/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# GPU Verification Examples

Concrete examples demonstrating the GPU verification properties from GpuVerification.lean.
These match the MLIR test cases in `test/Lego/verify_bank_conflicts.mlir`,
`test/Lego/verify_coalescing.mlir`, and `test/Lego/bounds_verifier.mlir`.

## References
- LEGO MLIR tests: `verify_bank_conflicts.mlir`, `verify_coalescing.mlir`
-/

import LegoLean.GpuVerification
import LegoLean.Examples
import Mathlib.Tactic.FinCases

namespace LegoLean.GpuExamples

open LegoLean.Examples

/-! ## Bank Conflict Examples -/

/-- Standard config has 32 banks. -/
example : GpuConfig.standard.numBanks = 32 := rfl

/-- Standard config has warp size 32. -/
example : GpuConfig.standard.warpSize = 32 := rfl

/-- Standard config: cacheLineElements = 128/4 = 32. -/
example : cacheLineElements GpuConfig.standard = 32 := by native_decide

/-! ### Example 1: Row-major stride-1 access is bank-conflict-free
    Matches: verify_bank_conflicts.mlir — "row_major_32_conflict_free" -/

/-- 32 consecutive addresses starting at 0: each thread t accesses address t.
    bank(t) = (t * 4 / 4) % 32 = t % 32, which is injective. -/
theorem row_major_32_conflict_free :
    BankConflictFree GpuConfig.standard
      (⟨fun (t : Fin 32) => (⟨t.val, by have := t.isLt; omega⟩ : Fin 1024)⟩) := by
  intro t₁ t₂ hne ⟨haddr, hbank⟩
  simp [bankIndex, GpuConfig.standard] at hbank
  omega

/-! ### Example 2: Padded layout avoids conflicts
    Matches: verify_bank_conflicts.mlir — "padded_32x33_conflict_free"

    A 32×33 matrix: row-major access with stride 33.
    bank(t) = (t * 33 * 4 / 4) % 32 = (t * 33) % 32.
    Since 33 ≡ 1 (mod 32), t * 33 ≡ t (mod 32) → injective → conflict-free. -/

theorem padded_32x33_conflict_free :
    BankConflictFree GpuConfig.standard
      (⟨fun (t : Fin 32) => (⟨t.val * 33, by have := t.isLt; omega⟩ : Fin 1056)⟩) := by
  intro t₁ t₂ hne ⟨haddr, hbank⟩
  simp [bankIndex, GpuConfig.standard] at hbank
  omega

/-! ### Example 3: Column-major access with 32 rows HAS conflicts
    Matches: verify_bank_conflicts.mlir — "col_major_32_conflict"

    Thread t accesses address t * 32. bank(t * 32) = (t * 32) % 32 = 0.
    All threads map to the same bank → maximum conflict. -/

/-- All threads accessing stride-32 addresses map to bank 0. -/
theorem col_major_32_all_same_bank :
    ∀ t : Fin 32, bankIndex GpuConfig.standard (t.val * 32) =
      ⟨0, GpuConfig.standard.hBanksPos⟩ := by
  intro t
  simp [bankIndex, GpuConfig.standard]

/-- Column-major stride-32 has bank conflicts: threads 0 and 1 conflict. -/
theorem col_major_32_has_conflict :
    HasBankConflict GpuConfig.standard (0 * 32) (1 * 32) := by
  constructor
  · omega
  · simp [bankIndex, GpuConfig.standard]

/-! ## Coalescing Examples -/

/-! ### Example 4: Row-major is coalesced
    Matches: verify_coalescing.mlir — "row_major_coalesced"

    Thread t accesses address t. All in [0, 32) → same cache line. -/

theorem row_major_coalesced :
    IsCoalesced GpuConfig.standard
      (⟨fun (t : Fin 32) => (⟨t.val, by have := t.isLt; omega⟩ : Fin 1024)⟩) := by
  apply coalesced_of_range GpuConfig.standard _ 0
    (by native_decide : 0 < cacheLineElements GpuConfig.standard)
  · intro t
    refine ⟨by omega, ?_⟩
    have := t.isLt
    show t.val < 0 + cacheLineElements GpuConfig.standard
    simp [cacheLineElements, GpuConfig.standard]
  · exact ⟨0, rfl⟩

/-! ### Example 5: Column-major is NOT coalesced
    Matches: verify_coalescing.mlir — "col_major_not_coalesced"

    Thread t accesses address t * 32. Stride ≥ cacheLineElements → different cache lines. -/

theorem col_major_not_coalesced :
    ¬IsCoalesced GpuConfig.standard
      (⟨fun (t : Fin 32) => (⟨t.val * 32, by have := t.isLt; omega⟩ : Fin 1024)⟩) := by
  intro h
  have h1 := h (⟨1, by norm_num⟩ : Fin 32)
  simp [cacheLineElements, GpuConfig.standard] at h1

/-! ## Out-of-Bounds Safety Examples -/

/-! ### Example 6: FullLayout forward safety
    Every valid multi-index in a 6×4 matrix maps to a valid flat index < 24.
    This is automatic from the Equiv type. -/

theorem example_6x4_forward_safe (mi : MultiIndex shape_6x4) :
    (exampleFullLayout.toEquiv mi).val < exampleFullLayout.layout.totalElements :=
  fullLayout_forward_safe exampleFullLayout mi

/-! ### Example 7: FullLayout roundtrip
    Apply then inverse recovers the original for ANY multi-index. -/

theorem example_6x4_roundtrip (mi : MultiIndex shape_6x4) :
    exampleFullLayout.toEquiv.symm (exampleFullLayout.toEquiv mi) = mi :=
  fullLayout_roundtrip exampleFullLayout mi

/-! ### Example 8: No aliasing — distinct multi-indices ≠ same flat index -/

theorem example_6x4_no_aliasing
    (mi₁ mi₂ : MultiIndex shape_6x4)
    (h : exampleFullLayout.toEquiv mi₁ = exampleFullLayout.toEquiv mi₂) :
    mi₁ = mi₂ :=
  fullLayout_no_aliasing exampleFullLayout mi₁ mi₂ h

/-! ### Example 9: No dead memory — every flat index is reachable -/

theorem example_6x4_no_dead_memory
    (flat : Fin exampleFullLayout.layout.totalElements) :
    ∃ mi : MultiIndex shape_6x4, exampleFullLayout.toEquiv mi = flat :=
  fullLayout_no_dead_memory exampleFullLayout flat

/-! ### Example 10: ExpandBy layout bijectivity on extended space -/

theorem example_expandby_bijective :
    Function.Bijective exampleExpandBy.layout.toEquiv :=
  exampleExpandBy.layout.toEquiv.bijective

/-! ## ThreadLayout from FullLayout -/

/-- A 64×32 shape where the innermost dim fits a warp. -/
def shape_64x32 : Shape 2 := ![64, 32]

def blockShape_64x32 : Shape 2 := ![8, 4]
def tileShape_64x32 : Shape 2 := ![8, 8]
def shapes_64x32 : Fin 2 → Shape 2 := ![blockShape_64x32, tileShape_64x32]

def orderBy_64x32 : OrderBy 2 2 where
  shapes := shapes_64x32
  perms := fun _ => TilePerm.regP (Equiv.refl (Fin 2))

def groupBy_64x32 : GroupBy 2 2 := GroupBy.ofOrderBy orderBy_64x32

def fullLayout_64x32 : FullLayout 2 2 where
  logicalShape := shape_64x32
  layout := groupBy_64x32
  hTiling := by
    intro i
    show ∏ k : Fin 2, shapes_64x32 k i = shape_64x32 i
    fin_cases i <;> native_decide

def defaultIdx_64x32 : MultiIndex shape_64x32 :=
  fun i => ⟨0, by fin_cases i <;> simp [shape_64x32]⟩

/-- Build a ThreadLayout where thread ID varies along dim 1 (columns, size 32).
    Distinct threads get distinct addresses (from FullLayout bijectivity). -/
def threadLayout_64x32 : ThreadLayout GpuConfig.standard fullLayout_64x32.layout.totalElements :=
  ThreadLayout.ofFullLayout1D GpuConfig.standard fullLayout_64x32 ⟨1, by omega⟩
    (by show 32 ≤ shape_64x32 ⟨1, by omega⟩; native_decide)
    defaultIdx_64x32

theorem threadLayout_64x32_injective :
    Function.Injective threadLayout_64x32.addressMap :=
  threadLayout_fullLayout_injective GpuConfig.standard fullLayout_64x32 ⟨1, by omega⟩ _ defaultIdx_64x32

end LegoLean.GpuExamples
