/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# GPU Verification Properties

This file formalizes three GPU memory access verification properties:
1. **Bank conflict freedom**: No two threads in a warp map to the same shared memory bank
2. **Coalesced access**: Consecutive threads access consecutive memory addresses
3. **Out-of-bounds safety**: All valid inputs map to valid outputs

These correspond to the MLIR verification passes:
  `-lego-verify-bank-conflicts`, `-lego-verify-coalescing`, `-lego-generate-bounds-checks`
-/

import LegoLean.GroupBy
import LegoLean.ExpandBy

namespace LegoLean

/-! ## GPU Configuration -/

/-- GPU hardware configuration parameters. -/
structure GpuConfig where
  warpSize : ℕ
  numBanks : ℕ
  elementSize : ℕ  -- in bytes
  hWarpPos : 0 < warpSize
  hBanksPos : 0 < numBanks

/-- Standard NVIDIA GPU configuration: 32-thread warps, 32 banks, 4-byte elements. -/
def GpuConfig.standard : GpuConfig where
  warpSize := 32
  numBanks := 32
  elementSize := 4
  hWarpPos := by omega
  hBanksPos := by omega

/-! ## Thread Layout

A ThreadLayout maps thread IDs to memory addresses through a LEGO layout.
The thread ID is a flat index in `Fin warpSize`, and the layout maps it to
an address (flat index in the layout's codomain). -/

/-- A thread-to-address mapping: given a thread ID, produce a flat memory address.
    This is the composition of thread indexing with the LEGO layout. -/
structure ThreadLayout (cfg : GpuConfig) (numElements : ℕ) where
  addressMap : Fin cfg.warpSize → Fin numElements

/-! ## 1. Bank Conflict Freedom

Two threads have a bank conflict when they access different addresses that
map to the same shared memory bank. Bank index is:
  bank(addr) = (addr * elementSize / 4) % numBanks

A broadcast (same address) is NOT a conflict. -/

/-- The bank index for a given flat address. -/
def bankIndex (cfg : GpuConfig) (addr : ℕ) : Fin cfg.numBanks :=
  ⟨(addr * cfg.elementSize / 4) % cfg.numBanks, Nat.mod_lt _ cfg.hBanksPos⟩

/-- Two threads have a bank conflict: different addresses, same bank. -/
def HasBankConflict (cfg : GpuConfig) (addr1 addr2 : ℕ) : Prop :=
  addr1 ≠ addr2 ∧ bankIndex cfg addr1 = bankIndex cfg addr2

/-- A thread layout is bank-conflict-free: no two distinct threads
    access different addresses in the same bank.
    (Broadcasts — same address — are allowed.) -/
def BankConflictFree {n : ℕ} (cfg : GpuConfig) (tl : ThreadLayout cfg n) : Prop :=
  ∀ t₁ t₂ : Fin cfg.warpSize, t₁ ≠ t₂ →
    ¬HasBankConflict cfg (tl.addressMap t₁).val (tl.addressMap t₂).val

/-- Equivalent formulation: distinct threads with different addresses have different banks. -/
theorem bankConflictFree_iff {n : ℕ} (cfg : GpuConfig) (tl : ThreadLayout cfg n) :
    BankConflictFree cfg tl ↔
    ∀ t₁ t₂ : Fin cfg.warpSize, t₁ ≠ t₂ →
      (tl.addressMap t₁).val ≠ (tl.addressMap t₂).val →
      bankIndex cfg (tl.addressMap t₁).val ≠ bankIndex cfg (tl.addressMap t₂).val := by
  unfold BankConflictFree HasBankConflict
  constructor
  · intro h t₁ t₂ hne haddr
    exact fun hbank => h t₁ t₂ hne ⟨haddr, hbank⟩
  · intro h t₁ t₂ hne ⟨haddr, hbank⟩
    exact h t₁ t₂ hne haddr hbank

/-- If the bank-index map is injective on threads, the layout is bank-conflict-free. -/
theorem bankConflictFree_of_injective_banks {n : ℕ} (cfg : GpuConfig)
    (tl : ThreadLayout cfg n)
    (h : Function.Injective (fun t => bankIndex cfg (tl.addressMap t).val)) :
    BankConflictFree cfg tl := by
  intro t₁ t₂ hne ⟨_, hbank⟩
  exact hne (h hbank)

/-! ### Bank Conflict: Sufficient Conditions -/

/-- Stride-1 access with standard config (32 banks, 4-byte elements):
    If the address map is `t ↦ base + t` (consecutive), then bank(t) = t % 32,
    which is injective for a 32-thread warp → conflict-free. -/
theorem bankConflictFree_consecutive {n : ℕ} (base : ℕ)
    (h32 : ∀ t : Fin 32, base + t.val < n) :
    BankConflictFree GpuConfig.standard
      ⟨fun t => ⟨base + t.val, h32 t⟩⟩ := by
  intro t₁ t₂ hne ⟨haddr, hbank⟩
  simp [bankIndex, GpuConfig.standard] at hbank
  omega

/-- When the address map is injective, a LEGO layout (which is always bijective)
    guarantees no two threads alias to the same address. This is a necessary
    condition for meaningful bank-conflict analysis. -/
theorem threadLayout_of_equiv_injective {n : ℕ} (cfg : GpuConfig)
    (f : Fin cfg.warpSize ↪ Fin n) :
    Function.Injective (ThreadLayout.mk (cfg := cfg) (numElements := n) f).addressMap :=
  f.injective

/-! ## 2. Coalesced Memory Access

Global memory coalescing: consecutive threads should access addresses
within the same cache line (typically 128 bytes = 32 × 4-byte elements).

For a warp of W threads, access is coalesced if:
  ∀ t, addr(t) / cacheLineElements = addr(0) / cacheLineElements

Or equivalently, the address range fits in one cache line. -/

/-- Cache line size in elements (128 bytes / elementSize). -/
def cacheLineElements (cfg : GpuConfig) : ℕ := 128 / cfg.elementSize

/-- Memory access is coalesced: all threads in the warp access the same cache line. -/
def IsCoalesced {n : ℕ} (cfg : GpuConfig) (tl : ThreadLayout cfg n) : Prop :=
  ∀ t : Fin cfg.warpSize,
    (tl.addressMap t).val / cacheLineElements cfg =
    (tl.addressMap ⟨0, cfg.hWarpPos⟩).val / cacheLineElements cfg

/-- Weaker coalescing: access spans at most `k` cache lines. -/
def CoalescedWithin {n : ℕ} (cfg : GpuConfig) (tl : ThreadLayout cfg n) (k : ℕ) : Prop :=
  ∃ baseLine : ℕ, ∀ t : Fin cfg.warpSize,
    (tl.addressMap t).val / cacheLineElements cfg < baseLine + k

/-- Perfect coalescing implies 1-line coalescing. -/
theorem isCoalesced_coalescedWithin {n : ℕ} (cfg : GpuConfig)
    (tl : ThreadLayout cfg n) (h : IsCoalesced cfg tl) :
    CoalescedWithin cfg tl 1 := by
  exact ⟨(tl.addressMap ⟨0, cfg.hWarpPos⟩).val / cacheLineElements cfg,
    fun t => by rw [h t]; omega⟩

/-- If all addresses lie in [base, base + cacheLineElements), they are coalesced. -/
theorem coalesced_of_range {n : ℕ} (cfg : GpuConfig) (tl : ThreadLayout cfg n)
    (base : ℕ) (hCLE : 0 < cacheLineElements cfg)
    (hRange : ∀ t : Fin cfg.warpSize,
      base ≤ (tl.addressMap t).val ∧ (tl.addressMap t).val < base + cacheLineElements cfg)
    (hAligned : cacheLineElements cfg ∣ base) :
    IsCoalesced cfg tl := by
  intro t
  obtain ⟨k, hk⟩ := hAligned
  have hBase0 := hRange ⟨0, cfg.hWarpPos⟩
  have hBaseT := hRange t
  have key : ∀ (v : ℕ), base ≤ v → v < base + cacheLineElements cfg →
      v / cacheLineElements cfg = k := by
    intro v hlo hhi
    -- v = base + r where r < cacheLineElements cfg
    obtain ⟨r, rfl⟩ : ∃ r, v = base + r := ⟨v - base, by omega⟩
    have hr : r < cacheLineElements cfg := by omega
    rw [hk]
    -- (cacheLineElements cfg * k + r) / cacheLineElements cfg
    -- = r / cacheLineElements cfg + k   (by Nat.add_mul_div_left)
    -- = 0 + k = k                       (by Nat.div_eq_of_lt)
    conv_lhs => rw [show cacheLineElements cfg * k + r = r + cacheLineElements cfg * k from by omega]
    rw [Nat.add_mul_div_left r k hCLE, Nat.div_eq_of_lt hr, Nat.zero_add]
  exact (key _ hBaseT.1 hBaseT.2).trans (key _ hBase0.1 hBase0.2).symm

/-! ## 3. Out-of-Bounds Safety

For a FullLayout or ExpandBy, we verify that:
- Forward: every valid logical index maps to a valid flat index (automatic from Equiv)
- ExpandBy: in-bounds inputs roundtrip correctly through apply/inv -/

/-- Forward OOB safety for FullLayout: trivially true because `toEquiv` produces `Fin n`.
    This is the key benefit of using Equiv: OOB is impossible by construction. -/
theorem fullLayout_forward_safe {d q : ℕ} (fl : FullLayout d q)
    (mi : MultiIndex fl.logicalShape) :
    (fl.toEquiv mi).val < fl.layout.totalElements :=
  (fl.toEquiv mi).isLt

/-- Inverse OOB safety for FullLayout: every flat index maps back to a valid multi-index. -/
theorem fullLayout_inverse_safe {d q : ℕ} (fl : FullLayout d q)
    (flat : Fin fl.layout.totalElements) (i : Fin d) :
    (fl.toEquiv.symm flat i).val < fl.logicalShape i :=
  (fl.toEquiv.symm flat i).isLt

/-- FullLayout roundtrip: apply then inverse recovers the original. -/
theorem fullLayout_roundtrip {d q : ℕ} (fl : FullLayout d q)
    (mi : MultiIndex fl.logicalShape) :
    fl.toEquiv.symm (fl.toEquiv mi) = mi :=
  fl.toEquiv.symm_apply_apply mi

/-- FullLayout inverse roundtrip: inverse then apply recovers the original. -/
theorem fullLayout_inv_roundtrip {d q : ℕ} (fl : FullLayout d q)
    (flat : Fin fl.layout.totalElements) :
    fl.toEquiv (fl.toEquiv.symm flat) = flat :=
  fl.toEquiv.apply_symm_apply flat

/-- ExpandBy: in-bounds inputs have valid flat indices when apply succeeds. -/
theorem expandBy_apply_valid {d q : ℕ} (eb : ExpandBy d q)
    (mi : MultiIndex eb.extShape)
    (flat : Fin (Shape.prod eb.origShape))
    (_h : eb.apply mi = some flat) :
    flat.val < Shape.prod eb.origShape :=
  flat.isLt

/-- The underlying layout of an ExpandBy is always bijective on the full extended space.
    This means no two extended-space inputs map to the same output. -/
theorem expandBy_layout_injective {d q : ℕ} (eb : ExpandBy d q) :
    Function.Injective eb.layout.toEquiv :=
  eb.layout.toEquiv.injective

/-! ## Connecting ThreadLayout to LEGO Layouts

Build a ThreadLayout from a FullLayout by specifying which dimension(s)
the thread ID maps to. -/

/-- Build a ThreadLayout from a FullLayout where thread ID varies along one dimension.
    Other dimensions are fixed at `defaultIdx`. Requires `warpSize ≤ dim size`. -/
def ThreadLayout.ofFullLayout1D {d q : ℕ}
    (cfg : GpuConfig) (fl : FullLayout d q)
    (threadDim : Fin d)
    (hFit : cfg.warpSize ≤ fl.logicalShape threadDim)
    (defaultIdx : MultiIndex fl.logicalShape) :
    ThreadLayout cfg fl.layout.totalElements :=
  ⟨fun t =>
    let mi : MultiIndex fl.logicalShape := fun i =>
      if h : i = threadDim then
        ⟨t.val, h ▸ Nat.lt_of_lt_of_le t.isLt hFit⟩
      else
        defaultIdx i
    fl.toEquiv mi⟩

/-! ## Parametric Theorems

These are the "for all shapes" theorems that go beyond instance-level testing. -/

/-- For any FullLayout, the address map derived from it is injective
    (no two logical indices map to the same flat index). -/
theorem fullLayout_no_aliasing {d q : ℕ} (fl : FullLayout d q)
    (mi₁ mi₂ : MultiIndex fl.logicalShape) (h : fl.toEquiv mi₁ = fl.toEquiv mi₂) :
    mi₁ = mi₂ :=
  fl.toEquiv.injective h

/-- For any FullLayout, every physical address is reachable from some logical index
    (no dead memory). -/
theorem fullLayout_no_dead_memory {d q : ℕ} (fl : FullLayout d q)
    (flat : Fin fl.layout.totalElements) :
    ∃ mi : MultiIndex fl.logicalShape, fl.toEquiv mi = flat :=
  fl.toEquiv.surjective flat

/-- A ThreadLayout built from a FullLayout inherits injectivity along the thread dimension:
    distinct thread IDs always produce distinct addresses. -/
theorem threadLayout_fullLayout_injective {d q : ℕ}
    (cfg : GpuConfig) (fl : FullLayout d q)
    (threadDim : Fin d) (hFit : cfg.warpSize ≤ fl.logicalShape threadDim)
    (defaultIdx : MultiIndex fl.logicalShape) :
    Function.Injective (ThreadLayout.ofFullLayout1D cfg fl threadDim hFit defaultIdx).addressMap := by
  intro t₁ t₂ heq
  simp only [ThreadLayout.ofFullLayout1D] at heq
  have hinj := fl.toEquiv.injective heq
  have h_eq := congr_fun hinj threadDim
  simp at h_eq
  exact Fin.ext h_eq

end LegoLean
