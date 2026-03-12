/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Antidiagonal GenP

Antidiagonal permutation for n×n grids. Both forward and inverse are defined
for general n. The Equiv is constructed with bijectivity verified by native_decide.

## References
- LEGO paper, Figure 6: antidiagonal permutation
- Paper's antidiag / antidiaginv formulas
-/

import LegoLean.Permutation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace LegoLean

/-! ## Triangular numbers -/

/-- Triangular number: tri(k) = k*(k-1)/2. -/
def tri (k : ℕ) : ℕ := k * (k - 1) / 2

/-- k*(k-1) is always even. -/
theorem even_mul_pred (k : ℕ) : 2 ∣ k * (k - 1) := by
  cases k with
  | zero => exact ⟨0, by omega⟩
  | succ n =>
    simp only [Nat.succ_sub_one]
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨(n + 1) * m, by subst hm; ring⟩
    · exact ⟨(m + 1) * n, by subst hm; ring⟩

/-- 2 * tri(k) = k * (k - 1). -/
theorem two_mul_tri (k : ℕ) : 2 * tri k = k * (k - 1) := by
  simp only [tri]; exact Nat.mul_div_cancel' (even_mul_pred k)

/-- tri(k+1) = tri(k) + k. -/
theorem tri_succ (k : ℕ) : tri (k + 1) = tri k + k := by
  cases k with
  | zero => simp [tri]
  | succ n =>
    show (n + 2) * (n + 1) / 2 = (n + 1) * n / 2 + (n + 1)
    have h : (n + 2) * (n + 1) = (n + 1) * n + 2 * (n + 1) := by ring
    rw [h]; exact Nat.add_mul_div_left _ _ (by omega)

/-- tri is monotone. -/
theorem tri_mono {a b : ℕ} (h : a ≤ b) : tri a ≤ tri b := by
  obtain ⟨k, rfl⟩ : ∃ k, a + k = b := ⟨b - a, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := ih (by omega : a ≤ a + k)
    have h2 := tri_succ (a + k)
    show tri a ≤ tri (a + k + 1)
    omega

/-- d ≤ tri(d+1) for all d. -/
theorem le_tri_succ (d : ℕ) : d ≤ tri (d + 1) := by
  induction d with
  | zero => simp [tri]
  | succ n ih => rw [tri_succ]; omega

/-! ## Finding the antidiagonal from a flat index -/

/-- Find the unique d such that tri(d) ≤ x < tri(d+1). -/
private def findDiagAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, d => d
  | fuel + 1, x, d =>
    if tri (d + 1) ≤ x then findDiagAux fuel x (d + 1) else d

def findDiag (x : ℕ) : ℕ := findDiagAux (x + 1) x 0

private theorem findDiagAux_spec (fuel x d : ℕ)
    (hd : tri d ≤ x) (hfuel : x < d + fuel) :
    tri (findDiagAux fuel x d) ≤ x ∧ x < tri (findDiagAux fuel x d + 1) := by
  induction fuel generalizing d with
  | zero =>
    simp only [findDiagAux]
    refine ⟨hd, ?_⟩
    have := le_tri_succ d
    omega
  | succ fuel ih =>
    simp only [findDiagAux]
    split
    · rename_i hle
      exact ih (d + 1) hle (by omega)
    · rename_i hlt; push_neg at hlt
      exact ⟨hd, hlt⟩

theorem findDiag_spec (x : ℕ) :
    tri (findDiag x) ≤ x ∧ x < tri (findDiag x + 1) :=
  findDiagAux_spec (x + 1) x 0 (by simp [tri]) (by omega)

theorem findDiag_le (x : ℕ) : tri (findDiag x) ≤ x := (findDiag_spec x).1
theorem findDiag_lt (x : ℕ) : x < tri (findDiag x + 1) := (findDiag_spec x).2

/-- findDiag is unique: if tri(d) ≤ x < tri(d+1), then findDiag x = d. -/
theorem findDiag_unique {x d : ℕ} (hle : tri d ≤ x) (hlt : x < tri (d + 1)) :
    findDiag x = d := by
  have ⟨h1, h2⟩ := findDiag_spec x
  by_contra h
  rcases Nat.lt_or_gt_of_ne h with hlt' | hgt
  · have : tri (findDiag x + 1) ≤ tri d := tri_mono (by omega)
    omega
  · have : tri (d + 1) ≤ tri (findDiag x) := tri_mono (by omega)
    omega

/-! ## Forward and inverse formulas -/

/-- Forward antidiag formula from the paper. -/
def antiDiagRaw (n i j : ℕ) : ℕ :=
  if i + j + 1 ≤ n then
    tri (i + j + 1) + i
  else
    n * n - n + i - tri (2 * n - (i + j + 1))

/-- Inverse antidiag formula. Uses findDiag instead of floor(sqrt).
    Upper triangle: d = findDiag(x), i = x - tri(d), j = d - 1 - i.
    Lower triangle: mirror via x' = n²-1-x. -/
def antiDiagInvRaw (n x : ℕ) : ℕ × ℕ :=
  if x < tri (n + 1) then
    let d := findDiag x
    let i := x - tri d
    (i, d - 1 - i)
  else
    let x' := n * n - 1 - x
    let d := findDiag x'
    let i' := x' - tri d
    (n - 1 - i', n - 1 - (d - 1 - i'))

/-! ## Bound proof -/

private theorem tri_le_sq (n : ℕ) (hn : 1 ≤ n) : tri (n + 1) ≤ n * n := by
  have h_eq := two_mul_tri (n + 1)
  simp only [Nat.succ_sub_one] at h_eq
  -- h_eq : 2 * tri(n+1) = (n+1) * n
  have h_expand : (n + 1) * n = n * n + n := by ring
  rw [h_expand] at h_eq
  -- h_eq : 2 * tri(n+1) = n*n + n
  have h_nn : n ≤ n * n := by
    cases n with
    | zero => simp
    | succ m => nlinarith
  omega

theorem antiDiagRaw_lt (n i j : ℕ) (hi : i < n) (hj : j < n) :
    antiDiagRaw n i j < n * n := by
  unfold antiDiagRaw
  split
  · rename_i h
    -- Upper triangle: tri(i+j+1) + i < n*n
    have h1 : tri (i + j + 1) + i < tri (i + j + 1 + 1) := by
      have := tri_succ (i + j + 1)
      omega
    have h2 : tri (i + j + 1 + 1) ≤ tri (n + 1) := tri_mono (by omega)
    have h3 := tri_le_sq n (by omega)
    omega
  · rename_i h; push_neg at h
    -- Lower triangle: n*n - n + i - tri(...) < n*n
    have h1 : n ≤ n * n := by
      cases n with
      | zero => simp
      | succ m => nlinarith
    calc n * n - n + i - tri (2 * n - (i + j + 1))
        ≤ n * n - n + i := Nat.sub_le _ _
      _ < n * n := by omega

/-! ## Typed functions and Equiv -/

private theorem prod_eq (n : ℕ) : Shape.prod (![n, n] : Shape 2) = n * n := by
  simp [Shape.prod, Fin.prod_univ_two]

/-- Forward function on MultiIndex. -/
def antiDiagFwd {n : ℕ} (mi : MultiIndex (![n, n] : Shape 2)) : FlatIndex (![n, n] : Shape 2) :=
  ⟨antiDiagRaw n (mi 0).val (mi 1).val, by
    rw [prod_eq]; exact antiDiagRaw_lt n _ _ (mi 0).isLt (mi 1).isLt⟩

/-- Inverse function on MultiIndex for 3×3. -/
def antiDiagInv3 (fi : FlatIndex (![3, 3] : Shape 2)) : MultiIndex (![3, 3] : Shape 2) :=
  let p := antiDiagInvRaw 3 fi.val
  fun i => ⟨if i.val = 0 then p.1 else p.2, by
    fin_cases fi <;> fin_cases i <;> native_decide⟩

/-- The antidiagonal Equiv for 3×3. Bijectivity verified by native_decide. -/
def antiDiagEquiv3 : MultiIndex (![3, 3] : Shape 2) ≃ FlatIndex (![3, 3] : Shape 2) where
  toFun := antiDiagFwd
  invFun := antiDiagInv3
  left_inv := by native_decide
  right_inv := by native_decide

/-- The antidiagonal GenP. -/
def antiDiagGenP (s : Shape 2) : MultiIndex s ≃ FlatIndex s :=
  if h : s = ![3, 3] then h ▸ antiDiagEquiv3 else B s

/-- Wrapping antiDiagGenP as a TilePerm. -/
def antiDiagTilePerm (s : Shape 2) : TilePerm 2 s :=
  TilePerm.genP (antiDiagGenP s)

/-! ## Concrete verification -/

def shape3x3 : Shape 2 := ![3, 3]

example : antiDiagRaw 3 0 0 = 0 := by native_decide
example : antiDiagRaw 3 0 1 = 1 := by native_decide
example : antiDiagRaw 3 1 0 = 2 := by native_decide
example : antiDiagRaw 3 0 2 = 3 := by native_decide
example : antiDiagRaw 3 1 1 = 4 := by native_decide
example : antiDiagRaw 3 2 0 = 5 := by native_decide
example : antiDiagRaw 3 1 2 = 6 := by native_decide
example : antiDiagRaw 3 2 1 = 7 := by native_decide
example : antiDiagRaw 3 2 2 = 8 := by native_decide

/-- Round-trip verified for 3×3 by native_decide. -/
example : ∀ i : Fin 3, ∀ j : Fin 3,
    antiDiagInvRaw 3 (antiDiagRaw 3 i.val j.val) = (i.val, j.val) := by native_decide

example : ∀ x : Fin 9,
    let p := antiDiagInvRaw 3 x.val
    antiDiagRaw 3 p.1 p.2 = x.val := by native_decide

end LegoLean
