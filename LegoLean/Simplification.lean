/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Simplification Rules

This file proves the 7 simplification rules from Table II of the LEGO paper,
plus additional rules used by the MLIR `LegoArithSimplification` pass.
Each theorem corresponds to a pattern rewrite in the CASTLE compiler.

## References
- LEGO paper, Table II: Simplification rules
- MLIR source: `LegoArithSimplification.cpp`
-/

import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace LegoLean.Simplification

/-! ## Table II rules (R1–R7) -/

/-- Rule 1: (d*q + r) % d = r % d
    MLIR: `SimplifyRemId` -/
theorem rule1 (d q r : ℕ) : (d * q + r) % d = r % d := by
  simp

/-- Rule 2: (d*q + r) / d = q + r/d
    MLIR: `SimplifyDivId` -/
theorem rule2 (d q r : ℕ) (hd : 0 < d) : (d * q + r) / d = q + r / d := by
  conv_lhs => rw [show d * q + r = r + d * q from by omega]
  rw [Nat.add_mul_div_left r q hd]
  omega

/-- Rule 3: (x % d) / d = 0
    MLIR: `SimplifyDivOfRem` -/
theorem rule3 (x d : ℕ) (hd : 0 < d) : (x % d) / d = 0 :=
  Nat.div_eq_of_lt (Nat.mod_lt x hd)

/-- Rule 4: x / a = 0 when x < a
    Paper: Table II, Rule 4 -/
theorem rule4 (x a : ℕ) (h : x < a) : x / a = 0 :=
  Nat.div_eq_of_lt h

/-- Rule 5: x % a = x when x < a
    Paper: Table II, Rule 5 -/
theorem rule5 (x a : ℕ) (h : x < a) : x % a = x :=
  Nat.mod_eq_of_lt h

/-- Rule 6: (n + y) / l = n/l + y/l when l ∣ n
    MLIR: `SimplifyDivConst` (constant specialization) -/
theorem rule6 (n y l : ℕ) (hl : 0 < l) (hdvd : l ∣ n) : (n + y) / l = n / l + y / l := by
  obtain ⟨k, hk⟩ := hdvd
  subst hk
  conv_lhs => rw [show l * k + y = y + l * k from by omega]
  rw [Nat.add_mul_div_left y k hl]
  rw [Nat.mul_div_cancel_left k hl]
  omega

/-- Rule 7: a * (x / a) + x % a = x
    MLIR: `ReconstructId` -/
theorem rule7 (a x : ℕ) : a * (x / a) + x % a = x :=
  Nat.div_add_mod x a

/-! ## Additional MLIR pass rules

The following rules are implemented in `LegoArithSimplification.cpp` but were
not listed in the original Table II. We prove them here to close the gap
between the formally verified rules and the compiler implementation. -/

/-- Idempotent remainder: (x % d) % d = x % d
    MLIR: `SimplifyRemOfRem` -/
theorem rem_idempotent (x d : ℕ) (hd : 0 < d) : (x % d) % d = x % d :=
  Nat.mod_eq_of_lt (Nat.mod_lt x hd)

/-- Shared-factor division decomposition:
    (q*s + r) / (k*s) = q/k + ((q%k)*s + r) / (k*s)
    MLIR: `ExtendedSimplifyDivId` -/
theorem shared_factor_div (q s k r : ℕ) (hk : 0 < k) (hs : 0 < s) :
    (q * s + r) / (k * s) = q / k + ((q % k) * s + r) / (k * s) := by
  have hks : 0 < k * s := Nat.mul_pos hk hs
  have key : q * s + r = (q % k * s + r) + k * s * (q / k) := by
    nlinarith [Nat.div_add_mod q k]
  rw [key, Nat.add_mul_div_left _ _ hks]; omega

/-- Shared-factor remainder decomposition:
    (q*s + r) % (k*s) = ((q%k)*s + r) % (k*s)
    MLIR: `ExtendedSimplifyRemId` -/
theorem shared_factor_rem (q s k r : ℕ) (_hk : 0 < k) (_hs : 0 < s) :
    (q * s + r) % (k * s) = ((q % k) * s + r) % (k * s) := by
  have key : q * s + r = (q % k * s + r) + k * s * (q / k) := by
    nlinarith [Nat.div_add_mod q k]
  rw [key, Nat.add_mul_mod_self_left]

/-- Mixed-radix bound: (a%n)*m + (b%m) < n*m.
    This justifies `SimplifyMixedRadixDiv` (result is 0) and
    `SimplifyMixedRadixRem` (result is the input itself). -/
theorem mixed_radix_bound (a b n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (a % n) * m + b % m < n * m := by
  have h1 : a % n < n := Nat.mod_lt a hn
  have h2 : b % m < m := Nat.mod_lt b hm
  have h3 : a % n ≤ n - 1 := by omega
  have h4 : (a % n) * m ≤ (n - 1) * m := Nat.mul_le_mul_right m h3
  nlinarith

/-- Mixed-radix division: divui(remui(a,n)*m + remui(b,m), n*m) = 0
    MLIR: `SimplifyMixedRadixDiv` -/
theorem mixed_radix_div (a b n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ((a % n) * m + b % m) / (n * m) = 0 :=
  Nat.div_eq_of_lt (mixed_radix_bound a b n m hn hm)

/-- Mixed-radix remainder: remui(remui(a,n)*m + remui(b,m), n*m) = remui(a,n)*m + remui(b,m)
    MLIR: `SimplifyMixedRadixRem` -/
theorem mixed_radix_rem (a b n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ((a % n) * m + b % m) % (n * m) = (a % n) * m + b % m :=
  Nat.mod_eq_of_lt (mixed_radix_bound a b n m hn hm)

/-- Distributive factoring: a*c + b*c = (a + b)*c
    MLIR: `DistributiveFactor` -/
theorem distributive_factor (a b c : ℕ) : a * c + b * c = (a + b) * c := by
  ring

end LegoLean.Simplification
