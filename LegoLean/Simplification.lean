/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Simplification Rules — Table II

This file proves the 7 simplification rules from Table II of the LEGO paper.
These rules are used by the LEGO simplifier to reduce index expressions to
simpler forms, enabling efficient code generation.

## References
- LEGO paper, Table II: Simplification rules
- Python source: `simplifier.py`
-/

import Mathlib.Algebra.Order.Ring.Nat

namespace LegoLean.Simplification

/-- Rule 1: (d*q + r) % d = r % d
    Paper: Table II, Rule 1 -/
theorem rule1 (d q r : ℕ) : (d * q + r) % d = r % d := by
  simp

/-- Rule 2: (d*q + r) / d = q + r/d
    Paper: Table II, Rule 2 -/
theorem rule2 (d q r : ℕ) (hd : 0 < d) : (d * q + r) / d = q + r / d := by
  conv_lhs => rw [show d * q + r = r + d * q from by omega]
  rw [Nat.add_mul_div_left r q hd]
  omega

/-- Rule 3: (x % d) / d = 0
    Paper: Table II, Rule 3 -/
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
    Paper: Table II, Rule 6 -/
theorem rule6 (n y l : ℕ) (hl : 0 < l) (hdvd : l ∣ n) : (n + y) / l = n / l + y / l := by
  obtain ⟨k, hk⟩ := hdvd
  subst hk
  conv_lhs => rw [show l * k + y = y + l * k from by omega]
  rw [Nat.add_mul_div_left y k hl]
  rw [Nat.mul_div_cancel_left k hl]
  omega

/-- Rule 7: a * (x / a) + x % a = x
    Paper: Table II, Rule 7 -/
theorem rule7 (a x : ℕ) : a * (x / a) + x % a = x :=
  Nat.div_add_mod x a

end LegoLean.Simplification
