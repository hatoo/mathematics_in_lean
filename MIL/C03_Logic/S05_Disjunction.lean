import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  cases le_or_gt x 0
  case inl h =>
    apply le_trans
    apply h
    apply abs_nonneg
  case inr h =>
    rw [abs_of_pos h]

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  cases le_or_gt (-x) 0
  case inl h =>
    apply le_trans
    apply h
    apply abs_nonneg
  case inr h =>
    rw [← abs_neg]
    rw [abs_of_pos h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  cases le_or_gt x 0
  case inl h =>
    cases le_or_gt y 0
    case inl g =>
      rw [abs_of_nonpos h]
      rw [abs_of_nonpos g]
      have : x + y ≤ 0 := by
        apply add_nonpos
        apply h
        apply g
      rw [abs_of_nonpos this]
      linarith
    case inr g =>
      rw [abs_of_nonpos h]
      rw [abs_of_pos g]
      cases le_or_gt (x + y) 0
      case inl l =>
        rw [abs_of_nonpos l]
        linarith
      case inr l =>
        rw [abs_of_pos l]
        linarith
  case inr h =>
    cases le_or_gt y 0
    case inl g =>
      rw [abs_of_pos h]
      rw [abs_of_nonpos g]
      cases le_or_gt (x + y) 0
      case inl l =>
        rw [abs_of_nonpos l]
        linarith
      case inr l =>
        rw [abs_of_pos l]
        linarith
    case inr g =>
      rw [abs_of_pos h]
      rw [abs_of_pos g]
      have : x + y > 0 := by
        rw [gt_iff_lt]
        linarith
      rw [abs_of_pos this]
theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · cases le_or_gt y 0
    case inl h =>
      rw [abs_of_nonpos h]
      intro g
      right
      exact g
    case inr h =>
      rw [abs_of_pos h]
      intro g
      left
      exact g
  · cases le_or_gt y 0
    case inl h =>
      rw [abs_of_nonpos h]
      intro g
      cases g
      case inl g =>
        linarith
      case inr g =>
        linarith
    case inr h =>
      intro g
      rw [abs_of_pos h]
      cases g
      case inl g =>
        linarith
      case inr g =>
        linarith

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  cases le_or_gt x 0
  case inl h =>
    rw [abs_of_nonpos h]
    constructor
    · intro g
      have t0 : -y < x := by linarith
      have t1 : x < y := by linarith
      exact ⟨t0, t1⟩
    · rintro ⟨g0, g1⟩
      linarith
  case inr h =>
    rw [abs_of_pos h]
    constructor
    · intro g
      have t0 : -y < x := by linarith
      have t1 : x < y := by linarith
      exact ⟨t0, t1⟩
    · rintro ⟨g0, g1⟩
      linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  sorry

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  sorry
