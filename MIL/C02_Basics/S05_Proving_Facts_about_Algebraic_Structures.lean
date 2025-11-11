import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
    apply le_inf
    apply inf_le_right
    apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  . apply le_inf
    · calc
        x ⊓ y ⊓ z ≤ x ⊓ y := inf_le_left
        x ⊓ y ≤ x := inf_le_left
    · apply le_inf
      . calc
        x ⊓ y ⊓ z ≤ x ⊓ y := inf_le_left
        x ⊓ y ≤ y := inf_le_right
      · apply inf_le_right
  · apply le_inf
    · apply le_inf
      . apply inf_le_left
      · calc
          _ ≤ y ⊓ z := inf_le_right
          y ⊓ z ≤ y := inf_le_left
    · calc
      x ⊓ (y ⊓ z) ≤ y ⊓ z := inf_le_right
      y ⊓ z ≤ z := inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le
    apply le_sup_right
    apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  apply sup_le
  apply sup_le
  · apply le_sup_left
  · calc
    y ≤ y ⊔ z := le_sup_left
    y ⊔ z ≤ x ⊔ (y ⊔ z) := le_sup_right
  · calc
    z ≤ y ⊔ z := le_sup_right
    _ ≤ _ := le_sup_right
  · apply sup_le
    calc
      x ≤ x ⊔ y := le_sup_left
      _ ≤ _ := le_sup_left
    · apply sup_le
      calc
        y ≤ x ⊔ y := le_sup_right
        _ ≤ _ := le_sup_left
      exact le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  · apply le_inf
    · rfl
    · exact le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · rfl
    · exact inf_le_left
  · exact le_sup_left
end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  apply le_antisymm
  · apply le_inf
    · apply sup_le
      · exact le_sup_left
      · calc
          b ⊓ c ≤ b := inf_le_left
          _ ≤ _ := le_sup_right
    · apply sup_le
      · exact le_sup_left
      · calc
          b ⊓ c ≤ c := inf_le_right
          _ ≤ _ := le_sup_right
  · rw [h]
    · apply sup_le
      have : (a ⊔ b) ⊓ a = a ⊓ (a ⊔ b) := by
        apply le_antisymm
        repeat
          apply le_inf
          apply inf_le_right
          apply inf_le_left
      · rw [this]
        rw [absorb1]
        exact le_sup_left
      · have : (a ⊔ b) ⊓ c = c ⊓ (a ⊔ b) := by
          apply le_antisymm
          · apply le_inf
            exact inf_le_right
            exact inf_le_left
          · apply le_inf
            exact inf_le_right
            exact inf_le_left
        rw [this]
        rw [h]
        apply sup_le
        · calc
          c ⊓ a ≤ a := inf_le_right
          a ≤ a ⊔ b ⊓ c := le_sup_left
        · have : c ⊓ b = b ⊓ c := by
            apply le_antisymm
            repeat
              apply le_inf
              apply inf_le_right
              apply inf_le_left
          rw [this]
          exact le_sup_right

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  apply le_antisymm
  · rw [h]
    · apply le_inf
      have : a ⊓ b ⊔ a = a ⊔ a ⊓ b := by apply sup_comm
      rw [this]
      rw [absorb2]
      exact inf_le_left
      have : a ⊓ b ⊔ c = c ⊔ (a ⊓ b) := by apply sup_comm
      rw [this]
      rw [h]
      apply le_inf
      calc
        _ ≤ a := inf_le_left
        _ ≤ _ := le_sup_right
      have : b ⊔ c = c ⊔ b := by apply sup_comm
      rw [this]
      exact inf_le_right
  · rw [h]
    apply le_inf
    have : a ⊓ b ⊔ a = a ⊔ a ⊓ b := by apply sup_comm
    · rw [this]
      rw [absorb2]
      exact inf_le_left
    · have : a ⊓ b ⊔ a = a := by
        apply le_antisymm
        apply sup_le
        exact inf_le_left
        rfl
        exact le_sup_right
      rw [this]
      have : a ⊓ b ⊔ c = c ⊔ a ⊓ b := by apply sup_comm
      rw [this]
      rw [h]
      have : c ⊔ b = b ⊔ c := by apply sup_comm
      rw [this]
      rw [← inf_assoc]
      exact inf_le_right
end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  rw [← show a - a = 0 from by apply sub_self]
  apply sub_le_sub_right
  exact h

example (h: 0 ≤ b - a) : a ≤ b := by
  rw [← show a - a = 0 from by apply sub_self] at h
  rw [show a = a - a + a from by simp]
  rw [show b = b - a + a from by simp]
  apply add_le_add_right
  exact h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  rw [← sub_add_cancel (b * c) (a * c)]
  nth_rw 1 [← add_zero (a * c)]
  rw [← add_comm 0]
  apply add_le_add_right
  rw [← mul_sub_right_distrib]
  have : 0 ≤ b - a := by
    rw [← sub_self a]
    apply sub_le_sub_right
    exact h
  exact mul_nonneg this h'
end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have : 0 ≤ 2 * dist x y := by
    rw [two_mul]
    nth_rw 2 [dist_comm x y]
    rw [← dist_self x]
    apply dist_triangle x y x
  rw [← mul_zero 2] at this
  rw [mul_le_mul_left] at this
  apply this
  linarith
end
