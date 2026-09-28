import Mathlib
import Submission.Work.HP.ConicsDefs

/-!
# Lifting conic coefficients from `ZMod p` to `ZMod (p^2)`

This file provides the elementary structural facts about the reduction
`Work.HP.Conics.red : ZMod (p^2) →+* ZMod p` that are needed for
`Work.HP.conics_lift`: the standard section `lif`, the shape of the kernel,
and the resulting parametrisation `Phi` of the affine space of lifts of a
coefficient vector `ā`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MvPolynomial Finset

namespace Work.HP.Conics

/-- The standard lift `ZMod p → ZMod (p^2)`, sending `x` to its representative in `[0,p)`. -/
def lif (p : ℕ) (x : ZMod p) : ZMod (p^2) := (x.val : ZMod (p^2))

theorem lif_def (p : ℕ) (x : ZMod p) : lif p x = (x.val : ZMod (p^2)) := rfl

/-- Coefficientwise standard lift of a conic. -/
def coefLift (p : ℕ) (a : Mon 2 2 → ZMod p) : Mon 2 2 → ZMod (p^2) := fun m => lif p (a m)

/-- Standard lift of a vector of `(ZMod p)^3`. -/
def vecLift (p : ℕ) (v : Fin 3 → ZMod p) : Fin 3 → ZMod (p^2) := fun i => lif p (v i)

/-- The lift of `ā` parametrised by `B : (ZMod p)^6`. -/
def Phi (p : ℕ) (ā : Mon 2 2 → ZMod p) (B : Mon 2 2 → ZMod p) : Mon 2 2 → ZMod (p^2) :=
  fun m => lif p (ā m) + (p : ZMod (p^2)) * lif p (B m)

theorem Phi_apply (p : ℕ) (ā : Mon 2 2 → ZMod p) (B : Mon 2 2 → ZMod p) (m : Mon 2 2) :
    Phi p ā B m = lif p (ā m) + (p : ZMod (p^2)) * lif p (B m) := rfl

variable (p : ℕ) [Fact p.Prime]

theorem neZero_sq : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (Fact.out : p.Prime).ne_zero⟩

/-- Reduction of an element of `ZMod (p^2)` is its value cast to `ZMod p`. -/
theorem red_val (z : ZMod (p ^ 2)) : red p z = (z.val : ZMod p) := by
  haveI := neZero_sq p
  simp only [red, ZMod.castHom_apply]
  rw [ZMod.cast_eq_val]

/-- `lif` is a section of the reduction. -/
theorem red_lif (x : ZMod p) : red p (lif p x) = x := by
  haveI := neZero_sq p
  show red p ((x.val : ZMod (p ^ 2))) = x
  simp only [red, ZMod.castHom_apply]
  rw [ZMod.cast_eq_val, ZMod.val_natCast]
  have h : x.val < p ^ 2 := by
    have := ZMod.val_lt x
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    nlinarith
  rw [Nat.mod_eq_of_lt h]
  exact ZMod.natCast_zmod_val x

@[simp]
theorem red_p : red p (p : ZMod (p ^ 2)) = 0 := by
  simp [red]

/-- The kernel of the reduction consists exactly of the elements `p · lif t`. -/
theorem red_eq_zero_iff_exists_lif (z : ZMod (p ^ 2)) :
    red p z = 0 ↔ ∃ t : ZMod p, z = (p : ZMod (p ^ 2)) * lif p t := by
  haveI := neZero_sq p
  constructor
  · intro h
    rw [red_val, ZMod.natCast_eq_zero_iff] at h
    obtain ⟨s, hs⟩ := h
    have hslt : s < p := by
      have h1 : z.val < p ^ 2 := ZMod.val_lt z
      rw [hs, pow_two] at h1
      exact (Nat.mul_lt_mul_left (Fact.out : p.Prime).pos).mp h1
    refine ⟨(s : ZMod p), ?_⟩
    have hval : ((s : ZMod p)).val = s := ZMod.val_natCast_of_lt hslt
    rw [lif_def, hval, (ZMod.natCast_zmod_val z).symm, hs, Nat.cast_mul]
  · rintro ⟨t, rfl⟩
    rw [lif_def, map_mul, map_natCast, ZMod.natCast_self, zero_mul]

/-- Multiplying by `p` only remembers the reduction. -/
theorem p_mul_eq_p_mul_lif_red (z : ZMod (p ^ 2)) :
    (p : ZMod (p ^ 2)) * z = (p : ZMod (p ^ 2)) * lif p (red p z) := by
  haveI := neZero_sq p
  have hred0 : red p (z - lif p (red p z)) = 0 := by
    rw [map_sub, red_lif, sub_self]
  obtain ⟨t, ht⟩ := (red_eq_zero_iff_exists_lif p _).mp hred0
  have hz : z = lif p (red p z) + (p : ZMod (p ^ 2)) * lif p t := by
    rw [← ht]
    abel
  have hpp : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 := by
    rw [← Nat.cast_mul, show p * p = p ^ 2 from (pow_two p).symm]
    exact ZMod.natCast_self (p ^ 2)
  calc (p : ZMod (p ^ 2)) * z
      = (p : ZMod (p ^ 2)) * (lif p (red p z) + (p : ZMod (p ^ 2)) * lif p t) := by
        conv_lhs => rw [hz]
    _ = (p : ZMod (p ^ 2)) * lif p (red p z)
          + (p : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * lif p t) := by rw [mul_add]
    _ = (p : ZMod (p ^ 2)) * lif p (red p z)
          + ((p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) * lif p t := by rw [mul_assoc]
    _ = (p : ZMod (p ^ 2)) * lif p (red p z) + 0 := by rw [hpp, zero_mul]
    _ = (p : ZMod (p ^ 2)) * lif p (red p z) := by rw [add_zero]

/-- `t ↦ p · lif t` is injective. -/
theorem p_mul_lif_eq_zero_iff (t : ZMod p) : (p : ZMod (p ^ 2)) * lif p t = 0 ↔ t = 0 := by
  rw [lif_def, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  constructor
  · intro h
    have h2 : p ∣ t.val :=
      Nat.dvd_of_mul_dvd_mul_left (Fact.out : p.Prime).pos (by simpa [pow_two] using h)
    have : t.val = 0 := Nat.eq_zero_of_dvd_of_lt h2 (ZMod.val_lt t)
    exact (ZMod.val_eq_zero t).mp this
  · rintro rfl
    simp

theorem p_mul_lif_inj {b b' : ZMod p}
    (h : (p : ZMod (p ^ 2)) * lif p b = (p : ZMod (p ^ 2)) * lif p b') : b = b' := by
  have h1 : (p : ZMod (p ^ 2)) * (lif p b - lif p b') = 0 := by
    rw [mul_sub, h, sub_self]
  have h2 : (p : ZMod (p ^ 2)) * lif p (red p (lif p b - lif p b')) = 0 := by
    rw [← p_mul_eq_p_mul_lif_red]
    exact h1
  have h3 : red p (lif p b - lif p b') = 0 := (p_mul_lif_eq_zero_iff p _).mp h2
  rw [map_sub, red_lif, red_lif] at h3
  exact sub_eq_zero.mp h3

theorem redC_Phi (ā : Mon 2 2 → ZMod p) (B : Mon 2 2 → ZMod p) :
    redC p (Phi p ā B) = ā := by
  funext m
  show red p (lif p (ā m) + (p : ZMod (p ^ 2)) * lif p (B m)) = ā m
  simp only [map_add, map_mul, red_lif, red_p, zero_mul, add_zero]

theorem Phi_injective (ā : Mon 2 2 → ZMod p) : Function.Injective (Phi p ā) := by
  intro B B' h
  funext m
  have hm := congrFun h m
  simp only [Phi_apply] at hm
  exact p_mul_lif_inj p (add_left_cancel hm)

theorem Phi_surjective (ā : Mon 2 2 → ZMod p) (A : Mon 2 2 → ZMod (p ^ 2))
    (hA : redC p A = ā) : ∃ B, Phi p ā B = A := by
  have h : ∀ m, red p (A m - lif p (ā m)) = 0 := by
    intro m
    rw [map_sub, red_lif]
    rw [show red p (A m) = ā m from congrFun hA m, sub_self]
  choose t ht using fun m => (red_eq_zero_iff_exists_lif p _).mp (h m)
  refine ⟨t, ?_⟩
  funext m
  have hm : A m = lif p (ā m) + (p : ZMod (p ^ 2)) * lif p (t m) := by
    rw [← ht m]
    abel
  rw [Phi_apply, hm]

end Work.HP.Conics
