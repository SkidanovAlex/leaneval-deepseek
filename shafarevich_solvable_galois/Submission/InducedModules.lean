import Mathlib.Tactic.Abel
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Submission.Work.GroupCohomology.H1_induction_on
import Submission.Work.GroupCohomology.H1pi_eq_zero_iff
import Submission.Work.GroupCohomology.H2_induction_on
import Submission.Work.GroupCohomology.H2pi_eq_zero_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Submission

open Work.GroupCohomology

section Coind

variable (G : Type*) (R : Type*) [Group G]

/-- The **coinduced module** structure on `G → R`: `(g • f) x = f (x * g)`. -/
instance instSMulCoind : SMul G (G → R) := ⟨fun g f => fun x => f (x * g)⟩

@[simp] lemma coind_smul_apply (g : G) (f : G → R) (x : G) : (g • f) x = f (x * g) := rfl

end Coind

section CoindAction

variable (G : Type*) (R : Type*) [Group G] [AddMonoid R]

instance instDistribMulActionCoind : DistribMulAction G (G → R) where
  one_smul f := by funext x; simp
  mul_smul g h f := by funext x; simp [mul_assoc]
  smul_zero f := by funext x; simp
  smul_add g f f' := by funext x; simp

end CoindAction

section Vanishing

variable {G : Type*} [Group G] {R : Type*} [AddCommGroup R]

theorem Z1_le_B1_coind : Z1 G (G → R) ≤ B1 G (G → R) := by
  intro f hf
  rw [mem_Z1_iff] at hf
  rw [mem_B1_iff]
  refine ⟨fun g => f g 1, ?_⟩
  funext g x
  have h := hf x g
  rw [d0_apply, Pi.sub_apply, coind_smul_apply, h]
  simp

theorem Z2_le_B2_coind : Z2 G (G → R) ≤ B2 G (G → R) := by
  intro c hc
  rw [mem_B2_iff]
  refine ⟨fun g x => c (x, g) 1, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  funext x
  have hcx := hc x g h
  rw [d1_apply, Pi.add_apply, Pi.sub_apply, coind_smul_apply]
  have hx : c (x * g, h) 1 + c (x, g) 1 = c (g, h) x + c (x, g * h) 1 := by
    have h1 := congrFun hcx 1
    simpa only [Pi.add_apply, coind_smul_apply, one_mul] using h1
  have hgoal : c (x * g, h) 1 - c (x, g * h) 1 + c (x, g) 1
      = c (x * g, h) 1 + c (x, g) 1 - c (x, g * h) 1 := by abel
  rw [hgoal, hx]
  abel

end Vanishing

section Subsingleton

variable {G : Type*} [Group G] {A : Type*} [AddCommGroup A] [DistribMulAction G A]

theorem subsingleton_H2_of_le (h : Z2 G A ≤ B2 G A) : Subsingleton (H2 G A) :=
  ⟨fun x y => by
    have hzero : ∀ x : H2 G A, x = 0 := fun x =>
      H2_induction_on (C := fun y : H2 G A => y = 0) x
        (fun c => (H2pi_eq_zero_iff c).mpr (h c.2))
    rw [hzero x, hzero y]⟩

theorem subsingleton_H1_of_le (h : Z1 G A ≤ B1 G A) : Subsingleton (H1 G A) :=
  ⟨fun x y => by
    have hzero : ∀ x : H1 G A, x = 0 := fun x =>
      H1_induction_on (C := fun y : H1 G A => y = 0) x
        (fun c => (H1pi_eq_zero_iff c).mpr (h c.2))
    rw [hzero x, hzero y]⟩

end Subsingleton

theorem subsingleton_H1_H2_coind (G : Type*) [Group G] (R : Type*) [AddCommGroup R] :
    Subsingleton (H1 G (G → R)) ∧ Subsingleton (H2 G (G → R)) :=
  ⟨subsingleton_H1_of_le Z1_le_B1_coind, subsingleton_H2_of_le Z2_le_B2_coind⟩

section Pi

variable {G : Type*} [Group G] {A : Type*} [AddCommGroup A] [DistribMulAction G A]

theorem Z2_le_B2_pi_of_le {ι : Type*} (h : Z2 G A ≤ B2 G A) :
    Z2 G (ι → A) ≤ B2 G (ι → A) := by
  intro c hc
  rw [mem_B2_iff]
  have key : ∀ i : ι, ∃ f : G → A, d1 G A f = fun p => c p i := by
    intro i
    have hci : (fun p : G × G => c p i) ∈ Z2 G A := by
      rw [mem_Z2_iff]
      intro g g' k
      have hh := congrFun (hc g g' k) i
      simpa using hh
    have hmem : (fun p : G × G => c p i) ∈ (d1 G A).range := h hci
    exact AddMonoidHom.mem_range.mp hmem
  choose f hf using key
  refine ⟨fun g i => f i g, ?_⟩
  funext p
  obtain ⟨g, g'⟩ := p
  funext i
  have := congrFun (hf i) (g, g')
  simpa using this

theorem subsingleton_H2_pi_of_le {ι : Type*} (h : Z2 G A ≤ B2 G A) :
    Subsingleton (H2 G (ι → A)) :=
  subsingleton_H2_of_le (Z2_le_B2_pi_of_le h)

end Pi

theorem subsingleton_H2_free (H : Type*) [Group H] (p r : ℕ) :
    Subsingleton (H2 H (Fin r → (H → ZMod p))) :=
  subsingleton_H2_pi_of_le (ι := Fin r) (Z2_le_B2_coind (G := H) (R := ZMod p))

end Submission
