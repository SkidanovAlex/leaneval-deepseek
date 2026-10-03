import Mathlib
import Submission.Work.OROneRel.weinbaumDefs
import Submission.Work.OROneRel.psiSubstDefs
import Submission.Work.OROneRel.mmStepData_of_expsum_zero
import Submission.Work.OROneRel.freiheitssatz_case2
import Submission.Work.OROneRel.sigma_t_Psi
import Submission.Work.OROneRel.case2_substitution
import Submission.Work.OROneRel.eps_eq_toAdd_sigma

namespace Work.OROneRel

universe u

/-- The exponent sum in `y` of the Magnus/Putman substitution `subst y x (σ_x T) (σ_y T)` of a word
that is trivial in `⟨β | T⟩` vanishes.

The substitution `Φ = subst y x (σ_x T) (σ_y T)` sends `y ↦ y ^ (σ_x T)` and
`x ↦ x * y ^ (-(σ_y T))` and fixes every other generator.  Hence the generator map of
`σ_y ∘ Φ` kills every generator other than `y` and `x`, and sends
`y ↦ σ_x T` and `x ↦ -(σ_y T)`.  Consequently `(σ_y ∘ Φ)(T) = (σ_y T) ^ (σ_x T) * (σ_x T) ^ (-(σ_y T))
= 1`, so that `σ_y ∘ Φ` factors through the presentation `⟨β | T⟩`.  Since `w` is trivial there,
`σ_y (Φ w) = 1`, i.e. `eps y (Φ w) = 0`. -/
theorem wneEpsSubst {β : Type u} (T : FreeGroup β) {y x : β} (hxy : x ≠ y) (w : FreeGroup β)
    (hcontra : PresentedGroup.mk ({T} : Set (FreeGroup β)) w = 1) :
    Work.OROneRel.eps y (Work.OROneRel.subst y x (Multiplicative.toAdd (Work.OROneRel.sigma x T))
      (Multiplicative.toAdd (Work.OROneRel.sigma y T)) w) = 0 := by
  classical
  -- the exponent sum of the substitution `subst y x p q` in `y`
  have hP : ∀ u : FreeGroup β,
      (sigma y) (subst y x (Multiplicative.toAdd (sigma x T)) (Multiplicative.toAdd (sigma y T)) u)
        = (sigma y u) ^ (Multiplicative.toAdd (sigma x T))
          * (sigma x u) ^ (-(Multiplicative.toAdd (sigma y T))) :=
    fun u => c2s_sigma_t_subst hxy _ _ u
  have hy : sigma y T = Multiplicative.ofAdd (Multiplicative.toAdd (sigma y T)) := by simp
  have hx : sigma x T = Multiplicative.ofAdd (Multiplicative.toAdd (sigma x T)) := by simp
  -- the composite `σ_y ∘ Φ` kills the relator `T`
  have hT : (sigma y) (subst y x (Multiplicative.toAdd (sigma x T))
      (Multiplicative.toAdd (sigma y T)) T) = 1 := by
    rw [hP T, hy, hx]
    exact c2s_ofAdd_zpow_mul_zpow (Multiplicative.toAdd (sigma x T))
      (Multiplicative.toAdd (sigma y T))
  -- hence it factors through the normal closure of `T`
  have hker : Subgroup.normalClosure ({T} : Set (FreeGroup β)) ≤
      MonoidHom.ker ((sigma y).comp (subst y x (Multiplicative.toAdd (sigma x T))
        (Multiplicative.toAdd (sigma y T)))) :=
    Subgroup.normalClosure_le_normal (by
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact hT)
  have hw : w ∈ Subgroup.normalClosure ({T} : Set (FreeGroup β)) :=
    (PresentedGroup.mk_eq_one_iff).mp hcontra
  have hΨ : (sigma y) (subst y x (Multiplicative.toAdd (sigma x T))
      (Multiplicative.toAdd (sigma y T)) w) = 1 := by
    have h := hker hw
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at h
    exact h
  rw [eps_eq_toAdd_sigma, hΨ]
  rfl

end Work.OROneRel
