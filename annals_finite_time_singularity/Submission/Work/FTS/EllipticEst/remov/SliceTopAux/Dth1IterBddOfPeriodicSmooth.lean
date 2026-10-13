import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Instances.Real.Lemmas
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SliceTopAux

open scoped Real Topology

/-- The derivative of a function periodic with period `c` is again periodic with period `c`.
(No differentiability hypothesis is needed: at a point where `f` is not differentiable both
`fderiv`s involved vanish by definition.) -/
private lemma periodic_deriv {f : ℝ → ℝ} {c : ℝ} (hp : Function.Periodic f c) :
    Function.Periodic (deriv f) c := by
  intro x
  have h1 : deriv (fun y => f (c + y)) x = deriv f (c + x) := deriv_comp_const_add f c x
  have h2 : (fun y => f (c + y)) = f := by
    funext y
    rw [add_comm, hp y]
  rw [h2] at h1
  rw [show (x + c : ℝ) = c + x from add_comm _ _]
  exact h1.symm

/-- `θ ↦ sin (2θ)` is periodic with period `π`. -/
private lemma periodic_sin_two : Function.Periodic (fun θ : ℝ => Real.sin (2 * θ)) Real.pi := by
  intro x
  have h := Real.sin_periodic (2 * x)
  show Real.sin (2 * (x + Real.pi)) = Real.sin (2 * x)
  rw [show (2 * (x + Real.pi)) = 2 * x + 2 * Real.pi by ring]
  exact h

/-- `Dth1Iter j h` is `C^∞` and `π`-periodic whenever `h` is (the `ContDiff`-`ω`, i.e. analytic,
hypothesis of the theorem implies `C^∞`) and `π`-periodic. -/
private lemma contDiff_periodic_Dth1Iter {h : ℝ → ℝ} (hsm : ContDiff ℝ (⊤ : WithTop ℕ∞) h)
    (hp : Function.Periodic h Real.pi) (j : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Elliptic.Dth1Iter j h)
      ∧ Function.Periodic (Work.Elliptic.Dth1Iter j h) Real.pi := by
  -- `ω` (the analytic notion) implies `∞` (all finite orders).
  have hsm' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h :=
    hsm.of_le (le_top : ((⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
  induction j with
  | zero => simpa using ⟨hsm', hp⟩
  | succ j ih =>
    obtain ⟨hF, hper⟩ := ih
    -- `deriv` of a `C^∞` function is `C^∞`: `deriv f = fun x => (fderiv ℝ f x) 1`.
    have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ (Work.Elliptic.Dth1Iter j h)) :=
      (contDiff_infty_iff_fderiv.mp hF).2
    have hder : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (Work.Elliptic.Dth1Iter j h)) :=
      hfd.clm_apply (contDiff_const (c := (1 : ℝ)))
    have hsin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun θ : ℝ => Real.sin (2 * θ)) :=
      Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
    have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Work.Elliptic.Dth1 (Work.Elliptic.Dth1Iter j h)) :=
      hsin.mul hder
    have hper' : Function.Periodic (Work.Elliptic.Dth1 (Work.Elliptic.Dth1Iter j h)) Real.pi :=
      periodic_sin_two.mul (periodic_deriv hper)
    rw [Work.Elliptic.Dth1Iter_succ]
    exact ⟨hcd, hper'⟩

theorem Dth1IterBddOfPeriodicSmooth {h : ℝ → ℝ} (hsm : ContDiff ℝ (⊤ : WithTop ℕ∞) h)
    (hp : Function.Periodic h Real.pi) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ, |Work.Elliptic.Dth1Iter j h θ| ≤ C := by
  obtain ⟨hcd, hper⟩ := contDiff_periodic_Dth1Iter hsm hp j
  -- a continuous periodic function is bounded
  have hb : Bornology.IsBounded (Set.range (Work.Elliptic.Dth1Iter j h)) :=
    hper.isBounded_of_continuous Real.pi_ne_zero hcd.continuous
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  refine ⟨C, ?_, ?_⟩
  · have h0 := hC _ ⟨0, rfl⟩
    rw [Real.norm_eq_abs] at h0
    exact le_trans (abs_nonneg _) h0
  · intro θ
    have h1 := hC _ ⟨θ, rfl⟩
    rwa [Real.norm_eq_abs] at h1

end Work.FTS.EllipticEst.remov.SliceTopAux
