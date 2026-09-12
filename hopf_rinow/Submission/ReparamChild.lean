import ChallengeDeps
import Submission.NeckEq
import Submission.ModelPkg
import Mathlib

/-!
# Affine reparametrizations of geodesics solve the same ODE (child task)

Model-level.  If `σ : ℝ → E` solves the model geodesic equation on `Ioo 0 1`:
  (hσd) : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt σ (deriv σ x) x
  (hσd2): ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt (deriv σ) (accel (g (σ x)) (fderiv ℝ g (σ x)) (deriv σ x)) x
then for any affine reparametrization `c(u) := σ ((u - s) / (t - s))` (s < t, u ∈ Ioo s t) the
same derivative equations hold for `c` on `Ioo s t`:
  (a) HasDerivAt c (deriv c u) u
  (b) HasDerivAt (deriv c) (accel (g (c u)) (fderiv ℝ g (c u)) (deriv c u)) u

Proof route: chain rule twice + `accel_smul` (accel is quadratic in the velocity): if
aff(u) = (u-s)/(t-s) =: a*u + b (a = 1/(t-s) ≠ 0), then c'(u) = a • σ'(aff u) and
c''(u) = a² • σ''(aff u) = accel(g (c u), c'(u))  (a²•accel(g,σ') = accel(g, a•σ') by
`Submission.Model.accel_smul` and `smul_smul`).

You may add helper lemmas.  Do NOT change the statement.  No placeholders/axioms.
-/

open scoped ENNReal ContDiff Topology
open Set Metric Filter

namespace Submission
namespace ReparamChild

open Submission.Model

set_option synthInstance.maxHeartbeats 10000000
set_option maxHeartbeats 32000000

theorem reparam_geodesic_ode {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (g : E → Submission.Model.Bilin E) (hg : ContDiff ℝ 3 g)
    {σ : ℝ → E}
    (hσd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt σ (deriv σ x) x)
    (hσd2 : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (deriv σ) (Submission.Model.accel (g (σ x)) (fderiv ℝ g (σ x)) (deriv σ x)) x)
    {s t u : ℝ} (hst : s < t) (hu : u ∈ Ioo s t) :
    let c : ℝ → E := fun w => σ ((w - s) / (t - s))
    HasDerivAt c (deriv c u) u ∧
    HasDerivAt (deriv c)
      (Submission.Model.accel (g (c u)) (fderiv ℝ g (c u)) (deriv c u)) u := by
  dsimp
  let cσ : ℝ → E := fun w => σ ((w - s) / (t - s))
  let aff : ℝ → ℝ := fun w => (w - s) / (t - s)
  let a : ℝ := (t - s)⁻¹
  change HasDerivAt cσ (deriv cσ u) u ∧
    HasDerivAt (deriv cσ) (accel (g (cσ u)) (fderiv ℝ g (cσ u)) (deriv cσ u)) u
  have hts_pos : 0 < t - s := sub_pos.mpr hst
  -- the affine change of variable sends Ioo s t into Ioo 0 1
  have haf (w : ℝ) (hw : w ∈ Ioo s t) : aff w ∈ Ioo (0 : ℝ) 1 := by
    dsimp [aff]
    constructor
    · exact div_pos (sub_pos.mpr hw.1) hts_pos
    · exact (div_lt_one hts_pos).mpr (sub_lt_sub_right hw.2 s)
  -- aff has constant derivative a = (t - s)⁻¹
  have hlin (w : ℝ) : HasDerivAt aff a w := by
    dsimp [aff, a]
    simpa using (((hasDerivAt_id w).sub_const s).div_const (t - s))
  -- chain rule for cσ = σ ∘ aff
  have hder_cσ (w : ℝ) (hw : w ∈ Ioo s t) : HasDerivAt cσ (a • deriv σ (aff w)) w := by
    have hmem : aff w ∈ Ioo (0 : ℝ) 1 := haf w hw
    have hσ : HasDerivAt σ (deriv σ (aff w)) (aff w) := hσd _ hmem
    exact hσ.scomp w (hlin w)
  constructor
  · exact (hder_cσ u hu).congr_deriv (hder_cσ u hu).deriv.symm
  · have hmemu : aff u ∈ Ioo (0 : ℝ) 1 := haf u hu
    have hder_eq (w : ℝ) (hw : w ∈ Ioo s t) : deriv cσ w = a • deriv σ (aff w) :=
      (hder_cσ w hw).deriv
    -- near u the derivative of cσ equals the reparametrized velocity function
    have hagree : deriv cσ =ᶠ[𝓝 u] (fun w => a • deriv σ (aff w)) := by
      refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds hu) ?_
      intro w hw
      exact hder_eq w hw
    have hσ2 : HasDerivAt (deriv σ)
        (accel (g (σ (aff u))) (fderiv ℝ g (σ (aff u))) (deriv σ (aff u))) (aff u) :=
      hσd2 _ hmemu
    -- second chain rule: derivative of w ↦ a • (deriv σ (aff w))
    have hchain : HasDerivAt (fun w => deriv σ (aff w))
        (a • accel (g (σ (aff u))) (fderiv ℝ g (σ (aff u))) (deriv σ (aff u))) u := by
      exact hσ2.scomp u (hlin u)
    have houter : HasDerivAt (fun w => a • deriv σ (aff w))
        (a • (a • accel (g (σ (aff u))) (fderiv ℝ g (σ (aff u))) (deriv σ (aff u)))) u := by
      exact HasDerivAt.const_smul a hchain
    have hmain : HasDerivAt (deriv cσ)
        (a • (a • accel (g (σ (aff u))) (fderiv ℝ g (σ (aff u))) (deriv σ (aff u)))) u :=
      houter.congr_of_eventuallyEq hagree
    have hcu : cσ u = σ (aff u) := rfl
    have hdcu : deriv cσ u = a • deriv σ (aff u) := hder_eq u hu
    -- a • (a • accel gx T v) = a ^ 2 • accel gx T v = accel gx T (a • v)   (accel_smul)
    have hval : a • (a • accel (g (σ (aff u))) (fderiv ℝ g (σ (aff u))) (deriv σ (aff u)))
        = accel (g (cσ u)) (fderiv ℝ g (cσ u)) (deriv cσ u) := by
      rw [hcu, hdcu]
      rw [accel_smul (g (σ (aff u))) (fderiv ℝ g (σ (aff u))) (deriv σ (aff u)) a]
      rw [pow_two, smul_smul]
    exact hmain.congr_deriv hval

end ReparamChild
end Submission
