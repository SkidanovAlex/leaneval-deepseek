import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.fourierCoeff_pd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The elliptic lower bound (the coercivity input of Gårding, design `A9`)

For a symmetric coefficient family `A` that is elliptic with constant `lam`, the quadratic form
`∑_{c,d} A c d x * (w d * conj (w c)).re` dominates `lam * ∑ᵢ ‖w i‖²` pointwise
(`elliptic_lower_pointwise`), and hence also after integration against a `C²` function `u`
(`elliptic_lower`).  These are the coercivity inputs used in `garding_estimate`.
-/

noncomputable section

open MeasureTheory BigOperators
open scoped ComplexConjugate

namespace Work.Diff.STE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A continuous real function is integrable on the (bounded) unit cube. -/
lemma el_integrableOn_unitCube_of_continuous_real {F : (ι → ℝ) → ℝ} (hF : Continuous F) :
    Integrable F (volume.restrict unitCube) := by
  have hC : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsub : unitCube ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩
  exact (ContinuousOn.integrableOn_compact hC hF.continuousOn).mono_set hsub

/-- The pointwise elliptic lower bound: for an elliptic coefficient family `A` (constant `lam`)
and any `w : ι → ℂ`, the quadratic form dominates `lam * ∑ᵢ ‖w i‖²`. -/
theorem elliptic_lower_pointwise (A : ι → ι → (ι → ℝ) → ℝ) (lam : ℝ)
    (hpos : ∀ x (ξ : ι → ℝ), lam * ∑ i, (ξ i) ^ 2 ≤ ∑ c, ∑ d, A c d x * ξ c * ξ d)
    (x : ι → ℝ) (w : ι → ℂ) :
    lam * ∑ i, ‖w i‖ ^ 2 ≤ ∑ c, ∑ d, A c d x * (w d * star (w c)).re := by
  have h1 := hpos x (fun i => (w i).re)
  have h2 := hpos x (fun i => (w i).im)
  have hkey : ∀ i, ‖w i‖ ^ 2 = (w i).re ^ 2 + (w i).im ^ 2 := by
    intro i
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hsum : ∑ i, ‖w i‖ ^ 2 = (∑ i, (w i).re ^ 2) + (∑ i, (w i).im ^ 2) := by
    rw [Finset.sum_congr rfl (fun i _ => hkey i), Finset.sum_add_distrib]
  have hre : ∀ c d, (w d * star (w c)).re = (w d).re * (w c).re + (w d).im * (w c).im := by
    intro c d
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  calc lam * ∑ i, ‖w i‖ ^ 2
      = lam * (∑ i, (w i).re ^ 2) + lam * (∑ i, (w i).im ^ 2) := by rw [hsum]; ring
    _ ≤ (∑ c, ∑ d, A c d x * (w c).re * (w d).re)
          + (∑ c, ∑ d, A c d x * (w c).im * (w d).im) := add_le_add h1 h2
    _ = ∑ c, ∑ d, A c d x * ((w d).re * (w c).re + (w d).im * (w c).im) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun d _ => ?_
        ring
    _ = ∑ c, ∑ d, A c d x * (w d * star (w c)).re := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [hre c d]

/-- The integrated elliptic lower bound for a `C²` function `u`. -/
theorem elliptic_lower (A : ι → ι → (ι → ℝ) → ℝ) (hA : ∀ c d, ContDiff ℝ (⊤ : ℕ∞) (A c d))
    (lam : ℝ)
    (hpos : ∀ x (ξ : ι → ℝ), lam * ∑ i, (ξ i) ^ 2 ≤ ∑ c, ∑ d, A c d x * ξ c * ξ d)
    (u : (ι → ℝ) → ℂ) (hu : ContDiff ℝ 2 u) :
    lam * ∑ i, ∫ x in unitCube, ‖pd i u x‖ ^ 2
      ≤ ∑ c, ∑ d, ∫ x in unitCube, A c d x * (pd d u x * star (pd c u x)).re := by
  have hpd : ∀ i, Continuous (fun x => pd i u x) := fun i =>
    continuous_pd (ContDiff.of_le hu (by norm_num)) i
  have hLint : Integrable (fun x => lam * ∑ i, ‖pd i u x‖ ^ 2)
      (volume.restrict unitCube) :=
    (el_integrableOn_unitCube_of_continuous_real
      (continuous_finset_sum _ fun i _ => (hpd i).norm.pow 2)).const_mul lam
  have hRint : Integrable
      (fun x => ∑ c, ∑ d, A c d x * (pd d u x * star (pd c u x)).re)
      (volume.restrict unitCube) :=
    el_integrableOn_unitCube_of_continuous_real
      (continuous_finset_sum _ fun c _ => continuous_finset_sum _ fun d _ =>
        (hA c d).continuous.mul
          (Complex.continuous_re.comp ((hpd d).mul (hpd c).star)))
  have hpt : ∀ x, lam * ∑ i, ‖pd i u x‖ ^ 2
      ≤ ∑ c, ∑ d, A c d x * (pd d u x * star (pd c u x)).re :=
    fun x => elliptic_lower_pointwise A lam hpos x (fun i => pd i u x)
  calc lam * ∑ i, ∫ x in unitCube, ‖pd i u x‖ ^ 2
      = ∫ x in unitCube, lam * ∑ i, ‖pd i u x‖ ^ 2 := by
        rw [integral_const_mul, integral_finset_sum]
        exact fun i _ => el_integrableOn_unitCube_of_continuous_real ((hpd i).norm.pow 2)
    _ ≤ ∫ x in unitCube, ∑ c, ∑ d, A c d x * (pd d u x * star (pd c u x)).re :=
        integral_mono_ae hLint hRint (Filter.Eventually.of_forall hpt)
    _ = ∑ c, ∑ d, ∫ x in unitCube, A c d x * (pd d u x * star (pd c u x)).re := by
        rw [integral_finset_sum]
        · refine Finset.sum_congr rfl fun c _ => ?_
          rw [integral_finset_sum]
          exact fun d _ => el_integrableOn_unitCube_of_continuous_real
            ((hA c d).continuous.mul
              (Complex.continuous_re.comp ((hpd d).mul (hpd c).star)))
        · exact fun c _ => el_integrableOn_unitCube_of_continuous_real
            (continuous_finset_sum _ fun d _ => (hA c d).continuous.mul
              (Complex.continuous_re.comp ((hpd d).mul (hpd c).star)))

end Work.Diff.STE

end
