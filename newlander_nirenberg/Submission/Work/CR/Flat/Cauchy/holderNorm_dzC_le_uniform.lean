/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Uniform `C^{k,α}` bound for the flat `∂_z`-operator

The flat `∂_z`-operator `dzC u = (1/2)(∂_x u - i ∂_y u)` on `ℂ` is a *continuous
linear* function of the real differential `fderiv ℝ u`: there is a continuous
linear map `dzLin : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ` with
`dzC u z = dzLin (fderiv ℝ u z)`.

Consequently the `C^{k,α}`-norm of `dzC u` on `univ` is controlled by the
`C^{k+1,α}`-norm of `u`, with a constant that is *independent of `u`*: it is the
operator norm of `dzLin` (plus one).  This is the uniform-in-`f` strengthening of
`Work.CR.Flat.Cauchy.holderNorm_dzC_le`, and it is what makes it legitimate to
treat `∂_z` as a bounded operator between the Hölder spaces.

The proof combines two ingredients:

* `Work.CR.Flat.Holder.comp_linear_le`, the chain rule bound
  `D^i (L ∘ φ) = L.compContinuousMultilinearMap (D^i φ)` for a continuous
  linear `L`;
* `Work.CR.Flat.Holder.iDN_fderivWithin` / `hSN_fderivWithin`, which identify the
  `i`-th (Hölder) norm of the function `z ↦ fderivWithin ℝ u univ z` with the
  `(i+1)`-th (Hölder) norm of `u`.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.CR.Flat.Holder.comp_linear_le
import Submission.Work.CR.Flat.Cauchy

noncomputable section

open scoped NNReal ENNReal
open Set MeasureTheory
open Work.CR.Flat.Holder

namespace Work.CR.Flat.Cauchy

/-- The real-linear map `A ↦ (1/2)(A 1 - i·A i)` from `ℂ →L[ℝ] ℂ` to `ℂ`,
so that `∂_z u = dzLin ∘ (fderiv ℝ u)`. -/
noncomputable def dzLin : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) -
    (ContinuousLinearMap.mul ℝ ℂ Complex.I).comp
      (ContinuousLinearMap.apply ℝ ℂ Complex.I))

/-- The defining formula of `dzLin`. -/
@[simp] lemma dzLin_apply (A : ℂ →L[ℝ] ℂ) :
    dzLin A = (1 / 2 : ℂ) * (A 1 - Complex.I * A Complex.I) := by
  simp [dzLin]

/-- `∂_z` is the composite of the continuous linear map `dzLin` with `fderiv`.
Stated with `fderivWithin` on `univ` (which equals `fderiv`) to match the
"within" derivatives used by the Hölder norms. -/
lemma dzC_eq_dzLin_comp (f : ℂ → ℂ) :
    dzC f = dzLin ∘ (fun z => fderivWithin ℝ f Set.univ z) := by
  funext z
  simp [dzC, dzLin, fderivWithin_univ]

/-- The `C^{k,α}`-norm of `∂_z u` on `univ` is bounded by the `C^{k+1,α}`-norm
of `u`, with a constant `C > 0` that is uniform in `u`. -/
theorem holderNorm_dzC_le_uniform {k : ℕ} {α : ℝ} :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ, ContDiff ℝ (k + 1) f →
      holderNorm k α (fun z => dzC f z) Set.univ
        ≤ ENNReal.ofReal C * holderNorm (k + 1) α f Set.univ := by
  refine ⟨‖dzLin‖ + 1, by positivity, ?_⟩
  intro f hf
  set φ : ℂ → (ℂ →L[ℝ] ℂ) := fun z => fderivWithin ℝ f Set.univ z with hφdef
  have hΩ : UniqueDiffOn ℝ (Set.univ : Set ℂ) := uniqueDiffOn_univ
  have hcomp : dzC f = dzLin ∘ φ := by
    funext z; simp [φ, dzC, dzLin, fderivWithin_univ]
  -- `fderiv ℝ f` is `C^i` for every `i ≤ k`, because `f` is `C^{k+1}`.
  have hcont : ∀ i, i ≤ k → ContDiffOn ℝ (i : ℕ∞) φ Set.univ := by
    intro i hi
    have hk : ContDiff ℝ k (fderiv ℝ f) := (contDiff_succ_iff_fderiv.mp hf).2.2
    have hi' : ContDiff ℝ i (fderiv ℝ f) := hk.of_le (by exact_mod_cast hi)
    rw [hφdef, fderivWithin_univ]
    exact contDiffOn_univ.mpr hi'
  -- Term-by-term bound: the `i`-th `C^{i,α}` norm of `∂_z f` is controlled by the
  -- `(i+1)`-th norm of `f`, with the uniform constant `‖dzLin‖`.
  have hterm : ∀ i, i ≤ k →
      iterDerivNorm i (dzC f) Set.univ + holderSeminorm i α (dzC f) Set.univ
        ≤ ‖dzLin‖ₑ *
            (iterDerivNorm (i + 1) f Set.univ + holderSeminorm (i + 1) α f Set.univ) := by
    intro i hi
    obtain ⟨h1, h2⟩ := comp_linear_le dzLin i α (hcont i hi) hΩ
    have keyDN : iDN i φ Set.univ = iDN (i + 1) f Set.univ := by
      rw [hφdef]; exact iDN_fderivWithin i f Set.univ hΩ
    have keySN : hSN i α φ Set.univ = hSN (i + 1) α f Set.univ := by
      rw [hφdef]; exact hSN_fderivWithin i α f Set.univ hΩ
    rw [keyDN] at h1
    rw [keySN] at h2
    have hsum := add_le_add h1 h2
    rw [hcomp]
    simpa [iDN_complex_eq, hSN_complex_eq, mul_add] using hsum
  have hmain : holderNorm k α (dzC f) Set.univ
      ≤ ‖dzLin‖ₑ * holderNorm (k + 1) α f Set.univ := by
    have h1 : holderNorm k α (dzC f) Set.univ
        ≤ ∑ i ∈ Finset.range (k + 1), ‖dzLin‖ₑ *
            (iterDerivNorm (i + 1) f Set.univ + holderSeminorm (i + 1) α f Set.univ) := by
      simp only [holderNorm]
      exact Finset.sum_le_sum fun i hi => hterm i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    -- shifting the index by one loses only the nonnegative `i = 0` term.
    have h3 : (∑ i ∈ Finset.range (k + 1),
          (iterDerivNorm (i + 1) f Set.univ + holderSeminorm (i + 1) α f Set.univ))
        ≤ holderNorm (k + 1) α f Set.univ := by
      rw [← Finset.sum_image
        (f := fun j => iterDerivNorm j f Set.univ + holderSeminorm j α f Set.univ)
        (g := fun i => i + 1) (s := Finset.range (k + 1)) (fun a _ b _ hab => Nat.succ.inj hab)]
      simp only [holderNorm]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => by positivity)
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
      simp only [Finset.mem_range] at hi ⊢
      omega
    calc holderNorm k α (dzC f) Set.univ
        ≤ ∑ i ∈ Finset.range (k + 1), ‖dzLin‖ₑ *
            (iterDerivNorm (i + 1) f Set.univ + holderSeminorm (i + 1) α f Set.univ) := h1
      _ = ‖dzLin‖ₑ * (∑ i ∈ Finset.range (k + 1),
            (iterDerivNorm (i + 1) f Set.univ + holderSeminorm (i + 1) α f Set.univ)) := by
          rw [Finset.mul_sum]
      _ ≤ ‖dzLin‖ₑ * holderNorm (k + 1) α f Set.univ :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  calc holderNorm k α (dzC f) Set.univ
      ≤ ‖dzLin‖ₑ * holderNorm (k + 1) α f Set.univ := hmain
    _ ≤ ENNReal.ofReal (‖dzLin‖ + 1) * holderNorm (k + 1) α f Set.univ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (by linarith)

end Work.CR.Flat.Cauchy
