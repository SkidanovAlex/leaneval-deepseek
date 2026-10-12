import Mathlib
import Submission.Q0Sector
import Submission.Work.BoseDict.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDict.integrable_star_modeProd_Phi`

The integrability of the real pairing of a symmetric mode product with a box state:

for `e : Fin m → Sp → ℂ` a.e. bounded (`MemLp _ ⊤`) and supported in the compact box
`boxL ℓ`, and `Φ : Xn n → ℝ` continuous with `tsupport Φ ⊆ abox n ℓ`, the function

    x ↦ Re (conj (modeProd e n α x) · Φ x)

is Lebesgue-integrable on the `n`-particle space.

The proof is the measure-theoretic half of the box → model dictionary:

* an a.e. bound for a `MemLp _ ⊤` function (`exists_bound_of_memLp_top`) and the
  "a.e. bounded + supported in a finite-measure set ⇒ integrable" criterion
  (`integrable_of_ae_bound_of_support`) give the integrability of every mode `e l`
  (the hypothesis `MemLp _ ⊤` is used only through the a.e. bound, and the support
  hypothesis through the finite measure of `boxL ℓ`);
* `modeProd` is a finite sum of `n`-fold products of the modes, each of which is
  integrable by Fubini over the product measure (`Integrable.fintype_prod_dep`);
* `Φ` is bounded because `tsupport Φ` is a closed subset of the compact box `abox n ℓ`;
* the integrand is dominated by `CΦ * ‖modeProd e n α x‖`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseDict

/-! ## 1. Two general integrability facts -/

/-- An a.e. bound for a `MemLp _ ⊤` function. -/
lemma exists_bound_of_memLp_top {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f ⊤ μ) : ∃ C : ℝ, ∀ᵐ x ∂μ, ‖f x‖ ≤ C := by
  have hlt : eLpNormEssSup f μ < ⊤ := by
    rw [← eLpNorm_exponent_top hf.aestronglyMeasurable]
    exact hf.eLpNorm_lt_top
  obtain ⟨C, hC⟩ := (eLpNormEssSup_lt_top_iff_isBoundedUnder (f := f) (μ := μ)).mp hlt
  refine ⟨(C : ℝ), ?_⟩
  filter_upwards [hC] with x hx
  have hx' : (‖f x‖₊ : ℝ) ≤ (C : ℝ) := by exact_mod_cast hx
  simpa using hx'

/-- A function that is a.e. bounded and vanishes off a set of finite measure is integrable. -/
lemma integrable_of_ae_bound_of_support {f : Sp → ℂ} {s : Set Sp} {C : ℝ}
    (hs : MeasurableSet s) (hfin : volume s < ⊤) (hmeas : AEStronglyMeasurable f volume)
    (hb : ∀ᵐ x ∂volume, ‖f x‖ ≤ C) (hsupp : Function.support f ⊆ s) : Integrable f := by
  have hind : f = s.indicator f := by
    funext x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      by_contra h
      exact hx (hsupp (Function.mem_support.mpr h))
  rw [hind]
  exact (IntegrableOn.of_bound hfin hmeas.restrict C
    (hb.filter_mono (ae_mono Measure.restrict_le_self))).integrable_indicator hs

/-! ## 2. Integrability of the mode factors -/

/-- Every mode `e l` is integrable: a.e. bounded and supported in the compact box `boxL ℓ`,
hence concentrated on a set of finite measure. -/
lemma integrable_single {m : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) (l : Fin m) :
    Integrable (e l) := by
  obtain ⟨C, hC⟩ := exists_bound_of_memLp_top (hbdd l)
  exact integrable_of_ae_bound_of_support (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)
    (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top (hbdd l).aestronglyMeasurable hC (hsupp l)

/-- The `n`-fold product of one mode along a labelling is integrable on the `n`-particle
space (Fubini over the product of the one-particle Lebesgue measures). -/
lemma integrable_prod_mode {m n : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (σ : Fin n → Fin m) :
    Integrable (fun x : Xn n => ∏ i : Fin n, e (σ i) (x i)) :=
  MeasureTheory.Integrable.fintype_prod_dep
    (E := fun _ : Fin n => Sp) (f := fun i : Fin n => fun y : Sp => e (σ i) y)
    (μ := fun _ : Fin n => (volume : Measure Sp))
    (fun i => integrable_single hbdd hsupp (σ i))

/-- The symmetric mode product `modeProd e n α` is integrable: it is a finite sum of
(rescaled) `n`-fold products of integrable modes. -/
lemma integrable_modeProd {m n : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (α : Fin m →₀ ℕ) :
    Integrable (fun x : Xn n => modeProd e n α x) := by
  have hterm : ∀ σ : Fin n → Fin m,
      Integrable (fun x : Xn n =>
        (if modeMult σ = α then (1 : ℂ) else 0) * ∏ i : Fin n, e (σ i) (x i)) :=
    fun σ => (integrable_prod_mode hbdd hsupp σ).const_mul _
  have h := integrable_finsetSum (Finset.univ : Finset (Fin n → Fin m))
    (f := fun σ (x : Xn n) =>
      (if modeMult σ = α then (1 : ℂ) else 0) * ∏ i : Fin n, e (σ i) (x i))
    (fun σ _ => hterm σ)
  simpa only [modeProd] using h

/-! ## 3. Compactness of the centred box for every side length -/

/-- The centred cube `acube ℓ` is compact for **every** `ℓ` (for `ℓ < 0` it is empty). -/
lemma acube_isCompact_all (ℓ : ℝ) : IsCompact (Submission.BoseGases.acube ℓ) := by
  by_cases hℓ : 0 ≤ ℓ
  · exact (Metric.isCompact_iff_isClosed_bounded).mpr
      ⟨Submission.BoseGases.acube_isClosed ℓ, Submission.BoseGases.acube_isBounded ℓ hℓ⟩
  · have hlt : ℓ < 0 := lt_of_not_ge hℓ
    have hempty : Submission.BoseGases.acube ℓ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      rw [Submission.BoseGases.mem_acube_iff] at hy
      linarith [(hy 0).1, (hy 0).2]
    rw [hempty]
    exact isCompact_empty

/-- The `N`-particle centred box `abox N ℓ` is compact for **every** `ℓ`. -/
lemma abox_isCompact_all (N : ℕ) (ℓ : ℝ) : IsCompact (Submission.BoseGases.abox N ℓ) := by
  rw [Submission.BoseGases.abox_eq_pi_acube]
  exact isCompact_univ_pi (fun _ : Fin N => acube_isCompact_all ℓ)

/-! ## 4. The main theorem -/

theorem integrable_star_modeProd_Phi {m n : ℕ} {ℓ : ℝ}
    {e : Fin m → Work.BoseDict.Sp → ℂ} {Φ : Work.BoseDict.Xn n → ℝ}
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hΦc : Continuous Φ) (hsuppΦ : tsupport Φ ⊆ Submission.BoseGases.abox n ℓ) (α : Fin m →₀ ℕ) :
    MeasureTheory.Integrable
      (fun x : Work.BoseDict.Xn n =>
        ((starRingEnd ℂ) (Work.BoseDict.modeProd e n α x) * (Φ x : ℂ)).re) := by
  classical
  -- `Φ` is bounded: `tsupport Φ` is a closed subset of the compact box `abox n ℓ`.
  have hΦbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Xn n, ‖(Φ x : ℂ)‖ ≤ C := by
    obtain ⟨C, hC⟩ := ((abox_isCompact_all n ℓ).of_isClosed_subset
      (isClosed_tsupport Φ) hsuppΦ).exists_bound_of_continuousOn hΦc.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    by_cases hx : x ∈ tsupport Φ
    · have h1 : ‖(Φ x : ℂ)‖ ≤ C := by
        rw [show ‖(Φ x : ℂ)‖ = |Φ x| from by simp, ← Real.norm_eq_abs]
        exact hC x hx
      exact le_trans h1 (le_max_left _ _)
    · have h0 : Φ x = 0 := by
        by_contra h
        exact hx (subset_closure (Function.mem_support.mpr h))
      simp [h0]
  obtain ⟨CΦ, -, hCΦ⟩ := hΦbdd
  -- the mode product is integrable
  have hM : Integrable (fun x : Xn n => modeProd e n α x) := integrable_modeProd hbdd hsupp α
  -- strong measurability of the integrand
  have hmeas : AEStronglyMeasurable
      (fun x : Xn n => ((starRingEnd ℂ) (modeProd e n α x) * (Φ x : ℂ)).re) volume := by
    have hsM : AEStronglyMeasurable
        (fun x : Xn n => (starRingEnd ℂ) (modeProd e n α x)) volume :=
      Continuous.comp_aestronglyMeasurable continuous_star hM.1
    have hsΦ : AEStronglyMeasurable (fun x : Xn n => (Φ x : ℂ)) volume :=
      (Complex.continuous_ofReal.comp hΦc).aestronglyMeasurable
    exact Continuous.comp_aestronglyMeasurable Complex.continuous_re (hsM.mul hsΦ)
  -- the domination
  have hbound : ∀ᵐ x ∂(volume : Measure (Xn n)),
      ‖((starRingEnd ℂ) (modeProd e n α x) * (Φ x : ℂ)).re‖ ≤ CΦ * ‖modeProd e n α x‖ := by
    filter_upwards with x
    have h1 : ‖((starRingEnd ℂ) (modeProd e n α x) * (Φ x : ℂ)).re‖
        ≤ ‖(starRingEnd ℂ) (modeProd e n α x) * (Φ x : ℂ)‖ := by
      rw [Real.norm_eq_abs]
      exact Complex.abs_re_le_norm _
    have h2 : ‖(starRingEnd ℂ) (modeProd e n α x) * (Φ x : ℂ)‖
        = ‖modeProd e n α x‖ * ‖(Φ x : ℂ)‖ := by
      rw [norm_mul, starRingEnd_apply, norm_star]
    calc ‖((starRingEnd ℂ) (modeProd e n α x) * (Φ x : ℂ)).re‖
        ≤ ‖(starRingEnd ℂ) (modeProd e n α x) * (Φ x : ℂ)‖ := h1
      _ = ‖modeProd e n α x‖ * ‖(Φ x : ℂ)‖ := h2
      _ ≤ ‖modeProd e n α x‖ * CΦ :=
          mul_le_mul_of_nonneg_left (hCΦ x) (norm_nonneg _)
      _ = CΦ * ‖modeProd e n α x‖ := mul_comm _ _
  exact (hM.norm.const_mul CΦ).mono' hmeas hbound

end Work.BoseDict
