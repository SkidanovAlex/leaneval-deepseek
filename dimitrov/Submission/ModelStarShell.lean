import Mathlib
import Submission.ModelStarMap
import Submission.ModelStar
import Submission.Commons.Analysis.Normed.inv_tendsto_zero_comap_norm_atTop
import Submission.Commons.Analysis.Complex.norm_one_sub_smul_inv_tendsto_one

/-!
# ModelStarShell -- holomorphy and asymptotic of the explicit Eremenko model map

Completes the "easy half" analytic shell of `Submission.ModelStarMap`
(SESSION-8 milestone (a) of the STATUS file): for the model map

    F(z) = z · ∏_k (1 - z_k·z^{-1})^(2 r_k)           (|z_k| ≤ 1 fixed)

PROVED here (all axiom-clean, 0 sorries):
  * holomorphy: `modelFactor_differentiableAt`, `modelProduct_differentiableAt`,
    `modelF_differentiableAt` (points with ‖z_k‖ < ‖z‖; the factor base
    `1 - z_k·z^{-1}` lies in the slit plane there, so
    `DifferentiableAt.cpow_const` applies), and
    `modelF_differentiableOn_exterior` (the domain `{z | 1 < ‖z‖}` for
    ‖z_k‖ ≤ 1);
  * real asymptotic: `ratio_eq_prod` (‖F(z)‖/‖z‖ = ∏_k ‖1 - z_k z^{-1}‖^(2 r_k)
    for z ≠ 0) and `modelF_ratio_tendsto_one` (‖F(z)‖/‖z‖ → 1 as ‖z‖ → ∞);
  * capacity-one normalization (complex limits along ‖z‖ → ∞, filter
    `growFilter` = comap ‖·‖ atTop): `inv_tendsto_zero` (z⁻¹ → 0),
    `factor_tendsto_one` (1 - a·z^{-1} → 1), `modelFactor_tendsto_one`,
    `modelProduct_tendsto_one` (∏_k (1 - z_k·z^{-1})^(2 r_k) → 1), and
    `modelF_div_tendsto_one` (F(z)/z → 1: leading coefficient 1, so the
    model star has transfinite diameter 1).

OPEN (harder): conformality (injectivity / open mapping) of `modelF` on the
exterior, and the folded boundary correspondence (arg F constant on arcs
between consecutive `z_k`, arcs swept onto the spikes, spike tips = arc
maxima of ‖F‖).
-/

set_option linter.unnecessarySimpa false

noncomputable section

open scoped Real BigOperators Topology
open Filter Set

namespace Submission.ModelStarShell

open Complex

/-! ## Holomorphy of the model map on the exterior -/

/-- The model factor `z ↦ (1 - a·z^{-1})^t` is complex-differentiable where
`‖a‖ < ‖z‖` (the base lies in the slit plane). -/
lemma modelFactor_differentiableAt {a : ℂ} {t : ℝ} {z : ℂ} (haz : ‖a‖ < ‖z‖) :
    DifferentiableAt ℂ (fun z : ℂ => Submission.ModelStarMap.modelFactor a t z) z := by
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0, norm_zero] at haz
    exact (lt_irrefl 0) (lt_of_le_of_lt (norm_nonneg a) haz)
  have hg : DifferentiableAt ℂ (fun w : ℂ => (1 - a * w⁻¹)) z := by
    have hinv : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) z := by
      simpa using (differentiableAt_inv (𝕜 := ℂ) (R := ℂ) hz0)
    exact (hinv.const_mul a).const_sub 1
  have h0 : (1 - a * z⁻¹) ∈ Complex.slitPlane :=
    Submission.ModelStarMap.factor_mem_slitPlane (a := a) (z := z) haz
  simpa [Submission.ModelStarMap.modelFactor] using
    (DifferentiableAt.cpow_const (f := fun w : ℂ => (1 - a * w⁻¹)) (x := z) (c := (t : ℂ)) hg h0)

/-- The model product is complex-differentiable when every `‖z₀ k‖ < ‖z‖`. -/
lemma modelProduct_differentiableAt {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) {z : ℂ}
    (hz : ∀ k : Fin n, ‖z₀ k‖ < ‖z‖) :
    DifferentiableAt ℂ (fun z : ℂ => Submission.ModelStarMap.modelProduct z₀ r z) z := by
  have hfac : ∀ k : Fin n, k ∈ (Finset.univ : Finset (Fin n)) → DifferentiableAt ℂ
      (fun z : ℂ => Submission.ModelStarMap.modelFactor (z₀ k) (2 * r k) z) z := by
    intro k hk
    exact modelFactor_differentiableAt (a := z₀ k) (t := 2 * r k) (hz k)
  have hprod := DifferentiableAt.finsetProd (u := (Finset.univ : Finset (Fin n))) hfac
  have hfun : (∏ i ∈ (Finset.univ : Finset (Fin n)),
        (fun z : ℂ => Submission.ModelStarMap.modelFactor (z₀ i) (2 * r i) z)) =
      (fun z : ℂ => Submission.ModelStarMap.modelProduct z₀ r z) := by
    funext z
    rw [Finset.prod_apply]
    rfl
  simpa [hfun] using hprod

/-- The model map `F` is complex-differentiable when every `‖z₀ k‖ < ‖z‖`. -/
lemma modelF_differentiableAt {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) {z : ℂ}
    (hz : ∀ k : Fin n, ‖z₀ k‖ < ‖z‖) :
    DifferentiableAt ℂ (fun z : ℂ => Submission.ModelStarMap.modelF z₀ r z) z := by
  have hid : DifferentiableAt ℂ (fun z : ℂ => z) z := by
    simpa using (hasDerivAt_id z).differentiableAt
  have hprod : DifferentiableAt ℂ
      (fun z : ℂ => Submission.ModelStarMap.modelProduct z₀ r z) z :=
    modelProduct_differentiableAt z₀ r hz
  have hmul : DifferentiableAt ℂ (fun z : ℂ => z * Submission.ModelStarMap.modelProduct z₀ r z) z :=
    DifferentiableAt.mul hid hprod
  simpa [Submission.ModelStarMap.modelF] using hmul

/-- **Holomorphy on the exterior.**  If all `‖z₀ k‖ ≤ 1` then `modelF` is
complex-differentiable at every point of `{z | 1 < ‖z‖}`. -/
theorem modelF_differentiableOn_exterior {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ)
    (hz₀ : ∀ k : Fin n, ‖z₀ k‖ ≤ 1) :
    DifferentiableOn ℂ (fun z : ℂ => Submission.ModelStarMap.modelF z₀ r z)
      {z : ℂ | 1 < ‖z‖} := by
  intro z hz
  exact (modelF_differentiableAt z₀ r (z := z) (fun k => lt_of_le_of_lt (hz₀ k) hz)).differentiableWithinAt

/-! ## Asymptotic growth of the model map -/

/-- `‖z‖ → ∞` as a filter on `ℂ`. -/
def growFilter : Filter ℂ := comap (fun z : ℂ => ‖z‖) atTop

/-- The norm of `1 - a·z^{-1}` tends to `1` as `‖z‖ → ∞`.  (Commons version
`Commons.Analysis.Complex.norm_one_sub_smul_inv_tendsto_one`; kept here as a
thin alias for use by `modelF_ratio_tendsto_one`.) -/
lemma factor_base_tendsto_one (a : ℂ) :
    Tendsto (fun z : ℂ => ‖1 - a * z⁻¹‖) growFilter (𝓝 1) := by
  simpa [growFilter] using (Commons.Analysis.Complex.norm_one_sub_smul_inv_tendsto_one a)

/-- Pointwise identity: `‖F(z)‖/‖z‖ = ∏_k ‖1 - z_k z^{-1}‖^(2 r_k)` for `z ≠ 0`
(no further hypothesis on the `z_k`). -/
lemma ratio_eq_prod {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) {z : ℂ} (hz : z ≠ 0) :
    ‖Submission.ModelStarMap.modelF z₀ r z‖ / ‖z‖ =
      ∏ k : Fin n, ‖1 - z₀ k * z⁻¹‖ ^ (2 * r k) := by
  unfold Submission.ModelStarMap.modelF
  rw [norm_mul, Submission.ModelStarMap.norm_modelProduct]
  have hnz : ‖z‖ ≠ 0 := (norm_ne_zero_iff.mpr hz)
  field_simp [hnz]

/-- **Asymptotic growth.**  `‖F(z)‖/‖z‖ → 1` as `‖z‖ → ∞`. -/
theorem modelF_ratio_tendsto_one {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) :
    Tendsto (fun z : ℂ => ‖Submission.ModelStarMap.modelF z₀ r z‖ / ‖z‖) growFilter (𝓝 1) := by
  have hpow : ∀ k : Fin n,
      Tendsto (fun z : ℂ => ‖1 - z₀ k * z⁻¹‖ ^ (2 * r k)) growFilter (𝓝 1) := by
    intro k
    have hc : ContinuousAt (fun x : ℝ => x ^ (2 * r k)) 1 :=
      Real.continuousAt_rpow_const (x := (1 : ℝ)) (q := 2 * r k) (Or.inl one_ne_zero)
    have hcomp : Tendsto ((fun x : ℝ => x ^ (2 * r k)) ∘ (fun z : ℂ => ‖1 - z₀ k * z⁻¹‖))
        growFilter (𝓝 ((1 : ℝ) ^ (2 * r k))) :=
      hc.tendsto.comp (factor_base_tendsto_one (z₀ k))
    have hfun : (fun z : ℂ => (‖1 - z₀ k * z⁻¹‖) ^ (2 * r k)) =
        ((fun x : ℝ => x ^ (2 * r k)) ∘ (fun z : ℂ => ‖1 - z₀ k * z⁻¹‖)) := by
      funext z
      rfl
    have hplain : Tendsto (fun z : ℂ => (‖1 - z₀ k * z⁻¹‖) ^ (2 * r k)) growFilter
        (𝓝 ((1 : ℝ) ^ (2 * r k))) :=
      hcomp.congr' (Filter.Eventually.of_forall (congrFun hfun.symm))
    simpa [Real.one_rpow] using hplain
  have hprod : Tendsto (fun z : ℂ => ∏ k : Fin n, ‖1 - z₀ k * z⁻¹‖ ^ (2 * r k))
      growFilter (𝓝 (∏ k : Fin n, (1 : ℝ))) := by
    simpa using (tendsto_finsetProd (Finset.univ) (fun k hk => hpow k))
  have hprod1 : Tendsto (fun z : ℂ => ∏ k : Fin n, ‖1 - z₀ k * z⁻¹‖ ^ (2 * r k))
      growFilter (𝓝 1) := by
    simpa using hprod
  have hev : (fun z : ℂ => ∏ k : Fin n, ‖1 - z₀ k * z⁻¹‖ ^ (2 * r k)) =ᶠ[growFilter]
      (fun z : ℂ => ‖Submission.ModelStarMap.modelF z₀ r z‖ / ‖z‖) := by
    have hz : ∀ᶠ z in growFilter, z ≠ 0 := by
      unfold growFilter
      rw [Filter.eventually_comap]
      rw [Filter.eventually_atTop]
      refine ⟨1, ?_⟩
      intro b hb z hzeq hz0
      rw [hz0, norm_zero] at hzeq
      linarith
    filter_upwards [hz] with z hz
    exact (ratio_eq_prod z₀ r hz).symm
  exact hprod1.congr' hev

/-! ## Normalization at infinity: the model map has capacity 1 -/

/-- The inverse tends to zero along `growFilter` (i.e. `z⁻¹ → 0` as `‖z‖ → ∞`).
(Commons version `Commons.Analysis.Normed.inv_tendsto_zero_comap_norm_atTop`.) -/
lemma inv_tendsto_zero :
    Tendsto (fun z : ℂ => z⁻¹) growFilter (𝓝 0) := by
  simpa [growFilter] using (Commons.Analysis.Normed.inv_tendsto_zero_comap_norm_atTop (R := ℂ))

/-- The factor base `1 - a·z^{-1}` tends to `1` in `ℂ` as `‖z‖ → ∞`. -/
lemma factor_tendsto_one (a : ℂ) :
    Tendsto (fun z : ℂ => 1 - a * z⁻¹) growFilter (𝓝 1) := by
  have hzero : Tendsto (fun z : ℂ => a * z⁻¹) growFilter (𝓝 0) := by
    have h : Tendsto (fun z : ℂ => a * z⁻¹) growFilter (𝓝 (a * 0)) := inv_tendsto_zero.const_mul a
    simpa using h
  have hc : Tendsto (fun z : ℂ => (1 : ℂ)) growFilter (𝓝 1) := tendsto_const_nhds
  have hsub : Tendsto (fun z : ℂ => (1 : ℂ) - a * z⁻¹) growFilter (𝓝 (1 - 0)) :=
    Filter.Tendsto.sub hc hzero
  simpa using hsub

/-- Each model factor `(1 - a·z^{-1})^t` tends to `1` in `ℂ` as `‖z‖ → ∞`. -/
lemma modelFactor_tendsto_one (a : ℂ) (t : ℝ) :
    Tendsto (fun z : ℂ => Submission.ModelStarMap.modelFactor a t z) growFilter (𝓝 1) := by
  have hf := factor_tendsto_one a
  have hc : Tendsto (fun z : ℂ => (t : ℂ)) growFilter (𝓝 (t : ℂ)) := tendsto_const_nhds
  have hmem : (1 : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl (by norm_num)
  have hmain := Filter.Tendsto.cpow hf hc hmem
  simpa [Submission.ModelStarMap.modelFactor, Complex.one_cpow] using hmain

/-- **Capacity-one normalization (product part).**  The model product
`∏_k (1 - z_k·z^{-1})^(2 r_k)` tends to `1` in `ℂ` as `‖z‖ → ∞`. -/
theorem modelProduct_tendsto_one {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) :
    Tendsto (fun z : ℂ => Submission.ModelStarMap.modelProduct z₀ r z) growFilter (𝓝 1) := by
  have hfac : ∀ k : Fin n, Tendsto (fun z : ℂ =>
      Submission.ModelStarMap.modelFactor (z₀ k) (2 * r k) z) growFilter (𝓝 1) := by
    intro k
    exact modelFactor_tendsto_one (z₀ k) (2 * r k)
  have hprod : Tendsto (fun z : ℂ => ∏ k : Fin n,
      Submission.ModelStarMap.modelFactor (z₀ k) (2 * r k) z) growFilter
        (𝓝 (∏ k : Fin n, (1 : ℂ))) := by
    simpa using (tendsto_finsetProd (Finset.univ) (fun k hk => hfac k))
  have hfun : (fun z : ℂ => ∏ k : Fin n,
      Submission.ModelStarMap.modelFactor (z₀ k) (2 * r k) z) =
      (fun z : ℂ => Submission.ModelStarMap.modelProduct z₀ r z) := by
    funext z
    rfl
  simpa [hfun] using hprod

/-- **Capacity-one normalization.**  `F(z)/z → 1` in `ℂ` as `‖z‖ → ∞`, i.e.
the model map has leading coefficient `1` (transfinite diameter `1`). -/
theorem modelF_div_tendsto_one {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) :
    Tendsto (fun z : ℂ => Submission.ModelStarMap.modelF z₀ r z / z) growFilter (𝓝 1) := by
  have hprod := modelProduct_tendsto_one z₀ r
  have hz : ∀ᶠ z in growFilter, z ≠ 0 := by
    unfold growFilter
    rw [Filter.eventually_comap]
    rw [Filter.eventually_atTop]
    refine ⟨1, ?_⟩
    intro b hb z hzeq hz0
    rw [hz0, norm_zero] at hzeq
    linarith
  have hev : (fun z : ℂ => Submission.ModelStarMap.modelF z₀ r z / z) =ᶠ[growFilter]
      (fun z : ℂ => Submission.ModelStarMap.modelProduct z₀ r z) := by
    filter_upwards [hz] with z hz
    unfold Submission.ModelStarMap.modelF
    field_simp [hz]
  exact hprod.congr' hev.symm

/-! ## KL bound on the unit circle (easy-half core) -/

/-- **Easy-half core.**  For `s ≥ 1` distinct unit directions `z₀ j` and
weights `r j ≥ 0` summing to `1`, the model map attains at some unit point
`w` the Konyagin–Lev lower bound
`4^(1/s) ≤ ‖modelF z₀ r w‖` (on the circle `‖modelF‖ = ∏_j ‖· − z₀ j‖^(2 r j)`,
so this is exactly `Submission.ModelStar.max_product_ge_four_rpow_inv`
rewritten through the boundary identity).  With the capacity-one
normalization (`modelF_div_tendsto_one`) this is the analytic content of
"a model star of transfinite diameter 1 has a spike of length ≥ 4^(1/s)",
the sharp Dubinin constant in the model direction. -/
theorem modelF_unit_sup_ge_four_rpow_inv {s : ℕ} (hs : 0 < s)
    (z₀ : Fin s → ℂ) (hz : ∀ j : Fin s, ‖z₀ j‖ = 1)
    (r : Fin s → ℝ) (hr : ∀ j : Fin s, 0 ≤ r j)
    (hsum : (∑ j : Fin s, r j) = 1) :
    ∃ w : ℂ, ‖w‖ = 1 ∧
      (4 : ℝ) ^ (1 / (s : ℝ)) ≤ ‖Submission.ModelStarMap.modelF z₀ r w‖ := by
  rcases Submission.ModelStar.max_product_ge_four_rpow_inv s hs z₀ hz r hr hsum with ⟨w, hw, hprod⟩
  refine ⟨w, hw, ?_⟩
  rw [Submission.ModelStarMap.norm_modelF_unit z₀ r hw]
  exact hprod

end Submission.ModelStarShell

end
