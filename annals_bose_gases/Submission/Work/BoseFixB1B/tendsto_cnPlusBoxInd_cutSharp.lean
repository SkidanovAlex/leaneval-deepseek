import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseFixB1B.sectorCountBoxAux
import Submission.Work.SlotWord.abs_boxQInd_le_of_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.tendsto_cnPlusBoxInd_cutSharp`

The count half of the sharp-fibre extension, in the `cutProd`/`sharpBoxState` vocabulary of
`Work.BoseFixB1B.sectorCountBoxAux`: the FS-faithful excited count `n₊(B(u))`
(`Work.UBBInputs8.cnPlusBoxInd`, i.e. `Σ_i ∫_{Λ} ‖Q_{B,i}Ψ‖²` with FS's box-projected
`Q_{B,i} = 1_B − P_{B,i}`, `eq:HBU`) of the smooth approximants
`Ψ_δ = (∏ᵢ γ_δ(xᵢ))·ψ = cutProd (γ δ) ψ` of the sharp box state
`1_{B(u)^k}·ψ = sharpBoxState (dlBox L d u) ψ` converges, as `δ → 0⁺`, to the corresponding
count of the sharp state.

This module is **self-contained**: for the statement vocabulary it imports only
`Work.BoseFixB1B.sectorCountBoxAux` (the hub defining `boxMargin`, `IsCutFamily`, `cutProd`,
`sharpBoxState`), and every analytic ingredient is proved here, so the file carries no `sorry`
and rests on no `sorryAx`.  (In particular it deliberately does *not* import the sibling
`Work.BoseFixB1B.SharpFibreDefs`, whose `sharpState_apply` collides by name with the
`sharpState_apply` of `sectorCountBoxAux`.)

The proof is dominated convergence, in three layers:

* **pointwise convergence off the box boundary** (`tendsto_cutProd_of_good_box`): for a
  configuration whose coordinates all have non-vanishing box margin, each cutoff factor
  `γ_δ(x_j)` is eventually equal to `1_{B(u)}(x_j)`, hence the product (times `ψ`) converges;
* **the slot integral** (`tendsto_boxPInd_cutProd_aux`): `z ↦ ∫_{B} Φ(x with xᵢ := z)` converges
  by DCT in `z`, using that the boundary `{boxMargin = 0}` is Lebesgue-null
  (`volume_boxMargin_eq_zero_hyperplane_sharp`) and that `ψ` is bounded by `Cb` on the box;
* **the count itself**: `boxQInd` is the difference of the boxed state and the slot mean, so it
  converges pointwise a.e. (`tendsto_boxQInd_cutProd_aux`), and `(boxQInd)²` is dominated by
  `(2Cb)²` on the finite-measure box (`abs_boxQInd_le_two_mul_sharp`), so the outer DCT applies;
  summing over the finitely many slots gives the statement.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## 0. The product form of the sharp box state -/

/-- `sharpBoxState B ψ` is the product of the slot indicators times `ψ`. -/
lemma sharpBoxState_eq_prod_sharp {k : ℕ} (B : Set E3) (ψ : X k → ℝ) :
    sharpBoxState B ψ
      = fun x : X k => (∏ i : Fin k, B.indicator (fun _ => (1 : ℝ)) (x i)) * ψ x := by
  classical
  funext x
  rw [sharpState_apply]
  by_cases h : ∀ i : Fin k, x i ∈ B
  · rw [if_pos h]
    have hone : (∏ i : Fin k, B.indicator (fun _ => (1 : ℝ)) (x i)) = (1 : ℝ) :=
      Finset.prod_eq_one (fun i _ => by rw [Set.indicator_of_mem (h i)])
    rw [hone, one_mul]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi⟩ := h
    have hzi : B.indicator (fun _ => (1 : ℝ)) (x i) = 0 := Set.indicator_of_notMem hi _
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hzi, zero_mul]

/-- A function supported in `B` vanishes off `B`. -/
lemma eq_zero_of_notMem_of_tsupport_subset_sharp {B : Set E3} {g : E3 → ℝ}
    (h : tsupport g ⊆ B) {x : E3} (hx : x ∉ B) : g x = 0 := by
  by_contra hne
  exact hx (h (subset_tsupport g (Function.mem_support.mpr hne)))

/-! ## 1. Null sets of the sliding-box geometry -/

/-- A coordinate hyperplane of `EuclideanSpace ℝ (Fin 3)` is Lebesgue-null. -/
lemma volume_coord_hyperplane_eq_zero_sharp (i : Fin 3) (c : ℝ) :
    (volume : Measure E3) {y : E3 | y i = c} = 0 := by
  have hqmp : Measure.QuasiMeasurePreserving (fun y : E3 => y i)
      (volume : Measure E3) (volume : Measure ℝ) :=
    (Measure.quasiMeasurePreserving_eval (fun _ : Fin 3 => (volume : Measure ℝ)) i).comp
      (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving
  have h := hqmp.preimage_null (Real.volume_singleton (a := c))
  have heq : (fun y : E3 => y i) ⁻¹' ({c} : Set ℝ) = {y : E3 | y i = c} := by
    ext y; simp
  rwa [heq] at h

/-- **The box margin vanishes only on a finite union of coordinate hyperplanes.**  Hence
`{y | boxMargin ℓ d u y = 0}` is Lebesgue-null. -/
lemma volume_boxMargin_eq_zero_hyperplane_sharp {ℓ d : ℝ} (u : E3) :
    (volume : Measure E3) {y : E3 | boxMargin ℓ d u y = 0} = 0 := by
  classical
  have hSnull : ∀ i : Fin 3,
      (volume : Measure E3) ({y : E3 | y i = ℓ / 2} ∪ {y : E3 | y i = -(ℓ / 2)}
        ∪ {y : E3 | y i = (ℓ * d) * u i + ℓ * d / 2}
        ∪ {y : E3 | y i = (ℓ * d) * u i - ℓ * d / 2}) = 0 := by
    intro i
    refine measure_union_null (measure_union_null (measure_union_null ?_ ?_) ?_) ?_
    · exact volume_coord_hyperplane_eq_zero_sharp i (ℓ / 2)
    · exact volume_coord_hyperplane_eq_zero_sharp i (-(ℓ / 2))
    · exact volume_coord_hyperplane_eq_zero_sharp i ((ℓ * d) * u i + ℓ * d / 2)
    · exact volume_coord_hyperplane_eq_zero_sharp i ((ℓ * d) * u i - ℓ * d / 2)
  have hcover : {y : E3 | boxMargin ℓ d u y = 0} ⊆
      ⋃ i : Fin 3, ({y : E3 | y i = ℓ / 2} ∪ {y : E3 | y i = -(ℓ / 2)}
        ∪ {y : E3 | y i = (ℓ * d) * u i + ℓ * d / 2}
        ∪ {y : E3 | y i = (ℓ * d) * u i - ℓ * d / 2}) := by
    intro y hy
    have hy' : boxMargin ℓ d u y = 0 := hy
    rw [boxMargin, min_eq_iff] at hy'
    rcases hy' with ⟨hA, -⟩ | ⟨hB, -⟩
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (H := Finset.univ_nonempty)
        (f := fun i : Fin 3 => ℓ / 2 - |y i|)
      have hzero : |y i| = ℓ / 2 := by linarith
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      rcases abs_cases (y i) with hh | hh
      · have : y i = ℓ / 2 := by linarith
        tauto
      · have : y i = -(ℓ / 2) := by linarith
        tauto
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (H := Finset.univ_nonempty)
          (f := fun i : Fin 3 => ℓ * d / 2 - |(y - (ℓ * d) • u) i|)
      have hzero : |(y - (ℓ * d) • u) i| = ℓ * d / 2 := by linarith
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      rcases abs_cases ((y - (ℓ * d) • u) i) with ⟨habs, -⟩ | ⟨habs, -⟩
      · have hsub : y i - (ℓ * d) * u i = ℓ * d / 2 := by
          have h1 := hzero
          have h2 := habs
          simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h1 h2
          linarith
        have : y i = (ℓ * d) * u i + ℓ * d / 2 := by linarith
        tauto
      · have hsub : y i - (ℓ * d) * u i = -(ℓ * d / 2) := by
          have h1 := hzero
          have h2 := habs
          simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h1 h2
          linarith
        have : y i = (ℓ * d) * u i - ℓ * d / 2 := by linarith
        tauto
  refine measure_mono_null hcover ?_
  exact measure_iUnion_null_iff.mpr hSnull

/-- **The configurations with a vanishing coordinate box margin are null.** -/
lemma volume_exists_boxMargin_coord_eq_zero_sharp (n : ℕ) {ℓ d : ℝ} (u : E3) :
    (volume : Measure (X n)) {x : X n | ∃ i : Fin n, boxMargin ℓ d u (x i) = 0} = 0 := by
  have hcoord : ∀ i : Fin n, (volume : Measure (X n))
      {x : X n | boxMargin ℓ d u (x i) = 0} = 0 := by
    intro i
    have hqmp : Measure.QuasiMeasurePreserving (fun x : X n => x i)
        (volume : Measure (X n)) (volume : Measure E3) :=
      Measure.quasiMeasurePreserving_eval (fun _ : Fin n => (volume : Measure E3)) i
    exact hqmp.preimage_null (volume_boxMargin_eq_zero_hyperplane_sharp (ℓ := ℓ) (d := d) u)
  have hunion : {x : X n | ∃ i : Fin n, boxMargin ℓ d u (x i) = 0}
      = ⋃ i : Fin n, {x : X n | boxMargin ℓ d u (x i) = 0} := by
    ext x; simp
  rw [hunion]
  exact measure_iUnion_null_iff.mpr hcoord

/-- For a.e. configuration of `X n`, the box margin of every coordinate is non-zero. -/
lemma ae_forall_boxMargin_coord_ne_zero_sharp (n : ℕ) {ℓ d : ℝ} (u : E3) :
    ∀ᵐ x ∂(volume : Measure (X n)), ∀ i : Fin n, boxMargin ℓ d u (x i) ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  have hset : {x : X n | ¬ (∀ i : Fin n, boxMargin ℓ d u (x i) ≠ 0)}
      = {x : X n | ∃ i : Fin n, boxMargin ℓ d u (x i) = 0} := by
    ext x; simp [not_forall]
  rw [hset]
  exact volume_exists_boxMargin_coord_eq_zero_sharp n u

/-! ## 2. The domination bound for `boxQInd` -/

/-- On the analysis box, `|boxQInd volA B i Ψ| ≤ 2C` as soon as `|Ψ| ≤ C` there, `B ⊆ Λ`,
`volA` is the volume of `B` and `B` has finite measure.  This is
`Work.SlotWord.abs_boxQInd_le_of_bound` together with the arithmetic bound
`|volA|⁻¹·(C·volA) ≤ C`. -/
lemma abs_boxQInd_le_two_mul_sharp {n : ℕ} {ℓ volA Cb : ℝ} {B : Set E3}
    (hBsub : B ⊆ acube ℓ) (hvolA : volA = (volume : Measure E3).real B)
    (hBfin : (volume : Measure E3) B < ⊤) (hCb : 0 ≤ Cb) {Ψ : X n → ℝ}
    (hΨ : ∀ x : X n, (∀ j : Fin n, x j ∈ acube ℓ) → |Ψ x| ≤ Cb)
    (i : Fin n) :
    ∀ x : X n, (∀ j : Fin n, x j ∈ acube ℓ) →
      |Work.UBBInputs8.boxQInd volA B i Ψ x| ≤ 2 * Cb := by
  intro x hx
  have h := Work.SlotWord.abs_boxQInd_le_of_bound (L := ℓ) (A := B) (volA := volA) (C := Cb)
    hBsub hCb hBfin hΨ i x hx
  have hreal : 0 ≤ (volume : Measure E3).real B := ENNReal.toReal_nonneg
  have h2 : |volA|⁻¹ * (Cb * (volume : Measure E3).real B) ≤ Cb := by
    rw [hvolA, abs_of_nonneg hreal]
    rcases eq_or_lt_of_le hreal with h0 | hpos
    · rw [← h0]
      simpa using hCb
    · have h1 : ((volume : Measure E3).real B)⁻¹ * (volume : Measure E3).real B = 1 :=
        inv_mul_cancel₀ (ne_of_gt hpos)
      calc ((volume : Measure E3).real B)⁻¹ * (Cb * (volume : Measure E3).real B)
          = Cb * (((volume : Measure E3).real B)⁻¹ * (volume : Measure E3).real B) := by ring
        _ ≤ Cb := le_of_eq (by rw [h1, mul_one])
  linarith

/-! ## 3. Pointwise convergence of the approximating states -/

/-- **Pointwise convergence off the boundary.**  If every coordinate of `x` has non-vanishing
box margin, then each factor `γ_δ(x_j)` is eventually equal to the indicator of the sliding box
(attained, since `γ_δ` is supported in the box and equals `1` where the margin exceeds `δ`), so
the finite product converges and hence `Ψ_δ(x) → 1_{B(u)^k}·ψ(x)`. -/
lemma tendsto_cutProd_of_good_box {n : ℕ} {ℓ d : ℝ} {u : E3}
    {ψ : X n → ℝ} {γ : ℝ → E3 → ℝ}
    (hγsupp : ∀ δ : ℝ, 0 < δ → tsupport (γ δ) ⊆ dlBox ℓ d u)
    (hγone : ∀ δ : ℝ, 0 < δ → ∀ x, boxMargin ℓ d u x ≥ δ → γ δ x = 1)
    (hγbdd : ∀ δ : ℝ, 0 < δ → ∀ x, 0 ≤ γ δ x ∧ γ δ x ≤ 1)
    {x : X n} (hgood : ∀ j : Fin n, boxMargin ℓ d u (x j) ≠ 0) :
    Filter.Tendsto (fun δ : ℝ => cutProd (γ δ) ψ x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (sharpBoxState (dlBox ℓ d u) ψ x)) := by
  classical
  have hfac : ∀ i : Fin n, Filter.Tendsto (fun δ : ℝ => γ δ (x i))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i))) := by
    intro i
    have hne : boxMargin ℓ d u (x i) ≠ 0 := hgood i
    rcases lt_trichotomy (boxMargin ℓ d u (x i)) 0 with hlt | heq | hgt
    · have hnot : x i ∉ dlBox ℓ d u := fun hmem =>
        absurd (boxMargin_nonneg_iff.mpr hmem) (not_le.mpr hlt)
      rw [Set.indicator_of_notMem hnot]
      have hev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), γ δ (x i) = 0 := by
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact eq_zero_of_notMem_of_tsupport_subset_sharp (hγsupp δ hδ) hnot
      exact Filter.Tendsto.congr' (hev.mono (fun δ h => h.symm))
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    · exact absurd heq hne
    · have hmem : x i ∈ dlBox ℓ d u := boxMargin_nonneg_iff.mp hgt.le
      rw [Set.indicator_of_mem hmem]
      have hev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), γ δ (x i) = 1 := by
        filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (s := Set.Ioi 0) (Iic_mem_nhds hgt)] with δ hδpos hδle
        exact hγone δ hδpos (x i) hδle
      exact Filter.Tendsto.congr' (hev.mono (fun δ h => h.symm))
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1))
  have hprod : Filter.Tendsto (fun δ : ℝ => ∏ i : Fin n, γ δ (x i))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∏ i : Fin n, (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i))) := by
    simpa using tendsto_finsetProd (Finset.univ : Finset (Fin n)) (fun i _ => hfac i)
  have h1 : Filter.Tendsto (fun δ : ℝ => (∏ i : Fin n, γ δ (x i)) * ψ x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((∏ i : Fin n, (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)) * ψ x)) :=
    Filter.Tendsto.mul_const (ψ x) hprod
  have hsharp : sharpBoxState (dlBox ℓ d u) ψ x
      = (∏ i : Fin n, (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)) * ψ x := by
    rw [sharpBoxState_eq_prod_sharp]
  simpa only [cutProd_apply, hsharp] using h1

/-! ## 4. Convergence of the slot integral -/

/-- **The slot integral converges.**  For a configuration `x` in the box all of whose coordinates
have non-vanishing margin, the `i`-th slot marginal
`δ ↦ ∫_{B(u)} Ψ_δ(x with xᵢ := z)` converges to the slot marginal of the sharp state.  This is
`tendsto_integral_filter_of_dominated_convergence` in `z ∈ B(u)`: the integrands are bounded by
`Cb` on the finite-measure box (`z ∈ B(u) ⊆ Λ` and `x ∈ Λ` keep the updated configuration in
`Λ`), and they converge for a.e. `z`, namely for every `z` whose box margin does not vanish. -/
lemma tendsto_boxPInd_cutProd_aux {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ)
    {u : E3} {ψ : X n → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) {Cb : ℝ}
    (hψb : ∀ x ∈ abox n ℓ, |ψ x| ≤ Cb)
    {γ : ℝ → E3 → ℝ}
    (hγcd : ∀ δ : ℝ, 0 < δ → ContDiff ℝ (⊤ : ENat) (γ δ))
    (hγsupp : ∀ δ : ℝ, 0 < δ → tsupport (γ δ) ⊆ dlBox ℓ d u)
    (hγone : ∀ δ : ℝ, 0 < δ → ∀ x, boxMargin ℓ d u x ≥ δ → γ δ x = 1)
    (hγbdd : ∀ δ : ℝ, 0 < δ → ∀ x, 0 ≤ γ δ x ∧ γ δ x ≤ 1)
    (i : Fin n) {x : X n} (hx : x ∈ abox n ℓ)
    (hgood : ∀ j : Fin n, boxMargin ℓ d u (x j) ≠ 0) :
    Filter.Tendsto (fun δ : ℝ => ∫ z in dlBox ℓ d u,
        cutProd (γ δ) ψ (Function.update x i z))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ z in dlBox ℓ d u,
        sharpBoxState (dlBox ℓ d u) ψ (Function.update x i z))) := by
  classical
  have hBmeas : MeasurableSet (dlBox ℓ d u) := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hBfin : (volume : Measure E3) (dlBox ℓ d u) < ⊤ :=
    Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u
  have hxmem : ∀ z ∈ dlBox ℓ d u, Function.update x i z ∈ abox n ℓ := by
    intro z hz j
    rw [Function.update_apply]
    by_cases hj : j = i
    · rw [if_pos hj]
      exact ((Submission.BoseGases.mem_dlBox_iff ℓ d u z).mp hz).1
    · rw [if_neg hj]
      exact (Submission.BoseGases.mem_abox_iff n ℓ x).mp hx j
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (F := fun δ (z : E3) => cutProd (γ δ) ψ (Function.update x i z))
    (f := fun (z : E3) => sharpBoxState (dlBox ℓ d u) ψ (Function.update x i z))
    (bound := fun _ => Cb) ?_ ?_ ?_ ?_
  · -- eventual a.e. strong measurability
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hmeas_c : Measurable (cutProd (γ δ) ψ) := by
      have h1 : Continuous (fun y : X n => ∏ j : Fin n, γ δ (y j)) :=
        continuous_finsetProd Finset.univ
          (fun j _ => (hγcd δ hδ).continuous.comp (continuous_apply j))
      exact (h1.mul hψ.continuous).measurable
    have hupd : Measurable (fun z : E3 => Function.update x i z) :=
      (measurable_update' (a := i)).comp (measurable_prodMk_left (x := x))
    exact (hmeas_c.comp hupd).aestronglyMeasurable
  · -- eventual domination
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [MeasureTheory.ae_restrict_iff' hBmeas]
    refine Filter.Eventually.of_forall (fun z hz => ?_)
    have hb : |cutProd (γ δ) ψ (Function.update x i z)| ≤ Cb := by
      rw [cutProd_apply, abs_mul]
      have hprod01 : (∏ j : Fin n, γ δ ((Function.update x i z) j)) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨Finset.prod_nonneg (fun j _ => (hγbdd δ hδ _).1),
         Finset.prod_le_one₀ (fun j _ => (hγbdd δ hδ _).1) (fun j _ => (hγbdd δ hδ _).2)⟩
      rw [abs_of_nonneg hprod01.1]
      calc (∏ j : Fin n, γ δ ((Function.update x i z) j)) * |ψ (Function.update x i z)|
          ≤ 1 * Cb :=
            mul_le_mul hprod01.2 (hψb _ (hxmem z hz)) (abs_nonneg _) zero_le_one
        _ = Cb := one_mul Cb
    rw [Real.norm_eq_abs]
    exact hb
  · -- the bound is integrable
    haveI : IsFiniteMeasure ((volume : Measure E3).restrict (dlBox ℓ d u)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hBfin⟩
    exact integrable_const Cb
  · -- a.e. convergence
    rw [MeasureTheory.ae_restrict_iff' hBmeas]
    have hae : ∀ᵐ z ∂(volume : Measure E3), boxMargin ℓ d u z ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simpa using volume_boxMargin_eq_zero_hyperplane_sharp (ℓ := ℓ) (d := d) u
    filter_upwards [hae] with z hz hzB
    refine tendsto_cutProd_of_good_box hγsupp hγone hγbdd ?_
    intro j
    rw [Function.update_apply]
    by_cases hj : j = i
    · rw [if_pos hj]
      exact hz
    · rw [if_neg hj]
      exact hgood j

/-! ## 5. Pointwise convergence of `boxQInd` -/

/-- **The FS box projection converges pointwise off the boundary.**  Since
`boxQInd volA B i Φ x = 1_B(xᵢ)·Φ(x) − |B|⁻¹∫_B Φ(x with xᵢ := z) dz · 1_B(xᵢ)`, this combines
the convergence of the state with that of the slot integral. -/
lemma tendsto_boxQInd_cutProd_aux {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) {u : E3}
    {ψ : X n → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) {Cb : ℝ}
    (hCb : 0 ≤ Cb) (hψb : ∀ x ∈ abox n ℓ, |ψ x| ≤ Cb)
    {γ : ℝ → E3 → ℝ}
    (hγcd : ∀ δ : ℝ, 0 < δ → ContDiff ℝ (⊤ : ENat) (γ δ))
    (hγsupp : ∀ δ : ℝ, 0 < δ → tsupport (γ δ) ⊆ dlBox ℓ d u)
    (hγone : ∀ δ : ℝ, 0 < δ → ∀ x, boxMargin ℓ d u x ≥ δ → γ δ x = 1)
    (hγbdd : ∀ δ : ℝ, 0 < δ → ∀ x, 0 ≤ γ δ x ∧ γ δ x ≤ 1)
    (i : Fin n) {x : X n} (hx : x ∈ abox n ℓ)
    (hgood : ∀ j : Fin n, boxMargin ℓ d u (x j) ≠ 0) :
    Filter.Tendsto (fun δ : ℝ => Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (dlBox ℓ d u) i (cutProd (γ δ) ψ) x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (dlBox ℓ d u) i (sharpBoxState (dlBox ℓ d u) ψ) x)) := by
  have h1 := tendsto_cutProd_of_good_box (ℓ := ℓ) (d := d) (ψ := ψ) hγsupp hγone hγbdd hgood
  have h2 := tendsto_boxPInd_cutProd_aux (ℓ := ℓ) (d := d) hℓ hψ hψb hγcd hγsupp hγone hγbdd
    i hx hgood
  simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
  exact (Filter.Tendsto.const_mul ((dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)) h1).sub
    (Filter.Tendsto.mul_const ((dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i))
      (Filter.Tendsto.const_mul (1 / Work.SmallBoxSliding.boxMass ℓ d u) h2))

/-! ## 6. The count convergence -/

theorem tendsto_cnPlusBoxInd_cutSharp {k : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3))
    {ψ : Submission.BoseGases.X k → ℝ} {K Cb : ℝ} {γ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hcut : Work.BoseFixB1B.IsCutFamily L d u K γ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox k L, |ψ x| ≤ Cb) :
    Filter.Tendsto (fun δ : ℝ => Work.UBBInputs8.cnPlusBoxInd L
        (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Work.BoseFixB1B.cutProd (γ δ) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Work.UBBInputs8.cnPlusBoxInd L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u)
        (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ))) := by
  classical
  have hγcd : ∀ δ : ℝ, 0 < δ → ContDiff ℝ (⊤ : ENat) (γ δ) :=
    fun δ hδ => (hcut.2 δ hδ).1
  have hγsupp : ∀ δ : ℝ, 0 < δ → tsupport (γ δ) ⊆ dlBox L d u :=
    fun δ hδ => (hcut.2 δ hδ).2.1
  have hγbdd : ∀ δ : ℝ, 0 < δ → ∀ x, 0 ≤ γ δ x ∧ γ δ x ≤ 1 :=
    fun δ hδ => (hcut.2 δ hδ).2.2.1
  have hγone : ∀ δ : ℝ, 0 < δ → ∀ x, boxMargin L d u x ≥ δ → γ δ x = 1 :=
    fun δ hδ => (hcut.2 δ hδ).2.2.2.1
  set B : Set E3 := dlBox L d u with hB
  set volA : ℝ := Work.SmallBoxSliding.boxMass L d u with hvolA
  have hBmeas : MeasurableSet B := Work.SmallBoxSliding.measurableSet_dlBox L d u
  have hBfin : (volume : Measure E3) B < ⊤ := Work.SmallBoxSliding.volume_dlBox_lt_top hL d u
  have hBsub : B ⊆ acube L := Work.SmallBoxSliding.dlBox_subset_acube L d u
  have hvolAeq : volA = (volume : Measure E3).real B :=
    Work.SmallBoxSliding.boxMass_eq_measureReal L d u
  haveI : IsFiniteMeasure ((volume : Measure (X k)).restrict (abox k L)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.abox_lt_top k L hL.le⟩
  -- the two states are bounded by `Cb` on the box
  have hcut_b : ∀ δ : ℝ, 0 < δ → ∀ y : X k,
      (∀ j : Fin k, y j ∈ acube L) → |cutProd (γ δ) ψ y| ≤ Cb := by
    intro δ hδ y hy
    rw [cutProd_apply, abs_mul]
    have hprod01 : (∏ j : Fin k, γ δ (y j)) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨Finset.prod_nonneg (fun j _ => (hγbdd δ hδ (y j)).1),
       Finset.prod_le_one₀ (fun j _ => (hγbdd δ hδ (y j)).1)
         (fun j _ => (hγbdd δ hδ (y j)).2)⟩
    rw [abs_of_nonneg hprod01.1]
    calc (∏ j : Fin k, γ δ (y j)) * |ψ y| ≤ 1 * Cb :=
          mul_le_mul hprod01.2 (hψb y ((Submission.BoseGases.mem_abox_iff k L y).mpr hy))
            (abs_nonneg _) zero_le_one
      _ = Cb := one_mul Cb
  -- the box margins of the coordinates vanish only on a null set
  have hgoodae : ∀ᵐ x ∂((volume : Measure (X k)).restrict (abox k L)),
      ∀ j : Fin k, boxMargin L d u (x j) ≠ 0 :=
    MeasureTheory.ae_mono Measure.restrict_le_self (ae_forall_boxMargin_coord_ne_zero_sharp k u)
  -- the count of each slot converges
  have key : ∀ i : Fin k, Filter.Tendsto (fun δ : ℝ =>
      ∫ x in abox k L, (Work.UBBInputs8.boxQInd volA B i (cutProd (γ δ) ψ) x) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ x in abox k L,
        (Work.UBBInputs8.boxQInd volA B i (sharpBoxState B ψ) x) ^ 2)) := by
    intro i
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (F := fun δ (x : X k) =>
        (Work.UBBInputs8.boxQInd volA B i (cutProd (γ δ) ψ) x) ^ 2)
      (f := fun (x : X k) =>
        (Work.UBBInputs8.boxQInd volA B i (sharpBoxState B ψ) x) ^ 2)
      (bound := fun _ => (2 * Cb) ^ 2) ?_ ?_ ?_ ?_
    · -- eventual a.e. strong measurability
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hΨm : Measurable (cutProd (γ δ) ψ) := by
        have h1 : Continuous (fun y : X k => ∏ j : Fin k, γ δ (y j)) :=
          continuous_finsetProd Finset.univ
            (fun j _ => (hγcd δ hδ).continuous.comp (continuous_apply j))
        exact (h1.mul hψ.continuous).measurable
      exact ((Work.SlotWord.measurable_boxQInd volA B hBmeas i hΨm).pow_const 2).aestronglyMeasurable
    · -- eventual domination
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable k L)]
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb := abs_boxQInd_le_two_mul_sharp (n := k) (ℓ := L) (volA := volA) (Cb := Cb) (B := B)
        hBsub hvolAeq hBfin hCb (hcut_b δ hδ) i x
        ((Submission.BoseGases.mem_abox_iff k L x).mp hx)
      calc (Work.UBBInputs8.boxQInd volA B i (cutProd (γ δ) ψ) x) ^ 2
          = |Work.UBBInputs8.boxQInd volA B i (cutProd (γ δ) ψ) x| ^ 2 := by rw [sq_abs]
        _ ≤ (2 * Cb) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    · -- the dominating function is integrable
      exact integrable_const _
    · -- a.e. pointwise convergence
      filter_upwards [hgoodae,
        MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable k L)]
        with x hgood hx
      have hpt := tendsto_boxQInd_cutProd_aux (n := k) (ℓ := L) (d := d) hL hψ hCb hψb hγcd
        hγsupp hγone hγbdd i hx hgood
      simpa [pow_two] using hpt.mul hpt
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin k)) (fun i _ => key i)
  show Filter.Tendsto (fun δ : ℝ => ∑ i : Fin k, ∫ x in abox k L,
      (Work.UBBInputs8.boxQInd volA B i (cutProd (γ δ) ψ) x) ^ 2)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds (∑ i : Fin k, ∫ x in abox k L,
      (Work.UBBInputs8.boxQInd volA B i (sharpBoxState B ψ) x) ^ 2))
  exact hsum

end Work.BoseFixB1B
