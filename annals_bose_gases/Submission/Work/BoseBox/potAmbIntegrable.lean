import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.LocPotBox
import Submission.Work.BoseBox.abs_potBracketG_le
import Submission.Work.BoseBox.coverU_volume
import Submission.Work.BoseBox.potAmb_support
import Submission.Work.BoseBox.stronglyMeasurable_potIntegrandG
import Submission.Work.ModeLatticeR3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.potAmbIntegrable` — the potential word is integrable in the translation

This module proves the potential half of the `C0` side condition `CWordIntegrable`
(`Submission/Work/BoseBox/CNodeDefs.lean`): for FS's potential regime
(`v ≥ 0` radial, compactly supported in `ball 0 R`, `L¹`, `R ≤ ℓ·r₀`, and the
convolution lower bound `1/2 ≤ (χ⋆χ)(x)` for `‖x‖ ≤ r₀`) and every smooth state
`Ψ` supported in the corner box `[0,L]³ᴺ`, the localised potential word

`u ↦ potAmb N L ℓ μ v h u Ψ = ∫_{Ωᴺ}(Ψ x)²·(−μΣᵢ∫_{Λ(u)}w_{1,u}(xᵢ,y)dy
                                        + Σ_{i<j}w_u(xᵢ,xⱼ)) dx`

is integrable over the localisation region `coverU ℓ L`.

## Route

`potAmb` is, definitionally, the `x`-integral of `(Ψ x)²` against the bracket
`potBracket`; using `potBracket_eq_G` the bracket may equally be read as its
full-space form `potBracketG` with kernels `v`, `g₀ v h`.  The proof is therefore

1. *(measurability)* `v` and `g₀ v h` are only a.e. measurable, so — exactly as in
   `Work.BoseBox.potAmb_integral` — one replaces them by measurable representatives
   `wv`, `wg`, observes that the `(u,x)`-integrands `F` (kernels `v`, `g₀`) and `F'`
   (kernels `wv`, `wg`) agree off a product-null set (the bad set is the union of
   the null sets `{x | x_{p.1} − x_{p.2} ∈ t}` over the pairs, `t` a measurable
   null superset of the set where `v ≠ wv`), and reads off
   `AEStronglyMeasurable F` from the strong measurability of `F'`
   (`stronglyMeasurable_potIntegrandG`);
2. *(domination)* `|F|` is dominated by the integrable function
   `(Ψ x)²·(|μ|N·2χ²·∫|g₀| + χ²Σ_p|v(x_{p.1}−x_{p.2})|)` of
   `Work.BoseBox.integrable_domination` via the pointwise bracket bound
   `Work.BoseBox.abs_potBracketG_le`;
3. *(Fubini)* hence `F` is integrable over the product
   `(volume↾coverU ℓ L) × (volume↾box N L)`, and
   `MeasureTheory.Integrable.integral_prod_left` makes the `x`-integral integrable
   in `u`.  `potBracket_eq_G` converts back to the sliding-box bracket of `potAmb`.

Note that the *finiteness* of the `u`-integral is genuine here: the localising
windows `χ_u` confine every fibre integral to `Λ(u)`, so all bounds in step 2 are
uniform in `u` and only the finite volume of `coverU ℓ L` is used.
-/

noncomputable section

namespace Work.BoseBox

local notation "P3" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory Metric
open scoped Real BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- Integrability of the dominating function for the `potAmb` integrand, with the *smooth*
(not analytic) hypothesis on `Ψ` that the main theorem supplies.  This is the (private)
`Work.BoseBox.potAmb_integral` helper, restated here for reuse. -/
private lemma integrable_domination_smooth {N : ℕ} {v : P3 → ℝ} {ℓ L A B : ℝ}
    (hℓ : 0 < ℓ) (hL : 0 < L) (hv1 : MeasureTheory.MemLp v 1)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    MeasureTheory.Integrable
      (fun p : P3 × Submission.BoseGases.X N =>
        (Ψ p.2) ^ 2 *
          (A + B * ∑ q ∈ Submission.BoseGases.pairSet N,
            |v (p.2 q.1 - p.2 q.2)|))
      ((MeasureTheory.volume.restrict (Work.BoseBox.coverU ℓ L)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (_root_.BoseGases.box N L))) := by
  have hvabs : MeasureTheory.MemLp (fun y : P3 => |v y|) 1 := by
    simpa only [Real.norm_eq_abs] using hv1.norm
  have hbase : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => (Ψ x) ^ 2) (_root_.BoseGases.box N L)
      MeasureTheory.volume :=
    Submission.BoseGases.es_sq_integrableOn hL hΨ.continuous
  have hpair : ∀ q ∈ Submission.BoseGases.pairSet N,
      MeasureTheory.Integrable
        (fun x : Submission.BoseGases.X N => (Ψ x) ^ 2 * |v (x q.1 - x q.2)|)
        (MeasureTheory.volume.restrict (_root_.BoseGases.box N L)) := by
    intro q hq
    have hne : q.1 ≠ q.2 := by
      simpa only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ,
        true_and] using hq
    exact Submission.BoseGases.es_sq_v_integrableOn (i := q.1) (j := q.2) hL hvabs hΨ hne
  have hsum : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N =>
        ∑ q ∈ Submission.BoseGases.pairSet N, (Ψ x) ^ 2 * |v (x q.1 - x q.2)|)
      (MeasureTheory.volume.restrict (_root_.BoseGases.box N L)) :=
    MeasureTheory.integrable_finsetSum (Submission.BoseGases.pairSet N)
      (fun q hq => hpair q hq)
  have hmain : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N =>
        (Ψ x) ^ 2 * (A + B * ∑ q ∈ Submission.BoseGases.pairSet N,
          |v (x q.1 - x q.2)|))
      (MeasureTheory.volume.restrict (_root_.BoseGases.box N L)) := by
    refine ((hbase.const_mul A).add (hsum.const_mul B)).congr ?_
    filter_upwards with x
    simp only [Pi.add_apply]
    rw [show (∑ q ∈ Submission.BoseGases.pairSet N, (Ψ x) ^ 2 * |v (x q.1 - x q.2)|)
        = (Ψ x) ^ 2 * (∑ q ∈ Submission.BoseGases.pairSet N, |v (x q.1 - x q.2)|) from by
      rw [Finset.mul_sum]]
    ring
  haveI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (Work.BoseBox.coverU ℓ L)) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Work.BoseBox.coverU_volume hℓ hL.le]
    exact ENNReal.ofReal_lt_top
  exact hmain.comp_snd (MeasureTheory.volume.restrict (Work.BoseBox.coverU ℓ L))

theorem potAmbIntegrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R r₀ : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hv_nonneg : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (hC : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ r₀ →
      1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x)
    {ℓ μ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hRℓ : R ≤ ℓ * r₀) {N : ℕ}
    (Ψ : Submission.BoseGases.X N → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hsupp : tsupport Ψ ⊆ _root_.BoseGases.box N L) :
    MeasureTheory.IntegrableOn
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseBox.potAmb N L ℓ μ v h u Ψ)
      (Work.BoseBox.coverU ℓ L) := by
  -- ## 0. the potential regime, and the derived support/integrability facts for `g₀`
  have hg0_int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  -- ## 1. measurable representatives of the two (only a.e. measurable) kernels
  have hvInt : MeasureTheory.Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hvae : AEMeasurable v := hvInt.aemeasurable
  let wv : P3 → ℝ := AEMeasurable.mk v hvae
  have hwv_meas : Measurable wv := AEMeasurable.measurable_mk hvae
  have hwv_eq : v =ᵐ[MeasureTheory.volume] wv := AEMeasurable.ae_eq_mk hvae
  have hg0ae : AEMeasurable (Submission.BoseGases.g0 v h) :=
    hg0_int.aemeasurable
  let wg : P3 → ℝ := AEMeasurable.mk (Submission.BoseGases.g0 v h) hg0ae
  have hwg_meas : Measurable wg := AEMeasurable.measurable_mk hg0ae
  have hwg_eq : (Submission.BoseGases.g0 v h) =ᵐ[MeasureTheory.volume] wg :=
    AEMeasurable.ae_eq_mk hg0ae
  -- ## 2. a null set off which `v` and its representative agree
  have hN0 : MeasureTheory.volume {z : P3 | ¬ (v z = wv z)} = 0 :=
    MeasureTheory.ae_iff.mp hwv_eq
  rcases MeasureTheory.exists_measurable_superset_of_null hN0 with ⟨t, hNt, htm, ht0⟩
  have hpre : ∀ p : Fin N × Fin N, p ∈ Submission.BoseGases.pairSet N →
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (_root_.BoseGases.box N L)
        {x : Submission.BoseGases.X N | x p.1 - x p.2 ∈ t} = 0 := by
    intro p hp
    have hne : p.1 ≠ p.2 := by
      simpa only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ,
        true_and] using hp
    exact Submission.BoseGases.null_preimage_pair hL htm ht0 p.1 p.2 hne
  have hBads_null :
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (_root_.BoseGases.box N L)
        (⋃ p ∈ Submission.BoseGases.pairSet N,
          {x : Submission.BoseGases.X N | x p.1 - x p.2 ∈ t}) = 0 := by
    apply le_antisymm _ bot_le
    calc (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
            (_root_.BoseGases.box N L)
            (⋃ p ∈ Submission.BoseGases.pairSet N,
              {x : Submission.BoseGases.X N | x p.1 - x p.2 ∈ t})
          ≤ ∑ p ∈ Submission.BoseGases.pairSet N,
              (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
                (_root_.BoseGases.box N L)
                {x : Submission.BoseGases.X N | x p.1 - x p.2 ∈ t} :=
            MeasureTheory.measure_biUnion_finset_le _ _
        _ = 0 := Finset.sum_eq_zero (fun p hp => hpre p hp)
  -- ## 3. the two spellings of the bracket agree a.e. against a big-box state
  have hbr : ∀ (u a : P3), potBr ℓ (Submission.BoseGases.g0 v h) u a = potBr ℓ wg u a := by
    intro u a
    simp only [potBr]
    apply MeasureTheory.integral_congr_ae
    have hq := (Submission.BoseGases.measurePreserving_sub_left a).quasiMeasurePreserving
    filter_upwards [hq.ae_eq_comp hwg_eq] with y hy
    have hy' : (Submission.BoseGases.g0 v h) (a - y) = wg (a - y) := hy
    simp only [Submission.BoseGases.wLoc, Submission.BoseGases.wScaled, hy']
  have hpair : ∀ (u : P3) {x : Submission.BoseGases.X N},
      (∀ p ∈ Submission.BoseGases.pairSet N, x p.1 - x p.2 ∉ t) →
      (∑ p ∈ Submission.BoseGases.pairSet N, Submission.BoseGases.wLoc ℓ v u (x p.1) (x p.2))
        = ∑ p ∈ Submission.BoseGases.pairSet N,
            Submission.BoseGases.wLoc ℓ wv u (x p.1) (x p.2) := by
    intro u x hx
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hvz : v (x p.1 - x p.2) = wv (x p.1 - x p.2) := by
      by_contra hne
      exact hx p hp (hNt hne)
    simp only [Submission.BoseGases.wLoc, Submission.BoseGases.wScaled, hvz]
  -- ## 4. the `(u,x)`-integrand, and the `(uncurried)` Fubini
  let F : P3 × Submission.BoseGases.X N → ℝ :=
    fun p => (Ψ p.2) ^ 2 * potBracketG N ℓ μ v (Submission.BoseGases.g0 v h) p.1 p.2
  let F' : P3 × Submission.BoseGases.X N → ℝ :=
    fun p => (Ψ p.2) ^ 2 * potBracketG N ℓ μ wv wg p.1 p.2
  have hFF'_pt : ∀ (u : P3) (x : Submission.BoseGases.X N),
      (∀ p ∈ Submission.BoseGases.pairSet N, x p.1 - x p.2 ∉ t) → F (u, x) = F' (u, x) := by
    intro u x hx
    have h1 : (∑ i : Fin N, potBr ℓ (Submission.BoseGases.g0 v h) u (x i))
        = ∑ i : Fin N, potBr ℓ wg u (x i) :=
      Finset.sum_congr rfl (fun i _ => hbr u (x i))
    have h2 := hpair u hx
    show (Ψ x) ^ 2 * potBracketG N ℓ μ v (Submission.BoseGases.g0 v h) u x
        = (Ψ x) ^ 2 * potBracketG N ℓ μ wv wg u x
    simp only [potBracketG, h1, h2]
  have hsub : {p : P3 × Submission.BoseGases.X N | ¬ (F p = F' p)}
      ⊆ Set.univ ×ˢ (⋃ p ∈ Submission.BoseGases.pairSet N,
          {x : Submission.BoseGases.X N | x p.1 - x p.2 ∈ t}) := by
    intro p hp
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and] at hp ⊢
    by_contra hbad
    refine hp (hFF'_pt p.1 p.2 ?_)
    intro q hq hmem
    exact hbad (Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, hmem⟩⟩)
  have hnull : ((MeasureTheory.volume : MeasureTheory.Measure P3).restrict
      (Work.BoseBox.coverU ℓ L)).prod
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (_root_.BoseGases.box N L))
      (Set.univ ×ˢ (⋃ p ∈ Submission.BoseGases.pairSet N,
          {x : Submission.BoseGases.X N | x p.1 - x p.2 ∈ t})) = 0 := by
    rw [MeasureTheory.Measure.prod_prod, hBads_null, mul_zero]
  have hFF' : F =ᵐ[((MeasureTheory.volume : MeasureTheory.Measure P3).restrict
      (Work.BoseBox.coverU ℓ L)).prod
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (_root_.BoseGases.box N L))] F' :=
    MeasureTheory.ae_iff.mpr (MeasureTheory.measure_mono_null hsub hnull)
  have hFmeas : MeasureTheory.AEStronglyMeasurable F
      (((MeasureTheory.volume : MeasureTheory.Measure P3).restrict
        (Work.BoseBox.coverU ℓ L)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (_root_.BoseGases.box N L))) := by
    have hF'meas : MeasureTheory.StronglyMeasurable F' := by
      show MeasureTheory.StronglyMeasurable
        (fun p : P3 × Submission.BoseGases.X N =>
          (Ψ p.2) ^ 2 * potBracketG N ℓ μ wv wg p.1 p.2)
      exact Work.BoseBox.stronglyMeasurable_potIntegrandG (N := N) (ℓ := ℓ) (μ := μ)
        (vK := wv) (gK := wg) hwv_meas hwg_meas (Ψ := Ψ) hΨ.continuous
    exact hF'meas.aestronglyMeasurable.congr hFF'.symm
  have hbound : ∀ᵐ p ∂(((MeasureTheory.volume : MeasureTheory.Measure P3).restrict
      (Work.BoseBox.coverU ℓ L)).prod
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (_root_.BoseGases.box N L))),
      ‖F p‖ ≤ (Ψ p.2) ^ 2 * (|μ| * (N : ℝ) * (2 * chiSup ^ 2 * g0mass v h)
        + chiSup ^ 2 * ∑ q ∈ Submission.BoseGases.pairSet N,
            |v (p.2 q.1 - p.2 q.2)|) := by
    apply Filter.Eventually.of_forall
    intro p
    have hb := Work.BoseBox.abs_potBracketG_le (N := N) (h := h) (ℓ := ℓ) (μ := μ)
      hR hr₀ hv_supp hC hℓ hRℓ p.1 p.2
    show ‖(Ψ p.2) ^ 2 * potBracketG N ℓ μ v (Submission.BoseGases.g0 v h) p.1 p.2‖
      ≤ (Ψ p.2) ^ 2 * (|μ| * (N : ℝ) * (2 * Work.BoseBox.chiSup ^ 2 * Work.BoseBox.g0mass v h)
        + Work.BoseBox.chiSup ^ 2 * ∑ q ∈ Submission.BoseGases.pairSet N,
            |v (p.2 q.1 - p.2 q.2)|)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (Ψ p.2))]
    exact mul_le_mul_of_nonneg_left hb (sq_nonneg (Ψ p.2))
  have hGint : MeasureTheory.Integrable
      (fun p : P3 × Submission.BoseGases.X N =>
        (Ψ p.2) ^ 2 * (|μ| * (N : ℝ) * (2 * Work.BoseBox.chiSup ^ 2 * Work.BoseBox.g0mass v h)
          + Work.BoseBox.chiSup ^ 2 * ∑ q ∈ Submission.BoseGases.pairSet N,
              |v (p.2 q.1 - p.2 q.2)|))
      (((MeasureTheory.volume : MeasureTheory.Measure P3).restrict
        (Work.BoseBox.coverU ℓ L)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (_root_.BoseGases.box N L))) :=
    integrable_domination_smooth hℓ hL hv1 hΨ
  -- ## 5. the product-measure integrability of the `(u,x)`-integrand
  have hInt : MeasureTheory.Integrable
      (Function.uncurry (fun (u : P3) (x : Submission.BoseGases.X N) =>
        (Ψ x) ^ 2 * potBracketG N ℓ μ v (Submission.BoseGases.g0 v h) u x))
      (((MeasureTheory.volume : MeasureTheory.Measure P3).restrict
        (Work.BoseBox.coverU ℓ L)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (_root_.BoseGases.box N L))) :=
    MeasureTheory.Integrable.mono' hGint hFmeas hbound
  -- ## 6. Fubini: the `x`-integral is integrable as a function of `u`
  have hfab := hInt.integral_prod_left
  have hgoal : MeasureTheory.Integrable
      (fun u : P3 => ∫ x in _root_.BoseGases.box N L,
        (Ψ x) ^ 2 * potBracket N ℓ μ v h u x)
      (MeasureTheory.volume.restrict (Work.BoseBox.coverU ℓ L)) := by
    refine hfab.congr ?_
    filter_upwards with u
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [Function.uncurry_apply_pair]
    exact congrArg (fun z : ℝ => (Ψ x) ^ 2 * z) (potBracket_eq_G hℓ u x).symm
  show MeasureTheory.Integrable
      (fun u : P3 => Work.BoseBox.potAmb N L ℓ μ v h u Ψ)
      (MeasureTheory.volume.restrict (Work.BoseBox.coverU ℓ L))
  simpa only [potAmb_eq_integral] using hgoal

end Work.BoseBox
