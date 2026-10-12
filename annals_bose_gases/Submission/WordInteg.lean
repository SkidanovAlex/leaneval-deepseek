import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
import ChallengeDeps
import Submission.KernelFibreBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5 — full-box integrability for bounded·L¹-pair kernels (`abox N ℓ`)

Every Section-5+ estimate over the *centred* analysis box `abox N ℓ`
(PotWords words, potapp-family bounds, a priori bounds, ...) involves
integrals over `x ∈ abox N ℓ` of monomial integrands

    (bounded measurable factor g x) · h (xᵢ − xⱼ)          h ∈ L¹(ℝ³),
    (bounded measurable factor g x) · wPair ℓ h (xᵢ) (xⱼ),  h ∈ L¹(ℝ³) supported in ball 0 R,

where the bounded factor is a product of `P`/`Q` images (`aP ℓ i Φ x`,
`aQ ℓ i Φ x`, bounded by `sup|Φ|` via `Q0Sector.aP_abs_le`; `ω = w₀(xᵢ−xⱼ)`
bounded a.e. by 1) or of similar terms.  This module proves the
per-monomial `IntegrableOn` facts over `abox N ℓ` and the quantitative
bounds

    ∫_{abox N ℓ} |h (xᵢ − xⱼ)|  ≤  (ℓ³)^(N−1) · ∫|h|
    ∫_{abox N ℓ} g·|h (xᵢ − xⱼ)| ≤  B · (ℓ³)^(N−1) · ∫|h|      (|g| ≤ B a.e.)
    |∫_{abox N ℓ} g·wPair(ℓ,h)(xᵢ,xⱼ)| ≤ B·(ℓ³)^(N−1)·2·chiSup·(√chiNormSq)⁻¹·∫|h|

that every later bound (KernelFibreBound/OneBodyBound-style fibre bounds
inside the box, QuadCS, potapp-FULL, a priori bounds) reduces to.  It is the
`box N L` machinery of `Submission/Potential.lean`
(`lintegral_pair_eq_iterated`, `null_preimage_pair`,
`integrableOn_abs_pair_of_measurable`, `integrableOn_pair_v`) ported to the
centred box `abox N ℓ`, using `CentreBox` (`restrict_abox_eq_pi`,
`measurePreserving_coordSplitFinAcube`, `acube_*`) and
`Q0Sector.abox_peel_mp` / `abox_integral_peel`.

## Route notes (for the child)

1. **Peel identity.** `lintegral_abox_pair_eq_iterated` mirrors
   `Potential.lintegral_pair_eq_iterated` word-for-word, with
   `restrict_box_eq_pi` ↦ `CentreBox.restrict_abox_eq_pi`,
   `cube L` ↦ `acube ℓ`, and `measurePreserving_coordSplitFin` ↦
   `measurePreserving_coordSplitFinAcube`.
2. `lintegral_acube_sub_le` mirrors `Potential.lintegral_sub_le` (`cube` ↦
   `acube`, using `measurePreserving_sub_right` from `Potential` on the full
   space and `acube ℓ ⊆ Set.univ`).
3. `lintegral_abox_pair_lt_top`, `abox_null_preimage_pair` mirror the
   same-named `Potential` lemmas; then `integrableOn_abs_sub_abox` mirrors
   `integrableOn_pair_v` (measurable representative of `h`).
4. `setIntegral_abs_sub_abox_le`: for `N ≥ 2` peel once along coordinate `i`
   (`abox_integral_peel`, or the lintegral version) leaving `X (N−1)` outer
   coordinates of total mass `(ℓ³)^(N−1)`, bound the inner `b`-integral by
   `∫|h|` (translation-invariance + `acube ⊆ ℝ³`); `N ≤ 1` is vacuous from
   `hij`.
5. The bounded-factor statements use `AEStronglyMeasurable g` + the a.e.
   bound `|g x| ≤ B` on the restricted measure; integrate
   `∫|g·h(xᵢ−xⱼ)| ≤ B·∫|h(xᵢ−xⱼ)|` via `lintegral_mono` and
   `IntegrableOn.of_bound`/`Integrable.mono'`.
6. The `wPair` bounds combine `Q0Chosen.wPair_abs_bound`
   (`|wPair ℓ h x y| ≤ chiScale ℓ x · (2·(√chiNormSq)⁻¹)·|h (x−y)|`) with
   `abs_chiScale_le_chiSup` (KernelFibreBound), giving the constant
   `chiSup · 2 · (Real.sqrt chiNormSq)⁻¹`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma lintegral_abox_pair_eq_iterated {n : ℕ} {ℓ : ℝ} {G : ℝ³ → ℝ≥0∞} (hG : Measurable G)
    (i j : Fin (n + 1)) (j' : Fin n) (hjj' : i.succAbove j' = j) :
    (∫⁻ x, G (x i - x j) ∂((volume : Measure (X (n + 1))).restrict (abox (n + 1) ℓ))) =
      (∫⁻ a : X n, ∫⁻ b : ℝ³, G (b - a j')
        ∂((volume : Measure ℝ³).restrict (acube ℓ))
        ∂((volume : Measure (X n)).restrict (abox n ℓ))) := by
  let μ' : Measure ℝ³ := (volume : Measure ℝ³).restrict (acube ℓ)
  have hbox : (volume : Measure (X (n + 1))).restrict (abox (n + 1) ℓ) =
      Measure.pi (fun _ : Fin (n + 1) => μ') := by
    dsimp [μ']
    exact restrict_abox_eq_pi (n + 1) ℓ
  rw [hbox]
  have hF : Measurable (fun q : ℝ³ × X n => G (q.1 - q.2 j')) := by
    fun_prop
  have hpt : ∀ x : X (n + 1),
      (fun q : ℝ³ × X n => G (q.1 - q.2 j'))
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i x) = G (x i - x j) := by
    intro x
    change G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i x).1
        - (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i x).2 j') = G (x i - x j)
    congr 1
    rw [show ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i x).1) = x i by rfl,
      show ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i x).2 j') =
        x (i.succAbove j') by rfl, hjj']
  have htr := MeasureTheory.MeasurePreserving.lintegral_comp
    (measurePreserving_coordSplitFinAcube n ℓ i) hF
  calc
    (∫⁻ x : X (n + 1), G (x i - x j) ∂(Measure.pi (fun _ : Fin (n + 1) => μ')))
        = ∫⁻ p : ℝ³ × X n, G (p.1 - p.2 j')
            ∂(μ'.prod (Measure.pi (fun _ : Fin n => μ'))) := by
          rw [← htr]
          apply lintegral_congr_ae
          filter_upwards with x
          exact (hpt x).symm
    _ = (∫⁻ a : X n, ∫⁻ b : ℝ³, G (b - a j')
          ∂((volume : Measure ℝ³).restrict (acube ℓ))
          ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ³).restrict (acube ℓ)))) := by
          simpa [μ'] using (lintegral_prod_symm (μ := μ') (ν := (Measure.pi (fun _ : Fin n => μ')))
            (f := fun q : ℝ³ × X n => G (q.1 - q.2 j')) hF.aemeasurable)
    _ = (∫⁻ a : X n, ∫⁻ b : ℝ³, G (b - a j')
          ∂((volume : Measure ℝ³).restrict (acube ℓ))
          ∂((volume : Measure (X n)).restrict (abox n ℓ))) := by
          rw [restrict_abox_eq_pi n ℓ]




lemma map_restrict_acube_sub_le (ℓ : ℝ) (c : ℝ³) :
    ((volume : Measure ℝ³).restrict (acube ℓ)).map (fun b : ℝ³ => b - c) ≤ (volume : Measure ℝ³) := by
  rw [Measure.le_iff]
  intro s hs
  have hmeas : MeasurableSet ((fun b : ℝ³ => b - c) ⁻¹' s) := by measurability
  rw [Measure.map_apply (f := (fun b : ℝ³ => b - c)) (by measurability) hs]
  rw [Measure.restrict_apply hmeas]
  calc
    volume ((fun b : ℝ³ => b - c) ⁻¹' s ∩ acube ℓ) ≤ volume ((fun b : ℝ³ => b - c) ⁻¹' s) :=
      measure_mono (by intro x hx; exact hx.1)
    _ = volume s := by
      have hmp := measurePreserving_sub_right c
      rw [← Measure.map_apply (f := (fun b : ℝ³ => b - c)) (by measurability) hs]
      rw [hmp.map_eq]

lemma lintegral_acube_sub_le (ℓ : ℝ) {G : ℝ³ → ℝ≥0∞} (hG : Measurable G) (c : ℝ³) :
    (∫⁻ b : ℝ³, G (b - c) ∂((volume : Measure ℝ³).restrict (acube ℓ))) ≤
      (∫⁻ y : ℝ³, G y) := by
  have hlin : (∫⁻ y : ℝ³, G y ∂((volume : Measure ℝ³).restrict (acube ℓ)).map (fun b : ℝ³ => b - c))
      = (∫⁻ b, G (b - c) ∂((volume : Measure ℝ³).restrict (acube ℓ))) :=
    MeasureTheory.lintegral_map (μ := (volume : Measure ℝ³).restrict (acube ℓ))
      (f := G) (g := (fun b : ℝ³ => b - c)) hG (by measurability)
  rw [← hlin]
  exact lintegral_mono' (map_restrict_acube_sub_le ℓ c) le_rfl



lemma lintegral_abox_pair_lt_top {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {G : ℝ³ → ℝ≥0∞}
    (hG : Measurable G) (hfin : (∫⁻ y : ℝ³, G y) < (∞ : ℝ≥0∞)) (i j : Fin N) (hij : i ≠ j) :
    (∫⁻ x, G (x i - x j) ∂((volume : Measure (X N)).restrict (abox N ℓ))) < (∞ : ℝ≥0∞) := by
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      let j' : Fin n := Classical.choose (Fin.exists_succAbove_eq (x := j) (y := i) hij.symm)
      have hjj' : i.succAbove j' = j := by
        simpa [j'] using (Classical.choose_spec (Fin.exists_succAbove_eq (x := j) (y := i) hij.symm))
      have heq := lintegral_abox_pair_eq_iterated (ℓ := ℓ) (G := G) hG i j j' hjj'
      rw [heq]
      have hle : (∫⁻ a : X n, ∫⁻ b : ℝ³, G (b - a j')
            ∂((volume : Measure ℝ³).restrict (acube ℓ))
            ∂((volume : Measure (X n)).restrict (abox n ℓ)))
          ≤ (∫⁻ a : X n, (∫⁻ y : ℝ³, G y)
              ∂((volume : Measure (X n)).restrict (abox n ℓ))) := by
        apply lintegral_mono_ae
        filter_upwards with a
        exact lintegral_acube_sub_le ℓ hG (a j')
      refine lt_of_le_of_lt hle ?_
      rw [lintegral_const]
      have hκ : ((volume : Measure (X n)).restrict (abox n ℓ)) Set.univ < (∞ : ℝ≥0∞) := by
        rw [Measure.restrict_apply_univ]
        exact abox_lt_top n ℓ hℓ.le
      exact ENNReal.mul_lt_top hfin hκ



lemma abox_null_preimage_pair {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {s : Set ℝ³}
    (hs : MeasurableSet s) (hs0 : volume s = 0) (i j : Fin N) (hij : i ≠ j) :
    (volume : Measure (X N)).restrict (abox N ℓ) {x | x i - x j ∈ s} = 0 := by
  have hG : Measurable (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) := by
    exact Measurable.indicator (by measurability : Measurable fun _ : ℝ³ => (1 : ℝ≥0∞)) hs
  have hzero : (∫⁻ y : ℝ³, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) y) = 0 := by
    rw [lintegral_indicator hs]
    simp [hs0]
  let t : Set (X N) := {x : X N | x i - x j ∈ s}
  have htmeas : MeasurableSet t := by
    dsimp [t]
    measurability
  have hval : (volume : Measure (X N)).restrict (abox N ℓ) t
      = ∫⁻ x, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) (x i - x j)
          ∂((volume : Measure (X N)).restrict (abox N ℓ)) := by
    calc
      (volume : Measure (X N)).restrict (abox N ℓ) t
          = ∫⁻ x in t, (1 : ℝ≥0∞) ∂((volume : Measure (X N)).restrict (abox N ℓ)) := by
              rw [lintegral_const]
              rw [Measure.restrict_apply_univ]
              simp
      _ = ∫⁻ x, (t.indicator (fun _ : X N => (1 : ℝ≥0∞))) x
            ∂((volume : Measure (X N)).restrict (abox N ℓ)) := by
              rw [lintegral_indicator htmeas]
      _ = ∫⁻ x, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) (x i - x j)
            ∂((volume : Measure (X N)).restrict (abox N ℓ)) := by
              apply lintegral_congr_ae
              filter_upwards with x
              by_cases h : x i - x j ∈ s <;> simp [t, h]
  rw [hval]
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      let j' : Fin n := Classical.choose (Fin.exists_succAbove_eq (x := j) (y := i) hij.symm)
      have hjj' : i.succAbove j' = j := by
        simpa [j'] using (Classical.choose_spec (Fin.exists_succAbove_eq (x := j) (y := i) hij.symm))
      have heq := lintegral_abox_pair_eq_iterated (ℓ := ℓ)
        (G := s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) hG i j j' hjj'
      rw [heq]
      have hin : ∀ a : X n,
          (∫⁻ b : ℝ³, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) (b - a j')
            ∂((volume : Measure ℝ³).restrict (acube ℓ))) ≤
            ∫⁻ y : ℝ³, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) y := by
        intro a
        exact lintegral_acube_sub_le ℓ hG (a j')
      have hle : (∫⁻ a : X n, ∫⁻ b : ℝ³, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) (b - a j')
            ∂((volume : Measure ℝ³).restrict (acube ℓ))
            ∂((volume : Measure (X n)).restrict (abox n ℓ)))
          ≤ (∫⁻ a : X n, (∫⁻ y : ℝ³, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) y)
              ∂((volume : Measure (X n)).restrict (abox n ℓ))) := by
        apply lintegral_mono_ae
        filter_upwards with a
        exact hin a
      apply le_antisymm
      · calc
          (∫⁻ a : X n, ∫⁻ b : ℝ³, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) (b - a j')
              ∂((volume : Measure ℝ³).restrict (acube ℓ))
              ∂((volume : Measure (X n)).restrict (abox n ℓ)))
              ≤ (∫⁻ a : X n, (∫⁻ y : ℝ³, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) y)
                  ∂((volume : Measure (X n)).restrict (abox n ℓ))) := hle
          _ = (∫⁻ a : X n, 0
                ∂((volume : Measure (X n)).restrict (abox n ℓ))) := by
                rw [hzero]
          _ = 0 := by
                rw [lintegral_const]
                simp
      · positivity





lemma integrableOn_abs_pair_abox_of_measurable {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {w : ℝ³ → ℝ} (hwm : Measurable w) (hfin : (∫⁻ y : ℝ³, ‖w y‖ₑ) < (∞ : ℝ≥0∞))
    (i j : Fin N) (hij : i ≠ j) :
    IntegrableOn (fun x : X N => |w (x i - x j)|) (abox N ℓ) volume := by
  let G : ℝ³ → ℝ≥0∞ := fun y => ENNReal.ofReal |w y|
  have hG : Measurable G := by
    dsimp [G]
    fun_prop
  have hGfin : (∫⁻ y : ℝ³, G y) < (∞ : ℝ≥0∞) := by
    have hpt : (fun y : ℝ³ => G y) = fun y : ℝ³ => ‖w y‖ₑ := by
      funext y
      dsimp [G]
      rw [← ofReal_norm (w y)]
      rfl
    rw [hpt]
    exact hfin
  have hlt : (∫⁻ x : X N, G (x i - x j) ∂(volume.restrict (abox N ℓ))) < (∞ : ℝ≥0∞) :=
    lintegral_abox_pair_lt_top (N := N) (ℓ := ℓ) hℓ hG hGfin i j hij
  have hmeas : AEStronglyMeasurable (fun x : X N => |w (x i - x j)|)
      (volume.restrict (abox N ℓ)) := by
    exact (by fun_prop : Measurable fun x : X N => |w (x i - x j)|).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  change (∫⁻ x, ‖|w (x i - x j)|‖ₑ ∂(volume.restrict (abox N ℓ))) < (∞ : ℝ≥0∞)
  have hnorm : (fun x : X N => ‖|w (x i - x j)|‖ₑ) = fun x : X N => G (x i - x j) := by
    funext x
    dsimp [G]
    rw [Real.enorm_eq_ofReal (abs_nonneg (w (x i - x j)))]
  rw [hnorm]
  exact hlt



lemma abox_ae_abs_pair_of_ae {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v w : ℝ³ → ℝ}
    (hvw : v =ᵐ[volume] w) (i j : Fin N) (hij : i ≠ j) :
    (fun x : X N => |v (x i - x j)|) =ᵐ[volume.restrict (abox N ℓ)]
      (fun x : X N => |w (x i - x j)|) := by
  have hN : volume {y : ℝ³ | v y ≠ w y} = 0 := by
    rw [← ae_iff]
    exact hvw
  rcases exists_measurable_superset_of_null (μ := (volume : Measure ℝ³)) hN with
    ⟨t, hNt, htm, ht0⟩
  have hpre : (volume : Measure (X N)).restrict (abox N ℓ) {x : X N | x i - x j ∈ t} = 0 :=
    abox_null_preimage_pair hℓ htm ht0 i j hij
  have hfail : (volume : Measure (X N)).restrict (abox N ℓ)
      {x : X N | |v (x i - x j)| ≠ |w (x i - x j)|} = 0 := by
    have hsub : {x : X N | |v (x i - x j)| ≠ |w (x i - x j)|} ⊆
          {x : X N | x i - x j ∈ t} := by
        intro x hx
        apply hNt
        intro hEq
        exact hx (by rw [hEq])
    apply le_antisymm
    · calc
        (volume : Measure (X N)).restrict (abox N ℓ) {x : X N | |v (x i - x j)| ≠ |w (x i - x j)|}
            ≤ (volume : Measure (X N)).restrict (abox N ℓ) {x : X N | x i - x j ∈ t} :=
              measure_mono hsub
        _ = 0 := hpre
    · positivity
  have hmem : {x : X N | |v (x i - x j)| = |w (x i - x j)|} ∈
      ae (volume.restrict (abox N ℓ)) := by
    rw [mem_ae_iff]
    rw [show ({x : X N | |v (x i - x j)| = |w (x i - x j)|}ᶜ) =
        {x : X N | |v (x i - x j)| ≠ |w (x i - x j)|} by ext x; simp]
    exact hfail
  rw [show (fun x : X N => |v (x i - x j)|) =ᵐ[volume.restrict (abox N ℓ)]
        (fun x : X N => |w (x i - x j)|) ↔
      {x : X N | |v (x i - x j)| = |w (x i - x j)|} ∈ ae (volume.restrict (abox N ℓ)) by rfl]
  exact hmem

lemma integrableOn_abs_sub_abox {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hh : Integrable h) (i j : Fin N) (hij : i ≠ j) :
    IntegrableOn (fun x : X N => |h (x i - x j)|) (abox N ℓ) volume := by
  let w : ℝ³ → ℝ := AEMeasurable.mk h hh.aemeasurable
  have hwm : Measurable w := AEMeasurable.measurable_mk hh.aemeasurable
  have hvw : h =ᵐ[volume] w := AEMeasurable.ae_eq_mk hh.aemeasurable
  have hwInt : Integrable w := hh.congr hvw
  have hwfin : (∫⁻ y : ℝ³, ‖w y‖ₑ) < (∞ : ℝ≥0∞) := hwInt.hasFiniteIntegral
  have hmain : IntegrableOn (fun x : X N => |w (x i - x j)|) (abox N ℓ) volume :=
    integrableOn_abs_pair_abox_of_measurable hℓ hwm hwfin i j hij
  have hae : (fun x : X N => |h (x i - x j)|) =ᵐ[volume.restrict (abox N ℓ)]
      (fun x : X N => |w (x i - x j)|) := abox_ae_abs_pair_of_ae hℓ hvw i j hij
  exact hmain.integrable.congr hae.symm



lemma lintegral_abox_pair_le (N : ℕ) {ℓ : ℝ} {G : ℝ³ → ℝ≥0∞} (hG : Measurable G)
    (i j : Fin N) (hij : i ≠ j) :
    (∫⁻ x in abox N ℓ, G (x i - x j)) ≤
      (∫⁻ y : ℝ³, G y) * volume (abox (N - 1) ℓ) := by
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      have hvol : volume (abox (Nat.succ n - 1) ℓ) = volume (abox n ℓ) := by simp
      rw [hvol]
      let j' : Fin n := Classical.choose (Fin.exists_succAbove_eq (x := j) (y := i) hij.symm)
      have hjj' : i.succAbove j' = j := by
        simpa [j'] using (Classical.choose_spec (Fin.exists_succAbove_eq (x := j) (y := i) hij.symm))
      have heq := lintegral_abox_pair_eq_iterated (ℓ := ℓ) (G := G) hG i j j' hjj'
      rw [heq]
      have hle : (∫⁻ a : X n, ∫⁻ b : ℝ³, G (b - a j')
            ∂((volume : Measure ℝ³).restrict (acube ℓ))
            ∂((volume : Measure (X n)).restrict (abox n ℓ)))
          ≤ (∫⁻ a : X n, (∫⁻ y : ℝ³, G y)
              ∂((volume : Measure (X n)).restrict (abox n ℓ))) := by
        apply lintegral_mono_ae
        filter_upwards with a
        exact lintegral_acube_sub_le ℓ hG (a j')
      refine le_trans hle ?_
      rw [lintegral_const]
      rw [Measure.restrict_apply_univ]

lemma real_abox_pair_le_meas {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {W : ℝ³ → ℝ} (hWm : Measurable W)
    (hW0 : 0 ≤ W) (hWfin : (∫⁻ y : ℝ³, ENNReal.ofReal (W y)) < (⊤ : ℝ≥0∞))
    (i j : Fin N) (hij : i ≠ j) :
    (∫ x in abox N ℓ, W (x i - x j)) ≤ (∫ y : ℝ³, W y) * (volume (abox (N - 1) ℓ)).toReal := by
  let G : ℝ³ → ℝ≥0∞ := fun y => ENNReal.ofReal (W y)
  have hGm : Measurable G := by
    dsimp [G]
    fun_prop
  have hvol : (volume (abox (N - 1) ℓ)) < (⊤ : ℝ≥0∞) := by
    exact abox_lt_top (N - 1) ℓ hℓ.le
  have hlin := lintegral_abox_pair_le (N := N) (ℓ := ℓ) hGm i j hij
  have hconv : (∫ x in abox N ℓ, W (x i - x j)) =
      (∫⁻ x in abox N ℓ, G (x i - x j)).toReal := by
    have hmeas : Measurable (fun x : X N => W (x i - x j)) := by
      exact hWm.comp (by fun_prop : Measurable (fun x : X N => (x i - x j) : X N → ℝ³))
    exact integral_eq_lintegral_of_nonneg_ae
      (μ := volume.restrict (abox N ℓ)) (f := fun x : X N => W (x i - x j)) (by
        filter_upwards with x
        exact hW0 (x i - x j)) hmeas.aestronglyMeasurable
  have hconv2 : (∫ y : ℝ³, W y) = (∫⁻ y : ℝ³, G y).toReal := by
    exact integral_eq_lintegral_of_nonneg_ae (μ := (volume : Measure ℝ³))
      (f := W) (by filter_upwards with y; exact hW0 y) hWm.aestronglyMeasurable
  calc
    (∫ x in abox N ℓ, W (x i - x j)) = (∫⁻ x in abox N ℓ, G (x i - x j)).toReal := hconv
    _ ≤ ((∫⁻ y : ℝ³, G y) * volume (abox (N - 1) ℓ)).toReal := by
      exact ENNReal.toReal_mono (ENNReal.mul_lt_top hWfin hvol).ne hlin
    _ = (∫⁻ y : ℝ³, G y).toReal * (volume (abox (N - 1) ℓ)).toReal := by
      rw [ENNReal.toReal_mul]
    _ = (∫ y : ℝ³, W y) * (volume (abox (N - 1) ℓ)).toReal := by rw [hconv2]

lemma setIntegral_abs_sub_abox_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hh : Integrable h) (i j : Fin N) (hij : i ≠ j) :
    (∫ x in abox N ℓ, |h (x i - x j)|) ≤ (ℓ ^ 3) ^ (N - 1) * (∫ y : ℝ³, |h y|) := by
  have hvae : AEMeasurable h := hh.aemeasurable
  let w : ℝ³ → ℝ := AEMeasurable.mk h hvae
  have hwm : Measurable w := AEMeasurable.measurable_mk hvae
  have hvw : h =ᵐ[volume] w := AEMeasurable.ae_eq_mk hvae
  have hwInt : Integrable w := hh.congr hvw
  let W : ℝ³ → ℝ := fun y => |w y|
  have hWm : Measurable W := by
    dsimp [W]
    fun_prop
  have hW0 : 0 ≤ W := by
    intro y
    exact abs_nonneg (w y)
  have hWfin : (∫⁻ y : ℝ³, ENNReal.ofReal (W y)) < (⊤ : ℝ≥0∞) := by
    have hfi := hwInt.abs.hasFiniteIntegral
    have hEq : (fun y : ℝ³ => ENNReal.ofReal (W y)) = fun y : ℝ³ => ‖W y‖ₑ := by
      funext y
      dsimp [W]
      rw [Real.enorm_eq_ofReal (abs_nonneg (w y))]
    rwa [hEq]
  have hconv_vw : (∫ x in abox N ℓ, |h (x i - x j)|) = (∫ x in abox N ℓ, W (x i - x j)) := by
    exact integral_congr_ae (abox_ae_abs_pair_of_ae hℓ hvw i j hij)
  have h_abs : (fun y : ℝ³ => W y) =ᵐ[volume] (fun y : ℝ³ => |h y|) := by
    filter_upwards [hvw] with y hy
    dsimp [W]
    exact congrArg abs hy.symm
  have hconv_ws : (∫ y : ℝ³, W y) = (∫ y : ℝ³, |h y|) := by
    calc
      (∫ y : ℝ³, W y) = ∫ y : ℝ³, |w y| := by
        apply integral_congr_ae
        filter_upwards with y
        dsimp [W]
      _ = ∫ y : ℝ³, |h y| := integral_congr_ae h_abs
  have hvolR : (volume (abox (N - 1) ℓ)).toReal = (ℓ ^ 3) ^ (N - 1) := by
    rw [abox_volume (N - 1) ℓ hℓ.le]
    rw [ENNReal.toReal_ofReal]
    exact pow_nonneg (pow_nonneg hℓ.le 3) (N - 1)
  calc
    (∫ x in abox N ℓ, |h (x i - x j)|) = (∫ x in abox N ℓ, W (x i - x j)) := hconv_vw
    _ ≤ (∫ y : ℝ³, W y) * (volume (abox (N - 1) ℓ)).toReal :=
      real_abox_pair_le_meas (N := N) (ℓ := ℓ) hℓ hWm hW0 hWfin i j hij
    _ = (∫ y : ℝ³, W y) * (ℓ ^ 3) ^ (N - 1) := by rw [hvolR]
    _ = (ℓ ^ 3) ^ (N - 1) * (∫ y : ℝ³, W y) := by rw [mul_comm]
    _ = (ℓ ^ 3) ^ (N - 1) * (∫ y : ℝ³, |h y|) := by rw [hconv_ws]





lemma integrableOn_bounded_mul_abs_sub_abox {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : X N → ℝ} {h : ℝ³ → ℝ} (hh : Integrable h) (i j : Fin N) (hij : i ≠ j)
    (hgm : AEStronglyMeasurable g (volume.restrict (abox N ℓ)))
    {B : ℝ} (hB : 0 ≤ B) (hgb : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |g x| ≤ B) :
    IntegrableOn (fun x : X N => g x * |h (x i - x j)|) (abox N ℓ) volume := by
  have hhi : IntegrableOn (fun x : X N => |h (x i - x j)|) (abox N ℓ) volume :=
    integrableOn_abs_sub_abox hℓ hh i j hij
  have hf_aesm : AEStronglyMeasurable (fun x : X N => g x * |h (x i - x j)|)
      (volume.restrict (abox N ℓ)) := hgm.mul hhi.aestronglyMeasurable
  have hdom : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      ‖g x * |h (x i - x j)|‖ ≤ B * |h (x i - x j)| := by
    filter_upwards [hgb] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (abs_nonneg (h (x i - x j)))]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg (h (x i - x j)))
  have hBint : IntegrableOn (fun x : X N => B * |h (x i - x j)|) (abox N ℓ) volume := by
    exact hhi.integrable.const_mul B
  exact Integrable.mono' hBint.integrable hf_aesm hdom



lemma setIntegral_bounded_mul_abs_sub_abox_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : X N → ℝ} {h : ℝ³ → ℝ} (hh : Integrable h) (i j : Fin N) (hij : i ≠ j)
    (hgm : AEStronglyMeasurable g (volume.restrict (abox N ℓ)))
    {B : ℝ} (hB : 0 ≤ B) (hgb : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |g x| ≤ B) :
    |∫ x in abox N ℓ, g x * h (x i - x j)| ≤
      B * (ℓ ^ 3) ^ (N - 1) * (∫ y : ℝ³, |h y|) := by
  let μ : Measure (X N) := volume.restrict (abox N ℓ)
  have hhi : IntegrableOn (fun x : X N => |h (x i - x j)|) (abox N ℓ) volume :=
    integrableOn_abs_sub_abox hℓ hh i j hij
  have hB_abs : Integrable (fun x : X N => B * |h (x i - x j)|) μ := by
    simpa [μ] using (hhi.integrable.const_mul B)
  have hgabs : AEStronglyMeasurable (fun x : X N => |g x|) μ := by
    simpa [μ] using hgm.norm
  have haesm_prod : AEStronglyMeasurable ((fun x : X N => |g x|) * (fun x : X N => |h (x i - x j)|)) μ :=
    hgabs.mul hhi.aestronglyMeasurable
  have hprod_abs_aesm : AEStronglyMeasurable (fun x : X N => |g x * h (x i - x j)|) μ := by
    refine AEStronglyMeasurable.congr haesm_prod ?_
    refine ae_of_all _ ?_
    intro x
    change |g x| * |h (x i - x j)| = |g x * h (x i - x j)|
    rw [abs_mul]
  have hdomB : ∀ᵐ x ∂μ, ‖|g x * h (x i - x j)|‖ ≤ B * |h (x i - x j)| := by
    filter_upwards [hgb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg (g x * h (x i - x j))), abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg (h (x i - x j)))
  have hprod_abs : Integrable (fun x : X N => |g x * h (x i - x j)|) μ :=
    Integrable.mono' hB_abs hprod_abs_aesm hdomB
  have hleB : (fun x : X N => |g x * h (x i - x j)|) ≤ᵐ[μ] (fun x : X N => B * |h (x i - x j)|) := by
    filter_upwards [hgb] with x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg (h (x i - x j)))
  calc
    |∫ x in abox N ℓ, g x * h (x i - x j)| ≤ ∫ x in abox N ℓ, |g x * h (x i - x j)| := by
      simpa [μ] using (abs_integral_le_integral_abs (μ := μ) (f := fun x : X N => g x * h (x i - x j)))
    _ ≤ ∫ x in abox N ℓ, B * |h (x i - x j)| := by
      simpa [μ] using (integral_mono_ae hprod_abs hB_abs hleB)
    _ = B * ∫ x in abox N ℓ, |h (x i - x j)| := by
      simpa [μ] using (integral_const_mul B (fun x : X N => |h (x i - x j)|))
    _ ≤ B * ((ℓ ^ 3) ^ (N - 1) * (∫ y : ℝ³, |h y|)) := by
      exact mul_le_mul_of_nonneg_left (setIntegral_abs_sub_abox_le hℓ hh i j hij) hB
    _ = B * (ℓ ^ 3) ^ (N - 1) * (∫ y : ℝ³, |h y|) := by ring





lemma wPair_abs_bound_le {ℓ R : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (hRℓ : R ≤ ℓ * chiR0) (x y : ℝ³) :
    |wPair ℓ h x y| ≤ chiSup * (2 * (Real.sqrt chiNormSq)⁻¹) * |h (x - y)| := by
  have hb := wPair_abs_bound (ℓ := ℓ) (R := R) hℓ hsupp hRℓ x y
  have hcs : chiScale ℓ x ≤ chiSup := by
    have hnn : 0 ≤ chiScale ℓ x := chiScale_nonneg ℓ x
    calc
      chiScale ℓ x = |chiScale ℓ x| := (abs_of_nonneg hnn).symm
      _ ≤ chiSup := abs_chiScale_le_chiSup ℓ x
  have hS0 : 0 ≤ (Real.sqrt chiNormSq)⁻¹ := by
    exact inv_nonneg.mpr (le_of_lt (Real.sqrt_pos.mpr chiNormSq_pos))
  have h2S0 : 0 ≤ 2 * (Real.sqrt chiNormSq)⁻¹ := mul_nonneg (by norm_num) hS0
  calc
    |wPair ℓ h x y| ≤ chiScale ℓ x * (2 * (Real.sqrt chiNormSq)⁻¹) * |h (x - y)| := hb
    _ ≤ chiSup * (2 * (Real.sqrt chiNormSq)⁻¹) * |h (x - y)| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcs h2S0) (abs_nonneg (h (x - y)))



lemma abox_ae_wPair_pair_of_ae {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {h w : ℝ³ → ℝ}
    (hvw : h =ᵐ[volume] w) (i j : Fin N) (hij : i ≠ j) :
    (fun x : X N => wPair ℓ h (x i) (x j)) =ᵐ[volume.restrict (abox N ℓ)]
      (fun x : X N => wPair ℓ w (x i) (x j)) := by
  have hN : volume {y : ℝ³ | h y ≠ w y} = 0 := by
    rw [← ae_iff]
    exact hvw
  rcases exists_measurable_superset_of_null (μ := (volume : Measure ℝ³)) hN with
    ⟨t, hNt, htm, ht0⟩
  have hpre : (volume : Measure (X N)).restrict (abox N ℓ) {x : X N | x i - x j ∈ t} = 0 :=
    abox_null_preimage_pair hℓ htm ht0 i j hij
  have hfail : (volume : Measure (X N)).restrict (abox N ℓ)
      {x : X N | wPair ℓ h (x i) (x j) ≠ wPair ℓ w (x i) (x j)} = 0 := by
    have hsub : {x : X N | wPair ℓ h (x i) (x j) ≠ wPair ℓ w (x i) (x j)} ⊆
          {x : X N | x i - x j ∈ t} := by
        intro x hx
        apply hNt
        intro hEq
        exact hx (by
          dsimp [wPair, wScaled]
          rw [hEq])
    apply le_antisymm
    · calc
        (volume : Measure (X N)).restrict (abox N ℓ) {x : X N | wPair ℓ h (x i) (x j) ≠ wPair ℓ w (x i) (x j)}
            ≤ (volume : Measure (X N)).restrict (abox N ℓ) {x : X N | x i - x j ∈ t} :=
              measure_mono hsub
        _ = 0 := hpre
    · positivity
  have hmem : {x : X N | wPair ℓ h (x i) (x j) = wPair ℓ w (x i) (x j)} ∈
      ae (volume.restrict (abox N ℓ)) := by
    rw [mem_ae_iff]
    rw [show ({x : X N | wPair ℓ h (x i) (x j) = wPair ℓ w (x i) (x j)}ᶜ) =
        {x : X N | wPair ℓ h (x i) (x j) ≠ wPair ℓ w (x i) (x j)} by ext x; simp]
    exact hfail
  rw [show (fun x : X N => wPair ℓ h (x i) (x j)) =ᵐ[volume.restrict (abox N ℓ)]
        (fun x : X N => wPair ℓ w (x i) (x j)) ↔
      {x : X N | wPair ℓ h (x i) (x j) = wPair ℓ w (x i) (x j)} ∈ ae (volume.restrict (abox N ℓ)) by rfl]
  exact hmem

lemma aesm_wPair_pair_of_measurable {N : ℕ} {ℓ : ℝ} {w : ℝ³ → ℝ} (hwm : Measurable w)
    (i j : Fin N) :
    AEStronglyMeasurable (fun x : X N => wPair ℓ w (x i) (x j))
      (volume.restrict (abox N ℓ)) := by
  have hU : Measurable (wPairU ℓ w) := wPairU_measurable hwm
  have hcomp : Measurable (fun x : X N => wPairU ℓ w (x i, x j)) := by
    exact hU.comp (by fun_prop : Measurable (fun x : X N => (x i, x j) : X N → ℝ³ × ℝ³))
  have heq : (fun x : X N => wPair ℓ w (x i) (x j)) = fun x : X N => wPairU ℓ w (x i, x j) := by
    funext x
    rfl
  simpa [heq] using hcomp.aestronglyMeasurable

lemma integrableOn_wPair_abs_sub_abox {N : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hh : Integrable h) (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (hRℓ : R ≤ ℓ * chiR0)
    (i j : Fin N) (hij : i ≠ j) :
    IntegrableOn (fun x : X N => |wPair ℓ h (x i) (x j)|) (abox N ℓ) volume := by
  let w : ℝ³ → ℝ := AEMeasurable.mk h hh.aemeasurable
  have hwm : Measurable w := AEMeasurable.measurable_mk hh.aemeasurable
  have hvw : h =ᵐ[volume] w := AEMeasurable.ae_eq_mk hh.aemeasurable
  let C : ℝ := chiSup * (2 * (Real.sqrt chiNormSq)⁻¹)
  have hhi : IntegrableOn (fun x : X N => |h (x i - x j)|) (abox N ℓ) volume :=
    integrableOn_abs_sub_abox hℓ hh i j hij
  have hg : Integrable (fun x : X N => C * |h (x i - x j)|)
      (volume.restrict (abox N ℓ)) := by
    simpa [C] using (hhi.integrable.const_mul (chiSup * (2 * (Real.sqrt chiNormSq)⁻¹)))
  have haesm : AEStronglyMeasurable (fun x : X N => wPair ℓ h (x i) (x j))
      (volume.restrict (abox N ℓ)) := by
    have hw_meas_ae : AEStronglyMeasurable (fun x : X N => wPair ℓ w (x i) (x j))
        (volume.restrict (abox N ℓ)) := aesm_wPair_pair_of_measurable hwm i j
    refine AEStronglyMeasurable.congr hw_meas_ae ?_
    simpa [w] using (abox_ae_wPair_pair_of_ae (hℓ := hℓ) hvw i j hij).symm
  have haesm_abs : AEStronglyMeasurable (fun x : X N => |wPair ℓ h (x i) (x j)|)
      (volume.restrict (abox N ℓ)) := by
    simpa [Real.norm_eq_abs] using haesm.norm
  have hdom : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      ‖|wPair ℓ h (x i) (x j)|‖ ≤ C * |h (x i - x j)| := by
    refine ae_of_all _ ?_
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg (wPair ℓ h (x i) (x j)))]
    simpa [C] using (wPair_abs_bound_le hℓ hsupp hRℓ (x i) (x j))
  exact Integrable.mono' hg haesm_abs hdom

lemma aesm_wPair_pair {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ} (hh : Integrable h)
    (i j : Fin N) (hij : i ≠ j) :
    AEStronglyMeasurable (fun x : X N => wPair ℓ h (x i) (x j))
      (volume.restrict (abox N ℓ)) := by
  let w : ℝ³ → ℝ := AEMeasurable.mk h hh.aemeasurable
  have hwm : Measurable w := AEMeasurable.measurable_mk hh.aemeasurable
  have hvw : h =ᵐ[volume] w := AEMeasurable.ae_eq_mk hh.aemeasurable
  have hw_meas_ae : AEStronglyMeasurable (fun x : X N => wPair ℓ w (x i) (x j))
      (volume.restrict (abox N ℓ)) := aesm_wPair_pair_of_measurable hwm i j
  refine AEStronglyMeasurable.congr hw_meas_ae ?_
  simpa [w] using (abox_ae_wPair_pair_of_ae hℓ hvw i j hij).symm

lemma integrableOn_bounded_mul_wPair_sub_abox {N : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ)
    {g : X N → ℝ} {h : ℝ³ → ℝ} (hh : Integrable h)
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (hRℓ : R ≤ ℓ * chiR0)
    (i j : Fin N) (hij : i ≠ j)
    (hgm : AEStronglyMeasurable g (volume.restrict (abox N ℓ)))
    {B : ℝ} (hB : 0 ≤ B) (hgb : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |g x| ≤ B) :
    IntegrableOn (fun x : X N => g x * wPair ℓ h (x i) (x j)) (abox N ℓ) volume := by
  let C : ℝ := chiSup * (2 * (Real.sqrt chiNormSq)⁻¹)
  have hhi : IntegrableOn (fun x : X N => |h (x i - x j)|) (abox N ℓ) volume :=
    integrableOn_abs_sub_abox hℓ hh i j hij
  have hg : Integrable (fun x : X N => (B * C) * |h (x i - x j)|)
      (volume.restrict (abox N ℓ)) := by
    simpa [C] using (hhi.integrable.const_mul (B * (chiSup * (2 * (Real.sqrt chiNormSq)⁻¹))))
  have haesm_w : AEStronglyMeasurable (fun x : X N => wPair ℓ h (x i) (x j))
      (volume.restrict (abox N ℓ)) := aesm_wPair_pair hℓ hh i j hij
  have haesm : AEStronglyMeasurable (fun x : X N => g x * wPair ℓ h (x i) (x j))
      (volume.restrict (abox N ℓ)) := hgm.mul haesm_w
  have hdom : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      ‖g x * wPair ℓ h (x i) (x j)‖ ≤ (B * C) * |h (x i - x j)| := by
    filter_upwards [hgb] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |g x| * |wPair ℓ h (x i) (x j)| ≤ B * |wPair ℓ h (x i) (x j)| :=
        mul_le_mul_of_nonneg_right hx (abs_nonneg _)
      _ ≤ B * (C * |h (x i - x j)|) := by
        simpa [C] using (mul_le_mul_of_nonneg_left (wPair_abs_bound_le hℓ hsupp hRℓ (x i) (x j)) hB)
      _ = (B * C) * |h (x i - x j)| := by ring
  exact Integrable.mono' hg haesm hdom



lemma setIntegral_bounded_mul_wPair_sub_abox_le {N : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ)
    {g : X N → ℝ} {h : ℝ³ → ℝ} (hh : Integrable h)
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (hRℓ : R ≤ ℓ * chiR0)
    (i j : Fin N) (hij : i ≠ j)
    (hgm : AEStronglyMeasurable g (volume.restrict (abox N ℓ)))
    {B : ℝ} (hB : 0 ≤ B) (hgb : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |g x| ≤ B) :
    |∫ x in abox N ℓ, g x * wPair ℓ h (x i) (x j)| ≤
      B * (ℓ ^ 3) ^ (N - 1) * (chiSup * (2 * (Real.sqrt chiNormSq)⁻¹)) *
        (∫ y : ℝ³, |h y|) := by
  let C : ℝ := chiSup * (2 * (Real.sqrt chiNormSq)⁻¹)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (le_of_lt chiSup_pos)
      (mul_nonneg (by norm_num)
        (inv_nonneg.mpr (le_of_lt (Real.sqrt_pos.mpr chiNormSq_pos))))
  have hBC0 : 0 ≤ B * C := mul_nonneg hB hC0
  let μ : Measure (X N) := volume.restrict (abox N ℓ)
  have h_int_mul : IntegrableOn (fun x : X N => g x * wPair ℓ h (x i) (x j)) (abox N ℓ) volume :=
    integrableOn_bounded_mul_wPair_sub_abox hℓ hh hsupp hRℓ i j hij hgm hB hgb
  have hprod_abs : Integrable (fun x : X N => |g x * wPair ℓ h (x i) (x j)|) μ := by
    simpa [μ] using h_int_mul.integrable.abs
  have hB_abs : Integrable (fun x : X N => (B * C) * |h (x i - x j)|) μ := by
    have hhi : IntegrableOn (fun x : X N => |h (x i - x j)|) (abox N ℓ) volume :=
      integrableOn_abs_sub_abox hℓ hh i j hij
    simpa [μ, C] using (hhi.integrable.const_mul (B * (chiSup * (2 * (Real.sqrt chiNormSq)⁻¹))))
  have hleB : (fun x : X N => |g x * wPair ℓ h (x i) (x j)|) ≤ᵐ[μ]
      (fun x : X N => (B * C) * |h (x i - x j)|) := by
    filter_upwards [hgb] with x hx
    rw [abs_mul]
    calc
      |g x| * |wPair ℓ h (x i) (x j)| ≤ B * |wPair ℓ h (x i) (x j)| :=
        mul_le_mul_of_nonneg_right hx (abs_nonneg _)
      _ ≤ B * (C * |h (x i - x j)|) := by
        simpa [C] using (mul_le_mul_of_nonneg_left (wPair_abs_bound_le hℓ hsupp hRℓ (x i) (x j)) hB)
      _ = (B * C) * |h (x i - x j)| := by ring
  calc
    |∫ x in abox N ℓ, g x * wPair ℓ h (x i) (x j)| ≤ ∫ x in abox N ℓ, |g x * wPair ℓ h (x i) (x j)| := by
      simpa [μ] using (abs_integral_le_integral_abs (μ := μ)
        (f := fun x : X N => g x * wPair ℓ h (x i) (x j)))
    _ ≤ ∫ x in abox N ℓ, (B * C) * |h (x i - x j)| := by
      simpa [μ] using (integral_mono_ae hprod_abs hB_abs hleB)
    _ = (B * C) * ∫ x in abox N ℓ, |h (x i - x j)| := by
      simpa [μ] using (integral_const_mul (B * C) (fun x : X N => |h (x i - x j)|))
    _ ≤ (B * C) * ((ℓ ^ 3) ^ (N - 1) * (∫ y : ℝ³, |h y|)) := by
      exact mul_le_mul_of_nonneg_left (setIntegral_abs_sub_abox_le hℓ hh i j hij) hBC0
    _ = B * (ℓ ^ 3) ^ (N - 1) * (chiSup * (2 * (Real.sqrt chiNormSq)⁻¹)) * (∫ y : ℝ³, |h y|) := by
      dsimp [C]
      ring





lemma pairSet_card_le (N : ℕ) : (pairSet N).card ≤ N ^ 2 := by
  have hsub : pairSet N ⊆ (Finset.univ : Finset (Fin N × Fin N)) := by
    intro p hp
    simp
  calc
    (pairSet N).card ≤ (Finset.univ : Finset (Fin N × Fin N)).card := Finset.card_le_card hsub
    _ = N ^ 2 := by
      simp [pow_two]



lemma setIntegral_sumPair_abs_sub_abox_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hh : Integrable h) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ, |h (x p.1 - x p.2)|) ≤
      (N : ℝ) ^ 2 * (ℓ ^ 3) ^ (N - 1) * (∫ y : ℝ³, |h y|) := by
  let V : ℝ := (ℓ ^ 3) ^ (N - 1) * (∫ y : ℝ³, |h y|)
  have hV : 0 ≤ V := by
    dsimp [V]
    exact mul_nonneg (pow_nonneg (pow_nonneg hℓ.le 3) (N - 1))
      (integral_nonneg (fun y => abs_nonneg (h y)))
  have hterm : ∀ p ∈ pairSet N, (∫ x in abox N ℓ, |h (x p.1 - x p.2)|) ≤ V := by
    intro p hp
    have hne : p.1 ≠ p.2 := by
      simpa [pairSet] using hp
    have hb := setIntegral_abs_sub_abox_le hℓ hh p.1 p.2 hne
    simpa [V] using hb
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ, |h (x p.1 - x p.2)|) ≤ ∑ p ∈ pairSet N, V :=
      Finset.sum_le_sum hterm
    _ = ((pairSet N).card : ℝ) * V := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ 2 * V := by
      have hcard : ((pairSet N).card : ℝ) ≤ (N : ℝ) ^ 2 := by
        exact_mod_cast pairSet_card_le N
      exact mul_le_mul_of_nonneg_right hcard hV
    _ = (N : ℝ) ^ 2 * (ℓ ^ 3) ^ (N - 1) * (∫ y : ℝ³, |h y|) := by
      dsimp [V]
      ring



lemma setIntegral_sumPair_wPair_abs_sub_abox_le {N : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ)
    {h : ℝ³ → ℝ} (hh : Integrable h) (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0)
    (hRℓ : R ≤ ℓ * chiR0) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ, |wPair ℓ h (x p.1) (x p.2)|) ≤
      (N : ℝ) ^ 2 * (ℓ ^ 3) ^ (N - 1) * (chiSup * (2 * (Real.sqrt chiNormSq)⁻¹)) *
        (∫ y : ℝ³, |h y|) := by
  let C : ℝ := chiSup * (2 * (Real.sqrt chiNormSq)⁻¹)
  let V : ℝ := (ℓ ^ 3) ^ (N - 1) * (∫ y : ℝ³, |h y|)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (le_of_lt chiSup_pos)
      (mul_nonneg (by norm_num)
        (inv_nonneg.mpr (le_of_lt (Real.sqrt_pos.mpr chiNormSq_pos))))
  have hV : 0 ≤ V := by
    dsimp [V]
    exact mul_nonneg (pow_nonneg (pow_nonneg hℓ.le 3) (N - 1))
      (integral_nonneg (fun y => abs_nonneg (h y)))
  have hCV0 : 0 ≤ C * V := mul_nonneg hC0 hV
  have hterm : ∀ p ∈ pairSet N, (∫ x in abox N ℓ, |wPair ℓ h (x p.1) (x p.2)|) ≤ C * V := by
    intro p hp
    have hne : p.1 ≠ p.2 := by
      simpa [pairSet] using hp
    have hdompt : ∀ x : X N, |wPair ℓ h (x p.1) (x p.2)| ≤ C * |h (x p.1 - x p.2)| := by
      intro x
      simpa [C] using (wPair_abs_bound_le hℓ hsupp hRℓ (x p.1) (x p.2))
    have hle1 : (∫ x in abox N ℓ, |wPair ℓ h (x p.1) (x p.2)|)
        ≤ ∫ x in abox N ℓ, C * |h (x p.1 - x p.2)| := by
      have hg : Integrable (fun x : X N => C * |h (x p.1 - x p.2)|)
          (volume.restrict (abox N ℓ)) := by
        have hhi : IntegrableOn (fun x : X N => |h (x p.1 - x p.2)|) (abox N ℓ) volume :=
          integrableOn_abs_sub_abox hℓ hh p.1 p.2 hne
        simpa [C] using (hhi.integrable.const_mul (chiSup * (2 * (Real.sqrt chiNormSq)⁻¹)))
      refine integral_mono_of_nonneg
        (μ := volume.restrict (abox N ℓ))
        (f := fun x : X N => |wPair ℓ h (x p.1) (x p.2)|)
        (g := fun x : X N => C * |h (x p.1 - x p.2)|) ?_ hg ?_
      · refine ae_of_all _ ?_
        intro x
        exact abs_nonneg (wPair ℓ h (x p.1) (x p.2))
      · refine ae_of_all _ ?_
        intro x
        exact hdompt x
    have hb2 := setIntegral_abs_sub_abox_le hℓ hh p.1 p.2 hne
    have hle3 : C * (∫ x in abox N ℓ, |h (x p.1 - x p.2)|) ≤ C * V := by
      exact mul_le_mul_of_nonneg_left hb2 hC0
    calc
      (∫ x in abox N ℓ, |wPair ℓ h (x p.1) (x p.2)|)
          ≤ ∫ x in abox N ℓ, C * |h (x p.1 - x p.2)| := hle1
      _ = C * (∫ x in abox N ℓ, |h (x p.1 - x p.2)|) := by
        simpa [C] using (integral_const_mul (chiSup * (2 * (Real.sqrt chiNormSq)⁻¹))
          (fun x : X N => |h (x p.1 - x p.2)|))
      _ ≤ C * V := hle3
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ, |wPair ℓ h (x p.1) (x p.2)|) ≤ ∑ p ∈ pairSet N, C * V :=
      Finset.sum_le_sum hterm
    _ = ((pairSet N).card : ℝ) * (C * V) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ 2 * (C * V) := by
      have hcard : ((pairSet N).card : ℝ) ≤ (N : ℝ) ^ 2 := by
        exact_mod_cast pairSet_card_le N
      exact mul_le_mul_of_nonneg_right hcard hCV0
    _ = (N : ℝ) ^ 2 * (ℓ ^ 3) ^ (N - 1) * (chiSup * (2 * (Real.sqrt chiNormSq)⁻¹)) *
        (∫ y : ℝ³, |h y|) := by
      dsimp [C, V]
      ring

end BoseGases

end Submission
