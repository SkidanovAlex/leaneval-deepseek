import Mathlib
import ChallengeDeps
import Submission.BoxMonotone
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Admissible potentials: integrability of the two-body terms.

The potential `v` of `theorem_1_2` is in `L¹(ℝ³)`.  For a smooth trial state
`Ψ : CInfty0Box N L` the interaction integrand
`x ↦ Ψ(x)² · Σ_{i<j} v(x_i − x_j)` is then integrable over the box, so the
Rayleigh-quotient numerator splits as kinetic + interaction energy
(`energy_decomposition`), i.e. the decomposition used everywhere below is
available for the potentials of the theorem without any further hypothesis.

Key intermediate step: for a pair `(i,j)` and `v ∈ L¹(ℝ³)`, the function
`x ↦ |v (x i − x j)|` is integrable over the box.  (Fix `x_i`; the map
`x_j ↦ x_i − x_j` is a translation followed by a reflection of `ℝ³`, so the
`x_j`-integral is bounded by `‖v‖₁`; the remaining coordinates contribute the
finite volume `L^(3(N−1))`.)
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

noncomputable section

/-- A potential in `L¹` is integrable. -/
lemma v_integrable {v : ℝ³ → ℝ} (hv : MemLp v 1) : Integrable v volume :=
  (memLp_one_iff_integrable.mp hv)

/-! ## The coordinate cube and the box as a product set -/

/-- Coordinate cube `[0,L]^3` in ℝ³. -/
def cube (L : ℝ) : Set ℝ³ := {y : ℝ³ | ∀ m : Fin 3, y m ∈ Set.Icc 0 L}

lemma cube_measurable (L : ℝ) : MeasurableSet (cube L) := by
  unfold cube
  rw [show {y : ℝ³ | ∀ m : Fin 3, y m ∈ Set.Icc 0 L} =
      (⋂ m : Fin 3, (fun y : ℝ³ => y m) ⁻¹' (Set.Icc 0 L)) by ext y; simp]
  exact MeasurableSet.iInter (fun m =>
    ((by fun_prop : Continuous fun y : ℝ³ => y m).measurable) measurableSet_Icc)

lemma box_eq_pi_cube (N : ℕ) (L : ℝ) :
    box N L = Set.univ.pi (fun _ : Fin N => cube L) := by
  ext x
  simp [box, cube]

lemma cube_isClosed (L : ℝ) : IsClosed (cube L) := by
  rw [show cube L = ⋂ m : Fin 3,
      (fun y : ℝ³ => y m) ⁻¹' (Set.Icc 0 L) by ext y; simp [cube]]
  exact isClosed_iInter (fun m =>
    (continuous_iff_isClosed.mp (by fun_prop : Continuous fun y : ℝ³ => y m)) _ isClosed_Icc)

lemma cube_isBounded (L : ℝ) (hL : 0 ≤ L) : Bornology.IsBounded (cube L) := by
  rw [Metric.isBounded_iff]
  refine ⟨2 * (Real.sqrt 3 * L), ?_⟩
  intro x hx y hy
  have hxle : ‖x‖ ≤ Real.sqrt 3 * L := by
    have hb : 0 ≤ Real.sqrt 3 * L := by positivity
    apply le_of_sq_le_sq
    · rw [EuclideanSpace.real_norm_sq_eq]
      calc
        (∑ k : Fin 3, (x k) ^ 2) ≤ ∑ k : Fin 3, L ^ 2 := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          have hyk : x k ∈ Set.Icc 0 L := hx k
          refine (sq_le_sq.mpr ?_)
          rw [abs_of_nonneg hyk.1, abs_of_nonneg hL]
          exact hyk.2
        _ = 3 * L ^ 2 := by norm_num
        _ = (Real.sqrt 3 * L) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]
    · exact hb
  have hyle : ‖y‖ ≤ Real.sqrt 3 * L := by
    have hb : 0 ≤ Real.sqrt 3 * L := by positivity
    apply le_of_sq_le_sq
    · rw [EuclideanSpace.real_norm_sq_eq]
      calc
        (∑ k : Fin 3, (y k) ^ 2) ≤ ∑ k : Fin 3, L ^ 2 := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          have hyk : y k ∈ Set.Icc 0 L := hy k
          refine (sq_le_sq.mpr ?_)
          rw [abs_of_nonneg hyk.1, abs_of_nonneg hL]
          exact hyk.2
        _ = 3 * L ^ 2 := by norm_num
        _ = (Real.sqrt 3 * L) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]
    · exact hb
  calc
    dist x y = ‖x - y‖ := by rw [dist_eq_norm]
    _ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
    _ ≤ Real.sqrt 3 * L + (Real.sqrt 3 * L) := by exact add_le_add hxle hyle
    _ = 2 * (Real.sqrt 3 * L) := by ring

lemma cube_compact {L : ℝ} (hL : 0 < L) : IsCompact (cube L) := by
  exact (Metric.isCompact_iff_isClosed_bounded).mpr ⟨cube_isClosed L, cube_isBounded L hL.le⟩

lemma measure_cube_lt_top {L : ℝ} (hL : 0 < L) : (volume : Measure ℝ³) (cube L) < ∞ := by
  exact IsCompact.measure_lt_top (cube_compact hL)

/-- The restricted box volume is the product of the cube-restricted volumes. -/
lemma restrict_box_eq_pi (N : ℕ) (L : ℝ) :
    (volume : Measure (X N)).restrict (box N L) =
      Measure.pi (fun _ : Fin N => (volume : Measure ℝ³).restrict (cube L)) := by
  rw [box_eq_pi_cube]
  rw [show (volume : Measure (X N)) = Measure.pi (fun _ : Fin N => (volume : Measure ℝ³)) by rfl]
  rw [Measure.restrict_pi_pi]

/-! ## Translation invariance of the cube-restricted integrals -/

lemma measurePreserving_sub_right (c : ℝ³) :
    MeasurePreserving (fun b : ℝ³ => b - c) (volume : Measure ℝ³) (volume : Measure ℝ³) := by
  simpa [sub_eq_add_neg] using (measurePreserving_add_right (μ := (volume : Measure ℝ³)) (-c))

lemma map_restrict_cube_sub_le (L : ℝ) (c : ℝ³) :
    ((volume : Measure ℝ³).restrict (cube L)).map (fun b : ℝ³ => b - c) ≤ (volume : Measure ℝ³) := by
  rw [Measure.le_iff]
  intro s hs
  have hmeas : MeasurableSet ((fun b : ℝ³ => b - c) ⁻¹' s) := by measurability
  rw [Measure.map_apply (f := (fun b : ℝ³ => b - c)) (by measurability) hs]
  rw [Measure.restrict_apply hmeas]
  calc
    volume ((fun b : ℝ³ => b - c) ⁻¹' s ∩ cube L) ≤ volume ((fun b : ℝ³ => b - c) ⁻¹' s) :=
      measure_mono (by intro x hx; exact hx.1)
    _ = volume s := by
      have hmp := measurePreserving_sub_right c
      rw [← Measure.map_apply (f := (fun b : ℝ³ => b - c)) (by measurability) hs]
      rw [hmp.map_eq]

/-- Shifting the argument of a nonnegative measurable function inside the cube-restricted
integral is bounded by the full integral. -/
lemma lintegral_sub_le (L : ℝ) {G : ℝ³ → ℝ≥0∞} (hG : Measurable G) (c : ℝ³) :
    (∫⁻ b, G (b - c) ∂((volume : Measure ℝ³).restrict (cube L))) ≤ (∫⁻ y : ℝ³, G y) := by
  have hlin : (∫⁻ y : ℝ³, G y ∂((volume : Measure ℝ³).restrict (cube L)).map (fun b : ℝ³ => b - c))
      = (∫⁻ b, G (b - c) ∂((volume : Measure ℝ³).restrict (cube L))) :=
    MeasureTheory.lintegral_map (μ := (volume : Measure ℝ³).restrict (cube L))
      (f := G) (g := (fun b : ℝ³ => b - c)) hG (by measurability)
  rw [← hlin]
  exact lintegral_mono' (map_restrict_cube_sub_le L c) le_rfl

/-! ## Fubini decomposition isolating one coordinate -/

/-- The measure-preserving split isolating the `i`-th of `n+1` coordinates. -/
lemma measurePreserving_coordSplitFin (n : ℕ) (L : ℝ) (i : Fin (n + 1)) :
    let μ' : Measure ℝ³ := (volume : Measure ℝ³).restrict (cube L)
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i)
      (Measure.pi (fun _ : Fin (n + 1) => μ')) (μ'.prod (Measure.pi (fun _ : Fin n => μ'))) := by
  intro μ'
  simpa using (measurePreserving_piFinSuccAbove (μ := fun _ : Fin (n + 1) => μ') i)

/-- Transport identity: the box-lintegral of `x ↦ G (x i - x j)` equals the iterated integral
with the `i`-coordinate in the fiber and the remaining coordinates (indexed by `Fin n`) outside. -/
lemma lintegral_pair_eq_iterated {n : ℕ} {L : ℝ} {G : ℝ³ → ℝ≥0∞} (hG : Measurable G)
    (i j : Fin (n + 1)) (j' : Fin n) (hjj' : i.succAbove j' = j) :
    (∫⁻ x, G (x i - x j) ∂((volume : Measure (X (n + 1))).restrict (box (n + 1) L))) =
      (∫⁻ a : X n, ∫⁻ b : ℝ³, G (b - a j')
        ∂((volume : Measure ℝ³).restrict (cube L))
        ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ³).restrict (cube L)))) := by
  let μ' : Measure ℝ³ := (volume : Measure ℝ³).restrict (cube L)
  have hbox : (volume : Measure (X (n + 1))).restrict (box (n + 1) L) =
      Measure.pi (fun _ : Fin (n + 1) => μ') := by
    dsimp [μ']
    exact restrict_box_eq_pi (n + 1) L
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
    (measurePreserving_coordSplitFin n L i) hF
  calc
    (∫⁻ x : X (n + 1), G (x i - x j) ∂(Measure.pi (fun _ : Fin (n + 1) => μ')))
        = ∫⁻ p : ℝ³ × X n, G (p.1 - p.2 j')
            ∂(μ'.prod (Measure.pi (fun _ : Fin n => μ'))) := by
          rw [← htr]
          apply lintegral_congr_ae
          filter_upwards with x
          exact (hpt x).symm
    _ = (∫⁻ a : X n, ∫⁻ b : ℝ³, G (b - a j')
          ∂((volume : Measure ℝ³).restrict (cube L))
          ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ³).restrict (cube L)))) := by
          simpa [μ'] using (lintegral_prod_symm (μ := μ') (ν := (Measure.pi (fun _ : Fin n => μ')))
            (f := fun q : ℝ³ × X n => G (q.1 - q.2 j')) hF.aemeasurable)

/-- Main machine lemma: for `G` measurable with finite total lintegral, the lintegral of
`x ↦ G (x i - x j)` over the box is finite, for `i ≠ j`. -/
lemma lintegral_pair_lt_top {N : ℕ} {L : ℝ} (hL : 0 < L) {G : ℝ³ → ℝ≥0∞} (hG : Measurable G)
    (hfin : (∫⁻ y : ℝ³, G y) < ∞) (i j : Fin N) (hij : i ≠ j) :
    (∫⁻ x, G (x i - x j) ∂((volume : Measure (X N)).restrict (box N L))) < ∞ := by
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      let μ' : Measure ℝ³ := (volume : Measure ℝ³).restrict (cube L)
      have hμ'fin : μ' Set.univ < ∞ := by
        dsimp [μ']
        rw [Measure.restrict_apply_univ]
        exact measure_cube_lt_top hL
      let j' : Fin n := Classical.choose (Fin.exists_succAbove_eq (x := j) (y := i) hij.symm)
      have hjj' : i.succAbove j' = j := by
        simpa [j'] using (Classical.choose_spec (Fin.exists_succAbove_eq (x := j) (y := i) hij.symm))
      have heq := lintegral_pair_eq_iterated (L := L) (G := G) hG i j j' hjj'
      rw [heq]
      have hle : (∫⁻ a : X n, ∫⁻ b : ℝ³, G (b - a j')
            ∂((volume : Measure ℝ³).restrict (cube L))
            ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ³).restrict (cube L))))
          ≤ (∫⁻ a : X n, (∫⁻ y : ℝ³, G y)
              ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ³).restrict (cube L)))) := by
        apply lintegral_mono_ae
        filter_upwards with a
        exact lintegral_sub_le L hG (a j')
      refine lt_of_le_of_lt hle ?_
      rw [lintegral_const]
      have hκ : (Measure.pi (fun _ : Fin n => (volume : Measure ℝ³).restrict (cube L))) Set.univ < ∞ := by
        rw [← Set.pi_univ (s := (Set.univ : Set (Fin n)))]
        rw [Measure.pi_pi (μ := fun _ : Fin n => (volume : Measure ℝ³).restrict (cube L))
          (s := fun _ : Fin n => (Set.univ : Set ℝ³))]
        exact ENNReal.prod_lt_top (fun k _ => by
          rw [Measure.restrict_apply_univ]
          exact measure_cube_lt_top hL)
      exact ENNReal.mul_lt_top hfin hκ

/-- For `i ≠ j`, the preimage of a Lebesgue-null set under `x ↦ x i - x j` is null in the box. -/
lemma null_preimage_pair {N : ℕ} {L : ℝ} (hL : 0 < L) {s : Set ℝ³} (hs : MeasurableSet s)
    (hs0 : volume s = 0) (i j : Fin N) (hij : i ≠ j) :
    (volume : Measure (X N)).restrict (box N L) {x | x i - x j ∈ s} = 0 := by
  have hG : Measurable (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) := by
    exact Measurable.indicator (by measurability : Measurable fun _ : ℝ³ => (1 : ℝ≥0∞)) hs
  have hzero : (∫⁻ y : ℝ³, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) y) = 0 := by
    rw [lintegral_indicator hs]
    simp [hs0]
  let t : Set (X N) := {x : X N | x i - x j ∈ s}
  have htmeas : MeasurableSet t := by
    dsimp [t]
    measurability
  have hval : (volume : Measure (X N)).restrict (box N L) t
      = ∫⁻ x, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) (x i - x j)
          ∂((volume : Measure (X N)).restrict (box N L)) := by
    calc
      (volume : Measure (X N)).restrict (box N L) t
          = ∫⁻ x in t, (1 : ℝ≥0∞) ∂((volume : Measure (X N)).restrict (box N L)) := by
              rw [lintegral_const]
              rw [Measure.restrict_apply_univ]
              simp
      _ = ∫⁻ x, (t.indicator (fun _ : X N => (1 : ℝ≥0∞))) x
            ∂((volume : Measure (X N)).restrict (box N L)) := by
              rw [lintegral_indicator htmeas]
      _ = ∫⁻ x, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) (x i - x j)
            ∂((volume : Measure (X N)).restrict (box N L)) := by
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
      have heq := lintegral_pair_eq_iterated (L := L)
        (G := s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) hG i j j' hjj'
      rw [heq]
      have hin : ∀ a : X n,
          (∫⁻ b : ℝ³, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) (b - a j')
            ∂((volume : Measure ℝ³).restrict (cube L))) ≤
            ∫⁻ y : ℝ³, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) y := by
        intro a
        exact lintegral_sub_le L hG (a j')
      have hle : (∫⁻ a : X n, ∫⁻ b : ℝ³, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) (b - a j')
            ∂((volume : Measure ℝ³).restrict (cube L))
            ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ³).restrict (cube L))))
          ≤ (∫⁻ a : X n, (∫⁻ y : ℝ³, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) y)
              ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ³).restrict (cube L)))) := by
        apply lintegral_mono_ae
        filter_upwards with a
        exact hin a
      apply le_antisymm
      · calc
          (∫⁻ a : X n, ∫⁻ b : ℝ³, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) (b - a j')
              ∂((volume : Measure ℝ³).restrict (cube L))
              ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ³).restrict (cube L))))
              ≤ (∫⁻ a : X n, (∫⁻ y : ℝ³, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) y)
                  ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ³).restrict (cube L)))) := hle
          _ = (∫⁻ a : X n, 0
                ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ³).restrict (cube L)))) := by
                rw [hzero]
          _ = 0 := by
                rw [lintegral_const]
                simp
      · positivity

/-! ## Integrability of `|v (x_i − x_j)|` for `v ∈ L¹` -/

/-- For a measurable `w` with finite `L¹`-norm, `|w (x_i − x_j)|` is integrable over the box. -/
lemma integrableOn_abs_pair_of_measurable {N : ℕ} {L : ℝ} (hL : 0 < L) {w : ℝ³ → ℝ}
    (hwm : Measurable w) (hfin : (∫⁻ y : ℝ³, ‖w y‖ₑ) < ∞) (i j : Fin N) (hij : i ≠ j) :
    IntegrableOn (fun x : X N => |w (x i - x j)|) (box N L) volume := by
  let G : ℝ³ → ℝ≥0∞ := fun y => ENNReal.ofReal |w y|
  have hG : Measurable G := by
    dsimp [G]
    fun_prop
  have hGfin : (∫⁻ y : ℝ³, G y) < ∞ := by
    have hpt : (fun y : ℝ³ => G y) = fun y : ℝ³ => ‖w y‖ₑ := by
      funext y
      dsimp [G]
      rw [← ofReal_norm (w y)]
      rfl
    rw [hpt]
    exact hfin
  have hlt : (∫⁻ x : X N, G (x i - x j) ∂(volume.restrict (box N L))) < ∞ :=
    lintegral_pair_lt_top (N := N) (L := L) hL hG hGfin i j hij
  have hmeas : AEStronglyMeasurable (fun x : X N => |w (x i - x j)|)
      (volume.restrict (box N L)) := by
    exact (by fun_prop : Measurable fun x : X N => |w (x i - x j)|).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  change (∫⁻ x, ‖|w (x i - x j)|‖ₑ ∂(volume.restrict (box N L))) < ∞
  have hnorm : (fun x : X N => ‖|w (x i - x j)|‖ₑ) = fun x : X N => G (x i - x j) := by
    funext x
    dsimp [G]
    rw [Real.enorm_eq_ofReal (abs_nonneg (w (x i - x j)))]
  rw [hnorm]
  exact hlt

/-- For `v ∈ L¹`, `|v (x_i − x_j)|` is integrable over the box. -/
lemma integrableOn_pair_v {N : ℕ} {L : ℝ} (hL : 0 < L) {v : ℝ³ → ℝ}
    (hv : MemLp v 1) (i j : Fin N) :
    IntegrableOn (fun x : X N => |v (x i - x j)|) (box N L) volume := by
  by_cases hij : i = j
  · -- the integrand is the constant `|v 0|`
    subst j
    have hcst : (fun x : X N => |v (x i - x i)|) = fun _ : X N => |v (0 : ℝ³)| := by
      funext x
      congr 1
      simp
    rw [hcst]
    have hfin : (volume : Measure (X N)) (box N L) ≠ ∞ := by
      exact ne_of_lt (IsCompact.measure_lt_top (box_compact hL))
    have hC : ‖(|v (0 : ℝ³)| : ℝ)‖ₑ ≠ ∞ := by
      rw [Real.enorm_eq_ofReal (abs_nonneg (v (0 : ℝ³)))]
      exact ENNReal.ofReal_ne_top
    exact integrableOn_const (s := box N L) (C := |v (0 : ℝ³)|) (hs := hfin) (hC := hC)
  · -- general case: use a measurable representative of `v`
    have hvInt : Integrable v := (memLp_one_iff_integrable.mp hv)
    have hvae : AEMeasurable v := hvInt.aemeasurable
    let w : ℝ³ → ℝ := AEMeasurable.mk v hvae
    have hwm : Measurable w := AEMeasurable.measurable_mk hvae
    have hvw : v =ᵐ[volume] w := AEMeasurable.ae_eq_mk hvae
    have hwInt : Integrable w := hvInt.congr hvw
    have hwfin : (∫⁻ y : ℝ³, ‖w y‖ₑ) < ∞ := by
      exact hwInt.hasFiniteIntegral
    have hmain : IntegrableOn (fun x : X N => |w (x i - x j)|) (box N L) volume :=
      integrableOn_abs_pair_of_measurable hL hwm hwfin i j hij
    -- a.e. equality of the two integrands on the box
    have hN : volume {y : ℝ³ | v y ≠ w y} = 0 := by
      rw [← ae_iff]
      exact hvw
    rcases exists_measurable_superset_of_null (μ := (volume : Measure ℝ³)) hN with
      ⟨t, hNt, htm, ht0⟩
    have hpre : (volume : Measure (X N)).restrict (box N L) {x : X N | x i - x j ∈ t} = 0 :=
      null_preimage_pair hL htm ht0 i j hij
    have hfail : (volume : Measure (X N)).restrict (box N L)
        {x : X N | |v (x i - x j)| ≠ |w (x i - x j)|} = 0 := by
      have hsub : {x : X N | |v (x i - x j)| ≠ |w (x i - x j)|} ⊆
            {x : X N | x i - x j ∈ t} := by
          intro x hx
          apply hNt
          intro hEq
          exact hx (by rw [hEq])
      apply le_antisymm
      · calc
          (volume : Measure (X N)).restrict (box N L) {x : X N | |v (x i - x j)| ≠ |w (x i - x j)|}
              ≤ (volume : Measure (X N)).restrict (box N L) {x : X N | x i - x j ∈ t} :=
                measure_mono hsub
          _ = 0 := hpre
      · positivity
    have hmem : {x : X N | |v (x i - x j)| = |w (x i - x j)|} ∈
        ae (volume.restrict (box N L)) := by
      rw [mem_ae_iff]
      rw [show ({x : X N | |v (x i - x j)| = |w (x i - x j)|}ᶜ) =
          {x : X N | |v (x i - x j)| ≠ |w (x i - x j)|} by ext x; simp]
      exact hfail
    have hae_eq : (fun x : X N => |v (x i - x j)|) =ᵐ[volume.restrict (box N L)]
        (fun x : X N => |w (x i - x j)|) := by
      rw [show (fun x : X N => |v (x i - x j)|) =ᵐ[volume.restrict (box N L)]
            (fun x : X N => |w (x i - x j)|) ↔
          {x : X N | |v (x i - x j)| = |w (x i - x j)|} ∈ ae (volume.restrict (box N L)) by rfl]
      exact hmem
    exact hmain.integrable.congr hae_eq.symm

/-! ## The interaction integrand of a smooth trial state -/

/-- A bound on `Ψ²` (zero outside the box). -/
lemma exists_bound_psi_sq {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : X N, (Ψ : X N → ℝ) x ^ 2 ≤ M := by
  have hcontOn : ContinuousOn (fun x : X N => (Ψ : X N → ℝ) x ^ 2) (box N L) := by
    exact (psi_contDiff Ψ).continuous.continuousOn.pow 2
  rcases IsCompact.exists_bound_of_continuousOn (box_compact hL) hcontOn with ⟨M, hM⟩
  refine ⟨max M 0, le_max_right M 0, ?_⟩
  intro x
  by_cases hx : x ∈ box N L
  · have hb := hM x hx
    have hn : 0 ≤ (Ψ : X N → ℝ) x ^ 2 := sq_nonneg _
    have hsq : (Ψ : X N → ℝ) x ^ 2 ≤ M := by
      simpa [abs_of_nonneg hn] using hb
    exact le_trans hsq (le_max_left M 0)
  · have hz : (Ψ : X N → ℝ) x = 0 := psi_eq_zero_of_not_mem_box Ψ hx
    rw [hz]
    simp

/-- `Ψ²` multiplied by a measurable function stays measurable. -/
lemma measurable_Ψ2_mul {N : ℕ} {L : ℝ} (Ψ : CInfty0Box N L) {f : X N → ℝ}
    (hf : Measurable f) :
    Measurable (fun x : X N => (Ψ : X N → ℝ) x ^ 2 * f x) := by
  have hΨ : Measurable (fun x : X N => (Ψ : X N → ℝ) x) := (psi_contDiff Ψ).continuous.measurable
  have hsq : Measurable (fun x : X N => (Ψ : X N → ℝ) x ^ 2) := by
    convert hΨ.mul hΨ using 1
    funext x
    rw [pow_two, Pi.mul_apply]
  convert hsq.mul hf using 1
  all_goals (funext x; rw [Pi.mul_apply])

/-- For measurable `w` with finite `L¹`-norm the smooth-state interaction integrand is
integrable over the box. -/
lemma integrableOn_intIntegrand_of_measurable {N : ℕ} {L : ℝ} (hL : 0 < L)
    {w : ℝ³ → ℝ} (hwm : Measurable w) (hfin : (∫⁻ y : ℝ³, ‖w y‖ₑ) < ∞)
    (Ψ : CInfty0Box N L) :
    IntegrableOn (intIntegrand N L w Ψ) (box N L) volume := by
  let F : Finset (Fin N × Fin N) := Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)
  let μ_box : Measure (X N) := volume.restrict (box N L)
  rcases exists_bound_psi_sq hL Ψ with ⟨M, hM0, hM⟩
  have hpair : ∀ p : Fin N × Fin N, p ∈ F →
      IntegrableOn (fun x : X N => |w (x p.1 - x p.2)|) (box N L) volume := by
    intro p hp
    apply integrableOn_abs_pair_of_measurable hL hwm hfin
    exact ne_of_lt (Finset.mem_filter.mp hp).2
  have hterm : ∀ p : Fin N × Fin N, p ∈ F →
      Integrable (fun x : X N => (Ψ : X N → ℝ) x ^ 2 * w (x p.1 - x p.2)) μ_box := by
    intro p hp
    have hw : Measurable (fun x : X N => w (x p.1 - x p.2)) := by
      fun_prop
    have hmeas : AEStronglyMeasurable
        (fun x : X N => (Ψ : X N → ℝ) x ^ 2 * w (x p.1 - x p.2)) μ_box := by
      exact (measurable_Ψ2_mul Ψ hw).aestronglyMeasurable
    refine Integrable.mono' (μ := μ_box)
      (f := fun x : X N => (Ψ : X N → ℝ) x ^ 2 * w (x p.1 - x p.2))
      (g := fun x : X N => M * |w (x p.1 - x p.2)|) ?_ hmeas ?_
    · simpa using ((hpair p hp).integrable.const_mul M)
    · filter_upwards with x
      have hb : |(Ψ : X N → ℝ) x ^ 2| ≤ M := by
        rw [abs_of_nonneg (sq_nonneg _)]
        exact hM x
      calc
        ‖(Ψ : X N → ℝ) x ^ 2 * w (x p.1 - x p.2)‖
            = |(Ψ : X N → ℝ) x ^ 2| * |w (x p.1 - x p.2)| := by simp
        _ ≤ M * |w (x p.1 - x p.2)| := by
            exact mul_le_mul hb le_rfl (abs_nonneg _) hM0
  have hS : Integrable (fun x : X N => ∑ p ∈ F,
      (Ψ : X N → ℝ) x ^ 2 * w (x p.1 - x p.2)) μ_box := by
    apply integrable_finsetSum (s := F)
      (f := fun (p : Fin N × Fin N) (x : X N) => (Ψ : X N → ℝ) x ^ 2 * w (x p.1 - x p.2))
    intro p hp
    exact hterm p hp
  have hint : Integrable (intIntegrand N L w Ψ) μ_box := by
    convert hS using 1
    funext x
    unfold intIntegrand
    rw [Finset.mul_sum]
  exact hint

/-- If `v = w` almost everywhere then the interaction integrands agree almost everywhere. -/
lemma ae_intIntegrand_of_ae {N : ℕ} {L : ℝ} (hL : 0 < L) {v w : ℝ³ → ℝ}
    (hvw : v =ᵐ[volume] w) (Ψ : CInfty0Box N L) :
    intIntegrand N L v Ψ =ᵐ[volume.restrict (box N L)] intIntegrand N L w Ψ := by
  let F : Finset (Fin N × Fin N) := Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)
  have hN : volume {y : ℝ³ | v y ≠ w y} = 0 := by
    rw [← ae_iff]
    exact hvw
  rcases exists_measurable_superset_of_null (μ := (volume : Measure ℝ³)) hN with ⟨t, hNt, htm, ht0⟩
  have hpre : ∀ p : Fin N × Fin N, p.1 < p.2 →
      (volume : Measure (X N)).restrict (box N L) {x : X N | x p.1 - x p.2 ∈ t} = 0 := by
    intro p hp
    exact null_preimage_pair hL htm ht0 p.1 p.2 (ne_of_lt hp)
  let U : Set (X N) := {x : X N | ∃ p : Fin N × Fin N, p ∈ F ∧ x p.1 - x p.2 ∈ t}
  have hU0 : (volume : Measure (X N)).restrict (box N L) U = 0 := by
    have hUeq : U = (⋃ p ∈ F, ({x : X N | x p.1 - x p.2 ∈ t} : Set (X N))) := by
      ext x
      simp [U]
    rw [hUeq]
    apply le_antisymm
    · calc
        (volume : Measure (X N)).restrict (box N L) (⋃ p ∈ F, {x : X N | x p.1 - x p.2 ∈ t})
            ≤ ∑ p ∈ F, (volume : Measure (X N)).restrict (box N L)
                {x : X N | x p.1 - x p.2 ∈ t} :=
              measure_biUnion_finset_le F (fun p : Fin N × Fin N => {x : X N | x p.1 - x p.2 ∈ t})
        _ = 0 := by
              apply Finset.sum_eq_zero
              intro p hp
              exact hpre p (Finset.mem_filter.mp hp).2
    · positivity
  have hsubset : {x : X N | intIntegrand N L v Ψ x ≠ intIntegrand N L w Ψ x} ⊆ U := by
    intro x hx
    dsimp [U]
    by_contra hnot
    have hno : ∀ p : Fin N × Fin N, p ∈ F → x p.1 - x p.2 ∉ t := by
      intro p hp ht'
      exact hnot ⟨p, hp, ht'⟩
    have halleq : ∀ p : Fin N × Fin N, p ∈ F → v (x p.1 - x p.2) = w (x p.1 - x p.2) := by
      intro p hp
      by_cases heq : v (x p.1 - x p.2) = w (x p.1 - x p.2)
      · exact heq
      · exfalso
        exact hno p hp (hNt heq)
    apply hx
    calc
      intIntegrand N L v Ψ x = (Ψ : X N → ℝ) x ^ 2 *
          (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)),
            v (x p.1 - x p.2)) := by
              rfl
      _ = (Ψ : X N → ℝ) x ^ 2 *
          (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)),
            w (x p.1 - x p.2)) := by
              apply congrArg (fun r : ℝ => (Ψ : X N → ℝ) x ^ 2 * r)
              apply Finset.sum_congr rfl
              intro p hp
              exact halleq p hp
      _ = intIntegrand N L w Ψ x := by
              rfl
  have hmem : {x : X N | intIntegrand N L v Ψ x = intIntegrand N L w Ψ x} ∈
      ae (volume.restrict (box N L)) := by
    rw [mem_ae_iff]
    rw [show ({x : X N | intIntegrand N L v Ψ x = intIntegrand N L w Ψ x}ᶜ) =
        {x : X N | intIntegrand N L v Ψ x ≠ intIntegrand N L w Ψ x} by ext x; simp]
    apply le_antisymm
    · calc
        (volume : Measure (X N)).restrict (box N L)
            {x : X N | intIntegrand N L v Ψ x ≠ intIntegrand N L w Ψ x}
            ≤ (volume : Measure (X N)).restrict (box N L) U := measure_mono hsubset
        _ = 0 := hU0
    · positivity
  rw [show intIntegrand N L v Ψ =ᵐ[volume.restrict (box N L)] intIntegrand N L w Ψ ↔
      {x : X N | intIntegrand N L v Ψ x = intIntegrand N L w Ψ x} ∈
        ae (volume.restrict (box N L)) by rfl]
  exact hmem

/-- For a smooth trial state the interaction integrand is integrable over the box. -/
lemma integrableOn_intIntegrand {N : ℕ} {L : ℝ} (hL : 0 < L) {v : ℝ³ → ℝ}
    (hv : MemLp v 1) (Ψ : CInfty0Box N L) :
    IntegrableOn (intIntegrand N L v Ψ) (box N L) volume := by
  have hvInt : Integrable v := (memLp_one_iff_integrable.mp hv)
  have hvae : AEMeasurable v := hvInt.aemeasurable
  let w : ℝ³ → ℝ := AEMeasurable.mk v hvae
  have hwm : Measurable w := AEMeasurable.measurable_mk hvae
  have hvw : v =ᵐ[volume] w := AEMeasurable.ae_eq_mk hvae
  have hwInt : Integrable w := hvInt.congr hvw
  have hwfin : (∫⁻ y : ℝ³, ‖w y‖ₑ) < ∞ := hwInt.hasFiniteIntegral
  have hmain : IntegrableOn (intIntegrand N L w Ψ) (box N L) volume :=
    integrableOn_intIntegrand_of_measurable hL hwm hwfin Ψ
  have hae := ae_intIntegrand_of_ae (L := L) hL hvw Ψ
  exact hmain.integrable.congr hae.symm

/-- For an `L¹` potential the numerator of the Rayleigh quotient splits as kinetic plus
interaction energy, for every smooth trial state. -/
lemma energy_decomposition_admissible (N : ℕ) {L : ℝ} (hL : 0 < L) {v : ℝ³ → ℝ}
    (hv : MemLp v 1) (Ψ : CInfty0Box N L) :
    (∫ x in box N L, (Ψ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x) =
      kineticEnergy N L Ψ + interactionEnergy N L v Ψ := by
  exact energy_decomposition N L v Ψ hL (integrableOn_intIntegrand hL hv Ψ)

end

end BoseGases

end Submission
