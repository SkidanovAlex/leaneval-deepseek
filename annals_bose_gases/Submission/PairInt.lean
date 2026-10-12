import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.Shift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Whole-space integrability of two-body interaction terms

For a smooth-enough (continuous), compactly supported weight `φ : X N → ℝ` and
a potential `v ∈ L¹(ℝ³)`, the two-body term `x ↦ φ x * v (x i - x j)` is
genuinely integrable over the whole configuration space `X N`.

Strategy (all machinery exists upstream):
  * the compact support of `φ` lies in a *translated* standard box:
    `tsupport φ ⊆ {x | x + w ∈ box N L}` for a suitable `w : X N` and `L > 0`
    (a common shift `w` per coordinate);
  * `x ↦ v (x i - x j)` is integrable over the standard box for `v ∈ L¹`
    (`Submission.Potential.integrableOn_pair_v`);
  * the common translation `x ↦ x + w` is measure-preserving
    (`measurePreserving_shiftAll`) and leaves `x i - x j` invariant, so the
    whole-space integral of the compactly supported `|φ x · v (x i - x j)|`
    reduces to the box integral of a bounded multiple of `|v (x i - x j)|`;
  * `φ` is bounded on its compact support (continuous + `HasCompactSupport`).
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped Topology Real ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

noncomputable section

/-- The constant vector all of whose coordinates equal `r`. -/
abbrev constVec (r : ℝ) : ℝ³ := WithLp.toLp 2 (fun _ : Fin 3 => r)

/-- A coordinate of `x : ℝ³` is bounded by the norm. -/
lemma coord_abs_le_norm (y : ℝ³) (k : Fin 3) : |(y.ofLp k)| ≤ ‖y‖ := by
  have hk : (y.ofLp k) ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (fun i hi => sq_nonneg (y.ofLp i)) (Finset.mem_univ k)
  have h := sq_le_sq.mp hk
  simpa [abs_of_nonneg (norm_nonneg y)] using h

/-- The compact support of `φ` is contained in the cube `[-r,r]³` in each
coordinate. -/
lemma tsupport_coord_bounds {N : ℕ} {φ : X N → ℝ} (hcs : HasCompactSupport φ) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ tsupport φ, ∀ i : Fin N, ∀ k : Fin 3,
      (x i).ofLp k ∈ Set.Icc (-r) r := by
  have hb : Bornology.IsBounded (tsupport φ) := hcs.isBounded
  rcases hb.subset_closedBall_lt (a := 0) (c := (0 : X N)) with ⟨r, hr0, hrsub⟩
  refine ⟨r, hr0, ?_⟩
  intro x hx i k
  have hxr : ‖x‖ ≤ r := by
    simpa [dist_eq_norm] using (hrsub hx)
  have hnorm : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
  have hle : |(x i).ofLp k| ≤ ‖x i‖ := coord_abs_le_norm (x i) k
  have hbnd : |(x i).ofLp k| ≤ r := le_trans (le_trans hle hnorm) hxr
  exact abs_le.mp hbnd

/-- A configuration with all coordinates in `[-r,r]³`, shifted by the constant
vector `(r,r,r)`, lies in the box `box N (2r)`. -/
lemma config_mem_shift_box {N : ℕ} {r : ℝ} {x : X N}
    (hx : ∀ i : Fin N, ∀ k : Fin 3, (x i).ofLp k ∈ Set.Icc (-r) r) :
    shiftAll N (fun _ : Fin N => constVec r) x ∈ box N (2 * r) := by
  intro i k
  have hk := hx i k
  have hshift : (shiftAll N (fun _ : Fin N => constVec r) x) i k = (x i).ofLp k + r := by
    simp [shiftAll, constVec]
  rw [hshift]
  constructor <;> linarith [hk.1, hk.2]

/-- Change of variables: for a common shift `w` (with `w i = w j`), the
lintegral of `G (x i - x j)` over the shifted box `{x | x + w ∈ box N L}`
equals the lintegral over the standard box. -/
lemma lintegral_shiftBox {N : ℕ} {L : ℝ} (w : X N) (G : ℝ³ → ℝ≥0∞) (hG : Measurable G)
    (i j : Fin N) (hij_diff : w i = w j) :
    (∫⁻ x in (shiftAll N w ⁻¹' box N L), G (x i - x j)) =
      (∫⁻ y in box N L, G (y i - y j)) := by
  have hmp : MeasurePreserving (shiftAll N w)
      (volume.restrict (shiftAll N w ⁻¹' box N L)) (volume.restrict (box N L)) :=
    MeasurePreserving.restrict_preimage (measurePreserving_shiftAll N w)
      (s := box N L) (hs := (box_closed L).measurableSet)
  have hG2meas : Measurable (fun y : X N => G (y i - y j)) := by fun_prop
  have hpt : ∀ x : X N, G (x i - x j) = (fun y : X N => G (y i - y j)) (shiftAll N w x) := by
    intro x
    congr 1
    dsimp [shiftAll]
    rw [hij_diff]
    abel
  calc
    (∫⁻ x in (shiftAll N w ⁻¹' box N L), G (x i - x j))
        = ∫⁻ x in (shiftAll N w ⁻¹' box N L), (fun y : X N => G (y i - y j)) (shiftAll N w x) := by
            apply lintegral_congr
            intro x
            exact hpt x
    _ = ∫⁻ y in box N L, (fun y : X N => G (y i - y j)) y := by
            exact MeasurePreserving.lintegral_comp hmp hG2meas
    _ = ∫⁻ y in box N L, G (y i - y j) := rfl

/-- Iterated-integral splitting of `G (x i - x j)` over the full volume. -/
lemma lintegral_pair_eq_iterated_volume {n : ℕ} {G : ℝ³ → ℝ≥0∞} (hG : Measurable G)
    (i j : Fin (n + 1)) (j' : Fin n) (hjj' : i.succAbove j' = j) :
    (∫⁻ x : X (n + 1), G (x i - x j)) =
      (∫⁻ a : X n, ∫⁻ b : ℝ³, G (b - a j')
        ∂(volume : Measure ℝ³)
        ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ³)))) := by
  have hbox : (volume : Measure (X (n + 1))) = Measure.pi (fun _ : Fin (n + 1) => (volume : Measure ℝ³)) := by rfl
  have hmp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i)
      (Measure.pi (fun _ : Fin (n + 1) => (volume : Measure ℝ³)))
      ((volume : Measure ℝ³).prod (Measure.pi (fun _ : Fin n => (volume : Measure ℝ³)))) := by
    simpa using (measurePreserving_piFinSuccAbove (μ := fun _ : Fin (n + 1) => (volume : Measure ℝ³)) i)
  have hF : Measurable (fun q : ℝ³ × X n => G (q.1 - q.2 j')) := by fun_prop
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
  have htr := MeasureTheory.MeasurePreserving.lintegral_comp hmp hF
  calc
    (∫⁻ x : X (n + 1), G (x i - x j) ∂(volume : Measure (X (n + 1))))
        = ∫⁻ x : X (n + 1), G (x i - x j)
            ∂(Measure.pi (fun _ : Fin (n + 1) => (volume : Measure ℝ³))) := by rw [hbox]
    _ = ∫⁻ p : ℝ³ × X n, G (p.1 - p.2 j')
            ∂((volume : Measure ℝ³).prod (Measure.pi (fun _ : Fin n => (volume : Measure ℝ³)))) := by
          rw [← htr]
          apply lintegral_congr_ae
          filter_upwards with x
          exact (hpt x).symm
    _ = (∫⁻ a : X n, ∫⁻ b : ℝ³, G (b - a j')
          ∂(volume : Measure ℝ³)
          ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ³)))) := by
          simpa using (lintegral_prod_symm (μ := (volume : Measure ℝ³))
            (ν := (Measure.pi (fun _ : Fin n => (volume : Measure ℝ³))))
            (f := fun q : ℝ³ × X n => G (q.1 - q.2 j')) hF.aemeasurable)

/-- For `i ≠ j`, the preimage of a Lebesgue-null set under `x ↦ x i - x j` is
null in the whole configuration space. -/
lemma null_preimage_pair_whole {N : ℕ} {s : Set ℝ³} (hs : MeasurableSet s)
    (hs0 : volume s = 0) (i j : Fin N) (hij : i ≠ j) :
    (volume : Measure (X N)) {x : X N | x i - x j ∈ s} = 0 := by
  have hG : Measurable (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) := by
    exact Measurable.indicator (by measurability : Measurable fun _ : ℝ³ => (1 : ℝ≥0∞)) hs
  have hAmeas : MeasurableSet {x : X N | x i - x j ∈ s} := by measurability
  have hval : (volume : Measure (X N)) {x : X N | x i - x j ∈ s}
      = ∫⁻ x : X N, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) (x i - x j) := by
    calc
      (volume : Measure (X N)) {x : X N | x i - x j ∈ s}
          = ∫⁻ x : X N in {x : X N | x i - x j ∈ s}, (1 : ℝ≥0∞) := by
              rw [lintegral_const]
              simp
      _ = ∫⁻ x : X N, (({x : X N | x i - x j ∈ s} : Set (X N)).indicator (fun _ : X N => (1 : ℝ≥0∞))) x := by
              exact (lintegral_indicator hAmeas (fun _ : X N => (1 : ℝ≥0∞))).symm
      _ = ∫⁻ x : X N, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) (x i - x j) := by
              apply lintegral_congr
              intro x
              by_cases hx : x i - x j ∈ s <;> simp [hx]
  rw [hval]
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      let j' : Fin n := Classical.choose (Fin.exists_succAbove_eq (x := j) (y := i) hij.symm)
      have hjj' : i.succAbove j' = j := by
        simpa [j'] using (Classical.choose_spec (Fin.exists_succAbove_eq (x := j) (y := i) hij.symm))
      have heq := lintegral_pair_eq_iterated_volume (G := s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) hG i j j' hjj'
      rw [heq]
      have hin : ∀ a : X n,
          (∫⁻ b : ℝ³, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) (b - a j')) = 0 := by
        intro a
        calc
          (∫⁻ b : ℝ³, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) (b - a j'))
              = ∫⁻ b : ℝ³, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) b := by
                  exact MeasurePreserving.lintegral_comp (measurePreserving_sub_right (a j')) hG
          _ = 0 := by
                  rw [lintegral_indicator hs]
                  rw [lintegral_const]
                  simp [hs0]
      calc
        (∫⁻ a : X n, ∫⁻ b : ℝ³, (s.indicator (fun _ : ℝ³ => (1 : ℝ≥0∞))) (b - a j')
            ∂(volume : Measure ℝ³)
            ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ³))))
            = ∫⁻ a : X n, (0 : ℝ≥0∞)
                ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ³))) := by
                apply lintegral_congr
                intro a
                exact hin a
        _ = 0 := by
                rw [lintegral_const]
                simp

/-- Monotonicity of the extended norm in `|·|` for real values. -/
lemma enorm_le_of_abs_le {M : ℝ} (hM0 : 0 ≤ M) (a : ℝ) (ha : |a| ≤ M) : ‖a‖ₑ ≤ ‖(M : ℝ)‖ₑ := by
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
  exact ENNReal.coe_le_coe.mpr (by
    exact NNReal.coe_le_coe.mp (by
      simpa [abs_of_nonneg hM0] using ha))

/-- A continuous function with compact support is bounded, and vanishes off its
topological support. -/
lemma exists_bound_of_hasCompactSupport {N : ℕ} {φ : X N → ℝ} (hφ : Continuous φ)
    (hcs : HasCompactSupport φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : X N, |φ x| ≤ M ∧ (x ∉ tsupport φ → φ x = 0) := by
  rcases IsCompact.exists_bound_of_continuousOn hcs hφ.continuousOn with ⟨C, hC⟩
  let M : ℝ := max C 0
  refine ⟨M, le_max_right C 0, ?_⟩
  intro x
  constructor
  · by_cases hx : x ∈ tsupport φ
    · have hb : |φ x| ≤ C := by simpa [Real.norm_eq_abs] using hC x hx
      exact le_trans hb (le_max_left C 0)
    · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hz, M]
  · intro hx
    exact image_eq_zero_of_notMem_tsupport hx

/-- A continuous function with compact support is integrable. -/
lemma integrable_of_continuous_hasCompactSupport {N : ℕ} {φ : X N → ℝ} (hφ : Continuous φ)
    (hcs : HasCompactSupport φ) : Integrable φ volume := by
  rcases exists_bound_of_hasCompactSupport hφ hcs with ⟨M, hM0, hφM⟩
  refine ⟨hφ.measurable.aestronglyMeasurable, ?_⟩
  have hKmeas : MeasurableSet (tsupport φ) := hcs.measurableSet
  have hb : ∀ x, ‖φ x‖ₑ ≤ ‖(M : ℝ)‖ₑ * ((tsupport φ).indicator (fun _ : X N => (1 : ℝ≥0∞))) x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · rw [Set.indicator_of_mem hx, mul_one]
      exact enorm_le_of_abs_le hM0 (φ x) (hφM x).1
    · have hz : φ x = 0 := (hφM x).2 hx
      simp [hx, hz]
  refine lt_of_le_of_lt (lintegral_mono hb) ?_
  calc
    (∫⁻ x : X N, ‖(M : ℝ)‖ₑ * ((tsupport φ).indicator (fun _ : X N => (1 : ℝ≥0∞))) x)
        = (∫⁻ x : X N, ((tsupport φ).indicator (fun _ : X N => ‖(M : ℝ)‖ₑ)) x) := by
            apply lintegral_congr
            intro x
            by_cases hx : x ∈ tsupport φ <;> simp [hx]
    _ = ∫⁻ x : X N in tsupport φ, ‖(M : ℝ)‖ₑ := lintegral_indicator hKmeas (fun _ : X N => ‖(M : ℝ)‖ₑ)
    _ = ‖(M : ℝ)‖ₑ * (volume : Measure (X N)) (tsupport φ) := by
            rw [lintegral_const]
            simp
    _ < (⊤ : ℝ≥0∞) := ENNReal.mul_lt_top (by
        rw [Real.enorm_eq_ofReal hM0]
        exact ENNReal.ofReal_lt_top) (IsCompact.measure_lt_top hcs)

/-- Core integrability for a measurable potential with finite `L¹`-lintegral
(valid for `i ≠ j`). -/
lemma integrable_mul_pair_meas {N : ℕ} {v : ℝ³ → ℝ} (hvm : Measurable v)
    (hvfin : (∫⁻ y : ℝ³, ‖v y‖ₑ) < (∞ : ℝ≥0∞)) {φ : X N → ℝ} (hφ : Continuous φ)
    (hcs : HasCompactSupport φ) (i j : Fin N) (hij : i ≠ j) :
    Integrable (fun x : X N => φ x * v (x i - x j)) volume := by
  rcases tsupport_coord_bounds hcs with ⟨r, hr0, hrcoord⟩
  let w0 : X N := fun _ : Fin N => constVec r
  let L : ℝ := 2 * r
  let S : Set (X N) := shiftAll N w0 ⁻¹' box N L
  have hKsubS : tsupport φ ⊆ S := by
    intro x hx
    dsimp [S, w0, L]
    exact config_mem_shift_box (fun i k => hrcoord x hx i k)
  rcases exists_bound_of_hasCompactSupport hφ hcs with ⟨M, hM0, hφM⟩
  have hLpos : 0 < L := by
    dsimp [L]
    exact mul_pos (by norm_num) hr0
  have hct : Continuous (shiftAll N w0) := by
    unfold shiftAll
    exact continuous_id.add (continuous_const : Continuous (fun _ : X N => w0))
  have hsmeas : MeasurableSet S := by
    dsimp [S]
    exact hct.measurable (box_closed L).measurableSet
  have hdiffmeas : Measurable (fun x : X N => x i - x j) := by
    exact (continuous_apply i).sub (continuous_apply j) |>.measurable
  have hvmeascomp : Measurable (fun x : X N => v (x i - x j)) := hvm.comp hdiffmeas
  have hφvmul : Measurable (fun x : X N => φ x * v (x i - x j)) :=
    (hφ.measurable).mul hvmeascomp
  have hGmeas : Measurable (fun y : ℝ³ => ‖v y‖ₑ) := (continuous_enorm.measurable).comp hvm
  have hmeasV : Measurable (fun x : X N => ‖v (x i - x j)‖ₑ) := hGmeas.comp hdiffmeas
  let E : ℝ≥0∞ := ‖(M : ℝ)‖ₑ
  have hbE : ∀ x, ‖φ x‖ₑ ≤ E * (S.indicator (fun _ : X N => (1 : ℝ≥0∞))) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, mul_one]
      dsimp [E]
      exact enorm_le_of_abs_le hM0 (φ x) (hφM x).1
    · have hnotK : x ∉ tsupport φ := by
        intro hxK
        exact hx (hKsubS hxK)
      have hz : φ x = 0 := (hφM x).2 hnotK
      simp [hx, hz]
  have hbnd : ∀ x, ‖φ x * v (x i - x j)‖ₑ ≤
      E * (S.indicator (fun _ : X N => (1 : ℝ≥0∞))) x * ‖v (x i - x j)‖ₑ := by
    intro x
    calc
      ‖φ x * v (x i - x j)‖ₑ = ‖φ x‖ₑ * ‖v (x i - x j)‖ₑ := enorm_mul (φ x) (v (x i - x j))
      _ ≤ (E * (S.indicator (fun _ : X N => (1 : ℝ≥0∞))) x) * ‖v (x i - x j)‖ₑ :=
        mul_le_mul_of_nonneg_right (hbE x) bot_le
  have hSfin : (∫⁻ x : X N in S, ‖v (x i - x j)‖ₑ) < (∞ : ℝ≥0∞) := by
    dsimp [S, w0, L]
    rw [lintegral_shiftBox (w := (fun _ : Fin N => constVec r))
        (G := fun y : ℝ³ => ‖v y‖ₑ) (hG := hGmeas) (i := i) (j := j) (hij_diff := by rfl)]
    exact lintegral_pair_lt_top (L := 2 * r) (hL := mul_pos (by norm_num) hr0) hGmeas hvfin i j hij
  refine ⟨hφvmul.aestronglyMeasurable, ?_⟩
  change (∫⁻ x : X N, ‖φ x * v (x i - x j)‖ₑ) < ∞
  refine lt_of_le_of_lt (lintegral_mono hbnd) ?_
  calc
    (∫⁻ x : X N, E * (S.indicator (fun _ : X N => (1 : ℝ≥0∞))) x * ‖v (x i - x j)‖ₑ)
        = (∫⁻ x : X N, (S.indicator (fun y : X N => E * ‖v (y i - y j)‖ₑ)) x) := by
            apply lintegral_congr
            intro x
            by_cases hx : x ∈ S <;> simp [hx]
    _ = ∫⁻ x : X N in S, E * ‖v (x i - x j)‖ₑ := lintegral_indicator hsmeas _
    _ = E * (∫⁻ x : X N in S, ‖v (x i - x j)‖ₑ) := by
            exact lintegral_const_mul (μ := (volume : Measure (X N)).restrict S) E hmeasV
    _ < (∞ : ℝ≥0∞) := ENNReal.mul_lt_top (by
            dsimp [E]
            rw [Real.enorm_eq_ofReal hM0]
            exact ENNReal.ofReal_lt_top) hSfin

/-- For `v ∈ L¹(ℝ³)` and continuous compactly-supported `φ : X N → ℝ`, the
two-body integrand `x ↦ φ x * v (x i - x j)` is integrable over `X N`. -/
lemma pairInt_mul {N : ℕ} {v : ℝ³ → ℝ} (hv1 : MemLp v 1) {φ : X N → ℝ}
    (hφ : Continuous φ) (hcs : HasCompactSupport φ) (i j : Fin N) :
    Integrable (fun x : X N => φ x * v (x i - x j)) volume := by
  by_cases hij : i = j
  · subst j
    have harg : ∀ x : X N, x i - x i = (0 : ℝ³) := by intro x; simp
    have heq : (fun x : X N => φ x * v (x i - x i)) =
        fun x : X N => φ x * v (0 : ℝ³) := by
      funext x
      rw [harg x]
    rw [heq]
    have hφint : Integrable φ volume := integrable_of_continuous_hasCompactSupport hφ hcs
    simpa [mul_comm] using hφint.const_mul (v (0 : ℝ³))
  · have hvInt : Integrable v := memLp_one_iff_integrable.mp hv1
    have hvae : AEMeasurable v := hvInt.aemeasurable
    let w : ℝ³ → ℝ := AEMeasurable.mk v hvae
    have hwm : Measurable w := AEMeasurable.measurable_mk hvae
    have hvw : v =ᵐ[volume] w := AEMeasurable.ae_eq_mk hvae
    have hwInt : Integrable w := hvInt.congr hvw
    have hwfin : (∫⁻ y : ℝ³, ‖w y‖ₑ) < (∞ : ℝ≥0∞) := hwInt.hasFiniteIntegral
    have hwmain : Integrable (fun x : X N => φ x * w (x i - x j)) volume :=
      integrable_mul_pair_meas hwm hwfin hφ hcs i j hij
    have hN : volume {y : ℝ³ | v y ≠ w y} = 0 := by
      rw [← ae_iff]
      exact hvw
    rcases exists_measurable_superset_of_null (μ := (volume : Measure ℝ³)) hN with
      ⟨t, hNt, htm, ht0⟩
    have hpre : (volume : Measure (X N)) {x : X N | x i - x j ∈ t} = 0 :=
      null_preimage_pair_whole htm ht0 i j hij
    have hfail : (volume : Measure (X N))
        {x : X N | φ x * w (x i - x j) ≠ φ x * v (x i - x j)} = 0 := by
      have hsub : {x : X N | φ x * w (x i - x j) ≠ φ x * v (x i - x j)} ⊆
          {x : X N | x i - x j ∈ t} := by
        intro x hx
        apply hNt
        intro hEq
        exact hx (by rw [hEq])
      apply le_antisymm
      · calc
          (volume : Measure (X N)) {x : X N | φ x * w (x i - x j) ≠ φ x * v (x i - x j)}
              ≤ (volume : Measure (X N)) {x : X N | x i - x j ∈ t} := measure_mono hsub
          _ = 0 := hpre
      · positivity
    have hmem : {x : X N | φ x * w (x i - x j) = φ x * v (x i - x j)} ∈
        ae (volume : Measure (X N)) := by
      rw [mem_ae_iff]
      rw [show ({x : X N | φ x * w (x i - x j) = φ x * v (x i - x j)}ᶜ) =
          {x : X N | φ x * w (x i - x j) ≠ φ x * v (x i - x j)} by ext x; simp]
      exact hfail
    have hae : (fun x : X N => φ x * w (x i - x j)) =ᵐ[volume]
        (fun x : X N => φ x * v (x i - x j)) := by
      rw [show (fun x : X N => φ x * w (x i - x j)) =ᵐ[volume]
            (fun x : X N => φ x * v (x i - x j)) ↔
          {x : X N | φ x * w (x i - x j) = φ x * v (x i - x j)} ∈ ae (volume : Measure (X N)) by rfl]
      exact hmem
    exact hwmain.congr hae

/-- For `v ∈ L¹(ℝ³)` and continuous compactly-supported `φ : X N → ℝ`, the
squared-weight two-body integrand `x ↦ (φ x)^2 * v (x i - x j)` is integrable
over `X N` (immediate corollary of `pairInt_mul` applied to `φ²`). -/
lemma pairInt_sq {N : ℕ} {v : ℝ³ → ℝ} (hv1 : MemLp v 1) {φ : X N → ℝ}
    (hφ : Continuous φ) (hcs : HasCompactSupport φ) (i j : Fin N) :
    Integrable (fun x : X N => (φ x) ^ 2 * v (x i - x j)) volume := by
  let ψ : X N → ℝ := fun x => (φ x) ^ 2
  have hψ : Continuous ψ := by
    dsimp [ψ]
    exact hφ.pow 2
  have hsupp : Function.support (fun x : X N => (φ x) ^ 2) = Function.support φ := by
    ext x
    change (φ x) ^ 2 ≠ 0 ↔ φ x ≠ 0
    constructor
    · intro hx hφ0
      exact hx (by rw [hφ0]; norm_num)
    · intro hx
      exact pow_ne_zero 2 hx
  have hts : tsupport (fun x : X N => (φ x) ^ 2) = tsupport φ := by
    unfold tsupport
    rw [hsupp]
  have hcsψ : HasCompactSupport ψ := by
    change IsCompact (tsupport ψ)
    dsimp [ψ]
    rw [hts]
    exact hcs
  simpa [ψ] using (pairInt_mul hv1 hψ hcsψ i j)

end

end BoseGases

end Submission
