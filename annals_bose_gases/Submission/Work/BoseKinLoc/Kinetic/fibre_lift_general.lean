import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Compare.compare_box_energy
import Submission.Work.BoseKinLoc.Kinetic.continuous_fibre_sq_diff
import Submission.Work.BoseKinLoc.Kinetic.dSpace_fibre_eq
import Submission.Work.BoseKinLoc.Kinetic.fsT_bound_abs
import Submission.Work.BoseKinLoc.Kinetic.gapBare_fibre_aemeasurable
import Submission.Work.BoseKinLoc.Kinetic.integral_fibre_sq
import Submission.Work.BoseKinLoc.Kinetic.mainWord_fibre_aemeasurable
import Submission.Work.BoseKinLoc.Kinetic.momForm_fibre_aemeasurable
import Submission.Work.BoseKinLoc.Kinetic.momForm_le_box
import Submission.Work.BoseKinLoc.Kinetic.slotForm_eq_fibre_integral
import Submission.Work.BoseKinLoc.NeuFrac.bddBelow_trialSet_of_integrableOn
import Submission.Work.BoseKinLoc.NeuFrac.neuFrac_add_const_L2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Kinetic.fibre_lift_general` — the `N`-body lifting at a general box radius

`Kinetic/fibre_lift.lean` lifts FS `lem:LocKinEn` (`∫_u 𝒯_u du ≤ −Δ`, the residual
`Work.BoseKinLoc.KineticLocalisation c₀`) to `N` particles *for states supported in the
centred box `abox N ℓ` of the localisation scale* `ℓ`.  The comparison theorem
`Compare.compare_box_energy` consumes the lifting for states supported in the *state's* box
`abox N L`, with `L` unrelated to the localisation scale `ℓ` (`0 ≤ L` is all that is known).

This file proves that general form:

  `∫_u kinForm N ℓ d s εT b u Φ  ≤  Σ_i ∫_x Σ_k (∂_{i,k}Φ)²`

for `Φ ∈ C^∞` with `tsupport Φ ⊆ abox N L`, `0 ≤ L`.

## The proof (the `fibre_lift` argument, with the two support inputs generalised)

Write `N = n+1`.  The slot-`i` fibre `genFibre i Φ r : z ↦ Φ (kcInsN n i (z,r))` is smooth,
compactly supported (it is supported in `acube L`, which is compact because `L ≥ 0`) and hence
admissible for `hKin`.  For each slot:

* the slot word peels, `slotForm (n+1) q ℓ u i Φ = ∫_r q (genFibre i Φ r)`
  (`slotForm_eq_fibre_integral`);
* the `(u,r)`-integrand `F u r = fsT ℓ d s εT b u (genFibre i Φ r)` is jointly measurable
  (the four `fsT`-words, `*_fibre_aemeasurable`), and is dominated by
  `C·1_{Λ(u)∩acube L ≠ ∅}·M(r)` with `M r = ∫ψ_r² + Σ_k∫(∂_kψ_r)²` integrable
  (`fsT_bound_abs` + the support estimate, `integral_fibre_sq`, `dSpace_fibre_eq`), so the
  Fubini exchange is legitimate;
* for a.e. `r` the fibre is admissible for `hKin`, giving `∫_u F u r ≤ dSpace (genFibre i Φ r)`;
* finally `∫_r dSpace (genFibre i Φ r)` is the slot-`i` kinetic energy of `Φ`
  (`dSpace_fibre_eq`).

The only difference from `Kinetic/fibre_lift.lean` is that the support radius is `L`, not `ℓ`:
the fibre's vanishing set is the complement of the cover `coverBoxU ℓ L` (a subset of the
bounded cube `acube ((L+ℓ)/ℓ)`), and compact support of the fibre comes from
`acube_compact_of_nonneg`.  The fibre API (`genFibre`) is repeated here, in the form needed at a
general radius `L`, so that this module only depends on the modules whose statements it uses.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Kinetic

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false


/-! ## 1. Compactness of the box at a nonnegative radius -/

/-- The centred cube is compact for `0 ≤ ℓ` (the corpus proves this for `0 < ℓ`). -/
lemma acube_compact_of_nonneg {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : IsCompact (acube ℓ) :=
  (Metric.isCompact_iff_isClosed_bounded).mpr
    ⟨acube_isClosed ℓ, acube_isBounded ℓ hℓ⟩

/-- The `N`-particle centred box is compact for `0 ≤ ℓ`. -/
lemma abox_compact_of_nonneg (N : ℕ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : IsCompact (abox N ℓ) :=
  (Metric.isCompact_iff_isClosed_bounded).mpr
    ⟨abox_isClosed N ℓ, abox_isBounded N ℓ hℓ⟩

/-! ## 2. The slot-`i` fibre at a general box radius -/

/-- The slot-`i` fibre of an `(n+1)`-particle state as a one-body state in the inserted
variable: `z ↦ Φ (kcInsN n i (z,r))`. -/
def genFibre {n : ℕ} (i : Fin (n + 1)) (Φ : Submission.BoseGases.X (n + 1) → ℝ)
    (r : Submission.BoseGases.X n) : ℝ³ → ℝ :=
  fun z => Φ (Submission.BoseGases.kcInsN n i (z, r))

/-- Re-inserting a coordinate does not change the fibre. -/
lemma genFibre_eq_fibre {n : ℕ} (i : Fin (n + 1))
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (r : Submission.BoseGases.X n) (y z : ℝ³) :
    genFibre i Φ r z = Work.BoseKinLoc.fibre (n + 1) i Φ
      (Submission.BoseGases.kcInsN n i (y, r)) z := by
  rw [genFibre, Work.BoseKinLoc.fibre, Submission.BoseGases.update_kcInsN]

/-- The fibre is smooth. -/
lemma genFibre_contDiff {n : ℕ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) (r : Submission.BoseGases.X n) :
    ContDiff ℝ (⊤ : ENat) (genFibre i Φ r) := by
  have hins : ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ =>
      Submission.BoseGases.kcInsN n i (z, r)) := by
    have h1 : (fun z : ℝ³ => Submission.BoseGases.kcInsN n i (z, r))
        = Function.update (Submission.BoseGases.kcInsN n i (0, r)) i := by
      funext z
      exact Submission.BoseGases.kcInsN_update_zero i z r
    rw [h1]
    exact contDiff_update (⊤ : ENat) (Submission.BoseGases.kcInsN n i (0, r)) i
  exact hΦ.comp hins

/-- The fibre vanishes off the centred cube `acube L` when `Φ` is supported in `abox (n+1) L`. -/
lemma genFibre_eq_zero_of_not_mem_acube {n : ℕ} {L : ℝ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) L) (i : Fin (n + 1))
    {r : Submission.BoseGases.X n} {z : ℝ³} (hz : z ∉ Submission.BoseGases.acube L) :
    genFibre i Φ r z = 0 := by
  have hxabox : Submission.BoseGases.kcInsN n i (z, r)
      ∉ Submission.BoseGases.abox (n + 1) L := by
    intro hmem
    have hcoord : Submission.BoseGases.kcInsN n i (z, r) i ∉ Submission.BoseGases.acube L := by
      rwa [Submission.BoseGases.kc_insN_apply_same n i z r]
    exact hcoord (hmem i)
  show Φ (Submission.BoseGases.kcInsN n i (z, r)) = 0
  exact image_eq_zero_of_notMem_tsupport (fun h => hxabox (hsupp h))

/-- The `tsupport` of the fibre is contained in `acube L`. -/
lemma genFibre_tsupport_subset {n : ℕ} {L : ℝ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) L) (i : Fin (n + 1))
    (r : Submission.BoseGases.X n) :
    tsupport (genFibre i Φ r) ⊆ Submission.BoseGases.acube L :=
  closure_minimal (fun z hz => by
      by_contra hzc
      exact hz (genFibre_eq_zero_of_not_mem_acube hsupp i hzc))
    (Submission.BoseGases.acube_isClosed L)

/-- The fibre is compactly supported for `0 ≤ L`. -/
lemma genFibre_hasCompactSupport_of_supp {n : ℕ} {L : ℝ} (hL : 0 ≤ L)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) L) (i : Fin (n + 1))
    (r : Submission.BoseGases.X n) : HasCompactSupport (genFibre i Φ r) :=
  IsCompact.of_isClosed_subset (acube_compact_of_nonneg hL) (isClosed_tsupport _)
    (genFibre_tsupport_subset hsupp i r)

/-- The slot-`i` fibre state of `Φ`, as a function of the configuration `q = (u,r)`. -/
def genFibreState {n : ℕ} (i : Fin (n + 1)) (Φ : Submission.BoseGases.X (n + 1) → ℝ)
    (q : ℝ³ × Submission.BoseGases.X n) : ℝ³ → ℝ :=
  fun z => Φ (Submission.BoseGases.kcInsN n i (z, q.2))

/-- The slot-`i` fibre `(q,z) ↦ Φ (kcInsN i (ℓ u + z, r))` is jointly continuous. -/
lemma continuous_genFibreState_pair_shift {n : ℕ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (ℓ : ℝ) (i : Fin (n + 1)) :
    Continuous (fun p : (ℝ³ × Submission.BoseGases.X n) × ℝ³ =>
      Φ (Submission.BoseGases.kcInsN n i (ℓ • p.1.1 + p.2, p.1.2))) :=
  hΦ.continuous.comp ((continuous_kcInsN_pair i).comp
    (((continuous_fst.fst).const_smul ℓ).add continuous_snd |>.prodMk continuous_fst.snd))

/-- The fibre `(q,z) ↦ Φ (kcInsN i (z, r))` is jointly continuous. -/
lemma continuous_genFibreState_pair {n : ℕ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    Continuous (fun p : (ℝ³ × Submission.BoseGases.X n) × ℝ³ =>
      Φ (Submission.BoseGases.kcInsN n i (p.2, p.1.2))) :=
  hΦ.continuous.comp ((continuous_kcInsN_pair i).comp (continuous_snd.prodMk continuous_fst.snd))

/-- Continuity of the shifted fibre in the configuration variable. -/
lemma continuous_genFibreState_shift_fst {n : ℕ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (ℓ : ℝ) (i : Fin (n + 1)) (z : ℝ³) :
    Continuous (fun q : ℝ³ × Submission.BoseGases.X n =>
      Φ (Submission.BoseGases.kcInsN n i (ℓ • q.1 + z, q.2))) :=
  (continuous_genFibreState_pair_shift hΦ ℓ i).comp (continuous_id.prodMk continuous_const)

/-- Continuity of the shifted fibre in the space variable. -/
lemma continuous_genFibreState_shift_snd {n : ℕ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (ℓ : ℝ) (i : Fin (n + 1))
    (q : ℝ³ × Submission.BoseGases.X n) :
    Continuous (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (ℓ • q.1 + z, q.2))) :=
  (continuous_genFibreState_pair_shift hΦ ℓ i).comp (continuous_const.prodMk continuous_id)

/-- Continuity of the fibre in the space variable. -/
lemma continuous_genFibreState_snd {n : ℕ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) (q : ℝ³ × Submission.BoseGases.X n) :
    Continuous (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, q.2))) :=
  (continuous_genFibreState_pair hΦ i).comp (continuous_const.prodMk continuous_id)

/-- Continuity of the box mass of the fibre. -/
lemma continuous_setIntegral_fibre_sq {ℓ M : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hM : ∀ x : Submission.BoseGases.X (n + 1), |Φ x| ≤ M) (i : Fin (n + 1)) :
    Continuous (fun q : ℝ³ × Submission.BoseGases.X n =>
      ∫ z in Work.BoseKinLoc.lamBox ℓ q.1, (genFibreState i Φ q z) ^ 2) := by
  have hrew : (fun q : ℝ³ × Submission.BoseGases.X n =>
        ∫ z in Work.BoseKinLoc.lamBox ℓ q.1, (genFibreState i Φ q z) ^ 2)
      = fun q : ℝ³ × Submission.BoseGases.X n =>
          ∫ z in Submission.BoseGases.acube ℓ,
            (Φ (Submission.BoseGases.kcInsN n i (ℓ • q.1 + z, q.2))) ^ 2 := by
    funext q
    exact Work.BoseKinLoc.Gap.setIntegral_lamBox_eq_acube ℓ q.1 _
  rw [hrew]
  refine continuous_of_dominated (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
    (Submission.BoseGases.acube ℓ)) (bound := fun _ => M ^ 2 + 1) ?_ ?_ ?_ ?_
  · intro q
    exact ((continuous_genFibreState_shift_snd hΦ ℓ i q).pow 2).aestronglyMeasurable
  · intro q
    filter_upwards with z
    show ‖(Φ (Submission.BoseGases.kcInsN n i (ℓ • q.1 + z, q.2))) ^ 2‖ ≤ M ^ 2 + 1
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := pow_le_pow_left₀ (abs_nonneg (Φ (Submission.BoseGases.kcInsN n i (ℓ • q.1 + z, q.2))))
      (hM _) 2
    rw [sq_abs] at h
    linarith
  · exact ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ) continuousOn_const
  · filter_upwards with z
    exact (continuous_genFibreState_shift_fst hΦ ℓ i z).pow 2

/-- Continuity of the mixed box integral `∫ ψ_q g`. -/
lemma continuous_setIntegral_fibre_mul {ℓ M : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hM : ∀ x : Submission.BoseGases.X (n + 1), |Φ x| ≤ M) (i : Fin (n + 1))
    {g : ℝ³ → ℝ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgcs : HasCompactSupport g) :
    Continuous (fun q : ℝ³ × Submission.BoseGases.X n =>
      ∫ z in Work.BoseKinLoc.lamBox ℓ q.1, genFibreState i Φ q z * g z) := by
  obtain ⟨Cg, hCg⟩ := hgcs.exists_bound_of_continuous hg.continuous
  have hrew : (fun q : ℝ³ × Submission.BoseGases.X n =>
        ∫ z in Work.BoseKinLoc.lamBox ℓ q.1, genFibreState i Φ q z * g z)
      = fun q : ℝ³ × Submission.BoseGases.X n =>
          ∫ z in Submission.BoseGases.acube ℓ,
            Φ (Submission.BoseGases.kcInsN n i (ℓ • q.1 + z, q.2)) * g (ℓ • q.1 + z) := by
    funext q
    exact Work.BoseKinLoc.Gap.setIntegral_lamBox_eq_acube ℓ q.1 _
  rw [hrew]
  refine continuous_of_dominated (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
    (Submission.BoseGases.acube ℓ)) (bound := fun _ => M * Cg + 1) ?_ ?_ ?_ ?_
  · intro q
    exact (((continuous_genFibreState_shift_snd hΦ ℓ i q).mul
      (hg.continuous.comp (continuous_const.add continuous_id)))).aestronglyMeasurable
  · intro q
    filter_upwards with z
    show ‖Φ (Submission.BoseGases.kcInsN n i (ℓ • q.1 + z, q.2)) * g (ℓ • q.1 + z)‖ ≤ M * Cg + 1
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |Φ (Submission.BoseGases.kcInsN n i (ℓ • q.1 + z, q.2))| ≤ M := hM _
    have h2 : |g (ℓ • q.1 + z)| ≤ Cg := by
      simpa only [Real.norm_eq_abs] using hCg (ℓ • q.1 + z)
    nlinarith [abs_nonneg (Φ (Submission.BoseGases.kcInsN n i (ℓ • q.1 + z, q.2))),
      abs_nonneg (g (ℓ • q.1 + z))]
  · exact ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ) continuousOn_const
  · filter_upwards with z
    exact (continuous_genFibreState_shift_fst hΦ ℓ i z).mul
      (hg.continuous.comp ((continuous_fst.const_smul ℓ).add continuous_const))

/-- Continuity of the box integral of a derivative square. -/
lemma continuous_setIntegral_deriv_sq {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    (i : Fin (n + 1)) {g : ℝ³ → ℝ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgcs : HasCompactSupport g) (k : Fin 3) :
    Continuous (fun q : ℝ³ × Submission.BoseGases.X n =>
      ∫ z in Work.BoseKinLoc.lamBox ℓ q.1,
        (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
  obtain ⟨Ck, hCk⟩ := (hgcs.fderiv_apply ℝ (Submission.BoseGases.kcStdBasis k)).exists_bound_of_continuous
    ((hg.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const))
  have hrew : (fun q : ℝ³ × Submission.BoseGases.X n =>
        ∫ z in Work.BoseKinLoc.lamBox ℓ q.1,
          (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
      = fun q : ℝ³ × Submission.BoseGases.X n =>
          ∫ z in Submission.BoseGases.acube ℓ,
            (fderiv ℝ g (ℓ • q.1 + z) (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
    funext q
    exact Work.BoseKinLoc.Gap.setIntegral_lamBox_eq_acube ℓ q.1 _
  rw [hrew]
  refine continuous_of_dominated (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
    (Submission.BoseGases.acube ℓ)) (bound := fun _ => Ck ^ 2 + 1) ?_ ?_ ?_ ?_
  · intro q
    have h : Continuous (fun z : ℝ³ =>
        fderiv ℝ g (ℓ • q.1 + z) (Submission.BoseGases.kcStdBasis k)) :=
      (hg.continuous_fderiv_apply (by norm_num)).comp
        ((continuous_const.add continuous_id).prodMk continuous_const)
    exact (h.pow 2).aestronglyMeasurable
  · intro q
    filter_upwards with z
    show ‖(fderiv ℝ g (ℓ • q.1 + z) (Submission.BoseGases.kcStdBasis k)) ^ 2‖ ≤ Ck ^ 2 + 1
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := pow_le_pow_left₀ (abs_nonneg (fderiv ℝ g (ℓ • q.1 + z)
      (Submission.BoseGases.kcStdBasis k))) (by
        simpa only [Real.norm_eq_abs] using hCk (ℓ • q.1 + z)) 2
    rw [sq_abs] at h
    linarith
  · exact ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ) continuousOn_const
  · filter_upwards with z
    have h : Continuous (fun q : ℝ³ × Submission.BoseGases.X n =>
        fderiv ℝ g (ℓ • q.1 + z) (Submission.BoseGases.kcStdBasis k)) :=
      (hg.continuous_fderiv_apply (by norm_num)).comp
        (((continuous_fst.const_smul ℓ).add continuous_const).prodMk continuous_const)
    exact h.pow 2

/-- Continuity of the box integral of a square. -/
lemma continuous_setIntegral_sq {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (i : Fin (n + 1))
    {g : ℝ³ → ℝ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgcs : HasCompactSupport g) :
    Continuous (fun q : ℝ³ × Submission.BoseGases.X n =>
      ∫ z in Work.BoseKinLoc.lamBox ℓ q.1, (g z) ^ 2) := by
  obtain ⟨Cg, hCg⟩ := hgcs.exists_bound_of_continuous hg.continuous
  have hrew : (fun q : ℝ³ × Submission.BoseGases.X n =>
        ∫ z in Work.BoseKinLoc.lamBox ℓ q.1, (g z) ^ 2)
      = fun q : ℝ³ × Submission.BoseGases.X n =>
          ∫ z in Submission.BoseGases.acube ℓ, (g (ℓ • q.1 + z)) ^ 2 := by
    funext q
    exact Work.BoseKinLoc.Gap.setIntegral_lamBox_eq_acube ℓ q.1 _
  rw [hrew]
  refine continuous_of_dominated (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
    (Submission.BoseGases.acube ℓ)) (bound := fun _ => Cg ^ 2 + 1) ?_ ?_ ?_ ?_
  · intro q
    exact ((hg.continuous.comp (continuous_const.add continuous_id)).pow 2).aestronglyMeasurable
  · intro q
    filter_upwards with z
    show ‖(g (ℓ • q.1 + z)) ^ 2‖ ≤ Cg ^ 2 + 1
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := pow_le_pow_left₀ (abs_nonneg (g (ℓ • q.1 + z))) (by
      simpa only [Real.norm_eq_abs] using hCg (ℓ • q.1 + z)) 2
    rw [sq_abs] at h
    linarith
  · exact ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ) continuousOn_const
  · filter_upwards with z
    exact (hg.continuous.comp ((continuous_fst.const_smul ℓ).add continuous_const)).pow 2

/-- The trial value in the definition of `neuFrac` for the raw fibre, as a function of `q`. -/
def rawTrialVal (ℓ a2 : ℝ) {n : ℕ} (i : Fin (n + 1)) (Φ : Submission.BoseGases.X (n + 1) → ℝ)
    (q : ℝ³ × Submission.BoseGases.X n) (g : ℝ³ → ℝ) : ℝ :=
  (∫ z in Work.BoseKinLoc.lamBox ℓ q.1, (genFibreState i Φ q z) ^ 2)
    - 2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ q.1, genFibreState i Φ q z * g z)
    + a2 * ((∑ k : Fin 3, ∫ z in Work.BoseKinLoc.lamBox ℓ q.1,
          (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
        + a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ q.1, (g z) ^ 2))

/-- Continuity of the raw trial value in the configuration. -/
lemma continuous_rawTrialVal {ℓ a2 M : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hM : ∀ x : Submission.BoseGases.X (n + 1), |Φ x| ≤ M) (i : Fin (n + 1))
    {g : ℝ³ → ℝ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgcs : HasCompactSupport g) :
    Continuous (fun q : ℝ³ × Submission.BoseGases.X n => rawTrialVal ℓ a2 i Φ q g) := by
  have h1 := continuous_setIntegral_fibre_sq (ℓ := ℓ) (M := M) hℓ hΦ hM i
  have h2 := continuous_setIntegral_fibre_mul (ℓ := ℓ) (M := M) hℓ hΦ hM i hg hgcs
  have h3 : Continuous (fun q : ℝ³ × Submission.BoseGases.X n =>
      ∑ k : Fin 3, ∫ z in Work.BoseKinLoc.lamBox ℓ q.1,
        (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2) :=
    continuous_finsetSum _ (fun k _ => continuous_setIntegral_deriv_sq hℓ i hg hgcs k)
  have h4 := continuous_setIntegral_sq (ℓ := ℓ) hℓ i hg hgcs
  have hmain : Continuous (fun q : ℝ³ × Submission.BoseGases.X n =>
      (∫ z in Work.BoseKinLoc.lamBox ℓ q.1, (genFibreState i Φ q z) ^ 2)
        - 2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ q.1, genFibreState i Φ q z * g z)
        + a2 * ((∑ k : Fin 3, ∫ z in Work.BoseKinLoc.lamBox ℓ q.1,
              (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
            + a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ q.1, (g z) ^ 2))) :=
    ((h1.sub (h2.const_mul (2 * a2))).add ((h3.add (h4.const_mul a2)).const_mul a2))
  simpa only [rawTrialVal] using hmain

/-- The raw trial set is bounded below. -/
lemma bddBelow_rawTrialVal {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 ≤ a2) {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (i : Fin (n + 1)) (q : ℝ³ × Submission.BoseGases.X n) :
    BddBelow {c : ℝ | ∃ g : ℝ³ → ℝ, ContDiff ℝ (⊤ : ENat) g ∧ HasCompactSupport g ∧
      c = rawTrialVal ℓ a2 i Φ q g} := by
  have hint : MeasureTheory.Integrable
      (fun z : ℝ³ => (genFibreState i Φ q z) ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict (Work.BoseKinLoc.lamBox ℓ q.1)) :=
    ContinuousOn.integrableOn_compact (Work.BoseKinLoc.Gap.isCompact_lamBox hℓ q.1)
      ((continuous_genFibreState_snd hΦ i q).pow 2).continuousOn
  exact Work.BoseKinLoc.NeuFrac.bddBelow_trialSet_of_integrableOn ha2 q.1 hint

/-- Measurability of `q ↦ neuFrac ℓ a2 q.1 ψ_q` for the raw fibre family. -/
theorem measurable_neuFrac_genFibreState {ℓ a2 M : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 ≤ a2) {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hM : ∀ x : Submission.BoseGases.X (n + 1), |Φ x| ≤ M) (i : Fin (n + 1)) :
    Measurable (fun q : ℝ³ × Submission.BoseGases.X n =>
      Work.BoseKinLoc.neuFrac ℓ a2 q.1 (genFibreState i Φ q)) := by
  classical
  have hsInf : ∀ q : ℝ³ × Submission.BoseGases.X n,
      Work.BoseKinLoc.neuFrac ℓ a2 q.1 (genFibreState i Φ q)
        = sInf {c : ℝ | ∃ g : ℝ³ → ℝ, ContDiff ℝ (⊤ : ENat) g ∧ HasCompactSupport g ∧
            c = rawTrialVal ℓ a2 i Φ q g} := by
    intro q
    simp only [rawTrialVal, genFibreState]
    unfold Work.BoseKinLoc.neuFrac
    rfl
  have hset : ∀ b : ℝ, {q : ℝ³ × Submission.BoseGases.X n |
        b ≤ Work.BoseKinLoc.neuFrac ℓ a2 q.1 (genFibreState i Φ q)}
      = ⋂ (g : {g : ℝ³ → ℝ // ContDiff ℝ (⊤ : ENat) g ∧ HasCompactSupport g}),
          {q : ℝ³ × Submission.BoseGases.X n | b ≤ rawTrialVal ℓ a2 i Φ q g.1} := by
    intro b
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hb g
      have hmem : rawTrialVal ℓ a2 i Φ q g.1 ∈ {c : ℝ | ∃ g' : ℝ³ → ℝ,
          ContDiff ℝ (⊤ : ENat) g' ∧ HasCompactSupport g' ∧ c = rawTrialVal ℓ a2 i Φ q g'} :=
        ⟨g.1, g.2.1, g.2.2, rfl⟩
      rw [hsInf q] at hb
      exact le_trans hb (csInf_le (bddBelow_rawTrialVal hℓ ha2 hΦ i q) hmem)
    · intro hall
      rw [hsInf q]
      refine le_csInf ?_ ?_
      · exact ⟨rawTrialVal ℓ a2 i Φ q 0, 0, contDiff_const, HasCompactSupport.zero, rfl⟩
      · rintro c ⟨g', hg'1, hg'2, rfl⟩
        exact hall ⟨g', hg'1, hg'2⟩
  have hclosed : ∀ b : ℝ, IsClosed {q : ℝ³ × Submission.BoseGases.X n |
      b ≤ Work.BoseKinLoc.neuFrac ℓ a2 q.1 (genFibreState i Φ q)} := by
    intro b
    rw [hset b]
    refine isClosed_iInter (fun g => ?_)
    exact isClosed_le continuous_const
      (continuous_rawTrialVal hℓ hΦ hM i g.2.1 g.2.2)
  exact measurable_of_Ici (fun b => (hclosed b).measurableSet)

/-- The fibre is compactly supported when `Φ` is supported in `abox (n+1) L`. -/
lemma genFibreState_hasCompactSupport_of_supp {n : ℕ} {L : ℝ} (hL : 0 ≤ L)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) L) (i : Fin (n + 1))
    (q : ℝ³ × Submission.BoseGases.X n) : HasCompactSupport (genFibreState i Φ q) := by
  refine IsCompact.of_isClosed_subset (acube_compact_of_nonneg hL) isClosed_closure ?_
  refine closure_minimal (fun z hz => ?_) (Submission.BoseGases.acube_isClosed L)
  have hne : Φ (Submission.BoseGases.kcInsN n i (z, q.2)) ≠ 0 := hz
  have hmem : Submission.BoseGases.kcInsN n i (z, q.2) ∈ Submission.BoseGases.abox (n + 1) L :=
    hsupp (subset_tsupport Φ hne)
  have hcoord : (Submission.BoseGases.kcInsN n i (z, q.2)) i ∈ Submission.BoseGases.acube L :=
    hmem i
  rwa [Submission.BoseGases.kc_insN_apply_same n i z q.2] at hcoord

/-- The measurability of the mean-free box Neumann fraction along the fibre family. -/
theorem neuFrac_Qfree_fibre_aemeasurable_alt {ℓ a2 M L : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2)
    (hL : 0 ≤ L) {n : ℕ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (hM : ∀ x : Submission.BoseGases.X (n + 1), |Φ x| ≤ M)
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) L) (i : Fin (n + 1)) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ³ × Submission.BoseGases.X n =>
        Work.BoseKinLoc.neuFrac ℓ a2 q.1
          (Work.BoseKinLoc.Qfree ℓ q.1 (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, q.2)))))
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))) := by
  have hraw := (measurable_neuFrac_genFibreState (ℓ := ℓ) (a2 := a2) (M := M) hℓ ha2.le hΦ hM i)
  refine hraw.aestronglyMeasurable.congr (Filter.Eventually.of_forall (fun q => ?_))
  have hcont : Continuous (genFibreState i Φ q) := continuous_genFibreState_snd hΦ i q
  have hint : MeasureTheory.Integrable (fun z : ℝ³ => (genFibreState i Φ q z) ^ 2) :=
    Continuous.integrable_of_hasCompactSupport (hcont.pow 2)
      ((genFibreState_hasCompactSupport_of_supp hL hsupp i q).comp_left
        (g := fun t : ℝ => t ^ 2) (by norm_num))
  have hQ : Work.BoseKinLoc.Qfree ℓ q.1 (genFibreState i Φ q)
      = fun z : ℝ³ => genFibreState i Φ q z
          + (-(Work.BoseKinLoc.meanU ℓ q.1 (genFibreState i Φ q))) := by
    funext z
    simp only [Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ, Work.BoseKinLoc.meanU,
      Pi.sub_apply, sub_eq_add_neg]
  show Work.BoseKinLoc.neuFrac ℓ a2 q.1 (genFibreState i Φ q)
      = Work.BoseKinLoc.neuFrac ℓ a2 q.1 (Work.BoseKinLoc.Qfree ℓ q.1 (genFibreState i Φ q))
  rw [hQ, Work.BoseKinLoc.NeuFrac.neuFrac_add_const_of_integrableSq ha2 q.1
    (genFibreState i Φ q) (-(Work.BoseKinLoc.meanU ℓ q.1 (genFibreState i Φ q)))
    hcont.measurable hint]


/-! ## 3. The lifting -/

/-- A continuous function supported in `abox (n+1) L` is bounded by a constant. -/
lemma exists_abs_bound_of_tsupport_subset_abox {n : ℕ} {L : ℝ} (hL : 0 ≤ L)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) L) :
    ∃ M : ℝ, ∀ x : Submission.BoseGases.X (n + 1), |Φ x| ≤ M := by
  obtain ⟨C, hC⟩ := (abox_compact_of_nonneg (n + 1) hL).exists_bound_of_continuousOn
    hΦ.continuous.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ Submission.BoseGases.abox (n + 1) L
  · have h := hC x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport (fun hmem => hx (hsupp hmem)), abs_zero]
    exact le_max_right _ _

theorem fibre_lift_general {c₀ : ℝ} (hKin : Work.BoseKinLoc.KineticLocalisation c₀) {N : ℕ}
    {ℓ L d s εT b : ℝ} (hreg : Work.BoseKinLoc.KinRegime c₀ ℓ d s εT b) (hL : 0 ≤ L)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox N L)
    (hint : MeasureTheory.Integrable (fun u : ℝ³ => Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ)) :
    (∫ u : ℝ³, Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ)
      ≤ ∑ i : Fin N, ∫ x : Submission.BoseGases.X N, ∑ k : Fin 3,
          (fderiv ℝ Φ x (Submission.BoseGases.kcDir N i k)) ^ 2 := by
  rcases N with _ | n
  · -- no particles: both sides vanish
    simp [Work.BoseKinLoc.kinForm]
  have hℓ : 0 < ℓ := hreg.1
  have hd : 0 < d := hreg.2.1
  have hcsΦ : HasCompactSupport Φ :=
    IsCompact.of_isClosed_subset (abox_compact_of_nonneg (n + 1) hL) (isClosed_tsupport Φ) hsupp
  -- the absolute one-body bound, using the pointwise momentum bound
  obtain ⟨C, hC0, hCbd⟩ := Work.BoseKinLoc.Kinetic.fsT_bound_abs (ℓ := ℓ) (d := d) (s := s)
    (εT := εT) (b := b) hℓ hd (fun u ψ hψ hcs =>
      Work.BoseKinLoc.Kinetic.momForm_le_box hℓ hd u hψ hcs)
  -- the support estimate: `Λ(u)` can only meet `acube L` for `u ∈ acube ((L+ℓ)/ℓ)`
  have hKnn : 0 ≤ (L + ℓ) / ℓ := by positivity
  have hcov_sub : Work.BoseKinLoc.Compare.coverBoxU ℓ L
      ⊆ Submission.BoseGases.acube ((L + ℓ) / ℓ) := by
    intro u hu
    rw [Submission.BoseGases.mem_acube_iff]
    intro k
    have h := (Work.BoseKinLoc.Compare.mem_coverBoxU_iff hℓ hL u).mp hu k
    have h2 : -((L + ℓ) / (2 * ℓ)) ≤ u k ∧ u k ≤ (L + ℓ) / (2 * ℓ) := abs_le.mp h
    rw [Set.mem_Icc]
    constructor
    · have h3 : -((L + ℓ) / ℓ) / 2 = -((L + ℓ) / (2 * ℓ)) := by ring
      linarith [h3, h2.1]
    · have h3 : ((L + ℓ) / ℓ) / 2 = (L + ℓ) / (2 * ℓ) := by ring
      linarith [h3, h2.2]
  -- a global bound for `Φ` (used by the measurability of the `sInf`)
  obtain ⟨MΦ, hMΦ⟩ := exists_abs_bound_of_tsupport_subset_abox (n := n) (L := L) hL hΦ hsupp
  -- the per-slot estimate
  have hstep : ∀ i : Fin (n + 1),
      MeasureTheory.Integrable (fun u : ℝ³ =>
          Work.BoseKinLoc.slotForm (n + 1) (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ)
        ∧ (∫ u : ℝ³, Work.BoseKinLoc.slotForm (n + 1) (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ)
            ≤ ∫ r : Submission.BoseGases.X n, Work.BSKinetic.dSpace (genFibre i Φ r) := by
    intro i
    set F : ℝ³ → Submission.BoseGases.X n → ℝ := fun u r =>
      Work.BoseKinLoc.fsT ℓ d s εT b u (genFibre i Φ r) with hF
    -- the peel
    have hpeel : ∀ u : ℝ³, Work.BoseKinLoc.slotForm (n + 1)
        (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ = ∫ r : Submission.BoseGases.X n, F u r := by
      intro u
      rw [Work.BoseKinLoc.Kinetic.slotForm_eq_fibre_integral hℓ
        (Work.BoseKinLoc.fsT ℓ d s εT b u) u i Φ]
      rfl
    -- the majorant
    set M : Submission.BoseGases.X n → ℝ := fun r => (∫ z : ℝ³, (genFibre i Φ r z) ^ 2)
      + ∑ k : Fin 3, ∫ z : ℝ³,
          (fderiv ℝ (genFibre i Φ r) z (Submission.BoseGases.kcStdBasis k)) ^ 2 with hM
    have hAint : MeasureTheory.Integrable (fun r : Submission.BoseGases.X n =>
        ∫ z : ℝ³, (genFibre i Φ r z) ^ 2) :=
      (Work.BoseKinLoc.Kinetic.integral_fibre_sq (n := n) hΦ hcsΦ i).1.congr
        (Filter.Eventually.of_forall (fun r => rfl))
    have hDint : MeasureTheory.Integrable (fun r : Submission.BoseGases.X n =>
        Work.BSKinetic.dSpace (genFibre i Φ r)) :=
      (Work.BoseKinLoc.Kinetic.dSpace_fibre_eq (n := n) hΦ hcsΦ i).1
    have hMint : MeasureTheory.Integrable M := by
      rw [hM]
      exact hAint.add (by simpa only [Work.BSKinetic.dSpace] using hDint)
    -- joint measurability
    have hmeas : MeasureTheory.AEStronglyMeasurable (Function.uncurry F)
        ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X n))) := by
      have h1 : MeasureTheory.AEStronglyMeasurable (fun q : ℝ³ × Submission.BoseGases.X n =>
          Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) q.1
            (Work.BoseKinLoc.Qfree ℓ q.1 (genFibre i Φ q.2)))
          ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X n))) := by
        show MeasureTheory.AEStronglyMeasurable (fun q : ℝ³ × Submission.BoseGases.X n =>
            Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) q.1
              (Work.BoseKinLoc.Qfree ℓ q.1 (fun z : ℝ³ =>
                Φ (Submission.BoseGases.kcInsN n i (z, q.2)))))
            ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X n)))
        exact neuFrac_Qfree_fibre_aemeasurable_alt (ℓ := ℓ) (a2 := (d * ℓ) ^ (-2 : ℤ))
          (M := MΦ) (L := L) hℓ (by positivity) hL hΦ hMΦ hsupp i
      have h2 := Work.BoseKinLoc.Kinetic.gapBare_fibre_aemeasurable (ℓ := ℓ) hΦ i
      have h3 := Work.BoseKinLoc.Kinetic.momForm_fibre_aemeasurable (ℓ := ℓ) (d := d) hΦ i
      have h4 := Work.BoseKinLoc.Kinetic.mainWord_fibre_aemeasurable (ℓ := ℓ) (d := d)
        (s := s) (εT := εT) hΦ i
      have hsum : MeasureTheory.AEStronglyMeasurable (fun q : ℝ³ × Submission.BoseGases.X n =>
          Work.BoseKinLoc.neuWord ℓ d εT q.1 (genFibre i Φ q.2)
            + Work.BoseKinLoc.gapWord ℓ b q.1 (genFibre i Φ q.2)
            + Work.BoseKinLoc.momWord ℓ d εT b q.1 (genFibre i Φ q.2)
            + Work.BoseKinLoc.mainWord ℓ d s εT q.1 (genFibre i Φ q.2))
          ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X n))) :=
        (((h1.const_mul ((1 / 2) * εT * (d * ℓ) ^ (-2 : ℤ))).add
          (h2.const_mul (b * ℓ ^ (-2 : ℤ)))).add
          (h3.const_mul (b * εT * (d * ℓ) ^ (-2 : ℤ)))).add h4
      refine hsum.congr (Filter.Eventually.of_forall (fun q => ?_))
      exact (Work.BoseKinLoc.fsT_eq_sum ℓ d s εT b q.1 (genFibre i Φ q.2)).symm
    -- the majorant is integrable
    have hind : MeasureTheory.Integrable (fun u : ℝ³ =>
        C * (Submission.BoseGases.acube ((L + ℓ) / ℓ)).indicator (fun _ => (1 : ℝ)) u) := by
      refine MeasureTheory.Integrable.const_mul ?_ C
      rw [integrable_indicator_iff (Submission.BoseGases.acube_measurable _)]
      exact integrableOn_const (by
        rw [Submission.BoseGases.acube_volume _ hKnn]
        exact ENNReal.ofReal_lt_top.ne) (by simp)
    have hGint : MeasureTheory.Integrable (fun q : ℝ³ × Submission.BoseGases.X n =>
        (C * (Submission.BoseGases.acube ((L + ℓ) / ℓ)).indicator (fun _ => (1 : ℝ)) q.1) * M q.2)
        ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X n))) :=
      MeasureTheory.Integrable.mul_prod hind hMint
    have hFint : MeasureTheory.Integrable (Function.uncurry F)
        ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X n))) := by
      refine MeasureTheory.Integrable.mono' hGint hmeas
        (Filter.Eventually.of_forall (fun q => ?_))
      obtain ⟨u, r⟩ := q
      change ‖F u r‖ ≤
        (C * (Submission.BoseGases.acube ((L + ℓ) / ℓ)).indicator (fun _ => (1 : ℝ)) u) * M r
      by_cases hu : u ∈ Work.BoseKinLoc.Compare.coverBoxU ℓ L
      · have hb := hCbd u (genFibre i Φ r) (genFibre_contDiff hΦ i r)
          (genFibre_hasCompactSupport_of_supp hL hsupp i r)
        rw [Set.indicator_of_mem (hcov_sub hu), mul_one]
        simpa only [hF, hM, Real.norm_eq_abs] using hb
      · have hzero : F u r = 0 := by
          have hzero' := Work.BoseKinLoc.Compare.fsT_fibre_eq_zero_of_not_mem_coverBoxU
            (N := n + 1) (ℓ := ℓ) (L := L) (d := d) (s := s) (εT := εT) (b := b)
            hℓ hsupp hu (Submission.BoseGases.kcInsN n i (0, r)) i
          have hfun : genFibre i Φ r
              = Work.BoseKinLoc.fibre (n + 1) i Φ (Submission.BoseGases.kcInsN n i (0, r)) :=
            funext (fun z => genFibre_eq_fibre i Φ r 0 z)
          change Work.BoseKinLoc.fsT ℓ d s εT b u (genFibre i Φ r) = 0
          rw [hfun]
          exact hzero'
        rw [hzero, norm_zero]
        have hMnn : 0 ≤ M r := by
          rw [hM]
          refine add_nonneg (integral_nonneg (fun z => sq_nonneg _))
            (Finset.sum_nonneg (fun k _ => integral_nonneg (fun z => sq_nonneg _)))
        have hindnn : 0 ≤ (Submission.BoseGases.acube ((L + ℓ) / ℓ)).indicator
            (fun _ => (1 : ℝ)) u := Set.indicator_nonneg (fun _ _ => zero_le_one) u
        exact mul_nonneg (mul_nonneg hC0 hindnn) hMnn
    -- assemble
    have hper : ∀ᵐ r ∂(volume : Measure (Submission.BoseGases.X n)),
        MeasureTheory.Integrable (fun u : ℝ³ => F u r) :=
      ((MeasureTheory.integrable_prod_iff' hmeas).1 hFint).1
    refine ⟨hFint.integral_prod_left.congr
      (Filter.Eventually.of_forall (fun u => (hpeel u).symm)), ?_⟩
    calc (∫ u : ℝ³, Work.BoseKinLoc.slotForm (n + 1)
            (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ)
        = ∫ u : ℝ³, ∫ r : Submission.BoseGases.X n, F u r :=
          MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall (fun u => hpeel u))
      _ = ∫ r : Submission.BoseGases.X n, ∫ u : ℝ³, F u r :=
          MeasureTheory.integral_integral_swap hFint
      _ ≤ ∫ r : Submission.BoseGases.X n, Work.BSKinetic.dSpace (genFibre i Φ r) := by
          refine MeasureTheory.integral_mono_ae hFint.integral_prod_right hDint ?_
          filter_upwards [hper] with r hr
          exact hKin ℓ d s εT b hreg (genFibre i Φ r)
            (genFibre_contDiff hΦ i r) (genFibre_hasCompactSupport_of_supp hL hsupp i r) hr
  calc (∫ u : ℝ³, Work.BoseKinLoc.kinForm (n + 1) ℓ d s εT b u Φ)
      = ∑ i : Fin (n + 1), ∫ u : ℝ³,
          Work.BoseKinLoc.slotForm (n + 1) (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ := by
        simp_rw [Work.BoseKinLoc.kinForm_eq]
        exact MeasureTheory.integral_finsetSum _ (fun i _ => (hstep i).1)
    _ ≤ ∑ i : Fin (n + 1), ∫ r : Submission.BoseGases.X n,
          Work.BSKinetic.dSpace (genFibre i Φ r) :=
        Finset.sum_le_sum (fun i _ => (hstep i).2)
    _ = ∑ i : Fin (n + 1), ∫ x : Submission.BoseGases.X (n + 1), ∑ k : Fin 3,
          (fderiv ℝ Φ x (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact (Work.BoseKinLoc.Kinetic.dSpace_fibre_eq (n := n) hΦ hcsΦ i).2.symm

end Work.BoseKinLoc.Kinetic
