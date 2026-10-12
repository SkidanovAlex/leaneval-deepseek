import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Sector.boxEnergy_le_sectorEnergy
import Submission.Work.BoseKinLoc.Sector.fibre_defs_v3
import Submission.Work.BoseKinLoc.Sector.fsT_box_invariant
import Submission.Work.BoseKinLoc.Sector.sectorEnergy_le_ratioB
import Submission.Work.BoseKinLoc.Word.boxFormB_eq_boxForm_of_supp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Sector

open Submission.BoseGases MeasureTheory

set_option autoImplicit false

/-! ## Auxiliary lemmas for `per_fibre_bound`

The target splits into two cases, according to whether the box norm of the state vanishes.

* If `sqNormB m ℓ ψ = 0`, the continuous state `ψ` vanishes on the box `abox m ℓ`
  (`perFibre_eq_zero_on_abox`), and then the box form vanishes as well
  (`perFibre_boxFormB_eq_zero`): each slot fibre of `ψ` vanishes on the moving box, so `fsT` of it
  vanishes by box locality, and the potential integrand is pointwise zero.
* If `sqNormB m ℓ ψ ≠ 0`, then `ψ` is an admissible `BoxState` of its own sector `m`, so the
  per-sector box energy is a lower bound for its Rayleigh quotient
  (`sectorEnergy_le_ratioB`), and `EΛ ≤ EΛn m` (`boxEnergy_le_sectorEnergy`); multiplying by the
  (positive) box norm gives the claim. -/

/-- The box norm square `sqNormB` is nonnegative. -/
lemma perFibre_sqNormB_nonneg {m : ℕ} {ℓ : ℝ} {ψ : Submission.BoseGases.X m → ℝ} :
    0 ≤ Work.BoseKinLoc.sqNormB m ℓ ψ := by
  rw [Work.BoseKinLoc.sqNormB]
  exact setIntegral_nonneg (Submission.BoseGases.abox_measurable m ℓ) (fun x _ => sq_nonneg _)

/-- **Scaling towards the centre lands strictly inside the box.**  If `x` lies in `abox m ℓ` and
`0 < t < 1`, then `t • x` lies in the interior of `abox m ℓ`; indeed the whole ball of radius
`(1-t)ℓ/2` around `t • x` is contained in the box, because every coordinate of `t • x` is at most
`t·ℓ/2` in absolute value. -/
lemma perFibre_interior_scale_mem {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {x : Submission.BoseGases.X m}
    (hx : x ∈ Submission.BoseGases.abox m ℓ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    t • x ∈ interior (Submission.BoseGases.abox m ℓ) := by
  refine interior_maximal ?_ Metric.isOpen_ball
    (Metric.mem_ball_self (by positivity : (0 : ℝ) < (1 - t) * ℓ / 2))
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  rw [Submission.BoseGases.mem_abox_iff]
  intro i
  rw [Submission.BoseGases.mem_acube_iff]
  intro k
  have hxk : (x i) k ∈ Set.Icc (-ℓ / 2) (ℓ / 2) :=
    (Submission.BoseGases.mem_acube_iff ℓ (x i)).mp
      ((Submission.BoseGases.mem_abox_iff m ℓ x).mp hx i) k
  have hxa : |(x i) k| ≤ ℓ / 2 := abs_le.mpr ⟨by linarith [hxk.1], hxk.2⟩
  have h1 : ‖z i - (t • x) i‖ ≤ ‖z - t • x‖ := by
    simpa using norm_le_pi_norm (z - t • x) i
  have h2 : |(z i - (t • x) i).ofLp k| ≤ ‖z i - (t • x) i‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (z i - (t • x) i) k
  have h2' : (z i - (t • x) i).ofLp k = (z i) k - t * (x i) k := by
    simp [Pi.smul_apply]
  have h4 : |(z i - (t • x) i).ofLp k| < (1 - t) * ℓ / 2 :=
    lt_of_le_of_lt (le_trans h2 h1) hz
  have h5 : t * |(x i) k| ≤ t * (ℓ / 2) :=
    mul_le_mul_of_nonneg_left hxa (le_of_lt ht0)
  have h3 : |(z i) k| ≤ |(z i - (t • x) i).ofLp k| + t * |(x i) k| := by
    have heq : (z i) k = (z i - (t • x) i).ofLp k + t * (x i) k := by
      rw [h2']; ring
    rw [heq]
    calc |(z i - (t • x) i).ofLp k + t * (x i) k|
        ≤ |(z i - (t • x) i).ofLp k| + |t * (x i) k| := abs_add_le _ _
      _ = |(z i - (t • x) i).ofLp k| + t * |(x i) k| := by
          rw [abs_mul, abs_of_pos ht0]
  have hlt : |(z i) k| < ℓ / 2 := by nlinarith [h3, h4, h5]
  have hle : |(z i) k| ≤ ℓ / 2 := le_of_lt hlt
  exact ⟨by linarith [(abs_le.mp hle).1], by linarith [(abs_le.mp hle).2]⟩

/-- **A state of vanishing box norm vanishes on the box.**  A continuous state whose box norm
square `sqNormB m ℓ ψ = ∫_{abox m ℓ} ψ²` vanishes is zero at every point of the box: `ψ² ≥ 0` is
continuous, hence vanishes almost everywhere on the box, so `ψ` vanishes on the (open) interior of
the box, and by continuity on the closure of that interior, which is the whole box (every point of
the box is the limit of points obtained by scaling it towards the centre). -/
lemma perFibre_eq_zero_on_abox {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {ψ : Submission.BoseGases.X m → ℝ} (hψ : Continuous ψ)
    (h0 : Work.BoseKinLoc.sqNormB m ℓ ψ = 0) :
    ∀ x ∈ Submission.BoseGases.abox m ℓ, ψ x = 0 := by
  have hInt : IntegrableOn (fun x : Submission.BoseGases.X m => (ψ x) ^ 2)
      (Submission.BoseGases.abox m ℓ) volume :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact m hℓ)
      (hψ.pow 2).continuousOn
  have hae : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox m ℓ)), ψ x ^ 2 = 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae (f := fun x : Submission.BoseGases.X m => ψ x ^ 2)
      (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hInt).mp h0
  have hae' : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox m ℓ)), ψ x = 0 :=
    hae.mono (fun x hx => pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx)
  have hms : MeasurableSet {x : Submission.BoseGases.X m | ψ x ≠ 0} :=
    (isOpen_compl_singleton.preimage hψ).measurableSet
  have hmeas : volume ({x : Submission.BoseGases.X m | ψ x ≠ 0} ∩
      Submission.BoseGases.abox m ℓ) = 0 := by
    have h := ae_iff.mp hae'
    rwa [Measure.restrict_apply hms] at h
  have hUopen : IsOpen ({x : Submission.BoseGases.X m | ψ x ≠ 0} ∩
      interior (Submission.BoseGases.abox m ℓ)) :=
    (isOpen_compl_singleton.preimage hψ).inter isOpen_interior
  have hUmeas : volume ({x : Submission.BoseGases.X m | ψ x ≠ 0} ∩
      interior (Submission.BoseGases.abox m ℓ)) = 0 :=
    measure_mono_null (Set.inter_subset_inter (subset_refl _) interior_subset) hmeas
  have hUempty : ({x : Submission.BoseGases.X m | ψ x ≠ 0} ∩
      interior (Submission.BoseGases.abox m ℓ)) = ∅ :=
    hUopen.eq_empty_of_measure_zero hUmeas
  have hint : ∀ x ∈ interior (Submission.BoseGases.abox m ℓ), ψ x = 0 := by
    intro x hx
    by_contra hne
    have hmem : x ∈ ({x : Submission.BoseGases.X m | ψ x ≠ 0} ∩
        interior (Submission.BoseGases.abox m ℓ)) := ⟨hne, hx⟩
    rw [hUempty] at hmem
    exact hmem
  have hclosed : IsClosed {x : Submission.BoseGases.X m | ψ x = 0} :=
    isClosed_eq hψ continuous_const
  have hcl : closure (interior (Submission.BoseGases.abox m ℓ)) ⊆
      {x : Submission.BoseGases.X m | ψ x = 0} :=
    closure_minimal (fun x hx => hint x hx) hclosed
  intro x hx
  refine hcl (Metric.mem_closure_iff.mpr (fun ε hε => ?_))
  set δ : ℝ := min (1 / 2) (ε / (2 * (‖x‖ + 1))) with hδdef
  have hδpos : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδle1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδle2 : δ ≤ ε / (2 * (‖x‖ + 1)) := min_le_right _ _
  have hδlt1 : δ < 1 := lt_of_le_of_lt hδle1 (by norm_num)
  refine ⟨(1 - δ) • x, perFibre_interior_scale_mem hℓ hx (by linarith) (by linarith), ?_⟩
  rw [dist_eq_norm]
  have hsub : x - (1 - δ) • x = δ • x := by
    have h := sub_smul (1 : ℝ) (1 - δ) x
    rw [one_smul, show (1 : ℝ) - (1 - δ) = δ by ring] at h
    exact h.symm
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
  have hxnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have h2 : δ * ‖x‖ ≤ (ε / (2 * (‖x‖ + 1))) * ‖x‖ :=
    mul_le_mul_of_nonneg_right hδle2 hxnn
  have h3 : (ε / (2 * (‖x‖ + 1))) * ‖x‖ < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (‖x‖ + 1))]
    nlinarith [hxnn, hε]
  linarith

/-- **The box form of a state vanishing on the box vanishes.**  If `ψ` is zero at every point of
`abox m ℓ`, then `boxFormB m … ψ = 0`: the potential integrand `ψ²·potWordU` is pointwise zero on
the box, and so is each slot-`i` kinetic integrand `indU ℓ 0 (xᵢ)·fsT … 0 (fibre m i ψ x)`, because
for `x` in the box the fibre `z ↦ ψ (x with xᵢ = z)` vanishes on the moving box `lamBox ℓ 0`
(updating a box slot keeps the configuration in the box), whence `fsT` of it equals `fsT` of the
zero function, which is `0` by box locality. -/
lemma perFibre_boxFormB_eq_zero {m : ℕ} {v g : EuclideanSpace ℝ (Fin 3) → ℝ}
    {ℓ μ d s εT b : ℝ} (hℓ : 0 < ℓ) {ψ : Submission.BoseGases.X m → ℝ}
    (h0 : ∀ x ∈ Submission.BoseGases.abox m ℓ, ψ x = 0) :
    Work.BoseKinLoc.boxFormB m v g ℓ μ d s εT b ψ = 0 := by
  have hkin : ∀ i : Fin m, (∫ x in Submission.BoseGases.abox m ℓ,
      Work.BoseKinLoc.indU ℓ 0 (x i)
        * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre m i ψ x)) = 0 := by
    intro i
    rw [MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable m ℓ)
      (fun x hx => ?_), integral_zero]
    have hfib : ∀ z ∈ Work.BoseKinLoc.lamBox ℓ 0,
        Work.BoseKinLoc.fibre m i ψ x z = (0 : EuclideanSpace ℝ (Fin 3) → ℝ) z := by
      intro z hz
      have hz' : z ∈ Submission.BoseGases.acube ℓ := by
        simpa [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox] using hz
      have hupd : Function.update x i z ∈ Submission.BoseGases.abox m ℓ := by
        rw [Submission.BoseGases.mem_abox_iff]
        intro j
        rw [Function.update_apply]
        by_cases hji : j = i
        · rw [if_pos hji]; exact hz'
        · rw [if_neg hji]
          exact (Submission.BoseGases.mem_abox_iff m ℓ x).mp hx j
      change ψ (Function.update x i z) = 0
      exact h0 _ hupd
    rw [fsT_box_invariant hℓ hfib, Work.BoseKinLoc.Word.fsT_zero hℓ, mul_zero]
  have hsum : (∑ i : Fin m, ∫ x in Submission.BoseGases.abox m ℓ,
      Work.BoseKinLoc.indU ℓ 0 (x i)
        * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre m i ψ x)) = 0 := by
    rw [Finset.sum_congr rfl (fun i _ => hkin i)]
    simp
  have hpot : (∫ x in Submission.BoseGases.abox m ℓ,
      (ψ x) ^ 2 * Work.BoseKinLoc.potWordU m v g ℓ μ 0 x) = 0 := by
    have hz : ∀ x ∈ Submission.BoseGases.abox m ℓ,
        (ψ x) ^ 2 * Work.BoseKinLoc.potWordU m v g ℓ μ 0 x = (0 : ℝ) := by
      intro x hx
      rw [h0 x hx]
      ring
    rw [MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable m ℓ) hz]
    simp
  unfold Work.BoseKinLoc.boxFormB Work.BoseKinLoc.kinFormB
  rw [hsum, hpot, mul_zero, add_zero]

/-- **The per-fibre bound.**  With the two bounded-below hypotheses of the box energy (the per-sector family `{EΛn m}` bounded below, and the box Rayleigh quotient family over the relaxed class `BoxState m ℓ` bounded below for every `m`), *every* smooth symmetric `m`-particle state `ψ` satisfies `min 0 EΛ · sqNormB m ℓ ψ ≤ boxFormB m … ψ`: the box-restricted form dominates `min 0 EΛ` times the box norm.  No support condition and no nonvanishing hypothesis is imposed.  For `sqNormB m ℓ ψ = 0` one has `boxFormB m … ψ = 0` (the state vanishes on the box, so each slot fibre of it vanishes on the box, whence `fsT` of it vanishes by box-locality `fsT_box_invariant` and the potential integrand vanishes on the box).  For `sqNormB m ℓ ψ > 0` the state is a `BoxState`, `EΛn m` is the infimum (`ciInf_le` with `hEi m`) and `EΛ ≤ EΛn m` (`boxEnergy_le_sectorEnergy` with `hEo`). -/
theorem per_fibre_bound {m : ℕ} {v g : ℝ³ → ℝ} {ℓ μ d s εT b : ℝ} (hℓ : 0 < ℓ)
    (hEo : BddBelow (Set.range (fun m : ℕ => Work.BoseKinLoc.EΛn m v g ℓ μ d s εT b)))
    (hEi : ∀ m : ℕ, BddBelow (Set.range (fun Φ : Work.BoseKinLoc.BoxState m ℓ =>
      Work.BoseKinLoc.boxFormB m v g ℓ μ d s εT b Φ / Work.BoseKinLoc.sqNormB m ℓ Φ)))
    {ψ : Submission.BoseGases.X m → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hsym : Submission.BoseGases.PermInvariant m ψ) :
    min 0 (Work.BoseKinLoc.EΛ v g ℓ μ d s εT b) * Work.BoseKinLoc.sqNormB m ℓ ψ
      ≤ Work.BoseKinLoc.boxFormB m v g ℓ μ d s εT b ψ := by
  by_cases h0 : Work.BoseKinLoc.sqNormB m ℓ ψ = 0
  · have hzero : ∀ x ∈ Submission.BoseGases.abox m ℓ, ψ x = 0 :=
      perFibre_eq_zero_on_abox hℓ hψ.continuous h0
    have hbox : Work.BoseKinLoc.boxFormB m v g ℓ μ d s εT b ψ = 0 :=
      perFibre_boxFormB_eq_zero hℓ hzero
    simp [h0, hbox]
  · have hpos : 0 < Work.BoseKinLoc.sqNormB m ℓ ψ :=
      lt_of_le_of_ne perFibre_sqNormB_nonneg (Ne.symm h0)
    have hne : ψ ≠ 0 := by
      intro h
      rw [h] at hpos
      simp [Work.BoseKinLoc.sqNormB] at hpos
    let Φ : Work.BoseKinLoc.BoxState m ℓ :=
      { toFun := ψ, contDiff := hψ, symm := hsym, nezero := hne }
    have hratio : Work.BoseKinLoc.EΛn m v g ℓ μ d s εT b
        ≤ Work.BoseKinLoc.boxFormB m v g ℓ μ d s εT b ψ / Work.BoseKinLoc.sqNormB m ℓ ψ :=
      sectorEnergy_le_ratioB (hEi m) Φ
    have hEΛn : Work.BoseKinLoc.EΛ v g ℓ μ d s εT b
        ≤ Work.BoseKinLoc.EΛn m v g ℓ μ d s εT b :=
      boxEnergy_le_sectorEnergy (m := m) hEo
    have hmin : min 0 (Work.BoseKinLoc.EΛ v g ℓ μ d s εT b)
        ≤ Work.BoseKinLoc.EΛn m v g ℓ μ d s εT b :=
      le_trans (min_le_right _ _) hEΛn
    calc min 0 (Work.BoseKinLoc.EΛ v g ℓ μ d s εT b) * Work.BoseKinLoc.sqNormB m ℓ ψ
        ≤ Work.BoseKinLoc.EΛn m v g ℓ μ d s εT b * Work.BoseKinLoc.sqNormB m ℓ ψ :=
          mul_le_mul_of_nonneg_right hmin (le_of_lt hpos)
      _ ≤ (Work.BoseKinLoc.boxFormB m v g ℓ μ d s εT b ψ / Work.BoseKinLoc.sqNormB m ℓ ψ)
            * Work.BoseKinLoc.sqNormB m ℓ ψ :=
          mul_le_mul_of_nonneg_right hratio (le_of_lt hpos)
      _ = Work.BoseKinLoc.boxFormB m v g ℓ μ d s εT b ψ :=
          div_mul_cancel₀ _ (ne_of_gt hpos)

end Work.BoseKinLoc.Sector
