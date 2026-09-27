import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLC6Core.box_facts
import Submission.Work.EKLC6Core.conjBox_nhds
import Submission.Work.EKLC6Core.conjBox_measurable
import Submission.Work.EKLC6Core.dirac_of_mass
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLRelCross.atomic_defs
import Submission.Work.EKLRelCross.subseq_of_frequently_mem_nhds
import Submission.Work.EKLRelCross.atomic_conc
import Submission.Work.EKLRelCross.conjBox_mass_tendsto
import Submission.Work.EKLContract.Lemmas.V_open_one
import Submission.Work.EKLProd.aDiag_nsmul

/-!
# `Work.EKLRelCross.atomic_trivial_of_covariant`

The atomic case of the ergodic dichotomy for a leafwise-measure system (EKL p. 13, Pisa 7.12):
if `ν x {1} > 0`, then `ν x = δ₁` a.e.

The argument: `hErg.1 (-t0)` makes the backward diagonal map `Ψ`-conjugation `relPsi t0 n`
measure preserving, and by the `A`-covariance `ν ((aDiag t₀ⁿ)⁻¹ • x) = cₙ · (ν x).map (relPsi t0 n)`
with `cₙ = (ν x (conjBox U (n t₀)))⁻¹`.  Along the orbit these leafwise measures converge vaguely
to `δ₁` (because `relPsi t0 n` expands `U` while `ν x (conjBox U (n t₀)) → ν x {1}`), and by
Poincaré recurrence (for the backward map) plus Luzin continuity of `x ↦ ∫ f dν x` along a
compact set, a subsequence of the orbit returns to `x`; hence `∫ f dν x = f 1` and `ν x = δ₁`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-- Iterating the backward diagonal map. -/
lemma relT_iter_aDiag (t0 : Fin 3 → ℝ) (n : ℕ) (x : X3) :
    (fun y : X3 => aDiag (-t0) • y)^[n] x = aDiag (-(((n:ℝ)) • t0)) • x := by
  rw [smul_iterate, ← Work.EKLC6Core.aDiag_real_nsmul, smul_neg]

/-- **The `A`-covariance, rearranged.**  `(ν x).map (relPsi t0 n)` is the leafwise measure at
`aDiag (-(n t₀)) • x`, rescaled by the normalising mass `ν x (conjBox U (n t₀))`. -/
theorem map_relPsi_eq_smul {μ : Measure X3} [IsProbabilityMeasure μ] {U : Subgroup SL3}
    (hU : IsHoro U) {ν : X3 → Measure SL3} {X' X'' : Set X3}
    (hL : IsLeafwise μ U ν X') (hcov : Work.EKLC6Core.ACovariant ν X'') (t0 : Fin 3 → ℝ) (n : ℕ)
    {x : X3} (hx : x ∈ X' ∩ X'') (hx' : aDiag (-(((n:ℝ)) • t0)) • x ∈ X' ∩ X'') :
    (ν x).map (relPsi t0 n)
      = ν x (Work.EKLC6Core.conjBox U (((n:ℝ)) • t0)) • ν (aDiag (-(((n:ℝ)) • t0)) • x) := by
  obtain ⟨c, hc0, hct, hce⟩ := hcov (-(((n:ℝ)) • t0)) x hx.2 hx'.2
  have hfun : (fun g => aDiag (-(((n:ℝ)) • t0)) * g * (aDiag (-(((n:ℝ)) • t0)))⁻¹)
      = relPsi t0 n := funext (fun g => (relPsi_eq_aDiag t0 n g).symm)
  rw [hfun] at hce
  have hnorm : ν (aDiag (-(((n:ℝ)) • t0)) • x) (Box1 U) = 1 := hL.normalised _ hx'.1
  have hq : ν x (Work.EKLC6Core.conjBox U (((n:ℝ)) • t0))
      = ((ν x).map (relPsi t0 n)) (Box1 U) := by
    rw [Measure.map_apply (measurable_relPsi t0 n) (Work.EKLC6Core.measurableSet_box1 hU),
      relPsi_preimage_box1]
  have h1 : (1 : ℝ≥0∞) = c * ν x (Work.EKLC6Core.conjBox U (((n:ℝ)) • t0)) := by
    have h := congrArg (fun ρ : Measure SL3 => ρ (Box1 U)) hce
    rw [hnorm, Measure.smul_apply, ← hq, smul_eq_mul] at h
    exact h
  calc (ν x).map (relPsi t0 n)
      = (c * ν x (Work.EKLC6Core.conjBox U (((n:ℝ)) • t0))) • (ν x).map (relPsi t0 n) := by
        rw [← h1, one_smul]
    _ = (ν x (Work.EKLC6Core.conjBox U (((n:ℝ)) • t0)) * c) • (ν x).map (relPsi t0 n) := by
        rw [mul_comm]
    _ = ν x (Work.EKLC6Core.conjBox U (((n:ℝ)) • t0)) • (c • (ν x).map (relPsi t0 n)) := by
        rw [smul_smul]
    _ = ν x (Work.EKLC6Core.conjBox U (((n:ℝ)) • t0)) • ν (aDiag (-(((n:ℝ)) • t0)) • x) := by
        rw [← hce]

theorem atomic_trivial_of_covariant (h2 : Work.EKLContract.P_X3)
    (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' X'' : Set Work.EKLContract.X3)
    (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ X''ᶜ = 0)
    (hLuzin : ∀ ε : ENNReal, 0 < ε → ∃ K : Set Work.EKLContract.X3, IsCompact K ∧ K ⊆ X' ∧ μ Kᶜ < ε ∧
        ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
          ContinuousOn (fun x => ∫ g, f g ∂(ν x)) K)
    (hErg : Work.EKLContract.IsAErgodic μ) :
    ∀ᵐ x ∂μ, ν x {1} > 0 → ν x = MeasureTheory.Measure.dirac 1 := by
  classical
  haveI : T2Space X3 := h2.1
  haveI : PolishSpace X3 := h2.2.1
  haveI : SecondCountableTopology X3 := by haveI := h2.2.1; infer_instance
  haveI : FirstCountableTopology X3 := by infer_instance
  have hBox1 : MeasurableSet (Box1 U) := Work.EKLC6Core.measurableSet_box1 hU
  have hTmp : MeasurePreserving (fun y : X3 => aDiag (-t0) • y) μ μ := hErg.1 (-t0)
  have hKex : ∀ m : ℕ, ∃ K : Set X3, IsCompact K ∧ K ⊆ X' ∧
      μ Kᶜ < ENNReal.ofReal (((m:ℝ)+1)⁻¹) ∧
      ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
        ContinuousOn (fun y => ∫ g, f g ∂(ν y)) K :=
    fun m => hLuzin _ (ENNReal.ofReal_pos.mpr (by positivity))
  choose K hK using hKex
  obtain ⟨basis, hbas⟩ := TopologicalSpace.exists_seq_basis X3
  have hgood : ∀ᵐ x ∂μ, ∀ (m j : ℕ), x ∈ K m ∩ basis j →
      ∃ᶠ n in atTop, (fun y : X3 => aDiag (-t0) • y)^[n] x ∈ K m ∩ basis j := by
    refine eventually_countable_forall.mpr (fun m => ?_)
    refine eventually_countable_forall.mpr (fun j => ?_)
    exact hTmp.conservative.ae_mem_imp_frequently_image_mem
      (((hK m).1.isClosed.measurableSet.inter (hbas.isOpen (Set.mem_range_self j)).measurableSet).nullMeasurableSet)
  have hKconull : μ ((⋃ m : ℕ, K m)ᶜ) = 0 := by
    have hle : ∀ M : ℕ, μ ((⋃ m : ℕ, K m)ᶜ) ≤ ENNReal.ofReal (((M:ℝ)+1)⁻¹) := by
      intro M
      refine le_trans (measure_mono ?_) (le_of_lt ((hK M).2.2.1))
      intro y hy
      simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hy ⊢
      exact hy M
    have htop : μ ((⋃ m : ℕ, K m)ᶜ) < ⊤ := lt_of_le_of_lt (hle 0) (by norm_num)
    by_contra hne
    have hpos : 0 < (μ ((⋃ m : ℕ, K m)ᶜ)).toReal := ENNReal.toReal_pos hne (ne_of_lt htop)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hpos
    have hle' : (μ ((⋃ m : ℕ, K m)ᶜ)).toReal ≤ ((N:ℝ)+1)⁻¹ := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hle N)
      rwa [ENNReal.toReal_ofReal (by positivity)] at h
    rw [one_div] at hN
    linarith
  have hX'ae : ∀ᵐ y ∂μ, y ∈ X' := by
    rw [MeasureTheory.ae_iff, show {y : X3 | ¬ y ∈ X'} = X'ᶜ from by ext y; simp]
    exact hL.conull
  have hX''ae : ∀ᵐ y ∂μ, y ∈ X'' := by
    rw [MeasureTheory.ae_iff, show {y : X3 | ¬ y ∈ X''} = X''ᶜ from by ext y; simp]
    exact hX''
  have hback : ∀ᵐ y ∂μ, ∀ n : ℕ,
      (fun z : X3 => aDiag (-t0) • z)^[n] y ∈ X' ∩ X'' := by
    rw [eventually_countable_forall]
    intro n
    exact ((((hTmp.iterate n).quasiMeasurePreserving).ae hX'ae)).and
      (((hTmp.iterate n).quasiMeasurePreserving).ae hX''ae)
  have hKae : ∀ᵐ y ∂μ, ∃ m : ℕ, y ∈ K m := by
    rw [MeasureTheory.ae_iff, show {y : X3 | ¬ ∃ m : ℕ, y ∈ K m} = (⋃ m : ℕ, K m)ᶜ from by
      ext y; simp]
    exact hKconull
  filter_upwards [hgood, hback, hX'ae, hX''ae, hKae] with x hgoodx hbackx hxX' hxX'' hxUK
  intro hp
  obtain ⟨m, hxm⟩ := hxUK
  set P : ℝ := (ν x {1}).toReal with hP
  have hone_box : (1 : SL3) ∈ Box1 U := ⟨one_mem U, fun i j => by simp⟩
  have hbox1m : ν x {1} ≤ ν x (Box1 U) :=
    measure_mono (Set.singleton_subset_iff.mpr hone_box)
  have hPpos : 0 < P := by
    rw [hP]
    exact ENNReal.toReal_pos (ne_of_gt hp)
      (ne_of_lt (lt_of_le_of_lt hbox1m (by rw [hL.normalised x hxX']; exact ENNReal.one_lt_top)))
  have hA : ∀ (f : CompactlySupportedContinuousMap SL3 ℝ),
      Tendsto (fun n : ℕ => ∫ g, f g ∂(ν ((fun z : X3 => aDiag (-t0) • z)^[n] x))) atTop
        (nhds (f 1)) := by
    intro f
    have hB := integral_relPsi_tendsto' hU t0 hcontr (hL.carried x hxX') (hL.radon x hxX') f
    have hq := conjBox_mass_tendsto hL hU t0 hcontr hxX'
    have hBA : ∀ n : ℕ,
        (∫ g, f g ∂(ν ((fun z : X3 => aDiag (-t0) • z)^[n] x)))
          = (ν x (Work.EKLC6Core.conjBox U (((n:ℝ)) • t0))).toReal⁻¹
            * (∫ g, f (relPsi t0 n g) ∂(ν x)) := by
      intro n
      have hxn : aDiag (-(((n:ℝ)) • t0)) • x ∈ X' ∩ X'' := by
        rw [← relT_iter_aDiag t0 n x]; exact hbackx n
      have hmap := map_relPsi_eq_smul hU hL hcov t0 n ⟨hxX', hxX''⟩ hxn
      have hmi : ∫ g, f g ∂((ν x).map (relPsi t0 n)) = ∫ g, f (relPsi t0 n g) ∂(ν x) :=
        MeasureTheory.integral_map (μ := ν x) (φ := relPsi t0 n) (f := fun g => f g)
          (measurable_relPsi t0 n).aemeasurable f.continuous.aestronglyMeasurable
      have hInt : (∫ g, f (relPsi t0 n g) ∂(ν x))
          = (ν x (Work.EKLC6Core.conjBox U (((n:ℝ)) • t0))).toReal
              * (∫ g, f g ∂(ν ((fun z : X3 => aDiag (-t0) • z)^[n] x))) := by
        rw [← hmi, hmap, MeasureTheory.integral_smul_measure, smul_eq_mul,
          ← relT_iter_aDiag t0 n x]
      have hqne : (ν x (Work.EKLC6Core.conjBox U (((n:ℝ)) • t0))).toReal ≠ 0 := by
        have hmem : (1 : SL3) ∈ Work.EKLC6Core.conjBox U (((n:ℝ)) • t0) :=
          ⟨1, ⟨one_mem U, fun i j => by simp⟩, by simp⟩
        have hle : ν x {1} ≤ ν x (Work.EKLC6Core.conjBox U (((n:ℝ)) • t0)) :=
          measure_mono (Set.singleton_subset_iff.mpr hmem)
        have hsub : Work.EKLC6Core.conjBox U (((n:ℝ)) • t0) ⊆ Box1 U := by
          simpa using (conjBox_antitone hU hcontr (Nat.zero_le n))
        have hfin : ν x (Work.EKLC6Core.conjBox U (((n:ℝ)) • t0)) ≠ ⊤ :=
          ne_of_lt (lt_of_le_of_lt (measure_mono hsub)
            (by rw [hL.normalised x hxX']; exact ENNReal.one_lt_top))
        have : P ≤ (ν x (Work.EKLC6Core.conjBox U (((n:ℝ)) • t0))).toReal := by
          rw [hP]; exact ENNReal.toReal_mono hfin hle
        exact ne_of_gt (lt_of_lt_of_le hPpos this)
      rw [hInt]
      rw [← mul_assoc, inv_mul_cancel₀ hqne, one_mul]
    have hlim1 : Tendsto (fun n : ℕ => (ν x (Work.EKLC6Core.conjBox U (((n:ℝ)) • t0))).toReal⁻¹)
        atTop (nhds P⁻¹) := hq.inv₀ (ne_of_gt hPpos)
    have hlim2 : Tendsto (fun n : ℕ => ∫ g, f (relPsi t0 n g) ∂(ν x)) atTop (nhds (f 1 * P)) := by
      rw [hP]; exact hB
    have hprod := hlim1.mul hlim2
    have hfinal : P⁻¹ * (f 1 * P) = f 1 := by
      rw [mul_comm (f 1) P, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hPpos), one_mul]
    rw [hfinal] at hprod
    refine hprod.congr' ?_
    filter_upwards with n
    exact (hBA n).symm
  have hmain : ∀ (f : CompactlySupportedContinuousMap SL3 ℝ), ∫ g, f g ∂(ν x) = f 1 := by
    intro f
    have hfreq : ∀ s ∈ nhds x, ∃ᶠ n in atTop,
        (fun z : X3 => aDiag (-t0) • z)^[n] x ∈ K m ∩ s := by
      intro s hs
      obtain ⟨t, ht, hxt, hts⟩ := hbas.mem_nhds_iff.mp hs
      obtain ⟨j, rfl⟩ := ht
      exact (hgoodx m j ⟨hxm, hxt⟩).mono (fun n hn => ⟨hn.1, hts hn.2⟩)
    obtain ⟨φ, hφmono, hφmem, hφtend⟩ := subseq_of_frequently_mem_nhds
      (fun n : ℕ => (fun z : X3 => aDiag (-t0) • z)^[n] x) x (K m) hfreq
    have hcont : Tendsto (fun k : ℕ => ∫ g, f g ∂(ν ((fun z : X3 => aDiag (-t0) • z)^[φ k] x)))
        atTop (nhds (∫ g, f g ∂(ν x))) := by
      have hcontOn := (hK m).2.2.2 f
      have hv : Tendsto (fun k : ℕ => (fun z : X3 => aDiag (-t0) • z)^[φ k] x) atTop
          (nhdsWithin x (K m)) :=
        tendsto_nhdsWithin_iff.mpr ⟨hφtend, Filter.Eventually.of_forall hφmem⟩
      exact Filter.Tendsto.comp (hcontOn x hxm) hv
    have hsub : Tendsto (fun k : ℕ => ∫ g, f g ∂(ν ((fun z : X3 => aDiag (-t0) • z)^[φ k] x)))
        atTop (nhds (f 1)) := (hA f).comp hφmono.tendsto_atTop
    exact tendsto_nhds_unique hcont hsub
  haveI : IsFiniteMeasureOnCompacts (ν x) := hL.radon x hxX'
  haveI : IsLocallyFiniteMeasure (ν x) := inferInstance
  haveI : (ν x).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (ν x)
  haveI : IsLocallyFiniteMeasure (Measure.dirac (1 : SL3)) := inferInstance
  haveI : (Measure.dirac (1 : SL3)).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  refine Measure.ext_of_integral_eq_on_compactlySupported (fun f => ?_)
  rw [MeasureTheory.integral_dirac]
  exact hmain f

end Work.EKLRelCross

end
