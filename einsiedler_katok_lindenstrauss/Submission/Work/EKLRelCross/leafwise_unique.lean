import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLComp.V_hasBasis_nhds_one
import Submission.Work.EKLProd.sl3EntryBox_compact
import Submission.Work.EKLC6Core.measurable_growthFun
import Submission.Work.EKLRelCross.bigShape_flowers
import Submission.Work.EKLRelCross.restrict_eq_of_pushforward_relation

/-!
# `Work.EKLRelCross.leafwise_unique` — uniqueness of the system of leafwise measures (U1)

Component (U1) of the frozen EKL contract `Work.EKLContract.P_Leafwise`: for a probability
measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, a horospherical subgroup `U` contracted by `α^{t₀} = aDiag t₀`
which preserves `μ`, any two systems `ν`, `ν'` of leafwise measures (`IsLeafwise`) agree `μ`-a.e.

The proof compares the two systems at a.e. point `x` using a *plaque algebra* of large *shape*
(`Work.EKLRelCross.bigShape_flowers`): for such an algebra `(Z,m)` with shape `S = shape m U x`
containing `B₁^U = Box1 U`, the `condexp` clause of `IsLeafwise` says that the conditional
expectation `condExp m (μ|_Z) f x` equals the mean of `u ↦ f (u • x)` over `S` with respect to
`ν x`.  Since this conditional expectation does not depend on the system, the pushforwards of
`ν x|_S` and `ν' x|_S` under `u ↦ u • x` are proportional; normalising on `Box1 U` (the clause
`ν x (Box1 U) = 1`) fixes the constant to `1`
(`Work.EKLRelCross.restrict_eq_of_pushforward_relation`), and hence the two systems agree on
every `V R ∩ U`, whose union is `U`.  Since both measures are carried by `U`, they are equal.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLRelCross
open Work.EKLContract

/-! ## A countable π-system generating the Borel σ-algebra of `X₃` -/

/-- The countable π-system of finite intersections of a countable topological basis of `X₃`. -/
def piSys : Set (Set X3) :=
  Set.range (fun t : Finset ↥(TopologicalSpace.countableBasis X3) =>
    ⋂ b ∈ (t : Set ↥(TopologicalSpace.countableBasis X3)), (b : Set X3))

lemma piSys_countable : piSys.Countable := Set.countable_range _

lemma piSys_isPiSystem : IsPiSystem piSys := by
  rintro s ⟨t, rfl⟩ u ⟨t', rfl⟩ -
  refine ⟨t ∪ t', ?_⟩
  ext z
  simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.coe_union, Set.mem_union]
  constructor
  · intro h
    exact ⟨fun b hb => h b (Or.inl hb), fun b hb => h b (Or.inr hb)⟩
  · rintro ⟨h1, h2⟩ b (hb | hb)
    exacts [h1 b hb, h2 b hb]

lemma measurableSet_of_mem_piSys {s : Set X3} (hs : s ∈ piSys) : MeasurableSet s := by
  obtain ⟨t, rfl⟩ := hs
  exact MeasurableSet.biInter t.countable_toSet (fun b _ =>
    (TopologicalSpace.isOpen_of_mem_countableBasis b.2).measurableSet)

lemma generateFrom_piSys : MeasurableSpace.generateFrom piSys = borel X3 := by
  refine le_antisymm ?_ ?_
  · refine MeasurableSpace.generateFrom_le ?_
    intro s hs
    exact measurableSet_of_mem_piSys hs
  · have hborel : borel X3 =
        MeasurableSpace.generateFrom (TopologicalSpace.countableBasis X3) :=
      (TopologicalSpace.isBasis_countableBasis X3).borel_eq_generateFrom
    rw [hborel]
    refine MeasurableSpace.generateFrom_le ?_
    intro b hb
    exact MeasurableSpace.measurableSet_generateFrom (show b ∈ piSys from ⟨{⟨b, hb⟩}, by simp⟩)

/-! ## The conditional-expectation relation (inlined for this π-system) -/

/-- The Bochner integral over `S` of the indicator of `C` composed with `u ↦ u • x` is the
(real) measure of `S ∩ {u | u • x ∈ C}`. -/
private lemma setIntegral_indicator_smul (ρ : Measure SL3) (S : Set SL3) (C : Set X3) (x : X3)
    (hS : MeasurableSet S) (hC : MeasurableSet C) :
    (∫ u in S, (Set.indicator C (1 : X3 → ℝ)) (u • x) ∂ρ)
      = (ρ (S ∩ (fun u : SL3 => u • x) ⁻¹' C)).toReal := by
  have hfm : Measurable (fun u : SL3 => u • x) := by measurability
  have hpre : MeasurableSet ((fun u : SL3 => u • x) ⁻¹' C) := hC.preimage hfm
  have hcongr : (fun u : SL3 => (Set.indicator C (1 : X3 → ℝ)) (u • x))
      = ((fun u : SL3 => u • x) ⁻¹' C).indicator (1 : SL3 → ℝ) := by
    funext u
    by_cases h : u • x ∈ C
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (by simpa using h)]
      rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (by simpa using h)]
  rw [hcongr]
  rw [← MeasureTheory.integral_indicator (μ := ρ)
      (f := ((fun u : SL3 => u • x) ⁻¹' C).indicator (1 : SL3 → ℝ)) hS]
  rw [Set.indicator_indicator]
  rw [MeasureTheory.integral_indicator_one (hS.inter hpre), MeasureTheory.Measure.real_def]

/-- **The pushforward relation.**  Two measures on `SL₃(ℝ)` whose `x`-orbit-averages over `S` of
the indicators of the π-system `piSys` agree (with the same weights `e`) have proportional
pushforwards of their restrictions to `S`. -/
theorem pushforward_relation_inline (x : X3) (S : Set SL3)
    (ρ ρ' : Measure SL3) [IsFiniteMeasureOnCompacts ρ] [IsFiniteMeasureOnCompacts ρ']
    (hSmeas : MeasurableSet S) (hSfin : ρ S ≠ ⊤) (hSfin' : ρ' S ≠ ⊤)
    (hSpos : ρ S ≠ 0) (hSpos' : ρ' S ≠ 0) (e : Set X3 → ℝ)
    (heq : ∀ C ∈ piSys,
        (∫ u in S, (Set.indicator C (1 : X3 → ℝ)) (u • x) ∂ρ) = (ρ S).toReal * e C ∧
        (∫ u in S, (Set.indicator C (1 : X3 → ℝ)) (u • x) ∂ρ') = (ρ' S).toReal * e C) :
    (ρ' S) • ((ρ.restrict S).map (fun g : SL3 => g • x))
      = (ρ S) • ((ρ'.restrict S).map (fun g : SL3 => g • x)) := by
  classical
  have hfm : Measurable (fun u : SL3 => u • x) := by measurability
  set μ : Measure X3 := Measure.map (fun u : SL3 => u • x) (ρ.restrict S) with hμ
  set ν : Measure X3 := Measure.map (fun u : SL3 => u • x) (ρ'.restrict S) with hν
  have hμuniv : μ univ = ρ S := by
    rw [hμ, Measure.map_apply hfm MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ]
  have hνuniv : ν univ = ρ' S := by
    rw [hν, Measure.map_apply hfm MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ]
  have key : ∀ C ∈ piSys, (ρ' S) * μ C = (ρ S) * ν C := by
    intro C hC
    have hCmeas : MeasurableSet C := measurableSet_of_mem_piSys hC
    have hpre : MeasurableSet ((fun u : SL3 => u • x) ⁻¹' C) := hCmeas.preimage hfm
    obtain ⟨heqρ, heqρ'⟩ := heq C hC
    have hμCeq : μ C = ρ ((fun u : SL3 => u • x) ⁻¹' C ∩ S) := by
      rw [hμ, Measure.map_apply hfm hCmeas, Measure.restrict_apply hpre]
    have hνCeq : ν C = ρ' ((fun u : SL3 => u • x) ⁻¹' C ∩ S) := by
      rw [hν, Measure.map_apply hfm hCmeas, Measure.restrict_apply hpre]
    have hμfin : μ C ≠ ⊤ := by
      rw [hμCeq]
      exact ne_top_of_le_ne_top hSfin (measure_mono Set.inter_subset_right)
    have hνfin : ν C ≠ ⊤ := by
      rw [hνCeq]
      exact ne_top_of_le_ne_top hSfin' (measure_mono Set.inter_subset_right)
    have hμreal : (μ C).toReal = (ρ S).toReal * e C := by
      rw [hμCeq, Set.inter_comm, ← heqρ, setIntegral_indicator_smul ρ S C x hSmeas hCmeas]
    have hνreal : (ν C).toReal = (ρ' S).toReal * e C := by
      rw [hνCeq, Set.inter_comm, ← heqρ', setIntegral_indicator_smul ρ' S C x hSmeas hCmeas]
    have hρSpos : 0 < (ρ S).toReal := ENNReal.toReal_pos hSpos hSfin
    have hρ'Spos : 0 < (ρ' S).toReal := ENNReal.toReal_pos hSpos' hSfin'
    have hμC : μ C = ENNReal.ofReal ((ρ S).toReal * e C) := by
      rw [← ENNReal.ofReal_toReal hμfin, hμreal]
    have hνC : ν C = ENNReal.ofReal ((ρ' S).toReal * e C) := by
      rw [← ENNReal.ofReal_toReal hνfin, hνreal]
    calc (ρ' S) * μ C
        = (ρ' S) * (ENNReal.ofReal ((ρ S).toReal) * ENNReal.ofReal (e C)) := by
            rw [hμC, ENNReal.ofReal_mul (le_of_lt hρSpos)]
      _ = (ρ S) * ν C := by
            rw [hνC, ENNReal.ofReal_mul (le_of_lt hρ'Spos),
              ENNReal.ofReal_toReal hSfin, ENNReal.ofReal_toReal hSfin']
            ac_rfl
  have htot : ((ρ' S) • μ) univ = ((ρ S) • ν) univ := by
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul, hμuniv, hνuniv,
      mul_comm]
  have hinst : IsFiniteMeasure ((ρ' S) • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul, hμuniv]
    exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hSfin' hSfin)⟩
  exact MeasureTheory.ext_of_generate_finite piSys generateFrom_piSys.symm piSys_isPiSystem key htot

/-! ## The glue -/

theorem leafwise_unique (h2 : Work.EKLContract.P_X3) (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3) (hL : Work.EKLContract.IsLeafwise μ U ν X') :
    ∀ (ν' : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X'' : Set Work.EKLContract.X3), Work.EKLContract.IsLeafwise μ U ν' X'' → ∀ᵐ x ∂μ, ν' x = ν x := by
  intro ν' X'' hL'
  have hcl : IsClosed (U : Set SL3) := hU.1
  have hfree := ae_free_orbit h2 μ U hU t0 ht0 hcontr
  have hfl : ∀ n : ℕ, ∃ (Z G : ℕ → Set X3) (m : ℕ → MeasurableSpace X3),
      (∀ k, IsPlaqueAlgebra U (Z k) (m k)) ∧
      (∀ k, MeasurableSet (G k) ∧ G k ⊆ Z k) ∧
      μ (⋃ k, G k)ᶜ = 0 ∧
      (∀ k, ∀ x ∈ G k, ∀ u ∈ (V ((n:ℝ)+2) ∩ (U : Set SL3)), u • x ∈ atom (m k) x) :=
    fun n => bigShape_flowers h2 μ U hU t0 ht0 hcontr ((n:ℝ)+2) (by positivity)
  choose Z G m hP using hfl
  have hPA : ∀ n k, IsPlaqueAlgebra U (Z n k) (m n k) := fun n k => (hP n).1 k
  have hGmeas : ∀ n k, MeasurableSet (G n k) := fun n k => ((hP n).2.1 k).1
  have hGsub : ∀ n k, G n k ⊆ Z n k := fun n k => ((hP n).2.1 k).2
  have hcover : ∀ n, μ (⋃ k, G n k)ᶜ = 0 := fun n => (hP n).2.2.1
  have hshape : ∀ n k x, x ∈ G n k → ∀ u ∈ (V ((n:ℝ)+2) ∩ (U : Set SL3)), u • x ∈ atom (m n k) x :=
    fun n k x hx u hu => (hP n).2.2.2 k x hx u hu
  have hZmeas : ∀ n k, MeasurableSet (Z n k) := fun n k => (hPA n k).1 (Z n k) (hPA n k).2.2.1
  set F : Finset ↥(TopologicalSpace.countableBasis X3) → X3 → ℝ := fun t => Set.indicator (⋂ b ∈ (t : Set ↥(TopologicalSpace.countableBasis X3)), (b : Set X3)) (1 : X3 → ℝ) with hF
  have hFmem : ∀ t : Finset ↥(TopologicalSpace.countableBasis X3), (⋂ b ∈ (t : Set ↥(TopologicalSpace.countableBasis X3)), (b : Set X3)) ∈ piSys :=
    fun t => ⟨t, rfl⟩
  have hFmeas : ∀ t, Measurable (F t) := fun t =>
    measurable_const.indicator (measurableSet_of_mem_piSys (hFmem t))
  have hFbdd : ∀ t, ∃ C, ∀ y, |F t y| ≤ C := by
    intro t
    refine ⟨1, fun y => ?_⟩
    by_cases hy : y ∈ (⋂ b ∈ (t : Set ↥(TopologicalSpace.countableBasis X3)), (b : Set X3))
    · have h1 : F t y = 1 := by rw [hF]; exact Set.indicator_of_mem hy (1 : X3 → ℝ)
      rw [h1]; norm_num
    · have h1 : F t y = 0 := by rw [hF]; exact Set.indicator_of_notMem hy (1 : X3 → ℝ)
      rw [h1]; norm_num
  have hEqν : ∀ n k t, ∀ᵐ x ∂(μ.restrict (Z n k)),
      condExp (m n k) (μ.restrict (Z n k)) (F t) x
        = (∫ u in shape (m n k) U x, (F t) (u • x) ∂(ν x)) / ((ν x) (shape (m n k) U x)).toReal :=
    fun n k t => hL.condexp (Z n k) (m n k) (hPA n k) (F t) (hFmeas t) (hFbdd t)
  have hEqν' : ∀ n k t, ∀ᵐ x ∂(μ.restrict (Z n k)),
      condExp (m n k) (μ.restrict (Z n k)) (F t) x
        = (∫ u in shape (m n k) U x, (F t) (u • x) ∂(ν' x)) / ((ν' x) (shape (m n k) U x)).toReal :=
    fun n k t => hL'.condexp (Z n k) (m n k) (hPA n k) (F t) (hFmeas t) (hFbdd t)
  have hEqAll : ∀ᵐ x ∂μ, ∀ (i : ℕ × ℕ × Finset ↥(TopologicalSpace.countableBasis X3)), x ∈ Z i.1 i.2.1 →
      (condExp (m i.1 i.2.1) (μ.restrict (Z i.1 i.2.1)) (F i.2.2) x
        = (∫ u in shape (m i.1 i.2.1) U x, (F i.2.2) (u • x) ∂(ν x)) / ((ν x) (shape (m i.1 i.2.1) U x)).toReal)
      ∧ (condExp (m i.1 i.2.1) (μ.restrict (Z i.1 i.2.1)) (F i.2.2) x
        = (∫ u in shape (m i.1 i.2.1) U x, (F i.2.2) (u • x) ∂(ν' x)) / ((ν' x) (shape (m i.1 i.2.1) U x)).toReal) := by
    rw [eventually_countable_forall]
    intro i
    obtain ⟨n, k, t⟩ := i
    filter_upwards [(MeasureTheory.ae_restrict_iff' (hZmeas n k)).mp (hEqν n k t),
      (MeasureTheory.ae_restrict_iff' (hZmeas n k)).mp (hEqν' n k t)] with x h1 h2
    intro hx
    exact ⟨h1 hx, h2 hx⟩
  have hCoverAll : ∀ᵐ x ∂μ, ∀ n : ℕ, x ∈ ⋃ k, G n k := by
    rw [eventually_countable_forall]
    intro n
    exact Filter.eventually_iff.mpr (MeasureTheory.mem_ae_iff.mpr (hcover n))
  have hX' : ∀ᵐ x ∂μ, x ∈ X' := Filter.eventually_iff.mpr (MeasureTheory.mem_ae_iff.mpr hL.conull)
  have hX'' : ∀ᵐ x ∂μ, x ∈ X'' := Filter.eventually_iff.mpr (MeasureTheory.mem_ae_iff.mpr hL'.conull)
  have hstep : ∀ n : ℕ, ∀ᵐ x ∂μ,
      (ν' x).restrict (V ((n:ℝ)+2) ∩ (U : Set SL3)) = (ν x).restrict (V ((n:ℝ)+2) ∩ (U : Set SL3)) := by
    intro n
    filter_upwards [hfree, hX', hX'', hCoverAll, hEqAll] with x hfreex hxX' hxX'' hcov hcond
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hcov n)
    set S : Set SL3 := shape (m n k) U x with hS
    have hxZ : x ∈ Z n k := hGsub n k hk
    have hbig : V ((n:ℝ)+2) ∩ (U : Set SL3) ⊆ S := fun u hu => ⟨hu.2, hshape n k x hk u hu⟩
    have hfreepair : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂ := by
      intro u₁ h1 u₂ h2 h
      have hmem : u₂⁻¹ * u₁ ∈ U := U.mul_mem (U.inv_mem h2) h1
      have hfix : (u₂⁻¹ * u₁) • x = x := by rw [mul_smul, h, inv_smul_smul]
      have h1' : u₂⁻¹ * u₁ = 1 := hfreex _ hmem hfix
      calc u₁ = u₂ * (u₂⁻¹ * u₁) := (mul_inv_cancel_left u₂ u₁).symm
        _ = u₂ * 1 := by rw [h1']
        _ = u₂ := mul_one u₂
    haveI hrad : IsFiniteMeasureOnCompacts (ν x) := hL.radon x hxX'
    haveI hrad' : IsFiniteMeasureOnCompacts (ν' x) := hL'.radon x hxX''
    have hSmeas : MeasurableSet S := by
      obtain ⟨O, hO, hshapeO⟩ := (hPA n k).2.2.2 x hxZ |>.2.2.1
      rw [hS, hshapeO]
      exact hO.measurableSet.inter hcl.measurableSet
    have hSU : S ⊆ (U : Set SL3) := fun u hu => hu.1
    have hBoxS : Box1 U ⊆ S := fun u hu => hbig (by
      refine ⟨fun i j => lt_of_le_of_lt (hu.2 i j) ?_, hu.1⟩
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith)
    have hSfin : (ν x) S ≠ ⊤ := by
      obtain ⟨C, hC⟩ := (hPA n k).2.2.2 x hxZ |>.2.2.2
      have hsub : S ⊆ {g : SL3 | ∀ i j, -(C+1) ≤ g i j ∧ g i j ≤ C+1} := by
        intro u hu i j
        have := hC u hu i j
        exact ⟨by linarith [neg_le_abs (u i j)], by linarith [le_abs_self (u i j)]⟩
      have hcomp : IsCompact {g : SL3 | ∀ i j, -(C+1) ≤ g i j ∧ g i j ≤ C+1} :=
        Work.EKLProd.sl3EntryBox_compact (fun _ _ => -(C+1)) (fun _ _ => C+1)
      exact ne_top_of_le_ne_top (hcomp.measure_lt_top (μ := ν x)).ne (measure_mono hsub)
    have hSfin' : (ν' x) S ≠ ⊤ := by
      obtain ⟨C, hC⟩ := (hPA n k).2.2.2 x hxZ |>.2.2.2
      have hsub : S ⊆ {g : SL3 | ∀ i j, -(C+1) ≤ g i j ∧ g i j ≤ C+1} := by
        intro u hu i j
        have := hC u hu i j
        exact ⟨by linarith [neg_le_abs (u i j)], by linarith [le_abs_self (u i j)]⟩
      have hcomp : IsCompact {g : SL3 | ∀ i j, -(C+1) ≤ g i j ∧ g i j ≤ C+1} :=
        Work.EKLProd.sl3EntryBox_compact (fun _ _ => -(C+1)) (fun _ _ => C+1)
      exact ne_top_of_le_ne_top (hcomp.measure_lt_top (μ := ν' x)).ne (measure_mono hsub)
    have hSpos : (ν x) S ≠ 0 := by
      have h1 : (1:ℝ≥0∞) ≤ (ν x) S := by
        rw [← hL.normalised x hxX']
        exact measure_mono hBoxS
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one h1)
    have hSpos' : (ν' x) S ≠ 0 := by
      have h1 : (1:ℝ≥0∞) ≤ (ν' x) S := by
        rw [← hL'.normalised x hxX'']
        exact measure_mono hBoxS
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one h1)
    have hrel : (ν' x) S • ((ν x).restrict S).map (fun g : SL3 => g • x)
        = (ν x) S • ((ν' x).restrict S).map (fun g : SL3 => g • x) := by
      refine pushforward_relation_inline x S (ν x) (ν' x) hSmeas hSfin hSfin' hSpos hSpos'
        (fun C => condExp (m n k) (μ.restrict (Z n k)) (Set.indicator C (1 : X3 → ℝ)) x) ?_
      intro C hC
      rw [piSys, Set.mem_range] at hC
      obtain ⟨t, ht⟩ := hC
      rw [← ht]
      have h := hcond (n, k, t) hxZ
      simp only [hF] at h ⊢
      have hd : ((ν x) S).toReal ≠ 0 := ne_of_gt (ENNReal.toReal_pos hSpos hSfin)
      have hd' : ((ν' x) S).toReal ≠ 0 := ne_of_gt (ENNReal.toReal_pos hSpos' hSfin')
      refine ⟨?_, ?_⟩
      · have hdd := (eq_div_iff hd).mp h.1
        rw [mul_comm]
        exact hdd.symm
      · have hdd := (eq_div_iff hd').mp h.2
        rw [mul_comm]
        exact hdd.symm
    have hres : (ν x).restrict S = (ν' x).restrict S :=
      restrict_eq_of_pushforward_relation U x S hcl (Work.EKLC6Core.isCompact_box1 hU) hSmeas hBoxS hSU
        hfreepair (ν x) (ν' x) hSfin hSfin' (hL.normalised x hxX') (hL'.normalised x hxX'') hrel
    have hAmeas : MeasurableSet (V ((n:ℝ)+2) ∩ (U : Set SL3)) :=
      (Work.EKLContract.Lemmas.V_open_one ((n:ℝ)+2) (by positivity)).1.measurableSet.inter hcl.measurableSet
    have h1 : ((ν x).restrict S).restrict (V ((n:ℝ)+2) ∩ (U : Set SL3)) = (ν x).restrict (V ((n:ℝ)+2) ∩ (U : Set SL3)) := by
      rw [Measure.restrict_restrict hAmeas]
      congr 1
      exact Set.Subset.antisymm Set.inter_subset_left (fun z hz => ⟨hz, hbig hz⟩)
    have h2 : ((ν' x).restrict S).restrict (V ((n:ℝ)+2) ∩ (U : Set SL3)) = (ν' x).restrict (V ((n:ℝ)+2) ∩ (U : Set SL3)) := by
      rw [Measure.restrict_restrict hAmeas]
      congr 1
      exact Set.Subset.antisymm Set.inter_subset_left (fun z hz => ⟨hz, hbig hz⟩)
    rw [← h1, ← h2, hres]
  have hstepall : ∀ᵐ x ∂μ, ∀ n : ℕ,
      (ν' x).restrict (V ((n:ℝ)+2) ∩ (U : Set SL3)) = (ν x).restrict (V ((n:ℝ)+2) ∩ (U : Set SL3)) := by
    rw [eventually_countable_forall]
    exact hstep
  filter_upwards [hstepall, hX', hX''] with x hstx hxX' hxX''
  refine Measure.ext (fun A hA => ?_)
  have hμU : (ν x) ((U : Set SL3)ᶜ) = 0 := hL.carried x hxX'
  have hμU' : (ν' x) ((U : Set SL3)ᶜ) = 0 := hL'.carried x hxX''
  have hEU : ∀ᵐ y ∂(ν x), y ∈ (U : Set SL3) := MeasureTheory.mem_ae_iff.mpr hμU
  have hEU' : ∀ᵐ y ∂(ν' x), y ∈ (U : Set SL3) := MeasureTheory.mem_ae_iff.mpr hμU'
  have hνr : (ν x).restrict (U : Set SL3) = ν x := MeasureTheory.Measure.restrict_eq_self_of_ae_mem hEU
  have hνr' : (ν' x).restrict (U : Set SL3) = ν' x := MeasureTheory.Measure.restrict_eq_self_of_ae_mem hEU'
  rw [← hνr', ← hνr, Measure.restrict_apply hA, Measure.restrict_apply hA]
  set B : Set SL3 := A ∩ (U : Set SL3) with hB
  have hmono : Monotone (fun n : ℕ => B ∩ V ((n:ℝ)+2)) := by
    intro a b hab g hg
    refine ⟨hg.1, fun i j => lt_of_lt_of_le (hg.2 i j) ?_⟩
    have : (a:ℝ) ≤ (b:ℝ) := Nat.cast_le.mpr hab
    linarith
  have hUn : (⋃ n : ℕ, (B ∩ V ((n:ℝ)+2))) = B := by
    refine le_antisymm (Set.iUnion_subset (fun n => Set.inter_subset_left)) ?_
    intro y hy
    obtain ⟨hyA, hyU⟩ := hy
    set M : ℝ := ∑ pq : Fin 3 × Fin 3, |y pq.1 pq.2 - (1 : Matrix (Fin 3) (Fin 3) ℝ) pq.1 pq.2| with hM
    obtain ⟨n, hn⟩ := exists_nat_gt M
    refine Set.mem_iUnion.mpr ⟨n, show y ∈ A ∩ (U : Set SL3) from ⟨hyA, hyU⟩, ?_⟩
    intro i j
    have h1 : |y i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ M := by
      rw [hM]
      exact Finset.single_le_sum (f := fun pq : Fin 3 × Fin 3 => |y pq.1 pq.2 - (1 : Matrix (Fin 3) (Fin 3) ℝ) pq.1 pq.2|) (fun pq _ => abs_nonneg _) (Finset.mem_univ (i, j))
    have h2 : M < (n:ℝ) + 2 := by linarith
    linarith
  have hfun : (fun n : ℕ => (ν' x) (B ∩ V ((n:ℝ)+2))) = fun n : ℕ => (ν x) (B ∩ V ((n:ℝ)+2)) := by
    funext n
    have h := congrArg (fun mm : Measure SL3 => mm B) (hstx n)
    rw [Measure.restrict_apply (hA.inter hcl.measurableSet)] at h
    rw [Measure.restrict_apply (hA.inter hcl.measurableSet)] at h
    have hset : B ∩ V ((n:ℝ)+2) = B ∩ (V ((n:ℝ)+2) ∩ (U : Set SL3)) := by
      rw [hB]
      ext z
      constructor
      · rintro ⟨⟨hzA, hzU⟩, hzV⟩
        exact ⟨⟨hzA, hzU⟩, hzV, hzU⟩
      · rintro ⟨h1, h2, -⟩
        exact ⟨h1, h2⟩
    rw [hset]
    exact h
  have t1 := MeasureTheory.tendsto_measure_iUnion_atTop (μ := ν' x) (s := fun n : ℕ => B ∩ V ((n:ℝ)+2)) hmono
  have t2 := MeasureTheory.tendsto_measure_iUnion_atTop (μ := ν x) (s := fun n : ℕ => B ∩ V ((n:ℝ)+2)) hmono
  have hcomp : ((ν' x) ∘ fun n : ℕ => B ∩ V ((n:ℝ)+2)) = (fun n : ℕ => (ν' x) (B ∩ V ((n:ℝ)+2))) := rfl
  rw [hcomp] at t1
  rw [hfun] at t1
  rw [hUn] at t1 t2
  exact tendsto_nhds_unique t1 t2

end Work.EKLRelCross
