import Mathlib
import Submission.Work.EKLRelCross.bigShape_flowers
import Submission.Work.EKLRelCross.leafwise_unique
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces

open MeasureTheory Filter Topology Set
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **Uniqueness of the leafwise system, from the "flower clause" form of the data.**

This is `Work.EKLRelCross.leafwise_unique` with the `ν`-side of the hypothesis supplied
directly rather than packaged as an `IsLeafwise` structure: conull domain `X'`, Radon-ness,
`U`-carriage, the normalisation `ν x (Box1 U) = 1`, and the conditional-expectation clause
only for the countable π-system `Work.EKLRelCross.piSys` and only for the plaque algebras
`(Z n k, m n k)` of the given flower family.

The proof is the same comparison as in `leafwise_unique`: at a.e. `x` lying in a leaf of the
flower family with shape `S = shape (m n k) U x ⊇ B₁ᵁ`, the conditional-expectation clause
identifies the orbit averages of the π-system indicators for `ν x` and `ν' x` with the same
numbers, hence (by the π-λ argument `pushforward_relation_inline`) the pushforwards of
`ν x|_S` and `ν' x|_S` under `u ↦ u • x` are proportional; normalising on `B₁ᵁ`
(`restrict_eq_of_pushforward_relation`) gives `ν x|_S = ν' x|_S`, hence equality on every
`V R ∩ U`, whose union is `U`; both measures are carried by `U`. -/
theorem leafwise_eq_of_flower_clauses {ρ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure ρ] [StandardBorelSpace Work.EKLContract.X3]
    (h2 : Work.EKLContract.P_X3)
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) ρ ρ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {X' : Set Work.EKLContract.X3}
    (hX' : ρ X'ᶜ = 0)
    (hradon : ∀ x ∈ X', MeasureTheory.IsFiniteMeasureOnCompacts (ν x))
    (hcar : ∀ x ∈ X', ν x (U : Set Work.EKLContract.SL3)ᶜ = 0)
    (hnorm : ∀ x ∈ X', ν x (Work.EKLContract.Box1 U) = 1)
    (Z G : ℕ → ℕ → Set Work.EKLContract.X3) (m : ℕ → ℕ → MeasurableSpace Work.EKLContract.X3)
    (hplaq : ∀ n k, Work.EKLContract.IsPlaqueAlgebra U (Z n k) (m n k))
    (hGmeas : ∀ n k, MeasurableSet (G n k)) (hGZ : ∀ n k, G n k ⊆ Z n k)
    (hcover : ∀ n, ρ (⋃ k, G n k)ᶜ = 0)
    (hshape : ∀ n k, ∀ x ∈ G n k, ∀ u ∈ (Work.EKLContract.V ((n:ℝ)+2) ∩ (U : Set Work.EKLContract.SL3)), u • x ∈ Work.EKLContract.atom (m n k) x)
    (hclause : ∀ n k (C : Set Work.EKLContract.X3), C ∈ Work.EKLRelCross.piSys →
        MeasureTheory.condExp (m n k) (ρ.restrict (Z n k)) (C.indicator (fun _ => (1:ℝ)))
          =ᵐ[ρ.restrict (Z n k)]
        (fun x => (∫ u in Work.EKLContract.shape (m n k) U x, (C.indicator (fun _ => (1:ℝ))) (u • x) ∂(ν x))
          / ((ν x) (Work.EKLContract.shape (m n k) U x)).toReal))
    {ν' : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {X'' : Set Work.EKLContract.X3}
    (hL' : Work.EKLContract.IsLeafwise ρ U ν' X'') :
    ∀ᵐ x ∂ρ, ν' x = ν x := by
  classical
  have hcl : IsClosed (U : Set SL3) := hU.1
  have hfree := Work.EKLRelCross.ae_free_orbit h2 ρ U hU t0 ht0 hcontr
  have hZmeas : ∀ n k, MeasurableSet (Z n k) :=
    fun n k => (hplaq n k).1 (Z n k) (hplaq n k).2.2.1
  set F : Finset ↥(TopologicalSpace.countableBasis X3) → X3 → ℝ :=
    fun t => Set.indicator (⋂ b ∈ (t : Set ↥(TopologicalSpace.countableBasis X3)), (b : Set X3)) (1 : X3 → ℝ) with hF
  have hFmem : ∀ t : Finset ↥(TopologicalSpace.countableBasis X3),
      (⋂ b ∈ (t : Set ↥(TopologicalSpace.countableBasis X3)), (b : Set X3)) ∈ Work.EKLRelCross.piSys :=
    fun t => ⟨t, rfl⟩
  have hFmeas : ∀ t, Measurable (F t) := fun t =>
    measurable_const.indicator (Work.EKLRelCross.measurableSet_of_mem_piSys (hFmem t))
  have hFbdd : ∀ t, ∃ C, ∀ y, |F t y| ≤ C := by
    intro t
    refine ⟨1, fun y => ?_⟩
    by_cases hy : y ∈ (⋂ b ∈ (t : Set ↥(TopologicalSpace.countableBasis X3)), (b : Set X3))
    · have h1 : F t y = 1 := by rw [hF]; exact Set.indicator_of_mem hy (1 : X3 → ℝ)
      rw [h1]; norm_num
    · have h1 : F t y = 0 := by rw [hF]; exact Set.indicator_of_notMem hy (1 : X3 → ℝ)
      rw [h1]; norm_num
  have hEqν : ∀ n k t, ∀ᵐ x ∂(ρ.restrict (Z n k)),
      condExp (m n k) (ρ.restrict (Z n k)) (F t) x
        = (∫ u in shape (m n k) U x, (F t) (u • x) ∂(ν x)) / ((ν x) (shape (m n k) U x)).toReal := by
    intro n k t
    have h := hclause n k (⋂ b ∈ (t : Set ↥(TopologicalSpace.countableBasis X3)), (b : Set X3)) (hFmem t)
    filter_upwards [h] with x hx
    rw [hF]
    exact hx
  have hEqν' : ∀ n k t, ∀ᵐ x ∂(ρ.restrict (Z n k)),
      condExp (m n k) (ρ.restrict (Z n k)) (F t) x
        = (∫ u in shape (m n k) U x, (F t) (u • x) ∂(ν' x)) / ((ν' x) (shape (m n k) U x)).toReal :=
    fun n k t => hL'.condexp (Z n k) (m n k) (hplaq n k) (F t) (hFmeas t) (hFbdd t)
  have hEqAll : ∀ᵐ x ∂ρ, ∀ (i : ℕ × ℕ × Finset ↥(TopologicalSpace.countableBasis X3)), x ∈ Z i.1 i.2.1 →
      (condExp (m i.1 i.2.1) (ρ.restrict (Z i.1 i.2.1)) (F i.2.2) x
        = (∫ u in shape (m i.1 i.2.1) U x, (F i.2.2) (u • x) ∂(ν x)) / ((ν x) (shape (m i.1 i.2.1) U x)).toReal)
      ∧ (condExp (m i.1 i.2.1) (ρ.restrict (Z i.1 i.2.1)) (F i.2.2) x
        = (∫ u in shape (m i.1 i.2.1) U x, (F i.2.2) (u • x) ∂(ν' x)) / ((ν' x) (shape (m i.1 i.2.1) U x)).toReal) := by
    rw [eventually_countable_forall]
    intro i
    obtain ⟨n, k, t⟩ := i
    filter_upwards [(MeasureTheory.ae_restrict_iff' (hZmeas n k)).mp (hEqν n k t),
      (MeasureTheory.ae_restrict_iff' (hZmeas n k)).mp (hEqν' n k t)] with x h1 h2
    intro hx
    exact ⟨h1 hx, h2 hx⟩
  have hCoverAll : ∀ᵐ x ∂ρ, ∀ n : ℕ, x ∈ ⋃ k, G n k := by
    rw [eventually_countable_forall]
    intro n
    exact Filter.eventually_iff.mpr (MeasureTheory.mem_ae_iff.mpr (hcover n))
  have hevX' : ∀ᵐ x ∂ρ, x ∈ X' := Filter.eventually_iff.mpr (MeasureTheory.mem_ae_iff.mpr hX')
  have hevX'' : ∀ᵐ x ∂ρ, x ∈ X'' := Filter.eventually_iff.mpr (MeasureTheory.mem_ae_iff.mpr hL'.conull)
  have hstep : ∀ n : ℕ, ∀ᵐ x ∂ρ,
      (ν' x).restrict (V ((n:ℝ)+2) ∩ (U : Set SL3)) = (ν x).restrict (V ((n:ℝ)+2) ∩ (U : Set SL3)) := by
    intro n
    filter_upwards [hfree, hevX', hevX'', hCoverAll, hEqAll] with x hfreex hxX' hxX'' hcov hcond
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hcov n)
    set S : Set SL3 := shape (m n k) U x with hS
    have hxZ : x ∈ Z n k := hGZ n k hk
    have hbig : V ((n:ℝ)+2) ∩ (U : Set SL3) ⊆ S := fun u hu => ⟨hu.2, hshape n k x hk u hu⟩
    have hfreepair : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂ := by
      intro u₁ h1 u₂ h2 h
      have hmem : u₂⁻¹ * u₁ ∈ U := U.mul_mem (U.inv_mem h2) h1
      have hfix : (u₂⁻¹ * u₁) • x = x := by rw [mul_smul, h, inv_smul_smul]
      have h1' : u₂⁻¹ * u₁ = 1 := hfreex _ hmem hfix
      calc u₁ = u₂ * (u₂⁻¹ * u₁) := (mul_inv_cancel_left u₂ u₁).symm
        _ = u₂ * 1 := by rw [h1']
        _ = u₂ := mul_one u₂
    haveI hrad : IsFiniteMeasureOnCompacts (ν x) := hradon x hxX'
    haveI hrad' : IsFiniteMeasureOnCompacts (ν' x) := hL'.radon x hxX''
    have hSmeas : MeasurableSet S := by
      obtain ⟨O, hO, hshapeO⟩ := (hplaq n k).2.2.2 x hxZ |>.2.2.1
      rw [hS, hshapeO]
      exact hO.measurableSet.inter hcl.measurableSet
    have hSU : S ⊆ (U : Set SL3) := fun u hu => hu.1
    have hBoxS : Box1 U ⊆ S := fun u hu => hbig (by
      refine ⟨fun i j => lt_of_le_of_lt (hu.2 i j) ?_, hu.1⟩
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith)
    have hSfin : (ν x) S ≠ ⊤ := by
      obtain ⟨C, hC⟩ := (hplaq n k).2.2.2 x hxZ |>.2.2.2
      have hsub : S ⊆ {g : SL3 | ∀ i j, -(C+1) ≤ g i j ∧ g i j ≤ C+1} := by
        intro u hu i j
        have := hC u hu i j
        exact ⟨by linarith [neg_le_abs (u i j)], by linarith [le_abs_self (u i j)]⟩
      have hcomp : IsCompact {g : SL3 | ∀ i j, -(C+1) ≤ g i j ∧ g i j ≤ C+1} :=
        Work.EKLProd.sl3EntryBox_compact (fun _ _ => -(C+1)) (fun _ _ => C+1)
      exact ne_top_of_le_ne_top (hcomp.measure_lt_top (μ := ν x)).ne (measure_mono hsub)
    have hSfin' : (ν' x) S ≠ ⊤ := by
      obtain ⟨C, hC⟩ := (hplaq n k).2.2.2 x hxZ |>.2.2.2
      have hsub : S ⊆ {g : SL3 | ∀ i j, -(C+1) ≤ g i j ∧ g i j ≤ C+1} := by
        intro u hu i j
        have := hC u hu i j
        exact ⟨by linarith [neg_le_abs (u i j)], by linarith [le_abs_self (u i j)]⟩
      have hcomp : IsCompact {g : SL3 | ∀ i j, -(C+1) ≤ g i j ∧ g i j ≤ C+1} :=
        Work.EKLProd.sl3EntryBox_compact (fun _ _ => -(C+1)) (fun _ _ => C+1)
      exact ne_top_of_le_ne_top (hcomp.measure_lt_top (μ := ν' x)).ne (measure_mono hsub)
    have hSpos : (ν x) S ≠ 0 := by
      have h1 : (1:ℝ≥0∞) ≤ (ν x) S := by
        rw [← hnorm x hxX']
        exact measure_mono hBoxS
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one h1)
    have hSpos' : (ν' x) S ≠ 0 := by
      have h1 : (1:ℝ≥0∞) ≤ (ν' x) S := by
        rw [← hL'.normalised x hxX'']
        exact measure_mono hBoxS
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one h1)
    have hrel : (ν' x) S • ((ν x).restrict S).map (fun g : SL3 => g • x)
        = (ν x) S • ((ν' x).restrict S).map (fun g : SL3 => g • x) := by
      refine Work.EKLRelCross.pushforward_relation_inline x S (ν x) (ν' x) hSmeas hSfin hSfin' hSpos hSpos'
        (fun C => condExp (m n k) (ρ.restrict (Z n k)) (Set.indicator C (1 : X3 → ℝ)) x) ?_
      intro C hC
      rw [Work.EKLRelCross.piSys, Set.mem_range] at hC
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
      Work.EKLRelCross.restrict_eq_of_pushforward_relation U x S hcl (Work.EKLC6Core.isCompact_box1 hU)
        hSmeas hBoxS hSU hfreepair (ν x) (ν' x) hSfin hSfin' (hnorm x hxX') (hL'.normalised x hxX'') hrel
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
  have hstepall : ∀ᵐ x ∂ρ, ∀ n : ℕ,
      (ν' x).restrict (V ((n:ℝ)+2) ∩ (U : Set SL3)) = (ν x).restrict (V ((n:ℝ)+2) ∩ (U : Set SL3)) := by
    rw [eventually_countable_forall]
    exact hstep
  filter_upwards [hstepall, hevX', hevX''] with x hstx hxX' hxX''
  refine Measure.ext (fun A hA => ?_)
  have hμU : (ν x) ((U : Set SL3)ᶜ) = 0 := hcar x hxX'
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

end Work.EKLC6Core
