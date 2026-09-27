import Mathlib
import Submission.Work.EKLRelCross.LeafCtor
import Submission.Work.EKLRelCross.pushOrbit_apply_of_injective
import Submission.Work.EKLRelCross.piece_meets_compact_finite

namespace Work.EKLRelCross

open MeasureTheory
open Work.EKLContract
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

lemma lbf_piece_zero (U : Subgroup SL3) : piece U 0 = Box1 U := rfl

lemma lbf_Box1_subset (U : Subgroup SL3) : Box1 U ⊆ (U : Set SL3) := fun _ hg => hg.1

lemma lbf_Ucl_mono (U : Subgroup SL3) {r r' : ℝ} (h : r ≤ r') : Ucl U r ⊆ Ucl U r' :=
  fun g hg => ⟨hg.1, fun i j => le_trans (hg.2 i j) h⟩

lemma lbf_Box1_inter_piece (U : Subgroup SL3) {k : ℕ} (hk : 1 ≤ k) : Box1 U ∩ piece U k = ∅ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  ext g
  constructor
  · intro hg
    obtain ⟨hg1, hg2⟩ := hg
    exact absurd (lbf_Ucl_mono U (by norm_num : (1 : ℝ) ≤ (j : ℝ) + 1) hg1) hg2.2
  · intro hg; exact absurd hg (Set.notMem_empty g)

lemma lbf_isClosed_entryBox (r : ℝ) :
    IsClosed {g : SL3 | ∀ i j : Fin 3,
      |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ r} := by
  have h : {g : SL3 | ∀ i j : Fin 3,
      |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ r}
      = ⋂ i, ⋂ j, {g : SL3 | |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ r} := by
    ext g
    simp [Set.mem_iInter]
  rw [h]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  have hcont : Continuous fun g : SL3 => (g : Matrix (Fin 3) (Fin 3) ℝ) i j := by fun_prop
  exact isClosed_le (continuous_abs.comp (hcont.sub continuous_const)) continuous_const

lemma lbf_measurableSet_Ucl {U : Subgroup SL3} (hU : IsClosed (U : Set SL3)) (r : ℝ) :
    MeasurableSet (Ucl U r) := by
  have h : Ucl U r = (U : Set SL3) ∩ {g : SL3 | ∀ i j : Fin 3,
      |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ r} := rfl
  rw [h]
  exact hU.measurableSet.inter (lbf_isClosed_entryBox r).measurableSet

lemma lbf_measurableSet_Box1 {U : Subgroup SL3} (hU : IsClosed (U : Set SL3)) :
    MeasurableSet (Box1 U) := by
  rw [Box1_eq_Ucl]
  exact lbf_measurableSet_Ucl hU 1

lemma lbf_measurableSet_piece {U : Subgroup SL3} (hU : IsClosed (U : Set SL3)) (k : ℕ) :
    MeasurableSet (piece U k) := by
  cases k with
  | zero => rw [lbf_piece_zero]; exact lbf_measurableSet_Box1 hU
  | succ k => exact (lbf_measurableSet_Ucl hU _).diff (lbf_measurableSet_Ucl hU _)

lemma lbf_pushOrbit_univ_le (U : Subgroup SL3) (x : X3) (ν : Measure X3) :
    pushOrbit U x ν Set.univ ≤ ν Set.univ := by
  rw [pushOrbit, Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ]
  refine le_trans (Measure.comap_apply_le (fun u : U => ((u : SL3) • x)) ν
    MeasurableSet.univ.nullMeasurableSet) (measure_mono (Set.subset_univ _))

lemma lbf_refPush_le_one (U : Subgroup SL3) (μ : Measure X3) [IsFiniteMeasure μ]
    (Z : ℕ → Set X3) (m : ℕ → MeasurableSpace X3) (G : ℕ → Set X3) (x : X3) :
    refPush U μ Z m G x Set.univ ≤ 1 := by
  rw [refPush]
  refine le_trans (lbf_pushOrbit_univ_le U x _) (le_of_eq ?_)
  rw [refKernel]
  exact (ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure
    (κ := ProbabilityTheory.condExpKernel (μ.restrict (Z (sel G x))) (m (sel G x))) x).measure_univ

lemma lbf_pushOrbit_carried (U : Subgroup SL3) (hU : IsClosed (U : Set SL3)) (x : X3)
    (ν : Measure X3) : pushOrbit U x ν ((U : Set SL3)ᶜ) = 0 := by
  have hpre : (Subtype.val ⁻¹' ((U : Set SL3)ᶜ) : Set U) = ∅ := by
    ext u
    constructor
    · intro h; exact absurd u.2 h
    · intro h; exact absurd h (Set.notMem_empty u)
  rw [pushOrbit, Measure.map_apply measurable_subtype_coe hU.measurableSet.compl, hpre]
  exact measure_empty

lemma lbf_refPush_carried (U : Subgroup SL3) (hU : IsClosed (U : Set SL3)) (μ : Measure X3)
    [IsFiniteMeasure μ] (Z : ℕ → Set X3) (m : ℕ → MeasurableSpace X3) (G : ℕ → Set X3) (x : X3) :
    refPush U μ Z m G x ((U : Set SL3)ᶜ) = 0 :=
  lbf_pushOrbit_carried U hU x _

lemma lbf_nuLevel_carried (U : Subgroup SL3) (hU : IsClosed (U : Set SL3)) (μ : Measure X3)
    [IsFiniteMeasure μ] (Z : ℕ → Set X3) (m : ℕ → MeasurableSpace X3) (G : ℕ → Set X3) (x : X3) :
    nuLevel U μ Z m G x ((U : Set SL3)ᶜ) = 0 := by
  rw [nuLevel, Measure.smul_apply, lbf_refPush_carried U hU]
  simp

lemma lbf_nuLevel_univ_lt_top {U : Subgroup SL3} {μ : Measure X3} [IsFiniteMeasure μ]
    {Z : ℕ → Set X3} {m : ℕ → MeasurableSpace X3} {G : ℕ → Set X3} {x : X3}
    (hc : refPush U μ Z m G x (Box1 U) ≠ 0) :
    nuLevel U μ Z m G x Set.univ < ⊤ := by
  rw [nuLevel, Measure.smul_apply]
  refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hc)) ?_
  exact lt_of_le_of_lt (lbf_refPush_le_one U μ Z m G x) ENNReal.one_lt_top

theorem lbf_nuFull_isFiniteMeasureOnCompacts {U : Subgroup SL3} [StandardBorelSpace X3]
    (μ : Measure X3) [IsFiniteMeasure μ] (Z : ℕ → ℕ → Set X3) (m : ℕ → ℕ → MeasurableSpace X3)
    (G : ℕ → ℕ → Set X3) (x : X3)
    (hc : ∀ k : ℕ, refPush U μ (Z k) (m k) (G k) x (Box1 U) ≠ 0) :
    IsFiniteMeasureOnCompacts (nuFull U μ Z m G x) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨N, hN⟩ := piece_meets_compact_finite (U := U) hK
  rw [nuFull, Measure.sum_apply _ hK.measurableSet]
  rw [show (∑' k, ((nuLevel U μ (Z k) (m k) (G k) x).restrict (piece U k)) K)
      = ∑ k ∈ Finset.range N, ((nuLevel U μ (Z k) (m k) (G k) x).restrict (piece U k)) K from
    tsum_eq_sum (fun k hk => by
      rw [Measure.restrict_apply hK.measurableSet, hN k (by simpa using hk), measure_empty])]
  exact ENNReal.sum_lt_top.mpr fun k _ => by
    rw [Measure.restrict_apply hK.measurableSet]
    exact lt_of_le_of_lt (le_trans (measure_mono Set.inter_subset_right)
      (measure_mono (Set.subset_univ _))) (lbf_nuLevel_univ_lt_top (hc k))

theorem lbf_nuFull_carried {U : Subgroup SL3} (hU : IsClosed (U : Set SL3))
    [StandardBorelSpace X3] (μ : Measure X3) [IsFiniteMeasure μ] (Z : ℕ → ℕ → Set X3)
    (m : ℕ → ℕ → MeasurableSpace X3) (G : ℕ → ℕ → Set X3) (x : X3) :
    nuFull U μ Z m G x ((U : Set SL3)ᶜ) = 0 := by
  rw [nuFull, Measure.sum_apply _ hU.measurableSet.compl]
  have hk0 : ∀ k : ℕ, (nuLevel U μ (Z k) (m k) (G k) x) ((U : Set SL3)ᶜ ∩ piece U k) = 0 := by
    intro k
    have hempty : (U : Set SL3)ᶜ ∩ piece U k = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro g hg
      exact hg.1 (piece_subset_U U k hg.2)
    rw [hempty, measure_empty]
  rw [show (∑' k, ((nuLevel U μ (Z k) (m k) (G k) x).restrict (piece U k)) ((U : Set SL3)ᶜ))
      = ∑' _k : ℕ, (0 : ℝ≥0∞) from tsum_congr (fun k => by
        rw [Measure.restrict_apply hU.measurableSet.compl]
        exact hk0 k), tsum_zero]

theorem lbf_nuFull_Box1 {U : Subgroup SL3} (hU : IsClosed (U : Set SL3)) [StandardBorelSpace X3]
    (μ : Measure X3) [IsFiniteMeasure μ] (Z : ℕ → ℕ → Set X3) (m : ℕ → ℕ → MeasurableSpace X3)
    (G : ℕ → ℕ → Set X3) (x : X3)
    (hc : refPush U μ (Z 0) (m 0) (G 0) x (Box1 U) ≠ 0) :
    nuFull U μ Z m G x (Box1 U) = 1 := by
  have hB : MeasurableSet (Box1 U) := lbf_measurableSet_Box1 hU
  rw [nuFull, Measure.sum_apply _ hB]
  rw [tsum_eq_sum (s := {0}) (fun k hk => ?_)]
  · rw [Finset.sum_singleton]
    rw [Measure.restrict_apply hB,
      show Box1 U ∩ piece U 0 = Box1 U from by rw [lbf_piece_zero, Set.inter_self]]
    rw [nuLevel, Measure.smul_apply]
    exact ENNReal.inv_mul_cancel hc (ne_of_lt (lt_of_le_of_lt
      (measure_mono (Set.subset_univ _))
      (lt_of_le_of_lt (lbf_refPush_le_one U μ (Z 0) (m 0) (G 0) x) ENNReal.one_lt_top)))
  · have hk0 : k ≠ 0 := by simpa using hk
    rw [Measure.restrict_apply hB, lbf_Box1_inter_piece U (by omega), measure_empty]

theorem lbf_nuFull_pos {U : Subgroup SL3} (hU : IsClosed (U : Set SL3)) [StandardBorelSpace X3]
    (μ : Measure X3) [IsFiniteMeasure μ] (Z : ℕ → ℕ → Set X3) (m : ℕ → ℕ → MeasurableSpace X3)
    (G : ℕ → ℕ → Set X3) (x : X3) {δ r : ℝ}
    (hinj : Function.Injective (fun u : U => ((u : SL3) • x)))
    (hr0 : 0 < r) (hrδ : r ≤ δ) (hr1 : r ≤ 1)
    (hker : 0 < refKernel μ (Z 0) (m 0) (G 0) x
      ((fun g : SL3 => g • x) '' (V r ∩ (U : Set SL3)))) :
    0 < nuFull U μ Z m G x (V δ) := by
  have hVopen : IsOpen (V r) := (Work.EKLContract.Lemmas.V_open_one r hr0).1
  have hmeasV : MeasurableSet (V r ∩ (U : Set SL3)) := hVopen.measurableSet.inter hU.measurableSet
  have hVsub : V r ∩ (U : Set SL3) ⊆ Box1 U := by
    intro g hg
    exact ⟨hg.2, fun i j => le_of_lt (lt_of_lt_of_le (hg.1 i j) hr1)⟩
  have hsub : V r ∩ (U : Set SL3) ⊆ V δ := fun g hg i j => lt_of_lt_of_le (hg.1 i j) hrδ
  have hsum : nuFull U μ Z m G x (V r ∩ (U : Set SL3))
      = ∑' k, (nuLevel U μ (Z k) (m k) (G k) x) (piece U k ∩ (V r ∩ (U : Set SL3))) := by
    rw [nuFull, Measure.sum_apply _ hmeasV]
    exact tsum_congr fun k => by rw [Measure.restrict_apply hmeasV, Set.inter_comm]
  have hterm0 : (nuLevel U μ (Z 0) (m 0) (G 0) x) (piece U 0 ∩ (V r ∩ (U : Set SL3)))
      = (refPush U μ (Z 0) (m 0) (G 0) x (Box1 U))⁻¹ *
        refPush U μ (Z 0) (m 0) (G 0) x (V r ∩ (U : Set SL3)) := by
    rw [nuLevel, Measure.smul_apply]
    congr 1
    rw [lbf_piece_zero, Set.inter_eq_right.mpr hVsub]
  have hpush : refPush U μ (Z 0) (m 0) (G 0) x (V r ∩ (U : Set SL3))
      = refKernel μ (Z 0) (m 0) (G 0) x
          ((fun g : SL3 => g • x) '' (V r ∩ (U : Set SL3))) := by
    rw [refPush, pushOrbit_apply_of_injective hU hinj
      (refKernel μ (Z 0) (m 0) (G 0) x) hmeasV]
    congr 1
    rw [Set.inter_eq_left.mpr Set.inter_subset_right]
  have hle : nuFull U μ Z m G x (V r ∩ (U : Set SL3)) ≤ nuFull U μ Z m G x (V δ) :=
    measure_mono hsub
  refine lt_of_lt_of_le ?_ hle
  rw [hsum]
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum 0)
  rw [hterm0, hpush]
  rcases eq_or_ne (refPush U μ (Z 0) (m 0) (G 0) x (Box1 U)) 0 with h0 | h0
  · rw [h0, ENNReal.inv_zero, ENNReal.top_mul', if_neg hker.ne']
    exact ENNReal.zero_lt_top
  · refine pos_iff_ne_zero.mpr (mul_ne_zero ?_ hker.ne')
    exact ENNReal.inv_ne_zero.mpr (ne_of_lt (lt_of_le_of_lt
      (measure_mono (Set.subset_univ _))
      (lt_of_le_of_lt (lbf_refPush_le_one U μ (Z 0) (m 0) (G 0) x) ENNReal.one_lt_top)))

/-! ## The two-parameter family of scales used for the positivity sets -/

/-- The scales `r n = 1/(n+1)` used to build the (countably many) positivity conditions. -/
def lbf_r (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

lemma lbf_r_pos (n : ℕ) : 0 < lbf_r n := by unfold lbf_r; positivity

lemma lbf_r_le_one (n : ℕ) : lbf_r n ≤ 1 := by
  unfold lbf_r
  rw [div_le_one (by positivity)]
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

/-- The positivity condition supplied by `PosPiece` for the plaque algebra `(Z k i, m k i)` and
the plaque `V (lbf_r n) ∩ U` at the point `x`. -/
def lbf_phi (U : Subgroup SL3) (μ : Measure X3) [IsFiniteMeasure μ] [StandardBorelSpace X3]
    (Z : ℕ → ℕ → Set X3) (m : ℕ → ℕ → MeasurableSpace X3) (k i n : ℕ) (x : X3) : Prop :=
  0 < ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3)
      (μ.restrict (Z k i)) (m k i) x
      ((fun g : SL3 => g • x) '' ((V (lbf_r n) : Set SL3) ∩ (U : Set SL3)))

/-- If the orbit map is injective at `x` and the conditional kernel puts positive mass on the
plaque `V r ∩ U`, then `refPush` puts positive mass on `B₁ᵁ`. -/
lemma lbf_refPush_Box1_ne_zero {U : Subgroup SL3} (hU : IsClosed (U : Set SL3))
    [StandardBorelSpace X3] (μ : Measure X3) [IsFiniteMeasure μ] (Z : ℕ → Set X3)
    (m : ℕ → MeasurableSpace X3) (G : ℕ → Set X3) (x : X3) {r : ℝ} (hr1 : r ≤ 1)
    (hinj : Function.Injective (fun u : U => ((u : SL3) • x)))
    (hker : 0 < refKernel μ Z m G x ((fun g : SL3 => g • x) '' (V r ∩ (U : Set SL3)))) :
    refPush U μ Z m G x (Box1 U) ≠ 0 := by
  have hbox : MeasurableSet (Box1 U) := lbf_measurableSet_Box1 hU
  have hstep : refPush U μ Z m G x (Box1 U)
      = refKernel μ Z m G x ((fun g : SL3 => g • x) '' Box1 U) := by
    rw [refPush, pushOrbit_apply_of_injective hU hinj (refKernel μ Z m G x) hbox]
    congr 1
    rw [Set.inter_eq_left.mpr (lbf_Box1_subset U)]
  rw [hstep]
  exact ne_of_gt (lt_of_lt_of_le hker (measure_mono (Set.image_mono (fun g hg =>
    ⟨hg.2, fun i j => le_of_lt (lt_of_lt_of_le (hg.1 i j) hr1)⟩))))

/-! ## The exceptional set and the assembly -/

theorem leafwise_base_fields_free {U : Subgroup Work.EKLContract.SL3}
    (hUcl : IsClosed (U : Set Work.EKLContract.SL3))
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    [StandardBorelSpace Work.EKLContract.X3] (D : Work.EKLRelCross.FlowerData U μ)
    (hpos : Work.EKLRelCross.PosPiece U μ)
    (hfree : ∀ᵐ x ∂μ, Function.Injective (fun u : U => (u : Work.EKLContract.SL3) • x)) :
    ∃ X' : Set Work.EKLContract.X3, MeasurableSet X' ∧ μ X'ᶜ = 0 ∧
      (∀ x ∈ X', Function.Injective (fun u : U => (u : Work.EKLContract.SL3) • x)) ∧
      (∀ x ∈ X',
        MeasureTheory.IsFiniteMeasureOnCompacts (Work.EKLRelCross.nuFull U μ D.Z D.m D.G x) ∧
        (Work.EKLRelCross.nuFull U μ D.Z D.m D.G x) ((U : Set Work.EKLContract.SL3)ᶜ) = 0 ∧
        (Work.EKLRelCross.nuFull U μ D.Z D.m D.G x) (Work.EKLContract.Box1 U) = 1 ∧
        (∀ δ : ℝ, 0 < δ → 0 < (Work.EKLRelCross.nuFull U μ D.Z D.m D.G x) (Work.EKLContract.V δ))) := by
  classical
  -- Each positivity condition of `PosPiece` fails on a `μ.restrict`-null set.
  have hA : ∀ k i n, μ (D.G k i ∩ {x | ¬ lbf_phi U μ D.Z D.m k i n x}) = 0 := by
    intro k i n
    have hO : IsOpen (V (lbf_r n)) :=
      (Work.EKLContract.Lemmas.V_open_one (lbf_r n) (lbf_r_pos n)).1
    have h1O : (1 : SL3) ∈ V (lbf_r n) :=
      (Work.EKLContract.Lemmas.V_open_one (lbf_r n) (lbf_r_pos n)).2
    have hae := hpos (D.Z k i) ⟨D.m k i⟩ (D.isPlaque k i) (V (lbf_r n)) hO h1O
    have hzero : (μ.restrict (D.Z k i)) {x | ¬ lbf_phi U μ D.Z D.m k i n x} = 0 := by
      simpa only [lbf_phi] using (ae_iff.mp hae)
    have hZ : MeasurableSet (D.Z k i) :=
      (MeasurableSpace.le_def.mp (D.isPlaque k i).1) _ (D.isPlaque k i).2.2.1
    rw [Measure.restrict_apply' hZ] at hzero
    refine measure_mono_null ?_ hzero
    rintro y ⟨hyG, hyA⟩
    exact ⟨hyA, D.sub k i hyG⟩
  -- The exceptional set.
  let F : Set X3 := {x | ¬ Function.Injective (fun u : U => (u : SL3) • x)}
  let Cov : Set X3 := ⋃ k, (⋃ i, D.G k i)ᶜ
  let AA : Set X3 := ⋃ k, ⋃ i, ⋃ n, (D.G k i ∩ {x | ¬ lbf_phi U μ D.Z D.m k i n x})
  let Bad : Set X3 := F ∪ (Cov ∪ AA)
  have hF : μ F = 0 := by
    simpa only [F] using (ae_iff.mp hfree)
  have hCov : μ Cov = 0 := by
    refine measure_iUnion_null (fun k => ?_)
    simpa only [Cov] using D.cover k
  have hAA : μ AA = 0 := by
    refine measure_iUnion_null (fun k => ?_)
    refine measure_iUnion_null (fun i => ?_)
    refine measure_iUnion_null (fun n => ?_)
    exact hA k i n
  have hBad : μ Bad = 0 := by
    have h1 : μ (Cov ∪ AA) = 0 := measure_union_null hCov hAA
    have h2 : μ (F ∪ (Cov ∪ AA)) = 0 := measure_union_null hF h1
    simpa only [Bad] using h2
  refine ⟨(toMeasurable μ Bad)ᶜ, ?_, ?_, ?_, ?_⟩
  · exact (measurableSet_toMeasurable μ Bad).compl
  · simp only [compl_compl, measure_toMeasurable, hBad]
  · -- Injectivity on `X'`.
    intro x hx
    have hxBad : x ∉ Bad := fun h => hx (subset_toMeasurable μ Bad h)
    have hF' : x ∉ F := fun h => hxBad (Or.inl h)
    exact not_not.mp hF'
  · -- The base fields of `nuFull`.
    intro x hx
    have hxBad : x ∉ Bad := fun h => hx (subset_toMeasurable μ Bad h)
    have hinj : Function.Injective (fun u : U => (u : SL3) • x) := by
      have hF' : x ∉ F := fun h => hxBad (Or.inl h)
      exact not_not.mp hF'
    have hxCovAA : x ∉ Cov ∪ AA := fun h => hxBad (Or.inr h)
    have hxCov : x ∉ Cov := fun h => hxCovAA (Or.inl h)
    have hxAA : x ∉ AA := fun h => hxCovAA (Or.inr h)
    have hGex : ∀ k, ∃ i, x ∈ D.G k i := by
      intro k
      have h1 : x ∈ ⋃ i, D.G k i := by
        by_contra h
        exact hxCov (show x ∈ Cov from Set.mem_iUnion.mpr ⟨k, h⟩)
      exact Set.mem_iUnion.mp h1
    have hsel_mem : ∀ k, x ∈ D.G k (sel (D.G k) x) := by
      intro k
      rw [sel, dif_pos (hGex k)]
      exact Nat.find_spec (hGex k)
    have hphi : ∀ k n, lbf_phi U μ D.Z D.m k (sel (D.G k) x) n x := by
      intro k n
      have hmem : x ∈ D.G k (sel (D.G k) x) := hsel_mem k
      have hnotA : x ∉ {y | ¬ lbf_phi U μ D.Z D.m k (sel (D.G k) x) n y} := by
        intro h
        exact hxAA (show x ∈ AA from Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr
          ⟨sel (D.G k) x, Set.mem_iUnion.mpr ⟨n, ⟨hmem, h⟩⟩⟩⟩)
      exact not_not.mp (by simpa using hnotA)
    have hrefK : ∀ k, refKernel μ (D.Z k) (D.m k) (D.G k) x
        = ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3)
            (μ.restrict (D.Z k (sel (D.G k) x))) (D.m k (sel (D.G k) x)) x := by
      intro k; rw [refKernel]
    have hker : ∀ k n, 0 < refKernel μ (D.Z k) (D.m k) (D.G k) x
        ((fun g : SL3 => g • x) '' (V (lbf_r n) ∩ (U : Set SL3))) := by
      intro k n
      rw [hrefK k]
      simpa only [lbf_phi] using hphi k n
    have hne : ∀ k, refPush U μ (D.Z k) (D.m k) (D.G k) x (Box1 U) ≠ 0 :=
      fun k => lbf_refPush_Box1_ne_zero hUcl μ (D.Z k) (D.m k) (D.G k) x
        (lbf_r_le_one 0) hinj (hker k 0)
    refine ⟨lbf_nuFull_isFiniteMeasureOnCompacts μ D.Z D.m D.G x hne,
      lbf_nuFull_carried hUcl μ D.Z D.m D.G x, lbf_nuFull_Box1 hUcl μ D.Z D.m D.G x (hne 0), ?_⟩
    intro δ hδ
    set n : ℕ := Nat.ceil (1 / δ) with hn
    have hrδ : lbf_r n ≤ δ := by
      unfold lbf_r
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      have h1 : 1 / δ ≤ (n : ℝ) := by rw [hn]; exact Nat.le_ceil _
      have h2 : 1 ≤ δ * (n : ℝ) := by rw [mul_comm]; exact (div_le_iff₀ hδ).mp h1
      nlinarith [h2]
    exact lbf_nuFull_pos hUcl μ D.Z D.m D.G x hinj (lbf_r_pos n) hrδ (lbf_r_le_one n) (hker 0 n)

end

end Work.EKLRelCross
