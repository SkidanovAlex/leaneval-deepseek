import Mathlib
import Submission.Work.EKLRelCross.LeafCtor
import Submission.Work.EKLRelCross.LeafMeasDefs
import Submission.Work.EKLRelCross.measurable_orbitLintegral
import Submission.Work.EKLRelCross.pushOrbit_lintegral_eq

/-!
# Measurability of the leafwise field `x ↦ ∫ f d(ν x)` for `LeafCtor.nuFull`

The field `nuFull U μ D.Z D.m D.G : X3 → Measure SL3` is built out of conditional kernels of
plaque algebras, pushed to the subgroup `U` along the orbit maps `u ↦ u • x`.  This file proves
that it is weakly measurable: for every compactly supported continuous `f : SL3 → ℝ` the function
`x ↦ ∫ g, f g ∂(nuFull U μ D.Z D.m D.G x)` is measurable.

Route.
* `cekKernel` — the conditional kernel of a plaque algebra as a kernel with the *Borel* σ-algebra
  on the source (the `MSAlgG` wrapper avoids instance capture);
* `lintegral_nuLevel_restrict` — the level term of `nuFull` is, definitionally, the level `k` of
  the normalised pushforward: `(refPush … (Box1 U))⁻¹ * ∫⁻ g, Ψ g · 1_{piece k}(g) ∂refPush`;
* `pushOrbit_lintegral_eq` — on a free orbit the pushforward integral is the layer-cake integral
  of the conditional kernel over the orbit-images of the superlevel sets;
* `measurable_orbitLintegral` — that layer-cake integral is measurable in `x`;
* off the (Borel, `freeSet_borel`) free-orbit set the whole field vanishes, because `pushOrbit` is
  `Measure.comap` of a non-injective map, which is the zero measure; so the field is
  `1_F · (measurable)`.
-/

open MeasureTheory Topology Filter
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-! ## The conditional kernel of a plaque algebra, as a Borel-source kernel -/

/-- The conditional expectation kernel of `(Z, m)` seen as a kernel from `X₃` (with the Borel
σ-algebra) to `X₃`.  The σ-algebra `m` is wrapped in `MSAlgG` so that it is not picked up by
instance search. -/
def cekKernel (ρ : Measure X3) [IsFiniteMeasure ρ] (A : MSAlgG X3) (hm : A.m ≤ borel X3) :
    ProbabilityTheory.Kernel X3 X3 where
  toFun := fun x => ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) ρ A.m x
  measurable' := MeasureTheory.Measure.measurable_of_measurable_coe _
    (fun s hs => (ProbabilityTheory.measurable_condExpKernel (m := A.m)
      (mΩ := instMeasurableSpaceX3) (μ := ρ) hs).mono hm le_rfl)

theorem cekKernel_apply (ρ : Measure X3) [IsFiniteMeasure ρ] (A : MSAlgG X3)
    (hm : A.m ≤ borel X3) (x : X3) :
    cekKernel ρ A hm x
      = ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) ρ A.m x := rfl

theorem isFiniteMeasure_cekKernel (ρ : Measure X3) [IsFiniteMeasure ρ] (A : MSAlgG X3)
    (hm : A.m ≤ borel X3) (x : X3) : IsFiniteMeasure (cekKernel ρ A hm x) := by
  rw [cekKernel_apply]
  infer_instance

/-! ## Measurability of the annuli `piece` -/

theorem measurableSet_piece (U : Subgroup SL3) (hUcl : IsClosed (U : Set SL3)) (k : ℕ) :
    MeasurableSet (piece U k) := by
  cases k with
  | zero => exact (isClosed_Ucl_expl U hUcl 1).measurableSet
  | succ j =>
    exact ((isClosed_Ucl_expl U hUcl _).measurableSet).diff ((isClosed_Ucl_expl U hUcl _).measurableSet)

/-! ## The index `sel` -/

theorem sel_eq_iff (G : ℕ → Set X3) (i : ℕ) (x : X3) :
    sel G x = i ↔ (x ∈ G i ∧ ∀ j < i, x ∉ G j) ∨ (i = 0 ∧ ∀ j, x ∉ G j) := by
  classical
  unfold sel
  by_cases h : ∃ k, x ∈ G k
  · rw [dif_pos h]
    constructor
    · intro heq
      left
      refine ⟨?_, fun j hj hxj => Nat.find_min h (heq.symm ▸ hj) hxj⟩
      rw [← heq]
      exact Nat.find_spec h
    · rintro (⟨hgi, hlt⟩ | ⟨h0, hall⟩)
      · exact le_antisymm (Nat.find_min' h hgi)
          (not_lt.mp fun hc => hlt (Nat.find h) hc (Nat.find_spec h))
      · obtain ⟨k, hk⟩ := h
        exact absurd hk (hall k)
  · rw [dif_neg h]
    constructor
    · rintro rfl
      exact Or.inr ⟨rfl, fun j hxj => h ⟨j, hxj⟩⟩
    · rintro (⟨hgi, _⟩ | ⟨h0, _⟩)
      · exact absurd ⟨i, hgi⟩ h
      · exact h0.symm

theorem measurableSet_sel_eq (G : ℕ → Set X3) (hG : ∀ i, MeasurableSet (G i)) (i : ℕ) :
    MeasurableSet {x : X3 | sel G x = i} := by
  have hcompl : MeasurableSet (⋃ j ∈ Finset.range i, G j) :=
    MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hG j
  have hset : {x : X3 | sel G x = i}
      = (G i ∩ (⋃ j ∈ Finset.range i, G j)ᶜ) ∪
        (if i = 0 then (⋃ j, G j)ᶜ else (∅ : Set X3)) := by
    ext x
    rw [Set.mem_ofPred_eq, sel_eq_iff]
    constructor
    · rintro (⟨hgi, hlt⟩ | ⟨h0, hall⟩)
      · left
        refine ⟨hgi, ?_⟩
        simp only [Set.mem_compl_iff, Set.mem_iUnion, exists_prop, not_exists, not_and]
        exact fun j hj => hlt j (Finset.mem_range.mp hj)
      · right
        subst h0
        rw [if_pos rfl]
        simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
        exact hall
    · rintro (⟨hgi, hlt⟩ | hmem)
      · exact Or.inl ⟨hgi, fun j hj hxj =>
          hlt (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hj, hxj⟩⟩)⟩
      · by_cases hi : i = 0
        · subst hi
          rw [if_pos rfl] at hmem
          exact Or.inr ⟨rfl, fun j hxj => hmem (Set.mem_iUnion.mpr ⟨j, hxj⟩)⟩
        · rw [if_neg hi] at hmem
          exact absurd hmem (Set.notMem_empty x)
  rw [hset]
  by_cases hi : i = 0
  · rw [if_pos hi]
    exact ((hG i).inter hcompl.compl).union (MeasurableSet.iUnion hG).compl
  · rw [if_neg hi]
    exact ((hG i).inter hcompl.compl).union MeasurableSet.empty

/-! ## The level term of `nuFull` -/

/-- The `k`-th level term of `nuFull` is, by definition, the level `k` of the normalised
pushforward; integrating it amounts to integrating against the indicator of the `k`-th annulus. -/
theorem lintegral_nuLevel_restrict {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
    {μ : Measure X3} [IsFiniteMeasure μ]
    (Z : ℕ → Set X3) (m : ℕ → MeasurableSpace X3) (G : ℕ → Set X3) (x : X3) (k : ℕ)
    (Ψ : SL3 → ENNReal) :
    ∫⁻ g, Ψ g ∂((nuLevel U μ Z m G x).restrict (piece U k))
      = (refPush U μ Z m G x (Box1 U))⁻¹ *
        ∫⁻ g, Ψ g * (piece U k).indicator (fun _ => (1 : ENNReal)) g
          ∂(refPush U μ Z m G x) := by
  have hmeas := measurableSet_piece U hUcl k
  rw [nuLevel, Measure.restrict_smul, lintegral_smul_measure]
  congr 1
  rw [← lintegral_indicator hmeas Ψ]
  refine lintegral_congr fun g => ?_
  by_cases hg : g ∈ piece U k
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, mul_one]
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, mul_zero]

/-! ## Pasting over the index `sel` -/

/-- Measurability of `x ↦ κ (sel (G x)) x (orbImg U x C)`: on the (measurable) pieces
`{x | sel G x = i}` the family is the measurable `x ↦ κ i x (orbImg U x C)`. -/
theorem measurable_sel_apply {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
    {G : ℕ → Set X3} (hG : ∀ i, MeasurableSet (G i))
    (KK : ℕ → ProbabilityTheory.Kernel X3 X3) (hK : ∀ i x, IsFiniteMeasure (KK i x))
    {C : Set SL3} (hC : IsCompact C) :
    Measurable (fun x : X3 => KK (sel G x) x (orbImg U x C)) := by
  have hfun : (fun x : X3 => KK (sel G x) x (orbImg U x C))
      = fun x => ∑' i : ℕ, ({x : X3 | sel G x = i}).indicator (fun _ => (1 : ENNReal)) x
          * KK i x (orbImg U x C) := by
    funext x
    rw [tsum_eq_single (sel G x) (fun i hi => by
      rw [Set.indicator_of_notMem, zero_mul]
      simp only [Set.mem_ofPred_eq]
      exact fun h => hi h.symm)]
    rw [Set.indicator_of_mem (show x ∈ {y : X3 | sel G y = sel G x} from rfl), one_mul]
  rw [hfun]
  refine Measurable.tsum fun i => ?_
  exact (measurable_const.indicator (measurableSet_sel_eq G hG i)).mul
    (measurable_kernel_orbImg hUcl (KK i) (hK i) hC)

/-- Measurability of `x ↦ ∫⁻ t, κ (sel (G x)) x (orbImg U x ({t < f} ∩ B))`. -/
theorem measurable_sel_orbitLintegral {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
    {G : ℕ → Set X3} (hG : ∀ i, MeasurableSet (G i))
    (KK : ℕ → ProbabilityTheory.Kernel X3 X3) (hK : ∀ i x, IsFiniteMeasure (KK i x))
    {h : SL3 → ℝ} (hh : Continuous h) {B : Set SL3}
    (hB : ∃ K : ℕ → Set SL3, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = B) :
    Measurable (fun x : X3 =>
      ∫⁻ t in Set.Ioi (0 : ℝ), KK (sel G x) x (orbImg U x ({g : SL3 | t < h g} ∩ B))) := by
  have hfun : (fun x : X3 =>
        ∫⁻ t in Set.Ioi (0 : ℝ), KK (sel G x) x (orbImg U x ({g : SL3 | t < h g} ∩ B)))
      = fun x => ∑' i : ℕ, ({x : X3 | sel G x = i}).indicator (fun _ => (1 : ENNReal)) x
          * (∫⁻ t in Set.Ioi (0 : ℝ),
              KK i x (orbImg U x ({g : SL3 | t < h g} ∩ B))) := by
    funext x
    rw [tsum_eq_single (sel G x) (fun i hi => by
      rw [Set.indicator_of_notMem, zero_mul]
      simp only [Set.mem_ofPred_eq]
      exact fun h => hi h.symm)]
    rw [Set.indicator_of_mem (show x ∈ {y : X3 | sel G y = sel G x} from rfl), one_mul]
  rw [hfun]
  refine Measurable.tsum fun i => ?_
  exact (measurable_const.indicator (measurableSet_sel_eq G hG i)).mul
    (measurable_orbitLintegral hUcl (KK i) (hK i) hh hB)

/-! ## The lintegral of `nuFull` against a continuous nonnegative test function is measurable -/

theorem measurable_nuFull_lintegral {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
    {μ : Measure X3} [IsProbabilityMeasure μ] [StandardBorelSpace X3]
    (D : FlowerData U μ) {h : SL3 → ℝ} (hh : Continuous h) (hh0 : ∀ g, 0 ≤ h g) :
    Measurable (fun x : X3 => ∫⁻ g, ENNReal.ofReal (h g) ∂(nuFull U μ D.Z D.m D.G x)) := by
  classical
  let KK : ℕ → ℕ → ProbabilityTheory.Kernel X3 X3 := fun k i =>
    cekKernel (μ.restrict (D.Z k i)) ⟨D.m k i⟩ (D.isPlaque k i).1
  have hKKfin : ∀ k i (x : X3), IsFiniteMeasure (KK k i x) := fun k i x =>
    isFiniteMeasure_cekKernel _ _ _ x
  let dd : ℕ → X3 → ENNReal := fun k x => KK k (sel (D.G k) x) x (orbImg U x (Box1 U))
  have hdd : ∀ k, Measurable (dd k) := fun k =>
    measurable_sel_apply hUcl (D.measG k) (KK k) (hKKfin k) (isCompact_box1 U hUcl)
  let AA : ℕ → X3 → ENNReal := fun k x =>
    ∫⁻ t in Set.Ioi (0 : ℝ),
      KK k (sel (D.G k) x) x (orbImg U x ({g : SL3 | t < h g} ∩ piece U k))
  have hAA : ∀ k, Measurable (AA k) := fun k =>
    measurable_sel_orbitLintegral hUcl (D.measG k) (KK k) (hKKfin k) hh
      (exists_isCompact_cover_piece U hUcl k)
  let LT : ℕ → X3 → ENNReal := fun k x =>
    (freeOrbitSet U).indicator (fun _ => (1 : ENNReal)) x * (dd k x)⁻¹ * AA k x
  have hLT : ∀ k, Measurable (LT k) := fun k =>
    ((measurable_const.indicator (measurableSet_freeOrbitSet hUcl)).mul (hdd k).inv).mul (hAA k)
  have hcand : Measurable (fun x : X3 => ∑' k : ℕ, LT k x) := Measurable.tsum hLT
  have hrefK : ∀ (k : ℕ) (x : X3),
      refKernel μ (D.Z k) (D.m k) (D.G k) x = KK k (sel (D.G k) x) x := by
    intro k x
    simp only [refKernel, KK, cekKernel_apply]
  have hpoint : ∀ x : X3, ∫⁻ g, ENNReal.ofReal (h g) ∂(nuFull U μ D.Z D.m D.G x)
      = ∑' k : ℕ, LT k x := by
    intro x
    rw [nuFull, lintegral_sum_measure]
    refine tsum_congr fun k => ?_
    by_cases hxF : x ∈ freeOrbitSet U
    · have hinj : Function.Injective (fun u : U => ((u : SL3) • x)) :=
        (mem_freeOrbitSet_iff U x).mp hxF
      have hpush_apply : pushOrbit U x (KK k (sel (D.G k) x) x) (Box1 U)
          = KK k (sel (D.G k) x) x (orbImg U x (Box1 U)) :=
        pushOrbit_apply_of_injective hUcl hinj (KK k (sel (D.G k) x) x)
          (isCompact_box1 U hUcl).measurableSet
      have hLTx : LT k x = (KK k (sel (D.G k) x) x (orbImg U x (Box1 U)))⁻¹ *
          (∫⁻ t in Set.Ioi (0 : ℝ),
            KK k (sel (D.G k) x) x (orbImg U x ({g : SL3 | t < h g} ∩ piece U k))) := by
        dsimp only [LT, dd, AA]
        rw [Set.indicator_of_mem hxF, one_mul]
      rw [lintegral_nuLevel_restrict hUcl (D.Z k) (D.m k) (D.G k) x k
        (fun g => ENNReal.ofReal (h g))]
      rw [show refPush U μ (D.Z k) (D.m k) (D.G k) x
          = pushOrbit U x (KK k (sel (D.G k) x) x) from by rw [refPush, hrefK k x]]
      rw [pushOrbit_lintegral_eq (U := U) hUcl hinj (KK k (sel (D.G k) x) x) hh hh0
        (measurableSet_piece U hUcl k), hpush_apply, hLTx]
    · have hnotinj : ¬ Function.Injective (fun u : U => ((u : SL3) • x)) := fun hcon =>
        hxF ((mem_freeOrbitSet_iff U x).mpr hcon)
      have hpush0 : refPush U μ (D.Z k) (D.m k) (D.G k) x = 0 := by
        rw [refPush, pushOrbit, Measure.comap_undef (f := fun u : U => ((u : SL3) • x))
          (μ := refKernel μ (D.Z k) (D.m k) (D.G k) x) (fun hcon => hnotinj hcon.1),
          Measure.map_zero]
      have hnu0 : nuLevel U μ (D.Z k) (D.m k) (D.G k) x = 0 := by
        rw [nuLevel, hpush0]
        simp
      have hLTx : LT k x = 0 := by
        dsimp only [LT]
        rw [Set.indicator_of_notMem hxF]
        simp
      rw [hnu0, hLTx]
      simp
  convert hcand using 1
  funext x
  exact hpoint x

/-! ## From `lintegral`-measurability to the Bochner integral -/

lemma ofReal_max_zero (a : ℝ) : ENNReal.ofReal (max a 0) = ENNReal.ofReal a := by
  rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]

/-- If `x ↦ ∫⁻ g, ofReal (h g) ∂(ν x)` is measurable for every continuous nonnegative `h`, then
the Bochner integral `x ↦ ∫ g, f g ∂(ν x)` is measurable.  Off the (measurable) set where `f` is
integrable the Bochner integral is `0` by `integral_undef`. -/
theorem measurable_bochner_of_lintegral {ν : X3 → Measure SL3}
    (f : CompactlySupportedContinuousMap SL3 ℝ)
    (hmeas : ∀ h : SL3 → ℝ, Continuous h → 0 ≤ h →
      Measurable (fun x : X3 => ∫⁻ g, ENNReal.ofReal (h g) ∂(ν x))) :
    Measurable (fun x : X3 => ∫ g, f g ∂(ν x)) := by
  classical
  have hfp : Continuous fun g : SL3 => max (f g) 0 := f.continuous.max continuous_const
  have hfp0 : ∀ g, 0 ≤ max (f g) 0 := fun g => le_max_right _ _
  have hfn : Continuous fun g : SL3 => max (-(f g)) 0 := f.continuous.neg.max continuous_const
  have hfn0 : ∀ g, 0 ≤ max (-(f g)) 0 := fun g => le_max_right _ _
  set A : X3 → ENNReal := fun x => ∫⁻ g, ENNReal.ofReal (max (f g) 0) ∂(ν x) with hAdef
  set B : X3 → ENNReal := fun x => ∫⁻ g, ENNReal.ofReal (max (-(f g)) 0) ∂(ν x) with hBdef
  have hAmeas : Measurable A := hmeas _ hfp hfp0
  have hBmeas : Measurable B := hmeas _ hfn hfn0
  have hpt : ∀ g : SL3, ‖f g‖ₑ
      = ENNReal.ofReal (max (f g) 0) + ENNReal.ofReal (max (-(f g)) 0) := by
    intro g
    by_cases h : 0 ≤ f g
    · rw [max_eq_left h, max_eq_right (by linarith : -(f g) ≤ 0), ENNReal.ofReal_zero, add_zero,
        Real.enorm_eq_ofReal h]
    · have h' : f g ≤ 0 := le_of_not_ge h
      rw [max_eq_right h', max_eq_left (by linarith : 0 ≤ -(f g)), ENNReal.ofReal_zero,
        zero_add, ← enorm_neg (f g), Real.enorm_eq_ofReal (by linarith : (0 : ℝ) ≤ -(f g))]
  have hAB : ∀ x : X3, ∫⁻ g, ‖f g‖ₑ ∂(ν x) = A x + B x := by
    intro x
    have h1 : (∫⁻ g, ‖f g‖ₑ ∂(ν x)) = ∫⁻ g, (ENNReal.ofReal (max (f g) 0)
        + ENNReal.ofReal (max (-(f g)) 0)) ∂(ν x) :=
      lintegral_congr fun g => hpt g
    rw [h1, lintegral_add_left (f := fun g : SL3 => ENNReal.ofReal (max (f g) 0))
      hfp.measurable.ennreal_ofReal]
  have hSmeas : MeasurableSet {x : X3 | ∫⁻ g, ‖f g‖ₑ ∂(ν x) < ⊤} := by
    have hset : {x : X3 | ∫⁻ g, ‖f g‖ₑ ∂(ν x) < ⊤} = {x : X3 | A x + B x < ⊤} := by
      ext x
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hAB x]
    rw [hset]
    exact measurableSet_lt (hAmeas.add hBmeas) measurable_const
  have hiff : ∀ x : X3, Integrable f (ν x) ↔ ∫⁻ g, ‖f g‖ₑ ∂(ν x) < ⊤ := by
    intro x
    rw [MeasureTheory.Integrable, MeasureTheory.HasFiniteIntegral]
    exact ⟨fun h => h.2, fun h => ⟨f.continuous.aestronglyMeasurable, h⟩⟩
  have hsetI : {x : X3 | Integrable f (ν x)} = {x : X3 | ∫⁻ g, ‖f g‖ₑ ∂(ν x) < ⊤} := by
    ext x; exact hiff x
  have hval : ∀ x : X3, ∫ g, f g ∂(ν x)
      = if Integrable f (ν x) then (A x).toReal - (B x).toReal else 0 := by
    intro x
    by_cases hx : Integrable f (ν x)
    · rw [if_pos hx, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hx]
      have e1 : (∫⁻ g, ENNReal.ofReal (f g) ∂(ν x)) = A x := by
        dsimp only [A]
        exact lintegral_congr fun g => (ofReal_max_zero (f g)).symm
      have e2 : (∫⁻ g, ENNReal.ofReal (-(f g)) ∂(ν x)) = B x := by
        dsimp only [B]
        exact lintegral_congr fun g => (ofReal_max_zero (-(f g))).symm
      rw [e1, e2]
    · rw [if_neg hx]
      exact integral_undef hx
  have hfin : Measurable (fun x : X3 =>
      if Integrable f (ν x) then (A x).toReal - (B x).toReal else 0) := by
    refine Measurable.piecewise (s := {x : X3 | Integrable f (ν x)}) ?_ ?_ measurable_const
    · rw [hsetI]; exact hSmeas
    · exact (hAmeas.ennreal_toReal).sub (hBmeas.ennreal_toReal)
  convert hfin using 1
  funext x
  exact hval x

/-- **Measurability of the leafwise field.**  For flower data `D` on `X₃`, the field
`x ↦ ∫ g, f g ∂(nuFull U μ D.Z D.m D.G x)` is measurable for every compactly supported continuous
`f`.  The free-orbit hypothesis is not needed: off the (Borel) set of points with free `U`-orbit
the field vanishes identically, because `pushOrbit` is `Measure.comap` of a non-injective map. -/
theorem leafwise_measurable_field_free {U : Subgroup Work.EKLContract.SL3}
    (hUcl : IsClosed (U : Set Work.EKLContract.SL3))
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    [StandardBorelSpace Work.EKLContract.X3] (D : Work.EKLRelCross.FlowerData U μ)
    (hfree : ∀ᵐ x ∂μ, Function.Injective (fun u : U => (u : Work.EKLContract.SL3) • x))
    (f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ) :
    Measurable (fun x : Work.EKLContract.X3 =>
      ∫ g, f g ∂(Work.EKLRelCross.nuFull U μ D.Z D.m D.G x)) := by
  exact measurable_bochner_of_lintegral (ν := fun x => nuFull U μ D.Z D.m D.G x) f
    (fun h hh hh0 => measurable_nuFull_lintegral hUcl D hh hh0)

end Work.EKLRelCross
