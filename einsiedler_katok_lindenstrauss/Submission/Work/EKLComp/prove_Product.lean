import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLProd.prodFlowerFam_exists_small
import Submission.Work.EKLProd.prodFlower_atom_product
import Submission.Work.EKLProd.prodBox_div_subset_shape_exp
import Submission.Work.EKLProd.sl3EntryBox_compact
import Submission.Work.EKLComp.abs_mul_entry_le
import Submission.Work.EKLGlobal.ProductLocal
import Submission.Work.EKLGlobal.conv_lt_top_of_isCompact
import Submission.Work.EKLGlobal.integrable_comp_mul_prod
import Submission.Work.EKLComp.prove_X3
import Submission.Work.EKLComp.prove_Leafwise
import Submission.Work.EKLComp.prove_Birkhoff

/-!
# C5b — the product structure of leafwise measures (`P_Product`)

This module contains the frozen component C5b,
`Work.EKLContract.P_Product` (Pisa Prop. 8.5 / Cor. 8.8), in its refereed component form
`prove_Product_aux : P_X3 → P_Leafwise → P_Birkhoff → P_Product`, together with the frozen
`prove_Product : P_Product` obtained by applying it to the sibling components.

## The route

The proof is the *globalisation* route described in `EKLComp/ProductPlan.md` §11–§12 and in the
`EKLProd/ProdFlower*` modules:

1. **Geometric input.**  `Work.EKLProd.prodFlowerFam_exists_small` supplies, for every `R₀ ≥ 1`,
   a family `F` of product-box flowers of radius `≥ R₀` whose plaques
   `prodBox T U F.R * (F.co n x)⁻¹` have *unit* displacement on their base:
   `F.co n x = t⁻¹` with `t ∈ Ucl H 1`.
2. **Atom-level product structure.**  `Work.EKLProd.prodFlower_atom_product` gives, for a.e. base
   point `z` of the `n`-th flower, the identity of measures
   `(νH z) ↾ shape = c · (conv νT νU) ↾ shape`, `c > 0`, restricted to the *shape* of the flower
   (the restriction on both sides is essential: `shape` lies in the proper closed subgroup `H`,
   so the corresponding statement with test functions supported in a shape would be vacuous).
3. **Growing shapes.**  At a base point the shape contains the product box of radius
   `F.R / 10⁹` (`Work.EKLProd.prodBox_div_subset_shape_exp`, an explicit-constant form of
   `prodBox_div_subset_shape`).  Taking flowers of radius `≥ 10⁹ (k+1)` therefore produces, for
   `μ`-a.e. `z` and every `k`, the box identity
   `(νH z) ↾ pBox T U (k+1) = c · (conv νT νU) ↾ pBox T U (k+1)`,
   where `pBox T U R = prodBox T U R` and `conv νT νU = (νT ⊗ νU) ↾ mul` is the convolution.
4. **Reduction.**  `Work.EKLGlobal.frozen_of_box_identities` turns the box identities for all
   radii (and the finiteness/positivity of the unit box, the a.e. carriedness of the systems and
   the a.e. integrability of the test functions) into the frozen test-function form.  The
   ingredients at a fixed `z` are: the constants agree, since two product boxes meet in a set of
   positive `conv`-mass; the boxes exhaust `H`, so the identity propagates to all Borel sets by
   continuity from below; and the test-function statement follows by
   `integral_smul_measure` together with Fubini for the convolution
   (`Work.EKLGlobal.integral_conv`).

The auxiliary facts proved here are the relative compactness of the unit product box and the
a.e. integrability of the composed test functions (from
`Work.EKLGlobal.integrable_comp_mul_prod`).
-/

open MeasureTheory Topology Filter
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLComp

open Work.EKLContract
open Work.EKLGlobal (pBox conv)

/-! ## Auxiliary: relative compactness of the unit product box

The product box of radius one is an entrywise bounded subset of `SL₃(ℝ)`, hence contained in a
compact set.  This is what makes the convolution of two locally finite measures finite on it. -/

theorem pBox_one_subset_entryBox {T U : Subgroup SL3} :
    pBox T U 1 ⊆ {g : SL3 | ∀ i j : Fin 3, |g i j| ≤ 12} := by
  rintro g ⟨a, ⟨haV, -⟩, b, ⟨hbV, -⟩, rfl⟩ i j
  have hbdd : ∀ (c : SL3), c ∈ V 1 → ∀ i j : Fin 3, |c i j| ≤ 2 := by
    intro c hc i j
    have hone : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
      rw [Matrix.one_apply]
      split <;> simp
    have hlt : |c i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < 1 := hc i j
    calc |c i j|
        = |(c i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
            + (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by congr 1; ring
      _ ≤ |c i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
            + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_add_le _ _
      _ ≤ 2 := by linarith
  have h := Work.EKLComp.abs_mul_entry_le (A := (a : Matrix (Fin 3) (Fin 3) ℝ))
    (B := (b : Matrix (Fin 3) (Fin 3) ℝ)) (C := 2) (η := 2) (by norm_num) (by norm_num)
    (hbdd a haV) (hbdd b hbV) i j
  calc |(a * b) i j|
      = |((a : Matrix (Fin 3) (Fin 3) ℝ) * (b : Matrix (Fin 3) (Fin 3) ℝ)) i j| := by
        simp [Matrix.SpecialLinearGroup.coe_mul]
    _ ≤ 3 * 2 * 2 := h
    _ ≤ 12 := by norm_num

theorem pBox_one_subset_compact {T U : Subgroup SL3} :
    ∃ K : Set SL3, IsCompact K ∧ pBox T U 1 ⊆ K := by
  refine ⟨{g : SL3 | ∀ i j : Fin 3, -(12 : ℝ) ≤ g i j ∧ g i j ≤ 12}, ?_, ?_⟩
  · exact Work.EKLProd.sl3EntryBox_compact (fun _ _ => -12) (fun _ _ => 12)
  · refine subset_trans pBox_one_subset_entryBox ?_
    intro g hg i j
    exact ⟨neg_le_of_abs_le (hg i j), le_of_abs_le (hg i j)⟩

/-! ## The component -/

/-- **C5b — product structure** (Pisa Prop. 8.5 / Cor. 8.8), in the refereed component form. -/
theorem prove_Product_aux (hX3 : P_X3) (hLeaf : P_Leafwise) (hBirk : P_Birkhoff) : P_Product := by
  intro μ hμprob hA H T U hH hT hU hTH hUH hsplit hnorm hcop hdisj νH νT νU XH XT XU hνH hνT hνU
  obtain ⟨t₀, hcent, hcontr⟩ := hsplit
  have hHc : IsClosed (H : Set SL3) := hH.1
  have hTc : IsClosed (T : Set SL3) := hT.1
  have hUc : IsClosed (U : Set SL3) := hU.1
  -- (0) a.e. integrability of the composed test functions
  have hint : ∀ᵐ z ∂μ, ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      Integrable (fun p : SL3 × SL3 => f (p.1 * p.2)) ((νT z).prod (νU z)) := by
    filter_upwards [ae_iff.mpr hνT.conull, ae_iff.mpr hνU.conull] with z hXTz hXUz
    haveI hfinT : IsFiniteMeasureOnCompacts (νT z) := hνT.radon z hXTz
    haveI hfinU : IsFiniteMeasureOnCompacts (νU z) := hνU.radon z hXUz
    intro f
    exact Work.EKLGlobal.integrable_comp_mul_prod hTH hUH hnorm hcop hdisj hHc hTc hUc
      (fun K hK => IsFiniteMeasureOnCompacts.lt_top_of_isCompact hK)
      (fun K hK => IsFiniteMeasureOnCompacts.lt_top_of_isCompact hK)
      (hνT.carried z hXTz) (hνU.carried z hXUz) f
  -- (1) the atom-level product structure of growing flowers gives box identities
  have hbox : ∀ᵐ z ∂μ, ∀ k : ℕ, ∃ c : ℝ, 0 < c ∧
      (νH z).restrict (pBox T U ((k : ℝ) + 1)) =
        ENNReal.ofReal c • (conv (νT z) (νU z)).restrict (pBox T U ((k : ℝ) + 1)) := by
    classical
    rw [ae_all_iff]
    intro k
    rw [MeasureTheory.ae_iff]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hR₀ : (1 : ℝ) ≤ (10 : ℝ) ^ 9 * ((k : ℝ) + 1) := by
      have h10 : (1 : ℝ) ≤ (10 : ℝ) ^ 9 := by norm_num
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (10 : ℝ) ^ 9 * ((k : ℝ) + 1) := mul_le_mul h10 hk1 (by norm_num) (by positivity)
    obtain ⟨F, hFR, hFco⟩ :=
      Work.EKLProd.prodFlowerFam_exists_small hX3 hH hT hU hTH hUH hnorm hcop hdisj hA
        ((10 : ℝ) ^ 9 * ((k : ℝ) + 1)) hR₀
    have hper : ∀ n : ℕ, μ ({z : X3 | ¬ (∃ c : ℝ, 0 < c ∧
        (νH z).restrict (pBox T U ((k : ℝ) + 1)) =
          ENNReal.ofReal c • (conv (νT z) (νU z)).restrict (pBox T U ((k : ℝ) + 1)))} ∩ F.G n)
        = 0 := by
      intro n
      have hAt := Work.EKLProd.prodFlower_atom_product hX3 hLeaf hBirk hH hT hU hTH hUH hnorm
        hcop hdisj hA hνH hνT hνU t₀ hcent hcontr F n
      have hZmeas : MeasurableSet (F.Z n) := (F.plaqH n).1 _ (F.plaqH n).2.2.1
      have hAt' : μ (F.Z n ∩ {z : X3 | ¬ (∃ c : ℝ, 0 < c ∧
          (νH z).restrict (shape (F.mH n) H z) =
            ENNReal.ofReal c • (conv (νT z) (νU z)).restrict (shape (F.mH n) H z))}) = 0 := by
        have h := MeasureTheory.ae_iff.mp hAt
        rwa [Measure.restrict_apply' hZmeas, Set.inter_comm] at h
      refine measure_mono_null ?_ hAt'
      intro z hz
      refine ⟨F.GZ n hz.2, ?_⟩
      intro hatom
      obtain ⟨t, ht1, htco⟩ := hFco n z hz.2
      obtain ⟨c, hc, hE⟩ := hatom
      refine hz.1 ⟨c, hc, ?_⟩
      have hRbig : 5000 ≤ F.R := by
        have hprod : (10 : ℝ) ^ 9 * 1 ≤ (10 : ℝ) ^ 9 * ((k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hk1 (by positivity)
        have h10 : (5000 : ℝ) ≤ (10 : ℝ) ^ 9 := by norm_num
        linarith
      have hle : (k : ℝ) + 1 ≤ F.R / (10 : ℝ) ^ 9 := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < (10 : ℝ) ^ 9)]
        linarith [hFR, mul_comm ((k : ℝ) + 1) ((10 : ℝ) ^ 9)]
      have hsub : pBox T U ((k : ℝ) + 1) ⊆ shape (F.mH n) H z :=
        subset_trans (Work.EKLGlobal.prodBox_mono hle)
          (Work.EKLProd.prodBox_div_subset_shape_exp hTH hUH hnorm hcop hdisj t₀ hcent hcontr
            F hRbig n (F.GZ n hz.2) ht1 htco)
      have hmeas : MeasurableSet (pBox T U ((k : ℝ) + 1)) :=
        Work.EKLGlobal.measurableSet_prodBox hTH hUH hnorm hcop hdisj hHc hTc hUc _
      calc (νH z).restrict (pBox T U ((k : ℝ) + 1))
          = ((νH z).restrict (shape (F.mH n) H z)).restrict (pBox T U ((k : ℝ) + 1)) := by
            rw [Measure.restrict_restrict hmeas, Set.inter_eq_self_of_subset_left hsub]
        _ = (ENNReal.ofReal c • (conv (νT z) (νU z)).restrict (shape (F.mH n) H z)).restrict
              (pBox T U ((k : ℝ) + 1)) := by rw [hE]
        _ = ENNReal.ofReal c • ((conv (νT z) (νU z)).restrict (shape (F.mH n) H z)).restrict
              (pBox T U ((k : ℝ) + 1)) := by rw [Measure.restrict_smul]
        _ = ENNReal.ofReal c • (conv (νT z) (νU z)).restrict (pBox T U ((k : ℝ) + 1)) := by
            rw [Measure.restrict_restrict hmeas, Set.inter_eq_self_of_subset_left hsub]
    refine measure_mono_null ?_ (measure_union_null (measure_iUnion_null hper) F.cover)
    intro z hz
    by_cases h : z ∈ ⋃ n, F.G n
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
      exact Or.inl (Set.mem_iUnion.mpr ⟨n, hz, hn⟩)
    · exact Or.inr h
  -- (2) the pointwise conclusion, by the reduction `frozen_of_box_identities`
  filter_upwards [hbox, ae_iff.mpr hνH.conull, ae_iff.mpr hνT.conull, ae_iff.mpr hνU.conull,
    hint] with z hboxz hXHz hXTz hXUz hintz
  haveI hTfin : IsFiniteMeasureOnCompacts (νT z) := hνT.radon z hXTz
  haveI hUfin : IsFiniteMeasureOnCompacts (νU z) := hνU.radon z hXUz
  haveI hTloc : IsLocallyFiniteMeasure (νT z) := inferInstance
  haveI hUloc : IsLocallyFiniteMeasure (νU z) := inferInstance
  haveI hTsig : SigmaFinite (νT z) := MeasureTheory.sigmaFinite_of_locallyFinite
  haveI hUsig : SigmaFinite (νU z) := MeasureTheory.sigmaFinite_of_locallyFinite
  have hTcar : νT z (T : Set SL3)ᶜ = 0 := hνT.carried z hXTz
  have hUcar : νU z (U : Set SL3)ᶜ = 0 := hνU.carried z hXUz
  have hcarH : νH z (H : Set SL3)ᶜ = 0 := hνH.carried z hXHz
  -- the unit product box has positive and finite `conv`-mass
  have hpos : 0 < conv (νT z) (νU z) (pBox T U 1) := by
    have hδ : (0 : ℝ) < 1 / 8 := by norm_num
    have hTpos : 0 < νT z (V (1 / 8) ∩ (T : Set SL3)) := by
      have h1 : νT z (V (1 / 8) ∩ (T : Set SL3)) + νT z (V (1 / 8) \ (T : Set SL3))
          = νT z (V (1 / 8)) := measure_inter_add_sdiff _ hTc.measurableSet
      have h2 : νT z (V (1 / 8) \ (T : Set SL3)) = 0 :=
        measure_mono_null (fun x hx => hx.2) hTcar
      have h3 : νT z (V (1 / 8) ∩ (T : Set SL3)) = νT z (V (1 / 8)) := by
        rw [← h1, h2, add_zero]
      rw [h3]
      exact hνT.pos z hXTz (1 / 8) hδ
    have hUpos : 0 < νU z (V (1 / 8) ∩ (U : Set SL3)) := by
      have h1 : νU z (V (1 / 8) ∩ (U : Set SL3)) + νU z (V (1 / 8) \ (U : Set SL3))
          = νU z (V (1 / 8)) := measure_inter_add_sdiff _ hUc.measurableSet
      have h2 : νU z (V (1 / 8) \ (U : Set SL3)) = 0 :=
        measure_mono_null (fun x hx => hx.2) hUcar
      have h3 : νU z (V (1 / 8) ∩ (U : Set SL3)) = νU z (V (1 / 8)) := by
        rw [← h1, h2, add_zero]
      rw [h3]
      exact hνU.pos z hXUz (1 / 8) hδ
    have hsub : ((V (1 / 8) ∩ (T : Set SL3)) ×ˢ (V (1 / 8) ∩ (U : Set SL3)))
        ⊆ (fun p : SL3 × SL3 => p.1 * p.2) ⁻¹' (pBox T U 1) := by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      exact ⟨a, ⟨Work.EKLGlobal.V_mono_local (by norm_num) ha.1, ha.2⟩, b,
        ⟨Work.EKLGlobal.V_mono_local (by norm_num) hb.1, hb.2⟩, rfl⟩
    have hmul : Measurable (fun p : SL3 × SL3 => p.1 * p.2) := by fun_prop
    have hP1 : MeasurableSet (pBox T U 1) :=
      Work.EKLGlobal.measurableSet_prodBox hTH hUH hnorm hcop hdisj hHc hTc hUc 1
    rw [conv, Measure.map_apply hmul hP1]
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Measure.prod_prod]
    exact ENNReal.mul_pos hTpos.ne' hUpos.ne'
  have hbdd : conv (νT z) (νU z) (pBox T U 1) < ⊤ := by
    obtain ⟨K, hKc, hKsub⟩ := pBox_one_subset_compact (T := T) (U := U)
    exact lt_of_le_of_lt (measure_mono hKsub)
      (Work.EKLGlobal.conv_lt_top_of_isCompact hTH hUH hnorm hcop hdisj hHc hTc hUc
        (fun K hK => IsFiniteMeasureOnCompacts.lt_top_of_isCompact hK)
        (fun K hK => IsFiniteMeasureOnCompacts.lt_top_of_isCompact hK) hTcar hUcar hKc)
  -- integer box identities give the box identity for every real radius
  have hbox' : ∀ R : ℝ, 1 ≤ R → ∃ c : ℝ, 0 < c ∧ (νH z).restrict (pBox T U R)
      = ENNReal.ofReal c • (conv (νT z) (νU z)).restrict (pBox T U R) := by
    intro R hR
    obtain ⟨c, hc, hident⟩ := hboxz (Nat.ceil R)
    refine ⟨c, hc, ?_⟩
    have hle : R ≤ ((Nat.ceil R : ℕ) : ℝ) + 1 := by
      have := Nat.le_ceil R
      linarith
    have hsub : pBox T U R ⊆ pBox T U (((Nat.ceil R : ℕ) : ℝ) + 1) :=
      Work.EKLGlobal.prodBox_mono hle
    have hmeas : MeasurableSet (pBox T U R) :=
      Work.EKLGlobal.measurableSet_prodBox hTH hUH hnorm hcop hdisj hHc hTc hUc R
    calc (νH z).restrict (pBox T U R)
        = ((νH z).restrict (pBox T U (((Nat.ceil R : ℕ) : ℝ) + 1))).restrict (pBox T U R) := by
          rw [Measure.restrict_restrict hmeas, Set.inter_eq_self_of_subset_left hsub]
      _ = (ENNReal.ofReal c • (conv (νT z) (νU z)).restrict
            (pBox T U (((Nat.ceil R : ℕ) : ℝ) + 1))).restrict (pBox T U R) := by rw [hident]
      _ = ENNReal.ofReal c • ((conv (νT z) (νU z)).restrict
            (pBox T U (((Nat.ceil R : ℕ) : ℝ) + 1))).restrict (pBox T U R) := by
          rw [Measure.restrict_smul]
      _ = ENNReal.ofReal c • (conv (νT z) (νU z)).restrict (pBox T U R) := by
          rw [Measure.restrict_restrict hmeas, Set.inter_eq_self_of_subset_left hsub]
  exact Work.EKLGlobal.frozen_of_box_identities hTH hUH hnorm hcop hdisj hHc hTc hUc hTcar hUcar
    hcarH hbdd hpos hbox' hintz

/-- The frozen component statement of `Defs.lean`: `prove_Product_aux` applied to the sibling
components. -/
theorem prove_Product : Work.EKLContract.P_Product :=
  prove_Product_aux prove_X3 prove_Leafwise prove_Birkhoff

end Work.EKLComp
