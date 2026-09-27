import Mathlib
import Submission.Work.EKLProd.BoxFlowerLocal
import Submission.Work.EKLGlobal.BadRatio

/-!
# From local box identities to the frozen product structure

Let `H = T·U` be a horospherical subgroup with the side conditions of the frozen component
`P_Product`, and let `νH`, `νT`, `νU` be leafwise measures of an `A`-invariant `μ`.

This module proves the **final measure-theoretic step** of C5b: if the `H`-system `νH` agrees,
up to a positive constant, with the convolution `conv νT νU := mul_* (νT ⊗ νU)` of the `T`- and
`U`-systems on every product box `pBox T U R` (`R ≥ 1`), then the frozen conclusion

`∀ f : C_c(SL₃, ℝ), ∫ f ∂νH = c * ∫ t, ∫ u, f (t*u) ∂νU ∂νT`

of `Work.EKLContract.P_Product` holds with a single constant `c > 0`.

The point is that `⋃_{R} pBox T U R = H` (the boxes of unbounded radius exhaust the leaf), so the
box identities determine the measures: the constants agree because two boxes always meet in a set
of positive `conv`-mass, and the identity propagates to all Borel sets by continuity from below
(`tendsto_measure_iUnion_atTop`).  No test-function approximation is needed; the frozen
test-function statement follows from the *measure* identity by `integral_smul_measure` and Fubini
for the convolution (`Work.EKLGlobal.integral_conv`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLGlobal

open Work.EKLContract

/-- The product box of `T` and `U` of radius `R` (notation for `Work.EKLProd.prodBox`). -/
abbrev pBox (T U : Subgroup SL3) (R : ℝ) : Set SL3 := Work.EKLProd.prodBox T U R

/-- `V` is monotone in the radius. -/
theorem V_mono_local {R R' : ℝ} (h : R ≤ R') : V R ⊆ V R' := fun g hg i j =>
  lt_of_lt_of_le (hg i j) h

/-- The product box `pBox T U R` is monotone in the radius. -/
theorem prodBox_mono {T U : Subgroup SL3} {R R' : ℝ} (h : R ≤ R') :
    pBox T U R ⊆ pBox T U R' := by
  rintro g ⟨a, ha, b, hb, rfl⟩
  exact ⟨a, ⟨V_mono_local h ha.1, ha.2⟩, b, ⟨V_mono_local h hb.1, hb.2⟩, rfl⟩

/-- `pBox T U R` is Borel (it is the trace on the closed subgroup `H` of an open set). -/
theorem measurableSet_prodBox {H T U : Subgroup SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3))
    (R : ℝ) : MeasurableSet (pBox T U R) := by
  obtain ⟨N, hNopen, hNH⟩ :=
    Work.EKLProd.exists_open_inter_prodBox hTH hUH hnorm hcop hdisj hHc hTc hUc (R := R)
  change MeasurableSet (Work.EKLProd.prodBox T U R)
  rw [← hNH]
  exact hNopen.measurableSet.inter hHc.measurableSet

/-- **The product boxes exhaust `H`**: every element of `H` lies in `pBox T U R` for some
`R ≥ 1`. -/
theorem iUnion_prodBox_eq {H T U : Subgroup SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) :
    (⋃ k : ℕ, pBox T U ((k : ℝ) + 1)) = (H : Set SL3) := by
  ext h
  constructor
  · intro hh
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hh
    exact Work.EKLProd.prodBox_subset_H hTH hUH hk
  · intro hh
    obtain ⟨t, htT, u, huU, rfl⟩ := hcop h hh
    set D : ℝ := (∑ i : Fin 3, ∑ j : Fin 3, |t i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|)
        + (∑ i : Fin 3, ∑ j : Fin 3, |u i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|) + 1 with hD
    have hDt : ∀ i j : Fin 3, |t i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < D := by
      intro i j
      have h1 : |t i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
          ≤ ∑ j' : Fin 3, |t i j' - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j'| :=
        Finset.single_le_sum (s := Finset.univ)
          (f := fun j' : Fin 3 => |t i j' - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j'|)
          (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
      have h2 : (∑ j' : Fin 3, |t i j' - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j'|)
          ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, |t i' j' - (1 : Matrix (Fin 3) (Fin 3) ℝ) i' j'| :=
        Finset.single_le_sum (s := Finset.univ)
          (f := fun i' : Fin 3 => ∑ j' : Fin 3, |t i' j' - (1 : Matrix (Fin 3) (Fin 3) ℝ) i' j'|)
          (fun i' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _) (Finset.mem_univ i)
      have h3 : (0:ℝ)
          ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, |u i' j' - (1 : Matrix (Fin 3) (Fin 3) ℝ) i' j'| :=
        Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _
      rw [hD]
      linarith
    have hDu : ∀ i j : Fin 3, |u i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < D := by
      intro i j
      have h1 : |u i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
          ≤ ∑ j' : Fin 3, |u i j' - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j'| :=
        Finset.single_le_sum (s := Finset.univ)
          (f := fun j' : Fin 3 => |u i j' - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j'|)
          (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
      have h2 : (∑ j' : Fin 3, |u i j' - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j'|)
          ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, |u i' j' - (1 : Matrix (Fin 3) (Fin 3) ℝ) i' j'| :=
        Finset.single_le_sum (s := Finset.univ)
          (f := fun i' : Fin 3 => ∑ j' : Fin 3, |u i' j' - (1 : Matrix (Fin 3) (Fin 3) ℝ) i' j'|)
          (fun i' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _) (Finset.mem_univ i)
      have h3 : (0:ℝ)
          ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, |t i' j' - (1 : Matrix (Fin 3) (Fin 3) ℝ) i' j'| :=
        Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _
      rw [hD]
      linarith
    refine Set.mem_iUnion.mpr ⟨Nat.ceil D, ?_⟩
    have hle : D ≤ ((Nat.ceil D : ℝ) + 1) := by
      have := Nat.le_ceil D
      linarith
    exact ⟨t, ⟨fun i j => lt_of_lt_of_le (hDt i j) hle, htT⟩,
      u, ⟨fun i j => lt_of_lt_of_le (hDu i j) hle, huU⟩, rfl⟩

/-! ## The reduction -/

/-- **The frozen product structure from box identities.**  If the two measures `νH` and
`conv νT νU` agree up to a positive constant on every product box `pBox T U R` (`R ≥ 1`),
then they agree globally up to a positive constant, in the test-function form of the frozen
component `P_Product`. -/
theorem frozen_of_box_identities
    {H T U : Subgroup SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3))
    {νH νT νU : Measure SL3}
    (hcarT : νT (T : Set SL3)ᶜ = 0) (hcarU : νU (U : Set SL3)ᶜ = 0)
    (hcarH : νH (H : Set SL3)ᶜ = 0)
    (hbdd : conv νT νU (pBox T U 1) < ⊤)
    (hpos : 0 < conv νT νU (pBox T U 1))
    (hbox : ∀ R : ℝ, 1 ≤ R → ∃ c : ℝ, 0 < c ∧
      νH.restrict (pBox T U R) = ENNReal.ofReal c • (conv νT νU).restrict (pBox T U R))
    [SFinite νT] [SFinite νU]
    (hint : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      Integrable (fun p : SL3 × SL3 => f (p.1 * p.2)) (νT.prod νU)) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      ∫ g, f g ∂νH = c * ∫ g, (∫ u, f (g * u) ∂νU) ∂νT := by
  classical
  have hP : ∀ R : ℝ, MeasurableSet (pBox T U R) := fun R =>
    measurableSet_prodBox hTH hUH hnorm hcop hdisj hHc hTc hUc R
  -- ## Step 1: the constants agree
  obtain ⟨c1, hc1, hid1⟩ := hbox 1 le_rfl
  have hconst : ∀ {R : ℝ} (hR : 1 ≤ R) {c : ℝ}, 0 < c →
      νH.restrict (pBox T U R) = ENNReal.ofReal c • (conv νT νU).restrict (pBox T U R) →
      c = c1 := by
    intro R hR c hc hid
    have hsub : pBox T U 1 ⊆ pBox T U R := prodBox_mono hR
    have hX0 : conv νT νU (pBox T U 1) ≠ 0 := ne_of_gt hpos
    have hXinf : conv νT νU (pBox T U 1) ≠ ⊤ := ne_of_lt hbdd
    have h1R : (νH.restrict (pBox T U R)) (pBox T U 1) = νH (pBox T U 1) := by
      rw [Measure.restrict_apply (hP 1), Set.inter_eq_self_of_subset_left hsub]
    have h2R : (conv νT νU).restrict (pBox T U R) (pBox T U 1) = conv νT νU (pBox T U 1) := by
      rw [Measure.restrict_apply (hP 1), Set.inter_eq_self_of_subset_left hsub]
    have h11 : (νH.restrict (pBox T U 1)) (pBox T U 1) = νH (pBox T U 1) := by
      rw [Measure.restrict_apply (hP 1), Set.inter_self]
    have h21 : (conv νT νU).restrict (pBox T U 1) (pBox T U 1) = conv νT νU (pBox T U 1) := by
      rw [Measure.restrict_apply (hP 1), Set.inter_self]
    have e1 : νH (pBox T U 1) = ENNReal.ofReal c1 * conv νT νU (pBox T U 1) := by
      have h := congrArg (fun μ : Measure SL3 => μ (pBox T U 1)) hid1
      rw [h11, Measure.smul_apply, smul_eq_mul, h21] at h
      exact h
    have e2 : νH (pBox T U 1) = ENNReal.ofReal c * conv νT νU (pBox T U 1) := by
      have h := congrArg (fun μ : Measure SL3 => μ (pBox T U 1)) hid
      rw [h1R, Measure.smul_apply, smul_eq_mul, h2R] at h
      exact h
    have hE : ENNReal.ofReal c1 = ENNReal.ofReal c :=
      (ENNReal.mul_left_inj hX0 hXinf).mp (e1.symm.trans e2)
    have hto : c1 = c := by
      have := congrArg ENNReal.toReal hE
      rw [ENNReal.toReal_ofReal (le_of_lt hc1), ENNReal.toReal_ofReal (le_of_lt hc)] at this
      exact this
    exact hto.symm
  have hbox' : ∀ R : ℝ, 1 ≤ R →
      νH.restrict (pBox T U R) = ENNReal.ofReal c1 • (conv νT νU).restrict (pBox T U R) := by
    intro R hR
    obtain ⟨c, hc, hid⟩ := hbox R hR
    rw [hid, hconst hR hc hid]
  -- ## Step 2: the `conv`-measure is carried by `H`
  have hconvH : conv νT νU ((H : Set SL3)ᶜ) = 0 := by
    have hsub : ((fun p : SL3 × SL3 => p.1 * p.2) ⁻¹' ((H : Set SL3)ᶜ))
        ⊆ (((T : Set SL3) ×ˢ (U : Set SL3))ᶜ) := by
      rintro ⟨a, b⟩ hab ⟨haT, hbU⟩
      exact hab (H.mul_mem (hTH haT) (hUH hbU))
    have hzero : (νT.prod νU) (((T : Set SL3) ×ˢ (U : Set SL3))ᶜ) = 0 := by
      have hset : (((T : Set SL3) ×ˢ (U : Set SL3))ᶜ : Set (SL3 × SL3))
          = ((T : Set SL3)ᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ ((U : Set SL3)ᶜ)) := by
        ext p
        simp only [Set.mem_compl_iff, Set.mem_prod, Set.mem_univ, and_true, true_and,
          Set.mem_union, not_and_or]
      rw [hset]
      refine measure_union_null ?_ ?_
      · rw [MeasureTheory.Measure.prod_prod, hcarT]; simp
      · rw [MeasureTheory.Measure.prod_prod, hcarU]; simp
    rw [conv, Measure.map_apply (by fun_prop) hHc.measurableSet.compl]
    exact measure_mono_null hsub hzero
  -- ## Step 3: the measure identity on all Borel sets
  have hmeasure : ∀ B : Set SL3, MeasurableSet B → νH B = ENNReal.ofReal c1 * conv νT νU B := by
    intro B hB
    have hBH : νH B = νH (B ∩ H) := by
      have h1 : νH (B ∩ H) + νH (B \ H) = νH B := measure_inter_add_sdiff B hHc.measurableSet
      have h2 : νH (B \ H) = 0 := measure_mono_null (fun x hx => hx.2) hcarH
      rw [← h1, h2, add_zero]
    have hCH : conv νT νU B = conv νT νU (B ∩ H) := by
      have h1 : conv νT νU (B ∩ H) + conv νT νU (B \ H) = conv νT νU B :=
        measure_inter_add_sdiff B hHc.measurableSet
      have h2 : conv νT νU (B \ H) = 0 := measure_mono_null (fun x hx => hx.2) hconvH
      rw [← h1, h2, add_zero]
    rw [hBH, hCH]
    -- continuity from below along the exhausting boxes
    have hmono : Monotone (fun k : ℕ => pBox T U ((k : ℝ) + 1)) := by
      intro k l hkl
      refine prodBox_mono ?_
      have : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
      linarith
    have hUn : (⋃ k : ℕ, pBox T U ((k : ℝ) + 1)) = (H : Set SL3) :=
      iUnion_prodBox_eq hTH hUH hcop
    have hmonoN : Monotone (fun k : ℕ => (B ∩ (H : Set SL3)) ∩ pBox T U ((k : ℝ) + 1)) := by
      intro k l hkl x hx
      exact ⟨hx.1, hmono hkl hx.2⟩
    have hUN : (⋃ k : ℕ, (B ∩ (H : Set SL3)) ∩ pBox T U ((k : ℝ) + 1)) = B ∩ (H : Set SL3) := by
      ext x
      constructor
      · intro hx
        exact (Set.mem_iUnion.mp hx).choose_spec.1
      · intro hx
        have hx' : x ∈ ⋃ k : ℕ, pBox T U ((k : ℝ) + 1) := by rw [hUn]; exact hx.2
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx'
        exact Set.mem_iUnion.mpr ⟨k, hx, hk⟩
    have hNH : Tendsto (fun k : ℕ => νH ((B ∩ (H : Set SL3)) ∩ pBox T U ((k : ℝ) + 1)))
        atTop (𝓝 (νH (B ∩ (H : Set SL3)))) := by
      have h := tendsto_measure_iUnion_atTop (μ := νH) hmonoN
      rw [hUN] at h
      exact h
    have hCH2 : Tendsto (fun k : ℕ =>
        conv νT νU ((B ∩ (H : Set SL3)) ∩ pBox T U ((k : ℝ) + 1)))
        atTop (𝓝 (conv νT νU (B ∩ (H : Set SL3)))) := by
      have h := tendsto_measure_iUnion_atTop (μ := conv νT νU) hmonoN
      rw [hUN] at h
      exact h
    have hstep : ∀ k : ℕ, νH ((B ∩ (H : Set SL3)) ∩ pBox T U ((k : ℝ) + 1))
        = ENNReal.ofReal c1 * conv νT νU ((B ∩ (H : Set SL3)) ∩ pBox T U ((k : ℝ) + 1)) := by
      intro k
      have hR : (1:ℝ) ≤ (k : ℝ) + 1 := by
        have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      set C : Set SL3 := (B ∩ (H : Set SL3)) ∩ pBox T U ((k : ℝ) + 1) with hC
      have hmeas : MeasurableSet C := (hB.inter hHc.measurableSet).inter (hP _)
      have hsub : C ⊆ pBox T U ((k : ℝ) + 1) := Set.inter_subset_right
      have h1 : (νH.restrict (pBox T U ((k : ℝ) + 1))) C = νH C := by
        rw [Measure.restrict_apply hmeas, Set.inter_eq_self_of_subset_left hsub]
      have h2 : (conv νT νU).restrict (pBox T U ((k : ℝ) + 1)) C = conv νT νU C := by
        rw [Measure.restrict_apply hmeas, Set.inter_eq_self_of_subset_left hsub]
      have h := congrArg (fun μ : Measure SL3 => μ C) (hbox' ((k : ℝ) + 1) hR)
      rw [h1, Measure.smul_apply, smul_eq_mul, h2] at h
      exact h
    have h2 : Tendsto (fun k : ℕ => νH ((B ∩ (H : Set SL3)) ∩ pBox T U ((k : ℝ) + 1)))
        atTop (𝓝 (ENNReal.ofReal c1 * conv νT νU (B ∩ (H : Set SL3)))) :=
      Filter.Tendsto.congr (fun k => (hstep k).symm)
        (ENNReal.Tendsto.const_mul hCH2 (Or.inr ENNReal.ofReal_ne_top))
    exact tendsto_nhds_unique hNH h2
  -- ## Step 4: the test-function statement
  refine ⟨c1, hc1, fun f => ?_⟩
  have hcong : νH = ENNReal.ofReal c1 • conv νT νU := Measure.ext hmeasure
  rw [hcong, integral_smul_measure, smul_eq_mul, ENNReal.toReal_ofReal (le_of_lt hc1),
    integral_conv f (hint f)]

end Work.EKLGlobal
