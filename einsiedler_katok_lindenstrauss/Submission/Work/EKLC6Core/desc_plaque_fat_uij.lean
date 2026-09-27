import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.cutAssembly
import Submission.Work.EKLC6Core.cutHDefs
import Submission.Work.EKLC6Core.cutHCutData
import Submission.Work.EKLC6Core.cutCodeZ
import Submission.Work.EKLC6Core.cutHMargin
import Submission.Work.EKLC6Core.cut_margin_at_depth
import Submission.Work.EKLC6Core.measure_iUnion_preimage_shellThin
import Submission.Work.EKLC6Core.shape_pastSig_eq
import Submission.Work.EKLContract.Lemmas.isHoro_Uij
import Submission.Work.EKLContract.Lemmas.Uij_range
import Submission.Work.EKLContract.Lemmas.Box1_Uij

/-!
# `Work.EKLC6Core.desc_plaque_fat_uij`

The *uniformly fat* form of L1 of component C6 (Pisa 7.37/7.38) for a root subgroup `U_ij`
contracted by the diagonal flow (`t i < t j`): for every probability measure `μ` on
`X₃ = SL₃(ℝ)/SL₃(ℤ)` preserved by `x ↦ aDiag t · x` and every `ε > 0` there are a countably
generated σ-algebra `A`, a set `Z` with `μ Zᶜ < ε`, and constants `0 < c < C` such that

* `A = descSig t (MCut S O)` is a plaque algebra for `U_ij` on `Z` (frozen `IsPlaqueAlgebra`)
  and is `aDiag t`-decreasing, and
* at every `x ∈ Z` the `U_ij`-shape is sandwiched between two *windows* of the root coordinate,

  `u_ij '' Icc (s₀ - c) (s₀ + c) ⊆ shape A (U_ij) x ⊆ u_ij '' Icc (s₀ - C) (s₀ + C)`,

with `c`, `C` uniform over `x ∈ Z` (only the centre `s₀` depends on `x`).

## Proof

Rerun the cut construction of `Work.EKLC6Core.exists_desc_subordinate` for `U = U_ij`, but with
the good set strengthened so that the *shell margin holds at every level* `n ≥ 0`:

`G = H ∩ {x | ∀ n, φⁿ x ∉ shellThin S (D μ₀ⁿ)}`,  `D = 20 b`,

and take its Borel core `H'' = (toMeasurable μ Gᶜ)ᶜ`, so `μ H''ᶜ < ofReal (3η) < ε`.  The Borel
core costs the summable geometric loss `C₁ · 20 b / (1 - μ₀)`, made arbitrarily small by the free
parameter `b`; the pay-off is that `Work.EKLC6Core.cut_margin_at_depth` (single-level margin)
yields a ball of the *fixed* rate `b μ₀ⁿ` inside every `M`-shape along the orbit.  Hence
`uball_subset_shape_descSig_local` gives the uniform fatness `Uball (U_ij) b ⊆ shape A (U_ij) y`
at every good point, and `uij_window_local` transfers it to the atom mates `x ∈ Z` and converts
entry bounds into the two windows.
-/

open MeasureTheory Topology Filter
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **The shape of an atom mate.**  If `x = u₀ • y` lies in the atom of `y`, then the shape at `x`
is the right translate by `u₀⁻¹` of the shape at `y`. -/
private theorem mem_shape_translate {A : MeasurableSpace X3} {U : Subgroup SL3} {x y : X3}
    {u₀ : SL3} (hu₀ : u₀ ∈ U) (hx : x = u₀ • y) (hax : x ∈ atom A y) {v : SL3} :
    v ∈ shape A U x ↔ v ∈ U ∧ v * u₀ ∈ shape A U y := by
  have hatom : atom A x = atom A y := atom_eq_of_mem_atom_c (x := y) (y := x) hax
  rw [shape, shape, Set.mem_ofPred_eq, Set.mem_ofPred_eq, hatom, hx, mul_smul]
  constructor
  · rintro ⟨hvU, hv⟩
    exact ⟨hvU, U.mul_mem hvU hu₀, hv⟩
  · rintro ⟨hvU, -, hv⟩
    exact ⟨hvU, hv⟩

/-- **The two `U_ij`-windows around a common atom.** -/
private theorem uij_window_local {A : MeasurableSpace X3} {Z H : Set X3} {i j : Fin 3}
    (hij : i ≠ j) {b C : ℝ} (hb : 0 < b) (hbC : b < C)
    (horb : ∀ y ∈ H, atom A y ⊆
      (fun u : SL3 => u • y) '' (Uij hij : Set SL3))
    (hmeet : ∀ x ∈ Z, ∃ y ∈ H, atom A x = atom A y)
    (hfat : ∀ y ∈ H, Work.EKLComp.Uball (Uij hij) b ⊆ shape A (Uij hij) y)
    (hbdd : ∀ y ∈ H, shape A (Uij hij) y ⊆ Work.EKLComp.Uball (Uij hij) C) :
    ∀ x ∈ Z, ∃ s₀ : ℝ,
      (fun s : ℝ => uij hij s) '' Set.Icc (s₀ - b / 2) (s₀ + b / 2) ⊆
        shape A (Uij hij) x ∧
      shape A (Uij hij) x ⊆ (fun s : ℝ => uij hij s) '' Set.Icc (s₀ - C) (s₀ + C) := by
  intro x hx
  obtain ⟨y, hyH, hatomxy⟩ := hmeet x hx
  have hxmem : x ∈ atom A y := hatomxy ▸ mem_atom_self_c A x
  obtain ⟨u₀, hu₀U, hu₀eq⟩ := horb y hyH hxmem
  obtain ⟨s', hs'⟩ := (Lemmas.mem_Uij_iff hij u₀).mp hu₀U
  have hxeq : x = u₀ • y := hu₀eq.symm
  have hbdd_y := hbdd y hyH
  have hfat_y := hfat y hyH
  have hmul_eq : ∀ t : ℝ, (uij hij t * u₀ : SL3) = uij hij (t + s') := by
    intro t
    rw [← hs']
    exact (Matrix.SpecialLinearGroup.transvection_add hij t s').symm
  have hval : ∀ t : ℝ, ((uij hij t * u₀ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j = t + s' := by
    intro t
    rw [hmul_eq t, Lemmas.uij_apply_self hij (t + s')]
  refine ⟨-s', ?_, ?_⟩
  · rintro z ⟨t, ht, rfl⟩
    rw [Set.mem_Icc] at ht
    have hw : |t + s'| < b := by
      have h2 : |t + s'| ≤ b / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      linarith
    have hmem : uij hij (t + s') ∈ Work.EKLComp.Uball (Uij hij) b := by
      refine ⟨Subgroup.subset_closure (Set.mem_range_self _), fun a c => ?_⟩
      rw [Lemmas.uij_apply hij (t + s') a c, Matrix.one_apply]
      by_cases hac : a = c
      · rw [if_pos hac, if_pos hac, sub_self, abs_zero]
        exact hb
      · rw [if_neg hac, if_neg hac]
        by_cases hpair : a = i ∧ c = j
        · rw [if_pos hpair, sub_zero]
          exact hw
        · rw [if_neg hpair, sub_self, abs_zero]
          exact hb
    have hwin : uij hij (t + s') ∈ shape A (Uij hij) y := hfat_y hmem
    rw [mem_shape_translate hu₀U hxeq hxmem]
    refine ⟨Subgroup.subset_closure (Set.mem_range_self _), ?_⟩
    rw [hmul_eq t]
    exact hwin
  · rintro z hz
    obtain ⟨t, ht⟩ := (Lemmas.mem_Uij_iff hij z).mp hz.1
    refine ⟨t, ?_, ht⟩
    have hzshape : uij hij t ∈ shape A (Uij hij) x := by rw [ht]; exact hz
    have hzbd : (uij hij t * u₀ : SL3) ∈ Work.EKLComp.Uball (Uij hij) C :=
      hbdd_y ((mem_shape_translate hu₀U hxeq hxmem).mp hzshape).2
    have hvalC : |t + s'| < C := by
      have h := hzbd.2 i j
      rw [Lemmas.one_apply_ne hij, sub_zero] at h
      rwa [hval t] at h
    rw [Set.mem_Icc]
    exact ⟨by linarith [(abs_lt.mp hvalC).1], by linarith [(abs_lt.mp hvalC).2]⟩

/-- **Uniform fatness of the descending shape.**  If the level-`n` shapes along the orbit contain
the balls `Uball U (c λⁿ)` and conjugation by `aDiag t ⁿ` contracts `Uball U c` into
`Uball U (c λⁿ)`, then the shape of the descending σ-algebra at `y` contains `Uball U c`. -/
private theorem uball_subset_shape_descSig_local {U : Subgroup SL3} {t : Fin 3 → ℝ}
    (hU : IsHoro U) {M : MeasurableSpace X3} {y : X3} {c lam : ℝ} (hc : 0 < c) (hlam0 : 0 ≤ lam)
    (hrate : ∀ n : ℕ, ∀ u : SL3, u ∈ U → u ∈ Work.EKLComp.Uball U c →
      aDiag t ^ n * u * (aDiag t ^ n)⁻¹ ∈ Work.EKLComp.Uball U (c * lam ^ n))
    (hmargin : ∀ n : ℕ, Work.EKLComp.Uball U (c * lam ^ n) ⊆
      shape M U (((fun x : X3 => aDiag t • x)^[n]) y)) :
    Work.EKLComp.Uball U c ⊆ shape (descSig t M) U y := by
  intro u hu
  rw [descSig, shape_pastSig_eq hU y]
  exact ⟨hu.1, fun n => hmargin n (hrate n u hu.1 hu)⟩

theorem desc_plaque_fat_uij {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {i j : Fin 3} (hij : i ≠ j) (t : Fin 3 → ℝ) (hlt : t i < t j)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ) :
    ∀ ε : ENNReal, 0 < ε →
      ∃ (A : MeasurableSpace Work.EKLContract.X3) (Z : Set Work.EKLContract.X3) (c C : ℝ),
        0 < c ∧ c < C ∧
        Work.EKLContract.IsPlaqueAlgebra (Work.EKLContract.Uij hij) Z A ∧ μ Zᶜ < ε ∧
        MeasurableSpace.comap
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A ∧
        ∀ x ∈ Z, ∃ s₀ : ℝ,
          (fun s : ℝ => Work.EKLContract.uij hij s) '' Set.Icc (s₀ - c) (s₀ + c) ⊆
            Work.EKLContract.shape A (Work.EKLContract.Uij hij) x ∧
          Work.EKLContract.shape A (Work.EKLContract.Uij hij) x ⊆
            (fun s : ℝ => Work.EKLContract.uij hij s) '' Set.Icc (s₀ - C) (s₀ + C) := by
  classical
  intro ε hε
  -- a small real scale
  obtain ⟨δ₀, hδ₀pos, hδ₀half, hδ₀ε⟩ := exists_eta ε hε
  let η : ℝ := δ₀ / 3
  have hη0 : 0 < η := by dsimp only [η]; linarith
  have h3η : 3 * η = δ₀ := by dsimp only [η]; ring
  have h3ηε : ENNReal.ofReal (3 * η) < ε := by rw [h3η]; exact hδ₀ε
  -- contraction rate and the intermediate rate
  obtain ⟨lam, hlam0, hlam1, hlam⟩ := exists_contract_rate t
  let μ0 : ℝ := max ((1 + lam) / 2) (1 / 2)
  have hμ00 : 0 < μ0 := lt_max_of_lt_right (by norm_num)
  have hμ01 : μ0 < 1 := max_lt (by linarith) (by norm_num)
  have hlamm : lam < μ0 := lt_max_of_lt_left (by linarith)
  have hμ0le : μ0 ≤ 1 := le_of_lt hμ01
  -- the subgroup
  let U : Subgroup SL3 := Uij hij
  have hUhoro : IsHoro U := by dsimp only [U]; exact Lemmas.isHoro_Uij hij
  have hUclosed : IsClosed (U : Set SL3) := hUhoro.1
  have hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) Filter.atTop (nhds 1) := by
    intro u hu
    obtain ⟨s, hs⟩ := (Lemmas.mem_Uij_iff hij u).mp hu
    rw [← hs]
    exact Lemmas.horoUij_tendsto_conj t hij hlt s
  -- the cut
  obtain ⟨S⟩ := cutHCutData μ U η hη0
  obtain ⟨O, hOopen, hOvis, hOsep⟩ := exists_base_sat_sep U hUclosed
  have huni : ∀ u ∈ U, ((u : Matrix (Fin 3) (Fin 3) ℝ) - 1) ^ 3 = 0 := cutHUnipotent hcontr
  have hfree : ∀ᵐ x ∂μ, x ∈ cutFree U := ae_free_orbit_of_contraction U hUhoro t hmp hcontr
  obtain ⟨C₁, hC₁pos, hC₁thin⟩ := shellThin_bound S
  -- the good set
  have hbad2 : μ S.bad < ENNReal.ofReal (2 * η) := by
    refine lt_of_lt_of_le S.hbad_small (ENNReal.ofReal_le_ofReal ?_)
    dsimp only [η]; linarith
  obtain ⟨N₁, H, hHmeas, hHsub, hHμ⟩ := cutHGoodExists (μ := μ) (U := U) S (t := t) hmp hfree
    (C := 1) (μ0 := μ0) one_pos hμ00 hμ01 (ε' := ENNReal.ofReal (2 * η)) hbad2
  -- the scale
  let b : ℝ := min (min (1 / 20) (10 * S.ρ)) (η * (1 - μ0) / (40 * C₁))
  have hb0 : 0 < b := by
    dsimp only [b]
    refine lt_min (lt_min (by norm_num) (by linarith [S.hρ])) ?_
    exact div_pos (mul_pos hη0 (by linarith)) (by linarith)
  have hb_le_20 : b ≤ 1 / 20 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hb_le_ρ : b ≤ 10 * S.ρ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hb_le_arith : b ≤ η * (1 - μ0) / (40 * C₁) := min_le_right _ _
  have hone : 0 < 1 - μ0 := by linarith
  have harith : C₁ * (20 * b) / (1 - μ0) ≤ η / 2 := by
    have h1 : C₁ * (20 * b) ≤ C₁ * (20 * (η * (1 - μ0) / (40 * C₁))) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC₁pos)
      exact mul_le_mul_of_nonneg_left hb_le_arith (by norm_num)
    have h2 : C₁ * (20 * (η * (1 - μ0) / (40 * C₁))) = η * (1 - μ0) / 2 := by
      field_simp
      ring
    rw [h2] at h1
    rw [div_le_iff₀ hone]
    calc C₁ * (20 * b) ≤ η * (1 - μ0) / 2 := h1
      _ = η / 2 * (1 - μ0) := by ring
  -- the flow and the shell-visiting set
  let φ : X3 → X3 := fun x => aDiag t • x
  let Bad : Set X3 := ⋃ n : ℕ, (φ^[n]) ⁻¹' shellThin S (20 * b * μ0 ^ n)
  have hBad_bound : μ Bad ≤ ENNReal.ofReal (η / 2) := by
    refine le_trans (measure_iUnion_preimage_shellThin (U := U) S (t := t) hmp hC₁pos hC₁thin
      (D := 20 * b) (μ0 := μ0) (by positivity) (le_of_lt hμ00) hμ01) ?_
    exact ENNReal.ofReal_le_ofReal harith
  -- the good set with depth at every level
  let G : Set X3 := H \ Bad
  have hGcompl : Gᶜ ⊆ Hᶜ ∪ Bad := by
    intro x hx
    by_cases h : x ∈ H
    · refine Or.inr ?_
      by_contra hb
      exact hx ⟨h, hb⟩
    · exact Or.inl h
  have hGbound : μ Gᶜ < ENNReal.ofReal (3 * η) := by
    have h1 : μ Gᶜ ≤ μ Hᶜ + μ Bad :=
      le_trans (measure_mono hGcompl) (measure_union_le _ _)
    have h2 : ENNReal.ofReal (2 * η) + ENNReal.ofReal (η / 2) < ENNReal.ofReal (3 * η) := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      rw [ENNReal.ofReal_lt_ofReal_iff (by linarith : (0 : ℝ) < 3 * η)]
      linarith
    exact lt_of_le_of_lt h1 (lt_of_le_of_lt (add_le_add (le_of_lt hHμ) hBad_bound) h2)
  -- Borel core
  let Hs : Set X3 := (MeasureTheory.toMeasurable μ Gᶜ)ᶜ
  have hHsmeas : MeasurableSet Hs := (MeasureTheory.measurableSet_toMeasurable μ Gᶜ).compl
  have hHssub : Hs ⊆ G := by
    intro x hx
    by_contra hcon
    exact hx (MeasureTheory.subset_toMeasurable μ Gᶜ hcon)
  have hHscompl : μ Hsᶜ = μ Gᶜ := by
    show μ ((MeasureTheory.toMeasurable μ Gᶜ)ᶜ)ᶜ = μ Gᶜ
    rw [compl_compl]
    exact MeasureTheory.measure_toMeasurable Gᶜ
  have hofreal3η_le1 : ENNReal.ofReal (3 * η) ≤ 1 := by
    rw [h3η]
    exact le_trans (ENNReal.ofReal_le_ofReal hδ₀half) (by norm_num)
  have hHsbig : 1 - ENNReal.ofReal (3 * η) < μ Hs := by
    have hcompl : μ Hsᶜ = 1 - μ Hs := by
      rw [measure_compl hHsmeas (measure_ne_top μ _), measure_univ]
    refine ENNReal.sub_lt_of_sub_lt hofreal3η_le1 (Or.inl ENNReal.one_ne_top) ?_
    rw [← hcompl, hHscompl]
    exact hGbound
  -- the saturated set
  obtain ⟨bseq, hbseqopen, hbseqrange⟩ := exists_enum_famAtom S O hOopen
  have hbseqmeas : ∀ n, MeasurableSet (bseq n) := fun n => (hbseqopen n).measurableSet
  have hMeq : MCut S O = MeasurableSpace.generateFrom (Set.range bseq) := by
    rw [MCut, ← hbseqrange]
  have hε'' : 0 < ENNReal.ofReal (3 * η) := ENNReal.ofReal_pos.mpr (by linarith)
  obtain ⟨Z, hZmeas0, hZsat0, hZmeet0, hZμ0⟩ :=
    cutCodeZ (t := t) bseq hbseqmeas hHsmeas μ hε'' hHsbig
  rw [← hMeq] at hZmeas0 hZsat0 hZmeet0
  have hmeetA : ∀ x ∈ Z, ∃ y ∈ Hs,
      atom (descSig t (MCut S O)) x = atom (descSig t (MCut S O)) y := by
    intro x hx
    obtain ⟨y, hy⟩ := hZmeet0 x hx
    exact ⟨y, hy.2, (atom_eq_of_mem_atom_c hy.1).symm⟩
  -- geometry at the good points
  have hHscut : Hs ⊆ CutGood S t 1 μ0 N₁ := hHssub.trans (Set.sdiff_subset.trans hHsub)
  have hHsfree : ∀ y ∈ Hs, ∀ n : ℕ, (φ^[n]) y ∈ cutFree U :=
    fun y hy n => CutGood_free (hHscut hy) n
  have hHsdeep : ∀ y ∈ Hs, ∀ n : ℕ, (φ^[n]) y ∉ shellThin S (20 * b * μ0 ^ n) := by
    intro y hy n hmem
    have hyG : y ∈ G := hHssub hy
    have hyBad : y ∈ Bad := Set.mem_iUnion.mpr ⟨n, hmem⟩
    exact hyG.2 hyBad
  have hHscell : ∀ y ∈ Hs, y ∈ ⋃ i, S.cell i := fun y hy => CutGood_subset_cell (hHscut hy)
  -- the margin at every level
  have hmarginLevel : ∀ y ∈ Hs, ∀ n : ℕ,
      Work.EKLComp.Uball U (b * μ0 ^ n) ⊆ shape (MCut S O) U ((φ^[n]) y) := by
    intro y hy n
    have hδ0 : 0 < 20 * b * μ0 ^ n := by positivity
    have hδ1 : 20 * b * μ0 ^ n ≤ 1 := by
      have h20 : 20 * b ≤ 1 := by linarith [hb_le_20]
      have hpow : μ0 ^ n ≤ 1 := pow_le_one₀ (le_of_lt hμ00) hμ0le
      calc 20 * b * μ0 ^ n = (20 * b) * μ0 ^ n := by ring
        _ ≤ 1 * 1 := mul_le_mul h20 hpow (by positivity) (by norm_num)
        _ = 1 := by ring
    have hτ0 : 0 < b * μ0 ^ n := by positivity
    have hτδ : 20 * (b * μ0 ^ n) ≤ 20 * b * μ0 ^ n := le_of_eq (by ring)
    have hτρ : b * μ0 ^ n ≤ 10 * S.ρ := by
      have hpow : μ0 ^ n ≤ 1 := pow_le_one₀ (le_of_lt hμ00) hμ0le
      calc b * μ0 ^ n ≤ b * 1 := mul_le_mul_of_nonneg_left hpow (le_of_lt hb0)
        _ = b := by ring
        _ ≤ 10 * S.ρ := hb_le_ρ
    exact cut_margin_at_depth S O hOopen hOvis hOsep huni (hHsfree y hy n)
      hδ0 hδ1 (hHsdeep y hy n) hτ0 hτδ hτρ
  -- the entry bound for the shape of the cut algebra
  obtain ⟨K, hK⟩ := Work.EKLProd.inv_entries_bound (10 * S.ρ) (by linarith [S.hρ])
  have hK0 : 0 ≤ K := by
    have h1 : (1 : SL3) ∈ V (10 * S.ρ) := by
      intro a b
      have h10 : (0 : ℝ) < 10 * S.ρ := by linarith [S.hρ]
      have hco : ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) a b
          = (1 : Matrix (Fin 3) (Fin 3) ℝ) a b := rfl
      rw [hco, sub_self, abs_zero]
      exact h10
    have h2 := hK 1 h1 0 0
    have h3 : (1 : ℝ) ≤ K := by simpa using h2
    linarith
  have hρgeo : 0 < 3 * (1 + 10 * S.ρ) * K + 2 := by
    have h10 : 0 < 10 * S.ρ := by linarith [S.hρ]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * (1 + 10 * S.ρ)) hK0]
  -- the plaque algebra
  have hplq : IsPlaqueAlgebra U Z (descSig t (MCut S O)) :=
    isPlaqueAlgebra_descSig (U := U) (t := t) (M := MCut S O) (b := Set.range bseq)
      (H := Hs) (Z := Z) (ρ := 3 * (1 + 10 * S.ρ) * K + 2) (c := b) (mu := μ0)
      (lam := lam) (N := 0)
      hUhoro (Set.countable_range bseq) hMeq (MCut_le_borel S O hOopen)
      hρgeo hb0 (le_of_lt hlam0) hlamm hμ01
      (fun n u _ huB => conj_pow_mem_Uball hUhoro hcontr hlam0 hlam huB n)
      (fun y hy n => cutDataOpenAt_shape (S := S) (O := O) (y := y) hOopen hOvis hOsep
        (hHscut hy) n)
      (fun y hy => shape_bdd_at (S := S) (O := O) (y := y) hOopen hOvis hOsep
        (hHscut hy) (fun g hg a c => hK g hg a c))
      (fun y hy n _ => hmarginLevel y hy n)
      (fun y hy => atom_subset_orb_at (S := S) (O := O) (y := y) hOopen hOvis hOsep
        (hHscut hy))
      hZmeas0 hZsat0 hmeetA
  -- fatness and boundedness at the good points
  have hfatA : ∀ y ∈ Hs, Work.EKLComp.Uball U b ⊆ shape (descSig t (MCut S O)) U y := by
    intro y hy
    have hm : ∀ n : ℕ, Work.EKLComp.Uball U (b * lam ^ n) ⊆
        shape (MCut S O) U ((φ^[n]) y) := by
      intro n
      refine le_trans (Work.EKLComp.Uball_mono ?_) (hmarginLevel y hy n)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (le_of_lt hlam0) (le_of_lt hlamm) n) (le_of_lt hb0)
    have h := uball_subset_shape_descSig_local (U := U) (t := t) (M := MCut S O) (y := y)
      hUhoro hb0 (le_of_lt hlam0)
      (fun n u _ huB => conj_pow_mem_Uball hUhoro hcontr hlam0 hlam huB n) hm
    simpa only [descSig] using h
  have hbddA : ∀ y ∈ Hs, shape (descSig t (MCut S O)) U y ⊆
      Work.EKLComp.Uball U (3 * (1 + 10 * S.ρ) * K + 2) := by
    intro y hy u hu
    exact shape_bdd_at (S := S) (O := O) (y := y) hOopen hOvis hOsep (hHscut hy)
      (fun g hg a c => hK g hg a c) ⟨hu.1, atom_descSig_le t (MCut S O) y hu.2⟩
  have horbA : ∀ y ∈ Hs, atom (descSig t (MCut S O)) y ⊆
      (fun u : SL3 => u • y) '' (U : Set SL3) :=
    fun y hy => (atom_descSig_le t (MCut S O) y).trans
      (atom_subset_orb_at (S := S) (O := O) (y := y) hOopen hOvis hOsep (hHscut hy))
  -- the window sandwich
  have hbC : b < 3 * (1 + 10 * S.ρ) * K + 2 := by
    have h10 : 0 < 10 * S.ρ := by linarith [S.hρ]
    have hge : 0 ≤ 3 * (1 + 10 * S.ρ) * K :=
      mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * (1 + 10 * S.ρ)) hK0
    linarith [hb_le_20]
  have hwindow := uij_window_local (A := descSig t (MCut S O)) (Z := Z) (H := Hs)
    (i := i) (j := j) hij (b := b) (C := 3 * (1 + 10 * S.ρ) * K + 2) hb0 hbC
    (fun y hy => horbA y hy) hmeetA (fun y hy => hfatA y hy) (fun y hy => hbddA y hy)
  refine ⟨descSig t (MCut S O), Z, b / 2, 3 * (1 + 10 * S.ρ) * K + 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith [hb0]
  · linarith [hbC]
  · exact hplq
  · exact lt_trans hZμ0 h3ηε
  · exact comap_descSig_le t (MCut S O)
  · intro x hx
    obtain ⟨s₀, h1, h2⟩ := hwindow x hx
    exact ⟨s₀, h1, h2⟩

end Work.EKLC6Core
