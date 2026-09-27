import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.desc_plaque_fat_uij
import Submission.Work.EKLC6Core.cutSetup
import Submission.Work.EKLC6Core.cutHDefs
import Submission.Work.EKLC6Core.cutHelpers
import Submission.Work.EKLC6Core.cutHCutData
import Submission.Work.EKLC6Core.cutHUnipotent
import Submission.Work.EKLC6Core.atom_gen_cut
import Submission.Work.EKLC6Core.isOpen_shape_cut_cell
import Submission.Work.EKLC6Core.shape_cut_bad
import Submission.Work.EKLC6Core.shape_cut_bounded_uniform
import Submission.Work.EKLC6Core.cut_margin_at_depth
import Submission.Work.EKLC6Core.contract_rate
import Submission.Work.EKLC6Core.ae_free_orbit_of_contraction
import Submission.Work.EKLC6Core.exists_base_sat_sep
import Submission.Work.EKLC6Core.plaqueAlgebra_of_ae_pointwise
import Submission.Work.EKLC6Core.shape_pastSig_eq
import Submission.Work.EKLComp.atom_bad_bound
import Submission.Work.EKLC6Core.ae_deep_avoid
import Submission.Work.EKLC6Core.shape_open_of_finite_margin
import Submission.Work.EKLC6Core.conj_inv_entry_bound

/-!
# `Work.EKLC6Core.desc_plaque_conull_ergodic_pt`

The conull (ergodic) form of the descending plaque algebra for a single root group `U_ij`
contracted by `aDiag t` (`t i < t j`): for an ergodic `aDiag t`-invariant probability measure `μ`
on `X₃ = SL₃(ℝ)/SL₃(ℤ)` there are a countably generated σ-algebra `A ≤ borel` and a conull set
`Z` such that `A` is a plaque algebra for `U_ij` on `Z` and `A` is `aDiag t`-decreasing.

## Proof outline

* Choose the cut `S : CutData μ U (1/2)` (Pisa 7.38) and the separating family `O`; let
  `M = MCut S O` and `A = descSig t M = ⨆ₙ comap ((aDiag t ·)^[n]) M`.
* For a.e. `x`: the whole orbit stays in `⋃ cell ∪ bad` (measure preservation + `S.hcover`), is
  free (`ae_free_orbit_of_contraction`), and for all large `n` avoids the shell
  `shellThin S (20 c νⁿ)` (Borel--Cantelli, `ae_deep_avoid`).  Ergodicity gives, for a.e. `x`,
  a forward visit to a cell.
* At a point of `cell i` the `M`-shape is a bounded open trace (`isOpen_shape_cut_cell`,
  `shape_cut_bounded_uniform`); at a point of `bad` it is the (open) trace
  `U ∩ {v | v • x ∈ bad}` (`shape_cut_bad`, `S.hbad_open`).  So *every* orbit point has a
  relatively open `M`-shape; the deepness converts (via `cut_margin_at_depth`) into the margin
  `Uball U (c μⁿ) ⊆ shape_M (aⁿ x)`.  The level-`n` bound of `shape A` is then obtained from the
  level-`k` bound (the cell visit), and `shape_open_of_finite_margin` shows that the
  `A`-shape is then the trace of an open set.
* `plaqueAlgebra_of_ae_pointwise` then produces the conull saturated set `Z`.

## Auxiliary lemmas (proved by colleagues in sibling files)

The file imports `EKLC6Core.ae_deep_avoid`, `EKLC6Core.shape_open_of_finite_margin` and
`EKLC6Core.conj_inv_entry_bound`; the local appendix below contains temporary copies used during
development.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

noncomputable section

namespace Work.EKLC6Core

open MeasureTheory Filter
open scoped ENNReal

open Work.EKLContract

/-! ## Elementary helpers -/

/-- The descent `comap φ A ≤ A` makes `φ` well defined on atoms. -/
private theorem atom_image_subset_c {A : MeasurableSpace X3} {φ : X3 → X3}
    (hdesc : MeasurableSpace.comap φ A ≤ A) (x : X3) :
    φ '' atom A x ⊆ atom A (φ x) := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [atom, Set.mem_sInter] at hz ⊢
  intro s hs
  exact hz (φ ⁻¹' s)
    ⟨hdesc (φ ⁻¹' s) (MeasurableSpace.measurableSet_comap.mpr ⟨s, hs.1, rfl⟩), hs.2⟩

/-- Iterated version of `atom_image_subset_c`. -/
private theorem atom_image_iterate_subset {A : MeasurableSpace X3} {φ : X3 → X3}
    (hdesc : MeasurableSpace.comap φ A ≤ A) (k : ℕ) (x : X3) :
    (φ^[k]) '' atom A x ⊆ atom A ((φ^[k]) x) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h1 : (φ^[n + 1]) = φ ∘ (φ^[n]) := funext fun y => Function.iterate_succ_apply' φ n y
    rw [h1, Set.image_comp]
    exact Set.Subset.trans (Set.image_mono ih) (atom_image_subset_c hdesc ((φ^[n]) x))

/-- Conjugation by a power of `aDiag s` preserves a horospherical subgroup. -/
private theorem conj_pow_mem_U_loc {U : Subgroup SL3} (hU : IsHoro U) {s : Fin 3 → ℝ} {u : SL3}
    (hu : u ∈ U) (n : ℕ) : aDiag s ^ n * u * (aDiag s ^ n)⁻¹ ∈ U := by
  induction n with
  | zero => simpa using hu
  | succ k ih =>
    rw [pow_succ']
    have key : aDiag s * aDiag s ^ k * u * (aDiag s * aDiag s ^ k)⁻¹
        = aDiag s * (aDiag s ^ k * u * (aDiag s ^ k)⁻¹) * (aDiag s)⁻¹ := by group
    rw [key]
    exact hU.2.1 s _ ih

/-- Conjugation by the *inverse* of a power of `aDiag s` preserves a horospherical subgroup. -/
private theorem conj_inv_pow_mem_U {U : Subgroup SL3} (hU : IsHoro U) {s : Fin 3 → ℝ} {u : SL3}
    (hu : u ∈ U) (n : ℕ) : (aDiag s ^ n)⁻¹ * u * aDiag s ^ n ∈ U := by
  have hstep : ∀ w : SL3, w ∈ U → (aDiag s)⁻¹ * w * aDiag s ∈ U := by
    intro w hw
    have h2 : (aDiag s)⁻¹ = aDiag (-s) := inv_eq_of_mul_eq_one_left (aDiag_neg_mul s)
    have h := hU.2.1 (-s) w hw
    rw [← h2, inv_inv] at h
    exact h
  induction n with
  | zero => simpa using hu
  | succ k ih =>
    have h1 : (aDiag s ^ (k + 1))⁻¹ * u * aDiag s ^ (k + 1)
        = (aDiag s)⁻¹ * ((aDiag s ^ k)⁻¹ * u * aDiag s ^ k) * aDiag s := by
      rw [pow_succ]; group
    rw [h1]
    exact hstep _ ih

/-! ## The main theorem -/

theorem desc_plaque_conull_ergodic_pt {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {i j : Fin 3} (hij : i ≠ j) (t : Fin 3 → ℝ) (hlt : t i < t j)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (herg : ∀ s : Set Work.EKLContract.X3, MeasurableSet s →
      (∃ N : Set Work.EKLContract.X3, μ N = 0 ∧ ∀ x : Work.EKLContract.X3, x ∉ N → x ∈ s →
        Work.EKLContract.aDiag t • x ∈ s) → μ s = 0 ∨ μ sᶜ = 0) :
    ∃ (A : MeasurableSpace Work.EKLContract.X3) (Z : Set Work.EKLContract.X3),
      Work.EKLContract.IsPlaqueAlgebra (Work.EKLContract.Uij hij) Z A ∧ μ Zᶜ = 0 ∧
      MeasurableSpace.comap
        (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A := by
  classical
  letI : MeasurableSpace X3 := Work.EKLContract.instMeasurableSpaceX3
  let U : Subgroup SL3 := Uij hij
  let φ : X3 → X3 := fun x => aDiag t • x
  have hUhoro : IsHoro U := Lemmas.isHoro_Uij hij
  have hUclosed : IsClosed (U : Set SL3) := hUhoro.1
  have hcontr : ∀ u ∈ U, Tendsto (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (nhds 1) := by
    intro u hu
    obtain ⟨s, hs⟩ := (Lemmas.mem_Uij_iff hij u).mp hu
    rw [← hs]
    exact Lemmas.horoUij_tendsto_conj t hij hlt s
  -- the cut, the separating family, the cut σ-algebra, the descending σ-algebra
  obtain ⟨S⟩ := cutHCutData μ U (1 / 2) (by norm_num)
  obtain ⟨O, hOopen, hOvis, hOsep⟩ := exists_base_sat_sep U hUclosed
  have huni : ∀ u ∈ U, ((u : Matrix (Fin 3) (Fin 3) ℝ) - 1) ^ 3 = 0 := cutHUnipotent hcontr
  let M : MeasurableSpace X3 := MCut S O
  let A : MeasurableSpace X3 := descSig t M
  letI : MeasurableSpace X3 := Work.EKLContract.instMeasurableSpaceX3
  have hAdesc : MeasurableSpace.comap (fun x : X3 => aDiag t • x) A ≤ A :=
    comap_descSig_le t M
  -- the constants
  let c : ℝ := min (1 / 20) (10 * S.ρ)
  have hc0 : 0 < c := lt_min (by norm_num) (by linarith [S.hρ])
  have hc20 : 20 * c ≤ 1 := by
    have h : c ≤ 1 / 20 := min_le_left _ _
    calc 20 * c ≤ 20 * (1 / 20) := mul_le_mul_of_nonneg_left h (by norm_num)
      _ = 1 := by norm_num
  have hcρ : c ≤ 10 * S.ρ := min_le_right _ _
  obtain ⟨lam, hlam0, hlam1, hlamle⟩ := exists_contract_rate t
  let mu : ℝ := (lam + 1) / 2
  have hlam_mu : lam < mu := by dsimp only [mu]; linarith
  have hmu0 : 0 < mu := lt_trans hlam0 hlam_mu
  have hmu1 : mu < 1 := by dsimp only [mu]; linarith
  let nu : ℝ := (mu + 1) / 2
  have hmu_nu : mu < nu := by dsimp only [nu]; linarith
  have hnu0 : 0 < nu := lt_trans hmu0 hmu_nu
  have hnu1 : nu < 1 := by dsimp only [nu]; linarith
  let rho : ℝ := 100 * (1 + 10 * S.ρ) ^ 3
  have hrho0 : 0 < rho := by
    have h1 : (0 : ℝ) < 1 + 10 * S.ρ := by linarith [S.hρ]
    dsimp only [rho]
    positivity
  have hrate : ∀ n : ℕ, ∀ u : SL3, u ∈ U → u ∈ EKLComp.Uball U rho →
      aDiag t ^ n * u * (aDiag t ^ n)⁻¹ ∈ EKLComp.Uball U (rho * lam ^ n) :=
    fun n u _ hb => conj_pow_mem_Uball hUhoro hcontr hlam0 hlamle hb n
  -- the open `M`-shape at every point of `⋃ cell ∪ bad`
  have hopenOn : ∀ y : X3, y ∈ (⋃ i, S.cell i) ∪ S.bad →
      ∃ W : Set SL3, IsOpen W ∧ shape (MCut S O) U y = W ∩ (U : Set SL3) := by
    intro y hy
    rcases hy with hy | hy
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      exact isOpen_shape_cut_cell S O hOopen hOvis hOsep i y hi
    · obtain ⟨-, hshape⟩ := shape_cut_bad S O hOopen hOvis hOsep y hy
      refine ⟨{v : SL3 | v • y ∈ S.bad}, ?_, ?_⟩
      · exact S.hbad_open.preimage ((continuous_smul (M := SL3)).comp
          (continuous_id.prodMk continuous_const))
      · rw [hshape, Set.inter_comm]
  -- (a) the orbit stays in `⋃ cell ∪ bad`
  have horb : ∀ᵐ x ∂μ, ∀ n : ℕ, (φ^[n]) x ∈ (⋃ i, S.cell i) ∪ S.bad := by
    rw [MeasureTheory.ae_all_iff]
    intro n
    rw [MeasureTheory.ae_iff]
    rw [show {x : X3 | ¬ (φ^[n]) x ∈ (⋃ i, S.cell i) ∪ S.bad}
        = (φ^[n]) ⁻¹' (((⋃ i, S.cell i) ∪ S.bad)ᶜ) from by ext x; simp]
    exact (hmp.iterate n).preimage_null S.hcover
  -- (b) the orbit is free
  have hfree : ∀ᵐ x ∂μ, ∀ n : ℕ, (φ^[n]) x ∈ cutFree U := by
    have h : ∀ᵐ x ∂μ, x ∈ cutFree U := ae_free_orbit_of_contraction U hUhoro t hmp hcontr
    have hc : μ (cutFree U)ᶜ = 0 := by
      have h' := MeasureTheory.ae_iff.mp h
      rwa [show {x : X3 | ¬ x ∈ cutFree U} = (cutFree U)ᶜ from by ext x; simp] at h'
    rw [MeasureTheory.ae_all_iff]
    intro n
    rw [MeasureTheory.ae_iff]
    rw [show {x : X3 | ¬ (φ^[n]) x ∈ cutFree U} = (φ^[n]) ⁻¹' (cutFree U)ᶜ from by ext x; simp]
    exact (hmp.iterate n).preimage_null hc
  -- (c) deepness: for a.e. `x` the orbit avoids the shells of rate `ν`
  have hdeep : ∀ᵐ x ∂μ, ∃ N : ℕ, ∀ n ≥ N, (φ^[n]) x ∉ shellThin S (20 * c * nu ^ n) := by
    have h := ae_deep_avoid (U := U) (ε := (1 : ℝ) / 2) S hmp (D := 20 * c) (ν := nu)
      (by positivity) hnu0 hnu1
    filter_upwards [h] with x hx
    exact hx
  -- (d) a forward visit to the cells, by ergodicity
  have hvisit : ∀ᵐ x ∂μ, ∃ k : ℕ, (φ^[k]) x ∈ ⋃ i, S.cell i := by
    have hcellcompl : μ (⋃ i, S.cell i)ᶜ ≤ μ S.bad := by
      have hsub : (⋃ i, S.cell i)ᶜ ⊆ (((⋃ i, S.cell i) ∪ S.bad)ᶜ) ∪ S.bad := by
        intro x hx
        by_cases hb : x ∈ S.bad
        · exact Or.inr hb
        · exact Or.inl (by
            simp only [Set.mem_compl_iff, Set.mem_union, not_or]
            exact ⟨hx, hb⟩)
      calc μ (⋃ i, S.cell i)ᶜ ≤ μ ((((⋃ i, S.cell i) ∪ S.bad)ᶜ) ∪ S.bad) :=
            MeasureTheory.measure_mono hsub
        _ ≤ μ (((⋃ i, S.cell i) ∪ S.bad)ᶜ) + μ S.bad := MeasureTheory.measure_union_le _ _
        _ = μ S.bad := by rw [S.hcover, zero_add]
    have hbad1 : μ S.bad < 1 :=
      lt_of_lt_of_le S.hbad_small (by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num))
    have hcellcompl_lt : μ (⋃ i, S.cell i)ᶜ < 1 := lt_of_le_of_lt hcellcompl hbad1
    set R : Set X3 := ⋂ k : ℕ, (φ^[k]) ⁻¹' (⋃ i, S.cell i)ᶜ with hRdef
    have hRmeas : MeasurableSet R := by
      rw [hRdef]
      exact MeasurableSet.iInter fun k =>
        (MeasurableSet.iUnion fun i => (S.hopen i).measurableSet).compl.preimage
          (Continuous.measurable ((continuous_const_smul (aDiag t)).iterate k))
    have hRfwd : ∀ x : X3, x ∈ R → φ x ∈ R := by
      intro x hx
      simp only [hRdef, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff] at hx ⊢
      intro k
      rw [← Function.iterate_succ_apply]
      exact hx (k + 1)
    have hRsub : R ⊆ (⋃ i, S.cell i)ᶜ := by
      intro x hx
      rw [hRdef] at hx
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff] at hx
      simpa using hx 0
    have hRlt : μ R < 1 := lt_of_le_of_lt (MeasureTheory.measure_mono hRsub) hcellcompl_lt
    rcases herg R hRmeas ⟨∅, by simp, fun x _ hx => hRfwd x hx⟩ with hzero | hczero
    · rw [MeasureTheory.ae_iff]
      rw [show {x : X3 | ¬ ∃ k : ℕ, (φ^[k]) x ∈ ⋃ i, S.cell i} = R from by
        rw [hRdef]; ext x; simp]
      exact hzero
    · exfalso
      have hone : μ R = 1 := by
        have h := MeasureTheory.measure_add_measure_compl (μ := μ) hRmeas
        rw [measure_univ, hczero, add_zero] at h
        exact h
      exact absurd (hone ▸ hRlt) (lt_irrefl 1)
  -- assemble the conull good set
  have hgood : ∀ᵐ x ∂μ, (∀ n : ℕ, (φ^[n]) x ∈ (⋃ i, S.cell i) ∪ S.bad) ∧
      (∀ n : ℕ, (φ^[n]) x ∈ cutFree U) ∧
      (∃ k : ℕ, (φ^[k]) x ∈ ⋃ i, S.cell i) ∧
      (∃ N : ℕ, ∀ n ≥ N, (φ^[n]) x ∉ shellThin S (20 * c * nu ^ n)) := by
    filter_upwards [horb, hfree, hvisit, hdeep] with x h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  -- (P1) the `A`-atom is inside the `U`-orbit
  have hP1 : ∀ᵐ x ∂μ, atom A x ⊆ (fun u : SL3 => u • x) '' (U : Set SL3) := by
    filter_upwards [hgood] with x hx
    obtain ⟨hxorb, hxfree, hxvis, -⟩ := hx
    obtain ⟨k, hk⟩ := hxvis
    obtain ⟨ic, hic⟩ := Set.mem_iUnion.mp hk
    intro z hz
    have hzmem : (φ^[k]) z ∈ atom A ((φ^[k]) x) :=
      atom_image_iterate_subset (A := A) (φ := φ) hAdesc k x ⟨z, hz, rfl⟩
    have hzM : (φ^[k]) z ∈ atom (MCut S O) ((φ^[k]) x) :=
      atom_descSig_le t (MCut S O) ((φ^[k]) x) hzmem
    have hcomm : (MCut S O) = MeasurableSpace.generateFrom (Set.range
        (fun p : Fin S.N × ℕ => genCell S O p.1 p.2) ∪ {S.bad}) := rfl
    rw [hcomm, atom_gen_cut S O hOopen hOvis hOsep ic ((φ^[k]) x) hic] at hzM
    obtain ⟨hcell, u, huU, hlift⟩ := hzM
    refine ⟨(aDiag t ^ k)⁻¹ * u * aDiag t ^ k, conj_inv_pow_mem_U hUhoro huU k, ?_⟩
    have h1 : aDiag t ^ k • z = u • (aDiag t ^ k • x) := by
      calc aDiag t ^ k • z = (φ^[k]) z := (smul_iterate_apply (aDiag t) k z).symm
        _ = mkX (S.lift ic ((φ^[k]) z)) := (S.lift_mk ic _ hcell).symm
        _ = mkX (u * S.lift ic ((φ^[k]) x)) := by rw [hlift]
        _ = u • mkX (S.lift ic ((φ^[k]) x)) := Lemmas.mkX_mul u _
        _ = u • (φ^[k]) x := by rw [S.lift_mk ic _ hic]
        _ = u • (aDiag t ^ k • x) := by rw [smul_iterate_apply]
    show ((aDiag t ^ k)⁻¹ * u * aDiag t ^ k) • x = z
    calc ((aDiag t ^ k)⁻¹ * u * aDiag t ^ k) • x
        = (aDiag t ^ k)⁻¹ • (u • (aDiag t ^ k • x)) := by simp only [mul_smul]
      _ = (aDiag t ^ k)⁻¹ • (aDiag t ^ k • z) := by rw [h1]
      _ = z := inv_smul_smul _ z
  -- (P2) the `A`-shape is the trace of an open set
  have hP2 : ∀ᵐ x ∂μ, ∃ O' : Set SL3, IsOpen O' ∧ shape A U x = O' ∩ (U : Set SL3) := by
    filter_upwards [hgood] with x hx
    obtain ⟨hxorb, hxfree, hxvis, hxdeep⟩ := hx
    obtain ⟨k, hk⟩ := hxvis
    obtain ⟨ic, hic⟩ := Set.mem_iUnion.mp hk
    refine shape_open_of_finite_margin (U := U) (t := t) (M := MCut S O) (x := x) (k := k)
      (c := c) (ρ := rho) (lam := lam) (mu := mu) hUhoro hc0 hrho0 (le_of_lt hlam0)
      hlam_mu hmu1 hrate ?_ ?_ ?_
    · intro n
      exact hopenOn _ (hxorb n)
    · exact shape_cut_bounded_uniform S O hOopen hOvis hOsep ic ((φ^[k]) x) hic (hxfree k)
    · obtain ⟨N, hN⟩ := hxdeep
      refine ⟨N, fun n hn => ?_⟩
      have hmono : shellThin S (20 * c * mu ^ n) ⊆ shellThin S (20 * c * nu ^ n) :=
        shellThin_mono S (by
          have hpow : mu ^ n ≤ nu ^ n := pow_le_pow_left₀ (le_of_lt hmu0) (le_of_lt hmu_nu) n
          nlinarith [hc0, hpow])
      exact cut_margin_at_depth S O hOopen hOvis hOsep huni (z := (φ^[n]) x) (hxfree n)
        (δ := 20 * c * mu ^ n) (τ := c * mu ^ n)
        (by positivity) (by
          have hpow : mu ^ n ≤ 1 := pow_le_one₀ (le_of_lt hmu0) (le_of_lt hmu1)
          nlinarith [hc20, hpow]) (fun hcon => hN n hn (hmono hcon))
        (by positivity) (by nlinarith) (by
          have hpow : mu ^ n ≤ 1 := pow_le_one₀ (le_of_lt hmu0) (le_of_lt hmu1)
          nlinarith [hcρ, hpow])
  -- (P3) the `A`-shape is entrywise bounded
  have hP3 : ∀ᵐ x ∂μ, ∃ C : ℝ, ∀ u ∈ shape A U x, ∀ a b : Fin 3,
      |((u : SL3) : Matrix (Fin 3) (Fin 3) ℝ) a b| ≤ C := by
    filter_upwards [hgood] with x hx
    obtain ⟨hxorb, hxfree, hxvis, -⟩ := hx
    obtain ⟨k, hk⟩ := hxvis
    obtain ⟨ic, hic⟩ := Set.mem_iUnion.mp hk
    have hbddk : shape (MCut S O) U ((φ^[k]) x) ⊆ EKLComp.Uball U rho :=
      shape_cut_bounded_uniform S O hOopen hOvis hOsep ic ((φ^[k]) x) hic (hxfree k)
    refine ⟨rho * (Real.exp (t i - t j) ^ k)⁻¹ + 1, fun u hu a b => ?_⟩
    have hu' : u ∈ shape (⨆ n : ℕ, MeasurableSpace.comap
        ((fun y : X3 => aDiag t • y)^[n]) (MCut S O)) U x := hu
    rw [shape_pastSig_eq (U := U) hUhoro x] at hu'
    have hconj : aDiag t ^ k * u * (aDiag t ^ k)⁻¹ ∈ EKLComp.Uball U rho := hbddk (hu'.2 k)
    exact conj_inv_entry_bound hij t k rho hrho0 hu'.1 hconj a b
  -- conclusion
  have hAle : A ≤ borel X3 := descSig_le_borel (MCut S O) (MCut_le_borel S O hOopen)
  have hgen : ∃ b : Set (Set X3), b.Countable ∧ A = MeasurableSpace.generateFrom b :=
    descSig_countably_generated (b := famAtom S O)
      ((Set.countable_range (fun p : Fin S.N × ℕ => genCell S O p.1 p.2)).union
        (Set.countable_singleton S.bad)) rfl
  obtain ⟨Z, hZ, hplq⟩ := plaqueAlgebra_of_ae_pointwise hAle hgen hP1 hP2 hP3
  exact ⟨A, Z, hplq, hZ, hAdesc⟩

end Work.EKLC6Core
