import Mathlib
import Submission.Work.EKLRelCross.flower_plaqueAlgebra_bdd
import Submission.Work.EKLRelCross.atom_flower_local
import Submission.Work.EKLRelCross.CrossSectionSetup
import Submission.Work.EKLRelCross.exists_shrink_nhds
import Submission.Work.EKLRelCross.exists_Ucl_bound
import Submission.Work.EKLRelCross.FlowerLocalAux.inj_nhds_local
import Submission.Work.EKLRelCross.freeSet_borel
import Submission.Work.EKLProd.inv_entries_bound

/-!
# `Work.EKLRelCross.W.W_flower_local` — the local flower (Pisa §6)

For a horospherical subgroup `U ≤ SL₃(ℝ)`, a point `x₀` with free `U`-orbit and `R > 0` there are
`Z, m, G, O` with `O` open containing `x₀`, `G` Borel with `G ⊆ Z`, `(Z, m)` a plaque algebra,
`x₀ ∈ G`, `O ∩ {U-free points} ⊆ G` and `V R ∩ U ⊆ shape m U x` for every `x ∈ G`.

The proof chains

* `Work.EKLRelCross.FlowerLocalAux.inj_nhds_local` and `Work.EKLRelCross.exists_shrink_nhds`
  (Pisa 6.7/6.8) into the bounded cross-section `C` of Pisa 6.9–6.12 (`crossSection_local`);
* the flower σ-algebra `flowerSigma U δ C W` of `C`, whose atoms are the plaques
  `(V δ ∩ U) • z` (`Work.EKLRelCross.atom_flower_local`) and which is a plaque algebra
  (`Work.EKLRelCross.flower_plaqueAlgebra_bdd`);
* the size bookkeeping that makes the `R`-plaque sit inside the atom: `δ` is chosen so that
  `V R · (element of Ucl U 1) ⊆ V δ` and so that the products needed by the local
  cross-section property land in the scale `b` at which `crossSection_local` holds.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

noncomputable section

open Work.EKLContract

namespace Work.EKLRelCross.W

/-! ## 0. Elementary entrywise lemmas (self-contained copies) -/

private lemma abs_one_apply_le' (i j : Fin 3) : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

private lemma abs_sub_le_abs_add' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)

private lemma sub_one_entry_le' {A : Matrix (Fin 3) (Fin 3) ℝ} {C : ℝ}
    (h : ∀ k l, |A k l| ≤ C) (i j : Fin 3) :
    |A i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C + 1 := by
  calc |A i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
      ≤ |A i j| + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_sub_le_abs_add' _ _
    _ ≤ C + 1 := add_le_add (h i j) (abs_one_apply_le' i j)

private lemma mul_entries_le_three' {A B : Matrix (Fin 3) (Fin 3) ℝ} (i j : Fin 3) {sA sB : ℝ}
    (hA : ∀ k l, |A k l| ≤ sA) (hB : ∀ k l, |B k l| ≤ sB) (hsA : 0 ≤ sA) (hsB : 0 ≤ sB) :
    |(A * B) i j| ≤ 3 * sA * sB := by
  rw [Matrix.mul_apply]
  calc |∑ k : Fin 3, A i k * B k j| ≤ ∑ k : Fin 3, |A i k * B k j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin 3, |A i k| * |B k j| := by simp [abs_mul]
    _ ≤ ∑ _k : Fin 3, sA * sB :=
        Finset.sum_le_sum (fun k _ => mul_le_mul (hA i k) (hB k j) (abs_nonneg _) hsA)
    _ = 3 * (sA * sB) := by simp [Finset.sum_const, Fintype.card_fin]
    _ = 3 * sA * sB := by ring

private lemma mul_sub_one_eq' (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by
  noncomm_ring

private lemma mul_sub_one_entry_le' {A B : Matrix (Fin 3) (Fin 3) ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ k l, |A k l - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ a)
    (hB : ∀ k l, |B k l - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ b) (i j : Fin 3) :
    |(A * B) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 3 * a * b + a + b := by
  have hsub : (A * B) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
      = ((A - 1) * (B - 1)) i j + (A - 1) i j + (B - 1) i j := by
    have h := congrFun (congrFun (mul_sub_one_eq' A B) i) j
    simpa [Matrix.sub_apply, Matrix.add_apply] using h
  have hAb : ∀ k l, |(A - 1) k l| ≤ a := fun k l => by simpa [Matrix.sub_apply] using hA k l
  have hBb : ∀ k l, |(B - 1) k l| ≤ b := fun k l => by simpa [Matrix.sub_apply] using hB k l
  have hprod := mul_entries_le_three' i j hAb hBb ha hb
  have h1 : |(A - 1) i j| ≤ a := by simpa [Matrix.sub_apply] using hA i j
  have h2 : |(B - 1) i j| ≤ b := by simpa [Matrix.sub_apply] using hB i j
  have habs := abs_add_le (((A - 1) * (B - 1)) i j + (A - 1) i j) ((B - 1) i j)
  have habs2 := abs_add_le (((A - 1) * (B - 1)) i j) ((A - 1) i j)
  rw [hsub]
  linarith

private lemma Ucl_mono' {U : Subgroup SL3} {a b : ℝ} (h : a ≤ b) :
    Work.EKLRelCross.Ucl U a ⊆ Work.EKLRelCross.Ucl U b :=
  fun _ hg => ⟨hg.1, fun i j => le_trans (hg.2 i j) h⟩

private lemma Ucl_one_subset_V_two' {U : Subgroup SL3} :
    Work.EKLRelCross.Ucl U 1 ⊆ V 2 := by
  intro g hg i j
  linarith [hg.2 i j]

/-! ## 1. The bounded cross-section (Pisa 6.7 + 6.9–6.12), clean version

This is `Work.EKLRelCross.pisa_crosssection` with the only gap in its proof
(`Work.EKLRelCross.exists_inj_nhds`) replaced by the proved
`Work.EKLRelCross.FlowerLocalAux.inj_nhds_local`. -/

theorem crossSection_local {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
    (x₀ : X3) {ρ : ℝ} (hρ : 2 < ρ)
    (hfree : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x₀ = u₂ • x₀ → u₁ = u₂) :
    ∃ (E C : Set X3), IsClosed E ∧ x₀ ∈ interior E ∧ C ⊆ E ∧ MeasurableSet C ∧
      (∀ x ∈ E, ∃! t : SL3, t ∈ Work.EKLRelCross.Ucl U 1 ∧ t • x ∈ C) ∧
      (∀ c ∈ C, ∀ u ∈ Work.EKLRelCross.Ucl U ρ, u • c ∈ C → u = 1) := by
  classical
  obtain ⟨R₀, hR₀inv, hR₀mul, hR₀mulinv⟩ := Work.EKLRelCross.exists_Ucl_bound U
  set R : ℝ := max R₀ ρ with hRdef
  have hRρ : ρ ≤ R := le_max_right _ _
  have hRR₀ : R₀ ≤ R := le_max_left _ _
  have hRpos : 0 ≤ R := le_trans (by linarith : (0 : ℝ) ≤ ρ) hRρ
  have hR1 : (1 : ℝ) ≤ R := le_trans (by linarith : (1 : ℝ) ≤ ρ) hRρ
  obtain ⟨E₁, hE₁c, hE₁int, hshrink⟩ :=
    Work.EKLRelCross.exists_shrink_nhds hUcl x₀ hfree (R := R) hRpos
  obtain ⟨E₂, hE₂c, hE₂int, hinj₂⟩ :=
    Work.EKLRelCross.FlowerLocalAux.inj_nhds_local hUcl x₀ hfree (R := R)
  set E : Set X3 := E₁ ∩ E₂ with hEdef
  have hEc : IsCompact E := hE₁c.inter hE₂c
  have hEint : x₀ ∈ interior E := by
    rw [hEdef, interior_inter]
    exact ⟨hE₁int, hE₂int⟩
  have hshrinkE : ∀ x ∈ E, ∀ x' ∈ E, ∀ u ∈ Work.EKLRelCross.Ucl U R,
      ∀ u' ∈ Work.EKLRelCross.Ucl U R,
      u • x = u' • x' → u' * u⁻¹ ∈ Work.EKLRelCross.Ucl U 1 ∧
        u⁻¹ * u' ∈ Work.EKLRelCross.Ucl U 1 :=
    fun x hx x' hx' u hu u' hu' h => hshrink x hx.1 x' hx'.1 u hu u' hu' h
  have hinjE : ∀ x ∈ E, ∀ u ∈ Work.EKLRelCross.Ucl U 1, ∀ u' ∈ Work.EKLRelCross.Ucl U 1,
      u • x = u' • x → u = u' :=
    fun x hx u hu u' hu' h =>
      hinj₂ x hx.2 u (Ucl_mono' hR1 hu) u' (Ucl_mono' hR1 hu') h
  have h1R : Work.EKLRelCross.Ucl U 1 ⊆ Work.EKLRelCross.Ucl U R := Ucl_mono' hR1
  have hR₀R : Work.EKLRelCross.Ucl U R₀ ⊆ Work.EKLRelCross.Ucl U R := Ucl_mono' hRR₀
  have hBc : IsCompact (Work.EKLRelCross.Ucl U 1) := Work.EKLRelCross.isCompact_Ucl hUcl 1
  have hAc : IsCompact (Work.EKLRelCross.Ucl U R) := Work.EKLRelCross.isCompact_Ucl hUcl R
  have h1Ucl1 : (1 : SL3) ∈ Work.EKLRelCross.Ucl U 1 :=
    Work.EKLRelCross.Uball_subset_Ucl U 1 (Work.EKLRelCross.one_mem_Uball U (by norm_num))
  have hρR : ∀ g ∈ Work.EKLRelCross.Ucl U ρ, g ∈ Work.EKLRelCross.Ucl U R := Ucl_mono' hRρ
  have hBinv : ∀ g ∈ Work.EKLRelCross.Ucl U 1, g⁻¹ ∈ Work.EKLRelCross.Ucl U R :=
    fun g hg => hR₀R (hR₀inv g hg)
  have hBB : ∀ g ∈ Work.EKLRelCross.Ucl U 1, ∀ g' ∈ Work.EKLRelCross.Ucl U 1,
      g * g' ∈ Work.EKLRelCross.Ucl U R :=
    fun g hg g' hg' => hR₀R (hR₀mul g hg g' hg')
  have hBBinv : ∀ g ∈ Work.EKLRelCross.Ucl U 1, ∀ g' ∈ Work.EKLRelCross.Ucl U 1,
      g * g'⁻¹ ∈ Work.EKLRelCross.Ucl U R :=
    fun g hg g' hg' => hR₀R (hR₀mulinv g hg g' hg')
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable X3
  obtain ⟨C, hCE, hCmeas, huniq⟩ :=
    Work.EKLRelCross.exists_borel_crossSection (B := Work.EKLRelCross.Ucl U 1)
      (A := Work.EKLRelCross.Ucl U R) (E := E)
      (d := TopologicalSpace.denseSeq X3) hEc (TopologicalSpace.denseRange_denseSeq X3)
      hBc hAc h1Ucl1 h1R hBinv hBB hBBinv hshrinkE hinjE
  refine ⟨E, C, hEc.isClosed, hEint, hCE, hCmeas, huniq, ?_⟩
  intro c hc u hu huc
  have hucE : u • c ∈ E := hCE huc
  have hcE : c ∈ E := hCE hc
  have huR : u ∈ Work.EKLRelCross.Ucl U R := hρR u hu
  obtain ⟨hgen1, _⟩ := hshrink (u • c) hucE.1 c hcE.1 (1 : SL3)
    (h1R (Work.EKLRelCross.Uball_subset_Ucl U 1 (Work.EKLRelCross.one_mem_Uball U (by norm_num))))
    u huR (by rw [one_smul])
  have hu1 : u ∈ Work.EKLRelCross.Ucl U 1 := by simpa using hgen1
  obtain ⟨b, hb, huniqb⟩ := huniq c hcE
  rw [huniqb u ⟨hu1, huc⟩, huniqb 1 ⟨h1Ucl1, by rw [one_smul]; exact hc⟩]

/-! ## 2. The local flower -/

theorem W_flower_local (h2 : Work.EKLContract.P_X3) {U : Subgroup Work.EKLContract.SL3}
    (hU : Work.EKLContract.IsHoro U) (x0 : Work.EKLContract.X3)
    (hfree : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x0 = u₂ • x0 → u₁ = u₂)
    (R : ℝ) (hR : 0 < R) :
    ∃ (Z : Set Work.EKLContract.X3) (m : MeasurableSpace Work.EKLContract.X3)
      (G O : Set Work.EKLContract.X3),
      IsOpen O ∧ x0 ∈ O ∧
      @MeasurableSet Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 G ∧ G ⊆ Z ∧
      Work.EKLContract.IsPlaqueAlgebra U Z m ∧ x0 ∈ G ∧
      O ∩ {x | ∀ u ∈ U, u • x = x → u = 1} ⊆ G ∧
      ∀ x ∈ G, Work.EKLContract.V R ∩ (U : Set Work.EKLContract.SL3)
        ⊆ Work.EKLContract.shape m U x := by
  classical
  have hUcl : IsClosed (U : Set SL3) := hU.1
  have hx0free : ∀ u ∈ U, u • x0 = x0 → u = 1 :=
    fun u hu h => hfree u hu 1 U.one_mem (by rw [h, one_smul])
  -- constants
  obtain ⟨K0, hK0⟩ := Work.EKLProd.inv_entries_bound 2 (by norm_num)
  set K : ℝ := |K0| + 2 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hK0lt : K0 + 1 < K := by rw [hKdef]; linarith [le_abs_self K0]
  set δ : ℝ := R + K + 3 * R * K + 1 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; nlinarith [hR, hKpos]
  have hδgtK : K < δ := by rw [hδdef]; nlinarith [hR, hKpos]
  have h1Vδ : (1 : SL3) ∈ V δ := (Work.EKLContract.Lemmas.V_open_one δ hδpos).2
  obtain ⟨Cδ, hCδ⟩ := Work.EKLProd.inv_entries_bound δ hδpos
  have hCδpos : 0 < Cδ := by
    have h := hCδ 1 h1Vδ 0 0
    rw [inv_one] at h
    have h1 : ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) 0 0 = 1 := by
      simp [Matrix.SpecialLinearGroup.coe_one]
    rw [h1, abs_one] at h
    linarith
  set b : ℝ := 3 * (Cδ + 2) * δ + (Cδ + 2) + δ + 1 with hbdef
  have hbpos : 0 < b := by rw [hbdef]; nlinarith [hCδpos, hδpos]
  set ρ : ℝ := max (b + 1) 3 with hρdef
  have hρ2 : 2 < ρ := by
    rw [hρdef]
    exact lt_of_lt_of_le (by norm_num : (2 : ℝ) < 3) (le_max_right (b + 1) 3)
  have hbρ : b ≤ ρ := by rw [hρdef]; linarith [le_max_left (b + 1) (3 : ℝ)]
  -- the bounded cross-section
  obtain ⟨E, C, hEclosed, hx0intE, hCE, hCmeas, hcover, hCSρ⟩ :=
    crossSection_local hUcl x0 hρ2 hfree
  -- the free set
  set Fr : Set X3 := {x : X3 | ∀ u ∈ U, u • x = x → u = 1} with hFrdef
  have hFrmeas : MeasurableSet Fr := Work.EKLRelCross.freeSet_borel hUcl
  have hx0Fr : x0 ∈ Fr := hx0free
  -- the separating family `W` (a countable basis, with `univ` prepended)
  obtain ⟨bas, hbas⟩ := TopologicalSpace.exists_seq_basis X3
  let W : ℕ → Set X3 := fun n => if n = 0 then Set.univ else bas (n - 1)
  have hW0 : W 0 = Set.univ := by simp [W]
  have hWopen : ∀ n, IsOpen (W n) := by
    intro n
    by_cases hn : n = 0
    · subst hn; rw [hW0]; exact isOpen_univ
    · have hn' : W n = bas (n - 1) := by simp [W, hn]
      rw [hn']
      exact hbas.isOpen (Set.mem_range_self (n - 1))
  have huniv_gen : MeasurableSet[MeasurableSpace.generateFrom (Set.range bas)]
      (Set.univ : Set X3) := by
    have hcov : (⋃ k, bas k) = (Set.univ : Set X3) := by
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨v, hv, hxv, -⟩ := hbas.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      obtain ⟨k, rfl⟩ := hv
      exact Set.mem_iUnion.mpr ⟨k, hxv⟩
    rw [← hcov]
    exact MeasurableSet.iUnion
      (fun k => MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self k))
  have hWgen : borel X3 = MeasurableSpace.generateFrom (Set.range W) := by
    rw [hbas.borel_eq_generateFrom]
    refine le_antisymm ?_ ?_
    · refine MeasurableSpace.generateFrom_le ?_
      rintro s ⟨k, rfl⟩
      have hbk : bas k = W (k + 1) := by simp [W]
      rw [hbk]
      exact MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self (k + 1))
    · refine MeasurableSpace.generateFrom_le ?_
      rintro s ⟨n, rfl⟩
      by_cases hn : n = 0
      · subst hn; rw [hW0]; exact huniv_gen
      · have hn' : W n = bas (n - 1) := by simp [W, hn]
        rw [hn']
        exact MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self (n - 1))
  have hsep : ∀ z ∈ C, ∀ z' ∈ C, (∀ n, z ∈ W n ↔ z' ∈ W n) → z = z' := by
    intro z _ z' _ hpat
    by_contra hne
    have hz : z ∈ ({(z' : X3)}ᶜ : Set X3) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact hne
    obtain ⟨v, hv, hzv, hvu⟩ := hbas.exists_subset_of_mem_open hz (isClosed_singleton.isOpen_compl)
    obtain ⟨k, rfl⟩ := hv
    have hWk : bas k = W (k + 1) := by simp [W]
    have hzW : z ∈ W (k + 1) := by rw [← hWk]; exact hzv
    have hz'W : z' ∈ W (k + 1) := (hpat (k + 1)).mp hzW
    rw [← hWk] at hz'W
    exact (hvu hz'W) rfl
  -- the cross-section property at the scale `b`
  have hCSb : ∀ z ∈ C, ∀ u ∈ U, u ∈ V b → u • z ∈ C → u = 1 := by
    intro z hz u huU huVb huzC
    exact hCSρ z hz u ⟨huU, fun i j => le_of_lt (lt_of_lt_of_le (huVb i j) hbρ)⟩ huzC
  -- the two product hypotheses
  have hprod : ∀ w ∈ U, w ∈ Work.EKLRelCross.Vinv δ → ∀ u ∈ U, u ∈ V δ → w * u ∈ V b := by
    intro w _ hwVinv u _ huV i j
    have hw1 : ∀ k l, |((w : Matrix (Fin 3) (Fin 3) ℝ)) k l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ Cδ + 2 := by
      intro k l
      have hw : |((w : Matrix (Fin 3) (Fin 3) ℝ)) k l| ≤ Cδ := by
        have h := hCδ w⁻¹ hwVinv k l
        simpa using h
      calc |((w : Matrix (Fin 3) (Fin 3) ℝ)) k l
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l|
          ≤ |((w : Matrix (Fin 3) (Fin 3) ℝ)) k l| + |(1 : Matrix (Fin 3) (Fin 3) ℝ) k l| :=
            abs_sub_le_abs_add' _ _
        _ ≤ Cδ + 1 := add_le_add hw (abs_one_apply_le' k l)
        _ ≤ Cδ + 2 := by linarith
    have hu1 : ∀ k l, |((u : Matrix (Fin 3) (Fin 3) ℝ)) k l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ δ := fun k l => le_of_lt (huV k l)
    rw [Matrix.SpecialLinearGroup.coe_mul]
    have h := mul_sub_one_entry_le' (A := (w : Matrix (Fin 3) (Fin 3) ℝ))
      (B := (u : Matrix (Fin 3) (Fin 3) ℝ)) (a := Cδ + 2) (b := δ)
      (by linarith) (le_of_lt hδpos) hw1 hu1 i j
    rw [hbdef]
    linarith
  have hprod2 : ∀ a ∈ U, a ∈ V δ → ∀ c ∈ U, c ∈ V δ → a⁻¹ * c ∈ V b := by
    intro a _ haV c _ hcV i j
    have ha1 : ∀ k l, |((a⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ Cδ + 2 := by
      intro k l
      have ha : |((a⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ Cδ := hCδ a haV k l
      calc |((a⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l|
          ≤ |((a⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l|
            + |(1 : Matrix (Fin 3) (Fin 3) ℝ) k l| := abs_sub_le_abs_add' _ _
        _ ≤ Cδ + 1 := add_le_add ha (abs_one_apply_le' k l)
        _ ≤ Cδ + 2 := by linarith
    have hc1 : ∀ k l, |((c : Matrix (Fin 3) (Fin 3) ℝ)) k l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ δ := fun k l => le_of_lt (hcV k l)
    rw [Matrix.SpecialLinearGroup.coe_mul]
    have h := mul_sub_one_entry_le' (A := ((a⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ))
      (B := (c : Matrix (Fin 3) (Fin 3) ℝ)) (a := Cδ + 2) (b := δ)
      (by linarith) (le_of_lt hδpos) ha1 hc1 i j
    rw [hbdef]
    linarith
  -- the plaque algebra
  have hPA : IsPlaqueAlgebra U
      (⋃ c ∈ C ∩ Fr, Work.EKLContract.atom (Work.EKLRelCross.flowerSigma U δ C W) c)
      (Work.EKLRelCross.flowerSigma U δ C W) :=
    Work.EKLRelCross.flower_plaqueAlgebra_bdd h2 hUcl hCmeas hCSb hδpos hprod hprod2
      hW0 hWopen hWgen hsep
  -- the atom computations
  have atom_of (t : SL3) (x : X3) (htU : t ∈ U) (htV2 : t ∈ V 2)
      (hzC : t • x ∈ C) :
      t⁻¹ ∈ V K ∧ t⁻¹ ∈ V δ ∧ t⁻¹ ∈ U := by
    have htinvVK : t⁻¹ ∈ V K := by
      intro i j
      have h := sub_one_entry_le' (A := ((t⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ))
        (C := K0) (fun k l => hK0 t htV2 k l) i j
      linarith [hK0lt]
    exact ⟨htinvVK, fun i j => lt_trans (htinvVK i j) hδgtK, U.inv_mem htU⟩
  refine ⟨(⋃ c ∈ C ∩ Fr, Work.EKLContract.atom (Work.EKLRelCross.flowerSigma U δ C W) c),
    Work.EKLRelCross.flowerSigma U δ C W, E ∩ Fr, interior E,
    isOpen_interior, hx0intE, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hEclosed.measurableSet.inter hFrmeas
  · -- `E ∩ Fr ⊆ Z`
    intro x hx
    obtain ⟨hxE, hxFr⟩ := hx
    obtain ⟨t, ht⟩ := hcover x hxE
    have htUcl : t ∈ Work.EKLRelCross.Ucl U 1 := ht.1.1
    have htU : t ∈ U := htUcl.1
    set z : X3 := t • x with hzdef
    have hzC : z ∈ C := ht.1.2
    have hzv : t⁻¹ • z = x := by rw [hzdef, ← mul_smul, inv_mul_cancel, one_smul]
    have htV2 : t ∈ V 2 := Ucl_one_subset_V_two' htUcl
    obtain ⟨htinvVK, htinvVδ, htinvU⟩ := atom_of t x htU htV2 hzC
    have hzFr : z ∈ Fr := by
      intro u huU huz
      have hfix : (t⁻¹ * u * t) • x = x := by
        calc (t⁻¹ * u * t) • x = t⁻¹ • (u • (t • x)) := by rw [mul_smul, mul_smul]
          _ = t⁻¹ • (t • x) := by rw [show u • (t • x) = t • x from huz]
          _ = x := by rw [← mul_smul, inv_mul_cancel, one_smul]
      have hmemU : t⁻¹ * u * t ∈ U := U.mul_mem (U.mul_mem (U.inv_mem htU) huU) htU
      have h1 : t⁻¹ * u * t = 1 := hxFr _ hmemU hfix
      calc u = t * (t⁻¹ * u * t) * t⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have hxatom : x ∈ Work.EKLContract.atom (Work.EKLRelCross.flowerSigma U δ C W) z := by
      rw [Work.EKLRelCross.atom_flower_local (U := U) (C := C) (b := b) hCSb hδpos hprod
            (W := W) hW0 hsep (v := (1 : SL3)) h1Vδ U.one_mem hzC (x := z) (by rw [one_smul])]
      exact ⟨t⁻¹, ⟨htinvVδ, htinvU⟩, hzv⟩
    exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨⟨hzC, hzFr⟩, hxatom⟩⟩
  · -- `IsPlaqueAlgebra U Z m`
    exact hPA
  · exact ⟨interior_subset hx0intE, hx0Fr⟩
  · exact fun x hx => ⟨interior_subset hx.1, hx.2⟩
  · -- the shape contains `V R ∩ U`
    intro x hx g hg
    obtain ⟨hxE, hxFr⟩ := hx
    obtain ⟨hgV, hgU⟩ := hg
    obtain ⟨t, ht⟩ := hcover x hxE
    have htUcl : t ∈ Work.EKLRelCross.Ucl U 1 := ht.1.1
    have htU : t ∈ U := htUcl.1
    set z : X3 := t • x with hzdef
    have hzC : z ∈ C := ht.1.2
    have hzv : t⁻¹ • z = x := by rw [hzdef, ← mul_smul, inv_mul_cancel, one_smul]
    have htV2 : t ∈ V 2 := Ucl_one_subset_V_two' htUcl
    obtain ⟨htinvVK, htinvVδ, htinvU⟩ := atom_of t x htU htV2 hzC
    rw [Work.EKLContract.shape]
    refine ⟨hgU, ?_⟩
    rw [Work.EKLRelCross.atom_flower_local (U := U) (C := C) (b := b) hCSb hδpos hprod
          (W := W) hW0 hsep (v := t⁻¹) htinvVδ htinvU hzC (x := x) hzv.symm]
    refine ⟨g * t⁻¹, ⟨?_, U.mul_mem hgU htinvU⟩, ?_⟩
    · intro i j
      rw [Matrix.SpecialLinearGroup.coe_mul]
      have h := mul_sub_one_entry_le' (A := (g : Matrix (Fin 3) (Fin 3) ℝ))
        (B := ((t⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) (a := R) (b := K)
        (le_of_lt hR) (le_of_lt hKpos) (fun k l => le_of_lt (hgV k l))
        (fun k l => le_of_lt (htinvVK k l)) i j
      rw [hδdef]
      linarith
    · show (g * t⁻¹) • z = g • x
      rw [mul_smul, hzv]

end Work.EKLRelCross.W
