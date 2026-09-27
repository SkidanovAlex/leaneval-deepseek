import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLRelCross.flower_balls
import Submission.Work.EKLRelCross.atom_flower
import Submission.Work.EKLRelCross.flowerSet_borel
import Submission.Work.EKLRelCross.pisa_crosssection
import Submission.Work.EKLRelCross.flower_plaqueAlgebra_bdd
import Submission.Work.EKLRelCross.atom_flower_local
import Submission.Work.EKLRelCross.CrossSectionSetup
import Submission.Work.EKLRelCross.exists_shrink_nhds
import Submission.Work.EKLRelCross.FlowerLocalAux.inj_nhds_local

/-!
# `Work.EKLRelCross.local_flower`

The local flower through a free point of the `U`-flow on `X₃ = SL₃(ℝ)/SL₃(ℤ)` (Pisa §6.7 +
§6.9–6.15): for a horospherical subgroup `U`, a point `x₀` with free `U`-orbit and every `R > 0`
there are a plaque algebra `(Z, m)`, an open set `O ∋ x₀` and a Borel set `G ⊆ Z` containing
`x₀` and every free point of `O`, such that at every `x ∈ G` the shape of the plaque algebra
contains the whole `R`-plaque `V R ∩ U ⊆ shape m U x`.

The construction: take the bounded cross-section `(E, C)` of the `U`-flow at `x₀` (with
`C ⊆ E` meeting every `Ucl U 1`-orbit of a point of `E` exactly once and being a `V b`-cross
section), let `W` be a countable basis of `X₃` (with `W 0 = X₃`) and let
`m = flowerSigma U δ C W`, `Z = ⋃_{c ∈ C ∩ free} atom m c`.  The atom of `m` at
`x = t⁻¹ • c` (`t ∈ Ucl U 1`, `c ∈ C`) is the plaque `(V δ ∩ U) • c`, so the shape at `x` is
`{u ∈ U | u * t⁻¹ ∈ V δ}` which contains `V R ∩ U` as soon as `V R · (Ucl U 1)⁻¹ ⊆ V δ`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-! ## Auxiliary estimates -/

private lemma abs_sub_le_abs_add' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_add_le a (-b)
  simpa [sub_eq_add_neg, abs_neg] using h

/-- **The size facts needed by the local flower.**  For every `R > 0` there are `δ, b > 0` such
that

* `(Ucl U 1)⁻¹ ⊆ V δ`,
* `V R · (Ucl U 1)⁻¹ ⊆ V δ`,
* `(Vinv δ) · (V δ) ⊆ V b` and `(V δ)⁻¹ (V δ) ⊆ V b`.

All three are entrywise estimates; the constants are chosen large enough that the entries of the
products stay below the prescribed radii. -/
lemma local_size_facts {R : ℝ} (hR : 0 < R) :
    ∃ δ b : ℝ, 0 < δ ∧ 0 < b ∧
      (∀ t : SL3, (∀ i j, |(t : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1) → t⁻¹ ∈ V δ) ∧
      (∀ u ∈ V R, ∀ t : SL3, (∀ i j, |(t : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1) → u * t⁻¹ ∈ V δ) ∧
      (∀ w : SL3, w⁻¹ ∈ V δ → ∀ u : SL3, u ∈ V δ → w * u ∈ V b) ∧
      (∀ a : SL3, a ∈ V δ → ∀ c : SL3, c ∈ V δ → a⁻¹ * c ∈ V b) := by
  obtain ⟨K0, hK0⟩ := Work.EKLProd.inv_entries_bound 2 (by norm_num)
  set K : ℝ := |K0| + 2 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  set δ : ℝ := R + K + 3 * R * K + 1 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    nlinarith [hR, hKpos, mul_pos hR hKpos]
  have hbnd : ∀ t : SL3, (∀ i j, |(t : Matrix (Fin 3) (Fin 3) ℝ) i j
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1) →
      ∀ i j, |(t⁻¹ : SL3) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < K := by
    intro t ht i j
    have htV2 : t ∈ V 2 := fun k l => lt_of_le_of_lt (ht k l) (by norm_num)
    have hb : |(t⁻¹ : SL3) i j| ≤ K0 := hK0 t htV2 i j
    have hone : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
      rw [Matrix.one_apply]; split_ifs <;> simp
    have h2 : |(t⁻¹ : SL3) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ |K0| + 1 := by
      calc |(t⁻¹ : SL3) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
          ≤ |(t⁻¹ : SL3) i j| + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| :=
            abs_sub_le_abs_add' _ _
        _ ≤ |(t⁻¹ : SL3) i j| + 1 := by linarith
        _ ≤ |K0| + 1 := by linarith [hb, le_abs_self K0]
    rw [hKdef]
    linarith [h2]
  obtain ⟨K1, hK1⟩ := Work.EKLProd.inv_entries_bound δ hδpos
  set Kδ : ℝ := |K1| + 2 with hKδdef
  have hKδpos : 0 < Kδ := by rw [hKδdef]; positivity
  set b : ℝ := Kδ + δ + 3 * Kδ * δ + 1 with hbdef
  have hbpos : 0 < b := by
    rw [hbdef]
    nlinarith [hδpos, hKδpos, mul_pos hδpos hKδpos]
  refine ⟨δ, b, hδpos, hbpos, ?_, ?_, ?_, ?_⟩
  · intro t ht i j
    have h1 := hbnd t ht i j
    show |(t⁻¹ : SL3) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < δ
    rw [hδdef]
    nlinarith [h1, hR, hKpos, mul_pos hR hKpos]
  · intro u hu t ht i j
    have hu' : ∀ k l, |(u : Matrix (Fin 3) (Fin 3) ℝ) k l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < R := hu
    have ht' : ∀ k l, |((t⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < K := hbnd t ht
    have h := entries_mul_sub_one_le (A := (u : Matrix (Fin 3) (Fin 3) ℝ))
      (B := ((t⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) (sA := R) (sB := K) i j hu' ht'
      (le_of_lt hR) (le_of_lt hKpos)
    have hcoe : ((u * t⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
        = (u : Matrix (Fin 3) (Fin 3) ℝ) * ((t⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) :=
      Matrix.SpecialLinearGroup.coe_mul u t⁻¹
    show |(u * t⁻¹ : SL3) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < δ
    rw [hcoe, hδdef]
    linarith
  · intro w hwVinv u huV i j
    have hw' : ∀ k l, |(w : Matrix (Fin 3) (Fin 3) ℝ) k l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < Kδ := by
      intro k l
      have hb : |(w : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ K1 := by
        have h := hK1 w⁻¹ hwVinv k l
        rwa [inv_inv] at h
      have hone : |(1 : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ 1 := by
        rw [Matrix.one_apply]; split_ifs <;> simp
      have h2 : |(w : Matrix (Fin 3) (Fin 3) ℝ) k l - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l|
          ≤ |K1| + 1 := by
        calc |(w : Matrix (Fin 3) (Fin 3) ℝ) k l - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l|
            ≤ |(w : Matrix (Fin 3) (Fin 3) ℝ) k l| + |(1 : Matrix (Fin 3) (Fin 3) ℝ) k l| :=
              abs_sub_le_abs_add' _ _
          _ ≤ |(w : Matrix (Fin 3) (Fin 3) ℝ) k l| + 1 := by linarith
          _ ≤ |K1| + 1 := by linarith [hb, le_abs_self K1]
      rw [hKδdef]
      linarith [h2]
    have hu' : ∀ k l, |(u : Matrix (Fin 3) (Fin 3) ℝ) k l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < δ := huV
    have h := entries_mul_sub_one_le (A := (w : Matrix (Fin 3) (Fin 3) ℝ))
      (B := (u : Matrix (Fin 3) (Fin 3) ℝ)) (sA := Kδ) (sB := δ) i j hw' hu'
      (le_of_lt hKδpos) (le_of_lt hδpos)
    have hcoe : ((w * u : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
        = (w : Matrix (Fin 3) (Fin 3) ℝ) * (u : Matrix (Fin 3) (Fin 3) ℝ) :=
      Matrix.SpecialLinearGroup.coe_mul w u
    show |(w * u : SL3) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < b
    rw [hcoe, hbdef]
    linarith
  · intro a haV c hcV i j
    have ha' : ∀ k l, |((a⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < Kδ := by
      intro k l
      have hb : |((a⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ K1 := hK1 a haV k l
      have hone : |(1 : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ 1 := by
        rw [Matrix.one_apply]; split_ifs <;> simp
      have h2 : |((a⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ |K1| + 1 := by
        calc |((a⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l
              - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l|
            ≤ |((a⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l|
              + |(1 : Matrix (Fin 3) (Fin 3) ℝ) k l| := abs_sub_le_abs_add' _ _
          _ ≤ |((a⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l| + 1 := by linarith
          _ ≤ |K1| + 1 := by linarith [hb, le_abs_self K1]
      rw [hKδdef]
      linarith [h2]
    have hc' : ∀ k l, |(c : Matrix (Fin 3) (Fin 3) ℝ) k l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < δ := hcV
    have h := entries_mul_sub_one_le (A := ((a⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ))
      (B := (c : Matrix (Fin 3) (Fin 3) ℝ)) (sA := Kδ) (sB := δ) i j ha' hc'
      (le_of_lt hKδpos) (le_of_lt hδpos)
    have hcoe : ((a⁻¹ * c : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
        = ((a⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) * (c : Matrix (Fin 3) (Fin 3) ℝ) :=
      Matrix.SpecialLinearGroup.coe_mul a⁻¹ c
    show |(a⁻¹ * c : SL3) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < b
    rw [hcoe, hbdef]
    linarith

/-! ## Freeness propagates along the `U`-leaf -/

lemma free_smul_of_free {U : Subgroup SL3} {x : X3} {t : SL3} (ht : t ∈ U)
    (hx : ∀ u ∈ U, u • x = x → u = 1) :
    ∀ u ∈ U, u • (t • x) = t • x → u = 1 := by
  intro u hu huz
  have h1 : (t⁻¹ * u * t) • x = x := by
    rw [mul_smul, mul_smul, huz, smul_smul, inv_mul_cancel, one_smul]
  have h2 : t⁻¹ * u * t ∈ U := U.mul_mem (U.mul_mem (U.inv_mem ht) hu) ht
  have h3 : t⁻¹ * u * t = 1 := hx _ h2 h1
  have h4 : u = t * (t⁻¹ * u * t) * t⁻¹ := by group
  rw [h4, h3]
  group

/-! ## A countable basis `W` with `W 0 = univ` -/

lemma exists_basis_W : ∃ W : ℕ → Set X3, W 0 = Set.univ ∧ (∀ n, IsOpen (W n)) ∧
    borel X3 = MeasurableSpace.generateFrom (Set.range W) ∧
    (∀ z z' : X3, z ≠ z' → ∃ n, ¬ (z ∈ W n ↔ z' ∈ W n)) := by
  obtain ⟨β, hβ⟩ := TopologicalSpace.exists_seq_basis X3
  let W : ℕ → Set X3 := fun n => if n = 0 then Set.univ else β (n - 1)
  have hW0 : W 0 = Set.univ := by simp [W]
  have hWsucc : ∀ k, W (k + 1) = β k := by
    intro k
    simp [W]
  refine ⟨W, hW0, ?_, ?_, ?_⟩
  · intro n
    cases n with
    | zero => rw [hW0]; exact isOpen_univ
    | succ k => rw [hWsucc k]; exact hβ.isOpen (Set.mem_range_self k)
  · have hrange : Set.range W = insert Set.univ (Set.range β) := by
      ext s
      constructor
      · rintro ⟨n, rfl⟩
        cases n with
        | zero => exact Set.mem_insert _ _
        | succ k => exact Set.mem_insert_of_mem _ (Set.mem_range_self k)
      · intro hs
        rcases hs with rfl | ⟨k, rfl⟩
        · exact ⟨0, hW0⟩
        · exact ⟨k + 1, hWsucc k⟩
    have hborel : borel X3 = MeasurableSpace.generateFrom (Set.range β) :=
      borel_eq_generateFrom_of_subbasis hβ.eq_generateFrom
    rw [hborel, hrange, MeasurableSpace.generateFrom_insert_univ]
  · intro z z' hne
    obtain ⟨u, v, hu, hv, hzu, hz'v, hdis⟩ := t2_separation hne
    obtain ⟨s, hs, hzs, hsu⟩ := hβ.exists_subset_of_mem_open hzu hu
    obtain ⟨k, rfl⟩ := hs
    have hz'k : z' ∉ β k := fun h => (Set.disjoint_left.mp hdis) (hsu h) hz'v
    refine ⟨k + 1, ?_⟩
    rw [hWsucc k]
    intro hiff
    exact hz'k (hiff.mp hzs)

/-! ## The bounded cross-section of the `U`-flow at a free point -/

/-- **Pisa 6.7 + 6.9–6.12** (bounded form).  For a closed subgroup `U ≤ SL₃(ℝ)`, a point `x₀` with
free `U`-orbit and a scale `ρ > 2` there are an open neighbourhood `E` of `x₀` and a Borel set
`C ⊆ E` such that every point of `E` is moved into `C` by an element of the closed unit
displacement ball `Ucl U 1`, and `C` meets no `Ucl U ρ`-orbit twice.

This is `Work.EKLRelCross.pisa_crosssection` with the injectivity input supplied by the
sorry-free `Work.EKLRelCross.FlowerLocalAux.inj_nhds_local` instead of
`Work.EKLRelCross.exists_inj_nhds`. -/
lemma cross_data (h2 : P_X3) {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3)) {x0 : X3}
    (hfree : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x0 = u₂ • x0 → u₁ = u₂) {ρ : ℝ} (hρ : 2 < ρ) :
    ∃ E C : Set X3, IsClosed E ∧ x0 ∈ interior E ∧ C ⊆ E ∧ MeasurableSet C ∧
      (∀ x ∈ E, ∃ t ∈ Ucl U 1, t • x ∈ C) ∧
      (∀ c ∈ C, ∀ u ∈ Ucl U ρ, u • c ∈ C → u = 1) := by
  classical
  obtain ⟨R₀, hR₀inv, hR₀mul, hR₀mulinv⟩ := exists_Ucl_bound U
  set R : ℝ := max R₀ ρ with hRdef
  have hRρ : ρ ≤ R := le_max_right _ _
  have hRR₀ : R₀ ≤ R := le_max_left _ _
  have hRpos : 0 ≤ R := le_trans (by linarith : (0 : ℝ) ≤ ρ) hRρ
  have hR1 : (1 : ℝ) ≤ R := le_trans (by linarith : (1 : ℝ) ≤ ρ) hRρ
  obtain ⟨E₁, hE₁c, hE₁int, hshrink⟩ := exists_shrink_nhds hUcl x0 hfree (R := R) hRpos
  obtain ⟨E₂, hE₂c, hE₂int, hinj₂⟩ :=
    Work.EKLRelCross.FlowerLocalAux.inj_nhds_local hUcl x0 hfree (R := R)
  set E : Set X3 := E₁ ∩ E₂ with hEdef
  have hEc : IsCompact E := hE₁c.inter hE₂c
  have hEint : x0 ∈ interior E := by
    rw [hEdef, interior_inter]
    exact ⟨hE₁int, hE₂int⟩
  have hshrinkE : ∀ x ∈ E, ∀ x' ∈ E, ∀ u ∈ Ucl U R, ∀ u' ∈ Ucl U R, u • x = u' • x' →
      u' * u⁻¹ ∈ Ucl U 1 ∧ u⁻¹ * u' ∈ Ucl U 1 :=
    fun x hx x' hx' u hu u' hu' h => hshrink x hx.1 x' hx'.1 u hu u' hu' h
  have hinjE : ∀ x ∈ E, ∀ u ∈ Ucl U 1, ∀ u' ∈ Ucl U 1, u • x = u' • x → u = u' :=
    fun x hx u hu u' hu' h => hinj₂ x hx.2 u (Ucl_mono hR1 hu) u' (Ucl_mono hR1 hu') h
  have h1R : Ucl U 1 ⊆ Ucl U R := Ucl_mono hR1
  have hR₀R : Ucl U R₀ ⊆ Ucl U R := Ucl_mono hRR₀
  have hBc : IsCompact (Ucl U 1) := isCompact_Ucl hUcl 1
  have hAc : IsCompact (Ucl U R) := isCompact_Ucl hUcl R
  have h1Ucl1 : (1 : SL3) ∈ Ucl U 1 := Uball_subset_Ucl U 1 (one_mem_Uball U (by norm_num))
  have hρR : ∀ g ∈ Ucl U ρ, g ∈ Ucl U R := Ucl_mono hRρ
  have hBinv : ∀ g ∈ Ucl U 1, g⁻¹ ∈ Ucl U R := fun g hg => hR₀R (hR₀inv g hg)
  have hBB : ∀ g ∈ Ucl U 1, ∀ g' ∈ Ucl U 1, g * g' ∈ Ucl U R :=
    fun g hg g' hg' => hR₀R (hR₀mul g hg g' hg')
  have hBBinv : ∀ g ∈ Ucl U 1, ∀ g' ∈ Ucl U 1, g * g'⁻¹ ∈ Ucl U R :=
    fun g hg g' hg' => hR₀R (hR₀mulinv g hg g' hg')
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable X3
  obtain ⟨C, hCE, hCmeas, huniq⟩ :=
    exists_borel_crossSection (B := Ucl U 1) (A := Ucl U R) (E := E)
      (d := TopologicalSpace.denseSeq X3) hEc (TopologicalSpace.denseRange_denseSeq X3)
      hBc hAc h1Ucl1 h1R hBinv hBB hBBinv hshrinkE hinjE
  refine ⟨E, C, hEc.isClosed, hEint, hCE, hCmeas, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, ht, htx⟩ := huniq x hx
    exact ⟨t, ht.1, ht.2⟩
  · intro c hc u hu huc
    have hucE : u • c ∈ E := hCE huc
    have hcE : c ∈ E := hCE hc
    have huR : u ∈ Ucl U R := hρR u hu
    obtain ⟨hgen1, _⟩ := hshrinkE (u • c) hucE c hcE (1 : SL3)
      (h1R (Uball_subset_Ucl U 1 (one_mem_Uball U (by norm_num)))) u huR (by rw [one_smul])
    have hu1 : u ∈ Ucl U 1 := by simpa using hgen1
    obtain ⟨b', hb', huniqb⟩ := huniq c hcE
    rw [huniqb u ⟨hu1, huc⟩, huniqb 1 ⟨h1Ucl1, by rw [one_smul]; exact hc⟩]

/-! ## The local flower -/

theorem local_flower (h2 : Work.EKLContract.P_X3) {U : Subgroup Work.EKLContract.SL3}
    (hU : Work.EKLContract.IsHoro U) (x0 : Work.EKLContract.X3)
    (hfree : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x0 = u₂ • x0 → u₁ = u₂)
    (R : ℝ) (hR : 0 < R) :
    ∃ (Z : Set Work.EKLContract.X3) (m : MeasurableSpace Work.EKLContract.X3)
      (G O : Set Work.EKLContract.X3),
      IsOpen O ∧ x0 ∈ O ∧ @MeasurableSet Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 G ∧
      G ⊆ Z ∧ Work.EKLContract.IsPlaqueAlgebra U Z m ∧ x0 ∈ G ∧
      O ∩ {x | ∀ u ∈ U, u • x = x → u = 1} ⊆ G ∧
      ∀ x ∈ G, Work.EKLContract.V R ∩ (U : Set Work.EKLContract.SL3)
        ⊆ Work.EKLContract.shape m U x := by
  classical
  have hUcl : IsClosed (U : Set SL3) := hU.1
  obtain ⟨δ, b, hδ, hb, htin, hsize, hprod, hprod2⟩ := local_size_facts (R := R) hR
  obtain ⟨ρ, hρ2, hbρ⟩ : ∃ ρ : ℝ, 2 < ρ ∧ b ≤ ρ :=
    ⟨max b 3, lt_of_lt_of_le (by norm_num) (le_max_right _ _), le_max_left _ _⟩
  obtain ⟨E, C, hEcl, hxE, hCE, hCmeas, hcover, hCSρ⟩ := cross_data h2 hUcl hfree hρ2
  obtain ⟨W, hW0, hWopen, hWgen, hWsep⟩ := exists_basis_W
  have hCS : ∀ z ∈ C, ∀ u ∈ U, u ∈ V b → u • z ∈ C → u = 1 := by
    intro z hz u huU huV huz
    exact hCSρ z hz u ⟨huU, fun i j => le_trans (le_of_lt (huV i j)) hbρ⟩ huz
  have hsep : ∀ z ∈ C, ∀ z' ∈ C, (∀ n, z ∈ W n ↔ z' ∈ W n) → z = z' := by
    intro z _ z' _ h
    by_contra hne
    obtain ⟨n, hn⟩ := hWsep z z' hne
    exact hn (h n)
  have hprodF : ∀ w ∈ U, w ∈ Vinv δ → ∀ u ∈ U, u ∈ V δ → w * u ∈ V b :=
    fun w _ hw u _ hu => hprod w (mem_Vinv_iff.mp hw) u hu
  have hprod2F : ∀ a ∈ U, a ∈ V δ → ∀ c ∈ U, c ∈ V δ → a⁻¹ * c ∈ V b :=
    fun a _ ha c _ hc => hprod2 a ha c hc
  have hplaque : IsPlaqueAlgebra U
      (⋃ c ∈ C ∩ {x : X3 | ∀ u ∈ U, u • x = x → u = 1}, atom (flowerSigma U δ C W) c)
      (flowerSigma U δ C W) :=
    flower_plaqueAlgebra_bdd h2 hUcl hCmeas hCS hδ hprodF hprod2F hW0 hWopen hWgen hsep
  refine ⟨(⋃ c ∈ C ∩ {x : X3 | ∀ u ∈ U, u • x = x → u = 1},
            atom (flowerSigma U δ C W) c),
          flowerSigma U δ C W,
          interior E ∩ {x : X3 | ∀ u ∈ U, u • x = x → u = 1}, interior E,
          isOpen_interior, hxE, ?_, ?_, hplaque, ?_, ?_, ?_⟩
  · exact isOpen_interior.measurableSet.inter (freeSet_borel hUcl)
  · intro x hx
    obtain ⟨hxE, hxFr⟩ := hx
    obtain ⟨t, htUcl, htz⟩ := hcover x (interior_subset hxE)
    have htU : t ∈ U := htUcl.1
    have htle : ∀ i j, |(t : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := htUcl.2
    have htinvδ : t⁻¹ ∈ V δ := htin t htle
    have htinvU : t⁻¹ ∈ U := U.inv_mem htU
    have hzfree : t • x ∈ {y : X3 | ∀ u ∈ U, u • y = y → u = 1} := free_smul_of_free htU hxFr
    have hxeq : x = t⁻¹ • (t • x) := (inv_smul_smul t x).symm
    have hatomz : atom (flowerSigma U δ C W) (t • x)
        = (fun u : SL3 => u • (t • x)) '' (V δ ∩ (U : Set SL3)) :=
      atom_flower_local hCS hδ hprodF hW0 hsep
        (Work.EKLContract.Lemmas.V_open_one δ hδ).2 U.one_mem htz (by rw [one_smul])
    refine Set.mem_iUnion.mpr ⟨t • x, Set.mem_iUnion.mpr ⟨⟨htz, hzfree⟩, ?_⟩⟩
    rw [hatomz]
    exact ⟨t⁻¹, ⟨htinvδ, htinvU⟩, hxeq.symm⟩
  · refine ⟨hxE, ?_⟩
    intro u hu hux
    exact hfree u hu 1 U.one_mem (by rw [hux, one_smul])
  · intro x hx
    exact hx
  · intro x hx
    obtain ⟨hxE, hxFr⟩ := hx
    obtain ⟨t, htUcl, htz⟩ := hcover x (interior_subset hxE)
    have htU : t ∈ U := htUcl.1
    have htle : ∀ i j, |(t : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := htUcl.2
    have htinvδ : t⁻¹ ∈ V δ := htin t htle
    have htinvU : t⁻¹ ∈ U := U.inv_mem htU
    have hxeq : x = t⁻¹ • (t • x) := (inv_smul_smul t x).symm
    have hatom : atom (flowerSigma U δ C W) x
        = (fun u : SL3 => u • (t • x)) '' (V δ ∩ (U : Set SL3)) :=
      atom_flower_local hCS hδ hprodF hW0 hsep htinvδ htinvU htz hxeq
    intro u₀ hu₀
    have hu₀R : u₀ ∈ V R := hu₀.1
    have hu₀U : u₀ ∈ U := hu₀.2
    have hscale : u₀ * t⁻¹ ∈ V δ := hsize u₀ hu₀R t htle
    refine ⟨hu₀U, ?_⟩
    rw [hatom]
    exact ⟨u₀ * t⁻¹, ⟨hscale, U.mul_mem hu₀U htinvU⟩, by
      show (u₀ * t⁻¹) • (t • x) = u₀ • x
      rw [smul_smul, mul_assoc, inv_mul_cancel, mul_one]⟩

end Work.EKLRelCross
