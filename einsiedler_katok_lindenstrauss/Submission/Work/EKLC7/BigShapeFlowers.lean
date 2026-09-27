import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLC7.LeafwiseGeom
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLRelCross.flower
import Submission.Work.EKLRelCross.flower_balls
import Submission.Work.EKLRelCross.atom_flower_local
import Submission.Work.EKLRelCross.flower_plaqueAlgebra_bdd
import Submission.Work.EKLRelCross.free_orbits_of_contracting
import Submission.Work.EKLRelCross.freeSet_borel
import Submission.Work.EKLRelCross.pisa_crosssection
import Submission.Work.EKLProd.inv_entries_bound

/-!
# `Work.EKLC7.BigShapeFlowers`

Flowers of `U`-plaques exist (Pisa 6.13–6.15): for a horospherical `U ≤ SL₃(ℝ)`, a probability
measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` and any `R > 0`, there are countably many plaque algebras
`(Z n, m n)` with measurable bases `G n ⊆ Z n` whose union is conull and at whose points the whole
`R`-plaque of the point lies in the atom of the plaque algebra.

The proof is the assembly of the following ingredients.

* `free_orbits_of_contracting` — a.e. freedom of the `U`-orbits.
* the local cross-section of Pisa 6.7 + 6.9–6.12 (`Work.EKLRelCross.pisa_crosssection`, proved),
  repackaged below as `crossSection_of_pisa`: through every free point there is a closed
  neighbourhood `E` and a Borel `C ⊆ E` such that every `x ∈ E` is `u • z` with `z ∈ C` and
  `u ∈ V 10 ∩ U` (the covering element is the inverse of an element of the closed unit ball
  `Ucl U 1`; the inverse of an element of `SL₃` is its adjugate, so entries `≤ 2` give entries
  within `9` of the identity), and `C` meets each `U`-orbit at most once inside any prescribed
  displacement ball `V b`.
* `FlowerSizeBig` below — the scale bookkeeping adapted to the covering element `V 10`.
* `atom_flower_local` — the atom of the flower σ-algebra `flowerSigma U δ C W` at a flower point
  is the plaque `(V δ ∩ U) • z`.
* `flower_plaqueAlgebra_bdd` — `flowerSigma U δ C W` is a plaque algebra on the union of the
  atoms over the free points of `C`.
* a countable basis of `X₃` turns the family of cross-sections (one for every free point) into a
  countable family of flowers whose bases are conull.

The main auxiliary results are `FlowerSizeBig` (the scale bookkeeping, Section 1),
`bigShapeFlowers_core` (Section 2, the measure-theoretic assembly from a cross-section through
every free point) and `crossSection_of_pisa` (Section 3); `BigShapeFlowers` is their combination.

-/


set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

noncomputable section

namespace Work.EKLC7

open Work.EKLContract

/-! ## 1. The scale bookkeeping: `V R · V 10 ⊆ V δ` and the two product facts -/

private lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)

/-- If `w⁻¹ ∈ V δ` then every entry of `w` is within `|C| + 2` of the corresponding entry of
the identity, where `C` is the adjugate bound for the entries of inverses of elements of `V δ`. -/
private lemma entries_sub_one_lt_of_inv_mem_V {δ : ℝ} (hδ : 0 < δ) :
    ∃ E : ℝ, 0 < E ∧ ∀ w : SL3, w⁻¹ ∈ V δ → ∀ i j : Fin 3,
      |(w : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < E := by
  obtain ⟨C, hC⟩ := Work.EKLProd.inv_entries_bound δ hδ
  refine ⟨|C| + 2, by positivity, ?_⟩
  intro w hw i j
  have hw1 : |(w : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ |C| := by
    have h := hC w⁻¹ hw i j
    rw [inv_inv] at h
    exact le_trans h (le_abs_self C)
  have hone : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
    rw [Matrix.one_apply]; split <;> simp
  calc |(w : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
      ≤ |(w : Matrix (Fin 3) (Fin 3) ℝ) i j| + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| :=
        abs_sub_le_abs_add _ _
    _ ≤ |C| + 1 := add_le_add hw1 hone
    _ < |C| + 2 := by linarith

/-- **The scale bookkeeping of the flower construction, for the covering element `V 10`.**

For every `R > 0` there are `δ > 10` and `b > 0` such that

* `V R · V 10 ⊆ V δ` (the `R`-plaque of a flower point `x = u₀ • z`, `u₀ ∈ V 10`, stays inside
  the atom `(V δ ∩ U) • z` of the flower);
* `(Vinv δ ∩ U) · (V δ ∩ U) ⊆ V b` (the product condition of `atom_flower_local`);
* `(V δ ∩ U)⁻¹ · (V δ ∩ U) ⊆ V b` (the product condition of `flower_plaqueAlgebra_bdd`). -/
theorem FlowerSizeBig {U : Subgroup SL3} {R : ℝ} (hR : 0 < R) :
    ∃ (δ b : ℝ), 10 < δ ∧ 0 < b ∧
      (∀ u ∈ V R, ∀ u₁ ∈ V 10, u * u₁ ∈ V δ) ∧
      (∀ w ∈ U, w ∈ Work.EKLRelCross.Vinv δ → ∀ u ∈ U, u ∈ V δ → w * u ∈ V b) ∧
      (∀ a ∈ U, a ∈ V δ → ∀ c ∈ U, c ∈ V δ → a⁻¹ * c ∈ V b) := by
  set δ : ℝ := max 11 (R + 10 + 3 * R * 10 + 1) with hδdef
  have hδ10 : 10 < δ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hδR10 : R + 10 + 3 * R * 10 < δ :=
    lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hδpos : 0 < δ := by linarith
  obtain ⟨E, hEpos, hE⟩ := entries_sub_one_lt_of_inv_mem_V (δ := δ) hδpos
  refine ⟨δ, E + δ + 3 * E * δ + 1, hδ10, by nlinarith [hEpos, hδpos], ?_, ?_, ?_⟩
  · intro u hu u₁ hu₁ i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    have h := Work.EKLRelCross.entries_mul_sub_one_le
      (A := (u : Matrix (Fin 3) (Fin 3) ℝ)) (B := (u₁ : Matrix (Fin 3) (Fin 3) ℝ))
      i j (fun k l => hu k l) (fun k l => hu₁ k l) (le_of_lt hR) (by norm_num)
    linarith
  · intro w _ hwVinv u _ huV i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    have h := Work.EKLRelCross.entries_mul_sub_one_le
      (A := (w : Matrix (Fin 3) (Fin 3) ℝ)) (B := (u : Matrix (Fin 3) (Fin 3) ℝ))
      i j (fun k l => hE w hwVinv k l) (fun k l => huV k l)
      (le_of_lt hEpos) (le_of_lt hδpos)
    linarith
  · intro a _ haV c _ hcV i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    have h := Work.EKLRelCross.entries_mul_sub_one_le
      (A := ((a⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) (B := (c : Matrix (Fin 3) (Fin 3) ℝ))
      i j (fun k l => hE a⁻¹ (by simpa [inv_inv] using haV) k l) (fun k l => hcV k l)
      (le_of_lt hEpos) (le_of_lt hδpos)
    linarith

/-! ## 2. The measure-theoretic assembly -/

/-- The assembly of the family of flowers from a cross-section through every free point: if for
every free point `x₀` and every `b > 0` there are a *closed* neighbourhood `E ∋ x₀` and a Borel
`C ⊆ E` such that every `y ∈ E` is `u • z` with `z ∈ C` and `u ∈ V 10 ∩ U`, and `C` meets each
`U`-orbit at most once inside `V b`, then the conclusion of `BigShapeFlowers` holds. -/
theorem bigShapeFlowers_core (h2 : P_X3) (μ : MeasureTheory.Measure X3)
    [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
    (hfree_ae : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1)
    {R : ℝ} (hR : 0 < R)
    (hcross : ∀ x : X3, (∀ u ∈ U, u • x = x → u = 1) → ∀ b : ℝ, 0 < b →
      ∃ (E C : Set X3), IsClosed E ∧ x ∈ interior E ∧ C ⊆ E ∧ MeasurableSet C ∧
        (∀ y ∈ E, ∃ z ∈ C, ∃ u ∈ U, u ∈ V 10 ∧ u • z = y) ∧
        (∀ z ∈ C, ∀ u ∈ U, u ∈ V b → u • z ∈ C → u = 1)) :
    ∃ (Z G : ℕ → Set X3) (m : ℕ → MeasurableSpace X3),
      (∀ n, IsPlaqueAlgebra U (Z n) (m n)) ∧
      (∀ n, MeasurableSet (G n) ∧ G n ⊆ Z n) ∧
      μ (⋃ n, G n)ᶜ = 0 ∧
      (∀ n, ∀ x ∈ G n, ∀ u ∈ (V R ∩ (U : Set SL3)), u • x ∈ atom (m n) x) := by
  classical
  -- scale data
  obtain ⟨δ, b, h10δ, hb, hsize, hprod, hprod2⟩ := FlowerSizeBig (U := U) hR
  have hδpos : 0 < δ := by linarith
  have hV10δ : V 10 ⊆ V δ := fun g hg i j => lt_of_lt_of_le (hg i j) (le_of_lt h10δ)
  have hV1δ : (1 : SL3) ∈ V δ := (Work.EKLContract.Lemmas.V_open_one δ hδpos).2
  -- the free locus
  set Fr : Set X3 := {x : X3 | ∀ u ∈ U, u • x = x → u = 1} with hFrdef
  have hFrmeas : MeasurableSet Fr := by rw [hFrdef]; exact Work.EKLRelCross.freeSet_borel hUcl
  have hFraec : μ Frᶜ = 0 := by
    have hset : Frᶜ = {a : X3 | ¬(∀ u ∈ U, u • a = a → u = 1)} := by
      rw [hFrdef]; ext a; simp
    rw [hset]
    exact MeasureTheory.ae_iff.mp hfree_ae
  -- a countable basis, with `univ` added as the 0-th element
  obtain ⟨O, hObas⟩ := TopologicalSpace.exists_seq_basis X3
  set W : ℕ → Set X3 := (fun n => if n = 0 then Set.univ else O (n - 1)) with hWdef
  have hW_succ : ∀ k : ℕ, W (k + 1) = O k := by
    intro k; simp only [hWdef, Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
  have hW0 : W 0 = Set.univ := by simp only [hWdef, ↓reduceIte]
  have hWopen : ∀ n, IsOpen (W n) := by
    intro n
    by_cases hn : n = 0
    · rw [hn, hW0]; exact isOpen_univ
    · rw [show W n = O (n - 1) from by simp only [hWdef, hn, ↓reduceIte]]
      exact hObas.isOpen (Set.mem_range_self (n - 1))
  have hWgen : borel X3 = MeasurableSpace.generateFrom (Set.range W) := by
    have hle1 : MeasurableSpace.generateFrom (Set.range O)
        ≤ MeasurableSpace.generateFrom (Set.range W) := by
      refine MeasurableSpace.generateFrom_le ?_
      rintro t ⟨k, rfl⟩
      rw [← hW_succ k]
      exact MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self (k + 1))
    have hle2 : MeasurableSpace.generateFrom (Set.range W)
        ≤ MeasurableSpace.generateFrom (Set.range O) := by
      refine MeasurableSpace.generateFrom_le ?_
      rintro t ⟨n, rfl⟩
      by_cases hn : n = 0
      · rw [hn, hW0]
        have hcov : (Set.univ : Set X3) ⊆ ⋃ k, O k := by
          intro z _
          obtain ⟨s, hs, hzs, -⟩ :=
            hObas.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
          obtain ⟨k, rfl⟩ := hs
          exact Set.mem_iUnion.mpr ⟨k, hzs⟩
        rw [Set.Subset.antisymm hcov (Set.subset_univ _)]
        exact MeasurableSet.iUnion fun k =>
          MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self k)
      · rw [show W n = O (n - 1) from by simp only [hWdef, hn, ↓reduceIte]]
        exact MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self (n - 1))
    rw [hObas.borel_eq_generateFrom]
    exact le_antisymm hle1 hle2
  -- the `W`-patterns separate the points of `X₃`
  have hsep_all : ∀ z z' : X3, (∀ n, z ∈ W n ↔ z' ∈ W n) → z = z' := by
    intro z z' hpat
    by_contra hne
    obtain ⟨u, v, hu, hv, hzu, hz'v, hdisj⟩ := t2_separation hne
    obtain ⟨t, ht, hzt, htu⟩ := (hObas.isOpen_iff.mp hu) z hzu
    obtain ⟨k, rfl⟩ := ht
    have h1 : z ∈ W (k + 1) := by rw [hW_succ k]; exact hzt
    have h2 : z' ∉ W (k + 1) := by
      rw [hW_succ k]
      intro hmem
      exact (Set.disjoint_left.mp hdisj (htu hmem)) hz'v
    exact h2 ((hpat (k + 1)).mp h1)
  -- the family of cross-section data
  let Data : Set (Set X3 × Set X3) :=
    {d | ∃ x : X3, (∀ u ∈ U, u • x = x → u = 1) ∧ IsClosed d.1 ∧ x ∈ interior d.1 ∧
      d.2 ⊆ d.1 ∧ MeasurableSet d.2 ∧
      (∀ y ∈ d.1, ∃ z ∈ d.2, ∃ u ∈ U, u ∈ V 10 ∧ u • z = y) ∧
      (∀ z ∈ d.2, ∀ u ∈ U, u ∈ V b → u • z ∈ d.2 → u = 1)}
  have hDataprop : ∀ d ∈ Data, IsClosed d.1 ∧ d.2 ⊆ d.1 ∧ MeasurableSet d.2 ∧
      (∀ y ∈ d.1, ∃ z ∈ d.2, ∃ u ∈ U, u ∈ V 10 ∧ u • z = y) ∧
      (∀ z ∈ d.2, ∀ u ∈ U, u ∈ V b → u • z ∈ d.2 → u = 1) := by
    rintro d ⟨x, -, h1, -, h3, h4, h5, h6⟩
    exact ⟨h1, h3, h4, h5, h6⟩
  -- for each basis element, one cross-section datum covering it
  let selPair : ℕ → Option (Set X3 × Set X3) := fun n =>
    if h : ∃ d ∈ Data, O n ⊆ d.1 then some (Classical.choose h) else none
  have hselmem : ∀ n d, selPair n = some d → d ∈ Data := by
    intro n d hd
    by_cases h : ∃ d ∈ Data, O n ⊆ d.1
    · have h1 : selPair n = some (Classical.choose h) := dif_pos h
      rw [h1] at hd
      rw [Option.some.injEq] at hd
      rw [← hd]
      exact (Classical.choose_spec h).1
    · have h1 : selPair n = none := dif_neg h
      rw [h1] at hd
      exact absurd hd (by simp)
  -- the flowers
  let Z : ℕ → Set X3 := fun n => match selPair n with
    | some d => ⋃ c ∈ d.2 ∩ Fr, atom (Work.EKLRelCross.flowerSigma U δ d.2 W) c
    | none => ∅
  let m : ℕ → MeasurableSpace X3 := fun n => match selPair n with
    | some d => Work.EKLRelCross.flowerSigma U δ d.2 W
    | none => ⊥
  let G : ℕ → Set X3 := fun n => match selPair n with
    | some d => d.1 ∩ Fr
    | none => ∅
  refine ⟨Z, G, m, ?_, ?_, ?_, ?_⟩
  · -- (i) each member is a plaque algebra
    intro n
    cases hsel : selPair n with
    | none =>
      have hZ : Z n = ∅ := by simp only [Z, hsel]
      have hm : m n = ⊥ := by simp only [m, hsel]
      rw [hZ, hm]
      exact isPlaqueAlgebra_empty U
    | some d =>
      obtain ⟨hclosed, hsub, hmeas, hhit, hcs⟩ := hDataprop d (hselmem n d hsel)
      have hZ : Z n = ⋃ c ∈ d.2 ∩ Fr, atom (Work.EKLRelCross.flowerSigma U δ d.2 W) c := by
        simp only [Z, hsel]
      have hm : m n = Work.EKLRelCross.flowerSigma U δ d.2 W := by simp only [m, hsel]
      rw [hZ, hm, hFrdef]
      refine Work.EKLRelCross.flower_plaqueAlgebra_bdd h2 hUcl hmeas hcs hδpos hprod hprod2
        hW0 hWopen hWgen ?_
      intro z _ z' _ hpat
      exact hsep_all z z' hpat
  · -- (ii) the bases are Borel and contained in the plaque algebras
    intro n
    cases hsel : selPair n with
    | none =>
      have hG : G n = ∅ := by simp only [G, hsel]
      rw [hG]
      exact ⟨MeasurableSet.empty, Set.empty_subset _⟩
    | some d =>
      obtain ⟨hclosed, hsub, hmeas, hhit, hcs⟩ := hDataprop d (hselmem n d hsel)
      have hG : G n = d.1 ∩ Fr := by simp only [G, hsel]
      have hZ : Z n = ⋃ c ∈ d.2 ∩ Fr, atom (Work.EKLRelCross.flowerSigma U δ d.2 W) c := by
        simp only [Z, hsel]
      rw [hG]
      refine ⟨hclosed.measurableSet.inter hFrmeas, ?_⟩
      rintro y ⟨hyE, hyFr⟩
      have hyfree : ∀ u ∈ U, u • y = y → u = 1 := by rw [hFrdef] at hyFr; exact hyFr
      obtain ⟨z, hz, u₀, hu₀U, hu₀V, hu₀z⟩ := hhit y hyE
      have hzmem : z ∈ d.2 ∩ Fr := by
        refine ⟨hz, ?_⟩
        rw [hFrdef]
        intro u' hu' hu'z
        have hfix : (u₀ * u' * u₀⁻¹) • y = y := by
          rw [← hu₀z]
          simp only [mul_smul, inv_smul_smul, hu'z]
        have h1 : u₀ * u' * u₀⁻¹ = 1 :=
          hyfree _ (U.mul_mem (U.mul_mem hu₀U hu') (U.inv_mem hu₀U)) hfix
        calc u' = u₀⁻¹ * (u₀ * u' * u₀⁻¹) * u₀ := by group
          _ = 1 := by rw [h1]; group
      rw [hZ]
      refine Set.mem_iUnion₂.mpr ⟨z, hzmem, ?_⟩
      have hatom := Work.EKLRelCross.atom_flower_local (U := U) (C := d.2) (b := b)
        (W := W) (v := (1 : SL3)) hcs hδpos hprod hW0
        (fun z _ z' _ hpat => hsep_all z z' hpat) hV1δ U.one_mem hz
        (by rw [one_smul])
      rw [hatom]
      exact ⟨u₀, ⟨hV10δ hu₀V, hu₀U⟩, hu₀z⟩
  · -- (iii) the union of the bases is conull
    have hsub : (⋃ n, G n)ᶜ ⊆ Frᶜ := by
      intro y hy
      by_contra hyFrc
      have hyFr : y ∈ Fr := by simpa using hyFrc
      have hyfree : ∀ u ∈ U, u • y = y → u = 1 := by rw [hFrdef] at hyFr; exact hyFr
      obtain ⟨E, C, hclosed, hyE, hCE, hCmeas, hhit, hcs⟩ := hcross y hyfree b hb
      have hdmem : (E, C) ∈ Data := ⟨y, hyfree, hclosed, hyE, hCE, hCmeas, hhit, hcs⟩
      obtain ⟨t, ht, hyt, htu⟩ := (hObas.isOpen_iff.mp isOpen_interior) y hyE
      obtain ⟨k, rfl⟩ := ht
      have hex : ∃ d ∈ Data, O k ⊆ d.1 :=
        ⟨(E, C), hdmem, fun z hz => interior_subset (htu hz)⟩
      have hselk : selPair k = some (Classical.choose hex) := dif_pos hex
      have hch := Classical.choose_spec hex
      have hGk : G k = (Classical.choose hex).1 ∩ Fr := by simp only [G, hselk]
      have hyG : y ∈ G k := by
        rw [hGk]
        exact ⟨hch.2 hyt, hyFr⟩
      exact hy (Set.mem_iUnion.mpr ⟨k, hyG⟩)
    exact MeasureTheory.measure_mono_null hsub hFraec
  · -- (iv) the `R`-plaque of a base point lies in the atom
    intro n x hx u hu
    obtain ⟨huV, huU⟩ := hu
    cases hsel : selPair n with
    | none =>
      have hG : G n = ∅ := by simp only [G, hsel]
      rw [hG] at hx
      exact absurd hx (Set.notMem_empty x)
    | some d =>
      obtain ⟨hclosed, hsub, hmeas, hhit, hcs⟩ := hDataprop d (hselmem n d hsel)
      have hx' : x ∈ d.1 ∧ x ∈ Fr := by
        have hG : G n = d.1 ∩ Fr := by simp only [G, hsel]
        rwa [hG] at hx
      obtain ⟨hxE, hxFr⟩ := hx'
      obtain ⟨z, hz, u₀, hu₀U, hu₀V, hu₀z⟩ := hhit x hxE
      have hm : m n = Work.EKLRelCross.flowerSigma U δ d.2 W := by simp only [m, hsel]
      have hatom := Work.EKLRelCross.atom_flower_local (U := U) (C := d.2) (b := b)
        (W := W) (v := u₀) hcs hδpos hprod hW0
        (fun z _ z' _ hpat => hsep_all z z' hpat) (hV10δ hu₀V) hu₀U hz hu₀z.symm
      rw [hm, hatom]
      refine ⟨u * u₀, ⟨hsize u huV u₀ hu₀V, U.mul_mem huU hu₀U⟩, ?_⟩
      show (u * u₀) • z = u • x
      rw [mul_smul, hu₀z]

/-! ## 3. The local cross-section through a free point (Pisa 6.7 + 6.9–6.12) -/

/-- **The local cross-section at a free point**, in the form consumed by the flower construction:
`Work.EKLRelCross.pisa_crosssection` provides a closed neighbourhood `E ∋ x₀` and a Borel
`C ⊆ E` together with a *unique* `t ∈ Ucl U 1` carrying each `x ∈ E` into `C`; the inverse `t⁻¹`
has entries within `9` of the identity (it is the adjugate of `t` and `t` has entries `≤ 2`),
hence lies in `V 10`, and `C` is a cross-section of the `U`-orbits at any prescribed scale. -/
private theorem crossSection_of_pisa {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
    {x₀ : X3} (hfree : ∀ u ∈ U, u • x₀ = x₀ → u = 1) (b : ℝ) (hb : 0 < b) :
    ∃ (E C : Set X3), IsClosed E ∧ x₀ ∈ interior E ∧ C ⊆ E ∧ MeasurableSet C ∧
      (∀ x ∈ E, ∃ z ∈ C, ∃ u ∈ U, u ∈ V 10 ∧ u • z = x) ∧
      (∀ z ∈ C, ∀ u ∈ U, u ∈ V b → u • z ∈ C → u = 1) := by
  set ρ : ℝ := max 3 (3 * b) with hρdef
  have hρ2 : 2 < ρ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hbρ : b ≤ ρ := le_trans (by linarith) (le_max_right _ _)
  have hfree' : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x₀ = u₂ • x₀ → u₁ = u₂ := by
    intro u₁ h₁ u₂ h₂ h
    have hfix : (u₂⁻¹ * u₁) • x₀ = x₀ := by
      rw [mul_smul, h, inv_smul_smul]
    have hone : u₂⁻¹ * u₁ = 1 := hfree _ (U.mul_mem (U.inv_mem h₂) h₁) hfix
    calc u₁ = u₂ * (u₂⁻¹ * u₁) := by group
      _ = u₂ := by rw [hone, mul_one]
  obtain ⟨E, C, hEc, hxE, hCE, hCmeas, huniq, hcs⟩ :=
    Work.EKLRelCross.pisa_crosssection hUcl x₀ hρ2 hfree'
  refine ⟨E, C, hEc, hxE, hCE, hCmeas, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, ht, -⟩ := huniq x hx
    refine ⟨t • x, ht.2, t⁻¹, U.inv_mem ht.1.1, ?_, inv_smul_smul t x⟩
    -- `t⁻¹ ∈ V 10`: the entries of `t` are `≤ 2`, so those of its adjugate (its inverse) are `≤ 8`
    have hone : ∀ i j : Fin 3, |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
      intro i j; rw [Matrix.one_apply]; split <;> simp
    have ht2 : ∀ i j : Fin 3, |(t : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 2 := by
      intro i j
      have h := ht.1.2 i j
      calc |(t : Matrix (Fin 3) (Fin 3) ℝ) i j|
          = |((t : Matrix (Fin 3) (Fin 3) ℝ) i j
              - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
              + (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by ring_nf
        _ ≤ |(t : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
              + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_add_le _ _
        _ ≤ 1 + 1 := add_le_add h (hone i j)
        _ = 2 := by norm_num
    intro i j
    have hadj : |((t⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 8 := by
      rw [Matrix.SpecialLinearGroup.coe_inv]
      have h := Work.EKLProd.abs_adjugate_entry_le (A := (t : Matrix (Fin 3) (Fin 3) ℝ))
        (B := 2) (by norm_num) ht2 i j
      norm_num at h
      exact h
    calc |((t⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
        ≤ |((t⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j|
            + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_sub_le_abs_add _ _
      _ ≤ 8 + 1 := add_le_add hadj (hone i j)
      _ < 10 := by norm_num
  · intro z hz u huU huV huz
    exact hcs z hz u ⟨huU, fun i j => le_of_lt (lt_of_lt_of_le (huV i j) hbρ)⟩ huz

/-- **Flowers of `U`-plaques exist** (Pisa 6.13–6.15). -/
theorem BigShapeFlowers (h2 : Work.EKLContract.P_X3) (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (R : ℝ) (hR : 0 < R) :
    ∃ (Z G : ℕ → Set Work.EKLContract.X3) (m : ℕ → MeasurableSpace Work.EKLContract.X3),
      (∀ n, Work.EKLContract.IsPlaqueAlgebra U (Z n) (m n)) ∧
      (∀ n, MeasurableSet (G n) ∧ G n ⊆ Z n) ∧
      μ (⋃ n, G n)ᶜ = 0 ∧
      (∀ n, ∀ x ∈ G n, ∀ u ∈ (Work.EKLContract.V R ∩ (U : Set Work.EKLContract.SL3)), u • x ∈ Work.EKLContract.atom (m n) x) :=
  bigShapeFlowers_core h2 μ hU.1
    (Work.EKLRelCross.free_orbits_of_contracting h2 hU t0 ht0 hcontr) hR
    (fun x hx b hb => crossSection_of_pisa hU.1 hx b hb)

end Work.EKLC7
