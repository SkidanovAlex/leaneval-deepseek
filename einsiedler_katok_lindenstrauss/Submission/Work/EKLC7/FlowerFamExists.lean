import Mathlib
import Submission.Work.EKLC7.LeafFlowerDefs
import Submission.Work.EKLC7.AeFreeStab
import Submission.Work.EKLC7.LocalFlowDefs
import Submission.Work.EKLRelCross.flower_plaque
import Submission.Work.EKLComp.prove_X3

/-!
# `Work.EKLC7.FlowerFamExists` — the flower family with unbounded radii exists

For a horospherical subgroup `U ≤ SL₃(ℝ)` and an `A`-invariant probability measure `μ` on
`X₃ = SL₃(ℝ)/SL₃(ℤ)`, this file constructs `Work.EKLC7.FlowerFam U μ` (Pisa Corollary 6.15 in
the uniform form used by the construction of leafwise measures): countably many flowers
`(R n, E n, Z n, m n)` with measurable bases whose union is `μ`-conull and whose radii `R n` are
unbounded.

## Content

The only geometric input is `Work.EKLC7.LocalFlowerFam U` (`Work.EKLC7.LocalFlowDefs`), the
local flower family of Pisa 6.7 + 6.9–6.15 at the points with trivial `U`-stabiliser; the
mathematical content of this file is the measure-theoretic assembly:

* `Upla_subset_atom_of_shape`: the frozen `BigPlaqueOn` condition follows from a shape condition;
* `flowersAtRadius`: for every `R > 0`, countably many radius-`R` flowers with measurable bases
  covering `μ`-a.e. point.  The countable-basis argument: for `μ`-a.e. `y` the point `y` is free
  and all is open neighbourhoods have positive measure, so a basis element `basis n ∋ y` lies in
  the neighbourhood `O` of the local flower family at `y`; registering, for every such basis
  element, the flower family of one chosen free witness inside it, the bases of the registered
  flowers cover a.e.;
* `FlowerFam_of_localFlowerFam`: assembling the radius-`(k+1)` families over `k ∈ ℕ` into one
  countable family shows `FlowerFamP U μ` (the index is `Nat.pair` of the level and the index in
  the level, and the `cover` field is satisfied because every `ρ > 0` is below some radius
  `k + 1`).

`FlowerFamExists` then combines this with the a.e. freeness of the `U`-orbits
(`ae_free_orbit_of_horo`, Poincaré recurrence) and the geometric input for horospherical `U`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC7

open Work.EKLContract
open Work.EKLComp

/-! ## 1. From the shape containment to the plaque condition -/

/-- `Uball U r` is the trace on `U` of the ambient entry ball `V r`. -/
theorem Uball_eq_inter_V (U : Subgroup SL3) (r : ℝ) :
    Uball U r = (U : Set SL3) ∩ V r := rfl

/-- **The frozen `BigPlaqueOn` condition from the shape form.**  If the shape of a plaque algebra
`m` at every point `x` of a base `E` contains the whole ambient ball `V R` (intersected with `U`),
then the `R`-plaque `Upla U R x` lies in the atom `atom m x`. -/
theorem Upla_subset_atom_of_shape {U : Subgroup SL3} {E : Set X3} {m : MeasurableSpace X3}
    {R : ℝ} (h : ∀ x ∈ E, V R ∩ (U : Set SL3) ⊆ shape m U x) :
    ∀ x ∈ E, Upla U R x ⊆ atom m x := by
  intro x hx y hy
  obtain ⟨g, hg, hgy⟩ := hy
  rw [← hgy]
  exact (h x hx ⟨hg.2, hg.1⟩).2

/-- The trivial flower on the empty set: `IsPlaqueAlgebra U ∅ ⊥` (vacuous atoms). -/
theorem isPlaqueAlgebra_empty (U : Subgroup SL3) :
    IsPlaqueAlgebra U (∅ : Set X3) (⊥ : MeasurableSpace X3) := by
  refine ⟨bot_le, ⟨∅, Set.countable_empty, ?_⟩, @MeasurableSet.empty X3 ⊥, ?_⟩
  · rw [MeasurableSpace.generateFrom_empty]
  · intro x hx; exact absurd hx (Set.notMem_empty x)

/-! ## 2. Flowers at a fixed radius covering almost everything -/

/-- **Countably many radius-`R` flowers with bases covering a.e.**  From the local flower family
at every free point and the a.e. freeness of the `U`-orbits, the countable-basis argument
produces countably many radius-`R` flowers whose measurable bases cover almost every point. -/
theorem flowersAtRadius (U : Subgroup SL3) (hLF : LocalFlowerFam U)
    (μ : Measure X3) [IsProbabilityMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1)
    (hpos : ∀ᵐ x ∂μ, ∀ s : Set X3, IsOpen s → x ∈ s → 0 < μ s)
    (R : ℝ) (hR : 0 < R) :
    ∃ (E Z : ℕ → Set X3) (m : ℕ → MeasurableSpace X3),
      (∀ n, MeasurableSet (E n)) ∧ (∀ n, BigPlaqueOn U R (E n) (Z n) (m n)) ∧
      μ (⋃ n, E n)ᶜ = 0 := by
  classical
  -- the local flower family, as a function of the free point
  have hloc : ∀ x : FreeSet U, ∃ (E Z : ℕ → Set X3) (m : ℕ → MeasurableSpace X3) (O : Set X3),
      IsOpen O ∧ (x : X3) ∈ O ∧
      (∀ n, @MeasurableSet X3 instMeasurableSpaceX3 (E n)) ∧
      (∀ n, BigPlaqueOn U R (E n) (Z n) (m n)) ∧
      (O ∩ FreeSet U) ⊆ ⋃ n, E n := by
    intro x
    exact hLF (x : X3) x.property R hR
  choose Efun Zfun mfun Ofun hOopen hxO hEmeas hbig hOcov using hloc
  obtain ⟨basis, hbas⟩ := TopologicalSpace.exists_seq_basis X3
  -- basis elements of positive measure lying inside the neighbourhood of a local flower family
  let ι : Set ℕ := {n | 0 < μ (basis n) ∧ ∃ s : FreeSet U, basis n ⊆ Ofun s}
  have hch : ∀ n : ℕ, n ∈ ι → ∃ s : FreeSet U, basis n ⊆ Ofun s := fun n hn => hn.2
  -- the flowers indexed by `ℕ`, padded with the trivial flower outside `ι`
  let F : ℕ → Set X3 := fun j =>
    if h : (Nat.unpair j).1 ∈ ι then Efun (Classical.choose (hch _ h)) (Nat.unpair j).2 else ∅
  let Z' : ℕ → Set X3 := fun j =>
    if h : (Nat.unpair j).1 ∈ ι then Zfun (Classical.choose (hch _ h)) (Nat.unpair j).2 else ∅
  let M' : ℕ → MeasurableSpace X3 := fun j =>
    if h : (Nat.unpair j).1 ∈ ι then mfun (Classical.choose (hch _ h)) (Nat.unpair j).2
    else ⊥
  have hF : ∀ j, MeasurableSet (F j) := by
    intro j
    by_cases h : (Nat.unpair j).1 ∈ ι
    · simp only [F, dif_pos h]; exact hEmeas _ _
    · simp only [F, dif_neg h]; exact MeasurableSet.empty
  have hbig' : ∀ j, BigPlaqueOn U R (F j) (Z' j) (M' j) := by
    intro j
    by_cases h : (Nat.unpair j).1 ∈ ι
    · simp only [F, Z', M', dif_pos h]; exact hbig _ _
    · simp only [F, Z', M', dif_neg h]
      exact ⟨isPlaqueAlgebra_empty U, Set.empty_subset _,
        Upla_subset_atom_of_shape (E := (∅ : Set X3))
          (fun x hx => absurd hx (Set.notMem_empty x))⟩
  refine ⟨F, Z', M', hF, hbig', ?_⟩
  have hcov : ∀ᵐ y ∂μ, y ∈ ⋃ j : ℕ, F j := by
    filter_upwards [hfree, hpos] with y hyS hypos
    have hyO : y ∈ Ofun ⟨y, hyS⟩ := hxO ⟨y, hyS⟩
    obtain ⟨t, htB, hyt, hts⟩ := hbas.exists_subset_of_mem_open hyO (hOopen ⟨y, hyS⟩)
    obtain ⟨n, rfl⟩ := htB
    have hnpos : 0 < μ (basis n) := hypos _ (hbas.isOpen (Set.mem_range_self n)) hyt
    have hn : n ∈ ι := ⟨hnpos, ⟨⟨y, hyS⟩, hts⟩⟩
    have hmem : y ∈ ⋃ k, Efun (Classical.choose (hch n hn)) k :=
      hOcov _ ⟨(Classical.choose_spec (hch n hn)) hyt, hyS⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
    refine Set.mem_iUnion.mpr ⟨Nat.pair n k, ?_⟩
    simp only [F, Nat.unpair_pair, dif_pos hn]
    exact hk
  have hcompl : (⋃ j : ℕ, F j)ᶜ = {y : X3 | ¬ y ∈ ⋃ j : ℕ, F j} := rfl
  rw [hcompl]
  exact MeasureTheory.ae_iff.mp hcov

/-! ## 3. The flower family -/

/-- **The flower family from the local flower family.**  Assembling the radius-`(k+1)` families of
`flowersAtRadius` over `k ∈ ℕ` (with index `Nat.pair k n`) gives a countable family of flowers
with unbounded radii whose bases cover a.e., i.e. `FlowerFamP U μ`. -/
theorem FlowerFam_of_localFlowerFam (U : Subgroup SL3) (hU : IsHoro U)
    (μ : Measure X3) [IsProbabilityMeasure μ] (hA : IsAInvariant μ)
    (hLF : LocalFlowerFam U) : FlowerFamP U μ := by
  classical
  have hfree : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1 := ae_free_orbit_of_horo μ hA U hU
  have hpos : ∀ᵐ x ∂μ, ∀ s : Set X3, IsOpen s → x ∈ s → 0 < μ s := ae_isOpen_pos (μ := μ)
  have hfam : ∀ k : ℕ, ∃ (E Z : ℕ → Set X3) (m : ℕ → MeasurableSpace X3),
      (∀ n, MeasurableSet (E n)) ∧ (∀ n, BigPlaqueOn U ((k : ℝ) + 1) (E n) (Z n) (m n)) ∧
      μ (⋃ n, E n)ᶜ = 0 := by
    intro k
    exact flowersAtRadius U hLF μ hfree hpos ((k : ℝ) + 1) (by positivity)
  choose E Z m hEmeas hbig hcov using hfam
  refine ⟨{ R := fun j => ((Nat.unpair j).1 : ℝ) + 1
            E := fun j => E (Nat.unpair j).1 (Nat.unpair j).2
            Z := fun j => Z (Nat.unpair j).1 (Nat.unpair j).2
            m := fun j => m (Nat.unpair j).1 (Nat.unpair j).2
            one_le := ?_
            measE := ?_
            big := ?_
            cover := ?_ }⟩
  · intro j
    have : (0 : ℝ) ≤ ((Nat.unpair j).1 : ℝ) := Nat.cast_nonneg _
    linarith
  · intro j
    exact hEmeas _ _
  · intro j
    exact hbig _ _
  · intro ρ hρ
    obtain ⟨k, hk⟩ := exists_nat_ge ρ
    have hk1 : ρ ≤ ((k : ℝ) + 1) := by linarith
    have h0 : ∀ᵐ x ∂μ, x ∈ ⋃ n, E k n := by
      rw [MeasureTheory.ae_iff]
      simpa [Set.compl_def] using hcov k
    filter_upwards [h0] with x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    refine ⟨Nat.pair k n, ?_, ?_⟩
    · show ρ ≤ ((Nat.unpair (Nat.pair k n)).1 : ℝ) + 1
      rw [Nat.unpair_pair]
      exact hk1
    · show x ∈ E (Nat.unpair (Nat.pair k n)).1 (Nat.unpair (Nat.pair k n)).2
      rw [Nat.unpair_pair]
      simpa using hn

/-! ## 4. The target -/

/-- **The geometric input** (Pisa 6.7 + 6.9-6.15) for horospherical `U`, in the "one flower
per point" form of `Work.EKLRelCross.flower_local_exists` (which is proved in this workspace from
`Work.EKLComp.prove_X3`, the proved component `P_X3` of the frozen contract).

Here it is converted to the local flower *family* `LocalFlowerFamAt` used by the assembly: the
single flower is put at index `0` and the remaining indices carry the trivial (empty) flower. -/
theorem localFlowerFam_exists (U : Subgroup SL3) (hU : IsHoro U) : LocalFlowerFam U := by
  intro x₀ hfree R hR
  -- the injectivity form of freeness, as required by `flower_local_exists`
  have hfree' : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x₀ = u₂ • x₀ → u₁ = u₂ := by
    intro u₁ h₁ u₂ h₂ heq
    have hfix : (u₂⁻¹ * u₁) • x₀ = x₀ := by rw [mul_smul, heq, inv_smul_smul]
    have hone : u₂⁻¹ * u₁ = 1 := hfree _ (U.mul_mem (U.inv_mem h₂) h₁) hfix
    calc u₁ = u₂ * (u₂⁻¹ * u₁) := (mul_inv_cancel_left u₂ u₁).symm
      _ = u₂ := by rw [hone, mul_one]
  obtain ⟨Z, m, G, O, hOopen, hxO, hGmeas, hGsub, hplaq, hxG, hOG, hshape⟩ :=
    Work.EKLRelCross.flower_local_exists Work.EKLComp.prove_X3 hU x₀ hfree' R hR
  let E : ℕ → Set X3 := fun n => if n = 0 then G else ∅
  let Z' : ℕ → Set X3 := fun n => if n = 0 then Z else ∅
  let M : ℕ → MeasurableSpace X3 := fun n => if n = 0 then m else ⊥
  have hE : ∀ n, @MeasurableSet X3 instMeasurableSpaceX3 (E n) := by
    intro n
    by_cases h : n = 0
    · simp only [E, if_pos h]
      exact hGmeas
    · simp only [E, if_neg h]
      exact @MeasurableSet.empty X3 instMeasurableSpaceX3
  have hB : ∀ n, BigPlaqueOn U R (E n) (Z' n) (M n) := by
    intro n
    by_cases h : n = 0
    · simp only [E, Z', M, if_pos h]
      exact ⟨hplaq, hGsub, Upla_subset_atom_of_shape hshape⟩
    · simp only [E, Z', M, if_neg h]
      exact ⟨isPlaqueAlgebra_empty U, Set.empty_subset _,
        Upla_subset_atom_of_shape (E := (∅ : Set X3))
          (fun x hx => absurd hx (Set.notMem_empty x))⟩
  have hC : O ∩ FreeSet U ⊆ ⋃ n, E n := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    simp only [E, if_pos rfl]
    exact hOG hx
  exact ⟨E, Z', M, O, hOopen, hxO, hE, hB, hC⟩

theorem FlowerFamExists (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U)
    (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (hA : Work.EKLContract.IsAInvariant μ) : Work.EKLC7.FlowerFamP U μ := by
  exact FlowerFam_of_localFlowerFam U hU μ hA (localFlowerFam_exists U hU)

end Work.EKLC7
