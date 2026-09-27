import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC7.LeafwiseGeom

/-!
# `Work.EKLC6Core.exists_gen_partition` — a generating measurable partition

RECONSTRUCTION NOTE.  The source of this module was lost from the workspace (only its compiled
`.olean` remained, and Lake refuses to build a module whose source is missing); the statements
below are the ones recorded in that `.olean`, and the proofs of the auxiliary lemmas are
reproved here from scratch.  The main theorem `exists_gen_partition` is the geometric core
(Pisa 7.37/7.38): the existence of a countable measurable partition `P` of a conull set whose
past σ-algebra `⨆ₙ comap ((aDiag t ·)^[n]) (σ(range P))` is a plaque algebra for `Uminus t` on a
conull set `Z` and which generates the Borel σ-algebra under `aDiag (-t) ·`.  It was a `sorry`
in the lost source as well; `exists_gen_plaque` uses it only for the generating property.
-/

open MeasureTheory Topology Filter Set
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The *past* σ-algebra of a countable family `P` along the flow `aDiag t ·`. -/
def pastSigma (t : Fin 3 → ℝ) (P : ℕ → Set X3) : MeasurableSpace X3 :=
  ⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
    (MeasurableSpace.generateFrom (Set.range P))

/-- The *past* σ-algebra of `pastSigma t P` along the inverse flow `aDiag (-t) ·`. -/
def fullSigma (t : Fin 3 → ℝ) (P : ℕ → Set X3) : MeasurableSpace X3 :=
  ⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag (-t) • x)^[n]) (pastSigma t P)

/-- If a sub-σ-algebra `A` of the Borel σ-algebra contains, for every point `x` and every open
neighbourhood `V` of `x`, a member `D ∈ 𝒟` with `x ∈ D ⊆ V`, and `𝒟` is a countable family of
`A`-measurable sets, then `A` is the whole Borel σ-algebra. -/
theorem borel_eq_of_countable_small_sets {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] {A : MeasurableSpace X}
    (hA : A ≤ borel X) (𝒟 : Set (Set X)) (h𝒟 : 𝒟.Countable)
    (h𝒟A : ∀ D ∈ 𝒟, @MeasurableSet X A D)
    (hsmall : ∀ (x : X) (V : Set X), IsOpen V → x ∈ V → ∃ D ∈ 𝒟, x ∈ D ∧ D ⊆ V) :
    A = borel X := by
  refine le_antisymm hA ?_
  show MeasurableSpace.generateFrom {V : Set X | IsOpen V} ≤ A
  refine MeasurableSpace.generateFrom_le fun V hV => ?_
  have hcover : V = ⋃₀ {D : Set X | D ∈ 𝒟 ∧ D ⊆ V} := by
    ext x
    constructor
    · intro hx
      obtain ⟨D, hD, hxD, hDV⟩ := hsmall x V hV hx
      exact Set.mem_sUnion.mpr ⟨D, ⟨⟨hD, hDV⟩, hxD⟩⟩
    · intro hx
      obtain ⟨D, ⟨⟨hD, hDV⟩, hxD⟩⟩ := Set.mem_sUnion.mp hx
      exact hDV hxD
  rw [hcover]
  exact MeasurableSet.sUnion (h𝒟.mono fun D hD => hD.1) fun D hD => h𝒟A D hD.1

/-- The past σ-algebra of a countable measurable family is contained in the Borel σ-algebra. -/
theorem pastSigma_le_borel (t : Fin 3 → ℝ) (P : ℕ → Set X3)
    (hP : ∀ n, MeasurableSet (P n)) : pastSigma t P ≤ borel X3 := by
  rw [pastSigma]
  refine iSup_le fun n => ?_
  have h1 : MeasurableSpace.generateFrom (Set.range P) ≤ borel X3 :=
    MeasurableSpace.generateFrom_le fun s hs => by
      obtain ⟨m, rfl⟩ := hs
      exact hP m
  exact (MeasurableSpace.comap_mono h1).trans
    (measurable_iff_comap_le.mp
      (((continuous_const_smul (aDiag t)).measurable).iterate n))

/-- The two-sided past σ-algebra is contained in the Borel σ-algebra. -/
theorem fullSigma_le_borel (t : Fin 3 → ℝ) (P : ℕ → Set X3)
    (hP : ∀ n, MeasurableSet (P n)) : fullSigma t P ≤ borel X3 := by
  rw [fullSigma]
  refine iSup_le fun n => ?_
  exact (MeasurableSpace.comap_mono (pastSigma_le_borel t P hP)).trans
    (measurable_iff_comap_le.mp
      (((continuous_const_smul (aDiag (-t))).measurable).iterate n))

/-- The generating family of the past σ-algebra is measurable for it. -/
theorem generateFrom_range_le_pastSigma (t : Fin 3 → ℝ) (P : ℕ → Set X3) :
    MeasurableSpace.generateFrom (Set.range P) ≤ pastSigma t P := by
  rw [pastSigma]
  simpa only [Function.iterate_zero, MeasurableSpace.comap_id] using
    le_iSup (fun n : ℕ => MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
      (MeasurableSpace.generateFrom (Set.range P))) 0

/-- Each member of the family is measurable for the past σ-algebra. -/
theorem measurableSet_pastSigma_cell (t : Fin 3 → ℝ) (P : ℕ → Set X3) (n : ℕ) :
    @MeasurableSet X3 (pastSigma t P) (P n) :=
  generateFrom_range_le_pastSigma t P (P n)
    (MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self n))

/-- Unions of members of the family are measurable for the past σ-algebra. -/
theorem measurableSet_pastSigma_iUnion (t : Fin 3 → ℝ) (P : ℕ → Set X3) (S : Set ℕ) :
    @MeasurableSet X3 (pastSigma t P) (⋃ n ∈ S, P n) :=
  MeasurableSet.biUnion (Set.countable_univ.mono (Set.subset_univ S))
    fun n _ => measurableSet_pastSigma_cell t P n

/-- **The plaque-algebra content of a coding partition.**  If the atoms of the past σ-algebra
have open, bounded `Uminus t`-shapes and stay in the `Uminus t`-orbit, then that σ-algebra is a
plaque algebra for `Uminus t` on the union of the selected cells. -/
theorem isPlaqueAlgebra_of_coding (t : Fin 3 → ℝ) (P : ℕ → Set X3) (S : Set ℕ)
    (hP : ∀ n, MeasurableSet (P n))
    (hcount : ∃ b : Set (Set X3), b.Countable ∧
      pastSigma t P = MeasurableSpace.generateFrom b)
    (hshape : ∀ x ∈ ⋃ n ∈ S, P n, ∃ O : Set SL3, IsOpen O ∧
      shape (pastSigma t P) (Uminus t) x = O ∩ (Uminus t : Set SL3))
    (hatom : ∀ x ∈ ⋃ n ∈ S, P n,
      atom (pastSigma t P) x ⊆ (fun u : SL3 => u • x) '' (Uminus t : Set SL3))
    (hbdd : ∀ x ∈ ⋃ n ∈ S, P n, ∃ C : ℝ,
      ∀ u ∈ shape (pastSigma t P) (Uminus t) x, ∀ i j : Fin 3, |u i j| ≤ C) :
    IsPlaqueAlgebra (Uminus t) (⋃ n ∈ S, P n) (pastSigma t P) :=
  ⟨pastSigma_le_borel t P hP, hcount, measurableSet_pastSigma_iUnion t P S,
    fun x hx =>
      ⟨fun y hy => Set.mem_sInter.mp hy (⋃ n ∈ S, P n)
          ⟨measurableSet_pastSigma_iUnion t P S, hx⟩,
        hatom x hx, hshape x hx, hbdd x hx⟩⟩

/-- **The coding form of Pisa 7.37/7.38.**  From a countable measurable partition `P` of `univ`
whose past σ-algebra is a plaque algebra on the union of the selected cells `S`, and whose
two-sided past σ-algebra is the whole Borel σ-algebra, one gets the generating partition. -/
theorem exists_gen_partition_of_coding {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ) (P : ℕ → Set X3) (S : Set ℕ)
    (hP : ∀ n, MeasurableSet (P n))
    (hPdisj : ∀ m n : ℕ, m ≠ n → Disjoint (P m) (P n))
    (hPcov : ⋃ n, P n = Set.univ)
    (hZ : μ (⋃ n ∈ S, P n)ᶜ = 0)
    (hcount : ∃ b : Set (Set X3), b.Countable ∧
      pastSigma t P = MeasurableSpace.generateFrom b)
    (hshape : ∀ x ∈ ⋃ n ∈ S, P n, ∃ O : Set SL3, IsOpen O ∧
      shape (pastSigma t P) (Uminus t) x = O ∩ (Uminus t : Set SL3))
    (hatom : ∀ x ∈ ⋃ n ∈ S, P n,
      atom (pastSigma t P) x ⊆ (fun u : SL3 => u • x) '' (Uminus t : Set SL3))
    (hbdd : ∀ x ∈ ⋃ n ∈ S, P n, ∃ C : ℝ,
      ∀ u ∈ shape (pastSigma t P) (Uminus t) x, ∀ i j : Fin 3, |u i j| ≤ C)
    (𝒟 : Set (Set X3)) (h𝒟c : 𝒟.Countable)
    (h𝒟full : ∀ D ∈ 𝒟, @MeasurableSet X3 (fullSigma t P) D)
    (h𝒟small : ∀ (x : X3) (V : Set X3), IsOpen V → x ∈ V → ∃ D ∈ 𝒟, x ∈ D ∧ D ⊆ V) :
    ∃ P' Z, (∀ n : ℕ, MeasurableSet (P' n)) ∧
      (∀ m n : ℕ, m ≠ n → Disjoint (P' m) (P' n)) ∧ μ (⋃ n, P' n)ᶜ = 0 ∧
      IsPlaqueAlgebra (Uminus t) Z (pastSigma t P') ∧ μ Zᶜ = 0 ∧
      fullSigma t P' = instMeasurableSpaceX3 := by
  refine ⟨P, ⋃ n ∈ S, P n, hP, hPdisj, ?_,
    isPlaqueAlgebra_of_coding t P S hP hcount hshape hatom hbdd, hZ, ?_⟩
  · rw [hPcov]; simp
  · exact borel_eq_of_countable_small_sets (fullSigma_le_borel t P hP) 𝒟 h𝒟c h𝒟full h𝒟small

/-- **Pisa 7.37/7.38 (the geometric core of L1 of C6).**  For an `A`-ergodic probability `μ` with
`Uminus t ≠ ⊥` there is a countable measurable partition of a conull set whose past σ-algebra is
a plaque algebra for `Uminus t` on a conull set, and which generates the Borel σ-algebra under
the inverse flow `aDiag (-t) ·`.

This is the hard geometric input; the lost source had it as a `sorry`, and the surrounding
development (`exists_gen_plaque`, `exists_gen_plaque_of_mp`, …) reduces to it. -/
theorem exists_gen_partition {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hErg : IsAErgodic μ) (hU : Uminus t ≠ ⊥) :
    ∃ P Z, (∀ n : ℕ, MeasurableSet (P n)) ∧
      (∀ m n : ℕ, m ≠ n → Disjoint (P m) (P n)) ∧ μ (⋃ n, P n)ᶜ = 0 ∧
      IsPlaqueAlgebra (Uminus t) Z (pastSigma t P) ∧ μ Zᶜ = 0 ∧
      fullSigma t P = instMeasurableSpaceX3 := by
  sorry

end Work.EKLC6Core

end
