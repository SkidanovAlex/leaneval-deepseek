import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces

/-!
# `Work.EKLC6Core.exists_gen_plaque_data`

**RESTORED MODULE.**  Deleted from the shared tree by its prover, breaking the build of
`Work.EKLC6Core.exists_gen_plaque_of_mp` (which imports it and destructures its conclusion).
Restored with its statement and a `sorry`.

## The statement

The *geometric core* of Pisa 7.37/7.43 in the form consumed by
`Work.EKLC6Core.exists_gen_plaque_of_mp` (whose `HasGenPlaqueData` is literally this nested
existential — the past σ-algebra is written out so that this module does **not** have to import
`Work.EKLC6Core.exists_gen_partition`, whose `pastSigma` clashes with the one of
`Work.EKLC6Core.PastJoin` in any module that sees both): a countable family `S` of Borel sets and
a `μ`-conull `Z` such that

* `⨆ₙ comap ((aDiag t ·)^[n]) σ(S)` is a plaque algebra for `Uminus t` on `Z`, and
* `S` is *dynamically small around every point*: for every `x` and every neighbourhood `V ∋ x`
  there are `n, m` with `x ∈ (aDiag t ^ n ·) '' S m ⊆ V`.

The second clause is what makes the past σ-algebra generate the *Borel* σ-algebra
(`borel_eq_of_smallFam`); the plaque-algebra clause alone does not.

## Why this is the relevant input for component C6

* `Work.EKLC6Core.exists_plaque_family_conull_of_gen_data` (below) shows that this data *implies*
  the conull plaque family `∃ S Z, … IsPlaqueAlgebra (Uminus t) Z (⨆ₙ comap ((aDiag t ·)^[n]) σ(S))`
  which is the sole geometric input of `Work.EKLC6Core.ent_ge_growth_uminus` (Pisa 7.6(ii) for
  `U = Uminus t`, the `⇐` direction of C6).  So the `CellBase`/`CellFacts`/`Margin` route of
  `EKLC6Core/exists_plaque_family_conull.lean` is not needed: proving this one lemma serves both
  routes.
* `Work.EKLC6Core.exists_desc_subordinate_data` (PROVED, `sorry`-free) is the *ε*-version: for
  every `ε > 0` there are a countable Borel family `G` and a `Z` with `μ Zᶜ < ε` such that
  `pastSig t (σ (range G))` is a plaque algebra for `Uminus t` on `Z` and is `aDiag t`-decreasing.
  What is missing here is (a) the *dynamic smallness* of the family and (b) the upgrade
  `μ Zᶜ < ε → μ Zᶜ = 0`; the source (Einsiedler–Lindenstrauss, Prop. 7.37 and the remark
  following it) gets (b) from the ergodicity of `aDiag t`, which the target does not assume, so the
  upgrade here has to be produced from the `ε`-version directly.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **The geometric core of Pisa 7.37/7.43 in data form** (definitionally the `HasGenPlaqueData`
of `exists_gen_plaque_of_mp`). -/
theorem exists_gen_plaque_data {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hne : Work.EKLC6Core.Uminus t ≠ ⊥) :
    ∃ (S : ℕ → Set Work.EKLContract.X3) (Z : Set Work.EKLContract.X3),
      (∀ n, MeasurableSet (S n)) ∧
      μ Zᶜ = 0 ∧
      Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z
        (⨆ n : ℕ, MeasurableSpace.comap
          ((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n])
          (MeasurableSpace.generateFrom (Set.range S))) ∧
      (∀ x : Work.EKLContract.X3, ∀ V : Set Work.EKLContract.X3, V ∈ nhds x →
        ∃ (n : ℕ) (m : ℕ),
          x ∈ (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t ^ n • y) '' (S m) ∧
          (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t ^ n • y) '' (S m) ⊆ V) := by
  sorry

/-- **The conull plaque family in the presentation used by C6**, derived from the geometric core:
the σ-algebra is the past σ-algebra of the same countable family, so this is the plaque-algebra
clause and the conull set of `exists_gen_plaque_data` with the (unused here) dynamic-smallness
clause dropped. -/
theorem exists_plaque_family_conull_of_gen_data {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hne : Work.EKLC6Core.Uminus t ≠ ⊥) :
    ∃ (S : ℕ → Set Work.EKLContract.X3) (Z : Set Work.EKLContract.X3),
      (∀ n, MeasurableSet (S n)) ∧
      μ Zᶜ = 0 ∧
      Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z
        (⨆ n : ℕ, MeasurableSpace.comap
          ((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n])
          (MeasurableSpace.generateFrom (Set.range S))) := by
  obtain ⟨S, Z, hS, hZ, hplq, -⟩ := exists_gen_plaque_data t hmp hne
  exact ⟨S, Z, hS, hZ, hplq⟩

end Work.EKLC6Core

end
