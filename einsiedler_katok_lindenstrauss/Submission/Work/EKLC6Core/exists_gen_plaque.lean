import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.exists_gen_partition
import Submission.Work.EKLContract.All

/-!
# `Work.EKLC6Core.exists_gen_plaque` — a *generating* `aDiag t`-descending plaque algebra

For an `A`-ergodic probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` and every `t : Fin 3 → ℝ`
there is a countably generated σ-algebra `A ≤ borel X₃` and a conull set `Z` such that

* `A` is a plaque algebra for the contracted horospherical subgroup
  `U = Uminus t = G⁻(t)` on `Z` (`IsPlaqueAlgebra (Uminus t) Z A`);
* `A` is `aDiag t`-*decreasing*: `comap (aDiag t ·) A ≤ A`;
* `A` *generates* under the flow: `⨆_n comap ((aDiag (-t))·)^[n] A = borel X₃`.

This is the σ-algebra input of Pisa Theorem 7.6(ii) (the equality half): the σ-algebra
`A = ⋁_{n≥0} aDiag(-nt)·σ(P)` built from a *generating* partition `P` subordinate to `G⁻(t)`
(Pisa Prop. 7.43).

## Structure of the proof

The non-degenerate case `Uminus t ≠ ⊥` is delegated to
`Work.EKLC6Core.exists_gen_partition`, which produces a countable measurable partition `P` of a
`μ`-conull set with `A := ⨆_n comap ((aDiag t)·)^[n] σ(P)` a plaque algebra for `Uminus t` on a
conull `Z`, together with the exact generation statement.  The only thing left to check here is
that this `A` is `aDiag t`-decreasing: composing two pullbacks gives
`comap (aDiag t ·) (comap ((aDiag t)·)^[n] σ(P)) = comap ((aDiag t)·)^[n+1] σ(P)`, so the
pullback lands in the same supremum.

The degenerate case `Uminus t = ⊥` (equivalently `t` constant, so that `aDiag t = 1` acts
trivially) is handled directly with `A = borel X₃`, `Z = X₃`: the atoms of `borel X₃` are
singletons, the atom of a point is contained in its `⊥`-orbit `{x}`, the shape is `⊥ = {1}`,
which is `O ∩ ⊥` for `O = univ`, and entrywise bounded.
-/

open MeasureTheory
open scoped ENNReal

namespace Work.EKLC6Core

open Work.EKLContract

set_option linter.style.haveILetI false

/-- In a `T1` Borel space the atom of the Borel σ-algebra at `x` is the singleton `{x}`. -/
theorem atom_borel_singleton (x : X3) : atom (borel X3) x = {x} := by
  haveI : IsClosed (Γ3 : Set SL3) := Work.EKLContract.Lemmas.isClosed_Γ3
  haveI : SecondCountableTopology SL3 := Work.EKLContract.Lemmas.SL3Topology.2
  haveI : T1Space X3 := inferInstance
  refine Set.Subset.antisymm ?_ ?_
  · exact Set.sInter_subset_of_mem ⟨(isClosed_singleton (x := x)).measurableSet, rfl⟩
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Set.mem_sInter.mpr (fun t ht => ht.2)

/-- `IsPlaqueAlgebra` holds for the trivial subgroup, with the Borel σ-algebra and the whole
space: the atoms are singletons, which are the trivial-group orbit of the point. -/
theorem bot_plaque : IsPlaqueAlgebra (⊥ : Subgroup SL3) Set.univ (borel X3) := by
  haveI : IsClosed (Γ3 : Set SL3) := Work.EKLContract.Lemmas.isClosed_Γ3
  haveI : SecondCountableTopology SL3 := Work.EKLContract.Lemmas.SL3Topology.2
  haveI : SecondCountableTopology X3 := inferInstance
  haveI : T1Space X3 := inferInstance
  refine ⟨le_rfl, ?_, MeasurableSet.univ, ?_⟩
  · obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis X3
    exact ⟨b, hbc, hb.borel_eq_generateFrom⟩
  · intro x hx
    have hatom : atom (borel X3) x = {x} := atom_borel_singleton x
    have hshape : shape (borel X3) (⊥ : Subgroup SL3) x = ((⊥ : Subgroup SL3) : Set SL3) := by
      ext u
      simp only [shape, Set.mem_ofPred_eq, SetLike.mem_coe, hatom]
      constructor
      · rintro ⟨hu, -⟩; exact hu
      · intro hu
        exact ⟨hu, by rw [Subgroup.mem_bot.mp hu, one_smul]; exact Set.mem_singleton x⟩
    refine ⟨by rw [hatom]; exact Set.singleton_subset_iff.mpr hx, ?_, ?_, ?_⟩
    · rw [hatom]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact ⟨1, Subgroup.mem_bot.mpr rfl, one_smul SL3 x⟩
    · refine ⟨Set.univ, isOpen_univ, ?_⟩
      rw [hshape, Set.univ_inter]
    · refine ⟨1, ?_⟩
      intro u hu i j
      rw [hshape] at hu
      have hu1 : u = 1 := Subgroup.mem_bot.mp hu
      rw [hu1]
      rw [show ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) = 1 from rfl, Matrix.one_apply]
      split <;> simp

theorem exists_gen_plaque {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    (t : Fin 3 → ℝ) (hErg : Work.EKLContract.IsAErgodic μ) :
    ∃ A : MeasurableSpace Work.EKLContract.X3, ∃ Z : Set Work.EKLContract.X3,
      Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z A ∧ μ Zᶜ = 0 ∧
      MeasurableSpace.comap
        (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A ∧
      (⨆ n : ℕ, MeasurableSpace.comap
        ((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag (-t) • x)^[n]) A)
        = Work.EKLContract.instMeasurableSpaceX3 := by
  by_cases hU : Work.EKLC6Core.Uminus t = ⊥
  · -- degenerate case: `aDiag t = 1`, take the Borel σ-algebra
    refine ⟨borel Work.EKLContract.X3, Set.univ, ?_, ?_, ?_, ?_⟩
    · rw [hU]; exact bot_plaque
    · simp
    · exact measurable_iff_comap_le.mp ((continuous_const_smul (Work.EKLContract.aDiag t)).measurable)
    · refine le_antisymm (iSup_le fun n => measurable_iff_comap_le.mp ?_) ?_
      · exact ((continuous_const_smul (Work.EKLContract.aDiag (-t))).measurable).iterate n
      · have h0 : MeasurableSpace.comap
            ((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag (-t) • x)^[0])
              (borel Work.EKLContract.X3)
            = Work.EKLContract.instMeasurableSpaceX3 := by
          rw [Function.iterate_zero, MeasurableSpace.comap_id]
          rfl
        rw [← h0]
        exact le_iSup (fun n : ℕ => MeasurableSpace.comap
          ((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag (-t) • x)^[n])
            (borel Work.EKLContract.X3)) 0
  · -- non-degenerate case: the generating partition of `exists_gen_partition`
    obtain ⟨P, Z, _hPmeas, _hPdisj, _hPcov, hplaq, hZ, hgen⟩ :=
      Work.EKLC6Core.exists_gen_partition t hErg hU
    refine ⟨(⨆ n : ℕ, MeasurableSpace.comap
          ((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n])
          (MeasurableSpace.generateFrom (Set.range P))), Z, hplaq, hZ, ?_, hgen⟩
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun n => ?_
    rw [MeasurableSpace.comap_comp]
    rw [← Function.iterate_succ]
    exact le_iSup (fun n : ℕ => MeasurableSpace.comap
          ((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n])
          (MeasurableSpace.generateFrom (Set.range P))) (n + 1)

end Work.EKLC6Core
