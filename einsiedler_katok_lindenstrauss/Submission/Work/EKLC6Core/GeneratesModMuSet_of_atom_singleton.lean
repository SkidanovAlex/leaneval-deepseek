import Mathlib
import Submission.Work.EKLC6Core.countableGenEntropy
import Submission.Work.EKLC6Core.Ch_finPart_plaque_generating
import Submission.Work.EKLComp.X3Background

/-!
# `Work.EKLC6Core.generatesModMuSet_of_atom_singleton`

The **mod-`μ` generator criterion for a countable family**: if the bi-infinite orbit σ-algebra
`biOrbit t S` has singleton atoms on a conull Borel set, then `S` generates the Borel σ-algebra
modulo `μ` (`GeneratesModMuSet μ t S`).

This is the *countable* analogue of the proved `Work.EKLC6Core.Ch_generatesModMu_of_atom_singleton`
(for a `FinPart`) and the repair tool for the geometric input of component C6: the exact σ-algebra
equality `biOrbit t S = borel X₃` is **false** (uncountably many fixed points of `aDiag t ·`:
`EKLC6Core/gen_partition_of_core.lean`, `fullSigma_ne_inst_of_uncountable_fixed`), while the
singleton-atom property — which the Pisa 7.37/7.38 Markov core supplies directly
(`atom M x = {x}` off a `μ`-null set) — is exactly what the general separation criterion
`Work.EKLC6Core.Ch_exists_measurableSet_ae_eq_of_atom_singleton` consumes.

The only new ingredients are that `biOrbit t S` is countably generated and contained in the Borel
σ-algebra; both are proved here for an arbitrary measurable family `S`.
-/

open MeasureTheory

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The bi-infinite orbit σ-algebra of a countable measurable family is contained in the Borel
σ-algebra. -/
theorem le_biOrbit (t : Fin 3 → ℝ) (S : ℕ → Set X3) (hS : ∀ n, MeasurableSet (S n)) :
    biOrbit t S ≤ instMeasurableSpaceX3 := by
  rw [biOrbit]
  refine iSup_le fun n => sup_le ?_ ?_
  · refine (MeasurableSpace.comap_mono ?_).trans
      (measurable_iff_comap_le.mp (((continuous_const_smul (aDiag t)).measurable).iterate n))
    exact MeasurableSpace.generateFrom_le fun s hs => by
      obtain ⟨i, rfl⟩ := hs
      exact hS i
  · refine (MeasurableSpace.comap_mono ?_).trans
      (measurable_iff_comap_le.mp (((continuous_const_smul (aDiag (-t))).measurable).iterate n))
    exact MeasurableSpace.generateFrom_le fun s hs => by
      obtain ⟨i, rfl⟩ := hs
      exact hS i

/-- The bi-infinite orbit σ-algebra of a countable family is countably generated. -/
theorem cg_biOrbit (t : Fin 3 → ℝ) (S : ℕ → Set X3) :
    ∃ b : Set (Set X3), b.Countable ∧ biOrbit t S = MeasurableSpace.generateFrom b := by
  refine ⟨⋃ n : ℕ, (Set.range (fun i : ℕ => ((fun x : X3 => aDiag t • x)^[n]) ⁻¹' (S i)) ∪
      Set.range (fun i : ℕ => ((fun x : X3 => aDiag (-t) • x)^[n]) ⁻¹' (S i))), ?_, ?_⟩
  · exact Set.countable_iUnion fun _ => (Set.countable_range _).union (Set.countable_range _)
  · have hstep : ∀ (f : X3 → X3) (n : ℕ),
        MeasurableSpace.comap (f^[n]) (MeasurableSpace.generateFrom (Set.range S))
          = MeasurableSpace.generateFrom (Set.range (fun i : ℕ => (f^[n]) ⁻¹' (S i))) := by
      intro f n
      rw [MeasurableSpace.comap_generateFrom]
      congr 1
      rw [← Set.range_comp]
      rfl
    have hsup : ∀ A B : Set (Set X3),
        MeasurableSpace.generateFrom A ⊔ MeasurableSpace.generateFrom B
          = MeasurableSpace.generateFrom (A ∪ B) := by
      intro A B
      refine le_antisymm ?_ ?_
      · refine sup_le (MeasurableSpace.generateFrom_mono Set.subset_union_left)
          (MeasurableSpace.generateFrom_mono Set.subset_union_right)
      · refine MeasurableSpace.generateFrom_le fun s hs => ?_
        rcases hs with hs | hs
        · exact MeasurableSpace.le_def.mp le_sup_left s
            (MeasurableSpace.measurableSet_generateFrom hs)
        · exact MeasurableSpace.le_def.mp le_sup_right s
            (MeasurableSpace.measurableSet_generateFrom hs)
    have hiUnion : MeasurableSpace.generateFrom
          (⋃ n : ℕ, (Set.range (fun i : ℕ => ((fun x : X3 => aDiag t • x)^[n]) ⁻¹' (S i)) ∪
            Set.range (fun i : ℕ => ((fun x : X3 => aDiag (-t) • x)^[n]) ⁻¹' (S i))))
        = ⨆ n : ℕ, MeasurableSpace.generateFrom
            (Set.range (fun i : ℕ => ((fun x : X3 => aDiag t • x)^[n]) ⁻¹' (S i)) ∪
              Set.range (fun i : ℕ => ((fun x : X3 => aDiag (-t) • x)^[n]) ⁻¹' (S i))) := by
      refine le_antisymm ?_ ?_
      · refine MeasurableSpace.generateFrom_le fun s hs => ?_
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hs
        exact MeasurableSpace.le_def.mp (le_iSup (fun n : ℕ => MeasurableSpace.generateFrom
            (Set.range (fun i : ℕ => ((fun x : X3 => aDiag t • x)^[n]) ⁻¹' (S i)) ∪
              Set.range (fun i : ℕ => ((fun x : X3 => aDiag (-t) • x)^[n]) ⁻¹' (S i)))) n) s
          (MeasurableSpace.measurableSet_generateFrom hn)
      · refine iSup_le fun n => MeasurableSpace.generateFrom_mono ?_
        intro s hs
        exact Set.mem_iUnion.mpr ⟨n, hs⟩
    rw [biOrbit, hiUnion]
    refine iSup_congr fun n => ?_
    rw [hstep (fun x : X3 => aDiag t • x) n, hstep (fun x : X3 => aDiag (-t) • x) n, hsup]

/-- **The mod-`μ` generator criterion for a countable family.** -/
theorem generatesModMuSet_of_atom_singleton {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ) (S : ℕ → Set X3)
    (hS : ∀ n, MeasurableSet (S n))
    (Z : Set X3) (hZ : MeasurableSet Z) (hZc : μ Zᶜ = 0)
    (hatom : ∀ x ∈ Z, atom (biOrbit t S) x = {x}) :
    GeneratesModMuSet μ t S := by
  intro E hE
  obtain ⟨E', hE', h1, h2⟩ :=
    Ch_exists_measurableSet_ae_eq_of_atom_singleton (μ := μ) Work.EKLComp.X3Background.2.2.2.2
      ⟨biOrbit t S⟩ (le_biOrbit t S hS) (cg_biOrbit t S) Z hZ hZc
      (fun x hx y hy => by
        have hmem : y ∈ atom (biOrbit t S) x :=
          Set.mem_sInter.mpr fun s hs => hy s hs.1 hs.2
        rw [hatom x hx] at hmem
        exact Set.mem_singleton_iff.mp hmem) E hE
  exact ⟨E', hE', h1, h2⟩

end Work.EKLC6Core

end
