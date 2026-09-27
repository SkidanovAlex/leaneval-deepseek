import Mathlib
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLC7.SupportFacts
import Submission.Work.EKLContract.Lemmas.Box1_Uij
import Submission.Work.EKLContract.Lemmas.SL3Topology

/-!
# C7: the support of a nontrivial leafwise measure on `U_ij` is not small

`Work.EKLC7.SuppSmall` is the last piece of the C7 (commutator) computation: if `ν` is a
system of leafwise measures for the root group `U_ij` of an `A`-ergodic probability measure
`μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, and if `μ` has *no* `U_ij`-cross-section (i.e. the leafwise
measures are non-trivial, Pisa 6.23), then `ν x = δ₁` for no `x` (a.e. `x`), `ν x` charges
every ball `ballU hij ε` (`= u_ij([-ε,ε])`) around the identity, gives no mass to `{1}`, and
has a point `u_ij(r)`, `r ≠ 0`, in its support.

Mathematically:
* `ν x ≠ δ₁` and `ν x {1} = 0` are the ergodic dichotomy (U8) of `P_Leafwise`: an ergodic
  `A`-invariant `μ` either has a `U_ij`-cross-section, or the leafwise measure has no atom at
  the identity a.e.  The hypothesis `¬ CrossSection μ (U_ij)` therefore selects the second
  alternative.  (`δ₁ {1} = 1 ≠ 0` gives `ν x ≠ δ₁` from `ν x {1} = 0`.)
* `0 < ν x (ballU hij ε)`: `IsLeafwise.pos` gives `0 < ν x (V δ)` for every `δ > 0`, `ν x` is
  carried by `U_ij`, and `V ε ∩ U_ij = u_ij((-ε,ε)) ⊆ u_ij([-ε,ε])`.
* The support is contained in the closed subgroup `U_ij` (a measure carried by a closed set has
  its support in that set), and `ν x` is non-zero (normalised: `ν x (Box1 U_ij) = 1`).  Since
  `ν x {1} = 0` and (`SL₃(ℝ)` being second countable) the support is conull, the support cannot
  be `{1}`, and `U_ij = {u_ij(s)}` then provides `r ≠ 0` with `u_ij(r) ∈ support`.
-/

namespace Work.EKLC7

open MeasureTheory Filter Topology
open Work.EKLContract

set_option linter.unusedSimpArgs false

/-- `SL₃(ℝ)` is second countable (its topology is the subspace topology of the matrix space
`(Fin 3 → Fin 3 → ℝ)`, a finite product of copies of `ℝ`); hence hereditarily Lindelöf, and the
support of any measure on it is conull.  `Matrix` is a `def` that instance search does not
unfold, so the instance is recorded here. -/
instance instSecondCountableTopologySL3SuppSmall :
    SecondCountableTopology Work.EKLContract.SL3 :=
  Work.EKLContract.Lemmas.SL3Topology.2

/-- The displacement neighbourhood `V ε` of the identity, intersected with the root group
`U_ij`, lies in the ball `ballU hij ε = u_ij([-ε,ε])`. -/
theorem V_inter_Uij_subset_ballU {i j : Fin 3} (hij : i ≠ j) (ε : ℝ) :
    V ε ∩ (Uij hij : Set SL3) ⊆ ballU hij ε := by
  intro g hg
  obtain ⟨hgV, hgU⟩ := hg
  obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hij g).mp hgU
  have h1 : ((uij hij s : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j = s :=
    Work.EKLContract.Lemmas.uij_apply_self hij s
  have h2 : (1 : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 :=
    Work.EKLContract.Lemmas.one_apply_ne hij
  have h3 := hgV i j
  rw [h1, h2, sub_zero] at h3
  exact ⟨s, ⟨le_of_lt (abs_lt.mp h3).1, le_of_lt (abs_lt.mp h3).2⟩, rfl⟩

/-- A measure on `SL₃(ℝ)` carried by the root group `U_ij` and charging every
`V δ` positively charges every ball `ballU hij ε` around the identity. -/
theorem ballU_pos_of_carried_pos {i j : Fin 3} (hij : i ≠ j) (ν : Measure SL3)
    (hcarried : ν (Uij hij : Set SL3)ᶜ = 0)
    (hpos : ∀ δ : ℝ, 0 < δ → 0 < ν (V δ)) :
    ∀ ε : ℝ, 0 < ε → 0 < ν (ballU hij ε) := by
  intro ε hε
  have hnull : ν (V ε ∩ (Uij hij : Set SL3)ᶜ) = 0 :=
    measure_mono_null Set.inter_subset_right hcarried
  have hsplit : V ε ⊆ (V ε ∩ (Uij hij : Set SL3)) ∪ (V ε ∩ (Uij hij : Set SL3)ᶜ) := by
    intro g hg
    by_cases h : g ∈ (Uij hij : Set SL3)
    · exact Or.inl ⟨hg, h⟩
    · exact Or.inr ⟨hg, h⟩
  have hle : ν (V ε) ≤ ν (V ε ∩ (Uij hij : Set SL3)) := by
    calc ν (V ε)
        ≤ ν ((V ε ∩ (Uij hij : Set SL3)) ∪ (V ε ∩ (Uij hij : Set SL3)ᶜ)) :=
          measure_mono hsplit
      _ ≤ ν (V ε ∩ (Uij hij : Set SL3)) + ν (V ε ∩ (Uij hij : Set SL3)ᶜ) :=
          measure_union_le _ _
      _ = ν (V ε ∩ (Uij hij : Set SL3)) := by rw [hnull, add_zero]
  exact lt_of_lt_of_le (lt_of_lt_of_le (hpos ε hε) hle)
    (measure_mono (V_inter_Uij_subset_ballU hij ε))

/-- A non-zero measure on `SL₃(ℝ)` carried by the root group `U_ij` and giving no mass to the
identity has a point `u_ij(r)`, `r ≠ 0`, in its support.  (`SL₃(ℝ)` is second countable, so the
complement of the support is null; if the support contained no such point it would be `{1}` and
the measure would vanish.) -/
theorem exists_uij_mem_support_of_carried {i j : Fin 3} (hij : i ≠ j) (ν : Measure SL3)
    (hcarried : ν (Uij hij : Set SL3)ᶜ = 0) (h1 : ν {1} = 0) (hne : ν ≠ 0) :
    ∃ r : ℝ, r ≠ 0 ∧ uij hij r ∈ ν.support := by
  by_contra h
  push Not at h
  -- the support is contained in the closed subgroup `U_ij`
  have hsupp : ν.support ⊆ (Uij hij : Set SL3) :=
    Set.compl_subset_compl.mp
      (Measure.subset_compl_support_of_isOpen
        (Work.EKLContract.Lemmas.horoUij_isClosed hij).isOpen_compl hcarried)
  -- ... and, by assumption, in the singleton `{1}`
  have hsub1 : ν.support ⊆ ({1} : Set SL3) := by
    intro g hg
    obtain ⟨s, hs⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hij g).mp (hsupp hg)
    by_cases hs0 : s = 0
    · rw [hs0] at hs
      rw [← hs, Work.EKLContract.Lemmas.horoUij_zero hij]
      exact Set.mem_singleton 1
    · exact absurd (hs.symm ▸ hg) (h s hs0)
  have hcompl : ν (({1} : Set SL3)ᶜ) = 0 :=
    measure_mono_null (Set.compl_subset_compl.mpr hsub1) Measure.measure_compl_support
  have huniv : ν Set.univ ≤ 0 := by
    calc ν Set.univ = ν (({1} : Set SL3) ∪ ({1} : Set SL3)ᶜ) := by rw [Set.union_compl_self]
      _ ≤ ν ({1} : Set SL3) + ν (({1} : Set SL3)ᶜ) := measure_union_le _ _
      _ = 0 := by rw [h1, hcompl, add_zero]
  exact hne (Measure.measure_univ_eq_zero.mp (le_antisymm huniv zero_le))

theorem SuppSmall :
    Work.EKLContract.P_Leafwise →
    ∀ (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ],
      Work.EKLContract.IsAErgodic μ →
      ∀ {i j : Fin 3} (hij : i ≠ j)
        (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
        (X' : Set Work.EKLContract.X3),
        Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij hij) ν X' →
        ¬ Work.EKLContract.CrossSection μ (Work.EKLContract.Uij hij) →
        ∀ᵐ x ∂μ, ν x ≠ MeasureTheory.Measure.dirac 1
          ∧ (∀ ε : ℝ, 0 < ε → 0 < ν x (Work.EKLContract.ballU hij ε))
          ∧ ν x {1} = 0
          ∧ (∃ r : ℝ, r ≠ 0 ∧ Work.EKLContract.uij hij r ∈ (ν x).support) := by
  intro hPL μ _ hErg i j hij ν X' hLeaf hNoCross
  -- the leafwise system is the one supplied by `P_Leafwise`, so its clauses (U1)–(U9) apply
  obtain ⟨t0, ht0⟩ := (Work.EKLContract.Lemmas.isHoro_Uij hij).2.2
  have hMP : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ := hErg.1 t0
  obtain ⟨-, -, -, -, -, -, -, hU8, -⟩ :=
    (hPL μ (Uij hij) (Work.EKLContract.Lemmas.isHoro_Uij hij) t0 hMP ht0).2 ν X' hLeaf
  -- (U8): ergodicity + no cross-section ⇒ no atom at the identity a.e.
  have hν1 : ∀ᵐ x ∂μ, ν x {1} = 0 := by
    rcases hU8 hErg with hcs | h
    · exact absurd hcs hNoCross
    · exact h
  have hX' : ∀ᵐ x ∂μ, x ∈ X' := mem_ae_iff.mpr hLeaf.conull
  filter_upwards [hν1, hX'] with x hx1 hxX
  have hcarried := hLeaf.carried x hxX
  have hnorm := hLeaf.normalised x hxX
  have hne : ν x ≠ 0 := by
    intro h0
    have hz : ν x (Box1 (Uij hij)) = 0 := by rw [h0]; simp
    rw [hz] at hnorm
    exact zero_ne_one hnorm
  refine ⟨?_, ?_, hx1, ?_⟩
  · intro hdirac
    rw [hdirac, Measure.dirac_apply_of_mem (Set.mem_singleton 1)] at hx1
    exact one_ne_zero hx1
  · exact ballU_pos_of_carried_pos hij (ν x) hcarried (hLeaf.pos x hxX)
  · exact exists_uij_mem_support_of_carried hij (ν x) hcarried hx1 hne

end Work.EKLC7
