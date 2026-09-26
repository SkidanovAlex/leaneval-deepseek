import Submission.Work.Item3.EnergyExtract
import Submission.Work.ConjectureK
import Submission.Work.StrictDescent
import Submission.Work.AssemblyBridge
import Submission.Work.NielsenEnergy

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
set_option autoImplicit false

/-!
# The `(N, energy)` descent: `aut_nielsen` from the residual Conjecture K

`NielsenEnergy.energy_terminates` shows that the lexicographic `(N, eEnergy)`
descent is well-founded.  `Item3/EnergyExtract.lean` shows that a *residual*
half-length-1 Fall-II configuration has a single closure move preserving `N`
and strictly decreasing `eEnergy`; the Fall I/II dichotomy
(`aggregate_reduces_or_balanced`) and `¬ NoEndCancel ⟹ strict single move`
supply the rest.  Hence, modulo the single combinatorial statement

> **(K, residual form)** `ConjectureKResidual n`: a residual state carries no
> `k ≥ 2` balanced configuration  — *** CAVEAT (this session): this statement is
> FALSE ***.  Machine counterexample: the `F₃` basis
> `[a₀a₀A₂A₁, a₁a₂a₀A₂, a₂A₀A₀A₀a₁]` is residual and carries a confined
> `k = 2` balanced configuration in the aggregate of `a₁` (details in
> `Submission/Status.lean`).  The theorem `aut_nielsen_of_conjectureKResidual`
> below is therefore *vacuous as an application*; the file is kept because the
> surrounding descent/assembly machinery (`reachable_signed_of_energyStep`,
> `aut_nielsen_of_energyStep`) is the correct remaining architecture.  What must
> be proved instead is the *macro* energy step (see `Status.lean`, "Re-aimed
> target"): every non-signed-permutation state admits a closure macro with
> `N`-decrease or `N`-preserving `eEnergy`-decrease.  (For an elementary
> statement: the general-`k` cut-slide lemma, in the non-degenerate case
> `rankseq B ≠ rev rankseq A`, holds for all `k` and is not yet formalised; the
> degenerate case and rare stuck states need inversions/other transvections.)

the elementary Nielsen moves generate `Aut(F_n)` — by the `(N, energy)`
well-founded descent, with no pass iteration and no index-advance argument.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- **The `(N, energy)` descent.**  If every non-signed-permutation
automorphism admits a closure element that either strictly decreases `N` or
keeps `N` and strictly decreases the energy, then every automorphism is
right-composable into a signed permutation. -/
theorem reachable_signed_of_energyStep {n : ℕ}
    (hstep : ∀ α : MulAut (FreeGroup (Fin n)), ¬ IsSignedPermutation α →
      ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
        (N (α * γ) < N α ∨ (N (α * γ) = N α ∧ eEnergy (α * γ) < eEnergy α))) :
    ∀ α : MulAut (FreeGroup (Fin n)),
      ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ IsSignedPermutation (α * γ) := by
  classical
  have hwf : WellFounded (fun b a : MulAut (FreeGroup (Fin n)) =>
      N b < N a ∨ (N b = N a ∧ eEnergy b < eEnergy a)) :=
    energy_terminates N eEnergy
  intro α
  let C : MulAut (FreeGroup (Fin n)) → Prop :=
    fun α => ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ IsSignedPermutation (α * γ)
  refine WellFounded.fix hwf (C := C) ?_ α
  intro x rec
  by_cases ht : IsSignedPermutation x
  · refine ⟨1, (AutClosure n).one_mem, ?_⟩
    simpa using ht
  · rcases hstep x ht with ⟨γ0, hγ0, hstep'⟩
    rcases rec (x * γ0) hstep' with ⟨γ1, hγ1, hS⟩
    refine ⟨γ0 * γ1, (AutClosure n).mul_mem hγ0 hγ1, ?_⟩
    simpa [mul_assoc] using hS

/-- **`aut_nielsen` from the `(N, energy)` step.** -/
theorem aut_nielsen_of_energyStep {n : ℕ}
    (hstep : ∀ α : MulAut (FreeGroup (Fin n)), ¬ IsSignedPermutation α →
      ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
        (N (α * γ) < N α ∨ (N (α * γ) = N α ∧ eEnergy (α * γ) < eEnergy α))) :
    Subgroup.closure (AutGen n : Set (MulAut (FreeGroup (Fin n)))) = ⊤ :=
  aut_nielsen_of_reachable_signed n (reachable_signed_of_energyStep hstep)

/-- **The macro energy step (the re-aimed pin).**  Every state that is not a
signed permutation admits a *closure macro* (not necessarily a single
elementary move) that either strictly decreases `N` or, keeping `N`, strictly
decreases the positional energy `eEnergy`.  This is the hypothesis consumed by
`aut_nielsen_of_energyStep`; unlike `ConjectureKResidual` (FALSE, see the
module note) and `ExactSeamLocalization` (FALSE), it is exactly what the
well-founded `(N, eEnergy)` descent needs and it is machine-supported
(`FallTwoRunNotes.md`: the classical cut-slide step covers the non-degenerate
half-length cases for *all* `k` — `Item3/EnergyStepGeneral.lean` — with the
fallback list `[L1, R1, invert the balanced row, …]`; single elementary moves
suffice except in `15/35 697` random residual peaks, where a short macro
exists). -/
def EnergyStepMacro (n : ℕ) : Prop :=
  ∀ α : MulAut (FreeGroup (Fin n)), ¬ IsSignedPermutation α →
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      (N (α * γ) < N α ∨ (N (α * γ) = N α ∧ eEnergy (α * γ) < eEnergy α))

/-- **`aut_nielsen` from the macro energy step** — the re-aimed architecture
(all the descent machinery is PROVEN; only `EnergyStepMacro` remains). -/
theorem aut_nielsen_of_energyStepMacro {n : ℕ} (h : EnergyStepMacro n) :
    Subgroup.closure (AutGen n : Set (MulAut (FreeGroup (Fin n)))) = ⊤ :=
  aut_nielsen_of_energyStep h

/-- The step, from the residual Conjecture K (kept for the record; the
hypothesis is FALSE, so this is vacuous as an application).  A non-signed-permutation
automorphism either admits a strict single move (if it is not residual), or a
strict closure move (the Fall-I branch of the dichotomy), or — in the residual
Fall-II branch — K forces half-length 1, where the energy step applies. -/
theorem energyStep_of_conjectureKResidual {n : ℕ} (hK : ConjectureKResidual n) :
    ∀ α : MulAut (FreeGroup (Fin n)), ¬ IsSignedPermutation α →
      ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
        (N (α * γ) < N α ∨ (N (α * γ) = N α ∧ eEnergy (α * γ) < eEnergy α)) := by
  intro α hnot
  by_cases hres : NoEndCancel n α
  · have hlong := not_signed_has_long_image α hnot
    rcases aggregate_reduces_or_balanced α hlong with hstrict | hbal
    · obtain ⟨γ, hγ, hlt⟩ := hstrict
      exact ⟨γ, hγ, Or.inl hlt⟩
    · obtain ⟨m, j, hj, hj0, hj1, hconf, A, B, X, Z, hmid, hAB, hl, hr⟩ := hbal
      -- K forces half-length 1
      have hk1 : A.length = 1 := by
        have hne : A.length ≠ 0 := by
          intro h0
          have hA0 : A = [] := List.length_eq_zero_iff.mp h0
          have hB0 : B = [] := List.length_eq_zero_iff.mp (by rw [← hAB, h0])
          have hw : ((imageAggregate α m)[j]).toWord = [] := by
            rw [hmid, hA0, hB0]
            rfl
          have hone : (imageAggregate α m)[j] = 1 := by
            rw [← FreeGroup.mk_toWord (x := (imageAggregate α m)[j]), hw]
            rfl
          exact (systemReduced_imageAggregate α m).1 _ (List.getElem_mem hj) hone
        rcases Nat.lt_or_ge A.length 2 with h2 | h2
        · omega
        · exact absurd ⟨m, j, hj, hj0, hj1, hconf, A, B, X, Z, hmid, hAB, h2, hl, hr⟩ (hK α hres)
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hk1
      obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp (by rw [← hAB, hk1] : B.length = 1)
      obtain ⟨q, hq⟩ := aggregate_factor_coordinate α (imageAggregate α m)
        (imageAggregate_isImageAggregate α m) hj
      rcases energy_step_aggregate α hres m hj hj0 hj1 hq a b X Z
        (by rw [hmid, ha, hb]) (by rw [hl, ha]) (by rw [hr, hb]) with
        ⟨γ, hγ, hN, hE⟩
      refine ⟨γ, hγ, ?_⟩
      by_cases hlt : N (α * γ) < N α
      · exact Or.inl hlt
      · exact Or.inr ⟨le_antisymm hN (not_lt.mp hlt), hE⟩
  · rcases nonresidual_strict_move α hres with ⟨γ, hγ, hlt⟩
    exact ⟨γ, hγ, Or.inl hlt⟩

/-- **`aut_nielsen` from the residual Conjecture K.** -/
theorem aut_nielsen_of_conjectureKResidual {n : ℕ} (hK : ConjectureKResidual n) :
    Subgroup.closure (AutGen n : Set (MulAut (FreeGroup (Fin n)))) = ⊤ :=
  aut_nielsen_of_energyStep (energyStep_of_conjectureKResidual hK)

/-! ## The Fall-II-level pin (the cleanest form of the remaining input)

`EnergyStepMacro` is stated for *every* non-signed-permutation state.  By
`nonresidual_strict_move` (a non-residual state has a strict single move) and
`aggregate_reduces_or_balanced` (a residual state with a long image either has
a strict closure move or exhibits `FallTwoConfig`), it suffices to prove the
energy step **at a `FallTwoConfig` of a residual state**.  That is the form
`FallTwoEnergyStep` below; `EnergyStepMacro` follows. -/

/-- **The residual Fall-II pin.**  Every residual (`NoEndCancel`) state with a
`FallTwoConfig` (a confined balanced interior factor of an image aggregate)
admits a closure macro that keeps `N` and strictly decreases the positional
energy. -/
def FallTwoEnergyStep (n : ℕ) : Prop :=
  ∀ α : MulAut (FreeGroup (Fin n)), NoEndCancel n α → FallTwoConfig α →
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      N (α * γ) = N α ∧ eEnergy (α * γ) < eEnergy α

/-- **`EnergyStepMacro` from the residual Fall-II pin.** -/
theorem energyStep_of_fallTwoEnergyStep {n : ℕ} (h : FallTwoEnergyStep n) :
    EnergyStepMacro n := by
  intro α hnot
  by_cases hres : NoEndCancel n α
  · have hlong := not_signed_has_long_image α hnot
    rcases aggregate_reduces_or_balanced α hlong with hstrict | hbal
    · obtain ⟨γ, hγ, hlt⟩ := hstrict
      exact ⟨γ, hγ, Or.inl hlt⟩
    · obtain ⟨γ, hγ, hN, hE⟩ := h α hres hbal
      exact ⟨γ, hγ, Or.inr ⟨hN, hE⟩⟩
  · obtain ⟨γ, hγ, hlt⟩ := nonresidual_strict_move α hres
    exact ⟨γ, hγ, Or.inl hlt⟩

/-- **`aut_nielsen` from the residual Fall-II pin.** -/
theorem aut_nielsen_of_fallTwoEnergyStep {n : ℕ} (h : FallTwoEnergyStep n) :
    Subgroup.closure (AutGen n : Set (MulAut (FreeGroup (Fin n)))) = ⊤ :=
  aut_nielsen_of_energyStepMacro (energyStep_of_fallTwoEnergyStep h)

end Submission.Nielsen
