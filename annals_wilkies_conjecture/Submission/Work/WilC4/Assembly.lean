/-
  WilC4/Assembly : the frozen `ValIneq` (Wilkie's relativised valuation inequality for `TR`)
  from the van den Dries–Speissegger preparation step plus the rank induction of the area.

  The chain proved here is

      `PreparationStep`  ⟹  `ValIneq`

  where at each step the values of the definable closure are tracked by `ValSpans`:

  * `valSpans_dcl_range` (the induction on the number of generators): for a `dcl`-closed base
    `S` and generators `a : Fin k → M`, the values occurring in `Dcl S (range a)` are spanned
    over `Γ S` by `k` values.  Base case: `Dcl S ∅ = S` and `ValSpans S S 0`.  Step: split off
    the last generator, apply `PreparationStep` to the base `Dcl S (range a|Fin k)` (which is
    `dcl`-closed and a value base by `dcl_idem`/`dcl_valBase`), and combine with
    `valSpans_step`.
  * `valSpans_use` (the rank argument): `r` spanning values and `m` values that are
    ℤ-independent modulo `Γ S` force `m ≤ r`.

  Consequences for `ValIneq`: `S` is an elementary substructure, so `Dcl S ∅ = S`
  (`dcl_elementary`) and `Γ S` is a subgroup (`elementary_valBase`); each `b j` lies in
  `Dcl S (range a)` by hypothesis, and its value is independent, so `valSpans_use` gives
  `m ≤ k`.
-/
import Submission.Work.WilC4.Defs
import Submission.Work.WilC4.valSpans_use
import Submission.Work.WilC4.valSpans_step
import Submission.Work.WilC4.valSpans_self_zero
import Submission.Work.WilC4.dcl_elementary
import Submission.Work.WilC4.dcl_idem
import Submission.Work.WilC4.dcl_valBase
import Submission.Work.WilC4.elementary_valBase
import Submission.Work.WilC4.definableElt_of_mem_left
import Submission.Work.WilC4.valEq_refl

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Classical
namespace Work.WilC4
open WilkiesDesign WilkiesDesign.CG FirstOrder FirstOrder.Language

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [Ring.CompatibleRing M]
  [rexpL.Structure M] [(constantsOn ℝ).Structure M]

/-- The range of a map on `Fin (k+1)` is the range of its restriction to the first `k`
coordinates together with the last value. -/
theorem range_castSucc_union_last {k : ℕ} (a : Fin (k + 1) → M) :
    Set.range a = Set.range (fun i : Fin k => a (Fin.castSucc i)) ∪ {a (Fin.last k)} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.lastCases ?_ ?_ i
    · exact Or.inr rfl
    · intro j
      exact Or.inl ⟨j, rfl⟩
  · rintro (⟨j, rfl⟩ | rfl)
    · exact ⟨Fin.castSucc j, rfl⟩
    · exact ⟨Fin.last k, rfl⟩

/-- `Dcl S A` is `dcl`-closed as soon as `S` is: `Dcl (Dcl S A) ∅ = Dcl S A`. -/
theorem definableElt_dcl_self {S A : Set M}
    (_hS : ∀ x : M, DefinableElt S ∅ x ↔ x ∈ S) :
    ∀ x : M, DefinableElt (Dcl S A) ∅ x ↔ x ∈ Dcl S A := by
  intro x
  rw [show DefinableElt (Dcl S A) ∅ x ↔ x ∈ Dcl (Dcl S A) ∅ from Iff.rfl,
    dcl_idem S A ∅, Set.union_empty]

/-- **The rank induction.**  For a `dcl`-closed value base `S` and generators
`a : Fin k → M`, the values occurring in the definable closure `Dcl S (range a)` are spanned
over `Γ S` by `k` values. -/
theorem valSpans_dcl_range (hP : PreparationStep) (hM : M ⊨ TR) (S : Set M)
    (hSb : IsValBase S) (hSdcl : ∀ x : M, DefinableElt S ∅ x ↔ x ∈ S) (k : ℕ)
    (a : Fin k → M) : ValSpans S (Dcl S (Set.range a)) k := by
  induction k with
  | zero =>
    have hrange : Set.range a = (∅ : Set M) := by
      ext x
      exact ⟨fun h => (by rcases h with ⟨i, -⟩; exact i.elim0), fun h => absurd h (Set.notMem_empty x)⟩
    have hDS : Dcl S (∅ : Set M) = S := Set.ext fun x => hSdcl x
    rw [hrange, hDS]
    exact valSpans_self_zero hSb
  | succ k ih =>
    obtain ⟨δ, hδ0, hδV⟩ := hP M hM (Dcl S (Set.range fun i : Fin k => a (Fin.castSucc i)))
      (fun x => definableElt_dcl_self hSdcl x) (a (Fin.last k))
    rw [range_castSucc_union_last a,
      show Dcl S (Set.range (fun i : Fin k => a (Fin.castSucc i)) ∪ {a (Fin.last k)})
        = Dcl (Dcl S (Set.range (fun i : Fin k => a (Fin.castSucc i)))) {a (Fin.last k)}
        from (dcl_idem S (Set.range fun i : Fin k => a (Fin.castSucc i)) {a (Fin.last k)}).symm]
    exact valSpans_step hSb (dcl_valBase hSb) (ih (fun i : Fin k => a (Fin.castSucc i))) hδV

/-- **Wilkie's relativised valuation inequality for `TR` from the preparation step.** -/
theorem valIneq_of_preparation (hP : PreparationStep) : ValIneq := by
  intro M _ _ _ _ _ _ hM S k m a b hb0 hbdef hind
  have hSb : IsValBase (S : Set M) := elementary_valBase S
  have hSdcl : ∀ x : M, DefinableElt (S : Set M) ∅ x ↔ x ∈ (S : Set M) := fun x =>
    (show x ∈ Dcl (S : Set M) ∅ ↔ x ∈ (S : Set M) from
      Iff.of_eq (congrArg (fun t : Set M => x ∈ t) (dcl_elementary S)))
  have hspan := valSpans_dcl_range (M := M) hP hM (S : Set M) hSb hSdcl k a
  have hV : ∀ j, ValOf (Dcl (S : Set M) (Set.range a)) (b j) := fun j =>
    ⟨b j, hbdef j, hb0 j, valEq_refl (b j)⟩
  exact valSpans_use b hSb hspan hV hind

end Work.WilC4
