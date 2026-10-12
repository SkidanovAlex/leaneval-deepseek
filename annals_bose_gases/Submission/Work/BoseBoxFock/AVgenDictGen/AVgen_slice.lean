import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.sliceTransport
import Submission.Work.BoseBoxFock.slotAVgen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.AVgenDictGen

/-- **The function-level form of `Work.BoseBoxFock.boxSlotSum_slice`.**  The one-body box slot sum
`Work.BoseDict.boxSlotSum e T`, applied to the `sliceEquiv S`-reindexed state, *is* (as a function)
the `↥S`-slot sum `Work.BoseBoxFock.slotSumSub e T S` applied to the state and then reindexed: the
pointwise identity `Work.BoseBoxFock.boxSlotSum_slice` after `funext`.

This is the form in which the transport is stable under **composition** of slot sums, which is what
the pair rows of `Work.BoseBoxFock.AVgen` need: the inner factor `boxSlotSum e T₂ (fun x => Ψ (φ x))`
occurs *unapplied* there, so the pointwise lemma does not see it. -/
lemma boxSlotSum_slice_fun {m n : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (S : Finset (Fin n))
    (Ψ : ({i // i ∈ S} → EuclideanSpace ℝ (Fin 3)) → ℂ) :
    Work.BoseDict.boxSlotSum e T (fun x => Ψ (Work.BoseBoxFock.sliceEquiv S x))
      = fun x => Work.BoseBoxFock.slotSumSub e T S Ψ (Work.BoseBoxFock.sliceEquiv S x) :=
  funext fun u => Work.BoseBoxFock.boxSlotSum_slice e T S Ψ u

/-- **The `sliceEquiv S` transport of the whole `AVgen` expression.**

`Work.BoseBoxFock.boxSlotSum_slice` (in `sliceTransport.lean`) transports one atom
`Work.BoseDict.boxSlotSum e T` along the measurable equivalence `Work.BoseBoxFock.sliceEquiv S`
(which identifies `Fin S.card → Ω` with `{i // i ∈ S} → Ω`); this is the corresponding transport of
the *whole* operator `AVgen (fun T => boxSlotSum e T) id …`.  For every state
`X : ({i // i ∈ S} → Ω) → ℂ` and every `u : Fin S.card → Ω`,

    AVgen (boxSlotSum e) id … (fun x => X (sliceEquiv S x)) u
      = AVgen (slotSumSub e · S) (fun Y => Y) … X (sliceEquiv S u).

Proof: `AVgen`'s every atom is a one-body slot sum `boxSlotSum e T`, a composition of two of them,
or the (unused) identity; `boxSlotSum_slice` gives the pointwise transport of `boxSlotSum e T`, and
its function-level form `boxSlotSum e T (fun x => Ψ (sliceEquiv S x))
= fun u => slotSumSub e T S Ψ (sliceEquiv S u)` makes the closure under composition work; sums,
differences and real multiples close trivially.  No measure theory, no good-state hypothesis. -/
theorem AVgen_slice {m n : ℕ} [NeZero m] (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (T_NH : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (PHs : Finset Mode)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) (S : Finset (Fin n))
    (X : ({i // i ∈ S} → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (u : Fin S.card → EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
        (id : (Work.BoseDict.Xn S.card → ℂ) → (Work.BoseDict.Xn S.card → ℂ))
        f g T_NH PHs E gHat0 (fun x => X (Work.BoseBoxFock.sliceEquiv S x)) u
      = Work.BoseBoxFock.AVgen (fun T => Work.BoseBoxFock.slotSumSub e T S) (fun Y => Y)
          f g T_NH PHs E gHat0 X (Work.BoseBoxFock.sliceEquiv S u) := by
  -- Unfold the seven rows of `AVgen`, β-reduce the parametrising lambdas, and push the state
  -- argument inside the finite sums, the pointwise additions/subtractions and the pointwise
  -- scalar multiples.  `boxSlotSum_slice_fun` then rewrites every one-body atom, and — because it
  -- is a *function-level* identity — it also rewrites the inner factor of every pair row
  -- `(B T₁) ∘ (B T₂)` and of `B (T₁ ∘ T₂)`, while `Function.comp_apply` unfolds the compositions.
  simp only [Work.BoseBoxFock.AVgen, boxSlotSum_slice_fun, Finset.sum_apply, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, Function.comp_apply]

end Work.BoseBoxFock.AVgenDictGen
