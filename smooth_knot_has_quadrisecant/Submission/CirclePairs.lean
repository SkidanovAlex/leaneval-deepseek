import Mathlib
import Submission.Helpers
import Submission.SecantSpace
import Submission.Pi1Mobius

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# The open Möbius band as unordered pairs of *circle* points

The secant space of the parameter model (`SecantSpace.lean`) is the swap
quotient of pairs of parameters `x ∈ AddCircle period`.  Through the
exponential homeomorphism `paramCircleHomeo : AddCircle period ≃ₜ Circle`
the parameter square is homeomorphic to `Circle × Circle`, and the swap
quotient is carried along:

    UnordCirclePairs ≃ₜ CircleUnordPairs,
    OpenMobius       ≃ₜ CircleOpenPairs

(`CircleOpenPairs := {c : (Circle × Circle)/swap // off the diagonal}`).
This identifies the abstract secant space with the classical *plane* model
object — unordered pairs of points of the unit circle — on top of which the
chord parametrisation `OpenMobius ≃ MobiusModel` (`ChordModel.lean`,
`MobiusModel.lean`) will be built in a later module.

Verified here: the swap setoid/quotient on `Circle × Circle` with its class
API (`circleSwapRel`, `circleSwapSetoid`, `CircleUnordPairs`,
`circleUnordMk_eq_iff`, `circleDiagClass`); the homeomorphism
`unordParamCircleEquiv : UnordCirclePairs ≃ₜ CircleUnordPairs` (Mathlib
`Homeomorph.Quotient.congr` applied to `paramCircleHomeo.prodCongr
paramCircleHomeo`, with the swap-relation transport
`pairRel_circle_iff`); the diagonal-class transport (`unordParamCircleEquiv_diag`,
`openDiag_iff`, `openDiag_iff'`); and the restricted homeomorphism
`openMobiusCircleEquiv : OpenMobius ≃ₜ CircleOpenPairs`.
-/

/-- The endpoint-swap involution on pairs of circle points. -/
def circleSwap (c : Circle × Circle) : Circle × Circle := (c.2, c.1)

@[simp]
lemma circleSwap_circleSwap (c : Circle × Circle) : circleSwap (circleSwap c) = c := by
  rfl

lemma continuous_circleSwap : Continuous (circleSwap : Circle × Circle → Circle × Circle) := by
  unfold circleSwap
  exact continuous_snd.prodMk continuous_fst

/-- Two pairs of circle points are equivalent when they are equal or swapped
(the two orders of an unordered pair). -/
def circleSwapRel (c d : Circle × Circle) : Prop := c = d ∨ circleSwap c = d

lemma circleSwapRel_refl (c : Circle × Circle) : circleSwapRel c c := Or.inl rfl

lemma circleSwapRel_symm {c d : Circle × Circle} (h : circleSwapRel c d) : circleSwapRel d c := by
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    rw [← h]
    exact circleSwap_circleSwap c

lemma circleSwapRel_trans {c d e : Circle × Circle} (h : circleSwapRel c d)
    (h' : circleSwapRel d e) : circleSwapRel c e := by
  rcases h with h | h
  · rcases h' with h' | h'
    · exact Or.inl (h.trans h')
    · right
      rw [h]
      exact h'
  · rcases h' with h' | h'
    · right
      rw [← h']
      exact h
    · left
      calc c = circleSwap (circleSwap c) := (circleSwap_circleSwap c).symm
        _ = circleSwap d := congrArg circleSwap h
        _ = e := h'

/-- The swap-orbit equivalence relation on pairs of circle points. -/
instance circleSwapSetoid : Setoid (Circle × Circle) where
  r := circleSwapRel
  iseqv := ⟨circleSwapRel_refl, @circleSwapRel_symm, @circleSwapRel_trans⟩

/-- Unordered pairs of points of the unit circle (a Möbius band with its
boundary of degenerate pairs). -/
abbrev CircleUnordPairs := Quotient circleSwapSetoid

/-- Two pairs of circle points are equal as unordered pairs iff they are
equal or swapped. -/
lemma circleUnordMk_eq_iff (c d : Circle × Circle) :
    ((⟦c⟧ : CircleUnordPairs) = ⟦d⟧) ↔ circleSwapRel c d := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-- The class of a diagonal pair of circle points (a degenerate secant). -/
def circleDiagClass (a : Circle) : CircleUnordPairs := ⟦(a, a)⟧

/-- The open Möbius band in the circle-pair model: classes of *distinct*
circle points. -/
abbrev CircleOpenPairs := {c : CircleUnordPairs // ¬ ∃ a : Circle, c = circleDiagClass a}

/-- The parameter square and the circle square are homeomorphic through the
complex exponential. -/
noncomputable def paramSquareCircleEquiv : (AddCircle period × AddCircle period) ≃ₜ
    (Circle × Circle) :=
  paramCircleHomeo.prodCongr paramCircleHomeo

/-- Under `paramSquareCircleEquiv` the swap relation is transported: two
parameter pairs are swap-equivalent iff their images are. -/
lemma pairRel_circle_iff (p q : AddCircle period × AddCircle period) :
    pairRel p q ↔ circleSwapRel (paramSquareCircleEquiv p) (paramSquareCircleEquiv q) := by
  constructor
  · intro h
    rcases h with h | h
    · left
      exact congrArg paramSquareCircleEquiv h
    · right
      have hq : paramSquareCircleEquiv (pairFlip p) = paramSquareCircleEquiv q := by
        exact congrArg paramSquareCircleEquiv h
      rw [← hq]
      simp [circleSwap, pairFlip, paramSquareCircleEquiv]
  · intro h
    rcases h with h | h
    · left
      exact paramSquareCircleEquiv.injective h
    · right
      have he : paramSquareCircleEquiv (pairFlip p) = paramSquareCircleEquiv q := by
        simpa [circleSwap, pairFlip, paramSquareCircleEquiv] using h
      exact paramSquareCircleEquiv.injective he

/-- The quotient of the parameter square by the swap is homeomorphic to the
quotient of the circle square by the swap. -/
noncomputable def unordParamCircleEquiv : UnordCirclePairs ≃ₜ CircleUnordPairs :=
  Homeomorph.Quotient.congr (rX := pairSetoid) (rY := circleSwapSetoid)
    paramSquareCircleEquiv pairRel_circle_iff

/-- The diagonal class of a parameter is carried to the diagonal class of its
circle image. -/
lemma unordParamCircleEquiv_diag (a : AddCircle period) :
    unordParamCircleEquiv (diagClass a) = circleDiagClass (paramCircleHomeo a) := by
  rfl

/-- A class of the parameter quotient is a diagonal class iff its image under
the circle homeomorphism is. -/
lemma openDiag_iff (c : UnordCirclePairs) :
    (∃ a : AddCircle period, c = diagClass a) ↔
      ∃ a' : Circle, unordParamCircleEquiv c = circleDiagClass a' := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨paramCircleHomeo a, unordParamCircleEquiv_diag a⟩
  · rintro ⟨a', h⟩
    refine ⟨paramCircleHomeo.symm a', ?_⟩
    apply unordParamCircleEquiv.injective
    calc
      unordParamCircleEquiv c = circleDiagClass a' := h
      _ = circleDiagClass (paramCircleHomeo (paramCircleHomeo.symm a')) := by simp
      _ = unordParamCircleEquiv (diagClass (paramCircleHomeo.symm a')) := by
        exact (unordParamCircleEquiv_diag (paramCircleHomeo.symm a')).symm

/-- The backward transport: a class of the circle quotient is a diagonal
class iff its preimage under the parameter homeomorphism is. -/
lemma openDiag_iff' (d : CircleUnordPairs) :
    (∃ a : AddCircle period, unordParamCircleEquiv.symm d = diagClass a) ↔
      ∃ a' : Circle, d = circleDiagClass a' := by
  constructor
  · rintro ⟨a, h⟩
    refine ⟨paramCircleHomeo a, ?_⟩
    have he : unordParamCircleEquiv (unordParamCircleEquiv.symm d) =
        unordParamCircleEquiv (diagClass a) := by
      rw [h]
    exact (by
      have hd : d = circleDiagClass (paramCircleHomeo a) := by
        rw [← unordParamCircleEquiv_diag a]
        simpa using he
      exact hd)
  · rintro ⟨a', h⟩
    refine ⟨paramCircleHomeo.symm a', ?_⟩
    apply unordParamCircleEquiv.injective
    calc
      unordParamCircleEquiv (unordParamCircleEquiv.symm d) = d := by simp
      _ = circleDiagClass a' := h
      _ = circleDiagClass (paramCircleHomeo (paramCircleHomeo.symm a')) := by simp
      _ = unordParamCircleEquiv (diagClass (paramCircleHomeo.symm a')) := by
        exact (unordParamCircleEquiv_diag (paramCircleHomeo.symm a')).symm

/-- The homeomorphism between the two open Möbius bands: the parameter secant
space and the circle-pair model. -/
noncomputable def openMobiusCircleEquiv : OpenMobius ≃ₜ CircleOpenPairs where
  toEquiv := (Equiv.subtypeEquiv unordParamCircleEquiv.toEquiv (fun c =>
    Iff.not (openDiag_iff c)))
  continuous_toFun := by
    exact Continuous.subtype_mk (f := fun c : OpenMobius =>
      unordParamCircleEquiv (c.1 : UnordCirclePairs))
      (p := fun d : CircleUnordPairs => ¬ ∃ a : Circle, d = circleDiagClass a)
      (unordParamCircleEquiv.continuous.comp continuous_subtype_val)
      (by intro c; exact (Iff.not (openDiag_iff c.1)).1 c.2)
  continuous_invFun := by
    exact Continuous.subtype_mk (f := fun d : CircleOpenPairs =>
      unordParamCircleEquiv.symm (d.1 : CircleUnordPairs))
      (p := fun c : UnordCirclePairs => ¬ ∃ a : AddCircle period, c = diagClass a)
      (unordParamCircleEquiv.symm.continuous.comp continuous_subtype_val)
      (by intro d; exact (Iff.not (openDiag_iff' d.1)).mpr d.2)

end LeanEval.KnotTheory.Quadrisecant
