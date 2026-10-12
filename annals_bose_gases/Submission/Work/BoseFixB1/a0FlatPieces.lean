import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1.boxPInd_boxQInd_self
import Submission.Work.BoseFixB1.boxPInd_self_idem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.a0FlatPieces` — the joint `(P,Q)`-flat pieces of the box projections

The **single missing ingredient** of the rung-4 target `Work.BoseFixB1.a0SectorLower`
(= FS `lm:appinteractionestimate` at the sliding box) is the joint spectral decomposition of

    n₀ = Σᵢ Pᵢ ,      Pᵢ = `Work.UBBInputs8.boxPInd V A i`,   Qᵢ = `Work.UBBInputs8.boxQInd V A i`

at the FS-faithful box projections.  Every audit of the route to the target
(`Submission/Work/BoseFixB1/FINDING_boxQSum_cross_is_variance.md` §3–§4 and (G), and
`FINDING_rungXB_le_credit_FALSE.md`) concludes that the surviving proof of the target is FS's
per-eigenvalue completion of squares `final_v2.tex` l.3726–3740, whose formalisation needs the
projections

    Π_S = (∏_{i∈S} Pᵢ) (∏_{i∉S} Qᵢ) ,        S : Finset (Fin N) ,

with `Π_S` self-adjoint idempotent, `Π_S Π_T = δ_{ST} Π_S`, `Σ_S Π_S = 1_{A^N}`, and
`n₀ Π_S = |S| Π_S` — because on the range of `Π_S` the number operator `n₀` is the *number*
`|S|`, which is exactly what turns FS's operator-`√` AM-GM
`2(t−m)ab ≥ −[(√t+√m)²a² + (√t−√m)²b²]` into a *scalar* inequality at each piece
(see the notes: "the `√`-weights are *numbers* `(√k±√(μV))²`").

## The definition

`flatPiece V A S Φ` is the composite `(∏_{i∈S}Pᵢ)(∏_{i∉S}Qᵢ) Φ`.  It is defined by folding over
the list `List.finRange N` (an enumeration of all slots), the two products being interleaved.  The
operators pairwise commute (they act in different slots) and are idempotent with `PᵢQᵢ = 0`, so the
value is independent of the enumeration order; the fold over `List.finRange N` is the
finite-object way of writing the (commuting) product.

The properties are being established in parallel:
`boxPInd_QInd_swap` (the adjoint-swap, requested) and the eigen/orthogonality/completeness
lemmas below (requested).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

local notation "𝔼3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- The one-slot `P`-operator as an endomorphism of the state space. -/
def pEnd {N : ℕ} (V : ℝ) (A : Set 𝔼3) (i : Fin N) : (X N → ℝ) → (X N → ℝ) :=
  fun Ψ => Work.UBBInputs8.boxPInd V A i Ψ

/-- The one-slot `Q`-operator as an endomorphism of the state space. -/
def qEnd {N : ℕ} (V : ℝ) (A : Set 𝔼3) (i : Fin N) : (X N → ℝ) → (X N → ℝ) :=
  fun Ψ => Work.UBBInputs8.boxQInd V A i Ψ

/-- **The joint `(P,Q)`-flat auxiliary**: fold the slot operators of `S` (as `P` when the slot
belongs to `S` and as `Q` otherwise) over a slot list. -/
def flatPieceList {N : ℕ} (V : ℝ) (A : Set 𝔼3) :
    List (Fin N) → Finset (Fin N) → (X N → ℝ) → (X N → ℝ)
  | [], _, Ψ => Ψ
  | i :: l, S, Ψ =>
      (if i ∈ S then Work.UBBInputs8.boxPInd V A i else Work.UBBInputs8.boxQInd V A i)
        (flatPieceList V A l S Ψ)

/-- **The joint `(P,Q)`-flat piece** `Π_SΦ = (∏_{i∈S}Pᵢ)(∏_{i∉S}Qᵢ)Φ` of a state `Φ` at the box
projections of `Work.SmallBoxSliding.dlBox`. -/
def flatPiece {N : ℕ} (V : ℝ) (A : Set 𝔼3) (S : Finset (Fin N)) (Φ : X N → ℝ) : X N → ℝ :=
  flatPieceList V A (List.finRange N) S Φ

@[simp] theorem flatPieceList_nil {N : ℕ} (V : ℝ) (A : Set 𝔼3) (S : Finset (Fin N))
    (Ψ : X N → ℝ) : flatPieceList V A [] S Ψ = Ψ := rfl

@[simp] theorem flatPieceList_cons {N : ℕ} (V : ℝ) (A : Set 𝔼3) (i : Fin N)
    (l : List (Fin N)) (S : Finset (Fin N)) (Ψ : X N → ℝ) :
    flatPieceList V A (i :: l) S Ψ
      = (if i ∈ S then Work.UBBInputs8.boxPInd V A i else Work.UBBInputs8.boxQInd V A i)
          (flatPieceList V A l S Ψ) := rfl

/-! ## 2. The `(P,Q,R)`-refined pieces (complete on the *whole* box, not only on `A^N`)

The two-slot-set refinement is needed because `Σ_SΠ_S = 1_{A^N}` only, while the target's
quantities involve the out-of-`A` slots too: e.g. for `N = 2` and `Φ = ψ(x₁)·η(x₂)` with `η = 0`
on `A` one has `1_{A^N}Φ = 0` **but** `P₁Φ ≠ 0` (`P₁Φ(x) = 1_A(x₁)η(x₂)(1/V)∫_Aψ ≠ 0`).  The
three-slot-set pieces (a set `S` of `P`-slots, a disjoint set `T` of `Q`-slots, and the complement
carrying the *multiplication* `Rᵢ = 1_{xᵢ∉A}`) are complete on the whole box:
`Pᵢ + Qᵢ + Rᵢ = 1`.  Their eigen-properties give `n₀Θ_{S,T} = |S|Θ_{S,T}`,
`n₊Θ_{S,T} = |T|Θ_{S,T}`, `n_RΘ_{S,T} = (N−|S|−|T|)Θ_{S,T}` *everywhere*. -/

/-- The `R`-slot operator: multiplication by the indicator of the complement of `A` in slot `i`. -/
def rInd {N : ℕ} (A : Set 𝔼3) (i : Fin N) (Ψ : X N → ℝ) : X N → ℝ :=
  fun y => Aᶜ.indicator (fun _ => (1 : ℝ)) (y i) * Ψ y

/-- **The `(P,Q,R)`-flat auxiliary**: fold the slot operators over a slot list — `P` on the slots
of `S`, `Q` on the slots of `T`, and the multiplication by `1_{·_i ∉ A}` on the remaining ones. -/
def flatPieceRTList {N : ℕ} (V : ℝ) (A : Set 𝔼3) :
    List (Fin N) → Finset (Fin N) → Finset (Fin N) → (X N → ℝ) → (X N → ℝ)
  | [], _, _, Ψ => Ψ
  | i :: l, S, T, Ψ =>
      (if i ∈ S then Work.UBBInputs8.boxPInd V A i
       else if i ∈ T then Work.UBBInputs8.boxQInd V A i
       else rInd A i)
        (flatPieceRTList V A l S T Ψ)

/-- **The `(P,Q,R)`-refined flat piece** `Θ_{S,T}Φ` of a state `Φ`. -/
def flatPieceRT {N : ℕ} (V : ℝ) (A : Set 𝔼3) (S T : Finset (Fin N)) (Φ : X N → ℝ) :
    X N → ℝ :=
  flatPieceRTList V A (List.finRange N) S T Φ

@[simp] theorem flatPieceRTList_nil {N : ℕ} (V : ℝ) (A : Set 𝔼3) (S T : Finset (Fin N))
    (Ψ : X N → ℝ) : flatPieceRTList V A [] S T Ψ = Ψ := rfl

@[simp] theorem flatPieceRTList_cons {N : ℕ} (V : ℝ) (A : Set 𝔼3) (i : Fin N)
    (l : List (Fin N)) (S T : Finset (Fin N)) (Ψ : X N → ℝ) :
    flatPieceRTList V A (i :: l) S T Ψ
      = (if i ∈ S then Work.UBBInputs8.boxPInd V A i
         else if i ∈ T then Work.UBBInputs8.boxQInd V A i
         else rInd A i) (flatPieceRTList V A l S T Ψ) := rfl

end Work.BoseFixB1
