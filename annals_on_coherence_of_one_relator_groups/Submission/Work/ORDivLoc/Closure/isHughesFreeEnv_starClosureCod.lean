import Mathlib
import Submission.Work.ORDivLoc.Basic
import Submission.Work.ORDivLoc.Vocabulary
import Submission.Work.ORHughesFree.Section6.HughesFreeEnv
import Submission.Work.ORDivLoc.Closure.starRegularClosure_image_le
import Submission.Work.ORDivLoc.Closure.isHughesFreeEnv_of_ringHom

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORDivLoc.Closure

/-- **The Hughes-freeness hypothesis is inherited by the `∗`-regular closure.**

Let `V = R(K[H], U(G)) = starClosureOfSubgroup E φK H ⊆ U(G)` be the `∗`-regular closure of the
image of `K[H]` in `U(G)`, and let `ρ : ↥V →+* E.U` be the inclusion.  The structure map
`starClosureCod E φK H : K[H] →+* ↥V` is the codomain restriction of `toUK E φK H : K[H] →+* E.U`
along `ρ`, i.e. `(toUK E φK H).toRingHom = ρ.comp (starClosureCod E φK H)`.

Since `IsHughesFreeEnv φ` is stated in terms of the `∗`-regular closures `U_N` of the images of
`K[N] in the *codomain* ring, the transfer rests on the closure comparison

`ρ '' U_N(starClosureCod …) ⊆ U_N(toUK …)`   (`starRegularClosure_image_le`),

i.e. the elements of the `∗`-regular closure computed inside the `∗`-regular subring `V` are also
in the closure computed inside `U(G)`: the `∗`-regular closure of a subring is generated from its
generators by `∗`-subring generation and adjunction of relative inverses, and both operations are
preserved by the injection `ρ` (relative inverses in a `∗`-regular ring being unique, the closures
in fact coincide).  With this comparison in hand, a matrix `A` over the smaller `U_N` can be pushed
forward to the larger one, and `isHughesFreeEnv_of_ringHom` transports the invertibility of
`1 + A·φ(t)` back along the injective map `ρ` of matrix rings (using that `Mat_n(↥V)` is von
Neumann regular, `↥V` being `∗`-regular). -/
theorem isHughesFreeEnv_starClosureCod {K : Type} [Field K] {G : Type} [Group G]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U] (H : Subgroup G)
    (h : Work.ORHughesFree.IsHughesFreeEnv (Work.ORBridgeLinnell.toUK E φK H).toRingHom) :
    Work.ORHughesFree.IsHughesFreeEnv (Work.ORDivLoc.starClosureCod E φK H) := by
  let V : Work.ORHughesFree.StarSubring E.U := Work.ORDivLoc.starClosureOfSubgroup E φK H
  let ρ : ↥V →+* E.U := Subring.subtype V.toSubring
  let φR : MonoidAlgebra K ↥H →+* ↥V := Work.ORDivLoc.starClosureCod E φK H
  let φU : MonoidAlgebra K ↥H →+* E.U := (Work.ORBridgeLinnell.toUK E φK H).toRingHom
  have hρinj : Function.Injective ρ := fun _ _ hab => Subtype.ext hab
  have hcomp : φU = ρ.comp φR := by
    apply RingHom.ext
    intro x
    exact (Work.ORDivLoc.starClosureCod_apply E φK H x).symm
  have hUN : ∀ (H₀ : Subgroup ↥H) (N : Subgroup H₀),
      ∀ z : Work.Section6.UNty φR H₀ N, ρ (z : ↥V) ∈ (Work.Section6.UN φU H₀ N : Set E.U) := by
    intro H₀ N z
    -- `phiN φU = ρ ∘ phiN φR`, since `φU = ρ ∘ φR` and `phiN` is a composite with `φ`.
    have hphiN : Work.Section6.phiN φU H₀ N = ρ.comp (Work.Section6.phiN φR H₀ N) := by
      simp only [Work.Section6.phiN, hcomp, RingHom.comp_assoc]
    -- The generators of the two closures correspond: `ρ '' range (phiN φR) ⊆ range (phiN φU)`.
    have hAB : ρ '' (Set.range (Work.Section6.phiN φR H₀ N)) ⊆
        ((Work.ORHughesFree.starSubringClosure
          (Set.range (Work.Section6.phiN φU H₀ N))) : Set E.U) := by
      rintro y ⟨x, hx, hyx⟩
      rw [← hyx]
      obtain ⟨a, rfl⟩ := hx
      refine Work.ORHughesFree.subset_starSubringClosure _ ⟨a, ?_⟩
      exact congrArg (fun f => f a) hphiN
    -- The closure comparison `starRegularClosure_image_le`, specialised to the two `U_N`.
    have hmain := starRegularClosure_image_le ρ (fun x => rfl)
      (Set.range (Work.Section6.phiN φR H₀ N))
      (Work.ORHughesFree.starSubringClosure (Set.range (Work.Section6.phiN φU H₀ N))) hAB
    exact hmain ⟨z, z.2, rfl⟩
  exact isHughesFreeEnv_of_ringHom ρ hρinj φR φU hcomp hUN h

end Work.ORDivLoc.Closure
