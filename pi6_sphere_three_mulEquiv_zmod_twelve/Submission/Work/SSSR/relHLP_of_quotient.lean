import Mathlib
import Submission.Work.SSSR.HornDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

/-- **Relative homotopy lifting property descends along a quotient map.**
If `Φ : X → Y` is a quotient map identifying points of `A = Φ ⁻¹' C` (and off `A` it is
injective, in the weak sense that a point identified with a *different* point lies in `A`),
and `p` has the relative homotopy lifting property for `(X, A)`, then `p` has it for `(Y, C)`.

The proof pulls a lifting problem on `Y` back along `Φ`, lifts on `X`, and observes that the
resulting lift is constant on the fibres of `Φ` (on a non-trivial fibre both points lie in `A`,
where the lift is prescribed by `u ∘ Φ`), so it descends through the quotient map. -/
theorem relHLP_of_quotient {E B X Y : Type} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace X] [TopologicalSpace Y]
    (p : C(E, B)) (A : Set X) (Cset : Set Y)
    (Φ : C(X, Y)) (hquo : Topology.IsQuotientMap Φ)
    (hAC : ∀ x : X, Φ x ∈ Cset ↔ x ∈ A)
    (hfiber : ∀ x x' : X, Φ x = Φ x' → x ≠ x' → x ∈ A)
    (h : Work.SSSR.RelHLP p X A) : Work.SSSR.RelHLP p Y Cset := by
  intro v u huv
  -- `Φ ⁻¹' Cset = A`
  have hmemA : ∀ x : X, x ∈ A → Φ x ∈ Cset := fun x hx => (hAC x).mpr hx
  -- the prescribed lift on `A`, pulled back from `u` along `Φ`
  let u' : C(↥A, E) :=
    u.comp ⟨fun x : ↥A => ⟨Φ x.1, hmemA x.1 x.2⟩,
      Continuous.subtype_mk (Φ.continuous.comp continuous_subtype_val) _⟩
  have hu'_apply : ∀ (x : X) (hx : x ∈ A), u' ⟨x, hx⟩ = u ⟨Φ x, hmemA x hx⟩ :=
    fun x hx => rfl
  have huv' : p.comp u' = (v.comp Φ).comp ⟨Subtype.val, continuous_subtype_val⟩ := by
    ext x
    have := congrArg (fun f : C(↥Cset, B) => f ⟨Φ x.1, hmemA x.1 x.2⟩) huv
    simpa [u'] using this
  -- lift on `X`
  obtain ⟨F, hF, hFA⟩ := h (v.comp Φ) u' huv'
  have hF_apply : ∀ x : X, p (F x) = v (Φ x) := by
    intro x
    have := congrArg (fun f : C(X, B) => f x) hF
    simpa using this
  have hFA_apply : ∀ (x : X) (hx : x ∈ A), F x = u' ⟨x, hx⟩ := by
    intro x hx
    have := congrArg (fun f : C(↥A, E) => f ⟨x, hx⟩) hFA
    simpa using this
  -- `F` is constant on the fibres of `Φ`
  have hconst : Function.FactorsThrough F Φ := by
    intro x x' heq
    by_cases hxx : x = x'
    · subst hxx; rfl
    · have hxA : x ∈ A := hfiber x x' heq hxx
      have hx'A : x' ∈ A := hfiber x' x heq.symm (fun hc => hxx hc.symm)
      rw [hFA_apply x hxA, hFA_apply x' hx'A, hu'_apply x hxA, hu'_apply x' hx'A]
      congr 1
      exact Subtype.ext heq
  -- descend through the quotient map
  let Fbar : C(Y, E) := hquo.lift F hconst
  have hcomp : Fbar.comp Φ = F := hquo.lift_comp F hconst
  have hFbar_apply : ∀ x : X, Fbar (Φ x) = F x := by
    intro x
    have := congrArg (fun f : C(X, E) => f x) hcomp
    simpa using this
  refine ⟨Fbar, ?_, ?_⟩
  · ext y
    obtain ⟨x, rfl⟩ := hquo.surjective y
    simp only [ContinuousMap.comp_apply]
    rw [hFbar_apply x, hF_apply x]
  · ext y
    obtain ⟨x, hx⟩ := hquo.surjective (y : Y)
    have hxA : x ∈ A := (hAC x).mp (by rw [hx]; exact y.2)
    have hydesc : Fbar (y : Y) = u y := by
      rw [← hx, hFbar_apply x, hFA_apply x hxA, hu'_apply x hxA]
      congr 1
      exact Subtype.ext hx
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk] using hydesc

end Work.SSSR
