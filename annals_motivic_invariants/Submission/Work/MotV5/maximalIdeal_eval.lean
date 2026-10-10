import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2Cls.Setup

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

/-- Every maximal ideal of the affine coordinate ring `N[X,Y]/(W_E)` of an elliptic curve over an
algebraically closed field is the kernel of an `N`-algebra homomorphism `N[X,Y]/(W_E) → N`, i.e. of
the evaluation at a rational point of the curve.

Route.  Let `π : MvPolynomial (Fin 2) N →ₐ[N] Work.MotC2.Coord E` be
`MvPolynomial.aeval ![Work.MotC2.coordX E, Work.MotC2.coordY E]`; it is surjective because `coordX`,
`coordY` generate `Coord E` (`MvPolynomial.aeval_range` together with
`Work.MotC2.adjoin_coordX_coordY`, plus `Set.range ![a,b] = {a,b}`).  Then `M := m.comap π` is a
maximal ideal of `MvPolynomial (Fin 2) N` (`Ideal.comap_isMaximal_of_surjective`), so by the
Nullstellensatz (`MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal`) there is `x : Fin 2 → N`
with `M = MvPolynomial.vanishingIdeal N {x}`; equivalently `M = RingHom.ker (MvPolynomial.aeval x)`
(`MvPolynomial.mem_vanishingIdeal_iff`, `RingHom.mem_ker`).  Since `ker π ≤ M = ker (aeval x)`, the
map descends along the surjection `π`:
`φ := AlgHom.liftOfSurjective π hπ (MvPolynomial.aeval x) hker : Coord E →ₐ[N] N`, which satisfies
`φ (π a) = aeval x a` (`AlgHom.liftOfSurjective_apply`).  Finally `RingHom.ker φ = m`: every
`z : Coord E` is `π a`, and `φ z = aeval x a = 0 ↔ a ∈ ker (aeval x) = m.comap π ↔ π a = z ∈ m`. -/
theorem maximalIdeal_eval {N : Type*} [Field N] [IsAlgClosed N] (E : WeierstrassCurve N)
    [E.IsElliptic] (m : Ideal (Work.MotC2.Coord E)) (hm : m.IsMaximal) :
    ∃ φ : Work.MotC2.Coord E →ₐ[N] N, RingHom.ker φ = m := by
  -- the evaluation map `N[X,Y] → N[x,y] = Coord E`, `X ↦ x`, `Y ↦ y`
  set π : MvPolynomial (Fin 2) N →ₐ[N] Work.MotC2.Coord E :=
    MvPolynomial.aeval ![Work.MotC2.coordX E, Work.MotC2.coordY E] with hπdef
  -- it is surjective, because `x` and `y` generate `Coord E`
  have hπ : Function.Surjective π := by
    rw [← AlgHom.range_eq_top, hπdef, MvPolynomial.aeval_range, Matrix.range_cons_cons_empty]
    exact Work.MotC2.adjoin_coordX_coordY E
  -- pull back the maximal ideal along the surjection
  have hM : (m.comap π).IsMaximal :=
    @Ideal.comap_isMaximal_of_surjective _ _ _ _ _ _ _ π hπ m hm
  -- Nullstellensatz: `m.comap π` is the vanishing ideal of a point
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal (K := N) hM
  have hxker : RingHom.ker (MvPolynomial.aeval x) = m.comap π := by
    rw [hx]
    ext p
    rw [RingHom.mem_ker, MvPolynomial.mem_vanishingIdeal_singleton_iff]
  -- hence `ker π ≤ ker (aeval x)` and the evaluation descends
  have hker : RingHom.ker π.toRingHom ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    have h0 : π a = 0 := ha
    have ham : a ∈ m.comap π := by
      rw [Ideal.mem_comap, h0]
      exact m.zero_mem
    rw [← hxker, RingHom.mem_ker] at ham
    exact ham
  refine ⟨AlgHom.liftOfSurjective π hπ (MvPolynomial.aeval x) hker, ?_⟩
  have hφ : ∀ a : MvPolynomial (Fin 2) N,
      AlgHom.liftOfSurjective π hπ (MvPolynomial.aeval x) hker (π a) = MvPolynomial.aeval x a :=
    fun a => AlgHom.liftOfSurjective_apply π hπ (MvPolynomial.aeval x) hker a
  refine le_antisymm ?_ ?_
  · -- `ker φ ≤ m`
    intro z hz
    obtain ⟨a, rfl⟩ := hπ z
    rw [RingHom.mem_ker] at hz
    have hza : MvPolynomial.aeval x a = 0 := by rw [← hφ a]; exact hz
    have : a ∈ RingHom.ker (MvPolynomial.aeval x) := by rwa [RingHom.mem_ker]
    rw [hxker, Ideal.mem_comap] at this
    exact this
  · -- `m ≤ ker φ`
    intro z hz
    obtain ⟨a, rfl⟩ := hπ z
    rw [RingHom.mem_ker, hφ a]
    have : a ∈ m.comap π := by rw [Ideal.mem_comap]; exact hz
    rw [← hxker, RingHom.mem_ker] at this
    exact this

end Work.MotV5
