import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.Hilbert90IsAlgClosure
import Submission.Work.SSGRoute.ext_continuous_descent_fg
import Submission.Work.SSGRoute.localKummerReciprocity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **The continuous descent, in the regime of the application.**

`L` of characteristic `0`, `M` an algebraic closure of `L` (so `Mˣ` is divisible, `M` is Galois over
every intermediate field, and `Gal(M/L)` carries Mathlib's canonical Krull topology), `K ⊆ M` a
finite Galois intermediate field, and `X` a **finite** `𝔽_p[Gal(K/L)]`-module (in E7a,
`X = E' = DualMod p (E ⊗ T)`, which is finite and killed by `p`).  Then

  `Ext¹_{ℤ[Q]}(X, Kˣ) ≅ H¹_cont(G, Hom_ℤ(infl X, Mˣ))`,  `Q = Gal(K/L)`, `G = Gal(M/L)`,

where `H¹_cont` is the workspace's continuous cohomology `Work.AbsoluteKummer.H1` (locally constant
crossed homomorphisms modulo coboundaries) and the coefficient type
`(infl X).V →ₗ[ULift ℤ] Mˣ` carries the conjugation action `(g·f)(x) = g · f (g⁻¹ · x)` (written
*unfolded* so that `homRep`'s `DistribMulAction`/`SMulCommClass` instances are found).

**`X` must be finite and `p`-torsion — this is not cosmetic.**  The arbitrary-`X` version is FALSE:
with `L = ℚ`, `M = ℚ̄`, `K = ⊥`, `X = ℚ` trivial, the left side is `Ext¹_ℤ(ℚ,ℚˣ) ≠ 0` (free
presentation `0 → ⊕ℤ --φ--> ⊕ℤ → ℚ → 0`, `φ(e_n) = e_n − (n+1)e_{n+1}`) while the right side vanishes
(`Hom_ℤ(ℚ,ℚ̄ˣ) = lim_n(ℚ̄ˣ ←·(n+1)← ℚ̄ˣ)`, and the locally constant crossed homs vanishing on
`Gal(ℚ̄/E)` form `lim_n(Eˣ/ℚˣ, [y] ↦ [y^{n+1}]) = 0` for finite `E/ℚ`).  With `X` finite and killed by
`p`, `Hom_ℤ(X, Mˣ) = Hom_{𝔽_p}(X, μ_p)` and the `K = L` case is
`Ext¹_ℤ(X,Lˣ) = (Lˣ/(Lˣ)^p)^{dim X}` versus `H¹_cont(G, μ_p)^{dim X} = (Lˣ/(Lˣ)^p)^{dim X}` by continuous
Kummer (a reviewer hand-checked `L = ℚ₃, K = ℚ₃(ζ₃), p = 3, X =` the twist: both `ℚ₃ˣ/(ℚ₃ˣ)³`).

**Ingredients** (all on disk): `(Mˣ)^H = Kˣ` (`InfiniteGalois.fixedField_fixingSubgroup`);
`H¹_cont(H, Mˣ) = 0` (Hilbert 90 for the algebraic closure `M` of `K`,
`PT/Hilbert90IsAlgClosure.hilbert90_H1_eq_zero_of_isAlgClosure`); vanishing of `H¹_cont` for the
`Map(G,Mˣ)`-type modules arising from a free presentation of `X` over `ℤ[Q]` (Shapiro/coind,
`ext_h1_bridge.lean`'s `CoindU`/`h1Transfer`); the inflation/restriction sequences of
`Work.AbsoluteKummer.Inflation`/`.SES`; and continuous Kummer
`Work.SSGRoute.kummer_reciprocity_general` (`Submission/Work/SSGRoute/local_kummer_reciprocity.lean`).
Note the naive dictionary `Ext¹_Q(X,Kˣ) ≅ H¹(Q,Hom(X,Kˣ))` is unavailable (`Kˣ` is not divisible), so
the proof must go through `p`-Kummer + Hochschild–Serre. -/
theorem ext_continuous_descent {L M : Type} [Field L] [CharZero L] [Field M] [Algebra L M]
    [IsAlgClosure L M] (K : IntermediateField L M) [FiniteDimensional L K] [IsGalois L K]
    (p : ℕ) [Fact p.Prime] (X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[L] K)) [Finite X]
    (hX : ∀ x : X.V, p • x = 0) :
    Nonempty (CategoryTheory.Abelian.Ext X
        (SSGRoute.PTExt.modRep (K ≃ₐ[L] K) (Additive (Units ↥K))) 1 ≃+
      Work.AbsoluteKummer.H1 (M ≃ₐ[L] M)
        ((Rep.res (AlgEquiv.restrictNormalHom (F := L) (K₁ := M) ↥K) X).V →ₗ[SSGRoute.PTExt.Coeff]
          (SSGRoute.PTExt.modRep (M ≃ₐ[L] M) (Additive (Units M))).V)) := by
  -- `X` finite means `X.V` finite, hence finitely generated over `ℤ`, hence over
  -- `Coeff = ULift ℤ`; this is exactly the hypothesis of the already-proved finitely generated
  -- form of the descent, whose two coefficient spellings are definitionally the ones above.
  haveI : Module.Finite (ULift.{0} ℤ) X.V := inferInstance
  exact ext_continuous_descent_fg (L := L) (M := M) K X

end Work.SSGRoute
