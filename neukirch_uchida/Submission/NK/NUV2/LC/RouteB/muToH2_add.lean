import Mathlib
import Submission.NK.NUV2.ABHN.muColimEquivH2ProfiniteOfIsPrimitiveRoot
import Submission.NK.NUV2.LC.h2ProfiniteAddGroup
import Submission.NK.NUV2.ABHN.LocalBrauerAux
import Submission.NK.HassePrinciple.MuColimAdd

/-!
# Additivity of the colimit comparison `MuColim p ⊤ → H2Profinite p ⊤`

`NK.NUV2.ABHN.muToH2 p hζ : MuColim p ⊤ → H2Profinite p ⊤` compares the `μ_p`-colimit with the
trivial-coefficient profinite cohomology when `K` contains a primitive `p`-th root of unity `ζ`
(`Submission/Work/NUV2/ABHN/muColimEquivH2ProfiniteOfIsPrimitiveRoot.lean`).  It is built by the
universal property `NK.BrauerTwist.LevelSystem.lift` out of the level-wise comparisons
`levelCompareRoot p hζ ⊤ L : MuLevelH2 p ⊤ L ≃ H²(LevelGroup ⊤ L, Z/p)`.

Both sides carry an additive structure (the chosen `AddCommGroup` instances of the two colimits,
`NK.NUV2.ABHN.instAddCommGroupMuColim` and
`NK.NUV2.LC.instAddCommGroupH2Profinite`), and this file proves that `muToH2` is **additive**.

The reduction is the same one used for the Kummer map
(`NK.NUV2.LC.RouteB.kummerColim_add`): every class of a colimit is represented at a finite level,
and the structure maps of both colimits are additive
(`NK.NUV2.ABHN.MuColim.ofLevel_add`, `NK.BrauerHasse.H2Profinite.ofLevel_add`), so it suffices
to know that the *levelwise* comparison is additive.  That last point is the only non-formal
ingredient: `levelCompareRoot` is built from `NK.IndecomposedDeep.H2congr`, whose definition goes
through the explicit description of `H²` by 2-cocycles and the (arbitrary) choice
`Function.surjInv`; additivity is proved here by transporting the cocycle equation
(`H2congr_add`).

## Main results

* `muToH2_add` — the requested additivity of `NK.NUV2.ABHN.muToH2`.
-/

open CategoryTheory Representation

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace NK.NUV2.LC.RouteB

/-! ## Additivity of the level-wise comparison -/

section Generic

variable {k k' : Type u} [CommRing k] [CommRing k'] {G : Type u} [Group G]

/-- **The transport of 2-cocycles along an equivariant additive equivalence of coefficients is
additive.**  `NK.IndecomposedDeep.eCocycle e he` acts on a cocycle by the *pointwise* application
of `e`, and `e` is additive, so it is additive on the (pointwise) group `↥(cocycles₂ A)`. -/
private lemma eCocycle_add {A : Rep k G} {B : Rep k' G} (e : A.V ≃+ B.V)
    (he : ∀ (g : G) (y : A.V), e (A.ρ g y) = B.ρ g (e y))
    (x y : ↥(groupCohomology.cocycles₂ A)) :
    NK.IndecomposedDeep.eCocycle e he (x + y) =
      NK.IndecomposedDeep.eCocycle e he x + NK.IndecomposedDeep.eCocycle e he y := by
  apply Subtype.ext
  funext i
  show e ((x : G × G → A.V) i + (y : G × G → A.V) i) = _
  rw [map_add]
  rfl

/-- **The level comparison `NK.IndecomposedDeep.H2congr` is additive.**

`H2congr e he` is defined on the class of a cocycle `x` by transporting `x` along `e` and taking
the class again (`H2congr_H2π`).  Since `H2π` is additive, `eCocycle` is additive
(`eCocycle_add`) and the representatives chosen by `Function.surjInv` are irrelevant, this is
additive. -/
private theorem H2congr_add {A : Rep k G} {B : Rep k' G} (e : A.V ≃+ B.V)
    (he : ∀ (g : G) (y : A.V), e (A.ρ g y) = B.ρ g (e y))
    (x y : groupCohomology.H2 A) :
    NK.IndecomposedDeep.H2congr e he (x + y) =
      NK.IndecomposedDeep.H2congr e he x + NK.IndecomposedDeep.H2congr e he y := by
  obtain ⟨x', rfl⟩ := NK.IndecomposedDeep.H2π_surj A x
  obtain ⟨y', rfl⟩ := NK.IndecomposedDeep.H2π_surj A y
  rw [← map_add (ConcreteCategory.hom (groupCohomology.H2π A)) x' y',
    NK.IndecomposedDeep.H2congr_H2π, NK.IndecomposedDeep.H2congr_H2π,
    NK.IndecomposedDeep.H2congr_H2π,
    ← map_add (ConcreteCategory.hom (groupCohomology.H2π B)) _ _, eCocycle_add]

end Generic

section LevelCompare

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The level-wise comparison `muColimEquivH2ProfiniteOfIsPrimitiveRoot.levelCompareRoot` is
additive** in the `μ_p`-coefficient argument.  It is the `H2congr` attached to the coefficient
identification `muAddEquiv`, so this is `H2congr_add`. -/
private lemma levelCompare_add (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (a b : NK.HassePrinciple.MuLevelH2 p V L) :
    NK.NUV2.ABHN.levelCompareRoot p hζ V L (a + b) =
      NK.NUV2.ABHN.levelCompareRoot p hζ V L a +
        NK.NUV2.ABHN.levelCompareRoot p hζ V L b :=
  H2congr_add (A := NK.NUV2.ABHN.muLevelRepP p V L)
    (B := NK.NUV2.ABHN.trivLevelRep p V L)
    (NK.NUV2.ABHN.muAddEquiv p ζ hζ L)
    (NK.NUV2.ABHN.muAddEquiv_equivariance p hζ V L) a b


/-- The computation rule for `muToH2` on a level class, in the `MuColim.ofLevel`/`MuLevelH2`
vocabulary used by the target statement (the source lemma `NK.NUV2.ABHN.muToH2_ofLevel` is
stated with the definitionally equal `LevelSystem` projections, which the `rw` matcher does not
unfold). -/
private lemma muToH2_ofLevel_mu (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (L : FiniteGaloisIntermediateField K K')
    (a : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p (⊤ : Subgroup Gal(K'/K)) L) :
    NK.NUV2.ABHN.muToH2 (K := K) (K' := K') p hζ
        (NK.HassePrinciple.MuColim.ofLevel (K := K) (K' := K') p ⊤ L a) =
      NK.BrauerHasse.H2Profinite.ofLevel L
        (NK.NUV2.ABHN.levelCompareRoot (K := K) (K' := K') p hζ ⊤ L a) :=
  NK.NUV2.ABHN.muToH2_ofLevel (K := K) (K' := K') p hζ L a

end LevelCompare

/-! ## The requested additivity -/

/-- **`muToH2` is additive.**  Both classes are represented at finite levels, the sum is computed
at the join of the two levels (the structure maps of the colimit are additive), and there the claim
is the additivity of the level comparison together with the additivity of the structure maps of
`H2Profinite`. -/
theorem muToH2_add {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (x y : NK.HassePrinciple.MuColim (K := K) (K' := K') p ⊤) :
    NK.NUV2.ABHN.muToH2 (K := K) (K' := K') p hζ (x + y) =
      NK.NUV2.ABHN.muToH2 (K := K) (K' := K') p hζ x +
      NK.NUV2.ABHN.muToH2 (K := K) (K' := K') p hζ y := by
  obtain ⟨L, a, ha⟩ := NK.BrauerTwist.LevelSystem.ofLevel_surjective
    (S := NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p (⊤ : Subgroup Gal(K'/K))) x
  obtain ⟨L', b, hb⟩ := NK.BrauerTwist.LevelSystem.ofLevel_surjective
    (S := NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p (⊤ : Subgroup Gal(K'/K))) y
  let M : FiniteGaloisIntermediateField K K' := L ⊔ L'
  have hLM : L ≤ M := le_sup_left
  have hL'M : L' ≤ M := le_sup_right
  let A : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p (⊤ : Subgroup Gal(K'/K)) M :=
    (NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p ⊤).map hLM a
  let B : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p (⊤ : Subgroup Gal(K'/K)) M :=
    (NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p ⊤).map hL'M b
  have hxM : x = NK.HassePrinciple.MuColim.ofLevel (K := K) (K' := K') p ⊤ M A :=
    ha.symm.trans (NK.BrauerTwist.LevelSystem.ofLevel_map hLM a).symm
  have hyM : y = NK.HassePrinciple.MuColim.ofLevel (K := K) (K' := K') p ⊤ M B :=
    hb.symm.trans (NK.BrauerTwist.LevelSystem.ofLevel_map hL'M b).symm
  calc NK.NUV2.ABHN.muToH2 (K := K) (K' := K') p hζ (x + y)
      = NK.NUV2.ABHN.muToH2 (K := K) (K' := K') p hζ
          (NK.HassePrinciple.MuColim.ofLevel (K := K) (K' := K') p ⊤ M A +
           NK.HassePrinciple.MuColim.ofLevel (K := K) (K' := K') p ⊤ M B) := by rw [hxM, hyM]
    _ = NK.NUV2.ABHN.muToH2 (K := K) (K' := K') p hζ
          (NK.HassePrinciple.MuColim.ofLevel (K := K) (K' := K') p ⊤ M (A + B)) := by
          rw [NK.NUV2.ABHN.MuColim.ofLevel_add]
    _ = NK.BrauerHasse.H2Profinite.ofLevel M
          (NK.NUV2.ABHN.levelCompareRoot (K := K) (K' := K') p hζ ⊤ M (A + B)) :=
          muToH2_ofLevel_mu (K := K) (K' := K') p hζ M (A + B)
    _ = NK.BrauerHasse.H2Profinite.ofLevel M
          (NK.NUV2.ABHN.levelCompareRoot (K := K) (K' := K') p hζ ⊤ M A +
           NK.NUV2.ABHN.levelCompareRoot (K := K) (K' := K') p hζ ⊤ M B) := by
          rw [levelCompare_add]
    _ = NK.BrauerHasse.H2Profinite.ofLevel M
          (NK.NUV2.ABHN.levelCompareRoot (K := K) (K' := K') p hζ ⊤ M A) +
        NK.BrauerHasse.H2Profinite.ofLevel M
          (NK.NUV2.ABHN.levelCompareRoot (K := K) (K' := K') p hζ ⊤ M B) :=
          NK.BrauerHasse.H2Profinite.ofLevel_add p ⊤ M _ _
    _ = NK.NUV2.ABHN.muToH2 (K := K) (K' := K') p hζ x +
        NK.NUV2.ABHN.muToH2 (K := K) (K' := K') p hζ y := by
          rw [hxM, hyM, muToH2_ofLevel_mu, muToH2_ofLevel_mu]

end NK.NUV2.LC.RouteB
