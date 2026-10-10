import Mathlib
import Submission.Work.MotK.TwRuling.TwSixAssemblyDefs
import Submission.Work.MotK.TGen.SdualTBrick
import Submission.Work.MotK.TwRuling.sdW_ne_zero_of_coeff
import Submission.Work.MotK.KleinTwRMap

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

namespace Work.MotK.TwRuling

/-!
# `rpEval K D h = 0` from the vanishing of `kleinTwR0 … (sdW K D h)`

The target ruling polynomial `rpEval K D h ∈ (OmG K D)[T]` is the polynomial
`R₀(A(κ) + T·B(κ))` computed with the twisted Klein coordinates `κ = twCoordG K D h` over the
function field `OmG K D`, whereas `sdW K D h` is the *same* expression computed inside the target
ruling field `sdA K D h = RatFunc ↥(twistFieldTG K D h)`, the function field of the target ruling
divisor `{sdualT = 0}` over the twisted Klein curve.

The two are related by the ring homomorphism `Φ : sdA K D h →+* RatFunc (OmG K D)` induced by the
inclusion `↥(twistFieldTG K D h) ↪ OmG K D` of the intermediate field of twisted Klein coordinates
into the whole function field.  `Φ` is obtained from `IsFractionRing.lift`, and the whole
divisor-free construction `kleinTwRuleA`, `kleinTwRuleB`, `kleinTwR0` is natural for ring
homomorphisms, so

`Φ (kleinTwR0 a b h (sdW K D h)) = algebraMap (Polynomial (OmG K D)) (RatFunc (OmG K D)) (rpEval K D h)`.

Since `algebraMap (Polynomial L) (RatFunc L)` is injective and `Φ 0 = 0`, the vanishing hypothesis
`hzero : kleinTwR0 a b h (sdW K D h) = 0` yields `rpEval K D h = 0`.

The naturality computation is the same one carried out inline in `sdW_ne_zero_of_coeff` (there the
direction used is the reverse one); it is reproduced here because that file exposes no standalone
naturality lemma.
-/

theorem rpEval_eq_zero_of_sdW {K : Type} [Field K] (D : Work.MotV.KleinData K) (h : K)
    (hzero : Work.MotK.kleinTwR0 (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
      (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
      (algebraMap K (Work.MotK.TGen.sdA K D h) h) (Work.MotK.TGen.sdW K D h) = 0) :
    Work.MotK.TwRuling.rpEval K D h = 0 := by
  -- Setup: the intermediate field `F = twistFieldTG K D h`, the ambient field `L = OmG K D`,
  -- and the ring hom `Φ : RatFunc ↥F →+* RatFunc L` induced by the inclusion `↥F ↪ L`.
  let F : IntermediateField K (Work.MotK.OmG K D) := Work.MotK.twistFieldTG K D h
  let L : Type := Work.MotK.OmG K D
  let f : ↥F →+* L := algebraMap ↥F L
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext hxy
  let φp : Polynomial ↥F →+* Polynomial L := Polynomial.mapRingHom f
  have hφpinj : Function.Injective φp := Polynomial.map_injective f hf
  let φp' : Polynomial ↥F →+* RatFunc L := (algebraMap (Polynomial L) (RatFunc L)).comp φp
  have hAinj : Function.Injective (algebraMap (Polynomial L) (RatFunc L)) := by
    intro x y hxy
    by_contra hne
    exact RatFunc.algebraMap_ne_zero (sub_ne_zero.mpr hne) (by rw [map_sub, hxy, sub_self])
  have hinj : Function.Injective φp' := by
    intro x y hxy
    exact hφpinj (hAinj hxy)
  let Φ : RatFunc ↥F →+* RatFunc L := IsFractionRing.lift (g := φp') hinj
  -- `Φ` on the image of the polynomial ring.
  have hΦalg : ∀ p : Polynomial ↥F, Φ (algebraMap (Polynomial ↥F) (RatFunc ↥F) p)
      = algebraMap (Polynomial L) (RatFunc L) (φp p) := by
    intro p
    exact IsFractionRing.lift_algebraMap (g := φp') hinj p
  -- `algebraMap ↥F (RatFunc ↥F)` is `algebraMap (Polynomial ↥F) (RatFunc ↥F) ∘ Polynomial.C`.
  have hcoeC : ∀ x : ↥F, algebraMap ↥F (RatFunc ↥F) x
      = algebraMap (Polynomial ↥F) (RatFunc ↥F) (Polynomial.C x) := by
    intro x
    rw [RatFunc.algebraMap_eq_C (K := ↥F)]
    exact (RingHom.congr_fun (RatFunc.algebraMap_comp_C (K := ↥F)) x).symm
  -- The corresponding statement over `L`.
  have hCσ : ∀ y : L, algebraMap (Polynomial L) (RatFunc L) (Polynomial.C y)
      = algebraMap L (RatFunc L) y := by
    intro y
    rw [RatFunc.algebraMap_eq_C (K := L)]
    exact RingHom.congr_fun (RatFunc.algebraMap_comp_C (K := L)) y
  -- `Φ` on constants.
  have hΦC : ∀ x : ↥F, Φ (algebraMap ↥F (RatFunc ↥F) x) = algebraMap L (RatFunc L) (f x) := by
    intro x
    have hCx : φp (Polynomial.C x) = Polynomial.C (f x) := by
      show Polynomial.map f (Polynomial.C x) = Polynomial.C (f x)
      rw [Polynomial.map_C]
    rw [hcoeC x, hΦalg (Polynomial.C x), hCx]
    exact hCσ (f x)
  -- `Φ` fixes `RatFunc.X`.
  have hΦX : Φ RatFunc.X = RatFunc.X := by
    conv_lhs => rw [← RatFunc.algebraMap_X (K := ↥F)]
    rw [hΦalg Polynomial.X,
      show φp (Polynomial.X) = (Polynomial.X : Polynomial L) from Polynomial.map_X (f := f)]
    exact RatFunc.algebraMap_X (K := L)
  -- `Φ` on the base field `K`.
  have hA : ∀ c : K, algebraMap K (RatFunc ↥F) c
      = algebraMap ↥F (RatFunc ↥F) (algebraMap K ↥F c) := by
    intro c
    rw [RatFunc.algebraMap_apply (K := ↥F) (R := K) c,
      RatFunc.algebraMap_apply (K := ↥F) (R := ↥F) (algebraMap K ↥F c)]
    have hAB : algebraMap (Polynomial ↥F) (RatFunc ↥F) (algebraMap K (Polynomial ↥F) c)
        = algebraMap (Polynomial ↥F) (RatFunc ↥F)
            (algebraMap ↥F (Polynomial ↥F) (algebraMap K ↥F c)) := by
      rw [Polynomial.algebraMap_apply, ← Polynomial.C_eq_algebraMap]
    rw [hAB]
  have hΦK : ∀ c : K, Φ (algebraMap K (RatFunc ↥F) c) = algebraMap K (RatFunc L) c := by
    intro c
    rw [hA c, hΦC (algebraMap K ↥F c),
      show f (algebraMap K ↥F c) = algebraMap K L c from rfl]
    exact (IsScalarTower.algebraMap_apply K L (RatFunc L) c).symm
  -- `Φ` on the twisted Klein coordinates.
  have hΦsdY : ∀ i : Fin 5, Φ (Work.MotK.TGen.sdY K D h i)
      = algebraMap L (RatFunc L) (Work.MotK.twCoordG K D h i) := by
    intro i
    rw [show Work.MotK.TGen.sdY K D h i
        = algebraMap ↥F (RatFunc ↥F) ⟨Work.MotK.twCoordG K D h i,
            IntermediateField.subset_adjoin K (Set.range (Work.MotK.twCoordG K D h))
              (Set.mem_range_self i)⟩ from rfl]
    rw [hΦC]
    rfl
  -- The ruling vectors evaluated at the twisted Klein coordinates over `L`.
  let A : Fin 5 → L := fun i => Work.MotK.kleinTwRuleA (algebraMap K L D.a)
    (algebraMap K L D.b) (algebraMap K L h) (Work.MotK.twCoordG K D h) i
  let B : Fin 5 → L := fun i => Work.MotK.kleinTwRuleB (algebraMap K L D.a)
    (algebraMap K L D.b) (algebraMap K L h) (Work.MotK.twCoordG K D h) i
  let u : Fin 5 → Polynomial L := fun k => Polynomial.C (A k) + Polynomial.X * Polynomial.C (B k)
  have hψu : ∀ k : Fin 5, algebraMap (Polynomial L) (RatFunc L) (u k)
      = algebraMap L (RatFunc L) (A k) + RatFunc.X * algebraMap L (RatFunc L) (B k) := by
    intro k
    rw [show u k = Polynomial.C (A k) + Polynomial.X * Polynomial.C (B k) from rfl]
    rw [map_add, map_mul, hCσ (A k), hCσ (B k), RatFunc.algebraMap_X]
  -- `Φ (sdW i) = C'(A i) + X · C'(B i)`.
  have hΦW : ∀ i : Fin 5, Φ (Work.MotK.TGen.sdW K D h i)
      = algebraMap L (RatFunc L) (A i) + RatFunc.X * algebraMap L (RatFunc L) (B i) := by
    intro i
    have hA' : Φ (Work.MotK.TGen.sdRuleA K D h i) = algebraMap L (RatFunc L) (A i) := by
      have h1 : Φ (Work.MotK.TGen.sdRuleA K D h i)
          = Work.MotK.kleinTwRuleA (Φ (algebraMap K (RatFunc ↥F) D.a))
              (Φ (algebraMap K (RatFunc ↥F) D.b)) (Φ (algebraMap K (RatFunc ↥F) h))
              (fun j => Φ (Work.MotK.TGen.sdY K D h j)) i := by
        rw [show Work.MotK.TGen.sdRuleA K D h i
            = Work.MotK.kleinTwRuleA (algebraMap K (RatFunc ↥F) D.a)
                (algebraMap K (RatFunc ↥F) D.b) (algebraMap K (RatFunc ↥F) h)
                (Work.MotK.TGen.sdY K D h) i from rfl]
        exact congrFun (Work.MotK.kleinTwRuleA_map Φ (algebraMap K (RatFunc ↥F) D.a)
          (algebraMap K (RatFunc ↥F) D.b) (algebraMap K (RatFunc ↥F) h)
          (Work.MotK.TGen.sdY K D h)) i
      rw [h1, hΦK D.a, hΦK D.b, hΦK h,
        IsScalarTower.algebraMap_apply K L (RatFunc L) D.a,
        IsScalarTower.algebraMap_apply K L (RatFunc L) D.b,
        IsScalarTower.algebraMap_apply K L (RatFunc L) h, funext hΦsdY]
      rw [← congrFun (Work.MotK.kleinTwRuleA_map (algebraMap L (RatFunc L))
          (algebraMap K L D.a) (algebraMap K L D.b) (algebraMap K L h)
          (Work.MotK.twCoordG K D h)) i]
    have hB' : Φ (Work.MotK.TGen.sdRuleB K D h i) = algebraMap L (RatFunc L) (B i) := by
      have h1 : Φ (Work.MotK.TGen.sdRuleB K D h i)
          = Work.MotK.kleinTwRuleB (Φ (algebraMap K (RatFunc ↥F) D.a))
              (Φ (algebraMap K (RatFunc ↥F) D.b)) (Φ (algebraMap K (RatFunc ↥F) h))
              (fun j => Φ (Work.MotK.TGen.sdY K D h j)) i := by
        rw [show Work.MotK.TGen.sdRuleB K D h i
            = Work.MotK.kleinTwRuleB (algebraMap K (RatFunc ↥F) D.a)
                (algebraMap K (RatFunc ↥F) D.b) (algebraMap K (RatFunc ↥F) h)
                (Work.MotK.TGen.sdY K D h) i from rfl]
        exact congrFun (Work.MotK.kleinTwRuleB_map Φ (algebraMap K (RatFunc ↥F) D.a)
          (algebraMap K (RatFunc ↥F) D.b) (algebraMap K (RatFunc ↥F) h)
          (Work.MotK.TGen.sdY K D h)) i
      rw [h1, hΦK D.a, hΦK D.b, hΦK h,
        IsScalarTower.algebraMap_apply K L (RatFunc L) D.a,
        IsScalarTower.algebraMap_apply K L (RatFunc L) D.b,
        IsScalarTower.algebraMap_apply K L (RatFunc L) h, funext hΦsdY]
      rw [← congrFun (Work.MotK.kleinTwRuleB_map (algebraMap L (RatFunc L))
          (algebraMap K L D.a) (algebraMap K L D.b) (algebraMap K L h)
          (Work.MotK.twCoordG K D h)) i]
    rw [show Work.MotK.TGen.sdW K D h i
        = Work.MotK.TGen.sdRuleA K D h i
          + RatFunc.X * Work.MotK.TGen.sdRuleB K D h i from rfl]
    rw [map_add, map_mul, hΦX, hA', hB']
  -- Left-hand side: `Φ (kleinTwR0 … (sdW))`.
  have hΦ0L : Φ (Work.MotK.kleinTwR0 (algebraMap K (RatFunc ↥F) D.a)
        (algebraMap K (RatFunc ↥F) D.b) (algebraMap K (RatFunc ↥F) h)
        (Work.MotK.TGen.sdW K D h))
      = Work.MotK.kleinTwR0 (algebraMap L (RatFunc L) (algebraMap K L D.a))
          (algebraMap L (RatFunc L) (algebraMap K L D.b))
          (algebraMap L (RatFunc L) (algebraMap K L h))
          (fun i => algebraMap L (RatFunc L) (A i)
            + RatFunc.X * algebraMap L (RatFunc L) (B i)) := by
    rw [kleinTwR0_map Φ (algebraMap K (RatFunc ↥F) D.a) (algebraMap K (RatFunc ↥F) D.b)
      (algebraMap K (RatFunc ↥F) h) (Work.MotK.TGen.sdW K D h)]
    rw [hΦK D.a, hΦK D.b, hΦK h,
      IsScalarTower.algebraMap_apply K L (RatFunc L) D.a,
      IsScalarTower.algebraMap_apply K L (RatFunc L) D.b,
      IsScalarTower.algebraMap_apply K L (RatFunc L) h, funext hΦW]
  -- Right-hand side: the image of `rpEval`.
  have hΦ0R : algebraMap (Polynomial L) (RatFunc L) (Work.MotK.TwRuling.rpEval K D h)
      = Work.MotK.kleinTwR0 (algebraMap L (RatFunc L) (algebraMap K L D.a))
          (algebraMap L (RatFunc L) (algebraMap K L D.b))
          (algebraMap L (RatFunc L) (algebraMap K L h))
          (fun i => algebraMap L (RatFunc L) (A i)
            + RatFunc.X * algebraMap L (RatFunc L) (B i)) := by
    rw [show Work.MotK.TwRuling.rpEval K D h = Work.MotK.kleinTwR0
        (Polynomial.C (algebraMap K L D.a)) (Polynomial.C (algebraMap K L D.b))
        (Polynomial.C (algebraMap K L h)) u from rfl]
    rw [kleinTwR0_map (algebraMap (Polynomial L) (RatFunc L))
        (Polynomial.C (algebraMap K L D.a)) (Polynomial.C (algebraMap K L D.b))
        (Polynomial.C (algebraMap K L h)) u]
    rw [hCσ (algebraMap K L D.a), hCσ (algebraMap K L D.b), hCσ (algebraMap K L h),
      funext hψu]
  have hΦ0 := hΦ0L.trans hΦ0R.symm
  -- `hzero` transported to the local notation.
  have hzero' : Work.MotK.kleinTwR0 (algebraMap K (RatFunc ↥F) D.a)
      (algebraMap K (RatFunc ↥F) D.b) (algebraMap K (RatFunc ↥F) h)
      (Work.MotK.TGen.sdW K D h) = 0 := hzero
  -- Conclusion: the image of `rpEval` is `0`, hence `rpEval = 0` by injectivity.
  have hz : algebraMap (Polynomial L) (RatFunc L) (Work.MotK.TwRuling.rpEval K D h) = 0 := by
    rw [← hΦ0, hzero', map_zero]
  by_contra hne
  exact RatFunc.algebraMap_ne_zero hne hz

end Work.MotK.TwRuling
