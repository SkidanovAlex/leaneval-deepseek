import Mathlib
import Submission.Work.MotAS.SdualAS2Defs
import Submission.Work.MotAS.KleinTwProjAS

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS

/-! ## Naturality of the ruling data of the corrected AS chart under a ring homomorphism

Every ingredient of `asRuleQW` (`asRuleQA`, `asRuleQB`, `asPolarP`, `asTanQ`, `kleinBilinAS`,
`kleinQAS`, `kleinPAS`, `kleinE`, `Pi.single`) is a polynomial expression with integer coefficients
in `a, b, g` and the coordinates, so it commutes with every ring homomorphism.  We prove the
naturality componentwise, following the T-twisted analogue
(`Work.MotK.kleinTwTan_map` / `kleinTwRuleA_map`, `MotK/KleinTwRulingQuinticMem.lean`), and then
assemble the target. -/

/-- The standard basis vectors `kleinE k = Pi.single k 1` are fixed by every ring homomorphism. -/
theorem map_kleinE_apply {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (k i : Fin 5) :
    φ (Work.MotK.kleinE (R := R) k i) = Work.MotK.kleinE (R := S) k i := by
  simp only [Work.MotK.kleinE, Pi.single_apply]
  split <;> simp

/-- The standard basis vectors are fixed by every ring homomorphism, as functions. -/
theorem map_kleinE_fn {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (k : Fin 5) :
    (fun i => φ (Work.MotK.kleinE (R := R) k i)) = Work.MotK.kleinE (R := S) k := by
  funext i
  exact map_kleinE_apply φ k i

/-- Naturality of the AS invariant quadric `kleinQAS`. -/
theorem map_kleinQAS_nat {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R)
    (u : Fin 5 → R) :
    φ (kleinQAS a b u) = kleinQAS (φ a) (φ b) (fun i => φ (u i)) := by
  simp only [kleinQAS, map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_one,
    map_zero, map_neg]

/-- Naturality of the polar form `kleinBilinAS` of `kleinQAS`. -/
theorem map_kleinBilinAS_nat {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R)
    (u v : Fin 5 → R) :
    φ (kleinBilinAS a b u v)
      = kleinBilinAS (φ a) (φ b) (fun i => φ (u i)) (fun i => φ (v i)) := by
  have h1 : (fun i => φ ((u + v) i)) = (fun i => φ (u i)) + (fun i => φ (v i)) := by
    funext i; simp only [Pi.add_apply, map_add]
  simp only [kleinBilinAS, map_sub]
  rw [map_kleinQAS_nat, map_kleinQAS_nat, map_kleinQAS_nat, h1]

/-- Naturality of the tangent vectors `asTanQ` of the AS quadric `kleinQAS`. -/
theorem map_asTanQ {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R)
    (c : Fin 5 → R) (k : Fin 5) :
    (fun i => φ (asTanQ a b c k i)) = asTanQ (φ a) (φ b) (fun i => φ (c i)) k := by
  funext i
  simp only [asTanQ, map_sub, map_mul, map_kleinBilinAS_nat, map_kleinE_apply]

/-- Pointwise naturality of the AS Pfaffian tuple `kleinPAS` (from `map_kleinPAS`). -/
theorem map_kleinPAS_apply {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b g : R)
    (y : Fin 5 → R) (k : Fin 5) :
    φ (kleinPAS a b g y k) = kleinPAS (φ a) (φ b) (φ g) (fun i => φ (y i)) k :=
  (congrFun (map_kleinPAS φ a b g y) k).symm

/-- Naturality of the polarisation `asPolarP` of the AS Pfaffian map `kleinPAS`. -/
theorem map_asPolarP {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b g : R)
    (x y : Fin 5 → R) (k : Fin 5) :
    φ (asPolarP a b g x y k)
      = asPolarP (φ a) (φ b) (φ g) (fun i => φ (x i)) (fun i => φ (y i)) k := by
  have h1 : (fun i => φ ((x + y) i)) = (fun i => φ (x i)) + (fun i => φ (y i)) := by
    funext i; simp only [Pi.add_apply, map_add]
  simp only [asPolarP]
  rw [map_sub, map_sub, map_kleinPAS_apply, h1, map_kleinPAS_apply, map_kleinPAS_apply]

/-- Naturality of the first ruling vector `asRuleQA`. -/
theorem map_asRuleQA {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b g : R)
    (c : Fin 5 → R) (i : Fin 5) :
    φ (asRuleQA a b g c i) = asRuleQA (φ a) (φ b) (φ g) (fun i => φ (c i)) i := by
  simp only [asRuleQA]
  rw [map_asPolarP, map_asTanQ]

/-- Naturality of the second ruling vector `asRuleQB`. -/
theorem map_asRuleQB {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b g : R)
    (c : Fin 5 → R) (i : Fin 5) :
    φ (asRuleQB a b g c i) = asRuleQB (φ a) (φ b) (φ g) (fun i => φ (c i)) i := by
  simp only [asRuleQB]
  rw [map_asPolarP, map_asTanQ]

/-- **Naturality of the ruling parametrisation `asRuleQW`.**  `asRuleQW a b g c t` is the point
`A(c) + t·B(c)` of the ruling line of the corrected AS chart (see
`Submission/Work/MotAS/SdualAS2Defs.lean`), where `A(c) = dP^AS_c(asTanQ(·,1))` and
`B(c) = dP^AS_c(asTanQ(·,2))` are the polars of the five AS Pfaffians `kleinPAS` in the directions
`asTanQ a b c k` (the tangent vectors of the AS quadric `kleinQAS = -kleinPAS4` at `c`, based at
`kleinE 4`).  All of the data are polynomial expressions in `a, b, g` and the coordinates `c, t`,
so any ring homomorphism `φ` commutes with them.  This is the analogue of
`Work.MotAS.map_kleinPAS` / `map_kleinRAS` (`Submission/Work/MotAS/KleinTwProjAS.lean`, both
proved).

Route.  Unfold `asRuleQW`, `asRuleQA`, `asRuleQB` (`SdualAS2Defs.lean`), then `asPolarP`
(`ASRulDefs.lean`), `asTanQ` (`SdualAS2Defs.lean`), `kleinBilinAS` (`ASLink.lean`), `kleinQAS` and
`kleinPAS` (`ASData.lean`), using `Matrix.cons_val_*` for the `![...]` tuples and
`Work.MotK.kleinE k = Pi.single k 1`, and close with `simp only [map_add, map_sub, map_mul, map_pow,
map_ofNat, map_natCast, map_one, map_zero, map_neg]`.  Naturality of `kleinPAS` itself is available
as `Work.MotAS.map_kleinPAS`, so `asPolarP` naturality can also be derived from it. -/
theorem map_asRuleQW {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (c : Fin 5 → R) (t : R) :
    Work.MotAS.asRuleQW (φ a) (φ b) (φ g) (fun i => φ (c i)) (φ t)
      = fun i => φ (Work.MotAS.asRuleQW a b g c t i) := by
  funext i
  simp only [asRuleQW, map_add, map_mul, map_asRuleQA, map_asRuleQB]

end Work.MotAS
