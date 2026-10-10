import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotK.KleinData
import Submission.Work.MotV5.bridge_as
import Submission.Work.MotV5.asCoord_asTwCoord
import Submission.Work.MotV5.hurwitz_AS_ratFunc
import Submission.Work.Wire123.RatFuncCoeff

set_option linter.unusedVariables false -- v435-speed

/-!
# `constantsOnly_as_base`: the base parameter `t` maps to a constant

Step 1 of node **CO_AS** (`constantsOnly_as`): for good Klein data `D` over a field `𝕜` of
characteristic `5`, an Artin–Schreier class `g ∈ {fAS, 2·fAS}` and a `𝕜`-algebra map
`ι : asTwistField D g →ₐ[𝕜] RatFunc M` into a one-variable rational function field, the image of the
base parameter `t = RatFunc.X` under `ι` is a constant of `M`.

## The argument

Put `F = asTwistField D g`, `K = 𝕜(t)`.  The bridge condition of `bridge_as`
(`ASUnramified 𝕜 F t g`) says that at every valuation of `F` trivial on `𝕜` at which `t` has a pole,
the class `g` is congruent modulo the valuation ring to an Artin–Schreier value `u⁵ - u`.

* Pulling such a valuation back along `ι` gives, for every place of `M(t)` at which `r := ι t` has
  a pole, a witness `u` with `aeval r f - (u⁵ - u)` integral, where `f = T³ + T` (or `2·(T³ + T)`);
  the polynomial `f` is produced by the elementary identities
  `aeval (ι t) (T³ + T) = ι (algebraMap g)`, which hold because `g ∈ {fAS, 2·fAS}` is a polynomial
  in `t` (see `aeval_algebraMap_fAS`, `aeval_algebraMap_two_smul_fAS`).
* This is exactly the hypothesis of the Artin–Schreier Hurwitz theorem `hurwitz_AS_ratFunc`
  (node H0_AS), which requires an algebraically closed base field.  We therefore apply it over
  `K = AlgebraicClosure M` to `ιK = ratFuncCoeffMap M K ∘ ι`, and descend with
  `Work.Wire123.exists_algebraMap_of_ratFuncCoeffMap_eq_algebraMap` ("if the base change of
  `x : RatFunc M` is constant, then `x` is constant").
-/

set_option autoImplicit false

namespace Work.MotV5.AssKlein

open Polynomial
open scoped WithZero

/-! ## §1 The two substitution identities -/

/-- `fAS = T³ + T` is a polynomial in `t`, so pushing it along `ι` is evaluation of `T³ + T` at
`ι t`. -/
theorem aeval_algebraMap_fAS {𝕜 L F : Type} [Field 𝕜] [Field L] [Field F] [Algebra 𝕜 L]
    [Algebra 𝕜 F] [Algebra (RatFunc 𝕜) F] [IsScalarTower 𝕜 (RatFunc 𝕜) F]
    (ι : F →ₐ[𝕜] RatFunc L) :
    Polynomial.aeval (ι (algebraMap (RatFunc 𝕜) F RatFunc.X))
        (Polynomial.X ^ 3 + Polynomial.X : Polynomial L)
      = ι (algebraMap (RatFunc 𝕜) F (Work.MotV.fAS 𝕜)) := by
  rw [Work.MotV.fAS]
  simp only [map_add, map_pow, Polynomial.aeval_X]

/-- The `2·fAS` version of `aeval_algebraMap_fAS`. -/
theorem aeval_algebraMap_two_smul_fAS {𝕜 L F : Type} [Field 𝕜] [Field L] [Field F] [Algebra 𝕜 L]
    [Algebra 𝕜 F] [Algebra (RatFunc 𝕜) F] [IsScalarTower 𝕜 (RatFunc 𝕜) F]
    (ι : F →ₐ[𝕜] RatFunc L) :
    Polynomial.aeval (ι (algebraMap (RatFunc 𝕜) F RatFunc.X))
        (2 * (Polynomial.X ^ 3 + Polynomial.X) : Polynomial L)
      = ι (algebraMap (RatFunc 𝕜) F (2 • Work.MotV.fAS 𝕜)) := by
  rw [Work.MotV.fAS, nsmul_eq_mul]
  simp only [map_mul, map_add, map_pow, Polynomial.aeval_X, map_ofNat, Nat.cast_ofNat]

/-! ## §2 The local Artin–Schreier condition from the bridge condition -/

/-- **The bridge condition gives local Artin–Schreier solvability at the poles.**  If `ι` pushes the
twist field `F` into a rational function field, and `t`, `g ∈ F` satisfy the Artin–Schreier
"unramified at the poles of `t`" condition, then at every pole of `r = ι t` the value `aeval r f`
(where `f` is the polynomial with `aeval (ι t) f = ι g`) is congruent to an Artin–Schreier value
modulo the valuation ring. -/
theorem localSol_of_asUnramified {𝕜 L F : Type} [Field 𝕜] [Field L] [Field F] [Algebra 𝕜 L]
    [Algebra 𝕜 F] [Algebra (RatFunc 𝕜) F] [IsScalarTower 𝕜 (RatFunc 𝕜) F]
    (ι : F →ₐ[𝕜] RatFunc L) (f : Polynomial L) {t g : F}
    (hB : Work.MotV5.ASUnramified 𝕜 F t g)
    (hsub : Polynomial.aeval (ι t) f = ι g) :
    ∀ v : Valuation (RatFunc L) (WithZero (Multiplicative ℤ)), Work.MotV.TrivOn L v →
      1 < v (ι t) → ∃ u, v (Polynomial.aeval (ι t) f - (u ^ 5 - u)) ≤ 1 := by
  intro v hv hlt
  have hw : Work.MotV.TrivOn 𝕜 (v.comap ι.toRingHom) := by
    intro c hc
    show v (ι (algebraMap 𝕜 F c)) = 1
    rw [ι.commutes c, IsScalarTower.algebraMap_apply 𝕜 L (RatFunc L)]
    exact hv _ (fun h => hc ((algebraMap 𝕜 L).injective (by rw [h, map_zero])))
  obtain ⟨z, hz⟩ := hB _ hw hlt
  refine ⟨ι z, ?_⟩
  rw [hsub]
  have hz' : v (ι g - ((ι z) ^ 5 - ι z)) ≤ 1 := by
    have h1 : (v.comap ι.toRingHom) (g - (z ^ 5 - z)) = v (ι g - ((ι z) ^ 5 - ι z)) := by
      rw [Valuation.comap_apply]
      simp
    rwa [h1] at hz
  exact hz'

/-! ## §3 Compatibility of `aeval` with the coefficient extension -/

/-- The coefficient extension commutes with `aeval`: `β (aeval r f) = aeval (β r) (f.map σ)`. -/
theorem ratFuncCoeffMap_aeval {M K : Type} [Field M] [Field K] [Algebra M K]
    (r : RatFunc M) (p : Polynomial M) :
    Work.Wire123.ratFuncCoeffMap M K (Polynomial.aeval r p)
      = Polynomial.aeval (Work.Wire123.ratFuncCoeffMap M K r) (p.map (algebraMap M K)) := by
  apply Polynomial.map_aeval_eq_aeval_map
  ext c
  exact (Work.Wire123.ratFuncCoeffMap_algebraMap c).symm

/-! ## §4 The reduction to the algebraically closed case -/

/-- Given the bridge condition and the substitution identity, `ι t` is a constant.  The proof
applies the Artin–Schreier Hurwitz theorem over the algebraic closure of `M` and descends. -/
private theorem key {𝕜 M : Type} [Field 𝕜] [Field M] [Algebra 𝕜 M] [CharP M 5]
    {F : Type} [Field F] [Algebra 𝕜 F] [Algebra (RatFunc 𝕜) F] [IsScalarTower 𝕜 (RatFunc 𝕜) F]
    (t gF : F) (hB : Work.MotV5.ASUnramified 𝕜 F t gF)
    (f : Polynomial M) (hf2 : 2 ≤ f.natDegree) (hf5 : ¬ 5 ∣ f.natDegree)
    (ι : F →ₐ[𝕜] RatFunc M) (hsub : Polynomial.aeval (ι t) f = ι gF) :
    ∃ c : M, algebraMap M (RatFunc M) c = ι t := by
  have hloc := localSol_of_asUnramified (L := M) ι f hB hsub
  haveI : CharP (AlgebraicClosure M) 5 :=
    charP_of_injective_algebraMap (RingHom.injective (algebraMap M (AlgebraicClosure M))) 5
  set β : RatFunc M →+* RatFunc (AlgebraicClosure M) :=
    Work.Wire123.ratFuncCoeffMap M (AlgebraicClosure M) with hβ
  -- the base-changed algebra map
  set ιK : F →ₐ[𝕜] RatFunc (AlgebraicClosure M) :=
    { toRingHom := β.comp ι.toRingHom
      commutes' := by
        intro c
        show β (ι (algebraMap 𝕜 F c)) = algebraMap 𝕜 (RatFunc (AlgebraicClosure M)) c
        rw [ι.commutes c, IsScalarTower.algebraMap_apply 𝕜 M (RatFunc M)]
        rw [show β (algebraMap M (RatFunc M) (algebraMap 𝕜 M c))
            = algebraMap (AlgebraicClosure M) (RatFunc (AlgebraicClosure M))
                (algebraMap M (AlgebraicClosure M) (algebraMap 𝕜 M c)) from
          Work.Wire123.ratFuncCoeffMap_algebraMap (algebraMap 𝕜 M c)]
        rw [← IsScalarTower.algebraMap_apply 𝕜 M (AlgebraicClosure M) c,
          ← IsScalarTower.algebraMap_apply 𝕜 (AlgebraicClosure M)
            (RatFunc (AlgebraicClosure M)) c] }
    with hιK
  -- transfer of the local condition to `AlgebraicClosure M`
  have htr : ∀ v : Valuation (RatFunc (AlgebraicClosure M)) (WithZero (Multiplicative ℤ)),
      Work.MotV.TrivOn (AlgebraicClosure M) v → 1 < v (ιK t) →
      ∃ u, v (Polynomial.aeval (ιK t) (f.map (algebraMap M (AlgebraicClosure M)))
        - (u ^ 5 - u)) ≤ 1 := by
    intro v hv hlt
    have hw : Work.MotV.TrivOn M (v.comap β) := by
      intro c hc
      show v (β (algebraMap M (RatFunc M) c)) = 1
      rw [Work.Wire123.ratFuncCoeffMap_algebraMap c]
      exact hv _ (fun h => hc ((algebraMap M (AlgebraicClosure M)).injective (by rw [h, map_zero])))
    have ht : (v.comap β) (ι t) = v (ιK t) := rfl
    obtain ⟨u, hu⟩ := hloc (v.comap β) hw (ht ▸ hlt)
    refine ⟨β u, ?_⟩
    have hβeval : β (Polynomial.aeval (ι t) f)
        = Polynomial.aeval (ιK t) (f.map (algebraMap M (AlgebraicClosure M))) := by
      rw [ratFuncCoeffMap_aeval]
      rfl
    have hβsub : β (Polynomial.aeval (ι t) f - (u ^ 5 - u))
        = Polynomial.aeval (ιK t) (f.map (algebraMap M (AlgebraicClosure M)))
          - ((β u) ^ 5 - β u) := by
      have h2 : β (u ^ 5 - u) = (β u) ^ 5 - β u := by rw [map_sub, map_pow]
      rw [map_sub, hβeval, h2]
    rw [← hβsub]
    exact hu
  -- the Hurwitz theorem over the algebraically closed field
  obtain ⟨c, hc⟩ := Work.MotV5.hurwitz_AS_ratFunc
    (f := f.map (algebraMap M (AlgebraicClosure M)))
    (by rw [Polynomial.natDegree_map_eq_of_injective (algebraMap M (AlgebraicClosure M)).injective]
        exact hf2)
    (by rw [Polynomial.natDegree_map_eq_of_injective (algebraMap M (AlgebraicClosure M)).injective]
        exact hf5)
    (ιK t) htr
  -- descend along the coefficient extension
  have hd : β (ι t) = algebraMap (AlgebraicClosure M) (RatFunc (AlgebraicClosure M)) c :=
    hc.symm
  obtain ⟨a, ha⟩ := Work.Wire123.exists_algebraMap_of_ratFuncCoeffMap_eq_algebraMap
    (K := M) (M := AlgebraicClosure M) (x := ι t) (m := c) hd
  exact ⟨a, ha.symm⟩

/-! ## §5 The target -/

theorem constantsOnly_as_base (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : D.Good) (hNC : Work.MotV5.KleinData.Nonconstant D)
    (hsm : D.a ^ 2 - D.a * D.b - D.b ^ 2 ≠ 0) (g : RatFunc 𝕜)
    (hg : g = Work.MotV.fAS 𝕜 ∨ g = 2 • Work.MotV.fAS 𝕜)
    (M : Type) [Field M] [Algebra 𝕜 M]
    (ι : ↥(Work.MotV5.asTwistField D g) →ₐ[𝕜] RatFunc M) :
    ∃ c : M, algebraMap M (RatFunc M) c
      = ι (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistField D g) RatFunc.X) := by
  haveI hM5 : CharP M 5 :=
    charP_of_injective_algebraMap (RingHom.injective (algebraMap 𝕜 M)) 5
  have hnd : (Polynomial.X ^ 3 + Polynomial.X : Polynomial M).natDegree = 3 := by
    compute_degree!
  have hnd2 : (2 * (Polynomial.X ^ 3 + Polynomial.X) : Polynomial M).natDegree = 3 := by
    have h2ne : (2 : M) ≠ 0 := fun h => by
      have hd : 5 ∣ 2 := (CharP.cast_eq_zero_iff M 5 2).mp h
      norm_num at hd
    have h2C : (2 : Polynomial M) = Polynomial.C (2 : M) := by
      rw [Polynomial.C_eq_algebraMap, map_ofNat]
    rw [h2C, Polynomial.natDegree_C_mul h2ne, hnd]
  have hf2 : 2 ≤ (Polynomial.X ^ 3 + Polynomial.X : Polynomial M).natDegree := by
    rw [hnd]; norm_num
  have hf5 : ¬ 5 ∣ (Polynomial.X ^ 3 + Polynomial.X : Polynomial M).natDegree := by
    rw [hnd]; norm_num
  have hg2 : 2 ≤ (2 * (Polynomial.X ^ 3 + Polynomial.X) : Polynomial M).natDegree := by
    rw [hnd2]; norm_num
  have hg5 : ¬ 5 ∣ (2 * (Polynomial.X ^ 3 + Polynomial.X) : Polynomial M).natDegree := by
    rw [hnd2]; norm_num
  rcases hg with hg1 | hg1
  · subst hg1
    have hB : Work.MotV5.ASUnramified 𝕜 ↥(Work.MotV5.asTwistField D (Work.MotV.fAS 𝕜))
        (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistField D (Work.MotV.fAS 𝕜)) RatFunc.X)
        (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistField D (Work.MotV.fAS 𝕜))
          (Work.MotV.fAS 𝕜)) :=
      Work.MotV5.bridge_as 𝕜 D hD hNC hsm (Work.MotV.fAS 𝕜)
        (fun i => Work.MotV5.asCoord_asTwCoord 𝕜 D (Work.MotV.fAS 𝕜) i)
    exact key _ _ hB _ hf2 hf5 ι (aeval_algebraMap_fAS ι)
  · subst hg1
    have hB : Work.MotV5.ASUnramified 𝕜 ↥(Work.MotV5.asTwistField D (2 • Work.MotV.fAS 𝕜))
        (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistField D (2 • Work.MotV.fAS 𝕜)) RatFunc.X)
        (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistField D (2 • Work.MotV.fAS 𝕜))
          (2 • Work.MotV.fAS 𝕜)) :=
      Work.MotV5.bridge_as 𝕜 D hD hNC hsm (2 • Work.MotV.fAS 𝕜)
        (fun i => Work.MotV5.asCoord_asTwCoord 𝕜 D (2 • Work.MotV.fAS 𝕜) i)
    exact key _ _ hB _ hg2 hg5 ι (aeval_algebraMap_two_smul_fAS ι)

end Work.MotV5.AssKlein
