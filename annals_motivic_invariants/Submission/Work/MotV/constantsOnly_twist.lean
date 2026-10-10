import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotV.bridge
import Submission.Work.MotV.hurwitz_five_ratFunc
import Submission.Work.MotV.CTAux
import Submission.Work.MotV.ExpRigDefs
import Submission.Work.MotV.fifthPowerValued_of_pow
import Submission.Work.MotV.fifthPowerValued_map_algHom
import Submission.Work.MotV.exists_algHom_ratFunc_of_image_X
import Submission.Work.MotT.RouteVCorollaries
import Submission.Work.MotT.constantsOnly_twistK
import Submission.Work.MotT.RouteVBridge

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

set_option linter.style.haveILetI false
set_option linter.dupNamespace false

namespace Work.MotV

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.MotV

/-- Node CO (constants-only): for `h = hT = t(t-1)` or `h = (hT)^2` (and `char ≠ 5`), every
`𝕜`-embedding of the T-twist field `F_h` into a rational function field `M(y)` has image in the
constants `M`.

This is provable **without** the point transport between the Klein quintic and the Weierstrass
model: the `RatFunc 𝕜`-linear form of the statement is node T5 of the generic layer and the
`𝕜`-linear form follows from it plus the one-variable rigidity H0.  Route:

1. **The `RatFunc 𝕜`-linear form.**  Put `K := RatFunc 𝕜`, `D' := MotT.kleinDataBaseChange D K` and
   `h' : K := h`.  `Work.MotT.constantsOnly_twistK D' (Work.MotT.kleinDataBaseChange_good D hD)
   (Work.MotT.ringChar_ratFunc_ne_five hk) h hh'` gives
   `ConstantsOnly K (Work.MotT.twistFieldTK D' h)`, and `Work.MotT.twistFieldT_eq_twistFieldTK` is
   `rfl`, so this is `ConstantsOnly K (twistFieldT D h)`.
2. **`ι t ∈ M`.**  Let `M` be a `𝕜`-field and `ι : twistFieldT D h →ₐ[𝕜] RatFunc M`; compose with
   `RatFunc M ↪ RatFunc M̄` for an algebraic closure `M̄`/`M` to get `ῑ`.
   * If `h = hT 𝕜`: for every `v : Valuation (RatFunc M̄) ℤᵐ⁰` with `TrivOn M̄ v`, the composite
     `v ∘ ῑ` is a valuation of `twistFieldT D h` trivial on `𝕜` (use that `ῑ` is a `𝕜`-algebra map),
     and `Work.MotV.bridge D hD (hT 𝕜) …` (node BR) gives that
     `v (ῑ (algebraMap K _ (hT 𝕜))) = v (ῑ t · (ῑ t - 1))` is a fifth power.  Then
     `Work.MotV.hurwitz_five_ratFunc` (node H0, `char ≠ 5`, `M̄` algebraically closed) gives
     `ῑ t = algebraMap M̄ (RatFunc M̄) c` for some `c : M̄`.
   * If `h = hT 𝕜 ^ 2`: BR gives the same conclusion for `(ῑ t · (ῑ t - 1))²`; as the value group
     `ℤᵐ⁰` is torsion-free, `2·a = 5·b ⟹ 5 ∣ a`, so `v (ῑ t · (ῑ t - 1))` is a fifth power as well
     (e.g. `v (ῑ (t(t-1))) = v (u³ / ῑ (t(t-1))) ^ 5`), and H0 applies again.
   * **Descent.**  `ι t ∈ RatFunc M` and its image in `RatFunc M̄` is a constant: writing
     `ι t = p/q` with `p, q ∈ M[X]`, `q ≠ 0`, the identity `p̄ = c · q̄` in `M̄[X]` and comparison of
     the coefficient of `X ^ q.natDegree` shows `c ∈ M`; hence `ι t ∈ M`.  (So
     `M̄ ∩ RatFunc M = M` inside `RatFunc M̄`.)
3. **Conclusion.**  The composite `K → twistFieldT D h → RatFunc M` is injective (both maps are
   nonzero ring maps between fields, `twistFieldT D h` being a field), so `ι t` is transcendental
   over `𝕜`; the `𝕜`-algebra map `𝕜[X] → M`, `X ↦ ι t` therefore localises to a ring hom
   `K → M`, which makes `M` a `K`-algebra (with `IsScalarTower 𝕜 K M`).  With respect to it, `M ↪
   RatFunc M` is `K`-linear and the composite `K → twistFieldT D h → RatFunc M` (which sends `t` to
   `ι t`) agrees with it; hence `ι` is `K`-linear.  Applying the `RatFunc 𝕜`-linear form of step 1
   with this `K`-algebra structure on `M` and the map `ι` gives, for every `x`, some `c : M` with
   `algebraMap M (RatFunc M) c = ι x`, i.e. `ι x ∈ M`.  That is `ConstantsOnly 𝕜 (twistFieldT D h)`.

(For `h = hT 𝕜` the `h ≠ 0` needed in steps 1–2 follows from `hT 𝕜 ≠ 0`, e.g. from
`Work.MotV.vT_hT : vT 𝕜 (hT 𝕜) = exp (-1)` in `Submission/Work/MotV/ExpRigDefs.lean`; for
`h = hT 𝕜 ^ 2` use `pow_ne_zero 2`.) -/
theorem constantsOnly_twist {𝕜 : Type} [Field 𝕜] (D : KleinData 𝕜) (hD : D.Good)
    (hk : ringChar 𝕜 ≠ 5) (h : RatFunc 𝕜) (hh : h = hT 𝕜 ∨ h = hT 𝕜 ^ 2) :
    ConstantsOnly 𝕜 (twistFieldT D h) := by
  classical
  -- `h ≠ 0` (needed for the bridge BR and for the `RatFunc 𝕜`-linear form T5)
  have hh0 : h ≠ 0 := by
    rcases hh with hh | hh
    · rw [hh]; exact hT_ne_zero 𝕜
    · rw [hh]; exact pow_ne_zero 2 (hT_ne_zero 𝕜)
  -- the Kummer parameter `t(t-1)` is fifth-power valued in `F_h`
  have hfpvT : FifthPowerValued 𝕜
      (algebraMap (RatFunc 𝕜) ↥(twistFieldT D h) (hT 𝕜)) := by
    rcases hh with hh | hh
    · rw [hh]
      exact bridge D hD (hT 𝕜) (hT_ne_zero 𝕜)
    · rw [hh]
      refine fifthPowerValued_of_pow (k := 2) (by norm_num) ?_
      rw [← map_pow]
      exact bridge D hD (hT 𝕜 ^ 2) (pow_ne_zero 2 (hT_ne_zero 𝕜))
  have hKchar : ringChar (RatFunc 𝕜) ≠ 5 := MotT.ringChar_ratFunc_ne_five hk
  have hD' : (MotT.kleinDataBaseChange D (RatFunc 𝕜)).Good :=
    MotT.kleinDataBaseChange_good D hD
  intro M _instM _instAlgM ι x
  -- ## Step 1: the image of `t` lies in the constants
  have hmain : ∃ m : M, algebraMap M (RatFunc M) m
      = ι (algebraMap (RatFunc 𝕜) ↥(twistFieldT D h) (RatFunc.X : RatFunc 𝕜)) := by
    -- the algebraic closure `N := M̄` and the coefficient extension `ρ₀ : M(t) → N(t)`
    let N := AlgebraicClosure M
    have hcoeff : Function.Injective
        (Polynomial.mapAlgHom (Algebra.ofId M N) : Polynomial M →ₐ[M] Polynomial N) := by
      intro p q hpq
      exact Polynomial.map_injective (algebraMap M N) (algebraMap M N).injective hpq
    have hφ : nonZeroDivisors (Polynomial M) ≤
        Submonoid.comap (Polynomial.mapAlgHom (Algebra.ofId M N))
          (nonZeroDivisors (Polynomial N)) :=
      nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hcoeff
    let ρ₀ : RatFunc M →ₐ[M] RatFunc N :=
      RatFunc.mapAlgHom (Polynomial.mapAlgHom (Algebra.ofId M N)) hφ
    have hρ₀inj : Function.Injective ρ₀ :=
      RingHom.injective (ρ₀ : RatFunc M →+* RatFunc N)
    let ιbar : ↥(twistFieldT D h) →ₐ[𝕜] RatFunc N := (ρ₀.restrictScalars 𝕜).comp ι
    let s : ↥(twistFieldT D h) := algebraMap (RatFunc 𝕜) _ (RatFunc.X : RatFunc 𝕜)
    have hNchar : ringChar N ≠ 5 := by
      intro h5
      haveI : CharP N 5 := ringChar.of_eq h5
      have hzero : (5 : N) = 0 := CharP.cast_eq_zero N 5
      have hM5 : (5 : M) = 0 := (algebraMap M N).injective (by rw [map_ofNat, hzero, map_zero])
      haveI : CharP M 5 := (CharP.charP_iff_prime_eq_zero (by norm_num : Nat.Prime 5)).mpr hM5
      have hk5 : (5 : 𝕜) = 0 := (algebraMap 𝕜 M).injective (by rw [map_ofNat, hM5, map_zero])
      haveI : CharP 𝕜 5 := (CharP.charP_iff_prime_eq_zero (by norm_num : Nat.Prime 5)).mpr hk5
      exact hk (ringChar.eq (R := 𝕜) 5)
    -- BR + H0: `ιbar t` is a constant of `N(y)`
    have hconst : ∃ c : N, algebraMap N (RatFunc N) c = ιbar s := by
      have hpush := fifthPowerValued_map_algHom ιbar
        (algebraMap (RatFunc 𝕜) ↥(twistFieldT D h) (hT 𝕜)) hfpvT
      have hrew : ιbar (algebraMap (RatFunc 𝕜) ↥(twistFieldT D h) (hT 𝕜))
          = ιbar s * (ιbar s - 1) := by
        simp only [hT, map_mul, map_sub, map_one, s]
      rw [hrew] at hpush
      exact hurwitz_five_ratFunc hNchar (ιbar s) hpush
    -- descent: `ι t` is algebraic over `M`, hence constant
    obtain ⟨c, hc⟩ := hconst
    have halg : IsAlgebraic M (ρ₀ (ι s)) := by
      have h1 : ρ₀ (ι s) = algebraMap N (RatFunc N) c :=
        (show ρ₀ (ι s) = ιbar s from rfl).trans hc.symm
      rw [h1]
      exact IsAlgebraic.algebraMap (Algebra.IsAlgebraic.isAlgebraic c)
    have halg' : IsAlgebraic M (ι s) := (isAlgebraic_algHom_iff ρ₀ hρ₀inj).mp halg
    obtain ⟨m, hm⟩ := MotC.ratFunc_eq_C_of_isAlgebraic (ι s) halg'
    exact ⟨m, hm.symm⟩
  -- ## Step 2: `M` is a `RatFunc 𝕜`-algebra and `ι` is `RatFunc 𝕜`-linear
  obtain ⟨m₀, hm₀⟩ := hmain
  obtain ⟨χ, _hχX, hχ⟩ := exists_algHom_ratFunc_of_image_X ι m₀ hm₀
  letI : Algebra (RatFunc 𝕜) M := χ.toRingHom.toAlgebra
  haveI hST : IsScalarTower 𝕜 (RatFunc 𝕜) M :=
    IsScalarTower.of_algebraMap_eq fun c => by
      show algebraMap 𝕜 M c = χ (algebraMap 𝕜 (RatFunc 𝕜) c)
      exact (χ.commutes c).symm
  have hιK : ∀ k : RatFunc 𝕜, ι (algebraMap (RatFunc 𝕜) ↥(twistFieldT D h) k)
      = algebraMap (RatFunc 𝕜) (RatFunc M) k := by
    intro k
    rw [IsScalarTower.algebraMap_apply (RatFunc 𝕜) M (RatFunc M) k]
    show ι (algebraMap (RatFunc 𝕜) ↥(twistFieldT D h) k)
      = algebraMap M (RatFunc M) (algebraMap (RatFunc 𝕜) M k)
    rw [show algebraMap (RatFunc 𝕜) M k = χ k from rfl]
    exact hχ k
  let ι' : ↥(twistFieldT D h) →ₐ[RatFunc 𝕜] RatFunc M :=
    { ι.toRingHom with commutes' := hιK }
  -- ## Step 3: the `RatFunc 𝕜`-linear form T5
  have hCO := MotT.constantsOnly_twistK (MotT.kleinDataBaseChange D (RatFunc 𝕜)) hD' hKchar h hh0
  have hx : ∃ c : M, algebraMap M (RatFunc M) c = ι' x := hCO M ι' x
  exact hx

end Work.MotV

set_option linter.dupNamespace false

/-- `Work.MotV.constantsOnly_twist`: the canonical (single-namespace) statement, definitionally
equal to the declaration `Work.MotV.Work.MotV.constantsOnly_twist` above, which is kept so that the
doubly nested name also resolves. -/
theorem constantsOnly_twist {𝕜 : Type} [Field 𝕜] (D : KleinData 𝕜) (hD : D.Good)
    (hk : ringChar 𝕜 ≠ 5) (h : RatFunc 𝕜) (hh : h = hT 𝕜 ∨ h = hT 𝕜 ^ 2) :
    ConstantsOnly 𝕜 (twistFieldT D h) :=
  _root_.Work.MotV.Work.MotV.constantsOnly_twist D hD hk h hh

end Work.MotV
