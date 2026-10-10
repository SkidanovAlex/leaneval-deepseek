import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.hurwitz_AS_ratFunc
import Submission.Work.MotV5.AssKlein.constantsOnly_as_base
import Submission.Work.MotV.constantsOnly_twist
import Submission.Work.Wire123.RatFuncCoeff
import Submission.Work.MotV.exists_algHom_ratFunc_of_image_X

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

namespace Work.MotV5.RigAS

/-! The `𝕜`-linear/`K`-linear transfer for constants-only of the AS twist field
`F = asTwistFieldTrue D g τ σS` (`K = RatFunc 𝕜`): assuming

* `hB` — the Artin–Schreier bridge condition `ASUnramified 𝕜 F t g` (node BR_AS
  `Work.MotV5.Nodes.bridge_AS`; `t = algebraMap K F RatFunc.X`, `g ∈ {fAS, 2•fAS}`), and
* `hK` — the `K`-linear constants-only form (`Work.MotV5.RigAS.constantsOnly_K_AS`),

every `𝕜`-algebra map `F →ₐ[𝕜] RatFunc M` has image inside the constants `M`.

ROUTE — mirror `Work.MotV.constantsOnly_twist` (`Submission/Work/MotV/constantsOnly_twist.lean`,
PROVED) steps 2–3.

* Let `ι : F →ₐ[𝕜] RatFunc M`, put `N := AlgebraicClosure M` and `ιbar : F →ₐ[𝕜] RatFunc N` the
  composite with the coefficient extension; `CharP N 5` holds.
* **`ι t` is a constant.**  Take `f : Polynomial N` = `X^3 + X` if `g = fAS 𝕜`, and
  `2 * (X^3 + X)` if `g = 2 • fAS 𝕜`; the substitution identities
  `Work.MotV5.AssKlein.aeval_algebraMap_fAS` / `aeval_algebraMap_two_smul_fAS` give
  `Polynomial.aeval (ιbar t) f = ιbar (algebraMap K F g)`, and
  `Work.MotV5.AssKlein.localSol_of_asUnramified` (PROVED, general in `F`) converts `hB` into the
  local Artin–Schreier hypothesis of `Work.MotV5.hurwitz_AS_ratFunc` (PROVED) at `r = ιbar t`.
  `hurwitz_AS_ratFunc` gives `∃ c : N, algebraMap N (RatFunc N) c = ιbar t`; then
  `Work.Wire123.exists_algebraMap_of_ratFuncCoeffMap_eq_algebraMap` descends it to
  `∃ m : M, algebraMap M (RatFunc M) m = ι t`.
  The whole of this step is already written (generically in `F`) in
  `Submission/Work/MotV5/AssKlein/constantsOnly_as_base.lean`, as the PRIVATE declaration `key`
  (`(t gF : F) (hB : ASUnramified 𝕜 F t gF) (f : Polynomial M) ... (ι : F →ₐ[𝕜] RatFunc M)
  (hsub : aeval (ι t) f = ι gF) : ∃ c : M, algebraMap M (RatFunc M) c = ι t`): copy its proof body,
  instantiating `F := ↥(asTwistFieldTrue D g τ σS)`, `t := algebraMap K F RatFunc.X`,
  `gF := algebraMap K F g`, `hB := hB`.
* **Transfer.**  `ι t ∈ M`; then use `Work.MotV.exists_algHom_ratFunc_of_image_X` (PROVED) to make
  `M` a `K`-algebra with `χ : K →ₐ[𝕜] M`, `χ X = ι t`, and `ι` a `K`-algebra map `F →ₐ[K] RatFunc M`;
  `hK` then gives `ι x ∈ M` for every `x`.  This is verbatim the final part of
  `Work.MotV.constantsOnly_twist`. -/

/-- Copy of the (private) declaration `key` of `Submission/Work/MotV5/AssKlein/constantsOnly_as_base`
with all names qualified.  Given an Artin–Schreier unramified condition on `(t, gF)` in `F`, a
polynomial `f` of degree `≢ 0` mod `5` (with `2 ≤ deg f`) satisfying the substitution identity
`aeval (ι t) f = ι gF`, the image `ι t` is a constant of the rational function field `M(y)`.

The proof works over the algebraic closure of `M` (applying `hurwitz_AS_ratFunc`), then descends
along the coefficient extension by `Work.Wire123.exists_algebraMap_of_ratFuncCoeffMap_eq_algebraMap`. -/
private theorem key {𝕜 M : Type} [Field 𝕜] [Field M] [Algebra 𝕜 M] [CharP M 5]
    {F : Type} [Field F] [Algebra 𝕜 F] [Algebra (RatFunc 𝕜) F] [IsScalarTower 𝕜 (RatFunc 𝕜) F]
    (t gF : F) (hB : Work.MotV5.ASUnramified 𝕜 F t gF)
    (f : Polynomial M) (hf2 : 2 ≤ f.natDegree) (hf5 : ¬ 5 ∣ f.natDegree)
    (ι : F →ₐ[𝕜] RatFunc M) (hsub : Polynomial.aeval (ι t) f = ι gF) :
    ∃ c : M, algebraMap M (RatFunc M) c = ι t := by
  have hloc := Work.MotV5.AssKlein.localSol_of_asUnramified (L := M) ι f hB hsub
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
      rw [Work.MotV5.AssKlein.ratFuncCoeffMap_aeval]
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

theorem constantsOnly_transfer_AS (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜)
    (hg : g = Work.MotV.fAS 𝕜 ∨ g = 2 • Work.MotV.fAS 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ)
    (hB : Work.MotV5.ASUnramified 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) g))
    (hK : Work.MotV.ConstantsOnly (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS)) :
    Work.MotV.ConstantsOnly 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS) := by
  classical
  intro M _instM _instAlgM ι x
  haveI hM5 : CharP M 5 :=
    charP_of_injective_algebraMap (RingHom.injective (algebraMap 𝕜 M)) 5
  -- degree bookkeeping for the two polynomials
  have hnd : (Polynomial.X ^ 3 + Polynomial.X : Polynomial M).natDegree = 3 := by
    compute_degree!
  have hnd2 : (2 * (Polynomial.X ^ 3 + Polynomial.X) : Polynomial M).natDegree = 3 := by
    have h2ne : (2 : M) ≠ 0 := by
      intro h20
      have hd : 5 ∣ 2 := (CharP.cast_eq_zero_iff M 5 2).mp h20
      norm_num at hd
    have h2C : (2 : Polynomial M) = Polynomial.C (2 : M) := by
      rw [Polynomial.C_eq_algebraMap, map_ofNat]
    rw [h2C, Polynomial.natDegree_C_mul h2ne, hnd]
  -- ## Step 1: the image of the parameter `t` is a constant
  have hmain : ∃ m : M, algebraMap M (RatFunc M) m
      = ι (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X) := by
    rcases hg with hg1 | hg1
    · -- `g = fAS 𝕜`
      have hga : algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) g
          = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
              (Work.MotV.fAS 𝕜) :=
        congrArg (fun z => algebraMap (RatFunc 𝕜)
          ↥(Work.MotV5.asTwistFieldTrue D g τ σS) z) hg1
      refine key (F := ↥(Work.MotV5.asTwistFieldTrue D g τ σS))
        (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X)
        (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) g)
        hB (Polynomial.X ^ 3 + Polynomial.X : Polynomial M) ?_ ?_ ι ?_
      · rw [hnd]; norm_num
      · rw [hnd]; norm_num
      · exact (Work.MotV5.AssKlein.aeval_algebraMap_fAS ι).trans
          (congrArg (fun z => ι z) hga.symm)
    · -- `g = 2 • fAS 𝕜`
      have hga : algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) g
          = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
              (2 • Work.MotV.fAS 𝕜) :=
        congrArg (fun z => algebraMap (RatFunc 𝕜)
          ↥(Work.MotV5.asTwistFieldTrue D g τ σS) z) hg1
      refine key (F := ↥(Work.MotV5.asTwistFieldTrue D g τ σS))
        (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X)
        (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) g)
        hB (2 * (Polynomial.X ^ 3 + Polynomial.X) : Polynomial M) ?_ ?_ ι ?_
      · rw [hnd2]; norm_num
      · rw [hnd2]; norm_num
      · exact (Work.MotV5.AssKlein.aeval_algebraMap_two_smul_fAS ι).trans
          (congrArg (fun z => ι z) hga.symm)
  -- ## Step 2: `M` is a `RatFunc 𝕜`-algebra and `ι` is `RatFunc 𝕜`-linear
  obtain ⟨m₀, hm₀⟩ := hmain
  obtain ⟨χ, _hχX, hχ⟩ := Work.MotV.exists_algHom_ratFunc_of_image_X ι m₀ hm₀
  letI : Algebra (RatFunc 𝕜) M := χ.toRingHom.toAlgebra
  haveI hST : IsScalarTower 𝕜 (RatFunc 𝕜) M :=
    IsScalarTower.of_algebraMap_eq fun c => by
      show algebraMap 𝕜 M c = χ (algebraMap 𝕜 (RatFunc 𝕜) c)
      exact (χ.commutes c).symm
  have hιK : ∀ k : RatFunc 𝕜, ι (algebraMap (RatFunc 𝕜)
      ↥(Work.MotV5.asTwistFieldTrue D g τ σS) k) = algebraMap (RatFunc 𝕜) (RatFunc M) k := by
    intro k
    rw [IsScalarTower.algebraMap_apply (RatFunc 𝕜) M (RatFunc M) k]
    show ι (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) k)
      = algebraMap M (RatFunc M) (algebraMap (RatFunc 𝕜) M k)
    rw [show algebraMap (RatFunc 𝕜) M k = χ k from rfl]
    exact hχ k
  let ι' : ↥(Work.MotV5.asTwistFieldTrue D g τ σS) →ₐ[RatFunc 𝕜] RatFunc M :=
    { ι.toRingHom with commutes' := hιK }
  -- ## Step 3: the `RatFunc 𝕜`-linear form
  exact hK M ι' x

end Work.MotV5.RigAS
