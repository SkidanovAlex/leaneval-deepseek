import Mathlib
import Submission.Work.MotC5N3.Ruling
import Submission.Work.MotC5N3.ASZChartSetupGen
import Submission.Work.MotC5N3.twistFieldAS_eq
import Submission.Work.MotV5.ASLocal.asPhi2_denom
import Submission.Work.MotAS.map_asRuleQW
import Submission.Work.MotV.Defs
import Submission.Work.MotK.TwRuling.sdW_four_ne_zero

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.asPhi2_denom` — the chart-2 normalising coordinate over a general `K`

The `RatFunc 𝕜 ↦ K` fork of `Work.MotV5.ASLocal.asPhi2_denom`
(`Submission/Work/MotV5/ASLocal/asPhi2_denom.lean`): for an arbitrary `𝕜`-algebra field `K` of
characteristic `5`, any Klein datum `D : Work.MotV.KleinData 𝕜` with `ASGood D` and any `g : K`,
the zeroth component of the ruling point `asRuleQW a b g (asY0 D g) RatFunc.X` in
`RatFunc ↥(twistFieldAS D g)` is nonzero.

The ingredients are:

* `asTwY_mem_span_gen`: the Galois coordinates `asTwY D g` lie in `L(5·O)` (the span of
  `sdBas = (1, x, y, x², xy)`);
* `asRuleQB_asTwY_gen`: the quadratic form `asRuleQB a b g (asTwY D g) 0` is nonzero in the
  function field `OmA K D` — the "kernel of the multiplication map" computation
  (`Work.MotV5.ASLocal.cB_notMem_ker_Phi`, generic in the base ring) applied to `asTwY D g`;
* `asRuleQB_asY0_gen`: descent to the twist field `↥(twistFieldAS D g)`, using that `asY0 D g` is
  the projective normalisation `asTwY D g · (asTwY D g 0)⁻¹` and that `asRuleQB · 0` is a
  quadratic form;
* the assembly in `RatFunc ↥(twistFieldAS D g)`: `asRuleQW · 0` is `A + RatFunc.X · B` with
  `B ≠ 0`, and `RatFunc.X` is transcendental over `↥(twistFieldAS D g)`
  (`Work.MotV5.ASLocal.ratFunc_algebraMap_add_X_mul_ne_zero`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

namespace Work.MotC5N3

open WeierstrassCurve WeierstrassCurve.Affine

variable {𝕜 : Type} [Field 𝕜]
variable {K : Type} [Field K] [Algebra 𝕜 K]

/-! ## §1 Membership of `asTwY` in the span of `sdBas` -/

/-- The Galois coordinates `asTwY D g` lie in the span of the five functions `1, x, y, x², xy`
(the `RatFunc 𝕜 ↦ K` fork of `Work.MotAS.ASChart3.asTwY_mem_span`). -/
theorem asTwY_mem_span_gen (D : Work.MotV.KleinData 𝕜) (g : K) (i : Fin 5) :
    asTwY D g i ∈ Submodule.span (KbA K)
      (Set.range (Work.MotK.TwRuling.sdBas (D.E.baseChange (KbA K)))) := by
  have hbas : ∀ m : Fin 5, Work.MotV.kleinBas D (KbA K) m =
      Work.MotK.TwRuling.sdBas (D.E.baseChange (KbA K)) m := fun m => rfl
  have hklein : ∀ j : Fin 5, Work.MotV.kleinCoord D (KbA K) j ∈
      Submodule.span (KbA K)
        (Set.range (Work.MotK.TwRuling.sdBas (D.E.baseChange (KbA K)))) := by
    intro j
    rw [Work.MotV.kleinCoord_eq_sum]
    apply Submodule.sum_mem
    intro m _
    rw [hbas m, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  simp only [asTwY]
  apply Submodule.sum_mem
  intro j _
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (hklein j)

/-! ## §2 The generic non-degeneracy over `OmA K D` -/

section

variable [CharP K 5]

/-- **Non-vanishing of the chart-`2` ruling form at the Galois coordinates** (in `OmA K D`), the
`RatFunc 𝕜 ↦ K` fork of `Work.MotV5.ASLocal.asRuleQB_asTwY_ne_zero`. -/
theorem asRuleQB_asTwY_gen [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : K) :
    Work.MotAS.asRuleQB (algebraMap 𝕜 (OmA K D) D.a)
      (algebraMap 𝕜 (OmA K D) D.b) (algebraMap K (OmA K D) g) (asTwY D g) 0 ≠ 0 := by
  classical
  have h5R : (5 : KbA K) = 0 := five_eq_zero_KbA K
  have h2R : (2 : KbA K) ≠ 0 := by
    intro hh
    have h1 : (1 : KbA K) = 0 := by
      have h52 : (5 : KbA K) = 2 * 2 + 1 := by norm_num
      rw [h52, hh, mul_zero, zero_add] at h5R
      exact h5R
    exact one_ne_zero h1
  have hδ : (algebraMap 𝕜 (KbA K) D.a) ^ 2
      - (algebraMap 𝕜 (KbA K) D.a) * (algebraMap 𝕜 (KbA K) D.b)
      - (algebraMap 𝕜 (KbA K) D.b) ^ 2 ≠ 0 := by
    intro h
    exact hD.2.2.2 (RingHom.injective (algebraMap 𝕜 (KbA K))
      (by simpa only [map_sub, map_mul, map_pow, map_zero] using h))
  have ha0 : D.a ≠ 0 := fun h => hD.1.ab_ne (by rw [h, zero_mul])
  have hb0 : D.b ≠ 0 := fun h => hD.1.ab_ne (by rw [h, mul_zero])
  have hAne : algebraMap 𝕜 (KbA K) D.a ≠ 0 :=
    fun h => ha0 (RingHom.injective (algebraMap 𝕜 (KbA K)) (by rw [h, map_zero]))
  have hBne : algebraMap 𝕜 (KbA K) D.b ≠ 0 :=
    fun h => hb0 (RingHom.injective (algebraMap 𝕜 (KbA K)) (by rw [h, map_zero]))
  have hκmem : ∀ i : Fin 5, asTwY D g i ∈ Submodule.span (KbA K)
      (Set.range (Work.MotK.TwRuling.sdBas (D.E.baseChange (KbA K)))) :=
    fun i => asTwY_mem_span_gen D g i
  have hspans : ∀ m : Fin 5, Work.MotK.TwRuling.sdBas (D.E.baseChange (KbA K)) m
      ∈ Submodule.span (KbA K) (Set.range (asTwY D g)) := by
    obtain ⟨e, he⟩ := hD.1.spans
    intro m
    rw [show Work.MotK.TwRuling.sdBas (D.E.baseChange (KbA K)) m
        = Work.MotV.kleinBas D (KbA K) m from rfl, he (KbA K) m]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [show Work.MotV.kleinCoord D (KbA K) i = asKap D g i from rfl, ← Algebra.smul_def]
    refine Submodule.smul_mem _ _ ?_
    have h := congrFun (asMO_mulVec_asTwY D g) i
    rw [← h, Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    rw [show asMO D g i j
        = algebraMap (KbA K) (OmA K D)
            (Work.MotAS.asM (asRoot g) i j) from rfl, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hκ : ∀ k : Fin 5, Work.MotAS.kleinPAS (algebraMap 𝕜 (OmA K D) D.a)
      (algebraMap 𝕜 (OmA K D) D.b) (algebraMap K (OmA K D) g) (asTwY D g) k = 0 := by
    intro k
    have h := congrFun (kleinPAS_asTwY D hD.1 g) k
    simp only [aK, bK] at h
    rw [← IsScalarTower.algebraMap_apply 𝕜 K (OmA K D) D.a,
      ← IsScalarTower.algebraMap_apply 𝕜 K (OmA K D) D.b] at h
    exact h
  have hnot := Work.MotV5.ASLocal.cB_notMem_ker_Phi (algebraMap 𝕜 (KbA K) D.a)
    (algebraMap 𝕜 (KbA K) D.b) (algebraMap K (KbA K) g)
    h2R hδ hAne hBne h5R (asTwY D g) hκmem hspans hκ
  intro h0
  exact hnot (by
    rw [LinearMap.mem_ker, Work.MotV5.ASLocal.Phi_cB_eq]
    rw [← IsScalarTower.algebraMap_apply 𝕜 (KbA K) (OmA K D) D.a,
      ← IsScalarTower.algebraMap_apply 𝕜 (KbA K) (OmA K D) D.b,
      ← IsScalarTower.algebraMap_apply K (KbA K) (OmA K D) g]
    exact h0)

/-! ## §3 Descent to the twist field -/

/-- **Non-vanishing of the chart-`2` ruling form at the generic point `asY0 D g` of the twisted
Klein curve**, the `RatFunc 𝕜 ↦ K` fork of `Work.MotV5.ASLocal.asRuleQB_asY0_ne_zero`. -/
theorem asRuleQB_asY0_gen [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : K) :
    Work.MotAS.asRuleQB (algebraMap 𝕜 ↥(twistFieldAS D g) D.a)
      (algebraMap 𝕜 ↥(twistFieldAS D g) D.b)
      (algebraMap K ↥(twistFieldAS D g) g)
      (asY0 D g) 0 ≠ 0 := by
  have hOm := asRuleQB_asTwY_gen D hD g
  intro hB
  have towerA : algebraMap 𝕜 (OmA K D) D.a
      = algebraMap ↥(twistFieldAS D g) (OmA K D)
          (algebraMap 𝕜 ↥(twistFieldAS D g) D.a) := by
    rw [IsScalarTower.algebraMap_apply 𝕜 K (OmA K D) D.a,
      IsScalarTower.algebraMap_apply K ↥(twistFieldAS D g) (OmA K D)
        (algebraMap 𝕜 K D.a),
      ← IsScalarTower.algebraMap_apply 𝕜 K ↥(twistFieldAS D g) D.a]
  have towerB : algebraMap 𝕜 (OmA K D) D.b
      = algebraMap ↥(twistFieldAS D g) (OmA K D)
          (algebraMap 𝕜 ↥(twistFieldAS D g) D.b) := by
    rw [IsScalarTower.algebraMap_apply 𝕜 K (OmA K D) D.b,
      IsScalarTower.algebraMap_apply K ↥(twistFieldAS D g) (OmA K D)
        (algebraMap 𝕜 K D.b),
      ← IsScalarTower.algebraMap_apply 𝕜 K ↥(twistFieldAS D g) D.b]
  have towerG : algebraMap K (OmA K D) g
      = algebraMap ↥(twistFieldAS D g) (OmA K D)
          (algebraMap K ↥(twistFieldAS D g) g) :=
    IsScalarTower.algebraMap_apply K ↥(twistFieldAS D g) (OmA K D) g
  have hpt : (fun j => algebraMap ↥(twistFieldAS D g) (OmA K D) (asY0 D g j))
      = (asTwY D g 0)⁻¹ • asTwY D g := by
    funext j
    show algebraMap ↥(twistFieldAS D g) (OmA K D) (asY0 D g j)
      = (asTwY D g 0)⁻¹ * asTwY D g j
    rw [show algebraMap ↥(twistFieldAS D g) (OmA K D) (asY0 D g j)
        = ((asY0 D g j : ↥(twistFieldAS D g)) : OmA K D) from rfl,
      show ((asY0 D g j : ↥(twistFieldAS D g)) : OmA K D)
        = asTwY D g j / asTwY D g 0 from rfl,
      div_eq_mul_inv, mul_comm]
  have key : Work.MotAS.asRuleQB (algebraMap 𝕜 (OmA K D) D.a)
      (algebraMap 𝕜 (OmA K D) D.b) (algebraMap K (OmA K D) g)
      (fun j => algebraMap ↥(twistFieldAS D g) (OmA K D) (asY0 D g j)) 0 = 0 := by
    have h1 : algebraMap ↥(twistFieldAS D g) (OmA K D)
        (Work.MotAS.asRuleQB (algebraMap 𝕜 ↥(twistFieldAS D g) D.a)
          (algebraMap 𝕜 ↥(twistFieldAS D g) D.b)
          (algebraMap K ↥(twistFieldAS D g) g) (asY0 D g) 0) = 0 := by rw [hB, map_zero]
    rw [Work.MotAS.map_asRuleQB (algebraMap ↥(twistFieldAS D g) (OmA K D))
      (algebraMap 𝕜 ↥(twistFieldAS D g) D.a)
      (algebraMap 𝕜 ↥(twistFieldAS D g) D.b)
      (algebraMap K ↥(twistFieldAS D g) g) (asY0 D g) 0] at h1
    rw [← towerA, ← towerB, ← towerG] at h1
    exact h1
  rw [hpt, Work.MotV5.ASLocal.asRuleQB_smul_zero] at key
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (pow_ne_zero 2 (inv_ne_zero (asTwY_zero_ne_zero D g hD.1)))
  · exact hOm h

end

/-! ## §4 The assembly -/

/-- **The chart-`2` normalising coordinate is nonzero.**  `asW2 D g 0` is `A + RatFunc.X · B` with
`A, B ∈ ↥(twistFieldAS D g)` and `B ≠ 0`; `RatFunc.X` is transcendental over `↥(twistFieldAS D g)`,
so the sum cannot vanish. -/
theorem asPhi2_denom (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K) :
    Work.MotC5N3.asW2 D g 0 ≠ 0 := by
  haveI : CharP 𝕜 5 := charP_of_algebra_charP (𝕜 := 𝕜) (K := K)
  have hB : Work.MotAS.asRuleQB (algebraMap 𝕜 ↥(twistFieldAS D g) D.a)
      (algebraMap 𝕜 ↥(twistFieldAS D g) D.b)
      (algebraMap K ↥(twistFieldAS D g) g) (asY0 D g) 0 ≠ 0 :=
    asRuleQB_asY0_gen D hD g
  have hmain : Work.MotC5N3.asW2 D g 0
      = algebraMap ↥(twistFieldAS D g) (RatFunc ↥(twistFieldAS D g))
          (Work.MotAS.asRuleQA (algebraMap 𝕜 ↥(twistFieldAS D g) D.a)
            (algebraMap 𝕜 ↥(twistFieldAS D g) D.b)
            (algebraMap K ↥(twistFieldAS D g) g) (asY0 D g) 0)
        + RatFunc.X * algebraMap ↥(twistFieldAS D g) (RatFunc ↥(twistFieldAS D g))
          (Work.MotAS.asRuleQB (algebraMap 𝕜 ↥(twistFieldAS D g) D.a)
            (algebraMap 𝕜 ↥(twistFieldAS D g) D.b)
            (algebraMap K ↥(twistFieldAS D g) g) (asY0 D g) 0) := by
    simp only [asW2, Work.MotAS.asRuleQW, as2a, as2b, as2g, as2A]
    rw [IsScalarTower.algebraMap_apply 𝕜 ↥(twistFieldAS D g)
          (RatFunc ↥(twistFieldAS D g)) D.a,
      IsScalarTower.algebraMap_apply 𝕜 ↥(twistFieldAS D g)
          (RatFunc ↥(twistFieldAS D g)) D.b,
      IsScalarTower.algebraMap_apply K ↥(twistFieldAS D g)
          (RatFunc ↥(twistFieldAS D g)) g,
      ← Work.MotAS.map_asRuleQA (algebraMap ↥(twistFieldAS D g)
          (RatFunc ↥(twistFieldAS D g)))
        (algebraMap 𝕜 ↥(twistFieldAS D g) D.a) (algebraMap 𝕜 ↥(twistFieldAS D g) D.b)
        (algebraMap K ↥(twistFieldAS D g) g) (asY0 D g) 0,
      ← Work.MotAS.map_asRuleQB (algebraMap ↥(twistFieldAS D g)
          (RatFunc ↥(twistFieldAS D g)))
        (algebraMap 𝕜 ↥(twistFieldAS D g) D.a) (algebraMap 𝕜 ↥(twistFieldAS D g) D.b)
        (algebraMap K ↥(twistFieldAS D g) g) (asY0 D g) 0]
  rw [hmain]
  exact Work.MotV5.ASLocal.ratFunc_algebraMap_add_X_mul_ne_zero hB

end Work.MotC5N3
