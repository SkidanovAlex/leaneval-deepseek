import Mathlib
import Submission.Work.Diff.GE.EvolB.NrmBounds
import Submission.Work.Diff.GE.EvolB.rmPbound_B
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.EXT.SmConnVar
import Submission.Work.Diff.EXT.CovRicAux
import Submission.Work.Diff.Evol.covRic_eq_sum_covRm_fin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE.EvolB

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- `|rmP g x u b c d| ≤ √|Rm|² (√⟨u,u⟩ √⟨b,b⟩ √⟨c,c⟩ √⟨d,d⟩)`, at the smooth level. -/
theorem rmP_norm_le_B_sqrt [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) :
    ∀ (g : SMet I M) (x : M) (u b c d : TangentSpace I x),
      |rmP g x u b c d|
        ≤ Real.sqrt (rmNormSq g x)
          * (Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x b b)
             * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) := by
  intro g x u b c d
  have h := rmP_norm_le_B (I := I) (M := M) hLC g x u b c d
  simp only [nrm_eq_sqrt] at h
  calc |rmP g x u b c d|
      ≤ Real.sqrt (rmNormSq g x) * Real.sqrt ((g.inner x u) u) * Real.sqrt ((g.inner x b) b)
        * Real.sqrt ((g.inner x c) c) * Real.sqrt ((g.inner x d) d) := h
    _ = Real.sqrt (rmNormSq g x)
          * (Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x b b)
             * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) := by ring

/-! ## The pointwise curvature bound at the smooth level

The frozen interfaces (`SMet I M`, `LCSmooth I M`) live at the *smooth* level `IsManifold I ∞ M`,
whereas `Work.Diff.GE.rmP_norm_bound` is stated under the *analytic* hypothesis `IsManifold I ω M`
and hence is not applicable here.  Its auxiliary lemmas (`rmP_expansion`, `onFrame_parseval_sq`,
`sum4_coeff_sq_le`, ...) are all already at the smooth level, so the final argument is re-run below
with the smooth instance. -/

/-! ## Arithmetic core of the four-term estimate -/

/-- If four quantities `T₁,…,T₄` are bounded by `R` times a product of four nonnegative factors,
and in each product the factor sitting in the "variation" slot is bounded by `sC * D * (sv * s_i)`,
then the sum is bounded by `(4 * sC) * R * D * (sv * sa * sb * sc * sd)`. -/
theorem connVarFourArith
    (R D sC sv sa sb sc sd swa swb swc swd T1 T2 T3 T4 : ℝ)
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hsC : 0 ≤ sC) (hsv : 0 ≤ sv) (hsa : 0 ≤ sa)
    (hsb : 0 ≤ sb) (hsc : 0 ≤ sc) (hsd : 0 ≤ sd)
    (hwa : swa ≤ sC * D * (sv * sa)) (hwb : swb ≤ sC * D * (sv * sb))
    (hwc : swc ≤ sC * D * (sv * sc)) (hwd : swd ≤ sC * D * (sv * sd))
    (h1 : |T1| ≤ R * (swa * sb * sc * sd))
    (h2 : |T2| ≤ R * (sa * swb * sc * sd))
    (h3 : |T3| ≤ R * (sa * sb * swc * sd))
    (h4 : |T4| ≤ R * (sa * sb * sc * swd)) :
    |T1 + T2 + T3 + T4| ≤ (4 * sC) * R * D * (sv * sa * sb * sc * sd) := by
  have hz1 : 0 ≤ sb * sc * sd := mul_nonneg (mul_nonneg hsb hsc) hsd
  have hz2 : 0 ≤ sa * sc * sd := mul_nonneg (mul_nonneg hsa hsc) hsd
  have hz3 : 0 ≤ sa * sb * sd := mul_nonneg (mul_nonneg hsa hsb) hsd
  have hz4 : 0 ≤ sa * sb * sc := mul_nonneg (mul_nonneg hsa hsb) hsc
  have e1 : |T1| ≤ sC * R * D * (sv * sa * sb * sc * sd) := by
    calc |T1| ≤ R * (swa * sb * sc * sd) := h1
      _ = R * (swa * (sb * sc * sd)) := by ring
      _ ≤ R * ((sC * D * (sv * sa)) * (sb * sc * sd)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hwa hz1) hR
      _ = sC * R * D * (sv * sa * sb * sc * sd) := by ring
  have e2 : |T2| ≤ sC * R * D * (sv * sa * sb * sc * sd) := by
    calc |T2| ≤ R * (sa * swb * sc * sd) := h2
      _ = R * (swb * (sa * sc * sd)) := by ring
      _ ≤ R * ((sC * D * (sv * sb)) * (sa * sc * sd)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hwb hz2) hR
      _ = sC * R * D * (sv * sa * sb * sc * sd) := by ring
  have e3 : |T3| ≤ sC * R * D * (sv * sa * sb * sc * sd) := by
    calc |T3| ≤ R * (sa * sb * swc * sd) := h3
      _ = R * (swc * (sa * sb * sd)) := by ring
      _ ≤ R * ((sC * D * (sv * sc)) * (sa * sb * sd)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hwc hz3) hR
      _ = sC * R * D * (sv * sa * sb * sc * sd) := by ring
  have e4 : |T4| ≤ sC * R * D * (sv * sa * sb * sc * sd) := by
    calc |T4| ≤ R * (sa * sb * sc * swd) := h4
      _ = R * (swd * (sa * sb * sc)) := by ring
      _ ≤ R * ((sC * D * (sv * sd)) * (sa * sb * sc)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hwd hz4) hR
      _ = sC * R * D * (sv * sa * sb * sc * sd) := by ring
  have htri : |T1 + T2 + T3 + T4| ≤ |T1| + |T2| + |T3| + |T4| := by
    have h₁ := abs_add_le (T1 + T2 + T3) T4
    have h₂ := abs_add_le (T1 + T2) T3
    have h₃ := abs_add_le T1 T2
    linarith
  have hsum : |T1| + |T2| + |T3| + |T4| ≤ 4 * (sC * R * D * (sv * sa * sb * sc * sd)) := by
    linarith [e1, e2, e3, e4]
  calc |T1 + T2 + T3 + T4| ≤ |T1| + |T2| + |T3| + |T4| := htri
    _ ≤ 4 * (sC * R * D * (sv * sa * sb * sc * sd)) := hsum
    _ = (4 * sC) * R * D * (sv * sa * sb * sc * sd) := by ring

/-! ## The `⟨w,w⟩` bound for the connection variation

`IsConnVar G t x (smoothExt x u) (smoothExt x v) A` tests the characterising Koszul pairing against
`Z = smoothExt x A`; since `dtMet G t = -2 Ric(g(t))` along the flow, the pairing is
`-2(∇_u Ric)(v,A) - 2(∇_v Ric)(u,A) + 2(∇_A Ric)(u,v)`, and `covRic_bound_of_trace` bounds each
`(∇Ric)`-term by `n √|∇Rm|²` times the three metric norms.  The resulting `bA ≤ M √bA` is squared. -/

/-- `⟨A,A⟩ ≤ C |∇Rm|² ⟨u,u⟩⟨v,v⟩` for the connection-variation vector `A`. -/
theorem connVarInnerLe [I.Boundaryless] [T2Space M] [CompactSpace M] (hLC : LCSmooth I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M, ∀ u v : TangentSpace I x, ∀ A : TangentSpace I x,
        IsConnVar G t x (smoothExt x u) (smoothExt x v) A →
        (G t).inner x A A ≤ C * dRmNormSq (G t) x * ((G t).inner x u u * (G t).inner x v v) := by
  -- the contracted second Bianchi identity, in the chosen orthonormal frame
  have hsum : ∀ (g : SMet I M) (x : M) (v a b : TangentSpace I x),
      Work.Diff.Evol.covRic g x v a b
        = (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
            (fun m => covRm g x v (onFrame g x m) a (onFrame g x m) b) :=
    fun g x v a b =>
      Work.Diff.Evol.covRic_eq_sum_covRm_fin (I := I) (M := M) hLC g x (onFrame g x)
        (isONFrame_onFrame g x) v a b
  obtain ⟨C₀, hC₀, hbnd⟩ := Work.Diff.EXT.covRic_bound_of_trace (I := I) (M := M) hLC hsum
  refine ⟨9 * C₀ ^ 2, by positivity, ?_⟩
  intro G T hflow t ht x u v A hA
  -- `∂ₜ g = -2 Ric` at `t` (interior point of the flow interval)
  have hdtfun : dtMet G t = fun y p q => (-2 : ℝ) * ricAt (lcOf (G t)) y p q := by
    funext y p q
    exact Sm.dtMet_eq_ric_of_flow G T hflow t ht y p q
  -- on smooth extensions, the Koszul pairing with `∂ₜ g` is `-2 ∇Ric`
  have hId : ∀ a b c : TangentSpace I x,
      covDerivSym2 (lcOf (G t)) (dtMet G t) (smoothExt x a) (smoothExt x b) (smoothExt x c) x
        = -2 * Work.Diff.Evol.covRic (G t) x a b c := by
    intro a b c
    rw [hdtfun]
    rw [Sm.covDerivSym2_const_mul (lcOf (G t)) (-2)
      (fun z p q => ricAt (lcOf (G t)) z p q) (smoothExt x a) (smoothExt x b) (smoothExt x c) x]
    rw [Sm.covDerivSym2_ricAt_eq_dRicPhi (G t) x (smoothExt x a) (smoothExt x b)
      (smoothExt x c)]
    rw [smoothExt_apply x a, ← Work.Diff.Evol.covRic_eq_dRicPhi (G t) x a b c]
  -- test the characterising identity of `A` against the smooth extension of `A` itself
  have hpair := hA (smoothExt x A) (smoothExt_cmdiff x A)
  rw [smoothExt_apply x A] at hpair
  rw [hId u v A, hId v u A, hId A u v] at hpair
  have hS1 := hbnd (G t) x u v A
  have hS2 := hbnd (G t) x v u A
  have hS3 := hbnd (G t) x A u v
  have hD0 : 0 ≤ dRmNormSq (G t) x := Gest.dRmNormSq_nonneg (G t) x
  have hV0 : 0 ≤ (G t).inner x u u := Sm.smet_inner_self_nonneg (G t) x u
  have hW0 : 0 ≤ (G t).inner x v v := Sm.smet_inner_self_nonneg (G t) x v
  have hA0 : 0 ≤ (G t).inner x A A := Sm.smet_inner_self_nonneg (G t) x A
  have hmain : (G t).inner x A A
      ≤ 9 * C₀ ^ 2 * dRmNormSq (G t) x * (G t).inner x u u * (G t).inner x v v :=
    Sm.connVar_arith C₀ (dRmNormSq (G t) x) ((G t).inner x u u) ((G t).inner x v v)
      ((G t).inner x A A)
      (Work.Diff.Evol.covRic (G t) x u v A) (Work.Diff.Evol.covRic (G t) x v u A)
      (Work.Diff.Evol.covRic (G t) x A u v)
      hC₀ hD0 hV0 hW0 hA0 hS1 hS2 hS3 hpair
  calc (G t).inner x A A
      ≤ 9 * C₀ ^ 2 * dRmNormSq (G t) x * (G t).inner x u u * (G t).inner x v v := hmain
    _ = (9 * C₀ ^ 2) * dRmNormSq (G t) x * ((G t).inner x u u * (G t).inner x v v) := by ring

end Helpers

/-- Bound on the connection-variation term of the `∇Rm` evolution along a Ricci flow.  For
`t ∈ (0,T)` the vectors `wₐ = ∂ₜ(∇_v Aₐ)`, … at `x` (the derivative of the connection applied to the
fixed smooth fields `smoothExt x v`, `smoothExt x a`, …) are characterised by the `LCVariation`
pairing `IsConnVar G t x (smoothExt x v) (smoothExt x s) wₛ`, and their contribution to the evolution
of `covRm`, namely `Σ_s rmP (G t) x (… , wₛ , …)`, is bounded by a universal constant times
`|Rm| |∇Rm|` and the metric norms of the five vectors.  Proof route: `LCVariation` (`t ∈ Ioo 0 T`,
joint smoothness on an open interval provided by `jointSmooth_Ioo_of_Ico`) gives the `wₛ`; the
pairing is the Koszul combination of first derivatives of the Ricci tensor (`dtMet G t = −2 Ric` by
`IsRicciFlow`), bounded by `C|∇Rm|` through the contracted second Bianchi identity
(`Submission.Work.Diff.GE.connVar_bound` is the associated `⟨w,w⟩ ≤ C·dRmNormSq·‖V‖²‖W‖²` bound),
and `rmP` is bounded by `√rmNormSq` times the four vector norms
(`Submission.Work.Diff.GE.rmP_norm_bound`); combining the two for the four slots gives the stated
estimate with a constant independent of the flow. -/
theorem connectionVariation_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) (hLV : LCVariation I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M, ∀ v a b c d : TangentSpace I x,
        ∃ wa wb wc wd : TangentSpace I x,
          Work.Diff.GE.IsConnVar G t x (smoothExt x v) (smoothExt x a) wa ∧
          Work.Diff.GE.IsConnVar G t x (smoothExt x v) (smoothExt x b) wb ∧
          Work.Diff.GE.IsConnVar G t x (smoothExt x v) (smoothExt x c) wc ∧
          Work.Diff.GE.IsConnVar G t x (smoothExt x v) (smoothExt x d) wd ∧
          |rmP (G t) x wa b c d + rmP (G t) x a wb c d + rmP (G t) x a b wc d
             + rmP (G t) x a b c wd| ≤
            C * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
              * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
                * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
                * Real.sqrt ((G t).inner x d d)) := by
  obtain ⟨C₀, hC₀, hbnd⟩ := connVarInnerLe (I := I) (M := M) hLC
  refine ⟨4 * Real.sqrt C₀, by positivity, ?_⟩
  intro G T hflow t ht x v a b c d
  have hGs : JointSmooth G (Set.Ioo 0 T) := Sm.jointSmooth_Ioo_of_Ico G T hflow.1
  -- the four connection-variation vectors, from the first-variation contract
  obtain ⟨wa, -, hwaP⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo hGs t ht
    (smoothExt x v) (smoothExt x a) (smoothExt_cmdiff x v) (smoothExt_cmdiff x a) x
  obtain ⟨wb, -, hwbP⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo hGs t ht
    (smoothExt x v) (smoothExt x b) (smoothExt_cmdiff x v) (smoothExt_cmdiff x b) x
  obtain ⟨wc, -, hwcP⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo hGs t ht
    (smoothExt x v) (smoothExt x c) (smoothExt_cmdiff x v) (smoothExt_cmdiff x c) x
  obtain ⟨wd, -, hwdP⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo hGs t ht
    (smoothExt x v) (smoothExt x d) (smoothExt_cmdiff x v) (smoothExt_cmdiff x d) x
  refine ⟨wa, wb, wc, wd, hwaP, hwbP, hwcP, hwdP, ?_⟩
  -- the `⟨w,w⟩` bounds
  have hwa := hbnd G T hflow t ht x v a wa hwaP
  have hwb := hbnd G T hflow t ht x v b wb hwbP
  have hwc := hbnd G T hflow t ht x v c wc hwcP
  have hwd := hbnd G T hflow t ht x v d wd hwdP
  -- nonnegativity
  have hD0 : 0 ≤ dRmNormSq (G t) x := Gest.dRmNormSq_nonneg (G t) x
  have hv0 : 0 ≤ (G t).inner x v v := Sm.smet_inner_self_nonneg (G t) x v
  -- the square-root bounds on the four variation vectors
  have hwaS : Real.sqrt ((G t).inner x wa wa)
      ≤ Real.sqrt C₀ * Real.sqrt (dRmNormSq (G t) x)
        * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)) := by
    calc Real.sqrt ((G t).inner x wa wa)
        ≤ Real.sqrt (C₀ * dRmNormSq (G t) x * ((G t).inner x v v * (G t).inner x a a)) :=
          Real.sqrt_le_sqrt hwa
      _ = Real.sqrt (C₀ * dRmNormSq (G t) x)
            * Real.sqrt ((G t).inner x v v * (G t).inner x a a) :=
          Real.sqrt_mul (mul_nonneg hC₀ hD0) _
      _ = Real.sqrt C₀ * Real.sqrt (dRmNormSq (G t) x)
            * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)) := by
          rw [Real.sqrt_mul hC₀, Real.sqrt_mul hv0]
  have hwbS : Real.sqrt ((G t).inner x wb wb)
      ≤ Real.sqrt C₀ * Real.sqrt (dRmNormSq (G t) x)
        * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x b b)) := by
    calc Real.sqrt ((G t).inner x wb wb)
        ≤ Real.sqrt (C₀ * dRmNormSq (G t) x * ((G t).inner x v v * (G t).inner x b b)) :=
          Real.sqrt_le_sqrt hwb
      _ = Real.sqrt (C₀ * dRmNormSq (G t) x)
            * Real.sqrt ((G t).inner x v v * (G t).inner x b b) :=
          Real.sqrt_mul (mul_nonneg hC₀ hD0) _
      _ = Real.sqrt C₀ * Real.sqrt (dRmNormSq (G t) x)
            * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x b b)) := by
          rw [Real.sqrt_mul hC₀, Real.sqrt_mul hv0]
  have hwcS : Real.sqrt ((G t).inner x wc wc)
      ≤ Real.sqrt C₀ * Real.sqrt (dRmNormSq (G t) x)
        * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x c c)) := by
    calc Real.sqrt ((G t).inner x wc wc)
        ≤ Real.sqrt (C₀ * dRmNormSq (G t) x * ((G t).inner x v v * (G t).inner x c c)) :=
          Real.sqrt_le_sqrt hwc
      _ = Real.sqrt (C₀ * dRmNormSq (G t) x)
            * Real.sqrt ((G t).inner x v v * (G t).inner x c c) :=
          Real.sqrt_mul (mul_nonneg hC₀ hD0) _
      _ = Real.sqrt C₀ * Real.sqrt (dRmNormSq (G t) x)
            * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x c c)) := by
          rw [Real.sqrt_mul hC₀, Real.sqrt_mul hv0]
  have hwdS : Real.sqrt ((G t).inner x wd wd)
      ≤ Real.sqrt C₀ * Real.sqrt (dRmNormSq (G t) x)
        * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x d d)) := by
    calc Real.sqrt ((G t).inner x wd wd)
        ≤ Real.sqrt (C₀ * dRmNormSq (G t) x * ((G t).inner x v v * (G t).inner x d d)) :=
          Real.sqrt_le_sqrt hwd
      _ = Real.sqrt (C₀ * dRmNormSq (G t) x)
            * Real.sqrt ((G t).inner x v v * (G t).inner x d d) :=
          Real.sqrt_mul (mul_nonneg hC₀ hD0) _
      _ = Real.sqrt C₀ * Real.sqrt (dRmNormSq (G t) x)
            * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x d d)) := by
          rw [Real.sqrt_mul hC₀, Real.sqrt_mul hv0]
  -- the four `rmP` bounds
  have h1 := rmP_norm_le_B_sqrt (I := I) (M := M) hLC (G t) x wa b c d
  have h2 := rmP_norm_le_B_sqrt (I := I) (M := M) hLC (G t) x a wb c d
  have h3 := rmP_norm_le_B_sqrt (I := I) (M := M) hLC (G t) x a b wc d
  have h4 := rmP_norm_le_B_sqrt (I := I) (M := M) hLC (G t) x a b c wd
  exact connVarFourArith (Real.sqrt (rmNormSq (G t) x)) (Real.sqrt (dRmNormSq (G t) x))
    (Real.sqrt C₀)
    (Real.sqrt ((G t).inner x v v)) (Real.sqrt ((G t).inner x a a))
    (Real.sqrt ((G t).inner x b b)) (Real.sqrt ((G t).inner x c c))
    (Real.sqrt ((G t).inner x d d))
    (Real.sqrt ((G t).inner x wa wa)) (Real.sqrt ((G t).inner x wb wb))
    (Real.sqrt ((G t).inner x wc wc)) (Real.sqrt ((G t).inner x wd wd))
    (rmP (G t) x wa b c d) (rmP (G t) x a wb c d) (rmP (G t) x a b wc d)
    (rmP (G t) x a b c wd)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hwaS hwbS hwcS hwdS h1 h2 h3 h4

end Work.Diff.GE.EvolB
