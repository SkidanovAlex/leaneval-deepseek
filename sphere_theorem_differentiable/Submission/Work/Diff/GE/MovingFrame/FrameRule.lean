import Mathlib
import Submission.Work.Diff.GE.MovingFrame.Defs
import Submission.Work.Diff.GE.MovingFrame.covRm5_multilinear
import Submission.Work.Diff.GE.MovingFrame.isONFrame_at_of_eventually

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Work.Diff.GE.MovingFrame

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Elementary facts about the norms occurring in the estimate -/

theorem rmNormSq_nonneg (g : SMet I M) (x : M) : 0 ≤ rmNormSq g x := by
  rw [rmNormSq, Submission.Diff.Alg.frobSq]
  positivity

theorem dRmNormSq_nonneg (g : SMet I M) (x : M) : 0 ≤ dRmNormSq g x := by
  rw [dRmNormSq]
  positivity

theorem sqrt_le_one_add_of_nonneg {K : ℝ} (hK : 0 ≤ K) : Real.sqrt K ≤ 1 + K := by
  nlinarith [Real.sq_sqrt hK, Real.sqrt_nonneg K]

/-- The product of the `g`-norms of a tuple all of whose *diagonal* entries are unit vectors is `1`.
(No orthonormality of the tuple is needed, only the diagonal entries.) -/
theorem argNorms_eq_one_of_diag (g : SMet I M) (x : M) (w : Fin 5 → TangentSpace I x)
    (hw : ∀ p, g.inner x (w p) (w p) = 1) : argNorms g x w = 1 := by
  rw [argNorms]
  refine Finset.prod_eq_one fun p _ => ?_
  rw [hw p, Real.sqrt_one]

/-- The `argNorms` of a tuple which differs from a tuple with unit diagonal entries in the slot
`p`. -/
theorem argNorms_update_eq_of_diag (g : SMet I M) (x : M) (w : Fin 5 → TangentSpace I x)
    (hw : ∀ p, g.inner x (w p) (w p) = 1) (p : Fin 5) (v : TangentSpace I x) :
    argNorms g x (Function.update w p v) = Real.sqrt ((g.inner x v v)) := by
  rw [argNorms, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p)]
  have h1 : (∏ x_1 ∈ Finset.univ.erase p,
      Real.sqrt ((g.inner x (Function.update w p v x_1) (Function.update w p v x_1)))) = 1 := by
    refine Finset.prod_eq_one fun q hq => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hq), hw q, Real.sqrt_one]
  rw [h1, mul_one, Function.update_self]

/-! ## The product rule for `∇Rm` in a moving frame

Given the fixed-vector estimate with constant `C'`, the components of `∇Rm` in a family of frames
which is orthonormal at time `t` and differentiable with derivative `edot` at `t` differentiate at
`t`, and their derivative is bounded by the same rough Laplacian plus `(C' + 5)(1+K)|Rm||∇Rm|`.

The extra `5(1+K)|Rm||∇Rm|` comes from the five frame-slot terms produced by the multilinearity of
`∇Rm` in its five vector arguments. -/
theorem frame_of_fixed
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M)
    (G : ℝ → SMet I M) (T t : ℝ) (hRic : IsRicciFlow G T) (ht : t ∈ Set.Ico 0 T) (x : M)
    (e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I x)
    (edot : Fin (Module.finrank ℝ E) → TangentSpace I x) (K : ℝ) (hK : 0 ≤ K)
    (hON : ∀ᶠ s in 𝓝[Set.Ico 0 T] t, IsONFrame (G s) x (e s))
    (hed : ∀ i, HasDerivWithinAt (fun s ↦ e s i) (edot i) (Set.Ico 0 T) t)
    (hKb : ∀ i, (G t).inner x (edot i) (edot i) ≤ K * rmNormSq (G t) x)
    (C' : ℝ) (hC' : 0 ≤ C')
    (A : SMet I M → ContinuousMultilinearMap ℝ (fun _ : Fin 5 => TangentSpace I x) ℝ)
    (hAeval : ∀ (g : SMet I M) (w : Fin 5 → TangentSpace I x), A g w = covRm5 g x w)
    (hAbound : ∀ (g : SMet I M) (w : Fin 5 → TangentSpace I x),
      |A g w| ≤ dRmNorm g x * argNorms g x w)
    (hApply : ∀ (Φ : ℝ → MultilinearMap ℝ (fun _ : Fin 5 => TangentSpace I x) ℝ)
        (L : (Fin 5 → TangentSpace I x) → ℝ) (u : ℝ → Fin 5 → TangentSpace I x)
        (u₀ : Fin 5 → TangentSpace I x) {l : Filter ℝ},
      (∀ w : Fin 5 → TangentSpace I x, Tendsto (fun s => Φ s w) l (𝓝 (L w))) →
        Tendsto u l (𝓝 u₀) → Tendsto (fun s => Φ s (u s)) l (𝓝 (L u₀)))
    (hFix : ∀ w : Fin 5 → TangentSpace I x,
      ∃ D : ℝ, HasDerivWithinAt (fun s ↦ covRm5 (G s) x w) D (Set.Ico 0 T) t ∧
        D ≤ lapCovRmAt5 (G t) x w
          + C' * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
              * argNorms (G t) x w) :
    ∀ m i j k l : Fin (Module.finrank ℝ E), ∃ D : ℝ,
      HasDerivWithinAt
        (fun s ↦ covRm (G s) x (e s m) (e s i) (e s j) (e s k) (e s l)) D (Set.Ico 0 T) t ∧
      D ≤ lapCovRmAt (G t) x (e t m) (e t i) (e t j) (e t k) (e t l)
          + (C' + 5) * (1 + K) * Real.sqrt (rmNormSq (G t) x)
              * Real.sqrt (dRmNormSq (G t) x) := by
  classical
  -- the model-space structure on the tangent space (`TangentSpace I x` is a type synonym for `E`,
  -- which type class inference does not unfold)
  letI hNAG : NormedAddCommGroup (TangentSpace I x) :=
    (inferInstanceAs (NormedAddCommGroup E) : NormedAddCommGroup E)
  letI hNS : NormedSpace ℝ (TangentSpace I x) :=
    (inferInstanceAs (NormedSpace ℝ E) : NormedSpace ℝ E)
  letI hFD : FiniteDimensional ℝ (TangentSpace I x) :=
    (inferInstanceAs (FiniteDimensional ℝ E) : FiniteDimensional ℝ E)
  -- the frame is orthonormal at time `t`
  have het : IsONFrame (G t) x (e t) :=
    isONFrame_at_of_eventually G T t hRic ht x e (fun i => (hed i).continuousWithinAt) hON
  -- the fixed-vector derivatives
  choose Dfix hD using hFix
  have hDfix : ∀ w : Fin 5 → TangentSpace I x,
      HasDerivWithinAt (fun s ↦ covRm5 (G s) x w) (Dfix w) (Set.Ico 0 T) t :=
    fun w => (hD w).1
  have hDfixle : ∀ w : Fin 5 → TangentSpace I x,
      Dfix w ≤ lapCovRmAt5 (G t) x w
        + C' * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x) * argNorms (G t) x w :=
    fun w => (hD w).2
  intro m i j k l
  -- the index tuple and the moving frame tuple
  let idx : Fin 5 → Fin (Module.finrank ℝ E) := frameIndex m i j k l
  let W : ℝ → Fin 5 → TangentSpace I x := fun s p => e s (idx p)
  let et : Fin 5 → TangentSpace I x := fun p => e t (idx p)
  let ed : Fin 5 → TangentSpace I x := fun p => edot (idx p)
  -- the diagonal entries of the frame at `t` are unit vectors
  have hdiag : ∀ p : Fin 5, (G t).inner x (et p) (et p) = 1 := by
    intro p
    have h := het (idx p) (idx p)
    simpa [et] using h
  -- ## Step 1: differentiability of the frame curve
  have hWderiv : HasDerivWithinAt W ed (Set.Ico 0 T) t := by
    have h : HasDerivWithinAt (fun s => fun p => e s (idx p)) (fun p => edot (idx p))
        (Set.Ico 0 T) t :=
      (hasDerivWithinAt_pi).mpr (fun p => hed (idx p))
    simpa only [W, ed] using h
  -- ## Step 2: the "frozen" part
  have hFrozen : HasDerivWithinAt (fun s => A (G t) (W s))
      (∑ p : Fin 5, A (G t) (Function.update et p (ed p))) (Set.Ico 0 T) t := by
    have hML : HasFDerivAt (fun w : Fin 5 → TangentSpace I x => A (G t) w)
        ((A (G t)).linearDeriv et) et := (A (G t)).hasFDerivAt et
    have hWf : HasFDerivWithinAt W (ContinuousLinearMap.toSpanSingleton ℝ ed)
        (Set.Ico 0 T) t := hWderiv.hasFDerivWithinAt
    have hcomp : HasFDerivWithinAt (fun s => A (G t) (W s))
        (((A (G t)).linearDeriv et) ∘SL (ContinuousLinearMap.toSpanSingleton ℝ ed))
        (Set.Ico 0 T) t :=
      hML.hasFDerivWithinAt.comp t hWf (fun y _ => Set.mem_univ _)
    have hder := hcomp.hasDerivWithinAt
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply_one,
      ContinuousMultilinearMap.linearDeriv_apply] at hder
    exact hder
  -- ## Step 3: the difference quotient form
  let Ψfun : ℝ → (Fin 5 → TangentSpace I x) → ℝ :=
    fun s w => (s - t)⁻¹ * (covRm5 (G s) x w - covRm5 (G t) x w)
  have hΨmulti : ∀ s : ℝ, IsMulti5 (TangentSpace I x) (Ψfun s) := by
    intro s
    have h1 := covRm5_multilinear (I := I) hLC (G s) x
    have h2 := covRm5_multilinear (I := I) hLC (G t) x
    constructor
    · intro w p a b
      simp only [Ψfun, h1.1 w p a b, h2.1 w p a b]
      ring
    · intro w p c a
      simp only [Ψfun, h1.2 w p c a, h2.2 w p c a]
      ring
  let Ψ : ℝ → MultilinearMap ℝ (fun _ : Fin 5 => TangentSpace I x) ℝ := fun s =>
    MultilinearMap.mk' (Ψfun s) (fun w p a b => (hΨmulti s).1 w p a b)
      (fun w p c a => by simpa only [smul_eq_mul] using (hΨmulti s).2 w p c a)
  have hΨeval : ∀ (s : ℝ) (w : Fin 5 → TangentSpace I x), Ψ s w = Ψfun s w := fun s w => rfl
  -- ## Step 4: pointwise convergence of `Ψ`
  have hΨtend : ∀ w : Fin 5 → TangentSpace I x,
      Tendsto (fun s => Ψ s w) (𝓝[Set.Ico 0 T \ {t}] t) (𝓝 (Dfix w)) := by
    intro w
    have hslope := (hasDerivWithinAt_iff_tendsto_slope).mp (hDfix w)
    refine hslope.congr' (Filter.Eventually.of_forall fun s => ?_)
    change slope (fun s => covRm5 (G s) x w) t s = Ψfun s w
    simp only [slope, Ψfun, smul_eq_mul, vsub_eq_sub]
  -- ## Step 5: the frame curve converges
  have hWtend : Tendsto W (𝓝[Set.Ico 0 T \ {t}] t) (𝓝 et) := by
    have hc : Tendsto W (𝓝[Set.Ico 0 T] t) (𝓝 (W t)) := hWderiv.continuousWithinAt
    have hle : 𝓝[Set.Ico 0 T \ {t}] t ≤ 𝓝[Set.Ico 0 T] t :=
      nhdsWithin_mono t (Set.sdiff_subset : Set.Ico 0 T \ {t} ⊆ Set.Ico 0 T)
    have h2 : Tendsto W (𝓝[Set.Ico 0 T \ {t}] t) (𝓝 (W t)) := hc.mono_left hle
    simpa only [W, et] using h2
  -- ## Step 6: the value limit, and the resulting differentiability of the error term
  have hΨW : Tendsto (fun s => Ψ s (W s)) (𝓝[Set.Ico 0 T \ {t}] t) (𝓝 (Dfix et)) :=
    hApply Ψ (fun w => Dfix w) W et (l := 𝓝[Set.Ico 0 T \ {t}] t) hΨtend hWtend
  have hErr : HasDerivWithinAt (fun s => A (G s) (W s) - A (G t) (W s)) (Dfix et)
      (Set.Ico 0 T) t := by
    rw [hasDerivWithinAt_iff_tendsto_slope]
    refine hΨW.congr' (Filter.Eventually.of_forall fun s => ?_)
    change Ψ s (W s) = slope (fun s => A (G s) (W s) - A (G t) (W s)) t s
    simp only [slope, Ψ, MultilinearMap.mk'_apply, Ψfun, smul_eq_mul, vsub_eq_sub, sub_self,
      sub_zero, hAeval]
  -- ## Step 7: add the two parts
  have hTotal : HasDerivWithinAt (fun s => A (G s) (W s))
      (Dfix et + ∑ p : Fin 5, A (G t) (Function.update et p (ed p))) (Set.Ico 0 T) t := by
    refine (hErr.add hFrozen).congr (fun y _ => ?_) ?_ <;>
      simp only [Pi.add_apply, sub_add_cancel]
  -- ## Step 8: the bound
  set R : ℝ := Real.sqrt (rmNormSq (G t) x) with hR
  set Rn : ℝ := Real.sqrt (dRmNormSq (G t) x) with hRn
  have hR0 : 0 ≤ R := by rw [hR]; exact Real.sqrt_nonneg _
  have hRn0 : 0 ≤ Rn := by rw [hRn]; exact Real.sqrt_nonneg _
  -- the fixed part
  have h1 : Dfix et ≤ lapCovRmAt5 (G t) x et + C' * R * Rn := by
    have h := hDfixle et
    rw [argNorms_eq_one_of_diag (G t) x et hdiag, mul_one] at h
    simpa only [hR, hRn] using h
  -- the frame-motion part
  have h2 : (∑ p : Fin 5, A (G t) (Function.update et p (ed p))) ≤ 5 * (1 + K) * R * Rn := by
    have hbd : ∀ p : Fin 5,
        A (G t) (Function.update et p (ed p)) ≤ Rn * Real.sqrt ((G t).inner x (ed p) (ed p)) := by
      intro p
      have h := hAbound (G t) (Function.update et p (ed p))
      rw [argNorms_update_eq_of_diag (G t) x et hdiag p (ed p), dRmNorm] at h
      exact le_trans (le_abs_self _) (by simpa only [hRn] using h)
    have hterm : ∀ p : Fin 5,
        Real.sqrt ((G t).inner x (ed p) (ed p)) ≤ Real.sqrt K * R := by
      intro p
      have hle : (G t).inner x (ed p) (ed p) ≤ K * rmNormSq (G t) x := by
        simpa only [ed] using hKb (idx p)
      calc Real.sqrt ((G t).inner x (ed p) (ed p))
          ≤ Real.sqrt (K * rmNormSq (G t) x) := Real.sqrt_le_sqrt hle
        _ = Real.sqrt K * R := by rw [Real.sqrt_mul hK, hR]
    have h5 : (∑ p : Fin 5, Real.sqrt ((G t).inner x (ed p) (ed p))) ≤ 5 * (Real.sqrt K * R) := by
      calc (∑ p : Fin 5, Real.sqrt ((G t).inner x (ed p) (ed p)))
          ≤ ∑ _p : Fin 5, (Real.sqrt K * R) := Finset.sum_le_sum fun p _ => hterm p
        _ = 5 * (Real.sqrt K * R) := by
              simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc (∑ p : Fin 5, A (G t) (Function.update et p (ed p)))
        ≤ ∑ p : Fin 5, Rn * Real.sqrt ((G t).inner x (ed p) (ed p)) :=
          Finset.sum_le_sum fun p _ => hbd p
      _ = Rn * ∑ p : Fin 5, Real.sqrt ((G t).inner x (ed p) (ed p)) := by
          rw [Finset.mul_sum]
      _ ≤ Rn * (5 * (Real.sqrt K * R)) := mul_le_mul_of_nonneg_left h5 hRn0
      _ ≤ 5 * (1 + K) * R * Rn := by
          have hsk : Real.sqrt K ≤ 1 + K := sqrt_le_one_add_of_nonneg hK
          have h0 : (0:ℝ) ≤ 5 * (R * Rn) :=
            mul_nonneg (by norm_num) (mul_nonneg hR0 hRn0)
          nlinarith [mul_le_mul_of_nonneg_left hsk h0]
  have h3 : C' * R * Rn ≤ C' * (1 + K) * R * Rn := by
    have h1 : (1:ℝ) ≤ 1 + K := by linarith
    have h0 : (0:ℝ) ≤ C' * (R * Rn) := mul_nonneg hC' (mul_nonneg hR0 hRn0)
    nlinarith [mul_le_mul_of_nonneg_left h1 h0]
  -- ## Step 9: the conclusion
  refine ⟨Dfix et + ∑ p : Fin 5, A (G t) (Function.update et p (ed p)), ?_, ?_⟩
  · -- differentiability, with the function written in the target form
    refine hTotal.congr (fun y _ => ?_) ?_
    · simp only [W, idx, frameIndex_zero, frameIndex_one, frameIndex_two, frameIndex_three,
        frameIndex_four, hAeval, covRm5]
    · simp only [W, idx, frameIndex_zero, frameIndex_one, frameIndex_two, frameIndex_three,
        frameIndex_four, hAeval, covRm5]
  · -- the estimate
    calc Dfix et + ∑ p : Fin 5, A (G t) (Function.update et p (ed p))
        ≤ (lapCovRmAt5 (G t) x et + C' * R * Rn) + 5 * (1 + K) * R * Rn := add_le_add h1 h2
      _ ≤ (lapCovRmAt5 (G t) x et + C' * (1 + K) * R * Rn) + 5 * (1 + K) * R * Rn := by
          linarith [h3]
      _ = lapCovRmAt (G t) x (e t m) (e t i) (e t j) (e t k) (e t l)
            + (C' + 5) * (1 + K) * Real.sqrt (rmNormSq (G t) x)
                * Real.sqrt (dRmNormSq (G t) x) := by
          simp only [lapCovRmAt5, et, idx, frameIndex_zero, frameIndex_one, frameIndex_two,
            frameIndex_three, frameIndex_four, hR, hRn]
          ring

