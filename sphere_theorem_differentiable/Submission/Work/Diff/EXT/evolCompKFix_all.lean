import Mathlib
import Submission.Work.Diff.EXT.evolKDefs
import Submission.Work.Diff.EXT.evolK_bridges
import Submission.Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.EXT.covKRmExt_antisymm_pair1
import Submission.Work.Diff.EXT.lapCovKRm_one_eq_lapCovRmAt
import Submission.Work.Diff.EXT.covKRm_expand_packed
import Submission.Work.Diff.EXT.covK_valueDep
import Submission.Work.Diff.EXT.evolCompKFixReactDefs
import Submission.Work.Diff.EXT.evolX.covRm_fixed_le
import Submission.Work.Diff.T.lc_variation
import Submission.Work.Diff.EXT.covK_familySmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-!
# The fixed-vector componentwise evolution of `∇^k Rm` (second formulation of the analytic core)

`Work.Diff.EXT.EvolCompKFix k` (`Submission/Work/Diff/EXT/evolKDefs.lean`) states, for fixed tangent
vectors, that every component of `∇^k Rm` has a right derivative along a Ricci flow, bounded by the
corresponding component of the rough Laplacian plus
`C (1 + Σ_{j<k} f_j) (1 + √f_k) · Pn (G t)-norms of the vectors`.

It is the *frame-free* form of the componentwise estimate `Work.Diff.EXT.EvolCompK k` (whose bound
carries `(1+K')` for a moving frame with velocity `K'|Rm|²`), and it is the natural target for the
classical computation: in fixed vectors the `s`-dependence is only through the metric,

  `∂ₜ(∇^k Rm) = Δ(∇^k Rm) + R_k`,  `|R_k| ≤ C_k Σ_{i+j=k}|∇^iRm| |∇^jRm|`,

so that `|R_k| ≤ C_k (1+Σ_{j<k}f_j)(1+√f_k)` because `2√(f_i f_j) ≤ f_i + f_j`; the `−2|∇^{k+1}Rm|²`
of the exact identity is dropped, and Clairaut (`Work.Diff.GE.hasDerivAt_mvfderiv`) applies
directly, with no frame bookkeeping and no `Classical.epsilon`-extension bookkeeping beyond the
value-dependence `Work.Diff.EXT.covKRmExt_locality`.

The `k = 1` case follows from the GE-area `Work.Diff.GE.hasDerivWithinAt_covRm_le` /
`covRm_frame_evol_abs` through the dictionary of `Submission/Work/Diff/EXT/evolK_bridges.lean` and
`Work.Diff.EXT.lapCovKRm_one_eq_lapCovRmAt`.  The induction step `k → k+1` differentiates the
defining recursion of `covKRmExt` at level `k+1`: with `R_k = ∂ₜ∇^kRm − Δ∇^kRm` it gives
`R_{k+1} = ∇R_k + [Ricci-identity commutator] + (∂ₜ∇)-terms`, where `∂ₜ∇` is the first variation of
the connection (`LCVariation`); the bounds follow from the explicit form of `R_k` by induction on
`k` — note that this *explicit* form (not merely the bound `|R_k| ≤ ⋯`) is what makes the step work,
since `R_k` must be differentiated in space, whence the induction has to carry "identity with
explicit reaction + bounds".

## Contents of this file (status)

This file contains the *reduction* of `evolCompKFix_all` to the classical inputs, together with the
elementary estimates that the reduction needs.  The two inputs that are not available in the
workspace yet are isolated as explicit hypotheses of
`Work.Diff.EXT.evolCompKFix_one_of` and `Work.Diff.EXT.evolCompKFix_of_reaction`:

* the `k = 1` *fixed-vector* evolution estimate (`Work.Diff.GE.hasDerivWithinAt_covRm_le`, whose
  proof is being assembled in the GE area) together with the Laplacian dictionary
  `Work.Diff.EXT.lapCovKRm_one_eq_lapCovRmAt` — this gives `EvolCompKFix 1`;
* for `k ≥ 2`, the *explicit* evolution identity with the classical reaction shape
  `R_k = Σ_{i+j=k} ∇^iRm ∗ ∇^jRm` together with its bound `|R_k| ≤ C(1+Σ_{j<k}f_j)(1+√f_k)Pn‖·‖`;
  the arithmetic that turns the classical reaction shape `Σ_{i+j=k}√(f_i f_j)` into the bound of
  `EvolCompKFix k` is proved below (`sum_sqrt_le`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Elementary real estimates -/

/-- `√x ≤ 1 + x` for `x ≥ 0`. -/
theorem sqrt_le_one_add {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ 1 + x := by
  nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x]

/-- The elementary kernel of the final arithmetic step: `√f₀ √f₁ ≤ (1+f₀)(1+√f₁)`. -/
theorem sqrt_mul_sqrt_le {f₀ f₁ : ℝ} (h₀ : 0 ≤ f₀) :
    Real.sqrt f₀ * Real.sqrt f₁ ≤ (1 + f₀) * (1 + Real.sqrt f₁) := by
  have h₁ : Real.sqrt f₁ ≤ 1 + Real.sqrt f₁ := by linarith [Real.sqrt_nonneg f₁]
  have h₀' : Real.sqrt f₀ ≤ 1 + f₀ := sqrt_le_one_add h₀
  have h₁' : (0 : ℝ) ≤ 1 + Real.sqrt f₁ := by linarith [Real.sqrt_nonneg f₁]
  exact mul_le_mul h₀' h₁ (Real.sqrt_nonneg f₁) (by linarith)

/-- The classical reaction shape `Σ_{i+j=k} √(f_i f_j)` is dominated by the bound of
`EvolCompKFix k`: for `k ≥ 1` and `f ≥ 0`,

  `Σ_{i ∈ range (k+1)} √(f i) √(f (k-i)) ≤ (k+1) (1 + Σ_{j<k} f j) (1 + √(f k))`.

This is the arithmetic content of "`2√(f_i f_j) ≤ f_i + f_j`" spelled out for the induction. -/
theorem sum_sqrt_le (k : ℕ) (hk : 1 ≤ k) (f : ℕ → ℝ) (hf : ∀ i ≤ k, 0 ≤ f i) :
    (∑ i ∈ Finset.range (k + 1), Real.sqrt (f i) * Real.sqrt (f (k - i)))
      ≤ (k + 1 : ℝ) * (1 + ∑ j ∈ Finset.range k, f j) * (1 + Real.sqrt (f k)) := by
  set S : ℝ := ∑ j ∈ Finset.range k, f j with hSdef
  have hSnonneg : 0 ≤ S :=
    Finset.sum_nonneg (fun j hj => hf j (Finset.mem_range.mp hj).le)
  have hS1 : 0 ≤ 1 + S := by linarith
  have hmem0 : (0 : ℕ) ∈ Finset.range k := Finset.mem_range.mpr hk
  have hf0S : f 0 ≤ S :=
    Finset.single_le_sum (fun j hj => hf j (Finset.mem_range.mp hj).le) hmem0
  have hsk : 0 ≤ Real.sqrt (f k) := Real.sqrt_nonneg _
  have hbound : ∀ i ∈ Finset.range (k + 1),
      Real.sqrt (f i) * Real.sqrt (f (k - i)) ≤ (1 + S) * (1 + Real.sqrt (f k)) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hfi : 0 ≤ f i := hf i hik
    have hfki : 0 ≤ f (k - i) := hf (k - i) (Nat.sub_le k i)
    have htarget : S ≤ (1 + S) * (1 + Real.sqrt (f k)) := by nlinarith
    rcases eq_or_ne i 0 with hi0 | hi0
    · subst hi0
      rw [Nat.sub_zero]
      have h1 : Real.sqrt (f 0) ≤ 1 + f 0 := sqrt_le_one_add (hf 0 (by omega))
      have h3 : (1 + f 0) * Real.sqrt (f k) ≤ (1 + S) * (1 + Real.sqrt (f k)) := by
        have h4 : f 0 * Real.sqrt (f k) ≤ S * Real.sqrt (f k) :=
          mul_le_mul_of_nonneg_right hf0S hsk
        have h5 : S * Real.sqrt (f k) ≤ (1 + S) * (1 + Real.sqrt (f k)) := by nlinarith
        nlinarith
      exact le_trans (mul_le_mul_of_nonneg_right h1 hsk) h3
    · rcases eq_or_ne i k with hik' | hik''
      · rw [hik', Nat.sub_self]
        have h1 : Real.sqrt (f 0) ≤ 1 + f 0 := sqrt_le_one_add (hf 0 (by omega))
        have h3 : Real.sqrt (f k) * (1 + f 0) ≤ (1 + S) * (1 + Real.sqrt (f k)) := by
          have h4 : f 0 * Real.sqrt (f k) ≤ S * Real.sqrt (f k) :=
            mul_le_mul_of_nonneg_right hf0S hsk
          have h5 : S * Real.sqrt (f k) ≤ (1 + S) * (1 + Real.sqrt (f k)) := by nlinarith
          nlinarith
        exact le_trans (mul_le_mul_of_nonneg_left h1 hsk) h3
      · have hik_ : i < k := lt_of_le_of_ne hik hik''
        have hmemi : i ∈ Finset.range k := Finset.mem_range.mpr hik_
        have hmemj : k - i ∈ Finset.range k := Finset.mem_range.mpr (by omega)
        have hlei : f i ≤ S :=
          Finset.single_le_sum (fun j hj => hf j (Finset.mem_range.mp hj).le) hmemi
        have hlej : f (k - i) ≤ S :=
          Finset.single_le_sum (fun j hj => hf j (Finset.mem_range.mp hj).le) hmemj
        have hamgm : 2 * (Real.sqrt (f i) * Real.sqrt (f (k - i))) ≤ f i + f (k - i) := by
          have h := sq_nonneg (Real.sqrt (f i) - Real.sqrt (f (k - i)))
          rw [sub_sq, Real.sq_sqrt hfi, Real.sq_sqrt hfki] at h
          linarith
        have hstep : Real.sqrt (f i) * Real.sqrt (f (k - i)) ≤ S := by linarith
        exact le_trans hstep htarget
  calc (∑ i ∈ Finset.range (k + 1), Real.sqrt (f i) * Real.sqrt (f (k - i)))
      ≤ ∑ _i ∈ Finset.range (k + 1), (1 + S) * (1 + Real.sqrt (f k)) :=
        Finset.sum_le_sum hbound
    _ = (k + 1 : ℝ) * (1 + S) * (1 + Real.sqrt (f k)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        ring
    _ = (k + 1 : ℝ) * (1 + ∑ j ∈ Finset.range k, f j) * (1 + Real.sqrt (f k)) := by
        rw [hSdef]

/-- Nonnegativity of the metric pairing of a vector with itself. -/
theorem smet_inner_self_nonneg (g : SMet I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with h | h
  · subst h; simp
  · exact le_of_lt (g.pos x v h)

/-- `|Rm|² ≥ 0`. -/
theorem rmNormSq_nonneg' (g : SMet I M) (x : M) : 0 ≤ rmNormSq g x := by
  rw [Submission.Diff.rmNormSq, Submission.Diff.Alg.frobSq]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
    Finset.sum_nonneg fun l _ => sq_nonneg _

/-- `|∇Rm|² ≥ 0`. -/
theorem dRmNormSq_nonneg' (g : SMet I M) (x : M) : 0 ≤ dRmNormSq g x := by
  rw [Submission.Diff.dRmNormSq]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
    Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun m _ => sq_nonneg _


/-! ## The `k = 1` case, from the GE-area fixed-vector estimate -/

/-- **`EvolCompKFix 1` from the GE-area fixed-vector estimate.**

The GE area (`Work.Diff.GE.hasDerivWithinAt_covRm_le`, whose proof is being assembled in
`Submission/Work/Diff/GE/`) proves the *sharp* one-sided fixed-vector estimate for `∇Rm`:

`∃ C ≥ 0`, for every Ricci flow `G` on `[0,T)`, `t ∈ [0,T)`, `x`, `v a b c d`,
`∃ D`, `HasDerivWithinAt (fun s ↦ covRm (G s) x v a b c d) D (Ico 0 T) t ∧
  D ≤ lapCovRmAt (G t) x v a b c d + C √|Rm|² √|∇Rm|² ‖v‖‖a‖‖b‖‖c‖‖d‖`.

This is exactly the `k = 1` instance of `EvolCompKFix` up to (i) the dictionary
`covKRm g x 1 (fun _ ↦ v) a b c d = covRm g x v a b c d` (`Work.Diff.EXT.covKRm_one`), (ii) the
dictionary of the two Laplacians (`Work.Diff.EXT.lapCovKRm_one_eq_lapCovRmAt`, **proved** and used
here),
(iii) `curvNormK g x 0 = |Rm|²`, `curvNormK g x 1 = |∇Rm|²`
(`Work.Diff.EXT.curvNormK_zero_eq_rmNormSq`, `curvNormK_one_eq_dRmNormSq`), and (iv) the elementary
`√f₀ √f₁ ≤ (1+f₀)(1+√f₁)` (`Work.Diff.EXT.sqrt_mul_sqrt_le`, proved above).  It isolates those
steps so that `EvolCompKFix 1` follows as soon as the GE estimate lands. -/
theorem evolCompKFix_one_of
    [T2Space M]
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ v a b c d : TangentSpace I x, ∃ D : ℝ,
        HasDerivWithinAt (fun s => covRm (G s) x v a b c d) D (Set.Ico 0 T) t ∧
        D ≤ Work.Diff.GE.lapCovRmAt (G t) x v a b c d
          + C * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
            * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
              * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
              * Real.sqrt ((G t).inner x d d)))
    :
    Work.Diff.EXT.EvolCompKFix (I := I) (M := M) 1 := by
  obtain ⟨C, hC, hcov⟩ := h
  refine ⟨C, hC, ?_⟩
  intro G T hflow t ht x u a b c d
  obtain ⟨D, hD, hle⟩ := hcov G T hflow t ht x (u 0) a b c d
  -- the tuple `u : Fin 1 → TangentSpace I x` is determined by `u 0`
  have hu : u = fun _ : Fin 1 => u 0 := by
    funext r
    exact congrArg u (Subsingleton.elim r 0)
  refine ⟨D, ?_, ?_⟩
  · have hfun : (fun s => covKRm (G s) x 1 u a b c d)
        = (fun s => covRm (G s) x (u 0) a b c d) := by
      funext s
      rw [hu]
      exact covKRm_one (G s) x (u 0) a b c d
    rw [hfun]
    exact hD
  · -- the numerical comparison of the two bounds
    have hlap' : Work.Diff.EXT.lapCovKRm (G t) x 1 u a b c d
        = Work.Diff.GE.lapCovRmAt (G t) x (u 0) a b c d := by
      rw [hu]
      exact lapCovKRm_one_eq_lapCovRmAt (G t) x (u 0) a b c d
    have hsum : (∑ j ∈ Finset.range 1, curvNormK (G t) x j) = rmNormSq (G t) x := by
      rw [Finset.sum_range_one, curvNormK_zero_eq_rmNormSq]
    have hone : curvNormK (G t) x 1 = dRmNormSq (G t) x := curvNormK_one_eq_dRmNormSq (G t) x
    have hprod : (∏ r : Fin 1, Real.sqrt ((G t).inner x (u r) (u r)))
        = Real.sqrt ((G t).inner x (u 0) (u 0)) :=
      Fin.prod_univ_one _
    set Pn : ℝ := Real.sqrt ((G t).inner x (u 0) (u 0)) * Real.sqrt ((G t).inner x a a)
        * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
        * Real.sqrt ((G t).inner x d d) with hPndef
    have hPnnn : 0 ≤ Pn := by
      rw [hPndef]
      positivity
    rw [hlap', hsum, hone, hprod]
    refine le_trans hle ?_
    have hsq : Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
        ≤ (1 + rmNormSq (G t) x) * (1 + Real.sqrt (dRmNormSq (G t) x)) :=
      sqrt_mul_sqrt_le (rmNormSq_nonneg' (G t) x)
    have key : C * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x) * Pn
        ≤ C * (1 + rmNormSq (G t) x) * (1 + Real.sqrt (dRmNormSq (G t) x)) * Pn := by
      calc C * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x) * Pn
          = (C * (Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x))) * Pn := by
            ring
        _ ≤ (C * ((1 + rmNormSq (G t) x) * (1 + Real.sqrt (dRmNormSq (G t) x)))) * Pn :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hC) hPnnn
        _ = C * (1 + rmNormSq (G t) x) * (1 + Real.sqrt (dRmNormSq (G t) x)) * Pn := by ring
    linarith [key]

/-! ## The general case: the classical reaction shape suffices -/

/-- **The arithmetic step of the reduction**: the classical reaction shape implies the bound of
`EvolCompKFix`.  For `k ≥ 1` the classical reaction `Σ_{i+j=k}√(f_i f_j)` is dominated by
`(k+1)(1+Σ_{j<k}f_j)(1+√f_k)` (`Work.Diff.EXT.sum_sqrt_le`), hence the constant `C(k+1)` works. -/
theorem evolCompKFix_of_reaction (k : ℕ) (hk : 1 ≤ k)
    (h : Work.Diff.EXT.EvolCompKFixReact (I := I) (M := M) k) :
    Work.Diff.EXT.EvolCompKFix (I := I) (M := M) k := by
  obtain ⟨C, hC, hrec⟩ := h
  refine ⟨C * (k + 1), mul_nonneg hC (by positivity), ?_⟩
  · intro G T hflow t ht x u a b c d
    obtain ⟨D, hD, hle⟩ := hrec G T hflow t ht x u a b c d
    refine ⟨D, hD, ?_⟩
    set Pn : ℝ := (∏ r : Fin k, Real.sqrt ((G t).inner x (u r) (u r)))
        * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
        * Real.sqrt ((G t).inner x c c) * Real.sqrt ((G t).inner x d d) with hPndef
    have hPnnn : 0 ≤ Pn := by
      rw [hPndef]
      positivity
    have hfnn : ∀ i ≤ k, 0 ≤ curvNormK (G t) x i := fun i _ => curvNormK_nonneg (G t) x i
    have hsum := sum_sqrt_le k hk (fun i => curvNormK (G t) x i) hfnn
    have key : C * (∑ i ∈ Finset.range (k + 1), Real.sqrt (curvNormK (G t) x i)
            * Real.sqrt (curvNormK (G t) x (k - i))) * Pn
        ≤ C * (k + 1) * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
            * (1 + Real.sqrt (curvNormK (G t) x k)) * Pn := by
      have h1 : C * (∑ i ∈ Finset.range (k + 1), Real.sqrt (curvNormK (G t) x i)
            * Real.sqrt (curvNormK (G t) x (k - i)))
          ≤ C * ((k + 1 : ℝ) * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
            * (1 + Real.sqrt (curvNormK (G t) x k))) :=
        mul_le_mul_of_nonneg_left hsum hC
      calc C * (∑ i ∈ Finset.range (k + 1), Real.sqrt (curvNormK (G t) x i)
              * Real.sqrt (curvNormK (G t) x (k - i))) * Pn
          ≤ C * ((k + 1 : ℝ) * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
              * (1 + Real.sqrt (curvNormK (G t) x k))) * Pn :=
            mul_le_mul_of_nonneg_right h1 hPnnn
        _ = C * (k + 1) * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
              * (1 + Real.sqrt (curvNormK (G t) x k)) * Pn := by ring
    linarith [key]


/-! ## The `k = 1` case, unconditionally -/

/-- **`EvolCompKFix 1`, proved.**  This instantiates `Work.Diff.EXT.evolCompKFix_one_of` with the
proved one-sided fixed-vector estimate for `∇Rm`
`Work.Diff.EXT.evolX.covRm_fixed_le` (which supplies, in the exact shape needed, the right
derivative of `s ↦ covRm (G s) x v a b c d` and its bound by `lapCovRmAt` plus
`C √|Rm|² √|∇Rm|²` times the metric norms), using `Work.Diff.T.lc_smooth` and
`Work.Diff.T.lc_variation`.  Hence the `k = 1` case of `Work.Diff.EXT.evolCompKFix_all` is
*complete*: only the `k ≥ 2` ladder case remains. -/
theorem evolCompKFix_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] :
    Work.Diff.EXT.EvolCompKFix (I := I) (M := M) 1 :=
  evolCompKFix_one_of (I := I) (M := M)
    (Work.Diff.EXT.evolX.covRm_fixed_le (I := I) (M := M)
      (Work.Diff.T.lc_smooth (I := I) (M := M))
      (Work.Diff.T.lc_variation (I := I) (M := M) (Work.Diff.T.lc_smooth (I := I) (M := M))))

/-! ## The target -/

/-- **The fixed-vector componentwise evolution of `∇^k Rm` for all `k ≥ 1`** (the requested
statement).  Reduction status:

* `k = 1`: `Work.Diff.EXT.evolCompKFix_one_of` (proved above) derives it from the GE-area fixed-vector
  estimate `Work.Diff.GE.hasDerivWithinAt_covRm_le` and the Laplacian dictionary
  `Work.Diff.EXT.lapCovKRm_one_eq_lapCovRmAt`; both are being proved in sibling files, so this case is
  a *bridge*, not new analysis here.
* `k ≥ 2`: this is the *induction step* of the analytic core.  Given the level-`k` evolution
  *identity* with an explicit reaction (which is what the induction has to carry, since `R_k` must be
  differentiated in space to reach level `k+1`), the passage from the classical reaction shape
  `Σ_{i+j=k}√(f_i f_j)` to the bound of `EvolCompKFix` is
  `Work.Diff.EXT.evolCompKFix_of_reaction` (proved) via `Work.Diff.EXT.sum_sqrt_le` (proved).

The remaining content is therefore exactly: (a) the `k = 1` fixed-vector estimate (GE area) and
(b) the explicit-reaction tower recursion of the docstring (differentiate the defining recursion of
`covKRmExt` at level `k+1`: `R_{k+1} = ∇R_k + [Ricci commutator] + (∂ₜ∇)-terms`, with `∂ₜ∇` from
`LCVariation` and the commutator from the Ricci identity, then bound the resulting explicit sum by
`Σ_{i+j=k+1}√(f_i f_j)`). -/
theorem evolCompKFix_all
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] :
    ∀ k : ℕ, 1 ≤ k → Work.Diff.EXT.EvolCompKFix (I := I) (M := M) k := by
  intro k hk
  rcases eq_or_lt_of_le hk with hk1 | hk2
  · subst hk1
    exact evolCompKFix_one (I := I) (M := M)
  · -- the `k ≥ 2` ladder case; see the module docstring for the architecture and the two notes
    -- above (`EvolCompKFixReact k` from the ladder, then `evolCompKFix_of_reaction`)
    sorry


/-! ## The existence half of the analytic core -/

/-- The `Classical.epsilon`-chosen extension `smoothExt x u` of a tangent vector is a globally
smooth field. -/
theorem smoothExt_smooth' [T2Space M] (x : M) (u : TangentSpace I x) :
    SmoothTField (I := I) (M := M) (smoothExt x u) :=
  (Classical.epsilon_spec
    (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u)).1

/-- **The `∃ D` half of `EvolCompKFix k`, reduced to joint smoothness of the tower family.**

If the tower `(s,y) ↦ (∇^k Rm)(G s)(y)` is joint `C^∞` on the fields `smoothExt x ·` at `(t, x)`,
then `s ↦ covKRm (G s) x k u a b c d` is `C^∞` in `s` near `t`, hence has a derivative there.  The
joint smoothness hypothesis is *provable* for every Ricci flow: it is
`Work.Diff.EXT.covK_familySmooth` (with the constant field families
`Work.Diff.EXT.jointField_const`, applied on the open set `Ioo 0 T` where `JointSmooth` gives
`JointMet`); it is taken as a hypothesis here only because that module imports
`Submission.Work.Diff.GE.norms_defs`, which is *currently incompatible* with
`Submission.Work.Diff.EXT.evolKDefs` (the module carrying `EvolCompKFix`): both files declare
`Work.Diff.GE.rot5` (`GE/frobSq5_frameIndep.lean`, a `Finset.sum_comm` helper, and
`GE/norms_defs.lean`, the rotation action of a curvature array).  Making the former `private`
removes the obstruction. -/
theorem hasDerivAt_covKRm_of_jointSmooth
    [I.Boundaryless] [T2Space M]
    {G : ℝ → SMet I M} {t₀ : ℝ} {k : ℕ} {x : M} {u : Fin k → TangentSpace I x}
    {a b c d : TangentSpace I x}
    (hsmooth : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => covKRmExt (G p.1) k (fun r : Fin k => smoothExt x (u r))
        (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) p.2) (t₀, x)) :
    HasDerivAt (fun s => covKRm (G s) x k u a b c d)
      (deriv (fun s => covKRm (G s) x k u a b c d) t₀) t₀ := by
  have hγ : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞ (fun s : ℝ => (s, x)) t₀ :=
    contMDiffAt_id.prodMk (contMDiffAt_const (c := x))
  have hcomp : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      ((fun p : ℝ × M => covKRmExt (G p.1) k (fun r : Fin k => smoothExt x (u r))
        (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) p.2)
        ∘ (fun s : ℝ => (s, x))) t₀ :=
    hsmooth.comp t₀ hγ
  have hfun : ((fun p : ℝ × M => covKRmExt (G p.1) k (fun r : Fin k => smoothExt x (u r))
        (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) p.2)
        ∘ (fun s : ℝ => (s, x)))
      = (fun s => covKRm (G s) x k u a b c d) := rfl
  rw [hfun] at hcomp
  exact (hcomp.contDiffAt.differentiableAt (by simp)).hasDerivAt

/-- The `∃ D` half of `EvolCompKFix k`, in the exact form used by the target. -/
theorem exists_hasDerivWithinAt_covKRm
    [I.Boundaryless] [T2Space M]
    {G : ℝ → SMet I M} {T t₀ : ℝ} {k : ℕ} {x : M} {u : Fin k → TangentSpace I x}
    {a b c d : TangentSpace I x}
    (hsmooth : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => covKRmExt (G p.1) k (fun r : Fin k => smoothExt x (u r))
        (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) p.2) (t₀, x)) :
    ∃ D, HasDerivWithinAt (fun s => covKRm (G s) x k u a b c d) D (Set.Ico 0 T) t₀ :=
  ⟨_, (hasDerivAt_covKRm_of_jointSmooth hsmooth).hasDerivWithinAt⟩

/-- **The `∃ D` half of `EvolCompKFix k`, proved for interior times.**

The joint smoothness hypothesis of `Work.Diff.EXT.hasDerivAt_covKRm_of_jointSmooth` is discharged by
`Work.Diff.EXT.covK_familySmooth`: restricting the flow to the open interval `Ioo 0 T` gives a
family of metrics jointly smooth in `(s, y)` (`JointMet`), the fields `smoothExt x ·` are smooth, so
the constant families they span are `JointField`s (`Work.Diff.EXT.jointField_const`) and the tower
`(s,y) ↦ covKRmExt (G s) k … y` is `C^∞` on `Ioo 0 T × univ`; composing it with the smooth curve
`s ↦ (s, x)` makes `s ↦ covKRm (G s) x k u a b c d` `C^∞` near `t₀`, whence the derivative exists.

(The `t₀ = 0` endpoint of the target would need a version of the joint smoothness on the half-open
set `Ico 0 T × univ`; for `k = 1` it is covered by the proved `Work.Diff.EXT.evolCompKFix_one`, and
for `k ≥ 2` by the ladder, whose hypothesis is stated on `Ico 0 T`.) -/
theorem exists_hasDerivWithinAt_covKRm_of_flow
    [I.Boundaryless] [T2Space M]
    {G : ℝ → SMet I M} {T t₀ : ℝ} (hflow : IsRicciFlow G T) (ht₀ : t₀ ∈ Set.Ioo 0 T)
    (k : ℕ) (x : M) (u : Fin k → TangentSpace I x) (a b c d : TangentSpace I x) :
    ∃ D, HasDerivWithinAt (fun s => covKRm (G s) x k u a b c d) D (Set.Ico 0 T) t₀ := by
  have hLC : LCSmooth I M := Work.Diff.T.lc_smooth (I := I) (M := M)
  have hJmet : JointMet G (Set.Ioo 0 T ×ˢ (univ : Set M)) :=
    ((jointMet_prod G (Set.Ico 0 T)).2 hflow.1).mono
      (Set.prod_mono Set.Ioo_subset_Ico_self (Subset.refl _))
  have hVf : ∀ r : Fin k,
      JointField (fun _ : ℝ => smoothExt x (u r)) (Set.Ioo 0 T ×ˢ (univ : Set M)) :=
    fun r => (jointField_const (I := I) (M := M) (smoothExt_smooth' x (u r))).mono
      (Set.subset_univ _)
  have hA : JointField (fun _ : ℝ => smoothExt x a) (Set.Ioo 0 T ×ˢ (univ : Set M)) :=
    (jointField_const (I := I) (M := M) (smoothExt_smooth' x a)).mono (Set.subset_univ _)
  have hB : JointField (fun _ : ℝ => smoothExt x b) (Set.Ioo 0 T ×ˢ (univ : Set M)) :=
    (jointField_const (I := I) (M := M) (smoothExt_smooth' x b)).mono (Set.subset_univ _)
  have hC : JointField (fun _ : ℝ => smoothExt x c) (Set.Ioo 0 T ×ˢ (univ : Set M)) :=
    (jointField_const (I := I) (M := M) (smoothExt_smooth' x c)).mono (Set.subset_univ _)
  have hD : JointField (fun _ : ℝ => smoothExt x d) (Set.Ioo 0 T ×ˢ (univ : Set M)) :=
    (jointField_const (I := I) (M := M) (smoothExt_smooth' x d)).mono (Set.subset_univ _)
  have hsm := covK_familySmooth (I := I) (M := M) hLC
    (isOpen_Ioo.prod isOpen_univ : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ (univ : Set M)))
    hJmet k hVf hA hB hC hD
  have hγ : ContMDiffWithinAt 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I) ∞
      (fun s : ℝ => (s, x)) (Set.Ioo 0 T) t₀ :=
    ContMDiffWithinAt.prodMk contMDiffWithinAt_id
      (contMDiffWithinAt_const (x := t₀) (c := x))
  have hΦ : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => covKRmExt (G p.1) k (fun r : Fin k => smoothExt x (u r))
        (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) p.2)
      (Set.Ioo 0 T ×ˢ (univ : Set M)) (t₀, x) := hsm (t₀, x) ⟨ht₀, Set.mem_univ x⟩
  have hmap : Set.MapsTo (fun s : ℝ => (s, x)) (Set.Ioo 0 T) (Set.Ioo 0 T ×ˢ (univ : Set M)) :=
    fun s hs => ⟨hs, Set.mem_univ x⟩
  have hAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      ((fun p : ℝ × M => covKRmExt (G p.1) k (fun r : Fin k => smoothExt x (u r))
        (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) p.2)
        ∘ (fun s : ℝ => (s, x))) t₀ :=
    (hΦ.comp t₀ hγ hmap).contMDiffAt (isOpen_Ioo.mem_nhds ht₀)
  have hfun : ((fun p : ℝ × M => covKRmExt (G p.1) k (fun r : Fin k => smoothExt x (u r))
        (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) p.2)
        ∘ (fun s : ℝ => (s, x)))
      = (fun s => covKRm (G s) x k u a b c d) := rfl
  rw [hfun] at hAt
  exact ⟨_, (hAt.contDiffAt.differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt⟩


/-! ## Two-sidedness: the form consumed by the moving-frame conversion -/

/-- Antisymmetry of `covKRm` in the first two of its four curvature slots. -/
theorem covKRm_antisymm_pair1 (g : SMet I M) (x : M) (j : ℕ) (w : Fin j → TangentSpace I x)
    (A B C D : TangentSpace I x) :
    covKRm g x j w B A C D = - covKRm g x j w A B C D := by
  have h1 := covKRmExt_antisymm_pair1 g x j (fun r => smoothExt x (w r)) (smoothExt x A)
    (smoothExt x B) (smoothExt x C) (smoothExt x D)
  simp only [covKRm]
  rw [h1]
  ring

/-- Antisymmetry of the rough Laplacian component `lapCovKRm` in the same two slots. -/
theorem lapCovKRm_antisymm_pair1 (g : SMet I M) (x : M) (k : ℕ) (u : Fin k → TangentSpace I x)
    (a b c d : TangentSpace I x) :
    lapCovKRm g x k u b a c d = - lapCovKRm g x k u a b c d := by
  simp only [lapCovKRm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := covKRm_antisymm_pair1 g x (k + 2) (Fin.cons (onFrame g x m) (Fin.cons (onFrame g x m) u)) a b c d
  linarith

/-- **The two-sided fixed-vector estimate from the one-sided `EvolCompKFix`.**

`EvolCompKFix k` is one-sided (`D ≤ lap + C·shape`).  Exchanging the first two curvature slots
(`a ↔ b`) multiplies both the component `covKRm (G s) x k v · · · ·` and the rough-Laplacian
component `lapCovKRm` by `-1` (`Work.Diff.EXT.covKRmExt_antisymm_pair1`), while the bound factor is
*unchanged* (it is symmetric in `a, b`).  The derivative on `Ico 0 T` is unique
(`uniqueDiffOn_Ico`), so the one-sided estimate applied to the exchanged tuple yields exactly the
missing *lower* bound for the original derivative; together with the upper bound this gives
`|D - lap| ≤ C·shape`.

This is the form in which fixed-vector estimates are consumed by
`Work.Diff.EXT.evolCompK_of_fixed` (`Submission/Work/Diff/EXT/evolCompK_all.lean`), which converts
them into `EvolCompK k` in a moving orthonormal frame. -/
theorem twoSided_of_EvolCompKFix (k : ℕ) (h : Work.Diff.EXT.EvolCompKFix (I := I) (M := M) k) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ico 0 T, ∀ x : M,
      ∀ (v : Fin k → TangentSpace I x) (a b c d : TangentSpace I x), ∃ D : ℝ,
        HasDerivWithinAt (fun s => covKRm (G s) x k v a b c d) D (Set.Ico 0 T) t ∧
        |D - lapCovKRm (G t) x k v a b c d|
          ≤ C₀ * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
              * (1 + Real.sqrt (curvNormK (G t) x k))
              * ((∏ r : Fin k, Real.sqrt ((G t).inner x (v r) (v r)))
                  * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
                  * Real.sqrt ((G t).inner x c c) * Real.sqrt ((G t).inner x d d)) := by
  obtain ⟨C, hC, hE⟩ := h
  refine ⟨C, hC, ?_⟩
  intro G T hflow t ht x v a b c d
  -- the one-sided estimate for the tuple and for the exchanged tuple
  obtain ⟨D₁, hD₁, hb₁⟩ := hE G T hflow t ht x v a b c d
  obtain ⟨D₂, hD₂, hb₂⟩ := hE G T hflow t ht x v b a c d
  -- the exchanged component is the negative, and so is its rough Laplacian
  have hneg : (fun s => covKRm (G s) x k v b a c d)
      = (fun s => - covKRm (G s) x k v a b c d) :=
    funext fun s => covKRm_antisymm_pair1 (G s) x k v a b c d
  have hD₂' : HasDerivWithinAt (fun s => - covKRm (G s) x k v a b c d) D₂ (Set.Ico 0 T) t := by
    rw [← hneg]
    exact hD₂
  have hD₂'' : HasDerivWithinAt (fun s => - - covKRm (G s) x k v a b c d) (-D₂) (Set.Ico 0 T) t :=
    hD₂'.neg
  have huniq : UniqueDiffWithinAt ℝ (Set.Ico 0 T) t := (uniqueDiffOn_Ico 0 T).uniqueDiffWithinAt ht
  have hfun : (fun s => - - covKRm (G s) x k v a b c d)
      = (fun s => covKRm (G s) x k v a b c d) := by
    funext s; simp
  have hD₁eq : D₁ = -D₂ := by
    have e1 := hD₁.derivWithin huniq
    have e2 : derivWithin (fun s => covKRm (G s) x k v a b c d) (Set.Ico 0 T) t = -D₂ := by
      rw [← hfun]
      exact hD₂''.derivWithin huniq
    rw [← e1, e2]
  -- the exchanged bound is a lower bound for `D₁`
  have hb₂' : D₂ ≤ - lapCovKRm (G t) x k v a b c d
      + C * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
          * (1 + Real.sqrt (curvNormK (G t) x k))
          * ((∏ r : Fin k, Real.sqrt ((G t).inner x (v r) (v r)))
              * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
              * Real.sqrt ((G t).inner x c c) * Real.sqrt ((G t).inner x d d)) := by
    have h1 : lapCovKRm (G t) x k v b a c d = - lapCovKRm (G t) x k v a b c d :=
      lapCovKRm_antisymm_pair1 (G t) x k v a b c d
    have h2 : C * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
          * (1 + Real.sqrt (curvNormK (G t) x k))
          * ((∏ r : Fin k, Real.sqrt ((G t).inner x (v r) (v r)))
              * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x a a)
              * Real.sqrt ((G t).inner x c c) * Real.sqrt ((G t).inner x d d))
        = C * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
          * (1 + Real.sqrt (curvNormK (G t) x k))
          * ((∏ r : Fin k, Real.sqrt ((G t).inner x (v r) (v r)))
              * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
              * Real.sqrt ((G t).inner x c c) * Real.sqrt ((G t).inner x d d)) := by
      ring
    linarith [hb₂, h1, h2]
  refine ⟨D₁, hD₁, ?_⟩
  have hupper : D₁ - lapCovKRm (G t) x k v a b c d
      ≤ C * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
          * (1 + Real.sqrt (curvNormK (G t) x k))
          * ((∏ r : Fin k, Real.sqrt ((G t).inner x (v r) (v r)))
              * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
              * Real.sqrt ((G t).inner x c c) * Real.sqrt ((G t).inner x d d)) := by
    linarith [hb₁]
  have hlower : -(C * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
          * (1 + Real.sqrt (curvNormK (G t) x k))
          * ((∏ r : Fin k, Real.sqrt ((G t).inner x (v r) (v r)))
              * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
              * Real.sqrt ((G t).inner x c c) * Real.sqrt ((G t).inner x d d)))
      ≤ D₁ - lapCovKRm (G t) x k v a b c d := by
    linarith [hD₁eq, hb₂']
  exact abs_le.mpr ⟨hlower, hupper⟩


/-! ## The multilinear expansion (`hexp` of the moving-frame conversion) -/

/-- **The multilinear expansion of `∇^k Rm` in a spanning family.**

This is the `hexp` input of `Work.Diff.EXT.evolCompK_of_fixed`
(`Submission/Work/Diff/EXT/evolCompK_all.lean`), i.e. the statement that the component of `∇^k Rm`
on a tuple `p` expanded as `p j = ∑ r, cp j r • a r` in a spanning family `a` is the corresponding
multilinear combination of the components on `a`.  It is the one-line consequence of
`Work.Diff.EXT.covKRm_expand_packed` (proved) with the value-level multilinearity
`Work.Diff.EXT.KrMulti_of_Kpt` (proved) supplied explicitly — the `[T2Space M]` instance is needed
by the latter. -/
theorem covKRm_expand_spanning
    [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) (k : ℕ)
    {n : ℕ} (a : Fin n → TangentSpace I x) (p : Fin (k + 4) → TangentSpace I x)
    (cp : Fin (k + 4) → Fin n → ℝ)
    (hp : ∀ j : Fin (k + 4), ∑ r, cp j r • a r = p j) :
    covKRm g x k (fun i : Fin k => p (Fin.castAdd 4 i)) (p (Fin.natAdd k 0))
        (p (Fin.natAdd k 1)) (p (Fin.natAdd k 2)) (p (Fin.natAdd k 3))
      = ∑ r : Fin (k + 4) → Fin n, (∏ j : Fin (k + 4), cp j (r j)) *
          covKRm g x k (fun i : Fin k => a (r (Fin.castAdd 4 i))) (a (r (Fin.natAdd k 0)))
            (a (r (Fin.natAdd k 1))) (a (r (Fin.natAdd k 2))) (a (r (Fin.natAdd k 3))) :=
  covKRm_expand_packed g x k (KrMulti_of_Kpt hLC g x k) a p cp hp

end Work.Diff.EXT
