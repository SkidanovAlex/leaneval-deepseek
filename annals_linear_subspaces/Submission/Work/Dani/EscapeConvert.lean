import Mathlib
import ChallengeDeps
import Submission.Work.Dani.EscapeMetric
import Submission.GeometryOfNumbers.FlowSpanSxLower

/-!
# The bad-event conversion for the graph chart (Step A of conjunct 2)

`Submission.EscapeMetric` sets up the graph chart `x = graphPlane c = span(e_i + c_i)` and the
bridge from "no short integer vector" to the escape hypothesis.  This file supplies **Step A**:
the *conversion* of the geometric bad event for the plane `x` into the integer diophantine
event consumed by the cylinder-measure bound (`Commons.Analysis.Measure.volume_bad_union_le`).

The two ingredients are

* **the angle lemma** (`norm_le_sqrt_cterm_mul_orth`): for `Y ∈ x₀ᗮ` one has
  `‖Y‖ ≤ √(2 + Σ_{i,j} c_{ij}²)·‖π^⊥_x Y‖`
  (the proof: `π_{x₀}(π_x Y) = headVec a'` is *minus* a projection of `π^⊥_x Y`, so
  `‖headVec a'‖ ≤ ‖π^⊥_x Y‖`, and `‖π_x Y‖² ≤ (1 + Σc²)‖headVec a'‖²`);

* **the conversion** (`bad_imp_event`): if `n ≠ 0` is an integer vector whose `x`-projections are
  small at time `t` (the bad event), then the integer head coordinates `a := headComp n` are
  non-zero, bounded by `2e^{t(1/ℓ − ε)}`, and the integer tail coordinates `b := tailComp n`
  satisfy `|∑_i a_i c_{ij} − b_j| < √(2 + Σ c²)·e^{−t(1/(d−ℓ)+ε)}`.

Module `Submission.Work.Dani.EscapeConvert`, namespace `Submission.EscapeConvert`.
-/

noncomputable section

open LinearSubspaces Module Real MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission.EscapeConvert

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "𝔹" => Submission.ExteriorCoordinates.B

open Submission.EscapeMetric

/-- The "slope mass" `Σ_{i,j} (c i j)²` of the graph chart. -/
def cterm (l : ℕ) (c : Fin l → Fin (d - l) → ℝ) : ℝ := ∑ j, ∑ i, (c i j) ^ 2

lemma cterm_nonneg (l : ℕ) (c : Fin l → Fin (d - l) → ℝ) : 0 ≤ cterm l c :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ### The graph vector: coordinates, norm, and the Cauchy–Schwarz bound -/

lemma graphVec_apply_head (l : ℕ) (hld : l < d) (c : Fin l → Fin (d - l) → ℝ)
    (a : Fin l → ℝ) (i : Fin l) : graphVec l hld c a (headIdx l hld i) = a i := by
  rw [graphVec_eq_headVec_add, WithLp.ofLp_add, Pi.add_apply, headVec_coord_head,
    tailVec_coord_head, add_zero]

lemma graphVec_apply_tail (l : ℕ) (hld : l < d) (c : Fin l → Fin (d - l) → ℝ)
    (a : Fin l → ℝ) (j : Fin (d - l)) : graphVec l hld c a (tailIdx l hld j) = cComb l c a j := by
  rw [graphVec_eq_headVec_add, WithLp.ofLp_add, Pi.add_apply, headVec_coord_tail,
    tailVec_coord_tail, zero_add]

lemma graphVec_zero (l : ℕ) (hld : l < d) (c : Fin l → Fin (d - l) → ℝ) :
    graphVec l hld c 0 = 0 := by
  rw [graphVec_eq_headVec_add]
  simp [headVec, cComb, tailVec]

lemma inner_headVec_tailVec (l : ℕ) (hld : l < d) (a : Fin l → ℝ) (y : Fin (d - l) → ℝ) :
    inner ℝ (headVec l hld a) (tailVec l hld y) = 0 :=
  (Submodule.mem_orthogonal _ _).mp (tailVec_mem_orth l hld y) _ (headVec_mem_modelX l hld a)

lemma norm_sq_graphVec (l : ℕ) (hld : l < d) (c : Fin l → Fin (d - l) → ℝ) (a : Fin l → ℝ) :
    ‖graphVec l hld c a‖ ^ 2 = (∑ i, (a i) ^ 2) + ∑ j, (cComb l c a j) ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (headVec l hld a)
    (tailVec l hld (cComb l c a)) (inner_headVec_tailVec l hld a _)
  rw [graphVec_eq_headVec_add, sq, h, ← sq, ← sq, norm_sq_headVec, norm_sq_tailVec]

lemma cComb_sq_le (l : ℕ) (c : Fin l → Fin (d - l) → ℝ) (a : Fin l → ℝ) (j : Fin (d - l)) :
    (cComb l c a j) ^ 2 ≤ (∑ i, (a i) ^ 2) * (∑ i, (c i j) ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) (f := a) (g := fun i => c i j)
  simpa [cComb] using h

lemma sum_cComb_sq_le (l : ℕ) (c : Fin l → Fin (d - l) → ℝ) (a : Fin l → ℝ) :
    ∑ j, (cComb l c a j) ^ 2 ≤ (∑ i, (a i) ^ 2) * cterm l c := by
  have h3 : ∑ j, (cComb l c a j) ^ 2 ≤ ∑ j, (∑ i, (a i) ^ 2) * (∑ i, (c i j) ^ 2) :=
    Finset.sum_le_sum fun j _ => cComb_sq_le l c a j
  rw [← Finset.mul_sum] at h3
  rwa [← cterm] at h3

lemma norm_sq_graphVec_le (l : ℕ) (hld : l < d) (c : Fin l → Fin (d - l) → ℝ) (a : Fin l → ℝ) :
    ‖graphVec l hld c a‖ ^ 2 ≤ (1 + cterm l c) * ∑ i, (a i) ^ 2 := by
  have h2 := sum_cComb_sq_le l c a
  rw [norm_sq_graphVec]
  calc (∑ i, (a i) ^ 2) + ∑ j, (cComb l c a j) ^ 2
      ≤ (∑ i, (a i) ^ 2) + (∑ i, (a i) ^ 2) * cterm l c := add_le_add le_rfl h2
    _ = (1 + cterm l c) * ∑ i, (a i) ^ 2 := by ring

/-! ### The angle lemma -/

/-- **The angle lemma.**  For `Y ∈ x₀ᗮ` one has `‖Y‖ ≤ √(2 + cterm)‖π^⊥_x Y‖`, where
`x = graphPlane c` is the graph plane of `c` and `cterm = Σ_{i,j} c_{ij}²`. -/
theorem norm_le_sqrt_cterm_mul_orth (l : ℕ) (hld : l < d) (c : Fin l → Fin (d - l) → ℝ)
    {Y : ℝᵈ} (hY : Y ∈ (Submission.WedgeBlocks.modelX (d := d) l)ᗮ) :
    ‖Y‖ ≤ Real.sqrt (2 + cterm l c) *
      ‖((graphPlane l hld c)ᗮ).starProjection Y‖ := by
  classical
  set x : Submodule ℝ ℝᵈ := graphPlane l hld c with hxdef
  set Z : ℝᵈ := (x.starProjection Y : ℝᵈ) with hZdef
  set W : ℝᵈ := ((xᗮ).starProjection Y : ℝᵈ) with hWdef
  have hZW : Z + W = Y := by
    rw [hZdef, hWdef]
    exact Submodule.starProjection_add_starProjection_orthogonal (K := x) Y
  -- `Z` is a graph vector
  have hZx : Z ∈ x := Submodule.starProjection_apply_mem x Y
  obtain ⟨a', ha'⟩ : ∃ a' : Fin l → ℝ, graphVec l hld c a' = Z := hZx
  -- `π_{x₀} Z = headVec a'`
  have hprojZ : ((Submission.WedgeBlocks.modelX (d := d) l).starProjection Z : ℝᵈ) = headVec l hld a' := by
    rw [← ha', graphVec_eq_headVec_add, map_add,
      Submodule.starProjection_eq_self_iff.mpr (headVec_mem_modelX l hld a'),
      (Submodule.starProjection_apply_eq_zero_iff _).mpr (tailVec_mem_orth l hld _), add_zero]
  -- `headVec a' = -π_{x₀} W`
  have hhead : headVec l hld a' = -((Submission.WedgeBlocks.modelX (d := d) l).starProjection W : ℝᵈ) := by
    have h1 : Z = Y - W := by rw [← hZW]; abel
    have h2 : ((Submission.WedgeBlocks.modelX (d := d) l).starProjection Z : ℝᵈ) =
        ((Submission.WedgeBlocks.modelX (d := d) l).starProjection Y : ℝᵈ) - ((Submission.WedgeBlocks.modelX (d := d) l).starProjection W : ℝᵈ) := by
      rw [h1, map_sub]
    rw [hprojZ, (Submodule.starProjection_apply_eq_zero_iff _).mpr hY, zero_sub] at h2
    exact h2
  have hhead_le : ‖headVec l hld a'‖ ≤ ‖W‖ := by
    rw [hhead, norm_neg]
    exact Submodule.norm_starProjection_apply_le _ _
  have hhead_sq : ‖headVec l hld a'‖ ^ 2 ≤ ‖W‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hhead_le 2
  have hZsq : ‖Z‖ ^ 2 ≤ (1 + cterm l c) * ‖W‖ ^ 2 := by
    have h1 : ‖Z‖ ^ 2 = (∑ i, (a' i) ^ 2) + ∑ j, (cComb l c a' j) ^ 2 := by
      rw [← ha']; exact norm_sq_graphVec l hld c a'
    have h2 : (∑ i, (a' i) ^ 2) = ‖headVec l hld a'‖ ^ 2 := (norm_sq_headVec l hld a').symm
    have h3 : ∑ j, (cComb l c a' j) ^ 2 ≤ ‖headVec l hld a'‖ ^ 2 * cterm l c := by
      rw [← h2]; exact sum_cComb_sq_le l c a'
    have h4 : (∑ i, (a' i) ^ 2) + ∑ j, (cComb l c a' j) ^ 2
        ≤ (1 + cterm l c) * ‖W‖ ^ 2 := by
      have h5 : ‖headVec l hld a'‖ ^ 2 * cterm l c ≤ ‖W‖ ^ 2 * cterm l c :=
        mul_le_mul_of_nonneg_right hhead_sq (cterm_nonneg l c)
      nlinarith [h2, h3, h5, hhead_sq, cterm_nonneg l c]
    rw [h1]
    exact h4
  have hpyth : ‖Y‖ ^ 2 = ‖Z‖ ^ 2 + ‖W‖ ^ 2 := by
    rw [hZdef, hWdef]
    exact Submodule.norm_sq_eq_add_norm_sq_starProjection Y x
  have hfinal : ‖Y‖ ^ 2 ≤ (2 + cterm l c) * ‖W‖ ^ 2 := by
    have h1 : (1 + cterm l c) * ‖W‖ ^ 2 = ‖W‖ ^ 2 + cterm l c * ‖W‖ ^ 2 := by ring
    have h2 : (2 + cterm l c) * ‖W‖ ^ 2 = (‖W‖ ^ 2 + cterm l c * ‖W‖ ^ 2) + ‖W‖ ^ 2 := by ring
    rw [hpyth, h2]
    linarith [hZsq]
  have h2nn : 0 ≤ 2 + cterm l c := by linarith [cterm_nonneg l c]
  have h3 : ‖Y‖ ^ 2 ≤ (Real.sqrt (2 + cterm l c) * ‖W‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt h2nn]
    exact hfinal
  calc ‖Y‖ = Real.sqrt (‖Y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg Y)).symm
    _ ≤ Real.sqrt ((Real.sqrt (2 + cterm l c) * ‖W‖) ^ 2) := Real.sqrt_le_sqrt h3
    _ = Real.sqrt (2 + cterm l c) * ‖W‖ :=
        Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))

/-! ### Step A: the conversion of the bad event into the integer event -/

lemma tailVec_sub (l : ℕ) (hld : l < d) (y y' : Fin (d - l) → ℝ) :
    tailVec l hld (y - y') = tailVec l hld y - tailVec l hld y' := by
  simp only [tailVec, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-- **Step A (the conversion).**  If `n ≠ 0` is an integer vector whose `x`-projections are small
at time `t ≥ 0` (the bad event for the plane `x = graphPlane c`), then its integer head
coordinates `a` are non-zero and bounded by `A`, and its integer tail coordinates `b` satisfy
the diophantine condition with accuracy `δ`. -/
theorem bad_imp_event (l : ℕ) (hl0 : 0 < l) (hld : l < d) (c : Fin l → Fin (d - l) → ℝ)
    {ε t A δ : ℝ} (ht : 0 ≤ t) (hδ1 : δ ≤ 1 / 2)
    {n : ℝᵈ} (hnmem : n ∈ intPoints (d := d)) (hn : n ≠ 0)
    (hb1 : Real.exp (-t / (l : ℝ)) * ‖((graphPlane l hld c).starProjection n : ℝᵈ)‖ <
      Real.exp (-(ε * t)))
    (hb2 : Real.exp (t / ((d : ℝ) - (l : ℝ))) *
      ‖(((graphPlane l hld c)ᗮ).starProjection n : ℝᵈ)‖ < Real.exp (-(ε * t)))
    (hA : 2 * Real.exp (t * (1 / (l : ℝ) - ε)) ≤ A)
    (hδ : Real.sqrt (2 + cterm l c) * Real.exp (-(t * (1 / ((d : ℝ) - (l : ℝ)) + ε))) ≤ δ) :
    ∃ a : Fin l → ℤ, (∃ i, a i ≠ 0) ∧ (∀ i, |(a i : ℝ)| ≤ A) ∧
      ∃ b : Fin (d - l) → ℤ, ∀ j, |(∑ i, (a i : ℝ) * c i j) - (b j : ℝ)| < δ := by
  classical
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
  have hdlR : (0 : ℝ) < (d : ℝ) - (l : ℝ) := by
    have : (l : ℝ) < (d : ℝ) := by exact_mod_cast hld
    linarith
  set x : Submodule ℝ ℝᵈ := graphPlane l hld c with hxdef
  set Z : ℝᵈ := (x.starProjection n : ℝᵈ) with hZdef
  set W : ℝᵈ := ((xᗮ).starProjection n : ℝᵈ) with hWdef
  -- integer head and tail coordinates
  choose a haeq using fun i : Fin l =>
    Submission.EscapeGlue.intPoints_coord_int n hnmem (headIdx l hld i)
  choose b hbeq using fun j : Fin (d - l) =>
    Submission.EscapeGlue.intPoints_coord_int n hnmem (tailIdx l hld j)
  set aR : Fin l → ℝ := fun i => (a i : ℝ) with haR
  set bR : Fin (d - l) → ℝ := fun j => (b j : ℝ) with hbR
  have hnrec : n = headVec l hld aR + tailVec l hld bR := by
    have h := reconstruct l hld n
    have h1 : (fun i => n (headIdx l hld i)) = aR := funext fun i => haeq i
    have h2 : (fun j => n (tailIdx l hld j)) = bR := funext fun j => hbeq j
    rw [h1, h2] at h
    exact h.symm
  -- the norm floor
  have hn1 : (1 : ℝ) ≤ ‖n‖ := Submission.FlowSpanSxLower.norm_ge_one_of_mem_intPoints hnmem hn
  -- the two projection bounds
  have hZlt : ‖Z‖ < Real.exp (t * (1 / (l : ℝ) - ε)) := by
    have hpos : 0 < Real.exp (-t / (l : ℝ)) := Real.exp_pos _
    have h1 : ‖Z‖ < Real.exp (-(ε * t)) / Real.exp (-t / (l : ℝ)) := by
      rw [hZdef, lt_div_iff₀ hpos, mul_comm]
      exact hb1
    have heq : -(ε * t) - -t / (l : ℝ) = t * (1 / (l : ℝ) - ε) := by
      field_simp
      ring
    rw [← Real.exp_sub, heq] at h1
    exact h1
  have hWlt : ‖W‖ < Real.exp (-(t * (1 / ((d : ℝ) - (l : ℝ)) + ε))) := by
    have hpos : 0 < Real.exp (t / ((d : ℝ) - (l : ℝ))) := Real.exp_pos _
    have h1 : ‖W‖ < Real.exp (-(ε * t)) / Real.exp (t / ((d : ℝ) - (l : ℝ))) := by
      rw [hWdef, lt_div_iff₀ hpos, mul_comm]
      exact hb2
    have heq : -(ε * t) - t / ((d : ℝ) - (l : ℝ))
        = -(t * (1 / ((d : ℝ) - (l : ℝ)) + ε)) := by ring
    rw [← Real.exp_sub, heq] at h1
    exact h1
  -- the vector `Y = n − graphVec c (headComp n)` and its tail representation
  set Y : ℝᵈ := n - graphVec l hld c aR with hYdef
  have hYtail : Y = tailVec l hld (bR - cComb l c aR) := by
    have h2 : n - graphVec l hld c aR = tailVec l hld bR - tailVec l hld (cComb l c aR) := by
      rw [hnrec, graphVec_eq_headVec_add]
      abel
    rw [hYdef, h2, tailVec_sub]
  have hYorth : Y ∈ (Submission.WedgeBlocks.modelX (d := d) l)ᗮ := by
    rw [hYtail]; exact tailVec_mem_orth l hld _
  have hYproj : ((graphPlane l hld c)ᗮ).starProjection Y = W := by
    have hmem : graphVec l hld c aR ∈ ((graphPlane l hld c)ᗮ)ᗮ := by
      rw [Submodule.orthogonal_orthogonal]
      exact graphVec_mem_graphPlane l hld c aR
    have hzero : ((graphPlane l hld c)ᗮ).starProjection (graphVec l hld c aR) = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff _).mpr hmem
    rw [show Y = n - graphVec l hld c aR from hYdef, map_sub, hzero, sub_zero]
  have hYlt : ‖Y‖ < δ := by
    have hangle := norm_le_sqrt_cterm_mul_orth l hld c hYorth
    rw [hYproj] at hangle
    refine lt_of_le_of_lt hangle ?_
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hWlt (Real.sqrt_pos.mpr (by
      linarith [cterm_nonneg l c]))) hδ
  -- the head coordinates are non-zero
  have ha0 : a ≠ 0 := by
    intro h0
    have haR0 : aR = 0 := by
      rw [haR]
      funext i
      simp [h0]
    have hYn : Y = n := by rw [hYdef, haR0, graphVec_zero]; simp
    have : ‖n‖ < δ := by rw [← hYn]; exact hYlt
    linarith
  refine ⟨a, ?_, ?_, b, ?_⟩
  · by_contra hc
    refine ha0 (funext fun i => ?_)
    exact not_not.mp (not_exists.mp hc i)
  · -- the coefficient bound
    intro i
    have h1 : |(a i : ℝ)| ≤ ‖headVec l hld (fun i => n (headIdx l hld i))‖ := by
      have h2 : headVec l hld (fun i => n (headIdx l hld i)) (headIdx l hld i) =
          n (headIdx l hld i) := headVec_coord_head l hld _ i
      have h3 := PiLp.norm_apply_le (headVec l hld (fun i => n (headIdx l hld i)))
        (headIdx l hld i)
      rw [h2, haeq i] at h3
      simpa [Real.norm_eq_abs] using h3
    have h4 : ‖headVec l hld (fun i => n (headIdx l hld i))‖ ≤ ‖Z‖ + ‖W‖ := by
      have h5 := norm_headComp_le l hld x n
      rw [hZdef, hWdef]
      exact h5
    have hWle : ‖W‖ ≤ Real.exp (t * (1 / (l : ℝ) - ε)) := by
      refine le_trans hWlt.le ?_
      refine Real.exp_le_exp.mpr ?_
      have h2 : 0 < 1 / (l : ℝ) := by positivity
      have h3 : 0 < 1 / ((d : ℝ) - (l : ℝ)) := by positivity
      nlinarith [ht, h2, h3]
    linarith [h1, h4, hZlt, hWle, hA]
  · -- the diophantine accuracy
    intro j
    have hYcoord : Y (tailIdx l hld j) = bR j - cComb l c aR j := by
      rw [hYtail]
      exact tailVec_coord_tail l hld _ j
    have h1 : |bR j - cComb l c aR j| ≤ ‖Y‖ := by
      rw [← hYcoord]
      have h3 := PiLp.norm_apply_le Y (tailIdx l hld j)
      simpa [Real.norm_eq_abs] using h3
    have h2 : (∑ i, (a i : ℝ) * c i j) = cComb l c aR j := by
      simp [cComb, haR]
    rw [h2, show (b j : ℝ) = bR j from rfl]
    calc |cComb l c aR j - bR j| = |bR j - cComb l c aR j| := by
          rw [abs_sub_comm]
      _ ≤ ‖Y‖ := h1
      _ < δ := hYlt

end Submission.EscapeConvert

end
