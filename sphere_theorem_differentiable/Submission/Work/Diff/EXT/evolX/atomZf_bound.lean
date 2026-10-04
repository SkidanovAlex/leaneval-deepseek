import Mathlib
import Submission.Work.Diff.EXT.evolX.ladderAtoms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The norm bound for the level-`l` curvature vector `Zf`

`Work.Diff.EXT.evolX.Zf g W l Ψ x = ∑ i, ckt g l (Fin.snoc Ψ (W i)) x • W i x` is the level-`l`
curvature vector `∇^l Rm(Ψ)`, expanded in a frame `W` which is `g`-orthonormal near `x` (so that
the coefficients of the expansion are the components `ckt g l (Fin.snoc Ψ (W i)) x` of the tower).

This module bounds its `g`-norm by `finrank ℝ E · √(curvNormK g x l) · ∏ r, |Ψ r x|`:

* `inner_sum_smul_orthonormal` — in an orthonormal frame, `⟪∑ cᵢ·eᵢ, ∑ cᵢ·eᵢ⟫ = ∑ cᵢ²`
  (the expansion of the metric inner product, using `IsONFrame`);
* `sqrt_natCast_le_self` — `√n ≤ n` for a natural number `n` (the loss `√n → n` in the constant);
* `atomZf_bound` — the assembly: the Frobenius evaluation bound `Work.Diff.EXT.ckt_norm_le` applied
  to the `finrank ℝ E` tower values `ckt g l (Fin.snoc Ψ (W i)) x`, Cauchy–Schwarz over the
  orthonormal expansion, and the arithmetic `∑ᵢ cᵢ² ≤ (finrank ℝ E)·B²`.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

/-- **The inner product of a vector with itself, expanded in an orthonormal frame.**  If `e` is
`g`-orthonormal at `x`, then `⟪∑ i, cᵢ • eᵢ, ∑ i, cᵢ • eᵢ⟫ = ∑ i, cᵢ²`. -/
lemma inner_sum_smul_orthonormal {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x : M)
    (e : Fin n → TangentSpace I x)
    (he : ∀ i j, (g.inner x) (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (c : Fin n → ℝ) :
    (g.inner x) (∑ i, c i • e i) (∑ i, c i • e i) = ∑ i, (c i) ^ 2 := by
  rw [show (g.inner x) (∑ i, c i • e i) (∑ i, c i • e i)
      = ∑ i, c i * ∑ j, c j * ((g.inner x) (e j)) (e i) from by
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul]]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [he i i, if_pos rfl, mul_one]; ring
  · intro b _ hb
    rw [he b i, if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- `√n ≤ n` for `n : ℕ`. -/
lemma sqrt_natCast_le_self (n : ℕ) : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    have h0 : (0 : ℝ) ≤ (n : ℝ) := le_trans zero_le_one h1
    have hnn : (n : ℝ) ≤ (n : ℝ) * (n : ℝ) := by nlinarith
    calc Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) * (n : ℝ)) := Real.sqrt_le_sqrt hnn
      _ = (n : ℝ) := Real.sqrt_mul_self h0

theorem atomZf_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hW : ∀ i, Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (W i))
    (hON : Work.Diff.EXT.evolX.ONFrameAt (I := I) (M := M) g x W)
    (l : ℕ) (Ψ : Fin (l + 3) → Work.Diff.EXT.TField (I := I) (M := M))
    (hΨ : ∀ r, Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (Ψ r)) :
    Work.Diff.EXT.gNrm g x (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Ψ x)
      ≤ (Module.finrank ℝ E : ℝ) * Real.sqrt (Work.Diff.EXT.curvNormK g x l)
          * ∏ r : Fin (l + 3), Work.Diff.EXT.gNrm g x (Ψ r x) := by
  classical
  -- the frame is `g`-orthonormal at `x`
  have hONx : Submission.Diff.IsONFrame g x (fun i => W i x) := hON.self_of_nhds
  -- the coefficients of the expansion of `Zf` in the frame, and the target bound `B`
  set c : Fin (Module.finrank ℝ E) → ℝ :=
    fun i => Work.Diff.EXT.ckt g l (Fin.snoc Ψ (W i)) x with hcdef
  set B : ℝ := Real.sqrt (Work.Diff.EXT.curvNormK g x l)
    * ∏ r : Fin (l + 3), Work.Diff.EXT.gNrm g x (Ψ r x) with hBdef
  -- the tuples of fields are smooth
  have hsm : ∀ (i : Fin (Module.finrank ℝ E)) (s : Fin (l + 4)),
      Work.Diff.EXT.SmoothF ((Fin.snoc Ψ (W i) :
        Fin (l + 4) → Work.Diff.EXT.TField (I := I) (M := M)) s) := by
    intro i s
    rcases Fin.eq_castSucc_or_eq_last s with ⟨j, rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]; exact hΨ j
    · rw [Fin.snoc_last]; exact hW i
  -- the Frobenius evaluation bound for every coefficient
  have hcB : ∀ i : Fin (Module.finrank ℝ E), |c i| ≤ B := by
    intro i
    have h1 := Work.Diff.EXT.ckt_norm_le (I := I) (M := M) hLC g x l
      (Fin.snoc Ψ (W i)) (hsm i)
    rw [Fin.prod_univ_castSucc] at h1
    have h2 : (∏ j : Fin (l + 3), Work.Diff.EXT.gNrm g x
          ((Fin.snoc Ψ (W i) : Fin (l + 4) → Work.Diff.EXT.TField (I := I) (M := M))
            j.castSucc x))
        = ∏ j : Fin (l + 3), Work.Diff.EXT.gNrm g x (Ψ j x) := by
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [Fin.snoc_castSucc]
    have h3 : Work.Diff.EXT.gNrm g x
        ((Fin.snoc Ψ (W i) : Fin (l + 4) → Work.Diff.EXT.TField (I := I) (M := M))
          (Fin.last (l + 3)) x) = 1 := by
      rw [Fin.snoc_last]
      rw [show Work.Diff.EXT.gNrm g x (W i x)
          = Real.sqrt ((g.inner x) (W i x) (W i x)) from rfl]
      have hii : (g.inner x) (W i x) (W i x) = 1 := by
        have hh := hONx i i
        simpa using hh
      rw [hii, Real.sqrt_one]
    rw [h2, h3, mul_one] at h1
    exact h1
  have hBnn : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _)
    (Finset.prod_nonneg (fun r _ => Work.Diff.EXT.gNrm_nonneg g x (Ψ r x)))
  -- the expansion of the inner product of `Zf` with itself
  have hinner : (g.inner x) (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Ψ x)
      (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Ψ x) = ∑ i, (c i) ^ 2 := by
    rw [show Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Ψ x
        = ∑ i : Fin (Module.finrank ℝ E), c i • W i x from rfl]
    exact inner_sum_smul_orthonormal (I := I) (M := M) g x (fun i => W i x) hONx c
  have hLHS : Work.Diff.EXT.gNrm g x (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Ψ x)
      = Real.sqrt (∑ i, (c i) ^ 2) := by
    rw [show Work.Diff.EXT.gNrm g x (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Ψ x)
        = Real.sqrt ((g.inner x) (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Ψ x)
            (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Ψ x)) from rfl]
    rw [hinner]
  -- Cauchy--Schwarz / orthonormal-expansion arithmetic
  have hsum : (∑ i : Fin (Module.finrank ℝ E), (c i) ^ 2)
      ≤ (Module.finrank ℝ E : ℝ) * B ^ 2 := by
    calc (∑ i : Fin (Module.finrank ℝ E), (c i) ^ 2)
        ≤ ∑ i : Fin (Module.finrank ℝ E), B ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [← sq_abs (c i)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hcB i) 2
      _ = (Module.finrank ℝ E : ℝ) * B ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsqrt : Real.sqrt (∑ i : Fin (Module.finrank ℝ E), (c i) ^ 2)
      ≤ (Module.finrank ℝ E : ℝ) * B := by
    calc Real.sqrt (∑ i : Fin (Module.finrank ℝ E), (c i) ^ 2)
        ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) * B ^ 2) := Real.sqrt_le_sqrt hsum
      _ = Real.sqrt ((Module.finrank ℝ E : ℝ)) * Real.sqrt (B ^ 2) :=
          Real.sqrt_mul (Nat.cast_nonneg _) (B ^ 2)
      _ = Real.sqrt ((Module.finrank ℝ E : ℝ)) * B := by rw [Real.sqrt_sq hBnn]
      _ ≤ (Module.finrank ℝ E : ℝ) * B :=
          mul_le_mul_of_nonneg_right (sqrt_natCast_le_self _) hBnn
  calc Work.Diff.EXT.gNrm g x (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Ψ x)
      = Real.sqrt (∑ i : Fin (Module.finrank ℝ E), (c i) ^ 2) := hLHS
    _ ≤ (Module.finrank ℝ E : ℝ) * B := hsqrt
    _ = (Module.finrank ℝ E : ℝ) * Real.sqrt (Work.Diff.EXT.curvNormK g x l)
          * ∏ r : Fin (l + 3), Work.Diff.EXT.gNrm g x (Ψ r x) := by
        rw [mul_assoc]

end Work.Diff.EXT.evolX
