import Mathlib
import Submission.Work.Diff.MP.Basic
import Submission.Work.Diff.MP.LM_aux
import Submission.Work.Diff.GE.uhlenbeck_defs
import Submission.Work.Diff.GE.matrix_sqrt_family_kit
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The inverse-function-theorem square root near `1`, and the two-sided tube lemma

This file collects the parts of the `MP` development that do not depend on the truncation model
itself, so that they can be imported by other modules (in particular by delegated lemmas about the
truncation model): `Work.Diff.MP.sqrtC` (a square root near `1` which is `C^1` on a *neighbourhood*
of `1`, unlike `Work.Diff.GE.sqrtNear`, whose inverse-function-theorem construction only gives
differentiability *at* `1`), its properties, the orthogonalisation lemma `sqrtC_orthogonal`, and the
two-sided tube lemma `exists_pos_forall_mem_of_isCompact_two`.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Filter

set_option maxHeartbeats 8000000

namespace Work.Diff.MP

/-! ## A continuously differentiable matrix square root near the identity

`Work.Diff.GE.sqrtNear` is the inverse-function-theorem local inverse of the squaring map on a
normed ring; it is differentiable *at* `1` but Mathlib's construction gives no differentiability on
a neighbourhood.  The step from "the local model exists" to the *uniform* one-step estimate needs
the model to be differentiable in the time variable on a whole interval (so that the mean value
theorem applies), so here we use `ContDiffAt.localInverse` instead, which comes with
`ContDiffAt.to_localInverse` and hence is `C¹` on a neighbourhood of `1`.

Nothing about it is special to matrices. -/

private theorem contDiffAt_sq (𝔸 : Type*) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] :
    ContDiffAt ℝ 1 (fun A : 𝔸 => A * A) (1 : 𝔸) :=
  ContDiffAt.mul (f := fun A : 𝔸 => A) (g := fun A : 𝔸 => A) contDiffAt_id contDiffAt_id

private theorem sq_hasFDerivAt (𝔸 : Type*) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] :
    HasFDerivAt (fun A : 𝔸 => A * A)
      ((Work.Diff.GE.sqrtEquiv (𝔸 := 𝔸) : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) (1 : 𝔸) :=
  (Work.Diff.GE.hasStrictFDerivAt_mul_self (𝔸 := 𝔸)).hasFDerivAt

private theorem hn_one : (1 : ℕ∞ω) ≠ 0 := by norm_num

private theorem localInverse_congr {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace E]
    {f : E → F} {f' : E ≃L[ℝ] F} {a : E}
    {h₁ h₂ : HasStrictFDerivAt f (f' : E →L[ℝ] F) a} :
    h₁.localInverse f f' a = h₂.localInverse f f' a := by
  rw [Subsingleton.elim h₁ h₂]

/-- The inverse-function-theorem square root near `1`. -/
noncomputable def sqrtC (n : ℕ) : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ :=
  (Work.Diff.GE.hasStrictFDerivAt_mul_self (𝔸 := Matrix (Fin n) (Fin n) ℝ)).localInverse
    (fun A : Matrix (Fin n) (Fin n) ℝ => A * A)
    (Work.Diff.GE.sqrtEquiv (𝔸 := Matrix (Fin n) (Fin n) ℝ)) 1

/-- `Work.Diff.MP.sqrtC` agrees with the `GE`-area square root `Work.Diff.GE.sqrtNear` (the two
constructions differ only in the proof argument of `HasStrictFDerivAt.localInverse`). -/
theorem sqrtC_eq_sqrtNear_apply (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    sqrtC n A = Work.Diff.GE.sqrtNear (𝔸 := Matrix (Fin n) (Fin n) ℝ) A := by
  have h := localInverse_congr (E := Matrix (Fin n) (Fin n) ℝ) (F := Matrix (Fin n) (Fin n) ℝ)
    (f := fun B : Matrix (Fin n) (Fin n) ℝ => B * B)
    (f' := Work.Diff.GE.sqrtEquiv (𝔸 := Matrix (Fin n) (Fin n) ℝ)) (a := 1)
    (h₁ := Work.Diff.GE.hasStrictFDerivAt_mul_self (𝔸 := Matrix (Fin n) (Fin n) ℝ))
    (h₂ := Work.Diff.GE.hasStrictFDerivAt_mul_self (𝔸 := Matrix (Fin n) (Fin n) ℝ))
  exact congrFun h A

/-- The functional form of `sqrtC_eq_sqrtNear_apply`. -/
theorem sqrtC_eq_sqrtNear (n : ℕ) :
    sqrtC n = Work.Diff.GE.sqrtNear (𝔸 := Matrix (Fin n) (Fin n) ℝ) :=
  funext (sqrtC_eq_sqrtNear_apply n)

theorem sqrtC_contDiffAt (n : ℕ) : ContDiffAt ℝ 1 (sqrtC n) 1 := by
  have h := (contDiffAt_sq (Matrix (Fin n) (Fin n) ℝ)).to_localInverse
    (sq_hasFDerivAt (Matrix (Fin n) (Fin n) ℝ)) hn_one
  have heq : (contDiffAt_sq (Matrix (Fin n) (Fin n) ℝ)).localInverse
      (sq_hasFDerivAt (Matrix (Fin n) (Fin n) ℝ)) hn_one = sqrtC n := by
    unfold sqrtC ContDiffAt.localInverse
    exact localInverse_congr
  rw [heq] at h
  simpa using h

theorem sqrtC_one (n : ℕ) : sqrtC n 1 = 1 := by
  have h := (Work.Diff.GE.hasStrictFDerivAt_mul_self (𝔸 := Matrix (Fin n) (Fin n) ℝ)).localInverse_apply_image
    (f := fun A : Matrix (Fin n) (Fin n) ℝ => A * A)
    (f' := Work.Diff.GE.sqrtEquiv (𝔸 := Matrix (Fin n) (Fin n) ℝ)) (a := 1)
  simpa [sqrtC, mul_one] using h

theorem sqrtC_sq_mul (n : ℕ) :
    ∀ᶠ y in 𝓝 ((fun A : Matrix (Fin n) (Fin n) ℝ => A * A) 1),
      (fun A : Matrix (Fin n) (Fin n) ℝ => A * A) (sqrtC n y) = y :=
  (Work.Diff.GE.hasStrictFDerivAt_mul_self (𝔸 := Matrix (Fin n) (Fin n) ℝ)).eventually_right_inverse
    (f := fun A : Matrix (Fin n) (Fin n) ℝ => A * A)
    (f' := Work.Diff.GE.sqrtEquiv (𝔸 := Matrix (Fin n) (Fin n) ℝ)) (a := 1)

theorem sqrtC_sq_eq (n : ℕ) :
    ∀ᶠ x in 𝓝 (1 : Matrix (Fin n) (Fin n) ℝ), sqrtC n (x * x) = x :=
  (Work.Diff.GE.hasStrictFDerivAt_mul_self (𝔸 := Matrix (Fin n) (Fin n) ℝ)).eventually_left_inverse
    (f := fun A : Matrix (Fin n) (Fin n) ℝ => A * A)
    (f' := Work.Diff.GE.sqrtEquiv (𝔸 := Matrix (Fin n) (Fin n) ℝ)) (a := 1)

theorem sqrtC_mul_self (n : ℕ) :
    ∀ᶠ y in 𝓝 (1 : Matrix (Fin n) (Fin n) ℝ), sqrtC n y * sqrtC n y = y := by
  simpa [mul_one] using sqrtC_sq_mul n

/-- The continuous-map part of the orthogonalisation: `Γ ↦ sqrtC (Ring.inverse Γ)` is continuous
at `1` with value `1`. -/
theorem sqrtC_inv_tendsto (n : ℕ) :
    Tendsto (fun Γ : Matrix (Fin n) (Fin n) ℝ => sqrtC n (Ring.inverse Γ)) (𝓝 1) (𝓝 1) := by
  have hinv : Tendsto (fun Γ : Matrix (Fin n) (Fin n) ℝ => Ring.inverse Γ) (𝓝 1) (𝓝 1) := by
    have h : ContinuousAt (Ring.inverse : Matrix (Fin n) (Fin n) ℝ →
        Matrix (Fin n) (Fin n) ℝ) 1 :=
      (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (Matrix (Fin n) (Fin n) ℝ)ˣ)).continuousAt
    simpa only [Ring.inverse_one] using h.tendsto
  have hsqrt : Tendsto (sqrtC n) (𝓝 (1 : Matrix (Fin n) (Fin n) ℝ)) (𝓝 1) := by
    have h : ContinuousAt (sqrtC n) (1 : Matrix (Fin n) (Fin n) ℝ) :=
      (sqrtC_contDiffAt n).continuousAt
    simpa only [sqrtC_one n] using h.tendsto
  exact hsqrt.comp hinv

/-- **Orthogonalisation near the identity.**  For a symmetric matrix `Γ` close enough to `1`, the
inverse-function-theorem square root `P = sqrtC (Ring.inverse Γ)` satisfies `Pᵀ Γ P = 1`, i.e. the
columns of `P` are orthonormal for the bilinear form `Γ`. -/
theorem sqrtC_orthogonal (n : ℕ) :
    ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℝ), ∀ Γ ∈ V,
      Matrix.transpose Γ = Γ →
      Matrix.transpose (sqrtC n (Ring.inverse Γ)) * Γ * sqrtC n (Ring.inverse Γ) = 1 := by
  classical
  have hinv : Tendsto (fun Γ : Matrix (Fin n) (Fin n) ℝ => Ring.inverse Γ) (𝓝 1) (𝓝 1) := by
    have h : ContinuousAt (Ring.inverse : Matrix (Fin n) (Fin n) ℝ →
        Matrix (Fin n) (Fin n) ℝ) 1 :=
      (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (Matrix (Fin n) (Fin n) ℝ)ˣ)).continuousAt
    simpa only [Ring.inverse_one] using h.tendsto
  have hmm := sqrtC_mul_self n
  have hsq := sqrtC_sq_eq n
  have hGinv_ev : ∀ᶠ Γ in 𝓝 (1 : Matrix (Fin n) (Fin n) ℝ), IsUnit Γ := by
    filter_upwards [Metric.ball_mem_nhds (1 : Matrix (Fin n) (Fin n) ℝ)
      (by norm_num : (0 : ℝ) < 1)] with Γ hΓ
    rw [Metric.mem_ball, dist_eq_norm] at hΓ
    have h' : ‖(1 : Matrix (Fin n) (Fin n) ℝ) - Γ‖ < 1 := by
      simpa [norm_sub_rev] using hΓ
    have h2 : IsUnit ((1 : Matrix (Fin n) (Fin n) ℝ) - ((1 : Matrix (Fin n) (Fin n) ℝ) - Γ)) :=
      isUnit_one_sub_of_norm_lt_one h'
    simpa using h2
  have hT : Tendsto (fun Γ : Matrix (Fin n) (Fin n) ℝ =>
      Matrix.transpose (sqrtC n (Ring.inverse Γ))) (𝓝 1) (𝓝 1) := by
    have htr : Tendsto (Matrix.transpose : Matrix (Fin n) (Fin n) ℝ →
        Matrix (Fin n) (Fin n) ℝ) (𝓝 1) (𝓝 1) := by
      have hc : Continuous (Matrix.transpose : Matrix (Fin n) (Fin n) ℝ →
          Matrix (Fin n) (Fin n) ℝ) := continuous_id.matrix_transpose
      simpa only [Matrix.transpose_one] using hc.tendsto 1
    exact htr.comp (sqrtC_inv_tendsto n)
  refine ⟨{Γ | sqrtC n (Ring.inverse Γ) * sqrtC n (Ring.inverse Γ) = Ring.inverse Γ}
      ∩ {Γ | IsUnit Γ}
      ∩ {Γ | Matrix.transpose (sqrtC n (Ring.inverse Γ)) ∈ {x | sqrtC n (x * x) = x}},
    Filter.inter_mem (Filter.inter_mem (hinv.eventually hmm) hGinv_ev) (hT.eventually hsq), ?_⟩
  intro Γ hΓ hsym
  obtain ⟨⟨hA, hunit⟩, hD⟩ := hΓ
  set P : Matrix (Fin n) (Fin n) ℝ := sqrtC n (Ring.inverse Γ) with hP
  have hPP : P * P = Ring.inverse Γ := hA
  have hGinv : Ring.inverse Γ * Γ = 1 := by
    obtain ⟨u, hu⟩ : ∃ u : (Matrix (Fin n) (Fin n) ℝ)ˣ,
        (u : Matrix (Fin n) (Fin n) ℝ) = Γ := ⟨hunit.unit, hunit.unit_spec⟩
    rw [← hu, Ring.inverse_unit]
    simpa using congrArg (Units.val) (Units.inv_mul u)
  have hGinv' : Γ * Ring.inverse Γ = 1 := by
    obtain ⟨u, hu⟩ : ∃ u : (Matrix (Fin n) (Fin n) ℝ)ˣ,
        (u : Matrix (Fin n) (Fin n) ℝ) = Γ := ⟨hunit.unit, hunit.unit_spec⟩
    rw [← hu, Ring.inverse_unit]
    simpa using congrArg (Units.val) (Units.mul_inv u)
  have hsyinv : Matrix.transpose (Ring.inverse Γ) = Ring.inverse Γ := by
    obtain ⟨u, hu⟩ : ∃ u : (Matrix (Fin n) (Fin n) ℝ)ˣ,
        (u : Matrix (Fin n) (Fin n) ℝ) = Γ := ⟨hunit.unit, hunit.unit_spec⟩
    rw [← hu, Ring.inverse_unit]
    let v : (Matrix (Fin n) (Fin n) ℝ)ˣ :=
      Units.mk (Matrix.transpose (u : Matrix (Fin n) (Fin n) ℝ))
        (Matrix.transpose ((u⁻¹ : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ))
        (by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one])
        (by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one])
    have hv : (v : Matrix (Fin n) (Fin n) ℝ) = (u : Matrix (Fin n) (Fin n) ℝ) := by
      show Matrix.transpose (u : Matrix (Fin n) (Fin n) ℝ) = (u : Matrix (Fin n) (Fin n) ℝ)
      rw [hu, hsym]
    have hvv : v = u := Units.ext hv
    have hv' : ((v⁻¹ : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ)
        = Matrix.transpose (((u⁻¹ : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ)) := by
      simp only [v, Units.inv_mk]
    calc Matrix.transpose (((u⁻¹ : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ))
        = ((v⁻¹ : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ) := hv'.symm
      _ = (((u⁻¹ : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ)) := by rw [hvv]
  have h1 : Matrix.transpose P * Matrix.transpose P = P * P := by
    rw [← Matrix.transpose_mul, hPP, hsyinv]
  have h2 : sqrtC n (Matrix.transpose P * Matrix.transpose P) = Matrix.transpose P := hD
  have hPsym : Matrix.transpose P = P := by
    rw [h1, hPP] at h2
    exact h2.symm
  have hL' : (Γ * P) * P = 1 := by rw [mul_assoc, hPP, hGinv']
  have hR' : P * (P * Γ) = 1 := by rw [← mul_assoc, hPP, hGinv]
  have hcomm : Γ * P = P * Γ := by
    calc Γ * P = (Γ * P) * (P * (P * Γ)) := by rw [hR', mul_one]
      _ = ((Γ * P) * P) * (P * Γ) := by rw [← mul_assoc]
      _ = P * Γ := by rw [hL', one_mul]
  calc Matrix.transpose P * Γ * P = P * Γ * P := by rw [hPsym]
    _ = (P * Γ) * P := rfl
    _ = (Γ * P) * P := by rw [hcomm]
    _ = 1 := hL'

/-! ## The two-sided tube lemma -/

/-- **Two-sided tube lemma.**  If `f` is continuous on `[a,b] × K` with `K` compact and `f t y ∈ W`
for all `y ∈ K` (`W` open, `t ∈ [a,b]`), then `f s y ∈ W` for all `y ∈ K` and all `s ∈ [a,b]` close
enough to `t`. -/
theorem exists_pos_forall_mem_of_isCompact_two {X : Type*} [TopologicalSpace X] {Y : Type*}
    [TopologicalSpace Y] {W : Set Y} (hW : IsOpen W) {K : Set X} (hK : IsCompact K)
    {a b t : ℝ} (hat : a ≤ t) (htb : t ≤ b) {f : ℝ → X → Y}
    (hf : ContinuousOn (fun p : ℝ × X => f p.1 p.2) (Set.Icc a b ×ˢ K))
    (h0 : ∀ y ∈ K, f t y ∈ W) :
    ∃ η : ℝ, 0 < η ∧ ∀ s ∈ Set.Icc a b, |s - t| ≤ η → ∀ y ∈ K, f s y ∈ W := by
  classical
  have hright : ∃ η : ℝ, 0 < η ∧ ∀ s ∈ Set.Icc t b, |s - t| ≤ η → ∀ y ∈ K, f s y ∈ W := by
    rcases lt_or_eq_of_le htb with hlt | heq
    · have hb : 0 < b - t := by linarith
      have hf' : ContinuousOn (fun p : ℝ × X => f p.1 p.2)
          (Set.Icc t (t + (b - t)) ×ˢ K) :=
        hf.mono (fun p hp => ⟨⟨le_trans hat hp.1.1, by linarith [hp.1.2]⟩, hp.2⟩)
      obtain ⟨η, hη, hη'⟩ := Work.Diff.MP.LM.exists_pos_forall_mem_of_isCompact (X := X) (Y := Y)
        hW hK hb hf' h0
      exact ⟨η, hη, fun s hs hs' y hy => hη' s ⟨hs.1, by linarith [hs.2]⟩ hs' y hy⟩
    · refine ⟨1, one_pos, fun s hs _ y hy => ?_⟩
      have hst : s = t := le_antisymm (heq ▸ hs.2) hs.1
      rw [hst]; exact h0 y hy
  have hleft : ∃ η : ℝ, 0 < η ∧ ∀ s ∈ Set.Icc a t, |s - t| ≤ η → ∀ y ∈ K, f s y ∈ W := by
    rcases lt_or_eq_of_le hat with hlt | heq
    · have hd : 0 < t - a := by linarith
      have hφcont : Continuous fun p : ℝ × X => (2 * t - p.1, p.2) :=
        (continuous_const.sub continuous_fst).prodMk continuous_snd
      have hφmap : Set.MapsTo (fun p : ℝ × X => (2 * t - p.1, p.2))
          (Set.Icc t (t + (t - a)) ×ˢ K) (Set.Icc a b ×ˢ K) :=
        fun p hp => ⟨⟨by linarith [hp.1.2], by linarith [hp.1.1, htb]⟩, hp.2⟩
      have hgc : ContinuousOn (fun p : ℝ × X => f (2 * t - p.1) p.2)
          (Set.Icc t (t + (t - a)) ×ˢ K) :=
        hf.comp hφcont.continuousOn hφmap
      obtain ⟨η, hη, hη'⟩ := Work.Diff.MP.LM.exists_pos_forall_mem_of_isCompact (X := X) (Y := Y)
        (f := fun s y => f (2 * t - s) y) hW hK hd hgc (fun y hy => by
          show f (2 * t - t) y ∈ W
          rw [show 2 * t - t = t by ring]
          exact h0 y hy)
      refine ⟨η, hη, fun s hs hs' y hy => ?_⟩
      have hmem : (2 * t - s) ∈ Set.Icc t (t + (t - a)) :=
        ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have habs : |2 * t - s - t| ≤ η := by
        rw [show 2 * t - s - t = -(s - t) by ring, abs_neg]; exact hs'
      have h := hη' (2 * t - s) hmem habs y hy
      simpa [show 2 * t - (2 * t - s) = s by ring] using h
    · refine ⟨1, one_pos, fun s hs _ y hy => ?_⟩
      have hst : s = t := le_antisymm hs.2 (heq ▸ hs.1)
      rw [hst]; exact h0 y hy
  obtain ⟨η₁, hη₁, hη₁'⟩ := hright
  obtain ⟨η₂, hη₂, hη₂'⟩ := hleft
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun s hs hs' y hy => ?_⟩
  rcases le_total s t with hst | hst
  · exact hη₂' s ⟨hs.1, hst⟩ (le_trans hs' (min_le_right _ _)) y hy
  · exact hη₁' s ⟨hst, hs.2⟩ (le_trans hs' (min_le_left _ _)) y hy


end Work.Diff.MP
