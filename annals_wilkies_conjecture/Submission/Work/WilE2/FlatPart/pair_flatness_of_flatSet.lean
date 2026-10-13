import Mathlib
import Submission.Work.WilE2.SardDefs
import Submission.Work.WilE2.flatSet_top_peano
import Submission.Work.WilE2.FlatPart.flatSet_taylor_integral

/-!
# Pairwise flatness of order `j + 1` on a subset of `flatSet f j`

If `f : ℝⁿ → ℝ` is of class `C^{j+1}` and `A ⊆ flatSet f j` (all iterated derivatives of `f` of
orders `1, …, j` vanish at every point of `A`), then at every `x ∈ A` the function `f` is flat of
order `j + 1` *along `A`*, with an arbitrarily small constant:

`‖f y - f x‖ ≤ ε ‖y - x‖^{j+1}`   for all `y ∈ A` close enough to `x`.

The point of the hypothesis on *both* endpoints is the following.  Taylor's formula for `f` at `x`
with integral remainder gives, since the derivatives of orders `1, …, j` vanish at `x`,

`f y - f x = (j!)⁻¹ ∫₀¹ (1-t)^j · D^{j+1}f (x + t(y-x)) (y-x,…,y-x) dt`,

whose integrand is *not* obviously small: it is of order `‖y-x‖^{j+1}` with a possibly non-zero
constant `D^{j+1}f x (y-x)^{j+1}`.  But since `y ∈ flatSet f j` as well, the curve
`t ↦ D^j f (x + t(y-x)) (y-x,…,y-x)` vanishes at *both* ends, so
`D^{j+1}f x (y-x)^{j+1} = -∫₀¹ [D^{j+1}f(x+t(y-x)) - D^{j+1}f x](y-x)^{j+1} dt`, which is
`o(‖y-x‖^{j+1})` by continuity of the `(j+1)`-st derivative at `x` (private lemma
`top_deriv_peano`).  Together with the continuity bound on the integrand (that same continuity,
uniformly along the segment) the estimate follows.

The case `j = 0` is false (`flatSet f 0 = univ`, take `f = id`), whence the hypothesis `1 ≤ j`.
-/

namespace Work.WilE2.FlatPart

open MeasureTheory Filter
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

/-- The norm of a constant `Fin (k+1)`-tuple of a normed group. -/
private lemma norm_const_fin {E : Type*} [SeminormedAddCommGroup E] (k : ℕ) (h : E) :
    ‖(fun _ : Fin (k + 1) => h)‖ = ‖h‖ := by
  refine le_antisymm ?_ (norm_le_pi_norm (fun _ : Fin (k + 1) => h) 0)
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg h)]
  intro i
  rfl

/-- The norm of a constant `Fin k`-tuple, given a witness that `Fin k` is nonempty. -/
private lemma norm_const_fin_of {E : Type*} [SeminormedAddCommGroup E] {k : ℕ} (i : Fin k)
    (h : E) : ‖(fun _ : Fin k => h)‖ = ‖h‖ := by
  refine le_antisymm ?_ (norm_le_pi_norm (fun _ : Fin k => h) i)
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg h)]
  intro l
  rfl

/-- **The top Taylor coefficient at a point of `flatSet f j` is `o(‖y-x‖^{j+1})` along
`flatSet f j`.**

Both `x` and `y` belong to `flatSet f j`, so the curve `z ↦ D^j f z` vanishes at both ends of the
segment and `D^{j+1}f x (y-x)^{…} = -∫₀¹ [D^{j+1}f(x+t(y-x)) - D^{j+1}f x](y-x)^{…} dt`, whence the
claim by continuity of the `(j+1)`-st derivative at `x`.  This is proved through the
differentiability of `z ↦ D^j f z` at `x`, whose derivative is the currying of `D^{j+1}f x`. -/
private lemma top_deriv_peano {n j : ℕ} (hj : 1 ≤ j) (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) f) {x : Fin n → ℝ} (hx : x ∈ flatSet f j) :
    ∀ ε > 0, ∃ ρ > 0, ∀ y ∈ flatSet f j, ‖y - x‖ ≤ ρ →
      ‖(iteratedFDeriv ℝ (j + 1) f x) (fun _ : Fin (j + 1) => y - x)‖
        ≤ ε * ‖y - x‖ ^ (j + 1) := by
  intro ε hε
  have hx' : ∀ i, 1 ≤ i → i ≤ j → iteratedFDeriv ℝ i f x = 0 := hx
  -- `z ↦ D^j f z` is differentiable at `x`
  have hdiff : DifferentiableAt ℝ (fun z : Fin n → ℝ => iteratedFDeriv ℝ j f z) x := by
    refine hf.contDiffAt.differentiableAt_iteratedFDeriv ?_
    exact_mod_cast Nat.lt_succ_self j
  -- the differentiability remainder is `o(‖z-x‖)`
  have hlit : (fun z : Fin n → ℝ => iteratedFDeriv ℝ j f z - iteratedFDeriv ℝ j f x
        - (fderiv ℝ (fun z : Fin n → ℝ => iteratedFDeriv ℝ j f z) x) (z - x))
      =o[𝓝 x] (fun z : Fin n → ℝ => z - x) := hdiff.hasFDerivAt.isLittleO
  rw [Asymptotics.isLittleO_iff] at hlit
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ z : Fin n → ℝ, dist z x < δ →
      ‖iteratedFDeriv ℝ j f z - iteratedFDeriv ℝ j f x
        - (fderiv ℝ (fun z : Fin n → ℝ => iteratedFDeriv ℝ j f z) x) (z - x)‖
          ≤ ε * ‖z - x‖ :=
    Metric.eventually_nhds_iff.mp (hlit hε)
  refine ⟨δ / 2, by linarith, fun y hy hρ => ?_⟩
  have hy' : ∀ i, 1 ≤ i → i ≤ j → iteratedFDeriv ℝ i f y = 0 := hy
  have hyd : dist y x < δ := by rw [dist_eq_norm]; linarith
  have hR := hδ y hyd
  have hGx : iteratedFDeriv ℝ j f x = 0 := hx' j hj le_rfl
  have hGy : iteratedFDeriv ℝ j f y = 0 := hy' j hj le_rfl
  -- `D^j f` vanishes at both ends, so the linear map `d(D^j f)(x)` is small at `y - x`
  have hdG : ‖(fderiv ℝ (fun z : Fin n → ℝ => iteratedFDeriv ℝ j f z) x) (y - x)‖
      ≤ ε * ‖y - x‖ := by
    rw [hGy, hGx, sub_self, zero_sub, norm_neg] at hR
    exact hR
  -- `D^{j+1}f x (y-x)^{…}` is that linear map evaluated at the constant tuple
  have hident : (iteratedFDeriv ℝ (j + 1) f x) (fun _ : Fin (j + 1) => y - x)
      = ((fderiv ℝ (fun z : Fin n → ℝ => iteratedFDeriv ℝ j f z) x) (y - x))
          (fun _ : Fin j => y - x) := by
    rw [iteratedFDeriv_succ_apply_left]
    rfl
  calc ‖(iteratedFDeriv ℝ (j + 1) f x) (fun _ : Fin (j + 1) => y - x)‖
      = ‖((fderiv ℝ (fun z : Fin n → ℝ => iteratedFDeriv ℝ j f z) x) (y - x))
            (fun _ : Fin j => y - x)‖ := by rw [hident]
    _ ≤ ‖(fderiv ℝ (fun z : Fin n → ℝ => iteratedFDeriv ℝ j f z) x) (y - x)‖ * ‖y - x‖ ^ j :=
        ContinuousMultilinearMap.le_opNorm_mul_pow_of_le _
          (le_of_eq (norm_const_fin_of (⟨0, hj⟩ : Fin j) (y - x)))
    _ ≤ (ε * ‖y - x‖) * ‖y - x‖ ^ j := mul_le_mul_of_nonneg_right hdG (by positivity)
    _ = ε * ‖y - x‖ ^ (j + 1) := by rw [pow_succ']; ring

theorem pair_flatness_of_flatSet {n j : ℕ} (hj : 1 ≤ j) (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) f) (A : Set (Fin n → ℝ))
    (hA : A ⊆ flatSet f j) :
    ∀ x ∈ A, ∀ ε > 0, ∃ ρ > 0, ∀ y ∈ A, ‖y - x‖ ≤ ρ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ (j + 1) := by
  intro x hxA ε hε
  have hfact_pos : (0 : ℝ) < (Nat.factorial j : ℝ) := by positivity
  have hfact_ne : (Nat.factorial j : ℝ) ≠ 0 := ne_of_gt hfact_pos
  -- The single constant `η` controlling both error terms.
  set η : ℝ := ε * (Nat.factorial j : ℝ) / 2 with hηdef
  have hηpos : 0 < η := by rw [hηdef]; positivity
  -- STEP 1: the `(j+1)`-st iterated derivative is continuous at `x`.
  have hcontD : ContinuousAt (fun z : Fin n → ℝ => iteratedFDeriv ℝ (j + 1) f z) x :=
    hf.continuous_iteratedFDeriv'.continuousAt
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ z : Fin n → ℝ, ‖z - x‖ ≤ δ →
      ‖iteratedFDeriv ℝ (j + 1) f z - iteratedFDeriv ℝ (j + 1) f x‖ ≤ η := by
    rw [Metric.continuousAt_iff] at hcontD
    obtain ⟨δ, hδpos, hδ⟩ := hcontD η hηpos
    refine ⟨δ / 2, by linarith, fun z hz => ?_⟩
    have hlt : dist z x < δ := by rw [dist_eq_norm]; linarith
    have h := hδ hlt
    rw [dist_eq_norm] at h
    exact le_of_lt h
  -- STEP 2: the top Taylor coefficient of `f` at `x` is `o(‖y-x‖^{j+1})` along `flatSet f j`.
  obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ flatSet f j, ‖y - x‖ ≤ ρ →
      ‖(iteratedFDeriv ℝ (j + 1) f x) (fun _ : Fin (j + 1) => y - x)‖
        ≤ η * ‖y - x‖ ^ (j + 1) :=
    top_deriv_peano hj f hf (hA hxA) η hηpos
  refine ⟨min δ₁ ρ₁, lt_min hδ₁pos hρ₁pos, fun y hyA hyρ => ?_⟩
  have hhδ₁ : ‖y - x‖ ≤ δ₁ := le_trans hyρ (min_le_left _ _)
  have hhρ₁ : ‖y - x‖ ≤ ρ₁ := le_trans hyρ (min_le_right _ _)
  set h : Fin n → ℝ := y - x with hhdef
  have hnorm : ‖h‖ = ‖y - x‖ := by rw [hhdef]
  have hhδ₁' : ‖h‖ ≤ δ₁ := by rw [hnorm]; exact hhδ₁
  -- STEP 3: the top Taylor coefficient of `f` at `x`, evaluated at `h`.
  have hL : ‖(iteratedFDeriv ℝ (j + 1) f x) (fun _ : Fin (j + 1) => h)‖ ≤ η * ‖h‖ ^ (j + 1) := by
    have hthis := hρ₁ y (hA hyA) hhρ₁
    rw [← hhdef] at hthis
    exact hthis
  -- STEP 4: Taylor's formula with integral remainder, the derivatives of orders `1, …, j` at `x`
  -- vanish, so only the remainder survives.
  have htaylor : f y - f x = ((Nat.factorial j : ℝ))⁻¹ * ∫ t in (0:ℝ)..1,
      (1 - t) ^ j * (iteratedFDeriv ℝ (j + 1) f (x + t • h)) (fun _ : Fin (j + 1) => h) := by
    have h0 := flatSet_taylor_integral (j := j) (x := x) (y := y) f hf (hA hxA)
    rw [← hhdef] at h0
    exact h0
  -- STEP 5: pointwise bound for the integrand.
  have hpoint : ∀ t ∈ Set.uIoc (0:ℝ) 1,
      ‖(1 - t) ^ j * (iteratedFDeriv ℝ (j + 1) f (x + t • h)) (fun _ : Fin (j + 1) => h)‖
        ≤ 2 * η * ‖h‖ ^ (j + 1) := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht1 : (0 : ℝ) < t := ht.1
    have ht2 : t ≤ 1 := ht.2
    have h1t : 0 ≤ 1 - t := by linarith
    -- the point `x + t • h` is within `δ₁` of `x`
    have hzδ : ‖x + t • h - x‖ ≤ δ₁ := by
      have hsub : x + t • h - x = t • h := by abel
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt ht1)]
      nlinarith [norm_nonneg h, hhδ₁']
    -- the difference of the two top derivatives, applied to `h, …, h`
    have hEm : ‖(iteratedFDeriv ℝ (j + 1) f (x + t • h) - iteratedFDeriv ℝ (j + 1) f x)
        (fun _ : Fin (j + 1) => h)‖ ≤ η * ‖h‖ ^ (j + 1) :=
      calc ‖(iteratedFDeriv ℝ (j + 1) f (x + t • h) - iteratedFDeriv ℝ (j + 1) f x)
              (fun _ : Fin (j + 1) => h)‖
          ≤ ‖iteratedFDeriv ℝ (j + 1) f (x + t • h) - iteratedFDeriv ℝ (j + 1) f x‖
              * ‖h‖ ^ (j + 1) :=
            ContinuousMultilinearMap.le_opNorm_mul_pow_of_le _ (le_of_eq (norm_const_fin j h))
        _ ≤ η * ‖h‖ ^ (j + 1) :=
            mul_le_mul_of_nonneg_right (hδ₁ _ hzδ) (by positivity)
    have hu : ‖(iteratedFDeriv ℝ (j + 1) f (x + t • h)) (fun _ : Fin (j + 1) => h)‖
        ≤ 2 * η * ‖h‖ ^ (j + 1) := by
      have hsplit : (iteratedFDeriv ℝ (j + 1) f (x + t • h)) (fun _ : Fin (j + 1) => h)
          = ((iteratedFDeriv ℝ (j + 1) f (x + t • h) - iteratedFDeriv ℝ (j + 1) f x)
                (fun _ : Fin (j + 1) => h))
            + (iteratedFDeriv ℝ (j + 1) f x) (fun _ : Fin (j + 1) => h) := by
        rw [← add_apply, sub_add_cancel]
      calc ‖(iteratedFDeriv ℝ (j + 1) f (x + t • h)) (fun _ : Fin (j + 1) => h)‖
          = ‖((iteratedFDeriv ℝ (j + 1) f (x + t • h) - iteratedFDeriv ℝ (j + 1) f x)
                (fun _ : Fin (j + 1) => h))
              + (iteratedFDeriv ℝ (j + 1) f x) (fun _ : Fin (j + 1) => h)‖ := by rw [hsplit]
        _ ≤ ‖(iteratedFDeriv ℝ (j + 1) f (x + t • h) - iteratedFDeriv ℝ (j + 1) f x)
                (fun _ : Fin (j + 1) => h)‖
              + ‖(iteratedFDeriv ℝ (j + 1) f x) (fun _ : Fin (j + 1) => h)‖ := norm_add_le _ _
        _ ≤ η * ‖h‖ ^ (j + 1) + η * ‖h‖ ^ (j + 1) := add_le_add hEm hL
        _ = 2 * η * ‖h‖ ^ (j + 1) := by ring
    have hle1 : (1 - t) ^ j ≤ 1 := pow_le_one₀ h1t (by linarith)
    calc ‖(1 - t) ^ j * (iteratedFDeriv ℝ (j + 1) f (x + t • h)) (fun _ : Fin (j + 1) => h)‖
        = (1 - t) ^ j
            * ‖(iteratedFDeriv ℝ (j + 1) f (x + t • h)) (fun _ : Fin (j + 1) => h)‖ := by
          rw [norm_mul, Real.norm_of_nonneg (pow_nonneg h1t j)]
      _ ≤ 1 * (2 * η * ‖h‖ ^ (j + 1)) :=
          mul_le_mul hle1 hu (norm_nonneg _) (by positivity)
      _ = 2 * η * ‖h‖ ^ (j + 1) := one_mul _
  -- STEP 6: bound the remainder integral.
  have hIbound : ‖∫ t in (0:ℝ)..1,
      (1 - t) ^ j * (iteratedFDeriv ℝ (j + 1) f (x + t • h)) (fun _ : Fin (j + 1) => h)‖
        ≤ 2 * η * ‖h‖ ^ (j + 1) := by
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
      (C := 2 * η * ‖h‖ ^ (j + 1)) hpoint
    simpa using hle
  -- STEP 7: assemble.
  calc ‖f y - f x‖
      = ((Nat.factorial j : ℝ))⁻¹ * ‖∫ t in (0:ℝ)..1,
          (1 - t) ^ j * (iteratedFDeriv ℝ (j + 1) f (x + t • h)) (fun _ : Fin (j + 1) => h)‖ := by
        rw [htaylor, norm_mul,
          Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ((Nat.factorial j : ℝ))⁻¹)]
    _ ≤ ((Nat.factorial j : ℝ))⁻¹ * (2 * η * ‖h‖ ^ (j + 1)) :=
        mul_le_mul_of_nonneg_left hIbound (by positivity)
    _ = ε * ‖y - x‖ ^ (j + 1) := by
        rw [← hnorm, hηdef]
        field_simp

end

end Work.WilE2.FlatPart
