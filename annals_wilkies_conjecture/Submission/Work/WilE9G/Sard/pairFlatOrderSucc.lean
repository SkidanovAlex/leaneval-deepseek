import Mathlib
import Submission.Work.WilE2.FlatPart.pair_flatness_of_flatSet

/-!
# Pairwise flatness of order `j + 2` on the `(j+1)`-flat set (vector valued)

If `f : ℝᵈ → ℝᵏ` is `C^{j+2}` and all iterated derivatives of `f` of orders `1, …, j+1` vanish at
every point of a set `A`, then at every `x ∈ A` the function `f` is flat of order `j+2` along `A`,
with an arbitrarily small constant:

`‖f y - f x‖ ≤ ε ‖y - x‖^{j+2}`   for all `y ∈ A` close enough to `x`.

This is the vector-valued, order-shifted companion of `Work.WilE2.FlatPart.pair_flatness_of_flatSet`.

The point of the hypothesis on *both* endpoints is the following.  Taylor's formula for `f` at `x`
with integral remainder of order `j+1` gives, since the derivatives of orders `1, …, j+1` vanish
at `x`,

`f y - f x = ((j+1)!)⁻¹ ∫₀¹ (1-t)^{j+1} · D^{j+2}f (x + t(y-x)) (y-x,…,y-x) dt`,

whose integrand is *not* obviously small: it is of order `‖y-x‖^{j+2}` with a possibly non-zero
constant `D^{j+2}f x (y-x)^{j+2}`.  But since `y ∈ A` as well, `D^{j+1}f` vanishes at *both* ends,
so `D^{j+2}f x (y-x, …, y-x) = o(‖y-x‖^{j+2})` as `y → x` through `A` (differentiating
`D^{j+1}f` at `x`).  Together with the continuity of `D^{j+2}f` at `x` (uniformly along the
segment) the estimate follows.
-/

namespace Work.WilE9G.Sard

open MeasureTheory Filter

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

/-- `iteratedFDeriv` at order `n+1` applied to a constant tuple, in terms of `fderiv`. -/
private lemma iteratedFDeriv_succ_const {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {f : E → F} {x : E} (n : ℕ) (a : E) :
    (iteratedFDeriv 𝕜 (n + 1) f x) (fun _ : Fin (n + 1) => a) =
      ((fderiv 𝕜 (iteratedFDeriv 𝕜 n f) x) a) (fun _ : Fin n => a) := by
  rw [iteratedFDeriv_succ_apply_left]
  rfl

theorem pairFlatOrderSucc {d k j : ℕ} (f : (Fin d → ℝ) → (Fin k → ℝ))
    (hf : ContDiff ℝ (j + 2) f) (A : Set (Fin d → ℝ))
    (hA : A ⊆ {x : Fin d → ℝ | ∀ i, 1 ≤ i → i ≤ j + 1 → iteratedFDeriv ℝ i f x = 0}) :
    ∀ x ∈ A, ∀ ε > 0, ∃ ρ > 0, ∀ y ∈ A, ‖y - x‖ ≤ ρ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ (j + 2) := by
  intro x hxA ε hε
  set η : ℝ := ε * (Nat.factorial (j + 1) : ℝ) / 2 with hηdef
  have hηpos : 0 < η := by rw [hηdef]; positivity
  have hxflat : ∀ i, 1 ≤ i → i ≤ j + 1 → iteratedFDeriv ℝ i f x = 0 := hA hxA
  -- STEP A: the `(j+2)`-nd iterated derivative is continuous at `x`.
  have hcontD : ContinuousAt (fun z : Fin d → ℝ => iteratedFDeriv ℝ (j + 2) f z) x :=
    hf.continuous_iteratedFDeriv'.continuousAt
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ z : Fin d → ℝ, ‖z - x‖ ≤ δ →
      ‖iteratedFDeriv ℝ (j + 2) f z - iteratedFDeriv ℝ (j + 2) f x‖ ≤ η := by
    rw [Metric.continuousAt_iff] at hcontD
    obtain ⟨δ, hδpos, hδ⟩ := hcontD η hηpos
    refine ⟨δ / 2, by linarith, fun z hz => ?_⟩
    have hlt : dist z x < δ := by rw [dist_eq_norm]; linarith
    have h := hδ hlt
    rw [dist_eq_norm] at h
    exact le_of_lt h
  -- STEP B: the top Taylor coefficient of `f` at `x` is `o(‖y-x‖^{j+2})` along `A`.
  obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ A, ‖y - x‖ ≤ ρ →
      ‖(iteratedFDeriv ℝ (j + 2) f x) (fun _ : Fin (j + 2) => y - x)‖
        ≤ η * ‖y - x‖ ^ (j + 2) := by
    have hgdiff : Differentiable ℝ (iteratedFDeriv ℝ (j + 1) f) :=
      hf.differentiable_iteratedFDeriv (by exact_mod_cast (Nat.lt_succ_self (j + 1)))
    have hL : HasFDerivAt (iteratedFDeriv ℝ (j + 1) f)
        (fderiv ℝ (iteratedFDeriv ℝ (j + 1) f) x) x :=
      hgdiff.differentiableAt.hasFDerivAt
    have hlittle := hL.isLittleO
    rw [Asymptotics.isLittleO_iff] at hlittle
    have hevent := hlittle hηpos
    rw [Metric.eventually_nhds_iff] at hevent
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := hevent
    refine ⟨δ₂ / 2, by linarith, fun y hyA hy => ?_⟩
    have hylt : dist y x < δ₂ := by rw [dist_eq_norm]; linarith
    have hkey := hδ₂ hylt
    have hgy : iteratedFDeriv ℝ (j + 1) f y = 0 := hA hyA (j + 1) (by omega) le_rfl
    have hgx : iteratedFDeriv ℝ (j + 1) f x = 0 := hxflat (j + 1) (by omega) le_rfl
    rw [hgy, hgx] at hkey
    simp only [sub_zero, zero_sub, norm_neg] at hkey
    rw [iteratedFDeriv_succ_const (f := f) (x := x) (j + 1) (y - x)]
    calc ‖((fderiv ℝ (iteratedFDeriv ℝ (j + 1) f) x) (y - x)) (fun _ : Fin (j + 1) => y - x)‖
        ≤ ‖(fderiv ℝ (iteratedFDeriv ℝ (j + 1) f) x) (y - x)‖ * ‖y - x‖ ^ (j + 1) :=
          ContinuousMultilinearMap.le_opNorm_mul_pow_of_le _
            (le_of_eq (norm_const_fin j (y - x)))
      _ ≤ (η * ‖y - x‖) * ‖y - x‖ ^ (j + 1) :=
          mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = η * ‖y - x‖ ^ (j + 2) := by
          rw [show (j + 2) = (j + 1) + 1 by omega, pow_succ]; ring
  refine ⟨min δ₁ ρ₁, lt_min hδ₁pos hρ₁pos, fun y hyA hyρ => ?_⟩
  have hyδ₁ : ‖y - x‖ ≤ δ₁ := le_trans hyρ (min_le_left _ _)
  have hyρ₁ : ‖y - x‖ ≤ ρ₁ := le_trans hyρ (min_le_right _ _)
  set h : Fin d → ℝ := y - x with hhdef
  have hnormh : ‖h‖ = ‖y - x‖ := by rw [hhdef]
  -- STEP C: Taylor's formula with integral remainder, order `j+1`.
  have hcont_at : ∀ t ∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ ((↑(j + 1) : WithTop ℕ∞) + 1) f (x + t • h) :=
    fun t _ => by
      have hcast : ((↑(j + 1) : WithTop ℕ∞) + 1) = ↑(j + 2) := by push_cast; ring
      rw [hcast]
      exact hf.contDiffAt
  have htaylor :=
    map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := x) (y := h) (n := j + 1) hcont_at
  have hxy : x + h = y := by rw [hhdef]; abel
  rw [hxy] at htaylor
  -- the Taylor sum collapses to its constant term.
  have hsum : (∑ k ∈ Finset.range (j + 2), ((k.factorial : ℝ))⁻¹ •
      (iteratedFDeriv ℝ k f x) (fun _ => h)) = f x := by
    rw [Finset.sum_eq_single 0]
    · rw [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, iteratedFDeriv_zero_apply]
    · intro b hb hb0
      have h1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb0
      have h2 : b ≤ j + 1 := by rw [Finset.mem_range] at hb; omega
      rw [hxflat b h1 h2, zero_apply, smul_zero]
    · intro h0
      exact absurd (Finset.mem_range.mpr (by omega : 0 < j + 2)) h0
  rw [hsum] at htaylor
  set J : Fin k → ℝ := ∫ t in (0:ℝ)..1, (1 - t) ^ (j + 1) •
      (iteratedFDeriv ℝ (j + 2) f (x + t • h)) (fun _ : Fin (j + 2) => h) with hJdef
  have hdiff : f y - f x = ((Nat.factorial (j + 1) : ℝ))⁻¹ • J := by
    rw [htaylor, hJdef]; abel
  -- pointwise bound on the integrand.
  have hpoint : ∀ t ∈ Set.uIoc (0:ℝ) 1,
      ‖(1 - t) ^ (j + 1) • (iteratedFDeriv ℝ (j + 2) f (x + t • h)) (fun _ : Fin (j + 2) => h)‖
        ≤ 2 * η * ‖h‖ ^ (j + 2) := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have ht1 : (0:ℝ) < t := ht.1
    have ht2 : t ≤ 1 := ht.2
    have h1t : 0 ≤ 1 - t := by linarith
    -- the point `x + t • h` is within `δ₁` of `x`.
    have hzδ : ‖x + t • h - x‖ ≤ δ₁ := by
      have hsub : x + t • h - x = t • h := by abel
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt ht1)]
      calc t * ‖h‖ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right ht2 (norm_nonneg _)
        _ = ‖h‖ := one_mul _
        _ = ‖y - x‖ := hnormh
        _ ≤ δ₁ := hyδ₁
    -- the difference term.
    have hEm : ‖(iteratedFDeriv ℝ (j + 2) f (x + t • h) - iteratedFDeriv ℝ (j + 2) f x)
        (fun _ : Fin (j + 2) => h)‖ ≤ η * ‖h‖ ^ (j + 2) :=
      calc ‖(iteratedFDeriv ℝ (j + 2) f (x + t • h) - iteratedFDeriv ℝ (j + 2) f x)
              (fun _ : Fin (j + 2) => h)‖
          ≤ ‖iteratedFDeriv ℝ (j + 2) f (x + t • h) - iteratedFDeriv ℝ (j + 2) f x‖
              * ‖h‖ ^ (j + 2) :=
            ContinuousMultilinearMap.le_opNorm_mul_pow_of_le _
              (le_of_eq (norm_const_fin (j + 1) h))
        _ ≤ η * ‖h‖ ^ (j + 2) := mul_le_mul_of_nonneg_right (hδ₁ _ hzδ) (by positivity)
    -- the constant term (Step B).
    have hL : ‖(iteratedFDeriv ℝ (j + 2) f x) (fun _ : Fin (j + 2) => h)‖ ≤ η * ‖h‖ ^ (j + 2) := by
      have hthis := hρ₁ y hyA hyρ₁
      rwa [← hhdef] at hthis
    have hu : ‖(iteratedFDeriv ℝ (j + 2) f (x + t • h)) (fun _ : Fin (j + 2) => h)‖
        ≤ 2 * η * ‖h‖ ^ (j + 2) := by
      have hsplit : (iteratedFDeriv ℝ (j + 2) f (x + t • h)) (fun _ : Fin (j + 2) => h)
          = ((iteratedFDeriv ℝ (j + 2) f (x + t • h) - iteratedFDeriv ℝ (j + 2) f x)
                (fun _ : Fin (j + 2) => h))
            + (iteratedFDeriv ℝ (j + 2) f x) (fun _ : Fin (j + 2) => h) := by
        rw [← add_apply, sub_add_cancel]
      calc ‖(iteratedFDeriv ℝ (j + 2) f (x + t • h)) (fun _ : Fin (j + 2) => h)‖
          = ‖((iteratedFDeriv ℝ (j + 2) f (x + t • h) - iteratedFDeriv ℝ (j + 2) f x)
                (fun _ : Fin (j + 2) => h))
              + (iteratedFDeriv ℝ (j + 2) f x) (fun _ : Fin (j + 2) => h)‖ := by rw [hsplit]
        _ ≤ ‖(iteratedFDeriv ℝ (j + 2) f (x + t • h) - iteratedFDeriv ℝ (j + 2) f x)
                (fun _ : Fin (j + 2) => h)‖
              + ‖(iteratedFDeriv ℝ (j + 2) f x) (fun _ : Fin (j + 2) => h)‖ := norm_add_le _ _
        _ ≤ η * ‖h‖ ^ (j + 2) + η * ‖h‖ ^ (j + 2) := add_le_add hEm hL
        _ = 2 * η * ‖h‖ ^ (j + 2) := by ring
    have hle1 : (1 - t) ^ (j + 1) ≤ 1 := pow_le_one₀ h1t (by linarith)
    calc ‖(1 - t) ^ (j + 1) • (iteratedFDeriv ℝ (j + 2) f (x + t • h)) (fun _ : Fin (j + 2) => h)‖
        = (1 - t) ^ (j + 1)
            * ‖(iteratedFDeriv ℝ (j + 2) f (x + t • h)) (fun _ : Fin (j + 2) => h)‖ := by
          rw [norm_smul, Real.norm_of_nonneg (pow_nonneg h1t _)]
      _ ≤ 1 * (2 * η * ‖h‖ ^ (j + 2)) :=
          mul_le_mul hle1 hu (norm_nonneg _) (by positivity)
      _ = 2 * η * ‖h‖ ^ (j + 2) := one_mul _
  -- bound the remainder integral.
  have hJbound : ‖J‖ ≤ 2 * η * ‖h‖ ^ (j + 2) := by
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
      (C := 2 * η * ‖h‖ ^ (j + 2)) hpoint
    rw [hJdef]
    simpa using hle
  -- assemble.
  rw [hdiff, norm_smul,
    Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ((Nat.factorial (j + 1) : ℝ))⁻¹)]
  calc ((Nat.factorial (j + 1) : ℝ))⁻¹ * ‖J‖
      ≤ ((Nat.factorial (j + 1) : ℝ))⁻¹ * (2 * η * ‖h‖ ^ (j + 2)) :=
        mul_le_mul_of_nonneg_left hJbound (by positivity)
    _ = ε * ‖h‖ ^ (j + 2) := by
        rw [hηdef]
        field_simp

end

end Work.WilE9G.Sard
