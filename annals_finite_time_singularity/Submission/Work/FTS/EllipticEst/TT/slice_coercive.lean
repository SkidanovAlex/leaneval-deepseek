/-
Copyright: work module for the Elgindi finite-time singularity project.

# Slicewise angular coercivity `Ptheta α m u ≤ C (Ptheta α m u'' + Ptheta α m (Lzero1 u))`

This is the *slice* form of the angular coercivity used by the elliptic estimates of the
self-similar Euler chapter: for a smooth slice `u` on a neighbourhood of `[0, π/2]` vanishing
at both endpoints, the angular `ℋ^m` functional

  `Ptheta α m u = ∫_θ u² sin(2θ)^{-η} + ∑_{i=1}^{m} ∫_θ (D_θ^i u)² sin(2θ)^{-γ}`

is dominated by the same functional applied to the second derivative `u''` and to
`Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u` (the `α = 0` angular part of the Biot–Savart
operator).  The two `PthetaMem` hypotheses are the honesty conditions making the finitely many
integrals non-junk (they are in fact automatic, see `TT.PthetaMem_of_smooth`).

## Structure of the proof

The argument is *triangular in the number of angular derivatives*.  Writing

* `Hη u = ∫_θ u² sin(2θ)^{-η}`,   `Gη u = ∫_θ (u'')² sin(2θ)^{-η}`,
* `Fη u = ∫_θ (Lzero1 u)² sin(2θ)^{-η}`,   `Gγ α i u = ∫_θ (D_θ^i u)² sin(2θ)^{-γ}`,

the three delegated inputs are

* `Hη_le_of_deriv_bound` (below) : `Hη u ≤ C₀ Gη u`.  The pointwise bound
  `(u' θ)² ≤ Gη u · (π/2)` is `slice_deriv_sq_le` (Rolle, since `u` has the same value at the
  two endpoints, plus Cauchy–Schwarz on the slice); `abs_le_sin_mul_of_deriv_bound` turns it
  into `|u θ| ≤ (π/4) sin(2θ) M` with `M = √(Gη u · π/2)`, and `Heta_le_of_sin_bound`
  integrates this against the singular weight `sEta`;
* `TT.first_iter_le_u` : `Gγ α 1 u ≤ C₁ (Gη u + Fη u)`.  By `Lzero_self_form`,
  `∫ Lzero1 u · u = ∫ (u')² + (1/2)∫ (u/cos θ)² - 6∫u²`, so
  `∫(u')² ≤ ∫(Lzero1 u)·u + 6∫u²`
  and both terms are bounded by `Fη u` and `Gη u` through Cauchy–Schwarz and the `Hη` bound;
  finally `(D_θ u)² sin(2θ)^{-γ} = (u')² sin(2θ)^{2-γ} ≤ (u')²`;
* `TT.iter_le_of_lower_u` : for `i ≥ 2`,
  `Gγ α i u ≤ K i (Gη u + ∑_{k ≤ i-2} Gγ α k (u'') + ∑_{k ≤ i-1} Gγ α k u)`, from the identity
  `D_θ(D_θ u) = sin(2θ)² u'' + 2 cos(2θ) D_θ u` and the Leibniz rule of the derivation `D_θ`.

The triangular system is then solved by the elementary recursion
`b₁ = C₁`, `bᵢ = Kᵢ (1 + b₁ + … + b_{i-1})`, i.e. `b₁ + … + b_m = ∏_{i ≤ m}(1 + bᵢ/Kᵢ) - 1`, so
that `∑_{i ≤ m} Gγ α i u ≤ (∏_{i ≤ m} (1 + K'_i) - 1) S`, where `K'_1 = C₁`, `K'_i = K i`
(`i ≥ 2`) and `S = Gη u + Fη u + ∑_{k ≤ m} Gγ α k (u'')`.  Since `S` is (up to non-negative
summands) exactly `Ptheta α m u'' + Ptheta α m (Lzero1 u)`, the theorem follows.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.FTS.EllipticEst.TT.SliceCoercDefs
import Submission.Work.FTS.EllipticEst.TT.Heta_le_of_sin_bound
import Submission.Work.FTS.EllipticEst.TT.abs_le_sin_mul_of_deriv_bound
import Submission.Work.FTS.EllipticEst.slice_deriv_sq_le
import Submission.Work.FTS.EllipticEst.TT.first_iter_le_u
import Submission.Work.FTS.EllipticEst.TT.iter_le_of_lower_u
import Submission.Work.FTS.EllipticEst.TT.PthetaMem_of_smooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The integrals are non-negative -/

private theorem Hη_nonneg (u : ℝ → ℝ) : 0 ≤ Hη u :=
  integral_nonneg_of_ae (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))

private theorem Gη_nonneg (u : ℝ → ℝ) : 0 ≤ Gη u :=
  integral_nonneg_of_ae (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))

private theorem Fη_nonneg (u : ℝ → ℝ) : 0 ≤ Fη u :=
  integral_nonneg_of_ae (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))

private theorem Gγ_nonneg (α : ℝ) (i : ℕ) (u : ℝ → ℝ) : 0 ≤ Gγ α i u :=
  integral_nonneg_of_ae (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (sGam_nonneg α hθ))

/-- `1 ≤ ∏_{i=1}^{m}(1 + K i)` when every `K i` is positive. -/
private theorem one_le_prod_Icc (K : ℕ → ℝ) (h : ∀ i, 0 < K i) (m : ℕ) :
    (1 : ℝ) ≤ ∏ i ∈ Finset.Icc 1 m, (1 + K i) := by
  induction m with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ N + 1)]
    have hA : 0 ≤ ∏ i ∈ Finset.Icc 1 N, (1 + K i) :=
      Finset.prod_nonneg (fun i _ => by linarith [h i])
    have hB : (1 : ℝ) ≤ 1 + K (N + 1) := by linarith [h (N + 1)]
    calc (1 : ℝ) ≤ (∏ i ∈ Finset.Icc 1 N, (1 + K i)) * 1 := by rw [mul_one]; exact ih
      _ ≤ (∏ i ∈ Finset.Icc 1 N, (1 + K i)) * (1 + K (N + 1)) :=
          mul_le_mul_of_nonneg_left hB hA

/-- The `i = 0` term of `Ptheta` is dominated by the second derivative: `Hη u ≤ C Gη u`.

The pointwise bound `(u' θ)² ≤ Gη u · (π/2)` is the Rolle + Cauchy–Schwarz estimate
`slice_deriv_sq_le` (the two endpoint values of `u` agree), which through
`abs_le_sin_mul_of_deriv_bound` gives `|u θ| ≤ (π/4) sin(2θ) M` with `M = √(Gη u · π/2)`, and
finally `Heta_le_of_sin_bound` integrates this against the weight `sEta`. -/
private theorem Hη_le_of_deriv_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (u : ℝ → ℝ), Work.Elliptic.SmoothSlice u → u 0 = 0 → u (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn (fun θ => (D2 u θ) ^ 2 * sEta θ) Work.Spaces.Iθ →
      Hη u ≤ C * Gη u := by
  refine ⟨(Real.pi / 4) ^ 2 * (Real.pi / 2) * (Real.pi / 2), by positivity, ?_⟩
  intro u hu h0 h1 hI
  have hGnn : 0 ≤ Gη u := Gη_nonneg u
  -- the integrability hypothesis in the vocabulary of `slice_deriv_sq_le`
  have hint : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ := by
    simpa only [Work.FTS.EllipticEst.sliceV, Work.FTS.EllipticEst.thEta, D2, sEta] using hI
  have hmom : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
      ≤ Real.pi / 2 :=
    (Work.FTS.EllipticEst.integrableOn_sin_two_rpow Work.Spaces.eta_nonneg).2
  -- the pointwise bound `(u')² ≤ Gη u · (π/2)`
  have hdsq : ∀ θ ∈ Work.Spaces.Iθ, (deriv u θ) ^ 2 ≤ Gη u * (Real.pi / 2) := by
    intro θ hθ
    have h1' := Work.FTS.EllipticEst.slice_deriv_sq_le hu (by rw [h0, h1]) hint θ hθ
    have hG : (∫ θ in Work.Spaces.Iθ,
          (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) = Gη u := rfl
    rw [hG] at h1'
    exact le_trans h1' (mul_le_mul_of_nonneg_left hmom hGnn)
  -- the derivative bound with `M := √(Gη u · π/2)`
  set M : ℝ := Real.sqrt (Gη u * (Real.pi / 2)) with hMdef
  have hMnn : 0 ≤ M := Real.sqrt_nonneg _
  have hderiv : ∀ θ ∈ Work.Spaces.Iθ, |deriv u θ| ≤ M := by
    intro θ hθ
    have h := hdsq θ hθ
    rw [← sq_abs (deriv u θ)] at h
    rw [← Real.sqrt_sq (abs_nonneg (deriv u θ))]
    exact Real.sqrt_le_sqrt h
  -- the pointwise bound on `u` itself
  have hu_bound : ∀ θ ∈ Work.Spaces.Iθ, |u θ| ≤ (Real.pi / 4 * M) * Real.sin (2 * θ) := by
    intro θ hθ
    have h := abs_le_sin_mul_of_deriv_bound hu h0 h1 hMnn hderiv θ hθ
    calc |u θ| ≤ (Real.pi / 4) * Real.sin (2 * θ) * M := h
      _ = (Real.pi / 4 * M) * Real.sin (2 * θ) := by ring
  -- integrate against the weight
  have hK : 0 ≤ Real.pi / 4 * M := by positivity
  have hmain := Heta_le_of_sin_bound u hK hu_bound
  have hMsq : M ^ 2 = Gη u * (Real.pi / 2) := Real.sq_sqrt (mul_nonneg hGnn (by positivity))
  have hC : (Real.pi / 4 * M) ^ 2 * (Real.pi / 2)
      ≤ ((Real.pi / 4) ^ 2 * (Real.pi / 2) * (Real.pi / 2)) * Gη u := by
    rw [mul_pow, hMsq]
    nlinarith [hGnn, Real.pi_pos, sq_nonneg (Real.pi / 4)]
  linarith [hmain, hC]

/-! ## The theorem -/

theorem slice_coercive (m : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.Elliptic.SmoothSlice u → u 0 = 0 → u (Real.pi / 2) = 0 →
      (∫ θ in Work.Spaces.Iθ, u θ * Work.Elliptic.sinCos2 θ) = 0 →
      Work.FTS.EllipticEst.PthetaMem α m (fun θ => deriv (fun t => deriv u t) θ) →
      Work.FTS.EllipticEst.PthetaMem α m (Work.FTS.EllipticEst.Lzero1 u) →
      Work.FTS.EllipticEst.Ptheta α m u
        ≤ C * (Work.FTS.EllipticEst.Ptheta α m (fun θ => deriv (fun t => deriv u t) θ)
            + Work.FTS.EllipticEst.Ptheta α m (Work.FTS.EllipticEst.Lzero1 u)) := by
  obtain ⟨C0, hC0pos, hP1⟩ := Hη_le_of_deriv_bound
  obtain ⟨C1, hC1pos, hP2⟩ := first_iter_le_u
  obtain ⟨K, hKpos, hP3⟩ := iter_le_of_lower_u
  -- the extended iteration constant: `Kp 1 = C1` (the first-iterate bound), `Kp i = K i`
  set Kp : ℕ → ℝ := Function.update K 1 C1 with hKpdef
  have hKp1 : Kp 1 = C1 := by
    rw [hKpdef]; exact Function.update_self 1 C1 K
  have hKpne : ∀ i, i ≠ 1 → Kp i = K i := by
    intro i hi; rw [hKpdef]; exact Function.update_of_ne hi C1 K
  have hKppos : ∀ i, 0 < Kp i := by
    intro i
    rcases eq_or_ne i 1 with h | h
    · subst h; rw [hKp1]; exact hC1pos
    · rw [hKpne i h]; exact hKpos i
  refine ⟨C0 + (∏ i ∈ Finset.Icc 1 m, (1 + Kp i) - 1), ?_, ?_⟩
  · have hprod1 : (1 : ℝ) ≤ ∏ i ∈ Finset.Icc 1 m, (1 + Kp i) :=
      one_le_prod_Icc Kp hKppos m
    linarith
  · intro α u hα hα4 hsm h0 h1 _hcon hmem2 hmemA
    -- honesty of the data and of the iterates of `u`
    have hI2 : MeasureTheory.IntegrableOn (fun θ => (D2 u θ) ^ 2 * sEta θ) Work.Spaces.Iθ :=
      hmem2.1
    have hIA : MeasureTheory.IntegrableOn (fun θ => (Lzero1 u θ) ^ 2 * sEta θ)
        Work.Spaces.Iθ := hmemA.1
    have hIk2 : ∀ k ∈ Finset.Icc 1 m, MeasureTheory.IntegrableOn
        (fun θ => (Work.Elliptic.Dth1Iter k (D2 u) θ) ^ 2 * sGam α θ) Work.Spaces.Iθ :=
      hmem2.2
    have hIkU : ∀ k ∈ Finset.Icc 1 m, MeasureTheory.IntegrableOn
        (fun θ => (Work.Elliptic.Dth1Iter k u θ) ^ 2 * sGam α θ) Work.Spaces.Iθ :=
      (PthetaMem_of_smooth α m u hα hα4 hsm h0 h1).2
    -- the two scale quantities: `B = Ptheta` of the data `u''`, `S = B + Fη u`
    set Dsum : ℝ := ∑ k ∈ Finset.Icc 1 m, Gγ α k (D2 u) with hDsum
    set B : ℝ := Gη u + Dsum with hB
    set S : ℝ := B + Fη u with hS
    have hDsum_nn : 0 ≤ Dsum := Finset.sum_nonneg (fun k _ => Gγ_nonneg α k (D2 u))
    have hA_nn : 0 ≤ ∑ k ∈ Finset.Icc 1 m, Gγ α k (Lzero1 u) :=
      Finset.sum_nonneg (fun k _ => Gγ_nonneg α k (Lzero1 u))
    have hBnn : 0 ≤ B := by rw [hB]; linarith [Gη_nonneg u, hDsum_nn]
    have hSnn : 0 ≤ S := by rw [hS]; linarith [hBnn, Fη_nonneg u]
    have hB_le_S : B ≤ S := by rw [hS]; linarith [Fη_nonneg u]
    have hG_le_B : Gη u ≤ B := by rw [hB]; linarith [hDsum_nn]
    -- ### the triangular induction
    have hsum : ∀ N, N ≤ m → (∑ i ∈ Finset.Icc 1 N, Gγ α i u)
        ≤ (∏ i ∈ Finset.Icc 1 N, (1 + Kp i) - 1) * S := by
      intro N
      induction N with
      | zero => intro _; simp
      | succ N ih =>
        intro hNm
        have hNle : N ≤ m := by omega
        have hIH := ih hNle
        have hprodnn : 0 ≤ ∏ i ∈ Finset.Icc 1 N, (1 + Kp i) - 1 := by
          linarith [one_le_prod_Icc Kp hKppos N]
        have hGN : Gγ α (N + 1) u
            ≤ Kp (N + 1) * (∏ i ∈ Finset.Icc 1 N, (1 + Kp i)) * S := by
          rcases Nat.eq_zero_or_pos N with hN0 | hNpos
          · -- `N = 0`: the first iterate
            subst hN0
            have hP2u := hP2 α u hα hα4 hsm h0 h1 hI2 hIA
            have hKp1' : Kp (0 + 1) = C1 := by simpa using hKp1
            have hprod0 : (∏ i ∈ Finset.Icc 1 0, (1 + Kp i)) = 1 := by simp
            rw [hKp1', hprod0, mul_one]
            refine le_trans hP2u (mul_le_mul_of_nonneg_left ?_ (le_of_lt hC1pos))
            rw [hS]; linarith [hBnn]
          · -- `N ≥ 1`: the iteration step at `i = N + 1`
            have h2 : 2 ≤ N + 1 := by omega
            have hIcc1 : Finset.Icc 1 (N + 1) ⊆ Finset.Icc 1 m :=
              Finset.Icc_subset_Icc_right hNm
            have hIk2' : ∀ k ∈ Finset.Icc 1 (N + 1), MeasureTheory.IntegrableOn
                (fun θ => (Work.Elliptic.Dth1Iter k (D2 u) θ) ^ 2 * sGam α θ)
                Work.Spaces.Iθ := fun k hk => hIk2 k (hIcc1 hk)
            have hIkU' : ∀ k ∈ Finset.Icc 1 (N + 1), MeasureTheory.IntegrableOn
                (fun θ => (Work.Elliptic.Dth1Iter k u θ) ^ 2 * sGam α θ)
                Work.Spaces.Iθ := fun k hk => hIkU k (hIcc1 hk)
            have hP3u := hP3 (N + 1) h2 α u hα hα4 hsm hI2 hIk2' hIkU'
            have hKpN1 : Kp (N + 1) = K (N + 1) := hKpne (N + 1) (by omega)
            have hsub2 : Finset.Icc 1 (N + 1 - 2) ⊆ Finset.Icc 1 m :=
              Finset.Icc_subset_Icc_right (by omega)
            have hsumD : (∑ k ∈ Finset.Icc 1 (N + 1 - 2), Gγ α k (D2 u)) ≤ Dsum := by
              rw [hDsum]
              exact Finset.sum_le_sum_of_subset_of_nonneg hsub2
                (fun k _ _ => Gγ_nonneg α k (D2 u))
            have heq3 : Finset.Icc 1 (N + 1 - 1) = Finset.Icc 1 N := by
              have : N + 1 - 1 = N := by omega
              rw [this]
            have hsumU : (∑ k ∈ Finset.Icc 1 (N + 1 - 1), Gγ α k u)
                ≤ (∏ i ∈ Finset.Icc 1 N, (1 + Kp i) - 1) * S := by
              rw [heq3]; exact hIH
            rw [hKpN1]
            refine le_trans hP3u ?_
            have hbr : Gη u + (∑ k ∈ Finset.Icc 1 (N + 1 - 2), Gγ α k (D2 u))
                + (∑ k ∈ Finset.Icc 1 (N + 1 - 1), Gγ α k u)
                ≤ (1 + (∏ i ∈ Finset.Icc 1 N, (1 + Kp i) - 1)) * S := by
              have h1 : Gη u + (∑ k ∈ Finset.Icc 1 (N + 1 - 2), Gγ α k (D2 u)) ≤ B := by
                rw [hB]; linarith [hsumD]
              nlinarith [h1, hsumU, hB_le_S, hSnn, hprodnn]
            have h4 := mul_le_mul_of_nonneg_left hbr (le_of_lt (hKpos (N + 1)))
            refine le_trans h4 (le_of_eq ?_)
            ring
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1),
          Finset.prod_Icc_succ_top (by omega : 1 ≤ N + 1)]
        calc (∑ i ∈ Finset.Icc 1 N, Gγ α i u) + Gγ α (N + 1) u
            ≤ ((∏ i ∈ Finset.Icc 1 N, (1 + Kp i) - 1) * S)
              + Kp (N + 1) * (∏ i ∈ Finset.Icc 1 N, (1 + Kp i)) * S := by
              linarith [hIH, hGN]
          _ = ((∏ i ∈ Finset.Icc 1 N, (1 + Kp i)) * (1 + Kp (N + 1)) - 1) * S := by
              ring
    have htop := hsum m le_rfl
    -- ### the `i = 0` term
    have hH : Hη u ≤ C0 * Gη u := hP1 u hsm h0 h1 hI2
    have hH' : Hη u ≤ C0 * S := by
      refine le_trans hH (mul_le_mul_of_nonneg_left ?_ (le_of_lt hC0pos))
      linarith [hG_le_B, hB_le_S]
    -- ### the total bound in terms of `S`
    have hmain : Ptheta α m u
        ≤ (C0 + (∏ i ∈ Finset.Icc 1 m, (1 + Kp i) - 1)) * S := by
      rw [Ptheta_eq]
      nlinarith [hH', htop, hSnn]
    -- ### `S` is dominated by the two `Ptheta`s of the data
    have hSle : S ≤ Ptheta α m (D2 u) + Ptheta α m (Lzero1 u) := by
      rw [Ptheta_eq, Ptheta_eq]
      have h1 : Hη (D2 u) = Gη u := rfl
      have h2 : (∑ i ∈ Finset.Icc 1 m, Gγ α i (D2 u)) = Dsum := rfl
      have h3 : Hη (Lzero1 u) = Fη u := rfl
      rw [h1, h2, h3, hS, hB]
      linarith [hA_nn, hDsum_nn]
    calc Ptheta α m u
        ≤ (C0 + (∏ i ∈ Finset.Icc 1 m, (1 + Kp i) - 1)) * S := hmain
      _ ≤ (C0 + (∏ i ∈ Finset.Icc 1 m, (1 + Kp i) - 1))
            * (Ptheta α m (D2 u) + Ptheta α m (Lzero1 u)) := by
          refine mul_le_mul_of_nonneg_left hSle ?_
          linarith [one_le_prod_Icc Kp hKppos m]

end Work.FTS.EllipticEst.TT
