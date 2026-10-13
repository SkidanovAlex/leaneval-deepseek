import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.Baux

theorem PthSlotPointwise (γ : ℝ) (m : ℕ) (hm : 2 ≤ m) (K : ℝ) (hK : 0 < K)
    (f : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hrev : (Real.sin (2 * θ)) ^ (m - 2) * |Work.Spaces.pthIter m f z θ|
      ≤ K * (|Work.Spaces.DthIter (m - 2) (Work.Spaces.pthIter 2 f) z θ|
        + ∑ r ∈ Finset.range (m - 2),
            (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter (r + 2) f z θ|)) :
    (Work.Spaces.pthIter m f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - 4 - γ)
      ≤ 2 * K ^ 2 * ((m : ℝ) - 1)
        * ((Work.Spaces.DthIter (m - 2) (Work.Spaces.pthIter 2 f) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-γ)
          + ∑ r ∈ Finset.range (m - 2),
              (Work.Spaces.pthIter (r + 2) f z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * ((r + 2 : ℕ) : ℝ) - 4 - γ)) := by
  -- Write `s := sin 2θ > 0` and abbreviate the three groups appearing in `hrev`.
  set s : ℝ := Real.sin (2 * θ) with hsdef
  have hs : 0 < s := by
    rw [hsdef]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  set u : ℝ := Work.Spaces.pthIter m f z θ with hudef
  set w0 : ℝ := Work.Spaces.DthIter (m - 2) (Work.Spaces.pthIter 2 f) z θ with hwdef
  set v : ℕ → ℝ := fun r => Work.Spaces.pthIter (r + 2) f z θ with hvdef
  set S : ℝ := ∑ r ∈ Finset.range (m - 2), s ^ r * |v r| with hSdef
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  -- Square `hrev`; both sides are nonnegative.
  have hstep1 : (s ^ (m - 2)) ^ 2 * u ^ 2 ≤ K ^ 2 * (|w0| + S) ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ s ^ (m - 2) * |u|) hrev 2
    simp only [mul_pow, sq_abs] at h
    exact h
  -- `(a + b)^2 ≤ 2 (a^2 + b^2)`.
  have hBS : (|w0| + S) ^ 2 ≤ 2 * (w0 ^ 2 + S ^ 2) := by
    nlinarith [sq_nonneg (|w0| - S), sq_abs w0, abs_nonneg w0]
  -- The sum `Sig` of the `(r+2)`-slots, in the order used by the goal.
  set Sig : ℝ := ∑ r ∈ Finset.range (m - 2), (v r) ^ 2 * (s ^ r) ^ 2 with hSigdef
  have hSig_nn : 0 ≤ Sig := by
    rw [hSigdef]; apply Finset.sum_nonneg; intro r hr; positivity
  -- Cauchy–Schwarz for the `(m-2)`-term sum.
  have hCS' : (∑ r ∈ Finset.range (m - 2), s ^ r * |v r|) ^ 2
      ≤ ((m - 2 : ℕ) : ℝ) * ∑ r ∈ Finset.range (m - 2), (s ^ r) ^ 2 * (v r) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (m - 2))
      (f := fun r => s ^ r * |v r|)
    simpa only [Finset.card_range, mul_pow, sq_abs] using h
  have hsum_eq : (∑ r ∈ Finset.range (m - 2), (s ^ r) ^ 2 * (v r) ^ 2) = Sig := by
    rw [hSigdef]; exact Finset.sum_congr rfl (fun r hr => by ring)
  have hCS : S ^ 2 ≤ ((m - 2 : ℕ) : ℝ) * Sig := by
    rw [hSdef, ← hsum_eq]; exact hCS'
  have hcc : ((m - 2 : ℕ) : ℝ) ≤ (m : ℝ) - 1 := by
    rw [Nat.cast_sub hm]; norm_num; linarith
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  -- The `s^{-γ}`-free core inequality.
  have hcore : (s ^ (m - 2)) ^ 2 * u ^ 2
      ≤ 2 * K ^ 2 * ((m : ℝ) - 1) * (w0 ^ 2 + Sig) := by
    have h1 : K ^ 2 * (|w0| + S) ^ 2 ≤ K ^ 2 * (2 * (w0 ^ 2 + S ^ 2)) :=
      mul_le_mul_of_nonneg_left hBS hK2
    have h2b : w0 ^ 2 + S ^ 2 ≤ w0 ^ 2 + ((m - 2 : ℕ) : ℝ) * Sig := by linarith [hCS]
    have h2 : K ^ 2 * (2 * (w0 ^ 2 + S ^ 2))
        ≤ 2 * K ^ 2 * (w0 ^ 2 + ((m - 2 : ℕ) : ℝ) * Sig) := by
      nlinarith [h2b, hK2]
    have h3b : w0 ^ 2 + ((m - 2 : ℕ) : ℝ) * Sig ≤ ((m : ℝ) - 1) * (w0 ^ 2 + Sig) := by
      nlinarith [hcc, hSig_nn, sq_nonneg w0, hm2]
    have h3 : 2 * K ^ 2 * (w0 ^ 2 + ((m - 2 : ℕ) : ℝ) * Sig)
        ≤ 2 * K ^ 2 * (((m : ℝ) - 1) * (w0 ^ 2 + Sig)) :=
      mul_le_mul_of_nonneg_left h3b (by positivity)
    calc (s ^ (m - 2)) ^ 2 * u ^ 2 ≤ K ^ 2 * (|w0| + S) ^ 2 := hstep1
      _ ≤ K ^ 2 * (2 * (w0 ^ 2 + S ^ 2)) := h1
      _ ≤ 2 * K ^ 2 * (w0 ^ 2 + ((m - 2 : ℕ) : ℝ) * Sig) := h2
      _ ≤ 2 * K ^ 2 * (((m : ℝ) - 1) * (w0 ^ 2 + Sig)) := h3
      _ = 2 * K ^ 2 * ((m : ℝ) - 1) * (w0 ^ 2 + Sig) := by ring
  -- Exponent bookkeeping: turn the natural powers `s ^ (m-2)`, `s ^ r` into the rpow
  -- exponents of the statement, and separate the common factor `s ^ (-γ)`.
  have hpowL : s ^ (2 * (m : ℝ) - 4 - γ) = (s ^ (m - 2)) ^ 2 * s ^ (-γ) := by
    have hcast : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := Nat.cast_sub hm
    have e1 : s ^ (2 * ((m - 2 : ℕ) : ℝ)) = (s ^ (m - 2)) ^ 2 := by
      rw [show 2 * ((m - 2 : ℕ) : ℝ) = ((m - 2 : ℕ) : ℝ) * 2 by ring,
          Real.rpow_natCast_mul (le_of_lt hs)]
      exact Real.rpow_natCast _ 2
    rw [show 2 * (m : ℝ) - 4 - γ = 2 * ((m - 2 : ℕ) : ℝ) + (-γ) by
          push_cast [hcast]; ring,
        Real.rpow_add hs, e1]
  have hpowR : ∀ r : ℕ, s ^ (2 * ((r + 2 : ℕ) : ℝ) - 4 - γ) = (s ^ r) ^ 2 * s ^ (-γ) := by
    intro r
    have hcast : ((r + 2 : ℕ) : ℝ) = (r : ℝ) + 2 := by push_cast; ring
    have e1 : s ^ (2 * (r : ℝ)) = (s ^ r) ^ 2 := by
      rw [show 2 * (r : ℝ) = (r : ℝ) * 2 by ring,
          Real.rpow_natCast_mul (le_of_lt hs)]
      exact Real.rpow_natCast _ 2
    rw [show 2 * ((r + 2 : ℕ) : ℝ) - 4 - γ = 2 * (r : ℝ) + (-γ) by
          push_cast [hcast]; ring,
        Real.rpow_add hs, e1]
  have key := mul_le_mul_of_nonneg_right hcore (le_of_lt (Real.rpow_pos_of_pos hs (-γ)))
  calc u ^ 2 * s ^ (2 * (m : ℝ) - 4 - γ)
      = (s ^ (m - 2)) ^ 2 * u ^ 2 * s ^ (-γ) := by rw [hpowL]; ring
    _ ≤ (2 * K ^ 2 * ((m : ℝ) - 1) * (w0 ^ 2 + Sig)) * s ^ (-γ) := key
    _ = 2 * K ^ 2 * ((m : ℝ) - 1)
          * (w0 ^ 2 * s ^ (-γ)
              + ∑ r ∈ Finset.range (m - 2), (v r) ^ 2 * s ^ (2 * ((r + 2 : ℕ) : ℝ) - 4 - γ)) := by
        rw [hSigdef]
        simp only [hpowR]
        rw [show (∑ r ∈ Finset.range (m - 2), (v r) ^ 2 * ((s ^ r) ^ 2 * s ^ (-γ)))
              = (∑ r ∈ Finset.range (m - 2), (v r) ^ 2 * (s ^ r) ^ 2) * s ^ (-γ) from by
              rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun r hr => by ring)]
        ring

end Work.FTS.EllipticEst.remov.Baux
