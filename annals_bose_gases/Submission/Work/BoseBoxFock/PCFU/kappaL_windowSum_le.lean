import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBoxFock.L1Tails.Defs
import Submission.Work.BoseBoxFock.PCFU.latTailAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.kappaL_windowSum_le` — the lattice window sum over the box momenta

The box momenta are `kappaL ℓ n = kmomInt ℓ n = ℓ⁻¹ • (2π • latVec n) = (2π/ℓ) • latVec n`, whose
squared norm is `(2π/ℓ)² · nSq n` (`nSq n = Σᵢ (nᵢ)²` the squared lattice norm,
`Work.BoseBoxFock.latVec_norm_sq`).  The target is the elementary but sharp **three-dimensional
lattice tail bound**

    ∑_{n ∈ S, ‖κ_n‖ ≥ Λ} 1 / ((1 + ‖κ_n‖)² ‖κ_n‖²)  ≤  C · ℓ³ / Λ .

The summand is `≍ ‖κ_n‖⁻⁴`, and the number of lattice momenta of size `≍ ρ` is `≍ ρ²`, so the sum
scales like `∑_{ρ > Λ} ρ² · ((ℓ/2π)ρ)⁻⁴ ≍ ℓ⁴ Λ⁻¹` — the factor `ℓ³/Λ` of the statement.  The
window `‖κ_n‖ ≥ Λ` is what makes it finite (the window-free sum still converges) and the loss is
exactly the one-dimensional tail, consistent with the standard sharp lattice estimate.

The proof has three layers:

* `kappaLWin_norm_sq` — the momentum identity `‖kappaL ℓ n‖² = (2π/ℓ)² nSq n`;
* `latTail_inv_sq_le` — the **sharp lattice tail bound** `∑_{nSq d > ρ²} (nSq d)⁻² ≤ 156/ρ` for
  *every* `ρ > 0` (the sibling `Work.BoseBoxFock.PCFU.latTailNSqBound` covers `ρ ≥ 1`; here the
  shell decomposition is reused with the *unrestricted* threshold comparison
  `max 1 ⌈ρ/3⌉₊ ≤ K d`, which only needs `ρ > 0`);
* `windowTerm_le` — the pointwise comparison `1/((1+‖κ‖)²‖κ‖²) ≤ (ℓ/2π)⁴ (nSq n)⁻²`, since
  `(1+‖κ‖)² ≥ ‖κ‖²`.

Assembling these with `ρ = Λℓ/(4π)` (so that `‖κ_n‖ ≥ Λ` gives `nSq n ≥ 4ρ² > ρ²`) yields the
statement with the explicit constant `C = 39` (in fact `39/π³ ≤ 39`).
-/

namespace Work.BoseBoxFock.PCFU

noncomputable section

open Finset

/-! ## 1. The lattice tail bound at an arbitrary positive threshold -/

/-- A lattice vector with `ρ ^ 2 < nSq d` is nonzero, so `1 ≤ K d` (valid for every `ρ > 0`;
`Work.BoseBoxFock.PCFU.latTailNSqAux_one_le_K` states the case `1 ≤ ρ`). -/
lemma kappaLWin_one_le_K (ρ : ℝ) (_hρ : 0 < ρ) (d : Fin 3 → ℤ)
    (hd : ρ ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)) : 1 ≤ Work.BoseBoxFock.K d := by
  rcases Nat.eq_zero_or_pos (Work.BoseBoxFock.K d) with h | h
  · exfalso
    have hd0 : d = 0 := Work.BoseBoxFock.eq_zero_of_K_eq_zero h
    rw [hd0] at hd
    simp only [Work.BoseBoxFock.nSq_zero, Nat.cast_zero] at hd
    nlinarith
  · exact h

/-- The threshold comparison `⌈ρ / 3⌉₊ ≤ K d` whenever `ρ ^ 2 < nSq d`, valid for every real `ρ`
(the analogue `Work.BoseBoxFock.PCFU.latTailNSqAux_ceil_third_le_K` assumes `1 ≤ ρ`, which its
proof does not use). -/
lemma kappaLWin_ceil_third_le_K (ρ : ℝ) (d : Fin 3 → ℤ)
    (hd : ρ ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)) : ⌈ρ / 3⌉₊ ≤ Work.BoseBoxFock.K d := by
  refine Nat.ceil_le.mpr ?_
  have hle := latTailNSqAux_nSq_le_three_mul_K_sq d
  have h1 : ρ ^ 2 < 3 * ((Work.BoseBoxFock.K d : ℕ) : ℝ) ^ 2 := lt_of_lt_of_le hd hle
  have hKnn : (0 : ℝ) ≤ (Work.BoseBoxFock.K d : ℕ) := Nat.cast_nonneg _
  have h3 : ρ < 3 * (Work.BoseBoxFock.K d : ℝ) := by
    by_contra hcon
    push Not at hcon
    nlinarith [hcon, hKnn, h1]
  linarith

/-- **The sharp lattice tail bound, at an arbitrary positive threshold.**  For every `ρ > 0` and
every finite set `u` of lattice vectors,

`∑_{d ∈ u, ρ ^ 2 < nSq d} (nSq d)⁻² ≤ 156 / ρ`,

the three-dimensional lattice tail `∑_{‖d‖ > ρ} ‖d‖⁻⁴ ≲ ρ⁻¹`.  The proof reuses the shell
decomposition `latTailNSqAux_shellSum` with `N = 2` and the `p`-series tail
`latTailNSqAux_powTail`, together with the unrestricted threshold comparisons above. -/
lemma latTail_inv_sq_le (ρ : ℝ) (hρ : 0 < ρ) (u : Finset (Fin 3 → ℤ)) :
    ∑ d ∈ u.filter (fun d => ρ ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)),
        ((Work.BoseBoxFock.nSq d : ℝ) ^ 2)⁻¹ ≤ 156 * ρ⁻¹ := by
  set K₀ : ℕ := max 1 ⌈ρ / 3⌉₊ with hK₀def
  have hK₀1 : 1 ≤ K₀ := by rw [hK₀def]; exact le_max_left _ _
  have hρK : ρ ≤ 3 * (K₀ : ℝ) := by rw [hK₀def]; exact latTailNSqAux_rho_le_three_mul ρ
  have hKd : ∀ d : Fin 3 → ℤ, ρ ^ 2 < (Work.BoseBoxFock.nSq d : ℝ) →
      K₀ ≤ Work.BoseBoxFock.K d := by
    intro d hd
    rw [hK₀def]
    exact max_le (kappaLWin_one_le_K ρ hρ d hd) (kappaLWin_ceil_third_le_K ρ d hd)
  have hMu : ∀ d ∈ u, Work.BoseBoxFock.K d ≤ u.sup Work.BoseBoxFock.K :=
    fun d hd => Finset.le_sup (f := Work.BoseBoxFock.K) hd
  have hA := latTailNSqAux_shellSum 2 ρ K₀ (u.sup Work.BoseBoxFock.K) hK₀1 hKd u hMu
  have hB := latTailNSqAux_powTail 2 (by norm_num) K₀ (u.sup Work.BoseBoxFock.K + 1) hK₀1
  have hpt : ∀ k ∈ Finset.Ico K₀ (u.sup Work.BoseBoxFock.K + 1),
      (24 * (k : ℝ) ^ 2 + 2) * (((k : ℝ) ^ 2) ^ 2)⁻¹ ≤ 26 * ((k : ℝ) ^ 2)⁻¹ := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk1 : 1 ≤ k := le_trans hK₀1 hk.1
    have h := latTailNSqAux_shellWeight_le 2 k (by norm_num) hk1
    have he : (2 : ℕ) * 2 - 2 = 2 := rfl
    rw [he] at h
    exact h
  have h3 : (K₀ : ℝ)⁻¹ ≤ 3 * ρ⁻¹ := by
    have h1 : (3 * (K₀ : ℝ))⁻¹ ≤ ρ⁻¹ := inv_anti₀ hρ hρK
    rw [mul_inv] at h1
    have h2 : ((3 : ℝ))⁻¹ = 1 / 3 := by norm_num
    rw [h2] at h1
    linarith
  calc ∑ d ∈ u.filter (fun d => ρ ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)),
        ((Work.BoseBoxFock.nSq d : ℝ) ^ 2)⁻¹
      ≤ ∑ k ∈ Finset.Ico K₀ (u.sup Work.BoseBoxFock.K + 1),
          (24 * (k : ℝ) ^ 2 + 2) * ((k : ℝ) ^ (2 * 2))⁻¹ := hA
    _ = ∑ k ∈ Finset.Ico K₀ (u.sup Work.BoseBoxFock.K + 1),
          (24 * (k : ℝ) ^ 2 + 2) * (((k : ℝ) ^ 2) ^ 2)⁻¹ := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [pow_mul]
    _ ≤ ∑ k ∈ Finset.Ico K₀ (u.sup Work.BoseBoxFock.K + 1), 26 * ((k : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum hpt
    _ = 26 * ∑ k ∈ Finset.Ico K₀ (u.sup Work.BoseBoxFock.K + 1), ((k : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ 26 * (2 * ((K₀ : ℝ) ^ (2 - 1))⁻¹) := mul_le_mul_of_nonneg_left hB (by norm_num)
    _ = 52 * ((K₀ : ℝ))⁻¹ := by
        rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]; ring
    _ ≤ 52 * (3 * ρ⁻¹) := mul_le_mul_of_nonneg_left h3 (by norm_num)
    _ = 156 * ρ⁻¹ := by ring

/-! ## 2. The momentum identity and the pointwise window comparison -/

/-- `Work.BoseB4.vec n = 2π • latVec n`, so the box momentum is `(2π/ℓ) • latVec n`. -/
lemma kappaLWin_vec_eq (n : Fin 3 → ℤ) :
    Work.BoseB4.vec n = (2 * Real.pi) • Work.BoseBoxFock.latVec n := by
  ext i; simp [Work.BoseB4.vec, Work.BoseBoxFock.latVec]

/-- **The square of the box momentum is `(2π/ℓ)²` times the squared lattice norm.** -/
lemma kappaLWin_norm_sq (ℓ : ℝ) (hℓ : 0 < ℓ) (n : Fin 3 → ℤ) :
    ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2
      = (2 * Real.pi / ℓ) ^ 2 * (Work.BoseBoxFock.nSq n : ℝ) := by
  have hvec : Work.BoseB4.vec n = (2 * Real.pi) • Work.BoseBoxFock.latVec n :=
    kappaLWin_vec_eq n
  have hk : Work.BoseBoxFock.kappaL ℓ n
      = (ℓ⁻¹ * (2 * Real.pi)) • Work.BoseBoxFock.latVec n := by
    rw [Work.BoseBoxFock.kappaL, Work.BoseBoxFock.kmomInt, hvec, smul_smul]
  have hpos : (0 : ℝ) < ℓ⁻¹ * (2 * Real.pi) := by positivity
  rw [hk, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos), mul_pow,
    Work.BoseBoxFock.latVec_norm_sq]
  field_simp

/-- **The pointwise comparison.**  Since `(1 + ‖κ‖)² ≥ ‖κ‖²`, the window summand is dominated by
`‖κ‖⁻⁴ = (ℓ/2π)⁴ (nSq n)⁻²`. -/
lemma windowTerm_le (ℓ : ℝ) (hℓ : 0 < ℓ) (n : Fin 3 → ℤ)
    (hκ : 0 < ‖Work.BoseBoxFock.kappaL ℓ n‖) :
    1 / ((1 + ‖Work.BoseBoxFock.kappaL ℓ n‖) ^ 2 * ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2)
      ≤ (ℓ / (2 * Real.pi)) ^ 4 * (((Work.BoseBoxFock.nSq n : ℝ) ^ 2)⁻¹) := by
  set K : ℝ := ‖Work.BoseBoxFock.kappaL ℓ n‖ with hKdef
  have hKpos : 0 < K := hκ
  have hq : K ^ 2 = (2 * Real.pi / ℓ) ^ 2 * (Work.BoseBoxFock.nSq n : ℝ) := by
    rw [hKdef]
    exact kappaLWin_norm_sq ℓ hℓ n
  have hstep : 1 / ((1 + K) ^ 2 * K ^ 2) ≤ 1 / (K ^ 2 * K ^ 2) := by
    apply one_div_le_one_div_of_le
    · positivity
    · have : K ^ 2 ≤ (1 + K) ^ 2 := by nlinarith [hKpos.le]
      nlinarith
  refine le_trans hstep ?_
  have hK2 : K ^ 2 * K ^ 2 = (((2 * Real.pi / ℓ) ^ 2) * (Work.BoseBoxFock.nSq n : ℝ)) ^ 2 := by
    rw [hq]; ring
  rw [hK2]
  have hA : (((2 * Real.pi / ℓ) ^ 2))⁻¹ = (ℓ / (2 * Real.pi)) ^ 2 := by
    rw [← inv_pow, inv_div]
  rw [one_div, ← inv_pow, mul_inv, mul_pow, hA, ← inv_pow]
  exact le_of_eq (by ring_nf)

/-! ## 3. The window sum -/

/-- **The lattice window sum.**  With `C = 39`,

`∑_{n ∈ S, Λ ≤ ‖kappaL ℓ n‖} 1 / ((1 + ‖kappaL ℓ n‖)² ‖kappaL ℓ n‖²) ≤ 39 ℓ³/Λ`.

The threshold is moved to the lattice: for `ρ = Λℓ/(4π)` the hypothesis `‖κ_n‖ ≥ Λ` gives
`(nSq n) ≥ 4ρ² > ρ²`, and the sum is dominated by `(ℓ/2π)⁴ ∑_{nSq n > ρ²} (nSq n)⁻² ≤
(ℓ/2π)⁴ · 156/ρ = 39 ℓ³/(π³Λ) ≤ 39 ℓ³/Λ`. -/
theorem kappaL_windowSum_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {ℓ Λ : ℝ}, 0 < ℓ → 0 < Λ → ∀ S : Finset (Fin 3 → ℤ),
      (∀ n ∈ S, Λ ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖) →
      ∑ n ∈ S, 1 / ((1 + ‖Work.BoseBoxFock.kappaL ℓ n‖) ^ 2
          * ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2) ≤ C * ℓ ^ 3 / Λ := by
  -- the reduction to the lattice tail bound
  refine ⟨39, by norm_num, ?_⟩
  intro ℓ Λ hℓ hΛ S hS
  set ρ : ℝ := Λ * ℓ / (4 * Real.pi) with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; positivity
  -- the lattice threshold: `‖κ_n‖ ≥ Λ` forces `nSq n ≥ 4 ρ²`
  have hge : ∀ n ∈ S, 4 * ρ ^ 2 ≤ (Work.BoseBoxFock.nSq n : ℝ) := by
    intro n hn
    have h1 : Λ ^ 2 ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2 := by
      have := hS n hn
      nlinarith [hΛ]
    rw [kappaLWin_norm_sq ℓ hℓ n] at h1
    have hfac : (0 : ℝ) < ((2 * Real.pi / ℓ) ^ 2)⁻¹ := by positivity
    calc 4 * ρ ^ 2 = ((2 * Real.pi / ℓ) ^ 2)⁻¹ * Λ ^ 2 := by
          rw [hρdef]; field_simp; ring
      _ ≤ ((2 * Real.pi / ℓ) ^ 2)⁻¹ *
            ((2 * Real.pi / ℓ) ^ 2 * (Work.BoseBoxFock.nSq n : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt hfac)
      _ = (Work.BoseBoxFock.nSq n : ℝ) := by
          rw [← mul_assoc,
            inv_mul_cancel₀ (ne_of_gt (by positivity : (0 : ℝ) < (2 * Real.pi / ℓ) ^ 2)),
            one_mul]
  have hlt : ∀ n ∈ S, ρ ^ 2 < (Work.BoseBoxFock.nSq n : ℝ) := by
    intro n hn
    have := hge n hn
    nlinarith [hρpos]
  have hsubset : S ⊆ S.filter (fun d => ρ ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)) := by
    intro n hn
    exact Finset.mem_filter.mpr ⟨hn, hlt n hn⟩
  calc ∑ n ∈ S, 1 / ((1 + ‖Work.BoseBoxFock.kappaL ℓ n‖) ^ 2 *
          ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2)
      ≤ ∑ n ∈ S, (ℓ / (2 * Real.pi)) ^ 4 * (((Work.BoseBoxFock.nSq n : ℝ) ^ 2)⁻¹) :=
        Finset.sum_le_sum (fun n hn => windowTerm_le ℓ hℓ n (lt_of_lt_of_le hΛ (hS n hn)))
    _ ≤ ∑ n ∈ S.filter (fun d => ρ ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)),
          (ℓ / (2 * Real.pi)) ^ 4 * (((Work.BoseBoxFock.nSq n : ℝ) ^ 2)⁻¹) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun n _ _ => by positivity)
    _ = (ℓ / (2 * Real.pi)) ^ 4 *
          ∑ n ∈ S.filter (fun d => ρ ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)),
            (((Work.BoseBoxFock.nSq n : ℝ) ^ 2)⁻¹) := by
        rw [Finset.mul_sum]
    _ ≤ (ℓ / (2 * Real.pi)) ^ 4 * (156 * ρ⁻¹) :=
        mul_le_mul_of_nonneg_left (latTail_inv_sq_le ρ hρpos S) (by positivity)
    _ = (39 / Real.pi ^ 3) * (ℓ ^ 3 / Λ) := by
        rw [hρdef]; field_simp; ring
    _ ≤ 39 * (ℓ ^ 3 / Λ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.pi ^ 3)]
        have hπ1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
        have hπ3 : (1 : ℝ) ≤ Real.pi ^ 3 := one_le_pow₀ hπ1
        nlinarith
    _ = 39 * ℓ ^ 3 / Λ := by rw [mul_div_assoc]

end

end Work.BoseBoxFock.PCFU
