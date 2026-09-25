import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.major_arc_bound_pre

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators

/-! ## Numerical core

Given `1 ≤ q ≤ 2^l ≤ N`, `N ≥ 3`, `M ≥ 1` and `|θ| ≤ 1/M`, the error term produced by
`poly_major_arc_approx_coeff`,
`|θ| · q · (N+q)^d / N + q/N`,
is `≤ 2^l · 2^d · (M⁻¹ N^{d-1} + N⁻¹)`, whence multiplying by `C₀(1+‖coeffs‖₁)` gives the
`M`-neighbourhood form of the statement. -/
private lemma major_arc_numeric_bound (d : ℕ) (hd : 1 ≤ d) (C0 A : ℝ) (hC0 : 0 < C0) (hA : 0 ≤ A)
    (N q : ℕ) (M θ : ℝ) (l : ℕ)
    (hN : 3 ≤ N) (hq : 1 ≤ q) (hql : (q:ℝ) ≤ (2:ℝ)^l) (hl : (2:ℝ)^l ≤ (N:ℝ))
    (hM : 1 ≤ M) (hθ : |θ| ≤ 1/M) :
    C0 * (1 + A) * (|θ| * (q:ℝ) * ((N:ℝ) + (q:ℝ))^d / (N:ℝ) + (q:ℝ)/(N:ℝ))
      ≤ (C0 * (1+A) + 1) * (2:ℝ)^d * (2:ℝ)^l * (M⁻¹ * (N:ℝ)^((d:ℝ)-1) + (N:ℝ)⁻¹) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hMpos : (0:ℝ) < M := by linarith
  have hθ' : |θ| ≤ M⁻¹ := by rw [one_div] at hθ; exact hθ
  have hNq : (N:ℝ) + (q:ℝ) ≤ 2 * (N:ℝ) := by
    have : (q:ℝ) ≤ (N:ℝ) := le_trans hql hl
    linarith
  have hpow : ((N:ℝ) + (q:ℝ))^d ≤ (2:ℝ)^d * (N:ℝ)^d := by
    have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (N:ℝ) + (q:ℝ)) hNq d
    rwa [mul_pow] at h
  have hrpow : (N:ℝ)^((d:ℝ)-1) = (N:ℝ)^(d-1) := by
    rw [show (d:ℝ) - 1 = ((d-1:ℕ):ℝ) by
      rw [Nat.cast_sub hd]; push_cast; ring, Real.rpow_natCast]
  have h1 : |θ| * (q:ℝ) * ((N:ℝ) + (q:ℝ))^d / (N:ℝ)
      ≤ M⁻¹ * (2:ℝ)^l * (2:ℝ)^d * (N:ℝ)^(d-1) := by
    have hsimpl : M⁻¹ * (2:ℝ)^l * ((2:ℝ)^d * (N:ℝ)^d) / (N:ℝ)
        = M⁻¹ * (2:ℝ)^l * (2:ℝ)^d * (N:ℝ)^(d-1) := by
      field_simp
      rw [show (N:ℝ)^d = (N:ℝ)^(d-1) * (N:ℝ) by
        rw [mul_comm, ← pow_succ', Nat.sub_add_cancel hd]]
      ring
    calc |θ| * (q:ℝ) * ((N:ℝ) + (q:ℝ))^d / (N:ℝ)
        ≤ M⁻¹ * (2:ℝ)^l * ((2:ℝ)^d * (N:ℝ)^d) / (N:ℝ) := by gcongr
      _ = M⁻¹ * (2:ℝ)^l * (2:ℝ)^d * (N:ℝ)^(d-1) := hsimpl
  have h2 : (q:ℝ)/(N:ℝ) ≤ (2:ℝ)^l * (N:ℝ)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hql (by positivity)
  have hb : |θ| * (q:ℝ) * ((N:ℝ) + (q:ℝ))^d / (N:ℝ) + (q:ℝ)/(N:ℝ)
      ≤ (2:ℝ)^d * (2:ℝ)^l * (M⁻¹ * (N:ℝ)^(d-1) + (N:ℝ)⁻¹) := by
    have hsum := add_le_add h1 h2
    have h2d1 : (1:ℝ) ≤ (2:ℝ)^d := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    have hY0 : 0 ≤ (N:ℝ)⁻¹ := by positivity
    have htl : 0 ≤ (2:ℝ)^l := by positivity
    have hYle : (N:ℝ)⁻¹ ≤ (2:ℝ)^d * (N:ℝ)⁻¹ := by nlinarith
    have h3 : M⁻¹ * (2:ℝ)^l * (2:ℝ)^d * (N:ℝ)^(d-1) + (2:ℝ)^l * ((2:ℝ)^d * (N:ℝ)⁻¹)
        = (2:ℝ)^d * (2:ℝ)^l * (M⁻¹ * (N:ℝ)^(d-1) + (N:ℝ)⁻¹) := by ring
    calc |θ| * (q:ℝ) * ((N:ℝ) + (q:ℝ))^d / (N:ℝ) + (q:ℝ)/(N:ℝ)
        ≤ M⁻¹ * (2:ℝ)^l * (2:ℝ)^d * (N:ℝ)^(d-1) + (2:ℝ)^l * (N:ℝ)⁻¹ := hsum
      _ ≤ M⁻¹ * (2:ℝ)^l * (2:ℝ)^d * (N:ℝ)^(d-1) + (2:ℝ)^l * ((2:ℝ)^d * (N:ℝ)⁻¹) := by
          have := mul_le_mul_of_nonneg_left hYle htl
          linarith
      _ = (2:ℝ)^d * (2:ℝ)^l * (M⁻¹ * (N:ℝ)^(d-1) + (N:ℝ)⁻¹) := h3
  rw [hrpow] at *
  have hK0 : 0 ≤ C0 * (1 + A) := by positivity
  have hC1 : C0 * (1 + A) ≤ C0 * (1 + A) + 1 := by linarith
  have hR0 : 0 ≤ (2:ℝ)^d * (2:ℝ)^l * (M⁻¹ * (N:ℝ)^(d-1) + (N:ℝ)⁻¹) := by positivity
  calc C0 * (1 + A) * (|θ| * (q:ℝ) * ((N:ℝ) + (q:ℝ))^d / (N:ℝ) + (q:ℝ)/(N:ℝ))
      ≤ C0 * (1 + A) * ((2:ℝ)^d * (2:ℝ)^l * (M⁻¹ * (N:ℝ)^(d-1) + (N:ℝ)⁻¹)) := by
        exact mul_le_mul_of_nonneg_left hb hK0
    _ ≤ (C0 * (1+A) + 1) * (2:ℝ)^d * (2:ℝ)^l * (M⁻¹ * (N:ℝ)^(d-1) + (N:ℝ)⁻¹) := by
        nlinarith [hC1, hR0]

/-- **The `M`-neighbourhood form of the major-arc approximation** (Kosz–Mirek–Słomian–Zhang,
arXiv:2606.12663, (6.19); Bourgain (1989), §7, (7.45)–(7.48)): for an integer polynomial `P` of
degree `d ≥ 2`, all `N ≥ 3`, all `1 ≤ q`, all `l : ℕ` with `q ≤ 2 ^ l ≤ N`, all `a : ℤ`, and all
`ξ` within `1/M` of `a/q` (with `1 ≤ M`), the Weyl kernel `N⁻¹ ∑_{n<N} e(ξ P(n))` differs from the
complete sum `W_q(a) = q⁻¹ ∑_{r<q} e(a P(r)/q)` times the profile
`Φ_N(ξ − a/q) = ∫_0^1 e((ξ − a/q) P(N s)) ds` by at most `C · 2^l · (M⁻¹ N^{d−1} + N⁻¹)`, with `C`
depending only on `P`.

This is the form of the major-arc approximation consumed by the circle-method assembly of the
maximal inequality for the density averages (`discAvg`, `polyKernel`); it is a direct consequence
of `Work.Analysis.ExponentialSums.poly_major_arc_approx_coeff`, which supplies the identical
estimate with the error `C (1 + ∑_i |coeff_i|) (|β| · q · (N+q)^d / N + q / N)`, by substituting
`β := ξ − a/q`, `|β| ≤ 1/M`, `q ≤ 2^l ≤ N` and `(N+q)^d ≤ (2N)^d`.  (Note this is the modulus-`q`,
offset-`ξ − a/q` form; the leading-coefficient-rescaled variant is `polyModelTermPre`.) -/
theorem major_arc_nbd_bound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N q : ℕ) (a : ℤ) (l : ℕ) (ξ M : ℝ),
      3 ≤ N → 1 ≤ q → (q : ℝ) ≤ (2 : ℝ) ^ l → (2 : ℝ) ^ l ≤ (N : ℝ) → 1 ≤ M →
      |ξ - (a : ℝ) / (q : ℝ)| ≤ 1 / M →
      ‖Work.BourgainPlan.Maximal.polyWeylKernel P N ξ
        - Work.BourgainPlan.Maximal.polyWeight P q a
          * Work.BourgainPlan.Maximal.polyProfile P N (ξ - (a : ℝ) / (q : ℝ))‖
        ≤ C * (2 : ℝ) ^ l * (M⁻¹ * (N : ℝ) ^ ((P.natDegree : ℝ) - 1) + (N : ℝ)⁻¹) := by
  obtain ⟨C0, hC0, hmain⟩ :=
    Work.Analysis.ExponentialSums.poly_major_arc_approx_coeff P.natDegree hd
  let A : ℝ := ∑ i ∈ Finset.range (P.natDegree + 1), |((P.coeff i : ℤ) : ℝ)|
  have hA0 : 0 ≤ A := by positivity
  refine ⟨(C0 * (1 + A) + 1) * (2:ℝ)^P.natDegree, by positivity, ?_⟩
  intro N q a l ξ M hN hq hq2 hlN hM hξ
  have hN1 : 1 ≤ N := by omega
  have hd1 : 1 ≤ P.natDegree := by omega
  have hW : polyWeylKernel P N ξ
      = (N:ℂ)⁻¹ * ∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I *
          ((((a:ℝ)/(q:ℝ) + (ξ - (a:ℝ)/(q:ℝ))) * ((P.eval (n:ℤ) : ℤ) : ℝ) : ℝ) : ℂ)) := by
    unfold polyWeylKernel
    rw [show ((↑↑N : ℂ))⁻¹ = ((↑N : ℂ))⁻¹ by norm_num]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    push_cast
    ring
  have hV : polyWeight P q a
      = (q:ℂ)⁻¹ * ∑ r ∈ Finset.range q, Complex.exp (2 * Real.pi * Complex.I *
          ((((a:ℝ)/(q:ℝ)) * ((P.eval (r:ℤ) : ℤ) : ℝ) : ℝ) : ℂ)) := by
    unfold polyWeight
    rfl
  have hU : polyProfile P N (ξ - (a:ℝ)/(q:ℝ))
      = ∫ s in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I *
          (((ξ - (a:ℝ)/(q:ℝ) : ℝ) : ℂ) *
            ((Polynomial.eval (((N:ℝ)*s) : ℝ) (P.map (Int.castRingHom ℝ)) : ℝ) : ℂ))) := by
    unfold polyProfile toRealPoly
    push_cast
    rfl
  have h := hmain N q a (ξ - (a:ℝ)/(q:ℝ)) P rfl hq hN1
  rw [hW, hV, hU]
  exact le_trans h (major_arc_numeric_bound P.natDegree hd1 C0 A hC0 hA0 N q M
    (ξ - (a:ℝ)/(q:ℝ)) l hN hq hq2 hlN hM hξ)

end Work.BourgainPlan.Maximal
