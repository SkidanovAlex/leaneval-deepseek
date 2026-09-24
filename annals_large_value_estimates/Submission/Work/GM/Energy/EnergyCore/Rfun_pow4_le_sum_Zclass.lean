import Mathlib
import Submission.Work.GM.Energy.EnergyCore.FourthMomentDefs

/-!
# GM (11.4): splitting `|R|⁴` over the dyadic classes

GM Lemma 11.6 starts from the identity
`Σ_{t₁,t₂,t₃,t₄ ∈ W} |x|^{i(t₁-t₂+t₃-t₄)} = |R(x)|⁴`, groups the two "difference" pairs
`(t₁,t₂)` and `(t₃,t₄)` by the key `⌊t₁-t₂⌋`, `⌊t₃-t₄⌋`, and then applies Cauchy–Schwarz to
the dyadic classes `U_B` (`clsSet W j`) of those keys.

The elementary input of that argument is the present lemma: with

* `R(x) = Σ_{t∈W} |x|^{it}` (`Submission.GM.Rfun`), and
* `Z_B(x) = Σ_{u∈U_B} Σ_{(t₁,t₂) ∈ W², ⌊t₁-t₂⌋=u} x^{i(t₁-t₂)}` (`Zclass W U_B x`),

the classes partition the pairs `W²`, so `Σ_B Z_B(x) = |R(x)|²` (as a *complex* number, namely
the nonnegative real `‖R(x)‖²`), and Cauchy–Schwarz gives

  `‖R(x)‖⁴ = ‖Σ_B Z_B(x)‖² ≤ (clsNum W) · Σ_B ‖Z_B(x)‖²`.

Everything here is elementary algebra with `Complex.cpow`; the only analytic input is `x > 0`,
which makes `x^{iτ}` have modulus `1` and conjugate `x^{-iτ}`.
-/

namespace Work.GM.Energy.EnergyCore

open Complex Finset
open scoped BigOperators
set_option autoImplicit false

/-- `conj (x^{iτ}) = x^{-iτ}` for `x > 0` real. -/
private lemma conj_cpow_ofReal_I_aux {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    (starRingEnd ℂ) ((x : ℂ) ^ (Complex.I * (τ : ℂ)))
      = (x : ℂ) ^ (Complex.I * ((-τ : ℝ) : ℂ)) := by
  have harg : ((x : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj ((x : ℂ)) (Complex.I * (τ : ℂ)) harg
  rw [Complex.conj_ofReal] at h
  rw [← h]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- Cauchy–Schwarz for the norm of a finite sum: `‖Σ z‖² ≤ #s · Σ ‖z‖²`. -/
private lemma norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖z i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, z i‖ ≤ ∑ i ∈ s, ‖z i‖ := norm_sum_le s z
  have h2 : (∑ i ∈ s, ‖z i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖z i‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => ‖z i‖)
  have h3 : ‖∑ i ∈ s, z i‖ ^ 2 ≤ (∑ i ∈ s, ‖z i‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  linarith

/-- **The classes reconstruct `‖R‖²`.**  For `x > 0`,
`Σ_{j < clsNum W} Zclass W (clsSet W j) x = ‖Rfun W x‖²` (the right-hand side viewed in `ℂ`). -/
private lemma sum_Zclass_eq_normSq_Rfun (W : Finset ℝ) {x : ℝ} (hx : 0 < x) :
    (∑ j ∈ Finset.range (clsNum W), Zclass W (clsSet W j) x)
      = ((‖Submission.GM.Rfun W x‖ ^ 2 : ℝ) : ℂ) := by
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  -- `Rfun W x = Σ_{t∈W} x^{it}` because `|x| = x`.
  have hR : Submission.GM.Rfun W x = ∑ t ∈ W, (x : ℂ) ^ (Complex.I * (t : ℂ)) := by
    unfold Submission.GM.Rfun
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [abs_of_pos hx]
  -- A single `cpow` of a difference splits as a product with a conjugate.
  have hterm : ∀ t1 t2 : ℝ, (x : ℂ) ^ (Complex.I * (((t1 - t2 : ℝ)) : ℂ))
      = (x : ℂ) ^ (Complex.I * (t1 : ℂ))
        * (starRingEnd ℂ) ((x : ℂ) ^ (Complex.I * (t2 : ℂ))) := by
    intro t1 t2
    rw [conj_cpow_ofReal_I_aux hx t2, ← Complex.cpow_add _ _ hxne]
    congr 1
    push_cast
    ring
  -- The sum over all pairs is `R · conj R = ‖R‖²`.
  have hpair : (∑ p ∈ pairSet W, (x : ℂ) ^ (Complex.I * (((p.1 - p.2 : ℝ)) : ℂ)))
      = ((‖Submission.GM.Rfun W x‖ ^ 2 : ℝ) : ℂ) := by
    rw [pairSet, Finset.sum_product]
    rw [show (∑ t1 ∈ W, ∑ t2 ∈ W, (x : ℂ) ^ (Complex.I * (((t1 - t2 : ℝ)) : ℂ)))
        = ∑ t1 ∈ W, ∑ t2 ∈ W,
            (x : ℂ) ^ (Complex.I * (t1 : ℂ))
              * (starRingEnd ℂ) ((x : ℂ) ^ (Complex.I * (t2 : ℂ)))
        from Finset.sum_congr rfl fun t1 _ => Finset.sum_congr rfl fun t2 _ => hterm t1 t2]
    rw [← Finset.sum_mul_sum, ← map_sum, hR, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  -- Regroup the pairs: keys, then dyadic classes of keys.
  have e1 : (∑ j ∈ Finset.range (clsNum W), Zclass W (clsSet W j) x)
      = ∑ j ∈ Finset.range (clsNum W), ∑ u ∈ clsSet W j, ∑ p ∈ repPairs W u,
          (x : ℂ) ^ (Complex.I * (((p.1 - p.2 : ℝ)) : ℂ)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Zclass]
  have e2 : (∑ j ∈ Finset.range (clsNum W), ∑ u ∈ clsSet W j, ∑ p ∈ repPairs W u,
          (x : ℂ) ^ (Complex.I * (((p.1 - p.2 : ℝ)) : ℂ)))
      = ∑ u ∈ keySet W, ∑ p ∈ repPairs W u,
          (x : ℂ) ^ (Complex.I * (((p.1 - p.2 : ℝ)) : ℂ)) :=
    sum_clsSet (W := W) _
  have e3 : (∑ u ∈ keySet W, ∑ p ∈ repPairs W u,
          (x : ℂ) ^ (Complex.I * (((p.1 - p.2 : ℝ)) : ℂ)))
      = ∑ p ∈ pairSet W, (x : ℂ) ^ (Complex.I * (((p.1 - p.2 : ℝ)) : ℂ)) :=
    sum_keySet (W := W) _
  rw [e1, e2, e3, hpair]

theorem Rfun_pow4_le_sum_Zclass (W : Finset ℝ) {x : ℝ} (hx : 0 < x) :
    ‖Submission.GM.Rfun W x‖ ^ 4
      ≤ (clsNum W : ℝ) * ∑ j ∈ Finset.range (clsNum W), ‖Zclass W (clsSet W j) x‖ ^ 2 := by
  have hnorm : ‖∑ j ∈ Finset.range (clsNum W), Zclass W (clsSet W j) x‖ ^ 2
      = ‖Submission.GM.Rfun W x‖ ^ 4 := by
    rw [sum_Zclass_eq_normSq_Rfun W hx, Complex.sq_norm, Complex.normSq_ofReal]
    ring
  rw [← hnorm]
  calc ‖∑ j ∈ Finset.range (clsNum W), Zclass W (clsSet W j) x‖ ^ 2
      ≤ ((Finset.range (clsNum W)).card : ℝ)
          * ∑ j ∈ Finset.range (clsNum W), ‖Zclass W (clsSet W j) x‖ ^ 2 :=
        norm_sum_sq_le_card_mul_sum_norm_sq _ _
    _ = (clsNum W : ℝ) * ∑ j ∈ Finset.range (clsNum W), ‖Zclass W (clsSet W j) x‖ ^ 2 := by
        rw [Finset.card_range]

end Work.GM.Energy.EnergyCore
