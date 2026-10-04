import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.SymCalcStep8.CSqZ
import Submission.Work.Diff.STE.B3.SymCalcStep8.L2re_le_sqrt_CSqZ
import Submission.Work.Diff.STE.contDiff_seriesFun
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Duality on the Sobolev scale: boundedness on `Hᵗ` of the adjoint gives `H^{-t}`

The target `Work.Diff.STE.B3.SymCalcStep8.csqZ_neg_le_of_adjoint` is the abstract duality
principle behind the negative-Sobolev estimates of the `SymCalcStep8` files (for instance
`perTransfer_CSqZ_neg_le`): if an operator `T` on smooth `1`-periodic functions admits an adjoint
`Tstar` for the real `L²` pairing `L2re`, and `Tstar` is bounded on the *positive* level `Hᵗ`
(measured by `CSqZ t ∘ fourierCoeff`), then `T` is bounded on the *negative* level `H^{-t}`.

The proof is the standard Riesz-duality argument, carried out **without** a `sup` (the sum
`CSqZ` is only `tsum`-convergent, so one must exhibit a concrete test function):

* for a smooth `1`-periodic `W` put `V := seriesFun (fun k ↦ ⟨k⟩^{-t} · (T W)^(k))`.  It is smooth
  and `1`-periodic because the Fourier coefficients of a smooth `1`-periodic function decay faster
  than every polynomial (`contDiff_seriesFun` + `summable_wt_pow_mul_norm_fourierCoeff`);
* Fourier inversion (`flat.fourierCoeff_seriesFun`) identifies the coefficients of `V`, whence
  `CSqZ t (V̂) = CSqZ (-t) ((T W)^)` — the exponent identity `t + 2·(-t) = -t` of `wt`;
* Parseval (`integral_seriesFun_mul_conj`) gives `CSqZ (-t) ((T W)^) = L2re (T W) V`, and the
  adjointness hypothesis turns this into `L2re (Tstar V) W`;
* the weighted Cauchy–Schwarz estimate `L2re_le_sqrt_CSqZ` then bounds it by
  `√(CSqZ t (Tstar V)^) · √(CSqZ (-t) Ŵ)`, and the `Hᵗ`-bound for `Tstar` (applied to `V`) plus
  the value of `CSqZ t (V̂)` turn this into `A ≤ √(C₁ A) · √B` for the two target quantities `A`,
  `B`;
* the elementary algebraic lemma `A ≤ √(C₁ A)√B → A ≤ C₁ B` (trivial for `A = 0`, otherwise
  square and cancel) finishes the proof with `C = C₁`.

The auxiliary lemmas are kept general: they concern an arbitrary coefficient family `c` and the
weighted family `k ↦ ⟨k⟩^e c k`.
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3.SymCalcStep8

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Rapid decay of the Fourier coefficients, in `ℓ¹` form.**  For a smooth `1`-periodic `f` and
every `N`, the family `k ↦ ⟨k⟩^N · ‖f̂(k)‖` is summable.  This is the summability input of
`contDiff_seriesFun`: it says that the coefficient family decays faster than every polynomial.

Proof: put `c' k = ⟨k⟩^N f̂(k)`.  Then `⟨k⟩^s ‖c' k‖² = ⟨k⟩^{s+2N} ‖f̂(k)‖²` is summable at the
level `s + 2N` by `summable_weighted_fourierCoeff_of_contDiff`, so `Σ_k ‖c' k‖ < ∞` by the AM–GM
criterion `summable_norm_of_CSq`. -/
lemma summable_wt_pow_mul_norm_fourierCoeff (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfp : Work.Diff.STE.Periodic1 f) (N : ℕ) :
    Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖Work.Diff.STE.fourierCoeff f k‖) := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ, Fintype.card ι < 2 * s := ⟨Fintype.card ι + 1, by omega⟩
  have key : ∀ k : ι → ℤ, (Work.Diff.STE.wt k) ^ s
      * ‖(↑(((Work.Diff.STE.wt k) ^ N : ℝ)) : ℂ) * Work.Diff.STE.fourierCoeff f k‖ ^ 2
      = (Work.Diff.STE.wt k) ^ (s + 2 * N) * ‖Work.Diff.STE.fourierCoeff f k‖ ^ 2 := by
    intro k
    rw [norm_mul, Work.Diff.STE.ste_norm_ofReal,
      abs_of_nonneg (pow_nonneg (Work.Diff.STE.wt_pos k).le N), mul_pow,
      ← pow_mul (Work.Diff.STE.wt k) N 2, Nat.mul_comm N 2, ← mul_assoc,
      ← pow_add (Work.Diff.STE.wt k) s (2 * N)]
  have hc : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s
      * ‖((↑(((Work.Diff.STE.wt k) ^ N : ℝ)) : ℂ) * Work.Diff.STE.fourierCoeff f k)‖ ^ 2) :=
    (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff f hf hfp (s + 2 * N)).congr
      (fun k => (key k).symm)
  have hnorm := Work.Diff.STE.summable_norm_of_CSq s hs
    (fun k : ι → ℤ => (↑(((Work.Diff.STE.wt k) ^ N : ℝ)) : ℂ) * Work.Diff.STE.fourierCoeff f k) hc
  refine hnorm.congr (fun k => ?_)
  rw [norm_mul, Work.Diff.STE.ste_norm_ofReal,
    abs_of_nonneg (pow_nonneg (Work.Diff.STE.wt_pos k).le N)]

/-- The norm of a monomial multiple of a coefficient: `‖⟨k⟩^e · c‖ = ⟨k⟩^e ‖c‖`, because the
weight is positive. -/
lemma zpow_norm_mul (k : ι → ℤ) (e : ℤ) (c : ℂ) :
    ‖(↑(((Work.Diff.STE.wt k) ^ e : ℝ)) : ℂ) * c‖ = (Work.Diff.STE.wt k) ^ e * ‖c‖ := by
  rw [norm_mul, Work.Diff.STE.ste_norm_ofReal,
    abs_of_nonneg (zpow_nonneg (Work.Diff.STE.wt_pos k).le e)]

omit [DecidableEq ι] in
/-- The square of the weight at an integer exponent: `(⟨k⟩^e)² = ⟨k⟩^{2e}`. -/
lemma zpow_sq (k : ι → ℤ) (e : ℤ) :
    ((Work.Diff.STE.wt k) ^ e) ^ 2 = (Work.Diff.STE.wt k) ^ (2 * e) := by
  rw [← zpow_natCast ((Work.Diff.STE.wt k) ^ e) 2, ← zpow_mul]
  congr 1
  ring

/-- **The weighted mass of a monomial multiple.**  Multiplying a coefficient family by the real
weight `⟨k⟩^e` shifts the exponent of `CSqZ` by `2e`:

  `CSqZ m (fun k ↦ ⟨k⟩^e · c k) = CSqZ (m + 2e) c`.

(When `m = t` and `e = -t` this is the `⟨k⟩^t · ⟨k⟩^{-2t} = ⟨k⟩^{-t}` cancellation of the
duality argument.) -/
lemma CSqZ_zpow_mul (c : (ι → ℤ) → ℂ) (e m : ℤ) :
    CSqZ m (fun k => (↑(((Work.Diff.STE.wt k) ^ e : ℝ)) : ℂ) * c k) = CSqZ (m + 2 * e) c := by
  simp only [CSqZ]
  refine tsum_congr (fun k => ?_)
  rw [zpow_norm_mul k e (c k), mul_pow, zpow_sq k e, ← mul_assoc,
    ← zpow_add₀ (ne_of_gt (Work.Diff.STE.wt_pos k))]

omit [DecidableEq ι] in
/-- The pointwise star identity behind Parseval: `c · conj(⟨k⟩^e c) = ⟨k⟩^e ‖c‖²`, the right-hand
side being a real number. -/
lemma mul_star_zpow_mul (e : ℤ) (k : ι → ℤ) (c : ℂ) :
    c * star ((↑(((Work.Diff.STE.wt k) ^ e : ℝ)) : ℂ) * c)
      = ((↑(((Work.Diff.STE.wt k) ^ e * ‖c‖ ^ 2)) : ℝ) : ℂ) := by
  rw [star_mul, Complex.star_def, Complex.conj_ofReal]
  have h1 : c * (starRingEnd ℂ c * ↑(((Work.Diff.STE.wt k) ^ e : ℝ)))
      = ↑(((Work.Diff.STE.wt k) ^ e : ℝ)) * (c * starRingEnd ℂ c) := by ring
  rw [h1, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul]

/-- **Parseval for a monomial weight: the `L²` pairing of a Fourier series with the monomial
multiple of itself is the weighted mass.**  For an `ℓ¹` coefficient family `c` whose weighted
mass `Σ_k ⟨k⟩^e ‖c k‖²` converges,

  `L2re (seriesFun c) (seriesFun (fun k ↦ ⟨k⟩^e c k)) = CSqZ e c`.

This exhibits `CSqZ e c` as the value of the `L²` pairing against a *concrete* test function, which
is exactly the "Riesz representative without a `sup`" used in the duality argument. -/
lemma L2re_seriesFun_zpow_mul (e : ℤ) (c : (ι → ℤ) → ℂ)
    (hc : Summable fun k => ‖c k‖)
    (hd : Summable fun k => ‖(↑(((Work.Diff.STE.wt k) ^ e : ℝ)) : ℂ) * c k‖)
    (hs : Summable fun k => (Work.Diff.STE.wt k) ^ e * ‖c k‖ ^ 2) :
    Work.Diff.STE.L2re (Work.Diff.STE.seriesFun c)
      (Work.Diff.STE.seriesFun (fun k => (↑(((Work.Diff.STE.wt k) ^ e : ℝ)) : ℂ) * c k))
      = CSqZ e c := by
  rw [Work.Diff.STE.L2re, Work.Diff.STE.integral_seriesFun_mul_conj c _ hc hd]
  have hsumc : Summable
      (fun k : ι → ℤ => ((↑(((Work.Diff.STE.wt k) ^ e * ‖c k‖ ^ 2)) : ℝ) : ℂ)) :=
    Summable.of_norm_bounded hs (fun k => by
      rw [Work.Diff.STE.ste_norm_ofReal,
        abs_of_nonneg (mul_nonneg (zpow_nonneg (Work.Diff.STE.wt_pos k).le e) (sq_nonneg _))])
  rw [tsum_congr (fun k => mul_star_zpow_mul e k (c k)), Complex.re_tsum hsumc]
  simp only [CSqZ, Complex.ofReal_re]

/-- **Duality principle**: an operator `T` on smooth `1`-periodic functions that admits an
adjoint `Tstar` for the `L²` pairing and such that `Tstar` is bounded on the positive Sobolev
level `Hᵗ` (i.e. `CSqZ t ∘ fourierCoeff`) is bounded on the negative level `H^{-t}`.

Proof (the Riesz representative inserted without a `sup`): for smooth periodic `W` put
`V := seriesFun (fun k => (wt k)^{-t} · fourierCoeff (T W) k)`, which is smooth periodic because
the Fourier coefficients of `T W` decay rapidly.  Then `fourierCoeff V k = (wt k)^{-t} ·
fourierCoeff (T W) k`, so `CSqZ t (fourierCoeff V) = CSqZ (-t) (fourierCoeff (T W))` (the
`wt^t · wt^{-t} = 1` cancellation) and `CSqZ (-t) (fourierCoeff (T W)) = L2re (T W) V` (Parseval);
then `= L2re (Tstar V) W` (`hpair`) `≤ √(CSqZ t (fourierCoeff (Tstar V))) ·
√(CSqZ (-t) (fourierCoeff W))` (weighted Cauchy–Schwarz `L2re_le_sqrt_CSqZ`) `≤
√(C₁ · CSqZ (-t) (fourierCoeff (T W))) · √(CSqZ (-t) (fourierCoeff W))` (`hbd` and the value of
`CSqZ t (fourierCoeff V)`).  Writing `A` and `B` for the two factors and dividing
(`A ≤ √(C₁ A)√B`, trivial when `A = 0`) gives the claim with `C = C₁`. -/
theorem csqZ_neg_le_of_adjoint {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℕ)
    (T Tstar : ((ι → ℝ) → ℂ) → ((ι → ℝ) → ℂ))
    (hT : ∀ W : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) W → Work.Diff.STE.Periodic1 W →
      ContDiff ℝ (⊤ : ℕ∞) (T W) ∧ Work.Diff.STE.Periodic1 (T W))
    (hTs : ∀ V : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) V → Work.Diff.STE.Periodic1 V →
      ContDiff ℝ (⊤ : ℕ∞) (Tstar V) ∧ Work.Diff.STE.Periodic1 (Tstar V))
    (hpair : ∀ W V : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) W → Work.Diff.STE.Periodic1 W →
      ContDiff ℝ (⊤ : ℕ∞) V → Work.Diff.STE.Periodic1 V →
      Work.Diff.STE.L2re (T W) V = Work.Diff.STE.L2re (Tstar V) W)
    (hbd : ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ V : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) V →
      Work.Diff.STE.Periodic1 V →
      Work.Diff.STE.B3.SymCalcStep8.CSqZ (t : ℤ) (Work.Diff.STE.fourierCoeff (Tstar V))
        ≤ C₁ * Work.Diff.STE.B3.SymCalcStep8.CSqZ (t : ℤ) (Work.Diff.STE.fourierCoeff V)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) W → Work.Diff.STE.Periodic1 W →
      Work.Diff.STE.B3.SymCalcStep8.CSqZ (-(t : ℤ)) (Work.Diff.STE.fourierCoeff (T W))
        ≤ C * Work.Diff.STE.B3.SymCalcStep8.CSqZ (-(t : ℤ)) (Work.Diff.STE.fourierCoeff W) := by
  classical
  obtain ⟨C₁, hC₁nn, hbd⟩ := hbd
  refine ⟨C₁, hC₁nn, ?_⟩
  intro W hW hWp
  obtain ⟨hTW, hTWp⟩ := hT W hW hWp
  -- the two quantities of the target
  let A : ℝ := CSqZ (-(t : ℤ)) (Work.Diff.STE.fourierCoeff (T W))
  let B : ℝ := CSqZ (-(t : ℤ)) (Work.Diff.STE.fourierCoeff W)
  have hA0 : 0 ≤ A := CSqZ_nonneg (-(t : ℤ)) (Work.Diff.STE.fourierCoeff (T W))
  have hB0 : 0 ≤ B := CSqZ_nonneg (-(t : ℤ)) (Work.Diff.STE.fourierCoeff W)
  -- summability inputs coming from the smoothness of `T W`
  have hc1 : Summable fun k : ι → ℤ => ‖Work.Diff.STE.fourierCoeff (T W) k‖ :=
    summable_norm_fourierCoeff_of_contDiff (T W) hTW hTWp
  have hts : (-(t : ℤ)) ≤ (t : ℤ) := by omega
  have hs2 : Summable fun k : ι → ℤ =>
      (Work.Diff.STE.wt k) ^ (-(t : ℤ)) * ‖Work.Diff.STE.fourierCoeff (T W) k‖ ^ 2 :=
    summable_wt_zpow_mul_normSq (Work.Diff.STE.fourierCoeff (T W)) (-(t : ℤ)) t hts
      (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff (T W) hTW hTWp t)
  -- the Riesz representative family and the test function `V`
  let α : (ι → ℤ) → ℂ := fun k =>
    (↑(((Work.Diff.STE.wt k) ^ (-(t : ℤ)) : ℝ)) : ℂ) * Work.Diff.STE.fourierCoeff (T W) k
  let V : (ι → ℝ) → ℂ := Work.Diff.STE.seriesFun α
  have hv1 : Summable fun k : ι → ℤ => ‖α k‖ := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hc1
    show ‖(↑(((Work.Diff.STE.wt k) ^ (-(t : ℤ)) : ℝ)) : ℂ)
        * Work.Diff.STE.fourierCoeff (T W) k‖ ≤ ‖Work.Diff.STE.fourierCoeff (T W) k‖
    rw [zpow_norm_mul k (-(t : ℤ)) (Work.Diff.STE.fourierCoeff (T W) k)]
    calc (Work.Diff.STE.wt k) ^ (-(t : ℤ)) * ‖Work.Diff.STE.fourierCoeff (T W) k‖
        ≤ 1 * ‖Work.Diff.STE.fourierCoeff (T W) k‖ :=
          mul_le_mul_of_nonneg_right
            (zpow_le_one_of_nonpos₀ (Work.Diff.STE.wt_one_le k) (by omega)) (norm_nonneg _)
      _ = ‖Work.Diff.STE.fourierCoeff (T W) k‖ := one_mul _
  have hsm : ∀ N : ℕ, Summable fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖α k‖ := by
    intro N
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (Work.Diff.STE.wt_pos k).le N) (norm_nonneg _))
      (fun k => ?_) (summable_wt_pow_mul_norm_fourierCoeff (T W) hTW hTWp N)
    show (Work.Diff.STE.wt k) ^ N * ‖(↑(((Work.Diff.STE.wt k) ^ (-(t : ℤ)) : ℝ)) : ℂ)
        * Work.Diff.STE.fourierCoeff (T W) k‖
      ≤ (Work.Diff.STE.wt k) ^ N * ‖Work.Diff.STE.fourierCoeff (T W) k‖
    rw [zpow_norm_mul k (-(t : ℤ)) (Work.Diff.STE.fourierCoeff (T W) k)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (Work.Diff.STE.wt_pos k).le N)
    calc (Work.Diff.STE.wt k) ^ (-(t : ℤ)) * ‖Work.Diff.STE.fourierCoeff (T W) k‖
        ≤ 1 * ‖Work.Diff.STE.fourierCoeff (T W) k‖ :=
          mul_le_mul_of_nonneg_right
            (zpow_le_one_of_nonpos₀ (Work.Diff.STE.wt_one_le k) (by omega)) (norm_nonneg _)
      _ = ‖Work.Diff.STE.fourierCoeff (T W) k‖ := one_mul _
  -- `V` is smooth and `1`-periodic, with coefficients `α`
  have hVsm : ContDiff ℝ (⊤ : ℕ∞) V := Work.Diff.STE.contDiff_seriesFun α hsm
  have hVp : Work.Diff.STE.Periodic1 V := Work.Diff.STE.flat.periodic1_seriesFun α
  have hcoefV : Work.Diff.STE.fourierCoeff V = α :=
    funext fun k => Work.Diff.STE.flat.fourierCoeff_seriesFun α hv1 k
  -- the two identities of the duality argument
  have hCSqV : CSqZ (t : ℤ) (Work.Diff.STE.fourierCoeff V) = A := by
    rw [hcoefV, CSqZ_zpow_mul (Work.Diff.STE.fourierCoeff (T W)) (-(t : ℤ)) (t : ℤ)]
    congr 1
    ring
  have hL2re : Work.Diff.STE.L2re (T W) V = A := by
    rw [show T W = Work.Diff.STE.seriesFun (Work.Diff.STE.fourierCoeff (T W)) from
      funext fun x => (Work.Diff.STE.flat.seriesFun_fourierCoeff (T W) hTW hTWp x).symm]
    exact L2re_seriesFun_zpow_mul (-(t : ℤ)) (Work.Diff.STE.fourierCoeff (T W)) hc1 hv1 hs2
  -- the adjoint bound and the two inequalities
  obtain ⟨hTSsm, hTSp⟩ := hTs V hVsm hVp
  have hbdV : CSqZ (t : ℤ) (Work.Diff.STE.fourierCoeff (Tstar V)) ≤ C₁ * A := by
    rw [← hCSqV]; exact hbd V hVsm hVp
  have hCS := L2re_le_sqrt_CSqZ (t : ℤ) (Tstar V) W hTSsm hTSp hW hWp
  have hpairW := hpair W V hW hWp hVsm hVp
  have hmain : A ≤ Real.sqrt (C₁ * A) * Real.sqrt B := by
    have h3 : Real.sqrt (CSqZ (t : ℤ) (Work.Diff.STE.fourierCoeff (Tstar V)))
        ≤ Real.sqrt (C₁ * A) := Real.sqrt_le_sqrt hbdV
    calc A = Work.Diff.STE.L2re (Tstar V) W := by rw [← hpairW, hL2re]
      _ ≤ Real.sqrt (CSqZ (t : ℤ) (Work.Diff.STE.fourierCoeff (Tstar V))) * Real.sqrt B :=
          (le_abs_self _).trans hCS
      _ ≤ Real.sqrt (C₁ * A) * Real.sqrt B :=
          mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg B)
  -- the elementary step `A ≤ √(C₁ A) √B → A ≤ C₁ B`
  show A ≤ C₁ * B
  rcases eq_or_lt_of_le hA0 with hAle | hAlt
  · rw [← hAle]; exact mul_nonneg hC₁nn hB0
  · have hsq : A * A
        ≤ (Real.sqrt (C₁ * A) * Real.sqrt B) * (Real.sqrt (C₁ * A) * Real.sqrt B) :=
      mul_self_le_mul_self hA0 hmain
    have hval : (Real.sqrt (C₁ * A) * Real.sqrt B) * (Real.sqrt (C₁ * A) * Real.sqrt B)
        = A * (C₁ * B) := by
      rw [show (Real.sqrt (C₁ * A) * Real.sqrt B) * (Real.sqrt (C₁ * A) * Real.sqrt B)
          = (Real.sqrt (C₁ * A) * Real.sqrt (C₁ * A)) * (Real.sqrt B * Real.sqrt B) by ring,
        Real.mul_self_sqrt (mul_nonneg hC₁nn hA0), Real.mul_self_sqrt hB0]
      ring
    rw [hval] at hsq
    exact le_of_mul_le_mul_left hsq hAlt

end Work.Diff.STE.B3.SymCalcStep8
