import Mathlib
import Submission.Work.EQ.chain_family_defs
import Submission.Work.EQ.meromorphicAt_punctured_bounded

namespace Work.EQ

open Complex Metric Filter
open scoped Topology

/-- Bound on the forward arguments of `germC`: for `n > n₁` the argument `λ^n (u + κ t^k)` stays
inside the closed ball of radius `λ · ρg < ρg` on the punctured disc, because
`‖λ^n (u + κ t^k)‖ = λ^{n-n₁} · ‖λ^{n₁} (u + κ t^k)‖ ≤ λ · ‖λ^{n₁} (u + κ t^k)‖ < λ · ρg`. -/
theorem norm_zpow_mul_germ_arg_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {u κ : ℂ} {k n₁ : ℕ} {ρ ρg : ℝ}
    (hsmall : ∀ t, 0 < ‖t‖ → ‖t‖ < ρ →
      ‖((eqLam a : ℝ) : ℂ) ^ n₁ * (u + κ * t ^ k)‖ < ρg)
    {n : ℤ} (hn : ((n₁ : ℕ) : ℤ) < n) {t : ℂ} (ht : 0 < ‖t‖) (ht' : ‖t‖ < ρ) :
    ‖((eqLam a : ℝ) : ℂ) ^ n * (u + κ * t ^ k)‖ ≤ eqLam a * ρg := by
  have hcne : ((eqLam a : ℝ) : ℂ) ≠ 0 := win_eqLamC_ne_zero ha0 ha1
  have harg : ‖((eqLam a : ℝ) : ℂ) ^ (((n₁ : ℕ) : ℤ)) * (u + κ * t ^ k)‖ < ρg := by
    simpa using hsmall t ht ht'
  have hfac : ((eqLam a : ℝ) : ℂ) ^ n * (u + κ * t ^ k) =
      ((eqLam a : ℝ) : ℂ) ^ (n - ((n₁ : ℕ) : ℤ)) *
        (((eqLam a : ℝ) : ℂ) ^ ((n₁ : ℕ) : ℤ) * (u + κ * t ^ k)) := by
    rw [show ((eqLam a : ℝ) : ℂ) ^ n = ((eqLam a : ℝ) : ℂ) ^ (n - ((n₁ : ℕ) : ℤ)) *
        ((eqLam a : ℝ) : ℂ) ^ ((n₁ : ℕ) : ℤ) by
          rw [← zpow_add₀ hcne]; congr 1; ring]
    rw [mul_assoc]
  rw [hfac, norm_mul]
  have hzle : ‖((eqLam a : ℝ) : ℂ) ^ (n - ((n₁ : ℕ) : ℤ))‖ ≤ eqLam a := by
    rw [norm_zpow, win_norm_eqLamC ha0 ha1]
    rw [show n - ((n₁ : ℕ) : ℤ) = (((n - ((n₁ : ℕ) : ℤ)).toNat : ℕ) : ℤ) by omega,
      zpow_natCast]
    calc eqLam a ^ (n - ((n₁ : ℕ) : ℤ)).toNat ≤ eqLam a ^ 1 :=
          pow_le_pow_of_le_one (le_of_lt (win_eqLam_pos ha0 ha1))
            (le_of_lt (win_eqLam_lt_one ha0 ha1)) (by omega)
      _ = eqLam a := pow_one _
  calc ‖((eqLam a : ℝ) : ℂ) ^ (n - ((n₁ : ℕ) : ℤ))‖ *
        ‖((eqLam a : ℝ) : ℂ) ^ ((n₁ : ℕ) : ℤ) * (u + κ * t ^ k)‖
      ≤ eqLam a * ‖((eqLam a : ℝ) : ℂ) ^ ((n₁ : ℕ) : ℤ) * (u + κ * t ^ k)‖ :=
        mul_le_mul_of_nonneg_right hzle (norm_nonneg _)
    _ ≤ eqLam a * ρg :=
        mul_le_mul_of_nonneg_left (le_of_lt harg) (le_of_lt (win_eqLam_pos ha0 ha1))

/-- Forward-tail case of the meromorphy of the window chain: for `n > n₁` the `n`-th entry of
`windowChain a h n₁ m₁ u κ k (psi2 a Yinv β) β t` is `germC a h (λ^n (u + κ t^k))`, and both of its
coordinates are meromorphic at `0`. -/
theorem windowChain_meromorphicAt_fwd {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {n₁ m₁ : ℕ} {u κ : ℂ} {k : ℕ} {ρ ρg : ℝ} (hρ : 0 < ρ) (hρg : 0 < ρg)
    (hgerm_an : AnalyticOnNhd ℂ (germC a h) (Metric.ball (0 : ℂ) ρg))
    (hsmall : ∀ t, 0 < ‖t‖ → ‖t‖ < ρ →
      ‖((eqLam a : ℝ) : ℂ) ^ n₁ * (u + κ * t ^ k)‖ < ρg)
    {n : ℤ} (hn : ((n₁ : ℕ) : ℤ) < n) :
    MeromorphicAt (fun t => (germC a h (((eqLam a : ℝ) : ℂ) ^ n * (u + κ * t ^ k))).1) 0 ∧
    MeromorphicAt (fun t => (germC a h (((eqLam a : ℝ) : ℂ) ^ n * (u + κ * t ^ k))).2) 0 := by
  -- `n > n₁` gives `n₁ ≤ n`, so the forward arguments are analytic on the punctured disc.
  have hnle : ((n₁ : ℕ) : ℤ) ≤ n := by omega
  have han := windowChain_analyticOnNhd_germC_fwd ha0 ha1 hsmall hgerm_an hnle
  -- the arguments stay in the closed ball of radius `λ · ρg < ρg`, on which `germC a h` is bounded.
  have hRlt : eqLam a * ρg < ρg := by
    nlinarith [win_eqLam_lt_one ha0 ha1, win_eqLam_pos ha0 ha1, hρg]
  obtain ⟨M, hM⟩ := exists_norm_bound_germC (a := a) (h := h) (ρg := ρg)
    (R := eqLam a * ρg) hRlt hgerm_an
  have hmem : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
      ‖((eqLam a : ℝ) : ℂ) ^ n * (u + κ * t ^ k)‖ ≤ eqLam a * ρg := by
    intro t ht
    exact norm_zpow_mul_germ_arg_le ha0 ha1 hsmall hn
      (norm_pos_iff.mpr ht.2) (by simpa [Metric.mem_ball, dist_eq_norm] using ht.1)
  constructor
  · refine meromorphicAt_punctured_bounded (C := M) hρ ?_ ?_
    · intro t ht
      exact ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _).comp (han t ht)
    · intro t ht
      exact le_trans (norm_fst_le _) (hM _ (hmem t ht))
  · refine meromorphicAt_punctured_bounded (C := M) hρ ?_ ?_
    · intro t ht
      exact ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _).comp (han t ht)
    · intro t ht
      exact le_trans (norm_snd_le _) (hM _ (hmem t ht))

end Work.EQ
