import Mathlib
import Submission.Work.EQ.chain_family_defs

namespace Work.EQ

open Complex Metric

/-! ## Index arithmetic for `windowIdx` -/

/-- The window entry at ℤ-index `n` with `-m₁ ≤ n < n₁` is the `castSucc` of the `Fin`-entry
`n + m₁`. -/
private lemma windowIdx_window_castSucc (n₁ m₁ : ℕ) (n : ℤ)
    (hle : -((m₁ : ℤ)) ≤ n) (hlt : n < ((n₁ : ℕ) : ℤ)) :
    windowIdx n₁ m₁ n ⟨hle, by omega⟩ =
      Fin.castSucc (⟨(n + (m₁ : ℤ)).toNat, by omega⟩ : Fin (n₁ + m₁)) := by
  apply Fin.ext
  rw [windowIdx_val, Fin.val_castSucc]

/-- The window entry at ℤ-index `n+1` with `-m₁ ≤ n < n₁` is the `succ` of the `Fin`-entry
`n + m₁`. -/
private lemma windowIdx_window_succIdx (n₁ m₁ : ℕ) (n : ℤ)
    (hle : -((m₁ : ℤ)) ≤ n) (hlt : n < ((n₁ : ℕ) : ℤ)) :
    windowIdx n₁ m₁ (n + 1) ⟨by omega, by omega⟩ =
      Fin.succ (⟨(n + (m₁ : ℤ)).toNat, by omega⟩ : Fin (n₁ + m₁)) := by
  apply Fin.ext
  simp only [windowIdx_val, Fin.val_succ]
  have : (n + 1 + (m₁ : ℤ)).toNat = (n + (m₁ : ℤ)).toNat + 1 := by omega
  omega

/-- The first window entry (`j = -m₁`) is `0`. -/
private lemma windowIdx_neg_m₁ (n₁ m₁ : ℕ)
    {hj : -((m₁ : ℤ)) ≤ -((m₁ : ℤ)) ∧ -((m₁ : ℤ)) ≤ ((n₁ : ℕ) : ℤ)} :
    windowIdx n₁ m₁ (-((m₁ : ℤ))) hj = (0 : Fin (n₁ + m₁ + 1)) := by
  apply Fin.ext
  rw [windowIdx_val, Fin.val_zero]
  omega

/-! ## The two generic chain steps -/

/-- The forward step of the germ `germC a h`: if the step is regular at `v`, it is regular at `v`
in the form produced by `windowChain`. -/
private lemma regPair_germC_step {a : ℝ} {h : ℂ → ℂ} {ρg : ℝ}
    (hstep : ∀ v : ℂ, v ∈ Metric.ball (0 : ℂ) ρg →
      RegPair a (germC a h v) (germC a h (((eqLam a : ℝ) : ℂ) * v)))
    {v : ℂ} (hv : v ∈ Metric.ball (0 : ℂ) ρg) :
    RegPair a (germC a h v) (germC a h (((eqLam a : ℝ) : ℂ) * v)) := hstep v hv

/-- The backward step of the mirrored germ `ugermC a h` (bisector reflection of the forward step):
`RegPair a (ugermC a h (λ v)) (ugermC a h v)`.  This is the direction in which the backward tail
of `windowChain` decreases: the entry at ℤ-index `j` has argument `λ^{-j} ψ₂`, so the step from `j`
to `j+1` multiplies the argument by `λ`. -/
private lemma regPair_ugermC_step {a : ℝ} {h : ℂ → ℂ} {ρg : ℝ}
    (hstep : ∀ v : ℂ, v ∈ Metric.ball (0 : ℂ) ρg →
      RegPair a (germC a h v) (germC a h (((eqLam a : ℝ) : ℂ) * v)))
    {v : ℂ} (hv : v ∈ Metric.ball (0 : ℂ) ρg) :
    RegPair a (ugermC a h (((eqLam a : ℝ) : ℂ) * v)) (ugermC a h v) := by
  rw [ugermC, ugermC]
  exact (H0_invParam_ge_regPair_mirror).mpr (regPair_germC_step hstep hv)

/-- **The chain built from a window is a chain of regular pairs.**  For every integer index the
pair of consecutive entries of `windowChain a h n₁ m₁ u κ k (psi2 a Yinv β) β t` is regular.
The five cases (`n ≤ -m₁-2`, `n = -m₁-1`, `-m₁ ≤ n ≤ n₁-1`, `n = n₁`, `n ≥ n₁+1`):
* *forward* (`n ≥ n₁+1`): `hgerm_reg` at `v = λ^n (u+κt^k)`, which lies in `ball 0 ρg` because
  `‖λ^n (u+κt^k)‖ ≤ ‖λ^{n₁}(u+κt^k)‖` (`hsmall`) times the factor `λ^{n-n₁} ≤ 1` (`norm_zpow_mul_germ_arg_lt` in `chain_family_defs`);
* *junction* (`n = n₁`): `hβend` identifies the first entry with `germC a h (λ^{n₁}(u+κt^k))` and
  `hgerm_reg` at that point (`hsmall`) gives the step;
* *window* (`-m₁ ≤ n ≤ n₁-1`): `hβreg` at `j : Fin (n₁+m₁)` with `windowIdx_castSucc`,
  `windowIdx_succIdx`;
* *junction* (`n = -m₁-1`): `hβcurve` gives the witness `w` with `β t 0 = ugermC a h w`; use
  `Work.EQ.H0_invParam_ge_regPair_mirror` (`RegPair a (eqMirror Q) (eqMirror P) ↔ RegPair a P Q`) at
  the regular pair `hgerm_reg` at `v = w` (with `w ∈ ball 0 ρY ⊆ ball 0 ρg`);
* *backward* (`n ≤ -m₁-2`): same mirror trick with `hgerm_reg` at `v = λ^{-n-1} ψ₂ t`, using
  `windowChain_psi2_witness` to see `λ^{-n-1}ψ₂ t = λ^{-n-1-m₁} w` has norm `≤ ‖w‖ < ρY ≤ ρg`. -/
theorem windowChain_regPair {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {n₁ m₁ : ℕ}
    {u κ : ℂ} {k : ℕ} {ρ ρg ρY : ℝ} (hρ : 0 < ρ) {Yinv : ℂ → ℂ}
    {β : ℂ → Fin (n₁ + m₁ + 1) → ℂ × ℂ}
    (hgerm_reg : ∀ v : ℂ, v ∈ Metric.ball (0 : ℂ) ρg →
      RegPair a (germC a h v) (germC a h (((eqLam a : ℝ) : ℂ) * v)))
    (hsmall : ∀ t, 0 < ‖t‖ → ‖t‖ < ρ →
      ‖((eqLam a : ℝ) : ℂ) ^ n₁ * (u + κ * t ^ k)‖ < ρg)
    (hβend : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0}, β t (Fin.last (n₁ + m₁)) =
      germC a h (((eqLam a : ℝ) : ℂ) ^ n₁ * (u + κ * t ^ k)))
    (hβreg : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0}, ∀ j : Fin (n₁ + m₁),
      RegPair a (β t (Fin.castSucc j)) (β t (Fin.succ j)))
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((germC a h w).2) = w)
    (hβcurve : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
      ∃ w, w ∈ Metric.ball (0 : ℂ) ρY ∧ w ≠ 0 ∧ ugermC a h w = β t 0)
    (hρYg : ρY ≤ ρg) {t : ℂ} (ht : t ∈ Metric.ball (0 : ℂ) ρ \ {0}) :
    ∀ n : ℤ, RegPair a ((windowChain a h n₁ m₁ u κ k (psi2 a Yinv β) β t).1 n)
      ((windowChain a h n₁ m₁ u κ k (psi2 a Yinv β) β t).1 (n + 1)) := by
  have hlam : ((eqLam a : ℝ) : ℂ) ≠ 0 := win_eqLamC_ne_zero ha0 ha1
  intro n
  by_cases hbwd : n < -((m₁ : ℤ))
  · -- ## backward region (`n < -m₁`)
    by_cases hjn : n + 1 < -((m₁ : ℤ))
    · -- backward step (`n ≤ -m₁-2`)
      rw [windowChain_fst_of_bwd (j := n) t hbwd,
        windowChain_fst_of_bwd (j := n + 1) t hjn]
      have hmem : ((eqLam a : ℝ) : ℂ) ^ (-(n + 1)) * psi2 a Yinv β t
          ∈ Metric.ball (0 : ℂ) ρg :=
        windowChain_mem_ball_zpow_mul_psi2 ha0 ha1 hlam hY3 hβcurve hρYg (n := n + 1) hjn ht
      have hde : ((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t =
          ((eqLam a : ℝ) : ℂ) * (((eqLam a : ℝ) : ℂ) ^ (-(n + 1)) * psi2 a Yinv β t) := by
        rw [show -n = (-(n + 1)) + 1 by ring, zpow_add_one₀ hlam]; ring
      rw [hde]
      exact regPair_ugermC_step hgerm_reg hmem
    · -- junction (`n = -m₁-1`)
      have hjn' : n + 1 = -((m₁ : ℤ)) := by omega
      obtain ⟨w, hw, _, hmul, hwcurve, _⟩ := windowChain_psi2_witness hlam hY3 hβcurve ht
      rw [windowChain_fst_of_bwd (j := n) t hbwd, hjn',
        windowChain_fst_of_window (j := -((m₁ : ℤ))) t ⟨by omega, by omega⟩,
        windowIdx_neg_m₁, ← hwcurve]
      have hde : ((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t = ((eqLam a : ℝ) : ℂ) * w := by
        have hn : -n = (m₁ : ℤ) + 1 := by omega
        rw [hn, zpow_add_one₀ hlam, zpow_natCast, ← hmul]; ring
      rw [hde]
      exact regPair_ugermC_step hgerm_reg (Metric.ball_subset_ball hρYg hw)
  · -- ## `n ≥ -m₁`
    simp only [not_lt] at hbwd
    by_cases hwin : n < ((n₁ : ℕ) : ℤ)
    · -- window region (`-m₁ ≤ n ≤ n₁-1`)
      rw [windowChain_fst_of_window (j := n) t ⟨hbwd, by omega⟩,
        windowChain_fst_of_window (j := n + 1) t ⟨by omega, by omega⟩,
        windowIdx_window_castSucc n₁ m₁ n hbwd hwin,
        windowIdx_window_succIdx n₁ m₁ n hbwd hwin]
      exact hβreg t ht ⟨(n + (m₁ : ℤ)).toNat, by omega⟩
    · have hn1 : ((n₁ : ℕ) : ℤ) ≤ n := not_lt.mp hwin
      rcases eq_or_lt_of_le hn1 with hmid | hgt
      · -- junction (`n = n₁`)
        subst hmid
        rw [windowChain_fst_of_window (j := ((n₁ : ℕ) : ℤ)) t ⟨by omega, by omega⟩,
          windowChain_fst_of_fwd (j := ((n₁ : ℕ) : ℤ) + 1) t (by omega),
          windowIdx_last, hβend t ht]
        have hmem : ((eqLam a : ℝ) : ℂ) ^ n₁ * (u + κ * t ^ k) ∈ Metric.ball (0 : ℂ) ρg := by
          rw [Metric.mem_ball, dist_zero_right]
          exact hsmall t (norm_pos_iff.mpr ht.2)
            (by have h1 := ht.1; rwa [Metric.mem_ball, dist_zero_right] at h1)
        rw [show ((eqLam a : ℝ) : ℂ) ^ (((n₁ : ℕ) : ℤ) + 1) * (u + κ * t ^ k) =
            ((eqLam a : ℝ) : ℂ) * (((eqLam a : ℝ) : ℂ) ^ n₁ * (u + κ * t ^ k)) by
          rw [zpow_add_one₀ hlam, zpow_natCast]; ring]
        exact hgerm_reg _ hmem
      · -- forward region (`n ≥ n₁+1`)
        rw [windowChain_fst_of_fwd (j := n) t hgt,
          windowChain_fst_of_fwd (j := n + 1) t (by omega)]
        have hmem : ((eqLam a : ℝ) : ℂ) ^ n * (u + κ * t ^ k) ∈ Metric.ball (0 : ℂ) ρg := by
          rw [Metric.mem_ball, dist_zero_right]
          exact norm_zpow_mul_germ_arg_lt ha0 ha1 hsmall (le_of_lt hgt) ht
        rw [show ((eqLam a : ℝ) : ℂ) ^ (n + 1) * (u + κ * t ^ k) =
            ((eqLam a : ℝ) : ℂ) * (((eqLam a : ℝ) : ℂ) ^ n * (u + κ * t ^ k)) by
          rw [zpow_add_one₀ hlam]; ring]
        exact hgerm_reg _ hmem

end Work.EQ
