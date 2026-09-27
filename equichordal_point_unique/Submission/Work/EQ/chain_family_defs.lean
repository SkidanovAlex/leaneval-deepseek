import Mathlib
import Submission.Work.EQ.germC_graph
import Submission.Work.EQ.H0_invParam_ge

/-! # The window-to-chain construction: definitions and basic facts

This file sets up the objects used by `Work.EQ.chain_family_of_window`.  A *window* is a family
`β t : Fin (n₁+m₁+1) → ℂ × ℂ` of chains ending at the stable leaf
`germC a h (λ^{n₁}(u + κ t^k))` whose first entry lies on the small unstable germ curve
(`ugermC a h w = β t 0`).  It is extended to a bi-infinite chain

`windowChain a h n₁ m₁ u κ k ψ₂ β t :=
  (fun j => if -m₁ ≤ j ≤ n₁ then β t (j+m₁) else if n₁ < j then germC (λ^j (u+κt^k))
            else ugermC (λ^{-j} ψ₂ t), u+κt^k, ψ₂ t)`,

with `ψ₂ t := psi2 a Yinv β t = Yinv ((β t 0).2) / λ^{m₁}`.

The file collects the definitions and the per-point consequences of the window hypotheses: the
witness identity `λ^{m₁} ψ₂ t = Yinv ((β t 0).2) = w` (`windowChain_psi2_witness`), the
non-vanishing of `ψ₂`, analyticity of the pieces on the punctured disc, and the norm bounds that
place the arguments of `germC` inside its ball of analyticity. -/

namespace Work.EQ

open Complex Metric Filter
open scoped Topology

noncomputable section

/-! ## The index of a window entry -/

/-- The index in `Fin (n₁+m₁+1)` of the window entry with ℤ-coordinate `j` (`-m₁ ≤ j ≤ n₁`):
the shift by `m₁` realises the window as the indices `-m₁, …, n₁` of the bi-infinite chain. -/
noncomputable def windowIdx (n₁ m₁ : ℕ) (j : ℤ)
    (hj : -((m₁ : ℤ)) ≤ j ∧ j ≤ ((n₁ : ℕ) : ℤ)) : Fin (n₁ + m₁ + 1) :=
  ⟨(j + (m₁ : ℤ)).toNat, by omega⟩

theorem windowIdx_val (n₁ m₁ : ℕ) (j : ℤ)
    (hj : -((m₁ : ℤ)) ≤ j ∧ j ≤ ((n₁ : ℕ) : ℤ)) :
    (windowIdx n₁ m₁ j hj).val = (j + (m₁ : ℤ)).toNat := rfl

/-- The window entry at ℤ-index `j` is the `Fin`-entry `j + m₁`. -/
theorem windowIdx_sub_m₁ (n₁ m₁ : ℕ) (i : Fin (n₁ + m₁ + 1)) :
    windowIdx n₁ m₁ (((i : ℕ) : ℤ) - (m₁ : ℤ)) (by omega) = i := by
  ext
  rw [windowIdx_val]
  rw [show (((i : ℕ) : ℤ) - (m₁ : ℤ)) + (m₁ : ℤ) = ((i : ℕ) : ℤ) by ring, Int.toNat_natCast]

/-- The last window entry (`j = n₁`) is `Fin.last`. -/
theorem windowIdx_last (n₁ m₁ : ℕ) :
    windowIdx n₁ m₁ ((n₁ : ℕ) : ℤ) (by omega) = Fin.last (n₁ + m₁) := by
  ext
  rw [windowIdx_val, Fin.val_last]
  rw [show ((n₁ : ℤ) + (m₁ : ℤ)) = ((n₁ + m₁ : ℕ) : ℤ) by push_cast; ring,
    Int.toNat_natCast]

/-- The window entry at ℤ-index `j.val - m₁` is the `j`-th entry of the window. -/
theorem windowIdx_castSucc (n₁ m₁ : ℕ) (j : Fin (n₁ + m₁)) :
    windowIdx n₁ m₁ (((j : ℕ) : ℤ) - (m₁ : ℤ)) (by have := j.isLt; omega) =
      Fin.castSucc j := by
  ext
  rw [windowIdx_val, Fin.val_castSucc]
  rw [show ((((j : ℕ)) : ℤ) - (m₁ : ℤ) + (m₁ : ℤ)) = ((j.val : ℕ) : ℤ) by ring,
    Int.toNat_natCast]

/-- The window entry at ℤ-index `j.val + 1 - m₁` is the `(j+1)`-th entry of the window. -/
theorem windowIdx_succIdx (n₁ m₁ : ℕ) (j : Fin (n₁ + m₁)) :
    windowIdx n₁ m₁ ((((j : ℕ) : ℤ) + 1 - (m₁ : ℤ))) (by have := j.isLt; omega) =
      Fin.succ j := by
  ext
  rw [windowIdx_val, Fin.val_succ]
  rw [show ((((j : ℕ) : ℤ) + 1 - (m₁ : ℤ)) + (m₁ : ℤ)) = ((j.val + 1 : ℕ) : ℤ) by
        push_cast; ring, Int.toNat_natCast]

variable {a : ℝ} {h : ℂ → ℂ} {n₁ m₁ : ℕ} {u κ : ℂ} {k : ℕ} {ρ ρg ρY : ℝ}
  {Yinv : ℂ → ℂ} {ψ₂ : ℂ → ℂ} {β : ℂ → Fin (n₁ + m₁ + 1) → ℂ × ℂ}

/-! ## The backward parameter and the chain of a window -/

/-- The backward linearising parameter of the chain built from a window, as in
`Work.EQ.chain_family_of_window`: `ψ₂ t = Yinv ((β t 0).2) / λ^{m₁}`. -/
noncomputable def psi2 {n₁ m₁ : ℕ} (a : ℝ) (Yinv : ℂ → ℂ)
    (β : ℂ → Fin (n₁ + m₁ + 1) → ℂ × ℂ) : ℂ → ℂ :=
  fun t => Yinv ((β t (0 : Fin (n₁ + m₁ + 1))).2) / ((eqLam a : ℝ) : ℂ) ^ m₁

/-- The bi-infinite chain determined by a window `β` and the parameters `u`, `κ`, `k`, `ψ₂`. -/
noncomputable def windowChain (a : ℝ) (h : ℂ → ℂ) (n₁ m₁ : ℕ) (u κ : ℂ) (k : ℕ)
    (ψ₂ : ℂ → ℂ) (β : ℂ → Fin (n₁ + m₁ + 1) → ℂ × ℂ) : ℂ → ChainData :=
  fun t => (fun j : ℤ =>
      if hj : -((m₁ : ℤ)) ≤ j ∧ j ≤ ((n₁ : ℕ) : ℤ) then β t (windowIdx n₁ m₁ j hj)
      else if ((n₁ : ℕ) : ℤ) < j then
        germC a h (((eqLam a : ℝ) : ℂ) ^ j * (u + κ * t ^ k))
      else ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-j) * ψ₂ t),
    u + κ * t ^ k, ψ₂ t)

@[simp] theorem windowChain_fst_eq (t : ℂ) :
    (windowChain a h n₁ m₁ u κ k ψ₂ β t).1 =
      (fun j : ℤ =>
        if hj : -((m₁ : ℤ)) ≤ j ∧ j ≤ ((n₁ : ℕ) : ℤ) then β t (windowIdx n₁ m₁ j hj)
        else if ((n₁ : ℕ) : ℤ) < j then
          germC a h (((eqLam a : ℝ) : ℂ) ^ j * (u + κ * t ^ k))
        else ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-j) * ψ₂ t)) := rfl

@[simp] theorem windowChain_snd_fst (t : ℂ) :
    (windowChain a h n₁ m₁ u κ k ψ₂ β t).2.1 = u + κ * t ^ k := rfl

@[simp] theorem windowChain_snd_snd (t : ℂ) :
    (windowChain a h n₁ m₁ u κ k ψ₂ β t).2.2 = ψ₂ t := rfl

/-- The window part of the chain. -/
theorem windowChain_fst_of_window {j : ℤ} (t : ℂ)
    (hj : -((m₁ : ℤ)) ≤ j ∧ j ≤ ((n₁ : ℕ) : ℤ)) :
    (windowChain a h n₁ m₁ u κ k ψ₂ β t).1 j = β t (windowIdx n₁ m₁ j hj) := by
  simp only [windowChain_fst_eq]
  exact dite_eq_left hj

/-- The forward tail of the chain. -/
theorem windowChain_fst_of_fwd {j : ℤ} (t : ℂ) (hj : ((n₁ : ℕ) : ℤ) < j) :
    (windowChain a h n₁ m₁ u κ k ψ₂ β t).1 j =
      germC a h (((eqLam a : ℝ) : ℂ) ^ j * (u + κ * t ^ k)) := by
  simp only [windowChain_fst_eq]
  rw [dite_eq_right (by omega), ite_eq_left hj]

/-- The backward tail of the chain. -/
theorem windowChain_fst_of_bwd {j : ℤ} (t : ℂ) (hj : j < -((m₁ : ℤ))) :
    (windowChain a h n₁ m₁ u κ k ψ₂ β t).1 j =
      ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-j) * ψ₂ t) := by
  simp only [windowChain_fst_eq]
  rw [dite_eq_right (by omega), ite_eq_right (by omega)]

/-! ## Elementary facts about `λ = eqLam a` -/

theorem win_eqLam_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < eqLam a := by
  rw [eqLam]; exact div_pos (by linarith) (by linarith)

theorem win_eqLam_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : eqLam a < 1 := by
  rw [eqLam, div_lt_one (by linarith)]; linarith

theorem win_eqLamC_ne_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ((eqLam a : ℝ) : ℂ) ≠ 0 := by
  rw [← Complex.ofReal_zero, ne_eq, Complex.ofReal_inj]
  exact ne_of_gt (win_eqLam_pos ha0 ha1)

theorem win_norm_eqLamC {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ‖((eqLam a : ℝ) : ℂ)‖ = eqLam a := by
  have h : ‖((eqLam a : ℝ) : ℂ)‖ = |eqLam a| := by simp
  rw [h, abs_of_pos (win_eqLam_pos ha0 ha1)]

theorem win_eqLam_zpow_le_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {j : ℤ}
    (hj : 0 ≤ j) : eqLam a ^ j ≤ 1 := by
  rw [show j = ((j.toNat : ℕ) : ℤ) by omega, zpow_natCast]
  exact pow_le_one₀ (le_of_lt (win_eqLam_pos ha0 ha1)) (le_of_lt (win_eqLam_lt_one ha0 ha1))

theorem win_norm_eqLamC_zpow_le_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {j : ℤ}
    (hj : 0 ≤ j) : ‖((eqLam a : ℝ) : ℂ) ^ j‖ ≤ 1 := by
  rw [norm_zpow, win_norm_eqLamC ha0 ha1, show j = ((j.toNat : ℕ) : ℤ) by omega, zpow_natCast]
  exact pow_le_one₀ (le_of_lt (win_eqLam_pos ha0 ha1)) (le_of_lt (win_eqLam_lt_one ha0 ha1))

theorem win_norm_eqLamC_zpow_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {j : ℤ}
    (hj : 1 ≤ j) : ‖((eqLam a : ℝ) : ℂ) ^ j‖ < 1 := by
  rw [norm_zpow, win_norm_eqLamC ha0 ha1, show j = ((j.toNat : ℕ) : ℤ) by omega, zpow_natCast]
  exact pow_lt_one₀ (le_of_lt (win_eqLam_pos ha0 ha1)) (win_eqLam_lt_one ha0 ha1) (by omega)

/-! ## The punctured disc is a punctured neighbourhood of `0` -/

theorem ball_diff_zero_mem_nhdsWithin {ρ : ℝ} (hρ : 0 < ρ) :
    Metric.ball (0 : ℂ) ρ \ {0} ∈ 𝓝[≠] (0 : ℂ) := by
  have h1 : Metric.ball (0 : ℂ) ρ ∈ 𝓝[≠] (0 : ℂ) :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hρ)
  have h2 : ({0} : Set ℂ)ᶜ ∈ 𝓝[≠] (0 : ℂ) := self_mem_nhdsWithin
  exact Filter.mem_of_superset (Filter.inter_mem h1 h2) (by rintro z ⟨hz1, hz2⟩; exact ⟨hz1, hz2⟩)

/-! ## A uniform bound for `germC` on a compact sub-ball -/

/-- `germC a h` is bounded on every closed ball strictly inside its ball of analyticity. -/
theorem exists_norm_bound_germC {a : ℝ} {h : ℂ → ℂ} {ρg R : ℝ} (hR : R < ρg)
    (han : AnalyticOnNhd ℂ (germC a h) (Metric.ball (0 : ℂ) ρg)) :
    ∃ M : ℝ, ∀ z : ℂ, ‖z‖ ≤ R → ‖germC a h z‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    (han.continuousOn.mono fun z hz => by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt (by simpa [Metric.mem_closedBall, dist_zero_right] using hz) hR)
  exact ⟨M, fun z hz => hM z (by simpa [Metric.mem_closedBall, dist_zero_right] using hz)⟩

/-! ## The witness on the unstable germ curve -/

/-- The witness on the small unstable germ curve, and the resulting value of `ψ₂`:
`λ^{m₁} ψ₂ t = Yinv ((β t 0).2) = w`. -/
theorem windowChain_psi2_witness (hlam : ((eqLam a : ℝ) : ℂ) ≠ 0)
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((germC a h w).2) = w)
    (hβcurve : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
      ∃ w, w ∈ Metric.ball (0 : ℂ) ρY ∧ w ≠ 0 ∧ ugermC a h w = β t 0)
    {t : ℂ} (ht : t ∈ Metric.ball (0 : ℂ) ρ \ {0}) :
    ∃ w, w ∈ Metric.ball (0 : ℂ) ρY ∧ w ≠ 0 ∧
      ((eqLam a : ℝ) : ℂ) ^ m₁ * psi2 a Yinv β t = w ∧
      ugermC a h w = β t 0 ∧ Yinv ((β t 0).2) = w := by
  obtain ⟨w, hw, hwne, hwcurve⟩ := hβcurve t ht
  have hsnd : (β t 0).2 = (germC a h w).2 := by
    have hh := congrArg Prod.snd hwcurve
    simpa [ugermC, eqMirror] using hh.symm
  refine ⟨w, hw, hwne, ?_, hwcurve, by rw [hsnd]; exact hY3 w hw⟩
  rw [psi2, hsnd, hY3 w hw, mul_div_cancel₀ _ (pow_ne_zero _ hlam)]

/-- `ψ₂` does not vanish (the window hypothesis keeps the witness nonzero). -/
theorem windowChain_psi2_ne_zero (hlam : ((eqLam a : ℝ) : ℂ) ≠ 0)
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((germC a h w).2) = w)
    (hβcurve : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
      ∃ w, w ∈ Metric.ball (0 : ℂ) ρY ∧ w ≠ 0 ∧ ugermC a h w = β t 0)
    {t : ℂ} (ht : t ∈ Metric.ball (0 : ℂ) ρ \ {0}) : psi2 a Yinv β t ≠ 0 := by
  obtain ⟨w, -, hwne, hmul, -, -⟩ := windowChain_psi2_witness hlam hY3 hβcurve ht
  intro h0
  rw [h0, mul_zero] at hmul
  exact hwne hmul.symm

/-- The `y`-coordinate of the first window entry lies in the ball on which `Yinv` inverts. -/
theorem windowChain_snd_mem_ball
    (hYim : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → (germC a h w).2 ∈ Metric.ball (0 : ℂ) ρY)
    (hβcurve : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
      ∃ w, w ∈ Metric.ball (0 : ℂ) ρY ∧ w ≠ 0 ∧ ugermC a h w = β t 0)
    {t : ℂ} (ht : t ∈ Metric.ball (0 : ℂ) ρ \ {0}) :
    (β t 0).2 ∈ Metric.ball (0 : ℂ) ρY := by
  obtain ⟨w, hw, -, hwcurve⟩ := hβcurve t ht
  have hsnd : (β t 0).2 = (germC a h w).2 := by
    have hh := congrArg Prod.snd hwcurve
    simpa [ugermC, eqMirror] using hh.symm
  rw [hsnd]
  exact hYim w hw

/-! ## Analyticity on the punctured disc -/

/-- `ψ₂` is analytic on the punctured disc. -/
theorem windowChain_analyticOnNhd_psi2
    (hYan : AnalyticOnNhd ℂ Yinv (Metric.ball (0 : ℂ) ρY))
    (hβan : AnalyticOnNhd ℂ (fun t => β t (0 : Fin (n₁ + m₁ + 1)))
      (Metric.ball (0 : ℂ) ρ \ {0}))
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((germC a h w).2) = w)
    (hYim : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → (germC a h w).2 ∈ Metric.ball (0 : ℂ) ρY)
    (hβcurve : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
      ∃ w, w ∈ Metric.ball (0 : ℂ) ρY ∧ w ≠ 0 ∧ ugermC a h w = β t 0) :
    AnalyticOnNhd ℂ (psi2 a Yinv β) (Metric.ball (0 : ℂ) ρ \ {0}) := by
  intro t ht
  have hmem : (β t 0).2 ∈ Metric.ball (0 : ℂ) ρY :=
    windowChain_snd_mem_ball hYim hβcurve ht
  have hsnd : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) (β t 0) :=
    (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (β t 0)
  have h1 : AnalyticAt ℂ (fun s => (β s 0).2) t :=
    AnalyticAt.comp (f := fun s => β s (0 : Fin (n₁ + m₁ + 1))) hsnd (hβan t ht)
  have h2 : AnalyticAt ℂ (fun s => Yinv ((β s 0).2)) t :=
    AnalyticAt.comp (f := fun s => (β s 0).2) (hYan _ hmem) h1
  exact h2.div_const

/-- `t ↦ λ^{-n} ψ₂ t` is analytic on the punctured disc. -/
theorem windowChain_analyticOnNhd_zpow_mul_psi2 (n : ℤ)
    (hYan : AnalyticOnNhd ℂ Yinv (Metric.ball (0 : ℂ) ρY))
    (hβan : AnalyticOnNhd ℂ (fun t => β t (0 : Fin (n₁ + m₁ + 1)))
      (Metric.ball (0 : ℂ) ρ \ {0}))
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((germC a h w).2) = w)
    (hYim : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → (germC a h w).2 ∈ Metric.ball (0 : ℂ) ρY)
    (hβcurve : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
      ∃ w, w ∈ Metric.ball (0 : ℂ) ρY ∧ w ≠ 0 ∧ ugermC a h w = β t 0) :
    AnalyticOnNhd ℂ (fun t => ((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t)
      (Metric.ball (0 : ℂ) ρ \ {0}) :=
  fun t ht =>
    (analyticAt_const.mul (windowChain_analyticOnNhd_psi2 hYan hβan hY3 hYim hβcurve t ht))

/-! ## Norm bounds for the arguments of `germC` -/

/-- The arithmetic identity behind the bound on the backward arguments. -/
theorem zpow_mul_div_eq (c w : ℂ) (hc : c ≠ 0) (n m : ℤ) :
    c ^ (-n) * (w / c ^ m) = c ^ (-n - m) * w := by
  rw [div_eq_mul_inv, (zpow_neg c m).symm, mul_comm w (c ^ (-m)), ← mul_assoc, ← zpow_add₀ hc,
    show -n + -m = -n - m by ring]

/-- The witness gives the identity `λ^{-n} ψ₂ t = λ^{-n-m₁} w`, hence the bound. -/
theorem windowChain_norm_zpow_mul_psi2_lt (ha0 : 0 < a) (ha1 : a < 1)
    (hlam : ((eqLam a : ℝ) : ℂ) ≠ 0)
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((germC a h w).2) = w)
    (hβcurve : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
      ∃ w, w ∈ Metric.ball (0 : ℂ) ρY ∧ w ≠ 0 ∧ ugermC a h w = β t 0)
    {n : ℤ} (hn : n < -((m₁ : ℤ))) {t : ℂ} (ht : t ∈ Metric.ball (0 : ℂ) ρ \ {0}) :
    ‖((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t‖ < ρY := by
  obtain ⟨w, hw, -, hmul, -, -⟩ := windowChain_psi2_witness hlam hY3 hβcurve ht
  have hwlt : ‖w‖ < ρY := by simpa [Metric.mem_ball, dist_zero_right] using hw
  have hψ : psi2 a Yinv β t = w / ((eqLam a : ℝ) : ℂ) ^ m₁ := by
    rw [← hmul, eq_comm, div_eq_iff (pow_ne_zero _ hlam), mul_comm]
  have hexp : 0 ≤ -n - ((m₁ : ℕ) : ℤ) := by omega
  rw [hψ, show ((eqLam a : ℝ) : ℂ) ^ m₁ = ((eqLam a : ℝ) : ℂ) ^ ((m₁ : ℕ) : ℤ) by
        simp, zpow_mul_div_eq _ _ hlam, norm_mul, norm_zpow, win_norm_eqLamC ha0 ha1]
  calc eqLam a ^ (-n - ((m₁ : ℕ) : ℤ)) * ‖w‖
      ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right
        (win_eqLam_zpow_le_one ha0 ha1 hexp) (norm_nonneg w)
    _ = ‖w‖ := one_mul _
    _ < ρY := hwlt

/-- The backward arguments of `germC` stay in its ball of analyticity. -/
theorem windowChain_mem_ball_zpow_mul_psi2 (ha0 : 0 < a) (ha1 : a < 1)
    (hlam : ((eqLam a : ℝ) : ℂ) ≠ 0)
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((germC a h w).2) = w)
    (hβcurve : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
      ∃ w, w ∈ Metric.ball (0 : ℂ) ρY ∧ w ≠ 0 ∧ ugermC a h w = β t 0)
    (hρYg : ρY ≤ ρg) {n : ℤ} (hn : n < -((m₁ : ℤ)))
    {t : ℂ} (ht : t ∈ Metric.ball (0 : ℂ) ρ \ {0}) :
    ((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t ∈ Metric.ball (0 : ℂ) ρg := by
  rw [Metric.mem_ball, dist_zero_right]
  exact lt_of_lt_of_le (windowChain_norm_zpow_mul_psi2_lt ha0 ha1 hlam hY3 hβcurve hn ht) hρYg

/-- The backward entries are analytic on the punctured disc. -/
theorem windowChain_analyticOnNhd_ugermC_zpow_mul_psi2 (n : ℤ)
    (ha0 : 0 < a) (ha1 : a < 1) (hlam : ((eqLam a : ℝ) : ℂ) ≠ 0)
    (hYan : AnalyticOnNhd ℂ Yinv (Metric.ball (0 : ℂ) ρY))
    (hβan : AnalyticOnNhd ℂ (fun t => β t (0 : Fin (n₁ + m₁ + 1)))
      (Metric.ball (0 : ℂ) ρ \ {0}))
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((germC a h w).2) = w)
    (hYim : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → (germC a h w).2 ∈ Metric.ball (0 : ℂ) ρY)
    (hβcurve : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
      ∃ w, w ∈ Metric.ball (0 : ℂ) ρY ∧ w ≠ 0 ∧ ugermC a h w = β t 0)
    (hρYg : ρY ≤ ρg) (hgerm_an : AnalyticOnNhd ℂ (germC a h) (Metric.ball (0 : ℂ) ρg))
    (hn : n < -((m₁ : ℤ))) :
    AnalyticOnNhd ℂ (fun t => ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t))
      (Metric.ball (0 : ℂ) ρ \ {0}) := by
  intro t ht
  have hmem : ((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t ∈ Metric.ball (0 : ℂ) ρg :=
    windowChain_mem_ball_zpow_mul_psi2 ha0 ha1 hlam hY3 hβcurve hρYg hn ht
  have h1 : AnalyticAt ℂ (fun s => ((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β s) t :=
    windowChain_analyticOnNhd_zpow_mul_psi2 n hYan hβan hY3 hYim hβcurve t ht
  have h2 : AnalyticAt ℂ
      (fun s => germC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β s)) t :=
    AnalyticAt.comp (f := fun s => ((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β s)
      (g := germC a h) (hgerm_an _ hmem) h1
  have h3 : AnalyticAt ℂ
      (fun s => -((germC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β s)).1)) t :=
    (((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _).comp h2).neg
  have h4 : AnalyticAt ℂ
      (fun s => (germC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β s)).2) t :=
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _).comp h2
  simpa only [ugermC, eqMirror] using h3.prod h4

/-- The forward arguments of `germC` stay in its ball of analyticity. -/
theorem norm_zpow_mul_germ_arg_lt (ha0 : 0 < a) (ha1 : a < 1)
    (hsmall : ∀ t, 0 < ‖t‖ → ‖t‖ < ρ →
      ‖((eqLam a : ℝ) : ℂ) ^ n₁ * (u + κ * t ^ k)‖ < ρg)
    {n : ℤ} (hn : ((n₁ : ℕ) : ℤ) ≤ n) {t : ℂ}
    (ht : t ∈ Metric.ball (0 : ℂ) ρ \ {0}) :
    ‖((eqLam a : ℝ) : ℂ) ^ n * (u + κ * t ^ k)‖ < ρg := by
  have ht1 : ‖t‖ < ρ := by
    have := ht.1
    rwa [Metric.mem_ball, dist_zero_right] at this
  have ht2 : 0 < ‖t‖ := norm_pos_iff.mpr ht.2
  have hfac : ((eqLam a : ℝ) : ℂ) ^ n =
      ((eqLam a : ℝ) : ℂ) ^ (n - ((n₁ : ℕ) : ℤ)) * ((eqLam a : ℝ) : ℂ) ^ n₁ := by
    rw [show ((eqLam a : ℝ) : ℂ) ^ n₁ = ((eqLam a : ℝ) : ℂ) ^ ((n₁ : ℕ) : ℤ) by simp,
      ← zpow_add₀ (win_eqLamC_ne_zero ha0 ha1)]
    congr 1
    ring
  have hexp : 0 ≤ n - ((n₁ : ℕ) : ℤ) := by omega
  rw [hfac, mul_assoc, norm_mul, norm_zpow, win_norm_eqLamC ha0 ha1]
  calc eqLam a ^ (n - ((n₁ : ℕ) : ℤ)) *
        ‖((eqLam a : ℝ) : ℂ) ^ n₁ * (u + κ * t ^ k)‖
      ≤ 1 * ‖((eqLam a : ℝ) : ℂ) ^ n₁ * (u + κ * t ^ k)‖ :=
        mul_le_mul_of_nonneg_right (win_eqLam_zpow_le_one ha0 ha1 hexp)
          (norm_nonneg _)
    _ = ‖((eqLam a : ℝ) : ℂ) ^ n₁ * (u + κ * t ^ k)‖ := one_mul _
    _ < ρg := hsmall t ht2 ht1

/-- The forward entries are analytic on the punctured disc. -/
theorem windowChain_analyticOnNhd_germC_fwd (ha0 : 0 < a) (ha1 : a < 1)
    (hsmall : ∀ t, 0 < ‖t‖ → ‖t‖ < ρ →
      ‖((eqLam a : ℝ) : ℂ) ^ n₁ * (u + κ * t ^ k)‖ < ρg)
    (hgerm_an : AnalyticOnNhd ℂ (germC a h) (Metric.ball (0 : ℂ) ρg))
    {n : ℤ} (hn : ((n₁ : ℕ) : ℤ) ≤ n) :
    AnalyticOnNhd ℂ (fun t => germC a h (((eqLam a : ℝ) : ℂ) ^ n * (u + κ * t ^ k)))
      (Metric.ball (0 : ℂ) ρ \ {0}) := by
  intro t ht
  refine AnalyticAt.comp (f := fun s => ((eqLam a : ℝ) : ℂ) ^ n * (u + κ * s ^ k))
    (g := germC a h) (hgerm_an _ ?_) (by fun_prop)
  rw [Metric.mem_ball, dist_zero_right]
  exact norm_zpow_mul_germ_arg_lt ha0 ha1 hsmall hn ht

end

end Work.EQ
