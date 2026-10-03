import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.pert2v2.steps

namespace Work.Pert.pert2v2.GatePreimageReBound

open Filter
open scoped Topology

/-- Purely real threshold lemma: a linear factor times a decaying exponential is eventually `≤ 1`. -/
theorem exists_linear_mul_exp_neg_le (M κ c : ℝ) (hM : 0 < M) (hκ : 0 < κ) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → (t + c) * M * Real.exp (-(κ * t)) ≤ 1 := by
  have hmain : Tendsto (fun t : ℝ => t * Real.exp (-(κ * t))) atTop (𝓝 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) κ hκ
    simpa [Real.rpow_one] using h
  have h2 : Tendsto (fun t : ℝ => 2 * M * (t * Real.exp (-(κ * t)))) atTop (𝓝 0) := by
    have h := hmain.const_mul (2 * M)
    simpa using h
  have h3 : ∀ᶠ t : ℝ in atTop, 2 * M * (t * Real.exp (-(κ * t))) < 1 :=
    h2.eventually_lt_const (by norm_num)
  obtain ⟨T0, hT0⟩ := Filter.eventually_atTop.mp h3
  refine ⟨max T0 (|c| + 1), fun t ht => ?_⟩
  have ht0 : T0 ≤ t := le_trans (le_max_left _ _) ht
  have htc : |c| + 1 ≤ t := le_trans (le_max_right _ _) ht
  have hct : t + c ≤ 2 * t := by
    have h1 : c ≤ |c| := le_abs_self c
    have h2 : (0 : ℝ) < t := by linarith [abs_nonneg c]
    linarith
  have hpos : (0 : ℝ) ≤ M * Real.exp (-(κ * t)) := by positivity
  calc (t + c) * M * Real.exp (-(κ * t))
      = (t + c) * (M * Real.exp (-(κ * t))) := by ring
    _ ≤ (2 * t) * (M * Real.exp (-(κ * t))) := mul_le_mul_of_nonneg_right hct hpos
    _ = 2 * M * (t * Real.exp (-(κ * t))) := by ring
    _ ≤ 1 := le_of_lt (hT0 t ht0)

-- Backward walk in the lower gate: from a point `z` of `Qm Ξ α` with `1 ≤ z.re` and `z.im` large,
-- repeatedly take the `F`-preimage (`F w = z`, `w ≈ z - 1`, available from `Work.Pert.pert2v2.backStep_exists`
-- because the left margin `margA_g` of the gate stays > 1 + 1/4 at large height), until the real part
-- drops into `[-1,0]`.  The displacement error of each step is the *actual* defect
-- `F w - w - 1`, which is exponentially small, so the accumulated error is summable, and the walk
-- preserves `Φ` up to the exact level shift `- N`.
theorem walk_bwd_re {Ξ : ℝ} {α : ℂ} {F Φ : ℂ → ℂ} {M κ Ydec : ℝ}
    (hNT : MandelDim.NearTranslationOn F (Work.Pert.Qm Ξ α))
    (habel : ∀ w ∈ Work.Pert.Qm Ξ α, F w ∈ Work.Pert.Qm Ξ α → Φ (F w) = Φ w + 1)
    (hdec : ∀ w ∈ Work.Pert.Qm Ξ α, Ydec < w.im →
      ‖F w - (w + 1)‖ ≤ M * Real.exp (-(κ * w.im)))
    (hM : 0 < M) (hκ : 0 < κ) :
    ∃ K : ℝ, ∀ z : ℂ, z ∈ Work.Pert.Qm Ξ α → 1 ≤ z.re → K ≤ z.im →
      ∃ z' : ℂ, z' ∈ Work.Pert.Qm Ξ α ∧ ∃ N : ℕ, Φ z' = Φ z - (N : ℂ) ∧
        z'.re ∈ Set.Icc (-2 : ℝ) 2 ∧ z.im - 1 ≤ z'.im ∧
        ‖(Φ z' - z') - (Φ z - z)‖ ≤ 1 := by
  obtain ⟨Texp, hTexp⟩ :=
    exists_linear_mul_exp_neg_le (M * Real.exp (3 * κ)) κ |Ξ| (by positivity) hκ
  classical
  let B : ℝ := Ξ + |(1 / α).im| - (1 / α).re + 13 / 4
  let K : ℝ := max (max (Ydec + 4) B) (max Texp 1)
  refine ⟨K, ?_⟩
  intro z hzQ hzre hzim
  have hKYdec : Ydec + 4 ≤ z.im := le_trans (by simp [K, B]) hzim
  have hKB : Ξ + |(1 / α).im| - (1 / α).re + 13 / 4 ≤ z.im :=
    le_trans (by simp [K, B]) hzim
  have hKTexp : Texp ≤ z.im := le_trans (by simp [K, B]) hzim
  have hK1 : 1 ≤ z.im := le_trans (by simp [K, B]) hzim
  have hzre0 : (0 : ℝ) ≤ z.re := by linarith
  let N : ℕ := Nat.floor z.re
  have hNle : (N : ℝ) ≤ z.re := by
    have h := Nat.floor_le (R := ℝ) hzre0
    simpa [N] using h
  have hNlt : z.re < (N : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one (R := ℝ) z.re
    simpa [N] using h
  let Γ : ℝ := z.im - 3
  let tiny : ℝ := M * Real.exp (-(κ * Γ))
  have htinypos : 0 < tiny := by
    simp only [tiny]
    exact mul_pos hM (Real.exp_pos _)
  -- The exponential bookkeeping: `N * tiny ≤ 1`.
  have hNz : (N : ℝ) < z.im + |Ξ| := by
    have hQ2 : z.re < |z.im| - Ξ := (Qm_mem_iff.mp hzQ).2
    have hzimp : 0 < z.im := lt_of_lt_of_le zero_lt_one hK1
    rw [abs_of_pos hzimp] at hQ2
    have habs : -Ξ ≤ |Ξ| := neg_le_abs Ξ
    linarith
  have hNbound : (N : ℝ) * tiny ≤ 1 := by
    have hexp : Real.exp (-(κ * Γ)) = Real.exp (3 * κ) * Real.exp (-(κ * z.im)) := by
      simp only [Γ, ← Real.exp_add]
      congr 1
      ring
    have h1 : (N : ℝ) * tiny
        ≤ (z.im + |Ξ|) * (M * Real.exp (3 * κ)) * Real.exp (-(κ * z.im)) := by
      have hT' : (0 : ℝ) ≤ Real.exp (-(κ * z.im)) := (Real.exp_pos _).le
      have hM' : (0 : ℝ) ≤ M * Real.exp (3 * κ) := by positivity
      have hle := mul_le_mul_of_nonneg_right hNz.le hM'
      calc (N : ℝ) * tiny
          = (N : ℝ) * (M * Real.exp (3 * κ)) * Real.exp (-(κ * z.im)) := by
            simp only [tiny, hexp]; ring
        _ ≤ (z.im + |Ξ|) * (M * Real.exp (3 * κ)) * Real.exp (-(κ * z.im)) :=
            mul_le_mul_of_nonneg_right hle hT'
    exact le_trans h1 (hTexp z.im hKTexp)
  -- The backward-walk step and the walk itself.
  have hNT' : DifferentiableOn ℂ F (Work.Pert.Qm Ξ α) ∧
      (∀ z ∈ Work.Pert.Qm Ξ α, ‖F z - (z + 1)‖ ≤ 1 / 32 ∧
        ‖deriv F z - 1‖ ≤ 1 / 32) := hNT
  let nxt : ℂ → ℂ := fun w =>
    if hw : w ∈ Work.Pert.Qm Ξ α ∧ (1 + 1 / 4 : ℝ) ≤ Work.Pert.margA_g Ξ α w then
      Classical.choose (backStep_exists (Ξ := Ξ) (α := α) (F := F) (Φ := Φ) hNT'.1
        (fun x hx => hNT'.2 x hx) hw.1 hw.2 habel)
    else w
  have hnxt : ∀ w ∈ Work.Pert.Qm Ξ α, (1 + 1 / 4 : ℝ) ≤ Work.Pert.margA_g Ξ α w →
      nxt w ∈ Work.Pert.Qm Ξ α ∧ F (nxt w) = w ∧ Φ (nxt w) = Φ w - 1 ∧
        ‖nxt w - (w - 1)‖ ≤ 1 / 32 := by
    intro w hwQ hwr
    have hch : nxt w = Classical.choose (backStep_exists (Ξ := Ξ) (α := α) (F := F) (Φ := Φ)
        hNT'.1 (fun x hx => hNT'.2 x hx) hwQ hwr habel) := by
      simp only [nxt]
      rw [dite_eq_left ⟨hwQ, hwr⟩]
    rw [hch]
    obtain ⟨h1, h2, h3, h4⟩ :=
      Classical.choose_spec (backStep_exists (Ξ := Ξ) (α := α) (F := F) (Φ := Φ)
        hNT'.1 (fun x hx => hNT'.2 x hx) hwQ hwr habel)
    exact ⟨h3, h2, h4, h1⟩
  let W : ℕ → ℂ := fun k => nxt^[k] z
  have hWzero : W 0 = z := by simp [W]
  have hWsucc : ∀ k : ℕ, W (k + 1) = nxt (W k) := by
    intro k
    show nxt^[Nat.succ k] z = nxt (nxt^[k] z)
    rw [Function.iterate_succ_apply']
  -- The walk: `N` backward steps.
  have hmain : ∀ k : ℕ, k ≤ N → W k ∈ Work.Pert.Qm Ξ α ∧ Φ (W k) = Φ z - (k : ℂ) ∧
      ‖W k - (z - (k : ℂ))‖ ≤ (k : ℝ) * tiny ∧ z.im - 1 ≤ (W k).im := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨hzQ, by simp [hWzero], by simp [hWzero], by simp [hWzero]⟩
    | succ k ih =>
      intro hk
      have hkN : k ≤ N := by omega
      obtain ⟨hQk, hΦk, hdevk, himk⟩ := ih hkN
      -- real part of `W k` is bounded below
      have hWkre : -1 ≤ (W k).re := by
        have h1 : |((W k) - (z - (k : ℂ))).re| ≤ (k : ℝ) * tiny :=
          le_trans (Complex.abs_re_le_norm _) hdevk
        have h2 : ((W k) - (z - (k : ℂ))).re = (W k).re - z.re + (k : ℝ) := by
          simp only [Complex.sub_re, Complex.natCast_re]
          ring
        have h3 : (k : ℝ) * tiny ≤ (N : ℝ) * tiny :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hkN) htinypos.le
        have hkN' : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
        linarith [(abs_le.mp h1).1, h3, hNbound, hNle, hkN']
      -- the margin condition at `W k`
      have hmarg : (1 + 1 / 4 : ℝ) ≤ Work.Pert.margA_g Ξ α (W k) := by
        have himnn : 0 ≤ (W k).im := by linarith
        have habs : |(W k).im| = (W k).im := abs_of_nonneg himnn
        have h1 : |(W k).im| - |(1 / α).im| ≤ |(W k).im + (1 / α).im| := by
          have h := abs_sub_abs_le_abs_sub ((W k).im) (-((1 / α).im))
          simpa [abs_neg, sub_neg_eq_add] using h
        rw [Work.Pert.margA_g]
        linarith [h1, habs, hKB]
      obtain ⟨hQ1, hF1, hΦ1, hd1⟩ := hnxt (W k) hQk hmarg
      have hQ1' : W (k + 1) ∈ Work.Pert.Qm Ξ α := by rw [hWsucc]; exact hQ1
      have hF1' : F (W (k + 1)) = W k := by rw [hWsucc]; exact hF1
      have hΦ1' : Φ (W (k + 1)) = Φ (W k) - 1 := by rw [hWsucc]; exact hΦ1
      have hd1' : ‖W (k + 1) - (W k - 1)‖ ≤ 1 / 32 := by rw [hWsucc]; exact hd1
      -- height of `W (k+1)`
      have him1 : z.im - 2 - 1 / 32 ≤ (W (k + 1)).im := by
        have h1 : |(W (k + 1) - (W k - 1)).im| ≤ 1 / 32 :=
          le_trans (Complex.abs_im_le_norm _) hd1'
        have h2 : (W (k + 1) - (W k - 1)).im = (W (k + 1)).im - (W k).im := by
          rw [show W (k + 1) - (W k - 1) = (W (k + 1) - W k) + 1 by ring]
          simp
        linarith [(abs_le.mp h1).1, h2, himk]
      have hYdec1 : Ydec < (W (k + 1)).im := by linarith
      have hΓ1 : Γ ≤ (W (k + 1)).im := by simp only [Γ]; linarith
      -- the actual defect at the preimage is exponentially small
      have hη : ‖F (W (k + 1)) - ((W (k + 1)) + 1)‖ ≤ tiny := by
        have h := hdec (W (k + 1)) hQ1' hYdec1
        have hexp : Real.exp (-(κ * (W (k + 1)).im)) ≤ Real.exp (-(κ * Γ)) :=
          Real.exp_le_exp.mpr (by nlinarith [hΓ1, hκ])
        calc ‖F (W (k + 1)) - ((W (k + 1)) + 1)‖
            ≤ M * Real.exp (-(κ * (W (k + 1)).im)) := h
          _ ≤ M * Real.exp (-(κ * Γ)) := mul_le_mul_of_nonneg_left hexp hM.le
          _ = tiny := by simp only [tiny]
      -- the accumulated displacement
      have hdisp : ‖W (k + 1) - (z - ((k + 1 : ℕ) : ℂ))‖ ≤ ((k + 1 : ℕ) : ℝ) * tiny := by
        have heq : W (k + 1) - (z - ((k + 1 : ℕ) : ℂ)) =
            (W k - (z - (k : ℂ))) - (F (W (k + 1)) - ((W (k + 1)) + 1)) := by
          rw [hF1']; push_cast; ring
        rw [heq]
        calc ‖(W k - (z - (k : ℂ))) - (F (W (k + 1)) - ((W (k + 1)) + 1))‖
            ≤ ‖W k - (z - (k : ℂ))‖ + ‖F (W (k + 1)) - ((W (k + 1)) + 1)‖ := norm_sub_le _ _
          _ ≤ (k : ℝ) * tiny + tiny := add_le_add hdevk hη
          _ = ((k + 1 : ℕ) : ℝ) * tiny := by push_cast; ring
      have hΦok : Φ (W (k + 1)) = Φ z - ((k + 1 : ℕ) : ℂ) := by
        rw [hΦ1', hΦk]; push_cast; ring
      have himok : z.im - 1 ≤ (W (k + 1)).im := by
        have h1 : |(W (k + 1) - (z - ((k + 1 : ℕ) : ℂ))).im| ≤ ((k + 1 : ℕ) : ℝ) * tiny :=
          le_trans (Complex.abs_im_le_norm _) hdisp
        have h2 : (W (k + 1) - (z - ((k + 1 : ℕ) : ℂ))).im = (W (k + 1)).im - z.im := by
          simp only [Complex.sub_im, Complex.natCast_im, sub_zero]
        have h3 : ((k + 1 : ℕ) : ℝ) * tiny ≤ (N : ℝ) * tiny :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hk) htinypos.le
        linarith [(abs_le.mp h1).1, h3, hNbound]
      exact ⟨hQ1', hΦok, hdisp, himok⟩
  obtain ⟨hQN, hΦN, hdevN, himN⟩ := hmain N le_rfl
  refine ⟨W N, hQN, N, hΦN, ⟨?_, ?_⟩, himN, ?_⟩
  · have h1 : |((W N) - (z - (N : ℂ))).re| ≤ (N : ℝ) * tiny :=
      le_trans (Complex.abs_re_le_norm _) hdevN
    have h2 : ((W N) - (z - (N : ℂ))).re = (W N).re - z.re + (N : ℝ) := by
      simp only [Complex.sub_re, Complex.natCast_re]
      ring
    linarith [(abs_le.mp h1).1, hNbound, hNle]
  · have h1 : |((W N) - (z - (N : ℂ))).re| ≤ (N : ℝ) * tiny :=
      le_trans (Complex.abs_re_le_norm _) hdevN
    have h2 : ((W N) - (z - (N : ℂ))).re = (W N).re - z.re + (N : ℝ) := by
      simp only [Complex.sub_re, Complex.natCast_re]
      ring
    linarith [(abs_le.mp h1).2, hNbound, hNlt]
  · have heq : (Φ (W N) - W N) - (Φ z - z) = -(W N - (z - (N : ℂ))) := by
      rw [hΦN]; ring
    rw [heq, norm_neg]
    exact le_trans hdevN hNbound

end Work.Pert.pert2v2.GatePreimageReBound
