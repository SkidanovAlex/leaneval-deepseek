import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.poisson_bound

/-!
# `patching`: the patching argument of AJ §9 (Ten Martini Problem)

`Main/expLocAEpos_of_regFamily` feeds this lemma: a formal solution `u` of `H u = E u` with
polynomial growth, together with a multiscale regularity family (every site `y > b` is
`(L₁, ≥ q)`-regular in the sense of `IsRegularBig`) satisfying the counting condition
`200 L₁ + 200 log 2 < L₁ q`, decays exponentially at rate `4 L₁ / 5` to the right.

The proof is the block-resolvent expansion of AJ §9.1.  Starting from a large site `k` one
expands `u` through the Poisson formula `u y = -G(y,x₁) u(x₁-1) - G(y,x₂) u(x₂+1)`; after
`N ≈ 40k/q` steps the accumulated Green decay is `e^{-L₁ Q N}` with `Q = q/40`, while the
number of branches is `2^N`, giving the rate `L₁ - 40 log 2/q > 4L₁/5`, exactly as the
counting condition guarantees.  The bookkeeping is done with the explicit upper bound
`sbn` and a two-part ansatz (`sbn`'s `T`-term for the depth-`N` frontier, `halfB`'s second
term for the branches that have reached the "cheap" region `≤ max b 0`).
-/

namespace Work.TMC16Core.Basic

open Work.TMC16Core

noncomputable section

/-! ## Generic one-variable estimates -/

private lemma one_add_le_exp (x : ℝ) : 1 + x ≤ Real.exp x := by
  linarith [Real.add_one_le_exp x]

/-- The exponential decay of `x ↦ e^{-L x} (x+1)` is nonincreasing on `[Q,∞)` as soon as
`L (Q+1) ≥ 1`. -/
theorem exp_neg_mul_le_of_mem_Ici {L Q d : ℝ} (hL : 0 < L) (hQ : 0 < Q)
    (h1 : 1 ≤ L * (Q + 1)) (hd : Q ≤ d) :
    Real.exp (-(L * d)) * (d + 1) ≤ Real.exp (-(L * Q)) * (Q + 1) := by
  have hQd : 0 ≤ d - Q := by linarith
  have h2 : d - Q ≤ (Q + 1) * L * (d - Q) := by
    have := mul_le_mul_of_nonneg_right h1 hQd
    linarith
  have h3 : d + 1 ≤ (Q + 1) * (1 + L * (d - Q)) := by nlinarith
  have h4 : (Q + 1) * (1 + L * (d - Q)) ≤ (Q + 1) * Real.exp (L * (d - Q)) :=
    mul_le_mul_of_nonneg_left (one_add_le_exp _) (by linarith [hL, hQ])
  have hmain : d + 1 ≤ (Q + 1) * Real.exp (L * (d - Q)) := le_trans h3 h4
  have hexp : Real.exp (-(L * d)) * Real.exp (L * (d - Q)) = Real.exp (-(L * Q)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.exp (-(L * d)) * (d + 1)
      ≤ Real.exp (-(L * d)) * ((Q + 1) * Real.exp (L * (d - Q))) :=
        mul_le_mul_of_nonneg_left hmain (Real.exp_nonneg _)
    _ = Real.exp (-(L * Q)) * (Q + 1) := by
        rw [show Real.exp (-(L * d)) * ((Q + 1) * Real.exp (L * (d - Q)))
              = (Q + 1) * (Real.exp (-(L * d)) * Real.exp (L * (d - Q))) by ring, hexp]
        ring

/-- The polynomial weight `1+|x|` is dominated by the exponential `e^{-L₁ x}` on `(-∞,B]`. -/
theorem one_add_abs_le_M1 {L₁ B : ℝ} (hL₁ : 0 < L₁) :
    ∀ x : ℝ, x ≤ B →
      1 + |x| ≤ (Real.exp (L₁ * B) * (1 + |B| + 2 / L₁)) * Real.exp (-(L₁ * x)) := by
  intro x hx
  set s : ℝ := B - x with hs
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hxe : x = B - s := by rw [hs]; ring
  have hxabs : |x| ≤ |B| + s := by
    rw [hxe]
    calc |B - s| ≤ |B| + |s| := abs_sub _ _
      _ = |B| + s := by rw [abs_of_nonneg hs0]
  have hxexp : Real.exp (-(L₁ * x)) = Real.exp (L₁ * s) * Real.exp (-(L₁ * B)) := by
    rw [hxe, ← Real.exp_add]; congr 1; ring
  have hM : 0 ≤ 1 + |B| + 2 / L₁ := by positivity
  have hkey : 1 + |x| ≤ (1 + |B| + 2 / L₁) * Real.exp (L₁ * s) := by
    have hL1 : 1 ≤ (1 + |B| + 2 / L₁) * L₁ := by
      have hE : (1 + |B| + 2 / L₁) * L₁ = L₁ * (1 + |B|) + 2 := by
        field_simp
      rw [hE]
      have : 0 ≤ L₁ * (1 + |B|) := mul_nonneg (le_of_lt hL₁) (by positivity)
      linarith
    have hsle : s ≤ (1 + |B| + 2 / L₁) * (L₁ * s) := by
      have := mul_le_mul_of_nonneg_right hL1 hs0
      nlinarith
    have h1 : 1 + |B| + s ≤ (1 + |B| + 2 / L₁) * (1 + L₁ * s) := by
      have h2L : 0 < 2 / L₁ := by positivity
      have hE : (1 + |B| + 2 / L₁) * (1 + L₁ * s)
          = (1 + |B| + 2 / L₁) + (1 + |B| + 2 / L₁) * (L₁ * s) := by ring
      rw [hE]; linarith
    have h2 : (1 + |B| + 2 / L₁) * (1 + L₁ * s) ≤ (1 + |B| + 2 / L₁) * Real.exp (L₁ * s) :=
      mul_le_mul_of_nonneg_left (one_add_le_exp _) hM
    linarith [hxabs]
  have hexpB : Real.exp (L₁ * B) * Real.exp (-(L₁ * B)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hgoal : Real.exp (L₁ * B) * (1 + |B| + 2 / L₁) * (Real.exp (L₁ * s) * Real.exp (-(L₁ * B)))
      = (1 + |B| + 2 / L₁) * Real.exp (L₁ * s) := by
    rw [show Real.exp (L₁ * B) * (1 + |B| + 2 / L₁) * (Real.exp (L₁ * s) * Real.exp (-(L₁ * B)))
          = (1 + |B| + 2 / L₁) * (Real.exp (L₁ * B) * Real.exp (-(L₁ * B))) * Real.exp (L₁ * s)
          by ring, hexpB, mul_one]
  rw [hxexp, hgoal]
  exact hkey

/-- Two affine-times-exponential terms tend to `0`; hence they are eventually `≤ 1`. -/
theorem exists_const_affine_exp {L₁ q P P' : ℝ} (hL₁ : 0 < L₁) (hq : 0 < q)
    (hcount : 200 * L₁ + 200 * Real.log 2 < L₁ * q) :
    ∃ K : ℝ, ∀ k : ℝ, K ≤ k →
      P * k * Real.exp (-((L₁ / 5 - 40 * Real.log 2 / q) * k))
        + P' * Real.exp (-((L₁ / 5 - 40 * (Real.log 2 + L₁) / q) * k)) ≤ 1 := by
  set a : ℝ := L₁ / 5 - 40 * Real.log 2 / q with ha
  set e : ℝ := L₁ / 5 - 40 * (Real.log 2 + L₁) / q with he
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLq : 200 * Real.log 2 < L₁ * q := by linarith [hcount, hL₁]
  have ha_pos : 0 < a := by
    rw [ha]
    have h5 : (0 : ℝ) < 5 := by norm_num
    have h : 40 * Real.log 2 / q < L₁ / 5 := by
      rw [div_lt_div_iff₀ hq h5]
      nlinarith [hLq]
    linarith
  have he_pos : 0 < e := by
    rw [he]
    have h5 : (0 : ℝ) < 5 := by norm_num
    have h : 40 * (Real.log 2 + L₁) / q < L₁ / 5 := by
      rw [div_lt_div_iff₀ hq h5]
      nlinarith [hcount]
    linarith
  have h1 : Filter.Tendsto (fun k : ℝ => P * (k * Real.exp (-(a * k)))) Filter.atTop (nhds 0) := by
    have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha_pos
    have h0' : Filter.Tendsto (fun k : ℝ => k * Real.exp (-(a * k))) Filter.atTop (nhds 0) := by
      simpa [Real.rpow_one] using h0
    simpa using h0'.const_mul P
  have h2 : Filter.Tendsto (fun k : ℝ => P' * Real.exp (-(e * k))) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun k : ℝ => Real.exp (-(e * k))) Filter.atTop (nhds 0) := by
      have h' : Filter.Tendsto (fun x : ℝ => (-e) * x) Filter.atTop Filter.atBot :=
        (Filter.tendsto_id).const_mul_atTop_of_neg (by linarith)
      exact Real.tendsto_exp_atBot.comp (by simpa [neg_mul] using h')
    simpa using h0.const_mul P'
  have hsum : Filter.Tendsto
      (fun k : ℝ => P * k * Real.exp (-(a * k)) + P' * Real.exp (-(e * k)))
      Filter.atTop (nhds 0) := by
    have := h1.add h2
    simpa [mul_assoc] using this
  have hev : ∀ᶠ k in Filter.atTop, P * k * Real.exp (-(a * k)) + P' * Real.exp (-(e * k)) ≤ 1 := by
    have h := hsum.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [h] with k hk using hk
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
  exact ⟨K, fun k hk => hK k hk⟩

/-! ## The block-resolvent bound `Bseq` -/

variable {α lam : ℝ} {θ : ℝ} {E : ℂ} {L₁ q b C : ℝ}

/-- The threshold above which the regularity family is available. -/
def thr (b : ℝ) : ℝ := max b 0

lemma thr_nonneg (b : ℝ) : 0 ≤ thr b := le_max_right b 0

lemma lt_thr_of_lt {b z : ℝ} (h : thr b < z) : b < z :=
  lt_of_le_of_lt (le_max_left b 0) h

/-- The witnessing interval of the regularity family at `z` (junk when `z ≤ thr b`). -/
noncomputable def iwin (hfam : ∀ y : ℤ, b < (y : ℝ) → IsRegularBig α lam θ E L₁ q y)
    (z : ℤ) : ℤ × ℤ :=
  if hz : thr b < (z : ℝ) then
    (Classical.choose (hfam z (lt_thr_of_lt hz)),
     Classical.choose (Classical.choose_spec (hfam z (lt_thr_of_lt hz))))
  else (z, z)

lemma iwin_spec (hfam : ∀ y : ℤ, b < (y : ℝ) → IsRegularBig α lam θ E L₁ q y)
    {z : ℤ} (hz : thr b < (z : ℝ)) :
    (iwin hfam z).1 ≤ z ∧ z ≤ (iwin hfam z).2 ∧
    q ≤ (((iwin hfam z).2 - (iwin hfam z).1 + 1 : ℤ) : ℝ) ∧
    (((iwin hfam z).2 - (iwin hfam z).1 + 1 : ℤ) : ℝ) ≤ 40 * (((z - (iwin hfam z).1 : ℤ)) : ℝ) ∧
    (((iwin hfam z).2 - (iwin hfam z).1 + 1 : ℤ) : ℝ) ≤ 40 * ((((iwin hfam z).2 - z : ℤ)) : ℝ) ∧
    (dirMat α lam (θ + ((iwin hfam z).1 : ℝ) * α) E
      (((iwin hfam z).2 - (iwin hfam z).1 + 1).toNat)).det ≠ 0 ∧
    ‖G α lam θ E (iwin hfam z).1 (iwin hfam z).2 z (iwin hfam z).1‖ <
      Real.exp (-(L₁ * (((z - (iwin hfam z).1 : ℤ)) : ℝ))) ∧
    ‖G α lam θ E (iwin hfam z).1 (iwin hfam z).2 z (iwin hfam z).2‖ <
      Real.exp (-(L₁ * ((((iwin hfam z).2 - z : ℤ)) : ℝ))) := by
  unfold iwin
  rw [dif_pos hz]
  exact Classical.choose_spec (Classical.choose_spec (hfam z (lt_thr_of_lt hz)))

/-- The explicit bound on `‖u z‖` obtained by expanding `n` levels of the tree. -/
noncomputable def Bseq (hfam : ∀ y : ℤ, b < (y : ℝ) → IsRegularBig α lam θ E L₁ q y)
    (C : ℝ) : ℕ → ℤ → ℝ
  | 0, z => C * (1 + |(z : ℝ)|)
  | (n + 1), z =>
      if hz : thr b < (z : ℝ) then
        ‖G α lam θ E (iwin hfam z).1 (iwin hfam z).2 z (iwin hfam z).1‖ *
            Bseq hfam C n ((iwin hfam z).1 - 1)
          + ‖G α lam θ E (iwin hfam z).1 (iwin hfam z).2 z (iwin hfam z).2‖ *
            Bseq hfam C n ((iwin hfam z).2 + 1)
      else C * (1 + |(z : ℝ)|)

lemma Bseq_zero (hfam : ∀ y : ℤ, b < (y : ℝ) → IsRegularBig α lam θ E L₁ q y) (C : ℝ)
    (z : ℤ) : Bseq hfam C 0 z = C * (1 + |(z : ℝ)|) := rfl

lemma Bseq_succ (hfam : ∀ y : ℤ, b < (y : ℝ) → IsRegularBig α lam θ E L₁ q y) (C : ℝ)
    (n : ℕ) (z : ℤ) :
    Bseq hfam C (n + 1) z =
      (if hz : thr b < (z : ℝ) then
        ‖G α lam θ E (iwin hfam z).1 (iwin hfam z).2 z (iwin hfam z).1‖ *
            Bseq hfam C n ((iwin hfam z).1 - 1)
          + ‖G α lam θ E (iwin hfam z).1 (iwin hfam z).2 z (iwin hfam z).2‖ *
            Bseq hfam C n ((iwin hfam z).2 + 1)
      else C * (1 + |(z : ℝ)|)) := rfl

lemma Bseq_of_le (hfam : ∀ y : ℤ, b < (y : ℝ) → IsRegularBig α lam θ E L₁ q y) (C : ℝ)
    {z : ℤ} (hz : (z : ℝ) ≤ thr b) (n : ℕ) :
    Bseq hfam C n z = C * (1 + |(z : ℝ)|) := by
  cases n with
  | zero => rw [Bseq_zero]
  | succ n => rw [Bseq_succ, dif_neg (not_lt.mpr hz)]

/-- The Poisson formula bounds `‖u z‖` by the recursion defining `Bseq`. -/
lemma le_Bseq (hfam : ∀ y : ℤ, b < (y : ℝ) → IsRegularBig α lam θ E L₁ q y) (C : ℝ)
    {u : ℤ → ℂ} (hsol : IsFormalSol α lam θ E u)
    (hpol : ∀ n : ℤ, ‖u n‖ ≤ C * (1 + |(n : ℝ)|)) :
    ∀ (n : ℕ) (z : ℤ), ‖u z‖ ≤ Bseq hfam C n z := by
  intro n
  induction n with
  | zero =>
    intro z
    rw [Bseq_zero]
    exact hpol z
  | succ n ih =>
    intro z
    by_cases hz : thr b < (z : ℝ)
    · rw [Bseq_succ, dif_pos hz]
      obtain ⟨h1, h2, hlen, h40a, h40b, hdet, hG1, hG2⟩ := iwin_spec (hfam := hfam) hz
      refine le_trans (poisson_bound hsol hdet h1 h2) (add_le_add ?_ ?_)
      · exact mul_le_mul_of_nonneg_left (ih _) (norm_nonneg _)
      · exact mul_le_mul_of_nonneg_left (ih _) (norm_nonneg _)
    · rw [Bseq_succ, dif_neg hz]
      exact hpol z

/-! ## The explicit ansatz `sbn` -/

/-- The two-part upper bound of the patching argument. -/
def sbn (L₁ Q C M₁ : ℝ) (n : ℕ) (z : ℤ) : ℝ :=
  (2 : ℝ) ^ n * (C * Real.exp (-(L₁ * Q * (n : ℝ))) * (1 + (z : ℝ) + (Q + 1) * (n : ℝ))
    + 2 * C * M₁ * Real.exp (L₁ * ((n : ℝ) - (z : ℝ))))

/-- Half of `sbn (n+1) z`: the budget for each of the two branches. -/
def halfB (L₁ Q C M₁ : ℝ) (n : ℕ) (z : ℤ) : ℝ :=
  (2 : ℝ) ^ n * C * Real.exp (-(L₁ * Q * (n : ℝ)))
      * (Real.exp (-(L₁ * Q)) * (1 + (z : ℝ) + (Q + 1) * (n : ℝ))
          + Real.exp (-(L₁ * Q)) * (Q + 1))
    + (2 : ℝ) ^ n * 2 * C * M₁ * Real.exp (L₁ * (n : ℝ))
        * Real.exp (-(L₁ * ((z : ℝ) - 1)))

lemma sbn_nonneg {Q M₁ : ℝ} (hCnn : 0 ≤ C) (hM1nn : 0 ≤ M₁) {n : ℕ} {z : ℤ}
    (hz : 0 ≤ (z : ℝ)) (hQ : 0 < Q) : 0 ≤ sbn L₁ Q C M₁ n z := by
  rw [sbn]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hQ1 : 0 ≤ Q + 1 := by linarith
  have hT : 0 ≤ 1 + (z : ℝ) + (Q + 1) * (n : ℝ) := by
    have : 0 ≤ (Q + 1) * (n : ℝ) := mul_nonneg hQ1 hn
    linarith
  refine mul_nonneg (by positivity) (add_nonneg ?_ ?_)
  · exact mul_nonneg (mul_nonneg hCnn (Real.exp_nonneg _)) hT
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hCnn) hM1nn)
      (Real.exp_nonneg _)

lemma sbn_succ {Q M₁ : ℝ} (n : ℕ) (z : ℤ) :
    sbn L₁ Q C M₁ (n + 1) z = 2 * halfB L₁ Q C M₁ n z := by
  have e1 : Real.exp (-(L₁ * Q * ((n : ℝ) + 1)))
      = Real.exp (-(L₁ * Q * (n : ℝ))) * Real.exp (-(L₁ * Q)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (L₁ * (((n : ℝ) + 1) - (z : ℝ)))
      = Real.exp (L₁ * (n : ℝ)) * Real.exp (-(L₁ * ((z : ℝ) - 1))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [sbn, halfB]
  push_cast
  rw [e1, e2, pow_succ]
  ring

/-- One branch of the expansion: the bound `halfB n z` for a single child. -/
lemma child_bound {Q M₁ : ℝ} (hLpos : 0 < L₁)
    (hfam : ∀ y : ℤ, b < (y : ℝ) → IsRegularBig α lam θ E L₁ q y)
    (hCnn : 0 ≤ C) (hQ : 0 < Q) (hM1nn : 0 ≤ M₁) (h1 : 1 ≤ L₁ * (Q + 1))
    (hM1 : ∀ x : ℝ, x ≤ thr b → 1 + |x| ≤ M₁ * Real.exp (-(L₁ * x)))
    {n : ℕ} {z c : ℤ} {d A : ℝ}
    (hz : thr b < (z : ℝ)) (hAnn : 0 ≤ A) (hA : A ≤ Real.exp (-(L₁ * d)))
    (hdQ : Q ≤ d)
    (hT : 1 + (c : ℝ) + (Q + 1) * (n : ℝ) ≤ (1 + (z : ℝ) + (Q + 1) * (n : ℝ)) + d + 1)
    (hsum : (z : ℝ) - 1 ≤ (c : ℝ) + d)
    (ih : ∀ z : ℤ, thr b < (z : ℝ) → Bseq hfam C n z ≤ sbn L₁ Q C M₁ n z) :
    A * Bseq hfam C n c ≤ halfB L₁ Q C M₁ n z := by
  have hznn : 0 ≤ (z : ℝ) := le_trans (thr_nonneg b) (le_of_lt hz)
  have hTznn : 0 ≤ 1 + (z : ℝ) + (Q + 1) * (n : ℝ) := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have : 0 ≤ (Q + 1) * (n : ℝ) := mul_nonneg (by linarith) hn
    linarith
  have hQ1 : 0 ≤ Q + 1 := by linarith
  have hterm1 : Real.exp (-(L₁ * d)) * (1 + (c : ℝ) + (Q + 1) * (n : ℝ))
      ≤ Real.exp (-(L₁ * Q)) * (1 + (z : ℝ) + (Q + 1) * (n : ℝ))
        + Real.exp (-(L₁ * Q)) * (Q + 1) := by
    have hA1 : Real.exp (-(L₁ * d)) * (1 + (c : ℝ) + (Q + 1) * (n : ℝ))
        ≤ Real.exp (-(L₁ * d)) * ((1 + (z : ℝ) + (Q + 1) * (n : ℝ)) + d + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg _)
    have hA2 : Real.exp (-(L₁ * d)) * ((1 + (z : ℝ) + (Q + 1) * (n : ℝ)) + d + 1)
        = Real.exp (-(L₁ * d)) * (1 + (z : ℝ) + (Q + 1) * (n : ℝ))
          + Real.exp (-(L₁ * d)) * (d + 1) := by ring
    have hA3 : Real.exp (-(L₁ * d)) * (1 + (z : ℝ) + (Q + 1) * (n : ℝ))
        ≤ Real.exp (-(L₁ * Q)) * (1 + (z : ℝ) + (Q + 1) * (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ hTznn
      apply Real.exp_le_exp.mpr
      nlinarith [hdQ, hLpos]
    have hA4 : Real.exp (-(L₁ * d)) * (d + 1) ≤ Real.exp (-(L₁ * Q)) * (Q + 1) :=
      exp_neg_mul_le_of_mem_Ici hLpos hQ h1 hdQ
    linarith [hA1, hA2, hA3, hA4]
  have hterm2 : Real.exp (-(L₁ * d)) * Real.exp (-(L₁ * (c : ℝ)))
      ≤ Real.exp (-(L₁ * ((z : ℝ) - 1))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hsum (le_of_lt hLpos)
    linarith
  by_cases hcz : thr b < (c : ℝ)
  · have hsbnnn : 0 ≤ sbn L₁ Q C M₁ n c :=
      sbn_nonneg hCnn hM1nn (le_trans (thr_nonneg b) (le_of_lt hcz)) hQ
    refine le_trans (le_trans (mul_le_mul_of_nonneg_left (ih c hcz) hAnn)
      (mul_le_mul_of_nonneg_right hA hsbnnn)) ?_
    rw [sbn, halfB]
    have eEnc : Real.exp (L₁ * ((n : ℝ) - (c : ℝ)))
        = Real.exp (L₁ * (n : ℝ)) * Real.exp (-(L₁ * (c : ℝ))) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexpand : Real.exp (-(L₁ * d))
          * ((2 : ℝ) ^ n * (C * Real.exp (-(L₁ * Q * (n : ℝ)))
                * (1 + (c : ℝ) + (Q + 1) * (n : ℝ))
              + 2 * C * M₁ * Real.exp (L₁ * ((n : ℝ) - (c : ℝ)))))
        = (2 : ℝ) ^ n * C * Real.exp (-(L₁ * Q * (n : ℝ)))
            * (Real.exp (-(L₁ * d)) * (1 + (c : ℝ) + (Q + 1) * (n : ℝ)))
          + (2 : ℝ) ^ n * 2 * C * M₁ * Real.exp (L₁ * (n : ℝ))
            * (Real.exp (-(L₁ * d)) * Real.exp (-(L₁ * (c : ℝ)))) := by
      rw [eEnc]; ring
    rw [hexpand]
    have hb1 : (2 : ℝ) ^ n * C * Real.exp (-(L₁ * Q * (n : ℝ)))
          * (Real.exp (-(L₁ * d)) * (1 + (c : ℝ) + (Q + 1) * (n : ℝ)))
        ≤ (2 : ℝ) ^ n * C * Real.exp (-(L₁ * Q * (n : ℝ)))
          * (Real.exp (-(L₁ * Q)) * (1 + (z : ℝ) + (Q + 1) * (n : ℝ))
              + Real.exp (-(L₁ * Q)) * (Q + 1)) :=
      mul_le_mul_of_nonneg_left hterm1 (by positivity)
    have hb2 : (2 : ℝ) ^ n * 2 * C * M₁ * Real.exp (L₁ * (n : ℝ))
          * (Real.exp (-(L₁ * d)) * Real.exp (-(L₁ * (c : ℝ))))
        ≤ (2 : ℝ) ^ n * 2 * C * M₁ * Real.exp (L₁ * (n : ℝ))
          * Real.exp (-(L₁ * ((z : ℝ) - 1))) :=
      mul_le_mul_of_nonneg_left hterm2 (by positivity)
    linarith [hb1, hb2]
  · have hcb : (c : ℝ) ≤ thr b := not_lt.mp hcz
    rw [Bseq_of_le hfam C hcb n, halfB]
    have hTpart : 0 ≤ (2 : ℝ) ^ n * C * Real.exp (-(L₁ * Q * (n : ℝ)))
        * (Real.exp (-(L₁ * Q)) * (1 + (z : ℝ) + (Q + 1) * (n : ℝ))
            + Real.exp (-(L₁ * Q)) * (Q + 1)) := by
      have hb : 0 ≤ Real.exp (-(L₁ * Q)) * (1 + (z : ℝ) + (Q + 1) * (n : ℝ))
          + Real.exp (-(L₁ * Q)) * (Q + 1) := by positivity
      exact mul_nonneg (by positivity) hb
    have hmono : 1 ≤ (2 : ℝ) ^ n * 2 * Real.exp (L₁ * (n : ℝ)) := by
      have h2n : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      have he : 1 ≤ Real.exp (L₁ * (n : ℝ)) :=
        Real.one_le_exp (mul_nonneg (le_of_lt hLpos) (Nat.cast_nonneg n))
      nlinarith
    have hAc : A * (C * (1 + |(c : ℝ)|))
        ≤ C * M₁ * (Real.exp (-(L₁ * d)) * Real.exp (-(L₁ * (c : ℝ)))) := by
      have hm1 := hM1 (c : ℝ) hcb
      have hCm : C * (1 + |(c : ℝ)|) ≤ C * (M₁ * Real.exp (-(L₁ * (c : ℝ)))) :=
        mul_le_mul_of_nonneg_left hm1 hCnn
      calc A * (C * (1 + |(c : ℝ)|)) ≤ A * (C * (M₁ * Real.exp (-(L₁ * (c : ℝ))))) :=
            mul_le_mul_of_nonneg_left hCm hAnn
        _ ≤ Real.exp (-(L₁ * d)) * (C * (M₁ * Real.exp (-(L₁ * (c : ℝ))))) :=
            mul_le_mul_of_nonneg_right hA (by positivity)
        _ = C * M₁ * (Real.exp (-(L₁ * d)) * Real.exp (-(L₁ * (c : ℝ)))) := by ring
    have hX : C * M₁ * (Real.exp (-(L₁ * d)) * Real.exp (-(L₁ * (c : ℝ))))
        ≤ (2 : ℝ) ^ n * 2 * C * M₁ * Real.exp (L₁ * (n : ℝ))
              * Real.exp (-(L₁ * ((z : ℝ) - 1))) := by
      have hnn : 0 ≤ C * M₁ * Real.exp (-(L₁ * ((z : ℝ) - 1))) := by positivity
      have hstep : C * M₁ * (Real.exp (-(L₁ * d)) * Real.exp (-(L₁ * (c : ℝ))))
          ≤ C * M₁ * Real.exp (-(L₁ * ((z : ℝ) - 1))) :=
        mul_le_mul_of_nonneg_left hterm2 (by positivity)
      calc C * M₁ * (Real.exp (-(L₁ * d)) * Real.exp (-(L₁ * (c : ℝ))))
          ≤ C * M₁ * Real.exp (-(L₁ * ((z : ℝ) - 1))) := hstep
        _ ≤ ((2 : ℝ) ^ n * 2 * Real.exp (L₁ * (n : ℝ)))
              * (C * M₁ * Real.exp (-(L₁ * ((z : ℝ) - 1)))) :=
            le_mul_of_one_le_left hnn hmono
        _ = (2 : ℝ) ^ n * 2 * C * M₁ * Real.exp (L₁ * (n : ℝ))
              * Real.exp (-(L₁ * ((z : ℝ) - 1))) := by ring
    calc A * (C * (1 + |(c : ℝ)|))
        ≤ C * M₁ * (Real.exp (-(L₁ * d)) * Real.exp (-(L₁ * (c : ℝ)))) := hAc
      _ ≤ (2 : ℝ) ^ n * 2 * C * M₁ * Real.exp (L₁ * (n : ℝ))
              * Real.exp (-(L₁ * ((z : ℝ) - 1))) := hX
      _ ≤ (2 : ℝ) ^ n * C * Real.exp (-(L₁ * Q * (n : ℝ)))
            * (Real.exp (-(L₁ * Q)) * (1 + (z : ℝ) + (Q + 1) * (n : ℝ))
                + Real.exp (-(L₁ * Q)) * (Q + 1))
          + (2 : ℝ) ^ n * 2 * C * M₁ * Real.exp (L₁ * (n : ℝ))
              * Real.exp (-(L₁ * ((z : ℝ) - 1))) := by linarith [hTpart]

/-- The two-branch induction: `Bseq` is bounded by the ansatz `sbn`. -/
lemma Bseq_le_sbound {Q M₁ : ℝ} (hLpos : 0 < L₁)
    (hfam : ∀ y : ℤ, b < (y : ℝ) → IsRegularBig α lam θ E L₁ q y)
    (hCnn : 0 ≤ C) (hQ : 0 < Q) (hQq : Q ≤ q / 40) (hM1nn : 0 ≤ M₁)
    (h1 : 1 ≤ L₁ * (Q + 1))
    (hM1 : ∀ x : ℝ, x ≤ thr b → 1 + |x| ≤ M₁ * Real.exp (-(L₁ * x))) :
    ∀ (n : ℕ) (z : ℤ), thr b < (z : ℝ) → Bseq hfam C n z ≤ sbn L₁ Q C M₁ n z := by
  intro n
  induction n with
  | zero =>
    intro z hz
    have hz0 : 0 ≤ (z : ℝ) := le_trans (thr_nonneg b) (le_of_lt hz)
    have hzabs : |(z : ℝ)| = (z : ℝ) := abs_of_nonneg hz0
    rw [Bseq_zero, hzabs, sbn]
    simp only [pow_zero, Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, one_mul, add_zero]
    have h2 : 0 ≤ 2 * C * M₁ * Real.exp (L₁ * ((0 : ℝ) - (z : ℝ))) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hCnn) hM1nn)
        (Real.exp_nonneg _)
    linarith [h2]
  | succ n ih =>
    intro z hz
    rw [Bseq_succ, dif_pos hz, sbn_succ]
    obtain ⟨hle1, hle2, hlen, h40a, h40b, hdet, hG1, hG2⟩ := iwin_spec (hfam := hfam) hz
    set x1 : ℤ := (iwin hfam z).1 with hx1def
    set x2 : ℤ := (iwin hfam z).2 with hx2def
    set d1 : ℝ := (((z - x1 : ℤ)) : ℝ) with hd1def
    set d2 : ℝ := (((x2 - z : ℤ)) : ℝ) with hd2def
    have hd1eq : d1 = (z : ℝ) - (x1 : ℝ) := by rw [hd1def]; push_cast; ring
    have hd2eq : d2 = (x2 : ℝ) - (z : ℝ) := by rw [hd2def]; push_cast; ring
    have hx1z : (x1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hle1
    have hx2z : (z : ℝ) ≤ (x2 : ℝ) := by exact_mod_cast hle2
    have hd1Q : Q ≤ d1 := by
      have hqq : q ≤ 40 * d1 := le_trans hlen h40a
      have : q / 40 ≤ d1 := by linarith
      linarith [hQq]
    have hd2Q : Q ≤ d2 := by
      have hqq : q ≤ 40 * d2 := le_trans hlen h40b
      have : q / 40 ≤ d2 := by linarith
      linarith [hQq]
    have hT1 : 1 + ((x1 - 1 : ℤ) : ℝ) + (Q + 1) * (n : ℝ)
        ≤ (1 + (z : ℝ) + (Q + 1) * (n : ℝ)) + d1 + 1 := by
      rw [hd1eq]; push_cast; linarith
    have hT2 : 1 + ((x2 + 1 : ℤ) : ℝ) + (Q + 1) * (n : ℝ)
        ≤ (1 + (z : ℝ) + (Q + 1) * (n : ℝ)) + d2 + 1 := by
      rw [hd2eq]; push_cast; linarith
    have hsum1 : (z : ℝ) - 1 ≤ ((x1 - 1 : ℤ) : ℝ) + d1 := by
      rw [hd1eq]; push_cast; linarith
    have hsum2 : (z : ℝ) - 1 ≤ ((x2 + 1 : ℤ) : ℝ) + d2 := by
      rw [hd2eq]; push_cast; linarith
    have hc1 := child_bound hLpos hfam hCnn hQ hM1nn h1 hM1 hz (norm_nonneg _)
      (le_of_lt hG1) hd1Q hT1 hsum1 ih
    have hc2 := child_bound hLpos hfam hCnn hQ hM1nn h1 hM1 hz (norm_nonneg _)
      (le_of_lt hG2) hd2Q hT2 hsum2 ih
    linarith [hc1, hc2]

/-- **Patching (AJ §9.1).**  A regularity family at a fixed rate `L₁` and scale `q` with
the counting condition `200 L₁ + 200 log 2 < L₁ q` forces exponential decay at rate `4 L₁/5`. -/
theorem patching {α lam : ℝ} {θ : ℝ} {E : ℂ} {L₁ q b C : ℝ} {u : ℤ → ℂ}
    (hL₁ : 0 < L₁) (hq : 0 < q) (hC : 0 < C)
    (hcount : 200 * L₁ + 200 * Real.log 2 < L₁ * q)
    (hfam : ∀ y : ℤ, b < (y : ℝ) → Work.TMC16Core.IsRegularBig α lam θ E L₁ q y)
    (hsol : Work.TMC16Core.IsFormalSol α lam θ E u)
    (hpol : ∀ n : ℤ, ‖u n‖ ≤ C * (1 + |(n : ℝ)|)) :
    ∃ K : ℝ, ∀ k : ℤ, K ≤ (k : ℝ) →
      ‖u k‖ ≤ Real.exp (-(4 * L₁ / 5) * (k : ℝ)) := by
  have hCnn : 0 ≤ C := le_of_lt hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set Q : ℝ := q / 40 with hQdef
  have hQ : 0 < Q := by rw [hQdef]; positivity
  have hQq : Q ≤ q / 40 := le_of_eq hQdef
  set M₁ : ℝ := Real.exp (L₁ * thr b) * (1 + |thr b| + 2 / L₁) with hM₁def
  have hM1nn : 0 ≤ M₁ := by rw [hM₁def]; positivity
  have hM1 : ∀ x : ℝ, x ≤ thr b → 1 + |x| ≤ M₁ * Real.exp (-(L₁ * x)) := by
    rw [hM₁def]; exact one_add_abs_le_M1 hL₁
  have h1 : 1 ≤ L₁ * (Q + 1) := by
    have hLQ : 5 * L₁ + 5 * Real.log 2 < L₁ * Q := by
      rw [hQdef, show L₁ * (q / 40) = L₁ * q / 40 by ring]
      linarith [hcount]
    have hl : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    nlinarith [hLQ, hL₁, hl]
  set P : ℝ := 2 * (1 + (Q + 1) + 2 + 40 / q) * C with hPdef
  set Pp : ℝ := 4 * C * M₁ * Real.exp L₁ with hPpdef
  obtain ⟨K₀, hK₀⟩ := exists_const_affine_exp (P := P) (P' := Pp) hL₁ hq hcount
  refine ⟨max (max K₀ 1) (thr b + 1), ?_⟩
  intro k hk
  have hkK₀ : K₀ ≤ (k : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hkb : thr b < (k : ℝ) := lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_right _ _) hk)
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := le_trans zero_le_one hk1
  set N : ℕ := Nat.ceil (40 * (k : ℝ) / q) with hNdef
  have hNlow : 40 * (k : ℝ) / q ≤ (N : ℝ) := Nat.le_ceil _
  have hNup : (N : ℝ) < 40 * (k : ℝ) / q + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hNup' : (N : ℝ) ≤ 40 * (k : ℝ) / q + 1 := le_of_lt hNup
  have hu : ‖u k‖ ≤ Bseq hfam C N k := le_Bseq hfam C hsol hpol N k
  have hBs : Bseq hfam C N k ≤ sbn L₁ Q C M₁ N k :=
    Bseq_le_sbound hL₁ hfam hCnn hQ hQq hM1nn h1 hM1 N k hkb
  refine le_trans (le_trans hu hBs) ?_
  -- final estimates
  have hQN : (k : ℝ) ≤ Q * (N : ℝ) := by
    have hq40 : 0 < q / 40 := by positivity
    have h := mul_le_mul_of_nonneg_right hNlow (le_of_lt hq40)
    have hL : 40 * (k : ℝ) / q * (q / 40) = (k : ℝ) := by field_simp
    rw [hQdef]
    linarith [h, hL]
  have h2N : (2 : ℝ) ^ N = Real.exp ((N : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hNlog : (N : ℝ) * Real.log 2 ≤ (40 * Real.log 2 / q) * (k : ℝ) + Real.log 2 := by
    have h := mul_le_mul_of_nonneg_right hNup' (le_of_lt hlog2)
    have he : (40 * (k : ℝ) / q + 1) * Real.log 2
        = (40 * Real.log 2 / q) * (k : ℝ) + Real.log 2 := by ring
    linarith [h, he]
  have hTk : 1 + (k : ℝ) + (Q + 1) * (N : ℝ) ≤ (1 + (Q + 1) + 2 + 40 / q) * (k : ℝ) := by
    have hQNle : (Q + 1) * (N : ℝ) ≤ (Q + 1) * (40 * (k : ℝ) / q + 1) :=
      mul_le_mul_of_nonneg_left hNup' (by linarith)
    have hQNle2 : (Q + 1) * (40 * (k : ℝ) / q + 1)
        = 40 * (Q + 1) * (k : ℝ) / q + (Q + 1) := by ring
    have hQr : 40 * (Q + 1) / q = 1 + 40 / q := by rw [hQdef]; field_simp
    have hkey : 40 * (Q + 1) * (k : ℝ) / q = (1 + 40 / q) * (k : ℝ) := by
      rw [show 40 * (Q + 1) * (k : ℝ) / q = 40 * (Q + 1) / q * (k : ℝ) by ring, hQr]
    have hQ1k : (Q + 1) ≤ (Q + 1) * (k : ℝ) := le_mul_of_one_le_right (by linarith) hk1
    rw [hQNle2, hkey] at hQNle
    nlinarith [hQNle, hQ1k, hk1]
  have hLQN : L₁ * (k : ℝ) ≤ L₁ * Q * (N : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hQN (le_of_lt hL₁)
    linarith
  have hT1s : (2 : ℝ) ^ N * (C * Real.exp (-(L₁ * Q * (N : ℝ)))
        * (1 + (k : ℝ) + (Q + 1) * (N : ℝ)))
      ≤ P * (k : ℝ) * Real.exp (-(L₁ - 40 * Real.log 2 / q) * (k : ℝ)) := by
    have hNlog2 : (N : ℝ) * Real.log 2 - L₁ * Q * (N : ℝ)
        ≤ ((40 * Real.log 2 / q) * (k : ℝ) + Real.log 2) - L₁ * (k : ℝ) := by
      linarith [hNlog, hLQN]
    have e1 : Real.exp ((N : ℝ) * Real.log 2) * Real.exp (-(L₁ * Q * (N : ℝ)))
        = Real.exp ((N : ℝ) * Real.log 2 - L₁ * Q * (N : ℝ)) := by
      rw [← Real.exp_add]; ring_nf
    have eq : (2 : ℝ) ^ N * (C * Real.exp (-(L₁ * Q * (N : ℝ)))
          * (1 + (k : ℝ) + (Q + 1) * (N : ℝ)))
        = C * (1 + (k : ℝ) + (Q + 1) * (N : ℝ))
            * Real.exp ((N : ℝ) * Real.log 2 - L₁ * Q * (N : ℝ)) := by
      rw [h2N, ← e1]; ring
    rw [eq]
    have hE : Real.exp ((N : ℝ) * Real.log 2 - L₁ * Q * (N : ℝ))
        ≤ Real.exp (((40 * Real.log 2 / q) * (k : ℝ) + Real.log 2) - L₁ * (k : ℝ)) :=
      Real.exp_le_exp.mpr hNlog2
    have hstep1 : C * (1 + (k : ℝ) + (Q + 1) * (N : ℝ))
          * Real.exp ((N : ℝ) * Real.log 2 - L₁ * Q * (N : ℝ))
        ≤ C * ((1 + (Q + 1) + 2 + 40 / q) * (k : ℝ))
          * Real.exp ((N : ℝ) * Real.log 2 - L₁ * Q * (N : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul_of_nonneg_left hTk hCnn
    have hstep2 : C * ((1 + (Q + 1) + 2 + 40 / q) * (k : ℝ))
          * Real.exp ((N : ℝ) * Real.log 2 - L₁ * Q * (N : ℝ))
        ≤ C * ((1 + (Q + 1) + 2 + 40 / q) * (k : ℝ))
          * Real.exp (((40 * Real.log 2 / q) * (k : ℝ) + Real.log 2) - L₁ * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    refine le_trans hstep1 (le_trans hstep2 ?_)
    have h2e : Real.exp (((40 * Real.log 2 / q) * (k : ℝ) + Real.log 2) - L₁ * (k : ℝ))
        = 2 * Real.exp (-(L₁ - 40 * Real.log 2 / q) * (k : ℝ)) := by
      rw [show ((40 * Real.log 2 / q) * (k : ℝ) + Real.log 2) - L₁ * (k : ℝ)
            = Real.log 2 + (-(L₁ - 40 * Real.log 2 / q) * (k : ℝ)) by ring,
          Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    apply le_of_eq; rw [h2e, hPdef]; ring
  have hNk : L₁ * ((N : ℝ) - (k : ℝ)) ≤ L₁ * (40 * (k : ℝ) / q + 1) - L₁ * (k : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hNup' (le_of_lt hL₁)
    linarith
  have hT2s : (2 : ℝ) ^ N * (2 * C * M₁ * Real.exp (L₁ * ((N : ℝ) - (k : ℝ))))
      ≤ Pp * Real.exp (-(L₁ - 40 * (Real.log 2 + L₁) / q) * (k : ℝ)) := by
    have e1 : Real.exp ((N : ℝ) * Real.log 2) * Real.exp (L₁ * ((N : ℝ) - (k : ℝ)))
        = Real.exp ((N : ℝ) * Real.log 2 + L₁ * ((N : ℝ) - (k : ℝ))) := by
      rw [← Real.exp_add]
    have eq : (2 : ℝ) ^ N * (2 * C * M₁ * Real.exp (L₁ * ((N : ℝ) - (k : ℝ))))
        = 2 * C * M₁ * (Real.exp ((N : ℝ) * Real.log 2)
            * Real.exp (L₁ * ((N : ℝ) - (k : ℝ)))) := by
      rw [h2N]; ring
    rw [eq, e1]
    have hE : Real.exp ((N : ℝ) * Real.log 2 + L₁ * ((N : ℝ) - (k : ℝ)))
        ≤ Real.exp (((40 * Real.log 2 / q) * (k : ℝ) + Real.log 2)
            + (L₁ * (40 * (k : ℝ) / q + 1) - L₁ * (k : ℝ))) :=
      Real.exp_le_exp.mpr (by linarith [hNlog, hNk])
    refine le_trans (mul_le_mul_of_nonneg_left hE (by positivity)) ?_
    have h2e : Real.exp (((40 * Real.log 2 / q) * (k : ℝ) + Real.log 2)
          + (L₁ * (40 * (k : ℝ) / q + 1) - L₁ * (k : ℝ)))
        = 2 * (Real.exp L₁ * Real.exp (-(L₁ - 40 * (Real.log 2 + L₁) / q) * (k : ℝ))) := by
      rw [show ((40 * Real.log 2 / q) * (k : ℝ) + Real.log 2)
              + (L₁ * (40 * (k : ℝ) / q + 1) - L₁ * (k : ℝ))
            = Real.log 2 + (L₁ + (-(L₁ - 40 * (Real.log 2 + L₁) / q) * (k : ℝ))) by ring,
          Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    apply le_of_eq; rw [h2e, hPpdef]; ring
  have hsplit1 : Real.exp (-(L₁ - 40 * Real.log 2 / q) * (k : ℝ))
      = Real.exp (-((L₁ / 5 - 40 * Real.log 2 / q) * (k : ℝ)))
          * Real.exp (-(4 * L₁ / 5) * (k : ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsplit2 : Real.exp (-(L₁ - 40 * (Real.log 2 + L₁) / q) * (k : ℝ))
      = Real.exp (-((L₁ / 5 - 40 * (Real.log 2 + L₁) / q) * (k : ℝ)))
          * Real.exp (-(4 * L₁ / 5) * (k : ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc sbn L₁ Q C M₁ N k
      = (2 : ℝ) ^ N * (C * Real.exp (-(L₁ * Q * (N : ℝ)))
            * (1 + (k : ℝ) + (Q + 1) * (N : ℝ)))
        + (2 : ℝ) ^ N * (2 * C * M₁ * Real.exp (L₁ * ((N : ℝ) - (k : ℝ)))) := by
        rw [sbn]; ring
    _ ≤ P * (k : ℝ) * Real.exp (-(L₁ - 40 * Real.log 2 / q) * (k : ℝ))
        + Pp * Real.exp (-(L₁ - 40 * (Real.log 2 + L₁) / q) * (k : ℝ)) :=
        add_le_add hT1s hT2s
    _ = (P * (k : ℝ) * Real.exp (-((L₁ / 5 - 40 * Real.log 2 / q) * (k : ℝ)))
          + Pp * Real.exp (-((L₁ / 5 - 40 * (Real.log 2 + L₁) / q) * (k : ℝ))))
          * Real.exp (-(4 * L₁ / 5) * (k : ℝ)) := by
        rw [hsplit1, hsplit2]; ring
    _ ≤ 1 * Real.exp (-(4 * L₁ / 5) * (k : ℝ)) :=
        mul_le_mul_of_nonneg_right (hK₀ k hkK₀) (Real.exp_nonneg _)
    _ = Real.exp (-(4 * L₁ / 5) * (k : ℝ)) := one_mul _

end
end Work.TMC16Core.Basic
