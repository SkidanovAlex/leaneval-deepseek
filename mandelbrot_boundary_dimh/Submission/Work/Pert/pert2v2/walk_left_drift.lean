import Mathlib
import Submission.Work.Pert.pert2v2.walk_left_deep
import Submission.Work.Pert.pert2v2.drift_geom_small
import Submission.Work.Pert.pert2v2.drift_quotient_le

set_option maxHeartbeats 8000000

/-!
# `Work.Pert.pert2v2.walk_left_drift`

The **drift-corrected** walk in the lower gate.  `F` is a near-translation of the gate `Qm Ξ α`
with the Abel relation `Φ (F z) = Φ z + 1` on the points with right-room `1 + 1/8`, and
asymptotic to the translation by `ρ` deep below: `‖F w - (w + ρ)‖ ≤ M e^{κ w.im}` for `w.im < -Y`.

The walk itself is the one of `Work.Pert.pert2v2.walk_left_deep` (`x₀ := 1`): starting from a
point `z` of the gate with `z.im` very negative and `z.re ≤ -2`, the iterates `F^[k] z` advance
the real part by at least `15/16` and at most `67/64` per step until the real part crosses `-2`,
so the first index with `(F^[k] z).re ≥ -2` lands in the column `[-2, -2 + 67/64] ⊆ [-2, 0]`.

The new content is the **accumulated drift**: each step moves `w - z` by `ρ` up to `1/64`, so

`(F^[k] z - z) - k ρ = Σ_{j<k} (F z_j - z_j - ρ)`,  `z_j := F^[j] z`,

and all the walk points satisfy `z_j.im ≤ -(55/64) H` (`H = -z.im`, `k ≤ 3 H`), whence every
summand is at most `M e^{-(55/64) κ H}` and the sum is at most `3 H M e^{-(55/64) κ H} ≤ 1/64`
as soon as `H ≥ 1000 (max 1 M)/κ²`.  With `Φ w = Φ z + k` this gives

`‖(Φ w - w/ρ) - (Φ z - z/ρ)‖ = ‖k - (w - z)/ρ‖ = ‖(w - z) - kρ‖/‖ρ‖ ≤ (1/64)/(31/32) ≤ 1`.
-/

namespace Work.Pert.pert2v2

open MandelDim Complex

/-! ## Small arithmetic helpers (private copies of the ones of `walk_left_deep`) -/

private lemma aux_R_le {R H A Bb Ξ ai : ℝ} (h1 : Ξ - A - ai < -R) (h2 : ai ≤ H + Bb) :
    R ≤ H + A + Bb - Ξ := by linarith

private lemma aux_R0_le {R₀ x₀ R H A Bb Ξ M1 : ℝ} (h1 : R₀ = x₀ + R) (h2 : R ≤ H + A + Bb - Ξ)
    (hx : x₀ ≤ |x₀|) (hA : A ≤ |A|) (hΞ : -Ξ ≤ |Ξ|) (hx1 : |x₀| ≤ M1) (hA1 : |A| ≤ M1)
    (hΞ1 : |Ξ| ≤ M1) (hBb1 : Bb ≤ M1) (hM1 : 4 * M1 ≤ H) : R₀ ≤ 2 * H := by linarith

private lemma aux_C2 {K R₀ H : ℝ} (hK : K ≤ (7 / 6) * R₀ + 3) (hR₀ : R₀ ≤ 2 * H)
    (hH : 1 ≤ H) : K * (3 / 64) ≤ H / 2 := by linarith

private lemma aux_C3 {K R₀ H R Ξ x₀ A Bb : ℝ} (hK : K ≤ (7 / 6) * R₀ + 3)
    (hR₀ : R₀ = x₀ + R) (hR : R ≤ H + A + Bb - Ξ) (hA : A ≤ |A|) (hx : x₀ ≤ |x₀|)
    (hΞ : Ξ ≤ |Ξ|) (hx1 : |x₀| ≤ H / 1000) (hA1 : |A| ≤ H / 1000) (hΞ1 : |Ξ| ≤ H / 1000)
    (hBb1 : Bb ≤ H / 1000) (hH1 : 10 ≤ H) : K * (35 / 32) + 9 / 8 ≤ H - Ξ + R := by linarith

private lemma aux_kick {K R₀ : ℝ} (hK : (7 / 6) * R₀ ≤ K) (hR₀ : 3 ≤ R₀) :
    R₀ ≤ K * (15 / 16) := by linarith

private lemma aux_small3 {K R₀ : ℝ} (hK : K ≤ (7 / 6) * R₀ + 3) (hR₀ : 3 ≤ R₀) :
    K * (3 / 64) ≤ R₀ / 2 + 1 := by linarith

private lemma aux_room_step {i K m0 m : ℝ} (hi : i ≤ K - 1) (h1 : m0 - i * (35 / 32) ≤ m)
    (h2 : K * (35 / 32) + 9 / 8 ≤ m0) : 1 + 1 / 8 ≤ m := by linarith

private lemma aux_im_step {i K zi m H : ℝ} (hi : i ≤ K) (h1 : m ≤ zi + i * (3 / 64))
    (h2 : zi = -H) (h3 : K * (3 / 64) ≤ H / 2) : m ≤ -H / 2 := by linarith

private lemma aux_acc {x y z d : ℝ} {i : ℕ} (h1 : y + d ≤ z) (h2 : x + (i : ℝ) * d ≤ y) :
    x + ((i + 1 : ℕ) : ℝ) * d ≤ z := by push_cast; linarith

private lemma aux_acc' {x y w d : ℝ} {i : ℕ} (h1 : w ≤ y + d) (h2 : y ≤ x + (i : ℝ) * d) :
    w ≤ x + ((i + 1 : ℕ) : ℝ) * d := by push_cast; linarith

private lemma aux_acc'' {x y w d : ℝ} {i : ℕ} (h1 : y - d ≤ w) (h2 : x - (i : ℝ) * d ≤ y) :
    x - ((i + 1 : ℕ) : ℝ) * d ≤ w := by push_cast; linarith

private lemma aux_lin {Y₂ H S D E : ℝ} (hY₂ : Y₂ = 1000 * S + D + E) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (h : Y₂ ≤ H) : 1000 * S ≤ H := by linarith

private lemma aux_expC {Y₂ H S D E : ℝ} (hY₂ : Y₂ = 1000 * S + D + E) (hS : 0 ≤ S)
    (hE : 0 ≤ E) (h : Y₂ ≤ H) : D ≤ H := by linarith

private lemma aux_driftC {Y₂ H S D E : ℝ} (hY₂ : Y₂ = 1000 * S + D + E) (hS : 0 ≤ S)
    (hD : 0 ≤ D) (h : Y₂ ≤ H) : E ≤ H := by linarith

private lemma aux_MY {S H MY x₀ A Bb Ξ M : ℝ}
    (hS : S = |x₀| + |A| + Bb + |Ξ| + MY + M + 1) (ha : 0 ≤ |x₀|) (hb : 0 ≤ |A|)
    (hc : 0 ≤ |Ξ|) (hd : 0 ≤ Bb) (hm : 0 ≤ MY) (hM0 : 0 ≤ M) (hlin : 1000 * S ≤ H) :
    1000 * MY ≤ H := by linarith

private lemma aux_2Y {H Y MY : ℝ} (h1 : Y ≤ MY) (h2 : 0 ≤ MY) (h3 : 1000 * MY ≤ H) :
    2 * Y ≤ H := by linarith

private lemma aux_S' {S H x₀ A Bb Ξ MY M : ℝ}
    (hS : S = |x₀| + |A| + Bb + |Ξ| + MY + M + 1) (hm : 0 ≤ MY) (hM0 : 0 ≤ M)
    (hlin : 1000 * S ≤ H) : 1000 * (|x₀| + |A| + Bb + |Ξ| + 1) ≤ H := by linarith

private lemma aux_bounds {H x₀ A Bb Ξ : ℝ} (hd : 0 ≤ Bb) (ha : 0 ≤ |x₀|) (hb : 0 ≤ |A|)
    (hc : 0 ≤ |Ξ|) (hH : 1000 * (|x₀| + |A| + Bb + |Ξ| + 1) ≤ H) :
    |x₀| ≤ H / 1000 ∧ |A| ≤ H / 1000 ∧ |Ξ| ≤ H / 1000 ∧ Bb ≤ H / 1000 := by
  have hH0 : (0 : ℝ) ≤ H := by linarith
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ## The independent pieces of the drift estimate (proved in parallel and imported) -/

-- The arithmetic core (`Work.Pert.pert2v2.drift_geom_small`), the telescoping of the per-step
-- near-translation bound (`Work.Pert.pert2v2.drift_accumulate`, whose induction is carried out
-- inline in `walk_left_column` below) and the final comparison of the drift-corrected
-- coordinates (`Work.Pert.pert2v2.drift_quotient_le`) are proved in their own modules and used
-- here.  Nothing about the gate enters them.

/-! ## The walk into the column, with the accumulated drift -/

/-- **Deep walk into the column `[x₀ - 3, x₀ - 3 + 67/64]`.**  Every point `z` of the lower gate
that is deep (`z.im ≤ -Y₂`) and left of the spine (`z.re ≤ x₀ - 3`) can be walked forward, and the
first iterate whose real part reaches `x₀ - 3` lies in the column; moreover the accumulated
near-translation error is at most `1/64`. -/
theorem walk_left_column {Ξ : ℝ} {α ρ : ℂ} {M κ Y : ℝ} {F Φ : ℂ → ℂ} {x₀ : ℝ}
    (hM : 0 < M) (hκ : 0 < κ) (hρ : ‖ρ - 1‖ ≤ 1 / 32)
    (hfwd : ∀ z ∈ Work.Pert.Qm Ξ α, 1 + 1 / 8 ≤ Work.Pert.margB_g Ξ z →
      F z ∈ Work.Pert.Qm Ξ α ∧ Φ (F z) = Φ z + 1)
    (hdec : ∀ w ∈ Work.Pert.Qm Ξ α, w.im < -Y →
      ‖F w - (w + ρ)‖ ≤ M * Real.exp (κ * w.im)) :
    ∃ Y₂ : ℝ, ∀ z ∈ Work.Pert.Qm Ξ α, z.im ≤ -Y₂ → z.re ≤ x₀ - 3 →
      ∃ (k : ℕ) (w : ℂ), w ∈ Work.Pert.Qm Ξ α ∧ Φ w = Φ z + (k : ℂ) ∧
        w.re ∈ Set.Icc (x₀ - 3) (x₀ - 3 + 67 / 64) ∧
        w.im ≤ z.im + (x₀ - z.re) / 2 + 1 ∧
        ‖(w - z) - (k : ℂ) * ρ‖ ≤ 1 / 64 := by
  classical
  -- ## elementary facts about `ρ`
  have hρre : |ρ.re - 1| ≤ 1 / 32 := by
    have h := Complex.abs_re_le_norm (ρ - 1)
    simp only [Complex.sub_re, Complex.one_re] at h
    exact le_trans h hρ
  have hρim : |ρ.im| ≤ 1 / 32 := by
    have h := Complex.abs_im_le_norm (ρ - 1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at h
    exact le_trans h hρ
  -- ## the constants
  set A : ℝ := (1 / α).re with hA
  set B : ℝ := (1 / α).im with hB
  set S : ℝ := |x₀| + |A| + |B| + |Ξ| + max Y 0 + M + 1 with hS
  set Y₂ : ℝ := 1000 * S + 200 * max 1 M / κ + 1000 * max 1 M / κ ^ 2 with hY₂
  refine ⟨Y₂, ?_⟩
  intro z hzQ hzim hzre
  -- ## the geometric data of `z`
  set H : ℝ := -z.im with hH
  set R : ℝ := -z.re with hR
  set R₀ : ℝ := x₀ - z.re with hR₀
  have hMY0 : (0 : ℝ) ≤ max Y 0 := le_max_right Y 0
  have hA0 : (0 : ℝ) ≤ |A| := abs_nonneg A
  have hB0 : (0 : ℝ) ≤ |B| := abs_nonneg B
  have hΞ0 : (0 : ℝ) ≤ |Ξ| := abs_nonneg Ξ
  have hx₀0 : (0 : ℝ) ≤ |x₀| := abs_nonneg x₀
  have hS1 : (1 : ℝ) ≤ S := by
    rw [hS]
    linarith
  have hD0 : (0 : ℝ) ≤ 200 * max 1 M / κ := div_nonneg (by positivity) hκ.le
  have hE0 : (0 : ℝ) ≤ 1000 * max 1 M / κ ^ 2 :=
    div_nonneg (by positivity) (sq_nonneg κ)
  have hY₂pos : 0 < Y₂ := by
    rw [hY₂]
    linarith
  have hHge : Y₂ ≤ H := by linarith
  have hHpos : 0 < H := lt_of_lt_of_le hY₂pos hHge
  have hzimneg : z.im < 0 := by linarith
  have hzabs : |z.im| = H := by rw [abs_of_neg hzimneg, hH]
  have hzeq : z.re = -R := by rw [hR]; ring
  have hR₀ge : 3 ≤ R₀ := by rw [hR₀]; linarith
  have hR₀eq : R₀ = x₀ + R := by rw [hR₀, hR, hzeq]; ring
  -- ## the numeric content of the choice of `Y₂`
  have hlin : 1000 * S ≤ H := aux_lin hY₂ hD0 hE0 hHge
  have hexpC : 200 * max 1 M / κ ≤ H := aux_expC hY₂ (le_trans zero_le_one hS1) hE0 hHge
  have hdrC : 1000 * max 1 M / κ ^ 2 ≤ H := aux_driftC hY₂ (le_trans zero_le_one hS1) hD0 hHge
  have hexp0 : M * Real.exp (-(κ * H / 2)) ≤ 1 / 64 :=
    exp_small_of_large (C := H) hM hκ hexpC le_rfl
  have hS' : 1000 * (|x₀| + |A| + |B| + |Ξ| + 1) ≤ H := aux_S' hS hMY0 hM.le hlin
  have hMYle : 1000 * max Y 0 ≤ H := aux_MY hS hx₀0 hA0 hΞ0 hB0 hMY0 hM.le hlin
  have hH2Y : 2 * Y ≤ H := aux_2Y (le_max_left Y 0) hMY0 hMYle
  obtain ⟨hbx, hbA, hbΞ, hbB⟩ := aux_bounds hB0 hx₀0 hA0 hΞ0 hS'
  -- ## the gate conditions
  obtain ⟨hQmA, hQmB⟩ := (Work.Pert.Qm_mem_iff (ξ := Ξ) (α := α) (z := z)).mp hzQ
  have hAle : Ξ - A - |z.im + B| < z.re := by rw [hA, hB]; exact hQmA
  have hRle : R ≤ H + A + |B| - Ξ := by
    have h1 : |z.im + B| ≤ H + |B| := by
      calc |z.im + B| ≤ |z.im| + |B| := abs_add_le _ _
        _ = H + |B| := by rw [hzabs]
    have h2 : Ξ - A - |z.im + B| < -R := by rw [← hzeq]; exact hAle
    exact aux_R_le h2 h1
  have hroom0 : Work.Pert.margB_g Ξ z = H - Ξ + R := by
    rw [Work.Pert.margB_g, hzabs, hzeq]; ring
  -- ## the a priori step count
  set K : ℕ := ⌈(7 / 6) * R₀⌉₊ + 2 with hK
  have hKub : (K : ℝ) ≤ (7 / 6) * R₀ + 3 := by
    have h0 : (0 : ℝ) ≤ (7 / 6) * R₀ := by linarith
    have h1 : ((⌈(7 / 6) * R₀⌉₊ : ℕ) : ℝ) < (7 / 6) * R₀ + 1 := Nat.ceil_lt_add_one h0
    simp only [hK]
    push_cast
    linarith
  have hKlb : (7 / 6) * R₀ ≤ (K : ℝ) := by
    have h1 := Nat.le_ceil ((7 / 6) * R₀)
    simp only [hK]
    push_cast
    linarith
  have hxle : x₀ ≤ |x₀| := le_abs_self x₀
  have hΞle : Ξ ≤ |Ξ| := le_abs_self Ξ
  have hΞne : -Ξ ≤ |Ξ| := neg_le_abs Ξ
  have hAle' : A ≤ |A| := le_abs_self A
  have hH10 : (10 : ℝ) ≤ H := by linarith
  -- the step count is compatible with the room available
  have hC3 : (K : ℝ) * (35 / 32) + 9 / 8 ≤ Work.Pert.margB_g Ξ z := by
    rw [hroom0]
    exact aux_C3 hKub hR₀eq hRle hAle' hxle hΞle hbx hbA hbΞ hbB hH10
  -- the height along the walk stays controlled
  have hR₀2H : R₀ ≤ 2 * H :=
    aux_R0_le hR₀eq hRle hxle hAle' hΞne hbx hbA hbΞ hbB (by linarith)
  have hC2 : (K : ℝ) * (3 / 64) ≤ H / 2 := aux_C2 hKub hR₀2H (by linarith)
  -- the number of steps is at most `3 H`
  have hK3H : (K : ℝ) ≤ 3 * H := by linarith
  -- ## the drift constant
  set ε : ℝ := M * Real.exp (-(55 / 64) * (κ * H)) with hε
  have hε0 : 0 ≤ ε := by rw [hε]; exact le_of_lt (mul_pos hM (Real.exp_pos _))
  -- ## one step of the walk
  have hstep : ∀ i : ℕ, i < K → (F^[i] z) ∈ Work.Pert.Qm Ξ α →
      (F^[i] z).im ≤ z.im + (i : ℝ) * (3 / 64) →
      Work.Pert.margB_g Ξ z - (i : ℝ) * (35 / 32) ≤ Work.Pert.margB_g Ξ (F^[i] z) →
      (F^[i + 1] z) ∈ Work.Pert.Qm Ξ α ∧
      Φ (F^[i + 1] z) = Φ (F^[i] z) + 1 ∧
      (F^[i] z).re + 15 / 16 ≤ (F^[i + 1] z).re ∧
      (F^[i + 1] z).re ≤ (F^[i] z).re + 9 / 8 ∧
      (F^[i + 1] z).re ≤ (F^[i] z).re + 67 / 64 ∧
      (F^[i + 1] z).im ≤ (F^[i] z).im + 3 / 64 ∧
      Work.Pert.margB_g Ξ (F^[i] z) - 35 / 32 ≤ Work.Pert.margB_g Ξ (F^[i + 1] z) ∧
      ‖F (F^[i] z) - ((F^[i] z) + ρ)‖ ≤ ε := by
    intro i hi hQi him1 hroomi
    have hiK : (i : ℝ) ≤ (K : ℝ) - 1 := by
      have h2 : i + 1 ≤ K := by omega
      have h3 : (i : ℝ) + 1 ≤ (K : ℝ) := by exact_mod_cast h2
      linarith
    -- the margins at the `i`-th point
    have hroomi' : 1 + 1 / 8 ≤ Work.Pert.margB_g Ξ (F^[i] z) :=
      aux_room_step hiK hroomi hC3
    have him2 : (F^[i] z).im ≤ -H / 2 := by
      have h1 : (i : ℝ) ≤ (K : ℝ) := by exact_mod_cast le_of_lt hi
      have hzimeq : z.im = -H := by rw [hH]; ring
      exact aux_im_step h1 him1 hzimeq hC2
    have himY : (F^[i] z).im < -Y := by
      have h3 : Y ≤ H / 2 := by linarith
      linarith
    obtain ⟨hQsucc, hΦsucc⟩ := hfwd (F^[i] z) hQi hroomi'
    have hd := hdec (F^[i] z) hQi himY
    have hei : M * Real.exp (κ * (F^[i] z).im) ≤ 1 / 64 := by
      have h1 : κ * (F^[i] z).im ≤ κ * (-H / 2) := by nlinarith [him2, hκ]
      have h2 : Real.exp (κ * (F^[i] z).im) ≤ Real.exp (-(κ * H / 2)) := by
        apply Real.exp_le_exp.mpr
        calc κ * (F^[i] z).im ≤ κ * (-H / 2) := h1
          _ = -(κ * H / 2) := by ring
      calc M * Real.exp (κ * (F^[i] z).im) ≤ M * Real.exp (-(κ * H / 2)) :=
            mul_le_mul_of_nonneg_left h2 hM.le
        _ ≤ 1 / 64 := hexp0
    have hd64 : ‖F (F^[i] z) - ((F^[i] z) + ρ)‖ ≤ 1 / 64 := le_trans hd hei
    have hsb := step_bounds (Ξ := Ξ) (ρ := ρ) (F := F) (a := F^[i] z) hρre hρim hd64
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hsb
    -- the tight right-displacement bound `67/64`
    have htight : (F (F^[i] z)).re ≤ (F^[i] z).re + 67 / 64 := by
      have hre64 : |(F (F^[i] z)).re - ((F^[i] z).re + ρ.re)| ≤ 1 / 64 := by
        have h : (F (F^[i] z)).re - ((F^[i] z).re + ρ.re)
            = (F (F^[i] z) - ((F^[i] z) + ρ)).re := by simp [Complex.sub_re]
        rw [h]
        exact le_trans (Complex.abs_re_le_norm _) hd64
      have hρre32 : ρ.re ≤ 1 + 1 / 32 := by
        have := (abs_le.mp hρre).2; linarith
      have := (abs_le.mp hre64).2
      linarith
    -- the drift step
    have hi3H : (i : ℝ) ≤ 3 * H := by
      have h1 : (i : ℝ) ≤ (K : ℝ) := by exact_mod_cast le_of_lt hi
      linarith
    have him55 : (F^[i] z).im ≤ -(55 / 64) * H := by
      have hzimeq : z.im = -H := by rw [hH]; ring
      have h2 : (i : ℝ) * (3 / 64) ≤ 3 * H * (3 / 64) :=
        mul_le_mul_of_nonneg_right hi3H (by norm_num)
      linarith
    have hdeep : κ * (F^[i] z).im ≤ -(55 / 64) * (κ * H) := by
      have h := mul_le_mul_of_nonneg_left him55 hκ.le
      calc κ * (F^[i] z).im ≤ κ * (-(55 / 64) * H) := h
        _ = -(55 / 64) * (κ * H) := by ring
    have hdriftε : ‖F (F^[i] z) - ((F^[i] z) + ρ)‖ ≤ ε := by
      rw [hε]
      calc ‖F (F^[i] z) - ((F^[i] z) + ρ)‖ ≤ M * Real.exp (κ * (F^[i] z).im) := hd
        _ ≤ M * Real.exp (-(55 / 64) * (κ * H)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hdeep) hM.le
    have hiter : F^[i + 1] z = F (F^[i] z) := Function.iterate_succ_apply' F i z
    have ha0 : (F^[i] z).im ≤ 0 := by linarith
    have hb0 : (F (F^[i] z)).im ≤ 0 := by linarith
    rw [hiter] at ⊢
    exact ⟨hQsucc, hΦsucc, hb1, hb2, htight, hb3, hb4 ha0 hb0, hdriftε⟩
  -- ## the walk estimates
  have hmain : ∀ j ≤ K, (F^[j] z) ∈ Work.Pert.Qm Ξ α ∧ Φ (F^[j] z) = Φ z + (j : ℂ) ∧
      z.re + (j : ℝ) * (15 / 16) ≤ (F^[j] z).re ∧
      (F^[j] z).re ≤ z.re + (j : ℝ) * (9 / 8) ∧
      (F^[j] z).im ≤ z.im + (j : ℝ) * (3 / 64) ∧
      Work.Pert.margB_g Ξ z - (j : ℝ) * (35 / 32) ≤ Work.Pert.margB_g Ξ (F^[j] z) ∧
      ‖((F^[j] z) - z) - (j : ℂ) * ρ‖ ≤ (j : ℝ) * ε := by
    intro j hj
    induction j with
    | zero =>
      simp only [Function.iterate_zero, id_eq]
      refine ⟨hzQ, by simp, by simp, by simp, by simp, by simp, by simp⟩
    | succ i ih =>
      have hiK : i ≤ K := by omega
      obtain ⟨hQi, hΦi, hre1, hre2, him1, hroomi, hdri⟩ := ih hiK
      have hlt : i < K := by omega
      obtain ⟨hQs, hΦs, hs1, hs2, hs2', hs3, hs4, hdrs⟩ := hstep i hlt hQi him1 hroomi
      have hΦs' : Φ (F^[i + 1] z) = Φ z + ((i + 1 : ℕ) : ℂ) := by
        rw [hΦs, hΦi]
        push_cast
        ring
      have hdrift_succ : ‖((F^[i + 1] z) - z) - ((i + 1 : ℕ) : ℂ) * ρ‖
          ≤ ((i + 1 : ℕ) : ℝ) * ε := by
        have hiter : F^[i + 1] z = F (F^[i] z) := Function.iterate_succ_apply' F i z
        have hsplit : ((F^[i + 1] z) - z) - ((i + 1 : ℕ) : ℂ) * ρ
            = (((F^[i] z) - z) - (i : ℂ) * ρ) + (F (F^[i] z) - ((F^[i] z) + ρ)) := by
          rw [hiter]
          push_cast
          ring
        rw [hsplit]
        calc ‖(((F^[i] z) - z) - (i : ℂ) * ρ) + (F (F^[i] z) - ((F^[i] z) + ρ))‖
              ≤ ‖((F^[i] z) - z) - (i : ℂ) * ρ‖ + ‖F (F^[i] z) - ((F^[i] z) + ρ)‖ :=
            norm_add_le _ _
          _ ≤ (i : ℝ) * ε + ε := add_le_add hdri hdrs
          _ = ((i + 1 : ℕ) : ℝ) * ε := by push_cast; ring
      exact ⟨hQs, hΦs', aux_acc hs1 hre1, aux_acc' hs2 hre2, aux_acc' hs3 him1,
        aux_acc'' hs4 hroomi, hdrift_succ⟩
  -- ## the landing index
  have hex : ∃ j : ℕ, j ≤ K ∧ x₀ - 3 ≤ (F^[j] z).re := by
    refine ⟨K, le_rfl, ?_⟩
    have h1 := (hmain K le_rfl).2.2.1
    have h3 : R₀ ≤ (K : ℝ) * (15 / 16) := aux_kick hKlb hR₀ge
    have h6 : x₀ ≤ z.re + R₀ := by rw [hR₀]; ring_nf; linarith
    linarith only [h1, h3, h6]
  obtain ⟨k, hkK, hkre, hkmin⟩ :
      ∃ k : ℕ, k ≤ K ∧ x₀ - 3 ≤ (F^[k] z).re ∧
        ∀ j < k, ¬(j ≤ K ∧ x₀ - 3 ≤ (F^[j] z).re) :=
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      fun j hj => Nat.find_min hex hj⟩
  obtain ⟨hwkQ, hwkΦ, hwk1, hwk2, hwk3, hwk4, hwk5⟩ := hmain k hkK
  refine ⟨k, F^[k] z, hwkQ, hwkΦ, ?_, ?_, ?_⟩
  · -- the real part lies in the column
    refine ⟨hkre, ?_⟩
    by_cases hk0 : k = 0
    · rw [hk0]
      simp only [Function.iterate_zero, id_eq]
      linarith only [hzre]
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hkl : k - 1 < k := Nat.sub_one_lt hk0
      have hklK : k - 1 < K := lt_of_lt_of_le hkl hkK
      have hprev : (F^[k - 1] z).re < x₀ - 3 := by
        by_contra hcon
        push_neg at hcon
        exact hkmin (k - 1) hkl ⟨le_of_lt hklK, hcon⟩
      obtain ⟨hpQ, -, -, -, hp3, hp4, -⟩ := hmain (k - 1) (le_of_lt hklK)
      obtain ⟨-, -, -, -, hs2', -, -, -⟩ := hstep (k - 1) hklK hpQ hp3 hp4
      have hsub : k - 1 + 1 = k := Nat.sub_add_cancel hk1
      have hs2'' : (F^[k] z).re ≤ (F^[k - 1] z).re + 67 / 64 := by
        have := hs2'
        rwa [hsub] at this
      linarith only [hs2'', hprev]
  · -- the height
    have h2 : (k : ℝ) * (3 / 64) ≤ (x₀ - z.re) / 2 + 1 := by
      have h3 : (k : ℝ) ≤ (K : ℝ) := Nat.cast_le.mpr hkK
      have h4 : (k : ℝ) ≤ (7 / 6) * R₀ + 3 := le_trans h3 hKub
      have h5 : (x₀ - z.re) / 2 + 1 = R₀ / 2 + 1 := by rw [hR₀]
      rw [h5]
      exact aux_small3 h4 hR₀ge
    linarith only [hwk3, h2]
  · -- the accumulated drift
    have hk3 : (k : ℝ) ≤ 3 * H := le_trans (Nat.cast_le.mpr hkK) hK3H
    have h1 : (k : ℝ) * ε ≤ 3 * H * ε := by
      have := mul_le_mul_of_nonneg_right hk3 hε0
      linarith
    have h2 : 3 * H * ε ≤ 1 / 64 := by
      rw [hε]
      exact drift_geom_small hM hκ hdrC
    linarith only [hwk5, h1, h2]

theorem walk_left_drift {Ξ : ℝ} {α ρ : ℂ} {M κ Y : ℝ} {F Φ : ℂ → ℂ}
    (hM : 0 < M) (hκ : 0 < κ) (hρ : ‖ρ - 1‖ ≤ 1 / 32)
    (hfwd : ∀ z ∈ Work.Pert.Qm Ξ α, 1 + 1 / 8 ≤ Work.Pert.margB_g Ξ z →
      F z ∈ Work.Pert.Qm Ξ α ∧ Φ (F z) = Φ z + 1)
    (hdec : ∀ w ∈ Work.Pert.Qm Ξ α, w.im < -Y →
      ‖F w - (w + ρ)‖ ≤ M * Real.exp (κ * w.im)) :
    ∃ Y₂ : ℝ, ∀ z ∈ Work.Pert.Qm Ξ α, z.im ≤ -Y₂ → z.re ≤ -2 →
      ∃ w : ℂ, w ∈ Work.Pert.Qm Ξ α ∧ w.re ∈ Set.Icc (-2) 0 ∧
        ‖(Φ w - w / ρ) - (Φ z - z / ρ)‖ ≤ 1 ∧ w.im ≤ z.im + |z.re| / 2 + 2 := by
  obtain ⟨Y₂, hY₂⟩ := walk_left_column (x₀ := 1) hM hκ hρ hfwd hdec
  refine ⟨Y₂, ?_⟩
  intro z hzQ hzim hzre
  obtain ⟨k, w, hwQ, hΦw, hwre, hwim, hdrift⟩ := hY₂ z hzQ hzim (by linarith)
  refine ⟨w, hwQ, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hwre
    exact ⟨by linarith, by linarith⟩
  · exact drift_quotient_le hρ hΦw hdrift
  · have hzabs : |z.re| = -z.re := abs_of_nonpos (by linarith)
    rw [hzabs]
    linarith only [hwim]

end Work.Pert.pert2v2
