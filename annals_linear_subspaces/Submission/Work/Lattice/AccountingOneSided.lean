import Mathlib
import Submission.Commons.Analysis.Real.sum_prefix_le_mul
import Submission.Work.Lattice.PositionData

/-!
# de Saxcé's Lemma 4: the block accounting, and what it really needs

The paper's Lemma 4 is the identity

    `⟨ċ_t, c_t⟩ = −(1/ℓ + 1/(d−ℓ)) · Σ_s (ℓ_{s+1} − ℓ_s)·Λ^{(s)}`,

used at a "good time" (`⟨ċ_t,c_t⟩ ≥ −1`) to bound the weighted sum of the polygon slopes

    `S := Σ_s (ℓ_{s+1} − ℓ_s)·Λ^{(s)}`

(`ℓ_s` = the *capacities*, i.e. the number of vectors the Prop-5 construction extracts at the
`s`-th flag member; `Λ^{(s)}` = the slopes of the Grayson polygon of the flowed lattice),
which in turn bounds the `k`-prefix wedge `‖v_1 ∧ … ∧ v_k‖` of the Prop-5 family.

## What is proved here (pure algebra, no analysis)

Let `jb` be the angular ranks (`jb 0 = 0`, `jb R = d`), `ω` the positions of the flag members
(`ω 0 = 0`, `ω R = ℓ`), `Λ` the block slopes, `r s := ċ_t(jb s)` the *level* derivatives
(`r 0 = r R = 0`, since `c_t(0) = c_t(d) = 0` for a unimodular flow lattice), and let

    `σ s := jb s/(d−ℓ) − rate·ω s = sigPos d (jb s) ℓ (ω s)`,   `rate = 1/ℓ + 1/(d−ℓ)`

be the flow rate of the position `ω s` (`Submission.PositionData.sigPos`).  Then, using only the
Abel identities and the *closure* `Σ_s Λ s·(jb (s+1) − jb s) = 0` (unimodularity),

* **`lemma4_identity`** — the exact identity

      `S = rate⁻¹·Σ_s (σ (s+1) − r (s+1))·(Λ (s+1) − Λ s) − rate⁻¹·Σ_s Λ s·(r (s+1) − r s)`.

  Note `Σ_s Λ s·(r (s+1) − r s) = ⟨ċ_t,c_t⟩` (`= ½ d/dt Σ_i Λ_i²`, the energy derivative).  So
  the paper's Lemma 4 is the *case `r s = σ s`* of this identity, while the general case carries
  the **defect** `Σ_s (σ − r)·ΔΛ_s`.
* **`lemma4_one_sided`** — if the slopes are nondecreasing and `σ s ≤ r s` at every flag member,
  then the defect is `≤ 0` and `S ≤ −rate⁻¹·⟨ċ,c⟩`; at a good time, `S ≤ rate⁻¹`.  (This is the
  direction needed to bound the wedge.)
* **`accounting_le_rate_inv`** — the packaged good-time form:
  `S ≤ ℓ(d−ℓ)/d`.
* `lemma4_ge_of_le_sigPos` — the *other* direction: if only `r s ≤ σ s` is known (which is what
  the flow gives for free — a member flows into `Λ_{t+h}`), one gets the *lower* bound
  `S ≥ −rate⁻¹·⟨ċ,c⟩`.  This shows that the upper bound genuinely needs the *equality*
  `r s = σ s` (equivalently `σ s ≤ r s`), i.e. that the flag member's covolume grows at its
  top-block rate — the point recorded in the roadmap for the remaining §3 work.

Module `Submission.Work.Lattice.AccountingOneSided`, namespace `Submission.AccountingOneSided`.
-/

noncomputable section

open Set Real Module
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Submission.AccountingOneSided

open Submission.PositionData
open Submission.FlowRateAsymptotic

variable {d : ℕ}

/-- The flow rate as its explicit two-denominator expression. -/
theorem slope_eq_explicit (ℓ : ℕ) :
    slope (d := d) ℓ = 1 / (ℓ : ℝ) + 1 / ((d : ℝ) - (ℓ : ℝ)) := rfl

/-- **Abel summation (forward form).** -/
lemma abel_forward (x y : ℕ → ℝ) (n : ℕ) :
    ∑ s ∈ Finset.range n, (x (s + 1) - x s) * y s =
      x n * y n - x 0 * y 0 - ∑ s ∈ Finset.range n, x (s + 1) * (y (s + 1) - y s) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      ring

/-- The flow rate is positive. -/
theorem rate_pos {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) : 0 < slope (d := d) ℓ := by
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
  have hdR : (0 : ℝ) < (d : ℝ) - (ℓ : ℝ) := by
    have : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
    linarith
  rw [slope_eq_explicit (d := d) ℓ]
  positivity

/-- **The exact Lemma-4 identity.**

With the flag data (`jb` the angular ranks, `ω` the positions, `Λ` the block slopes, `r` the level
derivatives) and the closure `Σ_s Λ s·(jb (s+1) − jb s) = 0`:

    `S = rate⁻¹·Σ_s (σ (s+1) − r (s+1))·ΔΛ_s − rate⁻¹·Σ_s Λ s·Δr_s`,

where `σ s = jb s/(d−ℓ) − rate·ω s` is the flow rate of the position `ω s` and
`ΔΛ_s = Λ (s+1) − Λ s`, `Δr_s = r (s+1) − r s`. -/
theorem lemma4_identity {ℓ R : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hR : 0 < R)
    (jb ω Λ r : ℕ → ℝ) (hjb0 : jb 0 = 0) (hjbR : jb R = (d : ℝ))
    (hω0 : ω 0 = 0) (hωR : ω R = (ℓ : ℝ))
    (hclosed : ∑ s ∈ Finset.range R, Λ s * (jb (s + 1) - jb s) = 0)
    (hr0 : r 0 = 0) (hrR : r R = 0) :
    ∑ s ∈ Finset.range R, (ω (s + 1) - ω s) * Λ s =
      (1 / slope (d := d) ℓ) *
          (∑ s ∈ Finset.range R,
            (jb (s + 1) / ((d : ℝ) - (ℓ : ℝ)) - slope (d := d) ℓ * ω (s + 1) - r (s + 1)) *
              (Λ (s + 1) - Λ s))
        - (1 / slope (d := d) ℓ) *
          (∑ s ∈ Finset.range R, Λ s * (r (s + 1) - r s)) := by
  classical
  set rate : ℝ := slope (d := d) ℓ with hrate
  have hrate0 : 0 < rate := rate_pos (d := d) hℓ0 hℓd
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
  have hdR : (0 : ℝ) < (d : ℝ) := lt_trans hℓR (by exact_mod_cast hℓd)
  have hdm : (0 : ℝ) < (d : ℝ) - (ℓ : ℝ) := by
    have : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
    linarith
  have hA := abel_forward ω Λ R
  have hB := abel_forward jb Λ R
  have hC := abel_forward r Λ R
  -- closure in `ΔΛ` form
  have hclos : ∑ s ∈ Finset.range R, jb (s + 1) * (Λ (s + 1) - Λ s) = (d : ℝ) * Λ R := by
    have h := hB
    simp only [hjb0, hjbR, zero_mul, sub_zero] at h
    have h0 : ∑ s ∈ Finset.range R, (jb (s + 1) - jb s) * Λ s = 0 := by
      rw [← hclosed]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    rw [h0] at h
    linarith
  -- the `r`-sum in `ΔΛ` form
  have hrsum : ∑ s ∈ Finset.range R, r (s + 1) * (Λ (s + 1) - Λ s) =
      -∑ s ∈ Finset.range R, Λ s * (r (s + 1) - r s) := by
    have h := hC
    simp only [hrR, hr0, zero_mul, sub_zero] at h
    have h' : ∑ s ∈ Finset.range R, r (s + 1) * (Λ (s + 1) - Λ s) =
        -∑ s ∈ Finset.range R, (r (s + 1) - r s) * Λ s := by linarith [h]
    rw [h']
    congr 1
    exact Finset.sum_congr rfl (fun s _ => by ring)
  -- split the defect sum
  have hsplit : ∑ s ∈ Finset.range R,
        (jb (s + 1) / ((d : ℝ) - (ℓ : ℝ)) - rate * ω (s + 1) - r (s + 1)) *
          (Λ (s + 1) - Λ s) =
      (1 / ((d : ℝ) - (ℓ : ℝ))) *
          (∑ s ∈ Finset.range R, jb (s + 1) * (Λ (s + 1) - Λ s))
        - rate * (∑ s ∈ Finset.range R, ω (s + 1) * (Λ (s + 1) - Λ s))
        - (∑ s ∈ Finset.range R, r (s + 1) * (Λ (s + 1) - Λ s)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    ring
  -- the arithmetic identity `rate·(d−ℓ) = d/ℓ`
  have hrate_eq : rate * ((d : ℝ) - (ℓ : ℝ)) = (d : ℝ) / (ℓ : ℝ) := by
    rw [hrate, slope_eq_explicit (d := d) ℓ]
    field_simp
    ring
  rw [hA]
  simp only [hω0, hωR, zero_mul, sub_zero]
  rw [hsplit, hclos, hrsum]
  have hr : rate ≠ 0 := ne_of_gt hrate0
  have hd' : (d : ℝ) - (ℓ : ℝ) ≠ 0 := ne_of_gt hdm
  have hℓ' : (ℓ : ℝ) ≠ 0 := ne_of_gt hℓR
  have h4' : (ℓ : ℝ) * (rate * ((d : ℝ) - (ℓ : ℝ))) = (d : ℝ) := by
    rw [hrate_eq]; field_simp
  field_simp
  linear_combination (Λ R) * h4'

/-! ## The effective capacities and the accounting theorem

The *capacities* of the Prop-5 construction are not the positions `ω_s` of the flag members but
the **effective positions** determined by the level derivatives: at the angular rank `jb s` the
member's covolume grows at rate `≈ r s := ċ_t(jb s)`, and the number of vectors extracted there is

    `effPos s := (jb s/(d−ℓ) − r s)/rate`     (`rate = 1/ℓ + 1/(d−ℓ)`),

i.e. the number `c` with `sigPos d (jb s) ℓ c = r s`.  With this choice the *defect*
`σ s − r s` of `lemma4_identity` vanishes identically, so the accounting becomes unconditional:

* `effPos_zero`, `effPos_top` — the capacities at the endpoints are `0` and `ℓ` (so
  `Σ_s Δ effPos_s = ℓ`: the construction extracts exactly `ℓ` vectors);
* `sigPos_effPos` — `sigPos` of the effective position is the level derivative;
* `sum_effPos_mul_eq` — **the paper's Lemma 4** as an identity:
  `Σ_s Δ effPos_s · Λ_s = −rate⁻¹ · Σ_s Λ_s·Δr_s = −rate⁻¹·⟨ċ_t,c_t⟩`;
* `sum_delta_mul_le_of_le` — passing to the running maximum `ω' ≥ ω` (with `ω' 0 = ω 0 = 0`,
  `ω' R = ω R = ℓ`) can only decrease the weighted sum (for nondecreasing slopes):
  `Σ_s Δω'_s·Λ_s ≤ Σ_s Δω_s·Λ_s` (the paper's `ℓ'_s = max_{i≤s}ℓ_i` step);
* `accounting_le_rate_inv` — the good-time conclusion `Σ_s Δω_s Λ_s ≤ ℓ(d−ℓ)/d`.
-/

/-- The **effective position** (capacity) attached to the level derivative `r t` at the angular
rank `jb t`: the number `c` with `sigPos d (jb t) ℓ c = r t`. -/
noncomputable def effPos (d ℓ : ℕ) (jb r : ℕ → ℝ) (t : ℕ) : ℝ :=
  (jb t / ((d : ℝ) - (ℓ : ℝ)) - r t) / slope (d := d) ℓ

theorem effPos_apply {ℓ : ℕ} (jb r : ℕ → ℝ) (t : ℕ) :
    effPos d ℓ jb r t = (jb t / ((d : ℝ) - (ℓ : ℝ)) - r t) / slope (d := d) ℓ := rfl

theorem effPos_zero {ℓ : ℕ} {jb r : ℕ → ℝ} (hjb0 : jb 0 = 0) (hr0 : r 0 = 0) :
    effPos d ℓ jb r 0 = 0 := by
  rw [effPos_apply, hjb0, hr0]
  simp

/-- The capacity at the top: the full lattice (rank `d`, level derivative `0`) has capacity
`ℓ`. -/
theorem effPos_top {ℓ R : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {jb r : ℕ → ℝ}
    (hjbR : jb R = (d : ℝ)) (hrR : r R = 0) :
    effPos d ℓ jb r R = (ℓ : ℝ) := by
  have hdm : (0 : ℝ) < (d : ℝ) - (ℓ : ℝ) := by
    have : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
    linarith
  have hrate0 : 0 < slope (d := d) ℓ := rate_pos (d := d) hℓ0 hℓd
  have hrate_eq : slope (d := d) ℓ * ((d : ℝ) - (ℓ : ℝ)) = (d : ℝ) / (ℓ : ℝ) := by
    rw [slope_eq_explicit (d := d) ℓ]
    field_simp
    ring
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
  have hden : ((d : ℝ) - (ℓ : ℝ)) * slope (d := d) ℓ = (d : ℝ) / (ℓ : ℝ) := by
    rw [mul_comm]; exact hrate_eq
  have hd_ne : (d : ℝ) ≠ 0 := by
    have : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
    linarith [hℓR]
  rw [effPos_apply, hjbR, hrR, sub_zero, div_div, hden]
  field_simp

/-- `sigPos` of the effective position is the level derivative (by construction). -/
theorem sigPos_effPos {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (jb r : ℕ → ℝ) (t : ℕ) :
    jb t / ((d : ℝ) - (ℓ : ℝ)) - slope (d := d) ℓ * effPos d ℓ jb r t = r t := by
  have hrate0 : 0 < slope (d := d) ℓ := rate_pos (d := d) hℓ0 hℓd
  rw [effPos_apply, mul_div_cancel₀ _ hrate0.ne']
  ring

/-- **Lemma 4 with the effective capacities**: with `ω_s := effPos s`, the weighted slope sum is
exactly `−rate⁻¹·⟨ċ_t,c_t⟩`. -/
theorem sum_effPos_mul_eq {ℓ R : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hR : 0 < R)
    (jb r Λ : ℕ → ℝ) (hjb0 : jb 0 = 0) (hjbR : jb R = (d : ℝ))
    (hr0 : r 0 = 0) (hrR : r R = 0)
    (hclosed : ∑ s ∈ Finset.range R, Λ s * (jb (s + 1) - jb s) = 0) :
    ∑ s ∈ Finset.range R, (effPos d ℓ jb r (s + 1) - effPos d ℓ jb r s) * Λ s =
      -(1 / slope (d := d) ℓ) * ∑ s ∈ Finset.range R, Λ s * (r (s + 1) - r s) := by
  have hid := lemma4_identity (d := d) (ℓ := ℓ) hℓ0 hℓd hR jb (fun t => effPos d ℓ jb r t) Λ r
    hjb0 hjbR (effPos_zero (d := d) (ℓ := ℓ) hjb0 hr0)
    (effPos_top (d := d) (ℓ := ℓ) hℓ0 hℓd hjbR hrR) hclosed hr0 hrR
  rw [hid]
  have hzero : ∑ s ∈ Finset.range R,
      (jb (s + 1) / ((d : ℝ) - (ℓ : ℝ)) - slope (d := d) ℓ * effPos d ℓ jb r (s + 1) -
        r (s + 1)) * (Λ (s + 1) - Λ s) = 0 := by
    refine Finset.sum_eq_zero (fun s _ => ?_)
    rw [sigPos_effPos (d := d) hℓ0 hℓd jb r (s + 1)]
    ring
  rw [hzero, mul_zero, zero_sub]
  ring

/-- **The running-maximum step.**  If `ω' ≥ ω` with `ω' 0 = ω 0 = 0` and `ω' R = ω R`, and the
slopes are nondecreasing, then `Σ_s Δω'_s·Λ_s ≤ Σ_s Δω_s·Λ_s`. -/
theorem sum_delta_mul_le_of_le {R : ℕ} {ω ω' Λ : ℕ → ℝ} (hω0 : ω 0 = 0) (hω'0 : ω' 0 = 0)
    (hωR : ω R = ω' R) (hle : ∀ s : ℕ, s ≤ R → ω s ≤ ω' s) (hmono : Monotone Λ) :
    ∑ s ∈ Finset.range R, (ω' (s + 1) - ω' s) * Λ s ≤
      ∑ s ∈ Finset.range R, (ω (s + 1) - ω s) * Λ s := by
  rw [abel_forward ω' Λ R, abel_forward ω Λ R, hω0, hω'0, hωR]
  simp only [zero_mul, sub_zero]
  have h1 : ∑ s ∈ Finset.range R, ω (s + 1) * (Λ (s + 1) - Λ s) ≤
      ∑ s ∈ Finset.range R, ω' (s + 1) * (Λ (s + 1) - Λ s) := by
    refine Finset.sum_le_sum (fun s hs => ?_)
    have hsR : s < R := Finset.mem_range.mp hs
    have hΔ : 0 ≤ Λ (s + 1) - Λ s := by
      have := hmono (Nat.le_succ s)
      linarith
    exact mul_le_mul_of_nonneg_right (hle (s + 1) (Nat.succ_le_of_lt hsR)) hΔ
  linarith

/-- `ℓ(d−ℓ)/d = 1/rate`. -/
theorem rate_inv_eq {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) :
    1 / slope (d := d) ℓ = (ℓ : ℝ) * ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) := by
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
  have hdR : (0 : ℝ) < (d : ℝ) := lt_trans hℓR (by exact_mod_cast hℓd)
  have hdmR : (0 : ℝ) < (d : ℝ) - (ℓ : ℝ) := by
    have : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
    linarith
  rw [slope_eq_explicit (d := d) ℓ]
  field_simp
  ring

/-- **The accounting theorem.**  At a "good time" (i.e. `⟨ċ_t,c_t⟩ = Σ_s Λ_s·Δr_s ≥ −1`), the
weighted slope sum computed with the *effective capacities* `effPos` is bounded by the constant
`ℓ(d−ℓ)/d = 1/rate`:

    `Σ_s (effPos (s+1) − effPos s)·Λ_s ≤ ℓ(d−ℓ)/d`. -/
theorem accounting_le_rate_inv {ℓ R : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hR : 0 < R)
    (jb r Λ : ℕ → ℝ) (hjb0 : jb 0 = 0) (hjbR : jb R = (d : ℝ))
    (hr0 : r 0 = 0) (hrR : r R = 0)
    (hclosed : ∑ s ∈ Finset.range R, Λ s * (jb (s + 1) - jb s) = 0)
    (hgood : -1 ≤ ∑ s ∈ Finset.range R, Λ s * (r (s + 1) - r s)) :
    ∑ s ∈ Finset.range R, (effPos d ℓ jb r (s + 1) - effPos d ℓ jb r s) * Λ s ≤
      (ℓ : ℝ) * ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) := by
  have hid := sum_effPos_mul_eq (d := d) (ℓ := ℓ) hℓ0 hℓd hR jb r Λ hjb0 hjbR hr0 hrR hclosed
  have hpos : 0 < slope (d := d) ℓ := rate_pos (d := d) hℓ0 hℓd
  have h2 : -(1 / slope (d := d) ℓ) * ∑ s ∈ Finset.range R, Λ s * (r (s + 1) - r s)
      ≤ 1 / slope (d := d) ℓ := by
    have h1 : -(1 / slope (d := d) ℓ) ≤ 0 := by
      have h3 : 0 < 1 / slope (d := d) ℓ := by positivity
      linarith
    calc -(1 / slope (d := d) ℓ) * ∑ s ∈ Finset.range R, Λ s * (r (s + 1) - r s)
        ≤ -(1 / slope (d := d) ℓ) * (-1) := mul_le_mul_of_nonpos_left hgood h1
      _ = 1 / slope (d := d) ℓ := by ring
  have h3 := rate_inv_eq (d := d) hℓ0 hℓd
  linarith [hid, h2, h3]


end Submission.AccountingOneSided

end
