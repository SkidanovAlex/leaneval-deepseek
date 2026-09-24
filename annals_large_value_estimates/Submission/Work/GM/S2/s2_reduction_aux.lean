import Mathlib
import Submission.Work.GM.S2.Defs
import Submission.Work.GM.S2.pair_sum_defs
import Submission.Work.GM.S2.norm_Sall_le
import Submission.Work.GM.S2.hhat_neg_symm
import Submission.Work.GM.S2.hhat_sum_tail
import Submission.Work.GM.Trace.Iterm_zero_bound
import Submission.Work.GM.Trace.hhat_norm_le_Azero
import Submission.Work.GM.Trace.hhat_zero_decay
import Submission.Work.GM.Trace.summable_Iterm
import Submission.Work.GM.S3.Iterm_summable
import Submission.Work.GM.Trace.trace_three_identity
import Submission.Work.GM.S2.exists_nat_rpow_neg_mul_le

/-!
# The `S₂` reduction (GM §6, the identity `S₂ = 3N³ĥ₀(0)Σ|Σ_m ĥ|² + O(T^{-10})`)

This file proves `Work.GM.S2.s2_reduction_aux`: from the two decay estimates for
`ĥ_t(ξ) = ∫ w(u)² u^{it} e(-ξu) du` (GM Lemma 4.3) one gets, uniformly in
`N ≥ N₀`, `W ⊆ [0, N^{6/5}]` a `(N^{6/5})^ε`-separated finite set,

`‖S₂‖ ≤ C N³ ‖ĥ_0(0)‖ Σ_{t₁,t₂∈W} |Σ_{m ≠ 0} ĥ_{t₁-t₂}(mN)|² + (N^{6/5})^{-10}`.

The identity (`S₂` = sum over `m` with exactly two non-zero coordinates) is split
according to which coordinate vanishes; each of the three pieces factorises as
`N³ Σ_{t₁,t₂,t₃} ĥ(t₁-t₂,0) · Σ_m ĥ(t₂-t₃,mN) · Σ_m ĥ(t₃-t₁,mN)`, whose "diagonal"
`t₁ = t₂` contributes `N³ ĥ₀(0) Σ_{t₂,t₃} |Σ_m ĥ(t₂-t₃,mN)|²` and whose off-diagonal
is `≪ N³ T^{-εj} |W|² Σ_{t₁,t₂} |Σ_m ĥ|²`, negligible for `j` large.
-/

namespace Work.GM.S2

open Complex Finset
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

/-! ## 0. The pieces -/

/-- `ĥ_d(mN)` as a function of the integer `m`. -/
noncomputable def Phi (N : ℕ) (d : ℝ) : ℤ → ℂ := fun q => Submission.GM.hhat d ((q : ℝ) * (N : ℝ))

/-- The pair sum that appears on the right-hand side of the reduction. -/
noncomputable def Rpair (N : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ t1 ∈ W, ∑ t2 ∈ W, ‖Sall N (t1 - t2)‖ ^ 2

/-- The part of `S₂` with `m₁ = 0`, `m₂, m₃ ≠ 0`. -/
noncomputable def Bg1 (N : ℕ) (W : Finset ℝ) : ℂ :=
  ∑' (m : ℤ × ℤ × ℤ),
    (if m.1 = 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0 then Submission.GM.Iterm N W m else 0)

/-- The part of `S₂` with `m₂ = 0`, `m₁, m₃ ≠ 0`. -/
noncomputable def Bg2 (N : ℕ) (W : Finset ℝ) : ℂ :=
  ∑' (m : ℤ × ℤ × ℤ),
    (if m.1 ≠ 0 ∧ m.2.1 = 0 ∧ m.2.2 ≠ 0 then Submission.GM.Iterm N W m else 0)

/-- The part of `S₂` with `m₃ = 0`, `m₁, m₂ ≠ 0`. -/
noncomputable def Bg3 (N : ℕ) (W : Finset ℝ) : ℂ :=
  ∑' (m : ℤ × ℤ × ℤ),
    (if m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 = 0 then Submission.GM.Iterm N W m else 0)

/-! ## 1. Summability of the one-dimensional families -/

lemma summable_hhat_int_norm (hxi : DecHyp) (N : ℕ) (hN : 1 ≤ N) (d : ℝ) :
    Summable (fun m : ℤ => ‖Submission.GM.hhat d ((m : ℝ) * (N : ℝ))‖) := by
  obtain ⟨C, hCpos, hC⟩ := hxi 2
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hbase : Summable (fun m : ℤ => ((|(m : ℝ)| : ℝ) ^ 2)⁻¹) :=
    summable_int_abs_pow_inv (le_refl 2)
  have h0 : Summable (fun m : ℤ => (if m = 0 then Work.GM.Trace.Azero else 0)) :=
    summable_of_ne_finset_zero (s := {0}) (by intro b hb; simp at hb; simp [hb])
  have hs : Summable (fun m : ℤ => (if m = 0 then Work.GM.Trace.Azero else 0)
      + C * (1 + |d|) ^ 2 * ((|(m : ℝ)| : ℝ) ^ 2)⁻¹) :=
    h0.add (hbase.mul_left (C * (1 + |d|) ^ 2))
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hs
  by_cases hm : m = 0
  · subst hm
    have hz : ((|(((0:ℤ)) : ℝ)|)^2)⁻¹ = (0:ℝ) := by norm_num
    rw [if_pos rfl, hz, mul_zero, add_zero]
    rw [show (((0:ℤ)) : ℝ) * (N:ℝ) = 0 by norm_num]
    exact Work.GM.Trace.hhat_norm_le_Azero d 0
  · have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm
    have hξne : (m:ℝ) * (N:ℝ) ≠ 0 := mul_ne_zero hmR (ne_of_gt hNpos)
    have hb := hC d ((m:ℝ)*(N:ℝ)) hξne
    rw [if_neg hm, zero_add]
    have habs : |(m:ℝ)*(N:ℝ)| = |(m:ℝ)| * (N:ℝ) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (N:ℝ))]
    have hle : |(m:ℝ)| ≤ |(m:ℝ)*(N:ℝ)| := by
      rw [habs]; nlinarith [abs_nonneg (m:ℝ), hN1]
    have hle2 : ((|(m:ℝ)|)^2) ≤ ((|(m:ℝ)*(N:ℝ)|)^2) := pow_le_pow_left₀ (abs_nonneg _) hle 2
    have hpos : (0:ℝ) < ((|(m:ℝ)|)^2) := by positivity
    calc ‖Submission.GM.hhat d ((m:ℝ)*(N:ℝ))‖
        ≤ C * (1+|d|)^2 / |(m:ℝ)*(N:ℝ)|^2 := hb
      _ = C * (1+|d|)^2 * ((|(m:ℝ)*(N:ℝ)|)^2)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ C * (1+|d|)^2 * ((|(m:ℝ)|)^2)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ hpos hle2) (by positivity)

lemma summable_hhat_int (hxi : DecHyp) (N : ℕ) (hN : 1 ≤ N) (d : ℝ) :
    Summable (fun m : ℤ => Submission.GM.hhat d ((m : ℝ) * (N : ℝ))) :=
  (summable_hhat_int_norm hxi N hN d).of_norm

/-- The triple product majorant is summable on `ℤ³`. -/
lemma summable_triple_norm (hxi : DecHyp) (N : ℕ) (hN : 1 ≤ N) (d1 d2 d3 : ℝ) :
    Summable (fun m : ℤ × ℤ × ℤ =>
      ‖Submission.GM.hhat d1 ((m.1:ℝ) * (N:ℝ))‖ *
      (‖Submission.GM.hhat d2 ((m.2.1:ℝ) * (N:ℝ))‖ *
       ‖Submission.GM.hhat d3 ((m.2.2:ℝ) * (N:ℝ))‖)) := by
  have h1 : Summable (fun m : ℤ => ‖Submission.GM.hhat d1 ((m:ℝ) * (N:ℝ))‖) :=
    summable_hhat_int_norm hxi N hN d1
  have h2 : Summable (fun m : ℤ => ‖Submission.GM.hhat d2 ((m:ℝ) * (N:ℝ))‖) :=
    summable_hhat_int_norm hxi N hN d2
  have h3 : Summable (fun m : ℤ => ‖Submission.GM.hhat d3 ((m:ℝ) * (N:ℝ))‖) :=
    summable_hhat_int_norm hxi N hN d3
  have h23 : Summable (fun q : ℤ × ℤ =>
      ‖Submission.GM.hhat d2 ((q.1:ℝ) * (N:ℝ))‖ * ‖Submission.GM.hhat d3 ((q.2:ℝ) * (N:ℝ))‖) :=
    Summable.mul_of_nonneg (f := fun m : ℤ => ‖Submission.GM.hhat d2 ((m:ℝ) * (N:ℝ))‖)
      (g := fun m : ℤ => ‖Submission.GM.hhat d3 ((m:ℝ) * (N:ℝ))‖)
      h2 h3 (fun q => norm_nonneg _) (fun q => norm_nonneg _)
  exact Summable.mul_of_nonneg (f := fun m : ℤ => ‖Submission.GM.hhat d1 ((m:ℝ) * (N:ℝ))‖)
    (g := fun q : ℤ × ℤ => ‖Submission.GM.hhat d2 ((q.1:ℝ) * (N:ℝ))‖ * ‖Submission.GM.hhat d3 ((q.2:ℝ) * (N:ℝ))‖)
    h1 h23 (fun q => norm_nonneg _) (fun q => by positivity)

/-! ## 2. The guard factorisation -/

/-- Summability of the guarded triple product on `ℤ³`. -/
lemma summable_guard_prod (hxi : DecHyp) (N : ℕ) (hN : 1 ≤ N) (d1 d2 d3 : ℝ)
    (b : ℤ × ℤ × ℤ → Prop) [DecidablePred b] :
    Summable (fun m : ℤ × ℤ × ℤ =>
      (if b m then Phi N d1 m.1 * Phi N d2 m.2.1 * Phi N d3 m.2.2 else 0)) := by
  refine Summable.of_norm_bounded
    (g := fun m : ℤ × ℤ × ℤ =>
      ‖Submission.GM.hhat d1 ((m.1:ℝ) * (N:ℝ))‖ *
      (‖Submission.GM.hhat d2 ((m.2.1:ℝ) * (N:ℝ))‖ *
       ‖Submission.GM.hhat d3 ((m.2.2:ℝ) * (N:ℝ))‖))
    (summable_triple_norm hxi N hN d1 d2 d3) (fun m => ?_)
  by_cases h : b m
  · rw [if_pos h]
    refine le_of_eq ?_
    simp only [Phi, norm_mul, mul_assoc]
  · rw [if_neg h, norm_zero]
    positivity

lemma tsum_guard_fst_aux (f1 f2 f3 : ℤ → ℂ)
    (h1 : Summable fun m : ℤ => ‖f1 m‖) (h2 : Summable fun m : ℤ => ‖f2 m‖)
    (h3 : Summable fun m : ℤ => ‖f3 m‖) :
    (∑' (m : ℤ × ℤ × ℤ),
        (if m.1 = 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0 then
          f1 m.1 * f2 m.2.1 * f3 m.2.2 else 0))
      = f1 0 * (∑' (m : {m : ℤ // m ≠ 0}), f2 (m : ℤ))
              * (∑' (m : {m : ℤ // m ≠ 0}), f3 (m : ℤ)) := by
  set g2 : ℤ → ℂ := fun q => if q = 0 then 0 else f2 q with hg2
  set g3 : ℤ → ℂ := fun q => if q = 0 then 0 else f3 q with hg3
  have hg2S : Summable (fun q : ℤ => ‖g2 q‖) := by
    refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_) h2
    by_cases h : q = 0 <;> simp [g2, h]
  have hg3S : Summable (fun q : ℤ => ‖g3 q‖) := by
    refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_) h3
    by_cases h : q = 0 <;> simp [g3, h]
  have hg2sub : (∑' (m : {m : ℤ // m ≠ 0}), f2 (m : ℤ)) = ∑' q : ℤ, g2 q := by
    conv_lhs => rw [show (∑' (m : {m : ℤ // m ≠ 0}), f2 (m : ℤ))
        = (∑' (m : {m : ℤ // m ≠ 0}), g2 (m : ℤ)) from
      tsum_congr (fun m => by simp [g2, m.2])]
    exact tsum_subtype_eq_of_support_subset
      (s := {m : ℤ | m ≠ 0}) (f := g2)
      (fun q hq => by
        by_cases hq0 : q = 0
        · exact absurd (by simp [g2, hq0]) hq
        · simpa using hq0)
  have hg3sub : (∑' (m : {m : ℤ // m ≠ 0}), f3 (m : ℤ)) = ∑' q : ℤ, g3 q := by
    conv_lhs => rw [show (∑' (m : {m : ℤ // m ≠ 0}), f3 (m : ℤ))
        = (∑' (m : {m : ℤ // m ≠ 0}), g3 (m : ℤ)) from
      tsum_congr (fun m => by simp [g3, m.2])]
    exact tsum_subtype_eq_of_support_subset
      (s := {m : ℤ | m ≠ 0}) (f := g3)
      (fun q hq => by
        by_cases hq0 : q = 0
        · exact absurd (by simp [g3, hq0]) hq
        · simpa using hq0)
  rw [hg2sub, hg3sub]
  -- step 1: iterated sum over `ℤ × (ℤ × ℤ)`
  have h23S : Summable (fun q : ℤ × ℤ => ‖f2 q.1‖ * ‖f3 q.2‖) :=
    Summable.mul_of_nonneg (f := fun q : ℤ => ‖f2 q‖) (g := fun q : ℤ => ‖f3 q‖)
      h2 h3 (fun q => norm_nonneg _) (fun q => norm_nonneg _)
  have hFsum : Summable (fun m : ℤ × (ℤ × ℤ) =>
      (if m.1 = 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0 then f1 m.1 * f2 m.2.1 * f3 m.2.2 else 0)) := by
    refine Summable.of_norm_bounded
      (g := fun m : ℤ × (ℤ × ℤ) => ‖f1 m.1‖ * (‖f2 m.2.1‖ * ‖f3 m.2.2‖))
      ?_ (fun m => ?_)
    · exact Summable.mul_of_nonneg (f := fun q : ℤ => ‖f1 q‖)
        (g := fun q : ℤ × ℤ => ‖f2 q.1‖ * ‖f3 q.2‖) h1 h23S
        (fun q => norm_nonneg _) (fun q => by positivity)
    · by_cases h : m.1 = 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0
      · rw [if_pos h]; refine le_of_eq ?_; simp only [norm_mul, mul_assoc]
      · rw [if_neg h, norm_zero]; positivity
  have hFsum' : ∀ b : ℤ, Summable (fun c : ℤ × ℤ =>
      (if b = 0 ∧ c.1 ≠ 0 ∧ c.2 ≠ 0 then f1 b * f2 c.1 * f3 c.2 else 0)) := by
    intro b
    refine Summable.of_norm_bounded
      (g := fun c : ℤ × ℤ => ‖f1 b‖ * (‖f2 c.1‖ * ‖f3 c.2‖))
      (Summable.mul_left _ h23S)
      (fun c => ?_)
    by_cases h : b = 0 ∧ c.1 ≠ 0 ∧ c.2 ≠ 0
    · rw [if_pos h]; refine le_of_eq ?_; simp only [norm_mul, mul_assoc]
    · rw [if_neg h, norm_zero]; positivity
  -- step 2: evaluate the inner sum
  have hinner : ∀ b : ℤ,
      (∑' c : ℤ × ℤ, (if b = 0 ∧ c.1 ≠ 0 ∧ c.2 ≠ 0 then f1 b * f2 c.1 * f3 c.2 else 0))
        = (if b = 0 then f1 b else 0) * (∑' c : ℤ × ℤ, g2 c.1 * g3 c.2) := by
    intro b
    rw [← tsum_mul_left]
    refine tsum_congr (fun c => ?_)
    by_cases h1' : b = 0 <;> by_cases h2' : c.1 = 0 <;> by_cases h3' : c.2 = 0 <;>
      simp [g2, g3, h1', h2', h3', mul_assoc]
  rw [Summable.tsum_prod' hFsum hFsum']
  rw [tsum_congr hinner]
  rw [tsum_congr (fun b => mul_comm _ _), tsum_mul_left, tsum_ite_eq]
  rw [← tsum_mul_tsum_of_summable_norm hg2S hg3S]
  ring


/-! ## 3. The guard factorisation, in the form used below -/

lemma tsum_guard_fst_Phi (hxi : DecHyp) (N : ℕ) (hN : 1 ≤ N) (d1 d2 d3 : ℝ) :
    (∑' (m : ℤ × ℤ × ℤ),
        (if m.1 = 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0 then
          Phi N d1 m.1 * Phi N d2 m.2.1 * Phi N d3 m.2.2 else 0))
      = Submission.GM.hhat d1 0 * Sall N d2 * Sall N d3 := by
  have h := tsum_guard_fst_aux (Phi N d1) (Phi N d2) (Phi N d3)
    (summable_hhat_int_norm hxi N hN d1) (summable_hhat_int_norm hxi N hN d2)
    (summable_hhat_int_norm hxi N hN d3)
  rw [h]
  have h0 : Phi N d1 0 = Submission.GM.hhat d1 0 := by simp [Phi]
  have h2 : (∑' (m : {m : ℤ // m ≠ 0}), Phi N d2 (m : ℤ)) = Sall N d2 := rfl
  have h3 : (∑' (m : {m : ℤ // m ≠ 0}), Phi N d3 (m : ℤ)) = Sall N d3 := rfl
  rw [h0, h2, h3]

/-- `(m₁,m₂,m₃) ↦ (m₂,m₃,m₁)`. -/
def shift2 : ℤ × ℤ × ℤ ≃ ℤ × ℤ × ℤ where
  toFun m := (m.2.1, m.2.2, m.1)
  invFun m := (m.2.2, m.1, m.2.1)
  left_inv m := by simp
  right_inv m := by simp

/-- `(m₁,m₂,m₃) ↦ (m₃,m₁,m₂)`. -/
def shift3 : ℤ × ℤ × ℤ ≃ ℤ × ℤ × ℤ where
  toFun m := (m.2.2, m.1, m.2.1)
  invFun m := (m.2.1, m.2.2, m.1)
  left_inv m := by simp
  right_inv m := by simp

lemma tsum_guard_snd_Phi (hxi : DecHyp) (N : ℕ) (hN : 1 ≤ N) (d1 d2 d3 : ℝ) :
    (∑' (m : ℤ × ℤ × ℤ),
        (if m.1 ≠ 0 ∧ m.2.1 = 0 ∧ m.2.2 ≠ 0 then
          Phi N d1 m.1 * Phi N d2 m.2.1 * Phi N d3 m.2.2 else 0))
      = Submission.GM.hhat d2 0 * Sall N d1 * Sall N d3 := by
  have h := tsum_guard_fst_Phi (hxi := hxi) (N := N) (hN := hN) (d1 := d2) (d2 := d3) (d3 := d1)
  have key : ∀ m : ℤ × ℤ × ℤ,
      (if m.1 ≠ 0 ∧ m.2.1 = 0 ∧ m.2.2 ≠ 0 then
          Phi N d1 m.1 * Phi N d2 m.2.1 * Phi N d3 m.2.2 else 0)
        = (if (shift2 m).1 = 0 ∧ (shift2 m).2.1 ≠ 0 ∧ (shift2 m).2.2 ≠ 0 then
            Phi N d2 (shift2 m).1 * Phi N d3 (shift2 m).2.1 * Phi N d1 (shift2 m).2.2
          else 0) := by
    intro m
    simp only [shift2]
    by_cases h1 : m.1 = 0 <;> by_cases h2 : m.2.1 = 0 <;> by_cases h3 : m.2.2 = 0 <;>
      simp [h1, h2, h3, and_comm, and_left_comm, and_assoc, mul_assoc, mul_comm, mul_left_comm]
  rw [tsum_congr key]
  rw [Equiv.tsum_eq shift2 (fun b : ℤ × ℤ × ℤ =>
      (if b.1 = 0 ∧ b.2.1 ≠ 0 ∧ b.2.2 ≠ 0 then
        Phi N d2 b.1 * Phi N d3 b.2.1 * Phi N d1 b.2.2 else 0))]
  rw [h]
  ring

lemma tsum_guard_thd_Phi (hxi : DecHyp) (N : ℕ) (hN : 1 ≤ N) (d1 d2 d3 : ℝ) :
    (∑' (m : ℤ × ℤ × ℤ),
        (if m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 = 0 then
          Phi N d1 m.1 * Phi N d2 m.2.1 * Phi N d3 m.2.2 else 0))
      = Submission.GM.hhat d3 0 * Sall N d1 * Sall N d2 := by
  have h := tsum_guard_fst_Phi (hxi := hxi) (N := N) (hN := hN) (d1 := d3) (d2 := d1) (d3 := d2)
  have key : ∀ m : ℤ × ℤ × ℤ,
      (if m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 = 0 then
          Phi N d1 m.1 * Phi N d2 m.2.1 * Phi N d3 m.2.2 else 0)
        = (if (shift3 m).1 = 0 ∧ (shift3 m).2.1 ≠ 0 ∧ (shift3 m).2.2 ≠ 0 then
            Phi N d3 (shift3 m).1 * Phi N d1 (shift3 m).2.1 * Phi N d2 (shift3 m).2.2
          else 0) := by
    intro m
    simp only [shift3]
    by_cases h1 : m.1 = 0 <;> by_cases h2 : m.2.1 = 0 <;> by_cases h3 : m.2.2 = 0 <;>
      simp [h1, h2, h3, and_comm, and_left_comm, and_assoc, mul_assoc, mul_comm, mul_left_comm]
  rw [tsum_congr key]
  rw [Equiv.tsum_eq shift3 (fun b : ℤ × ℤ × ℤ =>
      (if b.1 = 0 ∧ b.2.1 ≠ 0 ∧ b.2.2 ≠ 0 then
        Phi N d3 b.1 * Phi N d1 b.2.1 * Phi N d2 b.2.2 else 0))]
  rw [h]
  try ring


/-! ## 4. Summability of `Iterm` on `ℤ³` -/

lemma summable_Iterm_norm (hxi : DecHyp) (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ)
    (hW : ∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) :
    Summable (fun m : ℤ × ℤ × ℤ => ‖Submission.GM.Iterm N W m‖) := by
  obtain ⟨C, hCpos, hC⟩ := hxi 2
  have hCnn : 0 ≤ C := le_of_lt hCpos
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by positivity
  set T := Submission.LargeValues.M N with hT
  set K : ℝ := max Work.GM.Trace.Azero (C * (1 + T)^2) with hKdef
  have hKge : C * (1 + T)^2 ≤ K := by rw [hKdef]; exact le_max_right _ _
  have hKnn : 0 ≤ K := by
    rw [hKdef]; exact le_trans Work.GM.Trace.Azero_nonneg (le_max_left _ _)
  set β : ℤ → ℝ := fun m => if m = 0 then K else C * (1 + T)^2 * ((|(m:ℝ)|)^2)⁻¹ with hβdef
  have hβeq : β = fun m : ℤ => if m = 0 then K else C * (1 + T)^2 * ((|(m:ℝ)|)^2)⁻¹ := hβdef
  have hβval : ∀ m : ℤ, β m = (if m = 0 then K else C * (1 + T)^2 * ((|(m:ℝ)|)^2)⁻¹) :=
    fun m => by rw [hβeq]
  have hβn : ∀ m : ℤ, 0 ≤ β m := by
    intro m; rw [hβval m]; by_cases h : m = 0
    · rw [if_pos h]; exact hKnn
    · rw [if_neg h]; positivity
  have hβS : Summable β := by
    have h0 : Summable (fun m : ℤ => (if m = 0 then K else 0)) :=
      summable_of_ne_finset_zero (s := {0}) (by intro b hb; simp at hb; simp [hb])
    have h1 : Summable (fun m : ℤ => C * (1 + T)^2 * ((|(m:ℝ)|)^2)⁻¹) :=
      (summable_int_abs_pow_inv (le_refl 2)).mul_left _
    refine (h0.add h1).congr (fun m => ?_)
    rw [hβval m]
    by_cases h : m = 0 <;> simp [h]
  refine Work.GM.S3.Iterm_summable N W β hβn hβS ?_
  intro t s ht hs m
  have hTd : |t - s| ≤ T := by
    have h1 := (hW t ht).1; have h2 := (hW t ht).2
    have h3 := (hW s hs).1; have h4 := (hW s hs).2
    rw [abs_le]; constructor <;> linarith
  rw [hβval m]
  by_cases hm : m = 0
  · subst hm
    rw [if_pos rfl, hKdef]
    simp only [Int.cast_zero, zero_mul]
    exact (Work.GM.Trace.hhat_norm_le_Azero (t - s) 0).trans (le_max_left _ _)
  · rw [if_neg hm]
    have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm
    have hm1 : (1:ℝ) ≤ |(m:ℝ)| := by
      have h := Int.one_le_abs hm; rw [← Int.cast_abs]; exact_mod_cast h
    have hξne : (m:ℝ) * (N:ℝ) ≠ 0 := mul_ne_zero hmR (ne_of_gt hNpos)
    have hb := hC (t - s) ((m:ℝ) * (N:ℝ)) hξne
    have hfac : (1 + |t - s|)^2 ≤ (1 + T)^2 :=
      pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg (t - s)]) 2
    have hfacnn : (0:ℝ) ≤ C * (1 + T)^2 * ((|(m:ℝ)|)^2)⁻¹ := by positivity
    have habs : |(m:ℝ) * (N:ℝ)| = |(m:ℝ)| * (N:ℝ) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (N:ℝ))]
    have hξ2 : ((|(m:ℝ)|)^2) ≤ ((|(m:ℝ) * (N:ℝ)|)^2) := by
      rw [habs, mul_pow]
      have hN2 : (1:ℝ) ≤ (N:ℝ)^2 := by nlinarith [hN1]
      calc (|(m:ℝ)|)^2 = (|(m:ℝ)|)^2 * 1 := by ring
        _ ≤ (|(m:ℝ)|)^2 * (N:ℝ)^2 := mul_le_mul_of_nonneg_left hN2 (by positivity)
    have hξ2pos : (0:ℝ) < ((|(m:ℝ)|)^2) := by positivity
    calc ‖Submission.GM.hhat (t - s) ((m:ℝ) * (N:ℝ))‖
        ≤ C * (1 + |t-s|)^2 / |(m:ℝ) * (N:ℝ)|^2 := hb
      _ ≤ C * (1 + T)^2 / |(m:ℝ) * (N:ℝ)|^2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hfac hCnn
      _ = C * (1 + T)^2 * ((|(m:ℝ) * (N:ℝ)|)^2)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ C * (1 + T)^2 * ((|(m:ℝ)|)^2)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ hξ2pos hξ2) (by positivity)

lemma summable_guard_Iterm (hxi : DecHyp) (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ)
    (hW : ∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N))
    (b : ℤ × ℤ × ℤ → Prop) [DecidablePred b] :
    Summable (fun m : ℤ × ℤ × ℤ =>
      (if b m then Submission.GM.Iterm N W m else 0)) := by
  refine Summable.of_norm_bounded (summable_Iterm_norm hxi N hN W hW) (fun m => ?_)
  by_cases h : b m
  · simpa [if_pos h]
  · simp [if_neg h]

/-! ## 5. `S₂` splits into the three non-zero patterns -/

lemma spart_two_split (hxi : DecHyp) (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ)
    (hW : ∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) :
    Submission.GM.Spart 2 N W = Bg1 N W + Bg2 N W + Bg3 N W := by
  have hI := summable_Iterm_norm hxi N hN W hW
  have hs1 : Summable (fun m : ℤ × ℤ × ℤ =>
      (if m.1 = 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0 then Submission.GM.Iterm N W m else 0)) := by
    refine Summable.of_norm_bounded hI (fun m => ?_)
    by_cases h : m.1 = 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0
    · simp [if_pos h]
    · simp [if_neg h]
  have hs2 : Summable (fun m : ℤ × ℤ × ℤ =>
      (if m.1 ≠ 0 ∧ m.2.1 = 0 ∧ m.2.2 ≠ 0 then Submission.GM.Iterm N W m else 0)) := by
    refine Summable.of_norm_bounded hI (fun m => ?_)
    by_cases h : m.1 ≠ 0 ∧ m.2.1 = 0 ∧ m.2.2 ≠ 0
    · simp [if_pos h]
    · simp [if_neg h]
  have hs3 : Summable (fun m : ℤ × ℤ × ℤ =>
      (if m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 = 0 then Submission.GM.Iterm N W m else 0)) := by
    refine Summable.of_norm_bounded hI (fun m => ?_)
    by_cases h : m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 = 0
    · simp [if_pos h]
    · simp [if_neg h]
  have hpt : ∀ m : ℤ × ℤ × ℤ,
      (if Submission.GM.nzCount m = 2 then Submission.GM.Iterm N W m else 0)
        = (if m.1 = 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0 then Submission.GM.Iterm N W m else 0)
        + (if m.1 ≠ 0 ∧ m.2.1 = 0 ∧ m.2.2 ≠ 0 then Submission.GM.Iterm N W m else 0)
        + (if m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 = 0 then Submission.GM.Iterm N W m else 0) := by
    intro m
    unfold Submission.GM.nzCount
    by_cases h1 : m.1 = 0 <;> by_cases h2 : m.2.1 = 0 <;> by_cases h3 : m.2.2 = 0 <;>
      simp [h1, h2, h3]
  have hcoe : (∑' (m : {m : ℤ × ℤ × ℤ // Submission.GM.nzCount m = 2}), Submission.GM.Iterm N W m)
      = (∑' (m : ↑({m : ℤ × ℤ × ℤ | Submission.GM.nzCount m = 2})), Submission.GM.Iterm N W m) := rfl
  have hind : (∑' (m : ↑({m : ℤ × ℤ × ℤ | Submission.GM.nzCount m = 2})), Submission.GM.Iterm N W m)
      = (∑' (m : ℤ × ℤ × ℤ),
          (if Submission.GM.nzCount m = 2 then Submission.GM.Iterm N W m else 0)) := by
    rw [tsum_subtype (s := {m : ℤ × ℤ × ℤ | Submission.GM.nzCount m = 2})
      (f := fun m => Submission.GM.Iterm N W m)]
    refine tsum_congr (fun m => ?_)
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [Submission.GM.Spart, hcoe, hind]
  rw [tsum_congr hpt]
  rw [Summable.tsum_add (hs1.add hs2) hs3, Summable.tsum_add hs1 hs2]
  rfl

/-! ## 6. Each pattern factorises -/

lemma Bg1_eq (hxi : DecHyp) (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ) :
    Bg1 N W = (N:ℂ)^3 * ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
      Submission.GM.hhat (t1 - t2) 0 * Sall N (t2 - t3) * Sall N (t3 - t1) := by
  have hstep : (∑' (m : ℤ × ℤ × ℤ),
        (if m.1 = 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0 then Submission.GM.Iterm N W m else 0))
      = (N:ℂ)^3 * ∑' (m : ℤ × ℤ × ℤ),
        (if m.1 = 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0 then
          ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
            Phi N (t1 - t2) m.1 * Phi N (t2 - t3) m.2.1 * Phi N (t3 - t1) m.2.2
          else 0) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun m => ?_)
    by_cases h : m.1 = 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0
    · rw [if_pos h, if_pos h, Submission.GM.Iterm]
      simp only [Phi]
    · rw [if_neg h, if_neg h, mul_zero]
  have hinner : (∑' (m : ℤ × ℤ × ℤ),
        (if m.1 = 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0 then
          ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
            Phi N (t1 - t2) m.1 * Phi N (t2 - t3) m.2.1 * Phi N (t3 - t1) m.2.2
          else 0))
      = ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
          Submission.GM.hhat (t1 - t2) 0 * Sall N (t2 - t3) * Sall N (t3 - t1) := by
    have hpush : ∀ m : ℤ × ℤ × ℤ,
        (if m.1 = 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0 then
            ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
              Phi N (t1 - t2) m.1 * Phi N (t2 - t3) m.2.1 * Phi N (t3 - t1) m.2.2
          else 0)
        = ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
            (if m.1 = 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0 then
              Phi N (t1 - t2) m.1 * Phi N (t2 - t3) m.2.1 * Phi N (t3 - t1) m.2.2
            else 0) := by
      intro m
      by_cases h : m.1 = 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0
      · rw [if_pos h]; simp only [if_pos h]
      · rw [if_neg h]; simp only [if_neg h, Finset.sum_const_zero]
    rw [tsum_congr hpush]
    rw [← Work.GM.Trace.tsum_fin_swap W (fun t1 t2 t3 (m : ℤ × ℤ × ℤ) =>
        (if m.1 = 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0 then
          Phi N (t1 - t2) m.1 * Phi N (t2 - t3) m.2.1 * Phi N (t3 - t1) m.2.2
          else 0))
      (fun t1 _ t2 _ t3 _ => summable_guard_prod hxi N hN (t1 - t2) (t2 - t3) (t3 - t1)
        (fun m => m.1 = 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0))]
    refine Finset.sum_congr rfl (fun t1 _ => Finset.sum_congr rfl (fun t2 _ =>
      Finset.sum_congr rfl (fun t3 _ => ?_)))
    exact tsum_guard_fst_Phi hxi N hN (t1 - t2) (t2 - t3) (t3 - t1)
  rw [Bg1, hstep, hinner]

lemma Bg2_eq (hxi : DecHyp) (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ) :
    Bg2 N W = (N:ℂ)^3 * ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
      Sall N (t1 - t2) * Submission.GM.hhat (t2 - t3) 0 * Sall N (t3 - t1) := by
  have hstep : (∑' (m : ℤ × ℤ × ℤ),
        (if m.1 ≠ 0 ∧ m.2.1 = 0 ∧ m.2.2 ≠ 0 then Submission.GM.Iterm N W m else 0))
      = (N:ℂ)^3 * ∑' (m : ℤ × ℤ × ℤ),
        (if m.1 ≠ 0 ∧ m.2.1 = 0 ∧ m.2.2 ≠ 0 then
          ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
            Phi N (t1 - t2) m.1 * Phi N (t2 - t3) m.2.1 * Phi N (t3 - t1) m.2.2
          else 0) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun m => ?_)
    by_cases h : m.1 ≠ 0 ∧ m.2.1 = 0 ∧ m.2.2 ≠ 0
    · rw [if_pos h, if_pos h, Submission.GM.Iterm]
      simp only [Phi]
    · rw [if_neg h, if_neg h, mul_zero]
  have hinner : (∑' (m : ℤ × ℤ × ℤ),
        (if m.1 ≠ 0 ∧ m.2.1 = 0 ∧ m.2.2 ≠ 0 then
          ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
            Phi N (t1 - t2) m.1 * Phi N (t2 - t3) m.2.1 * Phi N (t3 - t1) m.2.2
          else 0))
      = ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
          Sall N (t1 - t2) * Submission.GM.hhat (t2 - t3) 0 * Sall N (t3 - t1) := by
    have hpush : ∀ m : ℤ × ℤ × ℤ,
        (if m.1 ≠ 0 ∧ m.2.1 = 0 ∧ m.2.2 ≠ 0 then
            ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
              Phi N (t1 - t2) m.1 * Phi N (t2 - t3) m.2.1 * Phi N (t3 - t1) m.2.2
          else 0)
        = ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
            (if m.1 ≠ 0 ∧ m.2.1 = 0 ∧ m.2.2 ≠ 0 then
              Phi N (t1 - t2) m.1 * Phi N (t2 - t3) m.2.1 * Phi N (t3 - t1) m.2.2
            else 0) := by
      intro m
      by_cases h : m.1 ≠ 0 ∧ m.2.1 = 0 ∧ m.2.2 ≠ 0
      · rw [if_pos h]; simp only [if_pos h]
      · rw [if_neg h]; simp only [if_neg h, Finset.sum_const_zero]
    rw [tsum_congr hpush]
    rw [← Work.GM.Trace.tsum_fin_swap W (fun t1 t2 t3 (m : ℤ × ℤ × ℤ) =>
        (if m.1 ≠ 0 ∧ m.2.1 = 0 ∧ m.2.2 ≠ 0 then
          Phi N (t1 - t2) m.1 * Phi N (t2 - t3) m.2.1 * Phi N (t3 - t1) m.2.2
          else 0))
      (fun t1 _ t2 _ t3 _ => summable_guard_prod hxi N hN (t1 - t2) (t2 - t3) (t3 - t1)
        (fun m => m.1 ≠ 0 ∧ m.2.1 = 0 ∧ m.2.2 ≠ 0))]
    refine Finset.sum_congr rfl (fun t1 _ => Finset.sum_congr rfl (fun t2 _ =>
      Finset.sum_congr rfl (fun t3 _ => ?_)))
    have hh := tsum_guard_snd_Phi hxi N hN (t1 - t2) (t2 - t3) (t3 - t1)
    rw [hh]; ring
  rw [Bg2, hstep, hinner]

lemma Bg3_eq (hxi : DecHyp) (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ) :
    Bg3 N W = (N:ℂ)^3 * ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
      Sall N (t1 - t2) * Sall N (t2 - t3) * Submission.GM.hhat (t3 - t1) 0 := by
  have hstep : (∑' (m : ℤ × ℤ × ℤ),
        (if m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 = 0 then Submission.GM.Iterm N W m else 0))
      = (N:ℂ)^3 * ∑' (m : ℤ × ℤ × ℤ),
        (if m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 = 0 then
          ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
            Phi N (t1 - t2) m.1 * Phi N (t2 - t3) m.2.1 * Phi N (t3 - t1) m.2.2
          else 0) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun m => ?_)
    by_cases h : m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 = 0
    · rw [if_pos h, if_pos h, Submission.GM.Iterm]
      simp only [Phi]
    · rw [if_neg h, if_neg h, mul_zero]
  have hinner : (∑' (m : ℤ × ℤ × ℤ),
        (if m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 = 0 then
          ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
            Phi N (t1 - t2) m.1 * Phi N (t2 - t3) m.2.1 * Phi N (t3 - t1) m.2.2
          else 0))
      = ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
          Sall N (t1 - t2) * Sall N (t2 - t3) * Submission.GM.hhat (t3 - t1) 0 := by
    have hpush : ∀ m : ℤ × ℤ × ℤ,
        (if m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 = 0 then
            ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
              Phi N (t1 - t2) m.1 * Phi N (t2 - t3) m.2.1 * Phi N (t3 - t1) m.2.2
          else 0)
        = ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
            (if m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 = 0 then
              Phi N (t1 - t2) m.1 * Phi N (t2 - t3) m.2.1 * Phi N (t3 - t1) m.2.2
            else 0) := by
      intro m
      by_cases h : m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 = 0
      · rw [if_pos h]; simp only [if_pos h]
      · rw [if_neg h]; simp only [if_neg h, Finset.sum_const_zero]
    rw [tsum_congr hpush]
    rw [← Work.GM.Trace.tsum_fin_swap W (fun t1 t2 t3 (m : ℤ × ℤ × ℤ) =>
        (if m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 = 0 then
          Phi N (t1 - t2) m.1 * Phi N (t2 - t3) m.2.1 * Phi N (t3 - t1) m.2.2
          else 0))
      (fun t1 _ t2 _ t3 _ => summable_guard_prod hxi N hN (t1 - t2) (t2 - t3) (t3 - t1)
        (fun m => m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 = 0))]
    refine Finset.sum_congr rfl (fun t1 _ => Finset.sum_congr rfl (fun t2 _ =>
      Finset.sum_congr rfl (fun t3 _ => ?_)))
    have hh := tsum_guard_thd_Phi hxi N hN (t1 - t2) (t2 - t3) (t3 - t1)
    rw [hh]; ring
  rw [Bg3, hstep, hinner]


/-! ## 7. The pair sum and the main bounds -/

lemma Rpair_nonneg (N : ℕ) (W : Finset ℝ) : 0 ≤ Rpair N W :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))

/-- The diagonal contribution `Σ_{u,v} ‖A(u-v)‖‖A(v-u)‖ ≤ 2 Rpair`. -/
lemma diag_sum_le (N : ℕ) (W : Finset ℝ) :
    (∑ u ∈ W, ∑ v ∈ W, ‖Sall N (u - v)‖ * ‖Sall N (v - u)‖) ≤ 2 * Rpair N W := by
  have hpt : ∀ u ∈ W, ∀ v ∈ W,
      ‖Sall N (u - v)‖ * ‖Sall N (v - u)‖ ≤ ‖Sall N (u - v)‖^2 + ‖Sall N (v - u)‖^2 := by
    intro u _ v _
    nlinarith [sq_nonneg (‖Sall N (u - v)‖ - ‖Sall N (v - u)‖)]
  have h1 : (∑ u ∈ W, ∑ v ∈ W, ‖Sall N (u - v)‖^2) = Rpair N W := rfl
  have h2 : (∑ u ∈ W, ∑ v ∈ W, ‖Sall N (v - u)‖^2) = Rpair N W := by
    rw [Rpair, Finset.sum_comm]
  calc (∑ u ∈ W, ∑ v ∈ W, ‖Sall N (u - v)‖ * ‖Sall N (v - u)‖)
      ≤ ∑ u ∈ W, ∑ v ∈ W, (‖Sall N (u - v)‖^2 + ‖Sall N (v - u)‖^2) :=
        Finset.sum_le_sum (fun u h1 => Finset.sum_le_sum (fun v h2 => hpt u h1 v h2))
    _ = (∑ u ∈ W, ∑ v ∈ W, ‖Sall N (u - v)‖^2)
          + (∑ u ∈ W, ∑ v ∈ W, ‖Sall N (v - u)‖^2) := by
        have hh : ∀ u ∈ W, (∑ v ∈ W, (‖Sall N (u - v)‖^2 + ‖Sall N (v - u)‖^2))
            = (∑ v ∈ W, ‖Sall N (u - v)‖^2) + (∑ v ∈ W, ‖Sall N (v - u)‖^2) :=
          fun u _ => Finset.sum_add_distrib
        rw [Finset.sum_congr rfl hh, Finset.sum_add_distrib]
    _ = 2 * Rpair N W := by rw [h1, h2]; ring

/-- The off-diagonal contribution for the first pattern. -/
lemma off1_le (N : ℕ) (W : Finset ℝ) :
    (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖)
      ≤ 2 * (W.card : ℝ) * Rpair N W := by
  have hkey : ∀ t1 ∈ W, ∀ t2 ∈ W, ∀ t3 ∈ W,
      ‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖
        ≤ ‖Sall N (t2 - t3)‖^2 + ‖Sall N (t3 - t1)‖^2 := by
    intro t1 _ t2 _ t3 _
    nlinarith [sq_nonneg (‖Sall N (t2 - t3)‖ - ‖Sall N (t3 - t1)‖)]
  have hsum1 : (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t2 - t3)‖^2)
      = (W.card : ℝ) * Rpair N W := by
    simp only [Finset.sum_const, nsmul_eq_mul, Rpair]
  have hsum2 : (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t3 - t1)‖^2)
      = (W.card : ℝ) * Rpair N W := by
    have h1 : (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t3 - t1)‖^2)
        = (W.card : ℝ) * (∑ t1 ∈ W, ∑ t3 ∈ W, ‖Sall N (t3 - t1)‖^2) := by
      have hh : ∀ t1 ∈ W, (∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t3 - t1)‖^2)
          = (W.card : ℝ) * (∑ t3 ∈ W, ‖Sall N (t3 - t1)‖^2) := fun t1 _ => by
        simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.sum_congr rfl hh, ← Finset.mul_sum]
    rw [h1]
    have hz : (∑ t1 ∈ W, ∑ t3 ∈ W, ‖Sall N (t3 - t1)‖^2) = Rpair N W := by
      rw [Rpair, Finset.sum_comm]
    rw [hz]
  have hstep : (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        ‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖)
      ≤ (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t2 - t3)‖^2)
        + (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t3 - t1)‖^2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun t1 ht1 => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun t2 ht2 => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun t3 ht3 => hkey t1 ht1 t2 ht2 t3 ht3)
  rw [hsum1, hsum2] at hstep
  linarith [hstep]

/-- The off-diagonal contribution for the second pattern. -/
lemma off2_le (N : ℕ) (W : Finset ℝ) :
    (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖ * ‖Sall N (t3 - t1)‖)
      ≤ 2 * (W.card : ℝ) * Rpair N W := by
  have hkey : ∀ t1 ∈ W, ∀ t2 ∈ W, ∀ t3 ∈ W,
      ‖Sall N (t1 - t2)‖ * ‖Sall N (t3 - t1)‖
        ≤ ‖Sall N (t1 - t2)‖^2 + ‖Sall N (t3 - t1)‖^2 := by
    intro t1 _ t2 _ t3 _
    nlinarith [sq_nonneg (‖Sall N (t1 - t2)‖ - ‖Sall N (t3 - t1)‖)]
  have hsum1 : (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖^2)
      = (W.card : ℝ) * Rpair N W := by
    have h1 : (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖^2)
        = (W.card : ℝ) * (∑ t1 ∈ W, ∑ t2 ∈ W, ‖Sall N (t1 - t2)‖^2) := by
      have hh : ∀ t1 ∈ W, (∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖^2)
          = (W.card : ℝ) * (∑ t2 ∈ W, ‖Sall N (t1 - t2)‖^2) := by
        intro t1 _
        rw [show (∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖^2)
            = ∑ t2 ∈ W, (W.card : ℝ) * ‖Sall N (t1 - t2)‖^2 from
          Finset.sum_congr rfl (fun t2 _ => by simp only [Finset.sum_const, nsmul_eq_mul]),
          ← Finset.mul_sum]
      rw [Finset.sum_congr rfl hh, ← Finset.mul_sum]
    rw [h1]
    have hz : (∑ t1 ∈ W, ∑ t2 ∈ W, ‖Sall N (t1 - t2)‖^2) = Rpair N W := rfl
    rw [hz]
  have hsum2 : (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t3 - t1)‖^2)
      = (W.card : ℝ) * Rpair N W := by
    have h1 : (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t3 - t1)‖^2)
        = (W.card : ℝ) * (∑ t1 ∈ W, ∑ t3 ∈ W, ‖Sall N (t3 - t1)‖^2) := by
      have hh : ∀ t1 ∈ W, (∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t3 - t1)‖^2)
          = (W.card : ℝ) * (∑ t3 ∈ W, ‖Sall N (t3 - t1)‖^2) := fun t1 _ => by
        simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.sum_congr rfl hh, ← Finset.mul_sum]
    rw [h1]
    have hz : (∑ t1 ∈ W, ∑ t3 ∈ W, ‖Sall N (t3 - t1)‖^2) = Rpair N W := by
      rw [Rpair, Finset.sum_comm]
    rw [hz]
  have hstep : (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        ‖Sall N (t1 - t2)‖ * ‖Sall N (t3 - t1)‖)
      ≤ (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖^2)
        + (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t3 - t1)‖^2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun t1 ht1 => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun t2 ht2 => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun t3 ht3 => hkey t1 ht1 t2 ht2 t3 ht3)
  rw [hsum1, hsum2] at hstep
  linarith [hstep]

/-- The off-diagonal contribution for the third pattern. -/
lemma off3_le (N : ℕ) (W : Finset ℝ) :
    (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖ * ‖Sall N (t2 - t3)‖)
      ≤ 2 * (W.card : ℝ) * Rpair N W := by
  have hkey : ∀ t1 ∈ W, ∀ t2 ∈ W, ∀ t3 ∈ W,
      ‖Sall N (t1 - t2)‖ * ‖Sall N (t2 - t3)‖
        ≤ ‖Sall N (t1 - t2)‖^2 + ‖Sall N (t2 - t3)‖^2 := by
    intro t1 _ t2 _ t3 _
    nlinarith [sq_nonneg (‖Sall N (t1 - t2)‖ - ‖Sall N (t2 - t3)‖)]
  have hsum1 : (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖^2)
      = (W.card : ℝ) * Rpair N W := by
    have h1 : (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖^2)
        = (W.card : ℝ) * (∑ t1 ∈ W, ∑ t2 ∈ W, ‖Sall N (t1 - t2)‖^2) := by
      have hh : ∀ t1 ∈ W, (∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖^2)
          = (W.card : ℝ) * (∑ t2 ∈ W, ‖Sall N (t1 - t2)‖^2) := by
        intro t1 _
        rw [show (∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖^2)
            = ∑ t2 ∈ W, (W.card : ℝ) * ‖Sall N (t1 - t2)‖^2 from
          Finset.sum_congr rfl (fun t2 _ => by simp only [Finset.sum_const, nsmul_eq_mul]),
          ← Finset.mul_sum]
      rw [Finset.sum_congr rfl hh, ← Finset.mul_sum]
    rw [h1]
    have hz : (∑ t1 ∈ W, ∑ t2 ∈ W, ‖Sall N (t1 - t2)‖^2) = Rpair N W := rfl
    rw [hz]
  have hsum2 : (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t2 - t3)‖^2)
      = (W.card : ℝ) * Rpair N W := by
    simp only [Finset.sum_const, nsmul_eq_mul, Rpair]
  have hstep : (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        ‖Sall N (t1 - t2)‖ * ‖Sall N (t2 - t3)‖)
      ≤ (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖^2)
        + (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t2 - t3)‖^2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun t1 ht1 => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun t2 ht2 => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun t3 ht3 => hkey t1 ht1 t2 ht2 t3 ht3)
  rw [hsum1, hsum2] at hstep
  linarith [hstep]

/-! ## 8. The three cyclic sums -/

/-- The main bound for the first pattern. -/
lemma cyc_bound1 (N : ℕ) (W : Finset ℝ) (ε Kd : ℝ) (j : ℕ) (hKd : 0 ≤ Kd)
    (hdec : ∀ s : ℝ, (Submission.LargeValues.M N) ^ ε ≤ |s| →
      ‖Submission.GM.hhat s 0‖ ≤ Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)))
    (hsep : Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε)) :
    ‖∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        Submission.GM.hhat (t1 - t2) 0 * Sall N (t2 - t3) * Sall N (t3 - t1)‖
      ≤ 2 * Work.GM.Trace.Azero * Rpair N W
        + Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
            * (2 * (W.card : ℝ) * Rpair N W) := by
  have hnorm0 : ‖Submission.GM.hhat 0 0‖ = Work.GM.Trace.Azero := by
    rw [Work.GM.Trace.hhat_zero_zero, Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self Work.GM.Trace.Azero_nonneg]
  have htri : ‖∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        Submission.GM.hhat (t1 - t2) 0 * Sall N (t2 - t3) * Sall N (t3 - t1)‖
      ≤ ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
          ‖Submission.GM.hhat (t1 - t2) 0‖ * (‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖) := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun t1 _ => (norm_sum_le _ _).trans ?_)
    refine Finset.sum_le_sum (fun t2 _ => (norm_sum_le _ _).trans ?_)
    refine Finset.sum_le_sum (fun t3 _ => le_of_eq ?_)
    rw [norm_mul, norm_mul, mul_assoc]
  have hsplit : ∀ t1 ∈ W, ∀ t2 ∈ W, ∀ t3 ∈ W,
      ‖Submission.GM.hhat (t1 - t2) 0‖ * (‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖)
        ≤ (if t1 = t2 then Work.GM.Trace.Azero
            else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)))
          * (‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖) := by
    intro t1 ht1 t2 ht2 t3 ht3
    have hb : ‖Submission.GM.hhat (t1 - t2) 0‖
        ≤ (if t1 = t2 then Work.GM.Trace.Azero
            else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))) := by
      by_cases h : t1 = t2
      · rw [if_pos h, h, sub_self]; exact le_of_eq hnorm0
      · rw [if_neg h]
        have hge : (Submission.LargeValues.M N) ^ ε ≤ |t1 - t2| := hsep t1 ht1 t2 ht2 h
        exact hdec (t1 - t2) hge
    exact mul_le_mul_of_nonneg_right hb (by positivity)
  have hstep : (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        ‖Submission.GM.hhat (t1 - t2) 0‖ * (‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖))
      ≤ ∑ t1 ∈ W, ∑ t2 ∈ W,
          (if t1 = t2 then Work.GM.Trace.Azero
            else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)))
          * (∑ t3 ∈ W, ‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖) := by
    refine Finset.sum_le_sum (fun t1 ht1 => Finset.sum_le_sum (fun t2 ht2 => ?_))
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun t3 ht3 => hsplit t1 ht1 t2 ht2 t3 ht3)
  have hdecomp : ∀ t1 ∈ W, ∀ t2 ∈ W,
      (if t1 = t2 then Work.GM.Trace.Azero
          else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)))
        * (∑ t3 ∈ W, ‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖)
      = (if t1 = t2 then Work.GM.Trace.Azero else 0)
          * (∑ t3 ∈ W, ‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖)
        + (if t1 = t2 then 0 else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)))
          * (∑ t3 ∈ W, ‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖) := by
    intro t1 _ t2 _
    by_cases h : t1 = t2 <;> simp [h]
  have hinnerdiag : ∀ t1 ∈ W,
      (∑ t2 ∈ W, (if t1 = t2 then Work.GM.Trace.Azero else 0)
        * (∑ t3 ∈ W, ‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖))
        = Work.GM.Trace.Azero
          * (∑ t3 ∈ W, ‖Sall N (t1 - t3)‖ * ‖Sall N (t3 - t1)‖) := by
    intro t1 ht1
    rw [show (∑ t2 ∈ W, (if t1 = t2 then Work.GM.Trace.Azero else 0)
          * (∑ t3 ∈ W, ‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖))
        = ∑ t2 ∈ W, (if t1 = t2 then Work.GM.Trace.Azero
            * (∑ t3 ∈ W, ‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖) else 0) from by
          refine Finset.sum_congr rfl (fun t2 _ => ?_)
          by_cases h : t1 = t2 <;> simp [h]]
    rw [Finset.sum_ite_eq]
    simp [ht1]
  have hdiag : (∑ t1 ∈ W, ∑ t2 ∈ W, (if t1 = t2 then Work.GM.Trace.Azero else 0)
        * (∑ t3 ∈ W, ‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖))
      = Work.GM.Trace.Azero * (∑ t1 ∈ W, ∑ t3 ∈ W,
          ‖Sall N (t1 - t3)‖ * ‖Sall N (t3 - t1)‖) := by
    rw [Finset.sum_congr rfl hinnerdiag, ← Finset.mul_sum]
  have hκnn : 0 ≤ Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)) := by
    apply mul_nonneg hKd
    apply Real.rpow_nonneg
    rw [Submission.LargeValues.M]; positivity
  have hoff : (∑ t1 ∈ W, ∑ t2 ∈ W, (if t1 = t2 then 0
        else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)))
        * (∑ t3 ∈ W, ‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖))
      ≤ Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
        * (2 * (W.card : ℝ) * Rpair N W) := by
    have hpt : ∀ t1 ∈ W, ∀ t2 ∈ W,
        (if t1 = t2 then 0 else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)))
          * (∑ t3 ∈ W, ‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖)
        ≤ Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
          * (∑ t3 ∈ W, ‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖) := by
      intro t1 _ t2 _
      by_cases h : t1 = t2
      · rw [if_pos h, zero_mul]
        exact mul_nonneg hκnn (Finset.sum_nonneg (fun t3 _ => by positivity))
      · rw [if_neg h]
    calc (∑ t1 ∈ W, ∑ t2 ∈ W, _)
        ≤ ∑ t1 ∈ W, ∑ t2 ∈ W, Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
            * (∑ t3 ∈ W, ‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖) :=
          Finset.sum_le_sum (fun t1 h1 => Finset.sum_le_sum (fun t2 h2 => hpt t1 h1 t2 h2))
      _ = Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
            * (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
                ‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun t1 _ => ?_)
          rw [Finset.mul_sum]
      _ ≤ Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
            * (2 * (W.card : ℝ) * Rpair N W) :=
          mul_le_mul_of_nonneg_left (off1_le N W) hκnn
  calc ‖∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        Submission.GM.hhat (t1 - t2) 0 * Sall N (t2 - t3) * Sall N (t3 - t1)‖
      ≤ ∑ t1 ∈ W, ∑ t2 ∈ W, (if t1 = t2 then Work.GM.Trace.Azero
            else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)))
          * (∑ t3 ∈ W, ‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖) := htri.trans hstep
    _ = (∑ t1 ∈ W, ∑ t2 ∈ W, (if t1 = t2 then Work.GM.Trace.Azero else 0)
          * (∑ t3 ∈ W, ‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖))
        + (∑ t1 ∈ W, ∑ t2 ∈ W, (if t1 = t2 then 0
            else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)))
          * (∑ t3 ∈ W, ‖Sall N (t2 - t3)‖ * ‖Sall N (t3 - t1)‖)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun t1 ht1 => ?_)
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun t2 ht2 => hdecomp t1 ht1 t2 ht2)
    _ ≤ 2 * Work.GM.Trace.Azero * Rpair N W
        + Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
            * (2 * (W.card : ℝ) * Rpair N W) := by
        rw [hdiag]
        refine add_le_add ?_ hoff
        exact (mul_le_mul_of_nonneg_left (diag_sum_le N W) Work.GM.Trace.Azero_nonneg).trans
          (le_of_eq (by ring))

/-- The main bound for the second pattern. -/
lemma cyc_bound2 (N : ℕ) (W : Finset ℝ) (ε Kd : ℝ) (j : ℕ) (hKd : 0 ≤ Kd)
    (hdec : ∀ s : ℝ, (Submission.LargeValues.M N) ^ ε ≤ |s| →
      ‖Submission.GM.hhat s 0‖ ≤ Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)))
    (hsep : Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε)) :
    ‖∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        Sall N (t1 - t2) * Submission.GM.hhat (t2 - t3) 0 * Sall N (t3 - t1)‖
      ≤ 2 * Work.GM.Trace.Azero * Rpair N W
        + Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
            * (2 * (W.card : ℝ) * Rpair N W) := by
  have hnorm0 : ‖Submission.GM.hhat 0 0‖ = Work.GM.Trace.Azero := by
    rw [Work.GM.Trace.hhat_zero_zero, Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self Work.GM.Trace.Azero_nonneg]
  have hκnn : 0 ≤ Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)) := by
    apply mul_nonneg hKd
    apply Real.rpow_nonneg
    rw [Submission.LargeValues.M]; positivity
  have htri : ‖∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        Sall N (t1 - t2) * Submission.GM.hhat (t2 - t3) 0 * Sall N (t3 - t1)‖
      ≤ ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
          ‖Sall N (t1 - t2)‖ * (‖Submission.GM.hhat (t2 - t3) 0‖ * ‖Sall N (t3 - t1)‖) := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun t1 _ => (norm_sum_le _ _).trans ?_)
    refine Finset.sum_le_sum (fun t2 _ => (norm_sum_le _ _).trans ?_)
    refine Finset.sum_le_sum (fun t3 _ => le_of_eq ?_)
    rw [norm_mul, norm_mul]; ring
  have hsplit : ∀ t1 ∈ W, ∀ t2 ∈ W, ∀ t3 ∈ W,
      ‖Sall N (t1 - t2)‖ * (‖Submission.GM.hhat (t2 - t3) 0‖ * ‖Sall N (t3 - t1)‖)
        ≤ ‖Sall N (t1 - t2)‖ * ((if t2 = t3 then Work.GM.Trace.Azero
            else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))) * ‖Sall N (t3 - t1)‖) := by
    intro t1 ht1 t2 ht2 t3 ht3
    have hb : ‖Submission.GM.hhat (t2 - t3) 0‖
        ≤ (if t2 = t3 then Work.GM.Trace.Azero
            else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))) := by
      by_cases h : t2 = t3
      · rw [if_pos h, h, sub_self]; exact le_of_eq hnorm0
      · rw [if_neg h]
        have hge : (Submission.LargeValues.M N) ^ ε ≤ |t2 - t3| := hsep t2 ht2 t3 ht3 h
        exact hdec (t2 - t3) hge
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (by positivity)) (by positivity)
  have hpattern : ∀ t1 ∈ W,
      (∑ t2 ∈ W, ∑ t3 ∈ W,
          ‖Sall N (t1 - t2)‖ * (‖Submission.GM.hhat (t2 - t3) 0‖ * ‖Sall N (t3 - t1)‖))
        ≤ Work.GM.Trace.Azero * (∑ t2 ∈ W, ‖Sall N (t1 - t2)‖ * ‖Sall N (t2 - t1)‖)
          + Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
            * (∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖ * ‖Sall N (t3 - t1)‖) := by
    intro t1 ht1
    have hstep : (∑ t2 ∈ W, ∑ t3 ∈ W,
          ‖Sall N (t1 - t2)‖ * (‖Submission.GM.hhat (t2 - t3) 0‖ * ‖Sall N (t3 - t1)‖))
        ≤ ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖
            * ((if t2 = t3 then Work.GM.Trace.Azero
                else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))) * ‖Sall N (t3 - t1)‖) :=
      Finset.sum_le_sum (fun t2 h2 => Finset.sum_le_sum (fun t3 h3 => hsplit t1 ht1 t2 h2 t3 h3))
    have hdecomp : (∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖
            * ((if t2 = t3 then Work.GM.Trace.Azero
                else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))) * ‖Sall N (t3 - t1)‖))
        = (∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖
            * ((if t2 = t3 then Work.GM.Trace.Azero else 0) * ‖Sall N (t3 - t1)‖))
          + (∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖
            * ((if t2 = t3 then 0
                else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))) * ‖Sall N (t3 - t1)‖)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun t2 _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun t3 _ => ?_)
      by_cases h : t2 = t3 <;> simp [h]
    have hdiag : (∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖
          * ((if t2 = t3 then Work.GM.Trace.Azero else 0) * ‖Sall N (t3 - t1)‖))
        = Work.GM.Trace.Azero * (∑ t2 ∈ W, ‖Sall N (t1 - t2)‖ * ‖Sall N (t2 - t1)‖) := by
      have hinner : ∀ t2 ∈ W, (∑ t3 ∈ W, ‖Sall N (t1 - t2)‖
            * ((if t2 = t3 then Work.GM.Trace.Azero else 0) * ‖Sall N (t3 - t1)‖))
          = Work.GM.Trace.Azero * (‖Sall N (t1 - t2)‖ * ‖Sall N (t2 - t1)‖) := by
        intro t2 ht2
        rw [show (∑ t3 ∈ W, ‖Sall N (t1 - t2)‖
              * ((if t2 = t3 then Work.GM.Trace.Azero else 0) * ‖Sall N (t3 - t1)‖))
            = ∑ t3 ∈ W, (if t2 = t3 then Work.GM.Trace.Azero
                * (‖Sall N (t1 - t2)‖ * ‖Sall N (t3 - t1)‖) else 0) from by
              refine Finset.sum_congr rfl (fun t3 _ => ?_)
              by_cases h : t2 = t3 <;> simp [h] <;> ring]
        rw [Finset.sum_ite_eq]
        simp [ht2]
      rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
    have hoff : (∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖
          * ((if t2 = t3 then 0
              else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))) * ‖Sall N (t3 - t1)‖))
        ≤ Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
            * (∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖ * ‖Sall N (t3 - t1)‖) := by
      have hpt2 : ∀ t2 ∈ W, ∀ t3 ∈ W,
          ‖Sall N (t1 - t2)‖ * ((if t2 = t3 then 0
              else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))) * ‖Sall N (t3 - t1)‖)
          ≤ Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
              * (‖Sall N (t1 - t2)‖ * ‖Sall N (t3 - t1)‖) := by
        intro t2 _ t3 _
        by_cases h : t2 = t3
        · rw [if_pos h]
          simp only [zero_mul, mul_zero]
          exact mul_nonneg hκnn (by positivity)
        · rw [if_neg h]
          exact le_of_eq (by ring)
      calc (∑ t2 ∈ W, ∑ t3 ∈ W, _)
          ≤ ∑ t2 ∈ W, ∑ t3 ∈ W, Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
              * (‖Sall N (t1 - t2)‖ * ‖Sall N (t3 - t1)‖) :=
            Finset.sum_le_sum (fun t2 h2 => Finset.sum_le_sum (fun t3 h3 => hpt2 t2 h2 t3 h3))
        _ = Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
              * (∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖ * ‖Sall N (t3 - t1)‖) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun t2 _ => ?_)
            rw [Finset.mul_sum]
    calc (∑ t2 ∈ W, ∑ t3 ∈ W,
          ‖Sall N (t1 - t2)‖ * (‖Submission.GM.hhat (t2 - t3) 0‖ * ‖Sall N (t3 - t1)‖))
        ≤ _ := hstep
      _ = _ + _ := hdecomp
      _ ≤ Work.GM.Trace.Azero * (∑ t2 ∈ W, ‖Sall N (t1 - t2)‖ * ‖Sall N (t2 - t1)‖)
          + Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
            * (∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖ * ‖Sall N (t3 - t1)‖) := by
          rw [hdiag]
          exact add_le_add le_rfl hoff
  calc ‖∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        Sall N (t1 - t2) * Submission.GM.hhat (t2 - t3) 0 * Sall N (t3 - t1)‖
      ≤ ∑ t1 ∈ W, (Work.GM.Trace.Azero * (∑ t2 ∈ W, ‖Sall N (t1 - t2)‖ * ‖Sall N (t2 - t1)‖)
          + Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
            * (∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖ * ‖Sall N (t3 - t1)‖)) :=
        htri.trans (Finset.sum_le_sum (fun t1 h1 => hpattern t1 h1))
    _ = Work.GM.Trace.Azero * (∑ t1 ∈ W, ∑ t2 ∈ W, ‖Sall N (t1 - t2)‖ * ‖Sall N (t2 - t1)‖)
        + Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
            * (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖ * ‖Sall N (t3 - t1)‖) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * Work.GM.Trace.Azero * Rpair N W
        + Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
            * (2 * (W.card : ℝ) * Rpair N W) := by
        refine add_le_add ?_ (mul_le_mul_of_nonneg_left (off2_le N W) hκnn)
        exact (mul_le_mul_of_nonneg_left (diag_sum_le N W) Work.GM.Trace.Azero_nonneg).trans
          (le_of_eq (by ring))

/-- The main bound for the third pattern. -/
lemma cyc_bound3 (N : ℕ) (W : Finset ℝ) (ε Kd : ℝ) (j : ℕ) (hKd : 0 ≤ Kd)
    (hdec : ∀ s : ℝ, (Submission.LargeValues.M N) ^ ε ≤ |s| →
      ‖Submission.GM.hhat s 0‖ ≤ Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)))
    (hsep : Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε)) :
    ‖∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        Sall N (t1 - t2) * Sall N (t2 - t3) * Submission.GM.hhat (t3 - t1) 0‖
      ≤ 2 * Work.GM.Trace.Azero * Rpair N W
        + Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
            * (2 * (W.card : ℝ) * Rpair N W) := by
  have hnorm0 : ‖Submission.GM.hhat 0 0‖ = Work.GM.Trace.Azero := by
    rw [Work.GM.Trace.hhat_zero_zero, Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self Work.GM.Trace.Azero_nonneg]
  have hκnn : 0 ≤ Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)) := by
    apply mul_nonneg hKd
    apply Real.rpow_nonneg
    rw [Submission.LargeValues.M]; positivity
  have htri : ‖∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        Sall N (t1 - t2) * Sall N (t2 - t3) * Submission.GM.hhat (t3 - t1) 0‖
      ≤ ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
          ‖Sall N (t1 - t2)‖ * (‖Sall N (t2 - t3)‖ * ‖Submission.GM.hhat (t3 - t1) 0‖) := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun t1 _ => (norm_sum_le _ _).trans ?_)
    refine Finset.sum_le_sum (fun t2 _ => (norm_sum_le _ _).trans ?_)
    refine Finset.sum_le_sum (fun t3 _ => le_of_eq ?_)
    rw [norm_mul, norm_mul, mul_assoc]
  have hsplit : ∀ t1 ∈ W, ∀ t2 ∈ W, ∀ t3 ∈ W,
      ‖Sall N (t1 - t2)‖ * (‖Sall N (t2 - t3)‖ * ‖Submission.GM.hhat (t3 - t1) 0‖)
        ≤ ‖Sall N (t1 - t2)‖ * (‖Sall N (t2 - t3)‖
            * (if t3 = t1 then Work.GM.Trace.Azero
                else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)))) := by
    intro t1 ht1 t2 ht2 t3 ht3
    have hb : ‖Submission.GM.hhat (t3 - t1) 0‖
        ≤ (if t3 = t1 then Work.GM.Trace.Azero
            else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))) := by
      by_cases h : t3 = t1
      · rw [if_pos h, h, sub_self]; exact le_of_eq hnorm0
      · rw [if_neg h]
        have hge : (Submission.LargeValues.M N) ^ ε ≤ |t3 - t1| := hsep t3 ht3 t1 ht1 h
        exact hdec (t3 - t1) hge
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (norm_nonneg _)) (norm_nonneg _)
  have hpattern : ∀ t1 ∈ W, ∀ t2 ∈ W,
      (∑ t3 ∈ W, ‖Sall N (t1 - t2)‖
          * (‖Sall N (t2 - t3)‖ * ‖Submission.GM.hhat (t3 - t1) 0‖)) ≤
        ‖Sall N (t1 - t2)‖ * (Work.GM.Trace.Azero * ‖Sall N (t2 - t1)‖)
          + ‖Sall N (t1 - t2)‖ * (Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
              * (∑ t3 ∈ W, ‖Sall N (t2 - t3)‖)) := by
    intro t1 ht1 t2 ht2
    have hstep : (∑ t3 ∈ W, ‖Sall N (t1 - t2)‖
          * (‖Sall N (t2 - t3)‖ * ‖Submission.GM.hhat (t3 - t1) 0‖))
        ≤ ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖ * (‖Sall N (t2 - t3)‖
            * (if t3 = t1 then Work.GM.Trace.Azero
                else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)))) :=
      Finset.sum_le_sum (fun t3 h3 => hsplit t1 ht1 t2 ht2 t3 h3)
    have hdecomp : (∑ t3 ∈ W, ‖Sall N (t1 - t2)‖ * (‖Sall N (t2 - t3)‖
            * (if t3 = t1 then Work.GM.Trace.Azero
                else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)))))
        = (∑ t3 ∈ W, ‖Sall N (t1 - t2)‖ * (‖Sall N (t2 - t3)‖
            * (if t3 = t1 then Work.GM.Trace.Azero else 0)))
          + (∑ t3 ∈ W, ‖Sall N (t1 - t2)‖ * (‖Sall N (t2 - t3)‖
            * (if t3 = t1 then 0
                else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun t3 _ => ?_)
      by_cases h : t3 = t1 <;> simp [h]
    have hdiag : (∑ t3 ∈ W, ‖Sall N (t1 - t2)‖ * (‖Sall N (t2 - t3)‖
          * (if t3 = t1 then Work.GM.Trace.Azero else 0)))
        = ‖Sall N (t1 - t2)‖ * (Work.GM.Trace.Azero * ‖Sall N (t2 - t1)‖) := by
      rw [show (∑ t3 ∈ W, ‖Sall N (t1 - t2)‖ * (‖Sall N (t2 - t3)‖
            * (if t3 = t1 then Work.GM.Trace.Azero else 0)))
          = ∑ t3 ∈ W, (if t3 = t1 then ‖Sall N (t1 - t2)‖
              * (‖Sall N (t2 - t3)‖ * Work.GM.Trace.Azero) else 0) from by
            refine Finset.sum_congr rfl (fun t3 _ => ?_)
            by_cases h : t3 = t1 <;> simp [h] <;> ring]
      rw [Finset.sum_ite_eq']
      simp only [ht1, if_true]
      ring
    have hoff : (∑ t3 ∈ W, ‖Sall N (t1 - t2)‖ * (‖Sall N (t2 - t3)‖
          * (if t3 = t1 then 0
              else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)))))
        ≤ ‖Sall N (t1 - t2)‖ * (Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
            * (∑ t3 ∈ W, ‖Sall N (t2 - t3)‖)) := by
      have hpt2 : ∀ t3 ∈ W, ‖Sall N (t1 - t2)‖ * (‖Sall N (t2 - t3)‖
            * (if t3 = t1 then 0
                else Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))))
          ≤ ‖Sall N (t1 - t2)‖ * (Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
              * ‖Sall N (t2 - t3)‖) := by
        intro t3 _
        by_cases h : t3 = t1
        · rw [if_pos h, mul_zero, mul_zero]
          exact mul_nonneg (norm_nonneg _) (by positivity)
        · rw [if_neg h]
          exact le_of_eq (by ring)
      calc (∑ t3 ∈ W, _)
          ≤ ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖ * (Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
              * ‖Sall N (t2 - t3)‖) := Finset.sum_le_sum (fun t3 h3 => hpt2 t3 h3)
        _ = ‖Sall N (t1 - t2)‖ * (Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
              * (∑ t3 ∈ W, ‖Sall N (t2 - t3)‖)) := by
            rw [Finset.mul_sum, Finset.mul_sum]
    calc (∑ t3 ∈ W, ‖Sall N (t1 - t2)‖
          * (‖Sall N (t2 - t3)‖ * ‖Submission.GM.hhat (t3 - t1) 0‖))
        ≤ _ := hstep
      _ = _ + _ := hdecomp
      _ ≤ ‖Sall N (t1 - t2)‖ * (Work.GM.Trace.Azero * ‖Sall N (t2 - t1)‖)
          + ‖Sall N (t1 - t2)‖ * (Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
              * (∑ t3 ∈ W, ‖Sall N (t2 - t3)‖)) := by
          rw [hdiag]
          exact add_le_add le_rfl hoff
  calc ‖∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        Sall N (t1 - t2) * Sall N (t2 - t3) * Submission.GM.hhat (t3 - t1) 0‖
      ≤ ∑ t1 ∈ W, ∑ t2 ∈ W,
          (‖Sall N (t1 - t2)‖ * (Work.GM.Trace.Azero * ‖Sall N (t2 - t1)‖)
            + ‖Sall N (t1 - t2)‖ * (Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
              * (∑ t3 ∈ W, ‖Sall N (t2 - t3)‖))) := by
        refine htri.trans ?_
        refine Finset.sum_le_sum (fun t1 h1 => Finset.sum_le_sum (fun t2 h2 => ?_))
        exact hpattern t1 h1 t2 h2
    _ = Work.GM.Trace.Azero * (∑ t1 ∈ W, ∑ t2 ∈ W, ‖Sall N (t1 - t2)‖ * ‖Sall N (t2 - t1)‖)
        + Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
            * (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ‖Sall N (t1 - t2)‖ * ‖Sall N (t2 - t3)‖) := by
        rw [Finset.sum_congr rfl (fun t1 _ => Finset.sum_add_distrib), Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun t1 _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun t2 _ => ?_)
          ring
        · simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun t1 _ => Finset.sum_congr rfl (fun t2 _ =>
            Finset.sum_congr rfl (fun t3 _ => ?_)))
          ring
    _ ≤ 2 * Work.GM.Trace.Azero * Rpair N W
        + Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
            * (2 * (W.card : ℝ) * Rpair N W) := by
        refine add_le_add ?_ (mul_le_mul_of_nonneg_left (off3_le N W) hκnn)
        exact (mul_le_mul_of_nonneg_left (diag_sum_le N W) Work.GM.Trace.Azero_nonneg).trans
          (le_of_eq (by ring))

/-! ## 9. The main theorem -/

theorem s2_reduction_aux
    (hxi : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t ξ : ℝ, ξ ≠ 0 →
      ‖Submission.GM.hhat t ξ‖ ≤ C * (1 + |t|) ^ j / |ξ| ^ j)
    (ht : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t ξ : ℝ, t ≠ 0 →
      ‖Submission.GM.hhat t ξ‖ ≤ C * (1 + |ξ|) ^ j / |t| ^ j) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
      ‖Submission.GM.Spart 2 N W‖ ≤ C * (N : ℝ) ^ 3 * ‖Submission.GM.hhat 0 0‖ *
          (∑ t₁ ∈ W, ∑ t₂ ∈ W,
            ‖∑' (m : {m : ℤ // m ≠ 0}), Submission.GM.hhat (t₁ - t₂) ((m : ℝ) * (N : ℝ))‖ ^ 2)
        + (Submission.LargeValues.M N) ^ (-10 : ℝ) := by
  intro ε hε
  set j : ℕ := Nat.ceil (100 / ε) with hjdef
  have hjle : 100 / ε ≤ (j : ℝ) := by rw [hjdef]; exact Nat.le_ceil _
  have hj100 : 100 ≤ ε * (j : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hjle (le_of_lt hε)
    rwa [mul_div_cancel₀ _ (ne_of_gt hε)] at h
  obtain ⟨Kd, hKdpos, hKddec⟩ := ht j
  have hKdnn : 0 ≤ Kd := le_of_lt hKdpos
  have hAzpos : 0 < Work.GM.Trace.Azero := Work.GM.Trace.Azero_pos
  have hβpos : 0 < (6:ℝ)/5 * (ε * (j:ℝ) - 1) := by nlinarith
  obtain ⟨Na, hNa⟩ := exists_nat_rpow_neg_mul_le (6 * Kd / Work.GM.Trace.Azero)
      (by positivity) ((6:ℝ)/5 * (ε * (j:ℝ) - 1)) hβpos
  refine ⟨12, by norm_num, max Na 1, ?_⟩
  intro N hN W hW hsep
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNa' : Na ≤ N := le_trans (le_max_left _ _) hN
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hM1 : 1 ≤ Submission.LargeValues.M N := Submission.LargeValues.M_ge_one hN1
  have hMpos : 0 < Submission.LargeValues.M N := Submission.LargeValues.M_pos hN1
  have hTε1 : 1 ≤ (Submission.LargeValues.M N) ^ ε := Real.one_le_rpow hM1 hε.le
  -- the decay input
  have hdec : ∀ s : ℝ, (Submission.LargeValues.M N) ^ ε ≤ |s| →
      ‖Submission.GM.hhat s 0‖ ≤ Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)) := by
    intro s hs
    have hs1 : 1 ≤ |s| := le_trans hTε1 hs
    have hsne : s ≠ 0 := by intro h0; rw [h0] at hs1; norm_num at hs1
    have hb : ‖Submission.GM.hhat s 0‖ ≤ Kd / |s|^j := by
      have h0 := hKddec s 0 hsne
      simpa using h0
    have hpow : ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
        = ((((Submission.LargeValues.M N) ^ ε) ^ j))⁻¹ := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    rw [hpow, ← div_eq_mul_inv]
    exact hb.trans (div_le_div_of_nonneg_left hKdnn (pow_pos (by positivity) j)
      (pow_le_pow_left₀ (by positivity) hs j))
  -- the numerical condition
  have hnum : 6 * Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
      * (2 * (Submission.LargeValues.M N)) ≤ 2 * Work.GM.Trace.Azero := by
    have hpow : ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
        = (Submission.LargeValues.M N) ^ (-(ε * (j:ℝ))) := by
      rw [← Real.rpow_mul (le_of_lt hMpos)]
      congr 1
      ring
    have hMpow : (Submission.LargeValues.M N) ^ (-(ε * (j:ℝ))) * (Submission.LargeValues.M N)
        = (Submission.LargeValues.M N) ^ (1 - ε * (j:ℝ)) := by
      have hexp : (1 - ε * (j:ℝ)) = 1 + (-(ε * (j:ℝ))) := by ring
      rw [hexp, Real.rpow_add hMpos, Real.rpow_one]
      ring
    have hNpow : (Submission.LargeValues.M N) ^ (1 - ε * (j:ℝ))
        = (N:ℝ) ^ (-((6:ℝ)/5 * (ε * (j:ℝ) - 1))) := by
      rw [Submission.LargeValues.M, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (N:ℝ))]
      congr 1
      ring
    rw [hpow]
    have h12 : 6 * Kd * ((Submission.LargeValues.M N) ^ (-(ε * (j:ℝ)))
        * (Submission.LargeValues.M N) * 2) ≤ 2 * Work.GM.Trace.Azero := by
      rw [hMpow, hNpow]
      have h := hNa N hNa'
      have h2 : Work.GM.Trace.Azero * (6 * Kd / Work.GM.Trace.Azero)
          * (N:ℝ) ^ (-((6:ℝ)/5 * (ε * (j:ℝ) - 1))) ≤ Work.GM.Trace.Azero * 1 := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left h (le_of_lt hAzpos)
      have h3 : Work.GM.Trace.Azero * (6 * Kd / Work.GM.Trace.Azero) = 6 * Kd := by
        field_simp
      rw [h3, mul_one] at h2
      linarith
    linarith [h12]
  -- the cardinality bound
  have hcard : (W.card : ℝ) ≤ 2 * (Submission.LargeValues.M N) := by
    have h1 : (W.card : ℝ) ≤ Submission.LargeValues.M N + 1 :=
      Commons.Analysis.Metric.one_separated_real_card_le W (Submission.LargeValues.M N)
        (le_of_lt hMpos) (fun x hx => ⟨(hW x hx).1, (hW x hx).2⟩)
        (fun x hx y hy hxy => le_trans hTε1 (hsep x hx y hy hxy))
    linarith
  -- assembling the three pieces
  have hspart := spart_two_split hxi N hN1 W hW
  have hb1 := Bg1_eq hxi N hN1 W
  have hb2 := Bg2_eq hxi N hN1 W
  have hb3 := Bg3_eq hxi N hN1 W
  have hc1 := cyc_bound1 N W ε Kd j hKdnn hdec hsep
  have hc2 := cyc_bound2 N W ε Kd j hKdnn hdec hsep
  have hc3 := cyc_bound3 N W ε Kd j hKdnn hdec hsep
  set κ : ℝ := Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)) with hκdef
  have hB : ∀ S : ℂ, ‖S‖ ≤ 2 * Work.GM.Trace.Azero * Rpair N W
      + κ * (2 * (W.card : ℝ) * Rpair N W) →
      ‖(N:ℂ)^3 * S‖ ≤ (N:ℝ)^3 * (2 * Work.GM.Trace.Azero * Rpair N W
        + κ * (2 * (W.card : ℝ) * Rpair N W)) := by
    intro S hS
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hS (by positivity)
  have hsum : ‖Submission.GM.Spart 2 N W‖ ≤
      (N:ℝ)^3 * (2 * Work.GM.Trace.Azero * Rpair N W
        + κ * (2 * (W.card : ℝ) * Rpair N W))
      + (N:ℝ)^3 * (2 * Work.GM.Trace.Azero * Rpair N W
        + κ * (2 * (W.card : ℝ) * Rpair N W))
      + (N:ℝ)^3 * (2 * Work.GM.Trace.Azero * Rpair N W
        + κ * (2 * (W.card : ℝ) * Rpair N W)) := by
    have h1 : ‖Submission.GM.Spart 2 N W‖
        ≤ ‖Bg1 N W‖ + ‖Bg2 N W‖ + ‖Bg3 N W‖ := by
      rw [hspart]
      refine (norm_add_le _ _).trans ?_
      refine add_le_add ?_ le_rfl
      exact norm_add_le _ _
    have e1 : ‖Bg1 N W‖ ≤ (N:ℝ)^3 * (2 * Work.GM.Trace.Azero * Rpair N W
        + κ * (2 * (W.card : ℝ) * Rpair N W)) := by
      rw [hb1]
      exact hB _ (by rw [hκdef]; exact hc1)
    have e2 : ‖Bg2 N W‖ ≤ (N:ℝ)^3 * (2 * Work.GM.Trace.Azero * Rpair N W
        + κ * (2 * (W.card : ℝ) * Rpair N W)) := by
      rw [hb2]
      exact hB _ (by rw [hκdef]; exact hc2)
    have e3 : ‖Bg3 N W‖ ≤ (N:ℝ)^3 * (2 * Work.GM.Trace.Azero * Rpair N W
        + κ * (2 * (W.card : ℝ) * Rpair N W)) := by
      rw [hb3]
      exact hB _ (by rw [hκdef]; exact hc3)
    linarith
  have herr : κ * (2 * (W.card : ℝ) * Rpair N W) ≤ 2 * Work.GM.Trace.Azero * Rpair N W := by
    have hcardnn : (0:ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
    have hRnn : 0 ≤ Rpair N W := Rpair_nonneg N W
    have hstep : κ * (2 * (W.card : ℝ)) ≤ 2 * Work.GM.Trace.Azero := by
      rw [hκdef]
      have h2 : 2 * (W.card : ℝ) ≤ 2 * (2 * Submission.LargeValues.M N) := by linarith
      calc Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ)) * (2 * (W.card : ℝ))
          ≤ Kd * ((Submission.LargeValues.M N) ^ ε) ^ (-(j:ℝ))
              * (2 * (2 * Submission.LargeValues.M N)) := by
            refine mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ 2 * Work.GM.Trace.Azero := by linarith [hnum]
    calc κ * (2 * (W.card : ℝ) * Rpair N W)
        = (κ * (2 * (W.card : ℝ))) * Rpair N W := by ring
      _ ≤ (2 * Work.GM.Trace.Azero) * Rpair N W :=
          mul_le_mul_of_nonneg_right hstep hRnn
      _ = 2 * Work.GM.Trace.Azero * Rpair N W := by ring
  have hmain : ‖Submission.GM.Spart 2 N W‖ ≤ 12 * (N:ℝ)^3 * Work.GM.Trace.Azero * Rpair N W := by
    have hN3 : (0:ℝ) ≤ (N:ℝ)^3 := by positivity
    have hA : (N:ℝ)^3 * (2 * Work.GM.Trace.Azero * Rpair N W
        + κ * (2 * (W.card : ℝ) * Rpair N W))
        ≤ 4 * (N:ℝ)^3 * Work.GM.Trace.Azero * Rpair N W := by
      have h2 : 2 * Work.GM.Trace.Azero * Rpair N W + κ * (2 * (W.card : ℝ) * Rpair N W)
          ≤ 4 * Work.GM.Trace.Azero * Rpair N W := by linarith [herr]
      calc (N:ℝ)^3 * (2 * Work.GM.Trace.Azero * Rpair N W
            + κ * (2 * (W.card : ℝ) * Rpair N W))
          ≤ (N:ℝ)^3 * (4 * Work.GM.Trace.Azero * Rpair N W) :=
            mul_le_mul_of_nonneg_left h2 hN3
        _ = 4 * (N:ℝ)^3 * Work.GM.Trace.Azero * Rpair N W := by ring
    linarith [hsum, hA]
  have hRHS : (∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖∑' (m : {m : ℤ // m ≠ 0}),
        Submission.GM.hhat (t₁ - t₂) ((m : ℝ) * (N : ℝ))‖ ^ 2) = Rpair N W := rfl
  have hh00 : ‖Submission.GM.hhat 0 0‖ = Work.GM.Trace.Azero := by
    rw [Work.GM.Trace.hhat_zero_zero, Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self Work.GM.Trace.Azero_nonneg]
  rw [hRHS, hh00]
  refine hmain.trans ?_
  have hT10 : (0:ℝ) ≤ (Submission.LargeValues.M N) ^ (-10 : ℝ) := by positivity
  linarith

end Work.GM.S2
