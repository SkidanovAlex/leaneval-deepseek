/-
# `Submission.Work.FIArea3.polarBox_delta_tau_sum_le` — the `Δ`-side divisor average over the
polar box, for fixed `z₁`

For every admissible `Pa`, every `φ` and every Gaussian integer `z₁` with
`|Δ(z₁,z)| ≤ 4πθN` for all `z` in the polar box,

  `Σ_{z ∈ box} τ(|Δ(z₁,z)|) ≤ C·(gcd(z₁.re,z₁.im)+2)·(u² + u·M^{1/4} + M^{1/4})·(log N + 2)^{1024}`

with `u = θ√N`, `M = 4πθN`.

The three terms are the three pieces of the divisor-sum route:

* FI Lemma 2.2 with `k = 4` turns `τ(m)`, for `m ≤ K⁴` with `K = ⌈M^{1/4}⌉`, into
  `τ(m) ≤ 256 Σ_{d ≤ K, d ∣ m} τ(d)^8` (the truncated form `tau_le_sum_Icc_eight`);
* swapping the (finite) sums turns the average into
  `256 Σ_{d ≤ K} τ(d)^8 · #{z ∈ box : d ∣ |Δ(z₁,z)|}`;
* the per-`d` count `≤ 401(u²·gcd(G,d)/d + u + 1)` (`G = gcd(z₁.re,z₁.im)`) — the delegated
  lemma `card_polarBox_filter_dvd_absDelta_noBox` — gives the main term `u²` (weighted by
  `Σ τ(d)^8/d ≤ C(log K+2)^{256}`), the term `u·M^{1/4}` and the term `M^{1/4}` (weighted by
  `Σ τ(d)^8 ≤ C·K·(log K+2)^{256}`, `K ≤ 2M^{1/4}`).

Since `gcd(G,d) ≤ G ≤ G+2`, no product estimate on `G` is needed.
-/
import Mathlib
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.lemma_2_2
import Submission.Work.FIArea2.sum_tau_pow_div_le
import Submission.Work.FIArea2.sum_tau_pow_le
import Submission.Work.FIArea3.card_polarBox_filter_dvd_absDelta_noBox

set_option maxHeartbeats 800000

namespace Work.FIArea3

open Finset Work.FIPlan
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## 1. Two elementary auxiliary facts -/

lemma log_four_pb : Real.log ((4 : ℕ) : ℝ) = 2 * Real.log (2 : ℝ) := by
  rw [show ((4 : ℕ) : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
  norm_num

lemma exp_eq_eight_pb : (((4 : ℕ) : ℝ) * Real.log ((4 : ℕ) : ℝ) / Real.log (2 : ℝ)) = ((8 : ℕ) : ℝ) := by
  rw [log_four_pb]
  have h2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

/-- `θ ≤ 1` for every admissible set-up. -/
theorem theta_le_one_polarBox (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
  have hlog : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    have h1 : Real.log 3 ≤ Real.log (Pa.x : ℝ) := Real.log_le_log (by norm_num) hx3
    linarith
  have hA'0 : (0 : ℝ) ≤ Pa.A' := by
    have h : (2 : ℝ) ^ (20 : ℕ) ≤ Pa.A' := by linarith [Pa.hA', Pa.hA]
    positivity
  rw [Pa.hθ]
  exact Real.rpow_le_one_of_one_le_of_nonpos hlog (by linarith)

/-! ## 2. The truncated FI divisor bound (`k = 4`) -/

/-- **FI Lemma 2.2 with `k = 4`, truncated form.**  For `m ≤ K⁴`,
`τ(m) ≤ 256 · Σ_{1 ≤ d ≤ K, d ∣ m} τ(d)⁸`. -/
theorem tau_le_sum_Icc_eight (m K : ℕ) (h : (m : ℝ) ≤ (K : ℝ) ^ (4 : ℕ)) :
    ((m.divisors.card : ℝ))
      ≤ 256 * ∑ d ∈ Finset.Icc 1 K,
          (if d ∣ m then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have h0 : (0 : ℝ) ≤ ∑ d ∈ Finset.Icc 1 K,
        (if d ∣ 0 then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) :=
      Finset.sum_nonneg (fun i _ => by split_ifs <;> positivity)
    rw [Nat.divisors_zero]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (by norm_num) h0
  · obtain ⟨d, hdvd, hdk, hbound⟩ := Work.FIArea3.lemma_2_2 (k := 4) (by norm_num) hm
    rw [exp_eq_eight_pb] at hbound
    rw [Real.rpow_natCast] at hbound
    have hd4 : ((d : ℝ)) ^ 4 ≤ (m : ℝ) := by exact_mod_cast hdk
    have hdK4 : ((d : ℝ)) ^ 4 ≤ (K : ℝ) ^ 4 := le_trans hd4 h
    have hdK : d ≤ K := by
      have := (pow_le_pow_iff_left₀ (show (0 : ℝ) ≤ (d : ℝ) by positivity)
        (show (0 : ℝ) ≤ (K : ℝ) by positivity) (by norm_num : (4 : ℕ) ≠ 0)).mp hdK4
      exact_mod_cast this
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd hm
    have hmem : d ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨hd1, hdK⟩
    have hsingle : (if d ∣ m then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0)
        ≤ ∑ d' ∈ Finset.Icc 1 K,
            (if d' ∣ m then ((((d'.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) :=
      Finset.single_le_sum (s := Finset.Icc 1 K)
        (f := fun d' => if d' ∣ m then ((((d'.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0)
        (fun i _ => by split_ifs <;> positivity) hmem
    rw [if_pos hdvd] at hsingle
    have h2 : (2 * (d.divisors.card : ℝ)) ^ (8 : ℕ) = 256 * ((d.divisors.card : ℝ)) ^ (8 : ℕ) := by
      ring
    rw [h2] at hbound
    calc (m.divisors.card : ℝ) ≤ 256 * ((d.divisors.card : ℝ)) ^ (8 : ℕ) := hbound
      _ ≤ 256 * ∑ d' ∈ Finset.Icc 1 K,
            (if d' ∣ m then ((((d'.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) :=
          mul_le_mul_of_nonneg_left hsingle (by norm_num)

/-! ## 3. The per-`z₁` `Δ`-count (delegated)

The count is `Work.FIArea3.card_polarBox_filter_dvd_absDelta_noBox`, proved in
`Submission/Work/FIArea3/card_polarBox_filter_dvd_absDelta_noBox.lean` and imported above. -/

/-! ## 4. Interchange of the two finite sums -/

/-- The `if`-sum over the box is the count of the filtered set (specialised to the concrete
divisibility condition `d ∣ m z`, so that the `Decidable` instances match those of the goal). -/
theorem sum_ite_div_mul_card (s : Finset GaussianInt) (t : Finset ℕ) (c : ℕ → ℝ)
    (m : GaussianInt → ℕ) :
    (∑ z ∈ s, ∑ d ∈ t, (if d ∣ m z then c d else 0))
      = ∑ d ∈ t, c d * (((s.filter (fun z => d ∣ m z)).card : ℕ) : ℝ) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have h1 : (∑ z ∈ s, (if d ∣ m z then c d else 0))
      = ∑ _z ∈ s.filter (fun z => d ∣ m z), c d :=
    (Finset.sum_filter (s := s) (p := fun z => d ∣ m z) (f := fun _ => c d)).symm
  rw [h1, Finset.sum_const, nsmul_eq_mul]
  ring

/-! ## 5. The final real-arithmetic step -/

/-- The final bookkeeping: from `Z ≤ 256·401·(u²G·S1 + u·S2 + S2)`, `S1 ≤ C1·P`,
`S2 ≤ C2·K·P`, `K ≤ 2D^{1/4}`, `P ≤ W·L` we obtain the target shape (with the numeral
`W = 5^{1024}` kept opaque, so that `ring` never expands it). -/
theorem delta_tau_sum_arith (C1 C2 u D G L P K S1 S2 Z W : ℝ)
    (hC1 : 0 < C1) (hC2 : 0 < C2) (hu : 0 ≤ u) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hL : 0 ≤ L) (hW : 0 ≤ W) (hP0 : 0 ≤ P) (hPL : P ≤ W * L)
    (hK : K ≤ 2 * D ^ ((1 : ℝ) / 4))
    (hS1 : S1 ≤ C1 * P) (hS2 : S2 ≤ C2 * K * P)
    (hZ : Z ≤ 256 * 401 * (u ^ 2 * G * S1 + u * S2 + S2)) :
    Z ≤ 256 * 401 * W * (C1 + 2 * C2 + 1) * (G + 2)
        * (u ^ 2 * L + u * D ^ ((1 : ℝ) / 4) * L + D ^ ((1 : ℝ) / 4) * L) := by
  have hd14 : 0 ≤ D ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hD _
  have hC0 : 0 < C1 + 2 * C2 + 1 := by linarith
  have hC0nn : 0 ≤ C1 + 2 * C2 + 1 := le_of_lt hC0
  have hWL : 0 ≤ W * L := mul_nonneg hW hL
  have hG2 : 1 ≤ G + 2 := by linarith
  have hg1 : G * C1 ≤ (G + 2) * (C1 + 2 * C2 + 1) := by
    have h1 : G * C1 ≤ G * (C1 + 2 * C2 + 1) := mul_le_mul_of_nonneg_left (by linarith) hG
    have h2 : G * (C1 + 2 * C2 + 1) ≤ (G + 2) * (C1 + 2 * C2 + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) hC0nn
    linarith
  have hg2 : 2 * C2 ≤ (G + 2) * (C1 + 2 * C2 + 1) := by
    have h1 : 2 * C2 ≤ C1 + 2 * C2 + 1 := by linarith
    have h2 : C1 + 2 * C2 + 1 ≤ (G + 2) * (C1 + 2 * C2 + 1) := by
      have := mul_le_mul_of_nonneg_right hG2 hC0nn
      linarith
    linarith
  have e1 : u ^ 2 * G * S1 ≤ W * L * ((C1 + 2 * C2 + 1) * (G + 2) * u ^ 2) := by
    calc u ^ 2 * G * S1 ≤ u ^ 2 * G * (C1 * P) :=
          mul_le_mul_of_nonneg_left hS1 (by positivity)
      _ ≤ u ^ 2 * G * (C1 * (W * L)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPL (le_of_lt hC1))
            (by positivity)
      _ = u ^ 2 * (G * C1) * (W * L) := by ring
      _ ≤ u ^ 2 * ((G + 2) * (C1 + 2 * C2 + 1)) * (W * L) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg1 (by positivity)) hWL
      _ = W * L * ((C1 + 2 * C2 + 1) * (G + 2) * u ^ 2) := by ring
  have e2 : u * S2 ≤ W * L * ((C1 + 2 * C2 + 1) * (G + 2) * (u * D ^ ((1 : ℝ) / 4))) := by
    calc u * S2 ≤ u * (C2 * K * P) := mul_le_mul_of_nonneg_left hS2 hu
      _ ≤ u * (C2 * (2 * D ^ ((1 : ℝ) / 4)) * P) := by
          apply mul_le_mul_of_nonneg_left _ hu
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (le_of_lt hC2)) hP0
      _ ≤ u * (C2 * (2 * D ^ ((1 : ℝ) / 4)) * (W * L)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPL (by positivity)) hu
      _ = u * D ^ ((1 : ℝ) / 4) * (2 * C2) * (W * L) := by ring
      _ ≤ u * D ^ ((1 : ℝ) / 4) * ((G + 2) * (C1 + 2 * C2 + 1)) * (W * L) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hg2 (mul_nonneg hu hd14)) hWL
      _ = W * L * ((C1 + 2 * C2 + 1) * (G + 2) * (u * D ^ ((1 : ℝ) / 4))) := by ring
  have e3 : S2 ≤ W * L * ((C1 + 2 * C2 + 1) * (G + 2) * D ^ ((1 : ℝ) / 4)) := by
    calc S2 ≤ C2 * K * P := hS2
      _ ≤ C2 * (2 * D ^ ((1 : ℝ) / 4)) * P :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (le_of_lt hC2)) hP0
      _ ≤ C2 * (2 * D ^ ((1 : ℝ) / 4)) * (W * L) :=
          mul_le_mul_of_nonneg_left hPL (by positivity)
      _ = D ^ ((1 : ℝ) / 4) * (2 * C2) * (W * L) := by ring
      _ ≤ D ^ ((1 : ℝ) / 4) * ((G + 2) * (C1 + 2 * C2 + 1)) * (W * L) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg2 hd14) hWL
      _ = W * L * ((C1 + 2 * C2 + 1) * (G + 2) * D ^ ((1 : ℝ) / 4)) := by ring
  have hsum : u ^ 2 * G * S1 + u * S2 + S2
      ≤ W * L * ((C1 + 2 * C2 + 1) * (G + 2) * u ^ 2)
        + W * L * ((C1 + 2 * C2 + 1) * (G + 2) * (u * D ^ ((1 : ℝ) / 4)))
        + W * L * ((C1 + 2 * C2 + 1) * (G + 2) * D ^ ((1 : ℝ) / 4)) :=
    add_le_add (add_le_add e1 e2) e3
  have hfac : (0 : ℝ) ≤ 256 * 401 := by norm_num
  calc Z ≤ 256 * 401 * (u ^ 2 * G * S1 + u * S2 + S2) := hZ
    _ ≤ 256 * 401 * (W * L * ((C1 + 2 * C2 + 1) * (G + 2) * u ^ 2)
          + W * L * ((C1 + 2 * C2 + 1) * (G + 2) * (u * D ^ ((1 : ℝ) / 4)))
          + W * L * ((C1 + 2 * C2 + 1) * (G + 2) * D ^ ((1 : ℝ) / 4))) :=
        mul_le_mul_of_nonneg_left hsum hfac
    _ = 256 * 401 * W * (C1 + 2 * C2 + 1) * (G + 2)
          * (u ^ 2 * L + u * D ^ ((1 : ℝ) / 4) * L + D ^ ((1 : ℝ) / 4) * L) := by ring

/-! ## 6. A logarithmic comparison used at the end -/

/-- If `0 < K ≤ 2D^{1/4}`, `0 < D ≤ 16N` and `1 ≤ N`, then `log K + 2 ≤ 5(log N + 2)`.
Stated with a light context so that the arithmetic stays cheap. -/
lemma log_le_five_log (K D N : ℝ) (hKpos : 0 < K) (hKle : K ≤ 2 * D ^ ((1 : ℝ) / 4))
    (hDpos : 0 < D) (hDle : D ≤ 16 * N) (hN1 : 1 ≤ N) :
    Real.log K + 2 ≤ 5 * (Real.log N + 2) := by
  have hlogKle : Real.log K ≤ Real.log (2 * D ^ ((1 : ℝ) / 4)) := Real.log_le_log hKpos hKle
  have hlog2D : Real.log (2 * D ^ ((1 : ℝ) / 4)) = Real.log 2 + (1 / 4) * Real.log D := by
    rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hDpos _)), Real.log_rpow hDpos]
  have hlogD : Real.log D ≤ Real.log (16 * N) := Real.log_le_log hDpos hDle
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hlog16N : Real.log (16 * N) = Real.log 16 + Real.log N := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)]
  have hlog16 : Real.log 16 ≤ 16 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16)
    linarith [h]
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith [h]
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  linarith [hlogKle, hlog2D, hlogD, hlog16N, hlog16, hlog2, hlogN0]

/-! ## 7. The main theorem -/

theorem polarBox_delta_tau_sum_le :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ) (z₁ : GaussianInt),
      (∀ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
          (Work.FIPlan.absDelta z₁ z : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N) →
      (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
          (((Work.FIPlan.absDelta z₁ z).divisors.card : ℕ) : ℝ))
        ≤ C * ((Nat.gcd z₁.re.natAbs z₁.im.natAbs : ℝ) + 2)
            * ((Pa.θ * Real.sqrt Pa.N) ^ 2 * (Real.log Pa.N + 2) ^ (1024 : ℕ)
              + (Pa.θ * Real.sqrt Pa.N) * (4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4)
                  * (Real.log Pa.N + 2) ^ (1024 : ℕ)
              + (4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4)
                  * (Real.log Pa.N + 2) ^ (1024 : ℕ)) := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.FIArea2.sum_tau_pow_div_le 8
  obtain ⟨C2, hC2pos, hC2⟩ := Work.FIArea2.sum_tau_pow_le 8
  refine ⟨256 * 401 * (5 : ℝ) ^ (1024 : ℕ) * (C1 + 2 * C2 + 1), ?_, ?_⟩
  · exact mul_pos (mul_pos (mul_pos (by norm_num) (by norm_num))
      (pow_pos (by norm_num) _)) (by linarith [hC1pos, hC2pos])
  · intro Pa φ z₁ hhyp
    set W : ℝ := (5 : ℝ) ^ (1024 : ℕ) with hW
    have hW0 : 0 ≤ W := by rw [hW]; exact le_of_lt (pow_pos (by norm_num) _)
    have hC0pos : 0 < C1 + 2 * C2 + 1 := by linarith [hC1pos, hC2pos]
    have hKconst : 0 < 256 * 401 * W * (C1 + 2 * C2 + 1) :=
      mul_pos (mul_pos (mul_pos (by norm_num) (by norm_num)) (by rw [hW]; positivity)) hC0pos
    have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
    have hNpos : (0 : ℝ) < Pa.N := lt_of_lt_of_le zero_lt_one hN1
    have hN0 : (0 : ℝ) ≤ Pa.N := le_of_lt hNpos
    have hlogN0 : 0 ≤ Real.log Pa.N := Real.log_nonneg hN1
    have hb1 : (1 : ℝ) ≤ Real.log Pa.N + 2 := by linarith [hlogN0]
    have hDpos0 : 0 < 4 * Real.pi * Pa.θ * Pa.N :=
      mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) Pa.hθ0) hNpos
    set u : ℝ := Pa.θ * Real.sqrt Pa.N with hu
    set D : ℝ := 4 * Real.pi * Pa.θ * Pa.N with hD
    set G : ℝ := (Nat.gcd z₁.re.natAbs z₁.im.natAbs : ℝ) with hG
    set L : ℝ := (Real.log Pa.N + 2) ^ (1024 : ℕ) with hL
    have hu0 : 0 ≤ u := by rw [hu]; exact mul_nonneg (le_of_lt Pa.hθ0) (Real.sqrt_nonneg _)
    have hDpos : 0 < D := by rw [hD]; exact hDpos0
    have hG0 : 0 ≤ G := by rw [hG]; exact Nat.cast_nonneg _
    have hL0 : 0 ≤ L := by rw [hL]; exact pow_nonneg (le_trans zero_le_one hb1) _
    have hDnn : 0 ≤ D := le_of_lt hDpos
    have hd14 : 0 ≤ D ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hDnn _
    have hRHSnn : 0 ≤ 256 * 401 * W * (C1 + 2 * C2 + 1) * (G + 2)
        * (u ^ 2 * L + u * D ^ ((1 : ℝ) / 4) * L + D ^ ((1 : ℝ) / 4) * L) := by
      have h1 : 0 ≤ u ^ 2 * L := mul_nonneg (sq_nonneg u) hL0
      have h2 : 0 ≤ u * D ^ ((1 : ℝ) / 4) * L := mul_nonneg (mul_nonneg hu0 hd14) hL0
      have h3 : 0 ≤ D ^ ((1 : ℝ) / 4) * L := mul_nonneg hd14 hL0
      have hbr : 0 ≤ u ^ 2 * L + u * D ^ ((1 : ℝ) / 4) * L + D ^ ((1 : ℝ) / 4) * L :=
        add_nonneg (add_nonneg h1 h2) h3
      have hG2 : 0 ≤ G + 2 := add_nonneg hG0 (by norm_num)
      exact mul_nonneg (mul_nonneg (le_of_lt hKconst) hG2) hbr
    rcases eq_or_ne z₁ 0 with hz1 | hz1
    · subst hz1
      have hzero : ∀ z ∈ Work.FIArea3.polarBoxFinset Pa φ, Work.FIPlan.absDelta 0 z = 0 := by
        intro z hz
        simp [Work.FIPlan.absDelta, Work.FIPlan.Delta]
      have hsum0 : (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
          (((Work.FIPlan.absDelta 0 z).divisors.card : ℕ) : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro z hz
        rw [hzero z hz, Nat.divisors_zero]
        simp
      rw [hsum0]
      exact hRHSnn
    · have hGpos : 0 < Nat.gcd z₁.re.natAbs z₁.im.natAbs := by
        rcases Nat.eq_zero_or_pos (Nat.gcd z₁.re.natAbs z₁.im.natAbs) with h0 | hpos
        · exfalso
          obtain ⟨h1, h2⟩ := Nat.gcd_eq_zero_iff.mp h0
          exact hz1 (Zsqrtd.ext (Int.natAbs_eq_zero.mp h1) (Int.natAbs_eq_zero.mp h2))
        · exact hpos
      have hhypD : ∀ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
          (Work.FIPlan.absDelta z₁ z : ℝ) ≤ D := by
        intro z hz
        rw [hD]
        exact hhyp z hz
      by_cases hsmall : D < 1
      · have hzero : ∀ z ∈ Work.FIArea3.polarBoxFinset Pa φ, Work.FIPlan.absDelta z₁ z = 0 := by
          intro z hz
          have h1 : ((Work.FIPlan.absDelta z₁ z : ℕ) : ℝ) < 1 :=
            lt_of_le_of_lt (hhypD z hz) hsmall
          exact Nat.cast_lt_one.mp h1
        have hsum0 : (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
            (((Work.FIPlan.absDelta z₁ z).divisors.card : ℕ) : ℝ)) = 0 := by
          apply Finset.sum_eq_zero
          intro z hz
          rw [hzero z hz, Nat.divisors_zero]
          simp
        rw [hsum0]
        exact hRHSnn
      · push_neg at hsmall
        set K : ℕ := Nat.ceil (D ^ ((1 : ℝ) / 4)) with hK
        have hKge : D ^ ((1 : ℝ) / 4) ≤ (K : ℝ) := Nat.le_ceil _
        have hD14_1 : 1 ≤ D ^ ((1 : ℝ) / 4) := Real.one_le_rpow hsmall (by norm_num)
        have hK1 : 1 ≤ K := by
          have h1 : (1 : ℝ) ≤ (K : ℝ) := le_trans hD14_1 hKge
          exact_mod_cast h1
        have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
        have hKlt : (K : ℝ) ≤ D ^ ((1 : ℝ) / 4) + 1 :=
          le_of_lt (Nat.ceil_lt_add_one hd14)
        have hKle : (K : ℝ) ≤ 2 * D ^ ((1 : ℝ) / 4) := by
          calc (K : ℝ) ≤ D ^ ((1 : ℝ) / 4) + 1 := hKlt
            _ ≤ D ^ ((1 : ℝ) / 4) + D ^ ((1 : ℝ) / 4) := add_le_add le_rfl hD14_1
            _ = 2 * D ^ ((1 : ℝ) / 4) := by ring
        have hDpow : (D ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = D := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hDnn]
          norm_num
        have hπ4 : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
        have hθ1 : Pa.θ ≤ 1 := theta_le_one_polarBox Pa
        have h4N : (0 : ℝ) ≤ 4 * Pa.N := mul_nonneg (by norm_num) hN0
        have hDle16 : D ≤ 16 * Pa.N := by
          rw [hD]
          calc 4 * Real.pi * Pa.θ * Pa.N = (4 * Pa.N) * (Pa.θ * Real.pi) := by ring
            _ ≤ (4 * Pa.N) * (1 * 4) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul hθ1 hπ4 (le_of_lt Real.pi_pos) (by norm_num)) h4N
            _ = 16 * Pa.N := by ring
        have hlogK : Real.log (K : ℝ) + 2 ≤ 5 * (Real.log Pa.N + 2) :=
          log_le_five_log (K : ℝ) D Pa.N hKpos hKle hDpos hDle16 hN1
        set P : ℝ := (Real.log (K : ℝ) + 2) ^ (256 : ℕ) with hP
        have hlogK0 : 0 ≤ Real.log (K : ℝ) + 2 :=
          add_nonneg (Real.log_nonneg (by exact_mod_cast hK1)) (by norm_num)
        have hP0 : 0 ≤ P := by rw [hP]; exact pow_nonneg hlogK0 _
        have hPL : P ≤ W * L := by
          rw [hP, hL, hW]
          have h5 : (5 : ℝ) ^ (256 : ℕ) ≤ (5 : ℝ) ^ (1024 : ℕ) :=
            pow_le_pow_right₀ (by norm_num) (by norm_num)
          have hLn : (Real.log Pa.N + 2) ^ (256 : ℕ) ≤ (Real.log Pa.N + 2) ^ (1024 : ℕ) :=
            pow_le_pow_right₀ hb1 (by norm_num)
          calc (Real.log (K : ℝ) + 2) ^ (256 : ℕ)
              ≤ (5 * (Real.log Pa.N + 2)) ^ (256 : ℕ) := pow_le_pow_left₀ hlogK0 hlogK 256
            _ = (5 : ℝ) ^ (256 : ℕ) * (Real.log Pa.N + 2) ^ (256 : ℕ) := by rw [mul_pow]
            _ ≤ (5 : ℝ) ^ (1024 : ℕ) * (Real.log Pa.N + 2) ^ (256 : ℕ) :=
                mul_le_mul_of_nonneg_right h5 (pow_nonneg (le_trans zero_le_one hb1) 256)
            _ ≤ (5 : ℝ) ^ (1024 : ℕ) * (Real.log Pa.N + 2) ^ (1024 : ℕ) :=
                mul_le_mul_of_nonneg_left hLn (pow_nonneg (by norm_num) 1024)
        set S1 : ℝ := ∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) / (d : ℝ)
          with hS1def
        set S2 : ℝ := ∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) with hS2def
        have hS1le : S1 ≤ C1 * P := by
          rw [hS1def, hP]
          exact hC1 K
        have hS2le : S2 ≤ C2 * (K : ℝ) * P := by
          rw [hS2def, hP]
          exact hC2 K
        have hpt : ∀ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
            (((Work.FIPlan.absDelta z₁ z).divisors.card : ℕ) : ℝ)
              ≤ 256 * ∑ d ∈ Finset.Icc 1 K,
                  (if d ∣ Work.FIPlan.absDelta z₁ z
                    then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) := by
          intro z hz
          apply tau_le_sum_Icc_eight
          calc ((Work.FIPlan.absDelta z₁ z : ℕ) : ℝ) ≤ D := hhypD z hz
            _ = (D ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := hDpow.symm
            _ ≤ ((K : ℝ)) ^ (4 : ℕ) := pow_le_pow_left₀ hd14 hKge 4
        have hswap := sum_ite_div_mul_card (Work.FIArea3.polarBoxFinset Pa φ) (Finset.Icc 1 K)
          (fun d => ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)))
          (fun z => Work.FIPlan.absDelta z₁ z)
        have hstep1 : (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
              (((Work.FIPlan.absDelta z₁ z).divisors.card : ℕ) : ℝ))
            ≤ 256 * ∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
                * ((((Work.FIArea3.polarBoxFinset Pa φ).filter
                      (fun z => d ∣ Work.FIPlan.absDelta z₁ z)).card : ℕ) : ℝ) := by
          calc (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
                (((Work.FIPlan.absDelta z₁ z).divisors.card : ℕ) : ℝ))
              ≤ ∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
                  256 * ∑ d ∈ Finset.Icc 1 K,
                    (if d ∣ Work.FIPlan.absDelta z₁ z
                      then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) :=
                Finset.sum_le_sum hpt
            _ = 256 * (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ, ∑ d ∈ Finset.Icc 1 K,
                    (if d ∣ Work.FIPlan.absDelta z₁ z
                      then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0)) :=
                (Finset.mul_sum _ _ 256).symm
            _ = 256 * ∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
                * ((((Work.FIArea3.polarBoxFinset Pa φ).filter
                      (fun z => d ∣ Work.FIPlan.absDelta z₁ z)).card : ℕ) : ℝ) :=
                congrArg (fun x => 256 * x) hswap
        have hstep2 : (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
                * ((((Work.FIArea3.polarBoxFinset Pa φ).filter
                      (fun z => d ∣ Work.FIPlan.absDelta z₁ z)).card : ℕ) : ℝ))
            ≤ ∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
                * (401 * (u ^ 2 * (G / (d : ℝ)) + u + 1)) := by
          apply Finset.sum_le_sum
          intro d hd
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
          have hcnt := card_polarBox_filter_dvd_absDelta_noBox Pa φ z₁ d hd1
          have hcntu : ((((Work.FIArea3.polarBoxFinset Pa φ).filter
                (fun z => d ∣ Work.FIPlan.absDelta z₁ z)).card : ℕ) : ℝ)
              ≤ 401 * (u ^ 2 * (((Nat.gcd (Nat.gcd z₁.re.natAbs z₁.im.natAbs) d : ℕ) : ℝ)
                    / (d : ℝ)) + u + 1) := by
            rw [hu]
            exact hcnt
          have hgle : (((Nat.gcd (Nat.gcd z₁.re.natAbs z₁.im.natAbs) d : ℕ) : ℝ)) ≤ G := by
            rw [hG]
            exact_mod_cast Nat.gcd_le_left d hGpos
          have hdiv : (((Nat.gcd (Nat.gcd z₁.re.natAbs z₁.im.natAbs) d : ℕ) : ℝ) / (d : ℝ))
              ≤ G / (d : ℝ) := div_le_div_of_nonneg_right hgle (le_of_lt hdpos)
          have hinner : u ^ 2 * (((Nat.gcd (Nat.gcd z₁.re.natAbs z₁.im.natAbs) d : ℕ) : ℝ)
                  / (d : ℝ)) + u + 1 ≤ u ^ 2 * (G / (d : ℝ)) + u + 1 :=
            add_le_add (add_le_add (mul_le_mul_of_nonneg_left hdiv (sq_nonneg u)) le_rfl) le_rfl
          have hc8 : 0 ≤ ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) := by positivity
          calc ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
                * ((((Work.FIArea3.polarBoxFinset Pa φ).filter
                      (fun z => d ∣ Work.FIPlan.absDelta z₁ z)).card : ℕ) : ℝ)
              ≤ ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
                * (401 * (u ^ 2 * (((Nat.gcd (Nat.gcd z₁.re.natAbs z₁.im.natAbs) d : ℕ) : ℝ)
                      / (d : ℝ)) + u + 1)) := mul_le_mul_of_nonneg_left hcntu hc8
            _ ≤ ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
                * (401 * (u ^ 2 * (G / (d : ℝ)) + u + 1)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner (by norm_num)) hc8
        have hstep3 : (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
                * (401 * (u ^ 2 * (G / (d : ℝ)) + u + 1)))
            = 401 * (u ^ 2 * G * S1 + u * S2 + S2) := by
          have hLHS : (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
                * (401 * (u ^ 2 * (G / (d : ℝ)) + u + 1)))
              = ∑ d ∈ Finset.Icc 1 K,
                  ((401 * u ^ 2 * G) * (((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) / (d : ℝ))
                    + (401 * u) * ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
                    + 401 * ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))) := by
            apply Finset.sum_congr rfl
            intro d hd
            ring
          rw [hLHS, Finset.sum_add_distrib, Finset.sum_add_distrib, hS1def, hS2def,
            ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
          ring
        have hZ : (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
              (((Work.FIPlan.absDelta z₁ z).divisors.card : ℕ) : ℝ))
            ≤ 256 * 401 * (u ^ 2 * G * S1 + u * S2 + S2) := by
          calc (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
                (((Work.FIPlan.absDelta z₁ z).divisors.card : ℕ) : ℝ))
              ≤ 256 * ∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
                  * ((((Work.FIArea3.polarBoxFinset Pa φ).filter
                        (fun z => d ∣ Work.FIPlan.absDelta z₁ z)).card : ℕ) : ℝ) := hstep1
            _ ≤ 256 * ∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
                  * (401 * (u ^ 2 * (G / (d : ℝ)) + u + 1)) :=
                mul_le_mul_of_nonneg_left hstep2 (by norm_num)
            _ = 256 * (401 * (u ^ 2 * G * S1 + u * S2 + S2)) := by rw [hstep3]
            _ = 256 * 401 * (u ^ 2 * G * S1 + u * S2 + S2) := by ring
        exact delta_tau_sum_arith C1 C2 u D G L P (K : ℝ) S1 S2 _ W
          hC1pos hC2pos hu0 hDnn hG0 hL0 hW0 hP0 hPL hKle hS1le hS2le hZ

end

end Work.FIArea3
