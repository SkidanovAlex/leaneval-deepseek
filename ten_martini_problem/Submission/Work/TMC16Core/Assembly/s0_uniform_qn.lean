import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Assembly.S0
import Submission.Work.TMC16Core.Core.irrat_blk_nr
import Submission.Work.TMC16Core.Core.uni_nonres3_support
import Submission.Work.TMC16Core.Core.blk_log_erase_ge
import Submission.Work.TMC16Core.Core.irrat_block_gen
import Submission.Work.TMC16Core.Core.irrat_blk_shift
import Submission.Work.TMC16Core.Core.uni_res5
import Submission.Work.TMC16Core.Core.uni_nonres3_blkle
import Submission.Work.TMC16Core.NrFinal.sep_small
import Submission.Work.TMC16Core.Assembly.uniform_of_sum_bounds_gen
import Submission.Work.TMC16Core.Assembly.s0qn_blk0
import Submission.Work.TMC16Core.Assembly.s0qn_cluster
import Submission.Work.TMC16Core.Assembly.s0qn_blk_erase_ge
import Submission.Work.TMC16Core.Assembly.s0qn_cos_ne

set_option maxHeartbeats 1600000

namespace Work.TMC16Core.Assembly

open Work.TMC16Core

noncomputable section

/-- The upper block bound with an arbitrary erased point (shifted shape). -/
private lemma s0qn_blk_bound_priv {L : ℕ} {α ξ : ℝ} {p d qr : ℤ} {Lsh : ℤ → ℤ} {B : ℝ}
    (hL : 1 ≤ L)
    (hblk : ∀ (k₀ : ℤ), k₀ ∈ Finset.Icc p (p + (L : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (L : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + ((k + Lsh k * qr : ℤ) : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + ((k₀ + Lsh k₀ * qr : ℤ) : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + ((k + Lsh k * qr : ℤ) : ℝ) * α))|
        + ((L : ℝ) - 1) * Real.log 2| ≤ B)
    (hnz : ∀ i ∈ Finset.Icc p (p + (L : ℤ) - 1), i ≠ d →
      Real.sin (Real.pi * (ξ + ((i + Lsh i * qr : ℤ) : ℝ) * α)) ≠ 0) :
    ∑ i ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase d,
        Real.log |Real.sin (Real.pi * (ξ + ((i + Lsh i * qr : ℤ) : ℝ) * α))|
      ≤ -(((L : ℝ) - 1) * Real.log 2) + B := by
  classical
  set Bset : Finset ℤ := Finset.Icc p (p + (L : ℤ) - 1) with hB
  set f : ℤ → ℝ :=
    fun i => Real.log |Real.sin (Real.pi * (ξ + ((i + Lsh i * qr : ℤ) : ℝ) * α))| with hf
  have hne : Bset.Nonempty := by
    refine ⟨p, ?_⟩
    rw [hB, Finset.mem_Icc]
    have : (1 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
    omega
  obtain ⟨k₀, hk₀, hk₀min⟩ :=
    Finset.exists_min_image Bset
      (fun k => |Real.sin (Real.pi * (ξ + ((k + Lsh k * qr : ℤ) : ℝ) * α))|) hne
  have hb := hblk k₀ hk₀ (fun k hk => hk₀min k hk)
  have hS : ∑ k ∈ Bset.erase k₀, f k ≤ -(((L : ℝ) - 1) * Real.log 2) + B := by
    have h2 := (abs_le.mp hb).2
    simp only [hf]
    linarith
  have hcomp : ∑ i ∈ Bset.erase d, f i ≤ ∑ i ∈ Bset.erase k₀, f i := by
    rcases eq_or_ne d k₀ with hd | hd
    · rw [hd]
    · by_cases hdB : d ∈ Bset
      · have hkd : f k₀ ≤ f d := by
          have hk0nz : Real.sin (Real.pi * (ξ + ((k₀ + Lsh k₀ * qr : ℤ) : ℝ) * α)) ≠ 0 :=
            hnz k₀ hk₀ (Ne.symm hd)
          simp only [hf]
          exact Core.log_abs_sin_mono hk0nz (hk₀min d hdB)
        have h1 := Finset.sum_erase_add Bset f hdB
        have h2 := Finset.sum_erase_add Bset f hk₀
        linarith
      · have he : Bset.erase d = Bset := Finset.erase_eq_of_notMem hdB
        rw [he]
        have h1 := Finset.sum_erase_add Bset f hk₀
        have hk0le : f k₀ ≤ 0 := by simp only [hf]; exact Core.log_abs_sin_nonpos _
        linarith
  linarith [hcomp, hS]

/-- Separation of distinct sites of the `s = 0` windows: `1/(8 q n) ≤ ‖(i-k)α‖`. -/
private lemma s0qn_sep_priv {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n U : ℕ} {a m : ℤ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) →
      Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    (hn : 1 ≤ n)
    (h2U : 2 * U ≤ q n)
    (hmq : m ≠ 0 → 10 * (|m| + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    {i k : ℤ}
    (hi : i ∈ Work.TMC16Core.Assembly.W1s0 a U ∪
        Work.TMC16Core.Assembly.W2s0 a U (q n) (m * (q n : ℤ)))
    (hk : k ∈ Work.TMC16Core.Assembly.W1s0 a U ∪
        Work.TMC16Core.Assembly.W2s0 a U (q n) (m * (q n : ℤ)))
    (hne : i ≠ k) :
    1 / (8 * (q n : ℝ)) ≤ Work.TMC16Core.fracDist (((i - k : ℤ) : ℝ) * α) := by
  have hQ : (0 : ℝ) < (q n : ℝ) := by have := hqpos n; exact_mod_cast this
  have h8 : (1 : ℝ) / (8 * (q n : ℝ)) ≤ 1 / (2 * (q n : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith [hQ]
  have h8' : (1 : ℝ) / (8 * (q n : ℝ))
      ≤ 1 / (2 * (q n : ℝ)) - 1 / (10 * (q n : ℝ)) := by
    field_simp
    norm_num
  have hsepAll : ∀ d : ℤ, d ≠ 0 → |d| < (q n : ℤ) →
      (1 : ℝ) / (2 * (q n : ℝ)) ≤ Work.TMC16Core.fracDist ((d : ℝ) * α) :=
    fun d hd hdn => NrFinal.sep_small hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hd hdn
  have hshift : Work.TMC16Core.fracDist (((m * (q n : ℤ) : ℤ) : ℝ) * α)
      ≤ 1 / (10 * (q n : ℝ)) := by
    have h1R : 10 * (((|m| : ℤ)) : ℝ) * (q n : ℝ) ≤ (q (n + 1) : ℝ) := by
      by_cases hm : m = 0
      · subst hm
        have hpos : (0 : ℝ) < (q (n + 1) : ℝ) := by
          have := hqpos (n + 1); exact_mod_cast this
        simpa only [abs_zero, Int.cast_zero, mul_zero, zero_mul] using le_of_lt hpos
      · have hmq' := hmq hm
        have hcast : 10 * ((((|m| : ℤ)) : ℝ) + 1) * (q n : ℝ) ≤ (q (n + 1) : ℝ) := by
          exact_mod_cast hmq'
        nlinarith [hcast, le_of_lt hQ]
    have h1 : Basic.nn (((m * (q n : ℤ) : ℤ) : ℝ) * α) ≤ (((m.natAbs : ℕ)) : ℝ) * Δ n := by
      have h := Core.nn_intCast_mul_le m (((q n : ℤ) : ℝ) * α)
      have hΔ : Basic.nn (((q n : ℤ) : ℝ) * α) = Δ n := by
        rw [show (((q n : ℤ) : ℝ) * α) = ((q n : ℝ) * α) by push_cast; ring]
        exact (Core.fracDist_eq_nn _).symm.trans (hΔeq n).symm
      rw [hΔ] at h
      have hcast : (m : ℝ) * (((q n : ℤ) : ℝ) * α) = (((m * (q n : ℤ) : ℤ)) : ℝ) * α := by
        push_cast; ring
      rwa [hcast] at h
    have h2 : (((m.natAbs : ℕ)) : ℝ) * Δ n ≤ 1 / (10 * (q n : ℝ)) := by
      have h3 : (((m.natAbs : ℕ)) : ℝ) = (((|m| : ℤ)) : ℝ) := by
        have h : (m.natAbs : ℤ) = |m| := (Int.abs_eq_natAbs m).symm
        calc (((m.natAbs : ℕ)) : ℝ) = ((m.natAbs : ℤ) : ℝ) := by rw [Int.cast_natCast]
          _ = ((|m| : ℤ) : ℝ) := by rw [h]
      rw [h3]
      have h4 : (((|m| : ℤ)) : ℝ) * Δ n
          ≤ (((|m| : ℤ)) : ℝ) * (1 / (q (n + 1) : ℝ)) :=
        mul_le_mul_of_nonneg_left (le_of_lt (hΔup n))
          (by exact_mod_cast (abs_nonneg m : (0 : ℤ) ≤ |m|))
      have h5 : (0 : ℝ) < (q (n + 1) : ℝ) := by have := hqpos (n + 1); exact_mod_cast this
      have h6 : (((|m| : ℤ)) : ℝ) * (1 / (q (n + 1) : ℝ)) ≤ 1 / (10 * (q n : ℝ)) := by
        rw [mul_one_div, div_le_div_iff₀ h5 (by positivity)]
        nlinarith [h1R, hQ]
      linarith [h4, h6]
    rw [Core.fracDist_eq_nn]
    linarith [h1, h2]
  have hcross : ∀ w : ℤ, 1 ≤ w → w ≤ (q n : ℤ) - 1 →
      1 / (8 * (q n : ℝ)) ≤
        Work.TMC16Core.fracDist (((w + m * (q n : ℤ) : ℤ) : ℝ) * α) := by
    intro w hw1 hw2
    have hwne : w ≠ 0 := by omega
    have hwabs : |w| < (q n : ℤ) := by
      rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ w)]; omega
    have hsepw : 1 / (2 * (q n : ℝ)) ≤ Work.TMC16Core.fracDist ((w : ℝ) * α) :=
      hsepAll w hwne hwabs
    have htri : Work.TMC16Core.fracDist ((w : ℝ) * α)
        ≤ Work.TMC16Core.fracDist (((w + m * (q n : ℤ) : ℤ) : ℝ) * α)
          + Work.TMC16Core.fracDist (((m * (q n : ℤ) : ℤ) : ℝ) * α) := by
      have hsplit : (((w + m * (q n : ℤ) : ℤ)) : ℝ) * α
          = (w : ℝ) * α + ((m * (q n : ℤ) : ℤ) : ℝ) * α := by push_cast; ring
      rw [hsplit]
      have key : Basic.nn ((w : ℝ) * α)
          ≤ Basic.nn ((w : ℝ) * α + ((m * (q n : ℤ) : ℤ) : ℝ) * α)
            + Basic.nn (((m * (q n : ℤ) : ℤ) : ℝ) * α) := by
        have h := Core.nn_sub_le_aux ((w : ℝ) * α + ((m * (q n : ℤ) : ℤ) : ℝ) * α)
          (((m * (q n : ℤ) : ℤ) : ℝ) * α)
        have h2 : (w : ℝ) * α + ((m * (q n : ℤ) : ℤ) : ℝ) * α
            - (((m * (q n : ℤ) : ℤ) : ℝ) * α) = (w : ℝ) * α := by ring
        rwa [h2] at h
      simpa only [Core.fracDist_eq_nn] using key
    linarith [hsepw, htri, hshift, h8', h8]
  simp only [W1s0, W2s0, Finset.mem_union, Finset.mem_Icc] at hi hk
  rcases hi with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩ <;> rcases hk with ⟨hk1, hk2⟩ | ⟨hk1, hk2⟩
  · have hlt : |(i - k : ℤ)| < (q n : ℤ) := by rw [abs_lt]; omega
    have h1 := hsepAll (i - k) (by omega) hlt
    linarith [h1, h8]
  · have hw1 : 1 ≤ k - i - m * (q n : ℤ) := by omega
    have hw2 : k - i - m * (q n : ℤ) ≤ (q n : ℤ) - 1 := by omega
    have h := hcross (k - i - m * (q n : ℤ)) hw1 hw2
    have heq : (k - i - m * (q n : ℤ)) + m * (q n : ℤ) = k - i := by ring
    rw [heq] at h
    have hneg : Work.TMC16Core.fracDist ((((k - i : ℤ)) : ℝ) * α)
        = Work.TMC16Core.fracDist ((((i - k : ℤ)) : ℝ) * α) := by
      have h1 : (((k - i : ℤ)) : ℝ) * α = -((((i - k : ℤ)) : ℝ) * α) := by push_cast; ring
      rw [h1, Core.fracDist_neg]
    rwa [hneg] at h
  · have hw1 : 1 ≤ i - k - m * (q n : ℤ) := by omega
    have hw2 : i - k - m * (q n : ℤ) ≤ (q n : ℤ) - 1 := by omega
    have h := hcross (i - k - m * (q n : ℤ)) hw1 hw2
    have heq : (i - k - m * (q n : ℤ)) + m * (q n : ℤ) = i - k := by ring
    rwa [heq] at h
  · have hlt : |(i - k : ℤ)| < (q n : ℤ) := by rw [abs_lt]; omega
    have h1 := hsepAll (i - k) (by omega) hlt
    linarith [h1, h8]


private lemma s0qn_blk_priv {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n : ℕ} {p m' : ℤ} {Lsh : ℤ → ℤ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) →
      Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    (hn : 1 ≤ n)
    (hLsh : ∀ k : ℤ, Lsh k = 0 ∨ Lsh k = m')
    (hmq : 10 * (|m'| + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    {ξ : ℝ} {k₀ : ℤ} (hk₀ : k₀ ∈ Finset.Icc p (p + (q n : ℤ) - 1))
    (hmin : ∀ k ∈ Finset.Icc p (p + (q n : ℤ) - 1),
      |Real.sin (Real.pi * (ξ + ((k + Lsh k * (q n : ℤ) : ℤ) : ℝ) * α))| ≥
        |Real.sin (Real.pi * (ξ + ((k₀ + Lsh k₀ * (q n : ℤ) : ℤ) : ℝ) * α))|) :
    |∑ k ∈ (Finset.Icc p (p + (q n : ℤ) - 1)).erase k₀,
        Real.log |Real.sin (Real.pi * (ξ + ((k + Lsh k * (q n : ℤ) : ℤ) : ℝ) * α))|
      + ((q n : ℝ) - 1) * Real.log 2| ≤ 8 * Real.log (q n : ℝ) := by
  classical
  -- The shift count `ℓ = |m'| + 1`.
  set ℓ : ℕ := m'.natAbs + 1 with hℓdef
  have hℓ1 : 1 ≤ ℓ := by omega
  have hℓcast : (ℓ : ℤ) = |m'| + 1 := by
    rw [hℓdef]; push_cast; ring
  have hℓsub : (ℓ : ℤ) - 1 = |m'| := by rw [hℓcast]; ring
  -- The non-resonance hypothesis in the form required by `irrat_blk_shift`.
  have hℓb_int : 10 * (ℓ : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ) := by
    rw [hℓcast]; exact hmq
  have hstrict : 10 * (ℓ : ℝ) * (q n : ℝ) < (q (n + 1) : ℝ) :=
    Core.res_strict_hℓb hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ1 hℓb_int
  have hLshb : ∀ k : ℤ, |Lsh k| ≤ (ℓ : ℤ) - 1 := by
    intro k
    rcases hLsh k with h | h
    · rw [h, abs_zero, hℓsub]; exact abs_nonneg m'
    · rw [h, hℓsub]
  -- AJ's `shift1` at `r = n`, `ℓ = |m'| + 1`.
  have hblk := Core.irrat_blk_shift (n := n) (r := n) (p := p) (ξ := ξ) (k₀ := k₀)
    (Lsh := Lsh) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest le_rfl hℓ1 hstrict hLshb hk₀ hmin
  -- Arithmetic finale.
  have hQ : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hqpos n
  have hQ1 : (0 : ℝ) < (q (n + 1) : ℝ) := by exact_mod_cast hqpos (n + 1)
  have hq1 : 1 ≤ q n := by have := hqpos n; omega
  have hlog : 0 ≤ Real.log (q n : ℝ) := Real.log_nonneg (by exact_mod_cast hq1)
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ1
  have h10Ql : 10 * (ℓ : ℝ) * (q n : ℝ) ≤ (q (n + 1) : ℝ) := by
    have h1 : ((10 * (ℓ : ℤ) * (q n : ℤ) : ℤ) : ℝ) ≤ (((q (n + 1) : ℤ)) : ℝ) := by
      exact_mod_cast hℓb_int
    push_cast at h1
    exact h1
  have hℓ1R : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ1
  have h10Q : 10 * (q n : ℝ) ≤ (q (n + 1) : ℝ) := by
    have hh : 10 * (1 : ℝ) * (q n : ℝ) ≤ 10 * (ℓ : ℝ) * (q n : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hQ)
    linarith [hh, h10Ql]
  -- `Δ n * q n < 1/10`
  have hA1 : Δ n * (q n : ℝ) < 1 / 10 := by
    have h1 : Δ n * (q n : ℝ) < (1 / (q (n + 1) : ℝ)) * (q n : ℝ) :=
      mul_lt_mul_of_pos_right (hΔup n) hQ
    have h2 : (1 / (q (n + 1) : ℝ)) * (q n : ℝ) = (q n : ℝ) / (q (n + 1) : ℝ) := by ring
    rw [h2] at h1
    have h3 : (q n : ℝ) / (q (n + 1) : ℝ) ≤ 1 / 10 := by
      rw [div_le_iff₀ hQ1]
      nlinarith [h10Q]
    linarith
  -- `ℓ * Δ n * q n < 1/10`
  have hA2 : (ℓ : ℝ) * Δ n * (q n : ℝ) < 1 / 10 := by
    have h3 : (q n : ℝ) / (q (n + 1) : ℝ) < 1 / (10 * (ℓ : ℝ)) := by
      rw [div_lt_div_iff₀ hQ1 (by positivity)]
      nlinarith [hstrict]
    have h1 : Δ n * (q n : ℝ) < (1 / (q (n + 1) : ℝ)) * (q n : ℝ) :=
      mul_lt_mul_of_pos_right (hΔup n) hQ
    have h2 : (1 / (q (n + 1) : ℝ)) * (q n : ℝ) = (q n : ℝ) / (q (n + 1) : ℝ) := by ring
    have h4 : Δ n * (q n : ℝ) < 1 / (10 * (ℓ : ℝ)) := by
      rw [h2] at h1; linarith
    have h5 : (ℓ : ℝ) * (Δ n * (q n : ℝ)) < (ℓ : ℝ) * (1 / (10 * (ℓ : ℝ))) :=
      mul_lt_mul_of_pos_left h4 hℓR
    have h6 : (ℓ : ℝ) * (1 / (10 * (ℓ : ℝ))) = 1 / 10 := by field_simp
    linarith [h5, h6.le, h6.ge]
  have hA : (Δ n + (ℓ : ℝ) * Δ n) * (q n : ℝ) < 1 / 5 := by nlinarith [hA1, hA2]
  have h32 : 32 * ((Δ n + (ℓ : ℝ) * Δ n) * (q n : ℝ)) ≤ 7 := by linarith
  have h1 : 32 * ((Δ n + (ℓ : ℝ) * Δ n) * (q n : ℝ) * Real.log (q n : ℝ))
      ≤ 7 * Real.log (q n : ℝ) := by
    rw [show 32 * ((Δ n + (ℓ : ℝ) * Δ n) * (q n : ℝ) * Real.log (q n : ℝ))
        = (32 * ((Δ n + (ℓ : ℝ) * Δ n) * (q n : ℝ))) * Real.log (q n : ℝ) by ring]
    exact mul_le_mul_of_nonneg_right h32 hlog
  linarith [hblk, h1]



/-! ## Helper lemmas -/

/-- Reindex a sum over a finite set that is the bijective image of an index block. -/
private lemma sum_erase_image {blk S : Finset ℤ} {site : ℤ → ℤ}
    (himg : blk.image site = S)
    (hinj : ∀ x ∈ blk, ∀ y ∈ blk, site x = site y → x = y)
    (f : ℤ → ℝ) {k : ℤ} (hk : k ∈ S) :
    ∃ k' ∈ blk, site k' = k ∧ (∑ i ∈ S.erase k, f i) = ∑ j ∈ blk.erase k', f (site j) := by
  obtain ⟨k', hk'blk, hk'eq⟩ := Finset.mem_image.mp (by rw [himg]; exact hk)
  refine ⟨k', hk'blk, hk'eq, ?_⟩
  rw [← himg, ← hk'eq]
  refine (Finset.sum_bij (fun j (_ : j ∈ blk.erase k') => site j) ?_ ?_ ?_ ?_).symm
  · intro j hj
    rw [Finset.mem_erase] at hj ⊢
    exact ⟨fun h => hj.1 (hinj j hj.2 k' hk'blk h),
      Finset.mem_image.mpr ⟨j, hj.2, rfl⟩⟩
  · intro j₁ hj₁ j₂ hj₂ heq
    rw [Finset.mem_erase] at hj₁ hj₂
    exact hinj j₁ hj₁.2 j₂ hj₂.2 heq
  · intro b hb
    rw [Finset.mem_erase] at hb
    obtain ⟨j, hjblk, hjeq⟩ := Finset.mem_image.mp hb.2
    refine ⟨j, ?_, hjeq⟩
    rw [Finset.mem_erase]
    exact ⟨fun h => hb.1 (by rw [← hjeq, h]), hjblk⟩
  · intro j _
    rfl

/-- A zero of the phase is a minimiser, hence the min-removed block estimate bounds the
sum with that term removed from below. -/
private lemma blk_erase_zero_local {L : ℕ} {α ξ : ℝ} {p d qr : ℤ} {Lsh : ℤ → ℤ} {B : ℝ}
    (hblk : ∀ (k₀ : ℤ), k₀ ∈ Finset.Icc p (p + (L : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (L : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + ((k + Lsh k * qr : ℤ) : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + ((k₀ + Lsh k₀ * qr : ℤ) : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + ((k + Lsh k * qr : ℤ) : ℝ) * α))|
        + ((L : ℝ) - 1) * Real.log 2| ≤ B)
    (hd : d ∈ Finset.Icc p (p + (L : ℤ) - 1))
    (hzero : Real.sin (Real.pi * (ξ + ((d + Lsh d * qr : ℤ) : ℝ) * α)) = 0) :
    ∑ i ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase d,
        Real.log |Real.sin (Real.pi * (ξ + ((i + Lsh i * qr : ℤ) : ℝ) * α))|
      ≥ -(((L : ℝ) - 1) * Real.log 2) - B := by
  have hb := hblk d hd (fun k _ => by rw [hzero, abs_zero]; exact abs_nonneg _)
  have h1 := (abs_le.mp hb).1
  linarith

theorem s0qn_engine {α θ ε cθ : ℝ} {q : ℕ → ℕ} {n U : ℕ} {a m p : ℤ} {Lsh : ℤ → ℤ}
    (hn : 3 ≤ n) (hH2 : 2 ≤ q n) (h2U : 2 * U ≤ q n)
    (ha : |a| ≤ 2 * (q n : ℤ))
    (hcθ : 0 < cθ) (hcθ1 : cθ ≤ 1 / 2)
    (hθC : ∀ t : ℤ, 0 ≤ t → t ≤ 2 → ∀ j : ℤ, |j| ≤ 8 * (q n : ℤ) + 8 →
      cθ ≤ fracDist (2 * θ + (((j + t * m * (q n : ℤ) : ℤ)) : ℝ) * α))
    (hsep : ∀ i : ℤ, i ∈ W1s0 a U ∪ W2s0 a U (q n) (m * (q n : ℤ)) →
      ∀ k : ℤ, k ∈ W1s0 a U ∪ W2s0 a U (q n) (m * (q n : ℤ)) → i ≠ k →
      1 / (8 * (q n : ℝ)) ≤ fracDist (((i - k : ℤ) : ℝ) * α))
    (himg : (Finset.Icc p (p + (q n : ℤ) - 1)).image (fun k => k + Lsh k * (q n : ℤ))
      = W1s0 a U ∪ W2s0 a U (q n) (m * (q n : ℤ)))
    (hinj : ∀ x ∈ Finset.Icc p (p + (q n : ℤ) - 1),
      ∀ y ∈ Finset.Icc p (p + (q n : ℤ) - 1),
      x + Lsh x * (q n : ℤ) = y + Lsh y * (q n : ℤ) → x = y)
    (hblk : ∀ (ξ : ℝ) (k₀ : ℤ), k₀ ∈ Finset.Icc p (p + (q n : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (q n : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + ((k + Lsh k * (q n : ℤ) : ℤ) : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + ((k₀ + Lsh k₀ * (q n : ℤ) : ℤ) : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (q n : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + ((k + Lsh k * (q n : ℤ) : ℤ) : ℝ) * α))|
        + ((q n : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (q n : ℝ))
    (hbudget : 300 * Real.log (q n : ℝ) + 8 * Real.log (1 / cθ) + 2 * Real.log (2 * (q n : ℝ))
      < ((q n : ℝ) - 1) * ε) :
    Uniform ε (fun j : {j : ℤ // j ∈ W1s0 a U ∪ W2s0 a U (q n) (m * (q n : ℤ))} =>
        θ + (((j : ℤ) : ℝ) + (((q n : ℝ) - 2) / 2)) * α) := by
  classical
  set S : Finset ℤ := W1s0 a U ∪ W2s0 a U (q n) (m * (q n : ℤ)) with hSdef
  have himg' : (Finset.Icc p (p + (q n : ℤ) - 1)).image (fun k => k + Lsh k * (q n : ℤ)) = S := by
    rw [hSdef]; exact himg
  have hcardS : S.card = q n := by
    rw [← himg']
    rw [Finset.card_image_of_injOn (f := fun k => k + Lsh k * (q n : ℤ))
      (by intro x hx y hy h; exact hinj x hx y hy h)]
    rw [Int.card_Icc]
    have h : p + (q n : ℤ) - 1 + 1 - p = (q n : ℤ) := by ring
    rw [h, Int.toNat_natCast]
  have hqpos : (0 : ℝ) < (q n : ℝ) := by
    exact_mod_cast (by omega : 0 < q n)
  have hsepS : ∀ i : ℤ, i ∈ S → ∀ k : ℤ, k ∈ S → i ≠ k →
      1 / (8 * (q n : ℝ)) ≤ fracDist (((i - k : ℤ) : ℝ) * α) := by
    intro i hi k hk hne
    exact hsep i hi k hk hne
  have hcluster : ∀ i : ℤ, i ∈ S → ∀ k : ℤ, k ∈ S →
      cθ ≤ fracDist (2 * θ + ((((q n : ℤ) - 2) + i + k : ℤ) : ℝ) * α) := by
    intro i hi k hk
    obtain ⟨t, j, ht0, ht2, hj, heq⟩ :=
      s0qn_cluster (M := m * (q n : ℤ)) hH2 h2U rfl ha hi hk
    have h1 := hθC t ht0 ht2 j hj
    have harg : (((j + t * m * (q n : ℤ) : ℤ)) : ℝ) * α
        = ((((q n : ℤ) - 2) + i + k : ℤ) : ℝ) * α := by
      have h2 : j + t * m * (q n : ℤ) = ((q n : ℤ) - 2) + i + k := by
        calc j + t * m * (q n : ℤ) = j + t * (m * (q n : ℤ)) := by ring
          _ = ((q n : ℤ) - 2) + i + k := heq.symm
      rw [h2]
    rw [harg] at h1
    exact h1
  set θ' : ℝ := θ + (((q n : ℝ) - 2) / 2) * α with hθ'def
  have hclustθ' : ∀ i : ℤ, i ∈ S → ∀ k : ℤ, k ∈ S →
      cθ ≤ fracDist (2 * θ' + ((i + k : ℤ) : ℝ) * α) := by
    intro i hi k hk
    have h1 := hcluster i hi k hk
    have harg : 2 * θ' + ((i + k : ℤ) : ℝ) * α
        = 2 * θ + ((((q n : ℤ) - 2) + i + k : ℤ) : ℝ) * α := by
      rw [hθ'def]; push_cast; ring
    rw [harg]; exact h1
  have hcos : ∀ i : ℤ, i ∈ S → ∀ j : ℤ, j ∈ S → i ≠ j →
      Real.cos (2 * Real.pi * (θ' + (i : ℝ) * α))
        ≠ Real.cos (2 * Real.pi * (θ' + (j : ℝ) * α)) := by
    intro i hi j hj hne
    exact s0qn_cos_ne (θ := θ') (cθ := cθ) (csep := 1 / (8 * (q n : ℝ)))
      hcθ (by positivity) hclustθ' hsepS hi hj hne
  have hN : ∀ (k : ℤ), k ∈ S → ∀ ξ : ℝ,
      (∀ i ∈ S.erase k, Real.sin (Real.pi * (ξ + (i : ℝ) * α)) ≠ 0) →
      ∑ i ∈ S.erase k, Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
        ≤ -((S.card : ℝ) - 1) * Real.log 2 + 32 * Real.log (q n : ℝ) := by
    intro k hk ξ hnz
    obtain ⟨k', hk'blk, hk'eq, hsum⟩ := sum_erase_image himg' hinj
      (fun i => Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|) hk
    rw [hsum]
    have hnz' : ∀ i ∈ Finset.Icc p (p + (q n : ℤ) - 1), i ≠ k' →
        Real.sin (Real.pi * (ξ + ((i + Lsh i * (q n : ℤ) : ℤ) : ℝ) * α)) ≠ 0 := by
      intro i hi hine
      have hmem : (i + Lsh i * (q n : ℤ)) ∈ S := by
        rw [← himg']; exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
      have hne : (i + Lsh i * (q n : ℤ)) ≠ k := by
        intro hcon
        exact hine (hinj i hi k' hk'blk (by rw [hcon, hk'eq]))
      exact hnz _ (Finset.mem_erase.mpr ⟨hne, hmem⟩)
    have hb := s0qn_blk_bound_priv (L := q n) (α := α) (ξ := ξ) (p := p) (d := k')
      (qr := (q n : ℤ)) (Lsh := Lsh) (B := 32 * Real.log (q n : ℝ)) (by omega)
      (hblk ξ) hnz'
    rw [hcardS]
    rw [show -((q n : ℝ) - 1) * Real.log 2 = -(((q n : ℝ) - 1) * Real.log 2) by ring]
    exact hb
  have hD1 : ∀ k : ℤ, k ∈ S →
      ∑ i ∈ S.erase k, Real.log |Real.sin (Real.pi * (2 * θ' + ((i + k : ℤ) : ℝ) * α))|
        ≥ -((S.card : ℝ) - 1) * Real.log 2 - 32 * Real.log (q n : ℝ)
          + 2 * Real.log (2 * cθ) := by
    intro k hk
    obtain ⟨k', hk'blk, hk'eq, hsum⟩ := sum_erase_image himg' hinj
      (fun i => Real.log |Real.sin (Real.pi * (2 * θ' + ((i + k : ℤ) : ℝ) * α))|) hk
    rw [hsum]
    have hstep : ∑ j ∈ (Finset.Icc p (p + (q n : ℤ) - 1)).erase k',
        Real.log |Real.sin (Real.pi * (2 * θ' + ((((j + Lsh j * (q n : ℤ)) + k : ℤ)) : ℝ) * α))|
        = ∑ j ∈ (Finset.Icc p (p + (q n : ℤ) - 1)).erase k',
          Real.log |Real.sin (Real.pi * ((2 * θ' + (k : ℝ) * α)
            + ((j + Lsh j * (q n : ℤ) : ℤ) : ℝ) * α))| := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1
      push_cast; ring
    rw [hstep]
    have hlo : ∀ j ∈ Finset.Icc p (p + (q n : ℤ) - 1),
        2 * cθ ≤ |Real.sin (Real.pi * ((2 * θ' + (k : ℝ) * α)
          + ((j + Lsh j * (q n : ℤ) : ℤ) : ℝ) * α))| := by
      intro j hj
      have hmem : (j + Lsh j * (q n : ℤ)) ∈ S := by
        rw [← himg']; exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
      have hcl := hclustθ' _ hmem k hk
      have harg : ((2 * θ' + (k : ℝ) * α) + ((j + Lsh j * (q n : ℤ) : ℤ) : ℝ) * α)
          = 2 * θ' + ((((j + Lsh j * (q n : ℤ)) + k : ℤ)) : ℝ) * α := by
        push_cast; ring
      rw [harg]
      exact le_trans (mul_le_mul_of_nonneg_left hcl (by norm_num : (0 : ℝ) ≤ 2))
        (Core.two_mul_fracDist_le_abs_sin _)
    have hb := s0qn_blk_erase_ge (L := q n) (α := α) (ξ := 2 * θ' + (k : ℝ) * α) (c := cθ)
      (p := p) (d := k') (qr := (q n : ℤ)) (Lsh := Lsh) (B := 32 * Real.log (q n : ℝ))
      (by omega) (hblk (2 * θ' + (k : ℝ) * α)) hcθ hcθ1 hlo
    have hlog2c : Real.log (2 * cθ) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    rw [hcardS]
    rw [show -((q n : ℝ) - 1) * Real.log 2 = -(((q n : ℝ) - 1) * Real.log 2) by ring]
    linarith [hb, hlog2c]
  have hD2 : ∀ k : ℤ, k ∈ S →
      ∑ i ∈ S.erase k, Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|
        ≥ -((S.card : ℝ) - 1) * Real.log 2 - 32 * Real.log (q n : ℝ)
          + Real.log (2 * (1 / (8 * (q n : ℝ)))) := by
    intro k hk
    obtain ⟨k', hk'blk, hk'eq, hsum⟩ := sum_erase_image himg' hinj
      (fun i => Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|) hk
    rw [hsum]
    have hstep : ∑ j ∈ (Finset.Icc p (p + (q n : ℤ) - 1)).erase k',
        Real.log |Real.sin (Real.pi * ((((j + Lsh j * (q n : ℤ)) - k : ℤ)) : ℝ) * α)|
        = ∑ j ∈ (Finset.Icc p (p + (q n : ℤ) - 1)).erase k',
          Real.log |Real.sin (Real.pi * ((-(k : ℝ) * α)
            + ((j + Lsh j * (q n : ℤ) : ℤ) : ℝ) * α))| := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1
      push_cast; ring
    rw [hstep]
    have hzero : Real.sin (Real.pi * ((-(k : ℝ) * α)
        + ((k' + Lsh k' * (q n : ℤ) : ℤ) : ℝ) * α)) = 0 := by
      have h1 : (-(k : ℝ) * α) + ((k' + Lsh k' * (q n : ℤ) : ℤ) : ℝ) * α
          = ((((k' + Lsh k' * (q n : ℤ)) - k : ℤ)) : ℝ) * α := by push_cast; ring
      rw [h1]
      have h2 : ((((k' + Lsh k' * (q n : ℤ)) - k : ℤ)) : ℝ) = 0 := by
        rw [hk'eq]; push_cast; ring
      rw [h2]
      simp
    have hb := blk_erase_zero_local (L := q n) (α := α) (ξ := -(k : ℝ) * α) (p := p)
      (d := k') (qr := (q n : ℤ)) (Lsh := Lsh) (B := 32 * Real.log (q n : ℝ))
      (hblk (-(k : ℝ) * α)) hk'blk hzero
    have hlog2c : Real.log (2 * (1 / (8 * (q n : ℝ)))) ≤ 0 := by
      apply Real.log_nonpos
      · positivity
      · rw [show (2 : ℝ) * (1 / (8 * (q n : ℝ))) = 2 / (8 * (q n : ℝ)) by ring,
          div_le_one (by positivity)]
        have : (2 : ℝ) ≤ 8 * (q n : ℝ) := by
          have h2 : (2 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hH2
          linarith
        linarith
    rw [hcardS]
    rw [show -((q n : ℝ) - 1) * Real.log 2 = -(((q n : ℝ) - 1) * Real.log 2) by ring]
    linarith [hb, hlog2c]
  have hqbound : 2 * (32 * Real.log (q n : ℝ)) + 32 * Real.log (q n : ℝ)
      + 32 * Real.log (q n : ℝ) + 2 * Real.log (1 / (2 * cθ))
      + Real.log (1 / (2 * (1 / (8 * (q n : ℝ))))) < ((S.card : ℝ) - 1) * ε := by
    have h4 : (1 : ℝ) / (2 * (1 / (8 * (q n : ℝ)))) = 4 * (q n : ℝ) := by
      field_simp
      ring
    rw [h4, hcardS]
    have hlogH : 0 ≤ Real.log (q n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q n))
    have hlog1cθ : 0 ≤ Real.log (1 / cθ) :=
      Real.log_nonneg (by rw [le_div_iff₀ hcθ]; linarith)
    have hkey1 : 2 * Real.log (1 / (2 * cθ)) ≤ 8 * Real.log (1 / cθ) := by
      have h2 : Real.log (1 / (2 * cθ)) = Real.log (1 / cθ) - Real.log 2 := by
        rw [show (1 : ℝ) / (2 * cθ) = (1 / cθ) / 2 by ring,
          Real.log_div (by positivity) (by norm_num)]
      rw [h2]
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
    have hkey2 : Real.log (4 * (q n : ℝ)) ≤ 2 * Real.log (2 * (q n : ℝ)) := by
      have h4' : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast; ring
      rw [Real.log_mul (by norm_num) (by positivity),
        Real.log_mul (by norm_num) (by positivity), h4']
      linarith
    linarith [hbudget, hkey1, hkey2, hlogH]
  have hmain := uniform_of_sum_bounds_gen (S := S) (α := α) (θ := θ') (ε := ε) (cθ := cθ)
    (csep := 1 / (8 * (q n : ℝ))) (A := 32 * Real.log (q n : ℝ))
    (B := 32 * Real.log (q n : ℝ)) (C := 32 * Real.log (q n : ℝ))
    hcos hN hD1 hD2 hcθ (by positivity) hqbound
  have hfam : (fun p : {p : ℤ // p ∈ S} => θ' + (p : ℝ) * α)
      = (fun p : {p : ℤ // p ∈ S} => θ + (((p : ℤ) : ℝ) + (((q n : ℝ) - 2) / 2)) * α) := by
    funext p
    rw [hθ'def]
    ring
  rwa [hfam] at hmain

/-! ### The site parametrisation of the windows in the four cases -/

private lemma s0qn_conf_m0 {H U : ℕ} {a m : ℤ} (h2U : 2 * U ≤ H) (hm0 : m = 0) :
    ((Finset.Icc a (a + (H : ℤ) - 1)).image (fun k => k + (fun _ : ℤ => (0 : ℤ)) k * (H : ℤ))
        = W1s0 a U ∪ W2s0 a U H (m * (H : ℤ))) ∧
      (∀ x ∈ Finset.Icc a (a + (H : ℤ) - 1), ∀ y ∈ Finset.Icc a (a + (H : ℤ) - 1),
        x + (fun _ : ℤ => (0 : ℤ)) x * (H : ℤ) = y + (fun _ : ℤ => (0 : ℤ)) y * (H : ℤ)
          → x = y) := by
  subst hm0
  have h2UZ : 2 * (U : ℤ) ≤ (H : ℤ) := by exact_mod_cast h2U
  have hset : W1s0 a U ∪ W2s0 a U H (0 * (H : ℤ)) = Finset.Icc a (a + (H : ℤ) - 1) := by
    rw [W1s0, W2s0]
    simp only [zero_mul, zero_add]
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
    · intro hx
      by_cases hx' : x ≤ a + 2 * (U : ℤ) - 1
      · exact Or.inl ⟨hx.1, hx'⟩
      · exact Or.inr ⟨by omega, hx.2⟩
  refine ⟨?_, ?_⟩
  · rw [hset]
    have hid : (fun k : ℤ => k + (fun _ : ℤ => (0 : ℤ)) k * (H : ℤ)) = id := by
      funext k; simp
    rw [hid, Finset.image_id]
  · intro x _ y _ h
    simpa using h

private lemma s0qn_conf_mm1 {H U : ℕ} {a m : ℤ} (h2U : 2 * U ≤ H) (hH1 : 1 ≤ H)
    (hm1 : m = -1) :
    ((Finset.Icc (m * (H : ℤ) + a + 2 * (U : ℤ))
          (m * (H : ℤ) + a + 2 * (U : ℤ) + (H : ℤ) - 1)).image
        (fun k => k + (fun _ : ℤ => (0 : ℤ)) k * (H : ℤ))
        = W1s0 a U ∪ W2s0 a U H (m * (H : ℤ))) ∧
      (∀ x ∈ Finset.Icc (m * (H : ℤ) + a + 2 * (U : ℤ))
            (m * (H : ℤ) + a + 2 * (U : ℤ) + (H : ℤ) - 1),
        ∀ y ∈ Finset.Icc (m * (H : ℤ) + a + 2 * (U : ℤ))
            (m * (H : ℤ) + a + 2 * (U : ℤ) + (H : ℤ) - 1),
        x + (fun _ : ℤ => (0 : ℤ)) x * (H : ℤ) = y + (fun _ : ℤ => (0 : ℤ)) y * (H : ℤ)
          → x = y) := by
  subst hm1
  have h2UZ : 2 * (U : ℤ) ≤ (H : ℤ) := by exact_mod_cast h2U
  have hH1Z : (1 : ℤ) ≤ (H : ℤ) := by exact_mod_cast hH1
  have hset : W1s0 a U ∪ W2s0 a U H ((-1) * (H : ℤ))
      = Finset.Icc ((-1) * (H : ℤ) + a + 2 * (U : ℤ))
          ((-1) * (H : ℤ) + a + 2 * (U : ℤ) + (H : ℤ) - 1) := by
    rw [W1s0, W2s0]
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
    · intro hx
      by_cases hx' : x ≤ a - 1
      · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inl ⟨by omega, by omega⟩
  refine ⟨?_, ?_⟩
  · rw [hset]
    have hid : (fun k : ℤ => k + (fun _ : ℤ => (0 : ℤ)) k * (H : ℤ)) = id := by
      funext k; simp
    rw [hid, Finset.image_id]
  · intro x _ y _ h
    simpa using h

private lemma s0qn_conf_pos {H U : ℕ} {a m : ℤ} (h2U : 2 * U ≤ H) (hH1 : 1 ≤ H)
    (hpos : 0 ≤ m) (hm0 : m ≠ 0) :
    ∃ Lsh : ℤ → ℤ,
      ((Finset.Icc a (a + (H : ℤ) - 1)).image (fun k => k + Lsh k * (H : ℤ))
          = W1s0 a U ∪ W2s0 a U H (m * (H : ℤ))) ∧
      (∀ x ∈ Finset.Icc a (a + (H : ℤ) - 1), ∀ y ∈ Finset.Icc a (a + (H : ℤ) - 1),
        x + Lsh x * (H : ℤ) = y + Lsh y * (H : ℤ) → x = y) ∧
      (∀ k : ℤ, Lsh k = 0 ∨ Lsh k = m) := by
  have h2UZ : 2 * (U : ℤ) ≤ (H : ℤ) := by exact_mod_cast h2U
  have hH1Z : (1 : ℤ) ≤ (H : ℤ) := by exact_mod_cast hH1
  have hmge : (1 : ℤ) ≤ m := by omega
  have hmH : (1 : ℤ) ≤ m * (H : ℤ) := by nlinarith [hmge, hH1Z]
  let Lsh : ℤ → ℤ := fun k => if a + 2 * (U : ℤ) ≤ k then m else 0
  refine ⟨Lsh, ?_, ?_, ?_⟩
  · dsimp only [Lsh]
    rw [W1s0, W2s0]
    ext x
    simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_union]
    constructor
    · rintro ⟨k, ⟨hk1, hk2⟩, hsite⟩
      by_cases hk : a + 2 * (U : ℤ) ≤ k
      · right
        rw [if_pos hk] at hsite
        constructor <;> omega
      · left
        rw [if_neg hk] at hsite
        simp only [zero_mul, add_zero] at hsite
        constructor <;> omega
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · refine ⟨x, ⟨h1, by omega⟩, ?_⟩
        rw [if_neg (by omega : ¬ (a + 2 * (U : ℤ) ≤ x))]
        ring
      · refine ⟨x - m * (H : ℤ), ⟨by omega, by omega⟩, ?_⟩
        rw [if_pos (by omega : a + 2 * (U : ℤ) ≤ x - m * (H : ℤ))]
        ring
  · dsimp only [Lsh]
    intro x hx y hy h
    simp only [Finset.mem_Icc] at hx hy
    by_cases hx' : a + 2 * (U : ℤ) ≤ x
    · rw [if_pos hx'] at h
      by_cases hy' : a + 2 * (U : ℤ) ≤ y
      · rw [if_pos hy'] at h; omega
      · rw [if_neg hy'] at h
        simp only [zero_mul, add_zero] at h
        omega
    · rw [if_neg hx'] at h
      simp only [zero_mul, add_zero] at h
      by_cases hy' : a + 2 * (U : ℤ) ≤ y
      · rw [if_pos hy'] at h; omega
      · rw [if_neg hy'] at h; omega
  · dsimp only [Lsh]
    intro k
    by_cases hk : a + 2 * (U : ℤ) ≤ k
    · rw [if_pos hk]; exact Or.inr rfl
    · rw [if_neg hk]; exact Or.inl rfl

private lemma s0qn_conf_neg {H U : ℕ} {a m : ℤ} (h2U : 2 * U ≤ H) (hH1 : 1 ≤ H)
    (hneg : ¬ 0 ≤ m) (hm1 : m ≠ -1) :
    ∃ Lsh : ℤ → ℤ,
      ((Finset.Icc (m * (H : ℤ) + a + 2 * (U : ℤ))
          (m * (H : ℤ) + a + 2 * (U : ℤ) + (H : ℤ) - 1)).image
          (fun k => k + Lsh k * (H : ℤ))
        = W1s0 a U ∪ W2s0 a U H (m * (H : ℤ))) ∧
      (∀ x ∈ Finset.Icc (m * (H : ℤ) + a + 2 * (U : ℤ))
            (m * (H : ℤ) + a + 2 * (U : ℤ) + (H : ℤ) - 1),
        ∀ y ∈ Finset.Icc (m * (H : ℤ) + a + 2 * (U : ℤ))
            (m * (H : ℤ) + a + 2 * (U : ℤ) + (H : ℤ) - 1),
        x + Lsh x * (H : ℤ) = y + Lsh y * (H : ℤ) → x = y) ∧
      (∀ k : ℤ, Lsh k = 0 ∨ Lsh k = -m - 1) ∧
      (10 * (|-m - 1| + 1) * (H : ℤ) ≤ 10 * (|m| + 1) * (H : ℤ)) := by
  have h2UZ : 2 * (U : ℤ) ≤ (H : ℤ) := by exact_mod_cast h2U
  have hH1Z : (1 : ℤ) ≤ (H : ℤ) := by exact_mod_cast hH1
  have hmle : m ≤ -2 := by omega
  have hm1'H : (m + 1) * (H : ℤ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by omega : m + 1 ≤ 0) (by linarith : (0 : ℤ) ≤ (H : ℤ))
  have hrel : (-m - 1) * (H : ℤ) = -((m + 1) * (H : ℤ)) := by ring
  have hA : (-m - 1) * (H : ℤ) = -(m * (H : ℤ)) - (H : ℤ) := by ring
  have hnn : (0 : ℤ) ≤ (-m - 1) * (H : ℤ) := by rw [hrel]; linarith
  have habs : |-m - 1| = -m - 1 := abs_of_nonneg (by omega : 0 ≤ -m - 1)
  let Lsh : ℤ → ℤ := fun k => if m * (H : ℤ) + a + (H : ℤ) ≤ k then -m - 1 else 0
  refine ⟨Lsh, ?_, ?_, ?_, ?_⟩
  · dsimp only [Lsh]
    rw [W1s0, W2s0]
    ext x
    simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_union]
    constructor
    · rintro ⟨k, ⟨hk1, hk2⟩, hsite⟩
      by_cases hk : m * (H : ℤ) + a + (H : ℤ) ≤ k
      · left
        rw [if_pos hk] at hsite
        rw [← hsite]
        constructor <;> omega
      · right
        rw [if_neg hk] at hsite
        simp only [zero_mul, add_zero] at hsite
        rw [← hsite]
        constructor <;> omega
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · refine ⟨x + m * (H : ℤ) + (H : ℤ), ⟨by omega, by omega⟩, ?_⟩
        rw [if_pos (by omega : m * (H : ℤ) + a + (H : ℤ)
          ≤ x + m * (H : ℤ) + (H : ℤ))]
        ring
      · refine ⟨x, ⟨by omega, by omega⟩, ?_⟩
        rw [if_neg (by omega : ¬ (m * (H : ℤ) + a + (H : ℤ) ≤ x))]
        ring
  · dsimp only [Lsh]
    intro x hx y hy h
    simp only [Finset.mem_Icc] at hx hy
    by_cases hx' : m * (H : ℤ) + a + (H : ℤ) ≤ x
    · rw [if_pos hx'] at h
      by_cases hy' : m * (H : ℤ) + a + (H : ℤ) ≤ y
      · rw [if_pos hy'] at h; omega
      · rw [if_neg hy'] at h
        simp only [zero_mul, add_zero] at h
        omega
    · rw [if_neg hx'] at h
      simp only [zero_mul, add_zero] at h
      by_cases hy' : m * (H : ℤ) + a + (H : ℤ) ≤ y
      · rw [if_pos hy'] at h
        omega
      · rw [if_neg hy'] at h; omega
  · dsimp only [Lsh]
    intro k
    by_cases hk : m * (H : ℤ) + a + (H : ℤ) ≤ k
    · rw [if_pos hk]; exact Or.inr rfl
    · rw [if_neg hk]; exact Or.inl rfl
  · rw [habs]
    have h1 : -m ≤ |m| + 1 := by
      have h2 : |m| = -m := abs_of_nonpos (by omega : m ≤ 0)
      omega
    have h2 : (-m - 1) * (H : ℤ) + (H : ℤ) ≤ (|m| + 1) * (H : ℤ) := by
      have h3 : -m ≤ |m| + 1 := h1
      nlinarith [h3, hH1Z]
    linarith [h2]

/-! ### The block estimates in the unshifted/shifted shapes -/

private lemma s0qn_hblk_zero {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n : ℕ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i) (hΔeq : ∀ i, Δ i = fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) → Δ i ≤ fracDist ((j : ℝ) * α))
    (hn1 : 1 ≤ n) (p : ℤ) :
    ∀ (ξ : ℝ) (k₀ : ℤ), k₀ ∈ Finset.Icc p (p + (q n : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (q n : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + ((k + (fun _ : ℤ => (0 : ℤ)) k * (q n : ℤ) : ℤ) : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + ((k₀ + (fun _ : ℤ => (0 : ℤ)) k₀ * (q n : ℤ) : ℤ) : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (q n : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + ((k + (fun _ : ℤ => (0 : ℤ)) k * (q n : ℤ) : ℤ) : ℝ) * α))|
        + ((q n : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (q n : ℝ) := by
  intro ξ k₀ hk₀ hmin
  have hb := s0qn_blk0 (α := α) (q := q) (Δ := Δ) (n := n) (p := p)
    hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn1 hk₀ (fun k hk => by simpa using hmin k hk)
  simpa using hb

private lemma s0qn_hblk_shift {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n : ℕ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i) (hΔeq : ∀ i, Δ i = fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) → Δ i ≤ fracDist ((j : ℝ) * α))
    (hn1 : 1 ≤ n) {p m' : ℤ} {Lsh : ℤ → ℤ}
    (hLsh : ∀ k : ℤ, Lsh k = 0 ∨ Lsh k = m')
    (hmq : 10 * (|m'| + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ)) :
    ∀ (ξ : ℝ) (k₀ : ℤ), k₀ ∈ Finset.Icc p (p + (q n : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (q n : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + ((k + Lsh k * (q n : ℤ) : ℤ) : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + ((k₀ + Lsh k₀ * (q n : ℤ) : ℤ) : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (q n : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + ((k + Lsh k * (q n : ℤ) : ℤ) : ℝ) * α))|
        + ((q n : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (q n : ℝ) := by
  intro ξ k₀ hk₀ hmin
  have hb := s0qn_blk_priv (α := α) (q := q) (Δ := Δ) (n := n) (p := p) (m' := m') (Lsh := Lsh)
    hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn1 hLsh hmq hk₀ hmin
  have hqn1 : 1 ≤ q n := by have := hqpos n; omega
  have hlogq : 0 ≤ Real.log (q n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hqn1)
  linarith [hb, hlogq]

theorem s0_uniform_qn {α θ ε cθ : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n H U : ℕ} {a m : ℤ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) →
      Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    (hn : 3 ≤ n) (hH : H = q n) (hH2 : 2 ≤ H) (h2U : 2 * U ≤ H)
    (ha : |a| ≤ 2 * (H : ℤ))
    (hmq : m ≠ 0 → 10 * (|m| + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    (hcθ : 0 < cθ) (hcθ1 : cθ ≤ 1 / 2)
    (hθC : ∀ t : ℤ, 0 ≤ t → t ≤ 2 → ∀ j : ℤ, |j| ≤ 8 * (H : ℤ) + 8 →
      cθ ≤ Work.TMC16Core.fracDist (2 * θ + (((j + t * m * (q n : ℤ) : ℤ)) : ℝ) * α))
    (hbudget : 300 * Real.log (H : ℝ) + 8 * Real.log (1 / cθ) + 2 * Real.log (2 * (H : ℝ))
      < ((H : ℝ) - 1) * ε) :
    Work.TMC16Core.Uniform ε
      (fun j : {j : ℤ // j ∈ Work.TMC16Core.Assembly.W1s0 a U ∪
          Work.TMC16Core.Assembly.W2s0 a U H (m * (q n : ℤ))} =>
        θ + (((j : ℤ) : ℝ) + (((H : ℝ) - 2) / 2)) * α) := by
  subst hH
  have hn1 : 1 ≤ n := by omega
  have hH1 : 1 ≤ q n := by omega
  have hsep : ∀ i : ℤ, i ∈ W1s0 a U ∪ W2s0 a U (q n) (m * (q n : ℤ)) →
      ∀ k : ℤ, k ∈ W1s0 a U ∪ W2s0 a U (q n) (m * (q n : ℤ)) → i ≠ k →
      1 / (8 * (q n : ℝ)) ≤ fracDist (((i - k : ℤ) : ℝ) * α) :=
    fun i hi k hk hne =>
      s0qn_sep_priv (α := α) (q := q) (Δ := Δ) (n := n) (U := U) (a := a) (m := m)
        hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn1 h2U hmq hi hk hne
  by_cases hm0 : m = 0
  · obtain ⟨himg, hinj⟩ := s0qn_conf_m0 (H := q n) (U := U) (a := a) (m := m) h2U hm0
    exact s0qn_engine (α := α) (q := q) (n := n) (U := U) (a := a) (m := m)
      (p := a) (Lsh := fun _ : ℤ => (0 : ℤ))
      hn hH2 h2U ha hcθ hcθ1 hθC hsep himg hinj
      (s0qn_hblk_zero hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn1 a) hbudget
  · by_cases hm1 : m = -1
    · obtain ⟨himg, hinj⟩ := s0qn_conf_mm1 (H := q n) (U := U) (a := a) (m := m) h2U hH1 hm1
      exact s0qn_engine (α := α) (q := q) (n := n) (U := U) (a := a) (m := m)
        (p := m * (q n : ℤ) + a + 2 * (U : ℤ)) (Lsh := fun _ : ℤ => (0 : ℤ))
        hn hH2 h2U ha hcθ hcθ1 hθC hsep himg hinj
        (s0qn_hblk_zero hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn1
          (m * (q n : ℤ) + a + 2 * (U : ℤ))) hbudget
    · by_cases hmpos : 0 ≤ m
      · obtain ⟨Lsh, himg, hinj, hLsh⟩ :=
          s0qn_conf_pos (H := q n) (U := U) (a := a) (m := m) h2U hH1 hmpos hm0
        exact s0qn_engine (α := α) (q := q) (n := n) (U := U) (a := a) (m := m)
          (p := a) (Lsh := Lsh)
          hn hH2 h2U ha hcθ hcθ1 hθC hsep himg hinj
          (s0qn_hblk_shift hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn1 hLsh (hmq hm0)) hbudget
      · obtain ⟨Lsh, himg, hinj, hLsh, hmq'⟩ :=
          s0qn_conf_neg (H := q n) (U := U) (a := a) (m := m) h2U hH1 hmpos hm1
        have hmq'' : 10 * (|-m - 1| + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ) := by
          have h1 := hmq (by omega : m ≠ 0)
          linarith [hmq', h1]
        exact s0qn_engine (α := α) (q := q) (n := n) (U := U) (a := a) (m := m)
          (p := m * (q n : ℤ) + a + 2 * (U : ℤ)) (Lsh := Lsh)
          hn hH2 h2U ha hcθ hcθ1 hθC hsep himg hinj
          (s0qn_hblk_shift hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn1 hLsh hmq'') hbudget

end

end Work.TMC16Core.Assembly
