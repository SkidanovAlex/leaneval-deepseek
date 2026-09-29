import Mathlib
import Submission.Work.TMC16Core.Assembly.RegWin
import Submission.Work.TMC16Core.Assembly.endgame_g
import Submission.Work.TMC16Core.Assembly.s0num
import Submission.Work.TMC16Core.Assembly.s0win
import Submission.Work.TMC16Core.Assembly.s0winL
import Submission.Work.TMC16Core.Assembly.s0_uniform_q1
import Submission.Work.TMC16Core.Assembly.s0_uniform_qn
import Submission.Work.TMC16Core.Assembly.s0_uniform_q4
import Submission.Work.TMC16Core.Assembly.s0_uniform_mirror
import Submission.Work.TMC16Core.Assembly.theta_strand
import Submission.Work.TMC16Core.Core.nr_ablock

namespace Work.TMC16Core.Assembly

open Work.TMC16Core
open Filter Topology

set_option maxHeartbeats 4000000

/-- `C + 622 log H` is eventually dominated by `(H-1) ε` for `ε > 0`. -/
private lemma budget_eventually (ε C c : ℝ) (hε : 0 < ε) :
    ∀ᶠ H : ℕ in Filter.atTop, C + c * Real.log (H : ℝ) < ((H : ℝ) - 1) * ε := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (𝓝 0) := by
    simpa only [id_eq] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hCx : Tendsto (fun x : ℝ => C / x) Filter.atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hmain : Tendsto (fun x : ℝ => (C + c * Real.log x) / x) Filter.atTop (𝓝 0) := by
    have h0 : c * 0 + 0 = 0 := by ring
    have h1 := (hlog.const_mul c).add hCx
    rw [h0] at h1
    exact h1.congr' (Eventually.of_forall (fun x => by ring))
  have hev : ∀ᶠ x : ℝ in Filter.atTop, (C + c * Real.log x) / x < ε / 2 :=
    (tendsto_order.1 hmain).2 (ε / 2) (by linarith)
  have hev1 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x := eventually_ge_atTop 1
  have hevR : ∀ᶠ x : ℝ in Filter.atTop, C + c * Real.log x < x * (ε / 2) := by
    filter_upwards [hev, hev1] with x hx hx1
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    rw [div_lt_iff₀ hx0] at hx
    linarith
  have hevN : ∀ᶠ H : ℕ in Filter.atTop, C + c * Real.log (H : ℝ) < (H : ℝ) * (ε / 2) :=
    tendsto_natCast_atTop_atTop.eventually hevR
  have hev2 : ∀ᶠ H : ℕ in Filter.atTop, 2 ≤ H := eventually_ge_atTop 2
  filter_upwards [hevN, hev2] with H hH hH2
  have hH2R : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH2
  nlinarith [hH, hH2R, hε]

/-- `Uniform` is invariant under replacing the index finset by an equal one. -/
private lemma Uniform_congr_finset {ε : ℝ} {A B : Finset ℤ} (hAB : A = B) {z : ℤ → ℝ}
    (h : Uniform ε (fun j : {j : ℤ // j ∈ A} => z j)) :
    Uniform ε (fun j : {j : ℤ // j ∈ B} => z j) := by
  have hiff : ∀ x : ℤ, (x ∈ B) ↔ (x ∈ A) := by intro x; rw [hAB]
  refine Uniform_of_cos_eq (e := Equiv.subtypeEquivRight hiff)
    (z := fun j : {j : ℤ // j ∈ A} => z j) (w := fun j : {j : ℤ // j ∈ B} => z j) ?_ h
  intro k
  rfl

/-- The phase `θ + (j + ((K+1)-2)/2)α` equals `θ + (j + (K-1)/2)α`. -/
private lemma Uniform_phase_succ {ε : ℝ} {I : Finset ℤ} {K : ℕ} {θ α : ℝ}
    (h : Uniform ε (fun j : {j : ℤ // j ∈ I} =>
        θ + (((j : ℤ) : ℝ) + ((((K + 1 : ℕ) : ℝ) - 2) / 2)) * α)) :
    Uniform ε (fun j : {j : ℤ // j ∈ I} =>
        θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α) := by
  have hfun : (fun j : {j : ℤ // j ∈ I} =>
        θ + (((j : ℤ) : ℝ) + ((((K + 1 : ℕ) : ℝ) - 2) / 2)) * α)
      = (fun j : {j : ℤ // j ∈ I} =>
        θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α) := by
    funext j
    have : ((((K + 1 : ℕ) : ℝ) - 2) / 2) = (((K : ℝ) - 1) / 2) := by push_cast; ring
    rw [this]
  rw [hfun] at h
  exact h

theorem s0_reg (h4 : Work.TMC16Core.P_LEBasics) (h7 : Work.TMC16Core.P_BJ_dioph)
    {α b₀ lam L κ : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hα : Irrational α) (hb₀ : 0 < b₀) (hDioph : Work.TMC16Core.DiophBelow α b₀)
    (hL : L = Real.log lam) (hlam : Real.exp (16 * b₀ / 9) < lam)
    (hκ : 0 < κ)
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i) (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) →
      Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    {E : ℝ} (hE : E ∈ Work.TMC16Core.amoSpec α lam) {θ : ℝ}
    (hθ : θ ∉ Work.TMC16Core.Theta α) {u : ℤ → ℂ}
    (hu : Work.TMC16Core.IsGenEigen α lam θ E u) (hu0 : u 0 ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ H : ℕ, ∀ y m : ℤ,
      (H = q (n - 1) ∨ H = q n ∨ (H = 4 * q (n - 1) ∧ H < q n)) →
      (q n : ℝ) ≤ (H : ℝ) ^ 2 →
      1 ≤ y →
      (y : ℝ) ≤ 100 * (Real.rpow (q (n + 1) : ℝ) (8 / 9) + (q n : ℝ)) →
      0 ≤ m →
      (m ≠ 0 → 10 * (m + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ)) →
      ((H : ℝ) - 1) / 20 + 3 ≤ (|y - m * (q n : ℤ)| : ℝ) →
      (|y - m * (q n : ℤ)| : ℝ) ≤ 95 * ((H : ℝ) - 1) / 100 - 3 →
      Work.TMC16Core.Assembly.RegWin α lam θ (E : ℂ) (7 * L / 10)
        (((H - 1 : ℕ) : ℝ) / 40) (H - 1) y := by
  classical
  have hlam1 : 1 < lam := lt_of_le_of_lt (Real.one_le_exp (by positivity)) hlam
  have hLpos : 0 < L := by rw [hL]; exact Real.log_pos hlam1
  have hεupos : 0 < L / 1000 := by positivity
  have hm0pos : 0 < min (L / 1000) (κ / 8) := lt_min (by positivity) (by positivity)
  obtain ⟨Npd, hpd⟩ := Filter.eventually_atTop.mp
    (Work.TMC16Core.Core.pd_eventually_bound_dioph h4 h7 hα hb₀ hDioph hlam hE
      (ε := min (L / 1000) (κ / 8)) hm0pos)
  obtain ⟨Nsg, hsg⟩ := Filter.eventually_atTop.mp
    (Work.TMC16Core.Core.sing_zero hu hu0 (m := L - L / 4) (by linarith))
  obtain ⟨Cθ, Nθ, hθstr⟩ := theta_strand hθ hqpos hmono hΔeq hΔup
  obtain ⟨Kar, hKar⟩ := s0num hLpos hκ
  obtain ⟨Nb1, hb1⟩ := Filter.eventually_atTop.mp
    (budget_eventually (L / 1000) (8 * Cθ + 160 * Real.log 3 + 2 * Real.log 2) 622 hεupos)
  obtain ⟨Nb2, hb2⟩ := Filter.eventually_atTop.mp
    (budget_eventually (L / 1000) (32 * Cθ + 640 * Real.log 3 + 8 * Real.log 2) 2488 hεupos)
  refine ⟨max (max Nθ (max (Nb1 + 1) (max (Nb2 + 1) (Kar + 2))))
    (max (max 42 (Nsg + 2)) (40 * Npd + 2)), ?_⟩
  intro n hn H y m hHd hHq2 hy1 hyhi hm0 hmq hlo hhi
  have hnθ : Nθ ≤ n := by omega
  have hnNb : Nb1 + 1 ≤ n := by omega
  have hnNb2 : Nb2 + 1 ≤ n := by omega
  have hnKar : Kar + 2 ≤ n := by omega
  have hn42 : 42 ≤ n := by omega
  have hnNsg : Nsg + 2 ≤ n := by omega
  have hnNpd : 40 * Npd + 2 ≤ n := by omega
  have hid : n - 1 ≤ q (n - 1) := hmono.id_le (n - 1)
  have hHge : q (n - 1) ≤ H := by
    rcases hHd with h1 | h2 | ⟨h3, _⟩
    · rw [h1]
    · rw [h2]; exact hmono.monotone (by omega)
    · rw [h3]; omega
  have hHqn : H ≤ q n := by
    rcases hHd with h1 | h2 | ⟨h3, h4⟩
    · rw [h1]; exact hmono.monotone (by omega)
    · rw [h2]
    · rw [h3] at h4 ⊢; exact h4.le
  have hH1 : 1 ≤ H := by have := hqpos (n - 1); omega
  have hHge' : n - 1 ≤ H := le_trans hid hHge
  set K : ℕ := H - 1 with hKdef
  have hHK : H = K + 1 := by omega
  have hKgeKar : Kar ≤ K := by omega
  have hK40 : 40 ≤ K := by omega
  have hKgeNsg : Nsg ≤ K := by omega
  have hKgeNpd : Npd ≤ K / 40 := by omega
  have hHgeNb : Nb1 ≤ H := by omega
  have hHgeNb2 : Nb2 ≤ H := by omega
  obtain ⟨hm0pos', hm0le, hApos, hm0ltA, hεultA, hL1pos, hL1le, hkeyar, hgapar,
    hδ1, hδ2, hKδ, hεsle, hAleL⟩ := hKar K hKgeKar
  set A : ℝ := (L / 4) * (1 / 40 + 1 / (K : ℝ)) - min (L / 1000) (κ / 8) with hAdef
  have hgap : 4 * ((K : ℝ) + 1) * Real.exp (L - A) < Real.exp ((K : ℝ) * (A - L / 1000)) :=
    hgapar
  have hkey : (L + min (L / 1000) (κ / 8)) * ((K : ℝ) - 1 - (K : ℝ) / 40)
      - ((K : ℝ) + 1) * (L - A) + (7 * L / 10) * ((K : ℝ) / 40) < 0 := hkeyar
  have hK0R : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hHKr : (K : ℝ) = (H : ℝ) - 1 := by rw [hHK]; push_cast; ring
  have hHqnR : (H : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hHqn
  have hH1R : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
  have hqn1R : (1 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast (hqpos n)
  have hrpow_nn : 0 ≤ Real.rpow (q (n + 1) : ℝ) (8 / 9) :=
    Real.rpow_nonneg (Nat.cast_nonneg (q (n + 1))) _
  have hεsingpos : 0 < L / 4 := by linarith
  have hsin : IsSingular α lam θ (E : ℂ) (L - L / 4) K 0 := hsg K hKgeNsg
  have hbd : ∀ N : ℕ, K / 40 ≤ N → N ≤ K → ∀ ζ : ℝ,
      ‖pd α lam ζ (E : ℂ) (N + 1)‖ ≤ Real.exp ((N : ℝ) * (L + min (L / 1000) (κ / 8))) := by
    intro N hN _ ζ
    have h1 := hpd N (le_trans hKgeNpd hN) ζ
    simpa [hL] using h1
  -- window data
  set Mz : ℤ := m * (q n : ℤ) with hMzdef
  set k0 : ℤ := |y - Mz| with hk0def
  have hk0nn : 0 ≤ k0 := by rw [hk0def]; exact abs_nonneg _
  have hk0R : (k0 : ℝ) = |(y : ℝ) - (m : ℝ) * ((q n : ℤ) : ℝ)| := by
    rw [hk0def, Int.cast_abs, hMzdef]
    push_cast
    rfl
  have hlo' : (K : ℝ) / 20 + 3 ≤ (k0 : ℝ) := by
    rw [hk0R, hHKr]
    exact hlo
  have hhi' : (k0 : ℝ) ≤ 95 * (K : ℝ) / 100 - 3 := by
    rw [hk0R, hHKr]
    exact hhi
  have hk0le_qn : (k0 : ℝ) ≤ (q n : ℝ) := by
    have hKH : (K : ℝ) ≤ (H : ℝ) := by rw [hHKr]; linarith
    have h2 : 95 * (K : ℝ) / 100 - 3 ≤ (q n : ℝ) := by nlinarith [hKH, hHqnR, hqn1R]
    linarith [hhi', h2]
  have hqn0 : (0 : ℝ) ≤ (q n : ℝ) := Nat.cast_nonneg (q n)
  have hMbound : (Mz : ℝ) ≤ 100 * Real.rpow (q (n + 1) : ℝ) (8 / 9) + 101 * (q n : ℝ) := by
    by_cases hyM : Mz ≤ y
    · have hMz : Mz = y - k0 := by
        have hk0eq : k0 = y - Mz := by rw [hk0def]; exact abs_of_nonneg (by omega)
        omega
      have hcast : (Mz : ℝ) = (y : ℝ) - (k0 : ℝ) := by rw [hMz]; push_cast; ring
      have hk0nnR : (0 : ℝ) ≤ (k0 : ℝ) := by exact_mod_cast hk0nn
      linarith [hcast, hyhi, hk0nnR, hqn0]
    · have hMz : Mz = y + k0 := by
        have hk0eq : k0 = Mz - y := by
          rw [hk0def, abs_of_neg (by omega)]
          ring
        omega
      have hcast : (Mz : ℝ) = (y : ℝ) + (k0 : ℝ) := by rw [hMz]; push_cast; ring
      linarith [hcast, hyhi, hk0le_qn]
  have hMbound2 : (m : ℝ) * (q n : ℝ) ≤ 100 * Real.rpow (q (n + 1) : ℝ) (8 / 9)
      + 101 * (q n : ℝ) := by
    have h := hMbound
    rw [hMzdef] at h
    push_cast at h
    exact h
  set c : ℕ := (K + 39) / 40 with hcdef
  set a : ℤ := k0 - (K : ℤ) - (c : ℤ) with hadef
  set U : ℕ := c + 1 with hUdef
  have hcK : (c : ℤ) ≤ (K : ℤ) := by
    have h1 : c ≤ K := by
      rw [hcdef]
      exact Nat.div_le_of_le_mul (by omega : K + 39 ≤ 40 * K)
    exact_mod_cast h1
  have hk0K : k0 ≤ (K : ℤ) := by
    have h1 : (k0 : ℝ) < (K : ℝ) := by
      have h2 : 95 * (K : ℝ) / 100 - 3 < (K : ℝ) := by linarith
      linarith [hhi', h2]
    have h3 : k0 < (K : ℤ) := by exact_mod_cast h1
    omega
  have ha2H : |a| ≤ 2 * (H : ℤ) := by
    have hHKZ : (H : ℤ) = (K : ℤ) + 1 := by omega
    rw [hadef, abs_le]
    constructor <;> omega
  -- the theta-separation constant
  set Breq : ℝ := 8 * (q n : ℝ) + 8 + 2 * (100 * Real.rpow (q (n + 1) : ℝ) (8 / 9)
    + 101 * (q n : ℝ)) with hBreqdef
  set Bn : ℤ := ⌈Breq⌉ with hBndef
  have hBn1 : 1 ≤ Bn := by
    have h1 : (1 : ℝ) ≤ Breq := by rw [hBreqdef]; linarith [hqn1R, hrpow_nn]
    have h2 := Int.le_ceil Breq
    rw [← hBndef] at h2
    have : (1 : ℝ) ≤ (Bn : ℝ) := le_trans h1 h2
    exact_mod_cast this
  have hBnle : (Bn : ℝ) ≤ 1000 * (Real.rpow (q (n + 1) : ℝ) (8 / 9) + (q n : ℝ)) := by
    have h2 := Int.ceil_lt_add_one Breq
    rw [← hBndef] at h2
    rw [hBreqdef] at h2
    linarith [h2, hrpow_nn, hqn1R]
  obtain ⟨cθ, hcθpos, hcθ1, hcθlog, hcθrng⟩ := hθstr n hnθ Bn hBn1 hBnle
  have hθC : ∀ t : ℤ, 0 ≤ t → t ≤ 2 → ∀ j : ℤ, |j| ≤ 8 * ((K + 1 : ℕ) : ℤ) + 8 →
      cθ ≤ Work.TMC16Core.fracDist (2 * θ + (((j + t * m * (q n : ℤ)) : ℤ) : ℝ) * α) := by
    intro t ht0 ht2 j hj
    apply hcθrng
    have htabs : |((t : ℤ) : ℝ)| ≤ 2 := by
      have h : |t| ≤ 2 := by rw [abs_le]; omega
      rw [← Int.cast_abs]; exact_mod_cast h
    have hjabs : |((j : ℤ) : ℝ)| ≤ 8 * (H : ℝ) + 8 := by
      have h : |j| ≤ 8 * (H : ℤ) + 8 := by simpa [hHK] using hj
      rw [← Int.cast_abs]; exact_mod_cast h
    have hmabs : |((m : ℤ) : ℝ)| = (m : ℝ) := abs_of_nonneg (by exact_mod_cast hm0)
    have hstep : |(((j + t * m * (q n : ℤ) : ℤ)) : ℝ)|
        ≤ 8 * (H : ℝ) + 8 + 2 * (100 * Real.rpow (q (n + 1) : ℝ) (8 / 9) + 101 * (q n : ℝ)) := by
      have ht0R : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht0
      have ht2R : (t : ℝ) ≤ 2 := by exact_mod_cast ht2
      have hm0R : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm0
      have hqn0R : (0 : ℝ) ≤ (q n : ℝ) := Nat.cast_nonneg (q n)
      have hmq0R : (0 : ℝ) ≤ (m : ℝ) * (q n : ℝ) := mul_nonneg hm0R hqn0R
      have he : (((j + t * m * (q n : ℤ) : ℤ)) : ℝ) = (j : ℝ) + (t : ℝ) * ((m : ℝ) * (q n : ℝ)) := by
        push_cast; ring
      rw [he]
      calc |(j : ℝ) + (t : ℝ) * ((m : ℝ) * (q n : ℝ))|
          ≤ |(j : ℝ)| + |(t : ℝ) * ((m : ℝ) * (q n : ℝ))| := abs_add_le _ _
        _ = |(j : ℝ)| + (t : ℝ) * ((m : ℝ) * (q n : ℝ)) := by
              rw [abs_mul, abs_mul, abs_of_nonneg ht0R, abs_of_nonneg hm0R,
                abs_of_nonneg hqn0R]
        _ ≤ (8 * (H : ℝ) + 8)
            + 2 * (100 * Real.rpow (q (n + 1) : ℝ) (8 / 9) + 101 * (q n : ℝ)) := by
              have h1 : (t : ℝ) * ((m : ℝ) * (q n : ℝ)) ≤ 2 * ((m : ℝ) * (q n : ℝ)) :=
                mul_le_mul_of_nonneg_right ht2R hmq0R
              linarith [hjabs, h1, hMbound2]
    have hle : 8 * (H : ℝ) + 8 + 2 * (100 * Real.rpow (q (n + 1) : ℝ) (8 / 9) + 101 * (q n : ℝ))
        ≤ (Bn : ℝ) := by
      have h1 : 8 * (H : ℝ) + 8 ≤ 8 * (q n : ℝ) + 8 := by linarith [hHqnR]
      have h2 : Breq ≤ (Bn : ℝ) := by rw [hBndef]; exact Int.le_ceil Breq
      have h3 : 8 * (q n : ℝ) + 8 + 2 * (100 * Real.rpow (q (n + 1) : ℝ) (8 / 9) + 101 * (q n : ℝ))
          = Breq := by rw [hBreqdef]
      linarith [h1, h2, h3]
    exact le_trans hstep hle
  have hlog2H : Real.log (2 * (H : ℝ)) = Real.log 2 + Real.log (H : ℝ) :=
    Real.log_mul (by norm_num) (by positivity)
  have hlogqn : Real.log ((q n : ℝ) + 2) ≤ Real.log 3 + 2 * Real.log (H : ℝ) := by
    have hqn2 : (q n : ℝ) + 2 ≤ 3 * (H : ℝ) ^ 2 := by nlinarith [hHq2, hH1R]
    have h1 : Real.log ((q n : ℝ) + 2) ≤ Real.log (3 * (H : ℝ) ^ 2) :=
      Real.log_le_log (by positivity) hqn2
    have h2 : Real.log (3 * (H : ℝ) ^ 2) = Real.log 3 + 2 * Real.log (H : ℝ) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; ring
    linarith [h1, h2.le]
  have hbudget : 300 * Real.log ((K + 1 : ℕ) : ℝ) + 8 * Real.log (1 / cθ)
      + 2 * Real.log (2 * ((K + 1 : ℕ) : ℝ)) < (((K + 1 : ℕ) : ℝ) - 1) * (L / 1000) := by
    rw [← hHK, hlog2H]
    have hb' := hb1 H hHgeNb
    nlinarith [hcθlog, hlogqn, hb']
  have hbudget4 : 1200 * Real.log ((K + 1 : ℕ) : ℝ) + 32 * Real.log (1 / cθ)
      + 8 * Real.log (2 * ((K + 1 : ℕ) : ℝ)) < (((K + 1 : ℕ) : ℝ) - 1) * (L / 1000) := by
    rw [← hHK, hlog2H]
    have hb' := hb2 H hHgeNb2
    nlinarith [hcθlog, hlogqn, hb']
  -- the local endgame
  have endgame : ∀ (I₁ I₂ : Finset ℤ),
      (I₁ ∪ I₂).card = K + 1 →
      Uniform (L / 1000) (fun j : {j : ℤ // j ∈ I₁ ∪ I₂} =>
        θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α) →
      (∀ x ∈ I₁, ‖pd α lam (θ + (x : ℝ) * α) (E : ℂ) (K + 1)‖
        ≤ Real.exp (((K : ℝ) + 1) * (L - A))) →
      (∀ x ∈ I₂, x ≤ y ∧ y ≤ x + (K : ℤ) - 1 ∧
        (K : ℝ) / 40 ≤ ((y - x : ℤ) : ℝ) ∧ (K : ℝ) / 40 ≤ ((x + (K : ℤ) - 1 - y : ℤ) : ℝ)) →
      RegWin α lam θ (E : ℂ) (7 * L / 10) ((K : ℝ) / 40) K y := by
    intro I₁ I₂ hcard huni hA hgeo
    exact endgame_g (α := α) (lam := lam) (L := L) (εA := A) (εu := L / 1000)
      (εf := min (L / 1000) (κ / 8)) (L₁ := 7 * L / 10) (g := (K : ℝ) / 40)
      (E := (E : ℂ)) (θ := θ) (K := K) (I₁ := I₁) (I₂ := I₂) (y := y)
      hlam1 hL hεupos hm0pos hεultA hm0ltA hK40 hgap hcard huni hA
      (le_of_eq (by ring_nf : (K : ℝ) = 40 * ((K : ℝ) / 40)))
      hgeo hbd hL1pos hL1le hkey
  by_cases hyM : Mz ≤ y
  · -- right-hand case: `y ≥ Mz`
    obtain ⟨h2U, hcard, hsubW, hgeoW, _⟩ := s0win (K := K) (k₀ := k0) (M := Mz)
      (c := c) (a := a) (U := U) hK40 hcdef hadef hUdef
      (Int.mul_nonneg hm0 (Int.natCast_nonneg (q n))) hlo' hhi'
    have hy_eq : Mz + k0 = y := by
      have hk0eq : k0 = y - Mz := by rw [hk0def]; exact abs_of_nonneg (by omega)
      omega
    have hgeo : ∀ x ∈ W2s0 a U (K + 1) Mz, x ≤ y ∧ y ≤ x + (K : ℤ) - 1 ∧
        (K : ℝ) / 40 ≤ ((y - x : ℤ) : ℝ) ∧ (K : ℝ) / 40 ≤ ((x + (K : ℤ) - 1 - y : ℤ) : ℝ) := by
      intro x hx
      obtain ⟨h1, h2, h3, h4⟩ := hgeoW x hx
      rw [hy_eq] at h1 h2 h3 h4
      refine ⟨h1, h2, ?_, ?_⟩
      · have h5 : (K : ℝ) ≤ 40 * ((y - x : ℤ) : ℝ) := by exact_mod_cast h3
        linarith
      · have h5 : (K : ℝ) ≤ 40 * ((x + (K : ℤ) - 1 - y : ℤ) : ℝ) := by exact_mod_cast h4
        linarith
    have hA : ∀ x ∈ W1s0 a U, ‖pd α lam (θ + (x : ℝ) * α) (E : ℂ) (K + 1)‖
        ≤ Real.exp (((K : ℝ) + 1) * (L - A)) := by
      have hraw := Work.TMC16Core.Core.nr_ablock (α := α) (lam := lam) (E := (E : ℂ))
        (θ := θ) (L := L) (ε₁ := min (L / 1000) (κ / 8)) (εsing := L / 4)
        (δ := 1 / 40 + 1 / (K : ℝ)) (K := K) (I₁ := W1s0 a U)
        hLpos hm0pos hεsingpos hεsle hδ1 hδ2 hK40 hKδ hbd hsin hsubW
      intro x hx
      have h := hraw x hx
      have he : (↑K + 1) * (L - L / 4 * (1 / 40 + 1 / (K : ℝ)) + min (L / 1000) (κ / 8))
          = ((K : ℝ) + 1) * (L - A) := by rw [hAdef]; ring
      rw [he] at h
      exact h
    have huniR : Uniform (L / 1000) (fun j : {j : ℤ // j ∈ W1s0 a U ∪ W2s0 a U (K + 1) Mz} =>
        θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α) := by
      have hmq' : m ≠ 0 → 10 * (|m| + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ) := by
        intro hm
        have : |m| = m := abs_of_nonneg hm0
        rw [this]; exact hmq hm
      rcases hHd with hH1 | hH2 | ⟨hH3, hHlt⟩
      · have h := s0_uniform_q1 (α := α) (θ := θ) (ε := L / 1000) (cθ := cθ)
          (q := q) (Δ := Δ) (n := n) (H := K + 1) (U := U) (a := a) (m := m)
          hqpos hmono hΔpos hΔeq hΔup hΔlo hbest (by omega) (by rw [← hHK]; exact hH1)
          (by omega) h2U (by simpa [hHK] using ha2H) hmq' hcθpos hcθ1 hθC hbudget
        exact Uniform_phase_succ h
      · have h := s0_uniform_qn (α := α) (θ := θ) (ε := L / 1000) (cθ := cθ)
          (q := q) (Δ := Δ) (n := n) (H := K + 1) (U := U) (a := a) (m := m)
          hqpos hmono hΔpos hΔeq hΔup hΔlo hbest (by omega) (by rw [← hHK]; exact hH2)
          (by omega) h2U (by simpa [hHK] using ha2H) hmq' hcθpos hcθ1 hθC hbudget
        exact Uniform_phase_succ h
      · have h := s0_uniform_q4 (α := α) (θ := θ) (ε := L / 1000) (cθ := cθ)
          (q := q) (Δ := Δ) (n := n) (H := K + 1) (U := U) (a := a) (m := m)
          hqpos hmono hΔpos hΔeq hΔup hΔlo hbest (by omega) (by rw [← hHK]; exact hH3)
          (by rw [← hHK]; exact hHlt) (by simpa [hHK] using hHq2) (by omega) h2U
          (by simpa [hHK] using ha2H) hmq' hcθpos hcθ1 hθC hbudget4
        exact Uniform_phase_succ h
    exact endgame (W1s0 a U) (W2s0 a U (K + 1) Mz) hcard huniR hA hgeo
  · -- left-hand case: `y < Mz`
    have hyMlt : y < Mz := by omega
    have hm1 : 1 ≤ m := by
      by_contra h
      have hmlt : m ≤ 0 := by omega
      have hm00 : m = 0 := by omega
      have hzero : Mz = 0 := by rw [hMzdef, hm00]; ring
      omega
    have hMge : (K : ℤ) + 1 ≤ Mz := by
      have hHKZ : (H : ℤ) = (K : ℤ) + 1 := by omega
      have hqnZ : (H : ℤ) ≤ (q n : ℤ) := by exact_mod_cast hHqn
      have hMz_ge : (q n : ℤ) ≤ Mz := by
        rw [hMzdef]
        simpa using Int.mul_le_mul_of_nonneg_right hm1 (Int.natCast_nonneg (q n))
      omega
    obtain ⟨h2U, hcard, hsubL, hgeoW⟩ := s0winL (K := K) (k₀ := k0) (M := Mz)
      (c := c) (a := a) (U := U) hK40 hcdef hadef hUdef hMge hlo' hhi'
    have hy_eq : Mz - k0 = y := by
      have hk0eq : k0 = Mz - y := by
        rw [hk0def, abs_of_neg (by omega)]
        ring
      omega
    have hgeo : ∀ x ∈ W2s0L a U (K + 1) Mz, x ≤ y ∧ y ≤ x + (K : ℤ) - 1 ∧
        (K : ℝ) / 40 ≤ ((y - x : ℤ) : ℝ) ∧ (K : ℝ) / 40 ≤ ((x + (K : ℤ) - 1 - y : ℤ) : ℝ) := by
      intro x hx
      obtain ⟨h1, h2, h3, h4⟩ := hgeoW x hx
      rw [hy_eq] at h1 h2 h3 h4
      refine ⟨h1, h2, ?_, ?_⟩
      · have h5 : (K : ℝ) ≤ 40 * ((y - x : ℤ) : ℝ) := by exact_mod_cast h3
        linarith
      · have h5 : (K : ℝ) ≤ 40 * ((x + (K : ℤ) - 1 - y : ℤ) : ℝ) := by exact_mod_cast h4
        linarith
    have hA : ∀ x ∈ W1s0L a U (K + 1), ‖pd α lam (θ + (x : ℝ) * α) (E : ℂ) (K + 1)‖
        ≤ Real.exp (((K : ℝ) + 1) * (L - A)) := by
      have hraw := Work.TMC16Core.Core.nr_ablock (α := α) (lam := lam) (E := (E : ℂ))
        (θ := θ) (L := L) (ε₁ := min (L / 1000) (κ / 8)) (εsing := L / 4)
        (δ := 1 / 40 + 1 / (K : ℝ)) (K := K) (I₁ := W1s0L a U (K + 1))
        hLpos hm0pos hεsingpos hεsle hδ1 hδ2 hK40 hKδ hbd hsin hsubL
      intro x hx
      have h := hraw x hx
      have he : (↑K + 1) * (L - L / 4 * (1 / 40 + 1 / (K : ℝ)) + min (L / 1000) (κ / 8))
          = ((K : ℝ) + 1) * (L - A) := by rw [hAdef]; ring
      rw [he] at h
      exact h
    have hθCm : ∀ t : ℤ, 0 ≤ t → t ≤ 2 → ∀ j : ℤ, |j| ≤ 8 * ((K + 1 : ℕ) : ℤ) + 8 →
        cθ ≤ Work.TMC16Core.fracDist (2 * (-θ) + (((j + t * (-m) * (q n : ℤ)) : ℤ) : ℝ) * α) := by
      intro t ht0 ht2 j hj
      have hj' : |(-j)| ≤ 8 * ((K + 1 : ℕ) : ℤ) + 8 := by
        simpa using hj
      have h := hθC t ht0 ht2 (-j) hj'
      have he : 2 * (-θ) + (((j + t * (-m) * (q n : ℤ)) : ℤ) : ℝ) * α
          = -(2 * θ + ((((-j) + t * m * (q n : ℤ)) : ℤ) : ℝ) * α) := by push_cast; ring
      rw [he, Work.TMC16Core.Core.fracDist_neg]
      exact h
    have hmq'' : (-m) ≠ 0 → 10 * (|(-m)| + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ) := by
      intro hm
      have hmne : m ≠ 0 := by simpa using hm
      have habs : |(-m)| = m := by rw [abs_neg]; exact abs_of_nonneg hm0
      rw [habs]; exact hmq hmne
    have huniW : Uniform (L / 1000)
        (fun j : {j : ℤ // j ∈ W1s0 a U ∪ W2s0 a U (K + 1) ((-m) * (q n : ℤ))} =>
          -θ + (((j : ℤ) : ℝ) + ((((K + 1 : ℕ) : ℝ) - 2) / 2)) * α) := by
      rcases hHd with hH1 | hH2 | ⟨hH3, hHlt⟩
      · exact s0_uniform_q1 (α := α) (θ := -θ) (ε := L / 1000) (cθ := cθ)
          (q := q) (Δ := Δ) (n := n) (H := K + 1) (U := U) (a := a) (m := -m)
          hqpos hmono hΔpos hΔeq hΔup hΔlo hbest (by omega) (by rw [← hHK]; exact hH1)
          (by omega) h2U (by simpa [hHK] using ha2H) hmq'' hcθpos hcθ1 hθCm hbudget
      · exact s0_uniform_qn (α := α) (θ := -θ) (ε := L / 1000) (cθ := cθ)
          (q := q) (Δ := Δ) (n := n) (H := K + 1) (U := U) (a := a) (m := -m)
          hqpos hmono hΔpos hΔeq hΔup hΔlo hbest (by omega) (by rw [← hHK]; exact hH2)
          (by omega) h2U (by simpa [hHK] using ha2H) hmq'' hcθpos hcθ1 hθCm hbudget
      · exact s0_uniform_q4 (α := α) (θ := -θ) (ε := L / 1000) (cθ := cθ)
          (q := q) (Δ := Δ) (n := n) (H := K + 1) (U := U) (a := a) (m := -m)
          hqpos hmono hΔpos hΔeq hΔup hΔlo hbest (by omega) (by rw [← hHK]; exact hH3)
          (by rw [← hHK]; exact hHlt) (by simpa [hHK] using hHq2) (by omega) h2U
          (by simpa [hHK] using ha2H) hmq'' hcθpos hcθ1 hθCm hbudget4
    have hW : Uniform (L / 1000)
        (fun j : {j : ℤ // j ∈ W1s0 a U ∪ W2s0 a U (K + 1) (-Mz)} =>
          -θ + (((j : ℤ) : ℝ) + ((((K + 1 : ℕ) : ℝ) - 2) / 2)) * α) := by
      have hfe : ((-m) * (q n : ℤ)) = -Mz := by rw [hMzdef]; ring
      have hwin : W1s0 a U ∪ W2s0 a U (K + 1) ((-m) * (q n : ℤ))
          = W1s0 a U ∪ W2s0 a U (K + 1) (-Mz) := by rw [hfe]
      exact Uniform_congr_finset (z := fun k : ℤ =>
        -θ + (((k : ℤ) : ℝ) + ((((K + 1 : ℕ) : ℝ) - 2) / 2)) * α) hwin huniW
    have huniL : Uniform (L / 1000)
        (fun j : {j : ℤ // j ∈ W1s0L a U (K + 1) ∪ W2s0L a U (K + 1) Mz} =>
          θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α) := by
      have h := s0_uniform_mirror (α := α) (θ := θ) (ε := L / 1000) (H := K + 1)
        (U := U) (a := a) (M := Mz) hW
      exact Uniform_phase_succ h
    exact endgame (W1s0L a U (K + 1)) (W2s0L a U (K + 1) Mz) hcard huniL hA hgeo

end Work.TMC16Core.Assembly
