import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Assembly.Consts
import Submission.Work.Assembly.rate_log_ratio
import Submission.Work.Assembly.rate_theta_bound
import Submission.Work.Assembly.rate_tendsto_small
import Submission.Work.Assembly.nr_log_qn_bound

/-!
# The uniformity-rate bound `rateNR1 ≤ L/8 + L/100` of the non-resonant branch

This is the numerical heart of AJ §9's hypothesis `λ > e^{16 b₀/9}`: for the continued
fraction data `q, Δ` of a Diophantine frequency `α` (with exponent `b₀`), the rate

`rateNR1 q n s c = 2 log(q n / s)/q(n-1) + 200 log q(n-1)/q(n-1)
                     + 2 log(1/c)/(s q(n-1)) + 200/q(n-1)`

is at most `L/8 + L/100` as soon as `L = log λ > 16 b₀/9`, at every level `n` large enough,
uniformly in the two "geometry" parameters `s ≥ 3` and the charge `c` (whose only role is the
θ-budget `log(1/c) ≤ Cθ + 20 log(q n + 2)`).

The estimate is

`rateNR1 ≤ (2/9) b₀ + o(1) ≤ L/8 + L/100`,

where

* `q n < e^{b₀ q(n-1)}` comes from `DiophBelow α b₀` applied at `k = q(n-1)`, combined with
  the best-approximation bound `Δ(n-1) < 1/q(n)`;
* the non-resonance hypothesis `(q n)^{8/9} < (s+1) q(n-1)` and `s ≥ 3` give
  `q n / s < (4/3) q(n-1) (q n)^{1/9}`, whence the main term is `≤ (2/9) b₀ + o(1)`;
* `s q(n-1) > (3/4) (q n)^{8/9}` kills the θ-charge term;
* `b₀ < 9L/16` gives `(2/9) b₀ < L/8`.

The statement below is the form consumed by the glue (`Assembly/Glue.lean`) and by
`Main.nr_branch_ge3`.
-/

namespace Work.TMC16Core.Assembly

open Work.TMC16Core

/-- **The uniformity-rate bound, with an explicit θ-constant.**  For every fixed `Cθ` the
bound `rateNR1 q n s c ≤ L/8 + L/100` holds for all sufficiently large `n`, uniformly in
`s ≥ 3` and in `c > 0` satisfying `log(1/c) ≤ Cθ + 20 log(q n + 2)`. -/
theorem rate_nr_bound_gen {α b₀ L : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hb₀ : 0 < b₀) (hDioph : Work.TMC16Core.DiophBelow α b₀)
    (hLb : 16 * b₀ / 9 < L)
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (Cθ : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ s : ℕ, ∀ c : ℝ,
      3 ≤ s → Real.rpow (q n : ℝ) (8 / 9) < (((s + 1) * q (n - 1) : ℕ) : ℝ) →
      2 * s * q (n - 1) < q n → 0 < c →
      Real.log (1 / c) ≤ Cθ + 20 * Real.log ((q n : ℝ) + 2) →
      rateNR1 q n s c ≤ L / 8 + L / 100 := by
  have hLpos : 0 < L := by linarith
  have hb0 : (2 / 9) * b₀ ≤ L / 8 := by linarith
  obtain ⟨Q₀, hQ₀⟩ := (Work.Assembly.rate_tendsto_small L hLpos Cθ).1
  obtain ⟨R₀, hR₀⟩ := (Work.Assembly.rate_tendsto_small L hLpos Cθ).2
  obtain ⟨Nd, hNd⟩ :=
    Work.Assembly.nr_log_qn_bound hb₀ hDioph hmono hqpos hΔeq hΔup
  -- the denominators grow at least linearly
  have hq_ge : ∀ k : ℕ, q 0 + k ≤ q k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hlt : q k < q (k + 1) := hmono (Nat.lt_succ_self k)
        omega
  refine ⟨max Nd (max (Nat.ceil Q₀ + 1) (Nat.ceil R₀ + 1)), ?_⟩
  intro n hn s c hs3 hnres h2s hcpos hclog
  have hnNd : Nd ≤ n := le_trans (le_max_left _ _) hn
  have hnQ0 : Nat.ceil Q₀ + 1 ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnR0 : Nat.ceil R₀ + 1 ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hn1 : 1 ≤ n := by omega
  set R : ℝ := (q n : ℝ) with hRdef
  set Q : ℝ := (q (n - 1) : ℝ) with hQdef
  have hRpos : 0 < R := by rw [hRdef]; exact_mod_cast hqpos n
  have hQpos : 0 < Q := by rw [hQdef]; exact_mod_cast hqpos (n - 1)
  have hs3R : (3 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs3
  -- `q(n-1) ≥ Q₀`
  have hQge : Q₀ ≤ Q := by
    rw [hQdef]
    have h1 : Nat.ceil Q₀ ≤ n - 1 := by omega
    have h2 : Nat.ceil Q₀ ≤ q (n - 1) := by
      have h3 : q 0 + (n - 1) ≤ q (n - 1) := hq_ge (n - 1)
      omega
    have h4 : (Nat.ceil Q₀ : ℝ) ≤ (q (n - 1) : ℝ) := by exact_mod_cast h2
    have h5 : Q₀ ≤ (Nat.ceil Q₀ : ℝ) := Nat.le_ceil Q₀
    linarith
  -- `q n ≥ R₀`
  have hRge : R₀ ≤ R := by
    rw [hRdef]
    have h1 : Nat.ceil R₀ ≤ n := by omega
    have h2 : Nat.ceil R₀ ≤ q n := by
      have h3 : q 0 + n ≤ q n := hq_ge n
      omega
    have h4 : (Nat.ceil R₀ : ℝ) ≤ (q n : ℝ) := by exact_mod_cast h2
    have h5 : R₀ ≤ (Nat.ceil R₀ : ℝ) := Nat.le_ceil R₀
    linarith
  -- `log(q n) < b₀ q(n-1)`: the Diophantine lower bound meets the best-approximation bound
  have hlogR : Real.log R ≤ b₀ * Q := by
    have h := hNd n hnNd
    rw [← hRdef, ← hQdef] at h
    exact le_of_lt h
  -- non-resonance, in the casting used below
  have hnonres : R ^ (8 / 9 : ℝ) < ((s : ℝ) + 1) * Q := by
    have h := hnres
    have hcast : (((s + 1) * q (n - 1) : ℕ) : ℝ) = ((s : ℝ) + 1) * Q := by
      rw [hQdef]; push_cast; ring
    rw [hcast] at h
    exact h
  have hratio := Work.Assembly.rate_log_ratio hRpos hQpos hs3R hnonres
  -- main term
  have hterm1 : 2 * Real.log (R / (s : ℝ)) / Q ≤
      (2 / 9) * b₀ + (2 * Real.log (4 / 3) + 2 * Real.log Q) / Q := by
    have h1 : 2 * Real.log (R / (s : ℝ)) ≤
        2 * (Real.log (4 / 3) + Real.log Q + (1 / 9) * Real.log R) := by linarith [hratio]
    have h2 : 2 * Real.log (R / (s : ℝ)) / Q ≤
        (2 * (Real.log (4 / 3) + Real.log Q + (1 / 9) * Real.log R)) / Q :=
      div_le_div_of_nonneg_right h1 (le_of_lt hQpos)
    have h3 : (2 * (Real.log (4 / 3) + Real.log Q + (1 / 9) * Real.log R)) / Q
        = (2 * Real.log (4 / 3) + 2 * Real.log Q) / Q + ((2 / 9) * Real.log R) / Q := by
      rw [← add_div]; ring
    have h4 : ((2 / 9) * Real.log R) / Q ≤ (2 / 9) * b₀ := by
      rw [div_le_iff₀ hQpos]
      have h4a : (2 / 9) * Real.log R ≤ (2 / 9) * (b₀ * Q) := by linarith [hlogR]
      have h4b : (2 / 9) * b₀ * Q = (2 / 9) * (b₀ * Q) := by ring
      rw [h4b]; exact h4a
    rw [h3] at h2
    linarith [h2, h4]
  have ht12 : 2 * Real.log (R / (s : ℝ)) / Q + 200 * Real.log Q / Q ≤
      (2 / 9) * b₀ + (2 * Real.log (4 / 3) + 202 * Real.log Q) / Q := by
    have he : (2 * Real.log (4 / 3) + 2 * Real.log Q) / Q + 200 * Real.log Q / Q
        = (2 * Real.log (4 / 3) + 202 * Real.log Q) / Q := by
      rw [← add_div]; ring
    linarith [hterm1, he]
  -- θ-charge term
  have hterm3 : 2 * Real.log (1 / c) / ((s : ℝ) * Q) ≤
      (8 / 3) * (|Cθ| + 20 * Real.log (R + 2)) / R ^ (8 / 9 : ℝ) :=
    Work.Assembly.rate_theta_bound hRpos hQpos hs3R hnonres hcpos hclog
  have hrate : rateNR1 q n s c ≤
      (2 / 9) * b₀ + ((2 * Real.log (4 / 3) + 202 * Real.log Q) / Q)
        + (8 / 3) * (|Cθ| + 20 * Real.log (R + 2)) / R ^ (8 / 9 : ℝ) + 200 / Q := by
    rw [rateNR1]
    rw [← hRdef, ← hQdef]
    linarith [ht12, hterm3]
  have hbracket : (2 * Real.log (4 / 3) + 202 * Real.log Q) / Q + 200 / Q ≤ L / 200 :=
    hQ₀ Q hQge
  have htb : (8 / 3) * (|Cθ| + 20 * Real.log (R + 2)) / R ^ (8 / 9 : ℝ) ≤ L / 200 :=
    hR₀ R hRge
  linarith [hrate, hbracket, htb, hb0]

theorem rate_nr_bound {α b₀ lam L : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hα : Irrational α) (hb₀ : 0 < b₀) (hDioph : Work.TMC16Core.DiophBelow α b₀)
    (hL : L = Real.log lam) (hLb : 16 * b₀ / 9 < L)
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i) (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ))) :
    ∃ Cθ : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ s : ℕ, ∀ c : ℝ,
      3 ≤ s → Real.rpow (q n : ℝ) (8 / 9) < (((s + 1) * q (n - 1) : ℕ) : ℝ) →
      2 * s * q (n - 1) < q n → 0 < c →
      Real.log (1 / c) ≤ Cθ + 20 * Real.log ((q n : ℝ) + 2) →
      Work.TMC16Core.Assembly.rateNR1 q n s c ≤ L / 8 + L / 100 := by
  obtain ⟨N, hN⟩ := rate_nr_bound_gen hb₀ hDioph hLb hqpos hmono hΔeq hΔup 0
  exact ⟨0, N, hN⟩

end Work.TMC16Core.Assembly
