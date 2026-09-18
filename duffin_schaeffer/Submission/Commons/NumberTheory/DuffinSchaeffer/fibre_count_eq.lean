import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Star
import Submission.Commons.NumberTheory.DuffinSchaeffer.residue_fiber_formula

/-!
# `fibre_count_eq` — exact count of close reduced pairs (Duffin–Schaeffer)

Count of pairs `(a,b)`, `0 ≤ a < m`, `gcd a m = 1`, `0 ≤ b < n`,
`gcd b n = 1` with `∃ j : Fin 3, |a·n − b·m − (j−1)·mn| < s·mn`
equals `2·Φ·Σ_{c ≤ ⌈W⌉−1, gcd c q = 1} S(c)` with `g = gcd m n`,
`M = m/g`, `N = n/g`, `q = MN`, `L = gq`, `W = sL`,
`Φ = ∏_{p | q} φ(p^{ν_p g})`, `K = ∏_{p | g, p ∤ q} p^{ν_p g}`,
`S c = ∏_{p | K} (p | c ? φ(p^{ν_p K}) : p^{ν_p K − 1}·(p−2))`.

## Outline

For each pair define `D = a·N − b·M ∈ (−L, L)`, coprime to `q`, and its residue
`e = D mod L`.  The window condition is `min(e, L−e) < s·L`; grouping the
counted pairs by residue gives `2·Σ_{1 ≤ e < W} C(e)` where `C(e)` is the
fibre count over the residue `e`.  The core lemma `residue_fiber_formula`
(shared commons) gives `C(e) = Φ·S(e)` for `gcd e q = 1` and `0` otherwise,
and `{e : 1 ≤ e < W} = Icc 1 (⌈W⌉₊ − 1)`, giving the statement.
-/

open scoped BigOperators

namespace Commons.NumberTheory.DuffinSchaeffer

set_option linter.unusedVariables false

/-! ## Section 1 — elementary arithmetic of `g M N q L` -/

/-- `(m.gcd n) · (m / (m.gcd n)) = m`. -/
private lemma gcd_mul_div_self (m n : ℕ) : (m.gcd n) * (m / (m.gcd n)) = m := by
  rw [Nat.mul_comm]
  exact Nat.div_mul_cancel (Nat.gcd_dvd_left m n)

/-- `m·n/(g·g) = M·N` with `g = gcd m n`, `M = m/g`, `N = n/g`. -/
private lemma mul_div_gcd_sq (m n : ℕ) :
    m * n / ((m.gcd n) * (m.gcd n)) = (m / (m.gcd n)) * (n / (m.gcd n)) := by
  exact (Nat.div_mul_div_comm (Nat.gcd_dvd_left m n) (Nat.gcd_dvd_right m n)).symm

/-- `(g·g) ∣ m·n`. -/
private lemma gcd_sq_dvd_mul (m n : ℕ) : (m.gcd n) * (m.gcd n) ∣ m * n := by
  exact Nat.mul_dvd_mul (Nat.gcd_dvd_left m n) (Nat.gcd_dvd_right m n)

/-- `m·n/g = g·M·N` with `M = m/g`, `N = n/g`, provided `0 < m`. -/
private lemma mul_div_gcd (m n : ℕ) (hm : 0 < m) :
    m * n / (m.gcd n) = (m.gcd n) * ((m / (m.gcd n)) * (n / (m.gcd n))) := by
  classical
  let g := m.gcd n
  have hg : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_left (m := m) n hm
  have hMN : (m / g) * (n / g) = m * n / (g * g) := by
    simpa [g] using (mul_div_gcd_sq m n).symm
  have hprod : m * n = (g * g) * ((m / g) * (n / g)) := by
    calc
      m * n = (m * n / (g * g)) * (g * g) := by
        rw [Nat.div_mul_cancel (gcd_sq_dvd_mul m n)]
      _ = (g * g) * (m * n / (g * g)) := by rw [Nat.mul_comm]
      _ = (g * g) * ((m / g) * (n / g)) := by rw [hMN]
  calc
    m * n / g = ((g * ((m / g) * (n / g))) * g) / g := by
      congr 1
      rw [hprod]
      ring
    _ = g * ((m / g) * (n / g)) := by
      rw [mul_assoc, Nat.mul_div_right _ hg, Nat.mul_comm]

/-- `(m/g)` and `(n/g)` are coprime when `0 < m`. -/
private lemma coprime_gcd_div (m n : ℕ) (hm : 0 < m) :
    (m / (m.gcd n)).Coprime (n / (m.gcd n)) := by
  exact Nat.coprime_div_gcd_div_gcd (m := m) (n := n)
    (Nat.gcd_pos_of_pos_left (m := m) n hm)

/-- `m = (m.gcd n)·(m/(m.gcd n))`. -/
private lemma self_eq_gcd_mul_div (m n : ℕ) : m = (m.gcd n) * (m / (m.gcd n)) :=
  (gcd_mul_div_self m n).symm

/-- `n = (m.gcd n)·(n/(m.gcd n))`. -/
private lemma self_eq_gcd_mul_div' (m n : ℕ) : n = (m.gcd n) * (n / (m.gcd n)) := by
  calc
    n = (n.gcd m) * (n / (n.gcd m)) := self_eq_gcd_mul_div n m
    _ = (m.gcd n) * (n / (m.gcd n)) := by rw [Nat.gcd_comm]

/-- positivity of `m/(m.gcd n)` when `0 < m`. -/
private lemma gcd_div_pos (m n : ℕ) (hm : 0 < m) : 0 < m / (m.gcd n) := by
  have hg : (m.gcd n) ≤ m := Nat.gcd_le_left (m := m) n hm
  exact Nat.div_pos hg (Nat.gcd_pos_of_pos_left (m := m) n hm)

/-- `n/g ≤ n`. -/
private lemma div_gcd_le_self (m n : ℕ) : n / (m.gcd n) ≤ n := Nat.div_le_self n (m.gcd n)

/-! ## Section 2 — the residue window analysis -/

/-- reduced residues below `m` -/
private def U (m : ℕ) : Finset ℕ := (Finset.range m).filter (fun a => a.gcd m = 1)

/-- residue of `a·N − b·M` modulo `L`, in `[0, L)`. -/
private def eRes (M N L : ℕ) (ab : ℕ × ℕ) : ℕ :=
  (ab.1 * N + L - ab.2 * M) % L

/-- fibre of the residue map. -/
private def fibre (m n M N L : ℕ) (e : ℕ) : ℕ :=
  ((U m ×ˢ U n).filter (fun ab => eRes M N L ab = e)).card

/-- `a·N < L` when `a < g·M`, `0 < N`, `L = g·M·N`. -/
private lemma mul_lt_L_of_lt_gM {g M N L : ℕ} (hN : 0 < N) (hL : L = g * M * N)
    {a : ℕ} (ha : a < g * M) : a * N < L := by
  rw [hL]
  calc
    a * N < (g * M) * N := Nat.mul_lt_mul_of_pos_right ha hN
    _ = g * M * N := by ring

/-- `b·M < L` when `b < g·N`, `0 < M`, `L = g·M·N`. -/
private lemma mul_lt_L_of_lt_gN {g M N L : ℕ} (hM : 0 < M) (hL : L = g * M * N)
    {b : ℕ} (hb : b < g * N) : b * M < L := by
  rw [hL]
  calc
    b * M < (g * N) * M := Nat.mul_lt_mul_of_pos_right hb hM
    _ = g * M * N := by ring

/-- the ℤ-value `D = aN − bM` satisfies `−L < D < L`. -/
private lemma zsub_lt_L {g M N L : ℕ} (hM : 0 < M) (hN : 0 < N) (hL : L = g * M * N)
    {a : ℕ} (ha : a < g * M) {b : ℕ} (hb : b < g * N) :
    -((L : ℤ)) < ((a : ℤ) * (N : ℤ) - (b : ℤ) * (M : ℤ)) ∧
      ((a : ℤ) * (N : ℤ) - (b : ℤ) * (M : ℤ)) < (L : ℤ) := by
  have haN : a * N < L := mul_lt_L_of_lt_gM (g := g) hN hL ha
  have hbM : b * M < L := mul_lt_L_of_lt_gN (g := g) hM hL hb
  have h1 : (a : ℤ) * (N : ℤ) < (L : ℤ) := by exact_mod_cast haN
  have h2 : (b : ℤ) * (M : ℤ) < (L : ℤ) := by exact_mod_cast hbM
  have h1' : 0 ≤ (a : ℤ) * (N : ℤ) := by positivity
  have h2' : 0 ≤ (b : ℤ) * (M : ℤ) := by positivity
  constructor <;> linarith


/-- `t ∈ {-1,0,1}` from the finset. -/
private lemma t_cases {t : ℤ} (h : t ∈ (Finset.Icc (-1 : ℤ) 1 : Finset ℤ)) :
    t = -1 ∨ t = 0 ∨ t = 1 := by
  have h1 : (-1 : ℤ) ≤ t := (Finset.mem_Icc.mp h).1
  have h2 : t ≤ 1 := (Finset.mem_Icc.mp h).2
  omega

/-- For `u ∈ [0, L)`, `∃t∈{-1,0,1}` with `|u − tL| < W` iff `u < W` or `L−u < W`. -/
private lemma window_pos (L u : ℕ) (huL : u < L) (W : ℝ) :
    (∃ t ∈ (Finset.Icc (-1 : ℤ) 1 : Finset ℤ),
        |(((u : ℤ) - t * (L : ℤ)) : ℝ)| < W) ↔
      (((u : ℕ) : ℝ) < W ∨ (((L - u : ℕ) : ℝ) < W)) := by
  have huLc : (u : ℝ) < (L : ℝ) := by exact_mod_cast huL
  constructor
  · rintro ⟨t, ht, hlt⟩
    rcases t_cases ht with ht | ht | ht
    · right
      have hh : |(u : ℝ) + (L : ℝ)| < W := by
        simpa [ht] using hlt
      have hz : |(u : ℝ) + (L : ℝ)| = (u : ℝ) + (L : ℝ) := abs_of_nonneg (by positivity)
      have hlt' : (u : ℝ) + (L : ℝ) < W := by rwa [hz] at hh
      have hsub : (((L - u : ℕ) : ℝ)) = (L : ℝ) - (u : ℝ) := by
        exact Nat.cast_sub (Nat.le_of_lt huL)
      rw [hsub]
      linarith
    · left
      have hh : |(u : ℝ)| < W := by simpa [ht] using hlt
      have hz : |(u : ℝ)| = (u : ℝ) := abs_of_nonneg (by positivity)
      have hlt' : (u : ℝ) < W := by rwa [hz] at hh
      exact hlt'
    · right
      have hh : |(u : ℝ) - (L : ℝ)| < W := by simpa [ht] using hlt
      have hz : |(u : ℝ) - (L : ℝ)| = (L : ℝ) - (u : ℝ) := by
        rw [abs_of_nonpos (by linarith : (u : ℝ) - (L : ℝ) ≤ 0)]
        ring
      have hlt' : (L : ℝ) - (u : ℝ) < W := by rwa [hz] at hh
      have hsub : (((L - u : ℕ) : ℝ)) = (L : ℝ) - (u : ℝ) := by
        exact Nat.cast_sub (Nat.le_of_lt huL)
      rwa [hsub]
  · intro h
    rcases h with h | h
    · refine ⟨0, by simp, ?_⟩
      simpa using h
    · refine ⟨1, by simp, ?_⟩
      have h1 : |(u : ℝ) - (L : ℝ)| = (((L - u : ℕ) : ℝ)) := by
        have hsub : (((L - u : ℕ) : ℝ)) = (L : ℝ) - (u : ℝ) := by
          exact Nat.cast_sub (Nat.le_of_lt huL)
        rw [abs_of_nonpos (by linarith : (u : ℝ) - (L : ℝ) ≤ 0), hsub]
        ring
      simpa [h1] using h

/-- eRes in the case `b·M ≤ a·N`. -/
private lemma eRes_pos_case {M N L : ℕ} {a b : ℕ} (hle : b * M ≤ a * N)
    (hlt : a * N - b * M < L) : ((a * N + L - b * M) % L) = a * N - b * M := by
  have hsum : a * N + L - b * M = L + (a * N - b * M) := by omega
  rw [hsum]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hlt]

/-- eRes in the case `a·N < b·M`. -/
private lemma eRes_neg_case {M N L : ℕ} {a b : ℕ} (hlt : a * N < b * M)
    (hlt2 : b * M - a * N < L) : ((a * N + L - b * M) % L) = L - (b * M - a * N) := by
  have hsum : a * N + L - b * M = L - (b * M - a * N) := by omega
  rw [hsum]
  have hmain : (L - (b * M - a * N)) % L = L - (b * M - a * N) := by
    apply Nat.mod_eq_of_lt
    omega
  exact hmain


private lemma Dℝ_pos {M N : ℕ} {a b : ℕ} (hle : b * M ≤ a * N) :
    ((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) = ((a * N - b * M : ℕ) : ℝ) := by
  rw [Nat.cast_sub hle]
  norm_num
private lemma Dℝ_neg {M N : ℕ} {a b : ℕ} (hlt : a * N < b * M) :
    ((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) = -((b * M - a * N : ℕ) : ℝ) := by
  rw [Nat.cast_sub (le_of_lt hlt)]
  norm_num

/-- window at value `u` (ℝ), `u ∈ [0, L)` -/
private lemma window_pos_R (L u : ℕ) (huL : u < L) (W : ℝ) :
    (∃ t ∈ (Finset.Icc (-1 : ℤ) 1 : Finset ℤ),
        |((u : ℝ) - (t : ℝ) * (L : ℝ))| < W) ↔
      (((u : ℕ) : ℝ) < W ∨ (((L - u : ℕ) : ℝ) < W)) := by
  have huLc : (u : ℝ) < (L : ℝ) := by exact_mod_cast huL
  constructor
  · rintro ⟨t, ht, hlt⟩
    rcases t_cases ht with ht | ht | ht
    · right
      have hlt1 : |(u : ℝ) + (L : ℝ)| < W := by simpa [ht] using hlt
      have hz : |(u : ℝ) + (L : ℝ)| = (u : ℝ) + (L : ℝ) := abs_of_nonneg (by positivity)
      have hlt' : (u : ℝ) + (L : ℝ) < W := by rwa [hz] at hlt1
      have hsub : (((L - u : ℕ) : ℝ)) = (L : ℝ) - (u : ℝ) := by
        exact Nat.cast_sub (Nat.le_of_lt huL)
      rw [hsub]
      linarith
    · left
      have hlt0 : |(u : ℝ)| < W := by simpa [ht] using hlt
      have hz : |(u : ℝ)| = (u : ℝ) := abs_of_nonneg (by positivity)
      have hlt' : (u : ℝ) < W := by rwa [hz] at hlt0
      exact hlt'
    · right
      have hlt2 : |(u : ℝ) - (L : ℝ)| < W := by simpa [ht] using hlt
      have hz : |(u : ℝ) - (L : ℝ)| = (L : ℝ) - (u : ℝ) := by
        rw [abs_of_nonpos (by linarith : (u : ℝ) - (L : ℝ) ≤ 0)]
        ring
      have hlt' : (L : ℝ) - (u : ℝ) < W := by rwa [hz] at hlt2
      have hsub : (((L - u : ℕ) : ℝ)) = (L : ℝ) - (u : ℝ) := by
        exact Nat.cast_sub (Nat.le_of_lt huL)
      rwa [hsub]
  · intro h
    rcases h with h | h
    · refine ⟨0, by simp, ?_⟩
      simpa using h
    · refine ⟨1, by simp, ?_⟩
      have h1 : |(u : ℝ) - (L : ℝ)| = (((L - u : ℕ) : ℝ)) := by
        have hsub : (((L - u : ℕ) : ℝ)) = (L : ℝ) - (u : ℝ) := by
          exact Nat.cast_sub (Nat.le_of_lt huL)
        rw [abs_of_nonpos (by linarith : (u : ℝ) - (L : ℝ) ≤ 0), hsub]
        ring
      simpa [h1] using h

/-- window at value `−u` (ℝ): the shifts `t` range over `{-1,0,1}` and
`|−u − tL|` takes the values `u`, `L−u`, `u+L`. -/
private lemma window_neg_R (L u : ℕ) (huL : u < L) (W : ℝ) :
    (∃ t ∈ (Finset.Icc (-1 : ℤ) 1 : Finset ℤ),
        |(-(u : ℝ) - (t : ℝ) * (L : ℝ))| < W) ↔
      (((u : ℕ) : ℝ) < W ∨ (((L - u : ℕ) : ℝ) < W)) := by
  have huLc : (u : ℝ) < (L : ℝ) := by exact_mod_cast huL
  constructor
  · rintro ⟨t, ht, hlt⟩
    rcases t_cases ht with ht | ht | ht
    · right
      have htmp : (-(u : ℝ) - ((t : ℝ) * (L : ℝ))) = (L : ℝ) - (u : ℝ) := by
        rw [ht]
        norm_num
        ring
      have hlt1 : |(L : ℝ) - (u : ℝ)| < W := by
        rwa [htmp] at hlt
      have hz : |(L : ℝ) - (u : ℝ)| = (L : ℝ) - (u : ℝ) := abs_of_nonneg (by linarith)
      have hlt' : (L : ℝ) - (u : ℝ) < W := by rwa [hz] at hlt1
      have hsub : (((L - u : ℕ) : ℝ)) = (L : ℝ) - (u : ℝ) := by
        exact Nat.cast_sub (Nat.le_of_lt huL)
      rwa [hsub]
    · left
      have htmp : (-(u : ℝ) - ((t : ℝ) * (L : ℝ))) = -(u : ℝ) := by
        rw [ht]
        norm_num
      have hlt0 : |(u : ℝ)| < W := by
        rwa [htmp, abs_neg] at hlt
      have hz : |(u : ℝ)| = (u : ℝ) := abs_of_nonneg (by positivity)
      have hlt' : (u : ℝ) < W := by rwa [hz] at hlt0
      exact hlt'
    · right
      have htmp : (-(u : ℝ) - ((t : ℝ) * (L : ℝ))) = -((u : ℝ) + (L : ℝ)) := by
        rw [ht]
        norm_num
        ring
      have hlt2 : |(u : ℝ) + (L : ℝ)| < W := by
        rwa [htmp, abs_neg] at hlt
      have hz : |(u : ℝ) + (L : ℝ)| = (u : ℝ) + (L : ℝ) := abs_of_nonneg (by positivity)
      have hlt' : (u : ℝ) + (L : ℝ) < W := by rwa [hz] at hlt2
      have hsub : (((L - u : ℕ) : ℝ)) = (L : ℝ) - (u : ℝ) := by
        exact Nat.cast_sub (Nat.le_of_lt huL)
      rw [hsub]
      linarith
  · intro h
    rcases h with h | h
    · refine ⟨0, by simp, ?_⟩
      have htmp : (-(u : ℝ) - ((0 : ℤ) : ℝ) * (L : ℝ)) = -(u : ℝ) := by norm_num
      rw [htmp, abs_neg, abs_of_nonneg (by positivity)]
      exact h
    · refine ⟨-1, by simp, ?_⟩
      have hsub : (((L - u : ℕ) : ℝ)) = (L : ℝ) - (u : ℝ) := by
        exact Nat.cast_sub (Nat.le_of_lt huL)
      have htmp : (-(u : ℝ) - ((-1 : ℤ) : ℝ) * (L : ℝ)) = (L : ℝ) - (u : ℝ) := by
        norm_num
        ring
      rw [htmp]
      have hz : |(L : ℝ) - (u : ℝ)| = ((L - u : ℕ) : ℝ) := by
        rw [hsub]
        exact abs_of_nonneg (by linarith)
      simpa [hz] using h



/-- The main arc equivalence, assembled from the ℝ-window machinery. -/
private theorem window_residue_arc (g M N L : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N)
    (hL : L = g * M * N) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1 / 8)
    (a b : ℕ) (ha : a < g * M) (hb : b < g * N) :
    (∃ j : Fin 3,
        |(((a : ℤ) * ((g * N) : ℤ) - (b : ℤ) * ((g * M) : ℤ)) -
            ((((j.1 : ℕ) : ℤ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℤ)) : ℝ)| <
          s * ((((g * M) * (g * N)) : ℕ) : ℝ)) ↔
      (((((a * N + L - b * M) % L : ℕ) : ℝ) < s * (L : ℝ)) ∨
        (((L - (a * N + L - b * M) % L : ℕ) : ℝ) < s * (L : ℝ))) := by
  classical
  have hL0 : 0 < L := by
    rw [hL]
    positivity
  have hgR : 0 < (g : ℝ) := by exact_mod_cast hg
  have haN : a * N < L := mul_lt_L_of_lt_gM (g := g) hN hL ha
  have hbM : b * M < L := mul_lt_L_of_lt_gN (g := g) hM hL hb
  have hmnL : ((g * M) * (g * N) : ℕ) = g * L := by
    rw [hL]
    ring
  let mn : ℕ := (g * M) * (g * N)
  have hmnL' : mn = g * L := by dsimp [mn]; exact hmnL
  have hmnL'' : (mn : ℝ) = (g : ℝ) * (L : ℝ) := by
    rw [hmnL']
    norm_num
  have hLc : (L : ℝ) = (g : ℝ) * (M : ℝ) * (N : ℝ) := by
    rw [hL]
    norm_num
  -- Step 1: the ℤ-window value equals the ℝ-window value for every j.
  have hstep1 : (∃ j : Fin 3,
        |(((a : ℤ) * ((g * N) : ℤ) - (b : ℤ) * ((g * M) : ℤ)) -
            ((((j.1 : ℕ) : ℤ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℤ)) : ℝ)| <
          s * ((((g * M) * (g * N)) : ℕ) : ℝ)) ↔
      (∃ j : Fin 3,
        |((a : ℝ) * (((g * N) : ℕ) : ℝ) - (b : ℝ) * (((g * M) : ℕ) : ℝ)) -
          (((j.1 : ℝ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℝ))| <
          s * ((((g * M) * (g * N)) : ℕ) : ℝ)) := by
    constructor <;> rintro ⟨j, hj⟩ <;> refine ⟨j, ?_⟩
    · have hcong : |(((((a : ℤ) * (((g * N) : ℕ) : ℤ) - (b : ℤ) * (((g * M) : ℕ) : ℤ)) -
            ((((j.1 : ℕ) : ℤ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℤ))) : ℝ))| =
          |((a : ℝ) * (((g * N) : ℕ) : ℝ) - (b : ℝ) * (((g * M) : ℕ) : ℝ)) -
            (((j.1 : ℝ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℝ))| := by
          congr 1
      simpa [hcong] using hj
    · have hcong : |(((((a : ℤ) * (((g * N) : ℕ) : ℤ) - (b : ℤ) * (((g * M) : ℕ) : ℤ)) -
            ((((j.1 : ℕ) : ℤ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℤ))) : ℝ))| =
          |((a : ℝ) * (((g * N) : ℕ) : ℝ) - (b : ℝ) * (((g * M) : ℕ) : ℝ)) -
            (((j.1 : ℝ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℝ))| := by
          congr 1
      simpa [hcong] using hj
  -- Step 2: the ℝ-window (∃j) ↔ t-window at the value level (∃t ∈ Icc)
  have hstep2 : (∃ j : Fin 3,
        |((a : ℝ) * (((g * N) : ℕ) : ℝ) - (b : ℝ) * (((g * M) : ℕ) : ℝ)) -
          (((j.1 : ℝ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℝ))| <
          s * ((((g * M) * (g * N)) : ℕ) : ℝ)) ↔
      (∃ t ∈ (Finset.Icc (-1 : ℤ) 1 : Finset ℤ),
        |((g : ℝ) * (((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) - (t : ℝ) * (L : ℝ)))| <
          s * ((g : ℝ) * (L : ℝ))) := by
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨(((j.1 : ℕ) : ℤ) - 1), ?_, ?_⟩
      · fin_cases j <;> simp
      · -- value equality: WvalR(j) = (g:ℝ)·(Dℝ − (j.1−1)·(L:ℝ))
        have hc1 : ((a : ℝ) * (((g * N) : ℕ) : ℝ) - (b : ℝ) * (((g * M) : ℕ) : ℝ)) =
            (g : ℝ) * ((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) := by
          norm_num
          ring
        have hc2 : ((((g * M) * (g * N)) : ℕ) : ℝ) = (g : ℝ) * (L : ℝ) := hmnL''
        have hval : ((a : ℝ) * (((g * N) : ℕ) : ℝ) - (b : ℝ) * (((g * M) : ℕ) : ℝ)) -
            ((((j.1 : ℕ) : ℝ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℝ))
            = (g : ℝ) * (((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) -
                ((((j.1 : ℕ) : ℤ) - 1 : ℤ) : ℝ) * (L : ℝ)) := by
          rw [hc1, hc2]
          norm_num
          ring
        have hs : s * ((((g * M) * (g * N)) : ℕ) : ℝ) = s * ((g : ℝ) * (L : ℝ)) := by
          rw [hc2]
        rw [← hval, ← hs]
        exact hj
    · rintro ⟨t, ht, htP⟩
      rcases t_cases ht with ht1 | ht0 | ht1'
      · refine ⟨0, ?_⟩
        have hval : ((a : ℝ) * (((g * N) : ℕ) : ℝ) - (b : ℝ) * (((g * M) : ℕ) : ℝ)) -
            ((((0 : Fin 3).1 : ℝ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℝ)) =
            (g : ℝ) * (((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) - (-1 : ℝ) * (L : ℝ)) := by
          rw [hLc]
          norm_num
          ring
        have hc2 : ((((g * M) * (g * N)) : ℕ) : ℝ) = (g : ℝ) * (L : ℝ) := hmnL''
        have htP1 : |((g : ℝ) * (((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) - (-1 : ℝ) * (L : ℝ)))| <
            s * ((g : ℝ) * (L : ℝ)) := by
          simpa [ht1] using htP
        have hgoal : |((a : ℝ) * (((g * N) : ℕ) : ℝ) - (b : ℝ) * (((g * M) : ℕ) : ℝ)) -
            ((((0 : Fin 3).1 : ℝ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℝ))| <
            s * ((((g * M) * (g * N)) : ℕ) : ℝ) := by
          rw [hval, hc2]
          exact htP1
        exact hgoal
      · refine ⟨1, ?_⟩
        have hval : ((a : ℝ) * (((g * N) : ℕ) : ℝ) - (b : ℝ) * (((g * M) : ℕ) : ℝ)) -
            ((((1 : Fin 3).1 : ℝ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℝ)) =
            (g : ℝ) * (((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) - (0 : ℝ) * (L : ℝ)) := by
          rw [hLc]
          norm_num
          ring
        have hc2 : ((((g * M) * (g * N)) : ℕ) : ℝ) = (g : ℝ) * (L : ℝ) := hmnL''
        have htP1 : |((g : ℝ) * (((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) - (0 : ℝ) * (L : ℝ)))| <
            s * ((g : ℝ) * (L : ℝ)) := by
          simpa [ht0] using htP
        have hgoal : |((a : ℝ) * (((g * N) : ℕ) : ℝ) - (b : ℝ) * (((g * M) : ℕ) : ℝ)) -
            ((((1 : Fin 3).1 : ℝ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℝ))| <
            s * ((((g * M) * (g * N)) : ℕ) : ℝ) := by
          rw [hval, hc2]
          exact htP1
        exact hgoal
      · refine ⟨2, ?_⟩
        have hval : ((a : ℝ) * (((g * N) : ℕ) : ℝ) - (b : ℝ) * (((g * M) : ℕ) : ℝ)) -
            ((((2 : Fin 3).1 : ℝ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℝ)) =
            (g : ℝ) * (((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) - (1 : ℝ) * (L : ℝ)) := by
          rw [hLc]
          norm_num
          ring
        have hc2 : ((((g * M) * (g * N)) : ℕ) : ℝ) = (g : ℝ) * (L : ℝ) := hmnL''
        have htP1 : |((g : ℝ) * (((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) - (1 : ℝ) * (L : ℝ)))| <
            s * ((g : ℝ) * (L : ℝ)) := by
          simpa [ht1'] using htP
        have hgoal : |((a : ℝ) * (((g * N) : ℕ) : ℝ) - (b : ℝ) * (((g * M) : ℕ) : ℝ)) -
            ((((2 : Fin 3).1 : ℝ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℝ))| <
            s * ((((g * M) * (g * N)) : ℕ) : ℝ) := by
          rw [hval, hc2]
          exact htP1
        exact hgoal
  -- Step 3: remove the factor g and split into the two sign cases.
  have hstep3 : (∃ t ∈ (Finset.Icc (-1 : ℤ) 1 : Finset ℤ),
        |((g : ℝ) * (((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) - (t : ℝ) * (L : ℝ)))| <
          s * ((g : ℝ) * (L : ℝ))) ↔
      (∃ t ∈ (Finset.Icc (-1 : ℤ) 1 : Finset ℤ),
        |(((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) - (t : ℝ) * (L : ℝ))| <
          s * (L : ℝ)) := by
    constructor <;> rintro ⟨t, ht, htP⟩ <;> refine ⟨t, ht, ?_⟩
    · have habs : |((g : ℝ) * (((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) - (t : ℝ) * (L : ℝ)))| =
          (g : ℝ) * |(((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) - (t : ℝ) * (L : ℝ))| := by
          rw [abs_mul, abs_of_nonneg (le_of_lt hgR)]
      have hb : (g : ℝ) * |(((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) - (t : ℝ) * (L : ℝ))| <
          (g : ℝ) * (s * (L : ℝ)) := by
        rw [habs] at htP
        simpa [mul_assoc, mul_comm, mul_left_comm] using htP
      have htarget : |(((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) - (t : ℝ) * (L : ℝ))| < s * (L : ℝ) :=
        lt_of_mul_lt_mul_left hb (le_of_lt hgR)
      exact htarget
    · have hz : (g : ℝ) * |(((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) - (t : ℝ) * (L : ℝ))| <
          (g : ℝ) * (s * (L : ℝ)) :=
        mul_lt_mul_of_pos_left htP hgR
      have habs : |((g : ℝ) * (((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) - (t : ℝ) * (L : ℝ)))| =
          (g : ℝ) * |(((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) - (t : ℝ) * (L : ℝ))| := by
          rw [abs_mul, abs_of_nonneg (le_of_lt hgR)]
      have hgoal : |((g : ℝ) * (((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) - (t : ℝ) * (L : ℝ)))| <
          s * ((g : ℝ) * (L : ℝ)) := by
        rw [habs]
        simpa [mul_assoc, mul_comm, mul_left_comm] using hz
      exact hgoal
  -- Step 4: sign case split with the residue-equalities
  have hstep4 : (∃ t ∈ (Finset.Icc (-1 : ℤ) 1 : Finset ℤ),
        |(((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) - (t : ℝ) * (L : ℝ))| <
          s * (L : ℝ)) ↔
      (((((a * N + L - b * M) % L : ℕ) : ℝ) < s * (L : ℝ)) ∨
        (((L - (a * N + L - b * M) % L : ℕ) : ℝ) < s * (L : ℝ))) := by
    by_cases hle : b * M ≤ a * N
    · let u : ℕ := a * N - b * M
      have huL : u < L := lt_of_le_of_lt (Nat.sub_le (a * N) (b * M)) haN
      have hD : ((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) = (u : ℝ) := by
        exact Dℝ_pos hle
      have he : (a * N + L - b * M) % L = u := by
        exact eRes_pos_case (M := M) (N := N) hle (by omega)
      have hmain := window_pos_R L u huL (s * (L : ℝ))
      have hmid : (∃ t ∈ (Finset.Icc (-1 : ℤ) 1 : Finset ℤ),
          |(((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) - (t : ℝ) * (L : ℝ))| < s * (L : ℝ)) ↔
          (((u : ℝ) < s * (L : ℝ)) ∨ (((L - u : ℕ) : ℝ) < s * (L : ℝ))) := by
        rw [hD]
        exact hmain
      have hside : (((u : ℝ) < s * (L : ℝ)) ∨ (((L - u : ℕ) : ℝ) < s * (L : ℝ))) ↔
          (((((a * N + L - b * M) % L : ℕ) : ℝ) < s * (L : ℝ)) ∨
            (((L - (a * N + L - b * M) % L : ℕ) : ℝ) < s * (L : ℝ))) := by
        simpa [he]
      exact hmid.trans hside
    · let u : ℕ := b * M - a * N
      have huL : u < L := lt_of_le_of_lt (Nat.sub_le (b * M) (a * N)) hbM
      have hD : ((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) = -(u : ℝ) := by
        exact Dℝ_neg (by omega)
      have he : (a * N + L - b * M) % L = L - u := by
        exact eRes_neg_case (M := M) (N := N) (by omega) (by omega)
      have hmain := window_neg_R L u huL (s * (L : ℝ))
      have hmid : (∃ t ∈ (Finset.Icc (-1 : ℤ) 1 : Finset ℤ),
          |(((a : ℝ) * (N : ℝ) - (b : ℝ) * (M : ℝ)) - (t : ℝ) * (L : ℝ))| < s * (L : ℝ)) ↔
          (((u : ℝ) < s * (L : ℝ)) ∨ (((L - u : ℕ) : ℝ) < s * (L : ℝ))) := by
        rw [hD]
        exact hmain
      have hside : (((u : ℝ) < s * (L : ℝ)) ∨ (((L - u : ℕ) : ℝ) < s * (L : ℝ))) ↔
          (((((a * N + L - b * M) % L : ℕ) : ℝ) < s * (L : ℝ)) ∨
            (((L - (a * N + L - b * M) % L : ℕ) : ℝ) < s * (L : ℝ))) := by
        have hcancel : L - (L - u) = u := by omega
        have hres1 : ((((a * N + L - b * M) % L : ℕ) : ℝ)) = (((L - u : ℕ) : ℝ)) := by
          rw [he]
        have hres2 : (((L - ((a * N + L - b * M) % L : ℕ)) : ℕ) : ℝ) = (u : ℝ) := by
          rw [he, hcancel]
        simpa [hres1, hres2, or_comm]
      exact hmid.trans hside
  exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))



/-! ## Section 3 — splitting the windowed count into the two residue arcs -/

/-- The window condition is exactly one of the two residue conditions (`P1`,`P2`);
the two residue conditions are mutually exclusive (since `2W < L`). -/
private lemma window_card_split (g M N L : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N)
    (hL : L = g * M * N) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1 / 8) :
    let W : ℝ := s * (L : ℝ)
    let S : Finset (ℕ × ℕ) :=
      Finset.product ((Finset.range (g * M)).filter (fun a : ℕ => a.gcd (g * M) = 1))
        ((Finset.range (g * N)).filter (fun b : ℕ => b.gcd (g * N) = 1))
    let P1 : ℕ × ℕ → Prop :=
      fun ab => ((((ab.1 * N + L - ab.2 * M) % L : ℕ) : ℝ) < W)
    let P2 : ℕ × ℕ → Prop :=
      fun ab => (((L - ((ab.1 * N + L - ab.2 * M) % L : ℕ)) : ℕ) : ℝ) < W
    ((S.filter (fun ab : ℕ × ℕ => ∃ j : Fin 3,
        |(((ab.1 : ℤ) * ((g * N) : ℤ) - (ab.2 : ℤ) * ((g * M) : ℤ)) -
            ((((j.1 : ℕ) : ℤ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℤ)) : ℝ)| <
          s * ((((g * M) * (g * N)) : ℕ) : ℝ))).card) =
      (S.filter P1).card + (S.filter P2).card := by
  classical
  let W : ℝ := s * (L : ℝ)
  let S : Finset (ℕ × ℕ) :=
      Finset.product ((Finset.range (g * M)).filter (fun a : ℕ => a.gcd (g * M) = 1))
        ((Finset.range (g * N)).filter (fun b : ℕ => b.gcd (g * N) = 1))
  let P1 : ℕ × ℕ → Prop :=
      fun ab => ((((ab.1 * N + L - ab.2 * M) % L : ℕ) : ℝ) < W)
  let P2 : ℕ × ℕ → Prop :=
      fun ab => (((L - ((ab.1 * N + L - ab.2 * M) % L : ℕ)) : ℕ) : ℝ) < W
  have hL0 : 0 < L := by rw [hL]; positivity
  have hW2 : W < (L : ℝ) / 2 := by
    have hLc : 0 < (L : ℝ) := by exact_mod_cast hL0
    have hs : s * (L : ℝ) < (1 / 8 : ℝ) * (L : ℝ) := mul_lt_mul_of_pos_right hs1 hLc
    dsimp [W]
    linarith
  have hres0 : ∀ x ∈ S, ((x.1 * N + L - x.2 * M) % L : ℕ) < L := by
    intro x hx
    exact Nat.mod_lt _ hL0
  have hiff : ∀ ab, ab ∈ S →
      ((∃ j : Fin 3,
        |(((ab.1 : ℤ) * ((g * N) : ℤ) - (ab.2 : ℤ) * ((g * M) : ℤ)) -
            ((((j.1 : ℕ) : ℤ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℤ)) : ℝ)| <
          s * ((((g * M) * (g * N)) : ℕ) : ℝ)) ↔ (P1 ab ∨ P2 ab)) := by
    intro ab hab
    have habp : ab ∈ S := hab
    have habp : ab ∈ S := hab
    dsimp [S] at habp
    have haS := (Finset.mem_product.mp habp).1
    have hbS := (Finset.mem_product.mp habp).2
    have ha : ab.1 < g * M := Finset.mem_range.mp (Finset.mem_filter.mp haS).1
    have hb : ab.2 < g * N := Finset.mem_range.mp (Finset.mem_filter.mp hbS).1
    have hb : ab.2 < g * N := Finset.mem_range.mp (Finset.mem_filter.mp hbS).1
    exact window_residue_arc g M N L hg hM hN hL s hs0 hs1 ab.1 ab.2 ha hb
  have hdisj : ∀ ab ∈ S, ¬ (P1 ab ∧ P2 ab) := by
    intro ab hab h
    have heL : (((ab.1 * N + L - ab.2 * M) % L : ℕ) : ℝ) < (L : ℝ) := by
      exact_mod_cast (Nat.mod_lt _ hL0)
    have h1 : (((ab.1 * N + L - ab.2 * M) % L : ℕ) : ℝ) < W := h.1
    have h2 : (((L - ((ab.1 * N + L - ab.2 * M) % L : ℕ)) : ℕ) : ℝ) < W := h.2
    have hleN : ((ab.1 * N + L - ab.2 * M) % L : ℕ) ≤ L := Nat.le_of_lt (Nat.mod_lt _ hL0)
    have hsub : (((L - ((ab.1 * N + L - ab.2 * M) % L : ℕ)) : ℕ) : ℝ) =
        (L : ℝ) - (((ab.1 * N + L - ab.2 * M) % L : ℕ) : ℝ) := by
      exact Nat.cast_sub hleN
    have hsum : (L : ℝ) < 2 * W := by
      rw [hsub] at h2
      linarith
    have hbig : (L : ℝ) / 2 < W := by linarith
    linarith
  have hset : S.filter (fun ab : ℕ × ℕ => ∃ j : Fin 3,
        |(((ab.1 : ℤ) * ((g * N) : ℤ) - (ab.2 : ℤ) * ((g * M) : ℤ)) -
            ((((j.1 : ℕ) : ℤ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℤ)) : ℝ)| <
          s * ((((g * M) * (g * N)) : ℕ) : ℝ)) =
      S.filter (fun ab => P1 ab ∨ P2 ab) := by
    ext ab
    constructor
    · intro hab
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hab).1, (hiff ab (Finset.mem_filter.mp hab).1).mp (Finset.mem_filter.mp hab).2⟩
    · intro hab
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hab).1, (hiff ab (Finset.mem_filter.mp hab).1).mpr (Finset.mem_filter.mp hab).2⟩
  have hdisj' : Disjoint (S.filter P1) (S.filter P2) := by
    rw [Finset.disjoint_left]
    intro ab hab h2mem
    rcases Finset.mem_filter.mp hab with ⟨hmem1, hP1⟩
    rcases Finset.mem_filter.mp h2mem with ⟨hmem2, hP2⟩
    exact hdisj ab hmem1 ⟨hP1, hP2⟩
  calc
    ((S.filter (fun ab : ℕ × ℕ => ∃ j : Fin 3,
        |(((ab.1 : ℤ) * ((g * N) : ℤ) - (ab.2 : ℤ) * ((g * M) : ℤ)) -
            ((((j.1 : ℕ) : ℤ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℤ)) : ℝ)| <
          s * ((((g * M) * (g * N)) : ℕ) : ℝ))).card)
        = (S.filter (fun ab : ℕ × ℕ => P1 ab ∨ P2 ab)).card := by rw [hset]
    _ = (S.filter P1).card + (S.filter P2).card := by
        rw [← Finset.card_union_of_disjoint hdisj']
        congr 1
        rw [Finset.filter_or]


/-! ## Section 4 — fiberwise sums, residue symmetry, range reindexing -/

/-- For a finset `S` and `f : α → ℕ` with values `< L`, the cardinality of
`S.filter (P ∘ f)` equals the sum over residues `e < L` of `C e · [P e]`. -/
private lemma card_filter_eq_sum_fiber (L : ℕ) (S : Finset (ℕ × ℕ))
    (f : ℕ × ℕ → ℕ) (hf : ∀ x ∈ S, f x < L) (P : ℕ → Prop) [DecidablePred P] :
    (S.filter (fun x => P (f x))).card =
      ∑ e ∈ Finset.range L, (S.filter (fun x => f x = e)).card * if P e then 1 else 0 := by
  classical
  have hdelta : ∀ x ∈ S, (∑ e ∈ Finset.range L, if e = f x then (if P e then 1 else 0) else 0) =
      if P (f x) then 1 else 0 := by
    intro x hx
    have hmem : f x ∈ Finset.range L := Finset.mem_range.mpr (hf x hx)
    have hs := Finset.sum_ite_eq (Finset.range L) (f x) (fun e => if P e then 1 else 0)
    -- hs : (∑ e ∈ range L, if f x = e then (if P e then 1 else 0) else 0) =
    --      if f x ∈ range L then (if P (f x) then 1 else 0) else 0
    simpa [hmem] using hs
  calc
    (S.filter (fun x => P (f x))).card
        = ∑ x ∈ S, if P (f x) then 1 else 0 := by
            rw [Finset.card_filter]
    _ = ∑ x ∈ S, ∑ e ∈ Finset.range L, if e = f x then (if P e then 1 else 0) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            exact (hdelta x hx).symm
    _ = ∑ e ∈ Finset.range L, ∑ x ∈ S, if f x = e then (if P e then 1 else 0) else 0 := by
            rw [Finset.sum_comm]
            simp [eq_comm]
    _ = ∑ e ∈ Finset.range L, (S.filter (fun x => f x = e)).card * if P e then 1 else 0 := by
            refine Finset.sum_congr rfl ?_
            intro e he
            have hinner1 : (∑ x ∈ S, if f x = e then (if P e then 1 else 0) else 0) =
                (if P e then 1 else 0) * (∑ x ∈ S, if f x = e then (1 : ℕ) else 0) := by
              calc
                (∑ x ∈ S, if f x = e then (if P e then 1 else 0) else 0)
                    = ∑ x ∈ S, (if P e then 1 else 0) * (if f x = e then 1 else 0) := by
                        refine Finset.sum_congr rfl ?_
                        intro x hx
                        by_cases h : f x = e <;> simp [h]
                _ = (if P e then 1 else 0) * (∑ x ∈ S, if f x = e then 1 else 0) := by
                        rw [Finset.mul_sum]
            have hinner2 : (∑ x ∈ S, if f x = e then (1 : ℕ) else 0) =
                (S.filter (fun x => f x = e)).card := by
              rw [Finset.sum_boole]
              simp
            calc
              (∑ x ∈ S, if f x = e then (if P e then 1 else 0) else 0)
                  = (if P e then 1 else 0) * (∑ x ∈ S, if f x = e then (1 : ℕ) else 0) := hinner1
              _ = (if P e then 1 else 0) * (S.filter (fun x => f x = e)).card := by rw [hinner2]
              _ = (S.filter (fun x => f x = e)).card * if P e then 1 else 0 := by rw [mul_comm]


/-! ## Section 5 — reflection symmetry of the fibres -/

/-- reflection `(a,b) ↦ ((gM−a)%gM, (gN−b)%gN)` on reduced pairs -/
private def reflect (g M N : ℕ) (ab : ℕ × ℕ) : ℕ × ℕ :=
  ((g * M - ab.1) % (g * M), (g * N - ab.2) % (g * N))

/-- gcd is invariant under `x ↦ (m−x) % m` for `x < m` coprime to `m`. -/
private lemma gcd_reflect (g M a : ℕ) (hg : 0 < g) (hM : 0 < M) (ha : a < g * M)
    (hcop : a.gcd (g * M) = 1) :
    (((g * M - a) % (g * M)).gcd (g * M)) = 1 := by
  have hgm0 : 0 < g * M := by positivity
  by_cases ha0 : a = 0
  · subst a
    have hgM : g * M = 1 := by simpa using hcop
    rw [hgM]
    simp
  · have ha1 : 1 ≤ a := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero ha0)
    have hlt : g * M - a < g * M := Nat.sub_lt hgm0 ha1
    rw [Nat.mod_eq_of_lt hlt]
    rw [Nat.gcd_self_sub_left (m := g * M) (n := a) (Nat.le_of_lt ha)]
    exact hcop

/-- membership in `U m` -/
private lemma mem_U {m : ℕ} {x : ℕ} : x ∈ U m ↔ x < m ∧ x.gcd m = 1 := by
  simp [U]

/-- the reflection of a reduced pair is a reduced pair -/
private lemma reflect_mem (g M N : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N)
    {ab : ℕ × ℕ} (hab : ab ∈ U (g * M) ×ˢ U (g * N)) :
    reflect g M N ab ∈ U (g * M) ×ˢ U (g * N) := by
  have ha1 : ab.1 < g * M := (mem_U.mp (Finset.mem_product.mp hab).1).1
  have hac : ab.1.gcd (g * M) = 1 := (mem_U.mp (Finset.mem_product.mp hab).1).2
  have hb1 : ab.2 < g * N := (mem_U.mp (Finset.mem_product.mp hab).2).1
  have hbc : ab.2.gcd (g * N) = 1 := (mem_U.mp (Finset.mem_product.mp hab).2).2
  rw [Finset.mem_product]
  rw [mem_U, mem_U]
  constructor
  · constructor
    · change ((g * M - ab.1) % (g * M)) < g * M
      exact Nat.mod_lt _ (by positivity : 0 < g * M)
    · change ((g * M - ab.1) % (g * M)).gcd (g * M) = 1
      exact gcd_reflect g M ab.1 hg hM ha1 hac
  · constructor
    · change ((g * N - ab.2) % (g * N)) < g * N
      exact Nat.mod_lt _ (by positivity : 0 < g * N)
    · change ((g * N - ab.2) % (g * N)).gcd (g * N) = 1
      exact gcd_reflect g N ab.2 hg hN hb1 hbc

/-- reflection is involutive on the reduced pairs -/
private lemma reflect_involutive (g M N : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N)
    {ab : ℕ × ℕ} (hab : ab ∈ U (g * M) ×ˢ U (g * N)) :
    reflect g M N (reflect g M N ab) = ab := by
  rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
  have ha2 : ab.1 < g * M := (mem_U.mp ha).1
  have hb2 : ab.2 < g * N := (mem_U.mp hb).1
  have hgm0 : 0 < g * M := by positivity
  have hgn0 : 0 < g * N := by positivity
  have ha_inv : ((g * M - ((g * M - ab.1) % (g * M))) % (g * M)) = ab.1 := by
    by_cases ha0 : ab.1 = 0
    · simp [ha0]
    · have ha1 : 1 ≤ ab.1 := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero ha0)
      have hlt : g * M - ab.1 < g * M := Nat.sub_lt hgm0 ha1
      rw [Nat.mod_eq_of_lt hlt]
      calc
        (g * M - (g * M - ab.1)) % (g * M) = ab.1 % (g * M) := by
          rw [Nat.sub_sub_self (Nat.le_of_lt ha2)]
        _ = ab.1 := Nat.mod_eq_of_lt ha2
  have hb_inv : ((g * N - ((g * N - ab.2) % (g * N))) % (g * N)) = ab.2 := by
    by_cases hb0 : ab.2 = 0
    · simp [hb0]
    · have hb1 : 1 ≤ ab.2 := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hb0)
      have hlt : g * N - ab.2 < g * N := Nat.sub_lt hgn0 hb1
      rw [Nat.mod_eq_of_lt hlt]
      calc
        (g * N - (g * N - ab.2)) % (g * N) = ab.2 % (g * N) := by
          rw [Nat.sub_sub_self (Nat.le_of_lt hb2)]
        _ = ab.2 := Nat.mod_eq_of_lt hb2
  ext <;> simp [reflect, ha_inv, hb_inv]


/-- `eRes` when the residue is non-negative: `y·M ≤ x·N`. -/
private lemma eRes_of_pos (M N L x y : ℕ) (hle : y * M ≤ x * N) (hlt : x * N - y * M < L) :
    eRes M N L (x, y) = x * N - y * M := by
  simpa [eRes] using (eRes_pos_case (M := M) (N := N) (L := L) (a := x) (b := y) hle hlt)

/-- `eRes` when the residue is negative: `x·N < y·M`. -/
private lemma eRes_of_neg (M N L x y : ℕ) (hlt : x * N < y * M) (hlt2 : y * M - x * N < L) :
    eRes M N L (x, y) = L - (y * M - x * N) := by
  simpa [eRes] using (eRes_neg_case (M := M) (N := N) (L := L) (a := x) (b := y) hlt hlt2)

/-- reflection residue identity when both `a,b ≥ 1` -/
private lemma reflect_residue_both (g M N L : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N)
    (hL : L = g * M * N) {a b : ℕ} (ha1 : 1 ≤ a) (hb1 : 1 ≤ b)
    (ha : a < g * M) (hb : b < g * N) :
    eRes M N L (g * M - a, g * N - b) = (L - eRes M N L (a, b)) % L := by
  have hL0 : 0 < L := by rw [hL]; positivity
  have haN : a * N < L := mul_lt_L_of_lt_gM (g := g) hN hL ha
  have hbM : b * M < L := mul_lt_L_of_lt_gN (g := g) hM hL hb
  set u : ℕ := a * N
  set v : ℕ := b * M
  have hu : u < L := by dsimp [u]; exact haN
  have hv : v < L := by dsimp [v]; exact hbM
  have huaN : (g * M - a) * N = L - u := by
    dsimp [u]
    rw [Nat.mul_sub_right_distrib]
    rw [hL]
  have hvbM : (g * N - b) * M = L - v := by
    dsimp [v]
    rw [Nat.mul_sub_right_distrib]
    rw [hL]
    ring
  by_cases hle : v ≤ u
  · -- `v ≤ u`: eRes(a,b) = u−v; eRes(refl) = (L−(u−v))%L
    have he1 : eRes M N L (a, b) = u - v := by
      dsimp [u, v]
      apply eRes_of_pos (M := M) (N := N) (L := L) (x := a) (y := b)
      · exact hle
      · have h1 : a * N - b * M < L := lt_of_le_of_lt (Nat.sub_le (a * N) (b * M)) haN
        exact h1
    have he2 : eRes M N L (g * M - a, g * N - b) = (L - (u - v)) % L := by
      by_cases hu0 : u - v = 0
      · -- u = v
        have huv : u = v := by omega
        -- reflected: (gM−a)N = L−u = L−v = (gN−b)M, pos-case gives 0
        have hle2 : (g * N - b) * M ≤ (g * M - a) * N := by
          rw [huaN, hvbM]
          omega
        have hlt2 : (g * M - a) * N - (g * N - b) * M < L := by
          rw [huaN, hvbM]
          omega
        have he2' : eRes M N L (g * M - a, g * N - b) = 0 := by
          rw [eRes_of_pos (M := M) (N := N) (L := L) (x := g * M - a) (y := g * N - b) hle2 hlt2]
          rw [huaN, hvbM]
          omega
        rw [he2']
        rw [hu0]
        simp
      · -- u > v: reflected residue = L − (u−v)
        have hgt : v < u := by omega
        have hle2 : (g * M - a) * N < (g * N - b) * M := by
          rw [huaN, hvbM]
          omega
        have hlt2 : (g * N - b) * M - (g * M - a) * N < L := by
          rw [huaN, hvbM]
          omega
        have he2' : eRes M N L (g * M - a, g * N - b) = L - ((g * N - b) * M - (g * M - a) * N) := by
          exact eRes_of_neg (M := M) (N := N) (L := L) (x := g * M - a) (y := g * N - b) hle2 hlt2
        rw [he2']
        have hd : (g * N - b) * M - (g * M - a) * N = u - v := by
          rw [huaN, hvbM]
          omega
        rw [hd]
        -- (L − (u−v)) % L with u−v ∈ [1,L−1] = L−(u−v)
        have h01 : 0 < u - v := by omega
        rw [Nat.mod_eq_of_lt (Nat.sub_lt hL0 h01)]
    -- RHS (L − eRes(a,b)) % L = (L − (u−v)) % L; LHS he2:
    rw [he1]
    exact he2
  · -- `u < v`: eRes(a,b) = L − (v−u); reflected = v−u
    have hlt : u < v := by omega
    have he1 : eRes M N L (a, b) = L - (v - u) := by
      dsimp [u, v]
      apply eRes_of_neg (M := M) (N := N) (L := L) (x := a) (y := b)
      · exact hlt
      · have h1 : b * M - a * N < L := lt_of_le_of_lt (Nat.sub_le (b * M) (a * N)) hbM
        exact h1
    have he2 : eRes M N L (g * M - a, g * N - b) = (v - u) % L := by
      -- reflected residue is positive: (gN−b)M < (gM−a)N
      have hle2 : (g * N - b) * M ≤ (g * M - a) * N := by
        rw [huaN, hvbM]
        omega
      have hlt2 : (g * M - a) * N - (g * N - b) * M < L := by
        rw [huaN, hvbM]
        omega
      have he2' : eRes M N L (g * M - a, g * N - b) = (g * M - a) * N - (g * N - b) * M := by
        exact eRes_of_pos (M := M) (N := N) (L := L) (x := g * M - a) (y := g * N - b) hle2 hlt2
      rw [he2']
      have hd : (g * M - a) * N - (g * N - b) * M = v - u := by
        rw [huaN, hvbM]
        omega
      rw [hd]
      rw [Nat.mod_eq_of_lt (by omega : v - u < L)]
    rw [he1]
    -- (L − (L − (v−u))) % L = (v−u) % L
    have hsub : L - (L - (v - u)) = v - u := by omega
    rw [hsub]
    exact he2

/-- reflection residue identity when `a = 0` -/
private lemma reflect_residue_left0 (g M N L : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N)
    (hL : L = g * M * N) {b : ℕ} (hb : b < g * N) :
    eRes M N L (0, (g * N - b) % (g * N)) = (L - eRes M N L (0, b)) % L := by
  have hL0 : 0 < L := by rw [hL]; positivity
  have hgn0 : 0 < g * N := by positivity
  by_cases hb0 : b = 0
  · subst b
    simp [eRes]
  · have hb1 : 1 ≤ b := by omega
    have hb'v : (g * N - b) % (g * N) = g * N - b :=
      Nat.mod_eq_of_lt (Nat.sub_lt hgn0 hb1)
    rw [hb'v]
    have hbM : b * M < L := mul_lt_L_of_lt_gN (g := g) hM hL hb
    have hbM0 : 0 < b * M := Nat.mul_pos (by omega : 0 < b) hM
    have hb'lt : g * N - b < g * N := Nat.sub_lt hgn0 hb1
    have hb'ML : (g * N - b) * M < L := mul_lt_L_of_lt_gN (g := g) hM hL hb'lt
    have hE1 : eRes M N L (0, b) = L - b * M := by
      have hg1 := eRes_of_neg (M := M) (N := N) (L := L) (x := 0) (y := b)
        (by simpa using hbM0) (by simpa using hbM)
      simpa using hg1
    have hE2 : eRes M N L (0, g * N - b) = L - (g * N - b) * M := by
      have hg2 := eRes_of_neg (M := M) (N := N) (L := L) (x := 0) (y := g * N - b)
        (by simpa using (Nat.mul_pos (by omega : 0 < g * N - b) hM)) (by simpa using hb'ML)
      simpa using hg2
    have hred : (g * N - b) * M = L - b * M := by
      rw [Nat.mul_sub_right_distrib]
      rw [hL]
      ring
    have hLHS : eRes M N L (0, g * N - b) = b * M := by
      rw [hE2, hred]
      rw [Nat.sub_sub_self (Nat.le_of_lt hbM)]
    rw [hE1]
    have hR : (L - (L - b * M)) % L = b * M := by
      rw [Nat.sub_sub_self (Nat.le_of_lt hbM)]
      exact Nat.mod_eq_of_lt hbM
    rw [hLHS, hR]

/-- reflection residue identity when `b = 0` -/
private lemma reflect_residue_right0 (g M N L : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N)
    (hL : L = g * M * N) {a : ℕ} (ha : a < g * M) :
    eRes M N L ((g * M - a) % (g * M), 0) = (L - eRes M N L (a, 0)) % L := by
  have hL0 : 0 < L := by rw [hL]; positivity
  have hgm0 : 0 < g * M := by positivity
  by_cases ha0 : a = 0
  · subst a
    simp [eRes]
  · have ha1 : 1 ≤ a := by omega
    have ha'v : (g * M - a) % (g * M) = g * M - a :=
      Nat.mod_eq_of_lt (Nat.sub_lt hgm0 ha1)
    rw [ha'v]
    have haN : a * N < L := mul_lt_L_of_lt_gM (g := g) hN hL ha
    have haN0 : 0 < a * N := Nat.mul_pos (by omega : 0 < a) hN
    have ha'lt : g * M - a < g * M := Nat.sub_lt hgm0 ha1
    have ha'NL : (g * M - a) * N < L := mul_lt_L_of_lt_gM (g := g) hN hL ha'lt
    have hE1 : eRes M N L (a, 0) = a * N := by
      have hg3 := eRes_of_pos (M := M) (N := N) (L := L) (x := a) (y := 0)
        (by simp) (by simpa using haN)
      simpa using hg3
    have hE2 : eRes M N L (g * M - a, 0) = (g * M - a) * N := by
      have hg4 := eRes_of_pos (M := M) (N := N) (L := L) (x := g * M - a) (y := 0)
        (by simp) (by simpa using ha'NL)
      simpa using hg4
    have hred : (g * M - a) * N = L - a * N := by
      rw [Nat.mul_sub_right_distrib]
      rw [hL]
    have hLHS : eRes M N L (g * M - a, 0) = L - a * N := by
      rw [hE2, hred]
    rw [hE1]
    have hR : (L - a * N) % L = L - a * N := by
      apply Nat.mod_eq_of_lt
      omega
    rw [hLHS, hR]

/-- reflection sends residue `e` to the residue `(L − e) % L`. -/
private lemma reflect_residue (g M N L : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N)
    (hL : L = g * M * N) {a b : ℕ} (ha : a < g * M) (hb : b < g * N) :
    eRes M N L (((g * M - a) % (g * M)), ((g * N - b) % (g * N))) =
      (L - eRes M N L (a, b)) % L := by
  by_cases ha0 : a = 0
  · subst a
    have hc : (g * M - 0) % (g * M) = 0 := by simp
    rw [hc]
    exact (reflect_residue_left0 (g := g) (M := M) (N := N) (L := L) hg hM hN hL hb)
  · by_cases hb0 : b = 0
    · subst b
      have hc : (g * N - 0) % (g * N) = 0 := by simp
      rw [hc]
      exact (reflect_residue_right0 (g := g) (M := M) (N := N) (L := L) hg hM hN hL ha)
    · have ha1 : 1 ≤ a := by omega
      have hb1 : 1 ≤ b := by omega
      have hgm0 : 0 < g * M := by positivity
      have hgn0 : 0 < g * N := by positivity
      have ha'v : (g * M - a) % (g * M) = g * M - a :=
        Nat.mod_eq_of_lt (Nat.sub_lt hgm0 ha1)
      have hb'v : (g * N - b) % (g * N) = g * N - b :=
        Nat.mod_eq_of_lt (Nat.sub_lt hgn0 hb1)
      rw [ha'v, hb'v]
      exact reflect_residue_both g M N L hg hM hN hL ha1 hb1 ha hb


/-- no reduced pair has residue zero when `M ≠ N` (and `M ⊥ N`); this is the
injectivity/positivity fact that makes the two residue arcs mirror each other. -/
private lemma no_zero_residue (g M N L : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N)
    (hc : M.Coprime N) (hL : L = g * M * N) (hMN : M ≠ N)
    {a b : ℕ} (ha : a < g * M) (hb : b < g * N)
    (hca : a.gcd (g * M) = 1) (hcb : b.gcd (g * N) = 1) :
    eRes M N L (a, b) ≠ 0 := by
  intro hz
  have haN : a * N < L := mul_lt_L_of_lt_gM (g := g) hN hL ha
  have hbM : b * M < L := mul_lt_L_of_lt_gN (g := g) hM hL hb
  set u : ℕ := a * N with hu
  set v : ℕ := b * M with hv
  by_cases hle : v ≤ u
  · -- `u = v`: aN = bM, then `M | a`, `N | b`, forcing `M = N = 1`
    have hle' : b * M ≤ a * N := by simpa [hv, hu] using hle
    have hpos : eRes M N L (a, b) = u - v := by
      calc
        eRes M N L (a, b) = a * N - b * M :=
          eRes_of_pos (M := M) (N := N) (L := L) (x := a) (y := b) hle'
            (lt_of_le_of_lt (Nat.sub_le (a * N) (b * M)) haN)
        _ = u - v := by rw [hu, hv]
    have hz' : u - v = 0 := by
      rw [hpos] at hz
      exact hz
    have huv : u = v := by omega
    have huveq : a * N = b * M := by
      simpa [hu, hv] using huv
    have huveqM : a * N = M * b := by simpa [Nat.mul_comm] using huveq
    have huveqN : M * b = N * a := by
      rw [Nat.mul_comm N a, ← Nat.mul_comm b M]
      exact huveq.symm
    have hMdiv : M ∣ a := by
      apply hc.dvd_of_dvd_mul_left
      · refine ⟨b, ?_⟩
        rw [Nat.mul_comm]
        exact huveqM
    have hNdiv : N ∣ b := by
      apply hc.symm.dvd_of_dvd_mul_left
      · refine ⟨a, ?_⟩
        exact huveqN
    have hMone : M = 1 := by
      have hMg : M ∣ g * M := ⟨g, by rw [Nat.mul_comm]⟩
      have h1 : M ∣ a.gcd (g * M) := Nat.dvd_gcd hMdiv hMg
      have hM1 : M ∣ 1 := by simpa [hca] using h1
      exact Nat.dvd_one.mp hM1
    have hNone : N = 1 := by
      have hNg : N ∣ g * N := ⟨g, by rw [Nat.mul_comm]⟩
      have h2 : N ∣ b.gcd (g * N) := Nat.dvd_gcd hNdiv hNg
      have hN1 : N ∣ 1 := by simpa [hcb] using h2
      exact Nat.dvd_one.mp hN1
    exact hMN (by rw [hMone, hNone])
  · -- `u < v`: residue would be `L − (v−u) ≠ 0`
    have hlt : u < v := by omega
    have hlt' : a * N < b * M := by simpa [hu, hv] using hlt
    have hpos : eRes M N L (a, b) = L - (v - u) := by
      calc
        eRes M N L (a, b) = L - (b * M - a * N) :=
          eRes_of_neg (M := M) (N := N) (L := L) (x := a) (y := b) hlt'
            (lt_of_le_of_lt (Nat.sub_le (b * M) (a * N)) hbM)
        _ = L - (v - u) := by rw [hu, hv]
    rw [hpos] at hz
    have hvu : v - u < L := by omega
    omega

/-- membership version of `no_zero_residue` -/
private lemma residue_pos_mem (g M N L : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N)
    (hc : M.Coprime N) (hL : L = g * M * N) (hMN : M ≠ N)
    {ab : ℕ × ℕ} (hab : ab ∈ U (g * M) ×ˢ U (g * N)) : eRes M N L ab ≠ 0 := by
  have ha1 : ab.1 < g * M := (mem_U.mp (Finset.mem_product.mp hab).1).1
  have hca : ab.1.gcd (g * M) = 1 := (mem_U.mp (Finset.mem_product.mp hab).1).2
  have hb1 : ab.2 < g * N := (mem_U.mp (Finset.mem_product.mp hab).2).1
  have hcb : ab.2.gcd (g * N) = 1 := (mem_U.mp (Finset.mem_product.mp hab).2).2
  have h := no_zero_residue g M N L hg hM hN hc hL hMN ha1 hb1 hca hcb
  simpa using h


/-- no reduced pair lies in the `e = 0` fibre when `M ≠ N` -/
private lemma fibre_zero_eq_zero (g M N L : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N)
    (hc : M.Coprime N) (hL : L = g * M * N) (hMN : M ≠ N) :
    ((U (g * M) ×ˢ U (g * N)).filter (fun ab => eRes M N L ab = 0)).card = 0 := by
  have hfilter : (U (g * M) ×ˢ U (g * N)).filter (fun ab => eRes M N L ab = 0) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro ab hab hz
    exact residue_pos_mem g M N L hg hM hN hc hL hMN hab hz
  simp [hfilter]

/-- the reflection sends a residue `u ≥ 1` to `L − u` -/
private lemma reflect_residue_of_pos (g M N L : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N)
    (hL : L = g * M * N) {ab : ℕ × ℕ} (hab : ab ∈ U (g * M) ×ˢ U (g * N))
    (hu0 : eRes M N L ab ≠ 0) :
    eRes M N L (reflect g M N ab) = L - eRes M N L ab := by
  have hL0 : 0 < L := by rw [hL]; positivity
  have ha1 : ab.1 < g * M := (mem_U.mp (Finset.mem_product.mp hab).1).1
  have hb1 : ab.2 < g * N := (mem_U.mp (Finset.mem_product.mp hab).2).1
  have hmain := reflect_residue g M N L hg hM hN hL ha1 hb1
  have huL : eRes M N L ab < L := by
    change (ab.1 * N + L - ab.2 * M) % L < L
    exact Nat.mod_lt _ hL0
  have hge : 1 ≤ eRes M N L ab := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hu0)
  have hmod : (L - eRes M N L ab) % L = L - eRes M N L ab :=
    Nat.mod_eq_of_lt (Nat.sub_lt hL0 hge)
  -- hmain: eRes M N L ((gM-ab.1)%gM, (gN-ab.2)%gN) = (L − eRes M N L (ab.1, ab.2)) % L
  simpa [reflect, huL, hmod] using hmain

/-- `P2 x ↔ P1 (reflect x)` for reduced pairs: residue `u ≥ 1` reflects to `L − u`. -/
private lemma arcP2_iff_P1_reflect (g M N L : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N)
    (hc : M.Coprime N) (hL : L = g * M * N) (hMN : M ≠ N)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1 / 8)
    {x : ℕ × ℕ} (hx : x ∈ U (g * M) ×ˢ U (g * N)) :
    let W : ℝ := s * (L : ℝ)
    (((L - eRes M N L x : ℕ) : ℝ) < W) ↔ (((eRes M N L (reflect g M N x) : ℕ) : ℝ) < W) := by
  classical
  let W : ℝ := s * (L : ℝ)
  have hxres : eRes M N L x ≠ 0 := residue_pos_mem g M N L hg hM hN hc hL hMN hx
  have heq : eRes M N L (reflect g M N x) = L - eRes M N L x :=
    reflect_residue_of_pos g M N L hg hM hN hL hx hxres
  simp [heq]

/-- the two residue arcs contain the same number of pairs -/
private theorem arc_card_eq (g M N L : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N)
    (hc : M.Coprime N) (hL : L = g * M * N) (hMN : M ≠ N)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1 / 8) :
    let W : ℝ := s * (L : ℝ)
    let S : Finset (ℕ × ℕ) := U (g * M) ×ˢ U (g * N)
    let P1 : ℕ × ℕ → Prop := fun ab => (((eRes M N L ab : ℕ) : ℝ) < W)
    let P2 : ℕ × ℕ → Prop := fun ab => (((L - eRes M N L ab : ℕ) : ℝ) < W)
    (S.filter P2).card = (S.filter P1).card := by
  classical
  let W : ℝ := s * (L : ℝ)
  let S : Finset (ℕ × ℕ) := U (g * M) ×ˢ U (g * N)
  let P1 : ℕ × ℕ → Prop := fun ab => (((eRes M N L ab : ℕ) : ℝ) < W)
  let P2 : ℕ × ℕ → Prop := fun ab => (((L - eRes M N L ab : ℕ) : ℝ) < W)
  -- σ maps S into S and is its own inverse
  have hσmap : ∀ ab ∈ S, reflect g M N ab ∈ S := by
    intro ab hab
    exact reflect_mem g M N hg hM hN hab
  have hσinv : ∀ ab ∈ S, reflect g M N (reflect g M N ab) = ab := by
    intro ab hab
    exact reflect_involutive g M N hg hM hN hab
  let F1 : Finset (ℕ × ℕ) := S.filter P1
  let F2 : Finset (ℕ × ℕ) := S.filter P2
  -- membership facts used below
  have hF2S : F2 ⊆ S := Finset.filter_subset P2 S
  have hF1S : F1 ⊆ S := Finset.filter_subset P1 S
  have hmap : ∀ a ∈ F2, reflect g M N a ∈ F1 := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    rcases ha with ⟨haS, haP2⟩
    constructor
    · exact hσmap a haS
    · exact (arcP2_iff_P1_reflect g M N L hg hM hN hc hL hMN s hs0 hs1 haS).mp haP2
  have hinj : ∀ (a1 : ℕ × ℕ) (ha1 : a1 ∈ F2) (a2 : ℕ × ℕ) (ha2 : a2 ∈ F2),
      reflect g M N a1 = reflect g M N a2 → a1 = a2 := by
    intro a1 ha1 a2 ha2 h
    have h1 := hσinv a1 (hF2S ha1)
    have h2 := hσinv a2 (hF2S ha2)
    calc
      a1 = reflect g M N (reflect g M N a1) := h1.symm
      _ = reflect g M N (reflect g M N a2) := by rw [h]
      _ = a2 := h2
  have hsurj : ∀ b ∈ F1, ∃ a, ∃ ha : a ∈ F2, reflect g M N a = b := by
    intro b hb
    have hbS : b ∈ S := hF1S hb
    refine ⟨reflect g M N b, ?_⟩
    · refine ⟨?mem, ?eq⟩
      · rw [Finset.mem_filter]
        constructor
        · exact hσmap b hbS
        · -- P2(reflect b) from P1 b via the iff and the involution
          have hbP1 : P1 b := (Finset.mem_filter.mp hb).2
          have hrefS : reflect g M N b ∈ S := hσmap b hbS
          have hiff := arcP2_iff_P1_reflect g M N L hg hM hN hc hL hMN s hs0 hs1 hrefS
          -- hiff : P2 (reflect b) ↔ P1 (reflect (reflect b)); reflect(reflect b) = b
          have hrev : reflect g M N (reflect g M N b) = b := hσinv b hbS
          rw [hrev] at hiff
          exact hiff.mpr hbP1
      · exact hσinv b hbS
  exact Finset.card_bij (fun a (ha : a ∈ F2) => reflect g M N a) hmap hinj hsurj


/-- the first arc (residues `e` with `e < W`) contains exactly `Σ_{1≤e<⌈W⌉} C(e)`
pairs, where `C(e)` is the fibre over the residue `e`. -/
private theorem arc1_card_eq_sum (g M N L : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N)
    (hc : M.Coprime N) (hL : L = g * M * N) (hMN : M ≠ N)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1 / 8) :
    let W : ℝ := s * (L : ℝ)
    (((U (g * M) ×ˢ U (g * N)).filter (fun ab : ℕ × ℕ => (((eRes M N L ab : ℕ) : ℝ) < W))).card) =
      ∑ e ∈ Finset.Icc 1 (Nat.ceil W - 1), fibre (g * M) (g * N) M N L e := by
  classical
  let W : ℝ := s * (L : ℝ)
  have hL0 : 0 < L := by rw [hL]; positivity
  have hW2 : W < (L : ℝ) / 2 := by
    have hLc : 0 < (L : ℝ) := by exact_mod_cast hL0
    have hs' : s * (L : ℝ) < (1 / 8 : ℝ) * (L : ℝ) := mul_lt_mul_of_pos_right hs1 hLc
    dsimp [W]
    linarith
  have hW_L : W < (L : ℝ) := by
    have hLc : 0 < (L : ℝ) := by exact_mod_cast hL0
    linarith
  have hXL : Nat.ceil W ≤ L := by
    rw [Nat.ceil_le]
    exact le_of_lt hW_L
  have hfib : ∀ x ∈ U (g * M) ×ˢ U (g * N), eRes M N L x < L := by
    intro x hx
    change (x.1 * N + L - x.2 * M) % L < L
    exact Nat.mod_lt _ hL0
  have hC : ∀ e, ((U (g * M) ×ˢ U (g * N)).filter (fun x : ℕ × ℕ => eRes M N L x = e)).card =
      fibre (g * M) (g * N) M N L e := by
    intro e
    rfl
  have hsum0 := card_filter_eq_sum_fiber (L := L) (U (g * M) ×ˢ U (g * N))
    (fun ab : ℕ × ℕ => eRes M N L ab) hfib (fun e : ℕ => (e : ℝ) < W)
  -- hsum0 : the arc count = Σ_e C(e)·[e < W]
  calc
    ((U (g * M) ×ˢ U (g * N)).filter (fun ab : ℕ × ℕ => (((eRes M N L ab : ℕ) : ℝ) < W))).card
        = ∑ e ∈ Finset.range L,
            ((U (g * M) ×ˢ U (g * N)).filter (fun x : ℕ × ℕ => eRes M N L x = e)).card *
              (if (e : ℝ) < W then 1 else 0) := hsum0
    _ = ∑ e ∈ Finset.range L, fibre (g * M) (g * N) M N L e * (if (e : ℝ) < W then 1 else 0) := by
        refine Finset.sum_congr rfl ?_
        intro e he
        rw [hC]
    _ = ∑ e ∈ (Finset.range L).filter (fun e : ℕ => (e : ℝ) < W),
          fibre (g * M) (g * N) M N L e := by
        have hstep : (∑ e ∈ Finset.range L,
            fibre (g * M) (g * N) M N L e * (if (e : ℝ) < W then 1 else 0)) =
            (∑ e ∈ (Finset.range L).filter (fun e : ℕ => (e : ℝ) < W),
              fibre (g * M) (g * N) M N L e) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl ?_
          intro e he
          by_cases h : (e : ℝ) < W <;> simp [h]
        exact hstep
    _ = ∑ e ∈ Finset.range (Nat.ceil W), fibre (g * M) (g * N) M N L e := by
        have hset : (Finset.range L).filter (fun e : ℕ => (e : ℝ) < W) =
            Finset.range (Nat.ceil W) := by
          ext e
          rw [Finset.mem_filter]
          rw [Finset.mem_range]
          rw [Finset.mem_range]
          rw [← Nat.lt_ceil]
          constructor
          · intro h
            exact h.2
          · intro he
            constructor
            · have hc : (e : ℝ) < W := (Nat.lt_ceil).mp he
              have hc2 : (e : ℝ) < (L : ℝ) := lt_trans hc hW_L
              exact Nat.cast_lt.mp hc2
            · exact he
        rw [hset]
    _ = ∑ e ∈ Finset.Icc 1 (Nat.ceil W - 1), fibre (g * M) (g * N) M N L e := by
        have hzer : (∑ e ∈ (Finset.range (Nat.ceil W)).filter (fun e : ℕ => ¬0 < e),
            fibre (g * M) (g * N) M N L e) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro e he
          rcases Finset.mem_filter.mp he with ⟨heX, hnot⟩
          have he0 : e = 0 := by omega
          subst e
          exact fibre_zero_eq_zero g M N L hg hM hN hc hL hMN
        have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.range (Nat.ceil W))
          (p := fun e : ℕ => 0 < e) (f := fun e => fibre (g * M) (g * N) M N L e)
        rw [hzer] at hsplit
        have hmain' : (∑ e ∈ Finset.range (Nat.ceil W), fibre (g * M) (g * N) M N L e) =
            (∑ e ∈ (Finset.range (Nat.ceil W)).filter (fun e : ℕ => 0 < e),
              fibre (g * M) (g * N) M N L e) := by
          simpa [Nat.add_zero] using hsplit.symm
        rw [hmain']
        have hrest : (Finset.range (Nat.ceil W)).filter (fun e : ℕ => 0 < e) =
            Finset.Icc 1 (Nat.ceil W - 1) := by
          ext e
          rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
          constructor
          · intro h
            constructor
            · exact h.2
            · omega
          · intro h
            constructor
            · omega
            · exact h.1
        rw [hrest]


/-- the window condition splits into the two residue arcs, in `eRes` terms. -/
private theorem windowed_arcs_eRes (g M N L : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N)
    (hL : L = g * M * N) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1 / 8) :
    let W : ℝ := s * (L : ℝ)
    let S : Finset (ℕ × ℕ) := U (g * M) ×ˢ U (g * N)
    (S.filter (fun ab : ℕ × ℕ => ∃ j : Fin 3,
        |(((ab.1 : ℤ) * ((g * N) : ℤ) - (ab.2 : ℤ) * ((g * M) : ℤ)) -
            ((((j.1 : ℕ) : ℤ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℤ)) : ℝ)| <
          s * ((((g * M) * (g * N)) : ℕ) : ℝ))).card =
      (S.filter (fun ab : ℕ × ℕ => (((eRes M N L ab : ℕ) : ℝ) < W))).card +
        (S.filter (fun ab : ℕ × ℕ => (((L - eRes M N L ab : ℕ) : ℝ) < W))).card := by
  classical
  have h := window_card_split g M N L hg hM hN hL s hs0 hs1
  -- h : (let W := ...; let S' := product-of-range-filters; ...; (S'.filter window).card = (S'.filter P1).card + (S'.filter P2).card)
  -- unfold the lets of h:
  dsimp at h
  -- unfold U and eRes in the goal:
  dsimp [U, eRes]
  exact h

/-- the windowed count on `U(gM) × U(gN)` is `2·Σ_{1≤e<⌈W⌉} C(e)`, by pairing the
two residue arcs through the reflection symmetry. -/
private theorem windowed_card_eq_two_sum (g M N L : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N)
    (hc : M.Coprime N) (hL : L = g * M * N) (hMN : M ≠ N)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1 / 8) :
    let W : ℝ := s * (L : ℝ)
    let S : Finset (ℕ × ℕ) := U (g * M) ×ˢ U (g * N)
    (S.filter (fun ab : ℕ × ℕ => ∃ j : Fin 3,
        |(((ab.1 : ℤ) * ((g * N) : ℤ) - (ab.2 : ℤ) * ((g * M) : ℤ)) -
            ((((j.1 : ℕ) : ℤ) - 1) * ((((g * M) * (g * N)) : ℕ) : ℤ)) : ℝ)| <
          s * ((((g * M) * (g * N)) : ℕ) : ℝ))).card =
      2 * (∑ e ∈ Finset.Icc 1 (Nat.ceil W - 1), fibre (g * M) (g * N) M N L e) := by
  classical
  have hsplit := windowed_arcs_eRes g M N L hg hM hN hL s hs0 hs1
  have harc := arc_card_eq g M N L hg hM hN hc hL hMN s hs0 hs1
  have harc1 := arc1_card_eq_sum g M N L hg hM hN hc hL hMN s hs0 hs1
  dsimp [U, eRes] at hsplit harc harc1 ⊢
  -- hsplit : T = A + B ; harc : B = A ; harc1 : A = Σ
  rw [harc] at hsplit
  rw [harc1] at hsplit
  -- hsplit : T = Σ + Σ ; goal : T = 2·Σ
  rw [two_mul]
  exact hsplit


/-- `eRes = e` (both `< L`) iff the pair satisfies the congruence
`a·N ≡ b·M + e (mod L)`, expressed with remainders. -/
private lemma eRes_eq_iff_congr (M N L a b e : ℕ) (hL0 : 0 < L)
    (haN : a * N < L) (hbM : b * M < L) (he : e < L) :
    eRes M N L (a, b) = e ↔ (a * N) % L = ((b * M + e) % L) := by
  classical
  set u : ℕ := a * N with hudef
  set v : ℕ := b * M with hvdef
  have hu : u < L := by rw [hudef]; exact haN
  have hv : v < L := by rw [hvdef]; exact hbM
  by_cases hle : v ≤ u
  · -- case `v ≤ u`: eRes = u − v
    have hle' : b * M ≤ a * N := by simpa [hudef, hvdef] using hle
    have heRes : eRes M N L (a, b) = u - v := by
      calc
        eRes M N L (a, b) = a * N - b * M :=
          eRes_of_pos (M := M) (N := N) (L := L) (x := a) (y := b) hle'
            (lt_of_le_of_lt (Nat.sub_le (a * N) (b * M)) haN)
        _ = u - v := by rw [← hudef, ← hvdef]
    have huL : u % L = u := Nat.mod_eq_of_lt hu
    constructor
    · intro h
      have huve : u - v = e := by rwa [heRes] at h
      have hue : u = v + e := by omega
      calc
        (a * N) % L = u % L := by rw [← hudef]
        _ = (v + e) % L := by rw [hue]
    · intro h
      have huve : u = (v + e) % L := by
        simpa [huL] using h
      by_cases hve : v + e < L
      · have hve2 : (v + e) % L = v + e := Nat.mod_eq_of_lt hve
        have hu2 : u = v + e := by simpa [hve2] using huve
        omega
      · have hge : L ≤ v + e := by omega
        have hve2 : (v + e) % L = v + e - L := by
          rw [Nat.mod_eq_sub_mod hge]
          exact Nat.mod_eq_of_lt (by omega : v + e - L < L)
        have hu2 : u = v + e - L := by simpa [hve2] using huve
        omega
  · -- case `u < v`: eRes = L − (v − u)
    have hlt : u < v := by omega
    have hlt' : a * N < b * M := by simpa [hudef, hvdef] using hlt
    have heRes : eRes M N L (a, b) = L - (v - u) := by
      calc
        eRes M N L (a, b) = L - (b * M - a * N) :=
          eRes_of_neg (M := M) (N := N) (L := L) (x := a) (y := b) hlt'
            (lt_of_le_of_lt (Nat.sub_le (b * M) (a * N)) hbM)
        _ = L - (v - u) := by rw [← hudef, ← hvdef]
    constructor
    · intro h
      have h2 : L - (v - u) = e := by rwa [heRes] at h
      -- v+e = L+u, so (v+e)%L = u
      have hve_ge : L ≤ v + e := by omega
      have hve2 : (v + e) % L = v + e - L := by
        rw [Nat.mod_eq_sub_mod hve_ge]
        exact Nat.mod_eq_of_lt (by omega : v + e - L < L)
      have hu2 : u = v + e - L := by omega
      calc
        (a * N) % L = u % L := by rw [← hudef]
        _ = (v + e) % L := by
          rw [hve2, ← hu2]
          exact Nat.mod_eq_of_lt hu
    · intro h
      have huL : u % L = u := Nat.mod_eq_of_lt hu
      have huve : u = (v + e) % L := by
        simpa [huL] using h
      by_cases hve : v + e < L
      · have hve2 : (v + e) % L = v + e := Nat.mod_eq_of_lt hve
        have hu2 : u = v + e := by simpa [hve2] using huve
        omega
      · have hge : L ≤ v + e := by omega
        have hve2 : (v + e) % L = v + e - L := by
          rw [Nat.mod_eq_sub_mod hge]
          exact Nat.mod_eq_of_lt (by omega : v + e - L < L)
        have hu2 : u = v + e - L := by simpa [hve2] using huve
        -- want L − (v−u) = e
        omega

/-- the fibre over residue `e` equals the core pair-count at congruence class `e`,
provided `e < L` -/
private lemma fibre_eq_core_count (g M N L e : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N)
    (hL : L = g * M * N) (he : e < L) :
    fibre (g * M) (g * N) M N L e =
      ((U (g * M) ×ˢ U (g * N)).filter (fun ab : ℕ × ℕ =>
        ((ab.1 * N) % L = ((ab.2 * M + e) % L)))).card := by
  have hL0 : 0 < L := by rw [hL]; positivity
  apply congrArg Finset.card
  -- prove the filtered sets are equal
  ext ab
  constructor
  · intro hab
    rw [Finset.mem_filter] at hab ⊢
    rcases hab with ⟨habS, heRes⟩
    constructor
    · exact habS
    · have ha1 : ab.1 < g * M := (mem_U.mp (Finset.mem_product.mp habS).1).1
      have hb1 : ab.2 < g * N := (mem_U.mp (Finset.mem_product.mp habS).2).1
      have haN : ab.1 * N < L := mul_lt_L_of_lt_gM (g := g) hN hL ha1
      have hbM : ab.2 * M < L := mul_lt_L_of_lt_gN (g := g) hM hL hb1
      exact (eRes_eq_iff_congr M N L ab.1 ab.2 e hL0 haN hbM he).mp heRes
  · intro hab
    rw [Finset.mem_filter] at hab ⊢
    rcases hab with ⟨habS, hcong⟩
    constructor
    · exact habS
    · have ha1 : ab.1 < g * M := (mem_U.mp (Finset.mem_product.mp habS).1).1
      have hb1 : ab.2 < g * N := (mem_U.mp (Finset.mem_product.mp habS).2).1
      have haN : ab.1 * N < L := mul_lt_L_of_lt_gM (g := g) hN hL ha1
      have hbM : ab.2 * M < L := mul_lt_L_of_lt_gN (g := g) hM hL hb1
      exact (eRes_eq_iff_congr M N L ab.1 ab.2 e hL0 haN hbM he).mpr hcong


/-- gcd/quotient identifications when applying the core residue formula at `(gM, gN)`. -/
private lemma core_ids (g M N : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N) (hc : M.Coprime N) :
    ((g * M).gcd (g * N) = g) ∧
    ((g * M) / ((g * M).gcd (g * N)) = M) ∧
    ((g * N) / ((g * M).gcd (g * N)) = N) ∧
    ((g * M) * (g * N) / ((g * M).gcd (g * N)) = g * M * N) := by
  have h1 : (g * M).gcd (g * N) = g := by
    calc
      (g * M).gcd (g * N) = (M * g).gcd (N * g) := by rw [Nat.mul_comm g M, Nat.mul_comm g N]
      _ = M.gcd N * g := Nat.gcd_mul_right M g N
      _ = 1 * g := by rw [hc.gcd_eq_one]
      _ = g := by rw [one_mul]
  have h2 : (g * M) / ((g * M).gcd (g * N)) = M := by
    rw [h1]
    exact Nat.mul_div_right M hg
  have h3 : (g * N) / ((g * M).gcd (g * N)) = N := by
    rw [h1]
    exact Nat.mul_div_right N hg
  have h4 : (g * M) * (g * N) / ((g * M).gcd (g * N)) = g * M * N := by
    rw [h1]
    rw [show (g * M) * (g * N) = g * (g * M * N) by ring]
    exact Nat.mul_div_right (g * M * N) hg
  exact ⟨h1, h2, h3, h4⟩

/-- the fibre over residue `e` at modulus `gMN` equals the core formula value. -/
private lemma fibre_core_formula (g M N : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N)
    (hc : M.Coprime N) (e : ℕ) (he : e < g * M * N) :
    let q : ℕ := M * N
    let K : ℕ := ∏ p ∈ (Nat.primeFactors g).filter (fun p => ¬ p ∣ q), p ^ (g.factorization p)
    let Phi : ℕ := ∏ p ∈ Nat.primeFactors q, (p ^ (g.factorization p)).totient
    let S : ℕ → ℕ := fun c => ∏ p ∈ Nat.primeFactors K,
        if p ∣ c then (p ^ (K.factorization p)).totient
        else p ^ (K.factorization p - 1) * (p - 2)
    fibre (g * M) (g * N) M N (g * M * N) e =
      if e.gcd q = 1 then Phi * S (e % (g * M * N)) else 0 := by
  classical
  dsimp
  let q : ℕ := M * N
  let K : ℕ := ∏ p ∈ (Nat.primeFactors g).filter (fun p => ¬ p ∣ q), p ^ (g.factorization p)
  let Phi : ℕ := ∏ p ∈ Nat.primeFactors q, (p ^ (g.factorization p)).totient
  let S : ℕ → ℕ := fun c => ∏ p ∈ Nat.primeFactors K,
      if p ∣ c then (p ^ (K.factorization p)).totient
      else p ^ (K.factorization p - 1) * (p - 2)
  have hb := fibre_eq_core_count g M N (g * M * N) e hg hM hN (by rfl) he
  rw [hb]
  have hcore := residue_fiber_formula (g * M) (g * N) e (by positivity : 0 < g * M)
    (by positivity : 0 < g * N)
  dsimp at hcore
  have hids := core_ids g M N hg hM hN hc
  rcases hids with ⟨hgid, _, _, _⟩
  have hMid : (g * M) / g = M := Nat.mul_div_right M hg
  have hNid : (g * N) / g = N := Nat.mul_div_right N hg
  have hLid : (g * M) * (g * N) / g = g * M * N := by
    rw [show (g * M) * (g * N) = g * (g * M * N) by ring]
    exact Nat.mul_div_right (g * M * N) hg
  -- rewrite the core's internal quotient/gcd data
  rw [hgid, hMid, hNid, hLid] at hcore
  -- hcore now: card over (range(gM)).filter-product with (a·N)%(gMN)=...  = if e.gcd (M·N)=1 then ...
  simpa [U] using hcore


/-- the interval sum of fibres collapses to `Phi·(Σ over coprime c)`; each fibre
`e < L` is `Phi·S(e)` when `e ⊥ q` and `0` otherwise. -/
private theorem fibre_sum_eval (g M N : ℕ) (hg : 0 < g) (hM : 0 < M) (hN : 0 < N)
    (hc : M.Coprime N) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1 / 8) :
    (∑ e ∈ Finset.Icc 1 (Nat.ceil (s * ((g * M * N : ℕ) : ℝ)) - 1),
        fibre (g * M) (g * N) M N (g * M * N) e) =
      (∏ p ∈ Nat.primeFactors (M * N), (p ^ (g.factorization p)).totient) *
      (∑ c ∈ (Finset.Icc 1 (Nat.ceil (s * ((g * M * N : ℕ) : ℝ)) - 1)).filter
          (fun c => c.gcd (M * N) = 1),
        (fun c : ℕ => ∏ p ∈ Nat.primeFactors (∏ p ∈ (Nat.primeFactors g).filter (fun p => ¬ p ∣ M * N),
            p ^ (g.factorization p)),
          if p ∣ c then (p ^ ((∏ p ∈ (Nat.primeFactors g).filter (fun p => ¬ p ∣ M * N),
              p ^ (g.factorization p)).factorization p)).totient
          else p ^ ((∏ p ∈ (Nat.primeFactors g).filter (fun p => ¬ p ∣ M * N),
              p ^ (g.factorization p)).factorization p - 1) * (p - 2)) c) := by
  classical
  set L : ℕ := g * M * N with hLdef
  set W : ℝ := s * (L : ℝ) with hWdef
  set q : ℕ := M * N with hqdef
  set K : ℕ := ∏ p ∈ (Nat.primeFactors g).filter (fun p => ¬ p ∣ q), p ^ (g.factorization p) with hKdef
  set Phi : ℕ := ∏ p ∈ Nat.primeFactors q, (p ^ (g.factorization p)).totient with hPhidef
  set S : ℕ → ℕ := fun c => ∏ p ∈ Nat.primeFactors K,
      if p ∣ c then (p ^ (K.factorization p)).totient
      else p ^ (K.factorization p - 1) * (p - 2) with hSdef
  have hL0 : 0 < L := by rw [hLdef]; positivity
  have hW_L : W < (L : ℝ) := by
    have hLc : 0 < (L : ℝ) := by exact_mod_cast hL0
    have hs' : s * (L : ℝ) < (1 / 8 : ℝ) * (L : ℝ) := mul_lt_mul_of_pos_right hs1 hLc
    dsimp [W]
    linarith
  have hXL : Nat.ceil W ≤ L := by
    rw [Nat.ceil_le]
    exact le_of_lt hW_L
  -- each e in the interval is < L
  have hltL : ∀ e ∈ Finset.Icc 1 (Nat.ceil W - 1), e < L := by
    intro e he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have he2 : e ≤ Nat.ceil W - 1 := (Finset.mem_Icc.mp he).2
    have heW : e < Nat.ceil W := by omega
    have heWL : (e : ℝ) < W := (Nat.lt_ceil).mp heW
    have heL : (e : ℝ) < (L : ℝ) := lt_trans heWL hW_L
    exact Nat.cast_lt.mp heL
  -- fibre values
  have hfib : ∀ e ∈ Finset.Icc 1 (Nat.ceil W - 1),
      fibre (g * M) (g * N) M N L e = (if e.gcd q = 1 then Phi * S (e % L) else 0) := by
    intro e he
    have heL : e < L := hltL e he
    have hfc := fibre_core_formula g M N hg hM hN hc e (by rw [← hLdef]; exact heL)
    simpa [L, q, K, Phi, S, hLdef, hqdef, hKdef, hPhidef, hSdef] using hfc
  -- (a) convert the summand of the left sum to the if-form
  have hleft : (∑ e ∈ Finset.Icc 1 (Nat.ceil W - 1), fibre (g * M) (g * N) M N L e) =
      (∑ e ∈ Finset.Icc 1 (Nat.ceil W - 1), if e.gcd q = 1 then Phi * S (e % L) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro e he
    exact hfib e he
  rw [hleft]
  -- (b) drop the zero terms and use e%L = e
  have hterm : ∀ e ∈ Finset.Icc 1 (Nat.ceil W - 1),
      (if e.gcd q = 1 then Phi * S (e % L) else 0) =
        (if e.gcd q = 1 then Phi * S e else 0) := by
    intro e he
    have heL : e < L := hltL e he
    have hmod : e % L = e := Nat.mod_eq_of_lt heL
    by_cases h : e.gcd q = 1 <;> simp [hmod, h]
  rw [Finset.sum_congr rfl (fun e he => hterm e he)]
  -- (c) sum over the coprime subset only
  have hsumc : (∑ e ∈ Finset.Icc 1 (Nat.ceil W - 1),
      if e.gcd q = 1 then Phi * S e else 0) =
      (∑ e ∈ (Finset.Icc 1 (Nat.ceil W - 1)).filter (fun e => e.gcd q = 1), Phi * S e) := by
    rw [Finset.sum_filter]
  rw [hsumc]
  -- (d) factor Phi out
  rw [← Finset.mul_sum]


/-- exact count of reduced pairs `(a,b)`, `0≤a<m`, `gcd(a,m)=1`, `0≤b<n`, `gcd(b,n)=1`
with `a/m` and `b/n` lying in a window of width `s` (on the circle), expressed via the
totient factor `Phi` and the function `S`. -/
private theorem fibre_count_eq_step (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n)
    (s : ℝ) (hs : 0 ≤ s) (hsmall : s < 1 / 8) :
    let g : ℕ := m.gcd n
    let M : ℕ := m / g
    let N : ℕ := n / g
    let q : ℕ := M * N
    let L : ℕ := g * M * N
    (((Finset.product ((Finset.range m).filter (fun a : ℕ => a.gcd m = 1))
        ((Finset.range n).filter (fun b : ℕ => b.gcd n = 1))).filter
      (fun ab : ℕ × ℕ => ∃ j : Fin 3,
        |((ab.1 : ℤ) * (n : ℤ) - (ab.2 : ℤ) * (m : ℤ) -
            (((j.1 : ℕ) : ℤ) - 1) * ((m * n : ℕ) : ℤ) : ℝ)| <
          s * ((m * n : ℕ) : ℝ))).card) =
      2 * (∑ e ∈ Finset.Icc 1 (Nat.ceil (s * (L : ℝ)) - 1),
        fibre (g * M) (g * N) M N L e) := by
  classical
  let g : ℕ := m.gcd n
  let M : ℕ := m / g
  let N : ℕ := n / g
  let q : ℕ := M * N
  let L : ℕ := g * M * N
  have hg : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_left (m := m) n hm
  have hM : 0 < M := by
    dsimp [M, g]
    exact Nat.div_pos (Nat.gcd_le_left (m := m) n hm) hg
  have hN : 0 < N := by
    dsimp [N, g]
    exact Nat.div_pos (Nat.gcd_le_right (n := n) m hn) hg
  have hMNc : M.Coprime N := by
    dsimp [M, N, g]
    exact Nat.coprime_div_gcd_div_gcd (m := m) (n := n) hg
  have hMN : M ≠ N := by
    intro h
    apply hmn
    calc
      m = g * M := by dsimp [g, M]; exact (gcd_mul_div_self m n).symm
      _ = g * N := by rw [h]
      _ = n := by dsimp [g, N]; exact (self_eq_gcd_mul_div' m n).symm
  have hm_eq : m = g * M := by dsimp [g, M]; exact (gcd_mul_div_self m n).symm
  have hn_eq : n = g * N := by dsimp [g, N]; exact self_eq_gcd_mul_div' m n
  have hL : L = g * M * N := rfl
  have hwin := windowed_card_eq_two_sum g M N L hg hM hN hMNc hL hMN s hs hsmall
  -- unfold the lets inside hwin:
  have hLHS : (((Finset.product ((Finset.range m).filter (fun a : ℕ => a.gcd m = 1))
        ((Finset.range n).filter (fun b : ℕ => b.gcd n = 1))).filter
      (fun ab : ℕ × ℕ => ∃ j : Fin 3,
        |((ab.1 : ℤ) * (n : ℤ) - (ab.2 : ℤ) * (m : ℤ) -
            (((j.1 : ℕ) : ℤ) - 1) * ((m * n : ℕ) : ℤ) : ℝ)| <
          s * ((m * n : ℕ) : ℝ))).card) =
      2 * (∑ e ∈ Finset.Icc 1 (Nat.ceil (s * (L : ℝ)) - 1),
        fibre (g * M) (g * N) M N L e) := by
    rw [hm_eq, hn_eq]
    dsimp [g, M, N, L] at hwin ⊢
    simpa [U] using hwin
  exact hLHS



/-- the interval sum of fibres over `m,n` equals `Phi·(Σ over coprime c)` (explicit form) -/
private theorem fibre_sum_mn (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n)
    (s : ℝ) (hs : 0 ≤ s) (hsmall : s < 1 / 8) :
    (∑ e ∈ Finset.Icc 1 (Nat.ceil (s * ((m * n / (m.gcd n) : ℕ) : ℝ)) - 1),
        fibre m n (m / (m.gcd n)) (n / (m.gcd n)) (m * n / (m.gcd n)) e) =
      (∏ p ∈ Nat.primeFactors (m * n / ((m.gcd n) * (m.gcd n))), (p ^ ((m.gcd n).factorization p)).totient) *
      (∑ c ∈ (Finset.Icc 1 (Nat.ceil (s * ((m * n / (m.gcd n) : ℕ) : ℝ)) - 1)).filter
          (fun c => c.gcd (m * n / ((m.gcd n) * (m.gcd n))) = 1),
        (fun c : ℕ => ∏ p ∈ Nat.primeFactors (∏ p ∈ (Nat.primeFactors (m.gcd n)).filter
            (fun p => ¬ p ∣ m * n / ((m.gcd n) * (m.gcd n))), p ^ ((m.gcd n).factorization p)),
          if p ∣ c then (p ^ ((∏ p ∈ (Nat.primeFactors (m.gcd n)).filter
              (fun p => ¬ p ∣ m * n / ((m.gcd n) * (m.gcd n))), p ^ ((m.gcd n).factorization p)).factorization p)).totient
          else p ^ ((∏ p ∈ (Nat.primeFactors (m.gcd n)).filter
              (fun p => ¬ p ∣ m * n / ((m.gcd n) * (m.gcd n))), p ^ ((m.gcd n).factorization p)).factorization p - 1) * (p - 2)) c) := by
  classical
  have hg : 0 < m.gcd n := Nat.gcd_pos_of_pos_left (m := m) n hm
  have hM : 0 < m / (m.gcd n) := Nat.div_pos (Nat.gcd_le_left (m := m) n hm) hg
  have hN : 0 < n / (m.gcd n) := Nat.div_pos (Nat.gcd_le_right (n := n) m hn) hg
  have hMNc : (m / (m.gcd n)).Coprime (n / (m.gcd n)) :=
    Nat.coprime_div_gcd_div_gcd (m := m) (n := n) hg
  have hMN : m / (m.gcd n) ≠ n / (m.gcd n) := by
    intro h
    apply hmn
    calc
      m = (m.gcd n) * (m / (m.gcd n)) := by exact (gcd_mul_div_self m n).symm
      _ = (m.gcd n) * (n / (m.gcd n)) := by rw [h]
      _ = n := (self_eq_gcd_mul_div' m n).symm
  have hfib := fibre_sum_eval (m.gcd n) (m / (m.gcd n)) (n / (m.gcd n)) hg hM hN hMNc s hs hsmall
  dsimp at hfib
  have hgM : (m.gcd n) * (m / (m.gcd n)) = m := gcd_mul_div_self m n
  have hgN : (m.gcd n) * (n / (m.gcd n)) = n := (self_eq_gcd_mul_div' m n).symm
  have hL : (m.gcd n) * (m / (m.gcd n)) * (n / (m.gcd n)) = m * n / (m.gcd n) := by
    rw [mul_assoc]
    exact (mul_div_gcd m n hm).symm
  have hq : (m / (m.gcd n)) * (n / (m.gcd n)) = m * n / ((m.gcd n) * (m.gcd n)) :=
    (mul_div_gcd_sq m n).symm
  rw [hL, hgM, hgN, hq] at hfib
  -- hfib now is exactly the target equality
  exact hfib


/-- LHS reduction: windowed count = `2·Σ_{1≤e<⌈W⌉} C(e)` (explicit form). -/
private theorem fibre_count_lhs (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n)
    (s : ℝ) (hs : 0 ≤ s) (hsmall : s < 1 / 8) :
    (((Finset.product ((Finset.range m).filter (fun a : ℕ => a.gcd m = 1))
        ((Finset.range n).filter (fun b : ℕ => b.gcd n = 1))).filter
      (fun ab : ℕ × ℕ => ∃ j : Fin 3,
        |((ab.1 : ℤ) * (n : ℤ) - (ab.2 : ℤ) * (m : ℤ) -
            (((j.1 : ℕ) : ℤ) - 1) * ((m * n : ℕ) : ℤ) : ℝ)| <
          s * ((m * n : ℕ) : ℝ))).card) =
      2 * (∑ e ∈ Finset.Icc 1 (Nat.ceil (s * ((m * n / (m.gcd n) : ℕ) : ℝ)) - 1),
        fibre m n (m / (m.gcd n)) (n / (m.gcd n)) (m * n / (m.gcd n)) e) := by
  classical
  have hstep := fibre_count_eq_step m n hm hn hmn s hs hsmall
  dsimp at hstep
  have hgM : (m.gcd n) * (m / (m.gcd n)) = m := gcd_mul_div_self m n
  have hgN : (m.gcd n) * (n / (m.gcd n)) = n := (self_eq_gcd_mul_div' m n).symm
  have hL : (m.gcd n) * (m / (m.gcd n)) * (n / (m.gcd n)) = m * n / (m.gcd n) := by
    rw [mul_assoc]
    exact (mul_div_gcd m n hm).symm
  rw [hL, hgM, hgN] at hstep
  exact hstep

/-- exact count of reduced pairs `(a,b)`, `0≤a<m`, `gcd(a,m)=1`, `0≤b<n`, `gcd(b,n)=1`
with `a/m` and `b/n` lying in an `s`-window (arc sense), expressed via `Phi` and `S`. -/
theorem fibre_count_eq (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n)
    (s : ℝ) (hs : 0 ≤ s) (hsmall : s < 1 / 8) :
    let g : ℕ := m.gcd n
    let K : ℕ := ∏ p ∈ (Nat.primeFactors g).filter (fun p => ¬ p ∣ m * n / (g * g)),
        p ^ (g.factorization p)
    let Phi : ℕ := ∏ p ∈ Nat.primeFactors (m * n / (g * g)), (p ^ (g.factorization p)).totient
    let L : ℕ := m * n / g
    let W : ℝ := s * (L : ℝ)
    let S : ℕ → ℕ := fun c => ∏ p ∈ Nat.primeFactors K,
        if p ∣ c then (p ^ (K.factorization p)).totient
        else p ^ (K.factorization p - 1) * (p - 2)
    (((Finset.product ((Finset.range m).filter (fun a : ℕ => a.gcd m = 1))
        ((Finset.range n).filter (fun b : ℕ => b.gcd n = 1))).filter
      (fun ab : ℕ × ℕ => ∃ j : Fin 3,
        |((ab.1 : ℤ) * (n : ℤ) - (ab.2 : ℤ) * (m : ℤ) -
            (((j.1 : ℕ) : ℤ) - 1) * ((m * n : ℕ) : ℤ) : ℝ)| <
          s * ((m * n : ℕ) : ℝ))).card : ℕ) =
      2 * Phi * (∑ c ∈ (Finset.Icc 1 (Nat.ceil W - 1)).filter (fun c => c.gcd (m * n / (g * g)) = 1),
        S c) := by
  classical
  dsimp
  have h1 := fibre_count_lhs m n hm hn hmn s hs hsmall
  have h2 := fibre_sum_mn m n hm hn hmn s hs hsmall
  calc
    (((Finset.product ((Finset.range m).filter (fun a : ℕ => a.gcd m = 1))
        ((Finset.range n).filter (fun b : ℕ => b.gcd n = 1))).filter
      (fun ab : ℕ × ℕ => ∃ j : Fin 3,
        |((ab.1 : ℤ) * (n : ℤ) - (ab.2 : ℤ) * (m : ℤ) -
            (((j.1 : ℕ) : ℤ) - 1) * ((m * n : ℕ) : ℤ) : ℝ)| <
          s * ((m * n : ℕ) : ℝ))).card)
        = 2 * (∑ e ∈ Finset.Icc 1 (Nat.ceil (s * ((m * n / (m.gcd n) : ℕ) : ℝ)) - 1),
            fibre m n (m / (m.gcd n)) (n / (m.gcd n)) (m * n / (m.gcd n)) e) := h1
    _ = 2 * ((∏ p ∈ Nat.primeFactors (m * n / ((m.gcd n) * (m.gcd n))), (p ^ ((m.gcd n).factorization p)).totient) *
        (∑ c ∈ (Finset.Icc 1 (Nat.ceil (s * ((m * n / (m.gcd n) : ℕ) : ℝ)) - 1)).filter
            (fun c => c.gcd (m * n / ((m.gcd n) * (m.gcd n))) = 1),
          (fun c : ℕ => ∏ p ∈ Nat.primeFactors (∏ p ∈ (Nat.primeFactors (m.gcd n)).filter
              (fun p => ¬ p ∣ m * n / ((m.gcd n) * (m.gcd n))), p ^ ((m.gcd n).factorization p)),
            if p ∣ c then (p ^ ((∏ p ∈ (Nat.primeFactors (m.gcd n)).filter
                (fun p => ¬ p ∣ m * n / ((m.gcd n) * (m.gcd n))), p ^ ((m.gcd n).factorization p)).factorization p)).totient
            else p ^ ((∏ p ∈ (Nat.primeFactors (m.gcd n)).filter
                (fun p => ¬ p ∣ m * n / ((m.gcd n) * (m.gcd n))), p ^ ((m.gcd n).factorization p)).factorization p - 1) * (p - 2)) c)) := by
        rw [h2]
    _ = 2 * (∏ p ∈ Nat.primeFactors (m * n / ((m.gcd n) * (m.gcd n))), (p ^ ((m.gcd n).factorization p)).totient) *
          (∑ c ∈ (Finset.Icc 1 (Nat.ceil (s * ((m * n / (m.gcd n) : ℕ) : ℝ)) - 1)).filter
              (fun c => c.gcd (m * n / ((m.gcd n) * (m.gcd n))) = 1),
            (fun c : ℕ => ∏ p ∈ Nat.primeFactors (∏ p ∈ (Nat.primeFactors (m.gcd n)).filter
                (fun p => ¬ p ∣ m * n / ((m.gcd n) * (m.gcd n))), p ^ ((m.gcd n).factorization p)),
              if p ∣ c then (p ^ ((∏ p ∈ (Nat.primeFactors (m.gcd n)).filter
                  (fun p => ¬ p ∣ m * n / ((m.gcd n) * (m.gcd n))), p ^ ((m.gcd n).factorization p)).factorization p)).totient
              else p ^ ((∏ p ∈ (Nat.primeFactors (m.gcd n)).filter
                  (fun p => ¬ p ∣ m * n / ((m.gcd n) * (m.gcd n))), p ^ ((m.gcd n).factorization p)).factorization p - 1) * (p - 2)) c) := by
        ring

end Commons.NumberTheory.DuffinSchaeffer