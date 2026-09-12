import Mathlib.Topology.Algebra.Polynomial

/-!
# Level chains with descending levels (`chain_down`)

Same as `Submission/ChainLevels.chain_down` but in its own file (one child per
file).  Mirror image of `chain_up`: if `f(b) ≤ −D·u` and `D·u ≤ f(a)` with
`a < b`, then for every `j = 0..D` there is a point `s j` with
`f (s j) = (D−j)·u`; the `s j` are strictly increasing and lie in `[a, b]`.

In contrast to `ChainLevels.chain_down` (which needs the *strict* upper
hypothesis `D·u < f a` because it demands points in `(a, b]`), this statement
only asks for points in `[a, b]`: the degenerate case `f a = D·u` is absorbed
by starting the chain at `a` itself, and every subsequent level lies strictly
below `D·u`, so it is attained at points `> a` by a strict sign change.
-/

noncomputable section

open scoped Real
open Polynomial

namespace Submission.ChainDown

/-- Sign change ⇒ a real polynomial has a root strictly between the two points. -/
lemma exists_root_of_mul_neg {p : Polynomial ℝ} {a b : ℝ} (hab : a < b)
    (h : p.eval a * p.eval b < 0) : ∃ r : ℝ, a < r ∧ r < b ∧ p.eval r = 0 := by
  rcases (mul_neg_iff.mp h) with hlt | hlt
  · have hpa_pos : 0 < p.eval a := hlt.1
    have hpb_neg : p.eval b < 0 := hlt.2
    have hIcc : (0 : ℝ) ∈ Set.Icc (p.eval b) (p.eval a) := ⟨le_of_lt hpb_neg, le_of_lt hpa_pos⟩
    have hset : Set.Icc (p.eval b) (p.eval a) ⊆ (fun x => p.eval x) '' Set.Icc a b :=
      intermediate_value_Icc' (le_of_lt hab) p.continuous.continuousOn
    rcases hset hIcc with ⟨c, hcIcc, hc0⟩
    refine ⟨c, ?_, ?_, hc0⟩
    · have hc_ne : c ≠ a := by
        intro hca
        subst c
        linarith
      exact lt_of_le_of_ne hcIcc.1 (Ne.symm hc_ne)
    · have hc_ne : c ≠ b := by
        intro hcb
        subst c
        linarith
      exact lt_of_le_of_ne hcIcc.2 hc_ne
  · have hpa_neg : p.eval a < 0 := hlt.1
    have hpb_pos : 0 < p.eval b := hlt.2
    have hIcc : (0 : ℝ) ∈ Set.Icc (p.eval a) (p.eval b) :=
      ⟨le_of_lt hpa_neg, le_of_lt hpb_pos⟩
    have hset : Set.Icc (p.eval a) (p.eval b) ⊆ (fun x => p.eval x) '' Set.Icc a b :=
      intermediate_value_Icc (le_of_lt hab) p.continuous.continuousOn
    rcases hset hIcc with ⟨c, hcIcc, hc0⟩
    refine ⟨c, ?_, ?_, hc0⟩
    · have hc_ne : c ≠ a := by
        intro hca
        subst c
        linarith
      exact lt_of_le_of_ne hcIcc.1 (Ne.symm hc_ne)
    · have hc_ne : c ≠ b := by
        intro hcb
        subst c
        linarith
      exact lt_of_le_of_ne hcIcc.2 hc_ne

/-- Start of the descending chain: some point `x ∈ [a, b]` where `p` takes the
top level `D·u`.  If `p a = D·u` we may take `x = a`; otherwise a strict sign
change of `p − D·u` across `(a, b)` gives a root inside. -/
lemma exists_top_level (D : ℕ) (hD : 1 ≤ D) {u : ℝ} (hu : 0 < u) {p : Polynomial ℝ}
    {a b : ℝ} (hab : a < b) (hlo : p.eval b ≤ -((D : ℝ) * u))
    (hhi : (D : ℝ) * u ≤ p.eval a) :
    ∃ x : ℝ, a ≤ x ∧ x ≤ b ∧ p.eval x = (D : ℝ) * u := by
  by_cases heq : p.eval a = (D : ℝ) * u
  · refine ⟨a, le_rfl, le_of_lt hab, heq⟩
  · have hgt : (D : ℝ) * u < p.eval a := lt_of_le_of_ne hhi (Ne.symm heq)
    let q0 : Polynomial ℝ := p - Polynomial.C ((D : ℝ) * u)
    have hq0a : 0 < q0.eval a := by
      dsimp [q0]
      rw [Polynomial.eval_sub, Polynomial.eval_C]
      exact sub_pos.mpr hgt
    have hq0b : q0.eval b < 0 := by
      dsimp [q0]
      rw [Polynomial.eval_sub, Polynomial.eval_C]
      exact sub_neg.mpr (by
        have hDpos : (0 : ℝ) < (D : ℝ) := by
          exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hD)
        have hDu_pos : 0 < (D : ℝ) * u := mul_pos hDpos hu
        calc
          p.eval b ≤ -((D : ℝ) * u) := hlo
          _ < (D : ℝ) * u := by linarith)
    have hmul : q0.eval a * q0.eval b < 0 := mul_neg_of_pos_of_neg hq0a hq0b
    rcases exists_root_of_mul_neg (p := q0) hab hmul with ⟨c, hac, hcb, hcq0⟩
    refine ⟨c, le_of_lt hac, le_of_lt hcb, ?_⟩
    dsimp [q0] at hcq0
    rw [Polynomial.eval_sub, Polynomial.eval_C] at hcq0
    exact sub_eq_zero.mp hcq0

/-- extend a chain one step in the mirror (descending-level) direction: given a point
where `p = (D-k)·u`, find (if `k+1 ≤ D`) a point strictly to its right where
`p = (D-(k+1))·u`.  (No hypothesis relating `x` to `a` is needed: the next
target lies one unit of `u` strictly below the value at `x`, while `p b` is at
most `−D·u`, hence far below every nonnegative target.) -/
lemma exists_next_level_down (D k : ℕ) {u : ℝ} (hD : 1 ≤ D) (hu : 0 < u) {p : Polynomial ℝ}
    {x b : ℝ} (hxb : x ≤ b) (hk1 : k + 1 ≤ D)
    (hpx : p.eval x = ((D - k : ℕ) : ℝ) * u) (hlo : p.eval b ≤ -((D : ℝ) * u)) :
    ∃ y : ℝ, x < y ∧ y ≤ b ∧ p.eval y = ((D - (k + 1) : ℕ) : ℝ) * u := by
  have hnat : D - k = (D - (k + 1)) + 1 := by omega
  have hcast : ((D - k : ℕ) : ℝ) = ((D - (k + 1) : ℕ) : ℝ) + 1 := by
    rw [hnat, Nat.cast_add, Nat.cast_one]
  let t : ℝ := ((D - (k + 1) : ℕ) : ℝ) * u
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hD)
  have hDu_pos : 0 < (D : ℝ) * u := mul_pos hDpos hu
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have hpb_lt_t : p.eval b < t := by
    dsimp [t]
    have hneg : -((D : ℝ) * u) < 0 := by linarith
    exact lt_of_lt_of_le (lt_of_le_of_lt hlo hneg) ht_nonneg
  have hx_lt_b : x < b := by
    refine lt_of_le_of_ne hxb ?_
    intro hxb_eq
    have hp : p.eval b = ((D - k : ℕ) : ℝ) * u := by simpa [hxb_eq] using hpx
    rw [hcast] at hp
    dsimp [t] at hpb_lt_t
    nlinarith [hu]
  let q : Polynomial ℝ := p - Polynomial.C t
  have hqx : 0 < q.eval x := by
    dsimp [q]
    rw [Polynomial.eval_sub, Polynomial.eval_C, hpx, hcast]
    dsimp [t]
    nlinarith [hu]
  have hqb : q.eval b < 0 := by
    dsimp [q, t]
    rw [Polynomial.eval_sub, Polynomial.eval_C]
    exact sub_neg.mpr hpb_lt_t
  have hmul : q.eval x * q.eval b < 0 := mul_neg_of_pos_of_neg hqx hqb
  rcases exists_root_of_mul_neg (p := q) hx_lt_b hmul with ⟨c, hxc, hcb, hc0⟩
  refine ⟨c, hxc, le_of_lt hcb, ?_⟩
  dsimp [q, t] at hc0
  rw [Polynomial.eval_sub, Polynomial.eval_C] at hc0
  exact sub_eq_zero.mp hc0

/-- recursive mirror chain: `chainDownPoints k` crosses level `(D-k)·u`, starting
from the top-level point `x0`.  For `k+1 ≤ D` the value at `k+1` is produced from
the value at `k` by `exists_next_level_down`; for larger `k` it is junk (`x0`). -/
private noncomputable def chainDownPoints (D : ℕ) (u : ℝ) (hu : 0 < u) (hD : 1 ≤ D)
    (p : Polynomial ℝ) (b : ℝ) (hlo : p.eval b ≤ -((D : ℝ) * u)) (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | k + 1 =>
      if h : k + 1 ≤ D ∧
                chainDownPoints D u hu hD p b hlo x0 k ≤ b ∧
                p.eval (chainDownPoints D u hu hD p b hlo x0 k) =
                  ((D - k : ℕ) : ℝ) * u then
        Classical.choose (exists_next_level_down D k hD hu h.2.1 h.1 h.2.2 hlo)
      else x0

private lemma chainDownPoints_succ (D : ℕ) (u : ℝ) (hu : 0 < u) (hD : 1 ≤ D)
    (p : Polynomial ℝ) (b : ℝ) (hlo : p.eval b ≤ -((D : ℝ) * u)) (x0 : ℝ) {k : ℕ}
    (hk1 : k + 1 ≤ D)
    (h2 : chainDownPoints D u hu hD p b hlo x0 k ≤ b)
    (h3 : p.eval (chainDownPoints D u hu hD p b hlo x0 k) = ((D - k : ℕ) : ℝ) * u) :
    chainDownPoints D u hu hD p b hlo x0 k <
        chainDownPoints D u hu hD p b hlo x0 (k + 1) ∧
    chainDownPoints D u hu hD p b hlo x0 (k + 1) ≤ b ∧
    p.eval (chainDownPoints D u hu hD p b hlo x0 (k + 1)) =
      ((D - (k + 1) : ℕ) : ℝ) * u := by
  have hc : k + 1 ≤ D ∧ chainDownPoints D u hu hD p b hlo x0 k ≤ b ∧
      p.eval (chainDownPoints D u hu hD p b hlo x0 k) = ((D - k : ℕ) : ℝ) * u :=
    ⟨hk1, h2, h3⟩
  rw [chainDownPoints]
  rw [dif_pos hc]
  rcases Classical.choose_spec (exists_next_level_down D k hD hu hc.2.1 hc.1 hc.2.2 hlo) with
    ⟨hxy, hyb, hpy⟩
  exact ⟨hxy, hyb, hpy⟩

private lemma chainDownPoints_spec (D : ℕ) (u : ℝ) (hu : 0 < u) (hD : 1 ≤ D)
    (p : Polynomial ℝ) (b : ℝ) (hlo : p.eval b ≤ -((D : ℝ) * u)) (x0 : ℝ)
    (hx0b : x0 ≤ b) (hx0 : p.eval x0 = ((D - 0 : ℕ) : ℝ) * u) :
    ∀ k : ℕ, k ≤ D → x0 ≤ chainDownPoints D u hu hD p b hlo x0 k ∧
      chainDownPoints D u hu hD p b hlo x0 k ≤ b ∧
      p.eval (chainDownPoints D u hu hD p b hlo x0 k) = ((D - k : ℕ) : ℝ) * u := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [chainDownPoints, hx0b, hx0]
  | succ k ih =>
      intro hk1
      have hk : k ≤ D := by omega
      rcases ih hk with ⟨h1, h2, h3⟩
      rcases chainDownPoints_succ D u hu hD p b hlo x0 (by omega : k + 1 ≤ D) h2 h3 with
        ⟨hlt, hb2, hp2⟩
      exact ⟨le_trans h1 (le_of_lt hlt), hb2, hp2⟩

private lemma chainDownPoints_mono (D : ℕ) (u : ℝ) (hu : 0 < u) (hD : 1 ≤ D)
    (p : Polynomial ℝ) (b : ℝ) (hlo : p.eval b ≤ -((D : ℝ) * u)) (x0 : ℝ)
    (hx0b : x0 ≤ b) (hx0 : p.eval x0 = ((D - 0 : ℕ) : ℝ) * u) :
    ∀ k : ℕ, k + 1 ≤ D →
      chainDownPoints D u hu hD p b hlo x0 k <
        chainDownPoints D u hu hD p b hlo x0 (k + 1) := by
  intro k hk1
  rcases chainDownPoints_spec D u hu hD p b hlo x0 hx0b hx0 k (by omega : k ≤ D)
    with ⟨h1, h2, h3⟩
  exact (chainDownPoints_succ D u hu hD p b hlo x0 hk1 h2 h3).1

/-- Mirror image of `chain_up`: if `f(b) ≤ −D·u` and `D·u ≤ f(a)` with
`a < b`, then for every `j = 0..D` there is a point `s j` with
`f (s j) = (D−j)·u`; the `s j` are strictly increasing and lie in `[a, b]`. -/
theorem chain_down {D : ℕ} (hD : 1 ≤ D) {u : ℝ} (hu : 0 < u) {p : Polynomial ℝ}
    {a b : ℝ} (hab : a < b) (hlo : p.eval b ≤ -((D : ℝ) * u)) (hhi : (D : ℝ) * u ≤ p.eval a) :
    ∃ s : Fin (D + 1) → ℝ,
      (∀ j : Fin (D + 1), a ≤ s j ∧ s j ≤ b) ∧
      (∀ j : Fin (D + 1), p.eval (s j) = ((D - j.val : ℕ) : ℝ) * u) ∧
      (∀ j : Fin D, s ⟨j.val, by omega⟩ < s ⟨j.val + 1, by omega⟩) := by
  rcases exists_top_level D hD hu hab hlo hhi with ⟨x0, hx0a, hx0b, hx0val⟩
  have hx0 : p.eval x0 = ((D - 0 : ℕ) : ℝ) * u := by
    simpa using hx0val
  refine ⟨fun j => chainDownPoints D u hu hD p b hlo x0 j.val, ?_, ?_, ?_⟩
  · intro j
    have hspec := chainDownPoints_spec D u hu hD p b hlo x0 hx0b hx0 j.val
      (by omega : j.val ≤ D)
    exact ⟨le_trans hx0a hspec.1, hspec.2.1⟩
  · intro j
    exact (chainDownPoints_spec D u hu hD p b hlo x0 hx0b hx0 j.val
      (by omega : j.val ≤ D)).2.2
  · intro j
    exact chainDownPoints_mono D u hu hD p b hlo x0 hx0b hx0 j.val
      (by omega : j.val + 1 ≤ D)

end Submission.ChainDown
