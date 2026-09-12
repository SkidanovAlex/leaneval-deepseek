import Mathlib.Topology.Algebra.Polynomial

/-!
# Level chains of a real polynomial in a bracket gap

Helper lemmas for `Submission/CompQRoots.lean` (`lem:comp_Q_roots`).  If a
continuous (real-polynomial) function `f` takes value `≤ −D·u` at `a` and
`≥ D·u` at `b` (`a < b`), it attains every intermediate level `j·u` for
`j = 0..D` at points strictly increasing from `a` toward `b`
(`chain_up`); the mirror image, where the sign pattern is reversed, attains
the levels `(D−j)·u` at increasing points (`chain_down`).

**Note on `chain_down`.**  The statement below of `chain_down` corrects the
original draft: the upper-bound hypothesis `D·u ≤ f a` had to be made strict
(`D·u < f a`).  As drafted, the lemma is *false*: for `f x = 1 − x`,
`D = 1`, `u = 1`, `a = 0`, `b = 2` one has `f b = −1 ≤ −D·u` and
`D·u = f a = 1`, yet the top level `D·u` is attained only at the endpoint
`a` itself, so no point of `(a, b]` reaches it (verified by instantiating the
lemma in Lean: the hypotheses all hold while the conclusion forces a point of
`(0, 2]` where `1 − x = 1`, i.e. `x = 0`).  The strict form is the true mirror; the
degenerate endpoint case `f a = D·u` genuinely allows no chain in `(a, b]`.
-/

noncomputable section

open scoped Real
open Polynomial

namespace Submission.ChainLevels

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

/-- extend a strictly-increasing chain by one level: given a point where `p = k·u`,
find (if `k+1 ≤ D`) a point strictly to its right where `p = (k+1)·u`. -/
lemma exists_next_level (D k : ℕ) {u : ℝ} (hu : 0 < u) {p : Polynomial ℝ} {a x b : ℝ}
    (_hax : a < x) (hxb : x ≤ b) (hk1 : k + 1 ≤ D)
    (hpx : p.eval x = (k : ℝ) * u) (hhi : (D : ℝ) * u ≤ p.eval b) :
    ∃ y : ℝ, x < y ∧ y ≤ b ∧ p.eval y = ((k + 1 : ℕ) : ℝ) * u := by
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  have htar_le : ((k + 1 : ℕ) : ℝ) * u ≤ p.eval b := by
    calc
      ((k + 1 : ℕ) : ℝ) * u ≤ (D : ℝ) * u := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.succ_le_iff.mp hk1)) (le_of_lt hu)
      _ ≤ p.eval b := hhi
  by_cases hb : p.eval b = ((k + 1 : ℕ) : ℝ) * u
  · refine ⟨b, ?_, le_rfl, hb⟩
    exact lt_of_le_of_ne hxb (by
      intro hxb_eq
      have hp : p.eval b = (k : ℝ) * u := by simpa [hxb_eq] using hpx
      rw [hcast] at hb
      nlinarith)
  · have hstrict : ((k + 1 : ℕ) : ℝ) * u < p.eval b := lt_of_le_of_ne htar_le (by
      intro h
      exact hb h.symm)
    have hx_lt_b : x < b := lt_of_le_of_ne hxb (by
      intro hxb_eq
      have hp : p.eval b = (k : ℝ) * u := by simpa [hxb_eq] using hpx
      rw [hcast] at hstrict
      nlinarith)
    let q : Polynomial ℝ := p - Polynomial.C (((k + 1 : ℕ) : ℝ) * u)
    have hqx : q.eval x < 0 := by
      dsimp [q]
      rw [Polynomial.eval_sub, Polynomial.eval_C, hpx, hcast]
      nlinarith [hu]
    have hqb : 0 < q.eval b := by
      dsimp [q]
      rw [Polynomial.eval_sub, Polynomial.eval_C]
      exact sub_pos.mpr hstrict
    have hmul : q.eval x * q.eval b < 0 := mul_neg_of_neg_of_pos hqx hqb
    rcases exists_root_of_mul_neg (p := q) hx_lt_b hmul with ⟨c, hxc, hcb, hc0⟩
    refine ⟨c, hxc, le_of_lt hcb, ?_⟩
    dsimp [q] at hc0
    rw [Polynomial.eval_sub, Polynomial.eval_C] at hc0
    exact sub_eq_zero.mp hc0

/-- recursive chain: `chainPoints k` is the crossing of level `k·u`.  For `k+1 ≤ D`
the value at `k+1` is produced from the value at `k` by `exists_next_level`; for
larger `k` it is junk (`x0`). -/
private noncomputable def chainPoints (D : ℕ) (u : ℝ) (hu : 0 < u) (p : Polynomial ℝ)
    (a b : ℝ) (hhi : (D : ℝ) * u ≤ p.eval b) (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | k + 1 =>
      if h : k + 1 ≤ D ∧ a < chainPoints D u hu p a b hhi x0 k ∧
                chainPoints D u hu p a b hhi x0 k ≤ b ∧
                p.eval (chainPoints D u hu p a b hhi x0 k) = (k : ℝ) * u then
        Classical.choose (exists_next_level D k hu h.2.1 h.2.2.1 h.1 h.2.2.2 hhi)
      else x0

private lemma chainPoints_succ (D : ℕ) (u : ℝ) (hu : 0 < u) (p : Polynomial ℝ) (a b : ℝ)
    (hhi : (D : ℝ) * u ≤ p.eval b) (x0 : ℝ) {k : ℕ} (hk1 : k + 1 ≤ D)
    (h1 : a < chainPoints D u hu p a b hhi x0 k)
    (h2 : chainPoints D u hu p a b hhi x0 k ≤ b)
    (h3 : p.eval (chainPoints D u hu p a b hhi x0 k) = (k : ℝ) * u) :
    chainPoints D u hu p a b hhi x0 k < chainPoints D u hu p a b hhi x0 (k + 1) ∧
    chainPoints D u hu p a b hhi x0 (k + 1) ≤ b ∧
    p.eval (chainPoints D u hu p a b hhi x0 (k + 1)) = ((k + 1 : ℕ) : ℝ) * u := by
  have hc : k + 1 ≤ D ∧ a < chainPoints D u hu p a b hhi x0 k ∧
      chainPoints D u hu p a b hhi x0 k ≤ b ∧
      p.eval (chainPoints D u hu p a b hhi x0 k) = (k : ℝ) * u :=
    ⟨hk1, h1, h2, h3⟩
  rw [chainPoints]
  rw [dif_pos hc]
  rcases Classical.choose_spec (exists_next_level D k hu hc.2.1 hc.2.2.1 hc.1 hc.2.2.2 hhi) with ⟨hxy, hyb, hpy⟩
  exact ⟨hxy, hyb, hpy⟩

private lemma chainPoints_spec (D : ℕ) (u : ℝ) (hu : 0 < u) (p : Polynomial ℝ) (a b : ℝ)
    (hhi : (D : ℝ) * u ≤ p.eval b) (x0 : ℝ) (hx0a : a < x0) (hx0b : x0 ≤ b)
    (hx0 : p.eval x0 = (0 : ℝ) * u) :
    ∀ k : ℕ, k ≤ D → a < chainPoints D u hu p a b hhi x0 k ∧
      chainPoints D u hu p a b hhi x0 k ≤ b ∧
      p.eval (chainPoints D u hu p a b hhi x0 k) = (k : ℝ) * u := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [chainPoints, hx0a, hx0b, hx0]
  | succ k ih =>
      intro hk1
      have hk : k ≤ D := by omega
      rcases ih hk with ⟨h1, h2, h3⟩
      rcases chainPoints_succ D u hu p a b hhi x0 (by omega : k + 1 ≤ D) h1 h2 h3 with
        ⟨hlt, hb2, hp2⟩
      exact ⟨lt_trans h1 hlt, hb2, hp2⟩

private lemma chainPoints_mono (D : ℕ) (u : ℝ) (hu : 0 < u) (p : Polynomial ℝ) (a b : ℝ)
    (hhi : (D : ℝ) * u ≤ p.eval b) (x0 : ℝ) (hx0a : a < x0) (hx0b : x0 ≤ b)
    (hx0 : p.eval x0 = (0 : ℝ) * u) :
    ∀ k : ℕ, k + 1 ≤ D →
      chainPoints D u hu p a b hhi x0 k < chainPoints D u hu p a b hhi x0 (k + 1) := by
  intro k hk1
  rcases chainPoints_spec D u hu p a b hhi x0 hx0a hx0b hx0 k (by omega : k ≤ D) with ⟨h1, h2, h3⟩
  exact (chainPoints_succ D u hu p a b hhi x0 hk1 h1 h2 h3).1

/-- If `f(a) ≤ −D·u` and `D·u ≤ f(b)` with `a < b`, then for every level
`j = 0..D` there is a point `s j` with `f (s j) = j·u`; the `s j` are strictly
increasing and lie in `(a, b]`. -/
theorem chain_up {D : ℕ} (hD : 1 ≤ D) {u : ℝ} (hu : 0 < u) {p : Polynomial ℝ}
    {a b : ℝ} (hab : a < b) (hlo : p.eval a ≤ -((D : ℝ) * u)) (hhi : (D : ℝ) * u ≤ p.eval b) :
    ∃ s : Fin (D + 1) → ℝ,
      (∀ j : Fin (D + 1), a < s j ∧ s j ≤ b) ∧
      (∀ j : Fin (D + 1), p.eval (s j) = (j.val : ℝ) * u) ∧
      (∀ j : Fin D, s ⟨j.val, by omega⟩ < s ⟨j.val + 1, by omega⟩) := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hD)
  have hDu_pos : 0 < (D : ℝ) * u := mul_pos hDpos hu
  have hpa_lt : p.eval a < 0 := by
    have h : -((D : ℝ) * u) < 0 := by linarith
    exact lt_of_le_of_lt hlo h
  have hpb_pos : 0 < p.eval b := lt_of_lt_of_le hDu_pos hhi
  have hmul : p.eval a * p.eval b < 0 := mul_neg_of_neg_of_pos hpa_lt hpb_pos
  rcases exists_root_of_mul_neg hab hmul with ⟨x0, hx0a, hx0b_lt, hx0p⟩
  have hx0b : x0 ≤ b := le_of_lt hx0b_lt
  have hx0 : p.eval x0 = (0 : ℝ) * u := by simpa using hx0p
  refine ⟨fun j => chainPoints D u hu p a b hhi x0 j.val, ?_, ?_, ?_⟩
  · intro j
    exact ⟨(chainPoints_spec D u hu p a b hhi x0 hx0a hx0b hx0 j.val (by omega)).1,
      (chainPoints_spec D u hu p a b hhi x0 hx0a hx0b hx0 j.val (by omega)).2.1⟩
  · intro j
    exact (chainPoints_spec D u hu p a b hhi x0 hx0a hx0b hx0 j.val (by omega)).2.2
  · intro j
    exact chainPoints_mono D u hu p a b hhi x0 hx0a hx0b hx0 j.val (by omega : j.val + 1 ≤ D)


/-- extend a chain one step in the mirror (descending-level) direction: given a point
where `p = (D-k)·u`, find (if `k+1 ≤ D`) a point strictly to its right where
`p = (D-(k+1))·u`. -/
lemma exists_next_level_down (D k : ℕ) {u : ℝ} (hD : 1 ≤ D) (hu : 0 < u) {p : Polynomial ℝ}
    {a x b : ℝ} (_hax : a < x) (hxb : x ≤ b) (hk1 : k + 1 ≤ D)
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

/-- recursive mirror chain: `chainDownPoints k` crosses level `(D-k)·u`. -/
private noncomputable def chainDownPoints (D : ℕ) (u : ℝ) (hu : 0 < u) (hD : 1 ≤ D)
    (p : Polynomial ℝ) (a b : ℝ) (hlo : p.eval b ≤ -((D : ℝ) * u)) (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | k + 1 =>
      if h : k + 1 ≤ D ∧ a < chainDownPoints D u hu hD p a b hlo x0 k ∧
                chainDownPoints D u hu hD p a b hlo x0 k ≤ b ∧
                p.eval (chainDownPoints D u hu hD p a b hlo x0 k) =
                  ((D - k : ℕ) : ℝ) * u then
        Classical.choose (exists_next_level_down D k hD hu h.2.1 h.2.2.1 h.1 h.2.2.2 hlo)
      else x0

private lemma chainDownPoints_succ (D : ℕ) (u : ℝ) (hu : 0 < u) (hD : 1 ≤ D)
    (p : Polynomial ℝ) (a b : ℝ) (hlo : p.eval b ≤ -((D : ℝ) * u)) (x0 : ℝ) {k : ℕ}
    (hk1 : k + 1 ≤ D)
    (h1 : a < chainDownPoints D u hu hD p a b hlo x0 k)
    (h2 : chainDownPoints D u hu hD p a b hlo x0 k ≤ b)
    (h3 : p.eval (chainDownPoints D u hu hD p a b hlo x0 k) = ((D - k : ℕ) : ℝ) * u) :
    chainDownPoints D u hu hD p a b hlo x0 k <
        chainDownPoints D u hu hD p a b hlo x0 (k + 1) ∧
    chainDownPoints D u hu hD p a b hlo x0 (k + 1) ≤ b ∧
    p.eval (chainDownPoints D u hu hD p a b hlo x0 (k + 1)) =
      ((D - (k + 1) : ℕ) : ℝ) * u := by
  have hc : k + 1 ≤ D ∧ a < chainDownPoints D u hu hD p a b hlo x0 k ∧
      chainDownPoints D u hu hD p a b hlo x0 k ≤ b ∧
      p.eval (chainDownPoints D u hu hD p a b hlo x0 k) = ((D - k : ℕ) : ℝ) * u :=
    ⟨hk1, h1, h2, h3⟩
  rw [chainDownPoints]
  rw [dif_pos hc]
  rcases Classical.choose_spec (exists_next_level_down D k hD hu hc.2.1 hc.2.2.1 hc.1
    hc.2.2.2 hlo) with ⟨hxy, hyb, hpy⟩
  exact ⟨hxy, hyb, hpy⟩

private lemma chainDownPoints_spec (D : ℕ) (u : ℝ) (hu : 0 < u) (hD : 1 ≤ D)
    (p : Polynomial ℝ) (a b : ℝ) (hlo : p.eval b ≤ -((D : ℝ) * u)) (x0 : ℝ)
    (hx0a : a < x0) (hx0b : x0 ≤ b) (hx0 : p.eval x0 = ((D - 0 : ℕ) : ℝ) * u) :
    ∀ k : ℕ, k ≤ D → a < chainDownPoints D u hu hD p a b hlo x0 k ∧
      chainDownPoints D u hu hD p a b hlo x0 k ≤ b ∧
      p.eval (chainDownPoints D u hu hD p a b hlo x0 k) = ((D - k : ℕ) : ℝ) * u := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [chainDownPoints, hx0a, hx0b, hx0]
  | succ k ih =>
      intro hk1
      have hk : k ≤ D := by omega
      rcases ih hk with ⟨h1, h2, h3⟩
      rcases chainDownPoints_succ D u hu hD p a b hlo x0 (by omega : k + 1 ≤ D) h1 h2 h3 with
        ⟨hlt, hb2, hp2⟩
      exact ⟨lt_trans h1 hlt, hb2, hp2⟩

private lemma chainDownPoints_mono (D : ℕ) (u : ℝ) (hu : 0 < u) (hD : 1 ≤ D)
    (p : Polynomial ℝ) (a b : ℝ) (hlo : p.eval b ≤ -((D : ℝ) * u)) (x0 : ℝ)
    (hx0a : a < x0) (hx0b : x0 ≤ b) (hx0 : p.eval x0 = ((D - 0 : ℕ) : ℝ) * u) :
    ∀ k : ℕ, k + 1 ≤ D →
      chainDownPoints D u hu hD p a b hlo x0 k <
        chainDownPoints D u hu hD p a b hlo x0 (k + 1) := by
  intro k hk1
  rcases chainDownPoints_spec D u hu hD p a b hlo x0 hx0a hx0b hx0 k (by omega : k ≤ D)
    with ⟨h1, h2, h3⟩
  exact (chainDownPoints_succ D u hu hD p a b hlo x0 hk1 h1 h2 h3).1

/-- Mirror image of `chain_up`: if `f(b) ≤ −D·u` and `D·u < f(a)` with `a < b`,
then for every `j = 0..D` there is a point `s j` with `f (s j) = (D−j)·u`;
the `s j` are strictly increasing and lie in `(a, b]`.

NOTE (corrected statement): the hypothesis at the high end must be **strict**
(`D·u < f a`).  With the non-strict `D·u ≤ f a` the statement is false: for
`f x = 1 - x`, `D = 1`, `u = 1`, `a = 0`, `b = 2` one has `f b = -1 ≤ -D·u`
and `D·u = f a`, yet the top level `D·u` is attained only at `a` itself, so no
point of `(a, b]` reaches it. -/
theorem chain_down {D : ℕ} (hD : 1 ≤ D) {u : ℝ} (hu : 0 < u) {p : Polynomial ℝ}
    {a b : ℝ} (hab : a < b) (hlo : p.eval b ≤ -((D : ℝ) * u)) (hhi : (D : ℝ) * u < p.eval a) :
    ∃ s : Fin (D + 1) → ℝ,
      (∀ j : Fin (D + 1), a < s j ∧ s j ≤ b) ∧
      (∀ j : Fin (D + 1), p.eval (s j) = ((D - j.val : ℕ) : ℝ) * u) ∧
      (∀ j : Fin D, s ⟨j.val, by omega⟩ < s ⟨j.val + 1, by omega⟩) := by
  let q0 : Polynomial ℝ := p - Polynomial.C ((D : ℝ) * u)
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hD)
  have hDu_pos : 0 < (D : ℝ) * u := mul_pos hDpos hu
  have hq0a : 0 < q0.eval a := by
    dsimp [q0]
    rw [Polynomial.eval_sub, Polynomial.eval_C]
    exact sub_pos.mpr hhi
  have hq0b : q0.eval b < 0 := by
    dsimp [q0]
    rw [Polynomial.eval_sub, Polynomial.eval_C]
    have h : p.eval b < (D : ℝ) * u := lt_of_le_of_lt hlo (by linarith)
    exact sub_neg.mpr h
  have hmul : q0.eval a * q0.eval b < 0 := mul_neg_of_pos_of_neg hq0a hq0b
  rcases exists_root_of_mul_neg (p := q0) hab hmul with ⟨x0, hx0a, hx0b_lt, hx0q⟩
  have hx0b : x0 ≤ b := le_of_lt hx0b_lt
  have hx0p : p.eval x0 = (D : ℝ) * u := by
    dsimp [q0] at hx0q
    rw [Polynomial.eval_sub, Polynomial.eval_C] at hx0q
    exact sub_eq_zero.mp hx0q
  have hx0 : p.eval x0 = ((D - 0 : ℕ) : ℝ) * u := by
    simpa using hx0p
  refine ⟨fun j => chainDownPoints D u hu hD p a b hlo x0 j.val, ?_, ?_, ?_⟩
  · intro j
    exact ⟨(chainDownPoints_spec D u hu hD p a b hlo x0 hx0a hx0b hx0 j.val (by omega)).1,
      (chainDownPoints_spec D u hu hD p a b hlo x0 hx0a hx0b hx0 j.val (by omega)).2.1⟩
  · intro j
    exact (chainDownPoints_spec D u hu hD p a b hlo x0 hx0a hx0b hx0 j.val (by omega)).2.2
  · intro j
    exact chainDownPoints_mono D u hu hD p a b hlo x0 hx0a hx0b hx0 j.val (by omega : j.val + 1 ≤ D)

end Submission.ChainLevels
