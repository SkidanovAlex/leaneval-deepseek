import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.N8.primesIn_half_card_le_pi0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# N8: the number of "bad" edges of an `ADI`-family is small

Let `A : ADIData k f c C X L P₁ P₂ ℓ` be a family of intervals `[x, x+L]`, `x ∈ A.fam`, carrying
edges `e = (x₁, x₂, p₁, p₂)` with `p₁, p₂` primes in `[P₁, 2P₁]` and
`|x₁ - (p₂/p₁) x₂| ≤ 100 L` (`A.geom`), the points of `A.fam` being `500 L`-separated
(`A.isFam`).  An edge is **bad** for a covering family `F : ℝ → Finset (… × ℕ × …)` (with at most
`K` elements per point, each carrying an integer `z.2.1 ≥ 1` with at most `B` prime factors) if one
of its primes divides one of those integers at one of its endpoints.

The main theorem says that the number of bad edges is at most
`16 · #A.fam · K · (B+1) · (π₀(P₁) + 1)`.

The counting is elementary but uses the geometry twice: an edge is *determined* by its two primes
together with one of its endpoints (a second edge with the same primes and the same left endpoint
would have its right endpoint within `400 L < 500 L` of the first one, contradicting the
separation of `A.fam`); hence, for a fixed point `x` and a fixed prime `p`, only edges with `p`
among their primes and `x` among their endpoints can be bad, and there are at most four per other
prime.

## Contents

* `mem_primesIn_iff` — membership in `primesIn a b`;
* `bad_edges_pi0_bound` — `#{primes in [P, 2P]} ≤ 4 (π₀ P + 1)`;
* `eq_of_fam_close` — two points of a family in the same short window coincide;
* `edge_eq_of_left`, `edge_eq_of_right` — uniqueness of an edge with prescribed endpoint and primes;
* `edges_at_prime_card_le` — the counting lemma above;
* `bad_edges_le` — the target.
-/

namespace Work.N8

open Finset

/-- Membership in `primesIn a b = {p prime : a ≤ p ≤ b}`. -/
lemma mem_primesIn_iff (a b : ℝ) (p : ℕ) :
    p ∈ Work.BMF.primesIn a b ↔ p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b := by
  rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    have hb0 : (0 : ℝ) ≤ b := by
      by_contra hb
      rw [not_le] at hb
      have hz : ⌊b⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      have hp2 : 2 ≤ p := hp.two_le
      omega
    have h1r : a ≤ ((p : ℕ) : ℝ) := le_trans (Nat.le_ceil a) (by exact_mod_cast h1)
    have h2r : ((p : ℕ) : ℝ) ≤ (⌊b⌋₊ : ℝ) := by exact_mod_cast h2
    exact ⟨hp, h1r, le_trans h2r (Nat.floor_le hb0)⟩
  · rintro ⟨hp, h1, h2⟩
    exact ⟨⟨Nat.ceil_le.mpr h1, Nat.le_floor h2⟩, hp⟩

/-- The number of primes in `[P, 2P]` is at most `4 (P / log P + 1)`, for `P ≥ 1`. -/
theorem bad_edges_pi0_bound (P : ℝ) (hP : 1 ≤ P) :
    ((Work.BMF.primesIn P (2 * P)).card : ℝ) ≤ 4 * (Work.BMF.pi0 P + 1) := by
  by_cases hPle : P ≤ 1
  · have hPeq : P = 1 := le_antisymm hPle hP
    subst hPeq
    have hsub : Work.BMF.primesIn 1 (2 * 1) ⊆ ({2} : Finset ℕ) := by
      intro p hp
      rw [mem_primesIn_iff] at hp
      have hp2 : p ≤ 2 := by exact_mod_cast hp.2.2
      have hp2' : 2 ≤ p := hp.1.two_le
      simp [le_antisymm hp2 hp2']
    have hcard : (Work.BMF.primesIn 1 (2 * 1)).card ≤ 1 := by
      have h := Finset.card_le_card hsub
      simpa using h
    have hc : ((Work.BMF.primesIn 1 (2 * 1)).card : ℝ) ≤ 1 := by exact_mod_cast hcard
    have hpi : Work.BMF.pi0 (1 : ℝ) = 0 := by simp [Work.BMF.pi0]
    rw [hpi, show (4 : ℝ) * (0 + 1) = 4 by norm_num]
    linarith
  · rw [not_le] at hPle
    have h2P : (1 : ℝ) < 2 * P := by linarith
    have hcard := primesIn_half_card_le_pi0 (2 * P) h2P
    have heq : Work.BMF.primesIn ((2 * P) / 2) (2 * P) = Work.BMF.primesIn P (2 * P) := by
      unfold Work.BMF.primesIn Work.BMF.natIcc
      rw [show (2 * P) / 2 = P by ring]
    rw [heq] at hcard
    have hstep : Work.BMF.pi0 (2 * P) ≤ 2 * Work.BMF.pi0 P := by
      have hlogP : 0 < Real.log P := Real.log_pos hPle
      have hlogmul : Real.log (2 * P) = Real.log 2 + Real.log P :=
        Real.log_mul (by norm_num) (by linarith)
      have hle : Real.log P ≤ Real.log 2 + Real.log P := by
        have := Real.log_pos one_lt_two
        linarith
      have h1' : (2 * P) / (Real.log 2 + Real.log P) ≤ (2 * P) / Real.log P :=
        div_le_div_of_nonneg_left (by linarith) hlogP hle
      unfold Work.BMF.pi0
      rw [hlogmul, show 2 * (P / Real.log P) = 2 * P / Real.log P by ring]
      exact h1'
    have hpos : 0 ≤ Work.BMF.pi0 P := by
      unfold Work.BMF.pi0
      exact div_nonneg (by linarith) (le_of_lt (Real.log_pos hPle))
    linarith

/-- **Separation.**  Two points of an `(X,L)`-family that both lie in a window
`|u - k t| ≤ 100 L` with `k > 2/5` coincide: otherwise they would be at distance at least `500 L`
but at most `200 L / k < 500 L`. -/
lemma eq_of_fam_close {S : Finset ℝ} {X L u k y y' : ℝ} (hS : Work.BMF.IsFam X L S)
    (hy : y ∈ S) (hy' : y' ∈ S) (hL : 0 < L) (hk : (2 : ℝ) / 5 < k)
    (h1 : |u - k * y| ≤ 100 * L) (h2 : |u - k * y'| ≤ 100 * L) : y = y' := by
  by_contra hne
  have hk0 : 0 < k := by linarith
  have hsep : 500 * L ≤ |y - y'| := hS.2 y hy y' hy' hne
  have htri : |(u - k * y) - (u - k * y')| ≤ |u - k * y| + |u - k * y'| := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [le_abs_self (u - k * y), neg_le_abs (u - k * y')],
           by linarith [le_abs_self (u - k * y'), neg_le_abs (u - k * y)]⟩
  have heq : |(u - k * y) - (u - k * y')| = k * |y - y'| := by
    rw [show (u - k * y) - (u - k * y') = k * (y' - y) by ring, abs_mul, abs_of_pos hk0,
      abs_sub_comm]
  have hkey : k * (500 * L) ≤ 200 * L := by
    have h3 : k * |y - y'| ≤ 200 * L := by rw [← heq]; linarith
    have h4 := mul_le_mul_of_nonneg_left hsep hk0.le
    linarith
  have hpos : 0 < L * (500 * k - 200) := mul_pos hL (by linarith)
  nlinarith [hkey, hpos]

/-- **Uniqueness of an edge with a prescribed left endpoint and prescribed primes.**
The right endpoint is pinned by the geometry `|x₁ - (p₂/p₁) x₂| ≤ 100 L` once `p₁, p₂` are fixed,
and the coefficient `p₂/p₁ ≥ 1/2 > 2/5` puts the two candidates in the same window. -/
lemma edge_eq_of_left {S : Finset ℝ} {E : Finset Work.BMF.Edge} {X L P₁ x : ℝ}
    {e e' : Work.BMF.Edge}
    (hS : Work.BMF.IsFam X L S) (hE : ∀ e ∈ E, Work.BMF.EdgeGeom S P₁ L e)
    (hL : 0 < L) (he : e ∈ E) (he' : e' ∈ E)
    (hp0 : (0 : ℝ) < e.p₁) (hq0 : (0 : ℝ) < e.p₂) (hpq : (e.p₁ : ℝ) ≤ 2 * e.p₂)
    (hx1 : e.x₁ = x) (hx1' : e'.x₁ = x) (hp1 : e.p₁ = e'.p₁) (hp2 : e.p₂ = e'.p₂) :
    e = e' := by
  have hwin := hE e he
  unfold Work.BMF.EdgeGeom at hwin
  obtain ⟨-, hx2mem, -, -, -, -, hwin⟩ := hwin
  have hwin' := hE e' he'
  unfold Work.BMF.EdgeGeom at hwin'
  obtain ⟨-, hx2mem', -, -, -, -, hwin'⟩ := hwin'
  rw [hx1] at hwin
  rw [hx1', ← hp2, ← hp1] at hwin'
  have hk : (2 : ℝ) / 5 < (e.p₂ : ℝ) / e.p₁ := by
    have hhalf : (1 : ℝ) / 2 ≤ (e.p₂ : ℝ) / e.p₁ := by
      rw [le_div_iff₀ hp0]
      linarith
    linarith
  have hxx : e.x₂ = e'.x₂ := eq_of_fam_close hS hx2mem hx2mem' hL hk hwin hwin'
  cases e
  cases e'
  simp_all

/-- **Uniqueness of an edge with a prescribed right endpoint and prescribed primes.**  Here the
geometry pins the left endpoint, and the coefficient attached to it is `1`. -/
lemma edge_eq_of_right {S : Finset ℝ} {E : Finset Work.BMF.Edge} {X L P₁ x : ℝ}
    {e e' : Work.BMF.Edge}
    (hS : Work.BMF.IsFam X L S) (hE : ∀ e ∈ E, Work.BMF.EdgeGeom S P₁ L e)
    (hL : 0 < L) (he : e ∈ E) (he' : e' ∈ E)
    (hx2 : e.x₂ = x) (hx2' : e'.x₂ = x) (hp1 : e.p₁ = e'.p₁) (hp2 : e.p₂ = e'.p₂) :
    e = e' := by
  have hwin := hE e he
  unfold Work.BMF.EdgeGeom at hwin
  obtain ⟨hx1mem, -, -, -, -, -, hwin⟩ := hwin
  have hwin' := hE e' he'
  unfold Work.BMF.EdgeGeom at hwin'
  obtain ⟨hx1mem', -, -, -, -, -, hwin'⟩ := hwin'
  rw [hx2] at hwin
  rw [hx2', ← hp2, ← hp1] at hwin'
  have hwin'' : |(e.p₂ : ℝ) / e.p₁ * x - 1 * e.x₁| ≤ 100 * L := by
    have h := hwin
    rw [abs_sub_comm] at h
    simpa using h
  have hwin''' : |(e.p₂ : ℝ) / e.p₁ * x - 1 * e'.x₁| ≤ 100 * L := by
    have h := hwin'
    rw [abs_sub_comm] at h
    simpa using h
  have hxx : e.x₁ = e'.x₁ :=
    eq_of_fam_close (u := (e.p₂ : ℝ) / e.p₁ * x) (k := 1) hS hx1mem hx1mem' hL
      (by norm_num) hwin'' hwin'''
  cases e
  cases e'
  simp_all

/-- **Counting lemma.**  For a point `x` of the family and a prime `p ∈ [P₁, 2P₁]`, the number of
edges having `x` as an endpoint and `p` among their two primes is at most
`4 · #{primes in [P₁, 2P₁]}`: split according to which endpoint is `x` and which prime is `p`; in
each class the *other* prime determines the edge, by `edge_eq_of_left` / `edge_eq_of_right`. -/
theorem edges_at_prime_card_le (k : ℕ) :
    ∀ (f : ℕ → ℂ) (c C X L P₁ P₂ : ℝ) (ℓ : ℕ) (A : Work.BMF.ADIData k f c C X L P₁ P₂ ℓ)
      (x : ℝ) (p : ℕ),
      1 ≤ L → 1 ≤ P₁ → x ∈ A.fam → p.Prime → P₁ ≤ (p : ℝ) → (p : ℝ) ≤ 2 * P₁ →
      ((A.edges.filter (fun e ↦ (e.x₁ = x ∧ e.p₁ = p) ∨ (e.x₁ = x ∧ e.p₂ = p) ∨
        (e.x₂ = x ∧ e.p₁ = p) ∨ (e.x₂ = x ∧ e.p₂ = p))).card)
        ≤ 4 * (Work.BMF.primesIn P₁ (2 * P₁)).card := by
  intro f c C X L P₁ P₂ ℓ A x p hL1 hP1 hxfam hp hp1 hp2
  classical
  have hL : 0 < L := by linarith
  set Q : Finset ℕ := Work.BMF.primesIn P₁ (2 * P₁) with hQ
  have hmemQ : ∀ q : ℕ, q ∈ Q ↔ q.Prime ∧ P₁ ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2 * P₁ := by
    intro q
    rw [hQ]
    exact mem_primesIn_iff P₁ (2 * P₁) q
  -- the components of `A.geom` that we use
  have hparts : ∀ {e : Work.BMF.Edge}, e ∈ A.edges →
      (0 : ℝ) < e.p₁ ∧ (0 : ℝ) < e.p₂ ∧ (e.p₁ : ℝ) ≤ 2 * e.p₂ ∧ e.p₂ ∈ Q ∧ e.p₁ ∈ Q := by
    intro e heE
    have hgeo := A.geom e heE
    unfold Work.BMF.EdgeGeom at hgeo
    obtain ⟨-, -, -, -, hp1in, hp2in, -⟩ := hgeo
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast hp1in.1.pos
    · exact_mod_cast hp2in.1.pos
    · linarith [hp1in.2.2, hp2in.2.1]
    · rw [hmemQ]; exact ⟨hp2in.1, hp2in.2.1, hp2in.2.2⟩
    · rw [hmemQ]; exact ⟨hp1in.1, hp1in.2.1, hp1in.2.2⟩
  set s1 : Finset Work.BMF.Edge := A.edges.filter (fun e => e.x₁ = x ∧ e.p₁ = p) with hs1
  set s2 : Finset Work.BMF.Edge := A.edges.filter (fun e => e.x₁ = x ∧ e.p₂ = p) with hs2
  set s3 : Finset Work.BMF.Edge := A.edges.filter (fun e => e.x₂ = x ∧ e.p₁ = p) with hs3
  set s4 : Finset Work.BMF.Edge := A.edges.filter (fun e => e.x₂ = x ∧ e.p₂ = p) with hs4
  have hs1c : s1.card ≤ Q.card := by
    rw [hs1]
    refine Finset.card_le_card_of_injOn (fun e => e.p₂) ?_ ?_
    · intro e he
      have he1 : e ∈ A.edges.filter (fun e => e.x₁ = x ∧ e.p₁ = p) := he
      exact (hparts (Finset.mem_filter.mp he1).1).2.2.2.1
    · intro e he e' he' heq
      have he1 : e ∈ A.edges.filter (fun e => e.x₁ = x ∧ e.p₁ = p) := he
      have he1' : e' ∈ A.edges.filter (fun e => e.x₁ = x ∧ e.p₁ = p) := he'
      obtain ⟨heE, hx, hpp⟩ := Finset.mem_filter.mp he1
      obtain ⟨heE', hx', hpp'⟩ := Finset.mem_filter.mp he1'
      obtain ⟨hp0, hq0, hpq, -, -⟩ := hparts heE
      exact edge_eq_of_left A.isFam A.geom hL heE heE' hp0 hq0 hpq hx hx'
        (by rw [hpp, hpp']) heq
  have hs2c : s2.card ≤ Q.card := by
    rw [hs2]
    refine Finset.card_le_card_of_injOn (fun e => e.p₁) ?_ ?_
    · intro e he
      have he1 : e ∈ A.edges.filter (fun e => e.x₁ = x ∧ e.p₂ = p) := he
      exact (hparts (Finset.mem_filter.mp he1).1).2.2.2.2
    · intro e he e' he' heq
      have he1 : e ∈ A.edges.filter (fun e => e.x₁ = x ∧ e.p₂ = p) := he
      have he1' : e' ∈ A.edges.filter (fun e => e.x₁ = x ∧ e.p₂ = p) := he'
      obtain ⟨heE, hx, hpp⟩ := Finset.mem_filter.mp he1
      obtain ⟨heE', hx', hpp'⟩ := Finset.mem_filter.mp he1'
      obtain ⟨hp0, hq0, hpq, -, -⟩ := hparts heE
      exact edge_eq_of_left A.isFam A.geom hL heE heE' hp0 hq0 hpq hx hx' heq
        (by rw [hpp, hpp'])
  have hs3c : s3.card ≤ Q.card := by
    rw [hs3]
    refine Finset.card_le_card_of_injOn (fun e => e.p₂) ?_ ?_
    · intro e he
      have he1 : e ∈ A.edges.filter (fun e => e.x₂ = x ∧ e.p₁ = p) := he
      exact (hparts (Finset.mem_filter.mp he1).1).2.2.2.1
    · intro e he e' he' heq
      have he1 : e ∈ A.edges.filter (fun e => e.x₂ = x ∧ e.p₁ = p) := he
      have he1' : e' ∈ A.edges.filter (fun e => e.x₂ = x ∧ e.p₁ = p) := he'
      obtain ⟨heE, hx, hpp⟩ := Finset.mem_filter.mp he1
      obtain ⟨heE', hx', hpp'⟩ := Finset.mem_filter.mp he1'
      exact edge_eq_of_right A.isFam A.geom hL heE heE' hx hx' (by rw [hpp, hpp']) heq
  have hs4c : s4.card ≤ Q.card := by
    rw [hs4]
    refine Finset.card_le_card_of_injOn (fun e => e.p₁) ?_ ?_
    · intro e he
      have he1 : e ∈ A.edges.filter (fun e => e.x₂ = x ∧ e.p₂ = p) := he
      exact (hparts (Finset.mem_filter.mp he1).1).2.2.2.2
    · intro e he e' he' heq
      have he1 : e ∈ A.edges.filter (fun e => e.x₂ = x ∧ e.p₂ = p) := he
      have he1' : e' ∈ A.edges.filter (fun e => e.x₂ = x ∧ e.p₂ = p) := he'
      obtain ⟨heE, hx, hpp⟩ := Finset.mem_filter.mp he1
      obtain ⟨heE', hx', hpp'⟩ := Finset.mem_filter.mp he1'
      exact edge_eq_of_right A.isFam A.geom hL heE heE' hx hx' heq (by rw [hpp, hpp'])
  have hsub : (A.edges.filter (fun e ↦ (e.x₁ = x ∧ e.p₁ = p) ∨ (e.x₁ = x ∧ e.p₂ = p) ∨
        (e.x₂ = x ∧ e.p₁ = p) ∨ (e.x₂ = x ∧ e.p₂ = p))) ⊆ ((s1 ∪ s2) ∪ (s3 ∪ s4)) := by
    intro e he
    have he1 : e ∈ A.edges.filter (fun e ↦ (e.x₁ = x ∧ e.p₁ = p) ∨ (e.x₁ = x ∧ e.p₂ = p) ∨
        (e.x₂ = x ∧ e.p₁ = p) ∨ (e.x₂ = x ∧ e.p₂ = p)) := he
    obtain ⟨heE, hd⟩ := Finset.mem_filter.mp he1
    rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl ?_)))
      rw [hs1, Finset.mem_filter]
      exact ⟨heE, h1, h2⟩
    · refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr ?_)))
      rw [hs2, Finset.mem_filter]
      exact ⟨heE, h1, h2⟩
    · refine Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl ?_)))
      rw [hs3, Finset.mem_filter]
      exact ⟨heE, h1, h2⟩
    · refine Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr ?_)))
      rw [hs4, Finset.mem_filter]
      exact ⟨heE, h1, h2⟩
  calc (A.edges.filter (fun e ↦ (e.x₁ = x ∧ e.p₁ = p) ∨ (e.x₁ = x ∧ e.p₂ = p) ∨
        (e.x₂ = x ∧ e.p₁ = p) ∨ (e.x₂ = x ∧ e.p₂ = p))).card
      ≤ ((s1 ∪ s2) ∪ (s3 ∪ s4)).card := Finset.card_le_card hsub
    _ ≤ (s1 ∪ s2).card + (s3 ∪ s4).card := Finset.card_union_le _ _
    _ ≤ (s1.card + s2.card) + (s3.card + s4.card) :=
        add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _)
    _ ≤ 4 * Q.card := by linarith [hs1c, hs2c, hs3c, hs4c]

theorem bad_edges_le (k : ℕ) :
    ∀ (f : ℕ → ℂ) (c C X L P₁ P₂ : ℝ) (ℓ : ℕ) (A : Work.BMF.ADIData k f c C X L P₁ P₂ ℓ)
      (F : ℝ → Finset (ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ)) (K : ℕ) (B : ℝ),
      1 ≤ L → 1 ≤ P₁ → 0 ≤ B →
      (∀ x, (F x).card ≤ K) →
      (∀ x, ∀ z ∈ F x, 1 ≤ z.2.1) →
      (∀ x, ∀ z ∈ F x, (((z.2.1).primeFactors.card : ℕ) : ℝ) ≤ B) →
      ((A.edges.filter (fun e ↦
        (∃ z ∈ F e.x₁, e.p₁ ∣ z.2.1 ∨ e.p₂ ∣ z.2.1) ∨
        (∃ z ∈ F e.x₂, e.p₁ ∣ z.2.1 ∨ e.p₂ ∣ z.2.1))).card : ℝ)
        ≤ 16 * (A.fam.card : ℝ) * (K : ℝ) * (B + 1) * (Work.BMF.pi0 P₁ + 1)
:= by
  intro f c C X L P₁ P₂ ℓ A F K B hL1 hP1 hB hKcard hpos hfac
  classical
  have hL : 0 < L := by linarith
  set Q : Finset ℕ := Work.BMF.primesIn P₁ (2 * P₁) with hQ
  have hmemQ : ∀ q : ℕ, q ∈ Q ↔ q.Prime ∧ P₁ ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2 * P₁ := by
    intro q
    rw [hQ]
    exact mem_primesIn_iff P₁ (2 * P₁) q
  set D : ℝ → Finset ℕ := fun x => Q.filter (fun p => ∃ z ∈ F x, p ∣ z.2.1) with hD
  set G : ℝ → ℕ → Finset Work.BMF.Edge := fun x p => A.edges.filter (fun e =>
      (e.x₁ = x ∧ e.p₁ = p) ∨ (e.x₁ = x ∧ e.p₂ = p) ∨
      (e.x₂ = x ∧ e.p₁ = p) ∨ (e.x₂ = x ∧ e.p₂ = p)) with hG
  -- ### every bad edge is covered by some `G x p`
  have hcover : (A.edges.filter (fun e ↦
        (∃ z ∈ F e.x₁, e.p₁ ∣ z.2.1 ∨ e.p₂ ∣ z.2.1) ∨
        (∃ z ∈ F e.x₂, e.p₁ ∣ z.2.1 ∨ e.p₂ ∣ z.2.1)))
      ⊆ A.fam.biUnion (fun x => (D x).biUnion (fun p => G x p)) := by
    intro e he
    have he1 : e ∈ A.edges.filter (fun e ↦
        (∃ z ∈ F e.x₁, e.p₁ ∣ z.2.1 ∨ e.p₂ ∣ z.2.1) ∨
        (∃ z ∈ F e.x₂, e.p₁ ∣ z.2.1 ∨ e.p₂ ∣ z.2.1)) := he
    obtain ⟨heE, hbad⟩ := Finset.mem_filter.mp he1
    have hgeo := A.geom e heE
    unfold Work.BMF.EdgeGeom at hgeo
    obtain ⟨hx1fam, hx2fam, -, -, hp1in, hp2in, -⟩ := hgeo
    have hp1Q : e.p₁ ∈ Q := by
      rw [hmemQ]; exact ⟨hp1in.1, hp1in.2.1, hp1in.2.2⟩
    have hp2Q : e.p₂ ∈ Q := by
      rw [hmemQ]; exact ⟨hp2in.1, hp2in.2.1, hp2in.2.2⟩
    rcases hbad with ⟨z, hz, hd⟩ | ⟨z, hz, hd⟩
    · refine Finset.mem_biUnion.mpr ⟨e.x₁, hx1fam, ?_⟩
      rcases hd with hd | hd
      · refine Finset.mem_biUnion.mpr ⟨e.p₁, ?_, ?_⟩
        · rw [hD, Finset.mem_filter]; exact ⟨hp1Q, z, hz, hd⟩
        · rw [hG, Finset.mem_filter]; exact ⟨heE, Or.inl ⟨rfl, rfl⟩⟩
      · refine Finset.mem_biUnion.mpr ⟨e.p₂, ?_, ?_⟩
        · rw [hD, Finset.mem_filter]; exact ⟨hp2Q, z, hz, hd⟩
        · rw [hG, Finset.mem_filter]; exact ⟨heE, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · refine Finset.mem_biUnion.mpr ⟨e.x₂, hx2fam, ?_⟩
      rcases hd with hd | hd
      · refine Finset.mem_biUnion.mpr ⟨e.p₁, ?_, ?_⟩
        · rw [hD, Finset.mem_filter]; exact ⟨hp1Q, z, hz, hd⟩
        · rw [hG, Finset.mem_filter]
          exact ⟨heE, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      · refine Finset.mem_biUnion.mpr ⟨e.p₂, ?_, ?_⟩
        · rw [hD, Finset.mem_filter]; exact ⟨hp2Q, z, hz, hd⟩
        · rw [hG, Finset.mem_filter]
          exact ⟨heE, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
  -- ### `D x` has at most `K (B+1)` elements
  have hDcard : ∀ x : ℝ, ((D x).card : ℝ) ≤ (K : ℝ) * (B + 1) := by
    intro x
    have hsub : D x ⊆ (F x).biUnion (fun z => (z.2.1).primeFactors) := by
      intro p hp
      have hp1 : p ∈ Q.filter (fun p => ∃ z ∈ F x, p ∣ z.2.1) := by simpa only [hD] using hp
      obtain ⟨hpQ, z, hz, hdvd⟩ := Finset.mem_filter.mp hp1
      refine Finset.mem_biUnion.mpr ⟨z, hz, ?_⟩
      rw [Nat.mem_primeFactors]
      have hz0 : z.2.1 ≠ 0 := by
        have := hpos x z hz
        omega
      exact ⟨((hmemQ p).mp hpQ).1, hdvd, hz0⟩
    have h1 : ((D x).card : ℝ)
        ≤ (((F x).biUnion (fun z => (z.2.1).primeFactors)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 : ((((F x).biUnion (fun z => (z.2.1).primeFactors)).card : ℕ) : ℝ)
        ≤ ∑ z ∈ F x, (((z.2.1).primeFactors.card : ℕ) : ℝ) := by
      have h := Finset.card_biUnion_le (s := F x) (t := fun z => (z.2.1).primeFactors)
      exact_mod_cast h
    have h3 : (∑ z ∈ F x, (((z.2.1).primeFactors.card : ℕ) : ℝ)) ≤ ∑ z ∈ F x, B :=
      Finset.sum_le_sum (fun z hz => hfac x z hz)
    have h4 : (∑ z ∈ F x, B) = ((F x).card : ℝ) * B := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h5 : ((F x).card : ℝ) * B ≤ (K : ℝ) * B :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hKcard x) hB
    have h6 : (K : ℝ) * B ≤ (K : ℝ) * (B + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg K)
    calc ((D x).card : ℝ) ≤ (((F x).biUnion (fun z => (z.2.1).primeFactors)).card : ℝ) := h1
      _ ≤ ∑ z ∈ F x, (((z.2.1).primeFactors.card : ℕ) : ℝ) := h2
      _ ≤ ∑ z ∈ F x, B := h3
      _ = ((F x).card : ℝ) * B := h4
      _ ≤ (K : ℝ) * B := h5
      _ ≤ (K : ℝ) * (B + 1) := h6
  -- ### `G x p` has at most `4 #Q` elements
  have hGcard : ∀ x ∈ A.fam, ∀ p ∈ Q, (G x p).card ≤ 4 * Q.card := by
    intro x hx p hpQ
    obtain ⟨hpP, hp1', hp2'⟩ := (hmemQ p).mp hpQ
    have h := edges_at_prime_card_le k f c C X L P₁ P₂ ℓ A x p hL1 hP1 hx hpP hp1' hp2'
    rw [hQ]
    exact h
  -- ### the double union bound, in `ℕ` then in `ℝ`
  have hsum_nat : (A.fam.biUnion (fun x => (D x).biUnion (fun p => G x p))).card ≤
      ∑ x ∈ A.fam, (D x).card * (4 * Q.card) := by
    calc (A.fam.biUnion (fun x => (D x).biUnion (fun p => G x p))).card
        ≤ ∑ x ∈ A.fam, ((D x).biUnion (fun p => G x p)).card := Finset.card_biUnion_le
      _ ≤ ∑ x ∈ A.fam, ∑ p ∈ D x, (G x p).card :=
          Finset.sum_le_sum (fun x hx => Finset.card_biUnion_le)
      _ ≤ ∑ x ∈ A.fam, ∑ p ∈ D x, 4 * Q.card := by
          refine Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun p hp => ?_))
          have hp1 : p ∈ Q.filter (fun p => ∃ z ∈ F x, p ∣ z.2.1) := by simpa only [hD] using hp
          exact hGcard x hx p (Finset.mem_filter.mp hp1).1
      _ = ∑ x ∈ A.fam, (D x).card * (4 * Q.card) := by
          refine Finset.sum_congr rfl (fun x hx => ?_)
          rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  have hsum_real : ((A.fam.biUnion (fun x => (D x).biUnion (fun p => G x p))).card : ℝ)
      ≤ ∑ x ∈ A.fam, (((D x).card * (4 * Q.card) : ℕ) : ℝ) := by
    exact_mod_cast hsum_nat
  have hsum_real2 : (∑ x ∈ A.fam, (((D x).card * (4 * Q.card) : ℕ) : ℝ))
      ≤ ∑ x ∈ A.fam, ((K : ℝ) * (B + 1)) * ((4 * Q.card : ℕ) : ℝ) := by
    refine Finset.sum_le_sum (fun x hx => ?_)
    have h4 : (0 : ℝ) ≤ ((4 * Q.card : ℕ) : ℝ) := by positivity
    calc (((D x).card * (4 * Q.card) : ℕ) : ℝ)
        = ((D x).card : ℝ) * ((4 * Q.card : ℕ) : ℝ) := Nat.cast_mul _ _
      _ ≤ ((K : ℝ) * (B + 1)) * ((4 * Q.card : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right (hDcard x) h4
  have hsum_real3 : (∑ x ∈ A.fam, ((K : ℝ) * (B + 1)) * ((4 * Q.card : ℕ) : ℝ))
      = (A.fam.card : ℝ) * ((K : ℝ) * (B + 1)) * ((4 * Q.card : ℕ) : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  have hQbound : ((4 * Q.card : ℕ) : ℝ) ≤ 16 * (Work.BMF.pi0 P₁ + 1) := by
    have h := bad_edges_pi0_bound P₁ hP1
    have hQc : (Q.card : ℝ) ≤ 4 * (Work.BMF.pi0 P₁ + 1) := h
    push_cast
    linarith
  calc ((A.edges.filter (fun e ↦
        (∃ z ∈ F e.x₁, e.p₁ ∣ z.2.1 ∨ e.p₂ ∣ z.2.1) ∨
        (∃ z ∈ F e.x₂, e.p₁ ∣ z.2.1 ∨ e.p₂ ∣ z.2.1))).card : ℝ)
      ≤ ((A.fam.biUnion (fun x => (D x).biUnion (fun p => G x p))).card : ℝ) :=
        by exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ x ∈ A.fam, (((D x).card * (4 * Q.card) : ℕ) : ℝ) := hsum_real
    _ ≤ ∑ x ∈ A.fam, ((K : ℝ) * (B + 1)) * ((4 * Q.card : ℕ) : ℝ) := hsum_real2
    _ = (A.fam.card : ℝ) * ((K : ℝ) * (B + 1)) * ((4 * Q.card : ℕ) : ℝ) := hsum_real3
    _ ≤ 16 * (A.fam.card : ℝ) * (K : ℝ) * (B + 1) * (Work.BMF.pi0 P₁ + 1) := by
        have hfac1 : 0 ≤ (A.fam.card : ℝ) * ((K : ℝ) * (B + 1)) :=
          mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (by linarith))
        calc (A.fam.card : ℝ) * ((K : ℝ) * (B + 1)) * ((4 * Q.card : ℕ) : ℝ)
            ≤ (A.fam.card : ℝ) * ((K : ℝ) * (B + 1)) * (16 * (Work.BMF.pi0 P₁ + 1)) :=
              mul_le_mul_of_nonneg_left hQbound hfac1
          _ = 16 * (A.fam.card : ℝ) * (K : ℝ) * (B + 1) * (Work.BMF.pi0 P₁ + 1) := by ring

end Work.N8
