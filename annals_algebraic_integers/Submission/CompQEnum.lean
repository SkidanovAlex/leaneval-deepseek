import Submission.CompQRoots

/-!
# Sorted enumeration of the roots of the complementary polynomial `Q`

Smith, adjust.tex, `lem:comp_Q_roots`: for all sufficiently large `r`, from the
`defn:comp_Q` construction data (a monic degree-`r` `T` with alternating signs
`0 < T·T̃` and `|T| ≥ κ^r/64` at the Chebyshev bracket points, `Q0 =
∏_{j'<D}(T − c_{j'})`, and a small perturbation `Q = Q1 + C N` with
`ε_t ∈ [0,2)`, `0 ≤ N ≤ 2·C2val⁻¹·κ^{Dr}`), the complementary polynomial `Q`
is squarefree, has every complex root real in the OPEN Serre interval, and its
`D·r` roots can be enumerated in strictly increasing order `β_1 < … < β_{Dr}`
with a gap `(gL_k, gR_k)` strictly inside the interval around each root,
`Q = ∏_k (X − C(β_k))`, and every root inside the interior Chebyshev window
`[extPoint (r+3) (r+1), extPoint (r+3) 1]`.

Proof route (all ingredients are public in `Submission.CompQRoots`):
* `gap_segments` gives, for each Chebyshev gap `i : Fin r`, a chain of `D+1`
  points `s` between the two bracket points with `Q(s_j)·Q(s_{j+1}) < 0` and
  big magnitudes `2·C2val⁻¹·κ^{Dr} ≤ |Q(s_j)|` for every `j : Fin D`;
* there are `r·D = Dr` such disjoint sign-change intervals (ordered: gap `i`
  lies to the LEFT of gap `i'` whenever `i' < i`), so `Q` has at least `Dr`
  distinct real roots there; since `Q` is monic of degree `Dr`, it has exactly
  one simple root per interval, no other roots, and is squarefree;
* enumerate the intervals in increasing order (gap `r−1` first, …, gap `0`
  last; within a gap, `j` ascending) to obtain `β : Fin (Dr) → ℝ` strictly
  increasing with `Q.eval (β k) = 0`; the gap endpoints `gL k`, `gR k` are the
  interval endpoints; `Q = ∏ (X − C(β_k))` follows from monicity + the
  factorization into `Dr` distinct real linear factors.
-/

noncomputable section

open ComplexOrder
open scoped Real BigOperators
open Polynomial

namespace Submission.CompQEnum

open Submission.SerreExample
open Submission.ChebSerre
open Submission.AdjustedCheb
open Submission.Bclps
open Submission.CompQNums
open Submission.CompQRoots

/-- The degree of the complementary polynomial: `Dr = D·r`. -/
abbrev Dr (r : ℕ) : ℕ := Bclps.Dconst * r


/-- value-preserving identification of `Fin (n * m)` with `Fin (m * n)`. -/
noncomputable def finMulComm (n m : ℕ) : Fin (n * m) ≃ Fin (m * n) where
  toFun i := ⟨i.1, by simpa [Nat.mul_comm] using i.2⟩
  invFun i := ⟨i.1, by simpa [Nat.mul_comm] using i.2⟩
  left_inv := by intro i; apply Fin.ext; rfl
  right_inv := by intro i; apply Fin.ext; rfl

/-- The sorted-position pairing `Fin (D·r) ≃ Fin r × Fin D`: `k` maps to the
interval (block from the left, segment within the block) at position `k.val`,
where block `i` starts at offset `D·i`; the value of the pair `(i, j)` is
`j + D·i`.  Blocks run from the leftmost gap (`gap r−1`) to the rightmost
(`gap 0`). -/
noncomputable def enumEquiv (r : ℕ) : (Fin r × Fin Bclps.Dconst) ≃ Fin (Bclps.Dconst * r) where
  toFun p :=
    ⟨p.2.val + Bclps.Dconst * p.1.val, by
      have hD : 0 < Bclps.Dconst := Dconst_pos
      have hj : p.2.val < Bclps.Dconst := p.2.isLt
      have hi : p.1.val < r := p.1.isLt
      have h1 : p.2.val + Bclps.Dconst * p.1.val < Bclps.Dconst + Bclps.Dconst * p.1.val :=
        Nat.add_lt_add_right hj (Bclps.Dconst * p.1.val)
      have hDd : Bclps.Dconst + Bclps.Dconst * p.1.val = Bclps.Dconst * (p.1.val + 1) := by
        rw [add_comm, ← Nat.mul_succ]
      have h2 : Bclps.Dconst * (p.1.val + 1) ≤ Bclps.Dconst * r :=
        Nat.mul_le_mul_left Bclps.Dconst (Nat.succ_le_of_lt hi)
      exact lt_of_lt_of_le (by simpa [hDd] using h1) h2⟩
  invFun k :=
    ⟨⟨k.val / Bclps.Dconst, by
        exact (Nat.div_lt_iff_lt_mul Dconst_pos).mpr (by simpa [Nat.mul_comm] using k.isLt)⟩,
      ⟨k.val % Bclps.Dconst, Nat.mod_lt k.val Dconst_pos⟩⟩
  left_inv := by
    intro p
    apply Prod.ext
    · apply Fin.eq_of_val_eq
      calc
        (p.2.val + Bclps.Dconst * p.1.val) / Bclps.Dconst = p.2.val / Bclps.Dconst + p.1.val :=
          Nat.add_mul_div_left _ _ Dconst_pos
        _ = 0 + p.1.val := by rw [Nat.div_eq_of_lt p.2.isLt]
        _ = p.1.val := Nat.zero_add _
    · apply Fin.eq_of_val_eq
      calc
        (p.2.val + Bclps.Dconst * p.1.val) % Bclps.Dconst = p.2.val % Bclps.Dconst :=
          Nat.add_mul_mod_self_left _ _ _
        _ = p.2.val := Nat.mod_eq_of_lt p.2.isLt
  right_inv := by
    intro k
    apply Fin.eq_of_val_eq
    simpa [Nat.add_comm, Nat.mul_comm] using Nat.mod_add_div k.val Bclps.Dconst

/-- positions of the sorted enumeration are ordered lexicographically:
`j + D·i < j' + D·i'` iff `i < i'` or (`i = i'` and `j < j'`). -/
lemma enum_pos_lt_iff {r : ℕ} : ∀ (p p' : Fin r × Fin Bclps.Dconst),
    (enumEquiv r p).val < (enumEquiv r p').val ↔
      p.1.val < p'.1.val ∨ (p.1.val = p'.1.val ∧ p.2.val < p'.2.val) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩
  simp only [enumEquiv]
  constructor
  · intro h
    have hle : i.val ≤ i'.val := by
      by_contra hnot
      have hi' : i'.val < i.val := Nat.lt_of_not_ge hnot
      have hz : (j.val : ℤ) + (Bclps.Dconst : ℤ) * i.val <
          (j'.val : ℤ) + (Bclps.Dconst : ℤ) * i'.val := by exact_mod_cast h
      have hjz : (j.val : ℤ) < (Bclps.Dconst : ℤ) := by exact_mod_cast j.isLt
      have hj'z : (j'.val : ℤ) < (Bclps.Dconst : ℤ) := by exact_mod_cast j'.isLt
      have hi'z : (i'.val : ℤ) < (i.val : ℤ) := by exact_mod_cast hi'
      nlinarith
    rcases lt_or_eq_of_le hle with hilt | heq
    · exact Or.inl hilt
    · right
      have hcomp : i' = i := Fin.eq_of_val_eq heq.symm
      subst i'
      constructor
      · rfl
      · exact Nat.lt_of_add_lt_add_right (n := Bclps.Dconst * i.val) (by simpa [add_comm, mul_comm] using h)
  · intro h
    rcases h with hilt | heq
    · have hj : j.val < Bclps.Dconst := j.isLt
      have h1 : j.val + Bclps.Dconst * i.val < Bclps.Dconst + Bclps.Dconst * i.val :=
        Nat.add_lt_add_right hj (Bclps.Dconst * i.val)
      have hDd : Bclps.Dconst + Bclps.Dconst * i.val = Bclps.Dconst * (i.val + 1) := by
        rw [add_comm, ← Nat.mul_succ]
      have h2 : Bclps.Dconst * (i.val + 1) ≤ Bclps.Dconst * i'.val :=
        Nat.mul_le_mul_left Bclps.Dconst (Nat.succ_le_of_lt hilt)
      have h3 : Bclps.Dconst * i'.val ≤ j'.val + Bclps.Dconst * i'.val := by
        rw [add_comm]
        exact Nat.le_add_right _ _
      exact lt_of_lt_of_le (lt_of_lt_of_le (by simpa [hDd] using h1) h2) h3
    · have hcomp : i' = i := Fin.eq_of_val_eq heq.1.symm
      subst i'
      exact Nat.add_lt_add_right heq.2 (Bclps.Dconst * i.val)

/-- left boundary of the interior Chebyshev window is strictly inside the open
Serre interval: `aSerre < extPoint (r+3) (r+1)`. -/
lemma aSerre_lt_extPoint_succ {r : ℕ} : aSerre < extPoint (r + 3) (r + 1) := by
  have hN : 1 ≤ r + 3 := by omega
  have hk : r + 1 < r + 3 := by omega
  have hroot : aSerre < rootPoint (r + 3) (r + 1) := (rootPoint_mem_Ioo hN hk).1
  have hint : rootPoint (r + 3) (r + 1) < extPoint (r + 3) (r + 1) :=
    (extPoint_rootPoint_interleave (N := r + 3) (k := r + 1) hN hk).2
  exact lt_trans hroot hint

/-- right boundary of the interior Chebyshev window is strictly inside the open
Serre interval: `extPoint (r+3) 1 < bSerre`. -/
lemma extPoint_one_lt_bSerre {r : ℕ} : extPoint (r + 3) 1 < bSerre := by
  have hN : 1 ≤ r + 3 := by omega
  have hant : extPoint (r + 3) 1 < extPoint (r + 3) 0 :=
    extPoint_antitone (N := r + 3) hN (by omega : 1 ≤ r + 3) (by omega : 0 < 1)
  rw [extPoint_zero] at hant
  exact hant

/-- inside a bracket `[x,y]` containing the single root `β` of `p`, with a
sign change at the ends, any two points `x < x' < β < y' < y` still have
opposite values. -/
lemma mul_neg_of_single_root {p : Polynomial ℝ} {x β y x' y' : ℝ}
    (hxx' : x < x') (hx'β : x' < β) (hβy' : β < y') (hy'y : y' < y)
    (hsgn : p.eval x * p.eval y < 0)
    (huniq : ∀ w : ℝ, x ≤ w → w ≤ y → p.eval w = 0 → w = β) :
    p.eval x' * p.eval y' < 0 := by
  have hsx : ∀ z : ℝ, x < z → z < β → 0 < p.eval z * p.eval x := by
    intro z hxz hzβ
    have hlt0 : ¬ p.eval z * p.eval x < 0 := by
      intro h
      have h' : p.eval x * p.eval z < 0 := by simpa [mul_comm] using h
      rcases (exists_root_of_mul_neg (p := p) hxz h') with ⟨w, hxw, hwz, hw0⟩
      have hwβ : w = β := huniq w (by linarith) (by linarith) hw0
      linarith
    have hne : p.eval z * p.eval x ≠ 0 := by
      intro h
      rcases (mul_eq_zero.mp h) with hz0 | hx0
      · have hzβeq : z = β := huniq z (by linarith) (by linarith) hz0
        linarith
      · have hxβeq : x = β := huniq x (by linarith) (by linarith) hx0
        linarith
    exact (lt_or_gt_of_ne hne).resolve_left hlt0
  have hsy : ∀ z : ℝ, β < z → z < y → 0 < p.eval z * p.eval y := by
    intro z hβz hzy
    have hlt0 : ¬ p.eval z * p.eval y < 0 := by
      intro h
      rcases (exists_root_of_mul_neg (p := p) hzy h) with ⟨w, hzw, hwy, hw0⟩
      have hwβ : w = β := huniq w (by linarith) (by linarith) hw0
      linarith
    have hne : p.eval z * p.eval y ≠ 0 := by
      intro h
      rcases (mul_eq_zero.mp h) with hz0 | hy0
      · have hzβeq : z = β := huniq z (by linarith) (by linarith) hz0
        linarith
      · have hyβeq : y = β := huniq y (by linarith) (le_refl y) hy0
        linarith
    exact (lt_or_gt_of_ne hne).resolve_left hlt0
  have hx'px : 0 < p.eval x' * p.eval x := hsx x' hxx' hx'β
  have hy'py : 0 < p.eval y' * p.eval y := hsy y' hβy' hy'y
  have hAB : 0 < (p.eval x' * p.eval x) * (p.eval y' * p.eval y) := mul_pos hx'px hy'py
  have hpos : 0 < (p.eval x' * p.eval y') * (p.eval x * p.eval y) := by
    have hrew : (p.eval x' * p.eval x) * (p.eval y' * p.eval y) =
        (p.eval x' * p.eval y') * (p.eval x * p.eval y) := by ring
    rwa [hrew] at hAB
  nlinarith [hsgn, hpos]

/-- Strengthened root structure used by `comp_q_roots_sorted`: all roots real in
the open Serre interval, sorted increasing enumeration `β : Fin (Dr) → ℝ`
(with `Dr = D·r`) of all `Dr` roots, each with a sign-changing gap `(gL, gR)`
strictly inside the interval, roots inside the interior Chebyshev window
`[extPoint (r+3) (r+1), extPoint (r+3) 1]`, and `Q = ∏ (X − C(β_k))`. -/
lemma comp_q_roots_sorted_core (r : ℕ) (hr2 : 2 ≤ r)
    (h6r : (4 : ℝ) / ((kappaC - 1) * kappaC ^ (r - 1)) < 6 * C2val⁻¹)
    (h4r : (4 : ℝ) / ((kappaC - 1) * kappaC ^ (r - 1)) < 4 * C2val⁻¹)
    {T Q0 Q1 Q : Polynomial ℝ} (eps : ℕ → ℝ) (N : ℝ)
    (hTmon : T.Monic) (hTdeg : T.natDegree = r)
    (hTsgn : ∀ i : Fin (r + 1),
      0 < T.eval (bracketPoint r i) * (prunedPoly r).eval (bracketPoint r i))
    (hTmag : ∀ i : Fin (r + 1), |T.eval (bracketPoint r i)| ≥ kappaC ^ r / 64)
    (hQ0 : Q0 = ∏ j' ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j')))
    (hQ1 : Q1 = Q0 + (∑ t ∈ Finset.Icc 1 (d r), Polynomial.C (eps t) * Bclps.auxPoly t))
    (hQ : Q = Q1 + Polynomial.C N)
    (hEps : ∀ t : ℕ, t ∈ Finset.Icc 1 (d r) → 0 ≤ eps t ∧ eps t < 2)
    (hN0 : 0 ≤ N) (hNle : N ≤ 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r)) :
    Squarefree Q ∧
    (∀ z : ℂ, Polynomial.aeval z Q = 0 → (aSerre : ℂ) < z ∧ z < (bSerre : ℂ)) ∧
    (∃ β gL gR : Fin (Bclps.Dconst * r) → ℝ,
      (∀ k : Fin (Bclps.Dconst * r),
        aSerre < gL k ∧ gL k < β k ∧ β k < gR k ∧ gR k < bSerre) ∧
      (∀ k : Fin (Bclps.Dconst * r), Q.eval (β k) = 0) ∧
      (∀ k : Fin (Bclps.Dconst * r), Q.eval (gL k) * Q.eval (gR k) < 0) ∧
      (∀ k : Fin (Bclps.Dconst * r),
        extPoint (r + 3) (r + 1) ≤ β k ∧ β k ≤ extPoint (r + 3) 1) ∧
      (∀ i j : Fin (Bclps.Dconst * r), i.val < j.val → gR i < gL j) ∧
      (∀ i j : Fin (Bclps.Dconst * r), i.val < j.val → β i < β j) ∧
      (∀ k : Fin (Bclps.Dconst * r), aSerre < β k ∧ β k < bSerre) ∧
      Q = ∏ k : Fin (Bclps.Dconst * r), (Polynomial.X - Polynomial.C (β k))) := by
  classical
  let D : ℕ := Bclps.Dconst
  have hD : 1 ≤ D := by dsimp [D]; exact Dconst_pos
  have hD0 : 0 < D := by omega
  have hDreal : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD0
  -- pointwise closeness of Q and Q0 on the interval
  have hepsAbs : ∀ t : ℕ, t ∈ Finset.Icc 1 (d r) → |eps t| < 2 := by
    intro t ht
    have h := hEps t ht
    rw [abs_of_nonneg h.1]
    exact h.2
  have hpert : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
      |Q.eval x - Q0.eval x| ≤ kappaC ^ (Bclps.Dconst * r) *
        (4 / ((kappaC - 1) * kappaC ^ (r - 1)) + 2 * C2val⁻¹) := by
    intro x hx
    exact Submission.CompQpert.pert_bound_total r (eps := eps) (N := N) hQ1 hQ hepsAbs hN0 hNle hx
  have hclose8 : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → |Q.eval x - Q0.eval x| <
      8 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
    intro x hx
    have h := hpert x hx
    have hsum : 4 / ((kappaC - 1) * kappaC ^ (r - 1)) + 2 * C2val⁻¹ < 8 * C2val⁻¹ := by
      nlinarith [h6r]
    have hpos : 0 < kappaC ^ (Bclps.Dconst * r) := pow_pos kappaC_pos _
    have hlt : kappaC ^ (Bclps.Dconst * r) *
          (4 / ((kappaC - 1) * kappaC ^ (r - 1)) + 2 * C2val⁻¹) <
        8 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
      nlinarith [mul_lt_mul_of_pos_right hsum hpos, hpos]
    exact lt_of_le_of_lt h hlt
  have hclose6 : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → |Q.eval x - Q0.eval x| <
      6 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
    intro x hx
    have h := hpert x hx
    have hsum : 4 / ((kappaC - 1) * kappaC ^ (r - 1)) + 2 * C2val⁻¹ < 6 * C2val⁻¹ := by
      nlinarith [h4r]
    have hpos : 0 < kappaC ^ (Bclps.Dconst * r) := pow_pos kappaC_pos _
    have hlt : kappaC ^ (Bclps.Dconst * r) *
          (4 / ((kappaC - 1) * kappaC ^ (r - 1)) + 2 * C2val⁻¹) <
        6 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
      nlinarith [mul_lt_mul_of_pos_right hsum hpos, hpos]
    exact lt_of_le_of_lt h hlt
  -- per-gap chains
  have hgap : ∀ i : Fin r, ∃ s : Fin (D + 1) → ℝ,
      (∀ j : Fin (D + 1), bracketPoint r ⟨i.val + 1, by omega⟩ ≤ s j ∧
          s j ≤ bracketPoint r ⟨i.val, by omega⟩) ∧
      (∀ j : Fin D, s ⟨j.val, by omega⟩ < s ⟨j.val + 1, by omega⟩) ∧
      (∀ j : Fin D, Q.eval (s ⟨j.val, by omega⟩) * Q.eval (s ⟨j.val + 1, by omega⟩) < 0 ∧
        2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤ |Q.eval (s ⟨j.val, by omega⟩)| ∧
        2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤ |Q.eval (s ⟨j.val + 1, by omega⟩)|) := by
    intro i
    rcases (gap_segments r hr2 hQ0 hTsgn hTmag hclose8 hclose6 i) with ⟨s, hs1, hs2, hs3⟩
    refine ⟨s, hs1, hs2, ?_⟩
    intro j
    have h3 := hs3 j
    exact ⟨h3.1, h3.2.1, h3.2.2⟩
  let sfunc : Fin r → Fin (D + 1) → ℝ := fun i => Classical.choose (hgap i)
  have sfunc_spec : ∀ i : Fin r,
      (∀ j : Fin (D + 1), bracketPoint r ⟨i.val + 1, by omega⟩ ≤ sfunc i j ∧
          sfunc i j ≤ bracketPoint r ⟨i.val, by omega⟩) ∧
      (∀ j : Fin D, sfunc i ⟨j.val, by omega⟩ < sfunc i ⟨j.val + 1, by omega⟩) ∧
      (∀ j : Fin D, Q.eval (sfunc i ⟨j.val, by omega⟩) * Q.eval (sfunc i ⟨j.val + 1, by omega⟩) < 0 ∧
        2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤ |Q.eval (sfunc i ⟨j.val, by omega⟩)| ∧
        2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤ |Q.eval (sfunc i ⟨j.val + 1, by omega⟩)|) :=
    fun i => Classical.choose_spec (hgap i)
  -- the interval index set: (block from the left, segment), position value j + D*i
  let τ : Type := Fin r × Fin D
  let gapOf : Fin r → Fin r := fun i => ⟨r - 1 - i.val, by omega⟩
  let xfun : Fin r → Fin D → ℝ := fun i j => sfunc (gapOf i) ⟨j.val, by omega⟩
  let yfun : Fin r → Fin D → ℝ := fun i j => sfunc (gapOf i) ⟨j.val + 1, by omega⟩
  let xx : τ → ℝ := fun p => xfun p.1 p.2
  let yy : τ → ℝ := fun p => yfun p.1 p.2
  -- monic degree Dr
  have hdeg : Q0.Monic ∧ Q0.natDegree = Bclps.Dconst * r ∧ Q.Monic ∧ Q.natDegree = Bclps.Dconst * r :=
    Submission.CompQdeg.monic_degree r (by omega : 1 ≤ r) eps N hTmon hTdeg hQ0 hQ1 hQ
  have hGmon : Q.Monic := hdeg.2.2.1
  have hQdegDr : Q.natDegree = Bclps.Dconst * r := hdeg.2.2.2
  have hGdeg : Q.natDegree = Fintype.card τ := by
    dsimp [τ]
    rw [hQdegDr]
    calc
      (Bclps.Dconst * r) = r * Bclps.Dconst := by rw [mul_comm]
      _ = Fintype.card (Fin r × Fin D) := by
        dsimp [D]
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  -- hypotheses of the splitting lemma
  have hxy : ∀ p : τ, xx p < yy p := by
    intro p
    rcases p with ⟨i, j⟩
    dsimp [τ, xx, yy, xfun, yfun]
    exact (sfunc_spec (gapOf i)).2.1 j
  have hsign : ∀ p : τ, Q.eval (xx p) * Q.eval (yy p) < 0 := by
    intro p
    rcases p with ⟨i, j⟩
    dsimp [τ, xx, yy, xfun, yfun]
    exact ((sfunc_spec (gapOf i)).2.2 j).1
  have hIcc : ∀ p : τ, aSerre ≤ xx p ∧ yy p ≤ bSerre := by
    intro p
    rcases p with ⟨i, j⟩
    dsimp [τ, xx, yy, xfun, yfun]
    have hx : aSerre ≤ sfunc (gapOf i) ⟨j.val, by omega⟩ :=
      le_trans (bracketPoint_mem_Icc r ⟨(gapOf i).val + 1, by omega⟩).1
        ((sfunc_spec (gapOf i)).1 ⟨j.val, by omega⟩).1
    have hy : sfunc (gapOf i) ⟨j.val + 1, by omega⟩ ≤ bSerre :=
      le_trans ((sfunc_spec (gapOf i)).1 ⟨j.val + 1, by omega⟩).2
        (bracketPoint_mem_Icc r ⟨(gapOf i).val, by omega⟩).2
    exact ⟨hx, hy⟩
  have hK : ∀ p : τ, 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤ |Q.eval (xx p)| ∧
      2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤ |Q.eval (yy p)| := by
    intro p
    rcases p with ⟨i, j⟩
    dsimp [τ, xx, yy, xfun, yfun]
    exact ⟨((sfunc_spec (gapOf i)).2.2 j).2.1, ((sfunc_spec (gapOf i)).2.2 j).2.2⟩
  -- interval separation for ordered positions
  have hsepOrd : ∀ p p' : τ, (enumEquiv r p).val < (enumEquiv r p').val → yy p ≤ xx p' := by
    intro p p' hpos
    rcases p with ⟨i, j⟩
    rcases p' with ⟨i', j'⟩
    have hlex := (enum_pos_lt_iff (r := r) (i, j) (i', j')).1 (by simpa using hpos)
    rcases hlex with hilt | heq
    · -- different gaps: gap(i) is left of gap(i')
      dsimp [τ, xx, yy, xfun, yfun]
      have h1 : sfunc (gapOf i) ⟨j.val + 1, by omega⟩ ≤ bracketPoint r ⟨(gapOf i).val, by omega⟩ :=
        ((sfunc_spec (gapOf i)).1 ⟨j.val + 1, by omega⟩).2
      have h2 : bracketPoint r ⟨(gapOf i).val, by omega⟩ ≤
          bracketPoint r ⟨(gapOf i').val + 1, by omega⟩ := by
        apply bracketPoint_antitone_le r
        dsimp [gapOf]
        have hilt' : i.val + 1 ≤ i'.val := Nat.succ_le_of_lt hilt
        have hi'le : i'.val ≤ r - 1 := Nat.le_pred_of_lt i'.isLt
        omega
      have h3 : bracketPoint r ⟨(gapOf i').val + 1, by omega⟩ ≤
          sfunc (gapOf i') ⟨j'.val, by omega⟩ :=
        ((sfunc_spec (gapOf i')).1 ⟨j'.val, by omega⟩).1
      exact le_trans h1 (le_trans h2 h3)
    · -- same gap
      have hEq : i' = i := Fin.eq_of_val_eq heq.1.symm
      subst i'
      have hj : j.val < j'.val := heq.2
      dsimp [τ, xx, yy, xfun, yfun]
      exact chain_mono_nat (N := D) (s := sfunc (gapOf i)) (sfunc_spec (gapOf i)).2.1
        (j.val + 1) (j'.val) (by omega) (by omega)
  have hsep : ∀ ⦃p p' : τ⦄, p ≠ p' → yy p ≤ xx p' ∨ yy p' ≤ xx p := by
    intro p p' hne
    by_cases hlt : (enumEquiv r p).val < (enumEquiv r p').val
    · exact Or.inl (hsepOrd p p' hlt)
    · right
      have hvne : (enumEquiv r p).val ≠ (enumEquiv r p').val := by
        intro hv
        have hEq : p = p' := (enumEquiv r).injective (Fin.eq_of_val_eq hv)
        exact hne hEq
      have hgt : (enumEquiv r p').val < (enumEquiv r p).val :=
        (lt_or_gt_of_ne hvne).resolve_left hlt
      exact hsepOrd p' p hgt
  -- invoke the generic splitting lemma
  rcases (split_of_segments (G := Q) hGmon hGdeg hxy hsign hIcc hK hsep) with
    ⟨rho, hrho1, hfacQ, hclassQ, hbracket⟩
  -- geometry: the extreme bracket points are strictly inside the open interval
  have hbr : aSerre < bracketPoint r ⟨r, by omega⟩ := by
    dsimp [bracketPoint]
    exact aSerre_lt_extPoint_succ (r := r)
  have hb0 : bracketPoint r ⟨0, by omega⟩ < bSerre := by
    dsimp [bracketPoint]
    exact extPoint_one_lt_bSerre (r := r)
  -- per-p bounds of the chain points relative to the window
  have hxxWin : ∀ p : τ, bracketPoint r ⟨r, by omega⟩ ≤ xx p := by
    intro p
    rcases p with ⟨i, j⟩
    dsimp [τ, xx, yy, xfun, yfun]
    calc
      bracketPoint r ⟨r, by omega⟩ ≤ bracketPoint r ⟨(gapOf i).val + 1, by omega⟩ := by
        apply bracketPoint_antitone_le r
        dsimp [gapOf]
        omega
      _ ≤ sfunc (gapOf i) ⟨j.val, by omega⟩ := ((sfunc_spec (gapOf i)).1 ⟨j.val, by omega⟩).1
  have hyyWin : ∀ p : τ, yy p ≤ bracketPoint r ⟨0, by omega⟩ := by
    intro p
    rcases p with ⟨i, j⟩
    dsimp [τ, xx, yy, xfun, yfun]
    calc
      sfunc (gapOf i) ⟨j.val + 1, by omega⟩ ≤ bracketPoint r ⟨(gapOf i).val, by omega⟩ :=
        ((sfunc_spec (gapOf i)).1 ⟨j.val + 1, by omega⟩).2
      _ ≤ bracketPoint r ⟨0, by omega⟩ := by
        apply bracketPoint_antitone_le r
        dsimp [gapOf]
        omega
  -- the sorted enumeration, transported to Fin (D*r)
  let β : Fin (Bclps.Dconst * r) → ℝ := fun k => rho ((enumEquiv r).symm k)
  have hβint : ∀ k : Fin (Bclps.Dconst * r), xx ((enumEquiv r).symm k) < β k ∧
      β k < yy ((enumEquiv r).symm k) := by
    intro k
    dsimp [β]
    exact ⟨(hrho1 ((enumEquiv r).symm k)).1, (hrho1 ((enumEquiv r).symm k)).2.1⟩
  have hβroot : ∀ k : Fin (Bclps.Dconst * r), Q.eval (β k) = 0 := by
    intro k
    dsimp [β]
    exact (hrho1 ((enumEquiv r).symm k)).2.2
  have hβmono : ∀ i j : Fin (Bclps.Dconst * r), i.val < j.val → β i < β j := by
    intro k k' hkk'
    have hpos : (enumEquiv r ((enumEquiv r).symm k)).val <
        (enumEquiv r ((enumEquiv r).symm k')).val := by
      simpa using hkk'
    have hsepkk : yy ((enumEquiv r).symm k) ≤ xx ((enumEquiv r).symm k') :=
      hsepOrd ((enumEquiv r).symm k) ((enumEquiv r).symm k') hpos
    calc
      β k < yy ((enumEquiv r).symm k) := (hβint k).2
      _ ≤ xx ((enumEquiv r).symm k') := hsepkk
      _ < β k' := (hβint k').1
  let gL : Fin (Bclps.Dconst * r) → ℝ := fun k =>
    (xx ((enumEquiv r).symm k) + β k) / 2
  let gR : Fin (Bclps.Dconst * r) → ℝ := fun k =>
    (β k + yy ((enumEquiv r).symm k)) / 2
  -- everything is strictly inside the open interval and the window
  have hLβ : ∀ k : Fin (Bclps.Dconst * r),
      aSerre < xx ((enumEquiv r).symm k) ∧ xx ((enumEquiv r).symm k) < β k := by
    intro k
    have hw := hxxWin ((enumEquiv r).symm k)
    have hw' : aSerre < xx ((enumEquiv r).symm k) := lt_of_lt_of_le hbr hw
    exact ⟨hw', (hβint k).1⟩
  have hβR : ∀ k : Fin (Bclps.Dconst * r),
      β k < yy ((enumEquiv r).symm k) ∧ yy ((enumEquiv r).symm k) < bSerre := by
    intro k
    have hw := hyyWin ((enumEquiv r).symm k)
    have hw' : yy ((enumEquiv r).symm k) < bSerre := lt_of_le_of_lt hw hb0
    exact ⟨(hβint k).2, hw'⟩
  have hgL : ∀ k : Fin (Bclps.Dconst * r), aSerre < gL k ∧ gL k < β k := by
    intro k
    dsimp [gL]
    have hL := (hLβ k).1
    have hLb := (hLβ k).2
    constructor
    · have hmid : xx ((enumEquiv r).symm k) < (xx ((enumEquiv r).symm k) + β k) / 2 := by
        nlinarith [hLb]
      exact lt_trans hL hmid
    · nlinarith [hLb]
  have hgR : ∀ k : Fin (Bclps.Dconst * r), β k < gR k ∧ gR k < bSerre := by
    intro k
    dsimp [gR]
    have hRb := (hβR k).1
    have hR := (hβR k).2
    constructor
    · nlinarith [hRb]
    · have hmid : (β k + yy ((enumEquiv r).symm k)) / 2 < yy ((enumEquiv r).symm k) := by
        nlinarith [hRb]
      exact lt_trans hmid hR
  have hsignG : ∀ k : Fin (Bclps.Dconst * r), Q.eval (gL k) * Q.eval (gR k) < 0 := by
    intro k
    let p := (enumEquiv r).symm k
    have hsgn' : Q.eval (xx p) * Q.eval (yy p) < 0 := hsign p
    have hb' : ∀ w : ℝ, xx p ≤ w → w ≤ yy p → Q.eval w = 0 → w = rho p := hbracket p
    have hroot' : rho p = β k := by
        simp [β, p]
    have hx' : xx p < gL k := by
      dsimp [gL, p]
      nlinarith [(hβint k).1]
    have hx'β : gL k < β k := by
      dsimp [gL, p]
      nlinarith [(hβint k).1]
    have hβy' : β k < gR k := by
      dsimp [gR, p]
      nlinarith [(hβint k).2]
    have hy' : gR k < yy p := by
      dsimp [gR, p]
      nlinarith [(hβint k).2]
    exact mul_neg_of_single_root (p := Q)
      (x := xx p) (β := β k) (y := yy p) (x' := gL k) (y' := gR k)
      hx' hx'β hβy' hy' hsgn' (by
        intro w hxw hyw hw0
        have hwβ : w = rho p := hb' w hxw hyw hw0
        rw [hroot'] at hwβ
        exact hwβ)
  have hgRltgL : ∀ i j : Fin (Bclps.Dconst * r), i.val < j.val → gR i < gL j := by
    intro k k' hkk'
    have hb : β k < β k' := hβmono k k' hkk'
    have hsepkk : yy ((enumEquiv r).symm k) ≤ xx ((enumEquiv r).symm k') :=
      hsepOrd ((enumEquiv r).symm k) ((enumEquiv r).symm k') (by simpa using hkk')
    dsimp [gR, gL]
    nlinarith [hb, hsepkk]
  have hβWin : ∀ k : Fin (Bclps.Dconst * r),
      extPoint (r + 3) (r + 1) ≤ β k ∧ β k ≤ extPoint (r + 3) 1 := by
    intro k
    have hwL := hxxWin ((enumEquiv r).symm k)
    have hwR := hyyWin ((enumEquiv r).symm k)
    have hL : extPoint (r + 3) (r + 1) ≤ β k := by
      dsimp [bracketPoint] at hwL
      exact le_of_lt (lt_of_le_of_lt hwL (hβint k).1)
    have hR : β k ≤ extPoint (r + 3) 1 := by
      dsimp [bracketPoint] at hwR
      exact le_of_lt (lt_of_lt_of_le (hβint k).2 hwR)
    exact ⟨hL, hR⟩
  have hβSerre : ∀ k : Fin (Bclps.Dconst * r), aSerre < β k ∧ β k < bSerre := by
    intro k
    exact ⟨lt_trans (hLβ k).1 (hβint k).1, lt_trans (hβint k).2 (hβR k).2⟩
  -- factorization over Fin (Dr)
  have hfac : Q = ∏ k : Fin (Bclps.Dconst * r), (Polynomial.X - Polynomial.C (β k)) := by
    rw [hfacQ]
    rw [← Equiv.prod_comp (enumEquiv r).symm (fun p : τ => Polynomial.X - Polynomial.C (rho p))]
  -- injectivity of β, squarefree
  have hβinj : Function.Injective β := by
    intro k k' hkk'
    by_contra hne
    have hv : k.val ≠ k'.val := by
      intro hv'
      exact hne (Fin.eq_of_val_eq hv')
    have hlt : k.val < k'.val ∨ k'.val < k.val := lt_or_gt_of_ne hv
    rcases hlt with hlt | hgt
    · have h := hβmono k k' hlt
      rw [hkk'] at h
      linarith
    · have h := hβmono k' k hgt
      rw [hkk'] at h
      linarith
  have hsepQ : Q.Separable := by
    rw [hfac]
    exact (separable_prod_X_sub_C_iff (F := ℝ) (f := β)).mpr hβinj
  have hsqfree : Squarefree Q := hsepQ.squarefree
  -- complex roots lie in the open Serre interval
  have hrootC : ∀ z : ℂ, Polynomial.aeval z Q = 0 → (aSerre : ℂ) < z ∧ z < (bSerre : ℂ) := by
    intro z hz
    have hzfac : (Polynomial.aeval z) (∏ k : Fin (Bclps.Dconst * r),
        (Polynomial.X - Polynomial.C (β k))) = 0 := by
      simpa [hfac] using hz
    have hprod : (∏ k : Fin (Bclps.Dconst * r), (z - (β k : ℂ))) = 0 := by
      simpa using hzfac
    rw [show (∏ k : Fin (Bclps.Dconst * r), (z - (β k : ℂ))) =
        ∏ k ∈ (Finset.univ : Finset (Fin (Bclps.Dconst * r))), (z - (β k : ℂ)) by rfl] at hprod
    rcases (Finset.prod_eq_zero_iff.mp hprod) with ⟨k, hk, hzi⟩
    have hz_eq : z = (β k : ℂ) := sub_eq_zero.mp hzi
    constructor
    · rw [hz_eq]
      exact Complex.real_lt_real.mpr (hβSerre k).1
    · rw [hz_eq]
      exact Complex.real_lt_real.mpr (hβSerre k).2
  refine ⟨hsqfree, hrootC, ⟨β, gL, gR, ?_⟩⟩
  constructor
  · -- (1)
    intro k
    exact ⟨(hgL k).1, (hgL k).2, (hgR k).1, (hgR k).2⟩
  constructor
  · exact hβroot
  constructor
  · exact hsignG
  constructor
  · exact hβWin
  constructor
  · exact hgRltgL
  constructor
  · exact hβmono
  constructor
  · exact hβSerre
  · exact hfac


/-- Sorted root enumeration of the complementary polynomial (`lem:comp_Q_roots`,
strengthened: squarefree + explicit increasing roots + gaps inside the interval
+ roots in the interior Chebyshev window). -/
theorem comp_q_roots_sorted : ∃ C0 : ℕ, 2 ≤ C0 ∧
  ∀ (r : ℕ), C0 ≤ r →
  ∀ (T Q0 Q1 Q : Polynomial ℝ) (eps : ℕ → ℝ) (N : ℝ),
    T.Monic → T.natDegree = r →
    (∀ i : Fin (r + 1),
      0 < T.eval (bracketPoint r i) * (prunedPoly r).eval (bracketPoint r i) ∧
      |T.eval (bracketPoint r i)| ≥ kappaC ^ r / 64) →
    Q0 = ∏ j' ∈ Finset.range Bclps.Dconst,
          (T - Polynomial.C (factorCenter r j')) →
    Q1 = Q0 + (∑ t ∈ Finset.Icc 1 (d r),
          Polynomial.C (eps t) * Bclps.auxPoly t) →
    Q = Q1 + Polynomial.C N →
    (∀ t : ℕ, t ∈ Finset.Icc 1 (d r) → 0 ≤ eps t ∧ eps t < 2) →
    0 ≤ N → N ≤ 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) →
    Q.Monic → Q.natDegree = Bclps.Dconst * r →
    Squarefree Q ∧
    (∀ z : ℂ, Polynomial.aeval z Q = 0 → (aSerre : ℂ) < z ∧ z < (bSerre : ℂ)) ∧
    (∃ β gL gR : Fin (Bclps.Dconst * r) → ℝ,
      (∀ k : Fin (Bclps.Dconst * r),
        aSerre < gL k ∧ gL k < β k ∧ β k < gR k ∧ gR k < bSerre) ∧
      (∀ k : Fin (Bclps.Dconst * r), Q.eval (β k) = 0) ∧
      (∀ k : Fin (Bclps.Dconst * r), Q.eval (gL k) * Q.eval (gR k) < 0) ∧
      (∀ k : Fin (Bclps.Dconst * r),
        extPoint (r + 3) (r + 1) ≤ β k ∧ β k ≤ extPoint (r + 3) 1) ∧
      (∀ i j : Fin (Bclps.Dconst * r), i.val < j.val → gR i < gL j) ∧
      (∀ i j : Fin (Bclps.Dconst * r), i.val < j.val → β i < β j) ∧
      (∀ k : Fin (Bclps.Dconst * r), aSerre < β k ∧ β k < bSerre) ∧
      Q = ∏ k : Fin (Bclps.Dconst * r),
            (Polynomial.X - Polynomial.C (β k))) := by
  classical
  rcases large_r with ⟨C6, hC6⟩
  rcases large_r4 with ⟨C4, hC4⟩
  let C0 : ℕ := max (max C6 C4) 2
  refine ⟨C0, ?_, ?_⟩
  · dsimp [C0]
    omega
  · intro r hr T Q0 Q1 Q eps N hTmon hTdeg hTsm hQ0 hQ1 hQ hEps hN0 hNle _hQmon _hQdeg
    have hr2 : 2 ≤ r := by dsimp [C0] at hr; omega
    have hC6r : C6 ≤ r := by dsimp [C0] at hr; omega
    have hC4r : C4 ≤ r := by dsimp [C0] at hr; omega
    have h6r : (4 : ℝ) / ((kappaC - 1) * kappaC ^ (r - 1)) < 6 * C2val⁻¹ := by
      simpa [div_eq_mul_inv] using (hC6 r hC6r)
    have h4r : (4 : ℝ) / ((kappaC - 1) * kappaC ^ (r - 1)) < 4 * C2val⁻¹ := by
      simpa [div_eq_mul_inv] using (hC4 r hC4r)
    have hTsgn : ∀ i : Fin (r + 1),
        0 < T.eval (bracketPoint r i) * (prunedPoly r).eval (bracketPoint r i) := fun i => (hTsm i).1
    have hTmag : ∀ i : Fin (r + 1), |T.eval (bracketPoint r i)| ≥ kappaC ^ r / 64 := fun i => (hTsm i).2
    exact comp_q_roots_sorted_core r hr2 h6r h4r eps N hTmon hTdeg hTsgn hTmag hQ0 hQ1 hQ hEps hN0 hNle

end Submission.CompQEnum

