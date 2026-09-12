import Mathlib

/-!
# Isolated task: first Fekete comparison lemma (Vandermonde ⟹ Chebyshev)

Self-contained definitions (mirror of Submission/Dubinin.lean).  Prove ONLY
the declarations below; leave nothing unproved.

Background: for a compact set `E`, `feketeNumber E n` is the maximal
Vandermonde product over `n`-point configurations in `E`, and the Chebyshev
number `chebyshevNumber E n` is the minimal sup-norm of a monic degree-`n`
polynomial on `E`.  Fekete's theorem identifies their `n`-th-root limits.
This file proves the *elementary, finitary* half:

    a well-spread `n`-point configuration (large Vandermonde product `v`)
    produces a monic degree-`n` polynomial `q` (its root polynomial) whose
    sup-norm on `E` is `≤ feketeNumber E (n+1) / v`.

Indeed, for `q(X) = ∏_{j<n} (X − x_j)` and any `X ∈ E`, the `(n+1)`-point
Vandermonde product of `x₀,…,x_{n−1}, X` equals `vdm(x₀..x_{n−1}) ·
‖q(X)‖`, and that product is a member of the `(n+1)`-point configuration
family, hence `≤ feketeNumber E (n+1)`.

Declarations (naming/definitions given below -- keep them, only fill proofs):

1. `vdm_extend` : for `x : ℕ → ℂ`, `n : ℕ`, and `X : ℂ`:
   `vdm (fun i => if h : i < n then x i else X) (n + 1) = vdm x n * ‖qX‖`
   where the extended configuration has `x₀,…,x_{n−1}, X`.  (State it with
   a helper function `xw : ℕ → ℂ := fun i => if h : i < n then x i else X`;
   prove by expanding `vdm` and splitting the last column/row, or simply
   prove the equivalent `∏` identity directly.  You may instead restate as
   `vdm_extend` over a directly defined successor configuration.)

2. `fekete_ratio_poly` : with `E : Set ℂ`, `n ≥ 1`, points
   `x : ℕ → ℂ` all in `E`, `v := vdm x n > 0`, and `q := ∏_{j<n} (X − x j)`
   monic degree `n`:  `∀ X ∈ E, ‖q.eval X‖ ≤ feketeNumber E (n+1) / v`.

3. `chebyshevNumber_le_fekete_ratio` : same hypotheses: the existence of
   such `q` witnesses `chebyshevNumber E n ≤ feketeNumber E (n+1) / v`
   (`chebyshevNumber_le_of_bounds`, stated below and to be proved: from a
   monic degree-`n` polynomial bounded by `c ≥ 0` on `E`).

Definitions (given):

    MonicDeg n     := {p : ℂ[X] | p.Monic ∧ p.natDegree = n}
    vdm x n        := ∏ i ∈ range n, ∏ j ∈ range i, ‖x j − x i‖
    feketeNumber E n := sSup {d | ∃ x, (∀ i < n, x i ∈ E) ∧ d = vdm x n}
    chebyshevNumber E n := sInf {c | 0 ≤ c ∧ ∃ p ∈ MonicDeg n,
                                     ∀ X ∈ E, ‖p.eval X‖ ≤ c}

Notes:
* Over ℝ use the conditionally-complete lattice lemmas: `csInf_le (h₁ :
  BddBelow s) (h₂ : a ∈ s)`, `le_csInf (h₁ : s.Nonempty)`, `csSup_le` /
  `le_csSup` for suprema with `BddAbove`/`Nonempty`; `csInf_lt_iff` /
  `lt_csSup_iff` may help.
* The set of Vandermonde products over configurations in a bounded `E` is
  bounded above (each `‖x_i − x_j‖ ≤ 2R` for a bound `R` of `E`, so
  `vdm ≤ (2R) ^ (n(n−1)/2)`); take a boundedness hypothesis
  `(hRb : Bornology.IsBounded E)` and derive `BddAbove` from it.
* For the root polynomial use `q := ∏ j ∈ Finset.range n, (X - C (x j))`;
  `q.Monic` and `q.natDegree = n` from products of monic `X - C a`.
* `‖q.eval X‖ = ∏ j ∈ range n, ‖X - x j‖` (norm_prod, eval_prod,
  `eval_sub`/`eval_X`/`eval_C`).
* In the sup bound use `le_csSup` (need `BddAbove` of the config set and
  `Nonempty`) or the pointwise bound with `le_csSup`.
* Feel free to add helper lemmas (e.g. `vdm`-extension identities, product
  bounds, monicity of products); do not change the three declarations'
  statements.
-/

noncomputable section

open scoped Real Polynomial Topology BigOperators

namespace Submission.Fekete

open Polynomial

/-- Monic complex polynomials of degree exactly `n`. -/
def MonicDeg (n : ℕ) : Set ℂ[X] := {p : ℂ[X] | p.Monic ∧ p.natDegree = n}

/-- The Vandermonde product of `n` points (pairs `j < i < n`). -/
def vdm (x : ℕ → ℂ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range i, ‖x j - x i‖

/-- The set of Vandermonde products over `n`-point configurations in `E`. -/
def feketeSet (E : Set ℂ) (n : ℕ) : Set ℝ :=
  {d : ℝ | ∃ x : ℕ → ℂ, (∀ i : ℕ, i < n → x i ∈ E) ∧ d = vdm x n}

/-- **Fekete number.** -/
def feketeNumber (E : Set ℂ) (n : ℕ) : ℝ := sSup (feketeSet E n)

/-- **Chebyshev number.** -/
def chebyshevNumber (E : Set ℂ) (n : ℕ) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ ∃ p ∈ MonicDeg n, ∀ X ∈ E, ‖p.eval X‖ ≤ c}

/-- `chebyshevNumber E n ≤ c` from a monic degree-`n` polynomial bounded by
`c ≥ 0` on `E`. -/
lemma chebyshevNumber_le_of_bounds {E : Set ℂ} {n : ℕ} {p : ℂ[X]}
    (hp : p ∈ MonicDeg n) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ X ∈ E, ‖p.eval X‖ ≤ c) :
    chebyshevNumber E n ≤ c := by
  unfold chebyshevNumber
  exact csInf_le (by
    refine ⟨0, ?_⟩
    intro b hb'
    exact hb'.1) ⟨hc, ⟨p, ⟨hp, hb⟩⟩⟩


/-- Vandermonde products are nonnegative (products of norms). -/
lemma vdm_nonneg (x : ℕ → ℂ) (n : ℕ) : 0 ≤ vdm x n := by
  unfold vdm
  exact Finset.prod_nonneg (fun i _ =>
    Finset.prod_nonneg (fun j _ => norm_nonneg (x j - x i)))

/-- Pointwise bound on an `m`-tuple in a norm-ball: `vdm x m` is bounded by
the product over `i < m` of `(2R)^i` (each pair `j < i` contributes at most
`2R`).  Used to show `feketeSet E m` is bounded above for bounded `E`. -/
lemma vdm_le_prod (x : ℕ → ℂ) (m : ℕ) (R : ℝ) (h : ∀ i, i < m → ‖x i‖ ≤ R) :
    vdm x m ≤ ∏ i ∈ Finset.range m, (∏ _j ∈ Finset.range i, (2 * R)) := by
  unfold vdm
  apply Finset.prod_le_prod
  · intro i _
    exact Finset.prod_nonneg (fun j _ => norm_nonneg (x j - x i))
  · intro i hi
    apply Finset.prod_le_prod
    · intro j _
      exact norm_nonneg (x j - x i)
    · intro j hj
      calc
        ‖x j - x i‖ ≤ ‖x j‖ + ‖x i‖ := norm_sub_le _ _
        _ ≤ R + R := by
          exact add_le_add
            (h j (lt_trans (Finset.mem_range.mp hj) (Finset.mem_range.mp hi)))
            (h i (Finset.mem_range.mp hi))
        _ = 2 * R := by ring

/-- For bounded `E`, the family of Vandermonde products over `m`-point
configurations in `E` is bounded above. -/
lemma feketeSet_bddAbove (E : Set ℂ) (hE : Bornology.IsBounded E) (m : ℕ) :
    BddAbove (feketeSet E m) := by
  rcases hE.exists_norm_le with ⟨C, hC⟩
  refine ⟨∏ i ∈ Finset.range m, (∏ _j ∈ Finset.range i, (2 * max C 0)), ?_⟩
  intro d hd
  rcases hd with ⟨x, hx, rfl⟩
  exact vdm_le_prod x m (max C 0) (fun i hi =>
    le_trans (hC (x i) (hx i hi)) (le_max_left C 0))

/-- The root polynomial `∏_{j<n} (X − x j)` is monic. -/
lemma root_poly_monic {n : ℕ} (x : ℕ → ℂ) :
    (∏ j ∈ Finset.range n, (Polynomial.X - C (x j))).Monic := by
  exact monic_prod_of_monic (Finset.range n) (fun j => Polynomial.X - C (x j))
    (fun j _ => Polynomial.monic_X_sub_C (x j))

/-- The root polynomial `∏_{j<n} (X − x j)` has degree `n`. -/
lemma root_poly_natDegree {n : ℕ} (x : ℕ → ℂ) :
    (∏ j ∈ Finset.range n, (Polynomial.X - C (x j))).natDegree = n := by
  rw [Polynomial.natDegree_prod]
  · simp
  · intro j _
    exact (Polynomial.monic_X_sub_C (x j)).ne_zero

/-- The `(n+1)`-point Vandermonde product of `x₀,…,x_{n−1}` extended by
`X` factors as `vdm x n * ∏_{j<n} ‖X − x j‖`.  (A cleaner equivalent:
`∏ i ∈ range (n+1), ∏ j ∈ range i, ‖xw j - xw i‖` with
`xw := fun i => if i < n then x i else X`; splitting off `i = n` gives the
right-hand side.) -/
lemma vdm_extend {n : ℕ} (x : ℕ → ℂ) (X : ℂ) :
    vdm (fun i : ℕ => if i < n then x i else X) (n + 1)
      = vdm x n * ∏ j ∈ Finset.range n, ‖X - x j‖ := by
  classical
  let xw : ℕ → ℂ := fun i => if i < n then x i else X
  have hxw_lt : ∀ {i}, i < n → xw i = x i := by
    intro i hi
    simp [xw, hi]
  have hxw_ge : ∀ {i}, ¬i < n → xw i = X := by
    intro i hi
    simp [xw, hi]
  calc
    vdm xw (n + 1)
        = (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range i, ‖xw j - xw i‖) *
            (∏ j ∈ Finset.range n, ‖xw j - xw n‖) := by
            unfold vdm
            rw [Finset.prod_range_succ]
    _ = vdm x n * (∏ j ∈ Finset.range n, ‖xw j - xw n‖) := by
            congr 1
            unfold vdm
            apply Finset.prod_congr rfl
            intro i hi
            apply Finset.prod_congr rfl
            intro j hj
            rw [hxw_lt (lt_trans (Finset.mem_range.mp hj) (Finset.mem_range.mp hi)),
                hxw_lt (Finset.mem_range.mp hi)]
    _ = vdm x n * (∏ j ∈ Finset.range n, ‖X - x j‖) := by
            apply congrArg (fun t => vdm x n * t)
            apply Finset.prod_congr rfl
            intro j hj
            rw [hxw_lt (Finset.mem_range.mp hj), hxw_ge (by simp)]
            exact norm_sub_rev (x j) X

/-- **First Fekete comparison.**  The root polynomial of a well-spread
configuration is controlled on `E` by the Fekete ratio `feketeNumber E
(n+1) / vdm x n`. -/
lemma fekete_ratio_poly {E : Set ℂ} {n : ℕ} (hn : 1 ≤ n)
    (hE : Bornology.IsBounded E) {x : ℕ → ℂ}
    (hx : ∀ i : ℕ, i < n → x i ∈ E) (hv : 0 < vdm x n) :
    ∀ Y ∈ E,
      ‖(∏ j ∈ Finset.range n, (Polynomial.X - C (x j))).eval Y‖
        ≤ feketeNumber E (n + 1) / vdm x n := by
  have _hn_used : 1 ≤ n := hn
  intro Y hY
  let xw : ℕ → ℂ := fun i => if i < n then x i else Y
  have hxw_mem : ∀ i : ℕ, i < n + 1 → xw i ∈ E := by
    intro i hi
    by_cases hin : i < n
    · have : xw i = x i := by simp [xw, hin]
      rw [this]
      exact hx i hin
    · have hin_eq : i = n := by omega
      subst i
      have : xw n = Y := by simp [xw]
      rw [this]
      exact hY
  have hmem : vdm xw (n + 1) ∈ feketeSet E (n + 1) := by
    exact ⟨xw, hxw_mem, rfl⟩
  have hbdd : BddAbove (feketeSet E (n + 1)) := feketeSet_bddAbove E hE (n + 1)
  have hle : vdm xw (n + 1) ≤ feketeNumber E (n + 1) := le_csSup hbdd hmem
  have hnorm : ‖(∏ j ∈ Finset.range n, (Polynomial.X - C (x j))).eval Y‖
      = ∏ j ∈ Finset.range n, ‖Y - x j‖ := by
    rw [Polynomial.eval_prod]
    rw [norm_prod]
    apply Finset.prod_congr rfl
    intro j _
    simp
  have hmul : vdm x n *
        ‖(∏ j ∈ Finset.range n, (Polynomial.X - C (x j))).eval Y‖
        ≤ feketeNumber E (n + 1) := by
    rw [hnorm]
    rw [← vdm_extend x Y]
    exact hle
  rw [le_div_iff₀ hv]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- **Chebyshev number ≤ Fekete ratio.**  (Consequence of
`fekete_ratio_poly` + `chebyshevNumber_le_of_bounds`.) -/
lemma chebyshevNumber_le_fekete_ratio {E : Set ℂ} {n : ℕ} (hn : 1 ≤ n)
    (hE : Bornology.IsBounded E) {x : ℕ → ℂ}
    (hx : ∀ i : ℕ, i < n → x i ∈ E) (hv : 0 < vdm x n) :
    chebyshevNumber E n ≤ feketeNumber E (n + 1) / vdm x n := by
  have hc : 0 ≤ feketeNumber E (n + 1) / vdm x n := by
    have hx0 : x 0 ∈ E := hx 0 (by omega)
    have hmem0 : vdm (fun _ : ℕ => x 0) (n + 1) ∈ feketeSet E (n + 1) := by
      refine ⟨(fun _ : ℕ => x 0), ?_, rfl⟩
      intro i _
      exact hx0
    have hnonneg : ∀ d ∈ feketeSet E (n + 1), 0 ≤ d := by
      intro d hd
      rcases hd with ⟨y, _hy, rfl⟩
      exact vdm_nonneg y (n + 1)
    have hbdd : BddAbove (feketeSet E (n + 1)) := feketeSet_bddAbove E hE (n + 1)
    have hF : 0 ≤ feketeNumber E (n + 1) :=
      le_trans (hnonneg _ hmem0) (le_csSup hbdd hmem0)
    exact div_nonneg hF (le_of_lt hv)
  apply chebyshevNumber_le_of_bounds
    (p := ∏ j ∈ Finset.range n, (Polynomial.X - C (x j)))
    ⟨root_poly_monic x, root_poly_natDegree x⟩ hc
  intro Y hY
  exact fekete_ratio_poly hn hE hx hv Y hY

end Submission.Fekete

end
