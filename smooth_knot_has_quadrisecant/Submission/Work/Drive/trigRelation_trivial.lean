import Mathlib
import Submission.Work.Drive.knotPerturbDefs

namespace Work.Drive

noncomputable section

/-- Pulling back a single coordinate of the coefficient vector. -/
private lemma trigRel_sum_single (i : Fin 9) (t : ℝ) :
    (∑ j : Fin 9, trigBasis j t * (Pi.single i (1:ℝ) : Fin 9 → ℝ) j) = trigBasis i t := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- Pulling back a single coordinate of the coefficient vector (derivative basis). -/
private lemma trigRel_sum_singleD (i : Fin 9) (t : ℝ) :
    (∑ j : Fin 9, trigBasisD j t * (Pi.single i (1:ℝ) : Fin 9 → ℝ) j) = trigBasisD i t := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- de Moivre in the form needed: the `k`-th power of `exp (i x)` is `cos (k x) + i sin (k x)`. -/
private lemma trigRel_exp_pow (x : ℝ) (k : ℕ) :
    (Complex.exp ((x:ℂ) * Complex.I))^k
      = (Real.cos (k*x) : ℂ) + (Real.sin (k*x) : ℂ) * Complex.I := by
  rw [← Complex.exp_nat_mul]
  have : (k:ℂ) * ((x:ℂ) * Complex.I) = ((k*x:ℝ):ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I]

/-- Two distinct points of `[0, 2π)` have distinct exponentials. -/
private lemma trigRel_exp_ne_exp_of {p q : ℝ} (hpq : p ≠ q)
    (hp : p ∈ Set.Ico 0 (2*Real.pi)) (hq : q ∈ Set.Ico 0 (2*Real.pi)) :
    Complex.exp ((p:ℂ) * Complex.I) ≠ Complex.exp ((q:ℂ) * Complex.I) := by
  intro heq
  rw [Complex.exp_eq_exp_iff_exists_int] at heq
  obtain ⟨n, hn⟩ := heq
  have him := congrArg Complex.im hn
  simp at him
  have h1 : p - q < 2*Real.pi := by linarith [hp.2, hq.1]
  have h2 : -2*Real.pi < p - q := by linarith [hp.1, hq.2]
  have h2π : (0:ℝ) < 2*Real.pi := by positivity
  have hthis : (n:ℝ) * (2*Real.pi) = p - q := by linarith [him]
  have h3a : (-1:ℝ) * (2*Real.pi) < (n:ℝ) * (2*Real.pi) := by
    have : (-1:ℝ) * (2*Real.pi) = -2*Real.pi := by ring
    linarith [h2, hthis, this]
  have h3 : (-1:ℝ) < (n:ℝ) := (mul_lt_mul_iff_of_pos_right h2π).mp h3a
  have h4a : (n:ℝ) * (2*Real.pi) < (1:ℝ) * (2*Real.pi) := by
    have : (1:ℝ) * (2*Real.pi) = 2*Real.pi := by ring
    linarith [h1, hthis, this]
  have h4 : (n:ℝ) < 1 := (mul_lt_mul_iff_of_pos_right h2π).mp h4a
  have h3' : (-1:ℤ) < n := by exact_mod_cast h3
  have h4' : n < (1:ℤ) := by exact_mod_cast h4
  have hn0 : n = 0 := by omega
  subst hn0
  simp at him
  exact hpq him

/-- Combining the cosine and sine relations of frequency `k` into a single complex relation. -/
private lemma trigRel_complex_of_cos_sin {p q r α A B C : ℝ} {k : ℕ}
    (hcos : A * Real.cos (k*p) + B * Real.cos (k*q) + C * Real.cos (k*r)
      - (α * (k:ℝ)) * Real.sin (k*p) = 0)
    (hsin : A * Real.sin (k*p) + B * Real.sin (k*q) + C * Real.sin (k*r)
      + (α * (k:ℝ)) * Real.cos (k*p) = 0) :
    ((A:ℂ) + Complex.I*((α * (k:ℝ):ℝ):ℂ)) * (Complex.exp ((p:ℂ)*Complex.I))^k
      + (B:ℂ)*(Complex.exp ((q:ℂ)*Complex.I))^k + (C:ℂ)*(Complex.exp ((r:ℂ)*Complex.I))^k = 0 := by
  rw [trigRel_exp_pow p k, trigRel_exp_pow q k, trigRel_exp_pow r k]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re]
    linarith [hcos]
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_im]
    linarith [hsin]

/-- The final complex-algebra step: three consecutive relations of the form
`(A + iαk) z^k + B y^k + C x^k = 0` (plus the `k = 0` relation) force `α = A = B = C = 0`. -/
private lemma trigRel_complex_algebra (Z Y X : ℂ) (α A B C : ℝ)
    (hZ0 : Z ≠ 0) (hZY : Z ≠ Y) (hZX : Z ≠ X) (hXY : X ≠ Y)
    (g0 : (A:ℂ) + (B:ℂ) + (C:ℂ) = 0)
    (g1 : ((A:ℂ) + Complex.I*(α:ℂ)) * Z + (B:ℂ)*Y + (C:ℂ)*X = 0)
    (g2 : ((A:ℂ) + Complex.I*((α:ℂ)*2)) * Z^2 + (B:ℂ)*Y^2 + (C:ℂ)*X^2 = 0)
    (g3 : ((A:ℂ) + Complex.I*((α:ℂ)*3)) * Z^3 + (B:ℂ)*Y^3 + (C:ℂ)*X^3 = 0) :
    α = 0 ∧ A = 0 ∧ B = 0 ∧ C = 0 := by
  have key1 : ((A:ℂ) + Complex.I*((α:ℂ)*2)) * Z^2 + (B:ℂ)*Y^2 + (C:ℂ)*X^2
        - (Y + X) * (((A:ℂ) + Complex.I*(α:ℂ)) * Z + (B:ℂ)*Y + (C:ℂ)*X)
        + Y*X*((A:ℂ) + (B:ℂ) + (C:ℂ))
      = (A:ℂ)*(Z - Y)*(Z - X) + Complex.I*(α:ℂ)*Z*(2*Z - Y - X) := by ring
  have lin1 : (A:ℂ)*(Z - Y)*(Z - X) + Complex.I*(α:ℂ)*Z*(2*Z - Y - X) = 0 := by
    rw [← key1, g2, g1, g0]; ring
  have key2 : ((A:ℂ) + Complex.I*((α:ℂ)*3)) * Z^3 + (B:ℂ)*Y^3 + (C:ℂ)*X^3
        - (Y + X) * (((A:ℂ) + Complex.I*((α:ℂ)*2)) * Z^2 + (B:ℂ)*Y^2 + (C:ℂ)*X^2)
        + Y*X*(((A:ℂ) + Complex.I*(α:ℂ)) * Z + (B:ℂ)*Y + (C:ℂ)*X)
      = Z*(((A:ℂ) + Complex.I*(α:ℂ))*(Z-Y)*(Z-X) + Complex.I*(α:ℂ)*Z*(2*Z-Y-X)) := by ring
  have lin2 : Z*(((A:ℂ) + Complex.I*(α:ℂ))*(Z-Y)*(Z-X) + Complex.I*(α:ℂ)*Z*(2*Z-Y-X)) = 0 := by
    rw [← key2, g3, g2, g1]; ring
  have key3 : Z*(((A:ℂ) + Complex.I*(α:ℂ))*(Z-Y)*(Z-X) + Complex.I*(α:ℂ)*Z*(2*Z-Y-X))
        - Z*((A:ℂ)*(Z - Y)*(Z - X) + Complex.I*(α:ℂ)*Z*(2*Z - Y - X))
      = Z*Complex.I*(α:ℂ)*(Z-Y)*(Z-X) := by ring
  have hprod : Z*Complex.I*(α:ℂ)*(Z-Y)*(Z-X) = 0 := by
    rw [← key3, lin2, lin1]; ring
  have hα0c : (α:ℂ) = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · exact absurd h hZ0
          · exact absurd h Complex.I_ne_zero
        · exact h
      · exact absurd h (sub_ne_zero.mpr hZY)
    · exact absurd h (sub_ne_zero.mpr hZX)
  have hα : α = 0 := Complex.ofReal_eq_zero.mp hα0c
  have hA0c : (A:ℂ) = 0 := by
    have h : (A:ℂ)*(Z-Y)*(Z-X) = 0 := by
      have h' := lin1; rw [hα0c] at h'; simpa using h'
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h (sub_ne_zero.mpr hZY)
    · exact absurd h (sub_ne_zero.mpr hZX)
  have hA : A = 0 := Complex.ofReal_eq_zero.mp hA0c
  have hB0c : (B:ℂ) = -(C:ℂ) := by
    have h : (B:ℂ) + (C:ℂ) = 0 := by
      have h' := g0; rw [hA0c] at h'; simpa using h'
    exact eq_neg_of_add_eq_zero_left h
  have hBY : (B:ℂ)*Y + (C:ℂ)*X = 0 := by
    have h' := g1; rw [hA0c, hα0c] at h'; simpa using h'
  have hC0c : (C:ℂ) = 0 := by
    have h2 : (C:ℂ)*(X - Y) = 0 := by
      have h' := hBY
      rw [hB0c] at h'
      rw [show -((C:ℂ))*Y + (C:ℂ)*X = (C:ℂ)*(X-Y) from by ring] at h'
      exact h'
    rcases mul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd h (sub_ne_zero.mpr hXY)
  have hC : C = 0 := Complex.ofReal_eq_zero.mp hC0c
  have hB : B = 0 := by
    have h' := hB0c; rw [hC0c, neg_zero] at h'
    exact Complex.ofReal_eq_zero.mp h'
  exact ⟨hα, hA, hB, hC⟩

/-- **The relation-space triviality for the degree-`4` trigonometric basis** (module `Submission.Work.Drive.knotPerturbDefs` supplies `trigBasis`, `trigBasisD`).

If a linear combination of the four functionals `φ ↦ φ'(p)`, `φ ↦ φ(p)`, `φ ↦ φ(q)` and `φ ↦ φ(r)` (the derivative at `p`, and the values at the three pairwise distinct points `p, q, r` of `[0, 2π)`) vanishes on every trigonometric polynomial of degree at most `4`, then all four coefficients vanish.

Proof route.  The space of trigonometric polynomials of degree at most `4` is translation invariant, so after translating one may assume `p = 0`.  Applying the hypothesis to `cos (k·)` and `sin (k·)` and combining (via `Complex.exp`) gives, for `k = 0, 1, …, 4`, the complex equation `A + B z^k + C w^k + i α k = 0`, where `z = exp (i q)`, `w = exp (i r)`.  Apply the difference operator `Q(E) = (E - z)(E - w)` in `k`: it kills the exponential terms and turns the affine term into `i α (k Q(1) + Q'(1))`; applying at `k = 0` and `k = 1` and subtracting gives `i α Q(1) = 0`, so `α = 0` because `Q(1) = (1 - z)(1 - w) ≠ 0` (using `q ≠ 0` and `r ≠ 0` mod `2π`, which follows from `q, r ∈ [0, 2π)`).  With `α = 0`, the equations at `k = 0, 1, 2` form the Vandermonde system `A + B z^k + C w^k = 0`, whose determinant `(z - 1)(w - 1)(w - z)` is nonzero (as `q ≠ r`), giving `A = B = C = 0`. -/
theorem trigRelation_trivial {p q r : ℝ} (hp : p ∈ Set.Ico 0 (2 * Real.pi))
    (hq : q ∈ Set.Ico 0 (2 * Real.pi)) (hr : r ∈ Set.Ico 0 (2 * Real.pi))
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (α A B C : ℝ)
    (h : ∀ c : Fin 9 → ℝ, α * (∑ j, (trigBasisD j p) * c j) + A * (∑ j, (trigBasis j p) * c j)
      + B * (∑ j, (trigBasis j q) * c j) + C * (∑ j, (trigBasis j r) * c j) = 0) :
    α = 0 ∧ A = 0 ∧ B = 0 ∧ C = 0 := by
  -- Extract the coordinate equations: the four functionals vanish on each basis element.
  have extract : ∀ i : Fin 9,
      α * trigBasisD i p + A * trigBasis i p + B * trigBasis i q + C * trigBasis i r = 0 := by
    intro i
    have hh := h (Pi.single i (1:ℝ) : Fin 9 → ℝ)
    rw [trigRel_sum_singleD, trigRel_sum_single, trigRel_sum_single,
      trigRel_sum_single] at hh
    exact hh
  have e0 : A + B + C = 0 := by
    have h' := extract 0; simpa [trigBasis, trigBasisD] using h'
  have g0c : (A:ℂ) + (B:ℂ) + (C:ℂ) = 0 := by
    have : ((A + B + C : ℝ) : ℂ) = 0 := by rw [e0, Complex.ofReal_zero]
    simpa using this
  have G1 : ((A:ℂ) + Complex.I*(α:ℂ)) * Complex.exp ((p:ℂ)*Complex.I)
      + (B:ℂ)*Complex.exp ((q:ℂ)*Complex.I) + (C:ℂ)*Complex.exp ((r:ℂ)*Complex.I) = 0 := by
    have hc : A * Real.cos p + B * Real.cos q + C * Real.cos r
        - (α * (1:ℝ)) * Real.sin p = 0 := by
      have h' := extract 1; simp only [trigBasis, trigBasisD] at h'; rw [← h']; ring
    have hs : A * Real.sin p + B * Real.sin q + C * Real.sin r
        + (α * (1:ℝ)) * Real.cos p = 0 := by
      have h' := extract 2; simp only [trigBasis, trigBasisD] at h'; rw [← h']; ring
    have hh := trigRel_complex_of_cos_sin (p:=p) (q:=q) (r:=r) (α:=α) (A:=A) (B:=B) (C:=C)
      (k:=1) (by simpa using hc) (by simpa using hs)
    simpa [mul_assoc] using hh
  have G2 : ((A:ℂ) + Complex.I*((α:ℂ)*2)) * (Complex.exp ((p:ℂ)*Complex.I))^2
      + (B:ℂ)*(Complex.exp ((q:ℂ)*Complex.I))^2 + (C:ℂ)*(Complex.exp ((r:ℂ)*Complex.I))^2 = 0 := by
    have hc : A * Real.cos (2*p) + B * Real.cos (2*q) + C * Real.cos (2*r)
        - (α * (2:ℝ)) * Real.sin (2*p) = 0 := by
      have h' := extract 3; simp only [trigBasis, trigBasisD] at h'; rw [← h']; ring
    have hs : A * Real.sin (2*p) + B * Real.sin (2*q) + C * Real.sin (2*r)
        + (α * (2:ℝ)) * Real.cos (2*p) = 0 := by
      have h' := extract 4; simp only [trigBasis, trigBasisD] at h'; rw [← h']; ring
    have hh := trigRel_complex_of_cos_sin (p:=p) (q:=q) (r:=r) (α:=α) (A:=A) (B:=B) (C:=C)
      (k:=2) (by simpa using hc) (by simpa using hs)
    simpa [mul_assoc] using hh
  have G3 : ((A:ℂ) + Complex.I*((α:ℂ)*3)) * (Complex.exp ((p:ℂ)*Complex.I))^3
      + (B:ℂ)*(Complex.exp ((q:ℂ)*Complex.I))^3 + (C:ℂ)*(Complex.exp ((r:ℂ)*Complex.I))^3 = 0 := by
    have hc : A * Real.cos (3*p) + B * Real.cos (3*q) + C * Real.cos (3*r)
        - (α * (3:ℝ)) * Real.sin (3*p) = 0 := by
      have h' := extract 5; simp only [trigBasis, trigBasisD] at h'; rw [← h']; ring
    have hs : A * Real.sin (3*p) + B * Real.sin (3*q) + C * Real.sin (3*r)
        + (α * (3:ℝ)) * Real.cos (3*p) = 0 := by
      have h' := extract 6; simp only [trigBasis, trigBasisD] at h'; rw [← h']; ring
    have hh := trigRel_complex_of_cos_sin (p:=p) (q:=q) (r:=r) (α:=α) (A:=A) (B:=B) (C:=C)
      (k:=3) (by simpa using hc) (by simpa using hs)
    simpa [mul_assoc] using hh
  exact trigRel_complex_algebra (Complex.exp ((p:ℂ)*Complex.I)) (Complex.exp ((q:ℂ)*Complex.I))
    (Complex.exp ((r:ℂ)*Complex.I)) α A B C (Complex.exp_ne_zero _)
    (trigRel_exp_ne_exp_of hpq hp hq) (trigRel_exp_ne_exp_of hpr hp hr)
    (Ne.symm (trigRel_exp_ne_exp_of hqr hq hr)) g0c G1 G2 G3

end

end Work.Drive
