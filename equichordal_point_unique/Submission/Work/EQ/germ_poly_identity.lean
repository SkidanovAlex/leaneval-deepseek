import Mathlib
import Submission.Work.EQ.Defs

/-!
# The polynomial identity behind `no_rational_germ`

If the stable germ `h` of the equichordal half map is the quotient `N/D` of two polynomials
near `0` (i.e. `h u * D(u) = N(u)` for `u` near `0`), then the cleared germ equation `GermFE`
becomes, after clearing the denominators, a *polynomial* identity in `u`:

```
( N(u) D(u/λ) - N(u/λ) D(u) )² ( N(λu) D(u) - N(u) D(λu) )²
  = a² N(u)² (N(u)² + D(u)²) ( N(λu) D(u/λ) - N(u/λ) D(λu) )² .
```

The proof is: on a neighbourhood of `0` the three quotients `h v`, `h (v/λ)`, `h (λ v)` may
be written with common denominator (`D`), and `GermFE` becomes

`(p - q)(s - p) + a p (s - q) √(1+p²) = 0`   with `p = h v`, `q = h (v/λ)`, `s = h (λ v)`,

so that squaring gives the bidimensional identity after multiplying by `D(v)⁴ D(v/λ)² D(λv)²`.
Both sides are values of an explicit polynomial in `v`; since they coincide on the infinite set
`(0, m) ⊂ ℝ`, the polynomial is identically zero.  The hypothesis `D(0) ≠ 0` of the request is
not needed for the identity itself, but is kept to match the statement.
-/

namespace Work.EQ

open Filter Metric

/-- Evaluation of a polynomial composed with `u ↦ c * u`. -/
private lemma eval_comp_C_mul_X (p : Polynomial ℂ) (c u : ℂ) :
    (p.comp (Polynomial.C c * Polynomial.X)).eval u = p.eval (c * u) := by
  rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

/-- Evaluation of a polynomial composed with `u ↦ u * c`. -/
private lemma eval_comp_X_mul_C (p : Polynomial ℂ) (c u : ℂ) :
    (p.comp (Polynomial.X * Polynomial.C c)).eval u = p.eval (u * c) := by
  rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]

/-- The principal square root of `1 + x`, squared, is `1 + x`. -/
private lemma sqrt_half_sq (x : ℂ) : ((1 + x) ^ (1 / 2 : ℂ)) ^ 2 = 1 + x := by
  have h : ((1 + x) ^ ((2 : ℂ))⁻¹) ^ 2 = 1 + x := Complex.cpow_nat_inv_pow (1 + x) (by norm_num)
  have h2 : ((2 : ℂ))⁻¹ = (1 / 2 : ℂ) := by norm_num
  rw [← h2]; exact h

/-- The algebraic core: from the germ equation and `z² = 1 + p²` one gets the polynomial
identity with the three `2×2` determinants. -/
private lemma germ_poly_identity_alg (c hp hq hs du di dl z : ℂ)
    (hFE : (hp - hq) * (hs - hp) + c * hp * (hs - hq) * z = 0)
    (hz2 : z ^ 2 = 1 + hp ^ 2) :
    ((hp * du) * di - (hq * di) * du) ^ 2 * ((hs * dl) * du - (hp * du) * dl) ^ 2
    = c ^ 2 * (hp * du) ^ 2 * ((hp * du) ^ 2 + du ^ 2) *
        ((hs * dl) * di - (hq * di) * dl) ^ 2 := by
  linear_combination (du ^ 4 * di ^ 2 * dl ^ 2 * ((hp - hq) * (hs - hp) - c * hp * (hs - hq) * z)) * hFE
    + (du ^ 4 * di ^ 2 * dl ^ 2 * c ^ 2 * hp ^ 2 * (hs - hq) ^ 2) * hz2

theorem germ_poly_identity {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) {N D : Polynomial ℂ} (hD0 : Polynomial.eval 0 D ≠ 0)
    (hDN : ∀ᶠ u in nhds (0 : ℂ), h u * Polynomial.eval u D = Polynomial.eval u N) (u : ℂ) :
    (Polynomial.eval u N * Polynomial.eval (u / (Work.EQ.eqLam a : ℂ)) D -
        Polynomial.eval (u / (Work.EQ.eqLam a : ℂ)) N * Polynomial.eval u D) ^ 2 *
      (Polynomial.eval ((Work.EQ.eqLam a : ℂ) * u) N * Polynomial.eval u D -
        Polynomial.eval u N * Polynomial.eval ((Work.EQ.eqLam a : ℂ) * u) D) ^ 2
    = ((a : ℂ)) ^ 2 * Polynomial.eval u N ^ 2 *
        (Polynomial.eval u N ^ 2 + Polynomial.eval u D ^ 2) *
      (Polynomial.eval ((Work.EQ.eqLam a : ℂ) * u) N * Polynomial.eval (u / (Work.EQ.eqLam a : ℂ)) D -
        Polynomial.eval (u / (Work.EQ.eqLam a : ℂ)) N * Polynomial.eval ((Work.EQ.eqLam a : ℂ) * u) D) ^ 2 := by
  obtain ⟨hr, _hana, _hh0, _hder, _him, hFE⟩ := hh
  have hlam_pos : 0 < eqLam a := by rw [eqLam]; exact div_pos (by linarith) (by linarith)
  -- eventual quotient relation
  obtain ⟨eps, heps_pos, heps⟩ := Metric.mem_nhds_iff.mp hDN
  -- the composed polynomials entering the two sides
  set Nl : Polynomial ℂ := N.comp (Polynomial.C ((eqLam a : ℂ)) * Polynomial.X) with hNl
  set Dl : Polynomial ℂ := D.comp (Polynomial.C ((eqLam a : ℂ)) * Polynomial.X) with hDl
  set Ni : Polynomial ℂ := N.comp (Polynomial.X * Polynomial.C (((eqLam a : ℂ))⁻¹)) with hNi
  set Di : Polynomial ℂ := D.comp (Polynomial.X * Polynomial.C (((eqLam a : ℂ))⁻¹)) with hDi
  set G : Polynomial ℂ := (N * Di - Ni * D) ^ 2 * (Nl * D - N * Dl) ^ 2
      - Polynomial.C ((a : ℂ) ^ 2) * N ^ 2 * (N ^ 2 + D ^ 2) * (Nl * Di - Ni * Dl) ^ 2 with hGdef
  have evNl : ∀ v, Nl.eval v = N.eval ((eqLam a : ℂ) * v) := by
    intro v; rw [hNl, eval_comp_C_mul_X]
  have evDl : ∀ v, Dl.eval v = D.eval ((eqLam a : ℂ) * v) := by
    intro v; rw [hDl, eval_comp_C_mul_X]
  have evNi : ∀ v, Ni.eval v = N.eval (v / (eqLam a : ℂ)) := by
    intro v; rw [hNi, eval_comp_X_mul_C, div_eq_mul_inv]
  have evDi : ∀ v, Di.eval v = D.eval (v / (eqLam a : ℂ)) := by
    intro v; rw [hDi, eval_comp_X_mul_C, div_eq_mul_inv]
  have evG : ∀ v : ℂ, G.eval v =
      (Polynomial.eval v N * Polynomial.eval (v / (eqLam a : ℂ)) D -
          Polynomial.eval (v / (eqLam a : ℂ)) N * Polynomial.eval v D) ^ 2 *
        (Polynomial.eval ((eqLam a : ℂ) * v) N * Polynomial.eval v D -
          Polynomial.eval v N * Polynomial.eval ((eqLam a : ℂ) * v) D) ^ 2
      - ((a : ℂ)) ^ 2 * Polynomial.eval v N ^ 2 *
          (Polynomial.eval v N ^ 2 + Polynomial.eval v D ^ 2) *
        (Polynomial.eval ((eqLam a : ℂ) * v) N * Polynomial.eval (v / (eqLam a : ℂ)) D -
          Polynomial.eval (v / (eqLam a : ℂ)) N * Polynomial.eval ((eqLam a : ℂ) * v) D) ^ 2 := by
    intro v
    rw [hGdef]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_C, evNl, evNi, evDl, evDi]
  -- a small radius where all three quotient relations and the germ equation hold
  set m : ℝ := min (min (eqLam a * r) eps) (min (eps * eqLam a) (eps / eqLam a)) with hm
  have hm_pos : 0 < m := by
    rw [hm]
    exact lt_min (lt_min (mul_pos hlam_pos hr) heps_pos)
      (lt_min (mul_pos heps_pos hlam_pos) (div_pos heps_pos hlam_pos))
  have hroot : ∀ t ∈ Set.Ioo (0 : ℝ) m, G.IsRoot (t : ℂ) := by
    intro t ht
    obtain ⟨ht0, htm⟩ := ht
    have hle1 : m ≤ min (eqLam a * r) eps := by rw [hm]; exact min_le_left _ _
    have hle2 : m ≤ min (eps * eqLam a) (eps / eqLam a) := by rw [hm]; exact min_le_right _ _
    have ht1 : t < eqLam a * r := lt_of_lt_of_le (lt_of_lt_of_le htm hle1) (min_le_left _ _)
    have hte : t < eps := lt_of_lt_of_le (lt_of_lt_of_le htm hle1) (min_le_right _ _)
    have ht2 : t < eps * eqLam a := lt_of_lt_of_le (lt_of_lt_of_le htm hle2) (min_le_left _ _)
    have ht3 : t < eps / eqLam a := lt_of_lt_of_le (lt_of_lt_of_le htm hle2) (min_le_right _ _)
    have hmem : (t : ℂ) ∈ Metric.ball (0 : ℂ) (eqLam a * r) := by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      exact ht1
    have hFEt : GermFE a h (t : ℂ) := hFE (t : ℂ) hmem
    have h1 : h (t : ℂ) * D.eval (t : ℂ) = N.eval (t : ℂ) := by
      apply heps
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      exact hte
    have h2 : h ((t : ℂ) / (eqLam a : ℂ)) * D.eval ((t : ℂ) / (eqLam a : ℂ))
        = N.eval ((t : ℂ) / (eqLam a : ℂ)) := by
      apply heps
      simp only [Metric.mem_ball, dist_zero_right, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht0, abs_of_pos hlam_pos]
      rw [div_lt_iff₀ hlam_pos]
      exact ht2
    have h3 : h ((eqLam a : ℂ) * (t : ℂ)) * D.eval ((eqLam a : ℂ) * (t : ℂ))
        = N.eval ((eqLam a : ℂ) * (t : ℂ)) := by
      apply heps
      simp only [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht0, abs_of_pos hlam_pos]
      rw [mul_comm (eqLam a) t, ← lt_div_iff₀ hlam_pos]
      exact ht3
    have hz2 : (((1 + h (t : ℂ) ^ 2) ^ (1 / 2 : ℂ))) ^ 2 = 1 + h (t : ℂ) ^ 2 := sqrt_half_sq _
    have key : G.eval (t : ℂ) = 0 := by
      rw [evG, sub_eq_zero]
      rw [← h1, ← h2, ← h3]
      exact germ_poly_identity_alg (a : ℂ) (h (t : ℂ)) (h ((t : ℂ) / (eqLam a : ℂ)))
        (h ((eqLam a : ℂ) * (t : ℂ))) (D.eval (t : ℂ)) (D.eval ((t : ℂ) / (eqLam a : ℂ)))
        (D.eval ((eqLam a : ℂ) * (t : ℂ))) (((1 + h (t : ℂ) ^ 2) ^ (1 / 2 : ℂ))) hFEt hz2
    exact key
  have hinf : (Set.Ioo (0 : ℝ) m).Infinite := Set.Ioo_infinite hm_pos
  have hinfimg : ((fun t : ℝ => (t : ℂ)) '' (Set.Ioo (0 : ℝ) m)).Infinite :=
    Set.Infinite.image (fun x _ y _ hxy => Complex.ofReal_injective hxy) hinf
  have hroots_inf : {x : ℂ | G.IsRoot x}.Infinite :=
    hinfimg.mono (by rintro z ⟨t, ht, rfl⟩; exact hroot t ht)
  have hGzero : G = 0 := Polynomial.eq_zero_of_infinite_isRoot G hroots_inf
  have h0 : G.eval u = 0 := by rw [hGzero]; simp
  rw [evG u] at h0
  exact sub_eq_zero.mp h0

end Work.EQ
