import Mathlib

/-!
# Child task (delegated): geometry of the δ-neighbourhood of [-1,1]

Prove `Submission.ChebGeom.exists_zeta_le` (below) and nothing else is
required; helper lemmas may be added freely above it.  No placeholders
may remain in this file at the end.

STATEMENT: for `0 ≤ δ : ℝ` and `w : ℂ` within distance `2·δ` of the real
segment `[-1,1]` (i.e. `∃ t ∈ Icc (-1) 1, ‖w - (t : ℂ)‖ ≤ 2 * δ`),
there exists `ζ : ℂ` with

    (ζ + ζ⁻¹) / 2 = w          (the Joukowski preimage, exact complex equality)
    1 ≤ ‖ζ‖
    ‖ζ‖ ≤ 1 + 2 * Real.sqrt δ + 4 * δ

This is used as follows by the parent: a point `z` within distance `δ` of
`[0,1]` is scaled to `w := 2z - 1`, which is within `2δ` of `[-1,1]`;
this lemma then produces the `ζ` to which the Chebyshev growth bound
(`Submission.ChebGrowth.cheb_growth`, in the sibling file) is applied.

## Mathematical proof route (all elementary; no analysis needed)

1. **Existence of a preimage root.**  The quadratic
   `f(X) := X^2 - C (2 * w) * X + 1 : ℂ[X]` is nonconstant
   (`natDegree = 2`, so `0 < f.degree`); by the fundamental theorem of
   algebra (`Complex.exists_root`, in
   `Mathlib/Analysis/Complex/Polynomial/Basic.lean`) it has a root
   `ζ₀ : ℂ` (`f.IsRoot ζ₀`, i.e. `f.eval ζ₀ = 0`).  Then `ζ₀ ≠ 0`
   (otherwise `f.eval 0 = 1`).  From `ζ₀² - 2wζ₀ + 1 = 0`, divide by
   `ζ₀` (`field_simp`) to get `ζ₀ + ζ₀⁻¹ = 2 * w`, hence
   `(ζ₀ + ζ₀⁻¹)/2 = w`.

   Define the "large" root `ζ := if 1 ≤ ‖ζ₀‖ then ζ₀ else ζ₀⁻¹`
   (or `max` of the two roots — your choice, see 4.).  For either root
   `(ζ + ζ⁻¹)/2 = w` still holds, since `(ζ₀⁻¹ + (ζ₀⁻¹)⁻¹)/2 =
   (ζ₀⁻¹ + ζ₀)/2` (`inv_inv`).  And `1 ≤ ‖ζ‖` by construction (if the
   else branch: `‖ζ₀⁻¹‖ = ‖ζ₀‖⁻¹ ≥ 1` from `norm_inv`, `inv_le_one₀`
   or similar, since `‖ζ₀‖ > 0`).

2. **The identity `‖w-1‖ + ‖w+1‖ = ‖ζ‖ + ‖ζ‖⁻¹`.**  From
   `(ζ + ζ⁻¹)/2 = w`:  `w - 1 = (ζ - 1)²/(2ζ)` and
   `w + 1 = (ζ + 1)²/(2ζ)` (field_simp/ring, using `ζ ≠ 0`).  Taking
   norms (`norm_div`, `norm_pow`, `norm_mul`, `norm_two`):
   `‖w - 1‖ = ‖ζ - 1‖²/(2‖ζ‖)`, `‖w + 1‖ = ‖ζ + 1‖²/(2‖ζ‖)`.  Sum:
   `‖ζ-1‖² + ‖ζ+1‖² = 2‖ζ‖² + 2` (expand `‖a‖²` as `Complex.normSq` /
   `normSq_apply`/`normSq_add`...; or use `‖z‖^2 = z * star z` via
   `Complex.normSq` — e.g. `Complex.normSq_add`, `Complex.normSq_sub`,
   and `Complex.normSq_apply` / `Complex.normSq_eq_norm_sq`:
   `‖z‖^2 = ‖z‖*‖z‖`; work through with
   `ring_nf`/`nlinarith` after `rw [← Complex.normSq_apply]`-style
   identities).  Conclude `‖w-1‖ + ‖w+1‖ = ‖ζ‖ + ‖ζ‖⁻¹`.  Helpers for
   `‖ζ‖ ≠ 0` from `ζ ≠ 0` (`norm_ne_zero_iff`).

3. **From the distance hypothesis to `‖ζ‖ + ‖ζ‖⁻¹ ≤ 2 + 4δ`.**  Pick the
   witness `t ∈ Icc (-1) 1` with `‖w - (t : ℂ)‖ ≤ 2δ`.  Since `t` is
   real and in `[-1,1]`, `‖t - 1‖ = 1 - t` and `‖t + 1‖ = t + 1`
   (or `|t-1| = 1-t`; note `‖(t:ℂ) - 1‖ = |t - 1|` via
   `Complex.norm_ofReal` / `Complex.norm_real` or `norm_eq_abs`-style
   lemmas).  Triangle inequality:
   `‖w - 1‖ ≤ ‖w - t‖ + ‖t - 1‖ ≤ 2δ + (1 - t)`, and
   `‖w + 1‖ ≤ ‖w - t‖ + ‖t + 1‖ ≤ 2δ + (1 + t)`.  Add:
   `‖w-1‖ + ‖w+1‖ ≤ 4δ + 2`.  Combine with 2.:
   `‖ζ‖ + ‖ζ‖⁻¹ ≤ 2 + 4δ`.

4. **Compare with `ρ := 1 + 2δ + 2√(δ(1+δ))`.**  Show `ρ ≥ 1`, `ρ ≠ 0`,
   `ρ⁻¹ = 1 + 2δ - 2√(δ(1+δ))` (multiply out:
   `(1+2δ+2√(δ(1+δ)))·(1+2δ-2√(δ(1+δ))) = (1+2δ)² - 4δ(1+δ) = 1`;
   the second factor is nonnegative: `(1+2δ)² ≥ 4δ(1+δ)` — expand —
   and so equals `ρ⁻¹` by uniqueness of inverse), hence
   `ρ + ρ⁻¹ = 2 + 4δ`.

   From 3.: `‖ζ‖ + ‖ζ‖⁻¹ ≤ ρ + ρ⁻¹`.  Since `1 ≤ ‖ζ‖` and `1 ≤ ρ`
   (and both positive): multiply by `‖ζ‖·ρ` and rearrange
   (`ring_nf`) to `(‖ζ‖ - ρ)·(‖ζ‖·ρ - 1) ≤ 0`, and since
   `‖ζ‖·ρ - 1 ≥ 0` (positivity from `1 ≤ ‖ζ‖`, `1 ≤ ρ`) conclude
   `‖ζ‖ ≤ ρ`.  (Or prove monotonicity of `u ↦ u + u⁻¹` on `[1,∞)`
   algebraically in one go.)

5. **The crude base comparison.**  For `0 ≤ δ`:
   `ρ = 1+2δ+2√(δ(1+δ)) ≤ 1 + 2√δ + 4δ`, i.e. `√(δ(1+δ)) ≤ √δ + δ`.
   Prove by squaring: both sides nonnegative; `(√δ+δ)² =
   δ + 2δ√δ + δ² ≥ δ(1+δ) = δ + δ²` since `2δ√δ ≥ 0`, then
   `Real.sqrt_le_sqrt`, `Real.sqrt_sq_eq_abs`/`Real.sq_sqrt`, positivity.
   Then `‖ζ‖ ≤ ρ ≤ 1 + 2√δ + 4δ`.

That is the entire content; assemble in the natural order.  `hδ0 : 0 ≤ δ`
is used for `Real.sqrt` legality and the comparisons; the statement needs
no upper bound on `δ`.

## Notes on style
- Namespace `Submission.ChebGeom`.
- `noncomputable section`, `open scoped Real Complex Polynomial BigOperators`.
- Mathlib facts likely useful: `Complex.exists_root`,
  `norm_inv`, `inv_inv`, `norm_mul`, `norm_pow`, `norm_div`,
  `norm_ne_zero_iff`, `Real.sqrt_le_sqrt`, `Real.sq_sqrt`,
  `Real.sqrt_sq_eq_abs`, `Complex.normSq`, `pow_le_pow_left₀`,
  `norm_nonneg`, `nlinarith`, `positivity`, `field_simp`, `ring_nf`.
- Do NOT change the statement of `exists_zeta_le`.
-/

noncomputable section

open scoped Real Complex Polynomial BigOperators

namespace Submission.ChebGeom

/-! ## Helper lemmas -/

/-- Monotonicity of `u ↦ u + u⁻¹` on `[1, ∞)`: if `1 ≤ x`, `1 ≤ ρ` and
`x + x⁻¹ ≤ ρ + ρ⁻¹` then `x ≤ ρ`. -/
lemma le_of_inv_add_le {x ρ : ℝ} (hx : 1 ≤ x) (hρ : 1 ≤ ρ)
    (h : x + x⁻¹ ≤ ρ + ρ⁻¹) : x ≤ ρ := by
  by_contra hnot
  have hlt : ρ < x := lt_of_not_ge hnot
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hρ0 : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hxρ : 0 < x * ρ := mul_pos hx0 hρ0
  have hx1 : 1 < x := lt_of_le_of_lt hρ hlt
  have hxρ1 : 1 < x * ρ := by
    have hprod : x ≤ x * ρ := by
      simpa using (mul_le_mul_of_nonneg_left hρ (le_of_lt hx0))
    nlinarith
  have hbig : ρ + ρ⁻¹ < x + x⁻¹ := by
    have hfac : 0 < (x - ρ) * (x * ρ - 1) / (x * ρ) := by
      exact div_pos (mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hxρ1)) hxρ
    have hdiff_eq : x + x⁻¹ - (ρ + ρ⁻¹) = (x - ρ) * (x * ρ - 1) / (x * ρ) := by
      field_simp [hx0.ne', hρ0.ne', hxρ.ne']
      ring
    have hpos : 0 < x + x⁻¹ - (ρ + ρ⁻¹) := by
      rw [hdiff_eq]
      exact hfac
    linarith
  exact (not_le_of_gt hbig) h

/-- `ρ := 1 + 2δ + 2√(δ(1+δ))` satisfies `ρ · (1 + 2δ - 2√(δ(1+δ))) = 1`. -/
lemma rho_mul (δ : ℝ) (hδ0 : 0 ≤ δ) :
    (1 + 2 * δ + 2 * Real.sqrt (δ * (1 + δ))) *
      (1 + 2 * δ - 2 * Real.sqrt (δ * (1 + δ))) = 1 := by
  have hu : 0 ≤ δ * (1 + δ) := mul_nonneg hδ0 (by linarith)
  have hsq : (2 * Real.sqrt (δ * (1 + δ))) ^ 2 = 4 * δ * (1 + δ) := by
    rw [mul_pow, Real.sq_sqrt hu]
    ring
  rw [show (1 + 2 * δ + 2 * Real.sqrt (δ * (1 + δ))) *
        (1 + 2 * δ - 2 * Real.sqrt (δ * (1 + δ)))
      = (1 + 2 * δ) ^ 2 - (2 * Real.sqrt (δ * (1 + δ))) ^ 2 by ring]
  rw [hsq]
  ring

/-- `ρ := 1 + 2δ + 2√(δ(1+δ)) ≥ 1` when `0 ≤ δ`. -/
lemma rho_ge_one (δ : ℝ) (hδ0 : 0 ≤ δ) : 1 ≤ 1 + 2 * δ + 2 * Real.sqrt (δ * (1 + δ)) := by
  have h1 : 0 ≤ 2 * δ := by nlinarith
  have h2 : 0 ≤ 2 * Real.sqrt (δ * (1 + δ)) := by
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  nlinarith

/-- `ρ := 1 + 2δ + 2√(δ(1+δ)) ≠ 0` when `0 ≤ δ`. -/
lemma rho_ne_zero (δ : ℝ) (hδ0 : 0 ≤ δ) :
    (1 + 2 * δ + 2 * Real.sqrt (δ * (1 + δ))) ≠ 0 := by
  have : 0 < 1 + 2 * δ + 2 * Real.sqrt (δ * (1 + δ)) :=
    lt_of_lt_of_le zero_lt_one (rho_ge_one δ hδ0)
  exact ne_of_gt this

/-- The exact inverse of `ρ := 1 + 2δ + 2√(δ(1+δ))`. -/
lemma rho_inv (δ : ℝ) (hδ0 : 0 ≤ δ) :
    (1 + 2 * δ + 2 * Real.sqrt (δ * (1 + δ)))⁻¹ =
      1 + 2 * δ - 2 * Real.sqrt (δ * (1 + δ)) := by
  exact (eq_inv_of_mul_eq_one_right (rho_mul δ hδ0)).symm

/-- `ρ + ρ⁻¹ = 2 + 4δ`. -/
lemma rho_add_inv (δ : ℝ) (hδ0 : 0 ≤ δ) :
    1 + 2 * δ + 2 * Real.sqrt (δ * (1 + δ)) +
      (1 + 2 * δ + 2 * Real.sqrt (δ * (1 + δ)))⁻¹ = 2 + 4 * δ := by
  rw [rho_inv δ hδ0]
  ring

/-- `√(δ(1+δ)) ≤ √δ + δ` for `0 ≤ δ`. -/
lemma sqrt_bound (δ : ℝ) (hδ0 : 0 ≤ δ) :
    Real.sqrt (δ * (1 + δ)) ≤ Real.sqrt δ + δ := by
  have hu : 0 ≤ δ * (1 + δ) := mul_nonneg hδ0 (by linarith)
  have hsq : (Real.sqrt (δ * (1 + δ))) ^ 2 ≤ (Real.sqrt δ + δ) ^ 2 := by
    calc (Real.sqrt (δ * (1 + δ))) ^ 2 = δ * (1 + δ) := Real.sq_sqrt hu
         _ ≤ (Real.sqrt δ + δ) ^ 2 := by
            rw [show (Real.sqrt δ + δ) ^ 2 = (Real.sqrt δ) ^ 2 + 2 * Real.sqrt δ * δ + δ ^ 2 by ring]
            rw [Real.sq_sqrt hδ0]
            nlinarith [mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (Real.sqrt_nonneg δ)) hδ0]
  calc Real.sqrt (δ * (1 + δ)) = Real.sqrt ((Real.sqrt (δ * (1 + δ))) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        _ ≤ Real.sqrt ((Real.sqrt δ + δ) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = Real.sqrt δ + δ := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg δ) hδ0)]

/-- `ρ := 1 + 2δ + 2√(δ(1+δ)) ≤ 1 + 2√δ + 4δ` when `0 ≤ δ`. -/
lemma rho_le_target (δ : ℝ) (hδ0 : 0 ≤ δ) :
    1 + 2 * δ + 2 * Real.sqrt (δ * (1 + δ)) ≤ 1 + 2 * Real.sqrt δ + 4 * δ := by
  have hs := sqrt_bound δ hδ0
  nlinarith

/-- The quadratic `X² - 2wX + 1` over `ℂ` has a nonzero root `z` with
`(z + z⁻¹)/2 = w`. -/
lemma quad_root (w : ℂ) :
    ∃ z : ℂ, z ^ 2 - 2 * w * z + 1 = 0 ∧ z ≠ 0 ∧ (z + z⁻¹) / 2 = w := by
  let p : ℂ[X] := Polynomial.X ^ 2 - Polynomial.C (2 * w) * Polynomial.X + 1
  have hp2 : p = Polynomial.X * (Polynomial.X - Polynomial.C (2 * w)) + 1 := by
    simp [p]
    ring
  have hnd1 : (Polynomial.X - Polynomial.C (2 * w)).natDegree = 1 := by
    simpa using (Polynomial.natDegree_X_sub_C (2 * w))
  have hnd : p.natDegree = 2 := by
    rw [hp2]
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · rw [Polynomial.natDegree_mul Polynomial.X_ne_zero (Polynomial.X_sub_C_ne_zero (2 * w))]
      rw [hnd1]
      norm_num
    · rw [Polynomial.natDegree_mul Polynomial.X_ne_zero (Polynomial.X_sub_C_ne_zero (2 * w))]
      norm_num
  have hp : p ≠ 0 := by
    intro hp0
    rw [hp0] at hnd
    norm_num at hnd
  have hdeg : 0 < p.degree := by
    rw [Polynomial.degree_eq_natDegree hp, hnd]
    norm_num
  obtain ⟨z, hzroot⟩ := Complex.exists_root hdeg
  have hzroot' : z ^ 2 - 2 * w * z + 1 = 0 := by
    have h := Polynomial.IsRoot.eq_zero hzroot
    simpa [p] using h
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz] at hzroot'
    norm_num at hzroot'
  have h2 : z ^ 2 + 1 = 2 * w * z := by
    have hh := congrArg (fun x : ℂ => x + 2 * w * z) hzroot'
    have h3 : z ^ 2 - 2 * w * z + 1 + 2 * w * z = z ^ 2 + 1 := by ring
    rw [h3] at hh
    simpa using hh
  have hmain : z + z⁻¹ = 2 * w := by
    apply mul_left_cancel₀ hz0
    calc z * (z + z⁻¹) = z * z + z * z⁻¹ := by rw [mul_add]
         _ = z * z + 1 := by rw [mul_inv_cancel₀ hz0]
         _ = z ^ 2 + 1 := by ring
         _ = 2 * w * z := h2
         _ = z * (2 * w) := by ring
  have hzeq : (z + z⁻¹) / 2 = w := by
    calc (z + z⁻¹) / 2 = (2 * w) / 2 := by rw [hmain]
         _ = w := by field_simp
  exact ⟨z, hzroot', hz0, hzeq⟩

/-- Among the two Joukowski preimages of `w` choose one of modulus `≥ 1`;
it is nonzero and still satisfies `(ζ + ζ⁻¹)/2 = w`. -/
lemma choose_zeta (w : ℂ) : ∃ ζ : ℂ, ζ ≠ 0 ∧ (ζ + ζ⁻¹) / 2 = w ∧ 1 ≤ ‖ζ‖ := by
  rcases quad_root w with ⟨z, hzroot', hz0, hzeq⟩
  by_cases hbig : 1 ≤ ‖z‖
  · exact ⟨z, hz0, hzeq, hbig⟩
  · have hle : ‖z‖ < 1 := lt_of_not_ge hbig
    refine ⟨z⁻¹, inv_ne_zero hz0, ?_, ?_⟩
    · calc (z⁻¹ + (z⁻¹)⁻¹) / 2 = (z⁻¹ + z) / 2 := by rw [inv_inv]
         _ = (z + z⁻¹) / 2 := by ring
         _ = w := hzeq
    · rw [norm_inv]
      have hzpos : 0 < ‖z‖ := (norm_pos_iff).mpr hz0
      have hle1 : ‖z‖ ≤ 1 := le_of_lt hle
      -- 1 ≤ ‖z‖⁻¹ : inverse is antitone on positives
      simpa using ((inv_le_inv₀ (a := (1 : ℝ)) (b := ‖z‖) zero_lt_one hzpos).mpr hle1)

/-- Joukowski identity: if `w = (ζ + ζ⁻¹)/2` and `ζ ≠ 0`, then
`‖w-1‖ + ‖w+1‖ = ‖ζ‖ + ‖ζ‖⁻¹`. -/
lemma joukowski_norm_identity {w ζ : ℂ} (hζ0 : ζ ≠ 0) (hw : (ζ + ζ⁻¹) / 2 = w) :
    ‖w - 1‖ + ‖w + 1‖ = ‖ζ‖ + ‖ζ‖⁻¹ := by
  have hw1 : w - 1 = (ζ - 1) ^ 2 / (2 * ζ) := by
    rw [← hw]
    field_simp [hζ0]
    ring
  have hw2 : w + 1 = (ζ + 1) ^ 2 / (2 * ζ) := by
    rw [← hw]
    field_simp [hζ0]
    ring
  have hn1 : ‖w - 1‖ = ‖ζ - 1‖ ^ 2 / (2 * ‖ζ‖) := by
    rw [hw1]
    rw [norm_div, norm_pow, norm_mul]
    norm_num
  have hn2 : ‖w + 1‖ = ‖ζ + 1‖ ^ 2 / (2 * ‖ζ‖) := by
    rw [hw2]
    rw [norm_div, norm_pow, norm_mul]
    norm_num
  have hns : Complex.normSq (ζ - 1) + Complex.normSq (ζ + 1) =
      2 * Complex.normSq ζ + 2 * Complex.normSq 1 := by
    rw [Complex.normSq_sub, Complex.normSq_add]
    simp
    ring
  have hsq2 : ‖ζ - 1‖ ^ 2 + ‖ζ + 1‖ ^ 2 = 2 * ‖ζ‖ ^ 2 + 2 := by
    calc ‖ζ - 1‖ ^ 2 + ‖ζ + 1‖ ^ 2
        = Complex.normSq (ζ - 1) + Complex.normSq (ζ + 1) := by
            simp only [← Complex.normSq_eq_norm_sq]
      _ = 2 * Complex.normSq ζ + 2 * Complex.normSq 1 := hns
      _ = 2 * ‖ζ‖ ^ 2 + 2 := by
            rw [Complex.normSq_eq_norm_sq, Complex.normSq_one]
            norm_num
  have hsum : ‖w - 1‖ + ‖w + 1‖ = (‖ζ - 1‖ ^ 2 + ‖ζ + 1‖ ^ 2) / (2 * ‖ζ‖) := by
    rw [hn1, hn2]
    ring
  have hζnorm0 : ‖ζ‖ ≠ 0 := (norm_ne_zero_iff).mpr hζ0
  calc ‖w - 1‖ + ‖w + 1‖ = (2 * ‖ζ‖ ^ 2 + 2) / (2 * ‖ζ‖) := by
         rw [hsum, hsq2]
       _ = ‖ζ‖ + ‖ζ‖⁻¹ := by
         field_simp [hζnorm0]

/-- A point `w` within `2δ` of a real `t ∈ [-1,1]` satisfies
`‖w-1‖ + ‖w+1‖ ≤ 2 + 4δ`. -/
lemma segment_norm_sum_le {δ : ℝ} {w : ℂ} {t : ℝ}
    (ht1 : -1 ≤ t) (ht2 : t ≤ 1) (hwt : ‖w - (t : ℂ)‖ ≤ 2 * δ) :
    ‖w - 1‖ + ‖w + 1‖ ≤ 2 + 4 * δ := by
  have ht1' : ‖(t : ℂ) - 1‖ = 1 - t := by
    have hsub : (t : ℂ) - 1 = ((t - 1 : ℝ) : ℂ) := by
      simp [Complex.ofReal_sub, Complex.ofReal_one]
    rw [hsub, Complex.norm_real, Real.norm_eq_abs]
    have ht0 : t - 1 ≤ 0 := by linarith
    rw [abs_of_nonpos ht0]
    ring
  have ht2' : ‖(t : ℂ) + 1‖ = 1 + t := by
    have hsub : (t : ℂ) + 1 = ((t + 1 : ℝ) : ℂ) := by
      simp [Complex.ofReal_add, Complex.ofReal_one]
    rw [hsub, Complex.norm_real, Real.norm_eq_abs]
    have ht0 : 0 ≤ t + 1 := by linarith
    rw [abs_of_nonneg ht0]
    ring
  have hb1 : ‖w - 1‖ ≤ ‖w - (t : ℂ)‖ + ‖(t : ℂ) - 1‖ := by
    have hcc : w - 1 = (w - (t : ℂ)) + ((t : ℂ) - 1) := by ring
    rw [hcc]
    exact norm_add_le _ _
  have hb2 : ‖w + 1‖ ≤ ‖w - (t : ℂ)‖ + ‖(t : ℂ) + 1‖ := by
    have hcc : w + 1 = (w - (t : ℂ)) + ((t : ℂ) + 1) := by ring
    rw [hcc]
    exact norm_add_le _ _
  have h1 : ‖w - 1‖ ≤ 2 * δ + (1 - t) := by
    calc ‖w - 1‖ ≤ ‖w - (t : ℂ)‖ + ‖(t : ℂ) - 1‖ := hb1
         _ ≤ 2 * δ + (1 - t) := by
              rw [ht1']
              linarith
  have h2 : ‖w + 1‖ ≤ 2 * δ + (1 + t) := by
    calc ‖w + 1‖ ≤ ‖w - (t : ℂ)‖ + ‖(t : ℂ) + 1‖ := hb2
         _ ≤ 2 * δ + (1 + t) := by
              rw [ht2']
              linarith
  nlinarith

/-- **Preimage of the fattened segment.**  A point `w` within `2δ` of the
real segment `[-1,1]` is the Joukowski image of some `ζ` with
`1 ≤ ‖ζ‖ ≤ 1 + 2√δ + 4δ`. -/
theorem exists_zeta_le {δ : ℝ} (hδ0 : 0 ≤ δ) {w : ℂ}
    (hdist : ∃ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 ∧ ‖w - (t : ℂ)‖ ≤ 2 * δ) :
    ∃ ζ : ℂ, (ζ + ζ⁻¹) / 2 = w ∧ 1 ≤ ‖ζ‖ ∧
      ‖ζ‖ ≤ 1 + 2 * Real.sqrt δ + 4 * δ := by
  obtain ⟨ζ, hζ0, hwζ, hζge1⟩ := choose_zeta w
  have hid := joukowski_norm_identity hζ0 hwζ
  have hbound : ‖ζ‖ + ‖ζ‖⁻¹ ≤ 2 + 4 * δ := by
    rcases hdist with ⟨t, ht, hwt⟩
    have hseg := segment_norm_sum_le ht.1 ht.2 hwt
    linarith
  have hρge1 : 1 ≤ 1 + 2 * δ + 2 * Real.sqrt (δ * (1 + δ)) := rho_ge_one δ hδ0
  have hρsum : 1 + 2 * δ + 2 * Real.sqrt (δ * (1 + δ)) +
      (1 + 2 * δ + 2 * Real.sqrt (δ * (1 + δ)))⁻¹ = 2 + 4 * δ :=
    rho_add_inv δ hδ0
  have hle : ‖ζ‖ ≤ 1 + 2 * δ + 2 * Real.sqrt (δ * (1 + δ)) :=
    le_of_inv_add_le hζge1 hρge1 (by
      rw [hρsum]
      exact hbound)
  have hρt : 1 + 2 * δ + 2 * Real.sqrt (δ * (1 + δ)) ≤ 1 + 2 * Real.sqrt δ + 4 * δ :=
    rho_le_target δ hδ0
  exact ⟨ζ, hwζ, hζge1, le_trans hle hρt⟩

end Submission.ChebGeom

end
