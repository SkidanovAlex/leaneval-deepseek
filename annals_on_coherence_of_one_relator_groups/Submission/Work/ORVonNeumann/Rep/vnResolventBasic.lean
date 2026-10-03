import Mathlib

/-!
# Basic estimates for the resolvent of a nonnegative self-adjoint operator

Let `S : H →L[ℂ] H` be a self-adjoint operator on a complex Hilbert space `H` whose
quadratic form is nonnegative, `0 ≤ re ⟪S u, u⟫` for all `u`, and let `D c` be a two-sided
inverse of `c • 1 + S` for every `c > 0`.

Three elementary facts are proved here, all of them direct consequences of the lower bound
`c * ‖u‖ ≤ ‖(c • 1 + S) u‖`:

* `resolvent_norm_le` — `‖(c • D c) u‖ ≤ ‖u‖`, i.e. the Yosida approximation `c (c + S)⁻¹`
  is a contraction;
* `resolvent_fixes_kernel` — `c (c + S)⁻¹` fixes `ker S` pointwise;
* `resolvent_range_le` — `‖(c • D c) (S v)‖ ≤ 2 c ‖v‖`, the quantitative vanishing on the
  range of `S` that, combined with the density of `ran S` in `(ker S)ᗮ` and the contraction
  bound, yields the strong convergence `c (c + S)⁻¹ u → 0` for `u ∈ (ker S)ᗮ`.

The last ingredients are assembled in `vnResolventBasic`.
-/

set_option autoImplicit false

open scoped InnerProductSpace

namespace Work.ORVonNeumann.Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- For a self-adjoint operator `S` with nonnegative quadratic form the shifted operator
`c • 1 + S` satisfies the lower bound `c * ‖u‖ ≤ ‖(c • 1 + S) u‖` for every real `c`. -/
lemma norm_smul_one_add_le (S : H →L[ℂ] H) (hS : ∀ u : H, 0 ≤ (inner ℂ (S u) u).re) (u : H) :
    ∀ c : ℝ, c * ‖u‖ ≤ ‖(c • 1 + S) u‖ := by
  intro c
  have hself : (inner ℂ u u).re = ‖u‖ ^ 2 := by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) u
  have hre : (inner ℂ ((c • 1 + S) u) u).re = c * ‖u‖ ^ 2 + (inner ℂ (S u) u).re := by
    have hcu : c • u = (c : ℂ) • u := (Complex.coe_smul c u).symm
    rw [show (c • 1 + S) u = c • u + S u by simp, hcu, inner_add_left, inner_smul_left,
      Complex.add_re, Complex.mul_re, Complex.conj_ofReal, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hself]
  have hlower : c * ‖u‖ ^ 2 ≤ (inner ℂ ((c • 1 + S) u) u).re := by rw [hre]; nlinarith [hS u]
  have hub : (inner ℂ ((c • 1 + S) u) u).re ≤ ‖(c • 1 + S) u‖ * ‖u‖ :=
    le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)
  have hkey : c * ‖u‖ ^ 2 ≤ ‖(c • 1 + S) u‖ * ‖u‖ := le_trans hlower hub
  rcases eq_or_lt_of_le (norm_nonneg u) with h | h
  · rw [← h, mul_zero]; exact norm_nonneg _
  · exact le_of_mul_le_mul_right (by nlinarith [hkey]) h

/-- The Yosida approximation `c (c + S)⁻¹` of a nonnegative self-adjoint operator is a
contraction: `‖(c • D c) u‖ ≤ ‖u‖`. -/
lemma resolvent_norm_le (S : H →L[ℂ] H) (hS : ∀ u : H, 0 ≤ (inner ℂ (S u) u).re)
    (D : ℝ → H →L[ℂ] H) (hD : ∀ c : ℝ, 0 < c → (c • 1 + S) * D c = 1 ∧ D c * (c • 1 + S) = 1)
    {c : ℝ} (hc : 0 < c) (u : H) : ‖(c • D c) u‖ ≤ ‖u‖ := by
  have h1 : (c • 1 + S) (D c u) = u := by simpa using DFunLike.congr_fun (hD c hc).1 u
  have hA : (c • 1 + S) ((c • D c) u) = c • u := by
    have hw : (c • D c) u = (c : ℂ) • (D c u) := by
      rw [show (c • D c) u = c • (D c u) from rfl, ← Complex.coe_smul]
    rw [hw, map_smul, h1, Complex.coe_smul]
  have hb := norm_smul_one_add_le S hS ((c • D c) u) c
  rw [hA, norm_smul, Real.norm_of_nonneg (le_of_lt hc)] at hb
  exact le_of_mul_le_mul_left hb hc

/-- On the range of `S` the Yosida approximation vanishes at rate `O(c)`:
`‖(c • D c) (S v)‖ ≤ 2 c ‖v‖`. -/
lemma resolvent_range_le (S : H →L[ℂ] H) (hS : ∀ u : H, 0 ≤ (inner ℂ (S u) u).re)
    (D : ℝ → H →L[ℂ] H) (hD : ∀ c : ℝ, 0 < c → (c • 1 + S) * D c = 1 ∧ D c * (c • 1 + S) = 1)
    {c : ℝ} (hc : 0 < c) (v : H) : ‖(c • D c) (S v)‖ ≤ 2 * c * ‖v‖ := by
  have hD2 : D c ((c • 1 + S) v) = v := by simpa using DFunLike.congr_fun (hD c hc).2 v
  have hsplit : S v = (c • 1 + S) v - c • v := by
    rw [show (c • 1 + S) v = c • v + S v by simp]; abel
  have hDsplit : D c (S v) = v - c • (D c v) := by
    rw [hsplit, map_sub, hD2]
    congr 1
    rw [show c • v = (c : ℂ) • v from (Complex.coe_smul c v).symm, map_smul, Complex.coe_smul]
  have hpart1' : ‖c • (D c v)‖ ≤ ‖v‖ := resolvent_norm_le S hS D hD hc v
  calc ‖(c • D c) (S v)‖ = ‖c • (D c (S v))‖ := rfl
    _ = ‖c • (v - c • (D c v))‖ := by rw [hDsplit]
    _ = c * ‖v - c • (D c v)‖ := by rw [norm_smul, Real.norm_of_nonneg (le_of_lt hc)]
    _ ≤ c * (‖v‖ + ‖c • (D c v)‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (le_of_lt hc)
    _ ≤ c * (‖v‖ + ‖v‖) :=
        mul_le_mul_of_nonneg_left (add_le_add (le_refl ‖v‖) hpart1') (le_of_lt hc)
    _ = 2 * c * ‖v‖ := by ring

/-- The Yosida approximation `c (c + S)⁻¹` fixes the kernel of `S` pointwise. -/
lemma resolvent_fixes_kernel (S : H →L[ℂ] H) (D : ℝ → H →L[ℂ] H)
    (hD : ∀ c : ℝ, 0 < c → (c • 1 + S) * D c = 1 ∧ D c * (c • 1 + S) = 1)
    {c : ℝ} (hc : 0 < c) (u : H) (hu : u ∈ S.ker) : (c • D c) u = u := by
  have h2 : D c ((c • 1 + S) u) = u := by simpa using DFunLike.congr_fun (hD c hc).2 u
  have hSu : S u = 0 := hu
  have hAu : (c • 1 + S) u = c • u := by
    rw [show (c • 1 + S) u = c • u + S u by simp, hSu, add_zero]
  have h2' : D c (c • u) = u := by rw [← hAu]; exact h2
  calc (c • D c) u = c • (D c u) := rfl
    _ = (c : ℂ) • (D c u) := (Complex.coe_smul c (D c u)).symm
    _ = D c ((c : ℂ) • u) := (map_smul (D c) (c : ℂ) u).symm
    _ = D c (c • u) := by rw [Complex.coe_smul]
    _ = u := h2'

theorem vnResolventBasic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : H →L[ℂ] H) (hadj : ContinuousLinearMap.adjoint S = S) (hS : ∀ u : H, 0 ≤ (inner ℂ (S u) u).re) (D : ℝ → H →L[ℂ] H) (hD : ∀ c : ℝ, 0 < c → (c • 1 + S) * D c = 1 ∧ D c * (c • 1 + S) = 1) : (∀ c : ℝ, 0 < c → ∀ u : H, ‖(c • D c) u‖ ≤ ‖u‖) ∧ (∀ c : ℝ, 0 < c → ∀ u ∈ S.ker, (c • D c) u = u) ∧ (∀ u ∈ S.kerᗮ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ c : ℝ, 0 < c → c < δ → ‖(c • D c) u‖ < ε) := by
  have hker : S.kerᗮ = S.range.topologicalClosure := by
    have h := ContinuousLinearMap.orthogonal_ker S
    rw [hadj] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · exact fun c hc u => resolvent_norm_le S hS D hD hc u
  · exact fun c hc u hu => resolvent_fixes_kernel S D hD hc u hu
  · intro u hu ε hε
    have hmem : u ∈ closure ((S.range : Submodule ℂ H) : Set H) := by
      rw [← Submodule.topologicalClosure_coe, ← hker]
      exact hu
    rw [Metric.mem_closure_iff] at hmem
    obtain ⟨w, hws, hdist⟩ := hmem (ε / 2) (by linarith)
    obtain ⟨v, hv⟩ := hws
    have hdist' : ‖u - S v‖ < ε / 2 := by
      rw [← hv, dist_eq_norm] at hdist
      simpa using hdist
    let δ : ℝ := ε / (4 * (‖v‖ + 1))
    have hδpos : 0 < δ := by
      simp only [δ]; apply div_pos hε; positivity
    refine ⟨δ, hδpos, ?_⟩
    intro c hc hclt
    have h2cv : 2 * c * ‖v‖ ≤ ε / 2 := by
      have h1 : 2 * c * ‖v‖ ≤ 2 * δ * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
        nlinarith [hc, hclt]
      have h2 : 2 * δ * ‖v‖ ≤ 2 * δ * (‖v‖ + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [norm_nonneg v]
      have h3 : 2 * δ * (‖v‖ + 1) = ε / 2 := by
        simp only [δ]; field_simp; ring
      linarith [h1, h2, h3.le]
    have htri : ‖(c • D c) u‖ ≤ ‖(c • D c) (u - S v)‖ + ‖(c • D c) (S v)‖ := by
      have hsum : (c • D c) (u - S v) + (c • D c) (S v) = (c • D c) u := by
        rw [← map_add, sub_add_cancel]
      calc ‖(c • D c) u‖ = ‖(c • D c) (u - S v) + (c • D c) (S v)‖ := by rw [← hsum]
        _ ≤ ‖(c • D c) (u - S v)‖ + ‖(c • D c) (S v)‖ := norm_add_le _ _
    have hA : ‖(c • D c) (u - S v)‖ ≤ ‖u - S v‖ := resolvent_norm_le S hS D hD hc _
    have hB : ‖(c • D c) (S v)‖ ≤ 2 * c * ‖v‖ := resolvent_range_le S hS D hD hc v
    linarith [htri, hA, hB, h2cv, hdist']

end Work.ORVonNeumann.Rep
