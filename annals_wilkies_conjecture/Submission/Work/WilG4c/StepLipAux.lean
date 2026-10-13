/-
  WilG4c / StepLipAux — the assembly infrastructure for the `r`-split of `FLemP`.

  `Work.WilkG4c.StepLip` reduces `FLemP (PY)`, i.e. an F-lemma statement for *all* `r ≥ 0`, to
  two slices:

  * `Work.WilkG4c.StepLipR0` — the `r = 0` slice (`PY 0` is only `|F| ≤ 1`, so the charts are
    built from a cell decomposition with exact hitting);
  * `Work.WilkG4c.StepLipHigh` — the `r ≥ 1` slice (BNZ §5.3).

  Since the witnesses `(a, b, c)` of `FLemP` may be chosen once and for all only *per* `F0`,
  the two slices have to be combined into a single triple of witnesses.  This file provides
  that combination.

  The count polynomial is the merging trick: for polynomials `c₀`, `c₁` over `ℝ` the
  polynomial
  `c₀ * c₀ + c₁ * c₁ + (c₀ + c₁) + 1`
  dominates *both* `c₀` and `c₁` at every real evaluation point, because
  `c₀² + c₁² + c₀ + c₁ + 1 - c₀ = (c₀ + 1/2)² + (c₁ + 1/2)² + 1/2 ≥ 0`
  and symmetrically.  No positivity assumption on `c₀`, `c₁` is needed.
-/
import Mathlib
import Submission.Work.WilG4c.FLemAPI

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- `ChartsOK` is monotone in the format and the degree of the chart graphs. -/
theorem ChartsOK_mono {S : SOMin} {p n k a a' Dg Dg' r : ℕ} {Λ : Set (Fin p → ℝ)}
    {F : Family k p n} {Φ : Finset (ChartTuple p n)} (h : ChartsOK S a Dg r Λ F Φ)
    (ha : a ≤ a') (hD : Dg ≤ Dg') : ChartsOK S a' Dg' r Λ F Φ := by
  intro φ hφ
  obtain ⟨hmem, hrest⟩ := h φ hφ
  exact ⟨fun j => Omega_mono_le S ha hD (hmem j), hrest⟩

/-- `YBound` and `LipOnCube` constrain each member of the family *fibre-wise in the
parameter* `l`: for a fixed `l` they only mention the fibre `F i l`.  Consequently a family
that agrees with another one on a parameter set `Λ` and is replaced outside `Λ` by the
constant `c ∈ (0,1)` still satisfies them, as soon as the *original* family satisfies them on
`Λ` (there is no need for them to hold outside `Λ`).  This is the λ-uniformity device of the
§5.3/§5.5 assemblies: the pieces of a decomposition are only valid on their own λ-projection.

This is the per-parameter-set strengthening of `Work.WilkG4c.iteFamPYLip`. -/
theorem iteFamPYLipOn {p n k : ℕ} (Λ : Set (Fin p → ℝ))
    (F G : Fin k → (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (c : ℝ) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (r : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hPY : ∀ i l, l ∈ Λ → ∀ x ∈ I, ∀ m, m ≤ r → ∀ y ∈ openCube n,
      ‖iteratedFDeriv ℝ m (slice (F i l) x) y‖ ≤ 1)
    (hLip : ∀ i l, l ∈ Λ → ∀ z z', z ∈ openCube (n + 1) → z' ∈ openCube (n + 1) →
      |F i l z - F i l z'| ≤ C * dist z z')
    (hval : ValuesIn01 Λ F)
    (hG : ∀ i l t, l ∈ Λ → G i l t = F i l t)
    (hGc : ∀ i l t, l ∉ Λ → G i l t = c) :
    YBound G r ∧ LipOnCube G C ∧ ValuesIn01 Λ G := by
  have hc0 : (0 : ℝ) < c := hc.1
  have hc1 : c < 1 := hc.2
  refine ⟨?_, ?_, ?_⟩
  · intro i l x hx m hm y hy
    by_cases hl : l ∈ Λ
    · rw [show G i l = F i l from funext fun t => hG i l t hl]
      exact hPY i l hl x hx m hm y hy
    · rw [show slice (G i l) x = fun _ : Fin n → ℝ => c from
        funext fun y' => by simp only [slice_apply]; exact hGc i l (pt x y') hl]
      cases m with
      | zero =>
          rw [norm_iteratedFDeriv_zero]
          show ‖c‖ ≤ 1
          rw [Real.norm_eq_abs, abs_of_pos hc0]
          linarith
      | succ m' =>
          rw [iteratedFDeriv_succ_const]
          simp
  · intro i l z z' hz hz'
    by_cases hl : l ∈ Λ
    · rw [show G i l = F i l from funext fun t => hG i l t hl]
      exact hLip i l hl z z' hz hz'
    · rw [hGc i l z hl, hGc i l z' hl, sub_self, abs_zero]
      exact mul_nonneg hC dist_nonneg
  · intro i l hl x hx
    rw [hG i l x hl]
    exact hval i l hl x hx

/-- The merged count polynomial dominates its left summand. -/
theorem le_mergePoly_left (x E0 E1 : ℝ) (h : x ≤ E0) :
    x ≤ E0 * E0 + E1 * E1 + (E0 + E1) + 1 := by
  nlinarith [sq_nonneg E0, sq_nonneg (E1 + 1 / 2)]

/-- The merged count polynomial dominates its right summand. -/
theorem le_mergePoly_right (x E0 E1 : ℝ) (h : x ≤ E1) :
    x ≤ E0 * E0 + E1 * E1 + (E0 + E1) + 1 := by
  nlinarith [sq_nonneg E1, sq_nonneg (E0 + 1 / 2)]

/-- The `r = 0` slice of `FLemP`, in the shape produced by `Work.WilkG4c.StepLipR0`: the
witnesses are chosen once and for all, and the conclusion is evaluated at `r = 0`. -/
def FLemPZero (S : SOMin) (p N : ℕ) (P : ℕ → ∀ k, Family k p N → Prop) : Prop :=
  ∀ F0 : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
    ∀ (D k : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∀ (Λ : Set (Fin p → ℝ)) (F : Family k p N),
      P 0 k F → (∀ i, famGraph (F i) ∈ S.Ω F0 D (p + N + 1)) → ValuesIn01 Λ F →
      ∃ Φ : Finset (ChartTuple p N),
        (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (0 : ℝ), (k : ℝ), -Real.log ε] c ∧
        ChartsOK S a (MvPolynomial.eval ![D, 0] b) 0 Λ F Φ ∧ Covers Λ F Φ ε

/-- The `r ≥ 1` slice of `FLemP`, in the shape produced by `Work.WilkG4c.StepLipHigh`. -/
def FLemPHigh (S : SOMin) (p N : ℕ) (P : ℕ → ∀ k, Family k p N → Prop) : Prop :=
  ∀ F0 : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
    ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 → 1 ≤ r →
    ∀ (Λ : Set (Fin p → ℝ)) (F : Family k p N),
      P r k F → (∀ i, famGraph (F i) ∈ S.Ω F0 D (p + N + 1)) → ValuesIn01 Λ F →
      ∃ Φ : Finset (ChartTuple p N),
        (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
        ChartsOK S a (MvPolynomial.eval ![D, r] b) r Λ F Φ ∧ Covers Λ F Φ ε

/-- **The `r`-split of `FLemP`.**  The two slices `r = 0` and `r ≥ 1` together give `FLemP`.
The witnesses are the pointwise maximum of the formats, the sum of the degree polynomials and
the merged count polynomial, which dominates both slice evaluations at every point (the
format is monotone and the degree polynomial has `ℕ`-coefficients, so both are monotone). -/
theorem FLemP_of_zero_of_high {S : SOMin} {p N : ℕ} {P : ℕ → ∀ k, Family k p N → Prop}
    (h0 : FLemPZero S p N P) (h1 : FLemPHigh S p N P) : FLemP S p N P := by
  rw [FLemP_iff]
  intro F0
  obtain ⟨a0, b0, c0, h0'⟩ := h0 F0
  obtain ⟨a1, b1, c1, h1'⟩ := h1 F0
  refine ⟨max a0 a1, b0 + b1, (c0 * c0 + c1 * c1) + (c0 + c1) + 1, ?_⟩
  intro D r k ε hε hε1 Λ F hP hΩ hval
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    obtain ⟨Φ, hcard, hok, hcov⟩ := h0' D k ε hε hε1 Λ F hP hΩ hval
    refine ⟨Φ, ?_, ?_, hcov⟩
    · simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, map_one, Nat.cast_zero]
      exact le_mergePoly_left _ _ _ hcard
    · refine ChartsOK_mono hok (le_max_left _ _) ?_
      rw [MvPolynomial.eval_add]
      exact Nat.le_add_right _ _
  · obtain ⟨Φ, hcard, hok, hcov⟩ := h1' D r k ε hε hε1 hr Λ F hP hΩ hval
    refine ⟨Φ, ?_, ?_, hcov⟩
    · simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, map_one]
      exact le_mergePoly_right _ _ _ hcard
    · refine ChartsOK_mono hok (le_max_right _ _) ?_
      rw [MvPolynomial.eval_add]
      exact Nat.le_add_left _ _

end Work.WilkG4c
