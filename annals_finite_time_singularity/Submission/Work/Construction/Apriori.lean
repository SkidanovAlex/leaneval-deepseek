/-
# The CONSTRUCTION area: the a-priori estimate of §Modulation (tex 1387-1578)

This module states and proves the a-priori estimate on the `ℋ⁴` inner product of the
`g`-equation with `g` (Propositions `N0Estimate`, `NEstimate`, `N*Estimate`,
`innerproductestimate` and the corollary following them, tex 1425-1547), together with the
coercivity corollary that turns the estimate into the bound `|g|_{ℋ⁴} ≤ 2Cα²` used by the
fixed-point argument.

## Structure of the interface

The paper's proof of each Proposition is a term-by-term estimate: every summand of `N₀`
(tex `\eqref{N0}`), `N` (tex `\eqref{N}`) and `N_*` (tex `\eqref{N*}`) is bounded using one of
the auxiliary propositions of §`H2` (`L12H`, `Transport1-3`, `SpecialTransport`,
`WProductRule`, `RemovingL12_R`, `RemovingL12_U`, `PhiStarRegularity`, `WtoH`,
`DivisionBySin`) and the results are added up.

Accordingly, this module *fixes the interface* of that argument: the structures `N0Inputs`,
`NInputs`, `NstarInputs` carry, as fields, a bound for each of the paper's summands
(the docstrings name the paper's proposition that supplies it), and the four Theorems below
are proved *from those fields* by the triangle inequality.  This is the "precisely named
input" discipline: the residual of this chapter is exactly the collection of fields of the
three structures, each of which is a paper proposition about a *single* summand — strictly
weaker than the conclusion, and independently provable by the areas that own it.

Constants: `C > 0` is a **universal** constant, i.e. independent of `α` (the paper's `C`);
the estimates hold for `0 < α ≤ 1`, the paper's range.  The modulation constants `μ, λ` are
free parameters of every statement; they enter only through `N_*` (where the paper's choice
`μ + λ + μλ = -μ` is the hypothesis `hlam`).  The condition `|μ| ≤ 1/2` is *not* needed here:
it belongs to the Stability layer, which reuses this file with time-dependent coefficients.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Construction.Defs
import Submission.Work.Construction.Basic
import Submission.Work.Construction.Equation
import Submission.Work.Construction.Terms
import Submission.Work.Construction.GammaN0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

set_option autoImplicit false

/-- The `ℋ⁴`-norm `|g|_{ℋ⁴}` of the estimates of §Modulation. -/
def H4N (α : ℝ) (g : ℝ → ℝ → ℝ) : ℝ := Work.Spaces.HkNorm α 4 g

theorem H4N_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) : 0 ≤ H4N α g :=
  Work.Spaces.HkNorm_nonneg α 4 g

/-- For `0 < α ≤ 1` the powers of `α` decrease with the exponent: `y ≤ z → α^z ≤ α^y`.
Used to fit the individual bounds into the shape of the paper's propositions. -/
theorem rpow_le_of_le_one {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {y z : ℝ} (hyz : y ≤ z) :
    α ^ z ≤ α ^ y := by
  have h : α ^ z = α ^ y * α ^ (z - y) := by
    rw [← Real.rpow_add hα]
    ring_nf
  rw [h]
  calc α ^ y * α ^ (z - y) ≤ α ^ y * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hα.le y)
        exact Real.rpow_le_one hα.le hα1 (by linarith)
    _ = α ^ y := by ring

/-- `α^{-1/2} ≤ α^{-3/2}` for `0 < α ≤ 1`. -/
theorem rpow_neg_half_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(3 / 2 : ℝ)) :=
  rpow_le_of_le_one hα hα1 (by norm_num)

theorem rpow_neg_three_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ^ (-(3 / 2 : ℝ)) ≤ α ^ (-(5 / 2 : ℝ)) :=
  rpow_le_of_le_one hα hα1 (by norm_num)

/-- The triangle inequality for a sum of five terms. -/
theorem abs_sum_le_five (a b c d e : ℝ) :
    |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h1 := abs_add_le (a + b + c + d) e
  have h2 := abs_add_le (a + b + c) d
  have h3 := abs_add_le (a + b) c
  have h4 := abs_add_le a b
  nlinarith [h1, h2, h3, h4, abs_nonneg (a + b + c + d), abs_nonneg (a + b + c),
    abs_nonneg (a + b)]

/-- The triangle inequality for a sum of four terms. -/
theorem abs_sum_le_four (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  nlinarith [h1, h2, h3, abs_nonneg (a + b + c), abs_nonneg (a + b)]

/-! ## The inputs for `N₀` -/

/-- The per-summand inputs for Proposition `N0Estimate` (tex 1433-1436).  Each field is one of
the paper's estimates for one summand of `\eqref{N0}`:

* `h12`: `I^{N₀}_1 + I^{N₀}_2` is `O(α²)` in `ℋ⁴` — the "direct calculation" using the exact
  form of `Γ` (tex 1398-1402; here via `N0_first_two_eq`);
* `h3`: `|(I^{N₀}_3,g)_{ℋ⁴}| ≤ Cα^{-3/2}|g|³` (tex 1406: `HProductRule` + `L12H`);
* `h4`: the two halves of `I^{N₀}_4` (tex 1410-1414: `WProductRule` + `L12H` and
  `Transport1` + `L12H`), merged into one bound;
* `h5`: the two halves of `I^{N₀}_5` (tex 1416-1421: `WProductRule` + `L12H` and
  `Transport2` + `L12H`), merged;
* `h6`: `I^{N₀}_6` (tex 1423: `Transport3`). -/
structure N0Inputs (α : ℝ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ) (C : ℝ)
    (F g : ℝ → ℝ → ℝ) : Prop where
  h12 : H4N α (N01 α F g + N02 α F g) ≤ C * α ^ 2
  h3 : |IP (N03 α F g) g| ≤ C * α ^ (-(3 / 2 : ℝ)) * H4N α g ^ 3
  h4 : |IP (N04 α F g) g|
    ≤ C * (Real.sqrt α + α ^ (-(3 / 2 : ℝ)) * H4N α g) * H4N α g ^ 2
  h5 : |IP (N05 α F g) g|
    ≤ C * (Real.sqrt α + α ^ (-(1 / 2 : ℝ)) * H4N α g) * H4N α g ^ 2
  h6 : |IP (N06 α F g) g| ≤ C * Real.sqrt α * H4N α g ^ 2

/-- **Proposition `N0Estimate`** (tex 1433-1436): `|(N₀,g)_{ℋ⁴}| ≤ C(α²|g| + √α|g|² +
α^{-3/2}|g|³)`, with `C` universal. -/
theorem N0Estimate {α C : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 < C)
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} (hIP : IsH4IP α IP) {F g : ℝ → ℝ → ℝ}
    (hin : N0Inputs α IP C F g) :
    |IP (N0 α F g) g|
      ≤ 8 * C * (α ^ 2 * H4N α g + Real.sqrt α * H4N α g ^ 2
        + α ^ (-(3 / 2 : ℝ)) * H4N α g ^ 3) := by
  set X := H4N α g with hXdef
  have hX : 0 ≤ X := H4N_nonneg α g
  have hsum : IP (N0 α F g) g = IP (N01 α F g + N02 α F g) g + IP (N03 α F g) g
      + IP (N04 α F g) g + IP (N05 α F g) g + IP (N06 α F g) g := by
    rw [N0_eq_sum, hIP.add_fst, hIP.add_fst, hIP.add_fst, hIP.add_fst, hIP.add_fst]
    try ring
  have hcs : |IP (N01 α F g + N02 α F g) g| ≤ C * α ^ 2 * X := by
    have h1 := hIP.cs (N01 α F g + N02 α F g) g
    have h2 : Work.Spaces.HkNorm α 4 (N01 α F g + N02 α F g) ≤ C * α ^ 2 := hin.h12
    have h3 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 4 (N01 α F g + N02 α F g) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    have h4 : (0 : ℝ) < C * α ^ 2 := mul_pos hC (pow_pos hα 2)
    calc |IP (N01 α F g + N02 α F g) g|
        ≤ Work.Spaces.HkNorm α 4 (N01 α F g + N02 α F g) * Work.Spaces.HkNorm α 4 g := h1
      _ ≤ (C * α ^ 2) * X := mul_le_mul h2 le_rfl hX h4.le
      _ = C * α ^ 2 * X := by ring
  have htri : |IP (N0 α F g) g| ≤ |IP (N01 α F g + N02 α F g) g| + |IP (N03 α F g) g|
      + |IP (N04 α F g) g| + |IP (N05 α F g) g| + |IP (N06 α F g) g| := by
    rw [hsum]
    exact abs_sum_le_five _ _ _ _ _
  have hhalf : α ^ (-(1 / 2 : ℝ)) * X ^ 3 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 3 :=
    mul_le_mul_of_nonneg_right (rpow_neg_half_le hα hα1) (by positivity)
  have h4' : |IP (N04 α F g) g|
      ≤ C * Real.sqrt α * X ^ 2 + C * α ^ (-(3 / 2 : ℝ)) * X ^ 3 := by
    refine le_trans hin.h4 ?_
    nlinarith [hX]
  have h5' : |IP (N05 α F g) g|
      ≤ C * Real.sqrt α * X ^ 2 + C * α ^ (-(3 / 2 : ℝ)) * X ^ 3 := by
    refine le_trans hin.h5 ?_
    nlinarith [hhalf, hX]
  have h6' : |IP (N06 α F g) g| ≤ C * Real.sqrt α * X ^ 2 := hin.h6
  have h3' : |IP (N03 α F g) g| ≤ C * α ^ (-(3 / 2 : ℝ)) * X ^ 3 := hin.h3
  have hpa : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hn1 : (0 : ℝ) ≤ C * α ^ 2 * X := by positivity
  have hn2 : (0 : ℝ) ≤ C * Real.sqrt α * X ^ 2 := by positivity
  have hn3 : (0 : ℝ) ≤ C * α ^ (-(3 / 2 : ℝ)) * X ^ 3 := by positivity
  refine le_trans htri ?_
  linarith [hcs, h3', h4', h5', h6', hn1, hn2, hn3]

/-! ## The inputs for `N` -/

/-- The per-summand inputs for Proposition `NEstimate` (tex 1488-1492).  The fields are the
paper's estimates for `I^{N}_1` (tex 1450-1454: `RemovingL12_R`, `HProductRule`,
`WProductRule`, `WtoH`) and for `I^{N}_2, …, I^{N}_5` (tex 1472-1490: `DivisionBySin`,
`Transport1`, `SpecialTransport`, `WtoH`, `PhiStarRegularity`). -/
structure NInputs (α : ℝ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ) (C : ℝ)
    (F Φ g : ℝ → ℝ → ℝ) : Prop where
  h1 : |IP (N1 α F Φ) g| ≤ C * (α ^ 2 * H4N α g + Real.sqrt α * H4N α g ^ 2
    + α ^ (-(1 / 2 : ℝ)) * H4N α g ^ 3)
  h25 : |IP (N2 α F Φ) g| + |IP (N3 α F Φ) g| + |IP (N4 α F Φ) g| + |IP (N5 α F Φ) g|
    ≤ C * (α ^ 2 * H4N α g + Real.sqrt α * H4N α g ^ 2
      + α ^ (-(1 / 2 : ℝ)) * H4N α g ^ 3)

/-- **Proposition `NEstimate`** (tex 1488-1492): `|(N,g)_{ℋ⁴}| ≤ C(α²|g| + √α|g|² +
α^{-3/2}|g|³)`. -/
theorem NEstimate {α C : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 < C)
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} (hIP : IsH4IP α IP) {F Φ g : ℝ → ℝ → ℝ}
    (hin : NInputs α IP C F Φ g) :
    |IP (N α F Φ) g|
      ≤ 8 * C * (α ^ 2 * H4N α g + Real.sqrt α * H4N α g ^ 2
        + α ^ (-(3 / 2 : ℝ)) * H4N α g ^ 3) := by
  set X := H4N α g with hXdef
  have hX : 0 ≤ X := H4N_nonneg α g
  have hsum : IP (N α F Φ) g = IP (N1 α F Φ) g + IP (N2 α F Φ) g + IP (N3 α F Φ) g
      + IP (N4 α F Φ) g + IP (N5 α F Φ) g := by
    rw [N_eq_sum, hIP.add_fst, hIP.add_fst, hIP.add_fst, hIP.add_fst]
    try ring
  have htri : |IP (N α F Φ) g| ≤ |IP (N1 α F Φ) g| + |IP (N2 α F Φ) g| + |IP (N3 α F Φ) g|
      + |IP (N4 α F Φ) g| + |IP (N5 α F Φ) g| := by
    rw [hsum]
    exact abs_sum_le_five _ _ _ _ _
  have hhalf : α ^ (-(1 / 2 : ℝ)) * X ^ 3 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 3 :=
    mul_le_mul_of_nonneg_right (rpow_neg_half_le hα hα1) (by positivity)
  have hone : |IP (N1 α F Φ) g| ≤ C * (α ^ 2 * X + Real.sqrt α * X ^ 2
      + α ^ (-(3 / 2 : ℝ)) * X ^ 3) := by
    refine le_trans hin.h1 ?_
    nlinarith [hhalf]
  have hrest : |IP (N2 α F Φ) g| + |IP (N3 α F Φ) g| + |IP (N4 α F Φ) g| + |IP (N5 α F Φ) g|
      ≤ C * (α ^ 2 * X + Real.sqrt α * X ^ 2 + α ^ (-(3 / 2 : ℝ)) * X ^ 3) := by
    refine le_trans hin.h25 ?_
    nlinarith [hhalf]
  have hpa : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hn1 : (0 : ℝ) ≤ C * α ^ 2 * X := by positivity
  have hn2 : (0 : ℝ) ≤ C * Real.sqrt α * X ^ 2 := by positivity
  have hn3 : (0 : ℝ) ≤ C * α ^ (-(3 / 2 : ℝ)) * X ^ 3 := by positivity
  refine le_trans htri ?_
  linarith [hone, hrest, hn1, hn2, hn3]

/-! ## The inputs for `N_*` -/

/-- The inputs for Proposition `N*Estimate` (tex 1528-1531): the paper's estimate on the
modulation constant `μ` (Proposition `muestimate`, tex 1507) and the elementary pairing bound
`|(g,g)_{ℋ⁴}| + |(g,z∂_zg)_{ℋ⁴}| ≤ |g|_{ℋ⁴}²` (tex 1502, from Cauchy--Schwarz and
`|z∂_zg|_{ℋ⁴} ≤ |g|_{ℋ⁴}`). -/
structure NstarInputs (α μ lam : ℝ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ) (C : ℝ)
    (F Φ g : ℝ → ℝ → ℝ) : Prop where
  hmu : |μ| ≤ C * (α + α ^ (-(3 / 2 : ℝ)) * H4N α g + α ^ (-(5 / 2 : ℝ)) * H4N α g ^ 2)
  hpair : |IP g g| + |IP (Work.Spaces.Dz g) g| ≤ H4N α g ^ 2

/-- **Proposition `N*Estimate`** (tex 1528-1531): with the paper's choice `λ = -2μ/(1+μ)`
(the hypothesis `hlam`), `|(N_*,g)_{ℋ⁴}| ≤ C(α|g|² + α^{-3/2}|g|³ + α^{-5/2}|g|⁴)`. -/
theorem NstarEstimate {α C μ lam : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 < C)
    (hlam : μ + lam + μ * lam = -μ)
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} (hIP : IsH4IP α IP) {F Φ g : ℝ → ℝ → ℝ}
    (hin : NstarInputs α μ lam IP C F Φ g) :
    |IP (Nstar μ lam g) g|
      ≤ 2 * C * (α * H4N α g ^ 2 + α ^ (-(3 / 2 : ℝ)) * H4N α g ^ 3
        + α ^ (-(5 / 2 : ℝ)) * H4N α g ^ 4) := by
  set X := H4N α g with hXdef
  have hX : 0 ≤ X := H4N_nonneg α g
  have hsm1 : IP (Ns1 μ lam g) g = -μ * IP g g := by
    rw [show Ns1 μ lam g = fun z θ => (-μ) * g z θ from rfl, hIP.smul_fst]
  have hsm2 : IP (Ns2 μ lam g) g = -(μ + lam + μ * lam) * IP (Work.Spaces.Dz g) g := by
    rw [show Ns2 μ lam g = fun z θ => (-(μ + lam + μ * lam)) * Work.Spaces.Dz g z θ from rfl,
      hIP.smul_fst]
  have hsum : IP (Nstar μ lam g) g = IP (Ns1 μ lam g) g + IP (Ns2 μ lam g) g := by
    rw [Nstar_eq_sum, hIP.add_fst]
  have hkey : -(μ + lam + μ * lam) = μ := by linarith [hlam]
  have htri : |IP (Nstar μ lam g) g| ≤ |μ| * (|IP g g| + |IP (Work.Spaces.Dz g) g|) := by
    rw [hsum, hsm1, hsm2, hkey]
    have heq : -μ * IP g g + μ * IP (Work.Spaces.Dz g) g
        = μ * (IP (Work.Spaces.Dz g) g - IP g g) := by ring
    rw [heq, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg μ)
    have h2 : |IP (Work.Spaces.Dz g) g - IP g g|
        ≤ |IP (Work.Spaces.Dz g) g| + |IP g g| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le (IP (Work.Spaces.Dz g) g) (-(IP g g))
    linarith [h2]
  have hprod : |μ| * (|IP g g| + |IP (Work.Spaces.Dz g) g|)
      ≤ C * (α * X ^ 2 + α ^ (-(3 / 2 : ℝ)) * X ^ 3 + α ^ (-(5 / 2 : ℝ)) * X ^ 4) := by
    have hbr : (0 : ℝ) ≤ α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2 := by
      have h1 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * X :=
        mul_nonneg (Real.rpow_nonneg hα.le _) hX
      have h2 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 2 :=
        mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
      linarith [hα.le, h1, h2]
    have hCX : (0 : ℝ) ≤ C * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) :=
      mul_nonneg hC.le hbr
    have hpr : (0 : ℝ) ≤ |IP g g| + |IP (Work.Spaces.Dz g) g| := by positivity
    calc |μ| * (|IP g g| + |IP (Work.Spaces.Dz g) g|)
        ≤ C * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) * X ^ 2 :=
          mul_le_mul hin.hmu hin.hpair hpr hCX
      _ = C * (α * X ^ 2 + α ^ (-(3 / 2 : ℝ)) * X ^ 3 + α ^ (-(5 / 2 : ℝ)) * X ^ 4) := by
          ring
  have hpa3 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hpa5 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hn1 : (0 : ℝ) ≤ C * (α * X ^ 2) := by positivity
  have hn2 : (0 : ℝ) ≤ C * (α ^ (-(3 / 2 : ℝ)) * X ^ 3) := by positivity
  have hn3 : (0 : ℝ) ≤ C * (α ^ (-(5 / 2 : ℝ)) * X ^ 4) := by positivity
  linarith [htri, hprod, hn1, hn2, hn3]

/-! ## The combined estimate and the coercivity corollary -/

/-- **Proposition `innerproductestimate`** (tex 1537-1539): the sum of the absolute values of
the four contributions to `\eqref{gEquationFinal}` is bounded by
`C(α²|g| + √α|g|² + α^{-3/2}|g|³ + α^{-5/2}|g|⁴)`; the fourth contribution is the `μ̄`-term
`(L₁₂(N₀)(0)+L₁₂(N)(0))AK`, whose bound is the input `hAK`. -/
theorem innerproductestimate {α C μ lam : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 < C)
    (hlam : μ + lam + μ * lam = -μ)
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} (hIP : IsH4IP α IP) {F Φ g : ℝ → ℝ → ℝ}
    (h0 : N0Inputs α IP C F g) (hn : NInputs α IP C F Φ g)
    (hns : NstarInputs α μ lam IP C F Φ g)
    (hAK : |IP (fun z θ => mubar (N0 α F g) (N α F Φ) * AK α z θ) g| ≤ C * α ^ 2 * H4N α g) :
    |IP (N0 α F g) g| + |IP (N α F Φ) g| + |IP (Nstar μ lam g) g|
        + |IP (fun z θ => mubar (N0 α F g) (N α F Φ) * AK α z θ) g|
      ≤ 32 * C * (α ^ 2 * H4N α g + Real.sqrt α * H4N α g ^ 2
        + α ^ (-(3 / 2 : ℝ)) * H4N α g ^ 3 + α ^ (-(5 / 2 : ℝ)) * H4N α g ^ 4) := by
  have h1 := N0Estimate hα hα1 hC hIP h0
  have h2 := NEstimate hα hα1 hC hIP hn
  have h3 := NstarEstimate hα hα1 hC hlam hIP hns
  have h4 := hAK
  set X := H4N α g with hXdef
  have hX : 0 ≤ X := H4N_nonneg α g
  have h5 : α ^ (-(3 / 2 : ℝ)) * X ^ 3 ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 3 :=
    mul_le_mul_of_nonneg_right (rpow_neg_three_le hα hα1) (by positivity)
  have hpa3 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hpa5 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hn0 : (0 : ℝ) ≤ C * α ^ 2 * X := by positivity
  have hn1 : (0 : ℝ) ≤ C * Real.sqrt α * X ^ 2 := by positivity
  have hn2 : (0 : ℝ) ≤ C * α ^ (-(3 / 2 : ℝ)) * X ^ 3 := by positivity
  have hn3 : (0 : ℝ) ≤ C * α ^ (-(5 / 2 : ℝ)) * X ^ 4 := by positivity
  have hsqrt : α ≤ Real.sqrt α := by
    have hs1 : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
    have hs0 : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
    have hsq := Real.sq_sqrt hα.le
    nlinarith [hs1, hs0, hsq]
  have hαsqC : 2 * C * (α * X ^ 2) ≤ 2 * C * (Real.sqrt α * X ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsqrt (by positivity)) (by positivity)
  have h5C : C * (α ^ (-(3 / 2 : ℝ)) * X ^ 3) ≤ C * (α ^ (-(5 / 2 : ℝ)) * X ^ 3) :=
    mul_le_mul_of_nonneg_left h5 hC.le
  linarith [h1, h2, h3, h4, hn0, hn1, hn2, hn3, h5C, hαsqC]

/-- **The corollary of the a-priori estimate** (tex 1543-1547): if `g` solves
`\eqref{gEquationFinal}` then the coercivity of `𝓛_Γ^T` and `innerproductestimate` give the
two-sided bound `c|g|_{ℋ⁴}² ≤ (𝓛_Γ^Tg,g)_{ℋ⁴} ≤ C(α²|g| + √α|g|² + α^{-3/2}|g|³ +
α^{-5/2}|g|⁴)`.  The paper only uses it in the form `|g|_{ℋ⁴} ≤ 2Cα²` under the a-priori
assumption `|g|_{ℋ⁴} ≤ α^{7/4}`, which is what the fixed-point argument of
`Submission/Work/Construction/FixedPoint.lean` consumes. -/
theorem apriori_corollary {α C μ lam : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 < C)
    (hlam : μ + lam + μ * lam = -μ)
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} (hIP : IsH4IP α IP) {F Φ g : ℝ → ℝ → ℝ}
    (hgsol : IsGSol α μ lam F g Φ)
    (h0 : N0Inputs α IP C F g) (hn : NInputs α IP C F Φ g)
    (hns : NstarInputs α μ lam IP C F Φ g)
    (hAK : |IP (fun z θ => mubar (N0 α F g) (N α F Φ) * AK α z θ) g| ≤ C * α ^ 2 * H4N α g) :
    IP (Work.Coercivity.LGammaT α g) g
        ≤ 32 * C * (α ^ 2 * H4N α g + Real.sqrt α * H4N α g ^ 2
          + α ^ (-(3 / 2 : ℝ)) * H4N α g ^ 3 + α ^ (-(5 / 2 : ℝ)) * H4N α g ^ 4) := by
  set X := H4N α g with hXdef
  have hX : 0 ≤ X := H4N_nonneg α g
  have hcongr : IP (Work.Coercivity.LGammaT α g) g
      = IP (gRHS α μ lam F Φ g) g :=
    hIP.congr_qd _ _ g (fun z θ hzθ => hgsol z θ hzθ)
  have hgr : gRHS α μ lam F Φ g
      = (fun z θ => -(mubar (N0 α F g) (N α F Φ) * AK α z θ)) + N0 α F g + N α F Φ
        + Nstar μ lam g := by
    funext z θ
    simp only [gRHS, Pi.add_apply]
    ring
  have hsum : IP (gRHS α μ lam F Φ g) g
      = IP (fun z θ => -(mubar (N0 α F g) (N α F Φ) * AK α z θ)) g
        + IP (N0 α F g) g + IP (N α F Φ) g + IP (Nstar μ lam g) g := by
    rw [hgr, hIP.add_fst, hIP.add_fst, hIP.add_fst]
    try ring
  have hneg : IP (fun z θ => -(mubar (N0 α F g) (N α F Φ) * AK α z θ)) g
      = -IP (fun z θ => mubar (N0 α F g) (N α F Φ) * AK α z θ) g := by
    rw [show (fun z θ => -(mubar (N0 α F g) (N α F Φ) * AK α z θ))
        = fun z θ => (-1) * (mubar (N0 α F g) (N α F Φ) * AK α z θ) from by
      funext z θ; ring, hIP.smul_fst]
    try ring
  have h1 := N0Estimate hα hα1 hC hIP h0
  have h2 := NEstimate hα hα1 hC hIP hn
  have h3 := NstarEstimate hα hα1 hC hlam hIP hns
  have h5 : α ^ (-(3 / 2 : ℝ)) * X ^ 3 ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 3 :=
    mul_le_mul_of_nonneg_right (rpow_neg_three_le hα hα1) (by positivity)
  have hbound : IP (gRHS α μ lam F Φ g) g ≤ |IP (fun z θ => mubar (N0 α F g) (N α F Φ) * AK α z θ) g|
      + |IP (N0 α F g) g| + |IP (N α F Φ) g| + |IP (Nstar μ lam g) g| := by
    rw [hsum, hneg]
    have hlt := le_abs_self (IP (fun z θ => mubar (N0 α F g) (N α F Φ) * AK α z θ) g)
    have h1' := neg_le_abs (IP (fun z θ => mubar (N0 α F g) (N α F Φ) * AK α z θ) g)
    have h2' := le_abs_self (IP (N0 α F g) g)
    have h3' := le_abs_self (IP (N α F Φ) g)
    have h4' := le_abs_self (IP (Nstar μ lam g) g)
    linarith [h1', h2', h3', h4']
  have hpa3 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hpa5 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hn0 : (0 : ℝ) ≤ C * α ^ 2 * X := by positivity
  have hn1 : (0 : ℝ) ≤ C * Real.sqrt α * X ^ 2 := by positivity
  have hn2 : (0 : ℝ) ≤ C * α ^ (-(3 / 2 : ℝ)) * X ^ 3 := by positivity
  have hn3 : (0 : ℝ) ≤ C * α ^ (-(5 / 2 : ℝ)) * X ^ 4 := by positivity
  have hsqrt : α ≤ Real.sqrt α := by
    have hs1 : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
    have hs0 : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
    have hsq := Real.sq_sqrt hα.le
    nlinarith [hs1, hs0, hsq]
  have hαsqC : 2 * C * (α * X ^ 2) ≤ 2 * C * (Real.sqrt α * X ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsqrt (by positivity)) (by positivity)
  have h5C : C * (α ^ (-(3 / 2 : ℝ)) * X ^ 3) ≤ C * (α ^ (-(5 / 2 : ℝ)) * X ^ 3) :=
    mul_le_mul_of_nonneg_left h5 hC.le
  rw [hcongr]
  refine le_trans hbound ?_
  linarith [hAK, h1, h2, h3, hn0, hn1, hn2, hn3, h5C, hαsqC]

end Work.Construction
