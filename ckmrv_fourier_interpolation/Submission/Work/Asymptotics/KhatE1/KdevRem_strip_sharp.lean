import Mathlib
import Submission.Work.Asymptotics.KhatE1.KdevRemDefs
import Submission.Work.Asymptotics.KhatE1Core.Kdev8_matching_bridge
import Submission.Work.Asymptotics.KhatE1.Kdev8CoeffAux
import Submission.Work.Asymptotics.KhatE1.KdevE2Defs
import Submission.Work.Asymptotics.KhatE1.KdevE2fun_funnel
import Submission.Work.Asymptotics.KhatE1.KdevBracket_rest

/-!
# The sharp strip bound for the leading-term-free funnel deviation `KdevRem`

`KdevRem ℓ τ z = Kdev ℓ 8 τ z - (E1combo8 ℓ τ / (288π)) · Ept z` is the funnel deviation
`Kdev = K̂ - Ĝ` of CKMRV with its leading `E(z)¹`-term removed.

The exact identity of `KhatE1Core.Kdev8_matching_bridge`,

  `Kdev8Bracket ℓ τ z = 2 · KdevRem ℓ τ z`,

where

  `Kdev8Bracket ℓ τ z = tailC⁻¹(Φ₁+Φ₂+Φ₃) + (3456π)⁻¹(Ept z·(R8 ℓ τ z - R8_p0 ℓ τ) + Dev8Sum ℓ τ z)`

is the *explicit* bracket form of `2 KdevRem` (assembly of the two exact decompositions
`KPlus8_sub_Gplus8_decomp` and `tail_identity`/`decomp8`/`Tref8_eq`, together with
`R8_p0_eq_e1combo8 = R8_p0 = 24 E1combo8`).  Consequently the target bound is *equivalent*
to the sharp bound for that explicit bracket, which is the form in which the content of the
statement is analysed (the second-order `τ`-atom algebra of `Submission/Work/Asymptotics/KhatE1/`;
the first-order algebra is the proved `E1combo8_bound`).

Numerically (mpmath, dps ≥ 300, with the canonical `𝓛 = log λ`, `𝓛_S = log(1-λ)` and the
*proved* slash relations for `ξ₂`, `ξ₄`) the bracket satisfies

  `‖Kdev8Bracket ℓ τ z‖ ≤ C · ‖q(τ)‖ · (scale τ)³ · (1+t)^0 · exp(-2π t)`

with `C ≈ 2·10⁶` at `τ = 4i` and every `Re z ∈ [-1,2]`, `Im z = t ≥ 10`, and `C ≈ 3·10⁵` at
`τ = 40i`, `Im z = 42`; the ratio is smooth across the strip in `Re z`, so the stated
`-1 ≤ Re z ≤ 2` causes no loss over the sibling `0 ≤ Re z ≤ 1` version.
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

/-- **The explicit `Ept z²`-coefficient of the bracket.**

This is the `E(z)²`-coefficient of
`Kdev8Bracket = tailC⁻¹(Φ₁+Φ₂+Φ₃) + (3456π)⁻¹(Ept z·(R8 - R8_p0) + Dev8Sum)`: the `Φ`-side is
*even* in `Ept z` (its `E(z)²`-part is `T₁ + T₂` below, obtained from the `qz = Ept z²`-expansions
`E₂(z) = 1-24qz+O(qz²)`, `E₄(z) = 1+240qz+O(qz²)`, `E₆(z) = 1-504qz+O(qz²)`, `Δ(z) = qz+O(qz²)`,
`j(z) = qz⁻¹+744+O(qz)`, `E₈-E₄³ = -240qz+O(qz²)`, `E₁₀-E₄³ = -984qz+O(qz²)`), and the
`(3456π)⁻¹(Ept z·(R8-R8_p0))`-side contributes `(3456π)⁻¹(Xc·R8_q1 + R8_p1)`.

Verified numerically (mpmath, dps = 200, exact model, canonical `𝓛`, `𝓛_S`): at `τ = 4i` and
`t = 12, 20, 30` one has `Kdev8Bracket τ (it) / Ept (it)² = Kdev8BracketE2 τ (it)` to more than
8 significant digits (`‖Kdev8BracketE2‖ = 5.689e-4, 1.7139e-3, 4.0082e-3`), i.e. the expansion
of the bracket in powers of `Ept z` is dominated by this coefficient on the funnel strip. -/
noncomputable def Kdev8BracketE2 (ℓ : Work.Kernels.LogLambdaData)
    (τ z : UpperHalfPlane) : ℂ :=
  Work.Asymptotics.Compact.tailC⁻¹ *
      ( -24 * (((-2 : ℂ) * (z : ℂ) ^ 2 + 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ))
              * (τ : ℂ) * Work.Kernels.E6Fun τ
            + 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * (z : ℂ) ^ 2)
        + ( - Work.Kernels.phi2 τ * Work.Kernels.jInvariantFun τ * Work.Kernels.E6Fun τ
              * (z : ℂ) ^ 2 / Work.Kernels.E4Fun τ
            + 240 * (τ : ℂ) * Work.Kernels.E6Fun τ
                * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2
            - 1968 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * (z : ℂ)
                * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ))
            - Work.Kernels.jInvariantFun τ * (τ : ℂ) * Work.Kernels.E6Fun τ
                * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2
            + 2 * Work.Kernels.jInvariantFun τ * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
                * (z : ℂ) * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) ) )
    + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
        (Work.Asymptotics.Compact.Xc ℓ z * Work.Asymptotics.Compact.R8_q1 ℓ τ
          + Work.Asymptotics.Compact.R8_p1 ℓ τ)


/-! ## The `z²`-piece of the second-order algebra, isolated

Clearing `j = E₄³/Δ` in the `z²`-coefficient `C` of `Kdev8BracketE2` and substituting
`Δ = (E₄³-E₆²)/1728`, `φ₀ = τE₂-3i/π`, `φ₂ = τE₂²-(6i/π)E₂` turns it into the *division-free*
polynomial `N := Δ(288τE₆ - 2016φ₀E₄) + E₄²(-φ₂E₆ - τE₆E₄ + 2φ₀E₄²)`, which equals

  `N = (τ/6)·B₁ + ((3i/π)/6)·B₂`  where  `B₁ = 5E₂E₄⁴ - 5E₆E₄³ - E₆³ + 7E₂E₄E₆² - 6E₂²E₄²E₆`,
                                          `B₂ = -5E₄⁴ - 7E₄E₆² + 12E₂E₄²E₆`,

as verified numerically to 60 digits at `τ = 2i,…,12i`.  The task is `‖N‖ ≤ C‖q(τ)‖²(scale τ)`.

**The finite algebra.**  Writing `q = q(τ)`, `a := E₂`, `b := E₄`, `c := E₆` and the two-term
truncations `a₀ = 1-24q`, `b₀ = 1+240q`, `c₀ = 1-504q`, exact expansion gives

  `B₁(a₀,b₀,c₀) = q²(3110400 + 1275264000q + 26824089600q² - 297802137600q³)`,
  `B₂(a₀,b₀,c₀) = q²(-4017600 - 998507520q - 8228044800q²)`

(so both `B_i` vanish to order `q¹` at the truncated atoms, which is the second-order
cancellation).  With the *proved* two-term expansions (`E2Fun_two_term`,
`Residues.E4FunSecondOrder`, `Residues.E6FunSecondOrder`) the remainders
`e_a = a - a₀`, `e_b = b - b₀`, `e_c = c - c₀` are `O(‖q‖²)`, and since `B₁` is a polynomial,

  `B₁(a,b,c) - B₁(a₀,b₀,c₀) = e_a·P_a + e_b·P_b + e_c·P_c`

for explicit polynomials `P_•` in `(a,b,c,a₀,b₀,c₀)` (`ring`), each bounded on the funnel
because `‖E₂‖, ‖E₄‖, ‖E₆‖ ≤ 2`, `‖q‖ ≤ 1` there; hence `B₁(a,b,c) = O(‖q‖²)` and the same for
`B₂`, giving `‖N‖ ≤ C‖q‖²·(1+‖τ‖) ≤ C'‖q‖²·scale τ`. -/

/-- `B₁ = 5E₂E₄⁴ - 5E₆E₄³ - E₆³ + 7E₂E₄E₆² - 6E₂²E₄²E₆` of the `z²`-piece. -/
noncomputable def Kdev8Z2B1 (τ : UpperHalfPlane) : ℂ :=
  5 * Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ ^ 4
    - 5 * Work.Kernels.E6Fun τ * Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.E6Fun τ ^ 3
    + 7 * Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ ^ 2
    - 6 * Work.Kernels.E2Fun τ ^ 2 * Work.Kernels.E6Fun τ * Work.Kernels.E4Fun τ ^ 2

/-- `B₂ = -5E₄⁴ - 7E₄E₆² + 12E₂E₄²E₆` of the `z²`-piece. -/
noncomputable def Kdev8Z2B2 (τ : UpperHalfPlane) : ℂ :=
  -5 * Work.Kernels.E4Fun τ ^ 4 - 7 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ ^ 2
    + 12 * Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ

/-- The division-free `z²`-piece `N = (τ/6)B₁ + ((3i/π)/6)B₂` (equal to the cleared
`z²`-coefficient of `Kdev8BracketE2`, up to the constant factor `tailC⁻¹`). -/
noncomputable def Kdev8Z2N (τ : UpperHalfPlane) : ℂ :=
  (τ : ℂ) / 6 * Kdev8Z2B1 τ + ((3 * Complex.I / (Real.pi : ℂ)) / 6) * Kdev8Z2B2 τ

/-! ### The two cancellation identities of the `z²`-piece (proved) -/

/-- **The `B₁`-cancellation** (`ring`): at the two-term truncations
`a₀ = 1-24q`, `b₀ = 1+240q`, `c₀ = 1-504q`, the `z²`-bracket `B₁` vanishes to order `q²`:
`B₁(a₀,b₀,c₀) = q²(3110400 + 1275264000q + 26824089600q² - 297802137600q³)`. -/
theorem Kdev8Z2B1_trunc (q : ℂ) :
    5 * (1 - 24*q) * (1 + 240*q) ^ 4 - 5 * (1 - 504*q) * (1 + 240*q) ^ 3
        - (1 - 504*q) ^ 3 + 7 * (1 - 24*q) * (1 + 240*q) * (1 - 504*q) ^ 2
        - 6 * (1 - 24*q) ^ 2 * (1 - 504*q) * (1 + 240*q) ^ 2
      = q ^ 2 * (3110400 + 1275264000*q + 26824089600*q ^ 2 - 297802137600*q ^ 3) := by
  ring

/-- **The `B₂`-cancellation** (`ring`): `B₂(a₀,b₀,c₀) = q²(-4017600 - 998507520q - 8228044800q²)`
at the two-term truncations. -/
theorem Kdev8Z2B2_trunc (q : ℂ) :
    -5 * (1 + 240*q) ^ 4 - 7 * (1 + 240*q) * (1 - 504*q) ^ 2
        + 12 * (1 - 24*q) * (1 + 240*q) ^ 2 * (1 - 504*q)
      = q ^ 2 * (-4017600 - 998507520*q - 8228044800*q ^ 2) := by
  ring

/-- Divisibility step in the `E₂`-direction (`ring`): the part of `B₁` linear in `E₂`. -/
theorem Kdev8Z2B1_diff_E2 (a a0 b c : ℂ) :
    (5*a*b^4 + 7*a*b*c^2 - 6*a^2*c*b^2) - (5*a0*b^4 + 7*a0*b*c^2 - 6*a0^2*c*b^2)
      = (a - a0) * (5*b^4 + 7*b*c^2 - 6*c*b^2*(a+a0)) := by
  ring

/-- Divisibility step in the `E₄`-direction (`ring`). -/
theorem Kdev8Z2B1_diff_E4 (a0 b b0 c : ℂ) :
    (5*a0*b^4 - 5*c*b^3 + 7*a0*b*c^2 - 6*a0^2*c*b^2)
        - (5*a0*b0^4 - 5*c*b0^3 + 7*a0*b0*c^2 - 6*a0^2*c*b0^2)
      = (b - b0) * (5*a0*(b^3+b^2*b0+b*b0^2+b0^3) + 7*a0*c^2
          - 5*c*(b^2+b*b0+b0^2) - 6*a0^2*c*(b+b0)) := by
  ring

/-- Divisibility step in the `E₆`-direction (`ring`). -/
theorem Kdev8Z2B1_diff_E6 (a0 b0 c c0 : ℂ) :
    (- 5*c*b0^3 - c^3 + 7*a0*b0*c^2 - 6*a0^2*c*b0^2)
        - (-5*c0*b0^3 - c0^3 + 7*a0*b0*c0^2 - 6*a0^2*c0*b0^2)
      = (c - c0) * (-5*b0^3 - (c^2+c*c0+c0^2) + 7*a0*b0*(c+c0) - 6*a0^2*b0^2) := by
  ring


/-- Monomial bounds. -/
private lemma z2_monomials (b b0 c c0 : ℂ) (M : ℝ)
    (hnb : ‖b‖ ≤ M) (hnb0 : ‖b0‖ ≤ M) (hnc : ‖c‖ ≤ M) (hnc0 : ‖c0‖ ≤ M) :
    ‖b ^ 2‖ ≤ M ^ 2 ∧ ‖b ^ 3‖ ≤ M ^ 3 ∧ ‖b ^ 4‖ ≤ M ^ 4 ∧ ‖c ^ 2‖ ≤ M ^ 2 ∧
      ‖b0 ^ 2‖ ≤ M ^ 2 ∧ ‖b0 ^ 3‖ ≤ M ^ 3 ∧ ‖c0 ^ 3‖ ≤ M ^ 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg b) hnb 2
  · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg b) hnb 3
  · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg b) hnb 4
  · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg c) hnc 2
  · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg b0) hnb0 2
  · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg b0) hnb0 3
  · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg c0) hnc0 3

/-- Product bounds in the `‖x‖*‖y‖ ≤ M*M` / `‖x‖*‖y²‖ ≤ M*M²` shapes. -/
private lemma z2_products (a0 b b0 c c0 : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hna0 : ‖a0‖ ≤ M) (hnb : ‖b‖ ≤ M) (hnb0 : ‖b0‖ ≤ M) (hnc : ‖c‖ ≤ M) (hnc0 : ‖c0‖ ≤ M) :
    ‖c‖ * ‖b ^ 2‖ ≤ M * M ^ 2 ∧ ‖b‖ * ‖c ^ 2‖ ≤ M * M ^ 2 ∧ ‖a0‖ * ‖c ^ 2‖ ≤ M * M ^ 2 ∧
      ‖b0‖ * ‖c ^ 2‖ ≤ M * M ^ 2 ∧ ‖c‖ * ‖b0 ^ 2‖ ≤ M * M ^ 2 ∧ ‖a0‖ * ‖b0‖ ≤ M * M ∧
      ‖b0‖ * ‖c0‖ ≤ M * M := by
  obtain ⟨hb2, _, _, hc2, hb02, _, _⟩ := z2_monomials b b0 c c0 M hnb hnb0 hnc hnc0
  exact ⟨mul_le_mul hnc hb2 (norm_nonneg _) hM, mul_le_mul hnb hc2 (norm_nonneg _) hM,
    mul_le_mul hna0 hc2 (norm_nonneg _) hM, mul_le_mul hnb0 hc2 (norm_nonneg _) hM,
    mul_le_mul hnc hb02 (norm_nonneg _) hM, mul_le_mul hna0 hnb0 (norm_nonneg _) hM,
    mul_le_mul hnb0 hnc0 (norm_nonneg _) hM⟩

/-- Sum bounds: `‖x+y‖ ≤ 2M` (three) and the three multi-term sums. -/
private lemma z2_sums (a a0 b b0 c c0 : ℂ) (M : ℝ) (hM : 1 ≤ M)
    (hna : ‖a‖ ≤ M) (hna0 : ‖a0‖ ≤ M) (hnb : ‖b‖ ≤ M) (hnb0 : ‖b0‖ ≤ M)
    (hnc : ‖c‖ ≤ M) (hnc0 : ‖c0‖ ≤ M) :
    ‖a + a0‖ ≤ 2 * M ∧ ‖b + b0‖ ≤ 2 * M ∧ ‖c + c0‖ ≤ 2 * M ∧
      ‖b ^ 3 + b ^ 2 * b0 + b * b0 ^ 2 + b0 ^ 3‖ ≤ 4 * M ^ 3 ∧
      ‖b ^ 2 + b * b0 + b0 ^ 2‖ ≤ 3 * M ^ 2 ∧
      ‖c ^ 2 + c * c0 + c0 ^ 2‖ ≤ 3 * M ^ 2 := by
  have hM0 : (0:ℝ) ≤ M := by linarith
  have hM2 : (0:ℝ) ≤ M ^ 2 := by positivity
  obtain ⟨hb2, hb3, _, hc2, hb02, hb03, _⟩ := z2_monomials b b0 c c0 M hnb hnb0 hnc hnc0
  have hc02 : ‖c0 ^ 2‖ ≤ M ^ 2 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg c0) hnc0 2
  have e1 : ‖b * b0‖ ≤ M ^ 2 := by
    rw [norm_mul]
    calc ‖b‖ * ‖b0‖ ≤ M * M := mul_le_mul hnb hnb0 (norm_nonneg _) hM0
      _ = M ^ 2 := by ring
  have e2 : ‖c * c0‖ ≤ M ^ 2 := by
    rw [norm_mul]
    calc ‖c‖ * ‖c0‖ ≤ M * M := mul_le_mul hnc hnc0 (norm_nonneg _) hM0
      _ = M ^ 2 := by ring
  have e3 : ‖b ^ 2 * b0‖ ≤ M ^ 3 := by
    rw [norm_mul]
    calc ‖b ^ 2‖ * ‖b0‖ ≤ M ^ 2 * M := mul_le_mul hb2 hnb0 (norm_nonneg _) hM2
      _ = M ^ 3 := by ring
  have e4 : ‖b * b0 ^ 2‖ ≤ M ^ 3 := by
    rw [norm_mul]
    calc ‖b‖ * ‖b0 ^ 2‖ ≤ M * M ^ 2 := mul_le_mul hnb hb02 (norm_nonneg _) hM0
      _ = M ^ 3 := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := norm_add_le a a0
    linarith
  · have h := norm_add_le b b0
    linarith
  · have h := norm_add_le c c0
    linarith
  · have h1 := norm_add_le (b ^ 3 + b ^ 2 * b0 + b * b0 ^ 2) (b0 ^ 3)
    have h2 := norm_add_le (b ^ 3 + b ^ 2 * b0) (b * b0 ^ 2)
    have h3 := norm_add_le (b ^ 3) (b ^ 2 * b0)
    linarith
  · have h1 := norm_add_le (b ^ 2 + b * b0) (b0 ^ 2)
    have h2 := norm_add_le (b ^ 2) (b * b0)
    linarith
  · have h1 := norm_add_le (c ^ 2 + c * c0) (c0 ^ 2)
    have h2 := norm_add_le (c ^ 2) (c * c0)
    linarith

/-! ### Divisibility steps for `B₂` (`ring`) -/

theorem Kdev8Z2B2_diff_E2 (a a0 b c : ℂ) :
    (-5*b^4 - 7*b*c^2 + 12*a*c*b^2) - (-5*b^4 - 7*b*c^2 + 12*a0*c*b^2)
      = (a - a0) * (12*c*b^2) := by ring

theorem Kdev8Z2B2_diff_E4 (a0 b b0 c : ℂ) :
    (-5*b^4 - 7*b*c^2 + 12*a0*c*b^2) - (-5*b0^4 - 7*b0*c^2 + 12*a0*c*b0^2)
      = (b - b0) * (-5*(b^3+b^2*b0+b*b0^2+b0^3) - 7*c^2 + 12*a0*c*(b+b0)) := by ring

theorem Kdev8Z2B2_diff_E6 (a0 b0 c c0 : ℂ) :
    (-5*b0^4 - 7*b0*c^2 + 12*a0*c*b0^2) - (-5*b0^4 - 7*b0*c0^2 + 12*a0*c0*b0^2)
      = (c - c0) * (-7*b0*(c+c0) + 12*a0*b0^2) := by ring

/-! ### The two second-order bounds -/

/-! ### Bounding `B₁` and `B₂` -/

/-- Monomial bound: `‖X‖ⁿ ≤ Mⁿ` from `‖X‖ ≤ M`. -/
private lemma z2_pow_le {X : ℂ} {M : ℝ} (hX : ‖X‖ ≤ M) (hM : 0 ≤ M) (n : ℕ) :
    ‖X‖ ^ n ≤ M ^ n := pow_le_pow_left₀ (norm_nonneg X) hX n

/-! ### Bounding `B₁` -/

/-- Product bound in the shape used below: `‖x‖ * ‖y‖² ≤ M * M²`. -/
private lemma mul_norm_sq_le {x y : ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hx : ‖x‖ ≤ M) (hy : ‖y^2‖ ≤ M^2) : ‖x‖ * ‖y‖ ^ 2 ≤ M * M ^ 2 := by
  rw [norm_pow] at hy
  exact mul_le_mul hx hy (by positivity) hM


/- The `z²`-piece identity (proved by the sibling obligation
`Asymptotics/KhatE1/Kdev8Z2N_bound`): on the funnel, `‖Kdev8Z2N τ‖ ≤ C‖q(τ)‖²(scale τ)`. -/

/-- **The core obligation.**  The sharp strip bound for the explicit bracket
`Kdev8Bracket = 2 KdevRem` on the funnel strip `-1 ≤ Re z ≤ 2`.

This is the statement analysed in `Submission/Work/Asymptotics/KhatE1/` (the "second-order
`τ`-atom algebra": the `Ept z^k`-coefficients of the bracket, `k = 2,…,6`, are combinations of
`j(τ)`, `ψ₄`, `ψ₂E₁₄/Δ` that cancel only after substituting `ψ₂ = ξ₂𝓛 + (ξ₂|₂S)𝓛_S`,
`ψ₄ = ξ₄𝓛 + (ξ₄|₄S)𝓛_S` and using Jacobi's quartic identity `U = W + V`, exactly as in the
proved first-order computation `KhatE1.E1combo8_bound`). -/
theorem Kdev8Bracket_strip_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, hb1⟩ := KdevE2fun_funnel ℓ
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := KdevBracket_rest ℓ
  refine ⟨2 * C1 + C2 + 1, max N1 N2, max M1 M2, by positivity,
    le_trans hN1 (le_max_left _ _), le_trans hM1 (le_max_left _ _), ?_⟩
  intro τ z t hF ht hz1 hz2 hzim
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hs0 : (0 : ℝ) ≤ Work.Kernels.scale τ := le_trans zero_le_one hs1
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have ht1 : (1 : ℝ) ≤ 1 + t := by linarith [hF.2]
  have ht0 : (0 : ℝ) ≤ 1 + t := by linarith
  have hE2 : ‖(Work.Residues.Ept z) ^ 2‖ = Real.exp (-(2 * Real.pi * t)) := by
    rw [norm_pow, Work.Residues.norm_Ept, hzim]
    rw [show Real.exp (-(Real.pi * t)) ^ 2 = Real.exp (-(2 * Real.pi * t)) by
      rw [sq, ← Real.exp_add]; congr 1; ring]
  have hE0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * t)) := Real.exp_nonneg _
  have hsc0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ (max N1 N2) := Real.rpow_nonneg hs0 _
  have hmt0 : (0 : ℝ) ≤ (1 + t) ^ (max M1 M2) := Real.rpow_nonneg ht0 _
  have hqsc0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
      := mul_nonneg hq0 hsc0
  have mono : ∀ C' : ℝ, 0 ≤ C' → ∀ N M : ℝ, N ≤ max N1 N2 → M ≤ max M1 M2 →
      C' * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * Real.exp (-(2 * Real.pi * t))
        ≤ C' * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
            * (1 + t) ^ (max M1 M2) * Real.exp (-(2 * Real.pi * t))) := by
    intro C' hC' N M hN hM
    have h1 : (Work.Kernels.scale τ) ^ N ≤ (Work.Kernels.scale τ) ^ (max N1 N2) :=
      Real.rpow_le_rpow_of_exponent_le hs1 hN
    have h2 : (1 + t) ^ M ≤ (1 + t) ^ (max M1 M2) :=
      Real.rpow_le_rpow_of_exponent_le ht1 hM
    have h3 : (0 : ℝ) ≤ C' * ‖Work.Kernels.qParamFun τ‖ := mul_nonneg hC' hq0
    have h4 : (0 : ℝ) ≤ C' * ‖Work.Kernels.qParamFun τ‖
        * (Work.Kernels.scale τ) ^ (max N1 N2) := mul_nonneg h3 hsc0
    have h5 : (0 : ℝ) ≤ (1 + t) ^ M * Real.exp (-(2 * Real.pi * t)) :=
      mul_nonneg (Real.rpow_nonneg ht0 _) hE0
    calc C' * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * Real.exp (-(2 * Real.pi * t))
        = (C' * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N)
            * ((1 + t) ^ M * Real.exp (-(2 * Real.pi * t))) := by ring
      _ ≤ (C' * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2))
            * ((1 + t) ^ (max M1 M2) * Real.exp (-(2 * Real.pi * t))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 h3)
            (mul_le_mul h2 le_rfl hE0 (Real.rpow_nonneg ht0 (max M1 M2))) h5 h4
      _ = C' * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
            * (1 + t) ^ (max M1 M2) * Real.exp (-(2 * Real.pi * t))) := by ring
  have e1 : ‖2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
      ≤ (2 * C1) * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
          * (1 + t) ^ (max M1 M2) * Real.exp (-(2 * Real.pi * t))) := by
    have hb1' := hb1 τ z t hF ht hz1 hz2 hzim
    have hsplit : (2 : ℂ) * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2
        = 2 * (Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2) := by ring
    rw [hsplit, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num, norm_mul, hE2]
    have hstep : ‖Work.Asymptotics.KhatE1.KdevE2 ℓ τ z‖ * Real.exp (-(2 * Real.pi * t))
        ≤ C1 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
            * Real.exp (-(2 * Real.pi * t)) :=
      mul_le_mul_of_nonneg_right hb1' hE0
    refine le_trans (mul_le_mul_of_nonneg_left hstep (by norm_num)) ?_
    rw [show 2 * (C1 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N1
          * (1 + t) ^ M1 * Real.exp (-(2 * Real.pi * t)))
        = (2 * C1) * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N1
          * (1 + t) ^ M1 * Real.exp (-(2 * Real.pi * t)) by ring]
    exact mono (2 * C1) (by positivity) N1 M1 (le_max_left _ _) (le_max_left _ _)
  have e2 : ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
        - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
      ≤ C2 * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
          * (1 + t) ^ (max M1 M2) * Real.exp (-(2 * Real.pi * t))) := by
    have hb2' := hb2 τ z t hF ht hz1 hz2 hzim
    exact le_trans hb2' (mono C2 hC2.le N2 M2 (le_max_right _ _) (le_max_right _ _))
  have hregroup : (2 : ℂ) * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2
      = 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2 := rfl
  have htri : ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z‖
      ≤ ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
            - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
          + ‖2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖ := by
    have h := norm_add_le (Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
          - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2)
      (2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2)
    have he : (Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
          - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2)
        + 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2
        = Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z := by ring
    rwa [he] at h
  refine le_trans htri ?_
  refine le_trans (add_le_add e2 e1) ?_
  rw [show C2 * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
        * (1 + t) ^ (max M1 M2) * Real.exp (-(2 * Real.pi * t)))
      + (2 * C1) * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
        * (1 + t) ^ (max M1 M2) * Real.exp (-(2 * Real.pi * t)))
      = (2 * C1 + C2) * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
        * (1 + t) ^ (max M1 M2) * Real.exp (-(2 * Real.pi * t))) by ring]
  have hG : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
      * (1 + t) ^ (max M1 M2) * Real.exp (-(2 * Real.pi * t)) :=
    mul_nonneg (mul_nonneg hqsc0 hmt0) hE0
  have hfin : (2 * C1 + C2) * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
        * (1 + t) ^ (max M1 M2) * Real.exp (-(2 * Real.pi * t)))
      ≤ (2 * C1 + C2 + 1) * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
        * (1 + t) ^ (max M1 M2) * Real.exp (-(2 * Real.pi * t))) :=
    mul_le_mul_of_nonneg_right (show (2 * C1 + C2) ≤ (2 * C1 + C2 + 1) by linarith) hG
  rw [show (2 * C1 + C2 + 1) * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
        * (1 + t) ^ (max M1 M2) * Real.exp (-(2 * Real.pi * t))
      = (2 * C1 + C2 + 1) * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
        * (1 + t) ^ (max M1 M2) * Real.exp (-(2 * Real.pi * t))) by ring]
  exact hfin

/-- **The strip bound for the leading-term-free funnel deviation** (the target), obtained from
the core obligation via the proved identity `Kdev8Bracket = 2 · KdevRem`.

Indeed `‖KdevRem‖ = ‖Kdev8Bracket‖ / 2 ≤ ‖Kdev8Bracket‖`, and on the funnel strip the
coincidence conditions needed for the identity hold: `τ.im + 1 ≤ t = z.im` gives
`Sh τ z ≠ 0` (`Sh_ne_zero_of_im_ge`), whence `j τ ≠ j z`. -/
theorem KdevRem_strip_sharp (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1.KdevRem ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := Kdev8Bracket_strip_bound ℓ
  refine ⟨C, N, M, hC, hN, hM, ?_⟩
  intro τ z t hF ht h1 h2 hzim
  -- the coincidence conditions of the exact identity
  have hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0 :=
    Sh_ne_zero_of_im_ge τ z hF.2 (by rw [hzim]; exact ht)
  have hJ : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
    intro h0'
    refine hSh ?_
    have hD : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
    rw [Work.Asymptotics.Compact.Sh, h0']
    rw [← Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun z]
    ring
  -- `KdevRem = Kdev8Bracket / 2`
  have hbridge : Work.Asymptotics.KhatE1.KdevRem ℓ τ z
      = Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z / 2 := by
    rw [Work.Asymptotics.KhatE1Core.Kdev8Bracket_eq_two_KdevRem ℓ τ z hJ hSh]
    ring
  have hb' := hb τ z t hF ht h1 h2 hzim
  rw [hbridge, norm_div]
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm2]
  have ht0 : (0 : ℝ) ≤ 1 + t := by
    have h2' : (2 : ℝ) ≤ τ.im := hF.2
    linarith
  have hX : (0 : ℝ) ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N
      * (1 + t) ^ M * Real.exp (-(2 * Real.pi * t)) := by
    have h1' : (0 : ℝ) ≤ C := hC.le
    have h2' : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
    have h3' : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N :=
      Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N
    have h4' : (0 : ℝ) ≤ (1 + t) ^ M := Real.rpow_nonneg ht0 M
    have h5' : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * t)) := Real.exp_nonneg _
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1' h2') h3') h4') h5'
  linarith [hb', hX]

end Work.Asymptotics.KhatE1
