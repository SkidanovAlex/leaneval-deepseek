import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseC3QAll.PH_subset_PHq_sub
import Submission.Work.BoseC3QAll.kernel_coef_bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseC3QAll.abs_W1_mul_alpha_sub_le`

The *shifted* pointwise bound on the squeezing weight `Ŵ₁(k)α_{s-k}` that the
`Q₃⁽¹⁾` estimate (and the `Σ_{k∈P_H}Ŵ₁(k)α_{s-k}` sums of FS §10) needs: for `s`
in the support of the low-momentum localisation and `k ∈ P_H`,

`|Ŵ₁(k) α_{s-k}| ≤ 2ρ_z ( Ŵ₁(k)²/‖k‖² + Ŵ₁(s-k)²/‖s-k‖² )`.

## The proof

`α` is derived (`Q3Env.alpha = alphaCoef 𝒜 ℬ`), so on `P_H^q`

* `‖q‖ ≥ 1/(4K_Ha) > 0`, hence `𝒜_q ≥ ‖q‖²/2 > 0` (`Q3KernelFSAll.A_ge`), and
* `|α_q| ≤ |ℬ_q|/𝒜_q = ρ_z|Ŵ₁(q)|/𝒜_q ≤ 2ρ_z|Ŵ₁(q)|/‖q‖²`
  (`abs_alphaCoef_le` and `Q3KernelFSAll.B_eq`).

Here `q := s - k` lies in `P_H^q` (`sub_mem_PHq`, using the scale separation
`ratio_small` from the diluteness hypothesis `hv.t ≤ 4⁻²⁴` and the geometry
`kmom (s-k) = kmom s - kmom k` of `Q3KernelFSAll`), so

`|Ŵ₁(k)α_{s-k}| ≤ 2ρ_z |Ŵ₁(k)| |Ŵ₁(s-k)| / ‖s-k‖²`.

The last factor is then split by AM–GM: with `x = |Ŵ₁(k)|`, `y = |Ŵ₁(s-k)|`,
`p = ‖k‖`, `q = ‖s-k‖`,

`x y / q² ≤ x²/p² + y²/q²`

because `xy/q² = (p/2q)·(2xy/pq)`, `2xy/pq ≤ x²/p² + y²/q²` (as `(x/p-y/q)² ≥ 0`)
and `p ≤ 2q`: the *only* geometric input, which is again the scale separation
(`‖kmom s‖ ≤ K_L√(μa) ≤ ½‖kmom k‖`, so that
`‖s-k‖ ≥ ‖k‖ - ‖s‖ ≥ ‖k‖/2`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

open Work.BoseB7

set_option linter.unusedVariables false

/-- **The AM–GM split of `xy/q²`.**  For `x, y ≥ 0` (`x = |Ŵ₁(k)|`,
`y = |Ŵ₁(s-k)|`) and `0 < p ≤ 2q` (`p = ‖k‖`, `q = ‖s-k‖`),

`x y / q² ≤ x²/p² + y²/q²`.

Indeed `xy/q² = (p/2q)·(2xy/(pq))` with `p/2q ≤ 1` and `2xy/(pq) ≤ x²/p²+y²/q²`
(the latter is `(x/p - y/q)² ≥ 0`). -/
lemma mul_div_sq_le {x y p q : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≤ 2 * q) :
    x * y / q ^ 2 ≤ x ^ 2 / p ^ 2 + y ^ 2 / q ^ 2 := by
  have hpne : p ≠ 0 := ne_of_gt hp
  have hqne : q ≠ 0 := ne_of_gt hq
  have hq2 : 0 < q ^ 2 := pow_pos hq 2
  rw [div_le_iff₀ hq2]
  have hqp : (1 : ℝ) / 2 ≤ q / p := by
    rw [le_div_iff₀ hp]
    linarith
  have hxy : 0 ≤ x * y := mul_nonneg hx hy
  have hfac : 0 ≤ 2 * (q / p) - 1 := by linarith
  have hsq : 0 ≤ (x * (q / p) - y) ^ 2 := sq_nonneg _
  have hkey : (x ^ 2 / p ^ 2 + y ^ 2 / q ^ 2) * q ^ 2 - x * y
      = (x * (q / p) - y) ^ 2 + (2 * (q / p) - 1) * (x * y) := by
    field_simp
    ring
  nlinarith [hsq, mul_nonneg hfac hxy]

theorem abs_W1_mul_alpha_sub_le (K₀ : ℝ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E)
    (hle : hv.t ≤ (1 / 4 : ℝ) ^ 36) (hK : Work.BoseC3QAll.Q3KernelFSAll K₀ F T E)
    {s k : Mode} (hfL : E.fL s ≠ 0) (hk : k ∈ F.PHset E) :
    |E.W1 k * E.alpha (s - k)| ≤
      2 * E.rho * (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 + E.W1 (s - k) ^ 2 / ‖F.kmom (s - k)‖ ^ 2) := by
  by_cases hW : E.W1 k = 0
  · -- `Ŵ₁ k = 0`: the left-hand side vanishes, the right-hand side is nonnegative
    simp only [hW, zero_mul, abs_zero]
    have h1 : 0 ≤ (0 : ℝ) ^ 2 / ‖F.kmom k‖ ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have h2 : 0 ≤ E.W1 (s - k) ^ 2 / ‖F.kmom (s - k)‖ ^ 2 :=
      div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hρ : 0 ≤ E.rho := (rho_pos E hv).le
    nlinarith [h1, h2, hρ]
  have hKH : 0 < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
  have ha : 0 < E.aScat := hv.a_pos
  have hrho : 0 ≤ E.rho := (rho_pos E hv).le
  have hcut : 0 < 1 / (4 * E.KH * E.aScat) := by positivity
  -- `k ∈ P_H ⊆ P_H^q`, so `‖k‖ > 0` and `𝒜_k > 0`
  have hPHk : 1 / (2 * E.KH * E.aScat) ≤ ‖F.kmom k‖ := (Finset.mem_filter.mp hk).2
  have hqk : F.PHq E.KH E.aScat k := PH_subset_PHq F E hv k hPHk
  have hp : 0 < ‖F.kmom k‖ := lt_of_lt_of_le hcut hqk
  -- `s - k ∈ P_H^q`
  have hsmall : E.KL * Real.sqrt (E.mu * E.aScat) ≤ 1 / (4 * E.KH * E.aScat) :=
    ratio_small E hv (le_trans hle (by norm_num))
  have hsmall8 : E.KL * Real.sqrt (E.mu * E.aScat) ≤ 1 / (8 * E.KH * E.aScat) :=
    ratio_small8 E hv hle
  have hPLs : ‖F.kmom s‖ ≤ 2 * (E.KL * Real.sqrt (E.mu * E.aScat)) := hK.fL_supp2 s hfL
  have hsub : F.kmom (s - k) = F.kmom s - F.kmom k := hK.kmom_subW s k hfL hk hW
  have hqsk : F.PHq E.KH E.aScat (s - k) :=
    sub_mem_PHq F E hv hsmall8 (fun a b hf hk hW => hK.kmom_subW a b hf hk hW)
      (fun s hf => hK.fL_supp2 s hf) hfL hk hW
  have hqpos : 0 < ‖F.kmom (s - k)‖ := lt_of_lt_of_le hcut hqsk
  have hApos : 0 < E.A (s - k) := by
    have h2 : 0 < ‖F.kmom (s - k)‖ ^ 2 / 2 := by positivity
    linarith [hK.A_ge (s - k) hqsk]
  -- the squeezing bound at `s - k`
  have hα : |E.alpha (s - k)| ≤ 2 * E.rho * |E.W1 (s - k)| / ‖F.kmom (s - k)‖ ^ 2 := by
    have h1 : |E.alpha (s - k)| ≤ |E.B (s - k)| / E.A (s - k) := by
      have h := abs_alphaCoef_le (A := E.A (s - k)) (B := E.B (s - k)) hApos
      simpa only [Q3Env.alpha] using h
    rw [hK.B_eq (s - k), abs_mul, abs_of_nonneg hrho] at h1
    have h2 : 0 ≤ E.rho * |E.W1 (s - k)| := mul_nonneg hrho (abs_nonneg _)
    have h3 : E.rho * |E.W1 (s - k)| / E.A (s - k)
        ≤ E.rho * |E.W1 (s - k)| / (‖F.kmom (s - k)‖ ^ 2 / 2) :=
      div_le_div_of_nonneg_left h2 (by positivity) (hK.A_ge (s - k) hqsk)
    have h4 : E.rho * |E.W1 (s - k)| / (‖F.kmom (s - k)‖ ^ 2 / 2)
        = 2 * E.rho * |E.W1 (s - k)| / ‖F.kmom (s - k)‖ ^ 2 := by ring
    linarith
  -- the geometry `‖k‖ ≤ 2‖s-k‖`
  have hpq : ‖F.kmom k‖ ≤ 2 * ‖F.kmom (s - k)‖ := by
    have hrt : ‖F.kmom k‖ - ‖F.kmom s‖ ≤ ‖F.kmom (s - k)‖ := by
      rw [hsub]
      have h1 : ‖F.kmom k‖ - ‖F.kmom s‖ ≤ |‖F.kmom k‖ - ‖F.kmom s‖| := le_abs_self _
      have h2 : |‖F.kmom k‖ - ‖F.kmom s‖| ≤ ‖F.kmom k - F.kmom s‖ :=
        abs_norm_sub_norm_le _ _
      rw [norm_sub_rev (F.kmom k) (F.kmom s)] at h2
      linarith
    have h3 : 1 / (4 * E.KH * E.aScat) ≤ ‖F.kmom k‖ / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
      have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * E.KH * E.aScat)).mp hPHk
      linarith
    have h4 : 2 * (E.KL * Real.sqrt (E.mu * E.aScat)) ≤ ‖F.kmom k‖ / 2 := by
      have hs8 : 2 * (E.KL * Real.sqrt (E.mu * E.aScat)) ≤ 1 / (4 * E.KH * E.aScat) := by
        have h8pos : 0 < 8 * E.KH * E.aScat := by positivity
        have h4pos : 0 < 4 * E.KH * E.aScat := by positivity
        have hmul : E.KL * Real.sqrt (E.mu * E.aScat) * (8 * E.KH * E.aScat) ≤ 1 := by
          rw [le_div_iff₀ h8pos] at hsmall8
          simpa only [mul_comm] using hsmall8
        rw [le_div_iff₀ h4pos]
        nlinarith [hmul]
      linarith [hs8, h3]
    linarith [hrt, hPLs, h4]
  -- the AM–GM split
  have hcore : |E.W1 k| * |E.W1 (s - k)| / ‖F.kmom (s - k)‖ ^ 2
      ≤ E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 + E.W1 (s - k) ^ 2 / ‖F.kmom (s - k)‖ ^ 2 := by
    rw [← sq_abs (E.W1 k), ← sq_abs (E.W1 (s - k))]
    exact mul_div_sq_le (abs_nonneg _) (abs_nonneg _) hp hqpos hpq
  have hfac : |E.W1 k| * (2 * E.rho * |E.W1 (s - k)| / ‖F.kmom (s - k)‖ ^ 2)
      = 2 * E.rho * (|E.W1 k| * |E.W1 (s - k)| / ‖F.kmom (s - k)‖ ^ 2) := by ring
  calc |E.W1 k * E.alpha (s - k)|
      = |E.W1 k| * |E.alpha (s - k)| := abs_mul _ _
    _ ≤ |E.W1 k| * (2 * E.rho * |E.W1 (s - k)| / ‖F.kmom (s - k)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hα (abs_nonneg _)
    _ = 2 * E.rho * (|E.W1 k| * |E.W1 (s - k)| / ‖F.kmom (s - k)‖ ^ 2) := hfac
    _ ≤ 2 * E.rho * (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 +
          E.W1 (s - k) ^ 2 / ‖F.kmom (s - k)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)


end Work.BoseC3QAll
