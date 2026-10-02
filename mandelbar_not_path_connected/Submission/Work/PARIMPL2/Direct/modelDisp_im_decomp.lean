import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL2.Direct.norm_modelDisp_add_rational_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.PARIMPL2.Direct

open Complex

/-!
# The second-order decomposition of the model displacement

This file proves the bound

  `‖Φ + (τ + (h₁ − τ²)·ζ)‖ ≤ 100·λ² + (2 + 4‖h₁‖ + 2A)·‖ζ‖²`

for the model displacement `Φ = modelDisp (iλ) h u` of the rotated local normal form,
where `ζ = ecalPt (iλ) u`, `h ζ = τ + h₁ ζ + O(ζ²)` (uniformly on the chart ball, with the
quadratic remainder bounded by `A‖ζ‖²`), `‖τ‖ = 1`, `‖ζ‖ ≤ 4/R`, `λR² ≤ 1` and `R ≥ 128`.

The mechanism: `Φ = −h(ζ)/(1 + ζ h(ζ)) + O(λ²)` (`norm_modelDisp_add_rational_le`), and the
rational expression `h(ζ)/(1+ζ h(ζ))` differs from its second-order Taylor polynomial
`τ + (h₁ − τ²)ζ` by

  `N/c`,   `N = ε − ζτ(h₁ζ + ε) − ζ²H(h₁ − τ²)`,  `c = 1 + ζH`, `ε = H − τ − h₁ζ`, `H = h ζ`,

which is `O(‖h₁‖‖ζ‖² + A‖ζ‖² + ‖ζ‖²)`; the linear term `‖h₁‖` is controlled by the two
available bounds on `K = ‖h₁‖‖ζ‖` (the pointwise germ bound and the ball bound), and the
arithmetic endgame is the lemma `arith_main` below.
-/

/-- The arithmetic endgame of the second-order decomposition.

`N/c` is bounded by `(2 + 4B + 2A)ρ²` from the two available bounds on `‖N‖`: the cruder one
(`E + ρ²B + ρE + 2ρ²(B+1)`, using `‖H‖ ≤ 2`) and the finer one (using `‖H‖ ≤ 1 + Bρ + E`).
If the cruder one already suffices, done; otherwise it forces `A ≤ 3/20`, `B ≤ 1/6`, and then
the finer one gives room to spare. -/
private lemma arith_main (A B ρ E NN cN : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ0 : 0 ≤ ρ)
    (hρle : ρ ≤ 1/32) (hE2 : E ≤ A * ρ^2) (hNN0 : 0 ≤ NN) (hcN : 15/16 ≤ cN)
    (hN1 : NN ≤ (A*(1+ρ) + 3*B + 2) * ρ^2)
    (hN2 : NN ≤ (A*(1+ρ) + 2*B + 1 + (B*ρ)*B + (B*ρ) + E*B + E) * ρ^2) :
    NN / cN ≤ (2 + 4*B + 2*A) * ρ^2 := by
  have hρ2 : (0:ℝ) ≤ ρ^2 := sq_nonneg ρ
  have hcpos : (0:ℝ) < cN := by linarith
  have hstep : NN / cN ≤ (16/15) * NN := by
    rw [div_le_iff₀ hcpos]; nlinarith [hcN, hNN0]
  by_cases hcase : (16/15) * (A*(1+ρ) + 3*B + 2) ≤ 2 + 4*B + 2*A
  · calc NN / cN ≤ (16/15) * NN := hstep
      _ ≤ (16/15) * ((A*(1+ρ) + 3*B + 2) * ρ^2) := by nlinarith [hN1]
      _ = ((16/15) * (A*(1+ρ) + 3*B + 2)) * ρ^2 := by ring
      _ ≤ (2 + 4*B + 2*A) * ρ^2 := by nlinarith [hcase, hρ2]
  · push Not at hcase
    have hC1le : A*(1+ρ) + 3*B + 2 ≤ A*(33/32) + 3*B + 2 := by nlinarith [hA, hρle]
    have hbig : (16/15) * (A*(33/32) + 3*B + 2) > 2 + 4*B + 2*A := by nlinarith [hcase, hC1le]
    have hAsmall : A ≤ 3/20 := by nlinarith [hbig]
    have hBsmall : B ≤ 1/6 := by nlinarith [hbig]
    have hBρ : B*ρ ≤ (1/6)*(1/32) := by nlinarith [hB, hρle, hBsmall]
    have hE' : E ≤ (3/20)*(1/1024) := by nlinarith [hE2, hAsmall, hρle, hρ0]
    have h1 : A*(1+ρ) ≤ A*(33/32) := by nlinarith [hA, hρle]
    have h2 : (B*ρ)*B ≤ (1/6)*(1/32)*(1/6) := by nlinarith [hB, hρ0, hρle, hBsmall]
    have h4 : E*B ≤ (3/20)*(1/1024)*(1/6) := by nlinarith [hE', hB, hBsmall]
    have hC2le : A*(1+ρ) + 2*B + 1 + (B*ρ)*B + (B*ρ) + E*B + E
        ≤ A*(33/32) + 2*B + 1 + (1/6)*(1/32)*(1/6) + (1/6)*(1/32) + (3/20)*(1/1024)*(1/6) + (3/20)*(1/1024) := by
      linarith
    calc NN / cN ≤ (16/15) * NN := hstep
      _ ≤ (16/15) * ((A*(1+ρ) + 2*B + 1 + (B*ρ)*B + (B*ρ) + E*B + E) * ρ^2) := by nlinarith [hN2]
      _ ≤ (16/15) * ((A*(33/32) + 2*B + 1 + (1/6)*(1/32)*(1/6) + (1/6)*(1/32) + (3/20)*(1/1024)*(1/6) + (3/20)*(1/1024)) * ρ^2) := by nlinarith [hC2le, hρ2]
      _ ≤ (2 + 4*B + 2*A) * ρ^2 := by nlinarith [hA, hB, hρ2]

theorem modelDisp_im_decomp (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1)
    (h : ℂ → ℂ) (tau h1 : ℂ) (A r : ℝ) (hA : 0 ≤ A) (hr : 0 < r)
    (hb : Work.PARIMPL.ParBounds h tau h1 A r) (htau1 : ‖tau - 1‖ ≤ 1 / 8)
    (u : ℂ) (hz : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ≤ 4 / R)
    (hzr : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ < r) :
    ‖Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u
        + (tau + (h1 - tau ^ 2) * Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u)‖
      ≤ 100 * lam ^ 2 + (2 + 4 * ‖h1‖ + 2 * A)
          * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ^ 2 := by
  have hRpos : (0:ℝ) < R := by linarith
  have hlam_le : lam ≤ 1/8 := by
    have h1' : lam ≤ 1/R^2 := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < R^2)]; linarith
    have h2 : (1:ℝ)/R^2 ≤ 1/8 := by
      apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 8); nlinarith
    linarith
  set a : ℂ := (lam : ℂ) * Complex.I with ha
  set ζ : ℂ := Work.Implosion.ecalPt a u with hζdef
  set H : ℂ := h ζ with hHdef
  set Φ : ℂ := Work.Implosion.modelDisp a h u with hΦdef
  set c : ℂ := 1 + ζ * H with hcdef
  set ε : ℂ := H - tau - h1 * ζ with hεdef
  set N : ℂ := H - (tau + (h1 - tau^2) * ζ) * c with hNdef
  set B : ℝ := ‖h1‖ with hBdef
  set ρ : ℝ := ‖ζ‖ with hρdef
  set E : ℝ := ‖ε‖ with hEdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; exact norm_nonneg ζ
  have hρle : ρ ≤ 1/32 := by
    rw [hρdef]
    have h1 : (4:ℝ)/R ≤ 4/128 := by
      rw [div_le_div_iff₀ hRpos (by norm_num : (0:ℝ) < 128)]; linarith
    linarith
  have hρ2 : (0:ℝ) ≤ ρ^2 := sq_nonneg ρ
  have hB0 : 0 ≤ B := by rw [hBdef]; exact norm_nonneg h1
  have hζr : ρ < r := by rw [hρdef]; exact hzr
  have hτn : ‖tau‖ = 1 := hb.2.1
  have hH2 : ‖H‖ ≤ 2 := by
    rw [hHdef]; exact hb.2.2.2.1 ζ (by rw [← hρdef]; exact hζr)
  have hE2 : E ≤ A * ρ^2 := by
    have hg := hb.2.2.1 ζ (by rw [← hρdef]; exact hζr)
    rw [hEdef, hεdef, hHdef, hρdef]
    exact hg
  have hζH : ‖ζ * H‖ ≤ 1/16 := by
    rw [norm_mul]
    calc ‖ζ‖ * ‖H‖ ≤ (1/32) * 2 :=
          mul_le_mul (by rw [← hρdef]; exact hρle) hH2 (norm_nonneg H) (by norm_num)
      _ = 1/16 := by norm_num
  have hcge : (15:ℝ)/16 ≤ ‖c‖ := by
    have hh := norm_sub_le (1 + ζ*H) (ζ*H)
    rw [add_sub_cancel_right, norm_one] at hh
    rw [hcdef]
    linarith
  have hcne : c ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hcge; norm_num at hcge
  have hfirst : ‖Φ + H / c‖ ≤ 100 * lam^2 := by
    have hh := norm_modelDisp_add_rational_le lam hlam hlam_le h u
      (by rw [← hζdef, ← hρdef]; exact le_trans hρle (by norm_num))
      (by rw [← hHdef]; exact hH2)
    simpa [hΦdef, hζdef, hHdef, hcdef] using hh
  -- the algebraic identity for `N` and its norm bound
  have hNid : N = ε - ζ*tau*(h1*ζ + ε) - ζ^2*H*(h1 - tau^2) := by
    rw [hNdef, hcdef, hεdef]; ring
  have hh1ζ : ‖h1*ζ‖ = B*ρ := by rw [norm_mul, ← hBdef, ← hρdef]
  have h2N : ‖h1*ζ + ε‖ ≤ B*ρ + E := by
    calc ‖h1*ζ + ε‖ ≤ ‖h1*ζ‖ + ‖ε‖ := norm_add_le _ _
      _ = B*ρ + E := by rw [hh1ζ, ← hEdef]
  have hτ2 : ‖h1 - tau^2‖ ≤ B + 1 := by
    calc ‖h1 - tau^2‖ ≤ ‖h1‖ + ‖tau^2‖ := norm_sub_le _ _
      _ = B + 1 := by rw [norm_pow, hτn, ← hBdef]; norm_num
  have hnormN : ‖N‖ ≤ E + ρ^2*B + ρ*E + ρ^2*‖H‖*(B+1) := by
    have h1' : ‖ζ*tau*(h1*ζ+ε)‖ ≤ ρ*1*(B*ρ + E) := by
      rw [norm_mul, norm_mul, hτn, ← hρdef]
      exact mul_le_mul_of_nonneg_left h2N (by positivity)
    have h4' : ‖ζ^2*H*(h1-tau^2)‖ ≤ ρ^2*‖H‖*(B+1) := by
      rw [norm_mul, norm_mul, norm_pow, ← hρdef]
      exact mul_le_mul_of_nonneg_left hτ2 (by positivity)
    have hsub := norm_sub_le ε (ζ*tau*(h1*ζ + ε))
    rw [← hEdef] at hsub
    calc ‖N‖ = ‖ε - ζ*tau*(h1*ζ + ε) - (ζ^2*H*(h1 - tau^2))‖ := by rw [hNid]
      _ ≤ ‖ε - ζ*tau*(h1*ζ + ε)‖ + ‖ζ^2*H*(h1 - tau^2)‖ := norm_sub_le _ _
      _ ≤ (E + ρ*1*(B*ρ + E)) + ρ^2*‖H‖*(B + 1) := by linarith
      _ = E + ρ^2*B + ρ*E + ρ^2*‖H‖*(B+1) := by ring
  have hH3 : ‖H‖ ≤ 1 + B*ρ + E := by
    have heq : H = tau + (h1*ζ + ε) := by rw [hHdef, hεdef]; ring
    rw [heq]
    calc ‖tau + (h1*ζ + ε)‖ ≤ ‖tau‖ + ‖h1*ζ + ε‖ := norm_add_le _ _
      _ ≤ 1 + (B*ρ + E) := by rw [hτn]; linarith
      _ = 1 + B*ρ + E := by ring
  -- the two coefficient bounds
  have hN1 : ‖N‖ ≤ (A*(1+ρ) + 3*B + 2) * ρ^2 := by
    have h1 : ρ^2*‖H‖*(B+1) ≤ 2*ρ^2*(B+1) := by
      have h : (0:ℝ) ≤ ρ^2*(B+1) := by positivity
      calc ρ^2*‖H‖*(B+1) = ‖H‖ * (ρ^2*(B+1)) := by ring
        _ ≤ 2 * (ρ^2*(B+1)) := mul_le_mul_of_nonneg_right hH2 h
        _ = 2*ρ^2*(B+1) := by ring
    have hρE : ρ*E ≤ A*ρ^3 := by
      have := mul_le_mul_of_nonneg_left hE2 hρ0; linarith [this]
    nlinarith [hnormN, h1, hE2, hρE, hρ0, hρ2, hA, hB0]
  have hN2 : ‖N‖ ≤ (A*(1+ρ) + 2*B + 1 + (B*ρ)*B + (B*ρ) + E*B + E) * ρ^2 := by
    have h1 : ρ^2*‖H‖*(B+1) ≤ ρ^2*(1 + B*ρ + E)*(B+1) := by
      have h : (0:ℝ) ≤ ρ^2*(B+1) := by positivity
      calc ρ^2*‖H‖*(B+1) = ‖H‖ * (ρ^2*(B+1)) := by ring
        _ ≤ (1+B*ρ+E) * (ρ^2*(B+1)) := mul_le_mul_of_nonneg_right hH3 h
        _ = ρ^2*(1+B*ρ+E)*(B+1) := by ring
    have hρE : ρ*E ≤ A*ρ^3 := by
      have := mul_le_mul_of_nonneg_left hE2 hρ0; linarith [this]
    nlinarith [hnormN, h1, hE2, hρE, hρ0, hρ2, hA, hB0]
  have hNcle : ‖N / c‖ ≤ (2 + 4*B + 2*A) * ρ^2 := by
    rw [norm_div]
    exact arith_main A B ρ E ‖N‖ ‖c‖ hA hB0 hρ0 hρle hE2 (norm_nonneg N) hcge hN1 hN2
  -- assembly
  have hNdiv : N / c = H / c - (tau + (h1 - tau^2) * ζ) := by
    rw [hNdef]; field_simp
  have hkey : Φ + (tau + (h1 - tau^2) * ζ) = (Φ + H / c) - N / c := by
    rw [hNdiv]; ring
  calc ‖Φ + (tau + (h1 - tau^2) * ζ)‖ = ‖(Φ + H / c) - N / c‖ := by rw [hkey]
    _ ≤ ‖Φ + H / c‖ + ‖N / c‖ := norm_sub_le _ _
    _ ≤ 100 * lam^2 + (2 + 4*B + 2*A) * ρ^2 := add_le_add hfirst hNcle
    _ = 100 * lam^2 + (2 + 4*‖h1‖ + 2*A) * ‖ζ‖^2 := by rw [hBdef, hρdef]

end Work.PARIMPL2.Direct
