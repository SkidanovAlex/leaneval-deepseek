import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.NB4Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

open Work.FTS.Galerkin (Fn)

set_option maxHeartbeats 800000

/-! ## The five even pieces of the second group

`N_b4_g2` prices the pieces `NBlk α w Φs Φg k`, `k ∈ {10, 12, 14, 16, 18}`, by a single
`α`-free constant times `1 + HkNorm α 5 w`.  We use the same constant `K := 8*C^4 + 1`
(with `C ≥ 1` the context constant) for all five pieces; it dominates every coefficient
that arises from the two product rules:

* piece `10 = -(2α)·(Vs · φD_zw)`:  coefficient `2αC³ ≤ 2C³`;
* piece `12 = -(1/2)·(FKw · D_θw)`: coefficient `(1/2)C²`;
* piece `14 = (1/2)·(FKneg · D_θw)`: coefficient `(1/2)C²`;
* piece `16 = -sin²θ·(FKw · w)`:     coefficient `C³`;
* piece `18 = -sin²θ·(FK(F_*) · w)`: coefficient `C³`.

Each coefficient is `≤ 8*C^4 + 1` (for `C ≥ 1`), and the factor `1 + HkNorm α 5 w` is
nonnegative, so the coefficient bound transfers to `K·(1 + HkNorm α 5 w)`. -/

/-- Coefficient bound for the `α`-small pieces `10`: `2αC³ ≤ 8C⁴+1` for `C ≥ 1`, `α ≤ 1`. -/
private lemma coef_alpha_C3 {C α : ℝ} (hC : 1 ≤ C) (hα1 : α ≤ 1) :
    2 * α * C ^ 3 ≤ 8 * C ^ 4 + 1 := by
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC
  have hC3 : (0 : ℝ) ≤ C ^ 3 := by positivity
  have h1 : α * C ^ 3 ≤ C ^ 3 := by
    calc α * C ^ 3 ≤ 1 * C ^ 3 := mul_le_mul_of_nonneg_right hα1 hC3
      _ = C ^ 3 := one_mul _
  have h2 : 2 * C ^ 3 ≤ 8 * C ^ 4 + 1 := by
    have hC3' : (0 : ℝ) ≤ 2 * C ^ 3 := by positivity
    have h4C : (1 : ℝ) ≤ 4 * C := by linarith
    have h : 2 * C ^ 3 ≤ 8 * C ^ 4 := by
      calc 2 * C ^ 3 = (2 * C ^ 3) * 1 := (mul_one _).symm
        _ ≤ (2 * C ^ 3) * (4 * C) := mul_le_mul_of_nonneg_left h4C hC3'
        _ = 8 * C ^ 4 := by ring
    linarith
  linarith

/-- Coefficient bound for the `C²`-pieces `12`, `14`: `(1/2)C² ≤ 8C⁴+1`. -/
private lemma coef_C2 {C : ℝ} (hC : 1 ≤ C) : (1 / 2) * C ^ 2 ≤ 8 * C ^ 4 + 1 := by
  nlinarith [hC, sq_nonneg (C ^ 2), sq_nonneg (C - 1)]

/-- Coefficient bound for the `C³`-pieces `16`, `18`: `C³ ≤ 8C⁴+1` for `C ≥ 1`. -/
private lemma coef_C3 {C : ℝ} (hC : 1 ≤ C) : C ^ 3 ≤ 8 * C ^ 4 + 1 := by
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC
  have hC3 : (0 : ℝ) ≤ C ^ 3 := by positivity
  have h : C ^ 3 ≤ C ^ 4 := by
    calc C ^ 3 = C ^ 3 * 1 := (mul_one _).symm
      _ ≤ C ^ 3 * C := mul_le_mul_of_nonneg_left hC hC3
      _ = C ^ 4 := by ring
  nlinarith [h]

/-- Absorption of the `C`-factor of the outer `-sin²θ`-multiplication
(`hSinMul` gives `Xn (sin²θ·f) ≤ C·Xn f`): `C·(C³·G) ≤ (8C⁴+1)·G`. -/
private lemma C_mul_C3 {C G : ℝ} (hG : 0 ≤ G) :
    C * (C ^ 3 * G) ≤ (8 * C ^ 4 + 1) * G := by
  rw [show C * (C ^ 3 * G) = C ^ 4 * G from by ring]
  exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (C ^ 2)]) hG

/-- Piece `10`: `-(2α)·(Vs · φD_zw)`, through `mulW_absorb` at `s = 1`. -/
private theorem N_b4_g2_10 {C C₀ Ce Cs α : ℝ} {Φs w Φg : Fn}
    (ctx : NB4Ctx C C₀ Ce Cs α Φs w Φg) :
    Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 10) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 10)
        ≤ (8 * C ^ 4 + 1) * (1 + Work.Spaces.HkNorm α 5 w) := by
  have hQ : (0 : ℝ) ≤ C * (1 + Work.Spaces.HkNorm α 5 w) :=
    mul_nonneg ctx.hCpos.le zero_le_G
  have hbF : Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z *
      Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) ≤ C * α ^ 1 := by
    simpa only [pow_one] using ctx.VsW
  have h := mulW_absorb ctx.hα0 ctx.hα1 ctx.hCpos ctx.hPW (c := -(2 * α)) (s := 1)
    (by norm_num) ctx.hCpos.le hQ ctx.Vssm ctx.VsWm ctx.phiDzwqo hbF ctx.phiDzwX
  have habs : |(-(2 * α))| = 2 * α := by
    rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos ctx.hα0]
  rw [habs] at h
  refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1, ?_⟩
  refine le_trans h.2 ?_
  rw [show 2 * α * C * C * (C * (1 + Work.Spaces.HkNorm α 5 w))
      = (2 * α * C ^ 3) * (1 + Work.Spaces.HkNorm α 5 w) from by ring]
  exact mul_le_mul_of_nonneg_right (coef_alpha_C3 ctx.hCone ctx.hα1) zero_le_G

/-- Piece `12`: `-(1/2)·(FKw · D_θw)`, through `mulQo_absorb` at `s = 2`. -/
private theorem N_b4_g2_12 {C C₀ Ce Cs α : ℝ} {Φs w Φg : Fn}
    (ctx : NB4Ctx C C₀ Ce Cs α Φs w Φg) :
    Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 12) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 12)
        ≤ (8 * C ^ 4 + 1) * (1 + Work.Spaces.HkNorm α 5 w) := by
  have h := mulQo_absorb ctx.hα0 ctx.hα1 ctx.hCpos ctx.hPQo (c := -(1 / 2)) (s := 2)
    (by norm_num) ctx.hCpos.le zero_le_G ctx.FKwqo ctx.dthwqo ctx.FKwX ctx.dthwX
  have habs : |(-(1 / 2) : ℝ)| = (1 / 2 : ℝ) := by norm_num
  rw [habs] at h
  refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1, ?_⟩
  refine le_trans h.2 ?_
  rw [show (1 / 2) * C * C * (1 + Work.Spaces.HkNorm α 5 w)
      = ((1 / 2) * C ^ 2) * (1 + Work.Spaces.HkNorm α 5 w) from by ring]
  exact mul_le_mul_of_nonneg_right (coef_C2 ctx.hCone) zero_le_G

/-- Piece `14`: `(1/2)·(FKneg · D_θw)`, through `mulW_absorb` at `s = 1`. -/
private theorem N_b4_g2_14 {C C₀ Ce Cs α : ℝ} {Φs w Φg : Fn}
    (ctx : NB4Ctx C C₀ Ce Cs α Φs w Φg) :
    Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 14) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 14)
        ≤ (8 * C ^ 4 + 1) * (1 + Work.Spaces.HkNorm α 5 w) := by
  have hbF : Work.Spaces.WlInf α 4 (fun z _ => (-(2 * α)) * Work.Spaces.hKer z)
      ≤ C * α ^ 1 := by
    simpa only [pow_one] using ctx.FKnegW
  have h := mulW_absorb ctx.hα0 ctx.hα1 ctx.hCpos ctx.hPW (c := (1 / 2)) (s := 1)
    (by norm_num) ctx.hCpos.le zero_le_G ctx.FKnegsm ctx.FKnegWm ctx.dthwqo hbF ctx.dthwX
  have habs : |(1 / 2 : ℝ)| = (1 / 2 : ℝ) := by norm_num
  rw [habs] at h
  refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1, ?_⟩
  refine le_trans h.2 ?_
  rw [show (1 / 2) * C * C * (1 + Work.Spaces.HkNorm α 5 w)
      = ((1 / 2) * C ^ 2) * (1 + Work.Spaces.HkNorm α 5 w) from by ring]
  exact mul_le_mul_of_nonneg_right (coef_C2 ctx.hCone) zero_le_G

/-- Piece `16`: `-sin²θ·(FKw · w)`: inner `ℋ⁴`-product rule, then `hSinMul`. -/
private theorem N_b4_g2_16 {C C₀ Ce Cs α : ℝ} {Φs w Φg : Fn}
    (ctx : NB4Ctx C C₀ Ce Cs α Φs w Φg) :
    Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 16) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 16)
        ≤ (8 * C ^ 4 + 1) * (1 + Work.Spaces.HkNorm α 5 w) := by
  have hinner := mulQo_absorb ctx.hα0 ctx.hα1 ctx.hCpos ctx.hPQo (c := 1) (s := 2)
    (by norm_num) ctx.hCpos.le zero_le_G ctx.FKwqo ctx.wqo ctx.FKwX ctx.wX
  have hmem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.FK w z * w z θ) := by
    simpa only [one_mul] using hinner.1
  have hsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.FK w z * w z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl ctx.FKwsm ctx.wqo.1
  have h := ctx.hSinMul (fun z θ => Work.Construction.FK w z * w z θ) hsm ⟨hsm, hmem⟩
  have hXn : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK w z * w z θ)
      ≤ C ^ 3 * (1 + Work.Spaces.HkNorm α 5 w) := by
    have h2 := hinner.2
    have h3 : |(1 : ℝ)| = 1 := by norm_num
    rw [h3] at h2
    have h4 : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK w z * w z θ)
        ≤ C * C * (1 + Work.Spaces.HkNorm α 5 w) := by
      simpa only [one_mul] using h2
    rw [show C * C * (1 + Work.Spaces.HkNorm α 5 w)
        = C ^ 2 * (1 + Work.Spaces.HkNorm α 5 w) from by ring] at h4
    calc Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK w z * w z θ)
        ≤ C ^ 2 * (1 + Work.Spaces.HkNorm α 5 w) := h4
      _ ≤ C ^ 3 * (1 + Work.Spaces.HkNorm α 5 w) :=
          mul_le_mul_of_nonneg_right (by nlinarith [ctx.hCone]) zero_le_G
  refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, one_mul] using h.1, ?_⟩
  exact le_trans (le_trans h.2 (mul_le_mul_of_nonneg_left hXn ctx.hCpos.le))
    (C_mul_C3 zero_le_G)

/-- Piece `18`: `-sin²θ·(FK(F_*) · w)`: inner `𝒲^{4,∞} × ℋ⁴` product rule, then `hSinMul`. -/
private theorem N_b4_g2_18 {C C₀ Ce Cs α : ℝ} {Φs w Φg : Fn}
    (ctx : NB4Ctx C C₀ Ce Cs α Φs w Φg) :
    Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 18) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 18)
        ≤ (8 * C ^ 4 + 1) * (1 + Work.Spaces.HkNorm α 5 w) := by
  have hbF : Work.Spaces.WlInf α 4 (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z)
      ≤ C * α ^ 1 := by simpa only [pow_one] using ctx.FKFSW
  have hinner := mulW_absorb ctx.hα0 ctx.hα1 ctx.hCpos ctx.hPW (c := 1) (s := 1)
    (by norm_num) ctx.hCpos.le zero_le_G ctx.FKFSsm ctx.FKFSWm ctx.wqo hbF ctx.wX
  have hmem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
      * w z θ) := by simpa only [one_mul] using hinner.1
  have hsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z * w z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl ctx.FKFSsm ctx.wqo.1
  have h := ctx.hSinMul (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z * w z θ)
    hsm ⟨hsm, hmem⟩
  have hXn : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
      * w z θ) ≤ C ^ 3 * (1 + Work.Spaces.HkNorm α 5 w) := by
    have h2 := hinner.2
    have h3 : |(1 : ℝ)| = 1 := by norm_num
    rw [h3] at h2
    have h4 : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * w z θ) ≤ C * C * (1 + Work.Spaces.HkNorm α 5 w) := by
      simpa only [one_mul] using h2
    rw [show C * C * (1 + Work.Spaces.HkNorm α 5 w)
        = C ^ 2 * (1 + Work.Spaces.HkNorm α 5 w) from by ring] at h4
    calc Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
          * w z θ)
        ≤ C ^ 2 * (1 + Work.Spaces.HkNorm α 5 w) := h4
      _ ≤ C ^ 3 * (1 + Work.Spaces.HkNorm α 5 w) :=
          mul_le_mul_of_nonneg_right (by nlinarith [ctx.hCone]) zero_le_G
  refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, one_mul] using h.1, ?_⟩
  exact le_trans (le_trans h.2 (mul_le_mul_of_nonneg_left hXn ctx.hCpos.le))
    (C_mul_C3 zero_le_G)

theorem N_b4_g2 (C C₀ Ce Cs : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.NB4Ctx C C₀ Ce Cs α Φs w Φg →
    ∀ k ∈ ({10, 12, 14, 16, 18} : Finset ℕ),
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
        ≤ K * (1 + Work.Spaces.HkNorm α 5 w) := by
  refine ⟨8 * C ^ 4 + 1, by nlinarith [sq_nonneg C, sq_nonneg (C ^ 2)], ?_⟩
  intro α _ Φs w Φg ctx k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact N_b4_g2_10 ctx
  · exact N_b4_g2_12 ctx
  · exact N_b4_g2_14 ctx
  · exact N_b4_g2_16 ctx
  · exact N_b4_g2_18 ctx

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
