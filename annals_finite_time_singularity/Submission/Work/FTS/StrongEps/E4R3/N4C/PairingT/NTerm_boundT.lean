/-
# `E4R3/N4C/PairingT/NTerm_boundT` — the honest `N`-block of the §8 assembly

The estimate for the twenty pieces of the `N`-block,
`|IP α (N α (F_*+g) (Φ_*+Φ_g)) g| ≤ 20·(K₀(C+1)·Pbd α X)` (`X = |g|_{ℋ⁴}`), in the honest
context `BlkCtxO` of `PairingT.RowInputs`.

This is the honest (`HQo α 4 = SmoothOpen ∧ HkMem α 4`) analogue of
`Work.FTS.Open2.NTerm_bound2` over `RowInputs2'`/`Good`, with the per-piece bounds supplied by
`pieceBdO`/`pieceDirO` and the `IP`-linearity by `IPO_add4`/`IPO_add5` of `PairingT.Atoms`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.RowInputs
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.RowInputs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C.PairingT

open Work.FTS.Galerkin (Fn)
open Work.FTS.VocabO (HQo)
open Work.FTS.Nonlin (Xn Pbd N1gg N1gs N1sg N1ss N2gg N2gs N2sg N2ss N3gg N3gs N3sg
  N3ss N4gg N4gs N4sg N4ss N5gg N5gs N5sg N5ss
  Pbd_nonneg alpha_sq_mul_le_Pbd sqrt_mul_sq_le_Pbd rpow_neg_half_mul_cube_le_Pbd
  rpow_three_half_mul_sq_le_Pbd cube_le_Pbd cube_alpha_mul_le_Pbd)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- `|a + b + c + d| ≤ |a| + |b| + |c| + |d|`. -/
theorem abs_sum_le_fourT (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith [h1, h2, h3, abs_nonneg a, abs_nonneg b, abs_nonneg c, abs_nonneg d]

/-- **The `N`-block of the pairing estimate** (twenty pieces): with the honest context
`BlkCtxO`, `|IP α (N α (F_*+g) (Φ_*+Φ_g)) g| ≤ 20·(K₀(C+1)·Pbd α X)`. -/
theorem NTerm_boundT {IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    {α₂ Ct K₀ C C₀ α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn}
    (h : Work.FTS.StrongEps.E4R3.N4C.BlkCtxO IP α₂ Ct K₀ C C₀ α g Φs Φg) :
    |IP α (Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) g|
      ≤ 20 * (K₀ * (C + 1) * Work.FTS.Nonlin.Pbd α (Work.FTS.Nonlin.Xn α g)) := by
  set Nv := Work.Construction.N α (Work.Construction.Ftot α g)
    (fun z θ => Φs z θ + Φg z θ) with hNvdef
  set X := Xn α g with hXdef
  have hE : N4ExtraH IP α₂ Ct := h.hE
  have hα : 0 < α := h.hα
  have hα1 : α ≤ 1 := h.hα1
  have hαIoc : α ∈ Set.Ioc 0 α₂ := h.hαIoc
  have hCt : 0 < Ct := h.hCt
  have hK₀Ct : Ct ≤ K₀ := h.hK₀Ct
  have hK₀one : 1 ≤ K₀ := h.hK₀one
  have hK₀pos : 0 < K₀ := h.hK₀pos
  have hC : 0 < C := h.hC
  have hR : RowInputsTO IP α C g Φs Φg := h.hR
  have hg4 : HQo α 4 g := h.hg4
  have hX0 : 0 ≤ X := Work.Spaces.HkNorm_nonneg α 4 g
  have hPbd0 : 0 ≤ Pbd α X := Pbd_nonneg hα.le hX0
  have hconv : K₀ * (C + 1) * Pbd α X ≤ C₀ * C * Pbd α X := by
    have hb := mul_le_mul_of_nonneg_right h.hbigK hPbd0
    linarith [hb]
  -- the `GoodO` witnesses of the nineteen `N₁`--`N₅` pieces
  have g8 : GoodO α (N1gg α g Φg) := hR.r8.1
  have g9 : GoodO α (N1gs α g Φg) := hR.r9.1
  have g10 : GoodO α (N1sg α Φs g) := hR.r10.1
  have g11 : GoodO α (N1ss α Φs) := hR.r11.1
  have g12 : GoodO α (N2gg α g Φg) := hR.r12.1
  have g13 : GoodO α (N2gs α g Φg) := hR.r13.1
  have g14 : GoodO α (N2sg α Φs g) := hR.r14.1
  have g15 : GoodO α (N2ss α Φs) := hR.r15.1
  have g16 : GoodO α (N3gg α g Φg) := hR.r16.1
  have g17 : GoodO α (N3gs α g Φg) := hR.r17.1
  have g18 : GoodO α (N3sg α Φs g) := hR.r18.1
  have g19 : GoodO α (N3ss α Φs) := hR.r19.1
  have g20 : GoodO α (N4gg α g) := hR.r20.1
  have g21 : GoodO α (N4gs α g) := hR.r21.1
  have g22 : GoodO α (N4sg α g) := hR.r22.1
  have g23 : GoodO α (N4ss α) := hR.r23.1
  have g24 : GoodO α (N5gg g) := hR.r24.1
  have g25 : GoodO α (N5gs α g) := hR.r25.1
  have g26 : GoodO α (N5sg α g) := hR.r25.2.1
  have g27 : GoodO α (N5ss α) := hR.r26.1
  -- the five four-term groups, and the whole `N`
  have gG1 : GoodO α (N1gg α g Φg + N1gs α g Φg + N1sg α Φs g + N1ss α Φs) :=
    goodO_add (goodO_add (goodO_add g8 g9) g10) g11
  have gG2 : GoodO α (N2gg α g Φg + N2gs α g Φg + N2sg α Φs g + N2ss α Φs) :=
    goodO_add (goodO_add (goodO_add g12 g13) g14) g15
  have gG3 : GoodO α (N3gg α g Φg + N3gs α g Φg + N3sg α Φs g + N3ss α Φs) :=
    goodO_add (goodO_add (goodO_add g16 g17) g18) g19
  have gG4 : GoodO α (N4gg α g + N4gs α g + N4sg α g + N4ss α) :=
    goodO_add (goodO_add (goodO_add g20 g21) g22) g23
  have gG5 : GoodO α (N5gg g + N5gs α g + N5sg α g + N5ss α) :=
    goodO_add (goodO_add (goodO_add g24 g25) g26) g27
  have gG12 : GoodO α ((N1gg α g Φg + N1gs α g Φg + N1sg α Φs g + N1ss α Φs)
      + (N2gg α g Φg + N2gs α g Φg + N2sg α Φs g + N2ss α Φs)) := goodO_add gG1 gG2
  have gG123 : GoodO α ((N1gg α g Φg + N1gs α g Φg + N1sg α Φs g + N1ss α Φs)
      + (N2gg α g Φg + N2gs α g Φg + N2sg α Φs g + N2ss α Φs)
      + (N3gg α g Φg + N3gs α g Φg + N3sg α Φs g + N3ss α Φs)) := goodO_add gG12 gG3
  have gG1234 : GoodO α ((N1gg α g Φg + N1gs α g Φg + N1sg α Φs g + N1ss α Φs)
      + (N2gg α g Φg + N2gs α g Φg + N2sg α Φs g + N2ss α Φs)
      + (N3gg α g Φg + N3gs α g Φg + N3sg α Φs g + N3ss α Φs)
      + (N4gg α g + N4gs α g + N4sg α g + N4ss α)) := goodO_add gG123 gG4
  have gGsum : GoodO α ((N1gg α g Φg + N1gs α g Φg + N1sg α Φs g + N1ss α Φs)
      + (N2gg α g Φg + N2gs α g Φg + N2sg α Φs g + N2ss α Φs)
      + (N3gg α g Φg + N3gs α g Φg + N3sg α Φs g + N3ss α Φs)
      + (N4gg α g + N4gs α g + N4sg α g + N4ss α)
      + (N5gg g + N5gs α g + N5sg α g + N5ss α)) := goodO_add gG1234 gG5
  have hNv : GoodO α Nv :=
    goodO_of_eqOn_Qd gGsum (fun z θ hzθ => by
      rw [hNvdef, hR.hN z θ hzθ]; simp only [Pi.add_apply])
  -- the block
  set G1 : Fn := N1gg α g Φg + N1gs α g Φg + N1sg α Φs g + N1ss α Φs with hG1def
  set G2 : Fn := N2gg α g Φg + N2gs α g Φg + N2sg α Φs g + N2ss α Φs with hG2def
  set G3 : Fn := N3gg α g Φg + N3gs α g Φg + N3sg α Φs g + N3ss α Φs with hG3def
  set G4 : Fn := N4gg α g + N4gs α g + N4sg α g + N4ss α with hG4def
  set G5 : Fn := N5gg g + N5gs α g + N5sg α g + N5ss α with hG5def
  have hcongr : IP α Nv g = IP α (G1 + G2 + G3 + G4 + G5) g := by
    refine hE.congr α hαIoc Nv _ g hR.hkN ?_ hg4 ?_
    · rw [hG1def, hG2def, hG3def, hG4def, hG5def]
      exact gGsum
    · intro z θ hzθ
      rw [hNvdef, hR.hN z θ hzθ, hG1def, hG2def, hG3def, hG4def, hG5def]
      simp only [Pi.add_apply]
      try ring
  have h1 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N1gg α g Φg)
    (α ^ (-(1 / 2 : ℝ)) * X ^ 2) hR.r8.2 (by
      have he : α ^ (-(1 / 2 : ℝ)) * X ^ 2 * X = α ^ (-(1 / 2 : ℝ)) * X ^ 3 := by ring
      rw [he]; exact rpow_neg_half_mul_cube_le_Pbd hα hα1 hX0) hR.r8.1
  have h2 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N1gs α g Φg)
    (Real.sqrt α * X) hR.r9.2 (by
      have he : Real.sqrt α * X * X = Real.sqrt α * X ^ 2 := by ring
      rw [he]; exact sqrt_mul_sq_le_Pbd hα hX0) hR.r9.1
  have h3 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N1sg α Φs g)
    (Real.sqrt α * X) hR.r10.2 (by
      have he : Real.sqrt α * X * X = Real.sqrt α * X ^ 2 := by ring
      rw [he]; exact sqrt_mul_sq_le_Pbd hα hX0) hR.r10.1
  have h4 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N1ss α Φs)
    (α ^ 2) hR.r11.2 (alpha_sq_mul_le_Pbd hα hX0) hR.r11.1
  have h5 := pieceDirO (N2gg α g Φg) (α ^ (-(1 / 2 : ℝ)) * X ^ 3) hR.r12.2
    (rpow_neg_half_mul_cube_le_Pbd hα hα1 hX0) hPbd0 hC hK₀one
  have h6 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N2gs α g Φg)
    (α ^ (3 / 2 : ℝ) * X) hR.r13.2 (by
      have he : α ^ (3 / 2 : ℝ) * X * X = α ^ (3 / 2 : ℝ) * X ^ 2 := by ring
      rw [he]; exact rpow_three_half_mul_sq_le_Pbd hα hα1 hX0) hR.r13.1
  have h7 := pieceDirO (N2sg α Φs g) (Real.sqrt α * X ^ 2) hR.r14.2
    (sqrt_mul_sq_le_Pbd hα hX0) hPbd0 hC hK₀one
  have h8 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N2ss α Φs)
    (α ^ 2) hR.r15.2 (alpha_sq_mul_le_Pbd hα hX0) hR.r15.1
  -- **row 16 at its actual rate `X³`** (the relaxed rate of the honest row table)
  have h9 := pieceDirO (N3gg α g Φg) (X ^ 3) hR.r16.2
    (cube_le_Pbd hα hα1 hX0) hPbd0 hC hK₀one
  have h10 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N3gs α g Φg)
    (α ^ (3 / 2 : ℝ) * X) hR.r17.2 (by
      have he : α ^ (3 / 2 : ℝ) * X * X = α ^ (3 / 2 : ℝ) * X ^ 2 := by ring
      rw [he]; exact rpow_three_half_mul_sq_le_Pbd hα hα1 hX0) hR.r17.1
  have h11 := pieceDirO (N3sg α Φs g) (α ^ (3 / 2 : ℝ) * X ^ 2) hR.r18.2
    (rpow_three_half_mul_sq_le_Pbd hα hα1 hX0) hPbd0 hC hK₀one
  have h12 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N3ss α Φs)
    (α ^ 3) hR.r19.2 (cube_alpha_mul_le_Pbd hα hα1 hX0) hR.r19.1
  have h13 := pieceDirO (N4gg α g) (α ^ (-(1 / 2 : ℝ)) * X ^ 3) hR.r20.2
    (rpow_neg_half_mul_cube_le_Pbd hα hα1 hX0) hPbd0 hC hK₀one
  have h14 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N4gs α g)
    (α ^ (3 / 2 : ℝ) * X) hR.r21.2 (by
      have he : α ^ (3 / 2 : ℝ) * X * X = α ^ (3 / 2 : ℝ) * X ^ 2 := by ring
      rw [he]; exact rpow_three_half_mul_sq_le_Pbd hα hα1 hX0) hR.r21.1
  have h15 := pieceDirO (N4sg α g) (Real.sqrt α * X ^ 2) hR.r22.2
    (sqrt_mul_sq_le_Pbd hα hX0) hPbd0 hC hK₀one
  have h16 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N4ss α)
    (α ^ 3) hR.r23.2 (cube_alpha_mul_le_Pbd hα hα1 hX0) hR.r23.1
  have h17 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N5gg g)
    (X ^ 2) hR.r24.2 (cube_le_Pbd hα hα1 hX0) hR.r24.1
  have h18 : |IP α (N5gs α g) g| + |IP α (N5sg α g) g| ≤ K₀ * (C + 1) * Pbd α X := by
    have hgs : |IP α (N5gs α g) g| ≤ Ct * Xn α (N5gs α g) * X :=
      hE.cs α hαIoc _ g hR.r25.1 hg4
    have hsg : |IP α (N5sg α g) g| ≤ Ct * Xn α (N5sg α g) * X :=
      hE.cs α hαIoc _ g hR.r25.2.1 hg4
    have hsum : Xn α (N5gs α g) + Xn α (N5sg α g) ≤ C * (Real.sqrt α * X) := hR.r25.2.2
    have hb : Ct * Xn α (N5gs α g) * X + Ct * Xn α (N5sg α g) * X
        ≤ Ct * (C * (Real.sqrt α * X)) * X := by
      have he : Ct * Xn α (N5gs α g) * X + Ct * Xn α (N5sg α g) * X
          = Ct * (Xn α (N5gs α g) + Xn α (N5sg α g)) * X := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hCt.le) hX0
    have hs : Real.sqrt α * X * X = Real.sqrt α * X ^ 2 := by ring
    have hPB : Real.sqrt α * X ^ 2 ≤ Pbd α X := sqrt_mul_sq_le_Pbd hα hX0
    have heq : Ct * (C * (Real.sqrt α * X)) * X = Ct * C * (Real.sqrt α * X * X) := by ring
    have hfin : Ct * C * (Real.sqrt α * X * X) ≤ K₀ * (C + 1) * Pbd α X := by
      rw [hs]
      have h1' : Ct * C * Pbd α X ≤ K₀ * C * Pbd α X :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK₀Ct hC.le) hPbd0
      have h2' : K₀ * C * Pbd α X ≤ K₀ * (C + 1) * Pbd α X := by
        have h := mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) hPbd0
        nlinarith [h, hK₀pos.le, hPbd0]
      exact le_trans (mul_le_mul_of_nonneg_left hPB (by positivity)) (le_trans h1' h2')
    linarith [hgs, hsg, hb, le_of_eq heq, hfin]
  have h19 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N5ss α)
    (α ^ 2) hR.r26.2 (alpha_sq_mul_le_Pbd hα hX0) hR.r26.1
  have hG1 : |IP α G1 g| ≤ 4 * (K₀ * (C + 1) * Pbd α X) := by
    have hsum : IP α G1 g = IP α (N1gg α g Φg) g + IP α (N1gs α g Φg) g
        + IP α (N1sg α Φs g) g + IP α (N1ss α Φs) g := by
      rw [hG1def]
      exact IPO_add4 hE hαIoc hg4 g8 g9 g10 g11 (goodO_add g8 g9)
        (goodO_add (goodO_add g8 g9) g10)
    rw [hsum]
    linarith [abs_sum_le_fourT (IP α (N1gg α g Φg) g)
      (IP α (N1gs α g Φg) g) (IP α (N1sg α Φs g) g) (IP α (N1ss α Φs) g),
      h1, h2, h3, h4, hconv,
      abs_nonneg (IP α (N1gg α g Φg) g), abs_nonneg (IP α (N1gs α g Φg) g),
      abs_nonneg (IP α (N1sg α Φs g) g), abs_nonneg (IP α (N1ss α Φs) g)]
  have hG2 : |IP α G2 g| ≤ 4 * (K₀ * (C + 1) * Pbd α X) := by
    have hsum : IP α G2 g = IP α (N2gg α g Φg) g + IP α (N2gs α g Φg) g
        + IP α (N2sg α Φs g) g + IP α (N2ss α Φs) g := by
      rw [hG2def]
      exact IPO_add4 hE hαIoc hg4 g12 g13 g14 g15 (goodO_add g12 g13)
        (goodO_add (goodO_add g12 g13) g14)
    rw [hsum]
    linarith [abs_sum_le_fourT (IP α (N2gg α g Φg) g)
      (IP α (N2gs α g Φg) g) (IP α (N2sg α Φs g) g) (IP α (N2ss α Φs) g),
      h5, h6, h7, h8, hconv,
      abs_nonneg (IP α (N2gg α g Φg) g), abs_nonneg (IP α (N2gs α g Φg) g),
      abs_nonneg (IP α (N2sg α Φs g) g), abs_nonneg (IP α (N2ss α Φs) g)]
  have hG3 : |IP α G3 g| ≤ 4 * (K₀ * (C + 1) * Pbd α X) := by
    have hsum : IP α G3 g = IP α (N3gg α g Φg) g + IP α (N3gs α g Φg) g
        + IP α (N3sg α Φs g) g + IP α (N3ss α Φs) g := by
      rw [hG3def]
      exact IPO_add4 hE hαIoc hg4 g16 g17 g18 g19 (goodO_add g16 g17)
        (goodO_add (goodO_add g16 g17) g18)
    rw [hsum]
    linarith [abs_sum_le_fourT (IP α (N3gg α g Φg) g)
      (IP α (N3gs α g Φg) g) (IP α (N3sg α Φs g) g) (IP α (N3ss α Φs) g),
      h9, h10, h11, h12, hconv,
      abs_nonneg (IP α (N3gg α g Φg) g), abs_nonneg (IP α (N3gs α g Φg) g),
      abs_nonneg (IP α (N3sg α Φs g) g), abs_nonneg (IP α (N3ss α Φs) g)]
  have hG4 : |IP α G4 g| ≤ 4 * (K₀ * (C + 1) * Pbd α X) := by
    have hsum : IP α G4 g = IP α (N4gg α g) g + IP α (N4gs α g) g
        + IP α (N4sg α g) g + IP α (N4ss α) g := by
      rw [hG4def]
      exact IPO_add4 hE hαIoc hg4 g20 g21 g22 g23 (goodO_add g20 g21)
        (goodO_add (goodO_add g20 g21) g22)
    rw [hsum]
    linarith [abs_sum_le_fourT (IP α (N4gg α g) g) (IP α (N4gs α g) g)
      (IP α (N4sg α g) g) (IP α (N4ss α) g), h13, h14, h15, h16, hconv,
      abs_nonneg (IP α (N4gg α g) g), abs_nonneg (IP α (N4gs α g) g),
      abs_nonneg (IP α (N4sg α g) g), abs_nonneg (IP α (N4ss α) g)]
  have hG5 : |IP α G5 g| ≤ 4 * (K₀ * (C + 1) * Pbd α X) := by
    have hsum : IP α G5 g = IP α (N5gg g) g + IP α (N5gs α g) g
        + IP α (N5sg α g) g + IP α (N5ss α) g := by
      rw [hG5def]
      exact IPO_add4 hE hαIoc hg4 g24 g25 g26 g27 (goodO_add g24 g25)
        (goodO_add (goodO_add g24 g25) g26)
    rw [hsum]
    linarith [abs_sum_le_fourT (IP α (N5gg g) g) (IP α (N5gs α g) g)
      (IP α (N5sg α g) g) (IP α (N5ss α) g), h17, h18, h19, hconv,
      abs_nonneg (IP α (N5gg g) g), abs_nonneg (IP α (N5gs α g) g),
      abs_nonneg (IP α (N5sg α g) g), abs_nonneg (IP α (N5ss α) g)]
  have hsplitN : IP α Nv g = IP α G1 g + IP α G2 g + IP α G3 g + IP α G4 g + IP α G5 g := by
    rw [hcongr]
    exact IPO_add5 hE hαIoc hg4
      (by rw [hG1def]; exact gG1) (by rw [hG2def]; exact gG2)
      (by rw [hG3def]; exact gG3) (by rw [hG4def]; exact gG4)
      (by rw [hG5def]; exact gG5)
      (by rw [hG1def, hG2def]; exact gG12)
      (by rw [hG1def, hG2def, hG3def]; exact gG123)
      (by rw [hG1def, hG2def, hG3def, hG4def]; exact gG1234)
  have htri : |IP α G1 g + IP α G2 g + IP α G3 g + IP α G4 g + IP α G5 g|
      ≤ |IP α G1 g| + |IP α G2 g| + |IP α G3 g| + |IP α G4 g| + |IP α G5 g| := by
    have h8 := abs_add_le (IP α G1 g + IP α G2 g + IP α G3 g + IP α G4 g) (IP α G5 g)
    have h9 := abs_sum_le_fourT (IP α G1 g) (IP α G2 g) (IP α G3 g) (IP α G4 g)
    linarith [h8, h9]
  have h20 : |IP α G1 g| + |IP α G2 g| + |IP α G3 g| + |IP α G4 g| + |IP α G5 g|
      ≤ 20 * (K₀ * (C + 1) * Pbd α X) := by
    linarith [hG1, hG2, hG3, hG4, hG5,
      abs_nonneg (IP α G1 g), abs_nonneg (IP α G2 g), abs_nonneg (IP α G3 g),
      abs_nonneg (IP α G4 g), abs_nonneg (IP α G5 g)]
  rw [hsplitN]
  linarith [htri, h20]

end Work.FTS.StrongEps.E4R3.N4C.PairingT
