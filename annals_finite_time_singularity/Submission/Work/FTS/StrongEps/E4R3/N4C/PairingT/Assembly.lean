/-
# `E4R3/N4C/PairingT/Assembly` — the honest §8 assembly (`pairing_bound_of_rowsT`)

This module assembles the pairing estimate

  `|rhsPair IP α g (Φ_* + Φ_g)| ≤ CcN · Pbd α (Xn α g)`

from the honest `IP`-interface `N4C.N4ExtraH` and the honest row table `N4C.RowsT`.

It is the honest (class-`C`, open-quadrant) analogue of `Open2.pairing_bound_of_rows2_open`:
the four blocks of `gRHS = -μ̄·AK + N₀ + N + N_*` are estimated by
`PairingT.AKTerm_boundT`, `PairingT.N0Term_boundT`, `PairingT.NTerm_boundT` and
`PairingT.NsTerm_boundT` in the honest context `PairingT.BlkCtxO`, the exact split
`gRHS = -μ̄AK + N₀ + N + N_*` is linearised with the honest `IPO_add4`, and the `μ̄`/`μ` bounds
come from the three `L₁₂`-rows `rl0`-`rl2` through `Nonlin.Apriori.mubar_bound_mul` /
`Nonlin.mu_bound_mul` / `Nonlin.mu_le_half`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.RowInputs
import Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.smoothOpen_pieces_N0
import Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.smoothOpen_pieces_N
import Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.N0Term_boundT
import Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.NTerm_boundT
import Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.NsTerm_boundT
import Submission.Work.FTS.Apriori.Defs
import Submission.Work.Construction.MufunS

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)
open Work.FTS.VocabO (HQo)
open Work.FTS.Nonlin

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- **The `-μ̄AK` block**, honest version of `Open2.AKTerm_bound2`. -/
theorem AKTerm_boundT {IP : ℝ → Fn → Fn → ℝ} {α₂ Ct K₀ C C₀ α : ℝ} {g Φs Φg : Fn} {A : ℝ}
    (h : BlkCtxO IP α₂ Ct K₀ C C₀ α g Φs Φg)
    (hA : |A| ≤ 2 * (C * (α ^ 2 + Real.sqrt α * (Xn α g)
      + α ^ (-(3 / 2 : ℝ)) * (Xn α g) ^ 2))) :
    |IP α (fun z θ => -A * Work.Construction.AK α z θ) g|
      ≤ 6 * K₀ * C ^ 2 * Pbd α (Xn α g) := by
  have hE : N4ExtraH IP α₂ Ct := h.hE
  have hα : 0 < α := h.hα
  have hαIoc : α ∈ Set.Ioc 0 α₂ := h.hαIoc
  have hCt : 0 < Ct := h.hCt
  have hK₀Ct : Ct ≤ K₀ := h.hK₀Ct
  have hK₀pos : 0 < K₀ := h.hK₀pos
  have hC : 0 < C := h.hC
  have hR : RowInputsTO IP α C g Φs Φg := h.hR
  have hg4 : HQo α 4 g := h.hg4
  have hX0 : 0 ≤ Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hPbd0 : 0 ≤ Pbd α (Xn α g) := Pbd_nonneg hα.le hX0
  have hsm : IP α (fun z θ => -A * Work.Construction.AK α z θ) g
      = -A * IP α (Work.Construction.AK α) g :=
    hE.smul α hαIoc (-A) (Work.Construction.AK α) g hR.rak.1 hg4
  have hAK : |IP α (Work.Construction.AK α) g| ≤ Ct * Xn α (Work.Construction.AK α) * Xn α g :=
    hE.cs α hαIoc _ g hR.rak.1 hg4
  have hAK' : |IP α (Work.Construction.AK α) g| ≤ K₀ * C * Xn α g := by
    have h1 : Ct * Xn α (Work.Construction.AK α) * Xn α g ≤ Ct * C * Xn α g :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR.rak.2 hCt.le) hX0
    have h2 : Ct * C * Xn α g ≤ K₀ * C * Xn α g :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK₀Ct hC.le) hX0
    linarith [hAK, h1, h2]
  have hm1 : α ^ 2 * Xn α g ≤ Pbd α (Xn α g) := alpha_sq_mul_le_Pbd hα hX0
  have hm2 : Real.sqrt α * Xn α g * Xn α g ≤ Pbd α (Xn α g) := by
    have he : Real.sqrt α * Xn α g * Xn α g = Real.sqrt α * Xn α g ^ 2 := by ring
    rw [he]; exact sqrt_mul_sq_le_Pbd hα hX0
  have hm3 : α ^ (-(3 / 2 : ℝ)) * Xn α g * Xn α g * Xn α g ≤ Pbd α (Xn α g) := by
    have he : α ^ (-(3 / 2 : ℝ)) * Xn α g * Xn α g * Xn α g
        = α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 3 := by ring
    rw [he]; exact rpow_neg_three_half_mul_cube_le_Pbd hα hX0
  have hprod : |A| * |IP α (Work.Construction.AK α) g|
      ≤ 2 * (C * (α ^ 2 + Real.sqrt α * Xn α g + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2))
        * (K₀ * C * Xn α g) :=
    mul_le_mul hA hAK' (abs_nonneg _) (by positivity)
  have hexp : 2 * (C * (α ^ 2 + Real.sqrt α * Xn α g + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2))
      * (K₀ * C * Xn α g)
      = 2 * K₀ * C ^ 2 * (α ^ 2 * Xn α g + Real.sqrt α * Xn α g * Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Xn α g * Xn α g * Xn α g) := by ring
  have hsum : α ^ 2 * Xn α g + Real.sqrt α * Xn α g * Xn α g
      + α ^ (-(3 / 2 : ℝ)) * Xn α g * Xn α g * Xn α g ≤ 3 * Pbd α (Xn α g) := by
    linarith [hm1, hm2, hm3]
  have hfin : 2 * K₀ * C ^ 2 * (α ^ 2 * Xn α g + Real.sqrt α * Xn α g * Xn α g
        + α ^ (-(3 / 2 : ℝ)) * Xn α g * Xn α g * Xn α g)
      ≤ 6 * K₀ * C ^ 2 * Pbd α (Xn α g) := by
    have h1 : 2 * K₀ * C ^ 2 * (α ^ 2 * Xn α g + Real.sqrt α * Xn α g * Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Xn α g * Xn α g * Xn α g)
        ≤ 2 * K₀ * C ^ 2 * (3 * Pbd α (Xn α g)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    have h2 : 2 * K₀ * C ^ 2 * (3 * Pbd α (Xn α g)) = 6 * K₀ * C ^ 2 * Pbd α (Xn α g) := by
      ring
    linarith [h1, h2.le, h2.ge]
  rw [hsm, abs_mul, abs_neg]
  exact hprod.trans (hexp.le.trans hfin)

/-- **The honest §8 pairing estimate, from the honest row table.**  The honest analogue of
`Open2.pairing_bound_of_rows2_open` (its pairing conjunct), with the row bundle supplied as a
hypothesis rather than derived inside. -/
theorem pairing_bound_of_rowsT (IP : ℝ → Fn → Fn → ℝ) {α₂ Ct Ce Cs : ℝ}
    (hCs : 0 < Cs) (hCe : 0 < Ce)
    (hE : N4ExtraH IP α₂ Ct) (hR : RowsT IP α₂ Ce Cs) :
    ∃ CcN α₄ : ℝ, 0 < CcN ∧ 0 < α₄ ∧ α₄ ≤ α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₄, ∀ {g Φs Φg : Fn},
        CtxT Cs Ce α₂ α g Φs Φg →
        Xn α g ≤ α ^ (7 / 4 : ℝ) →
        |Work.FTS.Apriori.rhsPair IP α g (fun z θ => Φs z θ + Φg z θ)|
          ≤ CcN * Pbd α (Xn α g) := by
  have hCt : 0 < Ct := hE.pos.1
  have hα₂ : 0 < α₂ := hE.pos.2
  set K₀ : ℝ := 4096 * (Ct + 4) with hK₀def
  have hK₀pos : 0 < K₀ := by rw [hK₀def]; positivity
  have hK₀Ct : Ct ≤ K₀ := by rw [hK₀def]; nlinarith [hCt.le]
  have hK₀one : (1 : ℝ) ≤ K₀ := by rw [hK₀def]; nlinarith [hCt.le]
  set CC : ℝ := max hR.K₁ (max hR.K₂ hR.K₃) with hCCdef
  have hCCpos : 0 < CC := lt_of_lt_of_le hR.hK₁ (le_max_left _ _)
  have hK1C : hR.K₁ ≤ CC := le_max_left _ _
  have hK2C : hR.K₂ ≤ CC := le_trans (le_max_left _ _) (le_max_right _ _)
  have hK3C : hR.K₃ ≤ CC := le_trans (le_max_right _ _) (le_max_right _ _)
  set C₀ : ℝ := 4096 * K₀ * (CC + 1) + 4096 * K₀ / CC with hC₀def
  have hC₀pos : 0 < C₀ := by rw [hC₀def]; positivity
  have hC₀Ceq : C₀ * CC = 4096 * K₀ * (CC * (CC + 1)) + 4096 * K₀ := by
    rw [hC₀def]; field_simp; try ring
  have hbig : 6 * K₀ * CC ^ 2 + 58 * (K₀ * (CC + 1)) ≤ C₀ * CC := by
    rw [hC₀Ceq]; nlinarith [hK₀pos.le, hCCpos.le]
  have hbigK : K₀ * (CC + 1) ≤ C₀ * CC := by
    nlinarith [hbig, hK₀pos.le, hCCpos.le]
  obtain ⟨α₄μ, hα₄μ_pos, hα₄μ⟩ := mu_le_half (4 * CC) (by positivity)
  refine ⟨C₀ * CC, min α₂ (min α₄μ 1), mul_pos hC₀pos hCCpos,
    lt_min hα₂ (lt_min hα₄μ_pos one_pos), min_le_left _ _, ?_⟩
  intro α hαle g Φs Φg hctx hX74
  have hα : 0 < α := hαle.1
  have hαα₄ : α ≤ min α₂ (min α₄μ 1) := hαle.2
  have hαα₂ : α ≤ α₂ := le_trans hαα₄ (min_le_left _ _)
  have hαμ : α ≤ α₄μ := le_trans hαα₄ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hα1 : α ≤ 1 := le_trans hαα₄ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hαIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hgC : Work.FTS.ClassC.ClassC α g := hctx.hg
  have hco : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g := hctx.hco
  have hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg := hctx.hell
  have hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs := hctx.hs
  have hX0 : 0 ≤ Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hPbd0 : 0 ≤ Pbd α (Xn α g) := Pbd_nonneg hα.le hX0
  have hsmN0 := PairingT.smoothOpen_pieces_N0 hα hα1 hgC hell hstar
  have hsmN := PairingT.smoothOpen_pieces_N hα hα1 hgC hell hstar
  have hRI : RowInputsTO IP α CC g Φs Φg :=
    rowInputsTO_of_rows hα hα1 hαα₂ hgC hco hell hstar
      (hR.rowsN0 hctx) (hR.rowsN hctx) (hR.rowsAux hctx)
      hK1C hK2C hK3C (hR.hk hctx) (hR.splits hctx) hsmN0 hsmN
  have hblk : BlkCtxO IP α₂ Ct K₀ CC C₀ α g Φs Φg :=
    { hE := hE, hα := hα, hαα₂ := hαα₂, hα1 := hα1, hgC := hgC, hco := hco, hR := hRI,
      hCt := hCt, hK₀pos := hK₀pos, hK₀Ct := hK₀Ct, hK₀one := hK₀one, hC := hCCpos,
      hbigK := hbigK }
  set N0v := Work.Construction.N0 α (Work.Construction.Ftot α g) g with hN0vdef
  set Nv := Work.Construction.N α (Work.Construction.Ftot α g)
    (fun z θ => Φs z θ + Φg z θ) with hNvdef
  set μ := Work.Construction.mufunS α N0v Nv g with hμdef
  have hμ4 : |μ| ≤ 4 * CC * (α + α ^ (-(1 : ℝ)) * Xn α g
      + α ^ (-(5 / 2 : ℝ)) * Xn α g ^ 2) := by
    have h := mu_bound_mul (N0v := N0v) (Nv := Nv) hα hα1 hX0 hCCpos.le hRI.rl0 hRI.rl1 hRI.rl2
    rw [hμdef]
    exact h.trans (le_of_eq (by ring_nf))
  have hμ1 : μ ≠ -1 := by
    intro h
    have hh : |μ| ≤ 1 / 2 :=
      hα₄μ α hα hαμ (Xn α g) hX0 hX74 μ hμ4
    rw [h] at hh
    norm_num at hh
  set A := Work.Construction.mubar N0v Nv with hAdef
  have hAb : |A| ≤ 2 * (CC * (α ^ 2 + Real.sqrt α * Xn α g
      + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2)) := by
    rw [hAdef]; exact mubar_bound_mul hCCpos.le hRI.rl0 hRI.rl1
  set Ns := Work.Construction.Nstar μ (Work.Construction.lamfun μ) g with hNsdef
  -- the `GoodO`-data of the four blocks
  have hg4 : HQo α 4 g := classC_hqo4 hgC
  have hAKq : GoodO α (Work.Construction.AK α) := hRI.rak.1
  have g1 : GoodO α (fun z θ => -A * Work.Construction.AK α z θ) :=
    goodO_const_mul (-A) hAKq
  have gN0v : GoodO α N0v := hRI.hkN0
  have gNv : GoodO α Nv := hRI.hkN
  have gNstarLam : GoodO α (NstarLam μ g) := by
    rw [show NstarLam μ g = (fun z θ => μ * Work.Spaces.Dz g z θ)
        + (fun z θ => (-μ) * g z θ) from by
      funext z θ; simp only [NstarLam, Pi.add_apply]; ring]
    exact goodO_add (goodO_const_mul μ hRI.hkDz) (goodO_const_mul (-μ) hg4)
  have gNs : GoodO α Ns :=
    goodO_of_eqOn_Qd gNstarLam (fun z θ _ => by
      rw [hNsdef]; exact (hRI.hNs μ hμ1 z θ).symm)
  have gs12 : GoodO α ((fun z θ => -A * Work.Construction.AK α z θ) + N0v) := goodO_add g1 gN0v
  have gs123 : GoodO α ((fun z θ => -A * Work.Construction.AK α z θ) + N0v + Nv) :=
    goodO_add gs12 gNv
  -- the exact split of `gRHS`
  have hgr : Work.Construction.gRHS α μ (Work.Construction.lamfun μ)
        (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) g
      = (fun z θ => -A * Work.Construction.AK α z θ) + N0v + Nv + Ns := by
    funext z θ
    simp only [Work.Construction.gRHS, Pi.add_apply, hAdef, hN0vdef, hNvdef, hNsdef]
    try ring
  have hIPsplit : IP α (Work.Construction.gRHS α μ (Work.Construction.lamfun μ)
        (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) g) g
      = IP α (fun z θ => -A * Work.Construction.AK α z θ) g + IP α N0v g + IP α Nv g
        + IP α Ns g := by
    rw [hgr]
    exact IPO_add4 hE hαIoc hg4 g1 gN0v gNv gNs gs12 gs123
  -- the four block estimates
  have hAKterm : |IP α (fun z θ => -A * Work.Construction.AK α z θ) g|
      ≤ 6 * K₀ * CC ^ 2 * Pbd α (Xn α g) := AKTerm_boundT hblk hAb
  have hN0term : |IP α N0v g| ≤ 7 * (K₀ * (CC + 1) * Pbd α (Xn α g)) := by
    rw [hN0vdef]; exact PairingT.N0Term_boundT hblk
  have hNterm : |IP α Nv g| ≤ 20 * (K₀ * (CC + 1) * Pbd α (Xn α g)) := by
    rw [hNvdef]; exact PairingT.NTerm_boundT hblk
  have hNsterm : |IP α Ns g| ≤ 24 * (K₀ * (CC + 1) * Pbd α (Xn α g)) := by
    rw [hNsdef]; exact PairingT.NsTerm_boundT hblk hμ1 hμ4
  have hmain : |IP α (Work.Construction.gRHS α μ (Work.Construction.lamfun μ)
        (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) g) g|
      ≤ C₀ * CC * Pbd α (Xn α g) := by
    rw [hIPsplit]
    have htri : |IP α (fun z θ => -A * Work.Construction.AK α z θ) g + IP α N0v g
        + IP α Nv g + IP α Ns g|
        ≤ |IP α (fun z θ => -A * Work.Construction.AK α z θ) g| + |IP α N0v g|
          + |IP α Nv g| + |IP α Ns g| := Work.Construction.abs_sum_le_four _ _ _ _
    have hfinal : |IP α (fun z θ => -A * Work.Construction.AK α z θ) g| + |IP α N0v g|
        + |IP α Nv g| + |IP α Ns g| ≤ C₀ * CC * Pbd α (Xn α g) := by
      have h56 : 6 * K₀ * CC ^ 2 * Pbd α (Xn α g)
          + 58 * (K₀ * (CC + 1) * Pbd α (Xn α g)) ≤ C₀ * CC * Pbd α (Xn α g) := by
        have h := mul_le_mul_of_nonneg_right hbig hPbd0
        have he : (6 * K₀ * CC ^ 2 + 58 * (K₀ * (CC + 1))) * Pbd α (Xn α g)
            = 6 * K₀ * CC ^ 2 * Pbd α (Xn α g)
              + 58 * (K₀ * (CC + 1) * Pbd α (Xn α g)) := by ring
        rw [he] at h
        exact h
      linarith [hAKterm, hN0term, hNterm, hNsterm, h56,
        abs_nonneg (IP α (fun z θ => -A * Work.Construction.AK α z θ) g),
        abs_nonneg (IP α N0v g), abs_nonneg (IP α Nv g), abs_nonneg (IP α Ns g)]
    linarith [htri, hfinal]
  simpa only [Work.FTS.Apriori.muOf, Work.FTS.Apriori.rhsPair] using hmain

end Work.FTS.StrongEps.E4R3.N4C
