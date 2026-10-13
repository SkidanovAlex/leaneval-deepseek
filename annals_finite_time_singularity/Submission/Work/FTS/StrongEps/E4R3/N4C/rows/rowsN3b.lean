/-
# `E4R3/N4C/rows/rowsN3b` — the honest rows 18 and 19

`|(N₃^{*g}, g)| ≤ K α^{3/2} X²` and `‖N₃^{**}‖_{ℋ⁴} ≤ K α³` in the *honest* (class-`C`,
open-quadrant) context `CtxT`.

* **Row 18** (`N₃^{*g} = -2α·V(Φ̃_*)·D_z g`, Elgindi §8, tex 1484): the piece is `(-2α)` times the
  product `f·D_z g` of the coefficient `f = V(Φ̃_*)` and the `D_z`-derivative of the perturbation,
  so the pairing bound is the `D_z`-transport clause `N4ExtraH.t3`.  That clause asks for
  `SmoothOpen f`, `WlInfMem α 4 f`, `CoefThMem 3 f` — exactly `smoothOpen_PhiTs`/`smoothOpen_Vop`
  plus the fields `StarPkgo2.VW` and `StarPkgo.Vth` — and for the honest `g`-side data, which
  `CtxT` supplies (`hSmoothOpen`, `hkMem4`, `hkMem5`, `hdecay`).  The honesty of the first
  argument of `IP` is the primed product rule `N4Norm'.wprod`.  The two coefficient norms are
  both `≤ max Cs 1·α`, so `2α · Ct α^{-1/2} · 2 max Cs 1 α = 4 Ct max Cs 1 · α^{3/2}`.

* **Row 19** (`N₃^{**} = -2α·V(Φ̃_*)·D_zF_*`): this is `Work.FTS.StrongPersist.L3Rhs.N3ssPriced`,
  which is stated for exactly the data at hand (`α ∈ (0,1]` and `StarPkgo2 α Cs Φs`) and prices
  the `Cs`-dependence as `(1 + |Cs|)`.

The proof of row 18 is a copy of the frozen `Nonlinear.Open.Row18` with the `GalClass` data
replaced by the `CtxT` projections (in particular `HkMem_Dz_quad` → `CtxT.hkMemDz`,
`galClass_DecayAll4` → `CtxT.hdecay`), and with the frozen clause bundle `N4Extra'` replaced by
the honest `N4ExtraH` (whose `smul` takes the honest class `HQo α 4` for the first argument).
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.Hon
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.HonDecay
import Submission.Work.FTS.NonlinRows.smoothOpen_radA
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C.rows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **Row 18 in the honest class**: `|(N₃^{*g}, g)| ≤ K α^{3/2} X²`. -/
theorem rowN3sg_honest (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      |IP α (Work.FTS.Nonlin.N3sg α Φs g) g|
        ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  have hCt : 0 < Ct := hE.pos.1
  refine ⟨4 * Ct * max Cs 1 + 1, by positivity, ?_⟩
  intro α g Φs Φg hC
  have hα : 0 < α := hC.hα
  have hα1 : α ≤ 1 := hC.hα1
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hC.hαα₂⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hCs1 : 0 ≤ max Cs 1 := le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_right Cs 1))
  -- the star package and the coefficient `f = V(Φ̃_*)`
  have hs2 : Work.FTS.VocabO2.StarPkgo2 α Cs Φs := hC.hs
  have hs : Work.FTS.VocabO.StarPkgo α Cs Φs := hs2.toStarPkgo
  have hfsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.NonlinRows.smoothOpen_Vop
      (Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hs)
  have hfWmem : Work.Spaces.WlInfMem α 4
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) := hs2.VW.1
  have hfWle : Work.Spaces.WlInf α 4
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) ≤ max Cs 1 * α :=
    le_trans hs2.VW.2 (mul_le_mul_of_nonneg_right (le_max_left Cs 1) hα.le)
  have hfΔmem : Work.FTS.VocabO.CoefThMem 3
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) := hs.Vth.1
  have hfΔle : Work.FTS.VocabO.CoefTh 3
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) ≤ max Cs 1 * α :=
    le_trans hs.Vth.2 (mul_le_mul_of_nonneg_right (le_max_left Cs 1) hα.le)
  -- the `g`-side data
  have hreg4 : Work.FTS.VocabO.HQo α 4 g := hC.hqo4
  have hmem5 : Work.Spaces.HkMem α 5 g := hC.hkMem5
  have hDzMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g) := hC.hkMemDz
  have hDzSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g) := hC.hSmoothOpen.Dz
  -- the product `V(Φ̃_*)·D_z g` is in `ℋ⁴` (also the honesty of the first argument of `IP`)
  have hprod : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
        * Work.Spaces.Dz g z θ) :=
    (hN.wprod α hIoc (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) (Work.Spaces.Dz g)
      hfsm hfWmem ⟨hDzSm, hDzMem⟩).1
  have hprodQ : Work.FTS.VocabO.HQo α 4
      (fun z θ => Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
        * Work.Spaces.Dz g z θ) :=
    ⟨hfsm.mul hDzSm, hprod⟩
  -- `N₃^{*g}` is `-2α` times that product
  have hN3 : Work.FTS.Nonlin.N3sg α Φs g
      = fun z θ => (-2 * α) * (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
          * Work.Spaces.Dz g z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N3sg]
    ring
  have hIPeq : IP α (Work.FTS.Nonlin.N3sg α Φs g) g
      = (-2 * α) * IP α (fun z θ => Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
          * Work.Spaces.Dz g z θ) g := by
    rw [hN3]
    exact hE.smul α hIoc (-2 * α) _ g hprodQ hreg4
  rw [hIPeq]
  have habs : |(-2 : ℝ) * α| = 2 * α := by
    rw [abs_of_neg (by linarith : (-2 : ℝ) * α < 0)]
    ring
  rw [abs_mul, habs]
  -- the `D_z`-transport estimate for the coefficient `V(Φ̃_*)`
  have ht3 := hE.t3 α hIoc (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) g
    hfsm hfWmem hfΔmem hC.hSmoothOpen hC.hkMem4 hmem5 hC.hdecay
  refine (mul_le_mul_of_nonneg_left ht3 (by linarith : (0 : ℝ) ≤ 2 * α)).trans ?_
  -- the weighted sum of the two coefficient norms is `≤ 2 Cs α`
  have hWsum : Work.Spaces.WlInf α 4
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
      + Work.FTS.VocabO.CoefTh 3 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
      ≤ 2 * (max Cs 1 * α) := by
    linarith
  have hstep : Ct * α ^ (-(1 / 2 : ℝ))
        * (Work.Spaces.WlInf α 4 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
          + Work.FTS.VocabO.CoefTh 3 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)))
        * Work.FTS.Nonlin.Xn α g ^ 2
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (2 * (max Cs 1 * α)) * Work.FTS.Nonlin.Xn α g ^ 2 := by
    have hpre : (0 : ℝ) ≤ Ct * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hCt.le hA0
    have hX2 : 0 ≤ Work.FTS.Nonlin.Xn α g ^ 2 := pow_nonneg hX0 2
    calc Ct * α ^ (-(1 / 2 : ℝ))
          * (Work.Spaces.WlInf α 4 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
            + Work.FTS.VocabO.CoefTh 3 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)))
          * Work.FTS.Nonlin.Xn α g ^ 2
        = (Ct * α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.WlInf α 4 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
              + Work.FTS.VocabO.CoefTh 3
                  (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))))
          * Work.FTS.Nonlin.Xn α g ^ 2 := by ring
      _ ≤ (Ct * α ^ (-(1 / 2 : ℝ)) * (2 * (max Cs 1 * α))) * Work.FTS.Nonlin.Xn α g ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWsum hpre) hX2
      _ = Ct * α ^ (-(1 / 2 : ℝ)) * (2 * (max Cs 1 * α)) * Work.FTS.Nonlin.Xn α g ^ 2 := by
          ring
  refine (mul_le_mul_of_nonneg_left hstep (by linarith : (0 : ℝ) ≤ 2 * α)).trans ?_
  -- `α · α^{-1/2} · α = α^{3/2}`
  have hpow : α * α ^ (-(1 / 2 : ℝ)) * α = α ^ (3 / 2 : ℝ) := by
    have h1 := Real.rpow_add hα (1 : ℝ) (1 / 2 : ℝ)
    rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num, Real.rpow_one] at h1
    have h2 := Real.rpow_add hα (1 : ℝ) (-(1 / 2 : ℝ))
    rw [show (1 : ℝ) + -(1 / 2) = 1 / 2 by norm_num, Real.rpow_one] at h2
    rw [h1, h2]
    ring
  have harith : 2 * α * (Ct * α ^ (-(1 / 2 : ℝ)) * (2 * (max Cs 1 * α))
        * Work.FTS.Nonlin.Xn α g ^ 2)
      = 4 * Ct * max Cs 1 * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g ^ 2) := by
    rw [← hpow]
    ring
  rw [harith]
  have h32 : 0 ≤ α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (pow_nonneg hX0 2)
  have hcs : 0 ≤ 4 * Ct * max Cs 1 := by positivity
  nlinarith [mul_nonneg hcs h32]

/-- **Row 19 in the honest class**: `‖N₃^{**}‖_{ℋ⁴} ≤ K α³` (from `N3ssPriced`, whose hypotheses
are exactly `0 < α ≤ 1` and `StarPkgo2 α Cs Φs`). -/
theorem rowN3ss_honest (Cs : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {Φs : Fn},
      0 < α → α ≤ 1 → Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs) ≤ K * α ^ 3 := by
  obtain ⟨C19, hC19pos, hC19⟩ := Work.FTS.StrongPersist.L3Rhs.N3ssPriced
  refine ⟨C19 * (1 + |Cs|) + 1, ?_, fun {α Φs} hα hα1 hs => ?_⟩
  · have h1 : (0 : ℝ) ≤ 1 + |Cs| := by positivity
    have h2 : 0 < C19 * (1 + |Cs|) := mul_pos hC19pos (by have := abs_nonneg Cs; linarith)
    linarith
  · have h := (hC19 α ⟨hα, hα1⟩ Cs Φs hs).2
    have h3 : (0 : ℝ) ≤ α ^ 3 := by positivity
    have h4 : C19 * (1 + |Cs|) * α ^ 3 ≤ (C19 * (1 + |Cs|) + 1) * α ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) h3
    linarith

theorem rowsN3b (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      |IP α (Work.FTS.Nonlin.N3sg α Φs g) g|
          ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g ^ 2) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs) ≤ K * α ^ 3 := by
  obtain ⟨K18, hK18pos, h18⟩ := rowN3sg_honest IP hN hE
  obtain ⟨K19, hK19pos, h19⟩ := rowN3ss_honest Cs
  refine ⟨max K18 K19, lt_max_iff.mpr (Or.inl hK18pos), ?_⟩
  intro α g Φs Φg hC
  constructor
  · exact le_trans (h18 hC)
      (mul_le_mul_of_nonneg_right (le_max_left K18 K19)
        (mul_nonneg (Real.rpow_nonneg hC.hα.le _)
          (pow_nonneg (Work.Spaces.HkNorm_nonneg α 4 g) 2)))
  · exact le_trans (h19 hC.hα hC.hα1 hC.hs)
      (mul_le_mul_of_nonneg_right (le_max_right K18 K19) (pow_nonneg hC.hα.le 3))

end Work.FTS.StrongEps.E4R3.N4C.rows
