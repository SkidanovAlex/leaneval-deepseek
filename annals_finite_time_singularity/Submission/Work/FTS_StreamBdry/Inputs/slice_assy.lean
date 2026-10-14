import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.Jeps_IP6_transfer_aux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.starDat
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.classCSinRate
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_bounds
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.coeff_C2
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.residual_slot_jetsB
import Submission.Work.FTS_StreamBdry.Inputs.slice_slots
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.FTS_StreamBdry.SB4.slice_L12_c2
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.SmoothStripDefs
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Leaves.L6CtxJfamP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Leaves/L6CtxJfamP.lean` — LEAF S5 (**PROVED**, session 23)

curric-46 install 2026-10-12 (`cbc/fts_apriori6_ruling.md` §3 S5).  The level-six context at the
projected mollified slices — what `H6Pair` (instantiated by the PROVED `H6Pair_ones3`) and
`H6Aux.H6Lin_IP6` consume — from `ClassC` + ball + `hEll` + `StarPkg6`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps

set_option autoImplicit false


end Work.FTS.StrongEps.EpsE4Thr.E4R4
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0_BData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks

set_option autoImplicit false
set_option maxHeartbeats 3200000

open Work.FTS.StrongPersist.H6Pair6Aux (NA1 NA4 NA5 NA6 NP3 NP4a NP4b NP5a NP5b NP6)

/-- The `N₀`-block is `C^∞` on the open quadrant (this is `H6Pair6Aux.SmoothN0`, spelled with
the `blkN0`-vocabulary). -/
theorem smoothOpen_blkN0 {α : ℝ} (hα : 0 < α) {w : ℝ → ℝ → ℝ}
    (hw : Work.FTS.EllipticEst.SmoothOpen w)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 w z)) :
    Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w) :=
  Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0 hα hw hL

/-- The `N₀`-block is `ℋ⁶`-honest: combine the `ℋ⁶`-memberships of the seven pieces of the
split `N0_split_open`. -/
theorem hkMem6_blkN0 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {w : ℝ → ℝ → ℝ}
    (hw : Work.FTS.ClassC.ClassC α w) :
    Work.Spaces.HkMem α 6
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w) := by
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hw.reg
  have hm7 : Work.Spaces.HkMem α 7 w := hw.mem
  have hm6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 6 (by norm_num) hm7
  have hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hw
  have hFstar : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have hs1 : Work.FTS.EllipticEst.SmoothOpen (NA1 α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NA1 α
  have hs2 : Work.FTS.EllipticEst.SmoothOpen (NP3 α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP3 hsmw hL
  have hs3 : Work.FTS.EllipticEst.SmoothOpen (NP4a α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP4a hsmw hL
  have hs4 : Work.FTS.EllipticEst.SmoothOpen (NP4b α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP4b hsmw hL
  have hs5 : Work.FTS.EllipticEst.SmoothOpen (NP5a α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP5a hsmw hL
  have hs6 : Work.FTS.EllipticEst.SmoothOpen (NP5b α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP5b hsmw hL
  have hs7 : Work.FTS.EllipticEst.SmoothOpen (NP6 α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP6 hsmw hL
  obtain ⟨_K12, _hK12, hNA1⟩ := Work.FTS.StrongPersist.H6Rows.FstarI12H6
  obtain ⟨hm1, _⟩ := hNA1 α hα hα1
  obtain ⟨hm2, hm3, hm4, hm5, hm6p, hm7p⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.hkmem_N0pieces_own hα hα1 hsmw hL hw.l12 hm6 hm7
  have h67 : Work.Spaces.HkMem α 6 (fun z θ => NP5b α w z θ + NP6 α w z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α 6 hs6 hs7 hm6p hm7p
  have hs67 := hs6.add hs7
  have h567 : Work.Spaces.HkMem α 6
      (fun z θ => NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ)) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α 6 hs5 hs67 hm5 h67
  have hs567 := hs5.add hs67
  have h4567 : Work.Spaces.HkMem α 6
      (fun z θ => NP4b α w z θ + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ))) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α 6 hs4 hs567 hm4 h567
  have hs4567 := hs4.add hs567
  have h34567 : Work.Spaces.HkMem α 6
      (fun z θ => NP4a α w z θ + (NP4b α w z θ
        + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ)))) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α 6 hs3 hs4567 hm3 h4567
  have hs34567 := hs3.add hs4567
  have h234567 : Work.Spaces.HkMem α 6
      (fun z θ => NP3 α w z θ + (NP4a α w z θ + (NP4b α w z θ
        + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ))))) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α 6 hs2 hs34567 hm2 h34567
  have hs234567 := hs2.add hs34567
  have h1234567 : Work.Spaces.HkMem α 6
      (fun z θ => NA1 α z θ + (NP3 α w z θ + (NP4a α w z θ + (NP4b α w z θ
        + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ)))))) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α 6 hs1 hs234567 hm1 h234567
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 6 h1234567 ?_
  intro z hz θ hθ
  exact (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.N0_split_open α hFstar
    hsmw z θ ⟨hz, hθ.1, hθ.2⟩).symm

theorem N0_BData : ∀ C₀ : ℝ, ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ w : ℝ → ℝ → ℝ,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    (∀ z θ : ℝ, 0 < z → θ ∉ Set.Ioo 0 (Real.pi / 2) → w z θ = 0) →
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w K
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w) := by
  intro C₀
  obtain ⟨K4, hK4pos, h4⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.N0_HkSq4_le C₀
  obtain ⟨K6, hK6pos, h6⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.N0_HkSq6_le C₀
  refine ⟨max K4 K6, lt_max_of_lt_left hK4pos, ?_⟩
  intro α hαIoc w hw hXw _hz
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hw
  have h5w : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by
    have h := Work.Spaces.HkSq_nonneg α 5 w
    linarith
  have h6w : (0 : ℝ) ≤ (1 + Work.Spaces.HkSq α 6 w) ^ 2 := sq_nonneg _
  have h7w : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 7 w := by
    have h := Work.Spaces.HkSq_nonneg α 7 w
    linarith
  refine ⟨smoothOpen_blkN0 hα hw.reg hL, hkMem6_blkN0 hα hα1 hw, ?_, ?_⟩
  · exact le_trans (h4 α hαIoc w hw hXw)
      (mul_le_mul_of_nonneg_right (le_max_left K4 K6) h5w)
  · have h := h6 α hαIoc w hw hXw
    have h1 : K6 * (1 + Work.Spaces.HkSq α 7 w)
        ≤ max K4 K6 * (1 + Work.Spaces.HkSq α 7 w) :=
      mul_le_mul_of_nonneg_right (le_max_right K4 K6) h7w
    have h2 : K6 * (1 + Work.Spaces.HkSq α 6 w) ^ 2
        ≤ max K4 K6 * (1 + Work.Spaces.HkSq α 6 w) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_right K4 K6) h6w
    linarith

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Decay3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `StrongEps/E4R3/Decay3.lean` — the chapter `DecayChapter3` (PROVED)

Statement from `cbc/fts_e5swap_e4chapters_B.lean` §2 (corrected chapter), on the in-place
bounded-block `EpsDecay`.  The proof is the sibling `Work.FTS.StrongEps.E4R3.Decay3_leaf`
(module `…E4R3.Decay3_leaf`), whose statement is byte-identical; the explicit majorant is
`Maj z = min 1 (√Ct · C₀α'² · z√z/(1+z)²)`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R3

set_option autoImplicit false

/-- The corrected chapter `DecayChapter3` above a `C₀`-threshold (PROVED). -/
theorem decayChapter3_leaf {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, ∀ C₀ : ℝ, C ≤ C₀ → DecayChapter3 Ce Cs C₀ ρ :=
  Work.FTS.StrongEps.E4R3.Decay3_leaf hρ

end Work.FTS.StrongEps.EpsE4Thr.E4R3
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Flow5Leaves.IP4Algebra =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Flow5Leaves/IP4Algebra.lean` — the three algebraic facts about `IP4` used by the product rule

* `IP4_add_open`  — additivity of `IP4` in its first argument on the open class `HQo α 4`
                    (`IPGen.Comm2o_three`; the `RegQ`-based `Assembly.V_core` is unusable here);
* `IP4_symm_fts`  — symmetry for arbitrary coefficients (`Assembly.vc_symm` + `H1IP_comm`);
* `IP4_cs_HQo`    — Cauchy–Schwarz on `HQo α 4` with a constant depending only on the six step
                    coefficients (three lifts of `StrongPersist.abs_HkIPStep_le` above
                    `Transfer.H1IP_cs_of_mem`).

These are the `ℋ⁴`-versions of `StrongEps/IP4_Jeps_comm.lean`'s lemmas; they are restated here
because that module imports `StrongEps.IP6_Jeps_comm`, which declares a `smoothOpen_Jeps` clashing
with the one in `StrongEps.JepsSmoothOpen` (already in the cone of `E4R3/Flow5.lean`), so that the
two cannot be imported together.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Flow5Leaves

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

local notation "IP4" => Work.FTS.CoercivityFix.Assembly.IP4

/-- **Additivity of `IP4` in its first argument on the open class `HQo α 4`** (the `Comm2o`
induction of `IPGen`, `Comm2o_three`). -/
theorem IP4_add_open {α : ℝ} (hα : 0 < α) {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} {f₁ f₂ g : Fn}
    (h₁ : Work.FTS.EllipticEst.SmoothOpen f₁) (h₂ : Work.FTS.EllipticEst.SmoothOpen f₂)
    (h₃ : Work.FTS.EllipticEst.SmoothOpen g)
    (m₁ : Work.Spaces.HkMem α 4 f₁) (m₂ : Work.Spaces.HkMem α 4 f₂)
    (m₃ : Work.Spaces.HkMem α 4 g) :
    IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (f₁ + f₂) g
      = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f₁ g + IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f₂ g :=
  (Work.FTS.IPGen.Comm2o_three α (by linarith [hα])).add f₁ f₂ g h₁ h₂ h₃ m₁ m₂ m₃

/-- **Symmetry of `IP4`** for arbitrary coefficients (the recursion `HkIPStep` preserves symmetry,
`Assembly.vc_symm`, and its base `H1IP` is symmetric, `Assembly.H1IP_comm`). -/
theorem IP4_symm_fts (c₁ c₂ c₁' c₂' c₁'' c₂'' α : ℝ) (f g : Fn) :
    IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α g f :=
  Work.FTS.CoercivityFix.Assembly.vc_symm (c₁ := c₁'') (c₂ := c₂'')
    (Work.FTS.CoercivityFix.Assembly.vc_symm (c₁ := c₁') (c₂ := c₂')
      (Work.FTS.CoercivityFix.Assembly.vc_symm (c₁ := c₁) (c₂ := c₂)
        (Work.FTS.CoercivityFix.Assembly.H1IP_comm α))) f g

/-- **Cauchy–Schwarz for `IP4` on the open class `HQo α 4`**, with a constant depending only on the
six step coefficients: three lifts of `StrongPersist.abs_HkIPStep_le` above the `ℋ¹`-bound
`Transfer.H1IP_cs_of_mem`. -/
theorem IP4_cs_HQo (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) :
    ∃ CC : ℝ, 0 < CC ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ f g : Fn,
      Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
      |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g|
        ≤ CC * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g := by
  refine ⟨(1 + |c₁''| + |c₂''|) * ((1 + |c₁'| + |c₂'|) * ((1 + |c₁| + |c₂|) * 10 ^ 22)),
    by positivity, ?_⟩
  intro α hα f g hf hg
  have hα0 : 0 < α := hα.1
  have hbase : ∀ u v : ℝ → ℝ → ℝ, Work.FTS.VocabO.HQo α 1 u → Work.FTS.VocabO.HQo α 1 v →
      |Work.Coercivity.H1IP α u v| ≤ 10 ^ 22 * Work.Spaces.HkNorm α 1 u
        * Work.Spaces.HkNorm α 1 v :=
    fun u v hu hv => Work.FTS.CoercivityFix.Transfer.H1IP_cs_of_mem α hα0 u v hu.2 hv.2
  have h1 := Work.FTS.StrongPersist.abs_HkIPStep_le (α := α) hα0 (n := 1)
    (IP := Work.Coercivity.H1IP α) (CC := 10 ^ 22) (c₁ := c₁) (c₂ := c₂)
    (by norm_num) hbase
  have h2 := Work.FTS.StrongPersist.abs_HkIPStep_le (α := α) hα0 (n := 2)
    (IP := Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α))
    (CC := (1 + |c₁| + |c₂|) * 10 ^ 22) (c₁ := c₁') (c₂ := c₂') (by positivity) h1
  have h3 := Work.FTS.StrongPersist.abs_HkIPStep_le (α := α) hα0 (n := 3)
    (IP := Work.Coercivity.HkIPStep c₁' c₂'
      (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α)))
    (CC := (1 + |c₁'| + |c₂'|) * ((1 + |c₁| + |c₂|) * 10 ^ 22))
    (c₁ := c₁'') (c₂ := c₂'') (by positivity) h2
  simpa only [Work.FTS.CoercivityFix.Assembly.IP4] using h3 f g hf hg

end Work.FTS.StrongEps.E4R3.Flow5Leaves
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.EpsWPSemitameAux.Common =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.L6Ctx_JfamP_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.RawE6Aux

theorem L6Ctx_JfamP_aux :
    ∀ C₀ Ce Cs : ℝ, ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Set.Ioc 0 α₀,
    ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
      {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn},
    Work.FTS.StrongEps.IsSmoothKernel ρ →
    (∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs → Work.FTS.StrongEps.MuLamOK α C₀ Φs E →
    ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ (g : Work.FTS.Galerkin.Fam) (τ : ℝ), 0 ≤ τ →
      Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) →
      Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 →
      Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o) α (C₀ * α ^ 2) Ce Cs E Φs
        (Work.FTS.StrongEps.JfamP ρ ε g) (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) τ :=
  Work.FTS.StrongEps.E4R3.Apriori4Proofs.L6Ctx_JfamP_proof

end Work.FTS.StrongEps.E4R3.RawE6Aux
end
-- ===== merged: Submission.Work.FTS_StreamBdry.Inputs.slice_assy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.Inputs.slice_assy` — assembly of the `SlotBd` conjunct of `slice_inputs`

`slotBd_of_pieces` turns the order-`≤ 2` jet bounds of the residual slots (`residual_slot_jetsB`)
and of the singular part (`theta_part_jets`) into a `SlotBd` for `slice (ΦR a Φs E g) τ`; the
`-! ##` sections below then transfer it to `slice (PsiCan Φs E g) τ` (`SlotBd_of_eqOn`) and add the
`C³` and `SrcOK` conjuncts (`slice_inputs_of_pieces`).
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.Inputs

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp)

set_option autoImplicit false

/-! ## `SlotBd` from the two jet bounds -/

/-- `SlotBd` of the slice of `ΦR` from the jet bounds of the residual slots and of the singular
part. -/
theorem slotBd_of_pieces {a Mv C : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ)
    (hSΨ1 : ContDiffOn ℝ 1 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ))
      Work.FTS.EllipticEst.Q0)
    (hSΘ1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Theta (pExp a)
      (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ)))
      Work.FTS.EllipticEst.Q0)
    (hSΨ3 : ContDiffOn ℝ 3 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ))
      Work.FTS.EllipticEst.Q0)
    (hSΘ3 : ContDiffOn ℝ 3 (Function.uncurry (Work.Construction.Theta (pExp a)
      (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ)))
      Work.FTS.EllipticEst.Q0)
    (hUres : ContDiffOn ℝ 2 (Function.uncurry (Ures a Φs E g τ)) Work.FTS.EllipticEst.Q0)
    (hUthS : ContDiffOn ℝ 2 (Function.uncurry (UthS a g τ)) Work.FTS.EllipticEst.Q0)
    (hVres : ContDiffOn ℝ 2 (Function.uncurry (Vres a Φs E g τ)) Work.FTS.EllipticEst.Q0)
    (hVthS : ContDiffOn ℝ 2 (Function.uncurry (VthS a g τ)) Work.FTS.EllipticEst.Q0)
    (hres : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i (Ures a Φs E g τ) z θ| ≤ Mv)
    (hresV : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i (Vres a Φs E g τ) z θ| ≤ Mv)
    (hth : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i (Uth a g τ) z θ| ≤ C)
    (hthV : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i (Vth a g τ) z θ| ≤ C) :
    Work.FTS.StreamBdryIface.SlotBd (pExp a)
      (slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ) (Mv + C) := by
  have hQ0 : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  have hopen : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hUeq := eqOn_Uprime_split (a := a) (Φs := Φs) (E := E) (g := g) (τ := τ) hSΨ3 hSΘ3
  have hVeq := eqOn_Vop_split (a := a) (Φs := Φs) (E := E) (g := g) (τ := τ) hSΨ1 hSΘ1
  have hUthEq := eqOn_UthS_Uth (a := a) (g := g) (τ := τ) hτ
  have hVthEq := eqOn_VthS_Vth (a := a) (g := g) (τ := τ) hτ
  intro z θ hzθ
  obtain ⟨hz, hθ, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  have hzI : (z, θ) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) := ⟨hz, trivial⟩
  have keyU : ∀ j i : ℕ, j + i ≤ 2 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < π / 2 →
      |Work.Spaces.mixed j i (Work.FTS.StreamBdryIface.Uprime (pExp a)
        (slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ)) z' θ'| ≤ Mv + C := by
    intro j i hji z' θ' hz' hθ' hθ2'
    have hzθ' : (z', θ') ∈ Work.FTS.EllipticEst.Q0 := ⟨hz', hθ', hθ2'⟩
    have h1 : Work.Spaces.mixed j i (Work.FTS.StreamBdryIface.Uprime (pExp a)
        (slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ)) z' θ'
        = Work.Spaces.mixed j i (Ures a Φs E g τ + UthS a g τ) z' θ' :=
      Work.FTS_RegExport.RXT.Sys.mixed_congr_of_isOpen hQ0 hUeq j i z' θ' hzθ'
    have h2 := mixed_add_of (f := Ures a Φs E g τ) (h := UthS a g τ) hUres hUthS hji hzθ'
    have h3 : Work.Spaces.mixed j i (UthS a g τ) z' θ' = Work.Spaces.mixed j i (Uth a g τ) z' θ' :=
      Work.FTS_RegExport.RXT.Sys.mixed_congr_of_isOpen hopen hUthEq j i z' θ' ⟨hz', trivial⟩
    rw [h1, h2, h3]
    have h4 := hres j i hji z' θ' hz' hθ' hθ2'
    have h5 := hth j i hji z' θ' hz' hθ' hθ2'
    calc |Work.Spaces.mixed j i (Ures a Φs E g τ) z' θ'
            + Work.Spaces.mixed j i (Uth a g τ) z' θ'|
        ≤ |Work.Spaces.mixed j i (Ures a Φs E g τ) z' θ'|
            + |Work.Spaces.mixed j i (Uth a g τ) z' θ'| := abs_add_le _ _
      _ ≤ Mv + C := add_le_add h4 h5
  have keyV : ∀ j i : ℕ, j + i ≤ 2 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < π / 2 →
      |Work.Spaces.mixed j i (Work.Construction.Vop
        (slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ)) z' θ'| ≤ Mv + C := by
    intro j i hji z' θ' hz' hθ' hθ2'
    have hzθ' : (z', θ') ∈ Work.FTS.EllipticEst.Q0 := ⟨hz', hθ', hθ2'⟩
    have h1 : Work.Spaces.mixed j i (Work.Construction.Vop
        (slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ)) z' θ'
        = Work.Spaces.mixed j i (Vres a Φs E g τ + VthS a g τ) z' θ' :=
      Work.FTS_RegExport.RXT.Sys.mixed_congr_of_isOpen hQ0 hVeq j i z' θ' hzθ'
    have h2 := mixed_add_of (f := Vres a Φs E g τ) (h := VthS a g τ) hVres hVthS hji hzθ'
    have h3 : Work.Spaces.mixed j i (VthS a g τ) z' θ' = Work.Spaces.mixed j i (Vth a g τ) z' θ' :=
      Work.FTS_RegExport.RXT.Sys.mixed_congr_of_isOpen hopen hVthEq j i z' θ' ⟨hz', trivial⟩
    rw [h1, h2, h3]
    have h4 := hresV j i hji z' θ' hz' hθ' hθ2'
    have h5 := hthV j i hji z' θ' hz' hθ' hθ2'
    calc |Work.Spaces.mixed j i (Vres a Φs E g τ) z' θ'
            + Work.Spaces.mixed j i (Vth a g τ) z' θ'|
        ≤ |Work.Spaces.mixed j i (Vres a Φs E g τ) z' θ'|
            + |Work.Spaces.mixed j i (Vth a g τ) z' θ'| := abs_add_le _ _
      _ ≤ Mv + C := add_le_add h4 h5
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    rw [← Work.Spaces.mixed_zero_right j]
    exact keyU j 0 (by omega) z θ hz hθ hθ2
  · exact keyU 0 1 (by norm_num) z θ hz hθ hθ2
  · intro j hj
    rw [← Work.Spaces.mixed_zero_right j]
    exact keyV j 0 (by omega) z θ hz hθ hθ2

/-! ## Congruence of the slots under equality on an open set -/

/-- `Uop` is congruent under equality of the stream functions on an open set. -/
theorem Uop_congr_of_eqOn {αG : ℝ} {f f' : Fn} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry f') V) :
    Set.EqOn (Function.uncurry (Work.Construction.Uop αG f))
      (Function.uncurry (Work.Construction.Uop αG f')) V := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hs : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V := by
    have hsec : IsOpen {z' : ℝ | (z', θ) ∈ V} :=
      hV.preimage (continuous_id.prodMk continuous_const)
    exact hsec.mem_nhds hp
  have hf : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => f' z' θ) := by
    filter_upwards [hs] with z' hz'
    exact h hz'
  have hval : f z θ = f' z θ := h hp
  simp only [Function.uncurry, Work.Construction.Uop, Work.Spaces.pz, hf.deriv_eq, hval]

/-- `Vop` is congruent under equality of the stream functions on an open set. -/
theorem Vop_congr_of_eqOn {f f' : Fn} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry f') V) :
    Set.EqOn (Function.uncurry (Work.Construction.Vop f))
      (Function.uncurry (Work.Construction.Vop f')) V := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hs : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ V := by
    have hsec : IsOpen {θ' : ℝ | (z, θ') ∈ V} :=
      hV.preimage (continuous_const.prodMk continuous_id)
    exact hsec.mem_nhds hp
  have hf : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => f' z θ') := by
    filter_upwards [hs] with θ' hθ'
    exact h hθ'
  have hval : f z θ = f' z θ := h hp
  simp only [Function.uncurry, Work.Construction.Vop, Work.Spaces.pth, hf.deriv_eq, hval]

/-- `Uprime` is congruent under equality of the stream functions on an open set. -/
theorem Uprime_congr_of_eqOn {αG : ℝ} {f f' : Fn} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry f') V) :
    Set.EqOn (Function.uncurry (Work.FTS.StreamBdryIface.Uprime αG f))
      (Function.uncurry (Work.FTS.StreamBdryIface.Uprime αG f')) V := by
  have hU := Uop_congr_of_eqOn (αG := αG) hV h
  intro p hp
  have h1 := hU hp
  simp only [Function.uncurry, Work.FTS.StreamBdryIface.Uprime] at h1 ⊢
  rw [h1]

/-- `SlotBd` is invariant under equality of the stream functions on the open quadrant. -/
theorem SlotBd_of_eqOn {αG M : ℝ} {f f' : Fn}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry f') Work.Construction.Qd)
    (hbd : Work.FTS.StreamBdryIface.SlotBd αG f M) :
    Work.FTS.StreamBdryIface.SlotBd αG f' M := by
  have hV : IsOpen (Work.Construction.Qd) := Work.FTS.EllipticEst.isOpen_Q0
  have hU := Uprime_congr_of_eqOn (αG := αG) hV h
  have hW := Vop_congr_of_eqOn hV h
  intro z θ hzθ
  obtain ⟨h1, h2, h3⟩ := hbd z θ hzθ
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    rw [← Work.Spaces.mixed_zero_right j]
    rw [← Work.FTS_RegExport.RXT.Sys.mixed_congr_of_isOpen hV hU j 0 z θ hzθ]
    exact h1 j hj
  · rw [← Work.FTS_RegExport.RXT.Sys.mixed_congr_of_isOpen hV hU 0 1 z θ hzθ]
    exact h2
  · intro j hj
    rw [← Work.Spaces.mixed_zero_right j]
    rw [← Work.FTS_RegExport.RXT.Sys.mixed_congr_of_isOpen hV hW j 0 z θ hzθ]
    exact h3 j hj

/-! ## The `slice_inputs` assembly, with the three delegated pieces as hypotheses -/

/-- `Work.FTS_StreamBdry.Inputs.slice_inputs`, assembled from

* the `SrcOK` leaf (delegated as `srcOK_Ftau`),
* the residual slot jets (delegated as `residual_slot_jetsB`),
* the singular-part slot jets (delegated as `theta_part_jets`),

and `psiCan_C3_proved` for the `C³` clause. -/
theorem slice_inputs_of_pieces {a C₀ Ce Cs : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp a) u →
      Work.FTS.VocabO.EllPkgGo (pExp a) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (pExp a) 6 Ce u (E u))
    (hEL : Work.FTS.FinalV2.EllLimOK3 (pExp a) E)
    (hStar : Work.FTS.VocabO2.StarPkgo2 (pExp a) Cs Φs)
    {g G : Fam} {A B : ℝ → ℝ}
    (hSol : Work.FTS.FinalV2.Sol (pExp a) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (pExp a) C₀ Φs E g)
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ)
    (hSrc : ∀ τ, 0 ≤ τ → ∃ L Mf : ℝ, Work.FTS.StreamBdryIface.SrcOK
      (Work.Construction.Ftau (pExp a) g τ) L Mf)
    (hRes : ∀ τ, 0 ≤ τ → ∃ M : ℝ,
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.v2_SlotU a
          (Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ)) z θ| ≤ M) ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (Work.Construction.Vop
          (Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ)) z θ| ≤ M))
    (hΘ : ∀ τ, 0 ≤ τ → ∃ C : ℝ, 0 < C ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (Uth a g τ) z θ| ≤ C) ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (Vth a g τ) z θ| ≤ C)) :
    ∀ τ, 0 ≤ τ → ∃ M L Mf : ℝ,
      ContDiffOn ℝ 3 (Function.uncurry (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ))
        Work.Construction.Qd ∧
      Work.FTS.StreamBdryIface.SlotBd (pExp a) (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) M ∧
      Work.FTS.StreamBdryIface.SrcOK (Work.Construction.Ftau (pExp a) g τ) L Mf := by
  have hpE : (0 : ℝ) < pExp a := Work.FTS.Regularity.pExp_pos ha
  intro τ hτ
  obtain ⟨hsm1, hsm2, hsm3, hsm4, hsm5, hsm6, hsm7, hsm8, hsm9, hsm10, hsm11, hsmPsi3,
    hsmTheta3⟩ :=
    Work.FTS_RegExport.RXT.Sys.coeff_pieces_contDiffOn (α := a) (C₀ := C₀) (Cs := Cs)
      ha ha13 hEL hStar hOK hτ
  obtain ⟨Mv, hMvU, hMvV⟩ := hRes τ hτ
  obtain ⟨C, -, hC_Uth, hC_Vth⟩ := hΘ τ hτ
  -- smoothness of the four slot functions
  have hUres : ContDiffOn ℝ 2 (Function.uncurry (Ures a Φs E g τ))
      Work.FTS.EllipticEst.Q0 := by
    refine (ContDiffOn.const_smul (1 / 2 : ℝ) hsm10).congr ?_
    intro p _
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry, Ures, Work.FTS_RegExport.RXT.v2_SlotU]
    ring
  have hUthS : ContDiffOn ℝ 2 (Function.uncurry (UthS a g τ))
      Work.FTS.EllipticEst.Q0 := by
    refine (ContDiffOn.const_smul (1 / 2 : ℝ) hsm11).congr ?_
    intro p _
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry, UthS]
    ring
  have hVres : ContDiffOn ℝ 2 (Function.uncurry (Vres a Φs E g τ))
      Work.FTS.EllipticEst.Q0 := by
    refine (ContDiffOn.const_smul (1 / (2 * pExp a)) hsm2).congr ?_
    intro p _
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry, Vres, Work.FTS_RegExport.RXT.v2_SlotV]
    have hne : (2 * pExp a) ≠ 0 := ne_of_gt (by positivity)
    rw [smul_eq_mul, one_div, inv_mul_cancel_left₀ hne]
  have hVthS : ContDiffOn ℝ 2 (Function.uncurry (VthS a g τ))
      Work.FTS.EllipticEst.Q0 := by
    refine (ContDiffOn.const_smul (1 / (2 * pExp a)) hsm3).congr ?_
    intro p hp
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry, VthS]
    rw [Vop_Theta_closed (αG := pExp a) (F := Work.Construction.Ftau (pExp a)
      (Work.FTS.RegExportIface.RXT.GR a g) τ) hp.2.1 hp.2.2]
    ring
  have hslotR := slotBd_of_pieces (a := a) (Mv := Mv) (C := C) hτ
    (hsmPsi3.of_le (by norm_num)) (hsmTheta3.of_le (by norm_num)) hsmPsi3 hsmTheta3
    hUres hUthS hVres hVthS
    (fun j i hji z θ hz hθ hθ2 => hMvU j i hji z θ hz hθ hθ2)
    (fun j i hji z θ hz hθ hθ2 => hMvV j i hji z θ hz hθ hθ2) hC_Uth hC_Vth
  have hslot : Work.FTS.StreamBdryIface.SlotBd (pExp a)
      (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) (Mv + C) :=
    SlotBd_of_eqOn (αG := pExp a) (M := Mv + C)
      (f := slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ)
      (f' := slice (Work.FTS.Nonlin.PsiCan Φs E g) τ)
      (fun p hp => by
        obtain ⟨z, θ⟩ := p
        exact (slice_PsiCan_eq_slice_PhiR (a := a) (Φs := Φs) (E := E) (g := g) hτ hp).symm)
      hslotR
  have hC3 : ContDiffOn ℝ 3 (Function.uncurry (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ))
      Work.Construction.Qd := by
    have h := Work.FTS_FinalLeaves.psiCan_C3_proved (α := pExp a) hEL hStar hOK τ hτ
    have hfun : Function.uncurry (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ)
        = fun q : ℝ × ℝ => Work.FTS.Nonlin.PsiCan Φs E g q.1 q.2 τ := by
      funext q
      obtain ⟨z, θ⟩ := q
      simp only [Function.uncurry, Work.FTS.Galerkin.slice_apply]
    rw [hfun]
    exact h
  obtain ⟨L, Mf, hSrc'⟩ := hSrc τ hτ
  exact ⟨Mv + C, L, Mf, hC3, hslot, hSrc'⟩

end Work.FTS_StreamBdry.Inputs
end
end
