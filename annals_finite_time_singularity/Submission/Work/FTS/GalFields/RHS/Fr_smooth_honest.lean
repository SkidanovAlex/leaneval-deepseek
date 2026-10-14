import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.Cores.aSlotsTwoInterp
import Submission.Work.FTS.EllipticEst.Cores.aSlotsTwoT1
import Submission.Work.FTS.EllipticEst.Final.Rep.TopSlotTwoFts.AHalfFinal
import Submission.Work.FTS.EllipticEst.Final.Rep.TopSlotTwoFts.BHalf
import Submission.Work.FTS.EllipticEst.H2W.lzeroSliceL1Ae
import Submission.Work.FTS.EllipticEst.TT.slot11_le
import Submission.Work.FTS.EllipticEst.TT.truncAux
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.Nonlinear.Open.Main
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.StrongEps.EpsE4Thr.EnergyDiagAssembly
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.VocabO2
import Submission.Work.Spaces.mixed_mul_le
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.TSCAssembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The `A`-profile `z²∂_z²Ψ`. -/
private abbrev Ab (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

/-- The `B`-profile `∂_θ²Ψ`. -/
private abbrev Bb (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ

/-- `Tk α k f` is `L2Sq` of the `k`-th weighted angular slot (definitional). -/
private theorem Tk_eq_L2Sq (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.remov.Step.Tk α k f
      = Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 k f z θ
          * Work.Spaces.Wt α z θ) := rfl

/-- The level-`0` `ℋ`-square is the weighted `L²`-square. -/
private theorem HkSq_zero_eq_L2Sq_aux (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g = Work.Spaces.L2Sq (fun z θ => g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) :=
  Work.FTS.EllipticEst.TT.HkSq_zero_eq_L2Sq α g

/-- **The `(1,1)`-slot of a `D_z`-shifted profile in the `Tk`-form** (a self-contained copy of
`Cores.Tk_one_Dz_eq_mixed11'`): `Tk α 1 (D_z Y) = L2Sq (mixed 1 1 Y · Wt α)`. -/
private theorem Tk_one_Dz_eq_mixed11_aux (α : ℝ) (hα : 0 < α) {Y : ℝ → ℝ → ℝ}
    (hY : Work.FTS.EllipticEst.SmoothOpen Y) :
    Work.FTS.EllipticEst.remov.Step.Tk α 1 (Work.Spaces.DzIter 1 Y)
      = Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 1 1 Y z θ
          * Work.Spaces.Wt α z θ) := by
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed 0 1 (Work.Spaces.DzIter 1 Y) z θ
        = Work.Spaces.mixed 1 1 Y z θ := by
    intro z θ hz hθ hlt
    have hpq : ((z, θ) : ℝ × ℝ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hlt⟩
    have hcm := Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0
      (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall Y).mp hY n) 1 1 hpq
    rw [Work.Spaces.mixed_zero_left]
    exact hcm
  rw [Tk_eq_L2Sq]
  exact l2sq_congr_q hα hpt

/-- **The sum of the three shifted level-`0` `B`-slots is dominated by `|F|²_{ℋ²}`** (the
paper's Step 3 at the `j ≤ 2` radially shifted data, `Cores.shiftZeroSlots_clean`). -/
theorem sigma_le (h0 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C) :
    ∃ CS : ℝ, 0 < CS ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
        ≤ CS * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C0, hC0, hz0⟩ := shiftZeroSlots_clean 2 0 (by norm_num)
  obtain ⟨C1, hC1, hz1⟩ := shiftZeroSlots_clean 2 1 (by norm_num)
  obtain ⟨C2, hC2, hz2⟩ := shiftZeroSlots_clean 2 2 le_rfl
  refine ⟨C0 + C1 + C2 + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  have hN : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have e0 := hz0 α F Ψ hα hα4 h h0
  have e1 := hz1 α F Ψ hα hα4 h h0
  have e2 := hz2 α F Ψ hα hα4 h h0
  have n0 : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 0 Ψ) z θ) :=
    mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg _ _ _)
  have n1 : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :=
    mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg _ _ _)
  have n2 : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) :=
    mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg _ _ _)
  have b0 : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 0 Ψ))
      ≤ C0 * Work.Spaces.HkSq α 2 F := by linarith
  have b1 : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
      ≤ C1 * Work.Spaces.HkSq α 2 F := by linarith
  have b2 : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
      ≤ C2 * Work.Spaces.HkSq α 2 F := by linarith
  have hsum : (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
      = Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 0 Ψ))
        + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ)) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    rw [← HkSq_zero_eq_L2Sq_aux α (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 0 Ψ)),
      ← HkSq_zero_eq_L2Sq_aux α (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)),
      ← HkSq_zero_eq_L2Sq_aux α (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))]
  rw [hsum]
  nlinarith [b0, b1, b2, hN, hC0, hC1, hC2]

/-- **The assembly.**  Given the `(1,1)`-slot bound of `A` and the level-`0` estimate, the six
`Tk`-slots of the target are bounded by `C|F|²_{ℋ²}`. -/
theorem TopSlotsTwoClean_of
    (hA11 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
          (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        ≤ C * Work.Spaces.HkSq α 2 F)
    (h0 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      (α ^ 4 * (Work.FTS.EllipticEst.remov.Step.Tk α 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + 3 * Work.FTS.EllipticEst.remov.Step.Tk α 1
            (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
          + Work.FTS.EllipticEst.remov.Step.Tk α 2
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)))
        + (Work.FTS.EllipticEst.remov.Step.Tk α 1 (Work.Spaces.pthIter 2 Ψ)
          + 3 * Work.FTS.EllipticEst.remov.Step.Tk α 1
            (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ))
          + Work.FTS.EllipticEst.remov.Step.Tk α 2 (Work.Spaces.pthIter 2 Ψ))
        ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C1, hC1, h1⟩ := aSlotsTwoT1 h0
  obtain ⟨C3, hC3, h3⟩ := Work.FTS.EllipticEst.TopSlotTwoFts.Tk_A_le h0
  obtain ⟨KA, hKA, hA⟩ := Work.FTS.EllipticEst.H2W.AngBW.slot01Bound
  obtain ⟨KB, hKB, hB⟩ := Work.FTS.EllipticEst.TT.slot11_le
  obtain ⟨KC, hKC, hC⟩ := Work.FTS.EllipticEst.TopSlotTwoFts.Tk_B_le h0
  obtain ⟨CS, hCS, hS⟩ := sigma_le h0
  obtain ⟨C2, hC2, h2⟩ := hA11
  refine ⟨C1 + 3 * C2 + C3 + KA * (CS + 1) + 3 * (KB * (CS + 1 + C2)) + KC + 1,
    by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  have hN : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have hα1 : α ≤ 1 := by linarith
  have hα4le : α ^ 4 ≤ 1 := pow_le_one₀ hα.le hα1
  have hAb : Work.FTS.EllipticEst.SmoothOpen (Ab Ψ) :=
    Work.FTS.EllipticEst.AeMom.Repair.SmoothOpen.zsq_mul
      (Work.FTS.EllipticEst.SmoothOpen.pzIter (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth) 2)
  have hBsm : Work.FTS.EllipticEst.SmoothOpen (Bb Ψ) :=
    (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth).pth.pth
  -- the three direct `A`-slots
  have s1 : α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1 (Ab Ψ)
      ≤ C1 * Work.Spaces.HkSq α 2 F := h1 α F Ψ hα hα4 h
  have s2 : α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
      (Work.Spaces.DzIter 1 (Ab Ψ)) ≤ C2 * Work.Spaces.HkSq α 2 F := h2 α F Ψ hα hα4 h
  have s3 : α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 2 (Ab Ψ)
      ≤ C3 * Work.Spaces.HkSq α 2 F := by
    have hTk : Work.FTS.EllipticEst.remov.Step.Tk α 2 (Ab Ψ)
        ≤ C3 * Work.Spaces.HkSq α 2 F := h3 α F Ψ hα hα4 h
    have hnn : 0 ≤ Work.FTS.EllipticEst.remov.Step.Tk α 2 (Ab Ψ) :=
      Work.FTS.EllipticEst.remov.Step.Tk_nonneg α 2 _
    calc α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 2 (Ab Ψ)
        ≤ 1 * Work.FTS.EllipticEst.remov.Step.Tk α 2 (Ab Ψ) :=
          mul_le_mul_of_nonneg_right hα4le hnn
      _ = Work.FTS.EllipticEst.remov.Step.Tk α 2 (Ab Ψ) := one_mul _
      _ ≤ C3 * Work.Spaces.HkSq α 2 F := hTk
  -- the shifted `ℋ⁰`-slots
  have hSig := hS α F Ψ hα hα4 h
  -- the three `B`-slots
  have hB1 : Work.FTS.EllipticEst.remov.Step.Tk α 1 (Bb Ψ)
      ≤ KA * ((∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
            Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
          + Work.Spaces.HkSq α 2 F) := by
    rw [Tk_eq_L2Sq]
    exact hA α F Ψ hα hα4 h
  have hB2 : Work.FTS.EllipticEst.remov.Step.Tk α 1 (Work.Spaces.DzIter 1 (Bb Ψ))
      ≤ KB * ((∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
            Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
          + Work.Spaces.HkSq α 2 F
          + α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
              Work.Spaces.mixed 1 1 (Ab Ψ) z θ * Work.Spaces.Wt α z θ)) := by
    rw [Tk_one_Dz_eq_mixed11_aux α hα hBsm]
    exact hB α F Ψ hα hα4 h
  have hB3 : Work.FTS.EllipticEst.remov.Step.Tk α 2 (Bb Ψ)
      ≤ KC * Work.Spaces.HkSq α 2 F := hC α F Ψ hα hα4 h
  -- the `(1,1)`-slot of `A` in the `mixed`-form
  have s2' : α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
      Work.Spaces.mixed 1 1 (Ab Ψ) z θ * Work.Spaces.Wt α z θ)
      ≤ C2 * Work.Spaces.HkSq α 2 F := by
    rw [← Tk_one_Dz_eq_mixed11_aux α hα hAb]
    exact s2
  have hshape : α ^ 4 * (Work.FTS.EllipticEst.remov.Step.Tk α 1 (Ab Ψ)
        + 3 * Work.FTS.EllipticEst.remov.Step.Tk α 1 (Work.Spaces.DzIter 1 (Ab Ψ))
        + Work.FTS.EllipticEst.remov.Step.Tk α 2 (Ab Ψ))
      = α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1 (Ab Ψ)
        + 3 * (α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
            (Work.Spaces.DzIter 1 (Ab Ψ)))
        + α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 2 (Ab Ψ) := by ring
  rw [hshape]
  have hA' : (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
      ≤ CS * Work.Spaces.HkSq α 2 F := hSig
  have hB1' : Work.FTS.EllipticEst.remov.Step.Tk α 1 (Bb Ψ)
      ≤ KA * (CS + 1) * Work.Spaces.HkSq α 2 F := by
    have hKA0 : 0 ≤ KA := le_of_lt hKA
    have : KA * ((∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
        + Work.Spaces.HkSq α 2 F) ≤ KA * (CS + 1) * Work.Spaces.HkSq α 2 F := by
      nlinarith [hA', hN]
    linarith [hB1]
  have hB2' : Work.FTS.EllipticEst.remov.Step.Tk α 1 (Work.Spaces.DzIter 1 (Bb Ψ))
      ≤ KB * (CS + 1 + C2) * Work.Spaces.HkSq α 2 F := by
    have hKB0 : 0 ≤ KB := le_of_lt hKB
    have : KB * ((∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
        + Work.Spaces.HkSq α 2 F
        + α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
            Work.Spaces.mixed 1 1 (Ab Ψ) z θ * Work.Spaces.Wt α z θ))
        ≤ KB * (CS + 1 + C2) * Work.Spaces.HkSq α 2 F := by
      nlinarith [hA', hN, s2']
    linarith [hB2]
  nlinarith [s1, s2, s3, hB1', hB2', hB3, hN]

end

end Work.FTS.EllipticEst.Cores
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.Fr_smooth_honest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `RHS/Fr_smooth_honest` — the open-quadrant smoothness and the `ℋ⁴`-honesty of the
dynamic right-hand side `Fr`

`Fr α Φs EllSol g = -𝓛_Γ^T(g) + gRHS(μ,λ,F_*+g, Φ_*+Φ_g, g)` is a finite sum of

* `-𝓛_Γ^T g`,
* `-μ̄·AK α` (a constant times `AK`),
* `N₀ α (F_*+g) g`,
* `N α (F_*+g) (Φ_*+Φ_g)`,
* `N_* μ (lamfun μ) g = -μ·g - (μ+lamfun μ+μ·lamfun μ)·D_z g`,

and every one of these is produced, in this workspace, by

* `smoothOpen_atoms_of_gal` — `C^∞` on the open quadrant `Q₀` of all twelve atoms under
  `GalClass α g` (the honesty of `g`), `StarPkgo2 α Cs Φs`, `EllPkgGo α Ce g Φg`;
* `Norm.Xn_LGammaT_le` — `HkMem α 4 (𝓛_Γ^T g)`;
* `Nonlinear.Open.PiecesHkOpen` — `HkMem α 4` of `AK`, of the blocks `N₀`, `N` and of
  `D_z g` (the `ℋ⁴`-honesty table of the §8 chunks).

The `N_*`-block is the only one not delivered as a package; it is a linear combination of
`g` and `D_z g`, so `LocData.HkMem_const_mul` + `Assembly.HkMem_add_open` +
`HkMem_congr_Q0` give its `ℋ⁴`-honesty from `HkMem α 4 g` and `HkMem α 4 (D_z g)` — no
hypothesis on `μ` (in particular `μ ≠ -1`) is needed, since the statement is only about
*smoothness* and *integrability*, never about a bound in terms of `Xn5`.

The last two conjuncts (the difference with `Fr α Φs EllSol 0`) are the closure of
`SmoothOpen` and of `HkMem α 4` under subtraction, applied to the two instances `g` and `0`
of the first three conjuncts (`GalClass α 0` is `EllSol.galClass_zero`).
-/

namespace Work.FTS.GalFields.RHS

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000




end Work.FTS.GalFields.RHS
end
