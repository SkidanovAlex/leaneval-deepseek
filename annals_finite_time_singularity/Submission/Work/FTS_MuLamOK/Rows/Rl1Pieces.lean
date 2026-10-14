import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gLocal
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum
import Submission.Work.FTS_MuLamOK.Rows.SgRowsEnv
import Submission.Work.FTS_MuLipC.RowN.PvAesmOpen
import Submission.Work.FTS_RegExport.RX0.sup2_extG_ext_hIS
import Submission.Work.FTS_RegExport.RXR5L.L12fAux.C1Jet_L12f_of_support
import Submission.Work.FTS_RegExport.RXT.st1_fb_theta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLamOK.Rows

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The `Fa`-table of the twenty pieces of `N`, in the honest class, against `Env`.** -/
theorem piecesEnv (Ce Cs : ℝ) : ∃ K : ℝ, 0 < K ∧
    ∀ {α : ℝ} {f Φs Ξg : Fn},
      0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.VocabO.StarPkgo α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce f Ξg →
      ∀ k : Fin 20,
        Fa (Work.FTS.Nonlinear.Pieces.rl1Tools.pv α f Φs Ξg k)
          ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) := by
  obtain ⟨CA, hCApos, hangCA⟩ := Work.FTS.NonlinRows.Rl1.angSup_le
  obtain ⟨Kgg, hKggpos, hgg⟩ := GgRowsEnv Ce
  obtain ⟨Ksg, hKsgpos, hsg⟩ := SgRowsEnv Cs
  obtain ⟨Kss, hKsspos, hss⟩ := SsRowsEnv Cs
  obtain ⟨Kfk1, hKfk1pos, hfk1⟩ := Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.gg_fk_open_rows
  obtain ⟨Kfk2, hKfk2pos, hfk2⟩ := Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.sg_fk_open_rows
  obtain ⟨Kgs45, hKgs45pos, hgs45⟩ := Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.gs_open_rows
  set cgs : ℝ := 2000 * Real.sqrt (10 * CA) * max Ce 0 with hcgs
  have hcgs0 : 0 ≤ cgs := by rw [hcgs]; positivity
  set Kc : ℝ := Kgg + Ksg + Kss + Kfk1 + Kfk2 + Kgs45 + cgs + 1 with hKc
  have hKc0 : 0 ≤ Kc := by rw [hKc]; linarith
  have hKcpos : 0 < Kc := by rw [hKc]; linarith
  refine ⟨Kc, hKcpos, ?_⟩
  intro α f Φs Ξg hα hα1 hso hmem hs hell
  have hEnv0 : 0 ≤ Work.FTS.NonlinRows.Rl1.Env α f :=
    Work.FTS.NonlinRows.Rl1.Env_nonneg f hα.le
  have hggL : Kgg ≤ Kc := by rw [hKc]; linarith
  have hsgL : Ksg ≤ Kc := by rw [hKc]; linarith
  have hssL : Kss ≤ Kc := by rw [hKc]; linarith
  have hfk1L : Kfk1 ≤ Kc := by rw [hKc]; linarith
  have hfk2L : Kfk2 ≤ Kc := by rw [hKc]; linarith
  have hgs45L : Kgs45 ≤ Kc := by rw [hKc]; linarith
  have hcgsL : cgs ≤ Kc := by rw [hKc]; linarith
  have hang : ∀ (A : Fn), Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 4 A →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (A z θ) ^ 2 ≤ CA / (Work.Spaces.gam α - 1)
        * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A z θ' :=
    fun A => hangCA α A hα hα1
  -- the two conversions to the common constant
  have conv : ∀ {N : Fn} {c : ℝ}, Fa N ≤ ENNReal.ofReal (c * Work.FTS.NonlinRows.Rl1.Env α f) →
      c ≤ Kc → Fa N ≤ ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α f) := by
    intro N c h hc
    exact h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc hEnv0))
  have convgs : ∀ {N : Fn},
      Fa N ≤ ENNReal.ofReal (cgs * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α f) →
      Fa N ≤ ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α f) := by
    intro N h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hm : α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α f
        ≤ Work.FTS.NonlinRows.Rl1.Env α f := by
      rw [Work.FTS.NonlinRows.Rl1.Env, ← Real.sqrt_eq_rpow α]
      have h1 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
      have h2 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α f) ^ 2 :=
        mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
      linarith
    calc cgs * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α f
        = cgs * (α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α f) := by ring
      _ ≤ cgs * Work.FTS.NonlinRows.Rl1.Env α f := mul_le_mul_of_nonneg_left hm hcgs0
      _ ≤ Kc * Work.FTS.NonlinRows.Rl1.Env α f := mul_le_mul_of_nonneg_right hcgsL hEnv0
  -- the `gs`-rows 1, 2, 3 (tight form, `α^{1/2}·|f|_{ℋ⁴}`)
  have hgs1 : Fa (Work.FTS.Nonlin.N1gs α f Ξg)
      ≤ ENNReal.ofReal (cgs * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α f) := by
    rw [hcgs]
    exact Work.FTS.NonlinRows.Rl1.row1gs (CA := CA) hCApos hang hα hα1 hell
  have hgs2 : Fa (Work.FTS.Nonlin.N2gs α f Ξg)
      ≤ ENNReal.ofReal (cgs * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α f) := by
    rw [hcgs]
    exact Work.FTS.NonlinRows.Rl1.gsRow2 (CA := CA) hCApos hang hα hα1 hell
  have hgs3 : Fa (Work.FTS.Nonlin.N3gs α f Ξg)
      ≤ ENNReal.ofReal (cgs * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α f) := by
    rw [hcgs]
    exact Work.FTS.NonlinRows.Rl1.gsRow3 (CA := CA) hCApos hang hα hα1 hell
  obtain ⟨hg1, hg2, hg3⟩ := hgg hα hα1 hso hmem hell
  obtain ⟨hs1, hs2, hs3⟩ := hsg hα hα1 hso hmem hs
  obtain ⟨ht1, ht2, ht3, ht4, ht5⟩ := hss hα hα1 hs
  obtain ⟨hf1, hf2⟩ := hfk1 hα hα1 hso hmem
  obtain ⟨hk1, hk2⟩ := hfk2 hα hα1 hso hmem
  obtain ⟨hm1, hm2⟩ := hgs45 hα hα1 hso hmem
  intro k
  fin_cases k <;>
    simp only [Work.FTS.Nonlinear.Pieces.rl1Tools.pv, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_succ]
  · exact conv hg1 hggL
  · exact convgs hgs1
  · exact conv hs1 hsgL
  · exact conv ht1 hssL
  · exact conv hg2 hggL
  · exact convgs hgs2
  · exact conv hs2 hsgL
  · exact conv ht2 hssL
  · exact conv hg3 hggL
  · exact convgs hgs3
  · exact conv hs3 hsgL
  · exact conv ht3 hssL
  · exact conv hf1 hfk1L
  · exact conv hm1 hgs45L
  · exact conv hk1 hfk2L
  · exact conv ht4 hssL
  · exact conv hf2 hfk1L
  · exact conv hm2 hgs45L
  · exact conv hk2 hfk2L
  · exact conv ht5 hssL

end Work.FTS_MuLamOK.Rows
