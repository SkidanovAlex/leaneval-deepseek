import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.ClassC.pth_Vop_EllResid_classC
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.StrongEps.EpsHbdd
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.StatResidual
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
import Submission.Work.FTS.StrongEps.JfamP_norm
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.zeroTermDth
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgMid
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXVP.NoHdat.velPkgEasy_noHdat
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
-- ===== merged: Submission.Work.FTS.ClassC.VopAux.vopTraces_classC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.VopAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Two elementary transfer lemmas: continuity on the closed interval gives the two
endpoint limits -/

/-- **Left endpoint.**  A function continuous on the closed interval `[0, π/2]` and vanishing at
`0` tends to `0` as `θ → 0⁺`. -/
theorem tendsto_zero_nhdsGT_of_continuousOn_Icc {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 (Real.pi / 2))) (h0 : f 0 = 0) :
    Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have h1 : ContinuousWithinAt f (Set.Icc 0 (Real.pi / 2)) 0 :=
    hf.continuousWithinAt (Set.left_mem_Icc.mpr (by positivity))
  have h2 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Icc 0 (Real.pi / 2)))
      (nhds (f 0)) := h1
  rw [h0] at h2
  rw [nhdsWithin_Icc_eq_nhdsGE (by positivity : (0 : ℝ) < Real.pi / 2)] at h2
  exact h2.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)

/-- **Right endpoint.**  The analogue at `π/2`. -/
theorem tendsto_zero_nhdsLT_pi_half_of_continuousOn_Icc {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 (Real.pi / 2))) (hp : f (Real.pi / 2) = 0) :
    Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have h1 : ContinuousWithinAt f (Set.Icc 0 (Real.pi / 2)) (Real.pi / 2) :=
    hf.continuousWithinAt (Set.right_mem_Icc.mpr (by positivity))
  have h2 : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Icc 0 (Real.pi / 2)))
      (nhds (f (Real.pi / 2))) := h1
  rw [hp] at h2
  rw [nhdsWithin_Icc_eq_nhdsLE (by positivity : (0 : ℝ) < Real.pi / 2)] at h2
  exact h2.mono_left (nhdsWithin_mono _ Set.Iio_subset_Iic_self)

/-- A constant times `sin 2θ` tends to `0` at the two endpoints of `(0, π/2)`. -/
theorem tendsto_zero_const_mul_sin_two (c : ℝ) :
    Filter.Tendsto (fun θ : ℝ => c * Real.sin (2 * θ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ : ℝ => c * Real.sin (2 * θ))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hcont : Continuous fun θ : ℝ => Real.sin (2 * θ) := by fun_prop
  have hleft : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := hcont.continuousAt (x := 0)
    have h' : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (nhds (0 : ℝ))
        (nhds (Real.sin (2 * 0))) := h
    rw [show Real.sin (2 * 0) = 0 by norm_num] at h'
    exact h'.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hright : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hsin : Real.sin (2 * (Real.pi / 2)) = 0 := by
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    have h := hcont.continuousAt (x := Real.pi / 2)
    have h' : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (nhds (Real.pi / 2))
        (nhds (Real.sin (2 * (Real.pi / 2)))) := h
    rw [hsin] at h'
    exact h'.mono_left (nhdsWithin_le_nhds (s := Set.Iio (Real.pi / 2)))
  exact ⟨by simpa using hleft.const_mul c, by simpa using hright.const_mul c⟩

/-! ## Additivity of the iterated radial operator on the open quadrant -/

/-- `D_z^j (f + g) = D_z^j f + D_z^j g` at every point of the open quadrant, for `f, g` of class
`C^∞` there. -/
theorem DzIter_add_on_Q0 (j : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter j (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.DzIter j f z θ + Work.Spaces.DzIter j g z θ := by
  induction j with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => f z θ + g z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter n f z' θ + Work.Spaces.DzIter n g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n f z' θ) z :=
        ((hf.DzIter n).hasDerivAt_slice hθ hz).differentiableAt
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n g z' θ) z :=
        ((hg.DzIter n).hasDerivAt_slice hθ hz).differentiableAt
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq]
      rw [show (fun z' => Work.Spaces.DzIter n f z' θ + Work.Spaces.DzIter n g z' θ)
          = (fun z' => Work.Spaces.DzIter n f z' θ)
            + (fun z' => Work.Spaces.DzIter n g z' θ) from rfl, deriv_add hd1 hd2]
      ring

/-! ## The `D_z`-shift of the weak class, iterated -/

/-- **The iterated radial shift of the weak class.**  From a datum of `EllWeakPos α k F Ψ` with
`k ≥ 1` one obtains, for every `j ≤ k-1`, a datum of the same class at level `k - j` for the
`j`-fold radial iterate `D_z^j`.  The single-step shift is
`Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le` (which needs level `≥ 2`); the composition
`D_z (D_z^j ·) = D_z^{j+1} ·` is `Work.Spaces.DzIter_add_right`. -/
theorem ellWeakPos_dzIter_shift_classC {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} {k : ℕ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ j, j ≤ k - 1 → Work.FTS.EllipticEst.TT.EllWeakPos α (k - j)
      (Work.Spaces.DzIter j F) (Work.Spaces.DzIter j Ψ) := by
  intro j
  induction j with
  | zero => intro _; simpa using h
  | succ n ih =>
      intro hn
      have hn' : n ≤ k - 1 := by omega
      have hk2 : 2 ≤ k - n := by omega
      have h1 := Work.FTS.EllipticEst.Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le
        (α := α) (k := k - n) hk2 (ih hn')
      have hlev : k - n - 1 = k - (n + 1) := by omega
      have hF : Work.Spaces.DzIter 1 (Work.Spaces.DzIter n F)
          = Work.Spaces.DzIter (n + 1) F := by
        rw [← Work.Spaces.DzIter_add_right 1 n F, Nat.add_comm 1 n]
      have hP : Work.Spaces.DzIter 1 (Work.Spaces.DzIter n Ψ)
          = Work.Spaces.DzIter (n + 1) Ψ := by
        rw [← Work.Spaces.DzIter_add_right 1 n Ψ, Nat.add_comm 1 n]
      rw [hF, hP, hlev] at h1
      exact h1

/-! ## The target -/


end Work.FTS.ClassC.VopAux
end
end
-- ===== merged: Submission.Work.FTS.ClassC.ellClassOk_exists_of_classC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology Interval BigOperators

namespace Work.FTS.ClassC

open MeasureTheory

/-! ## The `m = 0` coefficient of the source *is* the angular moment

`Series.eFam_zero_moment` proves `F_*F z = 0 → cmode 0 F z = 0`.  The converse is what a
*finite-mode* presentation of a source needs (it is how such a source produces the solvability
condition `F_*F ≡ 0` of `(PolarBSL)`), and it is unconditional: the Bochner integral is a total
function, so the chain only uses pointwise rewrites and the null-set comparison `Icc`/`Ioc`.
-/







end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5ExtractMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- **The `E5` extraction from the scheme's data.** -/
theorem E5Extract_of_mem_seq {α C₀ Ce Cs K' T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g₀ : Fn} {ε : ℕ → ℝ} {G : ℕ → Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ)
    (hc1 : 1 / 10 ≤ Work.Spaces.c α) (hc2 : Work.Spaces.c α ≤ 10)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : MuLamOK α C₀ Φs E)
    (hε : ∀ k : ℕ, ε k ∈ Set.Ioc 0 1) (hT : 0 < T)
    (hsol : ∀ k : ℕ, IsEpsSolP α ρ (ε k) T Φs E g₀ (G k))
    (hreg : ∀ k : ℕ, EpsRegP α ρ (ε k) T (G k))
    (hC : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.ClassC.ClassC α (slice (JfamP ρ (ε n) (G n)) s))
    (hb4 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.Nonlin.Xn α (slice (JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2)
    (hb6p : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (ε n) (G n)) s) ≤ Ce)
    (hsm : ∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (slice (G k) τ))
    (hmem6 : ∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 6 (slice (G k) τ))
    (hb6 : ∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice (G k) τ) ≤ K') :
    ∃ (φ : ℕ → ℕ) (F : ℝ → Fn), StrictMono φ ∧
      ∀ τ ∈ Set.Icc 0 T, ConvLocUnifH6 α K' (fun n => slice (G (φ n)) τ) (F τ) := by
  -- `hcont` from the joint `C¹` of the solutions
  have hcont : ∀ k : ℕ, ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => epsRHSP α ρ (ε k) Φs E (G k) s p.1 p.2) (Set.Icc 0 T) :=
    fun k => continuousOn_epsRHSP_of_regP hT (hsol k) (hreg k)
  -- `hbdd` from the value bound of `epsWP` on windows
  have hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ p ∈ K,
        |epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ C :=
    fun K hK hKQ => hbdd_of_mem_compact (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (T := T)
      (ρ := ρ) (Φs := Φs) (E := E) (G := G) (ε := ε) hα hρ hε hT.le hc1 hc2 hEll hstar hml
      hC hb4 hb6p hK hKQ
  exact E5Extract_of_hbdd (α := α) (B := K') (T := T) (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀)
    (ε := ε) (G := G) hα hρ hε hsol hsm hmem6 hb6 hcont hbdd

/-! ## The extraction from `EpsUniformMem` -/


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.IsEpsSolP_eq_of_epsClass =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **D1 — uniqueness of the ε-scheme at FIXED ε**. -/
theorem IsEpsSolP_eq_of_epsClass {α C₁ Ce Cs B T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g₀ : Fn} {g g' : Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hT : 0 < T)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : MuLamOK α C₁ Φs E) (hB : 0 ≤ B)
    (hsol : IsEpsSolP α ρ ε T Φs E g₀ g) (hsol' : IsEpsSolP α ρ ε T Φs E g₀ g')
    (hcl : ∀ τ ∈ Set.Icc 0 T, Work.FTS.EpsEngine.EpsClass α ρ ε C₁ B (slice g τ))
    (hcl' : ∀ τ ∈ Set.Icc 0 T, Work.FTS.EpsEngine.EpsClass α ρ ε C₁ B (slice g' τ))
    (hc1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T))
    (hc1' : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g' p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T)) :
    ∀ τ ∈ Set.Icc 0 T, ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → g z θ τ = g' z θ τ :=
  IsEpsSolP_eq_of_epsClass_proof hα hρ hε hε1 hT hEll hstar hml hB hsol hsol' hcl hcl' hc1 hc1'

end Work.FTS.StrongEps
end
end
