import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Transfer.HkMem_descent_Q0Sm
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.NonlinRows.NAux3
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0
import Submission.Work.FTS.StrongEps.EpsE4Thr.DiagCurveIRho
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPBdd
import Submission.Work.FTS.StrongEps.JfamP_norm
import Submission.Work.FTS.StrongEps.PZeroAux.bumpHkNormBound
import Submission.Work.FTS.StrongEps.PZeroAux.softClass_Pz
import Submission.Work.FTS.StrongEps.TenOfEight.GainAll
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAsm
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_LocDatum3a.Defs
import Submission.Work.FTS_RegExport.THL.cs7_rop_split
import Submission.Work.FTS_RegExport.THL.vopPert_theta_holder
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.EpsRHSPBdd_generalRadius =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn Fam slice famOf)

set_option maxHeartbeats 1600000

/-!
# `EpsRHSPBdd_generalRadius` — the `ℋ⁴`-bound of the projected right-hand side at an
*arbitrary* class-`C` radius

`EpsLocalPStar.EpsRHSPBdd` controls the projected right-hand side
`epsRHPSlice α ρ ε Φs E τ u` on the *specific* ball `Xn α (Pz (Jeps ρ ε u)) ≤ C₀ α²`, with the
modulation bounds supplied by `MuLamOK α C₀ Φs E` (whose constants `1/2`, `1` are hard-wired).

The present statement is the radius-agnostic form: the ball is `Xn α w ≤ B0` and the modulation
data is the bare hypothesis `hml` (constants `Mm`, `Ml`).  The proof is the proof of `EpsRHSPBdd`
with two modifications:

* the three block estimates `ClassCRHS.HkMemXn{LGammaT,N0,N}` — which are stated for a `C₀`-ball
  `Xn α w ≤ C₀ α²` — are instantiated at `C₀g := max (B0 / α²) 1`, so that `C₀g α² ≥ B0 ≥ Xn α w`
  (`HkMemXnLGammaT` does not use its smallness hypothesis at all; `HkMemXnN0`/`HkMemXnN` use it only
  through `Cx = max C₀ 1`, so a larger radius merely enlarges the existential constant);
* the `Nstar`-block `(-μ)w + (-(μ + λ + μλ))D_z w` is bounded by `Mm`, `Ml` as given, giving the
  constant `2 * (Mm * B0 + (Mm + Ml + Mm * Ml) * (A6 * B))` in place of
  `2 * ((1/2) * (C₀ α²) + 2 * (A6 * B))` (which is the `Mm = 1/2`, `Ml = 1` case).

Everything else — the splitting of the pre-mollified right-hand side into
`𝓛_Γ^T + (P₂+P₃) + P₄ + P₅`, the angular-boundary modification `X'`, the mollifier's `ℋ⁴`-gain
`X ↦ J_ε X'` and the projection `Pz` — is used verbatim.
-/

/-- **The projected scheme's right-hand side is `SmoothOpen`-regular and `ℋ⁶`-honest, with a
uniform `ℋ⁴`-size `R`, for class-`C` data of *arbitrary* radius `B0`.**

The constant `R` depends on the parameters `α, Ce, Cs, B, B0, Mm, Ml, ρ, Φs, E, ε` but not on the
datum `u` or the fake time `τ`.  `hml` is the modulation input at radius `B0`; it replaces the
`MuLamOK α C₀ Φs E` hypothesis of `EpsLocalPStar.EpsRHSPBdd` (whose constants are the
`Mm = 1/2`, `Ml = 1`, `B0 = C₀ α²` instance). -/
theorem EpsRHSPBdd_generalRadius {α Ce Cs B B0 Mm Ml : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hB : 0 ≤ B) (hB0 : 0 ≤ B0)
    (hml : ∀ w : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α w →
      Work.FTS.Nonlin.Xn α w ≤ B0 →
      ‖Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => w z θ))
          (fun z θ _ => w z θ) 0‖ ≤ Mm ∧
      ‖Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => w z θ))
          (fun z θ _ => w z θ) 0‖ ≤ Ml) :
    ∃ R : ℝ, 0 < R ∧ ∀ (τ : ℝ) (u : Work.FTS.Galerkin.Fn),
      Work.FTS.EllipticEst.SmoothOpen u → Work.Spaces.HkMem α 6 u →
      Work.Spaces.HkNorm α 6 u ≤ B →
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)) →
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)) ≤ B0 →
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E τ u) ∧
      Work.Spaces.HkMem α 6 (Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E τ u) ∧
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E τ u) ≤ R := by
  classical
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hε0 : 0 < ε := hε
  -- ## the generalised ball radius, written as a `C₀`-ball for the three block estimates
  set C₀g : ℝ := max (B0 / α ^ 2) 1 with hC₀gdef
  have hα2pos : 0 < α ^ 2 := pow_pos hα0 2
  have hB0le : B0 ≤ C₀g * α ^ 2 := by
    rw [hC₀gdef]
    have h1 : B0 / α ^ 2 ≤ max (B0 / α ^ 2) 1 := le_max_left _ _
    have h2 : (B0 / α ^ 2) * α ^ 2 = B0 := div_mul_cancel₀ B0 (ne_of_gt hα2pos)
    calc B0 = (B0 / α ^ 2) * α ^ 2 := h2.symm
      _ ≤ max (B0 / α ^ 2) 1 * α ^ 2 := mul_le_mul_of_nonneg_right h1 hα2pos.le
  -- ## the constants of the three block estimates, of the projected family, and of the mollifier
  obtain ⟨A6, hA6, hJfamP⟩ := HkNorm_JfamP_le (ρ := ρ) hρ
  have hAB0 : 0 ≤ A6 * B := mul_nonneg hA6 hB
  obtain ⟨K1, hK1, hLGT⟩ := ClassCRHS.HkMemXnLGammaT (α := α) hα (C₀ := C₀g) (B := A6 * B)
  obtain ⟨K2, hK2, hN0⟩ := ClassCRHS.HkMemXnN0 (α := α) hα (C₀ := C₀g) (B := A6 * B)
  obtain ⟨K3, hK3, hN⟩ := ClassCRHS.HkMemXnN (α := α) hα (C₀ := C₀g) (B := A6 * B) (Ce := Ce) (Cs := Cs)
    (Φs := Φs)
  obtain ⟨A, hApos, hAbnd⟩ := Work.FTS.StrongEps.PZeroAux.PzHkNormFour
  obtain ⟨CJ, hCJpos, hCJ⟩ := HkSq_Jeps_le ρ hρ.moll
  obtain ⟨KAK, hKAK, hra⟩ := Work.FTS.Nonlinear.Pieces.rak_bound
  have hAKmem : Work.Spaces.HkMem α 4 (Work.Construction.AK α) :=
    Work.FTS.NonlinRows.HkMem_AK α hα0 hα1
  have hAKbd : Work.FTS.Nonlin.Xn α (Work.Construction.AK α) ≤ KAK := hra hα0 hα1
  have hAKsmo : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.AK α) :=
    Work.FTS.StrongPersist.AK_smoothO α
  obtain ⟨CL, hCL, hl12z⟩ := Work.FTS.OpenPkg.l12zero_field
  have hCLnn : 0 ≤ CL := hCL.le
  have hgain := Work.FTS.StrongEps.EpsE4Thr.HkMem_Jeps_gain (ρ := ρ) hρ
  -- the crude constant of the estimate (valid for *every* datum `w`)
  set Lam : ℝ := max (2 * CL * (K2 + K3) * KAK) 0 with hLamdef
  set Nst : ℝ := max (2 * (Mm * B0 + (Mm + Ml + Mm * Ml) * (A6 * B))) 0 with hNstdef
  set KX : ℝ := 16 * (K1 + Lam + K2 + K3 + Nst) with hKXdef
  have hKXnn : 0 ≤ KX := by
    rw [hKXdef]
    have h1 : 0 ≤ K1 := hK1.le
    have hL0 : 0 ≤ Lam := le_max_right _ _
    have hN0' : 0 ≤ Nst := le_max_right _ _
    have h2 : 0 ≤ K2 := hK2.le
    have h3 : 0 ≤ K3 := hK3.le
    linarith
  refine ⟨max (A * Real.exp (CJ / 2) * KX) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  intro τ u huSmo huMem huBd hwC hw4
  set w : Fn := Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u) with hwdef
  -- ## the radius hypothesis in the shape required by the three block estimates
  have hw4' : Work.FTS.Nonlin.Xn α w ≤ C₀g * α ^ 2 := le_trans hw4 hB0le
  -- ## the data of `w`
  have hwSmo : Work.FTS.EllipticEst.SmoothOpen w := hwC.reg
  have hwMem6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hwC.reg 6 (by norm_num) hwC.mem
  have hwMem5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hwC.reg 5 (by norm_num) hwC.mem
  have hwMem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hwC.reg 4 (by norm_num) hwC.mem
  have hw6 : Work.Spaces.HkNorm α 6 w ≤ A6 * B := by
    have h := (hJfamP (g := famOf (fun _ : ℝ => u)) (s := τ) ⟨hα0, hα1⟩ ⟨hε, hε1⟩
      (fun n => huSmo.forall n) huMem).2
    have hslice : slice (famOf (fun _ : ℝ => u)) τ = u := rfl
    rw [hslice] at h
    exact le_trans h (mul_le_mul_of_nonneg_left huBd hA6)
  have hw5 : Work.Spaces.HkNorm α 5 w ≤ A6 * B :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := 5) (by norm_num) hwMem6)
      hw6
  have hDzmem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz w) :=
    (Work.FTS.CoercivityFix.Transfer.HkMem_descent_Q0Sm α hα0 4 (hwSmo.forall 5) hwMem5).2.2
  have hDzbd : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) ≤ A6 * B :=
    le_trans (Work.FTS.GalFields.Xn_Dz_le_Xn5 hα0 hwSmo hwMem5) hw5
  -- ## the elliptic package and the modulation bounds
  have hEllw : Work.FTS.VocabO.EllPkgGo α Ce w (E w) := (hEll w hwC).1
  -- the modulation input, rewritten from the `fun z θ _ => w z θ` shape of `hml` into the
  -- `famOf`-shape used by `Xrhs`
  have hfam : (famOf (fun _ : ℝ => w) : ℝ → ℝ → ℝ → ℝ) = (fun z θ _ => w z θ) := rfl
  have hmlw := hml w hwC hw4
  rw [← hfam] at hmlw
  have hmu0 : |Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w)))
      (famOf (fun _ => w)) 0| ≤ Mm := by
    simpa only [Real.norm_eq_abs] using hmlw.1
  have hlam0 : |Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w)))
      (famOf (fun _ => w)) 0| ≤ Ml := by
    simpa only [Real.norm_eq_abs] using hmlw.2
  -- ## the identification of the scheme's right-hand side at `u`
  have hWs : slice (JfamP ρ ε (famOf (fun _ : ℝ => u))) τ = w := rfl
  have hW0s : slice (famOf (fun _ => w)) 0 = w := rfl
  have hPhi : slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε (famOf (fun _ : ℝ => u)))) τ
      = slice (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w))) 0 := by
    funext z θ
    simp only [Work.FTS.Nonlin.PsiCan, Work.FTS.Galerkin.slice_apply, hWs, hW0s]
  have hF : Construction.Ftau α (JfamP ρ ε (famOf (fun _ : ℝ => u))) τ
      = Construction.Ftau α (famOf (fun _ => w)) 0 := by
    funext z θ
    simp only [Work.Construction.Ftau]
    rw [show JfamP ρ ε (famOf (fun _ : ℝ => u)) z θ τ = w z θ from
        congrFun (congrFun hWs z) θ]
    rfl
  have hmu : Work.FTS.Galerkin.muDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε (famOf (fun _ : ℝ => u))))
      (JfamP ρ ε (famOf (fun _ : ℝ => u))) τ
      = Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w)))
          (famOf (fun _ => w)) 0 := by
    rw [Work.FTS.Galerkin.muDyn_eq, Work.FTS.Galerkin.muDyn_eq, hF, hWs, hW0s, hPhi]
  have hlam : Work.FTS.Galerkin.lamDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε (famOf (fun _ : ℝ => u))))
      (JfamP ρ ε (famOf (fun _ : ℝ => u))) τ
      = Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w)))
          (famOf (fun _ => w)) 0 := by
    rw [Work.FTS.Galerkin.lamDyn, Work.FTS.Galerkin.lamDyn, hmu]
  have hFt : Construction.Ftau α (famOf (fun _ => w)) 0 = Work.Construction.Ftot α w := rfl
  have hPs : slice (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w))) 0
      = fun z θ => Φs z θ + E w z θ := rfl
  have key : epsWP α ρ ε Φs E (famOf (fun _ : ℝ => u)) τ
      = Work.FTS.StrongEps.EpsLocalPStar.Xrhs α Φs E w := by
    funext z θ
    simp only [epsWP, Work.FTS.StrongEps.EpsLocalPStar.Xrhs,
      Work.FTS.StrongPersist.dynLin_eq_linPart,
      Work.FTS.StrongPersist.dynRHS_eq_rhsOf, hF, hWs, hW0s, hPhi, hmu, hlam, hFt, hPs]
  have hslice : epsRHPSlice α ρ ε Φs E τ u
      = Pz (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.Xrhs α Φs E w)) := by
    rw [epsRHPSlice, epsRHSP, key]
  -- ## the pieces of `X`
  set X : Fn := Work.FTS.StrongEps.EpsLocalPStar.Xrhs α Φs E w with hXdef
  set muU : ℝ := Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w)))
      (famOf (fun _ => w)) 0 with hmuUdef
  set lamU : ℝ := Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w)))
      (famOf (fun _ => w)) 0 with hlamUdef
  have hmuU : |muU| ≤ Mm := by rw [hmuUdef]; exact hmu0
  have hlamU : |lamU| ≤ Ml := by rw [hlamUdef]; exact hlam0
  have hMmnn : 0 ≤ Mm := le_trans (abs_nonneg muU) hmuU
  have hMlnn : 0 ≤ Ml := le_trans (abs_nonneg lamU) hlamU
  set mb : ℝ := Work.Construction.mubar
      (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
      (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + E w z θ)) with hmb
  set P1 : Fn := Work.FTS.StrongPersist.linPart α w with hP1
  set P2 : Fn := fun z θ => -mb * Work.Construction.AK α z θ with hP2
  set P3 : Fn := Work.Construction.N0 α (Work.Construction.Ftot α w) w with hP3
  set P4 : Fn := Work.Construction.N α (Work.Construction.Ftot α w)
      (fun z θ => Φs z θ + E w z θ) with hP4
  set P5 : Fn := Work.Construction.Nstar muU lamU w with hP5
  have hXsplit : X = (P1 + ((P2 + P3) + P4)) + P5 := by
    funext z θ
    simp only [hXdef, Work.FTS.StrongEps.EpsLocalPStar.Xrhs, hP1, hP2, hP3, hP4, hP5, hmb,
      hmuUdef, hlamUdef,
      Work.FTS.StrongPersist.rhsOf, Work.Construction.gRHS, Pi.add_apply]
    ring
  -- ## smoothness of the pieces
  obtain ⟨hL12totSmo, hFKtotSmo, hLGTsmo, hN0smo, hNsmo⟩ :=
    ClassCRHS.SmoothOpenRHS hα0 hα1 hwC hEllw hstar
  have hP1smo : Work.FTS.EllipticEst.SmoothOpen P1 := by
    show Work.FTS.EllipticEst.SmoothOpen (-(Work.Coercivity.LGammaT α w))
    exact hLGTsmo.neg
  have hP2smo : Work.FTS.EllipticEst.SmoothOpen P2 := by
    rw [hP2]
    exact Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen (-mb) hAKsmo
  have hP3smo : Work.FTS.EllipticEst.SmoothOpen P3 := hN0smo
  have hP4smo : Work.FTS.EllipticEst.SmoothOpen P4 := hNsmo
  have hP5eq : P5 = fun z θ => (-muU) * w z θ
      + (-(muU + lamU + muU * lamU)) * Work.Spaces.Dz w z θ := by
    funext z θ
    rw [hP5, Work.Construction.Nstar]
    ring
  have hP5smo : Work.FTS.EllipticEst.SmoothOpen P5 := by
    rw [hP5eq]
    exact Work.FTS.NonlinRows.smoothOpen_add
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-muU) hwSmo)
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-(muU + lamU + muU * lamU)) hwSmo.Dz)
  -- ## membership of the pieces
  have hP1mem : Work.Spaces.HkMem α 4 P1 := by
    show Work.Spaces.HkMem α 4 (-(Work.Coercivity.LGammaT α w))
    exact Work.FTS.StrongEps.EpsLocalPStar.hkMem_neg_fts (hLGT (w := w) hwC hw4' hw6).1
  have hP2mem : Work.Spaces.HkMem α 4 P2 := by
    rw [hP2]
    exact Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-mb) hAKmem
  have hP3mem : Work.Spaces.HkMem α 4 P3 := by
    simpa only [hP3] using (hN0 (w := w) hwC hw4' hw6).1
  have hP4mem : Work.Spaces.HkMem α 4 P4 := by
    simpa only [hP4] using (hN (w := w) (Φg := E w) hwC hw4' hw6 hEllw hstar).1
  have hP5mem : Work.Spaces.HkMem α 4 P5 := by
    rw [hP5eq]
    exact Work.FTS.EllipticEst.HkMem_add_open
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-muU) hwSmo)
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-(muU + lamU + muU * lamU)) hwSmo.Dz)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-muU) hwMem4)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-(muU + lamU + muU * lamU)) hDzmem)
  -- ## the bounds of the pieces
  have hP1bd : Work.FTS.Nonlin.Xn α P1 ≤ K1 := by
    show Work.Spaces.HkNorm α 4 (-(Work.Coercivity.LGammaT α w)) ≤ K1
    rw [Work.FTS.EllipticEst.HkNorm_neg]
    exact (hLGT (w := w) hwC hw4' hw6).2
  have hP3bd : Work.FTS.Nonlin.Xn α P3 ≤ K2 := by
    simpa only [hP3] using (hN0 (w := w) hwC hw4' hw6).2
  have hP4bd : Work.FTS.Nonlin.Xn α P4 ≤ K3 := by
    simpa only [hP4] using (hN (w := w) (Φg := E w) hwC hw4' hw6 hEllw hstar).2
  have hmubar : |mb| ≤ CL * (K2 + K3) := by
    rw [hmb, Work.Construction.mubar]
    have h1 : |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) 0|
        ≤ CL * Work.FTS.Nonlin.Xn α P3 := hl12z α hα0 hα1 P3 ⟨hP3smo, hP3mem⟩
    have h2 : |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + E w z θ)) 0| ≤ CL * Work.FTS.Nonlin.Xn α P4 :=
      hl12z α hα0 hα1 P4 ⟨hP4smo, hP4mem⟩
    have h3 : Work.FTS.Nonlin.Xn α P3 ≤ K2 := hP3bd
    have h4 : Work.FTS.Nonlin.Xn α P4 ≤ K3 := hP4bd
    calc |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) 0
            + Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α w)
              (fun z θ => Φs z θ + E w z θ)) 0|
        ≤ |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) 0|
          + |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α w)
              (fun z θ => Φs z θ + E w z θ)) 0| := abs_add_le _ _
      _ ≤ CL * K2 + CL * K3 := add_le_add
          (le_trans h1 (mul_le_mul_of_nonneg_left h3 hCLnn))
          (le_trans h2 (mul_le_mul_of_nonneg_left h4 hCLnn))
      _ = CL * (K2 + K3) := by ring
  have hP2bd : Work.FTS.Nonlin.Xn α P2 ≤ Lam := by
    have h1 : Work.FTS.Nonlin.Xn α P2
        = |mb| * Work.FTS.Nonlin.Xn α (Work.Construction.AK α) := by
      rw [hP2, Work.FTS.Nonlin.Xn,
        Work.FTS.EllipticEst.HkNorm_const_mul (α := α) (k := 4) (c := -mb) hAKsmo.forall,
        abs_neg]
    rw [h1]
    have h2 : |mb| * Work.FTS.Nonlin.Xn α (Work.Construction.AK α)
        ≤ (CL * (K2 + K3)) * KAK :=
      mul_le_mul hmubar hAKbd (Work.Spaces.HkNorm_nonneg _ _ _)
        (le_trans (abs_nonneg _) hmubar)
    have hnn : 0 ≤ (CL * (K2 + K3)) * KAK :=
      mul_nonneg (mul_nonneg hCLnn (by linarith [hK2.le, hK3.le])) hKAK.le
    rw [hLamdef]
    refine le_trans (le_trans h2 ?_) (le_max_left _ _)
    nlinarith [hnn]
  have hP5bd : Work.FTS.Nonlin.Xn α P5 ≤ Nst := by
    rw [hP5eq]
    have hb1 : Work.Spaces.HkNorm α 4 (fun z θ => (-muU) * w z θ)
        = |muU| * Work.FTS.Nonlin.Xn α w := by
      rw [Work.FTS.EllipticEst.HkNorm_const_mul (α := α) (k := 4) (c := -muU) hwSmo.forall,
        abs_neg]
    have hb2 : Work.Spaces.HkNorm α 4
        (fun z θ => (-(muU + lamU + muU * lamU)) * Work.Spaces.Dz w z θ)
        = |muU + lamU + muU * lamU| * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) := by
      rw [Work.FTS.EllipticEst.HkNorm_const_mul (α := α) (k := 4)
        (c := -(muU + lamU + muU * lamU)) hwSmo.Dz.forall, abs_neg]
    have hsum := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-muU) hwSmo)
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-(muU + lamU + muU * lamU)) hwSmo.Dz)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-muU) hwMem4)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-(muU + lamU + muU * lamU)) hDzmem)
    have hkapp : |muU + lamU + muU * lamU| ≤ Mm + Ml + Mm * Ml := by
      calc |muU + lamU + muU * lamU| ≤ |muU + lamU| + |muU * lamU| := abs_add_le _ _
        _ ≤ (|muU| + |lamU|) + |muU| * |lamU| := by
            refine add_le_add (abs_add_le _ _) (le_of_eq (abs_mul _ _))
        _ ≤ (Mm + Ml) + Mm * Ml := by
            refine add_le_add (add_le_add hmuU hlamU) ?_
            exact mul_le_mul hmuU hlamU (abs_nonneg _) hMmnn
        _ = Mm + Ml + Mm * Ml := by ring
    have hknn : 0 ≤ Mm + Ml + Mm * Ml := by
      have hp : 0 ≤ Mm * Ml := mul_nonneg hMmnn hMlnn
      linarith
    have hstep : Work.Spaces.HkNorm α 4 (fun z θ => (-muU) * w z θ
        + (-(muU + lamU + muU * lamU)) * Work.Spaces.Dz w z θ)
        ≤ 2 * (Mm * B0 + (Mm + Ml + Mm * Ml) * (A6 * B)) := by
      refine le_trans hsum ?_
      rw [hb1, hb2]
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
      · exact mul_le_mul hmuU hw4 (Work.Spaces.HkNorm_nonneg _ _ _) hMmnn
      · exact mul_le_mul hkapp hDzbd (Work.Spaces.HkNorm_nonneg _ _ _) hknn
    rw [hNstdef]
    exact le_trans hstep (le_max_left _ _)
  -- ## the assembly of the pieces
  have hP23smo : Work.FTS.EllipticEst.SmoothOpen (P2 + P3) :=
    Work.FTS.NonlinRows.smoothOpen_add hP2smo hP3smo
  have hAsm1smo : Work.FTS.EllipticEst.SmoothOpen ((P2 + P3) + P4) :=
    Work.FTS.NonlinRows.smoothOpen_add hP23smo hP4smo
  have hAsm2smo : Work.FTS.EllipticEst.SmoothOpen (P1 + ((P2 + P3) + P4)) :=
    Work.FTS.NonlinRows.smoothOpen_add hP1smo hAsm1smo
  have hP23mem : Work.Spaces.HkMem α 4 (P2 + P3) :=
    Work.FTS.EllipticEst.HkMem_add_open hP2smo hP3smo hP2mem hP3mem
  have hAsm1mem : Work.Spaces.HkMem α 4 ((P2 + P3) + P4) :=
    Work.FTS.EllipticEst.HkMem_add_open hP23smo hP4smo hP23mem hP4mem
  have hAsm2mem : Work.Spaces.HkMem α 4 (P1 + ((P2 + P3) + P4)) :=
    Work.FTS.EllipticEst.HkMem_add_open hP1smo hAsm1smo hP1mem hAsm1mem
  -- ## the bound of `X`
  have hXbd : Work.FTS.Nonlin.Xn α X ≤ KX := by
    have hb1 : Work.FTS.Nonlin.Xn α ((P1 + ((P2 + P3) + P4)) + P5)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P1 + ((P2 + P3) + P4)) + Work.FTS.Nonlin.Xn α P5) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hAsm2smo hP5smo hAsm2mem hP5mem
    have hb2 : Work.FTS.Nonlin.Xn α (P1 + ((P2 + P3) + P4))
        ≤ 2 * (Work.FTS.Nonlin.Xn α P1 + Work.FTS.Nonlin.Xn α ((P2 + P3) + P4)) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hP1smo hAsm1smo hP1mem hAsm1mem
    have hb3 : Work.FTS.Nonlin.Xn α ((P2 + P3) + P4)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P2 + P3) + Work.FTS.Nonlin.Xn α P4) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hP23smo hP4smo hP23mem hP4mem
    have hb4 : Work.FTS.Nonlin.Xn α (P2 + P3)
        ≤ 2 * (Work.FTS.Nonlin.Xn α P2 + Work.FTS.Nonlin.Xn α P3) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hP2smo hP3smo hP2mem hP3mem
    have e4 : Work.FTS.Nonlin.Xn α (P2 + P3) ≤ 2 * (Lam + K2) := by linarith
    have e3 : Work.FTS.Nonlin.Xn α ((P2 + P3) + P4) ≤ 2 * (2 * (Lam + K2) + K3) := by linarith
    have e2 : Work.FTS.Nonlin.Xn α (P1 + ((P2 + P3) + P4))
        ≤ 2 * (K1 + 2 * (2 * (Lam + K2) + K3)) := by linarith
    have e1 : Work.FTS.Nonlin.Xn α ((P1 + ((P2 + P3) + P4)) + P5)
        ≤ 2 * (2 * (K1 + 2 * (2 * (Lam + K2) + K3)) + Nst) := by linarith
    rw [hXsplit]
    refine le_trans e1 ?_
    rw [hKXdef]
    have hL0 : 0 ≤ Lam := le_max_right _ _
    have hN0' : 0 ≤ Nst := le_max_right _ _
    linarith [hK1.le, hK2.le, hK3.le, hL0, hN0']
  -- ## `X` is smooth and honest
  have hXsmo : Work.FTS.EllipticEst.SmoothOpen X := by
    rw [hXsplit]
    exact Work.FTS.NonlinRows.smoothOpen_add hAsm2smo hP5smo
  have hXmem : Work.Spaces.HkMem α 4 X := by
    rw [hXsplit]
    exact Work.FTS.EllipticEst.HkMem_add_open hAsm2smo hP5smo hAsm2mem hP5mem
  have hX1mem : Work.Spaces.HkMem α 1 X :=
    Work.FTS.OpenPkg.HkMem_mono_open hXsmo 1 (by norm_num) hXmem
  -- ## the angular-boundary modification `X'`
  set X' : Fn := fun z θ => if θ ∈ Set.Ioo 0 (π / 2) then X z θ else 0 with hX'def
  have hX'smo : ∀ n : ℕ, ContDiffOn ℝ (↑n) (Function.uncurry X') Work.FTS.EllipticEst.Q0 := by
    intro n
    refine (hXsmo.forall n).congr (fun p hp => ?_)
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have h1 : X z θ = X' z θ := by
      simp only [hX'def, if_pos (show θ ∈ Set.Ioo 0 (π / 2) from ⟨hθ0, hθ1⟩)]
    have h2 : X' z θ = X z θ := h1.symm
    first
      | exact h1
      | exact h2
  have hvanX' : ∀ z : ℝ, 0 ≤ z → X' z 0 = 0 ∧ X' z (π / 2) = 0 := by
    intro z _
    have h0 : ¬((0 : ℝ) ∈ Set.Ioo 0 (π / 2)) := by simp [Set.mem_Ioo]
    have h1 : ¬((π / 2 : ℝ) ∈ Set.Ioo 0 (π / 2)) := by
      simp only [Set.mem_Ioo]
      exact fun h => lt_irrefl _ h.2
    exact ⟨by rw [hX'def]; exact if_neg h0, by rw [hX'def]; exact if_neg h1⟩
  have hX'agree : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), X z θ = X' z θ := by
    intro z _ θ hθ
    simp only [hX'def, if_pos hθ]
  have hX'1mem : Work.Spaces.HkMem α 1 X' :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 1 hX1mem hX'agree
  have hX'4mem : Work.Spaces.HkMem α 4 X' :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hXmem hX'agree
  have hJX' : Jeps ρ ε X' = Jeps ρ ε X := by
    funext z θ
    by_cases hq : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
    · rw [Jeps_eq_integral ρ ε X' hq.1 hq.2, Jeps_eq_integral ρ ε X hq.1 hq.2]
      refine integral_congr_ae (Eventually.of_forall (fun p => ?_))
      simp only [hX'def, if_pos (thShift_mem hq.2)]
    · rw [Jeps_eq_zero ρ ε X' hq, Jeps_eq_zero ρ ε X hq]
  have hmoll6 : Work.Spaces.HkMem α 6 (Jeps ρ ε X') :=
    hgain α hα0 hα1 1 5 le_rfl ε hε0 hε1 X' hX'smo hvanX' hX'1mem
  have h6mem : Work.Spaces.HkMem α 6 (Jeps ρ ε X) := by
    rw [← hJX']; exact hmoll6
  have hJepsX'smo : Work.FTS.EllipticEst.SmoothOpen (Jeps ρ ε X') :=
    smoothOpen_Jeps ρ hρ hε0 hX'smo
  have hJepsX'4mem : Work.Spaces.HkMem α 4 (Jeps ρ ε X') :=
    HkMem_Jeps hρ.moll hα hε0 hX'smo hX'4mem
  have hbd4 : Work.Spaces.HkSq α 4 (Jeps ρ ε X')
      ≤ Real.exp (CJ * ε) * Work.Spaces.HkSq α 4 X' :=
    hCJ α hα 4 ε hε0 hε1 X' hX'smo hX'4mem hJepsX'4mem
  have hsqX' : Work.Spaces.HkSq α 4 X' ≤ KX ^ 2 := by
    have h : Work.Spaces.HkSq α 4 X' = Work.Spaces.HkSq α 4 X :=
      Work.FTS.EllipticEst.HkSq_congr_open α 4 (fun z θ hz hθ0 hθ1 => by
        simp only [hX'def, if_pos (show θ ∈ Set.Ioo 0 (π / 2) from ⟨hθ0, hθ1⟩)])
    rw [h]
    have h1 : Work.Spaces.HkSq α 4 X = (Work.FTS.Nonlin.Xn α X) ^ 2 := by
      rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 X)]
    rw [h1]
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 X) hXbd 2
  have hJ4 : Work.Spaces.HkNorm α 4 (Jeps ρ ε X') ≤ Real.exp (CJ / 2) * KX := by
    have hstep : Work.Spaces.HkNorm α 4 (Jeps ρ ε X') ≤ Real.exp (CJ * ε / 2) * KX := by
      calc Work.Spaces.HkNorm α 4 (Jeps ρ ε X')
          = Real.sqrt (Work.Spaces.HkSq α 4 (Jeps ρ ε X')) := rfl
        _ ≤ Real.sqrt (Real.exp (CJ * ε) * KX ^ 2) := Real.sqrt_le_sqrt
            (le_trans hbd4 (mul_le_mul_of_nonneg_left hsqX' (Real.exp_pos _).le))
        _ = Real.exp (CJ * ε / 2) * KX := by
            rw [Real.sqrt_mul (Real.exp_pos _).le, Real.sqrt_sq hKXnn, Real.exp_half]
    refine le_trans hstep ?_
    refine mul_le_mul_of_nonneg_right ?_ hKXnn
    exact Real.exp_le_exp.mpr (by nlinarith [hε1, hCJpos, hCJpos.le])
  have hPzbd : Work.Spaces.HkNorm α 4 (Pz (Jeps ρ ε X'))
      ≤ A * Real.exp (CJ / 2) * KX := by
    refine le_trans (hAbnd α hα 4 le_rfl (Jeps ρ ε X') hJepsX'smo hJepsX'4mem) ?_
    calc A * Work.Spaces.HkNorm α 4 (Jeps ρ ε X')
        ≤ A * (Real.exp (CJ / 2) * KX) := mul_le_mul_of_nonneg_left hJ4 hApos.le
      _ = A * Real.exp (CJ / 2) * KX := by ring
  -- ## the final assembly
  have hPz_eq : Pz (Jeps ρ ε X') = fun z θ => Jeps ρ ε X' z θ
      + (-(Work.Construction.L12 (Jeps ρ ε X') 0 / Work.FTS.StrongEps.pzNorm))
        * Work.FTS.StrongEps.bump z θ := by
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply]
    ring
  have hPzbdsmo : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Jeps ρ ε X' z θ
        + (-(Work.Construction.L12 (Jeps ρ ε X') 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.NonlinRows.smoothOpen_add hJepsX'smo
      (Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen
        (-(Work.Construction.L12 (Jeps ρ ε X') 0 / Work.FTS.StrongEps.pzNorm))
        Work.FTS.StrongEps.smoothOpen_bump)
  have hPzbdmem : Work.Spaces.HkMem α 6
      (fun z θ => Jeps ρ ε X' z θ
        + (-(Work.Construction.L12 (Jeps ρ ε X') 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open hJepsX'smo
      (Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen
        (-(Work.Construction.L12 (Jeps ρ ε X') 0 / Work.FTS.StrongEps.pzNorm))
        Work.FTS.StrongEps.smoothOpen_bump)
      hmoll6
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen
        (-(Work.Construction.L12 (Jeps ρ ε X') 0 / Work.FTS.StrongEps.pzNorm))
        (Work.FTS.StrongEps.PZeroAux.classC_Pz_hkMem_bump α 6))
  have hPzbd' : Work.Spaces.HkNorm α 4 (fun z θ => Jeps ρ ε X' z θ
      + (-(Work.Construction.L12 (Jeps ρ ε X') 0 / Work.FTS.StrongEps.pzNorm))
        * Work.FTS.StrongEps.bump z θ)
      ≤ max (A * Real.exp (CJ / 2) * KX) 1 := by
    rw [← hPz_eq]
    exact le_trans hPzbd (le_max_left _ _)
  rw [hslice, ← hJX', hPz_eq]
  exact ⟨hPzbdsmo, hPzbdmem, hPzbd'⟩

end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.HkNorm_epsRHSP_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The `ℋ⁴`-size of the scheme's right-hand side is bounded uniformly in the fake time.**
This is `EpsLocalPStar.EpsRHSPBdd` transported to the *family* form via
`StrongEps.epsRHSP_eq_slice`. -/
theorem HkNorm_epsRHSP_le {α C₀ Ce Cs B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam}
    {ε T : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hB : 0 ≤ B)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (slice g s))
    (hmem : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α 6 (slice g s))
    (hbd : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkNorm α 6 (slice g s) ≤ B)
    (hC : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (slice g s))))
    (hball : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (slice g s)))
        ≤ C₀ * α ^ 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ) ≤ R := by
  obtain ⟨R, hR, hbdR⟩ :=
    Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPBdd (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (B := B) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) hα hρ hε hε1 hEll hstar hml hB
  refine ⟨R, hR, fun σ hσ => ?_⟩
  rw [Work.FTS.StrongEps.epsRHSP_eq_slice]
  exact (hbdR σ (slice g σ) (hsm σ hσ) (hmem σ hσ) (hbd σ hσ) (hC σ hσ) (hball σ hσ)).2.2


end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRHSPBdd_unif =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn Fam slice famOf)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The `ε`-uniform version of `Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPBdd`: the
`ℋ⁴`-size of the scheme's right-hand side at a single profile `u` is bounded by a constant
`R` that does **not** depend on the mollification scale `ε` (only on `ρ`, `α`, `C₀`, `Ce`, `Cs`,
`Φs`, `E` and the `ℋ⁶`-size `B` of the datum).

The proof is the proof of `EpsRHSPBdd` with the constant extraction moved before the
introduction of `ε`; every constant there (`K1`,`K2`,`K3`, `A`, `CJ`, `KAK`, `CL`, `Lam`,
`Nst`, `KX`) is built from the interface data and `B` only, and `ε` enters only through the
two hypotheses `0 < ε`, `ε ≤ 1`. -/
theorem EpsRHSPBdd_unif {α C₀ Ce Cs B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hB : 0 ≤ B) :
    ∃ R : ℝ, 0 < R ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ (τ : ℝ) (u : Work.FTS.Galerkin.Fn),
      Work.FTS.EllipticEst.SmoothOpen u → Work.Spaces.HkMem α 6 u →
      Work.Spaces.HkNorm α 6 u ≤ B →
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)) →
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u))
        ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E τ u) ≤ R := by
  classical
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- ## the constants of the three block estimates, of the projected family, and of the mollifier
  obtain ⟨A6, hA6, hJfamP⟩ := HkNorm_JfamP_le (ρ := ρ) hρ
  have hAB0 : 0 ≤ A6 * B := mul_nonneg hA6 hB
  obtain ⟨K1, hK1, hLGT⟩ := ClassCRHS.HkMemXnLGammaT (α := α) hα (C₀ := C₀) (B := A6 * B)
  obtain ⟨K2, hK2, hN0⟩ := ClassCRHS.HkMemXnN0 (α := α) hα (C₀ := C₀) (B := A6 * B)
  obtain ⟨K3, hK3, hN⟩ := ClassCRHS.HkMemXnN (α := α) hα (C₀ := C₀) (B := A6 * B) (Ce := Ce) (Cs := Cs)
    (Φs := Φs)
  obtain ⟨A, hApos, hAbnd⟩ := Work.FTS.StrongEps.PZeroAux.PzHkNormFour
  obtain ⟨CJ, hCJpos, hCJ⟩ := HkSq_Jeps_le ρ hρ.moll
  obtain ⟨KAK, hKAK, hra⟩ := Work.FTS.Nonlinear.Pieces.rak_bound
  have hAKmem : Work.Spaces.HkMem α 4 (Work.Construction.AK α) :=
    Work.FTS.NonlinRows.HkMem_AK α hα0 hα1
  have hAKbd : Work.FTS.Nonlin.Xn α (Work.Construction.AK α) ≤ KAK := hra hα0 hα1
  have hAKsmo : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.AK α) :=
    Work.FTS.StrongPersist.AK_smoothO α
  obtain ⟨CL, hCL, hl12z⟩ := Work.FTS.OpenPkg.l12zero_field
  have hCLnn : 0 ≤ CL := hCL.le
  have hgain := EpsE4Thr.HkMem_Jeps_gain (ρ := ρ) hρ
  -- the crude constant of the estimate (valid for *every* datum `w`)
  set Lam : ℝ := max (2 * CL * (K2 + K3) * KAK) 0 with hLamdef
  set Nst : ℝ := max (2 * ((1 / 2) * (C₀ * α ^ 2) + 2 * (A6 * B))) 0 with hNstdef
  set KX : ℝ := 16 * (K1 + Lam + K2 + K3 + Nst) with hKXdef
  have hKXnn : 0 ≤ KX := by
    rw [hKXdef]
    have h1 : 0 ≤ K1 := hK1.le
    have hL0 : 0 ≤ Lam := le_max_right _ _
    have hN0' : 0 ≤ Nst := le_max_right _ _
    have h2 : 0 ≤ K2 := hK2.le
    have h3 : 0 ≤ K3 := hK3.le
    linarith
  refine ⟨max (A * Real.exp (CJ / 2) * KX) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  intro ε hεIoc τ u huSmo huMem huBd hwC hw4
  have hε0 : 0 < ε := hεIoc.1
  have hε1 : ε ≤ 1 := hεIoc.2
  set w : Fn := Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u) with hwdef
  -- ## the data of `w`
  have hwSmo : Work.FTS.EllipticEst.SmoothOpen w := hwC.reg
  have hwMem6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hwC.reg 6 (by norm_num) hwC.mem
  have hwMem5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hwC.reg 5 (by norm_num) hwC.mem
  have hwMem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hwC.reg 4 (by norm_num) hwC.mem
  have hw6 : Work.Spaces.HkNorm α 6 w ≤ A6 * B := by
    have h := (hJfamP (g := famOf (fun _ : ℝ => u)) (s := τ) ⟨hα0, hα1⟩ ⟨hε0, hε1⟩
      (fun n => huSmo.forall n) huMem).2
    have hslice : slice (famOf (fun _ : ℝ => u)) τ = u := rfl
    rw [hslice] at h
    exact le_trans h (mul_le_mul_of_nonneg_left huBd hA6)
  have hw5 : Work.Spaces.HkNorm α 5 w ≤ A6 * B :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := 5) (by norm_num) hwMem6)
      hw6
  have hDzmem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz w) :=
    (Work.FTS.CoercivityFix.Transfer.HkMem_descent_Q0Sm α hα0 4 (hwSmo.forall 5) hwMem5).2.2
  have hDzbd : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) ≤ A6 * B :=
    le_trans (Work.FTS.GalFields.Xn_Dz_le_Xn5 hα0 hwSmo hwMem5) hw5
  -- ## the elliptic package and the modulation bounds
  have hEllw : Work.FTS.VocabO.EllPkgGo α Ce w (E w) := (hEll w hwC).1
  have hmu0 := (hml w hwC hw4).1
  have hlam0 := (hml w hwC hw4).2
  -- ## the identification of the scheme's right-hand side at `u`
  have hWs : slice (JfamP ρ ε (famOf (fun _ : ℝ => u))) τ = w := rfl
  have hW0s : slice (famOf (fun _ => w)) 0 = w := rfl
  have hPhi : slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε (famOf (fun _ : ℝ => u)))) τ
      = slice (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w))) 0 := by
    funext z θ
    simp only [Work.FTS.Nonlin.PsiCan, Work.FTS.Galerkin.slice_apply, hWs, hW0s]
  have hF : Construction.Ftau α (JfamP ρ ε (famOf (fun _ : ℝ => u))) τ
      = Construction.Ftau α (famOf (fun _ => w)) 0 := by
    funext z θ
    simp only [Work.Construction.Ftau]
    rw [show JfamP ρ ε (famOf (fun _ : ℝ => u)) z θ τ = w z θ from
        congrFun (congrFun hWs z) θ]
    rfl
  have hmu : Work.FTS.Galerkin.muDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε (famOf (fun _ : ℝ => u))))
      (JfamP ρ ε (famOf (fun _ : ℝ => u))) τ
      = Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w)))
          (famOf (fun _ => w)) 0 := by
    rw [Work.FTS.Galerkin.muDyn_eq, Work.FTS.Galerkin.muDyn_eq, hF, hWs, hW0s, hPhi]
  have hlam : Work.FTS.Galerkin.lamDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε (famOf (fun _ : ℝ => u))))
      (JfamP ρ ε (famOf (fun _ : ℝ => u))) τ
      = Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w)))
          (famOf (fun _ => w)) 0 := by
    rw [Work.FTS.Galerkin.lamDyn, Work.FTS.Galerkin.lamDyn, hmu]
  have hFt : Construction.Ftau α (famOf (fun _ => w)) 0 = Work.Construction.Ftot α w := rfl
  have hPs : slice (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w))) 0
      = fun z θ => Φs z θ + E w z θ := rfl
  have key : epsWP α ρ ε Φs E (famOf (fun _ : ℝ => u)) τ = Work.FTS.StrongEps.EpsLocalPStar.Xrhs α Φs E w := by
    funext z θ
    simp only [epsWP, Work.FTS.StrongEps.EpsLocalPStar.Xrhs, Work.FTS.StrongPersist.dynLin_eq_linPart,
      Work.FTS.StrongPersist.dynRHS_eq_rhsOf, hF, hWs, hW0s, hPhi, hmu, hlam, hFt, hPs]
  have hslice : epsRHPSlice α ρ ε Φs E τ u = Pz (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.Xrhs α Φs E w)) := by
    rw [epsRHPSlice, epsRHSP, key]
  -- ## the pieces of `X`
  set X : Fn := Work.FTS.StrongEps.EpsLocalPStar.Xrhs α Φs E w with hXdef
  set muU : ℝ := Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w)))
      (famOf (fun _ => w)) 0 with hmuUdef
  set lamU : ℝ := Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w)))
      (famOf (fun _ => w)) 0 with hlamUdef
  have hmuU : |muU| ≤ 1 / 2 := by rw [hmuUdef]; exact hmu0
  have hlamU : |lamU| ≤ 1 := by rw [hlamUdef]; exact hlam0
  set mb : ℝ := Work.Construction.mubar
      (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
      (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + E w z θ)) with hmb
  set P1 : Fn := Work.FTS.StrongPersist.linPart α w with hP1
  set P2 : Fn := fun z θ => -mb * Work.Construction.AK α z θ with hP2
  set P3 : Fn := Work.Construction.N0 α (Work.Construction.Ftot α w) w with hP3
  set P4 : Fn := Work.Construction.N α (Work.Construction.Ftot α w)
      (fun z θ => Φs z θ + E w z θ) with hP4
  set P5 : Fn := Work.Construction.Nstar muU lamU w with hP5
  have hXsplit : X = (P1 + ((P2 + P3) + P4)) + P5 := by
    funext z θ
    simp only [hXdef, Work.FTS.StrongEps.EpsLocalPStar.Xrhs, hP1, hP2, hP3, hP4, hP5, hmb, hmuUdef, hlamUdef,
      Work.FTS.StrongPersist.rhsOf, Work.Construction.gRHS, Pi.add_apply]
    ring
  -- ## smoothness of the pieces
  obtain ⟨hL12totSmo, hFKtotSmo, hLGTsmo, hN0smo, hNsmo⟩ :=
    ClassCRHS.SmoothOpenRHS hα0 hα1 hwC hEllw hstar
  have hP1smo : Work.FTS.EllipticEst.SmoothOpen P1 := by
    show Work.FTS.EllipticEst.SmoothOpen (-(Work.Coercivity.LGammaT α w))
    exact hLGTsmo.neg
  have hP2smo : Work.FTS.EllipticEst.SmoothOpen P2 := by
    rw [hP2]
    exact Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen (-mb) hAKsmo
  have hP3smo : Work.FTS.EllipticEst.SmoothOpen P3 := hN0smo
  have hP4smo : Work.FTS.EllipticEst.SmoothOpen P4 := hNsmo
  have hP5eq : P5 = fun z θ => (-muU) * w z θ
      + (-(muU + lamU + muU * lamU)) * Work.Spaces.Dz w z θ := by
    funext z θ
    rw [hP5, Work.Construction.Nstar]
    ring
  have hP5smo : Work.FTS.EllipticEst.SmoothOpen P5 := by
    rw [hP5eq]
    exact Work.FTS.NonlinRows.smoothOpen_add
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-muU) hwSmo)
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-(muU + lamU + muU * lamU)) hwSmo.Dz)
  -- ## membership of the pieces
  have hP1mem : Work.Spaces.HkMem α 4 P1 := by
    show Work.Spaces.HkMem α 4 (-(Work.Coercivity.LGammaT α w))
    exact Work.FTS.StrongEps.EpsLocalPStar.hkMem_neg_fts (hLGT (w := w) hwC hw4 hw6).1
  have hP2mem : Work.Spaces.HkMem α 4 P2 := by
    rw [hP2]
    exact Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-mb) hAKmem
  have hP3mem : Work.Spaces.HkMem α 4 P3 := by
    simpa only [hP3] using (hN0 (w := w) hwC hw4 hw6).1
  have hP4mem : Work.Spaces.HkMem α 4 P4 := by
    simpa only [hP4] using (hN (w := w) (Φg := E w) hwC hw4 hw6 hEllw hstar).1
  have hP5mem : Work.Spaces.HkMem α 4 P5 := by
    rw [hP5eq]
    exact Work.FTS.EllipticEst.HkMem_add_open
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-muU) hwSmo)
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-(muU + lamU + muU * lamU)) hwSmo.Dz)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-muU) hwMem4)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-(muU + lamU + muU * lamU)) hDzmem)
  -- ## the bounds of the pieces
  have hP1bd : Work.FTS.Nonlin.Xn α P1 ≤ K1 := by
    show Work.Spaces.HkNorm α 4 (-(Work.Coercivity.LGammaT α w)) ≤ K1
    rw [Work.FTS.EllipticEst.HkNorm_neg]
    exact (hLGT (w := w) hwC hw4 hw6).2
  have hP3bd : Work.FTS.Nonlin.Xn α P3 ≤ K2 := by
    simpa only [hP3] using (hN0 (w := w) hwC hw4 hw6).2
  have hP4bd : Work.FTS.Nonlin.Xn α P4 ≤ K3 := by
    simpa only [hP4] using (hN (w := w) (Φg := E w) hwC hw4 hw6 hEllw hstar).2
  have hmubar : |mb| ≤ CL * (K2 + K3) := by
    rw [hmb, Work.Construction.mubar]
    have h1 : |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) 0|
        ≤ CL * Work.FTS.Nonlin.Xn α P3 := hl12z α hα0 hα1 P3 ⟨hP3smo, hP3mem⟩
    have h2 : |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + E w z θ)) 0| ≤ CL * Work.FTS.Nonlin.Xn α P4 :=
      hl12z α hα0 hα1 P4 ⟨hP4smo, hP4mem⟩
    have h3 : Work.FTS.Nonlin.Xn α P3 ≤ K2 := hP3bd
    have h4 : Work.FTS.Nonlin.Xn α P4 ≤ K3 := hP4bd
    calc |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) 0
            + Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α w)
              (fun z θ => Φs z θ + E w z θ)) 0|
        ≤ |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) 0|
          + |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α w)
              (fun z θ => Φs z θ + E w z θ)) 0| := abs_add_le _ _
      _ ≤ CL * K2 + CL * K3 := add_le_add
          (le_trans h1 (mul_le_mul_of_nonneg_left h3 hCLnn))
          (le_trans h2 (mul_le_mul_of_nonneg_left h4 hCLnn))
      _ = CL * (K2 + K3) := by ring
  have hP2bd : Work.FTS.Nonlin.Xn α P2 ≤ Lam := by
    have h1 : Work.FTS.Nonlin.Xn α P2
        = |mb| * Work.FTS.Nonlin.Xn α (Work.Construction.AK α) := by
      rw [hP2, Work.FTS.Nonlin.Xn,
        Work.FTS.EllipticEst.HkNorm_const_mul (α := α) (k := 4) (c := -mb) hAKsmo.forall,
        abs_neg]
    rw [h1]
    have h2 : |mb| * Work.FTS.Nonlin.Xn α (Work.Construction.AK α)
        ≤ (CL * (K2 + K3)) * KAK :=
      mul_le_mul hmubar hAKbd (Work.Spaces.HkNorm_nonneg _ _ _)
        (le_trans (abs_nonneg _) hmubar)
    have hnn : 0 ≤ (CL * (K2 + K3)) * KAK :=
      mul_nonneg (mul_nonneg hCLnn (by linarith [hK2.le, hK3.le])) hKAK.le
    rw [hLamdef]
    refine le_trans (le_trans h2 ?_) (le_max_left _ _)
    nlinarith [hnn]
  have hP5bd : Work.FTS.Nonlin.Xn α P5 ≤ Nst := by
    rw [hP5eq]
    have hb1 : Work.Spaces.HkNorm α 4 (fun z θ => (-muU) * w z θ)
        = |muU| * Work.FTS.Nonlin.Xn α w := by
      rw [Work.FTS.EllipticEst.HkNorm_const_mul (α := α) (k := 4) (c := -muU) hwSmo.forall,
        abs_neg]
    have hb2 : Work.Spaces.HkNorm α 4
        (fun z θ => (-(muU + lamU + muU * lamU)) * Work.Spaces.Dz w z θ)
        = |muU + lamU + muU * lamU| * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) := by
      rw [Work.FTS.EllipticEst.HkNorm_const_mul (α := α) (k := 4)
        (c := -(muU + lamU + muU * lamU)) hwSmo.Dz.forall, abs_neg]
    have hsum := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-muU) hwSmo)
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-(muU + lamU + muU * lamU)) hwSmo.Dz)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-muU) hwMem4)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-(muU + lamU + muU * lamU)) hDzmem)
    have hkapp : |muU + lamU + muU * lamU| ≤ 2 := by
      have h1 : |muU| ≤ 1 / 2 := hmuU
      have h2 : |lamU| ≤ 1 := hlamU
      calc |muU + lamU + muU * lamU| ≤ |muU + lamU| + |muU * lamU| := abs_add_le _ _
        _ ≤ (|muU| + |lamU|) + |muU| * |lamU| := by
            refine add_le_add (abs_add_le _ _) (le_of_eq (abs_mul _ _))
        _ ≤ (1 / 2 + 1) + (1 / 2) * 1 := by
            refine add_le_add (add_le_add h1 h2) ?_
            exact mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        _ = 2 := by norm_num
    have hstep : Work.Spaces.HkNorm α 4 (fun z θ => (-muU) * w z θ
        + (-(muU + lamU + muU * lamU)) * Work.Spaces.Dz w z θ)
        ≤ 2 * ((1 / 2) * (C₀ * α ^ 2) + 2 * (A6 * B)) := by
      refine le_trans hsum ?_
      rw [hb1, hb2]
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
      · exact mul_le_mul hmuU hw4 (Work.Spaces.HkNorm_nonneg _ _ _) (by norm_num)
      · exact mul_le_mul hkapp hDzbd (Work.Spaces.HkNorm_nonneg _ _ _) (by norm_num)
    rw [hNstdef]
    exact le_trans hstep (le_max_left _ _)
  -- ## the assembly of the pieces
  have hP23smo : Work.FTS.EllipticEst.SmoothOpen (P2 + P3) :=
    Work.FTS.NonlinRows.smoothOpen_add hP2smo hP3smo
  have hAsm1smo : Work.FTS.EllipticEst.SmoothOpen ((P2 + P3) + P4) :=
    Work.FTS.NonlinRows.smoothOpen_add hP23smo hP4smo
  have hAsm2smo : Work.FTS.EllipticEst.SmoothOpen (P1 + ((P2 + P3) + P4)) :=
    Work.FTS.NonlinRows.smoothOpen_add hP1smo hAsm1smo
  have hP23mem : Work.Spaces.HkMem α 4 (P2 + P3) :=
    Work.FTS.EllipticEst.HkMem_add_open hP2smo hP3smo hP2mem hP3mem
  have hAsm1mem : Work.Spaces.HkMem α 4 ((P2 + P3) + P4) :=
    Work.FTS.EllipticEst.HkMem_add_open hP23smo hP4smo hP23mem hP4mem
  have hAsm2mem : Work.Spaces.HkMem α 4 (P1 + ((P2 + P3) + P4)) :=
    Work.FTS.EllipticEst.HkMem_add_open hP1smo hAsm1smo hP1mem hAsm1mem
  -- ## the bound of `X`
  have hXbd : Work.FTS.Nonlin.Xn α X ≤ KX := by
    have hb1 : Work.FTS.Nonlin.Xn α ((P1 + ((P2 + P3) + P4)) + P5)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P1 + ((P2 + P3) + P4)) + Work.FTS.Nonlin.Xn α P5) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hAsm2smo hP5smo hAsm2mem hP5mem
    have hb2 : Work.FTS.Nonlin.Xn α (P1 + ((P2 + P3) + P4))
        ≤ 2 * (Work.FTS.Nonlin.Xn α P1 + Work.FTS.Nonlin.Xn α ((P2 + P3) + P4)) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hP1smo hAsm1smo hP1mem hAsm1mem
    have hb3 : Work.FTS.Nonlin.Xn α ((P2 + P3) + P4)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P2 + P3) + Work.FTS.Nonlin.Xn α P4) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hP23smo hP4smo hP23mem hP4mem
    have hb4 : Work.FTS.Nonlin.Xn α (P2 + P3)
        ≤ 2 * (Work.FTS.Nonlin.Xn α P2 + Work.FTS.Nonlin.Xn α P3) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hP2smo hP3smo hP2mem hP3mem
    have e4 : Work.FTS.Nonlin.Xn α (P2 + P3) ≤ 2 * (Lam + K2) := by linarith
    have e3 : Work.FTS.Nonlin.Xn α ((P2 + P3) + P4) ≤ 2 * (2 * (Lam + K2) + K3) := by linarith
    have e2 : Work.FTS.Nonlin.Xn α (P1 + ((P2 + P3) + P4))
        ≤ 2 * (K1 + 2 * (2 * (Lam + K2) + K3)) := by linarith
    have e1 : Work.FTS.Nonlin.Xn α ((P1 + ((P2 + P3) + P4)) + P5)
        ≤ 2 * (2 * (K1 + 2 * (2 * (Lam + K2) + K3)) + Nst) := by linarith
    rw [hXsplit]
    refine le_trans e1 ?_
    rw [hKXdef]
    linarith [hK1.le, hK2.le, hK3.le, le_max_right (2 * CL * (K2 + K3) * KAK) 0,
      le_max_right (2 * ((1 / 2) * (C₀ * α ^ 2) + 2 * (A6 * B))) 0]
  -- ## `X` is smooth and honest
  have hXsmo : Work.FTS.EllipticEst.SmoothOpen X := by
    rw [hXsplit]
    exact Work.FTS.NonlinRows.smoothOpen_add hAsm2smo hP5smo
  have hXmem : Work.Spaces.HkMem α 4 X := by
    rw [hXsplit]
    exact Work.FTS.EllipticEst.HkMem_add_open hAsm2smo hP5smo hAsm2mem hP5mem
  have hX1mem : Work.Spaces.HkMem α 1 X :=
    Work.FTS.OpenPkg.HkMem_mono_open hXsmo 1 (by norm_num) hXmem
  -- ## the angular-boundary modification `X'`
  set X' : Fn := fun z θ => if θ ∈ Set.Ioo 0 (π / 2) then X z θ else 0 with hX'def
  have hX'smo : ∀ n : ℕ, ContDiffOn ℝ (↑n) (Function.uncurry X') Work.FTS.EllipticEst.Q0 := by
    intro n
    refine (hXsmo.forall n).congr (fun p hp => ?_)
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have h1 : X z θ = X' z θ := by simp only [hX'def, if_pos (show θ ∈ Set.Ioo 0 (π / 2) from ⟨hθ0, hθ1⟩)]
    have h2 : X' z θ = X z θ := h1.symm
    first
      | exact h1
      | exact h2
  have hvanX' : ∀ z : ℝ, 0 ≤ z → X' z 0 = 0 ∧ X' z (π / 2) = 0 := by
    intro z _
    have h0 : ¬((0 : ℝ) ∈ Set.Ioo 0 (π / 2)) := by simp [Set.mem_Ioo]
    have h1 : ¬((π / 2 : ℝ) ∈ Set.Ioo 0 (π / 2)) := by
      simp only [Set.mem_Ioo]
      exact fun h => lt_irrefl _ h.2
    exact ⟨by rw [hX'def]; exact if_neg h0, by rw [hX'def]; exact if_neg h1⟩
  have hX'agree : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), X z θ = X' z θ := by
    intro z _ θ hθ
    simp only [hX'def, if_pos hθ]
  have hX'1mem : Work.Spaces.HkMem α 1 X' :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 1 hX1mem hX'agree
  have hX'4mem : Work.Spaces.HkMem α 4 X' :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hXmem hX'agree
  have hJX' : Jeps ρ ε X' = Jeps ρ ε X := by
    funext z θ
    by_cases hq : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
    · rw [Jeps_eq_integral ρ ε X' hq.1 hq.2, Jeps_eq_integral ρ ε X hq.1 hq.2]
      refine integral_congr_ae (Eventually.of_forall (fun p => ?_))
      simp only [hX'def, if_pos (thShift_mem hq.2)]
    · rw [Jeps_eq_zero ρ ε X' hq, Jeps_eq_zero ρ ε X hq]
  have hmoll6 : Work.Spaces.HkMem α 6 (Jeps ρ ε X') :=
    hgain α hα0 hα1 1 5 le_rfl ε hε0 hε1 X' hX'smo hvanX' hX'1mem
  have h6mem : Work.Spaces.HkMem α 6 (Jeps ρ ε X) := by
    rw [← hJX']; exact hmoll6
  have hJepsX'smo : Work.FTS.EllipticEst.SmoothOpen (Jeps ρ ε X') :=
    smoothOpen_Jeps ρ hρ hε0 hX'smo
  have hJepsX'4mem : Work.Spaces.HkMem α 4 (Jeps ρ ε X') :=
    HkMem_Jeps hρ.moll hα hε0 hX'smo hX'4mem
  have hbd4 : Work.Spaces.HkSq α 4 (Jeps ρ ε X')
      ≤ Real.exp (CJ * ε) * Work.Spaces.HkSq α 4 X' :=
    hCJ α hα 4 ε hε0 hε1 X' hX'smo hX'4mem hJepsX'4mem
  have hsqX' : Work.Spaces.HkSq α 4 X' ≤ KX ^ 2 := by
    have h : Work.Spaces.HkSq α 4 X' = Work.Spaces.HkSq α 4 X :=
      Work.FTS.EllipticEst.HkSq_congr_open α 4 (fun z θ hz hθ0 hθ1 => by
        simp only [hX'def, if_pos (show θ ∈ Set.Ioo 0 (π / 2) from ⟨hθ0, hθ1⟩)])
    rw [h]
    have h1 : Work.Spaces.HkSq α 4 X = (Work.FTS.Nonlin.Xn α X) ^ 2 := by
      rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 X)]
    rw [h1]
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 X) hXbd 2
  have hJ4 : Work.Spaces.HkNorm α 4 (Jeps ρ ε X') ≤ Real.exp (CJ / 2) * KX := by
    have hstep : Work.Spaces.HkNorm α 4 (Jeps ρ ε X') ≤ Real.exp (CJ * ε / 2) * KX := by
      calc Work.Spaces.HkNorm α 4 (Jeps ρ ε X')
          = Real.sqrt (Work.Spaces.HkSq α 4 (Jeps ρ ε X')) := rfl
        _ ≤ Real.sqrt (Real.exp (CJ * ε) * KX ^ 2) := Real.sqrt_le_sqrt
            (le_trans hbd4 (mul_le_mul_of_nonneg_left hsqX' (Real.exp_pos _).le))
        _ = Real.exp (CJ * ε / 2) * KX := by
            rw [Real.sqrt_mul (Real.exp_pos _).le, Real.sqrt_sq hKXnn, Real.exp_half]
    refine le_trans hstep ?_
    refine mul_le_mul_of_nonneg_right ?_ hKXnn
    exact Real.exp_le_exp.mpr (by nlinarith [hε1, hCJpos, hCJpos.le])
  have hPzbd : Work.Spaces.HkNorm α 4 (Pz (Jeps ρ ε X'))
      ≤ A * Real.exp (CJ / 2) * KX := by
    refine le_trans (hAbnd α hα 4 le_rfl (Jeps ρ ε X') hJepsX'smo hJepsX'4mem) ?_
    calc A * Work.Spaces.HkNorm α 4 (Jeps ρ ε X')
        ≤ A * (Real.exp (CJ / 2) * KX) := mul_le_mul_of_nonneg_left hJ4 hApos.le
      _ = A * Real.exp (CJ / 2) * KX := by ring
  -- ## the final assembly
  have hPz_eq : Pz (Jeps ρ ε X') = fun z θ => Jeps ρ ε X' z θ
      + (-(Work.Construction.L12 (Jeps ρ ε X') 0 / Work.FTS.StrongEps.pzNorm))
        * Work.FTS.StrongEps.bump z θ := by
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply]
    ring
  have hPzbd' : Work.Spaces.HkNorm α 4 (fun z θ => Jeps ρ ε X' z θ
      + (-(Work.Construction.L12 (Jeps ρ ε X') 0 / Work.FTS.StrongEps.pzNorm))
        * Work.FTS.StrongEps.bump z θ)
      ≤ max (A * Real.exp (CJ / 2) * KX) 1 := by
    rw [← hPz_eq]
    exact le_trans hPzbd (le_max_left _ _)
  rw [hslice, ← hJX', hPz_eq]
  exact hPzbd'

end Work.FTS.StrongEps
end
