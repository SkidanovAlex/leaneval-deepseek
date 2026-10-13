import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Open.Row26

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

/-- **Priced row 26**: the `ℋ⁴`-honesty and the `α²`-bound of the profile-only star piece
`N₅^{**} = -sin²θ · FK(F_*) · F_*`, with a *constant* independent of all data.

This piece does not involve `g`, `Φs` or `Φg` at all: it is the explicit function
`-(4α²/c(α)) · (sin²θ · Γ(θ)) · (z²/(1+z)⁴)`, an angular `×` radial product.  The corresponding
row of the open vocabulary is `Work.FTS.Nonlinear.Open.Row26`, whose statement carries the
interfaces `N4Norm'`, `N4Extra'`, `GalClass α g`, `StarPkgo α Cs Φs`, `EllPkgGo α Ce g Φg` and the
hypotheses `0 < α`, `α ≤ 1`, `α ≤ α₂` — but its proof uses *only* `0 < α` and `α ≤ 1` (the file's
own header says "The hypotheses `g`, `Φs`, `Φg` (and hence the interfaces) are irrelevant for this
row").  The body works with the explicit factorisation `N5ss α = fun z θ => a θ * r z` with
`r z = Work.Spaces.hKer z ^ 2`, the angular jet bound `dthIter_sinSq_Gam_le_sharp`, and the
`AngRadHkMem`/`Xn_ang_rad_le_gen`/`hkerSq_radial_alt` machinery whose constants are independent of
every hypothesis.  So the proof is a verbatim copy of that proof with the interface hypotheses
dropped. -/
theorem N5ssPriced : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N5ss α) ∧
    Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5ss α) ≤ C * α ^ 2 := by
  obtain ⟨Csh, hCshpos, hCsh⟩ := Work.FTS.Nonlinear.Open.Row26Ang
  obtain ⟨Cr, hCrpos, hCr⟩ := Work.FTS.Nonlinear.Pieces.RNP.hkerSq_radial_alt
  obtain ⟨M, hMpos, hM⟩ := Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt
  refine ⟨Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M) * (40 * Cr) + 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M) * (40 * Cr) := by
      positivity
    linarith
  · intro α hαIoc
    have hα : 0 < α := hαIoc.1
    have hα1 : α ≤ 1 := hαIoc.2
    have hcge : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
    have hcpos : 0 < Work.Spaces.c α := by linarith
    -- the angular profile, the radial factor and the angular majorant
    set psi : ℝ → ℝ := fun θ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ with hpsi
    set r : ℝ → ℝ := fun z => (-(4 * α ^ 2 / Work.Spaces.c α)) * Work.Spaces.hKer z ^ 2 with hr
    set G : ℝ → ℝ := fun θ => Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) with hG
    -- ### the factorisation of the piece
    have hfac : Work.FTS.Nonlin.N5ss α = fun z θ => psi θ * r z := by
      funext z θ
      rw [hpsi, hr]
      simp only [Work.FTS.Nonlin.N5ss]
      rw [Work.FTS.Nonlin.FK_Fstar hα hα1]
      simp only [Work.Construction.Fstar, Work.FM.Fstar, Work.Spaces.hKer_apply]
      ring
    -- ### smoothness of the two factors
    have hSOsin2 : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Real.sin θ ^ 2) := by
      have h1 := Work.FTS.NonlinRows.smoothOpen_const_mul (-1)
        Work.FTS.Nonlinear.Open.row25_smoothOpen_neg_sinSq
      rw [show (fun _ (θ : ℝ) => (-1 : ℝ) * (-(Real.sin θ ^ 2)))
          = fun _ (θ : ℝ) => Real.sin θ ^ 2 from by
        funext z θ; ring] at h1
      exact h1
    have hSOpsi : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => psi θ) := by
      rw [hpsi]
      exact Work.FTS.Nonlinear.Open.row25_smoothOpen_ang_mul hSOsin2
        (Work.FTS.Nonlinear.Open.row25_smoothOpen_Gam α)
    have hrSO : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => r z) := by
      rw [hr]
      refine Work.FTS.NonlinRows.smoothOpen_const_mul (-(4 * α ^ 2 / Work.Spaces.c α)) ?_
      refine Work.FTS.NonlinRows.smoothOpen_radial fun n => ?_
      have h := Work.FTS.Nonlinear.Open.row25_contDiffOn_hKer n
      simpa only [pow_two] using h.mul h
    -- ### the two angular bounds
    have ha0 : ∀ θ ∈ Work.Spaces.Iθ, |psi θ| ≤ 1 := by
      intro θ hθ
      simpa only [hpsi, Work.FTS.Nonlinear.Pieces.RNP.psiB] using
        Work.FTS.Nonlinear.Pieces.RNP.psiB_abs_le_one (α := α) hα hθ
    have ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => psi θ') 0 θ| ≤ Csh * G θ := by
      intro i hi1 hi4 θ hθ
      have h := hCsh α hα hα1 i hi1 hi4 θ hθ
      simpa only [hpsi, hG] using h
    -- ### the angular majorant
    have hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G θ := by
      intro θ hθ
      have hGam := Work.Spaces.Gam_bounds α θ hα hθ
      have hs := Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
      rw [hG]
      exact mul_nonneg hGam.1 (by linarith)
    have hGint : MeasureTheory.IntegrableOn
        (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ := by
      have h := (hM α hα hα1).1
      rw [hG]
      simpa only [mul_pow, mul_assoc] using h
    have hm1 : ∫ θ in Work.Spaces.Iθ,
        G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ ≤ M := by
      have h := (hM α hα hα1).2
      rw [hG]
      simpa only [mul_pow, mul_assoc] using h
    -- ### the radial factor
    have hrmem : Work.Spaces.HkMem α 4 (fun z (_ : ℝ) => r z) := by
      rw [hr]
      exact Work.FTS.LocData.HkMem_const_mul α 4 (-(4 * α ^ 2 / Work.Spaces.c α))
        (hCr α hα hα1).1
    have hcoefabs : |-(4 * α ^ 2 / Work.Spaces.c α)| ≤ 40 * α ^ 2 := by
      rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * α ^ 2 / Work.Spaces.c α),
        div_le_iff₀ hcpos]
      nlinarith [hcge, sq_nonneg α, hα.le]
    have hXnr : Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => r z) ≤ 40 * α ^ 2 * Cr := by
      have h0 : Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => Work.Spaces.hKer z ^ 2) ≤ Cr :=
        (hCr α hα hα1).2
      have hrew : Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => r z)
          = |-(4 * α ^ 2 / Work.Spaces.c α)|
            * Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => Work.Spaces.hKer z ^ 2) := by
        rw [hr]
        exact Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α (-(4 * α ^ 2 / Work.Spaces.c α))
          (fun z (_ : ℝ) => Work.Spaces.hKer z ^ 2)
      rw [hrew]
      exact mul_le_mul hcoefabs h0 (Work.Spaces.HkNorm_nonneg α 4 _) (by positivity)
    -- ### the honesty and the norm
    have hHk : Work.Spaces.HkMem α 4 (fun z θ => psi θ * r z) :=
      Work.FTS.NonlinRows.AuxAngRad.HkMem_ang_rad (α := α) (a := psi) (r := r) (G := G)
        (B0 := 1) (B1 := Csh) hSOpsi hrSO hGnn hGint ha0 ha1 hrmem
    have hXn := Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen α hα psi r G
      (B0 := 1) (B1 := Csh) (M1 := M) (by norm_num) hCshpos.le hMpos.le hGnn ha0 ha1
      hGint hm1 hrmem
    rw [hfac]
    refine ⟨hHk, ?_⟩
    calc Work.FTS.Nonlin.Xn α (fun z θ => psi θ * r z)
        ≤ Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M)
            * Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => r z) := hXn
      _ ≤ Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M) * (40 * α ^ 2 * Cr) :=
          mul_le_mul_of_nonneg_left hXnr (Real.sqrt_nonneg _)
      _ = (Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M) * (40 * Cr)) * α ^ 2 := by ring
      _ ≤ (Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M) * (40 * Cr) + 1) * α ^ 2 := by
          have h1 : (0 : ℝ) ≤ Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M) * (40 * Cr) := by
            positivity
          nlinarith [h1, sq_nonneg α]

end Work.FTS.StrongPersist.L3Rhs
