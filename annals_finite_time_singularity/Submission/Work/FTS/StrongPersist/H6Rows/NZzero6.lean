import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.Construction.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.h6pair_N0_zero
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.h6pair_mod
import Submission.Work.FTS.Nonlinear.Pieces.rl1Bound
import Submission.Work.FTS.NonlinRows.Rl1.tools
import Submission.Work.FTS.NonlinRows.Rl1.starUopBound
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Psg
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Acf
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.PertResidPt
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.FstarSlotsFa
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.Slots
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.Decomp
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.NZarith
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.PtBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H6Rows/NZzero6` — the `N`-zero-mode bound `|L₁₂(N)(0)| ≤ K(1+|Ce|+|Cs|)⁴α^{-9}(1+M)⁴`

Elgindi's Proposition `muestimate` (tex 1508--1526) needs the zero mode `L₁₂(N)(0)` of the
nonlinear term `N` of the modulation (`Work.Construction.N`), on the level-six coercivity class
`H6Adm` with the *split* elliptic context `Ell6Ctx`.

## Route

Write `F = F_* + f`, `Ψ = Φs + E f` (`Ell6Ctx.hsum`), `Ξ := PhiTil α F Ψ = Ξ_s + Ξ_p` with
`Ξ_s := PhiTs α Φs`, `Ξ_p := PhiTg α f (E f)` (linearity of `L₁₂` at every `z > 0`,
`NZaux.L12AddFstar`), and group the five terms of `N` by the *slot* `{F, D_θF, D_zF}`:

`N α F Ψ = A₁·F + A₂·D_θF + A₃·D_zF` on the open quadrant, with
`A₁ := 2ℛ(Ξ) - sin²θ·FK F`, `A₂ := -(2𝒰(Ξ)/sin2θ + FK F/2)`, `A₃ := -2α𝒱(Ξ)`

(using `D_θF = sin(2θ)·∂_θF` and `K θ/sin(2θ) = (3/2)cos θ`).  The four majorants
`|ℛ(Ξ)|, |𝒰(Ξ)|, |𝒱(Ξ)|, |FK F| ≤ Kcoef` are `NZaux.NZ_coefs` (where the star parts are priced by
`StarPkgo` and the perturbation parts by `EllPkgGo` + the `ℋ⁴`-Agmon bound
`TransportS.sup_dz_le_hk`, i.e. the paper's Corollary `Linfty`), the pointwise domination of
`|K θ·N|` by the six slots is `NZaux.NZ_pt` (file `NZaux/PtBound.lean`), and the slot bounds
(`FaU f`, `FaU (D_θf)`, `FaU (D_zf)` by `√(π/2)|f|_{ℋ⁴}`, `FAU F_*` etc. by `Cf·α`) plus
`NZaux.Fa_le_slots` (the six-slot additivity of the `L₁₂`-density) give the estimate.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

theorem NZzero6 : ∀ Ce : ℝ, 0 < Ce → ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧ α₂ ≤ 1 ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (f Ψ Φs : Work.FTS.Galerkin.Fn) (M Cs : ℝ)
      (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn),
      Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f →
      Work.FTS.Nonlin.Xn α f ≤ M →
      Work.FTS.StrongPersist.Ell6Ctx α Ce Cs E Φs f Ψ →
      |Work.Construction.L12 (Work.Construction.N α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ) 0|
        ≤ K * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 := by
  intro Ce hCe
  obtain ⟨Cp, hCp0, hCpbd⟩ := NZaux.PertResidPt
  obtain ⟨Cu, hCu0, hCubd⟩ := Work.FTS.NonlinRows.Rl1.starUopBound
  obtain ⟨Cag, hCag0, hCagbd⟩ := Work.FTS.TransportS.sup_dz_le_hk
  obtain ⟨Cf, hCf0, hCfbd⟩ := NZaux.FstarSlotsFa
  set Cp' : ℝ := max Cp 1 with hCp'def
  set Cu' : ℝ := max Cu 1 with hCu'def
  set Cag' : ℝ := max (Cag * 4) 1 with hCag'def
  set Cf' : ℝ := max Cf 1 with hCf'def
  have hCp'0 : 0 < Cp' := lt_of_lt_of_le zero_lt_one (le_max_right Cp 1)
  have hCu'0 : 0 < Cu' := lt_of_lt_of_le zero_lt_one (le_max_right Cu 1)
  have hCag'0 : 0 < Cag' := lt_of_lt_of_le zero_lt_one (le_max_right (Cag * 4) 1)
  have hCf'0 : 0 < Cf' := lt_of_lt_of_le zero_lt_one (le_max_right Cf 1)
  have hCple : Cp ≤ Cp' := le_max_left Cp 1
  have hCule : Cu ≤ Cu' := le_max_left Cu 1
  have hCagle : Cag ≤ Cag' := le_trans (by linarith [hCag0]) (le_max_left (Cag * 4) 1)
  have hCfle : Cf ≤ Cf' := le_max_left Cf 1
  have hApos : 0 < Cp' + Cu' + Cag' + Cf' + 1 := by linarith
  have hBpos : 0 < Real.sqrt (Real.pi / 2) + Cf' := by
    have := Real.sqrt_nonneg (Real.pi / 2); linarith
  have hKpos : 0 < 54000 * (Cp' + Cu' + Cag' + Cf' + 1) * (Real.sqrt (Real.pi / 2) + Cf' + 1) + 1 := by
    have h2 : 0 < Cp' + Cu' + Cag' + Cf' + 1 := by linarith
    have h3 : 0 < Real.sqrt (Real.pi / 2) + Cf' + 1 := by
      have := Real.sqrt_nonneg (Real.pi / 2)
      linarith
    have h4 : 0 < (Cp' + Cu' + Cag' + Cf' + 1) * (Real.sqrt (Real.pi / 2) + Cf' + 1) :=
      mul_pos h2 h3
    nlinarith [h4]
  refine ⟨54000 * (Cp' + Cu' + Cag' + Cf' + 1) * (Real.sqrt (Real.pi / 2) + Cf' + 1) + 1, 1,
    hKpos, one_pos, le_refl 1, ?_⟩
  intro α hα f Ψ Φs M Cs E hreg h7 hM hctx
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hreg.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 f := hreg.reg.2
  have hmem4 : Work.Spaces.HkMem α 4 f := Work.FTS.IPGen.HkMem_mono_le hso 4 (by norm_num) hmem6
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hM
  have hstar : Work.FTS.VocabO.StarPkgo α Cs Φs := hctx.hstar.toStarPkgo
  have hgo : Work.FTS.VocabO.EllPkgGo α Ce f (E f) := hctx.hgo
  -- the pointwise data of the two elliptic packages, with the normalised constants
  have hresR' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Rop α (Work.Construction.PhiTil α f (E f)) z θ|
        ≤ Cp' * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f := by
    intro z θ hz hθ hθ2
    refine le_trans ((hCpbd hα0 hα1 hgo).1 z θ hz hθ hθ2) ?_
    have h0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hα0.le _) hCe.le)
        (Work.Spaces.HkNorm_nonneg α 4 f)
    calc Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f
        = Cp * (α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f) := by ring
      _ ≤ Cp' * (α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f) :=
          mul_le_mul_of_nonneg_right hCple h0
      _ = Cp' * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f := by ring
  have hresU' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ / Work.Construction.s2 θ|
        ≤ Cp' * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f := by
    intro z θ hz hθ hθ2
    refine le_trans ((hCpbd hα0 hα1 hgo).2.1 z θ hz hθ hθ2) ?_
    have h0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hα0.le _) hCe.le)
        (Work.Spaces.HkNorm_nonneg α 4 f)
    calc Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f
        = Cp * (α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f) := by ring
      _ ≤ Cp' * (α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f) :=
          mul_le_mul_of_nonneg_right hCple h0
      _ = Cp' * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f := by ring
  have hresV' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Vop (Work.Construction.PhiTil α f (E f)) z θ|
        ≤ Cp' * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f := by
    intro z θ hz hθ hθ2
    refine le_trans ((hCpbd hα0 hα1 hgo).2.2 z θ hz hθ hθ2) ?_
    have h0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hα0.le _) hCe.le)
        (Work.Spaces.HkNorm_nonneg α 4 f)
    calc Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f
        = Cp * (α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f) := by ring
      _ ≤ Cp' * (α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f) :=
          mul_le_mul_of_nonneg_right hCple h0
      _ = Cp' * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f := by ring
  have hUstar' : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ Cu' * max Cs 0 * α := by
    intro z θ hz hθI
    refine le_trans (hCubd hα0 hα1 hstar z hz θ hθI) ?_
    have h0 : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right Cs 0) hα0.le
    calc Cu * max Cs 0 * α = Cu * (max Cs 0 * α) := by ring
      _ ≤ Cu' * (max Cs 0 * α) := mul_le_mul_of_nonneg_right hCule h0
      _ = Cu' * max Cs 0 * α := by ring
  have hsupf' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |f z θ| ≤ Cag' * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f := by
    intro z θ hz hθ hθ2
    have h := hCagbd α f hα0 hα1 hso hmem4 0 (by norm_num) z θ hz hθ hθ2
    simp only [Work.Spaces.DzIter_zero] at h
    have h0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f :=
      mul_nonneg (Real.rpow_nonneg hα0.le _) (Work.Spaces.HkNorm_nonneg α 4 f)
    have hsqrt := inv_sqrt_gam_sub_one hα0
    have h10 : Real.sqrt 10 ≤ 4 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num), Real.sqrt_nonneg 10]
    have hCag4 : Cag * 4 ≤ Cag' := le_max_left (Cag * 4) 1
    calc |f z θ| ≤ Cag * (Real.sqrt (Work.Spaces.gam α - 1))⁻¹ * Work.FTS.Nonlin.Xn α f := by
          rw [div_eq_mul_inv] at h
          exact h
      _ = Cag * (Real.sqrt 10 * α ^ (-(1 / 2 : ℝ))) * Work.FTS.Nonlin.Xn α f := by rw [hsqrt]
      _ = Cag * Real.sqrt 10 * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f) := by ring
      _ ≤ Cag * 4 * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h10 hCag0.le) h0
      _ ≤ Cag' * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f) :=
          mul_le_mul_of_nonneg_right hCag4 h0
      _ = Cag' * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f := by ring
  -- =============== the four coefficient majorants and the pointwise bound
  have hcoef := NZ_coefs (α := α) (M := M) (Ce := Ce) (Cs := Cs) (f := f) (Ef := E f)
    (Φs := Φs) (Cp := Cp') (Cu := Cu') (Cag := Cag') hα0 hα1 hM0 hCe hso hmem4 h7 hM hstar hgo
    hCp'0 hCu'0 hCag'0 hresR' hresU' hresV' hUstar' hsupf'
  have hpt : ∀ r θ : ℝ, 0 < r → 0 < θ → θ < π / 2 →
      |Work.Spaces.K θ * Work.Construction.N α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + E f z θ) r θ|
        ≤ 9 * Kcoef α M Ce Cs Cp' Cu' Cag' * (∑ j : Fin 6, |slots α f j r θ|) := by
    intro r θ hr hθ hθ2
    obtain ⟨h1, h2, h3, h4⟩ := hcoef r θ hr hθ hθ2
    exact NZ_pt hα0 hα1 hM0 hCp'0 hCu'0 hCag'0 hso hr hθ hθ2 h1 h2 h3 h4
  -- =============== the slot continuity
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hFdth : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth (Work.Construction.Fstar α)) :=
    hFsm.Dth
  have hFdz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz (Work.Construction.Fstar α)) :=
    hFsm.Dz
  have hm : ∀ j : Fin 6, ContinuousOn (Function.uncurry (slots α f j))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    intro j
    fin_cases j <;>
      simp only [slots, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.cons_val]
    · exact hso.continuousOn
    · exact hso.Dth.continuousOn
    · exact hso.Dz.continuousOn
    · exact hFsm.continuousOn
    · exact hFdth.continuousOn
    · exact hFdz.continuousOn
  -- =============== the six slot bounds
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hbound : ∀ j : Fin 6, FaU (slots α f j)
      ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2) * M + Cf' * α) := by
    intro j
    have hc0 : 0 ≤ Real.sqrt (Real.pi / 2) * M + Cf' * α := by
      have h1 := Real.sqrt_nonneg (Real.pi / 2)
      have h2 : 0 ≤ Cf' * α := mul_nonneg hCf'0.le hα0.le
      nlinarith [hM0]
    fin_cases j <;>
      simp only [slots, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.cons_val]
    · refine le_trans (FaU_data_slots hα0 hso hmem4).1 (ENNReal.ofReal_le_ofReal ?_)
      have h1 := Real.sqrt_nonneg (Real.pi / 2)
      have h2 : 0 ≤ Cf' * α := mul_nonneg hCf'0.le hα0.le
      nlinarith [hM, hM0]
    · refine le_trans (FaU_data_slots hα0 hso hmem4).2.1 (ENNReal.ofReal_le_ofReal ?_)
      have h1 := Real.sqrt_nonneg (Real.pi / 2)
      have h2 : 0 ≤ Cf' * α := mul_nonneg hCf'0.le hα0.le
      nlinarith [hM, hM0]
    · refine le_trans (FaU_data_slots hα0 hso hmem4).2.2 (ENNReal.ofReal_le_ofReal ?_)
      have h1 := Real.sqrt_nonneg (Real.pi / 2)
      have h2 : 0 ≤ Cf' * α := mul_nonneg hCf'0.le hα0.le
      nlinarith [hM, hM0]
    · refine le_trans ((hCfbd α hα0 hα1).1) (ENNReal.ofReal_le_ofReal ?_)
      have h1 := Real.sqrt_nonneg (Real.pi / 2)
      have h2 : 0 ≤ Real.sqrt (Real.pi / 2) * M := mul_nonneg h1 hM0
      have h3 : Cf * α ≤ Cf' * α := mul_le_mul_of_nonneg_right hCfle hα0.le
      linarith
    · refine le_trans ((hCfbd α hα0 hα1).2.1) (ENNReal.ofReal_le_ofReal ?_)
      have h1 := Real.sqrt_nonneg (Real.pi / 2)
      have h2 : 0 ≤ Real.sqrt (Real.pi / 2) * M := mul_nonneg h1 hM0
      have h3 : Cf * α ^ 2 ≤ Cf' * α := by
        refine le_trans (mul_le_mul_of_nonneg_left (by nlinarith [hα0, hα1]) hCf0.le)
          (mul_le_mul_of_nonneg_right hCfle hα0.le)
      linarith
    · refine le_trans ((hCfbd α hα0 hα1).2.2) (ENNReal.ofReal_le_ofReal ?_)
      have h1 := Real.sqrt_nonneg (Real.pi / 2)
      have h2 : 0 ≤ Real.sqrt (Real.pi / 2) * M := mul_nonneg h1 hM0
      have h3 : Cf * α ≤ Cf' * α := mul_le_mul_of_nonneg_right hCfle hα0.le
      linarith
  have hslots : (∑ j : Fin 6, FaU (slots α f j))
      ≤ ENNReal.ofReal (6 * (Real.sqrt (Real.pi / 2) * M + Cf' * α)) := by
    refine le_trans (Finset.sum_le_sum (fun j _ => hbound j)) ?_
    have h6 : ((6 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 6 := (ENNReal.ofReal_natCast 6).symm
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, h6,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
  -- =============== the `Fa` bound
  have hFa := Fa_le_slots (Kc := 9 * Kcoef α M Ce Cs Cp' Cu' Cag')
    (N := Work.Construction.N α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
      (fun z θ => Φs z θ + E f z θ)) (G := slots α f)
    (by
      have h : (0 : ℝ) < Kcoef α M Ce Cs Cp' Cu' Cag' :=
        Kcoef_pos hα0 hCp'0 hCu'0 hCag'0 hM0
      linarith) hpt hm
  have hFa2 : Fa (Work.Construction.N α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
        (fun z θ => Φs z θ + E f z θ))
      ≤ ENNReal.ofReal (9 * Kcoef α M Ce Cs Cp' Cu' Cag'
          * (6 * (Real.sqrt (Real.pi / 2) * M + Cf' * α))) := by
    refine le_trans hFa ?_
    have hA0 : (0 : ℝ) ≤ 9 * Kcoef α M Ce Cs Cp' Cu' Cag' := by
      have h : (0 : ℝ) < Kcoef α M Ce Cs Cp' Cu' Cag' :=
        Kcoef_pos hα0 hCp'0 hCu'0 hCag'0 hM0
      linarith
    have hof : ENNReal.ofReal (9 * Kcoef α M Ce Cs Cp' Cu' Cag'
          * (6 * (Real.sqrt (Real.pi / 2) * M + Cf' * α)))
        = ENNReal.ofReal (9 * Kcoef α M Ce Cs Cp' Cu' Cag')
          * ENNReal.ofReal (6 * (Real.sqrt (Real.pi / 2) * M + Cf' * α)) :=
      ENNReal.ofReal_mul hA0
    rw [hof]
    exact mul_le_mul_of_nonneg_left hslots
      (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (9 * Kcoef α M Ce Cs Cp' Cu' Cag'))
  -- =============== the quantitative conclusion
  have hKbadge0 : 0 ≤ (54000 * (Cp' + Cu' + Cag' + Cf' + 1)
      * (Real.sqrt (Real.pi / 2) + Cf' + 1) + 1) * (1 + |Ce| + |Cs|) ^ 4
      * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 := by
    have h1 : (0 : ℝ) ≤ 54000 * (Cp' + Cu' + Cag' + Cf' + 1)
        * (Real.sqrt (Real.pi / 2) + Cf' + 1) + 1 := hKpos.le
    have h2 : (0 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
    have h3 : (0 : ℝ) ≤ α ^ (-(9 : ℝ)) := Real.rpow_nonneg hα0.le _
    have h4 : (0 : ℝ) ≤ (1 + M) ^ 4 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
  have hL12 := Work.FTS.Nonlinear.Pieces.ofReal_L12_le
    (Work.Construction.N α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
      (fun z θ => Φs z θ + E f z θ))
  have hbig : ENNReal.ofReal |Work.Construction.L12 (Work.Construction.N α
        (fun z θ => Work.Construction.Fstar α z θ + f z θ)
        (fun z θ => Φs z θ + E f z θ)) 0|
      ≤ ENNReal.ofReal ((54000 * (Cp' + Cu' + Cag' + Cf' + 1)
          * (Real.sqrt (Real.pi / 2) + Cf' + 1) + 1) * (1 + |Ce| + |Cs|) ^ 4
          * α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by
    refine le_trans hL12 (le_trans hFa2 ?_)
    exact ENNReal.ofReal_le_ofReal
      (NZ_arith hα0 hα1 hM0 hCf'0 hCp'0 hCu'0 hCag'0)
  exact (ENNReal.ofReal_le_ofReal_iff hKbadge0).mp (by
    rw [hctx.hsum]
    exact hbig)

end Work.FTS.StrongPersist.H6Rows
