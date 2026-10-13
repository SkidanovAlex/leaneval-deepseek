import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB4.near0Aux
import Submission.Work.FTS_StreamBdry.SB4.psiP_lipschitz
import Submission.Work.FTS_StreamBdry.SB4.abs_deriv_le_of_lipschitzOn_Ioc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB4.near0Core` — the SB4 assembly for one slice

`near0_core`: from the `D_z`-bounds of the elliptic summand `PhiTil αG f (E f)` and of `Theta αG f`
(`hφ3`, `hφ4`), the `C²`-regularity of `L12` on the slice (`hL12`) and the star package, the SB4
bound `|D_z psiP αG Ψ| ≤ K·z·sin 2θ` holds for the canonical slice `Ψ = slice (PsiCan Φs E g) τ`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB4

set_option maxHeartbeats 800000

/-! ## §5 The assembly for one slice -/

/-- **The core assembly**: from the `D_z`-bounds of the elliptic and `Θ(f)` summands and the
`C²`-regularity of `L12` on the slice, the SB4 bound holds for the canonical slice at `τ`. -/
theorem near0_core {a C₀ Cs : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hStar : Work.FTS.VocabO2.StarPkgo2 (Work.FTS.Regularity.pExp a) Cs Φs)
    (hEL : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp a) E)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g)
    (hL12 : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) w)
        (-(Work.Construction.L12dens (Work.FTS.Galerkin.slice g τ) z)) z ∧
      DifferentiableAt ℝ (fun w => Work.Construction.L12dens (Work.FTS.Galerkin.slice g τ) w) z)
    (hφ3 : ∀ τ : ℝ, 0 ≤ τ → ∃ K : ℝ, 0 ≤ K ∧ ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      z ≤ 1 →
      |Work.Spaces.Dz (fun z θ => Work.FTS.StreamBdryIface.Uprime (Work.FTS.Regularity.pExp a)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp a) (Work.FTS.Galerkin.slice g τ)
          (E (Work.FTS.Galerkin.slice g τ))) z θ) z θ| ≤ K * z)
    (hφ4 : ∀ τ : ℝ, 0 ≤ τ → ∃ K : ℝ, 0 ≤ K ∧ ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      z ≤ 1 →
      |Work.Spaces.Dz (fun z θ => Work.FTS.StreamBdryIface.Uprime (Work.FTS.Regularity.pExp a)
        (Work.Construction.Theta (Work.FTS.Regularity.pExp a) (Work.FTS.Galerkin.slice g τ))
          z θ) z θ| ≤ K * z) :
    ∀ τ, 0 ≤ τ → ∃ K : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd → z ≤ 1 →
      |Work.Spaces.DzIter 1 (Work.FTS.StreamBdryIface.psiP (Work.FTS.Regularity.pExp a)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ)) z θ|
        ≤ K * z * Work.Construction.s2 θ := by
  intro τ hτ
  set αG := Work.FTS.Regularity.pExp a with hαGdef
  have hαG : 0 < αG := by rw [hαGdef]; show (0 : ℝ) < 3 * a; linarith
  have hαG1 : αG ≤ 1 := by rw [hαGdef]; show (3 : ℝ) * a ≤ 1; linarith
  -- abbreviations
  set f : ℝ → ℝ → ℝ := Work.FTS.Galerkin.slice g τ with hfdef
  set Ψ : ℝ → ℝ → ℝ := Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ with hΨdef
  -- the star summand is smooth
  have hsm1 : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs αG Φs) :=
    (Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs hαG hαG1 hStar.smooth).1
  -- the elliptic summand is `C³`
  obtain ⟨gn, B, L, hC, hLc, hjet, hmu⟩ := hOK.2 (τ + 1) (by linarith)
  have hCτ : ∀ n, Work.FTS.ClassC.ClassC αG (Work.FTS.Galerkin.slice (gn n) τ) :=
    fun n => (hC n τ ⟨hτ, by linarith⟩).1
  have hBτ : ∀ n, Work.FTS.StrongGlobal.Xn6 αG (Work.FTS.Galerkin.slice (gn n) τ) ≤ B :=
    fun n => (hC n τ ⟨hτ, by linarith⟩).2.2
  have hf4 : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
      Work.FTS.EllipticEst.Q0 := hOK.1.1.c4 τ hτ
  have hjetτ : ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z θ)
        Filter.atTop (𝓝 (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ)) :=
    fun j i hji z θ hzθ => hjet τ ⟨hτ, by linarith⟩ j i hji z θ hzθ
  obtain ⟨-, hEf3, -⟩ := hEL (fun n => Work.FTS.Galerkin.slice (gn n) τ)
    (Work.FTS.Galerkin.slice g τ) B hCτ hBτ hf4 hjetτ
  -- radial differentiability of the two elementary summands of `ΦTil αG f (E f)`
  have hEf_diff : ∀ w θ : ℝ, (w, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun w' => E (Work.FTS.Galerkin.slice g τ) w' θ) w := by
    intro w θ hwθ
    have hslice : ContDiffOn ℝ 3 (fun w' => E (Work.FTS.Galerkin.slice g τ) w' θ) (Set.Ioi 0) :=
      Work.FTS.StrongEps.EComparison.contDiffOn_slice_z
        ⟨hwθ.2.1, hwθ.2.2⟩ hEf3
    exact (hslice.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hwθ.1)
  have hEf_pz_diff : ∀ w θ : ℝ, (w, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun w' => Work.Spaces.pz (E (Work.FTS.Galerkin.slice g τ)) w' θ) w :=
    fun w θ hwθ => near0_diff_pz_of_joint ⟨hwθ.2.1, hwθ.2.2⟩ hwθ.1 hEf3
  have hTh_diff : ∀ w θ : ℝ, (w, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun w' => Work.Construction.Theta αG
        (Work.FTS.Galerkin.slice g τ) w' θ) w :=
    fun w θ hwθ =>
      (near0_hasDerivAt_Theta (αG := αG) ((hL12 τ hτ w hwθ.1).1.differentiableAt)).differentiableAt
  have hTh_pz_diff : ∀ w θ : ℝ, (w, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun w' => Work.Spaces.pz (Work.Construction.Theta αG
        (Work.FTS.Galerkin.slice g τ)) w' θ) w :=
    fun w θ hwθ => near0_diff_pz_Theta hwθ.1 (fun w' hw' => (hL12 τ hτ w' hw').1)
      (fun w' hw' => (hL12 τ hτ w' hw').2)
  -- radial differentiability of the `U`-slot of the elliptic summand
  have hdiff3 : ∀ w θ : ℝ, (w, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun w' => Work.FTS.StreamBdryIface.Uprime αG
        (Work.Construction.PhiTil αG (Work.FTS.Galerkin.slice g τ)
          (E (Work.FTS.Galerkin.slice g τ))) w' θ) w := by
    intro w θ hwθ
    have hdPhi : DifferentiableAt ℝ (fun w' => Work.Construction.PhiTil αG
        (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ)) w' θ) w := by
      have h := (hEf_diff w θ hwθ).sub (hTh_diff w θ hwθ)
      have hfun : ((fun w' => E (Work.FTS.Galerkin.slice g τ) w' θ)
            - fun w' => Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ) w' θ)
          = (fun w' => Work.Construction.PhiTil αG (Work.FTS.Galerkin.slice g τ)
              (E (Work.FTS.Galerkin.slice g τ)) w' θ) := by
        funext w'; simp only [Pi.sub_apply, Work.Construction.PhiTil]
      rw [hfun] at h
      exact h
    have hpzPhi : DifferentiableAt ℝ (fun w' => Work.Spaces.pz (Work.Construction.PhiTil αG
        (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) w' θ) w := by
      have hev : (fun w' => Work.Spaces.pz (Work.Construction.PhiTil αG
            (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) w' θ)
          =ᶠ[𝓝 w] (fun w' => Work.Spaces.pz (E (Work.FTS.Galerkin.slice g τ)) w' θ
            - Work.Spaces.pz (Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ)) w' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hwθ.1] with w' hw'
        simp only [Work.Spaces.pz, Work.Construction.PhiTil]
        have hfun : (fun z' => E (Work.FTS.Galerkin.slice g τ) z' θ
              - Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ) z' θ)
            = (fun z' => E (Work.FTS.Galerkin.slice g τ) z' θ)
              - fun z' => Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ) z' θ := by
          funext z'; simp only [Pi.sub_apply]
        rw [hfun, deriv_sub (hEf_diff w' θ ⟨hw', hwθ.2.1, hwθ.2.2⟩)
          (hTh_diff w' θ ⟨hw', hwθ.2.1, hwθ.2.2⟩)]
      exact (hev.differentiableAt_iff).mpr ((hEf_pz_diff w θ hwθ).sub (hTh_pz_diff w θ hwθ))
    have hA : DifferentiableAt ℝ (fun w' : ℝ => αG * w') w :=
      differentiableAt_id.const_mul αG
    have h3 : DifferentiableAt ℝ (fun w' : ℝ => -3 * Work.Construction.PhiTil αG
        (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ)) w' θ
        - αG * w' * Work.Spaces.pz (Work.Construction.PhiTil αG (Work.FTS.Galerkin.slice g τ)
          (E (Work.FTS.Galerkin.slice g τ))) w' θ) w :=
      (hdPhi.const_mul (-3)).sub (hA.mul hpzPhi)
    simpa only [Work.FTS.StreamBdryIface.Uprime, Work.Construction.Uop] using
      h3.div_const (Work.Construction.s2 θ)
  -- the four Lipschitz constants
  obtain ⟨C1, hC1nn, hC1⟩ := near0_lip_star ha ha13 hStar
  obtain ⟨C3, hC3nn, hC3⟩ := hφ3 τ hτ
  obtain ⟨C4, hC4nn, hC4⟩ := hφ4 τ hτ
  have hC3' : ∀ z ∈ Set.Ioc 0 1, ∀ z' ∈ Set.Ioc 0 1, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.FTS.StreamBdryIface.Uprime αG (Work.Construction.PhiTil αG
          (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ
        - Work.FTS.StreamBdryIface.Uprime αG (Work.Construction.PhiTil αG
          (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z' θ|
        ≤ C3 * |z - z'| :=
    near0_lip_of_dz_bound hC3nn hdiff3 fun w θ hwθ hwle => hC3 w θ hwθ hwle
  have hC4' : ∀ z ∈ Set.Ioc 0 1, ∀ z' ∈ Set.Ioc 0 1, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.FTS.StreamBdryIface.Uprime αG
          (Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ)) z θ
        - Work.FTS.StreamBdryIface.Uprime αG
          (Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ)) z' θ|
        ≤ C4 * |z - z'| :=
    near0_lip_of_dz_bound hC4nn (fun w θ hwθ => by
        have hA : DifferentiableAt ℝ (fun w' : ℝ => αG * w') w :=
          differentiableAt_id.const_mul αG
        have h3 : DifferentiableAt ℝ (fun w' : ℝ => -3 * Work.Construction.Theta αG
            (Work.FTS.Galerkin.slice g τ) w' θ
            - αG * w' * Work.Spaces.pz (Work.Construction.Theta αG
              (Work.FTS.Galerkin.slice g τ)) w' θ) w :=
          ((hTh_diff w θ hwθ).const_mul (-3)).sub (hA.mul (hTh_pz_diff w θ hwθ))
        simpa only [Work.FTS.StreamBdryIface.Uprime, Work.Construction.Uop] using
          h3.div_const (Work.Construction.s2 θ))
      fun w θ hwθ hwle => hC4 w θ hwθ hwle
  -- the constant of the `Θ(F_*)` summand
  have hC2 := near0_lip_theta_fstar hαG hαG1
  -- additivity of the `U`-slot over the four summands
  have hLstar : ∀ z : ℝ, 0 < z → DifferentiableAt ℝ
      (fun w => Work.Construction.L12 (Work.Construction.Fstar αG) w) z := by
    intro z hz
    have hev : (fun w => Work.Construction.L12 (Work.Construction.Fstar αG) w)
        =ᶠ[𝓝 z] (fun w => 2 * αG / (1 + w)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact Work.Construction.L12_Fstar_eq hαG hαG1 hw.le
    have hd : DifferentiableAt ℝ (fun w : ℝ => 2 * αG / (1 + w)) z :=
      (differentiableAt_const (2 * αG)).div (differentiableAt_const 1 |>.add differentiableAt_id)
        (by positivity)
    exact (hev.differentiableAt_iff).mpr hd
  have hadd : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.FTS.StreamBdryIface.Uprime αG (Work.FTS.Galerkin.slice
          (Work.FTS.Nonlin.PsiCan Φs E g) τ) z θ
        = Work.FTS.StreamBdryIface.Uprime αG (Work.FTS.Nonlin.PhiTs αG Φs) z θ
          + Work.FTS.StreamBdryIface.Uprime αG
              (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z θ
          + Work.FTS.StreamBdryIface.Uprime αG (Work.Construction.PhiTil αG
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ
          + Work.FTS.StreamBdryIface.Uprime αG
              (Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ)) z θ := by
    intro z θ hzθ
    have hθm : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hzθ.2.1, hzθ.2.2⟩
    have hd1 : HasDerivAt (fun w => Work.FTS.Nonlin.PhiTs αG Φs w θ)
        (Work.Spaces.pz (Work.FTS.Nonlin.PhiTs αG Φs) z θ) z :=
      hsm1.hasDerivAt_slice hθm hzθ.1
    have hd2 : HasDerivAt (fun w => Work.Construction.Theta αG
        (Work.Construction.Fstar αG) w θ)
        (Work.Spaces.pz (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z θ) z :=
      near0_hasDerivAt_Theta (hLstar z hzθ.1)
    have hd3 : HasDerivAt (fun w => Work.Construction.PhiTil αG (Work.FTS.Galerkin.slice g τ)
        (E (Work.FTS.Galerkin.slice g τ)) w θ)
        (Work.Spaces.pz (Work.Construction.PhiTil αG (Work.FTS.Galerkin.slice g τ)
          (E (Work.FTS.Galerkin.slice g τ))) z θ) z := by
      have hsub := (hEf_diff z θ hzθ).hasDerivAt.sub (hTh_diff z θ hzθ).hasDerivAt
      have hval : Work.Spaces.pz (Work.Construction.PhiTil αG (Work.FTS.Galerkin.slice g τ)
            (E (Work.FTS.Galerkin.slice g τ))) z θ
          = Work.Spaces.pz (E (Work.FTS.Galerkin.slice g τ)) z θ
            - Work.Spaces.pz (Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ)) z θ := by
        simp only [Work.Spaces.pz, Work.Construction.PhiTil]
        have hfun : (fun z' => E (Work.FTS.Galerkin.slice g τ) z' θ
              - Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ) z' θ)
            = (fun z' => E (Work.FTS.Galerkin.slice g τ) z' θ)
              - fun z' => Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ) z' θ := by
          funext z'; simp only [Pi.sub_apply]
        rw [hfun, deriv_sub (hEf_diff z θ hzθ) (hTh_diff z θ hzθ)]
      rw [hval]
      have hfun : ((fun w' => E (Work.FTS.Galerkin.slice g τ) w' θ)
            - fun w' => Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ) w' θ)
          = (fun w' => Work.Construction.PhiTil αG (Work.FTS.Galerkin.slice g τ)
              (E (Work.FTS.Galerkin.slice g τ)) w' θ) := by
        funext w'; simp only [Pi.sub_apply, Work.Construction.PhiTil]
      rw [hfun] at hsub
      exact hsub
    have hd4 : HasDerivAt (fun w => Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ) w θ)
        (Work.Spaces.pz (Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ)) z θ) z :=
      near0_hasDerivAt_Theta ((hL12 τ hτ z hzθ.1).1.differentiableAt)
    have hderiv : deriv (fun w => Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ w θ) z
        = Work.Spaces.pz (Work.FTS.Nonlin.PhiTs αG Φs) z θ
          + Work.Spaces.pz (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z θ
          + Work.Spaces.pz (Work.Construction.PhiTil αG (Work.FTS.Galerkin.slice g τ)
              (E (Work.FTS.Galerkin.slice g τ))) z θ
          + Work.Spaces.pz (Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ)) z θ := by
      have hfun : (fun w => Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ w θ)
          = (((fun w => Work.FTS.Nonlin.PhiTs αG Φs w θ)
              + fun w => Work.Construction.Theta αG (Work.Construction.Fstar αG) w θ)
              + fun w => Work.Construction.PhiTil αG (Work.FTS.Galerkin.slice g τ)
                  (E (Work.FTS.Galerkin.slice g τ)) w θ)
              + fun w => Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ) w θ := by
        funext w
        simp only [Pi.add_apply, Work.FTS.Galerkin.slice, Work.FTS.Nonlin.PsiCan,
          Work.FTS.Nonlin.PhiTs, Work.Construction.PhiTil]
        ring
      rw [hfun, (((hd1.add hd2).add hd3).add hd4).deriv]
    rw [Work.FTS.StreamBdryIface.Uprime, Work.Construction.Uop, Work.Spaces.pz, hderiv]
    simp only [Work.FTS.Galerkin.slice, Work.FTS.Nonlin.PsiCan, Work.FTS.Nonlin.PhiTs,
      Work.Construction.PhiTil, Work.Construction.Theta, Work.FTS.StreamBdryIface.Uprime,
      Work.Construction.Uop, Work.Spaces.pz]
    ring
  -- the Lipschitz bound of `U'(Ψ)`
  have hU : ∀ z ∈ Set.Ioc 0 1, ∀ z' ∈ Set.Ioc 0 1, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.StreamBdryIface.Uprime αG Ψ z θ - Work.FTS.StreamBdryIface.Uprime αG Ψ z' θ|
        ≤ ((C1 + 2) + C3 + C4) * |z - z'| := by
    intro z hz z' hz' θ hθ
    have hCtot : (0 : ℝ) ≤ ((C1 + 2) + C3 + C4) := by linarith
    rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
    · rcases lt_or_eq_of_le hθ.2 with hθ2 | hθ2
      · have hzq : (z, θ) ∈ Work.Construction.Qd := ⟨hz.1, hθ0, hθ2⟩
        have hzq' : (z', θ) ∈ Work.Construction.Qd := ⟨hz'.1, hθ0, hθ2⟩
        have h1 := hadd z θ hzq
        have h2 := hadd z' θ hzq'
        rw [h1, h2]
        set a1 := Work.FTS.StreamBdryIface.Uprime αG (Work.FTS.Nonlin.PhiTs αG Φs) z θ with ha1
        set b1 := Work.FTS.StreamBdryIface.Uprime αG (Work.FTS.Nonlin.PhiTs αG Φs) z' θ with hb1
        set a2 := Work.FTS.StreamBdryIface.Uprime αG
          (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z θ with ha2
        set b2 := Work.FTS.StreamBdryIface.Uprime αG
          (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z' θ with hb2
        set a3 := Work.FTS.StreamBdryIface.Uprime αG (Work.Construction.PhiTil αG
          (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ with ha3
        set b3 := Work.FTS.StreamBdryIface.Uprime αG (Work.Construction.PhiTil αG
          (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z' θ with hb3
        set a4 := Work.FTS.StreamBdryIface.Uprime αG
          (Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ)) z θ with ha4
        set b4 := Work.FTS.StreamBdryIface.Uprime αG
          (Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ)) z' θ with hb4
        have e1 : |a1 - b1| ≤ C1 * |z - z'| := hC1 z hz z' hz' θ hθ
        have e2 : |a2 - b2| ≤ 2 * |z - z'| := hC2 z hz z' hz' θ hθ
        have e3 : |a3 - b3| ≤ C3 * |z - z'| := hC3' z hz z' hz' θ ⟨hθ0, hθ2⟩
        have e4 : |a4 - b4| ≤ C4 * |z - z'| := hC4' z hz z' hz' θ ⟨hθ0, hθ2⟩
        have hzznn : (0:ℝ) ≤ |z - z'| := abs_nonneg _
        calc |(a1 + a2 + a3 + a4) - (b1 + b2 + b3 + b4)|
            = |(a1 - b1) + (a2 - b2) + (a3 - b3) + (a4 - b4)| := by ring_nf
          _ ≤ |a1 - b1| + |a2 - b2| + |a3 - b3| + |a4 - b4| := by
              have h := abs_add_le ((a1 - b1) + (a2 - b2) + (a3 - b3)) (a4 - b4)
              have h' := abs_add_le ((a1 - b1) + (a2 - b2)) (a3 - b3)
              have h'' := abs_add_le (a1 - b1) (a2 - b2)
              linarith
          _ ≤ ((C1 + 2) + C3 + C4) * |z - z'| := by linarith
      · have h0 : Work.Construction.s2 θ = 0 := by
          rw [Work.Construction.s2_eq, hθ2, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        simp only [Work.FTS.StreamBdryIface.Uprime, h0, div_zero, sub_zero, abs_zero]
        exact mul_nonneg hCtot (abs_nonneg _)
    · have h0 : Work.Construction.s2 θ = 0 := by
        rw [← hθ0, Work.Construction.s2_eq, show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
      simp only [Work.FTS.StreamBdryIface.Uprime, h0, div_zero, sub_zero, abs_zero]
      exact mul_nonneg hCtot (abs_nonneg _)
  -- the `psiP`-Lipschitz bound and the derivative bound
  have hCtot : (0 : ℝ) ≤ (C1 + 2) + C3 + C4 := by linarith
  obtain ⟨K, hK⟩ := psiP_lipschitz hαG hCtot hU
  refine ⟨((C1 + 2) + C3 + C4) / (3 + αG), ?_⟩
  intro z θ hzθ hz1
  have hθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hzθ.2.1, le_of_lt hzθ.2.2⟩
  obtain ⟨hKval, hKlip⟩ := hK θ hθ
  have habs := abs_deriv_le_of_lipschitzOn_Ioc hKlip z ⟨hzθ.1, hz1⟩
  rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz, Work.Spaces.pz, hΨdef]
  rw [abs_mul, abs_of_pos hzθ.1]
  have hs2nn : 0 ≤ Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_nonneg_of_Iθ hθ
  rw [hKval] at habs
  have : z * |deriv (fun z' => Work.FTS.StreamBdryIface.psiP αG
      (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) z' θ) z|
      ≤ z * (Work.Construction.s2 θ * ((C1 + 2) + C3 + C4) / (3 + αG)) :=
    mul_le_mul_of_nonneg_left habs hzθ.1.le
  refine le_trans this (le_of_eq ?_)
  ring


end Work.FTS_StreamBdry.SB4
