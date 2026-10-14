import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.dzdIter_FK_eq_qang
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Assembly6
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.SolutionDelivery.DatumEuler
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row21 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The factorisation of the piece -/

/-- **`N₄^{g*}` is the product of the angular profile `A` and the radial function `FK g · hKer`.**
Unconditional (no regularity hypothesis is used): it is the algebra
`∂_θF_*(z,θ) = (α·F_*'(z)/c α)·Γ'(θ)`, `F_*'(z) = 2 hKer z`, `D_θΓ = sin(2θ)Γ'`. -/
theorem N4gs_factor (α : ℝ) (g : Work.FTS.Galerkin.Fn) :
    Work.FTS.Nonlin.N4gs α g = fun z θ =>
      (-(α / Work.Spaces.c α) * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ)
        * (Work.Construction.FK g z * Work.Spaces.hKer z) := by
  funext z θ
  rw [Work.FTS.Nonlin.N4gs, Work.Construction.s2]
  have hpth : Work.Spaces.pth (Work.Construction.Fstar α) z θ
      = (α * Work.FM.Fstar z / Work.Spaces.c α)
          * deriv (fun t => Work.Spaces.Gam α t) θ := by
    rw [Work.Spaces.pth]
    rw [show (fun θ' => Work.Construction.Fstar α z θ')
        = fun θ' => (α * Work.FM.Fstar z / Work.Spaces.c α) * Work.Spaces.Gam α θ' from by
      funext θ'; rw [Work.Construction.Fstar]; ring]
    rw [Work.Spaces.deriv_const_mul']
  rw [hpth, Work.Spaces.dthU_apply, Work.Spaces.hKer_apply, Work.FM.Fstar]
  ring

/-! ## The angular profile `A = -(α/c)·D_θΓ` against a radial function -/


/-! ## Auxiliary facts about the radial profile `hKer` -/






/-! ## The Leibniz rule for the product `Qang g 0 · hKer` -/



/-! ## The smoothness shift `f ↦ Dzd f` -/




/-! ## The product bound -/



end Work.FTS.Nonlinear.Pieces.RNP
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row24 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option linter.unusedVariables false

open scoped Real Topology
open MeasureTheory Set Filter

/-! ### Helper 1: the integration step of the radial product estimate

If the `ℋ⁴`-integrand of `R·h` is pointwise dominated (a.e. in `θ`, for every `z > 0`) by
`C·(M·HkIntegrand h + (D_z⁴R)²w²·smE·Qg h)`, then integrating in `(θ,z)` gives
`HkSq (R·h) ≤ C·(M + ∫_z (D_z⁴R)²w²)·HkSq h`. -/

/-! ### Helper 2: the `angmul` interface applied to the scaled profile `c·(-sin²θ)` -/


/-! ### Helper 3: the bound on the `D_z⁴`-slot of the radial factor -/



/-! ### Helper 4: the uniform sup bound for the `D_z`-iterates of the radial factor -/


/-! ### Helper 5: the main assembly (conditional on the two remaining interfaces) -/



end Work.FTS.Nonlinear.Pieces.RNP
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row25 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-! ## `D_z`-iterates of a `C^n` function on `(0,∞)` -/

/-- **`DzdIter b u` is `C^{n-b}` when `u` is `C^n` on `(0,∞)`.**  The proof is the induction on
`b`: `DzdIter (b+1) u = z·(DzdIter b u)'`, the derivative lowers the order by one
(`ContDiffOn.derivWithin`) and multiplication by `z` is `C^∞`. -/
theorem contDiffOn_dzdIter_of {n : ℕ} {u : ℝ → ℝ} (hu : ContDiffOn ℝ n u (Set.Ioi 0)) :
    ∀ b : ℕ, b ≤ n →
      ContDiffOn ℝ (n - b) (Work.Elliptic.DzdIter b u) (Set.Ioi 0) := by
  intro b
  induction b with
  | zero =>
      intro _
      simpa using hu
  | succ b ih =>
      intro hb
      have hb' : b ≤ n := by omega
      have hcast : ((n - b : ℕ) : WithTop ℕ∞) = ((n - (b + 1) : ℕ) : WithTop ℕ∞) + 1 := by
        have h : n - b = (n - (b + 1)) + 1 := by omega
        rw [h, Nat.cast_add, Nat.cast_one]
      have h1 : ContDiffOn ℝ ((n - b : ℕ) : WithTop ℕ∞) (Work.Elliptic.DzdIter b u)
          (Set.Ioi 0) := ih hb'
      have h2 : ContDiffOn ℝ ((n - (b + 1) : ℕ) : WithTop ℕ∞)
          (deriv (Work.Elliptic.DzdIter b u)) (Set.Ioi 0) := by
        have hd := h1.derivWithin (isOpen_Ioi.uniqueDiffOn (𝕜 := ℝ))
          (m := ((n - (b + 1) : ℕ) : WithTop ℕ∞)) (by rw [← hcast])
        exact hd.congr (fun x hx => (derivWithin_of_isOpen isOpen_Ioi hx).symm)
      have h3 : ContDiffOn ℝ ((n - (b + 1) : ℕ) : WithTop ℕ∞)
          (fun z : ℝ => z * deriv (Work.Elliptic.DzdIter b u) z) (Set.Ioi 0) :=
        contDiffOn_id.mul h2
      rw [Work.Elliptic.DzdIter_succ]
      exact h3

/-! ## Differentiability of the `D_z`-iterates of the angular moment `FK g` -/


/-! ## The angular-profile bound `|D_θ^i(sin²θ·Γ(θ))| ≤ B·sin(2θ)^{α/5}` -/

/-- **The `D_θ`-iterates of `sin²θ·Γ(θ)` are bounded by `B·sin(2θ)^{α/5}`.**  The profile
`sin²θ·Γ(θ)` is the angular factor of `N₅^{gs}` (through `F_* = α(Γ/c)·2z/(1+z)²`).  The proof
is the Leibniz rule for `dthU` on the open interval (`dthU_iter_mul_Ioo`, applied to
`sin²·Γ`), the sharp bound `|dthU^j Γ| ≤ 100000·α·Γ` (`dthU_iter_Gam_abs_bound` +
`Tfun_abs_le`) together with `Γ ≤ sin(2θ)^{α/5}` (`Gam_le_sin_two_rpow`), and the bound
`|dthU^a(sin²)| ≤ B·sin(2θ)` of `angProfile_sinSq`.  At the two endpoints both sides vanish. -/
theorem dthSinSqGam_le : ∃ B : ℝ, 0 < B ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') 0 θ|
        ≤ B * (Real.sin (2 * θ)) ^ (α / 5) := by
  obtain ⟨Bs, hBspos, -, hSinLe, hSinDth⟩ :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
  refine ⟨16 * (100000 + Bs * 100000) + 1, by positivity, ?_⟩
  intro α hα hα1 i hi1 hi4 θ hθ
  have hsnn : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsα : 0 ≤ (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_nonneg hsnn _
  have hsle : Real.sin (2 * θ) ≤ (Real.sin (2 * θ)) ^ (α / 5) := by
    rcases eq_or_lt_of_le hsnn with h0 | h0
    · rw [← h0, Real.zero_rpow (by positivity : α / 5 ≠ 0)]
    · have hle : α / 5 ≤ 1 := by linarith
      have h := Real.rpow_le_rpow_of_exponent_ge (x := Real.sin (2 * θ)) (y := (1 : ℝ))
        (z := α / 5) h0 hs1 hle
      simpa using h
  have hGam : Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) :=
    Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθ
  have hαGam : α * Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) := by
    calc α * Work.Spaces.Gam α θ
        ≤ α * (Real.sin (2 * θ)) ^ (α / 5) := mul_le_mul_of_nonneg_left hGam hα.le
      _ ≤ 1 * (Real.sin (2 * θ)) ^ (α / 5) := mul_le_mul_of_nonneg_right hα1 hsα
      _ = (Real.sin (2 * θ)) ^ (α / 5) := one_mul _
  have hT : ∀ j : ℕ, j ≤ 4 → ∀ θ' ∈ Work.Spaces.Iθ,
      |Work.Spaces.Tfun (j - 1) α θ'| ≤ 100000 :=
    fun j hj θ' _ => Work.FTS.LocData.Tfun_abs_le (j - 1) (by omega) α hα hα1 θ'
  have hGamJ : ∀ j : ℕ, 1 ≤ j → j ≤ 4 →
      |Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t) θ|
        ≤ 100000 * (Real.sin (2 * θ)) ^ (α / 5) := by
    intro j hj hj4
    have h := Work.Spaces.dthU_iter_Gam_abs_bound j hj α hα 100000 (hT j hj4) θ hθ
    calc |Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * 100000 * Work.Spaces.Gam α θ := h
      _ = 100000 * (α * Work.Spaces.Gam α θ) := by ring
      _ ≤ 100000 * (Real.sin (2 * θ)) ^ (α / 5) :=
          mul_le_mul_of_nonneg_left hαGam (by norm_num)
  have hSin1 : ∀ a : ℕ, 1 ≤ a → a ≤ 4 →
      |Work.Spaces.dthU^[a] (fun θ' => Real.sin θ' ^ 2) θ| ≤ Bs * Real.sin (2 * θ) := by
    intro a ha ha4
    have h := hSinDth a ha ha4 θ hθ
    have hconv : Work.Spaces.DthIter a (fun _ (θ' : ℝ) => -(Real.sin θ' ^ 2)) 0 θ
        = -(Work.Spaces.dthU^[a] (fun θ' => Real.sin θ' ^ 2) θ) := by
      rw [Work.FTS.LocData.DthIter_rad_eq a (fun θ' => -(Real.sin θ' ^ 2)) 0 θ]
      have h2 := congrFun (Work.Spaces.dthU_iter_const_mul a (-1)
        (fun θ' => Real.sin θ' ^ 2)) θ
      simpa using h2
    rw [hconv, abs_neg] at h
    exact h
  -- the endpoint cases
  rcases eq_or_lt_of_le hθ.1 with h0 | h0pos
  · subst h0
    have hzero : Work.Spaces.DthIter i
        (fun _ (θ' : ℝ) => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') 0 0 = 0 := by
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi1)
      subst hj
      simp [Work.Spaces.DthIter_succ, Work.Spaces.Dth]
    rw [hzero]
    norm_num [Real.zero_rpow (show α / 5 ≠ 0 by positivity)]
  · rcases eq_or_lt_of_le hθ.2 with hpi | hpilt
    · subst hpi
      have h2pi : 2 * (Real.pi / 2) = Real.pi := by ring
      have hzero : Work.Spaces.DthIter i
          (fun _ (θ' : ℝ) => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') 0 (Real.pi / 2) = 0 := by
        obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi1)
        subst hj
        simp [Work.Spaces.DthIter_succ, Work.Spaces.Dth, h2pi, Real.sin_pi]
      have hs0 : Real.sin (2 * (Real.pi / 2)) = 0 := by rw [h2pi, Real.sin_pi]
      rw [hzero, hs0]
      norm_num [Real.zero_rpow (show α / 5 ≠ 0 by positivity)]
    · -- the interior: the Leibniz rule and the term-by-term bounds
      have hioo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h0pos, hpilt⟩
      have hsmith : ContDiffOn ℝ ⊤ (fun θ' : ℝ => Real.sin θ' ^ 2)
          (Set.Ioo 0 (Real.pi / 2)) :=
        ((Real.contDiff_sin (n := ⊤)).pow 2).contDiffOn
      have hleib := Work.FTS.Nonlinear.FstarPkg.DthAux.dthU_iter_mul_Ioo i
        (fun θ' => Real.sin θ' ^ 2) (fun θ' => Work.Spaces.Gam α θ') hioo hsmith
        (Work.FTS.Nonlinear.FstarPkg.DthAux.contDiffOn_Gam_Ioo' α)
      have hDth : Work.Spaces.DthIter i
          (fun _ (θ' : ℝ) => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') 0 θ
          = ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) *
              (Work.Spaces.dthU^[a] (fun θ' => Real.sin θ' ^ 2) θ
                * Work.Spaces.dthU^[i - a] (fun t => Work.Spaces.Gam α t) θ) := by
        rw [Work.FTS.LocData.DthIter_rad_eq i
          (fun θ' => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') 0 θ]
        exact hleib
      have hsin2 : |Real.sin θ ^ 2| ≤ 1 := by
        rw [abs_of_nonneg (sq_nonneg _)]
        calc Real.sin θ ^ 2 = |Real.sin θ| ^ 2 := by rw [sq_abs]
          _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sin_le_one θ) 2
          _ = 1 := by norm_num
      have hterm : ∀ a ∈ Finset.range (i + 1),
          |(i.choose a : ℝ) * (Work.Spaces.dthU^[a] (fun θ' => Real.sin θ' ^ 2) θ
              * Work.Spaces.dthU^[i - a] (fun t => Work.Spaces.Gam α t) θ)|
            ≤ (i.choose a : ℝ) * ((100000 + Bs * 100000)
                * (Real.sin (2 * θ)) ^ (α / 5)) := by
        intro a ha
        have hai : a ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        rcases Nat.eq_zero_or_pos a with ha0 | hapos
        · -- `a = 0`: the `Γ`-iterate
          subst ha0
          rw [Function.iterate_zero_apply, Nat.sub_zero]
          have hΓ := hGamJ i hi1 hi4
          calc |Real.sin θ ^ 2 * Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
              = |Real.sin θ ^ 2| * |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ| :=
                abs_mul _ _
            _ ≤ 1 * (100000 * (Real.sin (2 * θ)) ^ (α / 5)) :=
                mul_le_mul hsin2 hΓ (abs_nonneg _) (by norm_num)
            _ ≤ (100000 + Bs * 100000) * (Real.sin (2 * θ)) ^ (α / 5) := by
                have hBnn : (0 : ℝ) ≤ Bs * 100000 := by positivity
                nlinarith [hsα, hBnn]
        · have hsinA := hSin1 a hapos (le_trans hai hi4)
          rcases Nat.eq_zero_or_pos (i - a) with hia0 | hiapos
          · -- `i = a`: the bare `Γ`
            have hΓ : Work.Spaces.dthU^[i - a] (fun t => Work.Spaces.Gam α t) θ
                = Work.Spaces.Gam α θ := by rw [hia0]; rfl
            have hGle : |Work.Spaces.Gam α θ| ≤ 1 := by
              rw [abs_of_nonneg (Work.Spaces.Gam_bounds α θ hα hθ).1]
              exact (Work.Spaces.Gam_bounds α θ hα hθ).2
            rw [hΓ]
            calc |Work.Spaces.dthU^[a] (fun θ' => Real.sin θ' ^ 2) θ * Work.Spaces.Gam α θ|
                = |Work.Spaces.dthU^[a] (fun θ' => Real.sin θ' ^ 2) θ| * |Work.Spaces.Gam α θ| :=
                  abs_mul _ _
              _ ≤ (Bs * Real.sin (2 * θ)) * 1 :=
                  mul_le_mul hsinA hGle (abs_nonneg _) (by positivity)
              _ = Bs * Real.sin (2 * θ) := by ring
              _ ≤ (100000 + Bs * 100000) * (Real.sin (2 * θ)) ^ (α / 5) := by
                  have h1 : Bs * Real.sin (2 * θ) ≤ Bs * (Real.sin (2 * θ)) ^ (α / 5) :=
                    mul_le_mul_of_nonneg_left hsle hBspos.le
                  have h2 : Bs * (Real.sin (2 * θ)) ^ (α / 5)
                      ≤ (100000 + Bs * 100000) * (Real.sin (2 * θ)) ^ (α / 5) := by
                    apply mul_le_mul_of_nonneg_right _ hsα
                    nlinarith [hBspos.le]
                  linarith
          · -- both iterates are positive
            have hΓ := hGamJ (i - a) hiapos (by omega)
            calc |Work.Spaces.dthU^[a] (fun θ' => Real.sin θ' ^ 2) θ
                  * Work.Spaces.dthU^[i - a] (fun t => Work.Spaces.Gam α t) θ|
                = |Work.Spaces.dthU^[a] (fun θ' => Real.sin θ' ^ 2) θ|
                  * |Work.Spaces.dthU^[i - a] (fun t => Work.Spaces.Gam α t) θ| := abs_mul _ _
              _ ≤ (Bs * Real.sin (2 * θ)) * (100000 * (Real.sin (2 * θ)) ^ (α / 5)) :=
                  mul_le_mul hsinA hΓ (abs_nonneg _) (by positivity)
              _ = Bs * 100000 * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
              _ ≤ Bs * 100000 * (Real.sin (2 * θ)) ^ (α / 5) := by
                  have h1 : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (α / 5)
                      ≤ 1 * (Real.sin (2 * θ)) ^ (α / 5) :=
                    mul_le_mul_of_nonneg_right hs1 hsα
                  have h2 : (1:ℝ) * (Real.sin (2 * θ)) ^ (α / 5)
                      = (Real.sin (2 * θ)) ^ (α / 5) := one_mul _
                  have h3 : (0:ℝ) ≤ Bs * 100000 := by positivity
                  nlinarith [h1, h2, h3, hsα]
              _ ≤ (100000 + Bs * 100000) * (Real.sin (2 * θ)) ^ (α / 5) := by
                  have h1 : (0:ℝ) ≤ 100000 * (Real.sin (2 * θ)) ^ (α / 5) := by positivity
                  nlinarith [hBspos.le, hsα]
      rw [hDth]
      calc |∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) *
              (Work.Spaces.dthU^[a] (fun θ' => Real.sin θ' ^ 2) θ
                * Work.Spaces.dthU^[i - a] (fun t => Work.Spaces.Gam α t) θ)|
          ≤ ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) *
              ((100000 + Bs * 100000) * (Real.sin (2 * θ)) ^ (α / 5)) :=
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
        _ = (∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ))
              * ((100000 + Bs * 100000) * (Real.sin (2 * θ)) ^ (α / 5)) := by
            rw [Finset.sum_mul]
        _ = (2 : ℝ) ^ i * ((100000 + Bs * 100000) * (Real.sin (2 * θ)) ^ (α / 5)) := by
            rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
        _ ≤ 16 * ((100000 + Bs * 100000) * (Real.sin (2 * θ)) ^ (α / 5)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have h2i : (2 : ℝ) ^ i ≤ 16 := by
              calc (2 : ℝ) ^ i ≤ (2 : ℝ) ^ 4 :=
                    pow_le_pow_right₀ (by norm_num) hi4
                _ = 16 := by norm_num
            exact h2i
        _ ≤ (16 * (100000 + Bs * 100000) + 1) * (Real.sin (2 * θ)) ^ (α / 5) := by
            have h1 : (0:ℝ) ≤ (Real.sin (2 * θ)) ^ (α / 5) := hsα
            nlinarith [h1]

/-! ## `SmoothInt` for the two profiles of `N₅^{sg}` -/




end Work.FTS.Nonlinear.Pieces.RNP
end
end
