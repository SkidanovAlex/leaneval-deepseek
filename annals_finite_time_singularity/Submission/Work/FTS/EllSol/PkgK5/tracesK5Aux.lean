import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.weakSliceRegular
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false
set_option maxHeartbeats 3200000

local notation "Iθ" => Work.Spaces.Iθ
local notation "sEta" => Work.FTS.EllipticEst.sEta
local notation "sg" => Work.Elliptic.sinCos2
local notation "Lzero1" => Work.FTS.EllipticEst.Lzero1

/-! ## 0. Elementary measure-theoretic helpers -/

/-- `sEta` is a.e. strongly measurable on `Iθ`. -/
theorem aesm_sEta_Iθ : AEStronglyMeasurable (fun θ : ℝ => sEta θ) (volume.restrict Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => sEta p.2)
    Work.FTS.EllipticEst.remov.ws_contOn_sEta (z := 1) (by norm_num)

/-- The angular slice of a `D_z`-iterate of a function smooth on the open quadrant is a.e.
strongly measurable. -/
theorem aesm_slice_dzIter {X : ℝ → ℝ → ℝ} (hXsm : Work.FTS.EllipticEst.SmoothOpen X) (j : ℕ)
    {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.DzIter j X z θ) (volume.restrict Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry (Work.Spaces.DzIter j X))
    (((hXsm.DzIter j).forall 0).continuousOn) hz

/-- Linearity of the `θ`-integral for a three-term sum (the shape produced by `ring` on
`(f₁ + f₂ + f₃)·sinθcos²θ`). -/
theorem integral_Iθ_add_three {f1 f2 f3 : ℝ → ℝ}
    (h1 : MeasureTheory.IntegrableOn f1 Iθ) (h2 : MeasureTheory.IntegrableOn f2 Iθ)
    (h3 : MeasureTheory.IntegrableOn f3 Iθ) :
    (∫ θ in Iθ, f1 θ + f2 θ + f3 θ)
      = (∫ θ in Iθ, f1 θ) + (∫ θ in Iθ, f2 θ) + (∫ θ in Iθ, f3 θ) := by
  have h12 : (∫ θ in Iθ, f1 θ + f2 θ) = (∫ θ in Iθ, f1 θ) + (∫ θ in Iθ, f2 θ) :=
    MeasureTheory.integral_add h1 h2
  have h123 : (∫ θ in Iθ, f1 θ + f2 θ + f3 θ)
      = (∫ θ in Iθ, f1 θ + f2 θ) + (∫ θ in Iθ, f3 θ) :=
    MeasureTheory.integral_add (h1.add h2) h3
  rw [h123, h12]

/-! ## 1. The radial moment tower of the source -/

/-- **The source moments vanish along the radial iterates.**  From `HkMem α (k+2) F` and the base
condition `F_*(F) ≡ 0` on `(0,∞)`, the radial moment tower
`HasDerivAt (F_*(D_z^jF)) (F_*(D_z^{j+1}F)(z)/z) z` (everywhere, `Cert.radIter_bmom_hasDerivAt`)
propagates the vanishing to all `j ≤ k+1`. -/
theorem fstar_dzIter_source_eq_zero {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hFsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hmem : Work.Spaces.HkMem α (k + 2) F)
    (h0 : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) :
    ∀ i : ℕ, i ≤ k + 1 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter i F) z = 0 := by
  have hder : ∀ j : ℕ, j ≤ k → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w : ℝ => Work.FTS.EllipticEst.Bmom F j w)
        (Work.FTS.EllipticEst.Bmom F (j + 1) z / z) z :=
    fun j hj z hz =>
      Work.FTS.EllipticEst.Cert.radIter_bmom_hasDerivAt α (k + 2) hFsm hmem j (by omega) hz
  have key : ∀ i : ℕ, i ≤ k + 1 → ∀ z : ℝ, 0 < z →
      Work.FTS.EllipticEst.Bmom F i z = 0 := by
    intro i hi
    induction i with
    | zero =>
        intro z hz
        rw [Work.FTS.EllipticEst.Bmom_zero]
        exact h0 z hz
    | succ i ih =>
        intro z hz
        have hprev : (fun w : ℝ => Work.FTS.EllipticEst.Bmom F i w)
            =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
          exact ih (by omega) w hw
        have hzero : HasDerivAt (fun w : ℝ => Work.FTS.EllipticEst.Bmom F i w) 0 z :=
          hprev.hasDerivAt_iff.mpr (hasDerivAt_const z 0)
        have huniq : Work.FTS.EllipticEst.Bmom F (i + 1) z / z = 0 :=
          (hder i (by omega) z hz).unique hzero
        rcases div_eq_zero_iff.mp huniq with h | h
        · exact h
        · exact absurd h (ne_of_gt hz)
  intro i hi z hz
  rw [← Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter]
  exact key i hi z hz

/-! ## 2. The `sEta`-energies of the radial iterates of `X`

`Ϝ_b(z) = ∫_θ (D_z^bX(z,θ))²·sEta θ`: finite for every `b ≤ k+4`, by the recursion
`D_z^{b+2}X = D_z^bA + D_z^{b+1}X` (`DzIter_zsq_pzIter2_eq`, with `b-2 ≤ k+3` under
`b ≤ k+4`) down to the base level `b = 1`, which is `ws_pz_energy_integrable`. -/

theorem slotEnergy_dzIter {α : ℝ} {k : ℕ} {F X : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F X)
    (hAh : Work.Spaces.HkMem α (k + 3)
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ)) :
    ∀ b : ℕ, b ≤ k + 4 → ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.DzIter b X z θ) ^ 2 * sEta θ) Iθ := by
  have hXsm : Work.FTS.EllipticEst.SmoothOpen X :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) :=
    Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq hXsm
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb z hz
    rcases lt_or_ge b 2 with hb2 | hb2
    · interval_cases b
      · -- `b = 0`: the slice is bounded (`abs_le_of_sq_mul_sEta`) and `sEta ∈ L¹`.
        have h2 : MeasureTheory.IntegrableOn
            (fun θ : ℝ => (deriv (fun t => deriv (fun θ' => X z θ') t) θ) ^ 2 * sEta θ) Iθ :=
          Work.FTS.EllipticEst.remov.ws_slot_slice ((hXsm.pth).pth) h.memB 0 (by omega) hz
        obtain ⟨C, hCpos, hC⟩ :=
          Work.FTS.EllipticEst.remov.abs_le_of_sq_mul_sEta
            (Work.FTS.EllipticEst.remov.ws_contDiffOn_slice hXsm hz) h2
        refine MeasureTheory.Integrable.mono'
          (Work.FTS.EllipticEst.remov.ws_sEta_integrableOn.const_mul (C ^ 2))
          (((aesm_slice_dzIter hXsm 0 hz).pow 2).mul aesm_sEta_Iθ) ?_
        filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
        have hS0 : 0 ≤ sEta θ :=
          Work.FTS.EllipticEst.remov.ws_sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hS0)]
        have hb' : |X z θ| ≤ C := (hC θ hθ).2
        have hXs : X z θ ^ 2 ≤ C ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hb' 2
        exact mul_le_mul_of_nonneg_right hXs hS0
      · -- `b = 1`: `D_zX = z ∂_zX` and `ws_pz_energy_integrable`.
        have h1 : MeasureTheory.IntegrableOn
            (fun θ : ℝ => (Work.Spaces.pz X z θ) ^ 2 * sEta θ) Iθ :=
          Work.FTS.EllipticEst.remov.ws_pz_energy_integrable (α := α) (k := k)
            (by omega : 1 ≤ k) h hz
        refine (h1.const_mul (z ^ 2)).congr ?_
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ _
        show z ^ 2 * ((Work.Spaces.pz X z θ) ^ 2 * sEta θ)
          = (Work.Spaces.DzIter 1 X z θ) ^ 2 * sEta θ
        rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
        simp only [Work.Spaces.Dz]
        ring
    · -- `b ≥ 2`: the recursion.
      have h1 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Spaces.DzIter (b - 2)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ) ^ 2 * sEta θ) Iθ :=
        Work.FTS.EllipticEst.remov.ws_slot_slice hAsm hAh (b - 2) (by omega) hz
      have h2 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Spaces.DzIter (b - 1) X z θ) ^ 2 * sEta θ) Iθ :=
        ih (b - 1) (by omega) (by omega) z hz
      refine MeasureTheory.Integrable.mono'
        ((h1.add h2).const_mul 2)
        (((aesm_slice_dzIter hXsm b hz).pow 2).mul aesm_sEta_Iθ) ?_
      filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      have hS0 : 0 ≤ sEta θ :=
        Work.FTS.EllipticEst.remov.ws_sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hS0)]
      have hrec : Work.Spaces.DzIter b X z θ
          = Work.Spaces.DzIter (b - 2) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ
            + Work.Spaces.DzIter (b - 1) X z θ := by
        have hsplit := Work.FTS.EllipticEst.H2W.DzIter_zsq_pzIter2_eq hXsm (b - 2) hz hθ
        have e2 : b - 2 + 2 = b := by omega
        have e1 : b - 2 + 1 = b - 1 := by omega
        rw [e2, e1] at hsplit
        linarith [hsplit]
      rw [hrec]
      have hsq : ∀ x y : ℝ, (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
        intro x y
        nlinarith [sq_nonneg (x - y)]
      have hstep := mul_le_mul_of_nonneg_right
        (hsq (Work.Spaces.DzIter (b - 2) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ)
          (Work.Spaces.DzIter (b - 1) X z θ)) hS0
      simp only [Pi.add_apply] at hstep ⊢
      linarith [hstep]


end Work.FTS.EllSol.PkgK5
