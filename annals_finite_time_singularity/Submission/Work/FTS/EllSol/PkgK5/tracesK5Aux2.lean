import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllSol.PkgK5.tracesK5Aux
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

/-! ## 3. The `sEta`-energy of `∂_θ²` of the radial iterates of `X` -/

theorem secondSlot_dzIter {α : ℝ} {k : ℕ} {F X : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F X)
    (j : ℕ) (hj : j ≤ k + 1) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t => deriv (fun θ' => Work.Spaces.DzIter j X z θ') t) θ) ^ 2
        * sEta θ) Iθ := by
  have hXsm : Work.FTS.EllipticEst.SmoothOpen X :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  rcases lt_or_eq_of_le hj with hjlt | hjeq
  · have hg : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 X) := (hXsm.pth).pth
    have h1 := Work.FTS.EllipticEst.remov.ws_slot_slice hg h.memB j (by omega) hz
    refine h1.congr_fun_ae ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    exact congrArg (fun x : ℝ => x ^ 2 * sEta θ)
      (Work.FTS.EllipticEst.remov.ws_pthIter_two_DzIter hXsm j hz hθ).symm
  · subst hjeq
    have hWsm : Work.FTS.EllipticEst.SmoothOpen
        (Work.Spaces.Dz (Work.Spaces.pthIter 2 X)) := ((hXsm.pth).pth).Dz
    have h1 := Work.FTS.EllipticEst.remov.ws_slot_slice hWsm h.memZPth2 k le_rfl hz
    have hshift : Work.Spaces.DzIter k (Work.Spaces.Dz (Work.Spaces.pthIter 2 X))
        = Work.Spaces.DzIter (k + 1) (Work.Spaces.pthIter 2 X) :=
      (Work.Spaces.DzIter_add_right k 1 (Work.Spaces.pthIter 2 X)).symm
    refine h1.congr_fun_ae ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    rw [hshift]
    exact congrArg (fun x : ℝ => x ^ 2 * sEta θ)
      (Work.FTS.EllipticEst.remov.ws_pthIter_two_DzIter hXsm (k + 1) hz hθ).symm

/-! ## 4. The slice form of the equation at radial level `j` -/

/-- On the open quadrant, `Lzero1 (D_z^j X(z,·)) = D_z^jF(z,·) + α²D_z^jA(z,·)
+ α(5+α)D_z^{j+1}X(z,·)`, obtained from `bslOp α (D_z^jX) = D_z^jF`
(`TT.bslOp_DzIter_eq`), the split `z²∂_z²X = D_z²X - D_zX` and the `A`-identity
`D_z^jA = D_z^{j+2}X - D_z^{j+1}X`. -/
theorem sliceEq_dzIter {α : ℝ} {k : ℕ} {F X : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F X) (j : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Lzero1 (fun t => Work.Spaces.DzIter j X z t) θ
      = Work.Spaces.DzIter j F z θ
        + α ^ 2 * Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ
        + (α * (5 + α)) * Work.Spaces.DzIter (j + 1) X z θ := by
  have hXsm : Work.FTS.EllipticEst.SmoothOpen X :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hbs := Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F X j h.smooth h.eq
    z hz θ hθ.1 hθ.2
  rw [Work.Elliptic.bslOp_apply] at hbs
  have hL1 : Lzero1 (fun t => Work.Spaces.DzIter j X z t) θ
      = Work.Elliptic.Lzero (Work.Spaces.DzIter j X) z θ := rfl
  have hzsq : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j X) z θ
      = Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ := by
    rw [Work.FTS.EllipticEst.H2W.zsq_pzIter2_eq (hXsm.DzIter j) hz hθ,
      Work.FTS.EllipticEst.H2W.DzIter_zsq_pzIter2_eq hXsm j hz hθ,
      show Work.Spaces.DzIter 2 (Work.Spaces.DzIter j X) = Work.Spaces.DzIter (j + 2) X from
        ((Work.Spaces.DzIter_add_right 2 j X).symm).trans (by rw [Nat.add_comm]),
      show Work.Spaces.Dz (Work.Spaces.DzIter j X) = Work.Spaces.DzIter (j + 1) X from
        (Work.Spaces.DzIter_succ j X).symm]
  have hDz : z * Work.Spaces.pz (Work.Spaces.DzIter j X) z θ = Work.Spaces.DzIter (j + 1) X z θ :=
    rfl
  have hkey : -(α ^ 2) * (z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j X) z θ)
      + (-(α * (5 + α))) * (z * Work.Spaces.pz (Work.Spaces.DzIter j X) z θ)
      + Work.Elliptic.Lzero (Work.Spaces.DzIter j X) z θ = Work.Spaces.DzIter j F z θ := by
    linarith [hbs]
  rw [hL1]
  rw [show Work.Elliptic.Lzero (Work.Spaces.DzIter j X) z θ
      = Work.Spaces.DzIter j F z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j X) z θ)
        + (α * (5 + α)) * (z * Work.Spaces.pz (Work.Spaces.DzIter j X) z θ) from by
    linarith [hkey]]
  rw [hzsq, hDz]

/-! ## 5. The `Lzero1`-energy of the slices -/

theorem lzero1_energy_dzIter {α : ℝ} {k : ℕ} {F X : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F X)
    (hAh : Work.Spaces.HkMem α (k + 3)
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ))
    (hFmem : Work.Spaces.HkMem α (k + 2) F)
    (j : ℕ) (hj : j ≤ k + 1) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Lzero1 (fun t => Work.Spaces.DzIter j X z t) θ) ^ 2 * sEta θ) Iθ := by
  have hXsm : Work.FTS.EllipticEst.SmoothOpen X :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hFsm : Work.FTS.EllipticEst.SmoothOpen F := Work.FTS.EllipticEst.remov.ws_smoothOpen_F h
  have hAsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) :=
    Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq hXsm
  have hI1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.DzIter j F z θ) ^ 2 * sEta θ) Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice hFsm hFmem j (by omega) hz
  have hI2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ) ^ 2 * sEta θ) Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice hAsm hAh j (by omega) hz
  have hI3 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.DzIter (j + 1) X z θ) ^ 2 * sEta θ) Iθ :=
    slotEnergy_dzIter hk h hAh (j + 1) (by omega) z hz
  have h2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 3 * ((α ^ 2 * Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ) ^ 2 * sEta θ)) Iθ :=
    ((hI2.const_mul (α ^ 4)).const_mul 3).congr
      (Filter.Eventually.of_forall (fun θ => by ring))
  have h3 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 3 * (((α * (5 + α)) * Work.Spaces.DzIter (j + 1) X z θ) ^ 2
        * sEta θ)) Iθ :=
    ((hI3.const_mul ((α * (5 + α)) ^ 2)).const_mul 3).congr
      (Filter.Eventually.of_forall (fun θ => by ring))
  have h1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 3 * ((Work.Spaces.DzIter j F z θ) ^ 2 * sEta θ)) Iθ := hI1.const_mul 3
  have hdom : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 3 * ((Work.Spaces.DzIter j F z θ) ^ 2
        + (α ^ 2 * Work.Spaces.DzIter j
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ) ^ 2
        + ((α * (5 + α)) * Work.Spaces.DzIter (j + 1) X z θ) ^ 2) * sEta θ) Iθ :=
    ((h1.add h2).add h3).congr (Filter.Eventually.of_forall (fun θ => by
      simp only [Pi.add_apply]; ring))
  have hLm : AEStronglyMeasurable
      (fun θ : ℝ => Lzero1 (fun t => Work.Spaces.DzIter j X z t) θ) (volume.restrict Iθ) := by
    have hslice := aesm_slice_dzIter hXsm j hz
    have h1 : AEStronglyMeasurable
        (fun θ : ℝ => deriv (fun t => deriv (fun t' => Work.Spaces.DzIter j X z t') t) θ)
        (volume.restrict Iθ) := (measurable_deriv _).aestronglyMeasurable
    have h2 : AEStronglyMeasurable
        (fun θ : ℝ => deriv (fun t => Real.tan t * Work.Spaces.DzIter j X z t) θ)
        (volume.restrict Iθ) := (measurable_deriv _).aestronglyMeasurable
    have hfun : (fun θ : ℝ => Lzero1 (fun t => Work.Spaces.DzIter j X z t) θ)
        = fun θ : ℝ => -(deriv (fun t => deriv (fun t' => Work.Spaces.DzIter j X z t') t) θ)
            + deriv (fun t => Real.tan t * Work.Spaces.DzIter j X z t) θ
            - 6 * Work.Spaces.DzIter j X z θ := rfl
    rw [hfun]
    exact ((h1.neg).add h2).sub (hslice.const_mul 6)
  refine MeasureTheory.Integrable.mono' hdom ((hLm.pow 2).mul aesm_sEta_Iθ) ?_
  filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
  have hS0 : 0 ≤ sEta θ :=
    Work.FTS.EllipticEst.remov.ws_sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hS0)]
  rw [sliceEq_dzIter h j hz hθ]
  nlinarith [sq_nonneg (Work.Spaces.DzIter j F z θ
      - α ^ 2 * Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ),
    sq_nonneg (α ^ 2 * Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ
      - (α * (5 + α)) * Work.Spaces.DzIter (j + 1) X z θ),
    sq_nonneg ((α * (5 + α)) * Work.Spaces.DzIter (j + 1) X z θ - Work.Spaces.DzIter j F z θ)]

/-! ## 6. The angular moment of the slices -/

theorem lzero1_moment_dzIter {α : ℝ} {k : ℕ} {F X : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F X)
    (hAh : Work.Spaces.HkMem α (k + 3)
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ))
    (hFmem : Work.Spaces.HkMem α (k + 2) F)
    (hmom : ∀ i : ℕ, i ≤ k + 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter i X) z = 0)
    (hmomF : ∀ i : ℕ, i ≤ k + 1 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter i F) z = 0)
    (j : ℕ) (hj : j ≤ k + 1) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Iθ, Lzero1 (fun t => Work.Spaces.DzIter j X z t) θ * sg θ) = 0 := by
  have hXsm : Work.FTS.EllipticEst.SmoothOpen X :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hFsm : Work.FTS.EllipticEst.SmoothOpen F := Work.FTS.EllipticEst.remov.ws_smoothOpen_F h
  have hAsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) :=
    Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq hXsm
  -- the four slot energies
  have hE1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.DzIter j F z θ) ^ 2 * sEta θ) Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice hFsm hFmem j (by omega) hz
  have hE2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ) ^ 2 * sEta θ) Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice hAsm hAh j (by omega) hz
  have hE3 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.DzIter (j + 1) X z θ) ^ 2 * sEta θ) Iθ :=
    slotEnergy_dzIter hk h hAh (j + 1) (by omega) z hz
  have hE4 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.DzIter (j + 2) X z θ) ^ 2 * sEta θ) Iθ :=
    slotEnergy_dzIter hk h hAh (j + 2) (by omega) z hz
  obtain ⟨hF1, _⟩ := Work.FTS.EllipticEst.remov.ws_absMoment (aesm_slice_dzIter hFsm j hz) hE1
  obtain ⟨hA1, _⟩ := Work.FTS.EllipticEst.remov.ws_absMoment (aesm_slice_dzIter hAsm j hz) hE2
  obtain ⟨hX1, _⟩ := Work.FTS.EllipticEst.remov.ws_absMoment (aesm_slice_dzIter hXsm (j + 1) hz) hE3
  obtain ⟨hX2, _⟩ := Work.FTS.EllipticEst.remov.ws_absMoment (aesm_slice_dzIter hXsm (j + 2) hz) hE4
  -- the corresponding integrabilities in the distributed shape
  have hA1' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (α ^ 2 * Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ) * sg θ) Iθ :=
    (hA1.const_mul (α ^ 2)).congr (Filter.Eventually.of_forall (fun θ => by ring))
  have hX1' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => ((α * (5 + α)) * Work.Spaces.DzIter (j + 1) X z θ) * sg θ) Iθ :=
    (hX1.const_mul (α * (5 + α))).congr (Filter.Eventually.of_forall (fun θ => by ring))
  -- split the integral through the slice equation
  have key : (∫ θ in Iθ, Lzero1 (fun t => Work.Spaces.DzIter j X z t) θ * sg θ)
      = (∫ θ in Iθ, Work.Spaces.DzIter j F z θ * sg θ)
        + (∫ θ in Iθ, (α ^ 2 * Work.Spaces.DzIter j
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ) * sg θ)
        + (∫ θ in Iθ, ((α * (5 + α)) * Work.Spaces.DzIter (j + 1) X z θ) * sg θ) := by
    have hfun : (fun θ : ℝ => Lzero1 (fun t => Work.Spaces.DzIter j X z t) θ * sg θ)
        =ᵐ[volume.restrict Iθ]
        (fun θ : ℝ => Work.Spaces.DzIter j F z θ * sg θ
          + (α ^ 2 * Work.Spaces.DzIter j
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ) * sg θ
          + ((α * (5 + α)) * Work.Spaces.DzIter (j + 1) X z θ) * sg θ) := by
      filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      rw [sliceEq_dzIter h j hz hθ]
      ring
    rw [MeasureTheory.integral_congr_ae hfun]
    exact integral_Iθ_add_three hF1 hA1' hX1'
  have e2 : (∫ θ in Iθ, (α ^ 2 * Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ) * sg θ)
      = α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ)) z := by
    rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun θ => by ring : ∀ θ : ℝ,
        (α ^ 2 * Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ) * sg θ
          = α ^ 2 * (Work.Spaces.DzIter j
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ * sg θ))),
      MeasureTheory.integral_const_mul]
    rfl
  have e3 : (∫ θ in Iθ, ((α * (5 + α)) * Work.Spaces.DzIter (j + 1) X z θ) * sg θ)
      = (α * (5 + α)) * Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) X) z := by
    rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun θ => by ring : ∀ θ : ℝ,
        ((α * (5 + α)) * Work.Spaces.DzIter (j + 1) X z θ) * sg θ
          = (α * (5 + α)) * (Work.Spaces.DzIter (j + 1) X z θ * sg θ))),
      MeasureTheory.integral_const_mul]
    rfl
  -- the middle moment via the `A`-identity
  have hAeq : Work.Elliptic.Fstar (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ)) z
      = Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 2) X) z
        - Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) X) z := by
    rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, Work.Elliptic.Fstar]
    have hcongr2 : (fun θ : ℝ => Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ * sg θ)
        =ᵐ[volume.restrict Iθ]
        (fun θ : ℝ => (Work.Spaces.DzIter (j + 2) X z θ
          - Work.Spaces.DzIter (j + 1) X z θ) * sg θ) := by
      filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      rw [Work.FTS.EllipticEst.H2W.DzIter_zsq_pzIter2_eq hXsm j hz hθ]
    rw [MeasureTheory.integral_congr_ae hcongr2,
      show (fun θ : ℝ => (Work.Spaces.DzIter (j + 2) X z θ
          - Work.Spaces.DzIter (j + 1) X z θ) * sg θ)
        = fun θ : ℝ => Work.Spaces.DzIter (j + 2) X z θ * sg θ
            - Work.Spaces.DzIter (j + 1) X z θ * sg θ from funext fun θ => by ring,
      MeasureTheory.integral_sub hX2 hX1]
  rw [key, e2, e3, hAeq,
    show (∫ θ in Iθ, Work.Spaces.DzIter j F z θ * sg θ)
      = Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z from rfl,
    hmomF j (by omega) z hz, hmom (j + 1) (by omega) z hz, hmom (j + 2) (by omega) z hz]
  ring

end Work.FTS.EllSol.PkgK5
