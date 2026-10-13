import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.H5.Data
import Submission.Work.FTS.StrongEps.H5.LevelShift
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.OpenPkg.l12H_field
import Submission.Work.FTS.OpenPkg.l12_open_bundle
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.StrongPersist.QangAe6
import Submission.Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.Galerkin.Inhabit
import Submission.Work.FTS.LocData.integral_sin_two_rpow_neg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.Atoms

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary sign facts for the radial iterates `D_z^i` -/

/-- `deriv` of a negated function (unconditional; `deriv` is additive even where the function
is not differentiable, both sides being the junk value `0`). -/
private theorem deriv_neg_fun (f : ℝ → ℝ) (x : ℝ) :
    deriv (fun y => -f y) x = -deriv f x := by
  rw [show (fun y => -f y) = fun y => (-1 : ℝ) * f y from by funext y; ring,
    deriv_const_mul_field]
  ring

/-- The iterated `z∂_z`-operator is odd. -/
private theorem DzdIter_neg_fun (f : ℝ → ℝ) (i : ℕ) :
    Work.Elliptic.DzdIter i (fun y => -f y) = fun z => -Work.Elliptic.DzdIter i f z := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Work.Elliptic.DzdIter_succ, Work.Elliptic.DzdIter_succ, ih]
      funext z
      show z * deriv (fun y => -Work.Elliptic.DzdIter n f y) z
        = -(z * deriv (Work.Elliptic.DzdIter n f) z)
      rw [deriv_neg_fun]
      ring

/-- The applied form of `DzdIter_neg_fun`, for the angular moment `Qang g 0`. -/
private theorem DzdIter_neg_Qang (g : ℝ → ℝ → ℝ) (i : ℕ) (z : ℝ) :
    Work.Elliptic.DzdIter i (fun y => -Work.Elliptic.Qang g 0 y) z
      = -Work.Elliptic.DzdIter i (fun y => Work.Elliptic.Qang g 0 y) z :=
  congrFun (DzdIter_neg_fun (fun y => Work.Elliptic.Qang g 0 y) i) z

/-! ## The `ℋ⁴`-membership of a radial lift -/

/-- **A radial lift is `ℋ⁴`-honest from its radial slot data.**  If every radial slot
`(D_z^i u)²w²`, `i ≤ 4`, is integrable on `Iz` with integral at most `M`, then the lift
`(z,θ) ↦ u z` lies in `ℋ⁴` and `HkSq α 4 (z,θ ↦ u z) ≤ 5 M ·∫_θ sin(2θ)^{-η}`.

The lift has no angular derivatives, so `HkIntegrand` reduces to the `D_z`-sum times
`sin(2θ)^{-η}` (`HkIntegrand_rad'`), and the two membership clauses are the two iterated
integrations of that identity. -/
private theorem radialLift_mem4 {α : ℝ} {u : ℝ → ℝ} {M : ℝ}
    (hInt : ∀ i : ℕ, i ≤ 4 → MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz)
    (hBnd : ∀ i : ℕ, i ≤ 4 → (∫ z in Work.Spaces.Iz,
      (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) ≤ M) :
    Work.Spaces.HkMem α 4 (fun z _ => u z) ∧
      Work.Spaces.HkSq α 4 (fun z _ => u z) ≤ 5 * M
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hsum_int : ∀ i ∈ Finset.range 5, MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => hInt i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hsum_le : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 5,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) ≤ 5 * M := by
    rw [MeasureTheory.integral_finsetSum (Finset.range 5) hsum_int]
    calc ∑ i ∈ Finset.range 5, (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _i ∈ Finset.range 5, M :=
          Finset.sum_le_sum fun i hi => hBnd i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      _ = 5 * M := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
  have hsinI : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    (Work.FTS.LocData.integral_sin_two_rpow_neg Work.Spaces.eta Work.Spaces.eta_pos
      Work.Spaces.eta_lt_one).1
  have hCthnn : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
    setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Real.rpow_nonneg (Work.Elliptic.sin_two_nonneg_of_mem hθ) _)
  have hinner : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z θ => u z) z θ)
      = (∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    intro z
    rw [setIntegral_congr_fun (s := Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α 4 (fun z θ => u z) z θ)
      (g := fun θ => (∑ i ∈ Finset.range 5,
          (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      measurableSet_Icc (fun θ hθ => Work.FTS.H2.HkIntegrand_rad' α 4 u z hθ)]
    rw [MeasureTheory.integral_const_mul]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z _
    refine MeasureTheory.Integrable.congr (f := fun θ : ℝ =>
        (∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (hsinI.const_mul _) ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => (Work.FTS.H2.HkIntegrand_rad' α 4 u z hθ).symm)
  · refine MeasureTheory.Integrable.congr (f := fun z : ℝ =>
        (∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        ((MeasureTheory.integrable_finsetSum (Finset.range 5) hsum_int).mul_const _) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => ?_)
    exact (hinner z).symm
  · rw [Work.Elliptic.HkSq_rad]
    exact mul_le_mul_of_nonneg_right hsum_le hCthnn

/-- **The `L5` data of the radial atom `z ↦ L₁₂(w)(z)`.**  For a `ClassC` datum `w` with
`Xn α w ≤ C₀ α²` and `HkNorm α 6 w ≤ B` there is `a > 0` with
`L5 α (fun z θ => L₁₂(w)(z)) a`, i.e. `HQo α 4` of `L₁₂(w)`, of its `D_z`-derivative and of its
`D_θ`-derivative, plus the corresponding `Xn`-bounds.

Route.  `ClassC α w` gives `SmoothOpen w`, `HkMem α 7 w` and `L₁₂(w)(0) = 0`.
* `HQo α 4 (fun z θ => L₁₂ w z)`: `Work.FTS.OpenPkg.l12H_field` (with `SmoothOpen` from
  `ClassCRHS.smoothOpen_L12_radial_classC`) gives `HkMem α 4` and `Xn α (L₁₂ w) ≤ C₁ · Xn α w`.
* `Dth (fun z θ => L₁₂ w z) = 0` pointwise (a radial function has `pth = 0`), so its `HQo α 4`
  and its `Xn`-bound are trivial.
* `HQo α 4 (Dz (fun z θ => L₁₂ w z))`: on the open quadrant `Dz (fun z θ => L₁₂ w z) = -Qang w 0`
  (`Work.FTS.OpenPkg.l12_open_bundle`, the recursion `D_z^{k+1} L₁₂ = -Qang g k` at `k = 0`,
  valid for `z > 0`), so it suffices to show `HkMem α 4 (fun z θ => - Qang w 0 z)` and
  `Xn α (fun z θ => - Qang w 0 z) ≤ C · Xn α w`.  The radial lift of `r` has
  `HkSq α 4 (fun z θ => r z) = (∫_z Σ_{i≤4} (DzdIter i r z)² w(z)²) · (∫_θ sin(2θ)^{-η})`
  (`Work.Elliptic.HkSq_rad`, `Work.FTS.Nonlinear.RadialProd.HkSq_rad_eq`), and the iterated
  `z∂_z`-derivatives of `Qang w 0` are the higher angular moments (`DzdIter i (Qang w 0) =
  Qang w i` for `i ≤ 4`, from `Work.FTS.StrongPersist.QangAe6` /
  `Work.FTS.OpenPkg.QangOpen.QangDiff_open`), each satisfying
  `∫_z (Qang w i z)² w(z)² ≤ (∫_θ Kθ²) · HkSq α 4 w`
  (`Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open`, `i ≤ 4`).  Conclude the membership
  with `Work.FTS.LocData.HkMem_of_majorant` and transport the a.e. identity with
  `Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0`.  `SmoothOpen (Dz (fun z θ => L₁₂ w z))` is
  automatic (`SmoothOpen.Dz` of the smooth radial lift). -/
theorem L5L12W : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
    ∃ a : ℝ, 0 < a ∧ ∀ {w : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ B →
      Work.FTS.StrongEps.H5.L5 α (fun z θ => Work.Construction.L12 w z) a := by
  intro α hαI C₀ B
  have hα : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  obtain ⟨C1, hC1pos, hL12bd⟩ := Work.FTS.OpenPkg.l12H_field
  -- ## the universal constants
  set AK : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hAKdef
  set Cth : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hCthdef
  set Cq : ℝ := Real.sqrt (5 * AK * Cth) with hCqdef
  have hCqnn : 0 ≤ Cq := Real.sqrt_nonneg _
  have hAKnn : 0 ≤ AK := by
    rw [hAKdef]
    exact setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hCthnn : 0 ≤ Cth := by
    rw [hCthdef]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Real.rpow_nonneg (Work.Elliptic.sin_two_nonneg_of_mem hθ) _)
  have h5 : 0 ≤ 5 * AK * Cth := mul_nonneg (mul_nonneg (by norm_num) hAKnn) hCthnn
  refine ⟨max 1 (max (C1 * (C₀ * α ^ 2)) (Cq * (C₀ * α ^ 2))),
    lt_of_lt_of_le one_pos (le_max_left 1 _), ?_⟩
  intro w hw hsmall _hB
  -- ## the `ClassC` data of the datum
  have hmem4w : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  have hL12 := hL12bd α hα hα1 w ⟨hw.reg, hmem4w⟩ hw.l12
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.L12 w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hw
  -- ## `D_z L₁₂(w) = -Qang w 0` on the open quadrant
  have hbundle := Work.FTS.OpenPkg.l12_open_bundle α w hα hα1 hw.reg hmem4w hw.l12
  have hDzEq : ∀ z θ : ℝ, Work.Spaces.Dz (fun z θ => Work.Construction.L12 w z) z θ
      = Work.Elliptic.DzdIter 1 (fun z => Work.Elliptic.L12 w z) z := by
    intro z θ
    show z * deriv (fun z' => Work.Construction.L12 w z') z
        = z * deriv (fun z' => Work.Elliptic.L12 w z') z
    rw [Work.FTS.H2.constructionL12_eq_ellipticL12 w]
  have hQang_eq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.Dz (fun z θ => Work.Construction.L12 w z) z θ
        = -Work.Elliptic.Qang w 0 z := by
    intro z θ hz _ _
    rw [hDzEq z θ]
    simpa using hbundle.1 0 (by norm_num) z hz
  -- ## the `Qang w i` slots and their a.e. identification with the iterates of `-Qang w 0`
  have hAe : ∀ᵐ z ∂(MeasureTheory.volume), z ∈ Work.Spaces.Iz → ∀ i ∈ Finset.range 5,
      Work.Elliptic.DzdIter i (fun y => -Work.Elliptic.Qang w 0 y) z
        = -Work.Elliptic.Qang w i z := by
    filter_upwards [Work.FTS.OpenPkg.QangOpen.DzdIter_Qang_ae_open hw.reg hmem4w,
      MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with z hz hne hzI
    intro i hi
    rw [DzdIter_neg_Qang w i z, hz (lt_of_le_of_ne hzI (Ne.symm hne)) i hi]
  have htransfer : ∀ i : ℕ, i ≤ 4 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.Qang w i z) ^ 2 * (Work.Spaces.w z) ^ 2
        = (Work.Elliptic.DzdIter i (fun y => -Work.Elliptic.Qang w 0 y) z) ^ 2
            * (Work.Spaces.w z) ^ 2 := by
    intro i hi
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [hAe] with z hz hzI
    rw [hz hzI i (Finset.mem_range.mpr (by omega : i < 5))]
    ring
  have hInt : ∀ i : ℕ, i ≤ 4 → MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i (fun y => -Work.Elliptic.Qang w 0 y) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => (Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open hα hα1 hw.reg hmem4w
      (i := i) hi).1.congr (htransfer i hi)
  have hBnd : ∀ i : ℕ, i ≤ 4 → (∫ z in Work.Spaces.Iz,
      (Work.Elliptic.DzdIter i (fun y => -Work.Elliptic.Qang w 0 y) z) ^ 2
        * (Work.Spaces.w z) ^ 2) ≤ AK * Work.Spaces.HkSq α 4 w := by
    intro i hi
    rw [hAKdef, ← MeasureTheory.integral_congr_ae (htransfer i hi)]
    exact (Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open hα hα1 hw.reg hmem4w
      (i := i) hi).2
  -- ## the radial lift of `-Qang w 0` is `ℋ⁴`
  have hrad := radialLift_mem4 (α := α) (u := fun y => -Work.Elliptic.Qang w 0 y)
    (M := AK * Work.Spaces.HkSq α 4 w) hInt hBnd
  rw [← hCthdef] at hrad
  have hmemQ : Work.Spaces.HkMem α 4 (fun y (_ : ℝ) => -Work.Elliptic.Qang w 0 y) := hrad.1
  have hXnQ : Real.sqrt (Work.Spaces.HkSq α 4 (fun y (_ : ℝ) => -Work.Elliptic.Qang w 0 y))
      ≤ Cq * Work.FTS.Nonlin.Xn α w := by
    calc Real.sqrt (Work.Spaces.HkSq α 4 (fun y (_ : ℝ) => -Work.Elliptic.Qang w 0 y))
        ≤ Real.sqrt (5 * (AK * Work.Spaces.HkSq α 4 w) * Cth) := Real.sqrt_le_sqrt hrad.2
      _ = Real.sqrt ((5 * AK * Cth) * Work.Spaces.HkSq α 4 w) := by congr 1; ring
      _ = Real.sqrt (5 * AK * Cth) * Real.sqrt (Work.Spaces.HkSq α 4 w) := Real.sqrt_mul h5 _
      _ = Cq * Work.FTS.Nonlin.Xn α w := by
          rw [hCqdef]
          simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
  -- ## transport to `Dz (L₁₂ w)`
  have hsqDz : Work.Spaces.HkSq α 4 (Work.Spaces.Dz (fun z θ => Work.Construction.L12 w z))
      = Work.Spaces.HkSq α 4 (fun y (_ : ℝ) => -Work.Elliptic.Qang w 0 y) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 4
      (fun z θ hz hθ hθ' => hQang_eq z θ hz hθ hθ')
  have hmemDz : Work.Spaces.HkMem α 4
      (Work.Spaces.Dz (fun z θ => Work.Construction.L12 w z)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hmemQ
      (fun z hz θ hθ => by
        show -Work.Elliptic.Qang w 0 z
          = Work.Spaces.Dz (fun z θ => Work.Construction.L12 w z) z θ
        rw [hQang_eq z θ hz hθ.1 hθ.2])
  have hXnDz : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz (fun z θ => Work.Construction.L12 w z))
      ≤ Cq * (C₀ * α ^ 2) := by
    have h1 : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz (fun z θ => Work.Construction.L12 w z))
        ≤ Cq * Work.FTS.Nonlin.Xn α w := by
      have h := hXnQ
      rwa [← hsqDz] at h
    exact le_trans h1 (mul_le_mul_of_nonneg_left hsmall hCqnn)
  -- ## `D_θ` of a radial lift vanishes
  have hDth_eq : Work.Spaces.Dth (fun z θ => Work.Construction.L12 w z)
      = fun _ _ => (0 : ℝ) := by
    funext z θ
    simp [Work.Spaces.Dth, Work.Spaces.pth]
  -- ## assembly
  refine ⟨⟨hsm, hL12.1⟩, ?_, ⟨hsm.Dz, hmemDz⟩, ?_, ⟨hsm.Dth, ?_⟩, ?_⟩
  · calc Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 w z)
        ≤ C1 * Work.FTS.Nonlin.Xn α w := hL12.2
      _ ≤ C1 * (C₀ * α ^ 2) := mul_le_mul_of_nonneg_left hsmall hC1pos.le
      _ ≤ max 1 (max (C1 * (C₀ * α ^ 2)) (Cq * (C₀ * α ^ 2))) :=
          le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans hXnDz (le_trans (le_max_right _ _) (le_max_right _ _))
  · rw [hDth_eq]
    exact Work.FTS.EllipticEst.HkMem_zero α 4
  · rw [hDth_eq]
    simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, Work.FTS.Galerkin.HkSq_zero_fun,
      Real.sqrt_zero]
    exact le_trans zero_le_one (le_max_left 1 _)

end Work.FTS.StrongEps.H5.Atoms
