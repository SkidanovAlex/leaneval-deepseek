import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.H2W.sliceWirtinger
import Submission.Work.H2W.zeroMeanPoincare
import Submission.Work.FTS.EllipticEst.aestronglyMeasurable_integral_Itheta_Q0
import Submission.Work.FTS.EllipticEst.integrable_prod_sq_restrict_open
import Submission.Work.FTS.EllipticEst.H2W.weakFirstIter
import Submission.Work.FTS.EllipticEst.H2W.Slot11Src.mixed11_Wt_sq_eq
import Submission.Work.FTS.EllipticEst.H2W.Slot11Src.integrableOn_mixed_slot_sq
import Submission.Work.FTS.EllipticEst.H2W.Slot11Src.aesm_pth_sq_int
import Submission.Work.FTS.EllipticEst.SliceLocal.PhiGKernel
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceTendstoZeroOfMoment
import Submission.Work.FTS.EllipticEst.H2W.weakSliceLimits
import Submission.Work.FTS.EllipticEst.DzCalc
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.FTS.EllipticEst.TT.SliceDatum
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.ZTBound
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.SliceKit
import Submission.Work.FTS.EllipticEst.H2W.weakSliceDerivBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT.Slot11

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

/-- The source integrand of the shifted slice. -/
noncomputable def Src (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) z t) θ) ^ 2
    * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)

theorem Src_apply (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Src α F Ψ z θ = (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) z t) θ) ^ 2
    * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α) := rfl

/-- The source integral of the shifted slice at fixed `z`. -/
noncomputable def SrcInt (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Iθ, Src α F Ψ z θ

/-- The `(1,1)`-mixed slot integral of a function `G` at fixed `z`. -/
noncomputable def SlotG (α : ℝ) (G : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Iθ, (Work.Spaces.mixed 1 1 G z θ * Work.Spaces.Wt α z θ) ^ 2

/-- The `j`-th pure `D_z`-slot of `∂_θ²Ψ` at fixed `z`, against the singular weight `sEta`. -/
noncomputable def PureZ (Ψ : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) : ℝ :=
  ∫ θ in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ) ^ 2
    * Work.FTS.EllipticEst.sEta θ

/-- `A = z²∂_z²Ψ`. -/
noncomputable def Abar (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

@[simp] theorem Abar_apply (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Abar Ψ z θ = z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ := rfl

/-- `Iθ`-form of `SrcInt`. -/
theorem SrcInt_eq (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    SrcInt α F Ψ z = ∫ θ in Iθ, Src α F Ψ z θ := rfl

/-- The angular weight `sin(2θ)^{2-γ}` of the shifted slice. -/
noncomputable def Sig2 (α θ : ℝ) : ℝ := Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)

/-- The `z²∂_z²Ψ`-slot of the first-order angular estimate at fixed `z`. -/
noncomputable def ZT (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Iθ, (deriv (fun θ' => Abar Ψ z θ') θ) ^ 2 * Sig2 α θ

/-- The `D_zΨ`-slot of the first-order angular estimate at fixed `z`. -/
noncomputable def ZD (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.DzIter 1 Ψ z θ') θ) ^ 2 * Sig2 α θ

theorem Sig2_nonneg {α θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Sig2 α θ :=
  Real.rpow_nonneg (Work.FTS.EllipticEst.TT.sin_two_nonneg hθ) _

/-- `(x+y+z)² ≤ 3(x²+y²+z²)`. -/
theorem sq_add_three_le (x y w : ℝ) : (x + y + w) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + w ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - w), sq_nonneg (x - w)]

/-- `(A · (wv / s^{η/2}))² = A² · s^{-η} · wv²` for `s ≥ 0`. -/
theorem sq_div_rpow_eta {A wv s : ℝ} (hs : 0 ≤ s) :
    (A * (wv / s ^ (Work.Spaces.eta / 2))) ^ 2
      = A ^ 2 * s ^ (-(Work.Spaces.eta)) * wv ^ 2 := by
  rw [div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta / 2)]
  rw [show (A * (wv * s ^ (-(Work.Spaces.eta / 2)))) ^ 2
      = A ^ 2 * wv ^ 2 * (s ^ (-(Work.Spaces.eta / 2))) ^ 2 from by ring]
  rw [show (s ^ (-(Work.Spaces.eta / 2))) ^ 2 = s ^ (-(Work.Spaces.eta)) from by
    rw [← Real.rpow_natCast (s ^ (-(Work.Spaces.eta / 2))) 2, ← Real.rpow_mul hs]
    ring_nf]
  ring

theorem smoothOpen_const_mul {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) (c : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * G z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have hfun : Function.uncurry (fun z θ : ℝ => c * G z θ)
      = (fun _ : ℝ × ℝ => c) * Function.uncurry G := by
    funext p; rfl
  rw [hfun]
  exact contDiffOn_const.mul (contDiffOn_iff_forall_nat_le.mp hG n le_top)

theorem smoothOpen_zsq_mul {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * G z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have hfun : Function.uncurry (fun z θ : ℝ => z ^ 2 * G z θ)
      = (fun p : ℝ × ℝ => p.1 ^ 2) * Function.uncurry G := by
    funext p; rfl
  rw [hfun]
  exact (contDiff_fst.pow 2).contDiffOn.mul (contDiffOn_iff_forall_nat_le.mp hG n le_top)

/-- The `θ`-slice of a function `C^∞` on the open quadrant is differentiable at every interior
angle. -/
theorem differentiableAt_slice_θ_open {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    DifferentiableAt ℝ (fun θ' => G z θ') θ :=
  ((hG.curry_θ hz).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
    (isOpen_Ioo.mem_nhds hθ)

/-- The shifts of the source: the `θ`-slice of `A = z²∂_z²Ψ` is `C^∞` on the open quadrant. -/
theorem smoothOpen_Abar {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Abar Ψ) :=
  smoothOpen_zsq_mul (hΨ.pzIter 2)

/-- The source `F` is `C^∞` on the open quadrant (it agrees there with `bslOp α Ψ`). -/
theorem smoothOpen_source {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.SmoothOpen F :=
  Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
      (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth))
    (fun z θ hz hθ hθ' => h.eq z hz θ hθ hθ')

/-- **The source of the shifted slice is `C^∞` on the open quadrant.** -/
theorem smoothOpen_Gsrc {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.Mine.Gsrc α
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ)) := by
  have hF : Work.FTS.EllipticEst.SmoothOpen F := smoothOpen_source h
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have h1 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 F) := hF.DzIter 1
  have h2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :=
    smoothOpen_zsq_mul ((hΨ.DzIter 1).pzIter 2)
  have h3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z θ) := by
    have he : (fun z θ : ℝ => z * Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z θ)
        = Work.Spaces.DzIter 2 Ψ := rfl
    rw [he]
    exact hΨ.DzIter 2
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.smoothOpen_add
      (Work.FTS.EllipticEst.smoothOpen_add h1 (smoothOpen_const_mul h2 (α ^ 2)))
      (smoothOpen_const_mul h3 (α * (5 + α)))) (fun z θ _ _ _ => ?_)
  simp only [Work.FTS.EllipticEst.Mine.Gsrc]

/-! ## 2. The three-term form of the source and its `θ`-derivative -/

/-- **The source of the shifted slice, in terms of `D_zΨ`, `D_z²Ψ`.** -/
theorem Gsrc_eq_three (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z t : ℝ) :
    Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) z t
      = Work.Spaces.DzIter 1 F z t
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z t)
        + (α * (5 + α)) * Work.Spaces.DzIter 2 Ψ z t := rfl

/-- **The `θ`-derivative of the source splits into three pieces.** -/
theorem Gsrc_pth_three {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α
          (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) z t) θ
        = deriv (fun t => Work.Spaces.DzIter 1 F z t) θ
          + α ^ 2 * deriv (fun t =>
              z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z t) θ
          + (α * (5 + α)) * deriv (fun t => Work.Spaces.DzIter 2 Ψ z t) θ := by
  intro z θ hz hθ
  have hF : Work.FTS.EllipticEst.SmoothOpen F := smoothOpen_source h
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have h1 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 F) := hF.DzIter 1
  have h2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :=
    smoothOpen_zsq_mul ((hΨ.DzIter 1).pzIter 2)
  have h3 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 2 Ψ) := hΨ.DzIter 2
  have hd1 : DifferentiableAt ℝ (fun t => Work.Spaces.DzIter 1 F z t) θ :=
    differentiableAt_slice_θ_open h1 hz hθ
  have hd2 : DifferentiableAt ℝ
      (fun t => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z t) θ :=
    differentiableAt_slice_θ_open h2 hz hθ
  have hd3 : DifferentiableAt ℝ (fun t => Work.Spaces.DzIter 2 Ψ z t) θ :=
    differentiableAt_slice_θ_open h3 hz hθ
  have hsrc : (fun t => Work.FTS.EllipticEst.Mine.Gsrc α
        (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) z t)
      =ᶠ[𝓝 θ] (fun t => Work.Spaces.DzIter 1 F z t
          + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z t)
          + (α * (5 + α)) * Work.Spaces.DzIter 2 Ψ z t) :=
    Filter.Eventually.of_forall (fun t => Gsrc_eq_three α F Ψ z t)
  rw [hsrc.deriv_eq,
    show (fun t : ℝ => Work.Spaces.DzIter 1 F z t
          + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z t)
          + (α * (5 + α)) * Work.Spaces.DzIter 2 Ψ z t)
        = (fun t : ℝ => Work.Spaces.DzIter 1 F z t)
          + (fun t : ℝ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2
              (Work.Spaces.DzIter 1 Ψ) z t))
          + (fun t : ℝ => (α * (5 + α)) * Work.Spaces.DzIter 2 Ψ z t) from rfl,
    deriv_add (hd1.add (hd2.const_mul _)) (hd3.const_mul _),
    deriv_add hd1 (hd2.const_mul _),
    deriv_const_mul (α ^ 2) hd2, deriv_const_mul (α * (5 + α)) hd3]

/-! ## 3. `z²∂_z² = D_z² - D_z` for `D_z`-shifts, and the product rule -/

/-- `D_z^1` is additive on differences of `SmoothOpen` data (open-quadrant locality). -/
theorem DzIter_one_sub {F G : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter 1 (fun z θ => F z θ - G z θ) z θ
        = Work.Spaces.DzIter 1 F z θ - Work.Spaces.DzIter 1 G z θ := by
  intro z θ hz h1 h2
  have hdiff : DifferentiableAt ℝ (fun z' => F z' θ) z :=
    (hF.hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
  have hdiff' : DifferentiableAt ℝ (fun z' => G z' θ) z :=
    (hG.hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
  have heq : (fun z' => (fun z θ => F z θ - G z θ) z' θ)
      =ᶠ[𝓝 z] (fun z' => F z' θ - G z' θ) := Filter.Eventually.of_forall (fun _ => rfl)
  simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
    Work.Spaces.pz]
  change z * deriv ((fun z' => F z' θ) - (fun z' => G z' θ)) z
      = z * deriv (fun z' => F z' θ) z - z * deriv (fun z' => G z' θ) z
  rw [deriv_sub hdiff hdiff']
  ring

/-- **`z² ∂_z² Ψ = D_z² Ψ - D_z Ψ`** on the open quadrant, for `SmoothOpen` data. -/
theorem zsq_pzIter2_sub {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
      = Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.DzIter 1 Ψ z θ := by
  have hd1 : DifferentiableAt ℝ (fun z' => Ψ z' θ) z :=
    (hΨ.hasDerivAt_slice hθ hz).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.pz Ψ z' θ) z :=
    (hΨ.hasDerivAt_slice_pzIter 1 hθ hz).differentiableAt
  have h := Work.FTS.EllipticEst.zsq_pzIter2_eq Ψ hd1 hd2
  rw [show Work.Spaces.Dz Ψ = Work.Spaces.DzIter 1 Ψ from rfl] at h
  exact h

/-- **The product rule `z² ∂_z² (D_zΨ) = D_z(z²∂_z²Ψ)`** on the open quadrant. -/
theorem zsq_pzIter2_DzIter_one {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
      = Work.Spaces.DzIter 1 (Abar Ψ) z θ := by
  have hP : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ) := hΨ.DzIter 1
  have hloc : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Abar Ψ z' θ' = Work.Spaces.DzIter 2 Ψ z' θ' - Work.Spaces.DzIter 1 Ψ z' θ' :=
    fun z' θ' hz' h1 h2 => zsq_pzIter2_sub hΨ hz' ⟨h1, h2⟩
  have hcongr := Work.FTS.EllipticEst.SmoothOpen.DzIter_congr (F := Abar Ψ)
    (G := fun z θ => Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.DzIter 1 Ψ z θ) hloc 1
  have hsub := DzIter_one_sub (hΨ.DzIter 2) (hΨ.DzIter 1) z θ hz hθ.1 hθ.2
  have h1 : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
      = Work.Spaces.DzIter 3 Ψ z θ - Work.Spaces.DzIter 2 Ψ z θ :=
    (zsq_pzIter2_sub hP hz hθ).trans rfl
  have h2 : Work.Spaces.DzIter 1 (Abar Ψ) z θ
      = Work.Spaces.DzIter 3 Ψ z θ - Work.Spaces.DzIter 2 Ψ z θ :=
    (hcongr z θ hz hθ.1 hθ.2).trans (hsub.trans rfl)
  rw [h1, h2]

/-! ## 5. The angular derivative functions of the three source pieces -/

noncomputable def pF (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ → ℝ :=
  fun θ => deriv (fun t => Work.Spaces.DzIter 1 F z t) θ
noncomputable def pA (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ → ℝ :=
  fun θ => deriv (fun t => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z t) θ
noncomputable def pDz (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ → ℝ :=
  fun θ => deriv (fun t => Work.Spaces.DzIter 1 Ψ z t) θ
noncomputable def pAb (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ → ℝ :=
  fun θ => deriv (fun t => Abar Ψ z t) θ

/-- `θ ↦ sin(2θ)` is positive on `(0, π/2)`. -/
theorem sin_two_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem continuousOn_sin_two :
    ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) := by
  apply Continuous.continuousOn
  fun_prop

theorem continuousOn_rpow_sin_two (c : ℝ) :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ c) (Set.Ioo 0 (Real.pi / 2)) :=
  continuousOn_sin_two.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_of_mem hθ)))

/-- A function continuous on the open interval is a.e. strongly measurable on `Iθ`. -/
theorem aesm_of_continuousOn_Ioo {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict Iθ) := by
  have h : (MeasureTheory.volume.restrict Iθ : Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine MeasureTheory.Measure.restrict_congr_set ?_
    exact (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2)).symm
  rw [h]
  exact hf.aestronglyMeasurable measurableSet_Ioo

theorem aesm_Wt (α : ℝ) (z : ℝ) :
    MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.Wt α z θ)
      (MeasureTheory.volume.restrict Iθ) := by
  refine aesm_of_continuousOn_Ioo ?_
  have hfun : (fun θ : ℝ => Work.Spaces.Wt α z θ)
      = fun θ : ℝ => Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext θ; rfl
  rw [hfun]
  exact continuousOn_const.mul (continuousOn_rpow_sin_two (-(Work.Spaces.gam α / 2)))

theorem aesm_Sig2 (α : ℝ) :
    MeasureTheory.AEStronglyMeasurable (fun θ => Sig2 α θ)
      (MeasureTheory.volume.restrict Iθ) := by
  refine aesm_of_continuousOn_Ioo ?_
  have hfun : (fun θ : ℝ => Sig2 α θ)
      = fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
    funext θ; rfl
  rw [hfun]
  exact continuousOn_rpow_sin_two (2 - Work.Spaces.gam α)

theorem aesm_mixed_slot_sq {α : ℝ} {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ => (Work.Spaces.mixed 1 1 G z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Iθ) :=
  ((Work.FTS.EllipticEst.remov.ws_aesm_slice (hG.mixed 1 1) hz).mul (aesm_Wt α z)).pow 2

/-- One mixed slot of the `ℋ²`-integrand is integrable on the angular slice. -/
theorem integrableOn_mixed_slot_sq_Iθ {α : ℝ} {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen G) (hm : Work.Spaces.HkMem α 2 G)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.mixed 1 1 G z θ * Work.Spaces.Wt α z θ) ^ 2) Iθ := by
  refine Integrable.mono' (hm.1 z (Set.mem_Ici.mpr hz.le)) (aesm_mixed_slot_sq hG hz) ?_
  filter_upwards with θ
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact Work.Spaces.sq_le_HkIntegrand_mixed α 2 G z θ 1 1 le_rfl (by norm_num)

/-- **The `(0,1)`-slot identity**: `(D_θ G · Wt)² = w(z)²·(∂_θG)²·σ₂` on the open interval. -/
theorem mixed01_Wt_sq_eq {α : ℝ} {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.mixed 0 1 G z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pth G z θ) ^ 2 * Sig2 α θ) := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem hθ
  have hmix : Work.Spaces.mixed 0 1 G z θ = Real.sin (2 * θ) * Work.Spaces.pth G z θ := rfl
  have hW : Work.Spaces.Wt α z θ
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := rfl
  rw [hmix, hW]
  have h := Work.FTS.EllipticEst.H2W.Slot11Src.mul_Wt_sq_key (s := Real.sin (2 * θ))
    (A := Work.Spaces.pth G z θ) (w := Work.Spaces.w z) (γ := Work.Spaces.gam α) hs
  rw [h]
  simp only [Sig2]
  rw [show Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)
      = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) from rfl]
  ring

/-- **The `(1,1)`-slot identity**: `w(z)²·(∂_θ(D_z G))²·σ₂ = (D_zD_θG · Wt)²` on the slice. -/
theorem w_sq_mul_pthDz_eq_slot {α : ℝ} {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen G) {z : ℝ} (hz : 0 < z) :
    (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (deriv (fun t => Work.Spaces.Dz G z t) θ) ^ 2
        * Sig2 α θ)
      = SlotG α G z := by
  rw [SlotG, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
  have h := Work.FTS.EllipticEst.H2W.Slot11Src.mixed11_Wt_sq_eq (α := α) hG z θ hz hθ.1 hθ.2
  show (Work.Spaces.w z) ^ 2 * ((deriv (fun t => Work.Spaces.Dz G z t) θ) ^ 2 * Sig2 α θ)
    = (Work.Spaces.mixed 1 1 G z θ * Work.Spaces.Wt α z θ) ^ 2
  rw [h]
  simp only [Sig2, Work.Spaces.pth, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
  ring

/-- **The `θ`-split of `∂_θ(D_z²Ψ)`**: a.e. in `θ` it is the sum of the two `Z`-slots. -/
theorem pC_eq_pDz_add_pAb {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z : ℝ} (hz : 0 < z) :
    (fun θ => deriv (fun t => Work.Spaces.DzIter 2 Ψ z t) θ)
      =ᵐ[MeasureTheory.volume.restrict Iθ] (fun θ => pDz Ψ z θ + pAb Ψ z θ) := by
  filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
  have hd1 : DifferentiableAt ℝ (fun t => Work.Spaces.DzIter 1 Ψ z t) θ :=
    differentiableAt_slice_θ_open (hΨ.DzIter 1) hz hθ
  have hd2 : DifferentiableAt ℝ (fun t => Abar Ψ z t) θ :=
    differentiableAt_slice_θ_open (smoothOpen_Abar hΨ) hz hθ
  have hev : (fun t => Work.Spaces.DzIter 2 Ψ z t)
      =ᶠ[𝓝 θ] (fun t => Work.Spaces.DzIter 1 Ψ z t + Abar Ψ z t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    have h := zsq_pzIter2_sub hΨ hz ht
    show Work.Spaces.DzIter 2 Ψ z t = Work.Spaces.DzIter 1 Ψ z t + Abar Ψ z t
    rw [Abar_apply]
    linarith [h]
  show deriv (fun t => Work.Spaces.DzIter 2 Ψ z t) θ = pDz Ψ z θ + pAb Ψ z θ
  rw [hev.deriv_eq]
  exact deriv_add hd1 hd2

/-- Nonnegativity of a pure slot. -/
theorem PureZ_nonneg (Ψ : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) : 0 ≤ PureZ Ψ j z :=
  MeasureTheory.integral_nonneg_of_ae (by
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.remov.ws_sEta_nonneg (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)))

/-- Nonnegativity of the source integral. -/
theorem SrcInt_nonneg (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ SrcInt α F Ψ z := by
  rw [SrcInt]
  refine MeasureTheory.integral_nonneg_of_ae ?_
  filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
  refine mul_nonneg (sq_nonneg _) ?_
  exact Sig2_nonneg (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)

/-- Nonnegativity of the source integrand. -/
theorem Src_nonneg (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Iθ) :
    0 ≤ Src α F Ψ z θ :=
  mul_nonneg (sq_nonneg _) (Sig2_nonneg hθ)

/-- The source of the shifted slice, as a `θ`-derivative, a.e. in `θ`. -/
theorem Src_ae_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ} (hz : 0 < z) :
    Src α F Ψ z =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ => (pF F z θ + α ^ 2 * pA Ψ z θ + (α * (5 + α))
          * (pDz Ψ z θ + pAb Ψ z θ)) ^ 2 * Sig2 α θ) := by
  filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo,
    pC_eq_pDz_add_pAb (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth) hz] with θ hθ hpc
  show (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) z t) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)
    = (pF F z θ + α ^ 2 * pA Ψ z θ + (α * (5 + α)) * (pDz Ψ z θ + pAb Ψ z θ)) ^ 2
      * Sig2 α θ
  rw [Gsrc_pth_three h z θ hz hθ, hpc]
  rfl

/-- `(x+y)² ≤ 2(x²+y²)`. -/
theorem sq_add_le_two (x y : ℝ) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (x - y)]

/-- `w z ≥ 1` for `z > 0`. -/
theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  have hz2 : 0 < z ^ 2 := by positivity
  rw [Work.Spaces.w, le_div_iff₀ hz2]
  nlinarith [sq_nonneg (1 + z), hz]

/-- **The two `Z`-slot inequalities** (`Work.H2W.slot01ZTBound`). -/
theorem ztSlots : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz), 0 < z →
      (ZT α Ψ z ≤ C * (PureZ Ψ 1 z + PureZ Ψ 2 z)) ∧ (ZD α Ψ z ≤ C * PureZ Ψ 1 z) :=
  Work.H2W.slot01ZTBound

/-- **The `D_zΨ`-slot is `L¹` on the angular slice.** -/
theorem ztDzIntegrable {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ z, 0 < z →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun θ' => Work.Spaces.DzIter 1 Ψ z θ') θ) ^ 2 * Sig2 α θ) Iθ := by
  intro z hz
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hcinf : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => Work.Spaces.DzIter 1 Ψ z θ)
      (Set.Ioo 0 (Real.pi / 2)) := fun n =>
    contDiffOn_iff_forall_nat_le.mp ((hΨ.DzIter 1).curry_θ hz) n le_top
  have hcont : ContinuousOn (fun θ => Work.Spaces.DzIter 1 Ψ z θ) Iθ :=
    (Work.H2W.weakSliceContinuousKit α F Ψ hα hα4 h z hz).2
  have h0 : (fun θ => Work.Spaces.DzIter 1 Ψ z θ) 0 = 0 :=
    Work.FTS.EllipticEst.TT.DzIter_zero_at_zero Ψ 1 h.zero z
  have hpi : (fun θ => Work.Spaces.DzIter 1 Ψ z θ) (Real.pi / 2) = 0 :=
    Work.FTS.EllipticEst.TT.DzIter_zero_at_pi_half Ψ 1 h.pi_half z
  have hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Work.Spaces.DzIter 1 Ψ z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Iθ := Work.H2W.dzpsi_second_sq h hz
  obtain ⟨hbdd, _⟩ := Work.FTS.EllipticEst.H2W.weakSliceDerivBound
    (fun θ => Work.Spaces.DzIter 1 Ψ z θ) hcinf hcont h0 hpi hint
  set A : ℝ := ∫ θ in Iθ, (deriv (fun t => deriv (fun θ' => Work.Spaces.DzIter 1 Ψ z θ') t) θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ with hA
  set B : ℝ := ∫ θ in Iθ, Real.sin (2 * θ) ^ Work.Spaces.eta with hB
  refine Integrable.mono' (g := fun _ : ℝ => |A * B|)
    (MeasureTheory.integrableOn_const Work.FTS.EllipticEst.remov.ws_vol_Iθ_ne_top) ?_ ?_
  · refine (((Work.FTS.EllipticEst.remov.ws_aesm_slice ((hΨ.DzIter 1).pth) hz).pow 2).mul
      (aesm_Sig2 α))
  · filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    have hs : 0 ≤ Real.sin (2 * θ) := le_of_lt (sin_two_pos_of_mem hθ)
    have hσ1 : Sig2 α θ ≤ 1 := by
      rw [Sig2]
      exact Real.rpow_le_one hs (Real.sin_le_one _)
        (by rw [Work.Spaces.gam]; linarith [hα4])
    have hσ0 : 0 ≤ Sig2 α θ := Sig2_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hσ0)]
    calc (deriv (fun θ' => Work.Spaces.DzIter 1 Ψ z θ') θ) ^ 2 * Sig2 α θ
        ≤ (deriv (fun θ' => Work.Spaces.DzIter 1 Ψ z θ') θ) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hσ1 (sq_nonneg _)
      _ = (deriv (fun θ' => Work.Spaces.DzIter 1 Ψ z θ') θ) ^ 2 := by ring_nf
      _ ≤ A * B := hbdd θ hθ
      _ ≤ |A * B| := le_abs_self _

/-- **The `A`-slot is `L¹` on the angular slice, a.e. in `z`.** -/
theorem ztAIntegrableAe {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz), 0 < z →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun θ' => Abar Ψ z θ') θ) ^ 2 * Sig2 α θ) Iθ := by
  have hA : Work.FTS.EllipticEst.SmoothOpen (Abar Ψ) :=
    smoothOpen_Abar (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth)
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz hzpos
  have hkey : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.w z) ^ 2
        * ((deriv (fun θ' => Abar Ψ z θ') θ) ^ 2 * Sig2 α θ)) Iθ := by
    refine Integrable.mono' (h.memA.1 z hz) ?_ ?_
    · refine (((Work.FTS.EllipticEst.remov.ws_aesm_slice (hA.pth) hzpos).pow 2).mul
        (aesm_Sig2 α)).const_mul _
    · filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      have hσ0 : 0 ≤ Sig2 α θ := Sig2_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hσ0))]
      have hmix := mixed01_Wt_sq_eq (α := α) (G := Abar Ψ) (z := z) hθ
      have hle := Work.Spaces.sq_le_HkIntegrand_mixed α 2 (Abar Ψ) z θ 1 0
        (le_refl 1) (by norm_num)
      calc (Work.Spaces.w z) ^ 2 * ((deriv (fun θ' => Abar Ψ z θ') θ) ^ 2 * Sig2 α θ)
          = (Work.Spaces.mixed 0 1 (Abar Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2 := hmix.symm
        _ ≤ Work.Spaces.HkIntegrand α 2 (Abar Ψ) z θ := hle
  have hw2 : (0 : ℝ) < (Work.Spaces.w z) ^ 2 := by
    have := one_le_w hzpos
    positivity
  refine (hkey.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
  filter_upwards with θ
  rw [inv_mul_cancel_left₀ (ne_of_gt hw2)]

/-- **The per-slice bound of the source integral.** -/
theorem srcInt_bound_ae {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {C : ℝ} (hC : 0 < C)
    (hZT : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz), 0 < z →
      (ZT α Ψ z ≤ C * (PureZ Ψ 1 z + PureZ Ψ 2 z)) ∧ (ZD α Ψ z ≤ C * PureZ Ψ 1 z)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz), 0 < z →
      (Work.Spaces.w z) ^ 2 * SrcInt α F Ψ z
        ≤ 3 * SlotG α F z + 3 * α ^ 4 * SlotG α (Abar Ψ) z
          + 12 * C * ((Work.Spaces.w z) ^ 2 * (2 * PureZ Ψ 1 z + PureZ Ψ 2 z)) := by
  have hF : Work.FTS.EllipticEst.SmoothOpen F := smoothOpen_source h
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hA : Work.FTS.EllipticEst.SmoothOpen (Abar Ψ) := smoothOpen_Abar hΨ
  filter_upwards [hZT, ztAIntegrableAe hα hα4 h] with z hzt hAbInt
  intro hz
  obtain ⟨hZD, hZT'⟩ := hzt hz
  have hDzInt : MeasureTheory.IntegrableOn
      (fun θ => (pDz Ψ z θ) ^ 2 * Sig2 α θ) Iθ := ztDzIntegrable hα hα4 h z hz
  have hAbInt' : MeasureTheory.IntegrableOn
      (fun θ => (pAb Ψ z θ) ^ 2 * Sig2 α θ) Iθ := hAbInt hz
  have hw2 : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hα2 : (0 : ℝ) ≤ (α * (5 + α)) ^ 2 := sq_nonneg _
  -- ### the four integrands
  set e₁ : ℝ → ℝ := fun θ => (Work.Spaces.w z) ^ 2 * ((pF F z θ) ^ 2 * Sig2 α θ) with he₁
  set e₂ : ℝ → ℝ := fun θ => (Work.Spaces.w z) ^ 2 * ((pA Ψ z θ) ^ 2 * Sig2 α θ) with he₂
  set e₃ : ℝ → ℝ := fun θ => (Work.Spaces.w z) ^ 2 * ((pDz Ψ z θ) ^ 2 * Sig2 α θ) with he₃
  set e₄ : ℝ → ℝ := fun θ => (Work.Spaces.w z) ^ 2 * ((pAb Ψ z θ) ^ 2 * Sig2 α θ) with he₄
  have hInt1 : MeasureTheory.IntegrableOn e₁ Iθ := by
    rw [he₁]
    refine (integrableOn_mixed_slot_sq_Iθ hF h.memF hz).congr ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    have hwide := Work.FTS.EllipticEst.H2W.Slot11Src.mixed11_Wt_sq_eq (α := α) hF z θ hz hθ.1 hθ.2
    show (Work.Spaces.mixed 1 1 F z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((pF F z θ) ^ 2 * Sig2 α θ)
    rw [hwide]
    simp only [Sig2, pF, Work.Spaces.pth, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
    ring
  have hpAeq : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      pA Ψ z θ = deriv (fun t => Work.Spaces.DzIter 1 (Abar Ψ) z t) θ := by
    intro θ hθ
    have hev : (fun t => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z t)
        =ᶠ[𝓝 θ] (fun t => Work.Spaces.DzIter 1 (Abar Ψ) z t) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
      exact zsq_pzIter2_DzIter_one hΨ hz ht
    exact hev.deriv_eq
  have hInt2 : MeasureTheory.IntegrableOn e₂ Iθ := by
    rw [he₂]
    refine (integrableOn_mixed_slot_sq_Iθ hA h.memA hz).congr ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    have hwide := Work.FTS.EllipticEst.H2W.Slot11Src.mixed11_Wt_sq_eq (α := α) hA z θ hz hθ.1 hθ.2
    show (Work.Spaces.mixed 1 1 (Abar Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((pA Ψ z θ) ^ 2 * Sig2 α θ)
    rw [hwide, hpAeq θ hθ]
    simp only [Sig2, Work.Spaces.pth]
    ring
  have hInt3 : MeasureTheory.IntegrableOn e₃ Iθ := by
    rw [he₃]
    refine (hDzInt.const_mul ((Work.Spaces.w z) ^ 2)).congr ?_
    filter_upwards with θ
    ring
  have hInt4 : MeasureTheory.IntegrableOn e₄ Iθ := by
    rw [he₄]
    refine (hAbInt'.const_mul ((Work.Spaces.w z) ^ 2)).congr ?_
    filter_upwards with θ
    ring
  -- ### the grouped majorant
  set M : ℝ → ℝ := fun θ => (3 * e₁ θ + 3 * α ^ 4 * e₂ θ)
    + (6 * (α * (5 + α)) ^ 2 * e₃ θ + 6 * (α * (5 + α)) ^ 2 * e₄ θ) with hM
  -- ### the pointwise bound, a.e. in `θ`
  have hpt : (fun θ => (Work.Spaces.w z) ^ 2 * Src α F Ψ z θ) ≤ᵐ[MeasureTheory.volume.restrict Iθ] M := by
    filter_upwards [Src_ae_eq h hz, Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hsrc hθ
    have hσ : 0 ≤ Sig2 α θ := Sig2_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have h1 := sq_add_three_le (pF F z θ) (α ^ 2 * pA Ψ z θ)
      ((α * (5 + α)) * (pDz Ψ z θ + pAb Ψ z θ))
    have h2 : (α ^ 2 * pA Ψ z θ) ^ 2 = α ^ 4 * (pA Ψ z θ) ^ 2 := by ring
    have h3 : ((α * (5 + α)) * (pDz Ψ z θ + pAb Ψ z θ)) ^ 2
        ≤ (α * (5 + α)) ^ 2 * (2 * ((pDz Ψ z θ) ^ 2 + (pAb Ψ z θ) ^ 2)) := by
      calc ((α * (5 + α)) * (pDz Ψ z θ + pAb Ψ z θ)) ^ 2
          = (α * (5 + α)) ^ 2 * (pDz Ψ z θ + pAb Ψ z θ) ^ 2 := by ring
        _ ≤ (α * (5 + α)) ^ 2 * (2 * ((pDz Ψ z θ) ^ 2 + (pAb Ψ z θ) ^ 2)) :=
            mul_le_mul_of_nonneg_left (sq_add_le_two _ _) hα2
    have hkey : (pF F z θ + α ^ 2 * pA Ψ z θ
        + (α * (5 + α)) * (pDz Ψ z θ + pAb Ψ z θ)) ^ 2
        ≤ 3 * (pF F z θ) ^ 2 + 3 * α ^ 4 * (pA Ψ z θ) ^ 2
          + 6 * (α * (5 + α)) ^ 2 * ((pDz Ψ z θ) ^ 2 + (pAb Ψ z θ) ^ 2) := by
      nlinarith [h1, h2, h3]
    rw [hsrc, hM, he₁, he₂, he₃, he₄]
    calc (Work.Spaces.w z) ^ 2
          * ((pF F z θ + α ^ 2 * pA Ψ z θ
              + (α * (5 + α)) * (pDz Ψ z θ + pAb Ψ z θ)) ^ 2 * Sig2 α θ)
        ≤ (Work.Spaces.w z) ^ 2
            * ((3 * (pF F z θ) ^ 2 + 3 * α ^ 4 * (pA Ψ z θ) ^ 2
              + 6 * (α * (5 + α)) ^ 2 * ((pDz Ψ z θ) ^ 2 + (pAb Ψ z θ) ^ 2)) * Sig2 α θ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkey hσ) hw2
      _ = _ := by ring
  -- ### the majorant is integrable
  have hIntSum : MeasureTheory.IntegrableOn M Iθ := by
    rw [hM]
    exact ((hInt1.const_mul 3).add (hInt2.const_mul (3 * α ^ 4))).add
      ((hInt3.const_mul (6 * (α * (5 + α)) ^ 2)).add
        (hInt4.const_mul (6 * (α * (5 + α)) ^ 2)))
  have hint : (∫ θ in Iθ, (Work.Spaces.w z) ^ 2 * Src α F Ψ z θ) ≤ ∫ θ in Iθ, M θ :=
    MeasureTheory.integral_mono_of_nonneg
      (by filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
          exact mul_nonneg hw2 (Src_nonneg α F Ψ z θ (Set.mem_Icc.mpr
            ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))) hIntSum hpt
  -- ### split the integral
  have hsplit : (∫ θ in Iθ, M θ)
      = 3 * (∫ θ in Iθ, e₁ θ) + 3 * α ^ 4 * (∫ θ in Iθ, e₂ θ)
        + 6 * (α * (5 + α)) ^ 2 * (∫ θ in Iθ, e₃ θ)
        + 6 * (α * (5 + α)) ^ 2 * (∫ θ in Iθ, e₄ θ) := by
    rw [hM]
    rw [MeasureTheory.integral_add]
    rw [MeasureTheory.integral_add]
    rw [MeasureTheory.integral_add]
    rw [MeasureTheory.integral_const_mul (3 : ℝ) _,
        MeasureTheory.integral_const_mul (3 * α ^ 4) _,
        MeasureTheory.integral_const_mul (6 * (α * (5 + α)) ^ 2) _,
        MeasureTheory.integral_const_mul (6 * (α * (5 + α)) ^ 2) _]
    ring
    all_goals first
      | exact hInt1.const_mul 3
      | exact hInt2.const_mul (3 * α ^ 4)
      | exact hInt3.const_mul (6 * (α * (5 + α)) ^ 2)
      | exact hInt4.const_mul (6 * (α * (5 + α)) ^ 2)
      | exact (hInt1.const_mul 3).add (hInt2.const_mul (3 * α ^ 4))
      | exact (hInt3.const_mul (6 * (α * (5 + α)) ^ 2)).add
          (hInt4.const_mul (6 * (α * (5 + α)) ^ 2))
  -- ### identify the four integrals
  have he1val : (∫ θ in Iθ, e₁ θ) = SlotG α F z := by
    rw [he₁]
    rw [MeasureTheory.integral_const_mul]
    exact w_sq_mul_pthDz_eq_slot hF hz
  have he2val : (∫ θ in Iθ, e₂ θ) = SlotG α (Abar Ψ) z := by
    rw [he₂, MeasureTheory.integral_const_mul]
    have hcongr : (∫ θ in Iθ, (pA Ψ z θ) ^ 2 * Sig2 α θ)
        = ∫ θ in Iθ, (deriv (fun t => Work.Spaces.Dz (Abar Ψ) z t) θ) ^ 2 * Sig2 α θ := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      rw [hpAeq θ hθ]
      rfl
    rw [hcongr]
    exact w_sq_mul_pthDz_eq_slot (α := α) hA hz
  have he3val : (∫ θ in Iθ, e₃ θ) = (Work.Spaces.w z) ^ 2 * ZD α Ψ z := by
    rw [he₃]
    exact MeasureTheory.integral_const_mul _ _
  have he4val : (∫ θ in Iθ, e₄ θ) = (Work.Spaces.w z) ^ 2 * ZT α Ψ z := by
    rw [he₄]
    exact MeasureTheory.integral_const_mul _ _
  have hmain : (Work.Spaces.w z) ^ 2 * SrcInt α F Ψ z
      ≤ 3 * SlotG α F z + 3 * α ^ 4 * SlotG α (Abar Ψ) z
        + 6 * (α * (5 + α)) ^ 2 * ((Work.Spaces.w z) ^ 2 * (ZD α Ψ z + ZT α Ψ z)) := by
    have hSrc : (Work.Spaces.w z) ^ 2 * SrcInt α F Ψ z
        = ∫ θ in Iθ, (Work.Spaces.w z) ^ 2 * Src α F Ψ z θ := by
      rw [SrcInt]
      exact (MeasureTheory.integral_const_mul ((Work.Spaces.w z) ^ 2) (Src α F Ψ z)).symm
    rw [hSrc]
    calc (∫ θ in Iθ, (Work.Spaces.w z) ^ 2 * Src α F Ψ z θ)
        ≤ ∫ θ in Iθ, M θ := hint
      _ = 3 * (∫ θ in Iθ, e₁ θ) + 3 * α ^ 4 * (∫ θ in Iθ, e₂ θ)
          + 6 * (α * (5 + α)) ^ 2 * (∫ θ in Iθ, e₃ θ)
          + 6 * (α * (5 + α)) ^ 2 * (∫ θ in Iθ, e₄ θ) := hsplit
      _ = 3 * SlotG α F z + 3 * α ^ 4 * SlotG α (Abar Ψ) z
          + 6 * (α * (5 + α)) ^ 2 * ((Work.Spaces.w z) ^ 2 * ZD α Ψ z)
          + 6 * (α * (5 + α)) ^ 2 * ((Work.Spaces.w z) ^ 2 * ZT α Ψ z) := by
          rw [he1val, he2val, he3val, he4val]
      _ = 3 * SlotG α F z + 3 * α ^ 4 * SlotG α (Abar Ψ) z
          + 6 * (α * (5 + α)) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (ZD α Ψ z + ZT α Ψ z)) := by
          ring
  -- ### bound the `Z`-slots
  have hcoef : 6 * (α * (5 + α)) ^ 2 * C ≤ 12 * C := by
    have hx : α * (5 + α) ≤ 21 / 16 := by nlinarith [hα, hα4]
    have hx0 : 0 ≤ α * (5 + α) := by nlinarith [hα]
    have h2 : (α * (5 + α)) ^ 2 ≤ 2 := by nlinarith [hx, hx0]
    nlinarith [h2, hC]
  have hZ : ZD α Ψ z + ZT α Ψ z ≤ C * (2 * PureZ Ψ 1 z + PureZ Ψ 2 z) := by
    have hp1 := PureZ_nonneg Ψ 1 z
    have hp2 := PureZ_nonneg Ψ 2 z
    linarith [hZD, hZT']
  have hZnn : 0 ≤ 2 * PureZ Ψ 1 z + PureZ Ψ 2 z := by
    have hp1 := PureZ_nonneg Ψ 1 z
    have hp2 := PureZ_nonneg Ψ 2 z
    linarith
  have hstep : 6 * (α * (5 + α)) ^ 2 * ((Work.Spaces.w z) ^ 2 * (ZD α Ψ z + ZT α Ψ z))
      ≤ 12 * C * ((Work.Spaces.w z) ^ 2 * (2 * PureZ Ψ 1 z + PureZ Ψ 2 z)) := by
    have h1 : (Work.Spaces.w z) ^ 2 * (ZD α Ψ z + ZT α Ψ z)
        ≤ (Work.Spaces.w z) ^ 2 * (C * (2 * PureZ Ψ 1 z + PureZ Ψ 2 z)) :=
      mul_le_mul_of_nonneg_left hZ hw2
    calc 6 * (α * (5 + α)) ^ 2 * ((Work.Spaces.w z) ^ 2 * (ZD α Ψ z + ZT α Ψ z))
        ≤ 6 * (α * (5 + α)) ^ 2
            * ((Work.Spaces.w z) ^ 2 * (C * (2 * PureZ Ψ 1 z + PureZ Ψ 2 z))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (6 * (α * (5 + α)) ^ 2 * C) * ((Work.Spaces.w z) ^ 2
            * (2 * PureZ Ψ 1 z + PureZ Ψ 2 z)) := by ring
      _ ≤ 12 * C * ((Work.Spaces.w z) ^ 2 * (2 * PureZ Ψ 1 z + PureZ Ψ 2 z)) :=
          mul_le_mul_of_nonneg_right hcoef (mul_nonneg hw2 hZnn)
  linarith [hmain, hstep]

/-! ## 7. The `z`-integrals of the right-hand side slots -/

/-- The mixed slot of `G`, integrated in `z`, is the `L²`-square of the slot. -/
theorem slot_z_eq_L2Sq (α : ℝ) (G : ℝ → ℝ → ℝ) :
    (∫ z in Iz, SlotG α G z)
      = Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 1 1 G z θ * Work.Spaces.Wt α z θ) := rfl

/-- **The pure slots as `z`-integrals of `L²`-norms.** -/
theorem PureZ_eq_L2Sq (Ψ : ℝ → ℝ → ℝ) (j : ℕ) :
    (∫ z in Iz, (Work.Spaces.w z) ^ 2 * PureZ Ψ j z)
      = Work.Spaces.L2Sq (fun z θ => Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) := by
  rw [Work.Spaces.L2Sq]
  simp only [PureZ]
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
  show (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ)
    = ∫ θ in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem hθ
  rw [sq_div_rpow_eta (A := Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ)
    (wv := Work.Spaces.w z) (s := Real.sin (2 * θ)) hs.le]
  simp only [Work.FTS.EllipticEst.sEta]
  ring

/-- **The pure slots are honest in `z`.** -/
theorem PureZ_integrable {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (j : ℕ) (hj : j ≤ 2) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * PureZ Ψ j z) Iz := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have h0 := Work.FTS.EllipticEst.integrableOn_slice_Iz α 2 (hΨ.pth.pth) h.memB j hj
  refine h0.congr ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz
  by_cases hz0 : z = 0
  · subst hz0
    have hw0 : Work.Spaces.w (0 : ℝ) = 0 := by simp [Work.Spaces.w]
    simp only [PureZ]
    rw [hw0]
    simp
  · have hzpos : 0 < z := lt_of_le_of_ne (Set.mem_Ici.mp hz) (Ne.symm hz0)
    simp only [PureZ]
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem hθ
    rw [sq_div_rpow_eta (A := Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.pth Ψ)) z θ)
      (wv := Work.Spaces.w z) (s := Real.sin (2 * θ)) hs.le]
    rw [Work.FTS.EllipticEst.remov.ws_pthIter_two_DzIter hΨ j hzpos hθ]
    simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
      Work.FTS.EllipticEst.sEta]
    ring

/-- Almost every `z ∈ Iz` is positive. -/
theorem ae_pos_Iz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz), 0 < z := by
  rw [MeasureTheory.ae_iff]
  have hset : {z : ℝ | ¬ (0 < z)} = Set.Iic 0 := by
    ext z; simp only [Set.mem_setOf_eq, not_lt, Set.mem_Iic]
  rw [hset, MeasureTheory.Measure.restrict_apply measurableSet_Iic]
  have hinter : Set.Iic (0 : ℝ) ∩ Iz = {(0 : ℝ)} := by
    ext z
    constructor
    · intro hz
      exact le_antisymm hz.1 hz.2
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      simp only [Set.mem_inter_iff, Set.mem_Iic, Work.Spaces.Iz, Set.mem_Ici]
      exact ⟨le_refl 0, le_refl 0⟩
  rw [hinter]
  simp

/-! ## 8. The target -/

/-- FINITENESS AND BOUND OF THE `z`-INTEGRAL OF THE SOURCE TERM of the shifted slice. -/
theorem srcBound : ∃ K : ℝ, 0 < K ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α
              (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) z t) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))) Work.Spaces.Iz
      ∧ (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α
              (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) z t) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)))
        ≤ K * ((∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
                Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
            + Work.Spaces.HkSq α 2 F
            + α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
                Work.Spaces.mixed 1 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
                  * Work.Spaces.Wt α z θ)) := by
  obtain ⟨C, hCpos, hZT0⟩ := ztSlots
  refine ⟨32 * C + 8, by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  have hF : Work.FTS.EllipticEst.SmoothOpen F := smoothOpen_source h
  have hA : Work.FTS.EllipticEst.SmoothOpen (Abar Ψ) :=
    smoothOpen_Abar (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth)
  have hpt := srcInt_bound_ae hα hα4 h hCpos (hZT0 α F Ψ hα hα4 h)
  have hIntF : MeasureTheory.IntegrableOn (fun z => SlotG α F z) Iz :=
    Work.FTS.EllipticEst.H2W.Slot11Src.integrableOn_mixed_slot_sq α 2 hF h.memF 1 1 le_rfl
      (by norm_num)
  have hIntA : MeasureTheory.IntegrableOn (fun z => SlotG α (Abar Ψ) z) Iz :=
    Work.FTS.EllipticEst.H2W.Slot11Src.integrableOn_mixed_slot_sq α 2 hA h.memA 1 1 le_rfl
      (by norm_num)
  have hIntP1 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * PureZ Ψ 1 z) Iz :=
    PureZ_integrable h 1 (by norm_num)
  have hIntP2 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * PureZ Ψ 2 z) Iz :=
    PureZ_integrable h 2 (by norm_num)
  -- ### the split majorant of the `z`-integral
  set Gmaj : ℝ → ℝ := fun z => (3 * SlotG α F z + 3 * α ^ 4 * SlotG α (Abar Ψ) z)
      + (24 * C * ((Work.Spaces.w z) ^ 2 * PureZ Ψ 1 z)
        + 12 * C * ((Work.Spaces.w z) ^ 2 * PureZ Ψ 2 z)) with hGmaj
  have hIntG : MeasureTheory.IntegrableOn Gmaj Iz := by
    rw [hGmaj]
    exact ((hIntF.const_mul 3).add (hIntA.const_mul (3 * α ^ 4))).add
      ((hIntP1.const_mul (24 * C)).add (hIntP2.const_mul (12 * C)))
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => (Work.Spaces.w z) ^ 2 * SrcInt α F Ψ z) (MeasureTheory.volume.restrict Iz) :=
    Work.FTS.EllipticEst.H2W.Slot11Src.aesm_pth_sq_int α (smoothOpen_Gsrc h)
  have hbnd : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz),
      (Work.Spaces.w z) ^ 2 * SrcInt α F Ψ z ≤ Gmaj z := by
    filter_upwards [hpt, ae_pos_Iz] with z hz1 hz2
    have hGz : Gmaj z = (3 * SlotG α F z + 3 * α ^ 4 * SlotG α (Abar Ψ) z)
        + (24 * C * ((Work.Spaces.w z) ^ 2 * PureZ Ψ 1 z)
          + 12 * C * ((Work.Spaces.w z) ^ 2 * PureZ Ψ 2 z)) := by rw [hGmaj]
    rw [hGz]
    calc (Work.Spaces.w z) ^ 2 * SrcInt α F Ψ z
        ≤ 3 * SlotG α F z + 3 * α ^ 4 * SlotG α (Abar Ψ) z
          + 12 * C * ((Work.Spaces.w z) ^ 2 * (2 * PureZ Ψ 1 z + PureZ Ψ 2 z)) := hz1 hz2
      _ = (3 * SlotG α F z + 3 * α ^ 4 * SlotG α (Abar Ψ) z)
          + (24 * C * ((Work.Spaces.w z) ^ 2 * PureZ Ψ 1 z)
            + 12 * C * ((Work.Spaces.w z) ^ 2 * PureZ Ψ 2 z)) := by ring
  have hint : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * SrcInt α F Ψ z) Iz := by
    refine Integrable.mono' hIntG haesm ?_
    filter_upwards [hbnd] with z hz
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (SrcInt_nonneg α F Ψ z))]
    exact hz
  refine ⟨hint, ?_⟩
  have hle := MeasureTheory.integral_mono_of_nonneg
    (f := fun z => (Work.Spaces.w z) ^ 2 * SrcInt α F Ψ z) (g := Gmaj)
    (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (SrcInt_nonneg α F Ψ z)) hIntG hbnd
  have hsplit : (∫ z in Iz, Gmaj z)
      = 3 * (∫ z in Iz, SlotG α F z) + 3 * α ^ 4 * (∫ z in Iz, SlotG α (Abar Ψ) z)
        + 24 * C * (∫ z in Iz, (Work.Spaces.w z) ^ 2 * PureZ Ψ 1 z)
        + 12 * C * (∫ z in Iz, (Work.Spaces.w z) ^ 2 * PureZ Ψ 2 z) := by
    rw [hGmaj]
    rw [MeasureTheory.integral_add]
    rw [MeasureTheory.integral_add]
    rw [MeasureTheory.integral_add]
    rw [MeasureTheory.integral_const_mul (3 : ℝ) _,
        MeasureTheory.integral_const_mul (3 * α ^ 4) _,
        MeasureTheory.integral_const_mul (24 * C) _,
        MeasureTheory.integral_const_mul (12 * C) _]
    ring
    all_goals first
      | exact hIntF.const_mul 3
      | exact hIntA.const_mul (3 * α ^ 4)
      | exact hIntP1.const_mul (24 * C)
      | exact hIntP2.const_mul (12 * C)
      | exact (hIntF.const_mul 3).add (hIntA.const_mul (3 * α ^ 4))
      | exact (hIntP1.const_mul (24 * C)).add (hIntP2.const_mul (12 * C))
  rw [hsplit] at hle
  -- ### the right-hand side of the statement, in named parts
  set G0 : ℝ := Work.Spaces.L2Sq (fun z θ => Work.Spaces.pthIter 2 (Work.Spaces.DzIter 0 Ψ) z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) with hG0
  set G1 : ℝ := Work.Spaces.L2Sq (fun z θ => Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) with hG1
  set G2 : ℝ := Work.Spaces.L2Sq (fun z θ => Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) with hG2
  set HK : ℝ := Work.Spaces.HkSq α 2 F with hHK
  set LA : ℝ := Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 1 1
    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * Work.Spaces.Wt α z θ) with hLA
  have hp1 : (∫ z in Iz, (Work.Spaces.w z) ^ 2 * PureZ Ψ 1 z) = G1 := PureZ_eq_L2Sq Ψ 1
  have hp2 : (∫ z in Iz, (Work.Spaces.w z) ^ 2 * PureZ Ψ 2 z) = G2 := PureZ_eq_L2Sq Ψ 2
  have hAle : (∫ z in Iz, SlotG α (Abar Ψ) z) = LA := rfl
  rw [hp1, hp2, hAle] at hle
  have hFle : (∫ z in Iz, SlotG α F z) ≤ HK :=
    Work.Spaces.L2Sq_mixed_le_HkSq α 2 F h.memF 1 1 le_rfl (by norm_num)
  have hsum : (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
      = G0 + G1 + G2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  have hL2nn : ∀ g : ℝ → ℝ → ℝ, 0 ≤ Work.Spaces.L2Sq g := fun g => by
    rw [Work.Spaces.L2Sq]
    exact MeasureTheory.integral_nonneg_of_ae (Eventually.of_forall fun _ =>
      MeasureTheory.integral_nonneg_of_ae (Eventually.of_forall fun _ => sq_nonneg _))
  have hHKnn : 0 ≤ HK := by
    rw [hHK, Work.Spaces.HkSq]
    exact MeasureTheory.integral_nonneg_of_ae (Eventually.of_forall fun _ =>
      MeasureTheory.integral_nonneg_of_ae (Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 2 F _ θ))
  have hG0nn : 0 ≤ G0 := by rw [hG0]; exact hL2nn _
  have hG1nn : 0 ≤ G1 := by rw [hG1]; exact hL2nn _
  have hG2nn : 0 ≤ G2 := by rw [hG2]; exact hL2nn _
  have hLAnn : 0 ≤ LA := by rw [hLA]; exact hL2nn _
  have ha4 : 0 ≤ α ^ 4 := pow_nonneg hα.le 4
  rw [hsum]
  have hK3 : (3 : ℝ) ≤ 32 * C + 8 := by linarith
  have hK24 : 24 * C ≤ 32 * C + 8 := by linarith
  have hK12 : 12 * C ≤ 32 * C + 8 := by linarith
  have hKpos : (0 : ℝ) < 32 * C + 8 := by linarith
  have hA1 : 3 * (∫ z in Iz, SlotG α F z) ≤ (32 * C + 8) * HK :=
    le_trans (mul_le_mul_of_nonneg_left hFle (by norm_num))
      (mul_le_mul_of_nonneg_right hK3 hHKnn)
  have hA2 : 3 * α ^ 4 * LA ≤ (32 * C + 8) * (α ^ 4 * LA) := by
    have h0 : (0 : ℝ) ≤ α ^ 4 * LA := mul_nonneg ha4 hLAnn
    have h := mul_le_mul_of_nonneg_right hK3 h0
    linarith [h]
  have hA3 : 24 * C * G1 ≤ (32 * C + 8) * G1 := mul_le_mul_of_nonneg_right hK24 hG1nn
  have hA4 : 12 * C * G2 ≤ (32 * C + 8) * G2 := mul_le_mul_of_nonneg_right hK12 hG2nn
  have hA5 : 0 ≤ (32 * C + 8) * G0 := mul_nonneg hKpos.le hG0nn
  refine le_trans hle ?_
  linarith [hA1, hA2, hA3, hA4, hA5]

end Work.FTS.EllipticEst.TT.Slot11
