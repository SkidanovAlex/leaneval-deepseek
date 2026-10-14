import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS_FinalLeaves.mu6_proved
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS_RegExport.RXR5.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp Jet gSlice)

set_option autoImplicit false

/-- The sanitised right-Taylor family of `R5Parts`. -/
abbrev SG (α : ℝ) (g : Fam) : Fam := Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)

/-- The stream function fed to `R5Parts`. -/
abbrev SΨ (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) : Fam :=
  Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)

/-- Two `Fn`'s agree on the open quadrant. -/
def AgreeOnQ (a b : Fn) : Prop := ∀ z θ, 0 < z → 0 < θ → θ < π/2 → a z θ = b z θ

theorem AgreeOnQ.refl (a : Fn) : AgreeOnQ a a := fun _ _ _ _ _ => rfl

theorem AgreeOnQ.symm {a b : Fn} (h : AgreeOnQ a b) : AgreeOnQ b a :=
  fun z θ hz hθ hθ2 => (h z θ hz hθ hθ2).symm

theorem AgreeOnQ.trans {a b c : Fn} (h₁ : AgreeOnQ a b) (h₂ : AgreeOnQ b c) : AgreeOnQ a c :=
  fun z θ hz hθ hθ2 => (h₁ z θ hz hθ hθ2).trans (h₂ z θ hz hθ hθ2)

/-! ## §1 The sanitised family -/

theorem SG_apply_of_pos {α z θ τ : ℝ} {g : Fam} (hz : 0 < z) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ π / 2) :
    SG α g z θ τ = Work.FTS.FinalV2.tauExt g z θ τ := by
  simp only [SG, Work.FTS.FinalV2.gS, hz, if_true, hθ0, hθ1, and_self, ↓reduceIte]

theorem SG_apply_of_nonpos {α z θ τ : ℝ} {g : Fam} (hz : z ≤ 0) : SG α g z θ τ = 0 := by
  simp only [SG, Work.FTS.FinalV2.gS, if_neg (not_lt.mpr hz)]


/-- The slice of the sanitised family agrees with the slice of `tauExt g` on the quadrant. -/
theorem SG_slice_agreeOnQ (α : ℝ) (g : Fam) (τ : ℝ) :
    AgreeOnQ (slice (SG α g) τ) (slice (Work.FTS.FinalV2.tauExt g) τ) := by
  intro z θ hz hθ hθ2
  exact SG_apply_of_pos hz hθ.le hθ2.le

/-- The stream function of `R5Parts` agrees with the canonical one on the quadrant. -/
theorem SΨ_slice_agreeOnQ (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ : ℝ) :
    AgreeOnQ (slice (SΨ α Φs E g) τ) (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.FinalV2.tauExt g)) τ) := by
  intro z θ hz hθ hθ2
  exact Work.FTS.RegExportIface.psiR_of_mem (α := α) (Φs := Φs) (E := E)
    (G := Work.FTS.FinalV2.tauExt g) hz hθ hθ2

/-! ## §2 Derivative congruence on the open quadrant -/

theorem pz_congr_of_agreeOnQ {a b : Fn} (h : AgreeOnQ a b) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Spaces.pz a z θ = Work.Spaces.pz b z θ := by
  show deriv (fun z' => a z' θ) z = deriv (fun z' => b z' θ) z
  exact Filter.EventuallyEq.deriv_eq (by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi hz] with z' hz'
    exact h z' θ hz' hθ hθ2)

theorem pth_congr_of_agreeOnQ {a b : Fn} (h : AgreeOnQ a b) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Spaces.pth a z θ = Work.Spaces.pth b z θ := by
  show deriv (fun θ' => a z θ') θ = deriv (fun θ' => b z θ') θ
  exact Filter.EventuallyEq.deriv_eq (by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo ⟨hθ, hθ2⟩] with θ' hθ'
    exact h z θ' hz hθ'.1 hθ'.2)

theorem Dz_congr_of_agreeOnQ {a b : Fn} (h : AgreeOnQ a b) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Spaces.Dz a z θ = Work.Spaces.Dz b z θ := by
  simp only [Work.Spaces.Dz]
  rw [pz_congr_of_agreeOnQ h hz hθ hθ2]

theorem Dth_congr_of_agreeOnQ {a b : Fn} (h : AgreeOnQ a b) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Spaces.Dth a z θ = Work.Spaces.Dth b z θ := by
  simp only [Work.Spaces.Dth]
  rw [pth_congr_of_agreeOnQ h hz hθ hθ2]

/-! ## §3 The integral operators -/


theorem L12_congr_of_agreeOnQ {a b : Fn} (h : AgreeOnQ a b) {z : ℝ} (hz : 0 ≤ z) :
    Work.Construction.L12 a z = Work.Construction.L12 b z :=
  Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ hz h

theorem L12f_congr_of_agreeOnQ {a b : Fn} (h : AgreeOnQ a b) {z : ℝ} (hz : 0 ≤ z) :
    Work.Coercivity.L12f a z = Work.Coercivity.L12f b z :=
  Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ hz h

theorem FK_congr_of_agreeOnQ {a b : Fn} (h : AgreeOnQ a b) {z : ℝ} (hz : 0 < z) :
    Work.Construction.FK a z = Work.Construction.FK b z := by
  simp only [Work.Construction.FK]
  refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
  filter_upwards [Work.FTS.GalFields.RHS.ae_mem_Ioo_of_mem_Iθ_gal] with θ hθ hθI
  obtain ⟨h1, h2⟩ := hθ hθI
  rw [h z θ hz h1 h2]

/-! ## §4 The pointwise combinations -/

theorem L_congr_of_agreeOnQ {a b : Fn} (h : AgreeOnQ a b) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Coercivity.L a z θ = Work.Coercivity.L b z θ := by
  have hp := h z θ hz hθ hθ2
  have hdz := Dz_congr_of_agreeOnQ h hz hθ hθ2
  simp only [Work.Coercivity.L]
  rw [hp, hdz]

theorem LGamma_congr_of_agreeOnQ {α : ℝ} {a b : Fn} (h : AgreeOnQ a b) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Coercivity.LGamma α a z θ = Work.Coercivity.LGamma α b z θ := by
  have hl := L_congr_of_agreeOnQ h hz hθ hθ2
  have h12 := L12f_congr_of_agreeOnQ h hz.le
  simp only [Work.Coercivity.LGamma]
  rw [hl, h12]

theorem Transport_congr_of_agreeOnQ {a b : Fn} (h : AgreeOnQ a b) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Coercivity.Transport a z θ = Work.Coercivity.Transport b z θ := by
  have hdt := Dth_congr_of_agreeOnQ h hz hθ hθ2
  simp only [Work.Coercivity.Transport]
  rw [hdt]

theorem Proj_congr_of_agreeOnQ {α : ℝ} {a b : Fn} (h : AgreeOnQ a b) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Coercivity.Proj α a z θ = Work.Coercivity.Proj α b z θ := by
  have hp := h z θ hz hθ hθ2
  have h12 := L12f_congr_of_agreeOnQ h (le_refl (0 : ℝ))
  simp only [Work.Coercivity.Proj]
  rw [hp, h12]

theorem LGammaT_congr_of_agreeOnQ {α : ℝ} {a b : Fn} (h : AgreeOnQ a b) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Coercivity.LGammaT α a z θ = Work.Coercivity.LGammaT α b z θ := by
  have hg := LGamma_congr_of_agreeOnQ (α := α) h hz hθ hθ2
  have hAB : AgreeOnQ (Work.Coercivity.Transport a) (Work.Coercivity.Transport b) :=
    fun z θ hz hθ hθ2 => Transport_congr_of_agreeOnQ h hz hθ hθ2
  have hp := Proj_congr_of_agreeOnQ (α := α) hAB hz hθ hθ2
  simp only [Work.Coercivity.LGammaT]
  rw [hg, hp]

/-! ## §5 The construction-level constituents -/

theorem Theta_congr_of_agreeOnQ {α : ℝ} {F F' : Fn} (h : AgreeOnQ F F') {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Construction.Theta α F z θ = Work.Construction.Theta α F' z θ := by
  have h12 := L12_congr_of_agreeOnQ h hz.le
  simp only [Work.Construction.Theta]
  rw [h12]

theorem PhiTil_congr_of_agreeOnQ {α : ℝ} {F F' Φ Φ' : Fn} (hF : AgreeOnQ F F')
    (hΦ : AgreeOnQ Φ Φ') {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Construction.PhiTil α F Φ z θ = Work.Construction.PhiTil α F' Φ' z θ := by
  have h1 := hΦ z θ hz hθ hθ2
  have h2 := Theta_congr_of_agreeOnQ (α := α) hF hz hθ hθ2
  simp only [Work.Construction.PhiTil]
  rw [h1, h2]

theorem Rop_congr_of_agreeOnQ {α : ℝ} {Φ Φ' : Fn} (h : AgreeOnQ Φ Φ') {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Construction.Rop α Φ z θ = Work.Construction.Rop α Φ' z θ := by
  have hp := h z θ hz hθ hθ2
  have hz' := pz_congr_of_agreeOnQ h hz hθ hθ2
  have ht' := pth_congr_of_agreeOnQ h hz hθ hθ2
  simp only [Work.Construction.Rop]
  rw [hp, hz', ht']

theorem Uop_congr_of_agreeOnQ {α : ℝ} {Φ Φ' : Fn} (h : AgreeOnQ Φ Φ') {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Construction.Uop α Φ z θ = Work.Construction.Uop α Φ' z θ := by
  have hp := h z θ hz hθ hθ2
  have hz' := pz_congr_of_agreeOnQ h hz hθ hθ2
  simp only [Work.Construction.Uop]
  rw [hp, hz']

theorem Vop_congr_of_agreeOnQ {Φ Φ' : Fn} (h : AgreeOnQ Φ Φ') {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Construction.Vop Φ z θ = Work.Construction.Vop Φ' z θ := by
  have hp := h z θ hz hθ hθ2
  have ht' := pth_congr_of_agreeOnQ h hz hθ hθ2
  simp only [Work.Construction.Vop]
  rw [hp, ht']

theorem N0_congr_of_agreeOnQ {α : ℝ} {F F' g g' : Fn} (hF : AgreeOnQ F F')
    (hg : AgreeOnQ g g') {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Construction.N0 α F g z θ = Work.Construction.N0 α F' g' z θ := by
  have hpF := hF z θ hz hθ hθ2
  have hpg := hg z θ hz hθ hθ2
  have hpthF := pth_congr_of_agreeOnQ hF hz hθ hθ2
  have hpthFstar := pth_congr_of_agreeOnQ (a := Work.Construction.Fstar α)
    (b := Work.Construction.Fstar α) (fun _ _ _ _ _ => rfl) hz hθ hθ2
  have hDzF := Dz_congr_of_agreeOnQ hF hz hθ hθ2
  have hDzg := Dz_congr_of_agreeOnQ hg hz hθ hθ2
  have hDzFstar := Dz_congr_of_agreeOnQ (a := Work.Construction.Fstar α)
    (b := Work.Construction.Fstar α) (fun _ _ _ _ _ => rfl) hz hθ hθ2
  have h12 := L12_congr_of_agreeOnQ hg hz.le
  simp only [Work.Construction.N0]
  rw [hpg, h12, hpthF, hDzF, hDzg]

theorem Nstar_congr_of_agreeOnQ {μ lam : ℝ} {g g' : Fn} (h : AgreeOnQ g g') {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Construction.Nstar μ lam g z θ = Work.Construction.Nstar μ lam g' z θ := by
  have hp := h z θ hz hθ hθ2
  have hDz := Dz_congr_of_agreeOnQ h hz hθ hθ2
  simp only [Work.Construction.Nstar]
  rw [hp, hDz]


theorem N_congr_of_agreeOnQ {α : ℝ} {F F' Φ Φ' : Fn} (hF : AgreeOnQ F F')
    (hΦ : AgreeOnQ Φ Φ') {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Construction.N α F Φ z θ = Work.Construction.N α F' Φ' z θ := by
  have hA : AgreeOnQ (Work.Construction.PhiTil α F Φ) (Work.Construction.PhiTil α F' Φ') :=
    fun z θ hz hθ hθ2 => PhiTil_congr_of_agreeOnQ (α := α) hF hΦ hz hθ hθ2
  have hRop := Rop_congr_of_agreeOnQ (α := α) hA hz hθ hθ2
  have hUop := Uop_congr_of_agreeOnQ (α := α) hA hz hθ hθ2
  have hVop := Vop_congr_of_agreeOnQ hA hz hθ hθ2
  have hpF := hF z θ hz hθ hθ2
  have hpthF := pth_congr_of_agreeOnQ hF hz hθ hθ2
  have hDzF := Dz_congr_of_agreeOnQ hF hz hθ hθ2
  have hFK := FK_congr_of_agreeOnQ hF hz
  simp only [Work.Construction.N]
  rw [hRop, hUop, hVop, hFK, hpF, hpthF, hDzF]

/-! ## §6 The right-hand side, the modulation and the equation -/

theorem mubar_congr_of_agreeOnQ {α : ℝ} {F F' g g' Φ Φ' : Fn}
    (hF : AgreeOnQ F F') (hg : AgreeOnQ g g') (hΦ : AgreeOnQ Φ Φ') :
    Work.Construction.mubar (Work.Construction.N0 α F g) (Work.Construction.N α F Φ)
      = Work.Construction.mubar (Work.Construction.N0 α F' g') (Work.Construction.N α F' Φ') := by
  have h1 : AgreeOnQ (Work.Construction.N0 α F g) (Work.Construction.N0 α F' g') :=
    fun z θ hz hθ hθ2 => N0_congr_of_agreeOnQ hF hg hz hθ hθ2
  have h2 : AgreeOnQ (Work.Construction.N α F Φ) (Work.Construction.N α F' Φ') :=
    fun z θ hz hθ hθ2 => N_congr_of_agreeOnQ hF hΦ hz hθ hθ2
  simp only [Work.Construction.mubar]
  rw [L12_congr_of_agreeOnQ h1 (le_refl (0 : ℝ)), L12_congr_of_agreeOnQ h2 (le_refl (0 : ℝ))]

theorem mufunS_congr_of_agreeOnQ {α : ℝ} {F F' g g' Φ Φ' : Fn}
    (hF : AgreeOnQ F F') (hg : AgreeOnQ g g') (hΦ : AgreeOnQ Φ Φ') :
    Work.Construction.mufunS α (Work.Construction.N0 α F g) (Work.Construction.N α F Φ) g
      = Work.Construction.mufunS α (Work.Construction.N0 α F' g') (Work.Construction.N α F' Φ') g' := by
  have h1 : AgreeOnQ (Work.Construction.N0 α F g) (Work.Construction.N0 α F' g') :=
    fun z θ hz hθ hθ2 => N0_congr_of_agreeOnQ hF hg hz hθ hθ2
  have h2 : AgreeOnQ (Work.Construction.N α F Φ) (Work.Construction.N α F' Φ') :=
    fun z θ hz hθ hθ2 => N_congr_of_agreeOnQ hF hΦ hz hθ hθ2
  have h3 : AgreeOnQ (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z))
      (fun z θ => 3 * Work.Spaces.Dth g' z θ / (1 + z)) := by
    intro z θ hz hθ hθ2
    show 3 * Work.Spaces.Dth g z θ / (1 + z) = 3 * Work.Spaces.Dth g' z θ / (1 + z)
    rw [Dth_congr_of_agreeOnQ hg hz hθ hθ2]
  simp only [Work.Construction.mufunS]
  rw [L12_congr_of_agreeOnQ h1 (le_refl (0 : ℝ)), L12_congr_of_agreeOnQ h2 (le_refl (0 : ℝ)),
    L12_congr_of_agreeOnQ h3 (le_refl (0 : ℝ))]

theorem Ftau_congr_of_agreeOnQ {α : ℝ} {g g' : Fam} {τ : ℝ}
    (h : AgreeOnQ (slice g τ) (slice g' τ)) :
    AgreeOnQ (Work.Construction.Ftau α g τ) (Work.Construction.Ftau α g' τ) := by
  intro z θ hz hθ hθ2
  have hp := h z θ hz hθ hθ2
  change Work.Construction.Fstar α z θ + slice g τ z θ
      = Work.Construction.Fstar α z θ + slice g' τ z θ
  rw [hp]

theorem gRHS_congr_of_agreeOnQ {α μ lam : ℝ} {F F' Φ Φ' g g' : Fn}
    (hF : AgreeOnQ F F') (hΦ : AgreeOnQ Φ Φ') (hg : AgreeOnQ g g') {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Construction.gRHS α μ lam F Φ g z θ = Work.Construction.gRHS α μ lam F' Φ' g' z θ := by
  have h1 : Work.Construction.mubar (Work.Construction.N0 α F g) (Work.Construction.N α F Φ)
      = Work.Construction.mubar (Work.Construction.N0 α F' g') (Work.Construction.N α F' Φ') :=
    mubar_congr_of_agreeOnQ hF hg hΦ
  have h2 := N0_congr_of_agreeOnQ (α := α) hF hg hz hθ hθ2
  have h3 := N_congr_of_agreeOnQ (α := α) hF hΦ hz hθ hθ2
  have h4 := Nstar_congr_of_agreeOnQ (μ := μ) (lam := lam) hg hz hθ hθ2
  simp only [Work.Construction.gRHS]
  rw [h1, h2, h3, h4]

theorem muDyn_congr_of_agreeOnQ {α : ℝ} {g g' Φ Φ' : Fam} {τ : ℝ}
    (hgτ : AgreeOnQ (slice g τ) (slice g' τ)) (hΦτ : AgreeOnQ (slice Φ τ) (slice Φ' τ)) :
    Work.FTS.Galerkin.muDyn α Φ g τ = Work.FTS.Galerkin.muDyn α Φ' g' τ := by
  have hFN := Ftau_congr_of_agreeOnQ (α := α) hgτ
  simp only [Work.FTS.Galerkin.muDyn]
  rw [mufunS_congr_of_agreeOnQ hFN hgτ hΦτ]

theorem lamDyn_congr_of_agreeOnQ {α : ℝ} {g g' Φ Φ' : Fam} {τ : ℝ}
    (hgτ : AgreeOnQ (slice g τ) (slice g' τ)) (hΦτ : AgreeOnQ (slice Φ τ) (slice Φ' τ)) :
    Work.FTS.Galerkin.lamDyn α Φ g τ = Work.FTS.Galerkin.lamDyn α Φ' g' τ := by
  have hm := muDyn_congr_of_agreeOnQ (α := α) hgτ hΦτ
  simp only [Work.FTS.Galerkin.lamDyn, Work.Construction.lamfun]
  rw [hm]

/-! ## §7 The fake-time equation and its right-hand side -/

theorem dynLin_congr_of_agreeOnQ {α : ℝ} {g g' : Fam} {τ : ℝ}
    (h : AgreeOnQ (slice g τ) (slice g' τ)) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.FTS.Galerkin.dynLin α g τ z θ = Work.FTS.Galerkin.dynLin α g' τ z θ := by
  have hL := LGammaT_congr_of_agreeOnQ (α := α) h hz hθ hθ2
  simp only [Work.FTS.Galerkin.dynLin]
  rw [hL]

theorem dynRHS_congr_of_agreeOnQ {α : ℝ} {g g' Φ Φ' : Fam} {τ : ℝ}
    (hg : AgreeOnQ (slice g τ) (slice g' τ)) (hΦ : AgreeOnQ (slice Φ τ) (slice Φ' τ))
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.FTS.Galerkin.dynRHS α Φ g τ z θ = Work.FTS.Galerkin.dynRHS α Φ' g' τ z θ := by
  have hm := muDyn_congr_of_agreeOnQ (α := α) hg hΦ
  have hl := lamDyn_congr_of_agreeOnQ (α := α) hg hΦ
  have hF := Ftau_congr_of_agreeOnQ (α := α) hg
  simp only [Work.FTS.Galerkin.dynRHS]
  rw [hm, hl]
  exact gRHS_congr_of_agreeOnQ (α := α) hF hΦ hg hz hθ hθ2

/-! ## §8 The two-sided glue of the right-Taylor extension at `τ = 0` -/

/-- **The `τ = 0` glue.**  If `G` has right-derivative `R` at `0` within `Ici 0`, then the
right-Taylor extension `s ↦ G 0 + s·R` (`s < 0`), `s ↦ G s` (`s ≥ 0`) has the *two-sided*
derivative `R` at `0`.  This is exactly the shape of `Work.FTS.FinalV2.tauExt`, whose slope on
`s < 0` is `derivWithin G (Ici 0) 0 = R`. -/
theorem hasDerivAt_glue_of_hasDerivWithinAt {G : ℝ → ℝ} {R : ℝ}
    (h : HasDerivWithinAt G R (Set.Ici 0) 0) :
    HasDerivAt (fun s => if s < 0 then G 0 + s * derivWithin G (Set.Ici 0) 0 else G s) R 0 := by
  have hder : derivWithin G (Set.Ici 0) 0 = R :=
    h.derivWithin (uniqueDiffWithinAt_Ici 0)
  set F : ℝ → ℝ := fun s => if s < 0 then G 0 + s * derivWithin G (Set.Ici 0) 0 else G s with hFdef
  have hright : HasDerivWithinAt F (derivWithin G (Set.Ici 0) 0) (Set.Ici 0) 0 := by
    rw [hder]
    refine h.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : ¬ s < 0 := not_lt.mpr (Set.mem_Ici.mp hs)
      show (if s < 0 then G 0 + s * derivWithin G (Set.Ici 0) 0 else G s) = G s
      rw [if_neg hs']
    · show (if (0:ℝ) < 0 then G 0 + 0 * derivWithin G (Set.Ici 0) 0 else G 0) = G 0
      rw [if_neg (lt_irrefl (0:ℝ))]
  have hleft : HasDerivWithinAt F (derivWithin G (Set.Ici 0) 0) (Set.Iic 0) 0 := by
    have hlin : HasDerivWithinAt (fun s : ℝ => G 0 + derivWithin G (Set.Ici 0) 0 * s)
        (derivWithin G (Set.Ici 0) 0) (Set.Iic 0) 0 := by
      have h0 : HasDerivAt (fun s : ℝ => G 0 + derivWithin G (Set.Ici 0) 0 * s)
          (derivWithin G (Set.Ici 0) 0) 0 := by
        have h1 := (hasDerivAt_id (0:ℝ)).const_mul (derivWithin G (Set.Ici 0) 0)
        have h2 := h1.const_add (G 0)
        simpa only [id_eq, mul_one] using h2
      exact h0.hasDerivWithinAt
    refine hlin.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs
      rcases lt_or_eq_of_le (Set.mem_Iic.mp hs) with hs' | rfl
      · show (if s < 0 then G 0 + s * derivWithin G (Set.Ici 0) 0 else G s)
          = G 0 + derivWithin G (Set.Ici 0) 0 * s
        rw [if_pos hs']; ring
      · show (if (0:ℝ) < 0 then G 0 + 0 * derivWithin G (Set.Ici 0) 0 else G 0)
          = G 0 + derivWithin G (Set.Ici 0) 0 * 0
        rw [if_neg (lt_irrefl (0:ℝ))]; ring
    · show (if (0:ℝ) < 0 then G 0 + 0 * derivWithin G (Set.Ici 0) 0 else G 0)
        = G 0 + derivWithin G (Set.Ici 0) 0 * 0
      rw [if_neg (lt_irrefl (0:ℝ))]; ring
  have hunion := hright.union hleft
  have hcover : Set.Ici (0:ℝ) ∪ Set.Iic 0 = Set.univ := by
    ext s
    simp only [Set.mem_union, Set.mem_Ici, Set.mem_Iic, Set.mem_univ, iff_true]
    exact le_total 0 s
  rw [hcover, hasDerivWithinAt_univ] at hunion
  rw [hder] at hunion
  exact hunion

/-- The `τ = 0` glue, in the exact shape of `Work.FTS.FinalV2.tauExt`: the right-Taylor extension
of `g z θ ·` has the two-sided derivative `R` at `0` as soon as its right-derivative within `Ici 0`
is `R`. -/
theorem hasDerivAt_tauExt_of_hasDerivWithinAt {g : Fam} {z θ R : ℝ}
    (h : HasDerivWithinAt (fun s => Work.FTS.FinalV2.tauExt g z θ s) R (Set.Ici 0) 0) :
    HasDerivAt (fun s => Work.FTS.FinalV2.tauExt g z θ s) R 0 := by
  have hdwg : HasDerivWithinAt (fun s => g z θ s) R (Set.Ici 0) 0 :=
    h.congr_of_eventuallyEq
      (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (Work.FTS.FinalV2.tauExt_of_nonneg g (Set.mem_Ici.mp hs)).symm)
      (by exact (Work.FTS.FinalV2.tauExt_of_nonneg g le_rfl).symm)
  have hglue := hasDerivAt_glue_of_hasDerivWithinAt (G := fun s => g z θ s) hdwg
  simpa only [Work.FTS.FinalV2.tauExt] using hglue

/-! ## §9 The dynamic equation at the sanitised family -/

/-- **`IsDynEqOn` transfers to the sanitised right-Taylor family.**  The sanitised family agrees
with `tauExt g` on the quadrant `z > 0, 0 < θ < π/2` — the region every operator of the dynamic
equation reads — so the equation for `(tauExt g, PsiCan Φs E (tauExt g))` is the equation for
`(gS α (tauExt g), psiR α Φs E (tauExt g))`. -/
theorem sol_SG {α : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g) :
    Work.FTS.Galerkin.IsDynEqOn (Work.FTS.Regularity.pExp α) (SΨ α Φs E g) (SG α g) := by
  have heq := (Work.FTS.FinalV2.sol_tauExt hSol).2
  intro z θ τ hτ hzθ
  have hz : 0 < z := hzθ.1
  have hθ0 : 0 < θ := hzθ.2.1
  have hθ2 : θ < π / 2 := hzθ.2.2
  have hfuneq : (fun s => SG α g z θ s) = fun s => Work.FTS.FinalV2.tauExt g z θ s :=
    funext fun s => SG_apply_of_pos hz hθ0.le hθ2.le
  have hval : Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) (SG α g) τ z θ
      + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) (SΨ α Φs E g) (SG α g) τ z θ
      = Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α)
          (Work.FTS.FinalV2.tauExt g) τ z θ
      + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α)
          (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.FinalV2.tauExt g))
          (Work.FTS.FinalV2.tauExt g) τ z θ := by
    rw [dynLin_congr_of_agreeOnQ (α := Work.FTS.Regularity.pExp α)
        (SG_slice_agreeOnQ α g τ) hz hθ0 hθ2,
      dynRHS_congr_of_agreeOnQ (α := Work.FTS.Regularity.pExp α)
        (SG_slice_agreeOnQ α g τ) (SΨ_slice_agreeOnQ α Φs E g τ) hz hθ0 hθ2]
  rw [hfuneq, hval]
  exact heq z θ τ hτ hzθ

/-- **The two-sided `τ = 0` equation at the sanitised family** (field `R5Parts.h0`): the
right-Taylor extension has a genuine two-sided derivative at `0`, because the slope of `tauExt` on
`τ < 0` is by construction the right-derivative of `g` at `0`, which the (one-sided) dynamic
equation identifies with the value of the right-hand side. -/
theorem h0_SG {α : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g) :
    ∀ z θ : ℝ, 0 < z → (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (fun s => SG α g z θ s)
        (Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) (SG α g) 0 z θ
          + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) (SΨ α Φs E g)
              (SG α g) 0 z θ) 0 := by
  have heq := (Work.FTS.FinalV2.sol_tauExt hSol).2
  intro z θ hz hzθ
  obtain ⟨hθ0, hθ2⟩ := hzθ.2
  have hfuneq : (fun s => SG α g z θ s) = fun s => Work.FTS.FinalV2.tauExt g z θ s :=
    funext fun s => SG_apply_of_pos hz hθ0.le hθ2.le
  have hstep : HasDerivAt (fun s => Work.FTS.FinalV2.tauExt g z θ s)
      (Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α)
          (Work.FTS.FinalV2.tauExt g) 0 z θ
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.FinalV2.tauExt g))
            (Work.FTS.FinalV2.tauExt g) 0 z θ) 0 :=
    hasDerivAt_tauExt_of_hasDerivWithinAt (heq z θ 0 (le_refl 0) hzθ)
  rw [hfuneq]
  convert hstep using 1
  rw [dynLin_congr_of_agreeOnQ (α := Work.FTS.Regularity.pExp α)
      (SG_slice_agreeOnQ α g 0) hz hθ0 hθ2,
    dynRHS_congr_of_agreeOnQ (α := Work.FTS.Regularity.pExp α)
      (SG_slice_agreeOnQ α g 0) (SΨ_slice_agreeOnQ α Φs E g 0) hz hθ0 hθ2]

end Work.FTS_RegExport.RXR5
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_majorant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.Inputs

set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Filter

open scoped Topology

/-! ## Self-contained proofs of the two remaining scalar inputs

These are the two independent scalar facts the `theta_part_jets` assembly needs; they are proved
here (self-contained, no `sorry`) so that the assembly does not depend on scratch material. -/

/-- **Tail majorant of `√s/(1+s)²`.** -/
theorem majorant_sqrt_tail' : ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z →
    IntegrableOn (fun s : ℝ => s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) (Set.Ioi z) ∧
    ∫ s in Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 ≤ C := by
  refine ⟨4, by norm_num, ?_⟩
  intro z hz
  -- continuity of the two integrands on the open half-line
  have hc_f : ContinuousOn (fun s : ℝ => s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) (Set.Ioi z) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact continuousOn_id.rpow_const (fun s hs => Or.inl (ne_of_gt (lt_trans hz hs)))
    · exact (continuousOn_const.add continuousOn_id).pow 2
    · intro s hs
      have : (0 : ℝ) < 1 + s := by linarith [lt_trans hz hs]
      positivity
  have hc_g' : ContinuousOn (fun s : ℝ => (1 + s) ^ (-(3 : ℝ) / 2)) (Set.Ioi z) := by
    refine ContinuousOn.rpow_const (continuousOn_const.add continuousOn_id) (fun s hs => Or.inl (by
      have : (0 : ℝ) < 1 + s := by linarith [lt_trans hz hs]
      positivity))
  have hc_g : ContinuousOn (fun s : ℝ => 2 * (1 + s) ^ (-(3 : ℝ) / 2)) (Set.Ioi z) :=
    hc_g'.const_mul 2
  -- integrability of the majorant `2(1+s)^{-3/2}` (dominated by `s^{-3/2}`)
  have hint_g' : IntegrableOn (fun s : ℝ => (1 + s) ^ (-(3 : ℝ) / 2)) (Set.Ioi z) := by
    refine Integrable.mono'
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 : ℝ) / 2) < -1) hz)
      (hc_g'.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) < s := lt_trans hz hs
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact Real.rpow_le_rpow_of_nonpos hs0 (by linarith) (by norm_num)
  have hint_g : IntegrableOn (fun s : ℝ => 2 * (1 + s) ^ (-(3 : ℝ) / 2)) (Set.Ioi z) :=
    hint_g'.const_mul 2
  -- the value of the majorant integral, by the fundamental theorem of calculus
  have hderiv : ∀ x ∈ Set.Ioi z,
      HasDerivAt (fun s : ℝ => -2 * (1 + s) ^ (-(1 : ℝ) / 2)) ((1 + x) ^ (-(3 : ℝ) / 2)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < 1 + x := by linarith [lt_trans hz hx]
    have hlin : HasDerivAt (fun s : ℝ => 1 + s) 1 x := (hasDerivAt_id x).const_add 1
    have hinner := (Real.hasDerivAt_rpow_const (x := 1 + x) (p := -(1 : ℝ) / 2)
      (Or.inl (ne_of_gt hx0))).comp x hlin
    have h1 := hinner.const_mul (-2)
    convert h1 using 1
    · ext s; simp [Function.comp_apply]
    · rw [show (-(1 : ℝ) / 2) - 1 = -(3 : ℝ) / 2 from by norm_num]; ring
  have hFTC : ∫ s in Set.Ioi z, (1 + s) ^ (-(3 : ℝ) / 2) = 2 * (1 + z) ^ (-(1 : ℝ) / 2) := by
    have hcont : ContinuousWithinAt (fun s : ℝ => -2 * (1 + s) ^ (-(1 : ℝ) / 2))
        (Set.Ici z) z := by
      refine ContinuousAt.continuousWithinAt ?_
      have hz0 : (0 : ℝ) < 1 + z := by linarith
      have h2 : ContinuousAt (fun s : ℝ => (1 + s) ^ (-(1 : ℝ) / 2)) z :=
        (Real.continuousAt_rpow_const (x := 1 + z) (-(1 : ℝ) / 2)
          (Or.inl (ne_of_gt hz0))).comp (continuousAt_const.add continuousAt_id)
      exact h2.const_mul (-2)
    have htend : Tendsto (fun s : ℝ => -2 * (1 + s) ^ (-(1 : ℝ) / 2)) atTop (𝓝 0) := by
      have hlin_t : Tendsto (fun s : ℝ => 1 + s) atTop atTop :=
        tendsto_atTop_mono' atTop (Filter.Eventually.of_forall
          (fun s => le_add_of_nonneg_left zero_le_one)) tendsto_id
      have h1 : Tendsto (fun s : ℝ => (1 + s) ^ (-(1 : ℝ) / 2)) atTop (𝓝 0) := by
        have h := (tendsto_rpow_neg_atTop (y := (1 : ℝ) / 2)
          (by norm_num : (0 : ℝ) < 1 / 2)).comp hlin_t
        convert h using 1
        ext s
        simp only [Function.comp_apply]
        congr 1
        norm_num
      simpa using h1.const_mul (-2)
    have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := z) (f := fun s : ℝ =>
      -2 * (1 + s) ^ (-(1 : ℝ) / 2)) (f' := fun s : ℝ => (1 + s) ^ (-(3 : ℝ) / 2))
      (m := 0) hcont hderiv hint_g' htend
    rw [h]
    ring
  -- integrability of the target
  have hint_f : IntegrableOn (fun s : ℝ => s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) (Set.Ioi z) := by
    have h0 : IntegrableOn (fun s : ℝ => Real.sqrt s / (1 + s) ^ 2) (Set.Ioi z) :=
      (Work.FTS_RegExport.RXB.integrableOn_sqrt_div_sq).mono_set (Set.Ioi_subset_Ioi hz.le)
    refine h0.congr ?_
    filter_upwards with s
    rw [Real.sqrt_eq_rpow]
  -- the pointwise domination
  have hpt : ∀ᵐ s ∂(volume.restrict (Set.Ioi z)),
      s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 ≤ 2 * (1 + s) ^ (-(3 : ℝ) / 2) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) < s := lt_trans hz hs
    have h1s : (0 : ℝ) < 1 + s := by linarith
    have hroot : s ^ ((1 : ℝ) / 2) ≤ 2 * (1 + s) ^ ((1 : ℝ) / 2) := by
      have h1 : s ^ ((1 : ℝ) / 2) ≤ (4 * (1 + s)) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow hs0.le (by linarith) (by norm_num)
      have h2 : (4 * (1 + s)) ^ ((1 : ℝ) / 2)
          = 4 ^ ((1 : ℝ) / 2) * (1 + s) ^ ((1 : ℝ) / 2) :=
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by linarith : (0 : ℝ) ≤ 1 + s)
      have h3 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, ← Real.rpow_natCast (2 : ℝ) 2,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      calc s ^ ((1 : ℝ) / 2) ≤ (4 * (1 + s)) ^ ((1 : ℝ) / 2) := h1
        _ = 4 ^ ((1 : ℝ) / 2) * (1 + s) ^ ((1 : ℝ) / 2) := h2
        _ = 2 * (1 + s) ^ ((1 : ℝ) / 2) := by rw [h3]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + s) ^ 2)]
    have hfac : 2 * (1 + s) ^ (-(3 : ℝ) / 2) * (1 + s) ^ 2 = 2 * (1 + s) ^ ((1 : ℝ) / 2) := by
      rw [show 2 * (1 + s) ^ (-(3 : ℝ) / 2) * (1 + s) ^ 2
          = 2 * ((1 + s) ^ (-(3 : ℝ) / 2) * (1 + s) ^ 2) from by ring]
      rw [← Real.rpow_natCast (1 + s) 2, ← Real.rpow_add h1s]
      congr 1
      norm_num
    rw [hfac]
    exact hroot
  refine ⟨hint_f, ?_⟩
  calc ∫ s in Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2
      ≤ ∫ s in Set.Ioi z, 2 * (1 + s) ^ (-(3 : ℝ) / 2) :=
        integral_mono_ae hint_f hint_g hpt
    _ = 2 * ∫ s in Set.Ioi z, (1 + s) ^ (-(3 : ℝ) / 2) := integral_const_mul 2 _
    _ = 2 * (2 * (1 + z) ^ (-(1 : ℝ) / 2)) := by rw [hFTC]
    _ = 4 * (1 + z) ^ (-(1 : ℝ) / 2) := by ring
    _ ≤ 4 * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    _ = 4 := by norm_num

end

end Work.FTS_StreamBdry.Inputs
end
