import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkDzdIterSharp
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.pz_DthIter_mul_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

set_option autoImplicit false

/-! ## Transfer of an a.e. statement on the first variable to the product measure

The `fst`-image of `μ.prod ν` is the scalar multiple `ν univ • μ`
(`Measure.map_fst_prod`), so a `μ`-null set pulls back to a `μ.prod ν`-null set.  This is
the form of the transfer used below: an a.e. bound in the radial variable `z` must become an
a.e. bound for the pairing on `Iz × Iθ`.  (`AEMeasurable.comp_fst` gives the analogous
statement for measurability; here no measurability of `p` is assumed, which is the point —
the a.e. *bound* on `z ↦ D_z^{b₁}(FK f)` carries no measurability.) -/
theorem ae_fst_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    {p : α → Prop} (h : ∀ᵐ z ∂μ, p z) :
    ∀ᵐ q ∂(μ.prod ν), p q.1 := by
  rw [MeasureTheory.ae_iff] at h ⊢
  have hmeas : MeasurableSet (toMeasurable μ {z | ¬ p z}) := measurableSet_toMeasurable _ _
  have hnull : μ (toMeasurable μ {z | ¬ p z}) = 0 := by
    rw [measure_toMeasurable]; exact h
  refine measure_mono_null (t := Prod.fst ⁻¹' toMeasurable μ {z | ¬ p z}) ?_ ?_
  · intro q hq
    exact subset_toMeasurable μ {z | ¬ p z} hq
  · rw [← Measure.map_apply measurable_fst hmeas, Measure.map_fst_prod, Measure.smul_apply,
      hnull, smul_zero]

/-! ## A.e. strong measurability of the angular moments -/

/-- `z ↦ Qang f i z = ∫_θ Kθ(θ)·D_z^i f(z,θ) dθ` is a.e. strongly measurable on `Iz` for an
interior-class datum: it is the `θ`-integral of the jointly continuous
`(z,θ) ↦ Kθ(θ)·D_z^i f(z,θ)` on the open quadrant
(`AEStronglyMeasurable.integral_prod_right'`, the open-quadrant continuity being
`QangOpen.continuousOn_Ktheta_DzIter_open`). -/
theorem aesm_Qang {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f) (i : ℕ) :
    AEStronglyMeasurable (fun z => Work.Elliptic.Qang f i z)
      (volume.restrict Work.Spaces.Iz) := by
  have h := (Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter i f p.1 p.2)
    (Work.FTS.OpenPkg.QangOpen.continuousOn_Ktheta_DzIter_open hsm i)).integral_prod_right'
  simpa only [Work.Elliptic.Qang] using h

/-- **The `D_z`-jets of `FK f` are a.e. the angular moments of `f`**:
`D_z^{b₁}(FK f) = Qang f b₁` a.e. on `Iz`, for `b₁ ≤ 6` and `HkMem α 6 f`.

`DzIter_FK_eq_ae` gives the two-dimensional form `D_z^{b₁}(FK f) = FK (D_z^{b₁} f)` a.e., and
the angular-moment identities `DzIter_rad` (`D_z^{b₁}` of a radial function),
`FK_eq_Qang_apply` and `Qang_DzIter_zero` convert it. -/
theorem fkQangAe {α : ℝ} {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hm6 : Work.Spaces.HkMem α 6 f) (b₁ : ℕ) (hb : b₁ ≤ 6) :
    (fun z => Work.Elliptic.DzdIter b₁ (fun w => Work.Construction.FK f w) z)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => Work.Elliptic.Qang f b₁ z) := by
  have hae := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae hsm hm6 b₁ hb
  filter_upwards [hae] with z hz
  calc Work.Elliptic.DzdIter b₁ (fun w => Work.Construction.FK f w) z
      = Work.Spaces.DzIter b₁ (fun z _ => Work.Construction.FK f z) z 0 :=
        (Work.Elliptic.DzIter_rad (fun w => Work.Construction.FK f w) b₁ z 0).symm
    _ = Work.Construction.FK (Work.Spaces.DzIter b₁ f) z := hz 0
    _ = Work.Elliptic.Qang (Work.Spaces.DzIter b₁ f) 0 z :=
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.FK_eq_Qang_apply _ _
    _ = Work.Elliptic.Qang f b₁ z :=
        congrFun (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.Qang_DzIter_zero f b₁) z

/-! ## Two elementary facts about the domain and the leaf weights -/

/-- Every leaf weight of the slot `a` is nonnegative on the closed quadrant `Iz × Iθ`. -/
theorem leaf_nonneg {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ ρ z θ := by
  rcases hρ with rfl | rfl | ⟨_, rfl⟩
  · intro z _ θ hθ
    rw [Work.FTS.TransportS.leafEta]
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)
  · intro z _ θ _
    rw [Work.FTS.TransportS.leafOne]
    exact sq_nonneg _
  · intro z _ θ hθ
    rw [Work.FTS.TransportS.leafGam]
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)

/-- Almost every point of `Iz × Iθ` lies in the open quadrant `Q0` (the exceptional set is
`{0} × Iθ` together with the two angular endpoints).  This is what turns the pointwise
domination of `HkIntegrand` — available on the open quadrant — into an a.e. bound. -/
theorem ae_mem_Q0 :
    ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)),
      p ∈ Work.FTS.EllipticEst.Q0 := by
  have hzpos : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), 0 < z := by
    rw [Work.FTS.StrongPersist.H6Pair6Aux.Iz_restrict_eq]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  have hθmem : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
    have h : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2)).symm
    rw [h]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  refine (Measure.ae_prod_mem_iff_ae_ae_mem (s := Work.FTS.EllipticEst.Q0)
    Work.FTS.EllipticEst.isOpen_Q0.measurableSet).mpr ?_
  filter_upwards [hzpos] with z hz
  filter_upwards [hθmem] with θ hθ
  exact ⟨hz, hθ⟩

/-! ## The pairing -/


end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux
