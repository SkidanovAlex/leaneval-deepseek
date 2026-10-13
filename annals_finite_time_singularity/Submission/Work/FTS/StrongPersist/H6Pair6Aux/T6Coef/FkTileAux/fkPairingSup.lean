/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FkTileAux/fkPairingSup` — the level-six pairing with an a.e.-bounded `D_z`-jet of `FK f`

The target of this file is the leaf pairing

  `∫_z ∫_θ ρ · D_z^{b₁}(FK f)(z) · (D_z^{b-b₁}D_θ^a f)(z,θ) · (D_z^bD_θ^a f)(z,θ)`

with `ρ` a leaf weight of the slot `a` (`IsLeafW α a ρ`), `b₁ ≤ b`, `a + b ≤ 6`, and the
`D_z`-jet of the angular moment `FK f` dominated *almost everywhere* by `K`.  The two
conclusions are the (product-measure) integrability of the integrand and the bound

  `|∫∫ ρ A X Y| ≤ C·K·(1 + |f|²_{ℋ⁶})`,

with a universal `C` (here `C = 2`).

## The argument

Everything is the AM–GM pairing of the two slots of the datum `f`, with the radial
coefficient `A = D_z^{b₁}(FK f)` playing the role of a bounded multiplier:

* both slots are honest `ℋ⁶`-slots — `ρ·(D_z^jD_θ^af)²` is integrable over the product
  measure `(volume.restrict Iz).prod (volume.restrict Iθ)` and its integral is at most
  `HkSq α 6 f` (`fkSlotSqInt`, valid for `a + j ≤ 6`);
* on the open quadrant (a conull set), `|ρ A X Y| = ρ·|A|·|X|·|Y| ≤ ρK|X||Y| ≤
  K(ρX² + ρY²)` by AM–GM (`two_mul_le_add_sq`), using `ρ ≥ 0`;
* the a.e. bound on `A` (given on `Iz`) transfers to the product measure
  (`ae_fst_prod`: the `fst`-image of `ν₁.prod ν₂` is a scalar multiple of `ν₁`, so the
  null sets agree), and the *measurability* of `A` — which an a.e. bound alone cannot give —
  comes from the a.e. identity `D_z^{b₁}(FK f) = Qang f b₁` (`DzIter_FK_eq_ae`): `A` is a.e.
  the `z`-integral of the jointly continuous `Kθ(θ)·D_z^{b₁}f`, hence a.e. strongly
  measurable (`AEStronglyMeasurable.integral_prod_right'`).

This file is the assembly (the pairing, the AM–GM and the transfer of the a.e. bound); the
slot-square integrability/estimate is the sibling `FkTileAux.fkSlotSqInt`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkDzdIterSharp
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkSlotSqInt
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T4bSlotAux
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

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

/-- **The level-six leaf pairing with an a.e.-bounded radial multiplier.**

For `0 < α ≤ 1`, a datum `f` smooth on the open quadrant with `HkMem α 7 f`, a leaf weight
`ρ` of the slot `a`, `b₁ ≤ b`, `a + b ≤ 6`, and a constant `K ≥ 0` bounding the `b₁`-th
radial jet of the angular moment `FK f` almost everywhere, the pairing

`∫_p ρ p.1 p.2 · D_z^{b₁}(FK f)(p.1) · (D_z^{b-b₁}D_θ^af) p · (D_z^bD_θ^af) p`

(with `p` ranging over the product of the two restricted Lebesgue measures) is integrable and
bounded by `2·K·(1 + HkSq α 6 f)`. -/
theorem fkPairingSup : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (a b b₁ : ℕ) (ρ : ℝ → ℝ → ℝ) (K : ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 7 f → 0 ≤ K →
      b₁ ≤ b → a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        |Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z| ≤ K) →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
          * Work.Spaces.mixed (b - b₁) a f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, ρ p.1 p.2 * Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
            * Work.Spaces.mixed (b - b₁) a f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * K * (1 + Work.Spaces.HkSq α 6 f) := by
  refine ⟨2, by norm_num, ?_⟩
  intro α hαI f a b b₁ ρ K hsm hm7 hK hb1b hab hleaf hA
  have hα : 0 < α := hαI.1
  have hb16 : b₁ ≤ 6 := by omega
  -- `ℋ⁶`-honesty of `f`, descending from `ℋ⁷`
  have hm6 : Work.Spaces.HkMem α 6 f := Work.FTS.OpenPkg.HkMem_mono_open hsm 6 (by omega) hm7
  -- the first slot of the pairing has order `a + (b - b₁) ≤ 6`
  have haX : a + (b - b₁) ≤ 6 := by omega
  -- ## measurability of the radial multiplier
  have hA_aesm : AEStronglyMeasurable
      (fun z => Work.Elliptic.DzdIter b₁ (fun w => Work.Construction.FK f w) z)
      (volume.restrict Work.Spaces.Iz) :=
    (aesm_Qang hsm b₁).congr (fkQangAe hsm hm6 b₁ hb16).symm
  have hAc : AEMeasurable
      (fun p : ℝ × ℝ => Work.Elliptic.DzdIter b₁ (fun w => Work.Construction.FK f w) p.1)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    hA_aesm.aemeasurable.comp_fst
  -- ## the a.e. bound, transferred to the product measure
  have hAprod : ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod
      (volume.restrict Work.Spaces.Iθ)),
      |Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1| ≤ K :=
    ae_fst_prod hA
  -- the `ρ·(slot)·(slot)` factor is continuous on the open quadrant, hence a.e. strongly
  -- measurable
  have hXYaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.1 p.2
      * Work.Spaces.mixed (b - b₁) a f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (((Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_leaf hleaf).mul
        (hsm.mixed (b - b₁) a).continuousOn).mul (hsm.mixed b a).continuousOn)
  have hF_aesm : AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.1 p.2
      * Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
      * Work.Spaces.mixed (b - b₁) a f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (hAc.aestronglyMeasurable.mul hXYaesm).congr
      (Eventually.of_forall (fun p => by simp only [Pi.mul_apply]; ring))
  -- ## the two slot squares
  obtain ⟨hXint, hXle⟩ := fkSlotSqInt (α := α) (f := f) (a := a) (j := b - b₁)
    hα haX hleaf hsm hm6
  obtain ⟨hYint, hYle⟩ := fkSlotSqInt (α := α) (f := f) (a := a) (j := b)
    hα hab hleaf hsm hm6
  have hmaj : MeasureTheory.Integrable (fun p : ℝ × ℝ => K *
      (ρ p.1 p.2 * Work.Spaces.mixed (b - b₁) a f p.1 p.2 ^ 2
        + ρ p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2 ^ 2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (hXint.add hYint).const_mul K
  -- ## the pointwise AM–GM bound
  have hpt : ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod
      (volume.restrict Work.Spaces.Iθ)),
      ‖ρ p.1 p.2 * Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
        * Work.Spaces.mixed (b - b₁) a f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2‖
      ≤ K * (ρ p.1 p.2 * Work.Spaces.mixed (b - b₁) a f p.1 p.2 ^ 2
          + ρ p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2 ^ 2) := by
    filter_upwards [ae_mem_Q0, hAprod] with p hp hAp
    obtain ⟨hpz, hpθ0, hpθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hρ0 : 0 ≤ ρ p.1 p.2 :=
      leaf_nonneg hleaf p.1 (le_of_lt hpz) p.2 ⟨le_of_lt hpθ0, le_of_lt hpθ1⟩
    have hkey : ‖ρ p.1 p.2 * Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
        * Work.Spaces.mixed (b - b₁) a f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2‖
        = ρ p.1 p.2 * |Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1|
          * |Work.Spaces.mixed (b - b₁) a f p.1 p.2| * |Work.Spaces.mixed b a f p.1 p.2| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hρ0]
    rw [hkey]
    have h2 : 2 * |Work.Spaces.mixed (b - b₁) a f p.1 p.2|
          * |Work.Spaces.mixed b a f p.1 p.2|
        ≤ (Work.Spaces.mixed (b - b₁) a f p.1 p.2) ^ 2
          + (Work.Spaces.mixed b a f p.1 p.2) ^ 2 := by
      have h := two_mul_le_add_sq |Work.Spaces.mixed (b - b₁) a f p.1 p.2|
        |Work.Spaces.mixed b a f p.1 p.2|
      rwa [sq_abs, sq_abs] at h
    have h1 : ρ p.1 p.2
          * |Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1|
        ≤ ρ p.1 p.2 * K :=
      mul_le_mul_of_nonneg_left hAp hρ0
    have hstep1 : ρ p.1 p.2
          * |Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1|
          * |Work.Spaces.mixed (b - b₁) a f p.1 p.2| * |Work.Spaces.mixed b a f p.1 p.2|
        ≤ ρ p.1 p.2 * K * |Work.Spaces.mixed (b - b₁) a f p.1 p.2|
          * |Work.Spaces.mixed b a f p.1 p.2| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1
        (abs_nonneg (Work.Spaces.mixed (b - b₁) a f p.1 p.2)))
        (abs_nonneg (Work.Spaces.mixed b a f p.1 p.2))
    have hstep2 : ρ p.1 p.2 * K * |Work.Spaces.mixed (b - b₁) a f p.1 p.2|
          * |Work.Spaces.mixed b a f p.1 p.2|
        ≤ K * (ρ p.1 p.2 * (Work.Spaces.mixed (b - b₁) a f p.1 p.2) ^ 2
            + ρ p.1 p.2 * (Work.Spaces.mixed b a f p.1 p.2) ^ 2) := by
      have h3 : |Work.Spaces.mixed (b - b₁) a f p.1 p.2|
            * |Work.Spaces.mixed b a f p.1 p.2|
          ≤ (Work.Spaces.mixed (b - b₁) a f p.1 p.2) ^ 2
            + (Work.Spaces.mixed b a f p.1 p.2) ^ 2 :=
        by nlinarith [h2, abs_nonneg (Work.Spaces.mixed (b - b₁) a f p.1 p.2),
          abs_nonneg (Work.Spaces.mixed b a f p.1 p.2)]
      calc ρ p.1 p.2 * K * |Work.Spaces.mixed (b - b₁) a f p.1 p.2|
            * |Work.Spaces.mixed b a f p.1 p.2|
          = ρ p.1 p.2 * K * (|Work.Spaces.mixed (b - b₁) a f p.1 p.2|
              * |Work.Spaces.mixed b a f p.1 p.2|) := by ring
        _ ≤ ρ p.1 p.2 * K * ((Work.Spaces.mixed (b - b₁) a f p.1 p.2) ^ 2
              + (Work.Spaces.mixed b a f p.1 p.2) ^ 2) :=
            mul_le_mul_of_nonneg_left h3 (mul_nonneg hρ0 hK)
        _ = K * (ρ p.1 p.2 * (Work.Spaces.mixed (b - b₁) a f p.1 p.2) ^ 2
              + ρ p.1 p.2 * (Work.Spaces.mixed b a f p.1 p.2) ^ 2) := by ring
    linarith [hstep1, hstep2]
  have hFint : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
      * Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
      * Work.Spaces.mixed (b - b₁) a f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Integrable.mono' hmaj hF_aesm hpt
  refine ⟨hFint, ?_⟩
  -- ## the value bound
  have h1 : |∫ p, ρ p.1 p.2 * Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
        * Work.Spaces.mixed (b - b₁) a f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2
      ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))|
      ≤ ∫ p, ‖ρ p.1 p.2 * Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
        * Work.Spaces.mixed (b - b₁) a f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2‖
      ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
        * Work.Spaces.mixed (b - b₁) a f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2)
  have h2 : (∫ p, ‖ρ p.1 p.2
        * Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
        * Work.Spaces.mixed (b - b₁) a f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2‖
      ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      ≤ ∫ p, K * (ρ p.1 p.2 * Work.Spaces.mixed (b - b₁) a f p.1 p.2 ^ 2
          + ρ p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2 ^ 2)
      ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    integral_mono_of_nonneg (Eventually.of_forall (fun p => norm_nonneg _)) hmaj hpt
  have h3 : (∫ p, K * (ρ p.1 p.2 * Work.Spaces.mixed (b - b₁) a f p.1 p.2 ^ 2
          + ρ p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2 ^ 2)
      ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      = K * ((∫ p, ρ p.1 p.2 * Work.Spaces.mixed (b - b₁) a f p.1 p.2 ^ 2
            ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
          + (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2 ^ 2
            ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))) := by
    rw [integral_const_mul, integral_add hXint hYint]
  have h4 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  calc |∫ p, ρ p.1 p.2 * Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
            * Work.Spaces.mixed (b - b₁) a f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))|
      ≤ _ := h1
    _ ≤ _ := h2
    _ = _ := h3
    _ ≤ K * (Work.Spaces.HkSq α 6 f + Work.Spaces.HkSq α 6 f) :=
        mul_le_mul_of_nonneg_left (add_le_add hXle hYle) hK
    _ = 2 * K * Work.Spaces.HkSq α 6 f := by ring
    _ ≤ 2 * K * (1 + Work.Spaces.HkSq α 6 f) := by nlinarith [hK, h4]

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux
