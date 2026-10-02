import Mathlib
import Submission.Work.Orient.Defs
import Submission.Work.Tubular.Defs
import Submission.Work.Thom.Cohomology
import Submission.Work.Tubular.relKronH_natural
import Submission.Work.ThomBordism.Transversality.OrientBridge.isFundClass_map_homeomorph

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The uniformity of the translated local pairing

`Work.ThomBordism.constancy_translated_local_pairing`: on the one-point compactification
`OnePoint (Euc n)` of `Euc n`, for a *fixed* cohomology class `σ` on the pair
`(OnePoint (Euc n), {some 0}ᶜ)` and a *fixed* absolute homology class `u₀`, the pairing

  `V p = ⟨(T_{-p})^* σ, locClass u₀ (some p)⟩`

of the translated class with the local class of `u₀` at `some p` is **independent of `p ∈ Euc n`**.

The proof is a single symmetry: `T_c` is homotopic to the identity of `OnePoint (Euc n)`, so
`(T_c)_*u₀ = u₀`; then for `ρ := T_{p-p'}` one has `ρ(some p') = some p` and
`T_{-p} ∘ ρ = T_{-p'}`, and naturality of the relative Kronecker pairing and of the local classes
along `ρ` gives `V p = V p'`.

This is the *entire* uniformity content of `Work.ThomBordism.collapseLocalisation_ambient`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.ThomBordism

noncomputable section

variable {n : ℕ}

/-- The translation homeomorphism `z ↦ z + c` of `Euc n`. -/
def eucAddHomeo (c : Work.Tubular.Euc n) : Work.Tubular.Euc n ≃ₜ Work.Tubular.Euc n where
  toFun := fun z => z + c
  invFun := fun z => z - c
  left_inv := fun z => add_sub_cancel_right z c
  right_inv := fun z => sub_add_cancel z c
  continuous_toFun := continuous_id.add continuous_const
  continuous_invFun := continuous_id.sub continuous_const

@[simp] theorem eucAddHomeo_apply (c z : Work.Tubular.Euc n) : eucAddHomeo c z = z + c := rfl

/-- The (one-point extension of the) translation `z ↦ z + c`, as an element of the mapping space. -/
def transT (c : Work.Tubular.Euc n) : C(OnePoint (Work.Tubular.Euc n), OnePoint (Work.Tubular.Euc n)) :=
  ⟨OnePoint.map (fun z => z + c), (Homeomorph.onePointCongr (eucAddHomeo c)).continuous_toFun⟩

@[simp] theorem transT_some (c z : Work.Tubular.Euc n) :
    transT c (OnePoint.some z) = OnePoint.some (z + c) := rfl

@[simp] theorem transT_infty (c : Work.Tubular.Euc n) : transT c OnePoint.infty = OnePoint.infty :=
  rfl

theorem transT_comp (c d : Work.Tubular.Euc n) : (transT c).comp (transT d) = transT (d + c) := by
  ext y
  induction y using OnePoint.rec with
  | infty => rfl
  | coe z => simp [add_assoc]

/-- The pair condition: `T_{-c}` maps the complement of `some c` into the complement of `some 0`. -/
theorem transT_pair (c : Work.Tubular.Euc n) :
    ∀ y ∈ ({OnePoint.some c}ᶜ : Set (OnePoint (Work.Tubular.Euc n))),
      transT (-c) y ∈ ({OnePoint.some (0 : Work.Tubular.Euc n)}ᶜ :
        Set (OnePoint (Work.Tubular.Euc n))) := by
  intro y hy
  rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
  induction y using OnePoint.rec with
  | infty => exact OnePoint.infty_ne_coe 0
  | coe z =>
    simp only [transT_some]
    intro h
    exact hy (by rw [sub_eq_zero.mp (OnePoint.coe_eq_coe.mp h)])

/-- **The family of translations `(s, y) ↦ T_{s·c}(y)` is jointly continuous.** -/
theorem continuous_transT_family (n : ℕ) (c : Work.Tubular.Euc n) :
    Continuous fun q : unitInterval × OnePoint (Work.Tubular.Euc n) =>
      OnePoint.map (fun z => z + (q.1 : ℝ) • c) q.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s, y⟩
  induction y using OnePoint.rec with
  | infty =>
    refine (OnePoint.hasBasis_nhds_infty.tendsto_right_iff).mpr ?_
    rintro K ⟨hKc, hKcomp⟩
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Work.Tubular.Euc n)).mp
      hKcomp.isBounded
    have hm : (OnePoint.some '' (Metric.closedBall (0 : Work.Tubular.Euc n) (R + ‖c‖))ᶜ ∪
        {OnePoint.infty}) ∈ 𝓝 (OnePoint.infty : OnePoint (Work.Tubular.Euc n)) :=
      OnePoint.hasBasis_nhds_infty.mem_iff.mpr
        ⟨Metric.closedBall (0 : Work.Tubular.Euc n) (R + ‖c‖),
          ⟨Metric.isClosed_closedBall, isCompact_closedBall _ _⟩, subset_rfl⟩
    filter_upwards [(continuous_snd.tendsto (s, OnePoint.infty)).eventually hm] with q hq
    rcases hq with hq | hq
    · obtain ⟨w, hw, hwq⟩ := hq
      rw [Set.mem_compl_iff, Metric.mem_closedBall, not_le, dist_zero_right] at hw
      refine Or.inl ⟨w + (q.1 : ℝ) • c, ?_, ?_⟩
      · intro hmem
        have h1 : ‖w + (q.1 : ℝ) • c‖ ≤ R := by
          have := hR hmem
          rwa [Metric.mem_closedBall, dist_zero_right] at this
        have h2 : ‖(q.1 : ℝ) • c‖ ≤ ‖c‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (unitInterval.nonneg q.1)]
          nlinarith [norm_nonneg c, unitInterval.le_one q.1]
        have h3 : ‖w‖ ≤ ‖w + (q.1 : ℝ) • c‖ + ‖(q.1 : ℝ) • c‖ := by
          calc ‖w‖ = ‖(w + (q.1 : ℝ) • c) - (q.1 : ℝ) • c‖ := by
                rw [add_sub_cancel_right]
            _ ≤ ‖w + (q.1 : ℝ) • c‖ + ‖(q.1 : ℝ) • c‖ := norm_sub_le _ _
        linarith
      · rw [← hwq]
        rfl
    · rw [hq]
      exact Or.inr rfl
  | coe z =>
    show Filter.Tendsto (fun q : unitInterval × OnePoint (Work.Tubular.Euc n) =>
        OnePoint.map (fun z => z + (q.1 : ℝ) • c) q.2) (𝓝 (s, OnePoint.some z))
      (𝓝 (OnePoint.map (fun z => z + (s : ℝ) • c) (OnePoint.some z)))
    rw [OnePoint.map_some, OnePoint.nhds_coe_eq]
    refine Filter.tendsto_def.mpr ?_
    intro t ht
    rw [Filter.mem_map] at ht
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ht
    have hne : (0 : ℝ) < 2 * (‖c‖ + 1) := by positivity
    have hV : Metric.ball z (δ / 2) ∈ 𝓝 z := Metric.ball_mem_nhds _ (by linarith)
    have h2 : ∀ᶠ q : unitInterval × OnePoint (Work.Tubular.Euc n) in 𝓝 (s, OnePoint.some z),
        q.2 ∈ OnePoint.some '' Metric.ball z (δ / 2) :=
      (continuous_snd.tendsto (s, OnePoint.some z)).eventually (by
        rw [OnePoint.nhds_coe_eq]
        exact Filter.mem_map.mpr (by
          convert hV using 1
          exact Set.preimage_image_eq _ OnePoint.coe_injective))
    have h1 : ∀ᶠ q : unitInterval × OnePoint (Work.Tubular.Euc n) in 𝓝 (s, OnePoint.some z),
        |(q.1 : ℝ) - (s : ℝ)| < δ / (2 * (‖c‖ + 1)) := by
      have hU : {t : ℝ | |t - (s : ℝ)| < δ / (2 * (‖c‖ + 1))} ∈ 𝓝 ((s : unitInterval) : ℝ) := by
        refine Metric.mem_nhds_iff.mpr ⟨δ / (2 * (‖c‖ + 1)), by positivity, ?_⟩
        intro t ht
        rwa [Metric.mem_ball, Real.dist_eq] at ht
      exact ((continuous_subtype_val.tendsto s).comp (continuous_fst.tendsto _)).eventually hU
    filter_upwards [h1, h2] with q hq1 hq2
    obtain ⟨w, hw, hwq⟩ := hq2
    show OnePoint.map (fun z => z + (q.1 : ℝ) • c) q.2 ∈ t
    rw [← hwq]
    have hwz : ‖w - z‖ < δ / 2 := by
      have := hw
      rwa [Metric.mem_ball, dist_eq_norm] at this
    have hstep : ‖w + (q.1 : ℝ) • c - (z + (s : ℝ) • c)‖ < δ := by
      have h4 : ‖w + (q.1 : ℝ) • c - (z + (s : ℝ) • c)‖
          ≤ ‖w - z‖ + |(q.1 : ℝ) - (s : ℝ)| * ‖c‖ := by
        rw [show w + (q.1 : ℝ) • c - (z + (s : ℝ) • c)
          = (w - z) + ((q.1 : ℝ) - (s : ℝ)) • c by module]
        calc ‖(w - z) + ((q.1 : ℝ) - (s : ℝ)) • c‖ ≤ ‖w - z‖ + ‖((q.1 : ℝ) - (s : ℝ)) • c‖ :=
              norm_add_le _ _
          _ = ‖w - z‖ + |(q.1 : ℝ) - (s : ℝ)| * ‖c‖ := by
              rw [norm_smul, Real.norm_eq_abs]
      have h5 : |(q.1 : ℝ) - (s : ℝ)| * ‖c‖ ≤ δ / 2 := by
        have h6 : (δ / (2 * (‖c‖ + 1))) * ‖c‖ ≤ δ / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ hne (by norm_num : (0:ℝ) < 2)]
          nlinarith [norm_nonneg c, hδ]
        exact le_trans (mul_le_mul_of_nonneg_right hq1.le (norm_nonneg c)) h6
      linarith
    exact hball (by rwa [Metric.mem_ball, dist_eq_norm])

/-- **The translation `T_c` of `OnePoint (Euc n)` is homotopic to the identity.** -/
def transT_homotopy (n : ℕ) (c : Work.Tubular.Euc n) :
    TopCat.Homotopy (𝟙 (TopCat.of (OnePoint (Work.Tubular.Euc n))))
      (TopCat.ofHom (transT c)) where
  toContinuousMap := ⟨fun q : unitInterval × OnePoint (Work.Tubular.Euc n) =>
      OnePoint.map (fun z => z + (q.1 : ℝ) • c) q.2, continuous_transT_family n c⟩
  map_zero_left := by
    intro y
    show OnePoint.map (fun z => z + (((0 : unitInterval) : ℝ)) • c) y = y
    have h : (fun z : Work.Tubular.Euc n => z + (((0 : unitInterval) : ℝ)) • c) = id := by
      funext z; simp
    rw [h]
    exact congrFun OnePoint.map_id y
  map_one_left := by
    intro y
    show OnePoint.map (fun z => z + (((1 : unitInterval) : ℝ)) • c) y
      = OnePoint.map (fun z => z + c) y
    have h : (fun z : Work.Tubular.Euc n => z + (((1 : unitInterval) : ℝ)) • c) = fun z => z + c := by
      funext z; simp
    rw [h]

/-- **The translation of `OnePoint (Euc n)` is homotopic to the identity**, hence its effect on
homology is the identity. -/
theorem transT_homotopic_id (n : ℕ) (c : Work.Tubular.Euc n) :
    Nonempty (TopCat.Homotopy (TopCat.ofHom (transT c))
      (𝟙 (TopCat.of (OnePoint (Work.Tubular.Euc n))))) :=
  ⟨(transT_homotopy n c).symm⟩


/-! ## The consequence for homology, and the constancy of the translated local pairing -/

/-- **The translation of `OnePoint (Euc n)` acts as the identity on homology.** -/
theorem transT_homologyMap_id (m : ℕ) (c : Work.Tubular.Euc n) :
    HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (OnePoint (Work.Tubular.Euc n)))
        (TopCat.of (OnePoint (Work.Tubular.Euc n))) (TopCat.ofHom (transT c))) m = 𝟙 _ := by
  obtain ⟨H⟩ := transT_homotopic_id n c
  have h := H.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℤ ℤ) m
  rw [h]
  simp

/-- **The uniformity of the translated local pairing.**  For a fixed cohomology class `σ` on the
pair `(OnePoint (Euc n), {some 0}ᶜ)` and a fixed absolute class `u₀`, the pairing of the translated
class `(T_{-p})^*σ` with the local class of `u₀` at `some p` is independent of `p ∈ Euc n`. -/
theorem constancy_translated_local_pairing (m : ℕ)
    (σ : Work.Thom.RelCoh ℤ m (OnePoint (Work.Tubular.Euc n))
      ({OnePoint.some 0}ᶜ : Set (OnePoint (Work.Tubular.Euc n))))
    (u₀ : (Work.Cohomology.singularChains ℤ (TopCat.of (OnePoint (Work.Tubular.Euc n)))).homology m)
    (p p' : Work.Tubular.Euc n) :
    Work.Tubular.relKronH (TopCat.of (OnePoint (Work.Tubular.Euc n)))
        ({OnePoint.some p}ᶜ : Set (OnePoint (Work.Tubular.Euc n))) m
        ((Work.Thom.relCohMap (transT (-p)) ({OnePoint.some p}ᶜ)
          ({OnePoint.some 0}ᶜ) (transT_pair p) ℤ m).hom σ)
        (Work.Orient.locClass (TopCat.of (OnePoint (Work.Tubular.Euc n))) m u₀ (OnePoint.some p))
      = Work.Tubular.relKronH (TopCat.of (OnePoint (Work.Tubular.Euc n)))
        ({OnePoint.some p'}ᶜ : Set (OnePoint (Work.Tubular.Euc n))) m
        ((Work.Thom.relCohMap (transT (-p')) ({OnePoint.some p'}ᶜ)
          ({OnePoint.some 0}ᶜ) (transT_pair p') ℤ m).hom σ)
        (Work.Orient.locClass (TopCat.of (OnePoint (Work.Tubular.Euc n))) m u₀ (OnePoint.some p')) := by
  -- the translation `ρ := T_{p-p'}` carries `some p'` to `some p`, hence the pairs
  have hpair : ∀ y ∈ ({OnePoint.some p'}ᶜ : Set (OnePoint (Work.Tubular.Euc n))),
      transT (p - p') y ∈ ({OnePoint.some p}ᶜ : Set (OnePoint (Work.Tubular.Euc n))) := by
    intro y hy
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
    intro h
    have hcomp2 : (transT (-(p - p'))).comp (transT (p - p')) = ContinuousMap.id _ := by
      rw [transT_comp, show (p - p') + -(p - p') = 0 from add_neg_cancel _]
      ext z
      show OnePoint.map (fun w => w + (0 : Work.Tubular.Euc n)) z = z
      have hfun : (fun w : Work.Tubular.Euc n => w + (0 : Work.Tubular.Euc n)) = id := by
        funext w; simp
      rw [hfun]
      exact congrFun OnePoint.map_id z
    have hkey : transT (-(p - p')) (transT (p - p') y) = y :=
      congrArg (fun (f : C(OnePoint (Work.Tubular.Euc n), OnePoint (Work.Tubular.Euc n))) => f y)
        hcomp2
    have h2 := congrArg (transT (-(p - p'))) h
    rw [hkey] at h2
    exact hy (by rw [h2]; exact congrArg OnePoint.some (by module))
  let G : TopCat.of ↥(({OnePoint.some p'}ᶜ : Set (OnePoint (Work.Tubular.Euc n)))) ⟶
      TopCat.of ↥(({OnePoint.some p}ᶜ : Set (OnePoint (Work.Tubular.Euc n)))) :=
    TopCat.ofHom ⟨fun y => ⟨transT (p - p') y.1, hpair y.1 y.2⟩,
      Continuous.subtype_mk ((transT (p - p')).continuous.comp continuous_subtype_val) _⟩
  have hw : Work.Cohomology.subtypeIncl (TopCat.of (OnePoint (Work.Tubular.Euc n)))
        ({OnePoint.some p'}ᶜ) ≫ TopCat.ofHom (transT (p - p'))
      = G ≫ Work.Cohomology.subtypeIncl (TopCat.of (OnePoint (Work.Tubular.Euc n)))
        ({OnePoint.some p}ᶜ) := by
    apply TopCat.ext
    intro a
    rfl
  -- naturality of the pairing along `ρ`
  have hnat := Work.Tubular.relKronH_natural
    (X := TopCat.of (OnePoint (Work.Tubular.Euc n)))
    (Y := TopCat.of (OnePoint (Work.Tubular.Euc n)))
    (A := ({OnePoint.some p'}ᶜ : Set (OnePoint (Work.Tubular.Euc n))))
    (B := ({OnePoint.some p}ᶜ : Set (OnePoint (Work.Tubular.Euc n))))
    (TopCat.ofHom (transT (p - p'))) G hpair hw m
    ((Work.Thom.relCohMap (transT (-p)) ({OnePoint.some p}ᶜ) ({OnePoint.some 0}ᶜ)
      (transT_pair p) ℤ m).hom σ)
    (Work.Orient.locClass (TopCat.of (OnePoint (Work.Tubular.Euc n))) m u₀ (OnePoint.some p'))
  -- the pullback of `σ` through `ρ` is the pullback through `T_{-p'}`
  have hρ : (transT (-p)).comp (transT (p - p')) = transT (-p') := by
    rw [transT_comp]
    congr 1
    module
  have hgfp : ∀ x ∈ ({OnePoint.some p'}ᶜ : Set (OnePoint (Work.Tubular.Euc n))),
      (transT (-p)) ((transT (p - p')) x) ∈ ({OnePoint.some 0}ᶜ :
        Set (OnePoint (Work.Tubular.Euc n))) := fun x hx => by
    have hx' := congrArg (fun (f : C(OnePoint (Work.Tubular.Euc n), OnePoint (Work.Tubular.Euc n))) => f x) hρ
    rw [show (transT (-p)) ((transT (p - p')) x) = transT (-p') x from hx']
    exact transT_pair p' x hx
  have hcomp := Work.Thom.relCohMap_compA (X := OnePoint (Work.Tubular.Euc n))
    (Y := OnePoint (Work.Tubular.Euc n)) (Z := OnePoint (Work.Tubular.Euc n))
    (A := ({OnePoint.some p'}ᶜ : Set (OnePoint (Work.Tubular.Euc n))))
    (B := ({OnePoint.some p}ᶜ : Set (OnePoint (Work.Tubular.Euc n))))
    (C := ({OnePoint.some 0}ᶜ : Set (OnePoint (Work.Tubular.Euc n))))
    (f := transT (p - p')) (g := transT (-p)) (hf := hpair)
    (hg := transT_pair p) (hgf := hgfp) ℤ m
  have hβ : (Work.Thom.relCohMap (transT (p - p'))
        ({OnePoint.some p'}ᶜ) ({OnePoint.some p}ᶜ) hpair ℤ m).hom
        ((Work.Thom.relCohMap (transT (-p)) ({OnePoint.some p}ᶜ) ({OnePoint.some 0}ᶜ)
          (transT_pair p) ℤ m).hom σ)
      = (Work.Thom.relCohMap (transT (-p')) ({OnePoint.some p'}ᶜ) ({OnePoint.some 0}ᶜ)
          (transT_pair p') ℤ m).hom σ := by
    have hcongr := Work.Thom.relCohMap_congrA (A := ({OnePoint.some p'}ᶜ :
        Set (OnePoint (Work.Tubular.Euc n))))
      (B := ({OnePoint.some 0}ᶜ : Set (OnePoint (Work.Tubular.Euc n)))) hρ hgfp
      (transT_pair p') ℤ m
    have htot : (Work.Thom.relCohMap (transT (-p)) ({OnePoint.some p}ᶜ) ({OnePoint.some 0}ᶜ)
          (transT_pair p) ℤ m ≫ Work.Thom.relCohMap (transT (p - p')) ({OnePoint.some p'}ᶜ)
          ({OnePoint.some p}ᶜ) hpair ℤ m)
        = Work.Thom.relCohMap (transT (-p')) ({OnePoint.some p'}ᶜ) ({OnePoint.some 0}ᶜ)
          (transT_pair p') ℤ m := hcomp.trans hcongr
    simpa only [ModuleCat.comp_apply] using congrArg (fun g => g.hom σ) htot
  -- the pushforward of the local class of `u₀`
  have hloc := Work.ThomBordism.Transversality.OrientBridge.relLocClass_map_pair
    (M := TopCat.of (OnePoint (Work.Tubular.Euc n)))
    (M' := TopCat.of (OnePoint (Work.Tubular.Euc n))) (n := m)
    (TopCat.ofHom (transT (p - p')))
    (K := ({OnePoint.some p'} : Set (OnePoint (Work.Tubular.Euc n))))
    (K' := ({OnePoint.some p} : Set (OnePoint (Work.Tubular.Euc n)))) G hw u₀
  rw [transT_homologyMap_id (n := n) m (p - p')] at hloc
  rw [hβ] at hnat
  rw [hnat]
  simp only [Work.Orient.locClass_eq_relClass, Work.Orient.relClass]
  exact congrArg (fun z => Work.Tubular.relKronH (TopCat.of (OnePoint (Work.Tubular.Euc n)))
    ({OnePoint.some p}ᶜ : Set (OnePoint (Work.Tubular.Euc n))) m
    ((Work.Thom.relCohMap (transT (-p)) ({OnePoint.some p}ᶜ) ({OnePoint.some 0}ᶜ)
      (transT_pair p) ℤ m).hom σ) z) hloc.symm

end

end Work.ThomBordism
