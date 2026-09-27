import Mathlib
import Submission.Work.OneDim.Defs

/-!
# The seam data at a point of a one-manifold

Given an injective local diffeomorphism `φ : ℝ → C` onto the complement of a point `q` of a smooth
`1`-manifold, we extract a local coordinate `κ` at `q` in which the two ends of `φ` are
parametrised in the standard way, together with the two functions `f = 1/(κ ∘ φ)` and
`g = 1/(κ ∘ φ)` on the two ends used to glue the seam.  Everything is stated at the smoothness
level `C^∞` (`Work.OneDim.sm`).
-/

open scoped Manifold ContDiff
open Topology Set Function Filter

namespace Work.OneDim

noncomputable section

/-- The standard linear equivalence `ℝ ≃L[ℝ] E1`. -/
def stdLEsd : ℝ ≃L[ℝ] E1 :=
  (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans
    (EuclideanSpace.equiv (Fin 1) ℝ).symm.toContinuousLinearEquiv

variable {C : Type*} [TopologicalSpace C] [ChartedSpace E1 C] [IsManifold I1 sm C]

/-- **A local coordinate at `q`.**  The chart at `q`, transported along a linear equivalence to a
real-valued coordinate `ℝ`. -/
def chartPDsd (q : C) : PartialDiffeomorph I1 (modelWithCornersSelf ℝ ℝ) C ℝ sm where
  toPartialEquiv :=
    { toFun := fun y => stdLEsd.symm (chartAt E1 q y - chartAt E1 q q)
      invFun := fun r : ℝ => (chartAt E1 q).symm (stdLEsd r + chartAt E1 q q)
      source := (chartAt E1 q).source
      target := {r : ℝ | stdLEsd r + chartAt E1 q q ∈ (chartAt E1 q).target}
      map_source' := by
        intro y hy
        show stdLEsd (stdLEsd.symm (chartAt E1 q y - chartAt E1 q q)) + chartAt E1 q q ∈
          (chartAt E1 q).target
        rw [stdLEsd.apply_symm_apply, sub_add_cancel]
        exact (chartAt E1 q).map_source hy
      map_target' := by
        intro r hr
        exact (chartAt E1 q).map_target hr
      left_inv' := by
        intro y hy
        show (chartAt E1 q).symm (stdLEsd (stdLEsd.symm (chartAt E1 q y - chartAt E1 q q)) +
          chartAt E1 q q) = y
        rw [stdLEsd.apply_symm_apply, sub_add_cancel, (chartAt E1 q).left_inv hy]
      right_inv' := by
        intro r hr
        show stdLEsd.symm (chartAt E1 q ((chartAt E1 q).symm (stdLEsd r + chartAt E1 q q)) -
          chartAt E1 q q) = r
        rw [(chartAt E1 q).right_inv hr, add_sub_cancel_right, stdLEsd.symm_apply_apply] }
  open_source := (chartAt E1 q).open_source
  open_target := (chartAt E1 q).open_target.preimage
    (by fun_prop : Continuous fun r : ℝ => stdLEsd r + chartAt E1 q q)
  contMDiffOn_toFun := by
    have hΘ : ContMDiffOn I1 (modelWithCornersSelf ℝ E1) sm (⇑(chartAt E1 q))
        (chartAt E1 q).source := by
      simpa [extChartAt_coe] using contMDiffOn_extChartAt (I := I1) (x := q)
    have hA : ContDiff ℝ sm (fun v : E1 => stdLEsd.symm (v - chartAt E1 q q)) :=
      (stdLEsd.symm.contDiff).comp (contDiff_id.sub contDiff_const)
    exact hA.contMDiff.comp_contMDiffOn hΘ
  contMDiffOn_invFun := by
    have hΘ : ContMDiffOn (modelWithCornersSelf ℝ E1) I1 sm (⇑(chartAt E1 q).symm)
        (chartAt E1 q).target := by
      simpa [extChartAt_coe_symm, extChartAt_target] using contMDiffOn_extChartAt_symm (I := I1) q
    have hB : ContDiff ℝ sm (fun r : ℝ => stdLEsd r + chartAt E1 q q) :=
      (stdLEsd.contDiff.comp contDiff_id).add contDiff_const
    exact hΘ.comp (hB.contMDiff.contMDiffOn.mono (subset_univ _)) (fun r hr => hr)

theorem chartPD_mem (q : C) : q ∈ (chartPDsd q).source := mem_chart_source E1 q

theorem chartPD_apply_self (q : C) : chartPDsd q q = 0 := by
  show stdLEsd.symm (chartAt E1 q q - chartAt E1 q q) = 0
  rw [sub_self, map_zero]

/-- The chart coordinate is injective on the chart source. -/
theorem chartPD_injOn (q : C) : Set.InjOn (⇑(chartPDsd q)) (chartPDsd q).source :=
  (chartPDsd q).toPartialEquiv.injOn

/-- **A local coordinate at `q`.**  There is a partial diffeomorphism from `C` to `ℝ` whose source
is a neighbourhood of `q` and which sends `q` to `0`. -/
theorem exists_chart_coordinate (q : C) :
    ∃ Φ : PartialDiffeomorph I1 (modelWithCornersSelf ℝ ℝ) C ℝ sm,
      q ∈ Φ.source ∧ Φ q = 0 :=
  ⟨chartPDsd q, chartPD_mem q, chartPD_apply_self q⟩


/-! ## Negation and the two-sided sign lemma -/

/-- The negation map of `ℝ` as a partial diffeomorphism. -/
def negPDsd : PartialDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) ℝ ℝ sm where
  toPartialEquiv :=
    { toFun := fun y : ℝ => -y
      invFun := fun y : ℝ => -y
      source := Set.univ
      target := Set.univ
      map_source' := fun _ _ => Set.mem_univ _
      map_target' := fun y _ => Set.mem_univ _
      left_inv' := fun y _ => neg_neg y
      right_inv' := fun y _ => neg_neg y }
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := by
    rw [contMDiffOn_univ, contMDiff_iff_contDiff]
    exact contDiff_neg
  contMDiffOn_invFun := by
    rw [contMDiffOn_univ, contMDiff_iff_contDiff]
    exact contDiff_neg

@[simp] theorem negPD_source : negPDsd.source = Set.univ := rfl
@[simp] theorem negPD_apply (y : ℝ) : negPDsd y = -y := rfl

/-- Negation is a local diffeomorphism of `ℝ`. -/
theorem isLocalDiffeomorphAt_neg (x : ℝ) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
      sm (fun y : ℝ => -y) x :=
  ⟨negPDsd, by simp, fun y _ => by simp⟩

/-- Two preconnected subsets of `(0,∞)` both accumulating at `0` meet. -/
theorem nonempty_inter_of_preconnected_pos {C D : Set ℝ} (hC : IsPreconnected C)
    (hD : IsPreconnected D) (hCpos : C ⊆ Set.Ioi 0) (hDpos : D ⊆ Set.Ioi 0)
    (h0C : (0 : ℝ) ∈ closure C) (h0D : (0 : ℝ) ∈ closure D) : (C ∩ D).Nonempty := by
  obtain ⟨c, hc⟩ : C.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at h0C
    exact h0C
  obtain ⟨d, hd⟩ : D.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at h0D
    exact h0D
  have hcd : 0 < min c d := lt_min (hCpos hc) (hDpos hd)
  have hbelowC : ∀ x : ℝ, 0 < x → ∃ y ∈ C, y < x := by
    intro x hx
    obtain ⟨y, hyC, hy⟩ := Metric.mem_closure_iff.mp h0C x hx
    have hyabs : |y| < x := by simpa [Real.dist_eq, sub_zero] using hy
    exact ⟨y, hyC, (abs_lt.mp hyabs).2⟩
  have hbelowD : ∀ x : ℝ, 0 < x → ∃ y ∈ D, y < x := by
    intro x hx
    obtain ⟨y, hyD, hy⟩ := Metric.mem_closure_iff.mp h0D x hx
    have hyabs : |y| < x := by simpa [Real.dist_eq, sub_zero] using hy
    exact ⟨y, hyD, (abs_lt.mp hyabs).2⟩
  have hmid : 0 < min c d / 2 := by positivity
  have hleC : min c d / 2 ≤ c := (half_lt_self hcd).trans_le (min_le_left c d) |>.le
  have hleD : min c d / 2 ≤ d := (half_lt_self hcd).trans_le (min_le_right c d) |>.le
  refine ⟨min c d / 2, ?_, ?_⟩
  · obtain ⟨y, hyC, hyx⟩ := hbelowC (min c d / 2) hmid
    exact hC.ordConnected.out hyC hc (Set.mem_Icc.mpr ⟨hyx.le, hleC⟩)
  · obtain ⟨y, hyD, hyx⟩ := hbelowD (min c d / 2) hmid
    exact hD.ordConnected.out hyD hd (Set.mem_Icc.mpr ⟨hyx.le, hleD⟩)


/-- Two preconnected subsets of `(-∞,0)` both accumulating at `0` meet. -/
theorem nonempty_inter_of_preconnected_neg {C D : Set ℝ} (hC : IsPreconnected C)
    (hD : IsPreconnected D) (hCneg : C ⊆ Set.Iio 0) (hDneg : D ⊆ Set.Iio 0)
    (h0C : (0 : ℝ) ∈ closure C) (h0D : (0 : ℝ) ∈ closure D) : (C ∩ D).Nonempty := by
  have h0C' : (0 : ℝ) ∈ closure ((fun x : ℝ => -x) '' C) :=
    image_closure_subset_closure_image continuous_neg (s := C) ⟨0, h0C, by simp⟩
  have h0D' : (0 : ℝ) ∈ closure ((fun x : ℝ => -x) '' D) :=
    image_closure_subset_closure_image continuous_neg (s := D) ⟨0, h0D, by simp⟩
  obtain ⟨z, hzC, hzD⟩ :=
    nonempty_inter_of_preconnected_pos (C := (fun x : ℝ => -x) '' C)
      (D := (fun x : ℝ => -x) '' D)
      (hC.image (fun x : ℝ => -x) continuous_neg.continuousOn)
      (hD.image (fun x : ℝ => -x) continuous_neg.continuousOn)
      (by rintro z ⟨x, hx, rfl⟩; exact neg_pos.mpr (by simpa using hCneg hx))
      (by rintro z ⟨x, hx, rfl⟩; exact neg_pos.mpr (by simpa using hDneg hx)) h0C' h0D'
  obtain ⟨x, hx, hxz⟩ := hzC
  obtain ⟨y, hy, hyz⟩ := hzD
  exact ⟨-z, by rw [← hxz]; simpa using hx, by rw [← hyz]; simpa using hy⟩

/-- If `F` tends to `0` at both ends, is continuous and nonvanishing on the two tails and takes
different values on the two tails, then it has opposite signs on the two tails. -/
theorem signs_opposite_of_tendsto_zero {F : ℝ → ℝ} {T : ℝ}
    (hcontC : ContinuousOn F (Set.Ici T)) (hcontD : ContinuousOn F (Set.Iic (-T)))
    (hneC : ∀ t, T ≤ t → F t ≠ 0) (hneD : ∀ t, t ≤ -T → F t ≠ 0)
    (htop : Tendsto F atTop (𝓝 0)) (hbot : Tendsto F atBot (𝓝 0))
    (hinj : ∀ ⦃t₁ t₂ : ℝ⦄, T ≤ t₁ → t₂ ≤ -T → F t₁ ≠ F t₂) :
    ((∀ t, T ≤ t → 0 < F t) ∧ (∀ t, t ≤ -T → F t < 0)) ∨
      ((∀ t, T ≤ t → F t < 0) ∧ (∀ t, t ≤ -T → 0 < F t)) := by
  have hposC : (∀ t, T ≤ t → 0 < F t) ∨ (∀ t, T ≤ t → F t < 0) := by
    have hpre : IsPreconnected (F '' Set.Ici T) := isPreconnected_Ici.image F hcontC
    have hsub : F '' Set.Ici T ⊆ Set.Ioi 0 ∪ Set.Iio 0 := by
      rintro z ⟨t, ht, rfl⟩
      rcases lt_trichotomy (F t) 0 with h | h | h
      · exact Or.inr h
      · exact absurd h (hneC t ht)
      · exact Or.inl h
    rcases hpre.subset_or_subset isOpen_Ioi isOpen_Iio
      (Set.disjoint_left.mpr fun x hx hy => absurd hx (not_lt.mpr hy.le)) hsub with h | h
    · left; intro t ht; exact h ⟨t, ht, rfl⟩
    · right; intro t ht; exact h ⟨t, ht, rfl⟩
  have hposD : (∀ t, t ≤ -T → 0 < F t) ∨ (∀ t, t ≤ -T → F t < 0) := by
    have hpre : IsPreconnected (F '' Set.Iic (-T)) := isPreconnected_Iic.image F hcontD
    have hsub : F '' Set.Iic (-T) ⊆ Set.Ioi 0 ∪ Set.Iio 0 := by
      rintro z ⟨t, ht, rfl⟩
      rcases lt_trichotomy (F t) 0 with h | h | h
      · exact Or.inr h
      · exact absurd h (hneD t ht)
      · exact Or.inl h
    rcases hpre.subset_or_subset isOpen_Ioi isOpen_Iio
      (Set.disjoint_left.mpr fun x hx hy => absurd hx (not_lt.mpr hy.le)) hsub with h | h
    · left; intro t ht; exact h ⟨t, ht, rfl⟩
    · right; intro t ht; exact h ⟨t, ht, rfl⟩
  have h0C : (0 : ℝ) ∈ closure (F '' Set.Ici T) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hev : ∀ᶠ t in atTop, F t ∈ Metric.ball 0 ε :=
      htop.eventually (Metric.ball_mem_nhds 0 hε)
    have hevT : ∀ᶠ t in atTop, T ≤ t := eventually_ge_atTop T
    obtain ⟨t, htε, htT⟩ := (hev.and hevT).exists
    exact ⟨F t, ⟨t, htT, rfl⟩, by simpa [Metric.mem_ball] using htε⟩
  have h0D : (0 : ℝ) ∈ closure (F '' Set.Iic (-T)) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hev : ∀ᶠ t in atBot, F t ∈ Metric.ball 0 ε :=
      hbot.eventually (Metric.ball_mem_nhds 0 hε)
    have hevT : ∀ᶠ t in atBot, t ≤ -T := eventually_le_atBot (-T)
    obtain ⟨t, htε, htT⟩ := (hev.and hevT).exists
    exact ⟨F t, ⟨t, htT, rfl⟩, by simpa [Metric.mem_ball] using htε⟩
  rcases hposC with hC | hC <;> rcases hposD with hD | hD
  · exfalso
    have hpreC : IsPreconnected (F '' Set.Ici T) := isPreconnected_Ici.image F hcontC
    have hpreD : IsPreconnected (F '' Set.Iic (-T)) := isPreconnected_Iic.image F hcontD
    obtain ⟨z, hzC, hzD⟩ := nonempty_inter_of_preconnected_pos hpreC hpreD
      (by rintro z ⟨t, ht, htz⟩; rw [← htz]; exact hC t ht)
      (by rintro z ⟨t, ht, htz⟩; rw [← htz]; exact hD t ht) h0C h0D
    obtain ⟨t₁, ht₁, h₁⟩ := hzC
    obtain ⟨t₂, ht₂, h₂⟩ := hzD
    exact hinj ht₁ ht₂ (h₁.trans h₂.symm)
  · exact Or.inl ⟨hC, hD⟩
  · exact Or.inr ⟨hC, hD⟩
  · exfalso
    have hpreC : IsPreconnected (F '' Set.Ici T) := isPreconnected_Ici.image F hcontC
    have hpreD : IsPreconnected (F '' Set.Iic (-T)) := isPreconnected_Iic.image F hcontD
    obtain ⟨z, hzC, hzD⟩ := nonempty_inter_of_preconnected_neg hpreC hpreD
      (by rintro z ⟨t, ht, htz⟩; rw [← htz]; exact hC t ht)
      (by rintro z ⟨t, ht, htz⟩; rw [← htz]; exact hD t ht) h0C h0D
    obtain ⟨t₁, ht₁, h₁⟩ := hzC
    obtain ⟨t₂, ht₂, h₂⟩ := hzD
    exact hinj ht₁ ht₂ (h₁.trans h₂.symm)

/-! ## Auxiliary analytic facts about the two ends -/

/-- The reciprocal map as a partial diffeomorphism of `ℝ`. -/
def invPD : PartialDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) ℝ ℝ sm where
  toPartialEquiv :=
    { toFun := fun y : ℝ => y⁻¹
      invFun := fun y : ℝ => y⁻¹
      source := {y : ℝ | y ≠ 0}
      target := {y : ℝ | y ≠ 0}
      map_source' := fun y hy => inv_ne_zero hy
      map_target' := fun y hy => inv_ne_zero hy
      left_inv' := fun y hy => inv_inv y
      right_inv' := fun y hy => inv_inv y }
  open_source := isOpen_ne
  open_target := isOpen_ne
  contMDiffOn_toFun := by
    rw [contMDiffOn_iff_contDiffOn]
    exact contDiffOn_inv (𝕜 := ℝ) (𝕜' := ℝ) (n := sm)
  contMDiffOn_invFun := by
    rw [contMDiffOn_iff_contDiffOn]
    exact contDiffOn_inv (𝕜 := ℝ) (𝕜' := ℝ) (n := sm)

/-- The reciprocal is a local diffeomorphism at a nonzero point. -/
theorem isLocalDiffeomorphAt_inv {x : ℝ} (hx : x ≠ 0) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) sm
      (fun y : ℝ => y⁻¹) x :=
  ⟨invPD, hx, fun y _ => rfl⟩

/-- A local diffeomorphism `ℝ → ℝ` has nonzero derivative. -/
theorem deriv_ne_zero_of_isLocalDiffeomorphAt_sd {f : ℝ → ℝ} {x : ℝ}
    (hf : IsLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) sm f x) :
    deriv f x ≠ 0 := by
  intro h0
  have hn : sm ≠ 0 := by decide
  have hcoe2 : ((hf.mfderivToContinuousLinearEquiv hn :
      TangentSpace (modelWithCornersSelf ℝ ℝ) x →L[ℝ]
        TangentSpace (modelWithCornersSelf ℝ ℝ) (f x))) = fderiv ℝ f x := by
    rw [IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe hf hn, mfderiv_eq_fderiv]
  have hinj : Function.Injective (fderiv ℝ f x) := by
    intro a b hab
    rw [← hcoe2] at hab
    exact (hf.mfderivToContinuousLinearEquiv hn).injective hab
  have h1 : fderiv ℝ f x 1 = 0 := by
    rw [fderiv_apply_one_eq_deriv, h0]
  exact one_ne_zero (hinj (by rw [h1, map_zero]))

/-- **The positive end.**  If `H` is smooth, injective and positive on a right ray and tends to `0`
at `+∞`, then its reciprocal has positive derivative there and tends to `+∞`. -/
theorem pos_end_data {H : ℝ → ℝ} {T : ℝ}
    (hsm : ContDiffOn ℝ sm H (Set.Ici T))
    (hinj : Set.InjOn H (Set.Ici T))
    (hpos : ∀ t, T ≤ t → 0 < H t)
    (hlim : Filter.Tendsto H Filter.atTop (𝓝 0))
    (hld : ∀ t, T < t →
      IsLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) sm
        (fun s => (H s)⁻¹) t) :
    ContDiffOn ℝ sm (fun t => (H t)⁻¹) (Set.Ici T) ∧
      (∀ t, T < t → 0 < deriv (fun t => (H t)⁻¹) t) ∧
      Filter.Tendsto (fun t => (H t)⁻¹) Filter.atTop Filter.atTop := by
  have hinv_sm : ContDiffOn ℝ sm (fun t => (H t)⁻¹) (Set.Ici T) :=
    hsm.inv (fun t ht => ne_of_gt (hpos t ht))
  have hcont_inv : ContinuousOn (fun t => (H t)⁻¹) (Set.Ici T) := hinv_sm.continuousOn
  have hinj_inv : Set.InjOn (fun t => (H t)⁻¹) (Set.Ici T) :=
    fun a ha b hb h => hinj ha hb (inv_injective h)
  refine ⟨hinv_sm, ?_, ?_⟩
  · intro t ht
    have hne : deriv (fun s => (H s)⁻¹) t ≠ 0 :=
      deriv_ne_zero_of_isLocalDiffeomorphAt_sd (hld t ht)
    obtain ⟨s', hs't, hs'gt⟩ : ∃ s', t < s' ∧ (H t)⁻¹ < (H s')⁻¹ := by
      have hev : ∀ᶠ u in Filter.atTop, H u < H t :=
        hlim.eventually (eventually_lt_nhds (hpos t ht.le))
      obtain ⟨u, hu⟩ := eventually_atTop.mp hev
      refine ⟨max u (t + 1), lt_of_lt_of_le (lt_add_one t) (le_max_right _ _), ?_⟩
      have hT1 : T ≤ max u (t + 1) := by
        have h := le_max_right u (t + 1); linarith
      have h2 : 0 < H (max u (t + 1)) := hpos _ hT1
      have h3 : H (max u (t + 1)) < H t := hu _ (le_max_left _ _)
      simpa only [one_div] using one_div_lt_one_div_of_lt h2 h3
    set s : ℝ := (T + t) / 2 with hsdef
    have hTs : T < s := by rw [hsdef]; linarith
    have hst : s < t := by rw [hsdef]; linarith
    have hsmono : StrictMonoOn (fun u => (H u)⁻¹) (Set.Icc s s') := by
      rcases ContinuousOn.strictMonoOn_of_injOn_Icc' (le_of_lt (lt_trans hst hs't))
        (hcont_inv.mono (fun u hu => hTs.le.trans hu.1))
        (hinj_inv.mono (fun u hu => hTs.le.trans hu.1)) with h | h
      · exact h
      · exfalso
        have h1 : (H s')⁻¹ < (H t)⁻¹ :=
            h ⟨hst.le, hs't.le⟩ ⟨hst.le.trans hs't.le, le_rfl⟩ hs't
        exact absurd hs'gt (not_lt.mpr h1.le)
    have hderiv : 0 ≤ deriv (fun u => (H u)⁻¹) t := by
      rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hst hs't)]
      exact hsmono.monotoneOn.derivWithin_nonneg
    exact lt_of_le_of_ne hderiv (Ne.symm hne)
  · rw [tendsto_atTop]
    intro M
    by_cases hM : M ≤ 0
    · filter_upwards [eventually_ge_atTop T] with u hu
      have h1 : 0 < H u := hpos u hu
      have h2 : 0 < (H u)⁻¹ := inv_pos.mpr h1
      linarith
    · have hMpos : 0 < M := not_le.mp hM
      have hev : ∀ᶠ u in Filter.atTop, H u < M⁻¹ :=
        hlim.eventually (eventually_lt_nhds (inv_pos.mpr hMpos))
      filter_upwards [hev, eventually_ge_atTop T] with u hu huT
      have hgoal : M < (H u)⁻¹ := by
        have h3 : (M⁻¹)⁻¹ < (H u)⁻¹ := by
          simpa only [one_div] using one_div_lt_one_div_of_lt (hpos u huT) hu
        simpa only [inv_inv] using h3
      exact hgoal.le

/-- **The negative end.**  If `H` is smooth, injective and negative on a left ray and tends to `0`
at `-∞`, then its reciprocal has positive derivative there and tends to `-∞`. -/
theorem neg_end_data {H : ℝ → ℝ} {T : ℝ}
    (hsm : ContDiffOn ℝ sm H (Set.Iic T))
    (hinj : Set.InjOn H (Set.Iic T))
    (hneg : ∀ t, t ≤ T → H t < 0)
    (hlim : Filter.Tendsto H Filter.atBot (𝓝 0))
    (hld : ∀ t, t < T →
      IsLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) sm
        (fun s => (H s)⁻¹) t) :
    ContDiffOn ℝ sm (fun t => (H t)⁻¹) (Set.Iic T) ∧
      (∀ t, t < T → 0 < deriv (fun t => (H t)⁻¹) t) ∧
      Filter.Tendsto (fun t => (H t)⁻¹) Filter.atBot Filter.atBot := by
  have hinv_sm : ContDiffOn ℝ sm (fun t => (H t)⁻¹) (Set.Iic T) :=
    hsm.inv (fun t ht => ne_of_lt (hneg t ht))
  have hcont_inv : ContinuousOn (fun t => (H t)⁻¹) (Set.Iic T) := hinv_sm.continuousOn
  have hinj_inv : Set.InjOn (fun t => (H t)⁻¹) (Set.Iic T) :=
    fun a ha b hb h => hinj ha hb (inv_injective h)
  refine ⟨hinv_sm, ?_, ?_⟩
  · intro t ht
    have hne : deriv (fun s => (H s)⁻¹) t ≠ 0 :=
      deriv_ne_zero_of_isLocalDiffeomorphAt_sd (hld t ht)
    obtain ⟨s', hs't, hs'lt⟩ : ∃ s', s' < t ∧ (H s')⁻¹ < (H t)⁻¹ := by
      have hev : ∀ᶠ u in Filter.atBot, H t < H u :=
        hlim.eventually (eventually_gt_nhds (hneg t ht.le))
      obtain ⟨u, hu⟩ := eventually_atBot.mp hev
      refine ⟨min u (t - 1), lt_of_le_of_lt (min_le_right u (t - 1)) (by linarith), ?_⟩
      have h1 : H (min u (t - 1)) < 0 :=
        hneg _ (by have hm := min_le_right u (t - 1); linarith)
      have h2 : H t < 0 := hneg t ht.le
      have h3 : H t < H (min u (t - 1)) := hu _ (min_le_left u (t - 1))
      exact (inv_lt_inv_of_neg h1 h2).mpr h3
    have hsmono : StrictMonoOn (fun u => (H u)⁻¹) (Set.Icc s' T) := by
      rcases ContinuousOn.strictMonoOn_of_injOn_Icc' (le_of_lt (lt_trans hs't ht))
        (hcont_inv.mono (fun u hu => hu.2))
        (hinj_inv.mono (fun u hu => hu.2)) with h | h
      · exact h
      · exfalso
        have h1 : (H t)⁻¹ < (H s')⁻¹ :=
          h ⟨le_rfl, (le_of_lt hs't).trans ht.le⟩ ⟨hs't.le, ht.le⟩ hs't
        exact absurd hs'lt (not_lt.mpr h1.le)
    have hderiv : 0 ≤ deriv (fun u => (H u)⁻¹) t := by
      rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hs't ht)]
      exact hsmono.monotoneOn.derivWithin_nonneg
    exact lt_of_le_of_ne hderiv (Ne.symm hne)
  · rw [tendsto_atBot]
    intro M
    by_cases hM : 0 ≤ M
    · filter_upwards [eventually_le_atBot T] with u hu
      have h1 : H u < 0 := hneg u hu
      have h2 : (H u)⁻¹ < 0 := inv_lt_zero'.mpr h1
      linarith
    · have hMneg : M < 0 := not_le.mp hM
      have hMinv : M⁻¹ < 0 := inv_lt_zero'.mpr hMneg
      have hev : ∀ᶠ u in Filter.atBot, M⁻¹ < H u :=
        hlim.eventually (eventually_gt_nhds hMinv)
      filter_upwards [hev, eventually_le_atBot T] with u hu huT
      have h1 : H u < 0 := hneg u huT
      have h2 : (H u)⁻¹ < M := by
        have h3 := (inv_lt_inv_of_neg h1 hMinv).mpr hu
        simpa using h3
      exact h2.le

/-! ## Composing the chart with the parametrisation -/

/-- The reciprocal of `κ ∘ φ` is a local diffeomorphism where `κ ∘ φ` does not vanish. -/
theorem recip_localDiffeomorphAt {φ : ℝ → C} {κ : C → ℝ} {t : ℝ}
    (hφ : IsLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ) I1 sm φ t)
    (hκ : IsLocalDiffeomorphAt I1 (modelWithCornersSelf ℝ ℝ) sm κ (φ t))
    (hne : κ (φ t) ≠ 0) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) sm
      (fun s => (κ (φ s))⁻¹) t :=
  IsLocalDiffeomorphAt.comp (K := modelWithCornersSelf ℝ ℝ) (P := ℝ)
    (IsLocalDiffeomorphAt.comp (K := modelWithCornersSelf ℝ ℝ) (P := ℝ) hφ hκ)
    (isLocalDiffeomorphAt_inv hne)

/-- The whole tail package: if `κ` has the standard seam properties on the two tails, then
`f = 1/(κ ∘ φ)` has all the properties needed to glue. -/
theorem tail_data_of_chart {φ : ℝ → C} {κ : C → ℝ} {T : ℝ}
    (hsm_rt : ContDiffOn ℝ sm (fun t => κ (φ t)) (Set.Ici T))
    (hsm_lf : ContDiffOn ℝ sm (fun t => κ (φ t)) (Set.Iic (-T)))
    (hpos : ∀ t, T ≤ t → 0 < κ (φ t))
    (hneg : ∀ t, t ≤ -T → κ (φ t) < 0)
    (hlim_rt : Filter.Tendsto (fun t => κ (φ t)) Filter.atTop (𝓝 0))
    (hlim_lf : Filter.Tendsto (fun t => κ (φ t)) Filter.atBot (𝓝 0))
    (hinj_rt : Set.InjOn (fun t => κ (φ t)) (Set.Ici T))
    (hinj_lf : Set.InjOn (fun t => κ (φ t)) (Set.Iic (-T)))
    (hld_rt : ∀ t, T < t →
      IsLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) sm
        (fun s => (κ (φ s))⁻¹) t)
    (hld_lf : ∀ t, t < -T →
      IsLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) sm
        (fun s => (κ (φ s))⁻¹) t) :
    ContDiffOn ℝ sm (fun t => (κ (φ t))⁻¹) (Set.Ici (T + 1)) ∧
      (∀ t, T + 1 ≤ t → 0 < deriv (fun t => (κ (φ t))⁻¹) t) ∧
      Filter.Tendsto (fun t => (κ (φ t))⁻¹) Filter.atTop Filter.atTop ∧
      ContDiffOn ℝ sm (fun t => (κ (φ t))⁻¹) (Set.Iic (-(T + 1))) ∧
      (∀ t, t ≤ -(T + 1) → 0 < deriv (fun t => (κ (φ t))⁻¹) t) ∧
      Filter.Tendsto (fun t => (κ (φ t))⁻¹) Filter.atBot Filter.atBot := by
  have hR := pos_end_data (H := fun t => κ (φ t)) (T := T) hsm_rt hinj_rt hpos hlim_rt hld_rt
  have hL := neg_end_data (H := fun t => κ (φ t)) (T := -T) hsm_lf hinj_lf hneg hlim_lf hld_lf
  refine ⟨hR.1.mono (Ici_subset_Ici.mpr (by linarith)), ?_, hR.2.2,
    hL.1.mono (Iic_subset_Iic.mpr (by linarith)), ?_, hL.2.2⟩
  · intro t ht; exact hR.2.1 t (by linarith)
  · intro t ht; exact hL.2.1 t (by linarith)

/-! ## The main statement -/

theorem seam_chart_data {C : Type*} [TopologicalSpace C] [ChartedSpace E1 C]
    [IsManifold I1 sm C] [T2Space C] [SecondCountableTopology C]
    {q : C} {φ : ℝ → C}
    (hinj : Function.Injective φ)
    (hld : IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 sm φ)
    (hrange : Set.range φ = Set.compl ({q} : Set C))
    (htop : Filter.Tendsto φ Filter.atTop (nhds q))
    (hbot : Filter.Tendsto φ Filter.atBot (nhds q)) :
    ∃ (κ : C → ℝ) (T : ℝ) (f g : ℝ → ℝ),
      IsLocalDiffeomorphAt I1 (modelWithCornersSelf ℝ ℝ) sm κ q ∧
      κ q = 0 ∧
      (∀ t, T ≤ t → 0 < κ (φ t)) ∧ (∀ t, t ≤ -T → κ (φ t) < 0) ∧
      (∀ t, T ≤ t → f t = 1 / κ (φ t)) ∧ (∀ t, t ≤ -T → g t = 1 / κ (φ t)) ∧
      ContDiffOn ℝ sm f (Set.Ici T) ∧
      (∀ t, T ≤ t → 0 < deriv f t) ∧
      Filter.Tendsto f Filter.atTop Filter.atTop ∧
      ContDiffOn ℝ sm g (Set.Iic (-T)) ∧
      (∀ t, t ≤ -T → 0 < deriv g t) ∧
      Filter.Tendsto g Filter.atBot Filter.atBot := by
  classical
  have hφq : ∀ t : ℝ, φ t ≠ q := by
    intro t h
    have hmem : q ∈ Set.range φ := ⟨t, h⟩
    rw [hrange] at hmem
    exact hmem (Set.mem_singleton_iff.mpr rfl)
  have hφsm : ContMDiff 𝓘(ℝ,ℝ) I1 sm φ := hld.contMDiff
  -- ### the chart neighbourhood and the threshold
  have hsrc : (chartPDsd q).source ∈ 𝓝 q := (chartPDsd q).open_source.mem_nhds (chartPD_mem q)
  obtain ⟨Tup, hTup⟩ := Filter.eventually_atTop.mp (htop.eventually hsrc)
  obtain ⟨Tdn, hTdn⟩ := Filter.eventually_atBot.mp (hbot.eventually hsrc)
  have hTup' : ∀ t, Tup ≤ t → φ t ∈ (chartPDsd q).source := hTup
  have hTdn' : ∀ t, t ≤ Tdn → φ t ∈ (chartPDsd q).source := hTdn
  set T₁ : ℝ := max (max Tup (-Tdn)) 0 + 1 with hT₁def
  have hT₁pos : 0 < T₁ := by rw [hT₁def]; linarith [le_max_right (max Tup (-Tdn)) (0 : ℝ)]
  have hT₁Tup : Tup ≤ T₁ := by
    rw [hT₁def]; linarith [le_max_left (max Tup (-Tdn)) 0, le_max_left Tup (-Tdn)]
  have hT₁Tdn : -Tdn ≤ T₁ := by
    rw [hT₁def]; linarith [le_max_left (max Tup (-Tdn)) 0, le_max_right Tup (-Tdn)]
  have hsrcRt : ∀ t, T₁ ≤ t → φ t ∈ (chartPDsd q).source := fun t ht => hTup' t (hT₁Tup.trans ht)
  have hsrcLf : ∀ t, t ≤ -T₁ → φ t ∈ (chartPDsd q).source :=
    fun t ht => hTdn' t (ht.trans (by linarith))
  -- ### smoothness of `κ₀ ∘ φ` on the two tails
  have hsm_rt : ContDiffOn ℝ sm (fun t => (chartPDsd q) (φ t)) (Set.Ici T₁) := by
    have h : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) sm (fun t => (chartPDsd q) (φ t)) (Set.Ici T₁) :=
      (chartPDsd q).contMDiffOn_toFun.comp (hφsm.contMDiffOn (s := Set.Ici T₁))
        (fun t ht => hsrcRt t ht)
    exact contMDiffOn_iff_contDiffOn.mp h
  have hsm_lf : ContDiffOn ℝ sm (fun t => (chartPDsd q) (φ t)) (Set.Iic (-T₁)) := by
    have h : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) sm (fun t => (chartPDsd q) (φ t)) (Set.Iic (-T₁)) :=
      (chartPDsd q).contMDiffOn_toFun.comp (hφsm.contMDiffOn (s := Set.Iic (-T₁)))
        (fun t ht => hsrcLf t ht)
    exact contMDiffOn_iff_contDiffOn.mp h
  -- ### the limits
  have hκ₀c : ContinuousAt (⇑(chartPDsd q)) q :=
    ((chartPDsd q).contMDiffOn_toFun.contMDiffAt hsrc).continuousAt
  have hlim_rt : Filter.Tendsto (fun t => (chartPDsd q) (φ t)) Filter.atTop (𝓝 0) := by
    have h : Filter.Tendsto (fun t => (chartPDsd q) (φ t)) Filter.atTop (𝓝 ((chartPDsd q) q)) :=
      hκ₀c.tendsto.comp htop
    simpa [chartPD_apply_self q] using h
  have hlim_lf : Filter.Tendsto (fun t => (chartPDsd q) (φ t)) Filter.atBot (𝓝 0) := by
    have h : Filter.Tendsto (fun t => (chartPDsd q) (φ t)) Filter.atBot (𝓝 ((chartPDsd q) q)) :=
      hκ₀c.tendsto.comp hbot
    simpa [chartPD_apply_self q] using h
  -- ### nonvanishing
  have hne_rt : ∀ t, T₁ ≤ t → (chartPDsd q) (φ t) ≠ 0 := by
    intro t ht h
    have heq : (chartPDsd q) (φ t) = (chartPDsd q) q := by rw [h, chartPD_apply_self]
    exact hφq t (chartPD_injOn q (hsrcRt t ht) (chartPD_mem q) heq)
  have hne_lf : ∀ t, t ≤ -T₁ → (chartPDsd q) (φ t) ≠ 0 := by
    intro t ht h
    have heq : (chartPDsd q) (φ t) = (chartPDsd q) q := by rw [h, chartPD_apply_self]
    exact hφq t (chartPD_injOn q (hsrcLf t ht) (chartPD_mem q) heq)
  -- ### injectivity on the tails
  have hinj_rt : Set.InjOn (fun t => (chartPDsd q) (φ t)) (Set.Ici T₁) := by
    intro a ha b hb hab
    exact hinj (chartPD_injOn q (hsrcRt a ha) (hsrcRt b hb) hab)
  have hinj_lf : Set.InjOn (fun t => (chartPDsd q) (φ t)) (Set.Iic (-T₁)) := by
    intro a ha b hb hab
    exact hinj (chartPD_injOn q (hsrcLf a ha) (hsrcLf b hb) hab)
  -- ### the sign dichotomy
  have hdich : ((∀ t, T₁ ≤ t → 0 < (chartPDsd q) (φ t)) ∧
      (∀ t, t ≤ -T₁ → (chartPDsd q) (φ t) < 0)) ∨
      ((∀ t, T₁ ≤ t → (chartPDsd q) (φ t) < 0) ∧
        (∀ t, t ≤ -T₁ → 0 < (chartPDsd q) (φ t))) :=
    signs_opposite_of_tendsto_zero (F := fun t => (chartPDsd q) (φ t))
      hsm_rt.continuousOn hsm_lf.continuousOn hne_rt hne_lf hlim_rt hlim_lf
      (fun t₁ t₂ h₁ h₂ heq => by
        have h12 : t₁ = t₂ :=
          hinj (chartPD_injOn q (hsrcRt t₁ h₁) (hsrcLf t₂ h₂) heq)
        have hlt : t₂ < t₁ := lt_of_le_of_lt h₂ (by linarith)
        exact absurd h12 (ne_of_gt hlt))
  rcases hdich with ⟨hApos, hAneg⟩ | ⟨hBneg, hBpos⟩
  · -- ### orientation A: `κ = chartPDsd q`
    have hldR : ∀ t, T₁ < t →
        IsLocalDiffeomorphAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) sm (fun s => ((chartPDsd q) (φ s))⁻¹) t :=
      fun t ht => recip_localDiffeomorphAt (hld t)
        ⟨chartPDsd q, hsrcRt t ht.le, fun _ _ => rfl⟩ (hne_rt t ht.le)
    have hldL : ∀ t, t < -T₁ →
        IsLocalDiffeomorphAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) sm (fun s => ((chartPDsd q) (φ s))⁻¹) t :=
      fun t ht => recip_localDiffeomorphAt (hld t)
        ⟨chartPDsd q, hsrcLf t ht.le, fun _ _ => rfl⟩ (hne_lf t ht.le)
    have htail := tail_data_of_chart (κ := ⇑(chartPDsd q)) hsm_rt hsm_lf hApos hAneg hlim_rt hlim_lf
      hinj_rt hinj_lf hldR hldL
    refine ⟨⇑(chartPDsd q), T₁ + 1, (fun t => ((chartPDsd q) (φ t))⁻¹),
      (fun t => ((chartPDsd q) (φ t))⁻¹),
      ⟨chartPDsd q, chartPD_mem q, fun _ _ => rfl⟩, chartPD_apply_self q,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht; exact hApos t (by linarith)
    · intro t ht; exact hAneg t (by linarith)
    · intro t ht; rw [one_div]
    · intro t ht; rw [one_div]
    · exact htail.1
    · exact htail.2.1
    · exact htail.2.2.1
    · exact htail.2.2.2.1
    · exact htail.2.2.2.2.1
    · exact htail.2.2.2.2.2
  · -- ### orientation B: `κ = - chartPDsd q`
    have hsm_rt' : ContDiffOn ℝ sm (fun t => -((chartPDsd q) (φ t))) (Set.Ici T₁) := hsm_rt.neg
    have hsm_lf' : ContDiffOn ℝ sm (fun t => -((chartPDsd q) (φ t))) (Set.Iic (-T₁)) := hsm_lf.neg
    have hlim_rt' : Filter.Tendsto (fun t => -((chartPDsd q) (φ t))) Filter.atTop (𝓝 0) := by
      have h : Filter.Tendsto (fun t => -((chartPDsd q) (φ t))) Filter.atTop (𝓝 (-(0 : ℝ))) :=
        (continuous_neg.tendsto (0 : ℝ)).comp hlim_rt
      simpa using h
    have hlim_lf' : Filter.Tendsto (fun t => -((chartPDsd q) (φ t))) Filter.atBot (𝓝 0) := by
      have h : Filter.Tendsto (fun t => -((chartPDsd q) (φ t))) Filter.atBot (𝓝 (-(0 : ℝ))) :=
        (continuous_neg.tendsto (0 : ℝ)).comp hlim_lf
      simpa using h
    have hinj_rt' : Set.InjOn (fun t => -((chartPDsd q) (φ t))) (Set.Ici T₁) :=
      fun a ha b hb h => hinj_rt ha hb (by linarith [h])
    have hinj_lf' : Set.InjOn (fun t => -((chartPDsd q) (φ t))) (Set.Iic (-T₁)) :=
      fun a ha b hb h => hinj_lf ha hb (by linarith [h])
    have hldR : ∀ t, T₁ < t →
        IsLocalDiffeomorphAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) sm (fun s => (-((chartPDsd q) (φ s)))⁻¹) t := by
      intro t ht
      have h1 : IsLocalDiffeomorphAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) sm
          (fun s => -(((chartPDsd q) (φ s))⁻¹)) t :=
        IsLocalDiffeomorphAt.comp (K := 𝓘(ℝ,ℝ)) (P := ℝ)
          (recip_localDiffeomorphAt (hld t) ⟨chartPDsd q, hsrcRt t ht.le, fun _ _ => rfl⟩
            (hne_rt t ht.le))
          (isLocalDiffeomorphAt_neg (((chartPDsd q) (φ t))⁻¹))
      simpa [inv_neg] using h1
    have hldL : ∀ t, t < -T₁ →
        IsLocalDiffeomorphAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) sm (fun s => (-((chartPDsd q) (φ s)))⁻¹) t := by
      intro t ht
      have h1 : IsLocalDiffeomorphAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) sm
          (fun s => -(((chartPDsd q) (φ s))⁻¹)) t :=
        IsLocalDiffeomorphAt.comp (K := 𝓘(ℝ,ℝ)) (P := ℝ)
          (recip_localDiffeomorphAt (hld t) ⟨chartPDsd q, hsrcLf t ht.le, fun _ _ => rfl⟩
            (hne_lf t ht.le))
          (isLocalDiffeomorphAt_neg (((chartPDsd q) (φ t))⁻¹))
      simpa [inv_neg] using h1
    have htail := tail_data_of_chart (κ := fun y => -(chartPDsd q) y) hsm_rt' hsm_lf'
      (fun t ht => by have := hBneg t ht; linarith)
      (fun t ht => by have := hBpos t ht; linarith)
      hlim_rt' hlim_lf' hinj_rt' hinj_lf' hldR hldL
    have hκld : IsLocalDiffeomorphAt I1 𝓘(ℝ,ℝ) sm (fun y => -(chartPDsd q) y) q :=
      IsLocalDiffeomorphAt.comp (K := 𝓘(ℝ,ℝ)) (P := ℝ)
        (show IsLocalDiffeomorphAt I1 𝓘(ℝ,ℝ) sm (⇑(chartPDsd q)) q from
          ⟨chartPDsd q, chartPD_mem q, fun _ _ => rfl⟩)
        (isLocalDiffeomorphAt_neg ((chartPDsd q) q))
    have hκq : (fun y => -(chartPDsd q) y) q = 0 := by simp [chartPD_apply_self]
    refine ⟨(fun y => -(chartPDsd q) y), T₁ + 1, (fun t => (-((chartPDsd q) (φ t)))⁻¹),
      (fun t => (-((chartPDsd q) (φ t)))⁻¹), hκld, hκq,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht; have := hBneg t (by linarith); linarith
    · intro t ht; have := hBpos t (by linarith); linarith
    · intro t ht; rw [one_div]
    · intro t ht; rw [one_div]
    · exact htail.1
    · exact htail.2.1
    · exact htail.2.2.1
    · exact htail.2.2.2.1
    · exact htail.2.2.2.2.1
    · exact htail.2.2.2.2.2

end

end Work.OneDim
