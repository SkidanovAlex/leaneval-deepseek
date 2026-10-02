import Mathlib
import Submission.Work.ThomBordism.absThomCompare
import Submission.Work.Tubular.contractibleSpace_onePointNonzero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# `A = (Z ∖ 0) ∪ {∞}` is contractible for an arbitrary real bundle

For an arbitrary real bundle `Z : RealBundle B F ι` over a compact Hausdorff base with
finite-dimensional fibre, and a norm-like function `N : NormLike Z` on it, the subspace

`absNZ Z = (Z∖0) ∪ {∞} ⊆ Z⁺`

of the one-point compactification is contractible: the fibrewise radial scaling
`v ↦ (1-t)⁻¹ v` contracts `A` onto the point at infinity.

This is the *metric-free* generalisation of `Work.Tubular.contractibleSpace_onePointNonzero`
(which treats the normal bundle of an embedding, where the fibrewise norm is the ordinary norm):
the only geometric input is the supplied `NormLike` function, whose closed unit ball is compact.

The proof is structured exactly as in the `Work.Tubular` case:

* `scaleMap Z c` is the fibrewise scaling `⟨p.1, c • p.2⟩` (`Work.Thom.continuous_smul_section`);
* `contractFunZ Z t` is `∞` for `t = 1` and the scaling by `(1-t)⁻¹` otherwise;
* it maps `absNZ Z` into itself (`contractFunZ_mem`) and is continuous there — at `t = 1`
  the scaled points leave every compact set because `N.f` is positively homogeneous and
  compact sets are bounded in the fibrewise norm.
-/

open CategoryTheory Limits
open Work.TangentClasses
open scoped Topology unitInterval
open Function Topology Set Filter

namespace Work.ThomBordism

open Work.Cohomology

noncomputable section

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}

/-! ## Two elementary facts about `OnePoint` -/

/-- **Tendsto into a neighbourhood of `some x`**: it suffices to control the underlying point. -/
theorem tendsto_some_coe {X : Type} [TopologicalSpace X] {α : Type} [TopologicalSpace α]
    {l : Filter α} {h : α → X} {x : X} (hh : Tendsto h l (𝓝 x)) :
    Tendsto (fun a => (OnePoint.some (h a) : OnePoint X)) l (𝓝 (OnePoint.some x)) := by
  rw [OnePoint.nhds_coe_eq]
  change Filter.map (fun a => OnePoint.some (h a)) l ≤ Filter.map OnePoint.some (𝓝 x)
  simpa only [Filter.map_map, Function.comp_def] using Filter.map_mono (m := OnePoint.some) hh

/-- **The neighbourhood filter of `(t₀, some w₀)` as the image of the product filter**: every
neighbourhood of `(t₀, some w₀)` contains `V × (some '' W)` for `V ∈ 𝓝 t₀`, `W ∈ 𝓝 w₀`. -/
theorem nhds_pair_some_le {X : Type} [TopologicalSpace X] {Y : Type} [TopologicalSpace Y]
    (t₀ : Y) (w₀ : X) :
    𝓝 (t₀, OnePoint.some w₀) ≤
      map (fun z : Y × X => (z.1, (OnePoint.some z.2 : OnePoint X))) (𝓝 t₀ ×ˢ 𝓝 w₀) := by
  intro s hs
  rw [Filter.mem_map] at hs
  obtain ⟨V, hV, T, hT, hVT⟩ := Filter.mem_prod_iff.mp hs
  rw [nhds_prod_eq, OnePoint.nhds_coe_eq]
  have hT' : OnePoint.some '' T ∈ Filter.map OnePoint.some (𝓝 w₀) := by
    rw [Filter.mem_map, Set.preimage_image_eq _ OnePoint.coe_injective]
    exact hT
  refine Filter.mem_of_superset (Filter.prod_mem_prod hV hT') ?_
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  obtain ⟨w, hw, rfl⟩ := hx
  have hmem : (t, w) ∈ V ×ˢ T := by rw [Set.mem_prod]; exact ⟨ht, hw⟩
  exact hVT hmem

/-! ## Two elementary facts about `unitInterval` -/

/-- A neighbourhood of `t₀ : unitInterval` in the ambient `ℝ` pulls back to a neighbourhood. -/
theorem preimage_coe_mem_nhds (t₀ : unitInterval) {U : Set ℝ} (hU : U ∈ 𝓝 ((t₀ : ℝ))) :
    ((fun t : unitInterval => (t : ℝ)) ⁻¹' U) ∈ 𝓝 t₀ :=
  (continuous_subtype_val (X := ℝ) (p := fun x : ℝ => x ∈ unitInterval)).continuousAt.preimage_mem_nhds hU

theorem one_sub_coe_nonneg (t : unitInterval) : 0 ≤ 1 - (t : ℝ) := by
  have := unitInterval.le_one t; linarith

theorem one_sub_coe_pos {t : unitInterval} (ht : (t : ℝ) ≠ 1) : 0 < 1 - (t : ℝ) := by
  have h : (t : ℝ) < 1 := lt_of_le_of_ne (unitInterval.le_one t) ht
  linarith

/-! ## The fibrewise scaling -/

/-- **The fibrewise scaling** `p ↦ ⟨p.1, c • p.2⟩` of a real bundle. -/
def scaleMap (Z : RealBundle B F ι) (c : ℝ) (p : Z.TotalSpace) : Z.TotalSpace :=
  ⟨p.1, c • p.2⟩

@[simp] theorem scaleMap_one (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    scaleMap Z 1 p = p := by rw [scaleMap, one_smul]

theorem scaleMap_scaleMap (Z : RealBundle B F ι) (c d : ℝ) (p : Z.TotalSpace) :
    scaleMap Z c (scaleMap Z d p) = scaleMap Z (c * d) p := by
  rw [scaleMap, scaleMap, scaleMap, smul_smul]

theorem continuous_scaleMap (Z : RealBundle B F ι) (c : ℝ) :
    Continuous (scaleMap Z c) :=
  Work.Thom.continuous_smul_section Z (ContinuousMap.id _) (ContinuousMap.const _ c)

/-- **The fibrewise scaling is jointly continuous** in the scalar and the point. -/
theorem continuous_scaleMap_prod (Z : RealBundle B F ι) :
    Continuous fun z : ℝ × Z.TotalSpace => scaleMap Z z.1 z.2 :=
  Work.Thom.continuous_smul_section Z ⟨Prod.snd, continuous_snd⟩ ⟨Prod.fst, continuous_fst⟩

/-- **The norm-like function is positively homogeneous**. -/
theorem norm_scaleMap {Z : RealBundle B F ι} (N : NormLike Z) (c : ℝ) (hc : 0 ≤ c)
    (p : Z.TotalSpace) : N.f (scaleMap Z c p) = c * N.f p := N.smul c hc p

/-- Scaling by a nonzero scalar preserves the complement of the zero section. -/
theorem scaleMap_mem_zeroComplement (Z : RealBundle B F ι) (c : ℝ) (hc : c ≠ 0)
    (p : Z.TotalSpace) :
    scaleMap Z c p ∈ Work.Thom.zeroComplement Z ↔ p ∈ Work.Thom.zeroComplement Z := by
  change (c • p.2 : Z.Fiber p.1) ≠ 0 ↔ (p.2 : Z.Fiber p.1) ≠ 0
  constructor
  · intro h hv
    exact h (by rw [hv, smul_zero])
  · intro hv h
    rcases smul_eq_zero.mp h with h1 | h1
    · exact hc h1
    · exact hv h1

/-- **Every compact subset of the total space is bounded in the fibre directions.** -/
theorem exists_le_norm_of_isCompact (Z : RealBundle B F ι) (N : NormLike Z)
    {K : Set Z.TotalSpace} (hK : IsCompact K) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ p ∈ K, N.f p ≤ R := by
  have hb : Bornology.IsBounded (N.f '' K) := (hK.image N.continuous_f).isBounded
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hb
  refine ⟨max r 0, le_max_right _ _, fun p hp => ?_⟩
  have h1 : N.f p ∈ Metric.closedBall (0 : ℝ) r := hr (mem_image_of_mem _ hp)
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
  exact le_trans (le_abs_self _) (le_trans h1 (le_max_left _ _))

/-! ## The contraction map -/

/-- **The contraction of `A = (Z∖0) ∪ {∞}` onto `∞`**: the fibrewise scaling by `(1-t)⁻¹`, with
`t = 1` collapsing everything to `∞` (and the point at infinity fixed). -/
def contractFunZ (Z : RealBundle B F ι) (t : ℝ) (p : OnePoint Z.TotalSpace) :
    OnePoint Z.TotalSpace :=
  if t = 1 then OnePoint.infty else OnePoint.map (scaleMap Z (1 - t)⁻¹) p

@[simp] theorem contractFunZ_one (Z : RealBundle B F ι) (p : OnePoint Z.TotalSpace) :
    contractFunZ Z 1 p = OnePoint.infty := by rw [contractFunZ, if_pos rfl]

@[simp] theorem contractFunZ_zero_some (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    contractFunZ Z 0 (OnePoint.some p) = OnePoint.some p := by
  rw [contractFunZ, if_neg (by norm_num : (0 : ℝ) ≠ 1), sub_zero, inv_one,
    OnePoint.map_some, scaleMap_one]

@[simp] theorem contractFunZ_infty (Z : RealBundle B F ι) (t : ℝ) :
    contractFunZ Z t (OnePoint.infty) = OnePoint.infty := by
  rw [contractFunZ]; split
  · rfl
  · exact OnePoint.map_infty _

@[simp] theorem contractFunZ_zero (Z : RealBundle B F ι) (p : OnePoint Z.TotalSpace) :
    contractFunZ Z 0 p = p := by
  cases p with
  | infty => exact contractFunZ_infty Z 0
  | coe w => exact contractFunZ_zero_some Z w

@[simp] theorem contractFunZ_some (Z : RealBundle B F ι) {t : ℝ} (ht : t ≠ 1)
    (p : Z.TotalSpace) :
    contractFunZ Z t (OnePoint.some p) = OnePoint.some (scaleMap Z (1 - t)⁻¹ p) := by
  rw [contractFunZ, if_neg ht, OnePoint.map_some]

/-- Membership in `A = (Z∖0) ∪ {∞}`, unfolded. -/
theorem mem_absNZ {Z : RealBundle B F ι} {p : OnePoint Z.TotalSpace} :
    p ∈ absNZ Z ↔ p = OnePoint.infty ∨
      ∃ q : Z.TotalSpace, q ∈ Work.Thom.zeroComplement Z ∧ OnePoint.some q = p := by
  constructor
  · intro h
    rcases h with h | h
    · obtain ⟨q, hq, rfl⟩ := h
      exact Or.inr ⟨q, hq, rfl⟩
    · exact Or.inl h
  · rintro (rfl | ⟨q, hq, rfl⟩)
    · exact Or.inr rfl
    · exact Or.inl ⟨q, hq, rfl⟩

/-- **`contractFunZ` maps `A = (Z∖0) ∪ {∞}` into itself.** -/
theorem contractFunZ_mem (Z : RealBundle B F ι) {t : ℝ} {p : OnePoint Z.TotalSpace}
    (hp : p ∈ absNZ Z) : contractFunZ Z t p ∈ absNZ Z := by
  rw [mem_absNZ] at hp ⊢
  rcases hp with rfl | ⟨q, hq, rfl⟩
  · rw [contractFunZ_infty]; exact Or.inl rfl
  · rcases eq_or_ne t 1 with rfl | ht
    · rw [contractFunZ_one]; exact Or.inl rfl
    · refine Or.inr ⟨scaleMap Z (1 - t)⁻¹ q, ?_,
        (contractFunZ_some Z ht q).symm ▸ rfl⟩
      exact (scaleMap_mem_zeroComplement Z _ (inv_ne_zero (sub_ne_zero.mpr (Ne.symm ht))) q).mpr hq

/-! ## Continuity of the contraction at the three kinds of points of `unitInterval × A` -/

/-- **Continuity of the contraction at `(t₀, ∞)`** (ambient statement, `t₀ ∈ unitInterval`).

The proof: a neighbourhood basis of `∞` is given by the complements of the closed compact sets
`L = {p | N.f p ≤ R + 1}`.  For `t ≤ 1` the scaling factor `(1-t)⁻¹` is at least `1`, so a point
`x` with `N.f x > R + 1` is scaled to a point of fibrewise norm `> R`, which is therefore outside
the compact set `K` of fibrewise norm `≤ R`. -/
theorem continuousAt_contractFunZ_infty (Z : RealBundle B F ι) (N : NormLike Z)
    (t₀ : unitInterval) :
    ContinuousAt (fun z : unitInterval × OnePoint Z.TotalSpace => contractFunZ Z (z.1 : ℝ) z.2)
      (t₀, OnePoint.infty) := by
  rw [ContinuousAt, nhds_prod_eq]
  rw [contractFunZ_infty Z (t₀ : ℝ)]
  refine (OnePoint.hasBasis_nhds_infty.tendsto_right_iff).mpr ?_
  rintro K ⟨hKc, hKcomp⟩
  obtain ⟨R, hR0, hR⟩ := exists_le_norm_of_isCompact Z N hKcomp
  set L : Set Z.TotalSpace := {p : Z.TotalSpace | N.f p ≤ R + 1} with hLdef
  have hLc : IsClosed L := isClosed_le N.continuous_f continuous_const
  have hLcomp : IsCompact L := by
    rw [hLdef]
    exact N.isCompact_le (by linarith)
  have hLn : OnePoint.some '' Lᶜ ∪ {OnePoint.infty} ∈ 𝓝 (OnePoint.infty) :=
    OnePoint.hasBasis_nhds_infty.mem_iff.mpr ⟨L, ⟨hLc, hLcomp⟩, subset_rfl⟩
  refine Filter.mem_of_superset (Filter.prod_mem_prod Filter.univ_mem hLn) ?_
  rintro ⟨t, p⟩ ⟨-, hp⟩
  change contractFunZ Z (t : ℝ) p ∈ OnePoint.some '' Kᶜ ∪ {OnePoint.infty}
  rcases hp with ⟨x, hxL, rfl⟩ | rfl
  · rcases eq_or_ne ((t : unitInterval) : ℝ) 1 with ht1 | ht1
    · rw [ht1, contractFunZ_one]; exact Or.inr rfl
    · rw [contractFunZ_some Z ht1]
      refine Or.inl ⟨scaleMap Z (1 - (t : ℝ))⁻¹ x, ?_, rfl⟩
      intro hxK
      have hle : N.f (scaleMap Z (1 - (t : ℝ))⁻¹ x) ≤ R := hR _ hxK
      rw [norm_scaleMap N (1 - (t : ℝ))⁻¹ (inv_nonneg.mpr (one_sub_coe_nonneg t)) x] at hle
      have htpos : 0 < 1 - (t : ℝ) := one_sub_coe_pos ht1
      have htle1 : 1 - (t : ℝ) ≤ 1 := by have := unitInterval.nonneg t; linarith
      have hge1 : 1 ≤ (1 - (t : ℝ))⁻¹ := (one_le_inv₀ htpos).mpr htle1
      have hxgt : R + 1 < N.f x := lt_of_not_ge hxL
      have hxnn : 0 ≤ N.f x := N.nonneg x
      have h1 : N.f x ≤ (1 - (t : ℝ))⁻¹ * N.f x := le_mul_of_one_le_left hxnn hge1
      linarith
  · rw [contractFunZ_infty]; exact Or.inr rfl

/-- **Continuity of the contraction at `(t₀, some w₀)` for `t₀ ≠ 1`** (ambient statement). -/
theorem continuousAt_contractFunZ_some (Z : RealBundle B F ι) {t₀ : unitInterval}
    (ht₀ : (t₀ : ℝ) ≠ 1) (w₀ : Z.TotalSpace) :
    ContinuousAt (fun z : unitInterval × OnePoint Z.TotalSpace => contractFunZ Z (z.1 : ℝ) z.2)
      (t₀, OnePoint.some w₀) := by
  rw [ContinuousAt]
  have hval : contractFunZ Z (t₀ : ℝ) (OnePoint.some w₀) =
      OnePoint.some (scaleMap Z (1 - (t₀ : ℝ))⁻¹ w₀) := contractFunZ_some Z ht₀ w₀
  rw [hval]
  have hjoint : Tendsto (fun z : unitInterval × Z.TotalSpace => scaleMap Z (1 - (z.1 : ℝ))⁻¹ z.2)
      (𝓝 t₀ ×ˢ 𝓝 w₀) (𝓝 (scaleMap Z (1 - (t₀ : ℝ))⁻¹ w₀)) := by
    rw [← nhds_prod_eq]
    have hf : ContinuousAt
        (fun z : unitInterval × Z.TotalSpace => ((1 - (z.1 : ℝ))⁻¹, z.2)) (t₀, w₀) := by
      refine ContinuousAt.prodMk ?_ continuousAt_snd
      have h1 : ContinuousAt (fun z : unitInterval × Z.TotalSpace => (z.1 : ℝ)) (t₀, w₀) :=
        continuous_subtype_val.continuousAt.comp continuous_fst.continuousAt
      exact (continuousAt_const.sub h1).inv₀ (sub_ne_zero.mpr (Ne.symm ht₀))
    exact ((continuous_scaleMap_prod Z).continuousAt).comp hf
  have hcomp : Tendsto (fun z : unitInterval × Z.TotalSpace =>
        contractFunZ Z (z.1 : ℝ) (OnePoint.some z.2))
      (𝓝 t₀ ×ˢ 𝓝 w₀) (𝓝 (OnePoint.some (scaleMap Z (1 - (t₀ : ℝ))⁻¹ w₀))) := by
    have hev : (fun z : unitInterval × Z.TotalSpace =>
          OnePoint.some (scaleMap Z (1 - (z.1 : ℝ))⁻¹ z.2))
        =ᶠ[𝓝 t₀ ×ˢ 𝓝 w₀]
        (fun z : unitInterval × Z.TotalSpace => contractFunZ Z (z.1 : ℝ) (OnePoint.some z.2)) := by
      filter_upwards [Filter.prod_mem_prod
        (preimage_coe_mem_nhds t₀ (isOpen_ne.mem_nhds ht₀)) Filter.univ_mem] with z hz
      rw [contractFunZ_some Z hz.1]
    exact Filter.Tendsto.congr' hev (tendsto_some_coe hjoint)
  have hmap : Tendsto (fun z : unitInterval × OnePoint Z.TotalSpace => contractFunZ Z (z.1 : ℝ) z.2)
      (map (fun z : unitInterval × Z.TotalSpace => (z.1, (OnePoint.some z.2 : OnePoint Z.TotalSpace)))
        (𝓝 t₀ ×ˢ 𝓝 w₀))
      (𝓝 (OnePoint.some (scaleMap Z (1 - (t₀ : ℝ))⁻¹ w₀))) := by
    change Filter.map (fun z : unitInterval × OnePoint Z.TotalSpace => contractFunZ Z (z.1 : ℝ) z.2)
      (Filter.map (fun z : unitInterval × Z.TotalSpace => (z.1, OnePoint.some z.2))
        (𝓝 t₀ ×ˢ 𝓝 w₀)) ≤
      𝓝 (OnePoint.some (scaleMap Z (1 - (t₀ : ℝ))⁻¹ w₀))
    rw [Filter.map_map]
    exact hcomp
  exact Filter.Tendsto.mono_left hmap (nhds_pair_some_le t₀ w₀)

/-- **Continuity of the contraction at `(1, some w₀)` with `w₀ ≠ 0`**: the point
`w₀/(1-t)` leaves every compact set as `t → 1`, uniformly in a neighbourhood of `w₀`. -/
theorem continuousAt_contractFunZ_one (Z : RealBundle B F ι) (N : NormLike Z) (t₀ : unitInterval)
    (ht₀ : (t₀ : ℝ) = 1) {w₀ : Z.TotalSpace} (hw₀ : w₀ ∈ Work.Thom.zeroComplement Z) :
    ContinuousAt (fun z : unitInterval × OnePoint Z.TotalSpace => contractFunZ Z (z.1 : ℝ) z.2)
      (t₀, OnePoint.some w₀) := by
  have hw₀ne : N.f w₀ ≠ 0 := fun h => hw₀ ((N.eq_zero w₀).mp h)
  have hw₀pos : 0 < N.f w₀ := lt_of_le_of_ne (N.nonneg w₀) (Ne.symm hw₀ne)
  set η : ℝ := N.f w₀ / 2 with hηdef
  have hηpos : 0 < η := by rw [hηdef]; linarith
  rw [ContinuousAt]
  rw [ht₀, contractFunZ_one]
  have hcomp : Tendsto (fun z : unitInterval × Z.TotalSpace =>
        contractFunZ Z (z.1 : ℝ) (OnePoint.some z.2))
      (𝓝 t₀ ×ˢ 𝓝 w₀) (𝓝 OnePoint.infty) := by
    refine (OnePoint.hasBasis_nhds_infty.tendsto_right_iff).mpr ?_
    rintro K ⟨hKc, hKcomp⟩
    obtain ⟨R, hR0, hR⟩ := exists_le_norm_of_isCompact Z N hKcomp
    set δd : ℝ := η / (R + 1) with hδddef
    have hR1 : 0 < R + 1 := by linarith
    have hδdpos : 0 < δd := by rw [hδddef]; positivity
    have hW : {w : Z.TotalSpace | η < N.f w} ∈ 𝓝 w₀ := by
      refine (isOpen_lt continuous_const N.continuous_f).mem_nhds ?_
      show η < N.f w₀
      rw [hηdef]; linarith
    have hI : ((fun t : unitInterval => (t : ℝ)) ⁻¹' Ioo (1 - δd) (1 + δd)) ∈ 𝓝 t₀ := by
      refine preimage_coe_mem_nhds t₀ (isOpen_Ioo.mem_nhds ?_)
      rw [ht₀, Set.mem_Ioo]
      constructor <;> linarith
    refine Filter.mem_of_superset (Filter.prod_mem_prod hI hW) ?_
    rintro ⟨t, w⟩ ⟨ht, hw⟩
    change contractFunZ Z (t : ℝ) (OnePoint.some w) ∈
      OnePoint.some '' Kᶜ ∪ {OnePoint.infty}
    simp only [Set.mem_preimage, Set.mem_Ioo] at ht
    rcases eq_or_ne ((t : unitInterval) : ℝ) 1 with ht1 | ht1
    · rw [ht1, contractFunZ_one]; exact Or.inr rfl
    · rw [contractFunZ_some Z ht1]
      refine Or.inl ⟨scaleMap Z (1 - (t : ℝ))⁻¹ w, ?_, rfl⟩
      intro hwK
      have hle : N.f (scaleMap Z (1 - (t : ℝ))⁻¹ w) ≤ R := hR _ hwK
      rw [norm_scaleMap N (1 - (t : ℝ))⁻¹ (inv_nonneg.mpr (one_sub_coe_nonneg t)) w] at hle
      have htpos : 0 < 1 - (t : ℝ) := one_sub_coe_pos ht1
      have hlt : 1 - (t : ℝ) < δd := by linarith [ht.1]
      have hltinv : δd⁻¹ < (1 - (t : ℝ))⁻¹ := inv_strictAnti₀ htpos hlt
      have hδinv : δd⁻¹ = (R + 1) / η := by rw [hδddef, inv_div]
      have h1 : (1 - (t : ℝ))⁻¹ < R / η := by
        rw [lt_div_iff₀ hηpos]
        exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hw (inv_pos.mpr htpos)) hle
      have h2 : R / η < δd⁻¹ := by
        rw [hδinv]
        exact div_lt_div_of_pos_right (by linarith) hηpos
      linarith
  have hmap : Tendsto (fun z : unitInterval × OnePoint Z.TotalSpace => contractFunZ Z (z.1 : ℝ) z.2)
      (map (fun z : unitInterval × Z.TotalSpace => (z.1, (OnePoint.some z.2 : OnePoint Z.TotalSpace)))
        (𝓝 t₀ ×ˢ 𝓝 w₀))
      (𝓝 OnePoint.infty) := by
    change Filter.map (fun z : unitInterval × OnePoint Z.TotalSpace => contractFunZ Z (z.1 : ℝ) z.2)
      (Filter.map (fun z : unitInterval × Z.TotalSpace => (z.1, OnePoint.some z.2))
        (𝓝 t₀ ×ˢ 𝓝 w₀)) ≤ 𝓝 OnePoint.infty
    rw [Filter.map_map]
    exact hcomp
  exact Filter.Tendsto.mono_left hmap (nhds_pair_some_le t₀ w₀)

/-! ## The contraction as a map of `A`, and the contractibility -/

/-- The contraction is continuous on `unitInterval × A`: outside `t = 1` it is the (jointly
continuous) fibrewise scaling, and at `t = 1` the points leave every compact set. -/
theorem continuous_contractFunZ_abs (Z : RealBundle B F ι) (N : NormLike Z) :
    Continuous (fun z : unitInterval × ↥(absNZ Z) => contractFunZ Z (z.1 : ℝ) z.2.1) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, p₀⟩
  have hkey : ContinuousAt
      (fun z : unitInterval × OnePoint Z.TotalSpace => contractFunZ Z (z.1 : ℝ) z.2)
      (t₀, p₀.1) := by
    rcases mem_absNZ.mp p₀.2 with hinf | ⟨w₀, hw₀, hsome⟩
    · rw [hinf]
      exact continuousAt_contractFunZ_infty Z N t₀
    · rw [← hsome]
      rcases eq_or_ne ((t₀ : ℝ)) 1 with h1 | h1
      · exact continuousAt_contractFunZ_one Z N t₀ h1 hw₀
      · exact continuousAt_contractFunZ_some Z h1 w₀
  have hf : ContinuousAt (fun z : unitInterval × ↥(absNZ Z) =>
      ((z.1 : unitInterval), (z.2.1 : OnePoint Z.TotalSpace))) (t₀, p₀) :=
    ContinuousAt.prodMk continuous_fst.continuousAt
      ((continuous_subtype_val (X := OnePoint Z.TotalSpace)
        (p := fun x : OnePoint Z.TotalSpace => x ∈ absNZ Z)).continuousAt.comp
        continuous_snd.continuousAt)
  exact ContinuousAt.comp (g := fun z : unitInterval × OnePoint Z.TotalSpace =>
      contractFunZ Z (z.1 : ℝ) z.2)
    (f := fun z : unitInterval × ↥(absNZ Z) =>
      ((z.1 : unitInterval), (z.2.1 : OnePoint Z.TotalSpace))) hkey hf

/-- The contraction, as a continuous map `unitInterval × A → A`. -/
noncomputable def contractMapZ (Z : RealBundle B F ι) (N : NormLike Z) :
    C(unitInterval × ↥(absNZ Z), ↥(absNZ Z)) where
  toFun z := ⟨contractFunZ Z (z.1 : ℝ) z.2.1, contractFunZ_mem Z z.2.2⟩
  continuous_toFun := (continuous_contractFunZ_abs Z N).subtype_mk (fun z => contractFunZ_mem Z z.2.2)

@[simp] theorem contractMapZ_apply (Z : RealBundle B F ι) (N : NormLike Z)
    (z : unitInterval × ↥(absNZ Z)) :
    (contractMapZ Z N z : OnePoint Z.TotalSpace) = contractFunZ Z (z.1 : ℝ) z.2.1 := rfl

/-- **`A = (Z ∖ 0) ∪ {∞}` is contractible**: the scaling `w ↦ w/(1-t)` contracts the complement
of the zero section in `Z⁺` onto the point at infinity. -/
theorem contractibleSpace_absNZ (Z : RealBundle B F ι) (N : NormLike Z) :
    ContractibleSpace ↥(absNZ Z) := by
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨⟨OnePoint.infty, infty_mem_absNZ Z⟩, ?_⟩
  refine ⟨{ toContinuousMap := contractMapZ Z N
            map_zero_left := ?_
            map_one_left := ?_ }⟩
  · intro x
    apply Subtype.ext
    change contractFunZ Z ((0 : unitInterval) : ℝ) x.1 = x.1
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl]
    exact contractFunZ_zero Z x.1
  · intro x
    apply Subtype.ext
    change contractFunZ Z ((1 : unitInterval) : ℝ) x.1 = OnePoint.infty
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
    exact contractFunZ_one Z x.1

theorem absContractible {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (N : Work.ThomBordism.NormLike Z) :
    ContractibleSpace ↥(Work.ThomBordism.absNZ Z) :=
  contractibleSpace_absNZ Z N

end

end Work.ThomBordism
