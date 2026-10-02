import Mathlib
import Submission.Work.ThomBordism.isCompact_fibreNorm_le
import Submission.Work.Thom.Continuous

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-!
# `A = (E ∖ 0) ∪ {∞}` is contractible for a real bundle `E → B` over a compact base

Let `Z` be a real vector bundle (in the gluing-data model `Work.TangentClasses.RealBundle`) over a
compact Hausdorff base `B`, with finite-dimensional model fibre `F`, and assume that the fibrewise
norm `Work.Thom.fibreNorm Z : Z.TotalSpace → ℝ` is **continuous** (this is the only geometric
input; it holds for a Euclidean bundle).  The set

`A = OnePoint.some '' Z.zeroComplement ∪ {OnePoint.infty} ⊆ Z⁺`

— the complement of the zero section in the one-point compactification `Z⁺` of the total space,
i.e. the "absolute" model of the Thom space — is **contractible**.

The contraction is the radial scaling `w ↦ w/(1-t)` of the fibres, which pushes everything to the
point at infinity: in the radial coordinate `E ∖ 0 ≅ S(E) × (0,∞)`, the point `∞` is the apex of the
cone on the sphere bundle.  The only point where continuity is not formal is `(t,w) = (1,w₀)` with
`w₀ ≠ 0`: there `w₀/(1-t)` leaves every compact set as `t → 1`, which is where the *properness* of
the fibrewise norm enters, in the form `Work.ThomBordism.isCompact_fibreNorm_le`.

This is the metric-freeness statement behind `Work.ThomBordism.Theta`/`Phi` (see
`Submission/Work/ThomBordism/absThomCompare.lean`); the same argument for the normal bundle of an
embedding is `Work.Tubular.contractibleSpace_onePointNonzero`.

## Main result

`Work.ThomBordism.contractibleZeroComplement`
-/

namespace Work.ThomBordism

open Work.TangentClasses
open scoped Topology unitInterval
open Function Topology Set Filter

noncomputable section

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}

/-! ## Elementary facts about the fibrewise scaling -/

/-- The fibrewise scaling `w ↦ c • w` of the total space of a real bundle. -/
private def scaleMap (Z : RealBundle B F ι) (c : ℝ) (p : Z.TotalSpace) : Z.TotalSpace :=
  ⟨p.1, c • p.2⟩

/-- Scaling by `1` is the identity. -/
private theorem scaleMap_one (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    scaleMap Z 1 p = p := by
  simp only [scaleMap, one_smul]

/-- **The fibrewise norm under scaling**, with the absolute value of the scalar. -/
private theorem fibreNorm_scaleMap (Z : RealBundle B F ι) (c : ℝ) (p : Z.TotalSpace) :
    Work.Thom.fibreNorm Z (scaleMap Z c p) = |c| * Work.Thom.fibreNorm Z p := by
  show ‖c • (show F from p.2)‖ = |c| * ‖(show F from p.2)‖
  rw [norm_smul, Real.norm_eq_abs]

/-- The fibrewise norm is non-negative. -/
private theorem fibreNorm_nonneg (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    0 ≤ Work.Thom.fibreNorm Z p := norm_nonneg _

private theorem continuousAt_localTrivAt_snd_gen {X : Type*} [TopologicalSpace X]
    (Z : RealBundle B F ι) (sec : C(X, Z.TotalSpace)) (x₀ : X) :
    ContinuousAt (fun x => ((Z.localTrivAt (sec x₀).1) (sec x)).2) x₀ := by
  have h := ((FiberBundle.continuousAt_totalSpace F sec (x₀ := x₀)).1
    sec.continuous.continuousAt).2
  simpa only [VectorBundleCore.trivializationAt, VectorBundleCore.proj] using h

/-- Fibrewise rescaling of a continuous map into the total space, for a *general* test space (the
version `Work.Thom.continuous_smul_section` restricts the test space to the smallest universe, so
it cannot be applied to `ℝ × Z.TotalSpace`). -/
private theorem continuous_smul_section_gen {X : Type*} [TopologicalSpace X]
    (Z : RealBundle B F ι) (sec : C(X, Z.TotalSpace)) (c : C(X, ℝ)) :
    Continuous (fun x => (⟨(sec x).1, c x • (sec x).2⟩ : Z.TotalSpace)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  set i := Z.indexAt (sec x₀).1 with hi
  have hx0 : (sec x₀).1 ∈ Z.baseSet i := by rw [hi]; exact Z.mem_baseSet_at (sec x₀).1
  have hsec : ContinuousAt (fun x => ((Z.localTriv i) (sec x)).2) x₀ :=
    continuousAt_localTrivAt_snd_gen Z sec x₀
  have hpair : ContinuousAt (fun x => ((sec x).1, c x • ((Z.localTriv i) (sec x)).2)) x₀ :=
    (Z.continuous_proj.continuousAt.comp sec.continuous.continuousAt).prodMk
      (c.continuous.continuousAt.smul hsec)
  have heq : (fun x => (Z.localTriv i) (⟨(sec x).1, c x • (sec x).2⟩ : Z.TotalSpace)) =
      fun x => ((sec x).1, c x • ((Z.localTriv i) (sec x)).2) := by
    funext x
    rw [VectorBundleCore.localTriv_apply, ContinuousLinearMap.map_smul,
      VectorBundleCore.localTriv_apply]
  refine (Z.localTriv i).continuousAt_of_comp_left ?_ hx0 ?_
  · show ContinuousAt (fun x => Z.proj (⟨(sec x).1, c x • (sec x).2⟩ : Z.TotalSpace)) x₀
    rw [show (fun x => Z.proj (⟨(sec x).1, c x • (sec x).2⟩ : Z.TotalSpace)) = fun x => (sec x).1
      from by funext x; rfl]
    exact Z.continuous_proj.continuousAt.comp sec.continuous.continuousAt
  · show ContinuousAt (fun x => (Z.localTriv i) (⟨(sec x).1, c x • (sec x).2⟩ : Z.TotalSpace)) x₀
    rw [heq]
    exact hpair

/-- **The fibrewise scaling is jointly continuous** in the scalar and the point. -/
private theorem continuous_scaleMap_prod (Z : RealBundle B F ι) :
    Continuous fun z : ℝ × Z.TotalSpace => scaleMap Z z.1 z.2 := by
  exact continuous_smul_section_gen Z
    (⟨fun z : ℝ × Z.TotalSpace => z.2, continuous_snd⟩ : C(ℝ × Z.TotalSpace, Z.TotalSpace))
    (⟨fun z : ℝ × Z.TotalSpace => z.1, continuous_fst⟩ : C(ℝ × Z.TotalSpace, ℝ))

/-- **Every compact subset of the total space is bounded in the fibre directions.** -/
private theorem exists_le_fibreNorm_of_isCompact (Z : RealBundle B F ι)
    (hcont : Continuous (Work.Thom.fibreNorm Z)) {K : Set Z.TotalSpace} (hK : IsCompact K) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ p ∈ K, Work.Thom.fibreNorm Z p ≤ R := by
  have hb : Bornology.IsBounded (Work.Thom.fibreNorm Z '' K) := (hK.image hcont).isBounded
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hb
  refine ⟨max r 0, le_max_right _ _, fun p hp => ?_⟩
  have h1 : Work.Thom.fibreNorm Z p ∈ Metric.closedBall (0 : ℝ) r := hr (mem_image_of_mem _ hp)
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
  exact le_trans (le_abs_self _) (le_trans h1 (le_max_left _ _))

/-! ## The complement of the zero section in `Z⁺` -/

/-- **The complement of the zero section in `Z⁺`**: `A = (Z∖0) ∪ {∞}`, the subspace whose
contractibility makes the forgetful map `relToAbs` invertible.  (`Work.ThomBordism.absNZ` in
`absThomCompare.lean` is the same set; this copy is private to keep the two developments
independent.) -/
private abbrev absNZ (Z : RealBundle B F ι) : Set (OnePoint Z.TotalSpace) :=
  OnePoint.some '' Work.Thom.zeroComplement Z ∪ {OnePoint.infty}

/-- The membership description of `A = (Z∖0) ∪ {∞}`. -/
private theorem mem_absNZ {Z : RealBundle B F ι} {p : OnePoint Z.TotalSpace} :
    p ∈ absNZ Z ↔ p = OnePoint.infty ∨
      ∃ w : Z.TotalSpace, w ∈ Work.Thom.zeroComplement Z ∧ p = OnePoint.some w := by
  rw [absNZ, Set.mem_union, Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro (⟨w, hw, hw'⟩ | h)
    · exact Or.inr ⟨w, hw, hw'.symm⟩
    · exact Or.inl h
  · rintro (h | ⟨w, hw, hw'⟩)
    · exact Or.inr h
    · exact Or.inl ⟨w, hw, hw'.symm⟩

/-! ## The neighbourhoods of the points of `A` inside `Z⁺`

These three lemmas are pure `OnePoint` topology (they hold for an arbitrary topological space). -/

/-- **Tendsto into a neighbourhood of `some x`**: it suffices to control the underlying point. -/
private theorem tendsto_some_coe {X : Type} [TopologicalSpace X] {α : Type*} [TopologicalSpace α]
    {l : Filter α} {h : α → X} {x : X} (hh : Tendsto h l (𝓝 x)) :
    Tendsto (fun a => (OnePoint.some (h a) : OnePoint X)) l (𝓝 (OnePoint.some x)) := by
  rw [OnePoint.nhds_coe_eq]
  change Filter.map (fun a => OnePoint.some (h a)) l ≤ Filter.map OnePoint.some (𝓝 x)
  simpa only [Filter.map_map, Function.comp_def] using Filter.map_mono (m := OnePoint.some) hh

/-- **The neighbourhood filter of `(t₀, some x₀)` as the image of the product filter**: every
neighbourhood of `(t₀, some x₀)` contains `V × (some '' W)` for `V ∈ 𝓝 t₀`, `W ∈ 𝓝 x₀`. -/
private theorem nhds_pair_coe_le {X : Type} [TopologicalSpace X] (t₀ : ℝ) (x₀ : X) :
    𝓝 (t₀, OnePoint.some x₀) ≤
      map (fun z : ℝ × X => (z.1, OnePoint.some z.2)) (𝓝 t₀ ×ˢ 𝓝 x₀) := by
  intro s hs
  rw [Filter.mem_map] at hs
  obtain ⟨V, hV, T, hT, hVT⟩ := Filter.mem_prod_iff.mp hs
  rw [nhds_prod_eq, OnePoint.nhds_coe_eq]
  have hT' : OnePoint.some '' T ∈ Filter.map OnePoint.some (𝓝 x₀) := by
    rw [Filter.mem_map, Set.preimage_image_eq _ OnePoint.coe_injective]
    exact hT
  refine Filter.mem_of_superset (Filter.prod_mem_prod hV hT') ?_
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  obtain ⟨w, hw, rfl⟩ := hx
  have hmem : (t, w) ∈ V ×ˢ T := ⟨ht, hw⟩
  exact hVT hmem

/-! ## The contraction map -/

/-- **The contraction of `Z⁺ ∖ 0` onto `∞`**: the fibrewise scaling by `(1-t)⁻¹`, with `t = 1`
collapsing everything to `∞` (and the point at infinity fixed). -/
private def contractFun (Z : RealBundle B F ι) (t : ℝ) (p : OnePoint Z.TotalSpace) :
    OnePoint Z.TotalSpace :=
  if t = 1 then OnePoint.infty else OnePoint.map (scaleMap Z (1 - t)⁻¹) p

@[simp] private theorem contractFun_one (Z : RealBundle B F ι) (p : OnePoint Z.TotalSpace) :
    contractFun Z 1 p = OnePoint.infty := by
  rw [contractFun, if_pos rfl]

@[simp] private theorem contractFun_zero_some (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    contractFun Z 0 (OnePoint.some p) = OnePoint.some p := by
  rw [contractFun, if_neg (by norm_num : (0 : ℝ) ≠ 1), sub_zero, inv_one, OnePoint.map_some,
    scaleMap_one]

@[simp] private theorem contractFun_infty (Z : RealBundle B F ι) (t : ℝ) :
    contractFun Z t (OnePoint.infty) = OnePoint.infty := by
  rw [contractFun]
  split
  · rfl
  · exact OnePoint.map_infty _

@[simp] private theorem contractFun_zero (Z : RealBundle B F ι) (p : OnePoint Z.TotalSpace) :
    contractFun Z 0 p = p := by
  cases p with
  | infty => exact contractFun_infty Z 0
  | coe w => exact contractFun_zero_some Z w

@[simp] private theorem contractFun_some (Z : RealBundle B F ι) {t : ℝ} (ht : t ≠ 1)
    (p : Z.TotalSpace) :
    contractFun Z t (OnePoint.some p) = OnePoint.some (scaleMap Z (1 - t)⁻¹ p) := by
  rw [contractFun, if_neg ht, OnePoint.map_some]

/-- **`contractFun` maps `A = (Z∖0) ∪ {∞}` into itself.** -/
private theorem contractFun_mem (Z : RealBundle B F ι) {t : ℝ} {p : OnePoint Z.TotalSpace}
    (hp : p ∈ absNZ Z) : contractFun Z t p ∈ absNZ Z := by
  rw [mem_absNZ] at hp ⊢
  rcases hp with rfl | ⟨w, hw, rfl⟩
  · rw [contractFun_infty]; exact Or.inl rfl
  · rcases eq_or_ne t 1 with rfl | ht
    · rw [contractFun_one]; exact Or.inl rfl
    · refine Or.inr ⟨scaleMap Z (1 - t)⁻¹ w, ?_, (contractFun_some Z ht w).symm ▸ rfl⟩
      rw [Work.Thom.mem_zeroComplement] at hw ⊢
      show (1 - t)⁻¹ • (show F from w.2) ≠ 0
      exact smul_ne_zero (inv_ne_zero (sub_ne_zero.mpr (Ne.symm ht))) hw

/-! ## Joint continuity of the contraction, at the three kinds of points of `[0,1] × A` -/

/-- **Continuity of the contraction at `(t₀, ∞)`** (for `t₀ ≤ 1`). -/
private theorem continuousAt_contractFun_infty (Z : RealBundle B F ι)
    (hcont : Continuous (Work.Thom.fibreNorm Z)) {t₀ : ℝ} (ht₀ : t₀ ≤ 1) :
    ContinuousAt (fun z : ℝ × OnePoint Z.TotalSpace => contractFun Z z.1 z.2)
      (t₀, OnePoint.infty) := by
  rw [ContinuousAt]
  have hval : contractFun Z ((t₀, OnePoint.infty) : ℝ × OnePoint Z.TotalSpace).1
      ((t₀, OnePoint.infty) : ℝ × OnePoint Z.TotalSpace).2 = OnePoint.infty :=
    contractFun_infty Z t₀
  rw [hval, nhds_prod_eq]
  refine (OnePoint.hasBasis_nhds_infty.tendsto_right_iff).mpr ?_
  rintro K ⟨hKc, hKcomp⟩
  obtain ⟨R, hR0, hR⟩ := exists_le_fibreNorm_of_isCompact Z hcont hKcomp
  set τ : ℝ := |1 - t₀| + 1 with hτdef
  have hτpos : 0 < τ := by positivity
  set L : Set Z.TotalSpace := {p : Z.TotalSpace | Work.Thom.fibreNorm Z p ≤ (R + 1) * τ}
    with hLdef
  have hLc : IsClosed L := isClosed_le hcont continuous_const
  have hLcomp : IsCompact L := by
    rw [hLdef]
    exact isCompact_fibreNorm_le Z hcont ((R + 1) * τ)
  have hLn : OnePoint.some '' Lᶜ ∪ {OnePoint.infty} ∈ 𝓝 (OnePoint.infty) :=
    OnePoint.hasBasis_nhds_infty.mem_iff.mpr ⟨L, ⟨hLc, hLcomp⟩, subset_rfl⟩
  rw [Filter.eventually_iff]
  refine Filter.mem_of_superset (Filter.prod_mem_prod
    (Ioo_mem_nhds (a := t₀ - 1) (b := t₀ + 1) (by linarith [abs_nonneg (1 - t₀)])
      (by linarith [abs_nonneg (1 - t₀)])) hLn) ?_
  rintro ⟨t, p⟩ ⟨ht, hp⟩
  rw [Set.mem_Ioo] at ht
  have ht1 : |1 - t| ≤ τ := by
    rw [abs_le]
    constructor
    · have h1 : t - 1 < t₀ := by linarith [ht.2]
      have h2 : t₀ ≤ τ := by rw [hτdef]; linarith [abs_nonneg (1 - t₀), ht₀]
      linarith
    · have h1 : 1 - t < 2 - t₀ := by linarith [ht.1]
      have h2 : (2 : ℝ) - t₀ ≤ τ := by rw [hτdef]; linarith [le_abs_self (1 - t₀)]
      linarith
  rcases hp with ⟨x, hxL, rfl⟩ | rfl
  · rcases eq_or_ne t 1 with rfl | htne
    · change contractFun Z 1 (OnePoint.some x) ∈ OnePoint.some '' Kᶜ ∪ {OnePoint.infty}
      rw [contractFun_one]; exact Or.inr rfl
    · change contractFun Z t (OnePoint.some x) ∈ OnePoint.some '' Kᶜ ∪ {OnePoint.infty}
      rw [contractFun_some Z htne]
      refine Or.inl ⟨scaleMap Z (1 - t)⁻¹ x, ?_, rfl⟩
      intro hxK
      have h1 : Work.Thom.fibreNorm Z (scaleMap Z (1 - t)⁻¹ x) ≤ R := hR _ hxK
      rw [fibreNorm_scaleMap] at h1
      have h2 : (R + 1) * τ < Work.Thom.fibreNorm Z x := lt_of_not_ge hxL
      have h3 : 1 / τ ≤ |(1 - t)⁻¹| := by
        have habs : |1 - t| ≤ τ := ht1
        have hpos : 0 < |1 - t| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm htne))
        rw [abs_inv, inv_eq_one_div]
        exact one_div_le_one_div_of_le hpos habs
      have h4 : R + 1 < |(1 - t)⁻¹| * Work.Thom.fibreNorm Z x := by
        calc R + 1 = (1 / τ) * ((R + 1) * τ) := by field_simp
          _ < (1 / τ) * Work.Thom.fibreNorm Z x := mul_lt_mul_of_pos_left h2 (by positivity)
          _ ≤ |(1 - t)⁻¹| * Work.Thom.fibreNorm Z x :=
              mul_le_mul_of_nonneg_right h3 (fibreNorm_nonneg Z x)
      linarith
  · change contractFun Z t (OnePoint.infty : OnePoint Z.TotalSpace) ∈
      OnePoint.some '' Kᶜ ∪ {OnePoint.infty}
    rw [contractFun_infty]; exact Or.inr rfl

/-- **Continuity of the contraction at `(t₀, some w₀)` for `t₀ ≠ 1`** (no hypothesis on `w₀`). -/
private theorem continuousAt_contractFun_some (Z : RealBundle B F ι) {t₀ : ℝ} (ht₀ne : t₀ ≠ 1)
    (w₀ : Z.TotalSpace) :
    ContinuousAt (fun z : ℝ × OnePoint Z.TotalSpace => contractFun Z z.1 z.2)
      (t₀, OnePoint.some w₀) := by
  rw [ContinuousAt]
  have hval : contractFun Z (t₀, OnePoint.some w₀).1 (t₀, OnePoint.some w₀).2
      = OnePoint.some (scaleMap Z (1 - t₀)⁻¹ w₀) := contractFun_some Z ht₀ne w₀
  rw [hval]
  have hjoint : Tendsto (fun z : ℝ × Z.TotalSpace => scaleMap Z (1 - z.1)⁻¹ z.2)
      (𝓝 t₀ ×ˢ 𝓝 w₀) (𝓝 (scaleMap Z (1 - t₀)⁻¹ w₀)) := by
    rw [← nhds_prod_eq]
    refine ContinuousAt.comp (g := fun z : ℝ × Z.TotalSpace => scaleMap Z z.1 z.2)
      (f := fun z : ℝ × Z.TotalSpace => ((1 - z.1)⁻¹, z.2))
      (continuous_scaleMap_prod Z).continuousAt ?_
    refine ContinuousAt.prodMk ?_ continuousAt_snd
    exact (continuousAt_const.sub continuousAt_fst).inv₀ (sub_ne_zero.mpr (Ne.symm ht₀ne))
  have hcomp : Tendsto (fun z : ℝ × Z.TotalSpace => contractFun Z z.1 (OnePoint.some z.2))
      (𝓝 t₀ ×ˢ 𝓝 w₀) (𝓝 (OnePoint.some (scaleMap Z (1 - t₀)⁻¹ w₀))) := by
    have hev : (fun z : ℝ × Z.TotalSpace => OnePoint.some (scaleMap Z (1 - z.1)⁻¹ z.2))
        =ᶠ[𝓝 t₀ ×ˢ 𝓝 w₀]
        (fun z : ℝ × Z.TotalSpace => contractFun Z z.1 (OnePoint.some z.2)) := by
      filter_upwards [Filter.prod_mem_prod (isOpen_ne.mem_nhds ht₀ne) Filter.univ_mem] with z hz
      rw [contractFun_some Z hz.1]
    exact Filter.Tendsto.congr' hev (tendsto_some_coe hjoint)
  have hmap : Tendsto (fun z : ℝ × OnePoint Z.TotalSpace => contractFun Z z.1 z.2)
      (map (fun z : ℝ × Z.TotalSpace => (z.1, OnePoint.some z.2)) (𝓝 t₀ ×ˢ 𝓝 w₀))
      (𝓝 (OnePoint.some (scaleMap Z (1 - t₀)⁻¹ w₀))) := by
    change Filter.map (fun z : ℝ × OnePoint Z.TotalSpace => contractFun Z z.1 z.2)
      (Filter.map (fun z : ℝ × Z.TotalSpace => (z.1, OnePoint.some z.2)) (𝓝 t₀ ×ˢ 𝓝 w₀)) ≤
      𝓝 (OnePoint.some (scaleMap Z (1 - t₀)⁻¹ w₀))
    rw [Filter.map_map]
    exact hcomp
  exact Filter.Tendsto.mono_left hmap (nhds_pair_coe_le t₀ w₀)

/-- **Continuity of the contraction at `(1, some w₀)` with `w₀ ∈ Z∖0`**: the point `w₀/(1-t)`
leaves every compact set as `t → 1`, uniformly in a neighbourhood of `w₀`. -/
private theorem continuousAt_contractFun_one (Z : RealBundle B F ι)
    (hcont : Continuous (Work.Thom.fibreNorm Z)) {w₀ : Z.TotalSpace}
    (hw₀ : w₀ ∈ Work.Thom.zeroComplement Z) :
    ContinuousAt (fun z : ℝ × OnePoint Z.TotalSpace => contractFun Z z.1 z.2)
      (1, OnePoint.some w₀) := by
  have hw₀pos : 0 < Work.Thom.fibreNorm Z w₀ := by
    rw [Work.Thom.mem_zeroComplement] at hw₀
    exact norm_pos_iff.mpr hw₀
  set η : ℝ := Work.Thom.fibreNorm Z w₀ / 2 with hηdef
  have hηpos : 0 < η := by rw [hηdef]; linarith
  rw [ContinuousAt]
  have hval : contractFun Z ((1 : ℝ), OnePoint.some w₀).1 ((1 : ℝ), OnePoint.some w₀).2
      = OnePoint.infty := contractFun_one Z _
  rw [hval]
  have hcomp : Tendsto (fun z : ℝ × Z.TotalSpace => contractFun Z z.1 (OnePoint.some z.2))
      (𝓝 (1 : ℝ) ×ˢ 𝓝 w₀) (𝓝 OnePoint.infty) := by
    refine (OnePoint.hasBasis_nhds_infty.tendsto_right_iff).mpr ?_
    rintro K ⟨hKc, hKcomp⟩
    obtain ⟨R, hR0, hR⟩ := exists_le_fibreNorm_of_isCompact Z hcont hKcomp
    set δd : ℝ := η / (R + 1) with hδddef
    have hδdpos : 0 < δd := by rw [hδddef]; positivity
    have hW : {w : Z.TotalSpace | η < Work.Thom.fibreNorm Z w} ∈ 𝓝 w₀ :=
      (isOpen_lt continuous_const hcont).mem_nhds
        (by show η < Work.Thom.fibreNorm Z w₀; rw [hηdef]; linarith)
    rw [Filter.eventually_iff]
    refine Filter.mem_of_superset (Filter.prod_mem_prod
      (Ioo_mem_nhds (a := 1 - δd) (b := 1 + δd) (by linarith) (by linarith)) hW) ?_
    rintro ⟨t, w⟩ ⟨ht, hw⟩
    rw [Set.mem_Ioo] at ht
    rcases eq_or_ne t 1 with rfl | htne
    · change contractFun Z 1 (OnePoint.some w) ∈ OnePoint.some '' Kᶜ ∪ {OnePoint.infty}
      rw [contractFun_one]; exact Or.inr rfl
    · change contractFun Z t (OnePoint.some w) ∈ OnePoint.some '' Kᶜ ∪ {OnePoint.infty}
      rw [contractFun_some Z htne]
      refine Or.inl ⟨scaleMap Z (1 - t)⁻¹ w, ?_, rfl⟩
      intro hwK
      have h1 : Work.Thom.fibreNorm Z (scaleMap Z (1 - t)⁻¹ w) ≤ R := hR _ hwK
      rw [fibreNorm_scaleMap] at h1
      have habs : |1 - t| < δd := by
        rw [abs_lt]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have h2 : 1 / δd < |(1 - t)⁻¹| := by
        have hpos : 0 < |1 - t| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm htne))
        rw [abs_inv, inv_eq_one_div]
        exact one_div_lt_one_div_of_lt hpos habs
      have h3 : 1 / δd = (R + 1) / η := by rw [hδddef, one_div_div]
      have h4 : (R + 1) / η < |(1 - t)⁻¹| := by rw [← h3]; exact h2
      have h5 : R < |(1 - t)⁻¹| * Work.Thom.fibreNorm Z w := by
        calc R < R + 1 := by linarith
          _ = ((R + 1) / η) * η := by field_simp
          _ < |(1 - t)⁻¹| * Work.Thom.fibreNorm Z w :=
              mul_lt_mul h4 (le_of_lt hw) hηpos (by positivity)
      linarith
  have hmap : Tendsto (fun z : ℝ × OnePoint Z.TotalSpace => contractFun Z z.1 z.2)
      (map (fun z : ℝ × Z.TotalSpace => (z.1, OnePoint.some z.2)) (𝓝 (1 : ℝ) ×ˢ 𝓝 w₀))
      (𝓝 OnePoint.infty) := by
    change Filter.map (fun z : ℝ × OnePoint Z.TotalSpace => contractFun Z z.1 z.2)
      (Filter.map (fun z : ℝ × Z.TotalSpace => (z.1, OnePoint.some z.2)) (𝓝 (1 : ℝ) ×ˢ 𝓝 w₀)) ≤
      𝓝 OnePoint.infty
    rw [Filter.map_map]
    exact hcomp
  exact Filter.Tendsto.mono_left hmap (nhds_pair_coe_le 1 w₀)

/-- **The contraction is continuous at every point of `[0,1] × A`.** -/
private theorem continuousAt_contractFun (Z : RealBundle B F ι)
    (hcont : Continuous (Work.Thom.fibreNorm Z)) {t₀ : ℝ} (ht₀ : t₀ ≤ 1)
    {p₀ : OnePoint Z.TotalSpace} (hp₀ : p₀ ∈ absNZ Z) :
    ContinuousAt (fun z : ℝ × OnePoint Z.TotalSpace => contractFun Z z.1 z.2) (t₀, p₀) := by
  cases p₀ with
  | infty => exact continuousAt_contractFun_infty Z hcont ht₀
  | coe w₀ =>
      rcases eq_or_ne t₀ 1 with rfl | ht₀ne
      · refine continuousAt_contractFun_one Z hcont ?_
        rcases (mem_absNZ.mp hp₀) with h | ⟨y, hy, hyeq⟩
        · exact absurd h (OnePoint.coe_ne_infty w₀)
        · have hyw : w₀ = y := OnePoint.coe_eq_coe.mp hyeq
          rw [hyw]
          exact hy
      · exact continuousAt_contractFun_some Z ht₀ne w₀

/-! ## The contraction as a map of `A`, and the contractibility -/

/-- The contraction, as a continuous map `[0,1] × A → A`. -/
private def contractMap (Z : RealBundle B F ι)
    (hcont : Continuous (Work.Thom.fibreNorm Z)) :
    C(unitInterval × ↥(absNZ Z), ↥(absNZ Z)) where
  toFun z := ⟨contractFun Z (z.1 : ℝ) z.2.1, contractFun_mem Z z.2.2⟩
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    rintro ⟨t, p⟩
    rw [ContinuousAt, tendsto_subtype_rng]
    refine ContinuousAt.comp (g := fun z : ℝ × OnePoint Z.TotalSpace => contractFun Z z.1 z.2)
      (f := fun z : unitInterval × ↥(absNZ Z) => ((z.1 : ℝ), z.2.1))
      (continuousAt_contractFun Z hcont (unitInterval.le_one t) p.2) ?_
    exact ContinuousAt.prodMk
      (continuous_subtype_val.continuousAt.comp continuous_fst.continuousAt)
      (continuous_subtype_val.continuousAt.comp continuous_snd.continuousAt)

@[simp] private theorem contractMap_apply (Z : RealBundle B F ι)
    (hcont : Continuous (Work.Thom.fibreNorm Z)) (z : unitInterval × ↥(absNZ Z)) :
    (contractMap Z hcont z : OnePoint Z.TotalSpace) = contractFun Z (z.1 : ℝ) z.2.1 := rfl

/-- **`A = (Z ∖ 0) ∪ {∞}` is contractible**: the radial scaling `w ↦ w/(1-t)` contracts the
complement of the zero section in `Z⁺` onto the point at infinity. -/
private theorem contractibleSpace_absNZ (Z : RealBundle B F ι)
    (hcont : Continuous (Work.Thom.fibreNorm Z)) : ContractibleSpace ↥(absNZ Z) := by
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨⟨OnePoint.infty, Or.inr rfl⟩, ?_⟩
  refine ⟨{ toContinuousMap := contractMap Z hcont
            map_zero_left := ?_
            map_one_left := ?_ }⟩
  · intro x
    apply Subtype.ext
    change contractFun Z ((0 : unitInterval) : ℝ) x.1 = x.1
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl]
    exact contractFun_zero Z x.1
  · intro x
    apply Subtype.ext
    change contractFun Z ((1 : unitInterval) : ℝ) x.1 = OnePoint.infty
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
    exact contractFun_one Z x.1

/-- **The complement of the zero section in the one-point compactification of a real bundle over a
compact Hausdorff base is contractible** (the "absolute" model of the Thom space, with the point at
infinity as the apex of the cone on the sphere bundle). -/
theorem contractibleZeroComplement {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (hcont : Continuous (Work.Thom.fibreNorm Z)) :
    ContractibleSpace ↥(OnePoint.some '' Work.Thom.zeroComplement Z ∪ {OnePoint.infty} :
      Set (OnePoint Z.TotalSpace)) := by
  exact contractibleSpace_absNZ Z hcont

end

end Work.ThomBordism
