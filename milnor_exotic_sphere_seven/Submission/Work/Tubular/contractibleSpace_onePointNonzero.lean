import Submission.Work.Tubular.OnePointCompl
import Submission.Work.Tubular.normalThomSpace_scale

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# `A = (ν ∖ 0) ∪ {∞}` is contractible

The complement of the zero section in the one-point compactification `ν⁺` of the normal bundle of an
embedding `E : V ↪ ℝ^{8+k}` — `Work.Tubular.onePointNonzero E` — is the **cone on the sphere bundle**
`S(ν)`: in the radial coordinate `X ∖ 0 ≅ S(ν) × (0, ∞)` the point at infinity is the apex, and the
radial scaling `w ↦ w/(1-t)` is a homotopy from the identity to the constant `∞`, continuous on
`[0,1] × A` because `∞` is the end of the fibre directions.

This is the geometric input of item (B2) of the chapter: with it,
`Work.Cohomology.homologyMap_cokernel_pi_bijective_of_isZero` turns the long exact sequence of the
pair `(ν⁺, A)` into the isomorphism `Hₙ(ν⁺) ≅ Hₙ(ν⁺,A)`, and excision identifies the latter with
`Hₙ(ν, ν∖0)`.

## The proof

`contractFun E t p` is the point `p/(1-t)` of `ν` (and `∞` when `p = ∞` or `t = 1`); it maps `A`
into itself (`contractFun_mem`) and its values at `t = 0` and `t = 1` are the identity and the
constant `∞`.  Its **joint continuity on `[0,1] × A`** is the only real content, and it holds at
`(t₀, p₀)` for `p₀ ∈ A` — *not* on the zero section:

* at `(t₀, ∞)` and at `(1, p₀)` with `p₀ ≠ 0` the point `p/(1-t)` leaves every compact set (the
  fibrewise norm is `‖w‖/|1-t|`, and either `|1-t|` is small or `‖w‖` is bounded below);
* at `(t₀, p₀)` with `t₀ ≠ 1` the map is the composition of the jointly continuous fibrewise
  scaling with the continuous coefficient `t ↦ (1-t)⁻¹`.
-/

open scoped Topology unitInterval
open Function Topology Set Filter

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

variable {V : Work.ThomBordism.Man8} {N : ℕ}

/-! ## Elementary facts about the fibrewise scaling -/

/-- **The fibrewise scaling is jointly continuous** in the scalar and the point. -/
theorem continuous_normalScaleMap_prod (E : EmbeddingData V N) :
    Continuous fun z : ℝ × NormalTotal E => normalScaleMap E z.1 z.2 := by
  apply Continuous.subtype_mk
  exact ((continuous_subtype_val.fst).comp continuous_snd).prodMk
    (continuous_fst.smul ((continuous_subtype_val.snd).comp continuous_snd))

/-- Scaling by `1` is the identity. -/
theorem normalScaleMap_one (E : EmbeddingData V N) (p : NormalTotal E) :
    normalScaleMap E 1 p = p := by
  apply NormalTotal.ext
  apply Prod.ext
  · rfl
  · simp [normalScaleMap]

/-- **The fibrewise norm under scaling**, with the absolute value of the scalar. -/
theorem normalNorm_normalScaleMap_abs (E : EmbeddingData V N) (r : ℝ) (p : NormalTotal E) :
    normalNorm E (normalScaleMap E r p) = |r| * normalNorm E p := by
  rw [normalNorm]
  show ‖r • p.1.2‖ = |r| * normalNorm E p
  rw [norm_smul, Real.norm_eq_abs, normalNorm]

/-- **Every compact subset of the normal bundle is bounded in the fibre directions.** -/
theorem exists_le_normalNorm_of_isCompact (E : EmbeddingData V N) {K : Set (NormalTotal E)}
    (hK : IsCompact K) : ∃ R : ℝ, 0 ≤ R ∧ ∀ p ∈ K, normalNorm E p ≤ R := by
  have hb : Bornology.IsBounded (normalNorm E '' K) :=
    (hK.image (continuous_normalNorm E)).isBounded
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hb
  refine ⟨max r 0, le_max_right _ _, fun p hp => ?_⟩
  have h1 : normalNorm E p ∈ Metric.closedBall (0 : ℝ) r := hr (mem_image_of_mem _ hp)
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
  exact le_trans (le_abs_self _) (le_trans h1 (le_max_left _ _))

/-- The sets `some '' U`, `U ∈ 𝓝 x`, form a basis of the neighbourhoods of `some x`. -/
theorem nhds_coe_basis {E : EmbeddingData V N} (x : NormalTotal E) :
    (𝓝 (OnePoint.some x)).HasBasis (fun U : Set (NormalTotal E) => U ∈ 𝓝 x)
      (fun U => OnePoint.some '' U) := by
  have h : (𝓝 x).HasBasis (fun s : Set (NormalTotal E) => s ∈ 𝓝 x) id :=
    ⟨fun s => ⟨fun hs => ⟨s, hs, subset_rfl⟩, fun ⟨t, ht, hts⟩ => mem_of_superset ht hts⟩⟩
  simpa [OnePoint.nhds_coe_eq x] using h.map OnePoint.some

/-- **Tendsto into a neighbourhood of `some x`**: it suffices to control the underlying point. -/
theorem tendsto_some_coe {E : EmbeddingData V N} {α : Type*} [TopologicalSpace α]
    {l : Filter α} {h : α → NormalTotal E} {x : NormalTotal E} (hh : Tendsto h l (𝓝 x)) :
    Tendsto (fun a => (OnePoint.some (h a) : OnePoint (NormalTotal E))) l (𝓝 (OnePoint.some x)) := by
  rw [OnePoint.nhds_coe_eq]
  change Filter.map (fun a => OnePoint.some (h a)) l ≤ Filter.map OnePoint.some (𝓝 x)
  simpa only [Filter.map_map, Function.comp_def] using Filter.map_mono (m := OnePoint.some) hh

/-- **The neighbourhood filter of `(t₀, some w₀)` as the image of the product filter**: every
neighbourhood of `(t₀, some w₀)` contains `V × (some '' W)` for `V ∈ 𝓝 t₀`, `W ∈ 𝓝 w₀`. -/
theorem nhds_pair_coe_le {E : EmbeddingData V N} (t₀ : ℝ) (w₀ : NormalTotal E) :
    𝓝 (t₀, OnePoint.some w₀) ≤
      map (fun z : ℝ × NormalTotal E => (z.1, OnePoint.some z.2)) (𝓝 t₀ ×ˢ 𝓝 w₀) := by
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
  have hmem : (t, w) ∈ V ×ˢ T := by
    rw [Set.mem_prod]
    exact ⟨ht, hw⟩
  exact hVT hmem

/-! ## The contraction map -/

/-- **The contraction of `ν⁺ ∖ 0` onto `∞`**: the fibrewise scaling by `(1-t)⁻¹`, with `t = 1`
collapsing everything to `∞` (and the point at infinity fixed). -/
def contractFun (E : EmbeddingData V N) (t : ℝ) (p : OnePoint (NormalTotal E)) :
    OnePoint (NormalTotal E) :=
  if t = 1 then OnePoint.infty else OnePoint.map (normalScaleMap E (1 - t)⁻¹) p

@[simp] theorem contractFun_one (E : EmbeddingData V N) (p : OnePoint (NormalTotal E)) :
    contractFun E 1 p = OnePoint.infty := by
  rw [contractFun, if_pos rfl]

@[simp] theorem contractFun_zero_some (E : EmbeddingData V N) (p : NormalTotal E) :
    contractFun E 0 (OnePoint.some p) = OnePoint.some p := by
  rw [contractFun, if_neg (by norm_num : (0 : ℝ) ≠ 1), sub_zero, inv_one,
    OnePoint.map_some, normalScaleMap_one]

@[simp] theorem contractFun_infty (E : EmbeddingData V N) (t : ℝ) :
    contractFun E t (OnePoint.infty) = OnePoint.infty := by
  rw [contractFun]
  split
  · rfl
  · exact OnePoint.map_infty _

@[simp] theorem contractFun_zero (E : EmbeddingData V N) (p : OnePoint (NormalTotal E)) :
    contractFun E 0 p = p := by
  cases p with
  | infty => exact contractFun_infty E 0
  | coe w => exact contractFun_zero_some E w

@[simp] theorem contractFun_some (E : EmbeddingData V N) {t : ℝ} (ht : t ≠ 1)
    (p : NormalTotal E) :
    contractFun E t (OnePoint.some p) = OnePoint.some (normalScaleMap E (1 - t)⁻¹ p) := by
  rw [contractFun, if_neg ht, OnePoint.map_some]

/-- **`contractFun` maps `A = (ν∖0) ∪ {∞}` into itself.** -/
theorem contractFun_mem (E : EmbeddingData V N) {t : ℝ} {p : OnePoint (NormalTotal E)}
    (hp : p ∈ onePointNonzero E) : contractFun E t p ∈ onePointNonzero E := by
  rw [mem_onePointNonzero] at hp ⊢
  rcases hp with rfl | ⟨w, hw, rfl⟩
  · rw [contractFun_infty]; exact Or.inl rfl
  · rcases eq_or_ne t 1 with rfl | ht
    · rw [contractFun_one]; exact Or.inl rfl
    · refine Or.inr ⟨normalScaleMap E (1 - t)⁻¹ w, ?_,
        (contractFun_some E ht w).symm ▸ rfl⟩
      rw [normalNorm_normalScaleMap_abs]
      intro h
      rcases mul_eq_zero.mp h with h1 | h2
      · rw [abs_eq_zero, inv_eq_zero] at h1
        exact ht (by linarith)
      · exact hw h2

/-! ## Joint continuity of the contraction, at the three kinds of points of `[0,1] × A` -/

/-- **Continuity of the contraction at `(t₀, ∞)`** (for `t₀ ≤ 1`). -/
theorem continuousAt_contractFun_infty {k : ℕ} (E : EmbeddingData V (8 + k)) {t₀ : ℝ}
    (ht₀ : t₀ ≤ 1) :
    ContinuousAt (fun z : ℝ × OnePoint (NormalTotal E) => contractFun E z.1 z.2)
      (t₀, OnePoint.infty) := by
  rw [ContinuousAt]
  have hval : contractFun E ((t₀, OnePoint.infty) : ℝ × OnePoint (NormalTotal E)).1
      ((t₀, OnePoint.infty) : ℝ × OnePoint (NormalTotal E)).2 = OnePoint.infty :=
    contractFun_infty E t₀
  rw [hval, nhds_prod_eq]
  refine (OnePoint.hasBasis_nhds_infty.tendsto_right_iff).mpr ?_
  rintro K ⟨hKc, hKcomp⟩
  obtain ⟨R, hR0, hR⟩ := exists_le_normalNorm_of_isCompact E hKcomp
  set τ : ℝ := |1 - t₀| + 1 with hτdef
  have hτpos : 0 < τ := by positivity
  set L : Set (NormalTotal E) := {p : NormalTotal E | normalNorm E p ≤ (R + 1) * τ} with hLdef
  have hLc : IsClosed L := isClosed_le (continuous_normalNorm E) continuous_const
  have hLcomp : IsCompact L := by
    rw [hLdef]
    exact isCompact_normalClosedDiscSet E ((R + 1) * τ)
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
    · change contractFun E 1 (OnePoint.some x) ∈ OnePoint.some '' Kᶜ ∪ {OnePoint.infty}
      rw [contractFun_one]; exact Or.inr rfl
    · change contractFun E t (OnePoint.some x) ∈ OnePoint.some '' Kᶜ ∪ {OnePoint.infty}
      rw [contractFun_some E htne]
      refine Or.inl ⟨normalScaleMap E (1 - t)⁻¹ x, ?_, rfl⟩
      intro hxK
      have h1 : normalNorm E (normalScaleMap E (1 - t)⁻¹ x) ≤ R := hR _ hxK
      rw [normalNorm_normalScaleMap_abs] at h1
      have h2 : (R + 1) * τ < normalNorm E x := lt_of_not_ge hxL
      have h3 : 1 / τ ≤ |(1 - t)⁻¹| := by
        have habs : |1 - t| ≤ τ := ht1
        have hpos : 0 < |1 - t| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm htne))
        rw [abs_inv, inv_eq_one_div]
        exact one_div_le_one_div_of_le hpos habs
      have h4 : R + 1 < |(1 - t)⁻¹| * normalNorm E x := by
        calc R + 1 = (1 / τ) * ((R + 1) * τ) := by field_simp
          _ < (1 / τ) * normalNorm E x := mul_lt_mul_of_pos_left h2 (by positivity)
          _ ≤ |(1 - t)⁻¹| * normalNorm E x :=
              mul_le_mul_of_nonneg_right h3 (normalNorm_nonneg E x)
      linarith
  · change contractFun E t (OnePoint.infty : OnePoint (NormalTotal E))
      ∈ OnePoint.some '' Kᶜ ∪ {OnePoint.infty}
    rw [contractFun_infty]; exact Or.inr rfl

/-- **Continuity of the contraction at `(t₀, some w₀)` for `t₀ ≠ 1`** (no hypothesis on `w₀`). -/
theorem continuousAt_contractFun_some {k : ℕ} (E : EmbeddingData V (8 + k)) {t₀ : ℝ}
    (ht₀ne : t₀ ≠ 1) (w₀ : NormalTotal E) :
    ContinuousAt (fun z : ℝ × OnePoint (NormalTotal E) => contractFun E z.1 z.2)
      (t₀, OnePoint.some w₀) := by
  rw [ContinuousAt]
  have hval : contractFun E (t₀, OnePoint.some w₀).1 (t₀, OnePoint.some w₀).2
      = OnePoint.some (normalScaleMap E (1 - t₀)⁻¹ w₀) := contractFun_some E ht₀ne w₀
  rw [hval]
  have hjoint : Tendsto (fun z : ℝ × NormalTotal E => normalScaleMap E (1 - z.1)⁻¹ z.2)
      (𝓝 t₀ ×ˢ 𝓝 w₀) (𝓝 (normalScaleMap E (1 - t₀)⁻¹ w₀)) := by
    rw [← nhds_prod_eq]
    refine ContinuousAt.comp (g := fun z : ℝ × NormalTotal E => normalScaleMap E z.1 z.2)
      (f := fun z : ℝ × NormalTotal E => ((1 - z.1)⁻¹, z.2))
      (continuous_normalScaleMap_prod E).continuousAt ?_
    refine ContinuousAt.prodMk ?_ continuousAt_snd
    exact (continuousAt_const.sub continuousAt_fst).inv₀ (sub_ne_zero.mpr (Ne.symm ht₀ne))
  have hcomp : Tendsto (fun z : ℝ × NormalTotal E => contractFun E z.1 (OnePoint.some z.2))
      (𝓝 t₀ ×ˢ 𝓝 w₀) (𝓝 (OnePoint.some (normalScaleMap E (1 - t₀)⁻¹ w₀))) := by
    have hev : (fun z : ℝ × NormalTotal E => OnePoint.some (normalScaleMap E (1 - z.1)⁻¹ z.2))
        =ᶠ[𝓝 t₀ ×ˢ 𝓝 w₀]
        (fun z : ℝ × NormalTotal E => contractFun E z.1 (OnePoint.some z.2)) := by
      filter_upwards [Filter.prod_mem_prod (isOpen_ne.mem_nhds ht₀ne) Filter.univ_mem] with z hz
      rw [contractFun_some E hz.1]
    exact Filter.Tendsto.congr' hev (tendsto_some_coe hjoint)
  have hmap : Tendsto (fun z : ℝ × OnePoint (NormalTotal E) => contractFun E z.1 z.2)
      (map (fun z : ℝ × NormalTotal E => (z.1, OnePoint.some z.2)) (𝓝 t₀ ×ˢ 𝓝 w₀))
      (𝓝 (OnePoint.some (normalScaleMap E (1 - t₀)⁻¹ w₀))) := by
    change Filter.map (fun z : ℝ × OnePoint (NormalTotal E) => contractFun E z.1 z.2)
      (Filter.map (fun z : ℝ × NormalTotal E => (z.1, OnePoint.some z.2)) (𝓝 t₀ ×ˢ 𝓝 w₀)) ≤
      𝓝 (OnePoint.some (normalScaleMap E (1 - t₀)⁻¹ w₀))
    rw [Filter.map_map]
    exact hcomp
  exact Filter.Tendsto.mono_left hmap (nhds_pair_coe_le t₀ w₀)

/-- **Continuity of the contraction at `(1, some w₀)` with `‖w₀‖ ≠ 0`**: the point `w₀/(1-t)` leaves
every compact set as `t → 1`, uniformly in a neighbourhood of `w₀`. -/
theorem continuousAt_contractFun_one {k : ℕ} (E : EmbeddingData V (8 + k)) {w₀ : NormalTotal E}
    (hw₀ : normalNorm E w₀ ≠ 0) :
    ContinuousAt (fun z : ℝ × OnePoint (NormalTotal E) => contractFun E z.1 z.2)
      (1, OnePoint.some w₀) := by
  have hw₀pos : 0 < normalNorm E w₀ := lt_of_le_of_ne (normalNorm_nonneg E w₀) (Ne.symm hw₀)
  set η : ℝ := normalNorm E w₀ / 2 with hηdef
  have hηpos : 0 < η := by rw [hηdef]; linarith
  rw [ContinuousAt]
  have hval : contractFun E ((1 : ℝ), OnePoint.some w₀).1 ((1 : ℝ), OnePoint.some w₀).2
      = OnePoint.infty := contractFun_one E _
  rw [hval]
  have hcomp : Tendsto (fun z : ℝ × NormalTotal E => contractFun E z.1 (OnePoint.some z.2))
      (𝓝 (1 : ℝ) ×ˢ 𝓝 w₀) (𝓝 OnePoint.infty) := by
    refine (OnePoint.hasBasis_nhds_infty.tendsto_right_iff).mpr ?_
    rintro K ⟨hKc, hKcomp⟩
    obtain ⟨R, hR0, hR⟩ := exists_le_normalNorm_of_isCompact E hKcomp
    set δd : ℝ := η / (R + 1) with hδddef
    have hδdpos : 0 < δd := by rw [hδddef]; positivity
    have hW : {w : NormalTotal E | η < normalNorm E w} ∈ 𝓝 w₀ :=
      (isOpen_lt continuous_const (continuous_normalNorm E)).mem_nhds
        (by show η < normalNorm E w₀; rw [hηdef]; linarith)
    rw [Filter.eventually_iff]
    refine Filter.mem_of_superset (Filter.prod_mem_prod
      (Ioo_mem_nhds (a := 1 - δd) (b := 1 + δd) (by linarith) (by linarith)) hW) ?_
    rintro ⟨t, w⟩ ⟨ht, hw⟩
    rw [Set.mem_Ioo] at ht
    rcases eq_or_ne t 1 with rfl | htne
    · change contractFun E 1 (OnePoint.some w) ∈ OnePoint.some '' Kᶜ ∪ {OnePoint.infty}
      rw [contractFun_one]; exact Or.inr rfl
    · change contractFun E t (OnePoint.some w) ∈ OnePoint.some '' Kᶜ ∪ {OnePoint.infty}
      rw [contractFun_some E htne]
      refine Or.inl ⟨normalScaleMap E (1 - t)⁻¹ w, ?_, rfl⟩
      intro hwK
      have h1 : normalNorm E (normalScaleMap E (1 - t)⁻¹ w) ≤ R := hR _ hwK
      rw [normalNorm_normalScaleMap_abs] at h1
      have habs : |1 - t| < δd := by
        rw [abs_lt]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have h2 : 1 / δd < |(1 - t)⁻¹| := by
        have hpos : 0 < |1 - t| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm htne))
        rw [abs_inv, inv_eq_one_div]
        exact one_div_lt_one_div_of_lt hpos habs
      have h3 : 1 / δd = (R + 1) / η := by rw [hδddef, one_div_div]
      have h4 : (R + 1) / η < |(1 - t)⁻¹| := by rw [← h3]; exact h2
      have h5 : R < |(1 - t)⁻¹| * normalNorm E w := by
        calc R < R + 1 := by linarith
          _ = ((R + 1) / η) * η := by field_simp
          _ < |(1 - t)⁻¹| * normalNorm E w :=
              mul_lt_mul h4 (le_of_lt hw) hηpos (by positivity)
      linarith
  have hmap : Tendsto (fun z : ℝ × OnePoint (NormalTotal E) => contractFun E z.1 z.2)
      (map (fun z : ℝ × NormalTotal E => (z.1, OnePoint.some z.2)) (𝓝 (1 : ℝ) ×ˢ 𝓝 w₀))
      (𝓝 OnePoint.infty) := by
    change Filter.map (fun z : ℝ × OnePoint (NormalTotal E) => contractFun E z.1 z.2)
      (Filter.map (fun z : ℝ × NormalTotal E => (z.1, OnePoint.some z.2)) (𝓝 (1 : ℝ) ×ˢ 𝓝 w₀)) ≤
      𝓝 OnePoint.infty
    rw [Filter.map_map]
    exact hcomp
  exact Filter.Tendsto.mono_left hmap (nhds_pair_coe_le 1 w₀)

/-- **The contraction is continuous at every point of `[0,1] × A`.** -/
theorem continuousAt_contractFun {k : ℕ} (E : EmbeddingData V (8 + k)) {t₀ : ℝ} (ht₀ : t₀ ≤ 1)
    {p₀ : OnePoint (NormalTotal E)} (hp₀ : p₀ ∈ onePointNonzero E) :
    ContinuousAt (fun z : ℝ × OnePoint (NormalTotal E) => contractFun E z.1 z.2) (t₀, p₀) := by
  cases p₀ with
  | infty => exact continuousAt_contractFun_infty E ht₀
  | coe w₀ =>
      rcases eq_or_ne t₀ 1 with rfl | ht₀ne
      · refine continuousAt_contractFun_one E ?_
        rcases (mem_onePointNonzero.mp hp₀) with h | ⟨y, hy, hyeq⟩
        · exact absurd h (OnePoint.coe_ne_infty w₀)
        · have hyw : y = w₀ := OnePoint.coe_eq_coe.mp hyeq
          rwa [← hyw]
      · exact continuousAt_contractFun_some E ht₀ne w₀

/-! ## The contraction as a map of `A`, and the contractibility -/

/-- The contraction, as a continuous map `[0,1] × A → A`. -/
def contractMap {k : ℕ} (E : EmbeddingData V (8 + k)) :
    C(unitInterval × ↥(onePointNonzero E), ↥(onePointNonzero E)) where
  toFun z := ⟨contractFun E (z.1 : ℝ) z.2.1, contractFun_mem E z.2.2⟩
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    rintro ⟨t, p⟩
    rw [ContinuousAt, tendsto_subtype_rng]
    refine ContinuousAt.comp (g := fun z : ℝ × OnePoint (NormalTotal E) => contractFun E z.1 z.2)
      (f := fun z : unitInterval × ↥(onePointNonzero E) => ((z.1 : ℝ), z.2.1))
      (continuousAt_contractFun E (unitInterval.le_one t) p.2) ?_
    exact ContinuousAt.prodMk
      (continuous_subtype_val.continuousAt.comp continuous_fst.continuousAt)
      (continuous_subtype_val.continuousAt.comp continuous_snd.continuousAt)

@[simp] theorem contractMap_apply {k : ℕ} (E : EmbeddingData V (8 + k))
    (z : unitInterval × ↥(onePointNonzero E)) :
    (contractMap E z : OnePoint (NormalTotal E)) = contractFun E (z.1 : ℝ) z.2.1 := rfl

/-- **`A = (ν ∖ 0) ∪ {∞}` is contractible**: the homeomorphism `w ↦ w/(1-t)` contracts the
complement of the zero section in `ν⁺` onto the point at infinity. -/
theorem contractibleSpace_onePointNonzero {k : ℕ} (E : EmbeddingData V (8 + k)) :
    ContractibleSpace ↥(onePointNonzero E) := by
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨⟨OnePoint.infty, Or.inr rfl⟩, ?_⟩
  refine ⟨{ toContinuousMap := contractMap E
            map_zero_left := ?_
            map_one_left := ?_ }⟩
  · intro x
    apply Subtype.ext
    change contractFun E ((0 : unitInterval) : ℝ) x.1 = x.1
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl]
    exact contractFun_zero E x.1
  · intro x
    apply Subtype.ext
    change contractFun E ((1 : unitInterval) : ℝ) x.1 = OnePoint.infty
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
    exact contractFun_one E x.1

end

end Work.Tubular
