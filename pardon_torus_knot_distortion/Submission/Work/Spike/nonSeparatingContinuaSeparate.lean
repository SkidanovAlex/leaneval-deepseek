import Mathlib
import Submission.Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy
import Submission.Work.Smooth.SphereJordan.mobiusAddInv
import Submission.Work.SphereJordan.domain_compl_simplyConnected
import Submission.Work.Smooth.JordanSeparation.isSimplyConnected_union_of_isOpen
import Submission.Work.Smooth.SphereJordan.jordanCurve_twoComponents
import Submission.Work.Smooth.JordanSeparation.onePoint_locallyPathConnected

/-!
# Two compact continua meeting in two points separate the plane

`Work.Spike.nonSeparatingContinuaSeparate`: if `K₁`, `K₂ ⊆ ℂ` are compact, preconnected, have
*connected complements* and intersect in exactly two points `p ≠ q`, then `(K₁ ∪ K₂)ᶜ` has two
points in different connected components — i.e. `K₁ ∪ K₂` separates the plane.

## The proof

By contradiction, assume `W := (K₁ ∪ K₂)ᶜ` preconnected.  In the Riemann sphere `S² = OnePoint ℂ`
put
* `U := (↑''K₁)ᶜ`, `V := (↑''K₂)ᶜ` — these are complementary domains of the continua `↑''K₁`,
  `↑''K₂`, hence (by `domain_compl_simplyConnected`: complementary domains of continua in `S²` are
  simply connected) they are simply connected;
* `U ∩ V = (↑''(K₁ ∪ K₂))ᶜ` is preconnected (assuming `W` preconnected) and open, hence path
  connected;
* `U ∪ V = ({↑p, ↑q})ᶜ`.

The elementary van Kampen lemma (`simplyConnectedSpace_of_isOpen_cover`) then shows that
`U ∪ V = S² ∖ {↑p, ↑q}` is simply connected.  But the twice punctured sphere is an annulus, and
is *not* simply connected: a Möbius transformation carries `{↑p, ↑q}` to `{∞, 0}` (so that
`S² ∖ {↑p,↑q} ≅ ℂ ∖ {0}`), and in `ℂ ∖ {0}` the standard loop `t ↦ exp (2 π i t)` has index `1`
while a constant loop has index `0`; a null-homotopy would give a nowhere vanishing homotopy of
closed loops, hence equal indices (`loopIndex_eq_of_homotopy`).  Contradiction.
-/

namespace Work.Spike

open Set
open scoped OnePoint

noncomputable section

/-! ## The twice punctured sphere is not simply connected -/

/-- **The punctured plane is not simply connected.**  The standard loop `t ↦ exp (2πit)` has
index `1`, while a constant loop has index `0`, and `loopIndex` is invariant under a nowhere
vanishing homotopy of closed loops. -/
theorem not_simplyConnected_compl_zero : ¬ IsSimplyConnected (({0} : Set ℂ)ᶜ) := by
  intro h
  haveI : SimplyConnectedSpace ↥(({0} : Set ℂ)ᶜ) := h
  -- the standard loop
  set c : C(unitInterval, ℂ) :=
    ⟨fun t : unitInterval => Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (t : ℝ)),
      by fun_prop⟩ with hcdef
  have hcval : ∀ t : unitInterval,
      c t = Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (t : ℝ)) := fun t => rfl
  have hcne : ∀ t : unitInterval, c t ≠ 0 := fun t => by
    rw [hcval t]; exact Complex.exp_ne_zero _
  have hc0 : c 0 = 1 := by
    rw [hcval 0]; simp
  have hc1 : c 1 = 1 := by
    rw [hcval 1]
    have h1 : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((1 : unitInterval) : ℝ)
        = 2 * Real.pi * Complex.I := by
      push_cast
      ring
    rw [h1, Complex.exp_two_pi_mul_I]
  -- its index is `1`
  have hidx : Work.Smooth.SphereJordan.loopIndex c = 1 := by
    have hcloop : c 0 = c 1 := by rw [hc0, hc1]
    set Λ : C(unitInterval, ℂ) :=
      ⟨fun t : unitInterval => (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (t : ℝ), by fun_prop⟩
      with hΛdef
    have hlift : ∀ t : unitInterval, Complex.exp (Λ t) = c t := fun t => by
      rw [hcval t]; rfl
    have hspec := Work.Smooth.SphereJordan.loopIndex_spec c hcne hcloop Λ hlift
    have hleft : Λ 1 - Λ 0 = 1 * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hΛdef]
      simp
    rw [hleft] at hspec
    have h2 : ((Work.Smooth.SphereJordan.loopIndex c : ℤ) : ℂ) = 1 :=
      mul_right_cancel₀ Work.Smooth.SphereJordan.two_pi_I_ne_zero hspec.symm
    exact_mod_cast h2
  -- the same loop, as a path of the subtype
  have hcmem : ∀ t : unitInterval, c t ∈ (({0} : Set ℂ)ᶜ) := fun t => by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hcne t
  set x : ↥(({0} : Set ℂ)ᶜ) := ⟨1, by simp⟩ with hxdef
  set γ : Path x x :=
    { toFun := fun t => (⟨c t, hcmem t⟩ : ↥(({0} : Set ℂ)ᶜ))
      continuous_toFun := Continuous.subtype_mk c.continuous hcmem
      source' := Subtype.ext hc0
      target' := Subtype.ext hc1 } with hγdef
  obtain ⟨F⟩ : Nonempty (γ.Homotopy (Path.refl x)) :=
    SimplyConnectedSpace.paths_homotopic γ (Path.refl x)
  -- a nowhere vanishing plane homotopy of closed loops
  set H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun s => ((F (s.2, s.1) : ↥(({0} : Set ℂ)ᶜ)) : ℂ),
      continuous_subtype_val.comp (F.continuous.comp (by fun_prop))⟩ with hHdef
  have hHne : ∀ s : unitInterval × unitInterval, H s ≠ 0 := by
    rintro ⟨a, b⟩
    show ((F (b, a) : ↥(({0} : Set ℂ)ᶜ)) : ℂ) ≠ 0
    have hmem : ((F (b, a) : ↥(({0} : Set ℂ)ᶜ)) : ℂ) ∈ (({0} : Set ℂ)ᶜ) := (F (b, a)).2
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hmem
  have hH0 : ∀ t : unitInterval, H (t, 0) = c t := by
    intro t
    show ((F (0, t) : ↥(({0} : Set ℂ)ᶜ)) : ℂ) = c t
    have h1 : ((F (0, t) : ↥(({0} : Set ℂ)ᶜ)) : ℂ) = ((γ t : ↥(({0} : Set ℂ)ᶜ)) : ℂ) :=
      congrArg (fun w : ↥(({0} : Set ℂ)ᶜ) => (w : ℂ)) (F.map_zero_left t)
    rw [h1]
    rfl
  have hH1 : ∀ t : unitInterval, H (t, 1) = (ContinuousMap.const unitInterval (1 : ℂ)) t := by
    intro t
    show ((F (1, t) : ↥(({0} : Set ℂ)ᶜ)) : ℂ) = (ContinuousMap.const unitInterval (1 : ℂ)) t
    have h1 : ((F (1, t) : ↥(({0} : Set ℂ)ᶜ)) : ℂ) = (((Path.refl x) t) : ℂ) :=
      congrArg (fun w : ↥(({0} : Set ℂ)ᶜ) => (w : ℂ)) (F.map_one_left t)
    rw [h1]
    rfl
  have hHloop : ∀ s : unitInterval, H (0, s) = H (1, s) := by
    intro s
    show ((F (s, 0) : ↥(({0} : Set ℂ)ᶜ)) : ℂ) = ((F (s, 1) : ↥(({0} : Set ℂ)ᶜ)) : ℂ)
    rw [Path.Homotopy.source F s, Path.Homotopy.target F s]
  have hzero : Work.Smooth.SphereJordan.loopIndex c = 0 := by
    have hh := Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy (c₀ := c)
      (c₁ := ContinuousMap.const unitInterval (1 : ℂ)) hcne (by simp) H hHne hH0 hH1 hHloop
    rwa [Work.Smooth.SphereJordan.loopIndex_const (1 : ℂ) one_ne_zero] at hh
  rw [hidx] at hzero
  exact one_ne_zero hzero

/-- **The twice punctured Riemann sphere is not simply connected.**  A Möbius transformation
carries `{↑p, ↑q}` to `{∞, 0}`, so `S² ∖ {↑p, ↑q} ≅ ℂ ∖ {0}`. -/
theorem not_simplyConnected_compl_pair {p q : ℂ} (hpq : p ≠ q) :
    ¬ IsSimplyConnected (({↑p, ↑q} : Set (OnePoint ℂ))ᶜ) := by
  intro h
  obtain ⟨Φ, hΦinfty, hΦ0, hΦz⟩ := Work.Smooth.SphereJordan.mobiusAddInv (-(q - p)⁻¹)
  set T : OnePoint ℂ ≃ₜ OnePoint ℂ :=
    Homeomorph.onePointCongr (Homeomorph.addRight (-p)) with hTdef
  set Ψ : OnePoint ℂ ≃ₜ OnePoint ℂ := T.trans Φ with hΨdef
  have hT : ∀ z : ℂ, T (↑z : OnePoint ℂ) = ↑(z - p) := by
    intro z
    rw [hTdef, Homeomorph.onePointCongr_apply]
    simp
    ring
  have hTinf : T ∞ = ∞ := by
    rw [hTdef, Homeomorph.onePointCongr_apply]
    simp
  have hΨp : Ψ (↑p : OnePoint ℂ) = ∞ := by
    rw [hΨdef, Homeomorph.trans_apply, hT p, sub_self]
    exact hΦ0
  have hΨq : Ψ (↑q : OnePoint ℂ) = (↑(0 : ℂ) : OnePoint ℂ) := by
    rw [hΨdef, Homeomorph.trans_apply, hT q, hΦz (q - p) (sub_ne_zero.mpr hpq.symm)]
    have h0 : -(q - p)⁻¹ + (q - p)⁻¹ = 0 := by ring
    rw [h0]
  -- the preimage of the complement of `{∞, 0}`
  have hpre : Ψ ⁻¹' (({∞, (↑(0 : ℂ) : OnePoint ℂ)} : Set (OnePoint ℂ))ᶜ)
      = ({↑p, ↑q} : Set (OnePoint ℂ))ᶜ := by
    rw [Set.preimage_compl]
    congr 1
    ext y
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (hy | hy)
      · left
        exact Ψ.injective (by rw [hy, hΨp])
      · right
        exact Ψ.injective (by rw [hy, hΨq])
    · rintro (hy | hy)
      · exact Or.inl (by rw [hy]; exact hΨp)
      · exact Or.inr (by rw [hy]; exact hΨq)
  have h1 : IsSimplyConnected (({∞, (↑(0 : ℂ) : OnePoint ℂ)} : Set (OnePoint ℂ))ᶜ) := by
    have hpre' : IsSimplyConnected
        (Ψ ⁻¹' (({∞, (↑(0 : ℂ) : OnePoint ℂ)} : Set (OnePoint ℂ))ᶜ)) := by
      rw [hpre]; exact h
    exact (Homeomorph.isSimplyConnected_preimage Ψ).mp hpre'
  -- `{∞,0}ᶜ = ↑''({0}ᶜ)`
  have hset : (({∞, (↑(0 : ℂ) : OnePoint ℂ)} : Set (OnePoint ℂ))ᶜ)
      = OnePoint.some '' (({0} : Set ℂ)ᶜ) := by
    ext y
    constructor
    · intro hy
      rw [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hy
      obtain ⟨hy1, hy2⟩ := hy
      cases y using OnePoint.rec with
      | infty => exact absurd rfl hy1
      | coe z =>
        refine ⟨z, ?_, rfl⟩
        rw [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hz
        exact hy2 (by rw [hz])
    · rintro ⟨z, hz, rfl⟩
      rw [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
      exact ⟨OnePoint.coe_ne_infty z, fun hc => hz (OnePoint.coe_injective hc)⟩
  have h2 : IsSimplyConnected (({0} : Set ℂ)ᶜ) := by
    have h3 : IsSimplyConnected (OnePoint.some '' (({0} : Set ℂ)ᶜ)) := by
      rw [← hset]; exact h1
    exact (Topology.IsEmbedding.isSimplyConnected_image
      (OnePoint.isOpenEmbedding_coe (X := ℂ)).toIsEmbedding (s := (({0} : Set ℂ)ᶜ))).mp h3
  exact not_simplyConnected_compl_zero h2

/-! ## Elementary van Kampen and the sphere complement of a continuum -/

/-- **Van Kampen, in the subspace form.**  The union of two open simply connected sets with path
connected intersection is simply connected. -/
theorem isSimplyConnected_union {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hUo : IsOpen U) (hVo : IsOpen V) (hU : IsSimplyConnected U) (hV : IsSimplyConnected V)
    (hUV : IsPathConnected (U ∩ V)) : IsSimplyConnected (U ∪ V) := by
  have hcov : ((↑) ⁻¹' U : Set ↥(U ∪ V)) ∪ ((↑) ⁻¹' V : Set ↥(U ∪ V)) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_univ, iff_true]
    exact x.2
  have hemb : Topology.IsEmbedding ((↑) : ↥(U ∪ V) → X) := Topology.IsEmbedding.subtypeVal
  have hU' : IsSimplyConnected ((↑) ⁻¹' U : Set ↥(U ∪ V)) := by
    have himg : (↑) '' ((↑) ⁻¹' U : Set ↥(U ∪ V)) = U := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨⟨x, Or.inl hx⟩, hx, rfl⟩
    rw [← (hemb.isSimplyConnected_image (s := ((↑) ⁻¹' U : Set ↥(U ∪ V)))), himg]
    exact hU
  have hV' : IsSimplyConnected ((↑) ⁻¹' V : Set ↥(U ∪ V)) := by
    have himg : (↑) '' ((↑) ⁻¹' V : Set ↥(U ∪ V)) = V := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨⟨x, Or.inr hx⟩, hx, rfl⟩
    rw [← (hemb.isSimplyConnected_image (s := ((↑) ⁻¹' V : Set ↥(U ∪ V)))), himg]
    exact hV
  have hUV' : IsPathConnected
      (((↑) ⁻¹' U : Set ↥(U ∪ V)) ∩ ((↑) ⁻¹' V : Set ↥(U ∪ V))) := by
    have h1 : (((↑) ⁻¹' U : Set ↥(U ∪ V)) ∩ ((↑) ⁻¹' V : Set ↥(U ∪ V)))
        = ((↑) ⁻¹' (U ∩ V) : Set ↥(U ∪ V)) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [h1]
    exact hUV.preimage_coe (fun x hx => Or.inl hx.1)
  exact Work.Smooth.JordanSeparation.simplyConnectedSpace_of_isOpen_cover
    (hUo.preimage continuous_subtype_val) (hVo.preimage continuous_subtype_val)
    hU' hV' hUV' hcov

/-- The complement in the sphere of the image of a compact set whose complement (in the plane) is
preconnected is preconnected. -/
theorem isPreconnected_compl_image_coe {K : Set ℂ} (hKc : IsCompact K)
    (hKp : IsPreconnected (Kᶜ : Set ℂ)) :
    IsPreconnected (((↑) '' K)ᶜ : Set (OnePoint ℂ)) := by
  rw [OnePoint.compl_image_coe]
  refine IsPreconnected.subset_closure (hKp.image _ OnePoint.continuous_coe.continuousOn)
    subset_union_left ?_
  intro z hz
  rcases hz with hz | hz
  · exact subset_closure hz
  · rw [Set.mem_singleton_iff] at hz
    rw [hz]
    refine Work.Smooth.SphereJordan.infty_mem_closure_coe_image (fun R => ?_)
    obtain ⟨C, hC⟩ := hKc.isBounded.subset_closedBall (0 : ℂ)
    refine ⟨((|C| + |R| + 1 : ℝ) : ℂ), ?_, ?_⟩
    · rw [Set.mem_compl_iff]
      intro hmem
      have h1 := hC hmem
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)] at h1
      linarith [le_abs_self C, abs_nonneg R]
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith [le_abs_self R, abs_nonneg C]

/-- **Complementary domains of continua in the sphere are simply connected**: the complement of
`↑''K` for a compact preconnected `K ⊆ ℂ` with preconnected complement. -/
theorem isSimplyConnected_compl_image_coe {K : Set ℂ} (hKc : IsCompact K)
    (hKp : IsPreconnected K) (hKpc : IsPreconnected (Kᶜ : Set ℂ)) :
    IsSimplyConnected (((↑) '' K)ᶜ : Set (OnePoint ℂ)) := by
  refine Work.SphereJordan.domain_compl_simplyConnected ?_ ?_ ?_ ?_
  · exact ((OnePoint.isClosed_image_coe).mpr ⟨hKc.isClosed, hKc⟩).isOpen_compl
  · exact ⟨∞, by rw [OnePoint.compl_image_coe]; exact Or.inr rfl⟩
  · exact isPreconnected_compl_image_coe hKc hKpc
  · rw [compl_compl]
    exact hKp.image _ OnePoint.continuous_coe.continuousOn

/-! ## The target: two continua meeting in two points separate the plane -/

theorem nonSeparatingContinuaSeparate {K₁ K₂ : Set ℂ} (h₁ : IsCompact K₁) (h₂ : IsCompact K₂)
    (hc₁ : IsPreconnected K₁) (hc₂ : IsPreconnected K₂)
    (hd₁ : IsPreconnected (K₁ᶜ : Set ℂ)) (hd₂ : IsPreconnected (K₂ᶜ : Set ℂ))
    {p q : ℂ} (hpq : p ≠ q) (hint : K₁ ∩ K₂ = {p, q}) :
    ∃ a b : ℂ, a ∉ K₁ ∪ K₂ ∧ b ∉ K₁ ∪ K₂ ∧
      b ∉ connectedComponentIn (K₁ ∪ K₂)ᶜ a := by
  by_contra hcon
  have hcon' : ∀ a : ℂ, a ∉ K₁ ∪ K₂ → ∀ b : ℂ, b ∉ K₁ ∪ K₂ →
      b ∈ connectedComponentIn (K₁ ∪ K₂)ᶜ a := by
    intro a ha b hb
    by_contra hb'
    exact hcon ⟨a, b, ha, hb, hb'⟩
  have hpK₁ : p ∈ K₁ := (by rw [hint]; exact Or.inl rfl : p ∈ K₁ ∩ K₂).1
  have hKcpt : IsCompact (K₁ ∪ K₂) := h₁.union h₂
  -- the complement of the union is nonempty
  have hWne : ((K₁ ∪ K₂)ᶜ : Set ℂ).Nonempty := by
    obtain ⟨R, hR⟩ := hKcpt.isBounded.subset_closedBall (0 : ℂ)
    have hRp : 0 ≤ R := by
      have h2 := hR (Or.inl hpK₁)
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h2
      exact le_trans (norm_nonneg p) h2
    refine ⟨((R + 1 : ℝ) : ℂ), ?_⟩
    rw [Set.mem_compl_iff]
    intro hmem
    have h2 := hR hmem
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h2
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at h2
    linarith
  obtain ⟨w₀, hw₀⟩ := hWne
  -- so it is preconnected
  have hWpre : IsPreconnected ((K₁ ∪ K₂)ᶜ : Set ℂ) := by
    have heq : ((K₁ ∪ K₂)ᶜ : Set ℂ) = connectedComponentIn ((K₁ ∪ K₂)ᶜ) w₀ :=
      Subset.antisymm (fun y hy => hcon' w₀ hw₀ y hy) (connectedComponentIn_subset _ _)
    rw [heq]
    exact isPreconnected_connectedComponentIn
  -- the two complementary domains in the sphere
  set U : Set (OnePoint ℂ) := ((↑) '' K₁)ᶜ with hUdef
  set V : Set (OnePoint ℂ) := ((↑) '' K₂)ᶜ with hVdef
  have hUo : IsOpen U := ((OnePoint.isClosed_image_coe).mpr ⟨h₁.isClosed, h₁⟩).isOpen_compl
  have hVo : IsOpen V := ((OnePoint.isClosed_image_coe).mpr ⟨h₂.isClosed, h₂⟩).isOpen_compl
  have hUsc : IsSimplyConnected U := isSimplyConnected_compl_image_coe h₁ hc₁ hd₁
  have hVsc : IsSimplyConnected V := isSimplyConnected_compl_image_coe h₂ hc₂ hd₂
  -- the intersection is path connected
  have hinter : U ∩ V = (((↑) '' (K₁ ∪ K₂))ᶜ : Set (OnePoint ℂ)) := by
    rw [hUdef, hVdef, ← Set.compl_union, Set.image_union]
  haveI : LocallyPathConnectedSpace (OnePoint ℂ) :=
    Work.Smooth.JordanSeparation.onePoint_locallyPathConnected
  have hUVpc : IsPathConnected (U ∩ V) := by
    rw [hinter]
    have hopen : IsOpen (((↑) '' (K₁ ∪ K₂))ᶜ : Set (OnePoint ℂ)) :=
      ((OnePoint.isClosed_image_coe).mpr ⟨hKcpt.isClosed, hKcpt⟩).isOpen_compl
    have hne : (((↑) '' (K₁ ∪ K₂))ᶜ : Set (OnePoint ℂ)).Nonempty :=
      ⟨∞, by rw [OnePoint.compl_image_coe]; exact Or.inr rfl⟩
    exact (hopen.isConnected_iff_isPathConnected).mp
      ⟨hne, isPreconnected_compl_image_coe hKcpt hWpre⟩
  -- van Kampen: the union is simply connected
  have hZ : IsSimplyConnected (U ∪ V) := isSimplyConnected_union hUo hVo hUsc hVsc hUVpc
  have hunion : U ∪ V = (({↑p, ↑q} : Set (OnePoint ℂ))ᶜ) := by
    rw [hUdef, hVdef, ← Set.compl_inter, ← Set.image_inter OnePoint.coe_injective, hint]
    congr 1
    exact Set.image_pair _ _ _
  rw [hunion] at hZ
  exact not_simplyConnected_compl_pair hpq hZ

end

end Work.Spike
