import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Projection.compact_embedding
import Submission.Work.Drive.N2.FieldData

/-! Guidance from the project lead (the requester):

# The level flow over a critical-point-free interval (assembly)

This file assembles `Work.Drive.N2.hasLevelFlow_of_noCritical` from the bricks
`exists_smooth_retraction_manifold`, `contDiff_flow_joint`, `eq_of_deriv_eq_one`,
`retraction_fixed_of_isIntegralCurve`, `exists_contDiff_bump_isCompact`, `contDiff_levelField`,
`levelField_spec`, `isIntegralCurve_mem_tsupport_or_eq`, `auxField_retraction_ne_zero`.  While
those are in flight the assembly is stated with them as explicit hypotheses
(`hasLevelFlow_of_hypotheses`), so that the argument can be developed and checked in parallel.
-/

open scoped Manifold ContDiff Topology
open Set Function
open Work.Drive.Morse

namespace Work.Drive.N2

set_option autoImplicit false

universe u


theorem hasLevelFlow_of_hypotheses {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (a b : ℝ)
    (hcrit : ∀ x, f x ∈ Set.Icc a b → ¬ IsCritical f x)
    (hretr : ∀ {n N : ℕ} {M' : Type u} [TopologicalSpace M']
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M']
      [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M']
      [T2Space M'] [CompactSpace M'] [Nonempty M']
      (e : M' → EuclideanSpace ℝ (Fin N))
      (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) ((⊤ : ℕ∞) : WithTop ℕ∞) e)
      (hinj : Function.Injective e)
      (himm : ∀ x, Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) e x)),
      ∃ (U : Set (EuclideanSpace ℝ (Fin N))) (π : EuclideanSpace ℝ (Fin N) → M'),
        IsOpen U ∧ Set.range e ⊆ U ∧
        ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) π U ∧
        (∀ x, π (e x) = x) ∧
        (∀ y ∈ U, dist y (e (π y)) = Metric.infDist y (Set.range e)) ∧
        (∀ y ∈ U, y - e (π y) ∈ (fderiv ℝ (fun z => e (π z)) y).rangeᗮ))
    (hflowSmooth : ∀ (E : EuclideanSpace ℝ (Fin (2 * 2 + 1)) → EuclideanSpace ℝ (Fin (2 * 2 + 1)))
      (G : EuclideanSpace ℝ (Fin (2 * 2 + 1)) → ℝ) (χ : EuclideanSpace ℝ (Fin (2 * 2 + 1)) → ℝ)
      (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E) (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G)
      (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hcχ : HasCompactSupport χ)
      (hsupp : tsupport χ ⊆ {z | auxField E G z ≠ 0}),
      ∃ FL : ℝ → EuclideanSpace ℝ (Fin (2 * 2 + 1)) → EuclideanSpace ℝ (Fin (2 * 2 + 1)),
        (∀ p, FL 0 p = p) ∧ (∀ s t p, FL (s + t) p = FL s (FL t p)) ∧
        (∀ p, IsIntegralCurve (fun s => FL s p) (fun _ z => levelField E G χ z)) ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × EuclideanSpace ℝ (Fin (2 * 2 + 1)) => FL p.1 p.2))
    (hcmp : ∀ {v : ℝ → ℝ}, Continuous v → ∀ (a0 b0 : ℝ), v 0 ∈ Set.Icc a0 b0 →
      (∀ t, v t ∈ Set.Icc a0 b0 → HasDerivAt v 1 t) → ∀ t, v 0 + t ∈ Set.Icc a0 b0 → v t = v 0 + t)
    (hfix : ∀ (E Y : EuclideanSpace ℝ (Fin (2 * 2 + 1)) → EuclideanSpace ℝ (Fin (2 * 2 + 1)))
      (γ : ℝ → EuclideanSpace ℝ (Fin (2 * 2 + 1)))
      (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E)
      (hY : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Y) (hc : HasCompactSupport Y)
      (hYrange : ∀ y, Y y ∈ (fderiv ℝ E y).range)
      (horth : ∀ y, y ∈ tsupport Y → y - E y ∈ (fderiv ℝ E y).rangeᗮ)
      (hγ : IsIntegralCurve γ (fun _ z => Y z)) (h0 : E (γ 0) = γ 0),
      ∀ t, E (γ t) = γ t)
    (hbump : ∀ {K O : Set (EuclideanSpace ℝ (Fin (2 * 2 + 1)))}, IsCompact K → IsOpen O → K ⊆ O →
      ∃ χ : EuclideanSpace ℝ (Fin (2 * 2 + 1)) → ℝ,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ O ∧
          K ⊆ interior {z | χ z = 1})
    (hfield : ∀ (E : EuclideanSpace ℝ (Fin (2 * 2 + 1)) → EuclideanSpace ℝ (Fin (2 * 2 + 1)))
      (G : EuclideanSpace ℝ (Fin (2 * 2 + 1)) → ℝ) (χ : EuclideanSpace ℝ (Fin (2 * 2 + 1)) → ℝ)
      (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E) (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G)
      (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hcχ : HasCompactSupport χ)
      (hsupp : tsupport χ ⊆ {z | auxField E G z ≠ 0}),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (levelField E G χ) ∧ HasCompactSupport (levelField E G χ))
    (hspec : ∀ (E : EuclideanSpace ℝ (Fin (2 * 2 + 1)) → EuclideanSpace ℝ (Fin (2 * 2 + 1)))
      (G : EuclideanSpace ℝ (Fin (2 * 2 + 1)) → ℝ) (χ : EuclideanSpace ℝ (Fin (2 * 2 + 1)) → ℝ)
      (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E) (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G),
      (∀ z, auxField E G z ≠ 0 → (fderiv ℝ G z) (levelField E G χ z) = χ z) ∧
        (∀ z, levelField E G χ z ∈ (fderiv ℝ E z).range))
    (hts : ∀ (Y : EuclideanSpace ℝ (Fin (2 * 2 + 1)) → EuclideanSpace ℝ (Fin (2 * 2 + 1)))
      (hY : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Y) (hc : HasCompactSupport Y)
      (γ : ℝ → EuclideanSpace ℝ (Fin (2 * 2 + 1))) (hγ : IsIntegralCurve γ (fun _ z => Y z)),
      ∀ t, γ t ∈ tsupport Y ∨ γ t = γ 0)
    (haux : ∀ {n N : ℕ} {M' : Type u} [TopologicalSpace M']
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M']
      [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M']
      (e : M' → EuclideanSpace ℝ (Fin N))
      (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) ((⊤ : ℕ∞) : WithTop ℕ∞) e)
      (himm : ∀ x, Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) e x))
      (U : Set (EuclideanSpace ℝ (Fin N))) (hUopen : IsOpen U) (π : EuclideanSpace ℝ (Fin N) → M')
      (hπsm : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) π U)
      (hπe : ∀ x, π (e x) = x) (x₀ : M') (hU : e x₀ ∈ U) (g : M' → ℝ)
      (hg : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) g)
      (hmf : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ ℝ) g x₀ ≠ 0),
      auxField (fun z => e (π z)) (fun z => g (π z)) (e x₀) ≠ 0)
    : HasLevelFlow f a b := by
  by_cases hne : ∃ x : M, f x ∈ Set.Icc a b
  · -- nontrivial case: some point of `M` has value in `[a, b]`
    obtain ⟨x₀, hx₀⟩ := hne
    haveI : Nonempty M := ⟨x₀⟩
    -- the weak Whitney embedding of the surface into `ℝ⁵`
    obtain ⟨e, he, hemb, himm⟩ := Work.Projection.exists_embedding_euclidean_of_compact 2 (M := M)
    -- the nearest-point retraction of a tubular neighbourhood, as a map into `M`
    obtain ⟨U, π, hUopen, hrange, hπsm, hπe, hπdist, hπorth⟩ :=
      hretr (n := 2) (N := 2 * 2 + 1) (M' := M) e he hemb.injective himm
    -- the ambient maps `E = e ∘ π` and `G = f ∘ π`
    let E : EuclideanSpace ℝ (Fin (2 * 2 + 1)) → EuclideanSpace ℝ (Fin (2 * 2 + 1)) := fun z => e (π z)
    let G : EuclideanSpace ℝ (Fin (2 * 2 + 1)) → ℝ := fun z => f (π z)
    have hEonU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E U := by
      have h1 : ContMDiffOn (𝓡 (2 * 2 + 1)) (𝓡 (2 * 2 + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) E U :=
        (he.contMDiffOn (s := Set.univ)).comp hπsm (fun z _ => Set.mem_univ (π z))
      exact (contMDiffOn_iff_contDiffOn).mp h1
    have hGonU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G U := by
      have h1 : ContMDiffOn (𝓡 (2 * 2 + 1)) (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) G U :=
        (hf.contMDiffOn (s := Set.univ)).comp hπsm (fun z _ => Set.mem_univ (π z))
      exact (contMDiffOn_iff_contDiffOn).mp h1
    -- the compact set `K = e '' f⁻¹[a,b]`
    have hKc : IsCompact (e '' (f ⁻¹' (Set.Icc a b))) :=
      (isClosed_Icc.preimage hf.continuous).isCompact.image he.continuous
    have hKU : e '' (f ⁻¹' (Set.Icc a b)) ⊆ U := by
      rintro z ⟨x, -, rfl⟩
      exact hrange ⟨x, rfl⟩
    have hKgood : e '' (f ⁻¹' (Set.Icc a b)) ⊆ {z | auxField E G z ≠ 0} := by
      rintro z ⟨x, hx, rfl⟩
      exact haux e he himm U hUopen π hπsm hπe x (hrange ⟨x, rfl⟩) f hf (hcrit x hx)
    -- a cutoff which is `1` near the whole image of `e` and supported in `U`
    obtain ⟨χ₀, hχ₀diff, hcχ₀, hχ₀supp, hχ₀int⟩ := hbump (isCompact_range he.continuous) hUopen hrange
    -- the damped ambient maps, smooth everywhere
    let Ê : EuclideanSpace ℝ (Fin (2 * 2 + 1)) → EuclideanSpace ℝ (Fin (2 * 2 + 1)) := fun z => χ₀ z • E z
    let Ĝ : EuclideanSpace ℝ (Fin (2 * 2 + 1)) → ℝ := fun z => χ₀ z • G z
    have hÊdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ê := by
      rw [contDiff_iff_contDiffAt]
      intro z
      by_cases hz : z ∈ U
      · exact hχ₀diff.contDiffAt.smul (hEonU.contDiffAt (hUopen.mem_nhds hz))
      · have hzt : z ∉ tsupport χ₀ := fun h => hz (hχ₀supp h)
        have h0 : ∀ᶠ w in 𝓝 z, χ₀ w = 0 :=
          Filter.mem_of_superset ((isClosed_tsupport χ₀).isOpen_compl.mem_nhds hzt)
            (fun w hw => Function.notMem_support.mp (fun h => hw (subset_tsupport χ₀ h)))
        have hev : Ê =ᶠ[𝓝 z] fun _ => (0 : EuclideanSpace ℝ (Fin (2 * 2 + 1))) := by
          filter_upwards [h0] with w hw
          rw [show Ê w = χ₀ w • E w from rfl, hw, zero_smul]
        exact contDiffAt_const.congr_of_eventuallyEq hev
    have hĜdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ĝ := by
      rw [contDiff_iff_contDiffAt]
      intro z
      by_cases hz : z ∈ U
      · exact hχ₀diff.contDiffAt.smul (hGonU.contDiffAt (hUopen.mem_nhds hz))
      · have hzt : z ∉ tsupport χ₀ := fun h => hz (hχ₀supp h)
        have h0 : ∀ᶠ w in 𝓝 z, χ₀ w = 0 :=
          Filter.mem_of_superset ((isClosed_tsupport χ₀).isOpen_compl.mem_nhds hzt)
            (fun w hw => Function.notMem_support.mp (fun h => hw (subset_tsupport χ₀ h)))
        have hev : Ĝ =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
          filter_upwards [h0] with w hw
          rw [show Ĝ w = χ₀ w • G w from rfl, hw, zero_smul]
        exact contDiffAt_const.congr_of_eventuallyEq hev
    -- the auxiliary field is continuous, so its non-vanishing set is open
    have hauxcont : Continuous (auxField Ê Ĝ) := by
      have h1 : Continuous fun z => (fderiv ℝ Ê z).adjoint :=
        (ContinuousLinearMap.adjoint (𝕜 := ℝ)).continuous.comp
          (hÊdiff.continuous_fderiv (by norm_num))
      have h2 : Continuous (grad Ĝ) :=
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (2 * 2 + 1)))).symm.continuous.comp
          (hĜdiff.continuous_fderiv (by norm_num))
      exact h1.clm_apply h2
    -- `χ₀ = 1` in a neighbourhood of each point of the image
    have hχ₀_one : ∀ z ∈ Set.range e, ∀ᶠ w in 𝓝 z, χ₀ w = 1 := by
      rintro z hz
      exact Filter.mem_of_superset (isOpen_interior.mem_nhds (hχ₀int hz)) interior_subset
    -- the set on which the field is built
    have hOgopen : IsOpen (U ∩ interior {x | χ₀ x = 1} ∩ {z | auxField Ê Ĝ z ≠ 0}) :=
      (hUopen.inter isOpen_interior).inter (isOpen_compl_singleton.preimage hauxcont)
    have hKOg : e '' (f ⁻¹' (Set.Icc a b)) ⊆ U ∩ interior {x | χ₀ x = 1} ∩ {z | auxField Ê Ĝ z ≠ 0} := by
      rintro z ⟨x, hx, rfl⟩
      have hmem : e x ∈ Set.range e := ⟨x, rfl⟩
      have hev : ∀ᶠ w in 𝓝 (e x), χ₀ w = 1 := hχ₀_one (e x) hmem
      have hÊev : Ê =ᶠ[𝓝 (e x)] E := by
        filter_upwards [hev] with w hw
        simp [Ê, hw]
      have hĜev : Ĝ =ᶠ[𝓝 (e x)] G := by
        filter_upwards [hev] with w hw
        simp [Ĝ, hw]
      have haux_eq : auxField Ê Ĝ (e x) = auxField E G (e x) := by
        simp only [auxField, grad, hÊev.fderiv_eq, hĜev.fderiv_eq]
      exact ⟨⟨hrange hmem, hχ₀int hmem⟩, by
        show auxField Ê Ĝ (e x) ≠ 0
        rw [haux_eq]
        exact hKgood ⟨x, hx, rfl⟩⟩
    -- the cutoff of the field
    obtain ⟨χ₁, hχ₁diff, hcχ₁, hχ₁supp, hχ₁int⟩ := hbump hKc hOgopen hKOg
    -- `χ₀ = 1` near every point of the support of `χ₁`
    have hχ₀_one' : ∀ z ∈ tsupport χ₁, ∀ᶠ w in 𝓝 z, χ₀ w = 1 := fun z hz =>
      Filter.mem_of_superset (isOpen_interior.mem_nhds (hχ₁supp hz).1.2) interior_subset
    have hÊeq : ∀ z ∈ tsupport χ₁, Ê =ᶠ[𝓝 z] E := by
      intro z hz
      filter_upwards [hχ₀_one' z hz] with w hw
      simp [Ê, hw]
    have hĜeq : ∀ z ∈ tsupport χ₁, Ĝ =ᶠ[𝓝 z] G := by
      intro z hz
      filter_upwards [hχ₀_one' z hz] with w hw
      simp [Ĝ, hw]
    -- the level field
    have htsχ₁ : tsupport χ₁ ⊆ {z | auxField Ê Ĝ z ≠ 0} := fun z hz => (hχ₁supp hz).2
    let Y : EuclideanSpace ℝ (Fin (2 * 2 + 1)) → EuclideanSpace ℝ (Fin (2 * 2 + 1)) := levelField Ê Ĝ χ₁
    have hYdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Y := by
      have := (hfield Ê Ĝ χ₁ hÊdiff hĜdiff hχ₁diff hcχ₁ htsχ₁).1
      simpa [Y] using this
    have hcY : HasCompactSupport Y := by
      have := (hfield Ê Ĝ χ₁ hÊdiff hĜdiff hχ₁diff hcχ₁ htsχ₁).2
      simpa [Y] using this
    have hYlevel : ∀ z, auxField Ê Ĝ z ≠ 0 → (fderiv ℝ Ĝ z) (Y z) = χ₁ z := by
      intro z hz
      exact (hspec Ê Ĝ χ₁ hÊdiff hĜdiff).1 z hz
    have hYrange : ∀ z, Y z ∈ (fderiv ℝ Ê z).range := fun z =>
      (hspec Ê Ĝ χ₁ hÊdiff hĜdiff).2 z
    -- the flow of the level field, jointly smooth
    obtain ⟨FL, hFL0, hFLsem, hFLcurve, hFLjoint⟩ :=
      hflowSmooth Ê Ĝ χ₁ hÊdiff hĜdiff hχ₁diff hcχ₁ htsχ₁
    have hFLcurveY : ∀ p, IsIntegralCurve (fun s : ℝ => FL s p) (fun _ z => Y z) := hFLcurve
    -- the trajectory stays in the image of `e`
    have hsubset : tsupport Y ⊆ tsupport χ₁ := by
      refine closure_mono fun w hw => ?_
      simp only [Function.mem_support, ne_eq] at hw ⊢
      intro h0
      exact hw (by simp [Y, levelField, h0])
    have horth : ∀ y, y ∈ tsupport Y → y - Ê y ∈ (fderiv ℝ Ê y).rangeᗮ := by
      intro y hy
      have hy₁ : y ∈ tsupport χ₁ := hsubset hy
      have hEU : y ∈ U := (hχ₁supp hy₁).1.1
      have hev := hÊeq y hy₁
      rw [hev.fderiv_eq, hev.eq_of_nhds]
      exact hπorth y hEU
    have hinv : ∀ x : M, ∀ t : ℝ, FL t (e x) = e (π (FL t (e x))) := by
      intro x t
      have hγ : IsIntegralCurve (fun t : ℝ => FL t (e x)) (fun _ z => Y z) := hFLcurve (e x)
      have hex : χ₀ (e x) = 1 := by
        have h := hχ₀int (Set.mem_range_self x)
        exact interior_subset (s := {z | χ₀ z = 1}) h
      have h0 : Ê (FL 0 (e x)) = FL 0 (e x) := by
        rw [hFL0, show Ê (e x) = χ₀ (e x) • E (e x) from rfl, hex, one_smul]
        show e (π (e x)) = e x
        rw [hπe x]
      have hfix' := hfix Ê Y (fun t : ℝ => FL t (e x)) hÊdiff hYdiff hcY hYrange horth hγ h0 t
      have hχ₀t : χ₀ (FL t (e x)) = 1 := by
        rcases hts Y hYdiff hcY (fun t : ℝ => FL t (e x)) hγ t with hmem | heq
        · exact interior_subset (s := {z | χ₀ z = 1}) (hχ₁supp (hsubset hmem)).1.2
        · rw [heq, hFL0]; exact hex
      calc FL t (e x) = Ê (FL t (e x)) := hfix'.symm
        _ = χ₀ (FL t (e x)) • E (FL t (e x)) := rfl
        _ = E (FL t (e x)) := by rw [hχ₀t, one_smul]
        _ = e (π (FL t (e x))) := rfl
    -- the level property
    have hlevel : ∀ (x : M) (t : ℝ), f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b →
        f (π (FL t (e x))) = f x + t := by
      intro x t hx ht
      have hγ : IsIntegralCurve (fun t : ℝ => FL t (e x)) (fun _ z => Y z) := hFLcurve (e x)
      have hχ₀t : ∀ t : ℝ, χ₀ (FL t (e x)) = 1 := by
        intro t
        rcases hts Y hYdiff hcY (fun t : ℝ => FL t (e x)) hγ t with hmem | heq
        · exact interior_subset (s := {z | χ₀ z = 1}) (hχ₁supp (hsubset hmem)).1.2
        · rw [heq, hFL0]
          exact interior_subset (s := {z | χ₀ z = 1}) (hχ₀int (Set.mem_range_self x))
      set u : ℝ → ℝ := fun s => Ĝ (FL s (e x)) with hu
      have huval : ∀ s : ℝ, u s = f (π (FL s (e x))) := by
        intro s
        simp only [hu, Ĝ, G, hχ₀t s, one_smul]
      have hu0 : u 0 ∈ Set.Icc a b := by
        rw [huval 0]
        simpa [hFL0, hπe x] using hx
      have huderiv : ∀ s : ℝ, u s ∈ Set.Icc a b → HasDerivAt u 1 s := by
        intro s hs
        rw [huval s] at hs
        have hKmem : e (π (FL s (e x))) ∈ e '' (f ⁻¹' (Set.Icc a b)) :=
          ⟨π (FL s (e x)), hs, rfl⟩
        have hγs : FL s (e x) = e (π (FL s (e x))) := hinv x s
        have hχ₁'' : χ₁ (e (π (FL s (e x)))) = 1 :=
          interior_subset (s := {z | χ₁ z = 1}) (hχ₁int hKmem)
        have hχ₁' : χ₁ (FL s (e x)) = 1 := by rw [hγs]; exact hχ₁''
        have hinK : FL s (e x) ∈ tsupport χ₁ := by
          rw [hγs]
          refine subset_tsupport χ₁ ?_
          show χ₁ (e (π (FL s (e x)))) ≠ 0
          rw [hχ₁'']
          exact one_ne_zero
        have hauxs : auxField Ê Ĝ (FL s (e x)) ≠ 0 := (hχ₁supp hinK).2
        have h1 : HasDerivAt u ((fderiv ℝ Ĝ (FL s (e x))) (Y (FL s (e x)))) s := by
          have hd : DifferentiableAt ℝ Ĝ (FL s (e x)) :=
            (hĜdiff.differentiable (by simp)).differentiableAt
          have h := hd.hasFDerivAt.comp_hasDerivAt s (hγ s)
          simpa [hu, Function.comp_def] using h
        rw [hYlevel _ hauxs, hχ₁'] at h1
        exact h1
      have hcont : Continuous u := hĜdiff.continuous.comp hγ.continuous
      have hu0_eq : u 0 = f x := by rw [huval 0, hFL0, hπe x]
      have hres := hcmp hcont a b hu0 huderiv t (by rwa [← hu0_eq] at ht)
      rw [hu0_eq] at hres
      rw [huval t] at hres
      exact hres
    -- the flow law
    have hflowlaw : ∀ (x : M) (s t : ℝ), f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b →
        f x + t + s ∈ Set.Icc a b → π (FL s (e (π (FL t (e x))))) = π (FL (s + t) (e x)) := by
      intro x s t hx ht hts
      rw [← hinv x t, hFLsem]
    -- conclusion
    refine ⟨fun p : ℝ × M => π (FL p.1 (e p.2)), ?_, ?_, ?_, ?_⟩
    · have hq : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 (2 * 2 + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × M => FL p.1 (e p.2)) := by
        have h1 : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 2))
            ((modelWithCornersSelf ℝ ℝ).prod (𝓡 (2 * 2 + 1))) ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun p : ℝ × M => (p.1, e p.2)) :=
          ContMDiff.prodMk contMDiff_fst (he.comp contMDiff_snd)
        have h2 : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod (𝓡 (2 * 2 + 1)))
            (𝓡 (2 * 2 + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun q : ℝ × EuclideanSpace ℝ (Fin (2 * 2 + 1)) => FL q.1 q.2) := by
          rw [show (modelWithCornersSelf ℝ ℝ).prod (𝓡 (2 * 2 + 1))
              = 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin (2 * 2 + 1))) from
            (modelWithCornersSelf_prod (F := EuclideanSpace ℝ (Fin (2 * 2 + 1)))).symm]
          rw [show prodChartedSpace ℝ ℝ (EuclideanSpace ℝ (Fin (2 * 2 + 1)))
                (EuclideanSpace ℝ (Fin (2 * 2 + 1)))
              = chartedSpaceSelf (ℝ × EuclideanSpace ℝ (Fin (2 * 2 + 1))) from
            chartedSpaceSelf_prod]
          exact (contMDiff_iff_contDiff).mpr hFLjoint
        exact h2.comp h1
      have hcomp : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × M => π (FL p.1 (e p.2))) Set.univ :=
        hπsm.comp (hq.contMDiffOn (s := Set.univ)) (fun p _ => by
          show FL p.1 (e p.2) ∈ U
          rw [hinv p.2 p.1]
          exact hrange (Set.mem_range_self _))
      exact contMDiffOn_univ.mp hcomp
    · intro x
      show π (FL 0 (e x)) = x
      rw [hFL0, hπe x]
    · intro x t hx ht
      exact hlevel x t hx ht
    · intro x s t hx ht hts
      exact hflowlaw x s t hx ht hts

  · -- trivial case: no point of `M` has value in `[a, b]`
    refine ⟨fun p : ℝ × M => p.2, contMDiff_snd, fun x => rfl, ?_, ?_⟩
    · intro x t hx _
      exact absurd ⟨x, hx⟩ hne
    · intro x s t hx _ _
      exact absurd ⟨x, hx⟩ hne


end Work.Drive.N2
