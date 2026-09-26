import Mathlib
import Submission.Work.Smooth.SphereJordan.LocalArc.Basic
import Submission.Work.Smooth.OneManifold.Plane.Basic

/-!
# Two arcs glued at a common endpoint are locally an arc

If `γ₁` is continuous and injective on the closed interval `[-a, 0]`, `γ₂` is continuous and
injective on `[-b, 0]`, the two images meet exactly in the common value `γ₁ 0 = γ₂ 0`, then the
union of the two half-open arcs `γ₁ '' (-a, 0]` and `γ₂ '' (-b, 0]` is a topological arc: it is
locally homeomorphic to `ℝ`.

The proof is elementary.  Glue the two parameter intervals at `0` into the open interval
`(-b, a)` and define the parametrisation

`G s = if 0 ≤ s then γ₁ (-s) else γ₂ s`,

so that `G '' (-b, a) = γ₁ '' (-a, 0] ∪ γ₂ '' (-b, 0]`.  On the compact interval `[-b, a]` the map
`G` is continuous (gluing two continuous maps on the closed halves) and injective (the hypothesis
that the two images meet only in `γ₁ 0`), hence — being a continuous bijection from a compact
space onto a Hausdorff space — it restricts to the desired homeomorphism of `(-b, a)` onto the
union (`exists_homeo_image` below).
-/

namespace Work.Drive.Mono

open Set

noncomputable section

/-- **A continuous injection on a compact set restricts to a homeomorphism onto the image of any
subset.**  If `J ⊆ K`, `K` is compact, `P` is continuous and injective on `K`, then `J ≃ₜ P '' J`.
The proof uses `Continuous.homeoOfEquivCompactToT2` for the compact piece `K` and transports the
inverse along the inclusion `P '' J ⊆ P '' K`. -/
private theorem exists_homeo_image {X : Type*} [TopologicalSpace X] [T2Space X]
    {J K : Set ℝ} (hJK : J ⊆ K) (hK : IsCompact K) {P : ℝ → X}
    (hcont : ContinuousOn P K) (hinj : Set.InjOn P K) :
    Nonempty (↥J ≃ₜ ↥(P '' J)) := by
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  let φ : ↥K → ↥(P '' K) := fun t => ⟨P (t : ℝ), (t : ℝ), t.2, rfl⟩
  have hφcont : Continuous φ :=
    Continuous.subtype_mk hcont.domRestrict fun t => ⟨(t : ℝ), t.2, rfl⟩
  have hφinj : Function.Injective φ :=
    fun s t hst => Subtype.ext (hinj s.2 t.2 (congrArg Subtype.val hst))
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨t, ht, hte⟩ := hy
    exact ⟨⟨t, ht⟩, Subtype.ext hte⟩
  let e : ↥K ≃ₜ ↥(P '' K) :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩) hφcont
  have he : ∀ t : ↥K, ((e t : ↥(P '' K)) : X) = P (t : ℝ) := fun t => rfl
  have he_symm : ∀ z : ↥(P '' K), P ((e.symm z : ↥K) : ℝ) = (z : X) := by
    intro z
    have h : ((e (e.symm z) : ↥(P '' K)) : X) = P ((e.symm z : ↥K) : ℝ) := he _
    rw [Homeomorph.apply_symm_apply] at h
    exact h.symm
  have hmemK : ∀ z : ↥(P '' J), (z : X) ∈ P '' K := by
    intro z
    rcases z.2 with ⟨t, ht, hte⟩
    exact ⟨t, hJK ht, hte⟩
  let mkK : ↥(P '' J) → ↥(P '' K) := fun z => ⟨(z : X), hmemK z⟩
  have hmemJ : ∀ z : ↥(P '' J), ((e.symm (mkK z) : ↥K) : ℝ) ∈ J := by
    intro z
    have h1 := he_symm (mkK z)
    rcases z.2 with ⟨t, ht, hte⟩
    have h2 : t = ((e.symm (mkK z) : ↥K) : ℝ) :=
      hinj (hJK ht) (e.symm (mkK z)).2 (by rw [hte, h1])
    rwa [← h2]
  refine ⟨{ toFun := fun s => ⟨P (s : ℝ), (s : ℝ), s.2, rfl⟩
            invFun := fun z => ⟨((e.symm (mkK z) : ↥K) : ℝ), hmemJ z⟩
            left_inv := ?_
            right_inv := ?_
            continuous_toFun := Continuous.subtype_mk (hcont.mono hJK).domRestrict _
            continuous_invFun := Continuous.subtype_mk
              (continuous_subtype_val.comp (e.symm.continuous.comp
                (Continuous.subtype_mk continuous_subtype_val hmemK))) _ }⟩
  · intro s
    apply Subtype.ext
    show ((((e.symm (mkK ⟨P (s : ℝ), (s : ℝ), s.2, rfl⟩) : ↥K)) : ℝ)) = (s : ℝ)
    have h1 : e ⟨(s : ℝ), hJK s.2⟩ = mkK ⟨P (s : ℝ), (s : ℝ), s.2, rfl⟩ :=
      Subtype.ext (he ⟨(s : ℝ), hJK s.2⟩)
    rw [← h1, Homeomorph.symm_apply_apply]
  · intro z
    apply Subtype.ext
    exact he_symm (mkK z)

/-- **Two arcs glued at a common endpoint form a topological arc.** -/
theorem two_arcs_glue {X : Type*} [TopologicalSpace X] [T2Space X]
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {γ₁ γ₂ : ℝ → X}
    (h₁ : ContinuousOn γ₁ (Set.Icc (-a) 0)) (h₂ : ContinuousOn γ₂ (Set.Icc (-b) 0))
    (hi₁ : Set.InjOn γ₁ (Set.Icc (-a) 0)) (hi₂ : Set.InjOn γ₂ (Set.Icc (-b) 0))
    (h0 : γ₁ 0 = γ₂ 0)
    (hdisj : γ₁ '' Set.Icc (-a) 0 ∩ γ₂ '' Set.Icc (-b) 0 = {γ₁ 0}) :
    Work.Smooth.SphereJordan.IsLocallyArc
      ↥(γ₁ '' Set.Ioc (-a) 0 ∪ γ₂ '' Set.Ioc (-b) 0) := by
  classical
  -- the glued parametrisation of the open interval `(-b, a)`
  let G : ℝ → X := fun s => if 0 ≤ s then γ₁ (-s) else γ₂ s
  have hGnn : ∀ s, 0 ≤ s → G s = γ₁ (-s) := fun s hs => by
    show (if 0 ≤ s then γ₁ (-s) else γ₂ s) = γ₁ (-s)
    rw [if_pos hs]
  have hGneg : ∀ s, s < 0 → G s = γ₂ s := fun s hs => by
    show (if 0 ≤ s then γ₁ (-s) else γ₂ s) = γ₂ s
    rw [if_neg (not_le.mpr hs)]
  -- continuity on the compact interval `[-b, a]`
  have hcont₂ : ContinuousOn G (Set.Icc (-b) 0) :=
    h₂.congr (fun s hs => by
      rcases lt_or_eq_of_le hs.2 with hlt | heq
      · exact hGneg s hlt
      · rw [heq, hGnn 0 le_rfl, neg_zero, h0])
  have hcont₁ : ContinuousOn G (Set.Icc (0:ℝ) a) :=
    (h₁.comp continuous_neg.continuousOn
      (fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩)).congr
      (fun s hs => hGnn s hs.1)
  have hIcc : Set.Icc (-b) 0 ∪ Set.Icc (0:ℝ) a = Set.Icc (-b) a :=
    Set.Icc_union_Icc_eq_Icc (by linarith) (by linarith)
  have hGcont : ContinuousOn G (Set.Icc (-b) a) := by
    rw [← hIcc]
    exact hcont₂.union_of_isClosed hcont₁ isClosed_Icc isClosed_Icc
  -- injectivity on `[-b, a]`
  have h0mem : (0 : ℝ) ∈ Set.Icc (-a) 0 := ⟨by linarith, le_rfl⟩
  have h0mem' : (0 : ℝ) ∈ Set.Icc (-b) 0 := ⟨by linarith, le_rfl⟩
  have hGinj : Set.InjOn G (Set.Icc (-b) a) := by
    intro s hs t ht hst
    by_cases hs0 : 0 ≤ s
    · by_cases ht0 : 0 ≤ t
      · rw [hGnn s hs0, hGnn t ht0] at hst
        have h1 : -s ∈ Set.Icc (-a) 0 := ⟨by linarith [hs.2], by linarith⟩
        have h2 : -t ∈ Set.Icc (-a) 0 := ⟨by linarith [ht.2], by linarith⟩
        linarith [hi₁ h1 h2 hst]
      · rw [hGnn s hs0, hGneg t (not_le.mp ht0)] at hst
        have h1 : -s ∈ Set.Icc (-a) 0 := ⟨by linarith [hs.2], by linarith⟩
        have h2 : t ∈ Set.Icc (-b) 0 := ⟨ht.1, le_of_lt (not_le.mp ht0)⟩
        have hmem : γ₁ (-s) ∈ γ₁ '' Set.Icc (-a) 0 ∩ γ₂ '' Set.Icc (-b) 0 :=
          ⟨⟨-s, h1, rfl⟩, ⟨t, h2, hst.symm⟩⟩
        rw [hdisj, Set.mem_singleton_iff] at hmem
        have h3 : -s = 0 := hi₁ h1 h0mem hmem
        rw [h3] at hst
        have h4 : γ₂ 0 = γ₂ t := by rw [← h0]; exact hst
        have h5 : (0 : ℝ) = t := hi₂ h0mem' h2 h4
        linarith
    · by_cases ht0 : 0 ≤ t
      · rw [hGneg s (not_le.mp hs0), hGnn t ht0] at hst
        have h1 : -t ∈ Set.Icc (-a) 0 := ⟨by linarith [ht.2], by linarith⟩
        have h2 : s ∈ Set.Icc (-b) 0 := ⟨hs.1, le_of_lt (not_le.mp hs0)⟩
        have hmem : γ₁ (-t) ∈ γ₁ '' Set.Icc (-a) 0 ∩ γ₂ '' Set.Icc (-b) 0 :=
          ⟨⟨-t, h1, rfl⟩, ⟨s, h2, hst⟩⟩
        rw [hdisj, Set.mem_singleton_iff] at hmem
        have h3 : -t = 0 := hi₁ h1 h0mem hmem
        rw [h3] at hst
        have h4 : γ₂ 0 = γ₂ s := by rw [← h0]; exact hst.symm
        have h5 : (0 : ℝ) = s := hi₂ h0mem' h2 h4
        linarith
      · rw [hGneg s (not_le.mp hs0), hGneg t (not_le.mp ht0)] at hst
        have h1 : s ∈ Set.Icc (-b) 0 := ⟨hs.1, le_of_lt (not_le.mp hs0)⟩
        have h2 : t ∈ Set.Icc (-b) 0 := ⟨ht.1, le_of_lt (not_le.mp ht0)⟩
        linarith [hi₂ h1 h2 hst]
  -- the image of the open interval is the union of the two half-open arcs
  have hGimage : G '' Set.Ioo (-b) a = γ₁ '' Set.Ioc (-a) 0 ∪ γ₂ '' Set.Ioc (-b) 0 := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      by_cases hs0 : 0 ≤ s
      · exact Or.inl ⟨-s, ⟨by linarith [hs.2], by linarith [hs0]⟩, (hGnn s hs0).symm⟩
      · exact Or.inr ⟨s, ⟨hs.1, le_of_lt (not_le.mp hs0)⟩, (hGneg s (not_le.mp hs0)).symm⟩
    · rintro (hy | hy)
      · obtain ⟨u, hu, rfl⟩ := hy
        refine ⟨-u, ⟨by linarith [hu.2], by linarith [hu.1]⟩, ?_⟩
        rw [hGnn (-u) (neg_nonneg.mpr hu.2)]
        ring_nf
      · obtain ⟨u, hu, rfl⟩ := hy
        rcases lt_or_eq_of_le hu.2 with hlt | heq
        · exact ⟨u, ⟨hu.1, by linarith [hu.2]⟩, hGneg u hlt⟩
        · exact ⟨0, ⟨by linarith, ha⟩, by rw [hGnn 0 le_rfl, neg_zero, h0, heq]⟩
  -- conclude
  obtain ⟨e⟩ := exists_homeo_image (X := X) (J := Set.Ioo (-b) a) (K := Set.Icc (-b) a)
    (fun s hs => ⟨le_of_lt hs.1, le_of_lt hs.2⟩) isCompact_Icc hGcont hGinj
  exact Work.Smooth.OneManifold.isLocallyArc_of_eq hGimage
    (Work.Smooth.OneManifold.isLocallyArc_of_homeomorph e
      (Work.Smooth.OneManifold.isLocallyArc_Ioo (-b) a))

end

end Work.Drive.Mono
