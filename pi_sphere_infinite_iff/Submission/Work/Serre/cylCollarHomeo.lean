import Mathlib
import Submission.Work.Serre.relCohPreimageDefs
import Submission.Work.Serre.C1Cyl

namespace Work.Serre

/-- **The collar of the mapping cylinder is the product `X × [0,1)`.**  For a continuous map
`q : C(X,Γ)`, the map `(x,t) ↦ cylMk q (Sum.inl (x,t))` is a homeomorphism from
`X × {t : unitInterval | (t : ℝ) < 1}` onto the collar `cylCollar q = {y : cyl q | (λ y : ℝ) < 1}`,
where `λ = cylLam q` is the collar coordinate introduced in
`Submission/Work/Serre/relCohPreimageDefs.lean` (`Work.Serre.cylLam`, `Work.Serre.cylCollar`).

The map is continuous and injective (no gluings happen below the top:
`Work.Serre.cylCollar_injective`), its image is exactly the collar
(`Work.Serre.exists_eq_cylMk_of_mem_cylCollar`), and it is a quotient map onto the collar because it
is the restriction of the quotient map `cylMk q` to the preimage of the *open* set `cylCollar q`
(`Topology.IsQuotientMap.restrictPreimage_isOpen`), which is the saturated set
`(X × {t | t < 1}) ⊕ ∅`; hence by `isHomeomorph_iff_isQuotientMap_injective` it is a homeomorphism
onto its image.  One also needs the easy identification of `(X × {t | t<1}) ⊕ ∅` with
`X × {t | t<1}`. -/
theorem cylCollarHomeo {Γ : Type} [TopologicalSpace Γ] {X : Type} [TopologicalSpace X]
    (q : C(X, Γ)) :
    ∃ e : X × ↥{t : unitInterval | (t : ℝ) < 1} ≃ₜ ↥(Work.Serre.cylCollar q),
      ∀ (x : X) (t : unitInterval) (ht : (t : ℝ) < 1),
        (e (x, ⟨t, ht⟩) : Work.Serre.cyl q) = Work.Serre.cylMk q (Sum.inl (x, t)) := by
  classical
  have hq : Topology.IsQuotientMap (cylMk q) := isQuotientMap_quotient_mk'
  let T : Set unitInterval := {t : unitInterval | (t : ℝ) < 1}
  have hTopen : IsOpen T := isOpen_lt continuous_subtype_val continuous_const
  let ι : X × ↥T → (X × unitInterval) ⊕ Γ := fun a => Sum.inl (a.1, (a.2 : unitInterval))
  let f : X × ↥T → ↥(cylCollar q) := fun a => ⟨cylMk q (ι a), a.2.2⟩
  have hιopen : IsOpenMap ι := by
    have hg : IsOpenMap (fun a : X × ↥T => (a.1, (a.2 : unitInterval))) :=
      IsOpenMap.id.prodMap hTopen.isOpenEmbedding_subtypeVal.isOpenMap
    have hcomp : IsOpenMap ((Sum.inl : X × unitInterval → (X × unitInterval) ⊕ Γ) ∘
        fun a : X × ↥T => (a.1, (a.2 : unitInterval))) :=
      (isOpenMap_inl (X := X × unitInterval) (Y := Γ)).comp hg
    exact hcomp
  have hquotOpen : ∀ V : Set (X × ↥T), IsOpen V → IsOpen (cylMk q '' (ι '' V)) := by
    intro V hV
    have hιV : IsOpen (ι '' V) := hιopen V hV
    have hsat : cylMk q ⁻¹' (cylMk q '' (ι '' V)) = ι '' V := by
      ext z
      constructor
      · intro hz
        obtain ⟨z', hz', hzz'⟩ := hz
        obtain ⟨a, ha, rfl⟩ := hz'
        have ht1 : (a.2 : unitInterval) ≠ 1 := by
          intro h1
          have h2 : ((a.2 : unitInterval) : ℝ) < 1 := a.2.2
          rw [h1] at h2
          exact lt_irrefl 1 h2
        have h3 : z = Sum.inl (a.1, (a.2 : unitInterval)) :=
          (eqvGen_inl_iff q ht1 (Quotient.exact hzz')).mp rfl
        rw [h3]
        exact ⟨a, ha, rfl⟩
      · intro hz
        exact ⟨z, hz, rfl⟩
    exact (hq.isOpen_preimage (s := cylMk q '' (ι '' V))).mp (by rw [hsat]; exact hιV)
  have hf_image : ∀ V : Set (X × ↥T),
      f '' V = Subtype.val ⁻¹' (cylMk q '' (ι '' V)) := by
    intro V
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨ι a, ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      obtain ⟨a, ha, haz⟩ := hz
      refine ⟨a, ha, Subtype.ext ?_⟩
      rw [← haz] at hzy
      exact hzy
  have hfopen : IsOpenMap f := by
    intro V hV
    rw [hf_image V]
    exact (hquotOpen V hV).preimage continuous_subtype_val
  have hfcont : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact hq.continuous.comp (continuous_inl.comp
      (continuous_id.prodMap continuous_subtype_val))
  have hex : ∀ y : ↥(cylCollar q),
      ∃ p : X × ↥T, (y : cyl q) = cylMk q (ι p) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, t, ht, hyt⟩ := exists_eq_cylMk_of_mem_cylCollar q hy
    exact ⟨(x, ⟨t, ht⟩), hyt⟩
  let Ψ : ↥(cylCollar q) → X × ↥T := fun y => (hex y).choose
  have hΨ : ∀ y : ↥(cylCollar q), (y : cyl q) = cylMk q (ι (Ψ y)) :=
    fun y => (hex y).choose_spec
  have hleft : Function.LeftInverse Ψ f := by
    intro a
    have h2 : cylMk q (ι a) = cylMk q (ι (Ψ (f a))) := by
      have h3 : (f a : cyl q) = cylMk q (ι (Ψ (f a))) := hΨ (f a)
      simpa using h3
    obtain ⟨hx, ht⟩ := cylCollar_injective q (x := a.1) (x' := (Ψ (f a)).1)
      (t := (a.2 : unitInterval)) (t' := ((Ψ (f a)).2 : unitInterval)) a.2.2 h2
    exact (Prod.ext hx (Subtype.ext ht)).symm
  have hright : Function.RightInverse Ψ f := by
    intro y
    refine Subtype.ext ?_
    exact (hΨ y).symm
  have hΨcont : Continuous Ψ := by
    rw [continuous_def]
    intro V hV
    have hpre : Ψ ⁻¹' V = Subtype.val ⁻¹' (cylMk q '' (ι '' V)) := by
      ext y
      constructor
      · intro hy
        exact ⟨ι (Ψ y), ⟨Ψ y, hy, rfl⟩, (hΨ y).symm⟩
      · rintro ⟨z, hz, hzy⟩
        obtain ⟨a, ha, haz⟩ := hz
        have hfay : f a = y := by
          refine Subtype.ext ?_
          rw [← haz] at hzy
          exact hzy
        have hthis : Ψ y = a := by
          rw [← hfay]
          exact hleft a
        change Ψ y ∈ V
        rw [hthis]
        exact ha
    rw [hpre]
    exact (hquotOpen V hV).preimage continuous_subtype_val
  let e : X × ↥T ≃ₜ ↥(cylCollar q) :=
    { toFun := f, invFun := Ψ, left_inv := hleft, right_inv := hright,
      continuous_toFun := hfcont, continuous_invFun := hΨcont }
  exact ⟨e, fun x t ht => rfl⟩


end Work.Serre
