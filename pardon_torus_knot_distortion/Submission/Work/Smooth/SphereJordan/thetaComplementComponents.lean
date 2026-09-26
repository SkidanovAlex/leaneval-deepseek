import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.planeArcComponentsCore
import Submission.Work.Smooth.SphereJordan.thetaSpansAux
import Submission.Work.Smooth.SphereJordan.Transport

/-!
# The two complementary components of a theta graph on the Riemann sphere

Two disjoint embedded discs `D₁`, `D₂` on the Riemann sphere joined by two disjoint arcs `α`, `β`
whose interiors avoid the discs: the complement of the union is the disjoint union of two non-empty
open preconnected sets.

The proof reduces to the plane (along a Möbius chart moving a point off the graph to `∞`): the
graph pulled back to the plane is a theta graph of two disjoint embedded discs joined by two
disjoint arcs, whose complement has exactly two components by
`Work.Smooth.SphereJordan.planeArcComponentsCore` (the *at most two components* half being
`Work.Smooth.SphereJordan.thetaPlane_not_preconnected` inside it).  The component containing the far
region receives `∞` back under the chart.
-/

set_option maxHeartbeats 4000000

namespace Work.Smooth.SphereJordan

noncomputable section

open Set

/-! ## The planar two-component statement -/

/-- **The plane theta graph has exactly two complementary components.** -/
def PlaneThetaTwoComponents : Prop :=
  ∀ {D₁ D₂ : Set ℂ}
    (hD₁ : ∃ f : C(Disc, ℂ), Function.Injective f ∧ Set.range f = D₁)
    (hD₂ : ∃ g : C(Disc, ℂ), Function.Injective g ∧ Set.range g = D₂)
    (hdisj : Disjoint D₁ D₂)
    (α β : C(Set.Icc (0 : ℝ) 1, ℂ)) (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hα₀ : α ⟨0, by norm_num⟩ ∈ D₁) (hα₁ : α ⟨1, by norm_num⟩ ∈ D₂)
    (hβ₀ : β ⟨0, by norm_num⟩ ∈ D₁) (hβ₁ : β ⟨1, by norm_num⟩ ∈ D₂)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂)
    (hβint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ D₁ ∪ D₂)
    (hsep : ∀ s t : Set.Icc (0 : ℝ) 1, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      α s ≠ β t)
    (hαβ₀ : α ⟨0, by norm_num⟩ ≠ β ⟨0, by norm_num⟩)
    (hαβ₁ : α ⟨1, by norm_num⟩ ≠ β ⟨1, by norm_num⟩)
    (h : PlaneHypothesis),
    ∃ P₁ P₂ : Set ℂ, P₁.Nonempty ∧ P₂.Nonempty ∧ IsOpen P₁ ∧ IsOpen P₂ ∧ Disjoint P₁ P₂ ∧
      P₁ ∪ P₂ = (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ ∧
      IsPreconnected P₁ ∧ IsPreconnected P₂

theorem planeThetaComponentsOf : PlaneThetaTwoComponents := by
  intro D₁ D₂ hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep hαβ₀ hαβ₁ h
  exact planeArcComponentsCore h hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint
    hsep hαβ₀ hαβ₁

/-! ## Adjoining `∞` to the far piece -/

/-- **The transport step.**  Given a homeomorphism `Φ` of the sphere, a closed set `X` with
`∞ ∉ X`, two complementary plane pieces `P, Q` whose union with `∞` is the sphere complement of
`Φ⁻¹ '' X`, and with `P` containing everything far out, the two sphere pieces
`Φ '' (P ∪ {∞})` and `Φ '' Q` realise the complement of `X` as two non-empty open preconnected
sets. -/
theorem sphereTwoPiecesOfPlanePair (Φ : RiemannSphere ≃ₜ RiemannSphere) {X : Set RiemannSphere}
    {R : ℝ} {P Q : Set ℂ}
    (hPo : IsOpen P) (hQo : IsOpen Q) (hd : Disjoint P Q)
    (hPc : IsPreconnected P) (hQc : IsPreconnected Q) (hQne : Q.Nonempty)
    (hX : (↑) '' (P ∪ Q) ∪ {infty} = (Φ.symm '' X)ᶜ)
    (hfar : ∀ z : ℂ, R < ‖z‖ → z ∈ P) :
    ∃ P₁ P₂ : Set RiemannSphere,
      P₁.Nonempty ∧ P₂.Nonempty ∧ IsOpen P₁ ∧ IsOpen P₂ ∧ Disjoint P₁ P₂ ∧
      P₁ ∪ P₂ = Set.univ \ X ∧ IsPreconnected P₁ ∧ IsPreconnected P₂ := by
  obtain ⟨hO₁, hO₂, hC₁, hC₂, hD, hCl⟩ := spherePairOfPlanePair hPo hQo hd hPc hQc hfar
  refine ⟨Φ '' ((↑) '' P ∪ {infty}), Φ '' ((↑) '' Q), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨Φ infty, infty, Or.inr rfl, rfl⟩
  · obtain ⟨q, hq⟩ := hQne
    exact ⟨Φ ↑q, ↑q, ⟨q, hq, rfl⟩, rfl⟩
  · exact Φ.isOpenMap _ hO₁
  · exact Φ.isOpenMap _ hO₂
  · rw [Set.disjoint_left]
    rintro x ⟨y, hy, rfl⟩ ⟨z, hz, hzy⟩
    exact (Set.disjoint_left.mp hD hy) (Φ.injective hzy ▸ hz)
  · have h1 : Φ '' ((↑) '' P ∪ {infty}) ∪ Φ '' ((↑) '' Q)
        = Φ '' ((↑) '' (P ∪ Q) ∪ {infty}) := by
      rw [← Set.image_union]
      congr 1
      rw [Set.image_union]
      ext x
      simp only [Set.mem_union, Set.mem_image, Set.mem_singleton_iff]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
        · exact Or.inl (Or.inr h)
      · rintro (h | h)
        · rcases h with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
        · exact Or.inl (Or.inr h)
    rw [h1, hX, Set.image_compl_eq Φ.bijective, Set.image_image]
    simp [Set.compl_eq_univ_sdiff]
  · exact hC₁.image Φ Φ.continuous.continuousOn
  · exact hC₂.image Φ Φ.continuous.continuousOn

/-! ## From the plane to the sphere -/

/-- **The sphere statement from the plane statement.**  A Möbius chart moves a point `p` off the
theta graph to `∞`; the graph pulled back to the plane has two complementary components by
`PlaneThetaTwoComponents`; the piece which contains the far region receives `∞` back. -/
theorem thetaComponentsOfPlane (h : PlaneHypothesis) (hplane : PlaneThetaTwoComponents)
    {D₁ D₂ : Set RiemannSphere}
    (hD₁ : ∃ f : C(Disc, RiemannSphere), Function.Injective f ∧ Set.range f = D₁)
    (hD₂ : ∃ g : C(Disc, RiemannSphere), Function.Injective g ∧ Set.range g = D₂)
    (hdisj : Disjoint D₁ D₂)
    (α β : C(Set.Icc (0 : ℝ) 1, RiemannSphere))
    (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hα₀ : α ⟨0, by norm_num⟩ ∈ D₁) (hα₁ : α ⟨1, by norm_num⟩ ∈ D₂)
    (hβ₀ : β ⟨0, by norm_num⟩ ∈ D₁) (hβ₁ : β ⟨1, by norm_num⟩ ∈ D₂)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂)
    (hβint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ D₁ ∪ D₂)
    (hsep : ∀ s t : Set.Icc (0 : ℝ) 1, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      α s ≠ β t)
    (hαβ₀ : α ⟨0, by norm_num⟩ ≠ β ⟨0, by norm_num⟩)
    (hαβ₁ : α ⟨1, by norm_num⟩ ≠ β ⟨1, by norm_num⟩) :
    ∃ P₁ P₂ : Set RiemannSphere,
      P₁.Nonempty ∧ P₂.Nonempty ∧ IsOpen P₁ ∧ IsOpen P₂ ∧ Disjoint P₁ P₂ ∧
      P₁ ∪ P₂ = Set.univ \ (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β) ∧
      IsPreconnected P₁ ∧ IsPreconnected P₂ := by
  classical
  obtain ⟨p, hp⟩ := exists_notMem_theta hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁
    hαint hβint hsep hαβ₀ hαβ₁
  obtain ⟨Φ, hΦ⟩ := exists_homeomorph_infty_eq p
  set Ψ : RiemannSphere ≃ₜ RiemannSphere := Φ.symm with hΨdef
  have hΨp : Ψ p = infty := by
    rw [hΨdef, ← hΦ]
    exact Φ.symm_apply_apply infty
  obtain ⟨f₁, hf₁inj, hf₁range⟩ := hD₁
  obtain ⟨f₂, hf₂inj, hf₂range⟩ := hD₂
  set X : Set RiemannSphere := D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β with hXdef
  have hpX : p ∉ X := hp
  have hInfX : (infty : RiemannSphere) ∉ Ψ '' X := by
    rintro ⟨y, hy, hyinf⟩
    have hyp : y = p := Ψ.injective (hyinf.trans hΨp.symm)
    exact hpX (hyp ▸ hy)
  have hne : ∀ y : RiemannSphere, y ∈ X → Ψ y ≠ infty := by
    intro y hy hcon
    exact hInfX ⟨y, hy, hcon⟩
  obtain ⟨F₁, hF₁coe₀, hF₁inj_of⟩ := exists_lift_of_avoids_infty
    ⟨fun u => Ψ (f₁ u), Ψ.continuous.comp f₁.continuous⟩
    (fun u => hne (f₁ u) (by rw [hXdef, ← hf₁range]; exact Or.inl (Or.inl (Or.inl ⟨u, rfl⟩))))
  have hF₁coe : ∀ u : Disc, ((F₁ u : ℂ) : RiemannSphere) = Ψ (f₁ u) := fun u => hF₁coe₀ u
  obtain ⟨F₂, hF₂coe₀, hF₂inj_of⟩ := exists_lift_of_avoids_infty
    ⟨fun u => Ψ (f₂ u), Ψ.continuous.comp f₂.continuous⟩
    (fun u => hne (f₂ u) (by rw [hXdef, ← hf₂range]; exact Or.inl (Or.inl (Or.inr ⟨u, rfl⟩))))
  have hF₂coe : ∀ u : Disc, ((F₂ u : ℂ) : RiemannSphere) = Ψ (f₂ u) := fun u => hF₂coe₀ u
  obtain ⟨A, hAcoe₀, hAinj_of⟩ := exists_lift_of_avoids_infty
    ⟨fun t => Ψ (α t), Ψ.continuous.comp α.continuous⟩
    (fun t => hne (α t) (by rw [hXdef]; exact Or.inl (Or.inr ⟨t, rfl⟩)))
  have hAcoe : ∀ t : Set.Icc (0 : ℝ) 1, ((A t : ℂ) : RiemannSphere) = Ψ (α t) :=
    fun t => hAcoe₀ t
  obtain ⟨B, hBcoe₀, hBinj_of⟩ := exists_lift_of_avoids_infty
    ⟨fun t => Ψ (β t), Ψ.continuous.comp β.continuous⟩
    (fun t => hne (β t) (by rw [hXdef]; exact Or.inr ⟨t, rfl⟩))
  have hBcoe : ∀ t : Set.Icc (0 : ℝ) 1, ((B t : ℂ) : RiemannSphere) = Ψ (β t) :=
    fun t => hBcoe₀ t
  have hF₁inj : Function.Injective F₁ := hF₁inj_of (Ψ.injective.comp hf₁inj)
  have hF₂inj : Function.Injective F₂ := hF₂inj_of (Ψ.injective.comp hf₂inj)
  have hAinj : Function.Injective A := hAinj_of (Ψ.injective.comp hαinj)
  have hBinj : Function.Injective B := hBinj_of (Ψ.injective.comp hβinj)
  set d₁ : Set ℂ := Set.range F₁ with hd₁def
  set d₂ : Set ℂ := Set.range F₂ with hd₂def
  have hd₁coe : (↑) '' d₁ = Ψ '' D₁ := by
    rw [hd₁def, ← hf₁range]
    ext x; constructor
    · rintro ⟨z, ⟨u, rfl⟩, rfl⟩
      exact ⟨f₁ u, ⟨u, rfl⟩, (hF₁coe u).symm⟩
    · rintro ⟨y, ⟨u, rfl⟩, rfl⟩
      exact ⟨F₁ u, ⟨u, rfl⟩, hF₁coe u⟩
  have hd₂coe : (↑) '' d₂ = Ψ '' D₂ := by
    rw [hd₂def, ← hf₂range]
    ext x; constructor
    · rintro ⟨z, ⟨u, rfl⟩, rfl⟩
      exact ⟨f₂ u, ⟨u, rfl⟩, (hF₂coe u).symm⟩
    · rintro ⟨y, ⟨u, rfl⟩, rfl⟩
      exact ⟨F₂ u, ⟨u, rfl⟩, hF₂coe u⟩
  have hd₁d₂ : Disjoint d₁ d₂ := by
    rw [Set.disjoint_left]
    intro z hz₁ hz₂
    have h1 : (↑z : RiemannSphere) ∈ Ψ '' D₁ := by rw [← hd₁coe]; exact ⟨z, hz₁, rfl⟩
    have h2 : (↑z : RiemannSphere) ∈ Ψ '' D₂ := by rw [← hd₂coe]; exact ⟨z, hz₂, rfl⟩
    obtain ⟨y₁, hy₁, hy₁z⟩ := h1
    obtain ⟨y₂, hy₂, hy₂z⟩ := h2
    exact (Set.disjoint_left.mp hdisj hy₁) (Ψ.injective (hy₁z.trans hy₂z.symm) ▸ hy₂)
  have hA₀ : A ⟨0, by norm_num⟩ ∈ d₁ := by
    obtain ⟨u, hu⟩ := (show α ⟨0, by norm_num⟩ ∈ Set.range f₁ by rw [hf₁range]; exact hα₀)
    exact ⟨u, OnePoint.coe_injective (by rw [hF₁coe u, hAcoe ⟨0, by norm_num⟩, hu])⟩
  have hA₁ : A ⟨1, by norm_num⟩ ∈ d₂ := by
    obtain ⟨u, hu⟩ := (show α ⟨1, by norm_num⟩ ∈ Set.range f₂ by rw [hf₂range]; exact hα₁)
    exact ⟨u, OnePoint.coe_injective (by rw [hF₂coe u, hAcoe ⟨1, by norm_num⟩, hu])⟩
  have hB₀ : B ⟨0, by norm_num⟩ ∈ d₁ := by
    obtain ⟨u, hu⟩ := (show β ⟨0, by norm_num⟩ ∈ Set.range f₁ by rw [hf₁range]; exact hβ₀)
    exact ⟨u, OnePoint.coe_injective (by rw [hF₁coe u, hBcoe ⟨0, by norm_num⟩, hu])⟩
  have hB₁ : B ⟨1, by norm_num⟩ ∈ d₂ := by
    obtain ⟨u, hu⟩ := (show β ⟨1, by norm_num⟩ ∈ Set.range f₂ by rw [hf₂range]; exact hβ₁)
    exact ⟨u, OnePoint.coe_injective (by rw [hF₂coe u, hBcoe ⟨1, by norm_num⟩, hu])⟩
  have hAint : ∀ t : Set.Icc (0:ℝ) 1, (t:ℝ) ∈ Set.Ioo 0 1 → A t ∉ d₁ ∪ d₂ := by
    intro t ht hmem
    have hmem' : (↑(A t) : RiemannSphere) ∈ Ψ '' D₁ ∪ Ψ '' D₂ := by
      rcases hmem with h | h
      · exact Or.inl (by rw [← hd₁coe]; exact ⟨A t, h, rfl⟩)
      · exact Or.inr (by rw [← hd₂coe]; exact ⟨A t, h, rfl⟩)
    rw [hAcoe t] at hmem'
    rcases hmem' with ⟨y, hy, hyz⟩ | ⟨y, hy, hyz⟩
    · exact hαint t ht (Or.inl (Ψ.injective hyz ▸ hy))
    · exact hαint t ht (Or.inr (Ψ.injective hyz ▸ hy))
  have hBint : ∀ t : Set.Icc (0:ℝ) 1, (t:ℝ) ∈ Set.Ioo 0 1 → B t ∉ d₁ ∪ d₂ := by
    intro t ht hmem
    have hmem' : (↑(B t) : RiemannSphere) ∈ Ψ '' D₁ ∪ Ψ '' D₂ := by
      rcases hmem with h | h
      · exact Or.inl (by rw [← hd₁coe]; exact ⟨B t, h, rfl⟩)
      · exact Or.inr (by rw [← hd₂coe]; exact ⟨B t, h, rfl⟩)
    rw [hBcoe t] at hmem'
    rcases hmem' with ⟨y, hy, hyz⟩ | ⟨y, hy, hyz⟩
    · exact hβint t ht (Or.inl (Ψ.injective hyz ▸ hy))
    · exact hβint t ht (Or.inr (Ψ.injective hyz ▸ hy))
  have hsep' : ∀ s t : Set.Icc (0:ℝ) 1, (s:ℝ) ∈ Set.Ioo 0 1 → (t:ℝ) ∈ Set.Ioo 0 1 →
      A s ≠ B t := by
    intro s t hs ht hcon
    exact hsep s t hs ht (Ψ.injective (by rw [← hAcoe s, ← hBcoe t, hcon]))
  have hAβ₀ : A ⟨0, by norm_num⟩ ≠ B ⟨0, by norm_num⟩ := by
    intro hcon
    exact hαβ₀ (Ψ.injective (by rw [← hAcoe ⟨0, by norm_num⟩, ← hBcoe ⟨0, by norm_num⟩, hcon]))
  have hAβ₁ : A ⟨1, by norm_num⟩ ≠ B ⟨1, by norm_num⟩ := by
    intro hcon
    exact hαβ₁ (Ψ.injective (by rw [← hAcoe ⟨1, by norm_num⟩, ← hBcoe ⟨1, by norm_num⟩, hcon]))
  obtain ⟨P₁', P₂', hP₁ne, hP₂ne, hP₁o, hP₂o, hPdisj, hPun, hP₁c, hP₂c⟩ :=
    hplane ⟨F₁, hF₁inj, hd₁def.symm⟩ ⟨F₂, hF₂inj, hd₂def.symm⟩ hd₁d₂ A B hAinj hBinj hA₀ hA₁
      hB₀ hB₁ hAint hBint hsep' hAβ₀ hAβ₁ h
  have hArcα : Set.range (fun t : Set.Icc (0 : ℝ) 1 => ((A t : ℂ) : RiemannSphere)) =
      Ψ '' Set.range α := by
    ext x; constructor
    · rintro ⟨t, rfl⟩; exact ⟨α t, ⟨t, rfl⟩, (hAcoe t).symm⟩
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩; exact ⟨t, hAcoe t⟩
  have hArcβ : Set.range (fun t : Set.Icc (0 : ℝ) 1 => ((B t : ℂ) : RiemannSphere)) =
      Ψ '' Set.range β := by
    ext x; constructor
    · rintro ⟨t, rfl⟩; exact ⟨β t, ⟨t, rfl⟩, (hBcoe t).symm⟩
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩; exact ⟨t, hBcoe t⟩
  have hO : ((↑) '' d₁ ∪ (↑) '' d₂ ∪
        Set.range (fun t : Set.Icc (0 : ℝ) 1 => ((A t : ℂ) : RiemannSphere)) ∪
        Set.range (fun t : Set.Icc (0 : ℝ) 1 => ((B t : ℂ) : RiemannSphere))) = Ψ '' X := by
    rw [hd₁coe, hd₂coe, hArcα, hArcβ, hXdef, ← Set.image_union, ← Set.image_union,
      ← Set.image_union]
  have hO' : (↑) '' (d₁ ∪ d₂ ∪ Set.range A ∪ Set.range B) = Ψ '' X := by
    rw [Set.image_union, Set.image_union, Set.image_union]
    rw [← Set.range_comp ((↑) : ℂ → RiemannSphere) A,
        ← Set.range_comp ((↑) : ℂ → RiemannSphere) B]
    exact hO
  have hPun' : P₁' ∪ P₂' = (↑) ⁻¹' (Ψ '' X)ᶜ := by
    rw [hPun, ← hO']
    ext z
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_image, Set.mem_union, Set.mem_range]
    constructor
    · intro hz ⟨a, has, haz⟩
      exact hz (OnePoint.coe_injective haz ▸ has)
    · intro hz hmem
      exact hz ⟨z, hmem, rfl⟩
  have hInfXc : (infty : RiemannSphere) ∈ (Ψ '' X)ᶜ := hInfX
  have hran : Set.range ((↑) : ℂ → RiemannSphere) = ({infty} : Set RiemannSphere)ᶜ := by
    rw [← OnePoint.compl_range_coe, compl_compl]
  have hX'compl : (↑) '' (P₁' ∪ P₂') ∪ {infty} = (Ψ '' X)ᶜ := by
    have h1 : (↑) '' (P₁' ∪ P₂') = (Ψ '' X)ᶜ \ {infty} := by
      rw [hPun', Set.image_preimage_eq_inter_range, hran, Set.sdiff_eq]
    rw [h1]
    ext x; constructor
    · rintro (⟨hx, -⟩ | rfl)
      · exact hx
      · exact hInfXc
    · intro hx
      by_cases h : x = infty
      · exact Or.inr h
      · exact Or.inl ⟨hx, h⟩
  have hXcompact : IsCompact X := by
    rw [hXdef, ← hf₁range, ← hf₂range]
    exact (((isCompact_range f₁.continuous).union (isCompact_range f₂.continuous)).union
      (isCompact_range α.continuous)).union (isCompact_range β.continuous)
  have hX'compact : IsCompact (Ψ '' X) := hXcompact.image Ψ.continuous
  have hX'open : IsOpen ((Ψ '' X)ᶜ) := hX'compact.isClosed.isOpen_compl
  have hcpt : IsCompact (((↑) ⁻¹' (Ψ '' X)ᶜ)ᶜ : Set ℂ) :=
    ((OnePoint.isOpen_iff_of_mem' hInfXc).mp hX'open).1
  obtain ⟨R, hR⟩ := hcpt.isBounded.exists_norm_le
  set R₀ : ℝ := max R 0 with hR₀def
  have hR₀pos : 0 < R₀ + 1 := by rw [hR₀def]; positivity
  have hfar_sub : ∀ z : ℂ, R₀ + 1 < ‖z‖ → z ∈ P₁' ∪ P₂' := by
    intro z hz
    rw [hPun']
    intro hmem
    have h1 : ‖z‖ ≤ R := hR z (fun hcon => hcon hmem)
    have h2 : R ≤ R₀ := by rw [hR₀def]; exact le_max_left R 0
    linarith
  have hXfin : (↑) '' (P₁' ∪ P₂') ∪ {infty} = (Φ.symm '' X)ᶜ := by
    rw [← hΨdef]; exact hX'compl
  have hXfin' : (↑) '' (P₂' ∪ P₁') ∪ {infty} = (Φ.symm '' X)ᶜ := by
    rw [Set.union_comm P₂' P₁']; exact hXfin
  rcases (isPreconnected_far' hR₀pos).subset_or_subset hP₁o hP₂o hPdisj hfar_sub with
    hfar₁ | hfar₂
  · obtain ⟨Q₁, Q₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      sphereTwoPiecesOfPlanePair Φ hP₁o hP₂o hPdisj hP₁c hP₂c hP₂ne hXfin hfar₁
    refine ⟨Q₁, Q₂, h1, h2, h3, h4, h5, ?_, h7, h8⟩
    exact h6.trans (congrArg (fun s => Set.univ \ s) hXdef)
  · obtain ⟨Q₁, Q₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      sphereTwoPiecesOfPlanePair Φ hP₂o hP₁o hPdisj.symm hP₂c hP₁c hP₁ne hXfin' hfar₂
    refine ⟨Q₁, Q₂, h1, h2, h3, h4, h5, ?_, h7, h8⟩
    exact h6.trans (congrArg (fun s => Set.univ \ s) hXdef)

/-! ## The target -/

theorem thetaComplementComponents
    (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {D₁ D₂ : Set Work.Smooth.SphereJordan.RiemannSphere}
    (hD₁ : ∃ f : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.RiemannSphere),
      Function.Injective f ∧ Set.range f = D₁)
    (hD₂ : ∃ g : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.RiemannSphere),
      Function.Injective g ∧ Set.range g = D₂)
    (hdisj : Disjoint D₁ D₂)
    (α β : C(Set.Icc (0 : ℝ) 1, Work.Smooth.SphereJordan.RiemannSphere))
    (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hα₀ : α ⟨0, le_refl 0, zero_le_one⟩ ∈ D₁) (hα₁ : α ⟨1, zero_le_one, le_refl 1⟩ ∈ D₂)
    (hβ₀ : β ⟨0, le_refl 0, zero_le_one⟩ ∈ D₁) (hβ₁ : β ⟨1, zero_le_one, le_refl 1⟩ ∈ D₂)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂)
    (hβint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ D₁ ∪ D₂)
    (hsep : ∀ s t : Set.Icc (0 : ℝ) 1, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      α s ≠ β t)
    (hαβ₀ : α ⟨0, le_refl 0, zero_le_one⟩ ≠ β ⟨0, le_refl 0, zero_le_one⟩)
    (hαβ₁ : α ⟨1, zero_le_one, le_refl 1⟩ ≠ β ⟨1, zero_le_one, le_refl 1⟩) :
    ∃ P₁ P₂ : Set Work.Smooth.SphereJordan.RiemannSphere,
      P₁.Nonempty ∧ P₂.Nonempty ∧ IsOpen P₁ ∧ IsOpen P₂ ∧ Disjoint P₁ P₂ ∧
      P₁ ∪ P₂ = Set.univ \ (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β) ∧
      IsPreconnected P₁ ∧ IsPreconnected P₂ := by
  exact thetaComponentsOfPlane h planeThetaComponentsOf hD₁ hD₂ hdisj α β
    hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep hαβ₀ hαβ₁

end

end Work.Smooth.SphereJordan
