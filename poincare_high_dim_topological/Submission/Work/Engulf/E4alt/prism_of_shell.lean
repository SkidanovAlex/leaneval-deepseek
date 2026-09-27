import Mathlib
import Submission.Work.Engulf.Tools
import Submission.Work.PL.Defs

/-!
# `Work.Engulf.E4alt.prism_of_shell`

The prism decomposition (`G2`/`JoinPrismForm n`) applied to a simplex given as the convex hull of
the *vertex images* `y '' τ` of a finite vertex set `τ ⊆ PL.E N` (`y : PL.E N → PL.E n`).

`JoinPrismForm n` is stated for the *identity* embedding of a vertex set of `PL.E n`; here the
simplex of interest is spanned by the images `y v` of the vertices.  The bridge is purely
combinatorial/geometric:

* `AffineIndependent ℝ (fun v : ↥τ => y v)` makes `y` injective on `τ` and makes the identity
  family on the image set `τ.image y` affinely independent (`affineIndependent_image`);
* `τ = top ⊔ fl` gives `τ.image y = top.image y ∪ fl.image y`, hence the counting and arithmetic
  hypotheses of `JoinPrismForm`;
* `⋃_{w ∈ fl.image y} simp ((τ.image y).erase w) = ⋃_{w ∈ fl} simp ((τ.erase w).image y)` by
  `image_biUnion_eq` + `image_erase_of_injOn`.

This is the input `G2`-application of the `E4b`–`E4d` analysis (`NOTES_E4alt.md` §4): the
"floor" `γ₀` corresponds to erasing a vertex of `fl` and the "top" `γ₁` to erasing one of `top`.
-/

namespace Work.Engulf.E4alt

open Set

/-- Affine independence of the vertex images forces `y` to be injective on `τ`. -/
lemma injOn_of_affineIndependent {n N : ℕ} {τ : Finset (PL.E N)} {y : PL.E N → PL.E n}
    (h : AffineIndependent ℝ (fun v : ↥τ => y v)) : Set.InjOn y (τ : Set (PL.E N)) :=
  fun a ha b hb hab =>
    congrArg Subtype.val
      (AffineIndependent.injective h (a₁ := (⟨a, ha⟩ : ↥τ)) (a₂ := ⟨b, hb⟩) hab)

/-- Affine independence transfers from the vertex family to the identity family on the image
vertex set. -/
lemma affineIndependent_image {n N : ℕ} {τ : Finset (PL.E N)} {y : PL.E N → PL.E n}
    (h : AffineIndependent ℝ (fun v : ↥τ => y v)) :
    AffineIndependent ℝ (fun v : ↥(τ.image y) => (v : PL.E n)) := by
  have hrange : Set.range (fun v : ↥τ => y v) = (↑(τ.image y) : Set (PL.E n)) := by
    ext x
    simp only [Set.mem_range, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨v, rfl⟩; exact ⟨v, v.2, rfl⟩
    · rintro ⟨v, hv, rfl⟩; exact ⟨⟨v, hv⟩, rfl⟩
  have h2 := h.range
  rwa [hrange] at h2

/-- Disjointness is preserved by the (injective) vertex map. -/
lemma disjoint_image {α β : Type*} [DecidableEq α] [DecidableEq β] {s t : Finset α}
    {f : α → β} (hdisj : Disjoint s t) (hinj : Set.InjOn f ((s ∪ t : Finset α) : Set α)) :
    Disjoint (s.image f) (t.image f) := by
  rw [Finset.disjoint_left]
  intro a ha ha'
  rw [Finset.mem_image] at ha ha'
  obtain ⟨x, hx, hfx⟩ := ha
  obtain ⟨z, hz, hfz⟩ := ha'
  have hxz : x = z := hinj (Finset.mem_union_left t hx) (Finset.mem_union_right s hz)
    (by rw [hfx, hfz])
  exact (Finset.disjoint_left.mp hdisj hx) (by simpa [hxz] using hz)

/-- Erasing the image of a member of a finset from the image is the same as imaging the erased
finset (the `InjOn` version of `Finset.image_erase`). -/
lemma image_erase_of_injOn {α β : Type*} [DecidableEq α] [DecidableEq β] {s : Finset α}
    {f : α → β} {a : α} (ha : a ∈ s) (hinj : Set.InjOn f (↑s : Set α)) :
    (s.image f).erase (f a) = (s.erase a).image f := by
  ext b
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hbne, v, hv, rfl⟩
    exact ⟨v, ⟨fun hva => hbne (by rw [hva]), hv⟩, rfl⟩
  · rintro ⟨v, ⟨hva, hv⟩, rfl⟩
    exact ⟨fun h => hva (hinj hv ha h), v, hv, rfl⟩

/-- The simplex on the erased image vertex set, in the form used by the target statement. -/
lemma simp_erase_image {n N : ℕ} {τ : Finset (PL.E N)} {y : PL.E N → PL.E n} {w : PL.E N}
    (hw : w ∈ τ) (hinj : Set.InjOn y (↑τ : Set (PL.E N))) :
    PL.simp ((τ.image y).erase (y w)) =
      convexHull ℝ (y '' (((τ.erase w) : Finset (PL.E N)) : Set (PL.E N))) := by
  rw [image_erase_of_injOn hw hinj, PL.simp, Finset.coe_image]

/-- A union over the image of a finset is the union over the finset. -/
lemma image_biUnion_eq {α β γ : Type*} [DecidableEq β] (s : Finset α) (f : α → β)
    (t : β → Set γ) : (⋃ b ∈ s.image f, t b) = ⋃ a ∈ s, t (f a) := by
  ext x
  simp only [Set.mem_iUnion, exists_prop, Finset.mem_image]
  constructor
  · rintro ⟨b, ⟨a, ha, rfl⟩, hx⟩; exact ⟨a, ha, hx⟩
  · rintro ⟨a, ha, hx⟩; exact ⟨f a, ⟨a, ha, rfl⟩, hx⟩

theorem prism_of_shell {n q : ℕ} (hqn : q + 1 ≤ n) {N : ℕ}
    (hjoin : Work.Engulf.JoinPrismForm n)
    {y : PL.E N → PL.E n} {τ top fl : Finset (PL.E N)}
    (hne_top : top.Nonempty) (hne_fl : fl.Nonempty) (hdisj : Disjoint top fl)
    (hunion : top ∪ fl = τ) (hcard : τ.card = q + 2)
    (hind : AffineIndependent ℝ (fun v : ↥τ => y v)) :
    ∃ (T : PL.E n ≃ᵃ[ℝ] Work.Engulf.Pr (n - q - 1) q) (F : Set (PL.E q))
      (γ₀ γ₁ : PL.E q → ℝ),
      IsCompact F ∧ Convex ℝ F ∧ Continuous γ₀ ∧ Continuous γ₁ ∧
      (∀ z ∈ F, γ₀ z ≤ γ₁ z) ∧ (∀ z ∈ frontier F, γ₀ z = γ₁ z) ∧
      T '' (convexHull ℝ (y '' (τ : Set (PL.E N)))) =
        {x : Work.Engulf.Pr (n - q - 1) q | x.1 = 0 ∧ x.2.1 ∈ F ∧
          γ₀ x.2.1 ≤ x.2.2 ∧ x.2.2 ≤ γ₁ x.2.1} ∧
      T '' (⋃ w ∈ fl, convexHull ℝ
          (y '' (((τ.erase w : Finset (PL.E N))) : Set (PL.E N)))) =
        {x : Work.Engulf.Pr (n - q - 1) q | x.1 = 0 ∧ x.2.1 ∈ F ∧ x.2.2 = γ₀ x.2.1} ∧
      T '' (⋃ w ∈ top, convexHull ℝ
          (y '' (((τ.erase w : Finset (PL.E N))) : Set (PL.E N)))) =
        {x : Work.Engulf.Pr (n - q - 1) q | x.1 = 0 ∧ x.2.1 ∈ F ∧ x.2.2 = γ₁ x.2.1} := by
  classical
  have hinjτ : Set.InjOn y (↑τ : Set (PL.E N)) := injOn_of_affineIndependent hind
  have hinj : Set.InjOn y (↑(top ∪ fl) : Set (PL.E N)) := by rw [hunion]; exact hinjτ
  have hun : top.image y ∪ fl.image y = τ.image y := by
    rw [← Finset.image_union, hunion]
  have hcard' : (top.image y ∪ fl.image y).card = q + 2 := by
    rw [hun, Finset.card_image_of_injOn hinjτ, hcard]
  have hind' : AffineIndependent ℝ (fun v : ↥(top.image y ∪ fl.image y) => (v : PL.E n)) := by
    rw [hun]; exact affineIndependent_image hind
  obtain ⟨T, F, γ₀, γ₁, hFc, hFconv, hγ₀, hγ₁, hle, hfr, h1, h2, h3⟩ :=
    hjoin (q := q) hqn (top.image y) (fl.image y) (hne_top.image y) (hne_fl.image y)
      (disjoint_image hdisj hinj) hcard' hind'
  have hτcoe : ((τ : Set (PL.E N))) = ((top : Set (PL.E N)) ∪ (fl : Set (PL.E N))) := by
    rw [← hunion, Finset.coe_union]
  have hsimpτ : PL.simp (top.image y ∪ fl.image y) =
      convexHull ℝ (y '' (τ : Set (PL.E N))) := by
    rw [PL.simp, Finset.coe_union, Finset.coe_image, Finset.coe_image, ← Set.image_union,
      ← hτcoe]
  have hmemτ : ∀ w, w ∈ fl → w ∈ τ := by
    intro w hw; rw [← hunion]; exact Finset.mem_union_right top hw
  have hpt : ∀ w ∈ fl, convexHull ℝ (y '' (((τ.erase w) : Finset (PL.E N)) : Set (PL.E N)))
      = PL.simp (((top.image y) ∪ (fl.image y)).erase (y w)) := by
    intro w hw
    rw [hun]
    exact (simp_erase_image (hmemτ w hw) hinjτ).symm
  have hfl : (⋃ w ∈ fl, convexHull ℝ
        (y '' (((τ.erase w : Finset (PL.E N))) : Set (PL.E N))))
      = ⋃ w ∈ fl.image y, PL.simp (((top.image y) ∪ (fl.image y)).erase w) := by
    rw [image_biUnion_eq fl y (fun b => PL.simp (((top.image y) ∪ (fl.image y)).erase b))]
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨w, hw, hx⟩; exact ⟨w, hw, (hpt w hw) ▸ hx⟩
    · rintro ⟨w, hw, hx⟩; exact ⟨w, hw, (hpt w hw).symm ▸ hx⟩
  have hmemtop : ∀ w, w ∈ top → w ∈ τ := by
    intro w hw; rw [← hunion]; exact Finset.mem_union_left fl hw
  have hpt' : ∀ w ∈ top, convexHull ℝ (y '' (((τ.erase w) : Finset (PL.E N)) : Set (PL.E N)))
      = PL.simp (((top.image y) ∪ (fl.image y)).erase (y w)) := by
    intro w hw
    rw [hun]
    exact (simp_erase_image (hmemtop w hw) hinjτ).symm
  have htop : (⋃ w ∈ top, convexHull ℝ
        (y '' (((τ.erase w : Finset (PL.E N))) : Set (PL.E N))))
      = ⋃ w ∈ top.image y, PL.simp (((top.image y) ∪ (fl.image y)).erase w) := by
    rw [image_biUnion_eq top y (fun b => PL.simp (((top.image y) ∪ (fl.image y)).erase b))]
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨w, hw, hx⟩; exact ⟨w, hw, (hpt' w hw) ▸ hx⟩
    · rintro ⟨w, hw, hx⟩; exact ⟨w, hw, (hpt' w hw).symm ▸ hx⟩
  exact ⟨T, F, γ₀, γ₁, hFc, hFconv, hγ₀, hγ₁, hle, hfr, by rw [← hsimpτ]; exact h1,
    by rw [hfl]; exact h2, by rw [htop]; exact h3⟩

end Work.Engulf.E4alt
