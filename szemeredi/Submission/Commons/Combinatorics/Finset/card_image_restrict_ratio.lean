import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

namespace Commons.Combinatorics.Finset

/-- Auxiliary counting lemma.  If `A` is a union of fibres of `f : α → β` (expressed as
`A = f ⁻¹' (f '' A)`) and `Ψ : α ≃ β × γ` is an equivalence compatible with `f` on the first
coordinate, then `#A = #(f '' A) * #γ`. -/
theorem card_eq_card_image_mul_of_fiber {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (f : α → β) (Ψ : α ≃ β × γ) (hf : ∀ x, (Ψ x).1 = f x) (A : Finset α)
    (hA : ∀ x, x ∈ A ↔ f x ∈ A.image f) :
    A.card = (A.image f).card * Fintype.card γ := by
  have hprod : A.image (fun x => Ψ x) = (A.image f) ×ˢ (Finset.univ : Finset γ) := by
    ext p
    rcases p with ⟨b, c⟩
    constructor
    · intro hp
      rw [Finset.mem_image] at hp
      obtain ⟨x, hxA, hx⟩ := hp
      rw [Finset.mem_product]
      exact ⟨Finset.mem_image.mpr ⟨x, hxA, by rw [← hf x, hx]⟩, Finset.mem_univ _⟩
    · intro hp
      rw [Finset.mem_product] at hp
      obtain ⟨h1, _⟩ := hp
      rw [Finset.mem_image] at h1
      obtain ⟨x0, hx0A, hx0⟩ := h1
      rw [Finset.mem_image]
      refine ⟨Ψ.symm (b, c), ?_, Ψ.apply_symm_apply (b, c)⟩
      rw [hA, ← hf (Ψ.symm (b, c)), Ψ.apply_symm_apply]
      exact Finset.mem_image.mpr ⟨x0, hx0A, hx0⟩
  calc A.card = (A.image (fun x => Ψ x)).card :=
        (Finset.card_image_of_injective A Ψ.injective).symm
    _ = ((A.image f) ×ˢ (Finset.univ : Finset γ)).card := by rw [hprod]
    _ = (A.image f).card * (Finset.univ : Finset γ).card := Finset.card_product _ _
    _ = (A.image f).card * Fintype.card γ := by rw [Finset.card_univ]

theorem card_image_restrict_ratio {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]
    (e : Finset ι) (A : Finset ((i : ι) → V i))
    (hA : ∀ x y, (∀ i ∈ e, y i = x i) → (y ∈ A ↔ x ∈ A)) :
    (A.card : ℝ) / (Fintype.card ((i : ι) → V i))
      = ((A.image (fun x => fun i : {i // i ∈ e} => x i.val)).card : ℝ)
          / (Fintype.card ((i : {i // i ∈ e}) → V i.val)) := by
  classical
  let Ψ : ((i : ι) → V i) ≃
      ((i : {i // i ∈ e}) → V i.val) × ((i : {i // i ∉ e}) → V i.val) :=
    Equiv.piEquivPiSubtypeProd (fun i => i ∈ e) V
  have hmem : ∀ x : (i : ι) → V i,
      x ∈ A ↔ (fun i : {i // i ∈ e} => x i.val) ∈
        A.image (fun x : (i : ι) → V i => fun i : {i // i ∈ e} => x i.val) := by
    intro x
    constructor
    · intro hx
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · intro hx
      rw [Finset.mem_image] at hx
      obtain ⟨y, hyA, hyx⟩ := hx
      have hab : ∀ i ∈ e, x i = y i := by
        intro i hi
        have := congrFun hyx ⟨i, hi⟩
        simpa using this.symm
      exact (hA y x hab).mpr hyA
  have hcard := card_eq_card_image_mul_of_fiber
      (f := fun x : (i : ι) → V i => fun i : {i // i ∈ e} => x i.val)
      (Ψ := Ψ) (by intro x; rfl) A hmem
  have hX : Fintype.card ((i : ι) → V i)
      = Fintype.card ((i : {i // i ∈ e}) → V i.val)
        * Fintype.card ((i : {i // i ∉ e}) → V i.val) := by
    rw [Fintype.card_congr Ψ,
      Fintype.card_prod ((i : {i // i ∈ e}) → V i.val) ((i : {i // i ∉ e}) → V i.val)]
  have ha : (A.card : ℝ)
      = ((A.image (fun x : (i : ι) → V i => fun i : {i // i ∈ e} => x i.val)).card : ℝ)
        * (Fintype.card ((i : {i // i ∉ e}) → V i.val) : ℝ) := by
    exact_mod_cast hcard
  have hX' : (Fintype.card ((i : ι) → V i) : ℝ)
      = (Fintype.card ((i : {i // i ∈ e}) → V i.val) : ℝ)
        * (Fintype.card ((i : {i // i ∉ e}) → V i.val) : ℝ) := by
    rw [hX]; push_cast; ring
  have hneX : (Fintype.card ((i : ι) → V i) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ((i : ι) → V i) ≠ 0)
  have hyne : (Fintype.card ((i : {i // i ∈ e}) → V i.val) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ((i : {i // i ∈ e}) → V i.val) ≠ 0)
  rw [div_eq_div_iff hneX hyne, ha, hX']
  ring

end Commons.Combinatorics.Finset