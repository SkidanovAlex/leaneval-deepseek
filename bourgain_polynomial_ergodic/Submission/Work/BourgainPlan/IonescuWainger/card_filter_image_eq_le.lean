import Mathlib

namespace Work.BourgainPlan.IonescuWainger

theorem card_filter_image_eq_le {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (B : Finset ι) :
    ((Finset.univ : Finset (κ → ι)).filter (fun s => Finset.univ.image s = B)).card
      ≤ B.card ^ Fintype.card κ := by
  rw [← Fintype.card_subtype (fun s : κ → ι => Finset.univ.image s = B)]
  have hle := Fintype.card_le_of_injective
      (fun s : {s : κ → ι // Finset.univ.image s = B} =>
        fun x : κ => (⟨s.1 x, by
          have hx : s.1 x ∈ Finset.univ.image s.1 := Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
          rw [s.2] at hx
          exact hx⟩ : B))
      (by
        intro s t hst
        have : ∀ x, s.1 x = t.1 x := fun x => Subtype.ext_iff.mp (congrFun hst x)
        exact Subtype.ext (funext this))
  have heq : Fintype.card (κ → ↑B) = B.card ^ Fintype.card κ := by
    rw [Fintype.card_fun, Fintype.card_coe]
  exact hle.trans (le_of_eq heq)

end Work.BourgainPlan.IonescuWainger
