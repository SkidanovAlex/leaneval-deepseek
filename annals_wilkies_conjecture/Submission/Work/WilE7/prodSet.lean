import Mathlib
import Submission.Work.WilE7.ProdDefs
import Submission.Work.WilE7.cubeC_add

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## Membership in a mapped product list -/

/-- Membership in `(l × l').map f` unfolded into a pair of memberships. -/
theorem exists_mem_product_map {α β γ : Type*} (l : List α) (l' : List β) (f : α × β → γ)
    (P : γ → Prop) :
    (∃ c ∈ (l.product l').map f, P c) ↔ ∃ a ∈ l, ∃ b ∈ l', P (f (a, b)) := by
  constructor
  · rintro ⟨c, hc, hP⟩
    rw [List.mem_map] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    obtain ⟨hp1, hp2⟩ := List.mem_product.mp hp
    exact ⟨p.1, hp1, p.2, hp2, hP⟩
  · rintro ⟨a, ha, b, hb, hP⟩
    exact ⟨f (a, b), List.mem_map.mpr ⟨(a, b), List.mem_product.mpr ⟨ha, hb⟩, rfl⟩, hP⟩

/-- The point set of `SemiPf.prod X X'` is the product of the point sets of `X` and `X'`. -/
theorem prodSet {k k' : ℕ} (X : WilkiesDesign.E.SemiPf k) (X' : WilkiesDesign.E.SemiPf k') :
    (Work.WilE7.SemiPf.prod X X').set =
      {z : Fin (k + k') → ℝ | WilkiesDesign.E.projFirst k k' z ∈ X.set ∧
        WilkiesDesign.E.projSnd k k' z ∈ X'.set} := by
  ext z
  change (z ∈ cubeC (k + k') ∧ ∃ B ∈ ((redBasics X).product (redBasics X')).map
      (fun p => Basic.prod p.1 p.2), Basic.holds (EAChain.prod X.c X'.c) B z) ↔
    ((projFirst k k' z ∈ cubeC k ∧ ∃ B ∈ X.basics, Basic.holds X.c B (projFirst k k' z)) ∧
     (projSnd k k' z ∈ cubeC k' ∧ ∃ B ∈ X'.basics, Basic.holds X'.c B (projSnd k k' z)))
  have hE : (∃ B ∈ ((redBasics X).product (redBasics X')).map
        (fun p => Basic.prod p.1 p.2), Basic.holds (EAChain.prod X.c X'.c) B z) ↔
      (∃ B ∈ redBasics X, Basic.holds X.c B (projFirst k k' z)) ∧
      (∃ B ∈ redBasics X', Basic.holds X'.c B (projSnd k k' z)) := by
    rw [exists_mem_product_map]
    constructor
    · rintro ⟨a, ha, b, hb, hh⟩
      obtain ⟨hh1, hh2⟩ := (Basic.holds_prod X.c X'.c a b z).mp hh
      exact ⟨⟨a, ha, hh1⟩, ⟨b, hb, hh2⟩⟩
    · rintro ⟨⟨a, ha, hh⟩, ⟨b, hb, hh'⟩⟩
      exact ⟨a, ha, b, hb, (Basic.holds_prod X.c X'.c a b z).mpr ⟨hh, hh'⟩⟩
  rw [hE, cubeC_add z, exists_holds_redBasics X (projFirst k k' z),
      exists_holds_redBasics X' (projSnd k k' z)]
  tauto

end Work.WilE7
