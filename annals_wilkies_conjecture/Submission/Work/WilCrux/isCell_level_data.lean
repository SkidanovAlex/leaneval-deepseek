import Mathlib
import Submission.Work.WilCrux.SheetDefs

namespace Work.WilCrux

/-- Dropping the last coordinate from a graph cell over `C` recovers `C`. -/
private theorem init_image_graph {n : ℕ} (C : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    Fin.init '' {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)} = C := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz.1
  · intro hx
    exact ⟨Fin.snoc x (f x),
      ⟨by rw [Fin.init_snoc]; exact hx, by rw [Fin.init_snoc, Fin.snoc_last]⟩,
      by rw [Fin.init_snoc]⟩

/-- Dropping the last coordinate from a band cell over `C` recovers `C`; the fibre of the band
over a base point is a nonempty open interval, which is where `a < b` on `C` is used. -/
private theorem init_image_band {n : ℕ} (C : Set (Fin n → ℝ)) (a b : (Fin n → ℝ) → EReal)
    (hab : ∀ x ∈ C, a x < b x) :
    Fin.init '' {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
        a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
        ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} = C := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz.1
  · intro hx
    obtain ⟨t, ht1, ht2⟩ := EReal.exists_between_coe_real (hab x hx)
    exact ⟨Fin.snoc x t,
      ⟨by rw [Fin.init_snoc]; exact hx,
       by rw [Fin.init_snoc, Fin.snoc_last]; exact ht1,
       by rw [Fin.init_snoc, Fin.snoc_last]; exact ht2⟩,
      by rw [Fin.init_snoc]⟩

/-- A cylindrical cell of `ℝ^{p+1}` whose base `Fin.init '' κ` is again a cell of `ℝ^p`, is
nonempty whenever `κ` is, and is a graph cell or a band cell over that base: the two
constructors of `WilkiesDesign.IsCell` at the top level, read back as the `WilCrux` vocabulary. -/
theorem isCell_level_data {p : ℕ} {κ : Set (Fin (p + 1) → ℝ)} (hκ : WilkiesDesign.IsCell (p + 1) κ)
    (hne : κ.Nonempty) :
    WilkiesDesign.IsCell p (Work.WilCrux.base κ) ∧ (Work.WilCrux.base κ).Nonempty ∧
      (Work.WilCrux.IsGraphCellAt κ (Work.WilCrux.base κ) ∨
        Work.WilCrux.IsBandCellAt κ (Work.WilCrux.base κ)) := by
  cases hκ with
  | graph hC f hf =>
    rename_i C
    have hbase : base {z : Fin (p + 1) → ℝ |
        Fin.init z ∈ C ∧ z (Fin.last p) = f (Fin.init z)} = C := init_image_graph C f
    rw [hbase]
    exact ⟨hC, ⟨_, hne.choose_spec.1⟩, Or.inl ⟨f, hf, rfl⟩⟩
  | band hC a b ha hb hab =>
    rename_i C
    have hbase : base {z : Fin (p + 1) → ℝ | Fin.init z ∈ C ∧
        a (Fin.init z) < ((z (Fin.last p) : ℝ) : EReal) ∧
        ((z (Fin.last p) : ℝ) : EReal) < b (Fin.init z)} = C := init_image_band C a b hab
    rw [hbase]
    exact ⟨hC, ⟨_, hne.choose_spec.1⟩, Or.inr ⟨a, b, ha, hb, hab, rfl⟩⟩

end Work.WilCrux
