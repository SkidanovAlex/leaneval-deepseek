import Mathlib
import Submission.Work.WilE7.pad_proj
import Submission.Work.WilE7.pad_deg

namespace Work.WilE7.Endgame.E2B

theorem packRaw {n : ℕ} (M : ℕ) (L : List (Σ r : ℕ, WilkiesDesign.E.SemiPf (n + r)))
    (h : ∀ x ∈ L, x.1 ≤ M)
    (F' : ℕ) (hfmt : ∀ x ∈ L, x.2.fmt ≤ F')
    (D : ℕ) (Q : Polynomial ℕ) (hdeg : ∀ x ∈ L, x.2.deg ≤ Q.eval D) :
    ∃ (Yl : List (WilkiesDesign.E.SemiPf (n + M))),
      Yl.length = L.length ∧
      (∀ Y ∈ Yl, Y.fmt ≤ F' + M ∧ Y.deg ≤ Q.eval D) ∧
      ∀ x ∈ L, ∃ i : Fin Yl.length,
        (Yl.get i).deg ≤ x.2.deg ∧
        WilkiesDesign.E.projFirst n M '' (Yl.get i).set =
          WilkiesDesign.E.projFirst n x.1 '' x.2.set := by
  classical
  let f : {y // y ∈ L} → WilkiesDesign.E.SemiPf (n + M) :=
    fun y => Work.WilE7.SemiPf.pad (Nat.add_le_add_left (h y.1 y.2) n) y.1.2
  refine ⟨L.attach.map f, ?_, ?_, ?_⟩
  · simp [List.length_map, List.length_attach]
  · intro Y hY
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hY
    constructor
    · -- format bound of the padded set
      have hpad : (f x).fmt = (n + M) + (x.1.2).r := rfl
      rw [hpad]
      have hxf : (x.1.2).fmt ≤ F' := hfmt x.1 x.2
      have hx1 : x.1.1 ≤ M := h x.1 x.2
      simp only [WilkiesDesign.E.SemiPf.fmt] at hxf
      omega
    · -- degree bound of the padded set
      exact le_trans (Work.WilE7.semipf_deg_pad_le
        (Nat.add_le_add_left (h x.1 x.2) n) x.1.2) (hdeg x.1 x.2)
  · -- index correspondence
    intro x hx
    have hmem : f ⟨x, hx⟩ ∈ L.attach.map f :=
      List.mem_map.mpr ⟨⟨x, hx⟩, List.mem_attach L ⟨x, hx⟩, rfl⟩
    obtain ⟨i, hi⟩ := List.get_of_mem hmem
    refine ⟨i, ?_, ?_⟩
    · rw [hi]
      exact Work.WilE7.semipf_deg_pad_le (Nat.add_le_add_left (h x hx) n) x.2
    · rw [hi]
      exact Work.WilE7.pad_proj (h x hx) x.2

end Work.WilE7.Endgame.E2B
