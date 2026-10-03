import Mathlib

namespace Work.OROneRel

theorem telescoping_britton {G : Type*} [Group G] (H : Subgroup G) (t : G)
    (φ : G →* Multiplicative ℤ) (hφt : φ t = Multiplicative.ofAdd 1)
    (hφH : ∀ h ∈ H, φ h = 1)
    (hgen : Subgroup.closure ((H : Set G) ∪ {t}) = ⊤)
    (hmono : ∀ m : ℤ, 1 ≤ m →
      H ⊓ H.map (MulAut.conj t ^ m).toMonoidHom
        = H ⊓ H.map (MulAut.conj t).toMonoidHom)
    (hmono' : ∀ m : ℤ, 1 ≤ m →
      H ⊓ H.map (MulAut.conj t ^ ((-m : ℤ))).toMonoidHom
        = H ⊓ H.map (MulAut.conj t ^ ((-1 : ℤ))).toMonoidHom)
    (h₀ : G) (L : List (ℤˣ × G))
    (hh : h₀ ∈ H) (hg : ∀ i : Fin L.length, (L.get i).2 ∈ H)
    (hchain : L.IsChain (fun a b => a.2 ∈ HNNExtension.toSubgroup
        (H ⊓ H.map (MulAut.conj t ^ ((-1 : ℤ))).toMonoidHom)
        (H ⊓ H.map (MulAut.conj t).toMonoidHom) a.1 → a.1 = b.1))
    (hne : h₀ ≠ 1 ∨ L ≠ []) :
    h₀ * (L.map (fun x : ℤˣ × G => t ^ (x.1 : ℤ) * x.2)).prod ≠ 1 := by sorry

end Work.OROneRel
