import Mathlib

namespace Work.CORE4

/-- **Cardinality of the projected image of a subgroup meeting `P` trivially.**

Let `π : ↥(P ⊔ E) →* ↥E` be a homomorphism that is a "projection modulo `P`":
`x * (π x)⁻¹ ∈ P` for every `x ∈ P ⊔ E`.  If `X ≤ P ⊔ E` with `X ⊓ P = ⊥`, then `π` is
injective on `X` (two elements of `X` with the same image differ by an element of
`X ⊓ P = ⊥`), so the image of `X` under `π` followed by `E.subtype` has the same
cardinality as `X`. -/
theorem Fibre9ImageCard {G : Type} [Group G] [Finite G] {P E X : Subgroup G}
    (π : ↥(P ⊔ E) →* ↥E)
    (hproj : ∀ x : ↥(P ⊔ E), (x : G) * (((π x : ↥E) : G))⁻¹ ∈ P)
    (hX : X ≤ P ⊔ E) (hinf : X ⊓ P = ⊥) :
    Nat.card ↥(Subgroup.map E.subtype ((X.subgroupOf (P ⊔ E)).map π)) = Nat.card ↥X := by
  set Im : Subgroup G := Subgroup.map E.subtype ((X.subgroupOf (P ⊔ E)).map π) with hIm
  have hmem : ∀ x : ↥X, E.subtype (π ⟨(x : G), hX x.2⟩) ∈ Im := by
    intro x
    rw [hIm]
    apply Subgroup.mem_map_of_mem
    apply Subgroup.mem_map_of_mem
    rw [Subgroup.mem_subgroupOf]
    exact x.2
  let f : ↥X → ↥Im := fun x => ⟨E.subtype (π ⟨(x : G), hX x.2⟩), hmem x⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : π ⟨(x : G), hX x.2⟩ = π ⟨(y : G), hX y.2⟩ := by
      apply Subgroup.subtype_injective E
      simpa [f] using congrArg Subtype.val hxy
    have hPmem : (x : G) * (y : G)⁻¹ ∈ P := by
      have hxP := hproj ⟨(x : G), hX x.2⟩
      have hyP := hproj ⟨(y : G), hX y.2⟩
      have hmem2 := mul_mem hxP (inv_mem hyP)
      have he : ((π ⟨(x : G), hX x.2⟩ : ↥E) : G)
          = ((π ⟨(y : G), hX y.2⟩ : ↥E) : G) := congrArg Subtype.val h1
      rw [← he] at hmem2
      convert hmem2 using 1
      group
    have hXmem : (x : G) * (y : G)⁻¹ ∈ X := mul_mem x.2 (inv_mem y.2)
    have hbot : (x : G) * (y : G)⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hinf]; exact ⟨hXmem, hPmem⟩
    have hone : (x : G) * (y : G)⁻¹ = 1 := by simpa using hbot
    exact Subtype.ext (mul_inv_eq_one.mp hone)
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    rw [hIm, Subgroup.mem_map] at hg
    obtain ⟨z, hzK, hzg⟩ := hg
    rw [Subgroup.mem_map] at hzK
    obtain ⟨w, hwK, hwz⟩ := hzK
    rw [Subgroup.mem_subgroupOf] at hwK
    refine ⟨⟨(w : G), hwK⟩, ?_⟩
    apply Subtype.ext
    dsimp only [f]
    have hw : (⟨(w : G), hX hwK⟩ : ↥(P ⊔ E)) = w := Subtype.ext rfl
    rw [← hzg, ← hwz, hw]
  have hcard : Nat.card ↥X = Nat.card ↥Im :=
    Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [hIm] at hcard
  exact hcard.symm

end Work.CORE4
