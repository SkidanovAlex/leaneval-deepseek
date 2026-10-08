import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.BrauerSuzuki.OddCore.le_of_normal_odd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `N_G(X)` normalises `O_{2'}(C_G(X))`

In Glauberman's analysis of the `Q₈` case of Brauer–Suzuki one studies
`C* = C_G(⟨x⟩)`, `N* = N_G(⟨x⟩)` and `H* = O_{2'}(C*)`.  The element `x` runs over the
elements of order `4` of a Sylow `2`-subgroup, and the group `N*` acts on `C*` by
conjugation; `H*` is a characteristic subgroup of `C*`, hence invariant under this action.

This file records that invariance in the form in which the rest of the development uses it:
the normaliser of `X` normalises the image in `G` of `O_{2'}(C_G(X))`.

The proof is split into three general facts, none of which mentions `oddCore` except the
first:

* `oddCore_characteristic` : `O(G) = O_{2'}(G)` is invariant under every automorphism of `G`
  (an automorphism permutes the normal subgroups of odd order, and the family of those has
  invariant supremum);
* `normalizer_le_normalizer_centralizer` : `N_G(X) ≤ N_G(C_G(X))`;
* `normalizer_le_normalizer_characteristic` : `N_G(H)` normalises the image in `G` of any
  characteristic subgroup of `H`.

The requested statement is then the immediate combination of these three.
-/

namespace Work.BrauerSuzuki.Q8

open Submission.Blueprint

/-- **`O(G) = O_{2'}(G)` is characteristic.**  An automorphism of a finite group `H` maps the
family `{N : Subgroup H | N.Normal ∧ Odd (Nat.card N)}` onto itself, hence fixes its supremum
`O(H)`.  (Only the `≤` direction is proved; the reverse is the same statement for the inverse
automorphism, via `characteristic_iff_map_le`.) -/
theorem oddCore_characteristic {H : Type*} [Group H] [Finite H] :
    (Submission.Blueprint.oddCore H).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨N, hN, hNodd, hyN⟩ :=
    Work.BrauerSuzuki.OddCore.exists_normal_odd_of_mem_oddCore hy
  have hmap : (N.map φ.toMonoidHom).Normal :=
    Subgroup.Normal.map hN φ.toMonoidHom φ.surjective
  have hodd : Odd (Nat.card ↥(N.map φ.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective φ.injective]
    exact hNodd
  exact Work.BrauerSuzuki.OddCore.le_of_normal_odd hmap hodd
    (Subgroup.mem_map.mpr ⟨y, hyN, rfl⟩)

/-- **The normaliser of a subset normalises its centraliser.**  If `n X n⁻¹ = X` and `c`
commutes with every element of `X`, then `n c n⁻¹` commutes with every element of `X`, since
conjugation by `n` is a bijection of `X` onto itself. -/
theorem normalizer_le_normalizer_centralizer {G : Type*} [Group G] (X : Set G) :
    Subgroup.normalizer X ≤ Subgroup.normalizer (Subgroup.centralizer X : Set G) := by
  intro n hn
  have hn' : ∀ z : G, z ∈ X ↔ n * z * n⁻¹ ∈ X := Subgroup.mem_set_normalizer_iff.mp hn
  have hn'' : ∀ z : G, z ∈ X ↔ n⁻¹ * z * n ∈ X := Subgroup.mem_set_normalizer_iff''.mp hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx z hz
    have h1 : (n⁻¹ * z * n) * x = x * (n⁻¹ * z * n) := hx _ ((hn'' z).mp hz)
    calc z * (n * x * n⁻¹)
        = n * ((n⁻¹ * z * n) * x) * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * z * n)) * n⁻¹ := by rw [h1]
      _ = (n * x * n⁻¹) * z := by group
  · intro hx z hz
    have h2 : (n * z * n⁻¹) * (n * x * n⁻¹) = (n * x * n⁻¹) * (n * z * n⁻¹) :=
      hx _ ((hn' z).mp hz)
    calc z * x
        = n⁻¹ * ((n * z * n⁻¹) * (n * x * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * x * n⁻¹) * (n * z * n⁻¹)) * n := by rw [h2]
      _ = x * z := by group

/-- **`N_G(H)` normalises the image in `G` of a characteristic subgroup `K ≤ H`.**  An element
`n ∈ N_G(H)` induces the automorphism `k ↦ n k n⁻¹` of `↥H`, which fixes the characteristic
subgroup `K`; transporting along `↥H ↪ G` gives `n (K.map H.subtype) n⁻¹ = K.map H.subtype`. -/
theorem normalizer_le_normalizer_characteristic {G : Type*} [Group G] (H : Subgroup G)
    (K : Subgroup H) (hK : K.Characteristic) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (K.map H.subtype : Set G) := by
  intro n hn
  have hmem : ∀ k : H, n * (k : G) * n⁻¹ ∈ H :=
    fun k => (Subgroup.mem_normalizer_iff.mp hn (k : G)).mp k.2
  have hmem' : ∀ k : H, n⁻¹ * (k : G) * n ∈ H :=
    fun k => (Subgroup.mem_set_normalizer_iff''.mp hn (k : G)).mp k.2
  let φ : H ≃* H :=
    { toFun := fun k => ⟨n * (k : G) * n⁻¹, hmem k⟩
      invFun := fun k => ⟨n⁻¹ * (k : G) * n, hmem' k⟩
      left_inv := fun k => Subtype.ext (by simp [mul_assoc])
      right_inv := fun k => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun k l => Subtype.ext (by simp [mul_assoc]) }
  have hφ : K.map φ.toMonoidHom = K := Subgroup.characteristic_iff_map_eq.mp hK φ
  have key : H.subtype.comp φ.toMonoidHom = (MulAut.conj n : G →* G).comp H.subtype := by
    ext k
    rfl
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_map, ← key, ← Subgroup.map_map, hφ]

theorem oddCore_centralizer_map_normalized {G : Type*} [Group G] [Finite G] (X : Subgroup G) :
    ∀ n ∈ Subgroup.normalizer (X : Set G),
      ∀ h ∈ (Submission.Blueprint.oddCore ↥(Subgroup.centralizer (X : Set G))).map
              (Subgroup.centralizer (X : Set G)).subtype,
        n * h * n⁻¹ ∈ (Submission.Blueprint.oddCore ↥(Subgroup.centralizer (X : Set G))).map
              (Subgroup.centralizer (X : Set G)).subtype := by
  intro n hn h hh
  have hnC : n ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer (X : Set G) hn
  have hchar : (Submission.Blueprint.oddCore ↥(Subgroup.centralizer (X : Set G))).Characteristic :=
    oddCore_characteristic
  have hK : n ∈ Subgroup.normalizer
      ((Submission.Blueprint.oddCore ↥(Subgroup.centralizer (X : Set G))).map
        (Subgroup.centralizer (X : Set G)).subtype : Set G) :=
    normalizer_le_normalizer_characteristic (Subgroup.centralizer (X : Set G))
      (Submission.Blueprint.oddCore ↥(Subgroup.centralizer (X : Set G))) hchar hnC
  rw [Subgroup.mem_normalizer_iff] at hK
  exact (hK h).mp hh

end Work.BrauerSuzuki.Q8
