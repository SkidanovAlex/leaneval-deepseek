import Mathlib
import Submission.Commons.GroupTheory.Subgroup.index_eq_of_ker_le_of_map_eq_zpowers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.GroupTheory

/-- `Nat.card` of the quotient of a subgroup by a `subgroupOf` is the relative index. -/
lemma natCard_quotient_subgroupOf_eq_relIndex {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card (H ⧸ K.subgroupOf H) = K.relIndex H := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card]

/-- The second isomorphism theorem in `relIndex` form: for `K` normal and of finite relative
index in `H`, the index `[(H ⊔ K) : H]` equals `[K : K ⊓ H]`. -/
lemma relIndex_sup_eq_relIndex_of_normal {G : Type*} [Group G] (H K : Subgroup G) [K.Normal]
    (hfin : K.relIndex H ≠ 0) : H.relIndex (H ⊔ K) = H.relIndex K := by
  have e1 : H.relIndex K * K.relIndex H = (H ⊓ K).relIndex (H ⊔ K) := by
    rw [← Subgroup.inf_relIndex_right (H := H) (K := K),
      ← Subgroup.relIndex_sup_right (H := H) (K := K),
      Subgroup.relIndex_mul_relIndex (H := H ⊓ K) (K := K) (L := H ⊔ K) inf_le_right le_sup_right]
  have e2 : K.relIndex H * H.relIndex (H ⊔ K) = (H ⊓ K).relIndex (H ⊔ K) := by
    rw [← Subgroup.inf_relIndex_left (H := H) (K := K),
      Subgroup.relIndex_mul_relIndex (H := H ⊓ K) (K := H) (L := H ⊔ K) inf_le_left le_sup_left]
  have h1 : H.relIndex K * K.relIndex H = K.relIndex H * H.relIndex (H ⊔ K) := e1.trans e2.symm
  have h2 : K.relIndex H * H.relIndex (H ⊔ K) = K.relIndex H * H.relIndex K :=
    h1.symm.trans (mul_comm (H.relIndex K) (K.relIndex H))
  exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hfin) h2

/-- **Splitting of the norm index into the value-group part and the "unit" part.**

Let `v : A →* Multiplicative ℤ` be a surjective "valuation" on the multiplicative group of a field
`F` (`A = Fˣ`), let `w : B →* Multiplicative ℤ` be a surjective "valuation" on the units of a finite
extension `E` (`B = Eˣ`), and let `N : B →* A` be a homomorphism (the field norm) with
`v (N b) = (w b) ^ f` for a fixed `f > 0` (the inertia degree: `w` measures the valuation of `E`
normalised so that `v = f · w` on the image of `N`).  Then, provided the "unit part" is of finite
index,

`[A : N.range] = f · [v.ker : v.ker ⊓ N.range]`.

This is the elementary decomposition `[Fˣ : N_{E/F} Eˣ] = f · [U_F : U_F ∩ N Eˣ]` of the norm index,
used in the Herbrand-function approach to the local norm index theorem. -/
theorem index_range_eq_mul_relIndex_ker
    {A B : Type*} [Group A] [Group B]
    (v : A →* Multiplicative ℤ) (hv : Function.Surjective v)
    (w : B →* Multiplicative ℤ) (hw : Function.Surjective w)
    (N : B →* A) (f : ℕ) (_hf : 0 < f)
    (hN : ∀ b : B, v (N b) = (w b) ^ f)
    (hfin : v.ker.relIndex N.range ≠ 0) :
    N.range.index = f * (v.ker ⊓ N.range).relIndex v.ker := by
  classical
  let ψ : A →* Multiplicative (ZMod f) :=
    (Int.castAddHom (ZMod f)).toMultiplicative.comp v
  have hψ : ∀ a : A, ψ a = Multiplicative.ofAdd ((v a).toAdd : ZMod f) := fun a => rfl
  have hNle : N.range ≤ ψ.ker := by
    rintro _ ⟨b, rfl⟩
    rw [MonoidHom.mem_ker, hψ, ofAdd_eq_one, hN b, Int.toAdd_pow]
    push_cast
    rw [ZMod.natCast_self f, mul_zero]
  have hKle : v.ker ≤ ψ.ker := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    rw [hψ, ha]
    simp
  have hsuple : N.range ⊔ v.ker ≤ ψ.ker := sup_le hNle hKle
  have hsupge : ψ.ker ≤ N.range ⊔ v.ker := by
    intro a ha
    have h0 : ((v a).toAdd : ZMod f) = 0 := by
      have h := ha
      rw [MonoidHom.mem_ker, hψ, ofAdd_eq_one] at h
      exact h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    obtain ⟨n, hn⟩ := h0
    obtain ⟨b, hb⟩ := hw (Multiplicative.ofAdd n)
    have hvb : v (N b) = v a := by
      rw [hN b, hb]
      apply Multiplicative.toAdd.injective
      rw [Int.toAdd_pow]
      simp only [toAdd_ofAdd]
      rw [hn]
      ring
    have hmem : a * (N b)⁻¹ ∈ v.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hvb, mul_inv_cancel]
    have hae : a = (a * (N b)⁻¹) * (N b) := by group
    rw [hae, sup_comm]
    exact Subgroup.mul_mem_sup hmem ⟨b, rfl⟩
  have hker : ψ.ker = N.range ⊔ v.ker := le_antisymm hsupge hsuple
  have hψsurj : Function.Surjective ψ := fun y => by
    obtain ⟨n, hn⟩ := ZMod.intCast_surjective (n := f) (Multiplicative.toAdd y)
    obtain ⟨a, ha⟩ := hv (Multiplicative.ofAdd n)
    exact ⟨a, by rw [hψ, ha, toAdd_ofAdd, hn, ofAdd_toAdd]⟩
  have hcardψ : Nat.card (A ⧸ ψ.ker) = f := by
    rw [← Subgroup.index_eq_card, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr hψsurj, Subgroup.card_top,
      ← Nat.card_congr (Multiplicative.ofAdd (α := ZMod f)), Nat.card_zmod]
  have hle : N.range ≤ ψ.ker := le_trans le_sup_left hsuple
  have h1 : Nat.card (A ⧸ N.range)
      = Nat.card (ψ.ker ⧸ N.range.subgroupOf ψ.ker) * Nat.card (A ⧸ ψ.ker) := by
    rw [← Subgroup.index_eq_card (G := A) N.range,
      ← Subgroup.relIndex_mul_index hle,
      ← natCard_quotient_subgroupOf_eq_relIndex ψ.ker N.range,
      Subgroup.index_eq_card]
  have h2 : Nat.card (ψ.ker ⧸ N.range.subgroupOf ψ.ker) = N.range.relIndex v.ker := by
    rw [natCard_quotient_subgroupOf_eq_relIndex, hker]
    exact relIndex_sup_eq_relIndex_of_normal N.range v.ker hfin
  have h3 : N.range.relIndex v.ker = (v.ker ⊓ N.range).relIndex v.ker := by
    rw [Subgroup.relIndex, Subgroup.relIndex]
    congr 1
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [Subgroup.index_eq_card, h1, hcardψ, h2, h3, mul_comm]



/-- In a commutative group every subgroup is normal, so all `subgroupOf`s are normal and the
`MulEquiv` of Noether's second isomorphism theorem applies without any normality hypothesis. -/
lemma le_normalizer_of_comm {G : Type*} [CommGroup G] (H K : Subgroup G) :
    H ≤ Subgroup.normalizer K := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [show x * y * x⁻¹ = y from by rw [mul_comm x y, mul_assoc, mul_inv_cancel, mul_one]]

/-- **Noether's second isomorphism theorem in `relIndex` form, commutative case.**
For subgroups `H`, `K` of a commutative group, `[(H ⊔ K) : H] = [K : K ⊓ H]`, i.e.
`H.relIndex (H ⊔ K) = H.relIndex K`.  This is the form needed when the factor being quoted out is
not normal — it is available here because in a commutative group *every* subgroup is normal. -/
lemma relIndex_sup_eq_relIndex_of_comm {G : Type*} [CommGroup G] (H K : Subgroup G) :
    H.relIndex (H ⊔ K) = H.relIndex K := by
  rw [← natCard_quotient_subgroupOf_eq_relIndex (H ⊔ K) H, sup_comm,
    ← natCard_quotient_subgroupOf_eq_relIndex K H]
  exact (Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient K H
    (le_normalizer_of_comm K H)).toEquiv).symm

/-- **Splitting of a norm index into its value-group part and its "unit" part** (commutative case;
this is the case relevant to the units of a field, and needs no finiteness hypothesis).

Let `v : A →* Multiplicative ℤ` be a surjective "valuation" on the multiplicative group of a field
`F` (`A = Fˣ`), let `w : B →* Multiplicative ℤ` be a surjective "valuation" on the units of a finite
extension `E` (`B = Eˣ`), and let `N : B →* A` be a homomorphism (the field norm) with
`v (N b) = (w b) ^ f` for a fixed `f > 0` (the inertia degree).  Then

`[A : N.range] = f · [v.ker : v.ker ⊓ N.range]`.

This is the elementary decomposition `[Fˣ : N_{E/F} Eˣ] = f · [U_F : U_F ∩ N Eˣ]` of the norm index,
used in the Herbrand-function approach to the local norm index theorem, and it is the first step of
every route to the local norm index theorem. -/
theorem index_range_eq_mul_relIndex_ker_of_comm
    {A B : Type*} [CommGroup A] [CommGroup B]
    (v : A →* Multiplicative ℤ) (hv : Function.Surjective v)
    (w : B →* Multiplicative ℤ) (hw : Function.Surjective w)
    (N : B →* A) (f : ℕ) (hf : 0 < f)
    (hN : ∀ b : B, v (N b) = (w b) ^ f) :
    N.range.index = f * (v.ker ⊓ N.range).relIndex v.ker := by
  classical
  let ψ : A →* Multiplicative (ZMod f) :=
    (Int.castAddHom (ZMod f)).toMultiplicative.comp v
  have hψ : ∀ a : A, ψ a = Multiplicative.ofAdd ((v a).toAdd : ZMod f) := fun a => rfl
  have hNle : N.range ≤ ψ.ker := by
    rintro _ ⟨b, rfl⟩
    rw [MonoidHom.mem_ker, hψ, ofAdd_eq_one, hN b, Int.toAdd_pow]
    push_cast
    rw [ZMod.natCast_self f, mul_zero]
  have hKle : v.ker ≤ ψ.ker := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    rw [hψ, ha]
    simp
  have hsuple : N.range ⊔ v.ker ≤ ψ.ker := sup_le hNle hKle
  have hsupge : ψ.ker ≤ N.range ⊔ v.ker := by
    intro a ha
    have h0 : ((v a).toAdd : ZMod f) = 0 := by
      have h := ha
      rw [MonoidHom.mem_ker, hψ, ofAdd_eq_one] at h
      exact h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    obtain ⟨n, hn⟩ := h0
    obtain ⟨b, hb⟩ := hw (Multiplicative.ofAdd n)
    have hvb : v (N b) = v a := by
      rw [hN b, hb]
      apply Multiplicative.toAdd.injective
      rw [Int.toAdd_pow]
      simp only [toAdd_ofAdd]
      rw [hn]
      ring
    have hmem : a * (N b)⁻¹ ∈ v.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hvb, mul_inv_cancel]
    have hae : a = (a * (N b)⁻¹) * (N b) := by group
    rw [hae, sup_comm]
    exact Subgroup.mul_mem_sup hmem ⟨b, rfl⟩
  have hker : ψ.ker = N.range ⊔ v.ker := le_antisymm hsupge hsuple
  have hψsurj : Function.Surjective ψ := fun y => by
    obtain ⟨n, hn⟩ := ZMod.intCast_surjective (n := f) (Multiplicative.toAdd y)
    obtain ⟨a, ha⟩ := hv (Multiplicative.ofAdd n)
    exact ⟨a, by rw [hψ, ha, toAdd_ofAdd, hn, ofAdd_toAdd]⟩
  have hcardψ : Nat.card (A ⧸ ψ.ker) = f := by
    rw [← Subgroup.index_eq_card, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr hψsurj, Subgroup.card_top,
      ← Nat.card_congr (Multiplicative.ofAdd (α := ZMod f)), Nat.card_zmod]
  have hle : N.range ≤ ψ.ker := le_trans le_sup_left hsuple
  have h1 : Nat.card (A ⧸ N.range)
      = Nat.card (ψ.ker ⧸ N.range.subgroupOf ψ.ker) * Nat.card (A ⧸ ψ.ker) := by
    rw [← Subgroup.index_eq_card (G := A) N.range,
      ← Subgroup.relIndex_mul_index hle,
      ← natCard_quotient_subgroupOf_eq_relIndex ψ.ker N.range,
      Subgroup.index_eq_card]
  have h2 : Nat.card (ψ.ker ⧸ N.range.subgroupOf ψ.ker) = N.range.relIndex v.ker := by
    rw [natCard_quotient_subgroupOf_eq_relIndex, hker]
    exact relIndex_sup_eq_relIndex_of_comm N.range v.ker
  have h3 : N.range.relIndex v.ker = (v.ker ⊓ N.range).relIndex v.ker := by
    rw [Subgroup.relIndex, Subgroup.relIndex]
    congr 1
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [Subgroup.index_eq_card, h1, hcardψ, h2, h3, mul_comm]



end Commons.GroupTheory
