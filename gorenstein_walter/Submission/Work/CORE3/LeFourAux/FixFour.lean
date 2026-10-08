import Mathlib
import Submission.Work.ASM.Defs

/-!
# `FixFour`

Let `V` be a Klein four-group (a subgroup of order `4` all of whose elements are
involutions).  Suppose `x, z ∈ N_G(V)` both fix a common non-identity element `v ∈ V`
(`x v x⁻¹ = v = z v z⁻¹`) and neither centralizes `V`.  Then `x` and `z` induce the SAME
automorphism of `V`.

The reason: `V` is elementary abelian of order `4`; the conjugation action of `N_G(V)`
on `V` realises the automorphism group of `V` as the permutation group of the three
non-identity elements.  An element fixing `v ≠ 1` acts as a permutation fixing `v`; being
non-trivial it must swap the two remaining non-identity elements — the unique such
permutation.  Hence both `x` and `z` act as that transposition.

We package the argument through two elementary lemmas about four-groups:
* `fourGroup_mem_cases'`: a four-group with two named distinct non-identity elements
  `a, b` is exactly `{1, a, b, a * b}`;
* `conj_fixes_second`: if `g ∈ N_G(V)` fixes `v ≠ 1` but does not centralize `V`, then
  it moves a second non-identity element `a` to `v * a` (the transposition).
-/

namespace Work.CORE3.LeFourAux

open Subgroup

/-- A four-group with two named distinct non-identity elements `a`, `b` consists exactly of
`1`, `a`, `b` and `a * b`.  (Local version of `Work.FUS.fourGroup_mem_cases` that does not
require `Finite G`: finiteness of `V` is derived from `Nat.card V = 4`.) -/
lemma fourGroup_mem_cases' {G : Type*} [Group G] {V : Subgroup G}
    (hV : Work.GW2.IsFourGroup V) {a b : G}
    (ha : a ∈ V) (hb : b ∈ V) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    ∀ y ∈ V, y = 1 ∨ y = a ∨ y = b ∨ y = a * b := by
  classical
  have hfin : Finite V := by
    have h0 : Nat.card V ≠ 0 := by rw [hV.1]; norm_num
    exact (Nat.card_ne_zero.mp h0).2
  haveI : Fintype V := Fintype.ofFinite V
  have hcard : Fintype.card V = 4 := by rw [← Nat.card_eq_fintype_card]; exact hV.1
  have haa : a * a = 1 := by simpa [pow_two] using hV.2 a ha
  have hbb : b * b = 1 := by simpa [pow_two] using hV.2 b hb
  have habV : a * b ∈ V := V.mul_mem ha hb
  have h1 : a * b ≠ 1 := by
    intro h
    exact hab (mul_left_cancel (by rw [h, haa]))
  have h2 : a * b ≠ a := by
    intro h
    exact hb1 (mul_left_cancel (by rw [h, mul_one]))
  have h3 : a * b ≠ b := by
    intro h
    exact ha1 (mul_right_cancel (by rw [one_mul, h]))
  have hS : ({1, a, b, a * b} : Finset G).card = 4 := by
    rw [Finset.card_eq_four]
    exact ⟨1, a, b, a * b, ha1.symm, hb1.symm, h1.symm, hab, h2.symm, h3.symm, rfl⟩
  have hsub : ({1, a, b, a * b} : Finset G) ⊆ (Finset.univ : Finset V).image Subtype.val := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz | hz
    · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, hz.symm⟩
    · exact Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_univ _, hz.symm⟩
    · exact Finset.mem_image.mpr ⟨⟨b, hb⟩, Finset.mem_univ _, hz.symm⟩
    · exact Finset.mem_image.mpr ⟨⟨a * b, habV⟩, Finset.mem_univ _, hz.symm⟩
  have hcard' : ((Finset.univ : Finset V).image Subtype.val).card = 4 := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ, hcard]
  have heq : ({1, a, b, a * b} : Finset G) = (Finset.univ : Finset V).image Subtype.val :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard', hS])
  intro y hy
  have hy' : y ∈ ({1, a, b, a * b} : Finset G) := by
    rw [heq]
    exact Finset.mem_image.mpr ⟨⟨y, hy⟩, Finset.mem_univ _, rfl⟩
  simpa using hy'

/-- If `g ∈ N_G(V)` fixes the non-identity element `v ∈ V` and does not centralize the
four-group `V`, then `g` acts on any second non-identity element `a` (distinct from `v`)
as the transposition fixing `v`: it sends `a` to `v * a`. -/
lemma conj_fixes_second {G : Type*} [Group G] {V : Subgroup G}
    (hV : Work.GW2.IsFourGroup V) {v a : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (ha : a ∈ V) (ha1 : a ≠ 1) (hanev : a ≠ v)
    {g : G} (hgN : g ∈ Subgroup.normalizer (V : Set G)) (hgv : g * v * g⁻¹ = v)
    (hgC : g ∉ Subgroup.centralizer (V : Set G)) :
    g * a * g⁻¹ = v * a := by
  classical
  have henum := fourGroup_mem_cases' hV hv ha hv1 ha1 (Ne.symm hanev)
  have hgaV : g * a * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hgN a).mp ha
  rcases henum (g * a * g⁻¹) hgaV with h | h | h | h
  · -- `g a g⁻¹ = 1` forces `a = 1`, impossible.
    exfalso
    have h' : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [h] at h'
    exact ha1 (by simpa using h')
  · -- `g a g⁻¹ = v` together with `g v g⁻¹ = v` forces `a = v`, impossible.
    exfalso
    have h' : g * a * g⁻¹ = g * v * g⁻¹ := by rw [h, hgv]
    exact hanev (mul_left_cancel (mul_right_cancel h'))
  · -- `g a g⁻¹ = a` would make `g` centralize `V`, impossible.
    exfalso
    apply hgC
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rcases henum t ht with ht1 | ht1 | ht1 | ht1
    · subst ht1; simp
    · subst ht1
      simpa [mul_assoc] using (congrArg (· * g) hgv).symm
    · subst ht1
      simpa [mul_assoc] using (congrArg (· * g) h).symm
    · subst ht1
      have hkey : g * (v * a) * g⁻¹ = v * a := by
        rw [show g * (v * a) * g⁻¹ = (g * v * g⁻¹) * (g * a * g⁻¹) by group, hgv, h]
      simpa [mul_assoc] using (congrArg (· * g) hkey).symm
  · exact h

theorem FixFour {G : Type} [Group G] {V : Subgroup G}
    (hV : Work.GW2.IsFourGroup V) {x z v : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hxv : x * v * x⁻¹ = v) (hzv : z * v * z⁻¹ = v)
    (hxN : x ∈ Subgroup.normalizer (V : Set G)) (hzN : z ∈ Subgroup.normalizer (V : Set G))
    (hxC : x ∉ Subgroup.centralizer (V : Set G)) (hzC : z ∉ Subgroup.centralizer (V : Set G)) :
    ∀ w : G, w ∈ V → x * w * x⁻¹ = z * w * z⁻¹ := by
  classical
  -- `V` is finite, of order `4`.
  have hfin : Finite V := by
    have h0 : Nat.card V ≠ 0 := by rw [hV.1]; norm_num
    exact (Nat.card_ne_zero.mp h0).2
  haveI : Fintype V := Fintype.ofFinite V
  have hcard : Fintype.card V = 4 := by rw [← Nat.card_eq_fintype_card]; exact hV.1
  -- Produce a second non-identity element `a` of `V`, distinct from `v`.
  set vv : V := ⟨v, hv⟩ with hvvdef
  have hvne : vv ≠ 1 := fun h => hv1 (Subtype.ext_iff.mp h)
  obtain ⟨aa, haa⟩ : ∃ aa : V, aa ∉ ({1, vv} : Finset V) := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hsub : (Finset.univ : Finset V) ⊆ ({1, vv} : Finset V) := fun u _ => h u
    have hle := Finset.card_le_card hsub
    have h2 : ({1, vv} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem (show (1 : V) ∉ ({vv} : Finset V) by
            simp only [Finset.mem_singleton]; exact fun hc => hvne hc.symm), Finset.card_singleton]
    rw [Finset.card_univ, hcard, h2] at hle
    omega
  have haa1v : aa ≠ (1 : V) := fun h => haa (by simp [h])
  have haanevv : aa ≠ vv := fun h => haa (by simp [h])
  have haa1 : (aa : G) ≠ 1 := fun h => haa1v (Subtype.ext h)
  have haanev : (aa : G) ≠ v := fun h => haanevv (Subtype.ext h)
  have ha : (aa : G) ∈ V := aa.2
  -- Enumerate the elements of `V`: they are `1`, `v`, `a` and `v * a`.
  have henum := fourGroup_mem_cases' hV hv ha hv1 haa1 (Ne.symm haanev)
  -- Both `x` and `z` act as the transposition on the second non-identity element.
  have hxa : x * (aa : G) * x⁻¹ = v * (aa : G) :=
    conj_fixes_second hV hv hv1 ha haa1 haanev hxN hxv hxC
  have hza : z * (aa : G) * z⁻¹ = v * (aa : G) :=
    conj_fixes_second hV hv hv1 ha haa1 haanev hzN hzv hzC
  intro w hw
  rcases henum w hw with h | h | h | h
  · subst h; simp
  · subst h; rw [hxv, hzv]
  · subst h; rw [hxa, hza]
  · subst h
    calc x * (v * (aa : G)) * x⁻¹ = (x * v * x⁻¹) * (x * (aa : G) * x⁻¹) := by group
      _ = (z * v * z⁻¹) * (z * (aa : G) * z⁻¹) := by rw [hxv, hxa, hzv, hza]
      _ = z * (v * (aa : G)) * z⁻¹ := by group

end Work.CORE3.LeFourAux
