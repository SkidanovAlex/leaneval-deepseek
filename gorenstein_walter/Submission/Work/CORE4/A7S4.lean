/-
Area CORE4 of the Gorenstein--Walter project: the `A₇` §4 structure fact (Bender 1981, p. 226).

Deliverable: `Work.CORE4.A7S4`, i.e. `Work.GW2.A7S4Prop` (the `a7s4` input of the `CORE4` bundle):
in a finite group `E ≅ A₇`, for a four-group `V ≤ S` (`S` a Sylow `2`-subgroup), every involution
`s ∈ N_E(V)` and every subgroup `K ≤ N_E(V)` of order `3` inverted by `s` admit a *second* subgroup
`K' ≠ K` of order `3` inverted by `s`.

## Shape of the proof

* `Submission/Work/CORE4/A7S4Defs.lean` fixes the vocabulary: the two model four-groups
  `V₁ = ⟨(01)(23), (02)(13)⟩` and `V₂ = ⟨(01)(23), (01)(45)⟩` of `A₇`, the element level
  normaliser conditions `InN1P`/`InN2P`, and the explicit lists `n1Inv`, `n1Ord3`, `n2Inv`,
  `n2Ord3` of the order-`2` resp. order-`3` elements of `N_{A₇}(V₁)` and `N_{A₇}(V₂)`.
* `Submission/Work/CORE4/A7S4/{n1Inv_mem,n1Ord3_mem,n2Inv_mem,n2Ord3_mem,n2Check,partnerConj}.lean`
  contain the finite computations over `Equiv.Perm (Fin 7)`; the companion check for `V₁` is
  `n1Check'` below.
* Here: the two model cases (`claimV1`, `claimV2`), the classification of the four-groups of `A₇`
  into the conjugacy classes of `V₁` and `V₂` (`fourGroup_conj_V1_V2`, using that all involutions
  of `A₇` are conjugate and the "companion of `t`" computation `partnerConj`), invariance of
  `ClaimProp` under group isomorphisms (`claimProp_mulEquiv`), and the transport from an arbitrary
  `E ≃* A₇`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.A7S4Defs
import Submission.Work.AUTA7.A7.InvolutionsConjugate
import Submission.Work.CORE4.A7S4.n1Inv_mem
import Submission.Work.CORE4.A7S4.n1Ord3_mem
import Submission.Work.CORE4.A7S4.n2Inv_mem
import Submission.Work.CORE4.A7S4.n2Ord3_mem
import Submission.Work.CORE4.A7S4.n2Check
import Submission.Work.CORE4.A7S4.partnerConj

open scoped MatrixGroups

namespace Work.CORE4

open Equiv

/-! ## Coercion bridges -/

theorem coe_a7T : ((a7T : A7) : Equiv.Perm (Fin 7)) = tP := rfl

theorem coe_a7U : ((a7U : A7) : Equiv.Perm (Fin 7)) = uP := rfl

theorem coe_a7V : ((a7V : A7) : Equiv.Perm (Fin 7)) = vP := rfl

theorem VaMem_coe (x : A7) : VaMem x ↔ VaMemP (x : Equiv.Perm (Fin 7)) := by
  simp only [VaMem, VaMemP, coe_a7T, coe_a7U, Subtype.ext_iff, Subgroup.coe_mul,
    Subgroup.coe_one]

theorem VbMem_coe (x : A7) : VbMem x ↔ VbMemP (x : Equiv.Perm (Fin 7)) := by
  simp only [VbMem, VbMemP, coe_a7T, coe_a7V, Subtype.ext_iff, Subgroup.coe_mul,
    Subgroup.coe_one]

theorem mem_V1sub (x : A7) : x ∈ V1sub ↔ VaMem x := Iff.rfl

theorem mem_V2sub (x : A7) : x ∈ V2sub ↔ VbMem x := Iff.rfl



/-! ## Transport lemmas for `Inverts`, normalisers and cyclic subgroups -/

section Transport

variable {G H : Type*} [Group G] [Group H]

theorem inverts_map_iff (φ : G ≃* H) (s : G) (K : Subgroup G) :
    Work.GW2.Inverts (φ s) (K.map φ.toMonoidHom) ↔ Work.GW2.Inverts s K := by
  constructor
  · intro h x hx
    have h1 := h (φ x) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    show s * x * s⁻¹ = x⁻¹
    apply φ.injective
    rw [map_mul, map_mul, map_inv, h1, map_inv]
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    show φ s * φ x * (φ s)⁻¹ = (φ x)⁻¹
    rw [← map_mul, ← map_inv, ← map_mul, h x hx, map_inv]

theorem mem_normalizer_map_iff (φ : G ≃* H) (V : Subgroup G) (x : G) :
    φ x ∈ Subgroup.normalizer ((V.map φ.toMonoidHom : Subgroup H) : Set H) ↔
      x ∈ Subgroup.normalizer (V : Set G) := by
  have hcv : Subgroup.comap φ.toMonoidHom (V.map φ.toMonoidHom) = V := by
    ext y
    simp only [Subgroup.mem_comap, Subgroup.mem_map]
    constructor
    · rintro ⟨v, hv, hvφ⟩
      rwa [φ.injective.eq_iff.mp hvφ.symm]
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hcomap : Subgroup.comap φ.toMonoidHom
      (Subgroup.normalizer ((V.map φ.toMonoidHom : Subgroup H) : Set H)) =
        Subgroup.normalizer (V : Set G) := by
    have h := Subgroup.comap_normalizer_eq_of_le_range (f := φ.toMonoidHom)
      (H := V.map φ.toMonoidHom) (Subgroup.map_le_range φ.toMonoidHom V)
    rwa [hcv] at h
  constructor
  · intro hx
    have hx' : x ∈ Subgroup.comap φ.toMonoidHom
        (Subgroup.normalizer ((V.map φ.toMonoidHom : Subgroup H) : Set H)) := by
      rw [Subgroup.mem_comap]
      exact hx
    rwa [hcomap] at hx'
  · intro hx
    have hx' : x ∈ Subgroup.comap φ.toMonoidHom
        (Subgroup.normalizer ((V.map φ.toMonoidHom : Subgroup H) : Set H)) := by
      rwa [hcomap]
    rw [Subgroup.mem_comap] at hx'
    exact hx'

end Transport

section Cyc

variable {G : Type*} [Group G]

theorem inverts_zpowers_iff (s k : G) :
    Work.GW2.Inverts s (Subgroup.zpowers k) ↔ s * k * s⁻¹ = k⁻¹ := by
  constructor
  · intro h
    exact h k (Subgroup.mem_zpowers k)
  · intro h x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hk : (MulAut.conj s) k = k⁻¹ := (MulAut.conj_apply s k).trans h
    calc s * k ^ m * s⁻¹ = (MulAut.conj s) (k ^ m) := (MulAut.conj_apply s (k ^ m)).symm
      _ = ((MulAut.conj s) k) ^ m := map_zpow (MulAut.conj s) k m
      _ = (k⁻¹) ^ m := by rw [hk]
      _ = (k ^ m)⁻¹ := inv_zpow k m

theorem exists_zpowers_eq_of_card_three [Finite G] (K : Subgroup G) (hK : Nat.card K = 3) :
    ∃ k ∈ K, orderOf k = 3 ∧ K = Subgroup.zpowers k := by
  have hne : K ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hK
    exact absurd hK (by norm_num)
  obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hcoe : orderOf (k : G) = orderOf k := orderOf_injective K.subtype K.subtype_injective k
  have hdvd : orderOf k ∣ 3 := by
    rw [← hK]
    exact orderOf_dvd_natCard k
  have hne1 : orderOf k ≠ 1 := fun h => hk1 (orderOf_eq_one_iff.mp h)
  have h3 : orderOf k = 3 := by
    rcases Nat.Prime.eq_one_or_self_of_dvd (p := 3) (by norm_num) (orderOf k) hdvd with h | h
    · exact absurd h hne1
    · exact h
  refine ⟨(k : G), k.2, ?_, ?_⟩
  · rw [hcoe]; exact h3
  · refine (Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers (k : G)) (K := K)
      (Subgroup.zpowers_le.mpr k.2) ?_).symm
    rw [Nat.card_zpowers, hcoe, h3, hK]

end Cyc

/-! ## `ClaimProp` is invariant under group isomorphisms -/

theorem map_comap_eq_of_surjective {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    (K : Subgroup H) : (Subgroup.comap φ.toMonoidHom K).map φ.toMonoidHom = K :=
  Subgroup.map_comap_eq_self (by rintro y -; exact ⟨φ.symm y, by simp⟩)

theorem card_comap_eq {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (K : Subgroup H) :
    Nat.card ↥(Subgroup.comap φ.toMonoidHom K) = Nat.card ↥K := by
  rw [← Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective (K := Subgroup.comap φ.toMonoidHom K),
    map_comap_eq_of_surjective φ K]

theorem claimProp_mulEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (V : Subgroup G) :
    ClaimProp H (V.map φ.toMonoidHom) ↔ ClaimProp G V := by
  constructor
  · intro h s hs hs2 K hK hKcard hInv
    have hs' : φ s ∈ Subgroup.normalizer ((V.map φ.toMonoidHom : Subgroup H) : Set H) :=
      (mem_normalizer_map_iff φ V s).mpr hs
    have hs2' : orderOf (φ s) = 2 :=
      (orderOf_injective φ.toMonoidHom φ.injective s).trans hs2
    have hK' : K.map φ.toMonoidHom ≤
        Subgroup.normalizer ((V.map φ.toMonoidHom : Subgroup H) : Set H) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact (mem_normalizer_map_iff φ V x).mpr (hK hx)
    have hcard' : Nat.card ↥(K.map φ.toMonoidHom) = 3 := by
      rw [Subgroup.card_map_of_injective φ.injective]; exact hKcard
    have hInv' : Work.GW2.Inverts (φ s) (K.map φ.toMonoidHom) := (inverts_map_iff φ s K).mpr hInv
    obtain ⟨K'', hK''le, hK''card, hK''ne, hK''inv⟩ :=
      h (φ s) hs' hs2' (K.map φ.toMonoidHom) hK' hcard' hInv'
    refine ⟨Subgroup.comap φ.toMonoidHom K'', ?_, ?_, ?_, ?_⟩
    · intro y hy
      rw [Subgroup.mem_comap] at hy
      exact (mem_normalizer_map_iff φ V y).mp (hK''le hy)
    · rw [card_comap_eq φ K'']; exact hK''card
    · intro hcon
      apply hK''ne
      rw [← map_comap_eq_of_surjective φ K'', hcon]
    · exact (inverts_map_iff φ s (Subgroup.comap φ.toMonoidHom K'')).mp
        (by rwa [map_comap_eq_of_surjective φ K''])
  · intro h s hs hs2 K hK hKcard hInv
    set x : G := φ.symm s with hx
    have hφx : φ x = s := by simp [hx]
    have hmem : x ∈ Subgroup.normalizer (V : Set G) := by
      rw [← mem_normalizer_map_iff φ V x, hφx]; exact hs
    have hord : orderOf x = 2 := by
      have h1 : orderOf x = orderOf s := by
        rw [← hφx]
        exact (orderOf_injective φ.toMonoidHom φ.injective x).symm
      rw [h1, hs2]
    have hKcomap : Subgroup.comap φ.toMonoidHom K ≤ Subgroup.normalizer (V : Set G) := by
      intro y hy
      rw [Subgroup.mem_comap] at hy
      exact (mem_normalizer_map_iff φ V y).mp (hK hy)
    have hcardcomap : Nat.card ↥(Subgroup.comap φ.toMonoidHom K) = 3 := by
      rw [card_comap_eq φ K]; exact hKcard
    have hinvcomap : Work.GW2.Inverts x (Subgroup.comap φ.toMonoidHom K) := by
      refine (inverts_map_iff φ x (Subgroup.comap φ.toMonoidHom K)).mp ?_
      rw [map_comap_eq_of_surjective φ K, hφx]
      exact hInv
    obtain ⟨L, hLle, hLcard, hLne, hLinv⟩ :=
      h x hmem hord (Subgroup.comap φ.toMonoidHom K) hKcomap hcardcomap hinvcomap
    refine ⟨L.map φ.toMonoidHom, ?_, ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      exact (mem_normalizer_map_iff φ V z).mpr (hLle hz)
    · rw [Subgroup.card_map_of_injective φ.injective]; exact hLcard
    · intro hcon
      apply hLne
      refine Subgroup.map_injective (f := φ.toMonoidHom) φ.injective ?_
      rw [hcon, map_comap_eq_of_surjective φ K]
    · have h2 : Work.GW2.Inverts (φ x) (L.map φ.toMonoidHom) := (inverts_map_iff φ x L).mpr hLinv
      rwa [hφx] at h2

/-! ## The `N(V₁)` companion check

The remaining finite check (`n1Check`) is a decidable statement over the *two explicit lists*
`n1Inv` and `n1Ord3` (the `21` involutions and the `26` elements of order `3` of `N_{A₇}(V₁)`); it
is cheap (`21 × 26` pairs), as opposed to the checks over the whole of `Equiv.Perm (Fin 7)`, which
are done in `Submission/Work/CORE4/A7S4/n1Inv_mem.lean`, `n1Ord3_mem.lean`, `n2Inv_mem.lean`,
`n2Ord3_mem.lean` and `partnerConj.lean`. -/

/-- The `N(V₁)` companion check, decided by expanding the two explicit lists. -/
private theorem n1Check' : ∀ s : Equiv.Perm (Fin 7), s ∈ n1Inv →
    ∀ k : Equiv.Perm (Fin 7), k ∈ n1Ord3 → s * k * s⁻¹ = k⁻¹ →
    ∃ k' : Equiv.Perm (Fin 7), k' ∈ n1Ord3 ∧ InN1P k' ∧ Equiv.Perm.sign k' = 1 ∧
      k' * k' * k' = 1 ∧ k' ≠ 1 ∧ s * k' * s⁻¹ = k'⁻¹ ∧ k' ≠ k ∧ k' ≠ k * k := by
  intro s hs k hk h
  simp only [n1Inv, Finset.mem_insert, Finset.mem_singleton] at hs
  simp only [n1Ord3, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact absurd h (by decide)
        | exact ⟨(Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 3 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 2 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 2 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 3 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 1 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 3 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 1 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 2 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)), by decide⟩ | exact ⟨(Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5 : Equiv.Perm (Fin 7)), by decide⟩

/-! ## The model four-groups: normaliser bridges and the claim on them -/

theorem VaMem_conj_iff (x y : A7) :
    VaMem (x * y * x⁻¹) ↔
      VaMemP ((x : Equiv.Perm (Fin 7)) * (y : Equiv.Perm (Fin 7)) * (x : Equiv.Perm (Fin 7))⁻¹) := by
  rw [VaMem_coe, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]

theorem VbMem_conj_iff (x y : A7) :
    VbMem (x * y * x⁻¹) ↔
      VbMemP ((x : Equiv.Perm (Fin 7)) * (y : Equiv.Perm (Fin 7)) * (x : Equiv.Perm (Fin 7))⁻¹) := by
  rw [VbMem_coe, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]

theorem mem_normalizer_V1sub (x : A7) :
    x ∈ Subgroup.normalizer (V1sub : Set A7) ↔ InN1P (x : Equiv.Perm (Fin 7)) := by
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff] at h
    exact ⟨(VaMem_conj_iff x a7T).mp (h a7T |>.mp (by rw [mem_V1sub]; exact Or.inr (Or.inl rfl))),
      (VaMem_conj_iff x a7U).mp (h a7U |>.mp (by rw [mem_V1sub]; exact Or.inr (Or.inr (Or.inl rfl)))),
      (VaMem_conj_iff x (a7T * a7U)).mp
        (h (a7T * a7U) |>.mp (by rw [mem_V1sub]; exact Or.inr (Or.inr (Or.inr rfl))))⟩
  · intro h
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      rw [mem_V1sub] at hz
      show VaMem (x * z * x⁻¹)
      rcases hz with rfl | rfl | rfl | rfl
      · rw [mul_one, mul_inv_cancel]; exact Or.inl rfl
      · exact (VaMem_conj_iff x a7T).mpr h.1
      · exact (VaMem_conj_iff x a7U).mpr h.2.1
      · exact (VaMem_conj_iff x (a7T * a7U)).mpr h.2.2
    · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]

theorem mem_normalizer_V2sub (x : A7) :
    x ∈ Subgroup.normalizer (V2sub : Set A7) ↔ InN2P (x : Equiv.Perm (Fin 7)) := by
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff] at h
    exact ⟨(VbMem_conj_iff x a7T).mp (h a7T |>.mp (by rw [mem_V2sub]; exact Or.inr (Or.inl rfl))),
      (VbMem_conj_iff x a7V).mp (h a7V |>.mp (by rw [mem_V2sub]; exact Or.inr (Or.inr (Or.inl rfl)))),
      (VbMem_conj_iff x (a7T * a7V)).mp
        (h (a7T * a7V) |>.mp (by rw [mem_V2sub]; exact Or.inr (Or.inr (Or.inr rfl))))⟩
  · intro h
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      rw [mem_V2sub] at hz
      show VbMem (x * z * x⁻¹)
      rcases hz with rfl | rfl | rfl | rfl
      · rw [mul_one, mul_inv_cancel]; exact Or.inl rfl
      · exact (VbMem_conj_iff x a7T).mpr h.1
      · exact (VbMem_conj_iff x a7V).mpr h.2.1
      · exact (VbMem_conj_iff x (a7T * a7V)).mpr h.2.2
    · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]

theorem mem_zpowers_of_order_three {G : Type*} [Group G] {k x : G} (hk : orderOf k = 3)
    (hx : x ∈ Subgroup.zpowers k) : x = 1 ∨ x = k ∨ x = k * k := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← hm]
  have hk3 : k ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat, ← hk, pow_orderOf_eq_one]
  rw [zpow_eq_zpow_emod m hk3]
  have h2 : 0 ≤ m % 3 := Int.emod_nonneg m (by norm_num)
  have h3 : m % 3 < 3 := Int.emod_lt_of_pos m (by norm_num)
  have hb : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hb with h | h | h
  · left; rw [h]; simp
  · right; left; rw [h]; simp
  · right; right; rw [h]; simp [pow_two, mul_assoc]

theorem cond_inv_of (s : A7) (hs2 : orderOf s = 2) (hsN : InN1P (s : Equiv.Perm (Fin 7))) :
    N1InvCond (s : Equiv.Perm (Fin 7)) := by
  refine ⟨?_, ?_, ?_, hsN⟩
  · have h : s ^ 2 = 1 := by rw [← hs2, pow_orderOf_eq_one]
    have h2 := congrArg (fun z : A7 => (z : Equiv.Perm (Fin 7))) h
    simpa [Subgroup.coe_pow, pow_two] using h2
  · intro h
    have hs1 : s = 1 := Subtype.ext h
    rw [hs1, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  · exact Equiv.Perm.mem_alternatingGroup.mp s.2

theorem cond_inv_of_V2 (s : A7) (hs2 : orderOf s = 2) (hsN : InN2P (s : Equiv.Perm (Fin 7))) :
    N2InvCond (s : Equiv.Perm (Fin 7)) := by
  refine ⟨?_, ?_, ?_, hsN⟩
  · have h : s ^ 2 = 1 := by rw [← hs2, pow_orderOf_eq_one]
    have h2 := congrArg (fun z : A7 => (z : Equiv.Perm (Fin 7))) h
    simpa [Subgroup.coe_pow, pow_two] using h2
  · intro h
    have hs1 : s = 1 := Subtype.ext h
    rw [hs1, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  · exact Equiv.Perm.mem_alternatingGroup.mp s.2

theorem cond_ord3_of (k : A7) (hk : orderOf k = 3) (hkN : InN1P (k : Equiv.Perm (Fin 7))) :
    N1Ord3Cond (k : Equiv.Perm (Fin 7)) := by
  have hsign : Equiv.Perm.sign (k : Equiv.Perm (Fin 7)) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp k.2
  refine ⟨?_, ?_, ?_, hsign, hkN⟩
  · have h : k ^ 3 = 1 := by rw [← hk, pow_orderOf_eq_one]
    have h2 := congrArg (fun z : A7 => (z : Equiv.Perm (Fin 7))) h
    simpa [Subgroup.coe_pow, pow_three, mul_assoc] using h2
  · intro h
    have h' : k = 1 := Subtype.ext h
    rw [h', orderOf_one] at hk
    exact absurd hk (by norm_num)
  · intro h
    have h2 : (k : Equiv.Perm (Fin 7)) ^ 2 = 1 := by rw [pow_two]; exact h
    have h3 : orderOf (k : Equiv.Perm (Fin 7)) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    have h4 : orderOf (k : Equiv.Perm (Fin 7)) = 3 := by
      rw [Subgroup.orderOf_coe]; exact hk
    rw [h4] at h3
    norm_num at h3

theorem cond_ord3_of_V2 (k : A7) (hk : orderOf k = 3) (hkN : InN2P (k : Equiv.Perm (Fin 7))) :
    N2Ord3Cond (k : Equiv.Perm (Fin 7)) := by
  have hsign : Equiv.Perm.sign (k : Equiv.Perm (Fin 7)) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp k.2
  refine ⟨?_, ?_, ?_, hsign, hkN⟩
  · have h : k ^ 3 = 1 := by rw [← hk, pow_orderOf_eq_one]
    have h2 := congrArg (fun z : A7 => (z : Equiv.Perm (Fin 7))) h
    simpa [Subgroup.coe_pow, pow_three, mul_assoc] using h2
  · intro h
    have h' : k = 1 := Subtype.ext h
    rw [h', orderOf_one] at hk
    exact absurd hk (by norm_num)
  · intro h
    have h2 : (k : Equiv.Perm (Fin 7)) ^ 2 = 1 := by rw [pow_two]; exact h
    have h3 : orderOf (k : Equiv.Perm (Fin 7)) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    have h4 : orderOf (k : Equiv.Perm (Fin 7)) = 3 := by
      rw [Subgroup.orderOf_coe]; exact hk
    rw [h4] at h3
    norm_num at h3

theorem claimV1 : ClaimProp A7 V1sub := by
  intro s hs hs2 K hK hKcard hInv
  have hsN : InN1P (s : Equiv.Perm (Fin 7)) := (mem_normalizer_V1sub s).mp hs
  have hsin : (s : Equiv.Perm (Fin 7)) ∈ n1Inv := A7S4.n1Inv_mem _ (cond_inv_of s hs2 hsN)
  obtain ⟨k, hkK, hkord, hKeq⟩ := exists_zpowers_eq_of_card_three K hKcard
  have hkN : InN1P (k : Equiv.Perm (Fin 7)) := (mem_normalizer_V1sub k).mp (hK hkK)
  have hkin : (k : Equiv.Perm (Fin 7)) ∈ n1Ord3 := A7S4.n1Ord3_mem _ (cond_ord3_of k hkord hkN)
  have hkinv : (s : Equiv.Perm (Fin 7)) * (k : Equiv.Perm (Fin 7)) * (s : Equiv.Perm (Fin 7))⁻¹
      = (k : Equiv.Perm (Fin 7))⁻¹ := by
    have h := hInv k hkK
    have h2 := congrArg (fun z : A7 => (z : Equiv.Perm (Fin 7))) h
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h2
  obtain ⟨k', hk'in, hk'N, hk'sgn, hk'3, hk'1, hk'inv, hk'k, hk'k2⟩ :=
    n1Check' _ hsin _ hkin hkinv
  set kA : A7 := ⟨k', Equiv.Perm.mem_alternatingGroup.mpr hk'sgn⟩ with hkAdef
  have hcoe : (kA : Equiv.Perm (Fin 7)) = k' := rfl
  refine ⟨Subgroup.zpowers kA, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le, mem_normalizer_V1sub, hcoe]; exact hk'N
  · rw [Nat.card_zpowers, ← Subgroup.orderOf_coe kA, hcoe]
    have h3 : (k' : Equiv.Perm (Fin 7)) ^ 3 = 1 := by
      calc (k' : Equiv.Perm (Fin 7)) ^ 3 = k' * (k' * k') := pow_three k'
        _ = (k' * k') * k' := by rw [mul_assoc]
        _ = 1 := hk'3
    exact orderOf_eq_prime h3 hk'1
  · intro hcon
    have hmem : kA ∈ Subgroup.zpowers k := by
      have h1 : kA ∈ Subgroup.zpowers kA := Subgroup.mem_zpowers kA
      rwa [hcon, hKeq] at h1
    rcases mem_zpowers_of_order_three hkord hmem with h | h | h
    · apply hk'1
      simp [← hcoe, h]
    · apply hk'k
      simp [← hcoe, h]
    · apply hk'k2
      simp [← hcoe, h]
  · rw [inverts_zpowers_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hcoe]
    exact hk'inv

theorem claimV2 : ClaimProp A7 V2sub := by
  intro s hs hs2 K hK hKcard hInv
  have hsN : InN2P (s : Equiv.Perm (Fin 7)) := (mem_normalizer_V2sub s).mp hs
  have hsin : (s : Equiv.Perm (Fin 7)) ∈ n2Inv := A7S4.n2Inv_mem _ (cond_inv_of_V2 s hs2 hsN)
  obtain ⟨k, hkK, hkord, hKeq⟩ := exists_zpowers_eq_of_card_three K hKcard
  have hkN : InN2P (k : Equiv.Perm (Fin 7)) := (mem_normalizer_V2sub k).mp (hK hkK)
  have hkin : (k : Equiv.Perm (Fin 7)) ∈ n2Ord3 := A7S4.n2Ord3_mem _ (cond_ord3_of_V2 k hkord hkN)
  have hkinv : (s : Equiv.Perm (Fin 7)) * (k : Equiv.Perm (Fin 7)) * (s : Equiv.Perm (Fin 7))⁻¹
      = (k : Equiv.Perm (Fin 7))⁻¹ := by
    have h := hInv k hkK
    have h2 := congrArg (fun z : A7 => (z : Equiv.Perm (Fin 7))) h
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h2
  obtain ⟨k', hk'in, hk'N, hk'sgn, hk'3, hk'1, hk'inv, hk'k, hk'k2⟩ :=
    A7S4.n2Check _ hsin _ hkin hkinv
  set kA : A7 := ⟨k', Equiv.Perm.mem_alternatingGroup.mpr hk'sgn⟩ with hkAdef
  have hcoe : (kA : Equiv.Perm (Fin 7)) = k' := rfl
  refine ⟨Subgroup.zpowers kA, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le, mem_normalizer_V2sub, hcoe]; exact hk'N
  · rw [Nat.card_zpowers, ← Subgroup.orderOf_coe kA, hcoe]
    have h3 : (k' : Equiv.Perm (Fin 7)) ^ 3 = 1 := by
      calc (k' : Equiv.Perm (Fin 7)) ^ 3 = k' * (k' * k') := pow_three k'
        _ = (k' * k') * k' := by rw [mul_assoc]
        _ = 1 := hk'3
    exact orderOf_eq_prime h3 hk'1
  · intro hcon
    have hmem : kA ∈ Subgroup.zpowers k := by
      have h1 : kA ∈ Subgroup.zpowers kA := Subgroup.mem_zpowers kA
      rwa [hcon, hKeq] at h1
    rcases mem_zpowers_of_order_three hkord hmem with h | h | h
    · apply hk'1
      simp [← hcoe, h]
    · apply hk'k
      simp [← hcoe, h]
    · apply hk'k2
      simp [← hcoe, h]
  · rw [inverts_zpowers_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hcoe]
    exact hk'inv

/-! ## Classification of the four-groups of `A₇` and the final assembly -/

theorem mulAut_conj_apply' {G : Type*} [Group G] (g x : G) :
    (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := MulAut.conj_apply g x

theorem commute_of_sq_eq_one {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * (a * b) = 1) : a * b = b * a := by
  have ha' : a = a⁻¹ := eq_inv_of_mul_eq_one_left ha
  have hb' : b = b⁻¹ := eq_inv_of_mul_eq_one_left hb
  calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left hab
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [← hb', ← ha']

theorem card_V1sub : Nat.card ↥V1sub = 4 := by
  have hset : (V1sub : Set A7) = ↑({1, a7T, a7U, a7T * a7U} : Finset A7) := by
    ext x
    simp [mem_V1sub, VaMem]
  rw [show Nat.card ↥V1sub = (V1sub : Set A7).ncard from Nat.card_coe_set_eq _,
    hset, Set.ncard_coe_finset]
  decide

theorem card_V2sub : Nat.card ↥V2sub = 4 := by
  have hset : (V2sub : Set A7) = ↑({1, a7T, a7V, a7T * a7V} : Finset A7) := by
    ext x
    simp [mem_V2sub, VbMem]
  rw [show Nat.card ↥V2sub = (V2sub : Set A7).ncard from Nat.card_coe_set_eq _,
    hset, Set.ncard_coe_finset]
  decide

theorem tmul_tmul_u : a7T * (a7T * a7U) = a7U := by
  calc a7T * (a7T * a7U) = a7T * a7T * a7U := by rw [mul_assoc]
    _ = a7U := by rw [Work.A7.a7Invol_mul_self, one_mul]

theorem tmul_tmul_v : a7T * (a7T * a7V) = a7V := by
  calc a7T * (a7T * a7V) = a7T * a7T * a7V := by rw [mul_assoc]
    _ = a7V := by rw [Work.A7.a7Invol_mul_self, one_mul]

theorem fourGroup_conj_V1_V2 (V : Subgroup A7) (hV : Work.GW2.IsFourGroup V) :
    ∃ g : A7, V.map (MulAut.conj g).toMonoidHom = V1sub ∨
      V.map (MulAut.conj g).toMonoidHom = V2sub := by
  have hne : V ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥V = 4 := hV.1
    rw [h, Subgroup.card_bot] at h1
    norm_num at h1
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hx1' : (x : A7) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hx2' : (x : A7) * (x : A7) = 1 := by
    have h := hV.2 (x : A7) x.2
    rwa [pow_two] at h
  obtain ⟨g₁, hg₁⟩ := isConj_iff.mp
    (Work.AUTA7.A7.InvolutionsConjugate hx2' Work.A7.a7Invol_mul_self hx1' Work.A7.a7Invol_ne_one)
  set W : Subgroup A7 := V.map (MulAut.conj g₁).toMonoidHom with hWdef
  have hW4 : Nat.card ↥W = 4 := by
    rw [hWdef, Subgroup.card_map_of_injective (MulAut.conj g₁).injective]
    exact hV.1
  have htW : a7T ∈ W := by
    rw [hWdef, Subgroup.mem_map]
    exact ⟨(x : A7), x.2, by rw [mulAut_conj_apply']; exact hg₁⟩
  have hWsq : ∀ z ∈ W, z * z = 1 := by
    intro z hz
    rw [hWdef, Subgroup.mem_map] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    rw [mulAut_conj_apply']
    have hv2 : v * v = 1 := by
      have h := hV.2 v hv
      rwa [pow_two] at h
    calc g₁ * v * g₁⁻¹ * (g₁ * v * g₁⁻¹) = g₁ * (v * v) * g₁⁻¹ := by group
      _ = 1 := by rw [hv2]; group
  have hw : ∃ w : A7, w ∈ W ∧ w ≠ 1 ∧ w ≠ a7T := by
    by_contra hc
    push Not at hc
    set S : Set A7 := (({1, a7T} : Finset A7) : Set A7) with hSdef
    have hsub : (W : Set A7) ⊆ S := by
      intro y hy
      by_cases hy1 : y = 1
      · rw [hy1, hSdef]; simp
      · have hy2 := hc y hy hy1
        rw [hy2, hSdef]; simp
    have hle := Set.ncard_le_ncard hsub (Set.toFinite S)
    have h2 : S.ncard = 2 := by
      rw [hSdef, Set.ncard_coe_finset]
      decide
    rw [h2] at hle
    have hWn : (W : Set A7).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]; exact hW4
    omega
  obtain ⟨w, hwW, hw1, hwt⟩ := hw
  have hw2 : w * w = 1 := hWsq w hwW
  have ht2 : a7T * a7T = 1 := Work.A7.a7Invol_mul_self
  have hwt2 : w * a7T * (w * a7T) = 1 := hWsq (w * a7T) (Subgroup.mul_mem _ hwW htW)
  have hcomm : w * a7T = a7T * w := commute_of_sq_eq_one hw2 ht2 hwt2
  have hsign : Equiv.Perm.sign (w : Equiv.Perm (Fin 7)) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp w.2
  have hcommP : (w : Equiv.Perm (Fin 7)) * tP = tP * (w : Equiv.Perm (Fin 7)) := by
    have h2 := congrArg (fun z : A7 => (z : Equiv.Perm (Fin 7))) hcomm
    simp only [Subgroup.coe_mul, a7T, Work.A7.coe_a7Invol, tP, Work.A7.dswapPerm,
      Work.A7.a7InvolPerm] at h2 ⊢
    exact h2
  have hw1P : (w : Equiv.Perm (Fin 7)) ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hwtP : (w : Equiv.Perm (Fin 7)) ≠ tP := by
    intro h
    apply hwt
    have h2 : (w : Equiv.Perm (Fin 7)) = (a7T : Equiv.Perm (Fin 7)) := by
      rw [coe_a7T]; exact h
    exact Subtype.ext h2
  have hw2P : (w : Equiv.Perm (Fin 7)) * (w : Equiv.Perm (Fin 7)) = 1 := by
    have := congrArg (fun z : A7 => (z : Equiv.Perm (Fin 7))) hw2
    simpa [Subgroup.coe_mul, Subgroup.coe_one] using this
  obtain ⟨h, _hhct, hhsgn, hht, hhcase⟩ :=
    A7S4.partnerConj _ ⟨hw2P, hw1P, hwtP, hsign, hcommP⟩
  set hA : A7 := ⟨h, Equiv.Perm.mem_alternatingGroup.mpr hhsgn⟩ with hhA
  have hhcoec : (hA : Equiv.Perm (Fin 7)) = h := rfl
  have hhtA : hA * a7T * hA⁻¹ = a7T := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hhcoec, coe_a7T]
    exact hht
  have htw : a7T ∈ W.map (MulAut.conj hA).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨a7T, htW, by rw [mulAut_conj_apply']; exact hhtA⟩
  have hlemma : ∀ (U : Subgroup A7) (c : A7), Nat.card ↥U = 4 → hA * w * hA⁻¹ = c →
      (∀ y : A7, y ∈ U → y = 1 ∨ y = a7T ∨ y = c ∨ y = a7T * c) →
      W.map (MulAut.conj hA).toMonoidHom = U := by
    intro U c hU4 hz hcar
    have hwmem : hA * w * hA⁻¹ ∈ W.map (MulAut.conj hA).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨w, hwW, ?_⟩
      rw [mulAut_conj_apply']
    refine (Subgroup.eq_of_le_of_card_ge (H := U)
      (K := W.map (MulAut.conj hA).toMonoidHom) ?_ ?_).symm
    · intro y hy
      rcases hcar y hy with rfl | rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact htw
      · rw [← hz]; exact hwmem
      · rw [← hz]
        exact Subgroup.mul_mem _ htw hwmem
    · rw [Subgroup.card_map_of_injective (MulAut.conj hA).injective, hW4, hU4]
  have hbridge : V.map (MulAut.conj (hA * g₁)).toMonoidHom =
      W.map (MulAut.conj hA).toMonoidHom := by
    rw [hWdef, Subgroup.map_map]
    have hfun : ((MulAut.conj hA).toMonoidHom.comp (MulAut.conj g₁).toMonoidHom) =
        (MulAut.conj (hA * g₁)).toMonoidHom := by
      ext x
      simp only [mulAut_conj_apply', MonoidHom.comp_apply]
      group
    rw [hfun]
  rcases hhcase with huw | huw | hvw | hvw
  · -- h w h⁻¹ = uP
    have hz : hA * w * hA⁻¹ = a7U := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hhcoec, coe_a7U]
      exact huw
    refine ⟨hA * g₁, Or.inl ?_⟩
    rw [hbridge, hlemma V1sub a7U card_V1sub hz]
    intro y hy
    exact (mem_V1sub y).mp hy
  · -- h w h⁻¹ = tP * uP
    have hz : hA * w * hA⁻¹ = a7T * a7U := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hhcoec, coe_a7T, coe_a7U]
      exact huw
    refine ⟨hA * g₁, Or.inl ?_⟩
    rw [hbridge, hlemma V1sub (a7T * a7U) card_V1sub hz]
    intro y hy
    rcases (mem_V1sub y).mp hy with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (by rw [h, tmul_tmul_u])))
    · exact Or.inr (Or.inr (Or.inl h))
  · -- h w h⁻¹ = vP
    have hz : hA * w * hA⁻¹ = a7V := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hhcoec, coe_a7V]
      exact hvw
    refine ⟨hA * g₁, Or.inr ?_⟩
    rw [hbridge, hlemma V2sub a7V card_V2sub hz]
    intro y hy
    exact (mem_V2sub y).mp hy
  · -- h w h⁻¹ = tP * vP
    have hz : hA * w * hA⁻¹ = a7T * a7V := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hhcoec, coe_a7T, coe_a7V]
      exact hvw
    refine ⟨hA * g₁, Or.inr ?_⟩
    rw [hbridge, hlemma V2sub (a7T * a7V) card_V2sub hz]
    intro y hy
    rcases (mem_V2sub y).mp hy with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (by rw [h, tmul_tmul_v])))
    · exact Or.inr (Or.inr (Or.inl h))

theorem isFourGroup_map {G H : Type*} [Group G] [Group H] (φ : G ≃* H) {V : Subgroup G}
    (h : Work.GW2.IsFourGroup V) : Work.GW2.IsFourGroup (V.map φ.toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · rw [Subgroup.card_map_of_injective φ.injective]; exact h.1
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
    rw [← map_pow, h.2 v hv, map_one]

theorem a7Claim_of_isFourGroup (V : Subgroup A7) (hV : Work.GW2.IsFourGroup V) :
    ClaimProp A7 V := by
  obtain ⟨g, hg | hg⟩ := fourGroup_conj_V1_V2 V hV
  · have h1 : ClaimProp A7 (V.map (MulAut.conj g).toMonoidHom) := by rw [hg]; exact claimV1
    exact (claimProp_mulEquiv (MulAut.conj g) V).mp h1
  · have h1 : ClaimProp A7 (V.map (MulAut.conj g).toMonoidHom) := by rw [hg]; exact claimV2
    exact (claimProp_mulEquiv (MulAut.conj g) V).mp h1

/-- The `A₇` §4 structure fact of p. 226 (Bender 1981). -/
theorem A7S4 : Work.GW2.A7S4Prop := by
  intro E _ _ hφ S V _hVS hV4
  obtain ⟨φ⟩ := hφ
  have hV4' : Work.GW2.IsFourGroup (V.map φ.toMonoidHom) := isFourGroup_map φ hV4
  have h1 : ClaimProp A7 (V.map φ.toMonoidHom) := a7Claim_of_isFourGroup _ hV4'
  exact (claimProp_mulEquiv φ V).mp h1

end Work.CORE4
