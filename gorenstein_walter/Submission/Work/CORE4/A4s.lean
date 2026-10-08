import Mathlib
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.NotA7Defs
import Submission.Work.CORE4.A7S4
import Submission.Work.CORE4.A4sDefs
import Submission.Work.CORE4.A4sChecks

namespace Work.CORE4

open Equiv

/-! ## Transport of the property along a group isomorphism

`A4sVProp G V` (`Submission/Work/CORE4/A4sDefs.lean`) is the statement of `A4s` at a four-group
`V ≤ G`: for every involution `s ∈ N_G(V)` and every `K ≤ C_G(V)` of order `3` inverted by `s`
there is `e ∈ C_G(s)` with `K^e ≤ N_G(V)` and `K^e ≠ K`.  This section shows that
`A4sVProp H (V.map φ) → A4sVProp G V` for an isomorphism `φ : G ≃* H`; the special case
`φ = MulAut.conj g` is the conjugation invariance used to reduce to the model four-groups. -/

/-- The image of a cyclic subgroup under a homomorphism. -/
theorem map_zpowers_eq {G H : Type*} [Group G] [Group H] (f : G →* H) (x : G) :
    (Subgroup.zpowers x).map f = Subgroup.zpowers (f x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← hn, map_zpow]
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
  · intro hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Subgroup.mem_map.mpr ⟨x ^ n, Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩,
      by rw [← hn, map_zpow]⟩

/-- `conjSub` is natural in the conjugating element. -/
theorem map_conjSub {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (e : G) (K : Subgroup G) :
    (Work.GW2.conjSub e K).map φ.toMonoidHom =
      Work.GW2.conjSub (φ e) (K.map φ.toMonoidHom) := by
  unfold Work.GW2.conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

/-- A centraliser is carried into the centraliser of the image subgroup. -/
theorem map_le_centralizer {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    {V K : Subgroup G} (h : K ≤ Subgroup.centralizer (V : Set G)) :
    K.map φ.toMonoidHom ≤ Subgroup.centralizer ((V.map φ.toMonoidHom : Subgroup H) : Set H) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hz
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp (h hx) v hv]

/-- `A4sVProp` pulls back along a group isomorphism. -/
theorem A4sVProp_of_map {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (V : Subgroup G)
    (h : A4sVProp H (V.map φ.toMonoidHom)) : A4sVProp G V := by
  intro s hs hs2 K hK hKcard hInv
  have hs' : φ s ∈ Subgroup.normalizer ((V.map φ.toMonoidHom : Subgroup H) : Set H) :=
    (mem_normalizer_map_iff φ V s).mpr hs
  have hs2' : orderOf (φ s) = 2 := (orderOf_injective φ.toMonoidHom φ.injective s).trans hs2
  have hK' := map_le_centralizer φ hK
  have hcard' : Nat.card ↥(K.map φ.toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective φ.injective]; exact hKcard
  have hInv' : Work.GW2.Inverts (φ s) (K.map φ.toMonoidHom) := (inverts_map_iff φ s K).mpr hInv
  obtain ⟨e, hes, heN, hene⟩ := h (φ s) hs' hs2' (K.map φ.toMonoidHom) hK' hcard' hInv'
  have h2 := map_conjSub φ (φ.symm e) K
  rw [φ.apply_symm_apply] at h2
  refine ⟨φ.symm e, ?_, ?_, ?_⟩
  · apply φ.injective
    rw [map_mul, map_mul, φ.apply_symm_apply, hes]
  · intro y hy
    have hy' : φ y ∈ Work.GW2.conjSub e (K.map φ.toMonoidHom) := by
      rw [← h2]
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    exact (mem_normalizer_map_iff φ V y).mp (heN hy')
  · intro hcon
    apply hene
    rw [← h2, hcon]

/-! ## The model case `V = V₁ = ⟨(0 1)(2 3), (0 2)(1 3)⟩`

`C_{A₇}(V₁) = V₁ × ⟨(4 5 6)⟩` has a unique subgroup of order `3`, namely `⟨k10⟩` with
`k10 = (4 5 6)`; the finite checks in `Submission/Work/CORE4/A4sChecks.lean` (`cent1`, `cent2`,
`check1`) supply the elementary facts. -/

/-- `k10 = (4 5 6)` as an element of `A₇`. -/
def k1A : A7 := ⟨k10, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

/-- `⟨a * a⟩ = ⟨a⟩` for an element of order `3`. -/
theorem zpowers_mul_self_eq_self_zpowers {G : Type*} [Group G] {a : G} (ha : a * a * a = 1) :
    Subgroup.zpowers (a * a) = Subgroup.zpowers a := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers a)
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_zpowers_iff.mpr ⟨2, ?_⟩
    show (a * a) ^ (2 : ℤ) = a
    rw [zpow_ofNat]
    calc (a * a) ^ 2 = a * a * a * a := by simp [pow_two, mul_assoc]
      _ = (a * a * a) * a := by simp [mul_assoc]
      _ = 1 * a := by rw [ha]
      _ = a := by simp

/-- **`A4s` at the model four-group `V₁`.** -/
theorem a4sVProp_V1 : A4sVProp A7 V1sub := by
  intro s hs hs2 K hK hKcard hInv
  have hsN : InN1P (s : Equiv.Perm (Fin 7)) := (mem_normalizer_V1sub s).mp hs
  have hsin : (s : Equiv.Perm (Fin 7)) ∈ n1Inv := A7S4.n1Inv_mem _ (cond_inv_of s hs2 hsN)
  obtain ⟨k, hkK, hkord, hKeq⟩ := exists_zpowers_eq_of_card_three K hKcard
  have hkC : k ∈ Subgroup.centralizer (V1sub : Set A7) := hK hkK
  have hkN : k ∈ Subgroup.normalizer (V1sub : Set A7) :=
    Subgroup.centralizer_le_normalizer _ hkC
  have hkNP : InN1P (k : Equiv.Perm (Fin 7)) := (mem_normalizer_V1sub k).mp hkN
  have hkin : (k : Equiv.Perm (Fin 7)) ∈ n1Ord3 :=
    A7S4.n1Ord3_mem _ (cond_ord3_of k hkord hkNP)
  have hkt' : a7T * k = k * a7T :=
    Subgroup.mem_centralizer_iff.mp hkC a7T ((mem_V1sub a7T).mpr (Or.inr (Or.inl rfl)))
  have hku' : a7U * k = k * a7U :=
    Subgroup.mem_centralizer_iff.mp hkC a7U ((mem_V1sub a7U).mpr (Or.inr (Or.inr (Or.inl rfl))))
  have hkt : (k : Equiv.Perm (Fin 7)) * tP = tP * (k : Equiv.Perm (Fin 7)) := by
    have h2 := congrArg (fun z : A7 => (z : Equiv.Perm (Fin 7))) hkt'
    simpa only [Subgroup.coe_mul, coe_a7T] using h2.symm
  have hku : (k : Equiv.Perm (Fin 7)) * uP = uP * (k : Equiv.Perm (Fin 7)) := by
    have h2 := congrArg (fun z : A7 => (z : Equiv.Perm (Fin 7))) hku'
    simpa only [Subgroup.coe_mul, coe_a7U] using h2.symm
  -- `k ∈ C(V₁)` of order `3` forces `⟨k⟩ = ⟨k10⟩`
  have hkk : (k : Equiv.Perm (Fin 7)) ∈ k1List := Work.CORE4.A4s.cent1 _ hkin hkt hku
  simp only [k1List, Finset.mem_insert, Finset.mem_singleton] at hkk
  have hkcases : k = k1A ∨ k = k1A * k1A := by
    rcases hkk with h | h
    · left; exact Subtype.ext h
    · right; refine Subtype.ext ?_; rw [Subgroup.coe_mul]; exact h
  have hKz : K = Subgroup.zpowers k1A := by
    rcases hkcases with h | h
    · rw [hKeq, h]
    · rw [hKeq, h, zpowers_mul_self_eq_self_zpowers (a := k1A) (by decide)]
  have hk1K : k1A ∈ K := by rw [hKz]; exact Subgroup.mem_zpowers k1A
  have hinv10 : (s : Equiv.Perm (Fin 7)) * k10 * (s : Equiv.Perm (Fin 7))⁻¹ = k10⁻¹ := by
    have h := hInv k1A hk1K
    have h2 := congrArg (fun z : A7 => (z : Equiv.Perm (Fin 7))) h
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, k1A] using h2
  obtain ⟨e, _hewit, hecomm, hesign, heN1, hene1, hene2⟩ :=
    Work.CORE4.A4s.check1 (s : Equiv.Perm (Fin 7)) hsin hinv10
  have hk1ord : orderOf k1A = 3 := by
    apply orderOf_eq_prime (p := 3) <;> decide
  set eA : A7 := ⟨e, Equiv.Perm.mem_alternatingGroup.mpr hesign⟩ with heA
  have heAc : ((eA : A7) : Equiv.Perm (Fin 7)) = e := rfl
  have hq_ne_one : e * k10 * e⁻¹ ≠ 1 := by
    intro h1
    have h2 : k10 = 1 := by
      calc k10 = e⁻¹ * (e * k10 * e⁻¹) * e := by group
        _ = 1 := by rw [h1]; simp
    exact absurd h2 (by decide)
  refine ⟨eA, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, heAc]
    exact hecomm
  · rw [hKz, Work.GW2.conjSub, map_zpowers_eq, Subgroup.zpowers_le, mem_normalizer_V1sub]
    show InN1P ((eA * k1A * eA⁻¹ : A7) : Equiv.Perm (Fin 7))
    rw [show ((eA * k1A * eA⁻¹ : A7) : Equiv.Perm (Fin 7)) = e * k10 * e⁻¹ from rfl]
    exact heN1
  · intro hcon
    rw [hKz, Work.GW2.conjSub, map_zpowers_eq] at hcon
    have hmem : eA * k1A * eA⁻¹ ∈ Subgroup.zpowers k1A := by
      rw [← hcon]; exact Subgroup.mem_zpowers _
    rcases mem_zpowers_of_order_three hk1ord hmem with h1 | h1 | h1
    · have h2 : e * k10 * e⁻¹ = 1 := by
        have h3 := congrArg (fun z : A7 => (z : Equiv.Perm (Fin 7))) h1
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one, heAc, k1A] using h3
      exact hq_ne_one h2
    · have h2 : e * k10 * e⁻¹ = k10 := by
        have h3 := congrArg (fun z : A7 => (z : Equiv.Perm (Fin 7))) h1
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, heAc, k1A] using h3
      exact hene1 h2
    · have h2 : e * k10 * e⁻¹ = k10 * k10 := by
        have h3 := congrArg (fun z : A7 => (z : Equiv.Perm (Fin 7))) h1
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, heAc, k1A] using h3
      exact hene2 h2

/-! ## All four-groups of `A₇`

`A₇` has two classes of four-groups (`fourGroup_conj_V1_V2`), represented by `V₁` and `V₂`.
The `V₂` case is *vacuous*: `C_{A₇}(V₂) = V₂` has order `4`, so it contains no subgroup of
order `3`; indeed it contains no element of order `3` (`cent2`, applied to the order-`3` elements
`n2Ord3` of `N_{A₇}(V₂)`, of which there are `8`). -/

/-- **`A4s` at every four-group of `A₇`.** -/
theorem a4sVProp_A7 (V : Subgroup A7) (hV : Work.GW2.IsFourGroup V) : A4sVProp A7 V := by
  intro s hs hs2 K hK hKcard hInv
  obtain ⟨g, hg | hg⟩ := fourGroup_conj_V1_V2 V hV
  · have hmodel : A4sVProp A7 (V.map (MulAut.conj g).toMonoidHom) := hg ▸ a4sVProp_V1
    exact A4sVProp_of_map (MulAut.conj g) V hmodel s hs hs2 K hK hKcard hInv
  · exfalso
    have hKconj : K.map (MulAut.conj g).toMonoidHom ≤
        Subgroup.centralizer ((V.map (MulAut.conj g).toMonoidHom : Subgroup A7) : Set A7) :=
      map_le_centralizer (MulAut.conj g) hK
    rw [hg] at hKconj
    have hcardconj : Nat.card ↥(K.map (MulAut.conj g).toMonoidHom) = 3 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]; exact hKcard
    obtain ⟨k, hkK, hkord, -⟩ :=
      exists_zpowers_eq_of_card_three (K.map (MulAut.conj g).toMonoidHom) hcardconj
    have hkc : k ∈ Subgroup.centralizer (V2sub : Set A7) := hKconj hkK
    have hkN : k ∈ Subgroup.normalizer (V2sub : Set A7) :=
      Subgroup.centralizer_le_normalizer _ hkc
    have hkin : (k : Equiv.Perm (Fin 7)) ∈ n2Ord3 :=
      A7S4.n2Ord3_mem _ (cond_ord3_of_V2 k hkord ((mem_normalizer_V2sub k).mp hkN))
    have hkt : (k : Equiv.Perm (Fin 7)) * tP = tP * (k : Equiv.Perm (Fin 7)) := by
      have h2 := congrArg (fun z : A7 => (z : Equiv.Perm (Fin 7)))
        (Subgroup.mem_centralizer_iff.mp hkc a7T ((mem_V2sub a7T).mpr (Or.inr (Or.inl rfl))))
      simpa only [Subgroup.coe_mul, coe_a7T] using h2.symm
    have hkv : (k : Equiv.Perm (Fin 7)) * vP = vP * (k : Equiv.Perm (Fin 7)) := by
      have h2 := congrArg (fun z : A7 => (z : Equiv.Perm (Fin 7)))
        (Subgroup.mem_centralizer_iff.mp hkc a7V
          ((mem_V2sub a7V).mpr (Or.inr (Or.inr (Or.inl rfl)))))
      simpa only [Subgroup.coe_mul, coe_a7V] using h2.symm
    exact Work.CORE4.A4s.cent2 _ hkin ⟨hkt, hkv⟩

/-- **A4s (pure `A₇` fact, design pass 15).**  For a four-group `V`, an involution `s ∈ N(V)` and
`K ≤ C(V)` of order 3 inverted by `s`, some `e ∈ C(s)` moves `K` to a *different* subgroup of
`N(V)`.

Statement copied verbatim from `_design_gw/Core15C4.lean` / `NotA7Defs.lean`:

    A7S4ConjProp = ∀ (E) [Group E] [Finite E], Nonempty (E ≃* alternatingGroup (Fin 7)) →
      ∀ V : Subgroup E, IsFourGroup V → ∀ s ∈ normalizer (V : Set E), orderOf s = 2 →
        ∀ K : Subgroup E, K ≤ centralizer (V : Set E) → Nat.card K = 3 → Inverts s K →
          ∃ e : E, e * s = s * e ∧ conjSub e K ≤ normalizer (V : Set E) ∧ conjSub e K ≠ K

GAP-verified (`_design_gw/gw15_a7conj.g`, `gw15_a7conj.out`): 18 configurations in `A₇` and 18 in
`3.A₇`, 0 failures.  Model witness: `V = ⟨(12)(34),(13)(24)⟩`, `s = (12)(56)`, `K = ⟨(567)⟩`,
`e = (15)(26)(374)`, giving `K^e = ⟨(123)⟩`.

It can be proved like `A7S4Prop` (`Submission/Work/CORE4/A7S4.lean`, PROVED, which uses explicit
normaliser lists for the two classes of four-groups and `decide`): enumerate the involutions `s` of
`N(V)`, the order-3 subgroups `K ≤ C(V)` inverted by `s`, and find `e ∈ C(s)`; transport by
conjugacy (the property is conjugation-invariant).  NOTE: `A₇` has **two** classes of subgroups of
order 3 (3-cycles and products of two disjoint 3-cycles), so `K^e ≤ N(V)` is *not* automatic from
`K ∈ N(V)`. -/
theorem A4s : Work.CORE4.C15.A7S4ConjProp := by
  intro E _inst _fin hφ V hV
  obtain ⟨φ⟩ := hφ
  have hV' : Work.GW2.IsFourGroup (V.map φ.toMonoidHom) := isFourGroup_map φ hV
  exact A4sVProp_of_map φ V (a4sVProp_A7 (V.map φ.toMonoidHom) hV')

end Work.CORE4
