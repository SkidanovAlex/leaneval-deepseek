import Mathlib
import Submission.Work.CORE2B.HallPerPrime_aux

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# AREA CORE2B — the per-prime step, auxiliary form: `O_p(U) ∩ C_G(s) ≤ O(C_G(s))`

Bender (J. Algebra 70 (1981) 216–228), proof of Theorem 2.10, p. 222:

> With `p` a prime, assume `1 ≠ X := C_{O_p(U)}(s) ≠ O_p(U)`.  By 1.1(ii), some `t`-invariant
> `S_p`-subgroup `P` of `O(C_G(s))` contains `X`.

The step that this file supplies is the containment `X ≤ O(C_G(s))` (and in fact the stronger
statement that *every* subgroup of odd order of `C_G(s)` lies in `O(C_G(s))`).

Mathematically: `s ∈ S − S₀` is an involution, and in the minimal counterexample all involutions
are conjugate, so `C_G(s) = C_G(t)^g = H^g` for some `g` with `g·s·g⁻¹ = t`.  Bender p. 219
(`T.split`, from the Frobenius normal `p`-complement theorem) gives `H = C_G(t) = O(H) ⊔ S`, i.e.
`H/O(H)` is a `2`-group.  Conjugating, `C_G(s) = O(C_G(s))·(2-group)`, so a subgroup of odd order
of `C_G(s)` (like `O_p(U) ∩ C_G(s)`, which lies in `O_p(U) ⊆ U = O(H)`, of odd order) has trivial
image in the `2`-group `C_G(s)/O(C_G(s))`, hence lies in `O(C_G(s))`.

The formalisation replaces `O(C_G(s))` by the conjugate `φ(O(H))` of `O(H)`, where `φ = conj g⁻¹`
is the automorphism carrying `H` to `C_G(s)`; that conjugate is an odd normal subgroup of
`C_G(s)` and therefore lies in `O(C_G(s))` (maximality of the odd core).

The supporting lemmas are the general ones (`hallXodd_…`): odd subgroups of `U ⊔ S` with `S` a
`2`-group and `U` normal lie in `U` (relative-index argument), and odd-order normal subgroups lie
in `O(·)` (maximality of the odd core).
-/

/-! ## 1. General lemmas about odd-order subgroups -/

/-- If `U ◁ G` and `U ⊔ S = ⊤` with `S` a `2`-group, then every subgroup of odd order lies in
`U`: the relative index `U.relIndex X` divides both `|X|` (odd) and `|S|` (a power of `2`). -/
theorem hallXodd_le_of_sup_isPGroup {G : Type} [Group G] [Finite G] {U S X : Subgroup G}
    [U.Normal] (hUS : U ⊔ S = ⊤) (hS : IsPGroup 2 S) (hX : Odd (Nat.card X)) : X ≤ U := by
  have h1 : U.relIndex X ∣ U.index := Subgroup.relIndex_dvd_index_of_normal U X
  have hidx : U.index = U.relIndex S := by
    rw [← Subgroup.relIndex_top_right, ← hUS, Subgroup.relIndex_sup_left]
  have h2 : U.relIndex X ∣ U.relIndex S := hidx ▸ h1
  have h3 : U.relIndex X ∣ Nat.card S := h2.trans (Subgroup.relIndex_dvd_card U S)
  have h4 : U.relIndex X ∣ Nat.card X := Subgroup.relIndex_dvd_card U X
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥S)).mp hS
  have h5 : U.relIndex X ∣ 2 ^ n := hn ▸ h3
  have hnot : ¬ 2 ∣ Nat.card X := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hX
  have hcop : Nat.Coprime (2 ^ n) (Nat.card X) :=
    (Nat.prime_two.coprime_pow_of_not_dvd (m := n) hnot).symm
  exact Subgroup.relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop h5 h4)

/-- If `U ⊔ S = C` with `U ◁ C` and `S` a `2`-group, then every odd-order subgroup of `C` lies
in `U`.  (Reduction to the previous lemma inside the group `↥C`.) -/
theorem hallXodd_odd_subgroup_le_of_sup {G : Type} [Group G] [Finite G]
    {C U S : Subgroup G} (hUS : U ⊔ S = C) (hUn : (U.subgroupOf C).Normal)
    (hS : IsPGroup 2 S) : ∀ X : Subgroup G, X ≤ C → Odd (Nat.card X) → X ≤ U := by
  intro X hXC hXodd
  have hUle : U ≤ C := hUS ▸ le_sup_left
  have hSle : S ≤ C := hUS ▸ le_sup_right
  have hUS' : U.subgroupOf C ⊔ S.subgroupOf C = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hUle hSle, hUS, Subgroup.subgroupOf_self]
  have hS' : IsPGroup 2 (S.subgroupOf C) := hS.comap_subtype
  have hXcard : Nat.card (X.subgroupOf C) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXC).toEquiv
  have hXodd' : Odd (Nat.card (X.subgroupOf C)) := hXcard.symm ▸ hXodd
  have hX' : X.subgroupOf C ≤ U.subgroupOf C := by
    haveI : (U.subgroupOf C).Normal := hUn
    exact hallXodd_le_of_sup_isPGroup hUS' hS' hXodd'
  intro x hx
  have hmem : (⟨x, hXC hx⟩ : ↥C) ∈ X.subgroupOf C := Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_subgroupOf.mp (hX' hmem)

/-- A subgroup of odd order that is normal in `M` lies in the odd core `O(M) = oddCoreIn M`
(maximality of `O(M)` among normal odd-order subgroups). -/
theorem hallXodd_le_oddCoreIn_of_normal_of_odd {G : Type} [Group G] [Finite G]
    {X M : Subgroup G} (hXM : X ≤ M) (hn : (X.subgroupOf M).Normal) (hodd : Odd (Nat.card X)) :
    X ≤ Work.GW2.oddCoreIn M := by
  have hcard : Nat.card (X.subgroupOf M) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv
  have hodd' : Odd (Nat.card (X.subgroupOf M)) := hcard.symm ▸ hodd
  have hle : X.subgroupOf M ≤ Work.GW2.oddCore ↥M :=
    (Subgroup.normal_le_normalCore (N := X.subgroupOf M) (hN := hn)
      (H := sSup {N : Subgroup ↥M | N.Normal ∧ Odd (Nat.card N)})).mpr
      (le_sSup ⟨hn, hodd'⟩)
  rw [← Subgroup.map_subgroupOf_eq_of_le hXM]
  simpa [Work.GW2.oddCoreIn] using Subgroup.map_mono (f := M.subtype) hle

/-- Centralizers are carried to centralizers by a `MulEquiv`. -/
theorem hallXodd_map_centralizer {G H : Type} [Group G] [Group H] (e : G ≃* H) (A : Set G) :
    (Subgroup.centralizer A).map e.toMonoidHom = Subgroup.centralizer (e '' A) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rw [← hxy]
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    rintro b ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hy a ha]
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro a ha
    apply e.injective
    simp only [map_mul, e.apply_symm_apply]
    exact hx (e a) ⟨a, ha, rfl⟩

/-- A non-abelian simple group has no normal subgroup of index `2`. -/
theorem hallXodd_no_index_two {G : Type} [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G)
    (N : Subgroup G) (hN : N.Normal) : N.index ≠ 2 := by
  intro hidx
  haveI := hN
  rcases hctx.simple.eq_bot_or_eq_top_of_normal N with hbot | htop
  · -- `N = ⊥` forces `|G| = 2`, hence `G` is abelian, contradicting `hctx.nonab`
    rw [hbot, Subgroup.index_bot] at hidx
    have hcard : Nat.card G = 2 := hidx
    have hpow : ∀ x : G, x ^ 2 = 1 := by
      intro x
      have hdvd : orderOf x ∣ Nat.card G := orderOf_dvd_natCard x
      rw [hcard] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · rw [orderOf_eq_one_iff.mp h1, one_pow]
      · rw [← h2]; exact pow_orderOf_eq_one x
    have hcomm : ∀ a b : G, a * b = b * a := by
      intro a b
      have ha : a⁻¹ = a := by
        have h := hpow a; rw [pow_two] at h; exact inv_eq_of_mul_eq_one_right h
      have hb : b⁻¹ = b := by
        have h := hpow b; rw [pow_two] at h; exact inv_eq_of_mul_eq_one_right h
      have hab : (a * b)⁻¹ = a * b := by
        have h := hpow (a * b); rw [pow_two] at h; exact inv_eq_of_mul_eq_one_right h
      rw [← hab, mul_inv_rev, ha, hb]
    obtain ⟨a, b, hab⟩ := hctx.nonab
    exact hab (hcomm a b)
  · rw [htop] at hidx
    simp at hidx

/-! ## 2. The target lemma -/

/-- For `s ∈ S − S₀` and any prime `p`, the fixed points of `s` on `O_p(U)` lie in the odd core
of `C_G(s)` (in fact every subgroup of odd order of `C_G(s)` does). -/
theorem HallPerPrime_Xodd (T : Work.GW2.LocalToolkit) (G : Type) [Group G] [Finite G]
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (s : G)
    (hs : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0) (p : ℕ) (hp : Nat.Prime p) :
    Work.GW2.pCoreIn p B.U ⊓ Subgroup.centralizer ({s} : Set G) ≤
      Work.GW2.oddCoreIn (Subgroup.centralizer ({s} : Set G)) := by
  -- `S` is dihedral, so all involutions of `G` are conjugate (`T.fus`) and `C_G(t) = O(H) ⊔ S`
  -- (`T.split`).
  obtain ⟨n, hn2, hiso⟩ := S_dihedral_iso hCtx B
  have hs2 : orderOf s = 2 := orderOf_eq_two_of_mem_S_notMem_S0 hCtx B hs hs0
  have hno2 : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 :=
    fun N hN => hallXodd_no_index_two hCtx N hN
  obtain ⟨g, hg⟩ := isConj_iff.mp ((T.fus G (B.S) n hn2 hiso hno2).1 s B.t hs2 B.t_order)
  -- `hg : g * s * g⁻¹ = B.t`
  have hsplit : B.U ⊔ (B.S : Subgroup G) = B.H :=
    T.split G (B.S) n hn2 hiso B.t (B.S0_le B.t_mem) B.t_order (t_central_in_S B)
  -- the automorphism `φ = conj g⁻¹` carries `H = C_G(t)` to `C = C_G(s)`
  set φ : MulAut G := MulAut.conj g⁻¹ with hφdef
  have hφt : φ B.t = s := by
    rw [hφdef, MulAut.conj_apply, inv_inv, ← hg]
    group
  set C : Subgroup G := Subgroup.centralizer ({s} : Set G) with hCdef
  have hHmap : B.H.map φ.toMonoidHom = C := by
    show (Subgroup.centralizer ({B.t} : Set G)).map φ.toMonoidHom = C
    rw [hallXodd_map_centralizer φ ({B.t} : Set G), Set.image_singleton, hφt]
  have hUleH : B.U ≤ B.H := Subgroup.map_subtype_le _
  have hHU : B.H ≤ Subgroup.normalizer (B.U : Set G) := by
    have h := le_normalizer_map_subtype_local B.H (Work.GW2.oddCore ↥B.H)
      (Work.GW2.oddCore_normal ↥B.H)
    simpa [Work.GW2.BenderSetup.U, Work.GW2.oddCoreIn] using h
  have hUφ_le_C : B.U.map φ.toMonoidHom ≤ C := by
    rw [← hHmap]
    exact Subgroup.map_mono hUleH
  -- `φ(U)` is an odd-order normal subgroup of `C = C_G(s)`
  have hUn : ((B.U.map φ.toMonoidHom).subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hUφ_le_C]
    intro h k hh hk
    rw [Subgroup.mem_map] at hh
    obtain ⟨u, hu, hφu⟩ := hh
    have hk' : k ∈ B.H.map φ.toMonoidHom := by
      rw [hHmap]
      exact hk
    obtain ⟨w, hw, hφw⟩ := Subgroup.mem_map.mp hk'
    rw [← hφu, ← hφw]
    refine Subgroup.mem_map.mpr ⟨w * u * w⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hHU hw) u).mp hu
    · simp only [map_mul, map_inv]
  have hUS : B.U.map φ.toMonoidHom ⊔ (B.S : Subgroup G).map φ.toMonoidHom = C := by
    rw [← Subgroup.map_sup, hsplit, hHmap]
  have hSφ : IsPGroup 2 ((B.S : Subgroup G).map φ.toMonoidHom) :=
    IsPGroup.map B.S.isPGroup' φ.toMonoidHom
  -- the target subgroup is an odd-order subgroup of `C`
  have hXC : Work.GW2.pCoreIn p B.U ⊓ C ≤ C := inf_le_right
  have hXodd : Odd (Nat.card ↥(Work.GW2.pCoreIn p B.U ⊓ C)) := by
    have hXB : Work.GW2.pCoreIn p B.U ⊓ C ≤ B.U :=
      le_trans inf_le_left (in_le_self B.U p ∅).2.1
    exact Odd.of_dvd_nat (odd_card_U B) (Subgroup.card_dvd_of_le hXB)
  have hXle : Work.GW2.pCoreIn p B.U ⊓ C ≤ B.U.map φ.toMonoidHom :=
    hallXodd_odd_subgroup_le_of_sup hUS hUn hSφ _ hXC hXodd
  -- and `φ(U)` lies in the odd core of `C`
  have hUφodd : Odd (Nat.card ↥(B.U.map φ.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective φ.injective]
    exact odd_card_U B
  have hUφO : B.U.map φ.toMonoidHom ≤ Work.GW2.oddCoreIn C :=
    hallXodd_le_oddCoreIn_of_normal_of_odd hUφ_le_C hUn hUφodd
  exact le_trans hXle hUφO

end Work.CORE2B
