import Mathlib
import Submission.Work.Frobenius.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The cardinality of the Frobenius kernel

For a Frobenius complement `H ≤ G` the *Frobenius kernel*
`frobeniusKernel H = {1} ∪ (univ \ ⋃ g, H^g)`
is the identity together with all elements that are not conjugate into `H`
(`Work.Frobenius.frobeniusKernel`).  The main result of the area is that this set
is the carrier of a normal complement to `H`, but the *cardinality* of the set is
elementary and is what is proved here:

`Nat.card (frobeniusKernel H) = H.index`.

The argument is a count of the union of the conjugates of `H`.  Two conjugates of
`H` are either equal or meet trivially (`Work.Frobenius.Basic.inf_conj_smul_eq_bot_of_ne`),
so the union of the conjugates consists of `1` together with `H.index` pairwise
disjoint copies of `H \ {1}`; a natural bijection (recorded below) identifies the
latter with `(G ⧸ H) × (H \ {1})`.  Hence

`⋃ g, H^g = 1 + H.index * (Nat.card H - 1)`

and the kernel, being the complement of that union together with `1`, has
`Nat.card G - H.index * (Nat.card H - 1) = H.index` elements.

Everything here is self-contained: the helpers are `private` and live in the
sub-namespace `CardFrobeniusKernel`, so this module can be imported alongside any
other work in the area.
-/

open scoped Pointwise

namespace Work.Frobenius.Basic

noncomputable section

namespace CardFrobeniusKernel

variable {G : Type*} [Group G]

/-- Conjugation by an element of `H` fixes `H`. -/
private lemma conj_smul_self {H : Subgroup G} {d : G} (hd : d ∈ H) : MulAut.conj d • H = H := by
  ext y
  rw [Work.Frobenius.mem_conj_smul_iff]
  constructor
  · intro hy
    have : y = d * (d⁻¹ * y * d) * d⁻¹ := by group
    rw [this]
    exact H.mul_mem (H.mul_mem hd hy) (H.inv_mem hd)
  · intro hy
    exact H.mul_mem (H.mul_mem (H.inv_mem hd) hy) hd

/-- If `u ∈ H` is nontrivial and `d * u * d⁻¹ ∈ H`, then `d` normalises `H` at a
nontrivial element of `H`; the Frobenius condition forces `d ∈ H`. -/
private lemma mem_of_conj_mem {H : Subgroup G} (hH : IsFrobeniusComplement H) {d u : G}
    (hu : u ∈ H) (hune : u ≠ 1) (h : d * u * d⁻¹ ∈ H) : d ∈ H := by
  by_contra hd
  have hd' : d⁻¹ ∉ H := fun hc => hd (by simpa using H.inv_mem hc)
  have hmem : u ∈ H ⊓ (MulAut.conj d⁻¹ • H) := by
    refine Subgroup.mem_inf.mpr ⟨hu, ?_⟩
    rw [Work.Frobenius.mem_conj_smul_iff]
    simpa using h
  rw [hH.ti d⁻¹ hd', Subgroup.mem_bot] at hmem
  exact hune hmem

/-- Two conjugates of `H` which meet nontrivially are equal: if `y ≠ 1` lies in
`H^a ⊓ H^b` then `b⁻¹ * a ∈ H`, so that the two conjugating elements differ by an
element of `H`. -/
private lemma key {H : Subgroup G} (hH : IsFrobeniusComplement H) {a b y : G}
    (ha : y ∈ (MulAut.conj a • H : Set G)) (hb : y ∈ (MulAut.conj b • H : Set G))
    (hy : y ≠ 1) : b⁻¹ * a ∈ H := by
  have hu : a⁻¹ * y * a ∈ H := (Work.Frobenius.mem_conj_smul_iff' (g := a) (x := y)).mp ha
  have hw : b⁻¹ * y * b ∈ H := (Work.Frobenius.mem_conj_smul_iff' (g := b) (x := y)).mp hb
  have hune : a⁻¹ * y * a ≠ 1 := by
    intro hc
    apply hy
    calc y = a * (a⁻¹ * y * a) * a⁻¹ := by group
      _ = a * 1 * a⁻¹ := by rw [hc]
      _ = 1 := by group
  exact mem_of_conj_mem hH hu hune (by
    have hh : (b⁻¹ * a) * (a⁻¹ * y * a) * (b⁻¹ * a)⁻¹ = b⁻¹ * y * b := by group
    rw [hh]; exact hw)

/-- The union of all conjugates of `H`. -/
private def conjUn (H : Subgroup G) : Set G := ⋃ g : G, (MulAut.conj g • H : Set G)

/-- The explicit map `(G ⧸ H) × (H \ {1}) → ⋃ g, H^g`, sending the coset of `r` and
`h ≠ 1` to `r * h * r⁻¹`. -/
private def psi (H : Subgroup G) (p : (G ⧸ H) × {h : H // h ≠ 1}) : G :=
  Quotient.out p.1 * ((p.2 : H) : G) * (Quotient.out p.1)⁻¹

/-- The image of `psi` lies in the union of the conjugates, away from `1`. -/
private theorem psi_mem {H : Subgroup G} (p : (G ⧸ H) × {h : H // h ≠ 1}) :
    psi H p ∈ (conjUn H \ {1}) := by
  refine ⟨?_, ?_⟩
  · rw [conjUn, Set.mem_iUnion]
    refine ⟨Quotient.out p.1, ?_⟩
    rw [Work.Frobenius.mem_conj_smul_iff']
    have hh : (Quotient.out p.1)⁻¹ * psi H p * Quotient.out p.1 = ((p.2 : H) : G) := by
      simp only [psi]; group
    rw [hh]
    exact (p.2 : H).2
  · intro hc
    apply p.2.2
    refine Subtype.coe_injective ?_
    calc ((p.2 : H) : G)
        = (Quotient.out p.1)⁻¹ * psi H p * Quotient.out p.1 := by
          simp only [psi]; group
      _ = (Quotient.out p.1)⁻¹ * 1 * Quotient.out p.1 := by rw [hc]
      _ = ((1 : H) : G) := by rw [Subgroup.coe_one]; group

/-- `psi` is injective: distinct cosets give disjoint conjugates (`key`), and inside
a fixed coset `r * h * r⁻¹` determines `h`. -/
private theorem psi_injective {H : Subgroup G} (hH : IsFrobeniusComplement H) :
    Function.Injective (fun p : (G ⧸ H) × {h : H // h ≠ 1} =>
      (⟨psi H p, psi_mem p⟩ : ↥(conjUn H \ {1}))) := by
  rintro ⟨qp, hp⟩ ⟨qq, hq⟩ hpq
  have hval : psi H (qp, hp) = psi H (qq, hq) := congrArg Subtype.val hpq
  dsimp only [psi] at hval
  set r : G := Quotient.out qp with hr
  set r' : G := Quotient.out qq with hr'
  have hne : r * ((hp : H) : G) * r⁻¹ ≠ 1 := by
    intro hc
    apply hp.2
    refine Subtype.coe_injective ?_
    calc ((hp : H) : G) = r⁻¹ * (r * ((hp : H) : G) * r⁻¹) * r := by group
      _ = r⁻¹ * 1 * r := by rw [hc]
      _ = ((1 : H) : G) := by rw [Subgroup.coe_one]; group
  have hy_a : r * ((hp : H) : G) * r⁻¹ ∈ (MulAut.conj r • H : Set G) := by
    rw [Work.Frobenius.mem_conj_smul_iff']
    have hh : r⁻¹ * (r * ((hp : H) : G) * r⁻¹) * r = ((hp : H) : G) := by group
    rw [hh]
    exact (hp : H).2
  have hy_b : r * ((hp : H) : G) * r⁻¹ ∈ (MulAut.conj r' • H : Set G) := by
    rw [Work.Frobenius.mem_conj_smul_iff']
    rw [hval]
    have hh : r'⁻¹ * (r' * ((hq : H) : G) * r'⁻¹) * r' = ((hq : H) : G) := by group
    rw [hh]
    exact (hq : H).2
  have hd : r'⁻¹ * r ∈ H := key hH hy_a hy_b hne
  have hcoset : ((r : G) : G ⧸ H) = ((r' : G) : G ⧸ H) := by
    rw [QuotientGroup.eq]
    simpa using H.inv_mem hd
  have hq_eq : qp = qq := by
    calc qp = ((r : G) : G ⧸ H) := by rw [hr]; exact (Quotient.out_eq qp).symm
      _ = ((r' : G) : G ⧸ H) := hcoset
      _ = qq := by rw [hr']; exact Quotient.out_eq qq
  subst hq_eq
  refine Prod.ext rfl (Subtype.ext (Subtype.coe_injective ?_))
  calc ((hp : H) : G) = r⁻¹ * (r * ((hp : H) : G) * r⁻¹) * r := by group
    _ = r⁻¹ * (r * ((hq : H) : G) * r⁻¹) * r := by rw [hval]
    _ = ((hq : H) : G) := by group

/-- `psi` is surjective: every element of a conjugate `H^g` is of the form
`r * h * r⁻¹` for the canonical representative `r` of the coset of `g`. -/
private theorem psi_surjective {H : Subgroup G} :
    Function.Surjective (fun p : (G ⧸ H) × {h : H // h ≠ 1} =>
      (⟨psi H p, psi_mem p⟩ : ↥(conjUn H \ {1}))) := by
  rintro ⟨x, hx⟩
  obtain ⟨hxmem, hxne⟩ := hx
  rw [conjUn, Set.mem_iUnion] at hxmem
  obtain ⟨g, hg⟩ := hxmem
  have hxne' : x ≠ 1 := by simpa using hxne
  have hrg : (Quotient.out (g : G ⧸ H))⁻¹ * g ∈ H :=
    QuotientGroup.eq.mp (Quotient.out_eq (g : G ⧸ H))
  rw [Work.Frobenius.mem_conj_smul_iff'] at hg
  have hmem : (Quotient.out (g : G ⧸ H))⁻¹ * x * Quotient.out (g : G ⧸ H) ∈ H := by
    have hh : (Quotient.out (g : G ⧸ H))⁻¹ * x * Quotient.out (g : G ⧸ H)
        = ((Quotient.out (g : G ⧸ H))⁻¹ * g) * (g⁻¹ * x * g) *
            ((Quotient.out (g : G ⧸ H))⁻¹ * g)⁻¹ := by
      group
    rw [hh]
    exact H.mul_mem (H.mul_mem hrg hg) (H.inv_mem hrg)
  have hne' : (Quotient.out (g : G ⧸ H))⁻¹ * x * Quotient.out (g : G ⧸ H) ≠ 1 := by
    intro hc
    apply hxne'
    calc x = Quotient.out (g : G ⧸ H) *
          ((Quotient.out (g : G ⧸ H))⁻¹ * x * Quotient.out (g : G ⧸ H)) *
            (Quotient.out (g : G ⧸ H))⁻¹ := by
          group
      _ = Quotient.out (g : G ⧸ H) * 1 * (Quotient.out (g : G ⧸ H))⁻¹ := by rw [hc]
      _ = 1 := by group
  have hneH : (⟨(Quotient.out (g : G ⧸ H))⁻¹ * x * Quotient.out (g : G ⧸ H), hmem⟩ : H) ≠ 1 := by
    intro hc
    apply hne'
    have hh := congrArg (fun z : H => (z : G)) hc
    simpa using hh
  refine ⟨((g : G ⧸ H), ⟨⟨_, hmem⟩, hneH⟩), ?_⟩
  refine Subtype.ext ?_
  simp only [psi]
  group

/-- **The count.**  The union of the conjugates of `H`, with the identity removed,
has exactly `H.index * (Nat.card H - 1)` elements. -/
private theorem ncard_conjUn_sdiff_one [Fintype G] {H : Subgroup G}
    (hH : IsFrobeniusComplement H) :
    (conjUn H \ {1}).ncard = H.index * (Nat.card H - 1) := by
  have hbij : Function.Bijective (fun p : (G ⧸ H) × {h : H // h ≠ 1} =>
      (⟨psi H p, psi_mem p⟩ : ↥(conjUn H \ {1}))) :=
    ⟨psi_injective hH, psi_surjective⟩
  have hcard := Nat.card_eq_of_bijective _ hbij
  have hsub : Nat.card {h : H // h ≠ 1} = Nat.card H - 1 := by
    have instH : Fintype H := Fintype.ofFinite H
    have instNe : Fintype {h : H // h ≠ 1} := Fintype.ofFinite _
    have instEq : Fintype {x : H // x = 1} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := H),
      Fintype.card_subtype_compl (fun x : H => x = 1), Fintype.card_subtype_eq]
  rw [← Nat.card_coe_set_eq, ← hcard, Nat.card_prod, ← Subgroup.index_eq_card H, hsub]

/-- The Frobenius kernel is the identity together with the complement of the union
of the conjugates of `H`. -/
private lemma frobeniusKernel_eq (H : Subgroup G) :
    frobeniusKernel H = {1} ∪ (conjUn H)ᶜ := by
  ext x
  simp [frobeniusKernel, conjUn, Set.mem_sdiff]

end CardFrobeniusKernel

open CardFrobeniusKernel

/-- The Frobenius kernel of a Frobenius complement `H` has `H.index` elements. -/
theorem card_frobeniusKernel {G : Type*} [Group G] [Fintype G] {H : Subgroup G} (hH : IsFrobeniusComplement H) : Nat.card (frobeniusKernel H) = H.index := by
  have hB : (conjUn H \ {1}).ncard = H.index * (Nat.card H - 1) := ncard_conjUn_sdiff_one hH
  have h1T : (1 : G) ∈ conjUn H := by
    rw [conjUn, Set.mem_iUnion]
    exact ⟨1, by rw [Work.Frobenius.mem_conj_smul_iff']; simp⟩
  have hdisj : Disjoint ({1} : Set G) (conjUn H)ᶜ :=
    (disjoint_compl_right (a := conjUn H)).mono_left (by rintro x rfl; exact h1T)
  have hncard : (frobeniusKernel H).ncard = 1 + (Nat.card G - (conjUn H).ncard) := by
    rw [frobeniusKernel_eq, Set.ncard_union_eq hdisj, Set.ncard_singleton, Set.ncard_compl]
  have hTcard : (conjUn H).ncard = (conjUn H \ {1}).ncard + 1 :=
    (Set.ncard_sdiff_singleton_add_one h1T).symm
  have hm : 1 ≤ Nat.card H := Nat.card_pos
  have hi : 1 ≤ H.index := le_of_lt (Subgroup.one_lt_index_of_ne_top hH.ne_top)
  have hn : Nat.card G = (conjUn H \ {1}).ncard + H.index := by
    rw [← Subgroup.card_mul_index H]
    calc Nat.card H * H.index
        = ((Nat.card H - 1) + 1) * H.index := by rw [Nat.sub_add_cancel hm]
      _ = (Nat.card H - 1) * H.index + H.index := by rw [add_mul, one_mul]
      _ = H.index * (Nat.card H - 1) + H.index := by rw [mul_comm]
      _ = (conjUn H \ {1}).ncard + H.index := by rw [← hB]
  have hA : (conjUn H \ {1}).ncard + H.index - (conjUn H \ {1}).ncard = H.index := by
    rw [Nat.add_comm (conjUn H \ {1}).ncard H.index, Nat.add_sub_cancel]
  rw [Nat.card_coe_set_eq]
  calc (frobeniusKernel H).ncard
      = 1 + (Nat.card G - (conjUn H).ncard) := hncard
    _ = 1 + (Nat.card G - ((conjUn H \ {1}).ncard + 1)) := by rw [hTcard]
    _ = 1 + (Nat.card G - (conjUn H \ {1}).ncard - 1) := by rw [← Nat.sub_sub]
    _ = 1 + ((conjUn H \ {1}).ncard + H.index - (conjUn H \ {1}).ncard - 1) := by rw [hn]
    _ = 1 + (H.index - 1) := by rw [hA]
    _ = H.index := by omega

end

end Work.Frobenius.Basic
