import Mathlib
import Submission.Work.PGroup.CommClosure
import Submission.Work.PGroup.card_sup_mul_card_inf
import Submission.Work.PGroup.centralizer_inf_eq_of_maxAbelianOrder_comm

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Thompson's product lemma for a maximal abelian subgroup

Let `P` be a finite subgroup of a group `G`, let `A ≤ P` be abelian with
`Nat.card A = maxAbelianOrder P` (i.e. `A` has maximal order among the abelian subgroups of `P`),
let `x ∈ G` and put `M = [x, A] = `commClosure x A``.  Assume `M ≤ P` and that `M` is abelian.
Then

`M ⊔ (A ⊓ C_G(M))`  is abelian of order `maxAbelianOrder P`.

This is Thompson's product lemma (`Thompson's lemma on product with centralizer of commutator
with abelian subgroup of maximum order`, Gorenstein, *Finite Groups*, Theorem 2.4), the counting
core of Thompson's replacement theorem (`Work.PGroup.thompson_replacement`).

The proof is the classical one: write `C = C_A(M)`; then `MC` is abelian (so `|MC| ≤ |A|` by
maximality), and the map `a ↦ ⁅x, a⁆` from `A` to `M` induces an injective map
`A/C ↪ M/(M ⊓ A)`, giving `|A| ≤ |MC|`.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open scoped Classical Pointwise commutatorElement
open Subgroup

noncomputable section

namespace Work.PGroup

variable {G : Type*} [Group G]

/-- `a ⁅x,c⁆ a⁻¹ = ⁅x,c⁆ ⁅⁅x,a⁆⁻¹, c⁆` when `a` commutes with `c` and `⁅x,a⁆` commutes with
`⁅x,c⁆`.  (Consequence of the Hall–Witt-type identity `[[x,a],c] = [[x,c],a]`.) -/
private theorem conj_commutatorElement_eq_mul_gen (x a c : G) (hac : Commute a c)
    (hx : Commute ⁅x,a⁆ ⁅x,c⁆) :
    a * ⁅x,c⁆ * a⁻¹ = ⁅x,c⁆ * ⁅⁅x,a⁆⁻¹, c⁆ := by
  have hac' : a * c * a⁻¹ = c := by rw [hac.eq]; group
  have h1 : a * ⁅x,c⁆ * a⁻¹ = ⁅a * x * a⁻¹, c⁆ := by
    rw [conjugate_commutatorElement, hac']
  have h2 : a * x * a⁻¹ = ⁅a,x⁆ * x := by
    rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul]
  rw [h1, h2, commutatorElement_mul_left_eq_conj_mul]
  have hcomm : Commute ⁅a,x⁆ ⁅x,c⁆ := by
    have hax : ⁅a,x⁆ = ⁅x,a⁆⁻¹ := by rw [commutatorElement_inv]
    rw [hax]; exact hx.inv_left
  rw [hcomm.eq, mul_inv_cancel_right, commutatorElement_inv]

/-- `⁅x, u⁻¹ * v⁆ = u⁻¹ * (⁅x,u⁆⁻¹ * ⁅x,v⁆) * u`. -/
private theorem commutatorElement_inv_mul (x u v : G) :
    ⁅x, u⁻¹ * v⁆ = u⁻¹ * (⁅x,u⁆⁻¹ * ⁅x,v⁆) * u := by
  rw [commutatorElement_def]; group

/-- If `⁅x,u⁆⁻¹ * ⁅x,v⁆` centralizes `A` and `u ∈ A`, then so does `⁅x, u⁻¹ * v⁆`. -/
private theorem commutator_inv_mul_mem_centralizer {A : Subgroup G} {x u v : G}
    (hu : u ∈ A)
    (hz : ⁅x,u⁆⁻¹ * ⁅x,v⁆ ∈ Subgroup.centralizer (A : Set G)) :
    ⁅x, u⁻¹ * v⁆ ∈ Subgroup.centralizer (A : Set G) := by
  rw [commutatorElement_inv_mul]
  have h : (⁅x,u⁆⁻¹ * ⁅x,v⁆) * u = u * (⁅x,u⁆⁻¹ * ⁅x,v⁆) :=
    (Subgroup.mem_centralizer_iff.mp hz u hu).symm
  have heq : u⁻¹ * (⁅x,u⁆⁻¹ * ⁅x,v⁆) * u = ⁅x,u⁆⁻¹ * ⁅x,v⁆ := by
    calc u⁻¹ * (⁅x,u⁆⁻¹ * ⁅x,v⁆) * u
        = u⁻¹ * ((⁅x,u⁆⁻¹ * ⁅x,v⁆) * u) := by group
      _ = u⁻¹ * (u * (⁅x,u⁆⁻¹ * ⁅x,v⁆)) := by rw [h]
      _ = ⁅x,u⁆⁻¹ * ⁅x,v⁆ := by group
  rw [heq]
  exact hz

/-- If `⁅x,a⁆` centralizes `A` and `a ∈ A`, then `a` centralizes `M = [x,A]`. -/
private theorem mem_centralizer_commClosure_of_commutator_mem {A : Subgroup G} {x a : G}
    (hAcomm : ∀ p ∈ A, ∀ q ∈ A, p * q = q * p)
    (hMcomm : ∀ p ∈ commClosure x A, ∀ q ∈ commClosure x A, p * q = q * p)
    (ha : a ∈ A)
    (hxaA : ⁅x, a⁆ ∈ Subgroup.centralizer (A : Set G)) :
    a ∈ Subgroup.centralizer (commClosure x A : Set G) := by
  have key : ∀ b ∈ A, Commute a ⁅x,b⁆ := by
    intro b hb
    have hyb : ⁅x,b⁆ ∈ commClosure x A := mem_commClosure hb
    have hcomm1 : Commute a b := (commute_iff_eq a b).mpr (hAcomm a ha b hb)
    have hcomm2 : Commute ⁅x,a⁆ ⁅x,b⁆ :=
      (commute_iff_eq _ _).mpr (hMcomm _ (mem_commClosure ha) _ hyb)
    have hkey := conj_commutatorElement_eq_mul_gen x a b hcomm1 hcomm2
    have h1 : b * ⁅x,a⁆ = ⁅x,a⁆ * b := Subgroup.mem_centralizer_iff.mp hxaA b hb
    have hz1 : ⁅⁅x,a⁆⁻¹, b⁆ = 1 := by
      have hc : Commute b ⁅x,a⁆ := (commute_iff_eq b ⁅x,a⁆).mpr h1
      have : ⁅b, ⁅x,a⁆⁻¹⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr hc.inv_right
      rw [← commutatorElement_inv, this, inv_one]
    rw [hz1, mul_one] at hkey
    rw [commute_iff_eq]
    conv_rhs => rw [← hkey]
    group
  have hsub : commClosure x A ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [commClosure, Subgroup.closure_le]
    rintro y ⟨b, hb, rfl⟩
    change ⁅x, b⁆ ∈ Subgroup.centralizer ({a} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (key b hb).eq
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact (Subgroup.mem_centralizer_iff.mp (hsub hh) a (Set.mem_singleton a)).symm

/-- If `c ∈ C_A(M)` with `M = [x,A]` and `c ∈ A`, then `⁅x,c⁆` centralizes `A`. -/
private theorem commutator_mem_centralizer_of_mem_centralizer_commClosure {A : Subgroup G} {x c : G}
    (hAcomm : ∀ p ∈ A, ∀ q ∈ A, p * q = q * p)
    (hMcomm : ∀ p ∈ commClosure x A, ∀ q ∈ commClosure x A, p * q = q * p)
    (hcA : c ∈ A)
    (hcM : c ∈ Subgroup.centralizer (commClosure x A : Set G)) :
    ⁅x, c⁆ ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hcd : Commute d c := (commute_iff_eq d c).mpr (hAcomm d hd c hcA)
  have hxcM : ⁅x,c⁆ ∈ commClosure x A := mem_commClosure hcA
  have hxdM : ⁅x,d⁆ ∈ commClosure x A := mem_commClosure hd
  have hxd2 : Commute ⁅x,d⁆ ⁅x,c⁆ := (commute_iff_eq _ _).mpr (hMcomm _ hxdM _ hxcM)
  have hkey := conj_commutatorElement_eq_mul_gen x d c hcd hxd2
  have hz : ⁅⁅x,d⁆⁻¹, c⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp hcM _ (inv_mem hxdM)
  rw [hz, mul_one] at hkey
  conv_rhs => rw [← hkey]
  group

/-- **Thompson's product lemma.**  For `A` an abelian subgroup of `P` of maximal order and
`M = [x,A] ≤ P` abelian, the subgroup `M ⊔ (A ⊓ C_G(M))` is abelian of order `maxAbelianOrder P`.
-/
theorem thompson_product_centralizer {G : Type*} [Group G] {P A : Subgroup G} [Finite P] {x : G}
    (hA : A ≤ P) (hAab : IsMulCommutative A)
    (hAmax : Nat.card A = Work.PGroup.maxAbelianOrder P)
    (hMle : Work.PGroup.commClosure x A ≤ P)
    (hMab : IsMulCommutative (Work.PGroup.commClosure x A)) :
    IsMulCommutative ↥(Work.PGroup.commClosure x A ⊔
        (A ⊓ Subgroup.centralizer (Work.PGroup.commClosure x A : Set G))) ∧
      Nat.card ↥(Work.PGroup.commClosure x A ⊔
        (A ⊓ Subgroup.centralizer (Work.PGroup.commClosure x A : Set G))) =
        Work.PGroup.maxAbelianOrder P := by
  let M : Subgroup G := Work.PGroup.commClosure x A
  let C : Subgroup G := A ⊓ Subgroup.centralizer (M : Set G)
  have hMP : M ≤ P := hMle
  have hCA : C ≤ A := inf_le_left
  have hMcomm : ∀ p ∈ M, ∀ q ∈ M, p * q = q * p :=
    fun p hp q hq => congrArg Subtype.val (isMulCommutative_iff.mp hMab ⟨p,hp⟩ ⟨q,hq⟩)
  have hAcomm : ∀ p ∈ A, ∀ q ∈ A, p * q = q * p :=
    fun p hp q hq => congrArg Subtype.val (isMulCommutative_iff.mp hAab ⟨p,hp⟩ ⟨q,hq⟩)
  have hMC : ∀ m ∈ M, ∀ c ∈ C, m * c = c * m :=
    fun m hm c hc => Subgroup.mem_centralizer_iff.mp hc.2 m hm
  -- finiteness instances
  haveI hFinM : Finite ↥M :=
    Finite.of_injective (Subgroup.inclusion hMP) (Subgroup.inclusion_injective hMP)
  haveI hFinC : Finite ↥C :=
    Finite.of_injective (Subgroup.inclusion (le_trans hCA hA))
      (Subgroup.inclusion_injective (le_trans hCA hA))
  haveI hFinA : Finite ↥A :=
    Finite.of_injective (Subgroup.inclusion hA) (Subgroup.inclusion_injective hA)
  -- `M ⊔ C` is abelian
  have hab : IsMulCommutative ↥(M ⊔ C) := by
    rw [Subgroup.sup_eq_closure]
    apply Subgroup.isMulCommutative_closure
    intro p hp q hq _
    rw [Set.mem_union] at hp hq
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact (commute_iff_eq p q).mpr (hMcomm p hp q hq)
    · exact (commute_iff_eq p q).mpr (hMC p hp q hq)
    · exact (commute_iff_eq p q).mpr (hMC q hq p hp).symm
    · exact (commute_iff_eq p q).mpr (hAcomm p hp.1 q hq.1)
  have hsupP : M ⊔ C ≤ P := sup_le hMP (le_trans hCA hA)
  -- self-centralizing
  have hsc : P ⊓ Subgroup.centralizer (A : Set G) = A :=
    centralizer_inf_eq_of_maxAbelianOrder_comm hA hAab hAmax
  have hAcentA : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hAab
  let D : Subgroup G := M ⊓ A
  have hDM : D ≤ M := inf_le_left
  have hDA : D ≤ A := inf_le_right
  have hD_cent : M ⊓ Subgroup.centralizer (A : Set G) = D := by
    refine le_antisymm ?_ ?_
    · exact le_inf inf_le_left (le_trans (inf_le_inf_right _ hMP) (le_of_eq hsc))
    · exact le_inf inf_le_left (le_trans inf_le_right hAcentA)
  have hDC : M ⊓ C = D := by
    refine le_antisymm ?_ ?_
    · exact le_inf inf_le_left (le_trans inf_le_right (inf_le_left : C ≤ A))
    · refine le_inf inf_le_left (le_inf inf_le_right ?_)
      intro z hz
      exact Subgroup.mem_centralizer_iff.mpr (fun m hm => hMcomm m hm z hz.1)
  haveI hFinD : Finite ↥D :=
    Finite.of_injective (Subgroup.inclusion hDM) (Subgroup.inclusion_injective hDM)
  -- cardinal bound from maximality
  have hcard_le : Nat.card ↥(M ⊔ C) ≤ Work.PGroup.maxAbelianOrder P :=
    le_maxAbelianOrder P (M ⊔ C) hsupP hab
  -- the injection `A/C → M/D`
  let g : ↥A → ↥M := fun a => ⟨⁅x, (a : G)⁆, mem_commClosure a.2⟩
  have hwd : ∀ p q : ↥A, QuotientGroup.leftRel (C.subgroupOf A) p q →
      QuotientGroup.leftRel (D.subgroupOf M) (g p) (g q) := by
    intro p q hpq
    rw [QuotientGroup.leftRel_apply] at hpq ⊢
    have hc0C : (p : G)⁻¹ * (q : G) ∈ C := by
      have := Subgroup.mem_subgroupOf.mp hpq
      simpa using this
    set c₀ : G := (p : G)⁻¹ * (q : G) with hc₀
    have hc0A : c₀ ∈ A := hCA hc0C
    have hxc0M : ⁅x, c₀⁆ ∈ M := mem_commClosure hc0A
    have hxc0cent : ⁅x, c₀⁆ ∈ Subgroup.centralizer (A : Set G) :=
      commutator_mem_centralizer_of_mem_centralizer_commClosure hAcomm hMcomm hc0A hc0C.2
    have hxc0D : ⁅x, c₀⁆ ∈ D := hD_cent ▸ ⟨hxc0M, hxc0cent⟩
    have hval : ⁅x, (p:G)⁆⁻¹ * ⁅x, (q:G)⁆ = ⁅x, c₀⁆ := by
      have hq : (q : G) = (p : G) * c₀ := by
        show (q : G) = (p : G) * ((p : G)⁻¹ * (q : G)); group
      rw [hq, commutatorElement_mul_right_eq_mul_conj]
      have hpz : (p : G) * ⁅x, c₀⁆ = ⁅x, c₀⁆ * (p : G) :=
        Subgroup.mem_centralizer_iff.mp hxc0cent (p : G) p.2
      calc ⁅x, (p:G)⁆⁻¹ * (⁅x, (p:G)⁆ * (p:G) * ⁅x, c₀⁆ * (p:G)⁻¹)
          = (p:G) * ⁅x, c₀⁆ * (p:G)⁻¹ := by group
        _ = ⁅x, c₀⁆ := by rw [hpz]; group
    rw [Subgroup.mem_subgroupOf]
    show (⁅x, (p:G)⁆)⁻¹ * ⁅x, (q:G)⁆ ∈ D
    rw [hval]
    exact hxc0D
  have hinj : Function.Injective (Quotient.map' g hwd) := by
    intro a b hab
    induction a using Quotient.ind with
    | _ p =>
    induction b using Quotient.ind with
    | _ q =>
    rw [Quotient.map'_mk'', Quotient.map'_mk''] at hab
    have hmem : (g p)⁻¹ * (g q) ∈ D.subgroupOf M := QuotientGroup.eq.mp hab
    have hzcent : ⁅x, (p:G)⁆⁻¹ * ⁅x, (q:G)⁆ ∈ Subgroup.centralizer (A : Set G) := by
      have hmemD : (↑((g p)⁻¹ * (g q)) : G) ∈ D := Subgroup.mem_subgroupOf.mp hmem
      have := hAcentA hmemD.2
      simpa only [Subgroup.coe_inv, Subgroup.coe_mul, Subtype.coe_mk] using this
    set c₀ : G := (p : G)⁻¹ * (q : G) with hc₀
    have hc0A : c₀ ∈ A := mul_mem (inv_mem p.2) q.2
    have hstep5 : ⁅x, c₀⁆ ∈ Subgroup.centralizer (A : Set G) :=
      commutator_inv_mul_mem_centralizer (A := A) p.2 hzcent
    have hstep6 : c₀ ∈ Subgroup.centralizer (commClosure x A : Set G) :=
      mem_centralizer_commClosure_of_commutator_mem hAcomm hMcomm hc0A hstep5
    have hc0C : c₀ ∈ C := ⟨hc0A, hstep6⟩
    rw [QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    show (p:G)⁻¹ * (q:G) ∈ C
    exact hc0C
  -- cardinal inequality `|A/C| ≤ |M/D|`
  haveI : Finite (M ⧸ (D.subgroupOf M)) := inferInstance
  have hcard_qle : Nat.card (A ⧸ (C.subgroupOf A)) ≤ Nat.card (M ⧸ (D.subgroupOf M)) :=
    Nat.card_le_card_of_injective _ hinj
  -- split cardinals
  have hA_split : Nat.card ↥A = Nat.card (A ⧸ (C.subgroupOf A)) * Nat.card ↥C := by
    rw [← Subgroup.index_mul_card (C.subgroupOf A),
        ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCA).toEquiv]
    rfl
  have hM_split : Nat.card ↥M = Nat.card (M ⧸ (D.subgroupOf M)) * Nat.card ↥D := by
    rw [← Subgroup.index_mul_card (D.subgroupOf M),
        ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv]
    rfl
  have hprod : Nat.card ↥(M ⊔ C) * Nat.card ↥D = Nat.card ↥M * Nat.card ↥C := by
    rw [← hDC]
    exact card_sup_mul_card_inf M C hMC
  have hDpos : 0 < Nat.card ↥D := Nat.card_pos
  have hcard_ge : Nat.card ↥A ≤ Nat.card ↥(M ⊔ C) := by
    have key : Nat.card ↥A * Nat.card ↥D ≤ Nat.card ↥(M ⊔ C) * Nat.card ↥D := by
      rw [hA_split, hprod, hM_split]
      have := Nat.mul_le_mul_right (Nat.card ↥C * Nat.card ↥D) hcard_qle
      simpa only [mul_assoc, mul_comm, mul_left_comm] using this
    exact Nat.le_of_mul_le_mul_right key hDpos
  have hcard_eq : Nat.card ↥(M ⊔ C) = Work.PGroup.maxAbelianOrder P :=
    le_antisymm hcard_le (by rw [← hAmax]; exact hcard_ge)
  exact ⟨hab, hcard_eq⟩

end Work.PGroup
