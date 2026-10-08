/-
# Appendix I (1)(b) of Peterfalvi I, at `d = 2`: surjectivity of `V × K → X`

Peterfalvi, *Le théorème de Bender–Suzuki I*, Appendix I (1)(b) (p. 200).  With `M` a finite
group, `t ∈ M` of order `d`, `X` a `d'`-subgroup of `M` normalised by `t`:

> Suppose `d = 2`. Then `K = {x ∈ X | x^t = x⁻¹}` (`= J(X,t)`), and the map `(x,y) ↦ xy` is a
> bijection of `V × K` onto `X`.

This file proves the surjectivity half, in the transcription used by `Work.NormalComplement.Defs`:
`Kset X t = invertedBy X t = {x ∈ X | t x t⁻¹ = x⁻¹}` and `V = X ⊓ C_G(t)`.  The proof follows
Peterfalvi's counting argument:

* `|Kapp t X| = |X : V|` (`Kapp_ncard_eq_index`), where `Kapp t X = {t⁻¹x⁻¹tx | x ∈ X}` is the
  commutator set: its elements are in bijection with the `X`-conjugates of `t` (orbit–stabiliser),
* `Kapp t X ⊆ Kset X t` for `orderOf t = 2` (`Kapp_subset_Kset`); hence `|Kset X t| ≥ |X : V|`,
* the multiplication map `V × Kset → X` is injective (`mul_centralizer_Kset_injective`), using
  that `X` has odd order so that squaring is injective on it,

so the map has domain and codomain of the same cardinality and is surjective.
-/
import Mathlib
import Submission.Work.NormalComplement.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

open Classical

-- `letI` is genuinely needed below (a `MulAction` instance), so silence the style linter.
set_option linter.style.haveILetI false

/-- **(Peterfalvi I, Appendix I (1)(a), in the form `u ↦ t⁻¹u`.)**  The commutator set
`Kapp t X = {t⁻¹x⁻¹tx | x ∈ X}` has as many elements as the index of `V = X ⊓ C_G(t)` in `X`,
equivalently as the number of conjugates of `t` under `X`.

The orbit–stabiliser theorem, applied to the action of `X` on `G` by conjugation, gives that the
number of conjugates of `t` is `|X : V|`; the map `u ↦ t⁻¹u` is a bijection from that orbit onto
`Kapp t X`. -/
lemma Kapp_ncard_eq_index {G : Type*} [Group G] [Finite G] (t : G) (X : Subgroup G) :
    (Kapp t X).ncard = ((X ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf X).index := by
  letI : MulAction ↥X G := MulAction.compHom G (MulAut.conj.comp X.subtype)
  have hsmul : ∀ (x : ↥X), x • t = (x : G) * t * (x : G)⁻¹ := by
    intro x
    rw [show x • t = (MulAut.conj (x : G)) • t from rfl, MulAut.smul_def, MulAut.conj_apply]
  have hstab :
      MulAction.stabilizer ↥X t = (X ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf X := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro (h : x • t = t)
      rw [hsmul x] at h
      exact ⟨x.2, (mul_inv_eq_iff_eq_mul.mp h)⟩
    · rintro ⟨-, hx⟩
      rw [hsmul x]
      exact mul_inv_eq_iff_eq_mul.mpr hx
  rw [← hstab, MulAction.index_stabilizer]
  symm
  refine Set.ncard_congr (fun u _ => t⁻¹ * u) ?_ ?_ ?_
  · intro u hu
    rw [MulAction.mem_orbit_iff] at hu
    obtain ⟨y, rfl⟩ := hu
    refine ⟨(y : G)⁻¹, X.inv_mem y.2, ?_⟩
    rw [hsmul y]
    group
  · intro u v _ _ huv
    exact mul_left_cancel huv
  · intro k hk
    rw [Kapp, Set.mem_ofPred_eq] at hk
    obtain ⟨w, hw, rfl⟩ := hk
    refine ⟨w⁻¹ * t * w, ?_, ?_⟩
    · rw [MulAction.mem_orbit_iff]
      exact ⟨⟨w⁻¹, X.inv_mem hw⟩, by rw [hsmul]; simp⟩
    · group

/-- **(Peterfalvi I, Appendix I (1)(b), first half.)**  When `orderOf t = 2`, every commutator
`t⁻¹x⁻¹tx = [t,x]` lies in `Kset X t = J(X,t)`, i.e. belongs to `X` and is inverted by `t`. -/
lemma Kapp_subset_Kset {G : Type*} [Group G] {t : G} (ht : orderOf t = 2) {X : Subgroup G}
    (htX : NormalizedBy t X) : Kapp t X ⊆ Kset X t := by
  rintro z ⟨x, hx, rfl⟩
  have h2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht, pow_two] at this
    exact this
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h2
  refine ⟨?_, ?_⟩
  · rw [htinv]
    have h1 : t * x⁻¹ * t ∈ X := by
      have := htX x⁻¹ (X.inv_mem hx)
      rwa [htinv] at this
    exact X.mul_mem h1 hx
  · have hR : (t * x⁻¹ * t * x)⁻¹ = x⁻¹ * t * x * t := by
      rw [show (t * x⁻¹ * t * x)⁻¹ = x⁻¹ * t⁻¹ * x * t⁻¹ from by group, htinv]
    rw [htinv, hR]
    rw [show t * (t * x⁻¹ * t * x) * t = (t * t) * (x⁻¹ * t * x) * t from by group,
      h2, one_mul]

/-- **(Peterfalvi I, Appendix I (1)(b), injectivity of `(x,y) ↦ xy`.)**  If `X` has odd order,
`t` is any element and `c₁, c₂ ∈ X ∩ C_G(t)`, `k₁, k₂ ∈ J(X,t) = Kset X t` with `c₁k₁ = c₂k₂`,
then `c₁ = c₂` and `k₁ = k₂`.

This is Peterfalvi's argument: writing `u = c₂⁻¹c₁ = k₂k₁⁻¹`, the element `u` both is fixed by
conjugation by `t` (it lies in `C_G(t)`) and is inverted by it (it is `k₂k₁⁻¹` with `k₁,k₂`
inverted), so `k₂⁻¹k₁ = k₂k₁⁻¹`, whence `k₁² = k₂²`, and squaring is injective on the odd-order
group `X`. -/
lemma mul_centralizer_Kset_injective {G : Type*} [Group G] [Finite G] {t : G}
    {X : Subgroup G} (hodd : Odd (Nat.card X)) :
    ∀ (c₁ : G), c₁ ∈ X ⊓ Subgroup.centralizer ({t} : Set G) → ∀ k₁ ∈ Kset X t,
    ∀ (c₂ : G), c₂ ∈ X ⊓ Subgroup.centralizer ({t} : Set G) → ∀ k₂ ∈ Kset X t,
    c₁ * k₁ = c₂ * k₂ → c₁ = c₂ ∧ k₁ = k₂ := by
  intro c₁ hc₁ k₁ hk₁ c₂ hc₂ k₂ hk₂ heq
  have hc₁C : c₁ ∈ Subgroup.centralizer ({t} : Set G) := hc₁.2
  have hc₂C : c₂ ∈ Subgroup.centralizer ({t} : Set G) := hc₂.2
  have hk₁inv : t * k₁ * t⁻¹ = k₁⁻¹ := hk₁.2
  have hk₂inv : t * k₂ * t⁻¹ = k₂⁻¹ := hk₂.2
  -- `c₂⁻¹ * c₁ = k₂ * k₁⁻¹`
  have h1 : c₂⁻¹ * c₁ = k₂ * k₁⁻¹ := by
    have h : c₂⁻¹ * c₁ * k₁ = k₂ := by
      calc c₂⁻¹ * c₁ * k₁ = c₂⁻¹ * (c₁ * k₁) := by group
        _ = c₂⁻¹ * (c₂ * k₂) := by rw [heq]
        _ = k₂ := by group
    calc c₂⁻¹ * c₁ = (c₂⁻¹ * c₁ * k₁) * k₁⁻¹ := by group
      _ = k₂ * k₁⁻¹ := by rw [h]
  -- `c₂⁻¹ * c₁` is centralised by `t`
  have hc₂C' : c₂⁻¹ ∈ Subgroup.centralizer ({t} : Set G) :=
    (Subgroup.centralizer ({t} : Set G)).inv_mem hc₂C
  have huC : c₂⁻¹ * c₁ ∈ Subgroup.centralizer ({t} : Set G) :=
    (Subgroup.centralizer ({t} : Set G)).mul_mem hc₂C' hc₁C
  have huconj : t * (c₂⁻¹ * c₁) * t⁻¹ = c₂⁻¹ * c₁ := by
    have hut : (c₂⁻¹ * c₁) * t = t * (c₂⁻¹ * c₁) :=
      Subgroup.mem_centralizer_singleton_iff.mp huC
    rw [← hut]; group
  -- while conjugation by `t` inverts `k₂ * k₁⁻¹`
  have h3 : t * (k₂ * k₁⁻¹) * t⁻¹ = k₂⁻¹ * k₁ := by
    have hk₁' : t * k₁⁻¹ * t⁻¹ = k₁ := by
      rw [show t * k₁⁻¹ * t⁻¹ = (t * k₁ * t⁻¹)⁻¹ by group, hk₁inv, inv_inv]
    calc t * (k₂ * k₁⁻¹) * t⁻¹ = (t * k₂ * t⁻¹) * (t * k₁⁻¹ * t⁻¹) := by group
      _ = k₂⁻¹ * k₁ := by rw [hk₂inv, hk₁']
  have h4 : k₂⁻¹ * k₁ = k₂ * k₁⁻¹ := by rw [← h3, ← h1, huconj]
  -- hence `k₁² = k₂²`
  have hsq : k₁ * k₁ = k₂ * k₂ := by
    have key : k₂ * (k₂⁻¹ * k₁) * k₁ = k₂ * (k₂ * k₁⁻¹) * k₁ :=
      congrArg (fun w => k₂ * w * k₁) h4
    rw [show k₂ * (k₂⁻¹ * k₁) * k₁ = k₁ * k₁ by group,
        show k₂ * (k₂ * k₁⁻¹) * k₁ = k₂ * k₂ by group] at key
    exact key
  have hcop : (Nat.card ↥X).Coprime 2 := Nat.coprime_two_right.mpr hodd
  have hsub : (⟨k₁, hk₁.1⟩ : ↥X) ^ 2 = ⟨k₂, hk₂.1⟩ ^ 2 := by
    refine Subtype.ext ?_
    simpa [pow_two] using hsq
  have hkk : k₁ = k₂ := by
    have hh := (Nat.Coprime.pow_left_bijective (G := ↥X) (n := 2) hcop).1 hsub
    have := congrArg Subtype.val hh
    simpa using this
  refine ⟨?_, hkk⟩
  have hceq : c₂⁻¹ * c₁ = 1 := by rw [h1, hkk, mul_inv_cancel]
  calc c₁ = c₂ * (c₂⁻¹ * c₁) := by group
    _ = c₂ * 1 := by rw [hceq]
    _ = c₂ := mul_one c₂

/-- **Peterfalvi I, Appendix I (1)(b) (`d = 2`): the map `V × J(X,t) → X`, `(c,k) ↦ ck`, is
surjective.**  Equivalently, every `z ∈ X` factors as `z = c k` with `c ∈ X ∩ C_G(t)` and
`k ∈ Kset X t = J(X,t)`.

`V × Kset` and `X` have the same cardinality: `V × Kset` has size
`|X : V| · |V| = |X|` because `Kapp t X ⊆ Kset X t` and `|Kapp t X| = |X : V|`, and the
multiplication map is injective; an injective map between finite sets of equal cardinality is
surjective. -/
theorem appI_phi_surjective {G : Type*} [Group G] [Finite G] {t : G} (ht : orderOf t = 2)
    {X : Subgroup G} (htX : Work.NormalComplement.NormalizedBy t X) (hodd : Odd (Nat.card X)) :
    ∀ z ∈ X, ∃ c : G, c ∈ Subgroup.centralizer ({t} : Set G) ∧ c ∈ X ∧
      ∃ k : G, k ∈ Work.NormalComplement.Kset X t ∧ c * k = z := by
  let C : Subgroup G := X ⊓ Subgroup.centralizer ({t} : Set G)
  let f : ↥C × ↥(Kset X t) → ↥X :=
    fun p => ⟨(p.1 : G) * (p.2 : G), X.mul_mem p.1.2.1 p.2.2.1⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨⟨c₁, hc₁⟩, ⟨k₁, hk₁⟩⟩ ⟨⟨c₂, hc₂⟩, ⟨k₂, hk₂⟩⟩ heq
    have hval : c₁ * k₁ = c₂ * k₂ := congrArg Subtype.val heq
    obtain ⟨hce, hke⟩ :=
      mul_centralizer_Kset_injective hodd c₁ hc₁ k₁ hk₁ c₂ hc₂ k₂ hk₂ hval
    exact Prod.ext (Subtype.ext hce) (Subtype.ext hke)
  have hcard_ub : Nat.card ↥X ≤ Nat.card (↥C × ↥(Kset X t)) := by
    have hCn : Nat.card ↥(C.subgroupOf X) = Nat.card ↥C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ≤ X)).toEquiv
    have hKapp : (Kapp t X).ncard = (C.subgroupOf X).index := Kapp_ncard_eq_index t X
    have hKle : (Kapp t X).ncard ≤ (Kset X t).ncard :=
      Set.ncard_le_ncard (Kapp_subset_Kset ht htX)
    calc Nat.card ↥X
        = Nat.card ↥(C.subgroupOf X) * (C.subgroupOf X).index :=
            (Subgroup.card_mul_index (C.subgroupOf X)).symm
      _ = Nat.card ↥C * (C.subgroupOf X).index := by rw [hCn]
      _ = Nat.card ↥C * (Kapp t X).ncard := by rw [hKapp]
      _ ≤ Nat.card ↥C * (Kset X t).ncard := Nat.mul_le_mul_left _ hKle
      _ = Nat.card ↥C * Nat.card ↥(Kset X t) := by rw [Nat.card_coe_set_eq]
      _ = Nat.card (↥C × ↥(Kset X t)) := (Nat.card_prod _ _).symm
  have hcard : Nat.card (↥C × ↥(Kset X t)) = Nat.card ↥X :=
    le_antisymm (Nat.card_le_card_of_injective f hf_inj) hcard_ub
  have hran : Set.range f = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    rw [Set.ncard_univ, Set.ncard_range_of_injective hf_inj, hcard]
  have hsurj : Function.Surjective f := fun y =>
    Set.mem_range.mp (by rw [hran]; exact Set.mem_univ y)
  intro z hz
  obtain ⟨p, hp⟩ := hsurj ⟨z, hz⟩
  exact ⟨(p.1 : G), p.1.2.2, p.1.2.1, (p.2 : G), p.2.2, congrArg Subtype.val hp⟩

end Work.NormalComplement
