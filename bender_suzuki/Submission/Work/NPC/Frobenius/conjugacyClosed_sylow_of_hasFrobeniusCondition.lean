/-
Area A9 of the Feit--Thompson drive: Frobenius' hypothesis implies that a Sylow `p`-subgroup is
*conjugacy closed*.

Main proof idea (Burnside's fusion lemma, in the form of Alperin's "conjugation family"
argument for the family of extremal subgroups):

* Call `A ≤ P` **extremal** if `N_P(A)` is a Sylow `p`-subgroup of `N_G(A)`.
* If `A` is extremal and `N_G(A)/C_G(A)` is a `p`-group (which is what Frobenius' hypothesis
  gives for non-trivial `p`-subgroups), then every element of `N_G(A)` is of the form `s * c`
  with `s ∈ N_P(A) ≤ P` and `c ∈ C_G(A)`; consequently such an element acts on `A` exactly as
  an element of `P` does.
* Every subgroup of `P` has a `G`-conjugate that is extremal (`exists_extremal_conj`), and the
  induction of `conjBy_of_le_sylow` on the index `[P : A]` shows that for every `A ≤ P` and
  every `g` with `A^g ≤ P` there is `r ∈ P` acting on `A` exactly as `g` does.

The final statement is the case `A = ⟨x⟩`.
-/
import Mathlib
import Submission.Work.NPC.Defs
import Submission.Work.NPC.Frobenius.exists_le_of_relIndex_coprime
import Submission.Work.NPC.Frobenius.exists_conj_le_of_relIndex_coprime
import Submission.Work.NPC.Frobenius.lt_normalizer_of_lt_of_isPGroup
import Submission.Work.NPC.Frobenius.relIndex_lt_of_lt_of_le
import Submission.Work.NPC.Frobenius.relIndex_eq_of_card_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.NPC.Frobenius

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-! ### Elementary lemmas on conjugation of subgroups -/

lemma conj_toMonoidHom_apply (g a : G) :
    (MulEquiv.toMonoidHom (MulAut.conj g)) a = g * a * g⁻¹ := by
  show (MulAut.conj g) a = g * a * g⁻¹
  rw [MulAut.conj_apply]

lemma map_conj_eq_smul (S : Subgroup G) (x : G) :
    S.map (MulAut.conj x).toMonoidHom = MulAut.conj x • S := by
  rw [Subgroup.pointwise_smul_def]; rfl

/-- Conjugating twice is conjugating by the product. -/
lemma map_conj_mul (A : Subgroup G) (a b : G) :
    (A.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom
      = A.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp only [MonoidHom.comp_apply]
  rw [conj_toMonoidHom_apply, conj_toMonoidHom_apply, conj_toMonoidHom_apply]
  group

lemma map_conj_inv_comp (g : G) :
    (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
  ext z
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
  rw [conj_toMonoidHom_apply, conj_toMonoidHom_apply]
  group

/-- An element of the normalizer fixes the subgroup. -/
lemma conj_one_toMonoidHom : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
  ext z; simp [MulAut.conj_apply]

lemma map_conj_eq_self_of_mem_normalizer {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    A.map (MulAut.conj g).toMonoidHom = A := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    intro a ha
    exact (Subgroup.mem_normalizer_iff.mp hg a).mp ha
  · rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]

/-- If conjugation by `g` fixes a subgroup then `g` lies in its normalizer. -/
lemma mem_normalizer_of_map_conj_eq_self {A : Subgroup G} {g : G}
    (h : A.map (MulAut.conj g).toMonoidHom = A) : g ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have : g * a * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    rwa [h] at this
  · intro ha
    have h' : A.map (MulAut.conj g⁻¹).toMonoidHom = A := by
      conv_lhs => rw [← h]
      rw [map_conj_mul, inv_mul_cancel, conj_one_toMonoidHom, Subgroup.map_id]
    have hmem : g⁻¹ * (g * a * g⁻¹) * g ∈ A.map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨g * a * g⁻¹, ha, by rw [conj_toMonoidHom_apply]; group⟩
    rw [h'] at hmem
    convert hmem using 1
    group

/-! ### The key index computation -/

/-- **Key lemma.**  If `S, C ≤ H`, `S` has index prime to `p` in `H` and `H ⧸ C` is a `p`-group,
then `H = S * C`: every element of `H` is a product of an element of `S` and an element of
`C`. -/
theorem sup_eq_of_isPGroup_quotient {H S C : Subgroup G}
    (hS : S ≤ H) (hC : C ≤ H) (hCn : (C.subgroupOf H).Normal)
    (hcop : ¬ p ∣ S.relIndex H)
    (hpg : IsPGroup p (↥H ⧸ (C.subgroupOf H))) :
    S ⊔ C = H := by
  have hp : p.Prime := Fact.out
  have hSCH : S ⊔ C ≤ H := sup_le hS hC
  have h1 : (S ⊔ C).relIndex H ∣ S.relIndex H :=
    ⟨S.relIndex (S ⊔ C),
      by rw [mul_comm]; exact (Subgroup.relIndex_mul_relIndex S (S ⊔ C) H le_sup_left hSCH).symm⟩
  have h2 : (S ⊔ C).relIndex H ∣ C.relIndex H :=
    ⟨C.relIndex (S ⊔ C),
      by rw [mul_comm]; exact (Subgroup.relIndex_mul_relIndex C (S ⊔ C) H le_sup_right hSCH).symm⟩
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  have hk' : C.relIndex H = p ^ k := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]; exact hk
  have hndvd : ¬ p ∣ (S ⊔ C).relIndex H := fun hd => hcop (hd.trans h1)
  have hc : ((S ⊔ C).relIndex H).Coprime p := ((hp.coprime_iff_not_dvd).mpr hndvd).symm
  have hdvd : (S ⊔ C).relIndex H ∣ p ^ k := hk' ▸ h2
  have hd1 : (S ⊔ C).relIndex H = 1 := by
    have := (hc.pow_right k).dvd_of_dvd_mul_right (by rw [one_mul]; exact hdvd)
    exact Nat.dvd_one.mp this
  exact le_antisymm hSCH ((Subgroup.relIndex_eq_one (H := S ⊔ C) (K := H)).mp hd1)

/-- The element-wise form of `sup_eq_of_isPGroup_quotient`. -/
theorem exists_mul_of_sup_eq {H S C : Subgroup G} (hCn : (C.subgroupOf H).Normal)
    (hsup : S ⊔ C = H) {x : G} (hx : x ∈ H) :
    ∃ s ∈ S, ∃ c ∈ C, x = s * c := by
  have hSle : S ≤ H := le_trans le_sup_left (le_of_eq hsup)
  have hCle : C ≤ H := le_trans le_sup_right (le_of_eq hsup)
  have hsub : S.subgroupOf H ⊔ C.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hSle hCle, hsup, Subgroup.subgroupOf_self]
  haveI := hCn
  have hmem : (⟨x, hx⟩ : ↥H) ∈ S.subgroupOf H ⊔ C.subgroupOf H := by
    rw [hsub]; exact Subgroup.mem_top _
  obtain ⟨s, hs, c, hc, hsc⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  exact ⟨(s : G), (Subgroup.mem_subgroupOf.mp hs), (c : G), (Subgroup.mem_subgroupOf.mp hc),
    (congrArg Subtype.val hsc).symm⟩

/-! ### Extremal subgroups -/

/-- `A ≤ P` is *extremal* if the normalizer of `A` in `P` is a Sylow `p`-subgroup of the
normalizer of `A` in `G`, i.e. `[N_G(A) : N_P(A)]` is prime to `p`. -/
def IsExtremal (P : Sylow p G) (A : Subgroup G) : Prop :=
  A ≤ P ∧ IsPGroup p A ∧
    ¬ p ∣ (Subgroup.normalizer (A : Set G) ⊓ (P : Subgroup G)).relIndex
            (Subgroup.normalizer (A : Set G))

/-- For an extremal subgroup whose `N_G(A)/C_G(A)` is a `p`-group, every element of `N_G(A)`
acts on `A` as some element of `N_P(A) ≤ P` does. -/
theorem exists_mul_of_isExtremal {P : Sylow p G} {A : Subgroup G} (hA : IsExtremal P A)
    (hpg : Work.NPC.IsConjPGroup p A) {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    ∃ s ∈ Subgroup.normalizer (A : Set G) ⊓ (P : Subgroup G),
      ∃ c ∈ Subgroup.centralizer (A : Set G), g = s * c := by
  have hS : Subgroup.normalizer (A : Set G) ⊓ (P : Subgroup G) ≤ Subgroup.normalizer (A : Set G) :=
    inf_le_left
  have hC : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.centralizer_le_normalizer (A : Set G)
  have hCn :
      ((Subgroup.centralizer (A : Set G)).subgroupOf (Subgroup.normalizer (A : Set G))).Normal :=
    Subgroup.normal_subgroupOf_centralizer_normalizer (A : Set G)
  have hpg' : IsPGroup p (↥(Subgroup.normalizer (A : Set G)) ⧸
      (Subgroup.centralizer (A : Set G)).subgroupOf (Subgroup.normalizer (A : Set G))) := hpg
  have hsup := sup_eq_of_isPGroup_quotient hS hC hCn hA.2.2 hpg'
  exact exists_mul_of_sup_eq hCn hsup hg

/-- The Sylow `p`-subgroup `P` is extremal as a subgroup of itself. -/
theorem IsExtremal.self (P : Sylow p G) : IsExtremal P (P : Subgroup G) := by
  have hle : (Subgroup.normalizer ((P : Subgroup G) : Set G) ⊓ (P : Subgroup G))
      = (P : Subgroup G) :=
    inf_eq_right.mpr Subgroup.le_normalizer
  refine ⟨le_rfl, P.isPGroup', ?_⟩
  rw [hle]
  exact fun hd => P.not_dvd_index
    (hd.trans (Subgroup.relIndex_dvd_index_of_le (H := (P : Subgroup G)) Subgroup.le_normalizer))

/-- **Every subgroup of `P` has an extremal `G`-conjugate**, and the conjugating element can be
chosen so that it also transports `N_P(A)` into `N_P(A^g)`. -/
theorem exists_extremal_conj (P : Sylow p G) {A : Subgroup G} (hA : A ≤ P) :
    ∃ x : G, (A.map (MulAut.conj x).toMonoidHom) ≤ (P : Subgroup G) ∧
      IsExtremal P (A.map (MulAut.conj x).toMonoidHom) ∧
      (Subgroup.normalizer (A : Set G) ⊓ (P : Subgroup G)).map (MulAut.conj x).toMonoidHom ≤
        (Subgroup.normalizer ((A.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G)) ⊓
          (P : Subgroup G) := by
  have hNA : A ≤ Subgroup.normalizer (A : Set G) := Subgroup.le_normalizer
  have hNPA_le : Subgroup.normalizer (A : Set G) ⊓ (P : Subgroup G) ≤
      Subgroup.normalizer (A : Set G) := inf_le_left
  have hNPA_le_P : Subgroup.normalizer (A : Set G) ⊓ (P : Subgroup G) ≤ (P : Subgroup G) :=
    inf_le_right
  have hpNPA : IsPGroup p ↥(Subgroup.normalizer (A : Set G) ⊓ (P : Subgroup G)) :=
    IsPGroup.of_injective P.isPGroup' (Subgroup.inclusion hNPA_le_P)
      (Subgroup.inclusion_injective hNPA_le_P)
  obtain ⟨Q, hNPAQ, hQH, hpQ, hQcop⟩ := exists_le_of_relIndex_coprime hNPA_le hpNPA
  obtain ⟨S, hQS⟩ := IsPGroup.exists_le_sylow hpQ
  obtain ⟨x, hxS⟩ := MulAction.exists_smul_eq G S P
  have hSmap : (S : Subgroup G).map (MulAut.conj x).toMonoidHom = (P : Subgroup G) := by
    rw [map_conj_eq_smul, ← Sylow.coe_subgroup_smul, hxS]
  have hpA : IsPGroup p A :=
    IsPGroup.of_injective P.isPGroup' (Subgroup.inclusion hA) (Subgroup.inclusion_injective hA)
  have hQmap_le_P : (Q.map (MulAut.conj x).toMonoidHom) ≤ (P : Subgroup G) :=
    le_trans (Subgroup.map_mono hQS) (le_of_eq hSmap)
  have hA_le_Q : A ≤ Q := le_trans (le_inf hNA hA) hNPAQ
  have hNG : Subgroup.normalizer ((A.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G)
      = (Subgroup.normalizer (A : Set G)).map (MulAut.conj x).toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq A (MulAut.conj x)).symm
  have hAmapP : (A.map (MulAut.conj x).toMonoidHom) ≤ (P : Subgroup G) :=
    le_trans (Subgroup.map_mono hA_le_Q) hQmap_le_P
  refine ⟨x, hAmapP, ⟨hAmapP, IsPGroup.map hpA (MulAut.conj x).toMonoidHom, ?_⟩, ?_⟩
  · have hle : (Q.map (MulAut.conj x).toMonoidHom) ≤
        ((Subgroup.normalizer (A : Set G)).map (MulAut.conj x).toMonoidHom) ⊓ (P : Subgroup G) :=
      le_inf (Subgroup.map_mono hQH) hQmap_le_P
    have hdiv := Subgroup.relIndex_dvd_of_le_left
      ((Subgroup.normalizer (A : Set G)).map (MulAut.conj x).toMonoidHom) hle
    rw [Subgroup.relIndex_map_map_of_injective _ _ (MulEquiv.injective (MulAut.conj x))] at hdiv
    rw [hNG]
    exact fun hd => hQcop (hd.trans hdiv)
  · exact le_inf (hNG.symm ▸ (Subgroup.map_mono inf_le_left))
      (le_trans (Subgroup.map_mono hNPAQ) hQmap_le_P)

/-- If `A^y` is extremal, then the conjugating element `y` can be adjusted (on the left, by an
element normalizing `A^y`) so that it also transports `N_P(A)` into `N_P(A^y)`. -/
theorem exists_mul_conj_le_of_isExtremal {P : Sylow p G} {A : Subgroup G} (hA : A ≤ P) {y : G}
    (hC : IsExtremal P (A.map (MulAut.conj y).toMonoidHom)) :
    ∃ n ∈ Subgroup.normalizer (((A.map (MulAut.conj y).toMonoidHom) : Subgroup G) : Set G),
      (Subgroup.normalizer (A : Set G) ⊓ (P : Subgroup G)).map (MulAut.conj (n * y)).toMonoidHom ≤
        (Subgroup.normalizer (((A.map (MulAut.conj y).toMonoidHom) : Subgroup G) : Set G)) ⊓
          (P : Subgroup G) := by
  obtain ⟨-, -, hCcop⟩ := hC
  have hS_le : (Subgroup.normalizer (((A.map (MulAut.conj y).toMonoidHom) : Subgroup G) : Set G) ⊓
      (P : Subgroup G)) ≤
      Subgroup.normalizer (((A.map (MulAut.conj y).toMonoidHom) : Subgroup G) : Set G) := inf_le_left
  have hT_le : (Subgroup.normalizer (A : Set G) ⊓ (P : Subgroup G)).map
        (MulAut.conj y).toMonoidHom ≤
      Subgroup.normalizer (((A.map (MulAut.conj y).toMonoidHom) : Subgroup G) : Set G) := by
    rw [← Subgroup.map_equiv_normalizer_eq A (MulAut.conj y)]
    exact Subgroup.map_mono inf_le_left
  have hNPC_le_P : (Subgroup.normalizer
      (((A.map (MulAut.conj y).toMonoidHom) : Subgroup G) : Set G) ⊓
      (P : Subgroup G)) ≤ (P : Subgroup G) := inf_le_right
  have hpS : IsPGroup p ↥(Subgroup.normalizer
      (((A.map (MulAut.conj y).toMonoidHom) : Subgroup G) : Set G) ⊓ (P : Subgroup G)) :=
    IsPGroup.of_injective P.isPGroup' (Subgroup.inclusion hNPC_le_P)
      (Subgroup.inclusion_injective hNPC_le_P)
  have hNPA_le_P : Subgroup.normalizer (A : Set G) ⊓ (P : Subgroup G) ≤ (P : Subgroup G) :=
    inf_le_right
  have hpNPA : IsPGroup p ↥(Subgroup.normalizer (A : Set G) ⊓ (P : Subgroup G)) :=
    IsPGroup.of_injective P.isPGroup' (Subgroup.inclusion hNPA_le_P)
      (Subgroup.inclusion_injective hNPA_le_P)
  have hpT : IsPGroup p ↥((Subgroup.normalizer (A : Set G) ⊓ (P : Subgroup G)).map
      (MulAut.conj y).toMonoidHom) :=
    IsPGroup.map hpNPA (MulAut.conj y).toMonoidHom
  obtain ⟨n, hn, hnle⟩ := exists_conj_le_of_relIndex_coprime hS_le hT_le hpS hpT hCcop
  refine ⟨n, hn, ?_⟩
  have hcomp : (MulAut.conj n).toMonoidHom.comp (MulAut.conj y).toMonoidHom
      = (MulAut.conj (n * y)).toMonoidHom := by
    ext z
    simp only [MonoidHom.comp_apply]
    rw [conj_toMonoidHom_apply, conj_toMonoidHom_apply, conj_toMonoidHom_apply]
    group
  rw [Subgroup.map_map, hcomp] at hnle
  exact hnle

/-! ### The fusion induction -/

/-- `ConjBy P A g`: the action of `g` on `A` agrees with the action of some `r ∈ P`. -/
def ConjBy (P : Sylow p G) (A : Subgroup G) (g : G) : Prop :=
  ∃ r ∈ (P : Subgroup G), ∀ a ∈ A, r * a * r⁻¹ = g * a * g⁻¹

theorem ConjBy.bot (P : Sylow p G) (g : G) : ConjBy P ⊥ g :=
  ⟨1, one_mem _, fun a ha => by rw [Subgroup.mem_bot.mp ha]; group⟩

theorem ConjBy.mono {P : Sylow p G} {A A' : Subgroup G} {g : G} (h : ConjBy P A g)
    (hA : A' ≤ A) : ConjBy P A' g := by
  obtain ⟨r, hr, hconj⟩ := h
  exact ⟨r, hr, fun a ha => hconj a (hA ha)⟩

theorem ConjBy.inv {P : Sylow p G} {A : Subgroup G} {g : G} (h : ConjBy P A g) :
    ConjBy P (A.map (MulAut.conj g).toMonoidHom) g⁻¹ := by
  obtain ⟨r, hr, hconj⟩ := h
  refine ⟨r⁻¹, (P : Subgroup G).inv_mem hr, ?_⟩
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
  have hga : (MulEquiv.toMonoidHom (MulAut.conj g)) a = g * a * g⁻¹ := conj_toMonoidHom_apply g a
  have hra : (MulEquiv.toMonoidHom (MulAut.conj g)) a = r * a * r⁻¹ := by
    rw [hga]; exact (hconj a ha).symm
  conv_lhs => rw [hra]
  conv_rhs => rw [hga]
  group

theorem ConjBy.comp {P : Sylow p G} {A : Subgroup G} {g h : G} (hg : ConjBy P A g)
    (hh : ConjBy P (A.map (MulAut.conj g).toMonoidHom) h) : ConjBy P A (h * g) := by
  obtain ⟨r, hr, hconj⟩ := hg
  obtain ⟨s, hs, hconj'⟩ := hh
  refine ⟨s * r, (P : Subgroup G).mul_mem hs hr, ?_⟩
  intro a ha
  have h1 : r * a * r⁻¹ = g * a * g⁻¹ := hconj a ha
  have h2 : g * a * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have h3 := hconj' (g * a * g⁻¹) h2
  calc (s * r) * a * (s * r)⁻¹ = s * (r * a * r⁻¹) * s⁻¹ := by group
    _ = s * (g * a * g⁻¹) * s⁻¹ := by rw [h1]
    _ = h * (g * a * g⁻¹) * h⁻¹ := h3
    _ = (h * g) * a * (h * g)⁻¹ := by group

/-- An element of `N_G(B)` acts on the extremal subgroup `B` as an element of `P` does. -/
theorem ConjBy.of_mem_normalizer {P : Sylow p G} {B : Subgroup G} {g : G}
    (hB : IsExtremal P B) (hpg : Work.NPC.IsConjPGroup p B)
    (hg : g ∈ Subgroup.normalizer (B : Set G)) : ConjBy P B g := by
  obtain ⟨s, hs, c, hc, hsc⟩ := exists_mul_of_isExtremal hB hpg hg
  refine ⟨s, hs.2, fun b hb => ?_⟩
  have hcb : c * b * c⁻¹ = b := by
    have h1 : b * c = c * b := (Subgroup.mem_centralizer_iff.mp hc) b hb
    rw [← h1]; group
  calc s * b * s⁻¹ = s * (c * b * c⁻¹) * s⁻¹ := by rw [hcb]
    _ = (s * c) * b * (s * c)⁻¹ := by group
    _ = g * b * g⁻¹ := by rw [hsc]

/-- **The fusion induction.**  If Frobenius' condition holds in `G`, then for every subgroup
`A ≤ P` and every `g ∈ G` with `A^g ≤ P`, the action of `g` on `A` agrees with the action of
some element of `P`. -/
theorem conjBy_of_le_sylow (h : Work.NPC.HasFrobeniusCondition p G) (P : Sylow p G)
    (n : ℕ) :
    ∀ A : Subgroup G, A ≤ (P : Subgroup G) → A.relIndex (P : Subgroup G) = n →
      ∀ g : G, (∀ a ∈ A, g * a * g⁻¹ ∈ (P : Subgroup G)) → ConjBy P A g := by
  induction n using Nat.strong_induction_on with
  | h N ih =>
    intro A hA hidx g hg
    by_cases hbot : A = ⊥
    · subst hbot; exact ConjBy.bot P g
    rcases eq_or_lt_of_le hA with h_eq | h_lt
    · -- Case `A = P`
      have hPd : (P : Subgroup G) ≠ ⊥ := fun h => hbot (h_eq.trans h)
      have hPP : Work.NPC.IsConjPGroup p (P : Subgroup G) := h _ P.isPGroup' hPd
      have hg' : ∀ a ∈ (P : Subgroup G), g * a * g⁻¹ ∈ (P : Subgroup G) :=
        fun a ha => hg a (h_eq ▸ ha)
      have hmap1 : ((P : Subgroup G).map (MulAut.conj g).toMonoidHom) = (P : Subgroup G) := by
        refine Subgroup.eq_of_le_of_card_ge ?_ ?_
        · rw [Subgroup.map_le_iff_le_comap]
          intro a ha
          exact hg' a ha
        · rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]
      have hnorm : g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
        mem_normalizer_of_map_conj_eq_self hmap1
      have hres : ConjBy P (P : Subgroup G) g :=
        ConjBy.of_mem_normalizer (IsExtremal.self P) hPP hnorm
      rw [h_eq]
      exact hres
    · -- Case `A < P`
      set A₁ := (P : Subgroup G) ⊓ ((P : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom) with hA₁def
      have hA_le_A₁ : A ≤ A₁ := by
        refine le_inf hA ?_
        intro a ha
        have h1 : g * a * g⁻¹ ∈ (P : Subgroup G) := hg a ha
        exact Subgroup.mem_map.mpr ⟨g * a * g⁻¹, h1, by
          show (MulAut.conj g⁻¹) (g * a * g⁻¹) = a
          rw [MulAut.conj_apply]; group⟩
      by_cases hstrict : A < A₁
      · -- Step 1: the induction hypothesis applies to the strictly bigger group `A₁`
        have hA₁le : A₁ ≤ (P : Subgroup G) := inf_le_left
        have hgA₁ : ∀ a ∈ A₁, g * a * g⁻¹ ∈ (P : Subgroup G) := by
          intro a ha
          obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp ha.2
          have hb' : g * a * g⁻¹ = b := by rw [← hba, conj_toMonoidHom_apply]; group
          rw [hb']; exact hb
        have hidxA₁ : A₁.relIndex (P : Subgroup G) < N := by
          rw [← hidx]
          exact relIndex_lt_of_lt_of_le hA hA₁le hstrict
        exact (ih _ hidxA₁ A₁ hA₁le rfl g hgA₁).mono hA_le_A₁
      · -- Step 2: `A = A₁`
        obtain ⟨x, hxP, hxEx, hxtrans⟩ := exists_extremal_conj P hA
        set C := A.map (MulAut.conj x).toMonoidHom with hCdef
        have hCne : C ≠ ⊥ := by
          rw [hCdef]
          intro hc
          exact hbot (Subgroup.map_injective (MulEquiv.injective (MulAut.conj x))
            (by rw [hc, Subgroup.map_bot]))
        have hCpg : Work.NPC.IsConjPGroup p C := h _ hxEx.2.1 hCne
        -- induction hypothesis on `N_P(A)`
        have hNPA_gt : A < Subgroup.normalizer (A : Set G) ⊓ (P : Subgroup G) :=
          lt_normalizer_of_lt_of_isPGroup P.isPGroup' h_lt
        have hidxNPA : (Subgroup.normalizer (A : Set G) ⊓ (P : Subgroup G)).relIndex
            (P : Subgroup G) < N := by
          rw [← hidx]
          exact relIndex_lt_of_lt_of_le hA inf_le_right hNPA_gt
        have hAx : ∀ a ∈ Subgroup.normalizer (A : Set G) ⊓ (P : Subgroup G),
            x * a * x⁻¹ ∈ (P : Subgroup G) :=
          fun a ha => (Subgroup.mem_inf.mp (hxtrans (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩))).2
        have hxNPA : ConjBy P (Subgroup.normalizer (A : Set G) ⊓ (P : Subgroup G)) x :=
          ih _ hidxNPA _ inf_le_right rfl x hAx
        have hA_x : ConjBy P A x := hxNPA.mono (le_inf Subgroup.le_normalizer hA)
        -- the `B`-side
        set B := A.map (MulAut.conj g).toMonoidHom with hBdef
        have hBleP : B ≤ (P : Subgroup G) := by
          rw [hBdef, Subgroup.map_le_iff_le_comap]
          intro a ha
          exact hg a ha
        have hBcard : Nat.card ↥B = Nat.card ↥A := by
          rw [hBdef]; exact Subgroup.card_map_of_injective (MulEquiv.injective _)
        have hB_lt_P : B < (P : Subgroup G) := by
          refine lt_of_le_of_ne hBleP ?_
          intro hBP
          have h1 : Nat.card ↥B = Nat.card ↥(P : Subgroup G) := by rw [hBP]
          rw [hBcard] at h1
          exact (ne_of_lt h_lt) (Subgroup.eq_of_le_of_card_ge hA h1.symm.le)
        have hByC : B.map (MulAut.conj (x * g⁻¹)).toMonoidHom = C := by
          rw [hBdef, hCdef, map_conj_mul, show x * g⁻¹ * g = x by group]
        have hCyEx : IsExtremal P (B.map (MulAut.conj (x * g⁻¹)).toMonoidHom) := by
          rw [hByC]; exact hxEx
        obtain ⟨m, hm, hmtrans⟩ := exists_mul_conj_le_of_isExtremal hBleP hCyEx
        have hmC : m ∈ Subgroup.normalizer (C : Set G) := by
          rw [← hByC]; exact hm
        set k := m * (x * g⁻¹) with hkdef
        have hmmap : C.map (MulAut.conj m).toMonoidHom = C :=
          map_conj_eq_self_of_mem_normalizer hmC
        have hkB : B.map (MulAut.conj k).toMonoidHom = C := by
          rw [hkdef, ← map_conj_mul B m (x * g⁻¹), hByC, hmmap]
        have hktrans : (Subgroup.normalizer (B : Set G) ⊓ (P : Subgroup G)).map
            (MulAut.conj k).toMonoidHom ≤
            Subgroup.normalizer (C : Set G) ⊓ (P : Subgroup G) := by
          rw [hkdef]
          rw [hByC] at hmtrans
          exact hmtrans
        -- induction hypothesis on `N_P(B)`
        have hidxNPB : (Subgroup.normalizer (B : Set G) ⊓ (P : Subgroup G)).relIndex
            (P : Subgroup G) < N := by
          have h1 : B.relIndex (P : Subgroup G) = A.relIndex (P : Subgroup G) :=
            relIndex_eq_of_card_eq hBleP hA hBcard
          rw [hidx] at h1
          rw [← h1]
          exact relIndex_lt_of_lt_of_le hBleP inf_le_right
            (lt_normalizer_of_lt_of_isPGroup P.isPGroup' hB_lt_P)
        have hBk : ∀ b ∈ Subgroup.normalizer (B : Set G) ⊓ (P : Subgroup G),
            k * b * k⁻¹ ∈ (P : Subgroup G) :=
          fun b hb => (Subgroup.mem_inf.mp (hktrans (Subgroup.mem_map.mpr ⟨b, hb, rfl⟩))).2
        have hkNPB : ConjBy P (Subgroup.normalizer (B : Set G) ⊓ (P : Subgroup G)) k :=
          ih _ hidxNPB _ inf_le_right rfl k hBk
        have hB_k : ConjBy P B k := hkNPB.mono (le_inf Subgroup.le_normalizer hBleP)
        have hC_kinv : ConjBy P C k⁻¹ := by
          have hh := ConjBy.inv hB_k
          rwa [hkB] at hh
        -- the element `k * g * x⁻¹` normalizes `C`
        have hCx : C.map (MulAut.conj x⁻¹).toMonoidHom = A := by
          rw [hCdef, map_conj_mul, inv_mul_cancel, conj_one_toMonoidHom, Subgroup.map_id]
        have hkgC : A.map (MulAut.conj (k * g)).toMonoidHom = C := by
          rw [← map_conj_mul A k g, ← hBdef, hkB]
        have hx'mem : k * g * x⁻¹ ∈ Subgroup.normalizer (C : Set G) := by
          apply mem_normalizer_of_map_conj_eq_self
          rw [← map_conj_mul C (k * g) x⁻¹, hCx]
          exact hkgC
        have hC_x' : ConjBy P C (k * g * x⁻¹) :=
          ConjBy.of_mem_normalizer hxEx hCpg hx'mem
        -- assembly
        have h2 : ConjBy P (A.map (MulAut.conj x).toMonoidHom) (k * g * x⁻¹) := by
          rw [← hCdef]; exact hC_x'
        have h3 : ConjBy P A ((k * g * x⁻¹) * x) := ConjBy.comp hA_x h2
        have h4 : ConjBy P A (k * g) := by
          rw [show (k * g * x⁻¹) * x = k * g by group] at h3
          exact h3
        have h5 : ConjBy P (A.map (MulAut.conj (k * g)).toMonoidHom) k⁻¹ := by
          rw [hkgC]; exact hC_kinv
        have h6 : ConjBy P A (k⁻¹ * (k * g)) := ConjBy.comp h4 h5
        have h7 : ConjBy P A g := by
          rw [show k⁻¹ * (k * g) = g by group] at h6
          exact h6
        exact h7


/-- **Frobenius' hypothesis implies that a Sylow `p`-subgroup is conjugacy closed**: two
elements of a Sylow `p`-subgroup that are conjugate in the whole group are already conjugate
inside the Sylow subgroup. -/
theorem conjugacyClosed_sylow_of_hasFrobeniusCondition {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (h : Work.NPC.HasFrobeniusCondition p G) :
    ∀ x y : ↥(P : Subgroup G), IsConj (x : G) (y : G) → IsConj x y := by
  intro x y hxy
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  set A := Subgroup.zpowers (x : G) with hAdef
  have hA_le : A ≤ (P : Subgroup G) := Subgroup.zpowers_le.mpr x.2
  have hcA : ∀ a ∈ A, c * a * c⁻¹ ∈ (P : Subgroup G) := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have h1 : c * (x : G) ^ k * c⁻¹ = (y : G) ^ k := by
      rw [← conj_toMonoidHom_apply c ((x : G) ^ k), map_zpow,
        conj_toMonoidHom_apply c (x : G), ← hc]
    rw [h1]
    exact (P : Subgroup G).zpow_mem y.2 k
  obtain ⟨r, hr, hri⟩ :=
    conjBy_of_le_sylow h P (A.relIndex (P : Subgroup G)) A hA_le rfl c hcA
  have hx : (x : G) ∈ A := Subgroup.mem_zpowers (x : G)
  have hkey : r * (x : G) * r⁻¹ = (y : G) := by
    rw [← hc]
    exact hri (x : G) hx
  refine isConj_iff.mpr ⟨⟨r, hr⟩, ?_⟩
  apply Subtype.ext
  show r * (x : G) * r⁻¹ = (y : G)
  exact hkey

end Work.NPC.Frobenius
