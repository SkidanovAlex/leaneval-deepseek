import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.Omega1
import Submission.Work.PGroup.omega_one_eq_omega1
import Submission.Work.PGroup.card_sup_mul_card_inf
import Submission.Work.PGroup.Symplectic.Basic
import Submission.Work.PGroup.Symplectic.centralProduct_of_structure
import Submission.Work.PGroup.Symplectic.card_quotient_center_pow_even
import Submission.Work.PGroup.Symplectic.omega1_eq_pow_eq_one_of_class_two
import Submission.Work.PGroup.Symplectic.isMulCommutative_of_isMulCommutative_omega1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The structure of `Ω₁` for a class-two `p`-group with cyclic centre

Let `C` be a finite `p`-group (`p` an odd prime) of nilpotency class at most two
(`⁅C,C⁆ ≤ Z(C)`), all of whose `p`-th powers are central, whose centre is cyclic, and in which
every abelian characteristic subgroup is cyclic.  Assume moreover that `C` is non-commutative.
Then the subgroup `Ω₁ = ⟨x ∈ C | x ^ p = 1⟩` has the following properties:

* `Ω₁` is non-commutative and of exponent dividing `p`;
* `Ω₁ ≤ C` and `C = Z(C) · Ω₁`;
* `Z(Ω₁) = ⁅C, C⁆` has order `p`.

This is the "class two" part of P. Hall's theorem on `p`-groups of symplectic type
(Feit–Thompson 3.5, Gorenstein Theorem 5.4.9).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical Pointwise commutatorElement IsMulCommutative
open Subgroup

noncomputable section

namespace Work.PGroup.Symplectic

/-- Membership in the centre of a subgroup, transported to the ambient group. -/
theorem mem_center_map_subtype_iff {G : Type*} [Group G] {K : Subgroup G} {x : G} :
    x ∈ (Subgroup.center ↥K).map K.subtype ↔ x ∈ K ∧ ∀ y ∈ K, y * x = x * y := by
  constructor
  · intro hx
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hx
    refine ⟨hcx ▸ c.2, fun y hy => ?_⟩
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc (⟨y, hy⟩ : ↥K))
    exact hcx ▸ h
  · rintro ⟨hxK, hxy⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hxy g.1 g.2)

/-- An injective homomorphism sends the centre of a subgroup onto the centre of its image. -/
theorem center_map_subtype_map {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (K : Subgroup A) :
    (Subgroup.center ↥(K.map f)).map (K.map f).subtype
      = ((Subgroup.center ↥K).map K.subtype).map f := by
  let e : ↥K ≃* ↥(K.map f) := Subgroup.equivMapOfInjective K f hf
  have h1 : (Subgroup.center ↥K).map e.toMonoidHom = Subgroup.center ↥(K.map f) :=
    Subgroup.map_center_eq e
  have h2 : ((K.map f).subtype.comp e.toMonoidHom) = f.comp K.subtype :=
    MonoidHom.ext fun k => rfl
  rw [← h1, Subgroup.map_map, h2, ← Subgroup.map_map]

theorem omega_one_structure_of_class_two {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2) (C : Subgroup X) (hCpg : IsPGroup p ↥C)
    (hclass : ⁅C, C⁆ ≤ (Subgroup.center ↥C).map C.subtype)
    (hquot : ∀ x ∈ C, x ^ p ∈ (Subgroup.center ↥C).map C.subtype)
    (hcyc : ∃ a : X, (Subgroup.center ↥C).map C.subtype = Subgroup.zpowers a)
    (hdc : ∀ A : Subgroup ↥C, A.Characteristic → IsMulCommutative A → ∃ a : ↥C, A = Subgroup.zpowers a)
    (hnab : ¬ IsMulCommutative ↥C) :
    ¬ IsMulCommutative ↥(Subgroup.closure {x : X | x ∈ C ∧ x ^ p = 1}) ∧
    (∀ x : ↥(Subgroup.closure {x : X | x ∈ C ∧ x ^ p = 1}), x ^ p = 1) ∧
    Subgroup.closure {x : X | x ∈ C ∧ x ^ p = 1} ≤ C ∧
    Nat.card (Subgroup.center ↥(Subgroup.closure {x : X | x ∈ C ∧ x ^ p = 1})) = p ∧
    (Subgroup.center ↥(Subgroup.closure {x : X | x ∈ C ∧ x ^ p = 1})).map
        (Subgroup.closure {x : X | x ∈ C ∧ x ^ p = 1}).subtype = ⁅C, C⁆ ∧
    C = (Subgroup.center ↥C).map C.subtype ⊔ Subgroup.closure {x : X | x ∈ C ∧ x ^ p = 1} ∧
    Nat.card (⁅C, C⁆ : Subgroup X) = p := by
  classical
  -- Local notation.
  let Om : Subgroup ↥C := Work.PGroup.omega1 (↥C) p ⊤
  let Ω : Subgroup X := Subgroup.closure {x : X | x ∈ C ∧ x ^ p = 1}
  let Z : Subgroup X := (Subgroup.center ↥C).map C.subtype
  let D : Subgroup X := ⁅C, C⁆
  -- `Ω` is the image of `Om` under the subtype map.
  have hΩeq : Ω = Om.map C.subtype := by
    show Subgroup.closure {x : X | x ∈ C ∧ x ^ p = 1}
        = (Subgroup.closure {x : ↥C | x ∈ ⊤ ∧ x ^ p = 1}).map C.subtype
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hyC, hyp⟩
      exact ⟨⟨y, hyC⟩, ⟨trivial, by apply Subtype.ext; simpa using hyp⟩, rfl⟩
    · rintro ⟨o, ⟨-, ho⟩, hox⟩
      rw [← hox]
      exact ⟨o.2, by rw [← map_pow, ho, map_one]⟩
  have hΩleC : Ω ≤ C := by
    rw [hΩeq]
    exact Subgroup.map_subtype_le _
  have hDleC : D ≤ C := hclass.trans (Subgroup.map_subtype_le _)
  -- Class two in `↥C` and centrality of `p`-th powers.
  have hclassC : ⁅(⊤ : Subgroup ↥C), (⊤ : Subgroup ↥C)⁆ ≤ Subgroup.center ↥C := by
    rw [← Subgroup.map_le_map_iff_of_injective (f := C.subtype) C.subtype_injective]
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    exact hclass
  have hquotC : ∀ x : ↥C, x ^ p ∈ Subgroup.center ↥C := by
    intro x
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (mem_center_map_subtype_iff.mp (hquot x x.2)).2 y y.2
  have hcycC : ∃ a : ↥C, Subgroup.center ↥C = Subgroup.zpowers a := by
    obtain ⟨a, ha⟩ := hcyc
    have haZ : a ∈ Z := by
      have : Z = Subgroup.zpowers a := ha
      rw [this]
      exact Subgroup.mem_zpowers a
    have haC : a ∈ C := Subgroup.map_subtype_le _ haZ
    refine ⟨⟨a, haC⟩, ?_⟩
    refine Subgroup.map_injective C.subtype_injective ?_
    show (Subgroup.center ↥C).map C.subtype = (Subgroup.zpowers (⟨a, haC⟩ : ↥C)).map C.subtype
    rw [MonoidHom.map_zpowers]
    simpa using ha
  have hOmChar : Om.Characteristic :=
    Work.PGroup.omega1_characteristic (H := ↥C) p (by
      rw [Subgroup.characteristic_iff_map_eq]
      intro φ
      simp)
  have hΩmem : ∀ x : ↥C, x ∈ Om ↔ x ^ p = 1 :=
    omega1_eq_pow_eq_one_of_class_two hp hodd hclassC hquotC
  have hΩmemX : ∀ x : X, x ∈ Ω ↔ x ∈ C ∧ x ^ p = 1 := by
    intro x
    rw [hΩeq, Subgroup.mem_map]
    constructor
    · rintro ⟨o, ho, hox⟩
      rw [← hox]
      have ho' : o ^ p = 1 := (hΩmem o).mp ho
      exact ⟨o.2, by rw [← map_pow, ho', map_one]⟩
    · rintro ⟨hxC, hxp⟩
      exact ⟨⟨x, hxC⟩, (hΩmem _).mpr (Subtype.ext (by simpa using hxp)), rfl⟩
  -- The `p`-th power homomorphism on `↥C`.
  have hcommC : ∀ a b : ↥C, ⁅a, b⁆ ^ p = 1 :=
    fun a b => commutator_pow_eq_one_of_pow_mem_center hclassC hquotC a b
  let φ : ↥C →* ↥C :=
    { toFun := fun x => x ^ p
      map_one' := one_pow p
      map_mul' := Work.PGroup.Symplectic.pow_mul_eq_of_class_two hp hodd hclassC hcommC }
  have hφker : φ.ker = Om := by
    ext x
    rw [MonoidHom.mem_ker, show φ x = x ^ p from rfl, hΩmem x]
  have hφrange : φ.range ≤ Subgroup.center ↥C := by
    intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    exact hquotC x
  -- `D` has exponent dividing `p`.
  have hsD : Subgroup.closure {g : X | ∃ g₁ ∈ C, ∃ g₂ ∈ C, ⁅g₁, g₂⁆ = g} ≤ D := by
    rw [Subgroup.closure_le]
    rintro g ⟨u, hu, v, hv, rfl⟩
    exact Subgroup.commutator_mem_commutator hu hv
  have hZab : ∀ a b : X, a ∈ Z → b ∈ Z → a * b = b * a := by
    intro a b ha hb
    exact congrArg Subtype.val
      (isMulCommutative_iff.mp (inferInstance : IsMulCommutative ↥Z) ⟨a, ha⟩ ⟨b, hb⟩)
  have hDpow : ∀ x ∈ (D : Subgroup X), x ^ p = 1 := by
    have key : ∀ x ∈ Subgroup.closure {g : X | ∃ g₁ ∈ C, ∃ g₂ ∈ C, ⁅g₁, g₂⁆ = g}, x ^ p = 1 := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
          obtain ⟨u, hu, v, hv, rfl⟩ := hy
          have hmem : ⁅u, v⁆ ∈ Z := hclass (Subgroup.commutator_mem_commutator hu hv)
          have hcu : Commute u ⁅u, v⁆ := (mem_center_map_subtype_iff.mp hmem).2 u hu
          rw [hcu.commutatorElement_pow_left p]
          have hv' : Commute (u ^ p) v :=
            ((mem_center_map_subtype_iff.mp (hquot u hu)).2 v hv).symm
          exact commutatorElement_eq_one_iff_mul_comm.mpr hv'
      | one => exact one_pow p
      | mul a b ha hb iha ihb =>
          have haZ : a ∈ Z := hclass (hsD ha)
          have hbZ : b ∈ Z := hclass (hsD hb)
          rw [Commute.mul_pow (hZab a b haZ hbZ) p, iha, one_mul, ihb]
      | inv a ha iha => rw [inv_pow, iha, inv_one]
    intro x hx
    exact key x (by rw [← Subgroup.commutator_def C C]; exact hx)
  have hDcard : Nat.card ↥D = p := by
    obtain ⟨a, ha⟩ := hcyc
    haveI : IsCyclic ↥(Subgroup.zpowers a) := isCyclic_zpowers a
    haveI : IsCyclic ↥D := Subgroup.isCyclic_of_le (ha ▸ hclass)
    have hDexp : ∀ x : ↥D, x ^ p = 1 := fun x => Subtype.ext (by
      simpa using hDpow (x : X) x.2)
    have hExpDvd : Monoid.exponent ↥D ∣ p :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hDexp
    have hcardDvd : Nat.card ↥D ∣ p := by
      rw [← IsCyclic.exponent_eq_card]; exact hExpDvd
    have hne : Nat.card ↥D ≠ 1 := by
      intro h1
      refine hnab ?_
      rw [isMulCommutative_iff]
      intro x y
      apply Subtype.ext
      have hDbot : D = ⊥ := Subgroup.card_eq_one.mp h1
      have hmem : ⁅(x : X), (y : X)⁆ ∈ D := Subgroup.commutator_mem_commutator x.2 y.2
      rw [hDbot, Subgroup.mem_bot] at hmem
      exact commutatorElement_eq_one_iff_mul_comm.mp hmem
    rcases hp.eq_one_or_self_of_dvd (Nat.card ↥D) hcardDvd with h | h
    · exact absurd h hne
    · exact h
  have hderC : Nat.card (⁅(⊤ : Subgroup ↥C), (⊤ : Subgroup ↥C)⁆ : Subgroup ↥C) = p := by
    have hmap : (⁅(⊤ : Subgroup ↥C), (⊤ : Subgroup ↥C)⁆ : Subgroup ↥C).map C.subtype = D := by
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    rw [← Subgroup.card_map_of_injective (f := C.subtype)
          (K := (⁅(⊤ : Subgroup ↥C), (⊤ : Subgroup ↥C)⁆ : Subgroup ↥C)) C.subtype_injective, hmap,
        hDcard]
  -- `Ω` has exponent `p`.
  have hΩexp : ∀ x : ↥Ω, x ^ p = 1 := by
    intro x
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact ((hΩmemX (x : X)).mp x.2).2
  -- `Ω` is non-commutative.
  have hΩnonab : ¬ IsMulCommutative ↥Ω := by
    intro hab
    have hOmab : IsMulCommutative ↥Om := by
      have e : ↥Om ≃* ↥Ω :=
        (Subgroup.equivMapOfInjective Om C.subtype C.subtype_injective).trans
          ((MulEquiv.subgroupCongr hΩeq).symm)
      rw [isMulCommutative_iff]
      intro a b
      exact e.injective (by
        rw [map_mul, map_mul]
        exact isMulCommutative_iff.mp hab (e a) (e b))
    exact hnab (isMulCommutative_of_isMulCommutative_omega1 hp hodd hCpg hclassC hquotC hcycC hdc
      hOmab)
  have hDleΩ : D ≤ Ω := fun x hx => (hΩmemX x).mpr ⟨hDleC hx, hDpow x hx⟩
  have hΩΩleD : ⁅Ω, Ω⁆ ≤ D := Subgroup.commutator_mono hΩleC hΩleC
  have hΩΩleΩ : ⁅Ω, Ω⁆ ≤ Ω := hΩΩleD.trans hDleΩ
  have hD_eqΩ : D = ⁅Ω, Ω⁆ := by
    have hne : ⁅Ω, Ω⁆ ≠ ⊥ := by
      intro hbot
      refine hΩnonab ?_
      rw [isMulCommutative_iff]
      intro x y
      apply Subtype.ext
      have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot x.2
      exact ((Subgroup.mem_centralizer_iff.mp h1 y.1 y.2)).symm
    refine (Subgroup.eq_of_le_of_card_ge hΩΩleD ?_).symm
    have hdvd := Subgroup.card_dvd_of_le hΩΩleD
    rw [hDcard] at hdvd
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd h (fun hc => hne (Subgroup.card_eq_one.mp hc))
    · rw [hDcard, h]
  have hΩΩleW : ⁅Ω, Ω⁆ ≤ (Subgroup.center ↥Ω).map Ω.subtype := by
    intro x hx
    rw [mem_center_map_subtype_iff]
    have hxZ : x ∈ Z := hclass (hΩΩleD hx)
    exact ⟨hΩΩleΩ hx, fun y hy => (mem_center_map_subtype_iff.mp hxZ).2 y (hΩleC hy)⟩
  have hclassΩ : ⁅(⊤ : Subgroup ↥Ω), (⊤ : Subgroup ↥Ω)⁆ ≤ Subgroup.center ↥Ω := by
    rw [← Subgroup.map_le_map_iff_of_injective (f := Ω.subtype) Ω.subtype_injective]
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    exact hΩΩleW
  have hderΩ : Nat.card (⁅(⊤ : Subgroup ↥Ω), (⊤ : Subgroup ↥Ω)⁆ : Subgroup ↥Ω) = p := by
    have hmap : (⁅(⊤ : Subgroup ↥Ω), (⊤ : Subgroup ↥Ω)⁆ : Subgroup ↥Ω).map Ω.subtype = D := by
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hD_eqΩ]
    rw [← Subgroup.card_map_of_injective (f := Ω.subtype)
          (K := (⁅(⊤ : Subgroup ↥Ω), (⊤ : Subgroup ↥Ω)⁆ : Subgroup ↥Ω)) Ω.subtype_injective, hmap,
        hDcard]
  have hquotΩ : ∀ x : ↥Ω, x ^ p ∈ Subgroup.center ↥Ω := by
    intro x
    rw [hΩexp x]
    exact Subgroup.one_mem _
  -- Parity of the exponents of `|C/Z(C)|` and `|Ω/Z(Ω)|`.
  obtain ⟨m, hm⟩ := card_quotient_center_pow_even (H := ↥C) hp hodd hclassC hderC hquotC
  obtain ⟨k, hk⟩ := card_quotient_center_pow_even (H := ↥Ω) hp hodd hclassΩ hderΩ hquotΩ
  -- The centre of `Ω`, transported to `↥C`, is characteristic and abelian.
  have hOmCenterMap : ((Subgroup.center ↥Om).map Om.subtype).map C.subtype
      = (Subgroup.center ↥Ω).map Ω.subtype := by
    rw [hΩeq]
    exact (center_map_subtype_map C.subtype C.subtype_injective Om).symm
  have hZOchar : ((Subgroup.center ↥Om).map Om.subtype).Characteristic := by
    haveI := hOmChar
    exact Subgroup.characteristic_of_characteristic_of_characteristic
  have hZOab : IsMulCommutative ↥((Subgroup.center ↥Om).map Om.subtype) := inferInstance
  obtain ⟨a0, ha0⟩ := hdc _ hZOchar hZOab
  have hZOcyc : IsCyclic ↥(((Subgroup.center ↥Om).map Om.subtype).map C.subtype) := by
    rw [ha0, MonoidHom.map_zpowers]
    exact isCyclic_zpowers _
  have hWcyc : IsCyclic ↥((Subgroup.center ↥Ω).map Ω.subtype) := hOmCenterMap ▸ hZOcyc
  have hDleW : D ≤ (Subgroup.center ↥Ω).map Ω.subtype := by
    rw [hD_eqΩ]; exact hΩΩleW
  have hWcard : Nat.card ↥((Subgroup.center ↥Ω).map Ω.subtype) = p := by
    haveI : IsCyclic ↥((Subgroup.center ↥Ω).map Ω.subtype) := hWcyc
    have hWexp : ∀ x : ↥((Subgroup.center ↥Ω).map Ω.subtype), x ^ p = 1 := by
      intro x
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      have h := congrArg (fun t : ↥Ω => (t : X))
        (hΩexp ⟨(x : X), Subgroup.map_subtype_le _ x.2⟩)
      simpa using h
    have hdvd : Nat.card ↥((Subgroup.center ↥Ω).map Ω.subtype) ∣ p := by
      rw [← IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hWexp
    have hge : p ∣ Nat.card ↥((Subgroup.center ↥Ω).map Ω.subtype) := by
      have h := Subgroup.card_dvd_of_le hDleW
      rwa [hDcard] at h
    exact Nat.dvd_antisymm hdvd hge
  have hWeqD : (Subgroup.center ↥Ω).map Ω.subtype = D :=
    (Subgroup.eq_of_le_of_card_ge hDleW (by rw [hWcard, hDcard])).symm
  have hcenterΩ : Nat.card ↥(Subgroup.center ↥Ω) = p := by
    rw [← Subgroup.card_map_of_injective (f := Ω.subtype) (K := Subgroup.center ↥Ω)
      Ω.subtype_injective]
    exact hWcard
  have hZinfΩ : Z ⊓ Ω = D := by
    refine le_antisymm ?_ (le_inf hclass hDleΩ)
    intro x hx
    obtain ⟨hxZ, hxΩ⟩ := Subgroup.mem_inf.mp hx
    rw [← hWeqD]
    exact mem_center_map_subtype_iff.mpr
      ⟨hxΩ, fun y hy => (mem_center_map_subtype_iff.mp hxZ).2 y (hΩleC hy)⟩
  -- Cardinality bookkeeping.
  have hcardmono : ∀ {H K : Subgroup X}, H ≤ K → Nat.card ↥H ≤ Nat.card ↥K :=
    fun {H K} h => Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le h)
  have hCcard : Nat.card ↥C = p ^ (2 * m) * Nat.card ↥(Subgroup.center ↥C) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥C), hm]
  have hΩcard : Nat.card ↥Ω = p ^ (2 * k) * p := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Ω), hk, hcenterΩ]
  have hZcard : Nat.card ↥Z = Nat.card ↥(Subgroup.center ↥C) :=
    Subgroup.card_map_of_injective C.subtype_injective
  have hOmcard : Nat.card (↥C ⧸ Om) = Nat.card ↥φ.range := by
    rw [← hφker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ)
  have hkm : k ≤ m := by
    have hcommZΩ : ∀ a ∈ Z, ∀ b ∈ Ω, a * b = b * a := by
      intro a ha b hb
      exact ((mem_center_map_subtype_iff.mp ha).2 b (hΩleC hb)).symm
    have hsup := Work.PGroup.card_sup_mul_card_inf Z Ω hcommZΩ
    have hinfD : Nat.card ↥(Z ⊓ Ω) = p := by rw [hZinfΩ]; exact hDcard
    have hsupcard : Nat.card ↥(Z ⊔ Ω) = p ^ (2 * k) * Nat.card ↥(Subgroup.center ↥C) := by
      have h1 : Nat.card ↥(Z ⊔ Ω) * p = p ^ (2 * k) * Nat.card ↥(Subgroup.center ↥C) * p := by
        calc Nat.card ↥(Z ⊔ Ω) * p = Nat.card ↥(Z ⊔ Ω) * Nat.card ↥(Z ⊓ Ω) := by rw [hinfD]
          _ = Nat.card ↥Z * Nat.card ↥Ω := hsup
          _ = Nat.card ↥(Subgroup.center ↥C) * (p ^ (2 * k) * p) := by rw [hZcard, hΩcard]
          _ = p ^ (2 * k) * Nat.card ↥(Subgroup.center ↥C) * p := by ring
      exact Nat.eq_of_mul_eq_mul_right hp.pos h1
    have hle : Nat.card ↥(Z ⊔ Ω) ≤ Nat.card ↥C :=
      hcardmono (sup_le (Subgroup.map_subtype_le (Subgroup.center ↥C)) hΩleC)
    rw [hsupcard, hCcard] at hle
    have h2 : p ^ (2 * k) ≤ p ^ (2 * m) := Nat.le_of_mul_le_mul_right hle Nat.card_pos
    have h3 := (Nat.pow_le_pow_iff_right hp.one_lt).mp h2
    omega
  have hmk : m ≤ k := by
    have h1 : Nat.card (↥C ⧸ Om) * Nat.card ↥Ω = Nat.card ↥C := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Om]
      congr 1
      rw [hΩeq, Subgroup.card_map_of_injective C.subtype_injective]
    have h2 : Nat.card (↥C ⧸ Om) ≤ Nat.card ↥(Subgroup.center ↥C) := by
      rw [hOmcard]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hφrange)
    have h3 : p ^ (2 * m) * Nat.card ↥(Subgroup.center ↥C)
        = Nat.card (↥C ⧸ Om) * p ^ (2 * k + 1) := by
      rw [← hCcard, ← h1, hΩcard]
      ring
    have h4 : Nat.card (↥C ⧸ Om) * p ^ (2 * k + 1)
        ≤ Nat.card ↥(Subgroup.center ↥C) * p ^ (2 * k + 1) :=
      Nat.mul_le_mul_right _ h2
    have h5 : p ^ (2 * m) * Nat.card ↥(Subgroup.center ↥C)
        ≤ p ^ (2 * k + 1) * Nat.card ↥(Subgroup.center ↥C) := by
      rw [h3]
      exact h4.trans (le_of_eq (Nat.mul_comm _ _))
    have h6 : p ^ (2 * m) ≤ p ^ (2 * k + 1) :=
      Nat.le_of_mul_le_mul_right h5 Nat.card_pos
    have h7 := (Nat.pow_le_pow_iff_right hp.one_lt).mp h6
    omega
  have hmk' : m = k := le_antisymm hmk hkm
  -- `C = Z(C) · Ω₁`.
  have hCeq : C = Z ⊔ Ω := by
    have hcommZΩ : ∀ a ∈ Z, ∀ b ∈ Ω, a * b = b * a := by
      intro a ha b hb
      exact ((mem_center_map_subtype_iff.mp ha).2 b (hΩleC hb)).symm
    have hsup := Work.PGroup.card_sup_mul_card_inf Z Ω hcommZΩ
    have hinfD : Nat.card ↥(Z ⊓ Ω) = p := by rw [hZinfΩ]; exact hDcard
    have hcardZC : Nat.card ↥(Z ⊔ Ω) = Nat.card ↥C := by
      have h1 : Nat.card ↥(Z ⊔ Ω) * p = Nat.card ↥C * p := by
        calc Nat.card ↥(Z ⊔ Ω) * p = Nat.card ↥(Z ⊔ Ω) * Nat.card ↥(Z ⊓ Ω) := by rw [hinfD]
          _ = Nat.card ↥Z * Nat.card ↥Ω := hsup
          _ = Nat.card ↥(Subgroup.center ↥C) * (p ^ (2 * k) * p) := by rw [hZcard, hΩcard]
          _ = p ^ (2 * m) * Nat.card ↥(Subgroup.center ↥C) * p := by rw [hmk']; ring
          _ = Nat.card ↥C * p := by rw [hCcard]
      exact Nat.eq_of_mul_eq_mul_right hp.pos h1
    exact (Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.map_subtype_le (Subgroup.center ↥C)) hΩleC)
      (le_of_eq hcardZC.symm)).symm
  exact ⟨hΩnonab, hΩexp, hΩleC, hcenterΩ, hWeqD, hCeq, hDcard⟩

end Work.PGroup.Symplectic
