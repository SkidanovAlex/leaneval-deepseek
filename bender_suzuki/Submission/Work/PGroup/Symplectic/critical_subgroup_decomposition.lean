import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.exists_isCriticalSubgroup
import Submission.Work.PGroup.Symplectic.Basic
import Submission.Work.PGroup.Symplectic.extraspecial_centralizer
import Submission.Work.PGroup.Symplectic.omega_one_structure_of_class_two
import Submission.Work.PGroup.Symplectic.commutator_top_closure_omega_le
import Submission.Work.PGroup.center_eq_centralizer_of_isCriticalSubgroup
import Submission.Work.PGroup.frattini_eq_agemo_sup_commutator
import Submission.Work.PGroup.pow_mem_frattiniIn

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Gorenstein's Lemma 5.4.7 (the critical-subgroup decomposition)

Let `X` be a finite `p`-group and `C` a critical subgroup of `X` all of whose abelian
characteristic subgroups are cyclic (a "group of symplectic type").  Then `X` is the product
of a subgroup `E` (either trivial or extraspecial) and the centralizer `R = C_X(E)` of `E`,
where `[E,R] = 1`, `E ∩ R = Z(E)`, `Z(C) ≤ R` and `C_R(Z(C)) = Z(C)`.

This is Gorenstein, *Finite Groups*, Lemma 5.4.7, and it is the technical heart of P. Hall's
classification of `p`-groups of symplectic type.  The proof splits into two cases.

* If `C` is commutative, then `C = Z(C)` is cyclic, and `E = ⊥`, `R = ⊤` satisfy everything:
  `C_X(Z(C)) = C_X(C) = Z(C)` by self-centralization of a critical subgroup.

* If `C` is non-commutative, set `E = Ω₁(C) = ⟨c ∈ C : c ^ p = 1⟩`.  The imported lemma
  `omega_one_structure_of_class_two` shows that `E` is extraspecial, that `C = Z(C) · E`
  and that `Z(E) = [C,C]` has order `p`.  Then `[X, E] ≤ Ω₁(Z(C)) ⊆ Z(E)`
  (`commutator_top_closure_omega_le`), so Gorenstein's Lemma 5.4.6
  (`extraspecial_centralizer`) gives `X = E ⊔ C_X(E)`, and `C_R(Z(C)) = Z(C)` follows from
  `C = Z(C) · E`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical Pointwise commutatorElement
open Subgroup

noncomputable section

namespace Work.PGroup.Symplectic

variable {X : Type*} [Group X]

/-- The centre of a commutative subgroup is the subgroup itself. -/
theorem centerIn_eq_self_of_commutative {C : Subgroup X} (h : IsMulCommutative ↥C) :
    Work.PGroup.centerIn C = C := by
  rw [Work.PGroup.centerIn, Subgroup.center_eq_top_iff.mpr h, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

/-- `⁅C, C⁆ ≤ C` for every subgroup `C`. -/
theorem commutator_self_le (C : Subgroup X) : ⁅C, C⁆ ≤ C :=
  Subgroup.commutator_le.mpr (fun a ha b hb => by
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem ha hb) (C.inv_mem ha)) (C.inv_mem hb))

/-- In a group in which `A` and `B` commute elementwise, every element of `A ⊔ B` is a product
`a * b` with `a ∈ A`, `b ∈ B`. -/
theorem exists_mul_eq_of_mem_sup_of_comm {G : Type*} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let S : Subgroup G :=
    { carrier := {x : G | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
      mul_mem' := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        exact ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', by
          calc (a * a') * (b * b') = a * (a' * (b * b')) := by rw [mul_assoc]
            _ = a * ((a' * b) * b') := by rw [mul_assoc]
            _ = a * ((b * a') * b') := by rw [h a' ha' b hb]
            _ = a * (b * (a' * b')) := by rw [mul_assoc]
            _ = (a * b) * (a' * b') := by rw [← mul_assoc]⟩
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro x ⟨a, ha, b, hb, rfl⟩
        exact ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, by
          rw [mul_inv_rev, h a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)]⟩ }
  have hA : A ≤ S := fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩
  have hB : B ≤ S := fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩
  exact (sup_le hA hB) hx

/-- Left multiplication by an element centralizing `C` does not change commutators with
elements of `C`. -/
theorem commutatorElement_mul_left_of_mem_centralizer {C : Subgroup X} {z : X}
    (hz : z ∈ Subgroup.centralizer (C : Set X)) (e b : X) (he : e ∈ C) (hb : b ∈ C) :
    ⁅z * e, b⁆ = ⁅e, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have h1 : ⁅z, b⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp hz b hb).symm
  have h2 : z * ⁅e, b⁆ * z⁻¹ = ⁅e, b⁆ := by
    have h3 : z * ⁅e, b⁆ = ⁅e, b⁆ * z :=
      (Subgroup.mem_centralizer_iff.mp hz ⁅e, b⁆
        (commutator_self_le C (Subgroup.commutator_mem_commutator he hb))).symm
    rw [h3, mul_assoc, mul_inv_cancel, mul_one]
  rw [h1, h2, mul_one]

/-- Right multiplication by an element centralizing `C` does not change commutators with
elements of `C`. -/
theorem commutatorElement_mul_right_of_mem_centralizer {C : Subgroup X} {z : X}
    (hz : z ∈ Subgroup.centralizer (C : Set X)) (a e : X) (ha : a ∈ C) (he : e ∈ C) :
    ⁅a, e * z⁆ = ⁅a, e⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have h1 : ⁅a, z⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp hz a ha
  rw [h1]
  group

/-- If a subgroup is the join of its centre with a subgroup `E`, then `⁅C, C⁆ = ⁅E, E⁆`. -/
theorem commutator_eq_of_eq_centerIn_sup {C E : Subgroup X}
    (h : C = Work.PGroup.centerIn C ⊔ E) : ⁅C, C⁆ = ⁅E, E⁆ := by
  have hZcent : Work.PGroup.centerIn C ≤ Subgroup.centralizer (C : Set X) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hu ⟨c, hc⟩)
  have hE_le_C : E ≤ C := by rw [h]; exact le_sup_right
  have hZcomm : ∀ a ∈ Work.PGroup.centerIn C, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hZcent ha) b (hE_le_C hb)).symm
  have hZcommC : ∀ a ∈ Work.PGroup.centerIn C, ∀ b ∈ C, b * a = a * b := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp (hZcent ha) b hb
  refine le_antisymm ?_ (Subgroup.commutator_mono hE_le_C hE_le_C)
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [h] at ha hb
  obtain ⟨z₁, hz₁, e₁, he₁, rfl⟩ := exists_mul_eq_of_mem_sup_of_comm hZcomm ha
  obtain ⟨z₂, hz₂, e₂, he₂, rfl⟩ := exists_mul_eq_of_mem_sup_of_comm hZcomm hb
  rw [commutatorElement_mul_left_of_mem_centralizer (hZcent hz₁) e₁ (z₂ * e₂) (hE_le_C he₁)
    (C.mul_mem (Work.PGroup.centerIn_le C hz₂) (hE_le_C he₂))]
  rw [← hZcommC z₂ hz₂ e₂ (hE_le_C he₂)]
  rw [commutatorElement_mul_right_of_mem_centralizer (hZcent hz₂) e₁ e₂
    (hE_le_C he₁) (hE_le_C he₂)]
  exact Subgroup.commutator_mem_commutator he₁ he₂

/-- `℧¹(E) = ⊥` when `E` has exponent dividing `p`. -/
theorem agemo_one_eq_bot_of_exp {p : ℕ} {E : Subgroup X} (h : ∀ x : ↥E, x ^ p = 1) :
    Work.PGroup.agemo p 1 E = ⊥ := by
  rw [Work.PGroup.agemo, Subgroup.eq_bot_iff_forall]
  intro y hy
  rw [Subgroup.mem_closure] at hy
  refine hy ⊥ (fun z hz => ?_)
  obtain ⟨x, hx, rfl⟩ := hz
  exact Subgroup.mem_bot.mpr (by
    have hx' := congrArg Subtype.val (h ⟨x, hx⟩)
    simpa using hx')

/-- **Gorenstein's Lemma 5.4.7.**  For a critical subgroup `C` of a finite `p`-group `X`
(`p` odd) all of whose abelian characteristic subgroups are cyclic, the group `X` is the
product of an extraspecial subgroup `E = Ω₁(C)` (or `E = ⊥` in the commutative case) and its
centralizer, with `E ∩ C_X(E) = Z(E)`, `Z(C) ≤ C_X(E)` and `C_{C_X(E)}(Z(C)) = Z(C)`. -/
theorem critical_subgroup_decomposition {p : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) (hX : IsPGroup p X) (C : Subgroup X) [Finite X]
    (hC : Work.PGroup.IsCriticalSubgroup p (⊤ : Subgroup X) C)
    (hdcC : Work.PGroup.AllAbelianCharCyclic ↥C) :
    ∃ E R : Subgroup X,
      E ⊔ R = ⊤ ∧ ⁅E, R⁆ = ⊥ ∧ E ⊓ R = Work.PGroup.centerIn E ∧
      (E = ⊥ ∨ Work.PGroup.IsExtraspecial p E) ∧
      Work.PGroup.centerIn C ≤ R ∧
      R ⊓ Subgroup.centralizer ((Work.PGroup.centerIn C : Subgroup X) : Set X) = Work.PGroup.centerIn C := by
  classical
  by_cases hCab : IsMulCommutative ↥C
  · -- Case A: `C` is commutative, so `C = Z(C)` is cyclic.
    have hZself : Work.PGroup.centerIn C = C := centerIn_eq_self_of_commutative hCab
    have hcentC : Subgroup.centralizer (C : Set X) = C := by
      refine le_antisymm ?_ ?_
      · intro x hx
        exact hC.self_centralizing (Subgroup.mem_inf.mpr ⟨trivial, hx⟩)
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact congrArg Subtype.val (isMulCommutative_iff.mp hCab ⟨y, hy⟩ ⟨x, hx⟩)
    refine ⟨⊥, ⊤, by simp, by simp, ?_, Or.inl rfl, le_top, ?_⟩
    · rw [bot_inf_eq, Work.PGroup.centerIn, Subgroup.center_eq_top_iff.mpr
        (isMulCommutative_iff.mpr (fun a b => Subsingleton.elim _ _)), ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    · rw [top_inf_eq, hZself, hcentC]
  · -- Case B: `C` is non-commutative; then `E = Ω₁(C)` is extraspecial.
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Finite ↥C := Finite.of_injective C.subtype C.subtype_injective
    have hCpg : IsPGroup p ↥C := hX.to_subgroup C
    have hclass : ⁅C, C⁆ ≤ (Subgroup.center ↥C).map C.subtype :=
      le_trans (Subgroup.commutator_mono le_top le_rfl) hC.commutator_le_center
    have hquot : ∀ x ∈ C, x ^ p ∈ (Subgroup.center ↥C).map C.subtype := fun x hx =>
      hC.frattini_le_center (Work.PGroup.pow_mem_frattiniIn hp C hCpg hx)
    have hcyc : ∃ a : X, (Subgroup.center ↥C).map C.subtype = Subgroup.zpowers a := by
      obtain ⟨a, ha⟩ := Work.PGroup.center_eq_zpowers_of_allAbelianCharCyclic hdcC
      exact ⟨(a : X), by rw [ha, MonoidHom.map_zpowers]; rfl⟩
    obtain ⟨hEnab, hEexp, hEle, hEcard, hEder, hCsup, hCdercard⟩ :=
      omega_one_structure_of_class_two hp hodd C hCpg hclass hquot hcyc hdcC hCab
    set E : Subgroup X := Subgroup.closure {x : X | x ∈ C ∧ x ^ p = 1} with hEdef
    have hCsup' : C = Work.PGroup.centerIn C ⊔ E := hCsup
    have hEpg : IsPGroup p ↥E := hX.to_subgroup E
    have hcc : ⁅C, C⁆ = ⁅E, E⁆ := commutator_eq_of_eq_centerIn_sup hCsup'
    have hcenterE : Work.PGroup.centerIn E = ⁅E, E⁆ := by
      rw [Work.PGroup.centerIn, hEder, hcc]
    have hfrE : Work.PGroup.centerIn E = Work.PGroup.frattiniIn E := by
      rw [hcenterE, Work.PGroup.frattini_eq_agemo_sup_commutator hp E hEpg,
        agemo_one_eq_bot_of_exp hEexp, bot_sup_eq]
    have hcea : Work.PGroup.IsElementaryAbelian p (Work.PGroup.centerIn E) := by
      refine ⟨?_, ?_⟩
      · rw [isMulCommutative_iff]
        intro a b
        apply Subtype.ext
        obtain ⟨u, hu, hua⟩ := Subgroup.mem_map.mp a.2
        obtain ⟨v, hv, hvb⟩ := Subgroup.mem_map.mp b.2
        show (a : X) * (b : X) = (b : X) * (a : X)
        rw [← hua, ← hvb]
        exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hu v)).symm
      · intro x
        apply Subtype.ext
        have hxE : (x : X) ∈ E := Work.PGroup.centerIn_le E x.2
        have h := congrArg Subtype.val (hEexp ⟨(x : X), hxE⟩)
        simpa using h
    have hEex : Work.PGroup.IsExtraspecial p E := by
      refine ⟨hEnab, Or.inr ⟨hEpg, hEnab, hcenterE, hfrE, hcea⟩, ?_⟩
      rw [Work.PGroup.centerIn, Subgroup.card_map_of_injective E.subtype_injective]
      exact hEcard
    -- `Z(C)` commutes elementwise with `E`
    have hZcommE : ∀ a ∈ Work.PGroup.centerIn C, ∀ b ∈ E, a * b = b * a := by
      intro a ha b hb
      obtain ⟨u, hu, hua⟩ := Subgroup.mem_map.mp ha
      have h := Subgroup.mem_center_iff.mp hu ⟨b, hEle hb⟩
      have h2 : (b : X) * (u : X) = (u : X) * (b : X) := by
        simpa using congrArg Subtype.val h
      rw [← hua]
      exact h2.symm
    -- `[X, E] ≤ Z(E)`
    have htop : ⁅(⊤ : Subgroup X), E⁆ ≤ Work.PGroup.centerIn E := by
      have h1 := commutator_top_closure_omega_le (p := p) C
        (hC.commutator_le_center : ⁅(⊤ : Subgroup X), C⁆ ≤ (Subgroup.center ↥C).map C.subtype)
      refine h1.trans ?_
      rw [Subgroup.closure_le]
      rintro z ⟨hzZ, hzp⟩
      have hzC : z ∈ C := Work.PGroup.centerIn_le C hzZ
      have hzE : z ∈ E := by
        rw [hEdef]
        exact Subgroup.subset_closure ⟨hzC, hzp⟩
      refine Subgroup.mem_map.mpr ⟨⟨z, hzE⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro e
      apply Subtype.ext
      exact (hZcommE z hzZ (e : X) e.2).symm
    refine ⟨E, Subgroup.centralizer (E : Set X), ?_, ?_, ?_, Or.inr hEex, ?_, ?_⟩
    · exact extraspecial_centralizer hp E hEex htop
    · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact (Subgroup.mem_centralizer_iff.mp hr e he).symm
    · rw [Work.PGroup.centerIn_eq_inf_centralizer]
    · -- `Z(C) ≤ C_X(E)`
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact (hZcommE z hz e he).symm
    · -- `C_X(E) ⊓ C_X(Z(C)) = Z(C)`
      refine le_antisymm ?_ ?_
      · intro r hr
        rw [Subgroup.mem_inf] at hr
        obtain ⟨hrR, hrZ⟩ := hr
        rw [Subgroup.mem_centralizer_iff] at hrR hrZ
        have hrc : r ∈ Subgroup.centralizer (C : Set X) := by
          rw [Subgroup.mem_centralizer_iff]
          intro c hc
          have hc' : c ∈ Work.PGroup.centerIn C ⊔ E := by rw [← hCsup']; exact hc
          obtain ⟨z₁, hz₁, e₁, he₁, rfl⟩ :=
            exists_mul_eq_of_mem_sup_of_comm hZcommE hc'
          calc (z₁ * e₁) * r = z₁ * (e₁ * r) := by rw [mul_assoc]
            _ = z₁ * (r * e₁) := by rw [hrR e₁ he₁]
            _ = (z₁ * r) * e₁ := by rw [mul_assoc]
            _ = (r * z₁) * e₁ := by rw [hrZ z₁ hz₁]
            _ = r * (z₁ * e₁) := by rw [mul_assoc]
        rw [Work.PGroup.centerIn_eq_inf_centralizer C, Subgroup.mem_inf]
        exact ⟨hC.self_centralizing (Subgroup.mem_inf.mpr ⟨trivial, hrc⟩), hrc⟩
      · intro r hr
        rw [Subgroup.mem_inf]
        obtain ⟨u, hu, hua⟩ := Subgroup.mem_map.mp hr
        refine ⟨?_, ?_⟩
        · -- `r ∈ C_X(E)`
          rw [Subgroup.mem_centralizer_iff]
          intro e he
          have h := Subgroup.mem_center_iff.mp hu ⟨e, hEle he⟩
          have h2 : (e : X) * (u : X) = (u : X) * (e : X) := by
            simpa using congrArg Subtype.val h
          rw [← hua]
          exact h2
        · -- `r ∈ C_X(Z(C))`
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          obtain ⟨v, hv, hvy⟩ := Subgroup.mem_map.mp hy
          have h := Subgroup.mem_center_iff.mp hv ⟨r, Work.PGroup.centerIn_le C hr⟩
          have h2 : (r : X) * (v : X) = (v : X) * (r : X) := by
            simpa using congrArg Subtype.val h
          rw [← hvy]
          exact h2.symm

end Work.PGroup.Symplectic
