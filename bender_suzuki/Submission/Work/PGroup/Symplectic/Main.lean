import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.Symplectic.Basic
import Submission.Work.PGroup.exists_isCriticalSubgroup
import Submission.Work.PGroup.Symplectic.critical_subgroup_decomposition
import Submission.Work.PGroup.Symplectic.extraspecial_centralizer
import Submission.Work.PGroup.Symplectic.conclusion_map_subtype
import Submission.Work.PGroup.Symplectic.false_of_cyclic_char_selfcentralizing
import Submission.Work.PGroup.Symplectic.top_transfer
import Submission.Work.PGroup.Symplectic.exists_centralProduct_of_class_two
import Submission.Work.PGroup.center_eq_commutator_of_isExtraspecial
import Submission.Work.PGroup.Symplectic.class_two_of_allAbelianCharCyclic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# P. Hall's theorem on `p`-groups of symplectic type (intrinsic form)

A finite nonabelian `p`-group (`p` odd) all of whose abelian characteristic subgroups are
cyclic is the central product of a cyclic group and an extraspecial group of exponent dividing
`p` (Feit–Thompson 3.5, Gorenstein Theorem 5.4.9, for odd `p`).

The proof is by strong induction on `|X|` and rests on three structural facts:

* `commutator_le_center_of_allAbelianCharCyclic`: `X` has nilpotency class at most two;
* a critical subgroup `C` of `X` (Thompson) together with Gorenstein's Lemma 5.4.7 gives a
  decomposition `X = E ⊔ C_X(E)` with `E = Ω₁(C)` extraspecial of exponent `p`, from which it
  follows that every `p`-th power in `X` is central — this is where the induction hypothesis is
  used, applied to the characteristic subgroup `C_X(E)` when the latter is non-commutative;
* `exists_centralProduct_of_class_two`: a class-two `p`-group of symplectic type in which `p`-th
  powers are central is the central product of `Z(X)` (cyclic) and `Ω₁(X)` (extraspecial).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical Pointwise commutatorElement
open Subgroup

noncomputable section

namespace Work.PGroup.Symplectic

variable {X : Type*} [Group X]

/-- The statement of P. Hall's theorem for a group of cardinality `n`. -/
theorem symplectic_main_aux (n : ℕ) :
    ∀ (X : Type*) [Group X] [Finite X] (p : ℕ), Nat.card X = n → p.Prime → p ≠ 2 →
      IsPGroup p X → ¬ IsMulCommutative X → Work.PGroup.AllAbelianCharCyclic X →
      ∃ Cc E : Subgroup X, Work.PGroup.IsCentralProduct (⊤ : Subgroup X) Cc E ∧
        (∃ a : X, Cc = Subgroup.zpowers a) ∧ Work.PGroup.IsExtraspecial p E ∧
        Monoid.exponent ↥E ∣ p := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X _ _ p hcard hp hodd hX hnab hdc
    classical
    haveI : Fact p.Prime := ⟨hp⟩
    have hnt : Nontrivial X := by
      by_contra h
      haveI : Subsingleton X := not_nontrivial_iff_subsingleton.mp h
      exact hnab (IsMulCommutative.of_comm fun a b => Subsingleton.elim _ _)
    haveI : Nontrivial X := hnt
    -- Step 1: `X` has nilpotency class at most two.
    have hclass2 : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ ≤ Subgroup.center X :=
      commutator_le_center_of_allAbelianCharCyclic hp hodd hX hnab hdc
    -- Step 2: every `p`-th power is central.
    have hquot : ∀ x : X, x ^ p ∈ Subgroup.center X := by
      obtain ⟨C, hCchar, hCne, hfr, hcomm, hsc⟩ :=
        Work.PGroup.exists_characteristic_critical_intrinsic (H := X) hp hX
      have hcrit : Work.PGroup.IsCriticalSubgroup p (⊤ : Subgroup X) C :=
        { le_self := le_top
          ne_bot := hCne
          characteristic := by
            intro g hg
            rw [Work.PGroup.conjBy_eq_map]
            exact Subgroup.characteristic_iff_map_eq.mp hCchar (MulAut.conj g)
          frattini_le_center := hfr
          commutator_le_center := hcomm
          self_centralizing := inf_le_right.trans hsc }
      have hdcC : Work.PGroup.AllAbelianCharCyclic ↥C := of_characteristic hCchar hdc
      by_cases hCab : IsMulCommutative ↥C
      · -- Case A: `C` is commutative, hence cyclic and self-centralizing: impossible.
        exfalso
        have hZself : Work.PGroup.centerIn C = C := centerIn_eq_self_of_commutative hCab
        have hcentC : Subgroup.centralizer (C : Set X) = C := by
          refine le_antisymm ?_ ?_
          · intro x hx
            exact hsc hx
          · intro x hx
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            exact congrArg Subtype.val (isMulCommutative_iff.mp hCab ⟨y, hy⟩ ⟨x, hx⟩)
        obtain ⟨a, ha⟩ := Work.PGroup.center_eq_zpowers_of_allAbelianCharCyclic hdcC
        have h1 : Work.PGroup.centerIn C = Subgroup.zpowers (a : X) := by
          rw [Work.PGroup.centerIn, ha]
          exact ConclusionMapSubtype.map_zpowers a
        have hCeq : C = Subgroup.zpowers (a : X) := hZself.symm.trans h1
        haveI : Finite ↥C := Finite.of_injective C.subtype C.subtype_injective
        have hCpg : IsPGroup p ↥C := hX.to_subgroup C
        obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hCpg a
        have hord : orderOf (a : X) = p ^ m := by rw [Subgroup.orderOf_coe]; exact hm
        have hm1 : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with h0 | hpos
          · exfalso
            rw [h0, pow_zero] at hm
            have ha1 : a = 1 := orderOf_eq_one_iff.mp hm
            exact hCne (by rw [hCeq, ha1]; exact Subgroup.zpowers_one_eq_bot)
          · exact hpos
        have hchar : (Subgroup.zpowers (a : X)).Characteristic := hCeq ▸ hCchar
        have hcent : Subgroup.centralizer ((Subgroup.zpowers (a : X) : Subgroup X) : Set X) =
            Subgroup.zpowers (a : X) := by
          rw [← hCeq]; exact hcentC
        exact false_of_cyclic_char_selfcentralizing hp hodd hX hm1 hnab hdc hord hchar hcent
      · -- Case B: `C` is non-commutative; `E = Ω₁(C)` is extraspecial and `X = E ⊔ C_X(E)`.
        haveI : Finite ↥C := Finite.of_injective C.subtype C.subtype_injective
        have hCpg : IsPGroup p ↥C := hX.to_subgroup C
        have hclassC : ⁅C, C⁆ ≤ (Subgroup.center ↥C).map C.subtype :=
          le_trans (Subgroup.commutator_mono le_top le_rfl) hcomm
        have hquotC : ∀ x ∈ C, x ^ p ∈ (Subgroup.center ↥C).map C.subtype := fun x hx =>
          hfr (Work.PGroup.pow_mem_frattiniIn hp C hCpg hx)
        have hcycC : ∃ a : X, (Subgroup.center ↥C).map C.subtype = Subgroup.zpowers a := by
          obtain ⟨a, ha⟩ := Work.PGroup.center_eq_zpowers_of_allAbelianCharCyclic hdcC
          exact ⟨(a : X), by rw [ha, MonoidHom.map_zpowers]; rfl⟩
        obtain ⟨hEnab, hEexp, hEle, hEcard, hEder, hCsup, hCdercard⟩ :=
          omega_one_structure_of_class_two hp hodd C hCpg hclassC hquotC hcycC hdcC hCab
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
        -- `E = Ω₁(C)` is characteristic in `X`
        have hEchar : E.Characteristic := by
          rw [hEdef]
          have hΩeq : Subgroup.closure {x : X | x ∈ C ∧ x ^ p = 1}
              = (Work.PGroup.omega1 (↥C) p ⊤).map C.subtype := by
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
          rw [hΩeq]
          exact map_subtype_characteristic hCchar
            (Work.PGroup.omega1_characteristic p Subgroup.topCharacteristic)
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
          have h1 := commutator_top_closure_omega_le (p := p) C hcomm
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
        set R : Subgroup X := Subgroup.centralizer (E : Set X) with hRdef
        have hsup : E ⊔ R = ⊤ := extraspecial_centralizer hp E hEex htop
        have hRchar : R.Characteristic := by
          haveI : E.Characteristic := hEchar
          exact Subgroup.characteristic_centralizer
        have hEinR : E ⊓ R = Work.PGroup.centerIn E := by
          rw [hRdef, Work.PGroup.centerIn_eq_inf_centralizer]
        have hERcomm : ∀ a ∈ E, ∀ b ∈ R, a * b = b * a := by
          intro a ha b hb
          exact Subgroup.mem_centralizer_iff.mp hb a ha
        -- `p`-th powers of elements of `E` are central
        have hEpow : ∀ e ∈ E, e ^ p ∈ Subgroup.center X := by
          intro e he
          have h1 : e ^ p ∈ Work.PGroup.centerIn E :=
            pow_mem_centerIn_of_isExtraspecial hp hEex e he
          rw [Work.PGroup.center_eq_commutator_of_isExtraspecial E hEex] at h1
          exact hclass2 (Subgroup.commutator_mono le_top le_top h1)
        have hZleR : Subgroup.center X ≤ R := by
          intro z hz
          rw [Subgroup.mem_centralizer_iff]
          intro e _
          exact Subgroup.mem_center_iff.mp hz e
        -- `p`-th powers of elements of `R` are central
        have hRpow : ∀ r ∈ R, r ^ p ∈ Subgroup.center X := by
          intro r hr
          by_cases hRab : IsMulCommutative ↥R
          · -- `R` is commutative, hence `R = Z(X)` by maximality.
            have hRleZ : R ≤ Subgroup.center X := by
              have hcommR : ∀ u v : ↥R, u * v = v * u := isMulCommutative_iff.mp hRab
              intro r0 hr0
              rw [Subgroup.mem_center_iff]
              intro x
              obtain ⟨e, he, r', hr', rfl⟩ :=
                exists_mul_eq_of_mem_sup_of_comm hERcomm (hsup ▸ Subgroup.mem_top x)
              have hrr : r' * r0 = r0 * r' := by
                simpa using congrArg Subtype.val (hcommR ⟨r', hr'⟩ ⟨r0, hr0⟩)
              have hrr' : r0 * r' = r' * r0 := hrr.symm
              calc (e * r') * r0 = e * (r' * r0) := mul_assoc e r' r0
                _ = e * (r0 * r') := by rw [hrr]
                _ = (e * r0) * r' := (mul_assoc e r0 r').symm
                _ = (r0 * e) * r' := by rw [hERcomm e he r0 hr0]
                _ = r0 * (e * r') := mul_assoc r0 e r'
            have hRZ : R = Subgroup.center X := le_antisymm hRleZ hZleR
            rw [← hRZ]
            exact R.pow_mem hr p
          · -- `R` is non-commutative: apply the induction hypothesis to `↥R`.
            have hRne : R ≠ ⊤ := by
              intro htopR
              have hEsub : E ≤ R := htopR ▸ le_top
              have habE : IsMulCommutative ↥E := by
                rw [isMulCommutative_iff]
                intro u v
                apply Subtype.ext
                show (u : X) * (v : X) = (v : X) * (u : X)
                have hu : (u : X) ∈ Work.PGroup.centerIn E :=
                  hEinR ▸ Subgroup.mem_inf.mpr ⟨u.2, hEsub u.2⟩
                obtain ⟨z, hz, hzu⟩ := Subgroup.mem_map.mp hu
                have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz v)
                rw [← hzu]
                simpa using h.symm
              exact hEnab habE
            have hRlt : Nat.card ↥R < Nat.card X := by
              have h1 : R < ⊤ := lt_of_le_of_ne le_top hRne
              have h2 := Subgroup.card_lt_of_lt (G := X) h1
              rwa [Nat.card_congr (Subgroup.topEquiv (G := X)).toEquiv] at h2
            have hdcR : Work.PGroup.AllAbelianCharCyclic ↥R := of_characteristic hRchar hdc
            obtain ⟨Cc₁, E₁, hcp₁, ⟨a₁, ha₁⟩, hE₁ex, hE₁exp⟩ :=
              ih (Nat.card ↥R) (by rw [← hcard]; exact hRlt) ↥R p rfl hp hodd
                (hX.to_subgroup R) hRab hdcR
            -- `Cc₁` is commutative (it is cyclic)
            have hCc₁comm : ∀ u ∈ Cc₁, ∀ v ∈ Cc₁, u * v = v * u := by
              intro u hu v hv
              obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (ha₁ ▸ hu)
              obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (ha₁ ▸ hv)
              rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm i j]
            have hE₁exp' : ∀ e : ↥E₁, e ^ p = 1 :=
              Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE₁exp
            -- `Cc₁` commutes elementwise with `E₁` inside `R`
            have hcommCE : ∀ a ∈ Cc₁, ∀ b ∈ E₁, a * b = b * a := by
              intro a ha b hb
              have h : a ∈ Subgroup.centralizer (E₁ : Set ↥R) :=
                Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcp₁.comm ha
              exact (Subgroup.mem_centralizer_iff.mp h b hb).symm
            -- `Cc₁ ≤ Z(R)`
            have hCc₁ZR : Cc₁ ≤ Subgroup.center ↥R := by
              intro c hc
              rw [Subgroup.mem_center_iff]
              intro r0
              obtain ⟨c₂, hc₂, e₂, he₂, hce₂⟩ := exists_mul_eq_of_mem_sup_of_comm hcommCE
                (hcp₁.eq_sup ▸ Subgroup.mem_top r0)
              rw [← hce₂]
              calc (c₂ * e₂) * c = c₂ * (e₂ * c) := mul_assoc c₂ e₂ c
                _ = c₂ * (c * e₂) := by rw [← hcommCE c hc e₂ he₂]
                _ = (c₂ * c) * e₂ := (mul_assoc c₂ c e₂).symm
                _ = (c * c₂) * e₂ := by rw [← hCc₁comm c hc c₂ hc₂]
                _ = c * (c₂ * e₂) := mul_assoc c c₂ e₂
            -- hence `Cc₁` is central in `X`
            have hCc₁Z : Cc₁.map R.subtype ≤ Subgroup.center X := by
              rintro z ⟨c, hc, rfl⟩
              rw [Subgroup.mem_center_iff]
              intro x
              obtain ⟨e, he, r', hr', rfl⟩ :=
                exists_mul_eq_of_mem_sup_of_comm hERcomm (hsup ▸ Subgroup.mem_top x)
              have hce : e * (c : X) = (c : X) * e := hERcomm e he (c : X) c.2
              have hcr : (c : X) * r' = r' * (c : X) := by
                have h := Subgroup.mem_center_iff.mp (hCc₁ZR hc) (⟨r', hr'⟩ : ↥R)
                simpa using (congrArg Subtype.val h).symm
              calc (e * r') * (c : X) = e * (r' * (c : X)) := mul_assoc e r' (c : X)
                _ = e * ((c : X) * r') := by rw [← hcr]
                _ = (e * (c : X)) * r' := (mul_assoc e (c : X) r').symm
                _ = ((c : X) * e) * r' := by rw [hce]
                _ = (c : X) * (e * r') := mul_assoc (c : X) e r'
            -- finally `r ^ p` lies in `Cc₁ ≤ Z(X)`
            obtain ⟨c, hc, e, he, hce⟩ := exists_mul_eq_of_mem_sup_of_comm hcommCE
              (hcp₁.eq_sup ▸ Subgroup.mem_top (⟨r, hr⟩ : ↥R))
            have hrepR : (⟨r, hr⟩ : ↥R) ^ p ∈ Cc₁ := by
              have hep : e ^ p = 1 := by simpa using hE₁exp' (⟨e, he⟩ : ↥E₁)
              rw [← hce, Commute.mul_pow (hcommCE c hc e he), hep, mul_one]
              exact Cc₁.pow_mem hc p
            refine hCc₁Z (Subgroup.mem_map.mpr ⟨(⟨r, hr⟩ : ↥R) ^ p, hrepR, ?_⟩)
            simp
        -- every element of `X = E ⊔ R` has central `p`-th power
        intro x
        obtain ⟨e, he, r, hr, rfl⟩ :=
          exists_mul_eq_of_mem_sup_of_comm hERcomm (hsup ▸ Subgroup.mem_top x)
        rw [Commute.mul_pow (hERcomm e he r hr)]
        exact (Subgroup.center X).mul_mem (hEpow e he) (hRpow r hr)
    -- Step 3: class two + central `p`-th powers suffice.
    exact exists_centralProduct_of_class_two hp hodd hX hnab hdc hclass2 hquot

/-- **The intrinsic form of FT 3.5 for odd `p`.** -/
theorem symplectic_main {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hX : IsPGroup p X) (hnab : ¬ IsMulCommutative X) (hdc : Work.PGroup.AllAbelianCharCyclic X) :
    ∃ Cc E : Subgroup X, Work.PGroup.IsCentralProduct (⊤ : Subgroup X) Cc E ∧
      (∃ a : X, Cc = Subgroup.zpowers a) ∧ Work.PGroup.IsExtraspecial p E ∧
      Monoid.exponent ↥E ∣ p :=
  symplectic_main_aux (Nat.card X) X p rfl hp hodd hX hnab hdc

end Work.PGroup.Symplectic
