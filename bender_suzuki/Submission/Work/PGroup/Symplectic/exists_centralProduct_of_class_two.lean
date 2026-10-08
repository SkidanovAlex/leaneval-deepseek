import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.Symplectic.Basic
import Submission.Work.PGroup.Symplectic.top_transfer
import Submission.Work.PGroup.Symplectic.omega_one_structure_of_class_two
import Submission.Work.PGroup.Symplectic.centralProduct_of_structure
import Submission.Work.PGroup.frattini_eq_agemo_sup_commutator
import Submission.Work.PGroup.center_eq_commutator_of_isExtraspecial
import Submission.Work.PGroup.Symplectic.class_two_of_allAbelianCharCyclic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A class-two `p`-group of symplectic type is a central product

Let `X` be a finite nonabelian `p`-group (`p` an odd prime) of nilpotency class at most two
(`⁅X, X⁆ ≤ Z(X)`) in which every `p`-th power is central, and suppose that every abelian
characteristic subgroup of `X` is cyclic.  Then `X` is the internal central product of a cyclic
subgroup `Cc` (namely `Z(X)`) and an extraspecial subgroup `E` of exponent dividing `p`
(namely `Ω₁(X)`), i.e. the "class two" case of Feit–Thompson 3.5 / Gorenstein Theorem 5.4.9.

The proof specializes `Work.PGroup.Symplectic.omega_one_structure_of_class_two` to `C = ⊤`
(the structure theorem for `Ω₁` of a class-two group with cyclic centre): it produces `Ω₁(X)`
with `X = Z(X) · Ω₁(X)`, `Z(Ω₁(X)) = ⁅X, X⁆` of order `p` and `Ω₁(X)` of exponent `p`.  The
only work here is the transport of the hypotheses along the isomorphism `↥⊤ ≃* X`, and the
verification of the two centrality conditions of an internal central product.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical Pointwise commutatorElement
open Subgroup

noncomputable section

namespace Work.PGroup.Symplectic

theorem exists_centralProduct_of_class_two {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2) (hX : IsPGroup p X) (hnab : ¬ IsMulCommutative X)
    (hdc : ∀ A : Subgroup X, A.Characteristic → IsMulCommutative A → ∃ a : X, A = Subgroup.zpowers a)
    (hclass : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ ≤ Subgroup.center X)
    (hquot : ∀ x : X, x ^ p ∈ Subgroup.center X) :
    ∃ Cc E : Subgroup X, Work.PGroup.IsCentralProduct (⊤ : Subgroup X) Cc E ∧
      (∃ a : X, Cc = Subgroup.zpowers a) ∧ Work.PGroup.IsExtraspecial p E ∧
      Monoid.exponent ↥E ∣ p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- ### Step 1: transport of the hypotheses along `↥⊤ ≃* X`.
  have hcenterTop : (Subgroup.center ↥(⊤ : Subgroup X)).map (⊤ : Subgroup X).subtype
      = Subgroup.center X := by
    ext z
    rw [Work.PGroup.Symplectic.mem_center_map_subtype_iff]
    constructor
    · rintro ⟨-, hz⟩
      rw [Subgroup.mem_center_iff]
      intro g
      exact hz g trivial
    · intro hz
      exact ⟨trivial, fun g _ => Subgroup.mem_center_iff.mp hz g⟩
  have hCpg : IsPGroup p ↥(⊤ : Subgroup X) := hX.of_equiv Subgroup.topEquiv.symm
  have hnabTop : ¬ IsMulCommutative ↥(⊤ : Subgroup X) := by
    intro h
    refine hnab (isMulCommutative_iff.mpr fun x y => ?_)
    exact congrArg Subtype.val (isMulCommutative_iff.mp h ⟨x, trivial⟩ ⟨y, trivial⟩)
  have hclassTop : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆
      ≤ (Subgroup.center ↥(⊤ : Subgroup X)).map (⊤ : Subgroup X).subtype := by
    rw [hcenterTop]; exact hclass
  have hquotTop : ∀ x ∈ (⊤ : Subgroup X),
      x ^ p ∈ (Subgroup.center ↥(⊤ : Subgroup X)).map (⊤ : Subgroup X).subtype := by
    intro x _
    rw [hcenterTop]; exact hquot x
  have hcycTop : ∃ a : X, (Subgroup.center ↥(⊤ : Subgroup X)).map (⊤ : Subgroup X).subtype
      = Subgroup.zpowers a := by
    obtain ⟨a, ha⟩ := Work.PGroup.center_eq_zpowers_of_allAbelianCharCyclic hdc
    exact ⟨a, by rw [hcenterTop]; exact ha⟩
  have hdcTop := allAbelianCharCyclic_top hdc
  -- ### Step 2: the structure theorem for `Ω₁`, applied with `C = ⊤`.
  obtain ⟨hΩnab, hΩexp, hΩle, hΩcenter, hΩcenter_eq, htop_eq, hDcard⟩ :=
    omega_one_structure_of_class_two hp hodd (⊤ : Subgroup X) hCpg hclassTop hquotTop hcycTop
      hdcTop hnabTop
  set Ω : Subgroup X := Subgroup.closure {x : X | x ∈ (⊤ : Subgroup X) ∧ x ^ p = 1} with hΩdef
  -- ### Step 3: `Ω` is extraspecial of exponent `p`.
  have hΩpg : IsPGroup p ↥Ω := (hX.of_equiv Subgroup.topEquiv.symm).to_le hΩle
  have hag : Work.PGroup.agemo p 1 Ω = ⊥ := by
    rw [Work.PGroup.agemo]
    refine le_antisymm ?_ bot_le
    rw [Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    change x ^ (p ^ 1) = 1
    have h := hΩexp ⟨x, hx⟩
    simpa using congrArg Subtype.val h
  have hEEleD : ⁅Ω, Ω⁆ ≤ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ :=
    Subgroup.commutator_mono le_top le_top
  have hEEne : (⁅Ω, Ω⁆ : Subgroup X) ≠ ⊥ := by
    intro hbot
    refine hΩnab ?_
    rw [isMulCommutative_iff]
    intro a b
    refine Subtype.ext ?_
    have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot a.2
    exact (Subgroup.mem_centralizer_iff.mp h b.1 b.2).symm
  have hEEcard : Nat.card ↥(⁅Ω, Ω⁆ : Subgroup X) = p := by
    have hdvd : Nat.card ↥(⁅Ω, Ω⁆ : Subgroup X) ∣ p := by
      have h := Subgroup.card_dvd_of_le hEEleD
      rwa [hDcard] at h
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd h (fun hc => hEEne (Subgroup.eq_bot_of_card_eq _ hc))
    · exact h
  have hcenterInΩ : Work.PGroup.centerIn Ω = ⁅Ω, Ω⁆ := by
    rw [show Work.PGroup.centerIn Ω = (Subgroup.center ↥Ω).map Ω.subtype from rfl]
    rw [hΩcenter_eq]
    exact (Subgroup.eq_of_le_of_card_ge hEEleD (by rw [hEEcard, hDcard])).symm
  have hcenterInFr : Work.PGroup.centerIn Ω = Work.PGroup.frattiniIn Ω := by
    rw [hcenterInΩ, Work.PGroup.frattini_eq_agemo_sup_commutator hp Ω hΩpg, hag, bot_sup_eq]
  have hElem : Work.PGroup.IsElementaryAbelian p (Work.PGroup.centerIn Ω) := by
    refine ⟨?_, ?_⟩
    · rw [show Work.PGroup.centerIn Ω = (Subgroup.center ↥Ω).map Ω.subtype from rfl]
      infer_instance
    · intro x
      apply Subtype.ext
      have hx : (x : X) ∈ Ω := Work.PGroup.centerIn_le Ω x.2
      have h := congrArg Subtype.val (hΩexp ⟨(x : X), hx⟩)
      simpa using h
  have hspecial : Work.PGroup.IsSpecial p Ω :=
    Or.inr ⟨hΩpg, hΩnab, hcenterInΩ, hcenterInFr, hElem⟩
  have hcardcenterIn : Nat.card ↥(Work.PGroup.centerIn Ω) = p := by
    rw [show Work.PGroup.centerIn Ω = (Subgroup.center ↥Ω).map Ω.subtype from rfl,
      Subgroup.card_map_of_injective Ω.subtype_injective]
    exact hΩcenter
  have hΩextra : Work.PGroup.IsExtraspecial p Ω := ⟨hΩnab, hspecial, hcardcenterIn⟩
  have hΩexpdvd : Monoid.exponent ↥Ω ∣ p :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hΩexp
  -- ### Step 4: the central product `X = Z(X) · Ω`.
  have hcenterInZ : Work.PGroup.centerIn (Subgroup.center X) = Subgroup.center X := by
    rw [Work.PGroup.centerIn]
    ext z
    rw [Work.PGroup.Symplectic.mem_center_map_subtype_iff]
    constructor
    · rintro ⟨hz, -⟩; exact hz
    · intro hz; exact ⟨hz, fun y hy => (Subgroup.mem_center_iff.mp hy z).symm⟩
  have hcentprod : Work.PGroup.IsCentralProduct (⊤ : Subgroup X) (Subgroup.center X) Ω := by
    refine ⟨le_top, le_top, ?_, ?_, ?_, ?_⟩
    · have h1 : (Subgroup.center ↥(⊤ : Subgroup X)).map (⊤ : Subgroup X).subtype ⊔ Ω
          = Subgroup.center X ⊔ Ω := by rw [hcenterTop]
      exact (htop_eq.trans h1).symm
    · rw [← le_bot_iff, Subgroup.commutator_le]
      intro a ha b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp ha b).symm
    · refine (inf_le_left : Subgroup.center X ⊓ Ω ≤ Subgroup.center X).trans ?_
      rw [hcenterInZ]
    · intro z hz
      obtain ⟨hzZ, hzΩ⟩ := Subgroup.mem_inf.mp hz
      rw [show Work.PGroup.centerIn Ω = (Subgroup.center ↥Ω).map Ω.subtype from rfl,
        Work.PGroup.Symplectic.mem_center_map_subtype_iff]
      exact ⟨hzΩ, fun y _ => Subgroup.mem_center_iff.mp hzZ y⟩
  exact ⟨Subgroup.center X, Ω, hcentprod,
    Work.PGroup.center_eq_zpowers_of_allAbelianCharCyclic hdc, hΩextra, hΩexpdvd⟩

end Work.PGroup.Symplectic
