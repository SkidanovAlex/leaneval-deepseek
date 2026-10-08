import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.commutatorElement_mul_of_abel_normal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman.HS

/-- **The two-cover pairing.**

Let `P` be a Suzuki 2-group, `A ⊴ P` a `ξ`-invariant abelian normal subgroup with `A² = Ω₁(P)`
(where `A ^ (2) = powSub A 2`) and `C_P(A) = A`, and `A ≤ D ≤ P` with `⁅D,D⁆ = A²`.

Then the commutator map `(a, d) ↦ ⁅a,d⁆` (`a ∈ A`, `d ∈ D`) takes values in `Ω₁(P) = A²` and
descends to a biadditive pairing

  `β : A/A² × D/A → Ω₁(P)`,  `β(aA², dA) = ⁅a,d⁆`,

which is non-degenerate in the second variable: if `β x y = 1` for all `x` then `y = 1`.

Well definedness: `⁅A,D⁆ ≤ ⁅D,D⁆ = A²` (using `A ≤ D`) so the values land in `A² = Ω₁(P)`,
which is central; `A²` is annihilated on the left since `A² ≤ Z(P)`, and `A` on the right since
`A` is abelian.  Biadditivity on representatives is `commutatorElement_mul_of_abel_normal`
(first variable) and `commutatorElement_mul_right_eq_mul_conj` together with the centrality of
`A²` (second variable).  Finally `β x y = 1` for all `x` says exactly that the representative of
`y` centralizes `A`, i.e. lies in `C_P(A) = A`. -/
theorem two_cover_pairing {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A D : Subgroup P} [hAn : A.Normal]
    [hN : ((Work.Higman.powSub A 2).subgroupOf A).Normal]
    [hM : (A.subgroupOf D).Normal]
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hAD : A ≤ D) (hDd : Bracket.bracket D D = Work.Higman.powSub A 2)
    (hcent : Subgroup.centralizer (A : Set P) = A) :
    ∃ β : (↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A) →
          (↥D ⧸ (A.subgroupOf D)) → ↥(Work.Higman.omega1 P),
      (∀ (a : ↥A) (d : ↥D),
          ((β (QuotientGroup.mk a) (QuotientGroup.mk d) : ↥(Work.Higman.omega1 P)) : P)
            = @Bracket.bracket P P (commutatorElement (G := P)) (a : P) (d : P)) ∧
      (∀ x y z, β (x * y) z = β x z * β y z) ∧
      (∀ x y z, β x (y * z) = β x y * β x z) ∧
      (∀ y : ↥D ⧸ (A.subgroupOf D), (∀ x, β x y = 1) → y = 1) := by
  classical
  -- `⁅A,D⁆ ≤ ⁅D,D⁆ = A²`
  have hDd' : ⁅D,D⁆ = Work.Higman.powSub A 2 := hDd
  have hmem : ∀ (a : P), a ∈ A → ∀ (d : P), d ∈ D → ⁅a,d⁆ ∈ Work.Higman.powSub A 2 := by
    intro a ha d hd
    have h1 : ⁅a,d⁆ ∈ ⁅A,D⁆ := Subgroup.commutator_mem_commutator ha hd
    have h2 : ⁅A,D⁆ ≤ ⁅D,D⁆ := Subgroup.commutator_mono hAD le_rfl
    exact hDd' ▸ h2 h1
  -- `A² = Ω₁(P)` is central
  have hzpow : ∀ x : P, x ∈ Work.Higman.powSub A 2 → x ∈ Subgroup.center P := by
    intro x hx
    rw [htop] at hx
    exact h.omega1_le_center hx
  have hzcomm : ∀ x : P, x ∈ Work.Higman.powSub A 2 → ∀ g : P, g * x = x * g := by
    intro x hx g
    exact Subgroup.mem_center_iff.mp (hzpow x hx) g
  have hmemO : ∀ (a : P), a ∈ A → ∀ (d : P), d ∈ D → ⁅a,d⁆ ∈ Work.Higman.omega1 P := by
    intro a ha d hd
    rw [← htop]
    exact hmem a ha d hd
  -- ## Well definedness in the second variable (`d ↦ ⁅a,d⁆` is constant on `A`-cosets)
  have wd2 : ∀ (a : ↥A) (d e : ↥D),
      QuotientGroup.leftRel (A.subgroupOf D) d e →
      (⟨⁅(a:P),(d:P)⁆, hmemO _ a.2 _ d.2⟩ : ↥(Work.Higman.omega1 P)) =
      ⟨⁅(a:P),(e:P)⁆, hmemO _ a.2 _ e.2⟩ := by
    intro a d e hde
    have hz : (d:P)⁻¹ * (e:P) ∈ A := Subgroup.mem_subgroupOf.mp
      (QuotientGroup.leftRel_apply.mp hde)
    have hcommz : ⁅(a:P), (d:P)⁻¹ * (e:P)⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hA.abelian _ a.2 _ hz)
    have he : (e:P) = (d:P) * ((d:P)⁻¹ * (e:P)) := by group
    apply Subtype.ext
    change ⁅(a:P),(d:P)⁆ = ⁅(a:P),(e:P)⁆
    rw [he, commutatorElement_mul_right_eq_mul_conj, hcommz]
    group
  -- ## Well definedness in the first variable (`a ↦ ⁅a,d⁆` is constant on `A²`-cosets)
  have wd1 : ∀ (a b : ↥A), QuotientGroup.leftRel ((Work.Higman.powSub A 2).subgroupOf A) a b →
      (fun y : ↥D ⧸ (A.subgroupOf D) => Quotient.liftOn y
        (fun d : ↥D => (⟨⁅(a:P),(d:P)⁆, hmemO _ a.2 _ d.2⟩ : ↥(Work.Higman.omega1 P)))
        (wd2 a)) =
      (fun y : ↥D ⧸ (A.subgroupOf D) => Quotient.liftOn y
        (fun d : ↥D => (⟨⁅(b:P),(d:P)⁆, hmemO _ b.2 _ d.2⟩ : ↥(Work.Higman.omega1 P)))
        (wd2 b)) := by
    intro a b hab
    funext y
    induction y using QuotientGroup.induction_on with
    | _ d =>
      have hz : (a:P)⁻¹ * (b:P) ∈ Work.Higman.powSub A 2 :=
        Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hab)
      have hcommz : ⁅(a:P)⁻¹ * (b:P), (d:P)⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (hzcomm _ hz (d:P)).symm
      have hb : (b:P) = (a:P) * ((a:P)⁻¹ * (b:P)) := by group
      apply Subtype.ext
      change ⁅(a:P),(d:P)⁆ = ⁅(b:P),(d:P)⁆
      rw [hb, commutatorElement_mul_left_eq_conj_mul, hcommz]
      group
  -- ## The pairing
  let β : (↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A) →
      (↥D ⧸ (A.subgroupOf D)) → ↥(Work.Higman.omega1 P) := fun x =>
    Quotient.liftOn x
      (fun a : ↥A => fun y : ↥D ⧸ (A.subgroupOf D) => Quotient.liftOn y
        (fun d : ↥D => (⟨⁅(a:P),(d:P)⁆, hmemO _ a.2 _ d.2⟩ : ↥(Work.Higman.omega1 P)))
        (wd2 a))
      wd1
  have hβdef : ∀ (a : ↥A) (d : ↥D),
      β (QuotientGroup.mk a) (QuotientGroup.mk d) =
      (⟨⁅(a:P),(d:P)⁆, hmemO _ a.2 _ d.2⟩ : ↥(Work.Higman.omega1 P)) := fun a d => rfl
  refine ⟨β, ?_, ?_, ?_, ?_⟩
  · -- values are the commutators
    intro a d
    rw [hβdef]
  · -- additivity in the first variable
    intro x
    induction x using QuotientGroup.induction_on with
    | _ a =>
      intro y
      induction y using QuotientGroup.induction_on with
      | _ b =>
        intro z
        induction z using QuotientGroup.induction_on with
        | _ d =>
          rw [← QuotientGroup.mk_mul, hβdef, hβdef, hβdef]
          apply Subtype.ext
          change ⁅((a : P) * (b : P)), (d:P)⁆ = ⁅(a:P),(d:P)⁆ * ⁅(b:P),(d:P)⁆
          exact Work.Higman.commutatorElement_mul_of_abel_normal hAn hA.abelian a.2 b.2 d.2
  · -- additivity in the second variable
    intro x
    induction x using QuotientGroup.induction_on with
    | _ a =>
      intro y
      induction y using QuotientGroup.induction_on with
      | _ d =>
        intro z
        induction z using QuotientGroup.induction_on with
        | _ e =>
          rw [← QuotientGroup.mk_mul, hβdef, hβdef, hβdef]
          apply Subtype.ext
          change ⁅(a:P), ((d : P) * (e : P))⁆ = ⁅(a:P),(d:P)⁆ * ⁅(a:P),(e:P)⁆
          have hce : ⁅(a:P),(e:P)⁆ ∈ Work.Higman.powSub A 2 := hmem _ a.2 _ e.2
          have hcommz : (d:P) * ⁅(a:P),(e:P)⁆ * (d:P)⁻¹ = ⁅(a:P),(e:P)⁆ := by
            rw [hzcomm _ hce (d:P), mul_assoc, mul_inv_cancel, mul_one]
          rw [commutatorElement_mul_right_eq_mul_conj]
          rw [show ⁅(a:P),(d:P)⁆ * (d:P) * ⁅(a:P),(e:P)⁆ * (d:P)⁻¹
              = ⁅(a:P),(d:P)⁆ * ((d:P) * ⁅(a:P),(e:P)⁆ * (d:P)⁻¹) by group, hcommz]
  · -- non-degeneracy in the second variable
    intro y hy
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective y
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, ← hcent,
        Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := hy (QuotientGroup.mk (⟨u, hu⟩ : ↥A))
    have h2 : ⁅u, (d:P)⁆ = 1 := by
      have h3 := congrArg (fun z : ↥(Work.Higman.omega1 P) => (z : P)) h1
      rw [hβdef] at h3
      simpa using h3
    exact commutatorElement_eq_one_iff_mul_comm.mp h2

end Work.Higman.HS
