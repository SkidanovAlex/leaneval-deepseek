import Mathlib
import Submission.Work.Higman.MSA.l8_local
import Submission.Work.Higman.MSA.l8_BV
import Submission.Work.Higman.MSA.l8_betaV
import Submission.Work.Higman.MSA.l8_sV
import Submission.Work.Higman.MSA.l8_card
import Submission.Work.Higman.h8_squaring_polar
import Submission.Work.Higman.powSub_C_eq_of_cover

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman.MSA

namespace L8

variable {P : Type} [Group P] [Finite P]

/-- **The polar identity of the power map**, on representatives: for `u, v ∈ C`,
`sV (uA · vA) = sV (uA) · sV (vA) · BV (uA) (vA)`.  This is the group-theoretic
identity `(u * v) ^ (2 ^ e) = u ^ (2 ^ e) * v ^ (2 ^ e) * ⁅u⁻¹, v⁆ ^ (2 ^ (e - 1))` of
Higman's Lemma 8 (`h8_squaring_polar`, together with the congruence
`⁅u⁻¹, v⁆ ≡ ⁅v, u⁆` modulo `A ^ (2)` which does not change `2 ^ (e-1)`-st powers). -/
theorem sV_mul_rep {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) (u v : ↥C) :
    sV S (QuotientGroup.mk u * QuotientGroup.mk v)
      = sV S (QuotientGroup.mk u) * sV S (QuotientGroup.mk v)
        * BV S (QuotientGroup.mk u) (QuotientGroup.mk v) := by
  have hXu : ((u : ↥C) : P) ∈ C := u.2
  have hYv : ((v : ↥C) : P) ∈ C := v.2
  have hXYA : ⁅(((u : ↥C) : P))⁻¹, ((v : ↥C) : P)⁆ ∈ A := by
    have hmem : ⁅(((u : ↥C) : P))⁻¹, ((v : ↥C) : P)⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator (C.inv_mem hXu) hYv
    rwa [S.hCd] at hmem
  have hYXA : ⁅((v : ↥C) : P), ((u : ↥C) : P)⁆ ∈ A := by
    have hmem : ⁅((v : ↥C) : P), ((u : ↥C) : P)⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator hYv hXu
    rwa [S.hCd] at hmem
  have hswap : (⁅((v : ↥C) : P), ((u : ↥C) : P)⁆) ^ 2 ^ (S.e - 1)
      = (⁅(((u : ↥C) : P))⁻¹, ((v : ↥C) : P)⁆) ^ 2 ^ (S.e - 1) :=
    (pow_eq_of_mul_inv_mem_powSub_two S hXYA hYXA
      (commutator_inv_eq_mod S hXu hYv)).symm
  rw [← QuotientGroup.mk_mul]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, sV_mk, sV_mk, sV_mk,
    BV_rep S (QuotientGroup.mk u) (QuotientGroup.mk v) u v rfl rfl]
  simp only [Subgroup.coe_mul]
  rw [h8_squaring_polar h S.hA S.hC2 S.hCd S.he1 S.he hXu hYv, hswap]

/-- **The polar identity of the power map.**  For `x, y ∈ C/A`,
`sV (x * y) = sV x * sV y * BV x y` (no cardinality hypothesis is needed). -/
theorem sV_mul {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) (x y : ↥C ⧸ (A.subgroupOf C)) :
    sV S (x * y) = sV S x * sV S y * BV S x y := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective y
  exact sV_mul_rep S u v

end L8

/-- The statement of Higman's Lemma 8 for the power map `sV : C/A → Ω₁(P)`, in the form in
which the Lemma-9 development consumes it: `sV` fixes `1`, is `ξ`-equivariant, has polar form
`BV`, and is onto.  (The injectivity half of `L8.l8_sV` needs the cardinality input `hcard`
and is not needed here; surjectivity, proved in `L8.sV_surjective`, needs none.) -/
theorem l8_sV_aux {P : Type} [Group P] [Finite P]
    {h : Work.Higman.IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : Work.Higman.MSA.L8.D h A C) :
    Work.Higman.MSA.L8.sV S 1 = 1 ∧
    (∀ x : ↥C ⧸ A.subgroupOf C, (Work.Higman.xiZ h) (Work.Higman.MSA.L8.sV S x)
      = Work.Higman.MSA.L8.sV S ((Work.Higman.MSA.L8.xiQuot h S.hA.map_eq S.hCinv) x)) ∧
    (∀ x y : ↥C ⧸ A.subgroupOf C,
      Work.Higman.MSA.L8.sV S (x * y)
        = Work.Higman.MSA.L8.sV S x * Work.Higman.MSA.L8.sV S y * Work.Higman.MSA.L8.BV S x y) ∧
    Function.Surjective (Work.Higman.MSA.L8.sV S) :=
  ⟨L8.sV_one S, L8.sV_xi S, L8.sV_mul S, L8.sV_surjective S⟩

end Work.Higman.MSA
