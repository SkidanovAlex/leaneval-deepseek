/-
# `Work.PSU3.benderSTProp` — the model facts for the distinguished involution

Peterfalvi II Ch. V §2 Lemma 2 c) and the remark after Lemma 1: in a simple Bender group `Y`
with a split rank-one datum `(B,U,w)` and a *distinguished* involution `s ∈ U`
(`w s w = r⁻¹ w r`, `r ∈ U`), the order of `s * w`, the size and abelianness of `U`, Suzuki's
"equal squares" clause and the `PSU(3,q)` centraliser clause are as in the three families.

The proof is a three-way case split on `IsSimpleBenderGroup Y`:

* transport the datum into the model along the isomorphism `Y ≃* PSL2Model n` / `SzModel n` /
  `PSU3Model n` (`Work.PSU3.BenderST.isSplitRankOne_map`);
* in the model, every split rank-one datum is conjugate to the *standard* datum of the model's
  `BenderPair` (`Work.PSU3.BenderST.datum_conj_standard`, which rests on
  `Work.PSU3.BST.card_twoPoint_of_twoTransitive` — the two-point stabiliser of a datum is a
  complement of the unipotent radical — and on the transitivity of the Borel on the involutions
  outside it, `Work.PSU3.BST.psl2_wTrans` / `sz_wTrans` / `psu3_wTrans`), so it suffices to
  prove the clause for the standard datum (`Work.PSU3.BenderST.StdClause`);
* the standard clause of each model is then assembled from the *existence* part of the structure
  identity for an explicit finite-field matrix
  (`Work.PSU3.BST.psl2_stdSol` / `sz_stdSol` / `psu3_stdSol`: `w * s₀ * w = r₀⁻¹ * w * r₀` with
  `orderOf (s₀ * w) = 3`, `5`, `3`), the *uniqueness* of the distinguished pair, which is
  Peterfalvi II Ch. V §2 Lemma 1 b) (`Work.ThmF.ChV12.structureIdentity`, packaged below as
  `fst_eq_of_structureIdentity`), and the structural computations in the models
  (`Work.PSU3.BenderST.psl2_standard_clause`, `sz_standard_clause`, `psu3_standard_clause`).
-/
import Mathlib
import ChallengeDeps
import Submission.Work.PSU3.BenderST
import Submission.Work.PSU3.BenderST.Defs
import Submission.Work.PSU3.BenderST.transport
import Submission.Work.PSU3.BenderST.transfer
import Submission.Work.PSU3.BenderST.psl2_standard_clause
import Submission.Work.PSU3.BenderST.sz_standard_clause
import Submission.Work.PSU3.BenderST.psu3_standard_clause
import Submission.Work.PSU3.BST.psl2_stdSol
import Submission.Work.PSU3.BST.sz_stdSol
import Submission.Work.PSU3.BST.psu3_stdSol
import Submission.Work.Models.ModelData.psu3ModelData_data
import Submission.Work.Models.ModelData.pSL2ModelData
import Submission.Work.Models.ModelData.szModelData

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint (involutions twoPoint IsAbelianSubgroup IsSplitRankOne)

namespace Work.PSU3

/-! ## The uniqueness step -/

/-- Peterfalvi II Ch. V §2 Lemma 1 b) (`Work.ThmF.ChV12.structureIdentity`), read off the
first component: in a split rank-one datum `(H,Q,t)`, any two solutions `(s,r)`, `(s₀,r₀)` of
the structure identity `t * s * t = r⁻¹ * t * r` (with `s, r ∈ Q`, `orderOf s = 2`) have the
same first component.  Consequently the given distinguished involution `s` coincides with any
explicitly exhibited one. -/
theorem fst_eq_of_structureIdentity {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t)
    (ht : t * t = 1)
    {s r s₀ r₀ : G}
    (hmem : s ∈ Q ∧ orderOf s = 2 ∧ r ∈ Q)
    (hrel : t * s * t = r⁻¹ * t * r)
    (hmem₀ : s₀ ∈ Q ∧ orderOf s₀ = 2 ∧ r₀ ∈ Q)
    (hrel₀ : t * s₀ * t = r₀⁻¹ * t * r₀) :
    s = s₀ := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  obtain ⟨p, _hp, huniq⟩ :=
    Work.ThmF.ChV12.structureIdentity (Work.ThmF.IsSplitRankOne.toData h)
  have h1 : (s, r⁻¹) = p := by
    refine huniq (s, r⁻¹) ⟨hmem.1, hmem.2.1, Subgroup.inv_mem _ hmem.2.2, ?_⟩
    simpa [hti] using hrel
  have h2 : (s₀, r₀⁻¹) = p := by
    refine huniq (s₀, r₀⁻¹) ⟨hmem₀.1, hmem₀.2.1, Subgroup.inv_mem _ hmem₀.2.2, ?_⟩
    simpa [hti] using hrel₀
  exact congrArg Prod.fst (h1.trans h2.symm)

/-! ## The `PSL(2,2ⁿ)` standard clause -/

/-- The standard facts for `PSL(2,2ⁿ)`: `U` is the additive group `(GF(2ⁿ),+)` (abelian) of
order `2ⁿ`, and the Borel has `2ⁿ - 1` involutions, so `|U| = #Inv(B) + 1`. -/
theorem psl2_stdFacts (n : ℕ) (hn : 2 ≤ n) :
    Nat.card ↥((Submission.PSL2.pSL2BenderPair n hn).U)
        = (involutions
            ((Submission.PSL2.pSL2BenderPair n hn).B :
              Set (LeanEval.GroupTheory.Defs.PSL2Model n))).ncard + 1 ∧
    IsAbelianSubgroup ((Submission.PSL2.pSL2BenderPair n hn).U) := by
  refine ⟨?_, ?_⟩
  · have hU : Nat.card ↥(Submission.PSL2.pSL2BenderPair n hn).U = 2 ^ n :=
      Submission.PSL2.card_unipotentPSLHom_range n (by omega)
    have hI : (involutions
        (((Submission.PSL2.pSL2BenderPair n hn).B : Subgroup (PSL2Model n)) :
          Set (PSL2Model n))).ncard = 2 ^ n - 1 :=
      Work.Models.ModelData.psl2NcardInvolutionsStab n hn
    rw [hU, hI]
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  · exact Work.Models.ModelData.psl2UnipotentComm n

/-- The `PSL(2,2ⁿ)` standard clause: the exhibited involution `s₀ = u(1)` of
`Work.PSU3.BST.psl2_stdSol` has `orderOf (s₀ * w) = 3`, and uniqueness of the distinguished
pair identifies the given `s` with `s₀`. -/
theorem psl2_stdClause (n : ℕ) (hn : 2 ≤ n) :
    BenderST.StdClause (Submission.PSL2.pSL2BenderPair n hn) := by
  intro s r hs hs2 hr hsr
  obtain ⟨s₀, r₀, hs₀, hs₀2, hr₀, hs₀r₀, hord₀⟩ := Work.PSU3.BST.psl2_stdSol n hn
  have hstd : IsSplitRankOne (Submission.PSL2.pSL2BenderPair n hn).B
      (Submission.PSL2.pSL2BenderPair n hn).U (Submission.PSL2.pSL2BenderPair n hn).w :=
    BenderST.benderPair_isSplitRankOne _ Submission.PSL2.weylPSL_mul_self
  have hs_eq : s = s₀ :=
    fst_eq_of_structureIdentity hstd Submission.PSL2.weylPSL_mul_self
      ⟨hs, hs2, hr⟩ hsr ⟨hs₀, hs₀2, hr₀⟩ hs₀r₀
  obtain ⟨hcard, hab⟩ := psl2_stdFacts n hn
  exact Or.inl ⟨by rw [hs_eq]; exact hord₀, hab, hcard⟩

/-! ## The `Sz(2^(2n+1))` standard clause -/

/-- The `Sz(2^(2n+1))` standard clause: the exhibited pair `(u(0,1), u(1,0))` of
`Work.PSU3.BST.sz_stdSol` satisfies the structure identity with `orderOf (s₀ * w) = 5`, and
uniqueness of the distinguished pair identifies the given `s` with `s₀`; the non-abelianness,
the order `q²` of the Suzuki `2`-group and Suzuki's equal-squares property are the model
computations of `Work.PSU3.BenderST.sz_standard_clause`. -/
theorem sz_stdClause (n : ℕ) (hn : 1 ≤ n) :
    BenderST.StdClause (Submission.Sz.szBenderPair n hn) := by
  intro s r hs hs2 hr hsr
  obtain ⟨s₀, r₀, hs₀, hs₀2, hr₀, hs₀r₀, hord₀⟩ := Work.PSU3.BST.sz_stdSol n hn
  have hstd : IsSplitRankOne (Submission.Sz.szBenderPair n hn).B
      (Submission.Sz.szBenderPair n hn).U (Submission.Sz.szBenderPair n hn).w :=
    BenderST.benderPair_isSplitRankOne _ (Work.Models.ModelData.szWgM_mul_self n)
  have hs_eq : s = s₀ :=
    fst_eq_of_structureIdentity hstd (Work.Models.ModelData.szWgM_mul_self n)
      ⟨hs, hs2, hr⟩ hsr ⟨hs₀, hs₀2, hr₀⟩ hs₀r₀
  obtain ⟨-, hnab, hcard, hsq⟩ :=
    BenderST.sz_standard_clause n hn hstd s₀ r₀ hs₀ hs₀2 hr₀ hs₀r₀
  exact Or.inr (Or.inl ⟨by rw [hs_eq]; exact hord₀, hnab, hcard, hsq⟩)

/-! ## The `PSU(3,2ⁿ)` standard clause -/

/-- The `PSU(3,2ⁿ)` standard clause: the exhibited involution `s₀ = u(0,1)` of
`Work.PSU3.BST.psu3_stdSol` satisfies `w̄ * s₀ * w̄ = s₀ * w̄ * s₀` with
`orderOf (s₀ * w̄) = 3`, and uniqueness of the distinguished pair identifies the given `s` with
`s₀`; the order `q³` of the unipotent radical and the `PSU(3,q)` centraliser clause are the
model computations of `Work.PSU3.BenderST.psu3_standard_clause`. -/
theorem psu3_stdClause (n : ℕ) (hn : 2 ≤ n) :
    BenderST.StdClause (Submission.PSU3.psu3BenderPair n hn) := by
  intro s r hs hs2 hr hsr
  obtain ⟨s₀, r₀, hs₀, hs₀2, hr₀, hs₀r₀, hord₀⟩ := Work.PSU3.BST.psu3_stdSol n hn
  have hstd : IsSplitRankOne (Submission.PSU3.psu3BenderPair n hn).B
      (Submission.PSU3.psu3BenderPair n hn).U (Submission.PSU3.psu3BenderPair n hn).w :=
    BenderST.benderPair_isSplitRankOne _ (Work.Models.ModelData.psu3Weyl_mul_self n)
  have hs_eq : s = s₀ :=
    fst_eq_of_structureIdentity hstd (Work.Models.ModelData.psu3Weyl_mul_self n)
      ⟨hs, hs2, hr⟩ hsr ⟨hs₀, hs₀2, hr₀⟩ hs₀r₀
  obtain ⟨-, hcard, hx⟩ :=
    BenderST.psu3_standard_clause n hn hstd s₀ r₀ hs₀ hs₀2 hr₀ hs₀r₀
  exact Or.inr (Or.inr ⟨by rw [hs_eq]; exact hord₀, hcard, hx⟩)

/-! ## `BenderSTProp` -/

/-- **Peterfalvi II Ch. V §2 Lemma 2 c)**: in a simple Bender group, a split rank-one datum
`(B,U,w)` and a distinguished involution `s ∈ U` determine the family of the group and the
model invariants `orderOf (s * w)`, `|U|`, the abelianness of `U`, Suzuki's equal-squares
property of `U` and the `PSU(3,q)` centraliser clause. -/
theorem benderSTProp : Work.PSU3.BenderSTProp := by
  intro Y _ _ hY B U w hsplit s r hs hs2 hr hsr
  cases hY with
  | isPSL2 n hn e =>
      refine BenderST.stConcl_iso (B := B) (U := U) (w := w) (s := s) (r := r) e ?_
      exact BenderST.benderSTProp_of_stdClause (Submission.PSL2.pSL2BenderPair n hn)
        (BenderST.benderPair_isSplitRankOne _ Submission.PSL2.weylPSL_mul_self)
        (psl2_stdClause n hn) (BenderST.isSplitRankOne_map e hsplit) (e s) (e r)
        (Subgroup.mem_map_of_mem e.toMonoidHom hs)
        (by simpa using (orderOf_injective e.toMonoidHom e.injective s).trans hs2)
        (Subgroup.mem_map_of_mem e.toMonoidHom hr)
        (by
          have h1 : e (w * s * w) = e (r⁻¹ * w * r) := by rw [hsr]
          simpa only [map_mul, map_inv] using h1)
  | isSuzuki n hn e =>
      refine BenderST.stConcl_iso (B := B) (U := U) (w := w) (s := s) (r := r) e ?_
      exact BenderST.benderSTProp_of_stdClause (Submission.Sz.szBenderPair n hn)
        (BenderST.benderPair_isSplitRankOne _ (Work.Models.ModelData.szWgM_mul_self n))
        (sz_stdClause n hn) (BenderST.isSplitRankOne_map e hsplit) (e s) (e r)
        (Subgroup.mem_map_of_mem e.toMonoidHom hs)
        (by simpa using (orderOf_injective e.toMonoidHom e.injective s).trans hs2)
        (Subgroup.mem_map_of_mem e.toMonoidHom hr)
        (by
          have h1 : e (w * s * w) = e (r⁻¹ * w * r) := by rw [hsr]
          simpa only [map_mul, map_inv] using h1)
  | isPSU3 n hn e =>
      refine BenderST.stConcl_iso (B := B) (U := U) (w := w) (s := s) (r := r) e ?_
      exact BenderST.benderSTProp_of_stdClause (Submission.PSU3.psu3BenderPair n hn)
        (BenderST.benderPair_isSplitRankOne _ (Work.Models.ModelData.psu3Weyl_mul_self n))
        (psu3_stdClause n hn) (BenderST.isSplitRankOne_map e hsplit) (e s) (e r)
        (Subgroup.mem_map_of_mem e.toMonoidHom hs)
        (by simpa using (orderOf_injective e.toMonoidHom e.injective s).trans hs2)
        (Subgroup.mem_map_of_mem e.toMonoidHom hr)
        (by
          have h1 : e (w * s * w) = e (r⁻¹ * w * r) := by rw [hsr]
          simpa only [map_mul, map_inv] using h1)

end Work.PSU3
