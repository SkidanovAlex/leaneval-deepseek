/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The refined `p`-central filtration: normality and the graded pieces as `𝔽_p[G]`-modules

Schmidt–Wingberg's graded pieces `E(d,τ) = F(d)_{(i,j)}/F(d)_{(i,j)+1}` of the refined
`p`-central filtration are elementary abelian `p`-groups on which `G` acts by `𝔽_p`-linear maps,
hence `𝔽_p[G]`-modules.  This file establishes

* every term `P_{(i,j)}` of the refinement is normal and characteristic (hence invariant under
  every automorphism of `P`, in particular under the action of `G`);
* `⁅P_{(i,j)}, P_{(i,j)}⁆ ≤ P_{(i,j)+1}` and `x ^ p ∈ P_{(i,j)+1}` for `x ∈ P_{(i,j)}`
  (Lemma 4 of the paper, in the form actually needed);
* the induced `𝔽_p[G]`-module structure on `Additive (refinedQuotient p P i j)`, i.e. on
  `E p G d i j`.

The two commutator/power statements are proved from the two abstract group-theoretic lemmas
`Work.CohomologicalShrinking.group.commutator_sup_le_of_le` and
`Work.CohomologicalShrinking.group.pow_sup_le_of_le`; the key point is that `P_{(i,j)+1}`
always contains `P_{i+1}`, which contains all commutators and `p`-th powers of `P_{(i,j)}`.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Defs
import Submission.Work.CohomologicalShrinking.group.commutator_sup_le_of_le
import Submission.Work.CohomologicalShrinking.group.pow_sup_le_of_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking

set_option maxHeartbeats 800000

universe u v

variable {p : ℕ}

/-! ## Normality and characteristic-ness -/

section Normal

variable {P : Type*} [Group P]

/-- The descending central series of `P` consists of characteristic subgroups. -/
theorem lowerCentralSeries_characteristic (P : Type*) [Group P] (j : ℕ) :
    ((⊤ : Subgroup P).lowerCentralSeries j).Characteristic := by
  induction j with
  | zero => rw [Subgroup.lowerCentralSeries_zero]; infer_instance
  | succ n ih =>
      haveI := ih
      rw [Subgroup.lowerCentralSeries_succ]
      infer_instance

/-- The paper's `P^j` is a characteristic subgroup. -/
theorem centralSeries_characteristic (P : Type*) [Group P] (j : ℕ) :
    (centralSeries P j).Characteristic :=
  lowerCentralSeries_characteristic P (j - 1)

/-- The paper's `P^j` is a normal subgroup. -/
theorem centralSeries_normal (P : Type*) [Group P] (j : ℕ) : (centralSeries P j).Normal := by
  haveI := centralSeries_characteristic P j
  infer_instance

/-- Every term `P_{(i,j)}` of the refinement is characteristic. -/
theorem refinedTerm_characteristic (p : ℕ) (P : Type*) [Group P] (i j : ℕ) :
    (refinedTerm p P i j).Characteristic := by
  haveI := centralSeries_characteristic P j
  haveI := Work.Shrinking.pCentralSeries_characteristic p P (i - 1)
  haveI := Work.Shrinking.pCentralSeries_characteristic p P i
  rw [refinedTerm]
  infer_instance

/-- Every term `P_{(i,j)}` of the refinement is normal. -/
theorem refinedTerm_normal (p : ℕ) (P : Type*) [Group P] (i j : ℕ) :
    (refinedTerm p P i j).Normal := by
  haveI := refinedTerm_characteristic p P i j
  infer_instance

instance instNormalCentralSeries (P : Type*) [Group P] (j : ℕ) : (centralSeries P j).Normal :=
  centralSeries_normal P j

instance instCharacteristicCentralSeries (P : Type*) [Group P] (j : ℕ) :
    (centralSeries P j).Characteristic :=
  centralSeries_characteristic P j

instance instNormalRefinedTerm (p : ℕ) (P : Type*) [Group P] (i j : ℕ) :
    (refinedTerm p P i j).Normal :=
  refinedTerm_normal p P i j

instance instCharacteristicRefinedTerm (p : ℕ) (P : Type*) [Group P] (i j : ℕ) :
    (refinedTerm p P i j).Characteristic :=
  refinedTerm_characteristic p P i j

/-- Every term of the refinement is invariant under every automorphism of `P`. -/
theorem map_refinedTerm_eq (p : ℕ) (φ : P ≃* P) (i j : ℕ) :
    (refinedTerm p P i j).map φ.toMonoidHom = refinedTerm p P i j :=
  Subgroup.characteristic_iff_map_eq.mp (refinedTerm_characteristic p P i j) φ

end Normal

/-! ## The graded pieces are elementary abelian `p`-groups -/

section Elementary

variable {P : Type*} [Group P]

/-- The paper's `[P_i, P] ≤ P_{i+1}` in the `pSeries` indexing. -/
theorem commutator_pSeries_le (p : ℕ) (P : Type*) [Group P] (i : ℕ) :
    ⁅pSeries p P i, (⊤ : Subgroup P)⁆ ≤ pSeries p P (i + 1) := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    exact le_top
  · rw [← Nat.sub_add_cancel h]
    exact (Work.Shrinking.commutator_le_pCentralSeries_succ p P (i - 1)).1

/-- The paper's `[P_i, P_i] ≤ P_{i+1}` in the `pSeries` indexing. -/
theorem commutator_pSeries_le_self (p : ℕ) (P : Type*) [Group P] (i : ℕ) :
    ⁅pSeries p P i, pSeries p P i⁆ ≤ pSeries p P (i + 1) := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    exact le_top
  · rw [← Nat.sub_add_cancel h]
    exact (Work.Shrinking.commutator_le_pCentralSeries_succ p P (i - 1)).2

/-- The paper's `P_i^p ≤ P_{i+1}` in the `pSeries` indexing. -/
theorem pow_mem_pSeries_succ (p : ℕ) (P : Type*) [Group P] (i : ℕ) {x : P}
    (hx : x ∈ pSeries p P i) : x ^ p ∈ pSeries p P (i + 1) := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    exact Subgroup.mem_top _
  · rw [← Nat.sub_add_cancel h]
    exact Work.Shrinking.pow_mem_pCentralSeries_succ p P hx

/-- The target `P_{(i,j)+1}` of the graded piece always contains `P_{i+1}`. -/
theorem pSeries_succ_le_refinedTerm_succ (p : ℕ) (i j : ℕ) :
    pSeries p P (i + 1) ≤ refinedTerm p P (tauSucc i j).1 (tauSucc i j).2 := by
  rcases lt_or_ge j i with h | h
  · rw [tauSucc_of_lt h, refinedTerm]
    exact le_sup_right
  · rw [tauSucc_of_le h, refinedTerm_one]

/-- The commutator of a refined term lies in `P_{i+1}`, hence in `P_{(i,j)+1}`. -/
theorem commutator_refinedTerm_le_pSeries (p : ℕ) (i j : ℕ) :
    ⁅refinedTerm p P i j, refinedTerm p P i j⁆ ≤ pSeries p P (i + 1) :=
  group.commutator_sup_le_of_le
    (A := pSeries p P i ⊓ centralSeries P j) (B := pSeries p P (i + 1))
    (le_trans (Subgroup.commutator_mono inf_le_left inf_le_left)
      (commutator_pSeries_le_self p P i))
    (le_trans (Subgroup.commutator_mono inf_le_left le_top)
      (commutator_pSeries_le p P i))
    (le_trans (Subgroup.commutator_mono le_rfl le_top)
      (le_trans (commutator_pSeries_le p P (i + 1))
        (pSeries_antitone p P (Nat.le_succ (i + 1)))))

/-- **Lemma 4 of Schmidt–Wingberg, commutator form**: the graded pieces of the refinement are
abelian, i.e. `⁅P_{(i,j)}, P_{(i,j)}⁆ ≤ P_{(i,j)+1}`. -/
theorem commutator_refinedTerm_le (p : ℕ) (i j : ℕ) :
    ⁅refinedTerm p P i j, refinedTerm p P i j⁆ ≤
      refinedTerm p P (tauSucc i j).1 (tauSucc i j).2 :=
  le_trans (commutator_refinedTerm_le_pSeries p i j)
    (pSeries_succ_le_refinedTerm_succ (p := p) (P := P) i j)

/-- **Lemma 4 of Schmidt–Wingberg, power form**: `P_{(i,j)}^p ≤ P_{(i,j)+1}`, i.e. the graded
pieces of the refinement have exponent dividing `p`. -/
theorem pow_refinedTerm_le (p : ℕ) (i j : ℕ) {x : P} (hx : x ∈ refinedTerm p P i j) :
    x ^ p ∈ refinedTerm p P (tauSucc i j).1 (tauSucc i j).2 := by
  have hK := pSeries_succ_le_refinedTerm_succ (p := p) (P := P) i j
  have hmain : ∀ x ∈ refinedTerm p P i j, x ^ p ∈ pSeries p P (i + 1) :=
    group.pow_sup_le_of_le
      (A := pSeries p P i ⊓ centralSeries P j) (B := pSeries p P (i + 1))
      (fun _ ha => pow_mem_pSeries_succ p P i ha.1)
      (fun _ hb => pSeries_antitone p P (Nat.le_succ (i + 1))
        (pow_mem_pSeries_succ p P (i + 1) hb))
      (commutator_refinedTerm_le_pSeries p i j)
  exact hK (hmain x hx)

/-- The graded pieces of the refinement are commutative. -/
theorem isMulCommutative_refinedQuotient (p : ℕ) (i j : ℕ) :
    IsMulCommutative (refinedQuotient p P i j) :=
  Work.Shrinking.isMulCommutative_subquotient (commutator_refinedTerm_le p i j)

/-- Every element of a graded piece of the refinement has order dividing `p`. -/
theorem pow_eq_one_refinedQuotient (p : ℕ) (i j : ℕ) (x : refinedQuotient p P i j) :
    x ^ p = 1 :=
  Work.Shrinking.pow_eq_one_subquotient (fun _ hx => pow_refinedTerm_le p i j hx) x

instance instIsMulCommutativeRefinedQuotient (p : ℕ) (i j : ℕ) :
    IsMulCommutative (refinedQuotient p P i j) :=
  isMulCommutative_refinedQuotient p i j

open scoped IsMulCommutative in
/-- The `𝔽_p`-vector space structure on the graded piece `P_{(i,j)}/P_{(i,j)+1}`, written
additively as `Additive (refinedQuotient p P i j)`. -/
noncomputable instance instAddCommGroupRefinedQuotient (p : ℕ) (i j : ℕ) :
    AddCommGroup (Additive (refinedQuotient p P i j)) :=
  inferInstanceAs (AddCommGroup (Additive (refinedQuotient p P i j)))

/-- The `𝔽_p`-module structure on the graded piece of the refinement (exponent `p`). -/
noncomputable instance instModuleZModRefinedQuotient (p : ℕ) (i j : ℕ) :
    Module (ZMod p) (Additive (refinedQuotient p P i j)) :=
  AddCommGroup.zmodModule (fun x => by
    refine (Additive.toMul).injective ?_
    rw [toMul_nsmul, toMul_zero]
    exact pow_eq_one_refinedQuotient p i j (Additive.toMul x))

end Elementary

/-! ## The descended `G`-action -/

section Action

variable {G P : Type*} [Group G] [Group P] [MulDistribMulAction G P]

/-- The `G`-action on the graded piece `P_{(i,j)}/P_{(i,j)+1}` induced by the action of `G` on
`P` by automorphisms. -/
noncomputable def refinedQuotientActionHom (p : ℕ) (i j : ℕ) :
    G →* MulAut (refinedQuotient p P i j) :=
  Work.Shrinking.quotActionHom (refinedTerm p P i j)
    (refinedTerm p P (tauSucc i j).1 (tauSucc i j).2)
    (fun g => map_refinedTerm_eq p (MulDistribMulAction.toMulAut G P g) i j)
    (fun g => map_refinedTerm_eq p (MulDistribMulAction.toMulAut G P g)
      (tauSucc i j).1 (tauSucc i j).2)

/-- The `G`-action on the graded pieces of the refinement by group automorphisms. -/
noncomputable instance instMulDistribMulActionRefinedQuotient (p : ℕ) (i j : ℕ) :
    MulDistribMulAction G (refinedQuotient p P i j) where
  smul g x := refinedQuotientActionHom (G := G) p i j g x
  one_smul x := by
    show refinedQuotientActionHom (G := G) p i j 1 x = x
    rw [map_one]
    rfl
  mul_smul g h x := by
    show refinedQuotientActionHom (G := G) p i j (g * h) x
      = refinedQuotientActionHom (G := G) p i j g
          (refinedQuotientActionHom (G := G) p i j h x)
    rw [map_mul]
    rfl
  smul_mul g x y := map_mul (refinedQuotientActionHom (G := G) p i j g) x y
  smul_one g := map_one (refinedQuotientActionHom (G := G) p i j g)

/-- The corresponding action on `Additive (P_{(i,j)}/P_{(i,j)+1})`. -/
noncomputable instance instDistribMulActionAdditiveRefinedQuotient (p : ℕ) (i j : ℕ) :
    DistribMulAction G (Additive (refinedQuotient p P i j)) where
  smul g x := Additive.ofMul (g • Additive.toMul x)
  one_smul x := by
    show Additive.ofMul ((1 : G) • Additive.toMul x) = x
    rw [one_smul, ofMul_toMul]
  mul_smul g h x := by
    show Additive.ofMul ((g * h) • Additive.toMul x)
      = Additive.ofMul (g • Additive.toMul (Additive.ofMul (h • Additive.toMul x)))
    rw [mul_smul, toMul_ofMul]
  smul_zero g := by
    show Additive.ofMul (g • Additive.toMul (0 : Additive (refinedQuotient p P i j))) = 0
    rw [toMul_zero, smul_one, ofMul_one]
  smul_add g x y := by
    show Additive.ofMul (g • Additive.toMul (x + y))
      = Additive.ofMul (g • Additive.toMul x) + Additive.ofMul (g • Additive.toMul y)
    rw [toMul_add, MulDistribMulAction.smul_mul, ofMul_mul]

/-- The action of `G` on the graded pieces of the refinement is by `𝔽_p`-linear maps. -/
instance instSMulCommClassRefinedQuotient (p : ℕ) [NeZero p] (i j : ℕ) :
    SMulCommClass G (ZMod p) (Additive (refinedQuotient p P i j)) where
  smul_comm g c x := by
    conv_lhs => rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
    conv_rhs => rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
    exact Work.Shrinking.smul_nsmul_of_distribMulAction g c.val x

/-- The graded piece `P_{(i,j)}/P_{(i,j)+1}`, with its descended `G`-action, is an
`𝔽_p[G]`-module. -/
theorem isFpGModule_refinedQuotient (p : ℕ) [NeZero p] (i j : ℕ) :
    Work.Shrinking.IsFpGModule p G (Additive (refinedQuotient p P i j)) :=
  instSMulCommClassRefinedQuotient (G := G) p i j

end Action

/-! ## The graded pieces of the free `G`-operator groups -/

section Free

variable {G : Type*} [Group G]

/-- The graded piece `E(d,τ) = F(d)_{(i,j)}/F(d)_{(i,j)+1}` of the free `G`-operator group of
rank `d` is an `𝔽_p[G]`-module. -/
theorem isFpGModule_E (p : ℕ) [NeZero p] (d i j : ℕ) :
    Work.Shrinking.IsFpGModule p G (E p G d i j) :=
  isFpGModule_refinedQuotient (G := G) (P := Work.Shrinking.freeOperatorGroup G d) p i j

end Free

end Work.CohomologicalShrinking
