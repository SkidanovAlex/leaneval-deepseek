import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ProperStageDefs
import Submission.Work.SSGRoute.inertia_map_eq_of_isCyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The twist layer of Step 4 of Theorem 15 (Schmidt–Wingberg §5)

This module contains the *algebraic core* of Step 4: the graded piece `E(n,τ)` inside
`F(n)/F(n)^{(τ+1)}` (as `gradeIncl`/`gradeInl`), its centrality and equivariance, the stage
projection `Γ_{τ+1} →* Γ_τ`, and the twist `flowTwistEHom p K n i j x ψ hψquot hxmul` of a solution
`ψ` by an `E(n,τ)`-valued `1`-cocycle `x` together with its basic calculus.

**Why it is a separate module.**  The sibling nodes of this one (`Work.SSGRoute.step4_shrunk_input`,
`Work.SSGRoute.step4_local_target`, `Work.SSGRoute.twist_cyclic_of_psi_trivial`) need
`Work.SSGRoute.flowTwistEHom` and `Work.SSGRoute.restrict` in order to *state* the arithmetic that
Step 4 consumes.  Those nodes must not have to import the node file
`Submission.Work.SSGRoute.scholz_succ_of_properStage` itself, because that node is supposed to
*consume* them (`step4_shrunk_input` is exactly the input of `scholz_succ_of_properStage`), and a
module cycle is impossible in Lean.  So the twist layer lives here, upstream of both sides:
`step4_shrunk_input` and friends should import *this* module, and the node file imports them.

**The flip, verified 2026-09-25 (session 5).**  Replacing

  `import Submission.Work.SSGRoute.scholz_succ_of_properStage`

by

  `import Submission.Work.SSGRoute.twistLayer`

in the three files

* `Submission/Work/SSGRoute/twist_cyclic_of_psi_trivial.lean`,
* `Submission/Work/SSGRoute/step4_local_target.lean`,
* `Submission/Work/SSGRoute/step4_transport_of_sha13.lean`  (and hence
  `step4_transport_of_sha13_psi.lean`, which only imports the former),

leaves every statement *and proof* in them unchanged: copies of the two files with exactly that
import swap were built successfully, and the two transport files were re-elaborated together with
only this module and `place_basics`/`RamifiedPlacesAux` in scope.  After the flip, the whole
Step-4 item assembly (`step4_local_cyclic_bridge`, `step4_items_assembly`) and the local targets
are upstream of the node file `Submission.Work.SSGRoute.scholz_succ_of_properStage`, so the node can
consume them (and the producer of the bundle `Work.SSGRoute.Step4Input` can be written in that file
or in a module upstream of it, without a module cycle).
This module therefore also carries the *conjugacy transport of local coboundary conditions*
(`isCoboundaryOn_map_conj`, `decomp_smul`, `isCoboundaryOn_decomp_smul`,
`isCoboundaryOn_decomp_smul_iff`) at its end: `Work.SSGRoute.step4_transport_of_sha13` and
`Work.SSGRoute.step4_transport_of_sha13_psi` use `isCoboundaryOn_map_conj`, and they too must stay
upstream of the node file.
-/

open scoped Pointwise

namespace Work.SSGRoute

open SSGRoute
open _root_.SSGRoute
open Work.CohomologicalShrinking

/-! ## The algebraic core of Step 4 of Theorem 15

The induction step of Schmidt–Wingberg is proved by twisting a proper solution `ψ` at level `n` and
stage `τ + 1` by a global cocycle `x` with values in the graded piece `E(n,τ)`, in order to remove
the unramified part of the local extensions at the places where the ramification is new.

This part of the argument is pure algebra; it is developed here, independently of the arithmetic
inputs (`SSGRoute.coker_obstruction`, `SSGRoute.shafarevich_existence`), so that the step lemma can
be assembled from it once the arithmetic lands.

The two structural facts that make the twisting operation well defined with the *plain* `G(K/k)`
action on `E(n,τ)` (and not a twisted action) are:
* `E(n,τ) = F(n)^{(τ)}/F(n)^{(τ+1)}` is **central** in `F(n)/F(n)^{(τ+1)}`
  (`commutator_refinedTerm_le_top`, `gradeIncl_central`);
* the inclusion `E(n,τ) → F(n)/F(n)^{(τ+1)}` is **equivariant** for the descended `G(K/k)`-actions
  (`gradeIncl_smul`).
-/

variable {p : ℕ}

/-- **Lemma 4, centrality form.** The commutator of the refined term `P_{(i,j)}` with all of `P` lies
in the next refined term `P_{(i,j)+1}`; for `P = F(n)` this says that the graded piece `E(n,τ)` is
central in `F(n)/F(n)^{(τ+1)}`. -/
theorem commutator_refinedTerm_le_top (p : ℕ) (P : Type*) [Group P] (i j : ℕ) :
    ⁅refinedTerm p P i j, ⊤⁆ ≤ refinedTerm p P (tauSucc i j).1 (tauSucc i j).2 :=
  calc ⁅refinedTerm p P i j, ⊤⁆
      ≤ ⁅pSeries p P i, ⊤⁆ :=
        Subgroup.commutator_mono (refinedTerm_le_pSeries p P i j) le_rfl
    _ ≤ pSeries p P (i + 1) := commutator_pSeries_le p P i
    _ ≤ refinedTerm p P (tauSucc i j).1 (tauSucc i j).2 :=
        pSeries_succ_le_refinedTerm_succ p i j

/-- Version for the flow group. -/
theorem commutator_flowTerm_le_top (p : ℕ) (G : Type*) [Group G] (n i j : ℕ) :
    ⁅flowTerm p G n i j, ⊤⁆ ≤ flowTerm p G n (tauSucc i j).1 (tauSucc i j).2 :=
  commutator_refinedTerm_le_top p (Work.Shrinking.freeOperatorGroup G n) i j

/-! ### The graded piece inside `F(n)/F(n)^{(τ+1)}` and inside `Γ_{τ+1}` -/

/-- The subgroup of `↥⊤` by which we quotient in `F(n)/F(n)^{(i,j)}`. -/
noncomputable abbrev flowRel (p : ℕ) (G : Type*) [Group G] (n i j : ℕ) :
    Subgroup (↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))) :=
  (flowTerm p G n i j).subgroupOf ⊤

/-- The canonical map `E(n,τ) = F(n)^{(τ)}/F(n)^{(τ+1)} → F(n)/F(n)^{(τ+1)}`. -/
noncomputable def gradeIncl (p : ℕ) (G : Type*) [Group G] (n i j : ℕ) :
    refinedQuotient p (Work.Shrinking.freeOperatorGroup G n) i j →*
      flowQuotient p G n (tauSucc i j).1 (tauSucc i j).2 :=
  QuotientGroup.map
    ((refinedTerm p (Work.Shrinking.freeOperatorGroup G n) (tauSucc i j).1
        (tauSucc i j).2).subgroupOf
      (refinedTerm p (Work.Shrinking.freeOperatorGroup G n) i j))
    (flowRel p G n (tauSucc i j).1 (tauSucc i j).2)
    (Subgroup.inclusion le_top)
    (by intro x hx; rw [Subgroup.mem_comap]; exact hx)

/-- The canonical map `E(n,τ) → Γ_{τ+1}` into the normal subgroup
`F(n)/F(n)^{(τ+1)} ◁ Γ_{τ+1}`. -/
noncomputable def gradeInl (p : ℕ) (G : Type*) [Group G] (n i j : ℕ) :
    refinedQuotient p (Work.Shrinking.freeOperatorGroup G n) i j →*
      flowGroup p G n (tauSucc i j).1 (tauSucc i j).2 :=
  (flowInl p G n (tauSucc i j).1 (tauSucc i j).2).comp (gradeIncl p G n i j)

@[simp] theorem gradeIncl_apply_mk' (p : ℕ) (G : Type*) [Group G] (n i j : ℕ)
    (x : ↥(refinedTerm p (Work.Shrinking.freeOperatorGroup G n) i j)) :
    gradeIncl p G n i j
        (QuotientGroup.mk' ((refinedTerm p (Work.Shrinking.freeOperatorGroup G n)
          (tauSucc i j).1 (tauSucc i j).2).subgroupOf
            (refinedTerm p (Work.Shrinking.freeOperatorGroup G n) i j)) x) =
      QuotientGroup.mk' (flowRel p G n (tauSucc i j).1 (tauSucc i j).2)
        (Subgroup.inclusion le_top x :
          ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))) := by
  unfold gradeIncl
  rw [QuotientGroup.map_mk']
  rfl

@[simp] theorem gradeIncl_apply (p : ℕ) (G : Type*) [Group G] (n i j : ℕ)
    (x : ↥(refinedTerm p (Work.Shrinking.freeOperatorGroup G n) i j)) :
    gradeIncl p G n i j (↑x) =
      QuotientGroup.mk' (flowRel p G n (tauSucc i j).1 (tauSucc i j).2)
        (Subgroup.inclusion le_top x :
          ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))) := by
  rw [← QuotientGroup.mk'_apply]
  exact gradeIncl_apply_mk' p G n i j x

@[simp] theorem gradeInl_apply_mk' (p : ℕ) (G : Type*) [Group G] (n i j : ℕ)
    (x : ↥(refinedTerm p (Work.Shrinking.freeOperatorGroup G n) i j)) :
    gradeInl p G n i j
        (QuotientGroup.mk' ((refinedTerm p (Work.Shrinking.freeOperatorGroup G n)
          (tauSucc i j).1 (tauSucc i j).2).subgroupOf
            (refinedTerm p (Work.Shrinking.freeOperatorGroup G n) i j)) x) =
      flowInl p G n (tauSucc i j).1 (tauSucc i j).2
        (QuotientGroup.mk' (flowRel p G n (tauSucc i j).1 (tauSucc i j).2)
          (Subgroup.inclusion le_top x :
            ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)))) := by
  rw [gradeInl, MonoidHom.comp_apply, gradeIncl_apply_mk']

/-- **Computation of the descended action on a class**: the action of `G` on `F(n)/F(n)^{(i,j)}` is
conjugation on representatives. -/
theorem flowAction_apply_mk (p : ℕ) (G : Type*) [Group G] (n i j : ℕ) (g : G)
    (y : ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))) :
    flowAction p G n i j g (QuotientGroup.mk' (flowRel p G n i j) y) =
      QuotientGroup.mk' (flowRel p G n i j)
        (Work.Shrinking.subAut (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)) g
          (Subgroup.map_top_of_surjective _
            (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G n)
              g).surjective) y) := by
  show (Work.Shrinking.quotAut (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))
      (flowTerm p G n i j) g
      (Subgroup.map_top_of_surjective _
        (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G n) g).surjective)
      (map_refinedTerm_eq p (MulDistribMulAction.toMulAut G
        (Work.Shrinking.freeOperatorGroup G n) g) i j))
      (QuotientGroup.mk' ((flowTerm p G n i j).subgroupOf ⊤) y) = _
  exact Work.Shrinking.quotAut_mk (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))
    (flowTerm p G n i j) g _ _ y

/-- **Computation of the descended action on a class** of the graded piece. -/
theorem refinedQuotient_smul_apply_mk (p : ℕ) (G : Type*) [Group G] (n i j : ℕ) (g : G)
    (x : ↥(refinedTerm p (Work.Shrinking.freeOperatorGroup G n) i j)) :
    g • (QuotientGroup.mk' ((refinedTerm p (Work.Shrinking.freeOperatorGroup G n)
        (tauSucc i j).1 (tauSucc i j).2).subgroupOf
          (refinedTerm p (Work.Shrinking.freeOperatorGroup G n) i j)) x :
        refinedQuotient p (Work.Shrinking.freeOperatorGroup G n) i j) =
      QuotientGroup.mk' ((refinedTerm p (Work.Shrinking.freeOperatorGroup G n)
          (tauSucc i j).1 (tauSucc i j).2).subgroupOf
            (refinedTerm p (Work.Shrinking.freeOperatorGroup G n) i j))
        (Work.Shrinking.subAut (refinedTerm p (Work.Shrinking.freeOperatorGroup G n) i j) g
          (map_refinedTerm_eq p (MulDistribMulAction.toMulAut G
            (Work.Shrinking.freeOperatorGroup G n) g) i j) x) := by
  show (Work.Shrinking.quotAut (refinedTerm p (Work.Shrinking.freeOperatorGroup G n) i j)
      (refinedTerm p (Work.Shrinking.freeOperatorGroup G n) (tauSucc i j).1 (tauSucc i j).2)
      g
      (map_refinedTerm_eq p (MulDistribMulAction.toMulAut G
        (Work.Shrinking.freeOperatorGroup G n) g) i j)
      (map_refinedTerm_eq p (MulDistribMulAction.toMulAut G
        (Work.Shrinking.freeOperatorGroup G n) g) (tauSucc i j).1 (tauSucc i j).2))
      (QuotientGroup.mk' _ x) = _
  exact Work.Shrinking.quotAut_mk _ _ g _ _ x

/-- **Equivariance of the inclusion of the graded piece**: the canonical map
`E(n,τ) → F(n)/F(n)^{(τ+1)}` commutes with the descended `G`-actions. -/
theorem gradeIncl_smul (p : ℕ) (G : Type*) [Group G] (n i j : ℕ) (g : G)
    (v : refinedQuotient p (Work.Shrinking.freeOperatorGroup G n) i j) :
    flowAction p G n (tauSucc i j).1 (tauSucc i j).2 g (gradeIncl p G n i j v) =
      gradeIncl p G n i j (g • v) := by
  refine QuotientGroup.induction_on v ?_
  intro x
  have key : (Work.Shrinking.subAut (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)) g
        (Subgroup.map_top_of_surjective _
          (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G n)
            g).surjective))
        (Subgroup.inclusion le_top x) =
      Subgroup.inclusion le_top
        (Work.Shrinking.subAut (refinedTerm p (Work.Shrinking.freeOperatorGroup G n) i j) g
          (map_refinedTerm_eq p (MulDistribMulAction.toMulAut G
            (Work.Shrinking.freeOperatorGroup G n) g) i j) x) :=
    Subtype.ext (by rw [Subgroup.coe_inclusion, Work.Shrinking.subAut_coe,
      Subgroup.coe_inclusion, Work.Shrinking.subAut_coe])
  rw [← QuotientGroup.mk'_apply, gradeIncl_apply_mk', flowAction_apply_mk,
    refinedQuotient_smul_apply_mk, gradeIncl_apply_mk', key]

/-- **Centrality of the graded piece**: the image of `E(n,τ)` in `F(n)/F(n)^{(τ+1)}` is central
(Lemma 4 of Schmidt–Wingberg). -/
theorem gradeIncl_central (p : ℕ) (G : Type*) [Group G] (n i j : ℕ)
    (a : flowQuotient p G n (tauSucc i j).1 (tauSucc i j).2)
    (v : refinedQuotient p (Work.Shrinking.freeOperatorGroup G n) i j) :
    a * gradeIncl p G n i j v * a⁻¹ = gradeIncl p G n i j v := by
  refine QuotientGroup.induction_on v ?_
  intro x
  refine QuotientGroup.induction_on a ?_
  intro y
  rw [gradeIncl_apply, QuotientGroup.mk'_apply]
  set u : ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)) :=
    Subgroup.inclusion le_top x with hu
  have hcomm : (↑u : ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)) ⧸
        flowRel p G n (tauSucc i j).1 (tauSucc i j).2) * ↑y = ↑y * ↑u := by
    refine QuotientGroup.eq_iff_div_mem.mpr ?_
    have h := commutator_refinedTerm_le_top p (Work.Shrinking.freeOperatorGroup G n) i j
    rw [Subgroup.commutator_le] at h
    have hh := h x x.2 y (Subgroup.mem_top y)
    rw [commutatorElement_def] at hh
    rw [Subgroup.mem_subgroupOf]
    simp only [hu, div_eq_mul_inv]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, mul_inv_rev,
      mul_assoc] using hh
  rw [← hcomm]
  group


/-! ### The stage projection `Γ_{τ+1} → Γ_τ` and its kernel

The passage from a solution at `τ + 1` to its `τ`-component is the quotient map
`F(n)/F(n)^{(τ+1)} → F(n)/F(n)^{(τ)}`; its kernel is exactly the image of the graded piece
`E(n,τ)`. This is what makes precise the dichotomy in the definition of
`SSGRoute.IsProperStage`: a local group maps to `1` at level `τ` if and only if it lies in the
graded piece. -/

/-- The next refined term is contained in the previous one. -/
theorem flowTerm_tauSucc_le (p : ℕ) (G : Type*) [Group G] (n i j : ℕ) :
    flowTerm p G n (tauSucc i j).1 (tauSucc i j).2 ≤ flowTerm p G n i j := by
  unfold flowTerm
  rcases lt_or_ge j i with h | h
  · rw [tauSucc_of_lt h]; exact refinedTerm_antitone_snd p _ i j
  · rw [tauSucc_of_le h, refinedTerm_one]; exact le_sup_right

/-- The projection `F(n)/F(n)^{(τ+1)} →* F(n)/F(n)^{(τ)}`. -/
noncomputable def stageProjQuotient (p : ℕ) (G : Type*) [Group G] (n i j : ℕ) :
    flowQuotient p G n (tauSucc i j).1 (tauSucc i j).2 →* flowQuotient p G n i j :=
  QuotientGroup.map (flowRel p G n (tauSucc i j).1 (tauSucc i j).2) (flowRel p G n i j)
    (MonoidHom.id _)
    (by
      intro x hx
      rw [Subgroup.mem_comap]
      refine Subgroup.mem_subgroupOf.mpr ?_
      exact flowTerm_tauSucc_le p G n i j (Subgroup.mem_subgroupOf.mp hx))

/-- The graded piece is killed by the stage projection. -/
theorem stageProjQuotient_gradeIncl (p : ℕ) (G : Type*) [Group G] (n i j : ℕ)
    (v : refinedQuotient p (Work.Shrinking.freeOperatorGroup G n) i j) :
    stageProjQuotient p G n i j (gradeIncl p G n i j v) = 1 := by
  refine QuotientGroup.induction_on v ?_
  intro x
  rw [← QuotientGroup.mk'_apply, gradeIncl_apply_mk', stageProjQuotient,
    QuotientGroup.map_mk']
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact x.2

/-- **The kernel of the stage projection is the graded piece**: the local group of a solution at
`τ + 1` maps to `1` in `Γ_τ` if and only if it lies in `E(n,τ)`. -/
theorem stageProjQuotient_ker (p : ℕ) (G : Type*) [Group G] (n i j : ℕ) :
    (stageProjQuotient p G n i j).ker = (gradeIncl p G n i j).range := by
  ext y
  constructor
  · intro hy
    rw [MonoidHom.mem_ker] at hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (flowRel p G n (tauSucc i j).1 (tauSucc i j).2) y
    rw [stageProjQuotient, QuotientGroup.map_mk'] at hy
    simp only [MonoidHom.id_apply] at hy
    have hx : x ∈ flowRel p G n i j := by
      rw [QuotientGroup.eq_one_iff] at hy
      exact hy
    have hx' : (x : Work.Shrinking.freeOperatorGroup G n) ∈ flowTerm p G n i j :=
      Subgroup.mem_subgroupOf.mp hx
    refine ⟨QuotientGroup.mk' _ ⟨(x : Work.Shrinking.freeOperatorGroup G n), hx'⟩, ?_⟩
    rw [gradeIncl_apply_mk']
    exact congrArg
      (QuotientGroup.mk' (flowRel p G n (tauSucc i j).1 (tauSucc i j).2))
      (Subtype.ext rfl)
  · intro hy
    rw [MonoidHom.mem_ker]
    obtain ⟨v, rfl⟩ := hy
    exact stageProjQuotient_gradeIncl p G n i j v

/-- The stage projection sends a class to the corresponding class. -/
theorem stageProjQuotient_mk (p : ℕ) (G : Type*) [Group G] (n i j : ℕ)
    (z : (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))) :
    stageProjQuotient p G n i j
        (↑z : flowQuotient p G n (tauSucc i j).1 (tauSucc i j).2) =
      (↑z : flowQuotient p G n i j) := by
  rw [show (↑z : flowQuotient p G n (tauSucc i j).1 (tauSucc i j).2) =
      QuotientGroup.mk' (flowRel p G n (tauSucc i j).1 (tauSucc i j).2) z from rfl]
  rw [stageProjQuotient, QuotientGroup.map_mk']
  rfl

/-- **A lift at `τ + 1` has the same `τ`-component**: if `y` lifts `x` through the refinement,
then the level projection of `y`'s left component is `x`'s left component. -/
theorem stageProjQuotient_apply_of_liftsFlowAt (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    {n i j : ℕ}
    {y : flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2}
    {x : flowGroup p (K ≃ₐ[ℚ] K) n i j} (h : SSGRoute.LiftsFlowAt y x) :
    stageProjQuotient p (K ≃ₐ[ℚ] K) n i j y.left = x.left := by
  obtain ⟨-, z, hz1, hz2⟩ := h
  rw [hz1, hz2, stageProjQuotient_mk]

/-- The components of the image of the graded piece in `Γ_{τ+1}`. -/
@[simp] theorem gradeInl_left (p : ℕ) (G : Type*) [Group G] (n i j : ℕ)
    (v : refinedQuotient p (Work.Shrinking.freeOperatorGroup G n) i j) :
    (gradeInl p G n i j v).left = gradeIncl p G n i j v := rfl

@[simp] theorem gradeInl_right (p : ℕ) (G : Type*) [Group G] (n i j : ℕ)
    (v : refinedQuotient p (Work.Shrinking.freeOperatorGroup G n) i j) :
    (gradeInl p G n i j v).right = 1 := rfl

/-! ### The twist by an `E(n,τ)`-valued cocycle -/

/-- The restriction map `G_ℚ →* Gal(K/ℚ)`. -/
noncomputable abbrev restrict (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] :
    SSGRoute.GalQ →* (K ≃ₐ[ℚ] K) :=
  AlgEquiv.restrictNormalHom K

/-- The conjugation formula in a semidirect product: conjugating `inl b` by `a` is `inl` of the
conjugate. -/
theorem semidirect_inl_conj {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N}
    (a : SemidirectProduct N G φ) (b : N) :
    a * SemidirectProduct.inl b * a⁻¹ =
      SemidirectProduct.inl (a.left * (φ a.right) b * a.left⁻¹) := by
  ext <;> simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.inv_left, mul_assoc]

/-- **The conjugation action of a lift on the graded piece is the `G(K/ℚ)`-action.** If
`ψ : G_ℚ →* Γ_{τ+1}` lifts the restriction map, then conjugating the image of `v ∈ E(n,τ)` by `ψ σ`
is the image of `(res σ) · v`. This is the algebraic heart of the twisting step: because of it the
twist is by a cocycle for the plain `G(K/ℚ)`-module structure of `E(n,τ)`. -/
theorem gradeInl_conj (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] (n i j : ℕ)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (σ : SSGRoute.GalQ)
    (hψ : flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) = restrict K σ)
    (v : refinedQuotient p (Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n) i j) :
    ψ σ * gradeInl p (K ≃ₐ[ℚ] K) n i j v * (ψ σ)⁻¹ =
      gradeInl p (K ≃ₐ[ℚ] K) n i j (restrict K σ • v) := by
  have h1 : gradeInl p (K ≃ₐ[ℚ] K) n i j v =
      SemidirectProduct.inl (gradeIncl p (K ≃ₐ[ℚ] K) n i j v) := rfl
  have h2 : gradeInl p (K ≃ₐ[ℚ] K) n i j (restrict K σ • v) =
      SemidirectProduct.inl (gradeIncl p (K ≃ₐ[ℚ] K) n i j (restrict K σ • v)) := rfl
  rw [h1, h2, semidirect_inl_conj, show (ψ σ).right = restrict K σ from hψ, gradeIncl_smul]
  exact congrArg SemidirectProduct.inl
    (gradeIncl_central p (K ≃ₐ[ℚ] K) n i j (ψ σ).left (restrict K σ • v))

/-- **The twist** of a homomorphism `ψ : G_ℚ →* Γ_{τ+1}` by a multiplicative function
`x : G_ℚ → E(n,τ)`: `σ ↦ (x σ) · ψ σ`. -/
noncomputable def flowTwist (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) (n i j : ℕ)
    (x : SSGRoute.GalQ →
      refinedQuotient p (Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n) i j)
    (ψ : SSGRoute.GalQ →*
      flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2) :
    SSGRoute.GalQ → flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 :=
  fun σ => gradeInl p (K ≃ₐ[ℚ] K) n i j (x σ) * ψ σ

/-- **The twist is multiplicative** as soon as `x` is a `1`-cocycle for the `G(K/ℚ)`-module
structure of `E(n,τ)`. -/
theorem flowTwist_mul (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] (n i j : ℕ)
    (x : SSGRoute.GalQ →
      refinedQuotient p (Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n) i j)
    (ψ : SSGRoute.GalQ →*
      flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hψ : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) = restrict K σ)
    (hx : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ * (restrict K σ • x τ))
    (σ τ : SSGRoute.GalQ) :
    flowTwist p K n i j x ψ (σ * τ) =
      flowTwist p K n i j x ψ σ * flowTwist p K n i j x ψ τ := by
  have hconj := gradeInl_conj p K n i j ψ σ (hψ σ) (x τ)
  simp only [flowTwist]
  rw [hx σ τ, map_mul, map_mul ψ σ τ, ← hconj]
  group

/-- The twist has the same image in `Gal(K/ℚ)` as `ψ`. -/
theorem flowQuot_flowTwist (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) (n i j : ℕ)
    (x : SSGRoute.GalQ →
      refinedQuotient p (Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n) i j)
    (ψ : SSGRoute.GalQ →*
      flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2) (σ : SSGRoute.GalQ) :
    flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2
        (flowTwist p K n i j x ψ σ) =
      flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) := by
  have hker : flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2
      (gradeInl p (K ≃ₐ[ℚ] K) n i j (x σ)) = 1 :=
    flowQuot_inl p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 _
  rw [flowTwist, map_mul, hker, one_mul]

/-- Where the cocycle `x` vanishes, the twist agrees with `ψ`. -/
theorem flowTwist_eq_of_eq_one (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) (n i j : ℕ)
    (x : SSGRoute.GalQ →
      refinedQuotient p (Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n) i j)
    (ψ : SSGRoute.GalQ →*
      flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    {H : Subgroup SSGRoute.GalQ} (hx : ∀ σ ∈ H, x σ = 1) :
    ∀ σ ∈ H, flowTwist p K n i j x ψ σ = ψ σ := by
  intro σ hσ
  rw [flowTwist, hx σ hσ, map_one, one_mul]

/-! ### The twist in the additive notation of the arithmetic input -/

/-- The twist of `ψ` by an `E(n,τ)`-valued `1`-cocycle `x`, in the additive notation in which
the arithmetic input (`SSGRoute.shafarevich_existence`) provides `x`. -/
noncomputable def flowTwistE (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) (n i j : ℕ)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →*
      flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2) :
    SSGRoute.GalQ → flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 :=
  flowTwist p K n i j (fun σ => Additive.toMul (x σ)) ψ

/-- **The twist by an `E(n,τ)`-valued cocycle is multiplicative**, with the cocycle condition in
the additive form in which `SSGRoute.shafarevich_existence` produces it. -/
theorem flowTwistE_mul (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] (n i j : ℕ)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →*
      flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hψ : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) = restrict K σ)
    (hx : ∀ σ τ : SSGRoute.GalQ,
      x (σ * τ) = x σ + (restrict K σ : K ≃ₐ[ℚ] K) • x τ)
    (σ τ : SSGRoute.GalQ) :
    flowTwistE p K n i j x ψ (σ * τ) =
      flowTwistE p K n i j x ψ σ * flowTwistE p K n i j x ψ τ := by
  refine flowTwist_mul p K n i j (fun σ => Additive.toMul (x σ)) ψ hψ ?_ σ τ
  intro σ τ
  rw [hx σ τ]
  rfl

/-- The twist has the same image in `Gal(K/ℚ)` as `ψ`. -/
theorem flowQuot_flowTwistE (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) (n i j : ℕ)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →*
      flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2) (σ : SSGRoute.GalQ) :
    flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2
        (flowTwistE p K n i j x ψ σ) =
      flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) :=
  flowQuot_flowTwist p K n i j _ ψ σ

/-- The restriction map is trivial on `G_K`. -/
theorem restrict_eq_one_of_mem_fixingSubgroup (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    {σ : SSGRoute.GalQ} (h : σ ∈ K.fixingSubgroup) : restrict K σ = 1 := by
  refine AlgEquiv.ext (fun y => ?_)
  exact Subtype.ext (by
    have h1 := @AlgEquiv.restrictNormalHom_apply ℚ _ SSGRoute.QBar _ _ K
      (inferInstance : Normal ℚ ↥K) σ y
    have h2 : (1 : ↥K ≃ₐ[ℚ] ↥K) y = y := rfl
    rw [h2]
    exact h1.trans ((IntermediateField.mem_fixingSubgroup_iff K σ).mp h y y.2))

/-- Conversely: an automorphism whose restriction to `K` is trivial fixes `K` pointwise. -/
theorem mem_fixingSubgroup_of_restrict_eq_one (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    {σ : SSGRoute.GalQ} (h : restrict K σ = 1) : σ ∈ K.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have h1 := @AlgEquiv.restrictNormalHom_apply ℚ _ SSGRoute.QBar _ _ K
    (inferInstance : Normal ℚ ↥K) σ (⟨x, hx⟩ : ↥K)
  have hx' : (((AlgEquiv.restrictNormalHom K) σ) ⟨x, hx⟩ : SSGRoute.QBar) = x :=
    congrArg (Subtype.val) (AlgEquiv.congr_fun h (⟨x, hx⟩ : ↥K))
  calc σ x = (((AlgEquiv.restrictNormalHom ↥K) σ) ⟨x, hx⟩ : SSGRoute.QBar) := h1.symm
    _ = x := hx'

/-- A coboundary for the `Gal(K/ℚ)`-action vanishes on `G_K`. This is the mechanism by which the
twist preserves condition (i) of the Scholz conditions. -/
theorem eq_zero_of_isCoboundaryOn (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    (n i j : ℕ) {x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j} {H : Subgroup SSGRoute.GalQ}
    (h : SSGRoute.IsCoboundaryOn (restrict K) H x) :
    ∀ σ ∈ H, σ ∈ K.fixingSubgroup → x σ = 0 := by
  obtain ⟨m, hm⟩ := h
  intro σ hσ hfix
  rw [hm σ hσ, restrict_eq_one_of_mem_fixingSubgroup K hfix, one_smul, sub_self]

/-- The `E`-valued twist agrees with `ψ` on every subgroup on which the cocycle vanishes. -/
theorem flowTwistE_eq_of_eq_zero (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) (n i j : ℕ)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →*
      flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    {H : Subgroup SSGRoute.GalQ} (hx : ∀ σ ∈ H, x σ = 0) :
    ∀ σ ∈ H, flowTwistE p K n i j x ψ σ = ψ σ := by
  intro σ hσ
  rw [flowTwistE, flowTwist, hx σ hσ]
  simp

/-- **Condition (i) is preserved by the twist** as soon as the cocycle vanishes on `G_K`. -/
theorem flowTwistE_scholzT1 (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    (n i j : ℕ) (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →*
      flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hT1 : ∀ A : ValuationSubring SSGRoute.QBar, _root_.SSGRoute.IsT1Place p K A →
      ∀ σ ∈ _root_.SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup → ψ σ = 1)
    (hx : ∀ σ ∈ K.fixingSubgroup, x σ = 0) :
    ∀ A : ValuationSubring SSGRoute.QBar, _root_.SSGRoute.IsT1Place p K A →
      ∀ σ ∈ _root_.SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup →
        flowTwistE p K n i j x ψ σ = 1 := by
  intro A hA σ hσ hfix
  rw [flowTwistE_eq_of_eq_zero p K n i j x ψ hx σ hfix]
  exact hT1 A hA σ hσ hfix

/-- The twist, as a group homomorphism, when `x` is a `1`-cocycle for the `G(K/ℚ)`-action. -/
noncomputable def flowTwistHom (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    (n i j : ℕ)
    (x : SSGRoute.GalQ → refinedQuotient p (Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n) i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hψ : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) = restrict K σ)
    (hx : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ * (restrict K σ • x τ)) :
    SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 where
  toFun := flowTwist p K n i j x ψ
  map_one' := by
    have h1 : x 1 = x 1 * x 1 := by
      have := hx 1 1
      rwa [mul_one, map_one, one_smul] at this
    have hone : x 1 = 1 := by
      have h := congrArg (fun y => (x 1)⁻¹ * y) h1
      simpa using h.symm
    rw [flowTwist, hone, map_one, map_one, one_mul]
  map_mul' := by
    intro σ τ
    exact flowTwist_mul p K n i j x ψ hψ hx σ τ

/-- **The twist has open kernel** (so it is continuous for the discrete topology on `Γ_{τ+1}`) as
soon as `ψ` has open kernel and the cocycle `x` is locally constant. -/
theorem flowTwist_isOpen_ker (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    (n i j : ℕ)
    (x : SSGRoute.GalQ → refinedQuotient p (Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n) i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hψ : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) = restrict K σ)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ * (restrict K σ • x τ))
    (hopen : IsOpen (ψ.ker : Set SSGRoute.GalQ))
    (hx : SSGRoute.IsLocConstOn ⊤ x) :
    IsOpen ((flowTwistHom p K n i j x ψ hψ hxmul).ker : Set SSGRoute.GalQ) := by
  obtain ⟨U₀, hU₀open, hU₀⟩ := hx
  obtain ⟨U₁, hU₁open, hU₁sub⟩ :
      ∃ U₁ : Subgroup SSGRoute.GalQ, IsOpen (U₁ : Set SSGRoute.GalQ) ∧ U₁ ≤ ψ.ker :=
    ⟨_, hopen, le_rfl⟩
  set U : Subgroup SSGRoute.GalQ := U₀ ⊓ U₁ with hU
  have hUopen : IsOpen (U : Set SSGRoute.GalQ) := hU₀open.inter hU₁open
  have hinv : ∀ g : SSGRoute.GalQ, ∀ u ∈ U,
      (flowTwistHom p K n i j x ψ hψ hxmul) (g * u) =
        (flowTwistHom p K n i j x ψ hψ hxmul) g := by
    intro g u hu
    have h1 : x (g * u) = x g := hU₀ g trivial u hu.1 trivial
    have h2 : ψ (g * u) = ψ g := by
      rw [map_mul, MonoidHom.mem_ker.mp (hU₁sub hu.2), mul_one]
    show flowTwist p K n i j x ψ (g * u) = flowTwist p K n i j x ψ g
    rw [flowTwist, flowTwist, h1, h2]
  have hUsub : (U : Set SSGRoute.GalQ) ⊆
      ((flowTwistHom p K n i j x ψ hψ hxmul).ker : Set SSGRoute.GalQ) := by
    intro u hu
    have h := hinv 1 u hu
    simpa using h
  have hmul : ∀ k ∈ ((flowTwistHom p K n i j x ψ hψ hxmul).ker : Set SSGRoute.GalQ),
      ∀ u ∈ (U : Set SSGRoute.GalQ),
        k * u ∈ ((flowTwistHom p K n i j x ψ hψ hxmul).ker : Set SSGRoute.GalQ) := by
    intro k hk u hu
    have hk1 : (flowTwistHom p K n i j x ψ hψ hxmul) k = 1 := hk
    show (flowTwistHom p K n i j x ψ hψ hxmul) (k * u) = 1
    rw [hinv k u hu, hk1]
  have hset : ((flowTwistHom p K n i j x ψ hψ hxmul).ker : Set SSGRoute.GalQ) *
        (U : Set SSGRoute.GalQ) =
      ((flowTwistHom p K n i j x ψ hψ hxmul).ker : Set SSGRoute.GalQ) := by
    ext y
    constructor
    · rintro ⟨k, hk, u, hu, rfl⟩
      exact hmul k hk u hu
    · intro hy
      exact ⟨y, hy, 1, U.one_mem, mul_one y⟩
  rw [← hset]
  exact IsOpen.mul_left hUopen

/-- **The twist does not change the `τ`-component** of a solution: the graded piece lies in the
kernel of the level projection. -/
theorem stageProjQuotient_flowTwist (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) (n i j : ℕ)
    (x : SSGRoute.GalQ →
      refinedQuotient p (Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n) i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (σ : SSGRoute.GalQ) :
    stageProjQuotient p (K ≃ₐ[ℚ] K) n i j (flowTwist p K n i j x ψ σ).left =
      stageProjQuotient p (K ≃ₐ[ℚ] K) n i j (ψ σ).left := by
  rw [flowTwist]
  show stageProjQuotient p (K ≃ₐ[ℚ] K) n i j
      ((gradeInl p (K ≃ₐ[ℚ] K) n i j (x σ) * ψ σ).left) =
    stageProjQuotient p (K ≃ₐ[ℚ] K) n i j (ψ σ).left
  rw [SemidirectProduct.mul_left, gradeInl_left, gradeInl_right, map_one, MulAut.one_apply,
    map_mul, stageProjQuotient_gradeIncl, one_mul]

/-- **The twist lifts the same `τ`-solution.** Since the graded piece lies in the kernel of the
level projection, twisting by an `E(n,τ)`-valued cocycle does not change the `τ`-component. -/
theorem flowTwist_liftsFlowAt (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) (n i j : ℕ)
    (x : SSGRoute.GalQ →
      refinedQuotient p (Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n) i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (hLift : ∀ σ, SSGRoute.LiftsFlowAt (ψ σ) (φ σ)) (σ : SSGRoute.GalQ) :
    SSGRoute.LiftsFlowAt (flowTwist p K n i j x ψ σ) (φ σ) := by
  obtain ⟨hright, z₀, hz₁, hz₂⟩ := hLift σ
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective
    (flowRel p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (gradeIncl p (K ≃ₐ[ℚ] K) n i j (x σ))
  refine ⟨?_, a * z₀, ?_, ?_⟩
  · rw [flowTwist, SemidirectProduct.mul_right, gradeInl_right, one_mul]
    exact hright
  · rw [flowTwist, SemidirectProduct.mul_left, gradeInl_left, gradeInl_right, map_one,
      MulAut.one_apply, ← ha, hz₁]
    rw [← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply, ← map_mul]
  · have ha1 : (QuotientGroup.mk' (flowRel p (K ≃ₐ[ℚ] K) n i j) a :
        flowQuotient p (K ≃ₐ[ℚ] K) n i j) = 1 := by
      rw [QuotientGroup.mk'_apply, ← stageProjQuotient_mk p (K ≃ₐ[ℚ] K) n i j a,
        show (↑a : flowQuotient p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2) =
          gradeIncl p (K ≃ₐ[ℚ] K) n i j (x σ) from ha, stageProjQuotient_gradeIncl]
    rw [hz₂, ← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply, map_mul, ha1, one_mul]

/-- Version for group homomorphisms: the twist of a solution lifts the same `τ`-solution. -/
theorem flowTwistHom_liftsFlow (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    (n i j : ℕ)
    (x : SSGRoute.GalQ →
      refinedQuotient p (Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n) i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (hψ : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) = restrict K σ)
    (hx : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ * (restrict K σ • x τ))
    (hLift : ∀ σ, SSGRoute.LiftsFlowAt (ψ σ) (φ σ)) :
    SSGRoute.LiftsFlow (flowTwistHom p K n i j x ψ hψ hx) φ := by
  intro σ
  exact flowTwist_liftsFlowAt p K n i j x ψ φ hLift σ

/-! ### The logical content of Step 4

The Scholz conditions at `τ+1` for a solution `ψ` differ from the stage-3 clauses of
`SSGRoute.IsProperStage` only at the places where the ramification is *new*: there the stage-3
conditions only assert that the `τ`-level solution `φ` vanishes, whereas condition (ii) requires
the local group to be cyclic and equal to the image of the inertia. The following lemma isolates
exactly this remaining piece of local information. -/

/-- **Step 4, logical part.** If `ψ` satisfies the stage-3 clauses with respect to `φ` and, in
addition, the local groups at the places of new ramification are cyclic and equal to the image of
the inertia, then `ψ` satisfies the Scholz conditions at `τ + 1`. -/
theorem scholzConditions_of_stageData (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hT1 : ∀ A : ValuationSubring SSGRoute.QBar, _root_.SSGRoute.IsT1Place p K A →
      ∀ σ ∈ _root_.SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup → ψ σ = 1)
    (hInv : ∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → ψ c = 1)
    (hProp : ∀ A : ValuationSubring SSGRoute.QBar, _root_.SSGRoute.IsFinPlace ℚ A →
      (∃ σ, _root_.SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ ψ σ ≠ 1) →
      (∀ σ ∈ _root_.SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup) ∧
      ((∀ σ ∈ _root_.SSGRoute.decomp ℚ A, φ σ = 1) ∨
        (IsCyclic ((_root_.SSGRoute.decomp ℚ A).map ψ) ∧
          ∀ σ ∈ _root_.SSGRoute.decomp ℚ A,
            ∃ τ, _root_.SSGRoute.IsInertia ℚ A τ ∧ ψ τ = ψ σ)))
    (hNew : ∀ A : ValuationSubring SSGRoute.QBar, _root_.SSGRoute.IsFinPlace ℚ A →
      (∃ σ, _root_.SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ ψ σ ≠ 1) →
      (∀ σ ∈ _root_.SSGRoute.decomp ℚ A, φ σ = 1) →
      IsCyclic ((_root_.SSGRoute.decomp ℚ A).map ψ) ∧
        ∀ σ ∈ _root_.SSGRoute.decomp ℚ A,
          ∃ τ, _root_.SSGRoute.IsInertia ℚ A τ ∧ ψ τ = ψ σ) :
    _root_.SSGRoute.ScholzConditions p K ψ := by
  refine ⟨hT1, hInv, ?_⟩
  intro A hA hhyp
  rcases hProp A hA hhyp with ⟨hsplit, hcase⟩
  rcases hcase with hcase | hcase
  · exact ⟨hsplit, hNew A hA hhyp hcase⟩
  · exact ⟨hsplit, hcase⟩

/-! ### Injectivity of the inclusion of the graded piece, and its exponent

The canonical map `E(n,τ) = F(n)^{(τ)}/F(n)^{(τ+1)} → F(n)/F(n)^{(τ+1)}` and its composite with
`flowInl` into `Γ_{τ+1}` are injective, and the graded piece has exponent `p`.  The injectivity is
what turns "the twist is trivial at a place" into "the cocycle vanishes there"; the exponent is what
makes a cyclic local group of the new solution have order dividing `p` (hence, since it is
ramified, that it is *totally* ramified). -/

theorem gradeIncl_injective (p : ℕ) (G : Type*) [Group G] (n i j : ℕ) :
    Function.Injective (gradeIncl p G n i j) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  show (gradeIncl p G n i j).ker = ⊥
  rw [gradeIncl, QuotientGroup.ker_map, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  intro x hx
  exact hx

theorem gradeInl_injective (p : ℕ) (G : Type*) [Group G] (n i j : ℕ) :
    Function.Injective (gradeInl p G n i j) := by
  intro a b hab
  exact gradeIncl_injective p G n i j (flowInl_injective p G n (tauSucc i j).1 (tauSucc i j).2 hab)

@[simp] theorem gradeInl_eq_one_iff (p : ℕ) (G : Type*) [Group G] (n i j : ℕ)
    (v : refinedQuotient p (Work.Shrinking.freeOperatorGroup G n) i j) :
    gradeInl p G n i j v = 1 ↔ v = 1 :=
  ⟨fun h => gradeInl_injective p G n i j (by rw [h, map_one]), fun h => by rw [h, map_one]⟩

/-- **The commutation rule of the graded piece**: `E(n,τ)` is central in `F(n)/F(n)^{(τ+1)}` and
`gradeInl` is equivariant, so moving `gradeInl (res σ • v)` past `ψ σ` replaces `v` by `res σ • v`.
This is the form of `gradeInl_conj` used when the twist is compared with `ψ`. -/
theorem flowTwist_gradeInl_conj (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    (n i j : ℕ)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (σ : SSGRoute.GalQ)
    (hψ : flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) = restrict K σ)
    (v : refinedQuotient p (Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n) i j) :
    gradeInl p (K ≃ₐ[ℚ] K) n i j (restrict K σ • v) * ψ σ =
      ψ σ * gradeInl p (K ≃ₐ[ℚ] K) n i j v := by
  have h := gradeInl_conj p K n i j ψ σ hψ v
  rw [← h]
  group

/-- **The graded piece has exponent `p`** (Schmidt–Wingberg's `E(d,τ)` is an `𝔽_p`-vector space).
In the additive notation in which the arithmetic delivers the twisting cocycle this is
`p · v = 0`. -/
theorem gradeInl_pow_p (p : ℕ) (G : Type*) [Group G] (n i j : ℕ)
    (v : refinedQuotient p (Work.Shrinking.freeOperatorGroup G n) i j) :
    gradeInl p G n i j v ^ p = 1 := by
  have hzero : (p : ℕ) • (Additive.ofMul v) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) p (Additive.ofMul v), ZMod.natCast_self, zero_smul]
  have hv : v ^ p = 1 := by
    apply Additive.ofMul.injective
    rw [ofMul_pow, hzero]
    rfl
  rw [← map_pow, hv, map_one]

/-- Every element of the copy of the graded piece inside `Γ_{τ+1}` has order dividing `p`. -/
theorem pow_p_eq_one_of_mem_range_gradeInl (p : ℕ) (G : Type*) [Group G] (n i j : ℕ)
    {g : flowGroup p G n (tauSucc i j).1 (tauSucc i j).2}
    (hg : g ∈ (gradeInl p G n i j).range) : g ^ p = 1 := by
  obtain ⟨v, rfl⟩ := hg
  exact gradeInl_pow_p p G n i j v

/-- **Properness from the `T⁰`-generation.**  Let `proj : Γ' →* Γ` be the level projection, `φ` a
surjective solution at `τ` and `ψ` a lift of `φ` whose `T⁰`-images generate `ker proj`.  If another
lift `ψ'` of `φ` agrees with `ψ` on each `T i`, then `ψ'` is surjective.  This is the criterion by
which the twist of a proper solution remains proper: at the primes of `T⁰` the twisting cocycle
vanishes by construction, so the twist agrees with `ψ` there. -/
theorem surjective_of_iSup_map_eq_ker {Γ' Γ H : Type*} [Group Γ'] [Group Γ] [Group H]
    (proj : Γ' →* Γ) (ψ ψ' : H →* Γ') (φ : H →* Γ)
    (hproj : ∀ σ, proj (ψ' σ) = φ σ) (hφ : Function.Surjective φ)
    {ι : Type*} (T : ι → Subgroup H)
    (hgen : ⨆ i, (T i).map ψ = proj.ker)
    (heq : ∀ i, ∀ σ ∈ T i, ψ' σ = ψ σ) :
    Function.Surjective ψ' := by
  have hle : (⨆ i, (T i).map ψ) ≤ (MonoidHom.range ψ') := by
    refine iSup_le fun i => ?_
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y, heq i y hy⟩
  rw [hgen] at hle
  intro x
  obtain ⟨σ, hσ⟩ := hφ (proj x)
  have hmem : x * (ψ' σ)⁻¹ ∈ proj.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hproj σ, hσ, mul_inv_cancel]
  obtain ⟨σ', hσ'⟩ := hle hmem
  exact ⟨σ' * σ, by rw [map_mul, hσ', mul_assoc, inv_mul_cancel, mul_one]⟩

/-! ### The twist as a homomorphism, in the additive notation of the arithmetic input -/

/-- The twist of `ψ` by an `E(n,τ)`-valued `1`-cocycle `x`, as a group homomorphism, in the
additive notation in which the arithmetic input (`Work.SSGRoute.shafarevich_theorem13`) produces
the cocycle. -/
noncomputable def flowTwistEHom (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    (n i j : ℕ)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hψ : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) = restrict K σ)
    (hx : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (restrict K σ) • x τ) :
    SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 :=
  flowTwistHom p K n i j (fun σ => Additive.toMul (x σ)) ψ hψ
    (fun σ τ => by rw [hx σ τ]; rfl)

@[simp] theorem flowTwistEHom_apply (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    (n i j : ℕ) (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hψ : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) = restrict K σ)
    (hx : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (restrict K σ) • x τ)
    (σ : SSGRoute.GalQ) :
    flowTwistEHom p K n i j x ψ hψ hx σ = flowTwistE p K n i j x ψ σ := rfl

/-! ### The level projection of the twist, and the properness of the twist

`flowGroupProj` is the level projection `Γ_{τ+1} →* Γ_τ` of `Submission.Work.SSGRoute.ProperStageDefs`,
whose kernel `flowEKer` is the copy of the graded piece `E(n,τ)` inside `Γ_{τ+1}`.  The twist does not
change the `τ`-component (`flowGroupProj_comp_flowTwistEHom`), and it remains proper as soon as the
primes of `T⁰` generate `flowEKer` under `ψ` and `x` vanishes on their decomposition groups
(`surjective_flowTwistEHom_of_iSup`, the `T⁰` part of Step 4 of the paper). -/




/-- The level projection kills the copy of the graded piece. -/
theorem flowGroupProj_gradeInl (p : ℕ) (G : Type*) [Group G] (n i j : ℕ)
    (v : refinedQuotient p (Work.Shrinking.freeOperatorGroup G n) i j) :
    flowGroupProj p G n i j (gradeInl p G n i j v) = 1 := by
  rw [show gradeInl p G n i j v = SemidirectProduct.inl (gradeIncl p G n i j v) from rfl]
  rw [show flowGroupProj p G n i j =
      SemidirectProduct.map (flowQuotientProj p G n i j) (MonoidHom.id G) _ from rfl]
  rw [SemidirectProduct.map_inl]
  rw [show flowQuotientProj p G n i j = stageProjQuotient p G n i j from rfl]
  rw [stageProjQuotient_gradeIncl]
  rfl

/-- A lift through the refinement projects to the solution it lifts. -/
theorem flowGroupProj_eq_of_liftsFlowAt {p : ℕ} {K : IntermediateField ℚ SSGRoute.QBar}
    [Normal ℚ K] {n i j : ℕ}
    {y : flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2}
    {x : flowGroup p (K ≃ₐ[ℚ] K) n i j} (h : SSGRoute.LiftsFlowAt y x) :
    flowGroupProj p (K ≃ₐ[ℚ] K) n i j y = x := by
  obtain ⟨hright, z, hz1, hz2⟩ := h
  have hy : flowGroupProj p (K ≃ₐ[ℚ] K) n i j y =
      SemidirectProduct.mk (QuotientGroup.mk z : flowQuotient p (K ≃ₐ[ℚ] K) n i j) y.right := by
    rw [show y = SemidirectProduct.mk y.left y.right from rfl, flowGroupProj_mk, hz1,
      flowQuotientProj_coe]
  have hx : x = SemidirectProduct.mk (QuotientGroup.mk z : flowQuotient p (K ≃ₐ[ℚ] K) n i j)
      x.right := by
    rw [show x = SemidirectProduct.mk x.left x.right from rfl, hz2]
  rw [hy, hx, hright]

/-- The twist projects to the same solution as `ψ`. -/
theorem flowGroupProj_comp_flowTwistEHom (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    [Normal ℚ K] (n i j : ℕ)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) = restrict K σ)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (restrict K σ) • x τ)
    (hLift : ∀ σ, SSGRoute.LiftsFlowAt (ψ σ) (φ σ)) :
    (flowGroupProj p (K ≃ₐ[ℚ] K) n i j).comp
      (flowTwistEHom p K n i j x ψ hψquot hxmul) = φ := by
  refine MonoidHom.ext (fun σ => ?_)
  have hker := flowGroupProj_gradeInl p (K ≃ₐ[ℚ] K) n i j (Additive.toMul (x σ))
  have hstep : flowTwistEHom p K n i j x ψ hψquot hxmul σ =
      gradeInl p (K ≃ₐ[ℚ] K) n i j (Additive.toMul (x σ)) * ψ σ := by
    rw [flowTwistEHom_apply, flowTwistE, flowTwist]
  rw [MonoidHom.comp_apply, hstep, map_mul, hker, one_mul]
  exact flowGroupProj_eq_of_liftsFlowAt (hLift σ)


/-- **Properness of the twist.**  If the twist projects to the same solution `φ` as `ψ`, the
subgroups `T i` generate the kernel of the level projection under `ψ`, and the cocycle `x` vanishes
on each `T i`, then the twist is surjective.  In Step 4 of the paper the `T i` are the decomposition
groups of the primes of `T⁰` (which are chosen so that their images generate the graded piece, and
at which `x` is zero). -/
theorem surjective_flowTwistEHom_of_iSup (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    [Normal ℚ K] (n i j : ℕ)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (hφsurj : Function.Surjective φ)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) = restrict K σ)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (restrict K σ) • x τ)
    (hLift : ∀ σ, SSGRoute.LiftsFlowAt (ψ σ) (φ σ))
    {ι : Type*} (T : ι → Subgroup SSGRoute.GalQ)
    (hgen : (⨆ i, (T i).map ψ) = flowEKer p (K ≃ₐ[ℚ] K) n i j)
    (hT : ∀ i, ∀ σ ∈ T i, x σ = 0) :
    Function.Surjective (flowTwistEHom p K n i j x ψ hψquot hxmul) := by
  refine surjective_of_iSup_map_eq_ker (flowGroupProj p (K ≃ₐ[ℚ] K) n i j) ψ
    (flowTwistEHom p K n i j x ψ hψquot hxmul) φ ?_ hφsurj T ?_ ?_
  · intro σ
    exact congrFun (congrArg DFunLike.coe
      (flowGroupProj_comp_flowTwistEHom p K n i j x ψ φ hψquot hxmul hLift)) σ
  · rw [show flowEKer p (K ≃ₐ[ℚ] K) n i j =
        (flowGroupProj p (K ≃ₐ[ℚ] K) n i j).ker from rfl] at hgen
    exact hgen
  · intro i σ hσ
    rw [flowTwistEHom_apply, flowTwistE, flowTwist, hT i σ hσ]
    simp


/-! ### The local group of the twist at a place where the `τ`-solution is trivial

Two local facts about the twist at a place `A` with `φ(D_A) = 1` (a place completely decomposed in
`N_τ/ℚ`): the twist takes its values in the graded piece
(`map_le_range_gradeInl_of_flowQuot_eq_one`), and if in addition `ψ(D_A) = 1` and the cocycle is
split by the pro-cyclic quotient `D_A/U` of the decomposition group
(Theorem 13's "`x` is cyclic"), then the local group of the twist is cyclic
(`isCyclic_map_flowTwistEHom_of_localCyclic`). -/



/-- If the `τ`-component of a lift is trivial on a decomposition group then the lift takes its
values in the copy of the graded piece. -/
theorem map_le_range_gradeInl_of_flowQuot_eq_one (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    [Normal ℚ K] (n i j : ℕ)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (hLift : ∀ σ, SSGRoute.LiftsFlowAt (ψ σ) (φ σ))
    (A : ValuationSubring SSGRoute.QBar) (hA : ∀ σ ∈ decomp ℚ A, φ σ = 1) :
    (decomp ℚ A).map ψ ≤ (gradeInl p (K ≃ₐ[ℚ] K) n i j).range := by
  rintro y ⟨σ, hσ, rfl⟩
  have hφ1 : φ σ = 1 := hA σ hσ
  have hleft : (ψ σ).left ∈ (gradeIncl p (K ≃ₐ[ℚ] K) n i j).range := by
    rw [← stageProjQuotient_ker p (K ≃ₐ[ℚ] K) n i j, MonoidHom.mem_ker,
      stageProjQuotient_apply_of_liftsFlowAt (p := p) (K := K) (n := n) (i := i) (j := j)
        (hLift σ), hφ1]
    rfl
  obtain ⟨v, hv⟩ := hleft
  obtain ⟨hright, -⟩ := hLift σ
  have hright' : (ψ σ).right = 1 := by rw [hright, hφ1]; rfl
  have hy : ψ σ = SemidirectProduct.mk (gradeIncl p (K ≃ₐ[ℚ] K) n i j v) 1 := by
    rw [show ψ σ = SemidirectProduct.mk (ψ σ).left (ψ σ).right from rfl, hv, hright']
  exact ⟨v, by rw [hy]; rfl⟩

/-- **Cyclicity of the local group of the twist from the local cyclicity of the cocycle.**  If the
`τ`-solution and the lift are both trivial on the decomposition group of `A` (so the twist is given
there by the cocycle alone), and the cocycle is split by the pro-cyclic quotient `D_A/U` generated
by `g`, then the local group of the twist is cyclic (generated by the image of `g`). -/
theorem isCyclic_map_flowTwistEHom_of_localCyclic (p : ℕ)
    (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] (n i j : ℕ)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) = restrict K σ)
    (hφquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n i j (φ σ) = restrict K σ)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (restrict K σ) • x τ)
    (A : ValuationSubring SSGRoute.QBar)
    (hA : ∀ σ ∈ decomp ℚ A, φ σ = 1)
    (hψA : ∀ σ ∈ decomp ℚ A, ψ σ = 1)
    (U : Subgroup SSGRoute.GalQ) (hU : U ≤ decomp ℚ A) (hxU : ∀ σ ∈ U, x σ = 0)
    (g : SSGRoute.GalQ) (hg : g ∈ decomp ℚ A)
    (hgen : ∀ δ ∈ decomp ℚ A, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ U) :
    IsCyclic ((decomp ℚ A).map (flowTwistEHom p K n i j x ψ hψquot hxmul)) := by
  have hres1 : ∀ σ ∈ decomp ℚ A, restrict K σ = 1 := fun σ hσ => by
    rw [← hφquot σ, hA σ hσ]; rfl
  have hxadd : ∀ σ ∈ decomp ℚ A, ∀ τ ∈ decomp ℚ A, x (σ * τ) = x σ + x τ := by
    intro σ hσ τ hτ
    rw [hxmul σ τ, hres1 σ hσ, one_smul]
  have hval : ∀ δ ∈ decomp ℚ A, ∃ m : ℤ,
      flowTwistEHom p K n i j x ψ hψquot hxmul δ =
        (flowTwistEHom p K n i j x ψ hψquot hxmul g) ^ m := by
    intro δ hδ
    obtain ⟨m, hm⟩ := hgen δ hδ
    have hδeq : δ = g ^ m * (δ⁻¹ * g ^ m)⁻¹ := by group
    have hmem : (δ⁻¹ * g ^ m) ∈ U := hm
    have hx0 : x ((δ⁻¹ * g ^ m)⁻¹) = 0 := by
      have h1 : x ((δ⁻¹ * g ^ m)⁻¹) + x (δ⁻¹ * g ^ m) = 0 := by
        rw [← hxadd _ (hU (Subgroup.inv_mem _ hmem)) _ (hU hmem), inv_mul_cancel,
          hxU 1 (U.one_mem)]
      rw [hxU _ hmem] at h1
      simpa using h1
    have hψ1 : ψ ((δ⁻¹ * g ^ m)⁻¹) = 1 := by
      rw [map_inv, hψA _ (hU hmem), inv_one]
    have htw : flowTwistEHom p K n i j x ψ hψquot hxmul ((δ⁻¹ * g ^ m)⁻¹) = 1 := by
      rw [flowTwistEHom_apply, flowTwistE, flowTwist, hx0, hψ1]
      simp
    refine ⟨m, ?_⟩
    rw [hδeq, map_mul, map_zpow, htw, mul_one]
  refine (Subgroup.isCyclic_iff_exists_zpowers_eq_top _).mpr ?_
  refine ⟨flowTwistEHom p K n i j x ψ hψquot hxmul g, le_antisymm ?_ ?_⟩
  · exact Subgroup.zpowers_le.mpr ⟨g, hg, rfl⟩
  · rintro y ⟨δ, hδ, rfl⟩
    obtain ⟨m, hm⟩ := hval δ hδ
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, hm.symm⟩


/-- **The "totally ramified" half of condition (ii), derived from the cyclicity of the local group.**

At a place `A` where the `τ`-solution is trivial (`φ(D_A) = 1`), the local group of the twist is
cyclic (the arithmetic input), and moreover the image of the inertia is already the whole local
group as soon as the twist is ramified there.  This is condition (ii) at the places of new
ramification, with everything except the cyclicity of the local group derived. -/
theorem inertia_map_eq_flowTwistEHom (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] (n i j : ℕ)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) = restrict K σ)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (restrict K σ) • x τ)
    (hLift : ∀ σ, SSGRoute.LiftsFlowAt (ψ σ) (φ σ))
    (A : ValuationSubring SSGRoute.QBar)
    (hφ1 : ∀ σ ∈ decomp ℚ A, φ σ = 1)
    (hcyc : IsCyclic ((decomp ℚ A).map (flowTwistEHom p K n i j x ψ hψquot hxmul)))
    (hne : ∃ σ, IsInertia ℚ A σ ∧ (flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) :
    ∀ σ ∈ decomp ℚ A, ∃ τ, IsInertia ℚ A τ ∧
      (flowTwistEHom p K n i j x ψ hψquot hxmul) τ =
      (flowTwistEHom p K n i j x ψ hψquot hxmul) σ := by
  have hLiftTwist : ∀ σ, SSGRoute.LiftsFlowAt
      (flowTwistEHom p K n i j x ψ hψquot hxmul σ) (φ σ) := fun σ =>
    flowTwist_liftsFlowAt p K n i j (fun θ => Additive.toMul (x θ)) ψ φ hLift σ
  have hsub := map_le_range_gradeInl_of_flowQuot_eq_one p K n i j
    (flowTwistEHom p K n i j x ψ hψquot hxmul) φ hLiftTwist A hφ1
  refine inertia_map_eq_of_isCyclic p _ A (fun g hg => ?_) hcyc hne
  exact pow_p_eq_one_of_mem_range_gradeInl p (K ≃ₐ[ℚ] K) n i j (hsub hg)


/-- **Where the cocycle `x` vanishes, the twist has the same local group as `ψ`.**  In particular
the twist is cyclic at a place `A` as soon as `ψ` is, provided `x` vanishes on `D_A`.  This is what
disposes of the primes of the finite set `T⁰` in Step 4 of the paper: there `x = 0` by construction
(the `T⁰` primes are responsible for the *properness* of the twist, and the cocycle is chosen
trivial on them), and the local groups of `ψ` are cyclic there. -/
theorem map_flowTwistEHom_eq_map_of_x_eq_zero (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    [Normal ℚ K] (n i j : ℕ) (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) = restrict K σ)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (restrict K σ) • x τ)
    {H : Subgroup SSGRoute.GalQ} (hx : ∀ σ ∈ H, x σ = 0) :
    H.map (flowTwistEHom p K n i j x ψ hψquot hxmul) = H.map ψ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ, (flowTwistE_eq_of_eq_zero p K n i j x ψ hx σ hσ).symm⟩
  · rintro _ ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ, flowTwistE_eq_of_eq_zero p K n i j x ψ hx σ hσ⟩

/-- **Cyclicity at a place where the cocycle vanishes.** -/
theorem isCyclic_map_flowTwistEHom_of_x_eq_zero (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    [Normal ℚ K] (n i j : ℕ) (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) = restrict K σ)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (restrict K σ) • x τ)
    {H : Subgroup SSGRoute.GalQ} (hx : ∀ σ ∈ H, x σ = 0)
    (hcyc : IsCyclic (H.map ψ)) :
    IsCyclic (H.map (flowTwistEHom p K n i j x ψ hψquot hxmul)) := by
  rw [map_flowTwistEHom_eq_map_of_x_eq_zero p K n i j x ψ hψquot hxmul hx]
  exact hcyc

/-- Two elements of the image of `gradeInl` commute (the graded piece is central in
`F(n)/F(n)^{(τ+1)}`). -/
theorem gradeInl_mul_comm (p : ℕ) (G : Type*) [Group G] (n i j : ℕ)
    (a b : refinedQuotient p (Work.Shrinking.freeOperatorGroup G n) i j) :
    gradeInl p G n i j a * gradeInl p G n i j b =
      gradeInl p G n i j b * gradeInl p G n i j a := by
  have hc := gradeIncl_central p G n i j (gradeIncl p G n i j b) a
  have key : gradeIncl p G n i j a * gradeIncl p G n i j b =
      gradeIncl p G n i j b * gradeIncl p G n i j a := by
    calc gradeIncl p G n i j a * gradeIncl p G n i j b
        = (gradeIncl p G n i j b * gradeIncl p G n i j a * (gradeIncl p G n i j b)⁻¹) *
            gradeIncl p G n i j b := by rw [hc]
      _ = gradeIncl p G n i j b * gradeIncl p G n i j a := by group
  simp only [gradeInl, MonoidHom.comp_apply]
  rw [← map_mul (flowInl p G n (tauSucc i j).1 (tauSucc i j).2) (gradeIncl p G n i j a)
        (gradeIncl p G n i j b),
      ← map_mul (flowInl p G n (tauSucc i j).1 (tauSucc i j).2) (gradeIncl p G n i j b)
        (gradeIncl p G n i j a),
      key]

/-- **Twisting by a coboundary is conjugation.** -/
theorem flowTwistEHom_eq_conj_of_isCoboundaryOn (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    [Normal ℚ K] (n i j : ℕ) (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) = restrict K σ)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (restrict K σ) • x τ)
    {H : Subgroup SSGRoute.GalQ} (h : SSGRoute.IsCoboundaryOn (restrict K) H x) :
    ∃ m : E p (K ≃ₐ[ℚ] K) n i j, ∀ σ ∈ H,
      flowTwistEHom p K n i j x ψ hψquot hxmul σ
        = (gradeInl p (K ≃ₐ[ℚ] K) n i j (Additive.toMul m))⁻¹ * ψ σ *
            gradeInl p (K ≃ₐ[ℚ] K) n i j (Additive.toMul m) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, fun σ hσ => ?_⟩
  rw [flowTwistEHom_apply, flowTwistE, flowTwist, hm σ hσ]
  have htoMul : Additive.toMul (restrict K σ • m - m) =
      (restrict K σ) • (Additive.toMul m) * (Additive.toMul m)⁻¹ := by
    rw [_root_.toMul_sub, div_eq_mul_inv]
    congr 1

  rw [htoMul, map_mul, map_inv]
  set M := gradeInl p (K ≃ₐ[ℚ] K) n i j (Additive.toMul m) with hM
  have h1 : gradeInl p (K ≃ₐ[ℚ] K) n i j ((restrict K σ) • Additive.toMul m) =
      ψ σ * M * (ψ σ)⁻¹ :=
    (gradeInl_conj p K n i j ψ σ (hψquot σ) (Additive.toMul m)).symm
  have h2 : gradeInl p (K ≃ₐ[ℚ] K) n i j ((restrict K (σ⁻¹)) • Additive.toMul m) =
      (ψ σ)⁻¹ * M * ψ σ := by
    have h := gradeInl_conj p K n i j ψ (σ⁻¹) (hψquot σ⁻¹) (Additive.toMul m)
    rw [map_inv] at h
    rw [← h, ← hM]
    group
  have hMN : Commute M (gradeInl p (K ≃ₐ[ℚ] K) n i j ((restrict K (σ⁻¹)) • Additive.toMul m)) :=
    gradeInl_mul_comm p (K ≃ₐ[ℚ] K) n i j _ _
  have hNinv : (ψ σ)⁻¹ * M⁻¹ * ψ σ =
      (gradeInl p (K ≃ₐ[ℚ] K) n i j ((restrict K (σ⁻¹)) • Additive.toMul m))⁻¹ := by
    rw [h2]; group
  rw [h1]
  rw [show (ψ σ * M * (ψ σ)⁻¹) * M⁻¹ * ψ σ =
        ψ σ * (M * ((ψ σ)⁻¹ * M⁻¹ * ψ σ)) from by group,
      show M⁻¹ * ψ σ * M = ψ σ * ((ψ σ)⁻¹ * M⁻¹ * ψ σ) * M from by group,
      hNinv, (Commute.inv_right hMN).eq]
  group

/-- **The inertia generates the local group of the twist exactly when it generates that of `ψ`.** -/
theorem inertia_generates_flowTwistEHom_iff (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    [Normal ℚ K] (n i j : ℕ) (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) = restrict K σ)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (restrict K σ) • x τ)
    {H I : Subgroup SSGRoute.GalQ} (hIH : I ≤ H)
    (h : SSGRoute.IsCoboundaryOn (restrict K) H x) :
    (∀ σ ∈ H, ∃ τ ∈ I, flowTwistEHom p K n i j x ψ hψquot hxmul τ =
        flowTwistEHom p K n i j x ψ hψquot hxmul σ) ↔
      (∀ σ ∈ H, ∃ τ ∈ I, ψ τ = ψ σ) := by
  obtain ⟨m, hm⟩ := flowTwistEHom_eq_conj_of_isCoboundaryOn p K n i j x ψ hψquot hxmul h
  constructor
  · intro h1 σ hσ
    obtain ⟨τ, hτ, hτeq⟩ := h1 σ hσ
    refine ⟨τ, hτ, ?_⟩
    rw [hm τ (hIH hτ), hm σ hσ] at hτeq
    exact mul_left_cancel (mul_right_cancel hτeq)
  · intro h1 σ hσ
    obtain ⟨τ, hτ, hτeq⟩ := h1 σ hσ
    exact ⟨τ, hτ, by rw [hm τ (hIH hτ), hm σ hσ, hτeq]⟩

/-- **Cyclicity of the local group survives twisting by a coboundary.** -/
theorem isCyclic_map_flowTwistEHom_of_isCoboundaryOn (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    [Normal ℚ K] (n i j : ℕ) (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) = restrict K σ)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (restrict K σ) • x τ)
    {H : Subgroup SSGRoute.GalQ} (h : SSGRoute.IsCoboundaryOn (restrict K) H x)
    (hcyc : IsCyclic (H.map ψ)) :
    IsCyclic (H.map (flowTwistEHom p K n i j x ψ hψquot hxmul)) := by
  obtain ⟨m, hm⟩ := flowTwistEHom_eq_conj_of_isCoboundaryOn p K n i j x ψ hψquot hxmul h
  set c := (gradeInl p (K ≃ₐ[ℚ] K) n i j (Additive.toMul m))⁻¹ with hc
  rw [Subgroup.isCyclic_iff_exists_zpowers_eq_top] at hcyc ⊢
  obtain ⟨g, hg⟩ := hcyc
  refine ⟨c * g * c⁻¹, ?_⟩
  have hpow : ∀ k : ℤ, (c * g * c⁻¹) ^ k = (MulAut.conj c) (g ^ k) := by
    intro k
    rw [← MulAut.conj_apply c g, map_zpow]
  ext y
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨k, rfl⟩
    have hmem : g ^ k ∈ H.map ψ := by
      rw [← hg]; exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
    obtain ⟨σ, hσ, hψσ⟩ := Subgroup.mem_map.mp hmem
    refine ⟨σ, hσ, ?_⟩
    rw [hm σ hσ, hψσ, hpow k, MulAut.conj_apply, hc]
    group
  · rintro ⟨σ, hσ, rfl⟩
    have hmem : ψ σ ∈ H.map ψ := Subgroup.mem_map_of_mem ψ hσ
    rw [← hg] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine ⟨k, ?_⟩
    rw [hpow, hk]
    rw [hm σ hσ, MulAut.conj_apply, hc]
    group

/-- **The primes of `T⁰` have cyclic local groups for `ψ`.**  If `T⁰` generates the kernel copy
`flowEKer` under `ψ` (so that the twist is proper, `surjective_flowTwistEHom_of_iSup`), then the
local group of `ψ` at every `A ∈ T⁰` lies in `flowEKer`; a place of `T⁰` is therefore completely
decomposed in the level-`τ` field. -/
theorem flowQuot_eq_one_of_mem_iSup_map_le (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    [Normal ℚ K] (n i j : ℕ)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (hLift : ∀ σ, flowGroupProj p (K ≃ₐ[ℚ] K) n i j (ψ σ) = φ σ)
    {T0 : Finset (ValuationSubring SSGRoute.QBar)}
    (hgen : (⨆ A ∈ T0, (decomp ℚ A).map ψ) = flowEKer p (K ≃ₐ[ℚ] K) n i j)
    {A : ValuationSubring SSGRoute.QBar} (hA : A ∈ T0) :
    ∀ σ ∈ decomp ℚ A, φ σ = 1 := by
  intro σ hσ
  have hle : (decomp ℚ A).map ψ ≤ flowEKer p (K ≃ₐ[ℚ] K) n i j := by
    rw [← hgen]
    exact le_iSup₂_of_le A hA le_rfl
  have hmem : ψ σ ∈ flowEKer p (K ≃ₐ[ℚ] K) n i j :=
    hle (Subgroup.mem_map_of_mem ψ hσ)
  rw [← hLift σ]
  exact hmem




/-! ### Conjugation of places and the transfer of local coboundary conditions

The places `A` and `g • A` of `Ω` are conjugate over `k`, so their decomposition groups are
conjugate (`decomp_smul`) and a `1`-cocycle which is a coboundary on `D_A` is a coboundary on
`D_{g • A}` (`isCoboundaryOn_decomp_smul`, `isCoboundaryOn_decomp_smul_iff`).  This is what allows
the local clauses of `SSGRoute.shafarevich_theorem13`, which are stated for the places of the
finite set `S` (one per prime), to be used at an arbitrary place over the same prime — e.g. in the
condition (i) of the Scholz conditions.  The general algebraic statement is
`isCoboundaryOn_map_conj`, whose explicit witness for the conjugate subgroup is
`act g • m - x g`. -/



/-- **Coboundaries transfer to conjugate subgroups.**  If `x` is a `1`-cocycle on `Γ` and a
coboundary on `H ≤ Γ`, then it is a coboundary on `g H g⁻¹`, with the explicit witness
`act g • m - x g`.  (The last correction term is what makes the conjugation of the *function* `x`
agree with `x` up to the coboundary of `x g`.) -/
theorem isCoboundaryOn_map_conj {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M] (act : Γ →* G) (H : Subgroup Γ) (g : Γ) (x : Γ → M)
    (hx : SSGRoute.IsCocycleOn act ⊤ x) (h : SSGRoute.IsCoboundaryOn act H x) :
    SSGRoute.IsCoboundaryOn act (H.map (MulAut.conj g).toMonoidHom) x := by
  obtain ⟨m, hm⟩ := h
  refine ⟨act g • m - x g, fun δ hδ => ?_⟩
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hδ
  change x (g * γ * g⁻¹) =
    act (g * γ * g⁻¹) • (act g • m - x g) - (act g • m - x g)
  have hx1 : x 1 = 0 := by
    have h := hx 1 (Subgroup.mem_top 1) 1 (Subgroup.mem_top 1)
    simpa using h
  have hginv : x g⁻¹ = - (act g⁻¹ • x g) := by
    have h := hx g⁻¹ (Subgroup.mem_top _) g (Subgroup.mem_top _)
    rw [inv_mul_cancel, hx1] at h
    have h' : x g⁻¹ + act g⁻¹ • x g = 0 := h.symm
    calc x g⁻¹ = x g⁻¹ + act g⁻¹ • x g - act g⁻¹ • x g := by abel
      _ = 0 - act g⁻¹ • x g := by rw [h']
      _ = - (act g⁻¹ • x g) := by rw [zero_sub]
  have hkey : x (g * γ * g⁻¹) = x g + act g • x γ - act (g * γ * g⁻¹) • x g := by
    have h2 := hx (g * γ) (Subgroup.mem_top _) g⁻¹ (Subgroup.mem_top _)
    have h3 := hx g (Subgroup.mem_top _) γ (Subgroup.mem_top _)
    rw [h3, hginv, smul_neg, ← mul_smul, ← map_mul] at h2
    rw [show (g * γ) * g⁻¹ = g * γ * g⁻¹ from rfl] at h2
    rw [h2]
    abel
  rw [hkey, hm γ hγ, smul_sub, smul_sub]
  rw [show act g • (act γ • m) = act (g * γ) • m from by rw [← mul_smul, ← map_mul]]
  rw [show act (g * γ * g⁻¹) • (act g • m) = act (g * γ) • m from by
    rw [← mul_smul, ← map_mul, show (g * γ * g⁻¹) * g = g * γ from by group]]
  abel


open scoped Pointwise

/-- Translating a place conjugates its decomposition group. -/
theorem decomp_smul {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (A : ValuationSubring Ω) (g : Ω ≃ₐ[k] Ω) :
    SSGRoute.decomp k (g • A) = (SSGRoute.decomp k A).map (MulAut.conj g).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g A

/-- **Coboundaries transfer between conjugate places.** -/
theorem isCoboundaryOn_decomp_smul {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] {M : Type} [AddCommGroup M]
    [DistribMulAction (K ≃ₐ[k] K) M]
    (A : ValuationSubring Ω) (g : Ω ≃ₐ[k] Ω) (x : (Ω ≃ₐ[k] Ω) → M)
    (hx : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ x)
    (h : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) x) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k (g • A)) x := by
  rw [decomp_smul]
  exact isCoboundaryOn_map_conj (SSGRoute.res k K) (SSGRoute.decomp k A) g x hx h

/-- **Coboundaries transfer between conjugate places**, as an equivalence. -/
theorem isCoboundaryOn_decomp_smul_iff {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] {M : Type} [AddCommGroup M]
    [DistribMulAction (K ≃ₐ[k] K) M]
    (A : ValuationSubring Ω) (g : Ω ≃ₐ[k] Ω) (x : (Ω ≃ₐ[k] Ω) → M)
    (hx : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ x) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k (g • A)) x ↔
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) x := by
  constructor
  · intro h
    have h' := isCoboundaryOn_decomp_smul K (g • A) g⁻¹ x hx h
    simpa using h'
  · intro h
    exact isCoboundaryOn_decomp_smul K A g x hx h



end Work.SSGRoute
