import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Nat.Prime.Defs
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Work.CohomologicalShrinking

/-!
# The equivariant surjection `F(m)/F(m)^{(ν+1,1)} ↠ F^(n)/F^(n)(ν)`

Auxiliary lemmas for `Work.SSGRoute.equivariant_flowQuotient_surjection`.

The map is built on the free `G`-operator group `F(m) = FreeGroup (Fin m × G)` (`m = max n 1`) by
sending the generator `x_{a,g}` to `Φ g (mk (of a'))` for the `Fin n`-index `a'` corresponding to
`a` (and to `1` when `(a : ℕ) ≥ n`, in particular when `n = 0`), and then descending to the
quotient `F(m)/F(m)^{(ν+1,1)} = F(m)/F(m)_ν` (since `F(m)^{(ν+1,1)} = F(m)_{ν+1}`, and `F(m)_{ν+1}`
is the `ν`-th term `pCentralSeries p F(m) ν` of the `0`-indexed `p`-central series).
-/

section Aux

variable {G : Type*} [Group G]

/-- The refined term `F(m)^{(ν+1,1)}` is the `ν`-th term of the (0-indexed) `p`-central series:
`pSeries p F (ν+1) = pCentralSeries p F ν`. -/
lemma ssg_flowTerm_succ_one (p : ℕ) (G : Type*) [Group G] (m ν : ℕ) :
    flowTerm p G m (ν + 1) 1
      = Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G m) ν := by
  show Work.CohomologicalShrinking.refinedTerm p
    (Work.Shrinking.freeOperatorGroup G m) (ν + 1) 1 = _
  rw [Work.CohomologicalShrinking.refinedTerm_one]
  rfl

/-- The `ν`-th term of the `p`-central series of a generic kernel `F^(n)/F^(n)(ν)` is trivial,
because it is the image of `F^(n)(ν) = ker (F^(n) ↠ F^(n)/F^(n)(ν))`. -/
lemma ssg_pCentralSeries_freePQuotient_self (p n ν : ℕ) :
    Work.Shrinking.pCentralSeries p (Work.ProP.FreePQuotient p n ν) ν = ⊥ := by
  rw [← Work.Shrinking.map_pCentralSeries_surjective p (Work.ProP.freePQuotientMk p n ν)
      (Work.ProP.freePQuotientMk_surjective p n ν) ν,
    Subgroup.map_eq_bot_iff, Work.ProP.freePQuotientMk_ker]

/-- The generator map `x_{a,g} ↦ Φ g (mk (of a'))`, where `a' : Fin n` is the index `a` when
`(a : ℕ) < n` and the value is `1` otherwise. -/
noncomputable def ssgGen (p n ν : ℕ) {G : Type*} [Group G]
    (Φ : G →* MulAut (Work.ProP.FreePQuotient p n ν)) (m : ℕ) :
    Fin m × G → Work.ProP.FreePQuotient p n ν :=
  fun x => if h : (x.1 : ℕ) < n then
      Φ x.2 (Work.ProP.freePQuotientMk p n ν (FreeGroup.of ⟨x.1, h⟩))
    else 1

/-- The homomorphism `F(m) →* F^(n)/F^(n)(ν)` underlying the wanted map, on the free
`G`-operator group (before descending to the flow quotient). -/
noncomputable def ssgLift (p n ν : ℕ) {G : Type*} [Group G]
    (Φ : G →* MulAut (Work.ProP.FreePQuotient p n ν)) (m : ℕ) :
    Work.Shrinking.freeOperatorGroup G m →* Work.ProP.FreePQuotient p n ν :=
  FreeGroup.lift (ssgGen p n ν Φ m)

lemma ssgLift_of (p n ν : ℕ) {G : Type*} [Group G]
    (Φ : G →* MulAut (Work.ProP.FreePQuotient p n ν)) (m : ℕ) (x : Fin m × G) :
    ssgLift p n ν Φ m (FreeGroup.of x) = ssgGen p n ν Φ m x :=
  FreeGroup.lift_apply_of

/-- `ssgLift` is surjective as soon as `n ≤ m`: the images of the generators `x_{a,1}` with
`a < n` are the images of the free generators of `F^(n)` under the projection `F^(n) ↠ F^(n)/F^(n)(ν)`,
which is surjective. -/
lemma ssgLift_surjective (p n ν : ℕ) {G : Type*} [Group G]
    (Φ : G →* MulAut (Work.ProP.FreePQuotient p n ν)) {m : ℕ} (hm : n ≤ m) :
    Function.Surjective (ssgLift p n ν Φ m) := by
  let ι : Fin n → Work.Shrinking.freeOperatorGroup G m :=
    fun a => FreeGroup.of ((⟨a.1, lt_of_lt_of_le a.2 hm⟩ : Fin m), (1 : G))
  let g : FreeGroup (Fin n) →* Work.Shrinking.freeOperatorGroup G m := FreeGroup.lift ι
  have hg_of : ∀ a : Fin n, g (FreeGroup.of a) = ι a := fun a => FreeGroup.lift_apply_of
  have hcomp : ∀ x : FreeGroup (Fin n),
      Work.ProP.freePQuotientMk p n ν x = ssgLift p n ν Φ m (g x) := by
    intro x
    induction x using FreeGroup.induction_on with
    | one => simp
    | of a =>
        rw [hg_of a, ssgLift_of]
        simp only [ssgGen]
        rw [dif_pos a.2, map_one, MulAut.one_apply]
    | inv_of a ih => simp [map_inv, ih]
    | mul a b iha ihb => simp [map_mul, iha, ihb]
  intro y
  obtain ⟨x, rfl⟩ := Work.ProP.freePQuotientMk_surjective p n ν y
  exact ⟨g x, (hcomp x).symm⟩

/-- `ssgLift` is `G`-equivariant: on generators `g • x_{a,h} = x_{a,gh}` and
`Φ (g * h) = Φ g * Φ h`. -/
lemma ssgLift_smul (p n ν : ℕ) {G : Type*} [Group G]
    (Φ : G →* MulAut (Work.ProP.FreePQuotient p n ν)) (m : ℕ) (g : G)
    (x : Work.Shrinking.freeOperatorGroup G m) :
    ssgLift p n ν Φ m (g • x) = Φ g (ssgLift p n ν Φ m x) := by
  have key : ∀ y : Fin m × G,
      ssgLift p n ν Φ m (g • FreeGroup.of y) = Φ g (ssgLift p n ν Φ m (FreeGroup.of y)) := by
    intro y
    rw [Work.Shrinking.smul_freeOperator_of, ssgLift_of, ssgLift_of]
    by_cases hy : (y.1 : ℕ) < n
    · simp only [ssgGen, dif_pos hy]
      rw [← MulAut.mul_apply, ← map_mul]
    · simp only [ssgGen, dif_neg hy, map_one]
  induction x using FreeGroup.induction_on with
  | one => simp
  | of y => exact key y
  | inv_of y ih =>
      simp only [Work.Shrinking.smul_freeOperatorGroup_eq] at ih ⊢
      simp only [map_inv, ih]
  | mul x y ihx ihy =>
      simp only [Work.Shrinking.smul_freeOperatorGroup_eq] at ihx ihy ⊢
      simp only [map_mul, ihx, ihy]

/-- `ssgLift` kills `pCentralSeries p F(m) ν`: the `p`-central series is functorial for surjective
homomorphisms, and its `ν`-th term vanishes in `F^(n)/F^(n)(ν)`. -/
lemma ssgLift_ker (p n ν : ℕ) {G : Type*} [Group G]
    (Φ : G →* MulAut (Work.ProP.FreePQuotient p n ν)) {m : ℕ} (hm : n ≤ m) :
    Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G m) ν
      ≤ (ssgLift p n ν Φ m).ker := by
  have h := Work.Shrinking.map_pCentralSeries_surjective p (ssgLift p n ν Φ m)
    (ssgLift_surjective p n ν Φ hm) ν
  rw [ssg_pCentralSeries_freePQuotient_self] at h
  exact (Subgroup.map_eq_bot_iff _).mp h

/-- `flowAction` on a class of the flow quotient is the descended automorphism `quotAut`: it acts
on `mk x` by `mk (subAut x)`. -/
lemma ssg_flowAction_mk (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) (g : G)
    (x : (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) :
    flowAction p G m i j g ((QuotientGroup.mk' ((flowTerm p G m i j).subgroupOf ⊤)) x)
      = (QuotientGroup.mk' ((flowTerm p G m i j).subgroupOf ⊤))
          (Work.Shrinking.subAut (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)) g
            (Subgroup.map_top_of_surjective _
              (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g).surjective)
            x) := by
  rw [show flowAction p G m i j g
      = Work.Shrinking.quotAut (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))
          (flowTerm p G m i j) g
          (Subgroup.map_top_of_surjective _
            (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g).surjective)
          (Work.CohomologicalShrinking.map_refinedTerm_eq p
            (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g) i j) from rfl]
  rw [Work.Shrinking.quotAut_mk]

/-- The underlying element of `subAut H g h x` is `g • x` (for any invariance proof `h`). -/
lemma ssg_subAut_coe_smul {G P : Type*} [Group G] [Group P] [MulDistribMulAction G P]
    (H : Subgroup P) (g : G)
    (h : H.map (MulEquiv.toMonoidHom (MulDistribMulAction.toMulAut G P g)) = H) (x : ↥H) :
    ((Work.Shrinking.subAut H g h x : ↥H) : P) = g • (x : P) := by
  rw [Work.Shrinking.subAut_coe]
  rfl

end Aux

/-!
An equivariant surjection from the flow quotient `F(m)/F(m)^{(ν+1,1)}` (with `m := max n 1`) onto
the generic kernel `P := FreePQuotient p n ν`, compatible with the canonical `G`-action on the free
`G`-operator group on the left and the given action `Φ` on the right.

Note `refinedTerm p · (ν+1) 1 = pCentralSeries p · ν`, so the left-hand side is
`freeOperatorGroup G (max n 1) ⧸ pCentralSeries p · ν` (with `freeOperatorGroup G m = FreeGroup (Fin m × G)`),
while the right-hand side is `FreeGroup (Fin n) ⧸ pCentralSeries p · ν`.

Suggested route: on generators use `FreeGroup.lift` with
`x_{a,g} ↦ Φ g (freePQuotientMk p n ν (FreeGroup.of a'))` where `a' : Fin n` corresponds to
`a : Fin (max n 1)` when `(a : ℕ) < n` and the value is `1` otherwise.  Surjectivity follows from
`freePQuotientMk_surjective` (the generators `x_{a,1}` hit the images of the free generators; for
`n = 0` both sides are trivial).  The map kills `pCentralSeries p (FreeGroup (Fin (max n 1) × G)) ν`
because it is surjective and `pCentralSeries p (FreePQuotient p n ν) ν = ⊥`
(`Work.Shrinking.map_pCentralSeries_surjective` with the quotient projection), so it descends along
`QuotientGroup.lift` to the subquotient `flowQuotient` (modelled as
`⊤ ⧸ (flowTerm p G m (ν+1) 1).subgroupOf ⊤`).  Equivariance is checked on generators, using
`Work.Shrinking.smul_freeOperator_of` (`g • FreeGroup.of (a,h) = FreeGroup.of (a, g*h)`) and
`Work.Shrinking.quotAut_mk`/`quotActionHom` for the descended action `flowAction`.
-/
theorem equivariant_flowQuotient_surjection
    {G : Type*} [Group G] {p n ν : ℕ} [Fact p.Prime]
    (Φ : G →* MulAut (Work.ProP.FreePQuotient p n ν)) :
    ∃ f : Work.CohomologicalShrinking.flowQuotient p G (max n 1) (ν + 1) 1 →*
        Work.ProP.FreePQuotient p n ν,
      Function.Surjective f ∧
      ∀ (g : G) (y : Work.CohomologicalShrinking.flowQuotient p G (max n 1) (ν + 1) 1),
        f (Work.CohomologicalShrinking.flowAction p G (max n 1) (ν + 1) 1 g y) = Φ g (f y) := by
  classical
  have hψsurj : Function.Surjective (ssgLift p n ν Φ (max n 1)) :=
    ssgLift_surjective p n ν Φ (le_max_left n 1)
  have hψker : Work.Shrinking.pCentralSeries p
      (Work.Shrinking.freeOperatorGroup G (max n 1)) ν
      ≤ (ssgLift p n ν Φ (max n 1)).ker :=
    ssgLift_ker p n ν Φ (le_max_left n 1)
  have hker : ((flowTerm p G (max n 1) (ν + 1) 1).subgroupOf
        (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G (max n 1))))
      ≤ ((ssgLift p n ν Φ (max n 1)).comp
          (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G (max n 1))).subtype).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    refine hψker ?_
    rw [Subgroup.mem_subgroupOf] at hx
    rwa [ssg_flowTerm_succ_one] at hx
  let f : Work.CohomologicalShrinking.flowQuotient p G (max n 1) (ν + 1) 1 →*
      Work.ProP.FreePQuotient p n ν :=
    QuotientGroup.lift
      ((flowTerm p G (max n 1) (ν + 1) 1).subgroupOf
        (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G (max n 1))))
      ((ssgLift p n ν Φ (max n 1)).comp
        (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G (max n 1))).subtype) hker
  have hfmk : ∀ y : (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G (max n 1))),
      f ((QuotientGroup.mk' ((flowTerm p G (max n 1) (ν + 1) 1).subgroupOf
        (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G (max n 1))))) y)
        = ssgLift p n ν Φ (max n 1) (y : Work.Shrinking.freeOperatorGroup G (max n 1)) := by
    intro y
    show (QuotientGroup.lift _ ((ssgLift p n ν Φ (max n 1)).comp
        (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G (max n 1))).subtype) hker)
          (QuotientGroup.mk' _ y) = _
    rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk']
    rfl
  refine ⟨f, ?_, ?_⟩
  · intro y
    obtain ⟨z, hz⟩ := hψsurj y
    refine ⟨QuotientGroup.mk' _ ⟨z, Subgroup.mem_top z⟩, ?_⟩
    rw [hfmk]
    exact hz
  · intro g y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      ((flowTerm p G (max n 1) (ν + 1) 1).subgroupOf
        (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G (max n 1)))) y
    rw [ssg_flowAction_mk, hfmk, hfmk, ssg_subAut_coe_smul]
    exact ssgLift_smul p n ν Φ (max n 1) g ↑x

end Work.SSGRoute
