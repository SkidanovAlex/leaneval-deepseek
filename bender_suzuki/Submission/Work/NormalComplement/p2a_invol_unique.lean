import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3Sub.prop3b_support
import Submission.Work.ThreePoints.chIIFourP3Subnormal
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThreePoints.Basic
import Submission.Work.NormalComplement.sec5_setup_invol

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- An element `u ∈ H` of order `2` centralising `V = centD H t` is an involution of the subgroup
`H ⊓ C_G(V)`, i.e. a member of `involutions ((H ⊓ C_G(V)) : Set G)`. -/
private lemma mem_involutions_inf_centralizer {G : Type} [Group G] {H : Subgroup G} {t : G} {u : G}
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    u ∈ Submission.Blueprint.involutions
      ((H ⊓ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) : Subgroup G) : Set G) :=
  ⟨Subgroup.mem_inf.mpr ⟨hu.1, hu.2.2⟩, hu.2.1⟩

/-- The `ncard`-form and the `∃!`-form of "exactly one involution": a subgroup `K ≤ G` has exactly
one involution if and only if there is a unique `u ∈ K` of order `2`.  Downstream users of
`p2a_invol_unique` (which is stated in the `ncard`-form) can pass between the two forms with this
lemma. -/
lemma ncard_involutions_eq_one_iff {G : Type} [Group G] (K : Subgroup G) :
    (Submission.Blueprint.involutions (K : Set G)).ncard = 1 ↔
      ∃! u : G, u ∈ K ∧ orderOf u = 2 := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := Set.ncard_eq_one.mp h
    -- `u` itself is an involution of `K`, and every other one equals `u`.
    have hu1 : u ∈ K ∧ orderOf u = 2 := by
      have hmem : u ∈ Submission.Blueprint.involutions (K : Set G) := by
        rw [hu]; exact Set.mem_singleton u
      rw [Submission.Blueprint.involutions, Set.mem_ofPred_eq] at hmem
      exact hmem
    refine ⟨u, hu1, fun v hv => ?_⟩
    have hvs : v ∈ Submission.Blueprint.involutions (K : Set G) := by
      rw [Submission.Blueprint.involutions, Set.mem_ofPred_eq]
      exact hv
    rw [hu] at hvs
    exact Set.mem_singleton_iff.mp hvs
  · rintro ⟨u, hu, huniq⟩
    have hsub : Submission.Blueprint.involutions (K : Set G) = {u} := by
      ext v
      rw [Submission.Blueprint.involutions, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact ⟨fun hv => huniq v hv, fun hv => by rw [hv]; exact hu⟩
    rw [hsub, Set.ncard_singleton]

/-- **Peterfalvi I, Ch. III §5 (p. 184).** In the §5 configuration there is a *unique* involution
of `H` centralising `V = centD H t = C_D(t)`; equivalently, the set `Inv(H ⊓ C_G(V))` has
cardinality `1`.  This is the uniqueness of the involution denoted `u` in §5 (used, e.g., to know
that every involution of `H` centralising `V` is the special involution `u`).

Proof: `Work.NormalComplement.sec5_setup_invol` supplies the unique element `u`, and the target is
the `ncard`-formulation of that uniqueness. -/
theorem p2a_invol_unique (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    (Submission.Blueprint.involutions
      ((H ⊓ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) : Subgroup G) : Set G)).ncard = 1 := by
  obtain ⟨u, hu, huniq⟩ := sec5_setup_invol hFT hC4 hP3 h
  have hset : Submission.Blueprint.involutions
      ((H ⊓ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) : Subgroup G) : Set G)
      = {u} := by
    ext x
    rw [Submission.Blueprint.involutions, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hx2⟩
      obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
      exact huniq x ⟨hxH, hx2, hxC⟩
    · rintro rfl
      exact mem_involutions_inf_centralizer hu
  rw [hset, Set.ncard_singleton]

end Work.NormalComplement
