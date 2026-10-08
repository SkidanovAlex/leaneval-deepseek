import Mathlib
import Submission.Work.DoubleTransitivity.Sec4.Defs
import Submission.Work.DoubleTransitivity.Sec3.prop1
import Submission.Work.DoubleTransitivity.App2.app2_3
import Submission.Work.DoubleTransitivity.App2.app2_4
import Submission.Work.DoubleTransitivity.Sec2.prop2
import Submission.Work.DoubleTransitivity.Sec1.unique_fixed
import Submission.Work.DoubleTransitivity.Sec1.normalizer_eq
import Submission.Work.DoubleTransitivity.App1.isSylowSubgroupOf_map_subtype

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec4.prop1` — Peterfalvi I, Ch. I §4 Proposition 1 (a) (p. 156)

Let `H` be a strongly embedded subgroup of a finite group `G` (so `Ω = G ⧸ H` is the class of
conjugates of `H`, acted on by left translation), and `p` an odd prime.  The source's
Proposition 1 (a) reads:

> If `𝓡_p = ∅`, then `G` acts doubly transitively on `Ω`.

Here `𝓡_p = ∅` is replaced by the (stronger, but exactly what the later chapters use) hypothesis
`hRp` of this lemma: for every involution `t ∉ H` and every `p`-Sylow `P` of the two-point
stabiliser `D = H ∩ H^t`, `P` does not fix three points of `Ω`.

Since `P ≤ H ⊓ conj t H`, `P` fixes both `pt H` and `mk t`, which are distinct because
`t ∉ H`; `hRp` then says that these are *all* the fixed points of `P`.  So every pair
`{pt H, c}` (`c ≠ pt H`) is the fixed-point set of a `p`-subgroup, and Peterfalvi's Appendix II
(3) (`Work.DoubleTransitivity.App2.app2_3`, which needs no smallness hypothesis on `Ω`) gives
double transitivity.

The two inputs about the coset structure of `Ω`:

* `involution_rep`: every point `mk x` with `x ∉ H` is `mk t` for an involution `t ∉ H` (the
  source's §2 Prop. 1 (c): the number of involutions `u` with `H^u = H'` is `n = |Inv(H)| ≥ 1`).
* `fixedPts_sylow_twoPoint`: the fixed points of a `p`-Sylow of `H ⊓ H^t` are exactly
  `{pt H, mk t}`.
-/

set_option linter.unusedVariables false

namespace Work.DoubleTransitivity.Sec4

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-! ## The involution representing a point of `Ω` outside `H` -/

/-- **Peterfalvi I §2 Prop. 1 (c), existence half.**  Every coset of `H` other than `H` itself
contains an involution: for `x ∉ H` there is an involution `t ∉ H` with
`conj t H = conj x H` (equivalently `t ∈ xH`, i.e. `mk t = mk x`).

Proof.  Let `s ∈ H` be an involution (Cauchy, `2 ∣ |H|`) and `u = x s x⁻¹`, an involution of
`conj x H`.  The two have no common fixed point of `Ω` (they fix `pt H` and `mk x`, which are
distinct), so Peterfalvi I §2 Prop. 1 (a) (`Sec2.prop1a_exists`) gives an involution `w` with
`w⁻¹ s w = u`.  Then `u ∈ conj w⁻¹ H` as well, so by uniqueness of the fixed point of `u`
(`Sec1.eq_of_smul_eq_of_orderOf_eq_two`) the points `mk w⁻¹` and `mk x` coincide, and equal
points have equal stabilisers: `conj w⁻¹ H = conj x H`. -/
theorem involution_rep {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {x : G} (hx : x ∉ H) :
    ∃ t : G, orderOf t = 2 ∧ t ∉ H ∧ conj t H = conj x H := by
  classical
  have hB : IsBender H := (isStronglyEmbedded_iff H).mp hH |>.2
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 2 hB.1
  have hs2 : orderOf ((s : ↥H) : G) = 2 := (Subgroup.orderOf_coe s).trans hs
  set u : G := x * ((s : ↥H) : G) * x⁻¹ with hu
  have hu2 : orderOf u = 2 := by
    rw [hu]
    simpa [MulAut.conj_apply, hs2] using MulEquiv.orderOf_eq (MulAut.conj x) ((s : ↥H) : G)
  have hu_mem : u ∈ conj x H := by
    refine Subgroup.mem_map.mpr ⟨((s : ↥H) : G), s.2, ?_⟩
    rw [hu]
    rfl
  have hfix_u : u • (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk x :=
    smul_mk_eq_mk_iff.mpr hu_mem
  have hfix_s : ((s : ↥H) : G) • (pt H) = pt H := by
    rw [smul_pt]
    exact mk_one_eq_iff.mpr s.2
  have hno : ¬ ∃ ω : G ⧸ H, ((s : ↥H) : G) • ω = ω ∧ u • ω = ω := by
    rintro ⟨ω, hωs, hωu⟩
    have h1 : ω = (QuotientGroup.mk x : G ⧸ H) :=
      Sec1.eq_of_smul_eq_of_orderOf_eq_two hB hu2 hωu hfix_u
    have h2 : ω = pt H :=
      Sec1.eq_of_smul_eq_of_orderOf_eq_two hB hs2 hωs hfix_s
    exact hx (mk_one_eq_iff.mp (h1.symm.trans h2))
  obtain ⟨w, hw2, hwconj, -, -⟩ := Sec2.prop1a_exists hB hs2 hu2 hno
  have hu_mem2 : u ∈ conj w⁻¹ H := by
    rw [mem_conj]
    have h : w⁻¹⁻¹ * u * w⁻¹ = ((s : ↥H) : G) := by
      rw [inv_inv, ← hwconj]
      group
    rw [h]
    exact s.2
  have hfix_u2 : u • (QuotientGroup.mk w⁻¹ : G ⧸ H) = QuotientGroup.mk w⁻¹ :=
    smul_mk_eq_mk_iff.mpr hu_mem2
  have heq : (QuotientGroup.mk w⁻¹ : G ⧸ H) = (QuotientGroup.mk x : G ⧸ H) :=
    Sec1.eq_of_smul_eq_of_orderOf_eq_two hB hu2 hfix_u2 hfix_u
  have hconj : conj w⁻¹ H = conj x H := by
    ext g
    rw [mem_conj_iff_smul_fixed, mem_conj_iff_smul_fixed, heq]
  refine ⟨w⁻¹, ?_, ?_, hconj⟩
  · rw [orderOf_inv, hw2]
  · intro hwH
    exact hx (mk_one_eq_iff.mp (heq.symm.trans (mk_one_eq_iff.mpr hwH)))

/-- A point of `Ω = G ⧸ H` is determined by its stabiliser: `conj g H = conj g' H` implies
`gH = g'H` (equivalently `N_G(H) = H`, `Sec1.normalizer_eq`). -/
theorem mk_eq_of_conj_eq {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {g g' : G}
    (h : conj g H = conj g' H) :
    (QuotientGroup.mk g : G ⧸ H) = (QuotientGroup.mk g' : G ⧸ H) := by
  have hB : IsBender H := (isStronglyEmbedded_iff H).mp hH |>.2
  have hnorm : Subgroup.normalizer (H : Set G) = H := Sec1.normalizer_eq hB
  have h1 : conj (g'⁻¹ * g) H = H := by
    have h2 := congrArg (conj g'⁻¹) h
    rwa [← conj_mul, conj_inv_conj] at h2
  have h2 : g'⁻¹ * g ∈ H := by
    rw [← hnorm]
    exact (conj_eq_self_iff_mem_normalizer (g'⁻¹ * g) H).mp h1
  rw [mk_eq_mk_iff]
  simpa [mul_inv_rev] using H.inv_mem h2

/-! ## The fixed points of a `p`-Sylow of a two-point stabiliser -/

/-- Under the hypothesis `hRp` of Ch. I §4 Prop. 1, a `p`-Sylow `P` of the two-point stabiliser
`H ⊓ conj t H` (`t ∉ H` an involution) has exactly the two fixed points `pt H` and `mk t`: it
fixes both, and `hRp` forbids a third. -/
theorem fixedPts_sylow_twoPoint {G : Type} [Group G] [Finite G] {H : Subgroup G} {p : ℕ}
    (hRp : ∀ (t : G) (P : Subgroup G), orderOf t = 2 → t ∉ H →
      IsSylowSubgroupOf p P (Submission.Blueprint.twoPoint H t) →
      ¬ FixesThree H P)
    {t : G} (ht : orderOf t = 2) (htH : t ∉ H) {P : Subgroup G}
    (hP : IsSylowSubgroupOf p P (Submission.Blueprint.twoPoint H t)) :
    Submission.Blueprint.fixedPts H P =
      ({(pt H : G ⧸ H), (QuotientGroup.mk t : G ⧸ H)} : Set (G ⧸ H)) := by
  have hle : P ≤ H ⊓ conj t H := hP.1
  have hPH : P ≤ H := hle.trans inf_le_left
  have hPt : P ≤ conj t H := hle.trans inf_le_right
  have hmem1 : (pt H : G ⧸ H) ∈ Submission.Blueprint.fixedPts H P :=
    (pt_mem_fixedPts_iff P H).mpr hPH
  have hmem2 : (QuotientGroup.mk t : G ⧸ H) ∈ Submission.Blueprint.fixedPts H P :=
    (mk_mem_fixedPts_iff P H t).mpr hPt
  have hne : (QuotientGroup.mk t : G ⧸ H) ≠ pt H := by
    intro h
    exact htH (mk_one_eq_iff.mp h)
  have hsub : ({(pt H : G ⧸ H), (QuotientGroup.mk t : G ⧸ H)} : Set (G ⧸ H)) ⊆
      Submission.Blueprint.fixedPts H P := by
    intro ω hω
    rcases hω with h | h
    · rw [h]; exact hmem1
    · rw [h]; exact hmem2
  have hlt : (Submission.Blueprint.fixedPts H P).ncard < 3 := by
    have h := hRp t P ht htH hP
    simp only [FixesThree, not_le] at h
    exact h
  have hpair : (({(pt H : G ⧸ H), (QuotientGroup.mk t : G ⧸ H)} : Set (G ⧸ H))).ncard = 2 :=
    Set.ncard_pair hne.symm
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hpair]; omega)).symm

/-! ## Peterfalvi I, Ch. I §4 Proposition 1 (a) -/

theorem prop1 {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hRp : ∀ (t : G) (P : Subgroup G), orderOf t = 2 → t ∉ H →
      IsSylowSubgroupOf p P (Submission.Blueprint.twoPoint H t) →
      ¬ Work.DoubleTransitivity.FixesThree H P) :
    Submission.Blueprint.IsTwoTransitiveOn H := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hne : H ≠ ⊤ := hH.1
  -- It suffices (Appendix II (3)) that every pair `{pt H, c}` is the fixed point set of a
  -- `p`-subgroup of `G`, and that `G` does not fix `pt H`.
  refine App2.app2_3 (X := G) (E := G ⧸ H) (p := p) (a := pt H) ?_ ?_
  · intro c hc
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    have hx : x ∉ H := fun h => hc (mk_one_eq_iff.mpr h)
    -- an involution `t ∉ H` with `conj t H = conj x H`, hence `mk t = mk x`
    obtain ⟨t, ht2, htH, hconj⟩ := involution_rep hH hx
    have hmt : (QuotientGroup.mk t : G ⧸ H) = (QuotientGroup.mk x : G ⧸ H) :=
      mk_eq_of_conj_eq hH hconj
    -- a `p`-Sylow of `H ⊓ conj t H = Stab(pt H) ⊓ Stab(mk x)`
    obtain ⟨S⟩ : Nonempty (Sylow p ↥(Submission.Blueprint.twoPoint H t)) := Sylow.nonempty
    set P : Subgroup G := (S : Subgroup ↥(Submission.Blueprint.twoPoint H t)).map
      (Submission.Blueprint.twoPoint H t).subtype with hPdef
    have hPsyl : IsSylowSubgroupOf p P (Submission.Blueprint.twoPoint H t) :=
      App1.isSylowSubgroupOf_map_subtype hp S
    have hfx : Work.DoubleTransitivity.fixedBySub P =
        ({(pt H : G ⧸ H), (QuotientGroup.mk t : G ⧸ H)} : Set (G ⧸ H)) :=
      fixedPts_sylow_twoPoint hRp ht2 htH hPsyl
    refine ⟨P, hPsyl.isPGroup, ?_⟩
    rw [← hmt]
    exact hfx
  · -- `G` does not fix `pt H`, because `H ≠ ⊤`
    intro htriv
    obtain ⟨g, hg⟩ : ∃ g : G, g ∉ H := by
      by_contra h
      exact hne ((Subgroup.eq_top_iff' H).mpr fun x => by
        by_contra hx
        exact h (⟨x, hx⟩ : ∃ g : G, g ∉ H))
    have h1 : g • (pt H) = pt H := htriv g
    rw [smul_pt] at h1
    exact hg (mk_one_eq_iff.mp h1)

end Work.DoubleTransitivity.Sec4
