import Mathlib
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup
import Submission.Work.ThreePoints.S4Prop2.even_card_normalizer_of_maximal_p_subgroup_gen
import Submission.Work.ThreePoints.three_involutions_even
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup_unconditional
import Submission.Work.DoubleTransitivity.App2.app2_2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.EvenCardSource

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open scoped Pointwise

/-- **Peterfalvi I Ch. I §3 Prop. 1, Case 2, without Brauer–Suzuki.**  Transcribed from
`Work.ThreePoints.S4Prop2.sec3_prop1_case2`, with its two Brauer–Suzuki lines
(`Work.ThreePoints.involution_commutator_mem_oddCore` and the ensuing `oddCore` bookkeeping)
replaced by the single application of `Work.ThreePoints.three_involutions_even` that is carried out
verbatim in the `¬ HasFourGroup` branch of
`Work.ThreePoints.sec3_prop1_transitive_unconditional`.

`K` is strongly embedded in the finite group `G` (`Ω = G ⧸ K`), `p` a prime, `Q` maximal among the
`p`-subgroups of `G` with at least three fixed points of `Ω`, `N_G(Q)` has `2`-rank `1`, and
`m₁, m₂ ∈ N_G(Q)` move a fixed point `ω₀` of `Q` to two distinct other points.  Then some fixed
point of `Q` has `|N_G(Q) ⊓ Stab_G(ω)|` even. -/
theorem sec3_prop1_case2_uncond {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K)
    {p : ℕ} (hp : p.Prime) {Q : Subgroup G} (hQp : IsPGroup p Q)
    (hQmax : ∀ R : Subgroup G, Q ≤ R → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q)
    (hB : ¬ Submission.Blueprint.HasFourGroup (Subgroup.normalizer (Q : Set G)))
    {ω₀ : G ⧸ K} (hω₀ : ω₀ ∈ Submission.Blueprint.fixedPts K Q)
    {m₁ m₂ : G} (hm₁ : m₁ ∈ Subgroup.normalizer (Q : Set G))
    (hm₂ : m₂ ∈ Subgroup.normalizer (Q : Set G))
    (hne₁ : m₁ • ω₀ ≠ ω₀) (hne₂ : m₂ • ω₀ ≠ ω₀) (hne₁₂ : m₂ • ω₀ ≠ m₁ • ω₀) :
    ∃ ω ∈ Submission.Blueprint.fixedPts K Q,
      Even (Nat.card (MulAction.stabilizer G ω ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set M : Subgroup G := Subgroup.normalizer (Q : Set G) with hMdef
  have hω₁ : m₁ • ω₀ ∈ fixedPts K Q :=
    Work.DoubleTransitivity.App2.smul_mem_fixedBySub_of_mem_normalizer hm₁ hω₀
  have hω₂ : m₂ • ω₀ ∈ fixedPts K Q :=
    Work.DoubleTransitivity.App2.smul_mem_fixedBySub_of_mem_normalizer hm₂ hω₀
  obtain ⟨t₁, ht₁M, ht₁2, ht₁⟩ :=
    Work.ThreePoints.sec3_lemma3 hK hp hQp hQmax hω₀ hω₁ hne₁.symm ⟨m₁, hm₁, rfl⟩
  obtain ⟨t₂, ht₂M, ht₂2, ht₂⟩ :=
    Work.ThreePoints.sec3_lemma3 hK hp hQp hQmax hω₀ hω₂ hne₂.symm ⟨m₂, hm₂, rfl⟩
  have ht₁sq : t₁ * t₁ = 1 := Work.ThreePoints.mul_self_eq_one_of_orderOf_eq_two ht₁2
  have ht₂sq : t₂ * t₂ = 1 := Work.ThreePoints.mul_self_eq_one_of_orderOf_eq_two ht₂2
  have hprodM : t₁ * t₂ ∈ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normalizer (Q : Set G)).mul_mem ht₁M ht₂M
  have hω' : (t₁ * t₂) • ω₀ ∈ fixedPts K Q :=
    Work.DoubleTransitivity.App2.smul_mem_fixedBySub_of_mem_normalizer hprodM hω₀
  have hne' : ω₀ ≠ (t₁ * t₂) • ω₀ := by
    intro hcon
    have h1 : t₁ • ((t₁ * t₂) • ω₀) = m₂ • ω₀ := by
      rw [mul_smul, ← mul_smul, ht₁sq, one_smul, ht₂]
    have h2 : t₁ • ω₀ = t₁ • ((t₁ * t₂) • ω₀) := congrArg (fun y => t₁ • y) hcon
    exact hne₁₂ (ht₁.symm.trans (h2.trans h1)).symm
  obtain ⟨t, htM, ht2, ht⟩ :=
    Work.ThreePoints.sec3_lemma3 hK hp hQp hQmax hω₀ hω' hne' ⟨t₁ * t₂, hprodM, rfl⟩
  have htsq : t * t = 1 := Work.ThreePoints.mul_self_eq_one_of_orderOf_eq_two ht2
  have hxmem : t₂ * t₁ * t ∈ M := M.mul_mem (M.mul_mem ht₂M ht₁M) htM
  have hxfix : (t₂ * t₁ * t) • ω₀ = ω₀ := by
    rw [mul_smul, mul_smul, ht, mul_smul]
    have h1 : t₁ • (t₁ • (t₂ • ω₀)) = t₂ • ω₀ := by
      rw [← mul_smul, ht₁sq, one_smul]
    rw [h1, ← mul_smul, ht₂sq, one_smul]
  refine ⟨ω₀, hω₀, ?_⟩
  refine even_iff_two_dvd.mpr ?_
  have hmem : (t₂ * t₁ * t) ∈ (MulAction.stabilizer G ω₀ ⊓ M : Subgroup G) :=
    ⟨MulAction.mem_stabilizer_iff.mpr hxfix, hxmem⟩
  set t₁' : M := ⟨t₁, ht₁M⟩
  set t₂' : M := ⟨t₂, ht₂M⟩
  set t' : M := ⟨t, htM⟩
  have ht₁2' : orderOf t₁' = 2 := by rw [← Subgroup.orderOf_coe t₁']; exact ht₁2
  have ht₂2' : orderOf t₂' = 2 := by rw [← Subgroup.orderOf_coe t₂']; exact ht₂2
  have ht2' : orderOf t' = 2 := by rw [← Subgroup.orderOf_coe t']; exact ht2
  -- the two involutions `t₁`, `t₂` are distinct, since they move `ω₀` to distinct points
  have hne₂₁ : t₂' ≠ t₁' := by
    intro heq
    refine hne' ?_
    have hw : (t₁' * t₂' : M) = 1 := by
      rw [heq, Work.ThreePoints.mul_self_eq_one_of_orderOf_eq_two ht₁2']
    have hcoe : ((t₁' * t₂' : M) : G) = t₁ * t₂ := rfl
    rw [hw] at hcoe
    rw [← hcoe]
    simp
  have hxeven : Even (orderOf (t₂' * t₁' * t')) :=
    Work.ThreePoints.three_involutions_even hB ht₂2' ht₁2' ht2' hne₂₁
  have hxevenG : Even (orderOf (t₂ * t₁ * t)) := by
    have hcoee : (((t₂' * t₁' * t') : M) : G) = t₂ * t₁ * t := rfl
    rw [← hcoee, Subgroup.orderOf_coe]
    exact hxeven
  refine dvd_trans (even_iff_two_dvd.mp hxevenG) ?_
  have hord : orderOf (⟨t₂ * t₁ * t, hmem⟩ :
      ↥(MulAction.stabilizer G ω₀ ⊓ M : Subgroup G)) = orderOf (t₂ * t₁ * t) :=
    Subgroup.orderOf_mk _ _
  rw [← hord]
  exact orderOf_dvd_natCard _

/-- **Peterfalvi I Ch. I §3 Prop. 1 (p. 154), existence form, with the Brauer–Suzuki hypothesis
replaced by `Work.ThreePoints.three_involutions_even`.**

`K` is a strongly embedded subgroup of the finite group `G` (`Ω = G ⧸ K`), `p ≠ 2` is a prime and
`Q` is maximal among the `p`-subgroups of `G` with at least three fixed points of `Ω`.  Conclusion:
some fixed point `ω` of `Q` has `|N_G(Q) ⊓ Stab_G(ω)|` even.

This is exactly the statement of `Work.ThreePoints.S4Prop2.sec3_prop1_exists` with its hypothesis
`hBrSz : Submission.Blueprint.BrauerSuzukiProp` removed.  Route: transcribe the proof of
`Work.ThreePoints.S4Prop2.sec3_prop1_exists` (it splits on `HasFourGroup (N_G(Q))`; the
`HasFourGroup` branch is Brauer–Suzuki-free).  In the `¬ HasFourGroup (N_G(Q))` branch, split on

    ∃ ω₀ ∈ fixedPts K Q, ∃ m₁ ∈ N_G(Q), ∃ m₂ ∈ N_G(Q),
      m₁ • ω₀ ≠ ω₀ ∧ m₂ • ω₀ ≠ ω₀ ∧ m₂ • ω₀ ≠ m₁ • ω₀.

* If this fails, use `sec3_prop1_case1` in the same file (Brauer–Suzuki-free, verbatim available).
* If it holds, use `sec3_prop1_case2` in the same file, **but** with its two Brauer–Suzuki lines
  (the invocation of `Work.ThreePoints.involution_commutator_mem_oddCore hBrSz hB ht₂2' ht₁2'` and
  the `oddCore` bookkeeping that follows it) replaced by a single application of
  `Work.ThreePoints.three_involutions_even hB ht₂2' ht₁2' ht2' hne₂₁`, where `t₁, t₂, t` are the
  three involutions produced by `Work.ThreePoints.sec3_lemma3` and `hne₂₁ : t₂' ≠ t₁'` follows from
  `hne₁₂` (the elements `t₁, t₂` move `ω₀` to distinct points).  The replacement is carried out
  verbatim in the `¬ HasFourGroup` branch of `Work.ThreePoints.sec3_prop1_transitive_unconditional`
  (`Submission/Work/ThreePoints/even_card_normalizer_of_maximal_p_subgroup_unconditional.lean`),
  which is the same computation; copy that pattern.

Do NOT call `Work.ThreePoints.S4Prop2.sec3_prop1_exists` or `Work.ThreePoints.S4Prop2.sec3_prop1_case2`
themselves (their file `Submission/Work/ThreePoints/S4Prop2/even_card_normalizer_of_maximal_p_subgroup_gen.lean`
contains a `hole`); transcribe their proof text.  Do not use
`Work.ThreePoints.brauerSuzukiProp_from_cases`, `Work.ThreePoints.involution_commutator_mem_oddCore`
or anything from `Submission/Work/BrauerSuzuki/Q8/` (resp. `Q8U/`, `Arith/`) that contains a `hole`:
the *only* input about groups of `2`-rank `1` is `Work.ThreePoints.three_involutions_even`. -/
theorem sec3_prop1_exists_uncond {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : Subgroup G} (hQp : IsPGroup p Q) (hQ3 : 3 ≤ (Submission.Blueprint.fixedPts K Q).ncard)
    (hQmax : ∀ R : Subgroup G, Q ≤ R → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q) :
    ∃ ω ∈ Submission.Blueprint.fixedPts K Q,
      Even (Nat.card (MulAction.stabilizer G ω ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set M : Subgroup G := Subgroup.normalizer (Q : Set G) with hMdef
  have hQodd : Odd (Nat.card ↥Q) := by
    rw [← Nat.not_even_iff_odd]
    intro hev
    haveI : Fintype ↥Q := Fintype.ofFinite ↥Q
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥Q) 2
      (by rw [← Nat.card_eq_fintype_card]; exact even_iff_two_dvd.mp hev)
    obtain ⟨n, hn⟩ := hQp x
    have hxG : orderOf ((x : Q) : G) = 2 := (Subgroup.orderOf_coe x).trans hx
    have h2dvd : 2 ∣ p ^ n := by
      rw [← hxG]
      exact orderOf_dvd_of_pow_eq_one (by simpa using congrArg (fun y : Q => (y : G)) hn)
    have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2dvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  by_cases h4 : HasFourGroup M
  · -- Case A: `N_G(Q)` has `2`-rank `≥ 2`
    obtain ⟨t, ht2⟩ : ∃ t : M, orderOf t = 2 := by
      obtain ⟨t, -, ht2, -, -, -⟩ := h4
      exact ⟨t, ht2⟩
    have htG : orderOf ((t : G)) = 2 := (Subgroup.orderOf_coe t).trans ht2
    obtain ⟨ω, hωfix, -⟩ := Work.ThreePoints.existsUnique_fixedPts_of_orderOf_eq_two hK htG
    have hle : Q ≤ MulAction.stabilizer G ω :=
      Work.ThreePoints.le_stabilizer_of_involution_mem_normalizer hK hQodd h4 ⟨t.2, htG⟩ hωfix
    refine ⟨ω, Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mpr hle, ?_⟩
    have hmem : (t : G) ∈ (MulAction.stabilizer G ω ⊓ M : Subgroup G) :=
      ⟨MulAction.mem_stabilizer_iff.mpr hωfix, t.2⟩
    refine even_iff_two_dvd.mpr ?_
    have hord : orderOf (⟨(t : G), hmem⟩ :
        ↥(MulAction.stabilizer G ω ⊓ M : Subgroup G)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact htG
    exact dvd_trans (by rw [hord]) (orderOf_dvd_natCard _)
  · -- Case B: `N_G(Q)` has `2`-rank `1`
    have hB : ¬ HasFourGroup M := h4
    have hΩne : (fixedPts K Q).Nonempty := by rw [← Set.ncard_pos]; omega
    by_cases hbig : ∃ ω₀ ∈ fixedPts K Q, ∃ m₁ ∈ M, ∃ m₂ ∈ M,
        m₁ • ω₀ ≠ ω₀ ∧ m₂ • ω₀ ≠ ω₀ ∧ m₂ • ω₀ ≠ m₁ • ω₀
    · obtain ⟨ω₀, hω₀, m₁, hm₁, m₂, hm₂, hne₁, hne₂, hne₁₂⟩ := hbig
      exact sec3_prop1_case2_uncond hK hp hQp hQmax hB hω₀ hm₁ hm₂ hne₁ hne₂ hne₁₂
    · exfalso
      -- two different points of `Ω_Q` in different `M`-orbits
      have htwo : ∃ ω₁ ∈ fixedPts K Q, ∃ ω₂ ∈ fixedPts K Q,
          ¬ ∃ m ∈ M, m • ω₁ = ω₂ := by
        by_contra hcon
        push_neg at hcon
        obtain ⟨ω₁, hω₁⟩ := hΩne
        obtain ⟨x, hx, hxne⟩ :=
          Set.exists_ne_of_one_lt_ncard (by omega : 1 < (fixedPts K Q).ncard) ω₁
        have h2 : 1 < ((fixedPts K Q) \ {ω₁}).ncard := by
          have h1 := Set.ncard_sdiff_singleton_add_one hω₁
          omega
        obtain ⟨y, hy, hyne⟩ := Set.exists_ne_of_one_lt_ncard h2 x
        obtain ⟨mx, hmx, hmx'⟩ := hcon ω₁ hω₁ x hx
        obtain ⟨my, hmy, hmy'⟩ := hcon ω₁ hω₁ y hy.1
        have hxne' : mx • ω₁ ≠ ω₁ := by rw [hmx']; exact hxne
        have hyne' : my • ω₁ ≠ ω₁ := by rw [hmy']; exact hy.2
        have hEq : mx • ω₁ = my • ω₁ := by
          by_contra hc
          exact hbig ⟨ω₁, hω₁, mx, hmx, my, hmy, hxne', hyne', fun h => hc h.symm⟩
        exact hyne (by rw [← hmx', ← hmy', hEq.symm])
      obtain ⟨ω₁, hω₁, ω₂, hω₂, hnot⟩ := htwo
      have h2 : 1 < ((fixedPts K Q) \ {ω₁}).ncard := by
        have h1 := Set.ncard_sdiff_singleton_add_one hω₁
        omega
      obtain ⟨ω₃, hω₃, hω₃ne⟩ := Set.exists_ne_of_one_lt_ncard h2 ω₂
      exact Work.ThreePoints.S4Prop2.sec3_prop1_case1 hK hp hp2 hQp hQmax hbig
        hω₁ hω₂ hω₃.1 hnot hω₃.2 hω₃ne

end Work.ThreePoints.EvenCardSource
