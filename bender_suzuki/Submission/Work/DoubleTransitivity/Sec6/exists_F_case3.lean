import Mathlib
import Submission.Work.DoubleTransitivity.Sec6.Defs
import Submission.Work.DoubleTransitivity.Sec6.step1
import Submission.Work.DoubleTransitivity.Sec6.coprime_generation
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.DoubleTransitivity.Action
import Submission.Work.DoubleTransitivity.Sec1.unique_fixed
import Submission.Work.DoubleTransitivity.Sec1.normalizer_eq
import Submission.Work.DoubleTransitivity.Sec2.inv_class
import Submission.Work.DoubleTransitivity.Sec2.prop1a_exists
import Submission.Work.DoubleTransitivity.Sec4.Defs
import Submission.Work.DoubleTransitivity.Sec4.RpDefs
import Submission.Work.DoubleTransitivity.Sec4.RpHelpers
import Submission.Work.DoubleTransitivity.Sec4.prop2
import Submission.Work.DoubleTransitivity.Sec4.lemma2_part1
import Submission.Work.DoubleTransitivity.Sec4.not_rp_twoTransitive
import Submission.Work.DoubleTransitivity.Sec4.rp_no_two_fixed_pts
import Submission.Work.DoubleTransitivity.App2.app2_2
import Submission.Work.DoubleTransitivity.App2.app2_6
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Basic
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup
import Submission.Work.ThreePoints.ThmC.pPrimeCoreSub_conj
import Submission.Work.ThreePoints.ThmC.odd_ncard_of_unique_fixed
import Submission.Work.ThreePoints.ThmC.exists_fixed_of_odd_ncard

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec6.exists_F_case3`

Peterfalvi I, Ch. I §6, Proposition 2 (p. 160), **Step 3** (the case `C_G(J(P,u)) ≤ H`),
in the form requested by the Ch. I §6 assembly: the subgroup `F = N_G(P)` works.

Let `H` be strongly embedded in the finite group `G`, `p` an odd prime, `P ≤ H` a `p`-subgroup
maximal among the `p`-subgroups of `G` with at least three fixed points
(`Work.DoubleTransitivity.MaxFixesThree p H P`), and `u ∈ Inv(H)` an involution normalising `P`
without centralising it.  Assume `C_G(⟨J(P,u)⟩) ≤ H` (Peterfalvi's second case).  Then

`F := N_G(P)` satisfies

* `F ∩ H` is a proper strongly embedded subgroup of `F`;
* for every involution `s ∈ F` and every point `ω` of `Ω = G ⧸ H` fixed by `s`,
  `J(P,u)` fixes `ω` and `O_{p'}(H ∩ H^s) ≤ O_{p'}(H(s) ∩ H ∩ H^s)`.

The argument follows the source.

* `F ∩ H` is strongly embedded in `F`: `|N_H(P)| = |F ∩ H|` is even (`Sec4.prop2`), and
  `F ⊄ H`: either `𝓡_p ≠ ∅`, in which case no `p`-subgroup has exactly two fixed points
  (`Sec4.rp_no_two_fixed_pts`), so a `p`-Sylow of the two-point stabiliser `Stab(pt H) ⊓ Stab ω`
  containing `P` must equal `P` and Ch. I §3 Lemma 1 (`ThreePoints.sec3_lemma1`) produces an
  involution of `F \ H`; or `𝓡_p = ∅`, in which case `G` is doubly transitive on `Ω`
  (`Sec4.not_rp_twoTransitive`) and `F` is transitive on `Ω_P` (`App2.app2_6`), so it moves
  `pt H`.  Ch. I §1 (6) then gives the strong embedding in `F` (`ThreePoints.subgroupOf_inf`).
* For an involution `s ∈ F`, the set `Ω_P` of fixed points of `P` is `u`-invariant with a unique
  fixed point, hence has odd cardinality, so `s` fixes a point `ω' ∈ Ω_P`; as `s` has a unique
  fixed point, `ω' = ω` and `P ≤ Stab(ω)`, whence `J(P,u) ≤ P` fixes `ω`.
* For the `O_{p'}` inclusion: for `s ∈ H` both sides are `O_{p'}(H)`.  Otherwise `ω ≠ pt H`,
  so `u` and `s` have no common fixed point and Ch. I §2 Prop. 1 (a) produces an involution `t`
  with `t⁻¹ u t = s`; Step 1 (`Sec6.step1`, with `H₁ = H`, `H₂ = Stab(ω)`, involution `u` and
  `p`-subgroup `P`, using `C_G(⟨J(P,u)⟩) ≤ H`) gives
  `O_{p'}(Stab(ω) ∩ Stab(ω)^u) ≤ O_{p'}(H ∩ Stab(ω) ∩ Stab(ω)^u)`, and conjugating by `t`
  (which exchanges `Stab(ω)` and `H`) yields the claim.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.DoubleTransitivity.Sec6

/-- `N_G(P) ⊄ H` for `P ≤ H` maximal among the `p`-subgroups of `G` fixing three points.

If `𝓡_p ≠ ∅` the source's Ch. I §4 Prop. 1 (b) says that no `p`-subgroup fixes exactly two
points; a `p`-Sylow `Q` of a two-point stabiliser `Stab(pt H) ⊓ Stab ω` containing `P` must
therefore equal `P`, and Ch. I §3 Lemma 1 then gives an involution of `N_G(P)` exchanging `pt H`
and `ω`.  If `𝓡_p = ∅`, `G` is doubly transitive on `Ω` and `N_G(P)` is transitive on `Ω_P`. -/
private theorem priv_exists_normalizer_not_mem {G : Type} [Group G] [Finite G]
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hP : Work.DoubleTransitivity.MaxFixesThree p H P) (hPH : P ≤ H) :
    ∃ g : G, g ∈ Subgroup.normalizer (P : Set G) ∧ g ∉ H := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype (Omega H) := Fintype.ofFinite _
  obtain ⟨hPp, hP3, hPmax⟩ := hP
  have hP3' : 3 ≤ (Submission.Blueprint.fixedPts H P).ncard := hP3
  have hPgt : 1 < (Submission.Blueprint.fixedPts H P).ncard :=
    lt_of_lt_of_le (by norm_num) hP3'
  have hstabH : MulAction.stabilizer G (pt H) = H :=
    Work.DoubleTransitivity.Sec4.stabilizer_pt_eq H
  by_cases hRp : Work.DoubleTransitivity.Sec4.Rp p H
  · -- ## `𝓡_p ≠ ∅`
    have h1 : Work.DoubleTransitivity.Sec4.Sec4Lemma2Part1 p H :=
      Work.DoubleTransitivity.Sec4.lemma2_part1 hBrSz hH hp hp2
    have hno2 := Work.DoubleTransitivity.Sec4.rp_no_two_fixed_pts hBrSz hH hp hp2 h1 hRp
    -- a fixed point `ω ≠ pt H` of `P`
    obtain ⟨ω, hωP, hωne⟩ := Set.exists_ne_of_one_lt_ncard
      (s := Submission.Blueprint.fixedPts H P) hPgt (pt H)
    have hωstab : P ≤ MulAction.stabilizer G ω :=
      Work.DoubleTransitivity.Sec4.mem_fixedPts_iff_le_stabilizer_aux.mp hωP
    have hPle : P ≤ MulAction.stabilizer G (pt H) ⊓ MulAction.stabilizer G ω :=
      le_inf (by rw [hstabH]; exact hPH) hωstab
    obtain ⟨Q, hPQ, hQsyl⟩ := Work.DoubleTransitivity.Sec4.exists_isSylowSubgroupOf_le hPp hPle
    have hQH : Q ≤ H := by rw [← hstabH]; exact le_trans hQsyl.1 inf_le_left
    -- `Q = P` by maximality: otherwise `Q` fixes exactly the two points `pt H`, `ω`
    have hQeq : Q = P := by
      by_contra hne
      have hle2 : (Submission.Blueprint.fixedPts H Q).ncard ≤ 2 := by
        by_contra hcon
        have h3 : 3 ≤ (Submission.Blueprint.fixedPts H Q).ncard := by omega
        exact hne (le_antisymm (hPmax Q hQsyl.2.1 h3 hPQ) hPQ)
      have hge2 : 2 ≤ (Submission.Blueprint.fixedPts H Q).ncard := by
        have hsub : ({(pt H), ω} : Set (Omega H)) ⊆ Submission.Blueprint.fixedPts H Q := by
          intro y hy
          rcases hy with rfl | rfl
          · exact Work.DoubleTransitivity.Sec4.mem_fixedPts_iff_le_stabilizer_aux.mpr
              (le_trans hQsyl.1 inf_le_left)
          · exact Work.DoubleTransitivity.Sec4.mem_fixedPts_iff_le_stabilizer_aux.mpr
              (le_trans hQsyl.1 inf_le_right)
        have h := Set.ncard_le_ncard hsub
        rwa [Set.ncard_pair (Ne.symm hωne)] at h
      exact hno2 Q hQsyl.2.1 (le_antisymm hle2 hge2)
    have hPsyl : Work.DoubleTransitivity.IsSylowSubgroupOf p P
        (MulAction.stabilizer G (pt H) ⊓ MulAction.stabilizer G ω) := hQeq ▸ hQsyl
    obtain ⟨v, _hv2, hvP, hvω⟩ := Work.ThreePoints.sec3_lemma1 hH hp (Ne.symm hωne) hPsyl
    refine ⟨v, ?_, ?_⟩
    · exact (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer v P).mp hvP
    · intro hvH
      have hfix : v • pt H = pt H :=
        MulAction.mem_stabilizer_iff.mp (by rw [hstabH]; exact hvH)
      exact hωne (hvω ▸ hfix)
  · -- ## `𝓡_p = ∅`: `G` is doubly transitive on `Ω`
    have hNnotle : ¬ (Subgroup.normalizer (P : Set G) ≤ H) := by
      intro hNle
      have h1 : Work.DoubleTransitivity.Sec4.Sec4Lemma2Part1 p H :=
        Work.DoubleTransitivity.Sec4.lemma2_part1 hBrSz hH hp hp2
      have htr : MulAction.IsMultiplyPretransitive G (Omega H) 2 :=
        Work.DoubleTransitivity.Sec4.not_rp_twoTransitive hBrSz hH hp hp2 h1 hRp
      obtain ⟨b, _hbP, hbne⟩ := Set.exists_ne_of_one_lt_ncard
        (s := Submission.Blueprint.fixedPts H P) hPgt (pt H)
      have hbigP : 3 ≤ (Work.DoubleTransitivity.fixedBySub P : Set (Omega H)).ncard := hP3'
      have hmax : ∀ Q : Subgroup G, IsPGroup p Q → Q ≤ MulAction.stabilizer G (pt H) →
          3 ≤ (Work.DoubleTransitivity.fixedBySub Q : Set (Omega H)).ncard → P ≤ Q → Q ≤ P := by
        intro Q hQp hQa hQ3 hPQ
        rw [hstabH] at hQa
        exact hPmax Q hQp hQ3 hPQ
      obtain ⟨-, h2trN⟩ := Work.DoubleTransitivity.App2.app2_6 (X := G) (E := Omega H)
        (p := p) (a := pt H) (b := b) (Ne.symm hbne) htr hPp (by rw [hstabH]; exact hPH)
        hbigP hmax
      have hmemP : pt H ∈ (Work.DoubleTransitivity.fixedBySub P : Set (Omega H)) := by
        rw [Work.DoubleTransitivity.mem_fixedBySub]
        intro q hq
        exact MulAction.mem_stabilizer_iff.mp (by rw [hstabH]; exact hPH hq)
      obtain ⟨c, hc, hcne⟩ := Set.exists_ne_of_one_lt_ncard
        (s := (Work.DoubleTransitivity.fixedBySub P : Set (Omega H)))
        (by exact lt_of_lt_of_le (by norm_num) hbigP) (pt H)
      obtain ⟨k, hkN, hk⟩ := h2trN.isTransitiveOnSub (pt H) hmemP c hc
      refine hcne ?_
      have hkfix : k • pt H = pt H :=
        MulAction.mem_stabilizer_iff.mp (by rw [hstabH]; exact hNle hkN)
      rw [hk] at hkfix
      exact hkfix
    obtain ⟨g, hgN, hgH⟩ : ∃ g : G, g ∈ Subgroup.normalizer (P : Set G) ∧ g ∉ H := by
      by_contra hcon
      apply hNnotle
      intro x hx
      by_contra hxH
      exact hcon ⟨x, hx, hxH⟩
    exact ⟨g, hgN, hgH⟩

/-- Conjugating the Step 1 inclusion by an involution `t` exchanging `u` and `s`.

Step 1 (`Sec6.step1`) with `H₁ = H`, `H₂ = Stab(ω)` and the involution `u` gives
`O_{p'}(Stab(ω) ⊓ Stab(ω)^u) ≤ O_{p'}(H ⊓ Stab(ω) ⊓ Stab(ω)^u)`.  Since `u` and `s` are
conjugate by the involution `t`, conjugation by `t` sends `Stab(ω)` to `H` (both contain the
involution `u`) and `H` to `Stab(ω)` (both contain `s`), and `(Stab ω)^u` to `H^s`; this is
exactly the requested inclusion. -/
private theorem priv_pPrimeCoreSub_conj_swap {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {H : Subgroup G} (hB : Work.DoubleTransitivity.IsBender H)
    {u s t : G} (hu2 : orderOf u = 2) (hs2 : orderOf s = 2) (ht2 : orderOf t = 2)
    (htconj : t⁻¹ * u * t = s) (huH : u ∈ H)
    {ω : Work.DoubleTransitivity.Omega H} (hω : s • ω = ω)
    (hstep : Work.DoubleTransitivity.pPrimeCoreSub p
        (MulAction.stabilizer G ω ⊓ Submission.Blueprint.conj u (MulAction.stabilizer G ω)) ≤
      Work.DoubleTransitivity.pPrimeCoreSub p
        (H ⊓ MulAction.stabilizer G ω ⊓ Submission.Blueprint.conj u
          (MulAction.stabilizer G ω))) :
    Work.DoubleTransitivity.pPrimeCoreSub p (H ⊓ Submission.Blueprint.conj s H) ≤
      Work.DoubleTransitivity.pPrimeCoreSub p
        (MulAction.stabilizer G ω ⊓ H ⊓ Submission.Blueprint.conj s H) := by
  classical
  have htinv : t⁻¹ = t := Work.DoubleTransitivity.App1.inv_eq_self_of_orderOf_eq_two ht2
  -- the two conjugates of each other which feature in the statement
  have hts : t * u * t⁻¹ = s := by rw [← htconj, htinv]
  have hut : u = t * s * t⁻¹ := by rw [← htconj]; group
  have htu : s * t = t * u := by rw [← hts, mul_assoc, inv_mul_cancel, mul_one]
  -- `t • ω = pt H`
  have htω : t • ω = pt H := by
    refine Work.DoubleTransitivity.Sec1.eq_of_smul_eq_of_orderOf_eq_two (H := H) hB (u := u) hu2
      ?_ ?_
    · show u • (t • ω) = t • ω
      rw [hut, mul_smul, mul_smul, inv_smul_smul, hω]
    · show u • pt H = pt H
      exact MulAction.mem_stabilizer_iff.mp (by
        rw [Work.DoubleTransitivity.Sec4.stabilizer_pt_eq H]; exact huH)
  -- `t • pt H = ω`
  have htpt : t • pt H = ω := by
    refine Work.DoubleTransitivity.Sec1.eq_of_smul_eq_of_orderOf_eq_two (H := H) hB (u := s) hs2
      ?_ hω
    show s • (t • pt H) = t • pt H
    rw [← hts, mul_smul, mul_smul, inv_smul_smul]
    congr 1
    show u • pt H = pt H
    exact MulAction.mem_stabilizer_iff.mp (by
      rw [Work.DoubleTransitivity.Sec4.stabilizer_pt_eq H]; exact huH)
  -- conjugation by `t` exchanges the two stabilisers
  have hStab1 : Submission.Blueprint.conj t (MulAction.stabilizer G ω) = H := by
    rw [← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj t ω, htω,
      Work.DoubleTransitivity.Sec4.stabilizer_pt_eq]
  have hStab2 : Submission.Blueprint.conj t H = MulAction.stabilizer G ω := by
    have h1 : Submission.Blueprint.conj t H =
        Submission.Blueprint.conj t (MulAction.stabilizer G (pt H)) := by
      rw [Work.DoubleTransitivity.Sec4.stabilizer_pt_eq]
    rw [h1, ← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj t (pt H), htpt]
  have hStab3 : MulAction.stabilizer G (s • pt H) = Submission.Blueprint.conj s H := by
    rw [Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj s (pt H),
      Work.DoubleTransitivity.Sec4.stabilizer_pt_eq]
  have hconj_uu : Submission.Blueprint.conj t
      (Submission.Blueprint.conj u (MulAction.stabilizer G ω)) =
      Submission.Blueprint.conj s H := by
    rw [← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj u ω,
      ← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj t (u • ω),
      ← mul_smul, ← htu, mul_smul, htω, hStab3]
  have hconjLHS : Submission.Blueprint.conj t
      (MulAction.stabilizer G ω ⊓ Submission.Blueprint.conj u (MulAction.stabilizer G ω)) =
      H ⊓ Submission.Blueprint.conj s H := by
    rw [Work.ThreePoints.conj_inf, hStab1, hconj_uu]
  have hconjRHS : Submission.Blueprint.conj t
      (H ⊓ MulAction.stabilizer G ω ⊓ Submission.Blueprint.conj u
        (MulAction.stabilizer G ω)) =
      MulAction.stabilizer G ω ⊓ H ⊓ Submission.Blueprint.conj s H := by
    rw [Work.ThreePoints.conj_inf, Work.ThreePoints.conj_inf, hStab2, hStab1, hconj_uu]
  have hpcs_conj : ∀ (X : Subgroup G) (g : G),
      Work.DoubleTransitivity.pPrimeCoreSub p (Submission.Blueprint.conj g X) =
        Submission.Blueprint.conj g (Work.DoubleTransitivity.pPrimeCoreSub p X) :=
    fun X g => Work.ThreePoints.ThmC.pPrimeCoreSub_conj p hp X g
  have h1 : Submission.Blueprint.conj t (Work.DoubleTransitivity.pPrimeCoreSub p
        (MulAction.stabilizer G ω ⊓ Submission.Blueprint.conj u (MulAction.stabilizer G ω))) ≤
      Submission.Blueprint.conj t (Work.DoubleTransitivity.pPrimeCoreSub p
        (H ⊓ MulAction.stabilizer G ω ⊓ Submission.Blueprint.conj u
          (MulAction.stabilizer G ω))) :=
    Subgroup.map_mono hstep
  rw [← hpcs_conj, ← hpcs_conj, hconjLHS, hconjRHS] at h1
  exact h1

theorem exists_F_case3 {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hP : Work.DoubleTransitivity.MaxFixesThree p H P) (hPH : P ≤ H)
    {u : G} (hu : u ∈ Submission.Blueprint.involutions (H : Set G))
    (huN : u ∈ Subgroup.normalizer (P : Set G))
    (hnc : ¬ ∀ x ∈ P, u * x * u⁻¹ = x)
    (hC : Subgroup.centralizer (Subgroup.closure (Submission.Blueprint.invertedBy P u) : Set G) ≤ H) :
    ∃ F : Subgroup G,
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((H ⊓ F).subgroupOf F) ∧
      ∀ s ∈ Submission.Blueprint.involutions (F : Set G),
        ∀ ω : Work.DoubleTransitivity.Omega H, (s : G) • ω = ω →
          (∀ k ∈ Submission.Blueprint.invertedBy P u, k • ω = ω) ∧
          Work.DoubleTransitivity.pPrimeCoreSub p (H ⊓ Submission.Blueprint.conj s H) ≤
            Work.DoubleTransitivity.pPrimeCoreSub p
              (MulAction.stabilizer G ω ⊓ H ⊓ Submission.Blueprint.conj s H) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype (Omega H) := Fintype.ofFinite _
  have hB : Work.DoubleTransitivity.IsBender H :=
    ((Work.DoubleTransitivity.isStronglyEmbedded_iff H).mp hH).2
  obtain ⟨huH, hu2⟩ := hu
  obtain ⟨hPp, hP3, hPmax⟩ := hP
  have hPmaxIn : Work.DoubleTransitivity.MaxFixesThreeIn p H P :=
    ⟨hPp, hPH, hP3, fun Q hQp _ hQ3 hPQ => hPmax Q hQp hQ3 hPQ⟩
  have hEvenN : Even (Nat.card ↥(Subgroup.normalizer (P : Set G) ⊓ H)) :=
    (Work.DoubleTransitivity.Sec4.prop2 hBrSz hH hp hp2 hPmaxIn).2
  have hstabH : MulAction.stabilizer G (pt H) = H :=
    Work.DoubleTransitivity.Sec4.stabilizer_pt_eq H
  obtain ⟨a₀, ha₀N, ha₀H⟩ :=
    priv_exists_normalizer_not_mem hBrSz hH hp hp2 ⟨hPp, hP3, hPmax⟩ hPH
  have hNnotle : ¬ (Subgroup.normalizer (P : Set G) ≤ H) := fun hle => ha₀H (hle ha₀N)
  have hproper : (Subgroup.normalizer (P : Set G) ⊓ H).subgroupOf
      (Subgroup.normalizer (P : Set G)) ≠ ⊤ := by
    intro htop
    refine hNnotle fun n hn => ?_
    have hmem : (⟨n, hn⟩ : ↥(Subgroup.normalizer (P : Set G))) ∈
        (Subgroup.normalizer (P : Set G) ⊓ H).subgroupOf (Subgroup.normalizer (P : Set G)) := by
      rw [htop]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp hmem).2
  have hseN : IsStronglyEmbedded ((Subgroup.normalizer (P : Set G) ⊓ H).subgroupOf
      (Subgroup.normalizer (P : Set G))) :=
    Work.ThreePoints.IsStronglyEmbedded.subgroupOf_inf hH hproper hEvenN
  refine ⟨Subgroup.normalizer (P : Set G), ?_, ?_⟩
  · -- ## `(H ⊓ N_G(P)).subgroupOf N_G(P)` is strongly embedded
    have hsubeq : ((H ⊓ Subgroup.normalizer (P : Set G)).subgroupOf
          (Subgroup.normalizer (P : Set G))) =
        ((Subgroup.normalizer (P : Set G) ⊓ H).subgroupOf
          (Subgroup.normalizer (P : Set G))) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      tauto
    rw [hsubeq]
    exact hseN
  · -- ## the two conditions for `F = N_G(P)`
    intro s hs ω hω
    obtain ⟨hsN, hs2⟩ := hs
    -- `P ≤ Stab(ω)`: `s` fixes a point of the odd-order invariant set `Ω_P`
    have hPstab : P ≤ MulAction.stabilizer G ω := by
      -- `u` acts on `Ω_P` with the unique fixed point `pt H`, so `|Ω_P|` is odd
      have hu_inv : Function.Involutive (fun x : Omega H => u • x) := by
        intro x
        show u • (u • x) = x
        rw [← mul_smul, Work.DoubleTransitivity.App1.mul_self_eq_one_of_orderOf_eq_two hu2,
          one_smul]
      have hu_pres : ∀ x ∈ (Submission.Blueprint.fixedPts H P : Set (Omega H)),
          u • x ∈ (Submission.Blueprint.fixedPts H P : Set (Omega H)) := by
        intro x hx
        rw [Work.ThreePoints.mem_fixedPts] at hx ⊢
        intro q hq
        have hq' : u⁻¹ * q * u ∈ P := by
          simpa only [inv_inv] using
            (Subgroup.mem_normalizer_iff.mp
              ((Subgroup.normalizer (P : Set G)).inv_mem huN) q).mp hq
        calc q • (u • x) = (q * u) • x := (mul_smul q u x).symm
          _ = (u * (u⁻¹ * q * u)) • x := by
              rw [show u * (u⁻¹ * q * u) = q * u from by group]
          _ = u • ((u⁻¹ * q * u) • x) := mul_smul u _ x
          _ = u • x := by rw [hx _ hq']
      have hΩodd : Odd (Submission.Blueprint.fixedPts H P : Set (Omega H)).ncard := by
        refine Work.ThreePoints.ThmC.odd_ncard_of_unique_fixed (fun x : Omega H => u • x)
          hu_inv hu_pres ?_ ?_
        · intro x y _ hxf _ hyf
          exact Work.DoubleTransitivity.Sec1.eq_of_smul_eq_of_orderOf_eq_two (H := H) hB
            (u := u) hu2 hxf hyf
        · refine ⟨pt H, Work.DoubleTransitivity.Sec4.mem_fixedPts_iff_le_stabilizer_aux.mpr
            (by rw [hstabH]; exact hPH), ?_⟩
          exact MulAction.mem_stabilizer_iff.mp (by rw [hstabH]; exact huH)
      -- `s` preserves `Ω_P` and hence fixes a point of it
      have hs_inv : Function.Involutive (fun x : Omega H => s • x) := by
        intro x
        show s • (s • x) = x
        rw [← mul_smul, Work.DoubleTransitivity.App1.mul_self_eq_one_of_orderOf_eq_two hs2,
          one_smul]
      have hs_pres : ∀ x ∈ (Submission.Blueprint.fixedPts H P : Set (Omega H)),
          s • x ∈ (Submission.Blueprint.fixedPts H P : Set (Omega H)) := by
        intro x hx
        rw [Work.ThreePoints.mem_fixedPts] at hx ⊢
        intro q hq
        have hq' : s⁻¹ * q * s ∈ P := by
          simpa only [Work.DoubleTransitivity.App1.inv_eq_self_of_orderOf_eq_two hs2] using
            (Subgroup.mem_normalizer_iff.mp
              ((Subgroup.normalizer (P : Set G)).inv_mem hsN) q).mp hq
        calc q • (s • x) = (q * s) • x := (mul_smul q s x).symm
          _ = (s * (s⁻¹ * q * s)) • x := by
              rw [show s * (s⁻¹ * q * s) = q * s from by group]
          _ = s • ((s⁻¹ * q * s) • x) := mul_smul s _ x
          _ = s • x := by rw [hx _ hq']
      obtain ⟨ω', hω', hω's⟩ := Work.ThreePoints.ThmC.exists_fixed_of_odd_ncard
        (fun x : Omega H => s • x) hs_inv hs_pres hΩodd
      have hωeq : ω' = ω := Work.DoubleTransitivity.Sec1.eq_of_smul_eq_of_orderOf_eq_two
        (H := H) hB (u := s) hs2 hω's hω
      rw [← hωeq]
      exact Work.DoubleTransitivity.Sec4.mem_fixedPts_iff_le_stabilizer_aux.mp hω'
    refine ⟨fun k hk => MulAction.mem_stabilizer_iff.mp (hPstab hk.1), ?_⟩
    -- ## the `O_{p'}` inclusion
    by_cases hsH : s ∈ H
    · -- `s ∈ H`: then `ω = pt H` and both sides are `O_{p'}(H)`
      have hωpt : ω = pt H := Work.DoubleTransitivity.Sec1.eq_of_smul_eq_of_orderOf_eq_two
        (H := H) hB (u := s) hs2 hω
        (MulAction.mem_stabilizer_iff.mp (by rw [hstabH]; exact hsH))
      have hconjH : Submission.Blueprint.conj s H = H :=
        (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer s H).mpr
          (by rw [Work.ThreePoints.IsStronglyEmbedded.normalizer_eq hH]; exact hsH)
      rw [hωpt, hstabH, hconjH]
      simp only [inf_idem, le_refl]
    · -- `s ∉ H`: Step 1 with `H₁ = H`, `H₂ = Stab(ω)`, involution `u`
      have hωne : ω ≠ pt H := by
        intro h
        exact hsH (by rw [← hstabH, ← h]; exact MulAction.mem_stabilizer_iff.mpr hω)
      -- `Stab(ω)` is a conjugate of `H`
      obtain ⟨g₀, hg₀⟩ : ∃ g : G, MulAction.stabilizer G ω = Submission.Blueprint.conj g H := by
        obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective ω
        exact ⟨g, by rw [← hg, Work.ThreePoints.stabilizer_mk]⟩
      -- `Stab(ω) ⊓ Stab(ω)^u` has odd order: two distinct conjugates of `H`
      have hnorm : Subgroup.normalizer (MulAction.stabilizer G ω : Set G) =
          MulAction.stabilizer G ω := by
        rw [hg₀]
        exact Work.ThreePoints.IsStronglyEmbedded.normalizer_eq
          (Work.ThreePoints.conj_stronglyEmbedded hH g₀)
      have hu_notstab : u ∉ MulAction.stabilizer G ω := by
        intro hu_stab
        have hpt : ω = pt H := Work.DoubleTransitivity.Sec1.eq_of_smul_eq_of_orderOf_eq_two
          (H := H) hB (u := u) hu2 (MulAction.mem_stabilizer_iff.mp hu_stab)
          (MulAction.mem_stabilizer_iff.mp (by rw [hstabH]; exact huH))
        exact hωne hpt
      have hne3 : MulAction.stabilizer G ω ≠
          Submission.Blueprint.conj u (MulAction.stabilizer G ω) := by
        intro heq
        have huN' : u ∈ Subgroup.normalizer (MulAction.stabilizer G ω : Set G) :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm
        rw [hnorm] at huN'
        exact hu_notstab huN'
      have hodd : Odd (Nat.card
          (MulAction.stabilizer G ω ⊓ Submission.Blueprint.conj u
            (MulAction.stabilizer G ω) : Subgroup G)) := by
        have hne'' : Submission.Blueprint.conj g₀ H ≠
            Submission.Blueprint.conj (u * g₀) H := by
          intro heq
          apply hne3
          rw [hg₀, ← Work.ThreePoints.conj_mul]
          exact heq
        have hres := Work.ThreePoints.card_inf_conj_odd hH hne''
        rw [Work.ThreePoints.conj_mul, ← hg₀] at hres
        exact hres
      have hcu : Submission.Blueprint.conj u P = P :=
        (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer u P).mpr huN
      have hC3 : Subgroup.centralizer
            (Subgroup.closure (Submission.Blueprint.invertedBy P u) : Set G) ⊓
            MulAction.stabilizer G ω ⊓ Submission.Blueprint.conj u
              (MulAction.stabilizer G ω) ≤ H :=
        le_trans (le_trans inf_le_left inf_le_left) hC
      have hstep := Work.DoubleTransitivity.Sec6.step1 hFT hH hp
        (H₁ := H) (H₂ := MulAction.stabilizer G ω) (K := P) (s := u)
        ⟨1, (Work.ThreePoints.conj_one H).symm⟩ ⟨g₀, hg₀⟩ hu2 huH hPH hPstab hcu hPp hodd hC3
      -- an involution `t` with `t⁻¹ * u * t = s`: `u` and `s` share no fixed point
      have hsep : ¬ ∃ ω' : Omega H, u • ω' = ω' ∧ s • ω' = ω' := by
        rintro ⟨ω', huω', hsω'⟩
        have h1 : ω' = pt H := Work.DoubleTransitivity.Sec1.eq_of_smul_eq_of_orderOf_eq_two
          (H := H) hB (u := u) hu2 huω'
          (MulAction.mem_stabilizer_iff.mp (by rw [hstabH]; exact huH))
        have h2 : ω' = ω := Work.DoubleTransitivity.Sec1.eq_of_smul_eq_of_orderOf_eq_two
          (H := H) hB (u := s) hs2 hsω' hω
        exact hωne (h2 ▸ h1)
      obtain ⟨t, ht2, htconj, -, -⟩ :=
        Work.DoubleTransitivity.Sec2.prop1a_exists hB hu2 hs2 hsep
      exact priv_pPrimeCoreSub_conj_swap hp hB hu2 hs2 ht2 htconj huH hω hstep

end Work.DoubleTransitivity.Sec6
