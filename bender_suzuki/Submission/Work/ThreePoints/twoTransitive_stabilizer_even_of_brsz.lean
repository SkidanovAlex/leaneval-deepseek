import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Pointwise

/-- **Peterfalvi I Ch. I §3 Prop. 1, Case 2 / Appendix III (1)–(2)**, the 2-rank-`1` case of Ch. I §4 Prop. 2, with the Brauer–Suzuki black box as a hypothesis: let `M` be a finite group acting 2-transitively on a finite set `E` with `3 ≤ |E|`, suppose `M` has no four-group (`¬ HasFourGroup M`) and contains an involution (`hz`).  Then every point stabiliser of `M` on `E` has even order.  In the source (`REFS/peterfalvi_I_ch1_2.md` p. 154, Case 2, for `M := N_G(P)` of 2-rank 1) this is exactly the step "By Brauer–Suzuki, `M/O_{2'}(M)` has a unique involution"; the workspace file `Submission/Work/ThreePoints/twoTransitive_stabilizer_even.lean` records the reduction (and its note `NOTES_twoTransitive_stabilizer_even.md`) and leaves the BrSz-free version open.

Reduction (all elementary; see the file just quoted): if some involution lies in a point stabiliser, that stabiliser — and, by 2-transitivity, every one — has even order.  Otherwise every involution is a derangement, every point stabiliser has odd order, `2 ∣ |E|`, `Inv(M)` is a single conjugacy class, `V := ⟨Inv(M)⟩ ⊴ M` is transitive on `E`, and in a minimal counterexample one may assume `O(M) = 1` and `M = O^{2'}(M)`.  There, `hBrSz` applied to an involution `z` gives `oddCore M ⊔ C_M(z) = ⊤`, i.e. `M = C_M(z)` (as `oddCore M = 1`); then `⟨z⟩ ⊴ M` has index `|M|/2`, so `O^{2'}(M) ≤ ⟨z⟩ ≠ M`, contradicting `M = O^{2'}(M)` — hence a point stabiliser has even order.  (`hFT` is included for project convention; `hz` is in fact implied by 2-transitivity and `3 ≤ |E|`.) -/
theorem twoTransitive_stabilizer_even_of_brsz {M E : Type} [Group M] [MulAction M E]
    [Finite M] [Finite E] (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (h2 : MulAction.IsMultiplyPretransitive M E 2) (h3 : 3 ≤ Nat.card E)
    (h4 : ¬ Submission.Blueprint.HasFourGroup M) {a : E} (hz : ∃ z : M, orderOf z = 2) :
    Even (Nat.card (MulAction.stabilizer M a)) := by
  -- Proof by contradiction: suppose the point stabiliser `H = M_a` is odd.
  -- Let `z` be an involution and put `N = O(M)` (normal, of odd order) and `C = C_M(z)`.
  -- Brauer–Suzuki gives `N ⊔ C = ⊤`, i.e. `M = O(M) · C_M(z)`.
  -- * If `N` acts nontrivially on `E`, then (quasi-primitivity of the 2-transitive
  --   action) `N` is transitive on `E`, so `|E|` divides the odd number `|N|`: `|E|` is odd,
  --   and then `|M| = |E| · |H|` is odd, contradicting `z`.
  -- * If `N` fixes every point, then `C` induces the same permutation group as `M`, so `C`
  --   is 2-transitive on `E`; as `z` is central in `C`, `⟨z⟩` is a normal subgroup of `C`
  --   not fixing every point, hence transitive: `|E| = |⟨z⟩ : ⟨z⟩ ∩ H| = 2`, as `H` is odd.
  --   Contradicts `3 ≤ |E|`.
  rw [← Nat.not_odd_iff_even]
  intro hodd
  obtain ⟨z, hz2⟩ := hz
  haveI hpretr : MulAction.IsPretransitive M E :=
    MulAction.isPretransitive_of_is_two_pretransitive (h2 := h2)
  set H : Subgroup M := MulAction.stabilizer M a with hH
  -- `z` does not lie in the stabiliser `H` (whose order is odd).
  have hzH : z ∉ H := by
    intro hzmem
    have h2dvd : 2 ∣ Nat.card ↥H := by
      have h := orderOf_dvd_natCard (⟨z, hzmem⟩ : ↥H)
      rwa [Subgroup.orderOf_mk, hz2] at h
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)
  have hza : z • a ≠ a := fun h => hzH (hH.symm ▸ MulAction.mem_stabilizer_iff.mpr h)
  set N : Subgroup M := Submission.Blueprint.oddCore M with hN
  set C : Subgroup M := Subgroup.centralizer ({z} : Set M) with hC
  have hbr : N ⊔ C = ⊤ := by
    rw [hN, hC]
    exact hBrSz M h4 z hz2
  haveI hNnormal : N.Normal := by rw [hN]; infer_instance
  by_cases htriv : ∀ x ∈ N, ∀ b : E, x • b = b
  · -- Case 1: `O(M)` acts trivially, so `C_M(z)` induces the full permutation group.
    have hzC : z ∈ C := by
      rw [hC, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
    let zc : ↥C := ⟨z, hzC⟩
    have h2C : MulAction.IsMultiplyPretransitive ↥C E 2 := by
      rw [MulAction.is_two_pretransitive_iff]
      intro x y u v hxy huv
      obtain ⟨g, hg1, hg2⟩ := MulAction.is_two_pretransitive_iff.mp h2 hxy huv
      have hg : g ∈ N ⊔ C := by rw [hbr]; trivial
      have hgm : g ∈ (N : Set M) * (C : Set M) := by
        rw [← Subgroup.normal_mul N C]
        exact hg
      rw [Set.mem_mul] at hgm
      obtain ⟨n, hn, c', hc', hnc'⟩ := hgm
      refine ⟨⟨c', hc'⟩, ?_, ?_⟩
      · show c' • x = u
        have h1 : (n * c') • x = c' • x := by rw [mul_smul, htriv n hn]
        rw [← hnc', h1] at hg1
        exact hg1
      · show c' • y = v
        have h1 : (n * c') • y = c' • y := by rw [mul_smul, htriv n hn]
        rw [← hnc', h1] at hg2
        exact hg2
    have hppC : MulAction.IsPreprimitive ↥C E :=
      MulAction.isPreprimitive_of_is_two_pretransitive h2C
    letI : MulAction.IsPreprimitive ↥C E := hppC
    have hqC : MulAction.IsQuasiPreprimitive ↥C E := inferInstance
    -- `z` is central in `C_M(z)`, so `⟨z⟩` is normal in `C_M(z)`.
    have hzc_center : zc ∈ Subgroup.center ↥C := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp w.2 z (by simp)).symm
    have hZnorm : (Subgroup.zpowers zc).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzc_center)
    letI : (Subgroup.zpowers zc).Normal := hZnorm
    -- `⟨z⟩` does not fix every point, so it acts transitively on `E`.
    have hfpZ : MulAction.fixedPoints ↥(Subgroup.zpowers zc) E ≠ Set.univ := by
      intro h
      have ha : a ∈ MulAction.fixedPoints ↥(Subgroup.zpowers zc) E := by rw [h]; trivial
      have h1 := (MulAction.mem_fixedPoints.mp ha)
        (⟨zc, Subgroup.mem_zpowers zc⟩ : ↥(Subgroup.zpowers zc))
      exact hza (by simpa [Subgroup.smul_def, zc] using h1)
    have hZtr : MulAction.IsPretransitive ↥(Subgroup.zpowers zc) E :=
      MulAction.IsQuasiPreprimitive.isPretransitive_of_normal (self := hqC) hfpZ
    have horbZ : MulAction.orbit ↥(Subgroup.zpowers zc) a = Set.univ :=
      (MulAction.isPretransitive_iff_orbit_eq_univ a).mp hZtr
    -- Orbit–stabiliser: `|E| * |⟨z⟩_a| = |⟨z⟩| = 2`, so `|E| ∣ 2`, whereas `3 ≤ |E|`.
    have hcardZ : Nat.card E * Nat.card ↥(MulAction.stabilizer ↥(Subgroup.zpowers zc) a)
        = Nat.card ↥(Subgroup.zpowers zc) := by
      have h1 := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥(Subgroup.zpowers zc) a)
      rw [Nat.card_prod] at h1
      rw [horbZ, Nat.card_coe_set_eq, Set.ncard_univ] at h1
      exact h1
    have hZcard : Nat.card ↥(Subgroup.zpowers zc) = 2 := by
      rw [Nat.card_zpowers]
      show orderOf zc = 2
      rw [show zc = ⟨z, hzC⟩ from rfl, Subgroup.orderOf_mk, hz2]
    have hdvd2 : Nat.card E ∣ 2 := ⟨_, (hcardZ.trans hZcard).symm⟩
    have hle := Nat.le_of_dvd (by norm_num) hdvd2
    omega
  · -- Case 2: `O(M)` moves a point, hence (primitive action) is transitive on `E`.
    have hfp : MulAction.fixedPoints ↥N E ≠ Set.univ := by
      intro h
      apply htriv
      intro x hx b
      have hb : b ∈ MulAction.fixedPoints ↥N E := by rw [h]; trivial
      have h1 := (MulAction.mem_fixedPoints.mp hb) ⟨x, hx⟩
      simpa [Subgroup.smul_def] using h1
    have hpp : MulAction.IsPreprimitive M E :=
      MulAction.isPreprimitive_of_is_two_pretransitive h2
    letI : MulAction.IsPreprimitive M E := hpp
    have hq : MulAction.IsQuasiPreprimitive M E := inferInstance
    have hNtr : MulAction.IsPretransitive ↥N E :=
      MulAction.IsQuasiPreprimitive.isPretransitive_of_normal (self := hq) hfp
    have horb : MulAction.orbit ↥N a = Set.univ :=
      (MulAction.isPretransitive_iff_orbit_eq_univ a).mp hNtr
    have hcardN : Nat.card ↥N = Nat.card E * Nat.card ↥(MulAction.stabilizer ↥N a) := by
      have h1 : Nat.card ↥(MulAction.orbit ↥N a) * Nat.card ↥(MulAction.stabilizer ↥N a)
          = Nat.card ↥N := by
        rw [← Nat.card_prod]
        exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥N a)
      rw [horb, Nat.card_coe_set_eq, Set.ncard_univ] at h1
      exact h1.symm
    have hdvd : Nat.card E ∣ Nat.card ↥N := ⟨_, hcardN⟩
    have hoddE : Odd (Nat.card E) :=
      Odd.of_dvd_nat (Work.BrauerSuzuki.OddCore.oddCard_oddCore (G := M)) hdvd
    -- `|M| = |E| · |H|` with both factors odd, contradicting the involution `z`.
    have hHindex : H.index = Nat.card E := by
      rw [hH, Subgroup.index]
      rw [← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer M a)]
      rw [MulAction.orbit_eq_univ M a, Nat.card_coe_set_eq, Set.ncard_univ]
    have hcardM : Nat.card ↥H * Nat.card E = Nat.card M := by
      rw [← hHindex]; exact Subgroup.card_mul_index H
    have hoddM : Odd (Nat.card M) := by
      rw [← hcardM]; exact Odd.mul hodd hoddE
    have h2dvdM : 2 ∣ Nat.card M := by
      have h := orderOf_dvd_natCard z
      rwa [hz2] at h
    exact (Nat.not_even_iff_odd.mpr hoddM) (even_iff_two_dvd.mpr h2dvdM)

end Work.ThreePoints
