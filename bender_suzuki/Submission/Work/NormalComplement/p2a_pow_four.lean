import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.isStronglyEmbedded_map_of_central_odd_ker
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3Sub.prop3b_support
import Submission.Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd
import Submission.Work.ThreePoints.Basic
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.NormalComplement.p2a_pow_four`

A `2`-element of `H ⊓ O^{2'}(C_G(A))` has order dividing `4`, where `A` is the subgroup of
`V = C_D(t)` of `Setup45A`.

Let `F = O^{2'}(C_G(A)) = p3F A`.  Ch. II §4 Prop. 3 at `X = A` (applicable because
`N_K(A) ⊇ C_K(A) ≠ 1`, from `|C_K(A)| = 2^p - 1 ≥ 3`) gives `O_{2'}(F) = Z(F)` and a surjection
`φ : F →* Y` with kernel `Z(F)` onto a simple Bender group `Y`.  Ch. II §4 Prop. 1 (b) at `X = A`
shows that `K₀ = (F ⊓ H).subgroupOf F` is strongly embedded in `F`; since `Z(F)` is central of odd
order, `Z(F) ≤ K₀` (a central element outside a strongly embedded subgroup would make `K₀ ⊓ K₀^z`
equal to `K₀`, of even order), so `K₀.map φ` is strongly embedded in `Y`
(`isStronglyEmbedded_map_of_central_odd_ker`).  Hence, by `BenderModelFacts2Prop` (1°),
`(φ x)^4 = 1` for every `2`-element `x ∈ K₀`, i.e. `x^4 ∈ Z(F)`.  But `x^4` has `2`-power order
while `Z(F) = O_{2'}(F)` has odd order, so `x^4 = 1`.

`p2aF`/`p2aK` below are the same objects as `p3F A` and `(p3F A ⊓ H).subgroupOf (p3F A)`, written
in the syntactic form in which `ChIIFourProp` produces them (its `let F`), so that `rw` finds them.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.NormalComplement

open Submission.Blueprint

/-- `F = O^{2'}(C_G(A)) = p3F A`, in the syntactic form in which `ChIIFourProp` produces it. -/
noncomputable abbrev p2aF {G : Type} [Group G] (A : Subgroup G) : Subgroup G :=
  Subgroup.map (Subgroup.centralizer (A : Set G)).subtype
    (oddResidual ↥(Subgroup.centralizer (A : Set G)))

/-- `K₀ = (F ⊓ H).subgroupOf F` for `F = O^{2'}(C_G(A))`: the strongly embedded subgroup of `F`
given by Ch. II §4 Prop. 1 (b) at `X = A`. -/
noncomputable abbrev p2aK {G : Type} [Group G] (H A : Subgroup G) : Subgroup ↥(p2aF A) :=
  (p2aF A ⊓ H).subgroupOf (p2aF A)

/-- Auxiliary: the hypothesis `N_K(A) ≠ 1` of Ch. II §4 Prop. 3 for `X = A`, deduced from
`|C_K(A)| = 2^p - 1 ≥ 3` (`Setup45A.A_CK`). -/
private theorem p2a_HasNonTrivialNK_A {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t,
      k ≠ 1 ∧ k ∈ Subgroup.normalizer (A : Set G) := by
  have hp2 : 2 ≤ p := h.prime.two_le
  have hcard : 3 ≤ (Work.NormalComplement.Design.CK H t A).ncard := by
    rw [h.A_CK]
    have h4 : 4 ≤ 2 ^ p := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp2
    omega
  obtain ⟨k, hk, hk1⟩ : ∃ k ∈ Work.NormalComplement.Design.CK H t A, k ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hsub : Work.NormalComplement.Design.CK H t A ⊆ ({1} : Set G) :=
      fun y hy => by simpa using hcon y hy
    have h1 : (Work.NormalComplement.Design.CK H t A).ncard ≤ 1 := by
      calc (Work.NormalComplement.Design.CK H t A).ncard ≤ ({1} : Set G).ncard :=
            Set.ncard_le_ncard hsub (Set.finite_singleton 1)
        _ = 1 := Set.ncard_singleton 1
    omega
  exact ⟨k, hk.1, hk1, Subgroup.centralizer_le_normalizer _ hk.2⟩

theorem p2a_pow_four (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    ∀ x : G, x ∈ H → x ∈ Work.ThreePoints.p3F A → (∃ k : ℕ, orderOf x = 2 ^ k) → x ^ 4 = 1 := by
  classical
  intro x hxH hxF hx2
  obtain ⟨k, hk⟩ := hx2
  have hxF' : x ∈ p2aF A := hxF
  -- ## Ch. II §4 Prop. 3 at `X = A`: the model quotient `F → Y = F/Z(F)`
  have hNK : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t,
      k ≠ 1 ∧ k ∈ Subgroup.normalizer (A : Set G) := p2a_HasNonTrivialNK_A h
  obtain ⟨hP1b, -, -, hP3clause, -, -⟩ := hC4 (G := G) h.sit H h.se t h.invol h.notMem
  have hP3 := hP3clause A h.A_ne h.A_le hNK
  obtain ⟨-, -, hmodel, -⟩ := hP3
  obtain ⟨hCenterEq, Y, hYgrp, φ, hφsurj, hφker, hYbend⟩ := hmodel
  letI : Group Y := hYgrp
  haveI : Finite Y := Finite.of_surjective φ hφsurj
  -- ## Ch. II §4 Prop. 1 (b) at `X = A`: `K₀` is strongly embedded in `F`
  have hKstrong : IsStronglyEmbedded (p2aK H A) := by
    have h1 := hP1b A (p2aF A)
      (Work.ThreePoints.three_le_ncard_fixedPts_of_le_centD h.se h.invol h.notMem h.A_le)
      (fun u hu => Work.ThreePoints.mem_p3F_of_involution hu.1 hu.2)
      (Work.ThreePoints.p3F_le_normalizer A) 1
      (by rw [Work.ThreePoints.conj_one]
          exact (Work.ThreePoints.le_of_le_centD h.A_le).1)
    rwa [Work.ThreePoints.conj_one] at h1
  -- ## `Z(F) = O_{2'}(F)` is central of odd order, hence inside `K₀`; `K₀ Z(F)/Z(F)` is
  -- strongly embedded in `Y`
  have hoddker : Odd (Nat.card ↥φ.ker) := by
    rw [hφker, ← hCenterEq]
    exact Work.BrauerSuzuki.OddCore.oddCard_oddCore
  have hcentker : φ.ker ≤ Subgroup.center ↥(p2aF A) := le_of_eq hφker
  have hbar : IsStronglyEmbedded ((p2aK H A).map φ) :=
    isStronglyEmbedded_map_of_central_odd_ker φ hφsurj hoddker hcentker hKstrong
  -- ## `BenderModelFacts2Prop` (1°): `2`-elements of a strongly embedded subgroup of a simple
  -- Bender group have order dividing `4`
  have hBM : ∀ y ∈ (p2aK H A).map φ, (∃ j : ℕ, orderOf y = 2 ^ j) → y ^ 4 = 1 :=
    (hMF2 Y hYbend ((p2aK H A).map φ) hbar).1
  -- ## The element `x` and its image in `Y`
  let xF : ↥(p2aF A) := ⟨x, hxF'⟩
  have hxK : xF ∈ p2aK H A := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨hxF', hxH⟩
  have hordF : orderOf xF = 2 ^ k := by
    rw [← Subgroup.orderOf_coe xF]
    exact hk
  have h2pow : ∃ j : ℕ, orderOf (φ xF) = 2 ^ j := by
    have hdvd : orderOf (φ xF) ∣ 2 ^ k := by
      have h := orderOf_map_dvd φ xF
      rwa [hordF] at h
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩
  have h4 : (φ xF) ^ 4 = 1 := hBM (φ xF) (Subgroup.mem_map_of_mem φ hxK) h2pow
  -- ## `x⁴ ∈ Z(F)`: it has both `2`-power order and odd order, so it is `1`
  have hker4 : xF ^ 4 ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, h4]
  have hcen4 : xF ^ 4 ∈ Subgroup.center ↥(p2aF A) := by
    rw [← hφker]
    exact hker4
  have hOddCenter : Odd (Nat.card ↥(Subgroup.center ↥(p2aF A))) := by
    rw [← hCenterEq]
    exact Work.BrauerSuzuki.OddCore.oddCard_oddCore
  have hoddord : Odd (orderOf (xF ^ 4)) := by
    have h := orderOf_dvd_natCard (⟨xF ^ 4, hcen4⟩ : ↥(Subgroup.center ↥(p2aF A)))
    have h2 := Subgroup.orderOf_coe (⟨xF ^ 4, hcen4⟩ : ↥(Subgroup.center ↥(p2aF A)))
    rw [← h2] at h
    exact Odd.of_dvd_nat hOddCenter h
  have h2ord : ∃ j : ℕ, orderOf (xF ^ 4) = 2 ^ j := by
    have hdvd : orderOf (xF ^ 4) ∣ 2 ^ k := by
      have h := orderOf_pow_dvd (x := xF) 4
      rwa [hordF] at h
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩
  have hz1 : xF ^ 4 = 1 := by
    obtain ⟨j, hj⟩ := h2ord
    have hodd2 : Odd (2 ^ j) := hj ▸ hoddord
    have h1 : orderOf (xF ^ 4) = 1 := by
      rw [hj]
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [h0, pow_zero]
      · exfalso
        have hdvd : 2 ∣ 2 ^ j := by
          simpa using pow_dvd_pow (2 : ℕ) (show 1 ≤ j by omega)
        exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr hdvd)) hodd2
    exact orderOf_eq_one_iff.mp h1
  have hcoe : (xF : G) ^ 4 = 1 := by
    have h := congrArg (Subtype.val) hz1
    simpa [Subgroup.coe_pow] using h
  simpa using hcoe

end Work.NormalComplement
