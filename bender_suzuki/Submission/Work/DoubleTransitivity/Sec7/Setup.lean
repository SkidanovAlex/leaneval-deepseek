import Mathlib
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.DoubleTransitivity.Sec1.unique_fixed
import Submission.Work.DoubleTransitivity.Sec2.prop1a_exists
import Submission.Work.DoubleTransitivity.Sec2.prop2
import Submission.Work.DoubleTransitivity.Sec4.RpDefs
import Submission.Work.DoubleTransitivity.Sec4.RpHelpers
import Submission.Work.ThreePoints.Basic
import Submission.Work.ThreePoints.Sec2b

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec7.Setup`

Small structural lemmas used in the final assembly of Theorem A (Peterfalvi I Ch. I §6):

* `exists_involution_notMem` : a strongly embedded subgroup has an involution outside it;
* `exists_involution_conj_stabilizer` : the stabiliser of any point of `Ω = G ⧸ H` is carried to
  `H` by an involution (so a conjugate base can be conjugated back);
* `inv_card_odd` : `n = |Inv H|` is odd;
* `rp_to_maxFixesThree` : `𝓡_p ≠ ∅` produces a maximal `p`-subgroup fixing three points which
  contains a `p`-Sylow of a two-point stabiliser.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.DoubleTransitivity.Sec7

variable {G : Type} [Group G]

/-- A strongly embedded subgroup `H ≠ ⊤` has an involution outside it: conjugate an involution of
`H` by an element outside `H`; the conjugate cannot lie in `H` (else `H ∩ H^g` would have even
order). -/
theorem exists_involution_notMem [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) :
    ∃ t : G, orderOf t = 2 ∧ t ∉ H := by
  obtain ⟨hne, hB⟩ := (isStronglyEmbedded_iff H).mp hH
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ H := by
    by_contra h
    push_neg at h
    exact hne ((Subgroup.eq_top_iff' H).mpr h)
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 2 hB.1
  have hv2 : orderOf ((v : ↥H) : G) = 2 := (Subgroup.orderOf_coe v).trans hv
  refine ⟨g⁻¹ * (v : G) * g, ?_, ?_⟩
  · have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) ((v : ↥H) : G)
    rw [hv2] at h
    simpa [MulAut.conj_apply] using h
  · intro hmem
    have hvconj : ((v : ↥H) : G) ∈ conj g H := by
      rw [mem_conj]
      show g⁻¹ * ((v : ↥H) : G) * g ∈ H
      exact hmem
    have hmem' : ((v : ↥H) : G) ∈ H ⊓ conj g H := ⟨v.2, hvconj⟩
    have hdvd : 2 ∣ Nat.card ↥(H ⊓ conj g H) :=
      dvd_trans (by rw [Nat.card_zpowers, hv2])
        (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hmem'))
    exact hB.2 g hg hdvd

/-- The stabiliser of any point `ω` of `Ω = G ⧸ H` is carried to `H` by an involution.  (Used to
conjugate the base of the §6 argument — a point of `Ω_P` — back to the given strongly embedded
subgroup.) -/
theorem exists_involution_conj_stabilizer [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {s : G} (hs : orderOf s = 2)
    (hsH : s ∉ H) {ω : G ⧸ H} (hω : s • ω = ω) :
    ∃ t : G, orderOf t = 2 ∧ Submission.Blueprint.conj t (MulAction.stabilizer G ω) = H := by
  have hB : IsBender H := (isStronglyEmbedded_iff H).mp hH |>.2
  -- an involution `v ∈ H`
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 2 hB.1
  have hv2 : orderOf ((v : ↥H) : G) = 2 := (Subgroup.orderOf_coe v).trans hv
  have hvH : ((v : ↥H) : G) ∈ H := v.2
  -- it fixes `pt H`, which is not `ω`
  have hpt_v : ((v : ↥H) : G) • (pt H) = pt H := by
    rw [smul_pt]
    exact mk_one_eq_iff.mpr hvH
  have hω_ne : ω ≠ pt H := by
    intro h
    have h1 : s • (pt H) = pt H := by rw [← h]; exact hω
    rw [smul_pt] at h1
    exact hsH (mk_one_eq_iff.mp h1)
  -- `v` and `s` have no common fixed point
  have hno : ¬ ∃ ω' : Omega H, ((v : ↥H) : G) • ω' = ω' ∧ s • ω' = ω' := by
    rintro ⟨ω', h1, h2⟩
    have e1 : ω' = pt H := Sec1.eq_of_smul_eq_of_orderOf_eq_two hB hv2 h1 hpt_v
    have e2 : ω' = ω := Sec1.eq_of_smul_eq_of_orderOf_eq_two hB hs h2 hω
    exact hω_ne (e2 ▸ e1)
  obtain ⟨u, hu2, huconj, -, -⟩ := Sec2.prop1a_exists hB hv2 hs hno
  -- `v = u s u⁻¹`, hence `v` fixes `u • ω`, so `u • ω = pt H`
  have hvu : ((v : ↥H) : G) * u = u * s := by
    rw [← huconj]; group
  have hfix : ((v : ↥H) : G) • (u • ω) = u • ω := by
    rw [← mul_smul, hvu, mul_smul, hω]
  have huniq : u • ω = pt H := Sec1.eq_of_smul_eq_of_orderOf_eq_two hB hv2 hfix hpt_v
  have hstab : MulAction.stabilizer G (pt H) = H :=
    Work.DoubleTransitivity.Sec4.stabilizer_pt_eq H
  have hconj := MulAction.stabilizer_smul_eq_stabilizer_map_conj u ω
  refine ⟨u, hu2, ?_⟩
  change (MulAction.stabilizer G ω).map (MulAut.conj u).toMonoidHom = H
  rw [← hconj, huniq, hstab]

/-- `n = |Inv H|` is odd (Peterfalvi I Ch. I §2: `n = |J(D,t)|`, a set closed under inversion
and contained in the odd-order group `D`). -/
theorem inv_card_odd [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) :
    Odd (Submission.Blueprint.involutions (H : Set G)).ncard := by
  obtain ⟨t, ht, htH⟩ := exists_involution_notMem hH
  have hB : IsBender H := (isStronglyEmbedded_iff H).mp hH |>.2
  have hne : H ≠ ⊤ := ((isStronglyEmbedded_iff H).mp hH).1
  have h1 : Nat.card (twoPoint H t) =
      Nat.card (centD H t : Subgroup G) * (invertedBy (twoPoint H t) t).ncard :=
    Work.ThreePoints.card_twoPoint_eq_card_centD_mul_ncard_invertedBy hH ht htH
  have hodd2 : Odd (Nat.card (twoPoint H t)) :=
    Work.ThreePoints.IsStronglyEmbedded.odd_card_inf_conj hH htH
  have hoddprod : Odd (Nat.card (centD H t : Subgroup G) *
      (invertedBy (twoPoint H t) t).ncard) := by
    rw [← h1]; exact hodd2
  have hoddK : Odd (invertedBy (twoPoint H t) t).ncard := (Nat.odd_mul.mp hoddprod).2
  have hk : (invertedBy (twoPoint H t) t).ncard =
      (Submission.Blueprint.involutions (H : Set G)).ncard :=
    (Sec2.prop2 hB hne ht htH).2.1
  rwa [← hk]

/-- `𝓡_p ≠ ∅` produces a `p`-subgroup maximal among those fixing at least three points, which
contains a `p`-Sylow of a two-point stabiliser. -/
theorem rp_to_maxFixesThree [Finite G] (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    (h4 : Submission.Blueprint.HasFourGroup G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hRp : Work.DoubleTransitivity.Sec4.Rp p H) :
    ∃ P : Subgroup G, Work.DoubleTransitivity.MaxFixesThree p H P ∧
      Work.DoubleTransitivity.Sec4.TwoPointSylowData p H P := by
  obtain ⟨ω₁, ω₂, hω₂₁, P₀, hP₀syl, hP₀even⟩ := hRp
  have hB : IsBender H := (isStronglyEmbedded_iff H).mp hH |>.2
  have hP₀p : IsPGroup p P₀ := hP₀syl.2.1
  have hω₁ : ω₁ ∈ fixedPts H P₀ :=
    Work.DoubleTransitivity.Sec4.mem_fixedPts_iff_le_stabilizer_aux.mpr
      (le_trans hP₀syl.1 inf_le_left)
  have hω₂ : ω₂ ∈ fixedPts H P₀ :=
    Work.DoubleTransitivity.Sec4.mem_fixedPts_iff_le_stabilizer_aux.mpr
      (le_trans hP₀syl.1 inf_le_right)
  have h2 : 2 ≤ (fixedPts H P₀).ncard := by
    have hsub : ({(ω₁ : Omega H), ω₂} : Set (Omega H)) ⊆ fixedPts H P₀ := by
      intro ω hω
      rcases hω with rfl | rfl
      · exact hω₁
      · exact hω₂
    have := Set.ncard_le_ncard hsub
    rwa [Set.ncard_pair (Ne.symm hω₂₁)] at this
  have h3 : 3 ≤ (fixedPts H P₀).ncard :=
    Work.DoubleTransitivity.Sec4.three_le_fixedPts_of_even_normalizer hB hω₁ hP₀even h2
  obtain ⟨P, hP₀P, hPmax⟩ :=
    Work.DoubleTransitivity.Sec4.exists_maxFixesThree_le (p := p) (H := H) (Q₀ := P₀)
      ⟨P₀, hP₀p, h3, le_rfl⟩
  exact ⟨P, hPmax, ⟨ω₁, ω₂, hω₂₁, P₀, hP₀syl, hP₀P⟩⟩

end Work.DoubleTransitivity.Sec7
