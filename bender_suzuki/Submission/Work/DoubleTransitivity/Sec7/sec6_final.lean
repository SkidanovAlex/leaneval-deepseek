import Mathlib
import Submission.Work.DoubleTransitivity.Sec7.Setup
import Submission.Work.DoubleTransitivity.Sec7.Sec4Aux
import Submission.Work.DoubleTransitivity.Sec7.ConjTransport
import Submission.Work.DoubleTransitivity.Sec6.prop1
import Submission.Work.DoubleTransitivity.Sec6.prop2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec7.sec6_final`

Peterfalvi I, Ch. I §6, the final argument of the proof of Theorem A (pp. 161–162).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.DoubleTransitivity.Sec7

/-- The closure of `invertedBy P u` is normalised by `u` (which inverts each of its elements). -/
theorem closure_invertedBy_normalizer {G : Type} [Group G] {P : Subgroup G} {u : G} :
    u ∈ Subgroup.normalizer
      (Subgroup.closure (Submission.Blueprint.invertedBy P u) : Set G) := by
  let f : G →* G := MulAut.conj u
  have hf : ∀ x : G, f x = u * x * u⁻¹ := fun x => by
    show MulAut.conj u x = u * x * u⁻¹
    rw [MulAut.conj_apply]
  have key : f '' Submission.Blueprint.invertedBy P u = Submission.Blueprint.invertedBy P u := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      rw [← hxy]
      have hyy : f y = y⁻¹ := by rw [hf]; exact hy.2
      rw [hyy]
      exact ⟨P.inv_mem hy.1, by
        show u * y⁻¹ * u⁻¹ = (y⁻¹)⁻¹
        calc u * y⁻¹ * u⁻¹ = (u * y * u⁻¹)⁻¹ := by group
          _ = (y⁻¹)⁻¹ := by rw [hy.2]⟩
    · intro hx
      refine ⟨x⁻¹, ⟨P.inv_mem hx.1, ?_⟩, ?_⟩
      · show u * x⁻¹ * u⁻¹ = (x⁻¹)⁻¹
        calc u * x⁻¹ * u⁻¹ = (u * x * u⁻¹)⁻¹ := by group
          _ = (x⁻¹)⁻¹ := by rw [hx.2]
      · rw [hf]
        calc u * x⁻¹ * u⁻¹ = (u * x * u⁻¹)⁻¹ := by group
          _ = (x⁻¹)⁻¹ := by rw [hx.2]
          _ = x := inv_inv x
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change Subgroup.map f (Subgroup.closure (Submission.Blueprint.invertedBy P u)) =
    Subgroup.closure (Submission.Blueprint.invertedBy P u)
  rw [MonoidHom.map_closure, key]

/-- **Peterfalvi I, Ch. I §6, final argument** (p. 161–162). -/
theorem sec6_final {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hZJ : Submission.Blueprint.GlaubermanZJProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {K : Subgroup G} (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K)
    (h4 : Submission.Blueprint.HasFourGroup G)
    (hInd : Work.DoubleTransitivity.ThmAForBelow (Nat.card G))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : Work.DoubleTransitivity.MaxFixesThree p K P) (hPK : P ≤ K)
    (hTP : Work.DoubleTransitivity.Sec4.TwoPointSylowData p K P)
    {u : G} (hu : u ∈ Submission.Blueprint.involutions (K : Set G))
    (huN : u ∈ Subgroup.normalizer (P : Set G))
    (hnc : ¬ ∀ x ∈ P, u * x * u⁻¹ = x) :
    Submission.Blueprint.IsTwoTransitiveOn K := by
  classical
  haveI : Fintype (G ⧸ K) := Fintype.ofFinite _
  have hB : IsBender K := (isStronglyEmbedded_iff K).mp hK |>.2
  have hstab : MulAction.stabilizer G (pt K) = K :=
    Work.DoubleTransitivity.Sec4.stabilizer_pt_eq K
  -- ## §6 Proposition 2
  obtain ⟨F, hFse, hFs⟩ := Sec6.prop2 hFT hBrSz hK hp hp2 hP hPK hu huN hnc
  -- ## Minimisation over the fixed points of the involutions of `F` outside `K`
  let W : Set (G ⧸ K) := {ω | ∃ s : G, s ∈ F ∧ orderOf s = 2 ∧ s ∉ K ∧ s • ω = ω}
  let val : (G ⧸ K) → ℕ := fun ω => Nat.card ↥(pPrimeCoreSub p (MulAction.stabilizer G ω ⊓ K))
  have hWne : W.Nonempty := by
    obtain ⟨s, hs2, hsnot⟩ :=
      exists_involution_notMem (G := ↥F) (H := (K ⊓ F).subgroupOf F) hFse
    have hs2' : orderOf ((s : ↥F) : G) = 2 := (Subgroup.orderOf_coe s).trans hs2
    have hsK : ((s : ↥F) : G) ∉ K := fun hc => hsnot ⟨hc, s.2⟩
    obtain ⟨ω, hω, -⟩ := Sec1.unique_fixed hB hs2'
    exact ⟨ω, _, s.2, hs2', hsK, hω⟩
  have hWfin : W.Finite := Set.toFinite W
  obtain ⟨ωs, hωsfin, hmin⟩ := Finset.exists_min_image hWfin.toFinset val
    ⟨hWne.choose, (Set.Finite.mem_toFinset hWfin).mpr hWne.choose_spec⟩
  obtain ⟨s, hsF, hs2, hsK, hωs⟩ := (Set.Finite.mem_toFinset hWfin).mp hωsfin
  -- §6 Prop. 2 clause for `s` and its fixed point `ωs`
  obtain ⟨hFs1, hFs2⟩ := hFs s ⟨hsF, hs2⟩ ωs hωs
  -- ## The two-point stabiliser `D = K(s) ⊓ K`
  let K' : Subgroup G := MulAction.stabilizer G ωs
  set D : Subgroup G := K' ⊓ K with hD
  have hK'se : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K' :=
    Work.ThreePoints.S4Prop2.isStronglyEmbedded_stabilizer hK ωs
  have hKsne : K' ≠ K := by
    intro hcontra
    exact hsK (hcontra ▸ MulAction.mem_stabilizer_iff.mpr hωs)
  have hsgK' : s ∈ K' := MulAction.mem_stabilizer_iff.mpr hωs
  -- ## The exchanging involution `τ`
  obtain ⟨τ, hτ2, hτconj⟩ := exists_involution_conj_stabilizer hK hs2 hsK hωs
  have htt : τ * τ = 1 := by
    have h := pow_orderOf_eq_one τ; rw [hτ2] at h; simpa [pow_two] using h
  have hτconjK : Submission.Blueprint.conj τ K = K' := by
    rw [← hτconj, ← Work.ThreePoints.conj_mul, htt, Work.ThreePoints.conj_one]
  have hτK : τ ∉ K := by
    intro hc
    rw [← Work.ThreePoints.IsStronglyEmbedded.normalizer_eq hK] at hc
    have h1 : Submission.Blueprint.conj τ K = K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hc
    exact hKsne (hτconjK.symm.trans h1)
  have hτK' : τ ∉ K' := by
    intro hc
    rw [← Work.ThreePoints.IsStronglyEmbedded.normalizer_eq hK'se] at hc
    have h1 : Submission.Blueprint.conj τ K' = K' :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hc
    exact hKsne ((hτconj.symm.trans h1).symm)
  -- ## Appendix I (3)(e) with `P₀ = ⟨invertedBy P u⟩` and `u ∈ Inv(K)`
  have huo : (Submission.Blueprint.involutions (K : Set G)).ncard.factorization p ≤
      (conjOrbit (Subgroup.closure (Submission.Blueprint.invertedBy P u)) u).ncard.factorization p := by
    have hPodd : Odd (Nat.card ↥P) :=
      Work.DoubleTransitivity.Sec4.l2p1_odd_card_of_isPGroup_of_odd_prime hp hp2 hP.1
    have hu2 : orderOf u = 2 := hu.2
    have hJobP : Subgroup.closure (Submission.Blueprint.invertedBy P u) ≤ P :=
      (Subgroup.closure_le P).mpr (fun x hx => hx.1)
    have hJobp : IsPGroup p (Subgroup.closure (Submission.Blueprint.invertedBy P u)) :=
      hP.1.to_le hJobP
    have hJobodd : Odd (Nat.card ↥(Subgroup.closure
        (Submission.Blueprint.invertedBy P u))) :=
      Work.DoubleTransitivity.Sec4.l2p1_odd_card_of_isPGroup_of_odd_prime hp hp2 hJobp
    have h1 : (Submission.Blueprint.invertedBy
          (Subgroup.closure (Submission.Blueprint.invertedBy P u)) u).ncard =
        (conjOrbit (Subgroup.closure (Submission.Blueprint.invertedBy P u)) u).ncard :=
      Work.ThreePoints.S4Prop2.ncard_invertedBy_eq_ncard_conjOrbit hu2 hJobodd
        (closure_invertedBy_normalizer (P := P) (u := u))
    have h2 : (Submission.Blueprint.invertedBy P u).ncard = (conjOrbit P u).ncard :=
      Work.ThreePoints.S4Prop2.ncard_invertedBy_eq_ncard_conjOrbit hu2 hPodd huN
    have hsub : (Submission.Blueprint.invertedBy P u).ncard ≤
        (Submission.Blueprint.invertedBy
          (Subgroup.closure (Submission.Blueprint.invertedBy P u)) u).ncard :=
      Set.ncard_le_ncard (fun x hx => ⟨Subgroup.subset_closure hx, hx.2⟩)
    have h3 : p ^ ((Submission.Blueprint.involutions (K : Set G)).ncard.factorization p) ≤
        (conjOrbit (Subgroup.closure (Submission.Blueprint.invertedBy P u)) u).ncard := by
      rw [← h1]
      calc p ^ ((Submission.Blueprint.involutions (K : Set G)).ncard.factorization p)
          ≤ (conjOrbit P u).ncard := conjOrbit_ge hBrSz hK hp hp2 hP hPK hTP hu
        _ = (Submission.Blueprint.invertedBy P u).ncard := h2.symm
        _ ≤ (Submission.Blueprint.invertedBy
              (Subgroup.closure (Submission.Blueprint.invertedBy P u)) u).ncard := hsub
    rw [Work.ThreePoints.S4Prop2.L2P1aux.card_conjOrbit_eq_pow_sub hp hJobp
        (closure_invertedBy_normalizer (P := P) (u := u))] at h3
    rw [Work.ThreePoints.S4Prop2.L2P1aux.card_conjOrbit_eq_pow_sub hp hJobp
        (closure_invertedBy_normalizer (P := P) (u := u)),
      Work.ThreePoints.S4Prop2.L2P1aux.factorization_pow_self hp]
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h3
  have htwoPointKD : Submission.Blueprint.twoPoint K τ = D := by
    rw [Submission.Blueprint.twoPoint, hτconjK, hD]
    exact inf_comm _ _
  have hregK : Work.DoubleTransitivity.IsRegularIntersection p D K := by
    have h := Work.ThreePoints.S4Prop2.L2P1aux.isRegularIntersection_of_invariant hK hp
      hτ2 hτK ⟨Subgroup.closure (Submission.Blueprint.invertedBy P u), ?_, ?_, u, hu, ?_, huo⟩
    · rwa [htwoPointKD] at h
    · rw [Submission.Blueprint.twoPoint, hτconjK]
      exact le_inf ((Subgroup.closure_le K).mpr
        (fun x hx => hPK ((Work.ThreePoints.mem_invertedBy.mp hx).1)))
        ((Subgroup.closure_le (MulAction.stabilizer G ωs)).mpr
          (fun x hx => MulAction.mem_stabilizer_iff.mpr (hFs1 x hx)))
    · exact hP.1.to_le ((Subgroup.closure_le P).mpr
        (fun x hx => (Work.ThreePoints.mem_invertedBy.mp hx).1))
    · exact closure_invertedBy_normalizer
  -- ## `(D,K') ∈ 𝓡_p`, transporting along `τ`
  have htwoPointK' : Submission.Blueprint.twoPoint K' τ = D := by
    rw [Submission.Blueprint.twoPoint, hτconj, hD]
  have hreg : Work.DoubleTransitivity.IsRegularIntersection p
      (Submission.Blueprint.twoPoint K' τ) K' := by
    rw [htwoPointK']
    obtain ⟨Q, hQsyl, hQeven⟩ := hregK
    have hDτ : Submission.Blueprint.conj τ D = D := by
      rw [hD, Work.ThreePoints.conj_inf, hτconj, hτconjK]
      exact inf_comm _ _
    refine ⟨Submission.Blueprint.conj τ Q, ?_, ?_⟩
    · rw [← hDτ]
      exact IsSylowSubgroupOf.conj τ hQsyl
    · have hN : Subgroup.normalizer (Submission.Blueprint.conj τ Q : Set G) =
          Submission.Blueprint.conj τ (Subgroup.normalizer (Q : Set G)) :=
        (Subgroup.map_normalizer_eq_of_bijective Q
          (f := (MulAut.conj τ).toMonoidHom) (MulAut.conj τ).bijective).symm
      have hstep : Subgroup.normalizer (Submission.Blueprint.conj τ Q : Set G) ⊓ K' =
          Submission.Blueprint.conj τ (Subgroup.normalizer (Q : Set G) ⊓ K) := by
        rw [hN, Work.ThreePoints.conj_inf, hτconjK]
      rw [hstep, Subgroup.card_map_of_injective (MulAut.conj τ).injective]
      exact hQeven
  -- ## Chapter I §6 Proposition 1
  have hsgInv : s ∈ Submission.Blueprint.involutions (K' : Set G) := ⟨hsgK', hs2⟩
  have hprop := Sec6.prop1 hFT hZJ hBrSz hInd hK'se h4 hτ2 hτK' hp hp2 hreg hsgInv
  have hprop1 : pPrimeCoreSub p (D ⊓ Submission.Blueprint.conj s D) ≤
      pPrimeCoreSub p D := by
    have hh := hprop.1
    rwa [htwoPointK'] at hh
  have hprop2 : pPrimeCoreSub p (D ⊓ Submission.Blueprint.conj s D) =
      pPrimeCoreSub p D → Submission.Blueprint.IsTwoTransitiveOn K' := by
    intro hh
    exact hprop.2 (by rwa [htwoPointK'])
  -- ## The first inclusion (Prop. 2 (b))
  have hIncl1 : pPrimeCoreSub p (K ⊓ Submission.Blueprint.conj s K) ≤
      pPrimeCoreSub p (D ⊓ Submission.Blueprint.conj s D) := by
    have hconjStab : Submission.Blueprint.conj s K' = K' :=
      (Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj s ωs).symm.trans
        (congrArg (MulAction.stabilizer G) hωs)
    have hDconj : D ⊓ Submission.Blueprint.conj s D =
        K' ⊓ K ⊓ Submission.Blueprint.conj s K := by
      rw [hD, Work.ThreePoints.conj_inf, hconjStab]
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    rw [hDconj]
    exact hFs2
  -- ## The minimality comparison, via `v = s w s` (`w` an involution of `K ⊓ F`)
  have hcmp : Nat.card ↥(pPrimeCoreSub p D) ≤
      Nat.card ↥(pPrimeCoreSub p (K ⊓ Submission.Blueprint.conj s K)) := by
    obtain ⟨wf, hwf2⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥((K ⊓ F).subgroupOf F)) 2 (even_iff_two_dvd.mp hFse.2.1)
    have hwf2' : orderOf ((wf : ↥F)) = 2 := (Subgroup.orderOf_coe wf).trans hwf2
    have hwf2G : orderOf (((wf : ↥F) : G)) = 2 := (Subgroup.orderOf_coe (wf : ↥F)).trans hwf2'
    have hwfK : ((wf.1 : ↥F) : G) ∈ K := by
      have h : ((wf.1 : ↥F) : G) ∈ (K ⊓ F) := Subgroup.mem_subgroupOf.mp wf.2
      exact h.1
    have hwfix : ((wf : ↥F) : G) • (pt K) = pt K := by
      rw [smul_pt]; exact mk_one_eq_iff.mpr hwfK
    have hss : s * s = 1 := by
      have h := pow_orderOf_eq_one s; rw [hs2] at h; simpa [pow_two] using h
    have hww : ((wf : ↥F) : G) * ((wf : ↥F) : G) = 1 := by
      have h := pow_orderOf_eq_one (((wf : ↥F) : G)); rw [hwf2G] at h
      simpa [pow_two] using h
    have hv2 : orderOf (s * ((wf : ↥F) : G) * s) = 2 := by
      have h1 : s * ((wf : ↥F) : G) * s = MulAut.conj s ((wf : ↥F) : G) := by
        rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_right hss]
      rw [h1]
      exact (MulEquiv.orderOf_eq (MulAut.conj s) ((wf : ↥F) : G)).trans hwf2G
    have hvfix : (s * ((wf : ↥F) : G) * s) • (s • pt K) = s • pt K := by
      rw [← mul_smul]
      rw [show s * ((wf : ↥F) : G) * s * s = s * ((wf : ↥F) : G) from by
        rw [mul_assoc, hss, mul_one]]
      rw [mul_smul, hwfix]
    have hvF : (s * ((wf : ↥F) : G) * s) ∈ F :=
      F.mul_mem (F.mul_mem hsF ((wf : ↥F).2)) hsF
    have hvK : (s * ((wf : ↥F) : G) * s) ∉ K := by
      intro hc
      have h1 : (s * ((wf : ↥F) : G) * s) • (pt K) = pt K := by
        rw [smul_pt]; exact mk_one_eq_iff.mpr hc
      have h2 : pt K = s • pt K := Sec1.eq_of_smul_eq_of_orderOf_eq_two hB hv2 h1 hvfix
      rw [smul_pt] at h2
      exact hsK (mk_one_eq_iff.mp h2.symm)
    have hωvW : s • pt K ∈ W := ⟨s * ((wf : ↥F) : G) * s, hvF, hv2, hvK, hvfix⟩
    have hminv : val ωs ≤ val (s • pt K) :=
      hmin (s • pt K) ((Set.Finite.mem_toFinset hWfin).mpr hωvW)
    have hStabV : MulAction.stabilizer G (s • pt K) = Submission.Blueprint.conj s K := by
      rw [Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj s (pt K), hstab]
    have hvs : val (s • pt K) =
        Nat.card ↥(pPrimeCoreSub p (K ⊓ Submission.Blueprint.conj s K)) := by
      show Nat.card ↥(pPrimeCoreSub p (MulAction.stabilizer G (s • pt K) ⊓ K)) = _
      rw [hStabV, inf_comm]
    calc Nat.card ↥(pPrimeCoreSub p D) = val ωs := rfl
      _ ≤ val (s • pt K) := hminv
      _ = _ := hvs
  -- ## The chain of inclusions and cardinalities
  have hcard1 : Nat.card ↥(pPrimeCoreSub p (D ⊓ Submission.Blueprint.conj s D)) ≤
      Nat.card ↥(pPrimeCoreSub p D) :=
    Work.ThreePoints.S4Prop2.L2P1aux.card_le_card_of_le hprop1
  have hcard2 : Nat.card ↥(pPrimeCoreSub p (K ⊓ Submission.Blueprint.conj s K)) ≤
      Nat.card ↥(pPrimeCoreSub p (D ⊓ Submission.Blueprint.conj s D)) :=
    Work.ThreePoints.S4Prop2.L2P1aux.card_le_card_of_le hIncl1
  have heqcard : Nat.card ↥(pPrimeCoreSub p (D ⊓ Submission.Blueprint.conj s D)) =
      Nat.card ↥(pPrimeCoreSub p D) := le_antisymm hcard1 (le_trans hcmp hcard2)
  have heqsub : pPrimeCoreSub p (D ⊓ Submission.Blueprint.conj s D) = pPrimeCoreSub p D :=
    Subgroup.eq_of_le_of_card_ge hprop1 (le_of_eq heqcard.symm)
  have h2t : Submission.Blueprint.IsTwoTransitiveOn K' := hprop2 heqsub
  -- ## Transport back to `K`
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective ωs
  have h2t' : Submission.Blueprint.IsTwoTransitiveOn (Submission.Blueprint.conj x K) := by
    rw [← Work.ThreePoints.stabilizer_mk]
    exact h2t
  exact conj_IsTwoTransitiveOn x h2t'

end Work.DoubleTransitivity.Sec7
