import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Sec2
import Submission.Work.ThreePoints.involutions_conj_of_stronglyEmbedded
import Submission.Work.ThreePoints.exists_involution_conj_of_odd_orderOf_mul
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup
import Submission.Work.DoubleTransitivity.App1.app1_1b
import Submission.Work.ThreePoints.ThmC.coprime_generation
import Submission.Work.ThreePoints.ThmC.step1_pPrimeCore
import Submission.Work.ThreePoints.ThmC.app3_consequence
import Submission.Work.ThreePoints.ThmC.exists_fixed_of_odd_ncard
import Submission.Work.ThreePoints.ThmC.odd_ncard_of_unique_fixed
import Submission.Work.ThreePoints.ThmC.mem_or_exists_mul_of_mem_closure
import Submission.Work.ThreePoints.ThmC.pPrimeCoreSub_conj
import Submission.Work.DoubleTransitivity.Sec2.inv_class

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.ThreePoints.ThmC

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G]

/-- The conjugate of a strongly embedded subgroup containing an involution is unique. -/
theorem eq_conj_of_mem_of_orderOf_eq_two {H : Subgroup G} (hH : IsStronglyEmbedded H) {g₁ g₂ : G}
    {s : G} (hs : orderOf s = 2) (h₁ : s ∈ conj g₁ H) (h₂ : s ∈ conj g₂ H) :
    conj g₁ H = conj g₂ H := by
  have hdvd : 2 ∣ Nat.card (conj g₁ H ⊓ conj g₂ H : Subgroup G) := by
    have hle : Subgroup.zpowers s ≤ conj g₁ H ⊓ conj g₂ H :=
      le_inf (Subgroup.zpowers_le.mpr h₁) (Subgroup.zpowers_le.mpr h₂)
    have h := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, hs] at h
  exact Work.ThreePoints.conj_eq_of_even_card_inf hH (even_iff_two_dvd.mpr hdvd)

/-- A proper strongly embedded subgroup does not contain all involutions. -/
theorem exists_involution_notMem_of_stronglyEmbedded {X : Type} [Group X] [Finite X]
    {M : Subgroup X} (hM : IsStronglyEmbedded M) : ∃ s : X, orderOf s = 2 ∧ s ∉ M := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨g, hg⟩ : ∃ g : X, g ∉ M := by
    by_contra h
    exact Work.ThreePoints.IsStronglyEmbedded.ne_top hM ((Subgroup.eq_top_iff' M).mpr fun x => by
      by_contra hx
      exact h ⟨x, hx⟩)
  obtain ⟨w, hw2⟩ : ∃ w : M, orderOf w = 2 :=
    exists_prime_orderOf_dvd_card' (G := ↥M) 2 (even_iff_two_dvd.mp (Work.ThreePoints.IsStronglyEmbedded.even_card hM))
  have hwX : orderOf ((w : M) : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hw2
  have ho2 : orderOf (g⁻¹ * (w : M) * g) = 2 := by
    have h1 := (MulAut.conj g⁻¹).orderOf_eq ((w : M) : X)
    rw [MulAut.conj_apply] at h1
    simpa only [inv_inv] using h1.trans hwX
  have hmemMul : g⁻¹ * (w : M) * g ∈ M := hcon _ ho2
  have hmem : g⁻¹ * (w : M) * g ∈ M ⊓ conj g⁻¹ M :=
    ⟨hmemMul, Subgroup.mem_map.mpr ⟨(w : M), (w : M).2, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩⟩
  have h2 : 2 ∣ Nat.card (M ⊓ conj g⁻¹ M : Subgroup X) := by
    have hdvd := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hmem)
    rwa [Nat.card_zpowers, ho2] at hdvd
  exact (Nat.not_even_iff_odd.mpr
      (Work.ThreePoints.IsStronglyEmbedded.odd_card_inf_conj hM (x := g⁻¹) (by simpa using hg)))
    (even_iff_two_dvd.mpr h2)

/-- **Peterfalvi I Ch. I §6 Proposition 2 (p. 160), the consequence used in Ch. II §3.**

Let `H` be strongly embedded in the finite group `G` of 2-rank `≥ 2`, `P` a `p`-subgroup (`p` odd)
maximal among those fixing at least three points of `Ω = G ⧸ H`, with `P ≤ H`, and let `u ∈ Inv(H)`
normalise `P` but not centralise it.  Then there is an involution `s ∉ H` such that, for the (unique)
point `ω` of `Ω` fixed by `s`,

`O_{p'}(H ∩ H^s) ≤ O_{p'}(Stab_G(ω) ∩ H ∩ H^s)`

(`pPrimeCoreSub p X = O_{p'}(X)` as a subgroup of `G`; `H^s = conj s H` is the stabiliser of the
point `s • H`, which is *not* the point fixed by `s`).

Source: Prop. 2 produces `F ≤ G` with `F ∩ H` a proper Bender group of `F` and, for `s ∈ Inv(F)`,
`K = J(P,u) ⊆ H(s)` and `O_{p'}(H ∩ H^s) ⊆ O_{p'}(H(s) ∩ H ∩ H^s)`; the statement above drops the
`K ⊆ H(s)` clause and the description of `F`, which is all the requester needs.

The source's proof of Prop. 2 (Steps 1–3, pp. 160–161) consumes Ch. I §6 Lemma 2 (a coprime-action
generation statement), Ch. I §4 Prop. 2 (available as
`Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup`, which needs `HasFourGroup`,
`ThmAProp` and `BrauerSuzukiProp`) and Ch. I §2 Prop. 1/2 and Lemma 2 (`Work.ThreePoints.ch1_lem2`,
`twoPoint_transitive_on_involutions`, `involutions_conj_of_stronglyEmbedded`); it also needs
Peterfalvi Appendix III (1) (`Work.ThreePoints.ThmC.app3_1`, being proved in parallel). -/
theorem ch1_sec6_prop2 {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hA : Submission.Blueprint.ThmAProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hfour : Submission.Blueprint.HasFourGroup G)
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) {P : Subgroup G}
    (hP : Work.ThreePoints.ThmC.IsMaxP3 H p P) (hPH : P ≤ H) {u : G}
    (hu : u ∈ Submission.Blueprint.involutions (H : Set G))
    (huP : u ∈ Subgroup.normalizer (P : Set G))
    (hnc : ∃ x ∈ P, u * x ≠ x * u) :
    ∃ s : G, orderOf s = 2 ∧ s ∉ H ∧
      ∀ ω : G ⧸ H, s • ω = ω →
        Work.ThreePoints.ThmC.pPrimeCoreSub p (H ⊓ Submission.Blueprint.conj s H) ≤
          Work.ThreePoints.ThmC.pPrimeCoreSub p
            (MulAction.stabilizer G ω ⊓ H ⊓ Submission.Blueprint.conj s H) := by
  classical
  have hu2 : orderOf u = 2 := hu.2
  have huH : u ∈ H := hu.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hPp : IsPGroup p P := hP.1
  have huu : u * u = 1 := Work.ThreePoints.mul_self_eq_one_of_orderOf_eq_two hu2
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hstab : MulAction.stabilizer G (((1 : G)) : G ⧸ H) = H := by
    rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.conj_one]
  -- the auxiliary `p`-subgroup `K = ⟨J(P,u)⟩`
  let K : Subgroup G := Subgroup.closure (Submission.Blueprint.invertedBy P u)
  have hKP : K ≤ P := (Subgroup.closure_le P).mpr (fun x hx => hx.1)
  have hKH : K ≤ H := le_trans hKP hPH
  have hKp : IsPGroup p K := hPp.to_le hKP
  have hKmem : ∀ x ∈ Submission.Blueprint.invertedBy P u, x ∈ K :=
    fun x hx => Subgroup.subset_closure hx
  -- `u` normalises `K`
  have hJinv : ∀ x ∈ Submission.Blueprint.invertedBy P u,
      u * x * u⁻¹ ∈ Submission.Blueprint.invertedBy P u := by
    rintro x ⟨hxP, hxu⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp huP x).mp hxP, ?_⟩
    rw [hxu]
    calc u * x⁻¹ * u⁻¹ = (u * x * u⁻¹)⁻¹ := by group
      _ = (x⁻¹)⁻¹ := by rw [hxu]
  have hKu : Submission.Blueprint.conj u K = K := by
    have himg : (MulAut.conj u).toMonoidHom '' (Submission.Blueprint.invertedBy P u : Set G)
        ⊆ (Submission.Blueprint.invertedBy P u : Set G) := by
      rintro y ⟨x, hx, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hJinv x hx
    have himg' : (MulAut.conj u).toMonoidHom '' (Submission.Blueprint.invertedBy P u : Set G)
        = (Submission.Blueprint.invertedBy P u : Set G) := by
      refine Set.Subset.antisymm himg ?_
      intro x hx
      refine ⟨(MulAut.conj u).toMonoidHom x, ?_, ?_⟩
      · simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hJinv x hx
      · calc (MulAut.conj u).toMonoidHom ((MulAut.conj u).toMonoidHom x)
            = (u * u) * x * (u⁻¹ * u⁻¹) := by
              simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
          _ = x := by rw [huu, huinv, one_mul, huu, mul_one]
    rw [Submission.Blueprint.conj]
    change Subgroup.map (MulAut.conj u).toMonoidHom (Subgroup.closure _) = _
    rw [MonoidHom.map_closure, himg']
  by_cases hC : Subgroup.centralizer (K : Set G) ≤ H
  · -- ## Case 3: `C_G(K) ≤ H`
    haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
    have h2t : MulAction.IsMultiplyPretransitive G (G ⧸ H) 2 := hA G hfour H hH
    have haP : (((1 : G)) : G ⧸ H) ∈ Work.DoubleTransitivity.fixedBySub P := by
      rw [Work.DoubleTransitivity.mem_fixedBySub]
      intro q hq
      exact MulAction.mem_stabilizer_iff.mp (by rw [hstab]; exact hPH hq)
    have hbigP : 3 ≤ (Work.DoubleTransitivity.fixedBySub P : Set (G ⧸ H)).ncard := hP.2.1
    have hmaxP : ∀ Q : Subgroup G, IsPGroup p Q →
        Q ≤ MulAction.stabilizer G (((1 : G)) : G ⧸ H) →
        3 ≤ (Work.DoubleTransitivity.fixedBySub Q : Set (G ⧸ H)).ncard → P ≤ Q → Q ≤ P := by
      intro Q hQp hQa hQ3 hPQ
      exact le_of_eq (hP.2.2 Q hPQ hQp hQ3)
    obtain ⟨-, htrans⟩ := Work.ThreePoints.app2_6_general (X := G) (E := G ⧸ H) hp h2t hPp
      (by rw [hstab]; exact hPH) hbigP hmaxP
    have hNnotle : ¬ (Subgroup.normalizer (P : Set G) ≤ H) := by
      intro hle
      have h1 : 1 < (Work.DoubleTransitivity.fixedBySub P : Set (G ⧸ H)).ncard := by
        have := hP.2.1; omega
      obtain ⟨d, hdP, hda⟩ := Set.exists_ne_of_one_lt_ncard h1 (((1 : G)) : G ⧸ H)
      obtain ⟨y, hyN, hya⟩ := htrans _ haP _ hdP
      have : y • (((1 : G)) : G ⧸ H) = (((1 : G)) : G ⧸ H) :=
        MulAction.mem_stabilizer_iff.mp (by rw [hstab]; exact hle hyN)
      exact hda (by rw [← hya, this])
    have hproperN : (Subgroup.normalizer (P : Set G) ⊓ H).subgroupOf (Subgroup.normalizer (P : Set G)) ≠ ⊤ := by
      intro htop
      apply hNnotle
      intro n hn
      have : (⟨n, hn⟩ : ↥(Subgroup.normalizer (P : Set G))) ∈
          (Subgroup.normalizer (P : Set G) ⊓ H).subgroupOf (Subgroup.normalizer (P : Set G)) := by
        rw [htop]; trivial
      exact (Subgroup.mem_subgroupOf.mp this).2
    have hevN : Even (Nat.card (Subgroup.normalizer (P : Set G) ⊓ H : Subgroup G)) := by
      have hle : Subgroup.zpowers u ≤ Subgroup.normalizer (P : Set G) ⊓ H :=
        le_inf (Subgroup.zpowers_le.mpr huP) (Subgroup.zpowers_le.mpr huH)
      have hdvd := Subgroup.card_dvd_of_le hle
      rw [Nat.card_zpowers, hu2] at hdvd
      exact even_iff_two_dvd.mpr hdvd
    haveI hstrongN : IsStronglyEmbedded
        ((Subgroup.normalizer (P : Set G) ⊓ H).subgroupOf (Subgroup.normalizer (P : Set G))) :=
      Work.ThreePoints.IsStronglyEmbedded.subgroupOf_inf hH hproperN hevN
    obtain ⟨sN, hsN2, hsNM⟩ := exists_involution_notMem_of_stronglyEmbedded hstrongN
    set s : G := (sN : G) with hsdef
    have hs2 : orderOf s = 2 := by rw [hsdef]; exact (Subgroup.orderOf_coe sN).trans hsN2
    have hss : s * s = 1 := Work.ThreePoints.mul_self_eq_one_of_orderOf_eq_two hs2
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have hsN : s ∈ Subgroup.normalizer (P : Set G) := sN.2
    have hsH : s ∉ H := fun hh => hsNM (Subgroup.mem_subgroupOf.mpr ⟨sN.2, hh⟩)
    -- `u` and `s` both act on `Ω_P = fixedPts H P`
    have hu_inv : Function.Involutive (fun ω : G ⧸ H => u • ω) := by
      intro x; show u • (u • x) = x; rw [← mul_smul, huu, one_smul]
    have hu_pres : ∀ x ∈ (Work.DoubleTransitivity.fixedBySub P : Set (G ⧸ H)),
        u • x ∈ (Work.DoubleTransitivity.fixedBySub P : Set (G ⧸ H)) := by
      intro x hx
      rw [Work.DoubleTransitivity.mem_fixedBySub] at hx ⊢
      intro q hq
      have hq' : u⁻¹ * q * u ∈ P := by
        simpa only [inv_inv] using
          (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (P : Set G)).inv_mem huP) q).mp hq
      calc q • (u • x) = (q * u) • x := (mul_smul q u x).symm
        _ = (u * (u⁻¹ * q * u)) • x := by
            rw [show u * (u⁻¹ * q * u) = q * u from by
              calc u * (u⁻¹ * q * u) = (u * u⁻¹) * (q * u) := by group
                _ = q * u := by rw [huinv, huu, one_mul]]
        _ = u • ((u⁻¹ * q * u) • x) := mul_smul u _ x
        _ = u • x := by rw [hx _ hq']
    have hΩodd : Odd (Work.DoubleTransitivity.fixedBySub P : Set (G ⧸ H)).ncard := by
      refine odd_ncard_of_unique_fixed (σ := fun ω => u • ω)
        (S := (Work.DoubleTransitivity.fixedBySub P : Set (G ⧸ H))) hu_inv hu_pres ?_ ?_
      · intro x y hx hxf hy hyf
        obtain ⟨w, hw, hwuniq⟩ := Work.ThreePoints.existsUnique_fixedPts_of_orderOf_eq_two hH hu2
        exact (hwuniq x hxf).trans (hwuniq y hyf).symm
      · exact ⟨(((1 : G)) : G ⧸ H), haP,
          MulAction.mem_stabilizer_iff.mp (by rw [hstab]; exact huH)⟩
    have hs_inv : Function.Involutive (fun ω : G ⧸ H => s • ω) := by
      intro x; show s • (s • x) = x; rw [← mul_smul, hss, one_smul]
    have hs_pres : ∀ x ∈ (Work.DoubleTransitivity.fixedBySub P : Set (G ⧸ H)),
        s • x ∈ (Work.DoubleTransitivity.fixedBySub P : Set (G ⧸ H)) := by
      intro x hx
      rw [Work.DoubleTransitivity.mem_fixedBySub] at hx ⊢
      intro q hq
      have hq' : s⁻¹ * q * s ∈ P := by
        simpa only [hsinv] using
          (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (P : Set G)).inv_mem hsN) q).mp hq
      calc q • (s • x) = (q * s) • x := (mul_smul q s x).symm
        _ = (s * (s⁻¹ * q * s)) • x := by
            rw [show s * (s⁻¹ * q * s) = q * s from by
              calc s * (s⁻¹ * q * s) = (s * s⁻¹) * (q * s) := by group
                _ = q * s := by rw [hsinv, hss, one_mul]]
        _ = s • ((s⁻¹ * q * s) • x) := mul_smul s _ x
        _ = s • x := by rw [hx _ hq']
    -- `s` fixes a point of `Ω_P`, hence `P ≤ Stab ω`
    obtain ⟨ω, hωP, hωs⟩ := exists_fixed_of_odd_ncard (σ := fun ω => s • ω)
      (S := (Work.DoubleTransitivity.fixedBySub P : Set (G ⧸ H))) hs_inv hs_pres hΩodd
    have hωstab : P ≤ MulAction.stabilizer G ω :=
      Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mp hωP
    have hωuniq : ∀ c : G ⧸ H, s • c = c → c = ω := by
      intro c hc
      obtain ⟨w, hw, hwuniq⟩ := Work.ThreePoints.existsUnique_fixedPts_of_orderOf_eq_two hH hs2
      exact (hwuniq c hc).trans (hwuniq ω hωs).symm
    obtain ⟨g₀, hg₀⟩ : ∃ g : G, MulAction.stabilizer G ω = Submission.Blueprint.conj g H := by
      obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective ω
      exact ⟨g, by rw [← hg, Work.ThreePoints.stabilizer_mk]⟩
    have hnorm : Subgroup.normalizer (MulAction.stabilizer G ω : Set G) = MulAction.stabilizer G ω := by
      rw [hg₀]
      exact Work.ThreePoints.IsStronglyEmbedded.normalizer_eq
        (Work.ThreePoints.conj_stronglyEmbedded hH g₀)
    have hu_notstab : u ∉ MulAction.stabilizer G ω := by
      intro hu_stab
      have hωeq : ω = (((1 : G)) : G ⧸ H) := by
        obtain ⟨w, hw, hwuniq⟩ := Work.ThreePoints.existsUnique_fixedPts_of_orderOf_eq_two hH hu2
        exact (hwuniq ω hu_stab).trans
          (hwuniq _ (MulAction.mem_stabilizer_iff.mp (by rw [hstab]; exact huH))).symm
      have hsH' : s ∈ H := by
        rw [← hstab]
        exact MulAction.mem_stabilizer_iff.mpr (by rw [← hωeq]; exact hωs)
      exact hsH hsH'
    have hne3 : MulAction.stabilizer G ω ≠ Submission.Blueprint.conj u (MulAction.stabilizer G ω) := by
      intro heq
      have huN : u ∈ Subgroup.normalizer (MulAction.stabilizer G ω : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm
      rw [hnorm] at huN
      exact hu_notstab huN
    have hcentK : Subgroup.centralizer (Subgroup.closure (Submission.Blueprint.invertedBy K u) : Set G)
        = Subgroup.centralizer (K : Set G) := by
      have hJeq : Subgroup.closure (Submission.Blueprint.invertedBy K u) = K := by
        refine le_antisymm ((Subgroup.closure_le K).mpr fun x hx => hx.1) ?_
        exact Subgroup.closure_mono (fun x hx => ⟨Subgroup.subset_closure hx, hx.2⟩)
      rw [hJeq]
    have hodd3 : Odd (Nat.card (MulAction.stabilizer G ω ⊓
        Submission.Blueprint.conj u (MulAction.stabilizer G ω) : Subgroup G)) := by
      have hne' : Submission.Blueprint.conj g₀ H ≠ Submission.Blueprint.conj (u * g₀) H := by
        intro heq
        apply hne3
        rw [hg₀, ← Work.ThreePoints.conj_mul]
        exact heq
      have hres := Work.ThreePoints.card_inf_conj_odd hH hne'
      rw [← hg₀, Work.ThreePoints.conj_mul, ← hg₀] at hres
      exact hres
    have hC3 : Subgroup.centralizer (Subgroup.closure (Submission.Blueprint.invertedBy K u) : Set G)
        ⊓ MulAction.stabilizer G ω ⊓ Submission.Blueprint.conj u (MulAction.stabilizer G ω) ≤ H :=
      fun x hx => hC (hcentK ▸ hx.1.1)
    have hstep3 := step1_pPrimeCore (H := H) (H₁ := H) (H₂ := MulAction.stabilizer G ω)
      (K := K) (s := u) (hH := hH) (hp := hp) (hH₁ := ⟨1, (Work.ThreePoints.conj_one H).symm⟩)
      (hs := hu2) (hsH₁ := huH) (hKH₁ := hKH) (hKH₂ := le_trans hKP hωstab) (hKs := hKu)
      (hH₂ := ⟨g₀, hg₀⟩) (hKp := hKp) (hodd := hodd3) (hC := hC3)
    -- an involution `v` conjugating `u` to `s`
    have hsep : ∀ ω' : G ⧸ H, u • ω' = ω' → s • ω' ≠ ω' := by
      intro ω' hω' hω's
      have h1 : ω' = ω := hωuniq ω' hω's
      have h2 : ω' = (((1 : G)) : G ⧸ H) := by
        obtain ⟨w, hw, hwuniq⟩ := Work.ThreePoints.existsUnique_fixedPts_of_orderOf_eq_two hH hu2
        exact (hwuniq ω' hω').trans
          (hwuniq _ (MulAction.mem_stabilizer_iff.mp (by rw [hstab]; exact huH))).symm
      have hsa : s • (((1 : G)) : G ⧸ H) = (((1 : G)) : G ⧸ H) := by
        rw [← h2, h1]
        exact hωs
      exact hsH (by rw [← hstab]; exact MulAction.mem_stabilizer_iff.mpr hsa)
    have hoddus : Odd (orderOf (u * s)) := Work.ThreePoints.odd_orderOf_mul hH hu2 hs2 hsep
    obtain ⟨v, hv2, hvu, -⟩ :=
      Work.ThreePoints.exists_involution_conj_of_odd_orderOf_mul hu2 hs2 hoddus
    have hvv : v * v = 1 := Work.ThreePoints.mul_self_eq_one_of_orderOf_eq_two hv2
    -- conjugation by `v` exchanges the two point stabilisers
    have hvs : Submission.Blueprint.conj v (MulAction.stabilizer G ω) = H := by
      have hmem1 : u ∈ Submission.Blueprint.conj (v * g₀) H := by
        rw [Work.ThreePoints.conj_mul, Work.ThreePoints.mem_conj_iff, ← hg₀,
          show v⁻¹ * u * v = s from by
            simpa only [inv_eq_of_mul_eq_one_right hvv] using hvu]
        exact MulAction.mem_stabilizer_iff.mpr hωs
      have hmem2 : u ∈ Submission.Blueprint.conj 1 H := by
        rw [Work.ThreePoints.conj_one]; exact huH
      have hres : Submission.Blueprint.conj (v * g₀) H = Submission.Blueprint.conj 1 H :=
        eq_conj_of_mem_of_orderOf_eq_two hH hu2 hmem1 hmem2
      calc Submission.Blueprint.conj v (MulAction.stabilizer G ω)
          = Submission.Blueprint.conj v (Submission.Blueprint.conj g₀ H) := by rw [hg₀]
        _ = Submission.Blueprint.conj (v * g₀) H := (Work.ThreePoints.conj_mul v g₀ H).symm
        _ = Submission.Blueprint.conj 1 H := hres
        _ = H := Work.ThreePoints.conj_one H
    have hvH : Submission.Blueprint.conj v H = MulAction.stabilizer G ω := by
      have hmem1 : s ∈ Submission.Blueprint.conj v H := by
        rw [Work.ThreePoints.mem_conj_iff]
        rw [show v⁻¹ * s * v = u from by rw [← hvu]; group]
        exact huH
      have hmem2 : s ∈ Submission.Blueprint.conj g₀ H := by
        rw [← hg₀]; exact MulAction.mem_stabilizer_iff.mpr hωs
      have hres : Submission.Blueprint.conj v H = Submission.Blueprint.conj g₀ H :=
        eq_conj_of_mem_of_orderOf_eq_two hH hs2 hmem1 hmem2
      rw [hg₀]; exact hres
    have hvs2 : Submission.Blueprint.conj v (Submission.Blueprint.conj u (MulAction.stabilizer G ω))
        = Submission.Blueprint.conj s H := by
      rw [← Work.ThreePoints.conj_mul]
      have hvu'' : v * u = s * v := by
        calc v * u = (v * u * v⁻¹) * v := by group
          _ = s * v := by rw [hvu]
      rw [hvu'', Work.ThreePoints.conj_mul, hvs]
    have hconjLHS : Submission.Blueprint.conj v
        (MulAction.stabilizer G ω ⊓ Submission.Blueprint.conj u (MulAction.stabilizer G ω))
        = H ⊓ Submission.Blueprint.conj s H := by
      rw [Work.ThreePoints.conj_inf, hvs, hvs2]
    have hconjRHS : Submission.Blueprint.conj v
        (H ⊓ MulAction.stabilizer G ω ⊓ Submission.Blueprint.conj u (MulAction.stabilizer G ω))
        = MulAction.stabilizer G ω ⊓ H ⊓ Submission.Blueprint.conj s H := by
      rw [Work.ThreePoints.conj_inf, Work.ThreePoints.conj_inf, hvH, hvs, hvs2]
    refine ⟨s, hs2, hsH, ?_⟩
    intro ω' hω'
    rw [hωuniq ω' hω']
    have h1 : Submission.Blueprint.conj v
        (Work.ThreePoints.ThmC.pPrimeCoreSub p
          (MulAction.stabilizer G ω ⊓ Submission.Blueprint.conj u (MulAction.stabilizer G ω)))
        ≤ Submission.Blueprint.conj v
          (Work.ThreePoints.ThmC.pPrimeCoreSub p
            (H ⊓ MulAction.stabilizer G ω ⊓ Submission.Blueprint.conj u (MulAction.stabilizer G ω))) :=
      Subgroup.map_mono hstep3
    rw [← pPrimeCoreSub_conj p hp, ← pPrimeCoreSub_conj p hp, hconjLHS, hconjRHS] at h1
    exact h1
  · -- ## Case 2: `C_G(K) ≰ H`
    have hPc : Odd (Nat.card ↥P) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPp
      rw [hn, ← Nat.not_even_iff_odd, even_iff_two_dvd]
      intro h2
      have hp2 : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
      exact hpodd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hp2).symm
    have hu_notC : u ∉ Subgroup.centralizer (K : Set G) := by
      intro huC
      have hone : ∀ x ∈ Submission.Blueprint.invertedBy P u, x = 1 := by
        rintro x ⟨hxP, hxu⟩
        have hcomm : x * u = u * x :=
          Subgroup.mem_centralizer_iff.mp huC x (hKmem x ⟨hxP, hxu⟩)
        have hx1 : x * x = 1 := by
          have h1 : x = x⁻¹ := by
            have h0 : u * x * u⁻¹ = x := by rw [← hcomm]; group
            rw [hxu] at h0
            exact h0.symm
          calc x * x = x⁻¹ * x := by rw [← h1]
            _ = 1 := inv_mul_cancel x
        have hdvd : orderOf x ∣ 2 :=
          orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hx1)
        have hdvdP : orderOf x ∣ Nat.card ↥P := by
          rw [Subgroup.orderOf_coe (⟨x, hxP⟩ : ↥P)]
          exact orderOf_dvd_natCard (⟨x, hxP⟩ : ↥P)
        rcases Nat.prime_two.eq_one_or_self_of_dvd (orderOf x) hdvd with h | h
        · exact orderOf_eq_one_iff.mp h
        · exfalso
          have h2 : 2 ∣ Nat.card ↥P := by rw [← h]; exact hdvdP
          exact (Nat.not_even_iff_odd.mpr hPc) (even_iff_two_dvd.mpr h2)
      have hcard_inv : (Submission.Blueprint.invertedBy P u).ncard = 1 := by
        rw [Set.ncard_eq_one]
        refine ⟨1, ?_⟩
        ext x
        constructor
        · intro hx; exact hone x hx
        · intro hx
          rw [Set.mem_singleton_iff] at hx
          subst hx
          exact ⟨P.one_mem, by group⟩
      obtain ⟨-, hcard⟩ := Work.DoubleTransitivity.App1.app1_1b hu2 hPc huP
      have hCP : Work.DoubleTransitivity.centralizerIn P u = P := by
        refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
        rw [hcard, hcard_inv, mul_one]
      obtain ⟨x₀, hx₀P, hx₀nc⟩ := hnc
      refine hx₀nc ?_
      have hx' : x₀ ∈ Work.DoubleTransitivity.centralizerIn P u := by rw [hCP]; exact hx₀P
      exact (Subgroup.mem_centralizer_singleton_iff.mp hx'.2).symm
    let C : Subgroup G := Subgroup.centralizer (K : Set G)
    let F₁ : Subgroup G := Subgroup.closure ((C : Set G) ∪ {u})
    have hCne : ∃ c : G, c ∈ C ∧ c ∉ H := by
      by_contra h
      apply hC
      intro x hx
      by_contra hxH
      exact h ⟨x, hx, hxH⟩
    have huF₁ : u ∈ F₁ := Subgroup.subset_closure (Or.inr rfl)
    have hCleF₁ : C ≤ F₁ := fun c hc => Subgroup.subset_closure (Or.inl hc)
    -- `u` normalises `C` and `C ⊴ F₁`
    have hCu : ∀ c ∈ C, u * c * u⁻¹ ∈ C := by
      intro c hc
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro x hx
      have hx' : u⁻¹ * x * u ∈ K :=
        Work.ThreePoints.mem_conj_iff.mp (by rw [hKu]; exact hx)
      calc x * (u * c * u⁻¹) = u * ((u⁻¹ * x * u) * c) * u⁻¹ := by group
        _ = u * (c * (u⁻¹ * x * u)) * u⁻¹ := by rw [hc _ hx']
        _ = (u * c * u⁻¹) * x := by group
    have hF₁mem : ∀ x ∈ F₁, x ∈ C ∨ ∃ c ∈ C, x = u * c :=
      fun x hx => mem_or_exists_mul_of_mem_closure (C := C) (u := u) hCu huu hx
    have hF₁normC : ∀ y ∈ F₁, ∀ c ∈ C, y * c * y⁻¹ ∈ C := by
      intro y hy c hc
      rcases hF₁mem y hy with hyC | ⟨c', hc', rfl⟩
      · exact C.mul_mem (C.mul_mem hyC hc) (C.inv_mem hyC)
      · have hmem : c' * c * c'⁻¹ ∈ C := C.mul_mem (C.mul_mem hc' hc) (C.inv_mem hc')
        have h2 : u * (c' * c * c'⁻¹) * u⁻¹ ∈ C := hCu _ hmem
        simpa only [show u * c' * c * (u * c')⁻¹ = u * (c' * c * c'⁻¹) * u⁻¹ from by group]
          using h2
    -- `K` is normalised by all of `F₁`
    have huK : ∀ z ∈ K, u * z * u⁻¹ ∈ K := by
      intro z hz
      have h1 : (MulAut.conj u) z ∈ Submission.Blueprint.conj u K :=
        Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom hz
      rw [hKu] at h1
      simpa only [MulAut.conj_apply] using h1
    have hF₁normK : ∀ y ∈ F₁, ∀ z ∈ K, y * z * y⁻¹ ∈ K := by
      intro y hy z hz
      rcases hF₁mem y hy with hyC | ⟨c', hc', rfl⟩
      · have h := Subgroup.mem_centralizer_iff.mp hyC z hz
        rw [← h]
        simpa using hz
      · have hmem : c' * z * c'⁻¹ ∈ K := by
          have h := Subgroup.mem_centralizer_iff.mp hc' z hz
          rw [← h]
          simpa using hz
        have h2 : u * (c' * z * c'⁻¹) * u⁻¹ ∈ K := huK _ hmem
        simpa only [show u * c' * z * (u * c')⁻¹ = u * (c' * z * c'⁻¹) * u⁻¹ from by group]
          using h2
    have hF₁notleH : ¬ (F₁ ≤ H) := by
      obtain ⟨c, hcC, hcH⟩ := hCne
      exact fun hle => hcH (hle (hCleF₁ hcC))
    have hproperF₁ : (F₁ ⊓ H).subgroupOf F₁ ≠ ⊤ := fun htop => hF₁notleH (fun x hx => by
      have : (⟨x, hx⟩ : ↥F₁) ∈ (F₁ ⊓ H).subgroupOf F₁ := by rw [htop]; trivial
      exact (Subgroup.mem_subgroupOf.mp this).2)
    have hevF₁ : Even (Nat.card (F₁ ⊓ H : Subgroup G)) := by
      have hle : Subgroup.zpowers u ≤ F₁ ⊓ H :=
        le_inf (Subgroup.zpowers_le.mpr huF₁) (Subgroup.zpowers_le.mpr huH)
      have hdvd := Subgroup.card_dvd_of_le hle
      rw [Nat.card_zpowers, hu2] at hdvd
      exact even_iff_two_dvd.mpr hdvd
    haveI hstrongF₁ : IsStronglyEmbedded ((F₁ ⊓ H).subgroupOf F₁) :=
      Work.ThreePoints.IsStronglyEmbedded.subgroupOf_inf hH hproperF₁ hevF₁
    -- all involutions of `F₁` are `F₁`-conjugate to `u`
    have hconjF₁ : ∀ w : G, orderOf w = 2 → w ∈ F₁ → ∃ y ∈ F₁, y⁻¹ * w * y = u := by
      intro w hw hwF₁
      have hw' : orderOf (⟨w, hwF₁⟩ : ↥F₁) = 2 := by
        rw [← Subgroup.orderOf_coe (⟨w, hwF₁⟩ : ↥F₁)]
        exact hw
      have hu' : orderOf (⟨u, huF₁⟩ : ↥F₁) = 2 := by
        rw [← Subgroup.orderOf_coe (⟨u, huF₁⟩ : ↥F₁)]
        exact hu2
      have hb : Work.DoubleTransitivity.IsBender ((F₁ ⊓ H).subgroupOf F₁) :=
        ((Work.DoubleTransitivity.isStronglyEmbedded_iff _).mp hstrongF₁).2
      have hnt : ((F₁ ⊓ H).subgroupOf F₁) ≠ ⊤ :=
        ((Work.DoubleTransitivity.isStronglyEmbedded_iff _).mp hstrongF₁).1
      obtain ⟨c, hc⟩ := Work.DoubleTransitivity.Sec2.inv_class hb hnt hw' hu'
      refine ⟨(c : G), c.2, ?_⟩
      have hco := congrArg (Subtype.val) hc
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk] using hco
    have hltF₁ : F₁ ⊓ H < F₁ :=
      lt_of_le_of_ne inf_le_left (fun h => hF₁notleH (by rw [← h]; exact inf_le_right))
    have hFexists : ∃ n, ∃ F : Subgroup G, F₁ ⊓ H < F ∧ F ≤ F₁ ∧ Nat.card F = n :=
      ⟨Nat.card F₁, F₁, hltF₁, le_rfl, rfl⟩
    obtain ⟨F, hM₁F, hFF₁, hFcard⟩ := Nat.find_spec hFexists
    have hFmin : ∀ B : Subgroup G, F₁ ⊓ H < B → B ≤ F₁ → Nat.card F ≤ Nat.card B := by
      intro B hB hBF
      rw [hFcard]
      exact Nat.find_min' hFexists ⟨B, hB, hBF, rfl⟩
    have hFH : F ⊓ H = F₁ ⊓ H := by
      refine le_antisymm ?_ ?_
      · intro x hx; exact ⟨hFF₁ hx.1, hx.2⟩
      · intro x hx; exact ⟨le_of_lt hM₁F hx, hx.2⟩
    have hMmaxI : ∀ B : Subgroup G, F ⊓ H ≤ B → B ≤ F → B = F ⊓ H ∨ B = F := by
      intro B hMB hBF
      by_cases hBeq : B = F ⊓ H
      · exact Or.inl hBeq
      · refine Or.inr ?_
        have hlt : F₁ ⊓ H < B := by
          rw [← hFH]
          exact lt_of_le_of_ne hMB (Ne.symm hBeq)
        have h1 : Nat.card F ≤ Nat.card B := hFmin B hlt (le_trans hBF hFF₁)
        have h2 : Nat.card B ≤ Nat.card F := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hBF)
        exact Subgroup.eq_of_le_of_card_ge hBF h1
    have hFnotleH : ¬ (F ≤ H) := by
      intro hle
      have h1 : F ⊓ H = F := inf_eq_left.mpr hle
      rw [hFH] at h1
      exact (lt_irrefl (F₁ ⊓ H)) (h1 ▸ hM₁F)
    have hproperF : (F ⊓ H).subgroupOf F ≠ ⊤ := fun htop => hFnotleH (fun x hx => by
      have : (⟨x, hx⟩ : ↥F) ∈ (F ⊓ H).subgroupOf F := by rw [htop]; trivial
      exact (Subgroup.mem_subgroupOf.mp this).2)
    have hevF : Even (Nat.card (F ⊓ H : Subgroup G)) := by rw [hFH]; exact hevF₁
    haveI hstrongF : IsStronglyEmbedded ((F ⊓ H).subgroupOf F) :=
      Work.ThreePoints.IsStronglyEmbedded.subgroupOf_inf hH hproperF hevF
    -- `F₁` (and hence `F`) has 2-rank 1
    have hCnoinv : ∀ w ∈ C, orderOf w ≠ 2 := by
      intro w hwC hw2
      obtain ⟨y, hyF₁, hy⟩ := hconjF₁ w hw2 (hCleF₁ hwC)
      have hmem : y⁻¹ * w * (y⁻¹)⁻¹ ∈ C := hF₁normC y⁻¹ (F₁.inv_mem hyF₁) w hwC
      rw [inv_inv, hy] at hmem
      exact hu_notC hmem
    have hrankF₁ : ¬ Submission.Blueprint.HasFourGroup ↥F₁ := by
      rintro ⟨a, b, ha, hb, hne, hcomm⟩
      have haF₁ : (a : G) ∈ F₁ := a.2
      have hbF₁ : (b : G) ∈ F₁ := b.2
      have haG : orderOf ((a : G)) = 2 := by rw [Subgroup.orderOf_coe]; exact ha
      have hbG : orderOf ((b : G)) = 2 := by rw [Subgroup.orderOf_coe]; exact hb
      have haC : (a : G) ∉ C := fun h => hCnoinv _ h haG
      have hbC : (b : G) ∉ C := fun h => hCnoinv _ h hbG
      obtain ⟨ca, hca, haeq⟩ : ∃ c ∈ C, (a : G) = u * c := by
        rcases hF₁mem (a : G) haF₁ with h | h
        · exact absurd h haC
        · exact h
      obtain ⟨cb, hcb, hbeq⟩ : ∃ c ∈ C, (b : G) = u * c := by
        rcases hF₁mem (b : G) hbF₁ with h | h
        · exact absurd h hbC
        · exact h
      have habC : (a : G) * (b : G) ∈ C := by
        rw [haeq, hbeq]
        have h1 : u * ca * u⁻¹ ∈ C := hCu ca hca
        have h2 : u * ca * (u * cb) = (u * ca * u⁻¹) * cb := by rw [huinv]; group
        rw [h2]
        exact C.mul_mem h1 hcb
      have hab2 : orderOf ((a : G) * (b : G)) = 2 := by
        have hcc : (a : G) * (b : G) = (b : G) * (a : G) := by
          simpa only [Subgroup.coe_mul, Subtype.coe_mk] using congrArg (Subtype.val) hcomm
        have hsq : (a : G) * (b : G) * ((a : G) * (b : G)) = 1 := by
          calc (a : G) * (b : G) * ((a : G) * (b : G))
              = (a : G) * ((b : G) * (a : G)) * (b : G) := by group
            _ = (a : G) * ((a : G) * (b : G)) * (b : G) := by rw [← hcc]
            _ = ((a : G) * (a : G)) * ((b : G) * (b : G)) := by group
            _ = 1 := by
                rw [Work.ThreePoints.mul_self_eq_one_of_orderOf_eq_two haG,
                  Work.ThreePoints.mul_self_eq_one_of_orderOf_eq_two hbG, mul_one]
        refine Work.ThreePoints.orderOf_eq_two_of ?_ hsq
        intro h1'
        have hbb : (b : G) * (b : G) = 1 :=
          Work.ThreePoints.mul_self_eq_one_of_orderOf_eq_two hbG
        have : (a : G) = (b : G) := by
          calc (a : G) = (a : G) * ((b : G) * (b : G)) := by rw [hbb, mul_one]
            _ = ((a : G) * (b : G)) * (b : G) := by rw [mul_assoc]
            _ = (b : G) := by rw [h1', one_mul]
        exact hne (Subtype.ext this)
      exact hCnoinv _ habC hab2
    have hrankF : ¬ Submission.Blueprint.HasFourGroup ↥F := by
      rintro ⟨a, b, ha, hb, hne, hcomm⟩
      refine hrankF₁ ⟨⟨(a : G), hFF₁ a.2⟩, ⟨(b : G), hFF₁ b.2⟩, ?_, ?_, ?_, ?_⟩
      · rw [← Subgroup.orderOf_coe (⟨(a : G), hFF₁ a.2⟩ : ↥F₁)]
        exact (Subgroup.orderOf_coe a).trans ha
      · rw [← Subgroup.orderOf_coe (⟨(b : G), hFF₁ b.2⟩ : ↥F₁)]
        exact (Subgroup.orderOf_coe b).trans hb
      · intro h
        apply hne
        apply Subtype.ext
        exact congrArg (fun z : ↥F₁ => (z : G)) h
      · apply Subtype.ext
        simpa only [Subgroup.coe_mul, Subtype.coe_mk] using congrArg (Subtype.val) hcomm
    have hcoatF : IsCoatom ((F ⊓ H).subgroupOf F) := by
      rw [SetLike.isCoatom_iff]
      refine ⟨hproperF, ?_⟩
      intro M g hle hgK hgM
      have hle' : F ⊓ H ≤ M.map (Subgroup.subtype F) := fun x hx =>
        Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩, hle (by rw [Subgroup.mem_subgroupOf]; exact hx), rfl⟩
      rcases hMmaxI (M.map (Subgroup.subtype F)) hle' (Subgroup.map_subtype_le M) with hcase | hcase
      · exfalso
        apply hgK
        rw [Subgroup.mem_subgroupOf]
        have : (g : G) ∈ M.map (Subgroup.subtype F) := Subgroup.mem_map.mpr ⟨g, hgM, rfl⟩
        rwa [hcase] at this
      · refine le_antisymm le_top fun x _ => ?_
        have : (x : G) ∈ M.map (Subgroup.subtype F) := by rw [hcase]; exact x.2
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp this
        rwa [Subtype.ext hyx] at hy
    obtain ⟨sF, hsF2, hsFM⟩ := exists_involution_notMem_of_stronglyEmbedded hstrongF
    set s : G := (sF : G) with hsdef
    have hs2 : orderOf s = 2 := by rw [hsdef]; exact (Subgroup.orderOf_coe sF).trans hsF2
    have hsF : s ∈ F := sF.2
    have hsH : s ∉ H := fun hh => hsFM (Subgroup.mem_subgroupOf.mpr ⟨sF.2, hh⟩)
    have hss : s * s = 1 := Work.ThreePoints.mul_self_eq_one_of_orderOf_eq_two hs2
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    obtain ⟨ω, hωs, hωuniq⟩ : ∃ ω : G ⧸ H, s • ω = ω ∧ ∀ c : G ⧸ H, s • c = c → c = ω := by
      obtain ⟨w, hw, hwu⟩ := Work.ThreePoints.existsUnique_fixedPts_of_orderOf_eq_two hH hs2
      exact ⟨w, hw, hwu⟩
    -- all involutions of `F` are `F`-conjugate to `u`; hence `ω` lies in the `F`-orbit of the base point
    have hconjF : ∃ y ∈ F, y⁻¹ * s * y = u := by
      have hs' : orderOf (⟨s, hsF⟩ : ↥F) = 2 := by
        rw [← Subgroup.orderOf_coe (⟨s, hsF⟩ : ↥F)]; exact hs2
      have huF : u ∈ F := le_of_lt hM₁F ⟨huF₁, huH⟩
      have hu' : orderOf (⟨u, huF⟩ : ↥F) = 2 := by
        rw [← Subgroup.orderOf_coe (⟨u, huF⟩ : ↥F)]; exact hu2
      have hb : Work.DoubleTransitivity.IsBender ((F ⊓ H).subgroupOf F) :=
        ((Work.DoubleTransitivity.isStronglyEmbedded_iff _).mp hstrongF).2
      have hnt : ((F ⊓ H).subgroupOf F) ≠ ⊤ :=
        ((Work.DoubleTransitivity.isStronglyEmbedded_iff _).mp hstrongF).1
      obtain ⟨c, hc⟩ := Work.DoubleTransitivity.Sec2.inv_class hb hnt hs' hu'
      refine ⟨(c : G), c.2, ?_⟩
      have hco := congrArg (Subtype.val) hc
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk] using hco
    have horb : ω ∈ MulAction.orbit F (((1 : G)) : G ⧸ H) := by
      obtain ⟨y, hyF, hy⟩ := hconjF
      refine ⟨⟨y, hyF⟩, ?_⟩
      show y • (((1 : G)) : G ⧸ H) = ω
      have hua : u • (((1 : G)) : G ⧸ H) = (((1 : G)) : G ⧸ H) :=
        MulAction.mem_stabilizer_iff.mp (by rw [hstab]; exact huH)
      have hfix : s • (y • (((1 : G)) : G ⧸ H)) = y • (((1 : G)) : G ⧸ H) := by
        rw [← mul_smul, show s * y = y * (y⁻¹ * s * y) from by group, mul_smul, hy, hua]
      exact hωuniq _ hfix
    -- Appendix III (1): `F ⊓ H ⊓ H^s` fixes `ω`
    have hCGK_le : Subgroup.centralizer (K : Set G) ⊓ H ⊓ Submission.Blueprint.conj s H
        ≤ MulAction.stabilizer G ω := by
      have h1 := app3_consequence (H := H) hH (F := F) hstrongF hcoatF hrankF hBrSz hFT
        hs2 hsF hsH hωs hωuniq horb
      intro x hx
      have hxFH : x ∈ F ⊓ H := by
        rw [hFH]
        exact ⟨hCleF₁ hx.1.1, hx.1.2⟩
      exact h1 ⟨hxFH, hx.2⟩
    -- `s = u * c` with `c ∈ C`, so `s` inverts the generators of `K`
    obtain ⟨k₀, hk₀C, hsk₀⟩ : ∃ c ∈ C, s = u * c := by
      rcases hF₁mem s (hFF₁ hsF) with hsC | h
      · exfalso
        obtain ⟨y, hyF₁, hy⟩ := hconjF₁ s hs2 (hFF₁ hsF)
        have hmem : y⁻¹ * s * (y⁻¹)⁻¹ ∈ C := hF₁normC y⁻¹ (F₁.inv_mem hyF₁) s hsC
        rw [inv_inv, hy] at hmem
        exact hu_notC hmem
      · exact h
    have hK₀sub : Submission.Blueprint.invertedBy P u ⊆ Submission.Blueprint.invertedBy K s := by
      intro x hx
      refine ⟨hKmem x hx, ?_⟩
      have hcx : k₀ * x * k₀⁻¹ = x := by
        rw [Subgroup.mem_centralizer_iff] at hk₀C
        rw [← hk₀C x (hKmem x hx), mul_assoc, mul_inv_cancel, mul_one]
      rw [hsk₀]
      show (MulAut.conj (u * k₀)) x = x⁻¹
      rw [MulAut.conj_apply]
      calc u * k₀ * x * (u * k₀)⁻¹ = u * (k₀ * x * k₀⁻¹) * u⁻¹ := by group
        _ = u * x * u⁻¹ := by rw [hcx]
        _ = x⁻¹ := hx.2
    have hsetS : ∀ x ∈ Submission.Blueprint.invertedBy P u,
        (MulAut.conj s) x ∈ Submission.Blueprint.invertedBy P u := by
      intro x hx
      have hcx : k₀ * x * k₀⁻¹ = x := by
        rw [Subgroup.mem_centralizer_iff] at hk₀C
        rw [← hk₀C x (hKmem x hx), mul_assoc, mul_inv_cancel, mul_one]
      rw [hsk₀]
      show (MulAut.conj (u * k₀)) x ∈ Submission.Blueprint.invertedBy P u
      rw [MulAut.conj_apply]
      have hval : u * k₀ * x * (u * k₀)⁻¹ = x⁻¹ := by
        rw [show u * k₀ * x * (u * k₀)⁻¹ = u * (k₀ * x * k₀⁻¹) * u⁻¹ from by group,
          hcx, hx.2]
      rw [hval]
      refine ⟨P.inv_mem hx.1, ?_⟩
      calc u * x⁻¹ * u⁻¹ = x := by
            rw [← hx.2]
            calc u * (u * x * u⁻¹) * u⁻¹ = (u * u) * x * (u⁻¹ * u⁻¹) := by group
              _ = x := by rw [huu, huinv, one_mul, huu, mul_one]
        _ = (x⁻¹)⁻¹ := (inv_inv x).symm
    have hsK : Submission.Blueprint.conj s K = K := by
      have himg : (MulAut.conj s).toMonoidHom '' (Submission.Blueprint.invertedBy P u : Set G)
          = (Submission.Blueprint.invertedBy P u : Set G) := by
        refine Set.Subset.antisymm ?_ ?_
        · rintro y ⟨x, hx, rfl⟩
          simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hsetS x hx
        · intro x hx
          refine ⟨(MulAut.conj s).toMonoidHom x, ?_, ?_⟩
          · simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hsetS x hx
          · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
            calc s * (s * x * s⁻¹) * s⁻¹ = (s * s) * x * (s⁻¹ * s⁻¹) := by group
              _ = x := by rw [hss, hsinv, one_mul, hss, mul_one]
      rw [Submission.Blueprint.conj]
      change Subgroup.map (MulAut.conj s).toMonoidHom (Subgroup.closure _) = _
      rw [MonoidHom.map_closure, himg]
    have hcentK2 : Subgroup.centralizer (Subgroup.closure (Submission.Blueprint.invertedBy K s) : Set G)
        ≤ Subgroup.centralizer (K : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro z hz
      refine hx z ?_
      refine Subgroup.closure_mono ?_
        (show z ∈ Subgroup.closure (Submission.Blueprint.invertedBy P u) from hz)
      intro w hw
      exact hK₀sub hw
    -- `K ≤ Stab ω` by counting (`Ω_K` has odd cardinality)
    have hu_invK : Function.Involutive (fun ω : G ⧸ H => u • ω) := by
      intro x; show u • (u • x) = x; rw [← mul_smul, huu, one_smul]
    have huKpres : ∀ x ∈ (Work.DoubleTransitivity.fixedBySub K : Set (G ⧸ H)),
        u • x ∈ (Work.DoubleTransitivity.fixedBySub K : Set (G ⧸ H)) := by
      intro x hx
      rw [Work.DoubleTransitivity.mem_fixedBySub] at hx ⊢
      intro q hq
      have hq' : u⁻¹ * q * u ∈ K :=
        Work.ThreePoints.mem_conj_iff.mp (by rw [hKu]; exact hq)
      calc q • (u • x) = (q * u) • x := (mul_smul q u x).symm
        _ = (u * (u⁻¹ * q * u)) • x := by
            rw [show u * (u⁻¹ * q * u) = q * u from by
              calc u * (u⁻¹ * q * u) = (u * u⁻¹) * (q * u) := by group
                _ = q * u := by rw [huinv, huu, one_mul]]
        _ = u • ((u⁻¹ * q * u) • x) := mul_smul u _ x
        _ = u • x := by rw [hx _ hq']
    have hΩKodd : Odd (Work.DoubleTransitivity.fixedBySub K : Set (G ⧸ H)).ncard := by
      refine odd_ncard_of_unique_fixed (σ := fun ω => u • ω)
        (S := (Work.DoubleTransitivity.fixedBySub K : Set (G ⧸ H))) hu_invK huKpres ?_ ?_
      · intro x y hx hxf hy hyf
        obtain ⟨w, hw, hwuniq⟩ := Work.ThreePoints.existsUnique_fixedPts_of_orderOf_eq_two hH hu2
        exact (hwuniq x hxf).trans (hwuniq y hyf).symm
      · refine ⟨(((1 : G)) : G ⧸ H), ?_, MulAction.mem_stabilizer_iff.mp (by rw [hstab]; exact huH)⟩
        rw [Work.DoubleTransitivity.mem_fixedBySub]
        intro q hq
        exact MulAction.mem_stabilizer_iff.mp (by rw [hstab]; exact hKH hq)
    have hs_invK : Function.Involutive (fun ω : G ⧸ H => s • ω) := by
      intro x; show s • (s • x) = x; rw [← mul_smul, hss, one_smul]
    have hsKpres : ∀ x ∈ (Work.DoubleTransitivity.fixedBySub K : Set (G ⧸ H)),
        s • x ∈ (Work.DoubleTransitivity.fixedBySub K : Set (G ⧸ H)) := by
      intro x hx
      rw [Work.DoubleTransitivity.mem_fixedBySub] at hx ⊢
      intro q hq
      have hq' : s⁻¹ * q * s ∈ K :=
        Work.ThreePoints.mem_conj_iff.mp (by rw [hsK]; exact hq)
      calc q • (s • x) = (q * s) • x := (mul_smul q s x).symm
        _ = (s * (s⁻¹ * q * s)) • x := by
            rw [show s * (s⁻¹ * q * s) = q * s from by
              calc s * (s⁻¹ * q * s) = (s * s⁻¹) * (q * s) := by group
                _ = q * s := by rw [hsinv, hss, one_mul]]
        _ = s • ((s⁻¹ * q * s) • x) := mul_smul s _ x
        _ = s • x := by rw [hx _ hq']
    have hKHstab : K ≤ MulAction.stabilizer G ω := by
      obtain ⟨ω₂, hω₂K, hω₂s⟩ := exists_fixed_of_odd_ncard (σ := fun ω => s • ω)
        (S := (Work.DoubleTransitivity.fixedBySub K : Set (G ⧸ H))) hs_invK hsKpres hΩKodd
      rw [← hωuniq ω₂ hω₂s]
      exact Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mp hω₂K
    have hodd2 : Odd (Nat.card (H ⊓ Submission.Blueprint.conj s H : Subgroup G)) := by
      have hne2 : Submission.Blueprint.conj (1 : G) H ≠ Submission.Blueprint.conj s H := by
        intro heq
        rw [Work.ThreePoints.conj_one] at heq
        have hsN : s ∈ Subgroup.normalizer (H : Set G) :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm
        rw [Work.ThreePoints.IsStronglyEmbedded.normalizer_eq hH] at hsN
        exact hsH hsN
      simpa only [Work.ThreePoints.conj_one] using
        Work.ThreePoints.card_inf_conj_odd hH (g := 1) (g' := s) hne2
    obtain ⟨g₀, hg₀⟩ : ∃ g : G, MulAction.stabilizer G ω = Submission.Blueprint.conj g H := by
      obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective ω
      exact ⟨g, by rw [← hg, Work.ThreePoints.stabilizer_mk]⟩
    have hstep2 := step1_pPrimeCore (H := H) (H₁ := MulAction.stabilizer G ω) (H₂ := H)
      (K := K) (s := s) (hH := hH) (hp := hp) (hH₁ := ⟨g₀, hg₀⟩)
      (hH₂ := ⟨1, (Work.ThreePoints.conj_one H).symm⟩) (hs := hs2)
      (hsH₁ := MulAction.mem_stabilizer_iff.mpr hωs) (hKH₁ := hKHstab) (hKH₂ := hKH)
      (hKs := hsK) (hKp := hKp) (hodd := hodd2)
      (hC := fun x hx => hCGK_le ⟨⟨hcentK2 hx.1.1, hx.1.2⟩, hx.2⟩)
    refine ⟨s, hs2, hsH, ?_⟩
    intro ω' hω'
    rw [hωuniq ω' hω']
    exact hstep2


end Work.ThreePoints.ThmC
