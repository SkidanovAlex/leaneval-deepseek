import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.ThreePoints.ThmC.Prop2h2t
import Submission.Work.ThreePoints.ThmC.ch1_sec6_cor1
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup_nofour
import Submission.Work.ThreePoints.involutions_conj_of_stronglyEmbedded

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ThreePoints.ThmC

/-- Conjugation by `x` carries a Sylow-`p` subgroup of `D` to one of `conj x D`. -/
theorem IsSylowOf.map_conj {G : Type} [Group G] {p : ℕ} {P D : Subgroup G}
    (h : IsSylowOf p P D) (x : G) :
    IsSylowOf p (Submission.Blueprint.conj x P) (Submission.Blueprint.conj x D) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map _, ?_⟩
  intro R hR hRD hRp
  have h1 : Submission.Blueprint.conj x⁻¹ R ≤ D := by
    have h2 : Submission.Blueprint.conj x⁻¹ R ≤
        Submission.Blueprint.conj x⁻¹ (Submission.Blueprint.conj x D) := Subgroup.map_mono hRD
    rwa [Work.DoubleTransitivity.conj_inv_conj] at h2
  have h3 : P ≤ Submission.Blueprint.conj x⁻¹ R := by
    have h2 : Submission.Blueprint.conj x⁻¹ (Submission.Blueprint.conj x P) ≤
        Submission.Blueprint.conj x⁻¹ R := Subgroup.map_mono hR
    rwa [Work.DoubleTransitivity.conj_inv_conj] at h2
  have h4 := h.2.2 (Submission.Blueprint.conj x⁻¹ R) h3 h1 (hRp.map _)
  have h5 : Submission.Blueprint.conj x (Submission.Blueprint.conj x⁻¹ R) =
      Submission.Blueprint.conj x P := by rw [h4]
  rwa [Work.DoubleTransitivity.conj_conj_inv] at h5

/-- **Peterfalvi I Ch. II §2 Lemma 1 (a) (p. 164).** -/
theorem maxP3_proof {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    (h2t : Submission.Blueprint.IsTwoTransitiveOn H)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {g : G} (hg : g ∉ H) {u : G} (hu : u ∈ Submission.Blueprint.involutions (H : Set G))
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) {P : Subgroup G}
    (hP : Work.ThreePoints.ThmC.IsSylowOf p P
      (Submission.Blueprint.twoPoint H g ⊓
        Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H g)))
    (huP : u ∈ Subgroup.normalizer (P : Set G)) :
    Work.ThreePoints.ThmC.IsMaxP3 H p P := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype (Subgroup G) := Fintype.ofFinite _
  have hPp : IsPGroup p P := hP.2.1
  have hPH : P ≤ H := (hP.1.trans inf_le_left).trans inf_le_left
  have hPHg : P ≤ Submission.Blueprint.conj g H := (hP.1.trans inf_le_left).trans inf_le_right
  have hPHug : P ≤ Submission.Blueprint.conj (u * g) H := by
    have h1 : P ≤ Submission.Blueprint.conj u (Submission.Blueprint.conj g H) :=
      (hP.1.trans inf_le_right).trans (Subgroup.map_mono inf_le_right)
    rwa [← Work.ThreePoints.conj_mul] at h1
  have huH : u ∈ H := hu.1
  have hu2 : orderOf u = 2 := hu.2
  -- the involution `u` has `1` as its unique fixed point
  have huniq : ∀ ω : G ⧸ H, u • ω = ω → ω = (((1 : G)) : G ⧸ H) := by
    obtain ⟨ω₀, hω₀, huniq'⟩ := Work.ThreePoints.existsUnique_fixedPts_of_orderOf_eq_two hH hu2
    have h1 : u • (((1 : G)) : G ⧸ H) = (((1 : G)) : G ⧸ H) :=
      MulAction.mem_stabilizer_iff.mp (by
        rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.conj_one]; exact huH)
    intro ω hω
    exact (huniq' ω hω).trans (huniq' _ h1).symm
  -- three distinct points fixed by `P`
  have h1g : (((1 : G)) : G ⧸ H) ≠ ((g : G) : G ⧸ H) := by
    intro h
    rw [QuotientGroup.eq] at h
    exact hg (by simpa using h)
  have h1ug : (((1 : G)) : G ⧸ H) ≠ (((u * g : G)) : G ⧸ H) := by
    intro h
    rw [QuotientGroup.eq] at h
    have h2 : u * g ∈ H := by simpa using h
    exact hg (by simpa using H.mul_mem (H.inv_mem huH) h2)
  have hgug : ((g : G) : G ⧸ H) ≠ (((u * g : G)) : G ⧸ H) := by
    intro h
    rw [QuotientGroup.eq] at h
    have h2 : u ∈ Submission.Blueprint.conj g H := by
      rw [Work.ThreePoints.mem_conj_iff]
      simpa [mul_assoc] using h
    have h3 : u • ((g : G) : G ⧸ H) = ((g : G) : G ⧸ H) :=
      MulAction.mem_stabilizer_iff.mp (by
        rw [Work.ThreePoints.stabilizer_mk]; exact h2)
    exact h1g (huniq _ h3).symm
  -- a general "three fixed points" criterion
  have three_le : ∀ (R : Subgroup G) (ω₁ ω₂ ω₃ : G ⧸ H), ω₁ ≠ ω₂ → ω₁ ≠ ω₃ → ω₂ ≠ ω₃ →
      R ≤ MulAction.stabilizer G ω₁ → R ≤ MulAction.stabilizer G ω₂ →
      R ≤ MulAction.stabilizer G ω₃ → 3 ≤ (Submission.Blueprint.fixedPts H R).ncard := by
    intro R ω₁ ω₂ ω₃ h12 h13 h23 hR1 hR2 hR3
    have hsub : ({ω₁, ω₂, ω₃} : Set (G ⧸ H)) ⊆ Submission.Blueprint.fixedPts H R := by
      intro ω hω
      rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer]
      rcases hω with h | h | h
      · rw [h]; exact hR1
      · rw [h]; exact hR2
      · rw [h]; exact hR3
    have hcard : ({ω₁, ω₂, ω₃} : Set (G ⧸ H)).ncard = 3 := by
      rw [Set.ncard_eq_three]
      exact ⟨_, _, _, h12, h13, h23, rfl⟩
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [hcard] at h2
  have h3P : 3 ≤ (Submission.Blueprint.fixedPts H P).ncard := by
    refine three_le P (((1 : G)) : G ⧸ H) ((g : G) : G ⧸ H) (((u * g : G)) : G ⧸ H)
      h1g h1ug hgug ?_ ?_ ?_
    · exact Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mpr (by
        rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.conj_one]; exact hPH)
    · exact Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mpr (by
        rw [Work.ThreePoints.stabilizer_mk]; exact hPHg)
    · exact Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mpr (by
        rw [Work.ThreePoints.stabilizer_mk]; exact hPHug)
  -- ## a maximal `p`-subgroup `Q ≤ H` with `≥ 3` fixed points containing `P`
  let S : Finset (Subgroup G) := Finset.univ.filter (fun R =>
      P ≤ R ∧ R ≤ H ∧ IsPGroup p R ∧ 3 ≤ (Submission.Blueprint.fixedPts H R).ncard)
  have hSne : S.Nonempty := by
    refine ⟨P, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨le_refl P, hPH, hPp, h3P⟩
  obtain ⟨Q, hQmax⟩ := Finset.exists_maximal hSne
  have hQS : Q ∈ S := hQmax.1
  have hQT : P ≤ Q ∧ Q ≤ H ∧ IsPGroup p Q ∧ 3 ≤ (Submission.Blueprint.fixedPts H Q).ncard := by
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hQS
  have hQmaxH : ∀ R : Subgroup G, Q ≤ R → R ≤ H → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts H R).ncard → R = Q := by
    intro R hQR hRH hRp hR3
    have hRS : R ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hQT.1.trans hQR, hRH, hRp, hR3⟩
    exact le_antisymm (hQmax.2 hRS hQR) hQR
  -- ## an involution `v ∈ N_H(Q)`
  have heven : Even (Nat.card ↥(Subgroup.normalizer (Q.subgroupOf H : Set H) : Subgroup H)) :=
    even_card_normalizer_h2t hH h2t hBrSz hp hpodd hQT.2.1 hQT.2.2.1 hQT.2.2.2 hQmaxH
  have heven' : Even (Nat.card ↥(H ⊓ Subgroup.normalizer (Q : Set G))) := by
    rw [← Work.ThreePoints.card_normalizer_subgroupOf_eq_card_inf hQT.2.1]
    exact heven
  obtain ⟨v, hvN, hv2⟩ : ∃ v : G, v ∈ H ⊓ Subgroup.normalizer (Q : Set G) ∧ orderOf v = 2 := by
    haveI : Fintype ↥(H ⊓ Subgroup.normalizer (Q : Set G)) := Fintype.ofFinite _
    have hdvd : 2 ∣ Fintype.card ↥(H ⊓ Subgroup.normalizer (Q : Set G)) := by
      rw [← Nat.card_eq_fintype_card]
      exact even_iff_two_dvd.mp heven'
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card
      (G := ↥(H ⊓ Subgroup.normalizer (Q : Set G))) 2 hdvd
    exact ⟨(w : G), w.2, (Subgroup.orderOf_coe w).trans hw⟩
  have hvH : v ∈ H := hvN.1
  have hvQ : Submission.Blueprint.conj v Q = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hvN.2
  have hvuniq : ∀ ω : G ⧸ H, v • ω = ω → ω = (((1 : G)) : G ⧸ H) := by
    obtain ⟨ω₀, hω₀, hvuniq'⟩ := Work.ThreePoints.existsUnique_fixedPts_of_orderOf_eq_two hH hv2
    have h1 : v • (((1 : G)) : G ⧸ H) = (((1 : G)) : G ⧸ H) :=
      MulAction.mem_stabilizer_iff.mp (by
        rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.conj_one]; exact hvH)
    intro ω hω
    exact (hvuniq' ω hω).trans (hvuniq' _ h1).symm
  -- ## a second fixed point of `Q` and the conjugating element `x`
  have hone : (((1 : G)) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H Q :=
    Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mpr (by
      rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.conj_one]; exact hQT.2.1)
  obtain ⟨ω₂, hω₂, hω₂ne⟩ := Set.exists_ne_of_one_lt_ncard
    (s := Submission.Blueprint.fixedPts H Q) (by omega) (((1 : G)) : G ⧸ H)
  obtain ⟨h₂, hh₂⟩ := QuotientGroup.mk_surjective ω₂
  have hh₂stab : Submission.Blueprint.conj h₂ H = MulAction.stabilizer G ω₂ := by
    rw [← hh₂, Work.ThreePoints.stabilizer_mk]
  have hQh₂ : Q ≤ Submission.Blueprint.conj h₂ H := by
    rw [hh₂stab]
    exact Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mp (hh₂ ▸ hω₂)
  have hh₂ne : Submission.Blueprint.conj h₂ H ≠ H := by
    intro h
    have h1 : Submission.Blueprint.conj h₂ H = Submission.Blueprint.conj (((1 : G))) H := by
      rw [Work.ThreePoints.conj_one]; exact h
    have h2 : ((h₂ : G) : G ⧸ H) = (((1 : G)) : G ⧸ H) :=
      Work.ThreePoints.mk_eq_of_conj_eq hH h1
    exact hω₂ne (by rw [← hh₂, h2])
  have hh₂H : h₂ ∉ H := fun h => hh₂ne (Work.ThreePoints.conj_eq_self_of_mem h)
  have hv_notin : v ∉ Submission.Blueprint.conj h₂ H := by
    intro hmem
    have hfix : v • ω₂ = ω₂ :=
      MulAction.mem_stabilizer_iff.mp (by rw [← hh₂stab]; exact hmem)
    exact hω₂ne (hvuniq ω₂ hfix)
  have h1h₂ : (((1 : G)) : G ⧸ H) ≠ ((h₂ : G) : G ⧸ H) := by
    intro h
    rw [QuotientGroup.eq] at h
    exact hh₂H (by simpa using h)
  have h1vh₂ : (((1 : G)) : G ⧸ H) ≠ (((v * h₂ : G)) : G ⧸ H) := by
    intro h
    rw [QuotientGroup.eq] at h
    have h2 : v * h₂ ∈ H := by simpa using h
    exact hh₂H (by simpa using H.mul_mem (H.inv_mem hvH) h2)
  have hh₂vh₂ : ((h₂ : G) : G ⧸ H) ≠ (((v * h₂ : G)) : G ⧸ H) := by
    intro h
    rw [QuotientGroup.eq] at h
    have h2 : v ∈ Submission.Blueprint.conj h₂ H := by
      rw [Work.ThreePoints.mem_conj_iff]
      simpa [mul_assoc] using h
    exact hv_notin h2
  have hne1 : Submission.Blueprint.conj (((1 : G))) H ≠ Submission.Blueprint.conj g H := by
    rw [Work.ThreePoints.conj_one]
    intro h
    exact hg ((Work.ThreePoints.IsStronglyEmbedded.normalizer_eq hH) ▸
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm))
  have hne2 : Submission.Blueprint.conj (((1 : G))) H ≠ Submission.Blueprint.conj h₂ H := by
    rw [Work.ThreePoints.conj_one]
    exact fun h => hh₂ne h.symm
  have hu1 : u ∈ Submission.Blueprint.involutions
      ((Submission.Blueprint.conj (((1 : G))) H : Subgroup G) : Set G) := by
    rw [Work.ThreePoints.conj_one]; exact hu
  have hv1 : v ∈ Submission.Blueprint.involutions
      ((Submission.Blueprint.conj (((1 : G))) H : Subgroup G) : Set G) := by
    rw [Work.ThreePoints.conj_one]; exact ⟨hvH, hv2⟩
  obtain ⟨x, hx1, hx2, hxu⟩ := ch1_sec6_cor1 hH h2t hne1 hne2 hu1 hv1
  have hxH : Submission.Blueprint.conj x H = H := by
    have h := hx1; rwa [Work.ThreePoints.conj_one] at h
  have hxu' : x * u = v * x := by
    calc x * u = (x * u * x⁻¹) * x := by group
      _ = v * x := by rw [hxu]
  have hQvh₂ : Q ≤ Submission.Blueprint.conj (v * h₂) H := by
    have h1 : Submission.Blueprint.conj v Q ≤
        Submission.Blueprint.conj v (Submission.Blueprint.conj h₂ H) := Subgroup.map_mono hQh₂
    rw [hvQ, ← Work.ThreePoints.conj_mul] at h1
    exact h1
  -- ## the two-point stabiliser `E`
  have hkey : Submission.Blueprint.conj x (Submission.Blueprint.twoPoint H g ⊓
        Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H g)) =
      ((H ⊓ Submission.Blueprint.conj h₂ H) ⊓ (H ⊓ Submission.Blueprint.conj (v * h₂) H)) := by
    have e1 : Submission.Blueprint.conj x (Submission.Blueprint.twoPoint H g) =
        H ⊓ Submission.Blueprint.conj h₂ H := by
      show Submission.Blueprint.conj x (H ⊓ Submission.Blueprint.conj g H) = _
      rw [Work.ThreePoints.conj_inf, hxH, hx2]
    have e2 : Submission.Blueprint.conj x
        (Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H g)) =
        H ⊓ Submission.Blueprint.conj (v * h₂) H := by
      calc Submission.Blueprint.conj x
            (Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H g))
          = Submission.Blueprint.conj (x * u) (Submission.Blueprint.twoPoint H g) :=
              (Work.ThreePoints.conj_mul x u (Submission.Blueprint.twoPoint H g)).symm
        _ = Submission.Blueprint.conj (v * x) (Submission.Blueprint.twoPoint H g) := by
              rw [hxu']
        _ = Submission.Blueprint.conj v (Submission.Blueprint.conj x
              (Submission.Blueprint.twoPoint H g)) :=
              Work.ThreePoints.conj_mul v x (Submission.Blueprint.twoPoint H g)
        _ = Submission.Blueprint.conj v (H ⊓ Submission.Blueprint.conj h₂ H) := by rw [e1]
        _ = Submission.Blueprint.conj v H ⊓
              Submission.Blueprint.conj v (Submission.Blueprint.conj h₂ H) :=
              Work.ThreePoints.conj_inf v H (Submission.Blueprint.conj h₂ H)
        _ = H ⊓ Submission.Blueprint.conj (v * h₂) H := by
              rw [Work.ThreePoints.conj_eq_self_of_mem hvH, ← Work.ThreePoints.conj_mul]
    calc Submission.Blueprint.conj x (Submission.Blueprint.twoPoint H g ⊓
            Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H g))
        = Submission.Blueprint.conj x (Submission.Blueprint.twoPoint H g) ⊓
            Submission.Blueprint.conj x
              (Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H g)) :=
              Work.ThreePoints.conj_inf x _ _
      _ = (H ⊓ Submission.Blueprint.conj h₂ H) ⊓
            (H ⊓ Submission.Blueprint.conj (v * h₂) H) := by rw [e1, e2]
  have hQE : Q ≤ (H ⊓ Submission.Blueprint.conj h₂ H) ⊓
      (H ⊓ Submission.Blueprint.conj (v * h₂) H) := by
    refine le_inf ?_ ?_
    · exact le_inf hQT.2.1 hQh₂
    · exact le_inf hQT.2.1 hQvh₂
  have hE3 : ∀ R : Subgroup G,
      R ≤ (H ⊓ Submission.Blueprint.conj h₂ H) ⊓ (H ⊓ Submission.Blueprint.conj (v * h₂) H) →
      3 ≤ (Submission.Blueprint.fixedPts H R).ncard := by
    intro R hR
    refine three_le R (((1 : G)) : G ⧸ H) ((h₂ : G) : G ⧸ H) (((v * h₂ : G)) : G ⧸ H)
      h1h₂ h1vh₂ hh₂vh₂ ?_ ?_ ?_
    · rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.conj_one]
      exact (hR.trans inf_le_left).trans inf_le_left
    · rw [Work.ThreePoints.stabilizer_mk]
      exact (hR.trans inf_le_left).trans inf_le_right
    · rw [Work.ThreePoints.stabilizer_mk]
      exact (hR.trans inf_le_right).trans inf_le_right
  have hQmaxE : ∀ R : Subgroup G, Q ≤ R →
      R ≤ (H ⊓ Submission.Blueprint.conj h₂ H) ⊓ (H ⊓ Submission.Blueprint.conj (v * h₂) H) →
      IsPGroup p R → R = Q := by
    intro R hQR hRE hRp
    exact hQmaxH R hQR ((hRE.trans inf_le_left).trans inf_le_left) hRp (hE3 R hRE)
  -- ## `Q` and `conj x P` are both `p`-Sylows of `E`
  have hP'E : IsSylowOf p (Submission.Blueprint.conj x P)
      ((H ⊓ Submission.Blueprint.conj h₂ H) ⊓ (H ⊓ Submission.Blueprint.conj (v * h₂) H)) := by
    have h0 := hP.map_conj x
    rwa [hkey] at h0
  have hQidx : ¬ p ∣ (Q.subgroupOf
      ((H ⊓ Submission.Blueprint.conj h₂ H) ⊓ (H ⊓ Submission.Blueprint.conj (v * h₂) H))).index := by
    intro hdvd
    obtain ⟨R, hRE, hRp, hQR⟩ :=
      Work.ThreePoints.exists_pSubgroup_lt_of_dvd_index hp hQT.2.2.1 hQE hdvd
    exact hQR.ne (hQmaxE R hQR.le hRE hRp).symm
  have hP'idx : ¬ p ∣ ((Submission.Blueprint.conj x P).subgroupOf
      ((H ⊓ Submission.Blueprint.conj h₂ H) ⊓ (H ⊓ Submission.Blueprint.conj (v * h₂) H))).index := by
    intro hdvd
    obtain ⟨R, hRE, hRp, hRQ⟩ :=
      Work.ThreePoints.exists_pSubgroup_lt_of_dvd_index hp (hPp.map _) hP'E.1 hdvd
    exact hRQ.ne (hP'E.2.2 R hRQ.le hRE hRp).symm
  obtain ⟨e, heE, heconj⟩ := Work.ThreePoints.exists_conj_of_isSylowSubgroupOf hp hQE hQT.2.2.1
    hQidx hP'E.1 (hPp.map _) hP'idx
  have hPconj : P = Submission.Blueprint.conj (x⁻¹ * e) Q := by
    have h1 : Submission.Blueprint.conj x⁻¹ (Submission.Blueprint.conj e Q) =
        Submission.Blueprint.conj x⁻¹ (Submission.Blueprint.conj x P) := by rw [heconj]
    rw [← Work.ThreePoints.conj_mul, Work.DoubleTransitivity.conj_inv_conj] at h1
    exact h1.symm
  -- ## `P` is maximal
  have hQmaxG := (Work.ThreePoints.app2_6_uniform h2t hp hQT.2.1 hQT.2.2.1 hQT.2.2.2 hQmaxH).1
  refine ⟨hPp, h3P, ?_⟩
  intro R hPR hRp hR3
  have hQR' : Q ≤ Submission.Blueprint.conj (x⁻¹ * e)⁻¹ R := by
    have h1 : Submission.Blueprint.conj (x⁻¹ * e)⁻¹ P ≤
        Submission.Blueprint.conj (x⁻¹ * e)⁻¹ R := Subgroup.map_mono hPR
    rw [hPconj, Work.DoubleTransitivity.conj_inv_conj] at h1
    exact h1
  have hR3' : 3 ≤ (Submission.Blueprint.fixedPts H
      (Submission.Blueprint.conj (x⁻¹ * e)⁻¹ R)).ncard := by
    rw [Work.ThreePoints.fixedPts_conj, Set.ncard_smul_set]
    exact hR3
  have hthis := hQmaxG (Submission.Blueprint.conj (x⁻¹ * e)⁻¹ R) hQR' (hRp.map _) hR3'
  have h2 : Submission.Blueprint.conj (x⁻¹ * e)
        (Submission.Blueprint.conj (x⁻¹ * e)⁻¹ R) =
      Submission.Blueprint.conj (x⁻¹ * e) Q := by rw [hthis]
  rw [Work.DoubleTransitivity.conj_conj_inv] at h2
  exact h2.trans hPconj.symm

end Work.ThreePoints.ThmC
