import Mathlib
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.DoubleTransitivity.App2.app2_7
import Submission.Work.ThmF.ChV12.lemma2a_Q_regular
import Submission.Work.ThmF.ChV12.lemma2b
import Submission.Work.RankOneUniqueness.qPt_surjective
import Submission.Work.RankOneUniqueness.qPt_injective
import Submission.Work.ThreePoints.Omega

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.step6aux_count` — the fixed-point count `|Ω^X| = |C_Q(X)| + 1`

This is the only fragment of Peterfalvi II, Ch. V §3 that is derivable from the standing context
`CtxF` alone (the rest of the chain needs the near-field input of App. XI Prop. 1,
`WielandtFixedPoint`, `HallWielandtProp`, …).  It formalises blueprint L1514

`ncard_fixedPts_eq_card_inf_centralizer (h : IsSplitRankOne H Q t) (hXV : X ≤ centD H t) :
  (fixedPts H X).ncard = Nat.card ↥(Q ⊓ Subgroup.centralizer (X : Set G)) + 1`

and, as its cardinality ingredient, `|Ω| = |Q| + 1` (stated as a `sorry` in
`ChV12/lemma2a_card_omega.lean`).

All inputs are on disk and sorry-free: `RankOneUniqueness.qPt_surjective`/`qPt_injective`
(bijection `Q ≃ Ω ∖ {pt H}`), `ChV12.lemma2a_Q_regular` (regularity of `Q` on that complement),
Peterfalvi Appendix II (7) `DoubleTransitivity.App2.app2_7_core`, and the split decomposition
`ThmF.split_exists_unique_factor`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF.ChV3

variable {G : Type} [Group G] [Finite G]

/-! ## Elementary facts about the points of `Ω = G ⧸ H` -/

/-- `qPt H t q` is not the base point, for `q ∈ Q` (using `t ∉ H`). -/
private lemma qPt_ne_pt {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t)
    {q : G} (hq : q ∈ Q) : Work.RankOneUniqueness.qPt H t q ≠ Work.RankOneUniqueness.pt H := by
  intro hcon
  have h1 : ((q * t)⁻¹ * (1 : G)) ∈ H := QuotientGroup.eq.mp hcon
  rw [mul_one] at h1
  have h1' : t⁻¹ * q⁻¹ ∈ H := by simpa [mul_inv_rev] using h1
  have h3 : (t⁻¹ * q⁻¹) * q ∈ H := H.mul_mem h1' (h.le hq)
  have h4 : t⁻¹ ∈ H := by simpa using h3
  exact h.not_mem (by simpa using H.inv_mem h4)

/-- An element of the two-point stabiliser `D = H ⊓ Hᵗ` fixes the point `t • pt H`. -/
private lemma mem_stabilizer_smul_pt {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t)
    {d : G} (hd : d ∈ twoPoint H t) :
    d ∈ MulAction.stabilizer G (t • Work.RankOneUniqueness.pt H) := by
  have hdConj : d ∈ conj t H := (Subgroup.mem_inf.mp hd).2
  have hdt : t⁻¹ * d * t ∈ H := (Work.ThreePoints.mem_conj_iff).mp hdConj
  rw [MulAction.mem_stabilizer_iff]
  simp only [Work.RankOneUniqueness.smul_pt, Work.RankOneUniqueness.smul_mk, mul_one]
  rw [QuotientGroup.eq, show (d * t)⁻¹ * t = (t⁻¹ * d * t)⁻¹ by group]
  exact H.inv_mem hdt

/-- Converse of `mem_stabilizer_smul_pt`: an element of `H` fixing `t • pt H` lies in
`D = H ⊓ Hᵗ`. -/
private lemma mem_twoPoint_of_mem_stabilizers {H Q : Subgroup G} {t d : G}
    (h : IsSplitRankOne H Q t) (hdH : d ∈ H)
    (hd : d ∈ MulAction.stabilizer G (t • Work.RankOneUniqueness.pt H)) :
    d ∈ twoPoint H t := by
  have h1 : d • (t • Work.RankOneUniqueness.pt H) = t • Work.RankOneUniqueness.pt H :=
    MulAction.mem_stabilizer_iff.mp hd
  simp only [Work.RankOneUniqueness.smul_pt, Work.RankOneUniqueness.smul_mk, mul_one] at h1
  have h2 : (d * t)⁻¹ * t ∈ H := QuotientGroup.eq.mp h1
  have h3 : t⁻¹ * d * t ∈ H := by
    rw [show t⁻¹ * d * t = ((d * t)⁻¹ * t)⁻¹ by group]
    exact H.inv_mem h2
  exact ⟨hdH, (Work.ThreePoints.mem_conj_iff (H := H) (g := t) (x := d)).mpr h3⟩

/-! ## `|Ω| = |Q| + 1` -/

/-- **`|Ω| = |Q| + 1`** (`ChV12/lemma2a_card_omega`, proved here).  The map `q ↦ q·t·H` is a
bijection `Q ≃ Ω ∖ {pt H}`. -/
theorem card_omega_eq {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) :
    Nat.card (G ⧸ H) = Nat.card Q + 1 := by
  have hbij : Function.Bijective
      (fun q : ↥Q =>
        (⟨Work.RankOneUniqueness.qPt H t (q : G),
          by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact qPt_ne_pt h q.2⟩ :
            ↥(({Work.RankOneUniqueness.pt H}ᶜ : Set (G ⧸ H))))) := by
    constructor
    · intro a b hab
      exact Subtype.ext
        (Work.RankOneUniqueness.qPt_injective h a.2 b.2 (Subtype.ext_iff.mp hab))
    · intro ω
      have hω : (ω : G ⧸ H) ≠ Work.RankOneUniqueness.pt H := by
        exact ω.2
      obtain ⟨x, hx, hxω⟩ := Work.RankOneUniqueness.qPt_surjective h hω
      exact ⟨⟨x, hx⟩, Subtype.ext hxω⟩
  have hS : (({Work.RankOneUniqueness.pt H}ᶜ : Set (G ⧸ H))).ncard = Nat.card Q := by
    have hc := Nat.card_congr (Equiv.ofBijective _ hbij)
    exact hc.symm
  have h1 := Set.ncard_add_ncard_compl ({Work.RankOneUniqueness.pt H} : Set (G ⧸ H))
  rw [Set.ncard_singleton, hS] at h1
  omega

/-! ## The `(Q, D)`-decomposition of an element of `H` -/

/-- Uniqueness form of the split decomposition: every `x ∈ H = Q ⋊ D` is uniquely `q * d` with
`q ∈ Q`, `d ∈ twoPoint H t`. -/
private lemma existsUnique_mul_Q_twoPoint {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) {x : G} (hx : x ∈ H) :
    ∃! p : G × G, p.1 ∈ Q ∧ p.2 ∈ twoPoint H t ∧ p.1 * p.2 = x := by
  obtain ⟨p, hp, _huniq⟩ := Work.ThmF.split_exists_unique_factor h hx
  have hd : p.1 ∈ twoPoint H t := hp.1
  have hq : p.2 ∈ Q := hp.2.1
  have hpq : p.1 * p.2 = x := hp.2.2
  have hdH : p.1 ∈ H := (Subgroup.mem_inf.mp hd).1
  have hq' : p.1 * p.2 * p.1⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (h.normal hdH) p.2).mp hq
  have hprod : (p.1 * p.2 * p.1⁻¹) * p.1 = x := by
    rw [← hpq]; group
  refine ⟨(p.1 * p.2 * p.1⁻¹, p.1), ⟨hq', hd, hprod⟩, ?_⟩
  rintro ⟨q, d⟩ ⟨hqQ, hdD, hqd⟩
  have hqQ' : q ∈ Q := hqQ
  have hdD' : d ∈ twoPoint H t := hdD
  have hqd' : q * d = x := hqd
  have hkey : d * p.1⁻¹ = q⁻¹ * (p.1 * p.2 * p.1⁻¹) := by
    have h1 : q * d = p.1 * p.2 := by rw [hqd', ← hprod]; group
    calc d * p.1⁻¹ = q⁻¹ * (q * d) * p.1⁻¹ := by group
      _ = q⁻¹ * (p.1 * p.2) * p.1⁻¹ := by rw [h1]
      _ = q⁻¹ * (p.1 * p.2 * p.1⁻¹) := by group
  have hmemD : d * p.1⁻¹ ∈ twoPoint H t := (twoPoint H t).mul_mem hdD' ((twoPoint H t).inv_mem hd)
  have hmemQ : q⁻¹ * (p.1 * p.2 * p.1⁻¹) ∈ Q := Q.mul_mem (Q.inv_mem hqQ') hq'
  have hmemD' : q⁻¹ * (p.1 * p.2 * p.1⁻¹) ∈ twoPoint H t := by
    rw [← hkey]; exact hmemD
  have hzero : d * p.1⁻¹ = 1 := by
    have hmem : d * p.1⁻¹ ∈ Q ⊓ twoPoint H t := by
      rw [hkey]; exact ⟨hmemQ, hmemD'⟩
    rwa [h.inf_eq, Subgroup.mem_bot] at hmem
  have hd_eq : d = p.1 := by
    have h2 := congrArg (fun z => z * p.1) hzero
    simpa using h2
  have hq_eq : q = p.1 * p.2 * p.1⁻¹ := by
    have h2 : q * p.1 = p.1 * p.2 := by
      have h4 : q * d = (p.1 * p.2 * p.1⁻¹) * p.1 := by rw [hqd', hprod]
      rw [hd_eq] at h4
      calc q * p.1 = (p.1 * p.2 * p.1⁻¹) * p.1 := h4
        _ = p.1 * p.2 := by group
    calc q = q * p.1 * p.1⁻¹ := by group
      _ = p.1 * p.2 * p.1⁻¹ := by rw [h2]
  exact Prod.ext hq_eq hd_eq

/-! ## The fixed-point count -/

/-- **Blueprint L1514.**  `|Ω^X| = |C_Q(X)| + 1` for `X ≤ V = C_D(t)`. -/
theorem ncard_fixedPts_eq_card_inf_centralizer {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) {X : Subgroup G} (hXV : X ≤ centD H t) :
    (fixedPts H X).ncard = Nat.card ↥(Q ⊓ Subgroup.centralizer (X : Set G)) + 1 := by
  have hu : t • Work.RankOneUniqueness.pt H ≠ Work.RankOneUniqueness.pt H :=
    Work.RankOneUniqueness.t_smul_pt_ne h
  have hcard : Nat.card (Work.DoubleTransitivity.Omega H) = Nat.card Q + 1 := card_omega_eq h
  have hreg : Work.DoubleTransitivity.IsRegularOnSub Q
      ({Work.RankOneUniqueness.pt H}ᶜ : Set (Work.DoubleTransitivity.Omega H)) :=
    Work.ThmF.ChV12.lemma2a_Q_regular h hcard
  have hstab1 : MulAction.stabilizer G (Work.RankOneUniqueness.pt H) = H := by
    simpa [Work.RankOneUniqueness.pt] using Work.ThmF.ChV12.stabilizer_one H
  -- `X ≤ H ⊓ Hᵗ`, whence `X` fixes both `pt H` and `t • pt H`
  have hXV' : X ≤ twoPoint H t := hXV.trans inf_le_left
  have hY : X ≤ MulAction.stabilizer G (Work.RankOneUniqueness.pt H)
      ⊓ MulAction.stabilizer G (t • Work.RankOneUniqueness.pt H) := by
    refine le_inf ?_ ?_
    · rw [hstab1]; exact hXV'.trans inf_le_left
    · exact fun x hx => mem_stabilizer_smul_pt h (hXV' hx)
  -- the unique decomposition hypothesis of Appendix II (7)
  have hdec : ∀ h' ∈ MulAction.stabilizer G (Work.RankOneUniqueness.pt H),
      ∃! q : ↥Q, ∃ d ∈ MulAction.stabilizer G (Work.RankOneUniqueness.pt H)
          ⊓ MulAction.stabilizer G (t • Work.RankOneUniqueness.pt H), (q : G) * d = h' := by
    intro h' hh'
    have hh'H : h' ∈ H := by rw [hstab1] at hh'; exact hh'
    obtain ⟨p, hp, huniqp⟩ := existsUnique_mul_Q_twoPoint h hh'H
    have hpQ : p.1 ∈ Q := hp.1
    have hpD : p.2 ∈ twoPoint H t := hp.2.1
    have hpq : p.1 * p.2 = h' := hp.2.2
    refine ⟨⟨p.1, hpQ⟩, ⟨p.2, ⟨?_, mem_stabilizer_smul_pt h hpD⟩, hpq⟩, ?_⟩
    · rw [hstab1]; exact (Subgroup.mem_inf.mp hpD).1
    · rintro ⟨q, hqQ⟩ ⟨d, hd, hqd⟩
      have hd1 : d ∈ MulAction.stabilizer G (Work.RankOneUniqueness.pt H) := (Subgroup.mem_inf.mp hd).1
      have hd2 : d ∈ MulAction.stabilizer G (t • Work.RankOneUniqueness.pt H) :=
        (Subgroup.mem_inf.mp hd).2
      have hdH : d ∈ H := by rw [← hstab1]; exact hd1
      have hpair : (q, d) = p := huniqp (q, d) ⟨hqQ, mem_twoPoint_of_mem_stabilizers h hdH hd2, hqd⟩
      exact Subtype.ext (congrArg Prod.fst hpair)
  obtain ⟨_hQstab, hvfix, huniq⟩ :=
    Work.DoubleTransitivity.App2.app2_7_core (X := G) (E := G ⧸ H)
      (u := Work.RankOneUniqueness.pt H) (v := t • Work.RankOneUniqueness.pt H)
      (Q := Q) (Y := X) hu.symm (by rw [hstab1]; exact h.le) (by rw [hstab1]; exact h.normal)
      hreg hdec hY
  -- the bijection `Q ⊓ C_G(X) ≃ (fixedPts H X) ∖ {pt H}`
  have hmain : (((Work.DoubleTransitivity.fixedBySub X : Set (G ⧸ H))) \
        {Work.RankOneUniqueness.pt H}).ncard
      = Nat.card ↥(Q ⊓ Subgroup.centralizer (X : Set G)) := by
    have hmem_fix : ∀ (q : ↥(Q ⊓ Subgroup.centralizer (X : Set G))),
        (q : G) • (t • Work.RankOneUniqueness.pt H)
          ∈ (Work.DoubleTransitivity.fixedBySub X : Set (G ⧸ H)) := by
      intro q
      rw [Work.DoubleTransitivity.mem_fixedBySub]
      intro m hm
      have hm2 : m ∈ twoPoint H t := hXV' hm
      have hm3 : t⁻¹ * m⁻¹ * t ∈ H :=
        (Work.ThreePoints.mem_conj_iff (H := H) (g := t) (x := m⁻¹)).mp
          (Subgroup.mem_inf.mp ((twoPoint H t).inv_mem hm2)).2
      have hcomm : m * (q : G) = (q : G) * m :=
        Subgroup.mem_centralizer_iff.mp q.2.2 m hm
      have hcomm' : (q : G)⁻¹ * m⁻¹ = m⁻¹ * (q : G)⁻¹ := by
        rw [← mul_inv_rev, hcomm, mul_inv_rev]
      have hkey : (m * (q * t))⁻¹ * (q * t) = t⁻¹ * m⁻¹ * t := by
        calc (m * (q * t))⁻¹ * (q * t)
            = (q * t)⁻¹ * m⁻¹ * (q * t) := by group
          _ = t⁻¹ * ((q : G)⁻¹ * m⁻¹) * (q * t) := by group
          _ = t⁻¹ * (m⁻¹ * (q : G)⁻¹) * (q * t) := by rw [hcomm']
          _ = t⁻¹ * m⁻¹ * t := by group
      simp only [Work.RankOneUniqueness.smul_pt, Work.RankOneUniqueness.smul_mk, mul_one]
      rw [QuotientGroup.eq, hkey]
      exact hm3
    have hmem_ne : ∀ (q : ↥(Q ⊓ Subgroup.centralizer (X : Set G))),
        (q : G) • (t • Work.RankOneUniqueness.pt H) ≠ Work.RankOneUniqueness.pt H := by
      intro q hcon
      have hqstab : (q : G) ∈ MulAction.stabilizer G (Work.RankOneUniqueness.pt H) := by
        rw [hstab1]; exact h.le q.2.1
      have hqstab' : (q : G)⁻¹ ∈ MulAction.stabilizer G (Work.RankOneUniqueness.pt H) :=
        (MulAction.stabilizer G _).inv_mem hqstab
      have hfix : (q : G)⁻¹ • Work.RankOneUniqueness.pt H = Work.RankOneUniqueness.pt H :=
        MulAction.mem_stabilizer_iff.mp hqstab'
      have h1 : (q : G)⁻¹ • ((q : G) • (t • Work.RankOneUniqueness.pt H))
          = (q : G)⁻¹ • Work.RankOneUniqueness.pt H := congrArg _ hcon
      rw [inv_smul_smul, hfix] at h1
      exact hu h1
    have hbij : Function.Bijective
        (fun q : ↥(Q ⊓ Subgroup.centralizer (X : Set G)) =>
          (⟨(q : G) • (t • Work.RankOneUniqueness.pt H),
            Set.mem_sdiff_of_mem (hmem_fix q)
              (by simpa [Set.mem_singleton_iff] using hmem_ne q)⟩ :
            ↥((((Work.DoubleTransitivity.fixedBySub X : Set (G ⧸ H))) \
              {Work.RankOneUniqueness.pt H})))) := by
      constructor
      · intro a b hab
        have heq : (a : G) • (t • Work.RankOneUniqueness.pt H)
            = (b : G) • (t • Work.RankOneUniqueness.pt H) := Subtype.ext_iff.mp hab
        exact (huniq ((a : G) • (t • Work.RankOneUniqueness.pt H)) (hmem_fix a)
          (hmem_ne a)).unique rfl heq.symm
      · intro ω
        have hωmem : (ω : G ⧸ H) ∈ (Work.DoubleTransitivity.fixedBySub X : Set (G ⧸ H)) :=
          ω.2.1
        have hωne : (ω : G ⧸ H) ≠ Work.RankOneUniqueness.pt H := by
          simpa [Set.mem_singleton_iff] using ω.2.2
        obtain ⟨q, hq⟩ := (huniq (ω : G ⧸ H) hωmem hωne).exists
        exact ⟨q, Subtype.ext hq⟩
    have hc := Nat.card_congr (Equiv.ofBijective _ hbij)
    exact hc.symm
  have hmem_pt : Work.RankOneUniqueness.pt H
      ∈ (Work.DoubleTransitivity.fixedBySub X : Set (G ⧸ H)) := by
    rw [Work.DoubleTransitivity.mem_fixedBySub]
    intro m hm
    exact MulAction.mem_stabilizer_iff.mp (hY hm).1
  have h1 := Set.ncard_sdiff_singleton_add_one hmem_pt
  rw [hmain] at h1
  have hfix : (fixedPts H X) = (Work.DoubleTransitivity.fixedBySub X : Set (G ⧸ H)) := rfl
  rw [hfix]
  omega

/-- The count in the form requested for `X = P` (`step6`'s neighbourhood). -/
theorem step6aux_count {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hC4 : ChIIFourProp) (c : CtxF H Q t s r P) :
    Nat.card ↥(CQ Q P) + 1 = (fixedPts H P).ncard := by
  have h := ncard_fixedPts_eq_card_inf_centralizer c.split c.P_le
  simpa [CQ] using h.symm

end Work.ThmF.ChV3
