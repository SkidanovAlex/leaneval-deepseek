import Mathlib
import Submission.Work.ThreePoints.ThmC.hAprereq
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.ThreePoints.ThmC.ch1_sec6_cor1
import Submission.Work.ThreePoints.ThmC.pPrimeCoreSub_conj
import Submission.Work.ThreePoints.involutions_conj_of_stronglyEmbedded
import Submission.Work.ThreePoints.ThmC.hA_step1_forward
import Submission.Work.ThreePoints.ThmC.hA_step1_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThreePoints.ThmC

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- Monotonicity of the cardinality of a subgroup under inclusion (statement kept in the
`Subgroup` universe to avoid unfolding `Nat.card` of a `Set`). -/
theorem natCard_le_of_le {G : Type} [Group G] [Finite G] {A B : Subgroup G} (h : A ≤ B) :
    Nat.card ↥A ≤ Nat.card ↥B := by
  rw [show Nat.card ↥A = (A : Set G).ncard from Nat.card_coe_set_eq (A : Set G),
      show Nat.card ↥B = (B : Set G).ncard from Nat.card_coe_set_eq (B : Set G)]
  exact Set.ncard_le_ncard (fun x hx => h hx)

/-- **Peterfalvi I Ch. II §3, Step 1, the transport of Ch. I §6 Prop. 2 by Ch. I §6 Cor. 1.**

`hsec` is the conclusion of Ch. I §6 Prop. 2 for the triple `(H, P, u)`: there is an involution
`s ∉ H` so that for every point `ω` of `Ω = G ⧸ H` fixed by `s`,
`O_{p'}(H ⊓ H^s) ≤ O_{p'}(Stab_G(ω) ⊓ H ⊓ H^s)`.  Taking `ω` the (unique) fixed point of `s` and
transporting the triple `(Stab ω, H, s)` to `(H, H^t, u)` with Ch. I §6 Cor. 1 gives an element `x`
with `conj x (Stab ω) = H`, `conj x H = H^t` and `x s x⁻¹ = u`.  Conjugating the inequality by `x`
(`pPrimeCoreSub_conj`) and computing the images (`x s = u x`, `u ∈ H`) yields

`O_{p'}(H^t ⊓ H^{ut}) ≤ O_{p'}(H ⊓ H^t ⊓ H^{ut})`. -/
theorem hA_step1_transport_aux {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsStronglyEmbedded H)
    (h2t : IsTwoTransitiveOn H)
    {t u : G} (ht : orderOf t = 2) (htH : t ∉ H)
    (hu : u ∈ involutions (H : Set G))
    {p : ℕ} (hp : p.Prime)
    (hsec : ∃ s : G, orderOf s = 2 ∧ s ∉ H ∧
      ∀ ω : G ⧸ H, s • ω = ω →
        pPrimeCoreSub p (H ⊓ conj s H) ≤
          pPrimeCoreSub p (MulAction.stabilizer G ω ⊓ H ⊓ conj s H)) :
    pPrimeCoreSub p (conj t H ⊓ conj (u * t) H) ≤
      pPrimeCoreSub p (H ⊓ conj t H ⊓ conj (u * t) H) := by
  classical
  obtain ⟨s, hs2, hsH, hprop⟩ := hsec
  -- the unique fixed point of `s`
  obtain ⟨ω, hωfix, -⟩ := Work.ThreePoints.existsUnique_fixedPts_of_orderOf_eq_two hH hs2
  have hpropω := hprop ω hωfix
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective ω
  have hstab : MulAction.stabilizer G ω = conj g₀ H := by
    rw [← hg₀, Work.ThreePoints.stabilizer_mk]
  have hsStab : s ∈ MulAction.stabilizer G ω := MulAction.mem_stabilizer_iff.mpr hωfix
  have hsconj : s ∈ conj g₀ H := by rw [← hstab]; exact hsStab
  have hne1 : conj g₀ H ≠ conj 1 H := by
    intro h
    have hs1 : s ∈ conj 1 H := by rw [← h]; exact hsconj
    rw [Work.ThreePoints.conj_one] at hs1
    exact hsH hs1
  have hne2 : conj 1 H ≠ conj t H := by
    intro h
    rw [Work.ThreePoints.conj_one] at h
    have hmem : t ∈ Subgroup.normalizer (H : Set G) :=
      (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer t H).mp h.symm
    exact htH (by rwa [Work.ThreePoints.IsStronglyEmbedded.normalizer_eq hH] at hmem)
  have hsInv : s ∈ involutions ((conj g₀ H : Subgroup G) : Set G) := ⟨hsconj, hs2⟩
  have huInv : u ∈ involutions ((conj 1 H : Subgroup G) : Set G) := by
    rw [Work.ThreePoints.conj_one]; exact hu
  obtain ⟨x, hx1, hx2, hxs⟩ := ch1_sec6_cor1 hH h2t hne1 hne2 hsInv huInv
  rw [Work.ThreePoints.conj_one] at hx1 hx2
  have hxs' : x * s = u * x := by rw [← hxs]; group
  have htrans : pPrimeCoreSub p (conj x (H ⊓ conj s H)) ≤
      pPrimeCoreSub p (conj x (MulAction.stabilizer G ω ⊓ H ⊓ conj s H)) := by
    rw [pPrimeCoreSub_conj p hp (H ⊓ conj s H) x,
        pPrimeCoreSub_conj p hp (MulAction.stabilizer G ω ⊓ H ⊓ conj s H) x]
    exact Subgroup.map_mono hpropω
  have hL : conj x (H ⊓ conj s H) = conj t H ⊓ conj (u * t) H := by
    rw [Work.ThreePoints.conj_inf x H (conj s H), hx2,
      ← Work.ThreePoints.conj_mul x s H, hxs', Work.ThreePoints.conj_mul u x H, hx2,
      ← Work.ThreePoints.conj_mul u t H]
  have hR : conj x (MulAction.stabilizer G ω ⊓ H ⊓ conj s H) =
      H ⊓ conj t H ⊓ conj (u * t) H := by
    rw [Work.ThreePoints.conj_inf x (MulAction.stabilizer G ω ⊓ H) (conj s H),
      Work.ThreePoints.conj_inf x (MulAction.stabilizer G ω) H, hstab]
    rw [hx1, hx2, ← Work.ThreePoints.conj_mul x s H, hxs',
      Work.ThreePoints.conj_mul u x H, hx2, ← Work.ThreePoints.conj_mul u t H]
  rw [← hL, ← hR]
  exact htrans

/-- **Peterfalvi I Ch. II §3, Step 1.**  With `p` odd, `P` a `p`-Sylow of `D ⊓ D^u` (where
`D = twoPoint H t = H ⊓ H^t`) normalised by `u ∈ Inv(H)`, `P` maximal among the `p`-subgroups
fixing `≥ 3` points and a `p`-Sylow of `P ⊔ (C_G(P) ⊓ D)`, and `u` not centralising `P`, one has
`O_{p'}(D ⊓ D^u) = O_{p'}(D)`.

The forward inclusion `O_{p'}(D ⊓ D^u) ≤ O_{p'}(D)` is Peterfalvi Appendix IV (Thompson–Bender,
`hA_step1_forward`).  For the reverse, Ch. I §6 Prop. 2 (`hsec6`) produces an involution `s ∉ H`
with `O_{p'}(H ⊓ H^s) ≤ O_{p'}(Stab(ω) ⊓ H ⊓ H^s)` for its fixed point `ω`, and Ch. I §6 Cor. 1
transports this (`hA_step1_transport_aux`) to `O_{p'}(H^t ⊓ H^{ut}) ≤ O_{p'}(D ⊓ D^u)`; the left
hand side has the same order as `O_{p'}(D)` because `H^t ⊓ H^{ut}` is conjugate to `D` by
`2`-transitivity (`hA_step1_conj`).  Hence `|O_{p'}(D)| ≤ |O_{p'}(D ⊓ D^u)|`, and the two
inclusions together give the equality. -/
theorem hA_step1 (hFT : Submission.Blueprint.FeitThompsonProp)
    (hA : Submission.Blueprint.ThmAProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (happ4 : Work.ThreePoints.ThmC.App4Hyp) (hsec6 : Work.ThreePoints.ThmC.Sec6Hyp)
    {G : Type} [Group G] [Finite G] (hSit : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    {t u : G} (ht : orderOf t = 2) (htH : t ∉ H)
    (hu : u ∈ Submission.Blueprint.involutions (H : Set G))
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) {P : Subgroup G}
    (hP : Work.ThreePoints.ThmC.IsSylowOf p P (Submission.Blueprint.twoPoint H t ⊓
      Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H t)))
    (huP : u ∈ Subgroup.normalizer (P : Set G))
    (hmax : Work.ThreePoints.ThmC.IsMaxP3 H p P)
    (hSylowPC : Work.ThreePoints.ThmC.IsSylowOf p P
      (P ⊔ (Subgroup.centralizer (P : Set G) ⊓ Submission.Blueprint.twoPoint H t)))
    (hnc : ∃ x ∈ P, u * x ≠ x * u) :
    Work.ThreePoints.ThmC.pPrimeCoreSub p (Submission.Blueprint.twoPoint H t ⊓
        Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H t)) =
      Work.ThreePoints.ThmC.pPrimeCoreSub p (Submission.Blueprint.twoPoint H t) := by
  classical
  have hDleH : Submission.Blueprint.twoPoint H t ≤ H := by
    rw [Work.ThreePoints.twoPoint_eq H t]; exact inf_le_left
  have hPH : P ≤ H := hP.1.trans (inf_le_left.trans hDleH)
  -- `D ⊓ D^u = D ⊓ H^{ut}` since `u ∈ H`
  have hD3decomp : Submission.Blueprint.twoPoint H t ⊓
      Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H t) =
      Submission.Blueprint.twoPoint H t ⊓ Submission.Blueprint.conj (u * t) H := by
    have h1 : Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H t) =
        H ⊓ Submission.Blueprint.conj (u * t) H := by
      rw [Work.ThreePoints.twoPoint_eq H t,
        Work.ThreePoints.conj_inf u H (Submission.Blueprint.conj t H),
        Work.ThreePoints.conj_eq_self_of_mem hu.1,
        ← Work.ThreePoints.conj_mul u t H]
    rw [h1, ← inf_assoc, inf_eq_left.mpr hDleH]
  rw [hD3decomp]
  by_cases hdeg : Submission.Blueprint.conj (u * t) H = Submission.Blueprint.conj t H
  · -- degenerate case: `D ⊓ D^u = D`
    have hz : Submission.Blueprint.twoPoint H t ⊓ Submission.Blueprint.conj (u * t) H =
        Submission.Blueprint.twoPoint H t := by
      rw [Work.ThreePoints.twoPoint_eq H t, hdeg, inf_assoc, inf_idem]
    rw [hz]
  · have hfour : Submission.Blueprint.HasFourGroup G := hSit.1.1
    have h2t : Submission.Blueprint.IsTwoTransitiveOn H := hA G hfour H hH
    -- forward inclusion (Peterfalvi App. IV)
    have hfwd : Work.ThreePoints.ThmC.pPrimeCoreSub p (Submission.Blueprint.twoPoint H t ⊓
        Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H t)) ≤
        Work.ThreePoints.ThmC.pPrimeCoreSub p (Submission.Blueprint.twoPoint H t) :=
      hA_step1_forward hFT happ4 hH htH hp hpodd hP hSylowPC
    have hfwd' : Work.ThreePoints.ThmC.pPrimeCoreSub p (Submission.Blueprint.twoPoint H t ⊓
        Submission.Blueprint.conj (u * t) H) ≤
        Work.ThreePoints.ThmC.pPrimeCoreSub p (Submission.Blueprint.twoPoint H t) := by
      rw [← hD3decomp]; exact hfwd
    -- Ch. I §6 Prop. 2 and its transport by Cor. 1
    have hsec : ∃ s : G, orderOf s = 2 ∧ s ∉ H ∧
        ∀ ω : G ⧸ H, s • ω = ω →
          Work.ThreePoints.ThmC.pPrimeCoreSub p (H ⊓ Submission.Blueprint.conj s H) ≤
            Work.ThreePoints.ThmC.pPrimeCoreSub p
              (MulAction.stabilizer G ω ⊓ H ⊓ Submission.Blueprint.conj s H) :=
      hsec6 hH hFT hA hBrSz hfour hp hpodd hmax hPH hu huP hnc
    have hT := hA_step1_transport_aux hH h2t ht htH hu hp hsec
    have hT' : Work.ThreePoints.ThmC.pPrimeCoreSub p (Submission.Blueprint.conj t H ⊓
        Submission.Blueprint.conj (u * t) H) ≤
        Work.ThreePoints.ThmC.pPrimeCoreSub p (Submission.Blueprint.twoPoint H t ⊓
          Submission.Blueprint.conj (u * t) H) := by
      rw [Work.ThreePoints.twoPoint_eq H t]; exact hT
    -- `H^t ⊓ H^{ut}` is conjugate to `D`, so the two `p'`-cores have the same order
    have hC := hA_step1_conj h2t htH (fun h => hdeg h.symm) hp
    have hle1 : Nat.card (Work.ThreePoints.ThmC.pPrimeCoreSub p (Submission.Blueprint.twoPoint H t)) ≤
        Nat.card (Work.ThreePoints.ThmC.pPrimeCoreSub p (Submission.Blueprint.twoPoint H t ⊓
          Submission.Blueprint.conj (u * t) H)) := by
      rw [← hC]
      exact natCard_le_of_le hT'
    have hle2 : Nat.card (Work.ThreePoints.ThmC.pPrimeCoreSub p (Submission.Blueprint.twoPoint H t ⊓
          Submission.Blueprint.conj (u * t) H)) ≤
        Nat.card (Work.ThreePoints.ThmC.pPrimeCoreSub p (Submission.Blueprint.twoPoint H t)) :=
      natCard_le_of_le hfwd'
    have hcardeq : Nat.card (Work.ThreePoints.ThmC.pPrimeCoreSub p (Submission.Blueprint.twoPoint H t ⊓
          Submission.Blueprint.conj (u * t) H)) =
        Nat.card (Work.ThreePoints.ThmC.pPrimeCoreSub p (Submission.Blueprint.twoPoint H t)) :=
      le_antisymm hle2 hle1
    exact Subgroup.eq_of_le_of_card_ge hfwd' (le_of_eq hcardeq.symm)

end Work.ThreePoints.ThmC
