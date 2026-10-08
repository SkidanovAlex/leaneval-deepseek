import Mathlib
import Submission.Work.ThreePoints.ThmC.hAprereq
import Submission.Work.ThreePoints.ThmC.hAzj
import Submission.Work.GlaubermanZJ.ZJ_le
import Submission.Work.ThreePoints.ThmC.hA_c1
import Submission.Work.ThreePoints.ThmC.hA_s
import Submission.Work.ThreePoints.ThmC.hA_step1
import Submission.Work.ThreePoints.ThmC.hA_step2
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.ThreePoints.ThmC.Base
import Submission.Work.ThreePoints.ThmC.app3_1
import Submission.Work.ThreePoints.ThmC.ch1_sec6_cor1
import Submission.Work.ThreePoints.ThmC.ch2_sec1_lem1
import Submission.Work.ThreePoints.ThmC.ch2_sec2_lem2
import Submission.Work.Models.models
import Submission.Work.ThreePoints.involutions_commute_of_below
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup
import Submission.Work.ThreePoints.app2_6_uniform
import Submission.Work.ThreePoints.TwoPointTransitive

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.ThmC

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- **Peterfalvi I Ch. II §3, Steps 1–3 (pp. 166–168): the subgroup `A` of a two-point
stabiliser.**

Let `G` satisfy `Situation G` (`HasFourGroup G`, `ThmBBelow |G|`, `O_{2'}(G) = ⊥`), let `H` be
strongly embedded in `G`, `t ∈ Inv(G∖H)`, `u ∈ Inv(H)`, `D = twoPoint H t = H ∩ H^t`, and suppose
`u` does not centralise `D₃ = D ⊓ D^u` (`D^u = conj u D`).  Then there is `A ≤ D` with `A ≠ ⊥`,
`A ⊴ D`, some involution `u' ∈ Inv(H)` normalising `A`, and `t ∈ N_G(A)`.

Route (the source's Ch. II §3, Steps 1–3, with `(C1)`: `p` odd and `P` a `p`-Sylow of `D₃`
normalised but not centralised by `u`, obtained from App. I (1)(b) and
`Work.ThreePoints.ThmC.app1_2`):

* **(C1)** exists because `u ∉ C(D₃)`: App. I (1)(b) gives `D₃ = C_{D₃}(u)·J(D₃,u)` with `J ≠ 1`;
  take `y ∈ J^#` of prime order `q` and extend `⟨y⟩` to a `q`-Sylow `P` of `D₃` normalised by `u`.
* **Step 1.** `O_{p'}(D₃) ≤ O_{p'}(D)` by `happ4` applied to `M = ↥D` (using `P` a `p`-Sylow of
  `P ⊔ (C_G(P) ⊓ D)`, which is `hlem1`'s clause (d), since `u ∉ C(P)`).  The reverse *order*
  inequality `|O_{p'}(D)| ≤ |O_{p'}(D₃)|` comes from `hsec6` applied to `(P,H,u)` together with
  Ch. I §6 Cor. 1 (`Work.ThreePoints.ThmC.ch1_sec6_cor1`):  `hsec6` gives `s ∈ Inv(G∖H)` with
  `O_{p'}(H ⊓ conj s H) ≤ O_{p'}(Stab ω ⊓ H ⊓ conj s H)`, and Cor. 1 transports the triple
  `(Stab ω, H, s)` to `(H, H^t, u)`, giving `O_{p'}(H^t ⊓ H^{ut}) ≤ O_{p'}(D₃)` with
  `|O_{p'}(H^t ⊓ H^{ut})| = |O_{p'}(D)|` (both are `O_{p'}` of a two-point stabiliser, and any two
  two-point stabilisers are conjugate by 2-transitivity, `hA`).  Hence `O_{p'}(D₃) = O_{p'}(D)`, so
  `u ∈ N_G(O_{p'}(D))` (as `u ∈ N_G(D₃)` and `u` normalises `O_{p'}(D₃)`).
* **Step 2.** If `O_{p'}(D) = ⊥`: let `𝒫 = {Q ≤ D : P ≤ Q, IsPGroup p Q, conj t Q = Q,
  involutions (normalizer P ⊓ H) ⊆ normalizer (ZJ Q)}`; a maximal element `Q` of `𝒫` is a `p`-Sylow
  of `D`.  If `N_G(P)` has 2-rank `1` this is `hlem1` (c).  Otherwise, for `Q ∈ 𝒫` not Sylow, take
  `F = N_G(ZJ Q)`, `R` a `p`-Sylow of `F ⊓ D` with `Q < R` normalised by `t` (App. I (2),
  `Work.ThreePoints.ThmC.app1_2`), and apply `hlem3` to `F` (whose `H_F = F ⊓ H` is strongly embedded
  with 2-rank `≥ 2` and whose involutions commute mod `O_{2'}(F)` by **(B1-a)**,
  `Work.ThreePoints.involutions_commute_of_below` with `hB1 = hSit.2.1` and
  `hMod = Work.Models.models_prop`, which is proved in-tree): this gives
  `Inv(F ⊓ H) ⊆ N(ZJ R)`, hence the `𝒫`-condition `(P3)` for `R` because `Inv(N(P) ⊓ H) ⊆ F`.
* **Step 3.** If `O_{p'}(D) ≠ ⊥` take `A = O_{p'}(D)` (characteristic in `D`, so `t ∈ N_G(A)` as
  `t ∈ N_G(D)`, and `u ∈ N_G(A)` by Step 1; `A ≠ ⊥` by assumption).  Otherwise take `A = ZJ Q` for a
  `p`-Sylow `Q` of `D` with `Q ∈ 𝒫` (Step 2): `A ⊴ D` because `hZJ` applied to `↥D` (odd order,
  Sylow 2-subgroups trivial, `pPrimeCore p D = ⊥`) makes `ZJ Q` characteristic in `D`; `u ∈ N_G(A)`
  by `(P3)` (as `u ∈ Inv(N(P) ⊓ H)`), `t ∈ N_G(A)` by `(P2)`, and `A ≠ ⊥` since
  `Z(J(Q)) ≠ 1` for a nontrivial `p`-group `Q` (`J(Q)` is a nontrivial `p`-group). -/
theorem hAexists (hFT : Submission.Blueprint.FeitThompsonProp)
    (hA : Submission.Blueprint.ThmAProp) (hZJ : Submission.Blueprint.GlaubermanZJProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    -- Peterfalvi Appendix IV (Thompson–Bender), solvable form
    (happ4 : ∀ (M : Type) [Group M] [Finite M] {p : ℕ}, p.Prime → p ≠ 2 → Group.IsSolvable M →
      ∀ {P X : Subgroup M}, IsPGroup p P →
        (∀ x : M, x ∈ Subgroup.centralizer (P : Set M) → orderOf x = p → x ∈ P) →
        Nat.Coprime (Nat.card X) p → P ≤ Subgroup.normalizer (X : Set M) →
        X ≤ Submission.Blueprint.pPrimeCore p M)
    -- Ch. II §2 Lemma 1
    (hlem1 : ∀ {G : Type} [Group G] [Finite G] {H : Subgroup G},
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded H → Submission.Blueprint.IsTwoTransitiveOn H →
      Submission.Blueprint.BrauerSuzukiProp → Submission.Blueprint.FeitThompsonProp →
      ∀ {g u : G}, g ∉ H → u ∈ Submission.Blueprint.involutions (H : Set G) →
      ∀ {p : ℕ} {P : Subgroup G}, p.Prime → p ≠ 2 →
      Work.ThreePoints.ThmC.IsSylowOf p P (Submission.Blueprint.twoPoint H g ⊓
        Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H g)) →
      u ∈ Subgroup.normalizer (P : Set G) →
      Work.ThreePoints.ThmC.IsMaxP3 H p P ∧
      (Work.DoubleTransitivity.IsTwoTransitiveOnSub (Subgroup.normalizer (P : Set G))
          (Submission.Blueprint.fixedPts H P) ∧
        ∀ g₁ : G, P ≤ Submission.Blueprint.conj g₁ H →
          LeanEval.GroupTheory.Defs.IsStronglyEmbedded
            ((Subgroup.normalizer (P : Set G) ⊓ Submission.Blueprint.conj g₁ H).subgroupOf
              (Subgroup.normalizer (P : Set G)))) ∧
      (¬ Submission.Blueprint.HasFourGroup (Subgroup.normalizer (P : Set G)) →
        Work.ThreePoints.ThmC.IsSylowOf p P (Submission.Blueprint.twoPoint H g)) ∧
      (¬ Work.ThreePoints.ThmC.IsSylowOf p P
          (P ⊔ (Subgroup.centralizer (P : Set G) ⊓ Submission.Blueprint.twoPoint H g)) →
        ∀ x ∈ P, u * x = x * u))
    -- Ch. II §2 Lemma 3
    (hlem3 : ∀ {F : Type} [Group F] [Finite F], Submission.Blueprint.FeitThompsonProp →
      Submission.Blueprint.GlaubermanZJProp → Submission.Blueprint.HasFourGroup F →
      ∀ {H : Subgroup F}, LeanEval.GroupTheory.Defs.IsStronglyEmbedded H →
      (∀ u v : F, u ∈ Submission.Blueprint.involutions (H : Set F) →
        v ∈ Submission.Blueprint.involutions (H : Set F) →
        u * v * u⁻¹ * v⁻¹ ∈ Submission.Blueprint.oddCore F) →
      ∀ {t : F}, orderOf t = 2 → t ∉ H → ∀ {p : ℕ} {R : Subgroup F}, p.Prime → p ≠ 2 →
      Work.ThreePoints.ThmC.IsSylowOf p R (Submission.Blueprint.twoPoint H t) →
      Submission.Blueprint.pPrimeCore p (Submission.Blueprint.twoPoint H t) = ⊥ →
      (∃ Q : Subgroup F, Q ≤ Submission.Blueprint.twoPoint H t ∧ IsPGroup p Q ∧
        ∃ u ∈ Submission.Blueprint.involutions (H : Set F),
          u ∈ Subgroup.normalizer (Q : Set F) ∧ ¬ ∀ x ∈ Q, u * x = x * u) →
      Submission.Blueprint.involutions (H : Set F) ⊆
        (Subgroup.normalizer (Submission.Blueprint.ZJ R : Set F) : Set F))
    -- Ch. I §6 Proposition 2
    (hsec6 : ∀ {G : Type} [Group G] [Finite G] {H : Subgroup G},
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded H → Submission.Blueprint.FeitThompsonProp →
      Submission.Blueprint.ThmAProp → Submission.Blueprint.BrauerSuzukiProp →
      Submission.Blueprint.HasFourGroup G →
      ∀ {p : ℕ} {P : Subgroup G}, p.Prime → p ≠ 2 → Work.ThreePoints.ThmC.IsMaxP3 H p P →
      P ≤ H → ∀ {u : G}, u ∈ Submission.Blueprint.involutions (H : Set G) →
      u ∈ Subgroup.normalizer (P : Set G) → (∃ x ∈ P, u * x ≠ x * u) →
      ∃ s : G, orderOf s = 2 ∧ s ∉ H ∧ ∀ ω : G ⧸ H, s • ω = ω →
        Work.ThreePoints.ThmC.pPrimeCoreSub p (H ⊓ Submission.Blueprint.conj s H) ≤
          Work.ThreePoints.ThmC.pPrimeCoreSub p
            (MulAction.stabilizer G ω ⊓ H ⊓ Submission.Blueprint.conj s H)) :
    ∀ {G : Type} [Group G] [Finite G], Submission.Blueprint.Situation G →
      ∀ {H : Subgroup G}, LeanEval.GroupTheory.Defs.IsStronglyEmbedded H →
      ∀ {t u : G}, orderOf t = 2 → t ∉ H →
      u ∈ Submission.Blueprint.involutions (H : Set G) →
      (∃ y ∈ Submission.Blueprint.twoPoint H t ⊓ Submission.Blueprint.conj u
          (Submission.Blueprint.twoPoint H t), u * y ≠ y * u) →
      ∃ A : Subgroup G, A ≤ Submission.Blueprint.twoPoint H t ∧ A ≠ ⊥ ∧
        (∀ d ∈ Submission.Blueprint.twoPoint H t, Submission.Blueprint.conj d A = A) ∧
        (∃ u' ∈ Submission.Blueprint.involutions (H : Set G),
          u' ∈ Subgroup.normalizer (A : Set G)) ∧
        t ∈ Subgroup.normalizer (A : Set G) := by
  intro G _ _ hSit H hH t u ht htH hu hnc
  have hfour : HasFourGroup G := hSit.1.1
  have h2t : IsTwoTransitiveOn H := hA G hfour H hH
  have htu : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
  have huu : u * u = 1 := by rw [← pow_two, ← hu.2]; exact pow_orderOf_eq_one u
  -- **(C1)**
  obtain ⟨p, P, hp, hpodd, hP, huP, hncP⟩ := hA_c1 hH ht htH hu hnc
  have hncP' : ∃ x ∈ P, u * x ≠ x * u := by
    by_contra h
    push_neg at h
    exact hncP h
  -- Ch. II §2 Lemma 1 for `P`
  obtain ⟨hmax, h1b, h1c, h1d⟩ := hlem1 (g := t) hH h2t hBrSz hFT htH hu hp hpodd hP huP
  -- `P` is a `p`-Sylow of `P·C(P) ∩ D` ((C1) + clause (d))
  have hSylowPC : IsSylowOf p P
      (P ⊔ (Subgroup.centralizer (P : Set G) ⊓ twoPoint H t)) := by
    by_contra hcon
    exact hncP (h1d hcon)
  -- **Step 1**: `O_{p'}(D ∩ D^u) = O_{p'}(D)`
  have hstep1 := hA_step1 hFT hA hBrSz happ4 hsec6 hSit hH ht htH hu hp hpodd hP huP hmax
    hSylowPC hncP'
  -- an involution `s` normalising `P` with `H ∩ H^s = D`
  obtain ⟨s, hsP, hs2, hsD⟩ := hA_s hH htH hp (le_trans hP.1 inf_le_left) hmax h1b.1
  -- basic facts about `D = twoPoint H t` and `D₃ = D ⊓ D^u`
  have hDodd : Odd (Nat.card ↥(twoPoint H t)) := IsStronglyEmbedded.odd_card_inf_conj hH htH
  have htD : t ∈ Subgroup.normalizer (twoPoint H t : Set G) := by
    rw [← Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer]
    rw [Work.ThreePoints.conj_inf]
    have h1 : Submission.Blueprint.conj t (Submission.Blueprint.conj t H) = H := by
      rw [← Work.DoubleTransitivity.conj_mul, htu, Work.DoubleTransitivity.conj_one]
    rw [h1, inf_comm]
  have huD3 : u ∈ Subgroup.normalizer
      (twoPoint H t ⊓ Submission.Blueprint.conj u (twoPoint H t) : Subgroup G) := by
    rw [← Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer]
    rw [Work.ThreePoints.conj_inf]
    have h1 : Submission.Blueprint.conj u (Submission.Blueprint.conj u (twoPoint H t)) =
        twoPoint H t := by
      rw [← Work.DoubleTransitivity.conj_mul, huu, Work.DoubleTransitivity.conj_one]
    rw [h1, inf_comm]
  rcases eq_or_ne (pPrimeCoreSub p (twoPoint H t)) ⊥ with hbotD | hneD
  · -- ## Step 2 / Step 3 with `A = ZJ Q`
    obtain ⟨Q, hQsyl, huQ⟩ := hA_step2 hFT hA hZJ hBrSz happ4 hlem1 hlem3 hSit hH ht htH hu
      hp hpodd hP huP hsP hs2 hsD hSylowPC hncP' hbotD
    have hPne : P ≠ ⊥ := by
      obtain ⟨x, hxP, hxne⟩ := hncP'
      intro hPbot
      refine hxne ?_
      have hx1 : x = 1 := Subgroup.mem_bot.mp (hPbot ▸ hxP)
      rw [hx1, mul_one, one_mul]
    have hpdvd : p ∣ Nat.card ↥(twoPoint H t) :=
      (prime_dvd_card_of_isPGroup_ne_bot hp hP.2.1 hPne).trans
        (Subgroup.card_dvd_of_le (le_trans hP.1 inf_le_left))
    have hQne : Q ≠ ⊥ := sylow_ne_bot_of_dvd hp hQsyl hpdvd
    refine ⟨Submission.Blueprint.ZJ Q, ?_, ?_, ?_, ⟨u, hu, huQ⟩, ?_⟩
    · exact le_trans (Work.GlaubermanZJ.ZJ_le Q) hQsyl.1
    · exact Work.GlaubermanZJ.ZJ_ne_bot hp Q hQsyl.2.1 hQne
    · intro d hd
      refine (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer d
        (Submission.Blueprint.ZJ Q)).mpr ?_
      refine normalizer_le_normalizer_ZJ hFT hZJ hp hpodd hDodd hQsyl hbotD ?_
      exact (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer d (twoPoint H t)).mp
        (Work.ThreePoints.conj_eq_self_of_mem hd)
    · exact normalizer_le_normalizer_ZJ hFT hZJ hp hpodd hDodd hQsyl hbotD htD
  · -- ## Step 3 with `A = O_{p'}(D)`
    refine ⟨pPrimeCoreSub p (twoPoint H t), ?_, ?_, ?_, ⟨u, hu, ?_⟩, ?_⟩
    · exact pPrimeCoreSub_le p (twoPoint H t)
    · exact hneD
    · intro d hd
      refine (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer d
        (pPrimeCoreSub p (twoPoint H t))).mpr ?_
      refine pPrimeCoreSub_mem_normalizer_of_mem_normalizer hp ?_
      exact (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer d (twoPoint H t)).mp
        (Work.ThreePoints.conj_eq_self_of_mem hd)
    · rw [← hstep1]
      exact pPrimeCoreSub_mem_normalizer_of_mem_normalizer hp huD3
    · exact pPrimeCoreSub_mem_normalizer_of_mem_normalizer hp htD

end Work.ThreePoints.ThmC
