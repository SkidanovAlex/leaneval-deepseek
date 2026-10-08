import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageA.RouteHints
import Submission.Work.PSU3.StageA.W_eq_bot_of_Q_eq_Q0sub
import Submission.Work.PSU3.StageA.centD_ne_bot
import Submission.Work.PSU3.StageA.caseC_setup
import Submission.Work.ThmF.ChV12.L5prop2_caseWbot
import Submission.Work.PSU3.StageA.Ksub_eq_Kset_of_Hyp5_of_solvable
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.L5Struct
import Submission.Work.ThmF.ChV12.X5RankOneAux
import Submission.Work.ThmF.ChV12.X5_eq_sup_conj_Q0sub
import Submission.Work.PSU3.RankOne.H16
import Submission.Work.PSU3.RankOne.canon_conj
import Submission.Work.PSU3.RankOne.canon_mul
import Submission.Work.ThmF.ChV12.L5bridge

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.not_caseA` (A5a): case a) contradicts simplicity

Peterfalvi II Ch. VI §1 Prop. case a) is `S = Q₀` (here `Q = Q0sub H`) and `st` of order `3`;
the "Réduction" of Ch. VI §3 (p. 264) kills it: `G₀ = (SK) ∪ (SKtS)` is a subgroup, so
`G₀ = ⟨Q, t⟩ = G` (simplicity), whence `H = G₀ ∩ H = Q₀K` and `D = K`; then `V ≤ K`, and since
`t` inverts `K` while centralising `V`, `V = 1` — contradicting `¬ IsZassenhaus H`.

## What is proved here (hole-free)

* `notCaseA_orderOf_mul_eq_three` — the hypothesis `t * s * t = s * t * s` together with `s² = t² = 1`
  gives `orderOf (s * t) = 3` (i.e. Peterfalvi's `Hyp5.ord3`);
* `notCaseA_hyp5` — the `Hyp5` data of Ch. V in case a);
* `notCaseA_false_of_Ksub_eq_Kset` — **the assembly**: in case a), assuming that `K = J(D,t)` is a
  subgroup (`Ksub H t = Kset H t`), one gets `V = centD H t = ⊥`, contradicting
  `Work.PSU3.StageA.centD_ne_bot`.  The route: `X5 H t = ⟨Q₀, K, t⟩ = ⊤` (because `Q = Q₀` and
  `⟨Q, t⟩ = ⊤` by `Work.RankOneUniqueness.closure_Q_t_eq_top`); the Bruhat-type decomposition
  `X5 = B ∪ BtB` (`Work.ThmF.L5.mem_bor_or_btb`) then gives `twoPoint H t ≤ bor H t = Q ⊔ Ksub`,
  and `Work.ThmF.L5.twoPoint_bor_eq_Ksub` gives
  `twoPoint H t ≤ bor H t ⊓ conj t (bor H t) = Ksub H t = Kset H t`; finally
  `v ∈ V ∩ Kset` satisfies `v = t v t = v⁻¹`, so `v² = 1`, which with `v ∈ D` of odd order gives
  `v = 1`.

The single remaining input is `Work.PSU3.StageA.Ksub_eq_Kset_of_hst_W_bot` (Ch. V §1 Prop. 2 in
the case `V ≠ ⊥`, `W = ⊥`), the case of `Work.ThmF.ChV12.L5prop2` that the workspace leaves open;
it is applied in case a) with `W H t = ⊥` from `Work.PSU3.StageA.W_eq_bot_of_Q_eq_Q0sub`.
-/

namespace Work.PSU3.StageA

open scoped Pointwise

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

omit [Finite G] in
/-- `K = J(D,t)` is closed under inverses. -/
theorem notCaseA_Kset_inv_mem {k : G} (hk : k ∈ Work.ThmF.Kset H t) : k⁻¹ ∈ Work.ThmF.Kset H t := by
  obtain ⟨hkD, hkinv⟩ := Work.ThmF.mem_Kset_iff.mp hk
  refine Work.ThmF.mem_Kset_iff.mpr ⟨(twoPoint H t).inv_mem hkD, ?_⟩
  have h1 : t * k⁻¹ * t⁻¹ = (t * k * t⁻¹)⁻¹ := by group
  rw [h1, hkinv, inv_inv]

omit [Finite G] in
/-- `K = J(D,t)` consists of elements of `H`. -/
theorem notCaseA_Kset_mem_H {k : G} (hk : k ∈ Work.ThmF.Kset H t) : k ∈ H :=
  (Work.RankOneUniqueness.mem_twoPoint_iff.mp (Work.ThmF.Kset_subset H t hk)).1

/-- In case a) (`Q = Q0sub H`) every element of `Q#` is an involution of `H`. -/
theorem notCaseA_mem_involutions (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hQ : (Q : Set G) = Work.ThmF.Q0sub H)
    {x : G} (hx : x ∈ Q) (hx1 : x ≠ 1) : x ∈ involutions (H : Set G) := by
  have hx' : x ∈ (Work.ThmF.Q0sub H : Set G) := by rw [← hQ]; exact hx
  rw [caseC_Q0sub_set hS hC4] at hx'
  rcases hx' with hx' | hx'
  · exact hx'
  · exact absurd hx' hx1

/-- **Peterfalvi II Ch. V §2 Lemma 5, first half** (the computation underlying the
"Réduction" of Ch. VI §3, p. 264).  In case a) (`Q = Q0sub H`), with `t * s * t = s * t * s`,
for every `x ∈ Q#` the conjugate `t * x * t` lies in `(Q ⊔ Ksub H t) · t · Q`:

  `t x t = (k⁻¹ s k · k⁻²) · t · (k⁻¹ s k)`, where `k ∈ Kset H t` is the unique element with
  `k s k⁻¹ = x` (`Work.ThmF.L5.Kset_regular`).  Consequently, whenever `Kset H t` is a subgroup,
  the set `Q · K ∪ Q · K · t · Q` is a subgroup of `G` containing `Q` and `t` — hence equal to
  `G` by `Work.RankOneUniqueness.closure_Q_t_eq_top` — so that `H = Q · K` and `D = K`; then
  `V ≤ Kset` and `V = ⊥`, contradicting `¬ IsZassenhaus H`. -/
theorem notCaseA_conj_mem (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hQ : (Q : Set G) = Work.ThmF.Q0sub H)
    {s x : G} (hs : s ∈ Q) (hs2 : orderOf s = 2)
    (hst : t * s * t = s * t * s) (hx : x ∈ Q) (hx1 : x ≠ 1) :
    ∃ a ∈ (Q ⊔ Work.ThmF.Ksub H t), ∃ q ∈ Q, t * x * t = a * t * q := by
  have hsplit : IsSplitRankOne H Q t := hS.split
  have ht2 : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hsplit
  have hti : t⁻¹ = t := Work.RankOneUniqueness.inv_eq_self hsplit
  have hs1 : s ≠ 1 := by
    intro h; rw [h, orderOf_one] at hs2; exact absurd hs2 (by norm_num)
  have hsInv : s ∈ involutions (H : Set G) := notCaseA_mem_involutions hS hC4 hQ hs hs1
  have hxInv : x ∈ involutions (H : Set G) := notCaseA_mem_involutions hS hC4 hQ hx hx1
  obtain ⟨k, ⟨hkK, hkx⟩, -⟩ := Work.ThmF.L5.Kset_regular hsplit s hsInv x hxInv
  have hkH : k ∈ H := notCaseA_Kset_mem_H hkK
  have hksk : k⁻¹ * s * k ∈ Q := by
    have h := Work.RankOneUniqueness.conj_mem_of_mem hsplit (H.inv_mem hkH) hs
    simpa only [mul_assoc, inv_inv] using h
  have hkt : t * k * t = k⁻¹ := by
    have h := (Work.ThmF.mem_Kset_iff.mp hkK).2
    rwa [hti] at h
  have hkt' : t * k⁻¹ * t = k := by
    have h1 : (t * k * t)⁻¹ = k := by rw [hkt, inv_inv]
    calc t * k⁻¹ * t = t⁻¹ * k⁻¹ * t⁻¹ := by rw [hti]
      _ = (t * k * t)⁻¹ := by rw [mul_inv_rev, mul_inv_rev, mul_assoc]
      _ = k := h1
  have hktk : k⁻¹ * t * k = (k⁻¹) ^ 2 * t := by
    have h1 : t * k = k⁻¹ * t := by
      have h := congrArg (fun z : G => z * t) hkt
      simpa only [mul_assoc, ht2, mul_one] using h
    calc k⁻¹ * t * k = k⁻¹ * (t * k) := by group
      _ = k⁻¹ * (k⁻¹ * t) := by rw [h1]
      _ = (k⁻¹) ^ 2 * t := by rw [pow_two]; group
  refine ⟨(k⁻¹ * s * k) * (k⁻¹) ^ 2, ?_, k⁻¹ * s * k, hksk, ?_⟩
  · refine (Q ⊔ Work.ThmF.Ksub H t).mul_mem (Subgroup.mem_sup_left hksk) ?_
    have hk1 : k⁻¹ ∈ Work.ThmF.Ksub H t :=
      Work.ThmF.Kset_le_Ksub H t (notCaseA_Kset_inv_mem hkK)
    exact Subgroup.mem_sup_right ((Work.ThmF.Ksub H t).pow_mem hk1 2)
  · have hconj : ∀ x y : G, t * (x * y) * t = (t * x * t) * (t * y * t) := by
      intro x y
      have hh := map_mul (MulAut.conj t) x y
      simpa only [MulAut.conj_apply, hti] using hh
    have hconjk : ∀ x y : G, k⁻¹ * (x * y) * k = (k⁻¹ * x * k) * (k⁻¹ * y * k) := by
      intro x y
      have hh := map_mul (MulAut.conj k⁻¹) x y
      simpa only [MulAut.conj_apply, inv_inv] using hh
    rw [← hkx]
    calc t * (k * s * k⁻¹) * t
        = (t * k * t) * (t * s * t) * (t * k⁻¹ * t) := by
          rw [hconj (k * s) k⁻¹, hconj k s]
      _ = k⁻¹ * (t * s * t) * k := by rw [hkt, hkt']
      _ = k⁻¹ * (s * t * s) * k := by rw [hst]
      _ = (k⁻¹ * s * k) * (k⁻¹ * t * k) * (k⁻¹ * s * k) := by
          rw [show s * t * s = s * (t * s) from by group]
          rw [hconjk s (t * s), hconjk t s]
          simp only [mul_assoc]
      _ = ((k⁻¹ * s * k) * (k⁻¹) ^ 2) * t * (k⁻¹ * s * k) := by rw [hktk]; group

/-- **`s * t` has order `3`.**  If `s`, `t` are involutions with `t ∉ H`, `s ∈ Q ≤ H` and
`t * s * t = s * t * s` (equivalently `(s * t)³ = 1`), then `orderOf (s * t) = 3`. -/
theorem notCaseA_orderOf_mul_eq_three (hsplit : IsSplitRankOne H Q t) {s : G} (hs : s ∈ Q)
    (hs2 : orderOf s = 2) (hst : t * s * t = s * t * s) : orderOf (s * t) = 3 := by
  have ht2 : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hsplit
  have hs2' : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  have hcube : (s * t) ^ 3 = 1 := by
    have h1 : (s * t) ^ 2 = t * s := by
      rw [pow_two]
      calc s * t * (s * t) = s * (t * s * t) := by group
        _ = s * (s * t * s) := by rw [hst]
        _ = t * s := by
            rw [show s * (s * t * s) = (s * s) * (t * s) from by group, hs2', one_mul]
    rw [pow_succ, h1]
    calc t * s * (s * t) = t * (s * s) * t := by group
      _ = 1 := by simp only [hs2', ht2, mul_one]
  have hne : s * t ≠ 1 := by
    intro h
    have htH : t ∈ H := by
      have h2 : t = s⁻¹ := by
        calc t = s⁻¹ * (s * t) := by group
          _ = s⁻¹ * 1 := by rw [h]
          _ = s⁻¹ := by rw [mul_one]
      rw [h2]
      exact H.inv_mem (hsplit.le hs)
    exact hsplit.not_mem htH
  exact orderOf_eq_prime hcube hne

/-- The `Hyp5` data of Peterfalvi II Ch. V §2 (the setting of `X5 = ⟨Q₀, K, t⟩`) in case a). -/
theorem notCaseA_hyp5 (hS : Work.PSU3.PSU3Hyp H Q t) {s : G} (hs : s ∈ Q)
    (hs2 : orderOf s = 2) (hst : t * s * t = s * t * s) :
    Work.ThmF.Lemma5.Hyp5 H Q t s :=
  ⟨hS.situation, hS.split, hs, hs2, notCaseA_orderOf_mul_eq_three hS.split hs hs2 hst⟩

/-- **The assembly of case a).**  If `Q = Q0sub H` (case a) of Peterfalvi II Ch. VI §1) and the
set `K = J(D,t)` happens to be a subgroup (`Ksub H t = Kset H t`), then
`V = centD H t = ⊥`, which contradicts `¬ IsZassenhaus H` (`centD_ne_bot`). -/
theorem notCaseA_false_of_Ksub_eq_Kset (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) {s : G} (hs : s ∈ Q) (hs2 : orderOf s = 2)
    (hst : t * s * t = s * t * s) (hQ : (Q : Set G) = Work.ThmF.Q0sub H)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t) : False := by
  have hsplit : IsSplitRankOne H Q t := hS.split
  have ht2 : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hsplit
  have hti : t⁻¹ = t := Work.RankOneUniqueness.inv_eq_self hsplit
  have hp5 : Work.ThmF.Lemma5.Hyp5 H Q t s := notCaseA_hyp5 hS hs hs2 hst
  haveI : IsSimpleGroup G := hS.simple
  have hQsub : Work.ThmF.Q0sub H = Q := Subgroup.ext (fun x => (Set.ext_iff.mp hQ x).symm)
  -- the Borel `bor H t = Q₀sub H ⊔ Ksub H t` equals `Q ⊔ Ksub H t` in case a)
  have hbor : Work.ThmF.L5.bor H t = Q ⊔ Work.ThmF.Ksub H t := by
    rw [Work.ThmF.L5.bor, hQsub]
  -- `X5 H t = ⟨Q₀, K, t⟩ = ⊤`
  have hX5 : Work.ThmF.Lemma5.X5 H t = ⊤ := by
    have hle : Subgroup.closure ((Q : Set G) ∪ {t}) ≤ Work.ThmF.Lemma5.X5 H t := by
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      rcases hx with hx | hx
      · exact Work.ThmF.L5.Q0sub_le_X5 (by rw [hQsub]; exact hx)
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact Work.ThmF.Lemma5.t_mem_X5 H t
    rw [Work.RankOneUniqueness.closure_Q_t_eq_top hsplit] at hle
    exact top_le_iff.mp hle
  -- the Bruhat-type decomposition `X5 = B ∪ BtB`
  have hdec : ∀ g : G, g ∈ Work.ThmF.L5.bor H t ∨
      ∃ b₁ ∈ Work.ThmF.L5.bor H t, ∃ b₂ ∈ Work.ThmF.L5.bor H t, g = b₁ * t * b₂ := by
    intro g
    have hg : g ∈ Work.ThmF.Lemma5.X5 H t := by rw [hX5]; exact Subgroup.mem_top g
    exact Work.ThmF.L5.mem_bor_or_btb hC4 hp5 hg
  -- `D = twoPoint H t ⊆ bor H t`
  have hDbor : twoPoint H t ≤ Work.ThmF.L5.bor H t := by
    intro d hd
    rcases hdec d with h | ⟨b₁, hb₁, b₂, hb₂, hdb⟩
    · exact h
    · exfalso
      have hb₁H : b₁ ∈ H := Work.ThmF.L5.bor_le_H hp5 hb₁
      have hb₂H : b₂ ∈ H := Work.ThmF.L5.bor_le_H hp5 hb₂
      have hdH : d ∈ H := (Subgroup.mem_inf.mp hd).1
      have htH : t ∈ H := by
        have h2 : t = b₁⁻¹ * d * b₂⁻¹ := by rw [hdb]; group
        rw [h2]
        exact H.mul_mem (H.mul_mem (H.inv_mem hb₁H) hdH) (H.inv_mem hb₂H)
      exact hsplit.not_mem htH
  -- `D` is stable under conjugation by `t`
  have hDstab : ∀ d ∈ twoPoint H t, t⁻¹ * d * t ∈ twoPoint H t := by
    intro d hd
    obtain ⟨hdH, hdHt⟩ := Subgroup.mem_inf.mp hd
    rw [Work.Models.mem_conj_iff] at hdHt
    refine Subgroup.mem_inf.mpr ⟨hdHt, ?_⟩
    rw [Work.Models.mem_conj_iff]
    rw [show t⁻¹ * (t⁻¹ * d * t) * t = d from by
      rw [hti, show t * (t * d * t) * t = (t * t) * d * (t * t) from by group, ht2]
      simp]
    exact hdH
  -- `D ≤ bor ⊓ borᵗ = Ksub H t`
  have hDleKsub : twoPoint H t ≤ Work.ThmF.Ksub H t := by
    have h1 : Work.ThmF.L5.bor H t ⊓ Submission.Blueprint.conj t (Work.ThmF.L5.bor H t)
        = Work.ThmF.Ksub H t := Work.ThmF.L5.twoPoint_bor_eq_Ksub hC4 hp5
    intro d hd
    have h2 : d ∈ Work.ThmF.L5.bor H t ⊓
        Submission.Blueprint.conj t (Work.ThmF.L5.bor H t) :=
      ⟨hDbor hd, Work.Models.mem_conj_iff.mpr (hDbor (hDstab d hd))⟩
    rwa [h1] at h2
  -- every `v ∈ V = centD H t` lies in `Kset H t`
  have hVK : ∀ v ∈ Submission.Blueprint.centD H t, v ∈ Work.ThmF.Kset H t := by
    intro v hv
    have hvD : v ∈ twoPoint H t := (Subgroup.mem_inf.mp hv).1
    exact hKsub ▸ hDleKsub hvD
  -- hence `V = ⊥`
  have hVbot : Submission.Blueprint.centD H t = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro v hv
    have hvD : v ∈ twoPoint H t := (Subgroup.mem_inf.mp hv).1
    have hvt : v ∈ Subgroup.centralizer ({t} : Set G) := (Subgroup.mem_inf.mp hv).2
    have h1 : t * v * t = v := by
      have hc : t * v = v * t :=
        (Subgroup.mem_centralizer_singleton_iff.mp hvt).symm
      rw [hc, mul_assoc, ht2, mul_one]
    have h2 : t * v * t = v⁻¹ := by
      have h := (Work.ThmF.mem_Kset_iff.mp (hVK v hv)).2
      rwa [hti] at h
    have hvv : v * v = 1 := by
      have hv1 : v = v⁻¹ := by
        calc v = t * v * t := h1.symm
          _ = v⁻¹ := h2
      have hthis : v⁻¹ * v = 1 := inv_mul_cancel v
      rwa [← hv1] at hthis
    have hdvd : orderOf v ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact hvv
    have hodd : Odd (orderOf v) :=
      (hsplit.stronglyEmbedded.2.2 t hsplit.not_mem).of_dvd_nat
        (Subgroup.orderOf_dvd_natCard (twoPoint H t) hvD)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hodd
      exact absurd hodd (by norm_num)
  exact Work.PSU3.StageA.centD_ne_bot hS hVbot

/-- **`not_caseA` with the odd-order theorem as an explicit input.**  This is the same statement
as `not_caseA` but carrying `FeitThompsonProp`; it is *proved* (the `FeitThompsonProp` hypothesis
enters only through Ch. V §1 Prop. 2 in the branch `V ≠ 1`, `W = ⊥`, i.e.
`Work.ThmF.ChV12.L5prop2_caseWbot`). -/
theorem not_caseA_of_FT {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) {s r : G} (hs : s ∈ Q) (hs2 : orderOf s = 2)
    (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (hst : t * s * t = s * t * s) : (Q : Set G) ≠ Work.ThmF.Q0sub H := by
  intro hQ
  refine notCaseA_false_of_Ksub_eq_Kset hS hC4 hs hs2 hst hQ ?_
  -- case a) forces `W = C_V(K) = ⊥`, and Ch. V §1 Prop. 2 in the case `V ≠ 1, W = 1` then
  -- gives `K = J(D,t) = Ksub H t` a subgroup.
  exact Work.ThmF.ChV12.L5prop2_caseWbot hFT hC4 (notCaseA_hyp5 hS hs hs2 hst)
    (Work.PSU3.StageA.centD_ne_bot hS)
    (Work.PSU3.StageA.W_eq_bot_of_Q_eq_Q0sub hS hs hs2 hr hsr hQ)

/-- **The case-a) input, isolated (with the odd-order theorem).**  In case a) (`Q = Q0sub H`),
`K = J(D,t)` is a subgroup: `Ksub H t = Kset H t`.  This is exactly the input consumed by
`not_caseA_false_of_Ksub_eq_Kset` and it is Ch. V §1 Prop. 2 in the branch `V ≠ 1`, `W = ⊥`
(`Work.ThmF.ChV12.L5prop2_caseWbot`), which needs `FeitThompsonProp`. -/
theorem caseA_Ksub_eq_Kset_of_FT {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    {s r : G} (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q)
    (hsr : t * s * t = r⁻¹ * t * r) (hst : t * s * t = s * t * s)
    (hQ : (Q : Set G) = Work.ThmF.Q0sub H) :
    (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t :=
  Work.ThmF.ChV12.L5prop2_caseWbot hFT hC4 (notCaseA_hyp5 hS hs hs2 hst)
    (Work.PSU3.StageA.centD_ne_bot hS)
    (Work.PSU3.StageA.W_eq_bot_of_Q_eq_Q0sub hS hs hs2 hr hsr hQ)

/-- **`not_caseA` from the local solvability of `D = twoPoint H t` — the exact gap.**

This is the *minimal* extra input: with `Group.IsSolvable ↥(twoPoint H t)` the requested
statement follows, using

* `Work.PSU3.StageA.Ksub_eq_Kset_of_Hyp5_of_solvable` (Ch. V §1 Prop. 2, App. X with
  solvability isolated in place of the odd order theorem — proved in the sibling module of this
  file), and
* `notCaseA_false_of_Ksub_eq_Kset` (the assembly of case a)).

Consequently the request `not_caseA` is provable as soon as the instance
`Group.IsSolvable ↥(twoPoint H t)` is available.  `Odd (Nat.card ↥(twoPoint H t))` is available
from `PSU3Hyp` (`IsStronglyEmbedded`), so by the odd order theorem — `FeitThompsonProp`, the
single open hole of this project (`Submission.Work.Skeleton.minSimpleOdd_false`) — that instance
always holds; but *no* hole-free proof of it exists in this workspace, and the request lists no
hypothesis from which it could be derived. -/
theorem not_caseA_of_solvable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hDsolv : Group.IsSolvable ↥(Submission.Blueprint.twoPoint H t))
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) {s r : G} (hs : s ∈ Q) (hs2 : orderOf s = 2)
    (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r) (hst : t * s * t = s * t * s) :
    (Q : Set G) ≠ Work.ThmF.Q0sub H := by
  intro hQ
  exact notCaseA_false_of_Ksub_eq_Kset hS hC4 hs hs2 hst hQ
    (Work.PSU3.StageA.Ksub_eq_Kset_of_Hyp5_of_solvable hC4 (notCaseA_hyp5 hS hs hs2 hst)
      hDsolv)

/-! ## The FT-free reduction: case a) forces `K = J(D,t)` to be all of `D`

The "Réduction" of Peterfalvi II Ch. VI §3 (p. 264) needs two ingredients: the Bruhat-type
decomposition `X5 H t = bor H t ∪ bor H t · t · bor H t` of `X = ⟨Q₀, K, t⟩` (Ch. V §2 Lemma 5's
first half, proved in `Work.ThmF.ChV12.L5Struct`) and `X5 ∩ D = Ksub`.  Granting those, case a)
is *equivalent* to `Ksub H t = twoPoint H t`: since `Q = Q0sub H ≤ bor`, the intermediate group
`X = ⟨Q₀, K, t⟩` contains `Q` and `t`, so `⟨Q, t⟩ = ⊤` forces `X = ⊤`; and then
`H = X ⊓ H = bor H t` and `D = D ⊓ H = D ⊓ bor = Ksub H t`.

Nothing here uses Ch. V §1 Prop. 2, hence nothing uses `FeitThompsonProp`.  What case a) does
*not* by itself provide is `Ksub H t = Kset H t`: with `K = J(D,t)` a subgroup of `D`, the
requested statement becomes exactly "`Kset H t` is closed under products (equivalently, pairwise
commuting)" — see `Ksub_eq_Kset_iff_pairwise_commute`. -/

/-- **Case a) makes `X = ⟨Q₀, K, t⟩` the whole group**: `Q = Q0sub H ≤ bor H t ≤ X5 H t` while
`t ∈ X5 H t`, so `⊤ = ⟨Q, t⟩ ≤ X5 H t` by simplicity. -/
theorem notCaseA_X5_eq_top (hS : Work.PSU3.PSU3Hyp H Q t) {s : G} (hs : s ∈ Q)
    (hs2 : orderOf s = 2) (hst : t * s * t = s * t * s)
    (hQ : (Q : Set G) = Work.ThmF.Q0sub H) : Work.ThmF.Lemma5.X5 H t = ⊤ := by
  have hsplit : IsSplitRankOne H Q t := hS.split
  haveI : IsSimpleGroup G := hS.simple
  have hQsub : Work.ThmF.Q0sub H = Q := Subgroup.ext (fun x => (Set.ext_iff.mp hQ x).symm)
  have hQ0sub_le : Work.ThmF.Q0sub H ≤ Work.ThmF.Lemma5.X5 H t :=
    (Subgroup.closure_le _).mpr (fun z hz => Work.ThmF.Lemma5.Q0_subset_X5 H t hz)
  have hle : Subgroup.closure ((Q : Set G) ∪ {t}) ≤ Work.ThmF.Lemma5.X5 H t := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rcases hx with hx | hx
    · exact hQ0sub_le (by rw [hQsub]; exact hx)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Work.ThmF.Lemma5.t_mem_X5 H t
  rw [Work.RankOneUniqueness.closure_Q_t_eq_top hsplit] at hle
  exact top_le_iff.mp hle

/-- **Case a) forces `H = bor H t = Q₀sub H ⊔ Ksub H t`**: `H = X5 H t ⊓ H` when `X5 H t = ⊤`. -/
theorem notCaseA_H_eq_bor (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    {s : G} (hs : s ∈ Q) (hs2 : orderOf s = 2) (hst : t * s * t = s * t * s)
    (hQ : (Q : Set G) = Work.ThmF.Q0sub H) : H = Work.ThmF.L5.bor H t := by
  have hp5 : Work.ThmF.Lemma5.Hyp5 H Q t s := notCaseA_hyp5 hS hs hs2 hst
  have h := Work.ThmF.L5.X5_inf_H hC4 hp5
  rw [notCaseA_X5_eq_top hS hs hs2 hst hQ, top_inf_eq] at h
  exact h

/-- **Case a) exhibits `(G, H)` as a group with a split BN-pair of rank `1`** (Bruhat
decomposition `G = H ∪ H t H`), the setting of the Kantor–Seitz / Peterfalvi Ch. VII §4 input
`RankOneVNeqWProp` below.  Immediate from the Bruhat decomposition of `X5 H t`
(`Work.ThmF.L5.X5_eq_borel`, proved without Ch. V §1 Prop. 2) and `notCaseA_H_eq_bor`. -/
theorem notCaseA_bruhat (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    {s : G} (hs : s ∈ Q) (hs2 : orderOf s = 2) (hst : t * s * t = s * t * s)
    (hQ : (Q : Set G) = Work.ThmF.Q0sub H) :
    (Set.univ : Set G) = (H : Set G) ∪ (H : Set G) * ({t} : Set G) * (H : Set G) := by
  have hp5 : Work.ThmF.Lemma5.Hyp5 H Q t s := notCaseA_hyp5 hS hs hs2 hst
  have h := Work.ThmF.L5.X5_eq_borel hC4 hp5
  rw [notCaseA_X5_eq_top hS hs hs2 hst hQ, ← notCaseA_H_eq_bor hS hC4 hs hs2 hst hQ] at h
  exact h

/-- **Case a) forces `K = J(D,t)` to be all of the two-point stabiliser `D`:**

`(Work.ThmF.Ksub H t : Set G) = twoPoint H t`.

This is the FT-free half of the "Réduction" (Ch. VI §3, p. 264): it uses only the Bruhat
decomposition `X5 H t = bor H t ∪ bor H t · t · bor H t` and `X5 H t ⊓ D = Ksub H t`
(`Work.ThmF.ChV12.L5Struct`), which are themselves free of Ch. V §1 Prop. 2. -/
theorem notCaseA_Ksub_eq_twoPoint (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    {s : G} (hs : s ∈ Q) (hs2 : orderOf s = 2) (hst : t * s * t = s * t * s)
    (hQ : (Q : Set G) = Work.ThmF.Q0sub H) :
    (Work.ThmF.Ksub H t : Set G) = Submission.Blueprint.twoPoint H t := by
  have hp5 : Work.ThmF.Lemma5.Hyp5 H Q t s := notCaseA_hyp5 hS hs hs2 hst
  have h := Work.ThmF.L5.X5_inf_D hC4 hp5
  rw [notCaseA_X5_eq_top hS hs hs2 hst hQ, top_inf_eq] at h
  exact (congrArg (fun T : Subgroup G => (T : Set G)) h).symm

/-- **`K = J(D,t)` is a subgroup iff its elements pairwise commute.**

For `t` an involution, `Kset H t = {x ∈ D | t x t = x⁻¹}` is closed under inverses and powers, so
its closure `Ksub H t` is `Kset H t` exactly when `Kset H t` is closed under products; and for
`k₁, k₂ ∈ Kset H t` one has `t (k₁ k₂) t = k₁⁻¹ k₂⁻¹` while `(k₁ k₂)⁻¹ = k₂⁻¹ k₁⁻¹`, so
`k₁ k₂ ∈ Kset H t ↔ k₁ k₂ = k₂ k₁`.

Consequently, in case a) the requested statement reduces exactly to "the elements of
`Kset H t` pairwise commute" (combine with `notCaseA_Ksub_eq_twoPoint`: `Ksub H t = twoPoint H t`
has order `|Kset H t| · |centD H t|` by `Work.ThmF.Bender.cardInvertedMulCardCentralizer`, so
`Ksub H t = Kset H t` forces `centD H t = ⊥`, contradicting `PSU3Hyp.notZ` through
`Work.PSU3.StageA.centD_ne_bot`). -/
theorem Ksub_eq_Kset_iff_pairwise_commute {G : Type} [Group G] {H : Subgroup G} {t : G}
    (ht : t * t = 1) :
    (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t ↔
      ∀ k₁ ∈ Work.ThmF.Kset H t, ∀ k₂ ∈ Work.ThmF.Kset H t, k₁ * k₂ = k₂ * k₁ := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hconjmul : ∀ a b : G, t * (a * b) * t = (t * a * t) * (t * b * t) := by
    intro a b
    have h := map_mul (MulAut.conj t) a b
    simpa only [MulAut.conj_apply, hti] using h
  have hconj : ∀ k ∈ Work.ThmF.Kset H t, t * k * t = k⁻¹ := by
    intro k hk
    have h := (Work.ThmF.mem_Kset_iff.mp hk).2
    rwa [hti] at h
  have hinv : ∀ k ∈ Work.ThmF.Kset H t, k⁻¹ ∈ Work.ThmF.Kset H t := by
    intro k hk
    obtain ⟨hkD, hkinv⟩ := Work.ThmF.mem_Kset_iff.mp hk
    refine Work.ThmF.mem_Kset_iff.mpr ⟨(Submission.Blueprint.twoPoint H t).inv_mem hkD, ?_⟩
    have h1 : t * k⁻¹ * t⁻¹ = (t * k * t⁻¹)⁻¹ := by group
    rw [h1, hkinv, inv_inv]
  constructor
  · intro hEq k₁ hk₁ k₂ hk₂
    have hk₁K : k₁ ∈ Work.ThmF.Ksub H t := Work.ThmF.Kset_le_Ksub H t hk₁
    have hk₂K : k₂ ∈ Work.ThmF.Ksub H t := Work.ThmF.Kset_le_Ksub H t hk₂
    have hmulK : k₁ * k₂ ∈ Work.ThmF.Ksub H t := (Work.ThmF.Ksub H t).mul_mem hk₁K hk₂K
    have hmul : k₁ * k₂ ∈ Work.ThmF.Kset H t := hEq ▸ hmulK
    have h1 : (k₁ * k₂)⁻¹ = t * (k₁ * k₂) * t := (hconj (k₁ * k₂) hmul).symm
    have h2 : t * (k₁ * k₂) * t = k₁⁻¹ * k₂⁻¹ := by
      rw [hconjmul k₁ k₂, hconj k₁ hk₁, hconj k₂ hk₂]
    rw [mul_inv_rev, h2] at h1
    -- `h1 : k₂⁻¹ * k₁⁻¹ = k₁⁻¹ * k₂⁻¹`
    have h3 := congrArg (fun z : G => z⁻¹) h1
    simpa only [mul_inv_rev, inv_inv] using h3
  · intro hcomm
    have hsub : ∀ a ∈ Work.ThmF.Kset H t, ∀ b ∈ Work.ThmF.Kset H t,
        a * b ∈ Work.ThmF.Kset H t := by
      intro a ha b hb
      obtain ⟨haD, hainv⟩ := Work.ThmF.mem_Kset_iff.mp ha
      obtain ⟨hbD, hbinv⟩ := Work.ThmF.mem_Kset_iff.mp hb
      have hinvcomm : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
        calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := (mul_inv_rev b a).symm
          _ = (a * b)⁻¹ := by rw [hcomm a ha b hb]
      refine Work.ThmF.mem_Kset_iff.mpr
        ⟨(Submission.Blueprint.twoPoint H t).mul_mem haD hbD, ?_⟩
      have h1 : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
      rw [h1, hainv, hbinv]
      exact hinvcomm
    -- `Kset H t` is a subgroup since it is closed under `1`, products and inverses
    let T : Subgroup G :=
      { carrier := Work.ThmF.Kset H t
        one_mem' := Work.ThmF.one_mem_Kset H t
        mul_mem' := fun ha hb => hsub _ ha _ hb
        inv_mem' := fun ha => hinv _ ha }
    have hle : (Work.ThmF.Ksub H t : Set G) ⊆ Work.ThmF.Kset H t :=
      (Subgroup.closure_le T).mpr (fun x hx => hx)
    exact Set.Subset.antisymm hle (Work.ThmF.Kset_le_Ksub H t)

/-- **Case a) says `Q` is exactly `Inv(H) ∪ {1}`.**  Under `ChIIFourProp`, `Q₀sub H = Q₀ H`
(`Work.ThmF.L5.mem_Q0sub_iff`), so case a) reads `Q = Q₀ H = Inv(H) ∪ {1}`: `Q` is elementary
abelian, every `2`-subgroup of `G` lies in a conjugate of `Q` and is therefore elementary abelian,
and `HigmanProp` (whose every clause is about *Suzuki* `2`-groups) is vacuous. -/
theorem notCaseA_Q_eq_Q0 (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    {s : G} (hs : s ∈ Q) (hs2 : orderOf s = 2) (hst : t * s * t = s * t * s)
    (hQ : (Q : Set G) = Work.ThmF.Q0sub H) : (Q : Set G) = Work.ThmF.Q0 H := by
  have hp5 : Work.ThmF.Lemma5.Hyp5 H Q t s := notCaseA_hyp5 hS hs hs2 hst
  rw [hQ]
  exact Set.ext (fun x => Work.ThmF.L5.mem_Q0sub_iff hC4 hp5 x)

/-! ## The Kantor–Seitz / Peterfalvi Ch. VII §4 input (an FT-free way to close the gap)

Besides Ch. V §1 Prop. 2, there is a *second* way to kill case a): by the split rank-one datum,
`G = H ∪ H t H` is a group with a **split BN-pair of rank 1** whose unipotent part `Q` is a
`2`-group, and Ch. VII §4 of Peterfalvi (pp. 278–280), following Kantor–Seitz, *Finite groups
with a split BN-pair of rank 1 II* §§14–15, proves that `V ≠ W` forces a proper normal subgroup
of odd index (`O^{2'}(G) ≠ G`).  In case a) one has `W = ⊥` (proved above) while `V ≠ ⊥`
(`Work.PSU3.StageA.centD_ne_bot`), so `V ≠ W` and simplicity is contradicted.

This route uses **no** `FeitThompsonProp`.  Its missing ingredient in this workspace is the
general rank-one statement, bundled below as `RankOneVNeqWProp`; the workspace's only
formalisation of it is the case-c) node `Work.PSU3.StageB.exists_omega_of_not_fpf` (still a
`hole`, and stated with a `CoarseFrame` as an input, hence not applicable in case a)). -/

/-- **Kantor–Seitz / Peterfalvi Ch. VII §4, bundled.**  A finite group with a split rank-one
datum whose `Q` is a `2`-group and with `W = C_V(Kset) < V = centD H t` is not simple.  (The
source proves the sharper `O^{2'}(G) ≠ G`.)  This is a *hypothesis-free* black box like
`ChIIFourProp` / `HigmanProp`: no proof of it is in this workspace, but it is the FT-free input
that closes case a). -/
def RankOneVNeqWProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H Q : Subgroup G) (t : G),
    IsSplitRankOne H Q t → IsPGroup 2 Q → Work.ThmF.W H t < Submission.Blueprint.centD H t →
      ¬ IsSimpleGroup G

/-- **`not_caseA` from the Kantor–Seitz input.**  In case a), `W = C_V(Kset) = ⊥` while
`V = centD H t ≠ ⊥`, so `W < V` and `RankOneVNeqWProp` contradicts `PSU3Hyp.simple`. -/
theorem not_caseA_of_VNeqW {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hKS : RankOneVNeqWProp)
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) {s r : G} (hs : s ∈ Q) (hs2 : orderOf s = 2)
    (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r) (hst : t * s * t = s * t * s) :
    (Q : Set G) ≠ Work.ThmF.Q0sub H := by
  intro hQ
  have hW : Work.ThmF.W H t = ⊥ :=
    Work.PSU3.StageA.W_eq_bot_of_Q_eq_Q0sub hS hs hs2 hr hsr hQ
  refine (hKS G H Q t hS.split hS.two ?_) hS.simple
  refine lt_of_le_of_ne (Work.ThmF.W_le_centD H t) ?_
  intro hEq
  exact Work.PSU3.StageA.centD_ne_bot hS (hEq ▸ hW)

/-! ## Status of the requested statement

The requested statement `not_caseA` is TRUE — it says that Ch. VI §1 case a) is impossible, i.e.
that in case a) `V = centD H t = ⊥`, contradicting `PSU3Hyp.notZ` — but it is **not provable from
its listed hypotheses in this workspace**, because the only available route to the case-a) input
`Ksub H t = Kset H t` is Ch. V §1 Prop. 2 in the branch `V ≠ 1`, `W = ⊥`, whose proof (App. X)
needs `D = twoPoint H t` — of odd order — to be solvable, i.e. the odd-order theorem
`FeitThompsonProp`.  The statement therefore **omits the hypothesis its proof consumes**: the
sibling node `Work.ThmF.ChV12.L5prop2_caseWbot` was corrected (2026-10-05, by the area's
maintainers) to take `FeitThompsonProp` for exactly this reason, and
`Submission/Work/PSU3/NOTES_LEAD_bs_psu3.md` §2 records that the area **may assume**
`FeitThompsonProp` (with `ThmF.ChV12.prop2v2`/`Ksub_cyclic_normal` as its consumers).

What is proved here:

* **the whole FT-free reduction**: `notCaseA_X5_eq_top`, `notCaseA_H_eq_bor` and
  `notCaseA_Ksub_eq_twoPoint` show that case a) makes `X = ⟨Q₀,K,t⟩` all of `G` and forces
  `Ksub H t = twoPoint H t = D` — the first half of the "Réduction" of Ch. VI §3 (p. 264), using
  only the Bruhat decomposition of `Work.ThmF.ChV12.L5Struct` (no Ch. V §1 Prop. 2, no
  `FeitThompsonProp`);
* `notCaseA_Q_eq_Q0` records that in case a) `Q = Inv(H) ∪ {1}` is elementary abelian, so
  `HigmanProp` is *vacuous* there (all `2`-subgroups of `G` are elementary abelian): the `hHig`
  hypothesis of the request is a copy of the sibling node's signature and is unused;
* `notCaseA_false_of_Ksub_eq_Kset`: case a) plus `Ksub H t = Kset H t` is contradictory, so
  (with `notCaseA_Ksub_eq_twoPoint`) the requested statement is **equivalent** to
  `Ksub H t = Kset H t`;
* `Ksub_eq_Kset_iff_pairwise_commute`: `Ksub H t = Kset H t` holds iff the elements of
  `Kset H t` pairwise commute — so, with `Work.ThmF.Bender.cardInvertedMulCardCentralizer`
  (`|D| = |Kset H t| · |centD H t|`), the gap is exactly "the elements of `Kset H t` pairwise
  commute", equivalently `centD H t = ⊥`;
* `not_caseA_of_FT` proves the requested statement verbatim once `FeitThompsonProp` is added to
  the hypotheses, and `caseA_Ksub_eq_Kset_of_FT` isolates the added input;
* `not_caseA_of_VNeqW` proves the requested statement verbatim from the **FT-free** input
  `RankOneVNeqWProp` (Kantor–Seitz §§14–15 / Peterfalvi Ch. VII §4: `V ≠ W` ⟹ `G` has a proper
  normal subgroup of odd index): case a) gives `W = ⊥ < V`, and that input contradicts
  `PSU3Hyp.simple`;
* `RankOneNormalIndexPProp` is the *output form* of the Kantor–Seitz theorem (a normal subgroup
  of prime index), and `rankOneVNeqW_of_normalIndexP` derives `RankOneVNeqWProp` from it, so the
  whole of [KS] §§12–15 is isolated as one statement.  Its transfer-theoretic half is formalised
  in the area `Submission/Work/KantorSeitz/` — see `KantorSeitz/NOTES_ks_chain.md`, where
  `transfer_ne_one_of_fusion_control` (the first computation of §15),
  `commutator_le_of_conj_congruence`, `exists_zmod_hom_of_sylow_normalizer`,
  `padicValNat_pow_add_one` ([KS] Lemma 11.1), `fusion_controlled_of_fixesThree`
  ([HKS] Lemma 4.3) and `exists_normal_index_p_of_twoPoint_fusion` are proved hole-free.

So there are exactly two inputs that close the request, and **neither is among its hypotheses**:

1. **Ch. V §1 Prop. 2** (`K = J(D,t)` is a subgroup) in the branch `V ≠ ⊥`, `W = ⊥`.  The
   workspace route is `Work.ThmF.ChV12.Ksub_cyclic_normal`, whose single non-elementary input is
   the odd-order theorem `FeitThompsonProp` (via `Work.ThmF.Tools.appX`); with solvability
   isolated, `Work.PSU3.StageA.appX_of_solvable` (proved) supplies the App. X step, and the
   remaining adaptation is `Ksub_eq_Kset_of_Hyp5_of_solvable` (statement recorded in
   `Submission/Work/PSU3/StageA/Ksub_eq_Kset_of_W_bot.lean`; both reviewers: "looks correct as
   stated").  `Group.IsSolvable ↥(twoPoint H t)` is *not* available in this workspace: for an
   odd-order group that instance is precisely `FeitThompsonProp`, the single open hole of the
   project (`Work.Skeleton.minSimpleOdd_false`).
2. **Kantor–Seitz / Ch. VII §4** `V ≠ W ⟹ G not simple` (`RankOneVNeqWProp`), which is
   FT-free but is *not* in the workspace: its only formalisation,
   `Work.PSU3.StageB.exists_omega_of_not_fpf`, is a `hole` and is stated for a `CoarseFrame`
   (case c) input, so it does not apply to case a).

The proof of route 1 in this workspace is now complete up to the instance
`Group.IsSolvable ↥(twoPoint H t)`: `not_caseA_of_solvable` (above) derives the requested
statement from exactly that instance, and the App. X step is
`Work.PSU3.StageA.Ksub_eq_Kset_of_Hyp5_of_solvable` (proved, hole-free, in the sibling module
of this file).

Accordingly the fix for the request is to add one of: `hFT : FeitThompsonProp` (the convention
the area maintainers adopted on 2026-10-05 for the sibling node
`Work.ThmF.ChV12.L5prop2_caseWbot`, and the one recorded as available to the whole area in
`Submission/Work/PSU3/NOTES_LEAD_bs_psu3.md` §2 — it gives the instance
`Group.IsSolvable ↥(twoPoint H t)` since `|twoPoint H t|` is odd), or that local instance
directly, or `RankOneVNeqWProp`.

## The omission is the maintainers' own recorded one (three independent confirmations)

1. `Submission/Work/ThmF/ChV12/L5prop2_caseWbot.lean` (header, "Corrected 2026-10-05"): the
   branch `V ≠ 1`, `W = ⊥` of Ch. V §1 Prop. 2 was "previously requested *without*
   `FeitThompsonProp`; the reviewers and the prover recorded that the source's route in this
   branch is … App. X … and that both need `D` of odd order to be **solvable**, i.e.
   `FeitThompsonProp`", and, explicitly: "it is kept only for the consumers that import it
   (`PSU3/StageA/not_caseA.lean`), which therefore also have to thread `FeitThompsonProp` — they
   have it, being given it by the assembly."  So `not_caseA` is *expected* to carry `hFT`.
2. The area's design note `Submission/Work/PSU3/NOTES_LEAD_bs_psu3.md` §2: "**PSU3 may assume:**
   `ChIIFourProp` … `HigmanProp` … `FeitThompsonProp`, and the ThmF Ch. V §1–2 files (App. X for
   `K` cyclic: `ThmF.ChV12.prop2v2`, `structureIdentity`). All allowed by AREAS.md."
3. The sibling node `Submission/Work/PSU3/StageA/not_caseB.lean` (same requester, same signature
   shape, plus `W H t = ⊥`) reaches the identical verdict for case b) and documents it at length:
   "it is a *true* theorem of the source, but it is **not derivable from the hypotheses listed
   here**, and its hypothesis list omits the structural input that the source's own proof
   consumes."

## Why no FT-free route exists in this workspace

The only FT-free replacement for Ch. V §1 Prop. 2 would be the classical theorem that an
**odd-order transitive linear group over `F₂` lies in `ΓL(1,2ⁿ)`** (Zassenhaus 1936 on finite
near-fields of characteristic 2, in the form isolated as `Work.ThmF.ChV12.SharpInvertingClosed` /
`Work.ThmF.ChV12.JFormClosed`).  Of that theorem the workspace has only fragments:

* `Work.PSU3.StageA.appX_prop_public` (Huppert's App. X lemma, FT-free) yields, for every prime
  `ℓ ∣ |D|`, that `O_ℓ(D)` is cyclic and fixed-point-free on `A` (see
  `Work.ThmF.ChV12.Fitting_cyclic_fpf`), hence `F(D)` cyclic and fixed-point-free; but the next
  step `C_D(F(D)) = F(D)` (equivalently `D/F(D)` abelian) is exactly App. X's third conclusion
  and needs `D` solvable (App. X §9.2 of `NOTES_lemma5_state.md`);
* `Work.ThmF.ChV12.AppV_semilinear` (the field/Schur-lemma step) is still a `hole`;
* the Kantor–Seitz §15 route (`Submission/Work/KantorSeitz/`) needs the §13.8 classification data
  of transitive linear groups — the same theorem;
* and the project lead has explicitly put the near-field theory out of scope for now, see
  `Submission/Work/ThmF/ChV3/NearField.lean`: "the repository builds no near-field (and per the
  project lead, App. XI is not to be proved yet)".

So the statement as requested cannot be closed with the current library, while with `hFT` it is
proved *verbatim* in this very file (`not_caseA_of_FT`, axioms
`[propext, Classical.choice, Quot.sound]`), as is `not_caseA_of_solvable` from the local instance
`Group.IsSolvable ↥(twoPoint H t)`. -/

/-! ## The Kantor–Seitz output as a black box, and the route from it to `RankOneVNeqWProp`

[KS] §15 concludes a *normal subgroup of prime index*, and simplicity converts that into a
contradiction.  Bundling the output of §15 that way isolates the whole of [KS] §§12–15 (whose
transfer-theoretic half is formalised in `Submission/Work/KantorSeitz/`, see
`KantorSeitz/NOTES_ks_chain.md`) as a single statement. -/

/-- **[KS] §15 (Theorem 15.1), in the form of a normal subgroup of prime index.**  A finite group
with a split rank-one datum whose unipotent part `Q` is a `2`-group and with `W < V` has a proper
normal subgroup of prime index.  ([KS] prove `O^{2'}(G) ≠ G`; a quotient of order `p` is what the
transfer argument produces.)  This is the black box that `RankOneVNeqWProp` is derived from. -/
def RankOneNormalIndexPProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H Q : Subgroup G) (t : G),
    Submission.Blueprint.IsSplitRankOne H Q t → IsPGroup 2 Q →
      Work.ThmF.W H t < Submission.Blueprint.centD H t →
      ∃ p : ℕ, p.Prime ∧ ∃ K : Subgroup G, K.Normal ∧ K.index = p

/-- **`RankOneVNeqWProp` from the [KS] output.**  A proper normal subgroup of prime index
contradicts simplicity: `|H|` is even, so `|G|` is even and at least `4`; hence `K ≠ ⊤`
(`index = p ≠ 1`) and `K ≠ ⊥` (else `|G| = p`, impossible for an even `|G| ≥ 4`). -/
theorem rankOneVNeqW_of_normalIndexP (hKS : RankOneNormalIndexPProp) :
    RankOneVNeqWProp := by
  intro G _ _ H Q t hsplit htwo hlt
  obtain ⟨p, hp, K, hKn, hKi⟩ := hKS G H Q t hsplit htwo hlt
  have hHeven : Even (Nat.card ↥H) := hsplit.stronglyEmbedded.2.1
  have hHdvd : Nat.card ↥H ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H
  have hHpos : 0 < Nat.card ↥H := by
    have hne : Nat.card ↥H ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨⟨1, H.one_mem⟩⟩, inferInstance⟩
    omega
  have hHge2 : 2 ≤ Nat.card ↥H := by
    rcases hHeven with ⟨k, hk⟩
    omega
  have hIdx : 2 ≤ H.index := by
    have hne1 : H.index ≠ 1 := fun h => hsplit.stronglyEmbedded.1 (Subgroup.index_eq_one.mp h)
    have hne0 : H.index ≠ 0 := by
      intro h0
      have h := Subgroup.card_mul_index H
      rw [h0, mul_zero] at h
      exact (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩) h.symm
    omega
  have hGge4 : 4 ≤ Nat.card G := by
    have h1 : 4 ≤ Nat.card ↥H * H.index := by
      calc (4 : ℕ) = 2 * 2 := by norm_num
        _ ≤ Nat.card ↥H * H.index := Nat.mul_le_mul hHge2 hIdx
    rwa [Subgroup.card_mul_index H] at h1
  have hGeven : Even (Nat.card G) := by
    rcases hHeven with ⟨k, hk⟩
    rcases hHdvd with ⟨m, hm⟩
    exact ⟨k * m, by rw [hm, hk]; ring⟩
  intro hsimple
  haveI := hsimple
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ K hKn with hb | ht
  · exfalso
    have hpG : p = Nat.card G := by
      rw [hb, Subgroup.index_bot] at hKi
      exact hKi.symm ▸ rfl
    by_cases h2 : p = 2
    · omega
    · exact (Nat.not_even_iff_odd.mpr (hp.odd_of_ne_two h2)) (hpG ▸ hGeven)
  · exact hp.ne_one (by rw [ht, Subgroup.index_top] at hKi; exact hKi.symm)

/-! ## `not_caseA` from the classical closure statement

The workspace reduction of case a) has been carried out entirely in
`Submission/Work/ThmF/ChV12/L5crux*.lean` and `L5bridge.lean`: the case-a) hypothesis
`Q = Q0sub H` plus `X5 H t = ⊤` forces `V = centD H t = ⊥` as soon as the classical closure
statement `Work.ThmF.ChV12.SharpInvertingClosed` holds (Zassenhaus 1936: a finite near-field of
characteristic `2` is a field; equivalently Hering's theorem on transitive linear groups of odd
order).  Everything else in the chain is proved there, with no `FeitThompsonProp` anywhere.

The assembly is two lines, because in case a) `X5 H t = ⊤` (`notCaseA_X5_eq_top`, by simplicity)
and `V = ⊥` contradicts `PSU3Hyp.notZ` through `Work.PSU3.StageA.centD_ne_bot`. -/

/-- **`not_caseA` from the classical closure statement.** -/
theorem notCaseA_of_sharpInvertingClosed
    (hSIC : Work.ThmF.ChV12.SharpInvertingClosed)
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    {s : G} (hs : s ∈ Q) (hs2 : orderOf s = 2) (hst : t * s * t = s * t * s) :
    (Q : Set G) ≠ Work.ThmF.Q0sub H := by
  intro hQ
  have hQ' : Q = Work.ThmF.Q0sub H := Subgroup.ext (fun x => Set.ext_iff.mp hQ x)
  have hcrux : Work.ThmF.ChV12.L5cruxProp :=
    Work.ThmF.ChV12.L5cruxProp_of_sharpInvertingClosed hSIC
  rcases hcrux hC4 (notCaseA_hyp5 hS hs hs2 hst) hQ' with hX5 | hV
  · exact absurd (notCaseA_X5_eq_top hS hs hs2 hst hQ) hX5
  · exact Work.PSU3.StageA.centD_ne_bot hS hV

/-! ### The remaining case, in the form in which it must be attacked

Write `A := Q0sub H` (elementary abelian of order `2ⁿ`, `n ≥ 2`), `D := twoPoint H t` and
`V := centD H t`.  In case a) with `X5 H t = ⊤` (so `G` is simple) the following are all proved
(`Work.ThmF.ChV12.L5cruxAux`, `L5bridge`, and this file):

* `D = ⟨Kset H t⟩` and `D` acts **faithfully** on `A` (`X5_eq_top_imp_…_centralizer_eq_bot`);
* `|Kset H t| = |A| - 1 = 2ⁿ - 1` and `Kset H t` is **sharply transitive** on `A∖{1}`
  (`L5.Kset_regular`), with `t` inverting it elementwise and `D = ⟨Kset⟩`;
* `|D| = |V| · (2ⁿ - 1)` (`ThmF.card_centD_mul_card_Kset`), and every element of `Kset∖{1}` acts
  fixed-point-freely on `A` (uniqueness in sharp transitivity);
* `V = D ⊓ C_G(u₀)` for an involution `u₀ ∈ Inv H` (`ChIIFourProp` P2(a)), i.e. `V` is exactly the
  stabilizer `D_{u₀}` of the non-zero vector `u₀` — its order is `|D|/(2ⁿ-1)`.

Two routes close the case, and **neither is among the hypotheses of the request**:

0. The extra hypotheses `hr`, `hsr` of the request are in fact redundant: `Work.ThmF.ChV12.structureIdentity`
   (Ch. V §2 Lemma 1(b)) says the pair `(u, r)` with `u ∈ Q` an involution, `r ∈ Q` and
   `t * u * t = r⁻¹ * t * r` is *unique*; both `(s, s)` (by `hst`) and `(s, r⁻¹)` (by `hsr`) are
   such pairs, so `r = s`.  Hence `not_caseA` depends only on `Hyp5`-data plus `ChIIFourProp`.

1. **Odd order theorem.**  If `D` is solvable then `appX_of_solvable`
   (`Work.PSU3.StageA.appX_of_solvable`) gives `IsCyclic (fitting D)`, `fpf (fitting D)` and
   `D' ≤ fitting D`; moreover `D = ⟨Kset⟩` and `τ = t` inverts the generating set, so `t` inverts
   `D/D'` and hence `V ⊆ D' ≤ fitting D`; as `V ≤ D_{u₀}` and `fitting D ∖ {1}` acts
   fixed-point-freely, `V ≤ fitting D ⊓ D_{u₀} = 1`.  `D` has odd order, so `IsSolvable D` is
   exactly the odd order theorem `FeitThompsonProp`
   (`Work.PSU3.StageA.Ksub_eq_Kset_of_Hyp5_of_solvable` already packages this route).
2. **The classical closure statement** `Work.ThmF.ChV12.SharpInvertingClosed`: the `t`-inverted set
   is closed under multiplication, which needs Zassenhaus's classification of finite near-fields
   of characteristic `2` (equivalently Hering's theorem on transitive linear groups of odd order).
   A concrete plan for it, excluding the Zsigmondy-exception `n = 6`: for a primitive prime
   divisor `p` of `2ⁿ - 1` (Bang–Zsigmondy) any `g ∈ D` of order `p` has a minimal polynomial
   dividing `Φ_p`, all of whose irreducible factors have degree `n = dim A`, so `A` is irreducible
   over `F₂[⟨g⟩]` and `C_{GL(A)}(g) = F_{2ⁿ}^*` is a Singer cycle.

A further, purely internal observation (this session) that any future attack can use: since `t`
inverts the generating set `Kset` of `D`, `t` inverts `D/D'`, so `V ⊆ D'`, `D = D'·Kset`, and
`J := D' ⊓ Kset` is *closed under multiplication* — for `k₁, k₂ ∈ J` one has `k₁k₂ ∈ D'` and also
`k₁k₂ ∈ J·Kset ⊆ Kset` because `J·Kset = Kset` — hence `J` is a subgroup with `J ⊆ Kset`,
`D' = V·J` and `V ⊓ J = 1` (from `|D'| = |V|·|J|`).  So `D'` is an extension of the `t`-fixed
part `V` by the `t`-inverted subgroup `J ⊆ Kset`, and the whole question is to see that `V` — a
*point stabiliser* of the faithful transitive action of `D` on `A∖{1}` — is trivial. -/

-- Superseded (2026): `sharpInvertingClosed_holds : Work.ThmF.ChV12.SharpInvertingClosed` was a
-- `hole` and was removed by the hole sweep; the classical near-field statement is never proved
-- in this workspace.  `Work.PSU3.StageA.notCaseA_of_sharpInvertingClosed` above keeps the
-- reduction from that statement as a hypothesis.

-- Superseded (2026): the hole-carrying `not_caseA` was removed by the hole sweep; its proved
-- replacement is `Work.PSU3.StageA.not_caseA_of_FT` above.

end Work.PSU3.StageA
