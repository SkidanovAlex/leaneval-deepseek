import Mathlib
import Submission.Work.ThmF.ChV3.Chain15
import Submission.Work.ThmF.ChV12.corProp2
import Submission.Work.S3.cq_ell_subgroup_isCyclic
import Submission.Work.AppXIDickson.sylow_two_complement_card_odd
import Submission.Work.AppXIDickson.isCyclic_of_odd_nilpotent_ellCyclic
import Submission.Work.AppXIDickson.card_le_eight_of_unique_involution
import Submission.Work.AppXIDickson.exists_order_four_and_conj_inv
import Submission.Work.AppXIDickson.zpowers_mul_eq_sup_of_coprime

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.AppXIDickson

/-- **B2** (structure of a non-abelian `C_Q(P)`; Peterfalvi II Ch. V §3 step (5), source p. 249).
In the standing context `CtxF H Q t s r P` of §3, with a non-abelian `C_Q(P) = Q ⊓ C_G(P)`, there
are `x, y ∈ C_Q(P)` and a subgroup `C ≤ C_Q(P)` such that `x` has order `4`, `y` inverts `x`
(`y * x * y⁻¹ = x⁻¹`), `C` has odd order and is central in `C_Q(P)`,
`A := Subgroup.zpowers x ⊔ C` is cyclic of order `4 * Nat.card C`, and
`Nat.card C_Q(P) = 8 * Nat.card C` — i.e. (with `T` the Sylow 2-subgroup of `C_Q(P)`, `Q₈`-like)
`C_Q(P) = T × C`, `|T| = 8`, and `x, y` are the standard generators of `T`.

Route. (i) `Q` is nilpotent (`Work.ThmF.ChV12.prop1b`), hence so is `C_Q(P)` (subgroup), so its
Sylow subgroups are normal and `C_Q(P) = S₂ × C` with `S₂` the Sylow 2-subgroup and
`C = O_{2'}(C_Q(P))` (take `C` to be the `2'`-part, e.g. `sSup` of the odd Sylow subgroups, or the
closure of the odd-order elements of `C_Q(P)`); `C` is central
(`IsNilpotent.commute_of_orderOf_coprime`, `Mathlib/GroupTheory/Nilpotent.lean:1222`) and cyclic
(every odd `ℓ`-subgroup of `C_Q(P)` is cyclic by `Work.S3.cq_ell_subgroup_isCyclic`, and the Sylow
subgroups of a nilpotent group commute pairwise). (ii) `C_Q(P)` non-abelian forces `S₂` non-abelian
(`C` central), hence `S = O₂(Q) ⊇ S₂` non-abelian, hence `S` is a Suzuki 2-group
(`Work.ThmF.ChV12.corProp2`), and `HigmanProp` gives `x² ∈ Z(S)` for all `x ∈ S`, so `S₂` has
exponent dividing `4`. (iii) `HigmanProp` also gives `Z(S) = Ω₁(S)`, so every involution of `S` is
central in `S`; two distinct involutions of `S₂ ≤ S` would therefore commute and generate a
four-group inside `C_G(P)`, contradicting (F1) (`c.F1`) — so `S₂` has a *unique* involution `z`.
(iv) A 2-group of exponent dividing `4` with a unique involution has order `≤ 8`; elementary proof:
`⟨z⟩` is central, `W := S₂/⟨z⟩` is elementary abelian (every square lies in `⟨z⟩`), squaring
induces a quadratic form `q : W → ZMod 2` via `(xy)² = x²y²[y,x]` (all commutators lie in `⟨z⟩`)
which is `1` on every non-zero vector, while for a quadratic form
`q(x+y+z) = q x + q y + q z + b(x,y) + b(y,z) + b(x,z)` with `b` the polarization, so three
independent vectors of `W` give `1 = 0`.  Hence `|W| ≤ 4`, `|S₂| ≤ 8`, and `S₂` non-abelian gives
`|S₂| = 8`. (v) `S₂` of order `8` with a unique involution is `Q₈`: take `x ∈ S₂` of order `4` and
some `y ∈ S₂ \ ⟨x⟩`, which inverts `x` (in `Q₈`, `y x y⁻¹ = x⁻¹` for every `y ∉ ⟨x⟩`), and
`A := ⟨x⟩ ⊔ C`, `C` central of odd order, is cyclic of order `4 · Nat.card C` (coprime orders,
`⟨x⟩ ∩ C = 1`). -/
theorem cq_noncomm_structure {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hTh : Submission.Blueprint.ThompsonFrobeniusProp)
    (hNF : Work.ThmF.ChV3.NearFieldAppXIProp) (hHig : Submission.Blueprint.HigmanProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P)
    (hnc : ¬ IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P)) :
    ∃ (x y : G) (C : Subgroup G), x ∈ Work.ThmF.ChV3.CQ Q P ∧ y ∈ Work.ThmF.ChV3.CQ Q P ∧
      C ≤ Work.ThmF.ChV3.CQ Q P ∧ orderOf x = 4 ∧
      y * x * y⁻¹ = x⁻¹ ∧ Odd (Nat.card C) ∧
      (∀ z ∈ C, ∀ g ∈ Work.ThmF.ChV3.CQ Q P, z * g = g * z) ∧
      IsCyclic ↥(Subgroup.zpowers x ⊔ C) ∧
      Nat.card ↥(Subgroup.zpowers x ⊔ C) = 4 * Nat.card C ∧
      Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = 8 * Nat.card C := by
  classical
  -- ## `Q` and `M = C_Q(P)` are nilpotent
  have hnilQ : Group.IsNilpotent ↥Q :=
    Work.ThmF.ChV12.prop1b c.sit hC4 hTh H Q t c.split (Work.ThmF.ChV3.CtxF.Kset_nontrivial c)
  haveI hnilQ' : Group.IsNilpotent ↥Q := hnilQ
  have hMQ : Work.ThmF.ChV3.CQ Q P ≤ Q := inf_le_left
  haveI hnilM : Group.IsNilpotent ↥(Work.ThmF.ChV3.CQ Q P) :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hMQ)).mp
      (Subgroup.isNilpotent ((Work.ThmF.ChV3.CQ Q P).subgroupOf Q))
  -- ## the Sylow `2`-subgroup `S` of `Q`: it is abelian or a Suzuki 2-group
  obtain ⟨S, hSQ, hSp, hSidx, hSinv⟩ := Work.ThmF.ChV12.sylowTwo_exists_invariant Q hnilQ
  obtain ⟨hKcyc, hKset, -⟩ := Work.ThmF.ChV12.Ksub_cyclic_normal hFT hC4 c.sit c.split
  have hStab : ∀ k ∈ Work.ThmF.Ksub H t, ∀ x ∈ S, k * x * k⁻¹ ∈ S := by
    intro k hk x hx
    have hkH : k ∈ H := (Subgroup.mem_inf.mp (Work.ThmF.Ksub_le_twoPoint (H := H) t hk)).1
    exact hSinv k (c.split.normal hkH) x hx
  have hKtrans : ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G),
      ∃ k ∈ Work.ThmF.Kset H t, k * a * k⁻¹ = b := by
    intro a ha b hb
    obtain ⟨k, hk, -⟩ := Work.ThmF.L5.Kset_regular c.split a ha b hb
    exact ⟨k, hk.1, hk.2⟩
  have hSdich : Submission.Blueprint.IsAbelianSubgroup S ∨ IsSuzukiTwoGroup ↥S := by
    by_cases hab : Submission.Blueprint.IsAbelianSubgroup S
    · exact Or.inl hab
    · refine Or.inr (Work.ThmF.ChV12.isSuzukiTwoGroup_of_Ksub_cyclic H t S (hSQ.trans c.split.le)
        hSp hStab ?_ hab hKcyc hKset hKtrans)
      rw [Work.ThmF.ChV12.involutions_S_eq_involutions_H H Q t c.split S hSQ hSp hSidx hStab
        hKset hKtrans]
      exact Work.ThmF.Bender.cardInvGeTwo c.split.stronglyEmbedded c.sit.1.1
  -- ## a Sylow `2`-subgroup `T'` of `M` and its odd complement `C'` (Schur–Zassenhaus)
  obtain ⟨T'⟩ := Sylow.nonempty (p := 2) (G := ↥(Work.ThmF.ChV3.CQ Q P))
  obtain ⟨C', hcompl, hC'odd, hcardM⟩ := sylow_two_complement_card_odd hnilM T'
  have hcycC' : IsCyclic ↥C' := by
    refine isCyclic_of_odd_nilpotent_ellCyclic hnilM hC'odd ?_
    intro ℓ hℓ hℓ2 B hB
    have hBmap : IsPGroup ℓ ↥(B.map (Work.ThmF.ChV3.CQ Q P).subtype) := hB.map _
    have hBle : B.map (Work.ThmF.ChV3.CQ Q P).subtype ≤ Work.ThmF.ChV3.CQ Q P :=
      Subgroup.map_subtype_le B
    have hres := Work.S3.cq_ell_subgroup_isCyclic hNF c hℓ hℓ2 hBle hBmap
    exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective B (Work.ThmF.ChV3.CQ Q P).subtype
      (Subgroup.subtype_injective _))).mpr hres
  -- ## `T = T'` and `C = C'` as subgroups of `G`
  set T : Subgroup G := (T' : Subgroup ↥(Work.ThmF.ChV3.CQ Q P)).map
    (Work.ThmF.ChV3.CQ Q P).subtype with hTdef
  set C : Subgroup G := C'.map (Work.ThmF.ChV3.CQ Q P).subtype with hCdef
  have hTM : T ≤ Work.ThmF.ChV3.CQ Q P := Subgroup.map_subtype_le _
  have hTQ : T ≤ Q := hTM.trans hMQ
  have hTpg : IsPGroup 2 ↥T := T'.isPGroup'.map _
  have hmemT : ∀ a : ↥T', ((a : ↥(Work.ThmF.ChV3.CQ Q P)) : G) ∈ T := by
    intro a
    rw [hTdef]
    exact Subgroup.mem_map.mpr ⟨(a : ↥(Work.ThmF.ChV3.CQ Q P)), a.2, rfl⟩
  have hcardT : Nat.card ↥T = Nat.card ↥T' :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hcardC : Nat.card ↥C = Nat.card ↥C' :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  -- ## `T ≤ S` (`Q` is nilpotent, so it has a unique Sylow `2`-subgroup)
  have hTS : T ≤ S := by
    have hT'' : IsPGroup 2 ↥(T.subgroupOf Q) :=
      IsPGroup.of_equiv hTpg (Subgroup.subgroupOfEquivOfLe hTQ).symm
    obtain ⟨P₂, hP₂⟩ := IsPGroup.exists_le_sylow (p := 2) (G := ↥Q) (P := T.subgroupOf Q) hT''
    have hS'' : IsPGroup 2 ↥(S.subgroupOf Q) :=
      IsPGroup.of_equiv hSp (Subgroup.subgroupOfEquivOfLe hSQ).symm
    let h3 : Sylow 2 ↥Q := IsPGroup.toSylow hS'' hSidx
    haveI : Unique (Sylow 2 ↥Q) :=
      Sylow.unique_of_normal h3 (Sylow.normal_of_normalizerCondition
        (Group.normalizerCondition_of_isNilpotent) h3)
    have hP₂eq : P₂ = h3 := Subsingleton.elim _ _
    intro x hx
    have hxQ : x ∈ Q := hTQ hx
    have h1 : (⟨x, hxQ⟩ : ↥Q) ∈ T.subgroupOf Q := Subgroup.mem_subgroupOf.mpr hx
    have h2 : (⟨x, hxQ⟩ : ↥Q) ∈ (S.subgroupOf Q) := by
      have h4 : (⟨x, hxQ⟩ : ↥Q) ∈ (P₂ : Subgroup ↥Q) := hP₂ h1
      rw [hP₂eq] at h4
      exact h4
    exact Subgroup.mem_subgroupOf.mp h2
  -- ## `M` is abelian as soon as `T'` is (so `S` and `T'` are non-abelian here)
  have hmemS : ∀ a : ↥T', ((a : ↥(Work.ThmF.ChV3.CQ Q P)) : G) ∈ S := fun a => hTS (hmemT a)
  have h2pow : ∀ u : ↥T', ∃ k : ℕ, orderOf (u : ↥(Work.ThmF.ChV3.CQ Q P)) = 2 ^ k := by
    intro u
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp T'.isPGroup' u
    exact ⟨k, by rw [Subgroup.orderOf_coe, hk]⟩
  have hoddC' : ∀ v : ↥C', Odd (orderOf (v : ↥(Work.ThmF.ChV3.CQ Q P))) := by
    intro v
    have h1 : orderOf (v : ↥(Work.ThmF.ChV3.CQ Q P)) = orderOf v := Subgroup.orderOf_coe v
    rw [h1]
    exact hC'odd.of_dvd_nat (orderOf_dvd_natCard v)
  have hT'ab_of_Sab (hSab : Submission.Blueprint.IsAbelianSubgroup S) : IsMulCommutative ↥T' := by
    refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    have h := hSab (((a : ↥(Work.ThmF.ChV3.CQ Q P)) : G)) (hmemS a)
      (((b : ↥(Work.ThmF.ChV3.CQ Q P)) : G)) (hmemS b)
    simpa using h
  have hMab_of_Tab (hT'ab : IsMulCommutative ↥T') :
      IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P) := by
    have hC'ab : IsMulCommutative ↥C' := hcycC'.isMulCommutative
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨⟨ta, ca⟩, ha, -⟩ := hcompl.existsUnique a
    obtain ⟨⟨tb, cb⟩, hb, -⟩ := hcompl.existsUnique b
    have h1 : Commute (ta : ↥(Work.ThmF.ChV3.CQ Q P)) (tb : ↥(Work.ThmF.ChV3.CQ Q P)) := by
      rw [commute_iff_eq]
      simpa using congrArg (fun z : ↥T' => (z : ↥(Work.ThmF.ChV3.CQ Q P)))
        (hT'ab.is_comm.comm ta tb)
    have h2 : Commute (ca : ↥(Work.ThmF.ChV3.CQ Q P)) (cb : ↥(Work.ThmF.ChV3.CQ Q P)) := by
      rw [commute_iff_eq]
      simpa using congrArg (fun z : ↥C' => (z : ↥(Work.ThmF.ChV3.CQ Q P)))
        (hC'ab.is_comm.comm ca cb)
    have h3 : Commute (ta : ↥(Work.ThmF.ChV3.CQ Q P)) (cb : ↥(Work.ThmF.ChV3.CQ Q P)) := by
      obtain ⟨k, hk⟩ := h2pow ta
      refine Group.IsNilpotent.commute_of_orderOf_coprime ?_
      rw [hk]
      exact Nat.Coprime.pow_left k ((Nat.coprime_two_left).mpr (hoddC' cb))
    have h4 : Commute (ca : ↥(Work.ThmF.ChV3.CQ Q P)) (tb : ↥(Work.ThmF.ChV3.CQ Q P)) := by
      obtain ⟨k, hk⟩ := h2pow tb
      refine Group.IsNilpotent.commute_of_orderOf_coprime ?_
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_two_right).mpr (hoddC' ca))
    rw [← ha, ← hb]
    exact (Commute.mul_left (h1.mul_right h3) (h4.mul_right h2)).eq
  have hSnab : ¬ Submission.Blueprint.IsAbelianSubgroup S :=
    fun hSab => hnc (hMab_of_Tab (hT'ab_of_Sab hSab))
  have hSuz : IsSuzukiTwoGroup ↥S := hSdich.resolve_left hSnab
  -- ## Higman's list applied to the Suzuki group `S`
  have hS4 : ∀ x ∈ S, x ^ 4 = 1 := by
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥S) ^ 2 ∈ Subgroup.center ↥S :=
      Work.ThmF.ChV12.sq_mem_center hHig hSuz ⟨x, hx⟩
    have h2 : ((⟨x, hx⟩ : ↥S) ^ 2) ^ 2 = 1 :=
      Work.ThmF.ChV12.center_sq_eq_one hHig hSuz _ h1
    have h3 : ((⟨x, hx⟩ : ↥S)) ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
      exact h2
    simpa using congrArg (fun z : ↥S => (z : G)) h3
  have hScent : ∀ u ∈ S, orderOf u = 2 → ∀ v ∈ S, u * v = v * u := by
    intro u hu hu2 v hv
    have hZu : (⟨u, hu⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rw [(hHig ↥S hSuz).1]
      apply Subtype.ext
      have h2 : (u : G) ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one u
      simpa using h2
    exact congrArg (fun z : ↥S => (z : G)) (Subgroup.mem_center_iff.mp hZu ⟨v, hv⟩).symm
  -- ## `T'` has a unique involution and exponent dividing `4`, hence `|T'| = 8`
  have hT'nab : ¬ IsMulCommutative ↥T' := fun hab => hnc (hMab_of_Tab hab)
  have hT'pow : ∀ x : ↥T', x ^ 4 = 1 := by
    intro x
    have h1 : (((x : ↥(Work.ThmF.ChV3.CQ Q P)) : G)) ^ 4 = 1 := hS4 _ (hmemS x)
    apply Subtype.ext
    apply Subtype.ext
    simpa using h1
  have huniq : ∀ x y : ↥T', orderOf x = 2 → orderOf y = 2 → x = y := by
    intro x y hx hy
    by_contra hne
    have hxM : orderOf (x : ↥(Work.ThmF.ChV3.CQ Q P)) = 2 := by
      rw [Subgroup.orderOf_coe]; exact hx
    have hyM : orderOf (y : ↥(Work.ThmF.ChV3.CQ Q P)) = 2 := by
      rw [Subgroup.orderOf_coe]; exact hy
    have hx2 : orderOf (((x : ↥(Work.ThmF.ChV3.CQ Q P)) : G)) = 2 := by
      rw [Subgroup.orderOf_coe]; exact hxM
    have hy2 : orderOf (((y : ↥(Work.ThmF.ChV3.CQ Q P)) : G)) = 2 := by
      rw [Subgroup.orderOf_coe]; exact hyM
    have hcomm := hScent _ (hmemS x) hx2 _ (hmemS y)
    have hxP : (((x : ↥(Work.ThmF.ChV3.CQ Q P)) : G)) ∈ Subgroup.centralizer (P : Set G) :=
      (show Work.ThmF.ChV3.CQ Q P ≤ Subgroup.centralizer (P : Set G) from inf_le_right)
        (hTM (hmemT x))
    have hyP : (((y : ↥(Work.ThmF.ChV3.CQ Q P)) : G)) ∈ Subgroup.centralizer (P : Set G) :=
      (show Work.ThmF.ChV3.CQ Q P ≤ Subgroup.centralizer (P : Set G) from inf_le_right)
        (hTM (hmemT y))
    refine c.F1 ⟨⟨_, hxP⟩, ⟨_, hyP⟩, ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.orderOf_mk]; exact hx2
    · rw [Subgroup.orderOf_mk]; exact hy2
    · intro hcon
      have hxy : (((x : ↥(Work.ThmF.ChV3.CQ Q P)) : G))
          = (((y : ↥(Work.ThmF.ChV3.CQ Q P)) : G)) :=
        congrArg (fun w : ↥(Subgroup.centralizer (P : Set G)) => (w : G)) hcon
      exact hne (Subtype.ext (Subtype.ext hxy))
    · simpa using hcomm
  have hcardT'eq : Nat.card ↥T' = 8 := by
    have hle := card_le_eight_of_unique_involution T'.isPGroup' hT'pow huniq
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp T'.isPGroup'
    have hk' : Nat.card ↥T' = 2 ^ k := hk
    have hk3 : k ≤ 3 := by
      have h2k : 2 ^ k ≤ 8 := by rw [← hk']; exact hle
      have h' : 2 ^ k ≤ 2 ^ 3 := by norm_num at h2k ⊢; exact h2k
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h'
    interval_cases k
    case «0» =>
      refine absurd ?_ hT'nab
      have h1 : Nat.card ↥T' ≤ 1 := by simp [hk']
      have hs : Subsingleton ↥T' := Finite.card_le_one_iff_subsingleton.mp h1
      exact IsMulCommutative.of_comm (fun a b => @Subsingleton.elim _ hs (a * b) (b * a))
    case «1» =>
      have h1 : Nat.card ↥T' = 2 := by simpa using hk'
      exact absurd (isCyclic_of_prime_card (p := 2) h1).isMulCommutative hT'nab
    case «2» =>
      have h1 : Nat.card ↥T' = 2 ^ 2 := by simpa using hk'
      exact absurd (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) h1) hT'nab
    case «3» => simpa using hk'
  -- ## the elements `x`, `y`
  obtain ⟨xₕ, yₕ, hxₕord, hxₕinv⟩ :=
    exists_order_four_and_conj_inv hcardT'eq hT'nab huniq
  set x : G := ((xₕ : ↥(Work.ThmF.ChV3.CQ Q P)) : G) with hxdef
  set y : G := ((yₕ : ↥(Work.ThmF.ChV3.CQ Q P)) : G) with hydef
  have hxM : x ∈ Work.ThmF.ChV3.CQ Q P := hTM (hmemT xₕ)
  have hyM : y ∈ Work.ThmF.ChV3.CQ Q P := hTM (hmemT yₕ)
  have hxord : orderOf x = 4 := by
    rw [hxdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hxₕord
  have hyinv : y * x * y⁻¹ = x⁻¹ := by
    have h1 := congrArg (fun w : ↥T' => ((w : ↥(Work.ThmF.ChV3.CQ Q P)) : G)) hxₕinv
    simpa [hxdef, hydef] using h1
  -- ## `C` is central in `M`
  have hCcentral' : ∀ z : ↥(Work.ThmF.ChV3.CQ Q P), z ∈ C' →
      ∀ g : ↥(Work.ThmF.ChV3.CQ Q P), z * g = g * z := by
    intro z hz g
    obtain ⟨⟨t, c⟩, hg, -⟩ := hcompl.existsUnique g
    have hC'ab : IsMulCommutative ↥C' := hcycC'.isMulCommutative
    have h1 : Commute z (c : ↥(Work.ThmF.ChV3.CQ Q P)) := by
      rw [commute_iff_eq]
      simpa using congrArg (fun w : ↥C' => (w : ↥(Work.ThmF.ChV3.CQ Q P)))
        (hC'ab.is_comm.comm ⟨z, hz⟩ c)
    have h2 : Commute z (t : ↥(Work.ThmF.ChV3.CQ Q P)) := by
      obtain ⟨k, hk⟩ := h2pow t
      have hzdvd : orderOf z ∣ Nat.card ↥C' := by
        rw [← Subgroup.orderOf_mk z hz]
        exact orderOf_dvd_natCard _
      have hzodd : Odd (orderOf z) := hC'odd.of_dvd_nat hzdvd
      refine Group.IsNilpotent.commute_of_orderOf_coprime ?_
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_two_right).mpr hzodd)
    rw [← hg]
    exact (h2.mul_right h1).eq
  have hCcentral : ∀ z ∈ C, ∀ g ∈ Work.ThmF.ChV3.CQ Q P, z * g = g * z := by
    intro z hz g hg
    have hz' := hz
    rw [hCdef] at hz'
    obtain ⟨zh, hzh, hzheq⟩ := Subgroup.mem_map.mp hz'
    have hcomm := hCcentral' zh hzh ⟨g, hg⟩
    have h2 := congrArg (fun w : ↥(Work.ThmF.ChV3.CQ Q P) => (w : G)) hcomm
    rw [← hzheq]
    exact h2
  -- ## `C = ⟨c₀⟩` is cyclic, and `⟨x⟩ ⊔ C = ⟨x · c₀⟩`
  have hcycC : IsCyclic ↥C := by
    rw [hCdef]
    exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective C' (Work.ThmF.ChV3.CQ Q P).subtype
      (Subgroup.subtype_injective _))).mp hcycC'
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := ↥C)
  set c₀ : G := (g₀ : G) with hc₀def
  have hCeq : C = Subgroup.zpowers c₀ := by
    refine le_antisymm ?_ ?_
    · intro z hz
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ ⟨z, hz⟩)
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      have h1 := congrArg (fun w : ↥C => (w : G)) hn
      simpa [hc₀def] using h1
    · exact Subgroup.zpowers_le.mpr (by rw [hc₀def]; exact g₀.2)
  have hordc₀ : orderOf c₀ = Nat.card ↥C := by
    rw [← Nat.card_zpowers c₀, ← hCeq]
  have hcommxc : Commute x c₀ := by
    rw [commute_iff_eq]
    exact (hCcentral c₀ (hCeq ▸ Subgroup.mem_zpowers c₀) x hxM).symm
  have hCodd : Odd (Nat.card ↥C) := by rw [hcardC]; exact hC'odd
  have hcop4 : (orderOf x).Coprime (orderOf c₀) := by
    rw [hxord, hordc₀]
    simpa using Nat.Coprime.pow_left 2 ((Nat.coprime_two_left).mpr hCodd)
  have hsup : Subgroup.zpowers x ⊔ C = Subgroup.zpowers (x * c₀) := by
    rw [hCeq]
    exact zpowers_mul_eq_sup_of_coprime hcommxc hcop4
  -- ## conclusion
  refine ⟨x, y, C, hxM, hyM, ?_, hxord, hyinv, hCodd, hCcentral, ?_, ?_, ?_⟩
  · rw [hCdef]; exact Subgroup.map_subtype_le C'
  · rw [hsup]; infer_instance
  · rw [hsup, Nat.card_zpowers, Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcommxc hcop4,
      hxord, hordc₀]
  · rw [hcardM, hcardT'eq, hcardC]

end Work.AppXIDickson
