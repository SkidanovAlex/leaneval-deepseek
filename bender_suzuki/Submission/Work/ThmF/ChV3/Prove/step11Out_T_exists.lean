import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.centDLowerCentralizerS
import Submission.Work.ThmF.Bender.twoInvolutionsOdd
import Submission.Work.PGroup.card_sup_mul_card_inf_of_le_normalizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.step11Out_T_exists`

The subgroup `T` of Peterfalvi II, Ch. V §3, step (11), in the "repaired" form the project uses:
given that `R` is abelian (`hcomm`) and of exponent `|P|` (`hexp`), and that the distinguished
involution `s` is centralised by `C_Q(P)` and by `Σ = C_W(P)`, there is a complement `T` of `P`
in `R` on which `s` acts by inversion, which is normalised by `C_Q(P) · Σ`, and whose order is
`|P| ^ m`.

## The mathematics

Put `T = {a ∈ R : s a s⁻¹ = a⁻¹}`.  Since `R` is abelian, `T` is a **subgroup** of `R`, and since
`s` normalises `R` (it lies in `C_G(P) ≤ N_G(R)`) and `s` is an involution, conjugation by `s`
is an involutive automorphism `σ` of `R` with `T = {a : σ a = a⁻¹}`.

* The fixed subgroup `C_R(s)` equals `P`: for `x ∈ C_R(s)`, the commutator `[x,s] = 1 ∈ P`, and the
  regularity clause `h15.hfpf` (with `Ker = P` by `h7`) at `y = s ∈ C_Q(P)` forces `x ∈ P`.
* `R` has odd order (`|R| = |P| ^ (m+1)` with `|P|` odd), so `C_R(s) ⊓ T = 1`; with
  `C_R(s) = P` and `R = C_R(s)·T` (the `σ`-eigenspace decomposition of `R`), we get
  `T ⊓ P = ⊥` and `T ⊔ P = R`, and the `σ`-decomposition of `x ∈ R` reads `x = (x σ x)^k (x σ x⁻¹)^k`
  with `2k = |R| + 1`, giving the unique factorisation clause.
* `C_Q(P)` and `Σ` lie in `C_G(P) ≤ N_G(R)` and centralise `s`, so they normalise `T`.
* `|T| = |R| / |P| = |P| ^ m`.

Nothing here uses `hexp`; the hypothesis is kept because the statement is the caller's.
-/

set_option linter.style.haveILetI false

namespace Work.ThmF.ChV3.Prove

/-- **Core group-theoretic lemma.**  Let `s` be an involution normalising an abelian subgroup `R`
of odd order, and let `P ≤ R` be an `s`-invariant subgroup with `C_R(s) ≤ P`.  Then
`T = {a ∈ R : s a s⁻¹ = a⁻¹}` is a complement of `P` in `R`, its elements are the unique
`P × T`-components of elements of `R`, and `|T| · |P| = |R|`. -/
private theorem step11Out_core {G : Type} [Group G] [Finite G] {R P : Subgroup G} {s : G}
    (hcomm : IsMulCommutative ↥R) (hs2 : s * s = 1)
    (hsNR : s ∈ Subgroup.normalizer (R : Set G))
    (hPR : P ≤ R)
    (hPs : ∀ p ∈ P, s * p * s⁻¹ = p)
    (hCRs : ∀ x ∈ R, s * x * s⁻¹ = x → x ∈ P)
    (hPodd : Odd (Nat.card P)) (hRodd : Odd (Nat.card R)) :
    ∃ T : Subgroup G, T ≤ R ∧ T ⊓ P = ⊥ ∧ T ⊔ P = R ∧
      (∀ a ∈ R, a ∈ T ↔ s * a * s⁻¹ = a⁻¹) ∧
      (∀ x ∈ R, ∃ p0 ∈ P, ∃ w ∈ T, x = p0 * w ∧ (x ∉ T → p0 ≠ 1) ∧ (x ∉ P → w ≠ 1)) ∧
      Nat.card ↥T * Nat.card ↥P = Nat.card ↥R := by
  classical
  have mulR : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb => by
    haveI := hcomm
    exact congrArg Subtype.val (mul_comm' (⟨a,ha⟩:↥R) (⟨b,hb⟩:↥R))
  let T : Subgroup G :=
    { carrier := {a : G | a ∈ R ∧ s * a * s⁻¹ = a⁻¹}
      mul_mem' := by
        intro a b ha hb
        obtain ⟨haR, haI⟩ := ha
        obtain ⟨hbR, hbI⟩ := hb
        refine ⟨R.mul_mem haR hbR, ?_⟩
        rw [mul_inv_rev]
        calc s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
          _ = a⁻¹ * b⁻¹ := by rw [haI, hbI]
          _ = b⁻¹ * a⁻¹ := mulR a⁻¹ (R.inv_mem haR) b⁻¹ (R.inv_mem hbR)
      one_mem' := by
        refine ⟨R.one_mem, ?_⟩
        simp
      inv_mem' := by
        intro a ha
        obtain ⟨haR, haI⟩ := ha
        refine ⟨R.inv_mem haR, ?_⟩
        rw [show s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ by group, haI, inv_inv] }
  have hTmem : ∀ a, a ∈ T ↔ a ∈ R ∧ s * a * s⁻¹ = a⁻¹ := fun a => Iff.rfl
  have hTR : T ≤ R := fun a ha => ((hTmem a).mp ha).1
  have hsn : ∀ x ∈ R, s * x * s⁻¹ ∈ R := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hsNR x).mp hx
  have hsinv' : s⁻¹ * s⁻¹ = 1 := by rw [← mul_inv_rev, hs2, inv_one]
  -- ## the `P × T` decomposition of `R`
  have hdec : ∀ x ∈ R, ∃ p0 ∈ P, ∃ w ∈ T, x = p0 * w ∧ (x ∉ T → p0 ≠ 1) ∧
      (x ∉ P → w ≠ 1) := by
    intro x hx
    set W : G := s * x * s⁻¹ with hW
    have hWR : W ∈ R := hsn x hx
    have hsw : s * W * s⁻¹ = x := by
      rw [hW]
      rw [show s * (s * x * s⁻¹) * s⁻¹ = (s * s) * x * (s⁻¹ * s⁻¹) by group, hs2, hsinv']
      group
    have hzR : x * W⁻¹ ∈ R := R.mul_mem hx (R.inv_mem hWR)
    have hzT : x * W⁻¹ ∈ T := by
      rw [hTmem]
      refine ⟨hzR, ?_⟩
      calc s * (x * W⁻¹) * s⁻¹ = W * (s * W * s⁻¹)⁻¹ := by rw [hW]; group
        _ = W * x⁻¹ := by rw [hsw]
        _ = (x * W⁻¹)⁻¹ := by group
    have huR : x * W ∈ R := R.mul_mem hx hWR
    have huC : s * (x * W) * s⁻¹ = x * W := by
      calc s * (x * W) * s⁻¹ = (s * x * s⁻¹) * (s * W * s⁻¹) := by group
        _ = W * x := by rw [show s * x * s⁻¹ = W from hW.symm, hsw]
        _ = x * W := mulR W hWR x hx
    have huP : x * W ∈ P := hCRs _ huR huC
    have hxW : x * W = W * x := mulR x hx W hWR
    have hWxx : W * (x * x) = (x * x) * W := mulR W hWR (x * x) (R.mul_mem hx hx)
    have huz : (x * W) * (x * W⁻¹) = x * x := by
      rw [hxW]
      rw [show (W * x) * (x * W⁻¹) = W * (x * x) * W⁻¹ by group]
      rw [hWxx]
      group
    have hxpow : x ^ Nat.card R = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard R hx)
    obtain ⟨j, hj⟩ := hRodd
    set k : ℕ := (Nat.card R + 1) / 2 with hkdef
    have h2k : 2 * k = Nat.card R + 1 := by rw [hkdef]; omega
    have hc : Commute (x * W) (x * W⁻¹) := mulR (x * W) huR (x * W⁻¹) hzR
    have hxeq : x = (x * W) ^ k * (x * W⁻¹) ^ k := by
      rw [← hc.mul_pow k, huz, ← pow_two, ← pow_mul, h2k, pow_succ, hxpow, one_mul]
    exact ⟨(x * W) ^ k, P.pow_mem huP k, (x * W⁻¹) ^ k, T.pow_mem hzT k, hxeq,
      fun hxT hp0 => hxT (show x ∈ T from by rw [hxeq, hp0, one_mul]; exact T.pow_mem hzT k),
      fun hxP hw => hxP (show x ∈ P from by rw [hxeq, hw, mul_one]; exact P.pow_mem huP k)⟩
  have hR_le_sup : R ≤ T ⊔ P := by
    intro x hx
    obtain ⟨p0, hp0P, w, hwT, hxeq, -, -⟩ := hdec x hx
    rw [hxeq]
    exact (T ⊔ P).mul_mem (Subgroup.mem_sup_right hp0P) (Subgroup.mem_sup_left hwT)
  have hsup : T ⊔ P = R := le_antisymm (sup_le hTR hPR) hR_le_sup
  -- ## `T ⊓ P = ⊥` (both sides are `s`-fixed, resp. `s`-inverted, and `P` has odd order)
  have hTP : T ⊓ P = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    obtain ⟨haT, haP⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨_, haI⟩ := (hTmem a).mp haT
    have hafix : s * a * s⁻¹ = a := hPs a haP
    rw [hafix] at haI
    have hsq : a * a = 1 := eq_inv_iff_mul_eq_one.mp haI
    have hdvd2 : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hsq)
    have hdvdP : orderOf a ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P haP
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      rw [h] at hdvdP
      obtain ⟨j, hj⟩ := hPodd
      obtain ⟨c, hc⟩ := hdvdP
      omega
  have hP_le_NGT : P ≤ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro p hp a ha
    have hpa : p * a = a * p := mulR p (hPR hp) a (hTR ha)
    rw [show p * a * p⁻¹ = a by rw [hpa]; group]
    exact ha
  have hcard : Nat.card ↥T * Nat.card ↥P = Nat.card ↥R := by
    have h := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer (H := T) (K := P) hP_le_NGT
    rw [hsup, hTP, Subgroup.card_bot, mul_one] at h
    exact h.symm
  exact ⟨T, hTR, hTP, hsup, fun a ha => (hTmem a).trans (and_iff_right ha), hdec, hcard⟩

theorem step11Out_T_exists {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P)
    (hpf : Nat.card P = orderOf (s * t)) (hcomm : IsMulCommutative ↥h15.R)
    (hexp : ∀ x ∈ h15.R, x ^ Nat.card P = 1)
    (hsC : ∀ y ∈ Work.ThmF.ChV3.CQ Q P, y * s * y⁻¹ = s)
    (hsS : ∀ y ∈ Work.ThmF.ChV3.Sig H t P, y * s * y⁻¹ = s) :
    ∃ T : Subgroup G,
      T ≤ h15.R ∧ T ⊓ P = ⊥ ∧ T ⊔ P = h15.R ∧
      Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P ≤ Subgroup.normalizer (T : Set G) ∧
      (∀ a ∈ h15.R, (a ∈ T ↔ s * a * s⁻¹ = a⁻¹)) ∧
      (∀ x ∈ h15.R, ∃ p0 ∈ P, ∃ w ∈ T, x = p0 * w ∧ (x ∉ T → p0 ≠ 1) ∧ (x ∉ P → w ≠ 1)) ∧
      Nat.card ↥T = Nat.card P ^ h15.m := by
  classical
  have hs_ne : s ≠ 1 := by
    intro h1
    have h2 : (2 : ℕ) = 1 := by rw [← c.s_inv, orderOf_eq_one_iff.mpr h1]
    exact absurd h2 (by norm_num)
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [c.s_inv, pow_two] at h
    exact h
  -- `|P|` is odd
  have hodd : Odd (orderOf (s * t)) :=
    Work.ThmF.Bender.twoInvolutionsOdd c.split.stronglyEmbedded (c.split.le c.s_mem) c.s_inv
      c.split.invol c.split.not_mem
  have hPodd : Odd (Nat.card P) := by rw [hpf]; exact hodd
  -- `P ≤ C_G(s)` (Ch. V §2 Lemma 3 a), hence `s ∈ C_Q(P)` and `s ∈ N_G(R)`
  have hPcs : P ≤ Subgroup.centralizer ({s} : Set G) :=
    c.P_le.trans (Work.ThmF.Prove.centDLowerCentralizerS c.split c.s_mem c.s_inv c.r_mem c.sid)
  have hPs : ∀ p ∈ P, s * p * s⁻¹ = p := by
    intro p hp
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hPcs hp)
    rw [h.symm]; group
  have hsCGP : s ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact Subgroup.mem_centralizer_singleton_iff.mp (hPcs hp)
  have hsCQ : s ∈ Work.ThmF.ChV3.CQ Q P := ⟨c.s_mem, hsCGP⟩
  have hsNR : s ∈ Subgroup.normalizer (h15.R : Set G) := h15.hRn hsCGP
  have hPR : P ≤ h15.R := by simpa [h7] using h15.hNR
  -- `C_R(s) ≤ P` (regularity of `C_Q(P)` on `R`, with `Ker = P`)
  have hCRs : ∀ x ∈ h15.R, s * x * s⁻¹ = x → x ∈ P := by
    intro x hxR hfix
    by_contra hxP
    have hmem : s * x * s⁻¹ * x⁻¹ ∈ Work.ThmF.ChV3.Ker H Q P t := by
      rw [h7, hfix, mul_inv_cancel]
      exact P.one_mem
    exact hs_ne (h15.hfpf x hxR (by rw [h7]; exact hxP) s hsCQ hmem)
  -- `|R| = |P| ^ (m+1)` is odd
  have hRcard : Nat.card ↥h15.R = Nat.card P ^ (h15.m + 1) := by
    have h := h15.hcardR
    rw [h7, ← hpf] at h
    rw [← pow_succ'] at h
    exact h
  have hRodd : Odd (Nat.card ↥h15.R) := by rw [hRcard]; exact Odd.pow hPodd
  obtain ⟨T, hTR, hTP, hsup, hiff, hdec, hcard⟩ :=
    step11Out_core hcomm hs2 hsNR hPR hPs hCRs hPodd hRodd
  -- `C_Q(P)` and `Σ` centralise `s` and normalise `R`, hence normalise `T`
  have hnorm_mem : ∀ y : G, y ∈ Subgroup.normalizer (h15.R : Set G) → y * s * y⁻¹ = s →
      ∀ a ∈ T, y * a * y⁻¹ ∈ T := by
    intro y hyNR hys a ha
    have hmem : y * a * y⁻¹ ∈ h15.R :=
      (Subgroup.mem_normalizer_iff.mp hyNR a).mp (hTR ha)
    rw [hiff (y * a * y⁻¹) hmem]
    have haI : s * a * s⁻¹ = a⁻¹ := (hiff a (hTR ha)).mp ha
    have hys' : y * s = s * y := by
      calc y * s = y * s * y⁻¹ * y := by group
        _ = s * y := by rw [hys]
    have hysi : s⁻¹ * y⁻¹ = y⁻¹ * s⁻¹ := by
      have h := congrArg Inv.inv hys'
      simpa [mul_inv_rev] using h
    calc s * (y * a * y⁻¹) * s⁻¹
        = (s * y) * a * (y⁻¹ * s⁻¹) := by group
      _ = (y * s) * a * (s⁻¹ * y⁻¹) := by rw [hys', hysi]
      _ = y * (s * a * s⁻¹) * y⁻¹ := by group
      _ = y * a⁻¹ * y⁻¹ := by rw [haI]
      _ = (y * a * y⁻¹)⁻¹ := by group
  have hCQ_le : Work.ThmF.ChV3.CQ Q P ≤ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy a ha
    exact hnorm_mem y (h15.hRn hy.2) (hsC y hy) a ha
  have hSig_le : Work.ThmF.ChV3.Sig H t P ≤ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy a ha
    exact hnorm_mem y (h15.hRn hy.2) (hsS y hy) a ha
  have hnorm : Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P ≤
      Subgroup.normalizer (T : Set G) := sup_le hCQ_le hSig_le
  have hTcard : Nat.card ↥T = Nat.card P ^ h15.m := by
    have h1 : Nat.card ↥T * Nat.card P = Nat.card P ^ h15.m * Nat.card P := by
      rw [hcard, hRcard, pow_succ']
      ring
    exact Nat.mul_right_cancel Nat.card_pos h1
  exact ⟨T, hTR, hTP, hsup, hnorm, hiff, hdec, hTcard⟩

end Work.ThmF.ChV3.Prove
