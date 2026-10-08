import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.ThmF.Prove.centDLowerCentralizerS
import Submission.Work.ThmF.ChV3.Prove.inv_of_fpf_conj
import Submission.Work.PGroup.card_sup_mul_card_inf_of_le_normalizer
import Submission.Work.ThmF.Bender.twoInvolutionsOdd
import Submission.Work.ThmF.ChV3.Prove.zpowers_mul_outside_T
import Submission.Work.ThmF.ChV3.Prove.exists_pow_order_prime

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.s_inverts_T_101`

`Work.ThmF.ChV3.Step11Out` supplies, through its field `reg`, that `C_Q(P)` acts *regularly* on
the order-`|P|` subgroups of `R` lying outside `T` and different from `P`.  We deduce from that
hypothesis alone (together with `|T| = |P|^m`, `|R| = |P|^{m+1}`, `s ∈ C_Q(P) ≤ N_G(T)`) that
the involution `conj s` has no fixed point other than `1` on `T`, and hence — `T` being abelian
inside the abelian `R = T ⊔ P` — that `s` inverts every element of `T`.

Fixed-point-freeness: if `x ∈ T`, `x ≠ 1`, were fixed by `s`, then (since `orderOf x ∣ |T| = |P|^m`
and `|P|` is prime) some `x₀ ∈ ⟨x⟩` has order `|P|` and is fixed by `s`; with `1 ≠ b₀ ∈ P`
(fixed by `s` because `s` centralises `P`) the cyclic group `B = ⟨x₀ b₀⟩ ≤ R` has order `|P|`,
is not contained in `T` and is different from `P` — and is fixed by `s`.  Both `s` and `1` are
therefore solutions of `B^y = B` for the action of `C_Q(P)`, contradicting the uniqueness in
`reg` and `s ≠ 1`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF.ChV3.Prove

private theorem mul_comm_of_mem' {G : Type} [Group G] {R : Subgroup G} (hc : IsMulCommutative ↥R)
    {a b : G} (ha : a ∈ R) (hb : b ∈ R) : a * b = b * a := by
  haveI := hc
  simpa using congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥R) (⟨b, hb⟩ : ↥R))

private theorem map_zpowers_conj' {G : Type} [Group G] (g x : G) :
    (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (g * x * g⁻¹) := by
  rw [MonoidHom.map_zpowers]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem s_inverts_T_101 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (hpf : Nat.card P = orderOf (s * t))
    {R T : Subgroup G} {m : ℕ} (hm : 1 ≤ m)
    (hRc : R ≤ Work.ThmF.ChV3.CG P) (hRn : Work.ThmF.ChV3.CG P ≤ Work.ThmF.ChV3.NG R)
    (hKer : Work.ThmF.ChV3.Ker H Q P t = P)
    (hcardR : Nat.card R = Nat.card ↥(Work.ThmF.ChV3.Ker H Q P t) * orderOf (s * t) ^ m)
    (hcq : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = orderOf (s * t) ^ m)
    (h11 : Work.ThmF.ChV3.Step11Out H Q t P R T) :
    ∀ x ∈ T, s * x * s⁻¹ = x⁻¹ := by
  classical
  -- ## 0.  Basic facts about the involution `s`, and `s ∈ C_Q(P)`
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [c.s_inv, pow_two] at h
    exact h
  have hs_ne : s ≠ 1 := by
    intro h1
    have h : (2 : ℕ) = 1 := by rw [← c.s_inv, orderOf_eq_one_iff.mpr h1]
    exact absurd h (by norm_num)
  have hV : Submission.Blueprint.centD H t ≤ Subgroup.centralizer ({s} : Set G) :=
    Work.ThmF.Prove.centDLowerCentralizerS c.split c.s_mem c.s_inv c.r_mem c.sid
  have hPs : ∀ q ∈ P, q * s = s * q := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mp (hV (c.P_le hq))
  have hsD : s ∈ Work.ThmF.ChV3.CQ Q P :=
    ⟨c.s_mem, Subgroup.mem_centralizer_iff.mpr (fun q hq => hPs q hq)⟩
  have hsCG : s ∈ Work.ThmF.ChV3.CG P := (Subgroup.mem_inf.mp hsD).2
  have hCQ_le_NG_T : Work.ThmF.ChV3.CQ Q P ≤ Subgroup.normalizer (T : Set G) :=
    le_trans le_sup_left h11.Tn
  have hsT : s ∈ Subgroup.normalizer (T : Set G) := hCQ_le_NG_T hsD
  have hTR : T ≤ R := by rw [← h11.TPR]; exact le_sup_left
  have hPR : P ≤ R := by rw [← h11.TPR]; exact le_sup_right
  have hcommT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    mul_comm_of_mem' h11.comm (hTR hx) (hTR hy)
  -- ## 1.  reduce to fixed-point-freeness of `conj s` on `T`
  refine inv_of_fpf_conj hcommT hsT hs2 ?_
  intro x hxT hfix
  by_contra hxne
  -- ## 2.  `|T| = |P|^m`
  have hPTcent : P ≤ Subgroup.centralizer (T : Set G) := fun p hp =>
    Subgroup.mem_centralizer_iff.mpr
      (fun q hq => (mul_comm_of_mem' h11.comm (hPR hp) (hTR hq)).symm)
  have hPTnorm : P ≤ Subgroup.normalizer (T : Set G) :=
    le_trans hPTcent (Subgroup.centralizer_le_normalizer (T : Set G))
  have hRcard : Nat.card R = Nat.card P * Nat.card P ^ m := by
    rw [hcardR, hKer, ← hpf]
  have hcardT : Nat.card ↥T = Nat.card P ^ m := by
    have hsup := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer (H := T) (K := P) hPTnorm
    rw [h11.TPR, h11.TP, Subgroup.card_bot, mul_one] at hsup
    have h1 : Nat.card ↥T * Nat.card ↥P = Nat.card P ^ m * Nat.card ↥P := by
      calc Nat.card ↥T * Nat.card ↥P = Nat.card ↥R := hsup.symm
        _ = Nat.card P * Nat.card P ^ m := hRcard
        _ = Nat.card P ^ m * Nat.card P := mul_comm _ _
    have hpos : 0 < Nat.card ↥P := Nat.card_pos
    exact Nat.mul_right_cancel hpos h1
  -- ## 3.  an element `x₀ ∈ ⟨x⟩` of order `|P|`, fixed by `s`
  have hxdvd : orderOf x ∣ Nat.card P ^ m := by
    have h := Subgroup.orderOf_dvd_natCard T hxT
    rwa [hcardT] at h
  obtain ⟨x₀, hx₀zp, _hx₀ord, hx₀p, hx₀ne⟩ :=
    exists_pow_order_prime c.P_prime hm hxne hxdvd
  have hx₀T : x₀ ∈ T := Subgroup.zpowers_le.mpr hxT hx₀zp
  have hsx₀ : s * x₀ * s⁻¹ = x₀ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx₀zp
    have h := map_zpow (MulAut.conj s).toMonoidHom x k
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [← hk, h, hfix]
  -- ## 4.  a nontrivial `b₀ ∈ P`, fixed by `s`
  have hPne : P ≠ ⊥ := fun h => c.P_prime.ne_one (Subgroup.card_eq_one.mpr h)
  obtain ⟨b₀, hb₀P, hb₀ne⟩ : ∃ b₀ ∈ P, b₀ ≠ 1 := by
    by_contra h
    push_neg at h
    exact hPne ((Subgroup.eq_bot_iff_forall P).mpr h)
  have hsb₀ : s * b₀ * s⁻¹ = b₀ := by
    have hc : b₀ * s = s * b₀ := Subgroup.mem_centralizer_iff.mp hsCG b₀ hb₀P
    calc s * b₀ * s⁻¹ = b₀ * s * s⁻¹ := by rw [← hc]
      _ = b₀ := by group
  -- ## 5.  the order-`|P|` subgroup `⟨x₀ b₀⟩ ≤ R` outside `T`, fixed by `s`
  obtain ⟨hBR, hBcard, hBnotT, hBneP⟩ :=
    zpowers_mul_outside_T h11.comm hTR hPR h11.TP c.P_prime hx₀T hx₀p hx₀ne hb₀P hb₀ne
  have hsB : (Subgroup.zpowers (x₀ * b₀)).map (MulAut.conj s).toMonoidHom =
      Subgroup.zpowers (x₀ * b₀) := by
    rw [map_zpowers_conj']
    congr 1
    rw [show s * (x₀ * b₀) * s⁻¹ = (s * x₀ * s⁻¹) * (s * b₀ * s⁻¹) by group, hsx₀, hsb₀]
  -- ## 6.  regularity of `C_Q(P)` on the order-`|P|` subgroups of `R` outside `T` gives `s = 1`
  obtain ⟨y0, _, huniq⟩ :=
    h11.reg (Subgroup.zpowers (x₀ * b₀)) (Subgroup.zpowers (x₀ * b₀))
      hBR hBR hBcard hBcard hBnotT hBnotT hBneP hBneP
  have hy_eq : (⟨s, hsD⟩ : ↥(Work.ThmF.ChV3.CQ Q P)) = y0 := huniq ⟨s, hsD⟩ hsB
  have hone_eq : (1 : ↥(Work.ThmF.ChV3.CQ Q P)) = y0 := by
    refine huniq 1 ?_
    change (Subgroup.zpowers (x₀ * b₀)).map
      (MulAut.conj (((1 : ↥(Work.ThmF.ChV3.CQ Q P)) : G))).toMonoidHom =
        Subgroup.zpowers (x₀ * b₀)
    rw [map_zpowers_conj']
    simp
  have hse : (⟨s, hsD⟩ : ↥(Work.ThmF.ChV3.CQ Q P)) = 1 := by rw [hy_eq, ← hone_eq]
  exact hs_ne (by simpa using Subtype.ext_iff.mp hse)

end Work.ThmF.ChV3.Prove
