import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.PGroup.card_sup_mul_card_inf_of_le_normalizer
import Submission.Work.ThmF.Bender.twoInvolutionsOdd
import Submission.Work.ThmF.Prove.centDLowerCentralizerS
import Submission.Work.ThmF.ChV3.Prove.exponent_eq_of_free_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.S3_T_facts` — leaf **S3** of the Ch. V §3 second half

The design's `T_facts` (`ThmF/_design16/ThmF16.lean`): `s` inverts `T`, `st ∈ T`, `T` has
exponent `p = |P|`, and `|T| = |P|^m`.  The statement below is the design's, with the standing
hypotheses of `Chain15` split into the explicit pieces its proof consumes (`hKer`, `hcardR`,
`hcq`, `h2`) and the step-(11) output `Step11Out`; the missing binder `{T : Subgroup G}` of the
requested rendering has been added.

Math (all inside the abelian subgroup `R = T ⊔ P`, `T ⊓ P = ⊥`):

* `|T| = |P|^m`: purely from `T ⊓ P = ⊥`, `T ⊔ P = R` and `|R| = |P|^{m+1}`.
* `s * t ∈ T`: `s * t` has odd order, so `h2` at `g = s t` gives `(s t)² ∈ R`, whence
  `s t ∈ R`; then `s t ∈ R = T ⊔ P` cannot lie outside `T` because `s` would give a nontrivial
  fixed point of the regular action of `C_Q(P)` used below.
* `T` is inverted by `s` and has exponent `|P|`, via the regularity `h11.reg` of `C_Q(P)` on the
  order-`|P|` subgroups of `R` outside `T`: it forces `C_Q(P)` to act *freely* on `T^#`
  (`hfree`), whence (orbit count `|C_Q(P)| = |T| − 1`) it acts transitively, so `T` is elementary
  abelian of exponent `|P|`, and the order-two automorphism `conj_s` of `T` is fixed-point-free,
  hence inversion.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3.Prove

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

/-- Commutativity of two elements of a commutative subgroup. -/
theorem mul_comm_of_mem {G : Type} [Group G] {R : Subgroup G} (hc : IsMulCommutative ↥R)
    {a b : G} (ha : a ∈ R) (hb : b ∈ R) : a * b = b * a := by
  haveI := hc
  simpa using congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥R) (⟨b, hb⟩ : ↥R))

/-- The image of `zpowers x` under conjugation by `g`. -/
theorem map_zpowers_conj {G : Type} [Group G] (g x : G) :
    (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (g * x * g⁻¹) := by
  rw [MonoidHom.map_zpowers]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem S3_T_facts {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (hpf : Nat.card P = orderOf (s * t))
    {R : Subgroup G} (m : ℕ) (hm : 1 ≤ m) {T : Subgroup G}
    (h11 : Work.ThmF.ChV3.Step11Out H Q t P R T)
    (hKer : Work.ThmF.ChV3.Ker H Q P t = P)
    (hcardR : Nat.card R = Nat.card ↥(Work.ThmF.ChV3.Ker H Q P t) * orderOf (s * t) ^ m)
    (hcq : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = orderOf (s * t) ^ m)
    (h2 : ∀ g ∈ Work.ThmF.ChV3.CG P, g * s * g⁻¹ * s⁻¹ ∈ R) :
    (∀ x ∈ T, s * x * s⁻¹ = x⁻¹) ∧ s * t ∈ T ∧ (∀ x ∈ T, x ^ Nat.card P = 1) ∧
      Nat.card T = Nat.card P ^ m := by
  classical
  -- ## 0. The standing context: involutions, `P ≤ C_G(s)`, `P ≤ C_G(t)`.
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [c.s_inv, pow_two] at h
    exact h
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [c.split.invol, pow_two] at h
    exact h
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hs_ne : s ≠ 1 := by
    intro h1
    have h : (2 : ℕ) = 1 := by rw [← c.s_inv, orderOf_eq_one_iff.mpr h1]
    exact absurd h (by norm_num)
  have hV : Submission.Blueprint.centD H t ≤ Subgroup.centralizer ({s} : Set G) :=
    Work.ThmF.Prove.centDLowerCentralizerS c.split c.s_mem c.s_inv c.r_mem c.sid
  have hPs : ∀ p ∈ P, p * s = s * p := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.mp (hV (c.P_le hp))
  have hPt : ∀ p ∈ P, p * t = t * p := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.mem_inf.mp (c.P_le hp)).2)
  -- `s ∈ C_Q(P)`
  have hsD : s ∈ Work.ThmF.ChV3.CQ Q P :=
    ⟨c.s_mem, Subgroup.mem_centralizer_iff.mpr (fun p hp => hPs p hp)⟩
  -- `C_Q(P) ≤ N_G(T)`
  have hCQ_le_NG_T : Work.ThmF.ChV3.CQ Q P ≤ Subgroup.normalizer (T : Set G) :=
    le_trans le_sup_left h11.Tn
  -- `s * t` has odd order (`H` strongly embedded, `s ∈ H`).
  have hodd : Odd (orderOf (s * t)) :=
    Work.ThmF.Bender.twoInvolutionsOdd c.split.stronglyEmbedded (c.split.le c.s_mem) c.s_inv
      c.split.invol c.split.not_mem
  have hPodd : Odd (Nat.card P) := by rw [hpf]; exact hodd
  -- `T ≤ R`, `P ≤ R`, and commutativity inside `R`.
  have hTR : T ≤ R := by rw [← h11.TPR]; exact le_sup_left
  have hPR : P ≤ R := by rw [← h11.TPR]; exact le_sup_right
  -- `P ≤ N_G(T)` (both lie in the abelian `R`).
  have hPTcent : P ≤ Subgroup.centralizer (T : Set G) := fun p hp =>
    Subgroup.mem_centralizer_iff.mpr (fun t ht => (mul_comm_of_mem h11.comm (hPR hp) (hTR ht)).symm)
  have hPTnorm : P ≤ Subgroup.normalizer (T : Set G) :=
    le_trans hPTcent (Subgroup.centralizer_le_normalizer (T : Set G))
  -- ## 1. `|T| = |P|^m`.
  have hRcard : Nat.card R = Nat.card P * Nat.card P ^ m := by
    rw [hcardR, hKer, ← hpf]
  have hcardT : Nat.card ↥T = Nat.card P ^ m := by
    have hsup := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer (H := T) (K := P) hPTnorm
    rw [h11.TPR, h11.TP, Subgroup.card_bot, mul_one] at hsup
    have h1 : Nat.card ↥T * Nat.card ↥P = Nat.card P ^ m * Nat.card ↥P := by
      rw [← hsup, hRcard, mul_comm]
    exact Nat.mul_right_cancel (Nat.card_pos_iff.mpr ⟨⟨⟨1, P.one_mem⟩⟩, inferInstance⟩) h1
  have hcardD : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = Nat.card ↥T - 1 := by
    have h1 : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = Nat.card ↥T := by
      rw [hcq, ← hpf, ← hcardT]
    omega
  -- ## 2. `C_Q(P)` acts freely on `T^#` (`h11.reg`).
  have hfree : ∀ y ∈ Work.ThmF.ChV3.CQ Q P, ∀ x ∈ T, x ≠ 1 → y * x * y⁻¹ = x → y = 1 := by
    intro y hyD x hxT hxne hfix
    -- a nonidentity element of the prime-order `P`
    have hPne : P ≠ ⊥ := fun h => c.P_prime.ne_one (Subgroup.card_eq_one.mpr h)
    obtain ⟨b₀, hb₀P, hb₀ne⟩ : ∃ b₀ ∈ P, b₀ ≠ 1 := by
      by_contra h
      push_neg at h
      exact hPne ((Subgroup.eq_bot_iff_forall P).mpr h)
    have hb₀R : b₀ ∈ R := hPR hb₀P
    have hb₀ord : orderOf b₀ = Nat.card P := by
      have hdvd := Subgroup.orderOf_dvd_natCard P hb₀P
      rcases (Nat.dvd_prime c.P_prime).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hb₀ne
      · exact h
    -- an element `x₀` of `⟨x⟩` of order `|P|`
    have hxdvd : orderOf x ∣ Nat.card P ^ m := by
      have h := Subgroup.orderOf_dvd_natCard T hxT
      rwa [hcardT] at h
    obtain ⟨k, hk, hxk⟩ := (Nat.dvd_prime_pow c.P_prime).mp hxdvd
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, pow_zero] at hxk
        exact absurd (orderOf_eq_one_iff.mp hxk) hxne
      · exact h
    set x₀ : G := x ^ (Nat.card P ^ (k - 1)) with hx₀def
    have hx₀p : x₀ ^ Nat.card P = 1 := by
      rw [hx₀def, ← pow_mul]
      have hmul : Nat.card P ^ (k - 1) * Nat.card P = Nat.card P ^ k := by
        rw [← pow_succ, Nat.sub_add_cancel hk1]
      rw [hmul, ← hxk, pow_orderOf_eq_one]
    have hx₀ne : x₀ ≠ 1 := by
      intro h
      rw [hx₀def] at h
      have hd : orderOf x ∣ Nat.card P ^ (k - 1) := orderOf_dvd_iff_pow_eq_one.mpr h
      rw [hxk] at hd
      have hle := Nat.le_of_dvd (Nat.pow_pos c.P_prime.pos) hd
      have hlt : Nat.card P ^ (k - 1) < Nat.card P ^ k :=
        (Nat.pow_lt_pow_iff_right c.P_prime.one_lt).mpr (Nat.sub_lt (by omega) one_pos)
      exact absurd hle (not_le.mpr hlt)
    have hx₀ord : orderOf x₀ = Nat.card P := by
      have hdvd : orderOf x₀ ∣ Nat.card P := orderOf_dvd_iff_pow_eq_one.mpr hx₀p
      rcases (Nat.dvd_prime c.P_prime).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx₀ne
      · exact h
    have hx₀T : x₀ ∈ T := hx₀def ▸ T.pow_mem hxT _
    have hx₀R : x₀ ∈ R := hTR hx₀T
    -- `B₀ = ⟨x₀ * b₀⟩` is an order-`|P|` subgroup of `R` outside `T`, not equal to `P`
    have hcommx₀b₀ : x₀ * b₀ = b₀ * x₀ := mul_comm_of_mem h11.comm hx₀R hb₀R
    have hb₀pow : b₀ ^ Nat.card P = 1 := by rw [← hb₀ord, pow_orderOf_eq_one]
    have hxb_pow : (x₀ * b₀) ^ Nat.card P = 1 := by
      rw [Commute.mul_pow hcommx₀b₀ (Nat.card P), hx₀p, hb₀pow, mul_one]
    have hxb_ne : x₀ * b₀ ≠ 1 := by
      intro h
      have hx₀eq : x₀ = b₀⁻¹ := by
        have h' := inv_eq_of_mul_eq_one_right h
        calc x₀ = (x₀⁻¹)⁻¹ := (inv_inv x₀).symm
          _ = b₀⁻¹ := by rw [h']
      have hx₀P : x₀ ∈ P := hx₀eq ▸ P.inv_mem hb₀P
      have hmem : x₀ ∈ T ⊓ P := ⟨hx₀T, hx₀P⟩
      rw [h11.TP, Subgroup.mem_bot] at hmem
      exact hx₀ne hmem
    have hxb_ord : orderOf (x₀ * b₀) = Nat.card P := by
      have hdvd : orderOf (x₀ * b₀) ∣ Nat.card P := orderOf_dvd_iff_pow_eq_one.mpr hxb_pow
      rcases (Nat.dvd_prime c.P_prime).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hxb_ne
      · exact h
    have hBcard : Nat.card ↥(Subgroup.zpowers (x₀ * b₀)) = Nat.card P := by
      rw [Nat.card_zpowers, hxb_ord]
    have hBR : Subgroup.zpowers (x₀ * b₀) ≤ R :=
      Subgroup.zpowers_le.mpr (R.mul_mem hx₀R hb₀R)
    have hBnotT : ¬ Subgroup.zpowers (x₀ * b₀) ≤ T := by
      intro hle
      have hxbT : x₀ * b₀ ∈ T := hle (Subgroup.mem_zpowers _)
      have hbT : b₀ ∈ T := by
        have h := T.mul_mem (T.inv_mem hx₀T) hxbT
        rwa [show x₀⁻¹ * (x₀ * b₀) = b₀ by group] at h
      have hmem : b₀ ∈ T ⊓ P := ⟨hbT, hb₀P⟩
      rw [h11.TP, Subgroup.mem_bot] at hmem
      exact hb₀ne hmem
    have hBneP : Subgroup.zpowers (x₀ * b₀) ≠ P := by
      intro hEq
      have hxbP : x₀ * b₀ ∈ P := hEq ▸ Subgroup.mem_zpowers _
      have hx₀P : x₀ ∈ P := by
        have h := P.mul_mem hxbP (P.inv_mem hb₀P)
        rwa [show (x₀ * b₀) * b₀⁻¹ = x₀ by group] at h
      have hmem : x₀ ∈ T ⊓ P := ⟨hx₀T, hx₀P⟩
      rw [h11.TP, Subgroup.mem_bot] at hmem
      exact hx₀ne hmem
    -- `y` fixes `B₀`
    have h1 : y * x₀ * y⁻¹ = x₀ := by
      rw [hx₀def]
      have hp := map_pow (MulAut.conj y).toMonoidHom x (Nat.card P ^ (k - 1))
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hp
      rw [hp, hfix]
    have hyCG : y ∈ Work.ThmF.ChV3.CG P := (Subgroup.mem_inf.mp hyD).2
    have h2b : y * b₀ * y⁻¹ = b₀ := by
      have hcomm : b₀ * y = y * b₀ := Subgroup.mem_centralizer_iff.mp hyCG b₀ hb₀P
      calc y * b₀ * y⁻¹ = b₀ * y * y⁻¹ := by rw [← hcomm]
        _ = b₀ := by group
    have hyfix : (Subgroup.zpowers (x₀ * b₀)).map (MulAut.conj y).toMonoidHom =
        Subgroup.zpowers (x₀ * b₀) := by
      rw [map_zpowers_conj,
        show y * (x₀ * b₀) * y⁻¹ = (y * x₀ * y⁻¹) * (y * b₀ * y⁻¹) by group, h1, h2b]
    -- `reg` at `A = B = B₀`: the unique such `z` is both `y` and `1`.
    obtain ⟨y0, _, hy0uniq⟩ :=
      h11.reg (Subgroup.zpowers (x₀ * b₀)) (Subgroup.zpowers (x₀ * b₀))
        hBR hBR hBcard hBcard hBnotT hBnotT hBneP hBneP
    have hy_eq : (⟨y, hyD⟩ : ↥(Work.ThmF.ChV3.CQ Q P)) = y0 := hy0uniq ⟨y, hyD⟩ hyfix
    have h1_eq : (1 : ↥(Work.ThmF.ChV3.CQ Q P)) = y0 := by
      refine hy0uniq 1 ?_
      show (Subgroup.zpowers (x₀ * b₀)).map
        (MulAut.conj ((1 : ↥(Work.ThmF.ChV3.CQ Q P)) : G)).toMonoidHom = Subgroup.zpowers (x₀ * b₀)
      rw [map_zpowers_conj]
      simp
    have : (⟨y, hyD⟩ : ↥(Work.ThmF.ChV3.CQ Q P)) = 1 := by rw [hy_eq, ← h1_eq]
    exact Subtype.ext_iff.mp this
  -- ## 3. `s` inverts `T` (fixed-point-free order-two automorphism of the abelian `T`).
  have hinv : ∀ x ∈ T, s * x * s⁻¹ = x⁻¹ := by
    intro x hxT
    have hsxT : s * x * s⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hCQ_le_NG_T hsD) x).mp hxT
    have hsxs : s * (s * x * s⁻¹) * s⁻¹ = x := by
      rw [show s * (s * x * s⁻¹) * s⁻¹ = (s * s) * x * (s⁻¹ * s⁻¹) by group, hs2,
        hs_inv, hs2, one_mul, mul_one]
    have hyT : x * (s * x * s⁻¹) ∈ T := T.mul_mem hxT hsxT
    have hfix : s * (x * (s * x * s⁻¹)) * s⁻¹ = x * (s * x * s⁻¹) := by
      calc s * (x * (s * x * s⁻¹)) * s⁻¹
          = (s * x * s⁻¹) * (s * (s * x * s⁻¹) * s⁻¹) := by group
        _ = (s * x * s⁻¹) * x := by rw [hsxs]
        _ = x * (s * x * s⁻¹) := (mul_comm_of_mem h11.comm (hTR hxT) (hTR hsxT)).symm
    have hxz : x * (s * x * s⁻¹) = 1 := by
      by_contra hne
      exact hs_ne (hfree s hsD (x * (s * x * s⁻¹)) hyT hne hfix)
    exact eq_inv_of_mul_eq_one_right hxz
  -- ## 4. `s * t ∈ T`.
  have hstT : s * t ∈ T := by
    by_contra hst_nT
    have hst_eq : (s * t) * s * (s * t)⁻¹ * s⁻¹ = (s * t) ^ 2 := by
      rw [show (s * t)⁻¹ = t * s by rw [mul_inv_rev, hs_inv, ht_inv], pow_two]
      group
    have hstCG : s * t ∈ Work.ThmF.ChV3.CG P := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      calc p * (s * t) = (p * s) * t := (mul_assoc p s t).symm
        _ = (s * p) * t := by rw [hPs p hp]
        _ = s * (p * t) := mul_assoc s p t
        _ = s * (t * p) := by rw [hPt p hp]
        _ = (s * t) * p := (mul_assoc s t p).symm
    have hsq : (s * t) ^ 2 ∈ R := by
      have h := h2 (s * t) hstCG
      rwa [hst_eq] at h
    have hstR : s * t ∈ R := by
      have hstpow : ((s * t) ^ 2) ^ ((orderOf (s * t) + 1) / 2) = s * t := by
        obtain ⟨k, hk⟩ := hodd
        rw [← pow_mul]
        have h2k : 2 * ((orderOf (s * t) + 1) / 2) = orderOf (s * t) + 1 := by
          rw [hk]; omega
        rw [h2k, pow_succ, pow_orderOf_eq_one, one_mul]
      rw [← hstpow]
      exact R.pow_mem hsq _
    have hsst : s * (s * t) * s⁻¹ = (s * t)⁻¹ := by
      have hR : (s * t)⁻¹ = t * s := by rw [mul_inv_rev, hs_inv, ht_inv]
      have hL : s * (s * t) * s⁻¹ = t * s := by
        rw [hs_inv, show s * (s * t) * s = (s * s) * (t * s) by group, hs2, one_mul]
      rw [hL, hR]
    have hBR : Subgroup.zpowers (s * t) ≤ R := Subgroup.zpowers_le.mpr hstR
    have hBcard : Nat.card ↥(Subgroup.zpowers (s * t)) = Nat.card P := by
      rw [Nat.card_zpowers]; exact hpf.symm
    have hBnotT : ¬ Subgroup.zpowers (s * t) ≤ T :=
      fun hle => hst_nT (hle (Subgroup.mem_zpowers _))
    have hBneP : Subgroup.zpowers (s * t) ≠ P := by
      intro hEq
      have hstP : s * t ∈ P := hEq ▸ Subgroup.mem_zpowers _
      have hfixst : s * (s * t) * s⁻¹ = s * t := by
        rw [(hPs (s * t) hstP).symm]
        group
      have hsq2 : (s * t) * (s * t) = 1 := by
        have h := congrArg (fun z => z * (s * t)) (hfixst.symm.trans hsst)
        rwa [inv_mul_cancel] at h
      have hdvd2 : orderOf (s * t) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hsq2)
      have hPdvd : Nat.card P ∣ 2 := by rw [hpf]; exact hdvd2
      rcases (Nat.dvd_prime Nat.prime_two).mp hPdvd with h | h
      · exact c.P_prime.ne_one h
      · obtain ⟨j, hj⟩ := hPodd
        rw [h] at hj
        omega
    obtain ⟨y0, _, hy0uniq⟩ :=
      h11.reg (Subgroup.zpowers (s * t)) (Subgroup.zpowers (s * t))
        hBR hBR hBcard hBcard hBnotT hBnotT hBneP hBneP
    have hs_satisfies : (Subgroup.zpowers (s * t)).map (MulAut.conj ((⟨s, hsD⟩ : ↥(Work.ThmF.ChV3.CQ Q P)) : G)).toMonoidHom =
        Subgroup.zpowers (s * t) := by
      rw [map_zpowers_conj, hsst]
      exact Subgroup.zpowers_inv (g := s * t)
    have hs_eq : (⟨s, hsD⟩ : ↥(Work.ThmF.ChV3.CQ Q P)) = y0 := hy0uniq ⟨s, hsD⟩ hs_satisfies
    have h1_eq : (1 : ↥(Work.ThmF.ChV3.CQ Q P)) = y0 := by
      refine hy0uniq 1 ?_
      show (Subgroup.zpowers (s * t)).map
        (MulAut.conj ((1 : ↥(Work.ThmF.ChV3.CQ Q P)) : G)).toMonoidHom = Subgroup.zpowers (s * t)
      rw [map_zpowers_conj]
      simp
    have hseq : (⟨s, hsD⟩ : ↥(Work.ThmF.ChV3.CQ Q P)) = 1 := by rw [hs_eq, ← h1_eq]
    exact hs_ne (Subtype.ext_iff.mp hseq)
  -- ## 5. `T` has exponent `|P|`.
  have hexp : ∀ x ∈ T, x ^ Nat.card P = 1 :=
    exponent_eq_of_free_conj (T := T) (D := Work.ThmF.ChV3.CQ Q P) (p := Nat.card P) (m := m)
      c.P_prime hm hcardT hCQ_le_NG_T hcardD hfree
  exact ⟨hinv, hstT, hexp, hcardT⟩

end Work.ThmF.ChV3.Prove
