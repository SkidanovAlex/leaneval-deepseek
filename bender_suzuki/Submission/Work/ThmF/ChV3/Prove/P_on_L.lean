import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.ThmF.ChV3.Prove.L_facts
import Submission.Work.ThmF.ChV3.Prove.W_V_on_L
import Submission.Work.ThmF.ChV3.Prove.S1_centralizerP_eq
import Submission.Work.ThmF.ChV3.Prove.S2_commS_mem_R
import Submission.Work.ThmF.ChV3.Prove.S3_T_facts

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.P_on_L` — Peterfalvi II Ch. V §3, step (15c)

`P` acts non-trivially on `L = X₅ ∩ C_G(st)` (cyclic of order `9`), and the commutator map
sends `L × P` into `Z₁ = ⟨st⟩`.

* **`P` acts on `L`.**  `P ≤ V = C_D(t)` (the standing hypothesis `CtxF.P_le`) and `V`
  normalises `L` (step (15b), `W_V_on_L`); hence `b L b⁻¹ = L` for `b ∈ P`.  Since
  `|P| = 3` (`d.p3`), the conjugation action of `P` on `L` has order dividing `3`, and `L`
  is cyclic of order `9`: the induced action on the order-`3` quotient `L/Z₁` is trivial,
  which is exactly `[L, P] ≤ Z₁` — the second conjunct, proved as the general
  `commutator_mem_of_cyclic_nine` (a cyclic group computation, using only that `a³ ∈ Z₁` for
  `a ∈ L`, that `b` centralises `Z₁`, and that `Z₁` is the set of elements of `L` of order
  dividing `3`).

* **Non-triviality.**  If `P` centralised `L`, a generator `g ∈ L` of order `9` would lie in
  `C_G(P)`; step (S2) `S2_commS_mem_R` then gives `g² = [g,s] ∈ R`.  But `R = T ⊔ P` is
  abelian of exponent `3` (S3 `S3_T_facts` gives `exp T = |P| = 3`, and `exp P = 3`), so
  `g⁶ = (g²)³ = 1`, contradicting `orderOf g = 9`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3.Prove

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint
open Work.ThmF.ChV3

/-- In a cyclic group of order `9`, the elements whose cube is trivial are exactly those of the
(unique) subgroup of order `3`: if `L` is cyclic of order `9`, `Z ≤ L` has order `3`, and
`x ∈ L` with `x³ = 1`, then `x ∈ Z`. -/
theorem pow_three_eq_one_mem_of_isCyclic_card_nine {G : Type} [Group G]
    {L Z : Subgroup G} (hLcyc : IsCyclic ↥L) (hLcard : Nat.card ↥L = 9)
    (hZL : Z ≤ L) (hZcard : Nat.card ↥Z = 3) {x : G} (hxL : x ∈ L) (hx : x ^ 3 = 1) :
    x ∈ Z := by
  haveI : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [hLcard]; norm_num)
  haveI : Finite ↥(Subgroup.zpowers (⟨x, hxL⟩ : ↥L)) := inferInstance
  have hsub : Subgroup.zpowers (⟨x, hxL⟩ : ↥L) ≤ Z.subgroupOf L := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers,
      show Nat.card ↥(Z.subgroupOf L) = Nat.card ↥Z from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv,
      hZcard, Subgroup.orderOf_mk]
    exact orderOf_dvd_iff_pow_eq_one.mpr hx
  exact Subgroup.mem_subgroupOf.mp (hsub (Subgroup.mem_zpowers _))

/-- If `L` is cyclic of order `9` with subgroup `Z ≤ L` of order `3`, and `b` normalises `L`
and centralises `Z`, then every commutator `[a,b]` with `a ∈ L` lies in `Z`. -/
theorem commutator_mem_of_cyclic_nine {G : Type} [Group G] {L Z : Subgroup G}
    (hLcyc : IsCyclic ↥L) (hLcard : Nat.card ↥L = 9) (hZL : Z ≤ L) (hZcard : Nat.card ↥Z = 3)
    {b : G} (hbL : ∀ x ∈ L, b * x * b⁻¹ ∈ L) (hbZ : ∀ z ∈ Z, b * z * b⁻¹ = z) :
    ∀ a ∈ L, a * b * a⁻¹ * b⁻¹ ∈ Z := by
  have hcyc : ∀ x ∈ L, x ^ 3 = 1 → x ∈ Z :=
    fun x hxL hx => pow_three_eq_one_mem_of_isCyclic_card_nine hLcyc hLcard hZL hZcard hxL hx
  -- every cube in `L` lies in `Z` (the elements of exponent `3` form the subgroup `Z`)
  have hcube_mem : ∀ x ∈ L, x ^ 3 ∈ Z := by
    intro x hxL
    apply hcyc (x ^ 3) (L.pow_mem hxL 3)
    rw [← pow_mul]
    have hd : orderOf x ∣ 9 := by
      rw [← hLcard]; exact Subgroup.orderOf_dvd_natCard _ hxL
    exact orderOf_dvd_iff_pow_eq_one.mp hd
  intro a ha
  have ha3Z : a ^ 3 ∈ Z := hcube_mem a ha
  have hyL : b * a * b⁻¹ ∈ L := hbL a ha
  set y : G := b * a * b⁻¹ with hydef
  -- `y³ = b a³ b⁻¹ = a³`, because `b` centralises `Z ∋ a³`
  have hcube : y ^ 3 = a ^ 3 := by
    rw [hydef]
    have h3 : (b * a * b⁻¹) ^ 3 = b * a ^ 3 * b⁻¹ := by
      have := map_pow (MulAut.conj b).toMonoidHom a 3
      simpa [MulAut.conj_apply] using this.symm
    rw [h3]
    exact hbZ _ ha3Z
  haveI := hLcyc
  have hcomm : a * y = y * a := by
    have h1 : (⟨a, ha⟩ : ↥L) * (⟨y, hyL⟩ : ↥L) =
        (⟨y, hyL⟩ : ↥L) * (⟨a, ha⟩ : ↥L) := mul_comm' _ _
    exact congrArg Subtype.val h1
  -- `(a y⁻¹)³ = 1`, so `a y⁻¹ ∈ Z`, and `[a,b] = a y⁻¹`
  have h1 : (a * y⁻¹) ^ 3 = 1 := by
    have hc : Commute a y := hcomm
    rw [show (a * y⁻¹) ^ 3 = a ^ 3 * (y⁻¹) ^ 3 from hc.inv_right.mul_pow 3, inv_pow, hcube]
    group
  have haY : a * y⁻¹ ∈ L := L.mul_mem ha (L.inv_mem hyL)
  have hz : a * y⁻¹ ∈ Z := hcyc _ haY h1
  convert hz using 1
  rw [hydef]
  group

theorem P_on_L {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Work.ThmF.ChV3.Step11Out H Q t P h15.R T)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    (∃ x ∈ P, ∃ y ∈ Work.ThmF.ChV3.Lsub H s t, x * y ≠ y * x) ∧
      (∀ a ∈ Work.ThmF.ChV3.Lsub H s t, ∀ b ∈ P,
        a * b * a⁻¹ * b⁻¹ ∈ Work.ThmF.ChV3.Z1 s t) := by
  classical
  -- ## Step (15a): `L` is cyclic of order `9`, `s` inverts it, and `st ∈ L`
  obtain ⟨hLcyc, hLcard, hLinv, hstL⟩ := L_facts hFT hC4 c h15 d
  -- ## `Z₁ ≤ L` and `|Z₁| = 3`
  have hZ1le : Z1 s t ≤ Lsub H s t := Subgroup.zpowers_le.mpr hstL
  have hZ1card : Nat.card ↥(Z1 s t) = 3 := by
    rw [show Z1 s t = Subgroup.zpowers (s * t) from rfl, Nat.card_zpowers, d.f3]
  -- ## `P ≤ V` and `V` normalises `L` (step (15b)); hence `P` normalises `L`
  have hPNL : ∀ b ∈ P, ∀ a ∈ Lsub H s t, b * a * b⁻¹ ∈ Lsub H s t := by
    intro b hb a ha
    have hV : (Lsub H s t).map (MulAut.conj b).toMonoidHom = Lsub H s t :=
      (W_V_on_L hC4 c).2 b (c.P_le hb)
    have hmem : b * a * b⁻¹ ∈ (Lsub H s t).map (MulAut.conj b).toMonoidHom :=
      ⟨a, ha, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    rwa [hV] at hmem
  -- ## Step (S1): the decomposition of `C_G(P)`, and step (S2)
  have hdec : h15.R ⊔ (CQ Q P ⊔ Sig H t P) = CG P :=
    (S1_centralizerP_eq hFT hC4 c h15 h7 hpf).2.1
  have h2 : ∀ g ∈ CG P, g * s * g⁻¹ * s⁻¹ ∈ h15.R :=
    S2_commS_mem_R hFT hC4 c hpf hdec h15.hRn
  -- ## Step (S3): `s` inverts `T`, `st ∈ T`, `T` has exponent `|P|`
  obtain ⟨_hTinv, hstT, hTexp, _hTcard⟩ :=
    S3_T_facts hFT hC4 c hpf h15.m h15.hm h11 h7 h15.hcardR h15.hcq h2
  -- ## `T ≤ R`, `P ≤ R`
  have hTR : T ≤ h15.R := h11.TPR ▸ le_sup_left
  have hPR : P ≤ h15.R := h11.TPR ▸ le_sup_right
  -- ## `P` centralises `Z₁` (both `Z₁ ≤ T` and `P` lie in the abelian `R`)
  have hPZ1 : ∀ b ∈ P, ∀ z ∈ Z1 s t, b * z * b⁻¹ = z := by
    intro b hb z hz
    have hzT : z ∈ T := (Subgroup.zpowers_le.mpr hstT) hz
    have hcomm : b * z = z * b := mul_comm_of_mem h11.comm (hPR hb) (hTR hzT)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  -- ## `R = T ⊔ P` has exponent `3`
  have hPexp : ∀ p ∈ P, p ^ 3 = 1 := fun p hp =>
    orderOf_dvd_iff_pow_eq_one.mp (by rw [← d.p3]; exact Subgroup.orderOf_dvd_natCard _ hp)
  have hTexp3 : ∀ x ∈ T, x ^ 3 = 1 := fun x hx => by rw [← d.p3]; exact hTexp x hx
  have hPTnorm : P ≤ Subgroup.normalizer (T : Set G) := by
    have hcent : P ≤ Subgroup.centralizer (T : Set G) := by
      intro p hp
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (mul_comm_of_mem h11.comm (hPR hp) (hTR hx)).symm
    exact hcent.trans (Subgroup.centralizer_le_normalizer (T : Set G))
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left T P hPTnorm
  have hRexp : ∀ x ∈ h15.R, x ^ 3 = 1 := by
    intro x hxR
    have hxTP : x ∈ (T ⊔ P : Subgroup G) := by rw [h11.TPR]; exact hxR
    have hxTP' : x ∈ (↑(T ⊔ P) : Set G) := hxTP
    rw [hcoe, Set.mem_mul] at hxTP'
    obtain ⟨u, huT, v, hvP, huv⟩ := hxTP'
    rw [← huv,
      Commute.mul_pow (show Commute u v from mul_comm_of_mem h11.comm (hTR huT) (hPR hvP)),
      hTexp3 u huT, hPexp v hvP, one_mul]
  -- ## Second conjunct: `[L, P] ≤ Z₁`
  have hsecond : ∀ a ∈ Lsub H s t, ∀ b ∈ P, a * b * a⁻¹ * b⁻¹ ∈ Z1 s t := by
    intro a ha b hb
    exact commutator_mem_of_cyclic_nine hLcyc hLcard hZ1le hZ1card
      (fun x hx => hPNL b hb x hx) (hPZ1 b hb) a ha
  refine ⟨?_, hsecond⟩
  -- ## First conjunct: `P` does not centralise `L`
  by_contra hcon
  have hcon' : ∀ x ∈ P, ∀ y ∈ Lsub H s t, x * y = y * x := by
    intro x hx y hy
    by_contra hne
    exact hcon ⟨x, hx, y, hy, hne⟩
  -- a generator `g` of `L`, of order `9`
  obtain ⟨gX, hgX⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hLcyc
  set g : G := (gX : G) with hgdef
  have hgL : g ∈ Lsub H s t := gX.2
  have hgord : orderOf g = 9 := by
    have h1 : Nat.card ↥(Subgroup.zpowers gX) = orderOf gX := Nat.card_zpowers gX
    rw [hgX, Subgroup.card_top, hLcard] at h1
    rw [hgdef, Subgroup.orderOf_coe gX]
    exact h1.symm
  -- `g ∈ C_G(P)`, so `[g,s] = g² ∈ R`
  have hgCG : g ∈ CG P := by
    rw [CG, Subgroup.mem_centralizer_iff]
    intro p hp
    exact hcon' p hp g hgL
  have hgs : g * s * g⁻¹ * s⁻¹ = g ^ 2 := by
    have hsgs : s * g⁻¹ * s⁻¹ = g := by
      rw [show s * g⁻¹ * s⁻¹ = (s * g * s⁻¹)⁻¹ by group, hLinv g hgL, inv_inv]
    rw [show g * s * g⁻¹ * s⁻¹ = g * (s * g⁻¹ * s⁻¹) by group, hsgs, pow_two]
  have hmemR : g ^ 2 ∈ h15.R := by
    have hh := h2 g hgCG
    rwa [hgs] at hh
  -- `R` has exponent `3`, so `g⁶ = 1`, contradicting `orderOf g = 9`
  have h6 : g ^ 6 = 1 := by
    have hh := hRexp (g ^ 2) hmemR
    rwa [← pow_mul] at hh
  have hdvd : orderOf g ∣ 6 := orderOf_dvd_iff_pow_eq_one.mpr h6
  rw [hgord] at hdvd
  have : 9 ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  omega

end Work.ThmF.ChV3.Prove
