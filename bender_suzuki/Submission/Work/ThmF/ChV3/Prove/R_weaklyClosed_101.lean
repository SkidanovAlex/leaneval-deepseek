import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.ThmF.ChV3.Prove.S1_centralizerP_eq
import Submission.Work.ThmF.ChV3.Prove.Center_R1_101
import Submission.Work.PGroup.card_sup_mul_card_inf_of_le_normalizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ThmF.ChV3.Prove

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint
open Pointwise

attribute [local instance] Fintype.ofFinite

variable {G : Type} [Group G] [Finite G]

/-! ## 0. Conjugation of subgroups

`cj g A = g A g⁻¹`.  These are the elementary rewriting rules used throughout. -/

private lemma cj_self_iff (a : G) (A : Subgroup G) : cj a A = A ↔ a ∈ NG A := by
  rw [show cj a A = A.map (MulAut.conj a) from rfl, Subgroup.mem_normalizer_iff_map_conj_eq]

private lemma cj_one (A : Subgroup G) : cj (1 : G) A = A :=
  (cj_self_iff 1 A).mpr (NG A).one_mem

private lemma cj_mul (a b : G) (A : Subgroup G) : cj a (cj b A) = cj (a * b) A := by
  simp only [cj]
  rw [Subgroup.map_map]
  have h : (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom
      = (MulAut.conj (a * b)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [h]

private lemma cj_eq_iff (a b : G) (A : Subgroup G) : cj a A = cj b A ↔ a⁻¹ * b ∈ NG A := by
  constructor
  · intro h
    have h2 : cj (a⁻¹ * a) A = cj (a⁻¹ * b) A := by rw [← cj_mul, ← cj_mul, h]
    rw [inv_mul_cancel, cj_one] at h2
    exact (cj_self_iff (a⁻¹ * b) A).mp h2.symm
  · intro h
    have h2 : cj (a⁻¹ * b) A = A := (cj_self_iff (a⁻¹ * b) A).mpr h
    have h3 : cj a (cj (a⁻¹ * b) A) = cj a A := by rw [h2]
    simp only [cj_mul, mul_inv_cancel_left] at h3
    exact h3.symm

private lemma card_cj (a : G) (A : Subgroup G) : Nat.card ↥(cj a A) = Nat.card ↥A := by
  rw [show cj a A = A.map (MulAut.conj a) from rfl]
  exact Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj a))

private lemma cj_le_cj {a : G} {A B : Subgroup G} (h : A ≤ B) : cj a A ≤ cj a B :=
  Subgroup.map_le_map_iff_of_injective (MulEquiv.injective (MulAut.conj a)) |>.mpr h

/-! ## 1. The standing context of the weak-closure lemma -/

/-- The hypotheses of `R_weaklyClosed_101`, bundled. -/
structure R101Ctx (H Q : Subgroup G) (t s r : G) (P : Subgroup G) (R1 : Subgroup G) where
  hFT : Submission.Blueprint.FeitThompsonProp
  hC4 : Submission.Blueprint.ChIIFourProp
  c : CtxF H Q t s r P
  h15 : Chain15 H Q t s r P
  h7 : Ker H Q P t = P
  hpf : Nat.card P = orderOf (s * t)
  T : Subgroup G
  h11 : Step11Out H Q t P h15.R T
  hm1 : h15.m = 1
  hsig : Sig H t P = ⊥
  hGp : pPart (Nat.card P) (Nat.card G) = Nat.card P ^ 3
  hcb : ∀ x ∈ CQ Q P, x ≠ 1 → ∀ X : Subgroup G, IsPGroup (Nat.card P) X →
      X ≤ Subgroup.centralizer ({x} : Set G) → Nat.card X ≤ Nat.card P
  hNR : Nat.card ↥(NG h15.R) = Nat.card P ^ 3 * (Nat.card P - 1)
  hRR1 : h15.R ≤ R1
  hR1N : R1 ≤ NG h15.R
  hR1c : Nat.card R1 = Nat.card P ^ 3
  hR1n : NG h15.R ≤ NG R1

variable {H Q : Subgroup G} {t s r : G} {P R1 : Subgroup G}

/-- `|R| = p²`. -/
private theorem R101_card_R (C : R101Ctx H Q t s r P R1) : Nat.card ↥C.h15.R = Nat.card P ^ 2 := by
  have h := C.h15.hcardR
  rw [C.h7, C.hpf, C.hm1, pow_one] at h
  rw [h, pow_two, ← C.hpf]

/-- `|C_Q(P)| = p - 1`. -/
private theorem R101_card_C (C : R101Ctx H Q t s r P R1) :
    Nat.card ↥(CQ Q P) = Nat.card P - 1 := by
  have h := C.h15.hcq
  rw [← C.hpf, C.hm1, pow_one] at h
  omega

/-- `p` is odd. -/
private theorem R101_p_odd (C : R101Ctx H Q t s r P R1) : Nat.card P ≠ 2 := by
  intro h2
  have hQ : Nat.card ↥Q = Nat.card ↥(CQ Q P) ^ Nat.card P := C.h15.h4
  rw [R101_card_C C, h2] at hQ
  have hQ1 : Nat.card ↥Q = 1 := by rw [hQ]; norm_num
  have hdvd : 2 ∣ Nat.card ↥Q := by
    have hle : Subgroup.zpowers s ≤ Q := Subgroup.zpowers_le.mpr C.c.s_mem
    have h1 : Nat.card ↥(Subgroup.zpowers s) ∣ Nat.card ↥Q :=
      Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, C.c.s_inv] at h1
  rw [hQ1] at hdvd
  omega

/-- `|Σ| = 1` (`Σ = ⊥`). -/
private theorem R101_card_sig (C : R101Ctx H Q t s r P R1) : Nat.card ↥(Sig H t P) = 1 := by
  rw [C.hsig, Subgroup.card_bot]

/-- `|C_G(P)| = p²(p-1)`. -/
private theorem R101_card_CG (C : R101Ctx H Q t s r P R1) :
    Nat.card ↥(CG P) = Nat.card P ^ 2 * (Nat.card P - 1) := by
  obtain ⟨-, -, hCG⟩ := S1_centralizerP_eq C.hFT C.hC4 C.c C.h15 C.h7 C.hpf
  rw [hCG, R101_card_R C, R101_card_C C, R101_card_sig C, mul_one]

/-- The centre of `R1` is `T`. -/
private theorem R101_center (C : R101Ctx H Q t s r P R1) :
    Subgroup.center ↥R1 = C.T.subgroupOf R1 :=
  (Center_R1_101 C.hFT C.hC4 C.c C.h15 C.h7 C.hpf C.h11 C.hm1 C.hsig C.hRR1 C.hR1N
    C.hR1n C.hR1c).1

/-- `|T| = p`. -/
private theorem R101_card_T (C : R101Ctx H Q t s r P R1) : Nat.card ↥C.T = Nat.card P :=
  (Center_R1_101 C.hFT C.hC4 C.c C.h15 C.h7 C.hpf C.h11 C.hm1 C.hsig C.hRR1 C.hR1N
    C.hR1n C.hR1c).2

/-- `T ≤ R`. -/
private theorem R101_T_le_R (C : R101Ctx H Q t s r P R1) : C.T ≤ C.h15.R := by
  rw [← C.h11.TPR]; exact le_sup_left

/-- `T ≤ R1`. -/
private theorem R101_T_le_R1 (C : R101Ctx H Q t s r P R1) : C.T ≤ R1 :=
  (R101_T_le_R C).trans C.hRR1

/-- `T` is normal in `R1`. -/
private theorem R101_T_normal (C : R101Ctx H Q t s r P R1) : (C.T.subgroupOf R1).Normal := by
  rw [← R101_center C]
  infer_instance

/-- If `Y ≤ X`, `|X| = p³`, `|Y| = p²` and `p` is prime, then `X` normalises `Y`. -/
private lemma le_normalizer_of_card_eq {p : ℕ} (hp : p.Prime) {X Y : Subgroup G}
    (hYX : Y ≤ X) (hX : Nat.card ↥X = p ^ 3) (hY : Nat.card ↥Y = p ^ 2) :
    X ≤ NG Y := by
  have hsub : Nat.card ↥(Y.subgroupOf X) = p ^ 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX)).trans hY
  have hidx : (Y.subgroupOf X).index = p := by
    have h := Subgroup.card_mul_index (Y.subgroupOf X)
    rw [hsub, hX] at h
    have h2 : p ^ 2 * (Y.subgroupOf X).index = p ^ 2 * p := by rw [h, pow_succ]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h2
  have hmin : (Nat.card ↥X).minFac = p := by
    rw [hX]
    have hn : p ^ 3 ≠ 1 := (one_lt_pow₀ hp.one_lt (by norm_num : (3 : ℕ) ≠ 0)).ne'
    have hpf : ((p ^ 3).minFac).Prime := Nat.minFac_prime hn
    have hdvd : (p ^ 3).minFac ∣ p := hpf.dvd_of_dvd_pow (Nat.minFac_dvd (p ^ 3))
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd h hpf.ne_one
    · exact h
  have hnorm : (Y.subgroupOf X).Normal :=
    Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, hmin])
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mp hnorm

/-- **Sylow adjustment.**  Every `G`-conjugate of `R` contained in `R1` is already an
`N_G(R1)`-conjugate of `R`: the conjugating element normalises `R1`.

Indeed `A = R^g ≤ R1` gives `R ≤ g⁻¹R1g`, and both `R1` and `g⁻¹R1g` are subgroups of
`N_G(R)` of order `p³` containing the normal (index `p`) subgroup `R`; a product argument then
forces `g⁻¹R1g = R1`. -/
private theorem R101_conj_le_imp_mem_ng (C : R101Ctx H Q t s r P R1) {g : G}
    (hg : cj g C.h15.R ≤ R1) : g ∈ NG R1 := by
  set p : ℕ := Nat.card P with hp_def
  have hp : p.Prime := C.c.P_prime
  have hcard_R : Nat.card ↥C.h15.R = p ^ 2 := R101_card_R C
  have hcard_R1 : Nat.card ↥R1 = p ^ 3 := C.hR1c
  set Ah : Subgroup G := cj g⁻¹ R1 with hAh_def
  have hcard_Ah : Nat.card ↥Ah = p ^ 3 := by rw [hAh_def, card_cj]; exact C.hR1c
  have hRAh : C.h15.R ≤ Ah := by
    have h1 : cj g⁻¹ (cj g C.h15.R) ≤ cj g⁻¹ R1 := cj_le_cj hg
    rwa [cj_mul, inv_mul_cancel, cj_one] at h1
  have hAh_N : Ah ≤ NG C.h15.R := le_normalizer_of_card_eq hp hRAh hcard_Ah hcard_R
  have hAh_R1 : Ah ≤ NG R1 := hAh_N.trans C.hR1n
  have hR1_le : R1 ≤ Ah := by
    by_contra hle
    have hne : Ah ⊓ R1 ≠ R1 := fun h => hle (le_of_eq h.symm |>.trans inf_le_left)
    have hdvd : Nat.card ↥(Ah ⊓ R1) ∣ p ^ 3 := by
      rw [← hcard_R1]; exact Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hkeq' : Nat.card ↥(Ah ⊓ R1) = p ^ k := hkeq
    have hk3 : k ≤ 3 := hk
    have hklt : k < 3 := by
      rcases lt_or_eq_of_le hk3 with h | h
      · exact h
      · exfalso
        refine hne (Subgroup.eq_of_le_of_card_ge inf_le_right ?_)
        rw [hkeq', h, hcard_R1]
    have hk2 : k ≤ 2 := by omega
    have hge : p ^ 2 ≤ Nat.card ↥(Ah ⊓ R1) := by
      have hdvd2 : p ^ 2 ∣ Nat.card ↥(Ah ⊓ R1) := by
        rw [← hcard_R]
        exact Subgroup.card_dvd_of_le (le_inf hRAh C.hRR1)
      exact Nat.le_of_dvd Nat.card_pos hdvd2
    have hle2 : Nat.card ↥(Ah ⊓ R1) ≤ p ^ 2 := by
      rw [hkeq']; exact Nat.pow_le_pow_right hp.pos hk2
    have hm : Nat.card ↥(Ah ⊓ R1) = p ^ 2 := le_antisymm hle2 hge
    have hsup : Nat.card ↥(Ah ⊔ R1) = p ^ 4 := by
      have hcs := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer (H := R1) (K := Ah) hAh_R1
      rw [sup_comm R1 Ah, inf_comm R1 Ah, hcard_R1, hcard_Ah, hm] at hcs
      have : Nat.card ↥(Ah ⊔ R1) * p ^ 2 = p ^ 4 * p ^ 2 := by rw [hcs]; ring
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) this
    have hdvd3 : Nat.card ↥(Ah ⊔ R1) ∣ p ^ 3 * (p - 1) := by
      rw [← C.hNR]
      exact Subgroup.card_dvd_of_le (sup_le hAh_N C.hR1N)
    rw [hsup] at hdvd3
    have h4 : p ^ 3 * p ∣ p ^ 3 * (p - 1) := by
      rw [← pow_succ]; exact hdvd3
    have hdiv : p ∣ p - 1 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos 3) h4
    have hp1 : p ∣ 1 := by
      have h := Nat.dvd_sub (dvd_refl p) hdiv
      rwa [Nat.sub_sub_self hp.one_le] at h
    exact hp.not_dvd_one hp1
  have hAh_eq : Ah = R1 :=
    (Subgroup.eq_of_le_of_card_ge hR1_le (by rw [hcard_Ah, hcard_R1])).symm
  have hg_inv : g⁻¹ ∈ NG R1 := by
    have hc : cj g⁻¹ R1 = R1 := by rw [← hAh_def]; exact hAh_eq
    exact (cj_self_iff g⁻¹ R1).mp hc
  simpa using (NG R1).inv_mem hg_inv

/-- Commuting two elements of `R`. -/
private lemma mul_comm_of_mem_R (C : R101Ctx H Q t s r P R1) {a b : G}
    (ha : a ∈ C.h15.R) (hb : b ∈ C.h15.R) : a * b = b * a := by
  haveI := C.h11.comm
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥C.h15.R) (⟨b, hb⟩ : ↥C.h15.R))

/-- Membership criterion for `T = Z(R1)`. -/
private lemma R101_mem_T_iff (C : R101Ctx H Q t s r P R1) {t : G} :
    t ∈ C.T ↔ t ∈ R1 ∧ ∀ g ∈ R1, g * t * g⁻¹ = t := by
  constructor
  · intro ht
    have htR1 : t ∈ R1 := R101_T_le_R1 C ht
    refine ⟨htR1, ?_⟩
    intro g hg
    have h1 : (⟨t, htR1⟩ : ↥R1) ∈ Subgroup.center ↥R1 := by
      rw [R101_center C]; exact ht
    have h2 := Subgroup.mem_center_iff.mp h1 (⟨g, hg⟩ : ↥R1)
    have h3 : (g * t : G) = t * g := congrArg (fun z : ↥R1 => (z : G)) h2
    rw [h3, mul_assoc, mul_inv_cancel, mul_one]
  · rintro ⟨htR1, hcomm⟩
    have h1 : (⟨t, htR1⟩ : ↥R1) ∈ Subgroup.center ↥R1 := by
      rw [Subgroup.mem_center_iff]
      intro g
      refine Subtype.ext ?_
      have h2 := hcomm (g : G) g.2
      have h3 : (g : G) * t = t * (g : G) := by
        have := congrArg (fun z => z * (g : G)) h2
        simpa [mul_assoc] using this
      simpa using h3
    rw [R101_center C] at h1
    exact h1

/-- `T` is invariant under `N_G(R1)`. -/
private lemma R101_T_char (C : R101Ctx H Q t s r P R1) {v : G} (hv : v ∈ NG R1) :
    ∀ t ∈ C.T, v * t * v⁻¹ ∈ C.T := by
  intro t ht
  have htR1 : t ∈ R1 := R101_T_le_R1 C ht
  have hmem : v * t * v⁻¹ ∈ R1 := (Subgroup.mem_normalizer_iff.mp hv t).mp htR1
  refine (R101_mem_T_iff C).mpr ⟨hmem, ?_⟩
  intro g hg
  have hvg : v⁻¹ * g * v ∈ R1 := by
    have hv' : v⁻¹ ∈ NG R1 := (NG R1).inv_mem hv
    simpa using (Subgroup.mem_normalizer_iff.mp hv' g).mp hg
  have h2 : (v⁻¹ * g * v) * t * (v⁻¹ * g * v)⁻¹ = t :=
    ((R101_mem_T_iff C).mp ht).2 _ hvg
  calc g * (v * t * v⁻¹) * g⁻¹
      = v * ((v⁻¹ * g * v) * t * (v⁻¹ * g * v)⁻¹) * v⁻¹ := by group
    _ = v * t * v⁻¹ := by rw [h2]

/-- Conjugation by an element of `N_G(R1)` preserves `T`. -/
private lemma R101_cj_T (C : R101Ctx H Q t s r P R1) {v : G} (hv : v ∈ NG R1) :
    cj v C.T = C.T := by
  refine le_antisymm ?_ ?_
  · intro t ht
    obtain ⟨s, hs, hsv⟩ := Subgroup.mem_map.mp ht
    rw [← hsv]
    simpa [MulAut.conj_apply] using R101_T_char C hv s hs
  · intro t ht
    have hv' : v⁻¹ ∈ NG R1 := (NG R1).inv_mem hv
    refine Subgroup.mem_map.mpr ⟨v⁻¹ * t * v, ?_, ?_⟩
    · simpa using R101_T_char C hv' t ht
    · show v * (v⁻¹ * t * v) * v⁻¹ = t
      group

/-- `R1/T` is commutative. -/
private lemma R101_R1_comm (C : R101Ctx H Q t s r P R1) :
    ∀ u ∈ R1, ∀ w ∈ R1, u * w * u⁻¹ * w⁻¹ ∈ C.T := by
  haveI : Fact (Nat.card P).Prime := ⟨C.c.P_prime⟩
  haveI : (C.T.subgroupOf R1).Normal := R101_T_normal C
  have hsub : Nat.card ↥(C.T.subgroupOf R1) = Nat.card P :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (R101_T_le_R1 C))).trans (R101_card_T C)
  have hcard : Nat.card (↥R1 ⧸ (C.T.subgroupOf R1)) = Nat.card P ^ 2 := by
    rw [← Subgroup.index_eq_card (C.T.subgroupOf R1)]
    have h := Subgroup.card_mul_index (C.T.subgroupOf R1)
    rw [hsub, C.hR1c] at h
    have h2 : Nat.card P * (C.T.subgroupOf R1).index = Nat.card P * Nat.card P ^ 2 := by
      rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h2
  haveI : IsMulCommutative (↥R1 ⧸ (C.T.subgroupOf R1)) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
  intro u hu w hw
  have key : QuotientGroup.mk' (C.T.subgroupOf R1)
      ((⟨u, hu⟩ : ↥R1) * ⟨w, hw⟩ * ⟨u, hu⟩⁻¹ * ⟨w, hw⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [mul_comm' (QuotientGroup.mk' (C.T.subgroupOf R1) (⟨u, hu⟩ : ↥R1))
      (QuotientGroup.mk' (C.T.subgroupOf R1) (⟨w, hw⟩ : ↥R1))]
    group
  have hmem : ((⟨u, hu⟩ : ↥R1) * ⟨w, hw⟩ * ⟨u, hu⟩⁻¹ * ⟨w, hw⟩⁻¹) ∈ C.T.subgroupOf R1 :=
    (QuotientGroup.eq_one_iff _).mp (by simpa [QuotientGroup.mk'_apply] using key)
  rwa [Subgroup.mem_subgroupOf] at hmem

/-- `C_Q(P)` fixes `R/T` pointwise. -/
private lemma R101_C_comm_R (C : R101Ctx H Q t s r P R1) :
    ∀ c ∈ CQ Q P, ∀ r ∈ C.h15.R, c * r * c⁻¹ * r⁻¹ ∈ C.T := by
  intro c hc r hr
  have hcP : c ∈ CG P := hc.2
  have hcR1 : c ∈ NG R1 := C.hR1n (C.h15.hRn hc.2)
  have hP_R : P ≤ C.h15.R := by rw [← C.h11.TPR]; exact le_sup_right
  have hTle : C.T ≤ NG P := by
    rw [Subgroup.le_normalizer_iff]
    intro t ht p hp
    have h1 : t * p = p * t := mul_comm_of_mem_R C (R101_T_le_R C ht) (hP_R hp)
    have h2 : t * p * t⁻¹ = p := by rw [h1, mul_assoc, mul_inv_cancel, mul_one]
    rwa [h2]
  have hPT : (↑(P ⊔ C.T) : Set G) = (↑P : Set G) * (↑C.T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left P C.T hTle
  have hr' : r ∈ (↑P : Set G) * (↑C.T : Set G) := by
    rw [← hPT, show P ⊔ C.T = C.h15.R from by rw [sup_comm]; exact C.h11.TPR]
    exact hr
  obtain ⟨p, hp, t, ht, rfl⟩ := Set.mem_mul.mp hr'
  have hcp : c * p = p * c := ((Subgroup.mem_centralizer_iff.mp hcP) p hp).symm
  have hct : c * t * c⁻¹ ∈ C.T := R101_T_char C hcR1 t ht
  have hmem : (c * t * c⁻¹) * t⁻¹ ∈ C.T := C.T.mul_mem hct (C.T.inv_mem ht)
  have heq : c * (p * t) * c⁻¹ * (p * t)⁻¹ = p * ((c * t * c⁻¹) * t⁻¹) * p⁻¹ := by
    calc c * (p * t) * c⁻¹ * (p * t)⁻¹
        = c * p * t * c⁻¹ * t⁻¹ * p⁻¹ := by group
      _ = p * c * t * c⁻¹ * t⁻¹ * p⁻¹ := by rw [hcp]
      _ = p * ((c * t * c⁻¹) * t⁻¹) * p⁻¹ := by group
  rw [heq]
  have hpc : p * ((c * t * c⁻¹) * t⁻¹) = ((c * t * c⁻¹) * t⁻¹) * p :=
    mul_comm_of_mem_R C (hP_R hp) (R101_T_le_R C hmem)
  rw [hpc, mul_assoc, mul_inv_cancel, mul_one]
  exact hmem

/-- If `c` factors as `(x u x⁻¹)(x c₀ x⁻¹)` with `u ∈ R1` and `c₀ ∈ C_Q(P)`, then `c` fixes
`(xRx⁻¹)/T` pointwise. -/
private lemma R101_c_acts_trivially_on_conj (C : R101Ctx H Q t s r P R1) {x u c c₀ : G}
    (hx : x ∈ NG R1) (hu : u ∈ R1) (hc₀ : c₀ ∈ CQ Q P)
    (hc_eq : c = (x * u * x⁻¹) * (x * c₀ * x⁻¹)) :
    ∀ a ∈ cj x C.h15.R, c * a * c⁻¹ * a⁻¹ ∈ C.T := by
  intro a ha
  obtain ⟨r, hr, hrfl⟩ := Subgroup.mem_map.mp ha
  rw [← hrfl]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hc₀R : c₀ ∈ NG C.h15.R := C.h15.hRn hc₀.2
  have hcr : c₀ * r * c₀⁻¹ ∈ C.h15.R := (Subgroup.mem_normalizer_iff.mp hc₀R r).mp hr
  have h1 : u * (c₀ * r * c₀⁻¹) * u⁻¹ * (c₀ * r * c₀⁻¹)⁻¹ ∈ C.T :=
    R101_R1_comm C u hu _ (C.hRR1 hcr)
  have h2 : c₀ * r * c₀⁻¹ * r⁻¹ ∈ C.T := R101_C_comm_R C c₀ hc₀ r hr
  have h3 : u * (c₀ * r * c₀⁻¹) * u⁻¹ * r⁻¹
      = (u * (c₀ * r * c₀⁻¹) * u⁻¹ * (c₀ * r * c₀⁻¹)⁻¹) * (c₀ * r * c₀⁻¹ * r⁻¹) := by
    group
  have hinner : u * (c₀ * r * c₀⁻¹) * u⁻¹ * r⁻¹ ∈ C.T := by
    rw [h3]; exact C.T.mul_mem h1 h2
  have hconj : c * (x * r * x⁻¹) * c⁻¹ * (x * r * x⁻¹)⁻¹
      = x * (u * (c₀ * r * c₀⁻¹) * u⁻¹ * r⁻¹) * x⁻¹ := by
    rw [hc_eq]; group
  rw [hconj]
  exact R101_T_char C hx _ hinner

/-- **Semiregularity.**  `C_Q(P)` acts freely on the `N_G(R1)`-conjugates of `R` other than `R`
itself. -/
private theorem R101_semireg (C : R101Ctx H Q t s r P R1) :
    ∀ x ∈ NG R1, cj x C.h15.R ≠ C.h15.R → ∀ c ∈ CQ Q P, c ≠ 1 →
      cj c (cj x C.h15.R) ≠ cj x C.h15.R := by
  intro x hx hxR c hc hc1 heq
  exfalso
  set p : ℕ := Nat.card P with hp_def
  have hp : p.Prime := C.c.P_prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hRc : Nat.card ↥C.h15.R = p ^ 2 := R101_card_R C
  have hR1c : Nat.card ↥R1 = p ^ 3 := C.hR1c
  set A : Subgroup G := cj x C.h15.R with hA_def
  have hAcard : Nat.card ↥A = p ^ 2 := by rw [hA_def, card_cj]; exact hRc
  have hA_ne : A ≠ C.h15.R := by rw [hA_def]; exact hxR
  have hA_R1 : A ≤ R1 := by
    intro y hy
    rw [hA_def] at hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    rw [← hzy]
    simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      (Subgroup.mem_normalizer_iff.mp hx z).mp (C.hRR1 hz)
  have hcA : c ∈ NG A := (cj_self_iff c A).mp heq
  have hR1_le_NG_A : R1 ≤ NG A := le_normalizer_of_card_eq hp hA_R1 hR1c hAcard
  have hR1_le_NG_R : R1 ≤ NG C.h15.R := C.hR1N
  have hcR : c ∈ NG C.h15.R := C.h15.hRn hc.2
  have hxc : x⁻¹ * c * x ∈ NG C.h15.R := by
    rw [← cj_self_iff]
    calc cj (x⁻¹ * c * x) C.h15.R
        = cj x⁻¹ (cj c (cj x C.h15.R)) := by rw [← cj_mul, ← cj_mul]
      _ = cj x⁻¹ (cj x C.h15.R) := by rw [heq]
      _ = C.h15.R := by rw [cj_mul, inv_mul_cancel, cj_one]
  -- the subgroup `R1 ⊓ C_Q(P)` is trivial, and `R1 ⊔ C_Q(P) = N_G(R)`
  have hC_le_NR : CQ Q P ≤ NG C.h15.R := fun x hx => C.h15.hRn hx.2
  have hC_le_NR1 : CQ Q P ≤ NG R1 := hC_le_NR.trans C.hR1n
  have hcard_inf : Nat.card ↥(R1 ⊓ CQ Q P) = 1 := by
    have hdvd : Nat.card ↥(R1 ⊓ CQ Q P) ∣ Nat.card P ^ 3 := by
      rw [← hR1c]; exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hk2 : k ≤ 3 := hk
    have hk0 : k = 0 := by
      by_contra hk0
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hpk : p ∣ Nat.card ↥(R1 ⊓ CQ Q P) := by
        rw [hkeq]
        exact dvd_pow_self p hk0
      have hpdvd : p ∣ Nat.card P - 1 := by
        rw [← R101_card_C C]
        exact hpk.trans (Subgroup.card_dvd_of_le inf_le_right)
      have : p ∣ 1 := by
        have h := Nat.dvd_sub (dvd_refl p) hpdvd
        rwa [Nat.sub_sub_self hp.one_le] at h
      exact hp.not_dvd_one this
    rw [hkeq, hk0, pow_zero]
  have hcard_sup : Nat.card ↥(R1 ⊔ CQ Q P) = Nat.card P ^ 3 * (Nat.card P - 1) := by
    have hcs := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer (H := R1) (K := CQ Q P)
      hC_le_NR1
    rw [hR1c, R101_card_C C, hcard_inf, mul_one] at hcs
    exact hcs
  have hsup_eq : R1 ⊔ CQ Q P = NG C.h15.R := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hR1_le_NG_R hC_le_NR) ?_
    rw [hcard_sup, C.hNR]
  -- decompose `x⁻¹ c x` in `N_G(R) = R1 · C_Q(P)`
  have hprod : (↑(R1 ⊔ CQ Q P) : Set G) = (↑R1 : Set G) * (↑(CQ Q P) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left R1 (CQ Q P) hC_le_NR1
  obtain ⟨u, hu, c₀, hc₀, hu_eq⟩ := Set.mem_mul.mp
    (show x⁻¹ * c * x ∈ (↑R1 : Set G) * (↑(CQ Q P) : Set G) from by
      rw [← hprod, hsup_eq]; exact hxc)
  have hc_split : c = (x * u * x⁻¹) * (x * c₀ * x⁻¹) := by
    have h1 : c = x * (u * c₀) * x⁻¹ := by rw [hu_eq]; group
    rw [h1]; group
  -- `c` fixes the quotients `R/T` and `A/T`
  have hD_R : ∀ w ∈ C.h15.R, c * w * c⁻¹ * w⁻¹ ∈ C.T := fun w hw => R101_C_comm_R C c hc w hw
  have hD_A : ∀ w ∈ A, c * w * c⁻¹ * w⁻¹ ∈ C.T := by
    have h := R101_c_acts_trivially_on_conj C hx hu hc₀ hc_split
    intro w hw
    rw [hA_def] at hw
    exact h w hw
  have hT_le_A : C.T ≤ A := by
    intro y hy
    have hy' : y ∈ cj x C.T := by
      have h1 : C.T = cj x C.T := (R101_cj_T C hx).symm
      exact h1 ▸ hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy'
    rw [hA_def]
    exact Subgroup.mem_map.mpr ⟨z, R101_T_le_R C hz, hzy⟩
  have hinf_RA : C.h15.R ⊓ A = C.T := by
    have hTle : C.T ≤ C.h15.R ⊓ A := le_inf (R101_T_le_R C) hT_le_A
    have hge : Nat.card P ≤ Nat.card ↥(C.h15.R ⊓ A) := by
      have h1 : Nat.card ↥C.T ∣ Nat.card ↥(C.h15.R ⊓ A) := Subgroup.card_dvd_of_le hTle
      rw [R101_card_T C] at h1
      exact Nat.le_of_dvd Nat.card_pos h1
    have hne : Nat.card ↥(C.h15.R ⊓ A) ≠ Nat.card P ^ 2 := by
      intro h
      have hRleA : C.h15.R ≤ A := by
        have h2 : Nat.card ↥C.h15.R ≤ Nat.card ↥(C.h15.R ⊓ A) := by rw [hRc, h]
        intro y hy
        exact (Subgroup.eq_of_le_of_card_ge inf_le_left h2 ▸ hy).2
      exact hA_ne ((Subgroup.eq_of_le_of_card_ge hRleA (le_of_eq (by rw [hAcard, hRc]))).symm)
    have hle : Nat.card ↥(C.h15.R ⊓ A) ≤ Nat.card P := by
      have hdvd : Nat.card ↥(C.h15.R ⊓ A) ∣ Nat.card P ^ 2 := by
        rw [← hRc]; exact Subgroup.card_dvd_of_le inf_le_left
      obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      by_contra hgt
      have hk2 : k ≤ 2 := hk
      rcases (show k = 2 ∨ k ≤ 1 by omega) with h2 | h1
      · exact hne (by rw [hkeq, h2])
      · refine absurd ?_ hgt
        rw [hkeq]
        calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos h1
          _ = p := pow_one p
    have hcard_eq : Nat.card ↥(C.h15.R ⊓ A) = Nat.card P := le_antisymm hle hge
    exact (Subgroup.eq_of_le_of_card_ge hTle (le_of_eq (by rw [R101_card_T C, hcard_eq]))).symm
  have hsup_RA : C.h15.R ⊔ A = R1 := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le C.hRR1 hA_R1) ?_
    have hcardsup : Nat.card ↥(C.h15.R ⊔ A) = p ^ 3 := by
      have hcs := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer (H := C.h15.R) (K := A)
        (hA_R1.trans hR1_le_NG_R)
      rw [hinf_RA, hRc, hAcard, R101_card_T C] at hcs
      have h2 : Nat.card ↥(C.h15.R ⊔ A) * Nat.card P = Nat.card P ^ 3 * Nat.card P := by
        rw [hcs]; ring
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
    rw [hR1c, hcardsup]
  -- hence `c` fixes `R1/T`
  have hD_R1 : ∀ w ∈ R1, c * w * c⁻¹ * w⁻¹ ∈ C.T := by
    intro w hw
    have hprodRA : (↑(C.h15.R ⊔ A) : Set G) = (↑C.h15.R : Set G) * (↑A : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left C.h15.R A (hA_R1.trans hR1_le_NG_R)
    have hw' : w ∈ (↑C.h15.R : Set G) * (↑A : Set G) := by
      rw [← hprodRA, hsup_RA]; exact hw
    obtain ⟨r, hr, a, ha, hrfl⟩ := Set.mem_mul.mp hw'
    rw [← hrfl]
    have h1 : c * r * c⁻¹ * r⁻¹ ∈ C.T := hD_R r hr
    have h2 : c * a * c⁻¹ * a⁻¹ ∈ C.T := hD_A a ha
    have h3 : r * (c * a * c⁻¹ * a⁻¹) * r⁻¹ = c * a * c⁻¹ * a⁻¹ :=
      ((R101_mem_T_iff C).mp h2).2 r (C.hRR1 hr)
    have hstep : c * (r * a) * c⁻¹ * (r * a)⁻¹
        = (c * r * c⁻¹ * r⁻¹) * (c * a * c⁻¹ * a⁻¹) := by
      calc c * (r * a) * c⁻¹ * (r * a)⁻¹
          = (c * r * c⁻¹ * r⁻¹) * (r * (c * a * c⁻¹ * a⁻¹) * r⁻¹) := by group
        _ = (c * r * c⁻¹ * r⁻¹) * (c * a * c⁻¹ * a⁻¹) := by rw [h3]
    rw [hstep]
    exact C.T.mul_mem h1 h2
  -- the homomorphism `R1 → T`, `w ↦ [w,c]`
  let ψ : ↥R1 →* ↥C.T :=
    { toFun := fun w => ⟨c * (w : G) * c⁻¹ * (w : G)⁻¹, hD_R1 w w.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        have ha' : (a : G) * (c * (b : G) * c⁻¹ * (b : G)⁻¹) * (a : G)⁻¹
            = c * (b : G) * c⁻¹ * (b : G)⁻¹ :=
          ((R101_mem_T_iff C).mp (hD_R1 b b.2)).2 a a.2
        simp only [Subgroup.coe_mul]
        calc c * ((a : G) * (b : G)) * c⁻¹ * ((a : G) * (b : G))⁻¹
            = (c * (a : G) * c⁻¹ * (a : G)⁻¹)
                * ((a : G) * (c * (b : G) * c⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
          _ = (c * (a : G) * c⁻¹ * (a : G)⁻¹) * (c * (b : G) * c⁻¹ * (b : G)⁻¹) := by rw [ha'] }
  have hrel : Nat.card ↥R1 = Nat.card ↥(MonoidHom.ker ψ) * Nat.card ↥(MonoidHom.range ψ) := by
    rw [← Subgroup.card_mul_index (MonoidHom.ker ψ), Subgroup.index_eq_card]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  have hrange_card : Nat.card ↥(MonoidHom.range ψ) ≤ p := by
    have h1 : Nat.card ↥(MonoidHom.range ψ) ∣ Nat.card ↥C.T :=
      Subgroup.card_subgroup_dvd_card (MonoidHom.range ψ)
    rw [R101_card_T C] at h1
    exact Nat.le_of_dvd Nat.card_pos h1
  have hker_ge : p ^ 2 ≤ Nat.card ↥(MonoidHom.ker ψ) := by
    rw [hR1c] at hrel
    have h1 : Nat.card P ^ 2 * p ≤ Nat.card ↥(MonoidHom.ker ψ) * p := by
      calc Nat.card P ^ 2 * p = Nat.card P ^ 3 := by ring
        _ = Nat.card ↥(MonoidHom.ker ψ) * Nat.card ↥(MonoidHom.range ψ) := hrel
        _ ≤ Nat.card ↥(MonoidHom.ker ψ) * p := Nat.mul_le_mul_left _ hrange_card
    exact Nat.le_of_mul_le_mul_right h1 hp.pos
  have hKcard : Nat.card ↥(R1 ⊓ Subgroup.centralizer ({c} : Set G))
      = Nat.card ↥(MonoidHom.ker ψ) := by
    refine (Nat.card_congr ?_).symm
    refine
      { toFun := fun w => ⟨(w.1 : G), ⟨w.1.2, ?_⟩⟩
        invFun := fun w => ⟨⟨(w.1 : G), w.2.1⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hw : c * (w.1 : G) * c⁻¹ * (w.1 : G)⁻¹ = 1 :=
        congrArg (fun z : ↥C.T => (z : G)) (MonoidHom.mem_ker.mp w.2)
      have hcw : c * (w.1 : G) * c⁻¹ = (w.1 : G) :=
        mul_inv_eq_one.mp (by simpa [mul_assoc] using hw)
      have hcomm : c * (w.1 : G) = (w.1 : G) * c := by
        have := congrArg (fun z => z * c) hcw
        simpa [mul_assoc] using this
      refine Subgroup.mem_centralizer_iff.mpr (fun h hh => ?_)
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hcomm
    · have hcomm : c * (w.1 : G) = (w.1 : G) * c :=
        (Subgroup.mem_centralizer_iff.mp w.2.2) c rfl
      refine Subtype.ext ?_
      show c * (w.1 : G) * c⁻¹ * (w.1 : G)⁻¹ = 1
      rw [hcomm]
      group
    · intro w
      exact Subtype.ext rfl
    · intro w
      exact Subtype.ext rfl
  have hcb_bound : Nat.card ↥(R1 ⊓ Subgroup.centralizer ({c} : Set G)) ≤ p := by
    refine C.hcb c hc hc1 _ ?_ ?_
    · obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).mp
        (show Nat.card ↥(R1 ⊓ Subgroup.centralizer ({c} : Set G)) ∣ Nat.card P ^ 3 from by
          rw [← hR1c]; exact Subgroup.card_dvd_of_le inf_le_left)
      exact IsPGroup.of_card hkeq
    · intro y hy
      exact hy.2
  rw [hKcard] at hcb_bound
  have hchain : p ^ 2 ≤ p := le_trans hker_ge hcb_bound
  nlinarith [hchain, hp.two_le]

/-- Each fibre of `h ↦ hRh⁻¹` on `N_G(R1)` has `|N_G(R)|` elements. -/
private lemma R101_fiber_card (C : R101Ctx H Q t s r P R1) :
    ∀ A ∈ Finset.univ.image (fun x : ↥(NG R1) => cj (x : G) C.h15.R),
      (Finset.univ.filter (fun x : ↥(NG R1) => cj (x : G) C.h15.R = A)).card
        = Nat.card ↥(NG C.h15.R) := by
  intro A hA
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hA
  have hcard : Nat.card ↥(NG C.h15.R) =
      (Finset.univ.filter (fun x : ↥(NG R1) => cj (x : G) C.h15.R = A)).card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype
      (fun x : ↥(NG R1) => cj (x : G) C.h15.R = A)]
    refine Fintype.card_congr
      ⟨fun n => ⟨⟨(a : G) * (n : G), (NG R1).mul_mem a.2 (C.hR1n n.2)⟩, ?_⟩,
       fun x => ⟨(a : G)⁻¹ * ((x : ↥(NG R1)) : G), ?_⟩, ?_, ?_⟩
    · show cj ((a : G) * (n : G)) C.h15.R = A
      rw [← cj_mul, (cj_self_iff (n : G) C.h15.R).mpr n.2, ha]
    · have hx : cj (((x : ↥(NG R1)) : G)) C.h15.R = A := x.2
      rw [← cj_eq_iff, ha, hx]
    · intro n
      exact Subtype.ext (by simp only [Subtype.coe_mk]; group)
    · intro x
      exact Subtype.ext (by simp only [Subtype.coe_mk]; group)
  exact hcard.symm

/-- `|Y| · |N_G(R)| = |N_G(R1)|` for `Y` the `N_G(R1)`-orbit of `R`. -/
private lemma R101_orbit_card (C : R101Ctx H Q t s r P R1) :
    (Finset.univ.image (fun x : ↥(NG R1) => cj (x : G) C.h15.R)).card
        * Nat.card ↥(NG C.h15.R) = Nat.card ↥(NG R1) := by
  have h := Finset.card_eq_sum_card_image
    (fun x : ↥(NG R1) => cj (x : G) C.h15.R) Finset.univ
  rw [Finset.sum_congr rfl (fun b hb => R101_fiber_card C b hb)] at h
  rw [Finset.sum_const, smul_eq_mul] at h
  rw [Finset.card_univ, Nat.card_eq_fintype_card (α := ↥(NG C.h15.R))] at h
  rw [Nat.card_eq_fintype_card (α := ↥(NG C.h15.R)),
    Nat.card_eq_fintype_card (α := ↥(NG R1))]
  exact h.symm

/-- `p` does not divide the length of the `N_G(R1)`-orbit of `R`. -/
private lemma R101_p_not_dvd_orbit (C : R101Ctx H Q t s r P R1) :
    ¬ Nat.card P ∣ (Finset.univ.image (fun x : ↥(NG R1) => cj (x : G) C.h15.R)).card := by
  intro hdvd
  set p : ℕ := Nat.card P with hp_def
  have hp : p.Prime := C.c.P_prime
  have hgold := R101_orbit_card C
  have hN : Nat.card ↥(NG C.h15.R) = p ^ 3 * (p - 1) := C.hNR
  have hR1dvd : p ^ 3 ∣ Nat.card ↥(NG R1) := by
    refine ⟨(Finset.univ.image (fun x : ↥(NG R1) => cj (x : G) C.h15.R)).card * (p - 1), ?_⟩
    rw [← hgold, hN]; ring
  have hp4 : p ^ 4 ∣ Nat.card ↥(NG R1) := by
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k * (p - 1), ?_⟩
    rw [← hgold, hN, hk]; ring
  have hHp : pPart p (Nat.card ↥(NG R1)) = p ^ 3 := by
    have hfacG : (Nat.card G).factorization p = 3 := by
      have h := C.hGp
      rw [pPart] at h
      exact Nat.pow_right_injective hp.two_le h
    have h1 : pPart p (Nat.card ↥(NG R1)) ∣ p ^ 3 := by
      rw [pPart, ← hfacG]
      refine Nat.pow_dvd_pow p ?_
      refine (hp.pow_dvd_iff_le_factorization (Nat.card_pos.ne')).mp ?_
      exact dvd_trans ((hp.pow_dvd_iff_le_factorization (Nat.card_pos.ne')).mpr le_rfl)
        (Subgroup.card_subgroup_dvd_card _)
    have h2 : p ^ 3 ∣ pPart p (Nat.card ↥(NG R1)) := by
      rw [pPart]
      refine Nat.pow_dvd_pow p ?_
      exact (hp.pow_dvd_iff_le_factorization (Nat.card_pos.ne')).mp hR1dvd
    exact Nat.dvd_antisymm h1 h2
  rw [pPart] at hHp
  have h4 : 4 ≤ (Nat.card ↥(NG R1)).factorization p :=
    (hp.pow_dvd_iff_le_factorization (Nat.card_pos.ne')).mp hp4
  have : (Nat.card ↥(NG R1)).factorization p = 3 := Nat.pow_right_injective hp.two_le hHp
  omega

/-- `|Y| ≤ p + 1`. -/
private lemma R101_orbit_le (C : R101Ctx H Q t s r P R1) :
    (Finset.univ.image (fun x : ↥(NG R1) => cj (x : G) C.h15.R)).card ≤ Nat.card P + 1 := by
  set p : ℕ := Nat.card P with hp_def
  have hp : p.Prime := C.c.P_prime
  have hRc : Nat.card ↥C.h15.R = p ^ 2 := R101_card_R C
  have hTc : Nat.card ↥C.T = p := R101_card_T C
  set Y := Finset.univ.image (fun x : ↥(NG R1) => cj (x : G) C.h15.R) with hY
  -- basic facts about the members of `Y`
  have hmemY : ∀ A ∈ Y, A ≤ R1 ∧ C.T ≤ A ∧ Nat.card ↥A = p ^ 2 := by
    intro A hA
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hA
    rw [← hx]
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
      rw [← hzy]
      simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
        (Subgroup.mem_normalizer_iff.mp x.2 z).mp (C.hRR1 hz)
    · -- T ≤ cj x R
      have h1 : C.T = cj (x : G) C.T := (R101_cj_T C x.2).symm
      rw [h1]
      exact cj_le_cj (R101_T_le_R C)
    · rw [card_cj]; exact hRc
  have hdisj : ∀ A ∈ Y, ∀ A' ∈ Y, A ≠ A' → Disjoint
      ((Finset.univ.filter (fun y : G => y ∈ A)) \ (Finset.univ.filter (fun y : G => y ∈ C.T)))
      ((Finset.univ.filter (fun y : G => y ∈ A')) \ (Finset.univ.filter (fun y : G => y ∈ C.T))) := by
    intro A hA A' hA' hne
    obtain ⟨-, hTleA, hcardA⟩ := hmemY A hA
    obtain ⟨-, hTleA', hcardA'⟩ := hmemY A' hA'
    have hinter : A ⊓ A' = C.T := by
      have hTle : C.T ≤ A ⊓ A' := le_inf hTleA hTleA'
      have hdvd : Nat.card ↥(A ⊓ A') ∣ p ^ 2 := by
        rw [← hcardA]; exact Subgroup.card_dvd_of_le inf_le_left
      have hge : p ≤ Nat.card ↥(A ⊓ A') := by
        have h1 : Nat.card ↥C.T ∣ Nat.card ↥(A ⊓ A') := Subgroup.card_dvd_of_le hTle
        rw [hTc] at h1
        exact Nat.le_of_dvd Nat.card_pos h1
      have hne2 : Nat.card ↥(A ⊓ A') ≠ p ^ 2 := by
        intro hcon
        have hcA' : Nat.card ↥A ≤ Nat.card ↥(A ⊓ A') := by rw [hcardA, hcon]
        have hAeq : A ⊓ A' = A := Subgroup.eq_of_le_of_card_ge inf_le_left hcA'
        have hAleA' : A ≤ A' := by
          intro z hz
          have hz' : z ∈ A ⊓ A' := by rw [hAeq]; exact hz
          exact hz'.2
        have hcA'' : Nat.card ↥A' ≤ Nat.card ↥A := by rw [hcardA', hcardA]
        exact hne (Subgroup.eq_of_le_of_card_ge hAleA' hcA'')
      have hle2 : Nat.card ↥(A ⊓ A') ≤ p := by
        obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
        by_contra hgt
        have hk2 : k ≤ 2 := hk
        rcases (show k = 2 ∨ k ≤ 1 by omega) with h2 | h1
        · have hcon : Nat.card ↥(A ⊓ A') = p ^ 2 := by rw [hkeq, h2]
          exact hne2 hcon
        · have hcon : Nat.card ↥(A ⊓ A') ≤ p := by
            rw [hkeq]
            calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos h1
              _ = p := pow_one p
          exact absurd hcon hgt
      exact (Subgroup.eq_of_le_of_card_ge hTle
        (by rw [hTc, le_antisymm hle2 hge])).symm
    rw [Finset.disjoint_left]
    intro y hy hy'
    rw [Finset.mem_sdiff, Finset.mem_filter] at hy hy'
    obtain ⟨hyA, hyT⟩ := hy
    obtain ⟨hyA', -⟩ := hy'
    have hyc : y ∉ C.T := by
      intro hyct
      exact hyT (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hyct⟩)
    have hyinf : y ∈ A ⊓ A' := ⟨hyA.2, hyA'.2⟩
    rw [hinter] at hyinf
    exact hyc hyinf
  -- counting
  let fA : Subgroup G → Finset G :=
    fun A => (Finset.univ.filter (fun y : G => y ∈ A)) \ (Finset.univ.filter (fun y : G => y ∈ C.T))
  have hcardA : ∀ A ∈ Y, (fA A).card = p ^ 2 - p := by
    intro A hA
    obtain ⟨-, hTleA, hcardA⟩ := hmemY A hA
    have hsub : (Finset.univ.filter (fun y : G => y ∈ C.T)) ⊆
        (Finset.univ.filter (fun y : G => y ∈ A)) := by
      intro y hy
      rw [Finset.mem_filter] at hy ⊢
      exact ⟨Finset.mem_univ _, hTleA hy.2⟩
    show ((Finset.univ.filter (fun y : G => y ∈ A)) \
        (Finset.univ.filter (fun y : G => y ∈ C.T))).card = p ^ 2 - p
    rw [Finset.card_sdiff_of_subset hsub]
    have h2 : (Finset.univ.filter (fun y : G => y ∈ A)).card = Nat.card ↥A := by
      rw [← Fintype.card_subtype (fun y : G => y ∈ A), Nat.card_eq_fintype_card]
    have h3 : (Finset.univ.filter (fun y : G => y ∈ C.T)).card = Nat.card ↥C.T := by
      rw [← Fintype.card_subtype (fun y : G => y ∈ C.T), Nat.card_eq_fintype_card]
    rw [h2, h3, hcardA, hTc]
  have hF2card : (Finset.univ.filter (fun y : G => y ∈ R1 ∧ y ∉ C.T)).card = p ^ 3 - p := by
    have hsub : (Finset.univ.filter (fun y : G => y ∈ C.T)) ⊆
        (Finset.univ.filter (fun y : G => y ∈ R1)) := by
      intro y hy
      rw [Finset.mem_filter] at hy ⊢
      exact ⟨Finset.mem_univ _, R101_T_le_R1 C hy.2⟩
    have hpart : (Finset.univ.filter (fun y : G => y ∈ R1 ∧ y ∉ C.T)) =
        (Finset.univ.filter (fun y : G => y ∈ R1)) \ (Finset.univ.filter (fun y : G => y ∈ C.T)) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    rw [hpart, Finset.card_sdiff_of_subset hsub]
    have h2 : (Finset.univ.filter (fun y : G => y ∈ R1)).card = Nat.card ↥R1 := by
      rw [Nat.card_eq_fintype_card (α := ↥R1)]
      exact (Fintype.card_subtype (fun y : G => y ∈ R1)).symm
    have h3 : (Finset.univ.filter (fun y : G => y ∈ C.T)).card = Nat.card ↥C.T := by
      rw [Nat.card_eq_fintype_card (α := ↥C.T)]
      exact (Fintype.card_subtype (fun y : G => y ∈ C.T)).symm
    rw [h2, h3, C.hR1c, hTc]
  have hsubY : Y.biUnion fA ⊆ Finset.univ.filter (fun y : G => y ∈ R1 ∧ y ∉ C.T) := by
    intro y hy
    rw [Finset.mem_biUnion] at hy
    obtain ⟨A, hA, hyA⟩ := hy
    have hsubA : (Finset.univ.filter (fun y : G => y ∈ C.T)) ⊆
        (Finset.univ.filter (fun y : G => y ∈ A)) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨Finset.mem_univ _, (hmemY A hA).2.1 hz.2⟩
    have hyA' : y ∈ (Finset.univ.filter (fun z : G => z ∈ A)) \
        (Finset.univ.filter (fun z : G => z ∈ C.T)) := hyA
    rw [Finset.mem_sdiff, Finset.mem_filter] at hyA'
    obtain ⟨⟨-, hyA2⟩, hyT⟩ := hyA'
    have hyT' : y ∉ C.T := by
      intro hyct
      exact hyT (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hyct⟩)
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hmemY A hA).1 hyA2, hyT'⟩
  have hbij : (Y.biUnion fA).card = Y.card * (p ^ 2 - p) := by
    rw [Finset.card_biUnion]
    · rw [Finset.sum_congr rfl hcardA, Finset.sum_const, smul_eq_mul]
    · intro A hA A' hA' hne
      exact hdisj A hA A' hA' hne
  have hle : (Y.biUnion fA).card ≤
      (Finset.univ.filter (fun y : G => y ∈ R1 ∧ y ∉ C.T)).card :=
    Finset.card_le_card hsubY
  rw [hbij, hF2card] at hle
  -- conclude
  have hpos : 0 < p ^ 2 - p := by
    have h2 : p * 1 < p * p := Nat.mul_lt_mul_of_pos_left hp.one_lt hp.pos
    rw [mul_one, ← pow_two] at h2
    exact Nat.sub_pos_of_lt h2
  have hone : p ^ 3 - p = (p + 1) * (p ^ 2 - p) := by
    have h1 : p ^ 2 - p = p * (p - 1) := by rw [Nat.mul_sub_left_distrib, mul_one]; ring_nf
    rw [h1]
    have h2 : (p + 1) * (p * (p - 1)) = p ^ 3 - p := by
      rw [show (p + 1) * (p * (p - 1)) = (p + 1) * p * (p - 1) from by ring_nf,
        Nat.mul_sub_left_distrib, mul_one]
      rw [show (p + 1) * p * p = p ^ 3 + p ^ 2 from by ring_nf,
        show (p + 1) * p = p ^ 2 + p from by ring_nf,
        show p ^ 2 + p = p + p ^ 2 from by ring_nf]
      exact Nat.add_sub_add_right (p ^ 3) (p ^ 2) p
    exact h2.symm
  rw [hone] at hle
  exact Nat.le_of_mul_le_mul_right hle hpos

theorem R_weaklyClosed_101 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Work.ThmF.ChV3.Step11Out H Q t P h15.R T)
    (hm1 : h15.m = 1) (hsig : Work.ThmF.ChV3.Sig H t P = ⊥)
    (hGp : Work.ThmF.ChV3.pPart (Nat.card P) (Nat.card G) = Nat.card P ^ 3)
    (hcb : ∀ x ∈ Work.ThmF.ChV3.CQ Q P, x ≠ 1 → ∀ X : Subgroup G, IsPGroup (Nat.card P) X →
      X ≤ Subgroup.centralizer ({x} : Set G) → Nat.card X ≤ Nat.card P)
    (hNR : Nat.card ↥(Work.ThmF.ChV3.NG h15.R) = Nat.card P ^ 3 * (Nat.card P - 1))
    {R1 : Subgroup G} (hRR1 : h15.R ≤ R1) (hR1N : R1 ≤ Work.ThmF.ChV3.NG h15.R)
    (hR1c : Nat.card R1 = Nat.card P ^ 3) (hR1n : Work.ThmF.ChV3.NG h15.R ≤
      Work.ThmF.ChV3.NG R1) :
    ∀ g : G, Work.ThmF.ChV3.cj g h15.R ≤ R1 → Work.ThmF.ChV3.cj g h15.R = h15.R := by
  classical
  let C : R101Ctx H Q t s r P R1 :=
    ⟨hFT, hC4, c, h15, h7, hpf, T, h11, hm1, hsig, hGp, hcb, hNR, hRR1, hR1N, hR1c, hR1n⟩
  have hpP : (Nat.card P).Prime := C.c.P_prime
  have hRc : Nat.card ↥C.h15.R = Nat.card P ^ 2 := R101_card_R C
  have hTc : Nat.card ↥C.T = Nat.card P := R101_card_T C
  intro g hg
  have hgH : g ∈ NG R1 := R101_conj_le_imp_mem_ng C hg
  set Y := Finset.univ.image (fun x : ↥(NG R1) => cj (x : G) C.h15.R) with hY
  have hRY : C.h15.R ∈ Y := by
    rw [hY]
    exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp [cj_one]⟩
  -- `Y` is a singleton
  have hYcard : Y.card = 1 := by
    by_contra hne
    have hex : ∃ A ∈ Y, A ≠ C.h15.R := by
      by_contra hcon
      push_neg at hcon
      apply hne
      have hsub : Y ⊆ {C.h15.R} := by
        intro A hA
        rw [Finset.mem_singleton]
        exact hcon A hA
      have h1 : Y.card ≤ 1 := by simpa using Finset.card_le_card hsub
      have h2 : 1 ≤ Y.card := Finset.card_pos.mpr ⟨C.h15.R, hRY⟩
      omega
    obtain ⟨A, hAY, hAR⟩ := hex
    obtain ⟨x, hxH, hAx⟩ := by rw [hY] at hAY; exact Finset.mem_image.mp hAY
    have hxR : cj (x : G) C.h15.R ≠ C.h15.R := by rw [hAx]; exact hAR
    -- the orbit of `A` under `C_Q(P)`
    set Orb := Finset.univ.image (fun y : ↥(CQ Q P) => cj (y : G) A) with hOrb
    have hOrb_card : Orb.card = Nat.card P - 1 := by
      rw [hOrb, Finset.card_image_of_injOn]
      · simpa [Finset.card_univ] using R101_card_C C
      · intro y _ y' _ heq
        set cc : ↥(CQ Q P) :=
          ⟨(y' : G)⁻¹ * (y : G), (CQ Q P).mul_mem ((CQ Q P).inv_mem y'.2) y.2⟩ with hcc
        have hccA : cj (cc : G) A = A := by
          have h2 := congrArg (fun z => cj ((y' : G)⁻¹) z) heq
          rw [cj_mul, cj_mul, inv_mul_cancel, cj_one] at h2
          exact h2
        have hcc1 : cc = 1 := by
          by_contra hcne
          rw [← hAx] at hccA
          exact R101_semireg C (x : G) x.2 hxR (cc : G) cc.2
            (fun h => hcne (Subtype.ext h)) hccA
        have hval : (y' : G)⁻¹ * (y : G) = 1 := congrArg Subtype.val hcc1
        have hyy : (y : G) = (y' : G) := by
          have := congrArg (fun z => (y' : G) * z) hval
          simpa using this
        exact Subtype.ext hyy
    have hOrb_sub : Orb ⊆ Y.erase C.h15.R := by
      intro B hB
      rw [hOrb] at hB
      obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hB
      rw [Finset.mem_erase]
      constructor
      · rw [← hy]
        intro hBR
        have h2 : A = C.h15.R := by
          have h3 := congrArg (fun z => cj ((y : G)⁻¹) z) hBR
          rw [cj_mul, inv_mul_cancel, cj_one] at h3
          have hyR : cj ((y : G)⁻¹) C.h15.R = C.h15.R :=
            (cj_self_iff ((y : G)⁻¹) C.h15.R).mpr ((NG C.h15.R).inv_mem (C.h15.hRn y.2.2))
          rw [hyR] at h3
          exact h3
        exact absurd h2 hAR
      · rw [hY]
        refine Finset.mem_image.mpr ⟨⟨(y : G) * (x : G),
          (NG R1).mul_mem (C.hR1n (C.h15.hRn y.2.2)) x.2⟩, Finset.mem_univ _, ?_⟩
        show cj ((y : G) * (x : G)) C.h15.R = B
        rw [← cj_mul, hAx]
        exact hy
    have hYge : Nat.card P ≤ Y.card := by
      have h1 : Orb.card ≤ (Y.erase C.h15.R).card := Finset.card_le_card hOrb_sub
      rw [hOrb_card, Finset.card_erase_of_mem hRY] at h1
      have h2 : 1 ≤ Y.card := Finset.card_pos.mpr ⟨C.h15.R, hRY⟩
      omega
    have hYle : Y.card ≤ Nat.card P + 1 := R101_orbit_le C
    have hYndvd : ¬ Nat.card P ∣ Y.card := R101_p_not_dvd_orbit C
    have hYeq : Y.card = Nat.card P + 1 := by
      have h2 : Y.card ≠ Nat.card P := fun h => hYndvd (h ▸ dvd_refl (Nat.card P))
      rcases lt_or_eq_of_le hYle with h1 | h1
      · exact absurd (by omega : Y.card = Nat.card P) h2
      · exact h1
    have hZcard : (Y.erase C.h15.R).card = Nat.card P := by
      rw [Finset.card_erase_of_mem hRY, hYeq]
      omega
    have hpos : 0 < ((Y.erase C.h15.R) \ Orb).card := by
      rw [Finset.card_sdiff_of_subset hOrb_sub, hZcard, hOrb_card,
        Nat.sub_sub_self (m := 1) Nat.card_pos]
      exact Nat.one_pos
    obtain ⟨A', hA'⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_sdiff] at hA'
    obtain ⟨hA'Z, hA'Orb⟩ := hA'
    rw [Finset.mem_erase] at hA'Z
    obtain ⟨hA'R, hA'Y⟩ := hA'Z
    obtain ⟨x', hx'H, hAx'⟩ := by rw [hY] at hA'Y; exact Finset.mem_image.mp hA'Y
    have hx'R : cj (x' : G) C.h15.R ≠ C.h15.R := by rw [hAx']; exact hA'R
    have hOrb'_sub : Finset.univ.image (fun y : ↥(CQ Q P) => cj (y : G) A') ⊆
        (Y.erase C.h15.R) \ Orb := by
      intro B hB
      obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hB
      rw [Finset.mem_sdiff]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_erase]
        constructor
        · rw [← hy]
          intro hBR
          have h2 : A' = C.h15.R := by
            have h3 := congrArg (fun z => cj ((y : G)⁻¹) z) hBR
            rw [cj_mul, inv_mul_cancel, cj_one] at h3
            have hyR : cj ((y : G)⁻¹) C.h15.R = C.h15.R :=
              (cj_self_iff ((y : G)⁻¹) C.h15.R).mpr ((NG C.h15.R).inv_mem (C.h15.hRn y.2.2))
            rw [hyR] at h3
            exact h3
          exact absurd h2 hA'R
        · rw [hY]
          refine Finset.mem_image.mpr ⟨⟨(y : G) * (x' : G),
            (NG R1).mul_mem (C.hR1n (C.h15.hRn y.2.2)) x'.2⟩, Finset.mem_univ _, ?_⟩
          show cj ((y : G) * (x' : G)) C.h15.R = B
          rw [← cj_mul, hAx']
          exact hy
      · rw [← hy]
        intro hmem
        rw [hOrb] at hmem hA'Orb
        obtain ⟨y', -, hy'⟩ := Finset.mem_image.mp hmem
        refine hA'Orb (Finset.mem_image.mpr ⟨⟨(y : G)⁻¹ * (y' : G),
          (CQ Q P).mul_mem ((CQ Q P).inv_mem y.2) y'.2⟩, Finset.mem_univ _, ?_⟩)
        show cj ((y : G)⁻¹ * (y' : G)) A = A'
        rw [← cj_mul, hy', cj_mul, inv_mul_cancel, cj_one]
    have hOrb'_card : (Finset.univ.image (fun y : ↥(CQ Q P) => cj (y : G) A')).card
        = Nat.card P - 1 := by
      rw [Finset.card_image_of_injOn]
      · simpa [Finset.card_univ] using R101_card_C C
      · intro y _ y' _ heq
        set cc : ↥(CQ Q P) :=
          ⟨(y' : G)⁻¹ * (y : G), (CQ Q P).mul_mem ((CQ Q P).inv_mem y'.2) y.2⟩ with hcc
        have hccA : cj (cc : G) A' = A' := by
          have h2 := congrArg (fun z => cj ((y' : G)⁻¹) z) heq
          rw [cj_mul, cj_mul, inv_mul_cancel, cj_one] at h2
          exact h2
        have hcc1 : cc = 1 := by
          by_contra hcne
          rw [← hAx'] at hccA
          exact R101_semireg C (x' : G) x'.2 hx'R (cc : G) cc.2
            (fun h => hcne (Subtype.ext h)) hccA
        have hval : (y' : G)⁻¹ * (y : G) = 1 := congrArg Subtype.val hcc1
        have hyy : (y : G) = (y' : G) := by
          have := congrArg (fun z => (y' : G) * z) hval
          simpa using this
        exact Subtype.ext hyy
    have hcontra : Nat.card P - 1 ≤ 1 := by
      have h1 : (Finset.univ.image (fun y : ↥(CQ Q P) => cj (y : G) A')).card
          ≤ ((Y.erase C.h15.R) \ Orb).card := Finset.card_le_card hOrb'_sub
      rw [hOrb'_card, Finset.card_sdiff_of_subset hOrb_sub, hZcard, hOrb_card] at h1
      rw [Nat.sub_sub_self (m := 1) Nat.card_pos] at h1
      exact h1
    have hne2 : Nat.card P ≠ 2 := R101_p_odd C
    have hp2 : 2 ≤ Nat.card P := hpP.two_le
    omega
  -- conclude
  have hmem : cj g C.h15.R ∈ Y := by
    rw [hY]
    exact Finset.mem_image.mpr ⟨⟨g, hgH⟩, Finset.mem_univ _, rfl⟩
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hYcard
  have h1 : cj g C.h15.R = a := by
    have := hmem
    rw [ha] at this
    simpa using this
  have h2 : C.h15.R = a := by
    have := hRY
    rw [ha] at this
    simpa using this
  rw [h1, h2]

end Work.ThmF.ChV3.Prove
