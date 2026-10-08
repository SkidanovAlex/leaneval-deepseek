import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain15
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.ChV3.Prove.L_facts
import Submission.Work.ThmF.ChV3.Prove.S4_centD_not_stronglyReal
import Submission.Work.ThmF.ChV3.Prove.S5_cst_inf_cs
import Submission.Work.ThmF.ChV3.Prove.cent_Kelem_order3_mem_W
import Submission.Work.ThmF.ChV3.Prove.exists_inverted_of_prime_dvd
import Submission.Work.ThmF.ChV3.Prove.Kset_card_seven
import Submission.Work.ThmF.ChV3.Prove.card_sup_of_le_normalizer
import Submission.Work.ThmF.ChV12.lemma4
import Submission.Work.ThmF.ChV12.X5isoPSL2_of
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.card_projectiveSpecialLinearGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.cst_isPGroup` — Peterfalvi II Ch. V §3, step (13)

`C_G(Z₁) = C_G(st)` is a `3`-group (the Sylow `3`-subgroup `R₂` of step (14)).

The proof follows the source (Ch. V §3, step (13)):

* `st = s · t` is a product of two involutions and has order `3 ≠ 1`, so `ChV12.lemma4` gives
  that `|C_G(st)|` is **odd**;
* `s` inverts `st` (`s (st) s⁻¹ = t s = (st)⁻¹`), so `s` normalises `C_G(st)`; moreover
  `C_G(st) ⊓ C_G(s) = V` (`S5_cst_inf_cs`) is a `3`-group (`|V| = 3|W|`, `centD_isPGroup`);
* if `p ≠ 3` is a prime divisor of `|C_G(st)|`, the coprime action of `s` produces
  `x ∈ C_G(st)` of order `p` inverted by `s` (`exists_inverted_of_prime_dvd`), hence strongly
  real; `ChV12.lemma4` conjugates `x` to `u t ∈ X₅` (`u ∈ Q₀^#`), and since `|X₅| = 504`
  (`X5_card_eq_504`) we get `p = 7`;
* `X₅` has exactly one class of subgroups of order `7` (`∃ 7² ∤ 504`, `K` is one of them), so a
  conjugate `k` of `x` lies in `K^#` (`exists_conj_mem_Kset_of_orderOf_seven`); then `(st)`'s
  corresponding conjugate `y` centralises `k`, has order `3`, and so lies in `W` (13b,
  `cent_Kelem_order3_mem_W`).  But `y` is strongly real and `W ≤ V`, contradicting `S4`
  (`S4_centD_not_stronglyReal`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3.Prove

open LeanEval.GroupTheory.Defs

variable {G : Type} [Group G] [Finite G]

/-! ## Elementary transport lemmas -/

/-- `StronglyReal` is preserved by conjugation. -/
theorem stronglyReal_conj {x g : G} (h : Work.ThmF.ChV3.StronglyReal x) :
    Work.ThmF.ChV3.StronglyReal (g * x * g⁻¹) := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  refine ⟨g * a * g⁻¹, g * b * g⁻¹, ?_, ?_, ?_⟩
  · rw [show (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ by group, ha]
    group
  · rw [show (g * b * g⁻¹) * (g * b * g⁻¹) = g * (b * b) * g⁻¹ by group, hb]
    group
  · rw [show (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ by group, hab]

/-- `C_G({x⁻¹}) = C_G({x})`. -/
theorem centralizer_singleton_inv (x : G) :
    Subgroup.centralizer ({x⁻¹} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hc : Commute y x⁻¹ := h
    have h' : Commute y x⁻¹⁻¹ := hc.inv_right
    have h'' := h'.eq
    simpa using h''
  · intro h
    have hc : Commute y x := h
    exact (hc.inv_right : Commute y x⁻¹).eq

/-! ## Generic Sylow conjugacy of subgroups of order `p` -/

/-- Two subgroups of a finite group `N` of the same prime order `p` are conjugate as soon as
`p ^ 2 ∤ |N|` (each of them is then a Sylow `p`-subgroup). -/
theorem exists_conj_of_card_eq_prime {N : Type} [Group N] [Finite N] {p : ℕ} (hp : p.Prime)
    {A B : Subgroup N} (hA : Nat.card ↥A = p) (hB : Nat.card ↥B = p)
    (hdiv : ¬ p ^ 2 ∣ Nat.card N) :
    ∃ g : N, A.map (MulAut.conj g).toMonoidHom = B := by
  classical
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hAp : IsPGroup p ↥A := IsPGroup.of_card (n := 1) (by rw [hA, pow_one])
  have hBp : IsPGroup p ↥B := IsPGroup.of_card (n := 1) (by rw [hB, pow_one])
  obtain ⟨S, hAS⟩ := IsPGroup.exists_le_sylow hAp
  obtain ⟨T, hBT⟩ := IsPGroup.exists_le_sylow hBp
  have hS : (S : Subgroup N) = A := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
    have hkS : Nat.card ↥(S : Subgroup N) = p ^ k := hk
    have hpdvd : p ∣ Nat.card ↥(S : Subgroup N) := by
      have h := Subgroup.card_dvd_of_le hAS
      rwa [hA] at h
    have hp2 : ¬ p ^ 2 ∣ Nat.card ↥(S : Subgroup N) := fun h =>
      hdiv (h.trans (Subgroup.card_subgroup_dvd_card (S : Subgroup N)))
    have hk_le : k ≤ 1 := by
      by_contra h
      push_neg at h
      exact hp2 (by rw [hkS]; exact Nat.pow_dvd_pow p (by omega : 2 ≤ k))
    have hk_ge : 1 ≤ k := by
      by_contra h
      push_neg at h
      have hk0 : k = 0 := by omega
      rw [hk0, pow_zero] at hkS
      have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num : 0 < 1) (hkS ▸ hpdvd)
      have h2 := hp.two_le
      omega
    have hk1 : k = 1 := by omega
    have hcardS : Nat.card ↥(S : Subgroup N) = p := by rw [hkS, hk1, pow_one]
    exact (Subgroup.eq_of_le_of_card_ge hAS (by rw [hA, hcardS])).symm
  have hT : (T : Subgroup N) = B := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp T.isPGroup'
    have hkT : Nat.card ↥(T : Subgroup N) = p ^ k := hk
    have hpdvd : p ∣ Nat.card ↥(T : Subgroup N) := by
      have h := Subgroup.card_dvd_of_le hBT
      rwa [hB] at h
    have hp2 : ¬ p ^ 2 ∣ Nat.card ↥(T : Subgroup N) := fun h =>
      hdiv (h.trans (Subgroup.card_subgroup_dvd_card (T : Subgroup N)))
    have hk_le : k ≤ 1 := by
      by_contra h
      push_neg at h
      exact hp2 (by rw [hkT]; exact Nat.pow_dvd_pow p (by omega : 2 ≤ k))
    have hk_ge : 1 ≤ k := by
      by_contra h
      push_neg at h
      have hk0 : k = 0 := by omega
      rw [hk0, pow_zero] at hkT
      have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num : 0 < 1) (hkT ▸ hpdvd)
      have h2 := hp.two_le
      omega
    have hk1 : k = 1 := by omega
    have hcardT : Nat.card ↥(T : Subgroup N) = p := by rw [hkT, hk1, pow_one]
    exact (Subgroup.eq_of_le_of_card_ge hBT (by rw [hB, hcardT])).symm
  haveI : Finite (Sylow p N) := .of_injective (fun P : Sylow p N => (P : Subgroup N))
    (fun _ _ h => Sylow.ext h)
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := N) S T
  have hcoe : (T : Subgroup N) = (S : Subgroup N).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.smul_def]
    rfl
  rw [hS, hT] at hcoe
  exact ⟨g, hcoe.symm⟩

/-! ## The pieces of step (13) -/

/-- `|X₅| = |PSL(2,8)| = 504` in case (10-2): `X₅ ≅ PSL(2,2ⁿ)` with `2ⁿ = |Q₀| = 2³`. -/
theorem X5_card_eq_504 {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    Nat.card ↥(Work.ThmF.Lemma5.X5 H t) = 504 := by
  classical
  have h5 : Work.ThmF.Lemma5.Hyp5 H Q t s :=
    { sit := c.sit, split := c.split, s_mem := c.s_mem, s_inv := c.s_inv, ord3 := d.f3 }
  obtain ⟨n, _hn, hcard, ⟨Φ⟩⟩ := Work.ThmF.ChV12.X5isoPSL2_of hFT hC4 h5
  have hQ0 : Nat.card ↥(Work.ThmF.Q0sub H) = 8 := by
    rw [h15.hQ0, d.p3]
    norm_num
  have hn3 : n = 3 := by
    have h : 2 ^ n = 2 ^ 3 := by rw [← hcard, hQ0]; norm_num
    exact Nat.pow_right_injective (by norm_num : 1 < 2) h
  have hpsl : Nat.card (PSL2Model n) = 504 := by
    rw [hn3]
    haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
    have hchar : CharP (GaloisField 2 3) 2 := inferInstance
    rw [Commons.GroupTheory.SL2.card_projectiveSpecialLinearGroup (F := GaloisField 2 3) hchar,
      GaloisField.card (p := 2) (n := 3) (by omega)]
    norm_num
  rw [Nat.card_congr Φ.toEquiv, hpsl]

/-- `V = C_D(t)` is a `3`-group: `V = W ⋊ P` with `|W| ∈ {3, 9}` and `|P| = 3`. -/
theorem centD_isPGroup {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hC4 : Submission.Blueprint.ChIIFourProp) (c : Work.ThmF.ChV3.CtxF H Q t s r P)
    (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P) (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    IsPGroup 3 ↥(Submission.Blueprint.centD H t) := by
  have hNW : P ≤ Subgroup.normalizer (Work.ThmF.W H t : Set G) :=
    Work.ThmF.ChV3.le_normalizer_W hC4 c
  have hcard : Nat.card ↥(Submission.Blueprint.centD H t) =
      Nat.card ↥(Work.ThmF.W H t) * 3 := by
    rw [← h15.hV, card_sup_of_le_normalizer hNW h15.hWP, d.p3]
  rcases d.W39 with h | h
  · exact IsPGroup.of_card (n := 2) (by rw [hcard, h]; norm_num)
  · exact IsPGroup.of_card (n := 3) (by rw [hcard, h]; norm_num)

/-- In `X₅` (`|X₅| = 504`), every element of order `7` is conjugate into `K^# = Ksub`. -/
theorem exists_conj_mem_Kset_of_orderOf_seven {H : Subgroup G} {t : G}
    (hX : Nat.card ↥(Work.ThmF.Lemma5.X5 H t) = 504)
    (hK : Nat.card ↥(Work.ThmF.Ksub H t) = 7)
    (hKset : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t)
    {w : G} (hw : w ∈ Work.ThmF.Lemma5.X5 H t) (hord : orderOf w = 7) :
    ∃ h ∈ Work.ThmF.Lemma5.X5 H t, h * w * h⁻¹ ∈ Work.ThmF.Kset H t := by
  classical
  have hKle : Work.ThmF.Ksub H t ≤ Work.ThmF.Lemma5.X5 H t := by
    rw [Work.ThmF.Ksub, Work.ThmF.Lemma5.X5]
    exact Subgroup.closure_mono (fun x hx => Or.inl (Or.inr hx))
  have hKcard' : Nat.card ↥((Work.ThmF.Ksub H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)) = 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv, hK]
  have hAcard :
      Nat.card ↥(Subgroup.zpowers (⟨w, hw⟩ : ↥(Work.ThmF.Lemma5.X5 H t))) = 7 := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe (⟨w, hw⟩ : ↥(Work.ThmF.Lemma5.X5 H t))]
    simpa using hord
  have hdiv : ¬ 7 ^ 2 ∣ Nat.card ↥(Work.ThmF.Lemma5.X5 H t) := by rw [hX]; norm_num
  obtain ⟨g, hg⟩ := exists_conj_of_card_eq_prime (N := ↥(Work.ThmF.Lemma5.X5 H t))
    Nat.prime_seven hAcard hKcard' hdiv
  refine ⟨(g : G), g.2, ?_⟩
  have hmem : (MulAut.conj g) (⟨w, hw⟩ : ↥(Work.ThmF.Lemma5.X5 H t))
      ∈ (Work.ThmF.Ksub H t).subgroupOf (Work.ThmF.Lemma5.X5 H t) := by
    rw [← hg]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers _)
  rw [Subgroup.mem_subgroupOf] at hmem
  have hcoe : (((MulAut.conj g) (⟨w, hw⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) :
      ↥(Work.ThmF.Lemma5.X5 H t)) : G) = (g : G) * w * (g : G)⁻¹ := by
    rw [MulAut.conj_apply]
    rfl
  rw [hcoe] at hmem
  rw [← hKset]
  exact hmem

/-! ## Step (13) -/

theorem cst_isPGroup {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    IsPGroup 3 ↥(Work.ThmF.ChV3.Cst s t) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  -- ## the two involutions `s`, `t`
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [c.s_inv] at h
    simpa [pow_two] using h
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [c.split.invol] at h
    simpa [pow_two] using h
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  -- ## (1) `|C_G(st)|` is odd (`ChV12.lemma4` applied to the strongly real `s · t`)
  have hst2ne : (s * t) * (s * t) ≠ 1 := by
    intro h
    have hdvd : orderOf (s * t) ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      exact h
    rw [d.f3] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hoddC : Odd (Nat.card ↥(Work.ThmF.ChV3.Cst s t)) := by
    have h := (Work.ThmF.ChV12.lemma4 c.sit hC4 H Q t c.split (s * t) hst2ne
      ⟨s, t, hs2, ht2, rfl⟩).2
    simpa [Work.ThmF.ChV3.Cst] using h
  -- ## (2) `s` normalises `C_G(st)` (`s` inverts `st`)
  have hsN : s ∈ Work.ThmF.ChV3.NG (Work.ThmF.ChV3.Cst s t) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 := Work.ThmF.ChV12.map_centralizer_singleton (MulAut.conj s) (s * t)
    have hconj : (MulAut.conj s) (s * t) = (s * t)⁻¹ := by
      rw [MulAut.conj_apply, mul_inv_rev, inv_eq_of_mul_eq_one_right hs2,
        inv_eq_of_mul_eq_one_right ht2, ← mul_assoc s s t, hs2, one_mul]
    show Subgroup.map (MulAut.conj s).toMonoidHom (Work.ThmF.ChV3.Cst s t)
      = Work.ThmF.ChV3.Cst s t
    rw [h1, hconj]
    exact centralizer_singleton_inv (s * t)
  -- ## (3) `C_G(st) ⊓ C_G(s) = V` is a `3`-group
  have hV3 : IsPGroup 3 ↥(Submission.Blueprint.centD H t) := centD_isPGroup hC4 c h15 d
  -- ## every prime divisor of `|C_G(st)|` is `3`
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥(Work.ThmF.ChV3.Cst s t) → p = 3 := by
    intro p hp hpdiv
    by_contra hp3
    have hpV : ¬ p ∣ Nat.card ↥(Work.ThmF.ChV3.Cst s t ⊓
        Subgroup.centralizer ({s} : Set G)) := by
      rw [S5_cst_inf_cs c]
      intro hdiv
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV3
      rw [hk] at hdiv
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hdiv))
    obtain ⟨x, hxX, hxord, hxs⟩ :=
      exists_inverted_of_prime_dvd (X := Work.ThmF.ChV3.Cst s t) (u := s)
        (by simpa using hoddC) c.s_inv hsN hp hpdiv hpV
    -- `x` is strongly real, of order `p ≠ 2`
    have hpodd : Odd p := hoddC.of_dvd_nat hpdiv
    have hx_ne1 : x ≠ 1 := fun h => hp.ne_one (by rw [← hxord, h, orderOf_one])
    have hx2 : x * x ≠ 1 := by
      intro h
      have hdvd : orderOf x ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one, pow_two]
        exact h
      rw [hxord] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact hp.ne_one h1
      · rw [h2] at hpodd
        exact absurd hpodd (by decide)
    have hsr_x : ∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = x := by
      refine ⟨x * s, s, ?_, hs2, by rw [mul_assoc, hs2, mul_one]⟩
      have hsx : s * x * s = x⁻¹ := by simpa [hs_inv] using hxs
      calc (x * s) * (x * s) = x * (s * x * s) := by group
        _ = x * x⁻¹ := by rw [hsx]
        _ = 1 := mul_inv_cancel x
    -- `x` is conjugate to `u * t ∈ X₅`, of order `p`
    obtain ⟨ug, hugQ0, _hug1, g, hgx⟩ :=
      (Work.ThmF.ChV12.lemma4 c.sit hC4 H Q t c.split x hx2 hsr_x).1
    have hugt_X5 : ug * t ∈ Work.ThmF.Lemma5.X5 H t :=
      (Work.ThmF.Lemma5.X5 H t).mul_mem (Work.ThmF.Lemma5.Q0_subset_X5 H t hugQ0)
        (Work.ThmF.Lemma5.t_mem_X5 H t)
    have hugt_ord : orderOf (ug * t) = p := by
      rw [← hgx, Work.ThmF.Bender.orderOf_conj_eq, hxord]
    -- hence `p = 7`, since `|X₅| = 504` and `p ∉ {2, 3}`
    have hX504 : Nat.card ↥(Work.ThmF.Lemma5.X5 H t) = 504 := X5_card_eq_504 hFT hC4 c h15 d
    have hp7 : p = 7 := by
      have hdvd : p ∣ Nat.card ↥(Work.ThmF.Lemma5.X5 H t) := by
        rw [← hugt_ord]
        exact Subgroup.orderOf_dvd_natCard _ hugt_X5
      rw [hX504] at hdvd
      have h504 : (504 : ℕ) = 2 ^ 3 * 3 ^ 2 * 7 := by norm_num
      rw [h504] at hdvd
      rcases hp.dvd_mul.mp hdvd with h | h
      · rcases hp.dvd_mul.mp h with h2 | h2
        · have h2' : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
            (hp.dvd_of_dvd_pow h2)
          rw [h2'] at hpodd
          exact absurd hpodd (by decide)
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
            (hp.dvd_of_dvd_pow h2)) hp3
      · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp h
    -- a conjugate `k` of `x` lies in `K^#`
    obtain ⟨hKsub_set, -, hKsub_card, -⟩ := Kset_card_seven hFT hC4 c h15 d
    obtain ⟨h, _hhX5, hk_mem⟩ :=
      exists_conj_mem_Kset_of_orderOf_seven hX504 hKsub_card hKsub_set hugt_X5
        (by rw [hugt_ord, hp7])
    -- `k = (h*g) x (h*g)⁻¹ ∈ K^#`, and `y = (h*g) (st) (h*g)⁻¹` centralises it of order `3`
    have hkx : (h * g) * x * (h * g)⁻¹ ∈ Work.ThmF.Kset H t := by
      have : (h * g) * x * (h * g)⁻¹ = h * (ug * t) * h⁻¹ := by rw [← hgx]; group
      rw [this]
      exact hk_mem
    have hk_ne1 : (h * g) * x * (h * g)⁻¹ ≠ 1 := by
      intro h1
      have h2 : orderOf ((h * g) * x * (h * g)⁻¹) = 1 := by rw [h1, orderOf_one]
      rw [Work.ThmF.Bender.orderOf_conj_eq, hxord] at h2
      exact hp.ne_one h2
    have hyord3 : orderOf ((h * g) * (s * t) * (h * g)⁻¹) = 3 := by
      rw [Work.ThmF.Bender.orderOf_conj_eq, d.f3]
    have hy_cent : ((h * g) * (s * t) * (h * g)⁻¹) ∈
        Subgroup.centralizer ({(h * g) * x * (h * g)⁻¹} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxcomm : x * (s * t) = (s * t) * x :=
        Subgroup.mem_centralizer_singleton_iff.mp hxX
      calc ((h * g) * (s * t) * (h * g)⁻¹) * ((h * g) * x * (h * g)⁻¹)
          = (h * g) * ((s * t) * x) * (h * g)⁻¹ := by group
        _ = (h * g) * (x * (s * t)) * (h * g)⁻¹ := by rw [hxcomm]
        _ = ((h * g) * x * (h * g)⁻¹) * ((h * g) * (s * t) * (h * g)⁻¹) := by group
    have hyW : ((h * g) * (s * t) * (h * g)⁻¹) ∈ Work.ThmF.W H t :=
      cent_Kelem_order3_mem_W hFT hC4 c h15 d _ hkx hk_ne1 _ hy_cent hyord3
    -- but `y` is strongly real and lies in `V`, contradicting `S4`
    have hyV : ((h * g) * (s * t) * (h * g)⁻¹) ∈ Submission.Blueprint.centD H t :=
      Work.ThmF.W_le_centD H t hyW
    have hy_ne1 : ((h * g) * (s * t) * (h * g)⁻¹) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hyord3
      exact absurd hyord3 (by norm_num)
    have hy_sr : Work.ThmF.ChV3.StronglyReal ((h * g) * (s * t) * (h * g)⁻¹) :=
      stronglyReal_conj (g := h * g) ⟨s, t, hs2, ht2, rfl⟩
    exact (S4_centD_not_stronglyReal hC4 c ((h * g) * (s * t) * (h * g)⁻¹) hyV hy_ne1 1)
      (by simpa using hy_sr)
  -- ## hence `|C_G(st)|` is a power of `3`
  haveI : Nonempty ↥(Work.ThmF.ChV3.Cst s t) :=
    ⟨⟨1, (Work.ThmF.ChV3.Cst s t).one_mem⟩⟩
  have hcardC : Nat.card ↥(Work.ThmF.ChV3.Cst s t) =
      3 ^ (Nat.card ↥(Work.ThmF.ChV3.Cst s t)).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd (p := 3) Nat.card_pos.ne'
      (fun {d} hd hdd => hprime d hd hdd)
  exact IsPGroup.of_card hcardC

end Work.ThmF.ChV3.Prove
