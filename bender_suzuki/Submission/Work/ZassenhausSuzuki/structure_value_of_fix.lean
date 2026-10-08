import Mathlib
import Submission.Work.ZassenhausSuzuki.frel_center
import Submission.Work.ZassenhausSuzuki.suzukiFProp
import Submission.Work.ZassenhausSuzuki.TitsAux
import Submission.Work.ZassenhausSuzuki.odd_m_of_isTitsTheta
import Submission.Work.ZassenhausSuzuki.orderOf_ringAut_eq_of_fix
import Submission.Work.ZassenhausSuzuki.not_three_dvd_card_G_of_odd
import Submission.Work.ZassenhausSuzuki.crux_structure_value

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.structure_value_of_fix`

The value of the structure element `ρ` of the structure identity `t s t = ρ t ρ⁻¹`
(Peterfalvi II Ch. V §2 Lemma 1 b)) in the coordinates `e : Q ≃* A(K,θ)` of a split
rank-one Zassenhaus configuration: `ρ` lies in the `Λ`-orbit of `⟨1,0⟩` or of `⟨1,1⟩`,
i.e. in the coordinates `e ρ = ⟨a,b⟩` one has `a ≠ 0` and `b ∈ {0, a·θa}`.

This is the "11.12 argument" of HB III XI §11 (the `p ∈ {0,1}` half of
`Work.ZassenhausSuzuki.structure_value`), for which the hypothesis `hfix` (`Fix θ = 𝔽₂`)
is used through the surjectivity of `λ ↦ (1+λ)/(1+θλ)` on `K ∖ {0,1}`.  The remaining
input is HB XI 11.11 (b), delegated as `Work.ZassenhausSuzuki.crux_structure_value`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-! ## General helpers -/

/-- `t` is an involution. -/
lemma sv_t_mul_self (hsplit : IsSplitRankOne H Q t) : t * t = 1 := ht_mul_self hsplit

/-- Elements of the root group commuting with `t` are trivial (`Q ⊓ Q^t = 1`). -/
lemma sv_centralizer_triv (hsplit : IsSplitRankOne H Q t) {q : G} (hq : q ∈ Q)
    (h : q * t * q⁻¹ = t) : q = 1 := by
  have ht2 : t * t = 1 := sv_t_mul_self hsplit
  have hcomm : q * t = t * q := by
    calc q * t = (q * t * q⁻¹) * q := by group
      _ = t * q := by rw [h]
  have htqt : t * q * t = q := by
    calc t * q * t = t * (q * t) := by rw [mul_assoc]
      _ = t * (t * q) := by rw [hcomm]
      _ = (t * t) * q := by rw [mul_assoc]
      _ = q := by rw [ht2, one_mul]
  have hconj : q ∈ conj t H := by
    refine Subgroup.mem_map.mpr ⟨q, hsplit.le hq, ?_⟩
    show t * q * t⁻¹ = q
    rw [inv_eq_of_mul_eq_one_right ht2]
    exact htqt
  have hmem : q ∈ twoPoint H t := ⟨hsplit.le hq, hconj⟩
  have : q ∈ Q ⊓ twoPoint H t := ⟨hq, hmem⟩
  rw [hsplit.inf_eq] at this
  exact Subgroup.mem_bot.mp this

/-- `m` is odd: from `hfix` the fixed field of `θ` is `𝔽₂`, so `orderOf θ = m`. -/
theorem sv_odd_m {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1)
    (hθodd : Odd (orderOf θ))
    (hfix : ∀ x : GaloisField 2 m, θ x = x → x = 0 ∨ x = 1) : Odd m := by
  have hm : 1 ≤ m := by
    by_contra h
    push_neg at h
    have hm0 : m = 0 := by omega
    subst hm0
    refine hθ1 (RingEquiv.ext fun x => ?_)
    haveI : Fintype (GaloisField 2 0) := Fintype.ofFinite _
    have hcard : Fintype.card (GaloisField 2 0) = 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact card_galoisField_two_zero
    have h01 : x = 0 ∨ x = 1 := by
      have hmem : x ∈ ({0, 1} : Finset (GaloisField 2 0)) := by
        have hc : ({0, 1} : Finset (GaloisField 2 0)).card =
            Fintype.card (GaloisField 2 0) := by
          rw [hcard, Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
        rw [Finset.eq_univ_of_card _ hc]
        exact Finset.mem_univ x
      simpa using hmem
    rcases h01 with h | h <;> simp [h]
  rw [← orderOf_ringAut_eq_of_fix hm θ hfix]
  exact hθodd

/-- `3 ∤ |G|` in our configuration. -/
theorem sv_three_not_dvd (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) {m : ℕ} (hm : Odd m)
    {θ : GaloisField 2 m ≃+* GaloisField 2 m}
    {e : Q ≃* SzA (GaloisField 2 m) θ} : ¬ 3 ∣ Nat.card G :=
  not_three_dvd_card_G_of_odd (e := e) hsplit hzass h2 hm

/-! ## The first coordinate of the structure element -/

/-- **The first coordinate of `e ρ` is non-zero.**  If `(e ρ).a = 0` then `ρ` is an
involution commuting with `t`, hence `ρ = s`, and then `s t` has order `3`, so
`3 ∣ |G|`, contradicting `sv_three_not_dvd`. -/
theorem sv_a_ne_zero (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m}
    (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ))
    (hfix : ∀ x : GaloisField 2 m, θ x = x → x = 0 ∨ x = 1)
    {e : Q ≃* SzA (GaloisField 2 m) θ} :
    (e ⟨(structPair hsplit).2, (structPair_spec hsplit).2.2.1⟩).a ≠ 0 := by
  intro ha
  set ρ : G := (structPair hsplit).2 with hρdef
  set s : G := (structPair hsplit).1 with hsdef
  obtain ⟨hsQ, hs2, hρQ, hstruct⟩ := structPair_spec hsplit
  have ht2 : t * t = 1 := sv_t_mul_self hsplit
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hstruct' : t * s * t = ρ * t * ρ⁻¹ := by simpa [hti] using hstruct
  -- `ρ ^ 2 = 1`
  have hρ2 : ρ * ρ = 1 := by
    have ha' : (e ⟨ρ, hρQ⟩ : SzA (GaloisField 2 m) θ).a = 0 := ha
    have he2 : (e ⟨ρ, hρQ⟩ : SzA (GaloisField 2 m) θ) ^ 2 = 1 := by
      rw [pow_two, SzA.sq_eq]
      ext <;> simp [ha']
    have hq2 : (⟨ρ, hρQ⟩ : Q) * ⟨ρ, hρQ⟩ = 1 := by
      apply e.injective
      rw [map_mul, map_one]
      simpa [pow_two] using he2
    simpa [Subgroup.coe_mul] using congrArg (fun z : Q => (z : G)) hq2
  have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ2
  have hs2inv : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  -- `s` is central in `Q` (its coordinate has vanishing first coordinate)
  have hscen : ∀ q : G, q ∈ Q → s * q = q * s := by
    intro q hq
    have hsq : (⟨s, hsQ⟩ : Q) * ⟨s, hsQ⟩ = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      exact hs2inv
    have hsa : (e ⟨s, hsQ⟩).a = 0 :=
      a_eq_zero_of_sq_eq_one θ _ (by rw [← map_mul, hsq, map_one])
    have h1 : e ⟨s, hsQ⟩ = (⟨0, (e ⟨s, hsQ⟩).b⟩ : SzA (GaloisField 2 m) θ) := by
      ext <;> simp [hsa]
    have h2 : (⟨s, hsQ⟩ : Q) * ⟨q, hq⟩ = ⟨q, hq⟩ * ⟨s, hsQ⟩ := by
      apply e.injective
      rw [map_mul, map_mul, h1]
      ext <;> simp [add_comm]
    have hq' := congrArg (fun z : Q => (z : G)) h2
    simpa [Subgroup.coe_mul] using hq'
  have hsρ : s * ρ = ρ * s := hscen ρ hρQ
  have hts_eq : t * s * t = ρ * t * ρ := by rw [hstruct', hρinv]
  -- `t * ρ * t = s * t * ρ`
  have htρt : t * ρ * t = s * t * ρ := by
    have h1 : s * t = t * ρ * t * ρ := by
      have h := congrArg (fun z : G => t * z) hts_eq
      have hL : t * (t * s * t) = s * t := by
        simp only [← mul_assoc, ht2, one_mul]
      have hR : t * (ρ * t * ρ) = t * ρ * t * ρ := by group
      rw [hL, hR] at h
      exact h
    have h2 : s * t * ρ = t * ρ * t := by
      calc s * t * ρ = (t * ρ * t * ρ) * ρ := by rw [h1]
        _ = t * ρ * t := by
              rw [show (t * ρ * t * ρ) * ρ = t * ρ * t * (ρ * ρ) by group]
              rw [hρ2, mul_one]
    exact h2.symm
  -- `u = ρ * s` is an involution of `Q` commuting with `t`
  have huQ : ρ * s ∈ Q := Q.mul_mem hρQ hsQ
  have hut : t * (ρ * s) * t = ρ * s := by
    calc t * (ρ * s) * t = (t * ρ * t) * (t * s * t) := by
          rw [show (t * ρ * t) * (t * s * t) = t * ρ * (t * t) * s * t by group]
          rw [ht2]
          group
      _ = (s * t * ρ) * (ρ * t * ρ) := by rw [htρt, hts_eq]
      _ = ρ * s := by
            rw [show (s * t * ρ) * (ρ * t * ρ) = s * t * (ρ * ρ) * t * ρ by group]
            rw [hρ2]
            rw [show s * t * 1 * t * ρ = s * (t * t) * ρ by group]
            rw [ht2]
            rw [show s * 1 * ρ = s * ρ by group]
            exact hsρ
  have hucomm : (ρ * s) * t = t * (ρ * s) := by
    have h2 : t * (ρ * s) * t * t = (ρ * s) * t := by rw [hut]
    rw [mul_assoc (t * (ρ * s)) t t, ht2, mul_one] at h2
    exact h2.symm
  have hu1 : ρ * s = 1 := by
    refine sv_centralizer_triv hsplit huQ ?_
    rw [hucomm]
    simp [mul_assoc]
  have hρs : ρ = s := by
    have h : ρ * s * s = s := by rw [hu1, one_mul]
    rw [mul_assoc, hs2inv, mul_one] at h
    exact h
  -- `(s t)^3 = 1`
  have hsts : t * s * t = s * t * s := by rw [hts_eq, hρs]
  have hst3 : (s * t) ^ 3 = 1 := by
    have h : s * t * s * t = t * s := by
      calc s * t * s * t = s * (t * s * t) := by group
        _ = s * (s * t * s) := by rw [hsts]
        _ = t * s := by
              rw [show s * (s * t * s) = (s * s) * t * s by group]
              rw [hs2inv]
              rw [show (1 : G) * t * s = t * s by group]
    calc (s * t) ^ 3 = (s * t) ^ 2 * (s * t) := by rw [pow_succ]
      _ = (s * t) * (s * t) * (s * t) := by rw [pow_two]
      _ = (s * t * s * t) * (s * t) := by group
      _ = (t * s) * (s * t) := by rw [h]
      _ = 1 := by
            rw [show (t * s) * (s * t) = t * (s * s) * t by group]
            rw [hs2inv]
            rw [show t * (1 : G) * t = t * t by group]
            exact ht2
  have hstne : s * t ≠ 1 := by
    intro h
    have h1 : s = t := by rw [eq_inv_of_mul_eq_one_left h, hti]
    exact hsplit.not_mem (hsplit.le (h1 ▸ hsQ))
  have hord3 : orderOf (s * t) = 3 := by
    have hdvd : orderOf (s * t) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hst3
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact absurd h (fun h1 => hstne (orderOf_eq_one_iff.mp h1))
    · exact h
  have h3dvd : 3 ∣ Nat.card G := hord3 ▸ orderOf_dvd_natCard (s * t)
  exact sv_three_not_dvd (e := e) hsplit hzass h2 (sv_odd_m hθ1 hθodd hfix) h3dvd

/-! ## The field step -/

/-- The map `λ ↦ (1+λ)/(1+θλ)` maps `K ∖ {0,1}` onto itself, when `Fix θ = 𝔽₂`.

Indeed `(1+λ)/(1+θλ) = x/θx` with `x = 1+λ`, and `x ↦ θx/x` is onto `Kˣ` because its
kernel is `Fix θ ∩ Kˣ = {1}` (HB 11.9/11.12). -/
theorem sv_lam_ratio_surjective {K : Type} [Field K] [CharP K 2] [Finite K]
    (θ : K ≃+* K) (hfix : ∀ x : K, θ x = x → x = 0 ∨ x = 1) :
    ∀ μ : K, μ ≠ 0 → μ ≠ 1 → ∃ lam : K, lam ≠ 0 ∧ lam ≠ 1 ∧ (1 + lam) / (1 + θ lam) = μ := by
  intro μ hμ0 hμ1
  obtain ⟨x, hx⟩ := units_div_map_surjective θ hfix (Units.mk0 μ hμ0)⁻¹
  have hxK : θ (x : K) / (x : K) = μ⁻¹ := by
    have h := congrArg (fun u : Kˣ => (u : K)) hx
    simpa [Units.val_div_eq_div_val] using h
  have hx0 : (x : K) ≠ 0 := Units.ne_zero x
  have hθx0 : θ (x : K) ≠ 0 := fun h => hx0 (θ.injective (by rw [h, map_zero]))
  refine ⟨1 + (x : K), ?_, ?_, ?_⟩
  · intro h
    have hx1 : (x : K) = 1 := by
      have h2 : (x : K) = -(1 : K) := eq_neg_of_add_eq_zero_right h
      rwa [CharTwo.neg_eq] at h2
    have hμinv : μ⁻¹ = 1 := by rw [← hxK, hx1, map_one, div_one]
    exact hμ1 (inv_eq_one.mp hμinv)
  · intro h
    have h2 : (1 : K) + (x : K) = (1 : K) + 0 := by rw [h, add_zero]
    exact hx0 (add_left_cancel h2)
  · have h1 : 1 + (1 + (x : K)) = (x : K) := by
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    have h2 : 1 + θ ((1 : K) + (x : K)) = θ (x : K) := by
      rw [map_add, map_one]
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    rw [h1, h2]
    rw [← inv_div (θ (x : K)) (x : K), hxK, inv_inv]

/-! ## The main theorem -/

theorem structure_value_of_fix {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1)
    (hθodd : Odd (orderOf θ))
    (hfix : ∀ x : GaloisField 2 m, θ x = x → x = 0 ∨ x = 1)
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : Work.ZassenhausSuzuki.TorusCoords (GaloisField 2 m) θ H Q t e) :
    ∃ (μ : (GaloisField 2 m)ˣ) (b : GaloisField 2 m), (b = 0 ∨ b = 1) ∧
      e (⟨(Work.ZassenhausSuzuki.structPair hsplit).2,
          (Work.ZassenhausSuzuki.structPair_spec hsplit).2.2.1⟩ : Q)
        = Work.ZassenhausSuzuki.SzA.hLam θ (μ : GaloisField 2 m)
            (⟨1, b⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) := by
  classical
  obtain ⟨hsQ, hs2, hρQ, hstruct⟩ := structPair_spec hsplit
  set ρ : G := (structPair hsplit).2 with hρdef
  have ha : (e ⟨ρ, hρQ⟩ : SzA (GaloisField 2 m) θ).a ≠ 0 :=
    sv_a_ne_zero hsplit hzass h2 hθ1 hθodd hfix
  set a : GaloisField 2 m := (e ⟨ρ, hρQ⟩ : SzA (GaloisField 2 m) θ).a with ha_def
  set b : GaloisField 2 m := (e ⟨ρ, hρQ⟩ : SzA (GaloisField 2 m) θ).b with hb_def
  have hmain : b = 0 ∨ b = a * θ a := by
    rcases eq_or_ne b 0 with hb0 | hb0
    · exact Or.inl hb0
    · right
      -- HB 11.12: no `λ ∈ K ∖ {0,1}` solves `a·θa·(1+θλ) = b·(λ+θλ)`
      have hclaim : ∀ lam : GaloisField 2 m, lam ≠ 0 → lam ≠ 1 →
          a * θ a * (1 + θ lam) ≠ b * (lam + θ lam) := by
        intro lam hlam0 hlam1 heq
        obtain ⟨d, hdD, hdact⟩ := exists_torus_action hsplit hzass htorus (Units.mk0 lam hlam0)
        have hdne : d ≠ 1 := by
          intro hd1
          have hx := hdact (e.symm (⟨1, 0⟩ : SzA (GaloisField 2 m) θ))
          rw [MulEquiv.apply_symm_apply, hd1, one_mul, inv_one, mul_one] at hx
          have hx' : e.symm (SzA.hLam θ (↑(Units.mk0 lam hlam0))
                (⟨1, 0⟩ : SzA (GaloisField 2 m) θ))
              = e.symm (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) := Subtype.ext hx
          have h2' : SzA.hLam θ (↑(Units.mk0 lam hlam0))
                (⟨1, 0⟩ : SzA (GaloisField 2 m) θ)
              = (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) := by
            have := congrArg (fun z : Q => e z) hx'
            simpa using this
          have h3 : lam = 1 := by
            have h4 := congrArg SzA.a h2'
            simpa [SzA.hLam] using h4
          exact hlam1 h3
        set w : Q := (⟨ρ, hρQ⟩ : Q)⁻¹
            * e.symm (SzA.hLam θ lam (e ⟨ρ, hρQ⟩)) with hw
        have hwG : (w : G) = ρ⁻¹ * d * ρ * d⁻¹ := by
          rw [hw, Subgroup.coe_mul, Subgroup.coe_inv]
          rw [show (↑(e.symm (SzA.hLam θ lam (e ⟨ρ, hρQ⟩))) : G)
              = ↑(e.symm (SzA.hLam θ (↑(Units.mk0 lam hlam0)) (e ⟨ρ, hρQ⟩))) by
            rw [Units.val_mk0]]
          rw [hdact ⟨ρ, hρQ⟩, show ((⟨ρ, hρQ⟩ : Q) : G) = ρ from rfl]
          group
        have hlam1' : (1 : GaloisField 2 m) + lam ≠ 0 := by
          intro h
          have h2 : lam = -(1 : GaloisField 2 m) := eq_neg_of_add_eq_zero_right h
          rw [CharTwo.neg_eq] at h2
          exact hlam1 h2
        have hθlam1' : (1 : GaloisField 2 m) + θ lam ≠ 0 := by
          intro h
          have h2 : θ lam = -(1 : GaloisField 2 m) := eq_neg_of_add_eq_zero_right h
          rw [CharTwo.neg_eq] at h2
          exact hlam1 (θ.injective (by rw [h2, map_one]))
        -- `h_{（1+lam)⁻¹} (e w) = e ρ`
        have hμ : SzA.hLam θ
            ((((Units.mk0 ((1 : GaloisField 2 m) + lam) hlam1')⁻¹ : (GaloisField 2 m)ˣ)
              : GaloisField 2 m)) (e w) = e ⟨ρ, hρQ⟩ := by
          have hew : e w = (⟨a * (1 + lam), b * (1 + lam * θ lam)
              + a * θ a * (1 + θ lam)⟩ : SzA (GaloisField 2 m) θ) := by
            rw [hw, map_mul, map_inv, MulEquiv.apply_symm_apply]
            have ha_ : (e ⟨ρ, hρQ⟩ : SzA (GaloisField 2 m) θ).a = a := ha_def.symm
            have hb_ : (e ⟨ρ, hρQ⟩ : SzA (GaloisField 2 m) θ).b = b := hb_def.symm
            ext
            · simp only [SzA.mul_a, SzA.inv_a, SzA.hLam_a, ha_, CharTwo.neg_eq]
              ring
            · simp only [SzA.mul_b, SzA.inv_a, SzA.inv_b, SzA.hLam_a, SzA.hLam_b, ha_, hb_,
                map_mul, map_add, map_one, CharTwo.neg_eq]
              ring
          rw [hew, Units.val_inv_eq_inv_val, Units.val_mk0]
          ext
          · simp only [SzA.hLam_a]
            rw [← ha_def, mul_comm a (1 + lam), ← mul_assoc, inv_mul_cancel₀ hlam1', one_mul]
          · simp only [SzA.hLam_b]
            rw [← hb_def, map_inv₀, map_add, map_one]
            field_simp
            linear_combination heq
        -- the crux contradicts `d w d⁻¹ = ρ`
        refine crux_structure_value hsplit hzass h2 hθ1 hθodd hfix e htorus d⁻¹
          ((twoPoint H t).inv_mem hdD) (fun hh => hdne (inv_eq_one.mp hh)) ?_
        obtain ⟨d', hd'D, hd'act⟩ :=
          exists_torus_action hsplit hzass htorus
            (Units.mk0 ((1 : GaloisField 2 m) + lam) hlam1')⁻¹
        refine ⟨d', hd'D, ?_⟩
        have h := hd'act w
        rw [hμ, MulEquiv.symm_apply_apply] at h
        rw [inv_inv, ← hwG, ← h]
      -- `a·θa/b + 1 ∉ K ∖ {0,1}`
      have hnot : ¬ (a * θ a / b + 1 ≠ 0 ∧ a * θ a / b + 1 ≠ 1) := by
        rintro ⟨h0, h1⟩
        obtain ⟨lam, hlam0, hlam1, hval⟩ :=
          sv_lam_ratio_surjective θ hfix (a * θ a / b + 1) h0 h1
        refine hclaim lam hlam0 hlam1 ?_
        have hθlam1 : (1 : GaloisField 2 m) + θ lam ≠ 0 := by
          intro h
          have h2 : θ lam = -(1 : GaloisField 2 m) := eq_neg_of_add_eq_zero_right h
          rw [CharTwo.neg_eq] at h2
          exact hlam1 (θ.injective (by rw [h2, map_one]))
        have hval2 : (1 + lam) * b = (a * θ a + b) * (1 + θ lam) := by
          have h2 := hval
          rw [div_eq_iff hθlam1] at h2
          rw [h2]
          field_simp
        have htwo : (2 : GaloisField 2 m) = 0 := CharP.cast_eq_zero (GaloisField 2 m) 2
        linear_combination -hval2 - (θ lam * b) * htwo
      rcases eq_or_ne (a * θ a / b + 1) 0 with h0 | h0
      · have h1 : a * θ a / b = 1 := by
          have h2 : a * θ a / b = -(1 : GaloisField 2 m) := eq_neg_of_add_eq_zero_left h0
          rwa [CharTwo.neg_eq] at h2
        exact ((div_eq_one_iff_eq hb0).mp h1).symm
      · have h1 : a * θ a / b + 1 = 1 := by
          by_contra hne
          exact hnot ⟨h0, hne⟩
        have hc0 : a * θ a / b = 0 := by
          have h2 : a * θ a / b + 1 = 0 + 1 := by rw [h1, zero_add]
          exact add_right_cancel h2
        have hz : a * θ a = 0 := by
          rw [div_eq_zero_iff] at hc0
          rcases hc0 with h | h
          · exact h
          · exact absurd h hb0
        have ha0 : a = 0 := by
          rcases mul_eq_zero.mp hz with h | h
          · exact h
          · exact θ.injective (by rw [h, map_zero])
        exact absurd ha0 ha
  rcases hmain with hb | hb
  · refine ⟨Units.mk0 a ha, 0, Or.inl rfl, ?_⟩
    have he : e ⟨ρ, hρQ⟩ = (⟨a, 0⟩ : SzA (GaloisField 2 m) θ) := by
      ext
      · rw [← ha_def]
      · rw [← hb_def]; exact hb
    rw [he]
    ext <;> simp [SzA.hLam]
  · refine ⟨Units.mk0 a ha, 1, Or.inr rfl, ?_⟩
    have he : e ⟨ρ, hρQ⟩ = (⟨a, a * θ a⟩ : SzA (GaloisField 2 m) θ) := by
      ext
      · rw [← ha_def]
      · rw [← hb_def]; exact hb
    rw [he]
    ext <;> simp [SzA.hLam]

end Work.ZassenhausSuzuki
