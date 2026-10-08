import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.AUTA7.A7.CentralizerOrderThree
import Submission.Work.CORE4.A7FGB.card_sup_of_inf_eq_bot
import Submission.Work.CORE4.A7FGB.involution_support
import Submission.Work.CORE4.A7FGB.commuting_support
import Submission.Work.CORE4.A7FGB.centralizer_le_sup
import Submission.Work.CORE4.A7FGB.involution_support_mem
import Submission.Work.CORE4.A7FGB.sylow_seven_card
import Submission.Work.CORE4.A7FGB.transitive_or_preserves
import Submission.Work.CORE4.A7FGB.relIndex_centralizer_normalizer_four_dvd
import Submission.Work.CORE4.A7FGB.sum_fixedBy_lower_bound
import Submission.Work.CORE4.A7FGB.involutions_ge_alt
import Submission.Work.CORE4.A7FGB.three_cycles_ge
import Submission.Work.CORE4.A7FGB.six_elt_order_six
import Submission.Work.CORE4.A7FGB.card_252_false

open scoped MatrixGroups

namespace Work.CORE4

open Subgroup

/-! ## The main theorem -/

theorem A7FourGroupBound (V K R : Subgroup (alternatingGroup (Fin 7)))
    (hV4 : Work.GW2.IsFourGroup V) (hK : Nat.card K = 3)
    (hKV : K ≤ Subgroup.centralizer (V : Set (alternatingGroup (Fin 7))))
    (hKR : K ≤ R) (hVR : V ≤ R) (hodd : Odd (V.relIndex R)) :
    Nat.card R ≤ 36 ∧ R ≤ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7))) := by
  classical
  obtain ⟨hVcard, hVsq⟩ := hV4
  have hVsq' : ∀ v ∈ V, v * v = 1 := fun v hv => by rw [← pow_two]; exact hVsq v hv
  -- ## 0. `|A₇| = 2520`
  have hA7card : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
    have h := Subgroup.card_mul_index
      (H := (alternatingGroup (Fin 7) : Subgroup (Equiv.Perm (Fin 7))))
    rw [alternatingGroup.index_eq_two] at h
    have h2 : Nat.card ↥(alternatingGroup (Fin 7)) * 2 = 5040 := by
      have h3 : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
        rw [Nat.card_perm, show Nat.card (Fin 7) = 7 by simp]
        norm_num
      rw [← h3]
      exact h
    omega
  -- ## 1. an element of `K` of order three
  obtain ⟨x, hxK, hxord⟩ : ∃ x : alternatingGroup (Fin 7), x ∈ K ∧ orderOf x = 3 := by
    have hdvd : 3 ∣ Fintype.card ↥K := by
      rw [← Nat.card_eq_fintype_card, hK]
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card (G := ↥K) 3 hdvd
    exact ⟨(y : ↥K), y.2, by
      rw [← hy]
      exact orderOf_injective (Subgroup.subtype K) Subtype.val_injective y⟩
  have hxR : x ∈ R := hKR hxK
  have hxcomm : ∀ v ∈ V, v * x = x * v := by
    intro v hv
    have h1 := (Subgroup.mem_centralizer_iff.mp (hKV hxK)) v hv
    simpa [mul_comm] using h1
  have hxp3 : (x : Equiv.Perm (Fin 7)) ^ 3 = 1 := by
    have h1 : x ^ orderOf x = 1 := pow_orderOf_eq_one x
    rw [hxord] at h1
    simpa using congrArg (fun y : alternatingGroup (Fin 7) => (y : Equiv.Perm (Fin 7))) h1
  have hxp1 : (x : Equiv.Perm (Fin 7)) ≠ 1 := by
    intro h
    have h1 : x = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hxord
    exact absurd hxord (by norm_num)
  -- ## 2. `V` is abelian, and the support of its non-identity elements
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    have hab : a * b ∈ V := V.mul_mem ha hb
    have ha2 : a * a = 1 := hVsq' a ha
    have hb2 : b * b = 1 := hVsq' b hb
    have h1 : (a * b) * (a * b) = 1 := by
      have h := hVsq' (a * b) hab
      rwa [← pow_two] at h
    calc a * b = (a * b)⁻¹ := mul_eq_one_iff_eq_inv.mp h1
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [inv_eq_of_mul_eq_one_right ha2, inv_eq_of_mul_eq_one_right hb2]
  have hsuppStruct : ∀ v ∈ V, v ≠ 1 →
      (v : Equiv.Perm (Fin 7)).support = Finset.univ \ (x : Equiv.Perm (Fin 7)).support := by
    intro v hv hv1
    have hvv : v * v = 1 := hVsq' v hv
    have hvp : (v : Equiv.Perm (Fin 7)) * (v : Equiv.Perm (Fin 7)) = 1 := by
      simpa using congrArg (fun y : alternatingGroup (Fin 7) => (y : Equiv.Perm (Fin 7))) hvv
    have hcmp : (v : Equiv.Perm (Fin 7)) * (x : Equiv.Perm (Fin 7)) =
        (x : Equiv.Perm (Fin 7)) * (v : Equiv.Perm (Fin 7)) := by
      simpa using
        congrArg (fun y : alternatingGroup (Fin 7) => (y : Equiv.Perm (Fin 7))) (hxcomm v hv)
    have hvc : (v : Equiv.Perm (Fin 7)).support.card = 4 :=
      Work.CORE4.A7FGB.involution_support v hvv hv1
    exact (Work.CORE4.A7FGB.commuting_support _ _ hxp3 hxp1 hvp hcmp hvc).1
  have hne : ∃ v : alternatingGroup (Fin 7), v ∈ V ∧ v ≠ 1 := by
    by_contra h
    push_neg at h
    have hbot : V ≤ ⊥ := fun y hy => by
      rw [Subgroup.mem_bot]
      exact h y hy
    have hVbot : V = ⊥ := bot_unique hbot
    rw [hVbot, Subgroup.card_bot] at hVcard
    exact absurd hVcard (by norm_num)
  obtain ⟨v₀, hv₀V, hv₀1⟩ := hne
  have hxcard3 : (x : Equiv.Perm (Fin 7)).support.card = 3 := by
    have hvv : v₀ * v₀ = 1 := hVsq' v₀ hv₀V
    have hvp : (v₀ : Equiv.Perm (Fin 7)) * (v₀ : Equiv.Perm (Fin 7)) = 1 := by
      simpa using congrArg (fun y : alternatingGroup (Fin 7) => (y : Equiv.Perm (Fin 7))) hvv
    have hcmp : (v₀ : Equiv.Perm (Fin 7)) * (x : Equiv.Perm (Fin 7)) =
        (x : Equiv.Perm (Fin 7)) * (v₀ : Equiv.Perm (Fin 7)) := by
      simpa using
        congrArg (fun y : alternatingGroup (Fin 7) => (y : Equiv.Perm (Fin 7))) (hxcomm v₀ hv₀V)
    have hvc : (v₀ : Equiv.Perm (Fin 7)).support.card = 4 :=
      Work.CORE4.A7FGB.involution_support v₀ hvv hv₀1
    exact (Work.CORE4.A7FGB.commuting_support _ _ hxp3 hxp1 hvp hcmp hvc).2
  -- ## 3. the set `T` of points fixed by `x`
  set T : Finset (Fin 7) := Finset.univ \ (x : Equiv.Perm (Fin 7)).support with hT
  have hTcard : T.card = 4 := by
    rw [hT, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hxcard3]
    norm_num
  have hsuppT : ∀ v ∈ V, v ≠ 1 → (v : Equiv.Perm (Fin 7)).support = T := by
    intro v hv hv1
    rw [hsuppStruct v hv hv1, hT]
  have hxT : (x : Equiv.Perm (Fin 7)).support = Finset.univ \ T := by
    rw [hT]
    ext a
    simp
  -- ## 4. the centralizer and the normalizer of `V` inside `R`
  have hVKbot : V ⊓ K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hyV, hyK⟩ := Subgroup.mem_inf.mp hy
    have h2 : orderOf y ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      exact hVsq' y hyV
    have h3 : orderOf y ∣ 3 := by
      have h := Subgroup.card_dvd_of_le (H := Subgroup.zpowers y) (K := K)
        (Subgroup.zpowers_le.mpr hyK)
      rwa [Nat.card_zpowers, hK] at h
    have h1 : orderOf y = 1 := by
      have hg : orderOf y ∣ Nat.gcd 2 3 := Nat.dvd_gcd h2 h3
      have h1 : orderOf y ∣ 1 := by simpa using hg
      exact Nat.dvd_one.mp h1
    exact orderOf_eq_one_iff.mp h1
  have hVxbot : V ⊓ Subgroup.zpowers x = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hyV, hyx⟩ := Subgroup.mem_inf.mp hy
    have h2 : orderOf y ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      exact hVsq' y hyV
    have h3 : orderOf y ∣ 3 := by
      have h := Subgroup.card_dvd_of_le (H := Subgroup.zpowers y) (K := Subgroup.zpowers x)
        (Subgroup.zpowers_le.mpr hyx)
      rwa [Nat.card_zpowers, Nat.card_zpowers, hxord] at h
    have h1 : orderOf y = 1 := by
      have hg : orderOf y ∣ Nat.gcd 2 3 := Nat.dvd_gcd h2 h3
      have h1 : orderOf y ∣ 1 := by simpa using hg
      exact Nat.dvd_one.mp h1
    exact orderOf_eq_one_iff.mp h1
  have hVleCentK : V ≤ Subgroup.centralizer (K : Set (alternatingGroup (Fin 7))) :=
    (Subgroup.le_centralizer_iff).mpr hKV
  have hVK_card : Nat.card ↥(V ⊔ K) = 12 := by
    have hN : V ≤ Subgroup.normalizer (K : Set (alternatingGroup (Fin 7))) :=
      le_trans hVleCentK
        (Subgroup.centralizer_le_normalizer (K : Set (alternatingGroup (Fin 7))))
    rw [Work.CORE4.A7FGB.card_sup_of_inf_eq_bot V K hN hVKbot, hVcard, hK] <;> norm_num
  have hVx_card : Nat.card ↥(V ⊔ Subgroup.zpowers x) = 12 := by
    have hN : V ≤ Subgroup.normalizer ((Subgroup.zpowers x) : Set (alternatingGroup (Fin 7))) := by
      refine le_trans ?_
        (Subgroup.centralizer_le_normalizer ((Subgroup.zpowers x) : Set (alternatingGroup (Fin 7))))
      intro c hc
      change c ∈ Subgroup.centralizer (Subgroup.zpowers x : Set (alternatingGroup (Fin 7)))
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp (hVleCentK hc)) y
        (Subgroup.zpowers_le.mpr hxK hy)
    rw [Work.CORE4.A7FGB.card_sup_of_inf_eq_bot V (Subgroup.zpowers x) hN hVxbot, hVcard,
      Nat.card_zpowers, hxord] <;> norm_num
  set Cc : Subgroup (alternatingGroup (Fin 7)) :=
    R ⊓ Subgroup.centralizer (V : Set (alternatingGroup (Fin 7))) with hCc
  set Nn : Subgroup (alternatingGroup (Fin 7)) :=
    R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7))) with hNn
  have hVK_le_Cc : V ⊔ K ≤ Cc := by
    rw [sup_le_iff]
    constructor
    · intro v hv
      refine ⟨hVR hv, ?_⟩
      change v ∈ Subgroup.centralizer (V : Set (alternatingGroup (Fin 7)))
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (hVcomm v hv w hw).symm
    · intro k hk
      exact ⟨hKR hk, hKV hk⟩
  have hCc_le_Vx : Cc ≤ V ⊔ Subgroup.zpowers x := by
    intro c hc
    obtain ⟨-, hcC⟩ := Subgroup.mem_inf.mp hc
    exact Work.CORE4.A7FGB.centralizer_le_sup V x hVcard hVsq hxord hxcard3
      (fun v hv => hxcomm v hv) hsuppStruct hcC
  have hzx_le_K : Subgroup.zpowers x ≤ K := Subgroup.zpowers_le.mpr hxK
  have hCc_eq : Cc = V ⊔ K := by
    refine le_antisymm ?_ hVK_le_Cc
    refine le_trans hCc_le_Vx ?_
    exact sup_le le_sup_left (le_trans hzx_le_K le_sup_right)
  have hCc_card : Nat.card ↥Cc = 12 := by rw [hCc_eq, hVK_card]
  have hCc_le_Nn : Cc ≤ Nn := by
    intro c hc
    obtain ⟨hcR, hcC⟩ := Subgroup.mem_inf.mp hc
    exact ⟨hcR, Subgroup.centralizer_le_normalizer _ hcC⟩
  have hNCdvd : Cc.relIndex Nn ∣ 6 :=
    Work.CORE4.A7FGB.relIndex_centralizer_normalizer_four_dvd R V hVcard hVsq' hVR
  have hrel1 : Cc.relIndex Nn * Nat.card ↥Cc = Nat.card ↥Nn := by
    have h := Subgroup.relIndex_mul_card (H := Cc) (K := Nn)
    rwa [inf_eq_left.mpr hCc_le_Nn] at h
  have hrel2 : Nn.relIndex R * Nat.card ↥Nn = Nat.card ↥R := by
    have h := Subgroup.relIndex_mul_card (H := Nn) (K := R)
    rwa [inf_eq_left.mpr inf_le_left] at h
  have hrel3 : V.relIndex R * Nat.card ↥V = Nat.card ↥R := by
    have h := Subgroup.relIndex_mul_card (H := V) (K := R)
    rwa [inf_eq_left.mpr hVR] at h
  -- ## 5. the index of `C_R(V)` in `N_R(V)` is `1` or `3`
  have h3kn : 3 * (Cc.relIndex Nn * Nn.relIndex R) = V.relIndex R := by
    have h1 : Nat.card ↥R = (Cc.relIndex Nn * Nn.relIndex R) * 12 := by
      rw [← hrel2, ← hrel1, hCc_card]
      ring
    have h2 : Nat.card ↥R = 4 * V.relIndex R := by
      rw [← hrel3, hVcard]
      ring
    have h3 : 4 * (3 * (Cc.relIndex Nn * Nn.relIndex R)) = 4 * V.relIndex R := by
      calc 4 * (3 * (Cc.relIndex Nn * Nn.relIndex R))
          = (Cc.relIndex Nn * Nn.relIndex R) * 12 := by ring
        _ = Nat.card ↥R := h1.symm
        _ = 4 * V.relIndex R := h2
    exact mul_left_cancel₀ (by norm_num : (4 : ℕ) ≠ 0) h3
  have hoddNC : Odd (Cc.relIndex Nn) := by
    have hk : Cc.relIndex Nn ∣ V.relIndex R := by
      refine ⟨3 * Nn.relIndex R, ?_⟩
      rw [← h3kn]
      ring
    exact Odd.of_dvd_nat hodd hk
  have hNC13 : Cc.relIndex Nn = 1 ∨ Cc.relIndex Nn = 3 := by
    have h3 : Cc.relIndex Nn ∣ 3 := by
      have h6 : Cc.relIndex Nn ∣ 2 * 3 := by simpa using hNCdvd
      exact (Odd.coprime_two_right hoddNC).dvd_of_dvd_mul_left h6
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h3 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hNn_card : Nat.card ↥Nn = 12 ∨ Nat.card ↥Nn = 36 := by
    have key : Nat.card ↥Nn = Cc.relIndex Nn * 12 := by
      rw [← hrel1, hCc_card]
    rcases hNC13 with h | h
    · left
      rw [key, h] <;> norm_num
    · right
      rw [key, h] <;> norm_num
  -- ## 6. the two cases
  by_cases hcase : Nn = R
  · -- `R` normalizes `V`
    refine ⟨?_, ?_⟩
    · rw [← hcase]
      rcases hNn_card with h | h <;> omega
    · rw [← hcase]
      exact inf_le_right
  · exfalso
    -- ## 6a. `R` acts transitively on the seven points
    have htrans : MulAction.IsPretransitive ↥R (Fin 7) := by
      rcases Work.CORE4.A7FGB.transitive_or_preserves R V x T hTcard hVR hVcard hVsq' hsuppT
        hxR hxord hxT with h | h
      · exact h
      · exfalso
        have hconjV : ∀ (a : alternatingGroup (Fin 7)), a ∈ R → ∀ w ∈ V, a * w * a⁻¹ ∈ V := by
          intro a ha w hw
          rcases eq_or_ne w 1 with rfl | hw1
          · simp
          · have hww : w * w = 1 := hVsq' w hw
            have hwsupp : (w : Equiv.Perm (Fin 7)).support = T := hsuppT w hw hw1
            have hmapT : Finset.map (Equiv.toEmbedding a) T = T := by
              refine Finset.eq_of_subset_of_card_le ?_ ?_
              · intro b hb
                rw [Finset.mem_map] at hb
                obtain ⟨c, hc, hcb⟩ := hb
                rw [← hcb]
                simpa using h ⟨a, ha⟩ c hc
              · rw [Finset.card_map]
            have hcs : ((a * w * a⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support = T := by
              have hcoe : ((a * w * a⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))
                  = (a : Equiv.Perm (Fin 7)) * (w : Equiv.Perm (Fin 7)) *
                    ((a : Equiv.Perm (Fin 7)))⁻¹ := rfl
              rw [hcoe, Equiv.Perm.support_conj, hwsupp]
              simpa using hmapT
            have hcc : ((a * w * a⁻¹) * (a * w * a⁻¹) : alternatingGroup (Fin 7)) = 1 := by
              rw [show ((a * w * a⁻¹) * (a * w * a⁻¹) : alternatingGroup (Fin 7))
                  = a * (w * w) * a⁻¹ from by group]
              rw [hww]
              group
            have hc1 : (a * w * a⁻¹ : alternatingGroup (Fin 7)) ≠ 1 := by
              intro h0
              refine hw1 ?_
              have h2 : a⁻¹ * (a * w * a⁻¹) * (a⁻¹)⁻¹ = w := by group
              rw [h0] at h2
              simpa using h2.symm
            exact Work.CORE4.A7FGB.involution_support_mem V T hTcard hVcard hVsq' hsuppT
              (a * w * a⁻¹) hcc hc1 hcs
        have hnormalizer : R ≤ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7))) := by
          rw [Subgroup.le_normalizer_iff]
          intro a ha w hw
          exact hconjV a ha w hw
        have hle : R ≤ Nn := fun a ha => ⟨ha, hnormalizer ha⟩
        exact hcase (le_antisymm (by rw [hNn]; exact inf_le_left) hle)
    -- ## 6b. `7 ∣ |R|`
    have h7R : 7 ∣ Nat.card ↥R := by
      haveI : MulAction.IsPretransitive ↥R (Fin 7) := htrans
      have h := MulAction.index_stabilizer_of_transitive ↥R (0 : Fin 7)
      have h2 : Nat.card (Fin 7) = 7 := by simp
      rw [h2] at h
      have h3 := Subgroup.card_mul_index (H := MulAction.stabilizer ↥R (0 : Fin 7))
      rw [h] at h3
      exact ⟨Nat.card ↥(MulAction.stabilizer ↥R (0 : Fin 7)), by rw [← h3, mul_comm]⟩
    rcases hNn_card with hNn12 | hNn36
    · -- ## 6c. `|N_R(V)| = 12`: the Burnside count
      have hb := Work.CORE4.A7FGB.sum_fixedBy_lower_bound R V T hTcard hVR hVcard hVsq' hsuppT
        ⟨x, hxR, hxord, hxT⟩ htrans
      rw [← hNn] at hb
      have hR : Nat.card ↥R = Nn.relIndex R * 12 := by rw [← hrel2, hNn12]
      omega
    · -- ## 6d. `|N_R(V)| = 36`
      have hR36 : Nat.card ↥R = Nn.relIndex R * 36 := by
        rw [← hrel2, hNn36]
      have h7n : 7 ∣ Nn.relIndex R := by
        have h := h7R
        rw [hR36] at h
        rcases (show Nat.Prime 7 by norm_num).dvd_mul.mp h with h1 | h1
        · exact h1
        · exact absurd h1 (by norm_num)
      have h36 : Nn.relIndex R * 36 ∣ 2520 := by
        have h1 : Nat.card ↥R ∣ Nat.card ↥(alternatingGroup (Fin 7)) := by
          have h2 : R ≤ (⊤ : Subgroup (alternatingGroup (Fin 7))) := le_top
          simpa using Subgroup.card_dvd_of_le h2
        rw [hA7card] at h1
        rw [hR36] at h1
        exact h1
      have hndvd70 : Nn.relIndex R ∣ 70 := by
        have h2 : 36 * Nn.relIndex R ∣ 36 * 70 := by
          rw [show (2520 : ℕ) = 36 * 70 by norm_num, mul_comm] at h36
          exact h36
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : (0 : ℕ) < 36) h2
      have hoddn : Odd (Nn.relIndex R) := by
        have h3n : 9 * Nn.relIndex R = V.relIndex R := by
          have h1 : Nat.card ↥R = 4 * V.relIndex R := by
            rw [← hrel3, hVcard]
            ring
          have h2 : 4 * (9 * Nn.relIndex R) = 4 * V.relIndex R := by
            rw [← h1, hR36]
            ring
          exact mul_left_cancel₀ (by norm_num : (4 : ℕ) ≠ 0) h2
        have hd : Nn.relIndex R ∣ V.relIndex R := ⟨9, by rw [← h3n, mul_comm]⟩
        exact Odd.of_dvd_nat hodd hd
      have hndvd35 : Nn.relIndex R ∣ 35 := by
        have h4 : Nn.relIndex R ∣ 35 * 2 := by
          rw [show (70 : ℕ) = 35 * 2 by norm_num] at hndvd70
          exact hndvd70
        exact (Odd.coprime_two_right hoddn).dvd_of_dvd_mul_left h4
      have hn : Nn.relIndex R = 7 ∨ Nn.relIndex R = 35 := by
        obtain ⟨j, hj⟩ := h7n
        have hj5 : j ∣ 5 := by
          have h1 : 7 * j ∣ 7 * 5 := by
            rw [hj] at hndvd35
            rwa [show (35 : ℕ) = 7 * 5 by norm_num] at hndvd35
          exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : (0 : ℕ) < 7) h1
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hj5 with h | h
        · left
          rw [h, mul_one] at hj
          exact hj
        · right
          rw [h] at hj
          omega
      rcases hn with hn7 | hn35
      · -- `|R| = 252`, impossible
        have hR252 : Nat.card ↥R = 252 := by
          rw [hR36, hn7] <;> norm_num
        have h7c := Work.CORE4.A7FGB.sylow_seven_card R hR252
        have hinv := Work.CORE4.A7FGB.involutions_ge_alt R V T hTcard hVR hVcard hVsq' hsuppT
        have h3c := Work.CORE4.A7FGB.three_cycles_ge R V x T hTcard hVR hVcard hVsq' hsuppT
          hxR hxord hxT
        have h6c := Work.CORE4.A7FGB.six_elt_order_six R V x hVR hxR hVcard hVsq' hxord hxcomm
        rw [hNn] at hn7
        rw [hn7] at hinv h3c
        norm_num at hinv h3c
        refine Work.CORE4.A7FGB.card_252_false R hR252 ?_ ?_ h6c h7c.2
        · simpa [Nat.card_eq_fintype_card] using hinv
        · simpa [Nat.card_eq_fintype_card] using h3c
      · -- `|R| = 1260`: a subgroup of index two
        have hR1260 : Nat.card ↥R = 1260 := by
          rw [hR36, hn35] <;> norm_num
        have hindex : R.index = 2 := by
          have h := Subgroup.card_mul_index (H := R)
          rw [hR1260, hA7card] at h
          omega
        haveI : R.Normal := Subgroup.normal_of_index_eq_two hindex
        haveI : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
          alternatingGroup.isSimpleGroup (α := Fin 7) (by simp)
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with h | h
        · rw [h, Subgroup.card_bot] at hR1260
          norm_num at hR1260
        · rw [h] at hR1260
          have htop : Nat.card ↥(⊤ : Subgroup (alternatingGroup (Fin 7))) = 2520 := by
            simpa using hA7card
          rw [htop] at hR1260
          norm_num at hR1260

end Work.CORE4
