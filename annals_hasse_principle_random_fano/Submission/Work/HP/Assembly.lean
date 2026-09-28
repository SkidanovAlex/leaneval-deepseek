import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.count_basic
import Submission.Work.HP.bridge
import Submission.Work.HP.prop1
import Submission.Work.HP.prop2
import Submission.Work.HP.density
import Submission.Work.HP.conics

/-! Final assembly for annals_hasse_principle_random_fano, term-checked against the sorry'd nodes. -/

namespace Work.HP

open Filter

lemma primCount_mono (d n : ℕ) (hfin : ∀ (A : ℝ) (P : (Mon d n → ℤ) → Prop), (primSet d n A P).Finite)
    (A : ℝ) {P Q : (Mon d n → ℤ) → Prop} (h : ∀ a, P a → Q a) :
    primCount d n A P ≤ primCount d n A Q := by
  unfold primCount
  exact_mod_cast Set.ncard_le_ncard
    (fun a (ha : a ∈ primSet d n A P) => (⟨ha.1, ha.2.1, h a ha.2.2⟩ : a ∈ primSet d n A Q)) (hfin A Q)

lemma primCount_or (d n : ℕ) (hfin : ∀ (A : ℝ) (P : (Mon d n → ℤ) → Prop), (primSet d n A P).Finite)
    (A : ℝ) (P Q R : (Mon d n → ℤ) → Prop) (h : ∀ a, P a → Q a ∨ R a) :
    primCount d n A P ≤ primCount d n A Q + primCount d n A R := by
  unfold primCount
  have hsub : primSet d n A P ⊆ primSet d n A Q ∪ primSet d n A R := by
    intro a ha
    rcases h a ha.2.2 with hq | hr
    · exact Or.inl ⟨ha.1, ha.2.1, hq⟩
    · exact Or.inr ⟨ha.1, ha.2.1, hr⟩
  have h1 := Set.ncard_le_ncard hsub ((hfin A Q).union (hfin A R))
  have h2 := Set.ncard_union_le (primSet d n A Q) (primSet d n A R)
  exact_mod_cast h1.trans h2

lemma ratio_mono (d n : ℕ) (hfin : ∀ (A : ℝ) (P : (Mon d n → ℤ) → Prop), (primSet d n A P).Finite)
    (A : ℝ) {P Q : (Mon d n → ℤ) → Prop} (h : ∀ a, P a → Q a) :
    ratio d n A P ≤ ratio d n A Q := by
  unfold ratio
  exact div_le_div_of_nonneg_right (primCount_mono d n hfin A h) (by unfold primCount; positivity)

lemma ratio_nonneg (d n : ℕ) (A : ℝ) (P : (Mon d n → ℤ) → Prop) : 0 ≤ ratio d n A P := by
  unfold ratio primCount; positivity

/-- `w(A/η) → ∞`. -/
lemma wOf_div_tendsto (η : ℝ) (hη : 0 < η) : Tendsto (fun A : ℝ => wOf (A / η)) atTop atTop := by
  have h1 : Tendsto (fun A : ℝ => Real.log (A / η)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const hη)
  suffices h : Tendsto (fun u : ℝ => u / Real.log u) atTop atTop from
    (h.comp h1).congr (fun A => rfl)
  have hlo := Real.isLittleO_log_id_atTop
  have h0 : Tendsto (fun u : ℝ => Real.log u / u) atTop (nhds 0) := by
    simpa using hlo.tendsto_div_nhds_zero
  have hpos : ∀ᶠ u : ℝ in atTop, 0 < Real.log u / u := by
    filter_upwards [eventually_gt_atTop (Real.exp 1)] with u hu
    have hu0 : 0 < u := lt_trans (Real.exp_pos 1) hu
    have : 1 < Real.log u := by
      rw [Real.lt_log_iff_exp_lt hu0]; exact hu
    positivity
  have h0' : Tendsto (fun u : ℝ => Real.log u / u) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨h0, hpos⟩
  have := h0'.inv_tendsto_nhdsGT_zero
  refine this.congr' ?_
  filter_upwards with u
  simp [inv_div]

/-- `w(A/η) ≤ A` eventually. -/
lemma wOf_div_le (η : ℝ) (hη : 0 < η) : ∀ᶠ A : ℝ in atTop, wOf (A / η) ≤ A := by
  have hb := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 2 by norm_num)
  have hL : Tendsto (fun A : ℝ => Real.log (Real.log (A / η))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const hη))
  filter_upwards [hb, hL.eventually_ge_atTop 1, eventually_ge_atTop (2 * |Real.log η| + 1),
    eventually_gt_atTop (0 : ℝ), eventually_ge_atTop η] with A hA hLL hAbig hA0 hAη
  have hlogdiv : Real.log (A / η) = Real.log A - Real.log η := Real.log_div hA0.ne' hη.ne'
  have hlogA : Real.log A ≤ A / 2 := by
    have := hA
    simp only [Real.norm_eq_abs, id] at this
    rw [abs_of_pos hA0] at this
    linarith [le_abs_self (Real.log A)]
  have hpos : 0 ≤ Real.log (A / η) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hη]
    linarith
  unfold wOf
  calc Real.log (A / η) / Real.log (Real.log (A / η)) ≤ Real.log (A / η) :=
        div_le_self hpos hLL
    _ = Real.log A - Real.log η := hlogdiv
    _ ≤ A := by linarith [neg_abs_le (Real.log η)]

/-- Hasse principle for 100% of the forms in `LocSet` (paper's main height result, via N10 and N13). -/
theorem hasse_most (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2))
    (h33 : (d, n) ≠ (3, 3)) :
    ∃ K : ℝ, 0 < K ∧ ∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ A in atTop,
      primCount d n A (fun a => LocSet d n (wOf (A / η)) a ∧ ¬ HasRatZero d n a)
        ≤ K * A ^ NN d n * η ^ (1 / (24 * (n : ℝ))) := by
  obtain ⟨hfin, -⟩ := count_basic d n hd hdn
  obtain ⟨K1, hK1, h1⟩ := prop1 d n hd hdn h22 h33
  obtain ⟨K2, hK2, h2⟩ := prop2 d n hd hdn h22
  refine ⟨K1 + K2, by positivity, fun η hη0 hη1 => ?_⟩
  have hφ : 1 < 1 / η := by rw [lt_div_iff₀ hη0]; linarith
  filter_upwards [h1 (1 / η) hφ, h2 (1 / η) hφ, eventually_ge_atTop (0 : ℝ)] with A hA1 hA2 hA0
  have hAη : A * (1 / η) = A / η := by ring
  rw [hAη] at hA1 hA2
  -- every bad `a` is caught by Proposition 1 or Proposition 2
  have hsplit := primCount_or d n hfin A
    (fun a => LocSet d n (wOf (A / η)) a ∧ ¬ HasRatZero d n a)
    (fun a => (1 / η) ^ ((2 : ℝ) / 3) < |NV d n a (A / η) - NVloc d n a (A / η)|)
    (fun a => LocSet d n (wOf (A / η)) a ∧ NVloc d n a (A / η) ≤ (1 / η) ^ ((2 : ℝ) / 3))
    (by
      intro a ⟨hloc, hnr⟩
      have hNV : NV d n a (A / η) = 0 := by
        unfold NV
        have : ({x ∈ Xi d n (A / η) | formEval d n a x = 0} : Set (Fin (n + 1) → ℤ)) = ∅ := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
          intro hx hx0
          apply hnr
          refine ⟨x, ?_, hx0⟩
          rintro rfl
          have h0 := hx.1
          unfold IsPrim at h0
          have hz : (Finset.univ : Finset (Fin (n + 1))).gcd (0 : Fin (n + 1) → ℤ) = 0 :=
            Finset.gcd_eq_zero_iff.2 (fun _ _ => rfl)
          rw [hz] at h0
          exact zero_ne_one h0
        rw [this]; simp
      by_cases hc : NVloc d n a (A / η) ≤ (1 / η) ^ ((2 : ℝ) / 3)
      · exact Or.inr ⟨hloc, hc⟩
      · left
        push Not at hc
        rw [hNV, zero_sub, abs_neg]
        exact lt_of_lt_of_le hc (le_abs_self _))
  have hκ : (0 : ℝ) < 1 / (24 * (n : ℝ)) := by
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hpow1 : (1 / η) ^ ((1 : ℝ) / 3) = (η ^ ((1 : ℝ) / 3))⁻¹ := by
    rw [one_div, Real.inv_rpow hη0.le]
  have hpow2 : (1 / η) ^ (1 / (24 * (n : ℝ))) = (η ^ (1 / (24 * (n : ℝ))))⁻¹ := by
    rw [one_div η, Real.inv_rpow hη0.le]
  have hcmp : η ^ ((1 : ℝ) / 3) ≤ η ^ (1 / (24 * (n : ℝ))) := by
    apply Real.rpow_le_rpow_of_exponent_ge hη0 hη1.le
    have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hAN : 0 ≤ A ^ NN d n := by positivity
  rw [hpow1, div_inv_eq_mul] at hA1
  rw [hpow2, div_inv_eq_mul] at hA2
  calc primCount d n A (fun a => LocSet d n (wOf (A / η)) a ∧ ¬ HasRatZero d n a)
      ≤ K1 * A ^ NN d n * η ^ ((1 : ℝ) / 3) + K2 * A ^ NN d n * η ^ (1 / (24 * (n : ℝ))) :=
        hsplit.trans (add_le_add hA1 hA2)
    _ ≤ K1 * A ^ NN d n * η ^ (1 / (24 * (n : ℝ))) + K2 * A ^ NN d n * η ^ (1 / (24 * (n : ℝ))) := by
        gcongr
    _ = (K1 + K2) * A ^ NN d n * η ^ (1 / (24 * (n : ℝ))) := by ring

/-- The main result, on primitive coefficient vectors. -/
theorem main (d n : ℕ) (hd : 2 ≤ d) (h₁ : d ≤ n) (h₂ : (d, n) ≠ (3, 3)) :
    Tendsto (HassePrincipleRandomFano.ρ d n) atTop (nhds (HassePrincipleRandomFano.ρLoc d n)) := by
  obtain ⟨hρ, hloc, hRA, hAL⟩ := bridge d n hd
  obtain ⟨hfin, c, hc, hcount⟩ := count_basic d n hd h₁
  have hρLoc : HassePrincipleRandomFano.ρLoc d n = atTop.limUnder (fun A => ratio d n A (AdelicSol d n)) := by
    unfold HassePrincipleRandomFano.ρLoc
    congr 1
    funext A
    exact hloc A
  have hρfun : HassePrincipleRandomFano.ρ d n = fun A => ratio d n A (HasRatZero d n) := funext hρ
  -- it suffices to find `L` with `ρ → L` and `loc → L`
  suffices H : ∃ L : ℝ, Tendsto (fun A => ratio d n A (HasRatZero d n)) atTop (nhds L) ∧
      Tendsto (fun A => ratio d n A (AdelicSol d n)) atTop (nhds L) by
    obtain ⟨L, hL1, hL2⟩ := H
    rw [hρLoc, hL2.limUnder_eq, hρfun]
    exact hL1
  have hRA_le : ∀ A, ratio d n A (HasRatZero d n) ≤ ratio d n A (AdelicSol d n) :=
    fun A => ratio_mono d n hfin A hRA
  by_cases h22 : (d, n) = (2, 2)
  · -- conics
    obtain ⟨rfl, rfl⟩ : d = 2 ∧ n = 2 := by simpa using h22
    refine ⟨0, ?_, ?_⟩
    · have hup : ∀ A, ratio 2 2 A (HasRatZero 2 2)
          ≤ ratio 2 2 A (fun a => ∀ p : ℕ, p.Prime → PrimModZero 2 2 a p 2) :=
        fun A => (hRA_le A).trans (ratio_mono 2 2 hfin A (fun a ha p hp => (hAL a ha).2 p 2 hp))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds conics
        (fun A => ratio_nonneg 2 2 A _) hup
    · have hup : ∀ A, ratio 2 2 A (AdelicSol 2 2)
          ≤ ratio 2 2 A (fun a => ∀ p : ℕ, p.Prime → PrimModZero 2 2 a p 2) :=
        fun A => ratio_mono 2 2 hfin A (fun a ha p hp => (hAL a ha).2 p 2 hp)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds conics
        (fun A => ratio_nonneg 2 2 A _) hup
  · have hn3 : 3 ≤ n := by
      by_contra hlt
      apply h22
      have : n = 2 := by omega
      have : d = 2 := by omega
      simp [*]
    obtain ⟨L, hL⟩ := density d n hd hn3
    obtain ⟨K, hK, hmost⟩ := hasse_most d n hd h₁ h22 h₂
    have hκ : (0 : ℝ) < 1 / (24 * (n : ℝ)) := by
      have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      positivity
    -- the upper envelope: `loc(A) ≤ ratio(LocSet(w(A/η)))`
    have hloc_le : ∀ η A, ratio d n A (AdelicSol d n) ≤ ratio d n A (LocSet d n (wOf (A / η))) :=
      fun η A => ratio_mono d n hfin A (fun a ha =>
        ⟨(hAL a ha).1, fun p hp _ => (hAL a ha).2 p _ hp⟩)
    -- the lower envelope: `ρ(A) ≥ ratio(LocSet(w(A/η))) - (K/c) η^κ`
    have hlow : ∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ A in atTop,
        ratio d n A (LocSet d n (wOf (A / η))) - K / c * η ^ (1 / (24 * (n : ℝ)))
          ≤ ratio d n A (HasRatZero d n) := by
      intro η hη0 hη1
      filter_upwards [hmost η hη0 hη1, hcount, eventually_gt_atTop (0 : ℝ)] with A hA hcA hA0
      have hP : 0 < primCount d n A (fun _ => True) :=
        lt_of_lt_of_le (by positivity) hcA
      have hsplit := primCount_or d n hfin A (LocSet d n (wOf (A / η)))
        (HasRatZero d n) (fun a => LocSet d n (wOf (A / η)) a ∧ ¬ HasRatZero d n a)
        (fun a ha => by
          by_cases h : HasRatZero d n a
          · exact Or.inl h
          · exact Or.inr ⟨ha, h⟩)
      have hbad : primCount d n A (fun a => LocSet d n (wOf (A / η)) a ∧ ¬ HasRatZero d n a)
          / primCount d n A (fun _ => True) ≤ K / c * η ^ (1 / (24 * (n : ℝ))) := by
        rw [div_le_iff₀ hP]
        calc _ ≤ K * A ^ NN d n * η ^ (1 / (24 * (n : ℝ))) := hA
          _ = K / c * η ^ (1 / (24 * (n : ℝ))) * (c * A ^ NN d n) := by
              field_simp
          _ ≤ K / c * η ^ (1 / (24 * (n : ℝ))) * primCount d n A (fun _ => True) := by
              gcongr
      unfold ratio
      have h3 := div_le_div_of_nonneg_right hsplit hP.le
      rw [add_div] at h3
      linarith
    -- choose `η` small enough for a given `ε`
    have hchoose : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ η < 1 ∧ K / c * η ^ (1 / (24 * (n : ℝ))) < ε := by
      intro ε hε
      have ht : Tendsto (fun η : ℝ => K / c * η ^ (1 / (24 * (n : ℝ)))) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (K / c * 0)) := by
        apply Tendsto.const_mul
        have := (Real.continuousAt_rpow_const 0 (1 / (24 * (n : ℝ))) (Or.inr hκ.le)).tendsto
        rw [Real.zero_rpow hκ.ne'] at this
        exact this.mono_left nhdsWithin_le_nhds
      rw [mul_zero] at ht
      have hev := (ht.eventually (gt_mem_nhds hε)).and
        ((Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)))
      obtain ⟨η, hη1, hη2⟩ := hev.exists
      exact ⟨η, hη2.1, hη2.2, hη1⟩
    have hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ A in atTop, ratio d n A (AdelicSol d n) < L + ε := by
      intro ε hε
      have := (hL _ (wOf_div_tendsto (1 / 2) (by norm_num)) (wOf_div_le (1 / 2) (by norm_num))).eventually (gt_mem_nhds (show L < L + ε by linarith))
      filter_upwards [this] with A hA
      exact lt_of_le_of_lt (hloc_le _ A) hA
    have hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ A in atTop, L - ε < ratio d n A (HasRatZero d n) := by
      intro ε hε
      obtain ⟨η, hη0, hη1, hηε⟩ := hchoose (ε / 2) (by positivity)
      have h1 := (hL _ (wOf_div_tendsto η hη0) (wOf_div_le η hη0)).eventually
        (lt_mem_nhds (show L - ε / 2 < L by linarith))
      filter_upwards [h1, hlow η hη0 hη1] with A hA1 hA2
      linarith
    refine ⟨L, ?_, ?_⟩
    · rw [tendsto_order]
      refine ⟨fun a ha => ?_, fun a ha => ?_⟩
      · filter_upwards [hlower (L - a) (by linarith)] with A hA
        linarith
      · filter_upwards [hupper (a - L) (by linarith)] with A hA
        linarith [hRA_le A]
    · rw [tendsto_order]
      refine ⟨fun a ha => ?_, fun a ha => ?_⟩
      · filter_upwards [hlower (L - a) (by linarith)] with A hA
        linarith [hRA_le A]
      · filter_upwards [hupper (a - L) (by linarith)] with A hA
        linarith

end Work.HP

namespace Submission

open HassePrincipleRandomFano
open MvPolynomial Filter NumberField Real
open scoped LinearAlgebra.Projectivization

variable (d n : ℕ)

theorem theorem_1_1 (hd : 2 ≤ d) (h₁ : d ≤ n) (h₂ : (d, n) ≠ (3, 3)) :
    Tendsto (ρ d n) atTop (nhds (ρLoc d n)) :=
  Work.HP.main d n hd h₁ h₂

end Submission
