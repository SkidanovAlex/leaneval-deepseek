import Submission.DS.CatlinDiv
import Submission.DS.RadAtt
import Submission.DS.Inclusion

open scoped Nat ENNReal NNReal
open Set MeasureTheory
open DuffinSchaefferConjecture

/-!
# Direction 1 of the paper's §2 equality `𝒜 ξ ∖ ℚ = 𝒦 ψ ∖ ℚ`

Given `ψ ≤ 1/2` and `x ∈ 𝒜 ξ` (with `ξ(q)/q = mRho(q)` the attained sup-radius),
every coprime solution pair `(a, q)` of `|x − a/q| ≤ ξ(q)/q` lifts, via the attained
multiple `n_q` of `q`, to a solution pair `(a·(n_q/q), n_q)` of `|x − m/n| ≤ ψ(n)/n`.
This gives an injective map from the infinite `𝒜 ξ`-pair set into the `𝒦 ψ`-pair set,
hence `𝒜 ξ ⊆ 𝒦 ψ`.
-/

namespace Submission.DS

variable {ψ : ℕ+ → ℝ≥0}

/-- The pair set underlying `𝒜 χ`. -/
def APair (χ : ℕ+ → ℝ≥0) (x : ℝ) : Set (ℕ × ℕ+) :=
  {(a, q) : ℕ × ℕ+ | Nat.Coprime a q ∧ inequality_1_7 χ x a q}

lemma mem_A_iff (χ : ℕ+ → ℝ≥0) (x : ℝ) :
    x ∈ 𝒜 χ ↔ x ∈ Set.Icc 0 1 ∧ (APair χ x).Infinite := by
  rfl

/-- `(mRho ψ q : ℝ) ≤ (1/2)/q` (real version). -/
lemma mRho_real_le (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0)) (q : ℕ+) :
    (mRho ψ q : ℝ) ≤ (1 / 2 : ℝ) / (q : ℝ) := by
  have h := mRho_le_half_div hle q
  have hR : ((mRho ψ q : NNReal) : ℝ) ≤ (((1 / 2 : NNReal) / q : NNReal) : ℝ) := by
    exact_mod_cast h
  rwa [NNReal.coe_div] at hR

/-- `ξ(q)/q` as a real number equals `mRho ψ q`. -/
lemma xi_div_self_real (q : ℕ+) : ((xi ψ q / q : NNReal) : ℝ) = (mRho ψ q : ℝ) := by
  exact congrArg (fun t : NNReal => (t : ℝ)) (xi_div_self (ψ := ψ) q)

/-- A solution of the `ξ`-inequality with `x ≤ 1` has numerator `≤ q`. -/
lemma num_le_q_of_xi (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0)) {x : ℝ} {a : ℕ} {q : ℕ+}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (h : inequality_1_7 (xi ψ) x a q) : a ≤ (q : ℕ) := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast PNat.pos q
  have hxiR : (xi ψ q : ℝ) / (q : ℝ) = (mRho ψ q : ℝ) := by
    simpa [NNReal.coe_div] using (xi_div_self_real (q := q))
  have hm : |x - (a : ℝ) / (q : ℝ)| ≤ (mRho ψ q : ℝ) := by
    unfold inequality_1_7 at h
    rw [hxiR] at h
    exact h
  have hleR : (mRho ψ q : ℝ) ≤ (1 / 2 : ℝ) / (q : ℝ) := mRho_real_le hle q
  have habs : |x - (a : ℝ) / (q : ℝ)| ≤ (1 / 2 : ℝ) / (q : ℝ) := le_trans hm hleR
  -- upper bound on a
  have haq : (a : ℝ) / (q : ℝ) ≤ x + (1 / 2 : ℝ) / (q : ℝ) := by
    rw [abs_le] at habs
    nlinarith [habs.1]
  have ha : (a : ℝ) ≤ (q : ℝ) * x + 1 / 2 := by
    have h1 : (a : ℝ) / (q : ℝ) * (q : ℝ) ≤ (x + (1 / 2 : ℝ) / (q : ℝ)) * (q : ℝ) :=
      mul_le_mul_of_nonneg_right haq (le_of_lt hq0)
    have h2 : (a : ℝ) / (q : ℝ) * (q : ℝ) = (a : ℝ) := by field_simp [hq0.ne']
    have h3 : (x + (1 / 2 : ℝ) / (q : ℝ)) * (q : ℝ) = x * (q : ℝ) + 1 / 2 := by
      rw [add_mul]
      field_simp [hq0.ne']
    rw [h2, h3] at h1
    nlinarith
  have hhalf : (1 / 2 : ℝ) < 1 := by norm_num
  have ha' : (a : ℝ) < (q : ℝ) + 1 := by
    nlinarith [hx1, hhalf, hq0]
  have haN : a < (q : ℕ) + 1 := by exact_mod_cast ha'
  omega

section lift

/-- An attained-multiple selector: `w q` is a multiple of `q` realizing `rad ψ q`. -/
noncomputable def witQ (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0)) (q : ℕ+) : ℕ+ :=
  Classical.choose (rad_att hle q)

lemma witQ_dvd (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0)) (q : ℕ+) : q ∣ witQ hle q :=
  (Classical.choose_spec (rad_att hle q)).1

lemma witQ_value (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0)) (q : ℕ+) :
    rad ψ q = (ψ (witQ hle q) : ℝ≥0∞) / ((witQ hle q) : ℝ≥0∞) :=
  (Classical.choose_spec (rad_att hle q)).2

/-- `k q = (witQ q)/q`, an integer with `q·k = witQ`. -/
noncomputable def liftK (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0)) (q : ℕ+) : ℕ :=
  (witQ hle q : ℕ) / (q : ℕ)

lemma q_mul_liftK (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0)) (q : ℕ+) :
    (q : ℕ) * liftK hle q = (witQ hle q : ℕ) := by
  have hdvd : (q : ℕ) ∣ (witQ hle q : ℕ) := (PNat.dvd_iff).mp (witQ_dvd hle q)
  have h := Nat.div_mul_cancel hdvd
  -- (wit/q)·q = wit; need q·(wit/q) = wit: commutativity
  rwa [mul_comm] at h

/-- The lifted numerator `a·k q`. -/
noncomputable def liftA (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0)) (a : ℕ) (q : ℕ+) : ℕ :=
  a * liftK hle q

/-- Lifted pairs stay in the `m ≤ n` regime. -/
lemma liftA_le (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0)) {a : ℕ} {q : ℕ+} (haq : a ≤ (q : ℕ)) :
    liftA hle a q ≤ (witQ hle q : ℕ) := by
  have hk : (q : ℕ) * liftK hle q = (witQ hle q : ℕ) := q_mul_liftK hle q
  calc
    liftA hle a q = a * liftK hle q := rfl
    _ ≤ (q : ℕ) * liftK hle q := by
      exact Nat.mul_le_mul_right (liftK hle q) haq
    _ = (witQ hle q : ℕ) := hk

/-- The lifted fraction has the same value as the original. -/
lemma lift_value (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0)) {a : ℕ} {q : ℕ+} :
    ((liftA hle a q : ℝ) / (witQ hle q : ℝ)) = (a : ℝ) / (q : ℝ) := by
  have hk : (q : ℕ) * liftK hle q = (witQ hle q : ℕ) := q_mul_liftK hle q
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt q.2)
  have hn0 : ((witQ hle q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (witQ hle q).2)
  have hnat : liftA hle a q * (q : ℕ) = a * (witQ hle q : ℕ) := by
    calc
      liftA hle a q * (q : ℕ) = (a * liftK hle q) * (q : ℕ) := rfl
      _ = a * (liftK hle q * (q : ℕ)) := by ring
      _ = a * (witQ hle q : ℕ) := by rw [mul_comm (liftK hle q) (q : ℕ), ← hk]
  rw [div_eq_div_iff hn0 hq0]
  exact_mod_cast hnat

/-- If `ψ ≤ 1/2`, `mRho q = rad q = ψ(witQ q)/(witQ q)`, i.e. the lift witnesses the sup. -/
lemma mRho_eq_wit (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0)) (q : ℕ+) :
    mRho ψ q = ψ (witQ hle q) / (witQ hle q : NNReal) := by
  have hrad : rad ψ q = (mRho ψ q : ℝ≥0∞) := rad_eq_coe_mRho hle q
  have hw : rad ψ q = (ψ (witQ hle q) : ℝ≥0∞) / ((witQ hle q) : ℝ≥0∞) := witQ_value hle q
  have hv : (ψ (witQ hle q) : ℝ≥0∞) / ((witQ hle q) : ℝ≥0∞) =
      ((ψ (witQ hle q) / (witQ hle q : NNReal) : NNReal) : ℝ≥0∞) := by
    rw [show (witQ hle q : ℝ≥0∞) = ((witQ hle q : NNReal) : ℝ≥0∞) by
      exact (by simp [ENNReal.coe_natCast] : ((witQ hle q : NNReal) : ℝ≥0∞) = (witQ hle q : ℝ≥0∞)).symm]
    exact (coe_div_ne_zero (ψ (witQ hle q)) ((witQ hle q : ℕ) : NNReal)
      (by exact_mod_cast (PNat.ne_zero (witQ hle q)))).symm
  have hEq : (mRho ψ q : ℝ≥0∞) = ((ψ (witQ hle q) / (witQ hle q : NNReal) : NNReal) : ℝ≥0∞) := by
    rw [← hrad, hw, hv]
  exact ENNReal.coe_inj.mp hEq

end lift


section inclusion

/-- Coprime pairs with equal real value coincide. -/
lemma coprime_pair_eq_of_eq {a1 a2 : ℕ} {q1 q2 : ℕ+} (hc1 : Nat.Coprime a1 (q1 : ℕ))
    (hc2 : Nat.Coprime a2 (q2 : ℕ)) (hval : (a1 : ℝ) / (q1 : ℝ) = (a2 : ℝ) / (q2 : ℝ)) :
    a1 = a2 ∧ (q1 : ℕ) = (q2 : ℕ) := by
  have hq10 : (q1 : ℕ) ≠ 0 := (q1 : ℕ+).2.ne'
  have hq20 : (q2 : ℕ) ≠ 0 := (q2 : ℕ+).2.ne'
  have hq1R : (q1 : ℝ) ≠ 0 := by exact_mod_cast hq10
  have hq2R : (q2 : ℝ) ≠ 0 := by exact_mod_cast hq20
  have hcross : a1 * (q2 : ℕ) = a2 * (q1 : ℕ) := by
    apply Nat.cast_injective (R := ℝ)
    have hmul : (a1 : ℝ) * (q2 : ℝ) = (a2 : ℝ) * (q1 : ℝ) := by
      rw [div_eq_div_iff hq1R hq2R] at hval
      exact hval
    simpa [Nat.cast_mul] using hmul
  have hq1dq2 : (q1 : ℕ) ∣ (q2 : ℕ) := by
    have hdv : (q1 : ℕ) ∣ a1 * (q2 : ℕ) := by
      rw [hcross]
      exact dvd_mul_left (q1 : ℕ) a2
    have hdv' : (q1 : ℕ) ∣ (q2 : ℕ) * a1 := by
      rwa [mul_comm]
    have hc1' : Nat.Coprime (q1 : ℕ) a1 := hc1.symm
    exact hc1'.dvd_of_dvd_mul_right hdv'
  have hq2dq1 : (q2 : ℕ) ∣ (q1 : ℕ) := by
    have hdv : (q2 : ℕ) ∣ a2 * (q1 : ℕ) := by
      rw [← hcross]
      exact dvd_mul_left (q2 : ℕ) a1
    have hdv' : (q2 : ℕ) ∣ (q1 : ℕ) * a2 := by
      rwa [mul_comm]
    have hc2' : Nat.Coprime (q2 : ℕ) a2 := hc2.symm
    exact hc2'.dvd_of_dvd_mul_right hdv'
  have hqeq : (q1 : ℕ) = (q2 : ℕ) := Nat.dvd_antisymm hq1dq2 hq2dq1
  have haeq : a1 = a2 := by
    rw [hqeq] at hcross
    -- a1·q2 = a2·q2 → a1 = a2
    exact Nat.eq_of_mul_eq_mul_right (show 0 < (q2 : ℕ) from (q2 : ℕ+).2) hcross
  exact ⟨haeq, hqeq⟩

/-- The lift map sends coprime `ξ`-solutions to `ψ`-solutions with `m ≤ n`. -/
lemma lift_mem_SolSet (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0)) {x : ℝ} {a : ℕ} {q : ℕ+}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hpair : (a, q) ∈ APair (xi ψ) x) :
    (liftA hle a q, witQ hle q) ∈ SolSet ψ x := by
  have hc : Nat.Coprime a (q : ℕ) := hpair.1
  have hineq : inequality_1_7 (xi ψ) x a q := hpair.2
  have haq : a ≤ (q : ℕ) := num_le_q_of_xi hle hx0 hx1 hineq
  constructor
  · exact liftA_le hle haq
  · unfold inequality_1_7
    have hxiR : (xi ψ q : ℝ) / (q : ℝ) = (mRho ψ q : ℝ) := by
      simpa [NNReal.coe_div] using (xi_div_self_real (q := q))
    have hR1 : |x - (liftA hle a q : ℝ) / (witQ hle q : ℝ)| ≤ (mRho ψ q : ℝ) := by
      rw [lift_value hle]
      unfold inequality_1_7 at hineq
      rw [hxiR] at hineq
      exact hineq
    have hmr : (mRho ψ q : ℝ) = (ψ (witQ hle q) : ℝ) / (witQ hle q : ℝ) := by
      have h := congrArg (fun t : NNReal => (t : ℝ)) (mRho_eq_wit hle q)
      simpa [NNReal.coe_div] using h
    simpa [hmr] using hR1

/-- A point in `[0,1]` with infinitely many `ψ`-solutions lies in `𝒦 ψ`. -/
lemma mem_K_of_SolSet_infinite (x : ℝ) (hx01 : x ∈ Set.Icc 0 1)
    (hQ : (SolSet ψ x).Infinite) : x ∈ 𝒦 ψ := by
  rw [mem_K_iff]
  refine ⟨hx01, ?_⟩
  have hEq : pairSet (Kfib ψ x) = SolSet ψ x := by
    unfold SolSet
    exact pairSet_Kfib ψ x
  have hPair : (pairSet (Kfib ψ x)).Infinite := by
    simpa [hEq] using hQ
  have hDen : (denomSet (Kfib ψ x)).Infinite :=
    (infinite_pairs_iff_infinite_denoms (Kfib ψ x) (Kfib_finite ψ x)).1 hPair
  have hEq2 : denomSet (Kfib ψ x) = {q : ℕ+ | x ∈ Bq ψ q} := by
    ext q
    simp [denomSet, Bq]
  change {q : ℕ+ | x ∈ Bq ψ q}.Infinite
  rwa [← hEq2]

/-- **Direction 1**: `𝒜 ξ ⊆ 𝒦 ψ` under `ψ ≤ 1/2`. -/
lemma Axi_subset_K (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0)) : 𝒜 (xi ψ) ⊆ 𝒦 ψ := by
  classical
  intro x hx
  have hx01 : x ∈ Set.Icc 0 1 := ((mem_A_iff (xi ψ) x).1 hx).1
  have hPinf : (APair (xi ψ) x).Infinite := ((mem_A_iff (xi ψ) x).1 hx).2
  have hQ : (SolSet ψ x).Infinite := by
    let T : ℕ × ℕ+ → ℕ × ℕ+ := fun p => (liftA hle p.1 p.2, witQ hle p.2)
    have hTimg : T '' APair (xi ψ) x ⊆ SolSet ψ x := by
      rintro p ⟨q, hq, rfl⟩
      exact lift_mem_SolSet hle hx01.1 hx01.2 hq
    have hTinj : Set.InjOn T (APair (xi ψ) x) := by
      intro p hp p' hp' hT
      have hw : witQ hle p.2 = witQ hle p'.2 := congrArg Prod.snd hT
      have hm : liftA hle p.1 p.2 = liftA hle p'.1 p'.2 := congrArg Prod.fst hT
      have hval : (p.1 : ℝ) / (p.2 : ℝ) = (p'.1 : ℝ) / (p'.2 : ℝ) := by
        calc
          (p.1 : ℝ) / (p.2 : ℝ) = (liftA hle p.1 p.2 : ℝ) / (witQ hle p.2 : ℝ) := (lift_value hle).symm
          _ = (liftA hle p'.1 p'.2 : ℝ) / (witQ hle p'.2 : ℝ) := by rw [hm, hw]
          _ = (p'.1 : ℝ) / (p'.2 : ℝ) := lift_value hle
      have hpq : p = p' := by
        rcases coprime_pair_eq_of_eq hp.1 hp'.1 hval with ⟨ha, hq⟩
        apply Prod.ext
        · exact ha
        · exact PNat.coe_injective hq
      exact hpq
    have hTinf : (T '' APair (xi ψ) x).Infinite := by
      intro hfin
      have hPfin : (APair (xi ψ) x).Finite := (Set.finite_image_iff hTinj).1 hfin
      exact hPinf hPfin
    exact Set.Infinite.mono hTimg hTinf
  exact mem_K_of_SolSet_infinite x hx01 hQ

/-- Full measure for `𝒜 ξ` transfers to `𝒦 ψ`. -/
lemma volume_K_of_Axi_full (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0))
    (_hAm : MeasurableSet (𝒜 (xi ψ))) (hAv : volume (𝒜 (xi ψ)) = 1) :
    volume (𝒦 ψ) = 1 := by
  classical
  have hsub := Axi_subset_K hle
  have hK01 : 𝒦 ψ ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact ((mem_K_iff ψ x).1 hx).1
  have hvol_le : volume (𝒦 ψ) ≤ 1 := by
    calc
      volume (𝒦 ψ) ≤ volume (Set.Icc (0 : ℝ) 1) := measure_mono hK01
      _ = 1 := by rw [Real.volume_Icc]; norm_num
  have hsub2 : 𝒜 (xi ψ) \ ratSet ⊆ 𝒦 ψ := by
    intro x hx
    exact hsub hx.1
  have hvolA : (1 : ℝ≥0∞) ≤ volume (𝒜 (xi ψ) \ ratSet) := by
    have hvol : volume (𝒜 (xi ψ)) ≤ volume (𝒜 (xi ψ) \ ratSet) + volume (𝒜 (xi ψ) ∩ ratSet) := by
      calc
        volume (𝒜 (xi ψ)) = volume ((𝒜 (xi ψ) \ ratSet) ∪ (𝒜 (xi ψ) ∩ ratSet)) := by
          congr 1
          ext x
          by_cases h : x ∈ ratSet <;> simp [h]
        _ ≤ volume (𝒜 (xi ψ) \ ratSet) + volume (𝒜 (xi ψ) ∩ ratSet) := measure_union_le _ _
    have hvolrat : volume (𝒜 (xi ψ) ∩ ratSet) = 0 := by
      apply le_antisymm _ bot_le
      exact (measure_mono (by intro x hx; exact hx.2)).trans_eq ratSet_volume_zero
    calc
      (1 : ℝ≥0∞) = volume (𝒜 (xi ψ)) := hAv.symm
      _ ≤ volume (𝒜 (xi ψ) \ ratSet) + volume (𝒜 (xi ψ) ∩ ratSet) := hvol
      _ = volume (𝒜 (xi ψ) \ ratSet) := by rw [hvolrat]; simp
  have hvol_ge : (1 : ℝ≥0∞) ≤ volume (𝒦 ψ) := le_trans hvolA (measure_mono hsub2)
  exact le_antisymm hvol_le hvol_ge

/-- **Theorem 2(b) restricted to `ψ ≤ 1/2`, assuming Theorem 1** (paper §2, Case 2). -/
theorem catlin_div_case2
    (hThm1 : ∀ (χ : ℕ+ → ℝ≥0),
      ¬ Summable (fun q => (χ q * φ q) / q) → MeasurableSet (𝒜 χ) ∧ volume (𝒜 χ) = 1)
    (ψ : ℕ+ → ℝ≥0) (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0))
    (hψ : (∑' q : ℕ+, ψ_star ψ q) = ∞) :
    MeasurableSet (𝒦 ψ) ∧ volume (𝒦 ψ) = 1 := by
  have hxi : ¬ Summable (fun q : ℕ+ => (xi ψ q * (φ q : NNReal)) / q) := not_summable_xi hle hψ
  rcases hThm1 (xi ψ) (by simpa using hxi) with ⟨hAm, hAv⟩
  constructor
  · exact measurableSet_K ψ
  · exact volume_K_of_Axi_full hle hAm hAv

end inclusion

