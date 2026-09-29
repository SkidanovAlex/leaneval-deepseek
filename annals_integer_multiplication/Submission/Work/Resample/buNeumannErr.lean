import Mathlib
import Submission.Work.Resample.buEroundW
import Submission.Work.Resample.buNeumann
import Submission.Work.Resample.buFixed

set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH

/-! ## Fixed-point linearity of the Neumann sum

`fxC p` is additive over the coordinate sums of `buJsum`, so that the fixed-point value of the
alternating integer sum is the alternating sum of the fixed-point values of the iterates. -/

/-- `fxC` commutes with a range sum of pairs (componentwise). -/
theorem buFxC_sum (p N : ℕ) (a b : ℕ → ℤ) :
    HvdH.fxC p ((∑ j ∈ Finset.range N, a j), (∑ j ∈ Finset.range N, b j)) =
      ∑ j ∈ Finset.range N, HvdH.fxC p (a j, b j) := by
  have h1 : (((∑ j ∈ Finset.range N, a j : ℤ) : ℂ) +
        ((∑ j ∈ Finset.range N, b j : ℤ) : ℂ) * Complex.I) =
      ∑ j ∈ Finset.range N, (((a j : ℤ) : ℂ) + ((b j : ℤ) : ℂ) * Complex.I) := by
    rw [Int.cast_sum, Int.cast_sum, Finset.sum_add_distrib, Finset.sum_mul]
  unfold HvdH.fxC
  rw [h1, Finset.sum_div]

/-- `fxC` commutes with the componentwise multiplication by an integer. -/
theorem buFxC_smul_int (p : ℕ) (c : ℤ) (z : ℤ × ℤ) :
    HvdH.fxC p (c * z.1, c * z.2) = (c : ℂ) * HvdH.fxC p z := by
  unfold HvdH.fxC
  push_cast
  ring

/-! ## Arithmetic on the parameters -/

/-- `egN p α s t ≤ α² + 1`: iteration count bound. -/
theorem buEgN_le_sq (s t α p : ℕ) (hs : 0 < s) (hst : s < t) (hα : 0 < α)
    (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) :
    (egN p α s t : ℝ) ≤ (α : ℝ) ^ 2 + 1 := by
  have hs0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hα0 : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
  have hts : (0 : ℝ) < (t : ℝ) - s := by
    have : (s : ℝ) < (t : ℝ) := by exact_mod_cast hst
    linarith
  have hden : (0 : ℝ) < (α : ℝ) ^ 2 * ((t : ℝ) - s) := mul_pos (by positivity) hts
  have key : (p : ℝ) * s ≤ (α : ℝ) ^ 4 * ((t : ℝ) - s) := by
    have h1 : (p : ℝ) ≤ (α : ℝ) ^ 4 * ((t : ℝ) / s - 1) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (α : ℝ) ^ 4)] at hθ
      linarith
    have h2 : ((t : ℝ) / s - 1) * s = (t : ℝ) - s := by
      field_simp
    have h3 : (p : ℝ) * s ≤ (α : ℝ) ^ 4 * (((t : ℝ) / s - 1) * s) := by
      have := mul_le_mul_of_nonneg_right h1 (le_of_lt hs0)
      linarith [this]
    rw [h2] at h3
    exact h3
  have hnatdiv : (((p * s - 1) / (α ^ 2 * (t - s)) : ℕ) : ℝ) ≤
      (p : ℝ) * s / ((α : ℝ) ^ 2 * ((t : ℝ) - s)) := by
    have h3 : (0 : ℝ) < ((α ^ 2 * (t - s) : ℕ) : ℝ) := by
      have : 0 < α ^ 2 * (t - s) := Nat.mul_pos (pow_pos hα 2) (Nat.sub_pos_of_lt hst)
      exact_mod_cast this
    have h4 : ((α ^ 2 * (t - s) : ℕ) : ℝ) = (α : ℝ) ^ 2 * ((t : ℝ) - s) := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (le_of_lt hst)]
    calc (((p * s - 1) / (α ^ 2 * (t - s)) : ℕ) : ℝ)
        ≤ ((p * s - 1 : ℕ) : ℝ) / ((α ^ 2 * (t - s) : ℕ) : ℝ) := Nat.cast_div_le
      _ ≤ ((p * s : ℕ) : ℝ) / ((α ^ 2 * (t - s) : ℕ) : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ (le_of_lt h3)
          have := Nat.sub_le (p * s) 1
          exact_mod_cast this
      _ = (p : ℝ) * s / ((α : ℝ) ^ 2 * ((t : ℝ) - s)) := by
          rw [h4, Nat.cast_mul]
  have h5 : (p : ℝ) * s / ((α : ℝ) ^ 2 * ((t : ℝ) - s)) ≤ (α : ℝ) ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [key]
  rw [egN]
  push_cast
  linarith

/-- `egM p α ≤ √p/(2α) + 1`. -/
theorem buEgM_le_sqrt (p α : ℕ) (hα : 0 < α) :
    (egM p α : ℝ) ≤ Real.sqrt p / (2 * (α : ℝ)) + 1 := by
  have hα0 : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
  have hnat : ((Nat.sqrt p : ℕ) : ℝ) ≤ Real.sqrt p := by
    have h2 : ((Nat.sqrt p : ℕ) : ℝ) ^ 2 ≤ (p : ℝ) := by
      have := Nat.sqrt_le' p
      push_cast [pow_two] at this ⊢
      exact_mod_cast this
    calc ((Nat.sqrt p : ℕ) : ℝ) = Real.sqrt (((Nat.sqrt p : ℕ) : ℝ) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt p := Real.sqrt_le_sqrt h2
  have h1 : ((Nat.sqrt p / (2 * α) : ℕ) : ℝ) ≤ (Nat.sqrt p : ℝ) / ((2 * α : ℕ) : ℝ) :=
    Nat.cast_div_le
  have h1' : (Nat.sqrt p : ℝ) / ((2 * α : ℕ) : ℝ) = (Nat.sqrt p : ℝ) / (2 * (α : ℝ)) := by
    push_cast
    ring
  rw [egM]
  push_cast
  rw [h1'] at h1
  have h2 : (0 : ℝ) ≤ 2 * (α : ℝ) := by linarith
  have h3 : (Nat.sqrt p : ℝ) / (2 * (α : ℝ)) ≤ Real.sqrt p / (2 * (α : ℝ)) :=
    div_le_div_of_nonneg_right hnat h2
  linarith

/-- The polynomial-vs-exponential estimate behind the disc bound. -/
theorem buPoly_two_pow (p : ℕ) (hp : 100 ≤ p) : 8 * (18 * p ^ 2 + 37 * p + 1) ≤ 2 ^ p := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    rw [h1]
    nlinarith [ih]

/-- Numerical core of the disc preservation: `(1 + n(19+18m))·2^{-p} ≤ 1/8`. -/
theorem buNumBound (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (hαp : α ^ 2 < p) (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) :
    (1 + (egN p α s t : ℝ) * (19 + 18 * (egM p α : ℝ))) / (2 : ℝ) ^ p ≤ 1 / 8 := by
  have hs0 : (0 : ℕ) < s := by omega
  have hα0 : (0 : ℕ) < α := by omega
  have hn : (egN p α s t : ℝ) ≤ (α : ℝ) ^ 2 + 1 := buEgN_le_sq s t α p hs0 hst hα0 hθ
  have hm : (egM p α : ℝ) ≤ Real.sqrt p / (2 * (α : ℝ)) + 1 := buEgM_le_sqrt p α hα0
  have hsp : Real.sqrt (p : ℝ) ≤ (p : ℝ) :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast (by omega : 1 ≤ p)))
  have hN : (egN p α s t : ℝ) ≤ (p : ℝ) := by
    have h1 : (α : ℝ) ^ 2 + 1 ≤ (p : ℝ) := by
      have : α ^ 2 + 1 ≤ p := by omega
      exact_mod_cast this
    linarith
  have hM : 19 + 18 * (egM p α : ℝ) ≤ 37 + 18 * (p : ℝ) := by
    have hα2 : (2 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα
    have h1 : (egM p α : ℝ) ≤ Real.sqrt (p : ℝ) + 1 := by
      have h2 : Real.sqrt (p : ℝ) / (2 * (α : ℝ)) ≤ Real.sqrt (p : ℝ) := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (α : ℝ))]
        nlinarith [Real.sqrt_nonneg (p : ℝ), hα2]
      linarith
    linarith
  have hb : 1 + (egN p α s t : ℝ) * (19 + 18 * (egM p α : ℝ))
      ≤ 18 * (p : ℝ) ^ 2 + 37 * (p : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ 19 + 18 * (egM p α : ℝ) := by positivity
    have h1 := mul_le_mul hN hM h0 (by positivity : (0 : ℝ) ≤ (p : ℝ))
    nlinarith [h1]
  have h8 : 8 * (18 * (p : ℝ) ^ 2 + 37 * (p : ℝ) + 1) ≤ (2 : ℝ) ^ p := by
    have h := buPoly_two_pow p hp
    exact_mod_cast h
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ p)]
  nlinarith [hb, h8]

/-! ## The main estimate -/

theorem buNeumannErr (RM : HvdH.ResMath1DProp) (p α s t : ℕ) (hs : 2 ≤ s) (hs0 : 0 < s)
    (hst : s < t) (hcop : Nat.Coprime s t) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
    (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1)
    (hwacc : ∀ (ℓ h : ℤ), h ∈ Work.Resample.egHset (Work.Resample.egM p α) →
      |(Work.Resample.buWt p α s t ℓ h : ℝ) / (2 : ℝ) ^ p - Work.Resample.egW s t α ℓ h|
        ≤ 4 / (2 : ℝ) ^ p)
    (hrow : ∀ (ℓ : Fin s) (x : Fin s → ℂ),
      ((HvdH.Emat s t α).mulVec x) ℓ = ∑' h : ℤ, (if h = 0 then 0 else
          ((Work.Resample.egW s t α (ℓ : ℤ) h : ℝ) : ℂ) * x (Work.Resample.egIdx s hs0 ((ℓ : ℤ) + h))))
    (htail : ∀ ℓ : Fin s,
      ∑' h : ℤ, (if Work.Resample.egM p α < h.natAbs then |Work.Resample.egW s t α (ℓ : ℤ) h| else 0)
        ≤ 3 / (2 : ℝ) ^ p)
    (z : Fin s → ℤ × ℤ) (hz : ∀ ℓ, HvdH.inDisc p (z ℓ)) :
    (∀ ℓ, (2 : ℝ) ^ p * ‖HvdH.fxC p (Work.Resample.buJsum (Work.Resample.buWt p α s t) p α s t hs0
          (fun ℓ => (Int.tdiv (z ℓ).1 2, Int.tdiv (z ℓ).2 2)) ℓ)
        - ((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec (fun ℓ => HvdH.fxC p (z ℓ)))) ℓ‖
      ≤ 1 + (Work.Resample.egN p α s t : ℝ) * (18 * (Work.Resample.egM p α : ℝ) + 24)) ∧
    (∀ ℓ, ‖HvdH.fxC p (Work.Resample.buJsum (Work.Resample.buWt p α s t) p α s t hs0
          (fun ℓ => (Int.tdiv (z ℓ).1 2, Int.tdiv (z ℓ).2 2)) ℓ)‖ ≤ 1) := by
  classical
  obtain ⟨-, -, hE, -, -, hJhalf, -, -⟩ := RM s t α p hs hst hcop hα hαp hθ
  have hnum := buNumBound p α s t hs hst hα hp hαp hθ
  set Z : Fin s → ℂ := fun ℓ => HvdH.fxC p (z ℓ) with hZdef
  set v0 : Fin s → ℤ × ℤ := fun ℓ => (Int.tdiv (z ℓ).1 2, Int.tdiv (z ℓ).2 2) with hv0def
  have hZnorm : ‖Z‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr (fun ℓ => ?_)
    exact Work.ConvR.norm_fxC_le_one (hz ℓ)
  have hhalf : (1 / 2 : ℂ) • Z = fun ℓ => Z ℓ / 2 := by
    funext ℓ
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hv0disc : ∀ ℓ : Fin s, HvdH.inDisc p (v0 ℓ) :=
    fun ℓ => (buFixed p α s t hα (z ℓ) (hz ℓ) ℓ).1.1
  have hv0err : ∀ ℓ : Fin s, (2 : ℝ) ^ p * ‖HvdH.fxC p (v0 ℓ) - HvdH.fxC p (z ℓ) / 2‖ ≤ 1 :=
    fun ℓ => (buFixed p α s t hα (z ℓ) (hz ℓ) ℓ).1.2
  -- ### (A)  the iterates stay in the disc and track the ideal Neumann trajectory
  have hiter : ∀ j : ℕ,
      (∀ ℓ : Fin s, HvdH.inDisc p (buIter (buWt p α s t) p α s t hs0 v0 j ℓ)) ∧
      (∀ ℓ : Fin s, (2 : ℝ) ^ p * ‖HvdH.fxC p (buIter (buWt p α s t) p α s t hs0 v0 j ℓ)
          - ((1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ j).mulVec Z)) ℓ‖
          ≤ 19 + 18 * (egM p α : ℝ)) := by
    intro j
    induction j with
    | zero =>
        constructor
        · intro ℓ
          simpa only [buIter] using hv0disc ℓ
        · intro ℓ
          have h2 : (1 : ℝ) ≤ 19 + 18 * (egM p α : ℝ) := by
            have : (0 : ℝ) ≤ (egM p α : ℝ) := Nat.cast_nonneg _
            linarith
          have h3 : (2 : ℝ) ^ p * ‖HvdH.fxC p (v0 ℓ) - HvdH.fxC p (z ℓ) / 2‖
              ≤ 19 + 18 * (egM p α : ℝ) := le_trans (hv0err ℓ) h2
          simp only [buIter, pow_zero, Matrix.one_mulVec]
          rw [hhalf]
          exact h3
    | succ j ih =>
        obtain ⟨ihd, ihe⟩ := ih
        set yj : Fin s → ℂ := fun k => HvdH.fxC p (buIter (buWt p α s t) p α s t hs0 v0 j k) with hyj
        have hyjn : ∀ k : Fin s, ‖yj k‖ ≤ 1 := fun k => Work.ConvR.norm_fxC_le_one (ihd k)
        have he0 : ∀ k : Fin s, (2 : ℝ) ^ p * ‖HvdH.fxC p
            (buIter (buWt p α s t) p α s t hs0 v0 j k) - yj k‖ ≤ 0 := by
          intro k
          have hk : yj k = HvdH.fxC p (buIter (buWt p α s t) p α s t hs0 v0 j k) := by
            rw [hyj]
          rw [hk, sub_self, norm_zero, mul_zero]
        obtain ⟨hd, herr⟩ := buEroundW RM p α s t hs hs0 hst hcop hα hp hαp hθ
          (buWt p α s t) 4 (by norm_num) (by norm_num) hwacc hrow htail
          (buIter (buWt p α s t) p α s t hs0 v0 j) ihd yj hyjn 0 he0
        constructor
        · intro ℓ
          show HvdH.inDisc p (buRound (buWt p α s t) p α s t hs0
            (buIter (buWt p α s t) p α s t hs0 v0 j) ℓ)
          exact hd ℓ
        · intro ℓ
          show (2 : ℝ) ^ p * ‖HvdH.fxC p (buRound (buWt p α s t) p α s t hs0
              (buIter (buWt p α s t) p α s t hs0 v0 j) ℓ)
              - ((1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ (j + 1)).mulVec Z)) ℓ‖
              ≤ 19 + 18 * (egM p α : ℝ)
          have h2p : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
          have hCn : ‖yj - (1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ j).mulVec Z)‖
              ≤ (19 + 18 * (egM p α : ℝ)) / (2 : ℝ) ^ p := by
            refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun k => ?_)
            rw [le_div_iff₀ h2p]
            have h' : ‖HvdH.fxC p (buIter (buWt p α s t) p α s t hs0 v0 j k)
                  - ((1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ j).mulVec Z)) k‖
                  * (2 : ℝ) ^ p ≤ 19 + 18 * (egM p α : ℝ) := by
              have h := ihe k
              linarith [h]
            exact h'
          have hdev : (HvdH.Emat s t α).mulVec yj
              - (1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ (j + 1)).mulVec Z)
              = (HvdH.Emat s t α).mulVec
                  (yj - (1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ j).mulVec Z)) := by
            rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_succ']
          have hEℓ : (2 : ℝ) ^ p * ‖(HvdH.Emat s t α).mulVec yj ℓ
              - ((1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ (j + 1)).mulVec Z)) ℓ‖
              ≤ (21 / 50) * (19 + 18 * (egM p α : ℝ)) := by
            have hdevℓ : (HvdH.Emat s t α).mulVec yj ℓ
                - ((1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ (j + 1)).mulVec Z)) ℓ
                = ((HvdH.Emat s t α).mulVec
                    (yj - (1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ j).mulVec Z))) ℓ :=
              congrFun hdev ℓ
            rw [hdevℓ]
            have h1 : ‖((HvdH.Emat s t α).mulVec
                  (yj - (1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ j).mulVec Z))) ℓ‖
                ≤ 21 / 50 * ((19 + 18 * (egM p α : ℝ)) / (2 : ℝ) ^ p) := by
              refine le_trans (norm_le_pi_norm _ ℓ) (le_trans (hE _) ?_)
              exact mul_le_mul_of_nonneg_left hCn (by norm_num)
            calc (2 : ℝ) ^ p * ‖((HvdH.Emat s t α).mulVec
                    (yj - (1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ j).mulVec Z))) ℓ‖
                ≤ (2 : ℝ) ^ p * (21 / 50 * ((19 + 18 * (egM p α : ℝ)) / (2 : ℝ) ^ p)) :=
                  mul_le_mul_of_nonneg_left h1 h2p.le
              _ = (21 / 50) * (19 + 18 * (egM p α : ℝ)) := by field_simp
          have hstep : (9 * (egM p α : ℝ) + 12)
              + (21 / 50) * (19 + 18 * (egM p α : ℝ)) ≤ 19 + 18 * (egM p α : ℝ) := by
            have hM1 : (1 : ℝ) ≤ (egM p α : ℝ) := by
              have h1 : 1 ≤ egM p α := by
                show 1 ≤ Nat.sqrt p / (2 * α) + 1
                exact Nat.succ_le_succ (Nat.zero_le _)
              exact_mod_cast h1
            nlinarith
          have htri : (2 : ℝ) ^ p * ‖HvdH.fxC p (buRound (buWt p α s t) p α s t hs0
                (buIter (buWt p α s t) p α s t hs0 v0 j) ℓ)
                - ((1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ (j + 1)).mulVec Z)) ℓ‖
              ≤ (2 : ℝ) ^ p * (‖HvdH.fxC p (buRound (buWt p α s t) p α s t hs0
                      (buIter (buWt p α s t) p α s t hs0 v0 j) ℓ)
                    - (HvdH.Emat s t α).mulVec yj ℓ‖
                  + ‖(HvdH.Emat s t α).mulVec yj ℓ
                    - ((1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ (j + 1)).mulVec Z)) ℓ‖) := by
            gcongr
            rw [show HvdH.fxC p (buRound (buWt p α s t) p α s t hs0
                    (buIter (buWt p α s t) p α s t hs0 v0 j) ℓ)
                  - ((1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ (j + 1)).mulVec Z)) ℓ
                = (HvdH.fxC p (buRound (buWt p α s t) p α s t hs0
                      (buIter (buWt p α s t) p α s t hs0 v0 j) ℓ)
                    - (HvdH.Emat s t α).mulVec yj ℓ)
                  + ((HvdH.Emat s t α).mulVec yj ℓ
                    - ((1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ (j + 1)).mulVec Z)) ℓ) by ring]
            exact norm_add_le _ _
          have h1 := herr ℓ
          calc (2 : ℝ) ^ p * ‖HvdH.fxC p (buRound (buWt p α s t) p α s t hs0
                  (buIter (buWt p α s t) p α s t hs0 v0 j) ℓ)
                  - ((1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ (j + 1)).mulVec Z)) ℓ‖
              ≤ (2 : ℝ) ^ p * (‖HvdH.fxC p (buRound (buWt p α s t) p α s t hs0
                        (buIter (buWt p α s t) p α s t hs0 v0 j) ℓ)
                      - (HvdH.Emat s t α).mulVec yj ℓ‖
                    + ‖(HvdH.Emat s t α).mulVec yj ℓ
                      - ((1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ (j + 1)).mulVec Z)) ℓ‖) := htri
            _ = (2 : ℝ) ^ p * ‖HvdH.fxC p (buRound (buWt p α s t) p α s t hs0
                      (buIter (buWt p α s t) p α s t hs0 v0 j) ℓ)
                    - (HvdH.Emat s t α).mulVec yj ℓ‖
                  + (2 : ℝ) ^ p * ‖(HvdH.Emat s t α).mulVec yj ℓ
                      - ((1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ (j + 1)).mulVec Z)) ℓ‖ := by ring
            _ ≤ (9 * (egM p α : ℝ) + 12) + (21 / 50) * (19 + 18 * (egM p α : ℝ)) := by
                linarith [h1, hEℓ]
            _ ≤ 19 + 18 * (egM p α : ℝ) := hstep
  -- ### (B)  alternating sum of the iterates
  set J : Fin s → ℤ × ℤ := buJsum (buWt p α s t) p α s t hs0 v0 with hJdef
  set J0 : Fin s → ℂ := ∑ j ∈ Finset.range (egN p α s t),
      ((-1 : ℂ) ^ j) • (((HvdH.Emat s t α) ^ j).mulVec ((1 / 2 : ℂ) • Z)) with hJ0def
  have hNeu := buNeumann RM p α s t hs hst hcop hα hp hαp hθ Z hZnorm
  have hJmatnorm : ‖((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z))‖ ≤ 7 / 8 := by
    have h1 : ‖((1 / 2 : ℂ) • HvdH.Jmat s t α).mulVec Z‖ ≤ 7 / 8 * ‖Z‖ := hJhalf Z
    rw [Matrix.smul_mulVec] at h1
    linarith [hZnorm]
  have hJsum_err : ∀ ℓ : Fin s, (2 : ℝ) ^ p * ‖HvdH.fxC p (J ℓ) - J0 ℓ‖
      ≤ (egN p α s t : ℝ) * (19 + 18 * (egM p α : ℝ)) := by
    intro ℓ
    have hfx : HvdH.fxC p (J ℓ) = ∑ j ∈ Finset.range (egN p α s t),
        ((-1 : ℂ) ^ j) * HvdH.fxC p (buIter (buWt p α s t) p α s t hs0 v0 j ℓ) := by
      show HvdH.fxC p ((∑ j ∈ Finset.range (egN p α s t),
            ((-1 : ℤ) ^ j) * (buIter (buWt p α s t) p α s t hs0 v0 j ℓ).1),
          (∑ j ∈ Finset.range (egN p α s t),
            ((-1 : ℤ) ^ j) * (buIter (buWt p α s t) p α s t hs0 v0 j ℓ).2)) = _
      rw [buFxC_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [buFxC_smul_int]
      congr 1
      simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]
    have hJ0ℓ : J0 ℓ = ∑ j ∈ Finset.range (egN p α s t),
        ((-1 : ℂ) ^ j) * ((HvdH.Emat s t α) ^ j).mulVec ((1 / 2 : ℂ) • Z) ℓ := by
      show (∑ j ∈ Finset.range (egN p α s t),
          ((-1 : ℂ) ^ j) • (((HvdH.Emat s t α) ^ j).mulVec ((1 / 2 : ℂ) • Z))) ℓ = _
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [hfx, hJ0ℓ]
    have hsub : (∑ j ∈ Finset.range (egN p α s t),
            ((-1 : ℂ) ^ j) * HvdH.fxC p (buIter (buWt p α s t) p α s t hs0 v0 j ℓ))
          - (∑ j ∈ Finset.range (egN p α s t),
            ((-1 : ℂ) ^ j) * ((HvdH.Emat s t α) ^ j).mulVec ((1 / 2 : ℂ) • Z) ℓ)
        = ∑ j ∈ Finset.range (egN p α s t),
            (((-1 : ℂ) ^ j) * HvdH.fxC p (buIter (buWt p α s t) p α s t hs0 v0 j ℓ)
              - ((-1 : ℂ) ^ j) * ((HvdH.Emat s t α) ^ j).mulVec ((1 / 2 : ℂ) • Z) ℓ) := by
      rw [← Finset.sum_sub_distrib]
    rw [hsub]
    calc (2 : ℝ) ^ p * ‖∑ j ∈ Finset.range (egN p α s t),
            (((-1 : ℂ) ^ j) * HvdH.fxC p (buIter (buWt p α s t) p α s t hs0 v0 j ℓ)
              - ((-1 : ℂ) ^ j) * ((HvdH.Emat s t α) ^ j).mulVec ((1 / 2 : ℂ) • Z) ℓ)‖
        ≤ (2 : ℝ) ^ p * ∑ j ∈ Finset.range (egN p α s t),
            ‖((-1 : ℂ) ^ j) * HvdH.fxC p (buIter (buWt p α s t) p α s t hs0 v0 j ℓ)
              - ((-1 : ℂ) ^ j) * ((HvdH.Emat s t α) ^ j).mulVec ((1 / 2 : ℂ) • Z) ℓ‖ := by
          gcongr
          exact norm_sum_le _ _
      _ = ∑ j ∈ Finset.range (egN p α s t), (2 : ℝ) ^ p *
            ‖((-1 : ℂ) ^ j) * HvdH.fxC p (buIter (buWt p α s t) p α s t hs0 v0 j ℓ)
              - ((-1 : ℂ) ^ j) * ((HvdH.Emat s t α) ^ j).mulVec ((1 / 2 : ℂ) • Z) ℓ‖ := by
          rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ Finset.range (egN p α s t), (19 + 18 * (egM p α : ℝ)) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          have h := (hiter j).2 ℓ
          have hmm : ((HvdH.Emat s t α) ^ j).mulVec ((1 / 2 : ℂ) • Z)
              = (1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ j).mulVec Z) := by
            rw [Matrix.mulVec_smul]
          rw [hmm]
          rw [show ((-1 : ℂ) ^ j) * HvdH.fxC p (buIter (buWt p α s t) p α s t hs0 v0 j ℓ)
                - ((-1 : ℂ) ^ j) * ((1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ j).mulVec Z)) ℓ
              = ((-1 : ℂ) ^ j) * (HvdH.fxC p (buIter (buWt p α s t) p α s t hs0 v0 j ℓ)
                - ((1 / 2 : ℂ) • (((HvdH.Emat s t α) ^ j).mulVec Z)) ℓ) by ring]
          rw [norm_mul]
          have hc : ‖((-1 : ℂ) ^ j)‖ = 1 := by rw [norm_pow]; simp
          rw [hc, one_mul]
          exact h
      _ = (egN p α s t : ℝ) * (19 + 18 * (egM p α : ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hJfinal : ∀ ℓ : Fin s, (2 : ℝ) ^ p * ‖HvdH.fxC p (J ℓ)
      - ((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z)) ℓ‖
      ≤ 1 + (egN p α s t : ℝ) * (19 + 18 * (egM p α : ℝ)) := by
    intro ℓ
    have h1 := hJsum_err ℓ
    have h2 : ‖J0 ℓ - ((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z)) ℓ‖ ≤ 1 / (2 : ℝ) ^ p := by
      have h4 : ‖(J0 - (1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z)) ℓ‖
          ≤ ‖J0 - (1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z)‖ := norm_le_pi_norm _ ℓ
      exact le_trans h4 hNeu.1
    calc (2 : ℝ) ^ p * ‖HvdH.fxC p (J ℓ)
            - ((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z)) ℓ‖
        ≤ (2 : ℝ) ^ p * (‖HvdH.fxC p (J ℓ) - J0 ℓ‖
            + ‖J0 ℓ - ((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z)) ℓ‖) := by
          gcongr
          rw [show HvdH.fxC p (J ℓ) - ((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z)) ℓ
              = (HvdH.fxC p (J ℓ) - J0 ℓ)
                + (J0 ℓ - ((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z)) ℓ) by ring]
          exact norm_add_le _ _
      _ ≤ 1 + (egN p α s t : ℝ) * (19 + 18 * (egM p α : ℝ)) := by
          have h2p : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
          have h4 : (2 : ℝ) ^ p * (1 / (2 : ℝ) ^ p) = 1 := by field_simp
          nlinarith [h1, h2, h2p, h4]
  -- ### (C)  the two conclusions, per component
  refine ⟨fun ℓ => ?_, fun ℓ => ?_⟩
  · have h := hJfinal ℓ
    have hle : 1 + (egN p α s t : ℝ) * (19 + 18 * (egM p α : ℝ))
        ≤ 1 + (egN p α s t : ℝ) * (18 * (egM p α : ℝ) + 24) := by
      have h0 : (0 : ℝ) ≤ (egN p α s t : ℝ) := Nat.cast_nonneg _
      nlinarith
    linarith [h, hle]
  · have hb1 : ‖((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z)) ℓ‖ ≤ 7 / 8 :=
      le_trans (norm_le_pi_norm _ ℓ) hJmatnorm
    have hb2 : ‖HvdH.fxC p (J ℓ) - ((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z)) ℓ‖ ≤ 1 / 8 := by
      have h2p : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
      have h5 : ‖HvdH.fxC p (J ℓ) - ((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z)) ℓ‖
          ≤ (1 + (egN p α s t : ℝ) * (19 + 18 * (egM p α : ℝ))) / (2 : ℝ) ^ p := by
        rw [le_div_iff₀ h2p]
        linarith [hJfinal ℓ]
      exact le_trans h5 hnum
    calc ‖HvdH.fxC p (J ℓ)‖
        = ‖(HvdH.fxC p (J ℓ) - ((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z)) ℓ)
            + ((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z)) ℓ‖ := by ring_nf
      _ ≤ ‖HvdH.fxC p (J ℓ) - ((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z)) ℓ‖
            + ‖((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z)) ℓ‖ := norm_add_le _ _
      _ ≤ 1 / 8 + 7 / 8 := by linarith
      _ = 1 := by norm_num

end Work.Resample
