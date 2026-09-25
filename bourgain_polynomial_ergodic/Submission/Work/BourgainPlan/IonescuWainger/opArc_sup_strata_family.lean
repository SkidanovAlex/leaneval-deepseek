import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.StrataCompDefs
import Submission.Work.BourgainPlan.IonescuWainger.opArc_strata_incl_excl
import Submission.Work.BourgainPlan.opArc_sup_torsion_family_of_bump

namespace Work.BourgainPlan.IonescuWainger

/-- The `p = ∞` endpoint of Tao's `ortho-apply`(ii) in the strata convention, for one fixed `A₀ ⊆ S` with `A₀.card ≤ k`: for a bump `φ` whose coefficient sequence `K m = ∫ ξ, φ ξ · star (fourier m ξ)` decays like `C ε (1+(εm)²)^{-3/2}`, with `2ε < 1/qmax^{2k}`, and for data `f` bounded by `C'`, the `ℓ²`-norm over the family `(Op_{φ;α+Σ_{A₀}}f(n))_{α ∈ Σ_{(A₀)}}` is at most `2 ^ k · 8 C C'` at every `n`, where `Σ_{A₀} = sigmaStrataFinset A₀` (Tao's stratum) and `Σ_{(A₀)} = strataCompFinset S k A₀ = ⋃_{B ⊆ S∖A₀, |B| ≤ k−|A₀|} Σ_B`.  Route: the strata inclusion-exclusion `opArc_strata_incl_excl` expands the strata multiplier as the alternating sum over `B ⊆ A₀` of the torsion multipliers `Op_{φ;α+Σ_{⊆B}}` (`Σ_{⊆B} = sigmaSubAFinset B`); Minkowski's inequality in `ℓ²` bounds the family `ℓ²`-norm by `2^{A₀.card} ≤ 2^k` times the maximum over `B ⊆ A₀` of the corresponding torsion family norm; each of those is `≤ 8 C C'` by the proved `opArc_sup_torsion_family_of_bump` (in `Submission/Work/BourgainPlan/opArc_sup_torsion_family_of_bump.lean`), applied with an index family enumerating `Σ_{(A₀)}` (each `α ∈ Σ_{(A₀)}` lies in a unique stratum `Σ_B` with `B ⊆ S∖A₀`, `B.card ≤ k − A₀.card`, and has a unique representation `α = arcPt (QA B) a`, `0 ≤ a < QA B`; the smallness hypothesis `ε · Q_B ≤ 1/2` there follows from `2ε < 1/qmax^{2k}` and `Q_B ≤ qmax^k`). -/
theorem opArc_sup_strata_family {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) {A₀ : Finset ℕ} (hA₀ : A₀ ⊆ S)
    {k : ℕ} (hk₀ : A₀.card ≤ k) {qmax : ℕ} (hmax : ∀ q ∈ S, q ≤ qmax) (hqmax : 1 ≤ qmax)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {K : ℤ → ℂ} {C : ℝ}
    (hC0 : 0 ≤ C)
    (hφsupp : ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle, ε < ‖ξ‖ → φ ξ = 0)
    (hK : ∀ m : ℤ, ∫ ξ, φ ξ * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1)) = K m)
    (hdecay : ∀ m : ℤ, ‖K m‖ ≤ C * ε / (1 + (ε * (m : ℝ)) ^ 2) ^ ((3 : ℝ) / 2))
    (hsmall : 2 * ε < 1 / (qmax : ℝ) ^ (2 * k))
    (f : ℤ → ℂ) (hf : Memℓp f 2) {C' : ℝ} (hC' : ∀ m : ℤ, ‖f m‖ ≤ C') (n : ℤ) :
    (∑ α ∈ Work.BourgainPlan.IonescuWainger.strataCompFinset S k A₀,
        ‖Work.BourgainPlan.IonescuWainger.opArc φ hφ
          (Work.BourgainPlan.IonescuWainger.arcShift
            (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀) α) f hf n‖ ^ 2)
        ^ ((1 : ℝ) / 2) ≤ 2 ^ k * (8 * C * C') := by
  classical
  have h2A₀ : ∀ q ∈ A₀, 2 ≤ q := fun q hq => h2 q (hA₀ hq)
  have hcopA₀ : ∀ p ∈ A₀, ∀ q ∈ A₀, p ≠ q → Nat.Coprime p q :=
    fun p hp q hq hpq => hS p (hA₀ hp) q (hA₀ hq) hpq
  have hC'0 : 0 ≤ C' := le_trans (norm_nonneg (f 0)) (hC' 0)
  set T : Finset Circle := strataCompFinset S k A₀ with hTdef
  let w : Finset ℕ → Circle → ℂ :=
    fun B α => opArc φ hφ (arcShift (sigmaSubAFinset B) α) f hf n
  let Fv : Circle → ℂ := fun α => opArc φ hφ (arcShift (sigmaStrataFinset A₀) α) f hf n
  have hFeq : ∀ α : Circle, Fv α
      = ∑ B ∈ A₀.powerset, ((-1 : ℂ) ^ (A₀.card - B.card)) * w B α := by
    intro α
    have h := congrFun (opArc_strata_incl_excl A₀ h2A₀ hcopA₀ α φ hφ f hf) n
    simpa only [Fv, w, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
  have hnorm_c : ∀ B : Finset ℕ, ‖((-1 : ℂ) ^ (A₀.card - B.card))‖ = 1 := by
    intro B
    rw [norm_pow]
    simp
  have hpt : ∀ α : Circle, ‖Fv α‖ ^ 2
      ≤ (A₀.powerset.card : ℝ) * ∑ B ∈ A₀.powerset, ‖w B α‖ ^ 2 := by
    intro α
    have h1 : ‖Fv α‖ ≤ ∑ B ∈ A₀.powerset, ‖w B α‖ := by
      rw [hFeq α]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun B _ => ?_))
      rw [norm_mul, hnorm_c B, one_mul]
    calc ‖Fv α‖ ^ 2 ≤ (∑ B ∈ A₀.powerset, ‖w B α‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (A₀.powerset.card : ℝ) * ∑ B ∈ A₀.powerset, ‖w B α‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
  have hbound : ∀ B ∈ A₀.powerset, (∑ α ∈ T, ‖w B α‖ ^ 2) ≤ (8 * C * C') ^ 2 := by
    intro B hB
    have hBA₀ : B ⊆ A₀ := Finset.mem_powerset.mp hB
    have hBS : B ⊆ S := hBA₀.trans hA₀
    have hBk : B.card ≤ k := le_trans (Finset.card_le_card hBA₀) hk₀
    have hwit : ∀ i : ↥T, ∃ p : Finset ℕ × ℤ,
        p.1 ∈ (S \ A₀).powerset.filter (fun C => C.card ≤ k - A₀.card) ∧
        arcPt (QA p.1) p.2 = (i : Circle) := by
      intro i
      have hi : (i : Circle) ∈ strataCompFinset S k A₀ := i.2
      rw [mem_strataCompFinset] at hi
      obtain ⟨C, hC, hiC⟩ := hi
      have hsub : (i : Circle) ∈ (Finset.range (QA C)).image
          (fun a : ℕ => arcPt (QA C) (a : ℤ)) :=
        sigmaStrataFinset_subset_sigmaSubAFinset C hiC
      obtain ⟨a, -, haeq⟩ := Finset.mem_image.mp hsub
      exact ⟨(C, (a : ℤ)), hC, haeq⟩
    let D : ↥T → Finset ℕ := fun i => (Classical.choose (hwit i)).1
    let a : ↥T → ℤ := fun i => (Classical.choose (hwit i)).2
    have hDmem : ∀ i, D i ∈ (S \ A₀).powerset.filter (fun C => C.card ≤ k - A₀.card) :=
      fun i => (Classical.choose_spec (hwit i)).1
    have haeq : ∀ i, arcPt (QA (D i)) (a i) = (i : Circle) :=
      fun i => (Classical.choose_spec (hwit i)).2
    have hDsub : ∀ i, D i ⊆ S \ B := by
      intro i q hq
      have h1 : D i ⊆ S \ A₀ := Finset.mem_powerset.mp (Finset.mem_filter.mp (hDmem i)).1
      have h1' : q ∈ S ∧ q ∉ A₀ := Finset.mem_sdiff.mp (h1 hq)
      exact Finset.mem_sdiff.mpr ⟨h1'.1, fun hqA₀ => h1'.2 (hBA₀ hqA₀)⟩
    have hDk : ∀ i, (D i).card ≤ k - B.card := by
      intro i
      have h1 : (D i).card ≤ k - A₀.card := (Finset.mem_filter.mp (hDmem i)).2
      exact h1.trans (Nat.sub_le_sub_left (Finset.card_le_card hBA₀) k)
    have hinj : ∀ i j : ↥T, i ≠ j →
        arcPt (QA (D i)) (a i) ≠ arcPt (QA (D j)) (a j) := by
      intro i j hij h
      exact hij (Subtype.ext (by rw [← haeq i, ← haeq j]; exact h))
    have hεQ : ε * (QA B : ℝ) ≤ 1 / 2 := by
      have hQle_nat : QA B ≤ qmax ^ k := by
        calc QA B = ∏ q ∈ B, q := rfl
          _ ≤ ∏ _q ∈ B, qmax :=
              Finset.prod_le_prod₀ (fun q _ => Nat.zero_le q) (fun q hq => hmax q (hBS hq))
          _ = qmax ^ B.card := Finset.prod_const qmax
          _ ≤ qmax ^ k := Nat.pow_le_pow_right (by omega) hBk
      have hQle : (QA B : ℝ) ≤ (qmax : ℝ) ^ k := by
        have h1 : (QA B : ℝ) ≤ ((qmax ^ k : ℕ) : ℝ) := by exact_mod_cast hQle_nat
        rwa [Nat.cast_pow] at h1
      have hq1 : (1 : ℝ) ≤ (qmax : ℝ) := by exact_mod_cast hqmax
      have hεlt : ε < 1 / (2 * (qmax : ℝ) ^ (2 * k)) := by
        have hpos : (0 : ℝ) < 2 * (qmax : ℝ) ^ (2 * k) := by positivity
        rw [lt_div_iff₀ hpos]
        have h := hsmall
        rw [lt_div_iff₀ (show (0 : ℝ) < (qmax : ℝ) ^ (2 * k) by positivity)] at h
        linarith [h]
      calc ε * (QA B : ℝ)
          ≤ (1 / (2 * (qmax : ℝ) ^ (2 * k))) * (qmax : ℝ) ^ k :=
            mul_le_mul hεlt.le hQle (by positivity) (by positivity)
        _ ≤ 1 / 2 := by
            rw [show (2 : ℕ) * k = k * 2 from by ring, pow_mul]
            rw [div_mul_eq_mul_div, one_mul,
              div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((qmax : ℝ) ^ k) ^ 2)]
            have hy1 : (1 : ℝ) ≤ (qmax : ℝ) ^ k := one_le_pow₀ hq1
            nlinarith [hy1, sq_nonneg ((qmax : ℝ) ^ k)]
    have hmain := Work.BourgainPlan.opArc_sup_torsion_family_of_bump
      (S := S) h2 hS (A₀ := B) hBS hBk D a hDsub hDk hinj (qmax := qmax) hmax
      φ hφ hC0 hε hε1 hφsupp hK hdecay hsmall hεQ f hf hC' n
    have hstep : (∑ α ∈ T, ‖w B α‖ ^ 2)
        = ∑ i : ↥T,
            ‖opArc φ hφ (arcShift (sigmaSubAFinset B) (arcPt (QA (D i)) (a i))) f hf n‖ ^ 2 := by
      rw [← Finset.sum_attach T (fun α => ‖w B α‖ ^ 2)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      show ‖w B (↑i)‖ ^ 2
        = ‖opArc φ hφ (arcShift (sigmaSubAFinset B) (arcPt (QA (D i)) (a i))) f hf n‖ ^ 2
      rw [haeq i]
    rw [← hstep] at hmain
    rw [← Real.sqrt_eq_rpow] at hmain
    have hSnn : 0 ≤ ∑ α ∈ T, ‖w B α‖ ^ 2 := Finset.sum_nonneg (fun α _ => sq_nonneg _)
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hmain 2
    rwa [Real.sq_sqrt hSnn] at h
  have hsum1 : (∑ α ∈ T, ‖Fv α‖ ^ 2)
      ≤ (A₀.powerset.card : ℝ) * ∑ B ∈ A₀.powerset, ∑ α ∈ T, ‖w B α‖ ^ 2 := by
    calc ∑ α ∈ T, ‖Fv α‖ ^ 2
        ≤ ∑ α ∈ T, (A₀.powerset.card : ℝ) * ∑ B ∈ A₀.powerset, ‖w B α‖ ^ 2 :=
          Finset.sum_le_sum (fun α _ => hpt α)
      _ = (A₀.powerset.card : ℝ) * ∑ α ∈ T, ∑ B ∈ A₀.powerset, ‖w B α‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ = (A₀.powerset.card : ℝ) * ∑ B ∈ A₀.powerset, ∑ α ∈ T, ‖w B α‖ ^ 2 := by
          rw [Finset.sum_comm]
  have hsum2 : ∑ B ∈ A₀.powerset, ∑ α ∈ T, ‖w B α‖ ^ 2
      ≤ (A₀.powerset.card : ℝ) * (8 * C * C') ^ 2 := by
    calc ∑ B ∈ A₀.powerset, ∑ α ∈ T, ‖w B α‖ ^ 2
        ≤ ∑ B ∈ A₀.powerset, (8 * C * C') ^ 2 := Finset.sum_le_sum hbound
      _ = (A₀.powerset.card : ℝ) * (8 * C * C') ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have key : ∑ α ∈ T, ‖Fv α‖ ^ 2 ≤ ((A₀.powerset.card : ℝ) * (8 * C * C')) ^ 2 := by
    calc ∑ α ∈ T, ‖Fv α‖ ^ 2
        ≤ (A₀.powerset.card : ℝ) * ((A₀.powerset.card : ℝ) * (8 * C * C') ^ 2) :=
          hsum1.trans (mul_le_mul_of_nonneg_left hsum2 (by positivity))
      _ = ((A₀.powerset.card : ℝ) * (8 * C * C')) ^ 2 := by ring
  rw [← Real.sqrt_eq_rpow]
  have hR : 0 ≤ 8 * C * C' := mul_nonneg (mul_nonneg (by norm_num) hC0) hC'0
  have hcardR : 0 ≤ (A₀.powerset.card : ℝ) * (8 * C * C') :=
    mul_nonneg (Nat.cast_nonneg _) hR
  calc Real.sqrt (∑ α ∈ T, ‖Fv α‖ ^ 2)
      ≤ Real.sqrt (((A₀.powerset.card : ℝ) * (8 * C * C')) ^ 2) := Real.sqrt_le_sqrt key
    _ = (A₀.powerset.card : ℝ) * (8 * C * C') := Real.sqrt_sq hcardR
    _ ≤ (2 : ℝ) ^ k * (8 * C * C') := by
        rw [show (A₀.powerset.card : ℝ) = (2 : ℝ) ^ A₀.card by
          rw [Finset.card_powerset, Nat.cast_pow]; norm_num]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk₀) hR


end Work.BourgainPlan.IonescuWainger
