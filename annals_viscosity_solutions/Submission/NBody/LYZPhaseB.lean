import Submission.NBody.LYZPhaseA
import Submission.NBody.LYZNoColl
import Mathlib

/-!
# Liu--Yan--Zhou's Lemma 6.1 (`unif`), second half

For an `h`-minimiser `γ` on `[0,τ]` running from `γ 0` to `x* + 2^n • a`, this module derives

* the pointwise angle bound `‖b_t - a‖_[m] ≤ θ` for all `t ≥ σ n₀` (where `b_t` is the unit
  vector in the direction of `γ t - x*`), which is what the geometric hypotheses `hncB`/`hpotB`
  need in order to be applied with `b = b_t`;
* hence the pointwise length bound `massLength m γ 0 t ≤ ‖γ t - x*‖_[m] + Ψ (‖γ t - x*‖_[m])`
  for all `t ∈ [σ n₀, τ]`.

Both are prerequisites for the dyadic induction of Liu--Yan--Zhou's Lemma `unif`.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **Liu--Yan--Zhou Lemma 6.1 (`unif`), preparation.**  From the output of `exists_lyz_phaseA`
we obtain, in addition, the *pointwise* angle bound (in the weak form `‖b_t - a‖_[m] ≤ θ`, which is
what the cone hypotheses `hncB`/`hpotB` require) and the pointwise length bound
`massLength m γ 0 t ≤ ‖γ t - x*‖_[m] + Ψ (‖γ t - x*‖_[m])` for all `t ∈ [σ n₀, τ]`. -/
theorem exists_lyz_phaseB_aux {m : Fin N → ℝ} {h : ℝ} (hh : 0 < h) (hm : ∀ i, 0 < m i)
    {xstar a : EN E N} {A B M θ : ℝ}
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hM0 : 0 ≤ M) (ha : ‖a‖_[m] = 1)
    {Ψ Ψb : ℝ → ℝ} (hΨnn : ∀ T, 0 ≤ T → 0 ≤ Ψ T)
    (hΨbnn : ∀ t, 0 ≤ Ψb t) (hrel : ∀ t, 0 < t → Real.sqrt (Ψ t / t) ≤ Ψb t)
    (hslow : ∀ s t, 0 < s → s ≤ t → t ≤ 2 * s → Ψb t ≤ 2 * Ψb s)
    (hsumm : Summable fun k : ℕ => Real.sqrt (Ψ ((2:ℝ) ^ k) / (2:ℝ) ^ k))
    (htail : ∀ i : ℕ, lyzTail Ψ i ≤ Ψb ((2:ℝ) ^ i))
    {n₀ n : ℕ} (hn : n₀ ≤ n) {τ : ℝ} {γ : ℝ → EN E N}
    (hτ : 0 < τ) (hac : AbsolutelyContinuousOnInterval γ 0 τ)
    (hfin : actionOn m h γ 0 τ < ⊤) (hmin : IsHMinimizer m h γ 0 τ)
    (hγτ : γ τ = xstar + (2:ℝ) ^ n • a)
    (h0lt : ‖γ 0 - xstar‖_[m] < (2:ℝ) ^ n₀)
    (hΦ : actionPot m h (γ 0) xstar < ⊤)
    (hAφ : (Real.sqrt (2 * h))⁻¹ * (actionPot m h (γ 0) xstar).toReal ≤ A)
    (hΨhalf : ∀ i, n₀ ≤ i → i < n → Ψ ((2:ℝ) ^ (i + 1)) ≤ (2:ℝ) ^ (i + 1) / 2)
    (hx0 : ∀ i, n₀ ≤ i → i < n → ‖γ 0 - xstar‖_[m] ≤ Ψ ((2:ℝ) ^ (i + 1)))
    (hpotB : ∀ b : EN E N, ‖b‖_[m] = 1 → ‖b - a‖_[m] ≤ θ → ∀ T : ℝ, 0 ≤ T →
        ∫ t in (0:ℝ)..T, U m (xstar + t • b) ≤ (2 * h) * B * Real.log (2 * T + 2 * M + 1))
    (hncB : ∀ b : EN E N, ‖b‖_[m] = 1 → ‖b - a‖_[m] ≤ θ → ∀ t : ℝ, 0 ≤ t →
        WithoutCollisions (xstar + t • b))
    (hΨlyz : ∀ T : ℝ, Ψ T = lyzPsi A B M T)
    (hθ : 50 * lyzTail Ψ (n₀ + 1) ≤ θ) :
    ∃ σ τhat : ℕ → ℝ,
      σ n = τ ∧
      (∀ i, n₀ ≤ i → i ≤ n → σ i ∈ Set.Icc 0 τ ∧ ‖γ (σ i) - xstar‖_[m] = (2:ℝ) ^ i ∧
        (∀ t ∈ Set.Icc (σ i) τ, (2:ℝ) ^ i ≤ ‖γ t - xstar‖_[m])) ∧
      (∀ i, n₀ ≤ i → i < n → σ i ≤ σ (i + 1)) ∧
      (∀ i, n₀ ≤ i → i < n → τhat i ∈ Set.Icc (σ i) (σ (i + 1)) ∧
        ‖γ (τhat i) - xstar‖_[m] = ‖γ (τhat i) - γ (σ (i + 1))‖_[m] ∧
        (2:ℝ) ^ i ≤ ‖γ (τhat i) - xstar‖_[m]) ∧
      (∀ i, n₀ ≤ i → i < n →
        ‖massScale m (γ (σ i)) - (massScale m xstar +
            ((1:ℝ) / 2) • (massScale m (γ (σ (i + 1))) - massScale m xstar))‖
          ≤ 4 * Real.sqrt ((2:ℝ) ^ (i + 1) * Ψ ((2:ℝ) ^ (i + 1)))) ∧
      (∀ i, n₀ ≤ i → i < n → ∀ t ∈ Set.Icc (σ i) (σ (i + 1)), ∃ c : ℝ, 0 ≤ c ∧
        ‖massScale m (γ t) - (massScale m xstar +
            c • (massScale m (γ (σ (i + 1))) - massScale m xstar))‖
          ≤ 6 * Real.sqrt ((2:ℝ) ^ (i + 1) * Ψ ((2:ℝ) ^ (i + 1)))) ∧
      (∀ i, n₀ ≤ i → i ≤ n →
        ‖((2:ℝ) ^ i)⁻¹ • (γ (σ i) - xstar) - a‖_[m] ≤ 24 * lyzTail Ψ (i + 1)) ∧
      (∀ t ∈ Set.Icc (σ n₀) τ,
        ‖(‖γ t - xstar‖_[m])⁻¹ • (γ t - xstar) - a‖_[m] ≤ θ) ∧
      (∀ t ∈ Set.Icc (σ n₀) τ,
        massLength m γ 0 t ≤ ‖γ t - xstar‖_[m] + Ψ (‖γ t - xstar‖_[m])) := by
  classical
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have htail0 : 0 ≤ lyzTail Ψ (n₀ + 1) := lyzTail_nonneg (Ψ := Ψ) hΨnn _
  have hθ0 : 0 ≤ θ := le_trans (mul_nonneg (by norm_num) htail0) hθ
  have hθA : 24 * lyzTail Ψ (n₀ + 1) ≤ θ :=
    le_trans (mul_le_mul_of_nonneg_right (by norm_num : (24:ℝ) ≤ 50) htail0) hθ
  obtain ⟨σ, τhat, hσn, hσv, hσmono, hτv, hmid, hray, hlenP, hdirP⟩ :=
    exists_lyz_phaseA hh hm hA0 hB0 hM0 ha hΨnn hΨbnn hrel hslow hsumm htail hn hτ hac hfin
      hmin hγτ h0lt hΦ hAφ hΨhalf hx0 hpotB hncB hΨlyz hθA
  have hσn₀mem : σ n₀ ∈ Set.Icc 0 τ := (hσv n₀ le_rfl hn).1
  have hσn₀le := (hσv n₀ le_rfl hn).2.2
  -- the pointwise angle bound
  have hconeAll : ∀ t ∈ Set.Icc (σ n₀) τ,
      ‖(‖γ t - xstar‖_[m])⁻¹ • (γ t - xstar) - a‖_[m] ≤ θ := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with hτ' | hτ'
    · have ht_eq : t = σ n := by rw [hσn]; exact hτ'
      have hDt : ‖γ t - xstar‖_[m] = (2:ℝ) ^ n := by
        rw [ht_eq]; exact (hσv n hn le_rfl).2.1
      have hγt : γ t = xstar + (2:ℝ) ^ n • a := by rw [ht_eq, hσn]; exact hγτ
      have h2n : ((2:ℝ) ^ n) ≠ 0 := by positivity
      rw [hDt, hγt, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ h2n, one_smul, sub_self]
      rw [weightedNorm_zero]
      exact hθ0
    · let S : Finset ℕ := (Finset.Icc n₀ n).filter (fun k => σ k ≤ t)
      have hSnn : S.Nonempty := by
        refine ⟨n₀, ?_⟩
        simp only [S, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨le_rfl, hn⟩, ht.1⟩
      set i : ℕ := S.max' hSnn with hi_def
      have hiS : i ∈ S := by rw [hi_def]; exact Finset.max'_mem S hSnn
      have hi_mem := Finset.mem_filter.mp hiS
      have hiIcc := Finset.mem_Icc.mp hi_mem.1
      have hi0 : n₀ ≤ i := hiIcc.1
      have hin : i ≤ n := hiIcc.2
      have hσi : σ i ≤ t := hi_mem.2
      have hin_lt : i < n := by
        rcases lt_or_eq_of_le hin with h | h
        · exact h
        · exfalso
          have hle : σ n ≤ t := by rw [← h]; exact hσi
          rw [hσn] at hle
          exact absurd hle (not_le.mpr hτ')
      have hti1 : t ≤ σ (i + 1) := by
        by_contra hcon
        rw [not_le] at hcon
        have hmem : i + 1 ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, le_of_lt hcon⟩
        have hmax := Finset.le_max' S (i + 1) hmem
        rw [← hi_def] at hmax
        omega
      have hSpos : n₀ ≤ i + 1 := by omega
      have hSle : i + 1 ≤ n := by omega
      have hSval : ‖γ (σ (i + 1)) - xstar‖_[m] = (2:ℝ) ^ (i + 1) := (hσv (i + 1) hSpos hSle).2.1
      have hdirP1 : ‖((2:ℝ) ^ (i + 1))⁻¹ • (γ (σ (i + 1)) - xstar) - a‖_[m]
          ≤ 24 * lyzTail Ψ ((i + 1) + 1) := hdirP (i + 1) hSpos hSle
      obtain ⟨c, hc, hcc⟩ := hray i hi0 hin_lt t ⟨hσi, hti1⟩
      have hDge : (2:ℝ) ^ i ≤ ‖γ t - xstar‖_[m] := (hσv i hi0 hin).2.2 t ⟨hσi, ht.2⟩
      have hDpos : 0 < ‖γ t - xstar‖_[m] := lt_of_lt_of_le (by positivity) hDge
      have hSpos' : (0:ℝ) < (2:ℝ) ^ (i + 1) := by positivity
      have huw : ‖(massScale m (γ t) - massScale m xstar)
            - c • (massScale m (γ (σ (i + 1))) - massScale m xstar)‖
          ≤ 6 * Real.sqrt ((2:ℝ) ^ (i + 1) * Ψ ((2:ℝ) ^ (i + 1))) := by
        have h := hcc
        rw [sub_add_eq_sub_sub] at h
        exact h
      have hkey := norm_inv_smul_sub_inv_smul_le_ray (F := EN E N)
        (u := massScale m (γ t) - massScale m xstar)
        (w := massScale m (γ (σ (i + 1))) - massScale m xstar)
        (r := ‖γ t - xstar‖_[m]) (s := (2:ℝ) ^ (i + 1))
        (δ := 6 * Real.sqrt ((2:ℝ) ^ (i + 1) * Ψ ((2:ℝ) ^ (i + 1)))) (c := c)
        hDpos hSpos'
        (by rw [← massScale_sub m (γ t) xstar, weightedNorm_eq_norm_massScale hm0])
        (by rw [← massScale_sub m (γ (σ (i + 1))) xstar,
              ← weightedNorm_eq_norm_massScale hm0, hSval])
        hc huw
      -- algebraic rewriting of the denominator
      have hXY : (2:ℝ) ^ (i + 1) * Ψ ((2:ℝ) ^ (i + 1))
          = ((2:ℝ) ^ (i + 1)) ^ 2 * (Ψ ((2:ℝ) ^ (i + 1)) / (2:ℝ) ^ (i + 1)) := by
        field_simp
      have hsimp : Real.sqrt ((2:ℝ) ^ (i + 1) * Ψ ((2:ℝ) ^ (i + 1)))
          = (2:ℝ) ^ (i + 1) * Real.sqrt (Ψ ((2:ℝ) ^ (i + 1)) / (2:ℝ) ^ (i + 1)) := by
        rw [hXY, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      have h2i : (2:ℝ) ^ (i + 1) = 2 * (2:ℝ) ^ i := by rw [pow_succ]; ring
      have h2ipos : ((2:ℝ) ^ i) ≠ 0 := by positivity
      have halg : 2 * (6 * Real.sqrt ((2:ℝ) ^ (i + 1) * Ψ ((2:ℝ) ^ (i + 1)))) / (2:ℝ) ^ i
          = 24 * Real.sqrt (Ψ ((2:ℝ) ^ (i + 1)) / (2:ℝ) ^ (i + 1)) := by
        rw [hsimp, h2i]
        field_simp
        ring
      have hstep1 : ‖(‖γ t - xstar‖_[m])⁻¹ • (γ t - xstar)
            - ((2:ℝ) ^ (i + 1))⁻¹ • (γ (σ (i + 1)) - xstar)‖_[m]
          ≤ 24 * Real.sqrt (Ψ ((2:ℝ) ^ (i + 1)) / (2:ℝ) ^ (i + 1)) := by
        have hconv : ‖(‖γ t - xstar‖_[m])⁻¹ • (γ t - xstar)
              - ((2:ℝ) ^ (i + 1))⁻¹ • (γ (σ (i + 1)) - xstar)‖_[m]
            ≤ 2 * (6 * Real.sqrt ((2:ℝ) ^ (i + 1) * Ψ ((2:ℝ) ^ (i + 1)))) / ‖γ t - xstar‖_[m] := by
          rw [weightedNorm_eq_norm_massScale hm0, massScale_sub, massScale_smul, massScale_smul,
            massScale_sub m (γ t) xstar, massScale_sub m (γ (σ (i + 1))) xstar]
          exact hkey
        refine hconv.trans ?_
        rw [← halg]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity : (0:ℝ) < (2:ℝ) ^ i) hDge
      have hlt : Real.sqrt (Ψ ((2:ℝ) ^ (i + 1)) / (2:ℝ) ^ (i + 1)) ≤ lyzTail Ψ (i + 1) := by
        rw [lyzTail_succ hsumm (i + 1)]
        exact le_add_of_nonneg_right (lyzTail_nonneg (Ψ := Ψ) hΨnn _)
      have hdir_t : ‖(‖γ t - xstar‖_[m])⁻¹ • (γ t - xstar)
            - ((2:ℝ) ^ (i + 1))⁻¹ • (γ (σ (i + 1)) - xstar)‖_[m] ≤ 24 * lyzTail Ψ (i + 1) :=
        hstep1.trans (mul_le_mul_of_nonneg_left hlt (by norm_num))
      have htri : ‖(‖γ t - xstar‖_[m])⁻¹ • (γ t - xstar) - a‖_[m]
          ≤ 24 * lyzTail Ψ (i + 1) + 24 * lyzTail Ψ ((i + 1) + 1) :=
        (weightedNorm_sub_le hm0 _ _ _).trans (add_le_add hdir_t hdirP1)
      have hmono1 : lyzTail Ψ ((i + 1) + 1) ≤ lyzTail Ψ (i + 1) :=
        lyzTail_mono hΨnn hsumm (Nat.le_succ (i + 1))
      have hmono2 : lyzTail Ψ (i + 1) ≤ lyzTail Ψ (n₀ + 1) :=
        lyzTail_mono hΨnn hsumm (Nat.succ_le_succ hi0)
      refine htri.trans ?_
      have := mul_le_mul_of_nonneg_left hmono2 (by norm_num : (0:ℝ) ≤ 48)
      linarith [hmono1, this, hθ]
  refine ⟨σ, τhat, hσn, hσv, hσmono, hτv, hmid, hray, hdirP, hconeAll, ?_⟩
  · intro t ht
    have ht0 : 0 ≤ t := le_trans hσn₀mem.1 ht.1
    have hDge : (2:ℝ) ^ n₀ ≤ ‖γ t - xstar‖_[m] := hσn₀le t ht
    have hDpos : 0 < ‖γ t - xstar‖_[m] := lt_of_lt_of_le (by positivity) hDge
    have hcone_t := hconeAll t ht
    have hb : ‖(‖γ t - xstar‖_[m])⁻¹ • (γ t - xstar)‖_[m] = 1 := by
      rw [weightedNorm_smul hm0, abs_of_nonneg (inv_nonneg.mpr hDpos.le),
        inv_mul_cancel₀ hDpos.ne']
    have hγσ : γ t = xstar + ‖γ t - xstar‖_[m] • ((‖γ t - xstar‖_[m])⁻¹ • (γ t - xstar)) := by
      rw [smul_smul, mul_inv_cancel₀ hDpos.ne', one_smul]
      abel
    have hncseg : ∀ s ∈ Set.Icc (0:ℝ) (‖γ t - xstar‖_[m]),
        WithoutCollisions (xstar + s • ((‖γ t - xstar‖_[m])⁻¹ • (γ t - xstar))) :=
      fun s hs => hncB _ hb hcone_t s hs.1
    have hpot := hpotB _ hb hcone_t _ (le_of_lt hDpos)
    have hlog : 0 ≤ Real.log (2 * ‖γ t - xstar‖_[m] + 2 * M + 1) := by
      apply Real.log_nonneg
      have : (1:ℝ) ≤ (2:ℝ) ^ n₀ := one_le_pow₀ (by norm_num)
      nlinarith
    have hres := massLength_le_psi_sub' hh hm0 ht0 ht.2 hDpos hac hfin hmin hγσ hb hncseg
      hΦ hAφ hA0 hB0 hM0 hpot hlog
    rw [← hΨlyz] at hres
    exact hres

end Submission.NBody
