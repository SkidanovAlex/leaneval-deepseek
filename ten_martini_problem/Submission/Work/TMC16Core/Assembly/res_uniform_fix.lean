import Mathlib
import Submission.Work.TMC16Core.Assembly.uni_res_theta2
import Submission.Work.TMC16Core.Assembly.Branch

/-!
# The resonant uniformity with the explicit rate `9 L / 64 + b₀ / 4`

`Assembly.uni_res_theta2` (AJ Lemma 9.13, enlarged `ℓ`-range) proves

`∃ ε > 0, ∃ N, ∀ n ≥ N, ... Uniform (9 L / 32 - ε) (θ + (j + q_n - 1) α)`.

Its proof in fact produces the *explicit* value `ε = (9 L / 32 - b₀ / 2) / 2`, for which
`9 L / 32 - ε = 9 L / 64 + b₀ / 4`.  The present theorem performs that substitution at the
top level, exposing the concrete rate.  It is proved exactly as `uni_res_theta2` with the
rate comparison `hrate` stated against the substituted value (the two are equal by `ring`).
-/

namespace Work.TMC16Core.Assembly

open Work.TMC16Core
open Work.TMC16Core.Core

noncomputable section

theorem res_uniform_fix {α b₀ lam L : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {θ : ℝ}
    (hα : Irrational α) (hb₀ : 0 < b₀) (hDioph : Work.TMC16Core.DiophBelow α b₀)
    (hL : L = Real.log lam) (hlam : 1 < lam) (hLb : 16 * b₀ / 9 < L)
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i) (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) →
      Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    (hθ : θ ∉ Work.TMC16Core.Theta α) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ ℓ : ℕ, 1 ≤ ℓ →
      (ℓ : ℝ) ≤ 2 * Real.rpow (q (n + 1) : ℝ) (8 / 9) / (q n : ℝ) →
      Work.TMC16Core.Uniform (9 * L / 64 + b₀ / 4)
        (fun j : {j : ℤ // j ∈ Work.TMC16Core.Assembly.I1r (q n)
            ∪ Work.TMC16Core.Assembly.I2r (q n) ℓ} =>
          θ + (((j : ℤ) : ℝ) + ((q n : ℝ) - 1)) * α) := by
  obtain ⟨K₀, hK₀1, csm, hcsm, hcsm1, h1θ, h2θ⟩ := Core.theta_setup hθ
  obtain ⟨Qr, hQrpos, hQrb⟩ := uni_res_theta_rate (b₀ := b₀) (L := L)
    (Kc := Real.log (1 / csm) + 60) hb₀ hLb
  obtain ⟨Kd, hKd⟩ : ∃ K : ℕ, ∀ k ≥ K,
      Real.exp (-(b₀ * (k : ℝ))) ≤ Work.TMC16Core.fracDist ((k : ℝ) * α) := by
    have h := hDioph
    rw [Work.TMC16Core.DiophBelow, Filter.eventually_atTop] at h
    exact h
  -- `q m ≥ m + 1`
  have hqge : ∀ m : ℕ, m + 1 ≤ q m := by
    intro m
    induction m with
    | zero => have := hqpos 0; omega
    | succ k ih =>
      have h1 : q k + 1 ≤ q (k + 1) := by
        show q k + 1 ≤ q k.succ
        have := hmono (Nat.lt_succ_self k)
        omega
      omega
  -- threshold for `csm * (q n)² ≥ 10⁶`
  have hbig_all : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 10 ^ 6 ≤ csm * (q n : ℝ) ^ 2 := by
    obtain ⟨Nb, hNb⟩ : ∃ Nb : ℕ, 10 ^ 3 / Real.sqrt csm ≤ (Nb : ℝ) := exists_nat_ge _
    refine ⟨Nb + 1, fun n hn => ?_⟩
    have hqn : 10 ^ 3 / Real.sqrt csm ≤ (q n : ℝ) := by
      have h1 : (Nb : ℝ) + 1 ≤ (q n : ℝ) := by
        have h2 : Nb + 1 ≤ q n := by have := hqge n; omega
        exact_mod_cast h2
      linarith [hNb]
    have hsq : (10 ^ 3 / Real.sqrt csm) ^ 2 ≤ (q n : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hqn 2
    have hval : (10 ^ 3 / Real.sqrt csm) ^ 2 = 10 ^ 6 / csm := by
      rw [div_pow, Real.sq_sqrt (le_of_lt hcsm)]
      norm_num
    have hgoal : 10 ^ 6 / csm ≤ (q n : ℝ) ^ 2 := by rw [← hval]; exact hsq
    have hfin : 10 ^ 6 ≤ (q n : ℝ) ^ 2 * csm := (div_le_iff₀ hcsm).mp hgoal
    linarith
  -- threshold for `Qr ≤ q n`
  have hQr_all : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Qr ≤ (q n : ℝ) := by
    obtain ⟨Nr, hNr⟩ : ∃ Nr : ℕ, Qr ≤ (Nr : ℝ) := exists_nat_ge _
    refine ⟨Nr + 1, fun n hn => ?_⟩
    have h1 : (Nr : ℝ) + 1 ≤ (q n : ℝ) := by
      have h2 : Nr + 1 ≤ q n := by have := hqge n; omega
      exact_mod_cast h2
    linarith [hNr]
  -- threshold for `Kd ≤ q n`
  have hKd_all : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Kd ≤ q n :=
    ⟨Kd + 1, fun n hn => by have := hqge n; omega⟩
  -- positivity of `q (n+1)` and the Diophantine growth bound
  have hβall : ∀ n : ℕ, Kd ≤ q n → (q (n + 1) : ℝ) ≤ Real.exp (b₀ * (q n : ℝ)) := by
    intro n hn
    have h1 : Real.exp (-(b₀ * (q n : ℝ))) ≤ Work.TMC16Core.fracDist ((q n : ℝ) * α) :=
      hKd (q n) hn
    rw [← hΔeq n] at h1
    have h2 : Δ n < 1 / (q (n + 1) : ℝ) := hΔup n
    have hPpos : (0 : ℝ) < (q (n + 1) : ℝ) := by
      have := hqpos (n + 1); exact_mod_cast this
    have h3 : Real.exp (-(b₀ * (q n : ℝ))) < 1 / (q (n + 1) : ℝ) := lt_of_le_of_lt h1 h2
    have h4 : Real.exp (-(b₀ * (q n : ℝ))) * (q (n + 1) : ℝ) < 1 :=
      (lt_div_iff₀ hPpos).mp h3
    have hepos : 0 < Real.exp (-(b₀ * (q n : ℝ))) := Real.exp_pos _
    have h5 : (q (n + 1) : ℝ) < (Real.exp (-(b₀ * (q n : ℝ))))⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ hepos]
      linarith [h4]
    have h6 : (Real.exp (-(b₀ * (q n : ℝ))))⁻¹ = Real.exp (b₀ * (q n : ℝ)) := by
      rw [← Real.exp_neg]
      ring_nf
    rw [h6] at h5
    exact h5.le
  -- the phase charging, on the range dictated by `ℓ`
  have hcharge : ∀ n : ℕ, 1 ≤ n → 10 ^ 6 ≤ csm * (q n : ℝ) ^ 2 → ∀ ℓ : ℕ, 1 ≤ ℓ →
      (ℓ : ℝ) ≤ 2 * Real.rpow (q (n + 1) : ℝ) (8 / 9) / (q n : ℝ) →
      ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
        (∀ k : ℤ, |k| ≤ 4 * ((ℓ : ℤ) + 2) * (q n : ℤ) →
          c ≤ Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α)) ∧
        Real.log (1 / c) ≤ (Real.log (1 / csm) + 60) + 20 * Real.log ((q n : ℝ) + 2) := by
    intro n hn1 hbig ℓ hℓ hℓle
    have hqnR : (0 : ℝ) < (q n : ℝ) := by
      have := hqpos n; exact_mod_cast this
    have hℓqn : (ℓ : ℝ) * (q n : ℝ) ≤ 2 * Real.rpow (q (n + 1) : ℝ) (8 / 9) := by
      have h := mul_le_mul_of_nonneg_right hℓle (le_of_lt hqnR)
      rwa [div_mul_cancel₀ _ (ne_of_gt hqnR)] at h
    -- expand the `ℓ`-range to the range of the two re-folded estimates
    have hrange : ∀ k : ℤ, |k| ≤ 4 * ((ℓ : ℤ) + 2) * (q n : ℤ) →
        |(k : ℝ)| ≤ 8 * Real.rpow (q (n + 1) : ℝ) (8 / 9) + 8 * (q n : ℝ) + 4 := by
      intro k hk
      have hk' : ((|k| : ℤ) : ℝ) ≤ ((4 * ((ℓ : ℤ) + 2) * (q n : ℤ) : ℤ) : ℝ) := by
        exact_mod_cast hk
      rw [Int.cast_abs] at hk'
      push_cast at hk'
      linarith [hk', hℓqn]
    rcases le_or_gt (q (n + 1)) ((8 * q n) ^ 9) with hslow | hfast
    · obtain ⟨c, hc0, hc1, hr, hl⟩ :=
        Aux2.theta_range_slow2 hK₀1 hcsm (le_trans hcsm1 (by norm_num)) h1θ h2θ hqpos hslow
      exact ⟨c, hc0, hc1, fun k hk => hr k (hrange k hk), hl⟩
    · have hqn2 : (2 : ℝ) ≤ (q n : ℝ) := by
        have h := hqge n
        exact_mod_cast (by omega : 2 ≤ q n)
      refine ⟨2 / (q n : ℝ) ^ 2, by positivity, ?_, ?_, ?_⟩
      · rw [div_le_iff₀ (by positivity)]
        nlinarith [hqn2]
      · intro k hk
        exact Aux2.theta_range_fast2 hK₀1 hcsm h1θ h2θ hqpos hΔeq hΔup hn1 hbig hfast.le
          k (hrange k hk)
      · have hval : 1 / (2 / (q n : ℝ) ^ 2) = (q n : ℝ) ^ 2 / 2 := by
          rw [one_div, inv_div]
        rw [hval]
        have hxne : (q n : ℝ) ≠ 0 := ne_of_gt hqnR
        have h1 : Real.log ((q n : ℝ) ^ 2 / 2) ≤ 2 * Real.log (q n : ℝ) := by
          rw [show (q n : ℝ) ^ 2 = (q n : ℝ) * (q n : ℝ) by ring,
            Real.log_div (mul_ne_zero hxne hxne) (by norm_num),
            Real.log_mul hxne hxne]
          have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
          linarith
        have h2 : 2 * Real.log (q n : ℝ) ≤ 20 * Real.log ((q n : ℝ) + 2) := by
          have h3 : Real.log (q n : ℝ) ≤ Real.log ((q n : ℝ) + 2) :=
            Real.log_le_log (by
              have := hqpos n; exact_mod_cast this) (by linarith)
          have h4 : 0 ≤ Real.log ((q n : ℝ) + 2) := Real.log_nonneg (by linarith)
          linarith
        have h5 : 0 ≤ Real.log (1 / csm) + 60 := by
          have : 0 ≤ Real.log (1 / csm) := Real.log_nonneg (by
            rw [le_div_iff₀ hcsm, one_mul]; linarith [hcsm1])
          linarith
        linarith
  obtain ⟨Nb, hNb⟩ := hbig_all
  obtain ⟨Nq, hNq⟩ := hQr_all
  obtain ⟨Nk, hNk⟩ := hKd_all
  refine ⟨Nb + Nq + Nk + 20 ^ 9 + 2, ?_⟩
  intro n hn ℓ hℓ hℓle
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hbig : 10 ^ 6 ≤ csm * (q n : ℝ) ^ 2 := hNb n (by omega)
  have hQn : Qr ≤ (q n : ℝ) := hNq n (by omega)
  have hKdq : Kd ≤ q n := hNk n (by omega)
  have hqnpos : 0 < q n := hqpos n
  have hqnR : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hqnpos
  have hP9 : 20 ^ 9 ≤ q (n + 1) := by have := hqge (n + 1); omega
  have hℓb : 10 * (ℓ : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ) :=
    uni_res_ell_le2 hℓ hP9 hqnpos hℓle
  have hβ : (q (n + 1) : ℝ) ≤ Real.exp (b₀ * (q n : ℝ)) := hβall n hKdq
  obtain ⟨c, hcpos, hcle, hθ', hclog⟩ := hcharge n hn1 hbig ℓ hℓ hℓle
  have hcoll : ∀ j ∈ J1resG (5 * q n / 8) ∪ J2resG (q n) (5 * q n / 8) ℓ,
      -b₀ * (q n : ℝ) - 10 ≤
        ∑ i ∈ (J1resG (5 * q n / 8) ∪ J2resG (q n) (5 * q n / 8) ℓ).filter
            (fun i => i ≠ j ∧ (q n : ℤ) ∣ (i - j)),
          Real.log |Real.sin (Real.pi * (((i - j : ℤ)) : ℝ) * α)| :=
    coll_res (α := α) (β := b₀) (q := q) (n := n) (h := 5 * q n / 8) (ℓ := ℓ)
      (le_of_lt hb₀) (by omega) hℓ (by omega) le_rfl hℓb
      (by rw [← hΔeq n]; exact hΔlo n) (by rw [← hΔeq n]; exact (hΔup n).le) hβ
  have huni5 : Uniform (b₀ / 2 + b₀ / (4 * (q n : ℝ) - 2)
      + 2 * Real.log (1 / c) / (q n : ℝ)
      + 200 * Real.log (q n : ℝ) / (q n : ℝ) + 200 / (q n : ℝ))
      (fun j : {j : ℤ // j ∈ J1resG (5 * q n / 8) ∪ J2resG (q n) (5 * q n / 8) ℓ} =>
        θ + (j : ℝ) * α) :=
    uni_res5 (α := α) (β := b₀) (q := q) (Δ := Δ) (n := n) (h := 5 * q n / 8) (ℓ := ℓ)
      (θ := θ) (c := c) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest (le_of_lt hb₀) hn2 hℓ
      (by omega) le_rfl hℓb hβ hcpos hθ' hcoll
  have hrate : b₀ / 2 + b₀ / (4 * (q n : ℝ) - 2) + 2 * Real.log (1 / c) / (q n : ℝ)
      + 200 * Real.log (q n : ℝ) / (q n : ℝ) + 200 / (q n : ℝ)
      ≤ 9 * L / 64 + b₀ / 4 := by
    have h1 : 2 * Real.log (1 / c) / (q n : ℝ)
        ≤ 2 * (Real.log (1 / csm) + 60 + 20 * Real.log ((q n : ℝ) + 2)) / (q n : ℝ) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hqnR)
      linarith [hclog]
    have h2 := hQrb (q n : ℝ) hQn
    rw [show 9 * L / 32 - (9 * L / 32 - b₀ / 2) / 2 = 9 * L / 64 + b₀ / 4 by ring] at h2
    linarith [h2]
  refine Core.Uniform_equiv (uniResEquivSymm (q n) ℓ) ?_ (Uniform_mono hrate huni5)
  intro j
  have hval : (((uniResEquivSymm (q n) ℓ j : ℤ)) : ℝ) = (j : ℝ) - ((q n : ℝ) - 1) := by
    have h : ((uniResEquivSymm (q n) ℓ j : ℤ)) = (j : ℤ) - ((q n : ℤ) - 1) := rfl
    rw [h]
    push_cast
    ring
  simp only [hval]
  ring
end

end Work.TMC16Core.Assembly
