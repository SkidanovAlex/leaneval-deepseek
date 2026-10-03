import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.interchangeLDefs
import Submission.Work.Peluse.UlowerA.Defs
import Submission.Work.Peluse.UlowerA.pinLossU
import Submission.Work.Peluse.Ulower.StepLe.roundReduce
import Submission.Work.Peluse.Ulower.StepLe.pinLoss
import Submission.Work.Peluse.Ulower.StepLe.blindConvertK_pin
import Submission.Work.Peluse.Ulower.StepLe.blindConvertK_book
import Submission.Work.Peluse.Ulower.StepLe.fibrePairs
import Submission.Work.Peluse.Ulower.thetaSet_card_ge
import Submission.Work.Peluse.Ulower.conclTerm_uniform_bound
import Submission.Work.Peluse.Ulower.dualFn_norm_le_one

namespace Work.Peluse.Ulower.StepLe

-- The arithmetic comparison of the lossy final step (proved inline; see the description below).
private theorem arith_lossy_aux {σ : ℕ} {γ η γd ρ Λ δ agg DNs ci CΛ Kc : ℝ} {Ki K₂ : ℕ}
    (hγ0 : 0 < γ) (hγ9 : γ ≤ 9) (hci : 0 < ci) (hCΛ : 1 ≤ CΛ) (hKc : 1 ≤ Kc)
    (hη : Real.sqrt γ / 6 ≤ η) (hη1 : η ≤ 1)
    (hγd : γ / 36 ≤ γd) (hγd1 : γd ≤ 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hDN0 : 0 < DNs)
    (hδ : δ = min 1 (ci * (η * γd * ρ) ^ Ki)) (hδ0 : 0 < δ)
    (hΛpos : 0 < Λ) (hΛ : δ ^ (3 * K₂) * Λ ≤ CΛ / γ)
    (hDN : DNs ≤ Kc * ρ / η)
    (hagg : (γ / 4) * ci * (η * γd * ρ) ^ Ki * γd ^ (2 ^ σ) / Λ ≤ agg) :
    (4:ℝ)⁻¹ * ci * (ci / (1 + ci)) ^ (3 * K₂) * CΛ⁻¹ * ((36:ℝ)⁻¹) ^ (2 ^ σ)
        * ((648:ℝ)⁻¹) ^ (Ki + 3 * Ki * K₂)
        * ((6 * Kc)⁻¹) ^ (2 * (1 + 2 ^ σ + 2 * (Ki * (1 + 3 * K₂))) + 2)
      * (γ * DNs) ^ (2 * (1 + 2 ^ σ + 2 * (Ki * (1 + 3 * K₂))) + 2) ≤ agg := by
  have hη0 : 0 < η := by
    have h := Real.sqrt_pos.mpr hγ0
    linarith
  have hγd0 : 0 < γd := by linarith
  have hCΛ0 : 0 < CΛ := lt_of_lt_of_le one_pos hCΛ
  have hγsq : Real.sqrt γ ^ 2 = γ := Real.sq_sqrt hγ0.le
  have hγsqrt3 : Real.sqrt γ ≤ 3 := by
    have h := Real.sqrt_le_sqrt hγ9
    rwa [show Real.sqrt (9:ℝ) = 3 by
      rw [show (9:ℝ) = 3^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  -- `t = η γd ρ ∈ (0,1]`, `t ^ Ki ≤ 1`
  have ht0 : 0 < η * γd * ρ := by positivity
  have ht1 : η * γd * ρ ≤ 1 := by
    have ha : η * γd ≤ 1 := mul_le_one₀ hη1 hγd0.le hγd1
    exact mul_le_one₀ ha hρ0.le hρ1
  have htKi1 : (η * γd * ρ) ^ Ki ≤ 1 := pow_le_one₀ ht0.le ht1
  -- the δ-lower bound
  have hδge : ci * (η * γd * ρ) ^ Ki / (1 + ci) ≤ δ := by
    have hw0 : 0 ≤ ci * (η * γd * ρ) ^ Ki := by positivity
    have hmin : ci * (η * γd * ρ) ^ Ki / (1 + ci * (η * γd * ρ) ^ Ki) ≤ δ := by
      rw [hδ]
      apply le_min
      · rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + ci * (η * γd * ρ) ^ Ki)]
        linarith
      · rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + ci * (η * γd * ρ) ^ Ki)]
        nlinarith [hw0]
    have h1 : 1 + ci * (η * γd * ρ) ^ Ki ≤ 1 + ci := by nlinarith [htKi1, hw0]
    have h2 : ci * (η * γd * ρ) ^ Ki / (1 + ci)
        ≤ ci * (η * γd * ρ) ^ Ki / (1 + ci * (η * γd * ρ) ^ Ki) :=
      div_le_div_of_nonneg_left hw0 (by positivity) h1
    exact le_trans h2 hmin
  have hδpow : (ci / (1 + ci)) ^ (3 * K₂) * ((η * γd * ρ) ^ Ki) ^ (3 * K₂) ≤ δ ^ (3 * K₂) := by
    have h1 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ci * (η*γd*ρ)^Ki / (1+ci)) hδge (3 * K₂)
    have hEq : (ci * (η * γd * ρ) ^ Ki / (1 + ci)) ^ (3 * K₂)
        = (ci / (1 + ci)) ^ (3 * K₂) * ((η * γd * ρ) ^ Ki) ^ (3 * K₂) := by
      rw [div_pow, mul_pow, div_pow]
      ring
    rwa [hEq] at h1
  -- 1/Λ
  have hInv : γ * δ ^ (3 * K₂) / CΛ ≤ 1 / Λ := by
    have h1 : γ * δ ^ (3 * K₂) ≤ CΛ / Λ := by
      rw [le_div_iff₀ hΛpos]
      calc γ * δ ^ (3 * K₂) * Λ = γ * (δ ^ (3 * K₂) * Λ) := by ring
        _ ≤ γ * (CΛ / γ) := mul_le_mul_of_nonneg_left hΛ hγ0.le
        _ = CΛ := by field_simp
    rw [div_le_iff₀ hCΛ0, show (1 / Λ) * CΛ = CΛ / Λ by ring]
    exact h1
  have hagg1 : (γ / 4) * ci * (η * γd * ρ) ^ Ki * γd ^ (2 ^ σ) * (γ * δ ^ (3 * K₂) / CΛ)
      ≤ agg := by
    have hnn : (0:ℝ) ≤ (γ / 4) * ci * (η * γd * ρ) ^ Ki * γd ^ (2 ^ σ) := by positivity
    calc (γ / 4) * ci * (η * γd * ρ) ^ Ki * γd ^ (2 ^ σ) * (γ * δ ^ (3 * K₂) / CΛ)
        ≤ (γ / 4) * ci * (η * γd * ρ) ^ Ki * γd ^ (2 ^ σ) * (1 / Λ) :=
          mul_le_mul_of_nonneg_left hInv hnn
      _ = (γ / 4) * ci * (η * γd * ρ) ^ Ki * γd ^ (2 ^ σ) / Λ := by ring
      _ ≤ agg := hagg
  -- powers of `γ`
  have hηlb : γ / 18 ≤ η := by
    have h1 : γ / 3 ≤ Real.sqrt γ := by nlinarith [hγsq, Real.sqrt_nonneg γ, hγsqrt3]
    linarith
  have htlb : γ ^ 2 * ρ / 648 ≤ η * γd * ρ := by
    have h1 : (γ / 18) * (γ / 36) * ρ ≤ η * γd * ρ := by
      have h2 : (γ / 18) * (γ / 36) ≤ η * γd :=
        mul_le_mul hηlb hγd (by positivity) hη0.le
      exact mul_le_mul_of_nonneg_right h2 hρ0.le
    have h3 : γ ^ 2 * ρ / 648 = (γ / 18) * (γ / 36) * ρ := by ring
    linarith [h1, h3.le, h3.ge]
  -- the γd-substitution, division-free
  have hγdp : γ ^ (2 ^ σ) * ((36:ℝ)⁻¹) ^ (2 ^ σ) ≤ γd ^ (2 ^ σ) := by
    have h1 : γ * (36:ℝ)⁻¹ ≤ γd := by
      have h := hγd
      rwa [div_eq_mul_inv] at h
    have h2 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ γ * (36:ℝ)⁻¹) h1 (2 ^ σ)
    rwa [mul_pow] at h2
  -- exponent bookkeeping
  set N : ℕ := Ki + 3 * Ki * K₂ with hNdef
  set A : ℕ := 1 + 2 ^ σ + 2 * N with hAdef
  have hK'A : 2 * (1 + 2 ^ σ + 2 * (Ki * (1 + 3 * K₂))) + 2 = 2 * A + 2 := by
    rw [hAdef, hNdef]; ring
  have hA1 : A + 1 = 2 + 2 ^ σ + 2 * N := by rw [hAdef]; ring
  have htN : (η * γd * ρ) ^ Ki * ((η * γd * ρ) ^ Ki) ^ (3 * K₂) = (η * γd * ρ) ^ N := by
    rw [hNdef, ← pow_mul, ← pow_add]; congr 1; ring
  have htlbN : (γ ^ 2 * ρ) ^ N * ((648:ℝ)⁻¹) ^ N ≤ (η * γd * ρ) ^ N := by
    have h := pow_le_pow_left₀ (by positivity) htlb N
    rwa [show γ ^ 2 * ρ / 648 = (γ ^ 2 * ρ) * (648:ℝ)⁻¹ by ring, mul_pow] at h
  -- (1) the substitution into `hagg1`
  have hstep1 : (γ / 4) * ci * (η * γd * ρ) ^ Ki * (γ ^ (2 ^ σ) * ((36:ℝ)⁻¹) ^ (2 ^ σ))
        * (γ * ((ci / (1 + ci)) ^ (3 * K₂) * ((η * γd * ρ) ^ Ki) ^ (3 * K₂)) / CΛ)
      ≤ agg := by
    have hfac : γ ^ (2 ^ σ) * (((36:ℝ)⁻¹) ^ (2 ^ σ)
          * ((ci / (1 + ci)) ^ (3 * K₂) * ((η * γd * ρ) ^ Ki) ^ (3 * K₂)))
        ≤ γd ^ (2 ^ σ) * δ ^ (3 * K₂) := by
      calc γ ^ (2 ^ σ) * (((36:ℝ)⁻¹) ^ (2 ^ σ)
            * ((ci / (1 + ci)) ^ (3 * K₂) * ((η * γd * ρ) ^ Ki) ^ (3 * K₂)))
          = (γ ^ (2 ^ σ) * ((36:ℝ)⁻¹) ^ (2 ^ σ))
            * ((ci / (1 + ci)) ^ (3 * K₂) * ((η * γd * ρ) ^ Ki) ^ (3 * K₂)) := by ring
        _ ≤ γd ^ (2 ^ σ) * δ ^ (3 * K₂) :=
            mul_le_mul hγdp hδpow (by positivity) (by positivity)
    have h0 : (γ / 4) * ci * (η * γd * ρ) ^ Ki * (γ ^ (2 ^ σ) * ((36:ℝ)⁻¹) ^ (2 ^ σ))
          * (γ * ((ci / (1 + ci)) ^ (3 * K₂) * ((η * γd * ρ) ^ Ki) ^ (3 * K₂)) / CΛ)
        = (γ / 4) * ci * (η * γd * ρ) ^ Ki * γ
          * (γ ^ (2 ^ σ) * (((36:ℝ)⁻¹) ^ (2 ^ σ)
            * ((ci / (1 + ci)) ^ (3 * K₂) * ((η * γd * ρ) ^ Ki) ^ (3 * K₂)))) / CΛ := by ring
    rw [h0]
    have h1 : (γ / 4) * ci * (η * γd * ρ) ^ Ki * γ
          * (γ ^ (2 ^ σ) * (((36:ℝ)⁻¹) ^ (2 ^ σ)
            * ((ci / (1 + ci)) ^ (3 * K₂) * ((η * γd * ρ) ^ Ki) ^ (3 * K₂))))
        ≤ (γ / 4) * ci * (η * γd * ρ) ^ Ki * γ * (γd ^ (2 ^ σ) * δ ^ (3 * K₂)) :=
      mul_le_mul_of_nonneg_left hfac (by positivity)
    refine le_trans (div_le_div_of_nonneg_right h1 (le_of_lt hCΛ0))
      (le_trans (le_of_eq ?_) hagg1)
    ring
  -- (2) the canonical lower bound
  set Ccan : ℝ := (4:ℝ)⁻¹ * ci * (ci / (1 + ci)) ^ (3 * K₂) * CΛ⁻¹ * ((36:ℝ)⁻¹) ^ (2 ^ σ)
    with hCcan
  have hCore_eq : Ccan * γ ^ (2 + 2 ^ σ) * (η * γd * ρ) ^ N
      = (γ / 4) * ci * (η * γd * ρ) ^ Ki * (γ ^ (2 ^ σ) * ((36:ℝ)⁻¹) ^ (2 ^ σ))
        * (γ * ((ci / (1 + ci)) ^ (3 * K₂) * ((η * γd * ρ) ^ Ki) ^ (3 * K₂)) / CΛ) := by
    rw [hCcan, ← htN, pow_add (γ) 2 (2 ^ σ)]
    ring
  have hCore_ge : Ccan * ((648:ℝ)⁻¹) ^ N * (γ ^ (A + 1) * ρ ^ N)
      ≤ Ccan * γ ^ (2 + 2 ^ σ) * (η * γd * ρ) ^ N := by
    have h := mul_le_mul_of_nonneg_left htlbN (by positivity : (0:ℝ) ≤ Ccan * γ ^ (2 + 2 ^ σ))
    have hid : Ccan * γ ^ (2 + 2 ^ σ) * ((γ ^ 2 * ρ) ^ N * ((648:ℝ)⁻¹) ^ N)
        = Ccan * ((648:ℝ)⁻¹) ^ N * (γ ^ (A + 1) * ρ ^ N) := by
      rw [hA1, pow_add (γ) (2 + 2 ^ σ) (2 * N), mul_pow, ← pow_mul]
      ring
    rw [hid] at h
    exact h
  -- (3) the `(γ DNs)`-bound
  have hDNsbound : γ * DNs ≤ 6 * Kc * ρ * Real.sqrt γ := by
    have h1 : 1 / η ≤ 6 / Real.sqrt γ := by
      rw [div_le_div_iff₀ hη0 (Real.sqrt_pos.mpr hγ0)]
      linarith [hη, Real.sqrt_pos.mpr hγ0, Real.sqrt_nonneg γ]
    have h2 : ρ / η ≤ 6 * ρ / Real.sqrt γ := by
      calc ρ / η = ρ * (1 / η) := by ring
        _ ≤ ρ * (6 / Real.sqrt γ) := mul_le_mul_of_nonneg_left h1 hρ0.le
        _ = 6 * ρ / Real.sqrt γ := by ring
    calc γ * DNs ≤ γ * (Kc * ρ / η) := mul_le_mul_of_nonneg_left hDN hγ0.le
      _ = γ * Kc * (ρ / η) := by ring
      _ ≤ γ * Kc * (6 * ρ / Real.sqrt γ) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 6 * Kc * ρ * Real.sqrt γ := by
        rw [show γ * Kc * (6 * ρ / Real.sqrt γ) = 6 * Kc * ρ * (γ / Real.sqrt γ) by ring]
        rw [Real.div_sqrt]
  have hx2 : ((6 * Kc)⁻¹ * (γ * DNs)) ^ (2 * A + 2) ≤ γ ^ (A + 1) * ρ ^ N := by
    have h1 : (6 * Kc)⁻¹ * (γ * DNs) ≤ ρ * Real.sqrt γ := by
      have h := mul_le_mul_of_nonneg_left hDNsbound (by positivity : (0:ℝ) ≤ (6 * Kc)⁻¹)
      refine le_trans h (le_of_eq ?_)
      field_simp
    have h2 : ((6 * Kc)⁻¹ * (γ * DNs)) ^ (2 * A + 2)
        ≤ (ρ * Real.sqrt γ) ^ (2 * A + 2) :=
      pow_le_pow_left₀ (by positivity) h1 (2 * A + 2)
    have h3 : (ρ * Real.sqrt γ) ^ (2 * A + 2) = ρ ^ (2 * A + 2) * γ ^ (A + 1) := by
      rw [mul_pow, show (Real.sqrt γ) ^ (2 * A + 2) = γ ^ (A + 1) by
        rw [show 2 * A + 2 = 2 * (A + 1) by ring, pow_mul, hγsq]]
    have h4 : ρ ^ (2 * A + 2) ≤ ρ ^ N := by
      refine pow_le_pow_of_le_one hρ0.le hρ1 ?_
      rw [hAdef]
      have h2σ : 1 ≤ 2 ^ σ := Nat.one_le_two_pow
      omega
    calc ((6 * Kc)⁻¹ * (γ * DNs)) ^ (2 * A + 2)
        ≤ (ρ * Real.sqrt γ) ^ (2 * A + 2) := h2
      _ = ρ ^ (2 * A + 2) * γ ^ (A + 1) := h3
      _ ≤ ρ ^ N * γ ^ (A + 1) := mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = γ ^ (A + 1) * ρ ^ N := by ring
  -- (4) assembly
  have hgoal : (4:ℝ)⁻¹ * ci * (ci / (1 + ci)) ^ (3 * K₂) * CΛ⁻¹ * ((36:ℝ)⁻¹) ^ (2 ^ σ)
        * ((648:ℝ)⁻¹) ^ N * ((6 * Kc)⁻¹) ^ (2 * A + 2) * (γ * DNs) ^ (2 * A + 2) ≤ agg := by
    have heq : (4:ℝ)⁻¹ * ci * (ci / (1 + ci)) ^ (3 * K₂) * CΛ⁻¹ * ((36:ℝ)⁻¹) ^ (2 ^ σ)
          * ((648:ℝ)⁻¹) ^ N * ((6 * Kc)⁻¹) ^ (2 * A + 2) * (γ * DNs) ^ (2 * A + 2)
        = Ccan * ((648:ℝ)⁻¹) ^ N * (((6 * Kc)⁻¹ * (γ * DNs)) ^ (2 * A + 2)) := by
      rw [hCcan, mul_pow]
      ring
    rw [heq]
    calc Ccan * ((648:ℝ)⁻¹) ^ N * (((6 * Kc)⁻¹ * (γ * DNs)) ^ (2 * A + 2))
        ≤ Ccan * ((648:ℝ)⁻¹) ^ N * (γ ^ (A + 1) * ρ ^ N) :=
          mul_le_mul_of_nonneg_left hx2 (by positivity)
      _ ≤ Ccan * γ ^ (2 + 2 ^ σ) * (η * γd * ρ) ^ N := hCore_ge
      _ = (γ / 4) * ci * (η * γd * ρ) ^ Ki * (γ ^ (2 ^ σ) * ((36:ℝ)⁻¹) ^ (2 ^ σ))
            * (γ * ((ci / (1 + ci)) ^ (3 * K₂) * ((η * γd * ρ) ^ Ki) ^ (3 * K₂)) / CΛ) := hCore_eq
      _ ≤ agg := hstep1
  rw [hNdef, ← hK'A] at hgoal
  exact hgoal

/-
Assembly of `blindConvertK2` from the **lossy** interchange `HasInterchangeL`.

This is `Work.Peluse.Ulower.StepLe.blindConvertK_of` (`StepLe/blindConvertK_main.lean`) with the
*sharp* interchange predicate `HasInterchange` replaced by the *lossy* `HasInterchangeL`
(`StepLe/interchangeLDefs.lean`) and the conclusion `blindConvertK` replaced by `blindConvertK2`
(the middle step with the extra `(D/Ns)^K'` on the left of the conclusion), which is exactly what
`Work.Peluse.Ulower.steple_of` consumes.

Recipe: the whole proof of `blindConvertK_of` can be copied.  Only these change:
* `hInt'` becomes `hInt σ hσ K hK` (the lossy predicate quantifies `∀ K₀ ≥ 1` *before* `∃ c, ∃ Ki`);
* in Step 3 the lossy interchange produces the density/level
  `ci * (eta * gammaD * ((D:ℝ)/(B:ℝ))) ^ Ki` (call `rho := (D:ℝ)/(B:ℝ)`) instead of
  `ci * (eta * gammaD) ^ Ki`; everything downstream is the same with `eta * gammaD` replaced by
  `eta * gammaD * rho` where the *interchange* level is used, while the Markov density `gammaD`
  (Step 2) is untouched — in particular `thetaSet_card_ge` is still applied with `gammaD`;
* so `delta := min 1 (ci * (eta * gammaD * rho) ^ Ki)`;
* the final arithmetic is the lossy comparison; `StepLe/blindConvertK_arith_lossy` is being proved
  in parallel and states exactly the needed estimate (from
  `(γ/4)*ci*(η*γd*rho)^Ki*γd^(2^σ)/Λ ≤ agg`, `rho ≤ 1` and `D/Ns ≤ K*rho/η` — the latter is
  `Ns/B ≥ η/C` with `C` the data-independent constant of `hBnd` — it produces `K'` with
  `cfin * (γ*(D/Ns))^{K'} ≤ agg`; if that module is not yet available, prove the same estimate
  inline).
-/

/-! ## Elementary support and size bounds -/

/-- The sharp per-element bound on the aggregate's summands: the cube term of `F` is supported in
`symIcc (S + σD)` and bounded by `1`, so the `B⁻¹`-normalised correlation is at most
`(2(S+σD)+1)/B`. -/
lemma cubeAmp_le_support_I {σ B S D : ℕ} {F : ℤ → ℂ}
    (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) (u v : Fin σ → ℤ) (hB : 1 ≤ B)
    (hF1 : ∀ x : ℤ, ‖F x‖ ≤ 1) (hFs : Work.Peluse.SupportIn F S)
    (hv : ∀ i : Fin σ, (v i).natAbs ≤ D) (hSB : S + σ * D ≤ B) :
    cubeAmp B F β u v ≤ (((2 * (S + σ * D) + 1 : ℕ)) : ℝ) / (B : ℝ) := by
  have hterm1 : ∀ x : ℤ, ‖Work.Peluse.cubeTerm u v F x‖ ≤ 1 :=
    fun x => Work.Peluse.Ulower.norm_cubeTerm_le hF1 u v x
  have hsupp : Work.Peluse.SupportIn (Work.Peluse.cubeTerm u v F) (S + σ * D) :=
    Work.Peluse.Ulower.supportIn_cubeTerm hFs hv
  have htsum : (∑' x : ℤ, ‖Work.Peluse.cubeTerm u v F x‖) ≤ ((2 * (S + σ * D) + 1 : ℕ) : ℝ) :=
    Work.Peluse.Ulower.supportIn_tsum_le hsupp hterm1
  have hsumm : Summable (fun x : ℤ => ‖Work.Peluse.cubeTerm u v F x *
      Complex.exp (2 * Real.pi * Complex.I * (β u v : ℂ) * (x : ℂ))‖) := by
    apply summable_of_ne_finset_zero
      (s := Finset.Icc (-(((S + σ * D) : ℕ) : ℤ)) (((S + σ * D) : ℕ) : ℤ))
    intro x hx
    have hx0 : Work.Peluse.cubeTerm u v F x = 0 := by
      apply Work.Peluse.Ulower.supportIn_off_Icc hsupp x
      simpa using hx
    rw [hx0, zero_mul, norm_zero]
  have hnorm : ‖∑' x : ℤ, Work.Peluse.cubeTerm u v F x *
        Complex.exp (2 * Real.pi * Complex.I * (β u v : ℂ) * (x : ℂ))‖
      ≤ ((2 * (S + σ * D) + 1 : ℕ) : ℝ) := by
    have h := norm_tsum_le_tsum_norm hsumm
    have hcongr : (∑' x : ℤ, ‖Work.Peluse.cubeTerm u v F x *
          Complex.exp (2 * Real.pi * Complex.I * (β u v : ℂ) * (x : ℂ))‖)
        = ∑' x : ℤ, ‖Work.Peluse.cubeTerm u v F x‖ :=
      tsum_congr (fun x => by rw [norm_mul, norm_exp_two_pi_I_mul (β u v) x, mul_one])
    rw [hcongr] at h
    exact h.trans htsum
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hstep : ‖((B : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v F x *
        Complex.exp (2 * Real.pi * Complex.I * (β u v : ℂ) * (x : ℂ))‖
      ≤ (((2 * (S + σ * D) + 1 : ℕ)) : ℝ) / (B : ℝ) := by
    rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right hnorm (le_of_lt hBpos)
  simpa [cubeAmp] using hstep

open Work.Peluse.Ulower in
/-- The iterated `Δ'`-difference of a function supported in `[-L,L]` is supported in
`[-L-σD, L+σD]` when all the coordinates of all the shift pairs are bounded by `D` in absolute
value.  (Sharper than `conclTerm_uniform_bound.iterDelta'_supportIn_le` by a factor `2`: at each
step only the *smaller* of the two shift coordinates is paid for, because the support of a product
is contained in the intersection of the two pulled-back supports.) -/
lemma iterDelta'_supportIn_add_I {D : ℕ} :
    ∀ (k : ℕ) (sh : Fin k → ℤ × ℤ) {L : ℕ} {F : ℤ → ℂ},
    (∀ i : Fin k, (sh i).1.natAbs ≤ D ∧ (sh i).2.natAbs ≤ D) →
    Work.Peluse.SupportIn F L → Work.Peluse.SupportIn (iterDelta' k sh F) (L + k * D) := by
  intro k
  induction k with
  | zero =>
      intro sh L F _ hF x hx
      exact hF x (by simpa using hx)
  | succ k ih =>
      intro sh L F hsh hF x hx
      have htail : ∀ i : Fin k, (sh i.succ).1.natAbs ≤ D ∧ (sh i.succ).2.natAbs ≤ D :=
        fun i => hsh i.succ
      have ih' := ih (fun i => sh i.succ) htail hF
      have hdef : iterDelta' (k + 1) sh F x =
          star (iterDelta' k (fun i => sh i.succ) F (x + (sh 0).1)) *
            iterDelta' k (fun i => sh i.succ) F (x + (sh 0).2) := rfl
      rw [hdef]
      have key : ∀ a : ℤ, a.natAbs ≤ D →
          iterDelta' k (fun i => sh i.succ) F (x + a) = 0 := by
        intro a ha
        apply ih'
        have h1 : (x + a).natAbs + a.natAbs ≥ x.natAbs := by
          have h := Int.natAbs_add_le (x + a) (-a)
          rw [add_neg_cancel_right, Int.natAbs_neg] at h
          exact h
        have hR : L + (k + 1) * D = L + k * D + D := by ring
        have hx' : L + k * D + D < x.natAbs := by rw [hR] at hx; exact hx
        omega
      rw [key (sh 0).1 (hsh 0).1, key (sh 0).2 (hsh 0).2, star_zero, zero_mul]

set_option maxHeartbeats 8000000

/-! ## Elementary index facts -/

private lemma arithIcc_one_eq' (D : ℕ) :
    Work.Peluse.arithIcc 1 D = Finset.Icc (1 : ℤ) (D : ℤ) := by
  ext z
  simp only [Work.Peluse.arithIcc, Finset.mem_image, Finset.mem_Icc, one_mul]
  constructor
  · rintro ⟨n, ⟨h1, h2⟩, rfl⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · intro hz
    have hznn : 0 ≤ z := by omega
    refine ⟨z.toNat, ⟨?_, ?_⟩, ?_⟩
    · exact_mod_cast (show (1 : ℤ) ≤ (z.toNat : ℤ) by
        rw [Int.toNat_of_nonneg hznn]; omega)
    · exact_mod_cast (show (z.toNat : ℤ) ≤ (D : ℤ) by
        rw [Int.toNat_of_nonneg hznn]; omega)
    · simp [Int.toNat_of_nonneg hznn]

private lemma card_piFinset_arithIcc' (s D : ℕ) :
    (Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D)).card = D ^ s := by
  rw [Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [arithIcc_one_eq', Int.card_Icc]
  have h : (D : ℤ) + 1 - 1 = (D : ℤ) := by ring
  rw [h]
  simp

private lemma natAbs_le_of_mem_Icc_one' {D : ℕ} {a : ℤ} (h : a ∈ Finset.Icc (1 : ℤ) (D : ℤ)) :
    a.natAbs ≤ D := by
  rw [Finset.mem_Icc] at h
  have h1 : |a| ≤ (D : ℤ) := abs_le.mpr ⟨by omega, h.2⟩
  rw [Int.abs_eq_natAbs] at h1
  exact_mod_cast h1

/-- The iterated `Δ'`-difference of a `1`-bounded function is `1`-bounded. -/
private lemma norm_iterDelta'_le_one' : ∀ (k : ℕ) (sh : Fin k → ℤ × ℤ) (G : ℤ → ℂ),
    (∀ x : ℤ, ‖G x‖ ≤ 1) → ∀ x : ℤ, ‖Work.Peluse.Ulower.iterDelta' k sh G x‖ ≤ 1 := by
  intro k
  induction k with
  | zero => intro sh G h x; exact h x
  | succ k ih =>
      intro sh G h x
      have hdef : Work.Peluse.Ulower.iterDelta' (k + 1) sh G x =
          star (Work.Peluse.Ulower.iterDelta' k (fun i => sh i.succ) G (x + (sh 0).1)) *
            Work.Peluse.Ulower.iterDelta' k (fun i => sh i.succ) G (x + (sh 0).2) := rfl
      rw [hdef, norm_mul, norm_star]
      have h1 := ih (fun i => sh i.succ) G h (x + (sh 0).1)
      have h2 := ih (fun i => sh i.succ) G h (x + (sh 0).2)
      nlinarith [h1, h2,
        norm_nonneg (Work.Peluse.Ulower.iterDelta' k (fun i => sh i.succ) G (x + (sh 0).1)),
        norm_nonneg (Work.Peluse.Ulower.iterDelta' k (fun i => sh i.succ) G (x + (sh 0).2))]

theorem blindConvertK_of_interchangeLU {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree)
    (h2 : Work.Peluse.PeluseMajorArc P)
    (hInt : ∀ C : ℕ, 1 ≤ C → Work.Peluse.UlowerA.HasInterchangeLU P C)
    (K : ℝ) (hK : 1 ≤ K) :
    ∀ C : ℕ, 1 ≤ C → ∀ σ : ℕ, 1 ≤ σ → ∃ c : ℝ, 0 < c ∧ ∃ K' : ℕ, 1 ≤ K' ∧
      ∀ (B Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ) (θ γ : ℝ)
        (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ),
        1 ≤ N → 1 ≤ Ns → Work.Peluse.UlowerA.UnbalScale P C Ns N → N ≤ Ns →
        1 ≤ D → (D : ℝ) ≤ K * (Ns : ℝ) →
        Work.Peluse.SupportIn f₀ Ns → Work.Peluse.SupportIn f₁ Ns →
        (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
        Work.Peluse.dSup P Ns N + 2 * σ * D ≤ B →
        0 < θ → θ ≤ 1 →
        θ ≤ Work.Peluse.boxNormPow (σ + 2) (fun _ : Fin (σ + 2) => Work.Peluse.arithIcc 1 D)
              (Work.Peluse.symIcc B) (Work.Peluse.dualFn N P f₀ f₁) →
        0 < γ →
        γ ≤ ((Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D)).card : ℝ)⁻¹ *
            ((Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D)).card : ℝ)⁻¹ *
            ∑ u ∈ Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D),
              ∑ v ∈ Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D),
                ‖((B : ℂ))⁻¹ * ∑' x : ℤ,
                  Work.Peluse.cubeTerm u v (Work.Peluse.dualFn N P f₀ f₁) x *
                  Complex.exp (2 * Real.pi * Complex.I * (β u v : ℂ) * (x : ℂ))‖ ^ 2 →
        ∃ ψ : Fin σ → (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ,
          (∀ i : Fin σ, ∀ u : Fin σ → ℤ, ∀ v : Fin σ → ℤ, ∀ a b : ℤ,
            ψ i u (Function.update v i a) = ψ i u (Function.update v i b)) ∧
          c * (γ * ((D : ℝ) / (Ns : ℝ))) ^ K' ≤
            ((Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D)).card : ℝ)⁻¹ *
            ((Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D)).card : ℝ)⁻¹ *
            ∑ u ∈ Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D),
              ∑ v ∈ Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D),
                ‖((B : ℂ))⁻¹ * ∑' x : ℤ,
                  Work.Peluse.cubeTerm u v (Work.Peluse.dualFn N P f₀ f₁) x *
                  Complex.exp (2 * Real.pi * Complex.I *
                    ((∑ i : Fin σ, ψ i u v) : ℂ) * (x : ℂ))‖ ^ 2 := by
  intro C hC σ hσ
  classical
  obtain ⟨C', hC'pos, Kp, hKp, hmain⟩ := h2
  obtain ⟨ci, hcipos, Ki, hKi, hInt'⟩ := hInt C hC σ hσ K hK
  have hσnn : (0 : ℝ) ≤ (σ : ℝ) := Nat.cast_nonneg σ
  -- the data-independent constants of the final bound
  set CS : ℝ := (C : ℝ) + σ * K with hCSdef
  have hCS1 : 1 ≤ CS := by
    rw [hCSdef]
    have hC1 : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
    nlinarith [hC1, hK, hσnn]
  set CLam : ℝ := ((2 : ℝ) ^ (σ + 1) + 3) * 4 * (C' + 2) ^ 2 *
      (2 * (C' * (18 + 48 * Real.pi * (2 * CS * (C : ℝ) + 1))) + 9) with hCLamdef
  have hCLam1 : 1 ≤ CLam := by
    rw [hCLamdef]
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (σ + 1) + 3 := by
      have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (σ + 1) := one_le_pow₀ (by norm_num)
      linarith
    have h2 : (1 : ℝ) ≤ 4 * (C' + 2) ^ 2 := by nlinarith [hC'pos, sq_nonneg (C' + 2)]
    have h3 : (1 : ℝ) ≤ 2 * (C' * (18 + 48 * Real.pi * (2 * CS * (C : ℝ) + 1))) + 9 := by
      have hCSnn : (0 : ℝ) ≤ CS := by rw [hCSdef]; positivity
      have hCnn : (0 : ℝ) ≤ ((C : ℕ) : ℝ) := by positivity
      have hbr : (0 : ℝ) ≤ 2 * CS * ((C : ℕ) : ℝ) + 1 := by positivity
      have hx : (0 : ℝ) ≤ C' * (18 + 48 * Real.pi * (2 * CS * ((C : ℕ) : ℝ) + 1)) :=
        mul_nonneg (le_of_lt hC'pos) (by
          have h2 : (0 : ℝ) ≤ 48 * Real.pi * (2 * CS * ((C : ℕ) : ℝ) + 1) := by positivity
          linarith)
      linarith
    have hA : (0 : ℝ) ≤ (2 : ℝ) ^ (σ + 1) + 3 := by linarith
    have hB : (0 : ℝ) ≤ 4 * (C' + 2) ^ 2 := by nlinarith [sq_nonneg (C' + 2)]
    have h12 : (1 : ℝ) ≤ ((2 : ℝ) ^ (σ + 1) + 3) * (4 * (C' + 2) ^ 2) := by
      have h := mul_le_mul h1 h2 (by norm_num : (0 : ℝ) ≤ 1) hA
      simpa using h
    have h123 : (1 : ℝ) ≤ (((2 : ℝ) ^ (σ + 1) + 3) * (4 * (C' + 2) ^ 2)) *
        (2 * (C' * (18 + 48 * Real.pi * (2 * CS * (C : ℝ) + 1))) + 9) := by
      have hB2 : (0 : ℝ) ≤ ((2 : ℝ) ^ (σ + 1) + 3) * (4 * (C' + 2) ^ 2) :=
        mul_nonneg hA hB
      have h := mul_le_mul h12 h3 (by norm_num : (0 : ℝ) ≤ 1) hB2
      simpa using h
    calc (1 : ℝ) ≤ (((2 : ℝ) ^ (σ + 1) + 3) * (4 * (C' + 2) ^ 2)) *
          (2 * (C' * (18 + 48 * Real.pi * (2 * CS * (C : ℝ) + 1))) + 9) := h123
      _ = ((2 : ℝ) ^ (σ + 1) + 3) * 4 * (C' + 2) ^ 2 *
          (2 * (C' * (18 + 48 * Real.pi * (2 * CS * (C : ℝ) + 1))) + 9) := by ring
  set Kc : ℝ := 2 * CS + 1 with hKcdef
  have hKc1 : 1 ≤ Kc := by rw [hKcdef]; linarith [hCS1]
  set K' : ℕ := 2 * (1 + 2 ^ σ + 2 * (Ki * (1 + 3 * Kp))) + 2 with hK'def
  have hK'1 : 1 ≤ K' := by
    rw [hK'def]
    have h2σ : 1 ≤ 2 ^ σ := Nat.one_le_two_pow
    omega
  set cfin : ℝ := (4:ℝ)⁻¹ * ci * (ci / (1 + ci)) ^ (3 * Kp) * CLam⁻¹ * ((36:ℝ)⁻¹) ^ (2 ^ σ)
      * ((648:ℝ)⁻¹) ^ (Ki + 3 * Ki * Kp) * ((6 * Kc)⁻¹) ^ K' with hcfin
  have hcfinpos : 0 < cfin := by
    rw [hcfin]
    have h1 : (0 : ℝ) < 1 + ci := by linarith
    have h2 : (0 : ℝ) < ci / (1 + ci) := by positivity
    have h3 : (0 : ℝ) < CLam := lt_of_lt_of_le one_pos hCLam1
    have h4 : (0 : ℝ) < 6 * Kc := by linarith
    positivity

  refine ⟨cfin, hcfinpos, K', hK'1, ?_⟩
  intro B Ns N D f₀ f₁ θ γ β hN hNs hScaled hNNs hD hDK hsup0 hsup1 hb0 hb1 hSB
    hθ hθ1 hbox hγ haggr
  let F : ℤ → ℂ := Work.Peluse.dualFn N P f₀ f₁
  have hNpos : 0 < N := by omega
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNs1 : (1 : ℝ) ≤ (Ns : ℝ) := by exact_mod_cast hNs
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hF1 : ∀ x : ℤ, ‖F x‖ ≤ 1 :=
    fun x => Work.Peluse.Ulower.dualFn_norm_le_one hN P f₀ f₁ hb0 hb1 x
  have hFs : Work.Peluse.SupportIn F (Work.Peluse.dSup P Ns N) :=
    Work.Peluse.Tools.dualFn_supportIn hNpos P f₀ f₁ hsup0 hsup1 hNNs
  have hdsup : Ns ≤ Work.Peluse.dSup P Ns N := by
    rw [Work.Peluse.dSup]; exact Nat.le_add_right _ _
  have hSB' : Work.Peluse.dSup P Ns N + σ * D ≤ B := by
    have hmm : σ * D ≤ 2 * σ * D := by
      nlinarith [Nat.zero_le (σ * D)]
    omega
  have hB1 : 1 ≤ B := by omega
  have hB1R : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB1
  have haggr' : γ ≤ aggr σ D B F β := haggr
  -- the pointwise bound and `γ ≤ 9`
  have hCubeBound : aggr σ D B F β ≤ (((2 * B + 1 : ℕ) : ℝ) / (B : ℝ)) ^ 2 := by
    have hboxpos : (0 : ℝ) < ((pairBox σ D).card : ℝ) := by
      have hc : 0 < (pairBox σ D).card := by
        refine Finset.card_pos.mpr ⟨(fun _ => (1 : ℤ), fun _ => (1 : ℤ)), ?_⟩
        rw [pairBox, Finset.mem_product]
        constructor <;> refine Fintype.mem_piFinset.mpr (fun _ => ?_)
        · show (1 : ℤ) ∈ Work.Peluse.arithIcc 1 D
          rw [arithIcc_one_eq']
          exact Finset.mem_Icc.mpr ⟨le_rfl, by exact_mod_cast hD⟩
        · show (1 : ℤ) ∈ Work.Peluse.arithIcc 1 D
          rw [arithIcc_one_eq']
          exact Finset.mem_Icc.mpr ⟨le_rfl, by exact_mod_cast hD⟩
      exact_mod_cast hc
    rw [aggr_eq]
    rw [inv_mul_eq_div, div_le_iff₀ hboxpos]
    have hle : ∀ p ∈ pairBox σ D,
        cubeCorr σ B F β p.1 p.2 ≤ (((2 * B + 1 : ℕ) : ℝ) / (B : ℝ)) ^ 2 := by
      intro p hp
      obtain ⟨hu, hv⟩ := mem_pairBox hp
      exact cubeCorr_le β p.1 p.2 hB1 hF1 hFs hSB'
        (fun i => natAbs_le_of_mem_arithIcc_one (hv i))
    calc ∑ p ∈ pairBox σ D, cubeCorr σ B F β p.1 p.2
        ≤ ∑ _p ∈ pairBox σ D, (((2 * B + 1 : ℕ) : ℝ) / (B : ℝ)) ^ 2 :=
          Finset.sum_le_sum hle
      _ = (((2 * B + 1 : ℕ) : ℝ) / (B : ℝ)) ^ 2 * ((pairBox σ D).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hratio : ((2 * B + 1 : ℕ) : ℝ) / (B : ℝ) ≤ 3 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (B : ℝ))]
    have h' : ((2 * B + 1 : ℕ) : ℝ) ≤ 3 * (B : ℝ) := by
      have h2 : 2 * B + 1 ≤ 3 * B := by omega
      calc ((2 * B + 1 : ℕ) : ℝ) ≤ ((3 * B : ℕ) : ℝ) := by exact_mod_cast h2
        _ = 3 * (B : ℝ) := by push_cast; ring
    linarith [h']
  have hγ9 : γ ≤ 9 := by
    have hnn : (0 : ℝ) ≤ ((2 * B + 1 : ℕ) : ℝ) / (B : ℝ) := by positivity
    have hsq : (((2 * B + 1 : ℕ) : ℝ) / (B : ℝ)) ^ 2 ≤ 9 := by nlinarith [hratio, hnn]
    exact le_trans haggr' (le_trans hCubeBound hsq)
  -- the lossy `D/B`-factor of the interchange, and the data-independent constant of the
  -- final arithmetic (the bound `D/Ns ≤ Kc·ρ/η` is consumed by `blindConvertK_arith_lossy`)
  set rho : ℝ := (D : ℝ) / (B : ℝ) with hrhodef
  have hBposR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB1
  have hDposR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hrho0 : 0 < rho := by rw [hrhodef]; exact div_pos hDposR hBposR
  have hDB : D ≤ B := by
    have h1 : D ≤ 2 * σ * D := by
      have h0 : 1 ≤ 2 * σ := by omega
      calc D = 1 * D := (one_mul D).symm
        _ ≤ (2 * σ) * D := Nat.mul_le_mul_right D h0
    have h3 : 2 * σ * D ≤ Work.Peluse.dSup P Ns N + 2 * σ * D := Nat.le_add_left _ _
    exact le_trans h1 (le_trans h3 hSB)
  have hrho1 : rho ≤ 1 := by
    rw [hrhodef, div_le_one hBposR]
    exact_mod_cast hDB

  -- Step 1: reduce and round the phases
  obtain ⟨T, β', hT1, hTbig, hTle, hgrβ, hβ0, hβ1, haggr2⟩ :=
    Work.Peluse.Ulower.StepLe.roundReduce (S := Work.Peluse.dSup P Ns N) β hB1 hD hF1 hFs hSB' hγ haggr'
  -- Step 2: Markov extraction of `H₁`
  set C0 : ℝ := (((2 * B + 1 : ℕ) : ℝ) / (B : ℝ)) ^ 2 with hC0def
  have hC0pos : 0 < C0 := by rw [hC0def]; positivity
  obtain ⟨H₁, hH₁sub, hH₁dens, hH₁lvl⟩ :=
    markov β' hB1 hD hF1 hFs hSB' (show (0 : ℝ) < γ / 2 by linarith) haggr2
  have hpaircard : ((pairBox σ D).card : ℝ) = (D : ℝ) ^ (2 * σ) := by
    rw [pairBox_card, card_piFinset_arithIcc']
    push_cast
    rw [← pow_mul]
    congr 1
    ring
  have hDσpos : (0 : ℝ) < (D : ℝ) ^ σ := by positivity
  have hD2σpos : (0 : ℝ) < (D : ℝ) ^ (2 * σ) := by positivity
  set gammaD : ℝ := γ / (4 * C0) with hgammaD
  have hgammaDpos : 0 < gammaD := by rw [hgammaD]; positivity
  have hH₁dens' : gammaD * (D : ℝ) ^ (2 * σ) ≤ (H₁.card : ℝ) := by
    have h2 : (γ / 2) / (2 * (((2 * B + 1 : ℕ) : ℝ) / (B : ℝ)) ^ 2) = gammaD := by
      rw [hgammaD, hC0def]; ring
    have h := hH₁dens
    rw [h2, hpaircard] at h
    exact h
  have hH₁ne : H₁.Nonempty := by
    have hpos : (0 : ℝ) < (H₁.card : ℝ) := by
      have hD2 : (0 : ℝ) < (D : ℝ) ^ (2 * σ) := by positivity
      nlinarith [hH₁dens', hgammaDpos, hD2]
    exact Finset.card_pos.mp (by exact_mod_cast hpos)
  set eta : ℝ := min 1 (Real.sqrt (γ / 4)) with heta
  have hetapos : 0 < eta := by
    rw [heta]; exact lt_min one_pos (Real.sqrt_pos.mpr (by linarith))
  have heta1 : eta ≤ 1 := by rw [heta]; exact min_le_left _ _
  have hlvlC : ∀ p ∈ H₁, eta ≤ cubeAmp B F β' p.1 p.2 := by
    intro p hp
    have h1 : γ / 4 ≤ cubeCorr σ B F β' p.1 p.2 := by
      have h := hH₁lvl p hp
      linarith
    have h3 : (cubeAmp B F β' p.1 p.2) ^ 2 = cubeCorr σ B F β' p.1 p.2 :=
      cubeAmp_sq B F β' p.1 p.2
    have h4 : 0 ≤ cubeAmp B F β' p.1 p.2 := norm_nonneg _
    have h6 : (Real.sqrt (γ / 4)) ^ 2 = γ / 4 := Real.sq_sqrt (by positivity)
    have h5 : Real.sqrt (γ / 4) ≤ cubeAmp B F β' p.1 p.2 := by nlinarith [h1, h3, h4, h6]
    exact le_trans (by rw [heta]; exact min_le_right _ _) h5
  -- Step 3: the exchange
  obtain ⟨H₂, hH₂sub, hH₂dens, hH₂lvl⟩ :=
    hInt' B Ns N D f₀ f₁ β' H₁ hN hNs hScaled hNNs hD hDK hsup0 hsup1 hb0 hb1 hSB
      hgammaDpos hetapos heta1 hH₁sub hH₁dens' hlvlC
  -- Step 4: the major-arc pinning
  set delta : ℝ := min 1 (ci * (eta * gammaD * rho) ^ Ki) with hdelta
  have hdeltapos : 0 < delta := by
    rw [hdelta]
    exact lt_min one_pos (by positivity)
  have hdelta1 : delta ≤ 1 := by rw [hdelta]; exact min_le_left _ _
  set Dpow : ℝ := C' * (delta⁻¹) ^ Kp with hDpow
  have hDpowpos : 0 < Dpow := by rw [hDpow]; positivity
  set T0 : ℕ := Nat.ceil Dpow with hT0
  set eps : ℝ := Dpow / (N : ℝ) ^ P.natDegree with heps
  have hT0le : (T0 : ℝ) ≤ Dpow + 1 := by
    rw [hT0]
    have h : ((Nat.ceil Dpow : ℕ) : ℝ) < Dpow + 1 := Nat.ceil_lt_add_one (le_of_lt hDpowpos)
    linarith
  have hepsnn : 0 ≤ eps := by rw [heps]; positivity
  have hpin : ∀ k ∈ H₂, ∃ t : ℕ, 1 ≤ t ∧ t ≤ T0 ∧ distInt ((t : ℝ) * mixedPhase β' k) ≤ eps := by
    intro k hk
    have hkΘ : k ∈ Work.Peluse.Ulower.ThetaSet σ D H₁ := hH₂sub hk
    have hkprod := (Finset.mem_filter.mp hkΘ).1
    have hk2 : ∀ i : Fin σ, k.2.1 i ∈ Finset.Icc (1 : ℤ) (D : ℤ) :=
      Fintype.mem_piFinset.mp (Finset.mem_product.mp (Finset.mem_product.mp hkprod).2).1
    have hk3 : ∀ i : Fin σ, k.2.2 i ∈ Finset.Icc (1 : ℤ) (D : ℤ) :=
      Fintype.mem_piFinset.mp (Finset.mem_product.mp (Finset.mem_product.mp hkprod).2).2
    have hnat2 : ∀ i : Fin σ, (k.2.1 i).natAbs ≤ D := fun i => natAbs_le_of_mem_Icc_one' (hk2 i)
    have hnat3 : ∀ i : Fin σ, (k.2.2 i).natAbs ≤ D := fun i => natAbs_le_of_mem_Icc_one' (hk3 i)
    have hcorr : delta * ((Ns + σ * D : ℕ) : ℝ) ≤
        ‖∑' x : ℤ, Work.Peluse.dualFn N P
            (Work.Peluse.Ulower.iterDelta' σ (fun i => (k.2.1 i, k.2.2 i)) f₀)
            (Work.Peluse.Ulower.iterDelta' σ (fun i => (k.2.1 i, k.2.2 i)) f₁) x *
          Complex.exp (2 * Real.pi * Complex.I * (mixedPhase β' k : ℂ) * (x : ℂ))‖ := by
      have hZeq : (∑' x : ℤ, sliceDual σ N P f₀ f₁
              (fun i => (k.2.1 i, k.2.2 i)) x *
            Complex.exp (2 * Real.pi * Complex.I * (mixedPhase β' k : ℂ) * (x : ℂ))) =
          (∑' x : ℤ, Work.Peluse.dualFn N P
              (Work.Peluse.Ulower.iterDelta' σ (fun i => (k.2.1 i, k.2.2 i)) f₀)
              (Work.Peluse.Ulower.iterDelta' σ (fun i => (k.2.1 i, k.2.2 i)) f₁) x *
            Complex.exp (2 * Real.pi * Complex.I * (mixedPhase β' k : ℂ) * (x : ℂ))) := rfl
      rw [← hZeq]
      have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB1
      have hlvl := hH₂lvl k hk
      have hlvl' : ci * (eta * gammaD * rho) ^ Ki ≤
          (B : ℝ)⁻¹ * ‖∑' x : ℤ, sliceDual σ N P f₀ f₁
              (fun i => (k.2.1 i, k.2.2 i)) x *
            Complex.exp (2 * Real.pi * Complex.I * (mixedPhase β' k : ℂ) * (x : ℂ))‖ := by
        have h := hlvl
        rw [norm_mul, norm_inv, Complex.norm_natCast] at h
        exact h
      have h2 : (B : ℝ) * (ci * (eta * gammaD * rho) ^ Ki) ≤
          ‖∑' x : ℤ, sliceDual σ N P f₀ f₁
              (fun i => (k.2.1 i, k.2.2 i)) x *
            Complex.exp (2 * Real.pi * Complex.I * (mixedPhase β' k : ℂ) * (x : ℂ))‖ := by
        have h := mul_le_mul_of_nonneg_left hlvl' (le_of_lt hBpos)
        have h2' : (B : ℝ) * ((B : ℝ)⁻¹ *
            ‖∑' x : ℤ, sliceDual σ N P f₀ f₁
                (fun i => (k.2.1 i, k.2.2 i)) x *
              Complex.exp (2 * Real.pi * Complex.I * (mixedPhase β' k : ℂ) * (x : ℂ))‖)
            = ‖∑' x : ℤ, sliceDual σ N P f₀ f₁
                (fun i => (k.2.1 i, k.2.2 i)) x *
              Complex.exp (2 * Real.pi * Complex.I * (mixedPhase β' k : ℂ) * (x : ℂ))‖ := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hBpos), one_mul]
        rw [h2'] at h
        exact h
      have h3 : delta ≤ ci * (eta * gammaD * rho) ^ Ki := by rw [hdelta]; exact min_le_right _ _
      have h4 : ((Ns + σ * D : ℕ) : ℝ) ≤ (B : ℝ) := by
        have h : Ns + σ * D ≤ B := by omega
        exact_mod_cast h
      calc delta * ((Ns + σ * D : ℕ) : ℝ)
          ≤ ci * (eta * gammaD * rho) ^ Ki * ((Ns + σ * D : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ ≤ ci * (eta * gammaD * rho) ^ Ki * (B : ℝ) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = (B : ℝ) * (ci * (eta * gammaD * rho) ^ Ki) := by ring
        _ ≤ _ := h2
    obtain ⟨t, ht1, htle, htpin⟩ := hmain (Ns + σ * D) N
      (Work.Peluse.Ulower.iterDelta' σ (fun i => (k.2.1 i, k.2.2 i)) f₀)
      (Work.Peluse.Ulower.iterDelta' σ (fun i => (k.2.1 i, k.2.2 i)) f₁)
      (mixedPhase β' k) delta
      hd (by omega : 1 ≤ Ns + σ * D) hN hdeltapos hdelta1
      (iterDelta'_supportIn_add_I σ _ (fun i => ⟨hnat2 i, hnat3 i⟩) hsup0)
      (iterDelta'_supportIn_add_I σ _ (fun i => ⟨hnat2 i, hnat3 i⟩) hsup1)
      (norm_iterDelta'_le_one' σ _ f₀ hb0)
      (norm_iterDelta'_le_one' σ _ f₁ hb1)
      hcorr
    refine ⟨t, ht1, ?_, ?_⟩
    · rw [hT0]
      have hh : (t : ℝ) ≤ Dpow := by rw [hDpow]; exact htle
      have h2 : (t : ℝ) ≤ ((Nat.ceil Dpow : ℕ) : ℝ) := le_trans hh (Nat.le_ceil Dpow)
      exact_mod_cast h2
    · rw [heps, hDpow]
      exact htpin
  -- Step 5: the pinning
  have hgrM : ∀ k ∈ H₂, ∃ m : ℤ, mixedPhase β' k = (m : ℝ) / (T : ℝ) :=
    fun k _ => mixedPhase_grid hT1 hgrβ k
  have hboundM : ∀ k ∈ H₂, |mixedPhase β' k| ≤ (2 : ℝ) ^ σ :=
    fun k _ => mixedPhase_abs_le (fun u v => abs_le.mpr ⟨by linarith [hβ0 u v], hβ1 u v⟩) k
  obtain ⟨H₂', hH₂'sub, hH₂'dens, v₀, hv₀⟩ :=
    blindConvertK_pin (σ := σ) (D := D) hD (T := T) (T₀ := T0) hT1 (ε := eps) hepsnn β' H₂
      hgrM hpin hboundM
  set Lam : ℝ := ((2 : ℝ) ^ (σ + 1) + 3) *
      (4 * ((T0 + 1) * T0) * (Nat.floor (2 * eps * (T : ℝ)) + 1)) with hLam
  have hT0pos : 1 ≤ T0 := by
    rw [hT0]
    have h := Nat.le_ceil Dpow
    have h2 : (0 : ℝ) < ((Nat.ceil Dpow : ℕ) : ℝ) := lt_of_lt_of_le hDpowpos h
    have h3 : (Nat.ceil Dpow : ℕ) ≠ 0 := by
      intro hh
      rw [hh] at h2
      norm_num at h2
    omega
  have hLampos : 0 < Lam := by
    rw [hLam]
    have h1 : (0 : ℝ) < (2 : ℝ) ^ (σ + 1) + 3 := by positivity
    have h2 : (0 : ℝ) < 4 * (((T0 : ℝ) + 1) * (T0 : ℝ)) *
        (((Nat.floor (2 * eps * (T : ℝ)) : ℝ)) + 1) := by
      have hT0R : (0 : ℝ) < (T0 : ℝ) := by exact_mod_cast (by omega : 0 < T0)
      positivity
    exact mul_pos h1 h2
  have hH₂'dens' : (H₂.card : ℝ) ≤ Lam * (H₂'.card : ℝ) := hH₂'dens
  -- Step 6: the fibre bookkeeping
  obtain ⟨hfr, Pp, hPsub, hPcard, hPpin⟩ :=
    fibrePairs (β := β') (H₁ := H₁) (H₂ := H₂') hD (hH₂'sub.trans hH₂sub)
      (fun k hk => hv₀ k hk)
  -- Step 7: the blind bookkeeping
  have i₀ : Fin σ := ⟨0, hσ⟩
  have hPbox : Pp ⊆ pairBox σ D := hPsub.trans hH₁sub
  have hlvlP : ∀ p ∈ Pp, (γ / 2) / 2 ≤ cubeCorr σ B F β' p.1 p.2 := by
    intro p hp
    have h := hH₁lvl p (hPsub hp)
    linarith
  have hbook := blind_bookkeeping (β := β') (P := Pp) hfr v₀ i₀ (γ := γ / 2) hD hPbox hPpin hlvlP
  -- Step 8: the density chain
  have hAg : (γ / 4) * ci * (eta * gammaD * rho) ^ Ki * gammaD ^ (2 ^ σ) / Lam ≤
      aggr σ D B F (fun u v => ∑ i : Fin σ, blindPhase β' (hfr u) v₀ u v i₀ i) := by
    have hbook' : (γ / 4) * (Pp.card : ℝ) ≤
        (D : ℝ) ^ (2 * σ) * aggr σ D B F
          (fun u v => ∑ i : Fin σ, blindPhase β' (hfr u) v₀ u v i₀ i) := by
      have h := hbook
      rw [hpaircard] at h
      linarith
    have hΘlb : gammaD ^ (2 ^ σ) * (D : ℝ) ^ (3 * σ) ≤
        ((Work.Peluse.Ulower.ThetaSet σ D H₁).card : ℝ) := by
      refine Work.Peluse.Ulower.thetaSet_card_ge hσ hD H₁ (le_of_lt hgammaDpos) ?_ hH₁dens'
      intro p hp i
      obtain ⟨hu, hv⟩ := mem_pairBox (hH₁sub hp)
      exact ⟨by rw [← arithIcc_one_eq']; exact hu i, by rw [← arithIcc_one_eq']; exact hv i⟩
    have hD3 : (D : ℝ) ^ (3 * σ) = (D : ℝ) ^ σ * (D : ℝ) ^ (2 * σ) := by
      rw [show 3 * σ = σ + 2 * σ by ring, pow_add]
    have hA1 : ci * (eta * gammaD * rho) ^ Ki * (gammaD ^ (2 ^ σ) * (D : ℝ) ^ (3 * σ)) ≤
        ci * (eta * gammaD * rho) ^ Ki * ((Work.Peluse.Ulower.ThetaSet σ D H₁).card : ℝ) :=
      mul_le_mul_of_nonneg_left hΘlb (show (0 : ℝ) ≤ ci * (eta * gammaD * rho) ^ Ki by positivity)
    have hA2 : ci * (eta * gammaD * rho) ^ Ki * ((Work.Peluse.Ulower.ThetaSet σ D H₁).card : ℝ) ≤
        (H₂.card : ℝ) := hH₂dens
    have hA34 : (H₂.card : ℝ) ≤ Lam * ((D : ℝ) ^ σ * (Pp.card : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_left hPcard (le_of_lt hLampos)
      linarith [hH₂'dens, h1]
    have htot : ci * (eta * gammaD * rho) ^ Ki * (gammaD ^ (2 ^ σ) * (D : ℝ) ^ (3 * σ)) ≤
        Lam * ((D : ℝ) ^ σ * (Pp.card : ℝ)) := le_trans hA1 (le_trans hA2 hA34)
    rw [hD3] at htot
    have hgoal : ci * (eta * gammaD * rho) ^ Ki * gammaD ^ (2 ^ σ) * (D : ℝ) ^ (2 * σ) ≤
        Lam * (Pp.card : ℝ) := by
      refine (mul_le_mul_iff_of_pos_left hDσpos).mp ?_
      calc (D : ℝ) ^ σ * (ci * (eta * gammaD * rho) ^ Ki * gammaD ^ (2 ^ σ) * (D : ℝ) ^ (2 * σ))
          = ci * (eta * gammaD * rho) ^ Ki *
              (gammaD ^ (2 ^ σ) * ((D : ℝ) ^ σ * (D : ℝ) ^ (2 * σ))) := by ring
        _ ≤ Lam * ((D : ℝ) ^ σ * (Pp.card : ℝ)) := htot
        _ = (D : ℝ) ^ σ * (Lam * (Pp.card : ℝ)) := by ring
    have hγ4nn : (0 : ℝ) ≤ γ / 4 := by linarith
    have hcomb : (γ / 4) * (ci * (eta * gammaD * rho) ^ Ki * gammaD ^ (2 ^ σ) * (D : ℝ) ^ (2 * σ)) ≤
        (γ / 4) * (Lam * (Pp.card : ℝ)) := mul_le_mul_of_nonneg_left hgoal hγ4nn
    have hAg' : (γ / 4) * (ci * (eta * gammaD * rho) ^ Ki * gammaD ^ (2 ^ σ) * (D : ℝ) ^ (2 * σ)) ≤
        (D : ℝ) ^ (2 * σ) * (aggr σ D B F
          (fun u v => ∑ i : Fin σ, blindPhase β' (hfr u) v₀ u v i₀ i)) * Lam := by
      calc (γ / 4) * (ci * (eta * gammaD * rho) ^ Ki * gammaD ^ (2 ^ σ) * (D : ℝ) ^ (2 * σ))
          ≤ (γ / 4) * (Lam * (Pp.card : ℝ)) := hcomb
        _ = Lam * ((γ / 4) * (Pp.card : ℝ)) := by ring
        _ ≤ Lam * ((D : ℝ) ^ (2 * σ) * (aggr σ D B F
              (fun u v => ∑ i : Fin σ, blindPhase β' (hfr u) v₀ u v i₀ i))) :=
            mul_le_mul_of_nonneg_left hbook' (le_of_lt hLampos)
        _ = (D : ℝ) ^ (2 * σ) * (aggr σ D B F
              (fun u v => ∑ i : Fin σ, blindPhase β' (hfr u) v₀ u v i₀ i)) * Lam := by ring
    rw [div_le_iff₀ hLampos]
    refine (mul_le_mul_iff_of_pos_left hD2σpos).mp ?_
    calc (D : ℝ) ^ (2 * σ) * ((γ / 4) * ci * (eta * gammaD * rho) ^ Ki * gammaD ^ (2 ^ σ))
        = (γ / 4) * (ci * (eta * gammaD * rho) ^ Ki * gammaD ^ (2 ^ σ) * (D : ℝ) ^ (2 * σ)) := by ring
      _ ≤ (D : ℝ) ^ (2 * σ) * (aggr σ D B F
            (fun u v => ∑ i : Fin σ, blindPhase β' (hfr u) v₀ u v i₀ i)) * Lam := hAg'
      _ = (D : ℝ) ^ (2 * σ) *
            ((aggr σ D B F (fun u v => ∑ i : Fin σ, blindPhase β' (hfr u) v₀ u v i₀ i)) * Lam) :=
          by ring
  -- Step 9: the pinning-loss bound
  have hSbound : (Work.Peluse.dSup P Ns N : ℝ) + (σ : ℝ) * (D : ℝ) ≤ CS * (Ns : ℝ) := by
    have hdC : (Work.Peluse.dSup P Ns N : ℝ) + 1 ≤ (C : ℝ) * (Ns : ℝ) := by
      exact_mod_cast hScaled.1
    have hd : (Work.Peluse.dSup P Ns N : ℝ) ≤ (C : ℝ) * (Ns : ℝ) := by linarith
    have hsig : (σ : ℝ) * (D : ℝ) ≤ (σ : ℝ) * (K * (Ns : ℝ)) :=
      mul_le_mul_of_nonneg_left hDK hσnn
    rw [hCSdef]
    nlinarith [hd, hsig, hNs1]
  have hBnd : Real.sqrt (γ / 4) * (B : ℝ) ≤
      2 * ((Work.Peluse.dSup P Ns N : ℝ) + (σ : ℝ) * (D : ℝ)) + 1 := by
    obtain ⟨p₀, hp₀⟩ := hH₁ne
    obtain ⟨hu₀, hv₀'⟩ := mem_pairBox (hH₁sub hp₀)
    have hvD : ∀ i : Fin σ, (p₀.2 i).natAbs ≤ D :=
      fun i => natAbs_le_of_mem_arithIcc_one (hv₀' i)
    have hcap := cubeAmp_le_support_I β' p₀.1 p₀.2 hB1 hF1 hFs hvD hSB'
    have hlvl0 : Real.sqrt (γ / 4) ≤ cubeAmp B F β' p₀.1 p₀.2 := by
      have h1 : γ / 4 ≤ cubeCorr σ B F β' p₀.1 p₀.2 := by
        have h := hH₁lvl p₀ hp₀
        linarith
      have h3 : (cubeAmp B F β' p₀.1 p₀.2) ^ 2 = cubeCorr σ B F β' p₀.1 p₀.2 :=
        cubeAmp_sq B F β' p₀.1 p₀.2
      have h4 : 0 ≤ cubeAmp B F β' p₀.1 p₀.2 := norm_nonneg _
      have h6 : (Real.sqrt (γ / 4)) ^ 2 = γ / 4 := Real.sq_sqrt (by positivity)
      nlinarith [h1, h3, h4, h6]
    have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB1
    have h1 : Real.sqrt (γ / 4) ≤
        (((2 * (Work.Peluse.dSup P Ns N + σ * D) + 1 : ℕ)) : ℝ) / (B : ℝ) :=
      le_trans hlvl0 hcap
    rw [le_div_iff₀ hBpos] at h1
    push_cast at h1
    linarith [h1]
  have hTle' : (T : ℝ) ≤ 2 + 4 * Real.pi * (2 * (B : ℝ) + 1) / Real.sqrt γ := by
    have h := hTle
    have h2 : (((2 * B + 1 : ℕ) : ℝ)) = 2 * (B : ℝ) + 1 := by push_cast; ring
    rw [h2] at h
    exact h
  have hNnd : (Ns : ℝ) ≤ (C : ℝ) * (N : ℝ) ^ P.natDegree := hScaled.2
  have hεeq : eps = C' * (delta⁻¹) ^ Kp / (N : ℝ) ^ P.natDegree := by rw [heps, hDpow]
  have hΛineq : Lam ≤ ((2 : ℝ) ^ (σ + 1) + 3) * 4 *
      ((C' * (delta⁻¹) ^ Kp + 2) * (C' * (delta⁻¹) ^ Kp + 1)) *
      ((Nat.floor (2 * eps * (T : ℝ)) : ℝ) + 1) := by
    have hT0b : (T0 : ℝ) ≤ C' * (delta⁻¹) ^ Kp + 1 := by
      have h := hT0le
      rw [hDpow] at h
      exact h
    have hmono : ((T0 : ℝ) + 1) * (T0 : ℝ) ≤
        (C' * (delta⁻¹) ^ Kp + 2) * (C' * (delta⁻¹) ^ Kp + 1) := by
      have hT0nn : (0 : ℝ) ≤ (T0 : ℝ) := Nat.cast_nonneg T0
      nlinarith [hT0b, hT0nn]
    have hYnn : (0 : ℝ) ≤ ((Nat.floor (2 * eps * (T : ℝ)) : ℝ) + 1) := by positivity
    have hAnn : (0 : ℝ) ≤ ((2 : ℝ) ^ (σ + 1) + 3) * 4 := by positivity
    rw [hLam]
    calc ((2 : ℝ) ^ (σ + 1) + 3) * (4 * (((T0 : ℝ) + 1) * (T0 : ℝ)) *
          (((Nat.floor (2 * eps * (T : ℝ)) : ℝ)) + 1))
        = ((2 : ℝ) ^ (σ + 1) + 3) * 4 * (((T0 : ℝ) + 1) * (T0 : ℝ)) *
            (((Nat.floor (2 * eps * (T : ℝ)) : ℝ)) + 1) := by ring
      _ ≤ ((2 : ℝ) ^ (σ + 1) + 3) * 4 *
            ((C' * (delta⁻¹) ^ Kp + 2) * (C' * (delta⁻¹) ^ Kp + 1)) *
            (((Nat.floor (2 * eps * (T : ℝ)) : ℝ)) + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ hYnn
          exact mul_le_mul_of_nonneg_left hmono hAnn
  have hΛbd : delta ^ (3 * Kp) * Lam ≤ CLam / γ := by
    have hAcast : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
    have h := Work.Peluse.UlowerA.pinLossU (σ := σ) (K := Kp) hKp hσ P.natDegree
      (γ := γ) (δ := delta) (B := (B : ℝ)) (S := (Work.Peluse.dSup P Ns N : ℝ))
      (D := (D : ℝ)) (N := (N : ℝ)) (Ns := (Ns : ℝ)) (A := (C : ℝ))
      (T := T) (ε := eps) (Λ := Lam) (C_S := CS) (C' := C')
      hN1 hB1R hγ hγ9 hdeltapos hdelta1 hC'pos hCS1 hNs1 hAcast hNnd hSbound hBnd hTle' hεeq hΛineq
    rw [hCLamdef]
    exact h
  -- Step 10: the final arithmetic
  have hηge : Real.sqrt γ / 6 ≤ eta := by
    rw [heta]
    have h1 : Real.sqrt (γ / 4) = Real.sqrt γ / 2 := by
      rw [Real.sqrt_div (le_of_lt hγ)]
      congr 1
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    refine le_min ?_ ?_
    · have h3 : Real.sqrt γ ≤ 3 := by
        have h := Real.sqrt_le_sqrt hγ9
        rwa [show Real.sqrt (9 : ℝ) = 3 by
          rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
      linarith
    · rw [h1]; linarith [Real.sqrt_nonneg γ]
  have hC09 : C0 ≤ 9 := by
    have hnn : (0 : ℝ) ≤ ((2 * B + 1 : ℕ) : ℝ) / (B : ℝ) := by positivity
    nlinarith [hratio, hnn]
  have hγdge : γ / 36 ≤ gammaD := by
    rw [hgammaD]
    refine div_le_div_of_nonneg_left (le_of_lt hγ) (by positivity : (0 : ℝ) < 4 * C0) ?_
    linarith
  have hγdle : gammaD ≤ 1 := by
    rw [hgammaD, div_le_one (by positivity : (0 : ℝ) < 4 * C0)]
    have h : γ ≤ C0 := le_trans haggr' hCubeBound
    linarith
  -- the lossy final arithmetic
  have heta_le : eta ≤ Real.sqrt γ / 2 := by
    rw [heta]
    calc min 1 (Real.sqrt (γ / 4)) ≤ Real.sqrt (γ / 4) := min_le_right _ _
      _ = Real.sqrt γ / 2 := by
          rw [Real.sqrt_div (le_of_lt hγ)]
          congr 1
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hDN0 : 0 < (D : ℝ) / (Ns : ℝ) := by
    have h1 : (0 : ℝ) < (Ns : ℝ) := by exact_mod_cast hNs
    exact div_pos hDposR h1
  have hBη : (B : ℝ) * eta ≤ (2 * CS + 1) * (Ns : ℝ) := by
    have hsqrt : Real.sqrt (γ / 4) = Real.sqrt γ / 2 := by
      rw [Real.sqrt_div (le_of_lt hγ)]
      congr 1
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hsqrt] at hBnd
    have h2 : 2 * ((Work.Peluse.dSup P Ns N : ℝ) + (σ : ℝ) * (D : ℝ)) + 1
        ≤ (2 * CS + 1) * (Ns : ℝ) := by
      have h2a : 2 * ((Work.Peluse.dSup P Ns N : ℝ) + (σ : ℝ) * (D : ℝ))
          ≤ 2 * (CS * (Ns : ℝ)) := by linarith [hSbound]
      have h2b : (2 * CS + 1) * (Ns : ℝ) = 2 * CS * (Ns : ℝ) + (Ns : ℝ) := by ring
      linarith [h2a, h2b, hNs1]
    have h3 : Real.sqrt γ / 2 * (B : ℝ) ≤ (2 * CS + 1) * (Ns : ℝ) := le_trans hBnd h2
    have h4 : 2 * eta ≤ Real.sqrt γ := by linarith [heta_le]
    have h5 : (B : ℝ) * (2 * eta) ≤ (B : ℝ) * Real.sqrt γ :=
      mul_le_mul_of_nonneg_left h4 (le_of_lt hBposR)
    linarith [h3, h5]
  have hBNs : (B : ℝ) / (Ns : ℝ) ≤ (2 * CS + 1) / eta := by
    have hNsR : (0 : ℝ) < (Ns : ℝ) := by exact_mod_cast hNs
    rw [div_le_div_iff₀ hNsR hetapos]
    exact hBη
  have hDN : (D : ℝ) / (Ns : ℝ) ≤ Kc * rho / eta := by
    have hDNs : (D : ℝ) / (Ns : ℝ) = rho * ((B : ℝ) / (Ns : ℝ)) := by
      rw [hrhodef]; field_simp
    rw [hDNs, hKcdef]
    calc rho * ((B : ℝ) / (Ns : ℝ)) ≤ rho * ((2 * CS + 1) / eta) :=
          mul_le_mul_of_nonneg_left hBNs (le_of_lt hrho0)
      _ = (2 * CS + 1) * rho / eta := by ring
  have harith := arith_lossy_aux (σ := σ) (γ := γ) (η := eta) (γd := gammaD)
    (ρ := rho) (Λ := Lam) (δ := delta)
    (agg := aggr σ D B F (fun u v => ∑ i : Fin σ, blindPhase β' (hfr u) v₀ u v i₀ i))
    (DNs := (D : ℝ) / (Ns : ℝ)) (ci := ci) (CΛ := CLam) (Kc := Kc) (Ki := Ki) (K₂ := Kp)
    hγ hγ9 hcipos hCLam1 hKc1 hηge heta1 hγdge hγdle hrho0 hrho1 hDN0 hdelta hdeltapos
    hLampos hΛbd hDN hAg

  refine ⟨fun i u v => blindPhase β' (hfr u) v₀ u v i₀ i, ?_, ?_⟩
  · intro i u v a b
    exact blindPhase_blind β' (hfr u) v₀ u i₀ i a b v
  · rw [hcfin, hK'def]
    refine le_trans harith ?_
    simp_rw [← Complex.ofReal_sum]
    exact le_refl _

end Work.Peluse.Ulower.StepLe
