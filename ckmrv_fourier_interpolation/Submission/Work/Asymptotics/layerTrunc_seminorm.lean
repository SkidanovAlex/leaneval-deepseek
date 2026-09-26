import Mathlib
import Submission.Work.Asymptotics.TailIntegral
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Asymptotics.abs_pow_mul_exp_le

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open scoped Topology ContDiff

namespace Work.Asymptotics

open Work.Kernels

/-! ## Auxiliary estimates for the assembly -/

/-- `r ↦ |r|^k (2|r|+2)^l e^{-π r²}` is bounded:  Gaussian decay beats polynomial growth. -/
theorem exists_bound_abs_pow_mul_exp_neg_sq (k l : ℕ) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ r : ℝ, |r| ^ k * (2 * |r| + 2) ^ l * Real.exp (-(Real.pi * r ^ 2)) ≤ W := by
  refine ⟨10 ^ (k + l) + (((k + l : ℕ) : ℝ) / (2 * Real.pi * Real.exp 1 * (1 / 8)))
      ^ (((k + l : ℕ) : ℝ) / 2), by positivity, fun r => ?_⟩
  have hexp1 : |r| ^ k * (2 * |r| + 2) ^ l ≤ (2 * |r| + 2) ^ (k + l) := by
    have h1 : |r| ^ k ≤ (2 * |r| + 2) ^ k :=
      pow_le_pow_left₀ (abs_nonneg r) (by linarith [abs_nonneg r]) k
    calc |r| ^ k * (2 * |r| + 2) ^ l ≤ (2 * |r| + 2) ^ k * (2 * |r| + 2) ^ l :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (2 * |r| + 2) ^ (k + l) := by rw [← pow_add]
  have hstep : |r| ^ k * (2 * |r| + 2) ^ l * Real.exp (-(Real.pi * r ^ 2))
      ≤ (2 * |r| + 2) ^ (k + l) * Real.exp (-(Real.pi * r ^ 2)) :=
    mul_le_mul_of_nonneg_right hexp1 (Real.exp_pos _).le
  have hterm1 : (0 : ℝ) ≤ 10 ^ (k + l) := by positivity
  have hterm2 : (0 : ℝ) ≤ (((k + l : ℕ) : ℝ) / (2 * Real.pi * Real.exp 1 * (1 / 8)))
      ^ (((k + l : ℕ) : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
  rcases le_or_gt |r| 4 with hr | hr
  · have hle : (2 * |r| + 2) ^ (k + l) * Real.exp (-(Real.pi * r ^ 2)) ≤ 10 ^ (k + l) := by
      have h1 : (2 * |r| + 2) ^ (k + l) ≤ 10 ^ (k + l) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      have h2 : Real.exp (-(Real.pi * r ^ 2)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg r])
      calc (2 * |r| + 2) ^ (k + l) * Real.exp (-(Real.pi * r ^ 2)) ≤ 10 ^ (k + l) * 1 :=
            mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
        _ = 10 ^ (k + l) := by ring
    exact (hstep.trans hle).trans (le_add_of_nonneg_right hterm2)
  · have hw : (3 : ℝ) ≤ |r| := by linarith
    have hsq : 2 * |r| + 1 ≤ |r| ^ 2 := by nlinarith [hw, sq_nonneg (|r| - 2)]
    have hu2 : (2 * |r| + 2) ^ 2 ≤ 8 * |r| ^ 2 := by nlinarith [hsq]
    have hu : (0 : ℝ) < 2 * |r| + 2 := by positivity
    have hexp2 : Real.exp (-(Real.pi * r ^ 2))
        ≤ Real.exp (-(Real.pi * (2 * |r| + 2) ^ 2 * (1 / 8))) := by
      apply Real.exp_le_exp.mpr
      have h1 : Real.pi * (2 * |r| + 2) ^ 2 * (1 / 8) ≤ Real.pi * r ^ 2 := by
        nlinarith [hu2, Real.pi_pos, sq_abs r]
      linarith
    have hmain : (2 * |r| + 2) ^ (k + l) * Real.exp (-(Real.pi * r ^ 2))
        ≤ (((k + l : ℕ) : ℝ) / (2 * Real.pi * Real.exp 1 * (1 / 8))) ^ (((k + l : ℕ) : ℝ) / 2) := by
      have h := abs_pow_mul_exp_le (k + l) (t := (1 : ℝ) / 8) (by norm_num) (2 * |r| + 2)
      rw [abs_of_pos hu] at h
      calc (2 * |r| + 2) ^ (k + l) * Real.exp (-(Real.pi * r ^ 2))
          ≤ (2 * |r| + 2) ^ (k + l) * Real.exp (-(Real.pi * (2 * |r| + 2) ^ 2 * (1 / 8))) :=
            mul_le_mul_of_nonneg_left hexp2 (by positivity)
        _ ≤ _ := h
    exact (hstep.trans hmain).trans (le_add_of_nonneg_left hterm1)

/-- The `i`-th derivative of `r ↦ r²` is bounded by `(2|r|+2)^i` for `i ≥ 1`. -/
lemma norm_iteratedDeriv_sq_le {i : ℕ} (hi : 1 ≤ i) (r : ℝ) :
    ‖iteratedDeriv i (fun r : ℝ => r ^ 2) r‖ ≤ (2 * |r| + 2) ^ i := by
  rcases i with _ | _ | _ | k
  · omega
  · have h : iteratedDeriv 1 (fun r : ℝ => r ^ 2) r = 2 * r := by
      rw [iteratedDeriv_one]
      simpa using ((hasDerivAt_id r).pow 2).deriv
    rw [h, Real.norm_eq_abs, abs_mul]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2, pow_one]
    linarith [abs_nonneg r]
  · have h : iteratedDeriv 2 (fun r : ℝ => r ^ 2) r = 2 := by
      have h1 : deriv (fun r : ℝ => r ^ 2) = fun r : ℝ => 2 * r := by
        funext y; simpa using ((hasDerivAt_id y).pow 2).deriv
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one, h1]
      simpa using ((hasDerivAt_id r).const_mul (2 : ℝ)).deriv
    rw [h, Real.norm_eq_abs]
    have hD : (2 : ℝ) ≤ 2 * |r| + 2 := by linarith [abs_nonneg r]
    calc |(2 : ℝ)| = 2 := by norm_num
      _ ≤ 2 ^ 2 := by norm_num
      _ ≤ (2 * |r| + 2) ^ 2 := pow_le_pow_left₀ (by norm_num) hD 2
  · have h : iteratedDeriv (k + 3) (fun r : ℝ => r ^ 2) r = 0 := by
      simp only [iteratedDeriv_pow]
      have hz : (2 : ℕ).descFactorial (k + 3) = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [hz]
      norm_num
    rw [h, norm_zero]
    positivity

/-- `‖iteratedFDerivWithin ℝ n f s x‖ = ‖iteratedDeriv n f x‖` for `s` open, `x ∈ s`. -/
lemma norm_iteratedFDerivWithin_eq_of_isOpen {s : Set ℝ} (hs : IsOpen s) {x : ℝ} (hx : x ∈ s)
    (n : ℕ) (f : ℝ → ℂ) :
    ‖iteratedFDerivWithin ℝ n f s x‖ = ‖iteratedDeriv n f x‖ := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  exact norm_iteratedDerivWithin_eq_of_isOpen hs hx n f

/-- If `h` is not a.e. strongly measurable then neither is `h` times the Gaussian factor
`t ↦ e^{-π s² t}` (continuous and nowhere zero). -/
lemma not_aestronglyMeasurable_mul_exp (h : ℝ → ℂ) {s : ℝ}
    (hne : ¬ AEStronglyMeasurable h (volume.restrict (Set.Ici (1 : ℝ)))) :
    ¬ AEStronglyMeasurable
      (fun t : ℝ => h t * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ))))
      (volume.restrict (Set.Ici (1 : ℝ))) := by
  intro hcon
  apply hne
  have hinv : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))
      (volume.restrict (Set.Ici (1 : ℝ))) :=
    (by fun_prop : Continuous fun t : ℝ =>
      Complex.exp (Real.pi * (s : ℂ) ^ 2 * (t : ℂ))).aestronglyMeasurable
  refine (hcon.mul hinv).congr ?_
  filter_upwards with t
  simp only [Pi.mul_apply]
  rw [mul_assoc, ← Complex.exp_add]
  have hz : -(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)) + Real.pi * (s : ℂ) ^ 2 * (t : ℂ) = 0 := by ring
  rw [hz, Complex.exp_zero, mul_one]

/-- `4 sin²(π r²/2) = 2 - 2 cos (π r²)`. -/
lemma sinSq_eq (r : ℝ) : sinSq r = (2 - 2 * Real.cos (Real.pi * r ^ 2) : ℂ) := by
  have hcast : (Real.pi * (r : ℂ) ^ 2 / 2) = ((Real.pi * r ^ 2 / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have hcos : Complex.cos ((Real.pi * r ^ 2 / 2 : ℝ) : ℂ) ^ 2
      = (1 / 2 : ℂ) + Complex.cos ((Real.pi * r ^ 2 : ℝ) : ℂ) / 2 := by
    rw [Complex.cos_sq]
    congr 1
    push_cast
    ring_nf
  have hmain : 4 * Complex.sin (((Real.pi * r ^ 2 / 2 : ℝ) : ℂ)) ^ 2
      = 2 - 2 * Complex.cos ((Real.pi * r ^ 2 : ℝ) : ℂ) := by
    rw [Complex.sin_sq, hcos]
    ring_nf
  rw [sinSq, hcast, hmain, ← Complex.ofReal_cos]

/-- **The `trunc` piece as a tail integral**:  with `λ = r²`, the exponentials and the
regularising factor `4 sin²(π r²/2) = 2 - 2 cos (π r²)` show that `layerTrunc` is the product of
the smooth function `λ ↦ 2 - 2cos (πλ)` with the tail integral of the amplitude. -/
lemma layerTrunc_eq_tailIntegral (G : Fin 2 → Fin 2 → ℍ → ℂ) (ℓ : LogLambdaData) (d : ℕ)
    (τ : ℍ) (r : ℝ) :
    layerTrunc G ℓ d τ r
      = (2 - 2 * Real.cos (Real.pi * r ^ 2) : ℂ)
        * tailIntegral (fun t : ℝ => Kaxis (Kfun ℓ d) τ t - Aexp G τ t) (r ^ 2) := by
  rw [layerTrunc, tailIntegral, sinSq_eq]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hexp : Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
      = ((Real.exp (-(Real.pi * r ^ 2 * t))) : ℂ) := by
    rw [show -(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)) = ((-(Real.pi * r ^ 2 * t) : ℝ) : ℂ) from by
      push_cast; ring, ← Complex.ofReal_exp]
  simp only [hexp]

/-! ## The target theorem -/

/-- The `r`-seminorms of the `trunc` part `layerTrunc` of the CKMRV layer are bounded, with
moderate growth in `τ` on `𝒟`; the only input is the exponential decay of the tail
`Kaxis - Aexp` for `t ≥ 1`, assumed almost everywhere in `t` (it can fail at the at most two
points where the contour meets the pole divisor `j(τ) = j(it)`, where Lean's `Kaxis` takes the junk
value `0`; see `Work.Asymptotics.Kaxis_cusp_expansion`). -/
theorem layerTrunc_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (htail : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ τ : UpperHalfPlane,
      τ ∈ Work.Asymptotics.DomainD →
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))),
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t‖
          ≤ C * (Work.Kernels.scale τ) ^ N * t ^ M * Real.exp (-(Real.pi * t))) :
    ∀ k l : ℕ, ∃ c N : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      τ ∈ Work.Asymptotics.DomainD →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerTrunc G ℓ d τ s) r‖
        ≤ c * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨C, N, M, hC, hN, hM, htail'⟩ := htail
  have _hd := hd
  have _hN := hN
  intro k l
  obtain ⟨W, hW0, hW⟩ := exists_bound_abs_pow_mul_exp_neg_sq k l
  refine ⟨(l.factorial : ℝ) * ((l + 1 : ℕ) : ℝ)
      * (4 * C * (2 * Real.pi) ^ l * tailDecay M l) * W, N, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ tailDecay M l := tailDecay_nonneg M l
    have h2 : (0 : ℝ) ≤ 4 * C * (2 * Real.pi) ^ l * tailDecay M l := by positivity
    positivity
  · intro τ r hτ
    set S : ℝ := scale τ with hSdef
    have hSpos : 0 < S := scale_pos τ
    set h : ℝ → ℂ := fun t => Kaxis (Kfun ℓ d) τ t - Aexp G τ t with hhdef
    have htailτ : ∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))),
        ‖h t‖ ≤ (C * S ^ N) * t ^ M * Real.exp (-(Real.pi * t)) := by
      filter_upwards [htail' τ hτ] with t ht
      simpa only [h, hSdef] using ht
    have hCN : 0 ≤ C * S ^ N := mul_nonneg hC.le (Real.rpow_nonneg hSpos.le N)
    by_cases hmeas : AEStronglyMeasurable h (volume.restrict (Set.Ici (1 : ℝ)))
    · -- Case A: `h` is a.e. strongly measurable, so the tail integral is smooth
      have hcont : ContDiffOn ℝ (l : ℕ∞ω) (tailIntegral h) (Set.Ioi (-1)) :=
        tailIntegral_contDiffOn l h hmeas hCN hM htailτ
      have hcont_cos : ContDiffOn ℝ (l : ℕ∞ω)
          (fun x : ℝ => (2 - 2 * Real.cos (Real.pi * x) : ℂ)) (Set.Ioi (-1)) := by
        have h1 : ContDiff ℝ (l : ℕ∞ω) (fun x : ℝ => (2 - 2 * Real.cos (Real.pi * x))) := by
          fun_prop
        have h2 := Complex.ofRealCLM.contDiff.comp h1
        refine h2.contDiffOn.congr (fun x _ => ?_)
        show (2 - 2 * (Real.cos (Real.pi * x) : ℂ)) = ((2 - 2 * Real.cos (Real.pi * x) : ℝ) : ℂ)
        push_cast
        ring
      have hfcont : ContDiffOn ℝ (l : ℕ∞ω) (fun r : ℝ => r ^ 2) Set.univ :=
        ((contDiff_id (𝕜 := ℝ)).pow 2).contDiffOn
      -- the product bound for the iterated derivatives of `λ ↦ (2 - 2cos (πλ)) * Ψ λ`
      have hbnd : ∀ i ≤ l, ∀ x : ℝ, 0 ≤ x →
          ‖iteratedDeriv i
              (fun x : ℝ => (2 - 2 * Real.cos (Real.pi * x) : ℂ) * tailIntegral h x) x‖
            ≤ S ^ N * Real.exp (-(Real.pi * x)) * (4 * C * (2 * Real.pi) ^ l * tailDecay M l) := by
        intro i hi x hx
        have hxmem : x ∈ Set.Ioi (-1) := by rw [Set.mem_Ioi]; linarith
        have hmul := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (s := Set.Ioi (-1))
          (f := fun x : ℝ => (2 - 2 * Real.cos (Real.pi * x) : ℂ))
          (g := tailIntegral h) (N := (l : ℕ∞ω)) hcont_cos hcont (uniqueDiffOn_Ioi (-1)) hxmem
          (show (i : ℕ∞ω) ≤ (l : ℕ∞ω) from by exact_mod_cast hi)
        have hL : ‖iteratedFDerivWithin ℝ i
              (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * tailIntegral h y)
              (Set.Ioi (-1)) x‖
            = ‖iteratedDeriv i
              (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * tailIntegral h y) x‖ :=
          norm_iteratedFDerivWithin_eq_of_isOpen isOpen_Ioi hxmem i _
        rw [hL] at hmul
        have hstep : ∀ j ∈ Finset.range (i + 1),
            (i.choose j : ℝ) *
              ‖iteratedFDerivWithin ℝ j (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ))
                (Set.Ioi (-1)) x‖ *
              ‖iteratedFDerivWithin ℝ (i - j) (tailIntegral h) (Set.Ioi (-1)) x‖
            ≤ (i.choose j : ℝ) * (4 * Real.pi ^ j) *
              ((C * S ^ N) * Real.pi ^ (i - j) * tailDecay M (i - j)
                * Real.exp (-(Real.pi * x))) := by
          intro j hj
          have hc : ‖iteratedFDerivWithin ℝ j
                (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ)) (Set.Ioi (-1)) x‖
              ≤ 4 * Real.pi ^ j := by
            rw [norm_iteratedFDerivWithin_eq_of_isOpen isOpen_Ioi hxmem j]
            exact norm_iteratedDeriv_two_sub_two_cos j x
          have ht : ‖iteratedFDerivWithin ℝ (i - j) (tailIntegral h) (Set.Ioi (-1)) x‖
              ≤ (C * S ^ N) * Real.pi ^ (i - j) * tailDecay M (i - j)
                * Real.exp (-(Real.pi * x)) := by
            rw [norm_iteratedFDerivWithin_eq_of_isOpen isOpen_Ioi hxmem (i - j)]
            exact tailIntegral_iteratedDeriv_bound h hmeas hCN hM htailτ (i - j) hx
          have h0 : (0 : ℝ) ≤ (i.choose j : ℝ) * (4 * Real.pi ^ j) := by positivity
          have hq : (0 : ℝ) ≤ (C * S ^ N) * Real.pi ^ (i - j) * tailDecay M (i - j)
              * Real.exp (-(Real.pi * x)) := by
            have := tailDecay_nonneg M (i - j); positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left hc (by positivity)) ht (by positivity) h0
        have hsum1 : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (4 * Real.pi ^ j) *
              ((C * S ^ N) * Real.pi ^ (i - j) * tailDecay M (i - j)
                * Real.exp (-(Real.pi * x))))
            = 4 * (C * S ^ N) * Real.pi ^ i * Real.exp (-(Real.pi * x)) *
              (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * tailDecay M (i - j)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          have : Real.pi ^ j * Real.pi ^ (i - j) = Real.pi ^ i := by
            rw [← pow_add]
            congr 1
            exact Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
          rw [← this]
          ring
        have hsum2 : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * tailDecay M (i - j))
            ≤ 2 ^ i * tailDecay M l := by
          calc (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * tailDecay M (i - j))
              ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * tailDecay M l := by
                refine Finset.sum_le_sum (fun j hj => ?_)
                exact mul_le_mul_of_nonneg_left
                  (tailDecay_mono hM (le_trans (Nat.sub_le i j) hi)) (by positivity)
            _ = (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) * tailDecay M l := by
                rw [Finset.sum_mul]
            _ = 2 ^ i * tailDecay M l := by
                congr 1
                have hh := add_pow (1 : ℝ) 1 i
                rw [one_add_one_eq_two] at hh
                rw [hh]
                apply Finset.sum_congr rfl
                intro j hj
                rw [one_pow, one_pow]
                ring
        have hfinal : 4 * (C * S ^ N) * Real.pi ^ i * Real.exp (-(Real.pi * x)) *
              (2 ^ i * tailDecay M l)
            ≤ S ^ N * Real.exp (-(Real.pi * x)) * (4 * C * (2 * Real.pi) ^ l * tailDecay M l) := by
          have hK : (0 : ℝ) ≤ tailDecay M l := tailDecay_nonneg M l
          have hpi : Real.pi ^ i * 2 ^ i ≤ (2 * Real.pi) ^ l := by
            have e : Real.pi ^ i * 2 ^ i = (2 * Real.pi) ^ i := by rw [mul_pow, mul_comm]
            rw [e]
            exact pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) hi
          have hkey : 4 * (C * S ^ N) * Real.pi ^ i * Real.exp (-(Real.pi * x)) * 2 ^ i
              ≤ S ^ N * Real.exp (-(Real.pi * x)) * (4 * C * (2 * Real.pi) ^ l) := by
            have e1 : 4 * (C * S ^ N) * Real.pi ^ i * Real.exp (-(Real.pi * x)) * 2 ^ i
                = 4 * C * S ^ N * Real.exp (-(Real.pi * x)) * (Real.pi ^ i * 2 ^ i) := by ring
            have e2 : S ^ N * Real.exp (-(Real.pi * x)) * (4 * C * (2 * Real.pi) ^ l)
                = 4 * C * S ^ N * Real.exp (-(Real.pi * x)) * (2 * Real.pi) ^ l := by ring
            rw [e1, e2]
            exact mul_le_mul_of_nonneg_left hpi (by positivity)
          calc 4 * (C * S ^ N) * Real.pi ^ i * Real.exp (-(Real.pi * x)) * (2 ^ i * tailDecay M l)
              = (4 * (C * S ^ N) * Real.pi ^ i * Real.exp (-(Real.pi * x)) * 2 ^ i) * tailDecay M l := by
                ring
            _ ≤ (S ^ N * Real.exp (-(Real.pi * x)) * (4 * C * (2 * Real.pi) ^ l)) * tailDecay M l :=
                mul_le_mul_of_nonneg_right hkey hK
            _ = S ^ N * Real.exp (-(Real.pi * x)) * (4 * C * (2 * Real.pi) ^ l * tailDecay M l) := by
                ring
        calc ‖iteratedDeriv i
              (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * tailIntegral h y) x‖
            ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
                ‖iteratedFDerivWithin ℝ j (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ))
                  (Set.Ioi (-1)) x‖ *
                ‖iteratedFDerivWithin ℝ (i - j) (tailIntegral h) (Set.Ioi (-1)) x‖ := hmul
          _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (4 * Real.pi ^ j) *
                ((C * S ^ N) * Real.pi ^ (i - j) * tailDecay M (i - j)
                  * Real.exp (-(Real.pi * x))) := Finset.sum_le_sum hstep
          _ = 4 * (C * S ^ N) * Real.pi ^ i * Real.exp (-(Real.pi * x)) *
                (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * tailDecay M (i - j)) := hsum1
          _ ≤ 4 * (C * S ^ N) * Real.pi ^ i * Real.exp (-(Real.pi * x)) *
                (2 ^ i * tailDecay M l) := by
              have hpos : (0 : ℝ) ≤ 4 * (C * S ^ N) * Real.pi ^ i * Real.exp (-(Real.pi * x)) := by
                have := tailDecay_nonneg M i; positivity
              exact mul_le_mul_of_nonneg_left hsum2 hpos
          _ ≤ S ^ N * Real.exp (-(Real.pi * x)) * (4 * C * (2 * Real.pi) ^ l * tailDecay M l) := hfinal
      -- the composition with `r ↦ r²`
      have hCbound : ∀ i, i ≤ l → ‖iteratedFDerivWithin ℝ i
            (fun x : ℝ => (2 - 2 * Real.cos (Real.pi * x) : ℂ) * tailIntegral h x)
            (Set.Ioi (-1)) (r ^ 2)‖
          ≤ S ^ N * Real.exp (-(Real.pi * r ^ 2))
            * (((l + 1 : ℕ) : ℝ) * (4 * C * (2 * Real.pi) ^ l * tailDecay M l)) := by
        intro i hi
        have hr2 : r ^ 2 ∈ Set.Ioi (-1) := by rw [Set.mem_Ioi]; nlinarith [sq_nonneg r]
        rw [norm_iteratedFDerivWithin_eq_of_isOpen isOpen_Ioi hr2]
        have h1 := hbnd i hi (r ^ 2) (sq_nonneg r)
        have h3 : (1 : ℝ) ≤ ((l + 1 : ℕ) : ℝ) := by
          have : (1 : ℕ) ≤ l + 1 := Nat.le_add_left 1 l
          exact_mod_cast this
        have h4 : (0 : ℝ) ≤ S ^ N * Real.exp (-(Real.pi * r ^ 2)) := by
          have h5 := Real.rpow_nonneg hSpos.le N
          positivity
        have h5 : (0 : ℝ) ≤ 4 * C * (2 * Real.pi) ^ l * tailDecay M l := by
          have h6 := tailDecay_nonneg M l
          positivity
        have h6 : S ^ N * Real.exp (-(Real.pi * r ^ 2)) * (4 * C * (2 * Real.pi) ^ l * tailDecay M l)
            ≤ S ^ N * Real.exp (-(Real.pi * r ^ 2))
              * (((l + 1 : ℕ) : ℝ) * (4 * C * (2 * Real.pi) ^ l * tailDecay M l)) := by
          refine mul_le_mul_of_nonneg_left ?_ h4
          calc 4 * C * (2 * Real.pi) ^ l * tailDecay M l
              = 1 * (4 * C * (2 * Real.pi) ^ l * tailDecay M l) := by ring
            _ ≤ ((l + 1 : ℕ) : ℝ) * (4 * C * (2 * Real.pi) ^ l * tailDecay M l) :=
                mul_le_mul_of_nonneg_right h3 h5
        linarith [h1, h6]
      have hDbound : ∀ i, 1 ≤ i → i ≤ l →
          ‖iteratedFDerivWithin ℝ i (fun r : ℝ => r ^ 2) Set.univ r‖ ≤ (2 * |r| + 2) ^ i := by
        intro i hi _
        rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        exact norm_iteratedDeriv_sq_le hi r
      have hcomp := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ)
        (g := fun x : ℝ => (2 - 2 * Real.cos (Real.pi * x) : ℂ) * tailIntegral h x)
        (f := fun r : ℝ => r ^ 2) (n := l) (s := Set.univ) (t := Set.Ioi (-1))
        (x := r) (N := (l : ℕ∞ω)) (hcont_cos.mul hcont) hfcont le_rfl
        (uniqueDiffOn_Ioi (-1)) uniqueDiffOn_univ
        (by intro x _; rw [Set.mem_Ioi]; nlinarith [sq_nonneg x]) (Set.mem_univ r) hCbound hDbound
      have hcomp' : ‖iteratedDeriv l
            (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ) * tailIntegral h (s ^ 2)) r‖
          ≤ (l.factorial : ℝ) * (S ^ N * Real.exp (-(Real.pi * r ^ 2))
              * (((l + 1 : ℕ) : ℝ) * (4 * C * (2 * Real.pi) ^ l * tailDecay M l)))
            * (2 * |r| + 2) ^ l := by
        have heq : (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ) * tailIntegral h (s ^ 2))
            = (fun x : ℝ => (2 - 2 * Real.cos (Real.pi * x) : ℂ) * tailIntegral h x)
              ∘ (fun r : ℝ => r ^ 2) := rfl
        rw [heq, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← iteratedFDerivWithin_univ]
        exact hcomp
      -- transfer to `layerTrunc`
      have hlayerfun : (fun s : ℝ => layerTrunc G ℓ d τ s)
          = fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ) * tailIntegral h (s ^ 2) := by
        funext s
        rw [layerTrunc_eq_tailIntegral]
      rw [hlayerfun]
      calc (|r| ^ k) * ‖iteratedDeriv l
            (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ) * tailIntegral h (s ^ 2)) r‖
          ≤ |r| ^ k * ((l.factorial : ℝ) * (S ^ N * Real.exp (-(Real.pi * r ^ 2))
              * (((l + 1 : ℕ) : ℝ) * (4 * C * (2 * Real.pi) ^ l * tailDecay M l)))
                * (2 * |r| + 2) ^ l) := mul_le_mul_of_nonneg_left hcomp' (by positivity)
        _ = (l.factorial : ℝ) * ((l + 1 : ℕ) : ℝ) * (4 * C * (2 * Real.pi) ^ l * tailDecay M l)
              * S ^ N * (|r| ^ k * (2 * |r| + 2) ^ l * Real.exp (-(Real.pi * r ^ 2))) := by
            ring
        _ ≤ (l.factorial : ℝ) * ((l + 1 : ℕ) : ℝ) * (4 * C * (2 * Real.pi) ^ l * tailDecay M l)
              * S ^ N * W := by
            have h1 : (0 : ℝ) ≤ (l.factorial : ℝ) * ((l + 1 : ℕ) : ℝ)
                * (4 * C * (2 * Real.pi) ^ l * tailDecay M l) * S ^ N := by
              have := tailDecay_nonneg M l; positivity
            exact mul_le_mul_of_nonneg_left (hW r) h1
        _ = ((l.factorial : ℝ) * ((l + 1 : ℕ) : ℝ)
              * (4 * C * (2 * Real.pi) ^ l * tailDecay M l) * W) * S ^ N := by ring
        _ = ((l.factorial : ℝ) * ((l + 1 : ℕ) : ℝ)
              * (4 * C * (2 * Real.pi) ^ l * tailDecay M l) * W) * (scale τ) ^ N := by rw [hSdef]
    · -- Case B: `h` is not a.e. strongly measurable, so every integral vanishes
      have hzero : ∀ s : ℝ, layerTrunc G ℓ d τ s = 0 := by
        intro s
        have hne : ¬ AEStronglyMeasurable
            (fun t : ℝ => h t * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ))))
            (volume.restrict (Set.Ici (1 : ℝ))) := not_aestronglyMeasurable_mul_exp (s := s) h hmeas
        have hint : ¬ Integrable (fun t : ℝ =>
            h t * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ))))
            (volume.restrict (Set.Ici (1 : ℝ))) := fun hi => hne hi.aestronglyMeasurable
        rw [layerTrunc]
        rw [show (∫ t in Set.Ici (1 : ℝ),
            (Kaxis (Kfun ℓ d) τ t - Aexp G τ t) * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ))))
            = 0 from integral_undef hint]
        ring
      have hlayerfun : (fun s : ℝ => layerTrunc G ℓ d τ s) = fun _ : ℝ => (0 : ℂ) := funext hzero
      rw [hlayerfun, iteratedDeriv_fun_const_zero, norm_zero, mul_zero]
      have h1 : (0 : ℝ) ≤ tailDecay M l := tailDecay_nonneg M l
      have h2 : (0 : ℝ) ≤ (scale τ) ^ N := Real.rpow_nonneg (scale_pos τ).le N
      positivity

end Work.Asymptotics
