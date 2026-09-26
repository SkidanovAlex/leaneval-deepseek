import Mathlib
import Submission.Work.Asymptotics.layerTrunc_seminorm
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.TailIntegral
import Submission.Work.Kernels.Kernels

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open scoped Topology ContDiff

namespace Work.Asymptotics

open Work.Kernels

/-- **The `r`-seminorm bound for the `trunc` piece of the CKMRV layer on a compact `K ⊆ 𝒟`.**

Adaptation of `Work.Asymptotics.layerTrunc_seminorm`
(`Submission/Work/Asymptotics/layerTrunc_seminorm.lean`) to a compact set: the tail hypothesis is
the *pointwise* bound `‖Kaxis (Kfun ℓ d) τ t - Aexp G τ t‖ ≤ C (1+t)^M e^{-π(t-T₀)}` for `τ ∈ K`,
`t ≥ 1` (the `τ ∈ 𝒟`-uniform two-regime `TailBound` of the paper is not available), and the
conclusion carries a single constant.

Strategy: copy the proof of `Work.Asymptotics.layerTrunc_seminorm`.  For `t ≥ 1` and `M ≥ 0`,
`1 + t ≤ 2 t` gives `(1+t)^M ≤ 2^M t^M` and `e^{-π(t-T₀)} = e^{πT₀} e^{-πt}`, so `hpolyK` supplies
the a.e. bound `‖h t‖ ≤ (C * e^{πT₀} * 2^M) * t^M * e^{-πt}` on `Set.Ici 1` needed by
`Work.Asymptotics.tailIntegral_iteratedDeriv_bound` (with the `(scale τ)^N` factor equal to `1`,
`N = 0`).  The case split on `AEStronglyMeasurable h` is inherited verbatim (in the negative case
every integral is `0` and the bound is trivial); `hd` is not actually used, as in the global
statement. -/
theorem layerTrunc_local_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) {K : Set UpperHalfPlane}
    (hpolyK : ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ K → 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t‖
          ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀)))) :
    ∀ k l : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ K →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerTrunc G ℓ d τ s) r‖ ≤ c := by
  obtain ⟨C, M, T₀, hC, hM, hT₀, hpoly⟩ := hpolyK
  have _hd := hd
  intro k l
  obtain ⟨W, hW0, hW⟩ := exists_bound_abs_pow_mul_exp_neg_sq k l
  set C' : ℝ := C * Real.exp (Real.pi * T₀) * 2 ^ M with hC'def
  have hC'0 : 0 ≤ C' := by rw [hC'def]; positivity
  refine ⟨(l.factorial : ℝ) * ((l + 1 : ℕ) : ℝ)
      * (4 * C' * (2 * Real.pi) ^ l * tailDecay M l) * W, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ tailDecay M l := tailDecay_nonneg M l
    have h2 : (0 : ℝ) ≤ 4 * C' * (2 * Real.pi) ^ l * tailDecay M l := by positivity
    positivity
  · intro τ r hτ
    set h : ℝ → ℂ := fun t => Kaxis (Kfun ℓ d) τ t - Aexp G τ t with hhdef
    have htailτ : ∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))),
        ‖h t‖ ≤ C' * t ^ M * Real.exp (-(Real.pi * t)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      have ht1 : 1 ≤ t := Set.mem_Ici.mp ht
      have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht1
      have hb := hpoly τ t hτ ht1
      have hpowle : (1 + t) ^ M ≤ 2 ^ M * t ^ M := by
        have h1 : (1 + t) ^ M ≤ (2 * t) ^ M :=
          Real.rpow_le_rpow (by linarith) (by linarith) hM
        rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht0] at h1
      have hexp : Real.exp (-(Real.pi * (t - T₀)))
          = Real.exp (Real.pi * T₀) * Real.exp (-(Real.pi * t)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp] at hb
      calc ‖h t‖
            ≤ C * (1 + t) ^ M * (Real.exp (Real.pi * T₀) * Real.exp (-(Real.pi * t))) := hb
        _ ≤ C * (2 ^ M * t ^ M) * (Real.exp (Real.pi * T₀) * Real.exp (-(Real.pi * t))) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpowle hC.le) (by positivity)
        _ = C' * t ^ M * Real.exp (-(Real.pi * t)) := by rw [hC'def]; ring
    by_cases hmeas : AEStronglyMeasurable h (volume.restrict (Set.Ici (1 : ℝ)))
    · -- Case A: `h` is a.e. strongly measurable, so the tail integral is smooth
      have hcont : ContDiffOn ℝ (l : ℕ∞ω) (tailIntegral h) (Set.Ioi (-1)) :=
        tailIntegral_contDiffOn l h hmeas hC'0 hM htailτ
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
      have hbnd : ∀ i ≤ l, ∀ x : ℝ, 0 ≤ x →
          ‖iteratedDeriv i
              (fun x : ℝ => (2 - 2 * Real.cos (Real.pi * x) : ℂ) * tailIntegral h x) x‖
            ≤ Real.exp (-(Real.pi * x)) * (4 * C' * (2 * Real.pi) ^ l * tailDecay M l) := by
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
              (C' * Real.pi ^ (i - j) * tailDecay M (i - j)
                * Real.exp (-(Real.pi * x))) := by
          intro j hj
          have hc : ‖iteratedFDerivWithin ℝ j
                (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ)) (Set.Ioi (-1)) x‖
              ≤ 4 * Real.pi ^ j := by
            rw [norm_iteratedFDerivWithin_eq_of_isOpen isOpen_Ioi hxmem j]
            exact norm_iteratedDeriv_two_sub_two_cos j x
          have ht : ‖iteratedFDerivWithin ℝ (i - j) (tailIntegral h) (Set.Ioi (-1)) x‖
              ≤ C' * Real.pi ^ (i - j) * tailDecay M (i - j)
                * Real.exp (-(Real.pi * x)) := by
            rw [norm_iteratedFDerivWithin_eq_of_isOpen isOpen_Ioi hxmem (i - j)]
            exact tailIntegral_iteratedDeriv_bound h hmeas hC'0 hM htailτ (i - j) hx
          have h0 : (0 : ℝ) ≤ (i.choose j : ℝ) * (4 * Real.pi ^ j) := by positivity
          have hq : (0 : ℝ) ≤ C' * Real.pi ^ (i - j) * tailDecay M (i - j)
              * Real.exp (-(Real.pi * x)) := by
            have := tailDecay_nonneg M (i - j); positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left hc (by positivity)) ht (by positivity) h0
        have hsum1 : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (4 * Real.pi ^ j) *
              (C' * Real.pi ^ (i - j) * tailDecay M (i - j)
                * Real.exp (-(Real.pi * x))))
            = 4 * C' * Real.pi ^ i * Real.exp (-(Real.pi * x)) *
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
        have hfinal : 4 * C' * Real.pi ^ i * Real.exp (-(Real.pi * x)) *
              (2 ^ i * tailDecay M l)
            ≤ Real.exp (-(Real.pi * x)) * (4 * C' * (2 * Real.pi) ^ l * tailDecay M l) := by
          have hK : (0 : ℝ) ≤ tailDecay M l := tailDecay_nonneg M l
          have hpi : Real.pi ^ i * 2 ^ i ≤ (2 * Real.pi) ^ l := by
            have e : Real.pi ^ i * 2 ^ i = (2 * Real.pi) ^ i := by rw [mul_pow, mul_comm]
            rw [e]
            exact pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) hi
          have hkey : 4 * C' * Real.pi ^ i * Real.exp (-(Real.pi * x)) * 2 ^ i
              ≤ Real.exp (-(Real.pi * x)) * (4 * C' * (2 * Real.pi) ^ l) := by
            have e1 : 4 * C' * Real.pi ^ i * Real.exp (-(Real.pi * x)) * 2 ^ i
                = 4 * C' * Real.exp (-(Real.pi * x)) * (Real.pi ^ i * 2 ^ i) := by ring
            have e2 : Real.exp (-(Real.pi * x)) * (4 * C' * (2 * Real.pi) ^ l)
                = 4 * C' * Real.exp (-(Real.pi * x)) * (2 * Real.pi) ^ l := by ring
            rw [e1, e2]
            exact mul_le_mul_of_nonneg_left hpi (by positivity)
          calc 4 * C' * Real.pi ^ i * Real.exp (-(Real.pi * x)) * (2 ^ i * tailDecay M l)
              = (4 * C' * Real.pi ^ i * Real.exp (-(Real.pi * x)) * 2 ^ i) * tailDecay M l := by
                ring
            _ ≤ (Real.exp (-(Real.pi * x)) * (4 * C' * (2 * Real.pi) ^ l)) * tailDecay M l :=
                mul_le_mul_of_nonneg_right hkey hK
            _ = Real.exp (-(Real.pi * x)) * (4 * C' * (2 * Real.pi) ^ l * tailDecay M l) := by
                ring
        calc ‖iteratedDeriv i
              (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * tailIntegral h y) x‖
            ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
                ‖iteratedFDerivWithin ℝ j (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ))
                  (Set.Ioi (-1)) x‖ *
                ‖iteratedFDerivWithin ℝ (i - j) (tailIntegral h) (Set.Ioi (-1)) x‖ := hmul
          _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (4 * Real.pi ^ j) *
                (C' * Real.pi ^ (i - j) * tailDecay M (i - j)
                  * Real.exp (-(Real.pi * x))) := Finset.sum_le_sum hstep
          _ = 4 * C' * Real.pi ^ i * Real.exp (-(Real.pi * x)) *
                (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * tailDecay M (i - j)) := hsum1
          _ ≤ 4 * C' * Real.pi ^ i * Real.exp (-(Real.pi * x)) *
                (2 ^ i * tailDecay M l) := by
              have hpos : (0 : ℝ) ≤ 4 * C' * Real.pi ^ i * Real.exp (-(Real.pi * x)) := by
                have := tailDecay_nonneg M i; positivity
              exact mul_le_mul_of_nonneg_left hsum2 hpos
          _ ≤ Real.exp (-(Real.pi * x)) * (4 * C' * (2 * Real.pi) ^ l * tailDecay M l) := hfinal
      have hCbound : ∀ i, i ≤ l → ‖iteratedFDerivWithin ℝ i
            (fun x : ℝ => (2 - 2 * Real.cos (Real.pi * x) : ℂ) * tailIntegral h x)
            (Set.Ioi (-1)) (r ^ 2)‖
          ≤ Real.exp (-(Real.pi * r ^ 2))
            * (((l + 1 : ℕ) : ℝ) * (4 * C' * (2 * Real.pi) ^ l * tailDecay M l)) := by
        intro i hi
        have hr2 : r ^ 2 ∈ Set.Ioi (-1) := by rw [Set.mem_Ioi]; nlinarith [sq_nonneg r]
        rw [norm_iteratedFDerivWithin_eq_of_isOpen isOpen_Ioi hr2]
        have h1 := hbnd i hi (r ^ 2) (sq_nonneg r)
        have h3 : (1 : ℝ) ≤ ((l + 1 : ℕ) : ℝ) := by
          have : (1 : ℕ) ≤ l + 1 := Nat.le_add_left 1 l
          exact_mod_cast this
        have h4 : (0 : ℝ) ≤ Real.exp (-(Real.pi * r ^ 2)) := (Real.exp_pos _).le
        have h5 : (0 : ℝ) ≤ 4 * C' * (2 * Real.pi) ^ l * tailDecay M l := by
          have h6 := tailDecay_nonneg M l
          positivity
        have h7 : Real.exp (-(Real.pi * r ^ 2)) * (4 * C' * (2 * Real.pi) ^ l * tailDecay M l)
            ≤ Real.exp (-(Real.pi * r ^ 2))
              * (((l + 1 : ℕ) : ℝ) * (4 * C' * (2 * Real.pi) ^ l * tailDecay M l)) := by
          refine mul_le_mul_of_nonneg_left ?_ h4
          calc 4 * C' * (2 * Real.pi) ^ l * tailDecay M l
              = 1 * (4 * C' * (2 * Real.pi) ^ l * tailDecay M l) := by ring
            _ ≤ ((l + 1 : ℕ) : ℝ) * (4 * C' * (2 * Real.pi) ^ l * tailDecay M l) :=
                mul_le_mul_of_nonneg_right h3 h5
        linarith [h1, h7]
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
          ≤ (l.factorial : ℝ) * (Real.exp (-(Real.pi * r ^ 2))
              * (((l + 1 : ℕ) : ℝ) * (4 * C' * (2 * Real.pi) ^ l * tailDecay M l)))
            * (2 * |r| + 2) ^ l := by
        have heq : (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ) * tailIntegral h (s ^ 2))
            = (fun x : ℝ => (2 - 2 * Real.cos (Real.pi * x) : ℂ) * tailIntegral h x)
              ∘ (fun r : ℝ => r ^ 2) := rfl
        rw [heq, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← iteratedFDerivWithin_univ]
        exact hcomp
      have hlayerfun : (fun s : ℝ => layerTrunc G ℓ d τ s)
          = fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ) * tailIntegral h (s ^ 2) := by
        funext s
        rw [layerTrunc_eq_tailIntegral]
      rw [hlayerfun]
      calc (|r| ^ k) * ‖iteratedDeriv l
            (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ) * tailIntegral h (s ^ 2)) r‖
          ≤ |r| ^ k * ((l.factorial : ℝ) * (Real.exp (-(Real.pi * r ^ 2))
              * (((l + 1 : ℕ) : ℝ) * (4 * C' * (2 * Real.pi) ^ l * tailDecay M l)))
                * (2 * |r| + 2) ^ l) := mul_le_mul_of_nonneg_left hcomp' (by positivity)
        _ = (l.factorial : ℝ) * ((l + 1 : ℕ) : ℝ) * (4 * C' * (2 * Real.pi) ^ l * tailDecay M l)
              * (|r| ^ k * (2 * |r| + 2) ^ l * Real.exp (-(Real.pi * r ^ 2))) := by
            ring
        _ ≤ (l.factorial : ℝ) * ((l + 1 : ℕ) : ℝ) * (4 * C' * (2 * Real.pi) ^ l * tailDecay M l)
              * W := by
            have h1 : (0 : ℝ) ≤ (l.factorial : ℝ) * ((l + 1 : ℕ) : ℝ)
                * (4 * C' * (2 * Real.pi) ^ l * tailDecay M l) := by
              have := tailDecay_nonneg M l; positivity
            exact mul_le_mul_of_nonneg_left (hW r) h1
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
      have h2 : (0 : ℝ) ≤ 4 * C' * (2 * Real.pi) ^ l * tailDecay M l := by positivity
      positivity

end Work.Asymptotics
