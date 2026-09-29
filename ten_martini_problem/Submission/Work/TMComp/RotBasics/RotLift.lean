import Submission.Work.TMComp.RotBasics.PSIter
import Submission.Work.TMComp.RotBasics.PSCont
import Submission.Work.TMComp.RotBasics.Fekete

/-!
# The fibre rotation number: parts 1–3 of `P_RotBasics`

* `sn α lam E n = ∫₀¹ pruferIter α lam E n x 0 dx`, the `n`-th Prüfer mean;
* `sn_almostAdditive`: `|sn (n+m) - sn n - sn m| ≤ 1` for `n, m ≥ 1` (cocycle identity,
  periodicity in `x`, and the displacement bound `|F t - F 0 - t| ≤ 1`);
* Fekete's lemma then gives the existence of `lim sn/n`, with the uniform rate `1/n`;
* `rotLift_tendsto` (part 1) and `rotLift_tendsto_rate`;
* `ids_monotone` (part 2) and `rotLift_continuous` (part 3).
-/

namespace Work.TMComp.RotBasics

open Work.TMContract
open MeasureTheory Filter
open scoped Topology

noncomputable section

theorem pruferIter_continuous_xt (α lam E : ℝ) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => pruferIter α lam E n p.1 p.2) := by
  induction n with
  | zero => simpa [pruferIter_zero] using continuous_snd
  | succ n ih =>
    have hfun : (fun p : ℝ × ℝ => pruferIter α lam E (n + 1) p.1 p.2)
        = fun p : ℝ × ℝ =>
            pruferStep (E - 2 * lam * Real.cos (2 * Real.pi * (p.1 + (n : ℝ) * α)))
              (pruferIter α lam E n p.1 p.2) := by
      funext p
      rw [pruferIter_succ]
    rw [hfun]
    have hg : Continuous (fun p : ℝ × ℝ =>
        E - 2 * lam * Real.cos (2 * Real.pi * (p.1 + (n : ℝ) * α))) := by fun_prop
    exact Continuous.comp (g := fun q : ℝ × ℝ => pruferStep q.1 q.2) pruferStep_continuous
      (hg.prodMk ih)

/-- The `n`-th Prüfer mean `∫₀¹ pruferIter α lam E n x 0 dx`. -/
def sn (α lam E : ℝ) (n : ℕ) : ℝ := ∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0

theorem sn_zero (α lam E : ℝ) : sn α lam E 0 = 0 := by
  simp [sn, pruferIter_zero]

theorem sn_almostAdditive (α lam E : ℝ) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    |sn α lam E (n + m) - sn α lam E n - sn α lam E m| ≤ 1 := by
  set G : ℝ → ℝ → ℝ := fun y u => pruferIter α lam E m y u with hG
  set P : ℝ → ℝ := fun x => pruferIter α lam E n x 0 with hP
  have hcoc : ∀ x : ℝ, pruferIter α lam E (n + m) x 0 = G (x + (n : ℝ) * α) (P x) := by
    intro x
    rw [hG, hP, pruferIter_cocycle]
  have hGper : ∀ y u : ℝ, G (y + 1) u = G y u := fun y u => pruferIter_periodic_x α lam E m y u
  have hsub : sn α lam E (n + m) = ∫ x in (0 : ℝ)..1, G (x + (n : ℝ) * α) (P x) := by
    show (∫ x in (0 : ℝ)..1, pruferIter α lam E (n + m) x 0)
      = ∫ x in (0 : ℝ)..1, G (x + (n : ℝ) * α) (P x)
    apply intervalIntegral.integral_congr
    intro x _
    exact hcoc x
  -- continuity of the integrands
  have hGcont : Continuous (fun p : ℝ × ℝ => G p.1 p.2) := pruferIter_continuous_xt α lam E m
  have hPcont : Continuous P := by
    have h1 : Continuous (fun x : ℝ => pruferIter α lam E n x 0) :=
      (pruferIter_continuous_xt α lam E n).comp (continuous_id.prodMk continuous_const)
    simpa [Function.comp_def, hP] using h1
  have hshiftcont : Continuous (fun x : ℝ => G (x + (n : ℝ) * α) 0) := by
    have h1 : Continuous (fun x : ℝ => (x + (n : ℝ) * α, (0 : ℝ))) := by fun_prop
    exact hGcont.comp h1
  have hGPcont : Continuous (fun x : ℝ => G (x + (n : ℝ) * α) (P x)) := by
    have h1 : Continuous (fun x : ℝ => (x + (n : ℝ) * α, P x)) := by fun_prop
    exact hGcont.comp h1
  set X : ℝ := ∫ x in (0 : ℝ)..1,
    (G (x + (n : ℝ) * α) (P x) - G (x + (n : ℝ) * α) 0 - P x) with hX
  have hsplit : (∫ x in (0 : ℝ)..1, G (x + (n : ℝ) * α) (P x))
      = (∫ x in (0 : ℝ)..1, G (x + (n : ℝ) * α) 0)
        + (∫ x in (0 : ℝ)..1, P x) + X := by
    rw [hX]
    have hI1 : IntervalIntegrable (fun x : ℝ => G (x + (n : ℝ) * α) (P x)) volume 0 1 :=
      hGPcont.intervalIntegrable 0 1
    have hI2 : IntervalIntegrable (fun x : ℝ => G (x + (n : ℝ) * α) 0) volume 0 1 :=
      hshiftcont.intervalIntegrable 0 1
    have hI3 : IntervalIntegrable
        (fun x : ℝ => G (x + (n : ℝ) * α) (P x) - G (x + (n : ℝ) * α) 0) volume 0 1 :=
      hI1.sub hI2
    have hI4 : IntervalIntegrable P volume 0 1 := hPcont.intervalIntegrable 0 1
    have hI5 : IntervalIntegrable (fun x : ℝ =>
        G (x + (n : ℝ) * α) (P x) - G (x + (n : ℝ) * α) 0 - P x) volume 0 1 :=
      hI3.sub hI4
    rw [intervalIntegral.integral_sub hI3 hI4, intervalIntegral.integral_sub hI1 hI2]
    ring
  have hPmean : (∫ x in (0 : ℝ)..1, P x) = sn α lam E n := by
    show (∫ x in (0 : ℝ)..1, P x) = ∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0
    rw [hP]
  have hGmean : (∫ x in (0 : ℝ)..1, G (x + (n : ℝ) * α) 0) = sn α lam E m := by
    show (∫ x in (0 : ℝ)..1, G (x + (n : ℝ) * α) 0)
      = ∫ x in (0 : ℝ)..1, pruferIter α lam E m x 0
    rw [hG]
    have hper : Function.Periodic (fun y : ℝ => pruferIter α lam E m y 0) 1 :=
      fun y => pruferIter_periodic_x α lam E m y 0
    rw [intervalIntegral.integral_comp_add_right (fun y : ℝ => pruferIter α lam E m y 0)
      ((n : ℝ) * α)]
    rw [zero_add, show (1 : ℝ) + (n : ℝ) * α = (n : ℝ) * α + 1 by ring]
    rw [hper.intervalIntegral_add_eq ((n : ℝ) * α) 0]
    norm_num
  have hsmall : |X| ≤ 1 := by
    rw [hX]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := 1)
      (f := fun x : ℝ => G (x + (n : ℝ) * α) (P x) - G (x + (n : ℝ) * α) 0 - P x)
      (fun x _ => by
        rw [Real.norm_eq_abs]
        exact pruferIter_bound α lam E m (x + (n : ℝ) * α) (P x))
    simpa using h
  rw [hsub, hsplit, hGmean, hPmean]
  have hcomb : sn α lam E m + sn α lam E n + X - sn α lam E n - sn α lam E m = X := by ring
  rw [hcomb]
  exact hsmall

theorem sn_continuous (lam : ℝ) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => sn p.1 lam p.2 n) := by
  show Continuous (fun p : ℝ × ℝ => ∫ x in (0 : ℝ)..1, pruferIter p.1 lam p.2 n x 0)
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 1
  have h : Continuous (fun q : (ℝ × ℝ) × ℝ => ((q.1.1, q.1.2, q.2) : ℝ × ℝ × ℝ)) := by
    refine Continuous.prodMk continuous_fst.fst ?_
    exact Continuous.prodMk continuous_fst.snd continuous_snd
  exact (pruferIter_continuous lam n).comp h

/-- **Part 1** (existence of the rotation-number limit), with the uniform rate. -/
theorem rotLift_tendsto_rate (α lam E : ℝ) :
    Filter.Tendsto (fun n : ℕ => sn α lam E n / (n : ℝ)) Filter.atTop (nhds (rotLift α lam E)) ∧
      ∀ n : ℕ, 1 ≤ n → |sn α lam E n / (n : ℝ) - rotLift α lam E| ≤ 1 / (n : ℝ) := by
  obtain ⟨L, hL, hrate⟩ := fekete_of_almostAdditive (s := fun n => sn α lam E n) (C := 1)
    (by norm_num) (fun n m hn hm => sn_almostAdditive α lam E hn hm)
  have hlim : rotLift α lam E = L := by
    rw [rotLift]
    exact hL.limUnder_eq
  refine ⟨?_, ?_⟩
  · rw [hlim]; exact hL
  · intro n hn
    simpa [hlim] using hrate n hn

theorem rotLift_tendsto (α lam E : ℝ) :
    Filter.Tendsto (fun n : ℕ => (∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) / (n : ℝ))
      Filter.atTop (nhds (rotLift α lam E)) :=
  (rotLift_tendsto_rate α lam E).1

theorem rotLift_rate (α lam E : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |(∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) / (n : ℝ) - rotLift α lam E|
      ≤ 1 / (n : ℝ) :=
  (rotLift_tendsto_rate α lam E).2 n hn

/-- **Part 2**: monotonicity of the integrated density of states. -/
theorem ids_monotone (α lam : ℝ) : Monotone (ids α lam) := by
  intro E₁ E₂ h12
  have hanti : ∀ n : ℕ, sn α lam E₂ n ≤ sn α lam E₁ n := by
    intro n
    show (∫ x in (0 : ℝ)..1, pruferIter α lam E₂ n x 0)
      ≤ ∫ x in (0 : ℝ)..1, pruferIter α lam E₁ n x 0
    have hI1 : IntervalIntegrable (fun x : ℝ => pruferIter α lam E₂ n x 0) volume 0 1 :=
      ((pruferIter_continuous_xt α lam E₂ n).comp
        (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
    have hI2 : IntervalIntegrable (fun x : ℝ => pruferIter α lam E₁ n x 0) volume 0 1 :=
      ((pruferIter_continuous_xt α lam E₁ n).comp
        (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
    exact intervalIntegral.integral_mono (show (0 : ℝ) ≤ 1 by norm_num) hI1 hI2
      (fun x => pruferIter_antitone_E α lam n x 0 h12)
  have h1 := (rotLift_tendsto_rate α lam E₁).1
  have h2 := (rotLift_tendsto_rate α lam E₂).1
  have hle : rotLift α lam E₂ ≤ rotLift α lam E₁ := by
    refine le_of_tendsto_of_tendsto h2 h1 (Eventually.of_forall fun n => ?_)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · rw [div_le_div_iff_of_pos_right (Nat.cast_pos.mpr hn)]
      exact hanti n
  simp only [ids]
  linarith

/-- **Part 3**: joint continuity of the rotation number in `(α, E)`. -/
theorem rotLift_continuous (lam : ℝ) :
    Continuous (fun p : ℝ × ℝ => rotLift p.1 lam p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨α₀, E₀⟩
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN1, hN⟩ : ∃ N : ℕ, 1 ≤ N ∧ 4 / (N : ℝ) < ε := by
    obtain ⟨k, hk⟩ := exists_nat_gt (4 / ε)
    refine ⟨max k 1, le_max_right k 1, ?_⟩
    have hpos : (0 : ℝ) < ((max k 1 : ℕ) : ℝ) := by
      have h1 : (1 : ℕ) ≤ max k 1 := le_max_right k 1
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
    rw [div_lt_iff₀ hpos]
    have hk' : 4 / ε < ((max k 1 : ℕ) : ℝ) :=
      lt_of_lt_of_le hk (by exact_mod_cast le_max_left k 1)
    have h5 : 4 < ε * ((max k 1 : ℕ) : ℝ) := by
      have h4 : (4 : ℝ) = (4 / ε) * ε := by field_simp
      rw [h4]
      have h6 := mul_lt_mul_of_pos_right hk' hε
      nlinarith [h6]
    exact h5
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  have hcont : ContinuousAt (fun p : ℝ × ℝ => sn p.1 lam p.2 N) (α₀, E₀) :=
    (sn_continuous lam N).continuousAt
  have hballpos : 0 < ε / 2 * N := by positivity
  have hball : Metric.ball (sn α₀ lam E₀ N) (ε / 2 * N) ∈ 𝓝 (sn α₀ lam E₀ N) :=
    Metric.isOpen_ball.mem_nhds (by simp [Metric.mem_ball, hballpos])
  have h1N : 1 / (N : ℝ) ≤ ε / 4 := by
    have h4N : 4 < ε * (N : ℝ) := by
      rw [div_lt_iff₀ hNposR] at hN
      exact hN
    rw [div_le_iff₀ hNposR]
    nlinarith [h4N, hε, hNposR]
  filter_upwards [hcont.tendsto.eventually hball] with p hp
  have hp' : dist (sn p.1 lam p.2 N) (sn α₀ lam E₀ N) < ε / 2 * N := by
    simpa [Metric.mem_ball] using hp
  rw [Real.dist_eq]
  have hdiv : |sn p.1 lam p.2 N / (N : ℝ) - sn α₀ lam E₀ N / (N : ℝ)| < ε / 2 := by
    rw [← sub_div, abs_div, abs_of_pos hNposR, div_lt_iff₀ hNposR]
    rw [Real.dist_eq] at hp'
    linarith [hp']
  have hrate₁ : |sn p.1 lam p.2 N / (N : ℝ) - rotLift p.1 lam p.2| ≤ 1 / (N : ℝ) :=
    (rotLift_tendsto_rate p.1 lam p.2).2 N hN1
  have hrate₂ : |sn α₀ lam E₀ N / (N : ℝ) - rotLift α₀ lam E₀| ≤ 1 / (N : ℝ) :=
    (rotLift_tendsto_rate α₀ lam E₀).2 N hN1
  have hrate₁' : |rotLift p.1 lam p.2 - sn p.1 lam p.2 N / (N : ℝ)| ≤ 1 / (N : ℝ) := by
    rw [abs_sub_comm]
    exact hrate₁
  have htri : |rotLift p.1 lam p.2 - rotLift α₀ lam E₀|
      ≤ |rotLift p.1 lam p.2 - sn p.1 lam p.2 N / (N : ℝ)|
        + |sn p.1 lam p.2 N / (N : ℝ) - sn α₀ lam E₀ N / (N : ℝ)|
        + |sn α₀ lam E₀ N / (N : ℝ) - rotLift α₀ lam E₀| := by
    have h := abs_sub_le (rotLift p.1 lam p.2) (sn p.1 lam p.2 N / (N : ℝ))
      (rotLift α₀ lam E₀)
    have h' := abs_sub_le (sn p.1 lam p.2 N / (N : ℝ)) (sn α₀ lam E₀ N / (N : ℝ))
      (rotLift α₀ lam E₀)
    linarith
  linarith [htri, hrate₁', hdiv, hrate₂, h1N]

end

end Work.TMComp.RotBasics
