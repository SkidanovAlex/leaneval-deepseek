import Mathlib
import Submission.Work.Holonomy3.mv_lex_defs
import Submission.Work.Holonomy3.polydisc_log_mean
import Submission.Work.Holonomy3.rev_jensen_trig
import Submission.Work.Holonomy3.pevalF_cons
import Submission.Work.Holonomy3.torMeasure_cons_integral
import Submission.Work.Holonomy3.integrable_cons_integral
import Submission.Work.Holonomy3.integrable_of_smoothed_lower_bound

/-!
# Integrability of `log ‖pevalF c (tor ·)‖` on the torus

For a non-zero finitely supported family `c` of multi-indices with complex coefficients, the
function `s ↦ log ‖pevalF c (tor s)‖` is integrable for the (normalised) torus measure `torMeasure`.

The proof rests on the following estimate, proved by induction on the number of variables: there is
a multi-index `n` in the support of `c` such that for every `ε > 0`

`log ‖c n‖ ≤ ∫ s, log (‖pevalF c (tor s)‖ + ε)`.

The induction step reverses the first variable: writing `P_{s'}(w) = ∑_k G_k(s') w^k` for the
polynomial obtained by fixing the remaining coordinates, the reversals `w^N P_{s'}(1/w)` of the
one-variable polynomials have constant term `G_N(s')`, so the one-variable smoothed Jensen
inequality gives `log ‖G_N(s')‖ ≤ ∫_{s₀} log ‖F(s₀, s')‖`. Integrating in `s'` and passing to the
slice `sliceF c N` (where `N` is the maximal first coordinate occurring in the support) gives the
induction step. The resulting lower bound is uniform in `ε`, and a final measure theory step turns a
uniform lower bound for the smoothed quantities into integrability of the limit.
-/

namespace Work.Holonomy3

open MeasureTheory
open scoped BigOperators

noncomputable section

lemma isProbabilityMeasure_torMeasure (d : ℕ) : IsProbabilityMeasure (torMeasure d) := by
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; norm_num⟩
  rw [torMeasure]
  infer_instance

/-! ### helpers -/

lemma norm_tor {d : ℕ} (s : Fin d → ℝ) (j : Fin d) : ‖tor s j‖ = 1 := by
  have h : tor s j = Complex.exp ((((2 * Real.pi * s j : ℝ)) : ℂ) * Complex.I) := by
    rw [tor]; congr 1; push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma norm_pevalF_le {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) (s : Fin d → ℝ) :
    ‖pevalF c (tor s)‖ ≤ ∑ m ∈ c.support, ‖c m‖ := by
  unfold pevalF
  refine le_trans (norm_sum_le c.support (fun m => c m * ∏ j, tor s j ^ (m j))) (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro m hm
  rw [norm_mul, norm_prod]
  simp [norm_tor]

lemma continuous_pevalF_tor {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) :
    Continuous (fun s : Fin d → ℝ => pevalF c (tor s)) := by
  have htor : Continuous (fun s : Fin d → ℝ => tor s) := by
    apply continuous_pi
    intro j
    unfold tor
    fun_prop
  unfold pevalF
  refine continuous_finsetSum _ (fun m hm => ?_)
  refine Continuous.mul continuous_const ?_
  refine continuous_finsetProd _ (fun j _ => ?_)
  exact ((continuous_apply j).comp htor).pow _

lemma continuous_log_norm_pevalF {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun s : Fin d → ℝ => Real.log (‖pevalF c (tor s)‖ + ε)) := by
  refine Continuous.log ((continuous_pevalF_tor c).norm.add_const ε) (fun s => ?_)
  exact ne_of_gt (by have h := norm_nonneg (pevalF c (tor s)); linarith)

lemma integrable_log_norm_pevalF {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun s : Fin d → ℝ => Real.log (‖pevalF c (tor s)‖ + ε)) (torMeasure d) := by
  haveI := isProbabilityMeasure_torMeasure d
  have hA : (0:ℝ) ≤ ∑ m ∈ c.support, ‖c m‖ := Finset.sum_nonneg (fun m _ => norm_nonneg _)
  refine Integrable.of_bound (continuous_log_norm_pevalF c hε).aestronglyMeasurable
    (max |Real.log ε| |Real.log ((∑ m ∈ c.support, ‖c m‖) + ε)|) ?_
  refine Filter.Eventually.of_forall (fun t => ?_)
  have hle : ‖pevalF c (tor t)‖ ≤ ∑ m ∈ c.support, ‖c m‖ := norm_pevalF_le c t
  have hn0 : (0:ℝ) ≤ ‖pevalF c (tor t)‖ := norm_nonneg _
  have hlo : Real.log ε ≤ Real.log (‖pevalF c (tor t)‖ + ε) := Real.log_le_log hε (by linarith)
  have hhi : Real.log (‖pevalF c (tor t)‖ + ε) ≤
      Real.log ((∑ m ∈ c.support, ‖c m‖) + ε) := Real.log_le_log (by linarith) (by linarith)
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have h1 : -|Real.log ε| ≤ Real.log ε := neg_abs_le _
    have h2 : |Real.log ε| ≤ max |Real.log ε| |Real.log ((∑ m ∈ c.support, ‖c m‖) + ε)| :=
      le_max_left _ _
    linarith
  · have h1 : Real.log ((∑ m ∈ c.support, ‖c m‖) + ε) ≤
        |Real.log ((∑ m ∈ c.support, ‖c m‖) + ε)| := le_abs_self _
    have h2 : |Real.log ((∑ m ∈ c.support, ‖c m‖) + ε)| ≤
        max |Real.log ε| |Real.log ((∑ m ∈ c.support, ‖c m‖) + ε)| := le_max_right _ _
    linarith

/-! ### the iteration -/

theorem iterated_jensen_bound : ∀ (d : ℕ) (c : (Fin d →₀ ℕ) →₀ ℂ), c ≠ 0 →
    ∃ n ∈ c.support, ∀ ε : ℝ, 0 < ε →
      Real.log ‖c n‖ ≤ ∫ s : Fin d → ℝ, Real.log (‖pevalF c (tor s)‖ + ε) ∂(torMeasure d) := by
  intro d
  induction d with
  | zero =>
    intro c hc
    have hc0 : c 0 ≠ 0 := by
      intro h0
      refine hc (Finsupp.ext (fun m => ?_))
      have hm : m = 0 := Subsingleton.elim m 0
      rw [hm, h0]
      rfl
    refine ⟨0, ?_, ?_⟩
    · rwa [Finsupp.mem_support_iff]
    · intro ε hε
      have hpeval : ∀ s : Fin 0 → ℝ, pevalF c (tor s) = c 0 := by
        intro s
        unfold pevalF
        rw [Finset.sum_eq_single 0]
        · show c 0 * (∏ j : Fin 0, tor s j ^ ((0 : Fin 0 →₀ ℕ) j)) = c 0
          rw [Finset.prod_eq_one (fun j _ => by rw [Finsupp.zero_apply]; exact pow_zero _), mul_one]
        · intro m hm hm0
          exact absurd (Subsingleton.elim m 0) hm0
        · intro h
          rw [Finsupp.notMem_support_iff.mp h, zero_mul]
      have hconst : (fun s : Fin 0 → ℝ => Real.log (‖pevalF c (tor s)‖ + ε))
          = fun _ : Fin 0 → ℝ => Real.log (‖c 0‖ + ε) := by
        funext s; rw [hpeval s]
      rw [hconst]
      haveI := isProbabilityMeasure_torMeasure 0
      rw [MeasureTheory.integral_const, measureReal_def, MeasureTheory.measure_univ,
        ENNReal.toReal_one, one_smul]
      exact Real.log_le_log (norm_pos_iff.mpr hc0) (by linarith)
  | succ d ih =>
    intro c hc
    have hne : (suppFst c).Nonempty := by
      obtain ⟨m, hm⟩ := Finsupp.support_nonempty_iff.mpr hc
      exact ⟨m 0, Finset.mem_image.mpr ⟨m, hm, rfl⟩⟩
    have hNmem : (suppFst c).max' hne ∈ suppFst c := Finset.max'_mem _ _
    have hNle : ∀ k ∈ suppFst c, k ≤ (suppFst c).max' hne := fun k hk => Finset.le_max' _ _ hk
    have hNbound : ∀ m ∈ c.support, m 0 ≤ (suppFst c).max' hne :=
      fun m hm => hNle (m 0) (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
    have hcs : sliceF c ((suppFst c).max' hne) ≠ 0 := by
      obtain ⟨m, hm, hm0⟩ := mem_suppFst.mp hNmem
      have hmne : c m ≠ 0 := Finsupp.mem_support_iff.mp hm
      let m' : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i : Fin d => m i.succ)
      have hm' : ∀ j : Fin d, m' j = m j.succ := by
        intro j
        have h1 : Finsupp.equivFunOnFinite m' = fun i : Fin d => m i.succ := by
          dsimp only [m']; rw [Equiv.apply_symm_apply]
        rw [← congrFun h1 j]
        exact Finsupp.equivFunOnFinite_apply m' j
      have hcons : consIdx ((suppFst c).max' hne) m' = m := by
        apply Finsupp.ext
        intro i
        rw [consIdx_apply]
        cases i using Fin.cases with
        | zero => simp [hm0]
        | succ j => simp [hm' j]
      intro hzero
      have h1 : sliceF c ((suppFst c).max' hne) m' = 0 := by rw [hzero]; rfl
      rw [sliceF_apply, hcons] at h1
      exact hmne h1
    obtain ⟨n', hn'mem, hn'bd⟩ := ih (sliceF c ((suppFst c).max' hne)) hcs
    refine ⟨consIdx ((suppFst c).max' hne) n', ?_, ?_⟩
    · rw [Finsupp.mem_support_iff]
      have h := Finsupp.mem_support_iff.mp hn'mem
      rwa [sliceF_apply] at h
    · intro ε hε
      have h1 := hn'bd ε hε
      rw [sliceF_apply] at h1
      have h2 : ∫ s' : Fin d → ℝ,
            Real.log (‖pevalF (sliceF c ((suppFst c).max' hne)) (tor s')‖ + ε) ∂(torMeasure d)
          ≤ ∫ t : Fin (d+1) → ℝ, Real.log (‖pevalF c (tor t)‖ + ε) ∂(torMeasure (d+1)) := by
        haveI := isProbabilityMeasure_torMeasure (d+1)
        haveI := isProbabilityMeasure_torMeasure d
        have hΦ : Integrable (fun t : Fin (d+1) → ℝ => Real.log (‖pevalF c (tor t)‖ + ε))
            (torMeasure (d+1)) := integrable_log_norm_pevalF c hε
        have hb : Integrable (fun s' : Fin d → ℝ =>
            Real.log (‖pevalF (sliceF c ((suppFst c).max' hne)) (tor s')‖ + ε)) (torMeasure d) :=
          integrable_log_norm_pevalF (sliceF c ((suppFst c).max' hne)) hε
        have hI : Integrable (fun s' : Fin d → ℝ =>
            ∫ s₀ : ℝ, Real.log (‖pevalF c (tor (Fin.cons s₀ s'))‖ + ε)
              ∂(volume.restrict (Set.Icc (0:ℝ) 1))) (torMeasure d) :=
          integrable_cons_integral _ hΦ
        have hpt : ∀ s' : Fin d → ℝ,
            Real.log (‖pevalF (sliceF c ((suppFst c).max' hne)) (tor s')‖ + ε) ≤
              ∫ s₀ : ℝ, Real.log (‖pevalF c (tor (Fin.cons s₀ s'))‖ + ε)
                ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
          intro s'
          have hrev := rev_jensen_trig (fun k => pevalF (sliceF c k) (tor s'))
            ((suppFst c).max' hne) hε
          have hcongr : ∀ θ : ℝ, (∑ k ∈ Finset.range ((suppFst c).max' hne + 1),
                pevalF (sliceF c k) (tor s') * circlePt θ ^ k)
              = pevalF c (tor (Fin.cons θ s')) := by
            intro θ
            have hconspt : tor (Fin.cons θ s') = consPt (circlePt θ) (tor s') := by
              funext i
              cases i using Fin.cases with
              | zero => simp [consPt, tor, circlePt]
              | succ j => simp [consPt, tor, circlePt]
            rw [hconspt, pevalF_cons c ((suppFst c).max' hne) hNbound (circlePt θ) (tor s')]
          have hfun : (fun θ : ℝ => Real.log (‖∑ k ∈ Finset.range ((suppFst c).max' hne + 1),
                pevalF (sliceF c k) (tor s') * circlePt θ ^ k‖ + ε))
              = fun θ : ℝ => Real.log (‖pevalF c (tor (Fin.cons θ s'))‖ + ε) := by
            funext θ; rw [hcongr θ]
          rw [hfun] at hrev
          simpa using hrev
        have hmono := integral_mono hb hI hpt
        rw [← torMeasure_cons_integral _ hΦ] at hmono
        exact hmono
      linarith

/-- **The main result.** For a non-zero finitely supported coefficient family `c`, the function
`s ↦ log ‖pevalF c (tor s)‖` is integrable for the torus measure.

Indeed `iterated_jensen_bound` provides a uniform lower bound `L` for all the smoothed integrals
`∫ log (‖pevalF c (tor ·)‖ + ε)`, `ε > 0`, and `integrable_of_smoothed_lower_bound` turns such a
bound into integrability of the limit (the two-sided bound `log (g + 1) ≤ C` with `C = log (A + 1)`,
`A = ∑ ‖c m‖`, supplies the upper bound). -/
theorem mv_lex_log_poly_integrable {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) (hc : c ≠ 0) :
    MeasureTheory.Integrable (fun s : Fin d → ℝ => Real.log ‖pevalF c (tor s)‖) (torMeasure d) := by
  obtain ⟨n, hnmem, hbound⟩ := iterated_jensen_bound d c hc
  haveI := isProbabilityMeasure_torMeasure d
  set g : (Fin d → ℝ) → ℝ := fun s => ‖pevalF c (tor s)‖ with hg
  have hgm : Measurable g := (continuous_pevalF_tor c).norm.measurable
  have hg0 : ∀ s, 0 ≤ g s := fun s => norm_nonneg _
  have hA : (0:ℝ) ≤ ∑ m ∈ c.support, ‖c m‖ := Finset.sum_nonneg (fun m _ => norm_nonneg _)
  have hC0 : (0:ℝ) ≤ Real.log ((∑ m ∈ c.support, ‖c m‖) + 1) := by
    apply Real.log_nonneg; linarith
  have hgC : ∀ s, Real.log (g s + 1) ≤ Real.log ((∑ m ∈ c.support, ‖c m‖) + 1) := by
    intro s
    apply Real.log_le_log
    · have := hg0 s; linarith
    · have := norm_pevalF_le c s; linarith
  have hε0 : ∀ k : ℕ, 0 < (1:ℝ)/((k:ℝ)+1) := fun k => by positivity
  have hε1 : ∀ k : ℕ, (1:ℝ)/((k:ℝ)+1) ≤ 1 := fun k => by
    rw [div_le_one (by positivity)]; exact_mod_cast Nat.le_add_left 1 k
  have hεt : Filter.Tendsto (fun k : ℕ => (1:ℝ)/((k:ℝ)+1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hlow : ∀ k : ℕ,
      Real.log ‖c n‖ ≤ ∫ s, Real.log (g s + (1:ℝ)/((k:ℝ)+1)) ∂(torMeasure d) := by
    intro k
    have h := hbound (1/((k:ℝ)+1)) (hε0 k)
    simpa [hg] using h
  have := integrable_of_smoothed_lower_bound (μ := torMeasure d) (g := g) hgm hg0 hC0 hgC
    hε0 hε1 hεt hlow
  simpa [hg] using this

end
end Work.Holonomy3
