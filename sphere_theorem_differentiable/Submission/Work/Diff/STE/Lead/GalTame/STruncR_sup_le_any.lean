import Mathlib
import Submission.Work.Diff.STE.Lead.STruncR_sup_le
import Submission.Work.Diff.STE.B3.abs_scoeff_le
import Submission.Work.Diff.STE.B3.JPrelim

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

/-- **`L^∞` bound for the Friedrichs truncation, uniform in `ε ∈ (0, ε₁]`.**  For any `ε₁ > 0`
there is a constant `C ≥ 0` with `|STruncR ρ ε f z| ≤ C * M` for every `ε ∈ (0, ε₁]`, every `M ≥ 0`
and every `f` with `|f| ≤ M` pointwise and support in the open cube `(-1/2,1/2)^n`.

For `ε ≤ 1` this is `Work.Diff.STE.Lead.STruncR_sup_le` verbatim.  For `1 ≤ ε` the box
`truncBox ε = ∏ᵢ [-⌈√2/ε⌉, ⌈√2/ε⌉]` is contained in `∏ᵢ [-2,2]` (so at most `5 ^ n` terms), the
multiplier has `‖trunc ρ ε c m‖ ≤ ‖c m‖` (`|ρ| ≤ 1`), and `‖perCoeff f m‖ ≤ M` because the
periodisation of a cube-supported `f` has a single non-zero term
(`Work.Diff.STE.B3.abs_scoeff_perCoeffN_norm_le`); hence `|STruncR ρ ε f z| ≤ 5 ^ n * M`. -/
theorem STruncR_sup_le_any
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hρ : ∀ y : Fin (Module.finrank ℝ E) → ℝ, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (ε₁ : ℝ) (hε₁ : 0 < ε₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) ε₁,
      ∀ (f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (M : ℝ), 0 ≤ M →
        (∀ z : Fin (Module.finrank ℝ E) → ℝ, |f z| ≤ M) →
        (Function.support f ⊆ Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) =>
          Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) →
        ∀ z : Fin (Module.finrank ℝ E) → ℝ,
          |Work.Diff.STE.B3Data.STruncR ρ ε f z| ≤ C * M := by
  classical
  obtain ⟨C₁, hC₁, hC₁b⟩ :=
    Work.Diff.STE.Lead.STruncR_sup_le (E := E) ρ hρ hρ0 hρs
  refine ⟨max C₁ (5 ^ Module.finrank ℝ E), le_trans hC₁ (le_max_left _ _), ?_⟩
  intro ε hεIoc f M hM hf hsupp z
  obtain ⟨hεpos, hεle⟩ := hεIoc
  by_cases hε1 : ε ≤ 1
  · exact le_trans (hC₁b ε ⟨hεpos, hε1⟩ f M hM hf hsupp z)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hM)
  · have hεge : 1 ≤ ε := le_of_not_ge hε1
    have hceil : ⌈Real.sqrt 2 / ε⌉ ≤ (2 : ℤ) := by
      refine Int.ceil_le.mpr ?_
      have h2 : Real.sqrt 2 ≤ 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      have h3 : Real.sqrt 2 / ε ≤ Real.sqrt 2 := by
        rw [div_le_iff₀ hεpos]
        nlinarith [Real.sqrt_nonneg 2, hεge]
      exact_mod_cast le_trans h3 h2
    have hcrd : (Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε).card
        ≤ 5 ^ Module.finrank ℝ E := by
      have hsub : Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε
          ⊆ Fintype.piFinset (fun _ : Fin (Module.finrank ℝ E) => Finset.Icc (-(2 : ℤ)) 2) := by
        intro m hm
        rw [Fintype.mem_piFinset]
        intro i
        have h := (Work.Diff.STE.B3.mem_truncBox.mp hm) i
        exact Finset.mem_Icc.mpr ⟨by linarith [h.1, hceil], by linarith [h.2, hceil]⟩
      refine le_trans (Finset.card_le_card hsub) ?_
      rw [Fintype.card_piFinset]
      simp
    have hper : ∀ m : Fin (Module.finrank ℝ E) → ℤ,
        ‖Work.Diff.STE.B3.perCoeff f m‖ ≤ M := by
      intro m
      have hsub : Function.support f ⊆ Set.pi Set.univ
          (fun _ : Fin (Module.finrank ℝ E) => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) := by
        intro y hy i _
        have hi := Set.mem_pi.mp (hsupp hy) i (Set.mem_univ i)
        exact ⟨(Set.mem_Ioo.mp hi).1, (Set.mem_Ioo.mp hi).2.le⟩
      have h1 := Work.Diff.STE.B3.abs_scoeff_perCoeffN_norm_le (n := Module.finrank ℝ E)
        f hsub M hf m
      simpa only [Work.Diff.STE.B3.perCoeff, Work.Diff.STE.B3.perCoeffN] using h1
    have hnorm : ∀ m : Fin (Module.finrank ℝ E) → ℤ,
        |(Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeff f) m
            * Work.Diff.STE.fourierExp m z).re| ≤ M := by
      intro m
      refine le_trans (Complex.abs_re_le_norm _) ?_
      have h1 : ‖((ρ (ε • fun i => (m i : ℝ)) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        simpa only [Real.norm_eq_abs] using hρ (ε • fun i => (m i : ℝ))
      have h3 : ‖Work.Diff.STE.fourierExp m z‖ = 1 :=
        Work.Diff.STE.B3.abs_scoeff_norm_fourierExp m z
      calc ‖Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeff f) m
              * Work.Diff.STE.fourierExp m z‖
          = ‖((ρ (ε • fun i => (m i : ℝ)) : ℝ) : ℂ) * Work.Diff.STE.B3.perCoeff f m‖
              * ‖Work.Diff.STE.fourierExp m z‖ := by
            rw [norm_mul, Work.Diff.STE.trunc]
        _ ≤ 1 * M * 1 := by
            rw [norm_mul, h3]
            have h4 : ‖((ρ (ε • fun i => (m i : ℝ)) : ℝ) : ℂ)‖
                * ‖Work.Diff.STE.B3.perCoeff f m‖ ≤ 1 * M :=
              mul_le_mul h1 (hper m) (norm_nonneg _) (by norm_num)
            linarith [h4]
        _ = M := by ring
    rw [Work.Diff.STE.B3.STruncR_eq_sum (E := E) ρ ε hεpos hρ0 f z]
    calc |∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
            (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeff f) m
              * Work.Diff.STE.fourierExp m z).re|
        ≤ ∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
            |(Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeff f) m
              * Work.Diff.STE.fourierExp m z).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε, M :=
          Finset.sum_le_sum (fun m _ => hnorm m)
      _ = ((Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε).card : ℝ) * M := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (5 ^ Module.finrank ℝ E : ℝ) * M :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcrd) hM
      _ ≤ max C₁ (5 ^ Module.finrank ℝ E) * M :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hM

end Work.Diff.STE.Lead.GalTame
