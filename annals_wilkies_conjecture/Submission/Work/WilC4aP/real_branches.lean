import Mathlib
import Submission.Work.WilC4aP.Basic
import Submission.Work.WilC4aP.RealExtract

namespace Work.WilC4aP

open Classical Topology Filter
open scoped BigOperators
open Polynomial

/-- The real part of a function that is complex-analytic at `0` is real-analytic at `0`
(companion of `analyticAt_im_of_complex`). -/
theorem analyticAt_re_of_complex {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℝ (fun x : ℝ => (f (x : ℂ)).re) 0 :=
  AnalyticAt.comp (g := fun z : ℂ => z.re) (f := fun x : ℝ => f (x : ℂ)) (x := 0)
    (Complex.reCLM.analyticAt (f 0)) (analyticAt_real_of_complex hf)

/-- An eventual statement on the punctured neighbourhood of `0` upgrades to an eventual
statement on `𝓝 0` carrying the guard `x ≠ 0`. -/
lemma eventually_nhds_of_eventually_nhdsWithin_ne {q : ℝ → Prop}
    (h : ∀ᶠ x : ℝ in 𝓝[≠] (0 : ℝ), q x) : ∀ᶠ x : ℝ in 𝓝 0, x ≠ 0 → q x := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp h
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with x hx hx0
  exact hsub ⟨hx, by simpa using hx0⟩

/-- An eventual statement at `𝓝 0` holds on a ball `(-ε, ε)` with `ε > 0`. -/
lemma exists_pos_ball_of_eventually_nhds {q : ℝ → Prop} (h : ∀ᶠ x : ℝ in 𝓝 0, q x) :
    ∃ ε > 0, ∀ x, |x| < ε → q x := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp h
  exact ⟨ε, hε, fun x hx => hsub (by simpa [Metric.mem_ball, Real.dist_eq] using hx)⟩

/-- For a real `s` with `|s| < ρF`, evaluating the fibre `Pz (polyOf F) s` at a real point `z`
(cast to `ℂ`) is the complexification of `mpoly c s z`. -/
theorem eval_Pz_polyOf_ofReal {d : ℕ} (F : Fin d → ℂ → ℂ) (c : Fin d → ℝ → ℝ) {ρF : ℝ}
    (hFc : ∀ j, ∀ x : ℝ, |x| < ρF → F j (x : ℂ) = (c j x : ℂ))
    {s : ℝ} (hs : |s| < ρF) (z : ℝ) :
    (Pz (polyOf F) (s : ℂ)).eval (z : ℂ) = ((WilkiesDesign.CG.C4a.mpoly c s z : ℝ) : ℂ) := by
  rw [Pz_polyOf, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  rw [WilkiesDesign.CG.C4a.mpoly]
  push_cast
  congr 1
  exact Finset.sum_congr rfl (fun j _ => by rw [hFc j s hs])

/-- **Real extraction.** From the complex Puiseux expansion of the complexified coefficients,
extract the real branches: the real roots of `mpoly c (r ^ N)` are exactly the values of
finitely many real-analytic functions of `r`.

PROOF HINT: `polyOf F` is monic of degree `d` (prove this from `monic_X_pow_add` and
`degree_sum_fin_lt`; `natDegree` follows from `natDegree_eq_of_degree_eq_some` after a degree
computation), so by `hfac` the roots of `Pz (polyOf F) (u ^ N)` are exactly the `η j u`.
By `reality_criterion` each `η j` is either real-valued near `0` or has no real value on
`(0, ε)`; let `J` be the set of `j` of the first kind, take `m = card J` and `ζ` the
restrictions of the `η j`, `j ∈ J`, to the real axis (real-analytic by
`analyticAt_real_of_complex`). For `0 < r < r0 := min (ρ, ε, ρF ^ (N⁻¹))` translate
`mpoly c (r ^ N) z = 0` into `(Pz (polyOf F) (r ^ N)).eval (z : ℂ) = 0` — via `Pz_polyOf`, the
agreement `hFc` at `r ^ N` and `ofReal_pow` — and use that a complex root of a product of
linear factors is one of its factors. -/
theorem real_branches {d : ℕ} {c : Fin d → ℝ → ℝ} {F : Fin d → ℂ → ℂ} {ρF : ℝ}
    (hρF : 0 < ρF) (hF : ∀ j, AnalyticOnNhd ℂ (F j) (Metric.ball 0 ρF))
    (hFc : ∀ j, ∀ x : ℝ, |x| < ρF → F j (x : ℂ) = (c j x : ℂ))
    {N : ℕ} (hN : 0 < N) {η : Fin d → ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hη : ∀ j, AnalyticOnNhd ℂ (η j) (Metric.ball 0 ρ))
    (hfac : Work.WilC4aP.FactoredOn (Work.WilC4aP.polyOf F) N η ρ) :
    ∃ (m : ℕ) (ζ : Fin m → ℝ → ℝ), (∀ i, AnalyticAt ℝ (ζ i) 0) ∧
      ∃ r0 > (0 : ℝ), ∀ r ∈ Set.Ioo (0 : ℝ) r0, ∀ z : ℝ,
        (WilkiesDesign.CG.C4a.mpoly c (r ^ N) z = 0 ↔ ∃ i, z = ζ i r) := by
  -- Each branch is either real-valued near `0`, or has no real value on a punctured
  -- neighbourhood of `0`.
  have hdich : ∀ j : Fin d, (∀ᶠ x : ℝ in 𝓝 0, (η j (x : ℂ)).im = 0) ∨
      (∀ᶠ x : ℝ in 𝓝[≠] (0 : ℝ), (η j (x : ℂ)).im ≠ 0) := fun j =>
    reality_criterion ((hη j) 0 (Metric.mem_ball_self hρ))
  let good : Fin d → Prop := fun j => ∀ᶠ x : ℝ in 𝓝 0, (η j (x : ℂ)).im = 0
  -- A single radius at which the dichotomy is decided for every branch simultaneously.
  have hphase : ∀ᶠ x : ℝ in 𝓝 0, ∀ j : Fin d,
      (good j → (η j (x : ℂ)).im = 0) ∧ (¬ good j → (x ≠ 0 → (η j (x : ℂ)).im ≠ 0)) := by
    rw [eventually_all]
    intro j
    by_cases hg : good j
    · filter_upwards [hg] with x hx
      exact ⟨fun _ => hx, fun h => absurd hg h⟩
    · rcases hdich j with h1 | h2
      · exact absurd h1 hg
      · filter_upwards [eventually_nhds_of_eventually_nhdsWithin_ne h2] with x hx
        exact ⟨fun h => absurd h hg, fun _ => hx⟩
  obtain ⟨ε, hεpos, hε⟩ := exists_pos_ball_of_eventually_nhds hphase
  -- The sub-collection of real branches and its enumeration.
  let ι := {j : Fin d // good j}
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, fun i r => (η (e i).val (r : ℂ)).re, ?_, ?_⟩
  · intro i
    exact analyticAt_re_of_complex ((hη (e i).val) 0 (Metric.mem_ball_self hρ))
  · refine ⟨min ε (min 1 (min ρ ρF)), ?_, ?_⟩
    · exact lt_min hεpos (lt_min one_pos (lt_min hρ hρF))
    · intro r hr z
      have hr0 : 0 < r := hr.1
      have hrlt : r < min ε (min 1 (min ρ ρF)) := hr.2
      have hrε : r < ε := lt_of_lt_of_le hrlt (min_le_left _ _)
      have hr1 : r < 1 :=
        lt_of_lt_of_le hrlt (le_trans (min_le_right _ _) (min_le_left _ _))
      have hrρ : r < ρ := lt_of_lt_of_le hrlt
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
      have hrρF : r < ρF := lt_of_lt_of_le hrlt
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
      have hrpow_lt_ρF : |r ^ N| < ρF := by
        rw [abs_of_nonneg (pow_nonneg (le_of_lt hr0) N)]
        have h2 : r ^ N ≤ r := by
          have h1 : (1 : ℕ) ≤ N := hN
          have h3 := pow_le_pow_of_le_one (le_of_lt hr0) (le_of_lt hr1) h1
          simpa using h3
        linarith
      have hball : (r : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by
        rw [Metric.mem_ball, dist_zero_right]
        have hnorm : ‖(r : ℂ)‖ = r := by
          rw [show ‖(r : ℂ)‖ = |r| by simp, abs_of_pos hr0]
        rw [hnorm]
        exact hrρ
      -- The fibre of `polyOf F` at `s = r ^ N` is the complexification of `mpoly c (r ^ N)`.
      have hfac_r : Pz (polyOf F) ((r : ℂ) ^ N) = ∏ j, (X - C (η j (r : ℂ))) :=
        hfac (r : ℂ) hball
      have heval : (Pz (polyOf F) ((r : ℂ) ^ N)).eval (z : ℂ) = ∏ j, ((z : ℂ) - η j (r : ℂ)) := by
        rw [hfac_r, Polynomial.eval_prod]
        simp
      have heval2 : (Pz (polyOf F) ((r : ℂ) ^ N)).eval (z : ℂ) =
          ((WilkiesDesign.CG.C4a.mpoly c (r ^ N) z : ℝ) : ℂ) := by
        rw [← Complex.ofReal_pow]
        exact eval_Pz_polyOf_ofReal F c hFc hrpow_lt_ρF z
      have hkey : ((WilkiesDesign.CG.C4a.mpoly c (r ^ N) z : ℝ) : ℂ) =
          ∏ j, ((z : ℂ) - η j (r : ℂ)) := by
        rw [← heval2, heval]
      have hforall : ∀ j : Fin d, (good j → (η j (r : ℂ)).im = 0) ∧
          (¬ good j → (η j (r : ℂ)).im ≠ 0) := by
        have hh := hε r (by rw [abs_of_pos hr0]; exact hrε)
        intro j
        exact ⟨(hh j).1, fun hg => (hh j).2 hg (ne_of_gt hr0)⟩
      -- Only the `good` indices can contribute real values.
      have hA : (∃ j : Fin d, (z : ℂ) = η j (r : ℂ)) ↔
          ∃ j : Fin d, good j ∧ z = (η j (r : ℂ)).re := by
        constructor
        · rintro ⟨j, hj⟩
          have him0 : (η j (r : ℂ)).im = 0 := by rw [← hj]; simp
          have hgj : good j := by
            by_contra hneg
            exact (hforall j).2 hneg him0
          have hz : z = (η j (r : ℂ)).re := by
            have := congrArg Complex.re hj
            simpa using this
          exact ⟨j, hgj, hz⟩
        · rintro ⟨j, hg, hj⟩
          refine ⟨j, ?_⟩
          have him0 : (η j (r : ℂ)).im = 0 := (hforall j).1 hg
          have hre : η j (r : ℂ) = ((η j (r : ℂ)).re : ℂ) := by
            rw [← Complex.re_add_im (η j (r : ℂ)), him0]
            simp
          rw [hre, ← hj]
      -- Reindex the `good` indices by `Fin (card ι)`.
      have hB : (∃ j : Fin d, good j ∧ z = (η j (r : ℂ)).re) ↔
          ∃ i : Fin (Fintype.card ι), z = (η (e i).val (r : ℂ)).re := by
        constructor
        · rintro ⟨j, hg, hj⟩
          exact ⟨e.symm ⟨j, hg⟩, by simpa using hj⟩
        · rintro ⟨i, hi⟩
          exact ⟨(e i).val, (e i).property, hi⟩
      have hprod : (∏ j, ((z : ℂ) - η j (r : ℂ))) = 0 ↔ ∃ j : Fin d, (z : ℂ) = η j (r : ℂ) := by
        rw [Finset.prod_eq_zero_iff]
        constructor
        · rintro ⟨j, -, hj⟩
          exact ⟨j, sub_eq_zero.mp hj⟩
        · rintro ⟨j, hj⟩
          exact ⟨j, Finset.mem_univ j, sub_eq_zero.mpr hj⟩
      rw [← Complex.ofReal_eq_zero (z := WilkiesDesign.CG.C4a.mpoly c (r ^ N) z), hkey, hprod,
        hA, hB]

end Work.WilC4aP
