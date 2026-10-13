/-
  Work.WilC4aAL.Basic

  Foundational lemmas for area C4a-AL ("analytic sign selection on analytic branches"):
  the sign of a real-analytic function is eventually constant on the right of `0`, a
  continuous function with no zero between two points has the same sign there, the functions
  `z ↦ mpoly c s z` are continuous and analytic in the parameter, and analytic branches are
  bounded near `0`.

  Everything here is used by `Work.WilC4aAL.analytic_sign_selection` (the cell-selection
  lemma) and by `Work.WilC4aAL.C4a_arcLift_proved`.
-/
import Submission.Work.WilC4aAL.Defs

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilC4aAL
open WilkiesDesign.CG.C4a

/-! ## 1. Filters on the right of `0` -/

/-- `∀ᶠ r in 𝓝[>] 0, P r` is the same as `P` holding on an interval `(0, ε)`. -/
theorem eventually_nhdsGT_iff_eps {P : ℝ → Prop} :
    (∀ᶠ r in 𝓝[>] (0 : ℝ), P r) ↔ ∃ ε > (0 : ℝ), ∀ r ∈ Set.Ioo (0 : ℝ) ε, P r := by
  constructor
  · intro h
    obtain ⟨ε, hε, hsub⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp h
    exact ⟨ε, hε, fun r hr => hsub hr⟩
  · rintro ⟨ε, hε, h⟩
    exact mem_of_superset (Ioo_mem_nhdsGT hε) h

/-! ## 2. Signs of real-analytic functions -/

/-- A continuous function with no zero strictly between `a ≤ b` and non-zero at the endpoints
has the same sign at `a` and at `b`. -/
theorem sign_eq_of_no_zero_between {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ∀ x ∈ Set.Icc a b, ContinuousAt f x)
    (hzero : ∀ x ∈ Set.Ioo a b, f x ≠ 0) (ha : f a ≠ 0) (hb : f b ≠ 0) :
    SignType.sign (f a) = SignType.sign (f b) := by
  rcases eq_or_lt_of_le hab with rfl | hab'
  · rfl
  have hc : ContinuousOn f (Set.Icc a b) := fun x hx => (hcont x hx).continuousWithinAt
  rcases lt_trichotomy (f a) 0 with hlt | heq | hgt
  · have hb' : f b < 0 := by
      by_contra hle
      rw [not_lt] at hle
      obtain ⟨c, hmem, hfc⟩ := intermediate_value_Icc hab hc ⟨hlt.le, hle⟩
      exact hzero c ⟨lt_of_le_of_ne hmem.1 (fun h : a = c => ha (h ▸ hfc)),
        lt_of_le_of_ne hmem.2 (fun h : c = b => hb (h ▸ hfc))⟩ hfc
    rw [sign_neg hlt, sign_neg hb']
  · exact absurd heq ha
  · have hb' : 0 < f b := by
      by_contra hle
      rw [not_lt] at hle
      have hb'' : f b < 0 := lt_of_le_of_ne hle (fun h : f b = 0 => hb h)
      obtain ⟨c, hmem, hfc⟩ := intermediate_value_Icc' hab hc ⟨hb''.le, hgt.le⟩
      exact hzero c ⟨lt_of_le_of_ne hmem.1 (fun h : a = c => ha (h ▸ hfc)),
        lt_of_le_of_ne hmem.2 (fun h : c = b => hb (h ▸ hfc))⟩ hfc
    rw [sign_pos hgt, sign_pos hb']

/-- **The sign of a real-analytic function is eventually constant on the right of `0`.** -/
theorem sign_eventually_const {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∃ ε > (0 : ℝ), ∃ s : SignType, ∀ r ∈ Set.Ioo (0 : ℝ) ε, SignType.sign (f r) = s := by
  have key : ∃ s : SignType, ∀ᶠ r in 𝓝[>] (0 : ℝ), SignType.sign (f r) = s := by
    rcases hf.eventually_eq_zero_or_eventually_ne_zero with h | h
    · refine ⟨0, ?_⟩
      filter_upwards [nhdsWithin_le_nhds h] with r hr
      rw [sign_eq_zero_iff.mpr hr]
    · have h' : ∀ᶠ r in 𝓝[>] (0 : ℝ), f r ≠ 0 :=
        (nhdsWithin_mono (0 : ℝ) (fun y hy => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt hy)) h
      obtain ⟨e, he, hene⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp h'
      obtain ⟨d, hd, hdan⟩ := Metric.eventually_nhds_iff.mp hf.eventually_analyticAt
      refine ⟨SignType.sign (f (min (e / 2) (d / 2))), ?_⟩
      rw [eventually_nhdsGT_iff_eps]
      refine ⟨min (e / 2) (d / 2), lt_min (half_pos he) (half_pos hd), ?_⟩
      intro r hr
      have hmpos : 0 < min (e / 2) (d / 2) := lt_min (half_pos he) (half_pos hd)
      have hmem : min (e / 2) (d / 2) ∈ Set.Ioo (0 : ℝ) e :=
        ⟨hmpos, lt_of_le_of_lt (min_le_left _ _) (half_lt_self he)⟩
      have hre : r ∈ Set.Ioo (0 : ℝ) e :=
        ⟨hr.1, lt_trans hr.2 (lt_of_le_of_lt (min_le_left _ _) (half_lt_self he))⟩
      refine sign_eq_of_no_zero_between hr.2.le ?_ ?_ (hene hre) (hene hmem)
      · intro x hx
        have hx0 : 0 < x := lt_of_lt_of_le hr.1 hx.1
        have hxd : |x| < d := by
          rw [abs_of_pos hx0]
          exact lt_of_le_of_lt (hx.2.trans (min_le_right _ _)) (half_lt_self hd)
        exact (hdan (by simpa [Real.dist_eq] using hxd)).continuousAt
      · intro x hx
        exact hene ⟨lt_trans hr.1 hx.1,
          lt_trans hx.2 (lt_of_le_of_lt (min_le_left _ _) (half_lt_self he))⟩
  obtain ⟨s, hs⟩ := key
  exact eventually_nhdsGT_iff_eps.mp hs |> fun ⟨e, he, h⟩ => ⟨e, he, s, h⟩

/-- Filter form of `sign_eventually_const`. -/
theorem eventually_sign_const_of_analytic {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∃ s : SignType, ∀ᶠ r in 𝓝[>] (0 : ℝ), SignType.sign (f r) = s := by
  obtain ⟨ε, hε, s, hs⟩ := sign_eventually_const hf
  exact ⟨s, mem_of_superset (Ioo_mem_nhdsGT hε) fun r hr => hs r hr⟩

/-! ## 3. Analyticity of the `mpoly` family -/

/-- `z ↦ mpoly c s z` is continuous. -/
theorem continuous_mpoly_right {d : ℕ} (c : Fin d → ℝ → ℝ) (s : ℝ) :
    Continuous fun z : ℝ => mpoly c s z := by
  simp only [mpoly]
  exact (continuous_id.pow d).add
    (continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_id.pow _)))

/-- Substituting an analytic function for `z` in `mpoly` keeps analyticity at `0`
(the parameter is the same variable). -/
theorem analyticAt_mpoly_comp {d : ℕ} {c : Fin d → ℝ → ℝ} (hc : ∀ j, AnalyticAt ℝ (c j) 0)
    {ρ : ℝ → ℝ} (hρ : AnalyticAt ℝ ρ 0) :
    AnalyticAt ℝ (fun r => mpoly c r (ρ r)) 0 := by
  simp only [mpoly]
  refine (hρ.pow d).add ?_
  simpa [Finset.sum_fn] using
    (Finset.analyticAt_sum Finset.univ (fun j _ => (hc j).mul (hρ.pow _)))

/-- Composing an analytic function at `0` with `r ↦ r ^ N` (`N ≠ 0`) stays analytic at `0`. -/
theorem analyticAt_comp_pow {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) {N : ℕ} (hN : 0 < N) :
    AnalyticAt ℝ (fun r => f (r ^ N)) 0 := by
  have hpow : AnalyticAt ℝ (fun r : ℝ => r ^ N) 0 := analyticAt_id.pow N
  have h0 : (fun r : ℝ => r ^ N) 0 = 0 := by simp [zero_pow hN.ne']
  have hf' : AnalyticAt ℝ f ((fun r : ℝ => r ^ N) 0) := by rw [h0]; exact hf
  have hcomp : AnalyticAt ℝ (fun r => f ((fun r : ℝ => r ^ N) r)) 0 :=
    AnalyticAt.comp (x := (0 : ℝ)) hf' hpow
  exact hcomp

/-- If every coefficient of the family vanishes at the parameter value `0`, the polynomial
degenerates to `z ^ d` there. -/
theorem mpoly_zero_of_coeffs_zero {d : ℕ} {c : Fin d → ℝ → ℝ} (hc : ∀ j, c j 0 = 0) (z : ℝ) :
    mpoly c 0 z = z ^ d := by
  simp only [mpoly]
  simp [hc]

/-! ## 4. Analytic branches are bounded near `0` -/

/-- Finitely many branches analytic at `0` are bounded on a right-neighbourhood of `0`. -/
theorem exists_bound_of_analytic {ι : Type*} [Fintype ι] (ξ : ι → ℝ → ℝ)
    (hξ : ∀ t, AnalyticAt ℝ (ξ t) 0) :
    ∃ C : ℝ, ∃ ε > (0 : ℝ), ∀ r ∈ Set.Ioo (0 : ℝ) ε, ∀ t, |ξ t r| < C := by
  have hδ : ∀ t : ι, ∃ δ > (0 : ℝ), ∀ r : ℝ, |r| < δ → |ξ t r| < |ξ t 0| + 1 := by
    intro t
    have ht : {r : ℝ | dist (ξ t r) (ξ t 0) < 1} ∈ 𝓝 (0 : ℝ) :=
      (hξ t).continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ one_pos)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_nhds_iff.mp ht
    exact ⟨δ, hδ, fun r hr => by
      have h1 : dist (ξ t r) (ξ t 0) < 1 := by
        have := hδ' (by rw [Metric.mem_ball, Real.dist_eq]; simpa using hr)
        simpa only [Set.mem_ofPred_eq] using this
      rw [Real.dist_eq] at h1
      have h2 : |ξ t r| ≤ |ξ t r - ξ t 0| + |ξ t 0| := by
        simpa using abs_add_le (ξ t r - ξ t 0) (ξ t 0)
      linarith⟩
  choose δ hδpos hδle using hδ
  by_cases hne : (Finset.univ.image δ).Nonempty
  · refine ⟨1 + ∑ t, (|ξ t 0| + 1), (Finset.univ.image δ).min' hne, ?_, ?_⟩
    · obtain ⟨t, _, ht⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne)
      rw [← ht]; exact hδpos t
    · intro r hr t
      have hrδ : |r| < δ t := by
        rw [abs_of_pos hr.1]
        exact lt_of_lt_of_le hr.2
          (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩))
      have h1 : |ξ t r| < |ξ t 0| + 1 := hδle t r hrδ
      have h2 : |ξ t 0| + 1 ≤ ∑ i, (|ξ i 0| + 1) :=
        Finset.single_le_sum (f := fun i => |ξ i 0| + 1) (fun i _ => by positivity)
          (Finset.mem_univ t)
      linarith
  · refine ⟨1, 1, one_pos, ?_⟩
    intro r hr t
    exact (hne ⟨δ t, Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩⟩).elim

/-! ## 5. The cell representatives `cand` -/

@[simp] theorem cand_inl {ι : Type*} (ξ : ι → ℝ → ℝ) (C : ℝ) (t u : ι) :
    cand ξ C (Sum.inl (t, u)) = fun r => (ξ t r + ξ u r) / 2 := rfl

@[simp] theorem cand_inr_true {ι : Type*} (ξ : ι → ℝ → ℝ) (C : ℝ) :
    cand ξ C (Sum.inr true) = fun _ => C := rfl

@[simp] theorem cand_inr_false {ι : Type*} (ξ : ι → ℝ → ℝ) (C : ℝ) :
    cand ξ C (Sum.inr false) = fun _ => -C := rfl

/-- The cell representatives built from analytic branches and a constant are analytic at `0`. -/
theorem analyticAt_cand {ι : Type*} {ξ : ι → ℝ → ℝ} (hξ : ∀ t, AnalyticAt ℝ (ξ t) 0)
    (C : ℝ) (j : CandIdx ι) : AnalyticAt ℝ (cand ξ C j) 0 := by
  cases j with
  | inl tu =>
    obtain ⟨t, u⟩ := tu
    exact (hξ t).add (hξ u) |>.div analyticAt_const two_ne_zero
  | inr b =>
    cases b <;> exact analyticAt_const

/-- For each cell representative `j`, the sign vector of the family `mpoly (c i) r ·` evaluated
at `cand ξ C j` is eventually constant on the right of `0`. -/
theorem eventually_signVector_of_cand {k : ℕ} {d : Fin k → ℕ} {c : ∀ i, Fin (d i) → ℝ → ℝ}
    (hc : ∀ i j, AnalyticAt ℝ (c i j) 0) {ι : Type*} {ξ : ι → ℝ → ℝ}
    (hξ : ∀ t, AnalyticAt ℝ (ξ t) 0) (C : ℝ) (j : CandIdx ι) :
    ∃ σ' : Fin k → SignType, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ i,
      SignType.sign (mpoly (c i) r (cand ξ C j r)) = σ' i := by
  have h : ∀ i, ∃ s : SignType, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      SignType.sign (mpoly (c i) r (cand ξ C j r)) = s := fun i =>
    eventually_sign_const_of_analytic (analyticAt_mpoly_comp (hc i) (analyticAt_cand hξ C j))
  choose σ' hσ' using h
  exact ⟨σ', Filter.eventually_all.mpr hσ'⟩

/-! ## 6. Same-sign bookkeeping -/

theorem SameSign.refl {k : ℕ} {d : Fin k → ℕ} (c : ∀ i, Fin (d i) → ℝ → ℝ) (r z : ℝ) :
    SameSign c r z z := fun _ => rfl

theorem SameSign.symm {k : ℕ} {d : Fin k → ℕ} {c : ∀ i, Fin (d i) → ℝ → ℝ} {r z z' : ℝ}
    (h : SameSign c r z z') : SameSign c r z' z := fun i => (h i).symm

theorem SameSign.trans {k : ℕ} {d : Fin k → ℕ} {c : ∀ i, Fin (d i) → ℝ → ℝ} {r z z' z'' : ℝ}
    (h₁ : SameSign c r z z') (h₂ : SameSign c r z' z'') : SameSign c r z z'' :=
  fun i => (h₁ i).trans (h₂ i)

/-- A sign vector realised at `z` is also realised at any `z'` with the same sign vector. -/
theorem SignVectorOk.of_sameSign {k : ℕ} {d : Fin k → ℕ} {c : ∀ i, Fin (d i) → ℝ → ℝ}
    {σ : Fin k → SignType} {r z z' : ℝ} (h : SameSign c r z z') (hz : SignVectorOk c σ r z) :
    SignVectorOk c σ r z' := fun i => (h i).symm.trans (hz i)

end Work.WilC4aAL
