import Mathlib
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.mfun_props

/-!
# C8 (Kotani theory): assembly

This file assembles the frozen `Work.TMContract.P_Kotani` from the "core" statement produced
by the extension argument (the analytic continuation of the `m`-function across `(a,b)`,
glued into a continuous `ℍ`-valued function on `kotaniDomain a b`).

`prove_Kotani_of_core` extends the core function to a total function of `(z,x)` by the
reflection formula off the domain: the 1-periodicity in `x` is then automatic outside the
domain, while on the domain it follows from continuity on the domain together with the
density of the off-axis points (`dense_offAxis`, `eqOn_of_dense_of_continuousOn`).
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Kotani

open Work.TMContract

/-- The core statement produced by the extension argument. -/
def CoreStatement (α lam a b : ℝ) : Prop :=
  ∃ M : ℂ → ℝ → ℂ,
    ContinuousOn (fun p : ℂ × ℝ => M p.1 p.2) (kotaniDomain a b ×ˢ Set.univ) ∧
    (∀ z ∈ kotaniDomain a b, ∀ x : ℝ, 0 < (M z x).im) ∧
    (∀ E : ℂ, 0 < E.im → ∀ x : ℝ, M E x = mfun α lam E x) ∧
    (∀ E : ℂ, E.im < 0 → ∀ x : ℝ,
      M E x = 1 / star (mfun α lam (star E) (α - x))) ∧
    (∀ x : ℝ, DifferentiableOn ℂ (fun z : ℂ => M z x) (kotaniDomain a b))

/-- The off-axis points are dense in `kotaniDomain a b`. -/
theorem dense_offAxis (a b : ℝ) :
    kotaniDomain a b ⊆ closure {z : ℂ | z ∈ kotaniDomain a b ∧ z.im ≠ 0} := by
  intro z hz
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases eq_or_ne z.im 0 with him | him
  · refine ⟨z + ((ε / 2 : ℝ) : ℂ) * Complex.I, ⟨?_, ?_⟩, ?_⟩
    · unfold kotaniDomain
      left
      have h : (z + ((ε / 2 : ℝ) : ℂ) * Complex.I).im = ε / 2 := by
        simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, him]
      rw [h]; exact ne_of_gt (by linarith)
    · have h : (z + ((ε / 2 : ℝ) : ℂ) * Complex.I).im = ε / 2 := by
        simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, him]
      rw [h]; exact ne_of_gt (by linarith)
    · rw [dist_eq_norm,
        show z - (z + ((ε / 2 : ℝ) : ℂ) * Complex.I) = -(((ε / 2 : ℝ) : ℂ) * Complex.I) by ring]
      rw [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
  · exact ⟨z, ⟨hz, him⟩, by simpa using hε⟩

/-- Two functions continuous on a set `s` which agree on a subset `t` that is dense in `s`
agree on `s`. -/
theorem eqOn_of_dense_of_continuousOn {X : Type*} [PseudoMetricSpace X] {f g : X → ℂ}
    {s t : Set X} (hf : ContinuousOn f s) (hg : ContinuousOn g s) (hts : t ⊆ s)
    (hst : s ⊆ closure t) (h : EqOn f g t) : EqOn f g s := by
  intro z hz
  have hzcl : z ∈ closure t := hst hz
  rw [Metric.mem_closure_iff] at hzcl
  have hseq : ∀ n : ℕ, ∃ y ∈ t, dist z y < 1 / (n + 1) :=
    fun n => hzcl (1 / (n + 1)) (by positivity)
  choose y hy using hseq
  have hyz : Tendsto y atTop (𝓝 z) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [dist_comm]; exact le_of_lt (hy n).2
  have hys : Tendsto y atTop (𝓝[s] z) :=
    tendsto_nhdsWithin_iff.mpr ⟨hyz, Filter.Eventually.of_forall fun n => hts (hy n).1⟩
  have h1 : Tendsto (fun n => f (y n)) atTop (𝓝 (f z)) :=
    (hf.continuousWithinAt hz).tendsto.comp hys
  have h2 : Tendsto (fun n => g (y n)) atTop (𝓝 (g z)) :=
    (hg.continuousWithinAt hz).tendsto.comp hys
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  exact Filter.Eventually.of_forall fun n => (h (hy n).1).symm

/-- **Assembly.**  From the core extension statement, the frozen `P_Kotani` follows. -/
theorem prove_Kotani_of_core
    (hcore : ∀ α lam a b : ℝ, Irrational α → 0 ≤ lam → a < b →
      (∀ E ∈ Set.Ioo a b, lyap α lam (E : ℂ) = 0) → CoreStatement α lam a b) :
    Work.TMContract.P_Kotani := by
  classical
  intro α lam a b hα h0 hab hL
  obtain ⟨M₀, hcont, him, hup, hdown, hdiff⟩ := hcore α lam a b hα h0 hab hL
  have hmpos : ∀ E : ℂ, 0 < E.im → ∀ x : ℝ, 0 < (mfun α lam E x).im :=
    fun E hE x => (mfun_props α lam).2.1 E hE x
  have hamo : ∀ E : ℂ, 0 < E.im → ∀ x : ℝ, mfun α lam E x = amoM α lam E x :=
    fun E hE x => (mfun_props α lam).2.2.1 E hE x
  have hper : ∀ (E : ℂ) (x : ℝ), mfun α lam E (x + 1) = mfun α lam E x :=
    fun E x => (mfun_props α lam).2.2.2.2.2.2 E x
  refine ⟨fun z x => if z ∈ kotaniDomain a b then M₀ z x
      else 1 / star (mfun α lam (star z) (α - x)), ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity on the domain
    refine hcont.congr ?_
    rintro ⟨z, x⟩ hp
    simp only [Set.mem_prod, Set.mem_univ, and_true] at hp
    simp only [if_pos hp]
  · -- differentiability in `E` on the domain
    intro x
    refine (hdiff x).congr ?_
    intro z hz
    simp only [if_pos hz]
  · -- positivity of the imaginary part on the domain
    intro z hz x
    simp only [if_pos hz]
    exact him z hz x
  · -- agreement with `amoM` on the upper half plane
    intro z hz x
    have hzdom : z ∈ kotaniDomain a b := by
      unfold kotaniDomain; exact Or.inl (ne_of_gt hz)
    simp only [if_pos hzdom]
    exact (hup z hz x).trans (hamo z hz x)
  · -- 1-periodicity in `x`
    intro z x
    have hshift : ∀ u : ℂ, mfun α lam (star u) (α - (x + 1)) = mfun α lam (star u) (α - x) := by
      intro u
      rw [show α - (x + 1) = (α - x) - 1 by ring, ← hper (star u) (α - x - 1),
        show (α - x - 1) + 1 = α - x by ring]
    by_cases hzdom : z ∈ kotaniDomain a b
    · have h1 : ContinuousOn (fun w : ℂ => M₀ w (x + 1)) (kotaniDomain a b) :=
        hcont.comp (by fun_prop : Continuous fun w : ℂ => (w, x + 1)).continuousOn
          (fun w hw => ⟨hw, Set.mem_univ _⟩)
      have h2 : ContinuousOn (fun w : ℂ => M₀ w x) (kotaniDomain a b) :=
        hcont.comp (by fun_prop : Continuous fun w : ℂ => (w, x)).continuousOn
          (fun w hw => ⟨hw, Set.mem_univ _⟩)
      have hoff : EqOn (fun w : ℂ => M₀ w (x + 1)) (fun w : ℂ => M₀ w x)
          {w : ℂ | w ∈ kotaniDomain a b ∧ w.im ≠ 0} := by
        intro w hw
        rcases lt_or_gt_of_ne hw.2 with hlt | hgt
        · simp only [hdown w hlt (x + 1), hdown w hlt x, hshift w]
        · simp only [hup w hgt (x + 1), hup w hgt x, hper w x]
      simp only [if_pos hzdom]
      exact eqOn_of_dense_of_continuousOn h1 h2 (fun w hw => hw.1) (dense_offAxis a b)
        hoff hzdom
    · simp only [if_neg hzdom, hshift z]

end Work.TMComp.Kotani
