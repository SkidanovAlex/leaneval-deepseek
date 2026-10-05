import Mathlib
import Submission.Work.RPB.B3.EvenTaylorDefs
import Submission.Work.RPB.B3.stepOpApply
import Submission.Work.RPB.B2.paramIntegral_contDiff_inf

/-!
# The even Hadamard splitting of a smooth function of one variable

Let `f : ℝ → ℝ → ℝ → E` be smooth in all three variables and even in its last variable,
`f τ t (-r) = f τ t r`.  Then, for every `k : ℕ`, there are smooth functions
`c : Fin k → ℝ → ℝ → E` and a smooth remainder `R : ℝ → ℝ → ℝ → E` with

`f τ t r = ∑_{j<k} r ^ (2j) • c j τ t + r ^ (2k) • R τ t r`.

The construction is the *even Hadamard quotient*: for a smooth even `h` the increment
`h (p, r) - h (p, 0)` vanishes to order `2` at `r = 0`, so it may be divided by `r ^ 2`; the
quotient is exhibited as an explicit parametric integral,

`(h (p, r) - h (p, 0)) / r ^ 2 = evenStep h (p, r)`,
`evenStep h = stepOp (stepOp (Hsub h))`,   `stepOp h (p, r) = ∫_0^1 ∂_r h (p, r u) du`,

which is manifestly smooth (`Work.RPB.B2.paramIntegral_contDiff_inf`), and preserves evenness.
Iterating this `k` times produces the splitting.  The vocabulary is in
`Work.RPB.B3.EvenTaylorDefs`; here we redo the bookkeeping without the `2π`-periodicity that the
`Work.RPB.B3` development also tracks, and without its dependence on the temporary stand-ins in
`Work.RPB.B3.EvenTaylorStubs`.
-/

open scoped ContDiff
open scoped Interval

set_option linter.unusedSectionVars false

namespace Work.RPB.B5

open Work.RPB.B3.EvenTaylor

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Any finite order is below `∞` in the `ContDiff` scale. -/
theorem le_sm (n : ℕ) : (n : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

/-! ### The Hadamard quotient `stepOp` -/

/-- An even function `g : ℝ → E` has vanishing derivative at the origin. -/
theorem deriv_zero_of_even (g : ℝ → E) (hg : ∀ r, g (-r) = g r) : deriv g 0 = 0 := by
  have h2 : fderiv ℝ (fun r : ℝ => g (-r)) 0 = fderiv ℝ g 0 := by
    rw [show (fun r : ℝ => g (-r)) = g from funext hg]
  have h1 : fderiv ℝ (fun r : ℝ => g (-r)) 0 = - fderiv ℝ g 0 := by
    rw [← fderivWithin_univ (f := fun r : ℝ => g (-r)), fderivWithin_comp_neg]
    simp
  rw [h1] at h2
  have h3 : fderiv ℝ g 0 = 0 := by
    apply ContinuousLinearMap.ext_ring
    have hh := congrArg (fun M : ℝ →L[ℝ] E => M 1) h2
    simp only [neg_apply, zero_apply] at hh ⊢
    have hv : (2 : ℝ) • ((fderiv ℝ g 0) 1) = 0 := by
      have hvv : (fderiv ℝ g 0) 1 + (fderiv ℝ g 0) 1 = 0 := by
        have hc := neg_add_cancel ((fderiv ℝ g 0) 1)
        rwa [hh] at hc
      rwa [two_smul ℝ ((fderiv ℝ g 0) 1)]
    have hnorm : (2 : ℝ) * ‖(fderiv ℝ g 0) 1‖ = 0 := by
      have hc := congrArg norm hv
      simpa [norm_smul] using hc
    have : ‖(fderiv ℝ g 0) 1‖ = 0 := by linarith [norm_nonneg ((fderiv ℝ g 0) 1)]
    exact norm_eq_zero.mp this
  rw [show deriv g 0 = (fderiv ℝ g 0) 1 from rfl, h3]
  simp

/-- Smoothness of `Hsub h = h - h (·, 0)`. -/
theorem Hsub_contDiff (h : (ℝ × ℝ) × ℝ → E) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (Hsub h) := by
  unfold Hsub
  fun_prop

/-- `Hsub` vanishes at `r = 0`. -/
theorem Hsub_zero (h : (ℝ × ℝ) × ℝ → E) (p : ℝ × ℝ) : Hsub h (p, 0) = 0 := by
  simp [Hsub]

/-- `Hsub` preserves evenness in the last variable. -/
theorem Hsub_even (h : (ℝ × ℝ) × ℝ → E) (he : ∀ p r, h (p, -r) = h (p, r)) :
    ∀ p r, Hsub h (p, -r) = Hsub h (p, r) := by
  intro p r
  simp only [Hsub]
  rw [he p r]

/-- `stepOp` preserves smoothness.  This is the parametric integral of the partial derivative
`pdR h` over the unit interval `x ↦ ∫_0^1 pdR h (x.1, x.2 * u) du`, smooth by
`Work.RPB.B2.paramIntegral_contDiff_inf`. -/
theorem stepOp_contDiff (h : (ℝ × ℝ) × ℝ → E) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (stepOp h) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ h) := by
    apply hh.fderiv_right
    simp
  have hpd : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => pdR h z) := by
    unfold pdR
    exact hfd.clm_apply contDiff_const
  have hg : ContDiff ℝ ∞ (fun q : ℝ × ((ℝ × ℝ) × ℝ) => pdR h (q.2.1, q.2.2 * q.1)) := by
    have hφ : ContDiff ℝ ∞ (fun q : ℝ × ((ℝ × ℝ) × ℝ) => (q.2.1, q.2.2 * q.1)) := by
      fun_prop
    exact hpd.comp hφ
  have hres := Work.RPB.B2.paramIntegral_contDiff_inf
    (f := fun s (z : (ℝ × ℝ) × ℝ) => pdR h (z.1, z.2 * s)) (0 : ℝ) 1 hg
  change ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => ∫ s in (0 : ℝ)..1, pdR h (z.1, z.2 * s))
  exact hres

/-- The divided-difference identity for `stepOp`: for `C¹` `h`,
`h (z.1, z.2) - h (z.1, 0) = z.2 • stepOp h z`. -/
theorem stepOp_sub (h : (ℝ × ℝ) × ℝ → E) (hh : ContDiff ℝ 1 h) (z : (ℝ × ℝ) × ℝ) :
    h (z.1, z.2) - h (z.1, 0) = z.2 • stepOp h z :=
  Work.RPB.B3.stepOpApply h hh z

/-- The divided-difference identity for functions vanishing on `r = 0`. -/
theorem stepOp_apply_zero (h : (ℝ × ℝ) × ℝ → E) (hh : ContDiff ℝ 1 h)
    (h0 : ∀ p, h (p, 0) = 0) (z : (ℝ × ℝ) × ℝ) :
    h z = z.2 • stepOp h z := by
  have h' := stepOp_sub h hh z
  rw [h0 z.1, sub_zero] at h'
  simpa using h'

/-- `stepOp` of an even function vanishes at `r = 0`. -/
theorem stepOp_zero_of_even (h : (ℝ × ℝ) × ℝ → E) (hh : ContDiff ℝ 1 h)
    (he : ∀ p r, h (p, -r) = h (p, r)) (p : ℝ × ℝ) :
    stepOp h (p, 0) = 0 := by
  rw [stepOp_zero]
  rw [pdR_eq_deriv h p 0 hh.differentiable_one.differentiableAt]
  exact deriv_zero_of_even (fun s : ℝ => h (p, s)) (fun s => he p s)

/-! ### The even quotient `evenStep` -/

/-- Smoothness of the even quotient. -/
theorem evenStep_contDiff (h : (ℝ × ℝ) × ℝ → E) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (evenStep h) := by
  unfold evenStep
  exact stepOp_contDiff _ (stepOp_contDiff _ (Hsub_contDiff h hh))

/-- The even-quotient identity: for even `h`, `h(·,r) - h(·,0) = r² • evenStep h (·,r)`. -/
theorem evenStep_apply (h : (ℝ × ℝ) × ℝ → E) (hh : ContDiff ℝ ∞ h)
    (he : ∀ p r, h (p, -r) = h (p, r)) (p : ℝ × ℝ) (r : ℝ) :
    h (p, r) - h (p, 0) = r ^ 2 • evenStep h (p, r) := by
  have hH1 : ContDiff ℝ 1 (Hsub h) := (Hsub_contDiff h hh).of_le (le_sm 1)
  have hHs : ContDiff ℝ ∞ (Hsub h) := Hsub_contDiff h hh
  have h1 : Hsub h (p, r) = r • stepOp (Hsub h) (p, r) :=
    stepOp_apply_zero (Hsub h) hH1 (fun q => Hsub_zero h q) (p, r)
  have h2 : stepOp (Hsub h) (p, r) = r • evenStep h (p, r) := by
    have hb := stepOp_sub (stepOp (Hsub h)) ((stepOp_contDiff (Hsub h) hHs).of_le (le_sm 1))
      (p, r)
    rw [stepOp_zero_of_even (Hsub h) hH1 (Hsub_even h he) p, sub_zero] at hb
    simpa [evenStep] using hb
  calc h (p, r) - h (p, 0) = Hsub h (p, r) := by simp [Hsub]
    _ = r • stepOp (Hsub h) (p, r) := h1
    _ = r • (r • evenStep h (p, r)) := by rw [h2]
    _ = r ^ 2 • evenStep h (p, r) := by rw [smul_smul, sq]

/-- The even quotient of an even function is even. -/
theorem evenStep_even (h : (ℝ × ℝ) × ℝ → E) (hh : ContDiff ℝ ∞ h)
    (he : ∀ p r, h (p, -r) = h (p, r)) :
    ∀ p r, evenStep h (p, -r) = evenStep h (p, r) := by
  intro p r
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · have h1 := evenStep_apply h hh he p r
    have h2 := evenStep_apply h hh he p (-r)
    rw [he p r, neg_sq] at h2
    have h3 : r ^ 2 • evenStep h (p, -r) = r ^ 2 • evenStep h (p, r) := by rw [← h2, h1]
    have h4 := congrArg (fun y => (r ^ 2)⁻¹ • y) h3
    simpa [inv_smul_smul₀ (pow_ne_zero 2 hr)] using h4

/-! ### The iterated even quotient `chi` -/

theorem chi_succ (f : (ℝ × ℝ) × ℝ → E) (n : ℕ) : chi f (n + 1) = evenStep (chi f n) := by
  rw [chi, chi, Function.iterate_succ_apply']

theorem chi_even_contDiff (f : (ℝ × ℝ) × ℝ → E) (hf : ContDiff ℝ ∞ f)
    (he : ∀ p r, f (p, -r) = f (p, r)) (n : ℕ) :
    (∀ p r, chi f n (p, -r) = chi f n (p, r)) ∧ ContDiff ℝ ∞ (chi f n) := by
  induction n with
  | zero => exact ⟨by simpa [chi] using he, by simpa [chi] using hf⟩
  | succ n ih =>
    rw [chi_succ]
    exact ⟨evenStep_even (chi f n) ih.2 ih.1, evenStep_contDiff (chi f n) ih.2⟩

theorem chi_even (f : (ℝ × ℝ) × ℝ → E) (hf : ContDiff ℝ ∞ f)
    (he : ∀ p r, f (p, -r) = f (p, r)) (n : ℕ) :
    ∀ p r, chi f n (p, -r) = chi f n (p, r) := (chi_even_contDiff f hf he n).1

theorem chi_contDiff (f : (ℝ × ℝ) × ℝ → E) (hf : ContDiff ℝ ∞ f)
    (he : ∀ p r, f (p, -r) = f (p, r)) (n : ℕ) :
    ContDiff ℝ ∞ (chi f n) := (chi_even_contDiff f hf he n).2

/-- The iterated decomposition:
`f (p,r) = ∑_{i<n} r^{2i} • chi f i (p,0) + r^{2n} • chi f n (p,r)`. -/
theorem chi_decomp (f : (ℝ × ℝ) × ℝ → E) (hf : ContDiff ℝ ∞ f)
    (he : ∀ p r, f (p, -r) = f (p, r)) (n : ℕ) :
    ∀ p r, f (p, r) = (∑ i ∈ Finset.range n, r ^ (2 * i) • chi f i (p, 0))
      + r ^ (2 * n) • chi f n (p, r) := by
  induction n with
  | zero => intro p r; simp [chi]
  | succ n ih =>
    intro p r
    have hE := evenStep_apply (chi f n) (chi_contDiff f hf he n) (chi_even f hf he n) p r
    rw [sub_eq_iff_eq_add] at hE
    rw [add_comm] at hE
    rw [ih p r, Finset.sum_range_succ, chi_succ, hE, smul_add, smul_smul, ← pow_add,
      show (2 : ℕ) * (n + 1) = 2 * n + 2 from by ring, add_assoc, add_right_inj]

/-! ### The splitting -/

theorem evenHadamardSplit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → ℝ → ℝ → E) (k : ℕ)
    (hf : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun z : ℝ × (ℝ × ℝ) => f z.1 z.2.1 z.2.2))
    (heven : ∀ τ t r, f τ t (-r) = f τ t r) :
    ∃ (c : Fin k → ℝ → ℝ → E) (R : ℝ → ℝ → ℝ → E),
      (∀ j, ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun z : ℝ × ℝ => c j z.1 z.2)) ∧
      ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun z : ℝ × (ℝ × ℝ) => R z.1 z.2.1 z.2.2) ∧
      ∀ τ t r, f τ t r = (∑ j : Fin k, r ^ (2 * (j : ℕ)) • c j τ t) + r ^ (2 * k) • R τ t r := by
  classical
  let F : (ℝ × ℝ) × ℝ → E := fun z => f z.1.1 z.1.2 z.2
  have hF : ContDiff ℝ ∞ F := by
    have hcomp : F = (fun z : ℝ × (ℝ × ℝ) => f z.1 z.2.1 z.2.2) ∘
        (fun z : (ℝ × ℝ) × ℝ => (z.1.1, (z.1.2, z.2))) := rfl
    rw [hcomp]
    exact hf.comp (by fun_prop)
  have hFeven : ∀ p r, F (p, -r) = F (p, r) := by
    intro p r
    exact heven p.1 p.2 r
  let c : Fin k → ℝ → ℝ → E := fun j τ t => chi F (j : ℕ) ((τ, t), 0)
  let R : ℝ → ℝ → ℝ → E := fun τ t r => chi F k ((τ, t), r)
  refine ⟨c, R, ?_, ?_, ?_⟩
  · intro j
    have hchi : ContDiff ℝ ∞ (chi F (j : ℕ)) := chi_contDiff F hF hFeven (j : ℕ)
    have hφ : ContDiff ℝ ∞ (fun z : ℝ × ℝ => ((z.1, z.2), (0 : ℝ))) := by fun_prop
    exact hchi.comp hφ
  · have hchi : ContDiff ℝ ∞ (chi F k) := chi_contDiff F hF hFeven k
    have hφ : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => ((z.1, z.2.1), z.2.2)) := by fun_prop
    exact hchi.comp hφ
  · intro τ t r
    have hdec := chi_decomp F hF hFeven k (τ, t) r
    simp only [c, R]
    rw [show f τ t r = F ((τ, t), r) from rfl, hdec,
      ← Fin.sum_univ_eq_sum_range (fun i : ℕ => r ^ (2 * i) • chi F i ((τ, t), 0)) k]

end

end Work.RPB.B5
