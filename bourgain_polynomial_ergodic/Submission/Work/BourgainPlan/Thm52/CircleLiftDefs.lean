import Mathlib
import Submission.Work.BourgainPlan.Thm52.decimatedKernel_lp

/-!
# The fundamental-domain lift of a circle symbol

The sampling principle of KMSZ Definition 5.1(3)
(`Work.BourgainPlan.Thm52.sampling_principle_variation_decimated_kernel` and its `ℓᵖ`-form
`sampling_principle_variation_decimated_lp`) applies to a symbol `m : ℝ → ℂ` which is
**integrable** and **supported in the single interval** `Icc (-1/(2Q)) (1/(2Q))`.

When the symbol is the *periodisation* of a circle function `f : Circ → ℂ` — i.e. when it is the
function `x ↦ f (-(x : Circ))`, which is what the decimated-kernel bridge
`Work.BourgainPlan.Thm52.opArcW_eq_decimatedKernel_comp` produces — then neither hypothesis can
hold: a non-zero `1`-periodic function is not integrable on `ℝ`, and its support meets every period
of `ℝ`, so it is not contained in a single interval of length `1/Q`.

The correct object is therefore the **fundamental-domain lift**

`circleLift f x = if x ∈ Ioc (-1/2) (1/2] then f (-(x : Circ)) else 0`,

which agrees with the periodisation on the fundamental domain `Ioc (-1/2) (1/2]` (a.e. on the
interval of integration `(-1/2, 1/2)` of the decimated kernel) and vanishes outside it.  It is
integrable as soon as `f` is essentially bounded, and it is supported in the ball of radius `a`
whenever `f` is; and — crucially — it has the *same decimated kernel* as the periodisation, so all
the identities of `opArcW_eq_decimatedKernel_comp` remain valid.

## Contents

* `circleLift`, with its two evaluation lemmas;
* `decimatedKernel_circleLift` — the lift has the same decimated kernel as the periodisation;
* `circleLift_eq_zero_of_support` — the lift of a symbol supported in the ball of radius `a` is
  supported in `Icc (-a) a`;
* `coe_add_natCast` — `((x + n : ℝ) : Circ) = (x : Circ)` for `n : ℕ` (the periodicity of the
  covering map, used by the vacuity lemma below);
* **`eq_zero_of_forall_notMem_Icc_neg_coe`** — the vacuity lemma: if the *periodisation*
  `x ↦ f (-(x : Circ))` vanished off a *single* interval `Icc (-a) a` with `0 < a ≤ 1/2`, then `f`
  would vanish identically.  This documents precisely why the hypotheses of
  `largeScaleBoundF_opArcW_of_sampling` (which asked for `Integrable` and for the support of the
  periodisation) are unsatisfiable for a non-zero symbol, and why the lift above is the correct
  object.
-/

open MeasureTheory
open Set
open scoped BigOperators Interval ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Thm52

open Work.BourgainPlan.IonescuWainger

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

noncomputable section

/-- The **fundamental-domain lift** of a circle function, in the convention of
`Work.BourgainPlan.Thm52.decimatedKernel`: `x ↦ f (-(x : Circ))` on `Ioc (-1/2) (1/2]`, and `0`
outside. -/
def circleLift (f : Circ → ℂ) : ℝ → ℂ :=
  fun x => if x ∈ Set.Ioc (-(1/2 : ℝ)) (1/2) then f (-(x : Circ)) else 0

@[simp] lemma circleLift_of_mem {f : Circ → ℂ} {x : ℝ}
    (hx : x ∈ Set.Ioc (-(1/2 : ℝ)) (1/2)) : circleLift f x = f (-(x : Circ)) := by
  simp only [circleLift, if_pos hx]

@[simp] lemma circleLift_of_notMem {f : Circ → ℂ} {x : ℝ}
    (hx : x ∉ Set.Ioc (-(1/2 : ℝ)) (1/2)) : circleLift f x = 0 := by
  simp only [circleLift, if_neg hx]

/-- **The lift has the same decimated kernel as the periodisation.**  The decimated kernel
`decimatedKernel Q m j = Q [Q ∣ j] ∫_{(-1/2)}^{(1/2)} m ξ e^{2πijξ} dξ` only sees the values of `m`
on the interval `(-1/2, 1/2)`, where `circleLift f` agrees with the periodic function
`x ↦ f (-(x : Circ))`. -/
lemma decimatedKernel_circleLift (Q : ℕ) (f : Circ → ℂ) (j : ℤ) :
    decimatedKernel Q (circleLift f) j
      = decimatedKernel Q (fun x : ℝ => f (-(x : Circ))) j := by
  unfold decimatedKernel
  by_cases h : (Q : ℤ) ∣ j
  · rw [if_pos h, if_pos h]
    congr 1
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x hx
    rw [uIoc_of_le (by norm_num : (-(1/2) : ℝ) ≤ 1/2)] at hx
    rw [circleLift_of_mem hx]
  · rw [if_neg h, if_neg h]

/-- **The lift of a symbol supported in the ball of radius `a` is supported in `Icc (-a) a`.**  On
the fundamental domain the norm of `-(x : Circ)` is `|x|`, so the circle-support hypothesis
transfers verbatim. -/
lemma circleLift_eq_zero_of_support {f : Circ → ℂ} {a : ℝ}
    (hf : ∀ ξ : Circ, a < ‖ξ‖ → f ξ = 0) :
    ∀ x : ℝ, x ∉ Set.Icc (-a) a → circleLift f x = 0 := by
  intro x hx
  by_cases hx1 : x ∈ Set.Ioc (-(1/2 : ℝ)) (1/2)
  · rw [circleLift_of_mem hx1]
    refine hf _ ?_
    have hxnorm : ‖(x : Circ)‖ = |x| := by
      refine (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero (x := x)).mpr ?_
      simpa using abs_le.mpr ⟨le_of_lt hx1.1, hx1.2⟩
    rw [norm_neg, hxnorm]
    exact not_le.mp fun h => hx (abs_le.mp h)
  · exact circleLift_of_notMem hx1

/-- The covering map `ℝ → AddCircle 1` is `ℕ`-periodic: `((x + n : ℝ) : Circ) = (x : Circ)`. -/
lemma coe_add_natCast (x : ℝ) (n : ℕ) : ((x + (n : ℝ) : ℝ) : Circ) = (x : Circ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcast : x + ((n + 1 : ℕ) : ℝ) = (x + (n : ℝ)) + 1 := by push_cast; ring
    rw [hcast, AddCircle.coe_add_period, ih]

/-- **The vacuity lemma.**  If the *periodisation* of a circle function `f`, namely
`x ↦ f (-(x : Circ))`, vanishes outside the single interval `Icc (-a) a` with `0 < a ≤ 1/2`, then
`f` vanishes identically (in particular, the periodisation is not integrable unless it is zero).

This is why the hypotheses `hIntR`/`hsuppR` of
`Work.BourgainPlan.Thm52.largeScaleBoundF_opArcW_of_sampling` cannot be met by a non-zero symbol:
`Integrable` of a non-zero periodic function is false, and the support condition below already
forces the symbol to vanish.  The correct object is `circleLift`. -/
theorem eq_zero_of_forall_notMem_Icc_neg_coe {f : Circ → ℂ} {a : ℝ} (ha : 0 < a)
    (ha2 : a ≤ 1/2) (h : ∀ x : ℝ, x ∉ Set.Icc (-a) a → f (-(x : Circ)) = 0) : f = 0 := by
  funext ξ
  -- write `ξ` canonically as `(x : Circ)` with `x ∈ Icc (-1/2) (1/2)`
  obtain ⟨x, hxI, hxξ⟩ : ∃ x : ℝ, x ∈ Set.Icc (-(1/2) : ℝ) (1/2) ∧ (x : Circ) = ξ := by
    have hsurj : ((↑) : ℝ → Circ) '' Set.Icc (-(1/2) : ℝ) (-(1/2) + 1) = Set.univ :=
      AddCircle.coe_image_Icc_eq (1 : ℝ) (-(1/2))
    have hmem : ξ ∈ ((↑) : ℝ → Circ) '' Set.Icc (-(1/2) : ℝ) (-(1/2) + 1) := by
      rw [hsurj]; exact Set.mem_univ ξ
    obtain ⟨x, hx, hxξ⟩ := hmem
    rw [Set.mem_Icc] at hx
    exact ⟨x, ⟨hx.1, by linarith [hx.2]⟩, hxξ⟩
  subst hxξ
  -- choose `N` large, so that `-x + N` lies to the right of the interval `Icc (-a) a`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, a + x < (N : ℝ) := exists_nat_gt (a + x)
  have hy : a < -x + (N : ℝ) := by linarith
  have hnotmem : -x + (N : ℝ) ∉ Set.Icc (-a) a := fun hmem =>
    absurd hmem.2 (not_le.mpr hy)
  have key := h (-x + (N : ℝ)) hnotmem
  have hcoe : -((-x + (N : ℝ) : ℝ) : Circ) = (x : Circ) := by
    rw [show (-x + (N : ℝ) : ℝ) = (-x) + (N : ℝ) by ring, coe_add_natCast (-x) N]
    rw [AddCircle.coe_neg, neg_neg]
  rw [hcoe] at key
  exact key

/-- **The support hypothesis of the (vacuous) `largeScaleBoundF_opArcW_of_sampling` forces the
symbol to vanish.**  That theorem required the *periodisation* `x ↦ f (-(x : Circle))` of the
model's bump to be supported in the single interval `Icc (-1/(2Q)) (1/(2Q))` with `Q = QA A ≥ 1`;
by `eq_zero_of_forall_notMem_Icc_neg_coe` this forces `f = 0`.  Together with the integrability
hypothesis (a non-zero `1`-periodic function has infinite integral) this shows that all its
hypotheses fail for a non-zero model, i.e. it is vacuous — which is why
`largeScaleBoundF_opArcW_of_sampling_lift` is stated for `circleLift`. -/
theorem eq_zero_of_support_Icc_neg_coe {f : Circ → ℂ} {Q : ℕ} (hQ : 1 ≤ Q)
    (h : ∀ x : ℝ,
      x ∉ Set.Icc (-(1 / (2 * (Q : ℝ)))) (1 / (2 * (Q : ℝ))) → f (-(x : Circ)) = 0) :
    f = 0 := by
  refine eq_zero_of_forall_notMem_Icc_neg_coe (a := 1 / (2 * (Q : ℝ)))
    (by positivity) ?_ h
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (Q : ℝ))]
  linarith

end

end Work.BourgainPlan.Thm52
