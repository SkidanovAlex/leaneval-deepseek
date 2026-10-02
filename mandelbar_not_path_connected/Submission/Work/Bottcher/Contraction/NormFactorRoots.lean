import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Contraction.preimage_pMap_eq_iff
import Submission.Work.Bottcher.Contraction.ChainDefs
import Submission.Work.Bottcher.Green.green_nonneg
import Submission.Work.Bottcher.Green.greenParam_pos_iff
import Submission.Work.Bottcher.Inverse.green_eq_log_of_inverseBottcher
import Submission.Work.Escape.exists_differentiableOn_ball_clog
import Submission.Work.Escape.continuous_green

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The roots of `pMap c` and the normalised-factor path

* `root1..root4` are the four roots of the monic quartic `pMap c`, i.e. the four preimages of `0`;
* `pMap_eq_prod_roots`: `pMap c z = ∏ (z - root_j)`;
* `green c (root_j c) = 0` and `green c 0 = 0` for `c ∈ M*` (the roots lie in the filled Julia set);
* `normFactorPath c γ : t ↦ pMap c (γ t)/(γ t)^4`, the path whose holomorphic logarithm is the
  content of `exists_analytic_log_normFactor_of_mem_mandelbar`.
-/

open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher.Contraction

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

variable (c : ℂ)

/-! ## The four roots of `pMap c` -/

/-- The first root of `pMap c`, i.e. the first preimage of `0`. -/
def root1 : ℂ := preim1 c 0

/-- The second root of `pMap c`. -/
def root2 : ℂ := preim2 c 0

/-- The third root of `pMap c`. -/
def root3 : ℂ := preim3 c 0

/-- The fourth root of `pMap c`. -/
def root4 : ℂ := preim4 c 0

theorem pMap_root1 : Work.Bottcher.pMap c (root1 c) = 0 := pMap_preim1 c 0
theorem pMap_root2 : Work.Bottcher.pMap c (root2 c) = 0 := pMap_preim2 c 0
theorem pMap_root3 : Work.Bottcher.pMap c (root3 c) = 0 := pMap_preim3 c 0
theorem pMap_root4 : Work.Bottcher.pMap c (root4 c) = 0 := pMap_preim4 c 0

theorem root2_eq : root2 c = -root1 c := rfl
theorem root4_eq : root4 c = -root3 c := rfl

theorem root1_sq : (root1 c) ^ 2 = Complex.sqrt (-c) - conj c := by
  simpa [root1, preim1, zero_sub] using (sqrt_sq (Complex.sqrt (0 - c) - conj c))

theorem root3_sq : (root3 c) ^ 2 = -Complex.sqrt (-c) - conj c := by
  simpa [root3, preim3, preim1, zero_sub] using (sqrt_sq (-Complex.sqrt (0 - c) - conj c))

theorem mul_root12 (z : ℂ) :
    (z - root1 c) * (z - root2 c) = z ^ 2 + (conj c - Complex.sqrt (-c)) := by
  have h : (z - root1 c) * (z - -root1 c) = z ^ 2 - (root1 c) ^ 2 := by ring
  rw [root2_eq, h, root1_sq]
  ring

theorem mul_root34 (z : ℂ) :
    (z - root3 c) * (z - root4 c) = z ^ 2 + (conj c + Complex.sqrt (-c)) := by
  have h : (z - root3 c) * (z - -root3 c) = z ^ 2 - (root3 c) ^ 2 := by ring
  rw [root4_eq, h, root3_sq]
  ring

/-- **The four roots factor `pMap c`**: since they are (up to signs) the square roots of
`± sqrt (-c) - conj c`, the difference-of-squares identity gives the factorisation. -/
theorem pMap_eq_prod_roots (z : ℂ) :
    Work.Bottcher.pMap c z = (z - root1 c) * (z - root2 c) * (z - root3 c) * (z - root4 c) := by
  have hs : Complex.sqrt (-c) ^ 2 = -c := sqrt_sq (-c)
  calc Work.Bottcher.pMap c z = (z ^ 2 + conj c) ^ 2 + c := by rw [Work.Bottcher.pMap_apply]
    _ = (z ^ 2 + (conj c - Complex.sqrt (-c))) * (z ^ 2 + (conj c + Complex.sqrt (-c))) := by
          linear_combination hs
    _ = ((z - root1 c) * (z - root2 c)) * ((z - root3 c) * (z - root4 c)) := by
          rw [mul_root12, mul_root34]
    _ = (z - root1 c) * (z - root2 c) * (z - root3 c) * (z - root4 c) := by ring

/-! ## The roots and `0` lie in the filled Julia set -/

theorem green_zero_of_mem_mandelbar (hc : c ∈ Mandelbar) : Work.Bottcher.green c 0 = 0 := by
  rcases lt_or_eq_of_le (Work.Bottcher.Green.green_nonneg c 0) with h | h
  · exfalso
    exact ((Work.Bottcher.Green.greenParam_pos_iff c).mp
      (by simpa [Work.Bottcher.greenParam_def] using h)) hc
  · exact h.symm

theorem green_root1_of_mem_mandelbar (hc : c ∈ Mandelbar) :
    Work.Bottcher.green c (root1 c) = 0 := by
  have h0 := green_zero_of_mem_mandelbar c hc
  have h := Work.Bottcher.Inverse.green_pMap c (root1 c)
  rw [pMap_root1, h0] at h
  linarith

theorem green_root2_of_mem_mandelbar (hc : c ∈ Mandelbar) :
    Work.Bottcher.green c (root2 c) = 0 := by
  have h0 := green_zero_of_mem_mandelbar c hc
  have h := Work.Bottcher.Inverse.green_pMap c (root2 c)
  rw [pMap_root2, h0] at h
  linarith

theorem green_root3_of_mem_mandelbar (hc : c ∈ Mandelbar) :
    Work.Bottcher.green c (root3 c) = 0 := by
  have h0 := green_zero_of_mem_mandelbar c hc
  have h := Work.Bottcher.Inverse.green_pMap c (root3 c)
  rw [pMap_root3, h0] at h
  linarith

theorem green_root4_of_mem_mandelbar (hc : c ∈ Mandelbar) :
    Work.Bottcher.green c (root4 c) = 0 := by
  have h0 := green_zero_of_mem_mandelbar c hc
  have h := Work.Bottcher.Inverse.green_pMap c (root4 c)
  rw [pMap_root4, h0] at h
  linarith

/-! ## The normalised-factor path -/

theorem continuous_pMap (c : ℂ) : Continuous (Work.Bottcher.pMap c) := by
  have h : Work.Bottcher.pMap c = fun z : ℂ => (z ^ 2 + conj c) ^ 2 + c :=
    funext fun z => Work.Bottcher.pMap_apply c z
  rw [h]
  fun_prop

/-- The path `t ↦ pMap c (γ t) / (γ t)^4`. -/
def normFactorPath (c : ℂ) (γ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ≠ 0) :
    C(unitInterval, ℂ) :=
  ⟨fun t => Work.Bottcher.pMap c (γ t) / (γ t) ^ 4,
    ((continuous_pMap c).comp γ.continuous).div (γ.continuous.pow 4)
      (fun t => pow_ne_zero 4 (hγ t))⟩

@[simp] theorem normFactorPath_apply (γ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ≠ 0)
    (t : unitInterval) : normFactorPath c γ hγ t = Work.Bottcher.pMap c (γ t) / (γ t) ^ 4 := rfl


/-! ## Analyticity of a continuous logarithm of the normalised factor -/

theorem isOpen_escapeSet (c : ℂ) : IsOpen (Work.Bottcher.EscapeSet c) := by
  have hc : Continuous (fun z : ℂ => Work.Bottcher.green c z) :=
    Work.Escape.continuous_green (Tantibar c) 2 ‖c‖ (Work.Escape.monicGrowth_Tantibar c) le_rfl
  exact isOpen_lt continuous_const hc

theorem normFactor_ne_zero_of_mem_mandelbar (hc : c ∈ Mandelbar) {z : ℂ}
    (hz : 0 < Work.Bottcher.green c z) : Work.Bottcher.pMap c z / z ^ 4 ≠ 0 := by
  have h0 := green_zero_of_mem_mandelbar c hc
  have hz0 : z ≠ 0 := by
    intro hz0
    have hz' : 0 < Work.Bottcher.green c 0 := by rw [← hz0]; exact hz
    rw [h0] at hz'
    exact lt_irrefl 0 hz'
  have hp : Work.Bottcher.pMap c z ≠ 0 := by
    intro h
    have h4 := Work.Bottcher.Inverse.green_pMap c z
    rw [h, h0] at h4
    linarith
  exact div_ne_zero hp (pow_ne_zero 4 hz0)

theorem differentiableOn_normFactor_of_mem_mandelbar (hc : c ∈ Mandelbar) :
    DifferentiableOn ℂ (fun z : ℂ => Work.Bottcher.pMap c z / z ^ 4) (Work.Bottcher.EscapeSet c) := by
  have h0 := green_zero_of_mem_mandelbar c hc
  refine DifferentiableOn.div ?_ ?_ ?_
  · have h : Work.Bottcher.pMap c = fun z : ℂ => (z ^ 2 + conj c) ^ 2 + c :=
      funext fun z => Work.Bottcher.pMap_apply c z
    rw [h]
    fun_prop
  · fun_prop
  · intro z hz
    refine pow_ne_zero 4 ?_
    intro hz0
    have hz' : 0 < Work.Bottcher.green c 0 := by rw [← hz0]; exact hz
    rw [h0] at hz'
    exact lt_irrefl 0 hz'

/-- A continuous logarithm of the normalised factor on the escape set is automatically holomorphic
there. -/
theorem analyticOnNhd_log_of_exp_eq (hc : c ∈ Mandelbar) {L : ℂ → ℂ}
    (hcont : ContinuousOn L (Work.Bottcher.EscapeSet c))
    (hexp : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      Complex.exp (L z) = Work.Bottcher.pMap c z / z ^ 4) :
    AnalyticOnNhd ℂ L (Work.Bottcher.EscapeSet c) := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_escapeSet c)
  exact Work.Escape.continuousOn_exp_eq_differentiableOn (isOpen_escapeSet c) hcont
    (differentiableOn_normFactor_of_mem_mandelbar c hc)
    (fun z hz => normFactor_ne_zero_of_mem_mandelbar c hc hz)
    (fun z hz => hexp z hz)

end

end Work.Bottcher.Contraction
