import Mathlib
import Submission.Work.Drive.BoxParityDefs
import Submission.Work.Drive.exists_global_integralCurve
import Submission.Work.Drive.flowField_basic
import Submission.Work.Drive.integralCurve_unique
import Submission.Work.Drive.flowField_on_box
import Submission.Work.Drive.fderiv_flowField_eq_zero
import Submission.Work.Drive.interior_unitBox
import Submission.Work.Drive.exists_face_index
import Submission.Work.Drive.ker_eq_span_cofactorVec
import Submission.Work.Drive.cofactorVec_apply_ne_zero

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# Framework for `boxParity`

The flow line `flowCurve F hF x` of the compactly supported tangential field `flowField F` is an
integral curve defined on all of `ℝ` along which `F` is constant (so it stays in the zero set while
it is inside the box).  `inTimes γ`, `arcTimes γ`, `arcEnd γ` describe the arc of the zero set
through a boundary zero: the component of the in-box times whose closure contains `0`, and the
"other endpoint" of that component.  `pairPt F hF b` is the point of the zero set at that other
endpoint, i.e. the candidate partner of `b` in the mod-2 pairing.
-/

namespace Work.Drive

open scoped ContDiff Topology
open Set

open Submission.Drive

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- The smoothness index `C^∞`. -/
abbrev Ctop : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The global flow line of `flowField F` through `x`. -/
noncomputable def flowCurve {m : ℕ} (F : Amb m → Tgt m) (hF : ContDiff ℝ Ctop F)
    (x : Amb m) : ℝ → Amb m :=
  Classical.choose (exists_global_integralCurve (flowField_basic hF).1 (flowField_basic hF).2.1 x)

theorem flowCurve_zero {m : ℕ} (F : Amb m → Tgt m) (hF : ContDiff ℝ Ctop F) (x : Amb m) :
    flowCurve F hF x 0 = x :=
  (Classical.choose_spec
    (exists_global_integralCurve (flowField_basic hF).1 (flowField_basic hF).2.1 x)).1

theorem flowCurve_hasDerivAt {m : ℕ} (F : Amb m → Tgt m) (hF : ContDiff ℝ Ctop F) (x : Amb m) :
    ∀ t, HasDerivAt (flowCurve F hF x) (flowField F (flowCurve F hF x t)) t :=
  (Classical.choose_spec
    (exists_global_integralCurve (flowField_basic hF).1 (flowField_basic hF).2.1 x)).2

/-- Uniqueness: any integral curve of `flowField F` through `x` equals `flowCurve F hF x`. -/
theorem flowCurve_eq_of_hasDerivAt {m : ℕ} {F : Amb m → Tgt m} (hF : ContDiff ℝ Ctop F)
    {x : Amb m} {γ : ℝ → Amb m} (hγ : ∀ t, HasDerivAt γ (flowField F (γ t)) t)
    (h0 : γ 0 = x) : γ = flowCurve F hF x := by
  obtain ⟨L, hL⟩ := (flowField_basic hF).2.2
  exact integralCurve_unique hL (γ := γ) (γ' := flowCurve F hF x) hγ
    (flowCurve_hasDerivAt F hF x) (by rw [h0, flowCurve_zero F hF x])

/-- `F` is constant along the flow lines of `flowField F`. -/
theorem F_flowCurve {m : ℕ} {F : Amb m → Tgt m} (hF : ContDiff ℝ Ctop F) (x : Amb m) (t : ℝ) :
    F (flowCurve F hF x t) = F x := by
  have hg : ∀ s, HasDerivAt (fun u => F (flowCurve F hF x u)) 0 s := by
    intro s
    have h1 : HasFDerivAt F (fderiv ℝ F (flowCurve F hF x s)) (flowCurve F hF x s) :=
      ((hF.differentiable (by simp)).differentiableAt).hasFDerivAt
    have h2 := h1.comp_hasDerivAt s (flowCurve_hasDerivAt F hF x s)
    have h3 : (fderiv ℝ F (flowCurve F hF x s)) (flowField F (flowCurve F hF x s)) = 0 :=
      fderiv_flowField_eq_zero _
    simpa only [Function.comp_def, h3] using h2
  have h := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) t 0
  rwa [flowCurve_zero F hF x] at h

/-- The flow line through `x` is also the flow line through any of its points (time-shifted). -/
theorem flowCurve_shift {m : ℕ} {F : Amb m → Tgt m} (hF : ContDiff ℝ Ctop F) {x : Amb m}
    {t₀ : ℝ} : flowCurve F hF (flowCurve F hF x t₀) = fun t => flowCurve F hF x (t + t₀) := by
  have h1 : ∀ t, HasDerivAt (fun s => flowCurve F hF x (s + t₀))
      (flowField F ((fun s => flowCurve F hF x (s + t₀)) t)) t := by
    intro t
    have h := (flowCurve_hasDerivAt F hF x (t + t₀)).comp_add_const t
    simpa using h
  have h2 : (fun s => flowCurve F hF x (s + t₀)) 0 = flowCurve F hF x t₀ := by simp
  exact (flowCurve_eq_of_hasDerivAt hF h1 h2).symm

/-- A global integral curve which takes the same value twice is periodic. -/
theorem flowCurve_periodic_of_eq {m : ℕ} {F : Amb m → Tgt m} (hF : ContDiff ℝ Ctop F)
    {x : Amb m} {s t : ℝ} (h : flowCurve F hF x s = flowCurve F hF x t) :
    Function.Periodic (flowCurve F hF x) (s - t) := by
  obtain ⟨L, hL⟩ := (flowField_basic hF).2.2
  have hshift : ∀ u, HasDerivAt (fun v => flowCurve F hF x (v + (s - t)))
      (flowField F (flowCurve F hF x (u + (s - t)))) u := by
    intro u
    have h := (flowCurve_hasDerivAt F hF x (u + (s - t))).comp_add_const u
    simpa using h
  have heq : (fun v => flowCurve F hF x (v + (s - t))) = flowCurve F hF x := by
    refine integralCurve_unique (t₀ := t) hL hshift (flowCurve_hasDerivAt F hF x) ?_
    show flowCurve F hF x (t + (s - t)) = flowCurve F hF x t
    have hts : t + (s - t) = s := by ring
    rw [hts, h]
  intro u
  have := congrFun heq u
  simpa using this

/-- At a point of the unit box, `flowField F` is a positive multiple of the cofactor field, so its
`i`-th component vanishes only if the cofactor vector does. -/
theorem flowField_apply_ne_zero_of_bdy {m : ℕ} {F : Amb m → Tgt m} {b : Amb m} {i : Fin (m + 1)}
    (hb : b ∈ unitBox m)
    (hsurj : Function.Surjective (fun v : {v : Amb m // v i = 0} => fderiv ℝ F b v.1)) :
    flowField F b i ≠ 0 := by
  have hne : cofactorVectorF F b i ≠ 0 := cofactorVec_apply_ne_zero (fderiv ℝ F b) i hsurj
  rw [flowField_on_box (x := b) hb]
  simp only [PiLp.smul_apply, smul_eq_mul]
  exact mul_ne_zero (inv_ne_zero (by positivity)) hne

/-- A point of the closed box which is not in its interior lies on a face. -/
theorem exists_coord_eq_zero_or_one_of_not_mem_interior {m : ℕ} {x : Amb m}
    (hx : x ∈ unitBox m) (hx' : x ∉ interior (unitBox m)) :
    ∃ i : Fin (m + 1), x i = 0 ∨ x i = 1 := by
  by_contra h
  push_neg at h
  apply hx'
  rw [interior_unitBox]
  intro i
  exact ⟨lt_of_le_of_ne (hx i).1 (Ne.symm (h i).1), lt_of_le_of_ne (hx i).2 (h i).2⟩

/-- A zero of `F` in the closed box which is not in the interior lies on the boundary of the box. -/
theorem mem_bdyZeros_of_mem_unitBox_not_mem_interior {m : ℕ} {F : Amb m → Tgt m} {x : Amb m}
    (hx : x ∈ unitBox m) (hx' : x ∉ interior (unitBox m)) (hF0 : F x = 0) :
    x ∈ bdyZeros F :=
  ⟨⟨hx, exists_coord_eq_zero_or_one_of_not_mem_interior hx hx'⟩, hF0⟩

/-- A boundary zero of the box is not an interior point of the box. -/
theorem not_mem_interior_of_mem_bdyZeros {m : ℕ} {F : Amb m → Tgt m} {x : Amb m}
    (hx : x ∈ bdyZeros F) : x ∉ interior (unitBox m) := by
  obtain ⟨i, hi⟩ := hx.1.2
  intro hcon
  rw [interior_unitBox] at hcon
  have hi' : x i ∈ Set.Ioo (0 : ℝ) 1 := hcon i
  rcases hi with h | h
  · rw [h] at hi'; exact absurd hi'.1 (lt_irrefl 0)
  · rw [h] at hi'; exact absurd hi'.2 (lt_irrefl 1)

/-- The set of times at which `γ` lies in the interior of the unit box. -/
def inTimes {m : ℕ} (γ : ℝ → Amb m) : Set ℝ := {t | γ t ∈ interior (unitBox m)}

/-- The set of times `t` such that the curve lies in the interior of the box throughout `(0,t)`. -/
def rightBoxTimes {m : ℕ} (γ : ℝ → Amb m) : Set ℝ :=
  {t | ∀ s ∈ Ioo (0 : ℝ) t, γ s ∈ interior (unitBox m)}

/-- The set of times `t` such that the curve lies in the interior of the box throughout `(t,0)`. -/
def leftBoxTimes {m : ℕ} (γ : ℝ → Amb m) : Set ℝ :=
  {t | ∀ s ∈ Ioo t (0 : ℝ), γ s ∈ interior (unitBox m)}

/-- The "other endpoint" of the in-box arc through the origin.  Exactly one of `sSup (rightBoxTimes γ)`
and `sInf (leftBoxTimes γ)` is `0` (the arc meets the origin on exactly one side), so their sum is the
other endpoint of the arc. -/
def arcEnd {m : ℕ} (γ : ℝ → Amb m) : ℝ := sSup (rightBoxTimes γ) + sInf (leftBoxTimes γ)

/-- The candidate partner of a boundary zero `b`: the point of the zero set at the other end of the
in-box arc of the flow line through `b`. -/
noncomputable def pairPt {m : ℕ} (F : Amb m → Tgt m) (hF : ContDiff ℝ Ctop F) (b : Amb m) : Amb m :=
  flowCurve F hF b (arcEnd (flowCurve F hF b))

end

end Work.Drive
