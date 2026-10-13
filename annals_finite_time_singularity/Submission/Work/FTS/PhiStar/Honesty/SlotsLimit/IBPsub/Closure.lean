/-
# `FTS/PhiStar/Honesty/SlotsLimit/IBPsub.Closure`

Closure properties of the class `TestQ0` of test functions on the open quadrant
`Q0 = (0,∞) × (0,π/2)`: closure under `∂_z`, `∂_θ`, under multiplication by a globally `C^∞`
factor, and hence under the transposes `DzStar`, `DthStar` and their iterates.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.Defs
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

set_option autoImplicit false
set_option maxHeartbeats 2000000

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-! ## 0. Closure of the class of test functions -/

/-- The plain `z`-derivative of a test function on the open quadrant is again a test function:
globally `C^∞`, compactly supported, and the support only shrinks. -/
theorem testQ0_pz {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) : TestQ0 (Work.Spaces.pz φ) := by
  have hF : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry φ) := h.1
  have hdiff : Differentiable ℝ (Function.uncurry φ) :=
    hF.differentiable (by rw [Work.Stability.smoothOrder]; simp)
  have hchain : Function.uncurry (Work.Spaces.pz φ)
      = fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry φ) p) (1, 0) := by
    funext p
    exact Work.Spaces.pz_eq_fderiv (hdiff p)
  have hfd : ContDiff ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry φ) p) :=
    ContDiff.fderiv_right hF (by rw [Work.Stability.smoothOrder]; simp)
  have hsmooth : ContDiff ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz φ)) := by
    rw [hchain]
    exact hfd.clm_apply contDiff_const
  have hcpt : HasCompactSupport (Function.uncurry (Work.Spaces.pz φ)) := by
    rw [hchain]
    exact h.2.1.fderiv_apply ℝ (1, 0)
  have hsub : tsupport (Function.uncurry (Work.Spaces.pz φ))
      ⊆ tsupport (Function.uncurry φ) := by
    rw [hchain]
    exact tsupport_fderiv_apply_subset ℝ (1, 0)
  exact ⟨hsmooth, hcpt, hsub.trans h.2.2⟩

/-- The plain `θ`-derivative of a test function on the open quadrant is again a test function. -/
theorem testQ0_pth {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) : TestQ0 (Work.Spaces.pth φ) := by
  have hF : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry φ) := h.1
  have hdiff : Differentiable ℝ (Function.uncurry φ) :=
    hF.differentiable (by rw [Work.Stability.smoothOrder]; simp)
  have hchain : Function.uncurry (Work.Spaces.pth φ)
      = fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry φ) p) (0, 1) := by
    funext p
    exact Work.Spaces.pth_eq_fderiv (hdiff p)
  have hfd : ContDiff ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry φ) p) :=
    ContDiff.fderiv_right hF (by rw [Work.Stability.smoothOrder]; simp)
  have hsmooth : ContDiff ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth φ)) := by
    rw [hchain]
    exact hfd.clm_apply contDiff_const
  have hcpt : HasCompactSupport (Function.uncurry (Work.Spaces.pth φ)) := by
    rw [hchain]
    exact h.2.1.fderiv_apply ℝ (0, 1)
  have hsub : tsupport (Function.uncurry (Work.Spaces.pth φ))
      ⊆ tsupport (Function.uncurry φ) := by
    rw [hchain]
    exact tsupport_fderiv_apply_subset ℝ (0, 1)
  exact ⟨hsmooth, hcpt, hsub.trans h.2.2⟩

/-- The uncurried pointwise product is the pointwise product of the uncurried factors. -/
theorem uncurry_mul_eq (ψ φ : ℝ → ℝ → ℝ) :
    Function.uncurry (fun z θ => ψ z θ * φ z θ)
      = Function.uncurry ψ * Function.uncurry φ := by
  funext p
  obtain ⟨z, θ⟩ := p
  rfl

/-- A test function multiplied on the left by a globally `C^∞` function is again a test function
(the support of a product is contained in the support of the right factor). -/
theorem testQ0_mul_left {ψ φ : ℝ → ℝ → ℝ}
    (hψ : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry ψ)) (hφ : TestQ0 φ) :
    TestQ0 (fun z θ => ψ z θ * φ z θ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [uncurry_mul_eq ψ φ]
    exact hψ.mul hφ.1
  · rw [uncurry_mul_eq ψ φ]
    exact hφ.2.1.mul_left
  · rw [uncurry_mul_eq ψ φ]
    exact (tsupport_mul_subset_right (f := Function.uncurry ψ)
      (g := Function.uncurry φ)).trans hφ.2.2

/-- A test function multiplied by a constant is again a test function. -/
theorem testQ0_const_mul (c : ℝ) {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) :
    TestQ0 (fun z θ => c * φ z θ) := by
  refine testQ0_mul_left ?_ h
  have hconst : Function.uncurry (fun _z _θ : ℝ => c) = fun _ : ℝ × ℝ => c := rfl
  rw [hconst]
  exact contDiff_const

/-- A test function multiplied by a power of the `z`-coordinate is again a test function. -/
theorem testQ0_zpow_mul (k : ℕ) {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) :
    TestQ0 (fun z θ => z ^ k * φ z θ) := by
  refine testQ0_mul_left ?_ h
  have hz : Function.uncurry (fun z _θ : ℝ => z ^ k) = fun p : ℝ × ℝ => p.1 ^ k := rfl
  rw [hz]
  exact contDiff_fst.pow k

/-- A test function multiplied by `sin (2θ)` is again a test function. -/
theorem testQ0_sin_mul {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) :
    TestQ0 (fun z θ => Real.sin (2 * θ) * φ z θ) := by
  refine testQ0_mul_left ?_ h
  have hs : Function.uncurry (fun _z θ : ℝ => Real.sin (2 * θ))
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) := rfl
  rw [hs]
  exact Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)

/-- The closed support of `∂_z φ` is contained in that of `φ`. -/
theorem tsupport_pz_subset {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) :
    tsupport (Function.uncurry (Work.Spaces.pz φ)) ⊆ tsupport (Function.uncurry φ) := by
  have hF : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry φ) := h.1
  have hdiff : Differentiable ℝ (Function.uncurry φ) :=
    hF.differentiable (by rw [Work.Stability.smoothOrder]; simp)
  have hchain : Function.uncurry (Work.Spaces.pz φ)
      = fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry φ) p) (1, 0) := by
    funext p
    exact Work.Spaces.pz_eq_fderiv (hdiff p)
  rw [hchain]
  exact tsupport_fderiv_apply_subset ℝ (1, 0)

/-- The closed support of `∂_θ φ` is contained in that of `φ`. -/
theorem tsupport_pth_subset {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) :
    tsupport (Function.uncurry (Work.Spaces.pth φ)) ⊆ tsupport (Function.uncurry φ) := by
  have hF : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry φ) := h.1
  have hdiff : Differentiable ℝ (Function.uncurry φ) :=
    hF.differentiable (by rw [Work.Stability.smoothOrder]; simp)
  have hchain : Function.uncurry (Work.Spaces.pth φ)
      = fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry φ) p) (0, 1) := by
    funext p
    exact Work.Spaces.pth_eq_fderiv (hdiff p)
  rw [hchain]
  exact tsupport_fderiv_apply_subset ℝ (0, 1)

/-- Iterated `∂_z` of a test function is a test function. -/
theorem testQ0_pzIter {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) : ∀ k : ℕ,
    TestQ0 (Work.Spaces.pzIter k φ)
  | 0 => by simpa using h
  | (k + 1) => by
      show TestQ0 (Work.Spaces.pz (Work.Spaces.pzIter k φ))
      exact testQ0_pz (testQ0_pzIter h k)

/-- Iterated `∂_θ` preserves smoothness on the open quadrant. -/
theorem smoothOpen_pthIter {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) (i : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i g) := by
  induction i with
  | zero => simpa using hg
  | succ i ih => rw [Work.Spaces.pthIter_succ]; exact Work.FTS.EllipticEst.SmoothOpen.pth ih

/-- Iterated `∂_θ` of a test function is a test function. -/
theorem testQ0_pthIter {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) : ∀ k : ℕ,
    TestQ0 (Work.Spaces.pthIter k φ)
  | 0 => by simpa using h
  | (k + 1) => by
      show TestQ0 (Work.Spaces.pth (Work.Spaces.pthIter k φ))
      exact testQ0_pth (testQ0_pthIter h k)

/-- The transpose of `D_z` preserves the class of test functions. -/
theorem testQ0_DzStar {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) : TestQ0 (DzStar φ) := by
  have hpzs : ContDiff ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz φ)) := (testQ0_pz h).1
  have hchain : Function.uncurry (DzStar φ) = fun p : ℝ × ℝ =>
      -(p.1 * Function.uncurry (Work.Spaces.pz φ) p + Function.uncurry φ p) := by
    funext p
    obtain ⟨z, θ⟩ := p
    rfl
  have hsum : Function.support (fun p : ℝ × ℝ =>
      p.1 * Function.uncurry (Work.Spaces.pz φ) p + Function.uncurry φ p)
      ⊆ tsupport (Function.uncurry φ) := by
    intro p hp
    rw [Function.mem_support] at hp
    by_cases h0 : Function.uncurry φ p = 0
    · refine tsupport_pz_subset h (subset_closure (Function.mem_support.mpr ?_))
      intro h1
      exact hp (by rw [h1, h0]; ring)
    · exact subset_closure (Function.mem_support.mpr h0)
  have hsupp : Function.support (fun p : ℝ × ℝ =>
      -(p.1 * Function.uncurry (Work.Spaces.pz φ) p + Function.uncurry φ p))
      ⊆ tsupport (Function.uncurry φ) := by
    refine Set.Subset.trans ?_ hsum
    intro p hp
    rw [Function.mem_support] at hp ⊢
    intro hzero
    exact hp (by rw [hzero, neg_zero])
  refine ⟨?_, ?_, ?_⟩
  · rw [hchain]
    exact (((contDiff_fst.mul hpzs).add h.1)).neg
  · rw [hchain]
    exact (((HasCompactSupport.mul_left (f := fun p : ℝ × ℝ => p.1)
      (testQ0_pz h).2.1)).add h.2.1).neg
  · rw [hchain]
    refine (closure_mono hsupp).trans ?_
    rw [(isClosed_tsupport (Function.uncurry φ)).closure_eq]
    exact h.2.2

/-- The transpose of `D_θ` preserves the class of test functions. -/
theorem testQ0_DthStar {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) : TestQ0 (DthStar φ) := by
  have hpths : ContDiff ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth φ)) := (testQ0_pth h).1
  have hsin : ContDiff ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2)) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)
  have hcos : ContDiff ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.cos (2 * p.2)) :=
    contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_snd))
  have hchain : Function.uncurry (DthStar φ) = fun p : ℝ × ℝ =>
      -(Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth φ) p
        + (2 * Real.cos (2 * p.2)) * Function.uncurry φ p) := by
    funext p
    obtain ⟨z, θ⟩ := p
    rfl
  have hsum : Function.support (fun p : ℝ × ℝ =>
      Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth φ) p
        + (2 * Real.cos (2 * p.2)) * Function.uncurry φ p)
      ⊆ tsupport (Function.uncurry φ) := by
    intro p hp
    rw [Function.mem_support] at hp
    by_cases h0 : Function.uncurry φ p = 0
    · refine tsupport_pth_subset h (subset_closure (Function.mem_support.mpr ?_))
      intro h1
      exact hp (by rw [h1, h0]; ring)
    · exact subset_closure (Function.mem_support.mpr h0)
  have hsupp : Function.support (fun p : ℝ × ℝ =>
      -(Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth φ) p
        + (2 * Real.cos (2 * p.2)) * Function.uncurry φ p))
      ⊆ tsupport (Function.uncurry φ) := by
    refine Set.Subset.trans ?_ hsum
    intro p hp
    rw [Function.mem_support] at hp ⊢
    intro hzero
    exact hp (by rw [hzero, neg_zero])
  refine ⟨?_, ?_, ?_⟩
  · rw [hchain]
    exact ((hsin.mul hpths).add (hcos.mul h.1)).neg
  · rw [hchain]
    exact (((testQ0_pth h).2.1.mul_left (f := fun p : ℝ × ℝ => Real.sin (2 * p.2))).add
      (h.2.1.mul_left (f := fun p : ℝ × ℝ => 2 * Real.cos (2 * p.2)))).neg
  · rw [hchain]
    refine (closure_mono hsupp).trans ?_
    rw [(isClosed_tsupport (Function.uncurry φ)).closure_eq]
    exact h.2.2

/-- Iterated `D_z`-transpose preserves the class of test functions. -/
theorem testQ0_DzIterStar {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) : ∀ j : ℕ,
    TestQ0 (DzIterStar j φ)
  | 0 => by show TestQ0 φ; exact h
  | (j + 1) => by
      show TestQ0 (DzIterStar j (DzStar φ))
      exact testQ0_DzIterStar (testQ0_DzStar h) j

/-- Iterated `D_θ`-transpose preserves the class of test functions. -/
theorem testQ0_DthIterStar {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) : ∀ i : ℕ,
    TestQ0 (DthIterStar i φ)
  | 0 => by show TestQ0 φ; exact h
  | (i + 1) => by
      show TestQ0 (DthIterStar i (DthStar φ))
      exact testQ0_DthIterStar (testQ0_DthStar h) i

/-- The transpose of any mixed operator preserves the class of test functions. -/
theorem testQ0_mixedStar {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) (j i : ℕ) :
    TestQ0 (mixedStar j i φ) :=
  testQ0_DthIterStar (testQ0_DzIterStar h j) i

/-- The transpose of `∂_z^j` preserves the class of test functions. -/
theorem testQ0_pzIterStar {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) (j : ℕ) :
    TestQ0 (pzIterStar j φ) := by
  have h1 : TestQ0 (Work.Spaces.pzIter j φ) := testQ0_pzIter h j
  have h2 : pzIterStar j φ = fun z θ => (-1 : ℝ) ^ j * Work.Spaces.pzIter j φ z θ := rfl
  rw [h2]
  exact testQ0_const_mul _ h1

/-- The transpose of `∂_θ^i` preserves the class of test functions. -/
theorem testQ0_pthIterStar {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) (i : ℕ) :
    TestQ0 (pthIterStar i φ) := by
  have h1 : TestQ0 (Work.Spaces.pthIter i φ) := testQ0_pthIter h i
  have h2 : pthIterStar i φ = fun z θ => (-1 : ℝ) ^ i * Work.Spaces.pthIter i φ z θ := rfl
  rw [h2]
  exact testQ0_const_mul _ h1


end Work.FTS.PhiStar.Honesty.SlotsLimit
