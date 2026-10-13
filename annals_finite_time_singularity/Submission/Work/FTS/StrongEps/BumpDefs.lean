/-
Copyright: work module for the Elgindi finite-time singularity project.

# The explicit bump profile `bump` and its elementary theory

`bump z θ = zCut z * thCut θ`, where

* `zCut z = st (z - 1/2) · st (1 - z)` is supported on `[1/2,1]` and strictly positive exactly
  on `(1/2,1)`;
* `thCut θ = st (θ - π/4) · st (3π/8 - θ)` is supported on `[π/4,3π/8]` and strictly positive
  exactly on `(π/4,3π/8)`;

here `st = Real.smoothTransition`.

So `bump` is `C^∞` on `ℝ²`, is supported on the box `[1/2,1] × [π/4,3π/8]` (which is contained
in the open quadrant `(0,∞) × (0,π/2)` and is *bounded away from* the singularities `z = 0`,
`θ = 0`, `θ = π/2` of the weights in `Work.Spaces.HkIntegrand`), and it is bounded below by the
positive constant `innerConst` on the inner box `[5/8,7/8] × [9π/32,11π/32]`.

Consequences recorded here (used by `Submission/Work/FTS/StrongEps/exists_smooth_supported_HkSq_gt.lean`
and by the delegated lemmas of the same area):

* the `ℋ^k`-integrand of `bump` vanishes outside the box;
* it is bounded by a constant (`exists_bound_HkIntegrand_bump`);
* it is strictly positive on the inner box.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The definitions -/

/-- The smooth cut-off `z ↦ st (z - 1/2) · st (1 - z)`, supported on `[1/2,1]`. -/
def zCut (z : ℝ) : ℝ :=
  Real.smoothTransition (z - (1 / 2 : ℝ)) * Real.smoothTransition (1 - z)

/-- The smooth cut-off `θ ↦ st (θ - π/4) · st (3π/8 - θ)`, supported on `[π/4,3π/8]`. -/
def thCut (θ : ℝ) : ℝ :=
  Real.smoothTransition (θ - Real.pi / 4) *
    Real.smoothTransition (3 * Real.pi / 8 - θ)

/-- The bump profile `bump z θ = zCut z · thCut θ`, supported on `[1/2,1] × [π/4,3π/8]`. -/
def bump (z θ : ℝ) : ℝ := zCut z * thCut θ

/-- The strictly positive lower bound of `bump` on the inner box
`[5/8,7/8] × [9π/32,11π/32]`. -/
def innerConst : ℝ :=
  Real.smoothTransition (1 / 8 : ℝ) ^ 2 * Real.smoothTransition (Real.pi / 32) ^ 2

/-! ## The two cut-offs -/

theorem smoothTransition_pos_iff (x : ℝ) : 0 < Real.smoothTransition x ↔ 0 < x := by
  constructor
  · intro h
    by_contra hx
    rw [not_lt] at hx
    rw [Real.smoothTransition.zero_of_nonpos hx] at h
    exact absurd h (lt_irrefl 0)
  · exact Real.smoothTransition.pos_of_pos

theorem zCut_nonneg (z : ℝ) : 0 ≤ zCut z :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem zCut_eq_zero_iff {z : ℝ} : zCut z = 0 ↔ z ≤ 1 / 2 ∨ 1 ≤ z := by
  rw [zCut, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl (by rw [Real.smoothTransition.zero_iff_nonpos] at h; linarith)
    · exact Or.inr (by rw [Real.smoothTransition.zero_iff_nonpos] at h; linarith)
  · rintro (h | h)
    · exact Or.inl (Real.smoothTransition.zero_of_nonpos (by linarith))
    · exact Or.inr (Real.smoothTransition.zero_of_nonpos (by linarith))

theorem zCut_pos_iff {z : ℝ} : 0 < zCut z ↔ z ∈ Set.Ioo (1 / 2) 1 := by
  rw [Set.mem_Ioo]
  constructor
  · intro h
    have hne : ¬ (z ≤ 1 / 2 ∨ 1 ≤ z) := fun hh => (ne_of_gt h) (zCut_eq_zero_iff.mpr hh)
    rcases not_or.mp hne with ⟨h1, h2⟩
    exact ⟨not_le.mp h1, not_le.mp h2⟩
  · rintro ⟨h1, h2⟩
    refine lt_of_le_of_ne (zCut_nonneg z) (Ne.symm fun hh => ?_)
    rcases zCut_eq_zero_iff.mp hh with h | h <;> linarith

theorem thCut_nonneg (θ : ℝ) : 0 ≤ thCut θ :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem thCut_eq_zero_iff {θ : ℝ} :
    thCut θ = 0 ↔ θ ≤ Real.pi / 4 ∨ 3 * Real.pi / 8 ≤ θ := by
  rw [thCut, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl (by rw [Real.smoothTransition.zero_iff_nonpos] at h; linarith)
    · exact Or.inr (by rw [Real.smoothTransition.zero_iff_nonpos] at h; linarith)
  · rintro (h | h)
    · exact Or.inl (Real.smoothTransition.zero_of_nonpos (by linarith))
    · exact Or.inr (Real.smoothTransition.zero_of_nonpos (by linarith))

theorem thCut_pos_iff {θ : ℝ} :
    0 < thCut θ ↔ θ ∈ Set.Ioo (Real.pi / 4) (3 * Real.pi / 8) := by
  rw [Set.mem_Ioo]
  constructor
  · intro h
    have hne : ¬ (θ ≤ Real.pi / 4 ∨ 3 * Real.pi / 8 ≤ θ) :=
      fun hh => (ne_of_gt h) (thCut_eq_zero_iff.mpr hh)
    rcases not_or.mp hne with ⟨h1, h2⟩
    exact ⟨not_le.mp h1, not_le.mp h2⟩
  · rintro ⟨h1, h2⟩
    refine lt_of_le_of_ne (thCut_nonneg θ) (Ne.symm fun hh => ?_)
    rcases thCut_eq_zero_iff.mp hh with h | h <;> linarith

/-! ## The bump profile -/

theorem bump_nonneg (z θ : ℝ) : 0 ≤ bump z θ :=
  mul_nonneg (zCut_nonneg z) (thCut_nonneg θ)

theorem bump_eq_zero_iff {z θ : ℝ} :
    bump z θ = 0 ↔ z ≤ 1 / 2 ∨ 1 ≤ z ∨ θ ≤ Real.pi / 4 ∨ 3 * Real.pi / 8 ≤ θ := by
  rw [bump, mul_eq_zero, zCut_eq_zero_iff, thCut_eq_zero_iff]
  tauto

theorem bump_pos_iff {z θ : ℝ} :
    0 < bump z θ ↔
      z ∈ Set.Ioo (1 / 2) 1 ∧ θ ∈ Set.Ioo (Real.pi / 4) (3 * Real.pi / 8) := by
  rw [show bump z θ = zCut z * thCut θ from rfl]
  constructor
  · intro h
    rcases mul_pos_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨zCut_pos_iff.mp h1, thCut_pos_iff.mp h2⟩
    · exfalso
      have hnn := zCut_nonneg z
      linarith
  · rintro ⟨h1, h2⟩
    exact mul_pos (zCut_pos_iff.mpr h1) (thCut_pos_iff.mpr h2)

theorem bump_ne_zero_iff {z θ : ℝ} :
    bump z θ ≠ 0 ↔
      z ∈ Set.Ioo (1 / 2) 1 ∧ θ ∈ Set.Ioo (Real.pi / 4) (3 * Real.pi / 8) := by
  rw [← bump_pos_iff]
  exact ⟨fun h => lt_of_le_of_ne (bump_nonneg z θ) (Ne.symm h), ne_of_gt⟩

/-- **Support condition**: where `bump` is nonzero both coordinates lie in the open intervals
demanded by the statement of `exists_smooth_supported_HkSq_gt`. -/
theorem bump_support {z θ : ℝ} (h : bump z θ ≠ 0) :
    z ∈ Set.Ioo (1 / 2) 1 ∧ θ ∈ Set.Ioo (Real.pi / 8) (Real.pi / 2) := by
  rw [bump_ne_zero_iff] at h
  exact ⟨h.1, by constructor <;> linarith [h.2.1, h.2.2, Real.pi_pos]⟩

/-! ## Smoothness -/

theorem contDiff_zCut (n : ℕ) : ContDiff ℝ n zCut := by
  have h1 : ContDiff ℝ n (fun z : ℝ => z - (1 / 2 : ℝ)) := contDiff_id.sub contDiff_const
  have h2 : ContDiff ℝ n (fun z : ℝ => (1 : ℝ) - z) := contDiff_const.sub contDiff_id
  exact (Real.smoothTransition.contDiff.comp h1).mul (Real.smoothTransition.contDiff.comp h2)

theorem contDiff_thCut (n : ℕ) : ContDiff ℝ n thCut := by
  have h1 : ContDiff ℝ n (fun θ : ℝ => θ - Real.pi / 4) := contDiff_id.sub contDiff_const
  have h2 : ContDiff ℝ n (fun θ : ℝ => 3 * Real.pi / 8 - θ) := contDiff_const.sub contDiff_id
  exact (Real.smoothTransition.contDiff.comp h1).mul (Real.smoothTransition.contDiff.comp h2)

theorem contDiff_bump (n : ℕ) : ContDiff ℝ n (fun p : ℝ × ℝ => bump p.1 p.2) := by
  have hz : ContDiff ℝ n (fun p : ℝ × ℝ => zCut p.1) := (contDiff_zCut n).comp contDiff_fst
  have hθ : ContDiff ℝ n (fun p : ℝ × ℝ => thCut p.2) := (contDiff_thCut n).comp contDiff_snd
  exact hz.mul hθ

/-- `bump` is `C^∞` on the open quadrant (indeed everywhere). -/
theorem smoothOpen_bump : Work.FTS.EllipticEst.SmoothOpen bump :=
  (Work.FTS.EllipticEst.smoothOpen_iff_forall bump).mpr
    (fun n => (contDiff_bump n).contDiffOn)

/-- Joint continuity of the `ℋ^k`-integrand of `bump` on the open quadrant. -/
theorem continuousOn_HkIntegrand_bump (α : ℝ) (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k bump p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
  smoothOpen_bump.continuousOn_HkIntegrand α k

/-! ## Vanishing of the iterated derivatives off a neighbourhood of the support

The tool is the general Lemma `vanishOn_mixed` below: a function which vanishes on `V ×ˢ W`
(with `V`, `W` open) has all its iterated mixed derivatives vanishing there as well.  Applying
it to `bump` on the four half-plane pieces complementary to `[1/2,1] × [π/4,3π/8]` gives the
vanishing of the whole `ℋ^k`-integrand outside that closed box. -/

theorem vanishOn_pz {g : ℝ → ℝ → ℝ} {V W : Set ℝ} (hV : IsOpen V) (hW : IsOpen W)
    (h : ∀ z' ∈ V, ∀ θ' ∈ W, g z' θ' = 0) :
    ∀ z' ∈ V, ∀ θ' ∈ W, Work.Spaces.pz g z' θ' = 0 := by
  intro z' hz' θ' hθ'
  have he : (fun z'' : ℝ => g z'' θ') =ᶠ[𝓝 z'] fun _ => (0 : ℝ) := by
    filter_upwards [hV.mem_nhds hz'] with z'' hz''
    exact h z'' hz'' θ' hθ'
  simp only [Work.Spaces.pz]
  rw [he.deriv_eq, deriv_const]

theorem vanishOn_pth {g : ℝ → ℝ → ℝ} {V W : Set ℝ} (hV : IsOpen V) (hW : IsOpen W)
    (h : ∀ z' ∈ V, ∀ θ' ∈ W, g z' θ' = 0) :
    ∀ z' ∈ V, ∀ θ' ∈ W, Work.Spaces.pth g z' θ' = 0 := by
  intro z' hz' θ' hθ'
  have he : (fun θ'' : ℝ => g z' θ'') =ᶠ[𝓝 θ'] fun _ => (0 : ℝ) := by
    filter_upwards [hW.mem_nhds hθ'] with θ'' hθ''
    exact h z' hz' θ'' hθ''
  simp only [Work.Spaces.pth]
  rw [he.deriv_eq, deriv_const]

theorem vanishOn_DzIter {g : ℝ → ℝ → ℝ} {V W : Set ℝ} (hV : IsOpen V) (hW : IsOpen W)
    (h : ∀ z' ∈ V, ∀ θ' ∈ W, g z' θ' = 0) (j : ℕ) :
    ∀ z' ∈ V, ∀ θ' ∈ W, Work.Spaces.DzIter j g z' θ' = 0 := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro z' hz' θ' hθ'
    have hpz := vanishOn_pz hV hW ih z' hz' θ' hθ'
    rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, hpz, mul_zero]

theorem vanishOn_DthIter {g : ℝ → ℝ → ℝ} {V W : Set ℝ} (hV : IsOpen V) (hW : IsOpen W)
    (h : ∀ z' ∈ V, ∀ θ' ∈ W, g z' θ' = 0) (i : ℕ) :
    ∀ z' ∈ V, ∀ θ' ∈ W, Work.Spaces.DthIter i g z' θ' = 0 := by
  induction i with
  | zero => exact h
  | succ i ih =>
    intro z' hz' θ' hθ'
    have hpth := vanishOn_pth hV hW ih z' hz' θ' hθ'
    rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth, hpth, mul_zero]

/-- If `g` vanishes on `V ×ˢ W` with `V`, `W` open, then so does every iterated mixed
derivative `D_z^j D_θ^i g`. -/
theorem vanishOn_mixed {g : ℝ → ℝ → ℝ} {V W : Set ℝ} (hV : IsOpen V) (hW : IsOpen W)
    (h : ∀ z' ∈ V, ∀ θ' ∈ W, g z' θ' = 0) (j i : ℕ) :
    ∀ z' ∈ V, ∀ θ' ∈ W, Work.Spaces.DzIter j (Work.Spaces.DthIter i g) z' θ' = 0 :=
  vanishOn_DzIter hV hW (vanishOn_DthIter hV hW h i) j

theorem bump_zCut_eq_zero_of_lt {z : ℝ} (hz : z < 1 / 2) : zCut z = 0 := by
  rw [zCut, Real.smoothTransition.zero_of_nonpos (by linarith : z - 1 / 2 ≤ 0), zero_mul]

theorem bump_zCut_eq_zero_of_gt {z : ℝ} (hz : 1 < z) : zCut z = 0 := by
  rw [zCut, Real.smoothTransition.zero_of_nonpos (by linarith : 1 - z ≤ 0), mul_zero]

theorem bump_thCut_eq_zero_of_lt {θ : ℝ} (hθ : θ < Real.pi / 4) : thCut θ = 0 := by
  rw [thCut, Real.smoothTransition.zero_of_nonpos (by linarith : θ - Real.pi / 4 ≤ 0), zero_mul]

theorem bump_thCut_eq_zero_of_gt {θ : ℝ} (hθ : 3 * Real.pi / 8 < θ) : thCut θ = 0 := by
  rw [thCut, Real.smoothTransition.zero_of_nonpos (by linarith : 3 * Real.pi / 8 - θ ≤ 0),
    mul_zero]

/-- Every iterated mixed derivative of `bump` vanishes at `(z,θ)` as soon as `z` or `θ` lies
strictly outside the support box `[1/2,1] × [π/4,3π/8]`. -/
theorem bump_iter_eq_zero_of_not_mem {z θ : ℝ}
    (h : z < 1 / 2 ∨ 1 < z ∨ θ < Real.pi / 4 ∨ 3 * Real.pi / 8 < θ) (j i : ℕ) :
    Work.Spaces.DzIter j (Work.Spaces.DthIter i bump) z θ = 0 := by
  rcases h with hz | hz | hθ | hθ
  · exact vanishOn_mixed isOpen_Iio isOpen_univ
      (fun z' hz' θ' _ => by rw [bump, bump_zCut_eq_zero_of_lt hz', zero_mul])
      j i z hz θ (Set.mem_univ θ)
  · exact vanishOn_mixed isOpen_Ioi isOpen_univ
      (fun z' hz' θ' _ => by rw [bump, bump_zCut_eq_zero_of_gt hz', zero_mul])
      j i z hz θ (Set.mem_univ θ)
  · exact vanishOn_mixed isOpen_univ isOpen_Iio
      (fun z' _ θ' hθ' => by rw [bump, bump_thCut_eq_zero_of_lt hθ', mul_zero])
      j i z (Set.mem_univ z) θ hθ
  · exact vanishOn_mixed isOpen_univ isOpen_Ioi
      (fun z' _ θ' hθ' => by rw [bump, bump_thCut_eq_zero_of_gt hθ', mul_zero])
      j i z (Set.mem_univ z) θ hθ

/-- The `ℋ^k`-integrand of `bump` vanishes outside the closed box
`[1/2,1] × [π/4,3π/8]`. -/
theorem HkIntegrand_bump_eq_zero_of_not_mem (α : ℝ) (k : ℕ) {z θ : ℝ}
    (h : z < 1 / 2 ∨ 1 < z ∨ θ < Real.pi / 4 ∨ 3 * Real.pi / 8 < θ) :
    Work.Spaces.HkIntegrand α k bump z θ = 0 := by
  have hz := bump_iter_eq_zero_of_not_mem h
  rw [Work.Spaces.HkIntegrand]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i bump z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [show Work.Spaces.DzIter i bump z θ = 0 from by
        simpa only [Work.Spaces.DthIter_zero] using hz i 0]
      ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i bump z θ * Work.Spaces.Wt α z θ) ^ 2
      else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hc, show Work.Spaces.mixed j i bump z θ = 0 from hz j i]; ring
      · rw [if_neg hc]
  rw [h1, h2, add_zero]

/-! ## The support box, the inner box, and the corresponding subsets -/

theorem box_subset_Q0 :
    Set.Icc ((1 : ℝ) / 2) 1 ×ˢ Set.Icc (Real.pi / 4) (3 * Real.pi / 8)
      ⊆ Work.FTS.EllipticEst.Q0 := by
  rintro ⟨z, θ⟩ hp
  rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hp
  rw [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
  exact ⟨by linarith [hp.1.1], by linarith [hp.2.1, Real.pi_pos],
    by linarith [hp.2.2, Real.pi_pos]⟩

/-- The integrand of `bump` is bounded by a constant (its maximum on the compact support box);
outside the box it vanishes. -/
theorem exists_bound_HkIntegrand_bump (α : ℝ) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z θ : ℝ, Work.Spaces.HkIntegrand α k bump z θ ≤ M := by
  obtain ⟨p₀, -, hp₀max⟩ :=
    (isCompact_Icc.prod isCompact_Icc :
        IsCompact (Set.Icc ((1 : ℝ) / 2) 1 ×ˢ Set.Icc (Real.pi / 4) (3 * Real.pi / 8)))
      |>.exists_isMaxOn ⟨(3 / 4, Real.pi / 4), by
        rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
        exact ⟨⟨by norm_num, by norm_num⟩, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩⟩⟩
      ((continuousOn_HkIntegrand_bump α k).mono box_subset_Q0)
  refine ⟨Work.Spaces.HkIntegrand α k bump p₀.1 p₀.2,
    Work.Spaces.HkIntegrand_nonneg α k bump p₀.1 p₀.2, fun z θ => ?_⟩
  by_cases h : (z, θ) ∈ Set.Icc ((1 : ℝ) / 2) 1 ×ˢ Set.Icc (Real.pi / 4) (3 * Real.pi / 8)
  · exact hp₀max h
  · have h' : z < 1 / 2 ∨ 1 < z ∨ θ < Real.pi / 4 ∨ 3 * Real.pi / 8 < θ := by
      simp only [Set.mem_prod, Set.mem_Icc, not_and_or, not_le] at h
      tauto
    rw [HkIntegrand_bump_eq_zero_of_not_mem α k h']
    exact Work.Spaces.HkIntegrand_nonneg α k bump p₀.1 p₀.2

/-! ## Strict positivity on the inner box -/

theorem innerConst_pos : 0 < innerConst := by
  rw [innerConst]
  exact mul_pos (pow_pos (Real.smoothTransition.pos_of_pos (by norm_num)) 2)
    (pow_pos (Real.smoothTransition.pos_of_pos (by linarith [Real.pi_pos])) 2)

/-- On the inner box `[5/8,7/8] × [9π/32,11π/32]` the bump is bounded below by `innerConst`. -/
theorem bump_ge_innerConst {z θ : ℝ} (hz1 : (5 : ℝ) / 8 ≤ z) (hz2 : z ≤ (7 : ℝ) / 8)
    (hθ1 : 9 * Real.pi / 32 ≤ θ) (hθ2 : θ ≤ 11 * Real.pi / 32) :
    innerConst ≤ bump z θ := by
  have h1 : Real.smoothTransition (1 / 8 : ℝ) ≤ Real.smoothTransition (z - 1 / 2) :=
    Real.smoothTransition.monotone (by linarith)
  have h2 : Real.smoothTransition (1 / 8 : ℝ) ≤ Real.smoothTransition (1 - z) :=
    Real.smoothTransition.monotone (by linarith)
  have h3 : Real.smoothTransition (Real.pi / 32) ≤ Real.smoothTransition (θ - Real.pi / 4) :=
    Real.smoothTransition.monotone (by linarith)
  have h4 : Real.smoothTransition (Real.pi / 32) ≤ Real.smoothTransition (3 * Real.pi / 8 - θ) :=
    Real.smoothTransition.monotone (by linarith)
  have hnn1 : 0 ≤ Real.smoothTransition (1 / 8 : ℝ) := Real.smoothTransition.nonneg _
  have hnn3 : 0 ≤ Real.smoothTransition (Real.pi / 32) := Real.smoothTransition.nonneg _
  simp only [bump, zCut, thCut, innerConst, pow_two]
  exact mul_le_mul (mul_le_mul h1 h2 hnn1 (Real.smoothTransition.nonneg _))
    (mul_le_mul h3 h4 hnn3 (Real.smoothTransition.nonneg _))
    (mul_nonneg hnn3 (Real.smoothTransition.nonneg _))
    (mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))

theorem innerBox_subset_Iz :
    Set.Icc ((5 : ℝ) / 8) ((7 : ℝ) / 8) ⊆ Work.Spaces.Iz :=
  fun _ hx => by rw [Work.Spaces.Iz, Set.mem_Ici]; linarith [hx.1]

theorem innerBox_subset_Iθ :
    Set.Icc (9 * Real.pi / 32) (11 * Real.pi / 32) ⊆ Work.Spaces.Iθ := by
  intro θ hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc]
  exact ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩

/-- The `ℋ^k`-integrand of `bump` is strictly positive on the inner box. -/
theorem HkIntegrand_bump_pos_of_inner (α : ℝ) (k : ℕ) {z θ : ℝ}
    (hz : z ∈ Set.Icc ((5 : ℝ) / 8) ((7 : ℝ) / 8))
    (hθ : θ ∈ Set.Icc (9 * Real.pi / 32) (11 * Real.pi / 32)) :
    0 < Work.Spaces.HkIntegrand α k bump z θ := by
  have hzpos : 0 < z := by linarith [hz.1]
  have hbump : 0 < bump z θ :=
    lt_of_lt_of_le innerConst_pos (bump_ge_innerConst hz.1 hz.2 hθ.1 hθ.2)
  have hw : 0 < Work.Spaces.w z := by
    rw [Work.Spaces.w]
    exact div_pos (pow_pos (by linarith) 2) (pow_pos hzpos 2)
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
      (by linarith [hθ.2, Real.pi_pos])
  have hwdiv : 0 < Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    div_pos hw (Real.rpow_pos_of_pos hsin _)
  have hterm : 0 < (bump z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    pow_pos (mul_pos hbump hwdiv) 2
  refine lt_of_lt_of_le hterm ?_
  simpa only [Work.Spaces.DzIter_zero] using
    Work.Spaces.sq_le_HkIntegrand_z α k bump z θ 0 (Nat.zero_le k)

end Work.FTS.StrongEps
