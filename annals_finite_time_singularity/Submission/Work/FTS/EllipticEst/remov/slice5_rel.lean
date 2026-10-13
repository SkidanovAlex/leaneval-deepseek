/-
Copyright: work module for the Elgindi finite-time singularity project.

# Relations between `u` and `v = u / cos θ` on `(0, π/2)`

This module collects, in the *weak* setting used by `slice_step5` (only
`ContDiffOn ℝ 4 u (Ioo 0 (π/2))` and the ODE `Lzero1 u = g` on `(0, π/2)`), all the
identities linking the derivatives of `u` to those of

  `v := fun θ => u θ / Real.cos θ`.

Write `S = sin θ`, `C = cos θ`.  The pure-algebra (product-rule) identities are

* `u''    = -C v - 2 S v' + C v''`,
* `u'''   =  S v - 3 C v' - 3 S v'' + C v'''`,
* `u''''  =  C v - 4 S v' - 6 C v'' - 4 S v''' + C v''''`,

and combining these with `slice5_idents` (`u'' = S v' - 5 C v - g`, etc.) gives the
relations that the Step-5 computation uses:

* `C v''  = u'' + u + 2 S v'`,
* `C v''  = 3 u'' + 11 u + 2 g`,
* `S v'   = u'' + 5 u + g`,
* `S v''  = u''' + 4 C v' - 5 S v + g'`,
* `C v''' = u''' - S v + 3 C v' + 3 S v''`,
* `C v''' = 4 u''' + 15 C v' - 16 S v + 3 g'`,
* `C v''' = 4 u''' + 15 u' - S v + 3 g'`,
* `S v    = tan θ · u`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.cosBarIdents
import Submission.Work.FTS.EllipticEst.remov.slice5_idents

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-- `v = u / cos θ`, the `cosBar` function of the paper's Step 5. -/
def cbV (u : ℝ → ℝ) : ℝ → ℝ := fun θ => u θ / Real.cos θ

lemma cbV_apply (u : ℝ → ℝ) : cbV u = fun θ => u θ / Real.cos θ := rfl

lemma cos_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩

/-- `cos θ * (u θ / cos θ) = u θ` on `(0, π/2)`. -/
lemma cos_mul_cbV {u : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos θ * (u θ / Real.cos θ) = u θ := by
  field_simp [(cos_pos_of_mem_Ioo hθ).ne']

/-- `(cos θ · v)' = -sin θ · v + cos θ · v'`, i.e. `u' = -S v + C v'`. -/
lemma slice5_v_rel_one (u : ℝ → ℝ) (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv u θ
        = -Real.sin θ * (u θ / Real.cos θ)
          + Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ := by
  intro θ hθ
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hcos_ne : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos t ≠ 0 :=
    fun t ht => (cos_pos_of_mem_Ioo ht).ne'
  have hψC : ContDiffOn ℝ 4 (fun θ' => u θ' / Real.cos θ') (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.div Real.contDiff_cos.contDiffOn hcos_ne
  have hV : HasDerivAt (fun θ' => u θ' / Real.cos θ')
      (deriv (fun θ' => u θ' / Real.cos θ') θ) θ :=
    ((hψC.contDiffAt hIoo).differentiableAt (by norm_num)).hasDerivAt
  have hev : u =ᶠ[𝓝 θ] fun t => Real.cos t * (u t / Real.cos t) := by
    filter_upwards [hIoo] with t ht
    exact (cos_mul_cbV ht).symm
  have hd : HasDerivAt (fun t => Real.cos t * (u t / Real.cos t))
      (-Real.sin θ * (u θ / Real.cos θ) + Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ) θ :=
    (Real.hasDerivAt_cos θ).mul hV
  rw [hev.deriv_eq, hd.deriv]

/-- `sin θ · v = tan θ · u`. -/
lemma slice5_v_rel_tan (u : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sin θ * (u θ / Real.cos θ) = Real.tan θ * u θ := by
  have hcos : Real.cos θ ≠ 0 := (cos_pos_of_mem_Ioo hθ).ne'
  simp only [Real.tan_eq_sin_div_cos]
  field_simp

/-- **Pure-algebra expansions.**  On `(0, π/2)`, `u = cos θ · v` with `v = u / cos θ`,
so the second, third and fourth derivatives of `u` are the corresponding Leibniz
combinations of `cos` and `v`. -/
theorem slice5_v_rel_pure (u : ℝ → ℝ) (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (deriv (deriv u) θ
          = -Real.cos θ * (u θ / Real.cos θ)
            - 2 * Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
            + Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ) ∧
      (deriv (deriv (deriv u)) θ
          = Real.sin θ * (u θ / Real.cos θ)
            - 3 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
            - 3 * Real.sin θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
            + Real.cos θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ) ∧
      (deriv (deriv (deriv (deriv u))) θ
          = Real.cos θ * (u θ / Real.cos θ)
            + 4 * Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
            - 6 * Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
            - 4 * Real.sin θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
            + Real.cos θ * deriv (deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ')))) θ) := by
  intro θ hθ
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hcos_ne : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos t ≠ 0 :=
    fun t ht => (cos_pos_of_mem_Ioo ht).ne'
  set ψ : ℝ → ℝ := fun θ' => u θ' / Real.cos θ' with hψ
  have hψC : ContDiffOn ℝ 4 ψ (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.div Real.contDiff_cos.contDiffOn hcos_ne
  have hψAt : ContDiffAt ℝ 4 ψ θ := hψC.contDiffAt hIoo
  have hev : u =ᶠ[𝓝 θ] fun t => Real.cos t * ψ t := by
    filter_upwards [hIoo] with t ht
    exact (cos_mul_cbV ht).symm
  have h2 : iteratedDeriv 2 u θ
      = -Real.cos θ * ψ θ - 2 * Real.sin θ * iteratedDeriv 1 ψ θ
        + Real.cos θ * iteratedDeriv 2 ψ θ := by
    rw [hev.iteratedDeriv_eq 2]
    exact itd_cos_two ψ θ (hψAt.of_le (by norm_num))
  have h3 : iteratedDeriv 3 u θ
      = Real.sin θ * ψ θ - 3 * Real.cos θ * iteratedDeriv 1 ψ θ
        - 3 * Real.sin θ * iteratedDeriv 2 ψ θ
        + Real.cos θ * iteratedDeriv 3 ψ θ := by
    rw [hev.iteratedDeriv_eq 3]
    exact itd_cos_three ψ θ (hψAt.of_le (by norm_num))
  have h4 : iteratedDeriv 4 u θ
      = Real.cos θ * ψ θ + 4 * Real.sin θ * iteratedDeriv 1 ψ θ
        - 6 * Real.cos θ * iteratedDeriv 2 ψ θ
        - 4 * Real.sin θ * iteratedDeriv 3 ψ θ
        + Real.cos θ * iteratedDeriv 4 ψ θ := by
    rw [hev.iteratedDeriv_eq 4]
    exact itd_cos_four ψ θ hψAt
  refine ⟨?_, ?_, ?_⟩
  · rw [← itd_two_val u θ, h2, iteratedDeriv_one, itd_two_val ψ θ]
  · rw [← itd_three_val u θ, h3, iteratedDeriv_one, itd_two_val ψ θ, itd_three_val ψ θ]
  · rw [← itd_four_val u θ, h4, iteratedDeriv_one, itd_two_val ψ θ, itd_three_val ψ θ,
      itd_four_val ψ θ]

/-- The full set of `u`-`v` relations used by the Step-5 computation. -/
theorem slice5_v_rel (u g : ℝ → ℝ)
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (deriv u θ = -Real.sin θ * (u θ / Real.cos θ)
          + Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ) ∧
      (Real.sin θ * (u θ / Real.cos θ) = Real.tan θ * u θ) ∧
      (Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
        = deriv (deriv u) θ + 5 * u θ + g θ) ∧
      (Real.sin θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
        = deriv (deriv (deriv u)) θ
          + 4 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
          - 5 * Real.sin θ * (u θ / Real.cos θ) + deriv g θ) ∧
      (Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
        = deriv (deriv u) θ + u θ
          + 2 * Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ) ∧
      (Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
        = 3 * deriv (deriv u) θ + 11 * u θ + 2 * g θ) ∧
      (Real.cos θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
        = deriv (deriv (deriv u)) θ - Real.sin θ * (u θ / Real.cos θ)
          + 3 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
          + 3 * Real.sin θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ) ∧
      (Real.cos θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
        = 4 * deriv (deriv (deriv u)) θ
          + 15 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
          - 16 * Real.sin θ * (u θ / Real.cos θ) + 3 * deriv g θ) ∧
      (Real.cos θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
        = 4 * deriv (deriv (deriv u)) θ + 15 * deriv u θ
          - Real.sin θ * (u θ / Real.cos θ) + 3 * deriv g θ) := by
  intro θ hθ
  have hid := slice5_idents u g hu hode
  have hrel := slice5_v_rel_pure u hu θ hθ
  have hone := slice5_v_rel_one u hu θ hθ
  have htan := slice5_v_rel_tan u hθ
  have hCV : Real.cos θ * (u θ / Real.cos θ) = u θ := cos_mul_cbV hθ
  have h1 := hid.2.1 θ hθ
  have h2 := hid.2.2.1 θ hθ
  have hp2 := hrel.1
  have hp3 := hrel.2.1
  have hS1 : Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
      = deriv (deriv u) θ + 5 * u θ + g θ := by
    linear_combination -h1 + 5 * hCV
  have hS2 : Real.sin θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
      = deriv (deriv (deriv u)) θ
        + 4 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
        - 5 * Real.sin θ * (u θ / Real.cos θ) + deriv g θ := by
    linear_combination -h2
  have hC2 : Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
      = deriv (deriv u) θ + u θ
        + 2 * Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ := by
    linear_combination -hp2 + hCV
  have hC2' : Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
      = 3 * deriv (deriv u) θ + 11 * u θ + 2 * g θ := by
    linear_combination hC2 + 2 * hS1
  have hC3 : Real.cos θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
      = deriv (deriv (deriv u)) θ - Real.sin θ * (u θ / Real.cos θ)
        + 3 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
        + 3 * Real.sin θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ := by
    linear_combination -hp3
  have hC3' : Real.cos θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
      = 4 * deriv (deriv (deriv u)) θ
        + 15 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
        - 16 * Real.sin θ * (u θ / Real.cos θ) + 3 * deriv g θ := by
    linear_combination hC3 + 3 * hS2
  have hC3'' : Real.cos θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
      = 4 * deriv (deriv (deriv u)) θ + 15 * deriv u θ
        - Real.sin θ * (u θ / Real.cos θ) + 3 * deriv g θ := by
    have hCV1 : Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
        = deriv u θ + Real.sin θ * (u θ / Real.cos θ) := by
      linear_combination -hone
    linear_combination hC3' + 15 * hCV1
  exact ⟨hone, htan, hS1, hS2, hC2, hC2', hC3, hC3', hC3''⟩

/-! ## Extractions -/

lemma slice5_v_SV1 (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
        = deriv (deriv u) θ + 5 * u θ + g θ :=
  fun θ hθ => (slice5_v_rel u g hu hode θ hθ).2.2.1

lemma slice5_v_SV2 (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.sin θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
        = deriv (deriv (deriv u)) θ
          + 4 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
          - 5 * Real.sin θ * (u θ / Real.cos θ) + deriv g θ :=
  fun θ hθ => (slice5_v_rel u g hu hode θ hθ).2.2.2.1

lemma slice5_v_CV2 (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
        = deriv (deriv u) θ + u θ
          + 2 * Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ :=
  fun θ hθ => (slice5_v_rel u g hu hode θ hθ).2.2.2.2.1

lemma slice5_v_CV2' (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
        = 3 * deriv (deriv u) θ + 11 * u θ + 2 * g θ :=
  fun θ hθ => (slice5_v_rel u g hu hode θ hθ).2.2.2.2.2.1

lemma slice5_v_CV3 (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.cos θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
        = deriv (deriv (deriv u)) θ - Real.sin θ * (u θ / Real.cos θ)
          + 3 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
          + 3 * Real.sin θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ :=
  fun θ hθ => (slice5_v_rel u g hu hode θ hθ).2.2.2.2.2.2.1

lemma slice5_v_CV3' (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.cos θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
        = 4 * deriv (deriv (deriv u)) θ
          + 15 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
          - 16 * Real.sin θ * (u θ / Real.cos θ) + 3 * deriv g θ :=
  fun θ hθ => (slice5_v_rel u g hu hode θ hθ).2.2.2.2.2.2.2.1

lemma slice5_v_CV3'' (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.cos θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
        = 4 * deriv (deriv (deriv u)) θ + 15 * deriv u θ
          - Real.sin θ * (u θ / Real.cos θ) + 3 * deriv g θ :=
  fun θ hθ => (slice5_v_rel u g hu hode θ hθ).2.2.2.2.2.2.2.2

/-- **Expansion of the third derivative of `tan θ · u`.**  Since `tan θ · u = sin θ · v`
with `v = u / cos θ`, the third derivative expands as
`S v_3 + 3 C v_2 - 3 S v_1 - C v` (where `v_j` is the `j`-th derivative of `v`). -/
lemma slice5_tanu3_weak (u : ℝ → ℝ) (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv (deriv (fun t => Real.tan t * u t))) θ
        = Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ
          + 3 * Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ
          - 3 * Real.sin θ * deriv (fun t => u t / Real.cos t) θ
          - Real.cos θ * (u θ / Real.cos θ) := by
  intro θ hθ
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hcos_ne : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos t ≠ 0 :=
    fun t ht => (cos_pos_of_mem_Ioo ht).ne'
  have hψC : ContDiffOn ℝ 4 (fun t => u t / Real.cos t) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.div Real.contDiff_cos.contDiffOn hcos_ne
  have hψAt : ContDiffAt ℝ 3 (fun t => u t / Real.cos t) θ :=
    (hψC.contDiffAt hIoo).of_le (by norm_num)
  have hev : (fun t => Real.tan t * u t) =ᶠ[𝓝 θ] fun t => Real.sin t * (u t / Real.cos t) := by
    filter_upwards [hIoo] with t ht
    have hc : Real.cos t ≠ 0 := hcos_ne t ht
    simp only [Real.tan_eq_sin_div_cos]
    field_simp
  have h2 : iteratedDeriv 3 (fun t => Real.tan t * u t) θ
      = -Real.cos θ * (u θ / Real.cos θ)
        - 3 * Real.sin θ * iteratedDeriv 1 (fun t => u t / Real.cos t) θ
        + 3 * Real.cos θ * iteratedDeriv 2 (fun t => u t / Real.cos t) θ
        + Real.sin θ * iteratedDeriv 3 (fun t => u t / Real.cos t) θ := by
    rw [hev.iteratedDeriv_eq 3]
    exact itd_sin_three (fun t => u t / Real.cos t) θ hψAt
  rw [← itd_three_val (fun t => Real.tan t * u t) θ, h2, iteratedDeriv_one,
    itd_two_val (fun t => u t / Real.cos t) θ, itd_three_val (fun t => u t / Real.cos t) θ]
  ring

end Work.FTS.EllipticEst.remov
