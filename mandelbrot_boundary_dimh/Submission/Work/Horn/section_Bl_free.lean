import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.deep_preimage_deep
import Submission.Work.L62.lift_section
import Submission.Work.L62.section_unique

/-!
# Free-parameter version of the lower-horn section (`section_Bl_free`)

This is the textbook Lemma 5.3/Lemma 5.4 section for the lower end, stated without the
`ParabData`/`HornData` packaging: given an open, simply connected, `T`-invariant domain `D`
containing a lower half plane `{w | w.im < -η}`, a holomorphic `E` on `D` with
`E (w + 1) = E w + 1` which is a covering map onto `ℂ ∖ (v + ℤ)` and whose lower-end translation
constant is `cl`, there is a global holomorphic section `σ` of `E` over `D` with `σ (y + 1) =
σ y + 1` and `σ w - w + cl → 0` at the lower end.

The proof is the same as the one of `Work.L62.section_Bl` (`β = 0`, free parameters):

1. `g := E - id - cl` is holomorphic on `D`, is `1`-periodic and tends to `0` at the lower end,
   so `Work.L62.deep_preimage_deep` provides a holomorphic inverse branch `u` of `E` on a deep
   half plane, together with uniqueness of the solution in a deeper half plane and the
   normalisation `u z - z + cl → 0`.
2. `u` is `T`-equivariant on that half plane (uniqueness of the deep solution).
3. `Work.L62.lift_section` extends `u` (restricted to a still deeper half plane) to a global
   holomorphic section `σ` of `E` over the simply connected `D`.
4. `Work.L62.section_unique` identifies `σ` with `u` on the deep half plane, transfers the
   `T`-equivariance to all of `D`, and transfers the lower-end normalisation.
-/

namespace Work.Horn

set_option linter.style.haveILetI false

open MandelDim Set Filter Topology Complex
open scoped Topology

noncomputable section

theorem section_Bl_free {E : ℂ → ℂ} {D : Set ℂ} {cl : ℂ} {η : ℝ} {v : ℂ}
    (hDopen : IsOpen D) (hDsc : SimplyConnectedSpace D)
    (hT : MandelDim.IsTInvariant D)
    (hlow : {w : ℂ | w.im < -η} ⊆ D)
    (hEhol : DifferentiableOn ℂ E D)
    (hEeq : ∀ w ∈ D, E (w + 1) = E w + 1)
    (hcov : IsCoveringMapOn (fun z : D => E z) {y : ℂ | ∀ k : ℤ, y ≠ v + k})
    (havoid : ∀ w ∈ D, ∀ k : ℤ, w ≠ v + k)
    (hcl : Filter.Tendsto (fun w => E w - w) MandelDim.lowerEnd (nhds cl)) :
    ∃ (y₀ x₀ : ℂ) (σ : ℂ → ℂ), y₀ ∈ D ∧ x₀ ∈ D ∧ E x₀ = y₀ ∧
      DifferentiableOn ℂ σ D ∧ σ y₀ = x₀ ∧
      (∀ y ∈ D, σ y ∈ D ∧ E (σ y) = y) ∧
      (∀ y ∈ D, σ (y + 1) = σ y + 1) ∧
      Filter.Tendsto (fun w => σ w - w + cl) MandelDim.lowerEnd (nhds 0) := by
  classical
  haveI : SimplyConnectedSpace D := hDsc
  -- (0) the covering over `D` itself
  have hcovD : IsCoveringMapOn (fun z : D => E z) D :=
    hcov.mono (fun y hy k => havoid y hy k)
  -- (1) the deep inverse branch of `E`
  have hgdiff : DifferentiableOn ℂ (fun w => E w - w - cl) D :=
    (hEhol.sub differentiableOn_id).sub_const cl
  have hglim : Filter.Tendsto (fun w => E w - w - cl) MandelDim.lowerEnd (nhds 0) := by
    have h1 := hcl.sub_const cl
    simpa using h1
  obtain ⟨L, Lz, hLY, _hL0, _hLz0, u, hu_diff, hu_mem, hu_uniq, hu_tend⟩ :=
    Work.L62.deep_preimage_deep (D := D) (g := fun w => E w - w - cl) (c := cl) (Y := -η)
      hDopen hlow hgdiff hglim 0 0
  -- (2) the deep section `u` and its properties
  have hσH_mem : ∀ y : ℂ, y.im < Lz → u y ∈ D :=
    fun y hy => hlow (lt_trans (hu_mem y hy).1 hLY)
  have hσH_sec : ∀ y : ℂ, y.im < Lz → E (u y) = y := by
    intro y hy
    have h1 : u y + cl + (E (u y) - u y - cl) = y := (hu_mem y hy).2
    have h2 : u y + cl + (E (u y) - u y - cl) = E (u y) := by ring
    rw [h2] at h1
    exact h1
  have hσH_T : ∀ y : ℂ, y.im < Lz → u (y + 1) = u y + 1 := by
    intro y hy
    have hz : (y + 1).im < Lz := by
      rw [Complex.add_im, Complex.one_im, add_zero]
      exact hy
    have hv : (u y + 1).im < L := by
      rw [Complex.add_im, Complex.one_im, add_zero]
      exact (hu_mem y hy).1
    refine (hu_uniq (y + 1) hz (u y + 1) hv ?_).symm
    have hT1 : E (u y + 1) = E (u y) + 1 := hEeq (u y) (hσH_mem y hy)
    have hEy : E (u y) = y := hσH_sec y hy
    rw [hT1, hEy]
    ring
  -- (3) the extension of the deep section to all of `D`
  set c : ℝ := min Lz (-η) with hc
  have hc_le1 : c ≤ Lz := by rw [hc]; exact min_le_left _ _
  have hc_le2 : c ≤ -η := by rw [hc]; exact min_le_right _ _
  have hYd_sub_deep : {y : ℂ | y.im < c} ⊆ {y : ℂ | y.im < Lz} :=
    fun y hy => lt_of_lt_of_le hy hc_le1
  have hYd_sub_D : {y : ℂ | y.im < c} ⊆ D :=
    fun y hy => hlow (lt_of_lt_of_le hy hc_le2)
  have hYd_open : IsOpen {y : ℂ | y.im < c} := isOpen_lt Complex.continuous_im continuous_const
  have hYd_pc : IsPreconnected {y : ℂ | y.im < c} := (convex_halfSpace_im_lt c).isPreconnected
  set y₁ : ℂ := ((c - 1 : ℝ) : ℂ) * I with hy₁
  have hy₁_mem : (y₁ : ℂ).im < c := by
    rw [hy₁]
    simp only [Complex.mul_I_im, Complex.ofReal_re]
    linarith
  have hy₁_D : y₁ ∈ D := hYd_sub_D hy₁_mem
  set x₁ : ℂ := u y₁ with hx₁
  have hx₁_mem : x₁ ∈ D := hσH_mem y₁ (hYd_sub_deep hy₁_mem)
  have hx₁_sec : E x₁ = y₁ := hσH_sec y₁ (hYd_sub_deep hy₁_mem)
  obtain ⟨σ, hσ_diff, hσ_y₁, hσ_sec⟩ :=
    Work.L62.lift_section (X := D) hDopen (p := E) hEhol
      (Y := D) hDopen hDsc hcovD hy₁_D hx₁_mem hx₁_sec
  -- (4) identify `σ` with the deep section on the deep half plane
  have hσ_eq : ∀ y ∈ {y : ℂ | y.im < c}, σ y = u y :=
    Work.L62.section_unique (X := D) hDopen hYd_open hYd_pc hYd_sub_D hEhol
      (hσ_diff.mono hYd_sub_D) (hu_diff.mono hYd_sub_deep)
      (fun y hy => hσ_sec y (hYd_sub_D hy))
      (fun y hy => ⟨hσH_mem y (hYd_sub_deep hy), hσH_sec y (hYd_sub_deep hy)⟩)
      hy₁_mem (by rw [hσ_y₁, hx₁])
  have hy₁1_mem : (y₁ + 1).im < c := by
    rw [Complex.add_im, Complex.one_im, add_zero]
    exact hy₁_mem
  have hσ_eq_y₁1 : σ (y₁ + 1) = u (y₁ + 1) := hσ_eq (y₁ + 1) hy₁1_mem
  -- (5) `T`-equivariance of `σ` on all of `D`
  have hσ_T : ∀ y ∈ D, σ (y + 1) = σ y + 1 := by
    have hs₁_diff : DifferentiableOn ℂ (fun y => σ (y + 1) - 1) D :=
      ((hσ_diff.comp (differentiableOn_id.add_const 1)
        (fun y hy => (hT y).mp hy))).sub_const 1
    have hs₁_sec : ∀ y ∈ D, (σ (y + 1) - 1) ∈ D ∧ E (σ (y + 1) - 1) = y := by
      intro y hy
      have hy1 : y + 1 ∈ D := (hT y).mp hy
      have h1 : σ (y + 1) ∈ D := (hσ_sec (y + 1) hy1).1
      have h2 : E (σ (y + 1)) = y + 1 := (hσ_sec (y + 1) hy1).2
      have hw : σ (y + 1) - 1 ∈ D := (hT (σ (y + 1) - 1)).mpr (by simpa using h1)
      have h3 := hEeq (σ (y + 1) - 1) hw
      have harg : σ (y + 1) - 1 + 1 = σ (y + 1) := by ring
      rw [harg] at h3
      refine ⟨hw, ?_⟩
      have h6 : E (σ (y + 1) - 1) = E (σ (y + 1)) - 1 := (eq_sub_iff_add_eq).mpr h3.symm
      rw [h6, h2]
      ring
    have hss : ∀ y ∈ D, (fun y => σ (y + 1) - 1) y = σ y :=
      Work.L62.section_unique (X := D) hDopen hDopen
        (isPreconnected_iff_preconnectedSpace.mpr (inferInstance : PreconnectedSpace D))
        (subset_refl D) hEhol hs₁_diff hσ_diff hs₁_sec hσ_sec hy₁_D ?_
    · intro y hy
      have h := hss y hy
      show σ (y + 1) = σ y + 1
      rw [← h]
      ring
    · -- agreement at the deep point `y₁`
      have hT1 := hσH_T y₁ (hYd_sub_deep hy₁_mem)
      rw [hσ_eq_y₁1, hσ_y₁, hx₁, hT1]
      ring
  -- (6) the lower-end asymptotics of `σ`
  have hσ_lim : Filter.Tendsto (fun w => σ w - w + cl) MandelDim.lowerEnd (nhds 0) := by
    have hmem : {y : ℂ | y.im < c} ∈ MandelDim.lowerEnd := by
      rw [MandelDim.lowerEnd, Filter.mem_comap]
      exact ⟨Set.Iic (c - 1), Filter.Iic_mem_atBot (c - 1),
        fun z hz => lt_of_le_of_lt hz (sub_one_lt c)⟩
    have hev : (fun w : ℂ => σ w - w + cl)
        =ᶠ[MandelDim.lowerEnd] (fun w : ℂ => u w - w + cl) := by
      refine Filter.eventually_of_mem hmem ?_
      intro w hw
      show σ w - w + cl = u w - w + cl
      rw [hσ_eq w hw]
    exact hu_tend.congr' hev.symm
  exact ⟨y₁, x₁, σ, hy₁_D, hx₁_mem, hx₁_sec, hσ_diff, hσ_y₁, hσ_sec, hσ_T, hσ_lim⟩

end

end Work.Horn
