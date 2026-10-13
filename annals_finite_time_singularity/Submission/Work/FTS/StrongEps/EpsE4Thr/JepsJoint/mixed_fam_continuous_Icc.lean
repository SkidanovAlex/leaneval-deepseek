/-
Copyright: work module for the Elgindi finite-time singularity project.

# Continuity of the mixed derivatives of a jointly smooth family on the *closed* slab

The sibling `Work.FTS.StrongEps.EpsE4Thr.JepsJoint.mixed_fam_continuous` proves that the mixed
jets `(z, θ) ↦ D_z^j D_θ^i (g · · t) z θ` of a jointly smooth family depend continuously on the
family parameter `t`, provided the family is jointly `C^n` (for every `n`) on the *open* slab
`Ioo 0 T ×ˢ Quad`.  This file proves the same statement on the *closed* slab
`Icc 0 T ×ˢ Quad`, which is what the level-four/level-six chapters of the `ε`-scheme need (they
state the joint regularity hypothesis `hreg` on the closed slab, and the measurability interface
`DiagCurveI_JfamP` then asks for `ContinuousOn … (Icc 0 T ×ˢ Quad)`).

## Method

The only new difficulty is the boundary of the `t`-interval: `ContDiffOn` on a closed set is
`ContDiffWithinAt`, i.e. one-sided smoothness in `t`, so the operator-transport argument of the
sibling (`contDiffOn_mixedJ`, which needs an *open* set) cannot be applied to `Icc 0 T` directly.

The fix is to *reparametrise the `t`-variable by a smooth surjection of an open interval onto
`[0,T]`* and pull the family back:

  `ψ s = T (1 - cos s) / 2`,   `Λ (s, (z,θ)) = (ψ s, (z,θ))`,

so that `Λ` maps the open set `Ioo (-1) (π+1) ×ˢ Quad` into `Icc 0 T ×ˢ Quad` (for `T ≥ 0`).
The chain rule (`ContDiffOn.comp`) then yields the joint smoothness of the pulled-back family
`g̃ z θ s = g z θ (ψ s)` on the open set, the *open*-set form of the sibling
(`continuousOn_mixed_of_contDiffOn_open`, proved below for an arbitrary open set) gives continuity
of the pulled-back mixed jets there, and the identification

  `mixed j i (g · · t) z θ = mixed j i (g̃ · · (arccos (1 - 2t/T))) z θ`   (`t ∈ [0,T]`, `T > 0`)

(which is `cos (arccos x) = x`) transports the conclusion back: the map
`(t, (z,θ)) ↦ (arccos (1 - 2t/T), (z,θ))` is continuous, and composing preserves continuity.

For `T = 0` the slab is `{0} ×ˢ Quad`, the same pull-back with the (constant) `ψ` is continuous
on the open set `Ioo (-1) (π+1) ×ˢ Quad` containing it, and monotonicity of `ContinuousOn` plus
`ψ 0 = 0` finishes.  For `T < 0` the slab is empty.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.mixed_fam_continuous

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 1000000

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.JepsJoint

/-! ## An open-set version of `mixed_fam_continuous`

The sibling's proof only uses that its domain is open (through `contDiffOn_mixedJ`), so it works
verbatim on any open subset of `ℝ × (ℝ × ℝ)`.  This form is what the pull-back argument below
needs. -/

theorem continuousOn_mixed_of_contDiffOn_open {g : ℝ → ℝ → ℝ → ℝ} {V : Set (ℝ × (ℝ × ℝ))}
    (hV : IsOpen V)
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (fun q : ℝ × (ℝ × ℝ) => g q.2.1 q.2.2 q.1) V)
    (j i : ℕ) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.mixed j i (fun z θ => g z θ q.1) q.2.1 q.2.2) V := by
  have hcd : ContDiffOn ℝ 0 (mixedJ j i (fun q : ℝ × (ℝ × ℝ) => g q.2.1 q.2.2 q.1)) V :=
    contDiffOn_mixedJ hV (hg (0 + j + i))
  refine hcd.continuousOn.congr (fun q hq => ?_)
  exact (mixedJ_apply j i (fun q : ℝ × (ℝ × ℝ) => g q.2.1 q.2.2 q.1) q).symm

/-! ## The closed slab with nonnegative horizon -/

/-- The pull-back window: the open interval `(-1, π+1)` parametrises the closed interval `[0,T]`
(and also contains `0`, which is all the degenerate case `T = 0` needs). -/
private def pullWindow : Set (ℝ × (ℝ × ℝ)) :=
  Set.Ioo (-1 : ℝ) (π + 1) ×ˢ Work.FTS.StrongEps.Quad

private theorem isOpen_pullWindow : IsOpen pullWindow := by
  rw [pullWindow, Work.FTS.StrongEps.Quad]
  exact isOpen_Ioo.prod (isOpen_Ioi.prod isOpen_Ioo)

/-- The smooth parametrisation `s ↦ T (1 - cos s)/2` of the `t`-coordinate. -/
private def pullPsi (T : ℝ) (s : ℝ) : ℝ := T * (1 - Real.cos s) / 2

private theorem pullPsi_smooth (T : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun q : ℝ × (ℝ × ℝ) => pullPsi T q.1) pullWindow := by
  show ContDiffOn ℝ n (fun q : ℝ × (ℝ × ℝ) => T * (1 - Real.cos q.1) / 2) pullWindow
  fun_prop

private theorem pullPsi_mem {T s : ℝ} (hT : 0 ≤ T) : pullPsi T s ∈ Set.Icc (0 : ℝ) T := by
  have h1 : -1 ≤ Real.cos s := Real.neg_one_le_cos s
  have h2 : Real.cos s ≤ 1 := Real.cos_le_one s
  show T * (1 - Real.cos s) / 2 ∈ Set.Icc (0 : ℝ) T
  constructor <;> nlinarith

private theorem pullPsi_zero (T : ℝ) : pullPsi T 0 = 0 := by
  show T * (1 - Real.cos 0) / 2 = 0
  norm_num

/-- **The closed-slab statement for `T ≥ 0`.** -/
theorem continuousOn_mixed_fam_Icc_of_nonneg {g : ℝ → ℝ → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) {j i : ℕ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (fun q : ℝ × (ℝ × ℝ) => g q.2.1 q.2.2 q.1)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad)) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.mixed j i (fun z θ => g z θ q.1) q.2.1 q.2.2)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) := by
  -- ## the pulled-back family on the open window
  have hΛ : ∀ n : ℕ, ContDiffOn ℝ n
      (fun q : ℝ × (ℝ × ℝ) => (pullPsi T q.1, q.2)) pullWindow := by
    intro n
    exact (pullPsi_smooth T n).prodMk contDiff_snd.contDiffOn
  have hmap : MapsTo (fun q : ℝ × (ℝ × ℝ) => (pullPsi T q.1, q.2)) pullWindow
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) :=
    fun q hq => ⟨pullPsi_mem hT, hq.2⟩
  have hgc : ∀ n : ℕ, ContDiffOn ℝ n
      (fun q : ℝ × (ℝ × ℝ) => g q.2.1 q.2.2 (pullPsi T q.1)) pullWindow := by
    intro n
    have h := (hg n).comp (hΛ n) hmap
    simpa only [Function.comp_def] using h
  have hcont : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.mixed j i (fun z θ => g z θ (pullPsi T q.1)) q.2.1 q.2.2) pullWindow :=
    continuousOn_mixed_of_contDiffOn_open (g := fun z θ s => g z θ (pullPsi T s))
      isOpen_pullWindow hgc j i
  -- ## transport back to the closed slab
  rcases eq_or_lt_of_le hT with hT0 | hTpos
  · -- ### `T = 0`: the slab is contained in the window and `ψ 0 = 0`
    have hTle : T ≤ 0 := le_of_eq hT0.symm
    refine (hcont.mono ?_).congr (fun q hq => ?_)
    · intro q hq
      obtain ⟨h1, h2⟩ := hq
      have hq1 : q.1 = 0 := le_antisymm (le_trans h1.2 hTle) h1.1
      refine ⟨⟨?_, ?_⟩, h2⟩
      · rw [hq1]; norm_num
      · rw [hq1]; linarith [Real.pi_pos]
    · obtain ⟨h1, _h2⟩ := hq
      have hq1 : q.1 = 0 := le_antisymm (le_trans h1.2 hTle) h1.1
      have hkey : pullPsi T q.1 = q.1 := by
        show T * (1 - Real.cos q.1) / 2 = q.1
        rw [hq1]
        simp
      simp only [hkey]
  · -- ### `T > 0`: invert the parametrisation with `arccos`
    have hιcont : ContinuousOn
        (fun q : ℝ × (ℝ × ℝ) => (Real.arccos (1 - 2 * q.1 / T), q.2))
        (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) := by
      refine ContinuousOn.prodMk ?_ continuous_snd.continuousOn
      exact Real.continuous_arccos.comp_continuousOn (by fun_prop)
    have hιmap : MapsTo (fun q : ℝ × (ℝ × ℝ) => (Real.arccos (1 - 2 * q.1 / T), q.2))
        (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) pullWindow := by
      intro q hq
      obtain ⟨⟨hq0, hqT⟩, hq2⟩ := hq
      refine ⟨⟨?_, ?_⟩, hq2⟩
      · linarith [Real.arccos_nonneg (1 - 2 * q.1 / T)]
      · linarith [Real.arccos_le_pi (1 - 2 * q.1 / T)]
    refine (hcont.comp' hιcont hιmap).congr (fun q hq => ?_)
    obtain ⟨⟨hq0, hqT⟩, _hq2⟩ := hq
    have hx1 : -1 ≤ 1 - 2 * q.1 / T := by
      have h2 : 2 * q.1 / T ≤ 2 := by
        rw [div_le_iff₀ hTpos]; linarith
      linarith
    have hx2 : 1 - 2 * q.1 / T ≤ 1 := by
      have h2 : 0 ≤ 2 * q.1 / T := div_nonneg (by linarith) hTpos.le
      linarith
    have hkey : pullPsi T (Real.arccos (1 - 2 * q.1 / T)) = q.1 := by
      show T * (1 - Real.cos (Real.arccos (1 - 2 * q.1 / T))) / 2 = q.1
      rw [Real.cos_arccos hx1 hx2]
      field_simp
      ring
    show Work.Spaces.mixed j i (fun z θ => g z θ q.1) q.2.1 q.2.2
      = Work.Spaces.mixed j i (fun z θ =>
          g z θ (pullPsi T (Real.arccos (1 - 2 * q.1 / T)))) q.2.1 q.2.2
    simp only [hkey]

/-! ## The requested statement -/

theorem mixed_fam_continuous_Icc {g : ℝ → ℝ → ℝ → ℝ} {T : ℝ} {j i : ℕ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (fun q : ℝ × (ℝ × ℝ) => g q.2.1 q.2.2 q.1)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad)) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.mixed j i (fun z θ => g z θ q.1) q.2.1 q.2.2)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) := by
  rcases lt_or_ge T 0 with hT | hT
  · -- the slab is empty
    refine fun q hq => ?_
    exfalso
    have h1 : (0 : ℝ) ≤ q.1 := hq.1.1
    have h2 : q.1 ≤ T := hq.1.2
    linarith
  · exact continuousOn_mixed_fam_Icc_of_nonneg hT hg

end Work.FTS.StrongEps.EpsE4Thr.JepsJoint
