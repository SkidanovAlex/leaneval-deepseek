import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.SysAux.dense_diffAt` — the core of the `Corr`-lemma of S6

The key structural input for the decomposition of `bR = Vθ7/sin 2θ` in the leaf
`Work.FTS_RegExport.RXT.Sys.forcing_bound` (see `RXT/Sys/NOTES_forcing_bound.md` §3):
the stream function `Φ = ΦR α Φs E g` is `Φs + E(slice G)`, an *arbitrary* function of `(z,θ)`
as far as the hypotheses of S6 are concerned, so the additivity
`Uop β Φ = Uop β Φ̃ + Uop β (Θ β F)` — equivalently `deriv_sub` on the `z`-slices — is not
available.  This file proves the substitute: the non-differentiability set of a slice has empty
interior (because on an interval the definition of `bR` forces `Φ = -sin 2θ·b/6`), whence the
differentiable points are dense and, by continuity, the *correction*
`Corr = bR - 2W - 2·Uop β (Θ β F)/sin 2θ` vanishes identically.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.SysAux

/-- **Density of the differentiability points.**  If a slice of `Φ` satisfies the pointwise
identity `b z θ = 2·(-3·Φ z θ - β·z·(∂_zΦ)(z,θ))/sin 2θ` with `b(·,θ)` differentiable on `(0,∞)`,
then every open interval of `(0,∞)` contains a point at which the slice `z ↦ Φ z θ` is
differentiable.  (Equivalently: the non-differentiability set of the slice has empty interior,
because on an interval the identity forces `Φ = -sin 2θ·b/6`.) -/
theorem exists_differentiableAt_of_slice_identity {β θ : ℝ} {b Φ : ℝ → ℝ → ℝ} (hβ : 0 < β)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hb : ∀ z : ℝ, 0 < z →
      b z θ = 2 * (-3 * Φ z θ - β * z * deriv (fun z' => Φ z' θ) z) / Real.sin (2 * θ))
    (hbd : DifferentiableOn ℝ (fun z : ℝ => b z θ) (Set.Ioi 0))
    {a c : ℝ} (ha : 0 < a) (hac : a < c) :
    ∃ z ∈ Set.Ioo a c, DifferentiableAt ℝ (fun z' : ℝ => Φ z' θ) z := by
  by_contra hcon
  push Not at hcon
  have hθπ : 2 * θ < Real.pi := by linarith
  have hsin : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) hθπ)
  -- on `(a,c)` the slice is nowhere differentiable, so `deriv` vanishes there
  have hzero : ∀ z ∈ Set.Ioo a c, deriv (fun z' : ℝ => Φ z' θ) z = 0 := fun z hz =>
    deriv_zero_of_not_differentiableAt (hcon z hz)
  -- hence `Φ(·,θ)` coincides on `(a,c)` with `-sin 2θ·b(·,θ)/6`
  have hEq : Set.EqOn (fun z => Φ z θ) (fun z => -(Real.sin (2 * θ) * b z θ) / 6)
      (Set.Ioo a c) := by
    intro z hz
    have hz0 : 0 < z := lt_trans ha hz.1
    have h := hb z hz0
    rw [hzero z hz] at h
    have h6 : 6 * Φ z θ = -(2 * (-3 * Φ z θ)) := by ring
    field_simp at h
    linarith [h]
  -- and the latter is differentiable on the interval
  have hd : DifferentiableOn ℝ (fun z => -(Real.sin (2 * θ) * b z θ) / 6) (Set.Ioo a c) := by
    have hsub : Set.Ioo a c ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_trans ha hz.1
    have h1 : DifferentiableOn ℝ (fun z : ℝ => Real.sin (2 * θ) * b z θ) (Set.Ioo a c) :=
      (hbd.mono hsub).const_mul _
    exact (h1.neg).div_const 6
  obtain ⟨z, hz⟩ : (Set.Ioo a c).Nonempty := Set.nonempty_Ioo.mpr hac
  refine hcon z hz ?_
  have hev : (fun z' => -(Real.sin (2 * θ) * b z' θ) / 6) =ᶠ[𝓝 z] (fun z' => Φ z' θ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hz] with y hy
    exact (hEq hy).symm
  exact (hd.differentiableAt (isOpen_Ioo.mem_nhds hz)).congr_of_eventuallyEq hev.symm

end Work.FTS_RegExport.RXT.SysAux
