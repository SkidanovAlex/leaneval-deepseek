/-
# `Work.FTS_RegExport.RX0.sup2_extG_ext_hIS` — `∂_z²` of the extension `g̃`, from the `hIS` bound

This is the `hIS`-version (the re-cut of `RegExportIface/Defs.lean`, `hRQ → hIS`) of
`Work.FTS.RegPkgGal.Der.sup2_extG_ext`: the uniform bound on `∂_z²` of the extension
`g̃ = extG g` over the strip `0 < z`, `θ ∈ Iθ`, `τ ∈ [0,S]`, where the class hypothesis of the
siblings (`RegQ`, i.e. `SmoothQuad` + `ℋ⁴`-membership + boundary traces, with the uniform
`ℋ⁴`-norm bound `hHkn`) is replaced by

* `hIS` — the interior order-`≤ 2` sup bound `|D_z^b D_θ^a (g-slice)| ≤ M` on the open quadrant;
* `hc4` — `C⁴` of the uncurried slice on the open quadrant `Q0` (used only for differentiability).

The near-axis hypothesis `hq2` is stated, as in `sup2_extG_ext`, for the **extension** slice.

**Proof.**  For `τ ∈ [0,S]` and `z > 0` the extension slice `z' ↦ g̃ z' θ τ` agrees with the
`g`-slice on the open half line `Ioi 0`, and `deriv` is local (`pz_congr_of_isOpen` applied
twice), so `∂_z²` agrees at every `z > 0` (`pz_pz_extG_eq`).  Three regimes:

* `θ = 0` and `θ = π/2`: the extension slice is *identically zero* in `z` — for `z' ≤ 0` by the
  definition of `extG`, for `z' > 0` by the angular vanishing hypothesis `hvan` — so both
  `∂_z`-derivatives vanish;
* `0 < z ≤ 2`: the hypothesis `hq2` verbatim;
* `z > 2`: the `hIS` bound gives `|D_z²F|, |D_zF| ≤ M`, and the elementary identity
  `D_z²F = D_zF + z²∂_z²F` (`DzIter_two_eq_add`, the `n = 2` case of the expansion of
  `D_z = z∂_z` in powers of `z^k∂_z^k`, proved from the product rule alone) turns this into
  `|∂_z²F| ≤ (|D_z²F| + |D_zF|)/z² ≤ 2M/z² ≤ M/2` since `z² > 4`.

The differentiability needed by the identity is the only use of `hc4`: the `z`-slice of `F` is
`C⁴` on `Ioi 0` (composition with `z ↦ (z,θ)`), hence its `deriv` is `C³`, hence differentiable
(`contDiffOn_pz_slice_four`).

The conclusion is therefore `M₂ = max Q₂ M`.  (`hα` and `hS` are not needed: the conclusion is a
pointwise bound on a fixed `τ`.)
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.Der.sup2_extG_ext
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Set MeasureTheory Filter

namespace Work.FTS_RegExport.RX0

set_option autoImplicit false

/-! ## Helpers -/

/-- **Congruence of `∂_z²` between the extension slice and the slice of `g`.**  For `τ ≥ 0` the
two functions `z' ↦ extG g z' θ τ` and `z' ↦ g z' θ τ` agree on the open half line `Ioi 0`
(`extG_of_pos`), and `pz` is a local operator, so their second `z`-derivatives agree at every
`z > 0`. -/
private lemma pz_pz_extG_eq {g : ℝ → ℝ → ℝ → ℝ} {τ z θ : ℝ} (hτ : 0 ≤ τ) (hz : 0 < z) :
    Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)) z θ
      = Work.Spaces.pz (Work.Spaces.pz (fun z θ => g z θ τ)) z θ := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hagree : EqOn (Function.uncurry (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ))
      (Function.uncurry (fun z θ => g z θ τ)) (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    rintro ⟨z', θ'⟩ ⟨hz', -⟩
    exact Work.FTS.RegPkgGal.extG_of_pos hz' hτ
  have h1 : EqOn (Function.uncurry (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)))
      (Function.uncurry (Work.Spaces.pz (fun z θ => g z θ τ)))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    intro y hy
    exact Work.Spaces.pz_congr_of_isOpen hV hagree hy
  exact Work.Spaces.pz_congr_of_isOpen hV h1 ⟨hz, trivial⟩

/-- **The bridge `D_z² = D_z + z²∂_z²`.**  If the `z`-slice of `pz F` is differentiable at `z`,
then `D_z²F = D_zF + z²∂_z²F` at `(z,θ)`.  (The `n = 2` case of the expansion of `D_z = z∂_z` in
powers of `z^k∂_z^k`, with the Stirling coefficients `S(2,1) = S(2,2) = 1`; only the product rule
is used, so no higher smoothness is required.) -/
private lemma DzIter_two_eq_add (F : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hd : DifferentiableAt ℝ (fun z' => Work.Spaces.pz F z' θ) z) :
    Work.Spaces.DzIter 2 F z θ
      = Work.Spaces.DzIter 1 F z θ + z ^ 2 * Work.Spaces.pz (Work.Spaces.pz F) z θ := by
  have hdmul : deriv (fun z' : ℝ => z' * Work.Spaces.pz F z' θ) z
      = Work.Spaces.pz F z θ + z * Work.Spaces.pz (Work.Spaces.pz F) z θ := by
    have h1 : HasDerivAt (fun z' : ℝ => z') (1 : ℝ) z := hasDerivAt_id' z
    have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pz F z' θ)
        (Work.Spaces.pz (Work.Spaces.pz F) z θ) z := hd.hasDerivAt
    have h3 : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pz F z' θ)
        (1 * Work.Spaces.pz F z θ + z * Work.Spaces.pz (Work.Spaces.pz F) z θ) z :=
      (h1.mul h2).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by funext z'; rfl))
    simpa only [one_mul] using h3.deriv
  show z * deriv (fun z' : ℝ => z' * Work.Spaces.pz F z' θ) z
      = z * Work.Spaces.pz F z θ + z ^ 2 * Work.Spaces.pz (Work.Spaces.pz F) z θ
  rw [hdmul]
  ring

/-- **Differentiability of the `∂_z`-slice from `C⁴` on the open quadrant.**  If `F` is `C⁴` on
`Q0 = (0,∞) × (0,π/2)` then the `z`-slice `z' ↦ ∂_zF(z',θ)` is differentiable at every `z > 0`
and interior angle: the slice of `F` is `C⁴` on `Ioi 0` (compose with the smooth injection
`z ↦ (z,θ)`), so its `deriv` is `C³`, hence differentiable. -/
private lemma contDiffOn_pz_slice_four {F : ℝ → ℝ → ℝ} {θ z : ℝ}
    (hc4 : ContDiffOn ℝ 4 (Function.uncurry F) Work.FTS.EllipticEst.Q0)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hz : z ∈ Set.Ioi (0 : ℝ)) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.pz F z' θ) z := by
  have hsl : ContDiffOn ℝ 4 (fun z' : ℝ => F z' θ) (Set.Ioi (0 : ℝ)) := by
    have hp : ContDiffOn ℝ 4 (fun z : ℝ => (z, θ)) (Set.Ioi (0 : ℝ)) := by fun_prop
    have h2 := hc4.comp hp (fun z hz => ⟨hz, hθ.1, hθ.2⟩)
    simpa [Function.comp_def, Function.uncurry] using h2
  have hder : ContDiffOn ℝ 3 (deriv (fun z' : ℝ => F z' θ)) (Set.Ioi (0 : ℝ)) :=
    hsl.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hfun : (fun z' : ℝ => Work.Spaces.pz F z' θ) = deriv (fun z' : ℝ => F z' θ) := by
    funext z'; rfl
  rw [hfun]
  exact (hder.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)

/-! ## The target -/

theorem sup2_extG_ext_hIS {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (hα : 0 < α) (hS : 0 < S)
    (hIS : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ,
      0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (Work.FTS.Regularity.gSlice g τ) z θ| ≤ M)
    (hc4 : ∀ τ ∈ Set.Icc 0 S, ContDiffOn ℝ 4
      (Function.uncurry (Work.FTS.Regularity.gSlice g τ)) Work.FTS.EllipticEst.Q0)
    (hvan : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (Real.pi / 2) τ = 0)
    (hq2 : ∃ Q₂ : ℝ, 0 ≤ Q₂ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ,
      0 < z → z ≤ 2 →
      |Work.Spaces.pz (Work.Spaces.pz
        (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG g) τ)) z θ| ≤ Q₂) :
    ∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)) z θ| ≤ M₂ := by
  obtain ⟨M, hM0, hM⟩ := hIS
  obtain ⟨Q₂, hQ₂0, hQ₂bd⟩ := hq2
  refine ⟨max Q₂ M, le_trans hQ₂0 (le_max_left _ _), ?_⟩
  intro τ hτ z θ hz hθI
  rcases lt_or_eq_of_le hθI.1 with hθpos | hθzero
  · rcases lt_or_eq_of_le hθI.2 with hθlt | hθtop
    · -- the interior angle: `hq2` for `z ≤ 2`, the `hIS` bound for `z > 2`
      rcases le_or_gt z 2 with hz2 | hz2
      · exact le_trans (hQ₂bd τ hτ θ hθI z hz hz2) (le_max_left _ _)
      · -- the extension slice agrees with the `g`-slice on `Ioi 0`
        have hcongr :
            Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)) z θ
              = Work.Spaces.pz (Work.Spaces.pz (fun z θ => g z θ τ)) z θ :=
          pz_pz_extG_eq hτ.1 hz
        rw [hcongr]
        -- the two `hIS` slots of order `≤ 2`
        have hm2 : |Work.Spaces.mixed 2 0 (Work.FTS.Regularity.gSlice g τ) z θ| ≤ M :=
          hM τ hτ 2 0 (by norm_num) z θ hz hθpos hθlt
        have hm1 : |Work.Spaces.mixed 1 0 (Work.FTS.Regularity.gSlice g τ) z θ| ≤ M :=
          hM τ hτ 1 0 (by norm_num) z θ hz hθpos hθlt
        simp only [Work.Spaces.mixed_zero_right] at hm2 hm1
        have hdiff : DifferentiableAt ℝ
            (fun z' => Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z' θ) z :=
          contDiffOn_pz_slice_four (hc4 τ hτ) ⟨hθpos, hθlt⟩ hz
        have hid := DzIter_two_eq_add (Work.FTS.Regularity.gSlice g τ) hdiff
        have hmul : z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ)) z θ
            = Work.Spaces.DzIter 2 (Work.FTS.Regularity.gSlice g τ) z θ
              - Work.Spaces.DzIter 1 (Work.FTS.Regularity.gSlice g τ) z θ := by
          linarith [hid]
        have hz2' : (4 : ℝ) ≤ z ^ 2 := by nlinarith
        have hstep :
            z ^ 2 * |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ)) z θ|
              ≤ 2 * M := by
          rw [← abs_of_pos (by positivity : (0 : ℝ) < z ^ 2), ← abs_mul, hmul]
          calc |Work.Spaces.DzIter 2 (Work.FTS.Regularity.gSlice g τ) z θ
                - Work.Spaces.DzIter 1 (Work.FTS.Regularity.gSlice g τ) z θ|
              = |Work.Spaces.DzIter 2 (Work.FTS.Regularity.gSlice g τ) z θ
                  + (-Work.Spaces.DzIter 1 (Work.FTS.Regularity.gSlice g τ) z θ)| := by
                ring_nf
            _ ≤ |Work.Spaces.DzIter 2 (Work.FTS.Regularity.gSlice g τ) z θ|
                  + |-Work.Spaces.DzIter 1 (Work.FTS.Regularity.gSlice g τ) z θ| :=
                abs_add_le _ _
            _ = |Work.Spaces.DzIter 2 (Work.FTS.Regularity.gSlice g τ) z θ|
                  + |Work.Spaces.DzIter 1 (Work.FTS.Regularity.gSlice g τ) z θ| := by
                rw [abs_neg]
            _ ≤ 2 * M := by linarith
        have hfin : |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ)) z θ|
            ≤ M := by
          have h4 : 4 * |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ)) z θ|
              ≤ z ^ 2 * |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ)) z θ| :=
            mul_le_mul_of_nonneg_right hz2' (abs_nonneg _)
          nlinarith [le_trans h4 hstep,
            abs_nonneg (Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ)) z θ)]
        exact le_trans hfin (le_max_right _ _)
    · -- the angle `θ = π/2`: the extension slice is identically zero in `z`
      have hzero : (fun z' : ℝ => Work.FTS.RegPkgGal.extG g z' θ τ) = fun _ => (0 : ℝ) := by
        funext z'
        rcases le_or_gt z' 0 with hz' | hz'
        · exact Work.FTS.RegPkgGal.extG_of_nonpos hz'
        · rw [Work.FTS.RegPkgGal.extG_of_pos hz' hτ.1, hθtop]
          exact (hvan τ hτ z' hz'.le).2
      have hpz0 : ∀ z' : ℝ,
          Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z' θ = 0 := by
        intro z'
        show deriv (fun z'' => Work.FTS.RegPkgGal.extG g z'' θ τ) z' = 0
        rw [hzero, deriv_const]
      have hpp : Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ))
          z θ = 0 := by
        show deriv (fun z' => Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z' θ) z
          = 0
        rw [show (fun z' => Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z' θ)
            = fun _ => (0 : ℝ) from funext hpz0, deriv_const]
      rw [hpp, abs_zero]
      exact le_trans hQ₂0 (le_max_left _ _)
  · -- the angle `θ = 0`: the extension slice is identically zero in `z`
    have hθ0 : θ = 0 := hθzero.symm
    have hzero : (fun z' : ℝ => Work.FTS.RegPkgGal.extG g z' θ τ) = fun _ => (0 : ℝ) := by
      funext z'
      rcases le_or_gt z' 0 with hz' | hz'
      · exact Work.FTS.RegPkgGal.extG_of_nonpos hz'
      · rw [Work.FTS.RegPkgGal.extG_of_pos hz' hτ.1, hθ0]
        exact (hvan τ hτ z' hz'.le).1
    have hpz0 : ∀ z' : ℝ,
        Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z' θ = 0 := by
      intro z'
      show deriv (fun z'' => Work.FTS.RegPkgGal.extG g z'' θ τ) z' = 0
      rw [hzero, deriv_const]
    have hpp : Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ))
        z θ = 0 := by
      show deriv (fun z' => Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z' θ) z
        = 0
      rw [show (fun z' => Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z' θ)
          = fun _ => (0 : ℝ) from funext hpz0, deriv_const]
    rw [hpp, abs_zero]
    exact le_trans hQ₂0 (le_max_left _ _)

end Work.FTS_RegExport.RX0
