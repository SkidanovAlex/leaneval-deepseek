import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB25.Lgs_nonneg_of_max

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.Lgs_le_zero_of_max` — the comparison half of the SB5 barrier

Companion of `Lgs_nonneg_of_max` (leaf E4a).  It says that a `C²` function `g` on a closed
rectangle `[zlo,zhi] × [alo,ahi] ⊂ Qd` whose **boundary** values are strictly negative and whose
`Lgs α`-image is strictly negative at every **interior** point cannot be positive anywhere:
`g ≤ 0` on the whole rectangle.

The proof is the standard Fermat/compactness argument.  If `g` were positive somewhere, the
continuous function `Function.uncurry g` attains a maximum `M > 0` on the compact rectangle at
some point `(z₀,θ₀)`; since the boundary values are `< 0 < M`, that point is interior
(`z₀ ∈ Ioo zlo zhi`, `θ₀ ∈ Ioo alo ahi`, hence also `z₀ > 0` and `θ₀ ∈ Ioo 0 (π/2)`, using
`0 < zlo`, `0 < alo`, `ahi < π/2`).  A global maximum of `g` on the rectangle is in particular a
one-dimensional local maximum of both slices `z ↦ g z θ₀` and `θ ↦ g z₀ θ`, so
`Lgs_nonneg_of_max` gives `0 ≤ Lgs α g z₀ θ₀`, contradicting the strict negativity hypothesis
`hneg` at the interior point `(z₀,θ₀)`.

This is exactly the `sb5_compare`/`sb5_barrier` interface: the barrier
`(M+δφ)(z/L)^{-k} + η` minus the solution is `≤ 0` on the half-strip, with the negative boundary
data on the outer rectangle and the strictly negative `Lgs`-image on the interior.
-/

open Filter

namespace Work.FTS_StreamBdry.SB25

theorem Lgs_le_zero_of_max (α zlo zhi alo ahi : ℝ) (g : ℝ → ℝ → ℝ)
    (hz : zlo < zhi) (ha : alo < ahi) (hz0 : 0 < zlo) (ha0 : 0 < alo) (ha1 : ahi < Real.pi / 2)
    (hcont : ContinuousOn (Function.uncurry g) (Set.Icc zlo zhi ×ˢ Set.Icc alo ahi))
    (hbd : ∀ z θ, z ∈ Set.Icc zlo zhi → θ ∈ Set.Icc alo ahi →
      (z = zlo ∨ z = zhi ∨ θ = alo ∨ θ = ahi) → g z θ < 0)
    (hC2 : ∀ z θ, z ∈ Set.Ioo zlo zhi → θ ∈ Set.Ioo alo ahi →
      ContDiffAt ℝ 2 (Function.uncurry g) (z, θ))
    (hneg : ∀ z θ, z ∈ Set.Ioo zlo zhi → θ ∈ Set.Ioo alo ahi →
      Work.FTS_StreamBdry.SB25.Lgs α g z θ < 0) :
    ∀ z θ, z ∈ Set.Icc zlo zhi → θ ∈ Set.Icc alo ahi → g z θ ≤ 0 := by
  -- suppose `g > 0` somewhere; then the maximum on the compact rectangle is positive
  by_contra hcon
  push_neg at hcon
  obtain ⟨zw, θw, hzw, hθw, hpos⟩ := hcon
  have hSne : (Set.Icc zlo zhi ×ˢ Set.Icc alo ahi).Nonempty := ⟨(zw, θw), hzw, hθw⟩
  have hScomp : IsCompact (Set.Icc zlo zhi ×ˢ Set.Icc alo ahi) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨p, hpS, hpmax⟩ := hScomp.exists_isMaxOn hSne hcont
  obtain ⟨z0, θ0⟩ := p
  rw [Set.mem_prod] at hpS
  rw [isMaxOn_iff] at hpmax
  have hmax : g zw θw ≤ g z0 θ0 := hpmax (zw, θw) ⟨hzw, hθw⟩
  have hz0posV : 0 < g z0 θ0 := lt_of_lt_of_le hpos hmax
  -- the maximiser is not on the boundary (the boundary values are `< 0`)
  have hzne : z0 ≠ zlo := by
    intro h
    have hb := hbd z0 θ0 hpS.1 hpS.2 (Or.inl h)
    linarith
  have hzne' : z0 ≠ zhi := by
    intro h
    have hb := hbd z0 θ0 hpS.1 hpS.2 (Or.inr (Or.inl h))
    linarith
  have hθne : θ0 ≠ alo := by
    intro h
    have hb := hbd z0 θ0 hpS.1 hpS.2 (Or.inr (Or.inr (Or.inl h)))
    linarith
  have hθne' : θ0 ≠ ahi := by
    intro h
    have hb := hbd z0 θ0 hpS.1 hpS.2 (Or.inr (Or.inr (Or.inr h)))
    linarith
  have hz0Ioo : z0 ∈ Set.Ioo zlo zhi :=
    ⟨lt_of_le_of_ne hpS.1.1 (Ne.symm hzne), lt_of_le_of_ne hpS.1.2 hzne'⟩
  have hθ0Ioo : θ0 ∈ Set.Ioo alo ahi :=
    ⟨lt_of_le_of_ne hpS.2.1 (Ne.symm hθne), lt_of_le_of_ne hpS.2.2 hθne'⟩
  have hz0pos : 0 < z0 := lt_of_lt_of_le hz0 hpS.1.1
  have hθ0mem : θ0 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨lt_of_lt_of_le ha0 hpS.2.1, lt_of_le_of_lt hpS.2.2 ha1⟩
  -- the maximiser is a one-dimensional local maximum of both slices
  have hmz : IsLocalMax (fun z => g z θ0) z0 := by
    rw [IsLocalMax]
    filter_upwards [isOpen_Ioo.mem_nhds hz0Ioo] with z' hz'
    exact hpmax (z', θ0) ⟨⟨le_of_lt hz'.1, le_of_lt hz'.2⟩, hpS.2⟩
  have hmθ : IsLocalMax (fun θ => g z0 θ) θ0 := by
    rw [IsLocalMax]
    filter_upwards [isOpen_Ioo.mem_nhds hθ0Ioo] with θ' hθ'
    exact hpmax (z0, θ') ⟨hpS.1, ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩⟩
  -- Fermat at an interior maximum contradicts the strict sign of `Lgs`
  have hge := Lgs_nonneg_of_max α g z0 θ0 hz0pos hθ0mem (hC2 z0 θ0 hz0Ioo hθ0Ioo) hmz hmθ
  have hlt := hneg z0 θ0 hz0Ioo hθ0Ioo
  linarith

end Work.FTS_StreamBdry.SB25
