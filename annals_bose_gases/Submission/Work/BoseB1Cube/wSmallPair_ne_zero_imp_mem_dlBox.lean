import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.cubeDenseSplitCorr
import Submission.Work.BoseB1Cube.rhoRho_pair_null
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The support of the sliding pair kernel `wSmallPair`

`Submission.BoseGases.wSmallPair M ℓ d u v x y` is the product of the two
sliding-cutoff factors at the slots `x` and `y` with the renormalised kernel
in between:

    wSmallPair M ℓ d u v x y
      = χ_{B(u)}(x) · ( W(x−y) / (χ⋆χ)((x−y)/ℓ) ) · χ_{B(u)}(y) ,

so if it is non-zero then *each* factor is non-zero — in particular
`χ_{B(u)}(x) ≠ 0 ≠ χ_{B(u)}(y)`, and the two-point support lemma
`Work.SlotWord.chiSmallB_support_mem_dlBox` (`χ_{B(u)}(z) ≠ 0 ⟹ z ∈ dlBox ℓ d u`,
available for `M ≥ 1`, `ℓ > 0`, `d > 0`) gives the conclusion.

The two hypotheses of that support lemma that are **not** supplied by the
statement are recovered here:

* `M ≥ 1`: the cut-off is the cosine bump normalised by the *integral*
  `chiSmallNormSq M = ∫ (χ_M^{base})²`; at `M = 0` the base profile is `≡ 1`,
  whose Bochner integral over `ℝ³` vanishes (`∫ 1 = (volume univ).toReal = 0`,
  the integrand not being integrable), so `chiSmall 0 ≡ 0`, hence
  `chiSmallB 0 ≡ 0` and `wSmallPair 0 ≡ 0`: the hypothesis `h` is then
  contradictory and the conclusion vacuous.  So `1 ≤ M` may be assumed.
* `d > 0` (`Work.BoseB1Cube.pD_pos_of_boxMass_pos`, proved in
  `Submission/Work/BoseB1Cube/rhoRho_pair_null.lean`): if `d ≤ 0` then `ℓd ≤ 0`, and for
  such a scale the small cube `acube (ℓd)` is contained in `{0}`
  (`acube_subset_singleton_of_nonpos`), so `dlBox ℓ d u ⊆ {(ℓd)•u}` is a singleton, of measure
  zero; hence `boxMass ℓ d u = 0`, contradicting `hV`.

Everything in this file is proved from Mathlib and from already-verified corpus
modules; the hypothesis `hV` is *used* (without it the statement is false: at
`d < 0` the cut-off `χ_{B(u)}` is supported well outside the empty set
`dlBox ℓ d u`).
-/

namespace Work.BoseB1Cube

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The `M = 0` cosine bump is the zero function.**  At `M = 0` the base profile is
`chiSmallBase 0 ≡ (…)^0 = 1`, so its normalisation integral is `∫_z (1 : ℝ) = 0` (a
non-integrable constant has vanishing Bochner integral, `(volume univ).toReal = 0`), and
`chiSmall 0 z = 1 / √0 = 0`. -/
lemma chiSmall_zero_apply (z : E3) : Submission.BoseGases.chiSmall 0 z = 0 := by
  have hS : Submission.BoseGases.chiSmallNormSq 0 = 0 := by
    simp [Submission.BoseGases.chiSmallNormSq, Submission.BoseGases.chiSmallBase, integral_const,
      Measure.real_def]
  simp [Submission.BoseGases.chiSmall, hS]

/-- The sliding cut-off at `M = 0` vanishes identically (its small-scale factor is the zero
bump `chiSmall 0`). -/
lemma chiSmallB_zero_apply (ℓ d : ℝ) (u x : E3) :
    Submission.BoseGases.chiSmallB 0 ℓ d u x = 0 := by
  simp [Submission.BoseGases.chiSmallB, chiSmall_zero_apply]

/-- **Support of the sliding pair kernel.**  If `wSmallPair M ℓ d u v x y ≠ 0` and the sliding
box has positive volume then *both* slots lie in the small box `B(u) = dlBox ℓ d u`.

Indeed the kernel is the product
`χ_{B(u)}(x)·(W(x−y)/(χ⋆χ)((x−y)/ℓ))·χ_{B(u)}(y)`, so both cut-off factors are non-zero; a
non-zero cut-off has `M ≥ 1` (at `M = 0` it is identically `0`), and the box mass hypothesis
gives `d > 0`, so the two-point support lemma `chiSmallB_support_mem_dlBox` applies at each
slot. -/
theorem wSmallPair_ne_zero_imp_mem_dlBox {M : ℕ} {ℓ d : ℝ} {u x y : EuclideanSpace ℝ (Fin 3)}
    {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hℓ : 0 < ℓ) (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    (h : Submission.BoseGases.wSmallPair M ℓ d u v x y ≠ 0) :
    x ∈ Submission.BoseGases.dlBox ℓ d u ∧ y ∈ Submission.BoseGases.dlBox ℓ d u := by
  -- the two cut-off factors are non-zero
  have hx0 : Submission.BoseGases.chiSmallB M ℓ d u x ≠ 0 := by
    intro h0
    exact h (by rw [Submission.BoseGases.wSmallPair, h0]; ring)
  have hy0 : Submission.BoseGases.chiSmallB M ℓ d u y ≠ 0 := by
    intro h0
    exact h (by rw [Submission.BoseGases.wSmallPair, h0]; ring)
  -- at `M = 0` the cut-off vanishes, so the hypothesis forces `1 ≤ M`
  have hM : 1 ≤ M := by
    by_contra hlt
    have hM0 : M = 0 := Nat.lt_one_iff.mp (not_le.mp hlt)
    rw [hM0] at hx0
    exact hx0 (chiSmallB_zero_apply ℓ d u x)
  -- and the positive box mass forces `0 < d`
  have hd : 0 < d := pD_pos_of_boxMass_pos hℓ hV
  exact ⟨Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hx0,
    Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hy0⟩

end Work.BoseB1Cube
