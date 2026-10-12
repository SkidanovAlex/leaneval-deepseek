import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.chiCubeB_hasCompactSupport
import Submission.Work.BoseFixB1B.chiCubeCorrB1
import Submission.Work.BoseFixB1S.win.chiSmallB_fsKinPGenIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.chiCubeB_fsKinPGenIntegrable`

`q`-integrability of the FS-weighted windowed mode content at the **smooth cube** window
`chiCubeB M ℓ d u` (`chiCubeBump.lean`), i.e. of

    q ↦ fsKinCoeff c ‖q‖ · boxWinModePGen ℓ |B(u)| (B(u)) (chiCubeB M ℓ d u) Ψ q .

## Route

Unlike the `chiSmallB` twin (`Submission/Work/BoseFixB1S/win/chiSmallB_fsKinPGenIntegrable.lean`),
which is only `C^{M−1}` and therefore has to be assembled from a smoothness-free pointwise slot
Cauchy–Schwarz plus a `C²`-level single-slot integrability, the cube bump is **`C^∞`**
(`chiCubeB_contDiff`).  So the general `C^∞` theorem

* `Work.BoseFixB1B.pairRung.fsKinPGenIntegrable` — for any `χ` that is `C^∞`, compactly supported,
  vanishes off `Ac`, and is nonnegative,

applies **verbatim**.  All that is left is to supply its four window side conditions at
`χ = chiCubeB M ℓ d u`:

* `ContDiff ℝ ∞` — `chiCubeB_contDiff` (`chiCubeBump.lean`);
* `HasCompactSupport` — `chiCubeB_hasCompactSupport` (`chiCubeB_hasCompactSupport.lean`, which needs
  only `0 < ℓ`);
* vanishing off the sliding box — `chiCubeB_eq_zero_off_dlBox` below, the contrapositive of the
  support containment `Function.support (chiCubeB M ℓ d u) ⊆ dlBox ℓ d u`.  This is the only
  genuinely geometric step; it is proved here directly from the coordinatewise form of the cube
  bump (its twin in `chiCubeCorrB1.lean` is `chiCubeB_mem_dlBox`), so that the target is
  self-contained in that respect;
* nonnegativity — `chiCubeB_nonneg` (`chiCubeBump.lean`).

and the box data `Ac = dlBox ℓ d u`, `volA = boxMass ℓ d u` from `Work.SmallBoxSliding`
(`measurableSet_dlBox`, `dlBox_subset_acube`, `boxMass_eq_measureReal`).

Note that `d ≤ 1`, `5 ≤ M` and `0 < c` are *not* used: the statement is true for every `M`, every
`d > 0` and every real `c` (the symbol `fsKinCoeff c ‖q‖ = [‖q‖ − c]₊²` is nonnegative regardless
of the sign of `c`, and only *grows* like `‖q‖²`).  They are kept because the requester's interface
carries them.
-/

namespace Work.BoseFixB1B

open MeasureTheory

noncomputable section

set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The support of the cube window lies in the sliding box

The two factors of `chiCubeB M ℓ d u = chiCubeScale ℓ · chiCubeScale (ℓd)(· − (ℓd)u)` are only
nonzero strictly inside the cubes of side `ℓ` and `ℓd`, hence the window vanishes off
`dlBox ℓ d u = acube ℓ ∩ ((ℓd)u + acube (ℓd))`. -/

/-- **Coordinate bound for one scaled cube factor**: `chiCubeScale a y ≠ 0` forces every coordinate
of `y` to lie in the closed cube of side `a`. -/
lemma mem_Icc_half_of_chiCubeScale_ne {a : ℝ} (ha : 0 < a) {y : E3}
    (hy : chiCubeScale a y ≠ 0) (j : Fin 3) : y.ofLp j ∈ Set.Icc (-a / 2) (a / 2) := by
  have hb : chiCubeBase ((a⁻¹ : ℝ) • y) ≠ 0 := hy
  have hj := chiCubeBase_ofLp_abs_lt_half hb j
  have hsm : ((a⁻¹ : ℝ) • y).ofLp j = a⁻¹ * y.ofLp j := by simp
  rw [hsm, abs_mul, abs_of_pos (inv_pos.mpr ha)] at hj
  have h : |y.ofLp j| / a < 1 / 2 := by
    rw [div_eq_inv_mul]; exact hj
  have h2 : |y.ofLp j| < a / 2 := by
    have := (div_lt_iff₀ ha).mp h
    linarith [this]
  rw [Set.mem_Icc]
  have hb := abs_le.mp (le_of_lt h2)
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

/-- **The support of the smooth cube window is contained in the sliding box** — the `chiCubeB`
twin of `Work.SlotWord.chiSmallB_support_mem_dlBox`.  Both factors are cube bumps, so this is
exactly `Function.support (chiCubeB M ℓ d u) ⊆ dlBox ℓ d u`. -/
theorem chiCubeB_eq_zero_off_dlBox {M : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3)
    {z : E3} (hz : z ∉ Submission.BoseGases.dlBox ℓ d u) : chiCubeB M ℓ d u z = 0 := by
  have hℓd : 0 < ℓ * d := mul_pos hℓ hd
  by_contra hne
  have h1 : chiCubeScale ℓ z ≠ 0 := fun h => hne (by unfold chiCubeB; rw [h, zero_mul])
  have h2 : chiCubeScale (ℓ * d) (z - (ℓ * d) • u) ≠ 0 :=
    fun h => hne (by unfold chiCubeB; rw [h, mul_zero])
  refine hz ?_
  rw [Submission.BoseGases.mem_dlBox_iff]
  refine ⟨?_, ?_⟩
  · rw [Submission.BoseGases.mem_acube_iff]
    intro j
    exact mem_Icc_half_of_chiCubeScale_ne hℓ h1 j
  · rw [Submission.BoseGases.mem_acube_iff]
    intro j
    exact mem_Icc_half_of_chiCubeScale_ne hℓd h2 j

/-! ## 2. The target -/

theorem chiCubeB_fsKinPGenIntegrable {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1)
    {M : ℕ} (hM : 5 ≤ M) (u : EuclideanSpace ℝ (Fin 3))
    (hVpos : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {c : ℝ} (hc : 0 < c) {Ψ : Submission.BoseGases.X n → ℝ} (hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.fsKinCoeff c ‖q‖ *
      Work.BoseFixB1.boxWinModePGen ℓ (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) (Work.BoseFixB1B.chiCubeB M ℓ d u) Ψ q) := by
  exact Work.BoseFixB1B.pairRung.fsKinPGenIntegrable (n := n) (a := ℓ)
    (volA := Work.SmallBoxSliding.boxMass ℓ d u) (c := c)
    (Ac := Submission.BoseGases.dlBox ℓ d u) (χ := Work.BoseFixB1B.chiCubeB M ℓ d u)
    (Ψ := Ψ) hℓ (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
    (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
    (Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u) hVpos
    (chiCubeB_contDiff M ℓ d u) (chiCubeB_hasCompactSupport (M := M) hℓ u)
    (fun z hz => chiCubeB_eq_zero_off_dlBox hℓ hd u hz)
    (fun z => chiCubeB_nonneg M ℓ d u z) hc (hΨc := hΨc)

end

end Work.BoseFixB1B
