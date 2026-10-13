import Mathlib
import Submission.Work.DSM5c.Eta.Setup

/-!
# `Work.DSM5c.Eta.locRes_fracT`

Naturality of the honest chart fractions `t_k/t_i` (`Work.DSM5c.Eta.fracT`) under the localisation
map `locRes t h : W_{t_S} →+* W_{t_T}` (`S ⊆ T`, `DSMap.Mix2.locRes`).

The proof is the "unit cancellation" one: both `locRes t h (fracT t S i k hi)` and
`fracT t T i k (h hi)` are characterised by multiplying with the image of `t i`, which is a unit of
`W_{t_T}` because `t i ∣ t_S ∣ t_T` (`Work.DSM5c.Eta.unitT`).  Concretely, applying `locRes t h`
to the defining relation `fracT_spec` and comparing with `fracT_spec` on `T` gives
`x * a = y * a` with `a = algebraMap W _ (t i)` a unit, whence `x = y`.
-/

namespace Work.DSM5c.Eta

open DSMap DSMap.Mix DSMap.Mix2

/-- The localisation map `locRes t h` sends the chart unit `t_i ∈ W_{t_S}` (`i ∈ S ⊆ T`) to the
corresponding chart unit of `W_{t_T}`.  (Both are `algebraMap W _ (t i)` by `unitT_spec`.) -/
theorem locRes_unitT {W : Type} [CommRing W] {ι : Type} [DecidableEq ι] (t : ι → W)
    {S T : Finset ι} (h : S ⊆ T) {i : ι} (hi : i ∈ S) :
    locRes t h ((unitT t S i hi : Localization.Away (tS t S))) =
      ((unitT t T i (h hi) : Localization.Away (tS t T))) := by
  rw [unitT_spec t S i hi, unitT_spec t T i (h hi)]
  exact AlgHom.commutes (locRes t h) (t i)

/-- **The honest chart fraction `t_k/t_i` is natural in the chart `S`**: for `i ∈ S ⊆ T`,
`locRes t h (t_k/t_i)` computed in `W_{t_S}` agrees with `t_k/t_i` computed in `W_{t_T}`. -/
theorem locRes_fracT {W : Type} [CommRing W] {ι : Type} [DecidableEq ι] (t : ι → W)
    {S T : Finset ι} (h : S ⊆ T) {i : ι} (hi : i ∈ S) (k : ι) :
    DSMap.Mix2.locRes t h (Work.DSM5c.Eta.fracT t S i k hi)
      = Work.DSM5c.Eta.fracT t T i k (h hi) := by
  -- `x := locRes t h (t_k/t_i) ∈ W_{t_T}` and `y := t_k/t_i ∈ W_{t_T}` both satisfy `· * t_i = t_k`.
  have hx : locRes t h (fracT t S i k hi) *
        algebraMap W (Localization.Away (tS t T)) (t i)
      = algebraMap W (Localization.Away (tS t T)) (t k) := by
    have h1 := congrArg (locRes t h) (fracT_spec t S i k hi)
    rw [map_mul, AlgHom.commutes, AlgHom.commutes] at h1
    simpa using h1
  have hy : fracT t T i k (h hi) * algebraMap W (Localization.Away (tS t T)) (t i)
      = algebraMap W (Localization.Away (tS t T)) (t k) := fracT_spec t T i k (h hi)
  -- the multiplier `algebraMap W _ (t i)` is a unit of `W_{t_T}` (`t i ∣ t_S ∣ t_T`).
  have hu : IsUnit (algebraMap W (Localization.Away (tS t T)) (t i)) := by
    have h2 : IsUnit (↑(unitT t T i (h hi)) : Localization.Away (tS t T)) :=
      (unitT t T i (h hi)).isUnit
    rwa [unitT_spec t T i (h hi)] at h2
  exact hu.mul_right_cancel (hx.trans hy.symm)

end Work.DSM5c.Eta
