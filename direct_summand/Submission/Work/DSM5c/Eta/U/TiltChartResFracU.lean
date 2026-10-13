import Mathlib
import Submission.Work.DSM5c.Eta.U.Setup
import Submission.Work.DSM5c.ChartPresheaf

universe a

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.DSM5c.Eta.U

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

/-!
# DSM5c / Eta — the restriction maps send the tilted chart fractions to themselves

`Work.DSM5c.tiltChartRes Q … h : R_S →+* R_T` (`S ⊆ T`) is, by definition, the localisation map
`DSMap.Mix2.locRes` between the ambient localisations `(W♭)_{t_S} → (W♭)_{t_T}`, restricted to the
perfected tilted chart subalgebras.  The tilted chart fraction `fracU Q … S i k hi = u_k/u_i` is
built from an element of `W♭` and the unit `unitU Q … S i hi = u_i ∈ (W♭)_{t_S}`.

Since `locRes` is a `PreTilt W p`-algebra map, it is the identity on the image of `W♭` and hence
sends the unit `u_i ∈ (W♭)_{t_S}` to the unit `u_i ∈ (W♭)_{t_T}`; multiplicativity then gives the
compatibility of the chart fractions, which is the input needed to see that `fracU` is a section of
the chart map `η` and that `tiltChartRes` is compatible with it.
-/

section Setup

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type a} [DecidableEq ι]
  (Q : PerfectoidData p W)
  (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
  (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)

/-- **`locRes` is the identity on the units `unitU`**: the localisation map
`(W♭)_{t_S} → (W♭)_{t_T}` is a `PreTilt W p`-algebra map, so it fixes the image of `u_i ∈ W♭`,
which is exactly `unitU Q … S i hi` (resp. `unitU Q … T i (h hi)`). -/
theorem locRes_unitU {S T : Finset ι} (h : S ⊆ T) {i : ι} (hi : i ∈ S) :
    DSMap.Mix2.locRes (chartTiltGen Q t tr htr0 htr j₀ e) h
        ↑(unitU Q t tr htr0 htr j₀ e S i hi)
      = ↑(unitU Q t tr htr0 htr j₀ e T i (h hi)) := by
  rw [unitU_spec, unitU_spec]
  exact AlgHom.commutes _ _

/-- **`locRes` is the identity on the inverses of the units `unitU`**: immediate from
`locRes_unitU`, since a ring hom sends a product equal to `1` to a product equal to `1`. -/
theorem locRes_unitU_inv {S T : Finset ι} (h : S ⊆ T) {i : ι} (hi : i ∈ S) :
    DSMap.Mix2.locRes (chartTiltGen Q t tr htr0 htr j₀ e) h
        ↑((unitU Q t tr htr0 htr j₀ e S i hi)⁻¹)
      = ↑((unitU Q t tr htr0 htr j₀ e T i (h hi))⁻¹) := by
  apply Units.eq_inv_of_mul_eq_one_right (u := unitU Q t tr htr0 htr j₀ e T i (h hi))
  rw [← locRes_unitU Q t tr htr0 htr j₀ e h hi]
  rw [← map_mul, Units.inv_mul, map_one]

end Setup

/-- **The chart fractions are compatible with the restriction maps**: `tiltChartRes` sends
`u_k/u_i ∈ R_S` to `u_k/u_i ∈ R_T` for `S ⊆ T`, `i ∈ S`.  Both sides are elements of the subtype
`R_T ⊆ (W♭)_{t_T}`; the claim reduces to the ambient localisation, where it is multiplicativity of
`locRes` together with `locRes_unitU_inv`. -/
theorem tiltChartRes_fracU {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type a} [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W)
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    {S T : Finset ι} (h : S ⊆ T) {i : ι} (hi : i ∈ S) (k : ι) :
    Work.DSM5c.tiltChartRes Q t tr htr0 htr j₀ e h
        (Work.DSM5c.Eta.U.fracU Q t tr htr0 htr j₀ e S i k hi)
      = Work.DSM5c.Eta.U.fracU Q t tr htr0 htr j₀ e T i k (h hi) := by
  apply Subtype.ext
  rw [Work.DSM5c.tiltChartRes_coe]
  simp only [Work.DSM5c.Eta.U.fracU]
  rw [map_mul, AlgHom.commutes, locRes_unitU_inv]

end Work.DSM5c.Eta.U
