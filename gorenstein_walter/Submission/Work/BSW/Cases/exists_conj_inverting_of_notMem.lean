import Mathlib
import Submission.Work.BSW.Basic
import Submission.Work.BSW.Cases.bswCompletionBase

namespace Work.BSW.Cases

/-- Every element `y` with `i(y) > 0` has a conjugate inverted by `t`, and that conjugate is
still outside the union of the conjugates of `C_G(t)`, with the same `i`-value.

Indeed `i(y) > 0` supplies an involution `u` inverting `y`; by condition (iv) of `BSWHyps2`,
`u` is conjugate to `t`, say `c * u * c⁻¹ = t`.  Then `x := c * y * c⁻¹` is inverted by `t`,
`x` is conjugate to `y` (so `x ∉ ⋃_g C_G(t)^g` since `y ∉ ⋃_g C_G(t)^g`), and `i` is a class
function (`iFn_conj`). -/
theorem exists_conj_inverting_of_notMem {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) {y : G}
    (hy : y ∉ {z : G | ∃ g : G, g * z * g⁻¹ ∈ Subgroup.centralizer ({t} : Set G)})
    (hy0 : 0 < Work.BSW.iFn G y) :
    ∃ x : G, x ∉ {z : G | ∃ g : G, g * z * g⁻¹ ∈ Subgroup.centralizer ({t} : Set G)} ∧
      t⁻¹ * x * t = x⁻¹ ∧ Work.BSW.iFn G x = Work.BSW.iFn G y := by
  -- an involution inverting `y`
  obtain ⟨u, hu2, huy⟩ : ∃ u : G, orderOf u = 2 ∧ u⁻¹ * y * u = y⁻¹ := by
    have hne : ({u : G | orderOf u = 2 ∧ u⁻¹ * y * u = y⁻¹} : Set G).Nonempty :=
      (Set.ncard_pos (s := {u : G | orderOf u = 2 ∧ u⁻¹ * y * u = y⁻¹})).mp hy0
    obtain ⟨u, hu⟩ := hne
    exact ⟨u, hu.1, hu.2⟩
  -- `u` is conjugate to `t`
  obtain ⟨c, hc⟩ := isConj_iff.mp (Work.BSW.involutions_conj h u hu2)
  refine ⟨c * y * c⁻¹, ?_, ?_, Work.BSW.Cases.iFn_conj c y⟩
  · -- `c * y * c⁻¹` is conjugate to `y`, hence still outside the conjugates of `C_G(t)`
    intro hmem
    obtain ⟨g, hg⟩ := hmem
    refine hy ⟨g * c, ?_⟩
    rw [show (g * c) * y * (g * c)⁻¹ = g * (c * y * c⁻¹) * g⁻¹ from by group]
    exact hg
  · -- `t` inverts `c * y * c⁻¹` because `u = c⁻¹ * t * c` inverts `y`
    rw [← hc]
    rw [show (c * u * c⁻¹)⁻¹ * (c * y * c⁻¹) * (c * u * c⁻¹) = c * (u⁻¹ * y * u) * c⁻¹
      from by group, huy]
    group

end Work.BSW.Cases
