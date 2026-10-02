import Mathlib
import Submission.Work.Whitney.ChernRelDefs
import Submission.Work.Whitney.ChernRelSeries

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `i = 1` summand of `(1 + z t) * (Σ (-1)^i z^i t^i)` at `k = m+1`

`Work.Whitney.ChernRel.twoTermSeries z` is the two-term series `1 + z t` (`0 ↦ 1`, `1 ↦ z`,
`i ↦ 0` for `i ≥ 2`) and `Work.Whitney.ChernRel.geoSeriesOf z` is the signed geometric series
`gᵢ = (-1)^i z^i`, defined by the recursion `g₀ = 1`, `g_{i+1} = - gᵢ ⌣ z`.

This module computes the `i = 1` summand of their convolution in degree `m+1`.  Since only the
`i = 0, 1` coefficients of `1 + z t` are nonzero, the summand is

  `convTerm (twoTermSeries z) (geoSeriesOf z) (m+1) 1 = z ⌣ g_m`

(up to the degree bookkeeping `2*1 + 2*m = 2*(m+1)`), and by the recursion `g_{m+1} = - z ⌣ g_m`
this is exactly `- g_{m+1}`:

  `convTerm (twoTermSeries z) (geoSeriesOf z) (m+1) 1 = - geoSeriesOf z (m+1)`.

The degree bookkeeping is handled by `Work.Whitney.ChernRel.convTerm_eq_cupChern` (which converts
the summand into the graded product `Work.Whitney.cupChern` with the cast built in) and by
`Work.Whitney.ChernRel.cupChern_comm` (commutativity of the graded product, the sign
`(-1)^{4m} = 1` being trivial), together with the cast lemmas `cohTransport_trans`,
`cohTransport_congr_proof`, `cohTransport_rfl`.

This is the `m+1`-coefficient input of the telescoping
`Work.Whitney.convSeries_twoTerm_geo`.
-/

namespace Work.Whitney

theorem convTerm_twoTerm_geo_one {B : Type} [TopologicalSpace B] (z : Work.Thom.Coh ℤ 2 B) (m : ℕ) :
    Work.LerayHirsch.convTerm (Work.Whitney.ChernRel.twoTermSeries z)
        (Work.Whitney.ChernRel.geoSeriesOf z) (m + 1) 1
      = - Work.Whitney.ChernRel.geoSeriesOf z (m + 1) := by
  -- The two degree identities of the argument (`2 * (1 + m)` and `2 * (m + 1)` are the same
  -- degree in either order) and the two-term series evaluated at `1` (`z`).
  have h1 : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
  have hα : 2 * (1 + m) = 2 * (m + 1) := by omega
  have hγ : 2 * (m + 1) = 2 * (1 + m) := by omega
  have hg : Work.Whitney.cupChern 1 m z (Work.Whitney.ChernRel.geoSeriesOf z m)
      = Work.Thom.cohTransport hγ
          (Work.Whitney.cupChern m 1 (Work.Whitney.ChernRel.geoSeriesOf z m) z) :=
    Work.Whitney.ChernRel.cupChern_comm 1 m z (Work.Whitney.ChernRel.geoSeriesOf z m)
  -- The `i = 1` summand of the convolution is the graded product `z ⌣ g_m`.
  rw [Work.Whitney.ChernRel.convTerm_eq_cupChern
      (x := Work.Whitney.ChernRel.twoTermSeries z) (y := Work.Whitney.ChernRel.geoSeriesOf z)
      (k := m + 1) (i := 1) h1]
  -- The right-hand side, by the recursion `g_{m+1} = - z ⌣ g_m`.
  rw [Work.Whitney.ChernRel.geoSeriesOf_succ z m]
  simp only [neg_neg]
  -- Normalise the degrees inside the cast (`2 * 1 = 2`, `(m+1) - 1 = m`, `twoTermSeries z 1 = z`).
  show Work.Thom.cohTransport hα
      (Work.Whitney.cupChern 1 m z (Work.Whitney.ChernRel.geoSeriesOf z m))
    = Work.Whitney.cupChern m 1 (Work.Whitney.ChernRel.geoSeriesOf z m) z
  -- Move `z` to the right with the (even-degree) commutativity of the graded product ...
  rw [hg]
  -- ... recombine the two casts, and cancel the resulting trivial cast.
  rw [Work.Whitney.cohTransport_trans hγ hα
    (Work.Whitney.cupChern m 1 (Work.Whitney.ChernRel.geoSeriesOf z m) z)]
  rw [Work.LerayHirsch.cohTransport_congr_proof (hγ.trans hα) rfl, Work.Thom.cohTransport_rfl]

end Work.Whitney
