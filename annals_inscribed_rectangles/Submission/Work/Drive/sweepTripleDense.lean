import Mathlib
import Submission.Work.Drive.identity_of_dense_localconst
import Submission.Work.Drive.sideGerm
import Submission.Work.Drive.OrderBase

/-!
# `hdense` for the germ count, from the identity at the *good* triples

`Work.Drive.parityCore_of_sideGerm` (`sideGerm.lean`) takes, as two of its three inputs, the
antisymmetry `hn2` and the *functional identity on a dense set of triples* `hdense` for the germ
count.  This file shows that `hdense` needs **no density bookkeeping in the final statement**: it
follows from

* the identity at the *good* triples (`hid`), and
* the density of the good triples in the relevant region (`hdense`),

by `Work.Drive.identity_of_dense_localconst` (the "dense match + locally constant ⟹ equality" step),
applied to the germ value `n := sideGerm Ξ Q c` on `Z := Zc γ`: the local constancy is
`Work.Drive.sideGerm_hn4` (the angle-locality of the germ, i.e. the route's `hn4`) and the
negation-stability of `Zc γ` is `Work.Drive.neg_mem_Zc`.

So the design's remaining obligation for `hdense` is exactly the identity at the generic triples —
which is what the transport's multiplicativity (T6) + the triple engine produce
(`SWEEP_TRIPLE_GENERIC_STATUS.md` §6).
-/

set_option linter.style.haveILetI false

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

noncomputable section

/-- **The angle-locality of the germ value in the `nhds`-membership form** (the hypothesis shape of
`Work.Drive.identity_of_dense_localconst`). -/
lemma sideGerm_hnloc {γ : Circle → ℝ × ℝ} {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace) (c : ℝ)
    (hΞ : ChartPert Q m Ξ)
    (hQ : IsChartData Q) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hdisj : ∀ x : Zc γ, Disjoint (chartDisk Q) (rotCapping (x : UnitAddCircle) '' chartDisk Q)) :
    ∀ x ∈ Zc γ, ∀ᶠ y in nhds x, y ∈ Zc γ →
      sideGerm Ξ Q c y = sideGerm Ξ Q c x := by
  intro x hx
  have h := sideGerm_hn4 Ξ Q c hΞ hQ hc hcbot hdisj ⟨x, hx⟩
  rw [nhds_subtype, Filter.eventually_comap] at h
  filter_upwards [h] with y hy hyZ
  simpa using hy ⟨y, hyZ⟩

/-- **`hdense` for the germ count, from the identity at the good triples.**

This is exactly the `hdense` hypothesis of `Work.Drive.parityCore_of_sideGerm`. -/
theorem hdense_sideGerm_of_good_identity {γ : Circle → ℝ × ℝ} {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace) (c : ℝ)
    (hΞ : ChartPert Q m Ξ)
    (hQ : IsChartData Q) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hdisj : ∀ x : Zc γ, Disjoint (chartDisk Q) (rotCapping (x : UnitAddCircle) '' chartDisk Q))
    (G : Set (UnitAddCircle × UnitAddCircle))
    (hdense : ∀ a b : UnitAddCircle, a ∈ Zc γ → b ∈ Zc γ → a + b ∈ Zc γ →
      (a, b) ∈ closure (G ∩ {q : UnitAddCircle × UnitAddCircle |
        q.1 ∈ Zc γ ∧ q.2 ∈ Zc γ ∧ q.1 + q.2 ∈ Zc γ}))
    (hid : ∀ q ∈ G, q.1 ∈ Zc γ → q.2 ∈ Zc γ → q.1 + q.2 ∈ Zc γ →
      sideGerm Ξ Q c q.1 * sideGerm Ξ Q c (q.1 + q.2)
        + sideGerm Ξ Q c (-q.1) * sideGerm Ξ Q c q.2
        + sideGerm Ξ Q c (-(q.1 + q.2)) * sideGerm Ξ Q c (-q.2) = 1) :
    ∀ a b : UnitAddCircle, a ∈ Zc γ → b ∈ Zc γ → a + b ∈ Zc γ →
      (a, b) ∈ closure {q : UnitAddCircle × UnitAddCircle |
        q.1 ∈ Zc γ ∧ q.2 ∈ Zc γ ∧ q.1 + q.2 ∈ Zc γ ∧
          sideGerm Ξ Q c q.1 * sideGerm Ξ Q c (q.1 + q.2)
            + sideGerm Ξ Q c (-q.1) * sideGerm Ξ Q c q.2
            + sideGerm Ξ Q c (-(q.1 + q.2)) * sideGerm Ξ Q c (-q.2) = 1} := by
  have hident := identity_of_dense_localconst (Z := Zc γ)
    (fun u hu => neg_mem_Zc (γ := γ) hu)
    (fun w : UnitAddCircle => sideGerm Ξ Q c w)
    (sideGerm_hnloc Ξ Q c hΞ hQ hc hcbot hdisj) G hdense hid
  intro a b ha hb hab
  refine subset_closure ⟨ha, hb, hab, hident a b ha hb hab⟩

end

end Work.Drive
