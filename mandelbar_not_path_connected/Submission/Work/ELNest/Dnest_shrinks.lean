/-
# EL nest at `b₂`: the nest shrinks to the branch point

The nest `Δ̂ₙ = S.D n` of `Work.ELNest.NestData` is the sequence of ray-polygon regions at the
branch point `b₂` of the tripod; the target of this file is `Work.ELNest.Dnest_shrinks`, the
statement that these regions shrink to the point `b₂`:

  `∀ ε > 0, ∃ N, ∀ n ≥ N, Δ̂ₙ ⊆ ball b₂ ε`.

The proof is the one described in `NOTES_LEAD_mandelbar_EL_F_contracts.md` (item N4), carried out
with the material of `Submission.Work.ELNest.Dnest_shrinks_aux`, which also exports the
reusable lemmas `NestData.g6_image` (`Δ̂ₙ₊₁ = g₆ '' Δ̂ₙ`), `NestData.g6_iterate_image`
(`Δ̂ₙ = g₆^[n] '' Δ̂₀`), `NestData.g6_b2` (the branch point is fixed by the inverse branch) and
`NestData.g6_tendsto`:

* the inverse branch `g₆ = S.g6` of `f_c^6 = F6 c` is a *bijection* `Δ̂ₙ → Δ̂ₙ₊₁`
  (`NestData.g6_image`); consequently `Δ̂ₙ = g₆^[n] '' Δ̂₀ = g₆^[n-1] '' Δ̂₁`;
* the iterates of `g₆` therefore converge locally uniformly on the open set `Δ̂₀` to the constant
  `b₂` (`NestData.g6_tendsto`): every locally uniform limit of a subsequence of the iterates is
  `b₂` (`NestData.g6_lim_eq_const`, by Montel, the identity theorem and the fact that the nest is
  *strictly* nested, `Dnest_cl`), and normality (Montel) upgrades the subsequence principle to
  convergence;
* finally `Δ̂ₙ = g₆^[n-1] '' Δ̂₁ ⊆ g₆^[n-1] '' closure Δ̂₁`, and the closure `closure Δ̂₁` is a
  compact subset of `Δ̂₀` (`Dnest_cl` and the boundedness of the nest), so uniform convergence on
  it gives the claim.
-/
import Mathlib
import Submission.Work.ELNest.Setup
import Submission.Work.ELNest.Dnest_shrinks_aux
import Submission.Work.ELTop.isOpen_polyRegion
import Submission.Work.ELTop.isClosed_polyCurve
import Submission.Work.Normal.montel_locallyBounded

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology
open scoped Topology

noncomputable section

namespace Work.ELNest

open Work.EL

variable {c : ℂ}

/-- **N4: the nest at the branch point shrinks to `b₂`.**  Every level `Δ̂ₙ = S.D n` of the nest
at `b₂` is eventually contained in any prescribed ball around `b₂`.

Indeed `Δ̂ₙ = g₆^[n-1] '' Δ̂₁`, the closure of `Δ̂₁` is a compact subset of the open set `Δ̂₀` on
which the iterates of `g₆` converge locally uniformly to the constant `b₂`, and locally uniform
convergence is uniform on compact subsets. -/
theorem Dnest_shrinks {c : ℂ} (S : Work.ELNest.NestData c) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, S.D n ⊆ Metric.ball S.b2 ε := by
  intro ε hε
  -- `closure Δ̂₁` is a compact subset of `Δ̂₀`
  have hclosed : IsClosed {z : ℂ | pot S.d.hN z ≤ Real.log S.L} :=
    isClosed_le S.d.hN.continuous_potential continuous_const
  have hbdd : Bornology.IsBounded (closure (S.D 1)) :=
    ((isCompact_le_pot S.d.hN (Real.log S.L)).isBounded).subset
      (closure_minimal (fun z hz => S.D_subset_potL 1 hz) hclosed)
  have hK : IsCompact (closure (S.D 1)) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hbdd⟩
  have hKsub : closure (S.D 1) ⊆ S.D 0 := S.Dnest_cl
  -- the iterates of `g₆` converge to `b₂` uniformly on it
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact (S.isOpen_D 0)).mp
    S.g6_tendsto (closure (S.D 1)) hKsub hK
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif ε hε)
  refine ⟨N + 1, fun n hn z hz => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : N ≤ m := by omega
  -- `Δ̂ₙ = g₆^[m] '' Δ̂₁`
  have hz' : z ∈ (S.g6^[m]) '' S.D 1 := by rw [S.g6_iterate_image_one m]; exact hz
  obtain ⟨w, hw1, hwz⟩ := hz'
  have h1 := hN m hm w (subset_closure hw1)
  rw [hwz] at h1
  rwa [Metric.mem_ball, dist_comm]

end Work.ELNest
