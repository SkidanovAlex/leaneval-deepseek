import Mathlib
import Submission.Work.LerayHirsch.Splitting
import Submission.Work.LerayHirsch.TwistUnit
import Submission.Work.LerayHirsch.TwistCongr
import Submission.Work.LerayHirsch.WhitneySumSnd
import Submission.Work.LerayHirsch.exists_tautSection
import Submission.Work.LerayHirsch.localTriv_tautSectionVec
import Submission.Work.LerayHirsch.nonempty_bundleIso_twist_dual
import Submission.Work.LerayHirsch.nonempty_bundleIso_twist_whitneySum
import Submission.Work.LerayHirsch.exists_quotientBundle_descend
import Submission.Work.Whitney.nonempty_bundleIso_of_nowhereZeroSection_of_paracompact
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm
import Submission.Work.Agree.PlumbDefs
import Submission.Work.Gen.DualLineCore

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The splitting principle: `π^*E ≅ ℓ ⊕ Q` over a paracompact Hausdorff base

The main result of this module is `Work.LerayHirsch.splitsOverProj_of_paracompact`: over a
paracompact Hausdorff base (and with `P(E)` paracompact Hausdorff), the tautological sequence
`0 → ℓ → π^*E → Q → 0` of a complex gluing-data bundle `Z` **splits**:
`π^*E ≅ ℓ ⊕ Q` for a bundle `Q` presented over the cover `ι × Fin (m+1)` of the tautological line
bundle.  This is the geometric input `Work.LerayHirsch.SplitsOverProj` of the splitting principle.

The route: by `Work.Whitney.nonempty_bundleIso_of_nowhereZeroSection_of_paracompact` the twist
`ℓ^* ⊗ π^*E` — which carries the tautological nowhere-zero section
(`Work.LerayHirsch.exists_tautSection`) — splits as `W ⊕ ε¹`; tensoring by `ℓ` and cancelling
`ℓ ⊗ ℓ^* ≅ ε` gives `π^*E ≅ (ℓ ⊗ W) ⊕ ℓ ≅ ℓ ⊕ (ℓ ⊗ W)`, and `ℓ ⊗ W` is re-presented over the cover
`ι × Fin (m+1)` of `ℓ` by `Work.Agree.reindexCore`.  The chart computation that makes the
re-presentation possible is `Work.LerayHirsch.localTriv_tautSectionVec`: on each chart `(i,k)` of
`ℓ`, the chart `(((i,k),i),k)` of the complement produced by Whitney's lemma contains the whole
chart `(i,k)`, because the tautological section has `k`-th coordinate `1` there.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-! ## Two elementary facts about the charts of the tautological line bundle -/

/-- **The chart `(i,k)` of `ℓ` lies over the chart `i` of `Z`.** -/
theorem tautBaseSetProj_subset_projMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (i : ι) (k : Fin (m + 1)) :
    tautBaseSetProj Z (i, k) ⊆ projMap Z ⁻¹' Z.baseSet i := by
  intro x hx
  obtain ⟨p, rfl⟩ := surjective_mkProj Z x
  rw [mem_tautBaseSetProj_mk] at hx
  simpa using hx.1

/-- **The chart coordinates only depend on the base point and the fibre coordinate.** -/
theorem chartCoord_congr (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι)
    {p q : ↥(zeroComplement (realification Z))}
    (h1 : (p : (realification Z).TotalSpace).1 = (q : (realification Z).TotalSpace).1)
    (h2 : (p : (realification Z).TotalSpace).2 = (q : (realification Z).TotalSpace).2) :
    chartCoord Z i p = chartCoord Z i q := by
  rw [chartCoord_def, chartCoord_def, h1, h2]

/-! ## The chart of the complement of the tautological line -/

/-- **The chart of `W` produced by Whitney's lemma contains the chart `(i,k)` of `ℓ`.**  The
tautological section of `ℓ^* ⊗ π^*E` has `k`-th coordinate `1` in the chart `((i,k),i)`
(`Work.LerayHirsch.localTriv_tautSectionVec`), so the tautological line it spans lies in the chart
`(((i,k),i),k)` of the tautological quotient. -/
theorem mem_baseSet_bundleComap_tautQuotient {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (σ : C(ProjSpace Z, ↥(zeroComplement (realification (tautTwist Z)))))
    (hσproj : ∀ x, ((σ x : ↥(zeroComplement (realification (tautTwist Z)))) :
      (realification (tautTwist Z)).TotalSpace).1 = x)
    (hσvec : ∀ x, ((σ x : ↥(zeroComplement (realification (tautTwist Z)))) :
      (realification (tautTwist Z)).TotalSpace).2 = tautSectionVec Z x)
    (i : ι) (k : Fin (m + 1)) {x : ProjSpace Z} (hx : x ∈ tautBaseSetProj Z (i, k)) :
    x ∈ (bundleComap (tautQuotient (tautTwist Z)) σ).baseSet (((i, k), i), k) := by
  rw [bundleComap_baseSet, Set.mem_preimage, mem_baseSet_tautQuotient, mem_tautBaseSet]
  have hpt : (σ x : (realification (tautTwist Z)).TotalSpace)
      = (⟨x, tautSectionVec Z x⟩ : (tautTwist Z).TotalSpace) := by
    apply Bundle.TotalSpace.ext
    · exact hσproj x
    · exact heq_of_eq (hσvec x)
  refine ⟨?_, ?_⟩
  · rw [hσproj x, tautTwist_baseSet]
    refine ⟨?_, ?_⟩
    · rw [Work.Gen.dualLineCore_baseSet, tautLine_baseSet]
      exact hx
    · simpa only [bundleComap_baseSet] using tautBaseSetProj_subset_projMap Z i k hx
  · have hloc := localTriv_tautSectionVec Z i k hx
    have h1 : chartCoord (tautTwist Z) ((i, k), i) (σ x)
        = (((tautTwist Z).localTriv ((i, k), i)
            ((σ x : (realification (tautTwist Z)).TotalSpace))).2) := rfl
    rw [h1, hpt]
    exact hloc

/-! ## The splitting principle -/

/-- **The splitting principle at the projectivisation.**  Over a paracompact Hausdorff base `B` (and
with `P(E)` paracompact Hausdorff), the tautological sequence `0 → ℓ → π^*E → Q → 0` splits:
there is a complex bundle `Q` of rank `m'` over `P(E)`, presented over the cover
`ι × Fin (m'+1)` of the tautological line bundle, with `π^*E ≅ ℓ ⊕ Q`. -/
theorem splitsOverProj_of_paracompact {m' : ℕ} {B : Type} [TopologicalSpace B] [ParacompactSpace B]
    [T2Space B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m' + 1))) ι)
    [ParacompactSpace (ProjSpace Z)] [T2Space (ProjSpace Z)] :
    SplitsOverProj Z := by
  obtain ⟨σ, hσproj, hσvec⟩ := exists_tautSection Z
  let W : VectorBundleCore ℂ (ProjSpace Z) (EuclideanSpace ℂ (Fin m'))
      (((ι × Fin (m' + 1)) × ι) × Fin (m' + 1)) :=
    bundleComap (tautQuotient (tautTwist Z)) σ
  let Eps : VectorBundleCore ℂ (ProjSpace Z) (EuclideanSpace ℂ (Fin 1)) PUnit :=
    trivialVectorBundleCore ℂ (ProjSpace Z) (EuclideanSpace ℂ (Fin 1)) PUnit
  obtain ⟨eW⟩ := Work.Whitney.nonempty_bundleIso_of_nowhereZeroSection_of_paracompact
    (tautTwist Z) σ hσproj (ι₀ := PUnit)
  let τ : ι × Fin (m' + 1) →
      (ι × Fin (m' + 1)) × (((ι × Fin (m' + 1)) × ι) × Fin (m' + 1)) :=
    fun a => (a, ((a, a.1), a.2))
  have hτ : ∀ x : ProjSpace Z, ∃ a : ι × Fin (m' + 1),
      x ∈ (twistCore (tautLine Z) W).baseSet (τ a) := by
    intro x
    refine ⟨(tautLine Z).indexAt x, ?_⟩
    rw [twistCore_baseSet]
    exact ⟨(tautLine Z).mem_baseSet_at x,
      mem_baseSet_bundleComap_tautQuotient Z σ hσproj hσvec _ _
        ((tautLine Z).mem_baseSet_at x)⟩
  let Q : VectorBundleCore ℂ (ProjSpace Z) (EuclideanSpace ℂ (Fin m')) (ι × Fin (m' + 1)) :=
    Work.Agree.reindexCore (twistCore (tautLine Z) W) τ hτ
  refine ⟨Q, ?_⟩
  obtain ⟨e1⟩ := nonempty_bundleIso_twist_dual (tautLine Z) (bundleComap Z (projMap Z))
  obtain ⟨e2⟩ := nonempty_bundleIso_twist_congr (tautLine Z) (tautTwist Z) (Work.Whitney.whitneySum W Eps) eW
  obtain ⟨e3⟩ := nonempty_bundleIso_twist_whitneySum (tautLine Z) W Eps
  obtain ⟨e4⟩ := nonempty_bundleIso_twist_trivial (B := ProjSpace Z)
    (ιL := ι × Fin (m' + 1)) (ι₀ := PUnit) (tautLine Z)
  obtain ⟨e5⟩ := nonempty_bundleIso_whitneySum_snd (twistCore (tautLine Z) W)
    (twistCore (tautLine Z) Eps) (tautLine Z) e4
  obtain ⟨e6⟩ := Work.Whitney.nonempty_bundleIso_whitneySum_comm
    (twistCore (tautLine Z) W) (tautLine Z)
  obtain ⟨e7⟩ := Work.Agree.nonempty_bundleIso_reindexCore_self (twistCore (tautLine Z) W) τ hτ
  obtain ⟨e8⟩ := nonempty_bundleIso_whitneySum_snd (tautLine Z) Q (twistCore (tautLine Z) W) e7
  exact ⟨e1.symm.trans (e2.trans (e3.trans (e5.trans (e6.trans e8.symm))))⟩

end

end Work.LerayHirsch
