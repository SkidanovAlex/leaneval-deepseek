import Submission.Work.PTGeometric.SourceWiring
import Submission.Work.ThomBordism.smoothingAgreement
import Submission.Work.ThomBordism.smoothingAgreement2

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism Work.ThomBordism.PontryaginThom

/-- `Work.PTGeometric.toAmbientCollapseEnd` is the collapse end of the pre-data, definitionally. -/
theorem toAmbientCollapseEnd_eq {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (hk : k ≤ n) (C : ContinuousAmbientData n k ι Fam) :
    toAmbientCollapseEnd hk C = (ambientPreData_of_continuous' hk C).ambientCollapseEnd := rfl

/-- **The raw data and the collapse end produced from them agree on the collar `S0` of the boundary.**

The chain of the source construction transforms the raw field `D.v` in three steps — the smoothing
`continuousAmbientData_of_rawData` (agreeing with `D.v` on `D.S0`), the smoothing inside
`ambientPreData_of_continuous` (agreeing on `Sh`, which contains `∂M`) and the ambient perturbation
inside `AmbientPreData.ambientCollapseEnd` (agreeing on `∂M`) — so at a boundary point of the collar
`S0` the three fields all agree with `D.v`.

This is the identification that lets the assembly state the orientation datum about the *raw* level set
`{D.v = 0}` (one of the choices of `W` that `Work.PTGeometric.AmbientOrientationDataFree` leaves free)
rather than about the produced level set: the boundary part of the level set — the end, where the
relative fundamental class meets its boundary — is the same set for both, because off the collar both
fields are bounded away from `0` (`RawAmbientData.hδ` on the raw side, `AmbientCollapseEnd.avoid` on
the produced one, using `S ⊆ S0`). -/
theorem toAmbientCollapseEnd_v_eq_on_S0 {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (hk : k ≤ n) (hk0 : 0 < k) (D : RawAmbientData n k ι Fam)
    (x : D.M) (hx : x ∈ (𝓡∂ ((8 + k) + 1)).boundary D.M) (hxS0 : x ∈ D.S0) :
    (toAmbientCollapseEnd hk (continuousAmbientDataOf hk hk0 D)).v x = D.v x := by
  have h1 : (toAmbientCollapseEnd hk (continuousAmbientDataOf hk hk0 D)).v x
      = (ambientPreData_of_continuous' hk (continuousAmbientDataOf hk hk0 D)).v x :=
    AmbientPreData.ambientCollapseEnd_v_eq_on_boundary
      (ambientPreData_of_continuous' hk (continuousAmbientDataOf hk hk0 D)) x hx
  have h2 : (ambientPreData_of_continuous' hk (continuousAmbientDataOf hk hk0 D)).v x
      = (continuousAmbientDataOf hk hk0 D).v x :=
    ambientPreData_of_continuous'_v_eqOn_Sh hk _ x
      (by rw [continuousAmbientDataOf_Sh hk hk0 D]; exact Set.mem_univ x)
  have h3 : (continuousAmbientDataOf hk hk0 D).v x = D.v x :=
    continuousAmbientDataOf_v_eqOn_S0 hk hk0 D x hxS0
  rw [h1, h2, h3]

/-- **The produced level set agrees with the raw one on the boundary** (zero-set form).

At a boundary point `x` of the raw source: if `x` lies in the raw collar `S0` then the produced field
and the raw field *agree* there (`toAmbientCollapseEnd_v_eq_on_S0`), so their zero sets coincide; and if
`x ∉ S0` then both are non-zero there — the raw one by `RawAmbientData.hδ` and the produced one by
`AmbientCollapseEnd.avoid` (using `S ⊆ S0`).

This is the identification of the boundary parts of the two level sets, i.e. the boundary part of the
level set of the produced ambient-collapse-end data — the end, where the relative fundamental class of
the null-bordism meets its boundary — is the *same set* as the boundary part of the raw level set
`{D.v = 0}`, whose collar is available (`Work.PTGeometric.producedRawData_collar`).  Hence the assembly
may state the orientation datum about the *raw* level set (a free choice of the `∃ W` in
`Work.PTGeometric.AmbientOrientationDataFree`) instead of about the produced one. -/
theorem toAmbientCollapseEnd_zero_iff_on_boundary {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (hk : k ≤ n) (hk0 : 0 < k) (D : RawAmbientData n k ι Fam)
    (x : D.M) (hx : x ∈ (𝓡∂ ((8 + k) + 1)).boundary D.M) :
    (toAmbientCollapseEnd hk (continuousAmbientDataOf hk hk0 D)).v x = 0 ↔ D.v x = 0 := by
  by_cases hxS0 : x ∈ D.S0
  · rw [toAmbientCollapseEnd_v_eq_on_S0 hk hk0 D x hx hxS0]
  · constructor
    · intro h0
      have hxS : x ∉ D.S := fun h => hxS0 (D.hSS0 h)
      exact absurd h0 ((toAmbientCollapseEnd hk (continuousAmbientDataOf hk hk0 D)).avoid x hx hxS)
    · intro h0
      have hδ := D.hδ x hx hxS0
      exact absurd h0 (norm_pos_iff.mp (lt_of_lt_of_le D.hδpos hδ))

end

end Work.PTGeometric

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism Work.ThomBordism.PontryaginThom

/-- **The boundary part of the produced level set, for the raw level set as `W`.**

With `W` chosen to be the *raw* level set `{D0.v = 0}` (one of the free choices of the `∃ W` in
`Work.PTGeometric.AmbientOrientationDataFree`), the boundary part required by that interface,
`W ∩ ∂M = S ∩ {x | v_produced x = 0}`, is the same set as the end — by
`toAmbientCollapseEnd_zero_iff_on_boundary` (the fields agree on the boundary) together with
`RawAmbientData.hzero_sub` (every boundary zero lies on the collapse end) and `S ⊆ ∂M`. -/
theorem toAmbientCollapseEnd_levelSet_bdry_eq {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Man8} [T2Space D.T]
    (hk : 11 ≤ k) (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    {x : (producedRawData hk G m hm hpow).M | (producedRawData hk G m hm hpow).v x = 0}
        ∩ (𝓡∂ ((8 + k) + 1)).boundary (producedRawData hk G m hm hpow).M
      = (producedRawData hk G m hm hpow).S ∩
        {x : (producedRawData hk G m hm hpow).M |
          (toAmbientCollapseEnd (Nat.le_add_right k G.mU)
            (producedAmbientData hk G m hm hpow)).v x = 0} := by
  classical
  set D0 := producedRawData hk G m hm hpow with hD0
  haveI : NeZero (8 + k + 1) := ⟨by omega⟩
  ext x
  constructor
  · rintro ⟨hvx, hxbd⟩
    exact ⟨D0.hzero_sub x (by simpa [hD0] using hxbd) (by simpa [hD0] using hvx),
      (toAmbientCollapseEnd_zero_iff_on_boundary (Nat.le_add_right k G.mU) (by omega) D0 x
        (by simpa [hD0] using hxbd)).mpr hvx⟩
  · rintro ⟨hxS, hvx⟩
    have hxbd : x ∈ (𝓡∂ ((8 + k) + 1)).boundary D0.M := D0.hSsub hxS
    exact ⟨(toAmbientCollapseEnd_zero_iff_on_boundary (Nat.le_add_right k G.mU) (by omega) D0 x
      hxbd).mp hvx, hxbd⟩

end

end Work.PTGeometric

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism Work.ThomBordism.PontryaginThom

/-- **The raw level set is nonempty as soon as the family is.**

The collapse end of the raw data is the disjoint union of the pieces
(`RawAmbientData.hend : ↥(S ∩ {v = 0}) ≃ₜ Σ i, (Fam i).pt`), so a point of any piece gives a point of
`S ∩ {v = 0} ⊆ {v = 0}`.  This is the `Nonempty` instance that the ORIENT route
(`Work.ThomBordism.exists_relFundClass_of_collar`) needs on the level set. -/
theorem nonempty_rawLevelSet {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι] [Nonempty ι]
    {Fam : ι → Man8} [T2Space D.T]
    (hk : 11 ≤ k) (hne : ∀ i, Nonempty (Fam i).pt)
    (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    Nonempty {x : (producedRawData hk G m hm hpow).M |
      (producedRawData hk G m hm hpow).v x = 0} := by
  classical
  set D0 := producedRawData hk G m hm hpow with hD0
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨w⟩ := hne i
  obtain ⟨x, -⟩ := D0.hend.surjective ⟨⟨⟨0, hm⟩, i⟩, w⟩
  exact ⟨⟨x.1, x.2.2⟩⟩

end

end Work.PTGeometric
