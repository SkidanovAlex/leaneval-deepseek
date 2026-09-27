import Mathlib
import Submission.Work.Drive.T6GenAtD
import Submission.Work.Drive.regBaseAssembly
import Submission.Work.Drive.ppParity.htube_of_strip
import Submission.Work.Drive.transportT6Sharp
import Submission.Work.Drive.blockT6Wrapper_of_T6GenAtD

/-!
# The per-block transport wrapper of the ends clause (`NOTES_LEAD_hodd_blockT6.md` §4.1)

**Statement (corrected hypotheses).**  `Odd (T 0) ↔ Odd (coreSideCount Q c₁ P₁) ∧ Odd (coreSideCount Q c₂ P₂)` for the
transport's top count `T 0` of the *block* triple `(diskPlane Q, P₁, P₂)` at the truncation levels
`![c₀, c₁, c₂]`, from

* the `Meet3Hyp` of that triple (`hM`) — the `s = 0` face's interiority and the collar regularity,
* the box-restricted bundle `T6GenAtDBox Q P₁ P₂ c₁ c₂` (`hgen`) — the loop and diameter clauses and
  `DiamFamRegBox`,
* the level/disjointness data of the design.

The proof (per the lead's note) is: `δc` from `hgen`, then `hregBase_design_chains`
(`regBaseAssembly.lean`, **proved**) with `hD3 := hM`, the `s = 0` interiority from
`collarInterior_zero_of_meet3Hyp` and the `s = 1` data from `pairOneData_of_T6GenAt` (both NEW, the
design lane's), the weight `w := glue (δ)` and `K := unitBox 8`, then `htube_of_strip` (**proved**), and
finally `odd_topBdryMeet_zero_iff_coreSideCount_mul_of_design_intrinsic_nf` (`transportT6Sharp.lean`,
**proved**) with `hfin`/`hbase` from `hgen.1.1`, `hfind` from `hfind_of_T6GenAt`, and `ht5` from
`odd_ncard_diamMeet_iff_coreSideCount_clampedSweep` (which reads `hgen.2` by definitional equality, now
that `DiamFamReg` is box-restricted).
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The per-block transport wrapper** (`NOTES_LEAD_hodd_blockT6.md` §4.1): the transport `T6` for one
block of the design's triple, from `Meet3Hyp` of the triple of sweeps and the box-restricted bundle.

**Statement corrected (this session).**  The hypothesis list below is the one that is *provable* (and
the one the fleet proved as `Work.Drive.blockT6Wrapper_of_T6GenAtD`, imported here): the earlier stub
carried `hlev : ∀ z, levelOf (Q z) ≠ c₂` and no `hc₁`/`hlev₁`, which is **one level band short** — the
avoidance `ftY2 x ≠ 0` of `Work.Drive.htube_of_strip` needs `c₁ < levelOf (Q z)` (see
`WALL_NODES_H3_STATUS.md` §5 and `Drive/blockT6Wrapper_of_T6GenAtD.lean`).  The conclusion is unchanged.
-/
theorem odd_topBdryMeet_zero_iff_of_T6GenAtDBox_meet3Hyp
    (Q : ℂ → CappingSpace)
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c₀ c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hP₁ : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P₁)
    (hP₂ : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P₂)
    (hP₁seam : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P₁ y = P₁ (seamInv2 y))
    (hP₂seam : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P₂ y = P₂ (seamInv2 y))
    (hdisj₁ : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 → Q z ≠ P₁ y)
    (hdisj₂ : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 → Q z ≠ P₂ y)
    (hdisj₁₂ : ∀ y y' : EuclideanSpace ℝ (Fin 2), P₁ y ≠ P₂ y')
    (hlev₁ : ∀ z : ℂ, ‖z‖ ≤ 1 → c₁ < levelOf (Q z))
    (hlev₂ : ∀ z : ℂ, ‖z‖ ≤ 1 → c₂ < levelOf (Q z))
    (hM : Meet3Hyp CappingSpace
      (fun k => clampedSweep (![c₀, c₁, c₂] k) (fun r => 1 - r)
        (![diskPlane Q, P₁, P₂] k)))
    (hgen : T6GenAtDBox Q P₁ P₂ c₁ c₂) :
    Odd (topBdryMeet CappingSpace
        (fun k => clampedSweep (![c₀, c₁, c₂] k) (fun r => 1 - r)
          (![diskPlane Q, P₁, P₂] k)) 0).ncard ↔
      Odd (coreSideCount Q c₁ P₁) ∧ Odd (coreSideCount Q c₂ P₂) :=
  blockT6Wrapper_of_T6GenAtD Q P₁ P₂ c₀ c₁ c₂ hc₁ hc₂ hQ hQseam hP₁ hP₂ hP₁seam hP₂seam
    hdisj₁ hdisj₂ hdisj₁₂ hlev₁ hlev₂ hM hgen

end

end Work.Drive
