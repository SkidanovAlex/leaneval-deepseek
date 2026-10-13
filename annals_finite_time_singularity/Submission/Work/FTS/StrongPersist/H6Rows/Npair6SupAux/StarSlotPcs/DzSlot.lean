/-
# The `D_zF_*`-slot: `z/(1+z)·D_zF_* = ((1-z)/(1+z))·(α·AK α)`

The extra factor `X z = (1-z)/(1+z)` is *radial* with bounded `D_z`-iterates
(`DzdIter_oneSubOneAdd_le_local`), so `radialBounded6_majorant` (this directory) gives

  `HkIntegrand α 6 (X·g) ≤ 10⁸·B²·HkIntegrand α 6 g`

on the open quadrant for every `g`; combined with `alphaAK_integrand_le` and the vanishing of
the integrand at the boundary of `Iz × Iθ` this is the sharp bound for the slot.  Honesty comes
from `HkMemOfContMajorant` and the norm bound from `AK6.hkSq_le_of_integrand_le6`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.AK_Mem6
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialBounded6_majorant
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.HkMemOfContMajorant
import Submission.Work.FTS.OpenPkg.Good
import Submission.Work.Spaces.pz_aux
import Submission.Work.Coercivity.HkIntegrand_endpoint_zero
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.Congr
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.AKSlot
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.Identities

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The `ℋ⁶`-membership and norm bound of the `D_zF_*`-slot, given the `D_z`-jet bound of the
radial multiplier `z ↦ (1-z)/(1+z)`. -/
theorem starSlotC_aux {B : ℝ} (hB : 0 ≤ B)
    (hbnd : ∀ k : ℕ, k ≤ 6 → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter k (fun y : ℝ => (1 - y) / (1 + y)) z| ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
      Work.Spaces.HkMem α 6
          (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ∧
      Work.Spaces.HkNorm α 6
          (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ≤ C := by
  obtain ⟨R, hR0, hrad⟩ := Work.FTS.StrongPersist.AK6.akRho_jet_bound6
  obtain ⟨K, _hKpos, hKmaj⟩ := radialBounded6_majorant
  obtain ⟨_CAK, _hCAK, hAKb⟩ := Work.FTS.StrongPersist.AK_Mem6
  set Kc : ℝ := K * B ^ 2 with hKcdef
  have hKc0 : 0 ≤ Kc := by rw [hKcdef]; positivity
  have hXsm : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (1 - z) / (1 + z)) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_radial (fun n =>
      (contDiffOn_const.sub contDiffOn_id).div (contDiffOn_const.add contDiffOn_id)
        (fun z hz => by
          have hz' := hz; simp only [Set.mem_Ioi] at hz'; linarith))
  refine ⟨Real.sqrt (2 * (Kc * 700 * R * 10 ^ 4 + Kc * 49 * 10 ^ 12 * R * 700)) + 1,
    by positivity, ?_⟩
  intro α hαIoc
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  obtain ⟨hAKmem, _⟩ := hAKb α hα hα1
  have hmemAK : Work.Spaces.HkMem α 6 (fun z θ => α * Work.Construction.AK α z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 α hAKmem
  have hSOAK : Work.FTS.EllipticEst.SmoothOpen (fun z θ => α * Work.Construction.AK α z θ) :=
    smoothOpen_alphaAK α
  -- the pointwise majorant on the open quadrant
  have hmaj : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α 6
          (fun z θ => (1 - z) / (1 + z) * (α * Work.Construction.AK α z θ)) z θ
        ≤ Kc * Work.Spaces.HkIntegrand α 6
            (fun z θ => α * Work.Construction.AK α z θ) z θ := by
    intro z θ hz hθ0 hθ1
    have h := hKmaj α (fun z => (1 - z) / (1 + z))
      (fun z θ => α * Work.Construction.AK α z θ) B hXsm hSOAK hB hbnd z θ hz hθ0 hθ1
    rwa [hKcdef]
  -- extend it to the closed quadrant
  have hmaj' : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6
          (fun z θ => (1 - z) / (1 + z) * (α * Work.Construction.AK α z θ)) z θ
        ≤ Kc * Work.Spaces.HkIntegrand α 6
            (fun z θ => α * Work.Construction.AK α z θ) z θ := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · rw [← hz0, Work.FTS.LocData.HkIntegrand_zero_fst α 6 _ θ,
        Work.FTS.LocData.HkIntegrand_zero_fst α 6 _ θ, mul_zero]
    · by_cases hθi : θ ∈ Set.Ioo 0 (π / 2)
      · have hθ1 : (0 : ℝ) < θ := hθi.1
        have hθ2 : θ < Real.pi / 2 := hθi.2
        exact hmaj z θ hzpos hθ1 hθ2
      · have hs : Real.sin (2 * θ) = 0 :=
          Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
        rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α 6 _ z θ hs,
          Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α 6 _ z θ hs, mul_zero]
  -- honesty
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6
      (fun z θ => (1 - z) / (1 + z) * (α * Work.Construction.AK α z θ)) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hXsm hSOAK).continuousOn_HkIntegrand α 6
  have hmemX : Work.Spaces.HkMem α 6
      (fun z θ => (1 - z) / (1 + z) * (α * Work.Construction.AK α z θ)) :=
    Work.FTS.StrongPersist.H6Rows.N0pair6Aux.HkMemOfContMajorant α 6 hKc0 hcont hmemAK
      (fun z hz θ hθ => hmaj' z hz θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  -- the pointwise bound in the canonical shape
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6
          (fun z θ => (1 - z) / (1 + z) * (α * Work.Construction.AK α z θ)) z θ
        ≤ (1 / (1 + z) ^ 2) *
            (Kc * 700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + Kc * 49 * 10 ^ 12 * R * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
    intro z hz θ hθ
    refine le_trans (hmaj' z hz θ hθ) ?_
    have h := alphaAK_integrand_le hR0 hrad α hα hα1 z hz θ hθ
    calc Kc * Work.Spaces.HkIntegrand α 6 (fun z θ => α * Work.Construction.AK α z θ) z θ
        ≤ Kc * ((1 / (1 + z) ^ 2) * (700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + 49 * 10 ^ 12 * R * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))) :=
          mul_le_mul_of_nonneg_left h hKc0
      _ = (1 / (1 + z) ^ 2) * (Kc * (700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + 49 * 10 ^ 12 * R * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))) := by ring
      _ = (1 / (1 + z) ^ 2) * (Kc * 700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + Kc * 49 * 10 ^ 12 * R * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by ring
  have hsq := Work.FTS.StrongPersist.AK6.hkSq_le_of_integrand_le6 hα hα1
    (by positivity) (by positivity) hpt
  have hid := Dz_Fstar_eq (α := α)
  refine ⟨hkMem_congr_Izθ (fun z hz θ hθ => (hid z hz θ hθ).symm) hmemX, ?_⟩
  rw [hkNorm_congr_Izθ hid]
  have h1 : Work.Spaces.HkNorm α 6
      (fun z θ => (1 - z) / (1 + z) * (α * Work.Construction.AK α z θ))
      ≤ Real.sqrt (2 * (Kc * 700 * R * 10 ^ 4 + Kc * 49 * 10 ^ 12 * R * 700)) := by
    rw [Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt hsq
  linarith [h1,
    Real.sqrt_nonneg (2 * (Kc * 700 * R * 10 ^ 4 + Kc * 49 * 10 ^ 12 * R * 700))]

end

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
