import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.StrongPersist.H6Aux.R.SlotHigh
import Submission.Work.FTS.StrongPersist.N6_fkH
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux

/-- **The base case of the commutator induction.**  For `h` smooth on the open quadrant with honest `ℋ²`-integral, the level-one pairing of the clean operator `Lhat h = 𝓛h − Transport h` against `h` is bounded below by `-r·|h|²_{ℋ¹}`.

Route (all ingredients are already proved in this workspace): write `H1IP α (Lhat h) h` as the four `wip`-pairings `10·⟨Dz(Lhat h), Dz h⟩_η + 10¹⁰·⟨Lhat h, h⟩_η + 10¹⁷·⟨Lhat h, h⟩_{w²} + 10²¹·⟨Dth(Lhat h), Dth h⟩_γ`; expand `Lhat h = 𝓛h − Transport h = h + Dz h − χ·h − τ·Dth h` (`χ = 2/(1+z)`, `τ = 3/(1+z)`, closed by `ring`) and use the commutator identities of `LhatCommOpen` (`Dz (Lhat h) = Lhat (Dz h) + Ê₂h`, `Dth (Lhat h) = Lhat (Dth h)`); each *adjacent* pair `∫ (Dz g) g ρ` (resp. `∫ (Dth g) g ρ`) is computed by `wip_Dz_ibp` (resp. `wip_Dth_ibp`), giving `-∫ g²(zρ)'` (resp. `(q-1)∫ cos2θ g² ρ`) whose coefficients are bounded pointwise (`(z w²)'/w² = (z-3)/(1+z)`, `|(q-1)cos2θ| ≤ 1`), and the remaining terms are paired by AM–GM (`DzSelf.wip_abs_le_half`) with the pointwise bounds `|χ| ≤ 2`, `|Dz τ| ≤ 3/4`, `|Ê₂ h| ≤ (2|h| + 3|Dth h|)/4` (`E2hat_abs_le`), together with the weight comparison `sin(2θ)^{-η} ≤ sin(2θ)^{-γ}` (valid for `0 < α ≤ 1`).  Every integral is dominated by an `ℋ¹`-slot of `h` (i.e. by `H1IP α h h`), except the terms of the two ibp's applied to `g = Dz h` and `g = Dth h`, which need the `ℋ²`-slots supplied by `HkMem α 2 h`.-/
theorem base_R : ∃ r : ℝ, 0 < r ∧ ∀ α ∈ Set.Ioc 0 1, ∀ h : ℝ → ℝ → ℝ,
    Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.HkMem α 2 h →
      -r * Work.Coercivity.H1IP α h h
        ≤ Work.Coercivity.H1IP α (Work.FTS.CoercivityFix.Lhat h) h := by
  refine ⟨4 * 10 ^ 21, by norm_num, ?_⟩
  intro α hα h hs hm
  obtain ⟨hα0, hα1⟩ := hα
  have hm1 : Work.Spaces.HkMem α 1 h := Work.FTS.IPGen.HkMem_mono_le hs 1 (by norm_num) hm
  have hS1 := Work.FTS.StrongPersist.H6Aux.R.SlotOne α hα0 hα1 hs hm
  have hS2 := (Work.FTS.StrongPersist.H6Aux.R.SlotLow α hα0.le hs hm1).1
  have hS3 := (Work.FTS.StrongPersist.H6Aux.R.SlotLow α hα0.le hs hm1).2
  have hS4 := Work.FTS.StrongPersist.H6Aux.R.SlotFour α hα0 hα1 hs hm
  have hE : Work.Spaces.HkSq α 1 h ≤ Work.Coercivity.H1IP α h h :=
    Work.FTS.StrongPersist.H1IP_le_self_SO hs hm1
  have hE0 : 0 ≤ Work.Spaces.HkSq α 1 h := Work.Spaces.HkSq_nonneg α 1 h
  have hH0 : 0 ≤ Work.Coercivity.H1IP α h h := Work.Coercivity.H1IP_nonneg α h
  -- the four slot bounds, in the `H1IP`-glyph normal form
  have hS1' : -(4 : ℝ) * Work.Spaces.HkSq α 1 h ≤ Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat h)) (Work.Spaces.Dz h) := hS1
  have hS2' : -(5 : ℝ) * Work.Spaces.HkSq α 1 h ≤ Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (Work.FTS.CoercivityFix.Lhat h) h := hS2
  rw [Work.FTS.StrongPersist.H6Aux.R.Rhoq_zero] at hS3
  have hE' : Work.Spaces.HkSq α 1 h ≤
      10 * Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Spaces.Dz h) (Work.Spaces.Dz h)
        + 10 ^ 10 * Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) h h
        + 10 ^ 17 * Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) h h
        + 10 ^ 21 * Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α))
          (Work.Spaces.Dth h) (Work.Spaces.Dth h) := hE
  have hH0' : (0 : ℝ) ≤
      10 * Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Spaces.Dz h) (Work.Spaces.Dz h)
        + 10 ^ 10 * Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) h h
        + 10 ^ 17 * Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) h h
        + 10 ^ 21 * Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α))
          (Work.Spaces.Dth h) (Work.Spaces.Dth h) := hH0
  have hS3' : -(5 : ℝ) * Work.Spaces.HkSq α 1 h ≤ Work.Coercivity.wip
      (fun z _ => Work.Spaces.w z ^ 2) (Work.FTS.CoercivityFix.Lhat h) h := hS3
  have hS4' : -(3 : ℝ) * Work.Spaces.HkSq α 1 h ≤ Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α))
      (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat h)) (Work.Spaces.Dth h) := hS4
  rw [Work.Coercivity.H1IP]
  rw [Work.Coercivity.H1IP]
  linarith [hS1', hS2', hS3', hS4', hE', hE0, hH0']

end Work.FTS.StrongPersist.H6Aux
