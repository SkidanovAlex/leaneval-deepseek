import Mathlib
import Submission.Work.Drive.tangencyBadSet
import Submission.Work.Drive.exists_close_transverse_noInflection
import Submission.Work.Drive.rankZeroSetTool
import Submission.Work.Drive.jets_independent
import Submission.Work.Drive.scalar_surjective_of_independent
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.fiveCollinearDefs
import Submission.Work.Drive.rank_fivePsi_slice

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant in
/-- Coefficients of the trigonometric perturbation family for which some `5`-tuple of separated
parameters inside one period gives five collinear points of the perturbed curve form a set with
empty interior, inside every ball of coefficients all of whose elements give knots.

With `Coeff`, `Kv`, `pertV`, `csep` as in `Submission/Work/Drive/tangencyBadSet.lean`, `ρ` the radius
of the coefficient ball and `k` the separation scale (`1/(k+1)` on the parameter circle), the bad
set is the projection of the zero set of
`Ψ (c,w) = (cross3 (p₂−p₁) (p₃−p₁), cross3 (p₂−p₁) (p₄−p₁), cross3 (p₂−p₁) (p₅−p₁)) ∈ Space³`
with `p i = pertV r c (w i)`, over the compact separated parameter region `w : Fin 5 → ℝ`, and the
coefficient derivative of `Ψ` has rank `6` at every zero (the two reviews of this statement supply
the argument: the coefficient derivative of the value map is the projection of five independent
evaluation functionals, Vandermonde in `z_i = exp (i w i)` with frequencies `0 … 4`, hence the five
evaluation vectors span, and the three `cross3 (·) (p₂−p₁)` slots then give rank `2 · 3 = 6 > 5`).
Then the rank form of the implicit-function dimension count
(`Work.Proj.interior_zeroSet_projection_empty_of_rank`, also copied in
`exists_close_transverse_noInflection.lean`) yields the empty interior. -/
theorem noFiveCollinear_bad_interior_empty {r : ℝ → Space} (hr : IsSmoothKnot r)
    {ρ : ℝ} (hρ : 0 < ρ) (hS : ∀ c ∈ Kv ρ, IsSmoothKnot (pertV r c)) (k : ℕ) :
    interior {c : Coeff | c ∈ Kv ρ ∧ ∃ w : Fin 5 → ℝ,
        (∀ i : Fin 5, w i ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) ∧
        (∀ i j : Fin 5, i ≠ j → (1:ℝ)/(k+1) ≤ csep (w i) (w j)) ∧
        (∃ p v : Space, v ≠ 0 ∧ ∀ i : Fin 5, ∃ t : ℝ, pertV r c (w i) = p + t • v)} = ∅ := by
  classical
  set B : Set Coeff := {c : Coeff | c ∈ Kv ρ ∧ ∃ w : Fin 5 → ℝ,
      (∀ i : Fin 5, w i ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) ∧
      (∀ i j : Fin 5, i ≠ j → (1 : ℝ) / (k + 1) ≤ csep (w i) (w j)) ∧
      (∃ p v : Space, v ≠ 0 ∧ ∀ i : Fin 5, ∃ t : ℝ, pertV r c (w i) = p + t • v)} with hB
  set Z : Set Coeff :=
    {c : Coeff | c ∈ Kv ρ ∧ ∃ w : Cfg, w ∈ Kc5 k ∧ fivePsiC r (c, w) = 0} with hZ
  -- the bad set is contained in the projection of the zero set of `fivePsiC`
  have hsub : B ⊆ Z := by
    intro c hc
    obtain ⟨hcv, w, hw1, hw2, p, v, hv, ht⟩ := hc
    refine ⟨hcv, cfgHomeo.symm w, ?_, ?_⟩
    · rw [Kc5, Set.mem_preimage, cfgHomeo.apply_symm_apply]
      exact mem_K5.mpr ⟨hw1, hw2⟩
    · have hw' : cfgEquiv (cfgHomeo.symm w) = w := by
        rw [cfgEquiv_apply, cfgHomeo.apply_symm_apply]
      show fivePsi r (c, cfgEquiv (cfgHomeo.symm w)) = 0
      rw [hw']
      show collMap5 (valMap r (c, w)) = 0
      refine collMap5_eq_zero_of_line (p := p) (v := v)
        (t := fun i => Classical.choose (ht i)) fun i => ?_
      rw [valMap_apply]
      exact Classical.choose_spec (ht i)
  -- the rank of the coefficient derivative exceeds the dimension of the parameter space
  have hrank : ∀ q ∈ Kv ρ ×ˢ Kc5 k, fivePsiC r q = 0 →
      Module.finrank ℝ Cfg < Module.finrank ℝ (fderiv ℝ (fivePsiC r) q).range := by
    intro q hq _
    obtain ⟨hqc, hqw⟩ := hq
    obtain ⟨hb, hs⟩ := mem_K5.mp hqw
    have hJ : Function.Surjective (valLin (cfgEquiv q.2)) :=
      valLin_surjective hb fun i j hij => lt_of_lt_of_le (by positivity) (hs i j hij)
    have hne : pertV r q.1 (cfgEquiv q.2 1) ≠ pertV r q.1 (cfgEquiv q.2 0) :=
      pertV_ne_of_csep_pos hr (hS q.1 hqc) (hb 1) (hb 0)
        (lt_of_lt_of_le (by positivity) (hs 1 0 (by decide)))
    have hd : pertV r q.1 (cfgEquiv q.2 1) - pertV r q.1 (cfgEquiv q.2 0) ≠ 0 :=
      sub_ne_zero.mpr hne
    have hrk := rank_fivePsi_slice hr (cfgEquiv q.2) q.1 hJ hd
    have hslice : 6 ≤ Module.finrank ℝ (LinearMap.range
        ((fderiv ℝ (fun c : Coeff => fivePsiC r (c, q.2)) q.1).toLinearMap)) := by
      show 6 ≤ Module.finrank ℝ (LinearMap.range
        ((fderiv ℝ (fun c : Coeff => fivePsi r (c, cfgEquiv q.2)) q.1).toLinearMap))
      exact hrk
    have hle := range_fderiv_slice_le (contDiff_fivePsiC hr) q
    have hmono := Submodule.finrank_mono hle
    have hfin : Module.finrank ℝ Cfg = 5 := finrank_euclideanSpace_fin
    omega
  have hZempty : interior Z = ∅ :=
    interior_zeroSet_projection_empty_of_rank (hΨ := contDiff_fivePsiC hr)
      (hKv := isCompact_Kv ρ) (hK := isCompact_Kc5 k) hrank
  have h2 : interior B ≤ (∅ : Set Coeff) := by
    calc interior B ≤ interior Z := interior_mono hsub
      _ = ∅ := hZempty
  exact le_bot_iff.mp h2

end Work.Drive
