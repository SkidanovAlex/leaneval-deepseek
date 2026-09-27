import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2C.curveExistsReparamOfRangeEq
import Submission.Work.Drive.N2C.exists_localPhase_of_immersed_curve
import Submission.Work.Drive.N2C.contDiff_invFun_of_strictMono
import Submission.Work.Drive.N2Lead.exists_arcLift

/-!
# The arc lift of a level curve

`Work.Drive.N2C.arcLiftOfLevelCurves`: the statement requested for the coherent-window architecture
(`Submission/Work/Drive/N2Lead/NOTES_LEAD_coherentWindows.md`).  A smooth immersion `α : ℝ → M`
whose image on an open preconnected `J ⊆ ℝ` lies in the range of one component curve `L.γ i` of a
`LevelCurves` parametrisation of the level `f = b` *is* that component curve up to a smooth
reparametrisation `τ` with nonvanishing derivative, and `τ` is monotone.

The proof is the local-to-global gluing of anchored pieces developed in
`Submission/Work/Drive/N2Lead/exists_arcLift.lean` (`Work.Drive.N2Lead.exists_arcLift`), whose
statement differs from the one here only by two *unused* hypotheses (`SecondCountableTopology M`,
`CompactSpace M`): every brick it is built from
(`exists_local_piece_of`, `exists_continuous_lift`, `contDiffOn_of_lift`, `deriv_ne_zero_of_lift`,
`strictMonoOn_or_strictAntiOn_of_deriv_ne_zero`, `mfderiv_γ_ne_zero`) is stated in the general
context, so the same assembly applies verbatim here.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter

theorem arcLiftOfLevelCurves {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat) M]
    [T2Space M]
    {f : M → ℝ} {b : ℝ} {n : ℕ} (L : Work.Drive.N2C.LevelCurves f b n) (i : Fin n)
    {α : ℝ → M}
    (hα : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat) α)
    (hαimm : ∀ w : ℝ, mfderiv (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) α w (1 : ℝ) ≠ 0)
    {J : Set ℝ} (hJ : IsOpen J) (hJc : IsPreconnected J)
    (hJα : ∀ w ∈ J, α w ∈ Set.range (L.γ i)) :
    ∃ τ : ℝ → ℝ, ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) τ J ∧
      (∀ w ∈ J, L.γ i (τ w) = α w) ∧ (∀ w ∈ J, deriv τ w ≠ 0) ∧
      (StrictMonoOn τ J ∨ StrictAntiOn τ J) := by
  have himm : ∀ t : ℝ, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) t 1 ≠ 0 :=
    fun t => Work.Drive.N2Lead.mfderiv_γ_ne_zero L i t
  have hpiece : ∀ (w : ℝ) (hw : w ∈ J) (t : ℝ), L.γ i t = α w →
      ∃ (V : Set ℝ) (τ_V : ℝ → ℝ), V ⊆ J ∧ IsOpen V ∧ V.OrdConnected ∧ w ∈ V ∧
        ContinuousOn τ_V V ∧ (∀ u ∈ V, L.γ i (τ_V u) = α u) ∧ τ_V w = t :=
    fun w hw t ht => Work.Drive.N2Lead.exists_local_piece_of L i hα himm hJ hJc hJα w hw t ht
  obtain ⟨τ, hτc, hτγ⟩ :=
    Work.Drive.N2Lead.exists_continuous_lift hJ hJc hJα (L.modOne i) (L.per i) hpiece
  have hsm : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) τ J :=
    Work.Drive.N2Lead.contDiffOn_of_lift (L.sm i) himm hα hJ hτc hτγ
  have hderiv : ∀ w ∈ J, deriv τ w ≠ 0 :=
    Work.Drive.N2Lead.deriv_ne_zero_of_lift (L.sm i) hαimm hJ hsm hτγ
  have hmono : StrictMonoOn τ J ∨ StrictAntiOn τ J :=
    Work.Drive.N2Lead.strictMonoOn_or_strictAntiOn_of_deriv_ne_zero hJ hJc hsm hderiv
  exact ⟨τ, hsm, hτγ, hderiv, hmono⟩

end Work.Drive.N2C
