import Mathlib
import Submission.Work.Drive.N2.MobiusChainX
import Submission.Work.Drive.N2C.mfrCoreRowsX

/-!
# Instantiating H8's Möbius chain with the lane's core rows

`Work.Drive.N2.MfrX.coreRowsLane` is the `hcore` hypothesis of
`Submission/Work/Drive/N2/MobiusChainX.lean`, discharged from the lane's single remaining lemma
`Work.Drive.N2C.mfrCoreRowsX` (whose conclusion is the same statement with the region family
`mfrRegions` written in inlined `if`-form; `xRegions` is definitionally that).
-/

open scoped Manifold ContDiff Topology

namespace Work.Drive.N2.MfrX

open Set Filter

/-- **The core rows, from the lane's lemma.** -/
theorem coreRowsLane {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] :
    ∀ {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
      (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
      (hsep : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η < 2 * D.ηd)
      (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
      (S : Work.Drive.N2Lead.MobiusPacket D η) (hshape : Work.Drive.N2C.MobiusShape D η S),
      CoreRows D η S := by
  intro f p D η hη hsmall hsep hf S hshape
  obtain ⟨ε, εp, Dp, hε, hεp, hDp, hcov, hrate, hray⟩ :=
    Work.Drive.N2C.mfrCoreRowsX D hη hsmall hsep hf S hshape
  refine ⟨ε, εp, Dp, hε, hεp, hDp, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨k, hk⟩ := hcov y hy
    refine ⟨k, ?_⟩
    by_cases hk' : k = S.i <;>
      simpa [Work.Drive.N2.MfrX.xRegions, Work.Drive.N2.MfrX.xCentres, hk'] using hk
  · intro y k hy hk
    have hk' : Work.Drive.N2Lead.proj2
        (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)
        ∈ (if k = S.i then Metric.ball (0 : ℂ) (Dp + 5)
            else Metric.ball (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos S.n k)
              + (Dp : ℂ) * Complex.I) 2) := by
      by_cases hki : k = S.i <;>
        simpa [Work.Drive.N2.MfrX.xRegions, Work.Drive.N2.MfrX.xCentres, hki] using hk
    exact ⟨(hrate y k hy hk').1, (hrate y k hy hk').2⟩
  · intro k
    refine ⟨?_, ?_⟩
    · by_cases hk : k = S.i <;>
        simpa [Work.Drive.N2.MfrX.xRays, hk] using (hray k).1
    · intro x y hx hy h1 h2
      refine (hray k).2 x y hx hy ?_ ?_
      · by_cases hk : k = S.i <;>
          simpa [Work.Drive.N2.MfrX.xCentres, Work.Drive.N2.MfrX.xRays, hk] using h1
      · by_cases hk : k = S.i <;>
          simpa [Work.Drive.N2.MfrX.xCentres, Work.Drive.N2.MfrX.xRays, hk] using h2

end Work.Drive.N2.MfrX
