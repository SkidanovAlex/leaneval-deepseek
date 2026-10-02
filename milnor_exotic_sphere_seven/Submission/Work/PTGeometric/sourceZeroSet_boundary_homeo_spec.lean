import Mathlib
import Submission.Work.PTGeometric.sourceZeroSet_boundary_homeo
import Submission.Work.PTGeometric.SourceZero
import Submission.Work.PTGeometric.mem_sourceZeroSet_iff_collar
import Submission.Work.PTGeometric.SourceFamily
import Submission.Work.PTGeometric.ConcreteCollapse
import Submission.Work.PTGeometric.isEmbedding_cubeToEuc
import Submission.Work.PTGeometric.mem_range_cubeToEuc
import Submission.Work.PTGeometric.alphaFamily_corePreimage_homeo_spec

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.PTGeometric

theorem sourceZeroSet_boundary_homeo_spec {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1) :
    ∃ h : ↥(Work.PTGeometric.sourceZeroSet G m hpow ∩
        {x : EuclideanHalfSpace ((8 + k) + 1) | x.1 0 = 0}) ≃ₜ
        (Σ a : Fin m × ι, (Fam a.2).pt),
      ∀ x, ∃ u : Fin (8 + k) → unitInterval,
        (G.emb (h x).1.2).e (h x).2 = Work.Tubular.cubeToEuc (8 + k) G.R u ∧
        (Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G (Fintype.equivFin ι (h x).1.2))
          (fun n => u (finCongr (Nat.add_comm k 8) n))
          = Work.PTGeometric.alphaFamily (D := D) (Fam := Fam) G m
              (cubeCoord (k + 8) (tail (k + 8) (srcCast k x.1.1))) := by
  classical
  -- the first stage: the boundary part of the zero set is the cube core preimage, explicitly
  obtain ⟨h₁, h₁spec⟩ := sourceZeroSet_boundary_homeo_cubeCast (D := D) (Fam := Fam) G m hpow
  -- the second stage: the cube core preimage is the pieces, with its coordinate formula
  obtain ⟨H, Hspec⟩ := alphaFamily_corePreimage_homeo_spec (D := D) (Fam := Fam) G m
  refine ⟨h₁.trans H, fun x => ?_⟩
  obtain ⟨u, hu₁, hu₂⟩ := Hspec (h₁ x)
  refine ⟨u, ?_, ?_⟩
  · rw [Homeomorph.trans_apply]
    exact hu₁
  · rw [Homeomorph.trans_apply, ← h₁spec x]
    exact hu₂

end Work.PTGeometric
