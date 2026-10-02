import Mathlib
import Submission.Work.ThomBordism.alphaFamily_corePreimage_homeo_spec_coord
import Submission.Work.PTGeometric.sourceZeroSet_boundary_homeo_spec

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

theorem sourceZeroSet_boundary_homeo_spec_coord
    {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1) :
    ∃ h : ↥(Work.PTGeometric.sourceZeroSet G m hpow ∩
        {x : EuclideanHalfSpace ((8 + k) + 1) | x.1 0 = 0}) ≃ₜ
        (Σ a : Fin m × ι, (Fam a.2).pt),
      ∀ x, (G.emb (h x).1.2).e (h x).2
            = Work.Tubular.cubeToEuc (8 + k) G.R
                (Work.ThomBordism.blockTubePoint G m
                  (Work.PTGeometric.cubeCoord (k + 8)
                    (Work.PTGeometric.tail (k + 8) (Work.PTGeometric.srcCast k x.1.1))))
        ∧ ((h x).1.1 : ℕ)
            = (Work.ThomBordism.outerStep G m
                (Work.PTGeometric.cubeCoord (k + 8)
                  (Work.PTGeometric.tail (k + 8) (Work.PTGeometric.srcCast k x.1.1)))).1
        ∧ ((Fintype.equivFin ι (h x).1.2) : ℕ)
            = (Work.ThomBordism.innerStep G m
                (Work.PTGeometric.cubeCoord (k + 8)
                  (Work.PTGeometric.tail (k + 8) (Work.PTGeometric.srcCast k x.1.1)))).1 := by
  classical
  -- the first stage: the boundary part of the zero set is the cube core preimage, with formula
  obtain ⟨h₁, h₁spec⟩ :=
    Work.PTGeometric.sourceZeroSet_boundary_homeo_cubeCast (D := D) (Fam := Fam) G m hpow
  -- the second stage: the cube core preimage is the pieces, with the coordinate formula
  obtain ⟨H, Hspec⟩ := alphaFamily_corePreimage_homeo_spec_coord (D := D) (Fam := Fam) G m
  refine ⟨h₁.trans H, fun x => ?_⟩
  obtain ⟨hu₁, hu₂, hu₃⟩ := Hspec (h₁ x)
  rw [h₁spec x] at hu₁ hu₂ hu₃
  refine ⟨?_, ?_, ?_⟩
  · rw [Homeomorph.trans_apply]; exact hu₁
  · rw [Homeomorph.trans_apply]; exact hu₂
  · rw [Homeomorph.trans_apply]; exact hu₃

end Work.ThomBordism
