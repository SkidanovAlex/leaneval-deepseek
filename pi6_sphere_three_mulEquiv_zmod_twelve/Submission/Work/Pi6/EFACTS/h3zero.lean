import Mathlib
import Submission.Work.Pi6.EFACTS.Basic
import Submission.Work.Pi6.EFACTS.subH2
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.EFACTS

set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

/-- **`H³(S³⟨3⟩;ℤ) = 0`.**  The cover `E = Ecov g3` of `S³` is `3`-connected (Serre's connected
cover), so its integral reduced homology vanishes in degrees `0 < i ≤ 3`
(`Work.Pi6.SQASM.connHomology`); in particular `H₂(E;ℤ) = H₃(E;ℤ) = 0`.  The Kronecker pairing
`H³(E;ℤ) → Hom(H₃(E;ℤ), ℤ)` is bijective in degree `3` as soon as `H_k(E;ℤ)` is free for `k < 3`
(`Work.Pi6.K2Z.kronH_bij`, with `H₀` free by `homology_zero_free` and `H₁`, `H₂` subsingleton, hence
free); its target vanishes because `H₃(E;ℤ) = 0`, hence so does its source. -/
theorem h3zero {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3)) (hP3 : Work.Pi6.PostnikovData 3 12 g3 Work.Pi6.s3) : Subsingleton (Work.Pi6.Coh ℤ (Work.Pi6.Ecov g3) 3) := by
  -- `E = S³⟨3⟩` is 3-connected
  have hconn : ∀ i : ℕ, i ≤ 3 →
      Subsingleton (HomotopyGroup (Fin i) (Work.Pi6.Ecov g3) (Work.Pi6.e0 g3)) :=
    (Work.Serre.serreConnectedCover 3 12 (by norm_num) (by norm_num) Work.Pi6.S3 Work.Pi6.s3 P3 g3
      (fun i hi => hP3.1 i hi Work.Pi6.s3) hP3.2).1
  have hZ1 : IsZero (Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 1) :=
    Work.Pi6.SQASM.connHomology (Work.Pi6.e0 g3) 3 1 hconn (by norm_num) (by norm_num)
  have hZ2 : IsZero (Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 2) :=
    Work.Pi6.SQASM.connHomology (Work.Pi6.e0 g3) 3 2 hconn (by norm_num) (by norm_num)
  have hZ3 : IsZero (Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 3) :=
    Work.Pi6.SQASM.connHomology (Work.Pi6.e0 g3) 3 3 hconn (by norm_num) (by norm_num)
  haveI hS1 : Subsingleton (↥(Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 1)) :=
    ModuleCat.isZero_iff_subsingleton.mp hZ1
  haveI hS2 : Subsingleton (↥(Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 2)) :=
    ModuleCat.isZero_iff_subsingleton.mp hZ2
  have hS3 : Subsingleton (↥(Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 3)) :=
    ModuleCat.isZero_iff_subsingleton.mp hZ3
  -- the homology below degree `3` is free
  have hfree : ∀ k : ℕ, k < 3 → Module.Free ℤ (Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) k) := by
    intro k hk
    interval_cases k
    · exact Work.Cohomology.homology_zero_free (TopCat.of (Work.Pi6.Ecov g3))
    · exact inferInstance
    · exact inferInstance
  -- the Kronecker pairing in degree `3` is bijective
  let X' := TopCat.toSSet.obj (TopCat.of (Work.Pi6.Ecov g3))
  have hbij := Work.Pi6.K2Z.kronH_bij (Work.Pi6.Ecov g3) 3 hfree
  -- its target is a subsingleton because `H₃(E;ℤ) = 0`
  have hsubcod : Subsingleton (↥((Work.Cohomology.chainC ℤ X').homology 3) →ₗ[ℤ] ℤ) := by
    haveI : Subsingleton (↥((Work.Cohomology.chainC ℤ X').homology 3)) := hS3
    refine ⟨fun f g => ?_⟩
    ext x
    have hx : x = 0 := Subsingleton.elim x 0
    simp [hx]
  haveI := hsubcod
  exact ⟨fun a b => hbij.1 (Subsingleton.elim _ _)⟩

end Work.Pi6.EFACTS
