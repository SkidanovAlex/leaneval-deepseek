import Mathlib
import Submission.Work.Drive.encFamBoxReparam
import Submission.Work.Drive.encParReparam
import Submission.Work.Drive.encFamQ0Smooth
import Submission.Work.Drive.surjective_paramDeriv_encFamQ0
import Submission.Work.Drive.localSard_family_in_open

/-!
# §2.1 (`exists_homotopy_meet3Hyp_encoded`) **proved**, by the reparametrisation route

The statement below is *verbatim* `Work.Drive.exists_homotopy_meet3Hyp_encoded`
(`Drive/encodedGeneric.lean`, the last research hole of the wall); it is proved here, so that the hole
can be closed by importing this module.

The proof is the assembly of four on-disk ingredients:

1. the **richness** of the design's family, in the `𝔼¹⁸` parametrisation: the already-proved pointwise
   form `Work.Drive.surjective_paramDeriv_encFamQ0`, transferred along the linear parametrisation by
   `Work.Drive.hrich_reparam_encParEquiv` (`Drive/encParReparam.lean`);
2. the **smoothness** data of the family in that parametrisation,
   `Work.Drive.contMDiff_encFamQ0_fam` / `contMDiff_encFamQ0_chain` (`Drive/encFamQ0Smooth.lean`) and
   the seam invariance `Work.Drive.encFamQ0_seam` (`Drive/encFamQ0.lean`);
3. the **localized parametrised Sard** `Work.Drive.localSard_family_in_open`, which produces a parameter
   `t` of arbitrarily small norm with `Meet3Hyp` of the *sheared* family;
4. the **transfer back** to the encoded chains of the perturbed homotopy,
   `Work.Drive.exists_meet3Hyp_encFamQ0` (`Drive/encFamBoxReparam.lean`), i.e. `meet3Hyp_of_boxReparam`
   applied to the design's shears and level twists.

The result is exactly the `∃ H'` of the statement, with `H' = encFamH' H (q0P t)` (the class-perturbed
homotopy), which agrees with `H` at the two ends.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.projCharted
attribute [local instance] Work.Drive.projTimesLineCharted
  Work.Drive.isManifold_projTimesLineCharted

noncomputable section

set_option maxHeartbeats 1000000

/-- **§2.1, proved**: the homotopy-genericity lemma of the ends clause.  Verbatim
`Work.Drive.exists_homotopy_meet3Hyp_encoded`. -/
theorem exists_homotopy_meet3Hyp_encoded_viaReparam
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    {c₀ : ℝ} (hc₀0 : 0 < c₀) (hc₀1 : c₀ < 1)
    (hH : ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1))))
    (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (hseamH : ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y →
      H (t, seamInv2 y) = H (t, y))
    (hseamA : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → A (seamInv2 y) = A y)
    (hseamB : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → B (seamInv2 y) = B y)
    (hH0 : ∀ s : ℝ, s ≤ 0 → ∀ y : EuclideanSpace ℝ (Fin 2), H (s, y) = H (0, y))
    (hH1 : ∀ s : ℝ, 1 ≤ s → ∀ y : EuclideanSpace ℝ (Fin 2), H (s, y) = H (1, y))
    (hpair : PairReg A B)
    (hend0 : EndTripleReg (fun y => H (0, y)) A B)
    (hend1 : EndTripleReg (fun y => H (1, y)) A B)
    (hfoldA : FoldFlat A) (hfoldB : FoldFlat B)
    (hfold0 : FoldFlat (fun y : EuclideanSpace ℝ (Fin 2) => H (0, y)))
    (hfold1 : FoldFlat (fun y : EuclideanSpace ℝ (Fin 2) => H (1, y))) :
    ∃ H' : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3),
      (∀ y, H' (0, y) = H (0, y)) ∧ (∀ y, H' (1, y) = H (1, y)) ∧
      Meet3Hyp (Projectivization ℝ (Eucl 3) × ℝ)
        (encodedChains (fun x : EuclideanSpace ℝ (Fin 3) => H' (x 2, pt2 (x 0) (x 1)))
          A B c₀) := by
  -- (1)+(2): the richness and smoothness data of the family in the `𝔼¹⁸` parametrisation
  have hsm : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 18) × EuclideanSpace ℝ (Fin 3)))
      (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 18) × EuclideanSpace ℝ (Fin 3) =>
        encFamQ0 H A B c₀ (encParEquiv q.1) k q.2) :=
    fun k => contMDiff_encFamQ0_fam H A B c₀ hH hA hB k
  have hrich : ∀ (p : Projectivization ℝ (Eucl 3) × ℝ)
      (K : Set (EuclideanSpace ℝ (Fin 9))) (s₀ : EuclideanSpace ℝ (Fin 18)) (δ : ℝ),
      IsCompact K → 0 < δ →
      (∀ (s : EuclideanSpace ℝ (Fin 18)) (y : EuclideanSpace ℝ (Fin 9)), ‖s - s₀‖ < δ → y ∈ K →
        ∀ k : Fin 3, encFamQ0 H A B c₀ (encParEquiv s) k (TParity.bPartC k y) ∈ (chr p).source) →
      ∀ (s : EuclideanSpace ℝ (Fin 18)) (y : EuclideanSpace ℝ (Fin 9)), ‖s - s₀‖ < δ → y ∈ K →
        TParity.chartDiff3 p (fun k x => encFamQ0 H A B c₀ (encParEquiv s) k x) y = 0 →
        Function.Surjective (fderiv ℝ (fun s' : EuclideanSpace ℝ (Fin 18) =>
          TParity.chartDiff3 p (fun k x => encFamQ0 H A B c₀ (encParEquiv s') k x) y) s) :=
    hrich_reparam_encParEquiv (fun _ : Unit => Projectivization ℝ (Eucl 3) × ℝ)
      (fun _ => encFamQ0 H A B c₀) (fun _ => hsm)
      (fun _ p t y hreg hz => surjective_paramDeriv_encFamQ0 H A B c₀ hc₀0 hc₀1 hH hA hB
        hfoldA hfoldB hfold0 hfold1 hH0 hH1 hpair hend0 hend1 p t y hreg hz) ()
  -- (3): the localized Sard
  obtain ⟨t, -, ht, hmeet⟩ := localSard_family_in_open
    (fun _ : Unit => Projectivization ℝ (Eucl 3) × ℝ)
    (fun _ (s : EuclideanSpace ℝ (Fin 18)) (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) =>
      encFamQ0 H A B c₀ (encParEquiv s) k x)
    (fun _ => hsm)
    (fun _ s k => contMDiff_encFamQ0_chain H A B c₀ hH hA hB k s)
    (fun _ s k x hx => (encFamQ0_seam H A B c₀ (encParEquiv s) hseamH hseamA hseamB
      (k := k) (x := x) hx).symm)
    (fun _ : Unit => hrich) Set.univ isOpen_univ
    (fun ε hε => ⟨0, Set.mem_univ 0, by simpa using hε⟩) 1 one_pos
  -- (4): the transfer back to the encoded chains of `encFamH' H (q0P t)`
  exact exists_meet3Hyp_encFamQ0 H A B (encParEquiv t) hH hseamH hA hseamA hB hseamB (hmeet ())

end

end Work.Drive
