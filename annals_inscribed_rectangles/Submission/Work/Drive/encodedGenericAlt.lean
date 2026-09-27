import Mathlib
import Submission.Work.Drive.encodedEndData
import Submission.Work.Drive.encFamBoxReparam
import Submission.Work.Drive.encParReparam
import Submission.Work.Drive.encFamQ0Smooth
import Submission.Work.Drive.surjective_paramDeriv_encFamQ0
import Submission.Work.Drive.localSard_family_in_open

/-!
# `exists_homotopy_meet3Hyp_encoded` — the §2.1 assembly, second proof

`Work.Drive.exists_homotopy_meet3Hyp_encoded` (`Drive/encodedGeneric.lean`) is the last **research**
obligation of the wall (`HOLE_AUDIT_2110.md`): the per-clause genericity of the ends clause.  Its proof
has two halves, and both are now on disk:

1. **the transfer half** (`Drive/encFamBoxReparam.lean`, by the `orderWitness_exists` lane):
   `Work.Drive.exists_meet3Hyp_encFamQ0` — from a `Meet3Hyp` of the *sheared* family `encFamQ0` at a
   parameter `t : EncParQ0`, the existential conclusion with `H' = encFamWitness H (q0P t)`;
2. **the Sard half**: the localized parametric Sard `Work.Drive.localSard_family_in_open` applied to
   `encFamQ0`, whose inputs are the pointwise surjectivity
   (`Work.Drive.surjective_paramDeriv_encFamQ0`, the split into Case I/II) and the family's
   smoothness — the latter supplied by `Drive/encFamQ0Smooth.lean` (this agent, session of
   2026-09-26 ~21:5x), together with the parametrisation bridge
   `Work.Drive.hrich_reparam_encParEquiv` (`Drive/encParReparam.lean`).

This file performs the assembly (it is a differently-named duplicate of §2.1 — the `hn2`/`hdense`
lanes may use whichever lands first).  Nothing here is new mathematics: the content is the wiring.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted
attribute [local instance] Work.Drive.projTimesLineCharted Work.Drive.isManifold_projTimesLineCharted

noncomputable section

/-- **§2.1, second proof.**  From the design's data (the homotopy `H` with its two `FoldFlat` ends,
the two plane class maps `A`, `B` with `PairReg` and the two `EndTripleReg`s, and the seam identities)
there is a perturbed homotopy `H'` with the same ends whose encoded chains satisfy `Meet3Hyp`. -/
theorem exists_homotopy_meet3Hyp_encodedAlt
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
  classical
  -- the family `encFamQ0` on its own (nested-product) parameter space
  let G : Unit → EncParQ0 → Fin 3 → EuclideanSpace ℝ (Fin 3) →
      Projectivization ℝ (Eucl 3) × ℝ := fun _ t k x => encFamQ0 H A B c₀ t k x
  have hsurj : ∀ (j : Unit) (p : Projectivization ℝ (Eucl 3) × ℝ)
      (t : EncParQ0) (y : EuclideanSpace ℝ (Fin 9)),
      (∀ k : Fin 3, G j t k (TParity.bPartC k y) ∈ (chr p).source) →
      TParity.chartDiff3 p (G j t) y = 0 →
      Function.Surjective
        (fderiv ℝ (fun t' : EncParQ0 => TParity.chartDiff3 p (G j t') y) t) := by
    intro j p t y hres hz
    exact surjective_paramDeriv_encFamQ0 H A B c₀ hc₀0 hc₀1 hH hA hB hfoldA hfoldB
      hfold0 hfold1 hH0 hH1 hpair hend0 hend1 p t y hres hz
  -- the same family after the linear reparametrisation `𝔼¹⁸ ≃L EncParQ0`, as the Sard needs it
  let G' : Unit → EuclideanSpace ℝ (Fin 18) → Fin 3 → EuclideanSpace ℝ (Fin 3) →
      Projectivization ℝ (Eucl 3) × ℝ := fun _ s k x => encFamQ0 H A B c₀ (encParEquiv s) k x
  have hGsm : ∀ (j : Unit) (k : Fin 3), ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 18) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 18) × EuclideanSpace ℝ (Fin 3) => G' j q.1 k q.2) := by
    intro j k
    simpa only [G'] using contMDiff_encFamQ0_fam H A B c₀ hH hA hB k
  have hsmooth : ∀ (j : Unit) (s : EuclideanSpace ℝ (Fin 18)) (k : Fin 3),
      ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (G' j s k) := by
    intro j s k
    simpa only [G'] using contMDiff_encFamQ0_chain H A B c₀ hH hA hB k s
  have hseam : ∀ (j : Unit) (s : EuclideanSpace ℝ (Fin 18)) (k : Fin 3)
      (x : EuclideanSpace ℝ (Fin 3)), onSeam x → G' j s k x = G' j s k (seamInv x) := by
    intro j s k x hx
    simpa only [G'] using (encFamQ0_seam H A B c₀ (encParEquiv s) hseamH hseamA hseamB
      (k := k) (x := x) hx).symm
  have hrich := hrich_reparam_encParEquiv (fun _ : Unit => Projectivization ℝ (Eucl 3) × ℝ)
    G (by
      intro j k
      simpa only [G, G'] using hGsm j k) hsurj
  have hO0 : ∀ ε' : ℝ, 0 < ε' → ∃ s ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 18))), ‖s‖ < ε' :=
    fun ε' hε' => ⟨0, trivial, by simpa using hε'⟩
  obtain ⟨s, -, -, hmeet⟩ := localSard_family_in_open
    (fun _ : Unit => Projectivization ℝ (Eucl 3) × ℝ) G' hGsm hsmooth hseam hrich
    Set.univ isOpen_univ hO0 1 one_pos
  exact exists_meet3Hyp_encFamQ0 H A B (encParEquiv s) hH hseamH hA hseamA hB hseamB
    (hmeet ())

end

end Work.Drive
