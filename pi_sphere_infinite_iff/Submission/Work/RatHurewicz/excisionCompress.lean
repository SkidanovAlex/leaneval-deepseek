import Mathlib
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.excisionDefs
import Submission.Work.RatHurewicz.CompressionGeometry
import Submission.Work.RatHurewicz.pinchedMap_nullHomotopic
import Submission.Work.RatHurewicz.Triad.Convert
import Submission.Work.RatHurewicz.compression_of_relPiVanishing

/-!
# The compression criterion with restricted boundary values

`Work.RatHurewicz.compression_of_relPiVanishing` proves tom Dieck's (6.7.3)/(6.7.5) equivalence
(vanishing of the relative groups at *all* base points of the subspace ⇒ compression) in the
unrestricted form `CompressRel Y A d`.

In the single-basepoint situation of `Work.RatHurewicz.excisionRelPiVanishing` the vanishing of the
relative groups is available only at the base points that are joined to `x₀` inside the relevant
piece, and, correspondingly, only maps of pairs whose *boundary* lands in that set can be
compressed.  This file provides that restricted form:

`compressRelBd_of_relPiVanishing`: if the relative group vanishes at every point of `Bd ⊆ A`,
then every map of pairs `(I^d, ∂I^d) → (Y, A)` whose boundary lands in `Bd` is homotopic relative to
`∂I^d` into `A`, for `1 ≤ d ≤ N + 1`.

The proof is the one of `compression_of_relPiVanishing`, with the observation that the base point at
which the vanishing hypothesis is consumed (the pinch point `f (pinchBase e)`, the image of a point
of the boundary) lies in `Bd` when the boundary of `f` lands in `Bd`.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Topology unitInterval

namespace Work.RatHurewicz

open Work.Stems.Cubical

noncomputable section

/-- **The compression criterion with restricted boundary values.**  Let `Bd ⊆ A ⊆ Y` and `N : ℕ`.
If the relative group of the pair `(Y, A)` vanishes at every base point of `Bd` in degrees `≤ N`,
then every map of pairs `(I^d, ∂I^d) → (Y, A)` with `1 ≤ d ≤ N + 1` whose boundary lands in `Bd`
is homotopic relative to `∂I^d` into `A`. -/
theorem compressRelBd_of_relPiVanishing {Y : Type} [TopologicalSpace Y] {A Bd : Set Y}
    (hBA : Bd ⊆ A) (N : ℕ)
    (hvan : ∀ a : ↥Bd, ∀ k, k ≤ N →
      Subsingleton (RelHomotopyGroup (setIncl A) ⟨a.1, hBA a.2⟩ k)) :
    ∀ d, 1 ≤ d → d ≤ N + 1 → CompressRelBd A Bd d := by
  intro d hd1 hd
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hd1)
  intro f hf
  -- step 1: homotope `f` through maps of pairs to a map pinched at `f (pinchBase e) ∈ Bd`
  obtain ⟨H1, hH10, hH1A, hH1pinch⟩ := exists_pinch e f (fun x hx => hBA (hf x hx))
  -- step 2: the vanishing of the relative group at the pinch point makes it null-homotopic
  have hvan' : Subsingleton (RelHomotopyGroup (setIncl A)
      ⟨f (pinchBase e), hBA (hf _ (pinchBase_mem_boundary e))⟩ e) :=
    hvan ⟨f (pinchBase e), hf _ (pinchBase_mem_boundary e)⟩ e (by omega)
  obtain ⟨L, hL0, hLA, hL1⟩ := pinchedMap_nullHomotopic e
    ⟨f (pinchBase e), hBA (hf _ (pinchBase_mem_boundary e))⟩ hvan'
    ⟨fun x => H1 (x, 1), by fun_prop⟩ hH1pinch (fun x hx => hH1A x hx 1)
  -- step 3: concatenate the two homotopies through maps of pairs
  set Gfun : ICube (e + 1) × I → Y := fun p =>
    if (2 : ℝ) * (p.2 : ℝ) ≤ 1 then H1 (p.1, clampI (2 * (p.2 : ℝ)))
    else L (p.1, clampI (2 * (p.2 : ℝ) - 1)) with Gfun_def
  have hGcont : Continuous Gfun := by
    rw [Gfun_def]
    refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
    · exact H1.continuous.comp (continuous_fst.prodMk (continuous_clampI.comp (by fun_prop)))
    · exact L.continuous.comp (continuous_fst.prodMk (continuous_clampI.comp (by fun_prop)))
    · exact continuous_const.mul (continuous_subtype_val.comp continuous_snd)
    · exact continuous_const
    · intro p hp
      have h1 : clampI (2 * (p.2 : ℝ)) = (1 : I) := by rw [hp, clampI_one']
      have h2 : clampI (2 * (p.2 : ℝ) - 1) = (0 : I) := by
        have h2' : 2 * (p.2 : ℝ) - 1 = 0 := by rw [hp]; norm_num
        rw [h2', clampI_zero']
      rw [h1, h2]
      exact (hL0 p.1).symm
  have hGle : ∀ p : ICube (e + 1) × I, (2 : ℝ) * (p.2 : ℝ) ≤ 1 →
      Gfun p = H1 (p.1, clampI (2 * (p.2 : ℝ))) := by
    intro p h
    rw [Gfun_def]
    exact if_pos h
  have hGgt : ∀ p : ICube (e + 1) × I, ¬ (2 : ℝ) * (p.2 : ℝ) ≤ 1 →
      Gfun p = L (p.1, clampI (2 * (p.2 : ℝ) - 1)) := by
    intro p h
    rw [Gfun_def]
    exact if_neg h
  have hG0 : ∀ x : ICube (e + 1), Gfun (x, 0) = f x := by
    intro x
    rw [hGle (x, 0) (by norm_num),
      show (2 : ℝ) * (((0 : I) : ℝ)) = 0 by norm_num, clampI_zero']
    exact hH10 x
  have hGbd : ∀ x, x ∈ Cube.boundary (Fin (e + 1)) → ∀ t : I, Gfun (x, t) ∈ A := by
    intro x hx t
    by_cases h : (2 : ℝ) * (t : ℝ) ≤ 1
    · rw [hGle (x, t) h]
      exact hH1A x hx _
    · rw [hGgt (x, t) h]
      exact hLA x hx _
  have hG1 : ∀ x : ICube (e + 1), Gfun (x, 1) ∈ A := by
    intro x
    rw [hGgt (x, 1) (by norm_num),
      show (2 : ℝ) * (((1 : I) : ℝ)) - 1 = 1 by norm_num, clampI_one']
    rw [hL1 x]
    exact hBA (hf _ (pinchBase_mem_boundary e))
  -- step 4: make the homotopy relative to the boundary (tom Dieck (6.7.2))
  exact Triad.compressRel_of_homotopyPairs f ⟨Gfun, hGcont⟩ hG0 hGbd hG1

end

end Work.RatHurewicz
