import Mathlib
import Submission.Work.Drive.exists_continuous_chordDir
import Submission.Work.Drive.muOrd_injective_unordered
import Submission.Work.Drive.DirCTools

namespace Work.Drive

open Submission.Configuration (muOrd midPair dirPair lenPair pairVec muOrd_eq
  continuous_midPair continuous_lenPair)
open Submission.Geometry (eucNorm eucNorm_eq_zero)

/-- Off the diagonal the extended chord direction is the doubled direction of the chord. -/
lemma chordDirExt_of_ne {γ : Circle → ℝ × ℝ} {a b : Circle} (hab : a ≠ b) :
    chordDirExt γ (a, b) = Submission.Collision.dirC (γ a - γ b) := by
  unfold chordDirExt
  rw [dif_neg]
  exact hab

/-- `eucNorm` is invariant under negation. -/
lemma eucNorm_neg_ext (x : ℝ × ℝ) : eucNorm (-x) = eucNorm x := by
  simp [Submission.Geometry.eucNorm, Submission.Geometry.eucDot]

/-- Halving a doubled vector of `ℝ × ℝ`: `(a + a) / 2 = a` (the `ℝ × ℝ` version of
`add_self_div_two`, which only applies in a division semiring). -/
lemma prod_add_self_div_two (a : ℝ × ℝ) : (a + a) / 2 = a := by
  apply Prod.ext <;> simp [add_self_div_two]

/-- The extended chord direction is invariant under swapping the two points. -/
lemma chordDirExt_swap (γ : Circle → ℝ × ℝ) (x y : Circle) :
    chordDirExt γ (y, x) = chordDirExt γ (x, y) := by
  by_cases hxy : x = y
  · subst hxy; rfl
  · rw [chordDirExt_of_ne (Ne.symm hxy), chordDirExt_of_ne hxy]
    have h1 : γ y - γ x = -(γ x - γ y) := by rw [neg_sub]
    rw [h1, dirC_neg]

open Manifold in
open scoped Manifold ContDiff in
/-- **The configuration Möbius strip is an embedded strip in the configuration space.**  For a smooth
embedded closed plane curve `γ` the configuration map of the paper — midpoint, doubled direction of the
chord, length — with the *tangent* direction used on the diagonal, is a continuous map
`Circle × Circle → ℝ² × S¹ × ℝ` which is symmetric under the swap and injective on unordered pairs.

Since `Circle × Circle` is compact and the target Hausdorff, such a map descends to a topological
embedding of the Möbius band `(Circle × Circle)/swap` onto its image: the object `M` that Hugelmeyer's
capping turns into a projective plane.  Concretely, the map `μ` produced is:

* continuous (`Work.Drive.chordDirExt`, `Work.Drive.exists_continuous_chordDir` supplies the direction
  coordinate, which agrees with the doubled direction `dirC (γ x - γ y)` off the diagonal and equals the
  doubled tangent direction on it; the midpoint and the length are continuous everywhere);
* swap-invariant: swapping the two points leaves the midpoint and the length unchanged, and changes the
  chord vector into its negative, whose doubled direction is the same;
* injective on unordered pairs: if two configurations agree then their lengths agree, so either both
  pairs are diagonal — and then the midpoint `γ x` determines the point — or both are off the diagonal,
  in which case `Work.Drive.muOrd_injective_unordered` applies;
* equal to the configuration map `Submission.Configuration.muOrd` off the diagonal and equal to
  `(γ x, tangentDirC γ x, 0)` on it.

The boundary of the image is the `(2,1)`-curve `{(γ x, dirC (γ' x), 0)}` (the diagonal of
`Circle × Circle` maps to it).  Reminder: `ℝ × ℝ` carries the *sup* norm in this workspace, so
`eucNorm` (not `‖·‖`) is the length coordinate. -/
theorem exists_embedded_configuration_strip (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) :
    ∃ μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ,
      Continuous μ ∧
      (∀ x y : Circle, μ (y, x) = μ (x, y)) ∧
      (∀ x y x' y' : Circle, μ (x, y) = μ (x', y') →
        (x = x' ∧ y = y') ∨ (x = y' ∧ y = x')) ∧
      (∀ x y : Circle, x ≠ y → μ (x, y) = Submission.Configuration.muOrd γ (x, y)) ∧
      (∀ x : Circle, μ (x, x) = (γ x, Work.Drive.tangentDirC γ x, 0)) := by
  have hγc : Continuous γ := hγ.isImmersion.contMDiff.continuous
  have hinj : Function.Injective γ := hγ.isEmbedding.injective
  have hdircont : Continuous (chordDirExt γ) := by
    rw [continuous_iff_continuousAt]
    rintro ⟨x, y⟩
    by_cases hxy : x = y
    · subst hxy
      exact continuousAt_chordDirExt_diag γ hγ x
    · exact continuousAt_chordDirExt_offDiag hγc hinj hxy
  refine ⟨fun p => (midPair γ p, chordDirExt γ p, lenPair γ p), ?_, ?_, ?_, ?_, ?_⟩
  · exact (continuous_midPair hγc).prodMk (hdircont.prodMk (continuous_lenPair hγc))
  · intro x y
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show midPair γ (y, x) = midPair γ (x, y)
      simp only [midPair]
      rw [add_comm (γ y) (γ x)]
    · exact chordDirExt_swap γ x y
    · show lenPair γ (y, x) = lenPair γ (x, y)
      simp only [lenPair, pairVec]
      rw [show γ y - γ x = -(γ x - γ y) by rw [neg_sub], eucNorm_neg_ext]
  · intro x y x' y' h
    have hmid : midPair γ (x, y) = midPair γ (x', y') := congrArg Prod.fst h
    have hdir : chordDirExt γ (x, y) = chordDirExt γ (x', y') :=
      congrArg (fun q => q.2.1) h
    have hlen : lenPair γ (x, y) = lenPair γ (x', y') :=
      congrArg (fun q => q.2.2) h
    by_cases hxy : x = y
    · -- both pairs are diagonal: the midpoint determines the point
      have h0 : lenPair γ (x', y') = 0 := by
        rw [← hlen, hxy.symm]
        simp [lenPair, pairVec]
      have hz : γ x' - γ y' = 0 :=
        eucNorm_eq_zero.mp (by simpa [lenPair, pairVec] using h0)
      have hx'y' : x' = y' := hinj (sub_eq_zero.mp hz)
      have hv : γ x = γ x' := by
        have hh := hmid
        simp only [midPair] at hh
        rw [hxy.symm, hx'y'.symm] at hh
        rwa [prod_add_self_div_two (γ x), prod_add_self_div_two (γ x')] at hh
      have hx : x = x' := hinj hv
      exact Or.inl ⟨hx, hxy.symm.trans (hx.trans hx'y')⟩
    · -- both pairs are off the diagonal: reduce to `muOrd`
      have hx'y' : x' ≠ y' := by
        intro h'
        have h0 : lenPair γ (x', y') = 0 := by
          rw [h']
          simp [lenPair, pairVec]
        have hz : γ x - γ y = 0 :=
          eucNorm_eq_zero.mp (by simpa [lenPair, pairVec] using hlen.trans h0)
        exact hxy (hinj (sub_eq_zero.mp hz))
      have hdir' : dirPair γ (x, y) = dirPair γ (x', y') := by
        simp only [dirPair, pairVec]
        rw [← chordDirExt_of_ne hxy, ← chordDirExt_of_ne hx'y']
        exact hdir
      have hmueq : muOrd γ (x, y) = muOrd γ (x', y') := by
        rw [muOrd_eq γ (x, y), muOrd_eq γ (x', y')]
        exact Prod.ext hmid (Prod.ext hdir' hlen)
      exact muOrd_injective_unordered hγ hmueq
  · intro x y hxy
    rw [muOrd_eq γ (x, y)]
    exact Prod.ext rfl (Prod.ext (chordDirExt_of_ne hxy) rfl)
  · intro x
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show midPair γ (x, x) = γ x
      simp only [midPair]
      exact prod_add_self_div_two (γ x)
    · show chordDirExt γ (x, x) = tangentDirC γ x
      unfold chordDirExt
      rw [dif_pos rfl]
    · show lenPair γ (x, x) = 0
      simp [lenPair, pairVec]

end Work.Drive
