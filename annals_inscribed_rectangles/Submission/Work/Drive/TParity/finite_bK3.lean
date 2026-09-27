import Mathlib
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.TParity.LocalGraph
import Submission.Work.Drive.TParity.ChartDeriv
import Submission.Work.Drive.TParity.isolated_of_face3
import Submission.Work.Drive.TParity.face_data_K3
import Submission.Work.Drive.cofactor_restrict_surjective
import Submission.Work.Drive.finite_of_isCompact_of_isolated

/-!
# Finiteness of the boundary part of the triple intersection set

`Work.Drive.TParity.finite_bK3`: for three smooth chains `D 0, D 1, D 2 : ℝ³ → M` in a smooth
`4`-manifold which meet transversally (`transHyp`) and cross the faces of the nine-box in the
prescribed way (`faceHyp`), the set `bK3 D` of triple intersection points on the boundary of the
nine-box is finite.

This is the finiteness half of the mod-2 parity statement for three chains, the exact analogue of
`Work.Drive.ManifoldParity.finite_bInterSet` for two chains.  The argument is:

* `bK3 D` is closed (the condition `meet3` is the coincidence of two continuous maps into the
  Hausdorff space `M`, and `unitBoxBdry 8` is closed), hence compact as a subset of the compact
  nine-box;
* each `b ∈ bK3 D` is isolated in `bK3 D`: the face hypothesis gives the block `k` and coordinate
  `i'` of the face crossed at `b`, and the vanishing coordinate of a common direction of the three
  derivatives.  That common direction spans the kernel of the charted difference map (which is a
  submersion by `transHyp`), so its non-vanishing at the coordinate `bIdx k i'` makes the
  restriction of the derivative to the hyperplane `{v | v (bIdx k i') = 0}` surjective; the local
  graph theorem `isolated_of_face3` then gives the neighbourhood.
* `Work.Drive.finite_of_isCompact_of_isolated` concludes.
-/

namespace Work.Drive.TParity

open scoped Manifold ContDiff Topology
open Manifold Set

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- **The face criterion for the charted difference map of three chains.**  If the charted
difference map is a submersion at a triple intersection point `x` of the chart region, and a common
direction `v` of the three derivatives has non-zero `i`-th coordinate (as a point of the nine-box,
i.e. `mk3 v i ≠ 0`), then the restriction of the derivative to the coordinate hyperplane
`{w | w i = 0}` is surjective.

Indeed the kernel of the derivative is one-dimensional and spanned by the cofactor vector; it is
spanned by the non-zero kernel vector `mk3 v`, and the restriction to the hyperplane is surjective
iff the kernel direction is not tangent to it, iff the `i`-th coordinate does not vanish
(`Work.Drive.surjective_domRestrict_iff_cofactorVec_ne_zero` and
`Work.Drive.cofactorVec_apply_ne_zero_iff`). -/
theorem chartDiff3_domRestrict_surjective (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (𝓡 3) (𝓡 4) Ctop (D k))
    {x : Amb 8} (hx : x ∈ region3 p D) (hm : meet3 D x)
    (hsurj : Function.Surjective (fderiv ℝ (chartDiff3 p D) x))
    {i : Fin 9} {v : Fin 3 → EuclideanSpace ℝ (Fin 3)}
    (hv : Work.Drive.TripleCommonDir (md3 D 0 x) (md3 D 1 x) (md3 D 2 x) v)
    (hi : mk3 v i ≠ 0) :
    Function.Surjective (fun w : {w : Amb 8 // w i = 0} =>
      fderiv ℝ (chartDiff3 p D) x w.1) := by
  have hk : fderiv ℝ (chartDiff3 p D) x (mk3 v) = 0 :=
    chartDiff3_eq_zero_of_commonDir p D hD hx hm hv
  have hne : mk3 v ≠ 0 := fun h => hi (by rw [h]; rfl)
  exact (Work.Drive.surjective_domRestrict_iff_cofactorVec_ne_zero
      (fderiv ℝ (chartDiff3 p D) x) hsurj i).mpr
    ((Work.Drive.cofactorVec_apply_ne_zero_iff (fderiv ℝ (chartDiff3 p D) x) hsurj hk hne i).mpr hi)

/-- The triple intersection set is compact: it is a closed subset of the compact nine-box. -/
theorem isCompact_bK3 (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, Continuous (D k)) : IsCompact (bK3 D) := by
  have h1 : IsClosed {x : Amb 8 | D 0 (bPartC 0 x) = D 1 (bPartC 1 x)} :=
    isClosed_eq ((hD 0).comp (bPartC 0).continuous) ((hD 1).comp (bPartC 1).continuous)
  have h2 : IsClosed {x : Amb 8 | D 0 (bPartC 0 x) = D 2 (bPartC 2 x)} :=
    isClosed_eq ((hD 0).comp (bPartC 0).continuous) ((hD 2).comp (bPartC 2).continuous)
  have hclosed : IsClosed (bK3 D) := by
    have hset : bK3 D = Submission.Drive.unitBoxBdry 8 ∩
        ({x : Amb 8 | D 0 (bPartC 0 x) = D 1 (bPartC 1 x)} ∩
          {x : Amb 8 | D 0 (bPartC 0 x) = D 2 (bPartC 2 x)}) := by
      ext x
      constructor
      · intro hx
        obtain ⟨hbox, hmeet, hbdry⟩ := mem_bK3.mp hx
        exact ⟨hbdry, hmeet.1, hmeet.2⟩
      · intro hx
        exact mem_bK3.mpr ⟨hx.1.1, ⟨hx.2.1, hx.2.2⟩, hx.1⟩
    rw [hset]
    exact (isClosed_unitBoxBdry 8).inter (h1.inter h2)
  exact (isCompact_unitBox 8).of_isClosed_subset hclosed (fun x hx => (mem_bK3.mp hx).1)

/-- **Finiteness of the boundary part of the triple intersection set.**  For three smooth chains
`D 0, D 1, D 2 : ℝ³ → M` in a smooth `4`-manifold `M`, meeting transversally (`htrans`) and
satisfying the face hypothesis `hface` (every boundary triple point lies on exactly one face of the
nine-box, the other coordinates strictly inside, with a common tangent direction non-zero in that
coordinate), the set `bK3 D` of triple intersection points on the boundary of the nine-box is
finite. -/
theorem finite_bK3 {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (D k))
    (htrans : Work.Drive.TParity.transHyp D) (hface : Work.Drive.TParity.faceHyp D) :
    (Work.Drive.TParity.bK3 D).Finite := by
  classical
  have hisol : ∀ b ∈ Work.Drive.TParity.bK3 D,
      ∃ U : Set (Work.Drive.Amb 8), IsOpen U ∧ b ∈ U ∧
        U ∩ Work.Drive.TParity.bK3 D ⊆ {b} := by
    intro b hb
    obtain ⟨hbox, hmeet, hbdry⟩ := mem_bK3.mp hb
    obtain ⟨k, i, hbi, hinside, hinside', v, hvcd, hvi⟩ := hface b hbox hmeet hbdry
    have hreg : b ∈ region3 (D 0 (bPartC 0 b)) D := mem_region3_self D hmeet
    have hsurj : Function.Surjective (fderiv ℝ (chartDiff3 (D 0 (bPartC 0 b)) D) b) :=
      chartDiff3_surj D hD hreg hmeet (htrans b hbox hmeet)
    have hsurj_p : Function.Surjective
        (fun w : {w : Work.Drive.Amb 8 // w (Work.Drive.bIdx k i) = 0} =>
          fderiv ℝ (chartDiff3 (D 0 (bPartC 0 b)) D) b w.1) :=
      chartDiff3_domRestrict_surjective (D 0 (bPartC 0 b)) D hD hreg hmeet hsurj hvcd
        (by rw [mk3_bIdx]; exact hvi)
    refine isolated_of_face3 D hD hbox hmeet (Work.Drive.bIdx k i) hbi ?_ hsurj_p
    intro q hq
    obtain ⟨k', j', hkj⟩ : ∃ (k' j' : Fin 3), Work.Drive.bIdx k' j' = q :=
      ⟨⟨q.val / 3, by omega⟩, ⟨q.val % 3, by omega⟩, by
        ext
        rw [Work.Drive.bIdx_val]
        have h := Nat.mod_add_div q.val 3
        omega⟩
    rw [← hkj] at hq ⊢
    by_cases hkk : k' = k
    · subst hkk
      exact hinside j' (fun hj => hq (by rw [hj]))
    · exact hinside' k' hkk j'
  have hKc : IsCompact (Work.Drive.TParity.bK3 D) :=
    isCompact_bK3 D (fun k => (hD k).continuous)
  exact Work.Drive.finite_of_isCompact_of_isolated hKc hisol

end

end Work.Drive.TParity
