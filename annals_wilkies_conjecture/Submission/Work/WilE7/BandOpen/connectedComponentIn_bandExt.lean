/-
  Area E7 / BandOpen: the connected components of the strict band lift.

  `Work.WilE7.bandExt X` is the *open* cylindrical lift of a semi-Pfaffian set `X ⊆ ℝ^{n+m}`
  along the coordinate insertion at position `n`: its point set is
  `bandRel X.set ∩ cubeC (n+1+m)`, i.e. the points whose `skipInj`-projection lies in `X.set`
  and whose new coordinate lies in the open interval `(-1,1)`.

  The component of the inserted base point `insCoord n m p 0` inside `(bandExt X).set` is the
  strict band over the component of `p`: it is `bandRel (connectedComponentIn X.set p)`,
  cut by the cube.  Geometrically `bandExt X` is the cylinder over `X.set` with an open
  interval replacing `[-1,1]`, and `insCoord` is a homeomorphism onto `ℝ^{n+1+m}`, so its
  components are the cylinders over the components of `X.set`.  The two topological inputs are
  * `IsPreconnected` of `bandRel C ∩ cubeC` for `C` preconnected (it is the continuous image of
  `C ×ˢ (-1,1)` under `insCoord`),
  * and the `skipInj`-projection argument showing the component lands inside the band over `C`.
-/
import Mathlib
import Submission.Work.WilE7.BandOpenDefs
import Submission.Work.WilE8.Star.LiftDef
import Submission.Work.WilE8.Star.lift_right_cube

set_option autoImplicit false
noncomputable section
open Classical Topology
open WilkiesDesign.E

namespace Work.WilE7.BandOpen

theorem connectedComponentIn_bandExt {n m : ℕ} (X : WilkiesDesign.E.SemiPf (n + m))
    (p : Fin (n + m) → ℝ) (hp : p ∈ X.set) :
    connectedComponentIn (Work.WilE7.bandExt X).set (Work.WilE8.Star.insCoord n m p 0) =
      Work.WilE7.bandRel (connectedComponentIn X.set p) ∩
        WilkiesDesign.E.cubeC (n + 1 + m) := by
  let C : Set (Fin (n + m) → ℝ) := connectedComponentIn X.set p
  let π : (Fin (n + 1 + m) → ℝ) → (Fin (n + m) → ℝ) :=
    fun x i => x (Work.WilE8.skipInj n m i)
  show connectedComponentIn (Work.WilE7.bandExt X).set (Work.WilE8.Star.insCoord n m p 0)
      = Work.WilE7.bandRel C ∩ WilkiesDesign.E.cubeC (n + 1 + m)
  have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCsubX : C ⊆ X.set := connectedComponentIn_subset X.set p
  have hCcube : C ⊆ WilkiesDesign.E.cubeC (n + m) :=
    fun y hy => Work.WilE8.SemiPf.set_subset_cube X (hCsubX hy)
  have hπcont : Continuous π := continuous_pi fun i => continuous_apply _
  have hπq : π (Work.WilE8.Star.insCoord n m p 0) = p :=
    funext fun i => Work.WilE8.Star.insCoord_skipInj n m p 0 i
  have hnew : Work.WilE8.Star.insCoord n m p 0 (Work.WilE7.newIdx n m) = 0 :=
    Work.WilE8.Star.insCoord_new n m p 0
  -- The base point lies in the band over `C`.
  have hqmem : Work.WilE8.Star.insCoord n m p 0 ∈ Work.WilE7.bandRel C ∩
      WilkiesDesign.E.cubeC (n + 1 + m) := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · change π (Work.WilE8.Star.insCoord n m p 0) ∈ C
      rw [hπq]
      exact mem_connectedComponentIn hp
    · rw [hnew]; norm_num
    · rw [hnew]; norm_num
    · exact Work.WilE8.Star.insCoord_cube n m (Work.WilE8.SemiPf.set_subset_cube X hp)
        (by norm_num)
  -- The band over `C`, cut by the cube, sits inside `(bandExt X).set`.
  have hbandsub : Work.WilE7.bandRel C ∩ WilkiesDesign.E.cubeC (n + 1 + m) ⊆
      (Work.WilE7.bandExt X).set := by
    rw [Work.WilE7.bandExt_set]
    rintro x ⟨hxb, hxc⟩
    exact ⟨⟨hCsubX hxb.1, hxb.2.1, hxb.2.2⟩, hxc⟩
  -- It is preconnected: the continuous image of `C ×ˢ (-1,1)` under `insCoord`.
  have hpre : IsPreconnected (Work.WilE7.bandRel C ∩ WilkiesDesign.E.cubeC (n + 1 + m)) := by
    have himg : Work.WilE7.bandRel C ∩ WilkiesDesign.E.cubeC (n + 1 + m)
        = (fun r : (Fin (n + m) → ℝ) × ℝ =>
              Work.WilE8.Star.insCoord n m r.1 r.2) '' (C ×ˢ Set.Ioo (-1 : ℝ) 1) := by
      ext x
      constructor
      · rintro ⟨hxb, hxc⟩
        exact ⟨(π x, x (Work.WilE7.newIdx n m)), ⟨hxb.1, hxb.2⟩,
          Work.WilE8.Star.insCoord_self n m x⟩
      · rintro ⟨⟨w, t⟩, ⟨hw, ht⟩, rfl⟩
        have htnew : Work.WilE8.Star.insCoord n m w t (Work.WilE7.newIdx n m) = t :=
          Work.WilE8.Star.insCoord_new n m w t
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · change (fun i => Work.WilE8.Star.insCoord n m w t (Work.WilE8.skipInj n m i)) ∈ C
          rw [funext fun i => Work.WilE8.Star.insCoord_skipInj n m w t i]
          exact hw
        · change -1 < Work.WilE8.Star.insCoord n m w t (Work.WilE7.newIdx n m)
          rw [htnew]; exact (Set.mem_Ioo.mp ht).1
        · change Work.WilE8.Star.insCoord n m w t (Work.WilE7.newIdx n m) < 1
          rw [htnew]; exact (Set.mem_Ioo.mp ht).2
        · exact Work.WilE8.Star.insCoord_cube n m (hCcube hw)
            (abs_le.mpr ⟨le_of_lt (Set.mem_Ioo.mp ht).1, le_of_lt (Set.mem_Ioo.mp ht).2⟩)
    rw [himg]
    exact (hCpre.prod isPreconnected_Ioo).image _
      (Work.WilE8.Star.continuous_insCoord n m).continuousOn
  have hqExt : Work.WilE8.Star.insCoord n m p 0 ∈ (Work.WilE7.bandExt X).set := hbandsub hqmem
  refine Set.Subset.antisymm ?_ ?_
  · -- The component is contained in the band over `C`.
    intro x hx
    have hxExt : x ∈ (Work.WilE7.bandExt X).set := connectedComponentIn_subset _ _ hx
    obtain ⟨hπX, h1, h2, hcub⟩ :=
      (Work.WilE7.bandExt_mem (n := n) (m := m) (X := X)).mp hxExt
    have hpc : IsPreconnected (π '' connectedComponentIn (Work.WilE7.bandExt X).set
        (Work.WilE8.Star.insCoord n m p 0)) :=
      isPreconnected_connectedComponentIn.image _ hπcont.continuousOn
    have hmem : p ∈ π '' connectedComponentIn (Work.WilE7.bandExt X).set
        (Work.WilE8.Star.insCoord n m p 0) :=
      ⟨_, mem_connectedComponentIn hqExt, hπq⟩
    have hsub2 : π '' connectedComponentIn (Work.WilE7.bandExt X).set
        (Work.WilE8.Star.insCoord n m p 0) ⊆ X.set := by
      rintro y ⟨z, hz, rfl⟩
      exact ((Work.WilE7.bandExt_mem (n := n) (m := m) (X := X)).mp
        (connectedComponentIn_subset _ _ hz)).1
    have hcc := hpc.subset_connectedComponentIn hmem hsub2
    exact ⟨⟨hcc ⟨x, hx, rfl⟩, h1, h2⟩, hcub⟩
  · -- The band over `C` is preconnected and contained in `(bandExt X).set`.
    exact hpre.subset_connectedComponentIn hqmem hbandsub

end Work.WilE7.BandOpen
