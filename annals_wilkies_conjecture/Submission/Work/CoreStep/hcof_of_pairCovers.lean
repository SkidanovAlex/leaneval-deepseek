/-
  Area E7 / `CoreLT_succ`, case B: the compactness step that upgrades branch-cofinality
  (`hcof`) from *off-diagonal pairs* over a base set `C` to *every* piece point over `C`.

  This is the node `CoreStep.hcof_of_pairCovers` of `NOTES_S35_pairGerm_counterexample.md` §1:
  the pair-stratum `Σ` machinery (`pairStratum_dimDrop`) only ever produces the covering
  statement for a pair `u, v` of *distinct* points of `T.X.set` over the same base point.  The
  remaining case -- `u` alone over its base point `x₀ ∈ C` -- is settled here by a compactness
  argument, using `hclosed` to turn the limit of a genuinely different branch into a point of
  the piece again.

  Argument (fix `u ∈ T.X.set` with `π u ∈ C` and `V ∈ 𝓝 u`): suppose no neighbourhood `U ∋ π u`
  has `C ∩ U ⊆ π '' (absSet T ∩ V)`, and let `Bad = {z ∈ absSet T : π z ∈ C, z ∉ V}`.  Choosing
  for every neighbourhood `U` of `π u` a point `x ∈ C ∩ U` with `x ∉ π '' (absSet T ∩ V)` and
  lifting it with `hCsub` produces points of `Bad` whose projections approach `π u`; hence
  `π u ∈ closure (π '' Bad)`.  Since `absSet T ⊆ cubeC` is bounded, `closure Bad` is compact and
  `π '' closure Bad` is closed, so `π u = π z*` for some `z* ∈ closure Bad ⊆ closure (absSet T)`.
  As `Bad ⊆ Vᶜ` we get `z* ≠ u`; and `π z* = π u ∈ C`, so `hclosed` puts `z* ∈ absSet T`, i.e.
  `z* = absPt u*` for a second point `u* ∈ T.X.set` over `π u`.  The hypothesis `hpair` applies
  to the pair `(u, u*)` and *directly* yields the required `U`, contradicting the assumption.

  Note that `hT`, `hrank` and `hfin` are carried for uniformity with the calling context of the
  case-B assembly; the argument below uses only `hCsub`, `hclosed` and `hpair`.
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.GermDefs

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical Filter Topology

namespace Work.CoreStep

/-- Every piece lies in the cube, so `absSet` is bounded: `absSet T ⊆ cubeC N`. -/
theorem absSet_subset_cubeC {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N) :
    Work.WilE7.MainDesign.absSet S ⊆ WilkiesDesign.E.cubeC N := by
  rintro z ⟨w, hw, hweq⟩
  rw [← hweq]
  intro i
  exact hw.1 (Fin.cast (Nat.zero_add N).symm i)

/-- The closed cube `[-1,1]^k` is compact. -/
theorem cubeC_isCompact' (k : ℕ) : IsCompact (WilkiesDesign.E.cubeC k) := by
  have h : WilkiesDesign.E.cubeC k = Set.univ.pi (fun _ : Fin k => Set.Icc (-1 : ℝ) 1) := by
    ext x
    simp only [Set.mem_pi, Set.mem_univ, true_implies, WilkiesDesign.E.cubeC, Set.mem_Icc]
    exact ⟨fun h i => ⟨neg_le_of_abs_le (h i), le_of_abs_le (h i)⟩,
      fun h i => abs_le.mpr ⟨(h i).1, (h i).2⟩⟩
  rw [h]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

/-- `projFirst` is continuous. -/
theorem continuous_projFirst' (n m : ℕ) : Continuous (WilkiesDesign.E.projFirst n m) :=
  continuous_pi (fun _ => continuous_apply _)

theorem hcof_of_pairCovers {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : T.Good)
    (hrank : ∀ z ∈ T.X.set, Work.WilE7.MainDesign.projRank T z = n + (m + 1) - T.j)
    (hfin : ∀ x : Fin n → ℝ,
      (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet T) x).Finite)
    (C : Set (Fin n → ℝ))
    (hCsub : C ⊆ WilkiesDesign.E.projFirst n (m + 1) '' Work.WilE7.MainDesign.absSet T)
    (hclosed : ∀ z ∈ closure (Work.WilE7.MainDesign.absSet T),
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C → z ∈ Work.WilE7.MainDesign.absSet T)
    (hpair : ∀ u v : Fin (Work.WilE7.CoreStep.pDim n m) → ℝ,
      u ∈ T.X.set → v ∈ T.X.set → Work.WilE7.CoreStep.absPtInv u ≠ Work.WilE7.CoreStep.absPtInv v →
      WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u) =
        WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv v) →
      WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u) ∈ C →
      ∀ V ∈ nhds (Work.WilE7.CoreStep.absPtInv u),
        ∃ U ∈ nhds (WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u)),
          C ∩ U ⊆ WilkiesDesign.E.projFirst n (m + 1) '' (Work.WilE7.MainDesign.absSet T ∩ V)) :
    ∀ u ∈ T.X.set,
      WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u) ∈ C →
      ∀ V ∈ nhds (Work.WilE7.CoreStep.absPtInv u),
        ∃ U ∈ nhds (WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u)),
          C ∩ U ⊆ WilkiesDesign.E.projFirst n (m + 1) '' (Work.WilE7.MainDesign.absSet T ∩ V) := by
  intro u hu hpC V hV
  -- the common base point and the "bad" points: piece points over `C` that stay out of `V`
  let p : Fin n → ℝ := WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u)
  let Bad : Set (Fin (n + (m + 1)) → ℝ) :=
    {z | z ∈ Work.WilE7.MainDesign.absSet T ∧
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C ∧ z ∉ V}
  by_contra hcon
  have hBad_sub : Bad ⊆ Work.WilE7.MainDesign.absSet T := fun z hz => hz.1
  -- failure of the conclusion puts `p` in the closure of the projection of `Bad`
  have hpc : p ∈ closure (WilkiesDesign.E.projFirst n (m + 1) '' Bad) := by
    rw [mem_closure_iff_nhds]
    intro U hU
    have hno : ¬ (C ∩ U ⊆ WilkiesDesign.E.projFirst n (m + 1) ''
        (Work.WilE7.MainDesign.absSet T ∩ V)) := fun hsub => hcon ⟨U, hU, hsub⟩
    rw [Set.not_subset] at hno
    obtain ⟨x, hxC_U, hxnot⟩ := hno
    obtain ⟨hxC, hxU⟩ := hxC_U
    -- lift `x` to a point of the piece; it cannot lie in `V`
    obtain ⟨z, hzA, hzπ⟩ := hCsub hxC
    have hzV : z ∉ V := fun hzV => hxnot ⟨z, ⟨hzA, hzV⟩, hzπ⟩
    exact ⟨x, hxU, ⟨z, ⟨hzA, hzπ ▸ hxC, hzV⟩, hzπ⟩⟩
  -- `closure Bad` is compact, since everything lives in the cube
  have habs_cube : Work.WilE7.MainDesign.absSet T ⊆ WilkiesDesign.E.cubeC (n + (m + 1)) :=
    absSet_subset_cubeC T
  have hBadCube : Bad ⊆ WilkiesDesign.E.cubeC (n + (m + 1)) := fun z hz => habs_cube hz.1
  have hclCube : closure Bad ⊆ WilkiesDesign.E.cubeC (n + (m + 1)) :=
    closure_minimal hBadCube (cubeC_isCompact' (n + (m + 1))).isClosed
  have hcompact : IsCompact (closure Bad) :=
    (cubeC_isCompact' (n + (m + 1))).of_isClosed_subset isClosed_closure hclCube
  have hcont : Continuous (WilkiesDesign.E.projFirst n (m + 1)) := continuous_projFirst' n (m + 1)
  -- hence the projection of `closure Bad` is closed and contains `p`
  have hclosed_img : IsClosed (WilkiesDesign.E.projFirst n (m + 1) '' closure Bad) :=
    (hcompact.image hcont).isClosed
  have hsub_img : WilkiesDesign.E.projFirst n (m + 1) '' Bad ⊆
      WilkiesDesign.E.projFirst n (m + 1) '' closure Bad := Set.image_mono subset_closure
  have hp_mem : p ∈ WilkiesDesign.E.projFirst n (m + 1) '' closure Bad :=
    closure_minimal hsub_img hclosed_img hpc
  obtain ⟨zstar, hzstar_cl, hzstar_pi⟩ := hp_mem
  -- `hclosed` upgrades the closure point over `C` to a genuine piece point
  have hzstar_clA : zstar ∈ closure (Work.WilE7.MainDesign.absSet T) :=
    closure_mono hBad_sub hzstar_cl
  have hzstar_A : zstar ∈ Work.WilE7.MainDesign.absSet T :=
    hclosed zstar hzstar_clA (by rw [hzstar_pi]; exact hpC)
  -- and it is a *different* point, because `Bad` avoids the neighbourhood `V` of `u`
  have hzstar_ne : zstar ≠ Work.WilE7.CoreStep.absPtInv u := by
    intro heq
    have hclV : zstar ∈ closure Vᶜ := closure_mono (fun z hz => hz.2.2) hzstar_cl
    rw [closure_compl] at hclV
    exact hclV (heq ▸ (mem_interior_iff_mem_nhds).mpr hV)
  -- read `z*` back as a point `u*` of the piece
  obtain ⟨v, hv, hv_eq⟩ := hzstar_A
  let u' : Fin (Work.WilE7.CoreStep.pDim n m) → ℝ :=
    Work.WilE7.CoreStep.absPtUp (n := n) (m := m) zstar
  have hu'_inv : Work.WilE7.CoreStep.absPtInv u' = zstar :=
    Work.WilE7.CoreStep.absPtInv_absPtUp zstar
  have hu' : u' ∈ T.X.set := by
    have : u' = v := by
      show Work.WilE7.CoreStep.absPtUp zstar = v
      rw [← hv_eq]
      exact Work.WilE7.CoreStep.absPtUp_absPtInv v
    rw [this]; exact hv
  -- the pair hypothesis for `(u, u*)` gives the desired neighbourhood
  obtain ⟨U, hU, hUsub⟩ := hpair u u' hu hu' (by rw [hu'_inv]; exact fun h => hzstar_ne h.symm)
    (by rw [hu'_inv]; exact hzstar_pi.symm) hpC V hV
  exact hcon ⟨U, hU, hUsub⟩

end Work.CoreStep
