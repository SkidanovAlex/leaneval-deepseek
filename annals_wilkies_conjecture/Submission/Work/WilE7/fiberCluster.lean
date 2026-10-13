/-
  Area E7, BV Lemma 8 ("effective fibre cutting"): the *cluster* form of `sheetAssembly`'s
  geometric input, i.e. upper semi-continuity of the fibre map over a base set `C` on which no
  forbidden (frontier) point of the stratum projects.

  Statement.  Let `S` be a stratum of `ℝ^{p+q}`, `C ⊆ ℝ^p`, and `Forbidden` a set of points of
  `ℝ^{p+q}` whose projections avoid `C` and which contains the frontier `closure S.X.set \ S.X.set`
  of the stratum.  Then for `v ∈ S.X.set` with `projFirst p q v ∈ C` and every `ε > 0` there is a
  neighbourhood `U` of `projFirst p q v` such that *every* point `(x,y) ∈ S.X.set` with `x ∈ U ∩ C`
  is `ε`-close to the fibre `{y₀ | (projFirst p q v, y₀) ∈ S.X.set}` of the stratum over the fixed
  base point `projFirst p q v`.

  Mathematics (a one-line compactness argument, no o-minimality).  Call a point `z ∈ S.X.set` bad
  if its projection lies in `C` and it keeps distance `≥ ε` from the fibre over `x₀ = projFirst p q v`,
  and let `Bad` be the set of bad points.  Every EA set lies in the compact cube `[-1,1]^{p+q}`, so
  `closure Bad` is compact and `projFirst p q '' closure Bad` is closed in `ℝ^p`; since
  `π '' Bad ⊆ π '' closure Bad`, the hypothesis `x₀ ∈ closure (π '' Bad)` would produce a point
  `z* ∈ closure Bad` with `π z* = x₀`.
  * The distance condition "`ε ≤ dist z (x₀, y₀)` for all `y₀` in the fibre over `x₀`" is closed
    (it is an intersection of preimages of `[ε,∞)` under the continuous maps `z ↦ dist z (x₀,y₀)`),
    so it holds at `z*` as well.
  * If `z* ∉ S.X.set` then `z*` lies in the frontier of `S.X.set`, hence in `Forbidden`, so
    `π z* = x₀ ∉ C`, contradicting `projFirst p q v ∈ C`.
  * Hence `z* ∈ S.X.set`, so `y* = projSnd p q z*` is a point of the fibre over `x₀` (because
    `Fin.append (projFirst p q z*) (projSnd p q z*) = z*`), and the closed distance condition
    gives `ε ≤ dist z* z* = 0`, contradicting `0 < ε`.

  The last two steps are exactly the two facts recorded as `clusterBad_not_mem_closure`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec

set_option autoImplicit false
-- `hv` in the statement of `fiberCluster` is not needed (only `hvC` is): the fibre over
-- `projFirst p q v` is nonempty because it contains `projSnd p q v`.
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Work.WilE7

open WilkiesDesign.E

/-! ## Elementary facts about the cube and the projections -/

/-- The closed cube `[-1,1]^k` is compact. -/
theorem fc_cubeC_isCompact (k : ℕ) : IsCompact (cubeC k) := by
  have h : cubeC k = Set.univ.pi (fun _ : Fin k => Set.Icc (-1 : ℝ) 1) := by
    ext x
    simp only [Set.mem_pi, Set.mem_univ, true_implies, cubeC, Set.mem_Icc]
    exact ⟨fun h i => ⟨neg_le_of_abs_le (h i), le_of_abs_le (h i)⟩,
      fun h i => abs_le.mpr ⟨(h i).1, (h i).2⟩⟩
  rw [h]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

/-- A semi-Pfaffian set lives in the cube. -/
theorem fc_subset_cubeC {k : ℕ} (X : SemiPf k) : X.set ⊆ cubeC k := fun _ hx => hx.1

/-- `projFirst` is continuous. -/
theorem fc_continuous_projFirst (p q : ℕ) : Continuous (projFirst p q) :=
  continuous_pi (fun _ => continuous_apply _)

/-- `z` is the gluing of its projections. -/
theorem fc_append_projFirst_projSnd {p q : ℕ} (z : Fin (p + q) → ℝ) :
    Fin.append (projFirst p q z) (projSnd p q z) = z := by
  funext i
  refine Fin.addCases (motive := fun i => Fin.append (projFirst p q z) (projSnd p q z) i = z i)
    (fun i => ?_) (fun j => ?_) i
  · simp [projFirst]
  · simp [projSnd]

/-- The first `p` coordinates of `Fin.append x y` are `x`. -/
theorem fc_projFirst_append {p q : ℕ} (x : Fin p → ℝ) (y : Fin q → ℝ) :
    projFirst p q (Fin.append x y) = x := by
  funext i
  simp [projFirst]

/-! ## The bad points -/

/-- The *bad* points of the cluster argument: points of the stratum which project into `C` but
stay at distance `≥ ε` from the whole fibre of the stratum over the fixed base point `x₀`. -/
def clusterBad {p q : ℕ} (S : Stratum p q) (C : Set (Fin p → ℝ)) (ε : ℝ) (x₀ : Fin p → ℝ) :
    Set (Fin (p + q) → ℝ) :=
  {z | z ∈ S.X.set ∧ projFirst p q z ∈ C ∧
    ∀ y₀ ∈ fiber S.X.set x₀, ε ≤ dist z (Fin.append x₀ y₀)}

/-- **The cluster lemma.**  Under the frontier hypotheses on `C`, no base point of `C` is a
cluster point of the projections of the bad points: `x₀` is not in the closure of the projection
of `clusterBad S C ε x₀`.  This is the whole compactness content of `fiberCluster`. -/
theorem clusterBad_not_mem_closure {p q : ℕ} (S : Stratum p q) (C : Set (Fin p → ℝ))
    (Forbidden : Set (Fin (p + q) → ℝ))
    (hForb : ∀ w ∈ Forbidden, projFirst p q w ∉ C)
    (hFr : closure S.X.set \ S.X.set ⊆ Forbidden)
    (x₀ : Fin p → ℝ) (hx₀ : x₀ ∈ C) (ε : ℝ) (hε : 0 < ε) :
    x₀ ∉ closure (projFirst p q '' clusterBad S C ε x₀) := by
  intro hmem
  -- the "distance too large from every point of the fibre over `x₀`" condition is closed
  have hTclosed : IsClosed {z : Fin (p + q) → ℝ |
      ∀ y₀ ∈ fiber S.X.set x₀, ε ≤ dist z (Fin.append x₀ y₀)} := by
    have hEq : {z : Fin (p + q) → ℝ | ∀ y₀ ∈ fiber S.X.set x₀, ε ≤ dist z (Fin.append x₀ y₀)}
        = ⋂ y₀ ∈ fiber S.X.set x₀, {z : Fin (p + q) → ℝ | ε ≤ dist z (Fin.append x₀ y₀)} := by
      ext z
      constructor
      · intro h; exact Set.mem_biInter h
      · intro h y₀ hy₀
        exact Set.mem_iInter.mp (Set.mem_iInter.mp h y₀) hy₀
    rw [hEq]
    exact isClosed_biInter (fun y₀ _ => isClosed_Ici.preimage (continuous_id.dist continuous_const))
  -- the bad set is bad, lives in the compact cube, and its closure projects to a closed set
  have hBadT : clusterBad S C ε x₀ ⊆
      {z : Fin (p + q) → ℝ | ∀ y₀ ∈ fiber S.X.set x₀, ε ≤ dist z (Fin.append x₀ y₀)} :=
    fun z hz => hz.2.2
  have hBadCube : clusterBad S C ε x₀ ⊆ cubeC (p + q) := fun z hz => fc_subset_cubeC S.X hz.1
  have hclCube : closure (clusterBad S C ε x₀) ⊆ cubeC (p + q) :=
    closure_minimal hBadCube (fc_cubeC_isCompact (p + q)).isClosed
  have hcompact : IsCompact (closure (clusterBad S C ε x₀)) :=
    (fc_cubeC_isCompact (p + q)).of_isClosed_subset isClosed_closure hclCube
  have himgcl : IsClosed (projFirst p q '' closure (clusterBad S C ε x₀)) :=
    (hcompact.image (fc_continuous_projFirst p q)).isClosed
  have hsub : projFirst p q '' clusterBad S C ε x₀
      ⊆ projFirst p q '' closure (clusterBad S C ε x₀) :=
    Set.image_mono subset_closure
  -- `x₀` is then the projection of a point of the closure of the bad set
  obtain ⟨zstar, hzstar_cl, hzstar_pi⟩ := closure_minimal hsub himgcl hmem
  have hzstar_T : zstar ∈ {z : Fin (p + q) → ℝ |
      ∀ y₀ ∈ fiber S.X.set x₀, ε ≤ dist z (Fin.append x₀ y₀)} :=
    hTclosed.closure_subset (closure_mono hBadT hzstar_cl)
  have hzstar_clX : zstar ∈ closure S.X.set := closure_mono (fun z hz => hz.1) hzstar_cl
  by_cases hzS : zstar ∈ S.X.set
  · -- `z*` is a stratum point, and `projSnd p q z*` is in the fibre over `x₀`
    have hy₀ : projSnd p q zstar ∈ fiber S.X.set x₀ := by
      show Fin.append x₀ (projSnd p q zstar) ∈ S.X.set
      rw [← hzstar_pi, fc_append_projFirst_projSnd zstar]
      exact hzS
    have h1 := hzstar_T (projSnd p q zstar) hy₀
    rw [← hzstar_pi, fc_append_projFirst_projSnd zstar, dist_self] at h1
    linarith
  · -- otherwise `z*` is a frontier point, so it is forbidden and projects outside `C`
    refine hForb zstar (hFr ⟨hzstar_clX, hzS⟩) ?_
    rw [hzstar_pi]
    exact hx₀

/-! ## The cluster statement -/

theorem fiberCluster {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (C : Set (Fin p → ℝ))
    (Forbidden : Set (Fin (p + q) → ℝ))
    (hForb : ∀ w ∈ Forbidden, WilkiesDesign.E.projFirst p q w ∉ C)
    (hFr : closure S.X.set \ S.X.set ⊆ Forbidden)
    (v : Fin (p + q) → ℝ) (hv : v ∈ S.X.set) (hvC : WilkiesDesign.E.projFirst p q v ∈ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set (Fin p → ℝ), IsOpen U ∧ WilkiesDesign.E.projFirst p q v ∈ U ∧
      ∀ x ∈ U ∩ C, ∀ y : Fin q → ℝ, Fin.append x y ∈ S.X.set →
        ∃ y₀ : Fin q → ℝ, Fin.append (WilkiesDesign.E.projFirst p q v) y₀ ∈ S.X.set ∧
          dist (Fin.append x y) (Fin.append (WilkiesDesign.E.projFirst p q v) y₀) < ε := by
  classical
  -- `x₀ = projFirst p q v` is contained in the complement of the closure of the projections of
  -- the bad points; that complement is the required neighbourhood `U`.
  have hkey := clusterBad_not_mem_closure S C Forbidden hForb hFr
    (WilkiesDesign.E.projFirst p q v) hvC ε hε
  refine ⟨(closure (WilkiesDesign.E.projFirst p q ''
      clusterBad S C ε (WilkiesDesign.E.projFirst p q v)))ᶜ,
    isClosed_closure.isOpen_compl, hkey, ?_⟩
  rintro x ⟨hxU, hxC⟩ y hy
  by_contra hcon
  -- `Fin.append x y` is a bad point: it would project to `x`, contradicting `x ∈ U`.
  have hxb : x ∈ WilkiesDesign.E.projFirst p q ''
      clusterBad S C ε (WilkiesDesign.E.projFirst p q v) := by
    refine ⟨Fin.append x y, ⟨hy, ?_, ?_⟩, fc_projFirst_append x y⟩
    · rw [fc_projFirst_append]; exact hxC
    · intro y₀ hy₀
      by_contra hge
      exact hcon ⟨y₀, hy₀, lt_of_not_ge hge⟩
  exact hxU (subset_closure hxb)

end Work.WilE7
