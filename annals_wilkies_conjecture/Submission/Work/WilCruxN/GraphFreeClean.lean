import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.Wilkies.Defs
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG1.Main
import Submission.Work.WilG4c.BadLocusThin
import Submission.Work.WilG4c.JointC1LocMem
import Submission.Work.WilG4c.C1BadLocusMemPB2
import Submission.Work.WilCrux.Defs
import Submission.Work.WilCrux.ShearDiff
import Submission.Work.WilCrux.ShearSliceC1
import Submission.Work.WilCrux.ShearGraphMem
import Submission.Work.WilCruxN.IsolatedSheetClean
import Submission.Work.WilCruxN.FlatSheetClean

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilCruxN

open WilkiesDesign

/-- Splitting a point of `ℝ^{m+N}` into its two blocks. -/
theorem append_split_aux {m N : ℕ} (z : Fin (m + N) → ℝ) :
    Fin.append (fun i : Fin m => z (Fin.castAdd N i)) (fun j : Fin N => z (Fin.natAdd m j)) = z := by
  funext i
  revert i
  refine Fin.addCases (motive := fun i => Fin.append (fun i : Fin m => z (Fin.castAdd N i))
      (fun j : Fin N => z (Fin.natAdd m j)) i = z i) ?_ ?_
  · intro i'; rw [Fin.append_left]
  · intro j'; rw [Fin.append_right]

/-- A sheet point is the gluing of its parameter and fibre blocks. -/
theorem sheetPt_eq_append {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2))
    (v : Fin (m + n1) → ℝ) (u : Fin n2 → ℝ) :
    Work.WilCrux.sheetPt e v u = Fin.append
      (fun i : Fin m => Work.WilCrux.sheetPt e v u (Fin.castAdd N i))
      (fun j : Fin N => Work.WilCrux.sheetPt e v u (Fin.natAdd m j)) :=
  (append_split_aux _).symm

/-- The fibre block of the sheet point, read through `e`, is the reindexed fibre. -/
theorem sheetFib_sheetPt_eq {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2))
    (v : Fin (m + n1) → ℝ) (w : Fin n2 → ℝ) :
    Work.WilCrux.sheetFib (Work.WilCrux.sheetPt e v w)
      = fun j : Fin N => (Fin.append (fun k : Fin n1 => v (Fin.natAdd m k)) w) (e j) :=
  Work.WilCrux.sheetFib_sheetPt e v w

/-- Distance bound for two reindexed fibres of the same parameter. -/
theorem dist_sheetFib_le {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2))
    (v : Fin (m + n1) → ℝ) (w w' : Fin n2 → ℝ) :
    dist (fun j : Fin N => (Fin.append (fun k : Fin n1 => v (Fin.natAdd m k)) w) (e j))
      (fun j : Fin N => (Fin.append (fun k : Fin n1 => v (Fin.natAdd m k)) w') (e j))
      ≤ dist w w' := by
  rw [dist_pi_le_iff dist_nonneg]
  intro j
  refine Fin.addCases (m := n1) (n := n2)
    (motive := fun x => dist ((Fin.append (fun k' : Fin n1 => v (Fin.natAdd m k')) w) x)
      ((Fin.append (fun k' : Fin n1 => v (Fin.natAdd m k')) w') x) ≤ dist w w') ?_ ?_ (e j)
  · intro i
    rw [Fin.append_left, Fin.append_left, dist_self]
    exact dist_nonneg
  · intro i
    rw [Fin.append_right, Fin.append_right]
    simpa only [dist_eq_norm, Pi.sub_apply] using norm_le_pi_norm (w - w') i

/-- **The "no bad sheet over a fat set of parameters" crux, clean re-proof.**

A continuous graph `w ↦ (w, γ w)` over a nonempty open `O ⊆ W` with values in the open `U`, on
which all slices `y ↦ g w y` are `C¹`, cannot consist entirely of joint non-`C¹` points.

The proof is the documented route: `IsolatedSheetClean` (the lexicographically maximal bad cell
isolates a continuous graph sheet over an open base), then the shear `u ↦ y_B - φ v` which flattens
the sheet, then the flat-sheet normal form `FlatSheetClean` (N4b + N4c + N4d + the `C¹` assembly),
on which the contradiction is immediate.

The argument is the port of `Work.WilCrux.BadProjThin`'s proof from the `hder`-taking chain to the
`hder`-free one, with the fatness hypothesis supplied by the sheet `γ` instead of by
`interior Bad ≠ ∅`.  Each of its analysis inputs is replaced as follows:

* the bad locus `Z` is `Ω`-definable by `Work.WilG4c.C1BadLocusMemPB2` (no `SharpDeriv`);
* the isolated sheet is `Work.WilCruxN.IsolatedSheetClean` (no `hder` in its statement);
* the flat-sheet normal form is `Work.WilCruxN.FlatSheetClean` (`hder`-free port of `FlatSheetC1`,
  assembled from the `hder`-free nodes `SliceDerivJointNorm` (N4b), `ParamDerivPointwiseClean`
  (N4c) and `ParamDerivJointClean` (N4d));
* the coordinate `C¹`-loci of `φ` are thin by `WilkiesDesign.CG.G1_generic_smooth_proved`. -/
theorem GraphFreeClean (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (m N F0 D : ℕ)
    (g : (Fin m → ℝ) → (Fin N → ℝ) → ℝ)
    (hg : WilkiesDesign.CG.famGraph g ∈ S.Ω F0 D (m + N + 1))
    (W : Set (Fin m → ℝ)) (hW : IsOpen W)
    (U : Set (Fin N → ℝ)) (hU : IsOpen U)
    (hsm : ∀ w ∈ W, ContDiffOn ℝ 1 (g w) U)
    (O : Set (Fin m → ℝ)) (hO : IsOpen O) (hOne : O.Nonempty) (hOW : O ⊆ W)
    (γ : (Fin m → ℝ) → (Fin N → ℝ)) (hγcont : ContinuousOn γ O) (hγU : ∀ w ∈ O, γ w ∈ U)
    (hgraph : ∀ w ∈ O, ¬ ContDiffAt ℝ 1 (Work.WilG4c.famFun g) (Fin.append w (γ w))) :
    False := by
  classical
  -- ## 0. The joint non-`C¹` locus `Z` is `Ω`-definable (no `SharpDeriv` needed)
  obtain ⟨aZ, bZ, hZmem'⟩ := Work.WilG4c.C1BadLocusMemPB2 (S := S) m N F0
  let Z : Set (Fin (m + N) → ℝ) := {z | ¬ ContDiffAt ℝ 1 (Work.WilG4c.famFun g) z}
  have hZ : Z ∈ S.Ω aZ (bZ.eval D) (m + N) := hZmem' D g hg
  have hfib : ∀ w ∈ O, ∃ y ∈ U, Fin.append w y ∈ Z := fun w hw =>
    ⟨γ w, hγU w hw, by simpa only [Z, Set.mem_setOf_eq] using hgraph w hw⟩
  -- ## 1. N1: an isolated graph sheet over the open `O`
  obtain ⟨n1, n2, e, V, φ, F', b', hVopen, hVne, hφcont, hφmem, hsheet, hiso⟩ :=
    Work.WilCruxN.IsolatedSheetClean S hcd Z hZ W hW U hU O hO hOne hOW hfib
  -- ## 2. Some point of `V` is a `C¹` point of the graph map
  have hcoord_open : ∀ j : Fin n2,
      IsOpen {v : Fin (m + n1) → ℝ | ContDiffAt ℝ 1 (fun v => φ v j) v} :=
    fun j => Work.WilkG4c.isOpen_contDiffAt_set (fun v : Fin (m + n1) → ℝ => φ v j)
  have hpoint : ∃ v₀ ∈ V, ∀ j : Fin n2, ContDiffAt ℝ 1 (fun v => φ v j) v₀ := by
    by_contra hcon
    push_neg at hcon
    have hsub : V ⊆ ⋃ j : Fin n2,
        {v : Fin (m + n1) → ℝ | ¬ ContDiffAt ℝ 1 (fun v => φ v j) v} := by
      intro v hv
      obtain ⟨j, hj⟩ := hcon v hv
      exact Set.mem_iUnion.mpr ⟨j, hj⟩
    have hnw : ∀ j : Fin n2,
        IsNowhereDense {v : Fin (m + n1) → ℝ | ¬ ContDiffAt ℝ 1 (fun v => φ v j) v} := by
      intro j
      -- the coordinate `C¹`-locus is a definable set, so its complement is thin
      have hbad : interior {v : Fin (m + n1) → ℝ | ¬ ContDiffAt ℝ 1 (fun v => φ v j) v} = ∅ :=
        WilkiesDesign.CG.G1_generic_smooth_proved S hcd
          (fun v : Fin (m + n1) → ℝ => φ v j) (hφmem j) 1
      refine (hcoord_open j).isClosed_compl.isNowhereDense_iff.mpr ?_
      simpa only [Set.compl_setOf] using hbad
    have hUnion : IsNowhereDense
        (⋃ j : Fin n2, {v : Fin (m + n1) → ℝ | ¬ ContDiffAt ℝ 1 (fun v => φ v j) v}) :=
      IsNowhereDense.iUnion hnw
    have hUint : interior
        (⋃ j : Fin n2, {v : Fin (m + n1) → ℝ | ¬ ContDiffAt ℝ 1 (fun v => φ v j) v}) = ∅ :=
      Set.eq_empty_of_subset_empty ((interior_mono subset_closure).trans (le_of_eq hUnion))
    have hVint : interior V = ∅ :=
      Set.eq_empty_of_subset_empty ((interior_mono hsub).trans (le_of_eq hUint))
    rw [hVopen.interior_eq] at hVint
    exact hVne.ne_empty hVint
  obtain ⟨v₀, hv₀V, hv₀CD⟩ := hpoint
  have hv₀CDvec : ContDiffAt ℝ 1 φ v₀ := contDiffAt_pi.mpr hv₀CD
  -- ## 3. The neighbourhood on which all the hypotheses of `FlatSheetClean` hold
  obtain ⟨ε₀, hε₀, hiso₀⟩ := hiso v₀ hv₀V
  obtain ⟨δV, hδV, hballV⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds hv₀V)
  have hCDopen : IsOpen {v : Fin (m + n1) → ℝ | ContDiffAt ℝ 1 φ v} := by
    have h : {v : Fin (m + n1) → ℝ | ContDiffAt ℝ 1 φ v}
        = ⋂ j : Fin n2, {v : Fin (m + n1) → ℝ | ContDiffAt ℝ 1 (fun v => φ v j) v} := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact contDiffAt_pi
    rw [h]
    exact isOpen_iInter_of_finite (fun j => hcoord_open j)
  obtain ⟨δC, hδC, hballC⟩ := Metric.mem_nhds_iff.mp (hCDopen.mem_nhds hv₀CDvec)
  obtain ⟨δS, hδS, hballS⟩ := Metric.continuousAt_iff.mp
    (Work.WilCrux.continuousAt_sheetPt_comp e hVopen hφcont hv₀V) (ε₀ / 2) (by linarith)
  have hWnhds : {v : Fin (m + n1) → ℝ | (fun i : Fin m => v (Fin.castAdd n1 i)) ∈ W}
      ∈ nhds v₀ := by
    have hcont : Continuous
        (fun v : Fin (m + n1) → ℝ => (fun i : Fin m => v (Fin.castAdd n1 i))) :=
      continuous_pi fun i => continuous_apply (Fin.castAdd n1 i)
    exact hcont.continuousAt.preimage_mem_nhds (hW.mem_nhds (hsheet v₀ hv₀V).2.1)
  obtain ⟨δW, hδW, hballW⟩ := Metric.mem_nhds_iff.mp hWnhds
  have hUnhds : {p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) |
      Work.WilCrux.sheetFib (Work.WilCrux.sheetPt e p.1 (φ p.1 + p.2)) ∈ U} ∈ nhds (v₀, 0) := by
    have hcont : Continuous (@Work.WilCrux.sheetFib m N) :=
      continuous_pi fun j => continuous_apply (Fin.natAdd m j)
    have hmem : (Work.WilCrux.sheetFib ∘ fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) =>
        Work.WilCrux.sheetPt e p.1 (φ p.1 + p.2)) (v₀, 0) ∈ U := by
      show Work.WilCrux.sheetFib (Work.WilCrux.sheetPt e v₀ (φ v₀ + 0)) ∈ U
      rw [add_zero, Work.WilCrux.sheetFib_sheetPt]
      exact (hsheet v₀ hv₀V).2.2
    exact (hcont.continuousAt.comp (Work.WilCrux.continuousAt_sheetPt_shift e hVopen hφcont hv₀V))
      |>.preimage_mem_nhds (hU.mem_nhds hmem)
  obtain ⟨δU, hδU, hballU⟩ := Metric.mem_nhds_iff.mp hUnhds
  -- the working neighbourhood and radius
  set δ : ℝ := min δV (min δC (min δS (min δW δU))) with hδdef
  have hδpos : 0 < δ := lt_min hδV (lt_min hδC (lt_min hδS (lt_min hδW hδU)))
  have hδVle : δ ≤ δV := min_le_left _ _
  have hδCle : δ ≤ δC := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδSle : δ ≤ δS :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδWle : δ ≤ δW := le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδUle : δ ≤ δU := le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  set Q : Set (Fin (m + n1) → ℝ) := Metric.ball v₀ (δ / 4) with hQdef
  have hQopen : IsOpen Q := Metric.isOpen_ball
  have hQv₀ : v₀ ∈ Q := Metric.mem_ball_self (by linarith)
  have hQne : Q.Nonempty := ⟨v₀, hQv₀⟩
  have hQdist : ∀ v ∈ Q, dist v v₀ < δ := by
    intro v hv
    have h := Metric.mem_ball.mp hv
    linarith [hδpos]
  have hQV : Q ⊆ V := fun v hv =>
    hballV (Metric.mem_ball.mpr (lt_of_lt_of_le (hQdist v hv) hδVle))
  have hQCD : ∀ v ∈ Q, ContDiffAt ℝ 1 φ v := fun v hv =>
    hballC (Metric.mem_ball.mpr (lt_of_lt_of_le (hQdist v hv) hδCle))
  have hQW : ∀ v ∈ Q, (fun i : Fin m => v (Fin.castAdd n1 i)) ∈ W := fun v hv =>
    hballW (Metric.mem_ball.mpr (lt_of_lt_of_le (hQdist v hv) hδWle))
  set r₀ : ℝ := min (ε₀ / 4) (δU / 2) with hr₀def
  have hr₀pos : 0 < r₀ := lt_min (by linarith) (by linarith)
  have hsheetU : ∀ v ∈ Q, ∀ u : Fin n2 → ℝ, ‖u‖ ≤ r₀ →
      Work.WilCrux.sheetFib (Work.WilCrux.sheetPt e v (φ v + u)) ∈ U := by
    intro v hv u hu
    have hb : ((v, u) : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ)) ∈ Metric.ball (v₀, 0) δU := by
      rw [Metric.mem_ball, Prod.dist_eq]
      refine max_lt ?_ ?_
      · refine lt_of_lt_of_le (hQdist v hv) ?_
        linarith [hδUle, hδpos]
      · have hdu : dist u 0 = ‖u‖ := by rw [dist_eq_norm, sub_zero]
        rw [hdu]
        refine lt_of_le_of_lt (le_trans hu (min_le_right _ _)) ?_
        linarith [hδU]
    exact hballU hb
  have hsheetFar : ∀ v ∈ Q, ∀ u : Fin n2 → ℝ, ‖u‖ ≤ r₀ →
      dist (Work.WilCrux.sheetPt e v (φ v + u)) (Work.WilCrux.sheetPt e v₀ (φ v₀)) < ε₀ := by
    intro v hv u hu
    have h1 : dist (Work.WilCrux.sheetPt e v (φ v + u)) (Work.WilCrux.sheetPt e v (φ v)) ≤ ‖u‖ := by
      have h := Work.WilCrux.dist_sheetPt_le e v (φ v + u) (φ v)
      have h2 : dist (φ v + u) (φ v) = ‖u‖ := by
        rw [dist_eq_norm]
        congr 1
        abel
      rwa [h2] at h
    have h2 : dist (Work.WilCrux.sheetPt e v (φ v)) (Work.WilCrux.sheetPt e v₀ (φ v₀)) < ε₀ / 2 :=
      hballS (lt_of_lt_of_le (hQdist v hv) hδSle)
    have h3 : ‖u‖ ≤ ε₀ / 4 := le_trans hu (min_le_left _ _)
    calc dist (Work.WilCrux.sheetPt e v (φ v + u)) (Work.WilCrux.sheetPt e v₀ (φ v₀))
        ≤ dist (Work.WilCrux.sheetPt e v (φ v + u)) (Work.WilCrux.sheetPt e v (φ v))
          + dist (Work.WilCrux.sheetPt e v (φ v)) (Work.WilCrux.sheetPt e v₀ (φ v₀)) :=
        dist_triangle _ _ _
      _ < ε₀ := by linarith
  -- ## 4. The sheared family and the flat-sheet normal form
  obtain ⟨F'', D'', hG⟩ := Work.WilCrux.ShearGraphMem S g hg e φ hφmem
  have hsl : ∀ v ∈ Q, ContDiffOn ℝ 1 (Work.WilCrux.shearFam g e φ v) (Metric.ball 0 r₀) := by
    intro v hv
    refine (Work.WilCrux.ShearSliceC1 g e φ W U hU hsm v (hQW v hv)).mono ?_
    intro u hu
    have hu' : ‖u‖ < r₀ := by
      have h := Metric.mem_ball.mp hu
      rwa [dist_eq_norm, sub_zero] at h
    have := hsheetU v hv u hu'.le
    rwa [Work.WilCrux.sheetFib_sheetPt] at this
  have hoff : ∀ v ∈ Q, ∀ u : Fin n2 → ℝ, u ≠ 0 → ‖u‖ < r₀ →
      ContDiffAt ℝ 1 (Work.WilG4c.famFun (Work.WilCrux.shearFam g e φ)) (Fin.append v u) := by
    intro v hv u hu huR
    rw [Work.WilCrux.ShearDiff g e φ v u (hQCD v hv)]
    by_contra hcon
    have hmemZ : Work.WilCrux.sheetPt e v (φ v + u) ∈ Z := by
      simpa only [Z, Set.mem_setOf_eq] using hcon
    obtain ⟨v', -, hv'eq⟩ := hiso₀ (Work.WilCrux.sheetPt e v (φ v + u)) hmemZ
      (hsheetFar v hv u (le_of_lt huR))
    have hp : (v, φ v + u) = (v', φ v') :=
      Work.WilCrux.sheetPt_injective e hv'eq
    have hzv : φ v + u = φ v := by
      have h2 : φ v + u = φ v' :=
        congrArg (fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) => p.2) hp
      have h1 : v = v' :=
        congrArg (fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) => p.1) hp
      rw [h2, ← h1]
    have hu0 : u = 0 := by
      have h1 : u = (φ v + u) - φ v := by abel
      rw [hzv] at h1
      simpa using h1
    exact hu hu0
  obtain ⟨v, hvQ, hvC1⟩ :=
    Work.WilCruxN.FlatSheetClean S hcd (Work.WilCrux.shearFam g e φ) hG Q hQopen hQne r₀ hr₀pos
      hsl hoff
  -- ## 5. The sheet point is bad, contradiction
  have hbad : ¬ ContDiffAt ℝ 1 (Work.WilG4c.famFun g) (Work.WilCrux.sheetPt e v (φ v)) := by
    have h := (hsheet v (hQV hvQ)).1
    simpa only [Z, Set.mem_setOf_eq] using h
  have hc1' : ContDiffAt ℝ 1 (Work.WilG4c.famFun g) (Work.WilCrux.sheetPt e v (φ v + 0)) :=
    (Work.WilCrux.ShearDiff g e φ v 0 (hQCD v hvQ)).mp hvC1
  rw [add_zero] at hc1'
  exact hbad hc1'

end Work.WilCruxN
