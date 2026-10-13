/-
  Subproject WilE9G — basic API for the objects of the E9 geometric input.

  Everything here is about the frozen vocabulary (`SemiPf`, `Stratum`, `EffStratum`,
  `stratProj`) and the closed cube.  Nothing in this file depends on the two frozen
  hypotheses (`E2_components`, `E5_strat`).
-/
import Submission.Work.WilE9G.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G
open WilkiesDesign WilkiesDesign.E Work.WilE9.Sharp

/-! ## 1. The closed cube `[-1,1]^k` -/

theorem cubeC_eq_pi (k : ℕ) : cubeC k = Set.univ.pi (fun _ : Fin k => Set.Icc (-1 : ℝ) 1) := by
  ext x
  simp only [Set.mem_pi, Set.mem_univ, true_implies, cubeC, Set.mem_ofPred_eq, Set.mem_Icc]
  exact ⟨fun h i => ⟨neg_le_of_abs_le (h i), le_of_abs_le (h i)⟩,
    fun h i => abs_le.mpr ⟨(h i).1, (h i).2⟩⟩

theorem isCompact_cubeC (k : ℕ) : IsCompact (cubeC k) := by
  rw [cubeC_eq_pi]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

theorem isClosed_cubeC (k : ℕ) : IsClosed (cubeC k) := (isCompact_cubeC k).isClosed

theorem isBounded_cubeC (k : ℕ) : Bornology.IsBounded (cubeC k) :=
  (isCompact_cubeC k).isBounded

theorem volume_cubeC_lt_top (k : ℕ) : volume (cubeC k) < ⊤ :=
  (isCompact_cubeC k).measure_lt_top

theorem measurableSet_cubeC (k : ℕ) : MeasurableSet (cubeC k) :=
  (isClosed_cubeC k).measurableSet

/-! ## 2. A semi-Pfaffian set lives in the cube -/

theorem SemiPf_set_subset_cubeC {k : ℕ} (X : SemiPf k) : X.set ⊆ cubeC k :=
  fun _ hx => hx.1

/-- Transport of `SemiPf.set` along an equality of semi-Pfaffian sets. -/
theorem SemiPf_set_eq_of_eq {k : ℕ} {X Y : SemiPf k} (h : X = Y) : X.set = Y.set := by rw [h]

/-- Transport of `SemiPf.deg` along an equality of semi-Pfaffian sets. -/
theorem SemiPf_deg_eq_of_eq {k : ℕ} {X Y : SemiPf k} (h : X = Y) : X.deg = Y.deg := by rw [h]

theorem SemiPf_closure_subset_cubeC {k : ℕ} (X : SemiPf k) : closure X.set ⊆ cubeC k :=
  closure_minimal (SemiPf_set_subset_cubeC X) (isClosed_cubeC k)

theorem SemiPf_isCompact_closure {k : ℕ} (X : SemiPf k) : IsCompact (closure X.set) :=
  (isCompact_cubeC k).of_isClosed_subset isClosed_closure (SemiPf_closure_subset_cubeC X)

theorem SemiPf_volume_set_lt_top {k : ℕ} (X : SemiPf k) : volume X.set < ⊤ :=
  lt_of_le_of_lt (measure_mono (SemiPf_set_subset_cubeC X)) (volume_cubeC_lt_top k)

theorem SemiPf_measure_closure_lt_top {k : ℕ} (X : SemiPf k) : volume (closure X.set) < ⊤ :=
  lt_of_le_of_lt (measure_mono (SemiPf_closure_subset_cubeC X)) (volume_cubeC_lt_top k)

theorem connectedComponentIn_nonempty_iff {k : ℕ} {X : Set (Fin k → ℝ)} {z : Fin k → ℝ} :
    (connectedComponentIn X z).Nonempty ↔ z ∈ X := by
  constructor
  · rintro ⟨w, hw⟩
    by_contra hz
    rw [connectedComponentIn_eq_empty hz] at hw
    exact hw
  · exact fun hz => ⟨z, mem_connectedComponentIn hz⟩

/-- A component of a set is *relatively closed* in that set: a point of the set which lies in
the ambient closure of the component already belongs to it.  (This is what lets a component of a
fibre be identified with the appropriate union of pieces of the ambient strata.) -/
theorem mem_of_mem_closure_of_mem_connectedComponentIn {k : ℕ} {X : Set (Fin k → ℝ)}
    {z w : Fin k → ℝ} (hz : z ∈ X)
    (hw : w ∈ closure (connectedComponentIn X z)) (hwX : w ∈ X) :
    w ∈ connectedComponentIn X z := by
  rw [connectedComponentIn_eq_image hz] at hw ⊢
  obtain ⟨T, hT, hTset⟩ := isClosed_induced_iff.mp
    (isClosed_connectedComponent (x := (⟨z, hz⟩ : X)))
  have hsub : Subtype.val '' (connectedComponent (⟨z, hz⟩ : X)) ⊆ T := by
    rintro w ⟨u, hu, rfl⟩
    have hu' : u ∈ connectedComponent (⟨z, hz⟩ : X) := hu
    rw [← hTset] at hu'
    exact hu'
  have hwT : w ∈ T := closure_minimal hsub hT hw
  refine ⟨⟨w, hwX⟩, ?_, rfl⟩
  rw [← hTset]
  exact hwT

/-! ## 3. Ambient strata: `E5_strat` at `p = 0` is the Gabrielov–Vorobjov stratification -/

/-- The frozen `E5_strat` at `p = 0` IS the ambient (Gabrielov–Vorobjov) stratification: the
fibre condition in `Good` is vacuous over `ℝ⁰`.  (Copied from the design file, where it is
proved.) -/
theorem Stratum.good_zero_ambient {q : ℕ} (S : Stratum 0 q) (hS : S.Good) :
    ∀ z ∈ S.X.set, ∀ᶠ z' in 𝓝 z, (∀ a, eaEval S.X.c (S.h a) z' = 0) → z' ∈ S.X.set := by
  intro z hz
  filter_upwards [(hS z hz).2.2] with z' hz'
  exact hz' (funext fun i => i.elim0)

theorem Stratum_subset_cubeC {q : ℕ} (S : Stratum 0 q) : S.X.set ⊆ cubeC (0 + q) :=
  SemiPf_set_subset_cubeC S.X

/-- The rank condition of a `Good` ambient stratum, read off in coordinates: the `j × q`
matrix of the partials of the `j` equations has rank `j` at every point of the stratum. -/
theorem Stratum.good_rank {q : ℕ} (S : Stratum 0 q) (hS : S.Good) {z : Fin (0 + q) → ℝ}
    (hz : z ∈ S.X.set) :
    (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
      eaEval S.X.c (eaD S.X.c (Fin.natAdd 0 l) (S.h a)) z).rank = S.j := (hS z hz).2.1

/-! ## 4. The projection `stratProj` -/

theorem stratProj_apply {n m : ℕ} (w : Fin (n + (1 + m)) → ℝ) (i : Fin (n + 1)) :
    stratProj w i = w (stratInj (Fin.castAdd m i)) := rfl

theorem continuous_stratProj {n m : ℕ} : Continuous (stratProj (n := n) (m := m)) :=
  continuous_pi fun i => continuous_apply _

theorem stratProj_eq_projFirst {n m : ℕ} (w : Fin (n + (1 + m)) → ℝ) :
    stratProj w = projFirst (n + 1) m (fun i => w (stratInj i)) := rfl

theorem stratProj_mem_image {n m : ℕ} {E : EffStratum n m} {w : Fin (n + (1 + m)) → ℝ}
    (hw : w ∈ E.X.set) : stratProj w ∈ stratProj '' E.X.set := ⟨w, hw, rfl⟩

/-! ## 5. Consequences of `EffStratum.Good` -/

theorem EffStratum.Good.eq_zero {n m : ℕ} (E : EffStratum n m) (h : E.Good)
    {z : Fin (n + (1 + m)) → ℝ} (hz : z ∈ E.X.set) : ∀ a, eaEval E.X.c (E.h a) z = 0 :=
  (h z hz).1

theorem EffStratum.Good.det_ne_zero {n m : ℕ} (E : EffStratum n m) (h : E.Good)
    {z : Fin (n + (1 + m)) → ℝ} (hz : z ∈ E.X.set) :
    (Matrix.of fun (a : Fin (1 + m)) (l : Fin (1 + m)) =>
      eaEval E.X.c (eaD E.X.c (Fin.natAdd n l) (E.h a)) z).det ≠ 0 := (h z hz).2.1

theorem EffStratum.Good.locality {n m : ℕ} (E : EffStratum n m) (h : E.Good)
    {z : Fin (n + (1 + m)) → ℝ} (hz : z ∈ E.X.set) :
    ∀ᶠ z' in 𝓝 z, (∀ a, eaEval E.X.c (E.h a) z' = 0) → z' ∈ E.X.set := (h z hz).2.2

theorem EffStratum_subset_cubeC {n m : ℕ} (E : EffStratum n m) :
    E.X.set ⊆ cubeC (n + (1 + m)) := SemiPf_set_subset_cubeC E.X

end Work.WilE9G
