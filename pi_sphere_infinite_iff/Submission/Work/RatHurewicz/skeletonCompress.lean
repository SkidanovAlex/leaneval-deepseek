import Mathlib
import Submission.Work.RatHurewicz.cycleModelDefs
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.cellDefs
import Submission.Work.StemsB.PiMap
import Submission.Work.Serre.CWModel.piOneSurjective
import Submission.Work.RatHurewicz.skeletonPiOne_surjective

/-!
# Pushing paths in the model `Model D` into its `1`-skeleton: the assembly

Assembles `CompressRel (Model D) (skeleton D) 1` from the two geometric inputs
`Work.RatHurewicz.cellPushRadial` and `Work.RatHurewicz.avoidCellOrigin`, together with the
invariance of `rawWeight` (the number of nonzero barycentric coordinates, or `1` on an arc) along
the gluing relation of the model.  Route: descending from `skel D (n+1) = univ` to
`skel D 1 = skeleton D`, one dimension at a time, avoiding the origins of the `k`-cells and then
pushing them off; see `COMPRESS_NOTES.md`.
-/

open scoped Topology Simplicial unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-! ## The support of a point of a standard simplex, in a dimension-agnostic form -/

/-- The support of a point of a standard simplex: the coordinates that are nonzero.  Unlike
`ptSupport` this is stated for every simplex dimension, which is what the face formula needs. -/
def ptSup {m : ℕ} (x : stdSimplex ℝ (Fin m)) : Finset (Fin m) :=
  Finset.univ.filter (fun k => x.1 k ≠ 0)

@[simp] theorem mem_ptSup {m : ℕ} {x : stdSimplex ℝ (Fin m)} {k : Fin m} :
    k ∈ ptSup x ↔ x.1 k ≠ 0 := by
  unfold ptSup
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ k, h⟩⟩

theorem ptSup_eq_ptSupport (x : stdSimplex ℝ (Fin (n + 2))) : ptSup x = ptSupport x := rfl

theorem rawWeight_inl_ptSup (D : MData X n x₀) (i : D.Idx) (x : stdSimplex ℝ (Fin (n + 2))) :
    rawWeight D (Sum.inl ⟨i, x⟩) = (ptSup x).card := rfl

theorem ptSupport_vertex (k : Fin (n + 2)) :
    ptSupport (stdSimplex.vertex k) = {k} := by
  ext j
  simp only [mem_ptSupport, Finset.mem_singleton, stdSimplex.vertex_coe]
  by_cases h : j = k
  · subst h
    rw [Pi.single_eq_same]
    simp
  · rw [Pi.single_eq_of_ne h]
    simp [h]

theorem ptSup_facept_apply {m : ℕ} (p : Fin (m + 1)) (y : stdSimplex ℝ (Fin m))
    (k : Fin (m + 1)) :
    (facept m p y).1 k
      = ∑ j ∈ Finset.univ.filter (fun j : Fin m => p.succAbove j = k), y.1 j := by
  show (stdSimplex.map p.succAbove y : Fin (m + 1) → ℝ) k = _
  rw [stdSimplex.map_coe]
  exact FunOnFinite.linearMap_apply_apply (R := ℝ) (M := ℝ) p.succAbove y.1 k

theorem ptSup_facept {m : ℕ} (p : Fin (m + 1)) (y : stdSimplex ℝ (Fin m)) :
    ptSup (facept m p y) = (ptSup y).image p.succAbove := by
  ext k
  simp only [mem_ptSup, Finset.mem_image]
  constructor
  · intro hk
    rw [ptSup_facept_apply] at hk
    obtain ⟨j, hj, hjne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
    exact ⟨j, hjne, (Finset.mem_filter.mp hj).2⟩
  · rintro ⟨j, hj, rfl⟩
    rw [ptSup_facept_apply]
    have hfilter : Finset.univ.filter
        (fun j' : Fin m => p.succAbove j' = p.succAbove j) = {j} := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hb => Fin.succAbove_right_injective hb, fun hb => by rw [hb]⟩
    rw [hfilter, Finset.sum_singleton]
    exact hj

theorem card_ptSup_facept_eq {m : ℕ} (p q : Fin (m + 1)) (y : stdSimplex ℝ (Fin m)) :
    (ptSup (facept m p y)).card = (ptSup (facept m q y)).card := by
  rw [ptSup_facept, ptSup_facept,
    Finset.card_image_of_injective _ (Fin.succAbove_right_injective),
    Finset.card_image_of_injective _ (Fin.succAbove_right_injective)]

theorem card_ptSupport_facept_eq (p q : Fin (n + 2)) (x : stdSimplex ℝ (Fin (n + 1))) :
    (ptSupport (facept (n + 1) p x)).card = (ptSupport (facept (n + 1) q x)).card :=
  card_ptSup_facept_eq p q x

/-! ## Invariance of the weight along the gluing relation -/

theorem rawWeight_rel (D : MData X n x₀) {a b : Raw D} (h : modelRel D a b) :
    rawWeight D a = rawWeight D b := by
  rcases h with ⟨i, j, p, q, x, rfl, rfl, _⟩ | ⟨i, ha, hb⟩ | ⟨i, j, ha, hb⟩
  · rw [rawWeight_inl, rawWeight_inl, card_ptSupport_facept_eq]
  · subst ha; subst hb
    rw [rawWeight_inl, rawWeight_inr, ptSupport_vertex]
    simp
  · subst ha; subst hb
    rw [rawWeight_inr, rawWeight_inr]

theorem rawWeight_eqvGen (D : MData X n x₀) {a b : Raw D}
    (h : Relation.EqvGen (modelRel D) a b) : rawWeight D a = rawWeight D b := by
  induction h with
  | rel x y hxy => exact rawWeight_rel D hxy
  | refl x => rfl
  | symm x y hxy ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

/-! ## Cells and skeleta -/

theorem openCell_subset_skel (D : MData X n x₀) (i : D.Idx) (S : Finset (Fin (n + 2))) :
    openCell D i S ⊆ skel D (S.card - 1) := by
  rintro z ⟨x, hx, rfl⟩
  refine ⟨Sum.inl ⟨i, x⟩, rfl, ?_⟩
  have hcard : S.card = (ptSup x).card := by
    rw [ptSup_eq_ptSupport]
    exact congrArg Finset.card hx.symm
  show (Finset.univ.filter (fun j : Fin (n + 2) => (x : Fin (n + 2) → ℝ) j ≠ 0)).card
      ≤ S.card - 1 + 1
  rw [show (Finset.univ.filter (fun j : Fin (n + 2) => (x : Fin (n + 2) → ℝ) j ≠ 0)).card
      = (ptSup x).card from rfl]
  omega

theorem skel_succ_univ (D : MData X n x₀) : skel D (n + 1) = Set.univ := by
  ext z
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  obtain ⟨a, rfl⟩ := Quotient.exists_rep z
  rcases a with ⟨i, x⟩ | ⟨i, t⟩
  · refine ⟨Sum.inl ⟨i, x⟩, rfl, ?_⟩
    show (Finset.univ.filter (fun j : Fin (n + 2) => (x : Fin (n + 2) → ℝ) j ≠ 0)).card
        ≤ n + 1 + 1
    have h := Finset.card_filter_le (Finset.univ : Finset (Fin (n + 2)))
      (fun j => (x : Fin (n + 2) → ℝ) j ≠ 0)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  · exact ⟨Sum.inr ⟨i, t⟩, rfl, trivial⟩

theorem skel_pred_of_not_mem_openCell (D : MData X n x₀) {k : ℕ} (hk : 1 ≤ k) {z : Model D}
    (hz : z ∈ skel D k)
    (hnot : ∀ (i : D.Idx) (S : Finset (Fin (n + 2))), S.card = k + 1 →
      z ∉ openCell D i S) :
    z ∈ skel D (k - 1) := by
  obtain ⟨a, ha, hw⟩ := hz
  rcases a with ⟨i, x⟩ | ⟨i, t⟩
  · rcases Nat.lt_or_ge (ptSup x).card (k + 1) with hlt | hge
    · refine ⟨Sum.inl ⟨i, x⟩, ha, ?_⟩
      show (Finset.univ.filter (fun j : Fin (n + 2) => (x : Fin (n + 2) → ℝ) j ≠ 0)).card
          ≤ k - 1 + 1
      have h2 : (Finset.univ.filter (fun j : Fin (n + 2) => (x : Fin (n + 2) → ℝ) j ≠ 0))
          = ptSup x := rfl
      rw [h2]
      omega
    · have heq : (ptSup x).card = k + 1 := le_antisymm hw hge
      have hzmem : z ∈ openCell D i (ptSup x) := by
        rw [← ha]
        exact ⟨x, rfl, rfl⟩
      exact absurd hzmem (hnot i (ptSup x) heq)
  · exact ⟨Sum.inr ⟨i, t⟩, ha, trivial⟩

theorem skel_one_notMem_openCell (D : MData X n x₀) (i : D.Idx)
    (S : Finset (Fin (n + 2))) (hS : 2 < S.card) {z : Model D} (hz : z ∈ skel D 1) :
    z ∉ openCell D i S := by
  rintro ⟨x, hx, hxz⟩
  obtain ⟨a, ha, hw⟩ := hz
  have hrel : Relation.EqvGen (modelRel D) a (Sum.inl ⟨i, x⟩) :=
    Quotient.exact (ha.trans hxz.symm)
  have hinv := rawWeight_eqvGen D hrel
  have hw2 : rawWeight D a ≤ 2 := by
    rcases a with ⟨ii, xx⟩ | ⟨ii, tt⟩
    · exact hw
    · rw [rawWeight_inr]
      norm_num
  have hcard : rawWeight D (Sum.inl ⟨i, x⟩) = S.card := by
    rw [rawWeight_inl, hx]
  omega


/-! ## Auxiliary facts about cells, used by the cell-pushing step -/

theorem skel_mono (D : MData X n x₀) {a b : ℕ} (h : a ≤ b) : skel D a ⊆ skel D b := by
  rintro z ⟨y, hy, hcond⟩
  refine ⟨y, hy, ?_⟩
  rcases y with ⟨i, xx⟩ | ⟨i, t⟩
  · show (Finset.univ.filter (fun j : Fin (n + 2) => (xx : Fin (n + 2) → ℝ) j ≠ 0)).card
        ≤ b + 1
    exact le_trans hcond (by omega)
  · trivial

/-- Two open cells meet only if the two faces have the same cardinality (the weight — the number
of nonzero barycentric coordinates — is invariant along the gluing relation of the model). -/
theorem openCell_card_eq_of_mem (D : MData X n x₀) {i j : D.Idx} {S T : Finset (Fin (n + 2))}
    {z : Model D} (hzS : z ∈ openCell D i S) (hzT : z ∈ openCell D j T) : S.card = T.card := by
  obtain ⟨x, hx, hxz⟩ := hzS
  obtain ⟨y, hy, hyz⟩ := hzT
  have hrel : Relation.EqvGen (modelRel D) (Sum.inl ⟨i, x⟩) (Sum.inl ⟨j, y⟩) :=
    Quotient.exact (hxz.trans hyz.symm)
  have hw := rawWeight_eqvGen D hrel
  rw [rawWeight_inl, rawWeight_inl, hx, hy] at hw
  exact hw

/-- A point of a closed cell which is not in its open cell lies in a cell of strictly smaller
cardinality, hence in the skeleton two dimensions down. -/
theorem closedCell_skel_pred (D : MData X n x₀) {i : D.Idx} {S : Finset (Fin (n + 2))}
    {z : Model D} (hz : z ∈ closedCell D i S) (hznot : z ∉ openCell D i S) :
    z ∈ skel D (S.card - 2) := by
  rw [closedCell] at hz
  obtain ⟨T, hzT⟩ := Set.mem_iUnion.mp hz
  obtain ⟨hT, hzT⟩ := Set.mem_iUnion.mp hzT
  rw [Finset.mem_powerset] at hT
  have hne : T ≠ S := fun h => hznot (h ▸ hzT)
  have hcard : T.card ≤ S.card - 1 := by
    have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hT, hne⟩)
    omega
  exact skel_mono D (by omega) (openCell_subset_skel D i T hzT)

/-! ## The assembly: descending one dimension at a time

The one-dimensional step (pushing the `k`-cells off, `k ≥ 2`) is the geometric input
`Work.RatHurewicz.skelStep`; everything below it — the descending induction from
`skel D (n+1) = univ` down to `skel D 1 = skeleton D` — is bookkeeping.
-/

section Assembly

variable (D : MData X n x₀)

/-- **The cell-pushing step, as consumed by the assembly.**  For `2 ≤ k`, a path in the
`k`-skeleton with endpoints in the `1`-skeleton is homotopic, relative to its endpoints, to a path
in the `(k-1)`-skeleton.  The proof pushes the `k`-cells off one at a time (after a general-position
homotopy making the path avoid the origins of those cells); see `COMPRESS_NOTES.md`. -/
def SkelStep : Prop :=
  ∀ (k : ℕ), 2 ≤ k → k ≤ n + 1 →
    ∀ {y z : Model D}, y ∈ skeleton D → z ∈ skeleton D → ∀ p : Path y z,
      (∀ t, p t ∈ skel D k) →
      ∃ q : Path y z, (∀ t, q t ∈ skel D (k - 1)) ∧ Nonempty (p.Homotopic q)

/-- **The descending induction**: a path in any skeleton `skel D k`, `1 ≤ k ≤ n+1`, with endpoints
in the `1`-skeleton, is homotopic relative to its endpoints to a path in the `1`-skeleton. -/
theorem compress_to_skel_one (step : SkelStep D) :
    ∀ (k : ℕ), 1 ≤ k → k ≤ n + 1 → ∀ {y z : Model D}, y ∈ skeleton D → z ∈ skeleton D →
      ∀ p : Path y z, (∀ t, p t ∈ skel D k) →
        ∃ q : Path y z, (∀ t, q t ∈ skel D 1) ∧ Nonempty (p.Homotopic q) := by
  intro k hk1
  induction k with
  | zero => omega
  | succ k ih =>
    intro hkn y z hy hz p hp
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      exact ⟨p, hp, ⟨Path.Homotopic.refl p⟩⟩
    · obtain ⟨q, hq, hhom⟩ := step (k + 1) (by omega) hkn hy hz p hp
      obtain ⟨r, hr, hhom2⟩ := ih (by omega) (by omega) hy hz q (by simpa using hq)
      exact ⟨r, hr, ⟨hhom.1.trans hhom2.1⟩⟩

/-- **Paths in the model between skeleton points can be pushed into the skeleton.** -/
theorem exists_path_in_skeleton_of (step : SkelStep D) {y z : Model D}
    (hy : y ∈ skeleton D) (hz : z ∈ skeleton D) (p : Path y z) :
    ∃ q : Path y z, (∀ t, q t ∈ skeleton D) ∧ Nonempty (p.Homotopic q) := by
  obtain ⟨q, hq, hhom⟩ :=
    compress_to_skel_one D step (n + 1) (by omega) le_rfl hy hz p
      (by rw [skel_succ_univ D]; exact fun _ => trivial)
  exact ⟨q, by simpa [skel_one_eq_skeleton] using hq, hhom⟩

/-- **`CompressRel` in dimension `1` from the cell-pushing step**, using the path/cube dictionary
`Work.RatHurewicz.compressRel_one_of_paths`. -/
theorem compressRel_one_of_skelStep (step : SkelStep D) :
    CompressRel (Model D) (skeleton D) 1 :=
  compressRel_one_of_paths (fun y z hy hz p => exists_path_in_skeleton_of D step hy hz p)

end Assembly
