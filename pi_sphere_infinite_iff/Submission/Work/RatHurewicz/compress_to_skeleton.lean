import Mathlib
import Submission.Work.RatHurewicz.cycleModelDefs
import Submission.Work.RatHurewicz.cellDefs
import Submission.Work.RatHurewicz.cellFacts
import Submission.Work.RatHurewicz.skelAvoidOrigins
import Submission.Work.RatHurewicz.skelPushDefs
import Submission.Work.RatHurewicz.pushModelUniform

open scoped Topology Simplicial unitInterval

namespace Work.RatHurewicz

namespace SkelPush

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-- A `Path.Homotopic` from a homotopy of continuous maps that is constant on the endpoints. -/
theorem homotopic_of_homotopyMap {Y : Type} [TopologicalSpace Y] {x y : Y} {p q : Path x y}
    (F : C(unitInterval × unitInterval, Y)) (h0 : ∀ t, F (0, t) = p t)
    (h1 : ∀ t, F (1, t) = q t) (hf0 : ∀ s, F (s, 0) = p 0) (hf1 : ∀ s, F (s, 1) = p 1) :
    p.Homotopic q :=
  ⟨{ toHomotopy := { toContinuousMap := F, map_zero_left := h0, map_one_left := h1 }
     prop' := by
       intro s x hx
       rcases hx with hx | hx
       · rw [hx]; exact hf0 s
       · rw [hx]; exact hf1 s }⟩

/-- Points of a skeleton do not lie in an open cell of larger dimension. -/
theorem skel_not_mem_openCell {D : MData X n x₀} {m : ℕ} {i : D.Idx}
    {S : Finset (Fin (n + 2))} (hcard : m + 1 < S.card) {z : Model D}
    (hz : z ∈ skel D m) : z ∉ openCell D i S := by
  intro hc
  obtain ⟨a, ha, hw⟩ := (mem_skel_iff (D := D)).mp hz
  obtain ⟨x, hx, hxz⟩ := hc
  have hrel : Relation.EqvGen (modelRel D) a (Sum.inl ⟨i, x⟩) :=
    Quotient.exact (ha.trans hxz.symm)
  have hinv := rawWeight_eqvGen' hrel
  rw [rawWeight_inl, hx] at hinv
  omega

/-- The relative interior of the face `S` lies in the `|S|-1`-skeleton. -/
theorem openCell_subset_skel {D : MData X n x₀} (i : D.Idx) (S : Finset (Fin (n + 2))) :
    openCell D i S ⊆ skel D (S.card - 1) := by
  rintro z ⟨x, hx, rfl⟩
  refine ⟨Sum.inl ⟨i, x⟩, rfl, ?_⟩
  have hcard : (ptSupport x).card = S.card := by rw [hx]
  change (ptSupport x).card ≤ S.card - 1 + 1
  rw [hcard]
  omega

/-- The complement of an open cell in its closed cell lies two dimensions down. -/
theorem closedCell_skel_pred {D : MData X n x₀} {i : D.Idx} {S : Finset (Fin (n + 2))}
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
  exact skel_mono' (a := T.card - 1) (b := S.card - 2) (by omega) (openCell_subset_skel i T hzT)

/-- The top skeleton is the whole model. -/
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

/-- The finset of `k`-cells of the model: the pairs (copy index, face of cardinality `k+1`). -/
def kCells (D : MData X n x₀) (k : ℕ) : Finset (D.Idx × Finset (Fin (n + 2))) :=
  ((Finset.univ : Finset D.Idx).product
      ((Finset.univ : Finset (Fin (n + 2))).powerset)).filter (fun c => c.2.card = k + 1)

theorem mem_kCells {D : MData X n x₀} {k : ℕ} {c : D.Idx × Finset (Fin (n + 2))} :
    c ∈ kCells D k ↔ c.2.card = k + 1 := by
  rw [kCells, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_univ _, Finset.mem_powerset.mpr (Finset.subset_univ _)⟩, h⟩

/-- The chosen origin of a `k`-cell: the image of the centroid of its face. -/
def cellOrig (D : MData X n x₀) (k : ℕ) (c : D.Idx × Finset (Fin (n + 2)))
    (hc : c.2.card = k + 1) : Model D :=
  cellOriginOf D c.1 c.2 (Finset.card_pos.mp (by rw [hc]; omega))

/-- **The cell-pushing step** for the `k`-skeleton, `2 ≤ k`: a path in `skel D k` with endpoints in
the `1`-skeleton is homotopic, relative to its endpoints, to a path in `skel D (k-1)`. -/
theorem skelPush_step (D : MData X n x₀) :
    ∀ (k : ℕ), 2 ≤ k → k ≤ n + 1 →
      ∀ (y z : Model D), y ∈ skeleton D → z ∈ skeleton D → ∀ p : Path y z,
        (∀ t, p t ∈ skel D k) →
        ∃ q : Path y z, (∀ t, q t ∈ skel D (k - 1)) ∧ Nonempty (p.Homotopic q) := by
  intro k hk hkn y z hy hz p hp
  classical
  have hy1 : y ∈ skel D 1 := by rw [skel_one_eq_skeleton]; exact hy
  have hz1 : z ∈ skel D 1 := by rw [skel_one_eq_skeleton]; exact hz
  let O : Finset (Model D) :=
    (kCells D k).attach.image (fun c => cellOrig D k c.1 (mem_kCells.mp c.2))
  have hO : ∀ o ∈ O, ∃ (i : D.Idx) (S : Finset (Fin (n + 2))),
      S.card = k + 1 ∧ o ∈ openCell D i S := by
    intro o ho
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp ho
    exact ⟨c.1.1, c.1.2, mem_kCells.mp c.2, cellOrigin_mem_openCell D c.1.1 c.1.2 _⟩
  have mem_O : ∀ (i : D.Idx) (S : Finset (Fin (n + 2))) (hS : S.Nonempty), S.card = k + 1 →
      cellOriginOf D i S hS ∈ O := by
    intro i S hS hcard
    have hc : (i, S) ∈ kCells D k := mem_kCells.mpr hcard
    have hm : cellOrig D k (i, S) (mem_kCells.mp hc) ∈ O := by
      refine Finset.mem_image.mpr ⟨⟨(i, S), hc⟩, Finset.mem_attach _ _, ?_⟩
      rfl
    have h1 : cellOrig D k (i, S) (mem_kCells.mp hc) = cellOriginOf D i S hS := by
      unfold cellOrig
      exact cellOrigin_congr i S _ hS
    rwa [h1] at hm
  obtain ⟨q₀, hq₀a, hq₀s, hq₀h⟩ := skelAvoidOrigins D k hk O hO hy hz p hp
  obtain ⟨Φ, hΦ0, hΦid, hΦw⟩ := pushModelUniform (D := D) k hk
  have hdom : ∀ t, pushDomainModel D k (q₀ t) := by
    intro t
    refine ⟨hq₀s t, ?_⟩
    rintro ⟨i, S, hS, hcard, hEq⟩
    exact hq₀a t (cellOriginOf D i S hS) (mem_O i S hS hcard) hEq
  have hy_mem : y ∈ skel D (k - 1) := skel_mono' (by omega) hy1
  have hz_mem : z ∈ skel D (k - 1) := skel_mono' (by omega) hz1
  let ψ : C(unitInterval, {z : Model D // pushDomainModel D k z}) :=
    ⟨fun t => ⟨q₀ t, hdom t⟩, q₀.continuous.subtype_mk hdom⟩
  let F : C(unitInterval × unitInterval, Model D) :=
    Φ.comp (ContinuousMap.prodMk ContinuousMap.fst (ψ.comp ContinuousMap.snd))
  have hF_val : ∀ s t, F (s, t) = Φ (s, ψ t) := fun s t => rfl
  have hψ0 : (ψ 0 : Model D) = y := q₀.source
  have hψ1 : (ψ 1 : Model D) = z := q₀.target
  let qc : C(unitInterval, Model D) :=
    ⟨fun t => Φ (1, ψ t), Φ.continuous.comp
      (Continuous.prodMk continuous_const ψ.continuous)⟩
  have hqc0 : qc 0 = y := by
    show Φ (1, ψ 0) = y
    rw [hΦid (ψ 0) (by rw [hψ0]; exact hy_mem) 1]
    exact q₀.source
  have hqc1 : qc 1 = z := by
    show Φ (1, ψ 1) = z
    rw [hΦid (ψ 1) (by rw [hψ1]; exact hz_mem) 1]
    exact q₀.target
  let qpath : Path y z := ⟨qc, hqc0, hqc1⟩
  have hq_val : ∀ t, qpath t = Φ (1, ψ t) := fun t => rfl
  have hhom : Nonempty (q₀.Homotopic qpath) := by
    refine ⟨homotopic_of_homotopyMap F ?_ ?_ ?_ ?_⟩
    · intro t
      rw [hF_val, hΦ0]
      rfl
    · intro t
      rw [hF_val, hq_val]
    · intro s
      rw [hF_val, hΦid (ψ 0) (by rw [hψ0]; exact hy_mem) s]
      exact hψ0.trans q₀.source.symm
    · intro s
      rw [hF_val, hΦid (ψ 1) (by rw [hψ1]; exact hz_mem) s]
      exact hψ1.trans q₀.target.symm
  obtain ⟨h1⟩ := hq₀h
  obtain ⟨h2⟩ := hhom
  exact ⟨qpath, fun t => hΦw (ψ t), ⟨h1.trans h2⟩⟩

theorem compress_descend (D : MData X n x₀) :
    ∀ (k : ℕ), 1 ≤ k → k ≤ n + 1 →
      ∀ (y z : Model D), y ∈ skeleton D → z ∈ skeleton D → ∀ p : Path y z,
        (∀ t, p t ∈ skel D k) →
        ∃ q : Path y z, (∀ t, q t ∈ skel D 1) ∧ Nonempty (p.Homotopic q) := by
  intro k
  induction k with
  | zero => intro hk1; omega
  | succ k ih =>
    intro _hk1 hkn y z hy hz p hp
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      exact ⟨p, hp, ⟨Path.Homotopic.refl p⟩⟩
    · obtain ⟨q, hq, hhom⟩ := skelPush_step D (k + 1) (by omega) hkn y z hy hz p hp
      obtain ⟨r, hr, hhom2⟩ := ih (by omega) (by omega) y z hy hz q (by simpa using hq)
      obtain ⟨h1⟩ := hhom
      obtain ⟨h2⟩ := hhom2
      exact ⟨r, hr, ⟨h1.trans h2⟩⟩

end

end SkelPush

end Work.RatHurewicz


namespace Work.RatHurewicz

/-- **Paths in the model can be pushed into the `1`-skeleton.**  For the model `Model D` attached to the simplex data `D` (definition `Work.RatHurewicz.MData`, space `Model D`, `1`-skeleton `skeleton D`, all in `Submission.Work.RatHurewicz.cycleModelDefs`), any path between two points of the `1`-skeleton is homotopic, relative to its endpoints, to a path that stays in the `1`-skeleton.

Route: `Model D` is a finite `Δ`-complex: its cells are the images of the relative interiors of the faces of the copies of `Δ^{n+2}`, each cell is open in the model, and the characteristic map of a face is a homeomorphism from the open simplex onto its cell (points with all coordinates nonzero have singleton classes, and the identifications only ever involve boundary points). The push is done cell by cell, in decreasing order of dimension: for every cell `c` of dimension `≥ 2` choose its origin `z_c` (the image of the centroid of the corresponding face); first homotope the path, relative to its endpoints, so that it avoids a neighbourhood of `z_c` (the cell is convex in its source coordinates and its punctured neighbourhood is path connected, so the standard "reroute the path around the point using the straight-line homotopy inside a convex chart" argument applies; the endpoints are never equal to `z_c` because they lie in the `1`-skeleton); then apply the radial push of the cell, i.e. the self-homotopy of the source simplex `Δ^d` given by `h_σ(x) = c + ((1-σ) + σ·t*(x))(x - c)` with `c` the centroid and `t*(x)` the parameter at which the ray from `c` through `x` leaves `Δ^d`. That map fixes `∂Δ^d` pointwise, hence is compatible with the face identifications and descends to a self-homotopy of `Model D` which moves the path off the cell (`h_1` maps `int Δ^d ∖ {c}` into `∂Δ^d`, and the path avoids `c`). -/
theorem compress_to_skeleton {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}
    (D : Work.RatHurewicz.MData X n x₀) (y z : Work.RatHurewicz.Model D)
    (hy : y ∈ Work.RatHurewicz.skeleton D) (hz : z ∈ Work.RatHurewicz.skeleton D)
    (p : Path y z) :
    ∃ q : Path y z, (∀ t, q t ∈ Work.RatHurewicz.skeleton D) ∧
      Nonempty (Path.Homotopic p q) := by
  obtain ⟨q, hq, hhom⟩ := SkelPush.compress_descend D (n + 1) (by omega) le_rfl y z hy hz p
    (by rw [SkelPush.skel_succ_univ]; exact fun _ => trivial)
  exact ⟨q, by simpa [skel_one_eq_skeleton] using hq, hhom⟩

end Work.RatHurewicz
