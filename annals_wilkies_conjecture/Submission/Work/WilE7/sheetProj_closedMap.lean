/-
  WilE7, `Work.WilE7.sheetProj_closedMap`: **the sheet projection is a closed map**.

  The sheet space `SheetSpace S C = S.X.set ∩ π⁻¹' C` carries the subspace topology, and
  `SheetProj : SheetE S C → C` is the restriction of the continuous projection `projFirst p q`.
  The claim is that this continuous surjection is *closed*.

  Mathematics.  Let `K ⊆ SheetE S C` be closed and let `A = Subtype.val '' K` be its underlying
  point set.  Then
  * `K` is the trace of a closed set `F` of the ambient space (`isClosed_induced_iff`), so
    `closure A ⊆ F`;
  * `A ⊆ S.X.set ⊆ cubeC (p+q)`, so `closure A` is compact (it is a closed subset of the compact
    cube) and `π '' closure A` is closed in `ℝ^p`;
  * the frontier hypothesis says exactly that `π '' closure A ∩ π⁻¹'C ⊆ A`: a point `z` of
    `closure A` with `π z ∈ C` cannot lie in `closure S.X.set \ S.X.set`, because such a point
    would be in `Forbidden` and hence project outside `C`; so `z ∈ S.X.set`, and with `z ∈ F`
    this reads `z ∈ SheetSpace S C ∩ F = A`.
  Therefore `Subtype.val ⁻¹' (π '' closure A) = SheetProj '' K` (both sides are the points of `C`
  whose lift lies in `A = K`), and the right-hand side is closed in `C` because `π '' closure A`
  is closed in `ℝ^p`.

  Note the statement uses `S.X.set` only through the two facts `S.X.set ⊆ cubeC (p+q)` and the
  frontier inclusion `closure S.X.set \ S.X.set ⊆ Forbidden`: no `Good`-ness, no fibrewise
  finiteness and no hypothesis on `C` itself is needed.
-/
import Mathlib
import Submission.Work.WilE7.SheetDefs
import Submission.Work.WilE7.fiberCluster

set_option autoImplicit false

open Set Filter Topology

namespace Work.WilE7

open WilkiesDesign.E

/-- **The frontier criterion, in point-set form.** If `K` is closed in the sheet space
`SheetE S C` over `C`, and every point of the frontier of the stratum is forbidden (hence
projects outside `C`), then no point of `C` lifts to a point of `closure K \ K`: the closure of
the underlying point set of `K`, cut down to the points projecting into `C`, is still `K`.

This is the whole content of the closedness of `SheetProj`: it says that "`C ∩ π '' closure K ⊆ π ''
K`", i.e. that the projection of `K` is closed in `C`. -/
theorem closure_val_image_inter_preimage_subset {p q : ℕ} (S : Stratum p q)
    (C : Set (Fin p → ℝ)) (Forbidden : Set (Fin (p + q) → ℝ))
    (hForb : ∀ w ∈ Forbidden, projFirst p q w ∉ C)
    (hFr : closure S.X.set \ S.X.set ⊆ Forbidden)
    {K : Set (SheetE S C)} (hK : IsClosed K) :
    closure (Subtype.val '' K) ∩ {w | projFirst p q w ∈ C} ⊆ Subtype.val '' K := by
  -- `K` is the trace of a closed set `F` on the sheet space
  obtain ⟨F, hF, hKF⟩ := isClosed_induced_iff.mp hK
  have hAF : Subtype.val '' K ⊆ F := by
    rintro v ⟨w, hw, rfl⟩
    rw [← hKF] at hw
    exact hw
  have hAS : Subtype.val '' K ⊆ S.X.set := by
    rintro v ⟨w, hw, rfl⟩
    exact w.2.1
  have hclF : closure (Subtype.val '' K) ⊆ F := closure_minimal hAF hF
  have hclS : closure (Subtype.val '' K) ⊆ closure S.X.set := closure_mono hAS
  rintro z ⟨hz, hzC⟩
  have hzF : z ∈ F := hclF hz
  -- `z` is in the closure of the stratum and projects into `C`, so `z` cannot be a frontier point
  have hzS : z ∈ S.X.set := by
    by_contra hzS
    exact hForb z (hFr ⟨hclS hz, hzS⟩) hzC
  exact ⟨⟨z, hzS, hzC⟩, by rw [← hKF]; exact hzF, rfl⟩

theorem sheetProj_closedMap {p q : ℕ} (S : WilkiesDesign.E.Stratum p q)
    (C : Set (Fin p → ℝ)) (Forbidden : Set (Fin (p + q) → ℝ))
    (hForb : ∀ w ∈ Forbidden, WilkiesDesign.E.projFirst p q w ∉ C)
    (hFr : closure S.X.set \ S.X.set ⊆ Forbidden) :
    IsClosedMap (Work.WilE7.SheetProj (p := p) (q := q) (S := S) (C := C)) := by
  intro K hK
  -- it suffices to exhibit a closed set of the base whose preimage is `SheetProj '' K`
  rw [isClosed_induced_iff]
  -- the stratum lives in the compact cube, so `closure K` is compact and its projection is closed
  have hAcube : Subtype.val '' K ⊆ cubeC (p + q) := by
    rintro v ⟨w, hw, rfl⟩
    exact fc_subset_cubeC S.X w.2.1
  have hclcube : closure (Subtype.val '' K) ⊆ cubeC (p + q) :=
    closure_minimal hAcube (fc_cubeC_isCompact (p + q)).isClosed
  have himg : IsClosed (projFirst p q '' closure (Subtype.val '' K)) :=
    (((fc_cubeC_isCompact (p + q)).of_isClosed_subset isClosed_closure hclcube).image
      (fc_continuous_projFirst p q)).isClosed
  refine ⟨projFirst p q '' closure (Subtype.val '' K), himg, ?_⟩
  ext x
  constructor
  · -- a base point over the closure of `K` already comes from a point of `K`
    intro hx
    obtain ⟨z, hz, hzπ⟩ := hx
    have hzK : z ∈ Subtype.val '' K :=
      closure_val_image_inter_preimage_subset S C Forbidden hForb hFr hK
        ⟨hz, by show projFirst p q z ∈ C; rw [hzπ]; exact x.2⟩
    obtain ⟨w, hw, hwz⟩ := hzK
    exact ⟨w, hw, Subtype.ext (by show projFirst p q w.1 = x.1; rw [hwz]; exact hzπ)⟩
  · -- conversely the projection of `K` lies in the projection of its closure
    rintro ⟨w, hw, rfl⟩
    exact ⟨w.1, subset_closure ⟨w, hw, rfl⟩, rfl⟩

end Work.WilE7
