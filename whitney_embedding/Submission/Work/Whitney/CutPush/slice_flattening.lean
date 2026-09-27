import Mathlib

open scoped Manifold

/-!
# Flattening a *graph slice* into a plane by a global diffeomorphism

This is the first (and smallest honest) case of the SLICE-FLATTENING input of the finger route
(`NOTES_finger_route_S51.md` §2): the fibre at height `t` of the finger must be carried into a fixed
`(n-1)`-plane `C ⊆ eᗮ`, smoothly in `t`, so that the proved assembly brick
`Work.Whitney.CutPush.exists_global_diffeo_of_fiberwise_diffeos` can turn the family into one global
diffeomorphism of `ℝ^{2n}`.

Here we do the case of a slice contained in the **graph of a smooth function `g` over a plane `P`**,
i.e. `D ⊆ {y : y - g (pr_P y) ∈ P}`.  The flattening is the *base-cutoff shear*

  `Φ y = y - g (pr_P y)`,  inverse  `Φ⁻¹ y = y + g (pr_P y)`,

which is a global `C^∞` diffeomorphism with the inverse displayed (the correction is a function of the
base point `pr_P y` and lands in `Pᗮ`, so the base coordinate is preserved).  On the graph of `g` it
reads `Φ y = pr_P y ∈ P`; composing further with a linear isomorphism `P ≅ C` (available for any two
planes of the same dimension) gives the slice-flattening into a *prescribed* plane `C`.

Note (recorded so it is not re-derived): *this* statement is not the general one.  A slice that is a
*union* of graphs (several sheets at the same height — which happens for a merely continuous `γ`
whose image doubles back in the height coordinate) needs the sheets separated first; see the note.
-/

namespace Work.Whitney.CutPush

open scoped ContDiff Manifold
open Topology

set_option linter.unusedVariables false

/-- The correction `y ↦ g (pr_P y)` of the base-cutoff shear is smooth. -/
theorem contDiff_comp_starProjection {N : ℕ} (P : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    [P.HasOrthogonalProjection]
    (g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin N) => g (P.starProjection y)) :=
  hg.comp (P.starProjection : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)).contDiff

/-- An element of `Pᗮ` is killed by the orthogonal projection onto `P`. -/
theorem starProjection_eq_zero_of_mem_orthogonal {N : ℕ} (P : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    [P.HasOrthogonalProjection] {v : EuclideanSpace ℝ (Fin N)} (hv : v ∈ Pᗮ) :
    P.starProjection v = 0 := by
  have h2 : P.orthogonalProjectionOnto v = 0 :=
    (Submodule.orthogonalProjectionOnto_eq_zero_iff (K := P)).mpr hv
  have h3 : P.starProjection v =
      ((P.orthogonalProjectionOnto v : P) : EuclideanSpace ℝ (Fin N)) := rfl
  rw [h3, h2]
  rfl

/-- **The base-cutoff shear along a plane is a global diffeomorphism.**  For a submodule `P` of a
Euclidean space and a smooth `g` with values in `Pᗮ`, the map `Φ y = y - g (pr_P y)` is a global
`C^∞` diffeomorphism with inverse `Φ⁻¹ y = y + g (pr_P y)`. -/
theorem exists_global_diffeo_of_base_shear {N : ℕ} (P : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    [P.HasOrthogonalProjection]
    (g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hmem : ∀ y, g y ∈ Pᗮ) :
    ∃ (Φ Φinv : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φinv ∧
      Function.LeftInverse Φinv Φ ∧ Function.RightInverse Φinv Φ ∧
      (∀ y, Φ y = y - g (P.starProjection y)) ∧
      (∀ y, Φinv y = y + g (P.starProjection y)) := by
  classical
  have hcorr := contDiff_comp_starProjection P g hg
  have hfix : ∀ y : EuclideanSpace ℝ (Fin N), P.starProjection (g (P.starProjection y)) = 0 :=
    fun y => starProjection_eq_zero_of_mem_orthogonal P (hmem _)
  refine ⟨fun y => y - g (P.starProjection y), fun y => y + g (P.starProjection y),
    ?_, ?_, ?_, ?_, fun y => rfl, fun y => rfl⟩
  · exact contDiff_id.sub hcorr
  · exact contDiff_id.add hcorr
  · intro y
    have hbase : P.starProjection (y - g (P.starProjection y)) = P.starProjection y := by
      rw [map_sub, hfix, sub_zero]
    show (y - g (P.starProjection y)) + g (P.starProjection (y - g (P.starProjection y))) = y
    rw [hbase]
    abel
  · intro y
    have hbase : P.starProjection (y + g (P.starProjection y)) = P.starProjection y := by
      rw [map_add, hfix, add_zero]
    show (y + g (P.starProjection y)) - g (P.starProjection (y + g (P.starProjection y))) = y
    rw [hbase]
    abel

/-- **Graph slices are flattened into the base plane.**  If `D` is contained in the graph of `g`
over `P` (i.e. `y - g (pr_P y) ∈ P` for `y ∈ D`), then some global `C^∞` diffeomorphism of the
ambient space carries `D` into `P` (namely the base-cutoff shear of `g`). -/
theorem exists_global_diffeo_of_graph_slice {N : ℕ} (P : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    [P.HasOrthogonalProjection]
    (g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hmem : ∀ y, g y ∈ Pᗮ)
    (D : Set (EuclideanSpace ℝ (Fin N)))
    (hD : ∀ y ∈ D, y - g (P.starProjection y) ∈ P) :
    ∃ (Φ Φinv : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φinv ∧
      Function.LeftInverse Φinv Φ ∧ Function.RightInverse Φinv Φ ∧
      (∀ y ∈ D, Φ y ∈ P) := by
  obtain ⟨Φ, Φinv, h1, h2, h3, h4, h5, _⟩ := exists_global_diffeo_of_base_shear P g hg hmem
  exact ⟨Φ, Φinv, h1, h2, h3, h4, fun y hy => by rw [h5 y]; exact hD y hy⟩

end Work.Whitney.CutPush

/-! ## The base projection is a homeomorphism on a slice where it is injective

This is the structural step of §S51c/§S51d of `NOTES_finger_route_S51.md`: for a *compact* slice `D`
on which `pr_P` is injective, `pr_P` induces a homeomorphism `↥D ≅ ↥(pr_P '' D)`.  It is what makes
`pr_P '' (O ∩ D)` open in the image for an open `O`, which in turn is what lets one patch *local*
graph functions into a global smooth graph function (the local function is only valid over the
projection of its own piece, and the naive choice of an ambient open set with the wrong trace on the
image breaks that). -/

/-- **`pr_P` restricted to a compact slice on which it is injective is a homeomorphism onto its
image.** -/
theorem starProjection_isHomeomorph_on {N : ℕ} (P : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    [P.HasOrthogonalProjection] (D : Set (EuclideanSpace ℝ (Fin N))) (hDcpt : IsCompact D)
    (hinj : Set.InjOn (fun y : EuclideanSpace ℝ (Fin N) => P.starProjection y) D) :
    IsHomeomorph (fun z : ↥D => (⟨P.starProjection (z : EuclideanSpace ℝ (Fin N)),
      ⟨(z : EuclideanSpace ℝ (Fin N)), z.2, rfl⟩⟩ : ↥(P.starProjection '' D))) := by
  classical
  haveI : CompactSpace ↥D := isCompact_iff_compactSpace.mp hDcpt
  have hcont : Continuous (fun z : ↥D => (⟨P.starProjection (z : EuclideanSpace ℝ (Fin N)),
      ⟨(z : EuclideanSpace ℝ (Fin N)), z.2, rfl⟩⟩ : ↥(P.starProjection '' D))) :=
    Continuous.subtype_mk
      ((P.starProjection : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)).continuous.comp
        continuous_subtype_val)
      (fun z => ⟨(z : EuclideanSpace ℝ (Fin N)), z.2, rfl⟩)
  have hbij : Function.Bijective (fun z : ↥D => (⟨P.starProjection (z : EuclideanSpace ℝ (Fin N)),
      ⟨(z : EuclideanSpace ℝ (Fin N)), z.2, rfl⟩⟩ : ↥(P.starProjection '' D))) := by
    constructor
    · intro z z' h
      have h' : P.starProjection (z : EuclideanSpace ℝ (Fin N)) =
          P.starProjection (z' : EuclideanSpace ℝ (Fin N)) := by
        simpa using congrArg (fun w : ↥(P.starProjection '' D) =>
          (w : EuclideanSpace ℝ (Fin N))) h
      exact Subtype.ext (hinj z.2 z'.2 h')
    · rintro ⟨u, y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  exact isHomeomorph_iff_continuous_bijective.mpr ⟨hcont, hbij⟩





/-- **The trace on the image of an open piece is open in the image.**  For a compact slice `D` on
which `pr_P` is injective and an open `O`, the set `pr_P '' (O ∩ D)`, viewed as a subset of the image
`pr_P '' D`, is open there.  This is the factored form of the key step of §S51c–§S51h of
`NOTES_finger_route_S51`: it produces a statement whose two sides are both `Subtype.val ⁻¹'`-sets, so
the subsequent extraction of an ambient open set (via `isOpen_induced_iff.mp`) is pure bookkeeping. -/
theorem isOpen_preimage_image_inter {N : ℕ} (P : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    [P.HasOrthogonalProjection] (D O : Set (EuclideanSpace ℝ (Fin N)))
    (hDcpt : IsCompact D) (hO : IsOpen O)
    (hinj : Set.InjOn (fun y : EuclideanSpace ℝ (Fin N) => P.starProjection y) D) :
    IsOpen (Subtype.val ⁻¹' (P.starProjection '' (O ∩ D)) : Set ↥(P.starProjection '' D)) := by
  classical
  have hH := starProjection_isHomeomorph_on P D hDcpt hinj
  let φ : ↥D → ↥(P.starProjection '' D) := fun z =>
    ⟨P.starProjection (z : EuclideanSpace ℝ (Fin N)),
      ⟨(z : EuclideanSpace ℝ (Fin N)), z.2, rfl⟩⟩
  have hpre : (Subtype.val ⁻¹' (P.starProjection '' (O ∩ D)) : Set ↥(P.starProjection '' D))
      = φ '' (Subtype.val ⁻¹' O) := by
    ext u
    constructor
    · intro hu
      rw [Set.mem_preimage] at hu
      obtain ⟨y, hy, hyeq⟩ := hu
      obtain ⟨hyO, hyD⟩ := hy
      refine ⟨⟨y, hyD⟩, ?_, ?_⟩
      · simpa using hyO
      · exact Subtype.ext (by simpa using hyeq)
    · rintro ⟨z, hzO', hz⟩
      rw [Set.mem_preimage]
      show ∃ y : EuclideanSpace ℝ (Fin N),
        (y ∈ O ∧ y ∈ D) ∧ P.starProjection y = (u : EuclideanSpace ℝ (Fin N))
      refine ⟨(z : EuclideanSpace ℝ (Fin N)), ⟨?_, z.2⟩, ?_⟩
      · simpa using hzO'
      · have h := congrArg (fun w : ↥(P.starProjection '' D) =>
          (w : EuclideanSpace ℝ (Fin N))) hz
        simpa using h
  exact hpre ▸ hH.isOpenMap _ (hO.preimage continuous_subtype_val)

/-- The projection of a piece is contained in the projection of the whole slice. -/
theorem image_inter_subset {N : ℕ} (P : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    [P.HasOrthogonalProjection] (D O : Set (EuclideanSpace ℝ (Fin N))) :
    P.starProjection '' (O ∩ D) ⊆ P.starProjection '' D :=
  Set.image_mono Set.inter_subset_right

/-- **Local pieces of a slice have the correct trace on the image.**  Given a compact slice `D` with
`pr_P` injective on it and a pointwise open cover `O` of `D` by sets carrying local graph data, there
are finitely many pieces and, for each of them, an ambient open set `W` whose trace on the image
`pr_P '' D` is *exactly* the projection of the piece `O i ∩ D` — not merely contained in it.  (This is
where the naive choice `W := pr_P '' O i` fails; see `NOTES_finger_route_S51` §S51c–§S51h.) -/
theorem exists_finite_base_cover {N : ℕ} (P : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    [P.HasOrthogonalProjection] (D : Set (EuclideanSpace ℝ (Fin N))) (hDcpt : IsCompact D)
    (hinj : Set.InjOn (fun y : EuclideanSpace ℝ (Fin N) => P.starProjection y) D)
    (O : D → Set (EuclideanSpace ℝ (Fin N))) (hOopen : ∀ z, IsOpen (O z))
    (hzO : ∀ z, (z : EuclideanSpace ℝ (Fin N)) ∈ O z) :
    ∃ (t : Finset D) (W : D → Set (EuclideanSpace ℝ (Fin N))),
      (∀ i, IsOpen (W i)) ∧
      (P.starProjection '' D ⊆ ⋃ i ∈ t, W i) ∧
      (∀ i : D, W i ∩ (P.starProjection '' D) = P.starProjection '' ((O i) ∩ D)) := by
  classical
  have hWi : ∀ i : ↥D, ∃ W : Set (EuclideanSpace ℝ (Fin N)), IsOpen W ∧
      W ∩ (P.starProjection '' D) = P.starProjection '' (O i ∩ D) := by
    intro i
    obtain ⟨W, hWopen, hWeq⟩ :=
      isOpen_induced_iff.mp (isOpen_preimage_image_inter P D (O i) hDcpt (hOopen i) hinj)
    refine ⟨W, hWopen, ?_⟩
    ext u
    constructor
    · intro hu
      rw [Set.mem_inter_iff] at hu
      obtain ⟨huW, huK⟩ := hu
      have h1 : (⟨u, huK⟩ : ↥(P.starProjection '' D)) ∈ Subtype.val ⁻¹' W := huW
      rw [hWeq] at h1
      exact h1
    · intro hu
      have huK : u ∈ P.starProjection '' D := image_inter_subset P D (O i) hu
      have hW : u ∈ W := by
        have h1 : (⟨u, huK⟩ : ↥(P.starProjection '' D)) ∈ Subtype.val ⁻¹' W := by
          rw [hWeq]
          exact hu
        exact h1
      rw [Set.mem_inter_iff]
      exact ⟨hW, huK⟩
  choose W hWopen hWtr using hWi
  have hcoverD : D ⊆ ⋃ z : ↥D, O z := by
    intro y hy
    rw [Set.mem_iUnion]
    exact ⟨⟨y, hy⟩, hzO ⟨y, hy⟩⟩
  obtain ⟨t, ht⟩ := hDcpt.elim_finite_subcover O hOopen hcoverD
  refine ⟨t, W, hWopen, ?_, hWtr⟩
  intro u hu
  obtain ⟨y, hyD, rfl⟩ := hu
  obtain ⟨i, hit, hyi⟩ := Set.mem_iUnion₂.mp (ht hyD)
  refine Set.mem_iUnion₂.mpr ⟨i, hit, ?_⟩
  have hmem : P.starProjection y ∈ P.starProjection '' (O i ∩ D) := by
    show ∃ x : EuclideanSpace ℝ (Fin N),
      (x ∈ O i ∧ x ∈ D) ∧ P.starProjection x = P.starProjection y
    refine ⟨y, ⟨?_, ?_⟩, ?_⟩
    · exact hyi
    · exact hyD
    · rfl
  have h2 : P.starProjection y ∈ W i ∩ (P.starProjection '' D) := by
    rw [hWtr i]
    exact hmem
  exact h2.1

/-- **Smooth partition of unity subordinate to a finite open cover of a compact set** (factored form).
This is the only analytic input of the gluing step of §S51j of `NOTES_finger_route_S51`: it is proved
from Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate` and is stated in terms of plain functions
`ℝ^N → ℝ` so that the consumer can form `∑ i, χ i x • g i x` without touching `finsum` bookkeeping. -/
theorem exists_smooth_partition_subordinate_of_compact {N : ℕ} {ι : Type*} [Fintype ι]
    (U : ι → Set (EuclideanSpace ℝ (Fin N))) (hU : ∀ i, IsOpen (U i))
    (K : Set (EuclideanSpace ℝ (Fin N))) (hKc : IsCompact K) (hK : K ⊆ ⋃ i, U i) :
    ∃ f : ι → EuclideanSpace ℝ (Fin N) → ℝ,
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f i)) ∧
      (∀ i x, 0 ≤ f i x) ∧
      (∀ i, tsupport (f i) ⊆ U i) ∧
      (∀ i x, f i x ≤ 1) ∧
      (∀ x ∈ K, ∑ᶠ i, f i x = 1) := by
  classical
  obtain ⟨F, hF⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N))) (s := K) hKc.isClosed U hU hK
  exact ⟨fun i x => F i x, fun i => contMDiff_iff_contDiff.mp (F i).contMDiff,
    fun i x => F.nonneg i x, fun i => hF i, fun i x => F.le_one i x, fun x hx => F.sum_eq_one hx⟩
