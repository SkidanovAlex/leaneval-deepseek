import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.E4Aux.facets_cover_frontier
import Submission.Work.Engulf.E4Aux.exists_vertex_image
import Submission.Work.PL.Generic.eq_of_sum_smul_eq_of_affineIndependent

/-!
# `Work.Engulf.E4Aux.ordGeom` — geometry of a list of faces covering a simplex

Elementary geometry of a list `ord` of faces of a complex `Γ₁` whose members cover a simplex
`simp Δ` (the shelling order of Newman's Lemma 7, Case 1; see
`Submission/Work/Engulf/E4Aux/loop.lean`).  These are the facts the preparation of the shelling
loop (`E4a`/`E4b`) needs in order to identify the vertices and the faces of the shelled simplices.

* `bary` and `bary_mem_simp_iff`: the barycentre of an affinely independent vertex set `t` lies in
  `simp t'` (`t' ⊆ t`) only when `t' = t`.  This is the "relative interior of a simplex" fact,
  proved from the uniqueness of barycentric coordinates.
* `face_subset_ord_of_simp_subset`: a face of `Γ₁` whose hull lies in the union of the members of
  `ord` is a subface of one of the members.
* `exists_ordCx`: the complex carried by the list — `ofErase` of the nonempty subsets of its
  members.  It is the smallest subcomplex of `Γ₁` containing all the members; it is the complex on
  which the vertex perturbation of the loop is performed, because every one of its faces carries
  the affine witness of the member containing it.
* `exists_vertex_image_ord`: the single vertex map of the preparation on the vertices occurring in
  `ord`, well defined because the chart is injective on the open unit cube.
-/

open Set Metric

namespace Work.Engulf.E4Aux

open _root_.PL

variable {N : ℕ}

/-! ## Barycentres detect the vertex set -/

/-- The barycentre of a finite vertex set: the centre of mass of its members. -/
noncomputable def bary (t : Finset (E N)) : E N := (t.card : ℝ)⁻¹ • ∑ v ∈ t, v

theorem bary_mem_simp {t : Finset (E N)} (ht : t.Nonempty) : bary t ∈ simp t := by
  have hcard : (t.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ht).ne'
  rw [PL.simp, bary, Finset.smul_sum]
  refine mem_convexHull_of_weights (S := t) (wt := fun _ => (t.card : ℝ)⁻¹)
    (fun y _ => by positivity) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcard]

/-- **The barycentre detects the vertex set.**  For an affinely independent vertex set `t` and a
subset `t' ⊆ t`, the barycentre of `t` lies in `simp t'` only if `t' = t`: the barycentric
coordinates of the barycentre with respect to `t` are all `1/|t|`, and they are unique. -/
theorem bary_mem_simp_iff {t t' : Finset (E N)}
    (hind : AffineIndependent ℝ (fun v : ↥t => (v : E N))) (ht : t.Nonempty) (ht' : t' ⊆ t) :
    bary t ∈ simp t' ↔ t' = t := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨v, hvt, hvt'⟩ :=
      Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨ht', hne⟩)
    obtain ⟨w, hw0, hw1, hwv⟩ := exists_weights_of_mem_convexHull h
    have hcard : (t.card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr ht).ne'
    have hsum1 : ∑ u ∈ t, (t.card : ℝ)⁻¹ = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcard]
    have hsum2 : ∑ u ∈ t, (if u ∈ t' then w u else 0) = 1 := by
      calc ∑ u ∈ t, (if u ∈ t' then w u else 0)
          = ∑ u ∈ t', (if u ∈ t' then w u else 0) :=
            (Finset.sum_subset ht' (fun u _ hu => by simp only [if_neg hu])).symm
        _ = ∑ u ∈ t', w u := Finset.sum_congr rfl (fun u hu => by simp only [if_pos hu])
        _ = 1 := hw1
    have hvec1 : ∑ u ∈ t, (t.card : ℝ)⁻¹ • u = bary t := by
      rw [bary, Finset.smul_sum]
    have hvec2 : ∑ u ∈ t, (if u ∈ t' then w u else 0) • u = bary t := by
      calc ∑ u ∈ t, (if u ∈ t' then w u else 0) • u
          = ∑ u ∈ t', (if u ∈ t' then w u else 0) • u :=
            (Finset.sum_subset ht' (fun u _ hu => by simp only [if_neg hu, zero_smul])).symm
        _ = ∑ u ∈ t', w u • u := Finset.sum_congr rfl (fun u hu => by simp only [if_pos hu])
        _ = bary t := hwv
    have heq := Work.PL.Generic.eq_of_sum_smul_eq_of_affineIndependent (n := N) (ι := PL.E N)
      (y := fun z => z) (s := t) hind hsum1 hsum2 (by rw [hvec1, hvec2])
    have hv' := heq v hvt
    rw [if_neg hvt'] at hv'
    exact (inv_ne_zero hcard) hv'
  · rintro rfl
    exact bary_mem_simp ht

/-- Restatement of `bary_mem_simp_iff` as an equality of vertex sets. -/
theorem bary_eq_of_mem {t t' : Finset (E N)}
    (hind : AffineIndependent ℝ (fun v : ↥t => (v : E N))) (ht : t.Nonempty) (ht' : t' ⊆ t)
    (h : bary t ∈ simp t') : t' = t :=
  (bary_mem_simp_iff hind ht ht').1 h

/-! ## Faces inside the union of the members of the list -/

/-- **Face identification (`E4a`).**  If the members of a list `ord` are faces of `Γ₁` whose hulls
cover the hull of a face `t` of `Γ₁`, then `t` is a subface of one of the members.  (The
barycentre of `t` lies in some member's hull, hence in the hull of the intersection with `t`;
`bary_mem_simp_iff` forces that intersection to be all of `t`.) -/
theorem face_subset_ord_of_simp_subset {Γ₁ : Cx N} {ord : List (Finset (E N))}
    (hord : ∀ i : Fin ord.length, ord.get i ∈ Γ₁.faces)
    {t : Finset (E N)} (ht : t ∈ Γ₁.faces)
    (hsub : simp t ⊆ ⋃ i : Fin ord.length, simp (ord.get i)) :
    ∃ i : Fin ord.length, t ⊆ ord.get i := by
  have htne := Γ₁.nonempty_of_mem_faces ht
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hsub (bary_mem_simp htne))
  refine ⟨i, ?_⟩
  have h1 : bary t ∈ simp (ord.get i ∩ t) := by
    rw [← Work.Engulf.simp_inter (hord i) ht]
    exact ⟨hi, bary_mem_simp htne⟩
  have h2 : ord.get i ∩ t = t :=
    bary_eq_of_mem (Γ₁.indep ht) htne Finset.inter_subset_right h1
  exact Finset.inter_eq_right.mp h2

/-- A vertex of `Γ₁` lying in a face `s` of `Γ₁` is one of the vertices of `s`. -/
theorem mem_of_vertex_mem_simp {Γ₁ : Cx N} {s : Finset (E N)} (hs : s ∈ Γ₁.faces) {v : E N}
    (hv : {v} ∈ Γ₁.faces) (h : v ∈ simp s) : v ∈ s :=
  (Geometry.SimplicialComplex.vertex_mem_convexHull_iff hv hs).1 h

/-! ## The complex carried by the list -/

/-- The family of nonempty subsets of the members of a list of vertex sets. -/
def ordFaces (ord : List (Finset (E N))) : Set (Finset (E N)) :=
  {t | t.Nonempty ∧ ∃ i : Fin ord.length, t ⊆ ord.get i}

theorem mem_ordFaces {ord : List (Finset (E N))} {t : Finset (E N)} :
    t ∈ ordFaces ord ↔ t.Nonempty ∧ ∃ i : Fin ord.length, t ⊆ ord.get i := Iff.rfl

/-- **The complex carried by a list of faces (`E4a`).**  If the members of a list `ord` are faces
of a complex `Γ₁`, then the family of nonempty subsets of the members is a simplicial complex: it
is the smallest subcomplex of `Γ₁` containing all the members, and its space is the union of their
hulls.  Every face of it is a subset of a member, so the affine witness of that member restricts
to it --- this is what makes the vertex perturbation of the loop applicable. -/
theorem exists_ordCx {Γ₁ : Cx N} (ord : List (Finset (E N)))
    (hG : ∀ i : Fin ord.length, ord.get i ∈ Γ₁.faces) :
    ∃ Γ' : Cx N, Γ'.faces = ordFaces ord ∧ Γ'.faces ⊆ Γ₁.faces ∧
      Γ'.space = ⋃ i : Fin ord.length, simp (ord.get i) := by
  classical
  set F : Set (Finset (E N)) := {t | ∃ i : Fin ord.length, t ⊆ ord.get i} ∪ {∅} with hF
  have hmemF : ∀ t, t ∈ F ↔ t = ∅ ∨ ∃ i : Fin ord.length, t ⊆ ord.get i := by
    intro t
    rw [hF, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact or_comm
  have hdown : IsLowerSet F := by
    intro t s hts ht
    rw [hmemF] at ht ⊢
    rcases ht with h | ⟨i, hi⟩
    · subst h
      exact Or.inl (Finset.Subset.antisymm hts (Finset.empty_subset s))
    · exact Or.inr ⟨i, hts.trans hi⟩
  have hind : ∀ t ∈ F, AffineIndependent ℝ ((↑) : t → E N) := by
    intro t ht
    rw [hmemF] at ht
    rcases ht with rfl | ⟨i, hi⟩
    · rw [affineIndependent_iff]
      intro s w _ _ e he
      have hsub : s = ∅ := by
        by_contra hne
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        exact (Finset.notMem_empty (x : E N)) x.2
      rw [hsub] at he
      exact absurd he (Finset.notMem_empty e)
    · exact (Γ₁.indep (hG i)).mono hi
  have hinter : ∀ s ∈ F, ∀ t ∈ F,
      convexHull ℝ ((s : Set (E N))) ∩ convexHull ℝ ((t : Set (E N))) ⊆
        convexHull ℝ (((s : Set (E N))) ∩ ((t : Set (E N)))) := by
    intro s hs t ht
    rw [hmemF] at hs ht
    rcases hs with rfl | ⟨i, hi⟩
    · simp
    rcases ht with rfl | ⟨j, hj⟩
    · simp
    by_cases hsne : s = ∅
    · subst hsne; simp
    by_cases htne : t = ∅
    · subst htne; simp
    exact Γ₁.inter_subset_convexHull
      (Γ₁.down_closed (hG i) hi (Finset.nonempty_iff_ne_empty.mpr hsne))
      (Γ₁.down_closed (hG j) hj (Finset.nonempty_iff_ne_empty.mpr htne))
  let Γ' : Cx N := Geometry.SimplicialComplex.ofErase F hind hdown hinter
  have hfaces : Γ'.faces = ordFaces ord := by
    show (Geometry.SimplicialComplex.ofErase F hind hdown hinter).faces = ordFaces ord
    rw [Geometry.SimplicialComplex.ofErase_faces]
    ext t
    rw [Set.mem_diff, Set.mem_singleton_iff, mem_ordFaces]
    constructor
    · rintro ⟨htF, htne⟩
      rw [hmemF] at htF
      rcases htF with h0 | ⟨i, hi⟩
      · exact absurd h0 htne
      · exact ⟨Finset.nonempty_iff_ne_empty.mpr htne, i, hi⟩
    · rintro ⟨htne, i, hi⟩
      exact ⟨(hmemF t).mpr (Or.inr ⟨i, hi⟩), Finset.nonempty_iff_ne_empty.mp htne⟩
  refine ⟨Γ', hfaces, ?_, ?_⟩
  · rw [hfaces]
    rintro t ht
    obtain ⟨htne, i, hi⟩ := mem_ordFaces.mp ht
    exact Γ₁.down_closed (hG i) hi htne
  · show (Geometry.SimplicialComplex.ofErase F hind hdown hinter).space
      = ⋃ i : Fin ord.length, simp (ord.get i)
    ext x
    constructor
    · intro hx
      rw [Geometry.SimplicialComplex.mem_space_iff] at hx
      obtain ⟨t, ht, hxt⟩ := hx
      rw [hfaces] at ht
      obtain ⟨-, i, hi⟩ := mem_ordFaces.mp ht
      exact Set.mem_iUnion.mpr ⟨i, simp_mono hi hxt⟩
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      rcases Finset.eq_empty_or_nonempty (ord.get i) with h0 | hne
      · rw [h0, simp_empty] at hxi
        exact hxi.elim
      · refine Geometry.SimplicialComplex.convexHull_subset_space ?_ hxi
        rw [hfaces]
        exact mem_ordFaces.mpr ⟨hne, i, Finset.Subset.refl _⟩

/-! ## The vertex map of the preparation -/

/-- **The vertex map of the preparation (`E4a`).**  Let `ord` be a list of faces of the complex
carried by a map `g`, each face carrying an affine witness `A i` with `g = ψ ∘ A i` on the face
and `A i` taking its values there into the open unit cube.  Then there is a *single* map `y` on
the vertices occurring in `ord` with `y v = A i v` for every member `i` containing `v`: for two
members, `ψ (A i v) = g v = ψ (A j v)`, both arguments lie in the open cube and `ψ` is injective
there.  All values of `y` lie in the open unit cube.  This is the vertex map to which the general
position statement `(T n).gp` and the vertex perturbation `(T n).vertexPerturb` are applied. -/
theorem exists_vertex_image_ord {n : ℕ} {M : Type*} [TopologicalSpace M] {ψ : PL.CubeChart n M}
    {g : PL.E N → M} (ord : List (Finset (PL.E N)))
    (A : ∀ i : Fin ord.length, PL.E N →ᵃ[ℝ] PL.E n)
    (hA : ∀ i : Fin ord.length,
      (∀ x ∈ PL.simp (ord.get i), A i x ∈ PL.openCube 1) ∧
      (∀ x ∈ PL.simp (ord.get i), g x = ψ.toFun (A i x))) :
    ∃ y : ↥(ord.toFinset.biUnion id) → PL.E n,
      (∀ v, y v ∈ PL.openCube 1) ∧
      (∀ v : ↥(ord.toFinset.biUnion id), g (v : PL.E N) = ψ.toFun (y v)) ∧
      ∀ (i : Fin ord.length) (v : PL.E N) (hv : v ∈ ord.get i),
        y ⟨v, Finset.mem_biUnion.mpr
          ⟨ord.get i, List.mem_toFinset.mpr (List.get_mem ord i), hv⟩⟩ = A i v := by
  classical
  have hmem : ∀ v : ↥(ord.toFinset.biUnion id), ∃ i : Fin ord.length,
      (v : PL.E N) ∈ ord.get i := by
    intro v
    obtain ⟨s, hs, hv⟩ := Finset.mem_biUnion.mp v.2
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hs)
    exact ⟨i, hv⟩
  let idx : ↥(ord.toFinset.biUnion id) → Fin ord.length := fun v => Classical.choose (hmem v)
  have hidx : ∀ v : ↥(ord.toFinset.biUnion id), (v : PL.E N) ∈ ord.get (idx v) :=
    fun v => Classical.choose_spec (hmem v)
  refine ⟨fun v => A (idx v) (v : PL.E N), ?_, ?_, ?_⟩
  · intro v
    exact (hA (idx v)).1 _ (Work.Engulf.subset_simp (hidx v))
  · intro v
    exact (hA (idx v)).2 _ (Work.Engulf.subset_simp (hidx v))
  · intro i v hv
    exact Work.Engulf.E4Aux.affine_witness_eq (hA (idx _)).2 (hA i).2 (hA (idx _)).1 (hA i).1
      (hidx _) hv

/-! ## Two consequences used by the preparation of the loop -/

/-- Every face of the complex carried by a list of members has an affine witness: the witness of
any member containing it (`exists_ordCx`). -/
theorem witness_on_ordCx {n : ℕ} {M : Type*} [TopologicalSpace M] {ψ : PL.CubeChart n M}
    {g : PL.E N → M} {ord : List (Finset (PL.E N))}
    (A : ∀ i : Fin ord.length, PL.E N →ᵃ[ℝ] PL.E n)
    (hA : ∀ i : Fin ord.length,
      (∀ x ∈ PL.simp (ord.get i), A i x ∈ PL.openCube 1) ∧
      (∀ x ∈ PL.simp (ord.get i), g x = ψ.toFun (A i x)))
    {Γ' : Cx N} (hfaces : ∀ t ∈ Γ'.faces, t ∈ ordFaces ord) :
    ∀ s ∈ Γ'.faces, ∃ A' : PL.E N →ᵃ[ℝ] PL.E n,
      (∀ x ∈ PL.simp s, A' x ∈ PL.openCube 1) ∧
      (∀ x ∈ PL.simp s, g x = ψ.toFun (A' x)) := by
  intro s hs
  obtain ⟨-, i, hi⟩ := mem_ordFaces.mp (hfaces s hs)
  exact ⟨A i, fun x hx => (hA i).1 x (simp_mono hi hx), fun x hx => (hA i).2 x (simp_mono hi hx)⟩

/-- An affine map (not necessarily injective) sends a set of dimension `≤ d` to a set of dimension
`≤ d`: the image of a simplex is contained in the simplex on the images of its vertices. -/
theorem DomDim.affine_image' {m m' : ℕ} (A : PL.E m →ᵃ[ℝ] PL.E m') {X : Set (PL.E m)} {d : ℤ}
    (h : PL.DomDim X d) : PL.DomDim (A '' X) d := by
  obtain ⟨S, hS, hsub⟩ := h
  refine ⟨S.image (fun s => s.image A), ?_, ?_⟩
  · intro s' hs'
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hs'
    have h1 : (s.image A).card ≤ s.card := Finset.card_image_le
    have h2 : ((s.image A).card : ℤ) ≤ (s.card : ℤ) := by exact_mod_cast h1
    have h3 := hS s hs
    omega
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp (hsub hx)
    refine Set.mem_iUnion₂.mpr ⟨s.image A, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
    have hmem : A x ∈ A '' convexHull ℝ (s : Set (PL.E m)) := ⟨x, hxs, rfl⟩
    rw [AffineMap.image_convexHull] at hmem
    simpa only [PL.simp, Finset.coe_image] using hmem

/-- **The `DomDim` count of the loop.**  The pair bound of the general position statement for a
pair `(ord[i], λ)` (a shelled `(q+1)`-simplex and a face of `Γ₁` with at most `p+1` vertices)
gives dimension `≤ (q+2) + (p+1) - 2 - n ≤ q - 2`, using the room `p + 3 ≤ n` of the ambient
manifold.  This is the count that makes the exceptional set `(q-2)`-dominated, hence the pieces
`q`-vertex simplices. -/
theorem gdbound {q p n : ℕ} (hp : p + 3 ≤ n) :
    ((q : ℤ) + 2 + ((p : ℤ) + 1) - 2 - (n : ℤ)) ≤ (q : ℤ) - 2 := by
  omega

end Work.Engulf.E4Aux
