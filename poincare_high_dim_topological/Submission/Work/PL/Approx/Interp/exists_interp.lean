import Mathlib
import Submission.Work.PL.Approx.Defs

/-!
# Vertexwise linear interpolation on a finite PL complex

Given a finite geometric simplicial complex `K` in `ℝᴺ` and *any* function `f : ℝᴺ → ℝⁿ`
(no regularity whatsoever is assumed), there is a function `ℓ` that is continuous on `K.space`,
affine on every simplex of `K`, and agrees with `f` at the vertices of every face of `K`.

This is the "vertex interpolant" of the PL approximation argument.  The only data of `f` used is
its values at the vertices: every face of a simplicial complex is affinely independent, so `f`
restricted to the vertices of a face extends to an affine map of the ambient space.  Two such
extensions for faces `s`, `t` agree on the overlap because
`simp s ∩ simp t = simp (s ∩ t)` (gluing of a simplicial complex) and an affine map is determined
by its values on the vertices.  Hence there is a well-defined function which is affine on each
face with the prescribed vertex values; it is continuous on `K.space` because `K.space` is a
finite union of the closed simplices `simp s`.
-/

namespace Work.PL.Approx.Interp

noncomputable section

open Set Metric

/-! ## Two general facts about affine maps -/

/-- The set of points where two affine maps into a vector space agree is convex. -/
lemma interp_convex_eqSet {N n : ℕ} (A B : PL.E N →ᵃ[ℝ] PL.E n) :
    Convex ℝ {x | A x = B x} := by
  rw [convex_iff_segment_subset]
  intro x hx y hy z hz
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨c, _hc, rfl⟩ := hz
  change A x = B x at hx
  change A y = B y at hy
  change A ((AffineMap.lineMap x y) c) = B ((AffineMap.lineMap x y) c)
  rw [AffineMap.apply_lineMap, AffineMap.apply_lineMap, hx, hy]

/-- Affine maps that agree on a set agree on its convex hull. -/
lemma interp_eqOn_convexHull {N n : ℕ} {A B : PL.E N →ᵃ[ℝ] PL.E n} {S : Set (PL.E N)}
    (h : ∀ x ∈ S, A x = B x) : ∀ x ∈ convexHull ℝ S, A x = B x :=
  convexHull_min (fun x hx => h x hx) (interp_convex_eqSet A B)

/-- Prescribed values on the vertices of an affinely independent finite set extend to an affine
map of the ambient space. -/
lemma interp_exists_affineMap {N n : ℕ} (s : Finset (PL.E N))
    (hs : AffineIndependent ℝ ((↑) : s → PL.E N)) (g : PL.E N → PL.E n) :
    ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ v ∈ s, A v = g v := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
  · exact ⟨AffineMap.const ℝ (PL.E N) (0 : PL.E n), by simp⟩
  · -- The differences from `v₀` of the other vertices are linearly independent.
    have hli : LinearIndependent ℝ
        (fun i : {x : s // x ≠ ⟨v₀, hv₀⟩} => ((i.1 : s) : PL.E N) - v₀) :=
      (affineIndependent_iff_linearIndependent_vsub ℝ (fun v : s => (v : PL.E N))
        ⟨v₀, hv₀⟩).mp hs
    let p : Submodule ℝ (PL.E N) :=
      Submodule.span ℝ
        (Set.range (fun i : {x : s // x ≠ ⟨v₀, hv₀⟩} => ((i.1 : s) : PL.E N) - v₀))
    let f' : {x : s // x ≠ ⟨v₀, hv₀⟩} → PL.E n :=
      fun i => g ((i.1 : s) : PL.E N) - g v₀
    let b : Module.Basis {x : s // x ≠ ⟨v₀, hv₀⟩} ℝ p := Module.Basis.span hli
    -- the linear map determined on the span of the difference vectors
    let φ : p →ₗ[ℝ] PL.E n := (b.constr ℝ) f'
    obtain ⟨L, hL⟩ := LinearMap.exists_extend φ
    refine ⟨L.toAffineMap + AffineMap.const ℝ (PL.E N) (g v₀ - L v₀), ?_⟩
    intro v hv
    have happly : ∀ x : PL.E N,
        (L.toAffineMap + AffineMap.const ℝ (PL.E N) (g v₀ - L v₀)) x
          = L x + (g v₀ - L v₀) := by
      intro x
      simp [AffineMap.coe_add, LinearMap.coe_toAffineMap]
    rw [happly]
    rcases eq_or_ne v v₀ with rfl | hne
    · abel
    · have hne' : (⟨v, hv⟩ : s) ≠ ⟨v₀, hv₀⟩ := fun h => hne (congrArg Subtype.val h)
      have hLi : L (v - v₀) = g v - g v₀ := by
        have hmem : v - v₀ ∈ p :=
          Submodule.subset_span
            (Set.mem_range_self (⟨⟨v, hv⟩, hne'⟩ : {x : s // x ≠ ⟨v₀, hv₀⟩}))
        have h1 : L (v - v₀) = φ ⟨v - v₀, hmem⟩ := by
          have := congrArg (fun (F : p →ₗ[ℝ] PL.E n) => F ⟨v - v₀, hmem⟩) hL
          simpa using this
        rw [h1]
        have h2 : (⟨v - v₀, hmem⟩ : p) = b ⟨⟨v, hv⟩, hne'⟩ := by
          rw [Module.Basis.span_apply]
        rw [h2, Module.Basis.constr_basis]
      have hvsub : L v - L v₀ = g v - g v₀ := by rw [← map_sub, hLi]
      calc L v + (g v₀ - L v₀) = (L v - L v₀) + g v₀ := by abel
        _ = (g v - g v₀) + g v₀ := by rw [hvsub]
        _ = g v := by abel

/-! ## The vertex interpolant of a finite complex -/

/-- The affine map attached to a face of `K`: the affine extension of the vertex values of `f`. -/
def interp_faceAff {N n : ℕ} (K : PL.Cx N) (f : PL.E N → PL.E n)
    (s : Finset (PL.E N)) (hs : s ∈ K.faces) : PL.E N →ᵃ[ℝ] PL.E n :=
  Classical.choose (interp_exists_affineMap s (K.indep hs) f)

/-- The affine map attached to a face takes the prescribed values at the vertices of the face. -/
lemma interp_faceAff_spec {N n : ℕ} (K : PL.Cx N) (f : PL.E N → PL.E n)
    (s : Finset (PL.E N)) (hs : s ∈ K.faces) :
    ∀ v ∈ s, interp_faceAff K f s hs v = f v :=
  Classical.choose_spec (interp_exists_affineMap s (K.indep hs) f)

/-- Two faces of `K` have consistent affine maps on their intersection. -/
lemma interp_faceAff_eq_of_mem_inter {N n : ℕ} (K : PL.Cx N) (f : PL.E N → PL.E n)
    {s t : Finset (PL.E N)} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    {x : PL.E N} (hx : x ∈ PL.simp s ∩ PL.simp t) :
    interp_faceAff K f s hs x = interp_faceAff K f t ht x := by
  have hset : PL.simp s ∩ PL.simp t = PL.simp (s ∩ t) := by
    simpa [PL.simp] using K.convexHull_inter_convexHull hs ht
  rw [hset] at hx
  refine interp_eqOn_convexHull (A := interp_faceAff K f s hs)
    (B := interp_faceAff K f t ht) (fun v hv => ?_) x hx
  rw [interp_faceAff_spec K f s hs v (Finset.mem_inter.mp hv).1,
    interp_faceAff_spec K f t ht v (Finset.mem_inter.mp hv).2]

/-- The vertexwise linear interpolant of `f` on the finite complex `K`. -/
def interp {N n : ℕ} (K : PL.Cx N) (f : PL.E N → PL.E n) : PL.E N → PL.E n := by
  classical
  exact fun x => if h : ∃ s ∈ K.faces, x ∈ PL.simp s then
      interp_faceAff K f (Classical.choose h) (Classical.choose_spec h).1 x
    else 0

/-- On a face of `K`, the interpolant agrees with the affine map attached to that face. -/
lemma interp_eq_of_mem {N n : ℕ} (K : PL.Cx N) (f : PL.E N → PL.E n)
    {s : Finset (PL.E N)} (hs : s ∈ K.faces) {x : PL.E N} (hx : x ∈ PL.simp s) :
    interp K f x = interp_faceAff K f s hs x := by
  classical
  have h0 : ∃ s ∈ K.faces, x ∈ PL.simp s := ⟨s, hs, hx⟩
  unfold interp
  rw [dite_eq_left h0]
  exact interp_faceAff_eq_of_mem_inter K f (Classical.choose_spec h0).1 hs
    ⟨(Classical.choose_spec h0).2, hx⟩

/-- The interpolant is continuous on every face of `K`. -/
lemma interp_continuousOn_simp {N n : ℕ} (K : PL.Cx N) (f : PL.E N → PL.E n)
    {s : Finset (PL.E N)} (hs : s ∈ K.faces) :
    ContinuousOn (interp K f) (PL.simp s) :=
  (((interp_faceAff K f s hs).continuous_of_finiteDimensional).continuousOn).congr
    (fun _ hx => interp_eq_of_mem K f hs hx)

/-- A finite union of closed simplices is closed. -/
lemma isClosed_biUnion_simp {N : ℕ} (F : Finset (Finset (PL.E N))) :
    IsClosed (⋃ s ∈ F, PL.simp s) :=
  isClosed_biUnion_finset (fun s _ => s.finite_toSet.isClosed_convexHull ℝ)

/-! ## The main statement -/

lemma exists_interp {N n : ℕ} (K : PL.Cx N) (hK : K.faces.Finite) (f : PL.E N → PL.E n) :
    ∃ ℓ : PL.E N → PL.E n, ContinuousOn ℓ K.space ∧ PL.LinOn K ℓ ∧
      ∀ (s : Finset (PL.E N)), s ∈ K.faces → ∀ v ∈ s, ℓ v = f v := by
  refine ⟨interp K f, ?_, ?_, ?_⟩
  · -- `K.space` is the union of the finitely many closed simplices.
    have hspace : K.space = ⋃ s ∈ hK.toFinset, PL.simp s := by
      rw [Geometry.SimplicialComplex.space]
      apply le_antisymm
      · intro x hx
        obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.mp hx
        exact Set.mem_biUnion (hK.mem_toFinset.mpr hs) hx
      · intro x hx
        obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.mp hx
        exact Set.mem_biUnion (hK.mem_toFinset.mp hs) hx
    rw [hspace]
    have key : ∀ F : Finset (Finset (PL.E N)), (∀ s ∈ F, s ∈ K.faces) →
        ContinuousOn (interp K f) (⋃ s ∈ F, PL.simp s) := by
      intro F
      induction F using Finset.induction with
      | empty =>
        intro _
        simp
      | insert a F _ha ih =>
        intro hmem
        rw [Finset.set_biUnion_insert]
        exact ContinuousOn.union_of_isClosed
          (interp_continuousOn_simp K f (hmem a (Finset.mem_insert_self a F)))
          (ih (fun s hs => hmem s (Finset.mem_insert_of_mem hs)))
          (a.finite_toSet.isClosed_convexHull ℝ)
          (isClosed_biUnion_simp F)
    exact key hK.toFinset (fun s hs => hK.mem_toFinset.mp hs)
  · intro s hs
    exact ⟨interp_faceAff K f s hs, fun x hx => interp_eq_of_mem K f hs hx⟩
  · intro s hs v hv
    rw [interp_eq_of_mem K f hs (subset_convexHull ℝ (s : Set (PL.E N)) hv),
      interp_faceAff_spec K f s hs v hv]

end

end Work.PL.Approx.Interp
