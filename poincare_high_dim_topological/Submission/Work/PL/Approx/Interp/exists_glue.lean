import Mathlib
import Submission.Work.PL.Approx.Defs
import Submission.Work.PL.Approx.Interp.exists_affineMap_eqOn
import Submission.Work.PL.Approx.Interp.eqOn_simp_of_eqOn

/-!
# Gluing prescribed affine maps along the faces of a finite PL complex

Let `K` be a geometric simplicial complex in `ℝᴺ` with finitely many faces, and suppose that to
every finite vertex set `s` we have attached an affine map `A s : ℝᴺ → ℝⁿ`, in such a way that the
maps attached to two faces `s, t ∈ K.faces` agree on the simplex spanned by `s ∩ t`.  Then the
`A s` glue into a single function `ℓ` which restricts to `A s` on every simplex `PL.simp s` of `K`
and is continuous on `K.space`.

This is the "gluing" step of the PL approximation argument: it produces a globally defined
function out of the local affine pieces, without any hypothesis on where the `A s` come from.
-/

namespace Work.PL.Approx.Interp

noncomputable section

open Set Metric

/-- The function obtained by gluing the affine maps `A s` along the faces of `K`: at a point `x`
of `K.space` it is the value of `A s` for any face `s` of `K` containing `x`, and `0` outside
`K.space`. -/
def glueFun {N n : ℕ} (K : PL.Cx N) (A : Finset (PL.E N) → PL.E N →ᵃ[ℝ] PL.E n) :
    PL.E N → PL.E n := by
  classical
  exact fun x => if h : ∃ s ∈ K.faces, x ∈ PL.simp s then A (Classical.choose h) x else 0

/-- The glued function is independent of the chosen face: on a face of `K` it agrees with the
affine map attached to that face. -/
lemma glueFun_eq_of_mem {N n : ℕ} (K : PL.Cx N)
    (A : Finset (PL.E N) → PL.E N →ᵃ[ℝ] PL.E n)
    (hA : ∀ (s : Finset (PL.E N)) (hs : s ∈ K.faces) (t : Finset (PL.E N)) (ht : t ∈ K.faces),
      ∀ x ∈ PL.simp (s ∩ t), A s x = A t x)
    {s : Finset (PL.E N)} (hs : s ∈ K.faces) {x : PL.E N} (hx : x ∈ PL.simp s) :
    glueFun K A x = A s x := by
  classical
  have h0 : ∃ s ∈ K.faces, x ∈ PL.simp s := ⟨s, hs, hx⟩
  have ht : Classical.choose h0 ∈ K.faces := (Classical.choose_spec h0).1
  have hxt : x ∈ PL.simp (Classical.choose h0) := (Classical.choose_spec h0).2
  unfold glueFun
  rw [dite_eq_left h0]
  have hset : PL.simp (Classical.choose h0) ∩ PL.simp s
      = PL.simp (Classical.choose h0 ∩ s) := by
    simpa [PL.simp] using K.convexHull_inter_convexHull ht hs
  have hxinter : x ∈ PL.simp (Classical.choose h0 ∩ s) := by
    rw [← hset]; exact ⟨hxt, hx⟩
  exact hA (Classical.choose h0) ht s hs x hxinter

/-- The glued function is continuous on every simplex of `K`. -/
lemma glueFun_continuousOn_simp {N n : ℕ} (K : PL.Cx N)
    (A : Finset (PL.E N) → PL.E N →ᵃ[ℝ] PL.E n)
    (hA : ∀ (s : Finset (PL.E N)) (hs : s ∈ K.faces) (t : Finset (PL.E N)) (ht : t ∈ K.faces),
      ∀ x ∈ PL.simp (s ∩ t), A s x = A t x)
    {s : Finset (PL.E N)} (hs : s ∈ K.faces) :
    ContinuousOn (glueFun K A) (PL.simp s) :=
  ((A s).continuous_of_finiteDimensional).continuousOn.congr
    (fun x hx => glueFun_eq_of_mem K A hA hs hx)

/-- A finite union of closed simplices is closed. -/
lemma isClosed_glue_biUnion_simp {N : ℕ} (F : Finset (Finset (PL.E N))) :
    IsClosed (⋃ s ∈ F, PL.simp s) :=
  isClosed_biUnion_finset (fun s _ => s.finite_toSet.isClosed_convexHull ℝ)

lemma exists_glue {N n : ℕ} (K : PL.Cx N) (hK : K.faces.Finite)
    (A : Finset (PL.E N) → PL.E N →ᵃ[ℝ] PL.E n)
    (hA : ∀ (s : Finset (PL.E N)) (hs : s ∈ K.faces) (t : Finset (PL.E N)) (ht : t ∈ K.faces),
      ∀ x ∈ PL.simp (s ∩ t), A s x = A t x) :
    ∃ ℓ : PL.E N → PL.E n,
      (∀ (s : Finset (PL.E N)), s ∈ K.faces → ∀ x ∈ PL.simp s, ℓ x = A s x) ∧
      ContinuousOn ℓ K.space := by
  classical
  refine ⟨glueFun K A, ?_, ?_⟩
  · intro s hs x hx
    exact glueFun_eq_of_mem K A hA hs hx
  · have hspace : K.space = ⋃ s ∈ hK.toFinset, PL.simp s := by
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
        ContinuousOn (glueFun K A) (⋃ s ∈ F, PL.simp s) := by
      intro F
      induction F using Finset.induction with
      | empty =>
        intro _
        simp
      | insert a F _ha ih =>
        intro hmem
        rw [Finset.set_biUnion_insert]
        exact ContinuousOn.union_of_isClosed
          (glueFun_continuousOn_simp K A hA (hmem a (Finset.mem_insert_self a F)))
          (ih (fun s hs => hmem s (Finset.mem_insert_of_mem hs)))
          (a.finite_toSet.isClosed_convexHull ℝ)
          (isClosed_glue_biUnion_simp F)
    exact key hK.toFinset (fun s hs => hK.mem_toFinset.mp hs)

end

end Work.PL.Approx.Interp
