import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Auxi.exists_far_piece
import Submission.Work.Engulf.E4Aux.injOn_of_affineIndependent_image

/-!
# `Work.Engulf.E4P.Far` — placing a chart piece as a far face

`E4c` of Newman §§13–14 attaches the pieces one at a time as *far* faces of the current complex
(`Work.Engulf.Aux.exists_far_piece`).  This file collects the two elementary facts about the
resulting affine map `A : E N →ᵃ[ℝ] E n` that the loop needs:

* `affineIndependent_comp_of_image_eq` : the vertex images of the far face are affinely independent
  (they are a copy of the affinely independent piece);
* `exists_far_piece_data` : the one-shot packaging of `exists_far_piece` together with the
  injectivity of `A` on `PL.simp Δ'` and the fact that `A '' PL.simp Δ'` lies in the positive cube
  (which is what makes `ψ ∘ A` continuous on `PL.simp Δ'`).
-/

open Set Metric PL

namespace Work.Engulf.E4P

/-- If an affine map takes a finite vertex set `Δ'` bijectively onto an affinely independent
vertex set `Δ`, then the images of the vertices of `Δ'` are affinely independent. -/
theorem affineIndependent_comp_of_image_eq {N m : ℕ} {Δ' : Finset (E N)} {Δ : Finset (E m)}
    (A : E N →ᵃ[ℝ] E m) (hcard : Δ'.card = Δ.card)
    (hA : A '' (Δ' : Set (E N)) = (Δ : Set (E m)))
    (hind : AffineIndependent ℝ (fun v : ↥Δ => (v : E m))) :
    AffineIndependent ℝ (fun v : ↥Δ' => A v) := by
  classical
  set f : ↥Δ' → ↥Δ := fun v => ⟨A v, by
    change A (v : E N) ∈ (Δ : Set (E m))
    rw [← hA]
    exact ⟨(v : E N), v.2, rfl⟩⟩ with hf
  have hsurj : Function.Surjective f := by
    intro w
    have hw : ((w : E m)) ∈ A '' (Δ' : Set (E N)) := by rw [hA]; exact w.2
    obtain ⟨v, hv, hvw⟩ := hw
    exact ⟨⟨v, hv⟩, Subtype.ext hvw⟩
  have himg : (Finset.univ : Finset ↥Δ').image f = (Finset.univ : Finset ↥Δ) := by
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => hsurj w⟩
  have hcard2 : ((Finset.univ : Finset ↥Δ').image f).card = (Finset.univ : Finset ↥Δ').card := by
    rw [himg, Finset.card_univ, Finset.card_univ, Fintype.card_coe, Fintype.card_coe]
    exact hcard.symm
  have hinj := Finset.card_image_iff.mp hcard2
  have hinj' : Function.Injective f := by
    intro a b hab
    exact hinj (by simp) (by simp) hab
  have he := hind.comp_embedding (Function.Embedding.mk f hinj')
  simpa [hf, Function.comp_def] using he

/-- The simplex on a face of a complex is the space of a subcomplex. -/
theorem isSubSp_simp_face {N : ℕ} {Γ : Cx N} {s : Finset (E N)} (hs : s ∈ Γ.faces) :
    IsSubSp Γ (simp s) :=
  ⟨fun _ hx => Geometry.SimplicialComplex.convexHull_subset_space hs hx,
    fun _ hx => ⟨s, hs, hx, Subset.rfl⟩⟩

/-- **Place a chart piece as a far face.**  Given a finite complex `Γc` in `E N` and a non-empty
affinely independent vertex set `Δ ⊆ E n` of at most `q ≤ N` vertices whose simplex lies in the
closed `11/16` cube, `exists_far_piece` produces a new complex `Γc' ⊇ Γc`, a far face `Δ'` and an
affine map `A : E N →ᵃ[ℝ] E n` taking `Δ'` onto `Δ`, with the additional facts that the loop uses:
`A` is injective on `simp Δ'` and `A '' simp Δ' ⊆ openCube 1`. -/
theorem exists_far_piece_data {n q N : ℕ} {Γc : Cx N} (hfin : Γc.faces.Finite)
    {Δ : Finset (E n)} (hne : Δ.Nonempty)
    (hind : AffineIndependent ℝ (fun v : ↥Δ => (v : E n)))
    (hcard : Δ.card ≤ q) (hqN : q ≤ N)
    (hcube : simp Δ ⊆ closedCube (n := n) (11 / 16 : ℝ)) :
    ∃ (Γ' : Cx N) (Δ' : Finset (E N)) (A : E N →ᵃ[ℝ] E n),
      Γ'.faces.Finite ∧ Γc.faces ⊆ Γ'.faces ∧ Δ' ∈ Γ'.faces ∧
      (∀ t ∈ Γ'.faces, t ∈ Γc.faces ∨ t ⊆ Δ') ∧
      Γ'.space = Γc.space ∪ simp Δ' ∧ simp Δ' ∩ Γc.space = ∅ ∧
      Δ'.card = Δ.card ∧ A '' (Δ' : Set (E N)) = (Δ : Set (E n)) ∧
      A '' simp Δ' = simp Δ ∧ Set.InjOn A (simp Δ') ∧
      (∀ x ∈ simp Δ', A x ∈ openCube (n := n) 1) := by
  obtain ⟨Γ', Δ', A, hfin', hsub', hmem', hfaces', hspace', hdisj', hcard', hAimg, hAsimp⟩ :=
    Work.Engulf.Aux.exists_far_piece Γc hfin Δ hne hind (le_trans hcard hqN)
  have hindA : AffineIndependent ℝ (fun v : ↥Δ' => A v) :=
    affineIndependent_comp_of_image_eq A hcard' hAimg hind
  have hinj : Set.InjOn A (simp Δ') := Work.Engulf.E4Aux.injOn_of_affineIndependent_image hindA
  refine ⟨Γ', Δ', A, hfin', hsub', hmem', hfaces', hspace', hdisj', hcard', hAimg, hAsimp,
    hinj, ?_⟩
  intro x hx
  have h1 : A x ∈ A '' simp Δ' := ⟨x, hx, rfl⟩
  rw [hAsimp] at h1
  exact Work.Engulf.closedCube_subset_openCube (by norm_num) (hcube h1)

end Work.Engulf.E4P
