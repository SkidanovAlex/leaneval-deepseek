import Mathlib
import Submission.Work.Pi6.MSS.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The front and back images of an epimorphism of simplices

For a morphism `π : ⦋n+m⦌ ⟶ ⦋t⦌` in `SimplexCategory` whose underlying monotone map is
surjective (equivalently, `π` is an epimorphism), the front `n+1` vertices and the back `m+1`
vertices of `⦋n+m⦌` together cover `⦋t⦌`, and their images under `π` meet in exactly the one point
`π n`.  Consequently the two image sets have total cardinality `t + 2`: the union has `t + 1`
elements and the intersection has `1`.  This is the numerical input used in the construction of
the multiplicative structure on the `E₂` page of the Serre spectral sequence.
-/

namespace Work.Pi6.MSS

/-- **Combinatorial heart of `cardFrontBackImage`.**  For a monotone surjection
`P : Fin (n+m+1) →o Fin (t+1)` (the underlying map of an epimorphism of simplices), the image of
the first `n+1` vertices and the image of the last `m+1` vertices have total cardinality `t + 2`. -/
lemma cardFrontBackImage_aux {n m t : ℕ} (hnm : n + 1 ≤ n + m + 1)
    (P : Fin (n + m + 1) →o Fin (t + 1)) (hP : Function.Surjective ⇑P) :
    (Finset.univ.image (fun i : Fin (n + 1) => P (Fin.castLE hnm i))).card +
      (Finset.univ.image (fun j : Fin (m + 1) => P (Fin.natAdd n j))).card = t + 2 := by
  set F1 : Finset (Fin (t+1)) := Finset.univ.image (fun i : Fin (n + 1) => P (Fin.castLE hnm i)) with hF1
  set F2 : Finset (Fin (t+1)) := Finset.univ.image (fun j : Fin (m + 1) => P (Fin.natAdd n j)) with hF2
  -- the middle vertex lies in both images
  have hmid1 : P ⟨n, by omega⟩ ∈ F1 := by
    rw [hF1, Finset.mem_image]
    refine ⟨⟨n, by omega⟩, Finset.mem_univ _, ?_⟩
    congr 1
  have hmid2 : P ⟨n, by omega⟩ ∈ F2 := by
    rw [hF2, Finset.mem_image]
    refine ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
    congr 1
  -- surjectivity: the front and back images cover everything
  have hunion : F1 ∪ F2 = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro x
    rw [Finset.mem_union, hF1, hF2, Finset.mem_image, Finset.mem_image]
    obtain ⟨u, hu⟩ := hP x
    by_cases h : (u : ℕ) ≤ n
    · left
      refine ⟨⟨u, by omega⟩, Finset.mem_univ _, ?_⟩
      rw [← hu]; congr 1
    · right
      push Not at h
      refine ⟨⟨u - n, by omega⟩, Finset.mem_univ _, ?_⟩
      rw [← hu]; congr 1; apply Fin.ext; simp; omega
  -- monotonicity: the two images meet exactly in the middle vertex
  have hinter : F1 ∩ F2 = {P ⟨n, by omega⟩} := by
    apply Finset.Subset.antisymm
    · intro x hx
      rw [Finset.mem_inter] at hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [hF1, Finset.mem_image] at hx1
      rw [hF2, Finset.mem_image] at hx2
      obtain ⟨i, -, hi⟩ := hx1
      obtain ⟨j, -, hj⟩ := hx2
      rw [Finset.mem_singleton]
      have h1 : P (Fin.castLE hnm i) ≤ P ⟨n, by omega⟩ :=
        P.monotone (Fin.le_iff_val_le_val.mpr (by simp [Fin.val_castLE]; omega))
      have h2 : P ⟨n, by omega⟩ ≤ P (Fin.natAdd n j) :=
        P.monotone (Fin.le_iff_val_le_val.mpr (by simp))
      rw [hi] at h1
      rw [hj] at h2
      exact le_antisymm h1 h2
    · intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx, Finset.mem_inter]
      exact ⟨hmid1, hmid2⟩
  have hc1 : (F1 ∪ F2).card = t + 1 := by rw [hunion, Finset.card_univ, Fintype.card_fin]
  have hc2 : (F1 ∩ F2).card = 1 := by rw [hinter, Finset.card_singleton]
  have h := Finset.card_union_add_card_inter F1 F2
  omega

theorem cardFrontBackImage {n m t : ℕ}
    (π : SimplexCategory.mk (n+m) ⟶ SimplexCategory.mk t) [CategoryTheory.Epi π] :
    (Finset.univ.image (SimplexCategory.Hom.toOrderHom
        (CategoryTheory.CategoryStruct.comp
          (Work.Cohomology.frontIncl n (n+m) (Nat.le_add_right n m)) π))).card +
      (Finset.univ.image (SimplexCategory.Hom.toOrderHom
        (CategoryTheory.CategoryStruct.comp (Work.Cohomology.backIncl n m) π))).card = t + 2 := by
  have hnm : n + 1 ≤ n + m + 1 := by omega
  have hsurj : Function.Surjective ⇑π.toOrderHom :=
    (SimplexCategory.epi_iff_surjective).mp inferInstance
  -- the front inclusion followed by `π` is `P` restricted to the first `n+1` vertices
  have e1 : ⇑(SimplexCategory.Hom.toOrderHom (CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.frontIncl n (n+m) (Nat.le_add_right n m)) π))
      = (fun i : Fin (n+1) => π.toOrderHom (Fin.castLE hnm i)) := by
    funext i
    rw [SimplexCategory.comp_toOrderHom]
    rfl
  -- the back inclusion followed by `π` is `P` restricted to the last `m+1` vertices
  have e2 : ⇑(SimplexCategory.Hom.toOrderHom (CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.backIncl n m) π))
      = (fun j : Fin (m+1) => π.toOrderHom (Fin.natAdd n j)) := by
    funext j
    rw [SimplexCategory.comp_toOrderHom]
    rfl
  rw [e1, e2]
  exact cardFrontBackImage_aux hnm π.toOrderHom hsurj

end Work.Pi6.MSS
