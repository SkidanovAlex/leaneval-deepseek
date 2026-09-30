import Mathlib
import Submission.Work.Cohomology.cup1defs
import Submission.Work.Pi6.MSS.Defs
import Submission.Work.Pi6.MSS.serreCohFilt
import Submission.Work.Pi6.MSS.essMapLeCardImage
import Submission.Work.Pi6.MSS.cardFrontBackImage
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The essential dimensions of the cup-1 faces

For the `s`-th summand of the cup-1 product one pairs the front `n`-face `[s, s+n]` with the
back `m`-face `[0,s] ∪ [s+n, n+m-1]` (see `Submission/Work/Cohomology/cup1Shuffle.lean`).  Both
are pullbacks of a simplex along order maps `Fface n m s` and `Gface n m s` into `⦋n+m-1⦌`.

This file proves the numerical estimate that makes the cup-1 product respect the Serre
filtration: if `y` is an `(n+m-1)`-simplex then the essential dimensions of its two cup-1 faces
add up to at most `ess y + 1`.

The argument is the one used for `essFrontBackLe`: write `y = Y.map π.op ν.simplex` with `ν` the
nondegenerate core of `y` of dimension `t = ess y` and `π : ⦋n+m-1⦌ ↠ ⦋t⦌` a degeneracy.  Then
the essential dimension of a pullback along `φ` is at most `|im φ| - 1`
(`essMapLeCardImage`), so it suffices to bound the cardinalities of the images of the two
composites `Fface ≫ π` and `Gface ≫ π` by `t + 3` in total.

Writing `P` for the underlying monotone surjection of `π`, the image `A` of `Fface ≫ π` is
`P {s, …, s+n}` and the image `G` of `Gface ≫ π` is `P {0,…,s} ∪ P {s+n,…,n+m-1}`.  Both are
contained in `Fin (t+1)`, so `|A ∪ G| ≤ t+1`; and an element of `A ∩ G` which is
`P(a) = P(b)` with `a ∈ {s,…,s+n}` and `b` in one of the two pieces of the second set lies
between `P s` and `P (s+n)` in a chain of inequalities that collapses it to `P s` or `P (s+n)`.
Hence `|A ∩ G| ≤ 2` and `|A| + |G| = |A ∪ G| + |A ∩ G| ≤ t + 3`.
-/

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section

/-- **Cardinality bound for the two cup-1 faces.**  Let `P : Fin (n+m) →o Fin (t+1)` be a
monotone map (the underlying map of the degeneracy to the nondegenerate core of a simplex), let
`f : Fin (n+1) → Fin (n+m)` have values `s + i` and let `g : Fin (m+1) → Fin (n+m)` be the
`Gface` map (values `j` for `j ≤ s` and `j + n - 1` for `j > s`, with `s = k`).  Then the
cardinalities of the images `P ∘ f` and `P ∘ g` add up to at most `t + 3`. -/
lemma cardImage_face_bound {n m k t : ℕ} (hk : k < m)
    (P : Fin (n + m - 1 + 1) →o Fin (t + 1))
    (f : Fin (n + 1) → Fin (n + m - 1 + 1)) (g : Fin (m + 1) → Fin (n + m - 1 + 1))
    (hf : ∀ i, (f i).val = k + i.val)
    (hg1 : ∀ j, j.val ≤ k → (g j).val = j.val)
    (hg2 : ∀ j, k < j.val → (g j).val = j.val + n - 1) :
    (Finset.univ.image (fun i => P (f i))).card +
      (Finset.univ.image (fun j => P (g j))).card ≤ t + 3 := by
  -- the two middle vertices `k` and `k+n` of the source of `P`
  let pk : Fin (n + m - 1 + 1) := ⟨k, by omega⟩
  let pq : Fin (n + m - 1 + 1) := ⟨k + n, by omega⟩
  have hpk : pk.val = k := rfl
  have hpq : pq.val = k + n := rfl
  set A : Finset (Fin (t + 1)) := Finset.univ.image (fun i => P (f i)) with hA
  set G : Finset (Fin (t + 1)) := Finset.univ.image (fun j => P (g j)) with hG
  have hkey := Finset.card_union_add_card_inter A G
  -- both images lie in `Fin (t+1)`
  have hcu : (A ∪ G).card ≤ t + 1 := by
    have h := Finset.card_le_card (Finset.subset_univ (A ∪ G))
    simpa [Finset.card_univ, Fintype.card_fin] using h
  -- the two images meet in at most the two vertices `P k` and `P (k+n)`
  have hsub : A ∩ G ⊆ ({P pk, P pq} : Finset (Fin (t + 1))) := by
    intro x hx
    rw [Finset.mem_inter, hA, hG, Finset.mem_image, Finset.mem_image] at hx
    obtain ⟨⟨i, -, hi⟩, ⟨j, -, hj⟩⟩ := hx
    rw [Finset.mem_insert, Finset.mem_singleton]
    by_cases hjk : j.val ≤ k
    · -- `g j ≤ pk ≤ f i` and `P (g j) = P (f i)`, so `x = P pk`
      left
      have h1 : P (g j) ≤ P pk :=
        P.monotone (Fin.le_iff_val_le_val.mpr (by rw [hg1 j hjk, hpk]; omega))
      have h2 : P pk ≤ P (f i) :=
        P.monotone (Fin.le_iff_val_le_val.mpr (by rw [hpk, hf i]; omega))
      rw [hj] at h1
      rw [hi] at h2
      exact le_antisymm h1 h2
    · -- `f i ≤ pq ≤ g j` and `P (f i) = P (g j)`, so `x = P pq`
      right
      push Not at hjk
      have h1 : P pq ≤ P (g j) :=
        P.monotone (Fin.le_iff_val_le_val.mpr (by rw [hpq, hg2 j hjk]; omega))
      have h2 : P (f i) ≤ P pq :=
        P.monotone (Fin.le_iff_val_le_val.mpr (by rw [hf i, hpq]; omega))
      rw [hj] at h1
      rw [hi] at h2
      exact le_antisymm h2 h1
  have hc2 : (A ∩ G).card ≤ 2 := by
    have h := Finset.card_le_card hsub
    refine le_trans h ?_
    rw [show ({P pk, P pq} : Finset (Fin (t + 1))) = insert (P pk) {P pq} from rfl]
    calc (insert (P pk) {P pq} : Finset (Fin (t + 1))).card
        ≤ ({P pq} : Finset (Fin (t + 1))).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  omega

theorem cup1FaceEss (n m k : ℕ) (hk : k < m) (Y : SSet.{0}) (y : Y.obj (Opposite.op (SimplexCategory.mk (n + m - 1)))) : Work.Pi6.MSS.ess (Y.map (Work.Cohomology.Fface n m k (by omega)).op y) + Work.Pi6.MSS.ess (Y.map (Work.Cohomology.Gface n m k (by omega)).op y) ≤ Work.Pi6.MSS.ess y + 1 := by
  have hkm : k + n ≤ n + m - 1 := by omega
  let s : Y.S := SSet.S.mk y
  let ν : Y.N := s.toN
  let π : ⦋n + m - 1⦌ ⟶ ⦋ν.dim⦌ := s.toNπ
  have hy : Y.map π.op ν.simplex = y := SSet.S.map_toNπ_op_apply s
  have hess : ess y = ν.dim := rfl
  let f : Fin (n + 1) → Fin (n + m - 1 + 1) :=
    fun i => SimplexCategory.Hom.toOrderHom (Work.Cohomology.Fface n m k hkm) i
  let g : Fin (m + 1) → Fin (n + m - 1 + 1) :=
    fun j => SimplexCategory.Hom.toOrderHom (Work.Cohomology.Gface n m k hkm) j
  -- the two faces are pullbacks along the composites with the degeneracy `π`
  have hF : Y.map (Work.Cohomology.Fface n m k (by omega)).op y
      = Y.map (Work.Cohomology.Fface n m k hkm ≫ π).op ν.simplex := by
    rw [← hy, op_comp, Functor.map_comp_apply]
  have hG : Y.map (Work.Cohomology.Gface n m k (by omega)).op y
      = Y.map (Work.Cohomology.Gface n m k hkm ≫ π).op ν.simplex := by
    rw [← hy, op_comp, Functor.map_comp_apply]
  have hA := essMapLeCardImage (X := Y) (φ := Work.Cohomology.Fface n m k hkm ≫ π)
    (y := ν.simplex)
  have hB := essMapLeCardImage (X := Y) (φ := Work.Cohomology.Gface n m k hkm ≫ π)
    (y := ν.simplex)
  have hAeq : (Finset.univ.image (SimplexCategory.Hom.toOrderHom
        (Work.Cohomology.Fface n m k hkm ≫ π)))
      = Finset.univ.image (fun i : Fin (n + 1) => π.toOrderHom (f i)) := by
    apply Finset.image_congr
    intro i _
    rw [SimplexCategory.comp_toOrderHom]
    rfl
  have hBeq : (Finset.univ.image (SimplexCategory.Hom.toOrderHom
        (Work.Cohomology.Gface n m k hkm ≫ π)))
      = Finset.univ.image (fun j : Fin (m + 1) => π.toOrderHom (g j)) := by
    apply Finset.image_congr
    intro j _
    rw [SimplexCategory.comp_toOrderHom]
    rfl
  rw [hAeq] at hA
  rw [hBeq] at hB
  have hcard := cardImage_face_bound (n := n) (m := m) (k := k) (t := ν.dim) hk π.toOrderHom f g
    (fun i => rfl)
    (fun j hj => Work.Cohomology.Gfun_val_le n m k hkm j hj)
    (fun j hj => Work.Cohomology.Gfun_val_gt n m k hkm j hj)
  have h1 : 1 ≤ (Finset.univ.image (fun i : Fin (n + 1) => π.toOrderHom (f i))).card :=
    Finset.card_pos.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
  have h2 : 1 ≤ (Finset.univ.image (fun j : Fin (m + 1) => π.toOrderHom (g j))).card :=
    Finset.card_pos.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
  rw [hF, hG, hess]
  omega

end

end Work.Pi6.MSS
