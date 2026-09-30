import Mathlib
import Submission.Work.Pi6.MSS.Defs
import Submission.Work.Pi6.MSS.essMapLeCardImage
import Submission.Work.Pi6.MSS.cardFrontBackImage
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The Serre cochain filtration is a filtration of cochain complexes respecting the cup product

This file proves `Work.Pi6.MSS.serreCohFilt`: for a map `p : C(E,B)` of topological spaces the
Serre cochain filtration `coFilt 𝕜 (sSingP p)` of the singular cochains of `E`
(`Submission/Work/Pi6/MSS/Defs.lean`) is

* decreasing in the filtration degree, `F^0 = ⊤`, `F^{n+1}C^n = ⊥`,
* a filtration by subcomplexes (`δ` preserves it),
* multiplicative, `F^s · F^{s'} ⊆ F^{s+s'}`,
* and the Alexander–Whitney cup product satisfies the Leibniz rule with respect to `δ`.

The mathematical content is the multiplicativity.  For a singular `(n+m)`-simplex `σ` of `E` whose
image in `B` has essential dimension `< s+s'`, write the image as `ν ∘ π` with `ν` the
nondegenerate core of dimension `t = ess (f σ)` and `π : [n+m] ↠ [t]` a degeneracy.  The
Alexander–Whitney front and back faces of `σ` are then `ν ∘ (incl_front ∘ π)` and
`ν ∘ (incl_back ∘ π)`, whose essential dimensions are `|im (incl_front ∘ π)| - 1` and
`|im (incl_back ∘ π)| - 1` (bound `essMapLeCardImage`).  Monotonicity of `π` shows that the two
vertex sets intersect in exactly `π n`, so the two cardinalities add up to `t + 2`; hence the two
essential dimensions add up to at most `t = ess (f σ) < s + s'`, and one of the two factors of the
cup product vanishes by the hypothesis.  (This is `essFrontBackLe` below.)
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

namespace Work.Pi6.MSS

noncomputable section

/-! ## The essential dimension: basic properties -/

/-- The essential dimension of an `n`-simplex is at most `n`. -/
lemma ess_le_dim {X : SSet.{0}} {n : ℕ} (x : X _⦋n⦌) : ess x ≤ n :=
  SSet.S.dim_toN_le (SSet.S.mk x)

/-- The essential dimension does not increase under pullback along a simplicial operator. -/
lemma ess_map_le {X : SSet.{0}} {n m : ℕ} (x : X _⦋n⦌) (f : ⦋m⦌ ⟶ ⦋n⦌) :
    ess (X.map f.op x) ≤ ess x := by
  have h : SSet.S.mk (X.map f.op x) ≤ SSet.S.mk x := SSet.S.mk_map_le x f
  have h2 : (SSet.S.mk (X.map f.op x)).toN ≤ (SSet.S.mk x).toN :=
    SSet.N.le_iff.mpr (by simpa only [SSet.S.subcomplex_toN] using (SSet.S.le_def.mp h))
  exact SSet.N.dim_le_of_le h2

/-- The essential dimension of a nondegenerate simplex is its dimension. -/
lemma ess_eq_of_nonDegenerate {X : SSet.{0}} {k : ℕ} (y : X _⦋k⦌)
    (hy : y ∈ X.nonDegenerate k) : ess y = k := by
  have h : (SSet.S.mk y).toN = SSet.N.mk y hy := by
    rw [SSet.S.toN_eq_iff]
    rfl
  rw [show ess y = (SSet.S.mk y).toN.dim from rfl, h]
  rfl

/-- **The essential dimensions of the Alexander–Whitney front and back faces add up to at most the
essential dimension.**  This is the multiplicativity input for the Serre filtration. -/
lemma essFrontBackLe {X : SSet.{0}} {n m : ℕ} (x : X _⦋n+m⦌) :
    ess (Work.Cohomology.frontFace X n (n+m) (Nat.le_add_right n m) x) +
      ess (Work.Cohomology.backFace X n m x) ≤ ess x := by
  let s : X.S := SSet.S.mk x
  let ν : X.N := s.toN
  let π : ⦋n+m⦌ ⟶ ⦋ν.dim⦌ := s.toNπ
  have hx : X.map π.op ν.simplex = x := SSet.S.map_toNπ_op_apply s
  haveI : Epi π := by dsimp [π, s]; infer_instance
  have hessx : ess x = ν.dim := rfl
  have hfront : Work.Cohomology.frontFace X n (n+m) (Nat.le_add_right n m) x
      = X.map (CategoryStruct.comp
          (Work.Cohomology.frontIncl n (n+m) (Nat.le_add_right n m)) π).op ν.simplex := by
    rw [← hx, Work.Cohomology.frontFace, op_comp, Functor.map_comp_apply]
  have hback : Work.Cohomology.backFace X n m x
      = X.map (CategoryStruct.comp (Work.Cohomology.backIncl n m) π).op ν.simplex := by
    rw [← hx, Work.Cohomology.backFace, op_comp, Functor.map_comp_apply]
  have hA := essMapLeCardImage (X := X)
    (φ := CategoryStruct.comp (Work.Cohomology.frontIncl n (n+m) (Nat.le_add_right n m)) π)
    (y := ν.simplex)
  have hB := essMapLeCardImage (X := X)
    (φ := CategoryStruct.comp (Work.Cohomology.backIncl n m) π) (y := ν.simplex)
  have hAB := cardFrontBackImage (n := n) (m := m) (t := ν.dim) π
  have h1 : 1 ≤ (Finset.univ.image (SimplexCategory.Hom.toOrderHom
      (CategoryStruct.comp (Work.Cohomology.frontIncl n (n+m) (Nat.le_add_right n m)) π))).card :=
    Finset.card_pos.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
  have h2 : 1 ≤ (Finset.univ.image (SimplexCategory.Hom.toOrderHom
      (CategoryStruct.comp (Work.Cohomology.backIncl n m) π))).card :=
    Finset.card_pos.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
  rw [hfront, hback, hessx]
  omega

/-! ## Naturality of the front/back faces and of the face maps -/

/-- The front face is natural in the simplicial set. -/
lemma frontFace_app {X Y : SSet.{0}} (f : X ⟶ Y) {n N : ℕ} (h : n ≤ N) (σ : X _⦋N⦌) :
    f.app (op ⦋n⦌) (Work.Cohomology.frontFace X n N h σ)
      = Work.Cohomology.frontFace Y n N h (f.app (op ⦋N⦌) σ) := by
  simp only [Work.Cohomology.frontFace]
  exact NatTrans.naturality_apply f (Work.Cohomology.frontIncl n N h).op σ

/-- The back face is natural in the simplicial set. -/
lemma backFace_app {X Y : SSet.{0}} (f : X ⟶ Y) {n m : ℕ} (σ : X _⦋n+m⦌) :
    f.app (op ⦋m⦌) (Work.Cohomology.backFace X n m σ)
      = Work.Cohomology.backFace Y n m (f.app (op ⦋n+m⦌) σ) := by
  simp only [Work.Cohomology.backFace]
  exact NatTrans.naturality_apply f (Work.Cohomology.backIncl n m).op σ

/-- The face maps are natural in the simplicial set. -/
lemma δ_app {X Y : SSet.{0}} (f : X ⟶ Y) {n : ℕ} (i : Fin (n+2)) (σ : X _⦋n+1⦌) :
    f.app (op ⦋n⦌) (X.δ i σ) = Y.δ i (f.app (op ⦋n+1⦌) σ) := by
  rw [SimplicialObject.δ_def, SimplicialObject.δ_def]
  exact NatTrans.naturality_apply f (SimplexCategory.δ i).op σ

/-- The essential dimension does not increase under a face map. -/
lemma ess_δ_le {X : SSet.{0}} {n : ℕ} (i : Fin (n+2)) (y : X _⦋n+1⦌) :
    ess (X.δ i y) ≤ ess y := by
  rw [SimplicialObject.δ_def]
  exact ess_map_le y (SimplexCategory.δ i)

/-! ## The filtration properties -/

variable {𝕜 : Type} [CommRing 𝕜] {X Y : SSet.{0}}

/-- The Serre filtration is decreasing. -/
lemma coFilt_mono (f : X ⟶ Y) (s n : ℕ) :
    coFilt 𝕜 f (s+1) n ≤ coFilt 𝕜 f s n :=
  fun c hc τ hτ => hc τ (by omega)

/-- `F^0` is everything. -/
lemma coFilt_zero (f : X ⟶ Y) (n : ℕ) : coFilt 𝕜 f 0 n = ⊤ :=
  Submodule.eq_top_iff'.mpr fun _c _τ hτ => absurd hτ (Nat.not_lt_zero _)

/-- The filtration is separated in each degree: `F^{n+1}C^n = 0`. -/
lemma coFilt_top (f : X ⟶ Y) (n : ℕ) : coFilt 𝕜 f (n+1) n = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun c hc => ?_
  apply Work.Cohomology.genEval_ext
  intro τ
  rw [hc τ (by have h := ess_le_dim (f.app (op ⦋n⦌) τ); omega)]
  simp [Work.Cohomology.genEval]

/-- The Serre filtration is a filtration by subcomplexes. -/
lemma cochainDiff_mem_coFilt (f : X ⟶ Y) (s n : ℕ) (c : Work.Cohomology.Cochain 𝕜 X n)
    (hc : c ∈ coFilt 𝕜 f s n) :
    Work.Cohomology.cochainDiff 𝕜 X c ∈ coFilt 𝕜 f s (n+1) := by
  intro τ hτ
  rw [Work.Cohomology.genEval_cochainDiff]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hc (X.δ i τ) (by rw [δ_app]; exact lt_of_le_of_lt (ess_δ_le i (f.app (op ⦋n+1⦌) τ)) hτ),
    mul_zero]

/-- The cup product respects the Serre filtration. -/
lemma cup_mem_coFilt (f : X ⟶ Y) (s s' n m : ℕ)
    (α : Work.Cohomology.Cochain 𝕜 X n) (β : Work.Cohomology.Cochain 𝕜 X m)
    (hα : α ∈ coFilt 𝕜 f s n) (hβ : β ∈ coFilt 𝕜 f s' m) :
    Work.Cohomology.cup 𝕜 X α β ∈ coFilt 𝕜 f (s+s') (n+m) := by
  intro σ hσ
  rw [Work.Cohomology.cup_apply']
  have hsum := essFrontBackLe (X := Y) (n := n) (m := m) (f.app (op ⦋n+m⦌) σ)
  rcases lt_or_ge (ess (Work.Cohomology.frontFace Y n (n+m) (Nat.le_add_right n m)
      (f.app (op ⦋n+m⦌) σ))) s with h | h
  · rw [hα (Work.Cohomology.frontFace X n (n+m) (Nat.le_add_right n m) σ)
      (by rw [frontFace_app]; exact h), zero_mul]
  · have hlt : ess (Work.Cohomology.backFace Y n m (f.app (op ⦋n+m⦌) σ)) < s' := by omega
    rw [hβ (Work.Cohomology.backFace X n m σ) (by rw [backFace_app]; exact hlt), mul_zero]

/-- Rewriting `eqToHom` applied to a cochain as a transport of the degree. -/
lemma eqToHom_apply_cast {R : Type} [CommRing R] (X : SSet) {p q : ℕ} (h : p = q)
    (x : (Work.Cohomology.SSetCochainComplex R X).X p) :
    ((CategoryTheory.eqToHom (congrArg (fun k =>
        (Work.Cohomology.SSetCochainComplex R X).X k) h)) :
        (Work.Cohomology.SSetCochainComplex R X).X p ⟶
          (Work.Cohomology.SSetCochainComplex R X).X q) x
      = h ▸ x := by
  cases h
  rfl

/-! ## The Serre filtration of the cochains of a Serre fibration -/

theorem serreCohFilt (𝕜 : Type) [CommRing 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) :
    (∀ s n, Work.Pi6.MSS.coFilt 𝕜 (Work.SSS.sSingP p) (s+1) n ≤
      Work.Pi6.MSS.coFilt 𝕜 (Work.SSS.sSingP p) s n) ∧
    (∀ n, Work.Pi6.MSS.coFilt 𝕜 (Work.SSS.sSingP p) 0 n = ⊤) ∧
    (∀ n, Work.Pi6.MSS.coFilt 𝕜 (Work.SSS.sSingP p) (n+1) n = ⊥) ∧
    (∀ (s n : ℕ) (c : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n),
      c ∈ Work.Pi6.MSS.coFilt 𝕜 (Work.SSS.sSingP p) s n →
      Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) c ∈
        Work.Pi6.MSS.coFilt 𝕜 (Work.SSS.sSingP p) s (n+1)) ∧
    (∀ (s s' n m : ℕ) (α : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n)
      (β : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) m),
      α ∈ Work.Pi6.MSS.coFilt 𝕜 (Work.SSS.sSingP p) s n →
      β ∈ Work.Pi6.MSS.coFilt 𝕜 (Work.SSS.sSingP p) s' m →
      Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) α β ∈
        Work.Pi6.MSS.coFilt 𝕜 (Work.SSS.sSingP p) (s+s') (n+m)) ∧
    (∀ (n m : ℕ) (α : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n)
      (β : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) m),
      Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E)
          (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) α β) =
        ((CategoryTheory.eqToHom (congrArg (fun k => (Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing E)).X k)
            (show (n+1)+m = n+m+1 by omega))) :
          (Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing E)).X ((n+1)+m) ⟶
            (Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing E)).X (n+m+1))
          (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E)
            (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) α) β) +
        (-1 : 𝕜)^n • (CategoryTheory.eqToHom (congrArg (fun k =>
            (Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing E)).X k)
            (show n+(m+1) = n+m+1 by omega)))
          (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) α
            (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) β))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun s n => coFilt_mono _ s n
  · exact fun n => coFilt_zero _ n
  · exact fun n => coFilt_top _ n
  · exact fun s n c hc => cochainDiff_mem_coFilt _ s n c hc
  · exact fun s s' n m α β hα hβ => cup_mem_coFilt _ s s' n m α β hα hβ
  · intro n m α β
    rw [Work.Cohomology.cupLeibniz]
    congr 1
    exact (eqToHom_apply_cast (Work.SSS.sSing E) _ _).symm

end

end Work.Pi6.MSS
