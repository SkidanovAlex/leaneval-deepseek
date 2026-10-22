import Mathlib
import Submission.Work.ANALYTIC.unprimedSetup

/-!
# `x_k·δ_k` lies in the image of `cBounded`

This file proves `Work.ANALYTIC.coordTimesDelta_mem_range`: the element `x_k·δ_k` of `∏^bnd ℤ` over
`S` (the `k`-th coordinate function of a uniformly bounded family `x`, times the basis vector
`δ_k`) is the image under `cBounded(S)` of an explicit element of `P(S)`.

Since `x_k : C(S,ℤ)` is continuous into the discrete group `ℤ` and is uniformly bounded by
`N = Classical.choose x.2`, its values lie in the finite set `Finset.Icc (-N) N`.  For each
`j ∈ Finset.Icc (-N) N` the set `{s | x_k(s) = j}` is clopen, so

`g_j : S ⟶ ℕ∪{∞}`,  `g_j(s) = k` if `x_k(s) = j` and `∞` otherwise,

is a morphism of light profinite sets (`continuous_ite_onePoint_clopen`), and the class `[g_j]` of
`g_j` in `P(S) = ℤ[ℕ∪∞](S)/ℤ[∞](S)` is the element `freeHomEquiv S P (zmap g_j ≫ P_proj)`.
The candidate preimage is `p := Σ_j j · [g_j]`; the identity `P_proj ≫ cBounded = (symm deltaElem)`
(`Work.ANALYTIC.P_proj_cBounded`) together with the naturality and additivity of `freeHomEquiv`
shows that `cBounded(S)` sends `[g_j]` to the family `m ↦ 1_{g_j⁻¹(m)}`, and the pointwise
computation (using `sum_Icc_ite_mul`) identifies `cBounded(S) p` with `coordTimesDelta S x k`.

The only technical point is that the elements of `↥(boundedSeq.obj.obj (op S))` live in a type that
is *definitionally* the submodule `boundedSeqSet S` of `ℕ → C(S,ℤ)` but whose instances are not
syntactically those of the submodule; the lemmas `coe_add_eq`, `coe_smul_eq`, `coe_zero_eq` (all
`rfl`) transport the addition, the scalar multiplication and the zero element into the submodule
flavour, where `Submodule.coe_add` etc. apply.  This gives the pointwise evaluation lemma
`sum_coe_apply` for sums in `↥(boundedSeq.obj.obj (op S))`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.ANALYTIC

/-! ## A function which is constant on a clopen set and `∞` outside -/

/-- A function into `ℕ∪{∞}` which is constant `k` on a clopen set `P` and `∞` outside is
continuous.  (Fibres over finite points are `P` for `n = k` and `∅` otherwise, so the criterion
`Work.ATOM.continuous_onePoint_iff_isClopen` applies.) -/
theorem continuous_ite_onePoint_clopen {X : Type*} [TopologicalSpace X] {P : Set X}
    (hP : IsClopen P) [DecidablePred (· ∈ P)] (k : ℕ) :
    Continuous (fun x : X => if x ∈ P then ((k : ℕ) : OnePoint ℕ) else (∞ : OnePoint ℕ)) := by
  rw [Work.ATOM.continuous_onePoint_iff_isClopen]
  intro n
  rcases eq_or_ne n k with hnk | hnk
  · have h : (fun x : X => if x ∈ P then ((k : ℕ) : OnePoint ℕ) else (∞ : OnePoint ℕ)) ⁻¹'
        {((n : ℕ) : OnePoint ℕ)} = P := by
      ext x
      show (if x ∈ P then ((k : ℕ) : OnePoint ℕ) else (∞ : OnePoint ℕ)) = ((n : ℕ) : OnePoint ℕ) ↔
        x ∈ P
      by_cases hx : x ∈ P
      · rw [if_pos hx]
        exact ⟨fun _ => hx, fun _ => by rw [hnk]⟩
      · rw [if_neg hx]
        exact ⟨fun h => absurd h.symm (OnePoint.coe_ne_infty n), fun h => absurd h hx⟩
    rw [h]
    exact hP
  · have h : (fun x : X => if x ∈ P then ((k : ℕ) : OnePoint ℕ) else (∞ : OnePoint ℕ)) ⁻¹'
        {((n : ℕ) : OnePoint ℕ)} = ∅ := by
      ext x
      show (if x ∈ P then ((k : ℕ) : OnePoint ℕ) else (∞ : OnePoint ℕ)) = ((n : ℕ) : OnePoint ℕ) ↔
        x ∈ (∅ : Set X)
      rw [Set.mem_empty_iff_false]
      by_cases hx : x ∈ P
      · rw [if_pos hx]
        exact ⟨fun h => absurd (OnePoint.coe_eq_coe.mp h).symm hnk, fun h => h.elim⟩
      · rw [if_neg hx]
        exact ⟨fun h => absurd h.symm (OnePoint.coe_ne_infty n), fun h => h.elim⟩
    rw [h]
    exact isClopen_empty

/-! ## The arithmetic identity for the weighted sum over `[-N,N]` -/

/-- If `|y| ≤ N` then the only index of `Finset.Icc (-N) N` with `y = j` is `j = y`, so the
weighted indicator sum is `y * c`. -/
theorem sum_Icc_ite_mul (N y c : ℤ) (hy : |y| ≤ N) :
    (∑ j ∈ Finset.Icc (-N) N, j * (if y = j then c else 0)) = y * c := by
  have hmem : y ∈ Finset.Icc (-N) N := Finset.mem_Icc.mpr (abs_le.mp hy)
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq, if_pos hmem]

/-! ## The indicator morphisms `g_j : S ⟶ ℕ∪{∞}` -/

/-- The morphism `S ⟶ ℕ∪{∞}` which is `k` on the fibre `{s | c s = j}` of `c : C(S,ℤ)` and `∞`
elsewhere.  (The fibre is clopen because `c` is continuous and `ℤ` is discrete.) -/
def gPoint (S : LightProfinite.{0}) (c : C(S, ℤ)) (k : ℕ) (j : ℤ) : S ⟶ (ℕ∪{∞}) := by
  classical
  refine ConcreteCategory.ofHom ⟨fun s : ↥S =>
    if c s = j then ((k : ℕ) : OnePoint ℕ) else (∞ : OnePoint ℕ), ?_⟩
  have hcont := continuous_ite_onePoint_clopen ((isClopen_discrete {j}).preimage c.continuous) k
  simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hcont

/-- The value of `gPoint` at a point. -/
lemma gPoint_val (S : LightProfinite.{0}) (c : C(S, ℤ)) (k : ℕ) (j : ℤ) (s : ↥S) :
    (ConcreteCategory.hom (gPoint S c k j)) s
      = (if c s = j then ((k : ℕ) : OnePoint ℕ) else (∞ : OnePoint ℕ)) := rfl

/-! ## Pointwise values of the generators `boundedSeq.map (g_j).op deltaElem` -/

/-- The action of `∏^bnd ℤ` on morphisms is precomposition of the coordinates. -/
lemma boundedSeq_map_apply {S T : LightProfinite.{0}} (g : T ⟶ S)
    (a : ↥(boundedSeq.obj.obj (op S))) (m : ℕ) (t : ↥T) :
    ((boundedSeq.obj.map g.op a).1 m) t = (a.1 m) (g t) := rfl

/-- **The `(m,s)`-component of `cBounded(S)` at the generator `[g_j]`.**  It is `1` when
`x_k(s) = j` and `m = k`, and `0` otherwise. -/
lemma D_apply (S : LightProfinite.{0}) (c : C(S, ℤ)) (k : ℕ) (j : ℤ) (m : ℕ) (s : ↥S) :
    ((boundedSeq.obj.map (gPoint S c k j).op deltaElem).1 m) s
      = if c s = j then (if m = k then (1 : ℤ) else 0) else 0 := by
  rw [boundedSeq_map_apply]
  show deltaFun m ((ConcreteCategory.hom (gPoint S c k j)) s) = _
  rw [gPoint_val]
  by_cases hx : c s = j
  · rw [if_pos hx, if_pos hx, deltaFun_eq, OnePoint.coe_eq_coe]
    rcases eq_or_ne m k with rfl | hmk
    · simp
    · rw [if_neg hmk, if_neg (Ne.symm hmk)]
  · rw [if_neg hx, if_neg hx, deltaFun_infty]

/-! ## The evaluation of sums in `↥(boundedSeq.obj.obj (op S))`

The type `↥(boundedSeq.obj.obj (op S))` is definitionally the submodule `boundedSeqSet S` of
`ℕ → C(S,ℤ)`, but the addition/scalar multiplication instances resolved for it are those of the
`ModuleCat` structure.  The three `rfl` lemmas below identify them with the submodule instances, so
that `Submodule.coe_add`, `Submodule.coe_smul` and `Submodule.coe_zero` become applicable. -/

/-- The two additions on the (definitionally equal) types agree. -/
lemma coe_add_eq (S : LightProfinite.{0}) (x y : ↥(boundedSeq.obj.obj (op S))) :
    (((x : ↥(boundedSeqSet S)) + (y : ↥(boundedSeqSet S)) : ↥(boundedSeqSet S)).1)
      = (x + y).1 := rfl

/-- The two zeros on the (definitionally equal) types agree. -/
lemma coe_zero_eq (S : LightProfinite.{0}) :
    ((0 : ↥(boundedSeqSet S)).1) = (0 : ↥(boundedSeq.obj.obj (op S))).1 := rfl

/-- The two scalar multiplications by an integer on the (definitionally equal) types agree. -/
lemma coe_smul_eq (S : LightProfinite.{0}) (c : ℤ) (x : ↥(boundedSeq.obj.obj (op S))) :
    ((c • (x : ↥(boundedSeqSet S)) : ↥(boundedSeqSet S)).1) = (c • x).1 := rfl

/-- Pointwise additivity of the evaluation of `↥(boundedSeq.obj.obj (op S))`. -/
lemma coe_add_apply (S : LightProfinite.{0}) (x y : ↥(boundedSeq.obj.obj (op S))) (m : ℕ)
    (t : ↥S.toTop) :
    ((x + y).1 m) t = ((x.1 m) t) + ((y.1 m) t) := by
  rw [← coe_add_eq S x y, Submodule.coe_add]
  simp only [Pi.add_apply, ContinuousMap.add_apply]

/-- The zero element of `↥(boundedSeq.obj.obj (op S))` vanishes at every `(m,t)`. -/
lemma coe_zero_apply (S : LightProfinite.{0}) (m : ℕ) (t : ↥S.toTop) :
    ((0 : ↥(boundedSeq.obj.obj (op S))).1 m) t = 0 := by
  rw [← coe_zero_eq S, Submodule.coe_zero]
  simp

/-- Pointwise `ℤ`-linearity of the evaluation of `↥(boundedSeq.obj.obj (op S))`. -/
lemma coe_smul_apply (S : LightProfinite.{0}) (c : ℤ) (x : ↥(boundedSeq.obj.obj (op S)))
    (m : ℕ) (t : ↥S.toTop) :
    ((c • x).1 m) t = c * ((x.1 m) t) := by
  rw [← coe_smul_eq S c x, Submodule.coe_smul]
  simp only [Pi.smul_apply, ContinuousMap.smul_apply, smul_eq_mul]

/-- The evaluation `x ↦ x_m(t)` of `↥(boundedSeq.obj.obj (op S))`, as an additive
homomorphism. -/
def evHomBS (S : LightProfinite.{0}) (m : ℕ) (t : ↥S.toTop) :
    ↥(boundedSeq.obj.obj (op S)) →+ ℤ where
  toFun x := (x.1 m) t
  map_zero' := coe_zero_apply S m t
  map_add' := fun x y => coe_add_apply S x y m t

/-- **Evaluation of a finite sum in `↥(boundedSeq.obj.obj (op S))`**: a sum is evaluated
componentwise. -/
lemma sum_coe_apply (S : LightProfinite.{0}) (F : ℤ → ↥(boundedSeq.obj.obj (op S)))
    (s : Finset ℤ) (m : ℕ) (t : ↥S.toTop) :
    ((∑ j ∈ s, F j).1 m) t = ∑ j ∈ s, (F j).1 m t :=
  map_sum (evHomBS S m t) F s

/-! ## Linearity of `freeHomEquiv` in the target -/

/-- The comparison `Hom(ℤ[S], M) ≅ M(S)` as an additive homomorphism. -/
noncomputable def freeHomEquivAddHom (S : LightProfinite) (M : LightCondAb) :
    ((free ℤ).obj S.toCondensed ⟶ M) →+ ↥(M.obj.obj (op S)) where
  toFun := freeHomEquiv S M
  map_zero' := freeHomEquiv_zero S M
  map_add' := freeHomEquiv_add S M

/-- `freeHomEquiv` commutes with finite sums. -/
lemma freeHomEquiv_sum {ι : Type*} (S : LightProfinite) (M : LightCondAb) (s : Finset ι)
    (F : ι → ((free ℤ).obj S.toCondensed ⟶ M)) :
    freeHomEquiv S M (∑ i ∈ s, F i) = ∑ i ∈ s, freeHomEquiv S M (F i) :=
  map_sum (freeHomEquivAddHom S M) F s

/-- `freeHomEquiv` commutes with integer scalar multiplication. -/
lemma freeHomEquiv_zsmul (S : LightProfinite) (M : LightCondAb) (c : ℤ)
    (F : (free ℤ).obj S.toCondensed ⟶ M) :
    freeHomEquiv S M (c • F) = c • (freeHomEquiv S M F) :=
  AddMonoidHom.map_zsmul (freeHomEquivAddHom S M) c F

/-- **`cBounded` sends the class of `g` to the indicator family of `g`.**  Namely, the value of
`cBounded(S)` on the element `[g] = freeHomEquiv S P (zmap g ≫ P_proj)` of `P(S)` is the family
`m ↦ 1_{g⁻¹(m)}`, i.e. `boundedSeq.map g.op deltaElem`. -/
lemma freeHomEquiv_gPoint (S : LightProfinite.{0}) (c : C(S, ℤ)) (k : ℕ) (j : ℤ) :
    freeHomEquiv S boundedSeq
        (Work.ATOM.zmap (gPoint S c k j) ≫
          (freeHomEquiv (ℕ∪{∞}) boundedSeq).symm deltaElem)
      = boundedSeq.obj.map (gPoint S c k j).op deltaElem := by
  rw [freeHomEquiv_naturality (gPoint S c k j) boundedSeq
    ((freeHomEquiv (ℕ∪{∞}) boundedSeq).symm deltaElem)]
  exact congrArg (fun y => (ConcreteCategory.hom (boundedSeq.obj.map (gPoint S c k j).op)) y)
    (Equiv.apply_symm_apply (freeHomEquiv (ℕ∪{∞}) boundedSeq) deltaElem)

/-! ## The main theorem -/

/-- **The `k`-th coordinate of a bounded family, times `δ_k`, lies in the image of `cBounded`.**
Concretely: there is an element `p` of `P(S)` whose image under `cBounded` (the map `P ⟶ ∏^bnd ℤ`,
`e_n ↦ δ_n`) is `coordTimesDelta S x k`, i.e. the element of `∏^bnd ℤ` over `S` whose `m`-th
component is `s ↦ x_k(s)·[m = k]`.

Route: `P(S) = ℤ[ℕ∪∞](S)/ℤ[∞](S)` and `cBounded(S)` sends the generator `[g]` (`g : S ⟶ ℕ∪∞`) to
the family `m ↦ 1_{g⁻¹(m)}`.  Since `x.1 k : C(S,ℤ)` is continuous into discrete `ℤ` and `S` is
compact, it takes finitely many values on clopen fibres `U_j = {s | x_k(s) = j}`; take the
finitely many maps `g_j : S ⟶ ℕ∪∞` (`k` on `U_j`, `∞` elsewhere, continuous because `U_j` is
clopen) and `p := Σ_j j·[g_j]` (i.e. the image of `Σ_j j • zmap g_j` under `P_proj`). -/
theorem coordTimesDelta_mem_range (S : LightProfinite.{0})
    (x : ↥(Work.ANALYTIC.boundedSeq.obj.obj (Opposite.op S))) (k : ℕ) :
    ∃ p : ↥(LightCondensed.P.obj.obj (Opposite.op S)),
      Work.ANALYTIC.cBounded.hom.app (Opposite.op S) p =
        Work.ANALYTIC.coordTimesDelta S x k := by
  classical
  obtain ⟨N, hN⟩ := x.2
  -- the candidate element `p := Σ_j j·[g_j]` of `P(S)`
  refine ⟨freeHomEquiv S P
    (∑ j ∈ Finset.Icc (-N) N,
      j • (Work.ATOM.zmap (gPoint S (x.1 k) k j) ≫ P_proj)), ?_⟩
  -- evaluate `cBounded` on it, using naturality in the target
  have hnat := freeHomEquiv_naturality_target S (cBounded : P ⟶ boundedSeq)
    (∑ j ∈ Finset.Icc (-N) N, j • (Work.ATOM.zmap (gPoint S (x.1 k) k j) ≫ P_proj))
  rw [← hnat]
  -- distribute the sum over `≫ cBounded` and use `P_proj ≫ cBounded = (symm deltaElem)`
  have hcomp : (∑ j ∈ Finset.Icc (-N) N,
        j • (Work.ATOM.zmap (gPoint S (x.1 k) k j) ≫ P_proj)) ≫ cBounded
      = ∑ j ∈ Finset.Icc (-N) N,
        j • (Work.ATOM.zmap (gPoint S (x.1 k) k j) ≫
          (freeHomEquiv (ℕ∪{∞}) boundedSeq).symm deltaElem) := by
    rw [Preadditive.sum_comp]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Linear.smul_comp, Category.assoc, P_proj_cBounded]
  rw [hcomp]
  -- pull the sum and the scalar out of `freeHomEquiv`
  rw [freeHomEquiv_sum]
  have hsum : (∑ j ∈ Finset.Icc (-N) N,
        freeHomEquiv S boundedSeq
          (j • (Work.ATOM.zmap (gPoint S (x.1 k) k j) ≫
            (freeHomEquiv (ℕ∪{∞}) boundedSeq).symm deltaElem)))
      = ∑ j ∈ Finset.Icc (-N) N,
        j • (boundedSeq.obj.map (gPoint S (x.1 k) k j).op deltaElem) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [freeHomEquiv_zsmul, freeHomEquiv_gPoint]
  rw [hsum]
  -- compare the two elements componentwise
  refine Subtype.ext ?_
  funext m
  apply ContinuousMap.ext
  intro s
  rw [sum_coe_apply]
  rw [show (∑ j ∈ Finset.Icc (-N) N,
        ((j • (boundedSeq.obj.map (gPoint S (x.1 k) k j).op deltaElem)).1 m) s)
      = ∑ j ∈ Finset.Icc (-N) N,
          j * ((boundedSeq.obj.map (gPoint S (x.1 k) k j).op deltaElem).1 m) s from
    Finset.sum_congr rfl (fun j _ => coe_smul_apply S j _ m s)]
  rw [show (∑ j ∈ Finset.Icc (-N) N,
        j * ((boundedSeq.obj.map (gPoint S (x.1 k) k j).op deltaElem).1 m) s)
      = ∑ j ∈ Finset.Icc (-N) N,
          j * (if x.1 k s = j then (if m = k then (1 : ℤ) else 0) else 0) from
    Finset.sum_congr rfl (fun j _ => by rw [D_apply S (x.1 k) k j m s])]
  rw [sum_Icc_ite_mul N (x.1 k s) (if m = k then (1 : ℤ) else 0) (hN k s)]
  rw [coordTimesDelta_val]

end Work.ANALYTIC
