import Mathlib
import Submission.Work.ANALYTIC.unprimedSetup

/-!
# `coordTimesDeltaAt S x f` lies in the image of `cBounded`

For a light profinite set `S`, a bounded family `x ∈ ∏^bnd ℤ(S)` and a continuous map
`f : S ⟶ ℕ∪{∞}`, the element

`y_m(s) = x_m(s)·[f s = m]`

of `∏^bnd ℤ(S)` is shown to lie in the image of `cBounded(S) : P(S) ⟶ ∏^bnd ℤ(S)`
(`P = ℤ[ℕ∪∞]/ℤ[∞]`); this is the general form of `coordTimesDelta_mem_range`, where `f` is the
constant map at `k` (there `y = x_k·δ_k`).

## The construction

`cBounded` corresponds under `freeHomEquiv` to `deltaElem ∈ ∏^bnd ℤ(ℕ∪{∞})`, whose `m`-th
component is `deltaFun m`, and the composite `ℤ[ℕ∪{∞}] --P_proj--> P --cBounded--> ∏^bnd ℤ` sends
the generator `[g]` (`g : S ⟶ ℕ∪{∞}` continuous) to the element `E_g` whose `m`-th component is
`s ↦ [g s = m]`.

For a fixed `j : ℤ` define `gAt S x f j : S ⟶ ℕ∪{∞}` by

`gAt S x f j s = f s` if `f s = m` is finite and `x_m(s) = j`, and `gAt S x f j s = ∞` otherwise.

This is continuous, because its fibre over `m : ℕ` is the *clopen* set
`{s | f s = m ∧ x_m(s) = j}` (`Work.ATOM.continuous_onePoint_iff_isClopen`).  Then, for any bound
`N` on `x`,

`(∑_{j ∈ Icc (-N) N} j·E_{gAt S x f j})_m(s) = ∑_j j·[gAt S x f j s = m] = x_m(s)·[f s = m]`,

because `gAt S x f j s = m` holds exactly for `j = x_m(s)` when `f s = m`, and for no `j` when
`f s ≠ m`; note that `x_m(s) ∈ Icc (-N) N` by the bound.  Hence

`y = ∑_{j ∈ Icc (-N) N} j • (zmap (gAt S x f j) ≫ cBounded)`

lies in the image of `cBounded(S)`: the element `∑_j j • (zmap (gAt S x f j) ≫ P_proj)` of `P(S)`
is a preimage, since `freeHomEquiv` is additive and natural in the target.

The finite sum over `Icc (-N) N` is legitimate because `x` is *uniformly* bounded: the function
`s ↦ x_{f s}(s)` takes only finitely many values, and each of them can be used as a constant
coefficient of one of the finitely many generators `[gAt S x f j]`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.ANALYTIC

attribute [local instance] Classical.propDecidable

/-- The continuous map `S ⟶ ℕ∪{∞}` which is `f s` when `f s` is a finite number `m` with
`x_m(s) = j`, and `∞` otherwise.  Its fibre over `m : ℕ` is the clopen set
`{s | f s = m ∧ x_m(s) = j}`, which is what makes it continuous. -/
def gAt (S : LightProfinite.{0}) (x : ↥(boundedSeq.obj.obj (op S)))
    (f : S ⟶ (ℕ∪{∞})) (j : ℤ) : S ⟶ (ℕ∪{∞}) :=
  ConcreteCategory.ofHom ⟨fun s : ↥S =>
    if ∃ m : ℕ, f s = (m : OnePoint ℕ) ∧ x.1 m s = j then f s else (∞ : OnePoint ℕ),
    by
      rw [Work.ATOM.continuous_onePoint_iff_isClopen]
      intro n
      have hfib : (fun s : ↥S =>
          if ∃ m : ℕ, f s = (m : OnePoint ℕ) ∧ x.1 m s = j then f s else (∞ : OnePoint ℕ)) ⁻¹'
            {OnePoint.some n} = {s : ↥S | f s = (n : OnePoint ℕ)} ∩ {s : ↥S | x.1 n s = j} := by
        ext s
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · intro h
          by_cases hex : ∃ m : ℕ, f s = (m : OnePoint ℕ) ∧ x.1 m s = j
          · rw [if_pos hex] at h
            refine ⟨h, ?_⟩
            obtain ⟨m, hm, hx⟩ := hex
            have hm' : m = n := OnePoint.coe_eq_coe.mp (hm.symm.trans h)
            rwa [hm'] at hx
          · rw [if_neg hex] at h
            exact absurd h.symm (OnePoint.coe_ne_infty n)
        · rintro ⟨hf, hx⟩
          rw [if_pos ⟨n, hf, hx⟩]
          exact hf
      rw [hfib]
      exact (Work.ATOM.isClopen_singleton_some n).preimage
        (ConcreteCategory.hom f).continuous |>.inter
          (isClopen_discrete {j} |>.preimage (x.1 n).continuous)⟩

/-- The defining property of `gAt`: `gAt S x f j s = m` (for `m : ℕ`) holds exactly when
`f s = m` and `x_m(s) = j`. -/
lemma gAt_apply_eq_coe (S : LightProfinite.{0}) (x : ↥(boundedSeq.obj.obj (op S)))
    (f : S ⟶ (ℕ∪{∞})) (j : ℤ) (m : ℕ) (s : ↥S) :
    gAt S x f j s = (m : OnePoint ℕ) ↔ f s = (m : OnePoint ℕ) ∧ x.1 m s = j := by
  classical
  show (if ∃ m : ℕ, f s = (m : OnePoint ℕ) ∧ x.1 m s = j then f s else (∞ : OnePoint ℕ))
      = (m : OnePoint ℕ) ↔ _
  constructor
  · intro h
    by_cases hex : ∃ m : ℕ, f s = (m : OnePoint ℕ) ∧ x.1 m s = j
    · rw [if_pos hex] at h
      refine ⟨h, ?_⟩
      obtain ⟨m', hm', hx⟩ := hex
      have hm'' : m' = m := OnePoint.coe_eq_coe.mp (hm'.symm.trans h)
      rwa [hm''] at hx
    · rw [if_neg hex] at h
      exact absurd h.symm (OnePoint.coe_ne_infty m)
  · rintro ⟨hf, hx⟩
    rw [if_pos ⟨m, hf, hx⟩]
    exact hf

/-- `deltaElem` viewed as an element of `∏^bnd ℤ(ℕ∪{∞})`. -/
noncomputable def deltaElemM : ↥(boundedSeq.obj.obj (op (ℕ∪{∞}))) := deltaElem

/-- The element `E_{gAt S x f j}` of `∏^bnd ℤ(S)` (whose `m`-th component is
`s ↦ [gAt S x f j s = m]`), as an element of the submodule `boundedSeqSet S`; the explicit
`show`-ascription keeps all later coercions at the level of the submodule. -/
noncomputable def gAtElem (S : LightProfinite.{0}) (x : ↥(boundedSeq.obj.obj (op S)))
    (f : S ⟶ (ℕ∪{∞})) (j : ℤ) : ↥(boundedSeqSet S) :=
  show ↥(boundedSeqSet S) from boundedSeq.obj.map (gAt S x f j).op deltaElemM

/-- The value of a pullback of a bounded family along `g : T ⟶ S` is the value of the original
family at `g t`. -/
lemma boundedSeq_map_apply {S T : LightProfinite.{0}} (g : T ⟶ S)
    (a : ↥(boundedSeq.obj.obj (op S))) (m : ℕ) (t : ↥T) :
    (boundedSeq.obj.map g.op a).1 m t = (a.1 m) (g t) := rfl

/-- The `m`-th component of `gAtElem S x f j` at the point `s` is `[gAt S x f j s = m]`. -/
lemma gAtElem_apply (S : LightProfinite.{0}) (x : ↥(boundedSeq.obj.obj (op S)))
    (f : S ⟶ (ℕ∪{∞})) (j : ℤ) (m : ℕ) (s : ↥S) :
    ((gAtElem S x f j).1 m : C(↥S.toTop, ℤ)) s
      = if gAt S x f j s = (m : OnePoint ℕ) then (1 : ℤ) else 0 := by
  show (boundedSeq.obj.map (gAt S x f j).op deltaElemM).1 m s = _
  rw [boundedSeq_map_apply]
  exact deltaFun_eq m (gAt S x f j s)

/-- The defining property of `coordTimesDeltaAt`, pointwise. -/
@[simp] theorem coordTimesDeltaAt_apply (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (op S))) (f : S ⟶ (ℕ∪{∞})) (m : ℕ) (s : ↥S.toTop) :
    (coordTimesDeltaAt S x f).1 m s = x.1 m s * deltaFun m (f s) := rfl

/-- A finite sum of `j·[y = j]` over `Icc (-N) N` equals `y·c`, provided `|y| ≤ N`. -/
lemma sum_ite_mul_Icc_mem (N y c : ℤ) (hy : |y| ≤ N) :
    (∑ j ∈ Finset.Icc (-N) N, j * (if y = j then c else 0)) = y * c := by
  have h : ∀ j : ℤ, j * (if y = j then c else 0) = (if j = y then j * c else 0) := by
    intro j
    by_cases hij : y = j
    · subst hij; simp
    · rw [if_neg hij, if_neg (Ne.symm hij), mul_zero]
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_ite_eq',
    if_pos (Finset.mem_Icc.mpr (abs_le.mp hy))]

/-- **The key pointwise computation.**  If `N` bounds the family `x`, then for every `m` and `s`
the sum `∑_j j·[gAt S x f j s = m]` equals `x_m(s)·[f s = m]`: when `f s = m` the only non-zero
term is the one with `j = x_m(s)` (which occurs in the summation range by the bound), and when
`f s ≠ m` all terms vanish. -/
lemma sum_gAt_mul (S : LightProfinite.{0}) (x : ↥(boundedSeq.obj.obj (op S)))
    (f : S ⟶ (ℕ∪{∞})) (N : ℤ) (hN : ∀ n s, |x.1 n s| ≤ N) (m : ℕ) (s : ↥S) :
    (∑ j ∈ Finset.Icc (-N) N,
        j * (if gAt S x f j s = (m : OnePoint ℕ) then (1 : ℤ) else 0))
      = x.1 m s * (if f s = (m : OnePoint ℕ) then (1 : ℤ) else 0) := by
  classical
  by_cases hf : f s = (m : OnePoint ℕ)
  · have hterm : ∀ j : ℤ, (if gAt S x f j s = (m : OnePoint ℕ) then (1 : ℤ) else 0)
        = (if x.1 m s = j then (1 : ℤ) else 0) := by
      intro j
      have hiff : gAt S x f j s = (m : OnePoint ℕ) ↔ x.1 m s = j := by
        rw [gAt_apply_eq_coe]
        exact ⟨fun h => h.2, fun h => ⟨hf, h⟩⟩
      by_cases h : x.1 m s = j
      · rw [if_pos (hiff.mpr h), if_pos h]
      · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
    rw [Finset.sum_congr rfl (fun j _ => by rw [hterm j]),
      sum_ite_mul_Icc_mem N (x.1 m s) 1 (hN m s), mul_one, hf, if_pos rfl, mul_one]
  · have hterm : ∀ j : ℤ, (if gAt S x f j s = (m : OnePoint ℕ) then (1 : ℤ) else 0) = 0 := by
      intro j
      rw [if_neg]
      intro h
      rw [gAt_apply_eq_coe] at h
      exact hf h.1
    rw [Finset.sum_congr rfl (fun j _ => by rw [hterm j, mul_zero]), Finset.sum_const_zero,
      if_neg hf, mul_zero]

/-- **The finite ℤ-linear combination representing `coordTimesDeltaAt S x f`**: the section
`∑_{j ∈ Icc (-N) N} j·E_{gAt S x f j}` of `∏^bnd ℤ` over `S` is `coordTimesDeltaAt S x f`. -/
lemma sum_gAt_eq (S : LightProfinite.{0}) (x : ↥(boundedSeq.obj.obj (op S)))
    (f : S ⟶ (ℕ∪{∞})) (N : ℤ) (hN : ∀ n s, |x.1 n s| ≤ N) :
    (∑ j ∈ Finset.Icc (-N) N, j • gAtElem S x f j)
      = (show ↥(boundedSeqSet S) from coordTimesDeltaAt S x f) := by
  refine Subtype.ext ?_
  funext m
  apply ContinuousMap.ext
  intro s
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul, gAtElem_apply]
  rw [sum_gAt_mul S x f N hN m s, coordTimesDeltaAt_apply, deltaFun_eq]

/-- `freeHomEquiv` as an additive homomorphism. -/
noncomputable def freeHomEquivAddMonoidHom (S : LightProfinite) (M : LightCondAb) :
    ((free ℤ).obj S.toCondensed ⟶ M) →+ ↥(M.obj.obj (op S)) where
  toFun := freeHomEquiv S M
  map_zero' := freeHomEquiv_zero S M
  map_add' := freeHomEquiv_add S M

/-- `freeHomEquiv` commutes with finite sums. -/
lemma freeHomEquiv_mapSum {ι : Type*} (S : LightProfinite) (M : LightCondAb) (s : Finset ι)
    (F : ι → ((free ℤ).obj S.toCondensed ⟶ M)) :
    freeHomEquiv S M (∑ i ∈ s, F i) = ∑ i ∈ s, freeHomEquiv S M (F i) :=
  map_sum (freeHomEquivAddMonoidHom S M) F s

/-- `freeHomEquiv` commutes with ℤ-multiples. -/
lemma freeHomEquiv_mapZsmul (S : LightProfinite) (M : LightCondAb) (c : ℤ)
    (F : (free ℤ).obj S.toCondensed ⟶ M) :
    freeHomEquiv S M (c • F) = c • (freeHomEquiv S M F) :=
  map_zsmul (freeHomEquivAddMonoidHom S M) c F

/-- `freeHomEquiv` sends the generator `[gAt S x f j]` to `gAtElem S x f j`. -/
lemma freeHomEquiv_zmap_gAt (S : LightProfinite.{0}) (x : ↥(boundedSeq.obj.obj (op S)))
    (f : S ⟶ (ℕ∪{∞})) (j : ℤ) :
    freeHomEquiv S boundedSeq (Work.ATOM.zmap (gAt S x f j) ≫
        (freeHomEquiv (ℕ∪{∞}) boundedSeq).symm deltaElem)
      = gAtElem S x f j := by
  rw [freeHomEquiv_naturality (gAt S x f j) boundedSeq
    ((freeHomEquiv (ℕ∪{∞}) boundedSeq).symm deltaElem), Equiv.apply_symm_apply]
  simp only [gAtElem, deltaElemM]

/-- **The element `coordTimesDeltaAt S x f` lies in the image of `cBounded`.**  Here
`coordTimesDeltaAt S x f` is the element of `∏^bnd ℤ` over `S` whose `m`-th component is
`s ↦ x_m(s)·[f s = m]`, for a continuous `f : S ⟶ ℕ∪{∞}` (for `f = const k` this is
`coordTimesDelta S x k`, the `const f` case is separately requested and is known true).

Equivalently, in the description `im(cBounded(S)) = ` the ℤ-span of the elements
`E_g := (m ↦ 1_{g⁻¹(m)}) ∈ ∏^bnd ℤ(S)` (`g : S ⟶ ℕ∪∞` continuous): the question is whether `y`
is a **finite** ℤ-linear combination of such `E_g`.

NOTE TO THE PROVER (this is a deliberately delicate statement, and a *negative* answer with a
precise argument is a fully acceptable outcome — use `declare_false` with the counterexample):
two independent reviewers disagreed about it.  The candidate counterexample is `S = ℕ∪{∞}`,
`f = 𝟙`, `x_m = [m even]` (the element `Work.ANALYTIC.evenOddElem`): then `y` has `m`-th component
`k ↦ [m even]·[k = m]`.  Relevant known facts: `{k : k ≤ m}` is clopen (this is what makes the
truncation data legitimate), while `{k : k < ∞} = ℕ` is only open; a set `g⁻¹(ℕ)` (`g` continuous)
is always *open*, and up to the relation `Σ_{j: g_j(s) ≠ ∞} a_j = Σ_m y_m(s)` the membership forces
`x_{f(s)}(s)·[f(s) ≠ ∞] = Σ_{j : g_j(s) ≠ ∞} a_j` pointwise. -/
theorem coordTimesDeltaAt_mem_range (S : LightProfinite.{0})
    (x : ↥(Work.ANALYTIC.boundedSeq.obj.obj (Opposite.op S)))
    (f : S ⟶ LightProfinite.of (OnePoint ℕ)) :
    ∃ p : ↥(LightCondensed.P.obj.obj (Opposite.op S)),
      Work.ANALYTIC.cBounded.hom.app (Opposite.op S) p =
        Work.ANALYTIC.coordTimesDeltaAt S x f := by
  classical
  obtain ⟨N, hN⟩ := x.2
  refine ⟨freeHomEquiv S LightCondensed.P
    (∑ j ∈ Finset.Icc (-N) N,
      j • (Work.ATOM.zmap (gAt S x f j) ≫ LightCondensed.P_proj)), ?_⟩
  have hnat := freeHomEquiv_naturality_target S (cBounded : LightCondensed.P ⟶ boundedSeq)
    (∑ j ∈ Finset.Icc (-N) N,
      j • (Work.ATOM.zmap (gAt S x f j) ≫ LightCondensed.P_proj))
  rw [← hnat]
  have hcomp : (∑ j ∈ Finset.Icc (-N) N,
        j • (Work.ATOM.zmap (gAt S x f j) ≫ LightCondensed.P_proj)) ≫ cBounded
      = ∑ j ∈ Finset.Icc (-N) N, j • (Work.ATOM.zmap (gAt S x f j) ≫
          (freeHomEquiv (ℕ∪{∞}) boundedSeq).symm deltaElem) := by
    rw [Preadditive.sum_comp]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Linear.smul_comp, Category.assoc, P_proj_cBounded]
  rw [hcomp, freeHomEquiv_mapSum]
  have hsum : (∑ j ∈ Finset.Icc (-N) N, freeHomEquiv S boundedSeq
        (j • (Work.ATOM.zmap (gAt S x f j) ≫
          (freeHomEquiv (ℕ∪{∞}) boundedSeq).symm deltaElem)))
      = (∑ j ∈ Finset.Icc (-N) N, j • gAtElem S x f j) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [freeHomEquiv_mapZsmul, freeHomEquiv_zmap_gAt]
  rw [hsum]
  exact sum_gAt_eq S x f N hN

end Work.ANALYTIC
