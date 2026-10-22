import Mathlib
import Submission.Work.ANALYTIC.unprimedSetup
import Submission.Work.ANALYTIC.coordTimesDeltaAt_mem_range

/-!
# The element `qElem` of `P((ℕ∪∞) ⊗ S)` for the map `G` of the unprimed tower

This file collects the definitions used by `Work.ANALYTIC.exists_unprimedTower` beyond
`Submission/Work/ANALYTIC/unprimedSetup.lean`.

The map `G : P ⊗ ∏^bnd ℤ ⟶ P` of REFS/03 §2 is the null family `(k,x) ↦ x_k·e_k`.  Its data is a
section of `P` over `(ℕ∪∞) × S` vanishing on `{∞} × S`, i.e. an element of `P((ℕ∪∞) ⊗ S)`:

* as a function it is `(k,s) ↦ x_k(s)·e_k` (`k` finite, and `0` at `k = ∞`);
* concretely, since `P = ℤ[ℕ∪∞]/ℤ[∞]` with basis `e_k`, it is the finite ℤ-linear combination
  `Σ_{j ∈ [-N,N]} j·[g_j]`, where `N` bounds `x` and `g_j : (ℕ∪∞) × S ⟶ ℕ∪∞` is the continuous
  map `(k,s) ↦ k` if `x_k(s) = j` and `↦ ∞` otherwise (the `fstNS`-instance of
  `Work.ANALYTIC.gAt` of `Submission/Work/ANALYTIC/coordTimesDeltaAt_mem_range.lean`).

The final sum is legitimate because `x` is uniformly bounded.  Its `cBounded`-image is
`coordTimesDeltaAt ((ℕ∪∞) ⊗ S) (pullbackX S x) (fstNS S)`, i.e. the family
`(m,(k,s)) ↦ x_m(s)·[k = m]`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.ANALYTIC

attribute [local instance] Classical.propDecidable

/-- A valid uniform bound for the bounded family `Work.ANALYTIC.pullbackX S x` over
`(ℕ∪∞) ⊗ S` (chosen canonically, so that it may occur in a definition). -/
noncomputable def qBound (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) : ℤ :=
  Classical.choose (pullbackX S x).2

/-- The defining property of `qBound`. -/
theorem qBound_spec (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) (m : ℕ)
    (t : ↥(((ℕ∪{∞}) ⊗ S).toTop)) :
    |(pullbackX S x).1 m t| ≤ qBound S x :=
  Classical.choose_spec (pullbackX S x).2 m t

/-- **The data of the null family `(k,x) ↦ x_k·e_k` of REFS/03 §2**, as an element of
`P((ℕ∪∞) ⊗ S)`: the finite ℤ-linear combination `Σ_{j ∈ [-N,N]} j·[g_j]` with `N = qBound S x`
and `g_j = gAt ((ℕ∪∞)⊗S) (pullbackX S x) (fstNS S) j`.

Its "value at `(k,s)`" is `x_k(s)·e_k` (and `0` at `k = ∞`), and its `cBounded`-image is the
section `(m,(k,s)) ↦ x_m(s)·[k = m]` of `∏^bnd ℤ`. -/
noncomputable def qElem (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    ↥(LightCondensed.P.obj.obj (Opposite.op ((ℕ∪{∞}) ⊗ S))) :=
  freeHomEquiv ((ℕ∪{∞}) ⊗ S) LightCondensed.P
    (∑ j ∈ Finset.Icc (-(qBound S x)) (qBound S x),
      j • (Work.ATOM.zmap (gAt ((ℕ∪{∞}) ⊗ S) (pullbackX S x) (fstNS S) j) ≫
        LightCondensed.P_proj))

/-! ## The statements of the lemmas delegated for the assembly of `G` -/

/-- **`cBounded` sends `qElem S x` to the shift-data of the tower.**  The `cBounded`-image of
`Work.ANALYTIC.qElem S x` is `Work.ANALYTIC.coordTimesDeltaAt ((ℕ∪∞) ⊗ S) (pullbackX S x)
(fstNS S)`, the element of `∏^bnd ℤ((ℕ∪∞) ⊗ S)` whose `m`-th component is
`(k,s) ↦ x_m(s)·[k = m]`.

This is the element-level input for the identity `T ≫ F = G ≫ cBounded`: `G`'s null family
`(k,x) ↦ x_k·e_k` maps under `cBounded` to `(k,x) ↦ x_k·δ_k`, which is exactly the `EA`-data of
`T ≫ F` (`Work.ANALYTIC.EAdataShift`).

ROUTE: this is the statement of `Work.ANALYTIC.coordTimesDeltaAt_mem_range` (module
`Submission.Work.ANALYTIC.coordTimesDeltaAt_mem_range`, with no missing steps) instantiated at the test object
`(ℕ∪∞) ⊗ S`, the family `pullbackX S x` and `f := fstNS S`, with the *explicit* witness
`qElem S x`.  That file's proof of `coordTimesDeltaAt_mem_range` already *is* the proof of this
statement (its witness is literally `qElem S x`); copy that argument, replacing the bound
`obtain ⟨N, hN⟩ := x.2` by `N := qBound S x` and `hN := qBound_spec S x`, and keeping the
instantiation `S ↦ (ℕ∪∞) ⊗ S`, `x ↦ pullbackX S x`, `f ↦ fstNS S`.  The pieces used there are
`getElem`-free: `P_proj_cBounded`, `freeHomEquiv_mapSum`, `freeHomEquiv_zmap_gAt`,
`freeHomEquiv_naturality_target`, `sum_gAt_eq` (with `gAt_apply_eq_coe`, `sum_gAt_mul`,
`sum_ite_mul_Icc_mem`). -/
def QElemCBounded : Prop :=
  ∀ (S : LightProfinite.{0}) (x : ↥(boundedSeq.obj.obj (Opposite.op S))),
    Work.ANALYTIC.cBounded.hom.app (Opposite.op ((ℕ∪{∞}) ⊗ S)) (qElem S x) =
      coordTimesDeltaAt ((ℕ∪{∞}) ⊗ S) (pullbackX S x) (fstNS S)

/-- **Naturality of `qElem` in the test object.**  For `g : T ⟶ S` and `x ∈ ∏^bnd ℤ(S)`, the
restriction of `qElem S x` along `(ℕ∪∞) × g` is `qElem T (x|_T)`.

ROUTE A (self-contained).  `freeHomEquiv` is natural in the source (`freeHomEquiv_naturality`,
module `Submission.Work.ANALYTIC.exists_realNullSeq`) and additive in the morphism
(`freeHomEquiv_sum`), so it suffices to compare the sums term by term.  The only genuine
difficulty is that the two sums range over `Finset.Icc (-(qBound S x)) (qBound S x)` and
`Finset.Icc (-(qBound T (x|_T))) (qBound T (x|_T))`, which are unrelated: a term with
`|j| > sup(|x|)` is *zero*, because then `gAt ((ℕ∪∞)⊗S) (pullbackX S x) (fstNS S) j` is
constantly `∞` (the existential in its definition fails at every point) and `zmap (const ∞)`
is `zmap (toPt _ ≫ LightCondensed.ι)`, which is killed by `P_proj`
(`LightCondensed.P_map ≫ P_proj = 0`; the file `Submission.Work.ANALYTIC.mono_cBounded` has the
packaged form `const_infty_comp`/`const_infty_comp'` if you import it).  So both sums may be
replaced by the sum over the *common* finite set of attained values of `x` (through which the
claim is term-by-term: for an attained `j`, `gAt S x (fstNS S) j ∘ whiskerLeft (ℕ∪∞) g`
`= gAt T (boundedSeq.obj.map g.op x) (fstNS T) j`).  Product-free alternative: use
`Work.ANALYTIC.QElemCBounded` together with the injectivity of the components of `cBounded`
(`Work.ANALYTIC.mono_cBounded`, module `Submission.Work.ANALYTIC.mono_cBounded`) and the
element-level naturality of `coordTimesDeltaAt` (`boundedSeq.obj.map (whiskerLeft (ℕ∪∞) g).op`
of `coordTimesDeltaAt ((ℕ∪∞)⊗S) (pullbackX S x) (fstNS S)` is
`coordTimesDeltaAt ((ℕ∪∞)⊗T) (pullbackX T (x|_T)) (fstNS T)`, a componentwise computation). -/
def QElemNat : Prop :=
  ∀ (T S : LightProfinite.{0}) (g : T ⟶ S)
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))),
    LightCondensed.P.obj.map (MonoidalCategory.whiskerLeft (ℕ∪{∞}) g).op (qElem S x) =
      qElem T (boundedSeq.obj.map g.op x)

/-- **Linearity of `qElem` in `x`**, componentwise on the concrete sections.

ROUTE.  The same two routes as for `QElemNat`.  With `Work.ANALYTIC.QElemCBounded` and the
injectivity of the components of `cBounded` (from `Work.ANALYTIC.mono_cBounded`, module
`Submission.Work.ANALYTIC.mono_cBounded`) both sides reduce to the componentwise identity
`coordTimesDeltaAt S (x+y) f = coordTimesDeltaAt S x f + coordTimesDeltaAt S y f` (and its
`c •` and `0` analogues), which is pointwise linearity of `s ↦ x_m(s)·[f s = m]`
(`coordTimesDeltaAt_apply`, `coe_add_apply`, `coe_smul_apply`, `coe_zero_apply`,
`boundedSeq_map_apply` in `Submission.Work.ANALYTIC.coordTimesDeltaAt_mem_range` /
`coordTimesDelta_mem_range`); the bounds `qBound` are again harmless because the sum is
independent of any valid bound (a term with `|j|` beyond the values of `x` vanishes, since then
`gAt` is constantly `∞` and `zmap (const ∞) ≫ P_proj = 0`). -/
def QElemLinear : Prop :=
  (∀ (S : LightProfinite.{0}) (x y : ↥(boundedSeq.obj.obj (Opposite.op S))),
      qElem S (x + y) = qElem S x + qElem S y) ∧
    (∀ (S : LightProfinite.{0}) (c : ℤ) (x : ↥(boundedSeq.obj.obj (Opposite.op S))),
      qElem S (c • x) = c • qElem S x) ∧
    (∀ (S : LightProfinite.{0}), qElem S (0 : ↥(boundedSeq.obj.obj (Opposite.op S))) = 0)

/-- **Vanishing of `qElem` on the `∞`-slice.**  The restriction of `qElem S x` along
`{∞} × S ⊆ (ℕ∪∞) × S` is zero, i.e. the morphism classified by `qElem S x` kills
`ℤ[{∞} × S]`; this is the hypothesis of `Work.ATOM.Toolkit.PS_desc` which makes that morphism
descend to `P ⊗ ℤ[S]`.  (Follows from `QElemCBounded` and the injectivity of `cBounded`, together
with the fact that the τ-coefficient `[∞ = m]` vanishes.)

ROUTE.  Either (a) `Work.ANALYTIC.QElemCBounded` (module
`Submission.Work.ANALYTIC.qElem_cBounded`) + the injectivity of the components of `cBounded`
(from `Work.ANALYTIC.mono_cBounded`, module `Submission.Work.ANALYTIC.mono_cBounded`), the
element-level computation being that the restriction of
`coordTimesDeltaAt ((ℕ∪∞)⊗S) (pullbackX S x) (fstNS S)` along `whiskerRight ι S` vanishes
componentwise (`fstNS S (∞,s) = ∞`, `deltaFun m ∞ = 0`, see `boundedSeq_map_apply` and
`deltaFun_infty`); or (b) directly: `gAt ((ℕ∪∞)⊗S) (pullbackX S x) (fstNS S) j` is constantly
`∞` after `whiskerRight ι S` (its existential fails at `(∞,s)`), so
`zmap (whiskerRight ι S) ≫ zmap (gAt … j) = zmap (const ∞)` is `zmap (toPt _ ≫ LightCondensed.ι)`
and is killed by `P_proj` (`LightCondensed.P_map ≫ P_proj = 0`), whence every summand — and hence
the whole sum — vanishes (`freeHomEquiv_sum`, `freeHomEquiv_naturality`). -/
def QElemSlice : Prop :=
  ∀ (S : LightProfinite.{0}) (x : ↥(boundedSeq.obj.obj (Opposite.op S))),
    LightCondensed.P.obj.map (MonoidalCategory.whiskerRight LightCondensed.ι S).op
      (qElem S x) = 0

end Work.ANALYTIC

end
