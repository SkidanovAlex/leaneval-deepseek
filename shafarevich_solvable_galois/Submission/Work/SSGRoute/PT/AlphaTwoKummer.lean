import Mathlib
import Submission.Work.SSGRoute.PT.alphaTwo_evalHom
import Submission.Work.AbsoluteKummer.Functoriality
import Submission.Work.AbsoluteKummer.SES.deltaH2_exact
import Submission.Work.SSGRoute.range_mapH2_eq_ker_mapH2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer base case of the `α²`-pairing

This module begins the proof of the *base case* of Milne, *Arithmetic Duality Theorems*, Theorem
I.1.8 in the coefficient model of `Submission/Work/SSGRoute/PT/AlphaPairing.lean`.

Theorem 1.8 is proved by dévissage over short exact sequences of coefficient modules, and the
induction is started by the **trivial-action** case: if an open subgroup `U` acts trivially on a
finite module `N` of exponent `p`, then `α^r(U, N)` is an isomorphism for every `r ≥ 2`.  In the
coefficient model this reads

  `H²(U, Hom_ℤ(N, C)) ≅ Hom(N, H²(U, C))`   (`C` the divisible class module),

and for `N = ℤ/p` with trivial action it is the Kummer computation `H²(U, C[p]) ≅ H²(U, C)[p]`,
which is a consequence of Hilbert 90 (`H¹(U, C) = 0`) and `cd_p(U) ≤ 2`.

## What is here

* `TrivMod G p` — `ℤ/p` with the trivial `G`-action, and `evalOne`, the evaluation at the
  generator `1` (the coefficient map that `α²` restricts to on the generator, by
  `alphaTwo_evalHom`), together with its equivariance;
* `nsmulHom p C` — the coefficient map `c ↦ p • c` on an additive group;
* `mapH2_nsmulHom` — `mapH2` of the multiplication-by-`p` map **is** multiplication by `p` on
  `H²` (the computation that identifies `H²(G, C) → H²(G, C)` in the Kummer sequence);
* `range_mapH2_eq_ker_nsmul` — consequently, for a short exact sequence
  `0 → M → C →^{p} C → 0` of coefficient modules, the range of `H²(M) → H²(C)` is exactly the
  `p`-torsion of `H²(G, C)`: **this is the Kummer identification `H²(G, C[p]) ≅ H²(G, C)[p]`;
* `ker_mapH2_eq_bot_of_subsingleton` — the same map is injective as soon as `H¹(G, C) = 0`
  (Hilbert 90), being `ker = range(δ²)` with `δ² = 0`.

## Remaining steps (milestone for the next session)

* the isomorphism `ConjHom (TrivMod G p) C ≅ C[p]`, `f ↦ f 1` (an additive hom out of `ℤ/p` is
  determined by its value at `1`, and conversely every `c` with `p • c = 0` defines one via
  `ZMod.lift`), together with its equivariance (the file `AlphaPairing.lean` already supplies the
  conjugation action needed to state it).  **Warning**: `TrivMod G p` is a plain `def`, so it does
  not unfold at the transparency level used by `rw`; state such equalities at type `ZMod p` (or use
  `show`/`change`) and only then transport along the (definitional) identification.
* combine `alphaTwo_evalHom` with the two lemmas above to obtain that `α²(G, ℤ/p)` is bijective
  under Hilbert 90 and `cd_p(G) ≤ 2`;
* the module-dévissage for trivial `N` (reduce to `ℤ/p` over a short exact sequence of *trivial*
  modules, where both the coefficient sequence and the sequence `Hom(N', H²) → Hom(N, H²) →
  Hom(N'', H²) → 0` are exact);
* Milne's dévissage (`N ↪ Coind^G_U N`) reducing the general finite `N` to the trivial case, which
  needs Frobenius reciprocity `Hom_ℤ(Coind^G_U N, C) ≅ Coind^G_U Hom_ℤ(N, C)` and Shapiro.

## Milne's dévissage at `r = 2` (worked out; the assembly that remains)

Write `α^r(N) : Ext^r_G(N,C) → H^{2-r}(G,N)^∨` and let `0 → M →ᵢ M* →^{π} M₁ → 0` be the
standard dévissage sequence with `M* = Coind^G_U M` and `M^U = M` (so `H^j(G, M*) = H^j(U,M)` and
`Ext^r_G(M*,C) = Ext^r_U(M,C)` by Shapiro).  The *correctly aligned* five-lemma diagram is

  `Ext^r_G(M₁,C) → Ext^r_U(M,C) → Ext^r_G(M,C) →^{δ} Ext^{r+1}_G(M₁,C) → Ext^{r+1}_U(M,C)`
  `     ↓α^r(G,M₁)      ↓α^r(U,M)      ↓α^r(G,M)         ↓α^{r+1}(G,M₁)        ↓α^{r+1}(U,M)`
  `H^{2-r}(G,M₁)^∨ → H^{2-r}(U,M)^∨ → H^{2-r}(G,M)^∨ → H^{1-r}(G,M₁)^∨ → H^{1-r}(U,M)^∨`

(the bottom row is the *dualised* long exact sequence in the first variable; note that the top row
starts with `Ext^r_G(M₁,C)`, not with `Ext^r_U(M,C)` as one might guess).  Both rows are exact and
the squares commute (`alphaTwo_naturality` for the first two, and the cup-product/connecting-map
compatibility for the third).

Since `cd_p(G_{k_v}) ≤ 2`, *everything* in degree `≥ 3` vanishes, so the `r ≥ 3` cases are trivially
isomorphisms and the induction is only two steps:

1. **surjectivity**: with `a₂ = α²(U,M)` an isomorphism (the base case!), `a₄ = α²(G,M₁)` a
   surjection onto `0`, and `a₅ = α³(U,M)` injective, the five lemma gives that `a₃ = α²(G,M)` is
   *surjective*, for every finite `M`;
2. **injectivity**: apply the five lemma again to the *same* diagram, now using that
   `a₁ = α²(G,M₁)` is surjective by step 1, `a₂` bijective (base case), `a₄` bijective, `a₅`
   injective: `a₃ = α²(G,M)` is an isomorphism.

This is exactly Milne's text ("the five-lemma shows that `α³(G,M)` is surjective.  Since this holds
for all `M`, `α³(G,M₁)` is also surjective, and now the five-lemma shows that `α³(G,M)` is an
isomorphism.  The same argument shows that `α²(G,M)` is an isomorphism."), with the `r = 3` step
vacuous because of `cd_p ≤ 2`.

Two remarks that save work:

* the **trivial-action base case for arbitrary finite `M` of exponent `p`** reduces to the case
  `M = ℤ/p` by a *module* dévissage over `0 → M' → M → M'' → 0` with `M`, `M'`, `M''` trivial of
  exponent `p` (all are `𝔽_p`-vector spaces, hence `M''` is free and `Hom(M'',-)` is exact, so the
  target row `Hom(M'',H²) → Hom(M,H²) → Hom(M',H²) → 0` is exact as well); the source row is exact
  by `Work.SSGRoute.range_mapH2_eq_ker_mapH2` plus `H³ = 0`.  This is why the *size* of the
  trivial module does not force a product decomposition of `H²`;
* the target's `invariant map` is **not** needed for the dévissage: only `H¹(U,C) = 0`
  (Hilbert 90, proved here as `Work.SSGRoute.PT.hilbert90_H1_eq_zero_openSubgroup`), `H³ = 0`
  (`cd_p ≤ 2`, a hypothesis in this workspace), Shapiro for `Coind`, and Frobenius reciprocity.
  `H²(G, C) ≅ ℚ/ℤ` (the local Brauer group) is needed *only* at the very end, to turn the `α²`
  isomorphism `H²(G, Hom(N,C)) ≅ Hom(N^G, H²(G,C))` into the dimension count against `ℚ/ℤ`.
-/

open Classical

namespace Work.SSGRoute.PT

noncomputable section

universe u v w

/-! ## `ℤ/p` with the trivial `G`-action -/

/-- `ZMod p` with the trivial `G`-action. -/
def TrivMod (G : Type u) (p : ℕ) : Type := ZMod p

namespace TrivMod

instance instAddCommGroup (G : Type u) (p : ℕ) : AddCommGroup (TrivMod G p) :=
  inferInstanceAs (AddCommGroup (ZMod p))

instance instOne (G : Type u) (p : ℕ) : One (TrivMod G p) :=
  inferInstanceAs (One (ZMod p))

instance instNatCast (G : Type u) (p : ℕ) : NatCast (TrivMod G p) :=
  inferInstanceAs (NatCast (ZMod p))

instance instIntCast (G : Type u) (p : ℕ) : IntCast (TrivMod G p) :=
  inferInstanceAs (IntCast (ZMod p))

instance instSMul (G : Type u) (p : ℕ) : SMul G (TrivMod G p) := ⟨fun _ x => x⟩

/-- `TrivMod G p` is a ring, so that instance search resolves the arithmetic *at* `TrivMod` (a
plain `def`, which search does not unfold) instead of silently falling back to `ZMod p`. -/
instance instCommRing (G : Type u) (p : ℕ) [NeZero p] : CommRing (TrivMod G p) :=
  inferInstanceAs (CommRing (ZMod p))

instance instCharP (G : Type u) (p : ℕ) [NeZero p] : CharP (TrivMod G p) p :=
  inferInstanceAs (CharP (ZMod p) p)

instance instFintype (G : Type u) (p : ℕ) [NeZero p] : Fintype (TrivMod G p) :=
  inferInstanceAs (Fintype (ZMod p))

instance instDecidableEq (G : Type u) (p : ℕ) [NeZero p] : DecidableEq (TrivMod G p) :=
  inferInstanceAs (DecidableEq (ZMod p))

instance instDistribMulAction (G : Type u) [Group G] (p : ℕ) :
    DistribMulAction G (TrivMod G p) where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

@[simp] theorem smul_eq (G : Type u) [Group G] (p : ℕ) (g : G) (x : TrivMod G p) :
    g • x = x := rfl

end TrivMod

/-! ## An additive hom out of `ℤ/p` is determined by its value at `1` -/

/-- Evaluation at the generator `1` of `ℤ/p`: this is the coefficient map `Hom_ℤ(ℤ/p, C) → C`
that `α²` restricts to on the generator. -/
def evalOne (G : Type u) [Group G] (p : ℕ) (C : Type v) [AddCommGroup C]
    [DistribMulAction G C] : ConjHom (TrivMod G p) C →+ C :=
  ConjHom.evalHom (1 : TrivMod G p)

@[simp] theorem evalOne_apply {G : Type u} [Group G] (p : ℕ) {C : Type v} [AddCommGroup C]
    [DistribMulAction G C] (f : ConjHom (TrivMod G p) C) : evalOne G p C f = f 1 := rfl

/-- Evaluation at `1` is `G`-equivariant (the action on `ℤ/p` being trivial). -/
theorem evalOne_equivariant (G : Type u) [Group G] (p : ℕ) (C : Type v) [AddCommGroup C]
    [DistribMulAction G C] : Work.GroupCohomology.IsEquivariant G (evalOne G p C) := by
  intro g f
  show ((g • f) 1 : C) = g • (f 1)
  rw [ConjHom.smul_apply, TrivMod.smul_eq]

/-! ## Multiplication by `p` as a coefficient map -/

/-- The coefficient map `c ↦ p • c`. -/
def nsmulHom (p : ℕ) (C : Type v) [AddCommGroup C] : C →+ C :=
  p • AddMonoidHom.id C

@[simp] theorem nsmulHom_apply (p : ℕ) {C : Type v} [AddCommGroup C] (c : C) :
    nsmulHom p C c = p • c := by
  simp [nsmulHom]

/-- **`mapH2` of multiplication by `p` is multiplication by `p` on `H²`.**  This is the
computation that identifies the second map of the coefficient Kummer sequence after applying
`H²`. -/
theorem mapH2_eq_nsmul {G : Type u} [TopologicalSpace G] [Group G] (p : ℕ) {C : Type v}
    [AddCommGroup C] [DistribMulAction G C] {M : Type v} [AddCommGroup M] [DistribMulAction G M]
    (S : Work.AbsoluteKummer.ShortExactSeq G M C C) (hSπ : ∀ c : C, S.pi c = p • c)
    (y : Work.AbsoluteKummer.H2 G C) :
    Work.AbsoluteKummer.mapH2 S.pi S.pi_equivariant y = p • y := by
  refine Work.AbsoluteKummer.SES.H2_induction_on y
    (C := fun z => Work.AbsoluteKummer.mapH2 S.pi S.pi_equivariant z = p • z) ?_
  intro c
  rw [Work.AbsoluteKummer.mapH2_H2π]
  have hmap : Work.AbsoluteKummer.mapZ2 S.pi S.pi_equivariant c = p • c := by
    refine Subtype.ext (funext (fun q => ?_))
    simp [Work.AbsoluteKummer.mapZ2_apply, hSπ]
  rw [hmap, map_nsmul]

/-- **The Kummer identification**: for a short exact sequence of coefficient modules
`0 → M → C →^{p} C → 0`, the image of `H²(G,M) → H²(G,C)` is the `p`-torsion of `H²(G,C)`. -/
theorem range_mapH2_eq_ker_nsmul {G : Type u} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (p : ℕ) {C : Type v} [AddCommGroup C] [DistribMulAction G C]
    {M : Type v} [AddCommGroup M] [DistribMulAction G M]
    (S : Work.AbsoluteKummer.ShortExactSeq G M C C) (hSπ : ∀ c : C, S.pi c = p • c) :
    (Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant).range
      = (nsmulHom p (Work.AbsoluteKummer.H2 G C)).ker := by
  rw [Work.SSGRoute.range_mapH2_eq_ker_mapH2 S]
  ext y
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, nsmulHom_apply, mapH2_eq_nsmul p S hSπ y]

/-- **Hilbert 90 in degree `2`**: for a short exact sequence `0 → M → C →^{p} C → 0` with
`H¹(G,C) = 0`, the map `H²(G,M) → H²(G,C)` is injective (its kernel is the range of the connecting
map `δ²: H¹(G,C) → H²(G,M)`, which vanishes). -/
theorem ker_mapH2_eq_bot_of_subsingleton {G : Type u} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (p : ℕ) {C : Type v} [AddCommGroup C] [DistribMulAction G C]
    {M : Type v} [AddCommGroup M] [DistribMulAction G M]
    (S : Work.AbsoluteKummer.ShortExactSeq G M C C)
    (h1 : Subsingleton (Work.AbsoluteKummer.H1 G C)) :
    (Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant).ker = ⊥ := by
  rw [← Work.AbsoluteKummer.SES.range_deltaH2_eq_ker_mapH2 S]
  have hzero : S.deltaH2 = 0 :=
    AddMonoidHom.ext (fun x => by
      show S.deltaH2 x = 0
      rw [show x = 0 from Subsingleton.elim x 0, S.deltaH2.map_zero])
  rw [hzero, AddMonoidHom.range_zero]

/-! ## The `p`-torsion subgroup, and `ℤ`-powers of a torsion element -/

/-- `n • (-a) = -(n • a)` in an additive group.  (Note: Mathlib's `nsmul_neg` is the *ordered
monoid* statement `n • a < 0 ↔ …`, not this one; hence the derivation through `nsmulHom`.) -/
theorem nsmul_neg' {C : Type v} [AddCommGroup C] (n : ℕ) (a : C) :
    n • (-a) = -(n • a) := by
  simpa [nsmulHom_apply] using (nsmulHom n C).map_neg a

/-- The `p`-torsion subgroup `C[p] = {c | p • c = 0}` of an additive group. -/
def PTor (p : ℕ) (C : Type v) [AddCommGroup C] : AddSubgroup C where
  carrier := {c | p • c = 0}
  zero_mem' := by show p • (0 : C) = 0; simp
  add_mem' := by
    intro a b ha hb
    show p • (a + b) = 0
    rw [nsmul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    show p • (-a) = 0
    rw [nsmul_neg', ha, neg_zero]

@[simp] theorem mem_PTor {p : ℕ} {C : Type v} [AddCommGroup C] {c : C} :
    c ∈ PTor p C ↔ p • c = 0 := Iff.rfl

/-- The additive map `ℤ →+ C`, `k ↦ k • c`; its restrictions are the additive homs out of `ℤ/p`
whose value at `1` is `c`, when `p • c = 0` (via `ZMod.lift`). -/
def zsmulHom {C : Type v} [AddCommGroup C] (c : C) : ℤ →+ C where
  toFun k := k • c
  map_zero' := zero_zsmul c
  map_add' m n := add_zsmul c m n

@[simp] theorem zsmulHom_apply {C : Type v} [AddCommGroup C] (c : C) (k : ℤ) :
    zsmulHom c k = k • c := rfl

/-! ## `Hom_ℤ(ℤ/p, C) ≅ C[p]`, and homs out of `ℤ/p` are determined by their value at `1` -/

/-- The value at `1` of an additive hom `ℤ/p →+ C` is `p`-torsion. -/
theorem mem_PTor_evalOne {G : Type u} [Group G] (p : ℕ) [Fact p.Prime]
    {C : Type v} [AddCommGroup C] [DistribMulAction G C] (f : ConjHom (TrivMod G p) C) :
    f 1 ∈ PTor p C := by
  show p • f.toHom (1 : TrivMod G p) = 0
  rw [← f.toHom.map_nsmul]
  have h0 : p • (1 : TrivMod G p) = 0 := by
    show p • (1 : ZMod p) = 0
    rw [nsmul_eq_mul, mul_one]
    exact CharP.cast_eq_zero (ZMod p) p
  rw [h0, map_zero]

/-- The argument of `ZMod.lift` producing the additive hom `ℤ/p →+ C` whose value at `1` is the
`p`-torsion element `c`, namely `k ↦ k • c` on `ℤ`. -/
def ptorLiftArg (p : ℕ) (C : Type v) [AddCommGroup C] (c : ↥(PTor p C)) :
    {g : ℤ →+ C // g (p : ℤ) = 0} :=
  ⟨zsmulHom (C := C) (c : C), by
    show (p : ℤ) • (c : C) = 0
    have hc : p • (c : C) = 0 := c.2
    simpa using hc⟩

/-- **An additive homomorphism out of `ℤ/p` is determined by its value at `1`.** -/
theorem ConjHom.ext_one {G : Type u} [Group G] (p : ℕ) [Fact p.Prime]
    {C : Type v} [AddCommGroup C] [DistribMulAction G C] {f g : ConjHom (TrivMod G p) C}
    (h : f 1 = g 1) : f = g := by
  have h1 : f.toHom (1 : ZMod p) = g.toHom (1 : ZMod p) := h
  have key : ∀ k : ℤ, f.toHom ((k : ℤ) : ZMod p) = g.toHom ((k : ℤ) : ZMod p) := by
    intro k
    have hk : ((k : ℤ) : ZMod p) = k • (1 : ZMod p) := by rw [zsmul_eq_mul, mul_one]
    calc f.toHom ((k : ℤ) : ZMod p)
        = f.toHom (k • (1 : ZMod p)) := congrArg f.toHom hk
      _ = k • f.toHom (1 : ZMod p) := f.toHom.map_zsmul k 1
      _ = k • g.toHom (1 : ZMod p) := congrArg (fun c => k • c) h1
      _ = g.toHom (k • (1 : ZMod p)) := (g.toHom.map_zsmul k 1).symm
      _ = g.toHom ((k : ℤ) : ZMod p) := congrArg g.toHom hk.symm
  refine ConjHom.ext_apply (fun n => ?_)
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective (n := p) n
  exact key k

/-- **`Hom_ℤ(ℤ/p, C) ≅ C[p]`**, by evaluation at `1`: on `ℤ` the inverse is `k ↦ k • c`, which
descends to `ℤ/p` through `ZMod.lift` because `p • c = 0`. -/
def conjHomTrivModEquivPTor (G : Type u) [Group G] (p : ℕ) [Fact p.Prime]
    (C : Type v) [AddCommGroup C] [DistribMulAction G C] :
    ConjHom (TrivMod G p) C ≃+ ↥(PTor p C) where
  toFun f := ⟨f 1, mem_PTor_evalOne p f⟩
  invFun c := ⟨(ZMod.lift p) (ptorLiftArg p C c)⟩
  left_inv f := ConjHom.ext_one p (by
    show ((ZMod.lift p) (ptorLiftArg p C ⟨f 1, mem_PTor_evalOne p f⟩)) (1 : ZMod p)
      = f 1
    have h := ZMod.lift_coe p (ptorLiftArg p C ⟨f 1, mem_PTor_evalOne p f⟩) 1
    simpa [ptorLiftArg, zsmulHom_apply] using h)
  right_inv c := by
    refine Subtype.ext ?_
    show ((ZMod.lift p) (ptorLiftArg p C c)) (1 : ZMod p) = (c : C)
    have h := ZMod.lift_coe p (ptorLiftArg p C c) 1
    simpa [ptorLiftArg, zsmulHom_apply] using h
  map_add' f g := Subtype.ext (by
    show ((f + g) 1 : C) = (f 1 : C) + (g 1 : C)
    rfl)

/- **The keystone**: `evalOne` *is* the composite of the coefficient identification
`Hom_ℤ(ℤ/p, C) ≅ C[p]` with the coercion `C[p] ⊆ C` — both are the map `f ↦ f 1` followed (or not)
by the inclusion.  Consequently every statement about the map `H²(G, C[p]) → H²(G, C)` phrased in
terms of a short exact sequence `S` with `S.iota = evalOne` will apply to this coefficient
identification (§`range_mapH2_eq_ker_nsmul`, `ker_mapH2_eq_bot_of_subsingleton`). -/
theorem subtype_comp_conjHomTrivModEquivPTor (G : Type u) [Group G] (p : ℕ) [Fact p.Prime]
    (C : Type v) [AddCommGroup C] [DistribMulAction G C] :
    (AddSubgroup.subtype (PTor p C)).comp (conjHomTrivModEquivPTor G p C).toAddMonoidHom
      = evalOne G p C :=
  AddMonoidHom.ext (fun _ => rfl)

/-- `G`-equivariance of the coefficient identification `Hom_ℤ(ℤ/p, C) ≅ C[p]` followed by the
inclusion `C[p] ⊆ C` (which is `evalOne`, by the keystone). -/
theorem subtype_comp_conjHomTrivModEquivPTor_equivariant (G : Type u) [Group G] (p : ℕ)
    [Fact p.Prime] (C : Type v) [AddCommGroup C] [DistribMulAction G C] :
    Work.GroupCohomology.IsEquivariant G
      ((AddSubgroup.subtype (PTor p C)).comp (conjHomTrivModEquivPTor G p C).toAddMonoidHom) := by
  rw [subtype_comp_conjHomTrivModEquivPTor]
  exact evalOne_equivariant G p C
/-- `mapH2` depends only on the coefficient map. -/
theorem mapH2_congr_coeff {G : Type u} [TopologicalSpace G] [Group G] {C : Type v}
    [AddCommGroup C] [DistribMulAction G C] {M : Type v} [AddCommGroup M]
    [DistribMulAction G M] {φ ψ : M →+ C}
    (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hψ : Work.GroupCohomology.IsEquivariant G ψ) (h : φ = ψ) :
    Work.AbsoluteKummer.mapH2 φ hφ = Work.AbsoluteKummer.mapH2 ψ hψ := by
  subst h
  rfl

/-- **The Kummer identification for the coefficient `Hom_ℤ(ℤ/p, C) = C[p]`**: for the coefficient
Kummer sequence `0 → Hom_ℤ(ℤ/p, C) → C →^p C → 0`, the image of `H²(G, Hom_ℤ(ℤ/p, C)) → H²(G,C)`
is exactly the `p`-torsion of `H²(G,C)`. -/
theorem range_mapH2_ptorEquiv {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (p : ℕ) [Fact p.Prime] {C : Type v} [AddCommGroup C] [DistribMulAction G C]
    (S : Work.AbsoluteKummer.ShortExactSeq G (ConjHom (TrivMod G p) C) C C)
    (hSι : S.iota = evalOne G p C) (hSπ : ∀ c : C, S.pi c = p • c) :
    (Work.AbsoluteKummer.mapH2
        ((AddSubgroup.subtype (PTor p C)).comp
          (conjHomTrivModEquivPTor G p C).toAddMonoidHom)
        (subtype_comp_conjHomTrivModEquivPTor_equivariant G p C)).range
      = (nsmulHom p (Work.AbsoluteKummer.H2 G C)).ker := by
  rw [mapH2_congr_coeff _ _ ((subtype_comp_conjHomTrivModEquivPTor G p C).trans hSι.symm)]
  exact range_mapH2_eq_ker_nsmul p S hSπ

/-- **Hilbert 90 for the coefficient `Hom_ℤ(ℤ/p, C) = C[p]`**: if `H¹(G,C) = 0` then the map
`H²(G, Hom_ℤ(ℤ/p, C)) → H²(G,C)` is injective. -/
theorem ker_mapH2_ptorEquiv {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (p : ℕ) [Fact p.Prime] {C : Type v} [AddCommGroup C] [DistribMulAction G C]
    (S : Work.AbsoluteKummer.ShortExactSeq G (ConjHom (TrivMod G p) C) C C)
    (hSι : S.iota = evalOne G p C)
    (h1 : Subsingleton (Work.AbsoluteKummer.H1 G C)) :
    (Work.AbsoluteKummer.mapH2
        ((AddSubgroup.subtype (PTor p C)).comp
          (conjHomTrivModEquivPTor G p C).toAddMonoidHom)
        (subtype_comp_conjHomTrivModEquivPTor_equivariant G p C)).ker = ⊥ := by
  rw [mapH2_congr_coeff _ _ ((subtype_comp_conjHomTrivModEquivPTor G p C).trans hSι.symm)]
  exact ker_mapH2_eq_bot_of_subsingleton p S h1

/-! ## Step (2): evaluation at any element factors through evaluation at `1`

Item (1) of the plan is **already available**: `Work.SSGRoute.PT.alphaTwo_evalHom`
(`Submission/Work/SSGRoute/PT/alphaTwo_evalHom.lean`, imported at the top of this file) states
`alphaTwo x n = mapH2 (ConjHom.evalHom n) _ x` for every `n ∈ invariants G N`.  Specialised to
`N = TrivMod G p` it needs no restatement; what has to be added is the *factorisation* of
`ConjHom.evalHom n` through `evalOne`, below, since `invariants G (TrivMod G p) = ⊤`.
-/

/-- Multiplication by an integer on an additive group, as an endomorphism: `c ↦ k • c`. -/
def zsmulHomEnd (k : ℤ) (C : Type v) [AddCommGroup C] : C →+ C :=
  k • AddMonoidHom.id C

@[simp] theorem zsmulHomEnd_apply (k : ℤ) {C : Type v} [AddCommGroup C] (c : C) :
    zsmulHomEnd k C c = k • c := by
  simp [zsmulHomEnd]

/-- **Evaluation at `↑k` factors through evaluation at `1`**: `f ↦ f ↑k` is `(c ↦ k • c)` after
`evalOne`.  Consequently, for the trivial module `ℤ/p`, every `ConjHom.evalHom n` that occurs in
`alphaTwo_evalHom` is `evalOne` followed by an endomorphism of `C`, so `α²` is completely described
by its value on the generator. -/
theorem evalHom_eq_zsmul_comp_evalOne (G : Type u) [Group G] (p : ℕ) [Fact p.Prime]
    (C : Type v) [AddCommGroup C] [DistribMulAction G C] (k : ℤ) :
    ConjHom.evalHom (C := C) ((k : ℤ) : TrivMod G p)
      = (zsmulHomEnd k C).comp (evalOne G p C) := by
  refine AddMonoidHom.ext (fun f => ?_)
  have hx : ((k : ℤ) : ZMod p) = k • (1 : ZMod p) := by rw [zsmul_eq_mul, mul_one]
  show f.toHom ((k : ℤ) : TrivMod G p) = k • f.toHom (1 : TrivMod G p)
  calc f.toHom ((k : ℤ) : TrivMod G p)
      = f.toHom (k • (1 : ZMod p)) := congrArg f.toHom hx
    _ = k • f.toHom (1 : ZMod p) := f.toHom.map_zsmul k 1
/-- **Composite functoriality of `mapH2`** (the `AddMonoidHom`-level form of
`Work.AbsoluteKummer.mapH2_comp_H2π`): the coefficient map `ψ.comp φ` acts on `H²` as `mapH2 ψ` after
`mapH2 φ`.  (The hinge for describing `alphaTwo`: with `φ = evalOne G p C` and `ψ = zsmulHomEnd k C`
it says `alphaTwo x n` is `k • y`, where `y = mapH2 (evalOne G p C) _ x` is the single class
governed by `range_mapH2_ptorEquiv` / `ker_mapH2_ptorEquiv`.) -/
theorem mapH2_comp {G : Type u} [TopologicalSpace G] [Group G] {M : Type v} {N : Type w}
    {P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (φ : M →+ N) (ψ : N →+ P) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hψ : Work.GroupCohomology.IsEquivariant G ψ)
    (hc : Work.GroupCohomology.IsEquivariant G (ψ.comp φ))
    (x : Work.AbsoluteKummer.H2 G M) :
    Work.AbsoluteKummer.mapH2 (ψ.comp φ) hc x
      = Work.AbsoluteKummer.mapH2 ψ hψ (Work.AbsoluteKummer.mapH2 φ hφ x) := by
  refine Work.AbsoluteKummer.SES.H2_induction_on x
    (C := fun z => Work.AbsoluteKummer.mapH2 (ψ.comp φ) hc z
      = Work.AbsoluteKummer.mapH2 ψ hψ (Work.AbsoluteKummer.mapH2 φ hφ z)) (fun c => ?_)
  exact Work.AbsoluteKummer.mapH2_comp_H2π φ ψ hφ hψ c

/-! ## Scalar identities in `ℤ/p`, stated at `ZMod p`

`TrivMod G p` is a plain `def`, so instance search does not unfold it: `rw [nsmul_eq_mul]` /
`rw [zsmul_eq_mul]` cannot instantiate at type `TrivMod G p`.  These two helpers are therefore stated
at `ZMod p`, which is definitionally the same type, and transported by `simpa`. -/

theorem nsmul_one_zmod (p : ℕ) : p • (1 : ZMod p) = 0 := by
  rw [nsmul_eq_mul, mul_one]
  exact CharP.cast_eq_zero (ZMod p) p

theorem zsmul_one_zmod (p : ℕ) (k : ℤ) : k • (1 : ZMod p) = ((k : ℤ) : ZMod p) := by
  rw [zsmul_eq_mul, mul_one]

end

end Work.SSGRoute.PT
