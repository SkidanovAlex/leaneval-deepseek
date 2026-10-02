import Mathlib
import Submission.Work.SignatureBordism.Numbers
import Submission.Work.SignatureBordism.signature_prod
import Submission.Work.SignatureBordism.signature_of_isLagrangian

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The bordism reduction of the dimension-`8` (**and dimension-`4`**) Hirzebruch identity

The dimension-`8` Hirzebruch identity `45 σ = 7 p₂ - p₁²` is *one linear equation* in the three
numbers of a closed oriented smooth `8`-manifold, and each of those three numbers is a bordism
invariant; hence the identity holds for **every** closed oriented smooth `8`-manifold as soon as it
holds on a set of bordism classes which spans `Ω^SO_8 ⊗ ℚ`, namely the classes of `ℂP⁴` and
`ℂP² × ℂP²`, whose numbers are `(σ, p₁², p₂) = (1, 25, 10)` and `(1, 18, 9)`.

This file **formalises exactly that reduction**, with the geometric input isolated as a single
*named* hypothesis:

* `Work.SignatureBordism.hirzebruchEight_of_mem_span` — **the linear algebra**: if the triple of
  numbers of `X` lies in `ℚ-span{(1,25,10), (1,18,9)}` then the identity holds for it.  No
  geometry, no bordism theory: the functional `(σ, p₁², p₂) ↦ 45σ - 7p₂ + p₁²` vanishes on both
  generators, hence on their span.  The two generator checks are discharged here
  (`hirzebruchFunctional8_cp4`, `hirzebruchFunctional8_cp2cp2`).
* `Work.SignatureBordism.NumbersInSpan8 X c p₁ p₂` — the geometric hypothesis, *named*: the
  numbers of `X` lie in that span.  It is the conjunction of (a) bordism invariance of the
  signature and of the two Pontryagin numbers and (b) the generation
  `Ω^SO_8 ⊗ ℚ = ℚ{[ℂP⁴], [ℂP² × ℂP²]}` (Thom's theorem, or surgery down to `3`-connected
  `8`-manifolds).  Neither (a) nor (b) is formalised anywhere in this workspace — Mathlib has no
  bordisms and no manifold orientations, see the README of this directory — so this is the
  *precisely scoped* form in which the remaining input is exposed.
* `Work.SignatureBordism.BordismPresentation8` — the same input in *semantic* form: a rational
  model `B` of `Ω^SO_8 ⊗ ℚ` in which the three numbers are ℚ-linear functionals (this is what
  bordism invariance *means*), together with the two generator classes, their values, the fact that
  they span, and a class carrying the numbers of `X`.  A presentation yields a span membership
  (`mem_span_of_presentation`) and conversely (`presentation_of_mem_span`), so the two forms of the
  hypothesis are equivalent; the presentation form is the one that shows *why* the hypothesis is
  the standard one.
* the same in dimension `4`, where the single generator is `ℂP²` with `(σ, p₁) = (1, 3)`
  (`hirzebruchFour_of_mem_span`, `NumbersInSpan4`, `BordismPresentation4`).

## Main results

* `Work.SignatureBordism.hirzebruchEight_of_mem_span` — the reduction, as a theorem;
* `Work.SignatureBordism.HirzebruchEightManifold_of_numbersInSpan` /
  `Work.SignatureBordism.HirzebruchEight.of_presentation` — the identity for `X` from the single
  named geometric hypothesis;
* `Work.SignatureBordism.mem_span_of_presentation`, `Work.SignatureBordism.presentation_of_mem_span`
  — the two forms of the hypothesis are equivalent;
* `Work.SignatureBordism.hirzebruchFour_of_mem_span`, `Work.SignatureBordism.hirzebruchFour_of_presentation`
  — the dimension-`4` base case in the same form.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Work.SignatureBordism

open Work.Cohomology

noncomputable section

/-! ## The algebraic skeleton of bordism invariance of the signature

Bordism invariance of `σ` is proved by exhibiting a Lagrangian for the middle form of `M ⊔ (-N)`
(the image of the relative cohomology of a bordism `W` from `M` to `N`) and applying three purely
algebraic facts, all of which are proved in this chapter:

* a nondegenerate form with a Lagrangian has signature `0`
  (`Work.SignatureBordism.signature_of_isLagrangian`);
* the signature is additive over orthogonal direct sums (`Work.SignatureBordism.signature_prod`);
* reversing the orientation negates the signature (`Work.SignatureBordism.signature_neg`).

The geometric statements — that the middle form of `∂W` is the orthogonal sum of the middle forms
of its pieces and that it carries the Lagrangian — need a bordism theory, which Mathlib does not
have (see the directory README).  The consequence of the three algebraic facts is recorded here. -/

/-- **Algebraic bordism invariance of the signature.**  If the middle form of the disjoint union of
two closed oriented `2k`-manifolds *with one orientation reversed*, i.e. the orthogonal direct sum
`Q₁ ⊥ (-Q₂)`, has signature `0` — which is what a bordism between them supplies, via the Lagrangian
`Work.SignatureBordism.signature_of_isLagrangian` — then `σ` of the two manifolds agrees. -/
theorem signature_eq_of_signature_prod_neg_eq_zero {𝕜 V W : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
    [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]
    (Q₁ : QuadraticForm 𝕜 V) (Q₂ : QuadraticForm 𝕜 W)
    (h : signature (Q₁.prod (-Q₂)) = 0) : signature Q₁ = signature Q₂ := by
  rw [signature_prod, signature_neg] at h
  linarith

/-- **Bordism invariance of the signature, in the exact form in which a bordism supplies it.**

Let `Q₁`, `Q₂` be the middle intersection forms of two closed oriented `2k`-manifolds `M`, `N` (with
their fundamental classes), so that the middle form of `M ⊔ (-N)` is the orthogonal direct sum
`Q₁ ⊥ (-Q₂)`.  If that form has a **Lagrangian** — a subspace `K` on which the form vanishes and
which is its own orthogonal complement with respect to the polar form — and is nondegenerate, then
`σ(M) = σ(N)`.

This is the *complete* algebraic content of the bordism invariance of the signature.  The geometric
input is exactly the existence of such a `K` for a bordism `W` from `M` to `N`: the long exact
sequence of the pair `(W, ∂W)` exhibits `K = ker(H^k(∂W) → H^{k+1}(W, ∂W)) = range(H^k(W) →
H^k(∂W))` as a Lagrangian of the middle form of `∂W = M ⊔ (-N)`, using Lefschetz duality.
Formalising that requires a bordism theory and Lefschetz duality, neither of which is in Mathlib
(see the directory README); everything after that point is
`Work.SignatureBordism.signature_of_isLagrangian`,
`Work.SignatureBordism.signature_prod` and `Work.SignatureBordism.signature_neg`. -/
theorem signature_eq_of_lagrangian_orthogonal_sum {𝕜 V W : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [Invertible (2 : 𝕜)]
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
    [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]
    (Q₁ : QuadraticForm 𝕜 V) (Q₂ : QuadraticForm 𝕜 W) (K : Submodule 𝕜 (V × W))
    (hK : ∀ x ∈ K, (Q₁.prod (-Q₂)) x = 0)
    (horth : ∀ x : V × W, (∀ y ∈ K, QuadraticMap.associated (Q₁.prod (-Q₂)) x y = 0) ↔ x ∈ K)
    (hrad : ∀ x : V × W, (∀ y : V × W, QuadraticMap.associated (Q₁.prod (-Q₂)) x y = 0) → x = 0) :
    signature Q₁ = signature Q₂ := by
  have h0 : signature (Q₁.prod (-Q₂)) = 0 := signature_of_isLagrangian _ K hK horth hrad
  rw [signature_prod, signature_neg] at h0
  linarith

/-! ## The generators and the Hirzebruch functional -/

/-- The numbers `(σ, p₁², p₂) = (1, 25, 10)` of `ℂP⁴`
(`p(TℂP⁴) = (1+x)⁵`, so `p₁ = 5x`, `p₂ = 10x²`). -/
def cp4Tuple : ℚ × ℚ × ℚ := (1, 25, 10)

/-- The numbers `(σ, p₁², p₂) = (1, 18, 9)` of `ℂP² × ℂP²`. -/
def cp2cp2Tuple : ℚ × ℚ × ℚ := (1, 18, 9)

/-- The numbers `(σ, p₁) = (1, 3)` of `ℂP²` (dimension `4`). -/
def cp2Tuple : ℚ × ℚ := (1, 3)

/-- **The Hirzebruch functional in dimension `8`**: `(σ, p₁², p₂) ↦ 45σ - 7p₂ + p₁²`, as a
`ℚ`-linear map on triples of numbers.  The dimension-`8` Hirzebruch identity says that this
functional vanishes on the numbers of every closed oriented smooth `8`-manifold. -/
def hirzebruchFunctional8 : (ℚ × ℚ × ℚ) →ₗ[ℚ] ℚ where
  toFun v := 45 * v.1 - 7 * v.2.2 + v.2.1
  map_add' := by intro a b; simp only [Prod.fst_add, Prod.snd_add]; ring_nf
  map_smul' := by
    intro a b; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring

/-- **The Hirzebruch functional in dimension `4`**: `(σ, p₁) ↦ p₁ - 3σ`. -/
def hirzebruchFunctional4 : (ℚ × ℚ) →ₗ[ℚ] ℚ where
  toFun v := v.2 - 3 * v.1
  map_add' := by intro a b; simp only [Prod.fst_add, Prod.snd_add]; ring_nf
  map_smul' := by
    intro a b; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem hirzebruchFunctional8_apply (v : ℚ × ℚ × ℚ) :
    hirzebruchFunctional8 v = 45 * v.1 - 7 * v.2.2 + v.2.1 := rfl

@[simp] theorem hirzebruchFunctional4_apply (v : ℚ × ℚ) :
    hirzebruchFunctional4 v = v.2 - 3 * v.1 := rfl

/-- **The generator check for `ℂP⁴`** (discharged here, not a hypothesis). -/
theorem hirzebruchFunctional8_cp4 : hirzebruchFunctional8 cp4Tuple = 0 := by
  simp only [hirzebruchFunctional8_apply, cp4Tuple]
  norm_num

/-- **The generator check for `ℂP² × ℂP²`** (discharged here, not a hypothesis). -/
theorem hirzebruchFunctional8_cp2cp2 : hirzebruchFunctional8 cp2cp2Tuple = 0 := by
  simp only [hirzebruchFunctional8_apply, cp2cp2Tuple]
  norm_num

/-- **The generator check for `ℂP²`** in dimension `4` (discharged here). -/
theorem hirzebruchFunctional4_cp2 : hirzebruchFunctional4 cp2Tuple = 0 := by
  simp only [hirzebruchFunctional4_apply, cp2Tuple]
  norm_num

/-! ## The reduction -/

/-- The functional vanishes on the span of the two generators: a `ℚ`-linear functional vanishing on
a spanning set vanishes everywhere. -/
theorem hirzebruchFunctional8_eq_zero_of_mem_span {v : ℚ × ℚ × ℚ}
    (hv : v ∈ Submodule.span ℚ {cp4Tuple, cp2cp2Tuple}) : hirzebruchFunctional8 v = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
      rcases hx with h | h
      · rw [h]; exact hirzebruchFunctional8_cp4
      · rw [h]; exact hirzebruchFunctional8_cp2cp2
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
  | smul a x hx ihx => rw [map_smul, ihx, smul_zero]

/-- **The dimension-`8` reduction, as a theorem**: if the triple of numbers `(σ, p₁², p₂)` lies in
the rational span of the two generator triples `(1,25,10)`, `(1,18,9)`, then the Hirzebruch identity
holds.

This is the whole arithmetic content of the bordism-theoretic proof of the dimension-`8` signature
theorem: the two generator checks are `hirzebruchFunctional8_cp4` and
`hirzebruchFunctional8_cp2cp2`, and the functional is `ℚ`-linear.  What remains geometric is the
*generation* hypothesis, which the caller supplies (see `NumbersInSpan8`). -/
theorem hirzebruchEight_of_mem_span (σ p₁sq p₂ : ℤ)
    (h : ((σ : ℚ), (p₁sq : ℚ), (p₂ : ℚ)) ∈ Submodule.span ℚ {cp4Tuple, cp2cp2Tuple}) :
    HirzebruchEight σ p₁sq p₂ := by
  have h0 := hirzebruchFunctional8_eq_zero_of_mem_span h
  have h1 : (45 : ℚ) * σ - 7 * p₂ + p₁sq = 0 := by simpa using h0
  have h2 : ((45 : ℤ) * σ - 7 * p₂ + p₁sq : ℚ) = 0 := by push_cast; linarith
  have h3 : (45 : ℤ) * σ - 7 * p₂ + p₁sq = 0 := by exact_mod_cast h2
  unfold HirzebruchEight
  linarith

/-- **The dimension-`4` reduction, as a theorem**: if `(σ, p₁)` lies in the rational span of
`(1, 3)` — the numbers of `ℂP²`, the single generator of `Ω^SO_4 ⊗ ℚ` — then `p₁ = 3σ`. -/
theorem hirzebruchFour_of_mem_span (σ p₁ : ℤ)
    (h : ((σ : ℚ), (p₁ : ℚ)) ∈ Submodule.span ℚ {cp2Tuple}) : HirzebruchFour σ p₁ := by
  rw [Submodule.mem_span_singleton] at h
  obtain ⟨a, ha⟩ := h
  have h1 : (σ : ℚ) = a := by
    have := congrArg Prod.fst ha
    simpa [cp2Tuple] using this.symm
  have h2 : (p₁ : ℚ) = 3 * a := by
    have := congrArg Prod.snd ha
    simpa [cp2Tuple, mul_comm] using this.symm
  have h3 : (p₁ : ℚ) = 3 * (σ : ℚ) := by rw [h2, h1]
  unfold HirzebruchFour
  exact_mod_cast h3

/-- **The span condition is exactly the dimension-`8` identity** (for a triple of integers).  The two
generator triples span the hyperplane `45σ - 7p₂ + p₁² = 0` of `ℚ³`, so `(σ, p₁², p₂)` lies in their
rational span if and only if the Hirzebruch identity holds.

The *forward* direction is `hirzebruchEight_of_mem_span` (the reduction).  The *backward* direction
is the honest statement of what the geometric input is: the span condition is not weaker than the
identity for a *single* manifold, and what makes `NumbersInSpan8` the right named form of the
input is the *route* — the generation statement `Ω^SO_8 ⊗ ℚ = ℚ{[ℂP⁴], [ℂP² × ℂP²]}` (together
with bordism invariance of the three numbers) *implies* it, by the standard proof of the
dimension-`8` signature theorem. -/
theorem mem_span_iff_hirzebruchEight (σ p₁sq p₂ : ℤ) :
    ((σ : ℚ), (p₁sq : ℚ), (p₂ : ℚ)) ∈ Submodule.span ℚ {cp4Tuple, cp2cp2Tuple} ↔
      HirzebruchEight σ p₁sq p₂ := by
  constructor
  · exact hirzebruchEight_of_mem_span σ p₁sq p₂
  · intro h
    unfold HirzebruchEight at h
    have hq : (45 : ℚ) * (σ : ℚ) = 7 * (p₂ : ℚ) - (p₁sq : ℚ) := by exact_mod_cast h
    refine Submodule.mem_span_pair.mpr
      ⟨((p₁sq : ℚ) - 18 * (σ : ℚ)) / 7, (25 * (σ : ℚ) - (p₁sq : ℚ)) / 7, ?_⟩
    simp only [cp4Tuple, cp2cp2Tuple, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_one]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · field_simp; ring
    · field_simp; ring
    · field_simp; linarith

/-! ## The named geometric hypothesis, in span form -/

/-- **The dimension-`8` bordism input for the manifold `X` with classes `p₁`, `p₂`**: the triple of
numbers `(σ(X), p₁(X)², p₂(X))` lies in the rational span of the numbers of the two generators
`ℂP⁴`, `ℂP² × ℂP²` of `Ω^SO_8 ⊗ ℚ`.

This is the *single* geometric hypothesis of the dimension-`8` signature theorem in this chapter:
it is the conjunction of

* bordism invariance of the signature and of the two Pontryagin numbers (so that they are functions
  on bordism classes), and
* the generation `Ω^SO_8 ⊗ ℚ = ℚ{[ℂP⁴], [ℂP² × ℂP²]}` (Thom's theorem, or surgery down to
  `3`-connected `8`-manifolds),

and it is *not* proved here (see `BordismPresentation8` for the semantic form, and this directory's
README for why neither input is available in the present library). -/
def NumbersInSpan8 (X : SSet) (c : (chainC ℤ X).homology 8) (p₁ : (cochainC ℤ X).homology 4)
    (p₂ : (cochainC ℤ X).homology 8) : Prop :=
  ((sigma 4 X c : ℚ), (p₁SqNumber X c p₁ : ℚ), (p₂Number X c p₂ : ℚ)) ∈
    Submodule.span ℚ {cp4Tuple, cp2cp2Tuple}

/-- **The dimension-`8` identity for a manifold, from the single named geometric hypothesis**
`Work.SignatureBordism.NumbersInSpan8`. -/
theorem HirzebruchEightManifold_of_numbersInSpan (X : SSet) (c : (chainC ℤ X).homology 8)
    (p₁ : (cochainC ℤ X).homology 4) (p₂ : (cochainC ℤ X).homology 8)
    (h : NumbersInSpan8 X c p₁ p₂) : HirzebruchEightManifold X c p₁ p₂ :=
  hirzebruchEight_of_mem_span _ _ _ h

/-- **The dimension-`4` bordism input for a manifold `X` with class `p₁`**: `(σ(X), p₁(X))` lies in
the rational span of `(1, 3)`, the numbers of the generator `ℂP²` of `Ω^SO_4 ⊗ ℚ`. -/
def NumbersInSpan4 (X : SSet) (c : (chainC ℤ X).homology 4) (p₁ : (cochainC ℤ X).homology 4) :
    Prop :=
  ((sigma 2 X c : ℚ), (p₁Number X c p₁ : ℚ)) ∈ Submodule.span ℚ {cp2Tuple}

/-- **The dimension-`4` identity for a manifold, from the single named geometric hypothesis**
`Work.SignatureBordism.NumbersInSpan4`. -/
theorem HirzebruchFourManifold_of_numbersInSpan (X : SSet) (c : (chainC ℤ X).homology 4)
    (p₁ : (cochainC ℤ X).homology 4) (h : NumbersInSpan4 X c p₁) :
    HirzebruchFourManifold X c p₁ :=
  hirzebruchFour_of_mem_span _ _ h

/-- **In dimension `4` the span condition is exactly the identity** `p₁ = 3σ`: the analogue of
`Work.SignatureBordism.mem_span_iff_hirzebruchEight`, and the same honest caveat — for a fixed
manifold the named hypothesis of `Work.SignatureBordism.NumbersInSpan4` *is* the conclusion, so it
can only be discharged from the generation `Ω^SO_4 ⊗ ℚ = ℚ{[ℂP²]}` (a theorem of topology). -/
theorem mem_span4_iff_hirzebruchFour (σ p₁ : ℤ) :
    ((σ : ℚ), (p₁ : ℚ)) ∈ Submodule.span ℚ {cp2Tuple} ↔ HirzebruchFour σ p₁ := by
  constructor
  · exact hirzebruchFour_of_mem_span σ p₁
  · intro h
    unfold HirzebruchFour at h
    have h1 : (p₁ : ℚ) = 3 * (σ : ℚ) := by exact_mod_cast h
    refine Submodule.mem_span_singleton.mpr ⟨(σ : ℚ), ?_⟩
    refine Prod.ext ?_ ?_
    · simp [cp2Tuple]
    · simp only [cp2Tuple, Prod.smul_snd, smul_eq_mul]
      linarith

/-! ## The same hypothesis, in bordism-presentation form -/

/-- **A rational bordism presentation of the dimension-`8` numbers of a manifold.**

`B` is a rational model of the oriented bordism group `Ω^SO_8 ⊗ ℚ` (in which the three numbers are
`ℚ`-linear functionals — this is exactly what *bordism invariance* means), `cp4` and `cp2cp2` are
the classes of the two generators with their numbers `(1,25,10)`, `(1,18,9)`, these two classes
span `B`, and `b` is a class whose numbers are those of the manifold in question.

Producing a `BordismPresentation8 σ p₁sq p₂` is therefore precisely the geometric input of the
dimension-`8` signature theorem; it is equivalent to the span form (`mem_span_of_presentation`,
`presentation_of_mem_span`). -/
structure BordismPresentation8 (σ p₁sq p₂ : ℤ) where
  /-- the rational model of `Ω^SO_8 ⊗ ℚ` -/
  B : Type
  [addCommGroup : AddCommGroup B]
  [module : Module ℚ B]
  /-- the signature functional -/
  sig : B →ₗ[ℚ] ℚ
  /-- the `p₁²`-number functional -/
  p1sq : B →ₗ[ℚ] ℚ
  /-- the `p₂`-number functional -/
  p2 : B →ₗ[ℚ] ℚ
  /-- the class of `ℂP⁴` -/
  cp4 : B
  /-- the class of `ℂP² × ℂP²` -/
  cp2cp2 : B
  /-- the numbers of `ℂP⁴` -/
  hcp4 : (sig cp4, p1sq cp4, p2 cp4) = (1, 25, 10)
  /-- the numbers of `ℂP² × ℂP²` -/
  hcp2cp2 : (sig cp2cp2, p1sq cp2cp2, p2 cp2cp2) = (1, 18, 9)
  /-- the two generators span the rational bordism group -/
  spanning : Submodule.span ℚ {cp4, cp2cp2} = ⊤
  /-- the bordism class whose numbers are those of the manifold -/
  b : B
  /-- the numbers of `b` -/
  hb : (sig b, p1sq b, p2 b) = ((σ : ℚ), (p₁sq : ℚ), (p₂ : ℚ))

attribute [instance] BordismPresentation8.addCommGroup BordismPresentation8.module

/-- **A presentation yields a span membership**: the numbers of `b` are in the span of the numbers
of the two generators, because the triple of functionals maps `B` onto the span of the two generator
triples. -/
theorem mem_span_of_presentation {σ p₁sq p₂ : ℤ} (P : BordismPresentation8 σ p₁sq p₂) :
    ((σ : ℚ), (p₁sq : ℚ), (p₂ : ℚ)) ∈ Submodule.span ℚ {cp4Tuple, cp2cp2Tuple} := by
  let β : P.B →ₗ[ℚ] (ℚ × ℚ × ℚ) := P.sig.prod (P.p1sq.prod P.p2)
  have hcp4 : β P.cp4 = cp4Tuple := P.hcp4
  have hcp2cp2 : β P.cp2cp2 = cp2cp2Tuple := P.hcp2cp2
  have hb : β P.b = ((σ : ℚ), (p₁sq : ℚ), (p₂ : ℚ)) := P.hb
  have hmem : P.b ∈ Submodule.span ℚ {P.cp4, P.cp2cp2} := by
    rw [P.spanning]; trivial
  have hmap : Submodule.map β (Submodule.span ℚ {P.cp4, P.cp2cp2}) =
      Submodule.span ℚ {cp4Tuple, cp2cp2Tuple} := by
    rw [Submodule.map_span]
    simp only [Set.image_pair, hcp4, hcp2cp2]
  rw [← hb, ← hmap]
  exact Submodule.mem_map_of_mem hmem

/-- **The dimension-`8` identity from a bordism presentation.**  This is the cleanest statement of
the reduction: *given* a rational bordism presentation of the numbers (bordism invariance plus
generation), the identity holds — with no further input. -/
theorem HirzebruchEight.of_presentation {σ p₁sq p₂ : ℤ} (P : BordismPresentation8 σ p₁sq p₂) :
    HirzebruchEight σ p₁sq p₂ :=
  hirzebruchEight_of_mem_span σ p₁sq p₂ (mem_span_of_presentation P)

/-- **A span membership yields a presentation**: take `B = ℚ²`, the numbers being the coordinates
of `a · (1,25,10) + b · (1,18,9)`.  So the two forms of the geometric hypothesis are
equivalent. -/
theorem presentation_of_mem_span {σ p₁sq p₂ : ℤ}
    (h : ((σ : ℚ), (p₁sq : ℚ), (p₂ : ℚ)) ∈ Submodule.span ℚ {cp4Tuple, cp2cp2Tuple}) :
    Nonempty (BordismPresentation8 σ p₁sq p₂) := by
  obtain ⟨a, c, hac⟩ := Submodule.mem_span_pair.mp h
  let L : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ × ℚ) :=
    { toFun := fun v : ℚ × ℚ => v.1 • cp4Tuple + v.2 • cp2cp2Tuple
      map_add' := by
        intro x y
        simp only [Prod.fst_add, Prod.snd_add, add_smul]
        abel
      map_smul' := by
        intro r x
        simp only [Prod.smul_fst, Prod.smul_snd, smul_add, smul_eq_mul, RingHom.id_apply]
        rw [smul_smul, smul_smul] }
  have hL : ∀ v : ℚ × ℚ, L v = v.1 • cp4Tuple + v.2 • cp2cp2Tuple := fun _ => rfl
  let sigL : (ℚ × ℚ) →ₗ[ℚ] ℚ := (LinearMap.fst ℚ ℚ (ℚ × ℚ)).comp L
  let p1sqL : (ℚ × ℚ) →ₗ[ℚ] ℚ :=
    (LinearMap.fst ℚ ℚ ℚ).comp ((LinearMap.snd ℚ ℚ (ℚ × ℚ)).comp L)
  let p2L : (ℚ × ℚ) →ₗ[ℚ] ℚ :=
    (LinearMap.snd ℚ ℚ ℚ).comp ((LinearMap.snd ℚ ℚ (ℚ × ℚ)).comp L)
  have hβ : ∀ v : ℚ × ℚ, (sigL v, p1sqL v, p2L v) = v.1 • cp4Tuple + v.2 • cp2cp2Tuple := by
    intro v
    simp only [sigL, p1sqL, p2L, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply]
    rw [hL v]
  refine ⟨{
    B := ℚ × ℚ
    sig := sigL
    p1sq := p1sqL
    p2 := p2L
    cp4 := (1, 0)
    cp2cp2 := (0, 1)
    hcp4 := by rw [hβ (1, 0)]; norm_num [cp4Tuple, cp2cp2Tuple]
    hcp2cp2 := by rw [hβ (0, 1)]; norm_num [cp4Tuple, cp2cp2Tuple]
    spanning := by
      rw [Submodule.eq_top_iff']
      intro v
      rw [Submodule.mem_span_pair]
      exact ⟨v.1, v.2, by cases v with | mk x y => simp⟩
    b := (a, c)
    hb := by rw [hβ (a, c)]; exact hac }⟩

/-- **A rational bordism presentation of the dimension-`4` numbers**: `Ω^SO_4 ⊗ ℚ = ℚ{[ℂP²]}`. -/
structure BordismPresentation4 (σ p₁ : ℤ) where
  /-- the rational model of `Ω^SO_4 ⊗ ℚ` -/
  B : Type
  [addCommGroup : AddCommGroup B]
  [module : Module ℚ B]
  /-- the signature functional -/
  sig : B →ₗ[ℚ] ℚ
  /-- the `p₁`-number functional -/
  p1 : B →ₗ[ℚ] ℚ
  /-- the class of `ℂP²` -/
  cp2 : B
  /-- the numbers of `ℂP²` -/
  hcp2 : (sig cp2, p1 cp2) = (1, 3)
  /-- the generator spans the rational bordism group -/
  spanning : Submodule.span ℚ {cp2} = ⊤
  /-- the class whose numbers are those of the manifold -/
  b : B
  /-- the numbers of `b` -/
  hb : (sig b, p1 b) = ((σ : ℚ), (p₁ : ℚ))

attribute [instance] BordismPresentation4.addCommGroup BordismPresentation4.module

/-- **A dimension-`4` presentation yields a span membership.** -/
theorem mem_span_of_presentation4 {σ p₁ : ℤ} (P : BordismPresentation4 σ p₁) :
    ((σ : ℚ), (p₁ : ℚ)) ∈ Submodule.span ℚ {cp2Tuple} := by
  let β : P.B →ₗ[ℚ] (ℚ × ℚ) := P.sig.prod P.p1
  have hcp2 : β P.cp2 = cp2Tuple := P.hcp2
  have hb : β P.b = ((σ : ℚ), (p₁ : ℚ)) := P.hb
  have hmem : P.b ∈ Submodule.span ℚ {P.cp2} := by rw [P.spanning]; trivial
  have hmap : Submodule.map β (Submodule.span ℚ {P.cp2}) = Submodule.span ℚ {cp2Tuple} := by
    rw [Submodule.map_span]
    simp only [Set.image_singleton, hcp2]
  rw [← hb, ← hmap]
  exact Submodule.mem_map_of_mem hmem

/-- **The dimension-`4` identity from a bordism presentation** (the base case `p₁ = 3σ` of the
Hirzebruch theory, in the form in which the bordism computation gives it). -/
theorem HirzebruchFour.of_presentation {σ p₁ : ℤ} (P : BordismPresentation4 σ p₁) :
    HirzebruchFour σ p₁ :=
  hirzebruchFour_of_mem_span σ p₁ (mem_span_of_presentation4 P)

end

end Work.SignatureBordism
