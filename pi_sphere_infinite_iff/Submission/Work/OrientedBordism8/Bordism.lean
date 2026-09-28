import Mathlib
import Submission.Work.SignatureBordism.Bordism

/-!
# The dimension-`4` and dimension-`8` signature theorems, from rational oriented bordism

This module sets up the *vocabulary* in which the Hirzebruch signature theorem in dimensions `4`
and `8` can be stated for a general closed oriented smooth manifold, and records the reduction to
the single topological input — **rational oriented bordism generation** — together with
everything that can be proved without it.

## The vocabulary

The workspace has no notion of smooth manifold at the level of `SSet` and no characteristic classes
of tangent bundles, see `Submission/Work/SignatureBordism/README.md`.  What it *does* have is the
cochain model of (co)homology: for a simplicial set `X` (the singular complex of the manifold) the
groups `H₄(X;ℤ)`, `H⁴(X;ℤ)`, `H⁸(X;ℤ)` are `(chainC ℤ X).homology 4` and
`(cochainC ℤ X).homology 4`, `.homology 8`.  Accordingly:

* `Work.OrientedBordism8.Manifold4` — the data of a closed oriented smooth `4`-manifold: a
  simplicial set, a fundamental class `c ∈ H₄`, and the first Pontryagin class of the tangent
  bundle `p₁ ∈ H⁴`;
* `Work.OrientedBordism8.Manifold8` — the same in dimension `8`: `c ∈ H₈`, `p₁ ∈ H⁴`, `p₂ ∈ H⁸`;
* the three numbers of such data — the signature `Work.SignatureBordism.sigma`, the `p₁²`-number
  `Work.SignatureBordism.p₁SqNumber`, the `p₂`-number `Work.SignatureBordism.p₂Number` — and the
  predicates `Manifold8.InSpan`, `Manifold8.IsHirzebruch`, `Manifold8.Congruence`.

The *only* thing not expressible here is the assertion that the data really come from a smooth
structure (that `c` is a fundamental class and `p₁`, `p₂` the Pontryagin classes of the tangent
bundle).  This is why the geometric input below is a hypothesis about a *family* of data rather
than about `Manifold8` itself.

## The geometric input

Let `Ω^SO_•` be the oriented bordism ring of closed oriented smooth manifolds.  Thom's theorem says
`Ω^SO_• ⊗ ℚ = ℚ[ℂP², ℂP⁴, ℂP⁶, …]`; in degrees `≤ 8` this is
`Ω^SO_4 ⊗ ℚ = ℚ{[ℂP²]}`, `Ω^SO_8 ⊗ ℚ = ℚ{[ℂP⁴], [ℂP² × ℂP²]}`.  Since the signature and the
Pontryagin numbers are bordism invariants, the *generation* of the rational bordism ring implies
that the three numbers of every closed oriented smooth `8`-manifold lie in the rational span of the
three numbers `(1,25,10)`, `(1,18,9)` of the two generators — i.e. `NumbersInSpan8` for every
genuine `8`-manifold.  This is the input:

* `Work.OrientedBordism8.Generation8 P` — generation holds on the family `P` of manifold data;
* `Work.OrientedBordism8.BordismModel8` — the *semantic* form: a rational model `B` of
  `Ω^SO_8 ⊗ ℚ` in which `σ`, `p₁²`, `p₂` are `ℚ`-linear functionals (this is what bordism
  invariance means), with the two generators, their numbers, a *family* `Genuine` of genuine
  manifolds, and a class realising the numbers of every genuine manifold;
  `BordismModel8.generation` shows that this implies `Generation8 P.Genuine`.

**Why the hypothesis is indexed by a family.**  `Manifold8` (and the parallel
`Work.TangentClasses.ClosedOriented8Manifold`) is *pure data*: it does not assert that `X` is a
smooth manifold or that `p₁`, `p₂` are the Pontryagin classes of its tangent bundle.  For a *single*
datum the span condition is equivalent to the Hirzebruch identity (`inSpan_iff_isHirzebruch`), and
any statement quantified over *all* such data is refutable by non-genuine data.  Hence the input is
parametrised by the family of genuine manifolds, on which it is the classical topological
statement (bordism invariance + generation); this is the strongest form in which it can be stated
without the (missing) vocabulary of tangent-bundle characteristic classes for a general manifold.

## Main results

* `Work.OrientedBordism8.hirzebruchEight_of_generation`,
  `congruence_of_generation`, `dvd_seven_of_generation` — the dimension-`8` identity, the
  congruence `p₁² ≡ 4σ (mod 7)` and the integrality `7 ∣ p₁² - 4σ` for every member of the family,
  from the generation hypothesis;
* the same in dimension `4`: `hirzebruchFour_of_generation`, `dvd_three_of_generation`
  (`3 ∣ p₁`);
* `Work.OrientedBordism8.inSpan_iff_isHirzebruch` — for a *single* datum, the generation
  hypothesis (span membership) is *equivalent* to the Hirzebruch identity; the content of the
  hypothesis is therefore entirely the statement that it holds for the whole family of genuine
  manifolds;
* `Work.OrientedBordism8.BordismModel8.generation` (family-indexed) and the consequences
  `BordismModel8.hirzebruchEight`, `.congruence`, `.dvd_seven` — the semantic form implies
  everything, for genuine data.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Work.OrientedBordism8

open Work.SignatureBordism Work.Cohomology

noncomputable section

/-! ## Closed oriented smooth manifolds in the cochain model -/

/-- **The data of a closed oriented smooth `4`-manifold** in the cochain model of this workspace:
a simplicial set `X` (the singular complex of the manifold), a fundamental class `c ∈ H₄(X;ℤ)` and
the first Pontryagin class `p₁ ∈ H⁴(X;ℤ)` of the tangent bundle.

The workspace cannot *express* the assertion that `X` is the singular complex of a smooth
`4`-manifold with fundamental class `c` and tangent Pontryagin class `p₁`; this structure is the
carrier of the data, and the geometric assertion is carried by hypotheses about *families* of such
data (see `Generation4`). -/
structure Manifold4 where
  /-- the simplicial set (the singular complex of the manifold) -/
  X : SSet
  /-- the fundamental class in `H₄` -/
  c : (chainC ℤ X).homology 4
  /-- the first Pontryagin class of the tangent bundle -/
  p1 : (cochainC ℤ X).homology 4

/-- **The data of a closed oriented smooth `8`-manifold** in the cochain model: a simplicial set,
a fundamental class `c ∈ H₈(X;ℤ)`, and the first two Pontryagin classes `p₁ ∈ H⁴(X;ℤ)`,
`p₂ ∈ H⁸(X;ℤ)` of the tangent bundle. -/
structure Manifold8 where
  /-- the simplicial set (the singular complex of the manifold) -/
  X : SSet
  /-- the fundamental class in `H₈` -/
  c : (chainC ℤ X).homology 8
  /-- the first Pontryagin class of the tangent bundle -/
  p1 : (cochainC ℤ X).homology 4
  /-- the second Pontryagin class of the tangent bundle -/
  p2 : (cochainC ℤ X).homology 8

namespace Manifold4

/-- The **signature** of a closed oriented `4`-manifold: the signature of the middle intersection
form (`Work.SignatureBordism.sigma 2`). -/
def signature (M : Manifold4) : ℤ := sigma 2 M.X M.c

/-- The **`p₁`-number** `⟨p₁(TM), [M]⟩` of a closed oriented `4`-manifold. -/
def p1Number (M : Manifold4) : ℤ := Work.SignatureBordism.p₁Number M.X M.c M.p1

/-- **The dimension-`4` Hirzebruch identity** `p₁ = 3σ` for a closed oriented `4`-manifold. -/
def IsHirzebruch (M : Manifold4) : Prop :=
  HirzebruchFourManifold M.X M.c M.p1

/-- **The generation hypothesis in dimension `4`** for a single datum: the pair of numbers
`(σ, p₁)` lies in the rational span of `(1, 3)`, the numbers of the generator `ℂP²` of
`Ω^SO_4 ⊗ ℚ`. -/
def InSpan (M : Manifold4) : Prop := NumbersInSpan4 M.X M.c M.p1

/-- **The congruence form** of the dimension-`4` identity: `3 ∣ p₁`. -/
def Congruence (M : Manifold4) : Prop := 3 ∣ M.p1Number

/-- The span condition is exactly the Hirzebruch identity, for a single datum
(`Work.SignatureBordism.mem_span4_iff_hirzebruchFour`). -/
theorem inSpan_iff_isHirzebruch (M : Manifold4) : M.InSpan ↔ M.IsHirzebruch :=
  mem_span4_iff_hirzebruchFour (signature M) (p1Number M)

/-- **The Hirzebruch identity gives the integrality `3 ∣ p₁`** (dimension `4`).

The converse is *false* and this matters: the congruence `3 ∣ p₁` is strictly weaker than
`p₁ = 3σ`, so the dimension-`4` signature theorem is not equivalent to the divisibility of `p₁`. -/
theorem isHirzebruch_congruence (M : Manifold4) (h : M.IsHirzebruch) : M.Congruence := by
  show 3 ∣ Work.SignatureBordism.p₁Number M.X M.c M.p1
  have h' : Work.SignatureBordism.p₁Number M.X M.c M.p1 = 3 * sigma 2 M.X M.c := h
  exact ⟨sigma 2 M.X M.c, h'⟩

end Manifold4

namespace Manifold8

/-- The **signature** of a closed oriented `8`-manifold: the signature of the middle intersection
form (`Work.SignatureBordism.sigma 4`). -/
def signature (M : Manifold8) : ℤ := sigma 4 M.X M.c

/-- The **`p₁²`-number** `⟨p₁(TM) ⌣ p₁(TM), [M]⟩` of a closed oriented `8`-manifold. -/
def p1sqNumber (M : Manifold8) : ℤ := Work.SignatureBordism.p₁SqNumber M.X M.c M.p1

/-- The **`p₂`-number** `⟨p₂(TM), [M]⟩` of a closed oriented `8`-manifold. -/
def p2Number (M : Manifold8) : ℤ := Work.SignatureBordism.p₂Number M.X M.c M.p2

/-- The **triple of numbers** `(σ, p₁², p₂)` of a closed oriented `8`-manifold. -/
def numbers (M : Manifold8) : ℤ × ℤ × ℤ := (M.signature, M.p1sqNumber, M.p2Number)

/-- **The dimension-`8` Hirzebruch identity** `45σ = 7p₂ - p₁²` for a closed oriented
`8`-manifold. -/
def IsHirzebruch (M : Manifold8) : Prop := HirzebruchEightManifold M.X M.c M.p1 M.p2

/-- **The generation hypothesis in dimension `8`** for a single datum: the triple of numbers
`(σ, p₁², p₂)` lies in the rational span of the numbers `(1,25,10)`, `(1,18,9)` of the two
generators `ℂP⁴`, `ℂP² × ℂP²` of `Ω^SO_8 ⊗ ℚ` (`Work.SignatureBordism.NumbersInSpan8`). -/
def InSpan (M : Manifold8) : Prop := NumbersInSpan8 M.X M.c M.p1 M.p2

/-- **The congruence form** of the dimension-`8` Hirzebruch identity:
`p₁² ≡ 4σ (mod 7)`, equivalently `7 ∣ p₁² - 4σ`. -/
def Congruence (M : Manifold8) : Prop :=
  M.p1sqNumber ≡ 4 * M.signature [ZMOD 7]

/-- The span condition is exactly the Hirzebruch identity, for a single datum
(`Work.SignatureBordism.mem_span_iff_hirzebruchEight`).

This is the precise sense in which the generation hypothesis is the *whole* content of the
dimension-`8` signature theorem: for a single manifold it is not weaker than the conclusion, and
its content is the statement that it holds for every genuine closed oriented smooth
`8`-manifold — that is, bordism invariance of the three numbers plus the generation of
`Ω^SO_8 ⊗ ℚ` by `ℂP⁴` and `ℂP² × ℂP²`. -/
theorem inSpan_iff_isHirzebruch (M : Manifold8) : M.InSpan ↔ M.IsHirzebruch :=
  mem_span_iff_hirzebruchEight (signature M) (p1sqNumber M) (p2Number M)

/-- The Hirzebruch identity gives the congruence `p₁² ≡ 4σ (mod 7)`
(`Work.SignatureBordism.hirzebruchEightManifold_congruence`). -/
theorem isHirzebruch_congruence (M : Manifold8) (h : M.IsHirzebruch) : M.Congruence :=
  hirzebruchEightManifold_congruence M.X M.c M.p1 M.p2 h

/-- The congruence is the integrality of Milnor's `λ`-invariant: `7 ∣ p₁² - 4σ`. -/
theorem congruence_iff_dvd (M : Manifold8) :
    M.Congruence ↔ 7 ∣ M.p1sqNumber - 4 * M.signature := by
  unfold Congruence
  rw [Int.modEq_iff_dvd]
  constructor
  · intro h; simpa only [neg_sub] using dvd_neg.mpr h
  · intro h; simpa only [neg_sub] using dvd_neg.mpr h

end Manifold8

/-! ## The generation hypothesis and its consequences -/

/-- **The rational oriented bordism generation hypothesis in dimension `8`, on a family.**

`P` cuts out the family of `8`-manifold data for which the topological input is asserted; for the
family of *genuine* closed oriented smooth `8`-manifolds, with their tangent Pontryagin classes,
`Generation8 P` is the classical statement

  *(bordism invariance of `σ`, `p₁²`, `p₂`) together with `Ω^SO_8 ⊗ ℚ = ℚ{[ℂP⁴], [ℂP² × ℂP²]}`*,

i.e. Thom's theorem in degree `8` (or the classical surgery computation of `Ω^SO_8 ⊗ ℚ`), not
available in this workspace (nor in Mathlib: there is no bordism theory and no manifold-with-
boundary theory).  Nothing below depends on *how* the family is described. -/
def Generation8 (P : Manifold8 → Prop) : Prop := ∀ M : Manifold8, P M → M.InSpan

/-- **The dimension-`8` Hirzebruch identity from the generation hypothesis.** -/
theorem hirzebruchEight_of_generation (P : Manifold8 → Prop) (hgen : Generation8 P)
    (M : Manifold8) (hM : P M) : M.IsHirzebruch :=
  (M.inSpan_iff_isHirzebruch).mp (hgen M hM)

/-- **The dimension-`8` Hirzebruch congruence from the generation hypothesis**:
`p₁² ≡ 4σ (mod 7)` for every closed oriented smooth `8`-manifold. -/
theorem congruence_of_generation (P : Manifold8 → Prop) (hgen : Generation8 P)
    (M : Manifold8) (hM : P M) : M.Congruence :=
  Manifold8.isHirzebruch_congruence M (hirzebruchEight_of_generation P hgen M hM)

/-- **The rational oriented bordism generation hypothesis in dimension `4`, on a family.**

`P` cuts out the family of `4`-manifold data for which the topological input is asserted; for the
family of *genuine* closed oriented smooth `4`-manifolds with their tangent `p₁`, `Generation4 P`
is the classical statement

  *(bordism invariance of `σ` and of `p₁`)* together with `Ω^SO_4 ⊗ ℚ = ℚ{[ℂP²]}`.

It is the dimension-`4` analogue of `Work.OrientedBordism8.Generation8`, and it is the *first*
instance of the dimension-`4` signature theorem `p₁ = 3σ`. -/
def Generation4 (P : Manifold4 → Prop) : Prop := ∀ M : Manifold4, P M → M.InSpan

/-- **Integrality of Milnor's `λ`-invariant from the generation hypothesis**:
`7 ∣ p₁² - 4σ` for every closed oriented smooth `8`-manifold. -/
theorem dvd_seven_of_generation (P : Manifold8 → Prop) (hgen : Generation8 P)
    (M : Manifold8) (hM : P M) : 7 ∣ M.p1sqNumber - 4 * M.signature :=
  M.congruence_iff_dvd.mp (congruence_of_generation P hgen M hM)

/-- **The dimension-`4` Hirzebruch identity from the generation hypothesis in dimension `4`.** -/
theorem hirzebruchFour_of_generation (P : Manifold4 → Prop)
    (hgen : ∀ M : Manifold4, P M → M.InSpan) (M : Manifold4) (hM : P M) : M.IsHirzebruch :=
  (M.inSpan_iff_isHirzebruch).mp (hgen M hM)

/-- **The integrality statement `3 ∣ p₁` in dimension `4`, from the generation hypothesis.** -/
theorem dvd_three_of_generation (P : Manifold4 → Prop)
    (hgen : ∀ M : Manifold4, P M → M.InSpan) (M : Manifold4) (hM : P M) : 3 ∣ M.p1Number :=
  Manifold4.isHirzebruch_congruence M (hirzebruchFour_of_generation P hgen M hM)

/-- **The dimension-`4` Hirzebruch identity from `Generation4`.** -/
theorem hirzebruchFour_of_generation4 (P : Manifold4 → Prop) (hgen : Generation4 P)
    (M : Manifold4) (hM : P M) : M.IsHirzebruch :=
  hirzebruchFour_of_generation P hgen M hM

/-- **The integrality `3 ∣ p₁` in dimension `4`, from `Generation4`.** -/
theorem dvd_three_of_generation4 (P : Manifold4 → Prop) (hgen : Generation4 P)
    (M : Manifold4) (hM : P M) : 3 ∣ M.p1Number :=
  dvd_three_of_generation P hgen M hM

/-- **The congruence `p₁ ≡ 0 (mod 3)`, i.e. `3 ∣ p₁`, from `Generation4`.** -/
theorem congruence_of_generation4 (P : Manifold4 → Prop) (hgen : Generation4 P)
    (M : Manifold4) (hM : P M) : M.Congruence :=
  Manifold4.isHirzebruch_congruence M (hirzebruchFour_of_generation4 P hgen M hM)

/-- **`Generation4` is exactly the family-indexed dimension-`4` identity**, as in dimension `8`:
for a *single* datum the span condition is equivalent to the identity, so the content of the input
is entirely the statement that it holds on the whole family of genuine manifolds. -/
theorem generation4_iff_isHirzebruch (P : Manifold4 → Prop) :
    Generation4 P ↔ ∀ M : Manifold4, P M → M.IsHirzebruch :=
  forall_congr' fun M => imp_congr_right fun _ => (M.inSpan_iff_isHirzebruch)

/-! ## The semantic form: a rational model of `Ω^SO_8 ⊗ ℚ` -/

/-- **A rational bordism model of closed oriented smooth `8`-manifolds.**

`B` is a rational model of `Ω^SO_8 ⊗ ℚ` (so `B` is two-dimensional), `sig`, `p1sq`, `p2` are the
three characteristic-number functionals on it — the fact that they are defined on *bordism classes*
rather than on manifolds is exactly bordism invariance of those numbers — `cp4` and `cp2cp2` are
the classes of `ℂP⁴` and `ℂP² × ℂP²` with their numbers, these two span `B` (generation), and
`realise` says that the numbers of every genuine closed oriented smooth `8`-manifold are the values
of the three functionals on some class of `B`.

Producing a `BordismModel8` is the geometric input of the dimension-`8` signature theorem; it is
not available in this workspace. -/
structure BordismModel8 where
  /-- the family of *genuine* closed oriented smooth `8`-manifolds on which the model is asserted;
  this is the parameter that keeps the hypothesis from being a statement about the purely formal
  structure `Manifold8` -/
  Genuine : Manifold8 → Prop
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
  /-- every genuine closed oriented smooth `8`-manifold has a bordism class realising its numbers -/
  realise : ∀ M : Manifold8, Genuine M → ∃ b : B,
    (sig b, p1sq b, p2 b)
      = (((M.signature : ℤ) : ℚ), ((M.p1sqNumber : ℤ) : ℚ), ((M.p2Number : ℤ) : ℚ))

attribute [instance] BordismModel8.addCommGroup BordismModel8.module

namespace BordismModel8

/-- **A rational bordism model implies the generation hypothesis** on the family of genuine data it
realises: the numbers of a realised manifold are the values of three linear functionals on an
element of the span of the two generators, hence lie in the span of the two generator triples.

Note the membership hypothesis `P.Genuine M`: the model is asserted only for the *genuine*
manifolds, which is what makes the hypothesis the topological statement rather than a statement
about the (purely formal) structure `Manifold8`. -/
theorem generation (P : BordismModel8) : Generation8 P.Genuine := by
  intro M _
  obtain ⟨b, hb⟩ := P.realise M ‹_›
  let β : P.B →ₗ[ℚ] (ℚ × ℚ × ℚ) := P.sig.prod (P.p1sq.prod P.p2)
  have hcp4 : β P.cp4 = cp4Tuple := P.hcp4
  have hcp2cp2 : β P.cp2cp2 = cp2cp2Tuple := P.hcp2cp2
  have hb' : β b = ((sigma 4 M.X M.c : ℚ), (p₁SqNumber M.X M.c M.p1 : ℚ),
      (p₂Number M.X M.c M.p2 : ℚ)) := hb
  have hmem : b ∈ Submodule.span ℚ {P.cp4, P.cp2cp2} := by rw [P.spanning]; trivial
  have hmap : Submodule.map β (Submodule.span ℚ {P.cp4, P.cp2cp2})
      = Submodule.span ℚ {cp4Tuple, cp2cp2Tuple} := by
    rw [Submodule.map_span]
    simp only [Set.image_pair, hcp4, hcp2cp2]
  unfold Manifold8.InSpan NumbersInSpan8
  rw [← hb', ← hmap]
  exact Submodule.mem_map_of_mem hmem

/-- **The dimension-`8` Hirzebruch identity from a rational bordism model**, for a genuine datum. -/
theorem hirzebruchEight (P : BordismModel8) (M : Manifold8) (hM : P.Genuine M) : M.IsHirzebruch :=
  hirzebruchEight_of_generation _ P.generation M hM

/-- **The dimension-`8` congruence from a rational bordism model**, for a genuine datum. -/
theorem congruence (P : BordismModel8) (M : Manifold8) (hM : P.Genuine M) : M.Congruence :=
  congruence_of_generation _ P.generation M hM

/-- **Integrality of `λ` from a rational bordism model**: `7 ∣ p₁² - 4σ`, for a genuine datum. -/
theorem dvd_seven (P : BordismModel8) (M : Manifold8) (hM : P.Genuine M) :
    7 ∣ M.p1sqNumber - 4 * M.signature :=
  dvd_seven_of_generation _ P.generation M hM

end BordismModel8

/-! ## The semantic form in dimension `4` -/

/-- **A rational bordism model of closed oriented smooth `4`-manifolds**: a rational model `B ≅ ℚ` of
`Ω^SO_4 ⊗ ℚ = ℚ{[ℂP²]}` (so `B` is one-dimensional), the signature and `p₁`-number functionals
(bordism invariance of both), the generator `[ℂP²]` with its numbers `(1,3)`, generation, and a
class realising the numbers of every genuine `4`-manifold.

This is the dimension-`4` analogue of `Work.OrientedBordism8.BordismModel8` and the base case of the
Hirzebruch theory. -/
structure BordismModel4 where
  /-- the family of *genuine* closed oriented smooth `4`-manifolds on which the model is asserted -/
  Genuine : Manifold4 → Prop
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
  /-- `ℂP²` generates -/
  spanning : Submodule.span ℚ {cp2} = ⊤
  /-- every genuine closed oriented `4`-manifold has a bordism class realising its numbers -/
  realise : ∀ M : Manifold4, Genuine M → ∃ b : B,
    (sig b, p1 b) = (((M.signature : ℤ) : ℚ), ((M.p1Number : ℤ) : ℚ))

attribute [instance] BordismModel4.addCommGroup BordismModel4.module

namespace BordismModel4

/-- **A rational bordism model in dimension `4` implies the generation hypothesis** for every
`4`-manifold datum it realises. -/
theorem generation (P : BordismModel4) : ∀ M : Manifold4, P.Genuine M → M.InSpan := by
  intro M _
  obtain ⟨b, hb⟩ := P.realise M ‹_›
  have hmem : b ∈ Submodule.span ℚ {P.cp2} := by rw [P.spanning]; trivial
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  have hsig2 : P.sig P.cp2 = 1 := congrArg Prod.fst P.hcp2
  have hp12 : P.p1 P.cp2 = 3 := congrArg Prod.snd P.hcp2
  have hsig : (M.signature : ℚ) = a := by
    have h2 : (P.sig b : ℚ) = a := by
      rw [← ha, map_smul, hsig2]
      simp
    exact ((congrArg Prod.fst hb : (P.sig b : ℚ) = ((M.signature : ℤ) : ℚ))).symm.trans h2
  have hp1 : (M.p1Number : ℚ) = 3 * a := by
    have h2 : (P.p1 b : ℚ) = 3 * a := by
      rw [← ha, map_smul, hp12]
      simp [smul_eq_mul]
      ring
    exact ((congrArg Prod.snd hb : (P.p1 b : ℚ) = ((M.p1Number : ℤ) : ℚ))).symm.trans h2
  show ((M.signature : ℚ), (M.p1Number : ℚ)) ∈ Submodule.span ℚ {cp2Tuple}
  rw [hsig, hp1]
  refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
  simp only [cp2Tuple, Prod.smul_mk, smul_eq_mul, mul_one]
  refine Prod.ext ?_ ?_ <;> ring

/-- **A rational bordism model in dimension `4` gives `Generation4`** for the family of genuine
manifolds it realises. -/
theorem generation4 (P : BordismModel4) : Generation4 P.Genuine :=
  fun M hM => P.generation M hM

/-- **The dimension-`4` Hirzebruch identity from a rational bordism model.** -/
theorem hirzebruchFour (P : BordismModel4) (M : Manifold4) (hM : P.Genuine M) : M.IsHirzebruch :=
  (M.inSpan_iff_isHirzebruch).mp (P.generation M hM)

/-- **The integrality `3 ∣ p₁` in dimension `4` from a rational bordism model.** -/
theorem dvd_three (P : BordismModel4) (M : Manifold4) (hM : P.Genuine M) : 3 ∣ M.p1Number :=
  Manifold4.isHirzebruch_congruence M (P.hirzebruchFour M hM)

end BordismModel4

/-! ## The incompatibility of the congruence with the numbers of `X = D(ξ) ∪_F D⁸`

The endgame of the exotic-`7`-sphere project computes `σ(X) = ±1` and
`p₁(X)² = 36 σ(X)`; the dimension-`8` Hirzebruch congruence would force
`p₁(X)² ≡ 4σ(X) (mod 7)`, i.e. `36σ ≡ 4σ`, i.e. `7 ∣ 32σ`, which is impossible since
`σ = ±1`.  The arithmetic of this incompatibility, in a form usable at `X`: -/

/-- **The dimension-`8` congruence fails for unimodular self-intersection with `p₁² = 36σ`.**  If
the signature is `±1` (unimodularity of the middle intersection form, so `σ = ±1` with `p₁ = q·x`
and `q² = 36`) then the congruence `p₁² ≡ 4σ (mod 7)` is *false*.

This is the arithmetic core of `Work.SignatureBordism.not_numbersInSpan_capped` and hence of the
endgame: the generation hypothesis is incompatible with the existence of the capped manifold. -/
theorem not_congruence_of_unimodular (σ p₁sq : ℤ) (hσ : σ = 1 ∨ σ = -1) (h : p₁sq = 36 * σ) :
    ¬ (p₁sq ≡ 4 * σ [ZMOD 7]) := by
  intro hc
  rw [Int.modEq_iff_dvd] at hc
  rcases hσ with rfl | rfl
  · rw [h] at hc; norm_num at hc
  · rw [h] at hc; norm_num at hc

end

/-! ## The arithmetic of the rank-`1` family (where the surgery computation of `Ω^SO_8 ⊗ ℚ` lands)

The classical surgery computation of `Ω^SO_8 ⊗ ℚ` reduces a closed oriented `8`-manifold to a
`3`-connected one, whose bordism class is governed by its middle intersection form and the
`π₃(SO(4)) = ℤ²` framings of its `4`-handles; the rank-`1` pieces are the manifolds
`W(ξ) = D(ξ) ∪ D⁸` for `ξ = L^aR^b` a rank-`4` bundle over `S⁴`, whose middle form is generated by
one class `x` with `⟨x ⌣ x, [W]⟩ = σ = ±1` and whose first Pontryagin class is `p₁ = 2(a-b)·x`,
so that `p₁² = 4k²σ` with `k = a - b`.  The following arithmetic is therefore the exact form the
dimension-`8` congruence takes on that family.
-/

/-- **The dimension-`8` congruence for a rank-`1` middle form.**  If `σ = ±1` and
`p₁² = 4k²σ` — the shape of the numbers of `W(L^aR^b) = D(L^aR^b) ∪ D⁸` with `k = a - b` — then
`p₁² ≡ 4σ (mod 7)` is equivalent to `k² ≡ 1 (mod 7)`, **independently of the orientation `σ`**.

For `k = 3` (Milnor's bundle `ξ = L²R⁻¹`, `p₁(ξ) = 6`) the condition fails, which together with
`Work.SignatureBordism.capped_p₁SqNumber_eq_thirtysix_sigma` and
`Work.OrientedBordism8.not_congruence_of_unimodular` is the exoticness of `Mk(-2)` itself.  For
`k = 1` it holds, and indeed the resulting numbers `(1, 4, 7)` of `ℍP² = D(L) ∪ D⁸` lie in the span
of the generator triples: `(1,4,7) = -2·(1,25,10) + 3·(1,18,9)`. -/
theorem rankOne_congruence_iff (k σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    (4 * k ^ 2 * σ ≡ 4 * σ [ZMOD 7]) ↔ (k ^ 2 ≡ 1 [ZMOD 7]) := by
  have hp : Prime (7 : ℤ) := by norm_num
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd]
  have hval : (4 * σ - 4 * k ^ 2 * σ) = 4 * σ * (1 - k ^ 2) := by ring
  rw [hval]
  constructor
  · intro h
    rcases hp.dvd_mul.mp h with h' | h'
    · exact absurd h' (by rcases hσ with rfl | rfl <;> norm_num)
    · exact h'
  · intro h
    exact dvd_mul_of_dvd_right h (4 * σ)

/-- **What generation gives on the rank-`1` family.**  If the numbers `(σ, 4k²σ, p₂)` of a rank-`1`
piece (with `σ = ±1`, `p₁ = 2k·x` and `⟨x ⌣ x, [W]⟩ = σ`) lie in the rational span of the generator
triples `(1,25,10)`, `(1,18,9)` — i.e. if the generation hypothesis holds for that piece — then
necessarily `k² ≡ 1 (mod 7)`.

Contrapositively: the rank-`1` pieces with `k ≢ ±1 (mod 7)` cannot satisfy the generation
hypothesis, and for Milnor's `ξ = L²R⁻¹` (`k = 3`) this is the exoticness of `Mk(-2)`.  So the
rank-`1` family — the family on which the surgery computation of `Ω^SO_8 ⊗ ℚ` lands — contributes
to `spanning` exactly the arithmetic restriction `k² ≡ 1 (mod 7)`; the `r ≥ 2` handles are genuinely
needed for the second dimension of `Ω^SO_8 ⊗ ℚ`. -/
theorem rankOne_inSpan_implies (k σ p₂ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (h : (((σ : ℚ), ((4 * k ^ 2 * σ : ℤ) : ℚ), (p₂ : ℚ))) ∈
      Submodule.span ℚ ({cp4Tuple, cp2cp2Tuple} : Set (ℚ × ℚ × ℚ))) :
    k ^ 2 ≡ 1 [ZMOD 7] := by
  have hh : HirzebruchEight σ (4 * k ^ 2 * σ) p₂ :=
    (mem_span_iff_hirzebruchEight σ (4 * k ^ 2 * σ) p₂).mp h
  unfold HirzebruchEight at hh
  have h7 : (7 : ℤ) ∣ 4 * σ - 4 * k ^ 2 * σ := ⟨7 * σ - p₂, by linarith⟩
  exact (rankOne_congruence_iff k σ hσ).mp (Int.modEq_iff_dvd.mpr h7)

/-- **The rank-`1` slice of the generation hypothesis, exactly.**  For a rank-`1` piece with
`σ = ±1` and `p₁² = 4k²σ`, the numbers *can* be completed to a triple lying in the span of the
generator triples `(1,25,10)`, `(1,18,9)` **iff** `k² ≡ 1 (mod 7)`.  In that case the completion is
unique, `p₂ = σ(45 + 4k²)/7`.

So the rank-`1` family (the family on which the surgery computation of `Ω^SO_8 ⊗ ℚ` lands)
contributes to `spanning` precisely the slice `k ≡ ±1 (mod 7)` of its parameters, and nothing else;
for Milnor's `ξ = L²R⁻¹` (`k = 3`) even the completion does not exist, which is the exoticness of
`Mk(-2)`. -/
theorem rankOne_mem_span_iff (k σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    (k ^ 2 ≡ 1 [ZMOD 7]) ↔
      ∃ p₂ : ℤ, ((σ : ℚ), ((4 * k ^ 2 * σ : ℤ) : ℚ), (p₂ : ℚ)) ∈
        Submodule.span ℚ ({cp4Tuple, cp2cp2Tuple} : Set (ℚ × ℚ × ℚ)) := by
  constructor
  · intro hk
    have h4 : (45 + 4 * k ^ 2) ≡ 0 [ZMOD 7] := by
      have h1 : (4 * k ^ 2) ≡ 4 * 1 [ZMOD 7] := (Int.ModEq.refl 4).mul hk
      have h2 : (45 + 4 * k ^ 2) ≡ 45 + 4 * 1 [ZMOD 7] := (Int.ModEq.refl 45).add h1
      have h3 : (45 + 4 * 1 : ℤ) ≡ 0 [ZMOD 7] := by decide
      exact h2.trans h3
    have hdiv : (7 : ℤ) ∣ 45 + 4 * k ^ 2 := by
      have h := Int.modEq_iff_dvd.mp h4
      rw [zero_sub] at h
      exact dvd_neg.mp h
    obtain ⟨c, hc⟩ := hdiv
    refine ⟨σ * c, ?_⟩
    rw [mem_span_iff_hirzebruchEight]
    unfold HirzebruchEight
    linear_combination (σ : ℤ) * hc
  · rintro ⟨p₂, hp⟩
    exact rankOne_inSpan_implies k σ p₂ hσ hp

end Work.OrientedBordism8
