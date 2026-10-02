import Mathlib
import Submission.Work.LerayHirsch.LH
import Submission.Work.Whitney.Stability
import Submission.Work.Whitney.Hypotheses

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.dupNamespace false

/-!
# The splitting principle for the projectivisation

Let `Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι` be a complex gluing-data bundle,
`P(E)` its projectivisation and `ℓ ⊆ π^*E` the tautological line bundle with `ζ = c₁(ℓ)`
(`Submission/Work/LerayHirsch/TautLine.lean`).  This module contains

* the **elementary Chern calculus of the tautological line bundle**: `c₁(ℓ) = ζ` and
  `c_j(ℓ) = 0` for `j ≥ 2` — i.e. the total Chern class of `ℓ` is `1 + ζ`;
* the **splitting principle** at the projectivisation, as the `Prop` `SplitsOverProj`: there is a
  complex bundle `Q` of rank `m-1` over `P(E)` with
  `π^*E ≅ ℓ ⊕ Q` (`Work.Thom.BundleIso`), and its cohomological consequence: over `P(E)` both
  factors of the Whitney formula can be split into line bundles;
* the **relationship to the Whitney formula**: the reduction
  `Work.LerayHirsch.chernClass_whitneySum_of_LerayHirsch` (delegated) — the statement that
  `LerayHirsch` plus the geometric splitting gives the Whitney sum formula
  `c_k(E ⊕ F) = Σ_{i+j=k} c_i(E)⌣c_j(F)` for the direct sum of
  `Submission/Work/Whitney/`.

## Conventions and the exact division of labour with WHITNEY

The top-degree multiplicativity of the Euler class
(`Work.Whitney.TopClassMul`, equivalently `c_{m+n}(E⊕F) = c_m(E)c_n(F)`) and the direct sum
`Work.Whitney.whitneySum`, the right-hand side `Work.Whitney.chernProductSum`, the graded product
`Work.Whitney.cupChern` and stability are **WHITNEY's**; this chapter adds the *projectivisation*
and the *Leray–Hirsch/splitting* input that closes the intermediate degrees `max(m,n) ≤ k ≤ m+n-1`
which WHITNEY's §6 shows cannot be reached by the descent equation alone.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-! ## The Chern calculus of the tautological line bundle -/

/-- **`c₁(ℓ) = ζ`**: the defining property of the hyperplane class. -/
theorem zeta_eq_chernClass_tautLine (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    [Fintype ι] :
    zeta Z = cohTransport (by rfl : 2 * 1 = 2) (chernClass 1 1 (tautLine Z)) := by
  rw [zeta]

/-- **The tautological line bundle has no Chern class above degree one**: `c_j(ℓ) = 0` for `j ≥ 2`.
Together with `zeta_eq_chernClass_tautLine` and `c₀ = 1` this says that the total Chern class of `ℓ`
is `1 + ζ`, which is the input of the splitting-principle computation of the Whitney formula. -/
theorem chernClass_tautLine_eq_zero_of_gt (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    [Fintype ι] {j : ℕ} (hj : 1 < j) : chernClass 1 j (tautLine Z) = 0 :=
  chernClass_succ_of_gt (tautLine Z) (by simpa using hj)

/-- The rank of the tautological line bundle is one. -/
theorem chernClass_tautLine_zero (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    [Fintype ι] : chernClass 1 0 (tautLine Z) = cohTransport (by rfl : 0 = 2 * 0)
      (Work.Cohomology.oneH ℤ (Work.Whitney.ssB (ProjSpace Z))) :=
  chernClass_zero_eq_oneH (tautLine Z)

/-- `ζ` is natural under pullback: the hyperplane class of the pullback of the projectivisation is
the pullback of the hyperplane class.  (Consequence of the naturality of the Chern classes,
`Work.Thom.chernClass_comap`.) -/
theorem zeta_congr_homeo (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    {B' : Type} [TopologicalSpace B'] (f : C(B', ProjSpace Z)) :
    (CohMap f ℤ 2).hom (zeta Z)
      = cohTransport (by rfl : 2 * 1 = 2) (chernClass 1 1 (bundleComap (tautLine Z) f)) := by
  rw [zeta, Work.Thom.chernClass_comap]
  rfl

/-! ## Bundle maps and the tautological embedding -/

/-- A **bundle map** between two gluing-data bundles over the same base: a fibrewise linear map whose
induced map of total spaces is continuous.  (The non-invertible companion of
`Work.Thom.BundleIso`.) -/
structure BundleMap {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
    {F F' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F']
    [NormedSpace 𝕜 F'] {ι ι' : Type} (Z : VectorBundleCore 𝕜 B F ι)
    (Z' : VectorBundleCore 𝕜 B F' ι') where
  /-- the fibrewise linear map -/
  hom : ∀ b : B, Z.Fiber b →ₗ[𝕜] Z'.Fiber b
  /-- continuity of the induced map of total spaces -/
  continuous_hom : Continuous fun p : Z.TotalSpace => (⟨p.1, hom p.1 p.2⟩ : Z'.TotalSpace)

/-- A bundle map is a **monomorphism** when every fibrewise linear map is injective. -/
def BundleMap.Injective {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
    {F F' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F']
    [NormedSpace 𝕜 F'] {ι ι' : Type} {Z : VectorBundleCore 𝕜 B F ι}
    {Z' : VectorBundleCore 𝕜 B F' ι'} (φ : BundleMap Z Z') : Prop :=
  ∀ b : B, Function.Injective (φ.hom b)

/-! ## The splitting principle -/

/-- **The splitting principle at the projectivisation**: for a complex gluing-data bundle `E` of
rank `m' + 1`, the pullback of `E` to `P(E)` splits as the tautological line bundle `ℓ` plus a
complex bundle `Q` of rank `m'`:

`π^*E ≅ ℓ ⊕ Q`.

(Classically `Q = π^*E/ℓ`, the tautological quotient bundle, and the splitting exists because
`π^*E` carries a nowhere-zero section of `π^*E ⊗ ℓ^*`, which splits off a line over a paracompact
base — `Work.Whitney.nonempty_bundleIso_of_nowhereZeroSection_of_paracompact`.  This is the single
geometric input of the splitting principle; everything else in this chapter is Leray–Hirsch.) -/
def SplitsOverProj {m' : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m' + 1))) ι)
    [Fintype ι] : Prop :=
  ∃ Q : VectorBundleCore ℂ (ProjSpace Z) (EuclideanSpace ℂ (Fin m')) (ι × Fin (m' + 1)),
    Nonempty (BundleIso (bundleComap Z (projMap Z))
      (Work.Whitney.whitneySum (tautLine Z) Q))

/-- **The tautological embedding**: the tautological line bundle is a sub-line-bundle of
`π^*E` — there is a continuous fibrewise *injective* linear map `ℓ → π^*E`.  Its image over a point
`x = [p]` is the line spanned by the fibre vector `p.2`. -/
def TautologicalEmbedding (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] :
    Prop :=
  ∃ φ : BundleMap (tautLine Z) (bundleComap Z (projMap Z)), φ.Injective

/-- **The flag-bundle form of the splitting principle**: there is a space `F` over `B`, a map
`π : F → B` which is injective on cohomology (in every degree), and a *tower*
`0 = V_0 ⊂ V_1 ⊂ … ⊂ V_m = π^*E` of subbundles of `π^*E` whose successive quotients are line
bundles:

`V_{k+1} ≅ L_k ⊕ V_k`   with `L_k` of rank one.

`F` is the flag bundle of `E`, obtained by iterating `SplitsOverProj` along the tower of
tautological quotients; the injectivity of `π^*` is the iterated Leray–Hirsch theorem
(`Work.LerayHirsch.CohMap_projMap_injective_of_LerayHirsch`).

**This is the *tower* form of the splitting principle, kept for reference.**  The form that is
actually proved in this chapter is the *sum* form `Work.LerayHirsch.SplittingPrinciple`
(`Submission/Work/LerayHirsch/FlagBundle.lean`), which is the more usable statement: it says that
`π^*E` is isomorphic to an explicit iterated direct sum `Work.LerayHirsch.lineSumCore m L` of line
bundles over one common cover of the flag bundle.  The tower above is a consequence of the sum form
(the tower of partial sums of `L`), but the sum form avoids the dependent recursion over the
successive intermediate bases, which is why it is the one stated and proved. -/
def SplittingPrincipleTower (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] : Prop :=
  ∃ (P : Type) (_ : TopologicalSpace P) (π : C(P, B)) (ιL : ℕ → Type)
    (_ : ∀ k, Fintype (ιL k)),
    (∀ k : ℕ, Function.Injective (CohMap π ℤ k).hom) ∧
      ∃ (V : (k : ℕ) → VectorBundleCore ℂ P (EuclideanSpace ℂ (Fin k)) (ιL k))
        (L : (k : ℕ) → VectorBundleCore ℂ P (EuclideanSpace ℂ (Fin 1)) (ιL (k + 1))),
        Nonempty (BundleIso (bundleComap Z π) (V m)) ∧
          (∀ k, k < m → Nonempty (BundleIso (V (k + 1))
            (Work.Whitney.whitneySum (L k) (V k))))

/-! ## The Whitney sum formula, and the assembly statement of this chapter -/

/-- The **Whitney sum formula** for the direct sum `Work.Whitney.whitneySum` of
`Submission/Work/Whitney/`: for complex gluing-data bundles `E`, `F` of ranks `m₁`, `m₂` over any
base, the `k`-th Chern class of `E ⊕ F` is `Σ_{i+j=k} c_i(E) ⌣ c_j(F)`. -/
def WhitneySumFormula (m₁ m₂ : ℕ) : Prop :=
  ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) (k : ℕ),
    Work.Thom.chernClass (m₁ + m₂) k (Work.Whitney.whitneySum Z₁ Z₂)
      = Work.Whitney.chernProductSum Z₁ Z₂ k

/-- **The assembly statement of this chapter**: the Leray–Hirsch theorem for the projectivisation
of every complex gluing-data bundle (`LerayHirschFull`, from `KunnethCP` and `LerayHirschGlue` by
the Mayer–Vietoris induction), the geometric splitting `SplitsOverProj`, and **the Whitney formula
in the case of one line-bundle summand**
(`∀ N, WhitneySumFormula 1 N`, the classical "projection formula" case) together imply the
**Whitney sum formula in all degrees**.

**The induction** (on `m₁`, in the form described in the docstring of
`Submission/Work/Whitney/README.md` §6): pull the identity back along `π : P(Z₁) → B`.  Then

* `π^*` is injective on cohomology (`CohMap_projMap_injective_of_LerayHirschFull`), so it suffices
  to prove the identity on `P(E)`;
* `π^*(Z₁ ⊕ Z₂) ≅ π^*Z₁ ⊕ π^*Z₂ ≅ ℓ ⊕ (Q ⊕ π^*Z₂)` (`Work.Whitney.whitneySum_bundleComap`,
  `SplitsOverProj`, associativity of `Work.Whitney.whitneySum`), so in degree `k`
  `c_k(π^*(Z₁⊕Z₂)) = Σ_{i+j=k} c_i(ℓ)c_j(Q ⊕ π^*Z₂)` by the line-bundle case,
  and since `c(ℓ) = 1 + ζ` (`zeta_eq_chernClass_tautLine`, `chernClass_tautLine_eq_zero_of_gt`)
  this is `c_k(Q ⊕ π^*Z₂) + ζ c_{k-1}(Q ⊕ π^*Z₂)`;
* `c(Q ⊕ π^*Z₂) = c(Q)c(π^*Z₂)` is the **induction hypothesis** in ranks `(m₁-1, m₂)`;
* substituting `π^*c_i(Z₁) = c_i(π^*Z₁) = c_i(ℓ ⊕ Q) = c_i(Q) + ζ c_{i-1}(Q)`, again by the
  line-bundle case, and summing over `i + j = k` gives `Σ_{i+j=k} π^*c_i(Z₁)π^*c_j(Z₂)`, which is
  the pullback of the right-hand side of the Whitney formula.

**Warning (do not over-claim).**  The line-bundle case `∀ N, WhitneySumFormula 1 N` is carried as an
explicit input: by `Submission/Work/Gen/whitneyLowDegree.lean` (see also `Submission/Work/Gen/EULERCHERN_STATUS.md`), the case
`(1,1)`, i.e. `c₁(L₁⊕L₂) = c₁(L₁)+c₁(L₂)`, is *not* implied by `LerayHirschFull` + `SplitsOverProj`
+ WHITNEY's `TopClassMul`, so it cannot be omitted; and without the `(1,N)` family the induction
above does not close either.  The core of the induction is not formalised here. -/
def WhitneySumFormulaFromLerayHirsch : Prop :=
  (∀ {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι), LerayHirschFull Z) →
  (∀ {m' : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m' + 1))) ι), SplitsOverProj Z) →
  (∀ N : ℕ, WhitneySumFormula 1 N) →
  ∀ m₁ m₂ : ℕ, WhitneySumFormula m₁ m₂

/-- The same assembly statement with WHITNEY's top-degree multiplicativity in place of the
line-bundle *formula*: `Work.Whitney.TopClassMul` and the single case
`WhitneySumFormula 1 1` are what the two other areas (`Submission/Work/Whitney/`,
`Submission/Work/Gen/`) are building, so this is the consumer-facing form of the target. -/
def WhitneySumFormulaFromLerayHirschTarget : Prop :=
  (∀ {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι), LerayHirschFull Z) →
  (∀ {m' : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m' + 1))) ι), SplitsOverProj Z) →
  Work.Whitney.TopClassMul →
  WhitneySumFormula 1 1 →
  ∀ m₁ m₂ : ℕ, WhitneySumFormula m₁ m₂

end

end Work.LerayHirsch
