import Mathlib
import Submission.Work.Cohomology.cap_d

/-!
# The Kronecker pairing of cochains with chains

`⟨α, c⟩ = α(c)`: the evaluation pairing between `n`-cochains and `n`-chains.  It is the elementary
pairing whose *descent* to `H^n(X;R) × H_n(X;R) ⟶ R` (the Kronecker pairing) is the tool with which
the intersection form of a closed manifold is computed: the intersection number of two cohomology
classes is `⟨α ⌣ β, [X]⟩`, and the cap/cup identity proved here rewrites it as `⟨β, [X] ⌢ α⟩`.

## Main results

* `kronecker` — the pairing `⟨α, c⟩ = α c` on (co)chains, and `kroneckerHom` its underlying
  bilinear map;
* `kronecker_cap_cup` — **the cap/cup identity** `⟨β, c ⌢ α⟩ = (α ⌣ β)(c)`, the cochain-level
  engine of the intersection form;
* `kronecker_coboundary_cycle`, `kronecker_cocycle_boundary` — the vanishing statements which make
  the pairing factor through `H^n(X;R) × H_n(X;R)` (the descent itself is
  `Work.Cohomology.kroneckerH`).

## Conventions

With the repo's Alexander–Whitney conventions (`σ ⌢ α = α(σ_front) • σ_back` and
`(α ⌣ β)(σ) = α(σ_front) · β(σ_back)`) the identity reads `⟨β, c ⌢ α⟩ = ⟨α ⌣ β, c⟩`: the cochain
*capped with* is contracted against the front, the one *paired with* against the back.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-- **The Kronecker pairing** of a degree `n` cochain with an `n`-chain: `⟨α, c⟩ = α(c)`. -/
def kronecker (X : SSet) {n : ℕ} (α : Cochain R X n)
    (c : ↑((X.chainComplex (ModuleCat.of R R)).X n)) : R :=
  α c

/-- The Kronecker pairing as a bilinear map. -/
def kroneckerHom (X : SSet) (n : ℕ) :
    Cochain R X n →ₗ[R] (↑((X.chainComplex (ModuleCat.of R R)).X n) →ₗ[R] R) :=
  LinearMap.id

/-- The bilinear map `kroneckerHom` is the Kronecker pairing. -/
theorem kroneckerHom_apply (X : SSet) {n : ℕ} (α : Cochain R X n)
    (c : ↑((X.chainComplex (ModuleCat.of R R)).X n)) :
    kroneckerHom R X n α c = kronecker R X α c := rfl

/-- The Kronecker pairing on a generator is the evaluation `genEval`. -/
theorem kronecker_gen (X : SSet) {n : ℕ} (α : Cochain R X n) (σ : X _⦋n⦌) :
    kronecker R X α ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1) = genEval R X α σ := rfl

/-- The Kronecker pairing is additive in the cochain. -/
theorem kronecker_add (X : SSet) {n : ℕ} (α β : Cochain R X n)
    (c : ↑((X.chainComplex (ModuleCat.of R R)).X n)) :
    kronecker R X (α + β) c = kronecker R X α c + kronecker R X β c := rfl

/-- The Kronecker pairing is homogeneous in the cochain. -/
theorem kronecker_smul (X : SSet) {n : ℕ} (r : R) (α : Cochain R X n)
    (c : ↑((X.chainComplex (ModuleCat.of R R)).X n)) :
    kronecker R X (r • α) c = r • kronecker R X α c := rfl

/-! ## The cap/cup identity -/

/-- **The cap/cup identity.**  For a degree `m` cochain `α`, a degree `n` cochain `β` and an
`(m+n)`-chain `c`:

  `⟨β, c ⌢ α⟩ = (α ⌣ β)(c)`.

Both sides are elementary on generators: the left is `β` applied to `α(σ_front) • σ_back`, that is
`α(σ_front) · β(σ_back)`, which is exactly the value of the cup product `α ⌣ β` on `σ`. -/
theorem kronecker_cap_cup (X : SSet) {m n : ℕ} (α : Cochain R X m) (β : Cochain R X n)
    (c : ↑((X.chainComplex (ModuleCat.of R R)).X (m + n))) :
    kronecker R X β (cap R X α n c) = kronecker R X (cup R X α β) c := by
  have h : β.comp (cap R X α n) = cup R X α β := by
    apply genEval_ext
    intro σ
    show β (cap R X α n ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)) =
      genEval R X (cup R X α β) σ
    rw [cap_apply, cup_apply, map_smul]
    rfl
  exact LinearMap.congr_fun h c

/-! ## The pairing factors through homology -/

/-- **The pairing of a coboundary with a cycle vanishes.** -/
theorem kronecker_coboundary_cycle (X : SSet) {n : ℕ} (β : Cochain R X n)
    (c : ↑((X.chainComplex (ModuleCat.of R R)).X (n + 1)))
    (hc : ((X.chainComplex (ModuleCat.of R R)).d (n + 1) n).hom c = 0) :
    kronecker R X (cochainDiff R X β) c = 0 := by
  have h1 : kronecker R X (cochainDiff R X β) c
      = β (((X.chainComplex (ModuleCat.of R R)).d (n + 1) n).hom c) := rfl
  rw [h1, hc, map_zero]

/-- **The pairing of a cocycle with a boundary vanishes.** -/
theorem kronecker_cocycle_boundary (X : SSet) {n : ℕ} (β : Cochain R X n)
    (hβ : cochainDiff R X β = 0) (e : ↑((X.chainComplex (ModuleCat.of R R)).X (n + 1))) :
    kronecker R X β (((X.chainComplex (ModuleCat.of R R)).d (n + 1) n).hom e) = 0 := by
  have h1 : kronecker R X β (((X.chainComplex (ModuleCat.of R R)).d (n + 1) n).hom e)
      = (cochainDiff R X β) e := rfl
  rw [h1, hβ]
  rfl

end

end Work.Cohomology
