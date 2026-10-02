import Mathlib
import Submission.Work.Cohomology.Kronecker
import Submission.Work.Cohomology.cupH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Kronecker pairing descends to (co)homology

`Work.Cohomology.kronecker R X α c = α c` is the evaluation pairing of a singular cochain with a
singular chain.  Its fundamental property is that it vanishes on coboundaries in the first
variable and on boundaries in the second (`kronecker_coboundary_cycle`,
`kronecker_cocycle_boundary`), which is exactly the statement that it *descends* to a pairing

  `Hⁿ(X;R) ⟶ (Hₙ(X;R) →ₗ[R] R)`,

the **Kronecker pairing** of the title.  This file constructs that descent and proves the defining
property `⟨[α], [z]⟩ = α(z)` for every `n`-cocycle `α` and every `n`-cycle `z`.

The descent is performed in the two variables separately, in exactly the style used for the cup
product (`Work.Cohomology.cupH`):

* in the *chain* variable, the functional `z ↦ α(z)` on the cycles of the chain complex
  `C = X.chainComplex R` is descended along the cokernel projection `C.homologyπ n`
  (`kroneckerCocycDesc`), which is legitimate because a *cocycle* pairs trivially with a boundary;
* the resulting map `kroneckerLin n : Zⁿ(X;R) ⟶ (Hₙ(X;R) →ₗ[R] R)` on the cycles of the cochain
  complex kills boundaries of the cochain complex (a coboundary pairs trivially with a cycle), so it
  descends along `(SSetCochainComplex R X).homologyπ n` (`Work.Cohomology.descH`), giving
  `kroneckerMap n : Hⁿ(X;R) ⟶ (Hₙ(X;R) →ₗ[R] R)`.

## Main results

* `kroneckerMap_apply` — the value of the descended pairing on the class of a cycle;
* `kronecker_descent` — **the Kronecker pairing on (co)homology**, with the computation rule
  `⟨[α], [z]⟩ = α(z)`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R] (X : SSet)

/-! ## Descending a cocycle's functional to the homology of the chains -/

/-- Evaluation of a cochain on the cycles of the chain complex `X.chainComplex R`, as a linear map
in the cochain. -/
def kroneckerCycEval (n : ℕ) :
    (↥((X.chainComplex (ModuleCat.of R R)).X n) →ₗ[R] R) →ₗ[R]
      (↥((X.chainComplex (ModuleCat.of R R)).cycles n) →ₗ[R] R) where
  toFun α := α.comp ((X.chainComplex (ModuleCat.of R R)).iCycles n).hom
  map_add' a b := by ext z; simp
  map_smul' r a := by ext z; simp

/-- The same, as a morphism of modules. -/
def kroneckerCycEvalHom (n : ℕ) (α : ↥((X.chainComplex (ModuleCat.of R R)).X n) →ₗ[R] R) :
    (X.chainComplex (ModuleCat.of R R)).cycles n ⟶ ModuleCat.of R R :=
  ModuleCat.ofHom (kroneckerCycEval R X n α)

/-- A cochain pairs to zero with a boundary: this is what makes the descent below possible. -/
lemma toCycles_kroneckerCycEvalHom (n : ℕ) (α : ↥((X.chainComplex (ModuleCat.of R R)).X n) →ₗ[R] R)
    (hα : cochainDiff R X α = 0) :
    (X.chainComplex (ModuleCat.of R R)).toCycles (n + 1) n ≫ kroneckerCycEvalHom R X n α = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  show α (((X.chainComplex (ModuleCat.of R R)).iCycles n).hom
    (((X.chainComplex (ModuleCat.of R R)).toCycles (n + 1) n).hom y)) = 0
  have h := congrArg (fun (g : (X.chainComplex (ModuleCat.of R R)).X (n + 1) ⟶
      (X.chainComplex (ModuleCat.of R R)).X n) => g.hom y)
    (HomologicalComplex.toCycles_i (X.chainComplex (ModuleCat.of R R)) (n + 1) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  change (cochainDiff R X α) y = 0
  rw [hα]
  rfl

/-- **Descent in the chain variable.**  The functional on the cycles of the chains given by a
*cocycle* factors through the homology: this is the map `Hₙ(X;R) →ₗ[R] R`, `[z] ↦ α(z)`. -/
def kroneckerCocycDesc (n : ℕ) (α : ↥((X.chainComplex (ModuleCat.of R R)).X n) →ₗ[R] R)
    (hα : cochainDiff R X α = 0) :
    (X.chainComplex (ModuleCat.of R R)).homology n ⟶ ModuleCat.of R R :=
  ((X.chainComplex (ModuleCat.of R R)).homologyIsCokernel (n + 1) n (ChainComplex.prev ℕ n)).desc
    (CokernelCofork.ofπ (kroneckerCycEvalHom R X n α) (toCycles_kroneckerCycEvalHom R X n α hα))

/-- Computation rule for `kroneckerCocycDesc`. -/
lemma homologyπ_kroneckerCocycDesc (n : ℕ)
    (α : ↥((X.chainComplex (ModuleCat.of R R)).X n) →ₗ[R] R)
    (hα : cochainDiff R X α = 0) :
    (X.chainComplex (ModuleCat.of R R)).homologyπ n ≫ kroneckerCocycDesc R X n α hα =
      kroneckerCycEvalHom R X n α := by
  exact Cofork.IsColimit.π_desc
    (s := CokernelCofork.ofπ ((X.chainComplex (ModuleCat.of R R)).homologyπ n)
      (HomologicalComplex.toCycles_comp_homologyπ (X.chainComplex (ModuleCat.of R R)) (n + 1) n))
    (t := CokernelCofork.ofπ (kroneckerCycEvalHom R X n α)
      (toCycles_kroneckerCycEvalHom R X n α hα))
    (((X.chainComplex (ModuleCat.of R R)).homologyIsCokernel (n + 1) n (ChainComplex.prev ℕ n)))

/-- Computation rule for `kroneckerCocycDesc` on the class of a cycle. -/
lemma kroneckerCocycDesc_apply (n : ℕ) (α : ↥((X.chainComplex (ModuleCat.of R R)).X n) →ₗ[R] R)
    (hα : cochainDiff R X α = 0) (c : (X.chainComplex (ModuleCat.of R R)).cycles n) :
    (kroneckerCocycDesc R X n α hα).hom
      (((X.chainComplex (ModuleCat.of R R)).homologyπ n).hom c) =
      α (((X.chainComplex (ModuleCat.of R R)).iCycles n).hom c) := by
  have h := congrArg (fun (g : (X.chainComplex (ModuleCat.of R R)).cycles n ⟶ ModuleCat.of R R)
    => g.hom c) (homologyπ_kroneckerCocycDesc R X n α hα)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, kroneckerCycEvalHom, ModuleCat.hom_ofHom,
    kroneckerCycEval, LinearMap.comp_apply] at h
  exact h

/-! ## The pairing of a cocycle with the homology of the chains -/

/-- The cochain underlying a cycle of the cochain complex (the same term, with the type written out
explicitly so that it may be applied as a function). -/
def cochainOfCycle (n : ℕ) (z : (SSetCochainComplex R X).cycles n) :
    ↥((X.chainComplex (ModuleCat.of R R)).X n) →ₗ[R] R :=
  ((SSetCochainComplex R X).iCycles n).hom z

/-- `cochainOfCycle` is additive. -/
lemma cochainOfCycle_add (n : ℕ) (z z' : (SSetCochainComplex R X).cycles n) :
    cochainOfCycle R X n (z + z') = cochainOfCycle R X n z + cochainOfCycle R X n z' := by
  rw [cochainOfCycle, cochainOfCycle, cochainOfCycle, iCycles_add]

/-- `cochainOfCycle` is homogeneous. -/
lemma cochainOfCycle_smul (n : ℕ) (a : R) (z : (SSetCochainComplex R X).cycles n) :
    cochainOfCycle R X n (a • z) = a • cochainOfCycle R X n z := by
  rw [cochainOfCycle, cochainOfCycle, iCycles_smul]

/-- The cochain of a boundary of the cochain complex is the coboundary of the cochain. -/
lemma cochainOfCycle_toCycles (n : ℕ) (x : (SSetCochainComplex R X).X n) :
    cochainOfCycle R X (n + 1) ((SSetCochainComplex R X).toCycles n (n + 1) x)
      = cochainDiff R X x := by
  rw [cochainOfCycle, iCycles_toCycles, SSetCochainComplex_d_apply]

/-- The cochain underlying `cocycleOf` is the cocycle itself. -/
lemma cochainOfCycle_cocycleOf (n : ℕ)
    (α : ↥((X.chainComplex (ModuleCat.of R R)).X n) →ₗ[R] R) (h : cochainDiff R X α = 0) :
    cochainOfCycle R X n (cocycleOf R X α h) = α := by
  rw [cochainOfCycle]
  exact iCycles_cocycleOf R X α h

/-- For a cycle `z` of the cochain complex, the pairing `⟨z, ·⟩ : Hₙ(X;R) ⟶ R`. -/
def kroneckerFun (n : ℕ) (z : (SSetCochainComplex R X).cycles n) :
    ((X.chainComplex (ModuleCat.of R R)).homology n) →ₗ[R] R :=
  (kroneckerCocycDesc R X n (cochainOfCycle R X n z) (cochainDiff_iCycles R X n z)).hom

/-- The value of `kroneckerFun` on the class of a cycle: `⟨z, [c]⟩ = z(c)`. -/
lemma kroneckerFun_apply (n : ℕ) (z : (SSetCochainComplex R X).cycles n)
    (c : (X.chainComplex (ModuleCat.of R R)).cycles n) :
    kroneckerFun R X n z (((X.chainComplex (ModuleCat.of R R)).homologyπ n).hom c) =
      cochainOfCycle R X n z (((X.chainComplex (ModuleCat.of R R)).iCycles n).hom c) :=
  kroneckerCocycDesc_apply R X n _ _ c

lemma kroneckerFun_add (n : ℕ) (z z' : (SSetCochainComplex R X).cycles n) :
    kroneckerFun R X n (z + z') = kroneckerFun R X n z + kroneckerFun R X n z' := by
  apply LinearMap.ext
  intro y
  obtain ⟨c, rfl⟩ :=
    (ModuleCat.epi_iff_surjective
      ((X.chainComplex (ModuleCat.of R R)).homologyπ n)).mp inferInstance y
  rw [LinearMap.add_apply, kroneckerFun_apply, kroneckerFun_apply, kroneckerFun_apply,
    cochainOfCycle_add, LinearMap.add_apply]

lemma kroneckerFun_smul (n : ℕ) (a : R) (z : (SSetCochainComplex R X).cycles n) :
    kroneckerFun R X n (a • z) = a • kroneckerFun R X n z := by
  apply LinearMap.ext
  intro y
  obtain ⟨c, rfl⟩ :=
    (ModuleCat.epi_iff_surjective
      ((X.chainComplex (ModuleCat.of R R)).homologyπ n)).mp inferInstance y
  rw [LinearMap.smul_apply, kroneckerFun_apply, kroneckerFun_apply,
    cochainOfCycle_smul, LinearMap.smul_apply]

/-- The pairing of a cocycle with the homology of the chains, as a linear map in the cocycle. -/
def kroneckerLin (n : ℕ) : (SSetCochainComplex R X).cycles n →ₗ[R]
    (((X.chainComplex (ModuleCat.of R R)).homology n) →ₗ[R] R) where
  toFun := kroneckerFun R X n
  map_add' := kroneckerFun_add R X n
  map_smul' := kroneckerFun_smul R X n

/-- The value of `kroneckerLin` on the class of a cycle. -/
lemma kroneckerLin_apply (n : ℕ) (z : (SSetCochainComplex R X).cycles n)
    (c : (X.chainComplex (ModuleCat.of R R)).cycles n) :
    kroneckerLin R X n z (((X.chainComplex (ModuleCat.of R R)).homologyπ n).hom c) =
      cochainOfCycle R X n z (((X.chainComplex (ModuleCat.of R R)).iCycles n).hom c) :=
  kroneckerCocycDesc_apply R X n _ _ c

/-! ## Descent in the cohomological variable -/

/-- **A coboundary pairs to zero with every cycle.**  This is what allows the pairing to descend to
the cohomology in the first variable. -/
lemma toCycles_kroneckerLin (n : ℕ) :
    (SSetCochainComplex R X).toCycles ((ComplexShape.up ℕ).prev n) n ≫
      ModuleCat.ofHom (kroneckerLin R X n) = 0 := by
  generalize hpn : (ComplexShape.up ℕ).prev n = pn
  rcases n with _ | n'
  · have hpn' : pn = 0 := by rw [← hpn]; simp
    rw [hpn']
    rw [HomologicalComplex.toCycles_eq_zero _ (by simp [ComplexShape.up_Rel])]
    simp
  · have hpn' : pn = n' := by rw [← hpn]; simp
    rw [hpn']
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx : kroneckerLin R X (n' + 1)
        ((SSetCochainComplex R X).toCycles n' (n' + 1) x) = 0 := by
      apply LinearMap.ext
      intro y
      obtain ⟨c, rfl⟩ :=
        (ModuleCat.epi_iff_surjective
          ((X.chainComplex (ModuleCat.of R R)).homologyπ (n' + 1))).mp inferInstance y
      rw [kroneckerLin_apply]
      rw [cochainOfCycle_toCycles R X n' x]
      simp only [cochainDiff, LinearMap.comp_apply]
      have hc := congrArg (fun (g : (X.chainComplex (ModuleCat.of R R)).cycles (n' + 1) ⟶
          (X.chainComplex (ModuleCat.of R R)).X n') => g.hom c)
        (HomologicalComplex.iCycles_d (X.chainComplex (ModuleCat.of R R)) (n' + 1) n')
      simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
        LinearMap.zero_apply] at hc
      rw [hc]
      simp
    simpa using hx

/-- **The Kronecker pairing of a cohomology class with a homology class**:
`Hⁿ(X;R) ⟶ (Hₙ(X;R) →ₗ[R] R)`. -/
def kroneckerMap (n : ℕ) : (SSetCochainComplex R X).homology n ⟶
    ModuleCat.of R (((X.chainComplex (ModuleCat.of R R)).homology n) →ₗ[R] R) :=
  descH R X n (ModuleCat.ofHom (kroneckerLin R X n)) (toCycles_kroneckerLin R X n)

/-- The value of the Kronecker pairing on the class of a cycle. -/
lemma kroneckerMap_apply (n : ℕ) (z : (SSetCochainComplex R X).cycles n) :
    (kroneckerMap R X n).hom ((SSetCochainComplex R X).homologyπ n z) =
      kroneckerFun R X n z :=
  descH_apply R X _ _ z

/-- **The Kronecker pairing descends to (co)homology.**  There is a pairing of the `n`-th cohomology
with the `n`-th homology, `⟨·, ·⟩ : Hⁿ(X;R) ⟶ (Hₙ(X;R) →ₗ[R] R)`, whose value on the class of a
cocycle `α` and the class of a cycle `z` is the evaluation `α z`. -/
theorem kronecker_descent (R : Type) [CommRing R] (X : SSet) :
    ∃ kron : ∀ n : ℕ, (Work.Cohomology.SSetCochainComplex R X).homology n →ₗ[R]
        (((X.chainComplex (ModuleCat.of R R)).homology n) →ₗ[R] R),
      ∀ (n : ℕ) (α : Work.Cohomology.Cochain R X n)
        (hα : Work.Cohomology.cochainDiff R X α = 0)
        (z : (X.chainComplex (ModuleCat.of R R)).cycles n),
        kron n (Work.Cohomology.cohomologyClassOf R X α hα)
          (((X.chainComplex (ModuleCat.of R R)).homologyπ n).hom z) =
          α (((X.chainComplex (ModuleCat.of R R)).iCycles n).hom z) := by
  refine ⟨fun n => (kroneckerMap R X n).hom, ?_⟩
  intro n α hα z
  rw [show cohomologyClassOf R X α hα
      = (SSetCochainComplex R X).homologyπ n (cocycleOf R X α hα) from rfl,
    kroneckerMap_apply R X n (cocycleOf R X α hα), kroneckerFun_apply,
    cochainOfCycle_cocycleOf R X n α hα]

end

end Work.Cohomology
