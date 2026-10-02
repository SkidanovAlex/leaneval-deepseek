import Mathlib
import Submission.Work.Cohomology.uctDual
import Submission.Work.Cohomology.free_submodule_of_free_int

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A cocycle not orthogonal to the boundaries detects a cycle

For a `ℕ`-indexed chain complex `E` of `ℤ`-modules with free terms and `H_{n-1}(E) = 0`, a
cocycle `φ` of the dual complex `Hom(E, ℤ)` that is *not* a coboundary must be non-zero on some
cycle: there is `z ∈ Eₙ` with `∂z = 0` and `φ z ≠ 0`.

Equivalently (the form proved below): if `φ` kills all `n`-cycles then `φ = ψ ∘ ∂` for some
`ψ : E_{n-1} → ℤ`.  Indeed `φ` then factors through the boundaries `B_{n-1} = im ∂ ⊆ E_{n-1}`,
and since `H_{n-1}(E) = 0` the boundaries are the cycles `Z_{n-1} = ker ∂`, a submodule of the
free module `E_{n-1}` whose quotient is free (submodules of free `ℤ`-modules are free), hence a
direct summand: so the induced functional on `B_{n-1}` extends to `E_{n-1}`.

## Main results

* `Work.Whitney.CycleDetect.submodule_free_of_free_int` — freeness of a submodule of a free
  `ℤ`-module, in the instance normalisation used here;
* `Work.Whitney.CycleDetect.projective_quot_ker_of_free_int` — `M ⧸ ker f` is projective for
  `M`, `N` free;
* `Work.Whitney.CycleDetect.uctZ_le_uctB_of_isZero` — cycles are boundaries when `H_m = 0`;
* `Work.Whitney.CycleDetect.exists_retraction_uctR` — `E_m` retracts onto `im d_{m+1,m}`
  (the hypothesis `H_m = 0`), which is the retraction hypothesis of the dual universal
  coefficient theorem `Work.Cohomology.uctPsi_ker`;
* `Work.Whitney.CycleDetect.exists_cycle_of_notMem_range` — the requested statement.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

-- The module structure on a submodule (resp. a quotient by a submodule) of a `ℤ`-module is the
-- one induced from the ambient module, rather than `AddCommGroup.toIntModule`: this matches the
-- normalisation used in `Submission/Work/Cohomology/uctDefs.lean`.
attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

open CategoryTheory CategoryTheory.Limits

namespace Work.Whitney.CycleDetect

noncomputable section

universe u v

/-- A submodule of a free `ℤ`-module is free, in the instance normalisation of `Submodule.module`
(the two `ℤ`-module structures are propositionally — but not definitionally — equal). -/
lemma submodule_free_of_free_int {M : Type u} [AddCommGroup M] [Module ℤ M] [Module.Free ℤ M]
    (N : Submodule ℤ M) : Module.Free ℤ ↥N := by
  rw [show Submodule.module N = AddCommGroup.toIntModule ↥N from Subsingleton.elim _ _]
  exact Work.Cohomology.free_submodule_of_free_int N

/-- For free `ℤ`-modules `M`, `N` the quotient `M ⧸ ker f` is projective: it is isomorphic to the
range of `f`, a submodule of the free module `N`, hence free. -/
lemma projective_quot_ker_of_free_int {M : Type u} {N : Type v} [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] [AddCommGroup N] [Module ℤ N] [Module.Free ℤ N] (f : M →ₗ[ℤ] N) :
    Module.Projective ℤ (M ⧸ LinearMap.ker f) := by
  haveI : Module.Free ℤ ↥(LinearMap.range f) := submodule_free_of_free_int (LinearMap.range f)
  haveI : Module.Projective ℤ ↥(LinearMap.range f) := Module.Projective.of_free
  exact Module.Projective.of_equiv' (LinearMap.quotKerEquivRange f).symm

variable (E : ChainComplex (ModuleCat ℤ) ℕ)

/-- If the `m`-th homology of `E` vanishes then the `m`-cycles of `E` are exactly the
`m`-boundaries, expressed as `Z_m ≤ B_m` (the reverse inclusion holds always). -/
lemma uctZ_le_uctB_of_isZero (m : ℕ) (h : IsZero (E.homology m)) :
    Work.Cohomology.uctZ E m ≤ Work.Cohomology.uctB E m := by
  intro x hx
  obtain ⟨e⟩ := Work.Cohomology.homology_iso_H E m
  haveI : Subsingleton ↥(E.homology m) := ModuleCat.isZero_iff_subsingleton.mp h
  have hz : IsZero (ModuleCat.of ℤ (↥(Work.Cohomology.uctZ E m) ⧸ Work.Cohomology.uctH E m)) :=
    IsZero.of_iso h e.symm
  haveI : Subsingleton (↥(Work.Cohomology.uctZ E m) ⧸ Work.Cohomology.uctH E m) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  have h0 : (Work.Cohomology.uctH E m).mkQ ⟨x, hx⟩ = 0 := by
    have := @Subsingleton.elim _ this ((Work.Cohomology.uctH E m).mkQ ⟨x, hx⟩) 0
    simpa using this
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  exact (Work.Cohomology.mem_uctH E m ⟨x, hx⟩).mp h0

/-- **The retraction of `E_m` onto the boundaries `im d_{m+1,m}`**, which exist because `H_m = 0`.
This is the splitting hypothesis needed by the dual universal coefficient theorem, in the form
required by `Work.Cohomology.uctPsi_ker`. -/
lemma exists_retraction_uctR (m : ℕ) (hfree : ∀ k, Module.Free ℤ ↥(E.X k))
    (hexact : IsZero (E.homology m)) :
    ∃ r : ↥(E.X m) →ₗ[ℤ] ↥(Work.Cohomology.uctR E (m + 1)),
      r ∘ₗ (Work.Cohomology.uctR E (m + 1)).subtype = LinearMap.id := by
  haveI : Module.Free ℤ ↥(E.X m) := hfree m
  haveI : Module.Free ℤ ↥(E.X (m - 1)) := hfree (m - 1)
  have hproj : Module.Projective ℤ (↥(E.X m) ⧸ Work.Cohomology.uctZ E m) :=
    projective_quot_ker_of_free_int (E.d m (m - 1)).hom
  obtain ⟨ρ, hρ⟩ := Work.Cohomology.exists_retraction_onto_of_projective_quotient
    (Work.Cohomology.uctZ E m) hproj
  have hZeq : Work.Cohomology.uctZ E m = Work.Cohomology.uctR E (m + 1) :=
    le_antisymm (uctZ_le_uctB_of_isZero E m hexact) (Work.Cohomology.uctB_le_uctZ E m)
  refine ⟨(LinearEquiv.ofEq _ _ hZeq).toLinearMap.comp ρ, ?_⟩
  apply LinearMap.ext
  intro x
  have hmem : (Work.Cohomology.uctR E (m + 1)).subtype x ∈ Work.Cohomology.uctZ E m :=
    Work.Cohomology.uctB_le_uctZ E m x.2
  have hρx : ρ ((Work.Cohomology.uctR E (m + 1)).subtype x)
      = ⟨(Work.Cohomology.uctR E (m + 1)).subtype x, hmem⟩ := by
    have h := congrArg (fun (g : ↥(Work.Cohomology.uctZ E m) →ₗ[ℤ] ↥(Work.Cohomology.uctZ E m)) =>
      g ⟨(Work.Cohomology.uctR E (m + 1)).subtype x, hmem⟩) hρ
    simpa using h
  show (LinearEquiv.ofEq (Work.Cohomology.uctZ E m) (Work.Cohomology.uctR E (m + 1)) hZeq)
      (ρ ((Work.Cohomology.uctR E (m + 1)).subtype x)) = x
  rw [hρx]
  exact Subtype.ext rfl

/-- **A cocycle of the dual complex which is not a coboundary is non-zero on a cycle.**

If `φ ∈ Hom_ℤ(Eₙ, ℤ)` is a cocycle (`φ ∘ d_{n+1,n} = 0`), and `H_{n-1}(E) = 0` with all `E_k`
free, and `φ` is not of the form `ψ ∘ d_{n,n-1}`, then `φ` does not vanish on all `n`-cycles:
there is a cycle `z` with `φ z ≠ 0`. -/
theorem exists_cycle_of_notMem_range (E : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (hn : 1 ≤ n)
    (hfree : ∀ k, Module.Free ℤ ↥(E.X k))
    (hexact : CategoryTheory.Limits.IsZero (E.homology (n - 1)))
    (φ : ↥((Work.Cohomology.dualComplex ℤ E).X n))
    (hφ : ((Work.Cohomology.dualComplex ℤ E).d n (n + 1)).hom φ = 0)
    (hnot : ∀ ψ : ↥((Work.Cohomology.dualComplex ℤ E).X (n - 1)),
      ((Work.Cohomology.dualComplex ℤ E).d (n - 1) n).hom ψ ≠ φ) :
    ∃ z : ↥(E.X n), (E.d n (n - 1)).hom z = 0 ∧ (Work.Cohomology.dval E n φ) z ≠ 0 := by
  rcases n with _ | m
  · exact absurd hn (by simp)
  simp only [Nat.succ_sub_one] at hexact hnot ⊢
  -- suppose `φ` kills every `(m+1)`-cycle: then it factors through the comparison map `Ψ`
  by_contra hcon
  push Not at hcon
  have hkill : ∀ x : ↥(E.X (m + 1)), x ∈ Work.Cohomology.uctZ E (m + 1) →
      (Work.Cohomology.dval E (m + 1) φ) x = 0 := by
    intro x hx
    exact hcon x hx
  have hpsi : Work.Cohomology.uctPsi E (m + 1) ⟨φ, hφ⟩ = 0 := by
    apply LinearMap.ext
    intro w
    obtain ⟨x, rfl⟩ := (Work.Cohomology.uctH E (m + 1)).mkQ_surjective w
    rw [Work.Cohomology.uctPsi_apply, LinearMap.zero_apply]
    exact hkill x x.2
  -- the kernel of `Ψ` is the image of the transposed differential `dᵐ`
  obtain ⟨r, hr⟩ := exists_retraction_uctR E m hfree hexact
  have hker := Work.Cohomology.uctPsi_ker E (m + 1) ⟨r, hr⟩
  have hmem : ⟨φ, hφ⟩ ∈ Work.Cohomology.uctPre E (m + 1) := by
    rw [← hker]
    exact LinearMap.mem_ker.mpr hpsi
  obtain ⟨y, hy⟩ := hmem
  have hval : ((Work.Cohomology.dualComplex ℤ E).d m (m + 1)).hom y = φ := by
    have h := congrArg Subtype.val hy
    simpa [LinearMap.codRestrict_apply] using h
  exact hnot y hval

end

end Work.Whitney.CycleDetect
