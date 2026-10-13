import Mathlib
import Submission.Work.DSMX0U.Cell
import Submission.Work.DSMX0U.exists_gen_sigma

/-!
# DSMX0U — one step of the cell construction

This file proves `Work.DSMX0U.stepData_exists`: given the state `s : Cell A C c₀ q` of the cell
construction in the degrees `[q - 1, q]` (see `Submission/Work/DSMX0U/Cell.lean`), a cochain
complex `C` of `A`-modules over a Noetherian ring `A` whose cohomology in degree `(q - 1) - 1` is
finitely generated, and a cocycle `c₀ : A ⟶ C⁰`, the data `StepData A s` producing the *next* cell
`stepCell A s sd : Cell A C c₀ (q - 1)` exists.

## The three ingredients

* **The generators** (`gen`, `σ`, `hσ`, `hcoaugσ`): a finitely generated free module whose cycles
  hit every class of `H^((q-1)-1)(C)` modulo boundaries, plus, when the new degree is `0`, one
  generator carrying *exactly* the coaugmentation cycle `c₀ 1` (legitimate by `hc₀`).  This is
  `Work.DSMX0U.exists_gen_sigma`, applied with `d = (q - 1) - 1`; it uses only the finiteness of
  the cohomology.
* **The relations** (`rel`, `cov`, `hcov`): a finite free module covering the excess kernel
  `Cell.K s ⊆ Cell.G s`.  Since `A` is Noetherian and `Cell.G s = gen × rel` is finitely generated,
  every submodule of it is finitely generated, hence covered by a finite free module.
* **The lift** (`β`, `hβ`): the chain-map condition for the relations.  By definition of the excess
  kernel, `φ (Cell.K s) ⊆ im (C.d ((q-1)-1) (q-1))`; since `rel` is free, `s.φ` restricted to the
  relations lifts along the differential `C.d ((q-1)-1) (q-1)`.

## The degree bookkeeping

The new degree is `(q - 1) - 1`, whereas `exists_gen_sigma` speaks of an arbitrary degree `d` and
of the *successor* degree `d + 1` (the degree in which the "cycle" hypothesis lives).  The single
arithmetic identity `((q - 1) - 1) + 1 = q - 1` (proved by `ring`) is what converts between them.
-/

namespace Work.DSMX0U

open CategoryTheory

universe a

set_option linter.style.haveILetI false

section Lift

variable {A : Type a} [CommRing A]

/-- A linear map `g : P → N` from a **free** module `P` into the range of a linear map
`f : M → N` lifts along `f`.  (Freeness of `P` is exactly the projectivity needed here;
`f` itself need not be surjective.) -/
lemma free_lift_of_mem_range {P : Type a} [AddCommGroup P] [Module A P] [Module.Free A P]
    {M : Type a} [AddCommGroup M] [Module A M]
    {N : Type a} [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (g : P →ₗ[A] N) (h : ∀ x, g x ∈ LinearMap.range f) :
    ∃ β : P →ₗ[A] M, f.comp β = g := by
  let b := Module.Free.chooseBasis A P
  refine ⟨(b.constr A (fun i => Classical.choose (h (b i))) : P →ₗ[A] M), ?_⟩
  apply b.ext
  intro i
  simp only [LinearMap.comp_apply, Module.Basis.constr_basis]
  exact Classical.choose_spec (h (b i))

end Lift

theorem stepData_exists {A : Type a} [CommRing A] [IsNoetherianRing A]
    {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0} {q : ℤ}
    (hc₀ : ∀ j : ℤ, CategoryTheory.CategoryStruct.comp c₀ (C.d 0 j) = 0)
    (s : Work.DSMX0U.Cell A C c₀ q)
    (hfg : Module.Finite A (C.homology ((q - 1) - 1))) :
    Nonempty (Work.DSMX0U.StepData A s) := by
  -- the generators of the cycles of `C` in the new degree `(q - 1) - 1`
  obtain ⟨gen, hgenFree, hgenFin, σ, hσgen, hcoauggen⟩ :=
    exists_gen_sigma (C := C) (c₀ := c₀) (d := (q - 1) - 1) hc₀ hfg
  haveI := hgenFree
  haveI := hgenFin
  -- the arithmetic identity relating the successor degree of the new degree to `q - 1`
  have hsucc : ((q - 1) - 1) + 1 = (q - 1) := by ring
  -- ## the relations: a finite free cover of the excess kernel
  haveI hGfin : Module.Finite A ↥(s.G A) := by
    haveI := s.finiteGen
    haveI := s.finiteRel
    exact inferInstance
  haveI hGnoeth : IsNoetherian A ↥(s.G A) := isNoetherian_of_isNoetherianRing_of_finite A _
  have hKfin : Module.Finite A ↥(s.K A) :=
    Module.Finite.iff_fg.mpr ((isNoetherian_def.mp hGnoeth) (s.K A))
  obtain ⟨n, cov, hcov⟩ := Module.Finite.exists_fin' A ↥(s.K A)
  -- ## the lift `β`
  -- an element of the excess kernel is mapped by `φ` into the range of the differential
  have hmemK : ∀ x : ↥(s.K A),
      (s.φHom A) ((x : ↥(s.K A)) : ↥(s.G A)) ∈
        LinearMap.range (C.d ((q - 1) - 1) (q - 1)).hom := by
    intro x
    have hx := x.2
    simp only [Cell.K] at hx
    have hx2 := (Submodule.mem_inf.mp hx).2
    have h2 : (bdryQ A C (q - 1)) ((s.φHom A) ((x : ↥(s.K A)) : ↥(s.G A))) = 0 := by
      simpa only [LinearMap.comp_apply, LinearMap.mem_ker] using hx2
    have h3 : (s.φHom A) ((x : ↥(s.K A)) : ↥(s.G A)) ∈
        LinearMap.ker (Submodule.mkQ (LinearMap.range (C.d ((q - 1) - 1) (q - 1)).hom)) := by
      simp only [bdryQ] at h2
      exact LinearMap.mem_ker.mpr h2
    simpa only [Submodule.ker_mkQ] using h3
  have hrange : ∀ x : Fin n → A, ((s.φHom A).comp ((s.K A).subtype.comp cov)) x ∈
      LinearMap.range (C.d ((q - 1) - 1) (q - 1)).hom := by
    intro x
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply] using hmemK (cov x)
  obtain ⟨β, hβc⟩ := free_lift_of_mem_range ((C.d ((q - 1) - 1) (q - 1)).hom)
    ((s.φHom A).comp ((s.K A).subtype.comp cov)) hrange
  have hβ : ∀ x : Fin n → A,
      (C.d ((q - 1) - 1) (q - 1)).hom (β x) =
        (s.φHom A) ((cov x : ↥(s.K A)) : ↥(s.G A)) := by
    intro x
    have h := congrArg (fun (g : (Fin n → A) →ₗ[A] ↥(C.X (q - 1))) => g x) hβc
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply] using h
  -- ## the cohomology condition, transported across `((q - 1) - 1) + 1 = q - 1`
  have hσ : ∀ z : ↥(C.X ((q - 1) - 1)), (C.d ((q - 1) - 1) (q - 1)).hom z = 0 →
      ∃ g : ↥gen, (C.iCycles ((q - 1) - 1)).hom (σ.hom g) - z ∈
        LinearMap.range (C.d (((q - 1) - 1) - 1) ((q - 1) - 1)).hom := by
    intro z hz
    refine hσgen z ?_
    rw [hsucc]
    exact hz
  exact ⟨{
    gen := gen
    rel := ModuleCat.of A (Fin n → A)
    freeGen := hgenFree
    finiteGen := hgenFin
    freeRel := inferInstance
    finiteRel := inferInstance
    σ := σ
    hσ := hσ
    hcoaugσ := hcoauggen
    cov := cov
    hcov := hcov
    β := β
    hβ := fun x => hβ x }⟩

end Work.DSMX0U
