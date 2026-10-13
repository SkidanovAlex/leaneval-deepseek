import Mathlib
import Submission.Work.DSMX0U.Cell
import Submission.Work.DSMX0U.FallbackGenSigma

/-!
# DSMX0U — the base cell of the tower, with vanishing differential

This file proves `Work.DSMX0U.baseCell_exists2`: over a Noetherian ring `A`, for a cochain complex
`C` of `A`-modules whose cohomology in degree `M` is finitely generated and a cocycle
`c₀ : A ⟶ C⁰`, there is a base cell `s : Work.DSMX0U.Cell A C c₀ (M + 1)` — a cell whose current
degree is `M` — whose differential `Cell.d A s : Cell.G s ⟶ s.Gprev` **vanishes**.

## The construction

A cell in degrees `[q - 1, q]` carries generators (mapped to cycles of `C`, hitting the cohomology
modulo boundaries) and relations (covering the excess kernel `Cell.K s` of the next level up).  Its
differential `Cell.d s` is the coproduct of the zero map on the generators with the composite
`Kprev.subtype ∘ cov`.  Hence `Cell.d s = 0` as soon as `cov = 0`; this is compatible with the
surjectivity requirement `hcov` precisely when the excess kernel `Kprev` of the next level up is
trivial.

We therefore take

* `gen` with `σ : gen ⟶ Z^M(C)` and the two properties (`hσ`, `hcoaugσ`) furnished by
  `Work.DSMX0U.Fallback.step_gen_sigma_aux` at the degree `(M + 1) - 1 = M` — a finitely generated
  free module whose cycles hit every class of `H^M(C)` modulo boundaries, together with a generator
  carrying exactly the coaugmentation cycle `c₀ 1` when `M = 0`;
* `rel = zmod A`, `Gprev = zmod A` with `Kprev = ⊥` (the whole of the trivial module, hence a
  subsingleton), and `cov = 0`, `φprev = 0`, `β = 0`.

Then `cov = 0` is surjective onto the subsingleton `↥Kprev`, the chain-map condition `hβ` is
vacuous, and the differential is `coprod 0 (Kprev.subtype ∘ 0) = 0`.
-/

namespace Work.DSMX0U

open CategoryTheory

universe a

set_option linter.style.haveILetI false

theorem baseCell_exists2 {A : Type a} [CommRing A] [IsNoetherianRing A]
    {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0} {M : ℤ}
    (hc₀ : ∀ j : ℤ, CategoryTheory.CategoryStruct.comp c₀ (C.d 0 j) = 0)
    (hfg : Module.Finite A (C.homology M)) :
    ∃ s : Work.DSMX0U.Cell A C c₀ (M + 1),
      Work.DSMX0U.Cell.d A s = 0 := by
  -- The cell is `Cell A C c₀ (M + 1)`, so its current degree is `(M + 1) - 1 = M`.
  have hd : (M + 1) - 1 = M := by ring
  have hsucc : ((M + 1) - 1) + 1 = M + 1 := by ring
  have hfg' : Module.Finite A (C.homology ((M + 1) - 1)) := by rw [hd]; exact hfg
  -- The generators of `H^M(C)`: a finite free module whose cycles hit every class of `H^M(C)`
  -- modulo boundaries, with a generator carrying the coaugmentation cycle when `M = 0`.
  obtain ⟨gen, hgenFree, hgenFin, σ, hσgen, hcoauggen⟩ :=
    Fallback.step_gen_sigma_aux (C := C) (c₀ := c₀) (d := (M + 1) - 1) hc₀ hfg'
  -- The base cell: generators as above, trivial relations, trivial previous level.
  refine ⟨{ gen := gen
            rel := zmod A
            freeGen := hgenFree
            finiteGen := hgenFin
            freeRel := inferInstance
            finiteRel := inferInstance
            σ := σ
            hσ := ?_
            hcoaugσ := hcoauggen
            Gprev := zmod A
            Kprev := ⊥
            cov := 0
            hcov := ?_
            φprev := 0
            β := 0
            hβ := ?_ }, ?_⟩
  · -- The generators hit the cohomology: `C.d ((M+1)-1) (M+1) = C.d d (d + 1)`.
    intro z hz
    exact hσgen z (by rw [hsucc]; exact hz)
  · -- The relations cover the (trivial) excess kernel: `↥Kprev` is a subsingleton.
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩
  · -- The chain-map condition on the relations is vacuous.
    intro x
    simp only [LinearMap.zero_apply, ModuleCat.hom_zero, map_zero]
  · -- The differential vanishes: `Cell.d s = ofHom (coprod 0 (Kprev.subtype ∘ 0)) = 0`.
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨p, u⟩ := x
    simp only [Cell.d, Cell.dHom, ModuleCat.hom_ofHom, LinearMap.coprod_apply,
      LinearMap.zero_apply, LinearMap.comp_apply, ModuleCat.hom_zero, map_zero, add_zero]

end Work.DSMX0U
