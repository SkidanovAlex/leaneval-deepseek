import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Submission.Work.FTS.ClassC.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

/-- **Linear selection from a linear relation.**  Let `C` be a class of profiles that contains `0`
and is closed under the operation `(g, g') ↦ g + c • g'` (hence, taking `c = 1` and, with `0 ∈ C`,
`c` arbitrary, it is a linear subspace), and let `P` be a relation which is likewise `0`-inhabited
and closed under the same operation in both variables.  If every `g ∈ C` is `P`-related to some
`Ψ`, then there is a *linear* selector `E` with `P g (E g)` for every `g ∈ C`.

The proof: the pairs `(g, Ψ)` with `g ∈ C` and `P g Ψ` form a submodule `S ≤ Fn × Fn`; its
first-coordinate projection `π : S →ₗ[ℝ] Fn` is onto the subspace `D = {g | C g}`, and since every
vector space over `ℝ` is a free (hence projective) module, `π` splits: there is a linear
`σ : D →ₗ[ℝ] S` with `π ∘ σ = id`.  Composing with the second coordinate gives a linear selector
`E₀ : D →ₗ[ℝ] Fn` over `D`; it is extended to all of `Fn` by `LinearMap.exists_extend`. -/
theorem exists_linear_selector {α : ℝ} {C : Work.FTS.Galerkin.Fn → Prop}
    {P : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → Prop}
    (hC0 : C 0)
    (hClin : ∀ g g' : Work.FTS.Galerkin.Fn, ∀ c : ℝ, C g → C g' → C (g + c • g'))
    (hP0 : P 0 0)
    (hPlin : ∀ g g' Ψ Ψ' : Work.FTS.Galerkin.Fn, ∀ c : ℝ, C g → C g' →
      P g Ψ → P g' Ψ' → P (g + c • g') (Ψ + c • Ψ'))
    (hex : ∀ g, C g → ∃ Ψ, P g Ψ) :
    ∃ E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn, ∀ g, C g → P g (E g) := by
  -- `C` is closed under addition and under scalar multiplication.
  have hCadd : ∀ g g', C g → C g' → C (g + g') := by
    intro g g' hg hg'
    have h := hClin g g' 1 hg hg'
    simpa using h
  have hCsmul : ∀ (c : ℝ) g, C g → C (c • g) := by
    intro c g hg
    have h := hClin 0 g c hC0 hg
    simpa using h
  -- The graph of the relation, restricted to `C`, is a submodule of `Fn × Fn`.
  let S : Submodule ℝ (Work.FTS.Galerkin.Fn × Work.FTS.Galerkin.Fn) :=
    { carrier := {x | C x.1 ∧ P x.1 x.2}
      zero_mem' := ⟨hC0, hP0⟩
      add_mem' := by
        rintro ⟨g, Ψ⟩ ⟨g', Ψ'⟩ ⟨hg, hP⟩ ⟨hg', hP'⟩
        refine ⟨hCadd g g' hg hg', ?_⟩
        have h := hPlin g g' Ψ Ψ' 1 hg hg' hP hP'
        simpa using h
      smul_mem' := by
        rintro c ⟨g, Ψ⟩ ⟨hg, hP⟩
        refine ⟨hCsmul c g hg, ?_⟩
        have h := hPlin 0 g 0 Ψ c hC0 hg hP0 hP
        simpa using h }
  -- First-coordinate projection of `S`, and its range `D`.
  let π : S →ₗ[ℝ] Work.FTS.Galerkin.Fn :=
    (LinearMap.fst ℝ Work.FTS.Galerkin.Fn Work.FTS.Galerkin.Fn).comp S.subtype
  let D : Submodule ℝ Work.FTS.Galerkin.Fn := LinearMap.range π
  have hmemD : ∀ g, g ∈ D ↔ C g := by
    intro g
    constructor
    · rintro ⟨x, hx⟩
      have hx' : x.1.1 = g := hx
      rw [← hx']
      exact x.2.1
    · intro hg
      obtain ⟨Ψ, hP⟩ := hex g hg
      exact ⟨⟨(g, Ψ), hg, hP⟩, rfl⟩
  let πD : S →ₗ[ℝ] D := π.codRestrict D (fun x => LinearMap.mem_range_self π x)
  have hsurj : Function.Surjective πD := by
    intro y
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x, Subtype.ext hx⟩
  -- `D` is a vector space over `ℝ`, hence free, hence projective.
  haveI : Module.Free ℝ D := Module.Free.of_divisionRing ℝ D
  -- Split the surjection `πD`.
  obtain ⟨σ, hσ⟩ := πD.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  let E₀ : D →ₗ[ℝ] Work.FTS.Galerkin.Fn :=
    ((LinearMap.snd ℝ Work.FTS.Galerkin.Fn Work.FTS.Galerkin.Fn).comp S.subtype).comp σ
  have hE₀ : ∀ y : D, P y (E₀ y) := by
    intro y
    have hσy : πD (σ y) = y := LinearMap.congr_fun hσ y
    have h1 : (σ y).1.1 = y.1 := by
      have h := congrArg Subtype.val hσy
      simpa [πD, π] using h
    have h3 : P (σ y).1.1 (σ y).1.2 := (σ y).2.2
    rw [← h1]
    exact h3
  -- Extend the selector from `D` to the whole space.
  obtain ⟨E, hE⟩ := LinearMap.exists_extend E₀
  refine ⟨E, fun g hg => ?_⟩
  have hgD : g ∈ D := (hmemD g).mpr hg
  have hEeq : E g = E₀ ⟨g, hgD⟩ := by
    have := LinearMap.congr_fun hE ⟨g, hgD⟩
    simpa using this
  rw [hEeq]
  exact hE₀ ⟨g, hgD⟩

end Work.FTS.ClassC
