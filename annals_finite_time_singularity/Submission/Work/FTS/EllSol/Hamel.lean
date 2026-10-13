/-
# `Work.FTS.EllSol.Hamel` — item (e): the Hamel-basis assembly

Abstract form of the last step of the design: if a *solution class* `P` is

* inhabited at `(0,0)`,
* closed under linear combinations `(g, Ψ) + c • (g', Ψ')` (for `g, g'` in the Galerkin class),
* inhabited over every profile of the Galerkin class, and if the Galerkin class is itself a
subspace (item (a)),

then there is a **linear** operator `EllSol : Fn →ₗ[ℝ] Fn` whose values on the Galerkin class are
solutions in `P`.  This is exactly the design's "pick a solution on a Hamel basis of the
subspace, then extend with `LinearMap.exists_extend`", and it is the reason the design needs
neither uniqueness nor a canonical choice of the elliptic solution.

The construction is `Basis.ofVectorSpace` on the submodule spanned by the class, `Basis.constr`
for the values, and `LinearMap.exists_extend` for the passage from the subspace to all of `Fn`.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.DFinsupp
import Submission.Work.FTS.EllSol.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Module

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

variable {α : ℝ} {P : Fn → Fn → Prop}

/-- **The Hamel-basis assembly (item (e)).** -/
theorem exists_linear_selector
    (hG0 : Work.FTS.Nonlin.GalClass α (0 : Fn))
    (hGlin : ∀ g g' : Fn, ∀ c : ℝ, Work.FTS.Nonlin.GalClass α g →
      Work.FTS.Nonlin.GalClass α g' → Work.FTS.Nonlin.GalClass α (g + c • g'))
    (hP0 : P 0 0)
    (hPlin : ∀ g g' Ψ Ψ' : Fn, ∀ c : ℝ, Work.FTS.Nonlin.GalClass α g →
      Work.FTS.Nonlin.GalClass α g' → P g Ψ → P g' Ψ' → P (g + c • g') (Ψ + c • Ψ'))
    (hex : ∀ g, Work.FTS.Nonlin.GalClass α g → ∃ Ψ, P g Ψ) :
    ∃ EllSol : Fn →ₗ[ℝ] Fn,
      ∀ g, Work.FTS.Nonlin.GalClass α g → P g (EllSol g) := by
  classical
  -- the submodule spanned by the Galerkin class
  let S : Submodule ℝ Fn := Submodule.span ℝ {g : Fn | Work.FTS.Nonlin.GalClass α g}
  -- every element of `S` is in the class
  have hGS : ∀ x : Fn, x ∈ S → Work.FTS.Nonlin.GalClass α x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact hG0
    | add a b _ _ ha hb => simpa using hGlin a b 1 ha hb
    | smul c a _ ha => simpa using hGlin 0 a c hG0 ha
  -- a Hamel basis of `S` and the values of the linear map on it
  let b : Basis (Module.Basis.ofVectorSpaceIndex ℝ S) ℝ S := Basis.ofVectorSpace ℝ S
  let σ : S →ₗ[ℝ] Fn := Submodule.subtype S
  have hσb : ∀ i, σ (b i) = ((b i : S) : Fn) := fun i => rfl
  have hb : ∀ i, Work.FTS.Nonlin.GalClass α (σ (b i)) := fun i => hGS _ (b i).2
  let solB : Module.Basis.ofVectorSpaceIndex ℝ S → Fn :=
    fun i => Classical.choose (hex _ (hb i))
  have hsolB : ∀ i, P (σ (b i)) (solB i) := fun i => Classical.choose_spec (hex _ (hb i))
  let f : S →ₗ[ℝ] Fn := b.constr ℝ solB
  -- evaluating the two `Finsupp` sums at an inserted index
  have hsumS : ∀ (i : Module.Basis.ofVectorSpaceIndex ℝ S) (bb : ℝ)
      (c' : Module.Basis.ofVectorSpaceIndex ℝ S →₀ ℝ),
      ((Finsupp.single i bb + c').sum fun j a => a • b j : S)
        = bb • b i + c'.sum (fun j a => a • b j) := by
    intro i bb c'
    rw [Finsupp.sum_add_index' (fun j => by simp) (fun j x y => by simp [add_smul]),
      Finsupp.sum_single_index (by simp)]
  have hsumF : ∀ (i : Module.Basis.ofVectorSpaceIndex ℝ S) (bb : ℝ)
      (c' : Module.Basis.ofVectorSpaceIndex ℝ S →₀ ℝ),
      (Finsupp.single i bb + c').sum (fun j a => a • solB j)
        = bb • solB i + c'.sum (fun j a => a • solB j) := by
    intro i bb c'
    rw [Finsupp.sum_add_index' (fun j => by simp) (fun j x y => by simp [add_smul]),
      Finsupp.sum_single_index (by simp)]
  -- the key induction: on the support of the representation
  have key : ∀ c : Module.Basis.ofVectorSpaceIndex ℝ S →₀ ℝ,
      Work.FTS.Nonlin.GalClass α (σ (c.sum fun i a => a • b i)) →
      P (σ (c.sum fun i a => a • b i)) (c.sum fun i a => a • solB i) := by
    intro c
    induction c using Finsupp.induction with
    | zero =>
      intro _
      simpa using hP0
    | single_add i bb c' _ _ ih =>
      intro hGwhole
      -- the whole sum, split at the inserted index
      have hsplit : σ ((Finsupp.single i bb + c').sum fun j a => a • b j)
          = bb • σ (b i) + σ (c'.sum fun j a => a • b j) := by
        rw [hsumS i bb c', map_add, map_smul]
      -- the class of the two pieces
      have hG1 : Work.FTS.Nonlin.GalClass α (bb • σ (b i)) := by
        have h := hGlin 0 (σ (b i)) bb hG0 (hb i)
        simpa using h
      have hGtail : σ (c'.sum fun j a => a • b j)
          = σ ((Finsupp.single i bb + c').sum fun j a => a • b j) - bb • σ (b i) := by
        rw [hsplit]; abel
      have hG2 : Work.FTS.Nonlin.GalClass α (σ (c'.sum fun j a => a • b j)) := by
        have h := hGlin _ _ (-1) hGwhole hG1
        have h' : Work.FTS.Nonlin.GalClass α
            (σ ((Finsupp.single i bb + c').sum fun j a => a • b j) - bb • σ (b i)) := by
          simpa only [sub_eq_add_neg, neg_smul, one_smul] using h
        simpa only [hGtail] using h'
      have hIH := ih hG2
      have hP1 : P (bb • σ (b i)) (bb • solB i) := by
        simpa using hPlin 0 (σ (b i)) 0 (solB i) bb hG0 (hb i) hP0 (hsolB i)
      have hres0 := hPlin (bb • σ (b i)) (σ (c'.sum fun j a => a • b j))
        (bb • solB i) (c'.sum fun j a => a • solB j) 1 hG1 hG2 hP1 hIH
      have hres : P (bb • σ (b i) + σ (c'.sum fun j a => a • b j))
          (bb • solB i + c'.sum fun j a => a • solB j) := by
        simpa only [one_smul] using hres0
      rw [hsplit, hsumF i bb c']
      exact hres
  -- every element of `S` carries a solution
  have keyS : ∀ x : S, Work.FTS.Nonlin.GalClass α (σ x) → P (σ x) (f x) := by
    intro x hx
    have hsum : ((b.repr x).sum fun i a => a • b i : S) = x := by
      rw [← Finsupp.linearCombination_apply]
      exact Basis.linearCombination_repr b x
    have hrepr : σ ((b.repr x).sum fun i a => a • b i) = σ x := congrArg σ hsum
    have hfx : f x = (b.repr x).sum (fun i a => a • solB i) := by
      show (b.constr ℝ solB) x = _
      rw [Basis.constr_apply]
    rw [hfx, ← hrepr]
    exact key (b.repr x) (by rw [hrepr]; exact hx)
  -- extend `f` to all of `Fn`
  obtain ⟨EllSol, hEll⟩ := LinearMap.exists_extend f
  refine ⟨EllSol, ?_⟩
  intro g hg
  have hgS : g ∈ S := Submodule.subset_span hg
  have h1 : EllSol g = f ⟨g, hgS⟩ := by
    have := congr_fun (congr_arg DFunLike.coe hEll) (⟨g, hgS⟩ : S)
    simpa [LinearMap.comp_apply] using this
  rw [h1]
  exact keyS ⟨g, hgS⟩ (by change Work.FTS.Nonlin.GalClass α g; exact hg)

end Work.FTS.EllSol
