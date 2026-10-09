import Mathlib
import Submission.Work.SSGRoute.PT.ClassFormation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Shapiro's lemma in degree zero for the coinduced module

For a group `G`, a subgroup `U ≤ G` and a `U`-module `M`, the coinduced module is

  `Coind^G_U M = { f : G → M // ∀ g u, f (g * u) = u⁻¹ • f g }`,

with the `G`-action `(g • f) x = f (g⁻¹ * x)`.  We show

  `H⁰(G, Coind^G_U M) ≅ H⁰(U, M)`,

where `H⁰ = invariants`.  Concretely a `G`-fixed element of `Coind^G_U M` is a *constant*
function whose value lies in `M^U`, and the isomorphism is `f ↦ f(1)` with inverse the constant
function.  This is the degree-zero case of Shapiro's lemma (Shapiro's isomorphism restricted to
`n = 0`), the input Milne's class-formation dévissage needs.
-/

namespace Work.SSGRoute.PT

open Work.GroupCohomology

section ShapiroH0

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (U : Subgroup G) {M : Type*} [AddCommGroup M] [DistribMulAction U M]

/-- A constant function `G → M` with `U`-invariant value lies in the coinduced module. -/
lemma const_mem_coindSub {m : M} (hm : ∀ u : U, u • m = m) :
    (fun _ : G => m) ∈ coindSub G U M := by
  intro g u
  change m = u⁻¹ • m
  have hu : u⁻¹ • m = m := by
    have h := congrArg (fun x : M => u⁻¹ • x) (hm u)
    rw [← mul_smul, inv_mul_cancel, one_smul] at h
    exact h.symm
  exact hu.symm

/-- The value at `1` of a `G`-fixed element of the coinduced module is `U`-fixed. -/
lemma val_one_mem_invariants (f : Coind G U M)
    (hf : f ∈ invariants G (Coind G U M)) : f.1 (1 : G) ∈ invariants U M := by
  rw [mem_invariants]
  intro u
  have h1 : f.1 (1 : G) = f.1 (u : G) := by
    have h := congrArg (fun z : Coind G U M => z.1 (u : G)) (hf (u : G))
    simpa [Coind.smul_apply] using h
  have h2 : f.1 (u : G) = u⁻¹ • f.1 (1 : G) := by
    simpa using Coind.coe_mul f (1 : G) u
  have h3 : u⁻¹ • f.1 (1 : G) = f.1 (1 : G) := by
    rw [← h2, h1]
  have h4 := congrArg (fun x : M => u • x) h3
  rw [smul_inv_smul] at h4
  exact h4.symm

/-- The constant function with value `c` (for `c ∈ M^U`) is a `G`-fixed element of the
coinduced module. -/
lemma const_mem_invariants (c : M) (hc : ∀ u : U, u • c = c) :
    (⟨fun _ : G => c, const_mem_coindSub U hc⟩ : Coind G U M) ∈
      invariants G (Coind G U M) := by
  rw [mem_invariants]
  intro g
  apply Subtype.ext
  funext x
  simp [Coind.smul_apply]

/-- A `G`-fixed element of the coinduced module is a constant function. -/
lemma eq_const_of_mem_invariants (f : Coind G U M)
    (hf : f ∈ invariants G (Coind G U M)) (g : G) : f.1 g = f.1 (1 : G) := by
  have h := congrArg (fun z : Coind G U M => z.1 g) (hf g)
  simpa [Coind.smul_apply] using h.symm

/-- **Shapiro's lemma in degree zero.**  Evaluation at `1` is an additive isomorphism
`H⁰(G, Coind^G_U M) ≃+ H⁰(U, M)`, with inverse the constant-function map. -/
noncomputable def shapiroH0AddEquiv :
    ↥(Work.AbsoluteKummer.H0 G (Coind G U M)) ≃+ ↥(Work.AbsoluteKummer.H0 U M) where
  toFun f := ⟨f.1.1 (1 : G), val_one_mem_invariants U f.1 f.2⟩
  invFun c := ⟨⟨fun _ : G => (c : M),
      const_mem_coindSub U (fun u => (mem_invariants U M (c : M)).1 c.2 u)⟩,
    const_mem_invariants U (c : M) (fun u => (mem_invariants U M (c : M)).1 c.2 u)⟩
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    dsimp only
    exact (eq_const_of_mem_invariants U f.1 f.2 g).symm
  right_inv c := by
    apply Subtype.ext
    rfl
  map_add' f g := by
    apply Subtype.ext
    rfl

end ShapiroH0

theorem shapiro_H0_coind {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G))
    {M : Type*} [AddCommGroup M] [DistribMulAction U M]
    (hM : Work.AbsoluteKummer.IsDiscreteModule U M) :
    Nonempty (↥(Work.AbsoluteKummer.H0 G (Work.SSGRoute.PT.Coind G U M)) ≃+
      ↥(Work.AbsoluteKummer.H0 U M)) :=
  ⟨shapiroH0AddEquiv U⟩

end Work.SSGRoute.PT
