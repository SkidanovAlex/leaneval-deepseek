import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.SSGRoute.PT.AlphaTwoBaseCase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Injectivity of `α²` on the trivial module

`alphaTwo_trivMod_apply_one` evaluates `alphaTwo x` at the generator `1`, and
`mapH2_ptorEquiv_injective` (Hilbert 90) says the resulting coefficient map is injective; since
every element of `invariants G (TrivMod G p)` is a multiple of that generator, this pins `alphaTwo`
down.
-/

open Classical

namespace Work.SSGRoute.PT

noncomputable section

universe u

/-- Injectivity of the coefficient map in `evalOne` form. -/
theorem mapH2_evalOne_injective {G : Type u} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (p : ℕ) [Fact p.Prime] {C : Type u} [AddCommGroup C]
    [DistribMulAction G C]
    (S : Work.AbsoluteKummer.ShortExactSeq G (ConjHom (TrivMod G p) C) C C)
    (hSι : S.iota = evalOne G p C)
    (h1 : Subsingleton (Work.AbsoluteKummer.H1 G C)) :
    Function.Injective
      (Work.AbsoluteKummer.mapH2 (evalOne G p C) (evalOne_equivariant G p C)) := by
  have hcongr := mapH2_congr_coeff
    (hφ := subtype_comp_conjHomTrivModEquivPTor_equivariant G p C)
    (hψ := evalOne_equivariant G p C)
    (h := subtype_comp_conjHomTrivModEquivPTor G p C)
  intro x y hxy
  refine mapH2_ptorEquiv_injective (G := G) p S hSι h1 ?_
  rw [hcongr]
  exact hxy

/-- **Injectivity of `α²` on the trivial module.** -/
theorem alphaTwo_trivMod_injective {G : Type u} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (p : ℕ) [Fact p.Prime] {C : Type u} [AddCommGroup C]
    [DistribMulAction G C]
    (S : Work.AbsoluteKummer.ShortExactSeq G (ConjHom (TrivMod G p) C) C C)
    (hSι : S.iota = evalOne G p C)
    (h1 : Subsingleton (Work.AbsoluteKummer.H1 G C)) :
    Function.Injective (alphaTwo (G := G) (N := TrivMod G p) (C := C)) := by
  have hk1 : ((1 : ℤ) : TrivMod G p) ∈ Work.GroupCohomology.invariants G (TrivMod G p) := by
    simp [Work.GroupCohomology.invariants, TrivMod.smul_eq]
  intro x y hxy
  have hgen := congrArg (fun (φ : ↥(Work.GroupCohomology.invariants G (TrivMod G p)) →+
      Work.AbsoluteKummer.H2 G C) => φ ⟨((1 : ℤ) : TrivMod G p), hk1⟩) hxy
  rw [alphaTwo_trivMod_apply_one (G := G) p x hk1,
      alphaTwo_trivMod_apply_one (G := G) p y hk1] at hgen
  exact mapH2_evalOne_injective (G := G) p S hSι h1 hgen

end

end Work.SSGRoute.PT
