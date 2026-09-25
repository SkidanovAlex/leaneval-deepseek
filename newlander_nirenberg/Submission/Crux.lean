import Submission.Work.Core.Solvable
import Submission.Work.Translate.ofTranslate
import Submission.Work.Translate.nijenhuisTranslate
import Submission.Work.NN.Core.dbarSolvable_one
import Submission.Work.NN.Newton.dbarSolvable_of_perturb_C1

open LeanEval.Geometry.NewlanderNirenberg
open Set
open scoped ContDiff

namespace Submission

variable {n : ℕ}

/-- **The analytic input of Newlander–Nirenberg, at the origin.**

Solvability of the linear `∂̄`-equation for the standard coordinate functions on a neighbourhood
of `0`: there are smooth corrections `v_j` with `∂̄_J v_j = ∂̄_J z_j` (i.e. `z_j - v_j`
`J`-holomorphic) whose differentials are invertible.  This is the content of the Cauchy-kernel /
Schauder estimates plus the small-perturbation (contraction) argument on a small polydisc,
Hörmander/Kohn/Nirenberg style; it is the single missing ingredient of the development.

The subprojects `Work/CR/Flat`, `Work/NN/Core` (for `n = 1` via `FlatSolver`) and
`Work/Hormander/Weights` (for `n ≥ 2`, weighted `L²` estimates) are devoted to it; see
`ROADMAP.md` and `Submission/Work/Core/PLAN.md`. -/
theorem dbar_solvable_zero {n : ℕ} {U : Set (E n)} (hU : IsOpen U) {J : E n → E n →L[ℝ] E n}
    (hJ : IsAlmostComplexOn J U) (hN : NijenhuisVanishesOn J U) (h0 : (0 : E n) ∈ U)
    {T : E n ≃L[ℝ] F n} (hT : ∀ v, T (J 0 v) = Complex.I • T v) :
    DbarSolvable J U 0 T := by
  rcases n with _ | n'
  · -- `n = 0`: everything is vacuous, and `E 0` and `Fin 0 → ℂ` are singletons
    refine ⟨U, hU, h0, subset_refl U, (fun j => Fin.elim0 j),
      (fun j => Fin.elim0 j), (fun j => Fin.elim0 j), ?_⟩
    intro y _
    haveI hsub : Subsingleton (E 0) := ⟨fun a b => by
      apply WithLp.ofLp_injective
      funext i
      exact i.elim0⟩
    haveI hsub2 : Subsingleton (Fin 0 → ℂ) := ⟨fun a b => funext fun i => i.elim0⟩
    exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ b⟩⟩
  rcases n' with _ | k
  · -- `n = 1`: proved via the Beltrami equation (`Work.NN.Core.dbarSolvable_one`)
    exact Work.NN.Core.dbarSolvable_one hU hJ h0 hT
  · -- `n ≥ 2`: the Newton/KAM iteration on shrinking polydiscs (`Work.NN.Newton`, see
    -- `Submission/Work/NN/Newton/DESIGN.md`), after rescaling to the `C^{1,α}`-small regime.
    exact Work.NN.Final.dbarSolvable_of_perturb_C1 hU hJ hN h0 hT

/-- **The analytic input at an arbitrary point**, obtained from the statement at the origin by
translating the structure.  Since a translation is a diffeomorphism, it preserves `J² = -1`
and the vanishing of the Nijenhuis tensor, the standard coordinates `zcoord T j` are linear
(hence their differentials are translation invariant), and derivatives are unchanged. -/
theorem dbar_solvable {n : ℕ} {U : Set (E n)} (hU : IsOpen U) {J : E n → E n →L[ℝ] E n}
    (hJ : IsAlmostComplexOn J U) (hN : NijenhuisVanishesOn J U) {x : E n} (hx : x ∈ U)
    {T : E n ≃L[ℝ] F n} (hT : ∀ v, T (J x v) = Complex.I • T v) :
    DbarSolvable J U x T := by
  have hU' : IsOpen {y : E n | x + y ∈ U} :=
    hU.preimage (continuous_const.add continuous_id)
  have hJ' : IsAlmostComplexOn (fun y : E n => J (x + y)) {y : E n | x + y ∈ U} := by
    refine ⟨?_, fun y hy v => hJ.2 (x + y) hy v⟩
    exact hJ.1.comp (by fun_prop) (fun y hy => hy)
  have hN' : NijenhuisVanishesOn (fun y : E n => J (x + y)) {y : E n | x + y ∈ U} :=
    Work.Translate.nijenhuisTranslate hU hN x
  have h0 : (0 : E n) ∈ {y : E n | x + y ∈ U} := by simpa using hx
  have hT' : ∀ v, T ((fun y : E n => J (x + y)) 0 v) = Complex.I • T v := by
    simpa using hT
  exact Work.Translate.ofTranslate hU x (dbar_solvable_zero hU' hJ' hN' h0 hT')

/-- **The analytic core of Newlander–Nirenberg.**  If `J` is an almost complex structure with
vanishing Nijenhuis tensor on an open set `U`, and `J x` is standard (there is a real-linear
isomorphism `T` intertwining `J x` with multiplication by `i` on `ℂⁿ`), then near `x` there are
`n` `J`-holomorphic functions whose differentials are everywhere invertible.

This is the Newlander–Nirenberg theorem in local normal form.  It follows from the solvability of
the `∂̄`-equation (`dbar_solvable`, whose content is the single analytic input), and everything
else is proved in this workspace. -/
theorem nn_core {n : ℕ} {U : Set (E n)} (hU : IsOpen U) {J : E n → E n →L[ℝ] E n}
    (hJ : IsAlmostComplexOn J U) (hN : NijenhuisVanishesOn J U) {x : E n} (hx : x ∈ U)
    (hT : ∃ T : E n ≃L[ℝ] F n, ∀ v, T (J x v) = Complex.I • T v) :
    ∃ V : Set (E n), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ u : Fin n → E n → ℂ, (∀ j, ContDiffOn ℝ ∞ (u j) V) ∧
      (∀ j, ∀ y ∈ V, ∀ v : E n,
        fderiv ℝ (u j) y (J y v) = Complex.I * fderiv ℝ (u j) y v) ∧
      (∀ y ∈ V, Function.Bijective (fderiv ℝ (fun y : E n => fun j => u j y) y)) := by
  obtain ⟨T, hT'⟩ := hT
  exact nn_core_of_dbar (dbar_solvable hU hJ hN hx hT')

end Submission
