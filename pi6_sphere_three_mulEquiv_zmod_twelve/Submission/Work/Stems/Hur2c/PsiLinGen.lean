import Submission.Work.RatHurewicz.psiDefs
import Submission.Work.RatHurewicz.CubicalDefs

/-!
# `Ψ` as a `ℤ`-linear map on cubical `(m+2)`-chains, in general degree

`Submission/Work/Stems/Hur2/PsiLin.lean` linearises the *degree-`2`* filling `psiGenLoop`; this
file does the same for the general-degree based-ification `Work.RatHurewicz.Psi` of
`Submission/Work/RatHurewicz/psiDefs.lean` (built from a filling family
`Work.RatHurewicz.Tower x₀ N`, `N ≥ m + 1`).

With `ΨLin := psiLinGen N m K hN`, the Hurewicz argument needs:

* **(Z)** `ΨLin (single p.1 1) = ⟦p⟧` for every *based* `(m+2)`-cube `p`
  (`psiLinGen_single_based`, from `Work.RatHurewicz.Psi_section`) — **proved here**;
* **(Y)** `ΨLin (∂ τ) = 0` for every `(m+3)`-cube `τ` — Hutchings' `(2.5)`, in additive form; it is
  `Work.Stems.HomAdd.PsiKillsBoundary` (`= Work.RatHurewicz.Psi_kills_boundary`) rewritten through
  `Additive.ofMul_prod`.  It lives in `Submission/Work/Stems/Hur2c/PsiLinGenCubD.lean` because the
  modules it needs are momentarily cyclic (`assembly_null.lean` now imports the three modules that
  import *it*) — a RATHUREWICZ-side import bug, transient;
* **(E)** `ΨLin` kills degenerate `(m+2)`-**cycles** (Hutchings' footnote in the form that is
  provable; `Submission/Work/Stems/PSI_DEG_NOTES.md` explains why the naive "`Ψ` kills every
  degenerate cube" is a dead end, and proves (E) in degree `2`).

(Z) + (Y) + (E) + the chain-level bridge `Work.RatHurewicz.cubicalBridgeDeg` give the injectivity of
the Hurewicz map in degree `m+2` — see `Submission/Work/Stems/HurewiczFirstDegree.lean` for the
statement requested by subproject SERRE.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical
open Work.RatHurewicz

namespace Work.Stems.Hur2c

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The class of `Ψ` of a single cube, with the type `HomotopyGroup` kept visible: writing
`(clPsi N m K hN c) ^ e` then finds the `zpow` instance of `HomotopyGroup`, which an explicit
ascription `(Quotient.mk _ (Psi …) : HomotopyGroup …)` does **not** (Lean unfolds the type and then
fails to synthesise `HPow`; use the `show`-form or this wrapper). -/
def clPsi (N m : ℕ) {x₀ : X} (K : Tower x₀ N) (hN : m + 1 ≤ N) (c : C(IC (m + 2), X)) :
    HomotopyGroup (Fin (m + 2)) X x₀ :=
  Quotient.mk _ (Psi N m K hN c)

theorem clPsi_def (N m : ℕ) {x₀ : X} (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (c : C(IC (m + 2), X)) : clPsi N m K hN c = ⟦Psi N m K hN c⟧ := rfl

/-- **The general-degree `Ψ` as a `ℤ`-linear map** on the cubical `(m+2)`-chains of `X`. -/
def psiLinGen (N m : ℕ) {x₀ : X} (K : Tower x₀ N) (hN : m + 1 ≤ N) :
    Cub (m + 2) X →ₗ[ℤ] Additive (HomotopyGroup (Fin (m + 2)) X x₀) :=
  Finsupp.linearCombination ℤ fun c : C(IC (m + 2), X) => Additive.ofMul (clPsi N m K hN c)

theorem psiLinGen_single (N m : ℕ) {x₀ : X} (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (c : C(IC (m + 2), X)) :
    psiLinGen N m K hN (Finsupp.single c 1) = Additive.ofMul (clPsi N m K hN c) := by
  rw [psiLinGen, Finsupp.linearCombination_single, one_smul]

/-- **(Z)** in chain form: `ΨLin` of a based cube is its class. -/
theorem psiLinGen_single_based (N m : ℕ) {x₀ : X} (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (p : GenLoop (Fin (m + 2)) X x₀) :
    psiLinGen N m K hN (Finsupp.single p.1 1) = Additive.ofMul ⟦p⟧ := by
  rw [psiLinGen_single]
  exact congrArg Additive.ofMul (Quotient.sound (Psi_section N m K hN p))

end

end Work.Stems.Hur2c
