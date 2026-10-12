import ChallengeDeps
import Submission.Work.BoseB1Cube.PerBoxRow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.perBoxFNomSharp` — the *nominal* spelling collapses on in-box states

Holder of `Submission/Work/BoseB1Cube/perBoxFNom_holds.lean`.  This module supplies the two exact
structural facts that make the frozen nominal per-box row (`Work.BoseB1Cube.PerBoxFNom`,
`Work.BoseB1Cube.perBoxRow`) tractable, and that connect it to the corpus's own mean-field-row
target (`Work.BoseFixB1B.sbWordCube_ge_meanFieldRow`).

## The point

`PerBoxFNom`'s only state-dependent positive row is the `F`-weight

    I(Φ) = ∫_{abox n ℓ} Φ(x)²·ψ(1, μp, boxIndCount(x)/|B(u)|) ,

read at the **indicator count** `boxIndCount(x) = Σᵢ 1_{B(u)}(xᵢ)` (`NominalPerBox.lean`), divided
by the *sharp* box volume `|B(u)| = boxMass ℓ d u`.  FS's `thm:smallbox` reads the same weight.

**On a state a.e. supported in the box** (`∀ᵐ x, Φ x ≠ 0 → ∀ i, xᵢ ∈ B(u)`) the count is the
constant `n`, hence

    I(Φ) = ψ(1, μp, n/|B(u)|)·‖Φ‖² .            (COLLAPSE)

So on in-box states the frozen row is *exactly* FS's (and the corpus's
`sbWordCube_ge_meanFieldRow`'s) constant-density row — the "nominal spelling" has no smoothing
bookkeeping and no count window at all.  This is the precise sense in which
`FINDING_cubeCrudeBand_session5.md` §9's `hcount` loop belongs to the *smooth* spelling only.

## Contents

* `indCount_eq_card_of_forall_mem` — the count of a set is the particle number when every particle
  lies in it (any `n`, any set);
* `boxIndCount_eq_n_of_forall_mem` — its `boxIndCount` instance;
* `perBoxFNom_I_eq_of_inBox` — **(COLLAPSE)**;
* `perBoxRow_eq_of_inBox` — the whole nominal row of an in-box state in constant-density form.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The indicator count of a set containing every particle -/

/-- The indicator count `Σᵢ 1_A(xᵢ)` of a set containing every particle is the particle number. -/
lemma indCount_eq_card_of_forall_mem {n : ℕ} {A : Set E3} {x : X n}
    (hall : ∀ i : Fin n, x i ∈ A) :
    (∑ i : Fin n, A.indicator (fun _ => (1 : ℝ)) (x i)) = (n : ℝ) := by
  rw [Finset.sum_congr rfl (fun i _ => Set.indicator_of_mem (hall i) (fun _ => (1 : ℝ)))]
  simp

/-- `boxIndCount` is the particle number on configurations with every particle in the box. -/
lemma boxIndCount_eq_n_of_forall_mem {n : ℕ} {ℓ d : ℝ} {u : E3} {x : X n}
    (hall : ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox ℓ d u) :
    boxIndCount ℓ d u x = (n : ℝ) :=
  indCount_eq_card_of_forall_mem hall

/-! ## 2. (COLLAPSE): the `F`-weight integral at an in-box state -/

/-- **(COLLAPSE).**  For a state a.e. supported in the sliding box, the nominal `F`-weight
integral of `PerBoxFNom` is the constant one:

    ∫_{abox} Φ²·ψ(1, μp, boxIndCount/|B(u)|) = ψ(1, μp, n/|B(u)|)·‖Φ‖² .

No integrability, positivity, or normalisation hypothesis is needed (the proof is a.e. congruence
of integrands, and both sides are junk-free). -/
theorem perBoxFNom_I_eq_of_inBox {n : ℕ} {ℓ d μp : ℝ} {u : E3} {Φ : X n → ℝ}
    (hmem : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      Φ x ≠ 0 → ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox ℓ d u) :
    (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 μp (boxIndCount ℓ d u x
          / Work.SmallBoxSliding.boxMass ℓ d u))
      = Work.SmallBoxSliding.psiWeight 1 μp ((n : ℝ) / Work.SmallBoxSliding.boxMass ℓ d u)
        * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hmem] with x hx
  rcases eq_or_ne (Φ x) 0 with h0 | h0
  · rw [h0]
    ring
  · have hcount : boxIndCount ℓ d u x = (n : ℝ) := boxIndCount_eq_n_of_forall_mem (hx h0)
    rw [hcount]
    ring

/-! ## 3. The whole nominal row of an in-box state -/

/-- **The nominal row of an in-box state, in constant-density form.**  With
`ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`, `M = (paramsAt μ (a v)).M`,
`W = w1MassB h M ℓ d u`, `χ = chiMass M ℓ d u`, `|B| = boxMass ℓ d u` and `N = ‖Φ‖²`, an in-box
state satisfies

    perBoxRow v h R c₁ C μp μ n Φ u
      = c₁·W·(ψ(1,μp,n/|B|)·N) − ½μp²·W·N
          − C·(μp²·(a v)·(Γ)·χ·N + μp·(a v)·N) ,   Γ = (R/(ℓd))² + K_B³(μa³)^{1/2} .

This is the form in which the corpus's own per-box target is written
(`Work.BoseFixB1B.sbWordCube_ge_meanFieldRow`); the only differences are the spelling of the
`F`-row (`ψ(1,μp,t)` against `¼(t−μ)² − ½μ²`) and that the present statement is a strict identity
rather than a lower bound. -/
theorem perBoxRow_eq_of_inBox {v : E3 → ℝ} {h : ScatSol v} {R c₁ C μp μ : ℝ} {n : ℕ}
    {Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))} {u : E3}
    (hmem : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n (sideAt μ (a v)))),
      (Φ : X n → ℝ) x ≠ 0 →
        ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) :
    perBoxRow v h R c₁ C μp μ n Φ u
      = c₁ * (Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u
          * (Work.SmallBoxSliding.psiWeight 1 μp
              ((n : ℝ) / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
            * normB v μ n (Φ : X n → ℝ)))
        - (1 / 2) * μp ^ 2 * Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
        - C * (μp ^ 2 * (a v)
              * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                  + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                    (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
              + μp * (a v) * normB v μ n (Φ : X n → ℝ)) := by
  have h := perBoxFNom_I_eq_of_inBox (μp := μp) (d := (paramsAt μ (a v)).d)
    (ℓ := sideAt μ (a v)) (u := u) (Φ := (Φ : X n → ℝ)) hmem
  unfold perBoxRow
  rw [h, Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]

end Work.BoseB1Cube
