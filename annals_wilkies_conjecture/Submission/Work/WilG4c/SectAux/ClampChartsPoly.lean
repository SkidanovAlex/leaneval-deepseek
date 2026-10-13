/-
  WilG4c / SectAux / ClampChartsPoly.

  The "clamp the parameter variable" device of BNZ §5.2, with the format/degree bookkeeping
  made explicit: given a finite family `Φ` of charts that is valid for the (sharply
  definable, `Ω (aP, dP)`-bounded) parameter set `P`, replace each chart `φ` by

    `sel φ j l t = if l ∈ P then φ j l t else 1/2`,

  the identity on `P` and the constant `1/2` off it.  The clamped family `Φ' := Φ.image (sel)`

  * does not grow in cardinality,
  * is `ChartsOK` for the *full* parameter set `Λ` with format and degree increased to
    `a + aP + 3 * (p + n + 1) + 3 * p + 6` and `Dg + 2 * dP + 5` respectively,
  * still `ε`-covers `P`, since on `P` the clamped charts agree with the originals.

  The `Ω`-membership of the clamped coordinate graphs is `IteFamGraphMemGen` applied to the
  single member `φ j`; the transfer of the chart conditions is `PerLambda.ChartsOK_extends`.
-/
import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG4c.IteFamGraphMemGen
import Submission.Work.WilG4c.PerLambda.ChartsOK_extends

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c.SectAux

open WilkiesDesign WilkiesDesign.CG

theorem ClampChartsPoly (S : WilkiesDesign.SOMin) (p n k r : ℕ)
    (Λ P : Set (Fin p → ℝ)) (F : Work.WilkG4c.Family k p n)
    (a Dg aP dP : ℕ) (hPmem : P ∈ S.Ω aP dP p)
    (hval : Work.WilkG4c.ValuesIn01 Λ F)
    (ε : ℝ) (Φ : Finset (Work.WilkG4c.ChartTuple p n))
    (hΦ : Work.WilkG4c.ChartsOK S a Dg r P F Φ)
    (hcov : Work.WilkG4c.Covers P F Φ ε) :
    ∃ Φ' : Finset (Work.WilkG4c.ChartTuple p n),
      Φ'.card ≤ Φ.card ∧
      Work.WilkG4c.ChartsOK S (a + aP + 3 * (p + n + 1) + 3 * p + 6) (Dg + 2 * dP + 5) r Λ F Φ' ∧
      Work.WilkG4c.Covers P F Φ' ε := by
  classical
  -- the clamped chart modification: the identity on `P`, the constant `1/2` outside it
  let sel : Work.WilkG4c.ChartTuple p n → Work.WilkG4c.ChartTuple p n :=
    fun φ j l t => if l ∈ P then φ j l t else (1 / 2 : ℝ)
  have hsel : ∀ (φ : Work.WilkG4c.ChartTuple p n) (j : Fin n) (l : Fin p → ℝ)
      (t : Fin n → ℝ), sel φ j l t = if l ∈ P then φ j l t else (1 / 2 : ℝ) :=
    fun _ _ _ _ => rfl
  have hmod : ∀ (φ : Work.WilkG4c.ChartTuple p n) (j : Fin n) (l : Fin p → ℝ),
      l ∈ P → ∀ t : Fin n → ℝ, sel φ j l t = φ j l t := by
    intro φ j l hl t
    simp only [hsel, hl, ite_true]
  have hmodc : ∀ (φ : Work.WilkG4c.ChartTuple p n) (j : Fin n) (l : Fin p → ℝ),
      l ∉ P → ∀ t : Fin n → ℝ, sel φ j l t = (1 / 2 : ℝ) := by
    intro φ j l hl t
    simp only [hsel, hl, ite_false]
  -- the constant point `1/2` lies in the open cube
  have hc : (fun _ : Fin n => (1 / 2 : ℝ)) ∈ WilkiesDesign.openCube n := by
    intro j
    norm_num
  -- the graphs of the clamped chart components are still `Ω`-bounded, at the stated bounds
  have hΩ : ∀ φ ∈ Φ, ∀ j : Fin n, WilkiesDesign.CG.famGraph ((sel φ) j) ∈
      S.Ω (a + aP + 3 * (p + n + 1) + 3 * p + 6) (Dg + 2 * dP + 5) (p + n + 1) := by
    intro φ hφ j
    have hφmem : WilkiesDesign.CG.famGraph (φ j) ∈ S.Ω a Dg (p + n + 1) := (hΦ φ hφ).1 j
    exact Work.WilG4c.IteFamGraphMemGen S P (1 / 2 : ℝ) (fun _ : Fin 1 => φ j)
      (fun _ : Fin 1 => (sel φ) j) 0 aP dP a Dg hPmem hφmem
      (fun l t hl => hmod φ j l hl t) (fun l t hl => hmodc φ j l hl t)
  -- the clamped charts satisfy the chart conditions for the full parameter set `Λ`
  obtain ⟨Φ', hΦ'mem, hΦ'card, hΦ'OK⟩ :=
    Work.WilG4c.PerLambda.ChartsOK_extends (S := S) (Λ := Λ) (Λ' := P) (F := F) (Φ := Φ)
      (c := fun _ : Fin n => (1 / 2 : ℝ)) hc hval sel hmod hmodc hΩ
      (fun φ hφ l hl => (hΦ φ hφ).2 l hl)
  refine ⟨Φ', hΦ'card, hΦ'OK, ?_⟩
  -- the `ε`-cover transfers because the clamped charts agree with the originals on `P`
  intro l hl x hx
  obtain ⟨φ, hφ, t, ht, hlt⟩ := hcov l hl x hx
  refine ⟨sel φ, hΦ'mem φ hφ, t, ht, fun i => ?_⟩
  have hpt : (fun j : Fin n => sel φ j l t) = (fun j : Fin n => φ j l t) :=
    funext (fun j => hmod φ j l hl t)
  rw [hpt]
  exact hlt i

end Work.WilG4c.SectAux
