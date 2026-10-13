/-
  WilG4c / ClampCharts.

  Given a finite family `Φ` of charts that is valid for the (sharply definable) parameter
  set `P`, produce a family `Φ'` of charts valid for the *full* parameter set `Λ`, without
  increasing the number of charts, so that the charts can only be read back on `P`.

  The construction is BNZ's "clamp" device, applied to the **parameter** variable: keep each
  chart `φ` as it is on `P` and replace it, off `P`, by the constant map
  `(1/2, …, 1/2) : Fin n → ℝ`.  Writing `sel φ` for the modification,

  * off `P` the modified chart takes the constant value `1/2`, which lies in the open cube,
    so the image condition is automatic there; the composite `t ↦ F i l (fun j => 1/2)` is
    constant in `t`, whence `C^{r}` with all derivatives `0` for order `≥ 1` and value in
    `(0,1)` for order `0` (this is where `ValuesIn01 Λ F` is used);
  * on `P` the modification is the identity, so the `C^{r}`-norms and the cube-to-cube
    condition transfer verbatim from the input charts
    (`Work.WilG4c.PerLambda.ChartsOK_extends`);
  * the graphs of the clamped chart components stay `Ω`-bounded, with format and degree
    increasing additively (`Work.WilG4c.IteFamGraphMemGen`, applied with `Λ := P`,
    `c := 1/2`, to the single member `φ j`);
  * `Φ' := Φ.image sel` keeps the cardinality bound, contains every `sel φ`, and the
    `ε`-cover of `P` by `Φ` is still an `ε`-cover by `Φ'` since the two agree on `P`.
-/
import Mathlib
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG4c.IteFamGraphMem
import Submission.Work.WilG4c.IteFamGraphMemGen
import Submission.Work.WilG4c.PerLambda.ChartsOK_extends

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

theorem ClampCharts (S : WilkiesDesign.SOMin) (p n k r : ℕ)
    (Λ P : Set (Fin p → ℝ)) (F : Work.WilkG4c.Family k p n)
    (a Dg aP dP : ℕ) (hPmem : P ∈ S.Ω aP dP p)
    (hval : Work.WilkG4c.ValuesIn01 Λ F)
    (Φ : Finset (Work.WilkG4c.ChartTuple p n))
    (hΦ : Work.WilkG4c.ChartsOK S a Dg r P F Φ) :
    ∃ (Φ' : Finset (Work.WilkG4c.ChartTuple p n)) (a' Dg' : ℕ)
      (sel : Work.WilkG4c.ChartTuple p n → Work.WilkG4c.ChartTuple p n),
      Φ'.card ≤ Φ.card ∧
      Work.WilkG4c.ChartsOK S a' Dg' r Λ F Φ' ∧
      (∀ φ ∈ Φ, sel φ ∈ Φ') ∧
      (∀ φ ∈ Φ, ∀ l ∈ P, ∀ j : Fin n, sel φ j l = φ j l) ∧
      (∀ ε : ℝ, Work.WilkG4c.Covers P F Φ ε → Work.WilkG4c.Covers P F Φ' ε) := by
  classical
  -- the clamped chart modification: the identity on the parameter set `P`, the constant
  -- point `1/2` outside it.
  let sel : Work.WilkG4c.ChartTuple p n → Work.WilkG4c.ChartTuple p n :=
    fun φ j l t => if l ∈ P then φ j l t else (1 / 2 : ℝ)
  have hsel_apply : ∀ (φ : Work.WilkG4c.ChartTuple p n) (j : Fin n) (l : Fin p → ℝ)
      (t : Fin n → ℝ), sel φ j l t = if l ∈ P then φ j l t else (1 / 2 : ℝ) :=
    fun φ j l t => rfl
  have hmod : ∀ (φ : Work.WilkG4c.ChartTuple p n) (j : Fin n) (l : Fin p → ℝ),
      l ∈ P → ∀ t : Fin n → ℝ, sel φ j l t = φ j l t := by
    intro φ j l hl t
    rw [hsel_apply, if_pos hl]
  have hmodc : ∀ (φ : Work.WilkG4c.ChartTuple p n) (j : Fin n) (l : Fin p → ℝ),
      l ∉ P → ∀ t : Fin n → ℝ, sel φ j l t = (1 / 2 : ℝ) := by
    intro φ j l hl t
    rw [hsel_apply, if_neg hl]
  -- the graphs of the clamped chart components are still `Ω`-bounded: off `P` the chart is
  -- the constant `1/2`, so `IteFamGraphMemGen` applies to the single member `φ j`.
  have hΩ : ∀ φ ∈ Φ, ∀ j : Fin n, WilkiesDesign.CG.famGraph ((sel φ) j) ∈
      S.Ω (a + aP + 3 * (p + n + 1) + 3 * p + 6) (Dg + 2 * dP + 5) (p + n + 1) := by
    intro φ hφ j
    have hφmem : WilkiesDesign.CG.famGraph (φ j) ∈ S.Ω a Dg (p + n + 1) := (hΦ φ hφ).1 j
    exact IteFamGraphMemGen S P (1 / 2 : ℝ) (fun _ : Fin 1 => φ j) (fun _ : Fin 1 => (sel φ) j)
      0 aP dP a Dg hPmem hφmem
      (fun l t hl => by simp only [hsel_apply, if_pos hl])
      (fun l t hl => by simp only [hsel_apply, if_neg hl])
  -- the clamped charts satisfy the chart conditions for the full parameter set `Λ`
  have hc : (fun _ : Fin n => (1 / 2 : ℝ)) ∈ WilkiesDesign.openCube n := by
    intro j
    norm_num
  obtain ⟨Ψ, hΨmem, hΨcard, hΨOK⟩ :=
    Work.WilG4c.PerLambda.ChartsOK_extends (S := S) (Λ := Λ) (Λ' := P) (F := F) (Φ := Φ)
      (c := fun _ : Fin n => (1 / 2 : ℝ)) hc hval sel hmod hmodc hΩ
      (fun φ hφ l hl => (hΦ φ hφ).2 l hl)
  refine ⟨Ψ, a + aP + 3 * (p + n + 1) + 3 * p + 6, Dg + 2 * dP + 5, sel,
    hΨcard, hΨOK, hΨmem, ?_, ?_⟩
  · intro φ hφ l hl j
    funext t
    exact hmod φ j l hl t
  · -- the `ε`-cover transfers because the clamped charts agree with the originals on `P`
    intro ε hcov l hl x hx
    obtain ⟨φ, hφ, t, ht, hlt⟩ := hcov l hl x hx
    refine ⟨sel φ, hΨmem φ hφ, t, ht, fun i => ?_⟩
    have hpt : (fun j : Fin n => sel φ j l t) = (fun j : Fin n => φ j l t) :=
      funext (fun j => hmod φ j l hl t)
    rw [hpt]
    exact hlt i

end Work.WilG4c
