/-
# `Submission/Work/FTS_MuLamOK/Main.lean` — **the μ/λ clause** (`Work.FTS.StrongEps.MuLamOK`)

The deliverable of the chapter: the proof of the final core field 1b of the strong-solution
interface v2,

  `Work.FTS.StrongEps.MuLamOK α C₀ Φs E`      (`Submission/Work/FTS/StrongEps/EpsLimit.lean`),

from the three zero-mode row lemmas of `Rows/`:

* `Rows/Rl0Open`  — `|L₁₂(N₀ α (F_*+f) f)(0)| ≤ K₀(α² + √α X + α^{-3/2}X²)`,
* `Rows/Rl1Open`  — `|L₁₂(N α (F_*+f) (Φs+Ef))(0)| ≤ K₁(α² + √α X + α^{-3/2}X²)`,
* `Rows/Rl2Open`  — `|L₁₂(3D_θf/(1+z))(0)| ≤ K₂ X`,                            `X = Xn α f`,

(each for the honest class `SmoothOpen f`, `HkMem α 4 f`; the `N`-row additionally at the
packages `StarPkgo`, `EllPkgGo`), together with the arithmetic of `Defs.lean`/`Conversion.lean`/
`RowReduction.lean`:

  `2αμ = L₁₂(N₀)(0) + L₁₂(N)(0) + L₁₂(3D_θf/(1+z))(0)`  ⟹  `|μ| ≤ 3Kα/2`
  ⟹ `|μ| ≤ 1/3 ∧ |λ| ≤ 1`  for `9Kα ≤ 2`,

with the constant `KMu C₀ Ce Cs = max (K₀(1+C₀+C₀²)) (max (K₁(1+C₀+C₀²)) (K₂C₀))` obtained from
the row constants by scaling the envelopes to `K α²` on profiles of `ℋ⁴`-size `≤ C₀α²`.

## Statements

* `MuLamOK_proved` — the clause at a fixed exponent `α` (the hypothesis `9·KMu·α ≤ 2` is the
  smallness of `α` *relative to* `C₀`, `Ce`, `Cs`; `KMu` does **not** depend on `α`);
* `MuLamOK_proved_eventually` — the same, in the form "for all sufficiently small `α`", with the
  explicit threshold `min 1 (2/(9·KMu C₀ Ce Cs))`: this is the shape in which the assembly
  (`Final/Defs.Inputs`, `exists_limH`) consumes it.

## What a caller supplies

* `hα : 0 < α`, `hα1 : α ≤ 1`, `hC₀ : 0 < C₀`;
* `hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs` — the star package (interface conjunct (2));
* `hell : ∀ f, ClassC α f → VocabO.EllPkgGo α Ce f (E f)` — the elliptic layer at the class `C`
  (the `EllPkgGo` half of interface conjunct (1));
* the smallness `9 * KMu C₀ Ce Cs * α ≤ 2`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_MuLamOK.Defs
import Submission.Work.FTS_MuLamOK.Conversion
import Submission.Work.FTS_MuLamOK.RowReduction
import Submission.Work.FTS_MuLamOK.Rows.Rl0Open
import Submission.Work.FTS_MuLamOK.Rows.Rl1Open
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS.Regularity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLamOK

open Work.FTS.Galerkin (Fn Fam slice muDyn lamDyn)
open Work.FTS_MuLamOK.Rows

set_option autoImplicit false

/-! ## The row constants -/

/-- The constant of `Rows/Rl0Open`. -/
noncomputable def KMu0 : ℝ := Classical.choose Rl0Open

/-- The constant of `Rows/Rl1Open` at the elliptic/star constants `Ce`, `Cs`. -/
noncomputable def KMu1 (Ce Cs : ℝ) : ℝ := Classical.choose (Rl1Open Ce Cs)

/-- The constant of `Rows/Rl2Open`. -/
noncomputable def KMu2 : ℝ := Classical.choose Rl2Open

theorem KMu0_pos : 0 < KMu0 := (Classical.choose_spec Rl0Open).1

theorem KMu0_pos' : 0 ≤ KMu0 := le_of_lt KMu0_pos

theorem KMu1_pos (Ce Cs : ℝ) : 0 < KMu1 Ce Cs := (Classical.choose_spec (Rl1Open Ce Cs)).1

theorem KMu1_pos' (Ce Cs : ℝ) : 0 ≤ KMu1 Ce Cs := le_of_lt (KMu1_pos Ce Cs)

theorem KMu2_pos : 0 < KMu2 := (Classical.choose_spec Rl2Open).1

theorem KMu2_pos' : 0 ≤ KMu2 := le_of_lt KMu2_pos

theorem KMu0_row : ∀ {α : ℝ} {f : Fn}, 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0|
      ≤ KMu0 * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f ^ 2) :=
  fun hα hα1 hso hmem => (Classical.choose_spec Rl0Open).2 hα hα1 hso hmem

theorem KMu1_row (Ce Cs : ℝ) : ∀ {α : ℝ} {f Φs Φg : Fn}, 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.VocabO.StarPkgo α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce f Φg →
    |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Φg z θ)) 0|
      ≤ KMu1 Ce Cs * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f ^ 2) :=
  fun hα hα1 hso hmem hs hell => (Classical.choose_spec (Rl1Open Ce Cs)).2 hα hα1 hso hmem hs hell

theorem KMu2_row : ∀ {α : ℝ} {f : Fn}, 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0|
      ≤ KMu2 * Work.FTS.Nonlin.Xn α f :=
  fun hα hα1 hso hmem => (Classical.choose_spec Rl2Open).2 hα hα1 hso hmem

/-- The combined constant of the μ/λ clause: `max (K₀(1+C₀+C₀²)) (max (K₁(1+C₀+C₀²)) (K₂C₀))`. -/
def KMu (C₀ Ce Cs : ℝ) : ℝ := KRow C₀ KMu0 (KMu1 Ce Cs) KMu2

theorem KMu_pos {C₀ Ce Cs : ℝ} (hC₀ : 0 < C₀) : 0 < KMu C₀ Ce Cs := by
  refine lt_of_lt_of_le ?_ (le_max_left _ _)
  exact mul_pos KMu0_pos (by nlinarith [sq_nonneg C₀])

/-! ## The clause -/

/-- The `ℋ⁴`-honesty of a `ClassC` profile at level `4` (the fragment of the class used by the
three rows). -/
theorem ClassC_hkMem_four {α : ℝ} {f : Fn} (hf : Work.FTS.ClassC.ClassC α f) :
    Work.Spaces.HkMem α 4 f :=
  Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hf.reg hf.mem

/-- **The μ/λ clause, at a fixed exponent.**  `KMu C₀ Ce Cs` is the combined row constant; the
hypothesis `9·KMu·α ≤ 2` is the smallness of `α` relative to `C₀`, `Ce`, `Cs`. -/
theorem MuLamOK_proved {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn → Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hC₀ : 0 < C₀)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.VocabO.EllPkgGo α Ce f (E f))
    (hsmall : 9 * KMu C₀ Ce Cs * α ≤ 2) :
    Work.FTS.StrongEps.MuLamOK α C₀ Φs E := by
  refine MuLamOK_of_rowEnvelopes (Φs := Φs) (E := E) hα hα1 KMu0_pos' (KMu1_pos' Ce Cs)
    KMu2_pos' ?_ ?_ ?_ hsmall
  · intro f hf
    exact KMu0_row hα hα1 hf.reg (ClassC_hkMem_four hf)
  · intro f hf
    exact KMu1_row Ce Cs hα hα1 hf.reg (ClassC_hkMem_four hf) hstar.toStarPkgo (hell f hf)
  · intro f hf
    exact KMu2_row hα hα1 hf.reg (ClassC_hkMem_four hf)

/-- **`MuLamOK` is monotone in `C₀`** (in the decreasing direction, which is the useful one):
the clause at the larger size constant `C₀'` gives it at the smaller constant `C₀ ≤ C₀'`, since
the class and the bounds do not depend on `C₀`. -/
theorem MuLamOK_mono_C₀ {α C₀ C₀' : ℝ} {Φs : Fn} {E : Fn → Fn}
    (h : Work.FTS.StrongEps.MuLamOK α C₀' Φs E) (hCC : C₀ ≤ C₀') :
    Work.FTS.StrongEps.MuLamOK α C₀ Φs E :=
  fun f hf hX => h f hf (le_trans hX (mul_le_mul_of_nonneg_right hCC (sq_nonneg α)))

/-- **The μ/λ clause, "for `α` small".**  The threshold `min 1 (2/(9·KMu C₀ Ce Cs))` depends on
the constants `C₀`, `Ce`, `Cs` but not on `α`; this is the form in which the clause is consumed
by the assembly at `pExp α ≤ α₂`. -/
theorem MuLamOK_proved_eventually {C₀ Ce Cs : ℝ} (hC₀ : 0 < C₀) :
    ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ {Φs : Fn} {E : Fn → Fn},
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
      (∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.VocabO.EllPkgGo α Ce f (E f)) →
      Work.FTS.StrongEps.MuLamOK α C₀ Φs E := by
  have hK : 0 < KMu C₀ Ce Cs := KMu_pos hC₀
  refine ⟨min 1 (2 / (9 * KMu C₀ Ce Cs)), lt_min one_pos (by positivity), ?_⟩
  intro α hα hΦs E hstar hell
  have hα1 : α ≤ 1 := le_trans hα.2 (min_le_left _ _)
  have hαc : α ≤ 2 / (9 * KMu C₀ Ce Cs) := le_trans hα.2 (min_le_right _ _)
  refine MuLamOK_proved hα.1 hα1 hC₀ hstar hell ?_
  have h9 : (0 : ℝ) < 9 * KMu C₀ Ce Cs := by positivity
  rw [le_div_iff₀ h9] at hαc
  linarith

/-! ## The clause at the profile exponent `pExp α = 3α` -/

/-- **The μ/λ clause at the profile exponent**, i.e. with `α` replaced by `pExp α = 3α` of
`Work.FTS.Regularity`: this is the instance consumed by the final assembly
(`Final/Defs.Inputs` conjunct (1b), `exists_limH` at `pExp α`).  The threshold is
`min (1/3) (2/(27·KMu C₀ Ce Cs))`, so that both `pExp α ≤ 1` and `9·KMu·(3α) ≤ 2` hold. -/
theorem MuLamOK_proved_pExp {C₀ Ce Cs : ℝ} (hC₀ : 0 < C₀) :
    ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ {Φs : Fn} {E : Fn → Fn},
      Work.FTS.VocabO2.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs →
      (∀ f : Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) f →
        Work.FTS.VocabO.EllPkgGo (Work.FTS.Regularity.pExp α) Ce f (E f)) →
      Work.FTS.StrongEps.MuLamOK (Work.FTS.Regularity.pExp α) C₀ Φs E := by
  have hK : 0 < KMu C₀ Ce Cs := KMu_pos hC₀
  refine ⟨min (1 / 3) (2 / (27 * KMu C₀ Ce Cs)),
    lt_min (by norm_num) (by positivity), ?_⟩
  intro α hα hΦs E hstar hell
  have hα0 : 0 < α := hα.1
  have hα3 : α ≤ 1 / 3 := le_trans hα.2 (min_le_left _ _)
  have hαc : α ≤ 2 / (27 * KMu C₀ Ce Cs) := le_trans hα.2 (min_le_right _ _)
  refine MuLamOK_proved (Work.FTS.Regularity.pExp_pos hα0)
    (Work.FTS.Regularity.pExp_le_one hα3) hC₀ hstar hell ?_
  have h27 : (0 : ℝ) < 27 * KMu C₀ Ce Cs := by positivity
  rw [le_div_iff₀ h27] at hαc
  rw [Work.FTS.Regularity.pExp_eq]
  nlinarith [hαc]

end Work.FTS_MuLamOK