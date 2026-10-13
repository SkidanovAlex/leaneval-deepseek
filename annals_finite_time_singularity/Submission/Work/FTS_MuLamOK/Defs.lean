/-
# `Submission/Work/FTS_MuLamOK/Defs.lean` — the μ/λ chapter: definitions and the reduction

Deliverable of the subproject **FTS_MuLamOK**: the proof of

  `Work.FTS.StrongEps.MuLamOK α C₀ Φs E`   (final core field 1b of the strong-solution
  interface v2, `Submission/Work/FTS/StrongEps/LEAD_strong_iface_v2.{md,lean.txt}`),

i.e. the μ/λ clause consumed by `Work.FTS.StrongEps.exists_limH`.  Recall (`EpsLimit.lean`)

```
MuLamOK α C₀ Φs E  :=  ∀ f, ClassC α f → Xn α f ≤ C₀ * α ^ 2 →
    |muDyn α (PsiCan Φs E (fun z θ _ => f z θ)) (fun z θ _ => f z θ) 0| ≤ 1 / 2 ∧
    |lamDyn α (PsiCan Φs E (fun z θ _ => f z θ)) (fun z θ _ => f z θ) 0| ≤ 1
```

The family `(z,θ,τ) ↦ f z θ` is written in the file as `fun z θ _ => f z θ`; here it is also
available under the name `constFam f` (notation only, so that the statements of this chapter
stay readable — the two forms are definitionally equal).

The mathematical content of the clause is Elgindi's Proposition `muestimate` (tex 1508) with the
paper's own corollary `|g|_{ℋ⁴} ≤ K α²`:

  `2α μ = L₁₂(N₀)(0) + L₁₂(N)(0) + L₁₂(3D_θg/(1+z))(0)`,

so the three `L₁₂`-zero-modes of `N₀`, `N` and the transport term, each of size `O(α²)` on a
profile of `ℋ⁴`-size `O(α²)`, give `|μ| ≤ (3/2)·K·α`, hence `|μ| ≤ 1/3` for `α` small, and then
`|λ| = |−2μ/(1+μ)| ≤ 1`.

## Contents of this file

* the constant family `constFam f` and the three *definitional* identifications it makes
  (`Ftau` at `τ = 0` is `Ftot`, the `τ = 0` slice of `PsiCan Φs E` is `Φs + E f`, and
  `muDyn` at `τ = 0` is `Construction.mufunS` at the profile `f`);
* `abs_lamfun_le_one`: `|μ| ≤ 1/3 → |lamfun μ| ≤ 1`;
* the three zero-mode predicates `ZeroMode0`, `ZeroMode1`, `ZeroMode2` — *exactly* the
  `L₁₂`-zero-mode estimates the μ-bound needs, as statements about `ClassC` profiles of
  `ℋ⁴`-size `≤ C₀α²` (this is the interface between this file and `Rows/`);
* `abs_muDyn_le_three_halves` — `|μ| ≤ 3Kα/2` from the three zero modes;
* **`MuLamOK_of_zeroModes`** — the reduction: the three zero modes plus `9Kα ≤ 2` give
  `Work.FTS.StrongEps.MuLamOK α C₀ Φs E`.

`ZeroModes.lean` supplies the three predicates from the honest open-quadrant row lemmas of
`Rows/`, and `Main.lean` is the resulting proof of `MuLamOK`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsLimit
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.FinalClock.MuBounds
import Submission.Work.Construction.MufunS

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

set_option autoImplicit false

/-! ## The constant family and the three definitional identifications -/

/-- The family which is constant in the fake time `τ`, attached to a single profile `f`:
this is the family at which the `τ = 0` clause of `MuLamOK` is evaluated (the `fun z θ _ => f z θ`
of `EpsLimit.lean`). -/
def constFam (f : Fn) : Fam := fun z θ _ => f z θ

@[simp] theorem constFam_apply (f : Fn) (z θ τ : ℝ) : constFam f z θ τ = f z θ := rfl

@[simp] theorem slice_constFam (f : Fn) (τ : ℝ) : slice (constFam f) τ = f := rfl

/-- `Ftau` of the constant family at `τ = 0` is the full profile `F_* + f` of `Construction`. -/
theorem Ftau_constFam_zero (α : ℝ) (f : Fn) :
    Work.Construction.Ftau α (constFam f) 0 = Work.Construction.Ftot α f := rfl

/-- The `τ = 0` slice of the canonical stream function of the constant family is `Φs + E f`. -/
theorem slice_PsiCan_constFam_zero (Φs : Fn) (E : Fn → Fn) (f : Fn) :
    slice (Work.FTS.Nonlin.PsiCan Φs E (constFam f)) 0 = fun z θ => Φs z θ + E f z θ := rfl

/-- **The modulation at `τ = 0` of the constant family is `Construction.mufunS` at the
profile**: `muDyn α Φ g 0 = mufunS α (N₀ α (F_*+f) f) (N α (F_*+f) (Φs+Ef)) f`.  This is the
definition of `muDyn` (`Galerkin.Defs`) together with the three identifications above. -/
theorem muDyn_constFam_zero (α : ℝ) (Φs : Fn) (E : Fn → Fn) (f : Fn) :
    muDyn α (Work.FTS.Nonlin.PsiCan Φs E (constFam f)) (constFam f) 0
      = Work.Construction.mufunS α
          (Work.Construction.N0 α (Work.Construction.Ftot α f) f)
          (Work.Construction.N α (Work.Construction.Ftot α f)
            (fun z θ => Φs z θ + E f z θ)) f := rfl

/-- The same identification in the literal form in which `MuLamOK` is stated. -/
theorem muDyn_lambda_zero (α : ℝ) (Φs : Fn) (E : Fn → Fn) (f : Fn) :
    muDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => f z θ)) (fun z θ _ => f z θ) 0
      = Work.Construction.mufunS α
          (Work.Construction.N0 α (Work.Construction.Ftot α f) f)
          (Work.Construction.N α (Work.Construction.Ftot α f)
            (fun z θ => Φs z θ + E f z θ)) f := rfl

/-- `lamDyn` is `lamfun` of `muDyn`, at the constant family. -/
theorem lamDyn_lambda_zero (α : ℝ) (Φs : Fn) (E : Fn → Fn) (f : Fn) :
    lamDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => f z θ)) (fun z θ _ => f z θ) 0
      = Work.Construction.lamfun
          (muDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => f z θ))
            (fun z θ _ => f z θ) 0) := rfl

/-! ## The second modulation constant `λ` -/

/-- **`|λ| ≤ 1` when `|μ| ≤ 1/3`.**  `lamfun μ = -2μ/(1+μ)` and `|1+μ| ≥ 1 - |μ| ≥ 2/3`, so
`|λ| ≤ 2·(1/3)/(2/3) = 1`. -/
theorem abs_lamfun_le_one {μ : ℝ} (hμ : |μ| ≤ 1 / 3) : |Work.Construction.lamfun μ| ≤ 1 := by
  have h1 : 1 - |μ| ≤ |1 + μ| := by
    have h := abs_sub_abs_le_abs_sub (1 : ℝ) (-μ)
    simpa [abs_neg, sub_neg_eq_add] using h
  have hpos : (0 : ℝ) < |1 + μ| := by linarith [abs_nonneg μ]
  have key : 2 * |μ| ≤ |1 + μ| := by linarith [hμ, h1, abs_nonneg μ]
  rw [Work.Construction.lamfun, abs_div, abs_mul, abs_neg]
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2, div_le_iff₀ hpos]
  linarith [key]

/-! ## The three zero-mode estimates as an interface -/

/-- **`Z₀`**: the zero mode of `N₀` on `ClassC` profiles of `ℋ⁴`-size `≤ C₀α²`:
`|L₁₂(N₀ α (F_*+f) f)(0)| ≤ K α²`. -/
def ZeroMode0 (α C₀ K : ℝ) : Prop :=
  ∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 →
    |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0|
      ≤ K * α ^ 2

/-- **`Z₁`**: the zero mode of `N` on `ClassC` profiles of `ℋ⁴`-size `≤ C₀α²`, evaluated with
the canonical stream function `Φs + E f`: `|L₁₂(N α (F_*+f) (Φs+Ef))(0)| ≤ K α²`. -/
def ZeroMode1 (α C₀ K : ℝ) (Φs : Fn) (E : Fn → Fn) : Prop :=
  ∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 →
    |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + E f z θ)) 0| ≤ K * α ^ 2

/-- **`Z₂`**: the zero mode of the transport term `3 D_θf/(1+z)` on `ClassC` profiles of
`ℋ⁴`-size `≤ C₀α²`: `|L₁₂(3D_θf/(1+z))(0)| ≤ K α²`. -/
def ZeroMode2 (α C₀ K : ℝ) : Prop :=
  ∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 →
    |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0| ≤ K * α ^ 2

/-! ## The μ-bound from the three zero modes -/

/-- **The modulation is `≤ 3Kα/2`.**  `2α μ` is the sum of the three `L₁₂`-zero-modes, each of
size `≤ K α²`, so `|μ| ≤ (1/(2α))·3Kα² = 3Kα/2`. -/
theorem abs_muDyn_le_three_halves {α C₀ K : ℝ} {Φs : Fn} {E : Fn → Fn}
    (hα : 0 < α) (h0 : ZeroMode0 α C₀ K) (h1 : ZeroMode1 α C₀ K Φs E)
    (h2 : ZeroMode2 α C₀ K) :
    ∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 →
      |muDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => f z θ))
        (fun z θ _ => f z θ) 0| ≤ 3 * K * α / 2 := by
  intro f hf hX
  have hA0 := h0 f hf hX
  have hA1 := h1 f hf hX
  have hA2 := h2 f hf hX
  rw [muDyn_lambda_zero]
  have hfac : Work.Construction.mufunS α
        (Work.Construction.N0 α (Work.Construction.Ftot α f) f)
        (Work.Construction.N α (Work.Construction.Ftot α f) (fun z θ => Φs z θ + E f z θ)) f
      = (1 / (2 * α)) * (Work.Construction.L12
            (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0
          + Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
              (fun z θ => Φs z θ + E f z θ)) 0)
        + (1 / (2 * α)) * Work.Construction.L12
            (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0 := rfl
  rw [hfac]
  have hval : (1 / (2 * α)) * (3 * (K * α ^ 2)) = 3 * K * α / 2 := by
    field_simp
  have hmain : |(1 / (2 * α)) * (Work.Construction.L12
          (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0
        + Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
            (fun z θ => Φs z θ + E f z θ)) 0)
      + (1 / (2 * α)) * Work.Construction.L12
          (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0|
      ≤ (1 / (2 * α)) * (3 * (K * α ^ 2)) := by
    have hre : (1 / (2 * α)) * (Work.Construction.L12
            (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0
          + Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
              (fun z θ => Φs z θ + E f z θ)) 0)
        + (1 / (2 * α)) * Work.Construction.L12
            (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0
        = (1 / (2 * α))
          * ((Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0
              + Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
                  (fun z θ => Φs z θ + E f z θ)) 0)
            + Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0) := by
      ring
    rw [hre, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * α))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith [abs_add_le (Work.Construction.L12 (Work.Construction.N0 α
            (Work.Construction.Ftot α f) f) 0)
          (Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
              (fun z θ => Φs z θ + E f z θ)) 0),
      abs_add_le (Work.Construction.L12 (Work.Construction.N0 α
            (Work.Construction.Ftot α f) f) 0
          + Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
              (fun z θ => Φs z θ + E f z θ)) 0)
          (Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0),
      hA0, hA1, hA2]
  rw [hval] at hmain
  exact hmain

/-! ## The reduction -/

/-- **The μ/λ clause from the three zero-mode estimates.**  For `9Kα ≤ 2` one has
`|μ| ≤ 3Kα/2 ≤ 1/3`, hence `|λ| ≤ 1`, which is exactly the conjunction of
`Work.FTS.StrongEps.MuLamOK` (`|μ| ≤ 1/2` and `|λ| ≤ 1`). -/
theorem MuLamOK_of_zeroModes {α C₀ K : ℝ} {Φs : Fn} {E : Fn → Fn}
    (hα : 0 < α) (h0 : ZeroMode0 α C₀ K) (h1 : ZeroMode1 α C₀ K Φs E)
    (h2 : ZeroMode2 α C₀ K) (hsmall : 9 * K * α ≤ 2) :
    Work.FTS.StrongEps.MuLamOK α C₀ Φs E := by
  intro f hf hX
  have hmu := abs_muDyn_le_three_halves hα h0 h1 h2 f hf hX
  have hthird : |muDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => f z θ))
      (fun z θ _ => f z θ) 0| ≤ 1 / 3 := by
    linarith
  exact ⟨by linarith, by rw [lamDyn_lambda_zero]; exact abs_lamfun_le_one hthird⟩

end Work.FTS_MuLamOK
