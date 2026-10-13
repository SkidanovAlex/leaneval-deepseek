/-
# `Submission/Work/FTS_MuLipC/Defs.lean` — the class-`C` Lipschitz bound of the modulation

Subproject **FTS_MuLipC** (design §G2 item (1c) `MuLipC` of
`sources/ftsV2/fts_final_redesign.md`, owner FTS_MuLamOK).

**Deliverable.** `Work.FTS_MuLipC.muLipC_pExp`, a proof with the *identical type* of
`Work.FTS.FinalV2.muLipC_pExp` (the frozen producer of
`Submission/Work/FTS/FinalV2/Producers.lean`, conjunct (1c)):

```
theorem muLipC_pExp {C₀ Ce Cs : ℝ} (hC₀ : 0 < C₀) :
    ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ {Φs : Fn} {E : Fn →ₗ[ℝ] Fn},
      Work.FTS.VocabO2.StarPkgo2 (pExp α) Cs Φs →
      (∀ f : Fn, ClassC (pExp α) f → EllPkgGo (pExp α) Ce f (E f)) →
      MuLipC (pExp α) C₀ Φs E
```

i.e. the `μ`-functional of the modulation problem is *Lipschitz* in the profile on the
class `C`:

`|μ(f) − μ(f')| ≤ L·|f − f'|_{ℋ⁴}`   for `ClassC` profiles of `ℋ⁴`-size `≤ C₀α²`,

the class-`C` input (1c) consumed by `mu6'` ((6′): the `τ`-Hölder regularity of `μ`).

## The mathematical content

Write `g ↦ constFam g := fun z θ _ => g z θ`.  At the constant family, the modulation is
`Work.Construction.mufunS` at the profile (`Work.FTS_MuLamOK.muDyn_lambda_zero`, definitional):

```
2α·μ(g) = L₁₂(N₀ α (F_*+g) g)(0) + L₁₂(N α (F_*+g) (Φ_s + E g))(0)
            + L₁₂(3 D_θ g/(1+z))(0)
```

(the sign of the transport term is the corrected one of `two_mul_mufunS`).  Each of the three
`L₁₂`-zero-modes is a **polynomial of degree ≤ 2 in the profile**:

* `N₀`, the quadratic term, is `C₀ + Lin₀(g) + Quad₀(g)` where
  `Lin₀(g) = (3/(2α))·s2·L₁₂(F_*)·∂_θF_* − c2m·L₁₂(F_*)·D_zF_* − c2m·L₁₂(F_*)·D_zg` and
  `Quad₀(g) = (1/α)(L₁₂ g)·g + (3/(2α))·L₁₂(g)·D_θg − c2m·(L₁₂ g)·D_zg`;
* `N` is a sum of products of a "stream-function factor" (`ℛ(Φ̃)`, `𝒰(Φ̃)/sin 2θ`, `𝒱(Φ̃)`, the
  angular moment `FK`) with a "profile factor" (`F`, `D_θF`, `D_zF`), hence bilinear plus a
  constant term, and `Φ̃ = Φ − (1/(4α))s2·L₁₂(F)` is *linear* in `g` because `E` is linear;
* the transport zero-mode is *linear* in `g`.

Consequently the difference `μ(f) − μ(f')` (with `d := f − f'`) is a sum of products each having
**one `d`-factor** and one factor controlled by the data, and the whole task reduces to the
three **difference rows** `DiffRow0`, `DiffRow1`, `DiffRow2` below:

```
|L₁₂(S₀ f)(0) − L₁₂(S₀ f')(0)| ≤ K·|f − f'|_{ℋ⁴}   (N₀,  quadratic)
|L₁₂(S  f)(0) − L₁₂(S  f')(0)| ≤ K·|f − f'|_{ℋ⁴}   (N,   bilinear)
|L₁₂(T  f)(0) − L₁₂(T  f')(0)| ≤ K·|f − f'|_{ℋ⁴}   (transport, linear)
```

for `ClassC` profiles of `ℋ⁴`-size `≤ C₀α²` (`C₀α² ≤ 1`) and a constant `K` depending on
`α, C₀, Ce, Cs` only.

## How the difference rows are proved (the route that works here)

The *single-profile* rows are already *proved*: `Work.FTS_MuLamOK.Rows.Rl0Open`,
`Rows.Rl1Open`, `Rows.Rl2Open` (exposed as `KMu0_row`, `KMu1_row`, `KMu2_row` in
`Work.FTS_MuLamOK.Main`), each in the envelope form

`|L₁₂(field)(0)| ≤ K·(α² + √α·X + α^{-3/2}·X²)`,   `X = Xn α f`   (`Env α X`).

The difference rows are then obtained by **polarization of the polynomial structure**: for a
field-valued polynomial `P(g) = C + Lin(g) + Quad(g)` and its `L₁₂`-zero-mode `Φ(g) = L₁₂(P g)(0)`,

* `Φ(f) − Φ(f') = L₁₂(Lin d)(0) + L₁₂(B(f+f', d))(0)`   where `B(u,v) = (Quad(u+v) − Quad(u−v))/4`;
* `L₁₂(B(u,d))(0) + ½L₁₂(Lin d)(0) = (1/(4t))·(Φ(u+td) − Φ(u−td))`  for every `t > 0`;
* `L₁₂(Lin d)(0) = (1/(2t))·(Φ(td) − Φ(−td))`;

so that, choosing `t := α²/Xn d`, the *single-profile row* applied at the profiles `u ± td` and
`±td` — all of them `ClassC` (the class is a linear subspace) with `ℋ⁴`-size `≤ C₀α² + α²` —
produces the difference rows with a constant independent of `f, f'`.  The only structural inputs
are the **linearity of `L₁₂` on the class** (`Work.FTS.GalFields.RHS.Sharp.L12_sub_ge0`,
`Work.FTS.LocData.L12_add_mul`, `Work.FTS.GalBasis.L12_congr_all`), the **polynomial identities**
of the fields, and `|u + v|_{ℋ⁴} ≤ √2(|u|_{ℋ⁴} + |v|_{ℋ⁴})` /
`|c·u|_{ℋ⁴} = |c|·|u|_{ℋ⁴}` (`Work.FTS.EllipticEst.HkNorm_add_le`, `HkNorm_const_mul`).

## Contents

* `Env` — the paper's envelope `α² + √α·X + α^{-3/2}X²` and its monotonicity;
* `Sn0`, `Sn`, `Tf` — the three fields whose `L₁₂`-zero-modes make up `2α·μ`;
* `muDyn_const_eq` — the definitional identification of `muDyn` at the constant family with those
  three `L₁₂`-values;
* `DiffRow0`, `DiffRow1`, `DiffRow2` — the three difference rows;
* `muLipC_of_diffRows` — the arithmetic: the three difference rows give `MuLipC`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_MuLamOK.Main
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.ClassC.A1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_MuLipC

open Work.FTS.Galerkin (Fn Fam slice muDyn)

set_option autoImplicit false

/-! ## The paper's envelope -/

/-- The envelope `α² + √α·X + α^{-3/2}·X²` of the three single-profile rows
(`Work.FTS.NonlinRows.Rl1.Env`). -/
def Env (α X : ℝ) : ℝ := α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2

theorem Env_nonneg {α X : ℝ} (hα : 0 ≤ α) (hX : 0 ≤ X) : 0 ≤ Env α X := by
  refine add_nonneg (add_nonneg (sq_nonneg α) ?_) ?_
  · exact mul_nonneg (Real.sqrt_nonneg α) hX
  · exact mul_nonneg (Real.rpow_nonneg hα _) (sq_nonneg X)

/-! ## The three fields of the modulation -/

/-- The `N₀`-field of the profile `g`: `N₀ α (F_*+g) g`. -/
def Sn0 (α : ℝ) (g : Fn) : Fn := Work.Construction.N0 α (Work.Construction.Ftot α g) g

/-- The `N`-field of the profile `g` at the stream function `Φ_s + E g`. -/
def Sn (α : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fn) : Fn :=
  Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + E g z θ)

/-- The transport field `3 D_θg/(1+z)`. -/
def Tf (g : Fn) : Fn := fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)

@[simp] theorem Sn0_apply (α : ℝ) (g : Fn) (z θ : ℝ) :
    Sn0 α g z θ = Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ := rfl

@[simp] theorem Sn_apply (α : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fn) (z θ : ℝ) :
    Sn α Φs E g z θ
      = Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + E g z θ) z θ :=
  rfl

@[simp] theorem Tf_apply (g : Fn) (z θ : ℝ) :
    Tf g z θ = 3 * Work.Spaces.Dth g z θ / (1 + z) := rfl

/-- **The modulation at the constant family is the `mufunS` of the three fields** `Sn0`, `Sn`,
`Tf`.  This is `Work.FTS_MuLamOK.muDyn_lambda_zero` together with the definition of
`Work.Construction.mufunS` (both sides unfold to the same `L₁₂`-expression). -/
theorem muDyn_const_eq (α : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fn) :
    muDyn α (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.FinalV2.cst g)) (Work.FTS.FinalV2.cst g) 0
      = (1 / (2 * α)) * (Work.Construction.L12 (Sn0 α g) 0
          + Work.Construction.L12 (Sn α Φs E g) 0)
        + (1 / (2 * α)) * Work.Construction.L12 (Tf g) 0 := rfl

/-! ## The three difference rows -/

/-- **The difference row of `N₀`.**  For `ClassC` profiles of `ℋ⁴`-size `≤ C₀α²` the `L₁₂`-zero
mode of the quadratic field `N₀ α (F_*+g) g` is Lipschitz in the profile, with a constant
depending on `α` and `C₀` only. -/
def DiffRow0 (α C₀ : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ f f' : Fn,
    Work.FTS.ClassC.ClassC α f → Work.FTS.ClassC.ClassC α f' →
    Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 → Work.FTS.Nonlin.Xn α f' ≤ C₀ * α ^ 2 →
    |Work.Construction.L12 (Sn0 α f) 0 - Work.Construction.L12 (Sn0 α f') 0|
      ≤ K * Work.FTS.Nonlin.Xn α (f - f')

/-- **The difference row of `N`.**  Same statement for the bilinear field
`N α (F_*+g) (Φ_s + E g)`; here `E` is a *linear* map (that is the hypothesis of the frozen
producer) so that `E(f − f') = E f − E f'`, and `Φ_s` satisfies the star package. -/
def DiffRow1 (α C₀ : ℝ) (Φs : Fn) (E : Fn → Fn) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ f f' : Fn,
    Work.FTS.ClassC.ClassC α f → Work.FTS.ClassC.ClassC α f' →
    Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 → Work.FTS.Nonlin.Xn α f' ≤ C₀ * α ^ 2 →
    |Work.Construction.L12 (Sn α Φs E f) 0 - Work.Construction.L12 (Sn α Φs E f') 0|
      ≤ K * Work.FTS.Nonlin.Xn α (f - f')

/-- **The difference row of the transport term.**  The transport zero-mode is *linear* in the
profile, so its difference row is the single-profile row of `Work.FTS.NonlinRows.rl2`
(`KMu2_row`), transported to the difference `f − f'` on the class. -/
def DiffRow2 (α C₀ : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ f f' : Fn,
    Work.FTS.ClassC.ClassC α f → Work.FTS.ClassC.ClassC α f' →
    Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 → Work.FTS.Nonlin.Xn α f' ≤ C₀ * α ^ 2 →
    |Work.Construction.L12 (Tf f) 0 - Work.Construction.L12 (Tf f') 0|
      ≤ K * Work.FTS.Nonlin.Xn α (f - f')

/-! ## The arithmetic: the three difference rows give `MuLipC` -/

/-- **The class-`C` Lipschitz bound from the three difference rows.**  `2α·μ` is the *sum* of the
three `L₁₂`-zero-modes, so the difference `μ(f) − μ(f')` is `(1/(2α))` times the sum of the three
differences, and the triangle inequality gives the constant `(K₀+K₁+K₂)/(2α)`. -/
theorem muLipC_of_diffRows {α C₀ : ℝ} {Φs : Fn} {E : Fn → Fn}
    (hα : 0 < α) (h0 : DiffRow0 α C₀) (h1 : DiffRow1 α C₀ Φs E) (h2 : DiffRow2 α C₀) :
    Work.FTS.FinalV2.MuLipC α C₀ Φs E := by
  obtain ⟨K0, hK0, hrow0⟩ := h0
  obtain ⟨K1, hK1, hrow1⟩ := h1
  obtain ⟨K2, hK2, hrow2⟩ := h2
  refine ⟨(K0 + K1 + K2) / (2 * α), by positivity, ?_⟩
  intro f f' hf hf' hXf hXf'
  have hA := hrow0 f f' hf hf' hXf hXf'
  have hB := hrow1 f f' hf hf' hXf hXf'
  have hC := hrow2 f f' hf hf' hXf hXf'
  set X : ℝ := Work.FTS.Nonlin.Xn α (f - f') with hX
  have hXnn : 0 ≤ X := by
    rw [hX]; exact Work.Spaces.HkNorm_nonneg α 4 _
  have hsum : |Work.Construction.L12 (Sn0 α f) 0 - Work.Construction.L12 (Sn0 α f') 0
      + (Work.Construction.L12 (Sn α Φs E f) 0 - Work.Construction.L12 (Sn α Φs E f') 0)
      + (Work.Construction.L12 (Tf f) 0 - Work.Construction.L12 (Tf f') 0)|
      ≤ (K0 + K1 + K2) * X := by
    have ht1 := abs_add_le (Work.Construction.L12 (Sn0 α f) 0
        - Work.Construction.L12 (Sn0 α f') 0)
      (Work.Construction.L12 (Sn α Φs E f) 0 - Work.Construction.L12 (Sn α Φs E f') 0)
    have ht2 := abs_add_le
      ((Work.Construction.L12 (Sn0 α f) 0 - Work.Construction.L12 (Sn0 α f') 0)
        + (Work.Construction.L12 (Sn α Φs E f) 0 - Work.Construction.L12 (Sn α Φs E f') 0))
      (Work.Construction.L12 (Tf f) 0 - Work.Construction.L12 (Tf f') 0)
    rw [hX] at hA hB hC
    linarith
  rw [muDyn_const_eq, muDyn_const_eq]
  have hfac : (1 / (2 * α)) * (Work.Construction.L12 (Sn0 α f) 0
        + Work.Construction.L12 (Sn α Φs E f) 0)
      + (1 / (2 * α)) * Work.Construction.L12 (Tf f) 0
      - ((1 / (2 * α)) * (Work.Construction.L12 (Sn0 α f') 0
        + Work.Construction.L12 (Sn α Φs E f') 0)
      + (1 / (2 * α)) * Work.Construction.L12 (Tf f') 0)
      = (1 / (2 * α)) * ((Work.Construction.L12 (Sn0 α f) 0
            - Work.Construction.L12 (Sn0 α f') 0)
          + (Work.Construction.L12 (Sn α Φs E f) 0 - Work.Construction.L12 (Sn α Φs E f') 0)
          + (Work.Construction.L12 (Tf f) 0 - Work.Construction.L12 (Tf f') 0)) := by
    ring
  rw [hfac, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * α))]
  calc (1 / (2 * α)) * |Work.Construction.L12 (Sn0 α f) 0
          - Work.Construction.L12 (Sn0 α f') 0
        + (Work.Construction.L12 (Sn α Φs E f) 0 - Work.Construction.L12 (Sn α Φs E f') 0)
        + (Work.Construction.L12 (Tf f) 0 - Work.Construction.L12 (Tf f') 0)|
      ≤ (1 / (2 * α)) * ((K0 + K1 + K2) * X) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (K0 + K1 + K2) / (2 * α) * X := by ring

end Work.FTS_MuLipC
