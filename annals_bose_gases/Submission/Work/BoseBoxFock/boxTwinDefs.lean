import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB4.creOf_annOf_eq_dGamma
import Submission.Work.BoseBoxFock.BombNExcDefs
import Submission.Work.BoseBoxFock.BombPairAux
import Submission.Work.BoseBoxFock.dGamma_rows
import Submission.Work.BoseDict.boxWordTwins
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxTwinDefs` — the box twins of the rows of `H2ndF` (BF3, stage A)

`Work.BoseBoxFock.H2ndF` is FS's `eq:HLambdaSecond` written on the *model* Fock space
`RealFock m` as a sum of eleven ladder words.  `Work.BoseBoxFock.box_to_model` needs the
same operator on the **box** side: the second half of the bridge is the *operator* identity

    `boxRealise e (d+2) (H2ndF f g NH PHs E gHat0 Ψ) = AVf e f g T_NH PHs E gHat0 d
        (boxRealise e (d+2) Ψ)`                                              (AVdict)

for every `Ψ` of degree `d+2` (given `NH = dGamma m T_NH`), together with its pairing
consequence (`Work.BoseDict.boxRealise_cIPn_gen`):

    `cIPn (d+2) (boxRealise e (d+2) Ψ) (AVf … d (boxRealise e (d+2) Ψ'))
       = ((bomb m Ψ (H2ndF … Ψ') : ℝ) : ℂ)`.

This module supplies the **vocabulary**: the three box word shapes

* `bW2 e w v d` — the twin of the two-letter word `creOf w ∘ annOf v`;
* `bW4 e w₁ w₂ v₁ v₂ d` — the twin of the four-letter word
  `creOf w₁ ∘ creOf w₂ ∘ annOf v₁ ∘ annOf v₂`;
* `bOB e T` — the twin of the one-body operator `dGamma m T` (the slot sum `boxSlotSum e T`),

and the operator `AVf` obtained from `H2ndF`'s expression tree by the termwise substitution

| model row of `H2ndF` | box twin |
|---|---|
| `Σ_k τ_k a_k†a_k` | `Σ_k τ_k • boxSlotSum e (rankOne (f k))` |
| `b(2ℓ²)⁻¹(N − n₀)` | `b(2ℓ²)⁻¹ • boxSlotSum e (boxT0 m)` (`nExc = dGamma boxT0`) |
| `ε_Tb(2d²ℓ²)⁻¹ NH` | `ε_Tb(2d²ℓ²)⁻¹ • boxSlotSum e T_NH` (given `NH = dGamma m T_NH`) |
| `½ℓ⁻³(ĝ(0)+Ŵ₁ω(0)) a₀†²a₀²` | `½ℓ⁻³(ĝ(0)+Ŵ₁ω(0)) • bW4 e e₀ e₀ e₀ e₀ d` |
| `−μĝ(0) n₀` | `−μĝ(0) • boxSlotSum e (rankOne e₀)` |
| the `(Ŵ₁+Ŵ₁ω) a₀†a_k†a_ka₀` row | `ℓ⁻³ • Σ_k (Ŵ₁(k)+Ŵ₁ω(k)) • bW4 e e₀ (f k) (f k) e₀ d` |
| the Bogoliubov pair row | `½ℓ⁻³ • Σ_k Ŵ₁(k) • (bW4 e e₀ e₀ (f k) (f(−k)) d + bW4 e (f k) (f(−k)) e₀ e₀ d)` |
| the two `χ̂`-linear rows | `Σ_k χ̂(k) • (L0box ∘ bW2 e (f k) e₀ d + bW2 e e₀ (f k) d ∘ L0box)` |
| the two `χ̂²`-linear rows | `Σ_{s∈ex} χ̂²(s) • (L1box ∘ bW2 e (g s) e₀ d + bW2 e e₀ (g s) d ∘ L1box)` |
| the `(L₀+L₁)∘Σ_k a_k†a_k` row | `(L0box+L1box) ∘ Σ_k boxSlotSum e (rankOne (f k))` |
| the `Q̃₃` row | `ℓ⁻³ • Σ_{s∈ex} Σ_{k∈PHs} f_L(s)Ŵ₁(k) • (bW4 e e₀ (g s) (f(s−k)) (f k) d + bW4 e (f k) (f(s−k)) (g s) e₀ d)` |

with `L0box`, `L1box` the box twins of `L0 = ℓ⁻³Ŵ₁(0) n₀ − μŴ₁(0)`, `L1 = ℓ⁻³Ŵ₁ω(0) n₀`
(namely `(ℓ⁻³Ŵ₁(0))•boxSlotSum e (rankOne e₀) − (μŴ₁(0))•1` and `(ℓ⁻³Ŵ₁ω(0))•boxSlotSum e
(rankOne e₀)`).

**Degree convention.**  `d` is the *lowest* degree of the word: `AVf … d` acts on
`Xn (d+2) → ℂ` (every intermediate degree is written `d + j` with a numeral `j`, so all
the `Fin`-indices are defeq — the `Nat`-subtraction form is *not* definitionally typed).
The one-body twins `boxSlotSum e T` are polymorphic in the degree and are simply applied at
`Xn (d+2)`.

The identity `(AVdict)` and its row-by-row proofs are in
`Submission/Work/BoseBoxFock/boxTwin.lean`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

open Work.BoseB4 Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

variable {m : ℕ} [NeZero m]

/-! ## 1. The one-particle rank-one operator and its second quantisation -/

/-- The one-particle rank-one operator `|v⟩⟨v| : x ↦ (Σ_l x_l v_l) • v`. -/
noncomputable def rankOne (v : Fin m → ℝ) : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  (∑ l : Fin m, v l • LinearMap.proj l).smulRight v

/-- **The rank-one bridge**: the second quantisation of `|v⟩⟨v|` is the ladder word
`creOf v ∘ annOf v` (`Work.BoseB4.creOf_annOf_eq_dGamma`). -/
theorem dGamma_rankOne_eq (v : Fin m → ℝ) :
    dGamma m (rankOne v) = (creOf m v).comp (annOf m v) :=
  (Work.BoseB4.creOf_annOf_eq_dGamma v v).symm

/-- The one-particle operator of the kinetic row, `T = Σ_k τ_k |f_k⟩⟨f_k|`. -/
noncomputable def Tkin {Mode : Type*} [Fintype Mode] (tau : Mode → ℝ)
    (f : Mode → Fin m → ℝ) : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  ∑ k : Mode, tau k • rankOne (f k)

/-- The one-particle operator of the `(L₀+L₁)∘Σ_k a_k†a_k` row:
`T = Σ_k |f_k⟩⟨f_k|`. -/
noncomputable def Tnum {Mode : Type*} [Fintype Mode] (f : Mode → Fin m → ℝ) :
    (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  ∑ k : Mode, rankOne (f k)

/-! ## 2. The three box word shapes -/

/-- The box twin of the two-letter word `creOf w ∘ annOf v`, on degree-`(d+2)` states. -/
noncomputable def bW2 (e : Fin m → Sp → ℂ) (w v : Fin m → ℝ) (d : ℕ) :
    (Xn (d + 2) → ℂ) → (Xn (d + 2) → ℂ) :=
  fun Θ => boxCreOf e w (d + 1) (boxAnnOf e v (d + 1) Θ)

/-- The box twin of the four-letter word `creOf w₁ ∘ creOf w₂ ∘ annOf v₁ ∘ annOf v₂`, on
degree-`(d+2)` states. -/
noncomputable def bW4 (e : Fin m → Sp → ℂ) (w₁ w₂ v₁ v₂ : Fin m → ℝ) (d : ℕ) :
    (Xn (d + 2) → ℂ) → (Xn (d + 2) → ℂ) :=
  fun Θ => boxCreOf e w₁ (d + 1)
    (boxCreOf e w₂ d (boxAnnOf e v₁ d (boxAnnOf e v₂ (d + 1) Θ)))

/-- The box twin of a one-body operator `dGamma m T` (`= boxSlotSum e T`, applied at
degree `d + 2`). -/
noncomputable def bOB (e : Fin m → Sp → ℂ) (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) {d : ℕ} :
    (Xn (d + 2) → ℂ) → (Xn (d + 2) → ℂ) :=
  fun Θ => boxSlotSum e T Θ

/-! ## 3. The box twin of the model Hamiltonian -/

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- The box twin of `L₀ = ℓ⁻³Ŵ₁(0) n₀ − μŴ₁(0)`. -/
noncomputable def L0box (e : Fin m → Sp → ℂ) (E : Work.BoseB7.Q3Env Mode) (d : ℕ) :
    (Xn (d + 2) → ℂ) → (Xn (d + 2) → ℂ) :=
  (E.ell ^ (-(3 : ℝ)) * E.W1 0) • (bOB e (rankOne (evec0 m)) (d := d))
    - (E.mu * E.W1 0) • (id : (Xn (d + 2) → ℂ) → (Xn (d + 2) → ℂ))

/-- The box twin of `L₁ = ℓ⁻³Ŵ₁ω(0) n₀`. -/
noncomputable def L1box (e : Fin m → Sp → ℂ) (E : Work.BoseB7.Q3Env Mode) (d : ℕ) :
    (Xn (d + 2) → ℂ) → (Xn (d + 2) → ℂ) :=
  (E.ell ^ (-(3 : ℝ)) * E.W1omega0) • (bOB e (rankOne (evec0 m)) (d := d))

/-- **The box twin of `H2ndF`** — the first-quantised `H_Λ^{2nd}` on degree-`(d+2)` box
states, obtained from `Work.BoseBoxFock.H2ndF` by the termwise substitution of the table in
the module docstring.  Its defining property is `boxRealise_H2ndF`
(`Submission/Work/BoseBoxFock/boxTwin.lean`). -/
noncomputable def AVf (e : Fin m → Sp → ℂ) (f g : Mode → Fin m → ℝ)
    (T_NH : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (PHs : Finset Mode)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) (d : ℕ) :
    (Xn (d + 2) → ℂ) → (Xn (d + 2) → ℂ) :=
  (∑ k : Mode, E.tau k • (bOB e (rankOne (f k)) (d := d)))
  + (E.b / (2 * E.ell ^ 2)) • (bOB e (boxT0 m) (d := d))
  + (E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) • (bOB e T_NH (d := d))
  + ((1 / 2 : ℝ) * E.ell ^ (-(3 : ℝ)) * (gHat0 + E.W1omega0)) •
      (bW4 e (evec0 m) (evec0 m) (evec0 m) (evec0 m) d)
  - (E.mu * gHat0) • (bOB e (rankOne (evec0 m)) (d := d))
  + (E.ell ^ (-(3 : ℝ))) • ∑ k : Mode,
      (E.W1 k + E.W1omega k) • (bW4 e (evec0 m) (f k) (f k) (evec0 m) d)
  + ((1 / 2 : ℝ) * E.ell ^ (-(3 : ℝ))) • ∑ k : Mode, E.W1 k •
      (bW4 e (evec0 m) (evec0 m) (f k) (f (-k)) d
        + bW4 e (f k) (f (-k)) (evec0 m) (evec0 m) d)
  + ∑ k : Mode, E.hatChi k •
      ((L0box e E d) ∘ (bW2 e (f k) (evec0 m) d)
        + (bW2 e (evec0 m) (f k) d) ∘ (L0box e E d))
  + ∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s •
      ((L1box e E d) ∘ (bW2 e (g s) (evec0 m) d)
        + (bW2 e (evec0 m) (g s) d) ∘ (L1box e E d))
  + (L0box e E d + L1box e E d) ∘ (∑ k : Mode, bOB e (rankOne (f k)) (d := d))
  + (E.ell ^ (-(3 : ℝ))) • ∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ PHs,
      (E.fL s * E.W1 k) •
        (bW4 e (evec0 m) (g s) (f (s - k)) (f k) d
          + bW4 e (f k) (f (s - k)) (g s) (evec0 m) d)

end Work.BoseBoxFock
