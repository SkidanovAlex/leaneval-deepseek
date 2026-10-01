/-
# ZeroFreeTables — t23Defs

The vocabulary of **HB Tables 2 and 3** (`HBTable2and3_engine`): the normalised `hb72G`
evaluation of the `F`-expressions of HB Lemma 6.3 for the test function of HB Lemma 7.2, the
row data, the row certificates, the coverage, and the two analytic inputs
(`GlueWitness`, `GlueH63`).

Everything here is definitional; the lemmas live in the modules that prove them.

**IMPORTANT (build order).**  A module that proves one of the `Prop`s below must import *this*
module (`Submission.Work.ZeroFreeTables.t23Defs`) and **not**
`Submission.Work.ZeroFreeTables.HBTable2and3_engine`: the engine module imports the piece modules
and would then be part of a cycle.  (The engine module's own file has no definitions that are not
re-exported through this one.)
-/
import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## The normalised evaluation of the `F`-expressions

Writing `g(u) = (2-u)³(4+6u+u²) = 32 - 40u² + 20u³ - u⁵` and `G(x) = ∫₀² g(u)e^{xu}du`, the
Laplace transform of HB Lemma 7.2's test function at scale `λ` is `F_λ(z) = G(-z/λ)/30`; hence
the row evaluation `2(F_λ(-v) - F_λ(b-v))` equals `(1/15)(G(v/λ) - G((v-b)/λ))`, a function of
the rational data `(λ,b,v)` alone. -/

/-- HB Lemma 7.2's density `g(u) = (2-u)³(4+6u+u²) = 32 - 40u² + 20u³ - u⁵`. -/
def hb72g (u : ℝ) : ℝ := 32 - 40 * u ^ 2 + 20 * u ^ 3 - u ^ 5

/-- `G(x) = ∫₀² g(u) e^{xu} du`. -/
def hb72G (x : ℝ) : ℝ := ∫ u in (0:ℝ)..2, hb72g u * Real.exp (x * u)

/-- The constant of the certificates: the coefficient `1/4 + 2·10⁻⁶ + 4·10⁻³` of the `f(0)`-term
of the HB Lemma 6.3 inequality, `2c + 4ε` with `c = 1/8 + 10⁻⁶` (`Table4.l52HypRealQuarter`)
and `ε = 10⁻³`. -/
def CertSlack : ℝ := 1 / 4 + 1 / 500000 + 4 * (1 / 1000)

/-- `G a − G(a−b) = ∫₀² g(u) e^{au}(1 − e^{−bu}) du`. -/
theorem hb72G_sub (a b : ℝ) :
    hb72G a - hb72G (a - b)
      = ∫ u in (0:ℝ)..2, hb72g u * Real.exp (a * u) * (1 - Real.exp (-(b * u))) := by
  have hcont : ∀ c : ℝ, ContinuousOn (fun u : ℝ => hb72g u * Real.exp (c * u)) (Set.Icc 0 2) :=
    fun c => by unfold hb72g; fun_prop
  have hint : ∀ c : ℝ, IntervalIntegrable (fun u : ℝ => hb72g u * Real.exp (c * u))
      MeasureTheory.volume (0 : ℝ) 2 := fun c =>
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (by
      simpa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)] using hcont c)
  rw [hb72G, hb72G, ← intervalIntegral.integral_sub (hint a) (hint (a - b))]
  exact intervalIntegral.integral_congr (fun u _ => by
    rw [show Real.exp ((a - b) * u) = Real.exp (a * u) * Real.exp (-(b * u)) by
      rw [← Real.exp_add]; ring_nf]
    ring)

/-! ## The row data of Tables 2 and 3 -/

/-- The first batch of the Tables 2/3 certificate (see `RowCert`). -/
def rowA : List (ℝ × ℝ × ℝ) :=
  [((2.3 : ℝ), (0.2 : ℝ), (3.244 : ℝ)),
   ((2.3 : ℝ), (0.198 : ℝ), (3.273 : ℝ)),
   ((2.3 : ℝ), (0.195 : ℝ), (3.305 : ℝ)),
   ((2.3 : ℝ), (0.192 : ℝ), (3.341 : ℝ)),
   ((2.3 : ℝ), (0.188 : ℝ), (3.382 : ℝ)),
   ((2.3 : ℝ), (0.184 : ℝ), (3.428 : ℝ))]

/-- The second batch (see `RowCert`). -/
def rowB : List (ℝ × ℝ × ℝ) :=
  [((2.35 : ℝ), (0.18 : ℝ), (3.481 : ℝ)),
   ((2.35 : ℝ), (0.175 : ℝ), (3.542 : ℝ)),
   ((2.35 : ℝ), (0.17 : ℝ), (3.611 : ℝ)),
   ((2.35 : ℝ), (0.164 : ℝ), (3.69 : ℝ)),
   ((2.35 : ℝ), (0.158 : ℝ), (3.78 : ℝ)),
   ((2.4 : ℝ), (0.151 : ℝ), (3.883 : ℝ))]

/-- The third batch (see `RowCert`). -/
def rowC : List (ℝ × ℝ × ℝ) :=
  [((2.4 : ℝ), (0.144 : ℝ), (4.001 : ℝ)),
   ((2.4 : ℝ), (0.135 : ℝ), (4.136 : ℝ)),
   ((2.4 : ℝ), (0.126 : ℝ), (4.291 : ℝ)),
   ((2.45 : ℝ), (0.117 : ℝ), (4.469 : ℝ)),
   ((2.45 : ℝ), (0.107 : ℝ), (4.674 : ℝ)),
   ((2.5 : ℝ), (0.097 : ℝ), (4.909 : ℝ))]

/-- The fourth batch (see `RowCert`). -/
def rowD : List (ℝ × ℝ × ℝ) :=
  [((2.5 : ℝ), (0.086 : ℝ), (5.18 : ℝ)),
   ((2.55 : ℝ), (0.075 : ℝ), (5.491 : ℝ)),
   ((2.55 : ℝ), (0.064 : ℝ), (5.849 : ℝ)),
   ((2.6 : ℝ), (0.054 : ℝ), (6.259 : ℝ)),
   ((2.6 : ℝ), (0.044 : ℝ), (6.728 : ℝ)),
   ((2.65 : ℝ), (0.035 : ℝ), (7.262 : ℝ))]

/-- The fifth batch (see `RowCert`). -/
def rowE : List (ℝ × ℝ × ℝ) :=
  [((2.7 : ℝ), (0.026 : ℝ), (7.867 : ℝ)),
   ((2.7 : ℝ), (0.02 : ℝ), (8.5 : ℝ)),
   ((549/200 : ℝ), (0.0145 : ℝ), (9.24 : ℝ)),
   ((139/50 : ℝ), (0.0102 : ℝ), (10.0 : ℝ)),
   ((113/40 : ℝ), (0.0068 : ℝ), (10.9 : ℝ)),
   ((2.8 : ℝ), (0.006 : ℝ), (11.071 : ℝ))]

/-- The **gap-filling rows**. -/
def rowF : List (ℝ × ℝ × ℝ) :=
  [((23/10 : ℝ), (588/3125 : ℝ), (1673/500 : ℝ)),
   ((23/10 : ℝ), (9217/50000 : ℝ), (3389/1000 : ℝ)),
   ((47/20 : ℝ), (3603/20000 : ℝ), (3433/1000 : ℝ)),
   ((47/20 : ℝ), (2193/12500 : ℝ), (3489/1000 : ℝ)),
   ((47/20 : ℝ), (17017/100000 : ℝ), (3547/1000 : ℝ)),
   ((47/20 : ℝ), (411/2500 : ℝ), (3619/1000 : ℝ)),
   ((47/20 : ℝ), (15803/100000 : ℝ), (1847/500 : ℝ)),
   ((12/5 : ℝ), (3777/25000 : ℝ), (473/125 : ℝ)),
   ((12/5 : ℝ), (13527/100000 : ℝ), (501/125 : ℝ)),
   ((12/5 : ℝ), (3161/25000 : ℝ), (2073/500 : ℝ)),
   ((49/20 : ℝ), (11701/100000 : ℝ), (859/200 : ℝ)),
   ((49/20 : ℝ), (2141/20000 : ℝ), (4473/1000 : ℝ)),
   ((51/20 : ℝ), (7503/100000 : ℝ), (648/125 : ℝ)),
   ((51/20 : ℝ), (3211/50000 : ℝ), (5501/1000 : ℝ)),
   ((27/10 : ℝ), (2649/100000 : ℝ), (7303/1000 : ℝ)),
   ((14/5 : ℝ), (313/50000 : ℝ), (2047/200 : ℝ))]

/-- **The row data of Tables 2 and 3**: a triple `(λ, b, v)` means "for the test function of
HB Lemma 7.2 at scale `λ`, every `λ₁ ≤ b` forces `λ₀ ≥ v`". -/
def t23rows : List (ℝ × ℝ × ℝ) := rowA ++ rowB ++ rowC ++ rowD ++ rowE ++ rowF

/-- The scales of the test functions occurring in `t23rows` and `rowG`. -/
def t23lams : List ℝ :=
  [3, 23/10, 47/20, 12/5, 49/20, 5/2, 51/20, 13/5, 53/20, 27/10, 11/4, 14/5,
   549/200, 139/50, 113/40, 41/20, 21/10, 43/20, 9/4]

/-- **The certificate of Tables 2 and 3.**  For every row `(λ, b, v)`, the `F`-expression of
HB Lemma 6.3 *fails* at `(λ₀, λ₁) = (v, b)` for the test function of HB Lemma 7.2 at scale `λ`,
with the constant `CertSlack`:
`(1/15)(G(v/λ) − G((v−b)/λ)) < 8/9 − CertSlack·(16λ/15)`. -/
def RowCert : Prop :=
  ∀ p : ℝ × ℝ × ℝ, p ∈ t23rows →
    (1 / 15) * (hb72G (p.2.2 / p.1) - hb72G ((p.2.2 - p.2.1) / p.1))
      < 8 / 9 - CertSlack * (16 * p.1 / 15)

/-- **Rows for the top of the second conjunct's range** (`λ₁ ∈ (1/5, 2/5]`): the same shape as
`t23rows`, with the requirement `(3/2)·log(1/λ₁)` in mind. -/
def rowG : List (ℝ × ℝ × ℝ) :=
  [((41/20 : ℝ), (2/5 : ℝ), (169/100 : ℝ)),
   ((21/10 : ℝ), (7/20 : ℝ), (199/100 : ℝ)),
   ((43/20 : ℝ), (3/10 : ℝ), (233/100 : ℝ)),
   ((9/4 : ℝ), (1/4 : ℝ), (273/100 : ℝ))]

/-- The certificate for `rowG`. -/
def RowCertG : Prop :=
  ∀ p : ℝ × ℝ × ℝ, p ∈ rowG →
    (1 / 15) * (hb72G (p.2.2 / p.1) - hb72G ((p.2.2 - p.2.1) / p.1))
      < 8 / 9 - CertSlack * (16 * p.1 / 15)

/-- **The coverage of the tables.**  Every `λ₁` in the two ranges of `HBTable2and3` is met by a
row of `t23rows` resp. `rowG` that applies to it and whose `v` dominates the required bound. -/
def RowCover : Prop :=
  (∀ x : ℝ, 0 < x → x ≤ 1 / 5 →
      ∃ p ∈ t23rows, x ≤ p.2.1 ∧ min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ p.2.2)
  ∧ (∀ x : ℝ, 1 / 1000 ≤ x → x ≤ 2 / 5 →
      (∃ p ∈ t23rows, x ≤ p.2.1 ∧ max ((3 / 2) * Real.log (1 / x)) (1294 / 1000) ≤ p.2.2)
      ∨ (∃ p ∈ rowG, x ≤ p.2.1 ∧ max ((3 / 2) * Real.log (1 / x)) (1294 / 1000) ≤ p.2.2))

/-! ## The two analytic inputs -/

/-- **The witness.**  For every window radius `δ ∈ (0,1/2]` there are `q₀` such that for every
`q ≥ q₀`, every real character `χ₁` with a real exceptional zero `ρ₁` (`IsMin1WideAt 10`) and every
*near-line* zero `ρ ≠ ρ₁` of the working region (`λ(ρ) ≤ δ·log q`, `λ(ρ) ≤ logloglog q/3`), there
is a zero `ρ' ≠ ρ₁` of `χ₁` and a box height `Hb` with

* `|Im ρ'| ≤ 10·log q` (the range of the log-derivative input `L52Hyp`),
* `|Im ρ'| + δ ≤ Hb` (so that the window of `ρ'` is contained in the box),
* `λ(ρ') ≤ λ(ρ)`,
* `ρ'` is `λ`-minimal among the zeros of `χ₁` other than `ρ₁` in the box `|Im| ≤ Hb`. -/
def GlueWitness : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
    IsZ χ₁ ρ → ρ ≠ ρ₁ →
    lamOf q ρ ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
    lamOf q ρ ≤ δ * Real.log (q : ℝ) →
    ∃ (ρ' : ℂ) (Hb : ℝ), zeroMult χ₁ ρ' ≠ 0 ∧ ρ' ≠ ρ₁ ∧
      |ρ'.im| ≤ 10 * Real.log (q : ℝ) ∧ |ρ'.im| + δ ≤ Hb ∧
      lamOf q ρ' ≤ lamOf q ρ ∧
      (∀ u : ℂ, zeroMult χ₁ u ≠ 0 → |u.im| ≤ Hb →
        u = ρ₁ ∨ lamOf q ρ' ≤ lamOf q u)

/-- **HB Lemma 6.3 (the engine inequality) for a witness satisfying the box-maximality.**  For
every `δ ∈ (0,1/2]` there are `q₀` with: for every `q ≥ q₀`, every real character `χ₁` with real
exceptional zero `ρ₁` (`IsMin1WideAt 10`, simple, `λ(ρ₁) ≤ 2/5`), every further zero `ρ' ≠ ρ₁` of
`χ₁` with `|Im ρ'| ≤ 10 log q`, `λ(ρ')` near-line, a box height `Hb ≥ |Im ρ'| + δ` on which `ρ'` is
maximal, and the `L52Hyp` input at `δ`, the HB Lemma 6.3 inequality holds at
`(λ₀, λ₁) = (λ(ρ'), λ(ρ₁))` for every scale `λ` of the tables:

`0 ≤ 2F_λ(−λ(ρ')) − 2F_λ(λ(ρ₁)−λ(ρ')) − F_λ(0) + f_λ(0)·CertSlack`. -/
def GlueH63 : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q)
    [NeZero χ₁.conductor] (ρ₁ ρ' : ℂ) (Hb : ℝ),
    IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
    zeroMult χ₁ ρ' ≠ 0 → ρ' ≠ ρ₁ →
    |ρ'.im| ≤ 10 * Real.log (q : ℝ) → |ρ'.im| + δ ≤ Hb →
    (∀ u : ℂ, zeroMult χ₁ u ≠ 0 → |u.im| ≤ Hb →
      u = ρ₁ ∨ lamOf q ρ' ≤ lamOf q u) →
    lamOf q ρ' ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
    lamOf q ρ' ≤ δ * Real.log (q : ℝ) →
    lamOf q ρ₁ ≤ 2 / 5 →
    zeroMult χ₁ ρ₁ = 1 →
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Commons.NumberTheory.Linnik.L52Hyp χ₁ (1 / 8 + 1 / 1000000) ε δ) →
    ∀ lam ∈ t23lams, ∀ (hlam : 0 < lam),
      0 ≤ 2 * (tf72T lam hlam).F (-(lamOf q ρ')) - 2 * (tf72T lam hlam).F (lamOf q ρ₁ - lamOf q ρ')
        - (tf72T lam hlam).F 0 + (tf72T lam hlam).f 0 * CertSlack

/-- **The multiplicity of the exceptional zero**, for the range `λ₁ ≤ 2/5`: a real zero of a real
character of minimal `λ` in `|Im| ≤ 2` with `λ ≤ 2/5` is simple. -/
def GlueSimple : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 →
    zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    (∀ u : ℂ, zeroMult χ₁ u ≠ 0 → |u.im| ≤ 2 → lamOf q (β₁ : ℂ) ≤ lamOf q u) →
    lamOf q (β₁ : ℂ) ≤ 2 / 5 →
    zeroMult χ₁ (β₁ : ℂ) = 1

/-- The `L52Hyp` input of HB Lemma 3.1 with the sharp constant `1/8 + 10⁻⁶` for **real**
characters, at a window radius `δ` fixed in advance and `δ ≤ 1/2`. -/
def GlueL52 : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∃ q₀ : ℕ,
    ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) [NeZero χ₁.conductor],
      χ₁ ≠ 1 → χ₁ ^ 2 = 1 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        Commons.NumberTheory.Linnik.L52Hyp χ₁ (1 / 8 + 1 / 1000000) ε δ

/-- **The far range.**  Either the second conjunct's bound already holds for the zero `ρ`, or
`λ(ρ)` is bounded by an absolute constant (so that the `F`-machinery, which needs a near-line test
zero, applies). -/
def GlueFar : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 → IsZ χ₁ ρ → ρ ≠ ρ₁ →
    (max ((3 / 2) * Real.log (1 / lamOf q ρ₁)) (1294 / 1000) ≤ lamOf q ρ) ∨
    (lamOf q ρ ≤ c)

/-! ## The fixed-scale (`λ = 3`) argument, and the finite facts about the row data -/

/-- The numeric input of the fixed-scale argument: `∫₀² u·g(u)·e^{(4/3)(u−2)} du < 3.3`. -/
def GlueLam3Num : Prop :=
  (∫ u in (0:ℝ)..2, u * hb72g u * Real.exp ((4 / 3) * (u - 2))) < 3.3

/-- **The fixed-scale `λ = 3` failure.**  With `λ₀ ≥ 4` and `λ₁ < e^{−2λ₀/3}` the `F`-expression of
HB Lemma 6.3 at the scale `3` fails at `(λ₀,λ₁)`, in normalized form
`(1/15)(G(λ₀/3) − G((λ₀−λ₁)/3)) < 8/9 − CertSlack·(16·3/15)`. -/
def GlueLam3 : Prop :=
  ∀ {a0 a1 : ℝ}, 4 ≤ a0 → 0 < a1 → a1 < Real.exp (-(2 / 3) * a0) → GlueLam3Num →
    (1 / 15) * (hb72G (a0 / 3) - hb72G ((a0 - a1) / 3))
      < 8 / 9 - CertSlack * (16 * 3 / 15)

/-- The scales of the rows all lie in `t23lams`. -/
def T23LamsMem : Prop :=
  ∀ p : ℝ × ℝ × ℝ, p ∈ t23rows ++ rowG → p.1 ∈ t23lams

/-- The scales of the rows are positive. -/
def T23Pos : Prop :=
  ∀ p : ℝ × ℝ × ℝ, p ∈ t23rows ++ rowG → 0 < p.1

end Work.ZeroFreeTables
