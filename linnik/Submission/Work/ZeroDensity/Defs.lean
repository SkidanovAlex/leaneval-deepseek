import Mathlib
import Submission.Work.LinnikAreas.Setup
import Submission.Work.LinnikAreas.SiegelBase

/-!
# `Work.ZeroDensity` — the zero-density theorems of the Linnik areas

This chapter is the vocabulary and the results of the *zero-density layer* of the Linnik L = 5.5
project (Heath-Brown 1992).  It is self-contained: everything is stated **uniformly in the modulus
`q`** (no constant may depend on `q`, cf. `LinnikContract/Quarantine.lean`), and the conventions are
those of `Work.LinnikContract` (`lamOf`, `zeroMult`, `IsZ`, `InBox`) and of
`Work.LinnikAreas.Setup` (`zeroCountIn`) and `Work.LinnikAreas.SiegelBase`
(`pairCount`, `pairCountHeight`), so that a consumer of the Areas can use the results here without
any transliteration.

## The three deliverables

* `FamDensity σlo c` / `FamDensityEps σlo c` — **log-free family zero-density estimate**
  `Σ_{χ mod q} N(σ,T,χ) ≤ C (qT)^{c(1-σ)+ε}` resp. `≤ C (qT)^{(c+ε)(1-σ)}` for `σ ≥ σlo`.
  The near-line version (Heath-Brown §11's zero detector with `φ = 1/2`, convexity) is
  `NearLineLogFree c A`, restricted to `(1-σ)𝓛 ≤ A log 𝓛`.
  `FamDensityEps (4/5) 2` **is** `Work.LinnikAreas.FamilyZeroDensityJutila`.
* `FamDensityPower σhi c B` / `MontgomerySharp B` — **Montgomery's density theorem**
  (multiplicative large sieve); `FamDensityPower (4/5) (12/5) B` **is**
  `Work.LinnikAreas.FamilyZeroDensityMontgomery`.
* `DHLogFree c` / `DHLogFreeHeight c c'` — the **log-free Deuring–Heilbronn bound with the `λ₁`
  factor**, covering the principal character; these are the `PairDensityInput` /
  `PairDensityHeightInput` of Area 6 verbatim.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroDensity

open Work.LinnikContract

/-! ## 1. The counting functions -/

/-- The **per-character zero count** `N(σ,T,χ)`: the multiplicity-weighted number of zeros `ρ` of
the completed `L`-function of the primitive character inducing `χ` with `σ ≤ Re ρ ≤ 1` and
`|Im ρ| ≤ T`.  Verbatim `Work.LinnikAreas.zeroCountIn`, whose conventions this chapter adopts. -/
def zCount {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T : ℝ) : ℝ :=
  Work.LinnikAreas.zeroCountIn χ σ T

/-- The **family zero count** `Σ_{χ mod q} N(σ,T,χ)` (the principal character included). -/
def famCount (q : ℕ) [NeZero q] (σ T : ℝ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q, zCount χ σ T

/-- The **multiplicity-weighted `λ`-count of Heath-Brown §11**: the total multiplicity of the zeros
`ρ` of the characters `χ mod q` (the principal character included) with `λ(ρ) = (1-Re ρ) log q ≤ λ`
and `|Im ρ| ≤ 1`. -/
def multCount (q : ℕ) [NeZero q] (lam : ℝ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q,
    ∑ᶠ ρ : ℂ, if zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 1 ∧ lamOf q ρ ≤ lam
      then (zeroMult χ ρ : ℝ) else 0

/-- The same `λ`-count with the height cut-off `|Im ρ| · log q ≤ T`. -/
def multCountHeight (q : ℕ) [NeZero q] (lam T : ℝ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q,
    ∑ᶠ ρ : ℂ, if zeroMult χ ρ ≠ 0 ∧ |ρ.im| * Real.log q ≤ T ∧ lamOf q ρ ≤ lam
      then (zeroMult χ ρ : ℝ) else 0

/-- The `λ`-count with one pair `(χ₁,β₁)` removed: verbatim `Work.LinnikAreas.Siegel.pairCount`,
the left-hand side of `PairDensityInput` (Area 6). -/
def restCount {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ) (lam : ℝ) : ℝ :=
  Work.LinnikAreas.Siegel.pairCount χ₁ β₁ lam

/-- The height version: verbatim `Work.LinnikAreas.Siegel.pairCountHeight`, the left-hand side of
`PairDensityHeightInput` (Area 6). -/
def restCountHeight {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ) (lam T : ℝ) : ℝ :=
  Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ lam T

/-! ## 2. The zero-density statements

All the density estimates below carry an explicit **two-sided range** `σlo ≤ σ ≤ σhi` of the
variable `σ` and are uniform in the modulus `q`: the constants never depend on `q`, `σ`, `T` or on
the characters.  Two-sided ranges are what makes the predicates *comparable* (a larger range is a
stronger statement), and they are exactly the ranges the consumers use
(`4/5 ≤ σ ≤ 1` for Jutila, `0 ≤ σ ≤ 4/5` for Montgomery). -/

/-- **Log-free family zero-density estimate**, exponent `c(1-σ)+ε`, on the range
`σlo ≤ σ ≤ σhi`: for every `ε > 0` there is `C > 0` with
`Σ_{χ mod q} N(σ,T,χ) ≤ C (qT)^{c(1-σ)+ε}` for all `q ≥ 2`, all `σ ∈ [σlo,σhi]` and all `T ≥ 1`.
This is the shape in which the *proof* of a density estimate naturally lands (the exponent of the
right-hand side is additive in `ε`); the consumer-facing shape is `FamDensityEpsRange`. -/
def FamDensityRange (σlo σhi c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), σlo ≤ σ → σ ≤ σhi → 1 ≤ T →
      famCount q σ T ≤ C * ((q : ℝ) * T) ^ (c * (1 - σ) + ε)

/-- **Log-free family zero-density estimate**, exponent `(c+ε)(1-σ)`, on `σlo ≤ σ ≤ σhi`.
`FamDensityEpsRange (4/5) 1 2` is exactly Jutila's log-free bound in the family form
(`Work.LinnikAreas.FamilyZeroDensityJutila`). -/
def FamDensityEpsRange (σlo σhi c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), σlo ≤ σ → σ ≤ σhi → 1 ≤ T →
      famCount q σ T ≤ C * ((q : ℝ) * T) ^ ((c + ε) * (1 - σ))

/-- **Family zero-density estimate with a logarithmic power**, on `σlo ≤ σ ≤ σhi`:
`Σ_{χ} N(σ,T,χ) ≤ C (qT)^{(c+ε)(1-σ)} (log qT)^B`.
`FamDensityPowerRange 0 (4/5) (12/5) B` is exactly `Work.LinnikAreas.FamilyZeroDensityMontgomery`
for the fixed `B`. -/
def FamDensityPowerRange (σlo σhi c B : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), σlo ≤ σ → σ ≤ σhi → 1 ≤ T →
      famCount q σ T ≤ C * ((q : ℝ) * T) ^ ((c + ε) * (1 - σ)) * (Real.log ((q : ℝ) * T)) ^ B

/-- The `∀ B > 0` form of `FamDensityPowerRange` — the shape of the classical statements
(Montgomery, Huxley), whose constants may depend on the logarithmic power `B`. -/
def FamDensityPowerForm (σlo σhi c : ℝ) : Prop :=
  ∀ B : ℝ, 0 < B → FamDensityPowerRange σlo σhi c B

/-- **Montgomery's density theorem in its sharp form**, exponent `3(1-σ)/(2-σ)+ε` and a
logarithmic power, on `σ ≥ 1/2`.  This is the estimate the multiplicative large sieve supplies
(Iwaniec–Kowalski, Theorem 10.4). -/
def MontgomerySharp (B : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (1 : ℝ)/2 ≤ σ → σ ≤ 1 → 1 ≤ T →
      famCount q σ T ≤ C * ((q : ℝ) * T) ^ (3 * (1 - σ) / (2 - σ) + ε)
        * (Real.log ((q : ℝ) * T)) ^ B

/-- **The log-free estimate near `σ = 1`** (Heath-Brown §11's zero detector with `k` fixed, i.e.
with `φ = 1/2` by convexity; `c = 4φ + ε = 2 + ε < 4`), restricted to the near-line range
`(1-σ)𝓛 ≤ A log 𝓛` where `𝓛 = log q`.  This is the `(D-far-1)` of `ROUTE_LEAD.md` §3.1, AREA 2;
it needs no Burgess input. -/
def NearLineLogFree (c A : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (σ T : ℝ),
    0 ≤ σ → σ ≤ 1 → 1 ≤ T → (1 - σ) * Real.log q ≤ A * Real.log (Real.log q) →
      famCount q σ T ≤ C * ((q : ℝ) * T) ^ (c * (1 - σ) + ε)

/-- **The log-free Deuring–Heilbronn zero count with the `λ₁` factor**, in the working region
`|Im ρ| ≤ 1`: `#{zeros ≠ (χ₁,β₁)} ≤ C λ₁ e^{cλ}` with `c < 49/10`, where `λ₁ = λ(β₁)` is the
exceptional real zero of the real character `χ₁`.  This is the `T = 1` instance of
`Σ_χ N*(σ,T,χ) ≤ C λ₁ (qT)^{c(1-σ)}` (Bombieri, *Le grand crible*, Thm. 14; Jutila 1977;
Heath-Brown (1992) §1 Principle 3 refined by the repulsion).  It covers the principal character. -/
def DHLogFree (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 → lamOf q (β₁ : ℂ) ≤ 1 / 2 →
    ∀ t : ℝ, 0 < t → t ≤ Real.log q →
      restCount χ₁ (β₁ : ℂ) t ≤ C * lamOf q (β₁ : ℂ) * Real.exp (c * t)

/-- `DHLogFree` with the exponent restriction `c < 49/10 = L - 2K` that the assembly needs. -/
def DHLogFreeSpec : Prop := ∃ c : ℝ, c < 49 / 10 ∧ DHLogFree c

/-- **The height version of the `λ₁`-saving Deuring–Heilbronn count**: `≤ C λ₁ e^{cλ} T^{c'}` with
`c < 49/10` and `c' < 2`, the left-hand side being the pairs with `λ(ρ) ≤ t`,
`|Im ρ|·𝓛 ≤ T`.  This is `PairDensityHeightInput` of Area 6. -/
def DHLogFreeHeight (c c' : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 → lamOf q (β₁ : ℂ) ≤ 1 / 2 →
    ∀ t T : ℝ, 0 < t → t ≤ Real.log q → 1 ≤ T →
      restCountHeight χ₁ (β₁ : ℂ) t T ≤ C * lamOf q (β₁ : ℂ) * Real.exp (c * t) * T ^ c'

/-- `DHLogFreeHeight` with the exponent restrictions. -/
def DHLogFreeHeightSpec : Prop := ∃ c c' : ℝ, c < 49 / 10 ∧ c' < 2 ∧ DHLogFreeHeight c c'

/-- **A log-free family zero count at height `1`, in `λ`-units.**  There is `C > 0` and a threshold
`q₀` such that for all `q ≥ q₀` and all `0 ≤ σ ≤ 1`,
`Σ_{χ mod q} N(σ,1,χ) ≤ C·e^{c₃(1-σ)𝓛}`, `𝓛 = log q`.

This is the `T = 1` instance of a log-free family zero-density estimate written in the exponential
form that the Deuring–Heilbronn argument needs: `e^{c₃(1-σ)𝓛} = q^{c₃(1-σ)}`, so it is exactly
`Σ_χ N(σ,1,χ) ≪ q^{c₃(1-σ)}`.  It follows from `FamDensityEpsRange 0 1 c` for every `c₃ > c`
(see `Work.ZeroDensity.logFreeFamHalf_of_density`). -/
def LogFreeFamHalf (c₃ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (σ : ℝ),
    0 ≤ σ → σ ≤ 1 → famCount q σ 1 ≤ C * Real.exp (c₃ * ((1 - σ) * Real.log q))

/-- **A log-free family zero count at height `T`, in `λ`-units.**  There are `C > 0` and `q₀` with
`Σ_{χ mod q} N(σ,T,χ) ≤ C·e^{c₃(1-σ)𝓛}·T^{c₃'}` for all `q ≥ q₀`, `0 ≤ σ ≤ 1`, `T ≥ 1`. -/
def LogFreeFamHeight (c₃ c₃' : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (σ T : ℝ),
    0 ≤ σ → σ ≤ 1 → 1 ≤ T → famCount q σ T ≤ C * Real.exp (c₃ * ((1 - σ) * Real.log q)) * T ^ c₃'

/-! ## 3. The Deuring–Heilbronn repulsion with an explicit constant -/

/-- **The Deuring–Heilbronn repulsion, with the constant pinned down.**  There is a threshold `q₀`
such that for every real character `χ₁` mod `q ≥ q₀` with an exceptional real zero `β₁`
(`λ(β₁) ≤ 1/2`), every further zero `ρ` of *any* character mod `q` with `|Im ρ| ≤ 1` satisfies
`c_r · log(1/λ(β₁)) ≤ λ(ρ)`.

This is the pair form used by Area 6 (`Work.LinnikAreas.Siegel.RepulsionInput`), except that the
constant `c_r` is a *parameter* rather than an unspecified existential: the Deuring–Heilbronn
density bound needs `c_r` bounded below (the two-exponential matching of
`Work.LinnikAreas.ownCount_le_of_threshold_and_logfree` produces the exponent `c₃ + 1/c_r`, so
`c < 49/10` requires `c_r > 5/12` when `c₃ < 12/5`). -/
def RepulsionWith (c_r : ℝ) : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 → lamOf q (β₁ : ℂ) ≤ 1 / 2 →
    ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) → c_r * Real.log (1 / lamOf q (β₁ : ℂ)) ≤ lamOf q ρ

/-- `RepulsionWith c` gives the pair form of Area 6, `Work.LinnikAreas.Siegel.RepulsionInput`. -/
theorem RepulsionWith.toRepulsionInput {c : ℝ} (hc : 0 < c) (hrep : RepulsionWith c) :
    Work.LinnikAreas.Siegel.RepulsionInput := by
  obtain ⟨q₀, hh⟩ := hrep
  exact ⟨c, hc, q₀, fun q hq _ χ₁ β₁ h1 h2 h3 h4 h5 χ ρ h6 h7 h8 =>
    hh q hq χ₁ β₁ h1 h2 h3 h4 h5 χ ρ h6 h7 h8⟩

end Work.ZeroDensity
