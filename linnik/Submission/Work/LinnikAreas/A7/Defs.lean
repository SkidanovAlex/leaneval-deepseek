/-
# Area 7 — working definitions

Auxiliary notions for the assembly of AREA 7 (`Work.LinnikContract.Assembly`, HB §§14–15).

The constants of the area are `L = 11/2`, `K = 3/10`, `a = L - 2K = 49/10`.
The per-character bound of HB Lemma 13.3 is `B(λ)` = `Work.LinnikContract.Bfun K λ`, the density
weight of HB Lemma 11.1 is `w(λ)` = `Work.LinnikContract.wHB λ`.
-/
import Mathlib
import Submission.Work.LinnikContract.Pre

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.A7

open Work.LinnikContract

/-- `L = 11/2`. -/
def Lc : ℝ := 11/2
/-- `K = 3/10`. -/
def Kc : ℝ := 3/10
/-- `a = L - 2K = 49/10`. -/
def ac : ℝ := 49/10
/-- `K² = 9/100`. -/
def K2 : ℝ := 9/100

/-- The normalised per-character constant `Φ(λ) = e^{-aλ} B(K,λ)`; the contribution of one
character with smallest zero-parameter `λ`, after the per-character bound of HB Lemma 13.3. -/
def Phi (lam : ℝ) : ℝ := Real.exp (-(ac * lam)) * Bfun Kc lam

/-- HB's density weight `w(λ)` (the same function as `Work.LinnikContract.wHB`). -/
def Wf (lam : ℝ) : ℝ := wHB lam

/-- The `C`-function of HB §15: `C(λ) = max(0, Φ(λ) - Φ(Λ) w(λ)/w(Λ))`. -/
def Cf (Lam lam : ℝ) : ℝ := max 0 (Phi lam - Phi Lam * Wf lam / Wf Lam)

/-- The set of characters of level `q` (other than the principal one) having a zero in HB's box
`InBox q R` (i.e. `λ(ρ) ≤ R` and `|γ| log q ≤ R`). -/
def Aset (q : ℕ) [NeZero q] (R : ℝ) : Finset (DirichletCharacter ℂ q) :=
  (Finset.univ.erase (1 : DirichletCharacter ℂ q)).filter
    (fun χ => ∃ ρ : ℂ, InBox q R ρ ∧ zeroMult χ ρ ≠ 0)

/-- The sum over the characters of `Aset` of `boxAbs`, i.e. the total (absolute-value) box sum
normalised by `K²`. -/
def TAbs (q : ℕ) [NeZero q] (K R : ℝ) : ℝ :=
  ∑ χ ∈ Aset q R, boxAbs q K R χ

/-- The `Φ`-sum over the characters of `Aset`, weighted by their least zero-parameter. -/
def PhiSum (q : ℕ) [NeZero q] (R : ℝ) : ℝ :=
  ∑ χ ∈ Aset q R, Phi (lamChar χ)


/-- The refinement term `A = (e^{-aλ} - e^{-aΛ₀})(B(λ) - K⁻²F₂(λ))` of HB §15 (case `χ₁` complex
or `χ₁, ρ₁` real): it is subtracted from `Φ(λ)` when the *second* zero of `χ₁` has parameter at
least `c0`. -/
def Aref (c0 lam : ℝ) : ℝ :=
  (Real.exp (-(ac * lam)) - Real.exp (-(ac * c0))) *
    (Bfun Kc lam - ((1 - Real.exp (-(Kc * lam))) / lam) ^ 2 / K2)

end Work.LinnikAreas.A7
