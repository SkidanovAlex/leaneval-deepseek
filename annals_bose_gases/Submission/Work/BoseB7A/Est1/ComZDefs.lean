import Mathlib.Tactic.Abel
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.BigOperators.Ring.Finset
import Submission.Work.BoseB7A.Est1.estT2sum_split
import Submission.Work.BoseB7A.NWindow_bp_N_le
import Submission.Work.BoseB7A.NWindow_ta_sum
import Submission.Work.BoseB7A.q3Denom_le_four
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.Est1.ComZDefs` — the objects of the `χ̂²` half

Piece **B** of FS `eq:EstimateQ3Tilde1` (`Est1.estT2sum`) splits as
`‖Y_kΦ‖² = Z²(T2ComF + T2OpF)` (`Est1.estT2sum_split`).  This module develops the
`χ̂²` half (`Est1.estT2sum_comZ`): the split of `T2ComF` into its `χ̂²` main
term and the two errors, and the auxiliary scalars the estimate runs on.

With `Z = z/ℓ³`, `gA E s k = f_L(s)Ŵ₁(k)q3Denom(s,k)`,
`κ_{ss'} = kCom F E s s' k = (1-α_{s-k}α_{s'-k})(χ̂²(s-s') - χ̂(s-k)χ̂(s'-k))`
(`Est1.kCom_eq`), we have

  `T2ComF F T E k Φ = Ŵ₁(k)²·(rawA k Φ - rawY k Φ)`,

where `rawA` carries the `χ̂²` kernel and `rawY` the `χ̂(s-k)χ̂(s'-k)` kernel, both
with the `k`-dependent weight `wc k s s' = q3Denom s k·q3Denom s' k·(1-α_{s-k}α_{s'-k})`.

## Contents

* `wgt` — the `k`-weight `Z²(c_k)⁻¹Ŵ₁(k)²` of the `χ̂²` half.
* `wc`, `rawA`, `rawY` — the split of `T2ComF`.
* `FA`, `AbsA0` — the `Ã`-form and its absolute value (the objects compared with
  `⟨G Φ⟩`).
* `NPL`, `TA`, `TB` — the low-momentum mode count and the two θ-mode moments.
* `wsum` — `Λ = Σ_{k∈P_H}wgt k`, whose value `2ρ_zΞ/(1-𝓁²)` is `wsum_eq`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

namespace Est1

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- The `k`-weight of the `χ̂²` half: `Z²(c_k)⁻¹Ŵ₁(k)²`, `Z = z/ℓ³`,
`c_k = cD E k = (1-𝓁²)𝒟_k`. -/
def wgt (E : Q3Env Mode) (k : Mode) : ℝ :=
  (E.z / E.ell ^ 3) ^ 2 * (cD E k)⁻¹ * E.W1 k ^ 2

/-- The `(s,s')` coefficient of the `χ̂²` half, before the kernels:
`q3Denom s k·q3Denom s' k·(1-α_{s-k}α_{s'-k})`. -/
def wc (E : Q3Env Mode) (k s s' : Mode) : ℝ :=
  E.q3Denom s k * E.q3Denom s' k * (1 - E.alpha (s - k) * E.alpha (s' - k))

/-- The `χ̂²` double sum (without the weight `Ŵ₁(k)²` and the `k`-weight `wgt`). -/
def rawA (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (k : Mode) (Φ : F.H) : ℝ :=
  ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
    (E.fL s * E.fL s' * wc E k s s') * E.hatChiSq (s' - s) *
      F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)

/-- The `χ̂(s-k)χ̂(s'-k)` double sum of `T2ComF`. -/
def rawY (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (k : Mode) (Φ : F.H) : ℝ :=
  ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
    (E.fL s * E.fL s' * wc E k s s') * (E.hatChi (s - k) * E.hatChi (s' - k)) *
      F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)

/-- `F_A(k) = Σ_{s,s'}f_L(s)f_L(s')χ̂²(s-s')⟨Ã_sΦ,Ã_{s'}Φ⟩`: the `Ã`-form of the
`χ̂²` main term (the object to be compared with `⟨G Φ⟩`). -/
def FA (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (k : Mode) (Φ : F.H) : ℝ :=
  ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
    E.fL s * E.fL s' * E.hatChiSq (s' - s) *
      F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)

/-- `Σ_{s,s'}f_L(s)f_L(s')|⟨Ã_sΦ,Ã_{s'}Φ⟩|`, the absolute-value companion of `FA`. -/
def AbsA0 (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (k : Mode) (Φ : F.H) : ℝ :=
  ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
    E.fL s * E.fL s' * |F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)|

/-- The bound `β_m = 2¹²K₀²𝓁²` on `|bA E s k| = |α_kα_{s-k}|` on the modes
`s ∈ supp f_L`, `k ∈ P_H`. -/
def bm (K₀ : ℝ) (E : Q3Env Mode) : ℝ := (2 : ℝ) ^ 12 * K₀ ^ 2 * E.lille ^ 2

/-- The bound `C_dev = 2²⁰K₀²𝓁²` on `|wc E k s s' - 1|`. -/
def devc (K₀ : ℝ) (E : Q3Env Mode) : ℝ := (2 : ℝ) ^ 20 * K₀ ^ 2 * E.lille ^ 2

/-- The error multiplier of the `χ̂²` half: the `wc`-deviation plus the
`χ̂(s-k)χ̂(s'-k)` term `(1+C_dev)K₀²η²`. -/
def erm (K₀ : ℝ) (E : Q3Env Mode) : ℝ :=
  devc K₀ E + (1 + devc K₀ E) * (K₀ ^ 2 * eta E ^ 2)

/-- The bound `Λ ≤ LamBound` of `wsum_le`. -/
def LamBound (K₀ : ℝ) (E : Q3Env Mode) : ℝ :=
  2 * E.rho * (E.W1omega0 + K₀ * E.aScat * E.KH⁻¹) * (1 + 2 * E.lille ^ 2)

/-- The excess `Λ - 2ρ_zŴ₁ω(0) ≤ dlt` used to pay the `Gop`-coefficient deficit. -/
def dlt (K₀ : ℝ) (E : Q3Env Mode) : ℝ :=
  8 * E.rho * K₀ * E.aScat * (E.lille ^ 2 + E.KH⁻¹)

/-- The constant of the `Ã`-vs-`ã` comparison `FA ≤ Q + C_b(⟨n₊⟩ + NPL‖Φ‖²)`. -/
def cbeta (K₀ : ℝ) (E : Q3Env Mode) : ℝ :=
  (K₀ + 1) * (4 * bm K₀ E + 4 * bm K₀ E ^ 2)

/-- `NPL = #{s ∈ P_L}`, the number of modes in the support of `f_L`. -/
def NPL (E : Q3Env Mode) : ℝ :=
  (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ)

/-- `TA = Σ_s f_L(s)‖ã_sΦ‖² ≤ ⟨Φ,n₊Φ⟩`. -/
def TA (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (Φ : F.H) : ℝ :=
  ∑ s ∈ excited Mode, E.fL s * F.bp (T.ta s Φ) (T.ta s Φ)

/-- `TB = Σ_s f_L(s)‖ã_{-s}†Φ‖² = TA + NPL·‖Φ‖²`. -/
def TB (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (Φ : F.H) : ℝ :=
  ∑ s ∈ excited Mode, E.fL s * F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ)

/-- `Λ = Σ_{k∈P_H}wgt k`, whose value is `2ρ_zΞ/(1-𝓁²)`. -/
def wsum (F : FockData Mode) (E : Q3Env Mode) : ℝ := ∑ k ∈ F.PHset E, wgt E k

/-! ## The split of `T2ComF` -/

/-- `χ̂²(s - s') = χ̂²(s' - s)` (`hatChiSq_even` and `-(s-s') = s'-s`). -/
theorem hatChiSq_swap {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3Kernel K₀ F T E) (s s' : Mode) :
    E.hatChiSq (s - s') = E.hatChiSq (s' - s) := by
  rw [← hK.hatChiSq_even (s - s'), show -(s - s') = s' - s by abel]

/-- **The split of the `χ̂²` half**: with `Z = z/ℓ³`,
`T2ComF F T E k Φ = Ŵ₁(k)²·(rawA k Φ - rawY k Φ)`.

Immediate from `Est1.kCom_eq` (`κ = (1-αα')(χ̂² - χ̂χ̂)`) and the definition of
`gA = f_LŴ₁q3Denom`. -/
theorem t2com_split {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3Kernel K₀ F T E) (k : Mode) (Φ : F.H) :
    T2ComF F T E k Φ = E.W1 k ^ 2 * (rawA F T E k Φ - rawY F T E k Φ) := by
  have h1 : rawA F T E k Φ - rawY F T E k Φ
      = ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          ((E.fL s * E.fL s' * wc E k s s') * E.hatChiSq (s' - s) *
              F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)
            - (E.fL s * E.fL s' * wc E k s s') *
              (E.hatChi (s - k) * E.hatChi (s' - k)) *
              F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)) := by
    rw [rawA, rawY, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_sub_distrib]
  rw [h1, T2ComF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [kCom_eq hK, hatChiSq_swap hK s s']
  unfold gA wc
  ring

end Est1

end Work.BoseB7A
