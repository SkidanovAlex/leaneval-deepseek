import Mathlib
import Submission.Work.OddVolterra.Defs

/-!
# The smooth (manifest) representative of the odd Abel kernel

## Why this file exists

The paper's kernel `K₁(s,σ,t) = J₁(s,σ,t)/Kden(s,σ,t)` is defined in `Work.OddVolterra.Defs`
with a case split: on the diagonal `σ = s` it is set to the limit value
`(2n+1)!! (-L ∂_sL)^{n+1}`, and off the diagonal it is the differentiated numerator.  As the
`Bridge/abel_form_of_curve` investigation established, that function is **discontinuous** at
every diagonal point: for `σ < s` the formula collapses to `0`
(`Work.OddVolterra.Bridge.Kvec_eq_zero_of_lt`), while on `σ = s` it is generically non-zero.
Hence `fun p => Kvec n h p.1 p.2 ...` is *never* `ContDiffOn ℝ 2` on a box `[a,b]²`, and the
commons Abel/Volterra library (`Commons.Analysis.Abel.volterra_equivalence_full`,
`Work.OddVolterra.Abel.abel_form_of_volterra_form`) cannot be applied to it.

The remedy is to replace `Kvec`, *on the triangle `s ≤ σ`* where it is actually used, by a
manifestly smooth representative.  The algebra behind it: with

`Z(s,σ,t) = L(σ,t)^2 - L(s,t)^2 = (σ-s)·(t+H(s,σ))·(L(σ,t)+L(s,t))`

one has `Kden² = Z/(σ-s)`, so for `σ > s`

`K₁(s,σ,t) = ∂_s^{n+1}[Z^{n+1/2}](s)·√(Z(s,σ,t))`,  `K₂(s,σ,t) = ∂_s^{n}[Z^{n-1/2}·∂_sL](s)·√(Z(s,σ,t))`.

Both right-hand sides are, as functions of `σ`, the product of `√Z` with a polynomial in the
`∂_s`-derivatives of `Z`, hence extend smoothly across `σ = s`.  The polynomial is produced by
the classical recursion for `F ↦ (d/ds)^m[Z^ν · init]·Z^{m-ν}`:

`R_0 = init`,   `R_{m+1} = Z·∂_s R_m + (ν-m)·(∂_s Z)·R_m`,

whose output `R_m` is a polynomial in `Z, ∂_sZ, …, ∂_s^m Z` and therefore manifestly smooth in
`(s,σ,t)`.  Taking `(ν, init) = (n+1/2, 1)` and `m = n+1` reproduces `J₁`;
`(ν, init) = (n-1/2, ∂_sL)` and `m = n` reproduces `J₂`.

`KvecM` below is `Kvec` with `J₁, J₂` replaced by `J1M = R_{n+1}` and `J2M = R_n`.  It is
smooth on a box whenever `Kden > 0` there, and it agrees with `Kvec` on the triangle
`σ > s`; on the diagonal it also agrees, which is what makes `G2(s,s)` consistent.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.KernelExt

open Work.OddVolterra

noncomputable section

/-- The radicand `Z(s,σ,t) = L(σ,t)² - L(s,t)²`, as a function of the triple `(s,σ,t)`. -/
def Zrad (h : ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  line h p.2.1 p.2.2 ^ 2 - line h p.1 p.2.2 ^ 2

/-- `∂_s` of `Zrad`, i.e. the value the recursion uses for `∂_s Z`. -/
def ZradS (h : ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  (fderiv ℝ (Zrad h) p) (1, 0, 0)

/-- **The recursive Bell numerator.**  `Rnu ν h init m` is the polynomial
`(d/ds)^m[Z^ν · init] · Z^{m-ν}` evaluated at `(s,σ,t)`; it is defined by the recursion
`R_{m+1} = Z·∂_s R_m + (ν-m)·(∂_s Z)·R_m` and therefore makes sense for every sign of `Z`. -/
noncomputable def Rnu (ν : ℝ) (h : ℝ → ℝ) (init : ℝ × ℝ × ℝ → ℝ) : ℕ → ℝ × ℝ × ℝ → ℝ
  | 0 => init
  | (m + 1) => fun p =>
      Zrad h p * (fderiv ℝ (Rnu ν h init m) p) (1, 0, 0)
      + (ν - (m : ℝ)) * (fderiv ℝ (Zrad h) p) (1, 0, 0) * Rnu ν h init m p

/-- The manifest numerator of the first Abel kernel: `J₁ = R_{n+1}` for `ν = n + 1/2`,
`init = 1`. -/
def J1M (n : ℕ) (h : ℝ → ℝ) (s σ t : ℝ) : ℝ :=
  Rnu ((n : ℝ) + 1 / 2) h (fun _ => (1 : ℝ)) (n + 1) (s, σ, t)

/-- The manifest numerator of the second Abel kernel: `J₂ = R_n` for `ν = n - 1/2`,
`init = ∂_s L(s,t) = t + h'(s)`. -/
def J2M (n : ℕ) (h : ℝ → ℝ) (s σ t : ℝ) : ℝ :=
  Rnu ((n : ℝ) - 1 / 2) h (fun p => lineSlope h p.1 p.2.2) n (s, σ, t)

/-- The manifest first Abel kernel. -/
def K1M (n : ℕ) (h : ℝ → ℝ) (s σ t : ℝ) : ℝ := J1M n h s σ t / Kden h s σ t

/-- The manifest second Abel kernel. -/
def K2M (n : ℕ) (h : ℝ → ℝ) (s σ t : ℝ) : ℝ := J2M n h s σ t / Kden h s σ t

/-- **The smooth representative of the paper's kernel.**  Identical to
`Work.OddVolterra.Kvec`, with `J₁, J₂` replaced by their manifest polynomial forms. -/
def KvecM (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (x y x' y' : ℝ) : Fin 2 → ℝ :=
  ![- (K1M n h s σ (-x) * x' + K1M n h s σ y * y'),
     - (K2M n h s σ (-x) * x' + K2M n h s σ y * y')]

/-- The `τ`-average of `KvecM`, the manifest form of `Work.OddVolterra.G2`. -/
def G2M (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (x y x' y' : ℝ) : Fin 2 → ℝ :=
  fun i : Fin 2 =>
    ∫ τ in (0 : ℝ)..1, (KvecM n h (s + τ * (σ - s)) σ x y x' y') i /
      Real.sqrt (τ * ((1 : ℝ) - τ))

/-- `Godd` with `G2` replaced by `G2M`. -/
def GoddM (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (Z : St) : St :=
  ![Z 0, Z 1,
    - (G2M n h s s (Z 0) (Z 1) (Z 2) (Z 3)) 0,
    - (G2M n h s s (Z 0) (Z 1) (Z 2) (Z 3)) 1]

/-- `Theta` with `G2` replaced by `G2M`. -/
def ThetaM (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (Z : St) : St :=
  ![- Z 2, - Z 3,
    - (deriv (fun u : ℝ => (G2M n h u σ (Z 0) (Z 1) (Z 2) (Z 3)) 0) s),
    - (deriv (fun u : ℝ => (G2M n h u σ (Z 0) (Z 1) (Z 2) (Z 3)) 1) s)]

/-- The system `(hah44)` with the manifest kernel `G2M`/`ThetaM`. -/
def VolterraEqOnM (n : ℕ) (h : ℝ → ℝ) (x y : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ s ∈ S, GoddM n h s (stateOf x y s) =
    (∫ σ in s..(1 : ℝ), ThetaM n h s σ (stateOf x y σ)) + Xi n h s

end

end Work.OddVolterra.KernelExt
