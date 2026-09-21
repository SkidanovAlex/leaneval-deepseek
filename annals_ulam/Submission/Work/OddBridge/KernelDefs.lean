import Mathlib
import Submission.Work.OddVolterra.Defs

/-!
# A manifest (globally smooth) representative of the odd Abel kernel

The paper's Abel kernel `K₁(s,σ,t) = J₁(s,σ,t)/Kden(s,σ,t)` (`Work.OddVolterra.K1`) is defined
with a case split at `σ = s`: on the diagonal it is the limit value, off it the differentiated
numerator.  That function is **discontinuous** at the diagonal (for `σ < s` the off-diagonal
formula collapses to `0`), so it is never `C²` on a box `[a,b]²` and the Abel/Volterra
equivalence of the commons library cannot be applied to it.

The remedy is to replace `Kvec` on the triangle `s ≤ σ` -- where it is actually used -- by a
manifestly smooth representative.  With

`Z(s,σ,t) = L(σ,t)² - L(s,t)² = (σ-s)·(t + H(s,σ))·(L(σ,t) + L(s,t))`

one has `Kden² = Z/(σ-s)`, so for `σ > s`

`K₁(s,σ,t) = ∂_s^{n+1}[Z^{n+1/2}](s)·√(Z(s,σ,t))`,  `K₂(s,σ,t) = ∂_s^{n}[Z^{n-1/2}·∂_sL](s)·√(Z(s,σ,t))`.

Both right-hand sides are the product of `√Z` with a polynomial in the `∂_s`-derivatives of `Z`,
and hence extend smoothly across `σ = s`.  The polynomial is produced by the classical recursion
for `F ↦ (d/ds)^m[Z^ν · init]·Z^{m-ν}`:

`R₀ = init`,   `R_{m+1} = Z·∂_s R_m + (ν-m)·(∂_s Z)·R_m`,

whose output `R_m` is a polynomial in `Z, ∂_sZ, …, ∂_s^m Z` and therefore manifestly smooth in
`(s,σ,t)`.  Taking `(ν, init) = (n+1/2, 1)` and `m = n+1` reproduces `J₁`; `(ν, init) =
(n-1/2, ∂_sL)` and `m = n` reproduces `J₂`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddBridge

open Work.OddVolterra

noncomputable section

/-- The radicand `Z(s,σ,t) = L(σ,t)² - L(s,t)²` of the paper's difference of squares. -/
def Zrad (h : ℝ → ℝ) (s σ t : ℝ) : ℝ := line h σ t ^ 2 - line h s t ^ 2

/-- `∂_s Z(s,σ,t)`, the value the recursion uses for `∂_s Z`. -/
def Zs (h : ℝ → ℝ) (s σ t : ℝ) : ℝ := deriv (fun u : ℝ => Zrad h u σ t) s

/-- **The recursive Bell numerator.**  `RR ν h init m s σ t` is the polynomial
`(d/ds)^m[Z^ν · init] · Z^{m-ν}` evaluated at `(s,σ,t)`; it is defined by the recursion
`R_{m+1} = Z·∂_s R_m + (ν-m)·(∂_s Z)·R_m` and therefore makes sense for every sign of `Z`. -/
def RR (ν : ℝ) (h : ℝ → ℝ) (init : ℝ → ℝ → ℝ → ℝ) : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0 => init
  | (m + 1) => fun s σ t =>
      Zrad h s σ t * deriv (fun u : ℝ => RR ν h init m u σ t) s
      + (ν - (m : ℝ)) * Zs h s σ t * RR ν h init m s σ t

/-- The manifest numerator of the first Abel kernel: `J₁ = R_{n+1}` for `ν = n + 1/2`,
`init = 1`. -/
def J1M (n : ℕ) (h : ℝ → ℝ) (s σ t : ℝ) : ℝ :=
  RR ((n : ℝ) + 1 / 2) h (fun _ _ _ => (1 : ℝ)) (n + 1) s σ t

/-- The manifest numerator of the second Abel kernel: `J₂ = R_n` for `ν = n - 1/2`,
`init = ∂_s L(s,t) = t + h'(s)`. -/
def J2M (n : ℕ) (h : ℝ → ℝ) (s σ t : ℝ) : ℝ :=
  RR ((n : ℝ) - 1 / 2) h (fun s _ t => lineSlope h s t) n s σ t

/-- The manifest first Abel kernel. -/
def K1M (n : ℕ) (h : ℝ → ℝ) (s σ t : ℝ) : ℝ := J1M n h s σ t / Kden h s σ t

/-- The manifest second Abel kernel. -/
def K2M (n : ℕ) (h : ℝ → ℝ) (s σ t : ℝ) : ℝ := J2M n h s σ t / Kden h s σ t

/-- **The smooth representative of the paper's kernel.**  Identical to `Work.OddVolterra.Kvec`,
with `J₁, J₂` replaced by their manifest polynomial forms. -/
def KvecM (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (x y x' y' : ℝ) : Fin 2 → ℝ :=
  ![- (K1M n h s σ (-x) * x' + K1M n h s σ y * y'),
     - (K2M n h s σ (-x) * x' + K2M n h s σ y * y')]

/-- The `τ`-average of `KvecM`, the manifest form of `Work.OddVolterra.G2`. -/
def G2M (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (x y x' y' : ℝ) : Fin 2 → ℝ :=
  fun i : Fin 2 =>
    ∫ τ in (0 : ℝ)..1, (KvecM n h (s + τ * (σ - s)) σ x y x' y') i /
      Real.sqrt (τ * ((1 : ℝ) - τ))

end

end Work.OddBridge
