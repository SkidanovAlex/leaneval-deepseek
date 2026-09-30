import Mathlib
import ChallengeDeps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

/-! Shared definitions for the Baker–Wüstholz route (BW = Baker–Wüstholz, Crelle 442 (1993)).
Throughout, `K` is a number field, `φ : K →+* ℂ`, `d = Module.finrank ℚ K`, and heights are
**relative** to `K`: `Height.logHeight₁ x` is BW's `h(x)` (= `d ·` absolute height), and
`Height.logHeight x` for a vector is BW's projective `h(x)`. Section numbers are BW's. -/

/-- The linear form `Λ = ∑ bᵢ log φ(αᵢ)` with principal logarithms (as in the challenge). -/
noncomputable def lam {K : Type*} [Field K] {n : ℕ} (φ : K →+* ℂ) (α : Fin n → K)
    (b : Fin n → ℤ) : ℂ :=
  ∑ i, (b i : ℂ) * Complex.log (φ (α i))

/-- The challenge conclusion for one family `α` (all coefficient vectors `b`, all `B`). -/
def BWHolds {K : Type*} [Field K] [NumberField K] {n : ℕ} (φ : K →+* ℂ) (α : Fin n → K) :
    Prop :=
  ∀ (b : Fin n → ℤ) (B : ℕ), 2 ≤ B → (∀ i, (b i).natAbs ≤ B) → lam φ α b ≠ 0 →
    Real.log ‖lam φ α b‖ ≥
      -(BakerWustholz.C n (Module.finrank ℚ K)
          * max (Real.log B) (1 / (Module.finrank ℚ K : ℝ))
          * ∏ i, BakerWustholz.modifiedHeight φ (α i))

/-- Modified height of `β` for an arbitrary determination `ℓ` of its logarithm (BW §1):
`max(h(β), |ℓ|, 1) / d` with `h` relative. `modifiedHeight φ β = hmod d β (log φ β)`. -/
noncomputable def hmod {K : Type*} [Field K] [NumberField K] (β : K) (ℓ : ℂ) : ℝ :=
  max (Height.logHeight₁ β / (Module.finrank ℚ K : ℝ))
    (max (‖ℓ‖ / (Module.finrank ℚ K : ℝ)) (1 / (Module.finrank ℚ K : ℝ)))

/-- BW's `h'(L)` for a (primitive) integer vector: `max(log max|bᵢ|, 1/d)`. -/
noncomputable def hL {n : ℕ} (b : Fin n → ℤ) (d : ℕ) : ℝ :=
  max (Real.log ((Finset.univ.sup fun i => (b i).natAbs : ℕ) : ℝ)) (1 / (d : ℝ))

/-- The §5 threshold `log C(n,d) - n log d - log(n+d)`. -/
noncomputable def Xbw (n d : ℕ) : ℝ :=
  Real.log (BakerWustholz.C n d) - n * Real.log d - Real.log (n + d)

/-- Kummer condition (BW §9, `p = 2`): no nontrivial product `∏ ηᵢ^{εᵢ}`, `εᵢ ∈ {0,1}`, is a
square in `K`. (Equivalent to `[K(√η₁,…,√η_r):K] = 2^r`.) -/
def KummerCond {K : Type*} [Field K] {r : ℕ} (η : Fin r → K) : Prop :=
  ∀ e : Fin r → Fin 2, e ≠ 0 → ¬ IsSquare (∏ i, η i ^ (e i : ℕ))

/-- `κ(r) = (64nd)^{n-r} (n!/2^{n-1}) min(c/2^v, 1)` (BW (7)). -/
noncomputable def kappa (n d r v : ℕ) (c : ℝ) : ℝ :=
  (64 * n * d : ℝ) ^ (n - r) * ((n.factorial : ℝ) / 2 ^ (n - 1)) * min (c / 2 ^ v) 1

/-- `κ'(r) = (9/4)(n+1) r^{r+1} (64d)^{r+2} log(2rd) max(2^v/c, 1)` (BW §11). -/
noncomputable def kappa' (n d r v : ℕ) (c : ℝ) : ℝ :=
  (9 / 4 : ℝ) * (n + 1) * (r : ℝ) ^ (r + 1) * (64 * d : ℝ) ^ (r + 2) *
    Real.log (2 * r * d) * max (2 ^ v / c) 1

/-- The determination `log α'_j := 2^{-v} L_j(log α₁,…,log αₙ)` (principal `log αᵢ`). -/
noncomputable def lamP {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (α : Fin n → K) (v : ℕ)
    (L : Fin r → Fin n → ℤ) (j : Fin r) : ℂ :=
  ((2 : ℂ) ^ v)⁻¹ * ∑ i, (L j i : ℂ) * Complex.log (φ (α i))

/-- BW §11 "basic hypothesis" at rank `r`, with explicit witnesses `L, α', σ`. -/
def BH {K : Type*} [Field K] [NumberField K] {n : ℕ} (φ : K →+* ℂ) (α : Fin n → K)
    (b : Fin n → ℤ) (v : ℕ) (c : ℝ) (r : ℕ) (L : Fin r → Fin n → ℤ) (α' : Fin r → K)
    (σ : Fin r → ℝ) : Prop :=
  LinearIndependent ℚ (fun j i => (L j i : ℚ)) ∧
  (fun i => (b i : ℚ)) ∈ Submodule.span ℚ (Set.range fun j i => (L j i : ℚ)) ∧
  (∀ j, α' j ≠ 0 ∧ Complex.exp (lamP φ α v L j) = φ (α' j)) ∧
  KummerCond α' ∧ (∀ j, 0 < σ j) ∧
  (∀ j, hmod (α' j) (lamP φ α v L j) ≤ σ j) ∧
  (∀ j, ∑ i, |(L j i : ℝ)| * BakerWustholz.modifiedHeight φ (α i) ≤ 2 ^ v * σ j) ∧
  ∏ j, σ j ≤ kappa n (Module.finrank ℚ K) r v c * ∏ i, BakerWustholz.modifiedHeight φ (α i)

/-- Standing assumptions of BW §11 (after the reductions of §5, §6): `k` plays BW's index `n`. -/
def Standing {K : Type*} [Field K] [NumberField K] {n : ℕ} (φ : K →+* ℂ) (α : Fin n → K)
    (b : Fin n → ℤ) (k : Fin n) (c : ℝ) : Prop :=
  2 ≤ n ∧ (∀ i, α i ≠ 0) ∧ LinearIndependent ℚ (fun i => Complex.log (φ (α i))) ∧
  Finset.univ.gcd b = 1 ∧ b k ≠ 0 ∧
  (∀ j, BakerWustholz.modifiedHeight φ (α j) ≤ BakerWustholz.modifiedHeight φ (α k)) ∧
  Xbw n (Module.finrank ℚ K) ≤ hL b (Module.finrank ℚ K) ∧ Real.exp 1 ≤ c ∧
  Real.log c < n * hL b (Module.finrank ℚ K)

/-- Coefficient vector (in `i : Fin r`) of BW's operator `∂*_j`, `j ≠ k`:
`b_k ∂L_i/∂z_j - b_j ∂L_i/∂z_k`. Also gives `γ_j(λ) = ∑ᵢ derVec b k L j i · λᵢ`. -/
def derVec {n r : ℕ} (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ) (j : Fin n)
    (i : Fin r) : ℤ :=
  b k * L i j - b j * L i k

/-- `ι` selects `r-1` of the operators `∂*_j` (`j ≠ k`) that are linearly independent (BW §10). -/
def IotaOK {n r : ℕ} (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ)
    (ι : Fin (r - 1) → Fin n) : Prop :=
  (∀ m, ι m ≠ k) ∧ LinearIndependent ℚ (fun m i => (derVec b k L (ι m) i : ℚ))

/-! ### BW §13 parameters (functions of `r, d, σ, h'(L), v`). -/

/-- `D = 2 r^r (32d)^{r+1} log(2rd) σ₁⋯σ_r`. -/
noncomputable def pD (r d : ℕ) (σ : Fin r → ℝ) : ℝ :=
  2 * (r : ℝ) ^ r * (32 * d : ℝ) ^ (r + 1) * Real.log (2 * r * d) * ∏ j, σ j

/-- `D₀ = [rD / (2 log(2rd))]`. -/
noncomputable def pD0 (r d : ℕ) (σ : Fin r → ℝ) : ℕ :=
  ⌊(r : ℝ) * pD r d σ / (2 * Real.log (2 * r * d))⌋₊

/-- `D_j = [D / (r d σ_j)]`. -/
noncomputable def pDj (r d : ℕ) (σ : Fin r → ℝ) (j : Fin r) : ℕ :=
  ⌊pD r d σ / ((r : ℝ) * d * σ j)⌋₊

/-- `h = [h'(L) + v log 2]`; `D_{-1} = h - 1`. -/
noncomputable def ph (H : ℝ) (v : ℕ) : ℕ :=
  ⌊H + v * Real.log 2⌋₊

/-- `S = 16 r d h`. -/
def pS (r d h : ℕ) : ℕ := 16 * r * d * h

/-- `T = [11.75 r D]`. -/
noncomputable def pT (r d : ℕ) (σ : Fin r → ℝ) : ℕ :=
  ⌊(11.75 : ℝ) * r * pD r d σ⌋₊

/-- `I = [50 log(2rd)]` (number of Kummer-descent steps, BW §20). -/
noncomputable def pI (r d : ℕ) : ℕ := ⌊50 * Real.log (2 * r * d)⌋₊

/-- `ξ = 1 - 0.536/r` (BW §19). -/
noncomputable def pxi (r : ℕ) : ℝ := 1 - 0.536 / r

/-! ### BW §12 delta functions and the §13 auxiliary values. -/

/-- `Δ(z;k) = (z+1)⋯(z+k)/k!` as a rational polynomial. -/
noncomputable def deltaPoly (k : ℕ) : Polynomial ℚ :=
  ((k.factorial : ℚ)⁻¹) • ∏ i ∈ Finset.range k, (Polynomial.X + Polynomial.C ((i : ℚ) + 1))

/-- `Δ(z;k)`. -/
noncomputable def Delta (z : ℂ) (k : ℕ) : ℂ := Polynomial.aeval z (deltaPoly k)

/-- `Θ(z;k,l,m) = (1/m!) (d/dz)^m Δ(z;k)^l`. -/
noncomputable def Theta (z : ℂ) (k l m : ℕ) : ℂ :=
  Polynomial.aeval z (Polynomial.hasseDeriv m (deltaPoly k ^ l))

/-- `u(k) = lcm(1,…,k)`. -/
def ulcm (k : ℕ) : ℕ := (Finset.range k).lcm (· + 1)

/-- Index set of the auxiliary polynomial: `λ₋₁ < h`, `λ₀ ≤ D₀`, `λ_j ≤ D_j`. -/
abbrev AuxIdx (r h D0 : ℕ) (Dj : Fin r → ℕ) : Type :=
  Fin h × Fin (D0 + 1) × ((j : Fin r) → Fin (Dj j + 1))

/-- `γ_j(λ) = ∑ᵢ (b_k ∂L_i/∂z_j − b_j ∂L_i/∂z_k) λᵢ` (BW §13), as a complex number. -/
noncomputable def gam {n r : ℕ} (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ)
    (j : Fin n) (lm : Fin r → ℕ) : ℂ :=
  ∑ i, ((derVec b k L j i : ℤ) : ℂ) * (lm i : ℂ)

/-- `Q(s, α'^s; t)` (BW §13): value at the integer `s` of the polynomial `Q(Y₀,…,Y_r; t)`
with `t = (t₀, t₁,…,t_{r-1})` split as `t0` and `t : Fin (r-1) → ℕ`. -/
noncomputable def Qval {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (b : Fin n → ℤ)
    (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (α' : Fin r → K)
    (h D0 : ℕ) (Dj : Fin r → ℕ) (p : AuxIdx r h D0 Dj → K) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (s : ℤ) : ℂ :=
  ∑ lm : AuxIdx r h D0 Dj,
    φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)) *
      (ulcm h : ℂ) ^ t0 * Theta ((s : ℂ) + (lm.1 : ℕ)) h ((lm.2.1 : ℕ) + 1) t0 *
      ∏ j, φ (α' j) ^ (s * ((lm.2.2 j : ℕ) : ℤ))

/-! ### Derivations on `ℂ[Y₀,…,Y_r]` (variable `0` is `Y₀`, variable `i.succ` is `Y_{i+1}`). -/

/-- The invariant derivation `∑ᵢ cᵢ Yᵢ ∂/∂Yᵢ` on the torus coordinates. -/
noncomputable def eulerDer {r : ℕ} (c : Fin r → ℚ) (P : MvPolynomial (Fin (r + 1)) ℂ) :
    MvPolynomial (Fin (r + 1)) ℂ :=
  ∑ i : Fin r, MvPolynomial.C (c i : ℂ) * MvPolynomial.X i.succ *
    MvPolynomial.pderiv i.succ P

/-- `∂₀^{t0} ∏_m D_m^{t m}` applied to `P`, where `D_m = eulerDer (c m)`. -/
noncomputable def applyDer {r q : ℕ} (c : Fin q → Fin r → ℚ) (t0 : ℕ) (t : Fin q → ℕ)
    (P : MvPolynomial (Fin (r + 1)) ℂ) : MvPolynomial (Fin (r + 1)) ℂ :=
  (MvPolynomial.pderiv (0 : Fin (r + 1)))^[t0]
    ((List.finRange q).foldr (fun m Q => (eulerDer (c m))^[t m] Q) P)

/-- The point `(s, e^{s ℓ₁}, …, e^{s ℓ_r})` of `G_a × G_m^r`. -/
noncomputable def ptS {r : ℕ} (ℓ : Fin r → ℂ) (s : ℕ) : Fin (r + 1) → ℂ :=
  Fin.cons (s : ℂ) (fun i => Complex.exp ((s : ℂ) * ℓ i))

/-- A primitive system of integer linear forms: `ℚ`-independent rows whose `ℤ`-span is
saturated in `ℤ^r` (equivalently the maximal minors are coprime). -/
def PrimSys {ρ r : ℕ} (M : Fin ρ → Fin r → ℤ) : Prop :=
  LinearIndependent ℚ (fun j i => (M j i : ℚ)) ∧
  ∀ (x : Fin r → ℤ) (m : ℤ), m ≠ 0 → m • x ∈ Submodule.span ℤ (Set.range M) →
    x ∈ Submodule.span ℤ (Set.range M)

/-- Output of the extrapolation + Kummer descent (BW §20–21): `P = Q^{(I)}(·; 0)` is a nonzero
polynomial in `Y₀,…,Y_r` with `deg_{Y₀} ≤ h(D₀+1)`, `deg_{Y_j} ≤ 2^{-I} D_j`, killed by all
`∂₀^{t₀} ∏ ∂*^{t}` with `t₀+∑t ≤ ξ T^{(I)}` at `(s, α'^s)`, `0 ≤ s ≤ 2 S^{(I)}`, where
`S^{(I)} = ξ^{-rI} S`, `T^{(I)} = ξ^{rI} T`. (Each descent step substitutes `Y_j ↦ Y_j²`,
`Y₀ ↦ Y₀/2`, so the points are again `(s, α'^s)` with `log α'_j` as in `lamP`.) -/
def PolyOut {K : Type*} [Field K] [NumberField K] {n r : ℕ} (φ : K →+* ℂ) (α : Fin n → K)
    (b : Fin n → ℤ) (k : Fin n) (v : ℕ) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n)
    (σ : Fin r → ℝ) (P : MvPolynomial (Fin (r + 1)) ℂ) : Prop :=
  P ≠ 0 ∧
  (P.degreeOf 0 : ℝ) ≤
    (ph (hL b (Module.finrank ℚ K)) v : ℝ) * ((pD0 r (Module.finrank ℚ K) σ : ℝ) + 1) ∧
  (∀ i : Fin r, (P.degreeOf i.succ : ℝ) ≤
    (pDj r (Module.finrank ℚ K) σ i : ℝ) / 2 ^ pI r (Module.finrank ℚ K)) ∧
  ∀ s : ℕ, (s : ℝ) ≤ 2 * pxi r ^ (-((r * pI r (Module.finrank ℚ K) : ℕ) : ℤ)) *
      (pS r (Module.finrank ℚ K) (ph (hL b (Module.finrank ℚ K)) v) : ℝ) →
    ∀ (t0 : ℕ) (t : Fin (r - 1) → ℕ),
      ((t0 + ∑ m, t m : ℕ) : ℝ) ≤
        pxi r * pxi r ^ (r * pI r (Module.finrank ℚ K)) * (pT r (Module.finrank ℚ K) σ : ℝ) →
      MvPolynomial.eval
        (ptS (fun i => lamP φ α v L i) s)
        (applyDer (fun m i => (derVec b k L (ι m) i : ℚ)) t0 t P) = 0

end Work.BW
