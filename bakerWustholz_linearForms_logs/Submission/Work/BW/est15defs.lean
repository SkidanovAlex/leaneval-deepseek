import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.auxpolydefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for `est15` (BW (15) at descent level `J`)

The algebraic identity behind BW (15) at level `J` is that the value `g^{(J)}(s)` of the
descended auxiliary function at an integer `s` is the image under `φ` of an explicit element
`gKJ` of `K`, whose `λ`-th summand is `p λ` times a *rational* coefficient `coefKJ λ`:

`gKJ = ∑_{λ ≡ μ (mod 2^J)} p λ · coefKJ λ`.

This file fixes these objects so that the algebraic identity (`acg φ α b k L ι v σ p J μ t0 t s
= φ (gKJ …)`) and the valuations estimates can be stated and proved separately.

We mirror literally the definition of `Qdesc`: the `Y₀`-substitution `Y₀ ↦ 2^{-J}X₀ + λ₋₁`
produces `Θ(2^{-J}s + λ₋₁; h, λ₀+1, t₀)`, which is a *rational* number, and the `Yⱼ`-exponents
`⌊λⱼ/2^J⌋` produce the monomials `∏ⱼ α'ⱼ^{s⌊λⱼ/2^J⌋}`.
-/

namespace Work.BW

open MvPolynomial

/-- `Θ` evaluated at a *rational* point: `aeval x (hasseDeriv m (deltaPoly k ^ l))`. This is the
rational number whose image in `ℂ` is `Theta (x:ℂ) k l m` and whose image in `K` occurs as the
`Y₀`-factor of `Q^{(J)}`. -/
noncomputable def thetaRatQ (x : ℚ) (k l m : ℕ) : ℚ :=
  Polynomial.aeval x (Polynomial.hasseDeriv m (deltaPoly k ^ l))

/-- `∏_m Δ(γ_m(λ); t_m) ∈ ℚ`, the "Π(t)" factor of BW §12 at the index `λ`. -/
noncomputable def piRat {n r : ℕ} (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ)
    (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ) (t : Fin (r - 1) → ℕ)
    (lm : AuxIdx r h D0 Dj) : ℚ :=
  ∏ m, deltaRat (gamInt b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)

/-- The rational `Y₀`-factor of the descended polynomial at level `J` and index `λ`:
`Θ(2^{-J}s + λ₋₁; h, λ₀+1, t₀)`. -/
noncomputable def thetaJ {r : ℕ} (h D0 : ℕ) (Dj : Fin r → ℕ) (J t0 : ℕ) (s : ℤ)
    (lm : AuxIdx r h D0 Dj) : ℚ :=
  thetaRatQ ((s : ℚ) / (2 : ℚ) ^ J + ((lm.1 : ℕ) : ℚ)) h ((lm.2.1 : ℕ) + 1) t0

/-- The coefficient `coefKJ λ ∈ K` of `p λ` in `gKJ`. -/
noncomputable def coefKJ {K : Type*} [Field K] {n r : ℕ} (b : Fin n → ℤ) (k : Fin n)
    (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (α' : Fin r → K) (h D0 : ℕ)
    (Dj : Fin r → ℕ) (J : ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ) (s : ℤ)
    (lm : AuxIdx r h D0 Dj) : K :=
  ((piRat b k L ι h D0 Dj t lm : ℚ) : K) * ((ulcm h : ℚ) : K) ^ t0 *
    ((thetaJ h D0 Dj J t0 s lm : ℚ) : K) *
    ∏ j : Fin r, (α' j) ^ (s * (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℤ))

/-- The algebraic number `gKJ` whose `φ`-image is `g^{(J)}(s;t)`: the sum of `p λ · coefKJ λ`
over the indices `λ` with `λ_j ≡ μ_j (mod 2^J)`. -/
noncomputable def gKJ {K : Type*} [Field K] {n r : ℕ} (b : Fin n → ℤ) (k : Fin n)
    (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (α' : Fin r → K)
    (h D0 : ℕ) (Dj : Fin r → ℕ) (p : AuxIdx r h D0 Dj → K) (J : ℕ) (μ : Fin r → ℕ)
    (t0 : ℕ) (t : Fin (r - 1) → ℕ) (s : ℤ) : K :=
  ∑ lm : AuxIdx r h D0 Dj,
    if (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j) then p lm * coefKJ b k L ι α' h D0 Dj J t0 t s lm
    else 0

end Work.BW

namespace Work.BW

/-- The constant `Λ` bounding `∑_m |γ_m(λ)| = ∑_m |γ_{ι m}(λ)|` (the argument of the `Π`-factor):
`(r-1)·2e·e^{h}·D`, valid because `e^{h'(L)}2^{v+1} ≤ 2e·e^{h}`. -/
noncomputable def gamBound (K : Type*) [Field K] [NumberField K] {n r : ℕ} (b : Fin n → ℤ) (v : ℕ)
    (σ : Fin r → ℝ) : ℝ :=
  ((r : ℝ) - 1) * (2 * Real.exp 1) * Real.exp (acH K b v : ℝ) * acD K σ

/-- The constant `μ = 57 r d` of BW §13, used to relax the `Θ`-estimate. -/
noncomputable def mu57 (K : Type*) [Field K] [NumberField K] (r : ℕ) : ℝ := 57 * r * dK K

/-- The `Y₀`-factor of `coefKJ` at level `J`, as a real number: `2^{-J}s + λ₋₁`. -/
noncomputable def zJ (J : ℕ) (s : ℤ) {r : ℕ} {h D0 : ℕ} {Dj : Fin r → ℕ}
    (lm : AuxIdx r h D0 Dj) : ℝ := (s : ℝ) / 2 ^ J + ((lm.1 : ℕ) : ℝ)

end Work.BW

namespace Work.BW

/-- The `λ`-th coefficient of `gKJ` without the `α'`-monomials: `Π(λ)·u(h)^{t₀}·Θ(λ)`.
`coefKJ … λ = coefPart … λ * ∏_j (α' j)^{s⌊λ_j/2^J⌋}`. -/
noncomputable def coefPart {K : Type*} [Field K] {n r : ℕ} (b : Fin n → ℤ) (k : Fin n)
    (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (J t0 : ℕ) (t : Fin (r - 1) → ℕ) (s : ℤ) (lm : AuxIdx r h D0 Dj) : K :=
  ((piRat b k L ι h D0 Dj t lm : ℚ) : K) * (((ulcm h : ℚ) : K)) ^ t0 *
    ((thetaJ h D0 Dj J t0 s lm : ℚ) : K)

lemma coefKJ_eq_coefPart_mul {K : Type*} [Field K] {n r : ℕ} (b : Fin n → ℤ) (k : Fin n)
    (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (α' : Fin r → K) (h D0 : ℕ)
    (Dj : Fin r → ℕ) (J t0 : ℕ) (t : Fin (r - 1) → ℕ) (s : ℤ) (lm : AuxIdx r h D0 Dj) :
    coefKJ b k L ι α' h D0 Dj J t0 t s lm =
      coefPart b k L ι h D0 Dj J t0 t s lm *
        ∏ j : Fin r, (α' j) ^ (s * (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℤ)) := by
  rw [coefKJ, coefPart, mul_assoc]

end Work.BW


namespace Work.BW

/-! ### Real-valued bounds used in the assembly of `est15` -/

/-- `T' = ∑_m t_m` as a real number (the total `t`-degree). -/
noncomputable abbrev estTp {r : ℕ} (t : Fin (r - 1) → ℕ) : ℝ := ∑ m, (t m : ℝ)

/-- The `α'`-monomial base at level `J`: `α'_j` if `0 ≤ s`, `α'_j⁻¹` if `s < 0`. The exponent
`s⌊λ_j/2^J⌋` of `coefKJ` is `≥ 0` in the first case and `≤ 0` in the second, so that always
`(α'_j)^{s⌊λ_j/2^J⌋} = (estBeta s (α'_j))^{m_j}` for some natural `m_j ≤ 2^{-J}|s|λ_j`. -/
def estBeta {K : Type*} [Field K] (s : ℤ) (a : K) : K := if 0 ≤ s then a else a⁻¹

/-- The `w`-independent Archimedean bound for `log |coefPart λ|_w`: the `Π`-factor, the
`u(h)^{t₀}` factor, and the `Θ`-factor (using `|2^{-J}s + λ₋₁| ≤ 2^{-J}|s| + h`). -/
noncomputable def estCi (K : Type*) [Field K] [NumberField K] {n r : ℕ} (b : Fin n → ℤ) (v : ℕ)
    (σ : Fin r → ℝ) (J t0 : ℕ) (t : Fin (r - 1) → ℕ) (s : ℤ) : ℝ :=
  estTp t * (1 + Real.log (1 + gamBound K b v σ / estTp t))
    + (t0 : ℝ) * Real.log (ulcm (acH K b v))
    + (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (acH K b v : ℝ) *
        (1 + Real.log (mu57 K r) + 1 / mu57 K r)
    + (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (acH K b v : ℝ) / mu57 K r
    + (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (((|s| : ℤ) : ℝ) / 2 ^ J) / mu57 K r

/-- The contribution of the `α'`-monomials `∏_j (β_j)^{m_j}` at a place `w`, with `m_j ≤ 2^{-J}|s|·D_j`
and `log |β_j|_w ≤ log⁺ |β_j|_w`. -/
noncomputable def estMon (K : Type*) [Field K] [NumberField K] {r : ℕ} (σ : Fin r → ℝ)
    (β : Fin r → K) (J : ℕ) (s : ℤ) (w : K → ℝ) : ℝ :=
  (((|s| : ℤ) : ℝ) / 2 ^ J) * ∑ j : Fin r, (pDj r (dK K) σ j : ℝ) * Real.posLog (w (β j))

/-- The Kummer (2-adic) contribution at a finite place `w`: `2Jh(D₀+1)·(−log w(2))`. -/
noncomputable def estCf (K : Type*) [Field K] [NumberField K] {n r : ℕ} (b : Fin n → ℤ) (v : ℕ)
    (σ : Fin r → ℝ) (J : ℕ) (w : K → ℝ) : ℝ :=
  ((2 : ℝ) * J * (acH K b v) * (((pD0 r (dK K) σ : ℕ) : ℝ) + 1)) * (- Real.log (w 2))

/-- The Kummer term summed over the finite places: `2Jh(D₀+1)d log 2 ≤ kumJ`. -/
noncomputable def estKum (K : Type*) [Field K] [NumberField K] {n r : ℕ} (b : Fin n → ℤ) (v : ℕ)
    (σ : Fin r → ℝ) (J : ℕ) : ℝ :=
  (2 : ℝ) * J * (acH K b v) * (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (dK K : ℝ) * Real.log 2

end Work.BW
