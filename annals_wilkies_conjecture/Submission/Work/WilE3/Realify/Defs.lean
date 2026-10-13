/-
  annals_wilkies_conjecture, AREA E3, `Realify`: the realification of a complexified EA system.

  This module fixes the *vocabulary* of the realification step (`NOTES.md` §3, §5′): given an
  EA chain `c : EAChain k r` and a "chart choice" `cc : Fin r → ℝ` (one offset per chain
  function, `cc j ∈ πℤ`), we build

  * `mkChain c cc : SepChainLocal (k + k) (r + r)`, the separable chain whose `2k` variables are
    `(u, v)` (`z = u + i v`) and whose `2r` chain functions are `y_j = exp (Re ℓ_j (z))`
    (`φ = Real.exp`, `R = X`) and `t_j = tan ((Im ℓ_j (z) - cc j) / 2)` (`φ = Real.tan`,
    `R = 1 + X²`);
  * `realifyRe N e P`, `realifyIm N e P : EAPoly (k + k) (r + r)`, the real and imaginary parts of
    `Π_j (1 + t_j²)^N` times the complexified polynomial `P` under the substitution
    `z_i ↦ u_i + i v_i`, `e^{ℓ_j} ↦ e_j y_j (1 + 2 i t_j - t_j²) / (1 + t_j²)`, where `e_j` is the
    sign `e^{i cc j}` (`NOTES.md` §5′: one `t_j` per *chain function*, not per coordinate).

  The point of the vocabulary is the *evaluation identity*: on the chart,
  `S.ev (realifyRe N e P) (u,v) = Wval^N · (eaEvalC c P (u + i v)).re` and likewise for
  `realifyIm`, where `Wval = Π_j (1 + t_j²)`.  Since `Wval ≠ 0` on the chart, the realified system
  has the same zero set as the complexified one, and (because the real Jacobian of a holomorphic
  map is the realification of its complex Jacobian) the same nondegenerate zeros.  Khovanskii's
  bound for separable chains (`Work.WilE3.SepKhovanskiiLocal`) then applies on any bounded chart.
-/
import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Sep

namespace Work.WilE3.Realify

set_option autoImplicit false
noncomputable section
open Classical Topology
open WilkiesDesign.E

variable {k r : ℕ}

/-- The variable index type of the realified system: `Fin (k + k)` is `(u, v)` and `Fin (r + r)`
is `(y, t)`. -/
abbrev Sig (k r : ℕ) := Fin (k + k) ⊕ Fin (r + r)

/-- The realified system lives in `EAPoly (k + k) (r + r)`. -/
abbrev RPoly (k r : ℕ) := EAPoly (k + k) (r + r)

/-! ## §1. The variables -/

/-- The `u i` variable. -/
def Vu (i : Fin k) : RPoly k r := MvPolynomial.X (Sum.inl (Fin.castAdd k i))

/-- The `v i` variable. -/
def Vv (i : Fin k) : RPoly k r := MvPolynomial.X (Sum.inl (Fin.natAdd k i))

/-- The `y j` variable. -/
def Vy (j : Fin r) : RPoly k r := MvPolynomial.X (Sum.inr (Fin.castAdd r j))

/-- The `t j` variable. -/
def Vt (j : Fin r) : RPoly k r := MvPolynomial.X (Sum.inr (Fin.natAdd r j))

/-- The clearing factor `1 + t j ^ 2` (as a real polynomial). -/
def VW (j : Fin r) : RPoly k r := 1 + Vt j ^ 2

/-- The realified variable points of a pair `(u, v)`. -/
def mkPt (u v : Fin k → ℝ) : Fin (k + k) → ℝ := Fin.addCases u v

/-- The first `k` coordinates of a point of `ℝ^{2k}`. -/
def uOf (w : Fin (k + k) → ℝ) : Fin k → ℝ := fun i => w (Fin.castAdd k i)

/-- The last `k` coordinates of a point of `ℝ^{2k}`. -/
def vOf (w : Fin (k + k) → ℝ) : Fin k → ℝ := fun i => w (Fin.natAdd k i)

/-- The chain value point: `(u, v, y, t)` with `y_j = exp (∑ a j i u i + b j)` and
`t_j = tan ((∑ a j i v i - cc j)/2)`. -/
def chainPt (c : EAChain k r) (cc : Fin r → ℝ) (u v : Fin k → ℝ) : Sig k r → ℝ :=
  Sum.elim (mkPt u v)
    (Fin.addCases
      (fun j => Real.exp (∑ i, c.a j i * u i + c.b j))
      (fun j => Real.tan ((∑ i, c.a j i * v i - cc j) / 2)))

/-- The clearing factor, evaluated at the chain point: `Π_j (1 + t_j²)`. -/
def Wval (c : EAChain k r) (cc : Fin r → ℝ) (v : Fin k → ℝ) : ℝ :=
  ∏ j : Fin r, (1 + (Real.tan ((∑ i, c.a j i * v i - cc j) / 2)) ^ 2)

/-- The complex point attached to a real point of `ℝ^{2k}`: `w ↦ w_u + i w_v`. -/
def zOf {k : ℕ} (w : Fin (k + k) → ℝ) : Fin k → ℂ :=
  fun i => (w (Fin.castAdd k i) : ℂ) + (w (Fin.natAdd k i) : ℂ) * Complex.I

/-- The complexified system evaluated on `ℝ^{2k}` (through `zOf`). -/
def evalUV (c : EAChain k r) (P : EAPoly k r) (w : Fin (k + k) → ℝ) : ℂ :=
  eaEvalC c P (zOf w)

/-- The clearing factor as a polynomial: `(Π_j (1 + t_j²))^N`. -/
def WPow (N : ℕ) : RPoly k r := (∏ j : Fin r, VW (k := k) j) ^ N

/-- The realification `[[Re A, -Im A],[Im A, Re A]]` of a complex matrix (the matrix of the
`ℝ`-linear map underlying a `ℂ`-linear map, in the basis `e_j, i e_j`). -/
def reifyMat {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin (k + k)) (Fin (k + k)) ℝ :=
  Matrix.of fun i j => Fin.addCases
    (fun i' => Fin.addCases (fun j' => (A i' j').re) (fun j' => -(A i' j').im) j)
    (fun i' => Fin.addCases (fun j' => (A i' j').im) (fun j' => (A i' j').re) j) i

/-- The gradient of `S.ev Q` along a separable chain: `dx ↦ ∑ i, S.ev (S.d i Q) x * dx i`. -/
def grad {n r : ℕ} (S : SepChainLocal n r) (Q : EAPoly n r) (x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ a : Fin n, (S.ev (S.d a Q) x) • ContinuousLinearMap.proj a

theorem grad_apply {n r : ℕ} (S : SepChainLocal n r) (Q : EAPoly n r) (x v : Fin n → ℝ) :
    grad S Q x v = ∑ a : Fin n, S.ev (S.d a Q) x * v a := by
  simp only [grad, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

/-! ## §2. The realified polynomials -/

/-- The real part of a complex polynomial, coefficientwise. -/
def rePoly (p : MvPolynomial (Sig k r) ℂ) : RPoly k r :=
  ∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m).re

/-- The imaginary part of a complex polynomial, coefficientwise. -/
def imPoly (p : MvPolynomial (Sig k r) ℂ) : RPoly k r :=
  ∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m).im

/-- The variables of the complexified target ring. -/
def cU (i : Fin k) : MvPolynomial (Sig k r) ℂ := MvPolynomial.X (Sum.inl (Fin.castAdd k i))
def cV (i : Fin k) : MvPolynomial (Sig k r) ℂ := MvPolynomial.X (Sum.inl (Fin.natAdd k i))
def cY (j : Fin r) : MvPolynomial (Sig k r) ℂ := MvPolynomial.X (Sum.inr (Fin.castAdd r j))
def cT (j : Fin r) : MvPolynomial (Sig k r) ℂ := MvPolynomial.X (Sum.inr (Fin.natAdd r j))

/-- The imaginary unit, as a polynomial. -/
def cI : MvPolynomial (Sig k r) ℂ := MvPolynomial.C Complex.I

/-- `1 + t_j²` in the complexified target ring. -/
def cW (j : Fin r) : MvPolynomial (Sig k r) ℂ := 1 + cT j ^ 2

/-- `1 + 2 i t_j - t_j² = (1 + i t_j)²`, the numerator of `e^{2 i θ_j}` with `t_j = tan θ_j`. -/
def cZ (j : Fin r) : MvPolynomial (Sig k r) ℂ := 1 + 2 * cI * cT j - cT j ^ 2

/-- The image of the monomial with exponent vector `m` under the realification: `N` is the
clearing exponent (which must dominate the `t`-exponents used). -/
def monoNum (N : ℕ) (e : Fin r → ℝ) (m : (Fin k ⊕ Fin r) →₀ ℕ) : MvPolynomial (Sig k r) ℂ :=
  (∏ i : Fin k, (cU i + cI * cV i) ^ (m (Sum.inl i))) *
    (∏ j : Fin r, ((MvPolynomial.C (e j : ℂ)) * cY j * cZ j) ^ (m (Sum.inr j))) *
    (∏ j : Fin r, (cW j) ^ (N - m (Sum.inr j)))

/-- The support sum of a coefficient family is additive in the polynomial. -/
theorem sum_support_add {σ : Type*} [DecidableEq σ] {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (v : (σ →₀ ℕ) → M) (P Q : MvPolynomial σ ℝ) :
    (∑ m ∈ (P + Q).support, (P + Q).coeff m • v m)
      = (∑ m ∈ P.support, P.coeff m • v m) + (∑ m ∈ Q.support, Q.coeff m • v m) := by
  have h1 : (∑ m ∈ (P + Q).support, (P + Q).coeff m • v m)
      = ∑ m ∈ P.support ∪ Q.support, (P + Q).coeff m • v m :=
    Finset.sum_subset MvPolynomial.support_add fun x _ hx => by
      rw [MvPolynomial.notMem_support_iff.mp hx, zero_smul]
  have h2 : (∑ m ∈ P.support, P.coeff m • v m)
      = ∑ m ∈ P.support ∪ Q.support, P.coeff m • v m :=
    Finset.sum_subset Finset.subset_union_left fun x _ hx => by
      rw [MvPolynomial.notMem_support_iff.mp hx, zero_smul]
  have h3 : (∑ m ∈ Q.support, Q.coeff m • v m)
      = ∑ m ∈ P.support ∪ Q.support, Q.coeff m • v m :=
    Finset.sum_subset Finset.subset_union_right fun x _ hx => by
      rw [MvPolynomial.notMem_support_iff.mp hx, zero_smul]
  rw [h1, h2, h3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, add_smul]

/-- The support sum of a coefficient family is `ℝ`-homogeneous in the polynomial. -/
theorem sum_support_smul {σ : Type*} [DecidableEq σ] {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (v : (σ →₀ ℕ) → M) (a : ℝ) (P : MvPolynomial σ ℝ) :
    (∑ m ∈ (a • P).support, (a • P).coeff m • v m) = a • (∑ m ∈ P.support, P.coeff m • v m) := by
  have h1 : (∑ m ∈ (a • P).support, (a • P).coeff m • v m)
      = ∑ m ∈ P.support, (a • P).coeff m • v m :=
    Finset.sum_subset (MvPolynomial.support_smul (a := a)) fun x _ hx => by
      rw [MvPolynomial.notMem_support_iff.mp hx, zero_smul]
  rw [h1, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_smul]

/-- The real part of the realified system, as a linear map in the polynomial. -/
def realifyRe (N : ℕ) (e : Fin r → ℝ) : EAPoly k r →ₗ[ℝ] RPoly k r where
  toFun P := ∑ m ∈ P.support, P.coeff m • rePoly (monoNum (k := k) (r := r) N e m)
  map_add' P Q := sum_support_add _ P Q
  map_smul' a P := sum_support_smul _ a P

/-- The imaginary part of the realified system, as a linear map in the polynomial. -/
def realifyIm (N : ℕ) (e : Fin r → ℝ) : EAPoly k r →ₗ[ℝ] RPoly k r where
  toFun P := ∑ m ∈ P.support, P.coeff m • imPoly (monoNum (k := k) (r := r) N e m)
  map_add' P Q := sum_support_add _ P Q
  map_smul' a P := sum_support_smul _ a P

/-! ## §3. The separable chain -/

/-- The coefficients of the realified chain: `a (inl j) (inl i) = c.a j i` for the `y`-chain and
`a (inr j) (inr i) = c.a j i / 2` for the `t`-chain, all other entries `0`. -/
def chainA (c : EAChain k r) : Fin (r + r) → Fin (k + k) → ℝ :=
  Fin.addCases
    (fun j => Fin.addCases (fun i => c.a j i) (fun _ => 0))
    (fun j => Fin.addCases (fun _ => 0) (fun i => c.a j i / 2))

/-- The constant terms: `b (inl j) = c.b j` for the `y`-chain and `b (inr j) = - cc j / 2` for the
`t`-chain. -/
def chainB (c : EAChain k r) (cc : Fin r → ℝ) : Fin (r + r) → ℝ :=
  Fin.addCases (fun j => c.b j) (fun j => -cc j / 2)

/-- The one-variable chain functions: `exp` and `tan`. -/
def chainPhi : Fin (r + r) → ℝ → ℝ :=
  Fin.addCases (fun _ => Real.exp) (fun _ => Real.tan)

/-- The differential relations `R = X` (for `exp`) and `R = 1 + X²` (for `tan`). -/
def chainR : Fin (r + r) → MvPolynomial (Fin 1) ℝ :=
  Fin.addCases (fun _ => MvPolynomial.X 0) (fun _ => 1 + MvPolynomial.X 0 ^ 2)

/-- The domains: everything for `exp`, `{cos ≠ 0}` for `tan`. -/
def chainDom : Fin (r + r) → Set ℝ :=
  Fin.addCases (fun _ => Set.univ) (fun _ => {y | Real.cos y ≠ 0})

/-- `Real.tan` satisfies `φ' = 1 + φ²` where it is defined. -/
theorem hasDerivAt_tan_one_add_sq (y : ℝ) (h : Real.cos y ≠ 0) :
    HasDerivAt Real.tan (1 + Real.tan y ^ 2) y := by
  have h' := Real.hasDerivAt_tan h
  convert h' using 1
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  nlinarith [Real.sin_sq y, Real.cos_sq_add_sin_sq y]

/-- The chain differential relation, case by case. -/
theorem chain_hasDeriv :
    ∀ (j : Fin (r + r)) (y : ℝ), y ∈ chainDom (r := r) j →
      HasDerivAt (chainPhi (r := r) j)
        ((chainR (r := r) j).eval (fun _ => chainPhi (r := r) j y)) y := by
  intro j y hy
  revert hy
  refine Fin.addCases (motive := fun j => y ∈ chainDom (r := r) j →
      HasDerivAt (chainPhi (r := r) j)
        ((chainR (r := r) j).eval (fun _ => chainPhi (r := r) j y)) y) ?_ ?_ j
  · intro i _
    simp only [chainDom, chainPhi, chainR, Fin.addCases_left]
    simpa using Real.hasDerivAt_exp y
  · intro i hyc
    simp only [chainDom, chainPhi, chainR, Fin.addCases_right] at hyc ⊢
    have h := hasDerivAt_tan_one_add_sq y hyc
    simpa using h

/-- The realified separable chain. -/
def mkChain (c : EAChain k r) (cc : Fin r → ℝ) : SepChainLocal (k + k) (r + r) where
  a := chainA c
  b := chainB c cc
  phi := chainPhi
  R := chainR
  dom := chainDom
  hderiv := chain_hasDeriv

end

end Work.WilE3.Realify
