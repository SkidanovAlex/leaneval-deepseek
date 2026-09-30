import Mathlib
import Submission.Work.BW.est15defs
import Submission.Work.BW.est14_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# BW (15): the algebraic identity `acg φ … = φ (gKJ …)` at descent level `J`

Baker–Wüstholz (15) at the descent level `J` says that the value
`g^{(J)}(s;t) = acg φ α b k L ι v σ p J μ t0 t (s:ℂ)` of the descended auxiliary function
is the image under `φ : K →+* ℂ` of the explicit element
`gKJ … = ∑_{λ_j ≡ μ_j (2^J)} p λ · coefKJ λ ∈ K`.

The proof compares the two sums term by term: `acg_eq_sum` writes the complex side as a sum
of `estCoeff · estTorus`, while `gKJ` is a sum of `p λ · coefKJ λ`.  The only inputs are
that `φ` commutes with the rational constants (`Δ(γ_m(λ);t_m)`, `u(h)^{t₀}` and
`Θ(2^{-J}s + λ₋₁;h,λ₀+1,t₀)` are all images of rationals) and that `φ (α'_j) = e^{ℓ_j}`.
-/

namespace Work.BW

/-- Evaluation of a rational polynomial at a rational point is compatible with `ℚ ↪ ℂ`. -/
lemma pgk_rat_aeval_cast (x : ℚ) (q : Polynomial ℚ) :
    ((Polynomial.aeval x q : ℚ) : ℂ) = Polynomial.aeval (x : ℂ) q :=
  (Polynomial.aeval_algebraMap_apply ℂ x q).symm

/-- `φ` sends a rational constant of `K` to the corresponding complex number. -/
lemma pgk_phi_ratCast {K : Type*} [Field K] (φ : K →+* ℂ) (q : ℚ) :
    φ ((q : ℚ) : K) = (q : ℂ) :=
  map_ratCast φ q

/-- `φ` of the `Π`-factor `piRat` of `coefKJ`: the product of the `Δ(γ_m(λ); t_m)`. -/
lemma pgk_phi_piRat {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (b : Fin n → ℤ) (k : Fin n)
    (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (t : Fin (r - 1) → ℕ) (lm : AuxIdx r h D0 Dj) :
    φ ((piRat b k L ι h D0 Dj t lm : ℚ) : K)
      = ∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m) := by
  rw [piRat, pgk_phi_ratCast φ]
  push_cast
  refine Finset.prod_congr rfl (fun m _ => ?_)
  rw [← Delta_eq_deltaRat, gamInt_cast]

/-- `φ` of `u(h)`. -/
lemma pgk_phi_ulcm {K : Type*} [Field K] (φ : K →+* ℂ) (h : ℕ) :
    φ ((ulcm h : ℚ) : K) = (ulcm h : ℂ) := by
  rw [pgk_phi_ratCast φ, Rat.cast_natCast]

/-- `φ` of the `Y₀`-factor `Θ(2^{-J}s + λ₋₁; h, λ₀+1, t₀)` of `coefKJ`. -/
lemma pgk_phi_thetaJ {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (h D0 : ℕ)
    (Dj : Fin r → ℕ) (J t0 : ℕ) (s : ℤ) (lm : AuxIdx r h D0 Dj) :
    φ ((thetaJ h D0 Dj J t0 s lm : ℚ) : K)
      = Polynomial.aeval ((((2 : ℂ) ^ J)⁻¹) * (s : ℂ) + ((lm.1 : ℕ) : ℂ))
          (Polynomial.hasseDeriv t0 (deltaPoly h ^ ((lm.2.1 : ℕ) + 1))) := by
  have hpt : ((((s : ℚ) / 2 ^ J + ((lm.1 : ℕ) : ℚ) : ℚ)) : ℂ)
      = (((2 : ℂ) ^ J)⁻¹) * (s : ℂ) + ((lm.1 : ℕ) : ℂ) := by
    push_cast
    rw [div_eq_mul_inv]
    ring
  rw [thetaJ, thetaRatQ, pgk_phi_ratCast φ, pgk_rat_aeval_cast, hpt]

/-- `φ` of the `α'`-monomial: `φ ((α'_j)^{s·λ}) = (e^{sℓ_j})^{λ}`. -/
lemma pgk_phi_zpow {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (α : Fin n → K) (v : ℕ)
    (L : Fin r → Fin n → ℤ) (α' : Fin r → K)
    (hexp : ∀ i, Complex.exp (lamP φ α v L i) = φ (α' i)) (j : Fin r) (s : ℤ) (e : ℕ) :
    φ ((α' j) ^ (s * (e : ℤ))) = (Complex.exp ((s : ℂ) * lamP φ α v L j)) ^ e := by
  rw [map_zpow₀, ← hexp j]
  rw [← Complex.exp_int_mul (lamP φ α v L j) (s * (e : ℤ))]
  rw [← Complex.exp_nat_mul ((s : ℂ) * lamP φ α v L j) e]
  congr 1
  push_cast
  ring

/-- Term-by-term identity: `φ` of the `λ`-th summand `p λ · coefKJ λ` of `gKJ` is the
`λ`-th summand `estCoeff · estTorus` of `acg`. -/
lemma pgk_phi_coefKJ {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (α : Fin n → K) (v : ℕ)
    (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n)
    (α' : Fin r → K) (h D0 : ℕ) (Dj : Fin r → ℕ) (J t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (s : ℤ) (lm : AuxIdx r h D0 Dj)
    (hexp : ∀ i, Complex.exp (lamP φ α v L i) = φ (α' i)) :
    φ (coefKJ b k L ι α' h D0 Dj J t0 t s lm) =
      (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)) * (ulcm h : ℂ) ^ t0 *
        Polynomial.aeval ((((2 : ℂ) ^ J)⁻¹) * (s : ℂ) + ((lm.1 : ℕ) : ℂ))
          (Polynomial.hasseDeriv t0 (deltaPoly h ^ ((lm.2.1 : ℕ) + 1))) *
        ∏ j : Fin r, (Complex.exp ((s : ℂ) * lamP φ α v L j)) ^ ((lm.2.2 j : ℕ) / 2 ^ J) := by
  rw [coefKJ]
  simp only [map_mul, map_pow, map_prod]
  rw [pgk_phi_piRat, pgk_phi_ulcm, pgk_phi_thetaJ]
  rw [Finset.prod_congr rfl (fun j _ =>
        pgk_phi_zpow φ α v L α' hexp j s ((lm.2.2 j : ℕ) / 2 ^ J))]

/-- BW (15), algebraic identity at descent level `J`: the complex value `g^{(J)}(s;t)` of the descended auxiliary function at an integer `s` is the image under `φ` of the explicit element `gKJ` of `K` (a `K`-linear combination of the `p λ` with rational coefficients). -/
theorem phi_gKJ_eq_acg {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (s : ℤ) :
    φ (gKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ t0 t s)
      = acg φ α b k L ι v σ p J μ t0 t (s : ℂ) := by
  have hexp : ∀ j, Complex.exp (lamP φ α v L j) = φ (α' j) :=
    fun j => (H.hBH.2.2.1 j).2
  rw [acg_eq_sum]
  rw [gKJ, map_sum]
  refine Finset.sum_congr rfl (fun lm _ => ?_)
  by_cases hc : estCond J μ lm
  · rw [if_pos hc, if_pos hc, map_mul,
      pgk_phi_coefKJ φ α v b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)
        J t0 t s lm hexp]
    simp only [estGT, estCoeff, estTorus]
    ring
  · rw [if_neg hc, if_neg hc, map_zero]

end Work.BW
