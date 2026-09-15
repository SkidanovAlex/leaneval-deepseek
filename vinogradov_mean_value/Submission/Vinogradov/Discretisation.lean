import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Submission.Vinogradov.Decoupling
import Submission.Vinogradov.DecouplingThm12
import Submission.Vinogradov.NormCoord
import Submission.Vinogradov.Orthogonality
import Submission.Commons.Algebra.BigOperators.sum_pow_eq_sum_pi
import Submission.Commons.Analysis.Real.add_pow_le_two_pow_mul
import Submission.Commons.Analysis.Real.exp_neg_pi_sq_mul_poly_bounded

noncomputable section
open MeasureTheory Complex Classical
open scoped Real BigOperators FourierTransform RealInnerProductSpace
open LeanEval.NumberTheory.VinogradovMeanValue

set_option autoImplicit false

/-!
# The discretisation bound `bdg_Jsep` (BDG Cor. 4.2) from BDG Thm 4.1

This module proves the analytic discretisation bound `bdg_Jsep` (BDG,
"Proof of the main conjecture in Vinogradov's mean value theorem for degrees
higher than three", Ann. Math. 184 (2016), Cor. 4.2 specialised to the integer
point set `{1,…,X}`), from the uniform discrete restriction theorem
`bdg_discrete_restriction` (their Thm 4.1, PROVEN in `Decoupling.lean` modulo
its critical case `bdg_critical`).  Once `bdg_Jsep` is proved here, the module
is plugged into the main chain by removing the placeholder `bdg_Jsep`
(theorem + `vmvt_of_Jsep_bound` + `vmvt_of_bdg`) from the tail of
`Decoupling.lean` and importing this module from `Main.lean` instead.

## The proof (BDG's Schwartz-function / change-of-variables argument)

For the integer point set `{1,…,X}` (`N = X`, points `i ↦ i ∈ (i−1, i]`):

1. **Test function.**  For `V = E k = ℝᵏ` let `gaussC` be the complexified
   Gaussian `v ↦ exp(−π‖v‖²)` and let `φ_X(x) = exp(πk − π‖x‖²/X^{2k})` be
   its `Xᵏ`-dilation scaled by `e^{πk}`.  The Fourier transform is known in
   closed form (Mathlib `Analysis.SpecialFunctions.Gaussian.FourierTransform`,
   used through `gaussFT_closed`, `gaussFT_char`, `integral_gauss_scale`
   below): for `c > 0` and `ω ∈ E k`

       ∫_x exp(−π‖x/c‖²) · e^{−2πi⟨x,ω⟩} dx = cᵏ · exp(−π‖c·ω‖²).

2. **Upper bound (BDG eq. (fek21) at `p = 2s`).**  With `R = Xᵏ`, the weight
   `φ_X` is dominated pointwise by a constant times the ball weight
   `w_{B(0,R)}` (`gauss_dominate_ballWeight`), so the `φ_X`-weighted integral
   is bounded by `bdg_discrete_restriction` applied to `aᵢ = 1`,
   `tᵢ = (i+1)/X` at `p = 2s` (`thm41_upper_bound` below).

3. **Lower bound (counting).**  Expanding `|f|^{2s}` (`f = Σ_i e(x·γ(tᵢ))`)
   as a double sum over pairs `(u,v)` of `s`-tuples of indices and integrating
   term by term (`expansion_term`), each term equals
   `X^{k²}·exp(−π‖Xᵏ·ω(u,v)‖²)` where the frequency vector has coordinates
   `ω(u,v)_j = (M_u(j+1) − M_v(j+1))/X^{j+1}`, `M_u(d) = Σ_r (u_r+1)^d`.
   Every term is positive; a term is `≥ X^{k²}e^{−πk}` whenever
   `|X^{k−d}(M_u(d) − M_v(d))| ≤ 1` for `d = 1,…,k` — exactly the `Jsep`
   condition on the pair of value tuples (`goodFin`).  The count of good
   index pairs is at least `Jsep s k X` (`goodFin_card_ge_Jsep`), giving
   `Jsep·X^{k²} ≤ ∫ φ_X |f|^{2s}` (`lower_bound_Jsep`).

4. **Assembly.**  Combine 2 and 3, divide by `X^{k²}`, bound
   `(X^{ε′}+X^{α+ε′})^{2s} ≤ 2^{2s}(X^{2sε′}+X^{2sα+2sε′})` (Commons
   `add_pow_le_two_pow_mul`), and choose `ε′ = ε/(2s)`; the exponents become
   exactly `s + ε` and `2s − k(k+1)/2 + ε`, matching `rhs s k ε X`
   (`bdg_Jsep_core`).

**Status (this file has no sorries).**  The Gaussian–Fourier engine, the
value-tuple character identities, the term evaluation and pair expansion, the
real–complex bridge (`Tint_complex_eq`, `Tint_eq_sum_terms`), the counting
injection (`goodFin_card_ge_Jsep`), the term lower bound (`term_lower_bound`,
`lower_bound_Jsep`), the Schwartz domination (`phiR_le_const_ballWeight`),
the BDG-application upper bound (`thm41_upper_bound`) and the final assembly
`bdg_Jsep_core` (BDG Cor. 4.2) are all PROVEN below; `vmvt_of_bdg` is
re-exported at the end.  The only remaining input to the whole chain is the
critical case `bdg_critical` of `bdg_discrete_restriction` in
`Decoupling.lean` (the ℓ²-decoupling theorem for the moment curve).
-/

namespace Submission.Vinogradov

/-- the complexified Gaussian `exp(−π‖v‖²)` on `E k` -/
def gaussC (k : ℕ) (v : E k) : ℂ := cexp (-(π : ℂ) * ‖v‖ ^ 2)

/-- Fourier transform of the Gaussian is a Gaussian: `𝓕(e^{−π‖v‖²})(w) = e^{−π‖w‖²}`. -/
lemma gaussFT_closed (k : ℕ) (w : E k) :
    (𝓕 (fun v : E k => gaussC k v)) w = cexp (-(π : ℂ) * ‖w‖ ^ 2) := by
  have hb : 0 < ((π : ℂ)).re := by simp [Real.pi_pos]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold gaussC
  rw [fourier_gaussian_innerProductSpace (V := E k) (b := (π : ℂ)) hb w]
  simp [hpi]
  congr 1
  field_simp [hpi]

/-- Explicit character form of the Gaussian Fourier integral
`∫_v e^{−π‖v‖²} e^{−2πi⟨v,w⟩} dv = e^{−π‖w‖²}`. -/
lemma gaussFT_char (k : ℕ) (w : E k) :
    (∫ v : E k, gaussC k v * cexp (↑(-2 * π * ⟪v, w⟫) * Complex.I))
      = cexp (-(π : ℂ) * ‖w‖ ^ 2) := by
  calc
    (∫ v : E k, gaussC k v * cexp (↑(-2 * π * ⟪v, w⟫) * Complex.I))
        = 𝓕 (fun v : E k => gaussC k v) w := by
          rw [Real.fourier_eq']
          apply integral_congr_ae
          filter_upwards with v
          simp [smul_eq_mul, mul_comm]
    _ = cexp (-(π : ℂ) * ‖w‖ ^ 2) := gaussFT_closed k w

/-- The scaled Gaussian Fourier integral: for `c > 0`,
`∫_x e^{−π‖x/c‖²} e^{−2πi⟨x,ω⟩} dx = cᵏ · e^{−π‖c·ω‖²}` (the change of
variables `x = c·y`; `c·ω` is the `ℝ`-scalar action on the vector `ω`). -/
lemma integral_gauss_scale (k : ℕ) (c : ℝ) (hc : 0 < c) (ω : E k) :
    (∫ x : E k, gaussC k (c⁻¹ • x) * cexp (↑(-2 * π * ⟪x, ω⟫) * Complex.I))
      = ((c ^ k : ℝ) : ℂ) * cexp (-(π : ℂ) * ‖c • ω‖ ^ 2) := by
  have hc0 : 0 ≤ c := le_of_lt hc
  let f : E k → ℂ := fun y => gaussC k y * cexp (↑(-2 * π * ⟪y, c • ω⟫) * Complex.I)
  have hmain : (∫ x : E k, f (c⁻¹ • x)) = (c ^ Module.finrank ℝ (E k) : ℝ) • (∫ y : E k, f y) := by
    exact MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (μ := (volume : Measure (E k))) f hc0
  have hfin : Module.finrank ℝ (E k) = k := by simp
  have hid : (fun x : E k => f (c⁻¹ • x)) = fun x : E k =>
      gaussC k (c⁻¹ • x) * cexp (↑(-2 * π * ⟪x, ω⟫) * Complex.I) := by
    funext x
    unfold f
    congr 1
    rw [inner_smul_left]
    simp [inner_smul_right, hc.ne']
  rw [← hid, hmain, hfin]
  have hf : (∫ y : E k, f y) = cexp (-(π : ℂ) * ‖c • ω‖ ^ 2) := by
    calc
      (∫ y : E k, f y) = (∫ y : E k, gaussC k y * cexp (↑(-2 * π * ⟪y, c • ω⟫) * Complex.I)) := by
        rfl
      _ = cexp (-(π : ℂ) * ‖c • ω‖ ^ 2) := gaussFT_char k (c • ω)
  rw [hf]
  simp

/-- `(z·conj z)^s = ‖z‖^{2s}` (as complex, `‖z‖` real): the bridge between the
`|f|^{2s}` power and the `f^s·conj(f)^s` double character sum. -/
lemma norm_pow_eq_cpow_conj (z : ℂ) (s : ℕ) :
    z ^ s * star z ^ s = ((‖z‖ ^ (2 * s) : ℝ) : ℂ) := by
  have h1 : z * star z = (‖z‖ ^ 2 : ℝ) := by
    calc
      z * star z = (Complex.normSq z : ℂ) := by simpa using (Complex.mul_conj z)
      _ = (‖z‖ ^ 2 : ℝ) := by rw [Complex.normSq_eq_norm_sq z]
  have hmul : z ^ s * star z ^ s = (z * star z) ^ s := by rw [← mul_pow]
  rw [hmul, h1]
  rw [← Complex.ofReal_pow]
  congr 1
  rw [pow_mul]

/-- product of two finite sums over types is the sum over the product type -/
lemma sum_pair_mul_complex {α β : Type*} [Fintype α] [Fintype β] (a : α → ℂ) (b : β → ℂ) :
    (∑ x : α, a x) * (∑ y : β, b y) = ∑ p : α × β, a p.1 * b p.2 := by
  classical
  calc
    (∑ x : α, a x) * (∑ y : β, b y) = ∑ x : α, a x * (∑ y : β, b y) := by
      rw [Finset.sum_mul]
    _ = ∑ x : α, ∑ y : β, a x * b y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
    _ = ∑ p : α × β, a p.1 * b p.2 := by
      rw [← Finset.sum_product' (s := (Finset.univ : Finset α)) (t := (Finset.univ : Finset β))
          (f := fun x y => a x * b y)]
      rw [Finset.univ_product_univ]

/-- the integer value of index `i : Fin X` is `i.1 + 1`; the power sum
`M_u(d) = Σ_r (u_r + 1)^d` over the `s` indices of a tuple of values. -/
def Msum (X : ℕ) (d : ℕ) {s : ℕ} (u : Fin s → Fin X) : ℕ :=
  ∑ r : Fin s, ((u r).1 + 1) ^ d

/-- the separated condition (BDG Cor. 4.2) for pairs of index tuples: for
`1 ≤ j ≤ k`, `|Z_j| ≤ X^{j−k}` where `Z_j = M_u(j) − M_v(j)`. -/
def goodFin (s k X : ℕ) (uv : (Fin s → Fin X) × (Fin s → Fin X)) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ k →
    |(((Msum X j uv.1 : ℤ) - (Msum X j uv.2 : ℤ)) : ℝ)| ≤ sepBound X j k

/-- The exponential character `e(x·γ(m/X))` of the single value `m ∈ [1,X]`
(in the BDG separation convention `t_m = m/X`), summed over `Fin X`. -/
def valSum (k X : ℕ) (x : E k) : ℂ :=
  ∑ i : Fin X, momChar k x ((((i.1 + 1 : ℕ) : ℝ)) / X)

/-- the separated character sum `Σ_i e(x·γ(t_i))` with `t_i = (i+1)/X`,
coefficients `1` — exactly the object bounded by `bdg_discrete_restriction`. -/
lemma valSum_eq_sepCharSum_ones (k X : ℕ) (x : E k) :
    valSum k X x = sepCharSum k (fun _ : Fin X => (1 : ℂ)) (fun i : Fin X => (((i.1 + 1 : ℕ) : ℝ) / X)) x := by
  simp [valSum, sepCharSum]


/-! ## Term evaluation: value-tuple characters and their Gaussian integrals -/

/-- frequency vector of a value tuple: coordinate `j` ↦ `M_u(j+1)/X^{j+1}` -/
def freq (X k : ℕ) {s : ℕ} (u : Fin s → Fin X) : E k :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm
    (fun j : Fin k => ((Msum X (j.val + 1) u : ℕ) : ℝ) / (X : ℝ) ^ (j.val + 1))

/-- the character of a value tuple: `Π_r e(x·γ((u_r+1)/X))` -/
def valMomChar (k X : ℕ) {s : ℕ} (x : E k) (u : Fin s → Fin X) : ℂ :=
  ∏ r : Fin s, momChar k x ((((u r).1 + 1 : ℕ) : ℝ) / X)

/-- pointwise identity: the product character of a value tuple equals the single
character with frequency vector `freq`: `e(x·freq u)` (up to the `2πi` exponent). -/
lemma valMomChar_eq (k X s : ℕ) (x : E k) (u : Fin s → Fin X) :
    valMomChar k X x u = cexp (((2 * Real.pi : ℂ) * Complex.I) *
        (((∑ j : Fin k, x j * (freq X k u) j : ℝ) : ℂ))) := by
  unfold valMomChar
  let c : ℂ := (2 * Real.pi : ℂ) * Complex.I
  let t : Fin s → ℝ := fun r => (((u r).1 + 1 : ℕ) : ℝ) / X
  let ph : Fin s → ℝ := fun r => (∑ j : Fin k, x j * (t r) ^ (j.val + 1) : ℝ)
  have hf : ∀ r : Fin s, momChar k x (t r) = cexp (c * ↑(ph r)) := by
    intro r
    rfl
  calc
    (∏ r : Fin s, momChar k x (t r)) = ∏ r : Fin s, cexp (c * ↑(ph r)) := by
      exact Finset.prod_congr rfl (fun r hr => hf r)
    _ = cexp (∑ r : Fin s, c * ↑(ph r)) := by
      rw [Complex.exp_sum]
    _ = cexp (c * (∑ r : Fin s, ↑(ph r) : ℂ)) := by
      congr 1
      rw [← Finset.mul_sum]
    _ = cexp (c * ↑(∑ r : Fin s, ph r)) := by
      congr 1
      rw [← Complex.ofReal_sum]
    _ = cexp (c * ↑(∑ j : Fin k, x j * (freq X k u) j : ℝ)) := by
      congr 1
      have hcoord : ∀ j : Fin k, (freq X k u) j = ∑ r : Fin s, (t r) ^ (j.val + 1) := by
        intro j
        unfold freq t
        simp [Msum, Finset.sum_div, div_pow]
      have hReal : (∑ r : Fin s, ph r) = (∑ j : Fin k, x j * (freq X k u) j : ℝ) := by
        calc
          (∑ r : Fin s, ph r) = ∑ r : Fin s, ∑ j : Fin k, x j * (t r) ^ (j.val + 1) := by
            rfl
          _ = ∑ j : Fin k, ∑ r : Fin s, x j * (t r) ^ (j.val + 1) := by
            rw [Finset.sum_comm]
          _ = ∑ j : Fin k, x j * (∑ r : Fin s, (t r) ^ (j.val + 1)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [← Finset.mul_sum]
          _ = ∑ j : Fin k, x j * (freq X k u) j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hcoord j]
      exact congrArg (fun z : ℂ => c * z) (congrArg (fun z : ℝ => (z : ℂ)) hReal)

/-- measure-preservation of negation on `E k` (x ↦ −x) -/
lemma integral_neg_eq (k : ℕ) (f : E k → ℂ) :
    (∫ x : E k, f (-x)) = ∫ x : E k, f x := by
  let e : E k ≃ₗᵢ[ℝ] E k := LinearIsometryEquiv.neg (R := ℝ) (E := E k)
  have hmp : MeasureTheory.MeasurePreserving (⇑e) volume volume := e.measurePreserving
  have hem : MeasurableEmbedding (⇑e) := e.toHomeomorph.measurableEmbedding
  have h := MeasureTheory.MeasurePreserving.integral_comp (μ := (volume : Measure (E k))) hmp hem f
  change (∫ x : E k, f (e x)) = ∫ x : E k, f x
  exact h

/-- pointwise product identity: `conj(char u) · char v` is the single character
with frequency vector `freq u − freq v`. -/
lemma star_valMomChar_mul (k X s : ℕ) (x : E k) (u v : Fin s → Fin X) :
    star (valMomChar k X x u) * valMomChar k X x v
      = cexp (↑(-2 * π * ⟪x, freq X k u - freq X k v⟫) * Complex.I) := by
  rw [valMomChar_eq k X s x u, valMomChar_eq k X s x v]
  let c : ℂ := (2 * Real.pi : ℂ) * Complex.I
  let A : ℝ := ∑ j : Fin k, x j * (freq X k u) j
  let B : ℝ := ∑ j : Fin k, x j * (freq X k v) j
  have hA : A = ⟪x, freq X k u⟫ := by rw [inner_coord]
  have hB : B = ⟪x, freq X k v⟫ := by rw [inner_coord]
  have hdiff : A - B = ⟪x, freq X k u - freq X k v⟫ := by
    rw [hA, hB]
    rw [← inner_sub_right]
  change star (cexp (c * (A : ℂ))) * cexp (c * (B : ℂ))
      = cexp (↑(-2 * π * ⟪x, freq X k u - freq X k v⟫) * Complex.I)
  have hstar : star (cexp (c * (A : ℂ))) = cexp (-c * (A : ℂ)) := by
    calc
      star (cexp (c * (A : ℂ))) = cexp (star (c * (A : ℂ))) := (Complex.exp_conj (c * (A : ℂ))).symm
      _ = cexp (-c * (A : ℂ)) := by
            congr 1
            simp [c]
  rw [hstar]
  rw [← Complex.exp_add]
  congr 1
  have hexp : -c * (A : ℂ) + c * (B : ℂ) = (↑(-2 * π * (A - B) : ℝ) : ℂ) * Complex.I := by
    simp [c]
    ring_nf
  rw [hexp]
  congr 2
  rw [hdiff]

/-- **Power expansion of the character sum over pairs of value tuples**:
`star(valSum)^s · valSum^s = Σ_{u,v} star(valMomChar u) · valMomChar v`
(the `−`-character convention of BDG's Cor. 4.2, matching the Gaussian
evaluation `integral_gauss_scale`).  Built from
`Commons.Algebra.BigOperators.sum_pow_eq_sum_pi` and `sum_pair_mul_complex`. -/
lemma expansion_eq (k X s : ℕ) (x : E k) :
    star (valSum k X x) ^ s * (valSum k X x) ^ s
      = ∑ uv : (Fin s → Fin X) × (Fin s → Fin X),
          star (valMomChar k X x uv.1) * valMomChar k X x uv.2 := by
  have hS : (valSum k X x) ^ s = ∑ u : Fin s → Fin X, valMomChar k X x u := by
    rw [show valSum k X x = ∑ i : Fin X, momChar k x ((((i.1 + 1 : ℕ) : ℝ)) / X) by rfl]
    rw [Commons.Algebra.BigOperators.sum_pow_eq_sum_pi (α := Fin X) (f := fun i : Fin X => momChar k x ((((i.1 + 1 : ℕ) : ℝ)) / X))]
    unfold valMomChar
    rfl
  have hStarS : star ((valSum k X x) ^ s) = ∑ v : Fin s → Fin X, star (valMomChar k X x v) := by
    rw [hS]
    simp
  have hpow : star (valSum k X x) ^ s = star ((valSum k X x) ^ s) := by
    simpa using (map_pow (starRingEnd ℂ) (valSum k X x) s).symm
  rw [hpow, hStarS, hS]
  rw [sum_pair_mul_complex]

lemma term_eval (k X : ℕ) (hX : 1 ≤ X) {s : ℕ} (u v : Fin s → Fin X) :
    (∫ x : E k, gaussC k (((X : ℝ) ^ k)⁻¹ • x)
        * star (valMomChar k X x u) * valMomChar k X x v)
      = (((X : ℝ) ^ k) ^ k : ℂ) * cexp (-(π : ℂ) * ‖(X : ℝ) ^ k • (freq X k u - freq X k v)‖ ^ 2) := by
  let c : ℝ := (X : ℝ) ^ k
  have hc : 0 < c := by
    dsimp [c]
    exact pow_pos (by exact_mod_cast (lt_of_lt_of_le zero_lt_one hX)) k
  have hpt : (fun x : E k => gaussC k (c⁻¹ • x) * star (valMomChar k X x u) * valMomChar k X x v)
      = fun x : E k => gaussC k (c⁻¹ • x)
        * cexp (↑(-2 * π * ⟪x, freq X k u - freq X k v⟫) * Complex.I) := by
    funext x
    rw [mul_assoc]
    rw [star_valMomChar_mul k X s x u v]
  calc
    (∫ x : E k, gaussC k (c⁻¹ • x) * star (valMomChar k X x u) * valMomChar k X x v)
        = (∫ x : E k, gaussC k (c⁻¹ • x)
            * cexp (↑(-2 * π * ⟪x, freq X k u - freq X k v⟫) * Complex.I)) := by
          rw [hpt]
    _ = ((c ^ k : ℝ) : ℂ) * cexp (-(π : ℂ) * ‖c • (freq X k u - freq X k v)‖ ^ 2) := by
          exact integral_gauss_scale k c hc (freq X k u - freq X k v)
    _ = (((X : ℝ) ^ k) ^ k : ℂ) * cexp (-(π : ℂ) * ‖(X : ℝ) ^ k • (freq X k u - freq X k v)‖ ^ 2) := by
          have hfac : ((c ^ k : ℝ) : ℂ) = (((X : ℝ) ^ k) ^ k : ℂ) := by
            simp [c]
          rw [hfac]

/-- real Gaussian weight φR(X) on E k: exp(−π·‖x/X^k‖²) -/
def phiR (k X : ℕ) (x : E k) : ℝ := Real.exp (-π * ‖((X : ℝ) ^ k)⁻¹ • x‖ ^ 2)

/-- real term value of the Gaussian character integral -/
def termVal (k X : ℕ) {s : ℕ} (uv : (Fin s → Fin X) × (Fin s → Fin X)) : ℝ :=
  ((X : ℝ) ^ k) ^ k * Real.exp (-π * ‖(X : ℝ) ^ k • (freq X k uv.1 - freq X k uv.2)‖ ^ 2)

lemma phiR_nonneg (k X : ℕ) (x : E k) : 0 ≤ phiR k X x := by
  unfold phiR
  exact Real.exp_nonneg _

lemma gaussC_eq_ofReal (k : ℕ) (v : E k) : gaussC k v = ((Real.exp (-π * ‖v‖ ^ 2)) : ℂ) := by
  unfold gaussC
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

lemma gaussC_scaled_eq_ofReal (k X : ℕ) (x : E k) :
    gaussC k (((X : ℝ) ^ k)⁻¹ • x) = (phiR k X x : ℂ) := by
  rw [gaussC_eq_ofReal]
  rfl

/-- `conj(valSum)^s · valSum^s = |valSum|^{2s}` (as complex, real on the right) -/
lemma star_valSum_pow_mul (k X s : ℕ) (x : E k) :
    star (valSum k X x) ^ s * (valSum k X x) ^ s
      = ((‖valSum k X x‖ ^ (2 * s) : ℝ) : ℂ) := by
  rw [mul_comm]
  exact norm_pow_eq_cpow_conj (valSum k X x) s

/-- unit modulus of the value-tuple character pair product -/
lemma star_mul_char_norm_one (k X s : ℕ) (x : E k) (u v : Fin s → Fin X) :
    ‖star (valMomChar k X x u) * valMomChar k X x v‖ = 1 := by
  rw [star_valMomChar_mul k X s x u v]
  simpa [mul_comm] using
    (Commons.Analysis.Complex.norm_exp_mul_I_ofReal
      (-2 * Real.pi * ⟪x, freq X k u - freq X k v⟫))

lemma norm_smul_sq_real (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : ℝ) (ha : 0 ≤ a) (x : V) : ‖a • x‖ ^ 2 = a ^ 2 * ‖x‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, mul_pow]

/-- the product integrand of the Gaussian term integral is dominated by φR -/
lemma gauss_char_integrand_norm_le (k X : ℕ) (_hX : 1 ≤ X) {s : ℕ} (u v : Fin s → Fin X) :
    ∀ x : E k, ‖gaussC k (((X : ℝ) ^ k)⁻¹ • x) * star (valMomChar k X x u) * valMomChar k X x v‖
      ≤ phiR k X x := by
  intro x
  have hnn : 0 ≤ Real.exp (-π * ‖((X : ℝ) ^ k)⁻¹ • x‖ ^ 2) := Real.exp_nonneg _
  have hmul :
      ‖(Real.exp (-π * ‖((X : ℝ) ^ k)⁻¹ • x‖ ^ 2) : ℂ) * star (valMomChar k X x u) * valMomChar k X x v‖
        = phiR k X x := by
    calc
      ‖(Real.exp (-π * ‖((X : ℝ) ^ k)⁻¹ • x‖ ^ 2) : ℂ) * star (valMomChar k X x u) * valMomChar k X x v‖
          = ‖(Real.exp (-π * ‖((X : ℝ) ^ k)⁻¹ • x‖ ^ 2) : ℂ)
              * (star (valMomChar k X x u) * valMomChar k X x v)‖ := by
              rw [mul_assoc]
      _ = ‖(Real.exp (-π * ‖((X : ℝ) ^ k)⁻¹ • x‖ ^ 2) : ℂ)‖
              * ‖star (valMomChar k X x u) * valMomChar k X x v‖ := by
              rw [norm_mul]
      _ = Real.exp (-π * ‖((X : ℝ) ^ k)⁻¹ • x‖ ^ 2) * 1 := by
              rw [complex_norm_ofReal_nonneg (Real.exp (-π * ‖((X : ℝ) ^ k)⁻¹ • x‖ ^ 2)) hnn,
                star_mul_char_norm_one k X s x u v]
      _ = phiR k X x := by
              unfold phiR
              ring
  calc
    ‖gaussC k (((X : ℝ) ^ k)⁻¹ • x) * star (valMomChar k X x u) * valMomChar k X x v‖
        ≤ phiR k X x := by
          simpa [gaussC_eq_ofReal] using le_of_eq hmul

/-- the real Gaussian weight is integrable on E k for X ≥ 1 -/
lemma phiR_integrable (k X : ℕ) (hX : 1 ≤ X) :
    Integrable (fun x : E k => phiR k X x) volume := by
  let c : ℝ := (X : ℝ) ^ k
  have hc0 : 0 < c := by
    dsimp [c]
    exact pow_pos (by exact_mod_cast (lt_of_lt_of_le zero_lt_one hX)) k
  let B : ℝ := π * (c⁻¹) ^ 2
  have hB : 0 < B := by
    dsimp [B]
    positivity
  let F : E k → ℂ := fun v => cexp (-(B : ℂ) * (‖v‖ : ℂ) ^ 2 + (0 : ℂ) * (⟪(0 : E k), v⟫ : ℝ))
  have hintcF : Integrable F volume := by
    dsimp [F]
    exact GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E k)
      (b := (B : ℂ)) (show 0 < ((B : ℂ)).re by simp [hB]) (0 : ℂ) (0 : E k)
  have hnorm_eq : (fun x : E k => ‖F x‖) = fun x : E k => Real.exp (-B * ‖x‖ ^ 2) := by
    funext x
    dsimp [F]
    have hz : -(B : ℂ) * (‖x‖ : ℂ) ^ 2 + (0 : ℂ) * (⟪(0 : E k), x⟫ : ℝ)
        = (↑(-B * ‖x‖ ^ 2) : ℂ) := by
      push_cast
      ring
    rw [hz]
    exact Complex.norm_exp_ofReal (-B * ‖x‖ ^ 2)
  have hgint : Integrable (fun x : E k => Real.exp (-B * ‖x‖ ^ 2)) volume := by
    simpa [hnorm_eq] using hintcF.norm
  have hpt : ∀ x : E k, Real.exp (-B * ‖x‖ ^ 2) = phiR k X x := by
    intro x
    unfold phiR
    congr 1
    have hns : ‖((X : ℝ) ^ k)⁻¹ • x‖ ^ 2 = ((X : ℝ) ^ k)⁻¹ ^ 2 * ‖x‖ ^ 2 := by
      rw [norm_smul_sq_real (E k) ((X : ℝ) ^ k)⁻¹
        (inv_nonneg.mpr (pow_nonneg (by exact_mod_cast (Nat.zero_le X)) k)) x]
    dsimp [B, c]
    rw [hns]
    ring
  have hptf : (fun x : E k => Real.exp (-B * ‖x‖ ^ 2)) = fun x : E k => phiR k X x := by
    funext x
    exact hpt x
  rw [← hptf]
  exact hgint


/-- the real integral T = ∫ φR·|valSum|^{2s} -/
def Tint (k X s : ℕ) : ℝ := ∫ x : E k, phiR k X x * ‖valSum k X x‖ ^ (2 * s)

/-- gaussC is continuous in its argument -/
lemma gaussC_continuous (k : ℕ) : Continuous (fun v : E k => gaussC k v) := by
  unfold gaussC
  fun_prop

/-- the moment-curve character is continuous in the extension variable -/
lemma momChar_continuous (k : ℕ) (t : ℝ) : Continuous (fun x : E k => momChar k x t) := by
  unfold momChar
  fun_prop

/-- the value-tuple character is continuous in the extension variable -/
lemma valMomChar_continuous (k X s : ℕ) (u : Fin s → Fin X) :
    Continuous (fun x : E k => valMomChar k X x u) := by
  unfold valMomChar
  apply continuous_finset_prod
  intro r hr
  exact momChar_continuous k ((((u r).1 + 1 : ℕ) : ℝ) / X)

/-- each Gaussian·character term is integrable (dominated by the real φR) -/
lemma gauss_term_integrable (k X : ℕ) (hX : 1 ≤ X) {s : ℕ} (u v : Fin s → Fin X) :
    Integrable (fun x : E k =>
      gaussC k (((X : ℝ) ^ k)⁻¹ • x) * star (valMomChar k X x u) * valMomChar k X x v) volume := by
  refine Integrable.mono' (phiR_integrable k X hX) ?_ ?_
  · -- AEStronglyMeasurable: continuous
    apply Continuous.aestronglyMeasurable
    have hg : Continuous (fun x : E k => gaussC k (((X : ℝ) ^ k)⁻¹ • x)) := by
      unfold gaussC
      fun_prop
    have hu : Continuous (fun x : E k => star (valMomChar k X x u)) := by
      exact Continuous.star (valMomChar_continuous k X s u)
    have hv : Continuous (fun x : E k => valMomChar k X x v) := valMomChar_continuous k X s v
    exact (hg.mul hu).mul hv
  · filter_upwards with x
    exact gauss_char_integrand_norm_le k X hX u v x

/-- integral of the expansion equals the sum of the Gaussian term integrals -/
lemma integral_expansion_complex (k X s : ℕ) (hX : 1 ≤ X) :
    (∫ x : E k, gaussC k (((X : ℝ) ^ k)⁻¹ • x)
        * star (valSum k X x) ^ s * (valSum k X x) ^ s)
      = ∑ uv : (Fin s → Fin X) × (Fin s → Fin X),
          ∫ x : E k,
            gaussC k (((X : ℝ) ^ k)⁻¹ • x) * star (valMomChar k X x uv.1) * valMomChar k X x uv.2 := by
  have hpt : ∀ x : E k,
      gaussC k (((X : ℝ) ^ k)⁻¹ • x)
          * star (valSum k X x) ^ s * (valSum k X x) ^ s
        = ∑ uv : (Fin s → Fin X) × (Fin s → Fin X),
            gaussC k (((X : ℝ) ^ k)⁻¹ • x) * star (valMomChar k X x uv.1) * valMomChar k X x uv.2 := by
    intro x
    rw [mul_assoc]
    rw [expansion_eq k X s x]
    rw [Finset.mul_sum]
    simp only [mul_assoc]
  calc
    (∫ x : E k, gaussC k (((X : ℝ) ^ k)⁻¹ • x)
        * star (valSum k X x) ^ s * (valSum k X x) ^ s)
        = ∫ x : E k,
            ∑ uv : (Fin s → Fin X) × (Fin s → Fin X),
              gaussC k (((X : ℝ) ^ k)⁻¹ • x) * star (valMomChar k X x uv.1) * valMomChar k X x uv.2 := by
            refine integral_congr_ae ?_
            filter_upwards with x
            exact hpt x
    _ = ∑ uv : (Fin s → Fin X) × (Fin s → Fin X),
          ∫ x : E k,
            gaussC k (((X : ℝ) ^ k)⁻¹ • x) * star (valMomChar k X x uv.1) * valMomChar k X x uv.2 := by
          simpa using (integral_finsetSum (Finset.univ : Finset ((Fin s → Fin X) × (Fin s → Fin X)))
            (by intro uv huv; exact gauss_term_integrable k X hX uv.1 uv.2))

/-- the complex closed-form term value equals the coerced real `termVal` -/
lemma term_eval_eq_ofReal (k X : ℕ) (_hX : 1 ≤ X) {s : ℕ} (u v : Fin s → Fin X) :
    (((X : ℝ) ^ k) ^ k : ℂ)
        * cexp (-(π : ℂ) * ‖(X : ℝ) ^ k • (freq X k u - freq X k v)‖ ^ 2)
      = (termVal k X (u, v) : ℂ) := by
  unfold termVal
  have h1 : cexp (-(π : ℂ) * ‖(X : ℝ) ^ k • (freq X k u - freq X k v)‖ ^ 2)
      = (Real.exp (-π * ‖(X : ℝ) ^ k • (freq X k u - freq X k v)‖ ^ 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  calc
    (((X : ℝ) ^ k) ^ k : ℂ)
        * cexp (-(π : ℂ) * ‖(X : ℝ) ^ k • (freq X k u - freq X k v)‖ ^ 2)
        = (((X : ℝ) ^ k) ^ k : ℂ)
            * (Real.exp (-π * ‖(X : ℝ) ^ k • (freq X k u - freq X k v)‖ ^ 2) : ℂ) := by
            rw [h1]
    _ = ((((X : ℝ) ^ k) ^ k * Real.exp (-π * ‖(X : ℝ) ^ k • (freq X k u - freq X k v)‖ ^ 2) : ℝ) : ℂ) := by
            have hfac : (((X : ℝ) ^ k : ℂ) ^ k) = ((((X : ℝ) ^ k) ^ k : ℝ) : ℂ) := by
              push_cast
              ring
            rw [hfac, ← Complex.ofReal_mul]
    _ = (termVal k X (u, v) : ℂ) := by rfl

/-- the complex Gaussian integral of the full power equals the sum of closed terms -/
lemma expansion_integral (k X s : ℕ) (hX : 1 ≤ X) :
    (∫ x : E k, gaussC k (((X : ℝ) ^ k)⁻¹ • x)
        * star (valSum k X x) ^ s * (valSum k X x) ^ s)
      = ∑ uv : (Fin s → Fin X) × (Fin s → Fin X), (termVal k X uv : ℂ) := by
  calc
    (∫ x : E k, gaussC k (((X : ℝ) ^ k)⁻¹ • x)
        * star (valSum k X x) ^ s * (valSum k X x) ^ s)
        = ∑ uv : (Fin s → Fin X) × (Fin s → Fin X),
            ∫ x : E k,
              gaussC k (((X : ℝ) ^ k)⁻¹ • x) * star (valMomChar k X x uv.1) * valMomChar k X x uv.2 :=
            integral_expansion_complex k X s hX
    _ = ∑ uv : (Fin s → Fin X) × (Fin s → Fin X),
            (((X : ℝ) ^ k) ^ k : ℂ)
              * cexp (-(π : ℂ) * ‖(X : ℝ) ^ k • (freq X k uv.1 - freq X k uv.2)‖ ^ 2) := by
          apply Finset.sum_congr rfl
          intro uv huv
          exact term_eval k X hX uv.1 uv.2
    _ = ∑ uv : (Fin s → Fin X) × (Fin s → Fin X), (termVal k X uv : ℂ) := by
          apply Finset.sum_congr rfl
          intro uv huv
          exact term_eval_eq_ofReal k X hX uv.1 uv.2



/-- pointwise: the Gaussian-weighted full power equals `φR·(‖f‖)^{2s}` (complex) -/
lemma gauss_scaled_valSum_eq (k X s : ℕ) (x : E k) :
    gaussC k (((X : ℝ) ^ k)⁻¹ • x) * star (valSum k X x) ^ s * (valSum k X x) ^ s
      = (phiR k X x : ℂ) * (‖valSum k X x‖ : ℂ) ^ (2 * s) := by
  calc
    gaussC k (((X : ℝ) ^ k)⁻¹ • x) * star (valSum k X x) ^ s * (valSum k X x) ^ s
        = gaussC k (((X : ℝ) ^ k)⁻¹ • x) * (star (valSum k X x) ^ s * (valSum k X x) ^ s) := by
            rw [mul_assoc]
    _ = gaussC k (((X : ℝ) ^ k)⁻¹ • x) * ((‖valSum k X x‖ ^ (2 * s) : ℝ) : ℂ) := by
            rw [star_valSum_pow_mul k X s x]
    _ = gaussC k (((X : ℝ) ^ k)⁻¹ • x) * (‖valSum k X x‖ : ℂ) ^ (2 * s) := by
            rw [Complex.ofReal_pow]
    _ = (phiR k X x : ℂ) * (‖valSum k X x‖ : ℂ) ^ (2 * s) := by
            rw [gaussC_scaled_eq_ofReal k X x]

/-- commutation: integral of the pointwise coercion equals the coerced integral
(written with `Complex.ofRealLI` to avoid coercion insertion inside the integral) -/
lemma integral_coe_ofReal {k : ℕ} (φ : E k → ℝ) :
    (∫ x : E k, (φ x : ℂ)) = Complex.ofRealLI (∫ x : E k, φ x) := by
  rw [← Complex.ofRealLI.integral_comp_comm]
  refine integral_congr_ae ?_
  filter_upwards with x
  simp [Complex.ofRealLI_apply]

/-- the complex Gaussian integral of the full power equals the coerced real `Tint` -/
lemma Tint_complex_eq (k X s : ℕ) (hX : 1 ≤ X) :
    (∫ x : E k, gaussC k (((X : ℝ) ^ k)⁻¹ • x)
        * star (valSum k X x) ^ s * (valSum k X x) ^ s)
      = (Tint k X s : ℂ) := by
  let φ : E k → ℝ := fun x => phiR k X x * ‖valSum k X x‖ ^ (2 * s)
  calc
    (∫ x : E k, gaussC k (((X : ℝ) ^ k)⁻¹ • x)
        * star (valSum k X x) ^ s * (valSum k X x) ^ s)
        = ∫ x : E k, (φ x : ℂ) := by
            refine integral_congr_ae ?_
            filter_upwards with x
            calc
              gaussC k (((X : ℝ) ^ k)⁻¹ • x)
                  * star (valSum k X x) ^ s * (valSum k X x) ^ s
                  = (phiR k X x : ℂ) * (‖valSum k X x‖ : ℂ) ^ (2 * s) := gauss_scaled_valSum_eq k X s x
              _ = (φ x : ℂ) := by
                    dsimp [φ]
                    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
    _ = Complex.ofRealLI (∫ x : E k, φ x) := integral_coe_ofReal φ
    _ = (Tint k X s : ℂ) := by
          unfold Tint
          dsimp [φ]



/-- each closed term is nonnegative -/
lemma termVal_nonneg (k X : ℕ) {s : ℕ} (uv : (Fin s → Fin X) × (Fin s → Fin X)) :
    0 ≤ termVal k X uv := by
  unfold termVal
  positivity

/-- real identity: `Tint` equals the sum over all value-pairs of the closed terms -/
lemma Tint_eq_sum_terms (k X s : ℕ) (hX : 1 ≤ X) :
    Tint k X s = ∑ uv : (Fin s → Fin X) × (Fin s → Fin X), termVal k X uv := by
  have hc : ((Tint k X s : ℝ) : ℂ) =
      ((∑ uv : (Fin s → Fin X) × (Fin s → Fin X), termVal k X uv : ℝ) : ℂ) := by
    calc
      ((Tint k X s : ℝ) : ℂ)
          = ∫ x : E k, gaussC k (((X : ℝ) ^ k)⁻¹ • x)
              * star (valSum k X x) ^ s * (valSum k X x) ^ s := (Tint_complex_eq k X s hX).symm
      _ = ∑ uv : (Fin s → Fin X) × (Fin s → Fin X), (termVal k X uv : ℂ) := expansion_integral k X s hX
      _ = ((∑ uv : (Fin s → Fin X) × (Fin s → Fin X), termVal k X uv : ℝ) : ℂ) := by
            simp
  exact Complex.ofReal_inj.mp hc

/-! ## Term lower bound: coordinates of the scaled frequency difference -/

lemma fin_val_add_one_le (k : ℕ) (j : Fin k) : j.val + 1 ≤ k := by
  have hj := j.isLt
  omega

lemma freq_coord (X k : ℕ) {s : ℕ} (u : Fin s → Fin X) (j : Fin k) :
    (freq X k u).ofLp j = ((Msum X (j.val + 1) u : ℕ) : ℝ) / (X : ℝ) ^ (j.val + 1) := by
  unfold freq Msum
  simp [Finset.sum_div]

/-- the ℤ-valued moment difference, as a real, is the real difference of the natural moments -/
lemma zmom_nat_diff_cast (a b : ℕ) :
    ((((a : ℤ) - (b : ℤ) : ℤ) : ℝ)) = (a : ℝ) - (b : ℝ) := by
  norm_num

/-- coordinate of the scaled frequency-difference vector (real-moment form) -/
lemma scaled_freq_coord_real (X k : ℕ) (hX : 1 ≤ X) {s : ℕ} (u v : Fin s → Fin X) (j : Fin k) :
    (((X : ℝ) ^ k • (freq X k u - freq X k v)).ofLp j)
      = (X : ℝ) ^ (k - (j.val + 1)) * ((Msum X (j.val + 1) u : ℝ) - (Msum X (j.val + 1) v : ℝ)) := by
  simp [freq_coord]
  have hXne : (X : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hX))
  have hd : j.val + 1 ≤ k := fin_val_add_one_le k j
  let a : ℝ := (Msum X (j.val + 1) u : ℝ)
  let b : ℝ := (Msum X (j.val + 1) v : ℝ)
  let c : ℝ := (X : ℝ) ^ (j.val + 1)
  have hc : c ≠ 0 := by dsimp [c]; exact pow_ne_zero _ hXne
  change (X : ℝ) ^ k * (a / c - b / c) = (X : ℝ) ^ (k - (j.val + 1)) * (a - b)
  calc
    (X : ℝ) ^ k * (a / c - b / c) = (X : ℝ) ^ k * ((a - b) / c) := by rw [sub_div]
    _ = ((X : ℝ) ^ k / c) * (a - b) := by
          field_simp [hc]
    _ = (X : ℝ) ^ (k - (j.val + 1)) * (a - b) := by
          congr 1
          dsimp [c]
          field_simp [hXne]
          rw [← pow_add]
          congr 1
          omega

/-- the same coordinate in ℤ-moment form (matching `goodFin`) -/
lemma scaled_freq_coord (X k : ℕ) (hX : 1 ≤ X) {s : ℕ} (u v : Fin s → Fin X) (j : Fin k) :
    (((X : ℝ) ^ k • (freq X k u - freq X k v)).ofLp j)
      = (X : ℝ) ^ (k - (j.val + 1))
          * ((((Msum X (j.val + 1) u : ℤ) - (Msum X (j.val + 1) v : ℤ) : ℤ) : ℝ)) := by
  rw [scaled_freq_coord_real X k hX u v j]
  congr 2
  rw [zmom_nat_diff_cast]

/-- the separated bound is a nonnegative real power of X -/
lemma sepBound_nonneg (X j k : ℕ) : 0 ≤ sepBound X j k := by
  unfold sepBound
  exact Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le X)) _

/-- product identity `X^{k-d}·X^{d-k} = 1` (real exponents) -/
lemma rpow_sub_pow_one (X : ℝ) (hXpos : 0 < X) (d k : ℕ) :
    (X : ℝ) ^ ((k : ℝ) - (d : ℝ)) * (X : ℝ) ^ ((d : ℝ) - (k : ℝ)) = 1 := by
  rw [← Real.rpow_add hXpos]
  have : (k : ℝ) - (d : ℝ) + ((d : ℝ) - (k : ℝ)) = 0 := by ring
  rw [this]
  simp

/-- `X^{k-d}·X^{d-k} = 1` with the first factor a natural power (d ≤ k) -/
lemma pow_sub_mul_rpow_sub (X : ℝ) (hXpos : 0 < X) (d k : ℕ) (hd : d ≤ k) :
    (X : ℝ) ^ (k - d) * (X : ℝ) ^ ((d : ℝ) - (k : ℝ)) = 1 := by
  have hfirst : (X : ℝ) ^ (k - d) = (X : ℝ) ^ ((k : ℝ) - (d : ℝ)) := by
    rw [← Real.rpow_natCast]
    congr 1
    exact Nat.cast_sub hd
  rw [hfirst]
  exact rpow_sub_pow_one X hXpos d k

/-- key coordinate bound: for `goodFin` pairs each scaled-frequency coordinate is ≤ 1 in abs -/
lemma goodFin_coord_bound (s k X : ℕ) (hX : 1 ≤ X) (uv : (Fin s → Fin X) × (Fin s → Fin X))
    (hgood : goodFin s k X uv) (j : Fin k) :
    |(((X : ℝ) ^ k • (freq X k uv.1 - freq X k uv.2)).ofLp j)| ≤ 1 := by
  let d : ℕ := j.val + 1
  have hd1 : 1 ≤ d := by dsimp [d]; omega
  have hdk : d ≤ k := by dsimp [d]; exact fin_val_add_one_le k j
  have hz := hgood d hd1 hdk
  have hz' : |(((Msum X d uv.1 : ℝ) - (Msum X d uv.2 : ℝ)))| ≤ sepBound X d k := by
    simpa [zmom_nat_diff_cast, d] using hz
  have hXa : 0 ≤ (X : ℝ) ^ (k - d) := pow_nonneg (by exact_mod_cast (Nat.zero_le X)) _
  have hmul : (X : ℝ) ^ (k - d) * |(((Msum X d uv.1 : ℝ) - (Msum X d uv.2 : ℝ)))|
      ≤ (X : ℝ) ^ (k - d) * sepBound X d k := by
    exact mul_le_mul_of_nonneg_left hz' hXa
  have hZeq : |((X : ℝ) ^ (k - d) * ((((Msum X d uv.1 : ℤ) - (Msum X d uv.2 : ℤ) : ℤ) : ℝ)))|
      = (X : ℝ) ^ (k - d) * |(((Msum X d uv.1 : ℝ) - (Msum X d uv.2 : ℝ)))| := by
    rw [abs_mul, abs_of_nonneg hXa]
    congr 1
    rw [zmom_nat_diff_cast]
  have hcoord : (((X : ℝ) ^ k • (freq X k uv.1 - freq X k uv.2)).ofLp j)
      = (X : ℝ) ^ (k - d) * ((((Msum X d uv.1 : ℤ) - (Msum X d uv.2 : ℤ) : ℤ) : ℝ)) := by
    simpa [d] using (scaled_freq_coord X k hX uv.1 uv.2 j)
  have hprod : (X : ℝ) ^ (k - d) * sepBound X d k = 1 := by
    unfold sepBound
    exact pow_sub_mul_rpow_sub (X : ℝ) (by exact_mod_cast (lt_of_lt_of_le zero_lt_one hX)) d k hdk
  calc
    |(((X : ℝ) ^ k • (freq X k uv.1 - freq X k uv.2)).ofLp j)|
        = (X : ℝ) ^ (k - d) * |(((Msum X d uv.1 : ℝ) - (Msum X d uv.2 : ℝ)))| := by
            rw [hcoord, hZeq]
    _ ≤ (X : ℝ) ^ (k - d) * sepBound X d k := hmul
    _ = 1 := hprod
    _ ≤ 1 := le_rfl



/-! ## Item 2: `goodFin` pairs ↔ `Jsep` pairs (counting injection) -/

/-- value in `[1,X]` of an index `i : Fin X`: `i.val + 1` -/
def toValue (X : ℕ) (i : Fin X) : Finset.Icc 1 X :=
  ⟨i.val + 1, by
    rw [Finset.mem_Icc]
    constructor
    · omega
    · exact Nat.succ_le_of_lt i.isLt⟩

/-- the index of a value `v ∈ [1,X]`: `v.val − 1` -/
def toIndex (X : ℕ) (v : Finset.Icc 1 X) : Fin X :=
  ⟨v.val - 1, by
    have hv := v.property
    rw [Finset.mem_Icc] at hv
    omega⟩

/-- `toValue` and `toIndex` are mutually inverse on values -/
lemma toIndex_toValue (X : ℕ) (i : Fin X) : toIndex X (toValue X i) = i := by
  apply Fin.ext
  simp [toIndex, toValue]

/-- `toIndex` and `toValue` are mutually inverse on values -/
lemma toValue_toIndex (X : ℕ) (v : Finset.Icc 1 X) : toValue X (toIndex X v) = v := by
  apply Subtype.ext
  have hv : 1 ≤ v.val ∧ v.val ≤ X := Finset.mem_Icc.mp v.property
  simp [toValue, toIndex]
  omega

/-- pointwise application of `toValue` to tuples -/
def toValueTuple (X : ℕ) {s : ℕ} (u : Fin s → Fin X) : Fin s → Finset.Icc 1 X :=
  fun r => toValue X (u r)

/-- pointwise application of `toIndex` to tuples -/
def toIndexTuple (X : ℕ) {s : ℕ} (x : Fin s → Finset.Icc 1 X) : Fin s → Fin X :=
  fun r => toIndex X (x r)

/-- moment of the value tuple equals `Msum` of the index tuple -/
lemma zmom_toValueTuple_eq_Msum (X j : ℕ) {s : ℕ} (u : Fin s → Fin X) :
    zmom j (toValueTuple X u) = (Msum X j u : ℤ) := by
  rfl

/-- moment of the index tuple of a value tuple is the original moment -/
lemma Msum_toIndexTuple_eq_zmom (X j : ℕ) {s : ℕ} (x : Fin s → Finset.Icc 1 X) :
    (Msum X j (toIndexTuple X x) : ℤ) = zmom j x := by
  unfold Msum zmom toIndexTuple
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  have hv : 1 ≤ (x r).val := (Finset.mem_Icc.mp (x r).property).1
  have hval : (toIndex X (x r)).val + 1 = (x r).val := by
    simp [toIndex]
    omega
  rw [hval]

/-- `toIndex` is injective -/
lemma toIndex_injective (X : ℕ) : Function.Injective (toIndex X) := by
  intro v w hvw
  have h' := congrArg (toValue X) hvw
  simpa [toValue_toIndex] using h'

/-- `toIndexTuple` is injective -/
lemma toIndexTuple_injective (X : ℕ) {s : ℕ} :
    Function.Injective (toIndexTuple X : (Fin s → Finset.Icc 1 X) → (Fin s → Fin X)) := by
  intro u v huv
  funext r
  have hc := congrFun huv r
  have h' := congrArg (toValue X) hc
  simpa [toIndexTuple, toValue_toIndex] using h'

/-- the pair preimage map is injective -/
lemma toIndexPair_injective (X : ℕ) {s : ℕ} :
    Function.Injective (fun p : PairSpace s X => (toIndexTuple X p.1, toIndexTuple X p.2)) := by
  intro p q hpq
  have h1 := congrArg Prod.fst hpq
  have h2 := congrArg Prod.snd hpq
  apply Prod.ext
  · exact toIndexTuple_injective X h1
  · exact toIndexTuple_injective X h2

/-- `Jsep` counts at most the `goodFin` index pairs -/
lemma goodFin_card_ge_Jsep (s k X : ℕ) (hX : 1 ≤ X) :
    (Jsep s k X : ℝ) ≤ ((Finset.univ.filter (fun uv : (Fin s → Fin X) × (Fin s → Fin X) => goodFin s k X uv)).card : ℝ) := by
  classical
  unfold Jsep
  let B : Type := (Fin s → Fin X) × (Fin s → Fin X)
  let sF : Finset (PairSpace s X) := Finset.univ.filter (fun p : PairSpace s X =>
    ∀ j : ℕ, 1 ≤ j → j ≤ k → |((zmom j p.1 - zmom j p.2) : ℝ)| ≤ sepBound X j k)
  let tF : Finset B := Finset.univ.filter (fun uv : B => goodFin s k X uv)
  let f : PairSpace s X → B := fun p => (toIndexTuple X p.1, toIndexTuple X p.2)
  have hfinj : Function.Injective f := by
    dsimp [f]
    exact toIndexPair_injective X
  have hmap : Set.MapsTo f ↑sF ↑tF := by
    intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    rw [Finset.mem_coe, Finset.mem_filter]
    rcases hp with ⟨_, hcond⟩
    constructor
    · simp
    · intro j hj1 hjk
      have hc := hcond j hj1 hjk
      rw [← Msum_toIndexTuple_eq_zmom X j p.1, ← Msum_toIndexTuple_eq_zmom X j p.2] at hc
      exact hc
  have hcard := Finset.card_le_card_of_injOn (s := sF) (t := tF) f hmap (hfinj.injOn)
  have hcast : (sF.card : ℝ) ≤ (tF.card : ℝ) := by exact_mod_cast hcard
  simpa [sF, tF] using hcast



/-! ## Item 3: term lower bound, item 4: `lower_bound_Jsep` -/

/-- `x^2 ≤ 1` from `|x| ≤ 1` -/
lemma sq_le_one_of_abs_le_one {x : ℝ} (h : |x| ≤ 1) : x ^ 2 ≤ 1 := by
  rw [← sq_abs, pow_two]
  calc
    |x| * |x| ≤ 1 * 1 := mul_le_mul h h (abs_nonneg x) (by norm_num)
    _ = 1 := by norm_num

/-- for `goodFin` pairs the scaled frequency-difference vector has norm-square ≤ k -/
lemma goodFin_norm_sq_le (s k X : ℕ) (hX : 1 ≤ X) (uv : (Fin s → Fin X) × (Fin s → Fin X))
    (hgood : goodFin s k X uv) :
    ‖(X : ℝ) ^ k • (freq X k uv.1 - freq X k uv.2)‖ ^ 2 ≤ (k : ℝ) := by
  rw [norm_sq_coord_sum]
  calc
    (∑ j : Fin k, (((X : ℝ) ^ k • (freq X k uv.1 - freq X k uv.2)) j) ^ 2 : ℝ)
        ≤ (∑ j : Fin k, (1 : ℝ) : ℝ) := by
          apply Finset.sum_le_sum
          intro j hj
          have hc := goodFin_coord_bound s k X hX uv hgood j
          exact sq_le_one_of_abs_le_one hc
    _ = (k : ℝ) := by simp

/-- lower bound of a single closed term for good pairs -/
lemma term_lower_bound (s k X : ℕ) (hX : 1 ≤ X) (uv : (Fin s → Fin X) × (Fin s → Fin X))
    (hgood : goodFin s k X uv) :
    ((X : ℝ) ^ k) ^ k * Real.exp (-π * (k : ℝ)) ≤ termVal k X uv := by
  unfold termVal
  have hnorm := goodFin_norm_sq_le s k X hX uv hgood
  let w : E k := (X : ℝ) ^ k • (freq X k uv.1 - freq X k uv.2)
  have hexp : Real.exp (-π * (k : ℝ)) ≤ Real.exp (-π * ‖w‖ ^ 2) := by
    apply Real.exp_le_exp.mpr
    have h1 : π * ‖w‖ ^ 2 ≤ π * (k : ℝ) := mul_le_mul_of_nonneg_left hnorm (le_of_lt Real.pi_pos)
    linarith
  calc
    ((X : ℝ) ^ k) ^ k * Real.exp (-π * (k : ℝ))
        ≤ ((X : ℝ) ^ k) ^ k * Real.exp (-π * ‖w‖ ^ 2) := by
            exact mul_le_mul_of_nonneg_left hexp (pow_nonneg (pow_nonneg (by exact_mod_cast (Nat.zero_le X)) k) k)
    _ = ((X : ℝ) ^ k) ^ k * Real.exp (-π * ‖(X : ℝ) ^ k • (freq X k uv.1 - freq X k uv.2)‖ ^ 2) := by
            rfl



/-- all `termVal` terms are ≥ the constant `c` on `goodFin` pairs, summed over the filter -/
lemma sum_good_ge_sum_const (s k X : ℕ) (hX : 1 ≤ X) (c : ℝ) (hc : ∀ uv : (Fin s → Fin X) × (Fin s → Fin X),
    goodFin s k X uv → c ≤ termVal k X uv) :
    (∑ uv : (Fin s → Fin X) × (Fin s → Fin X),
        if goodFin s k X uv then c else 0)
      ≤ ∑ uv : (Fin s → Fin X) × (Fin s → Fin X), termVal k X uv := by
  apply Finset.sum_le_sum
  intro uv huv
  by_cases hg : goodFin s k X uv
  · simp [hg, hc uv hg]
  · simp [hg, termVal_nonneg k X uv]

/-- the sum of `termVal` over all pairs is at least the sum of the constant over good pairs -/
lemma Tint_ge_const_good (s k X : ℕ) (hX : 1 ≤ X) (c : ℝ)
    (hc : ∀ uv : (Fin s → Fin X) × (Fin s → Fin X), goodFin s k X uv → c ≤ termVal k X uv) :
    (∑ uv : (Fin s → Fin X) × (Fin s → Fin X), if goodFin s k X uv then c else 0)
      ≤ Tint k X s := by
  calc
    (∑ uv : (Fin s → Fin X) × (Fin s → Fin X), if goodFin s k X uv then c else 0)
        ≤ ∑ uv : (Fin s → Fin X) × (Fin s → Fin X), termVal k X uv := sum_good_ge_sum_const s k X hX c hc
    _ = Tint k X s := (Tint_eq_sum_terms k X s hX).symm

/-- the indicator sum of the constant over good pairs equals `(number of good pairs)·c` -/
lemma sum_const_good_eq (s k X : ℕ) (c : ℝ) :
    (∑ uv : (Fin s → Fin X) × (Fin s → Fin X), if goodFin s k X uv then c else 0)
      = (((Finset.univ.filter (fun uv : (Fin s → Fin X) × (Fin s → Fin X) => goodFin s k X uv)).card : ℕ) : ℝ) * c := by
  classical
  rw [← Finset.sum_filter (s := (Finset.univ : Finset ((Fin s → Fin X) × (Fin s → Fin X))))
    (p := fun uv : (Fin s → Fin X) × (Fin s → Fin X) => goodFin s k X uv) (f := fun _ : (Fin s → Fin X) × (Fin s → Fin X) => c)]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- the lower bound: many `goodFin` terms contribute, giving
`Jsep·X^{k·k} ≤ e^{πk}·Tint` -/
lemma lower_bound_Jsep (s k X : ℕ) (hX : 1 ≤ X) :
    (Jsep s k X : ℝ) * ((X : ℝ) ^ k) ^ k ≤ Real.exp (π * (k : ℝ)) * Tint k X s := by
  let c : ℝ := ((X : ℝ) ^ k) ^ k * Real.exp (-π * (k : ℝ))
  have hc0 : 0 ≤ c := by
    dsimp [c]
    positivity
  have hc_le : ∀ uv : (Fin s → Fin X) × (Fin s → Fin X),
      goodFin s k X uv → c ≤ termVal k X uv := by
    intro uv hg
    dsimp [c]
    exact term_lower_bound s k X hX uv hg
  have hge : (Jsep s k X : ℝ) ≤
      ((Finset.univ.filter (fun uv : (Fin s → Fin X) × (Fin s → Fin X) => goodFin s k X uv)).card : ℝ) := by
    exact goodFin_card_ge_Jsep s k X hX
  have hJc : (Jsep s k X : ℝ) * c ≤ Tint k X s := by
    calc
      (Jsep s k X : ℝ) * c
          ≤ ((Finset.univ.filter (fun uv : (Fin s → Fin X) × (Fin s → Fin X) => goodFin s k X uv)).card : ℝ) * c := by
              exact mul_le_mul_of_nonneg_right hge hc0
      _ = (∑ uv : (Fin s → Fin X) × (Fin s → Fin X), if goodFin s k X uv then c else 0) := by
              rw [sum_const_good_eq]
      _ ≤ Tint k X s := Tint_ge_const_good s k X hX c hc_le
  have hstep : Real.exp (π * (k : ℝ)) * ((Jsep s k X : ℝ) * c) ≤
      Real.exp (π * (k : ℝ)) * Tint k X s := by
    exact mul_le_mul_of_nonneg_left hJc (Real.exp_nonneg _)
  have hEA : Real.exp (π * (k : ℝ)) * Real.exp (-π * (k : ℝ)) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    (Jsep s k X : ℝ) * ((X : ℝ) ^ k) ^ k
        = (Jsep s k X : ℝ) * ((X : ℝ) ^ k) ^ k
            * (Real.exp (π * (k : ℝ)) * Real.exp (-π * (k : ℝ))) := by
            rw [hEA]
            ring
    _ = Real.exp (π * (k : ℝ)) * ((Jsep s k X : ℝ) * (((X : ℝ) ^ k) ^ k * Real.exp (-π * (k : ℝ)))) := by
            ring
    _ = Real.exp (π * (k : ℝ)) * ((Jsep s k X : ℝ) * c) := by
            rfl
    _ ≤ Real.exp (π * (k : ℝ)) * Tint k X s := hstep



/-! ## Item 5: the Gaussian weight is dominated by the ball weight -/

/-- `‖c⁻¹•x‖ = ‖x‖/c` for `c = X^k > 0` -/
lemma norm_inv_smul_eq_div (k X : ℕ) (hX : 1 ≤ X) (x : E k) :
    ‖((X : ℝ) ^ k)⁻¹ • x‖ = ‖x‖ / (X : ℝ) ^ k := by
  rw [norm_smul]
  have hc : 0 < (X : ℝ) ^ k := pow_pos (by exact_mod_cast (lt_of_lt_of_le zero_lt_one hX)) k
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hc))]
  field_simp [ne_of_gt hc]

/-- the ball weight at `x` against `B(0,X^k)` in terms of `y = X^{-k}•x` -/
lemma ballWeight_zero_smul (k X : ℕ) (hX : 1 ≤ X) (x : E k) :
    ballWeight k 0 ((X : ℝ) ^ k) x = ((1 + ‖((X : ℝ) ^ k)⁻¹ • x‖) ^ (100 * k))⁻¹ := by
  unfold ballWeight
  have hdiv : ‖x‖ / (X : ℝ) ^ k = ‖((X : ℝ) ^ k)⁻¹ • x‖ := (norm_inv_smul_eq_div k X hX x).symm
  rw [sub_zero, hdiv]

/-- the Gaussian weight `φR` is bounded by a constant times the ball weight,
uniformly in `X ≥ 1` and `x` (BDG's Schwartz decay) -/
lemma phiR_le_const_ballWeight (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X → ∀ x : E k,
      phiR k X x ≤ C * ballWeight k 0 ((X : ℝ) ^ k) x := by
  rcases Commons.Analysis.Real.exp_neg_pi_sq_mul_poly_bounded k with ⟨C0, hC0, hb⟩
  refine ⟨C0, hC0, ?_⟩
  intro X hX x
  let y : E k := ((X : ℝ) ^ k)⁻¹ • x
  have hy : 0 ≤ ‖y‖ := norm_nonneg _
  have hmain := hb ‖y‖ hy
  have hpos : 0 < (1 + ‖y‖) ^ (100 * k) := pow_pos (by nlinarith) _
  have h1 : Real.exp (-π * ‖y‖ ^ 2) ≤ C0 * ballWeight k 0 ((X : ℝ) ^ k) x := by
    rw [ballWeight_zero_smul k X hX x]
    dsimp [y]
    have hdiv : C0 * ((1 + ‖((X : ℝ) ^ k)⁻¹ • x‖) ^ (100 * k))⁻¹
        = C0 / (1 + ‖((X : ℝ) ^ k)⁻¹ • x‖) ^ (100 * k) := by ring
    rw [hdiv]
    exact (le_div_iff₀ hpos).mpr hmain
  have hphi : phiR k X x = Real.exp (-π * ‖y‖ ^ 2) := by
    dsimp [phiR, y]
  rw [hphi]
  exact h1



/-! ## Item 6: applying BDG discrete restriction (`thm41_upper_bound`) -/

/-- the separated points `t_i = (i+1)/X` (BDG's integer-point set) -/
lemma separated_succ_div (X : ℕ) (hX : 1 ≤ X) :
    Separated X (fun i : Fin X => (((i.1 + 1 : ℕ) : ℝ) / X)) := by
  intro i
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hX)
  constructor
  · change (i.1 : ℝ) / X < (((i.1 + 1 : ℕ) : ℝ)) / X
    rw [Nat.cast_add, Nat.cast_one]
    field_simp [ne_of_gt hXpos]
    linarith
  · change (((i.1 + 1 : ℕ) : ℝ) / X) ≤ ((i.1 : ℝ) + 1) / X
    rw [Nat.cast_add, Nat.cast_one]

/-- the trivial pointwise bound for `valSum`: `‖valSum‖ ≤ X` -/
lemma valSum_norm_bound (k X : ℕ) (x : E k) : ‖valSum k X x‖ ≤ (X : ℝ) := by
  have h := sepCharSum_trivial_bound k (fun _ : Fin X => (1 : ℂ)) (fun i : Fin X => (((i.1 + 1 : ℕ) : ℝ) / X)) x
  rw [valSum_eq_sepCharSum_ones k X x]
  calc
    ‖sepCharSum k (fun _ : Fin X => (1 : ℂ)) (fun i : Fin X => (((i.1 + 1 : ℕ) : ℝ) / X)) x‖
        ≤ Real.sqrt (X : ℝ) * Real.sqrt (∑ i : Fin X, ‖(1 : ℂ)‖ ^ 2) := h
    _ = X := by
          simp

/-- the `Lᵖ`-power integrand of `valSum` against the ball weight is integrable
(`p = 2s ≥ 0`, `k ≥ 1`, `X ≥ 1`) -/
lemma valSum_wLp_integrable (s k X : ℕ) (hk : 1 ≤ k) (hX : 1 ≤ X) :
    Integrable (fun x : E k =>
      ‖valSum k X x‖ ^ (((2 * s : ℕ) : ℝ)) * ballWeight k 0 ((X : ℝ) ^ k) x) volume := by
  have hR : 0 < (X : ℝ) ^ k := pow_pos (by exact_mod_cast (lt_of_lt_of_le zero_lt_one hX)) k
  have h1 := sepCharSum_wLp_integrable k hk (fun _ : Fin X => (1 : ℂ))
    (fun i : Fin X => (((i.1 + 1 : ℕ) : ℝ) / X)) (show 0 ≤ ((2 * s : ℕ) : ℝ) by positivity) hR (0 : E k)
  have hpt : (fun x : E k => ‖sepCharSum k (fun _ : Fin X => (1 : ℂ))
        (fun i : Fin X => (((i.1 + 1 : ℕ) : ℝ) / X)) x‖ ^ (((2 * s : ℕ) : ℝ)) * ballWeight k 0 ((X : ℝ) ^ k) x)
      = fun x : E k => ‖valSum k X x‖ ^ (((2 * s : ℕ) : ℝ)) * ballWeight k 0 ((X : ℝ) ^ k) x := by
    funext x
    rw [valSum_eq_sepCharSum_ones k X x]
  rw [← hpt]
  exact h1



/-- `Tint` is bounded by a constant times the ball-weight `Lᵖ`-power (`p = 2s`) -/
lemma Tint_le_const_wLp (s k X : ℕ) (hk : 1 ≤ k) (hX : 1 ≤ X) (Cφ : ℝ) (hCφ0 : 0 < Cφ)
    (hφ : ∀ x : E k, phiR k X x ≤ Cφ * ballWeight k 0 ((X : ℝ) ^ k) x) :
    Tint k X s ≤ Cφ * wLpPow k 0 ((X : ℝ) ^ k) (((2 * s : ℕ) : ℝ)) (valSum k X) := by
  let f : E k → ℂ := valSum k X
  let g : E k → ℝ := fun x => (Cφ * ballWeight k 0 ((X : ℝ) ^ k) x) * ‖f x‖ ^ (((2 * s : ℕ) : ℝ))
  have hf1 : 0 ≤ᵐ[volume] (fun x : E k => phiR k X x * ‖f x‖ ^ (2 * s)) := by
    filter_upwards with x
    exact mul_nonneg (phiR_nonneg k X x) (pow_nonneg (norm_nonneg _) _)
  have hle : (fun x : E k => phiR k X x * ‖f x‖ ^ (2 * s)) ≤ᵐ[volume] g := by
    filter_upwards with x
    dsimp [f, g]
    have hn : ‖valSum k X x‖ ^ (2 * s) = ‖valSum k X x‖ ^ (((2 * s : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast]
    calc
      phiR k X x * ‖valSum k X x‖ ^ (2 * s)
          ≤ (Cφ * ballWeight k 0 ((X : ℝ) ^ k) x) * ‖valSum k X x‖ ^ (2 * s) := by
              exact mul_le_mul_of_nonneg_right (hφ x) (pow_nonneg (norm_nonneg _) _)
      _ = (Cφ * ballWeight k 0 ((X : ℝ) ^ k) x) * ‖valSum k X x‖ ^ (((2 * s : ℕ) : ℝ)) := by rw [hn]
  have hgi : Integrable g volume := by
    dsimp [g, f]
    have hi : Integrable (fun x : E k => Cφ * (‖valSum k X x‖ ^ (((2 * s : ℕ) : ℝ)) * ballWeight k 0 ((X : ℝ) ^ k) x)) volume :=
      (valSum_wLp_integrable s k X hk hX).const_mul Cφ
    exact hi.congr (by
      filter_upwards with x
      ring)
  have hmain := MeasureTheory.integral_mono_of_nonneg hf1 hgi hle
  -- hmain : ∫(φR·‖f‖^{2s}) ≤ ∫ g = ∫ (Cφ·w·‖f‖^p)
  calc
    Tint k X s
        = ∫ x : E k, phiR k X x * ‖valSum k X x‖ ^ (2 * s) := by rfl
    _ ≤ ∫ x : E k, (Cφ * ballWeight k 0 ((X : ℝ) ^ k) x) * ‖valSum k X x‖ ^ (((2 * s : ℕ) : ℝ)) := hmain
    _ = Cφ * ∫ x : E k, ballWeight k 0 ((X : ℝ) ^ k) x * ‖valSum k X x‖ ^ (((2 * s : ℕ) : ℝ)) := by
          have hcgr : (∫ x : E k, (Cφ * ballWeight k 0 ((X : ℝ) ^ k) x) * ‖valSum k X x‖ ^ (((2 * s : ℕ) : ℝ)))
              = ∫ x : E k, Cφ * (ballWeight k 0 ((X : ℝ) ^ k) x * ‖valSum k X x‖ ^ (((2 * s : ℕ) : ℝ))) := by
                refine integral_congr_ae ?_
                filter_upwards with x
                ring
          rw [hcgr]
          rw [integral_const_mul]
    _ = Cφ * wLpPow k 0 ((X : ℝ) ^ k) (((2 * s : ℕ) : ℝ)) (valSum k X) := by
          unfold wLpPow
          congr 1
          refine integral_congr_ae ?_
          filter_upwards with x
          ring



/-- raising a `1/p`-power bound -/
lemma le_of_rpow_le_rpow {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 < p)
    (h : a ^ (1 / p) ≤ b) : a ≤ b ^ p := by
  have h1 : 0 ≤ a ^ (1 / p) := Real.rpow_nonneg ha (1 / p)
  have h2 : (a ^ (1 / p)) ^ p ≤ b ^ p := Real.rpow_le_rpow h1 h (le_of_lt hp)
  have h3 : (a ^ (1 / p)) ^ p = a := by
    rw [← Real.rpow_mul ha (1 / p) p]
    have hpp : (1 / p) * p = 1 := by field_simp [ne_of_gt hp]
    rw [hpp, Real.rpow_one]
  rwa [h3] at h2

/-- the averaged weighted power of `valSum` equals that of the separated character sum -/
lemma wLpPowAvg_valSum_eq_sepCharSum (k X : ℕ) (p : ℝ) :
    wLpPowAvg k 0 ((X : ℝ) ^ k) p (valSum k X)
      = wLpPowAvg k 0 ((X : ℝ) ^ k) p
          (sepCharSum k (fun _ : Fin X => (1 : ℂ)) (fun i : Fin X => (((i.1 + 1 : ℕ) : ℝ) / X))) := by
  unfold wLpPowAvg wLpPow
  congr 1
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [valSum_eq_sepCharSum_ones k X x]

/-- `Cd`-bound instance of the discrete restriction for `valSum` -/
lemma bdg_valSum_bound (s k : ℕ) (hs : 1 ≤ s) (hk : 1 ≤ k) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
      (wLpPowAvg k 0 ((X : ℝ) ^ k) (((2 * s : ℕ) : ℝ)) (valSum k X))
          ^ (1 / (((2 * s : ℕ) : ℝ)))
        ≤ C * Real.sqrt (X : ℝ) * ((X : ℝ) ^ ε₀ + (X : ℝ) ^ (((1 : ℝ) / 2) * (1 - ((k : ℝ) * ((k : ℝ) + 1)) / (((2 * s : ℕ) : ℝ))) + ε₀)) := by
  rcases bdg_discrete_restriction k hk ε₀ hε₀ with ⟨Cd, hCd, hbd⟩
  refine ⟨Cd, hCd, ?_⟩
  intro X hX
  have hsep := separated_succ_div X hX
  have hR : 0 < (X : ℝ) ^ k := pow_pos (by exact_mod_cast (lt_of_lt_of_le zero_lt_one hX)) k
  have hp2 : 2 ≤ (((2 * s : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : 2 ≤ 2 * s)
  have hbdX := hbd X hX (fun i : Fin X => (((i.1 + 1 : ℕ) : ℝ) / X)) hsep
    (fun _ : Fin X => (1 : ℂ)) (0 : E k) (((2 * s : ℕ) : ℝ)) hp2
  rw [wLpPowAvg_valSum_eq_sepCharSum k X (((2 * s : ℕ) : ℝ))]
  simpa using hbdX

/-- applying BDG's discrete restriction theorem at `p = 2s` bounds `Tint` by
`X^{k·k}·X^s·(X^{ε₀} + X^{β(2s)+ε₀})^{2s}` (uniform constant) -/
lemma thm41_upper_bound (s k : ℕ) (hs : 1 ≤ s) (hk : 1 ≤ k) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
      Tint k X s ≤ C * (((X : ℝ) ^ k) ^ k) * (X : ℝ) ^ s
        * ((X : ℝ) ^ ε₀ + (X : ℝ) ^ (((1 : ℝ) / 2) * (1 - ((k : ℝ) * ((k : ℝ) + 1)) / (((2 * s : ℕ) : ℝ))) + ε₀)) ^ (2 * s) := by
  rcases phiR_le_const_ballWeight k with ⟨Cφ, hCφ, hphi⟩
  rcases bdg_valSum_bound s k hs hk ε₀ hε₀ with ⟨Cd, hCd, hbd⟩
  let p : ℝ := (((2 * s : ℕ) : ℝ))
  let C : ℝ := Cφ * (Cd ^ (2 * s)) * ballVol k 0 1
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact mul_pos (mul_pos hCφ (pow_pos hCd (2 * s))) (ballVol_pos k hk (0 : E k) (by norm_num))
  · intro X hX
    have h1 := Tint_le_const_wLp s k X hk hX Cφ hCφ (hphi X hX)
    have hbdX := hbd X hX
    have hX0 : 0 ≤ (X : ℝ) := by exact_mod_cast (Nat.zero_le X)
    have hR : 0 < (X : ℝ) ^ k := pow_pos (by exact_mod_cast (lt_of_lt_of_le zero_lt_one hX)) k
    let U : ℝ := (X : ℝ) ^ ε₀ + (X : ℝ) ^ (((1 : ℝ) / 2) * (1 - ((k : ℝ) * ((k : ℝ) + 1)) / (((2 * s : ℕ) : ℝ))) + ε₀)
    have hU0 : 0 ≤ U := by
      dsimp [U]
      exact add_nonneg (Real.rpow_nonneg hX0 ε₀) (Real.rpow_nonneg hX0 _)
    have hp0 : 0 < p := by
      dsimp [p]
      positivity
    have hav0 : 0 ≤ wLpPowAvg k 0 ((X : ℝ) ^ k) p (valSum k X) := by
      unfold wLpPowAvg
      have hw0 : 0 ≤ wLpPow k 0 ((X : ℝ) ^ k) p (valSum k X) := by
        unfold wLpPow
        apply integral_nonneg
        intro x
        exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) p)
          (le_of_lt (ballWeight_pos k 0 hR x))
      exact div_nonneg hw0 (le_of_lt (ballVol_pos k hk (0 : E k) hR))
    have hB0 : 0 ≤ Cd * Real.sqrt (X : ℝ) * U :=
      mul_nonneg (mul_nonneg (le_of_lt hCd) (Real.sqrt_nonneg _)) hU0
    have hra : wLpPowAvg k 0 ((X : ℝ) ^ k) p (valSum k X)
        ≤ (Cd * Real.sqrt (X : ℝ) * U) ^ p := by
      exact le_of_rpow_le_rpow hav0 hB0 hp0 (by simpa [U, p] using hbdX)
    have hvol : ballVol k 0 ((X : ℝ) ^ k) = (((X : ℝ) ^ k) ^ k) * ballVol k 0 1 := by
      simpa using (ballVol_smul k hk (0 : E k) (show 0 ≤ (X : ℝ) ^ k by positivity))
    have hvolpos : 0 < ballVol k 0 ((X : ℝ) ^ k) := ballVol_pos k hk (0 : E k) hR
    have hw : wLpPow k 0 ((X : ℝ) ^ k) p (valSum k X)
        = wLpPowAvg k 0 ((X : ℝ) ^ k) p (valSum k X) * ballVol k 0 ((X : ℝ) ^ k) := by
          unfold wLpPowAvg
          field_simp [ne_of_gt hvolpos]
    have hWle : wLpPow k 0 ((X : ℝ) ^ k) p (valSum k X)
        ≤ (((X : ℝ) ^ k) ^ k) * ballVol k 0 1 * (Cd * Real.sqrt (X : ℝ) * U) ^ p := by
      calc
        wLpPow k 0 ((X : ℝ) ^ k) p (valSum k X)
            = wLpPowAvg k 0 ((X : ℝ) ^ k) p (valSum k X) * ballVol k 0 ((X : ℝ) ^ k) := hw
        _ ≤ (Cd * Real.sqrt (X : ℝ) * U) ^ p * ballVol k 0 ((X : ℝ) ^ k) :=
              mul_le_mul_of_nonneg_right hra (le_of_lt hvolpos)
        _ = (((X : ℝ) ^ k) ^ k) * ballVol k 0 1 * (Cd * Real.sqrt (X : ℝ) * U) ^ p := by
              rw [hvol]
              ring
    have hsq : (Real.sqrt (X : ℝ)) ^ (2 * s) = (X : ℝ) ^ s := by
      rw [pow_mul]
      rw [Real.sq_sqrt hX0]
    have hBpow : (Cd * Real.sqrt (X : ℝ) * U) ^ p = (Cd ^ (2 * s)) * (X : ℝ) ^ s * U ^ (2 * s) := by
      dsimp [p]
      rw [Real.rpow_natCast]
      rw [mul_pow, mul_pow]
      rw [hsq]
    have hmain : Tint k X s ≤ C * (((X : ℝ) ^ k) ^ k) * (X : ℝ) ^ s * U ^ (2 * s) := by
      calc
        Tint k X s ≤ Cφ * wLpPow k 0 ((X : ℝ) ^ k) p (valSum k X) := h1
        _ ≤ Cφ * ((((X : ℝ) ^ k) ^ k) * ballVol k 0 1 * (Cd * Real.sqrt (X : ℝ) * U) ^ p) := by
              exact mul_le_mul_of_nonneg_left hWle (le_of_lt hCφ)
        _ = C * (((X : ℝ) ^ k) ^ k) * (X : ℝ) ^ s * U ^ (2 * s) := by
              rw [hBpow]
              dsimp [C]
              ring
    simpa [U, p] using hmain



/-! ## Item 7: assembly `bdg_Jsep_core` -/

/-- `(X^a)^n = X^(a·n)` for a real power raised to a natural power -/
lemma rpow_pow_nat {X : ℝ} (hX0 : 0 ≤ X) (a : ℝ) (n : ℕ) :
    (X ^ a) ^ n = X ^ (a * (n : ℝ)) := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hX0 a (n : ℝ)]

/-- `X^s·X^{t} = X^{s+t}` with `s` natural, `t` real -/
lemma pow_mul_rpow {X : ℝ} (hXpos : 0 < X) (s : ℕ) (t : ℝ) :
    X ^ s * X ^ t = X ^ ((s : ℝ) + t) := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_add hXpos (s : ℝ) t]

/-- the exponent `2s·β` where `β = (1/2)(1 − k(k+1)/(2s))` -/
lemma two_mul_beta (s k : ℕ) (hs : 1 ≤ s) :
    ((2 * s : ℕ) : ℝ) * (((1 : ℝ) / 2) * (1 - ((k : ℝ) * ((k : ℝ) + 1)) / (((2 * s : ℕ) : ℝ))))
      = (s : ℝ) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 := by
  have hqcast : ((2 * s : ℕ) : ℝ) = (2 : ℝ) * (s : ℝ) := by norm_num
  rw [hqcast]
  have hs0 : (s : ℝ) ≠ 0 := by positivity
  field_simp [hs0]

/-- the upper-bound exponent relation: `2s·ε₀ = ε` when `ε₀ = ε/(2s)` -/
lemma two_mul_eps0 (s : ℕ) (hs : 1 ≤ s) (ε ε₀ : ℝ) (hε₀ : ε₀ = ε / ((2 * s : ℕ) : ℝ)) :
    ((2 * s : ℕ) : ℝ) * ε₀ = ε := by
  rw [hε₀]
  have hqcast : ((2 * s : ℕ) : ℝ) = (2 : ℝ) * (s : ℝ) := by norm_num
  rw [hqcast]
  have hs0 : (s : ℝ) ≠ 0 := by positivity
  field_simp [hs0]

/-- `Jsep` satisfies BDG's Corollary 4.2 bound (regime `1 ≤ s`, `1 ≤ k`) -/
lemma bdg_Jsep_core (s k : ℕ) (hs : 1 ≤ s) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X → (Jsep s k X : ℝ) ≤ C * rhs s k ε X := by
  let q : ℝ := ((2 * s : ℕ) : ℝ)
  let ε₀ : ℝ := ε / q
  let β : ℝ := ((1 : ℝ) / 2) * (1 - ((k : ℝ) * ((k : ℝ) + 1)) / q)
  have hq0 : q ≠ 0 := by dsimp [q]; exact_mod_cast (by omega : (2 * s : ℕ) ≠ 0)
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  rcases thm41_upper_bound s k hs hk ε₀ hε₀ with ⟨Cu, hCu, hu⟩
  let C : ℝ := Real.exp (π * (k : ℝ)) * Cu * (2 : ℝ) ^ (2 * s)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro X hX
    have hXpos : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hX)
    have hX0 : 0 ≤ (X : ℝ) := le_of_lt hXpos
    have hlb := lower_bound_Jsep s k X hX
    have hub := hu X hX
    let U : ℝ := (X : ℝ) ^ ε₀ + (X : ℝ) ^ (β + ε₀)
    have hUa : 0 ≤ (X : ℝ) ^ ε₀ := Real.rpow_nonneg hX0 ε₀
    have hUb : 0 ≤ (X : ℝ) ^ (β + ε₀) := Real.rpow_nonneg hX0 _
    have hXkk : 0 < ((X : ℝ) ^ k) ^ k := pow_pos (pow_pos hXpos k) k
    -- (Jsep)·X^{kk} ≤ e^{πk}·Tint ≤ e^{πk}·Cu·X^{kk}·X^s·U^{2s}
    have hJ1 : (Jsep s k X : ℝ) * ((X : ℝ) ^ k) ^ k
        ≤ Real.exp (π * (k : ℝ)) * Cu * (((X : ℝ) ^ k) ^ k) * (X : ℝ) ^ s * U ^ (2 * s) := by
      calc
        (Jsep s k X : ℝ) * ((X : ℝ) ^ k) ^ k ≤ Real.exp (π * (k : ℝ)) * Tint k X s := hlb
        _ ≤ Real.exp (π * (k : ℝ)) * (Cu * (((X : ℝ) ^ k) ^ k) * (X : ℝ) ^ s * U ^ (2 * s)) := by
              have ht : Tint k X s ≤ Cu * (((X : ℝ) ^ k) ^ k) * (X : ℝ) ^ s * U ^ (2 * s) := by
                simpa [U, β, q] using hub
              exact mul_le_mul_of_nonneg_left ht (Real.exp_nonneg _)
        _ = Real.exp (π * (k : ℝ)) * Cu * (((X : ℝ) ^ k) ^ k) * (X : ℝ) ^ s * U ^ (2 * s) := by ring
    -- divide by X^{kk}
    have hJ2 : (Jsep s k X : ℝ) ≤ Real.exp (π * (k : ℝ)) * Cu * (X : ℝ) ^ s * U ^ (2 * s) := by
      have hJ1' : ((X : ℝ) ^ k) ^ k * (Jsep s k X : ℝ)
          ≤ ((X : ℝ) ^ k) ^ k * (Real.exp (π * (k : ℝ)) * Cu * (X : ℝ) ^ s * U ^ (2 * s)) := by
            simpa [mul_comm, mul_assoc, mul_left_comm] using hJ1
      exact le_of_mul_le_mul_left hJ1' hXkk
    -- now expand `U^{2s}` by the two-sum power bound and match exponents
    have hU2 : U ^ (2 * s) ≤ (2 : ℝ) ^ (2 * s)
        * ((((X : ℝ) ^ ε₀) ^ (2 * s)) + (((X : ℝ) ^ (β + ε₀)) ^ (2 * s))) := by
      -- add_pow_le_two_pow_mul (X^ε₀) (X^{β+ε₀}) (2*s) hUa hUb
      have hp := Commons.Analysis.Real.add_pow_le_two_pow_mul ((X : ℝ) ^ ε₀) ((X : ℝ) ^ (β + ε₀)) (2 * s) hUa hUb
      simpa [U] using hp
    have hXpos : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hX)
    have hX0' : 0 ≤ (X : ℝ) := le_of_lt hXpos
    have hε₁ : ((2 * s : ℕ) : ℝ) * ε₀ = ε := by
      exact two_mul_eps0 s hs ε ε₀ (by rfl)
    have hAeq : ((X : ℝ) ^ ε₀) ^ (2 * s) = (X : ℝ) ^ ε := by
      rw [rpow_pow_nat hX0' ε₀ (2 * s)]
      congr 1
      -- ε₀·(2s:ℝ) = ε
      have hc : ε₀ * ((2 * s : ℕ) : ℝ) = ε := by
        rw [mul_comm]
        exact two_mul_eps0 s hs ε ε₀ (by rfl)
      exact hc
    have hBeq : ((X : ℝ) ^ (β + ε₀)) ^ (2 * s) = (X : ℝ) ^ ((s : ℝ) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 + ε) := by
      rw [rpow_pow_nat hX0' (β + ε₀) (2 * s)]
      congr 1
      have hbb : ((2 * s : ℕ) : ℝ) * β = (s : ℝ) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 := by
        dsimp [β]
        exact two_mul_beta s k hs
      have hbb' : (β + ε₀) * ((2 * s : ℕ) : ℝ) = (s : ℝ) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 + ε := by
        rw [add_mul, mul_comm β ((2*s:ℕ):ℝ), mul_comm ε₀ ((2*s:ℕ):ℝ), hbb]
        rw [hε₁]
      exact hbb'
    -- multiply by X^s and combine with the two target powers
    have hfin : Real.exp (π * (k : ℝ)) * Cu * (X : ℝ) ^ s * U ^ (2 * s)
        ≤ C * rhs s k ε X := by
      calc
        Real.exp (π * (k : ℝ)) * Cu * (X : ℝ) ^ s * U ^ (2 * s)
            ≤ Real.exp (π * (k : ℝ)) * Cu * (X : ℝ) ^ s
                * ((2 : ℝ) ^ (2 * s) * ((((X : ℝ) ^ ε₀) ^ (2 * s)) + (((X : ℝ) ^ (β + ε₀)) ^ (2 * s)))) := by
                exact mul_le_mul_of_nonneg_left hU2 (mul_nonneg (mul_nonneg (Real.exp_nonneg _) (le_of_lt hCu)) (pow_nonneg hX0' s))
        _ = Real.exp (π * (k : ℝ)) * Cu * (2 : ℝ) ^ (2 * s)
            * ((X : ℝ) ^ s * (((X : ℝ) ^ ε₀) ^ (2 * s)) + (X : ℝ) ^ s * (((X : ℝ) ^ (β + ε₀)) ^ (2 * s))) := by
                ring
        _ = Real.exp (π * (k : ℝ)) * Cu * (2 : ℝ) ^ (2 * s)
            * ((X : ℝ) ^ ((s : ℝ) + ε) + (X : ℝ) ^ ((s : ℝ) + ((s : ℝ) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 + ε))) := by
                congr 2
                · rw [hAeq]
                  rw [pow_mul_rpow hXpos s ε]
                · rw [hBeq]
                  rw [pow_mul_rpow hXpos s ((s : ℝ) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 + ε)]
        _ = C * rhs s k ε X := by
                dsimp [C]
                rw [rhs]
                ring_nf
    exact le_trans hJ2 hfin


/-! ## Plug-in: `bdg_Jsep_core` implies the deep core

With `bdg_Jsep_core` (BDG Cor. 4.2 in the regime `1 ≤ s`, `1 ≤ k`) proven
above, the inclusion `J ≤ Jsep` and the asymptotics assembly
`vmvt_of_Jsep_bound` give the whole Vinogradov mean value theorem in the deep
regime (indeed in every regime with `1 ≤ s`, `1 ≤ k`); the only remaining
deep input is the critical case `bdg_critical` of `Decoupling.lean` (the
ℓ²-decoupling theorem for the moment curve, BDG Thm 1.2). -/

/-- **The deep core from the discretisation bound**: `bdg_Jsep_core` implies
the Vinogradov mean value theorem whenever `1 ≤ s` and `1 ≤ k` (in particular
in the deep regime `3 ≤ k`, `s ≥ k+1` of `Main.core_vinogradov`). -/
theorem vmvt_of_bdg (s k : ℕ) (hs : 1 ≤ s) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    VMVT s k ε hε := by
  exact vmvt_of_Jsep_bound s k ε hε (bdg_Jsep_core s k hs hk ε hε)

end Submission.Vinogradov
