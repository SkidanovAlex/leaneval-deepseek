import Mathlib
import Submission.Work.WilE9.Ift.Basic
import Submission.Work.WilE9.Defs
import Submission.Work.WilE9.Ift.AppendCLM
import Submission.Work.WilE9.Ift.fderiv_eaEval_append
import Submission.Work.WilE9.Ift.jc_eval_eq

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical Filter Topology
namespace Work.WilE9.Ift
open WilkiesDesign WilkiesDesign.E

/-! ## Auxiliary material for the implicit-function identity

The induction below differentiates the quotient `P_L(x,yx) / Q(x,yx)^(2|L|)` along a coordinate
direction.  The pieces are the chain rule (`fderiv_eaEval_append`), the first-order formula
`∂_{x_i} y_l = jc_{l i}/Q` (`jc_eval_eq`), the quotient rule for `f / h^k`
(`hasFDerivAt_div_pow`), and the arithmetic that clears the denominators (`quot_cleared`). -/

/-- `x ↦ eaEval c P (x, y x)`: the evaluation of `P` along the graph of `y`. -/
def evSol {n q r : ℕ} (c : EAChain (n + q) r) (y : (Fin n → ℝ) → (Fin q → ℝ))
    (P : EAPoly (n + q) r) : (Fin n → ℝ) → ℝ :=
  fun x => eaEval c P (Fin.append x (y x))

/-- The chain-rule derivative of `evSol c y P` at `x`: the continuous linear map of
`Work.WilE9.Ift.fderiv_eaEval_append`. -/
def chainFd {n q r : ℕ} (c : EAChain (n + q) r) (y : (Fin n → ℝ) → (Fin q → ℝ))
    (x : Fin n → ℝ) (P : EAPoly (n + q) r) : (Fin n → ℝ) →L[ℝ] ℝ :=
  (∑ i : Fin n, (eaEval c (eaD c (Fin.castAdd q i) P) (Fin.append x (y x))) •
      (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ))
    + (∑ l : Fin q, (eaEval c (eaD c (Fin.natAdd n l) P) (Fin.append x (y x))) •
        ((ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ y x)))

/-- The chain rule along the graph of `y`. -/
theorem evSol_chain {n q r : ℕ} (c : EAChain (n + q) r) (y : (Fin n → ℝ) → (Fin q → ℝ))
    (x : Fin n → ℝ) (P : EAPoly (n + q) r) (hy : HasFDerivAt y (fderiv ℝ y x) x) :
    HasFDerivAt (evSol c y P) (chainFd c y x P) x :=
  fderiv_eaEval_append c P y x hy

/-- The chain-rule derivative evaluated on the `i`-th coordinate direction. -/
theorem chainFd_single {n q r : ℕ} (c : EAChain (n + q) r) (y : (Fin n → ℝ) → (Fin q → ℝ))
    (x : Fin n → ℝ) (P : EAPoly (n + q) r) (i : Fin n) :
    chainFd c y x P (Pi.single i 1)
      = eaEval c (eaD c (Fin.castAdd q i) P) (Fin.append x (y x))
        + ∑ l : Fin q, eaEval c (eaD c (Fin.natAdd n l) P) (Fin.append x (y x))
            * (fderiv ℝ y x (Pi.single i 1)) l := by
  simp only [chainFd, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  simp [Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]

/-- The quotient rule for `y ↦ f y / h y ^ k`, in the form used by the recursion. -/
theorem hasFDerivAt_div_pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f h : E → ℝ) (f' h' : E →L[ℝ] ℝ) (x : E) (k : ℕ)
    (hf : HasFDerivAt f f' x) (hh : HasFDerivAt h h' x) (hx : h x ≠ 0) :
    HasFDerivAt (fun y => f y / h y ^ k)
      ((h x ^ k)⁻¹ • f' - (((h x ^ k) ^ 2)⁻¹ * f x * ((k : ℝ) * h x ^ (k - 1))) • h') x := by
  have hk : HasFDerivAt (fun y => h y ^ k) ((k • h x ^ (k - 1)) • h') x := hh.pow k
  have hinv : HasFDerivAt (fun y : ℝ => y⁻¹)
      (ContinuousLinearMap.toSpanSingleton ℝ (-((h x ^ k) ^ 2)⁻¹)) (h x ^ k) :=
    hasFDerivAt_inv (pow_ne_zero k hx)
  have hcomp : HasFDerivAt (fun y => (h y ^ k)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-((h x ^ k) ^ 2)⁻¹)).comp
        ((k • h x ^ (k - 1)) • h')) x := hinv.comp x hk
  have hmul := hf.mul hcomp
  have hCLM : (f x •
        ((ContinuousLinearMap.toSpanSingleton ℝ (-((h x ^ k) ^ 2)⁻¹)).comp
          ((k • h x ^ (k - 1)) • h')) + (h x ^ k)⁻¹ • f')
      = ((h x ^ k)⁻¹ • f' - (((h x ^ k) ^ 2)⁻¹ * f x * ((k : ℝ) * h x ^ (k - 1))) • h') := by
    ext v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    ring
  refine (hmul.congr_fderiv hCLM).congr_of_eventuallyEq ?_
  filter_upwards with y
  exact div_eq_mul_inv _ _

/-- Clearing the denominator: multiplying the derivative of `f / Q ^ k` by `Q ^ (k + 2)`. -/
theorem quot_cleared (Q dFL FL dQ : ℝ) (k : ℕ) (hQ : Q ≠ 0) :
    ((Q ^ k)⁻¹ * dFL - ((Q ^ k) ^ 2)⁻¹ * FL * ((k : ℝ) * Q ^ (k - 1)) * dQ) * Q ^ (k + 2)
      = Q ^ 2 * dFL - (k : ℝ) * FL * Q * dQ := by
  have hA : ∀ n : ℕ, (Q ^ n)⁻¹ * Q ^ (n + 2) = Q ^ 2 := by
    intro n
    rw [← inv_pow, pow_add, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hQ, one_pow, one_mul]
  have hB : ∀ n : ℕ, ((Q ^ (n + 1)) ^ 2)⁻¹ * Q ^ n * Q ^ (n + 1 + 2) = Q := by
    intro n
    have e1 : ((Q ^ (n + 1)) ^ 2)⁻¹ = (Q⁻¹ : ℝ) ^ (2 * (n + 1)) := by
      rw [pow_two, mul_inv, ← inv_pow, ← pow_add]
      congr 1
      ring
    have e2 : Q ^ n * Q ^ (n + 1 + 2) = Q ^ (2 * (n + 1)) * Q := by
      rw [← pow_add, show n + (n + 1 + 2) = 2 * (n + 1) + 1 from by ring, pow_add, pow_one]
    rw [show ((Q ^ (n + 1)) ^ 2)⁻¹ * Q ^ n * Q ^ (n + 1 + 2)
          = ((Q ^ (n + 1)) ^ 2)⁻¹ * (Q ^ n * Q ^ (n + 1 + 2)) from by ring]
    rw [e2, e1, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hQ, one_pow, one_mul]
  rcases k with _ | k
  · simp
    ring
  · rw [Nat.cast_add, Nat.cast_one, Nat.add_one_sub_one]
    rw [sub_mul]
    rw [show (Q ^ (k + 1))⁻¹ * dFL * Q ^ (k + 1 + 2)
          = dFL * ((Q ^ (k + 1))⁻¹ * Q ^ (k + 1 + 2)) from by ring]
    rw [hA (k + 1)]
    rw [show ((Q ^ (k + 1)) ^ 2)⁻¹ * FL * (((k : ℝ) + 1) * Q ^ k) * dQ * Q ^ (k + 1 + 2)
          = ((k : ℝ) + 1) * FL * dQ
              * (((Q ^ (k + 1)) ^ 2)⁻¹ * Q ^ k * Q ^ (k + 1 + 2)) from by ring]
    rw [hB k]
    ring

/-- Unfolding `glDeriv` at a cons: the head of the list is the outermost derivative. -/
theorem glDeriv_cons_single {n : ℕ} (i : Fin n) (L : List (Fin n)) (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) :
    glDeriv (i :: L) f x = fderiv ℝ (glDeriv L f) x (Pi.single i 1) := rfl

/-- **BNZ §3's implicit-function formula**, in the form of the induction: at every point where
`y` is a smooth solution with nonvanishing fibre Jacobian, `∂_L y_{l₀}` is the polynomial
`iftP c F l₀ L` divided by `Q ^ (2 |L|)`. -/
theorem ift_identity_aux {n q r : ℕ} (c : EAChain (n + q) r)
    (F : Fin q → EAPoly (n + q) r) (l₀ : Fin q) :
    ∀ (L : List (Fin n)) (y : (Fin n → ℝ) → (Fin q → ℝ)) (x₀ : Fin n → ℝ),
      ContDiffAt ℝ ⊤ y x₀ → IsSoln c F y x₀ →
      (∀ᶠ x in 𝓝 x₀, evSol c y (jQ c F) x ≠ 0) →
      evSol c y (iftP c F l₀ L) x₀ =
        glDeriv L (fun x => y x l₀) x₀ * evSol c y (jQ c F) x₀ ^ (2 * L.length) := by
  intro L
  induction L with
  | nil =>
    intro y x₀ hy hs hQ
    show eaEval c (MvPolynomial.X (Sum.inl (Fin.natAdd n l₀))) (Fin.append x₀ (y x₀))
      = (fun x => y x l₀) x₀
        * eaEval c (jQ c F) (Fin.append x₀ (y x₀)) ^ (2 * ([] : List (Fin n)).length)
    simp [eaEval, Fin.append_right]
  | cons i L ih =>
    intro y x₀ hy hs hQ
    have hdy : HasFDerivAt y (fderiv ℝ y x₀) x₀ :=
      (hy.differentiableAt (by simp)).hasFDerivAt
    have hQ0 : evSol c y (jQ c F) x₀ ≠ 0 := hQ.self_of_nhds
    -- the inductive hypothesis holds on a whole neighbourhood of `x₀`
    have hev : (fun x => glDeriv L (fun x => y x l₀) x) =ᶠ[𝓝 x₀]
        (fun x => evSol c y (iftP c F l₀ L) x / evSol c y (jQ c F) x ^ (2 * L.length)) := by
      filter_upwards [hy.eventually (by simp), hs.1.eventually_nhds, hs.2.eventually_nhds,
        hQ, hQ.eventually_nhds] with z hyz hs1 hs2 hQz hQzev
      rw [ih y z hyz ⟨hs1, hs2⟩ hQzev, mul_div_cancel_right₀ _ (pow_ne_zero _ hQz)]
    -- the derivative of the quotient at `x₀`
    have hquot : HasFDerivAt
        (fun x => evSol c y (iftP c F l₀ L) x / evSol c y (jQ c F) x ^ (2 * L.length)) _ x₀ :=
      hasFDerivAt_div_pow (evSol c y (iftP c F l₀ L)) (evSol c y (jQ c F))
        (chainFd c y x₀ (iftP c F l₀ L)) (chainFd c y x₀ (jQ c F)) x₀ (2 * L.length)
        (evSol_chain c y x₀ (iftP c F l₀ L) hdy) (evSol_chain c y x₀ (jQ c F) hdy) hQ0
    have hDL := hquot.congr_of_eventuallyEq hev
    have hfdval : fderiv ℝ (fun x => glDeriv L (fun x => y x l₀) x) x₀ (Pi.single i 1)
        = (evSol c y (jQ c F) x₀ ^ (2 * L.length))⁻¹
            * chainFd c y x₀ (iftP c F l₀ L) (Pi.single i 1)
          - ((evSol c y (jQ c F) x₀ ^ (2 * L.length)) ^ 2)⁻¹ * evSol c y (iftP c F l₀ L) x₀
              * (((2 * L.length : ℕ) : ℝ) * evSol c y (jQ c F) x₀ ^ (2 * L.length - 1))
            * chainFd c y x₀ (jQ c F) (Pi.single i 1) := by
      rw [hDL.fderiv]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    -- the first derivative of `y` in the `i`-th coordinate direction
    have hC : ∀ l : Fin q, eaEval c (jc c F l i) (Fin.append x₀ (y x₀))
        = (fderiv ℝ y x₀ (Pi.single i 1)) l * evSol c y (jQ c F) x₀ := fun l =>
      jc_eval_eq c F y x₀ i l hdy hs
    have hsum1 : (∑ l : Fin q, eaEval c (eaD c (Fin.natAdd n l) (iftP c F l₀ L))
            (Fin.append x₀ (y x₀)) * eaEval c (jc c F l i) (Fin.append x₀ (y x₀)))
        = (∑ l : Fin q, eaEval c (eaD c (Fin.natAdd n l) (iftP c F l₀ L))
              (Fin.append x₀ (y x₀)) * (fderiv ℝ y x₀ (Pi.single i 1)) l)
            * evSol c y (jQ c F) x₀ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun l _ => by rw [hC l]; ring)
    have hsum2 : (∑ l : Fin q, eaEval c (eaD c (Fin.natAdd n l) (jQ c F))
            (Fin.append x₀ (y x₀)) * eaEval c (jc c F l i) (Fin.append x₀ (y x₀)))
        = (∑ l : Fin q, eaEval c (eaD c (Fin.natAdd n l) (jQ c F))
              (Fin.append x₀ (y x₀)) * (fderiv ℝ y x₀ (Pi.single i 1)) l)
            * evSol c y (jQ c F) x₀ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun l _ => by rw [hC l]; ring)
    have hdFL : eaEval c (eaD c (Fin.castAdd q i) (iftP c F l₀ L)) (Fin.append x₀ (y x₀))
          + ∑ l : Fin q, eaEval c (eaD c (Fin.natAdd n l) (iftP c F l₀ L))
              (Fin.append x₀ (y x₀)) * (fderiv ℝ y x₀ (Pi.single i 1)) l
        = chainFd c y x₀ (iftP c F l₀ L) (Pi.single i 1) :=
      (chainFd_single c y x₀ (iftP c F l₀ L) i).symm
    have hdQ : eaEval c (eaD c (Fin.castAdd q i) (jQ c F)) (Fin.append x₀ (y x₀))
          + ∑ l : Fin q, eaEval c (eaD c (Fin.natAdd n l) (jQ c F))
              (Fin.append x₀ (y x₀)) * (fderiv ℝ y x₀ (Pi.single i 1)) l
        = chainFd c y x₀ (jQ c F) (Pi.single i 1) :=
      (chainFd_single c y x₀ (jQ c F) i).symm
    have hA' : eaEval c (eaD c (Fin.castAdd q i) (iftP c F l₀ L)) (Fin.append x₀ (y x₀))
        = chainFd c y x₀ (iftP c F l₀ L) (Pi.single i 1)
          - ∑ l : Fin q, eaEval c (eaD c (Fin.natAdd n l) (iftP c F l₀ L))
              (Fin.append x₀ (y x₀)) * (fderiv ℝ y x₀ (Pi.single i 1)) l := by
      rw [← hdFL]
      ring
    have hQi' : eaEval c (eaD c (Fin.castAdd q i) (jQ c F)) (Fin.append x₀ (y x₀))
        = chainFd c y x₀ (jQ c F) (Pi.single i 1)
          - ∑ l : Fin q, eaEval c (eaD c (Fin.natAdd n l) (jQ c F))
              (Fin.append x₀ (y x₀)) * (fderiv ℝ y x₀ (Pi.single i 1)) l := by
      rw [← hdQ]
      ring
    -- the recursion, evaluated along the solution
    have hrec : evSol c y (iftP c F l₀ (i :: L)) x₀
        = evSol c y (jQ c F) x₀ ^ 2
              * eaEval c (eaD c (Fin.castAdd q i) (iftP c F l₀ L)) (Fin.append x₀ (y x₀))
          + evSol c y (jQ c F) x₀
              * (∑ l : Fin q, eaEval c (eaD c (Fin.natAdd n l) (iftP c F l₀ L))
                    (Fin.append x₀ (y x₀)) * eaEval c (jc c F l i) (Fin.append x₀ (y x₀)))
          - (((2 * L.length : ℕ) : ℝ))
              * (evSol c y (iftP c F l₀ L) x₀
                  * (evSol c y (jQ c F) x₀
                        * eaEval c (eaD c (Fin.castAdd q i) (jQ c F)) (Fin.append x₀ (y x₀))
                      + ∑ l : Fin q, eaEval c (eaD c (Fin.natAdd n l) (jQ c F))
                            (Fin.append x₀ (y x₀))
                          * eaEval c (jc c F l i) (Fin.append x₀ (y x₀)))) := by
      rw [show evSol c y (iftP c F l₀ (i :: L)) x₀
            = eaEval c (iftP c F l₀ (i :: L)) (Fin.append x₀ (y x₀)) from rfl]
      rw [Work.WilE9.iftP]
      simp only [evSol, eaEval, map_add, map_mul, map_sub, map_sum, map_pow, map_natCast,
        nsmul_eq_mul]
    have hrec2 : evSol c y (iftP c F l₀ (i :: L)) x₀
        = evSol c y (jQ c F) x₀ ^ 2 * chainFd c y x₀ (iftP c F l₀ L) (Pi.single i 1)
          - ((2 * L.length : ℕ) : ℝ) * evSol c y (iftP c F l₀ L) x₀ * evSol c y (jQ c F) x₀
              * chainFd c y x₀ (jQ c F) (Pi.single i 1) := by
      rw [hrec, hsum1, hsum2, hA', hQi']
      ring
    rw [glDeriv_cons_single, hfdval]
    rw [show 2 * (i :: L).length = 2 * L.length + 2 from by
      simp [List.length_cons, Nat.mul_add]]
    rw [quot_cleared (evSol c y (jQ c F) x₀) (chainFd c y x₀ (iftP c F l₀ L) (Pi.single i 1))
      (evSol c y (iftP c F l₀ L) x₀) (chainFd c y x₀ (jQ c F) (Pi.single i 1)) (2 * L.length) hQ0]
    exact hrec2

/-- **BNZ §3's implicit-function formula.**  If `y : ℝⁿ → ℝ^q` is `C^∞` at `x₀` and solves
`F(x, y x) = 0` (fibre Jacobian invertible) near `x₀`, then the whole derivative `∂_L y_{l₀}`
in the directions of the list `L` is the *polynomial* `iftP c F l₀ L` divided by `Q^{2|L|}`:

`(∂_L y_{l₀})(x) = P_L(x, y x) / Q(x, y x) ^ (2 |L|)`.

Because `P_L` is a polynomial in the *ambient coordinates* (no extra jet variables), this is
what makes the format of the derivative graph independent of `|L|` while its degree grows only
linearly in `|L|` (that is the point of "sharp derivatives").

Proof plan (induction on `L`, keeping the identity on a whole neighbourhood of `x₀`):
* `L = []`: `iftP c F l₀ [] = X` at the fibre coordinate `l₀`, and `glDeriv [] = id`.
* `i :: L`: differentiate `x ↦ eaEval c (iftP c F l₀ L) (x, y x) / Q(x,yx)^{2|L|}` along the
  `i`-th coordinate.  The chain rule is `Work.WilE9.Ift.fderiv_eaEval_append`, the first
  derivatives of `y` are `Work.WilE9.Ift.jc_eval_eq` (`∂_{x_i} y_l = jc_{l i}/Q`), and the
  recursion defining `iftP` is exactly the cleared form of the quotient rule.
  (Both ingredient modules exist in the tree and may be imported.)

The hypothesis `hQ` (the denominator does not vanish near `x₀`) is implied by `IsSoln` together
with `eaEval c ((jm c F).det) = det ((jm c F).map (eaEval c ·))`, i.e. that evaluation is a ring
hom commuting with `Matrix.det` (Mathlib's `RingHom.map_det`). -/
theorem ift_identity {n q r : ℕ} (c : WilkiesDesign.E.EAChain (n + q) r)
    (F : Fin q → WilkiesDesign.E.EAPoly (n + q) r) (l₀ : Fin q)
    (y : (Fin n → ℝ) → (Fin q → ℝ)) (x₀ : Fin n → ℝ)
    (hy : ContDiffAt ℝ ⊤ y x₀) (hs : Work.WilE9.IsSoln c F y x₀)
    (hQ : ∀ᶠ x in nhds x₀,
      WilkiesDesign.E.eaEval c (Work.WilE9.jQ c F) (Fin.append x (y x)) ≠ 0)
    (L : List (Fin n)) :
    WilkiesDesign.E.eaEval c (Work.WilE9.iftP c F l₀ L) (Fin.append x₀ (y x₀)) =
      Work.WilE9.glDeriv L (fun x => y x l₀) x₀ *
        WilkiesDesign.E.eaEval c (Work.WilE9.jQ c F) (Fin.append x₀ (y x₀)) ^ (2 * L.length) := by
  exact ift_identity_aux c F l₀ L y x₀ hy hs hQ

end Work.WilE9.Ift
