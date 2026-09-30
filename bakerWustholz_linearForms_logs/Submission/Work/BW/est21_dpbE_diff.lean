import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.QdescBase
import Submission.Work.BW.est13_clean
import Submission.Work.BW.est21_l_vanish_n_red
import Submission.Work.BW.est14_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MvPolynomial

/-! # Port of `Work.BW.est21_dpb_diff`

`est21_dpb_diff` is the identity underlying BW's comparison `f^{(J)} - g^{(J)}`: applying the
twisted derivative `∂₀^a ∏_i (∂*_i)^{t'_i}` to the descended auxiliary polynomial `Q^{(J)}` and
evaluating first with the determination `ℓ = ellM` (BW's `f`) and then with `ℓ = lamP` (BW's `g`),
the difference is the sum over the residue index `λ`, of the `g`-summand times `e^{δ_λ} - 1`.

The two ingredients are the `λ`-decomposition of the twisted derivative
(`applyDer_n_Qdesc_eq_sum`, `est21_l_vanish_n_red`) together with the evaluation of a descended
summand at `ptC ℓ z` (`est21_dpbE_eval_Qdescbase_ptC`, ported here from `est21_dpb_pt`), and the
one-line factorisation `∏ e^{zM_j n_j} - ∏ e^{zℓ_j n_j} = ∏ e^{zℓ_j n_j} (e^{δ} - 1)`
(`prod_exp_sub`, `est14_defs`). -/

/-- Evaluating a descended summand `Qdescbase lm t0` at the point `(z, e^{zℓ₁}, …)` (port of
`eval_Qdescbase_ptC` of `Submission/Work/BW/est21_dpb_pt.lean`, stated against the sorry-free
`est13_clean`). -/
lemma est21_dpbE_eval_Qdescbase_ptC {r : ℕ} (h D0 : ℕ) (Dj : Fin r → ℕ) (J : ℕ)
    (lm : AuxIdx r h D0 Dj) (t0 : ℕ) (ℓ : Fin r → ℂ) (z : ℂ) :
    MvPolynomial.eval (ptC ℓ z) (Qdescbase h D0 Dj J lm t0)
      = Theta (((2 : ℂ) ^ J)⁻¹ * z + ((lm.1 : ℕ) : ℂ)) h ((lm.2.1 : ℕ) + 1) t0
          * ∏ j : Fin r, (Complex.exp (z * ℓ j)) ^ ((lm.2.2 j : ℕ) / 2 ^ J) := by
  rw [Qdescbase, MvPolynomial.eval_mul, dy0part, eval_aeval_scaled, dymon, ymon,
    eval_prod_X_succ_ptC]
  rfl

/-- Port of `est21_dpb_diff_fAt_sum`.  Evaluating the twisted derivative
`∂₀^a∏_{i:Fin n}(∂*_i)^{t'_i}Q^{(J)}(·;t₀,t)` at the point `ptC ℓ z = (z, e^{zℓ₁}, …)`: the `∂*_i`
contribute `γ_i(⌊λ/2^J⌋)^{t'_i}`, the `∂₀^a` contributes `a!·2^{-Ja}·C(a+t₀,a)` and the Hasse order
of the `Y₀`-part moves from `t₀` to `a+t₀`. -/
lemma est21_dpbE_diff_fAt_sum {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {b : Fin n → ℤ} {k : Fin n} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ) (a : ℕ) (t' : Fin n → ℕ)
    (z : ℂ) (ℓ : Fin r → ℂ) :
    fAt ℓ
        (applyDer (fun i j => (derVec b k L i j : ℚ)) a t' (QJ φ b k L ι v σ p J μ t0 t)) z
      = ∑ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
          (if estCond J μ lm then
            (φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
              * (ulcm (acH K b v) : ℂ) ^ t0
              * (∏ i, (gam b k L i (fun j => (lm.2.2 j : ℕ) / 2 ^ J)) ^ (t' i))
              * (((a.factorial : ℂ)) * (((2 : ℂ) ^ J)⁻¹) ^ a
                  * ((Nat.choose (a + t0) a : ℕ) : ℂ)))
              * Polynomial.aeval ((((2 : ℂ) ^ J)⁻¹) * z + ((lm.1 : ℕ) : ℂ))
                  (Polynomial.hasseDeriv (a + t0) (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1)))
              * estTorus J ℓ z (fun i => (lm.2.2 i : ℕ))
          else 0) := by
  have hmain := applyDer_n_Qdesc_eq_sum (φ := φ) b k L ι (acH K b v)
    (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ t0 t a t'
  simp only [QJ] at hmain ⊢
  rw [hmain, fAt_sum_red]
  refine Finset.sum_congr rfl fun lm _ => ?_
  rw [fAt_smul_red]
  by_cases hc : estCond J μ lm
  · rw [if_pos hc, if_pos hc]
    rw [fAt, est21_dpbE_eval_Qdescbase_ptC]
    simp only [Theta, estTorus]
    ring
  · rw [if_neg hc, if_neg hc]
    simp

/-- Port of `Work.BW.est21_dpb_diff` (the explicit `(f−g)`-decomposition of the twisted derivative, BW §17/§20).  The original lives in `Submission/Work/BW/est21_dpb_diff.lean` (line 58) — copy its proof verbatim, together with the two lemmas it uses from its own file / from `est21_dpb_pt.lean`:
* `est21_dpbE_diff_fAt_sum` = the lemma `est21_dpb_diff_fAt_sum` of `est21_dpb_diff.lean` (line 27),
* `est21_dpbE_eval_Qdescbase_ptC` = the lemma `eval_Qdescbase_ptC` of `Submission/Work/BW/est21_dpb_pt.lean` (line 17).
All those files import `Submission.Work.BW.est13`, which does NOT compile, so import `Submission.Work.BW.est13_clean` instead (it provides `eval_aeval_scaled` and `eval_prod_X_succ_ptC`, the two lemmas `eval_Qdescbase_ptC` needs).  Also replace `import Submission.Work.BW.est21_l_vanish_n` by `Submission.Work.BW.est21_l_vanish_n_red`: there the lemmas `fAt_sum` and `fAt_smul` are called `fAt_sum_red` and `fAt_smul_red` (use those names in the proof), while `applyDer_n_Qdesc_eq_sum` keeps its name.  ANY extra declaration must have a name starting with `est21_dpbE_` and be public. -/
theorem est21_dpbE_diff {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ) (a : ℕ) (t' : Fin n → ℕ) (z : ℂ) :
    fAt (ellM φ α b k v L)
        (applyDer (fun i j => (derVec b k L i j : ℚ)) a t' (QJ φ b k L ι v σ p J μ t0 t)) z
      - fAt (fun j => lamP φ α v L j)
        (applyDer (fun i j => (derVec b k L i j : ℚ)) a t' (QJ φ b k L ι v σ p J μ t0 t)) z
    = ∑ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
        (if estCond J μ lm then
            (φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
              * (ulcm (acH K b v) : ℂ) ^ t0
              * (∏ i, (gam b k L i (fun j => (lm.2.2 j : ℕ) / 2 ^ J)) ^ (t' i))
              * (((a.factorial : ℂ)) * (((2 : ℂ) ^ J)⁻¹) ^ a
                  * ((Nat.choose (a + t0) a : ℕ) : ℂ)))
              * Polynomial.aeval ((((2 : ℂ) ^ J)⁻¹) * z + ((lm.1 : ℕ) : ℂ))
                  (Polynomial.hasseDeriv (a + t0) (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1)))
              * estTorus J (fun j => lamP φ α v L j) z (fun i => (lm.2.2 i : ℕ))
              * (Complex.exp (estSig φ α b k v L J z lm) - 1)
          else 0) := by
  rw [est21_dpbE_diff_fAt_sum (ℓ := fun j => ellM φ α b k v L j) (z := z)
        J μ t0 t a t',
      est21_dpbE_diff_fAt_sum (ℓ := fun j => lamP φ α v L j) (z := z) J μ t0 t a t',
      ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun lm _ => ?_
  by_cases hc : estCond J μ lm
  · rw [if_pos hc, if_pos hc, if_pos hc]
    have hT : estTorus J (fun j => ellM φ α b k v L j) z (fun i => (lm.2.2 i : ℕ))
        - estTorus J (fun j => lamP φ α v L j) z (fun i => (lm.2.2 i : ℕ))
        = estTorus J (fun j => lamP φ α v L j) z (fun i => (lm.2.2 i : ℕ))
          * (Complex.exp (estSig φ α b k v L J z lm) - 1) := by
      have h := prod_exp_sub (a := fun j => z * ellM φ α b k v L j)
        (b := fun j => z * lamP φ α v L j) (n := fun j => (lm.2.2 j : ℕ) / 2 ^ J)
      have hsum : (∑ j, ((((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℂ)
            * (z * ellM φ α b k v L j - z * lamP φ α v L j)))
          = estSig φ α b k v L J z lm := by
        rw [estSig]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsum] at h
      exact h
    have hT1 : estTorus J (fun j => ellM φ α b k v L j) z (fun i => (lm.2.2 i : ℕ))
        = estTorus J (fun j => lamP φ α v L j) z (fun i => (lm.2.2 i : ℕ))
          + estTorus J (fun j => lamP φ α v L j) z (fun i => (lm.2.2 i : ℕ))
            * (Complex.exp (estSig φ α b k v L J z lm) - 1) := by
      rw [← hT]; ring
    rw [hT1]
    ring
  · rw [if_neg hc, if_neg hc, if_neg hc]
    ring

end Work.BW
