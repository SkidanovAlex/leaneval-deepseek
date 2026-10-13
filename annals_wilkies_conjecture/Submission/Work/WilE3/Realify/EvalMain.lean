/-
  annals_wilkies_conjecture, AREA E3, `Realify` (main).  The chain compatibility of the
  realified system, the support expansion of `realifyRe`/`realifyIm`, and the degree bounds.

  This module records, for the vocabulary of `Realify/Defs.lean`:

  * the chain point `chainPt` agrees with the chain functions of `mkChain` (`mkChain_psi`), so that
    `(mkChain c cc).ev Q (mkPt u v) = MvPolynomial.eval (chainPt c cc u v) Q`;
  * `realifyRe`/`realifyIm` expanded over the support of the polynomial;
  * the total-degree bounds `O (deg P + r N)` of the realified equations.
-/
import Submission.Work.WilE3.Realify.Defs

namespace Work.WilE3.Realify

set_option autoImplicit false
noncomputable section
open Classical Topology
open WilkiesDesign.E

variable {k r : ℕ}

/-! ## §1. The chain point -/

theorem mkPt_apply_castAdd (u v : Fin k → ℝ) (i : Fin k) :
    mkPt u v (Fin.castAdd k i) = u i := by
  simp only [mkPt, Fin.addCases_left]

theorem mkPt_apply_natAdd (u v : Fin k → ℝ) (i : Fin k) :
    mkPt u v (Fin.natAdd k i) = v i := by
  simp only [mkPt, Fin.addCases_right]

theorem zOf_mkPt (u v : Fin k → ℝ) :
    zOf (mkPt u v) = fun i => (u i : ℂ) + (v i : ℂ) * Complex.I := by
  funext i
  simp only [zOf, mkPt_apply_castAdd, mkPt_apply_natAdd]

theorem chainPt_inl (c : EAChain k r) (cc : Fin r → ℝ) (u v : Fin k → ℝ) (l : Fin (k + k)) :
    chainPt c cc u v (Sum.inl l) = mkPt u v l := rfl

theorem chainPt_inr_castAdd (c : EAChain k r) (cc : Fin r → ℝ) (u v : Fin k → ℝ) (j : Fin r) :
    chainPt c cc u v (Sum.inr (Fin.castAdd r j))
      = Real.exp (∑ i, c.a j i * u i + c.b j) := by
  simp only [chainPt, Sum.elim_inr, Fin.addCases_left]

theorem chainPt_inr_natAdd (c : EAChain k r) (cc : Fin r → ℝ) (u v : Fin k → ℝ) (j : Fin r) :
    chainPt c cc u v (Sum.inr (Fin.natAdd r j))
      = Real.tan ((∑ i, c.a j i * v i - cc j) / 2) := by
  simp only [chainPt, Sum.elim_inr, Fin.addCases_right]

/-! ## §2. The chain functions of `mkChain` -/

theorem mkChain_a (c : EAChain k r) (cc : Fin r → ℝ) :
    (mkChain c cc).a = chainA c := rfl

theorem mkChain_b (c : EAChain k r) (cc : Fin r → ℝ) :
    (mkChain c cc).b = chainB c cc := rfl

theorem mkChain_phi (c : EAChain k r) (cc : Fin r → ℝ) :
    (mkChain c cc).phi = chainPhi (r := r) := rfl

theorem mkChain_R (c : EAChain k r) (cc : Fin r → ℝ) :
    (mkChain c cc).R = chainR (r := r) := rfl

theorem mkChain_dom (c : EAChain k r) (cc : Fin r → ℝ) :
    (mkChain c cc).dom = chainDom (r := r) := rfl

theorem chainA_castAdd_castAdd (c : EAChain k r) (j : Fin r) (i : Fin k) :
    chainA c (Fin.castAdd r j) (Fin.castAdd k i) = c.a j i := by
  simp only [chainA, Fin.addCases_left]

theorem chainA_castAdd_natAdd (c : EAChain k r) (j : Fin r) (i : Fin k) :
    chainA c (Fin.castAdd r j) (Fin.natAdd k i) = 0 := by
  simp only [chainA, Fin.addCases_left, Fin.addCases_right]

theorem chainA_natAdd_castAdd (c : EAChain k r) (j : Fin r) (i : Fin k) :
    chainA c (Fin.natAdd r j) (Fin.castAdd k i) = 0 := by
  simp only [chainA, Fin.addCases_right, Fin.addCases_left]

theorem chainA_natAdd_natAdd (c : EAChain k r) (j : Fin r) (i : Fin k) :
    chainA c (Fin.natAdd r j) (Fin.natAdd k i) = c.a j i / 2 := by
  simp only [chainA, Fin.addCases_right]

theorem chainB_castAdd (c : EAChain k r) (cc : Fin r → ℝ) (j : Fin r) :
    chainB c cc (Fin.castAdd r j) = c.b j := by
  simp only [chainB, Fin.addCases_left]

theorem chainB_natAdd (c : EAChain k r) (cc : Fin r → ℝ) (j : Fin r) :
    chainB c cc (Fin.natAdd r j) = -cc j / 2 := by
  simp only [chainB, Fin.addCases_right]

theorem chainPhi_castAdd (j : Fin r) :
    chainPhi (r := r) (Fin.castAdd r j) = Real.exp := by
  simp only [chainPhi, Fin.addCases_left]

theorem chainPhi_natAdd (j : Fin r) :
    chainPhi (r := r) (Fin.natAdd r j) = Real.tan := by
  simp only [chainPhi, Fin.addCases_right]

theorem sum_chainA_castAdd (c : EAChain k r) (j : Fin r) (u v : Fin k → ℝ) :
    (∑ l : Fin (k + k), chainA c (Fin.castAdd r j) l * mkPt u v l)
      = ∑ i, c.a j i * u i := by
  rw [Fin.sum_univ_add]
  have h2 : (∑ i : Fin k, chainA c (Fin.castAdd r j) (Fin.natAdd k i)
      * mkPt u v (Fin.natAdd k i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [mkPt_apply_natAdd, chainA_castAdd_natAdd, zero_mul]
  rw [h2, add_zero]
  exact Finset.sum_congr rfl fun i _ => by rw [mkPt_apply_castAdd, chainA_castAdd_castAdd]

theorem sum_chainA_natAdd (c : EAChain k r) (j : Fin r) (u v : Fin k → ℝ) :
    (∑ l : Fin (k + k), chainA c (Fin.natAdd r j) l * mkPt u v l)
      = ∑ i, (c.a j i / 2) * v i := by
  rw [Fin.sum_univ_add]
  have h1 : (∑ i : Fin k, chainA c (Fin.natAdd r j) (Fin.castAdd k i)
      * mkPt u v (Fin.castAdd k i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [mkPt_apply_castAdd, chainA_natAdd_castAdd, zero_mul]
  rw [h1, zero_add]
  exact Finset.sum_congr rfl fun i _ => by rw [mkPt_apply_natAdd, chainA_natAdd_natAdd]

theorem sum_div_two_eq (c : EAChain k r) (j : Fin r) (cc : Fin r → ℝ) (v : Fin k → ℝ) :
    (∑ i, (c.a j i / 2) * v i) + (-cc j / 2) = (∑ i, c.a j i * v i - cc j) / 2 := by
  have h2 : (∑ i, (c.a j i / 2) * v i) = (∑ i, c.a j i * v i) / 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2]
  ring

theorem mkChain_psi (c : EAChain k r) (cc : Fin r → ℝ) (u v : Fin k → ℝ) (j : Fin (r + r)) :
    (mkChain c cc).psi j (mkPt u v) = chainPt c cc u v (Sum.inr j) := by
  revert j
  refine Fin.addCases
    (motive := fun j => (mkChain c cc).psi j (mkPt u v) = chainPt c cc u v (Sum.inr j)) ?_ ?_
  · intro j
    rw [SepChainLocal.psi, chainPt_inr_castAdd]
    simp only [mkChain_a, mkChain_b, mkChain_phi, chainPhi_castAdd, chainB_castAdd,
      sum_chainA_castAdd]
  · intro j
    rw [SepChainLocal.psi, chainPt_inr_natAdd]
    simp only [mkChain_a, mkChain_b, mkChain_phi, chainPhi_natAdd, chainB_natAdd,
      sum_chainA_natAdd]
    rw [sum_div_two_eq]

theorem mkChain_ev (c : EAChain k r) (cc : Fin r → ℝ) (Q : EAPoly (k + k) (r + r))
    (u v : Fin k → ℝ) :
    (mkChain c cc).ev Q (mkPt u v) = MvPolynomial.eval (chainPt c cc u v) Q := by
  rw [SepChainLocal.ev]
  have h : Sum.elim (mkPt u v) (fun j => (mkChain c cc).psi j (mkPt u v))
      = chainPt c cc u v := by
    funext x
    rcases x with l | j
    · exact chainPt_inl c cc u v l
    · exact mkChain_psi c cc u v j
  rw [h]

/-! ## §3. The support expansion of the realified polynomials -/

theorem monomial_eq_smul_monomial_one (m : (Fin k ⊕ Fin r) →₀ ℕ) (a : ℝ) :
    MvPolynomial.monomial m a = a • MvPolynomial.monomial m (1 : ℝ) := by
  ext m'
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  split_ifs <;> simp

theorem realifyRe_basis (N : ℕ) (e : Fin r → ℝ) (m : (Fin k ⊕ Fin r) →₀ ℕ) :
    realifyRe N e (MvPolynomial.monomial m (1 : ℝ))
      = rePoly (monoNum (k := k) (r := r) N e m) := by
  change (∑ m' ∈ (MvPolynomial.monomial m (1 : ℝ)).support,
      (MvPolynomial.monomial m (1 : ℝ)).coeff m' • rePoly (monoNum (k := k) (r := r) N e m'))
    = rePoly (monoNum (k := k) (r := r) N e m)
  rw [MvPolynomial.support_monomial, if_neg (one_ne_zero : (1 : ℝ) ≠ 0), Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl, one_smul]

theorem realifyIm_basis (N : ℕ) (e : Fin r → ℝ) (m : (Fin k ⊕ Fin r) →₀ ℕ) :
    realifyIm N e (MvPolynomial.monomial m (1 : ℝ))
      = imPoly (monoNum (k := k) (r := r) N e m) := by
  change (∑ m' ∈ (MvPolynomial.monomial m (1 : ℝ)).support,
      (MvPolynomial.monomial m (1 : ℝ)).coeff m' • imPoly (monoNum (k := k) (r := r) N e m'))
    = imPoly (monoNum (k := k) (r := r) N e m)
  rw [MvPolynomial.support_monomial, if_neg (one_ne_zero : (1 : ℝ) ≠ 0), Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl, one_smul]

theorem realifyRe_sum (N : ℕ) (e : Fin r → ℝ) (P : EAPoly k r) :
    realifyRe N e P = ∑ m ∈ P.support, P.coeff m • rePoly (monoNum (k := k) (r := r) N e m) := rfl

theorem realifyIm_sum (N : ℕ) (e : Fin r → ℝ) (P : EAPoly k r) :
    realifyIm N e P = ∑ m ∈ P.support, P.coeff m • imPoly (monoNum (k := k) (r := r) N e m) := rfl

/-! ## §5. The chain point of an arbitrary real point, and the clearing factor -/

theorem mkPt_uOf_vOf (w : Fin (k + k) → ℝ) : mkPt (uOf w) (vOf w) = w := by
  funext l
  revert l
  refine Fin.addCases (motive := fun l => mkPt (uOf w) (vOf w) l = w l) ?_ ?_
  · intro i
    simp only [mkPt, Fin.addCases_left, uOf]
  · intro i
    simp only [mkPt, Fin.addCases_right, vOf]

theorem zOf_mkPt_uOf_vOf (w : Fin (k + k) → ℝ) :
    zOf (mkPt (uOf w) (vOf w)) = zOf w := by
  rw [mkPt_uOf_vOf]

theorem mkChain_ev_of (c : EAChain k r) (cc : Fin r → ℝ) (Q : EAPoly (k + k) (r + r))
    (w : Fin (k + k) → ℝ) :
    (mkChain c cc).ev Q w = MvPolynomial.eval (chainPt c cc (uOf w) (vOf w)) Q := by
  rw [← mkChain_ev c cc Q (uOf w) (vOf w), mkPt_uOf_vOf]

theorem mkChain_dom_castAdd (c : EAChain k r) (cc : Fin r → ℝ) (j : Fin r) :
    (mkChain c cc).dom (Fin.castAdd r j) = Set.univ := by
  rw [mkChain_dom]
  simp only [chainDom, Fin.addCases_left]

theorem mkChain_dom_natAdd (c : EAChain k r) (cc : Fin r → ℝ) (j : Fin r) :
    (mkChain c cc).dom (Fin.natAdd r j) = {y | Real.cos y ≠ 0} := by
  rw [mkChain_dom]
  simp only [chainDom, Fin.addCases_right]

theorem mkChain_arg_castAdd (c : EAChain k r) (cc : Fin r → ℝ) (u v : Fin k → ℝ) (j : Fin r) :
    (∑ i, (mkChain c cc).a (Fin.castAdd r j) i * mkPt u v i) + (mkChain c cc).b (Fin.castAdd r j)
      = ∑ i, c.a j i * u i + c.b j := by
  rw [mkChain_a, mkChain_b, sum_chainA_castAdd, chainB_castAdd]

theorem mkChain_arg_natAdd (c : EAChain k r) (cc : Fin r → ℝ) (u v : Fin k → ℝ) (j : Fin r) :
    (∑ i, (mkChain c cc).a (Fin.natAdd r j) i * mkPt u v i) + (mkChain c cc).b (Fin.natAdd r j)
      = (∑ i, c.a j i * v i - cc j) / 2 := by
  rw [mkChain_a, mkChain_b, sum_chainA_natAdd, chainB_natAdd, sum_div_two_eq]

theorem mkChain_hx_castAdd (c : EAChain k r) (cc : Fin r → ℝ) (u v : Fin k → ℝ) (j : Fin r) :
    (∑ i, (mkChain c cc).a (Fin.castAdd r j) i * mkPt u v i) + (mkChain c cc).b (Fin.castAdd r j)
      ∈ (mkChain c cc).dom (Fin.castAdd r j) := by
  rw [mkChain_dom_castAdd]
  exact Set.mem_univ _

theorem mkChain_hx_natAdd (c : EAChain k r) (cc : Fin r → ℝ) (u v : Fin k → ℝ) (j : Fin r)
    (hcos : Real.cos ((∑ i, c.a j i * v i - cc j) / 2) ≠ 0) :
    (∑ i, (mkChain c cc).a (Fin.natAdd r j) i * mkPt u v i) + (mkChain c cc).b (Fin.natAdd r j)
      ∈ (mkChain c cc).dom (Fin.natAdd r j) := by
  rw [mkChain_dom_natAdd, mkChain_arg_natAdd]
  exact hcos

theorem ev_VW (c : EAChain k r) (cc : Fin r → ℝ) (w : Fin (k + k) → ℝ) (j : Fin r) :
    (mkChain c cc).ev (VW (k := k) j) w
      = 1 + (Real.tan ((∑ i, c.a j i * (vOf w) i - cc j) / 2)) ^ 2 := by
  rw [SepChainLocal.ev, VW]
  simp only [map_add, map_pow, map_one, Vt, MvPolynomial.eval_X, Sum.elim_inr]
  conv_lhs => rw [← mkPt_uOf_vOf w]
  rw [mkChain_psi, chainPt_inr_natAdd]

theorem ev_VPow (c : EAChain k r) (cc : Fin r → ℝ) (w : Fin (k + k) → ℝ) :
    (mkChain c cc).ev (∏ j : Fin r, VW (k := k) j) w = Wval c cc (vOf w) := by
  rw [SepChainLocal.ev, map_prod, Wval]
  exact Finset.prod_congr rfl fun j _ => ev_VW c cc w j

theorem ev_WPow (c : EAChain k r) (cc : Fin r → ℝ) (N : ℕ) (w : Fin (k + k) → ℝ) :
    (mkChain c cc).ev (WPow (k := k) (r := r) N) w = Wval c cc (vOf w) ^ N := by
  rw [WPow, SepChainLocal.ev, map_pow]
  congr 1
  exact ev_VPow c cc w


/-! ## §6. Linearity of the chain evaluation and its symbolic derivative -/

theorem SepChainLocal.ev_add {n r : ℕ} (S : SepChainLocal n r) (P Q : EAPoly n r)
    (x : Fin n → ℝ) : S.ev (P + Q) x = S.ev P x + S.ev Q x := by
  simp only [SepChainLocal.ev, map_add]

theorem SepChainLocal.ev_C_mul {n r : ℕ} (S : SepChainLocal n r) (a : ℝ) (Q : EAPoly n r)
    (x : Fin n → ℝ) : S.ev (MvPolynomial.C a * Q) x = a * S.ev Q x := by
  simp only [SepChainLocal.ev, map_mul, MvPolynomial.eval_C]

theorem SepChainLocal.d_add {n r : ℕ} (S : SepChainLocal n r) (l : Fin n) (P Q : EAPoly n r) :
    S.d l (P + Q) = S.d l P + S.d l Q := by
  simp only [SepChainLocal.d, map_add, mul_add, Finset.sum_add_distrib]
  abel

theorem SepChainLocal.d_C_mul {n r : ℕ} (S : SepChainLocal n r) (l : Fin n) (a : ℝ)
    (Q : EAPoly n r) : S.d l (MvPolynomial.C a * Q) = MvPolynomial.C a * S.d l Q := by
  have hinl : MvPolynomial.pderiv (Sum.inl l) (MvPolynomial.C a * Q)
      = MvPolynomial.C a * MvPolynomial.pderiv (Sum.inl l) Q := by
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add]
  have hinr : ∀ j : Fin r, MvPolynomial.pderiv (Sum.inr j) (MvPolynomial.C a * Q)
      = MvPolynomial.C a * MvPolynomial.pderiv (Sum.inr j) Q := by
    intro j
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add]
  rw [SepChainLocal.d, SepChainLocal.d, hinl, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hinr j]
  ring

theorem SepChainLocal.ev_d_add {n r : ℕ} (S : SepChainLocal n r) (l : Fin n) (P Q : EAPoly n r)
    (x : Fin n → ℝ) : S.ev (S.d l (P + Q)) x = S.ev (S.d l P) x + S.ev (S.d l Q) x := by
  rw [SepChainLocal.d_add, SepChainLocal.ev_add]

theorem SepChainLocal.ev_d_C_mul {n r : ℕ} (S : SepChainLocal n r) (l : Fin n) (a : ℝ)
    (Q : EAPoly n r) (x : Fin n → ℝ) :
    S.ev (S.d l (MvPolynomial.C a * Q)) x = a * S.ev (S.d l Q) x := by
  rw [SepChainLocal.d_C_mul, SepChainLocal.ev_C_mul]


end

end Work.WilE3.Realify
