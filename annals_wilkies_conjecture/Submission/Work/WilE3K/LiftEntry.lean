/-
  annals_wilkies_conjecture, AREA E3K: the entrywise identity comparing the lifted Jacobian with
  the Jacobian of the original separable-chain system.

  The chain rule applied to `x ↦ E.evP i (liftPoint S E x) = S.ev (f i) x` (an identity of
  functions) shows that the Schur complement of the lifted Jacobian — the matrix of the derivative
  of the `i`-th lifted equation along the `free` directions plus the `tan`-correction — is exactly
  the original Jacobian `(S.ev (S.d a (f i)) x)`.
-/
import Submission.Work.WilE3K.LiftJac
import Submission.Work.WilE3K.ContAux
import Submission.Work.WilE9.EaD.eaD_hasFDerivAt
import Submission.Work.WilE3.Realify.SepChainLocal_fderiv_ev
import Submission.Work.WilE3.Realify.Defs
import Mathlib

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {N rt n re r : ℕ}

/-! ## §1. The derivative of `E.evalPoly` -/

theorem evalPoly_hasFDerivAt_aux (E : ETData N rt n re) (Q : EAPoly (N + 1) re)
    (z : Fin (N + 1) → ℝ) :
    HasFDerivAt (fun w : Fin (N + 1) → ℝ => E.evalPoly Q w)
      (∑ c : Fin (N + 1), (E.evalPoly (E.dPoly c Q) z) •
        (ContinuousLinearMap.proj c : (Fin (N + 1) → ℝ) →L[ℝ] ℝ)) z := by
  have h := Work.WilE9.EaD.eaD_hasFDerivAt E.toChain Q z
  have hfd : (∑ c : Fin (N + 1), (eaEval E.toChain (eaD E.toChain c Q) z) •
        (ContinuousLinearMap.proj c : (Fin (N + 1) → ℝ) →L[ℝ] ℝ))
      = ∑ c : Fin (N + 1), (E.evalPoly (E.dPoly c Q) z) •
        (ContinuousLinearMap.proj c : (Fin (N + 1) → ℝ) →L[ℝ] ℝ) := by
    apply Finset.sum_congr rfl
    intro c _
    rw [ETData.evalPoly_eq_eaEval, ETData.dPoly_eq_eaD]
  have hfun : (fun w : Fin (N + 1) → ℝ => E.evalPoly Q w) = fun w => eaEval E.toChain Q w := by
    funext w; exact E.evalPoly_eq_eaEval Q w
  simpa only [hfun] using h.congr_fderiv hfd

/-! ## §2. Splitting a sum over the ambient coordinates -/

theorem sum_coords (E : ETData N rt n re) {M : Type*} [AddCommMonoid M] (F : Fin (N + 1) → M) :
    (∑ c, F c) = (∑ a : Fin n, F (E.freeCoord a)) + ∑ p : Fin rt, F (E.tanCoord p) := by
  rw [← Equiv.sum_comp (coordEquiv E) F, Fintype.sum_sum_type]
  simp only [coordEquiv_inl, coordEquiv_inr, add_comm]

/-! ## §3. The evaluation identity -/

theorem evP_liftPoint_self {S : Work.WilE3.SepChainLocal n r} (htype : Lift.IsET S)
    (hn : Lift.rt S + n = (Lift.rt S + n - 1) + 1) (f : Fin n → EAPoly n r)
    (k : Fin (Lift.rt S) → ℤ) (i : Fin n) (x : Fin n → ℝ) :
    (Lift.liftET S hn f k).evP i (Lift.liftPoint S (Lift.liftET S hn f k) x) = S.ev (f i) x := by
  set z := Lift.liftPoint S (Lift.liftET S hn f k) x with hz
  have hass : (Sum.elim z (fun q => Real.exp ((Lift.liftET S hn f k).ellChain q z)))
      ∘ (Lift.xi hn (Lift.cls S)) = Sum.elim x (fun j => S.psi j x) := by
    funext v
    rcases v with a' | j
    · rw [Function.comp_apply, Lift.xi_inl hn (Lift.cls S) a', Sum.elim_inl]
      change z ((Lift.liftET S hn f k).freeCoord a') = x a'
      rw [hz, Lift.liftPoint_free]
    · rcases hcl : Lift.cls S j with p | q
      · have hjp : j = Lift.tanIdx S p := Lift.eq_tanIdx_of_cls_eq_inl S hcl
        subst hjp
        rw [Function.comp_apply, Lift.xi_inr_inl hn (Lift.cls S) (Lift.tanIdx S p) p
          (Lift.cls_tanIdx S p), Sum.elim_inl]
        change z ((Lift.liftET S hn f k).tanCoord p) = S.psi (Lift.tanIdx S p) x
        rw [hz, Lift.liftPoint_tan, Lift.liftT, Lift.psi_eq_phi_ell, Lift.phi_tanIdx]
      · have hjq : j = Lift.expIdx S q := Lift.eq_expIdx_of_cls_eq_inr S hcl
        subst hjq
        rw [Function.comp_apply, Lift.xi_inr_inr hn (Lift.cls S) (Lift.expIdx S q) q
          (Lift.cls_expIdx S q), Sum.elim_inr]
        have hchain : (Lift.liftET S hn f k).ellChain q
            (Lift.liftPoint S (Lift.liftET S hn f k) x) = Lift.ell S (Lift.expIdx S q) x := by
          simp only [ETData.ellChain, Lift.liftET, Lift.liftE, Lift.liftCa, Lift.liftCb,
            Lift.liftPoint_free, Lift.ell]
        rw [hz, hchain, Sum.elim_inr, Lift.psi_eq_phi_ell, Lift.phi_expIdx S htype]
  have hG : (Lift.liftET S hn f k).G i = MvPolynomial.rename (Lift.xi hn (Lift.cls S)) (f i) :=
    rfl
  rw [ETData.evP, ETData.evalPoly, hG, MvPolynomial.eval_rename, hass,
    Work.WilE3.SepChainLocal.ev]

/-! ## §4. The derivative of the lift applied to a basis vector -/

theorem liftLin_apply (S : Work.WilE3.SepChainLocal n r)
    (E : ETData (Lift.rt S + n - 1) (Lift.rt S) n (Lift.re S)) (x : Fin n → ℝ)
    (v : Fin n → ℝ) (c : Fin ((Lift.rt S + n - 1) + 1)) :
    liftLin S E x v c = liftLinComp S E x c v := by
  rw [liftLin, ContinuousLinearMap.pi_apply]

theorem liftLin_single_tan (S : Work.WilE3.SepChainLocal n r)
    (E : ETData (Lift.rt S + n - 1) (Lift.rt S) n (Lift.re S)) (x : Fin n → ℝ) (a : Fin n)
    (p : Fin (Lift.rt S)) :
    liftLin S E x (Pi.single a (1 : ℝ) : Fin n → ℝ) (E.tanCoord p)
      = (1 + (Lift.liftT S x p) ^ 2) * S.a (Lift.tanIdx S p) a := by
  rw [liftLin_apply, liftLinComp_tan S E x (E.tanCoord p) (by simpa using p.isLt)]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single a]
  · simp only [Pi.single_eq_same, mul_one]
    rfl
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro ha; exact absurd (Finset.mem_univ a) ha

theorem liftLin_single_free (S : Work.WilE3.SepChainLocal n r)
    (E : ETData (Lift.rt S + n - 1) (Lift.rt S) n (Lift.re S)) (x : Fin n → ℝ) (a a' : Fin n) :
    liftLin S E x (Pi.single a (1 : ℝ) : Fin n → ℝ) (E.freeCoord a')
      = (Pi.single a (1 : ℝ) : Fin n → ℝ) a' := by
  rw [liftLin_apply, liftLinComp_free S E x (E.freeCoord a')
    (by simp)]
  simp only [ContinuousLinearMap.proj_apply, ETData.freeIndex_freeCoord]

/-! ## §5. The entrywise identity -/

theorem ev_d_eq {S : Work.WilE3.SepChainLocal n r} (htype : Lift.IsET S)
    (hn : Lift.rt S + n = (Lift.rt S + n - 1) + 1)
    (f : Fin n → EAPoly n r) (k : Fin (Lift.rt S) → ℤ) (x₀ : Fin n → ℝ)
    (hx : ∀ j, Lift.ell S j x₀ ∈ S.dom j) (i a : Fin n) :
    S.ev (S.d a (f i)) x₀ =
        (Lift.liftET S hn f k).evalPoly
            ((Lift.liftET S hn f k).dPoly ((Lift.liftET S hn f k).freeCoord a)
              ((Lift.liftET S hn f k).G i))
            (Lift.liftPoint S (Lift.liftET S hn f k) x₀)
        + ∑ p : Fin (Lift.rt S), (Lift.liftET S hn f k).evalPoly
            ((Lift.liftET S hn f k).dPoly ((Lift.liftET S hn f k).tanCoord p)
              ((Lift.liftET S hn f k).G i))
            (Lift.liftPoint S (Lift.liftET S hn f k) x₀)
          * ((1 + ((Lift.liftPoint S (Lift.liftET S hn f k) x₀)
              ((Lift.liftET S hn f k).tanCoord p)) ^ 2) * S.a (Lift.tanIdx S p) a) := by
  set E := Lift.liftET S hn f k with hE
  set z := Lift.liftPoint S E x₀ with hz
  have hEv : HasFDerivAt (fun w : Fin ((Lift.rt S + n - 1) + 1) → ℝ => E.evP i w)
      (∑ c : Fin ((Lift.rt S + n - 1) + 1), E.evalPoly (E.dPoly c (E.G i)) z •
        (ContinuousLinearMap.proj c : (Fin ((Lift.rt S + n - 1) + 1) → ℝ) →L[ℝ] ℝ)) z :=
    evalPoly_hasFDerivAt_aux E (E.G i) z
  have hLift : HasFDerivAt (fun x => Lift.liftPoint S E x) (liftLin S E x₀) x₀ :=
    hasFDerivAt_liftPoint S htype E x₀ hx
  have h1 : HasFDerivAt (fun x => E.evP i (Lift.liftPoint S E x))
      ((∑ c : Fin ((Lift.rt S + n - 1) + 1), E.evalPoly (E.dPoly c (E.G i)) z •
        (ContinuousLinearMap.proj c : (Fin ((Lift.rt S + n - 1) + 1) → ℝ) →L[ℝ] ℝ)).comp
        (liftLin S E x₀)) x₀ := hEv.comp x₀ hLift
  have h2 : HasFDerivAt (S.ev (f i)) (Work.WilE3.Realify.grad S (f i) x₀) x₀ :=
    Work.WilE3.Realify.SepChainLocal_fderiv_ev S (f i) x₀ hx
  have hfun : (fun x => E.evP i (Lift.liftPoint S E x)) = S.ev (f i) := by
    funext x
    exact evP_liftPoint_self (S := S) htype hn f k i x
  have huniq : (∑ c : Fin ((Lift.rt S + n - 1) + 1), E.evalPoly (E.dPoly c (E.G i)) z •
        (ContinuousLinearMap.proj c : (Fin ((Lift.rt S + n - 1) + 1) → ℝ) →L[ℝ] ℝ)).comp
        (liftLin S E x₀) = Work.WilE3.Realify.grad S (f i) x₀ := by
    rw [← h1.fderiv, hfun, h2.fderiv]
  have hval := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single a (1 : ℝ))) huniq
  rw [ContinuousLinearMap.comp_apply] at hval
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul] at hval
  have hzt : ∀ p : Fin (Lift.rt S), z (E.tanCoord p) = Lift.liftT S x₀ p :=
    fun p => Lift.liftPoint_tan S E x₀ p
  have hL : (∑ c : Fin ((Lift.rt S + n - 1) + 1), E.evalPoly (E.dPoly c (E.G i)) z
        * ((liftLin S E x₀ (Pi.single a (1 : ℝ))) c))
      = E.evalPoly (E.dPoly (E.freeCoord a) (E.G i)) z
        + ∑ p : Fin (Lift.rt S), E.evalPoly (E.dPoly (E.tanCoord p) (E.G i)) z
            * ((1 + (z (E.tanCoord p)) ^ 2) * S.a (Lift.tanIdx S p) a) := by
    rw [sum_coords (E := E)]
    congr 1
    · rw [Finset.sum_eq_single a]
      · rw [liftLin_single_free, Pi.single_eq_same, mul_one]
      · intro b _ hb
        rw [liftLin_single_free, Pi.single_eq_of_ne hb, mul_zero]
      · intro ha; exact absurd (Finset.mem_univ a) ha
    · apply Finset.sum_congr rfl
      intro p _
      rw [liftLin_single_tan, ← hzt p]
  have hR : Work.WilE3.Realify.grad S (f i) x₀ (Pi.single a (1 : ℝ)) = S.ev (S.d a (f i)) x₀ := by
    rw [Work.WilE3.Realify.grad_apply, Finset.sum_eq_single a]
    · rw [Pi.single_eq_same, mul_one]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  rw [hL, hR] at hval
  exact hval.symm

end Work.WilE3K
