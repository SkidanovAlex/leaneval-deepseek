import Mathlib
import Submission.Work.RPCore.GenFun.Basic

/-!
# The coefficient field of the type-2 form is curl-free (`bvec_curl_free`)

For a near-identity symplectic local diffeomorphism `ψ : PS → PS` (node C1 of the route
design) the vector field

`bvec ψ y = (pfun ψ y - y.2, Qfun ψ y - y.1)`

is the coefficient vector field of the 1-form `β = (Q - q) dP + (p - P) dq` written in the
`(q, P)` chart, i.e. `β = Σ ⱼ bvec ψ ⱼ dy ⱼ`.  Since `ψ` is symplectic one has `dβ = 0`, which in
coordinates is exactly the statement that the Jacobian of `bvec ψ` is symmetric, i.e. that
`fderiv (bvec ψ) y` is self-adjoint for the Euclidean structure.  That is the lemma below;
it is the (finite dimensional) Poincaré-lemma input of C1.

The proof has two independent halves.

* A pointwise linear-algebra computation (`selfadjoint_of_symp`): if `A` is a linear symplectic
  map of `PS` and `C` is a left inverse of `gprojLin A` in the sense that `(C u).1 = u.1` and
  `(A (C u)).2 = u.2`, then the linear map
  `L u = ((C u).2 - u.2, (A (C u)).1 - u.1)` is self-adjoint.  This is a pure computation: the
  symplectic relation for `A` evaluated at `C u`, `C v` is precisely `⟨L u, v⟩ = ⟨L v, u⟩`.
* A derivative computation: `fderiv (bvec ψ) y = L` with `A = fderiv ψ (invMap ψ y)` and
  `C = fderiv (invMap ψ) y`, the latter being the hypothesis `hderiv` of the statement.
-/

namespace Work.RPCore.GenFun

open Work.RPV

noncomputable section

/-- The first-coordinate projection `PS → ℝ²` as a continuous linear map. -/
noncomputable def coordFst : PS →L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ)

/-- The second-coordinate projection `PS → ℝ²` as a continuous linear map. -/
noncomputable def coordSnd : PS →L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ)

@[simp] theorem coordFst_apply (x : PS) : coordFst x = x.1 := rfl

@[simp] theorem coordSnd_apply (x : PS) : coordSnd x = x.2 := rfl

/-- **Pointwise linear algebra.** Let `A` be a symplectic linear endomorphism of `PS` and `C` a
linear map satisfying `(C u).1 = u.1` and `(A (C u)).2 = u.2` for all `u` (i.e. `C` is the
inverse of `gprojLin A`).  Then the linear map
`L u = ((C u).2 - u.2, (A (C u)).1 - u.1)` is self-adjoint for the Euclidean structure `dot`. -/
theorem selfadjoint_of_symp (A : PS →L[ℝ] PS) (C : PS →L[ℝ] PS)
    (hC1 : ∀ u, (C u).1 = u.1) (hC2 : ∀ u, (A (C u)).2 = u.2)
    (hsymp : ∀ a b, symp (A a) (A b) = symp a b) :
    ∀ u v, dot ((coordSnd.comp C - coordSnd).prod (coordFst.comp (A.comp C) - coordFst) u) v
         = dot ((coordSnd.comp C - coordSnd).prod (coordFst.comp (A.comp C) - coordFst) v) u := by
  intro u v
  have h1 := hC1 u; have h2 := hC2 u; have h1' := hC1 v; have h2' := hC2 v
  have hs := hsymp (C u) (C v)
  simp only [symp] at hs
  rw [h1, h2, h1', h2'] at hs
  simp only [dot, ContinuousLinearMap.prod_apply, sub_apply, ContinuousLinearMap.comp_apply,
    coordFst_apply, coordSnd_apply, Prod.fst_sub, Prod.snd_sub]
  nlinarith [hs]

theorem bvec_curl_free (ψ : Work.RPV.PS → Work.RPV.PS) (hψ : ContDiff ℝ 3 ψ)
    (hsymp : ∀ x a b, Work.RPV.symp (fderiv ℝ ψ x a) (fderiv ℝ ψ x b) = Work.RPV.symp a b)
    (hnear : ∀ x, ‖fderiv ℝ ψ x - ContinuousLinearMap.id ℝ Work.RPV.PS‖ ≤ 1 / 4)
    (hderiv : ∀ y : Work.RPV.PS, fderiv ℝ (Work.RPCore.GenFun.invMap ψ) y =
      ↑((Work.RPCore.GenFun.dgequivLin (fderiv ℝ ψ (Work.RPCore.GenFun.invMap ψ y))
        (hnear (Work.RPCore.GenFun.invMap ψ y))).symm)) :
    ∀ y u v : Work.RPV.PS,
      Work.RPCore.GenFun.dot (fderiv ℝ (Work.RPCore.GenFun.bvec ψ) y u) v =
      Work.RPCore.GenFun.dot (fderiv ℝ (Work.RPCore.GenFun.bvec ψ) y v) u := by
  intro y u v
  set A : PS →L[ℝ] PS := fderiv ℝ ψ (invMap ψ y) with hAdef
  have hA : ‖A - 1‖ ≤ 1/4 := by rw [hAdef]; exact hnear (invMap ψ y)
  set C : PS →L[ℝ] PS := ↑((dgequivLin A hA).symm) with hCdef
  have hderivC : fderiv ℝ (invMap ψ) y = C := by rw [hCdef]; exact hderiv y
  -- `C` is not the zero map, since `A` (hence `↑(dgequivLin A hA)`) is a linear equivalence.
  have hCne : C ≠ 0 := by
    intro h
    have hCe0 : (dgequivLin A hA).symm (((1:ℝ), 0), ((0:ℝ), 0)) = 0 := by
      have h1 : C (((1:ℝ), 0), ((0:ℝ), 0)) = 0 := by rw [h]; rfl
      exact h1
    have he0 : (((1:ℝ), 0), ((0:ℝ), 0)) ≠ (0 : PS) := by
      intro hh
      have hh1 : ((1:ℝ) = 0) := by simpa using congrArg (fun x : PS => x.1.1) hh
      exact one_ne_zero hh1
    exact he0 ((ContinuousLinearEquiv.map_eq_zero_iff (dgequivLin A hA).symm).mp hCe0)
  -- `hderiv` pins down `fderiv (invMap ψ) y` as the (nonzero) map `C`, so `invMap ψ` is
  -- differentiable at `y` and its derivative is `C`.
  have hdiff : DifferentiableAt ℝ (invMap ψ) y := by
    by_contra h
    have h0 : fderiv ℝ (invMap ψ) y = 0 := fderiv_zero_of_not_differentiableAt h
    exact hCne (by rw [← hderivC]; exact h0)
  have hC' : HasFDerivAt (invMap ψ) C y := by
    have hh := hdiff.hasFDerivAt
    rwa [hderivC] at hh
  have hψd : HasFDerivAt ψ A (invMap ψ y) := by
    have hh := (((hψ.differentiable (by norm_num)).differentiableAt (x := invMap ψ y))).hasFDerivAt
    rwa [← hAdef] at hh
  have hψinv : HasFDerivAt (fun x => ψ (invMap ψ x)) (A.comp C) y := hψd.comp y hC'
  -- derivative of `bvec ψ` at `y`
  have hbvec : HasFDerivAt (bvec ψ)
      ((coordSnd.comp C - coordSnd).prod (coordFst.comp (A.comp C) - coordFst)) y := by
    have hpfun : HasFDerivAt (fun x => (invMap ψ x).2) (coordSnd.comp C) y := hC'.snd
    have hQfun : HasFDerivAt (fun x => (ψ (invMap ψ x)).1) (coordFst.comp (A.comp C)) y :=
      hψinv.fst
    have h1 : HasFDerivAt (fun x => (invMap ψ x).2 - x.2) (coordSnd.comp C - coordSnd) y :=
      hpfun.sub coordSnd.hasFDerivAt
    have h2 : HasFDerivAt (fun x => (ψ (invMap ψ x)).1 - x.1)
        (coordFst.comp (A.comp C) - coordFst) y :=
      hQfun.sub coordFst.hasFDerivAt
    have hh := h1.prodMk h2
    change HasFDerivAt (fun x => ((invMap ψ x).2 - x.2, (ψ (invMap ψ x)).1 - x.1))
        ((coordSnd.comp C - coordSnd).prod (coordFst.comp (A.comp C) - coordFst)) y
    exact hh
  -- the two structural facts about `C`: it preserves the first coordinate, and `A ∘ C`
  -- preserves the second.  Both come from `gprojLin A ∘ C = id`.
  have hEv : ∀ v : PS, (dgequivLin A hA) v = (v.1, (A v).2) := by
    intro v
    show (↑(dgequivLin A hA) : PS →L[ℝ] PS) v = (v.1, (A v).2)
    rw [coe_dgequivLin, gprojLin_apply]
  have hC1 : ∀ u, (C u).1 = u.1 := by
    intro u
    have hh := ContinuousLinearEquiv.apply_symm_apply (dgequivLin A hA) u
    rw [hEv] at hh
    have := congrArg Prod.fst hh
    simpa [hCdef] using this
  have hC2 : ∀ u, (A (C u)).2 = u.2 := by
    intro u
    have hh := ContinuousLinearEquiv.apply_symm_apply (dgequivLin A hA) u
    rw [hEv] at hh
    have := congrArg Prod.snd hh
    simpa [hCdef] using this
  rw [hbvec.fderiv]
  exact selfadjoint_of_symp A C hC1 hC2
    (by intro a b; rw [hAdef]; exact hsymp (invMap ψ y) a b) u v

end

end Work.RPCore.GenFun
