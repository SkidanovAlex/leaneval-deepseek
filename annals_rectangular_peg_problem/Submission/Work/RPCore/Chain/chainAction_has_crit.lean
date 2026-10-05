import Mathlib
import Submission.Work.RPCore.Chain.C4Defs
import Submission.Work.RPCore.Chain.ref_action_quadratic
import Submission.Work.RPCore.Chain.ref_shift_quadratic
import Submission.Work.RPCore.Chain.chainModel_operator
import Submission.Work.RPCore.Chain.chainCoordEquiv
import Submission.Work.RPCore.Chain.BvForm_radical_quotient
import Submission.Work.RPCore.Chain.chainAction_contDiff
import Submission.Work.RPCore.Chain.chainPert_bounds
import Submission.Work.RPCore.Chain.chainAction_add_diagVec
import Submission.Work.RPCore.Saddle.saddle_point_periodic
import Submission.Work.RPCore.Flow.fderiv_bounded_of_periodic_on_slab

/-!
# C4: the perturbed chain action has a critical point

This file assembles the saddle-point theorem `saddle_point_periodic` into the existence of a
critical point of the *perturbed* broken-geodesic chain action `chainAction n W`, where `n = 3N-1`
and the generating functions `W j` agree with the reference ones `refGF N δ` on the middle block
`N ≤ j < 2N` and are compactly supported in the slab off it.

The reference action `Φ₀ = chainAction n (refGF N δ)` is the quadratic-plus-linear function
`z ↦ BvForm n N δ z z / 2 + Lav n N δ z` (`ref_action_quadratic`), and translating by the shift
`w` of `ref_shift_quadratic` removes its linear part:
`Φ₀ (z + w) = BvForm n N δ z z / 2 + Φ₀ w`.

Choose a linear equivalence `e : ℝ × EuclideanSpace ℝ (Fin M) ≃ₗ[ℝ] ChainSp n` carrying `(1,0)`
to `diagVec n` (`chainCoordEquiv`) and let `A` be the self-adjoint injective operator representing
the restriction of the polar form to the hyperplane `e ({0} × E)` (`chainModel_operator`).  Since
`diagVec n` lies in the radical of `BvForm n N δ` (`BvForm_radical_quotient`), the reference
action in the coordinates `p ↦ e p + w` is

`Φ₀ (e p + w) = ⟪A p.2, p.2⟫ / 2 + Φ₀ w`,

a pure quadratic form of the injective operator `A` in the second variable alone.  The difference
`V = Φ - Φ₀` is supported off the middle block, hence bounded with bounded derivative and `C²`
(`chainPert_bounds`), and the action is `2π`-periodic in the angular direction
(`chainAction_add_diagVec`).  All the hypotheses of `saddle_point_periodic` are therefore
satisfied by `F (p) = Φ (e p + w)`, and a critical point of `F` is transported back along the
affine isomorphism `g : p ↦ e p + w` to a critical point of `Φ`.
-/

open Real

open scoped BigOperators

namespace Work.RPCore.Chain

open Work.RPV

/-- The derivative of the diagonal quadratic form of a self-adjoint operator on
`ℝ × EuclideanSpace ℝ (Fin M)`: `p ↦ ⟪A p.2, p.2⟫ / 2` has derivative
`(0).coprod (innerSL ℝ (A p.2))`. -/
theorem hasFDerivAt_inner_self_symm {M : ℕ}
    (A : EuclideanSpace ℝ (Fin M) →L[ℝ] EuclideanSpace ℝ (Fin M))
    (hA : ∀ v w, inner ℝ (A v) w = inner ℝ v (A w)) (p : ℝ × EuclideanSpace ℝ (Fin M)) :
    HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin M) => inner ℝ (A q.2) q.2 / 2)
      ((0 : ℝ →L[ℝ] ℝ).coprod (innerSL ℝ (A p.2))) p := by
  have h1 : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin M) => q.2)
      (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin M))) p :=
    (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin M))).hasFDerivAt
  have h2 : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin M) => A q.2)
      (A.comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin M)))) p :=
    A.hasFDerivAt.comp p h1
  have h3 : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin M) => inner ℝ (A q.2) q.2)
      ((fderivInnerCLM ℝ (A p.2, p.2)).comp ((A.comp (ContinuousLinearMap.snd ℝ ℝ
        (EuclideanSpace ℝ (Fin M)))).prod
        (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin M))))) p := by
    have hh := h2.inner ℝ h1
    simpa [ContinuousLinearMap.compSL_apply] using hh
  have hCLM : (1/2:ℝ) • ((fderivInnerCLM ℝ (A p.2, p.2)).comp
      ((A.comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin M)))).prod
        (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin M)))))
      = (0 : ℝ →L[ℝ] ℝ).coprod (innerSL ℝ (A p.2)) := by
    refine ContinuousLinearMap.ext (fun u => ?_)
    obtain ⟨a, v⟩ := u
    simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coprod_apply, zero_apply, zero_add, fderivInnerCLM_apply]
    simp only [ContinuousLinearMap.coe_snd', innerSL_apply_apply, smul_eq_mul]
    rw [hA v p.2, real_inner_comm v (A p.2)]
    ring
  have h4 : HasFDerivAt
      (fun q : ℝ × EuclideanSpace ℝ (Fin M) => (1/2:ℝ) * inner ℝ (A q.2) q.2)
      ((1/2:ℝ) • ((fderivInnerCLM ℝ (A p.2, p.2)).comp ((A.comp
        (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin M)))).prod
        (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin M)))))) p :=
    h3.const_mul ((1:ℝ)/2)
  rw [hCLM] at h4
  convert h4 using 1
  funext u
  ring

set_option maxHeartbeats 800000 in
theorem chainAction_has_crit (n N : ℕ) (hN : 1 ≤ N) (hn : n = 3 * N - 1) (δ : ℝ)
    (hδ0 : 0 < δ) (hδπ : δ < π / 2) (hθπ : (N : ℝ) * δ < π)
    (W : Fin (n + 1) → Work.RPV.PS → ℝ)
    (hWc : ∀ j, ContDiff ℝ 3 (W j))
    (hWmid : ∀ j : Fin (n + 1), Work.RPCore.Chain.midBlock N (j : ℕ) → W j = Work.RPV.Wrot δ)
    (hWper : ∀ j x, W j (Work.RPV.Tk 1 x) = W j x)
    (hWsup : ∀ j : Fin (n + 1), ¬ Work.RPCore.Chain.midBlock N (j : ℕ) →
      ∃ R : ℝ, ∀ x, R ≤ |x.1.1| + |x.2.1| + |x.2.2| → W j x = 0) :
    ∃ z : Work.RPCore.Chain.ChainSp n,
      fderiv ℝ (fun z => Work.RPV.chainAction n W z.1 z.2) z = 0 := by
  -- The two nondegeneracy conditions on `δ` coming from the hypotheses `δ < π/2`, `N δ < π`.
  have hcos : Real.cos δ ≠ 0 := by
    apply ne_of_gt
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have := Real.pi_pos; linarith
    · exact hδπ
  have hsin : Real.sin ((N : ℝ) * δ) ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi
    · have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      nlinarith
    · exact hθπ
  -- Coordinates adapted to the kernel line `ℝ ∙ diagVec n`, and the model operator `A`.
  obtain ⟨M, e, he⟩ := chainCoordEquiv n
  obtain ⟨A, hAsym, hAinj, hABv⟩ := chainModel_operator n N hN hn δ hcos hsin e he
  -- The shift removing the linear part of the reference action.
  obtain ⟨w, hwlin, hwval⟩ := ref_shift_quadratic n N hN hn δ hcos hsin
  -- `e` written in coordinates: `e (a,v) = a • diagVec n + e (0,v)`.
  have he_apply : ∀ (a : ℝ) (v : EuclideanSpace ℝ (Fin M)),
      e (a, v) = a • diagVec n + e (0, v) := by
    intro a v
    have h1 : ((a, v) : ℝ × EuclideanSpace ℝ (Fin M)) =
        a • ((1:ℝ), (0 : EuclideanSpace ℝ (Fin M))) + ((0:ℝ), v) := by
      ext <;> simp
    rw [h1, map_add, map_smul, he]
  -- The reference action at the shifted point is the pure quadratic form of `A`.
  have hQ : ∀ (p : ℝ × EuclideanSpace ℝ (Fin M)),
      BvForm n N δ (e p) (e p) = inner ℝ (A p.2) p.2 := by
    intro p
    obtain ⟨a, v⟩ := p
    rw [he_apply a v, BvForm_radical_quotient n N δ a a (e (0, v)) (e (0, v))]
    exact (hABv v v).symm
  have hQ0 : ∀ (p : ℝ × EuclideanSpace ℝ (Fin M)),
      Work.RPV.chainAction n (fun j => refGF N δ (j:ℕ)) (e p + w).1 (e p + w).2
        = inner ℝ (A p.2) p.2 / 2
          + Work.RPV.chainAction n (fun j => refGF N δ (j:ℕ)) w.1 w.2 := by
    intro p
    rw [hwval (e p + w), show e p + w - w = e p from add_sub_cancel_right (e p) w, hQ p]
  -- The perturbation and its uniform bounds.
  obtain ⟨C, hC0, hVc, hVb, hVd⟩ := chainPert_bounds n N δ W hWc hWmid hWper hWsup
  set V : ChainSp n → ℝ := fun z => Work.RPV.chainAction n W z.1 z.2
      - Work.RPV.chainAction n (fun j => refGF N δ (j:ℕ)) z.1 z.2 with hVdef
  -- The affine chart `g` and the three functions on `ℝ × E`.
  let eC : (ℝ × EuclideanSpace ℝ (Fin M)) →L[ℝ] ChainSp n := e.toContinuousLinearEquiv
  let g : ℝ × EuclideanSpace ℝ (Fin M) → ChainSp n := fun p => e p + w
  let F : ℝ × EuclideanSpace ℝ (Fin M) → ℝ :=
    (fun z : ChainSp n => Work.RPV.chainAction n W z.1 z.2) ∘ g
  let H0 : ℝ × EuclideanSpace ℝ (Fin M) → ℝ := fun p => inner ℝ (A p.2) p.2 / 2
      + Work.RPV.chainAction n (fun j => refGF N δ (j:ℕ)) w.1 w.2
  let Vg : ℝ × EuclideanSpace ℝ (Fin M) → ℝ := V ∘ g
  -- Smoothness and derivative of `g`.
  have hgc : ContDiff ℝ 2 g := by
    show ContDiff ℝ 2 (fun p : ℝ × EuclideanSpace ℝ (Fin M) => e p + w)
    exact (eC.contDiff (n := 2)).add contDiff_const
  have hgdiff : ∀ p : ℝ × EuclideanSpace ℝ (Fin M), DifferentiableAt ℝ g p :=
    fun p => (hgc.differentiable (by norm_num)).differentiableAt
  have hgfd : ∀ p : ℝ × EuclideanSpace ℝ (Fin M), fderiv ℝ g p = eC := by
    intro p
    have h1 : HasFDerivAt (fun p : ℝ × EuclideanSpace ℝ (Fin M) => eC p + w) eC p :=
      eC.hasFDerivAt.add_const w
    have h2 : HasFDerivAt g eC p := h1
    exact h2.fderiv
  -- The perturbation as a function on `ℝ × E`, with its bounds.
  have hVgc : ContDiff ℝ 2 Vg := hVc.comp hgc
  have hVgb : ∀ p : ℝ × EuclideanSpace ℝ (Fin M), |Vg p| ≤ C := fun p => hVb (g p)
  have hVgd : ∀ p : ℝ × EuclideanSpace ℝ (Fin M), ‖fderiv ℝ Vg p‖ ≤ C * ‖eC‖ := by
    intro p
    have hdiff : fderiv ℝ Vg p = (fderiv ℝ V (e p + w)).comp eC := by
      have hcomp := fderiv_comp (f := g) p (g := V)
        (hVc.differentiable (by norm_num)).differentiableAt (hgdiff p)
      rw [hcomp, hgfd p]
    rw [hdiff]
    calc ‖(fderiv ℝ V (e p + w)).comp eC‖
        ≤ ‖fderiv ℝ V (e p + w)‖ * ‖eC‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * ‖eC‖ := mul_le_mul_of_nonneg_right (hVd (e p + w)) (norm_nonneg _)
  -- `F` is the quadratic model `H0` plus the perturbation `Vg`.
  have hFdecomp : ∀ p, F p = H0 p + Vg p := by
    intro p
    have h1 : F p = V (e p + w)
        + Work.RPV.chainAction n (fun j => refGF N δ (j:ℕ)) (e p+w).1 (e p+w).2 := by
      simp only [F, V, g, Function.comp_apply]; ring
    rw [h1, hQ0 p]
    simp only [H0, Vg, V, g, Function.comp_apply]
    ring
  have hFc : ContDiff ℝ 2 F := (chainAction_contDiff n W hWc).comp hgc
  -- `F` is `2π`-periodic in the angular variable.
  have hper : ∀ (a : ℝ) (v : EuclideanSpace ℝ (Fin M)), F (a + 2*Real.pi, v) = F (a, v) := by
    intro a v
    have h1 : e (a + 2*Real.pi, v) + w = (e (a, v) + w) + (2*Real.pi) • diagVec n := by
      rw [he_apply (a + 2*Real.pi) v, he_apply a v, add_smul]
      abel
    simp only [F, g, Function.comp_apply]
    rw [h1, chainAction_add_diagVec n W hWper (e (a,v) + w)]
  -- The derivative of the model `H0`.
  have hH0fd : ∀ p : ℝ × EuclideanSpace ℝ (Fin M),
      fderiv ℝ H0 p = (0 : ℝ →L[ℝ] ℝ).coprod (innerSL ℝ (A p.2)) := by
    intro p
    have h := hasFDerivAt_inner_self_symm A hAsym p
    have h2 : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin M) => inner ℝ (A q.2) q.2 / 2
        + Work.RPV.chainAction n (fun j => refGF N δ (j:ℕ)) w.1 w.2)
        ((0 : ℝ →L[ℝ] ℝ).coprod (innerSL ℝ (A p.2))) p := HasFDerivAt.add_const _ h
    simpa only [H0] using h2.fderiv
  have hH0diff : ∀ p : ℝ × EuclideanSpace ℝ (Fin M), DifferentiableAt ℝ H0 p := by
    intro p
    have h2 : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin M) => inner ℝ (A q.2) q.2 / 2
        + Work.RPV.chainAction n (fun j => refGF N δ (j:ℕ)) w.1 w.2)
        ((0 : ℝ →L[ℝ] ℝ).coprod (innerSL ℝ (A p.2))) p :=
      HasFDerivAt.add_const _ (hasFDerivAt_inner_self_symm A hAsym p)
    have h3 := h2.differentiableAt
    simpa only [H0] using h3
  have hVgdiff : ∀ p : ℝ × EuclideanSpace ℝ (Fin M), DifferentiableAt ℝ Vg p :=
    fun p => (hVgc.differentiable (by norm_num)).differentiableAt
  -- The two hypotheses (C) of `saddle_point_periodic`.
  have hCval : ∀ (a : ℝ) (v : EuclideanSpace ℝ (Fin M)),
      |F (a, v) - inner ℝ (A v) v / 2| ≤
        max (|Work.RPV.chainAction n (fun j => refGF N δ (j:ℕ)) w.1 w.2| + C) (C * ‖eC‖) := by
    intro a v
    have h1 : F (a, v) - inner ℝ (A (a, v).2) (a, v).2 / 2
        = Work.RPV.chainAction n (fun j => refGF N δ (j:ℕ)) w.1 w.2 + Vg (a, v) := by
      rw [hFdecomp (a,v)]; simp only [H0]; ring
    rw [h1]
    calc |Work.RPV.chainAction n (fun j => refGF N δ (j:ℕ)) w.1 w.2 + Vg (a,v)|
        ≤ |Work.RPV.chainAction n (fun j => refGF N δ (j:ℕ)) w.1 w.2| + |Vg (a,v)| :=
          abs_add_le _ _
      _ ≤ |Work.RPV.chainAction n (fun j => refGF N δ (j:ℕ)) w.1 w.2| + C := by
          linarith [hVgb (a,v)]
      _ ≤ max (|Work.RPV.chainAction n (fun j => refGF N δ (j:ℕ)) w.1 w.2| + C) (C * ‖eC‖) :=
            le_max_left _ _
  have hCder : ∀ (a : ℝ) (v : EuclideanSpace ℝ (Fin M)),
      ‖fderiv ℝ F (a, v) - (0 : ℝ →L[ℝ] ℝ).coprod (innerSL ℝ (A v))‖
        ≤ max (|Work.RPV.chainAction n (fun j => refGF N δ (j:ℕ)) w.1 w.2| + C) (C * ‖eC‖) := by
    intro a v
    have hfd : fderiv ℝ F (a,v) = fderiv ℝ H0 (a,v) + fderiv ℝ Vg (a,v) := by
      have h1 : F = fun p => H0 p + Vg p := funext hFdecomp
      rw [h1]
      exact fderiv_add (hH0diff (a,v)) (hVgdiff (a,v))
    rw [hfd, hH0fd (a,v), add_sub_cancel_left]
    calc ‖fderiv ℝ Vg (a,v)‖ ≤ C * ‖eC‖ := hVgd (a,v)
      _ ≤ max (|Work.RPV.chainAction n (fun j => refGF N δ (j:ℕ)) w.1 w.2| + C) (C * ‖eC‖) :=
          le_max_right _ _
  -- The saddle-point theorem.
  have hPd : (0:ℝ) < 2 * Real.pi := by positivity
  obtain ⟨p, hp⟩ := Work.RPCore.Saddle.saddle_point_periodic F hFc (2 * Real.pi) hPd hper A hAsym
    hAinj (max (|Work.RPV.chainAction n (fun j => refGF N δ (j:ℕ)) w.1 w.2| + C) (C * ‖eC‖))
    hCval hCder
  -- Transport the critical point back along the affine isomorphism `g`.
  refine ⟨g p, ?_⟩
  have hPhidiff : DifferentiableAt ℝ (fun z : ChainSp n => Work.RPV.chainAction n W z.1 z.2)
      (g p) :=
    (chainAction_contDiff n W hWc).differentiable (by norm_num) |>.differentiableAt
  have hFcomp : fderiv ℝ F p
      = (fderiv ℝ (fun z : ChainSp n => Work.RPV.chainAction n W z.1 z.2) (g p)).comp eC := by
    have hcomp := fderiv_comp (f := g) p
      (g := fun z : ChainSp n => Work.RPV.chainAction n W z.1 z.2) hPhidiff (hgdiff p)
    rw [hcomp, hgfd p]
  have hcrit : (fderiv ℝ (fun z : ChainSp n => Work.RPV.chainAction n W z.1 z.2) (g p)).comp eC
      = 0 := by
    rw [← hFcomp]; exact hp
  refine ContinuousLinearMap.ext (fun y => ?_)
  have h2 := congrArg (fun (L : (ℝ × EuclideanSpace ℝ (Fin M)) →L[ℝ] ℝ) =>
    L ((e.toContinuousLinearEquiv).symm y)) hcrit
  simp only [ContinuousLinearMap.comp_apply, zero_apply] at h2
  have h3 : eC ((e.toContinuousLinearEquiv).symm y) = y :=
    ContinuousLinearEquiv.apply_symm_apply _ _
  rw [h3] at h2
  simpa using h2

end Work.RPCore.Chain
