import Mathlib
import Submission.Work.NN.Newton.pushforward_setup
import Submission.Work.NN.Newton.nearInverseThin
import Submission.Work.NN.Newton.Minv_holderNorm_one_le
import Submission.Work.NN.Newton.phiNormBounds
import Submission.Work.NN.Newton.DvCLM_data_le
import Submission.Work.NN.Newton.contDiffOn_Aop

/-!
# The pushed-forward almost complex structure

Given a smooth perturbation `A` of the standard structure `Jstd` on the polydisc `Pd n r` which is
almost complex (`(Jstd + A)² = -1`) and a smooth correction `v : Fin n → ℂⁿ → ℂ` that is small in
`C^{2,α}` on the slightly smaller polydisc `Pd n (r(1-δ))`, this file builds the inverse `Ψ` of the
near-identity map `Φ = id - v` on the inner polydisc `Pd n (r(1-2δ))` together with the
pushed-forward perturbation

  `A' ζ = Aop A v (Ψ ζ)`

which is again smooth, almost complex, and intertwines the two structures along `Φ`.

The construction has two independent halves:

* the *analytic* half is `nearInverseThin`: it produces `Ψ` with all the norm and Hölder bounds,
  from the `C^{2,α}` smallness of `v`;
* the *algebraic* half re-expresses `Aop`, via the inverse relation `Minv v z = (1 - DvCLM v z)⁻¹`,
  as the conjugation `Jstd + A' = dΦ · (Jstd + A) · dΦ⁻¹`, from which the intertwining and the
  almost-complexity follow formally.
-/

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Newton

open Work.NN.Core

/-! ## The algebra of the push-forward -/

/-- A purely ring-theoretic identity. Let `d`, `M` be mutual inverses of each other (`M d = 1` and
`d M = 1`), `J` the standard structure and `A` a perturbation with `(J + A)² = -1`. Then the
conjugate `J + ((d (J + A) - J d) M)` satisfies the two conjugation identities and is again almost
complex. This is `Aop` with `d = dΦ = 1 - DvCLM`, `M = Minv = d⁻¹`, `J = Jstd`. -/
lemma conj_identity_ring {R : Type*} [Ring R] (d M J A : R)
    (hu1 : M * d = 1) (hu2 : d * M = 1) (hAC : (J + A) * (J + A) = -1) :
    (J + ((d * (J + A) - J * d) * M) = d * (J + A) * M) ∧
    ((J + ((d * (J + A) - J * d) * M)) * d = d * (J + A)) ∧
    ((J + ((d * (J + A) - J * d) * M)) * (J + ((d * (J + A) - J * d) * M)) = -1) := by
  have hA : J + ((d * (J + A) - J * d) * M) = d * (J + A) * M := by
    rw [sub_mul]; simp only [mul_assoc, hu2, mul_one]; abel
  refine ⟨hA, ?_, ?_⟩
  · rw [hA, mul_assoc, hu1, mul_one]
  · rw [hA]
    calc d * (J + A) * M * (d * (J + A) * M)
        = d * (J + A) * (M * d) * (J + A) * M := by noncomm_ring
      _ = d * (J + A) * 1 * (J + A) * M := by rw [hu1]
      _ = d * ((J + A) * (J + A)) * M := by noncomm_ring
      _ = d * (-1) * M := by rw [hAC]
      _ = -(d * M) := by noncomm_ring
      _ = -1 := by rw [hu2]

/-- `Aop A v z`, written in terms of `d = 1 - DvCLM v z` and `M = Minv v z`. -/
lemma Aop_eq {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n) (v : Fin n → Cn n → ℂ) (z : Cn n) :
    Aop A v z = ((1 - DvCLM v z) * (Jc n + A z) - Jc n * (1 - DvCLM v z)) * Minv v z := by
  rw [Aop, Bop, JstdCn_apply_eq]; rfl

/-- The almost-complexity hypothesis, in the ring of endomorphisms. -/
lemma ring_AC_of_pointwise {n : ℕ} {A : Cn n → Cn n →L[ℝ] Cn n} {z : Cn n}
    (hAC : ∀ u : Cn n, (JstdCn n + A) z ((JstdCn n + A) z u) = -u) :
    (Jc n + A z) * (Jc n + A z) = -1 := by
  have h1 : (JstdCn n + A) z = Jc n + A z := by
    show JstdCn n z + A z = Jc n + A z
    rw [JstdCn_apply_eq]
  rw [h1] at hAC
  refine ContinuousLinearMap.ext fun u => ?_
  rw [mul_apply_eq_comp, neg_apply, one_apply_eq_self]
  exact hAC u

/-- The two inverse relations satisfied by `Minv v z`. -/
lemma Minv_mul {n : ℕ} {v : Fin n → Cn n → ℂ} {z : Cn n}
    (hu : IsUnit (1 - DvCLM v z)) :
    Minv v z * (1 - DvCLM v z) = 1 ∧ (1 - DvCLM v z) * Minv v z = 1 :=
  ⟨Ring.inverse_mul_cancel _ hu, Ring.mul_inverse_cancel _ hu⟩

/-- The algebra of the push-forward: with `d = 1 - DvCLM v z` and `M = Minv v z` the pushed-forward
perturbation conjugates the structure `Jstd + A z` by `d`. -/
lemma Aop_algebra {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n) (v : Fin n → Cn n → ℂ) (z : Cn n)
    (hAC : (Jc n + A z) * (Jc n + A z) = -1)
    (hu1 : Minv v z * (1 - DvCLM v z) = 1)
    (hu2 : (1 - DvCLM v z) * Minv v z = 1) :
    (Jc n + Aop A v z = (1 - DvCLM v z) * (Jc n + A z) * Minv v z) ∧
    ((Jc n + Aop A v z) * (1 - DvCLM v z) = (1 - DvCLM v z) * (Jc n + A z)) ∧
    ((Jc n + Aop A v z) * (Jc n + Aop A v z) = -1) := by
  rw [Aop_eq A v z]
  exact conj_identity_ring (1 - DvCLM v z) (Minv v z) (Jc n) (A z) hu1 hu2 hAC

/-! ## The main statement -/

theorem exists_pushforward_structure {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {r δ : ℝ} (hr : 1 ≤ r) (hr4 : r ≤ 4) (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8)
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (hA : ∀ m : ℕ, ContDiffOn ℝ m A (Work.NN.Newton.Pd n r))
    (hAC : ∀ z ∈ Work.NN.Newton.Pd n r, ∀ u : Work.NN.Core.Cn n,
      (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z u) = -u)
    {v : Fin n → Work.NN.Core.Cn n → ℂ}
    (hv : ∀ l, ∀ m : ℕ, ContDiffOn ℝ m (v l) (Work.NN.Newton.Pd n (r * (1 - δ))))
    {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ l, Work.CR.Flat.holderNorm 2 α (v l) (Work.NN.Newton.Pd n (r * (1 - δ)))
      ≤ ENNReal.ofReal b)
    (hbδ : b ≤ r * δ / 4) (hb1 : b ≤ 1 / 16) :
    ∃ Ψ : Work.NN.Core.Cn n → Work.NN.Core.Cn n,
      (∀ m : ℕ, ContDiffOn ℝ m Ψ (Work.NN.Newton.Pd n (r * (1 - 2 * δ)))) ∧
      (∀ ζ ∈ Work.NN.Newton.Pd n (r * (1 - 2 * δ)), Work.NN.Newton.Phi v (Ψ ζ) = ζ) ∧
      (∀ z ∈ Work.NN.Newton.Pd n (r * (1 - δ)),
        Work.NN.Newton.Phi v z ∈ Work.NN.Newton.Pd n (r * (1 - 2 * δ)) →
        Ψ (Work.NN.Newton.Phi v z) = z) ∧
      (∀ ζ ∈ Work.NN.Newton.Pd n (r * (1 - 2 * δ)),
        Ψ ζ ∈ Work.NN.Newton.Pd n (r * (1 - δ))) ∧
      (∀ ζ ∈ Work.NN.Newton.Pd n (r * (1 - 2 * δ)),
        ∀ ζ' ∈ Work.NN.Newton.Pd n (r * (1 - 2 * δ)), ‖Ψ ζ - Ψ ζ'‖ ≤ 2 * ‖ζ - ζ'‖) ∧
      (∀ ζ ∈ Work.NN.Newton.Pd n (r * (1 - 2 * δ)), ‖fderiv ℝ Ψ ζ‖ ≤ 2) ∧
      (∀ ζ ∈ Work.NN.Newton.Pd n (r * (1 - 2 * δ)),
        ∀ ζ' ∈ Work.NN.Newton.Pd n (r * (1 - 2 * δ)),
        ‖fderiv ℝ Ψ ζ - fderiv ℝ Ψ ζ'‖ ≤ (1 / 2) * ‖ζ - ζ'‖ ^ α) ∧
      ∃ A' : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n,
        (∀ ζ ∈ Work.NN.Newton.Pd n (r * (1 - 2 * δ)),
          A' ζ = Work.NN.Newton.Aop A v (Ψ ζ)) ∧
        (∀ m : ℕ, ContDiffOn ℝ m A' (Work.NN.Newton.Pd n (r * (1 - 2 * δ)))) ∧
        (∀ z ∈ Work.NN.Newton.Pd n (r * (1 - δ)),
          Work.NN.Newton.Phi v z ∈ Work.NN.Newton.Pd n (r * (1 - 2 * δ)) →
          ∀ h : Work.NN.Core.Cn n,
            fderiv ℝ (Work.NN.Newton.Phi v) z ((Work.NN.Core.JstdCn n + A) z h)
              = (Work.NN.Core.JstdCn n + A') (Work.NN.Newton.Phi v z)
                  (fderiv ℝ (Work.NN.Newton.Phi v) z h)) ∧
        (∀ ζ ∈ Work.NN.Newton.Pd n (r * (1 - 2 * δ)), ∀ w : Work.NN.Core.Cn n,
          (Work.NN.Core.JstdCn n + A') ζ ((Work.NN.Core.JstdCn n + A') ζ w) = -w) := by
  classical
  -- basic radius inequalities
  have hrpos : (0 : ℝ) < r := by linarith
  have hRpos : 0 < r * (1 - δ) := by
    refine mul_pos hrpos ?_; linarith
  have hR'pos : 0 < r * (1 - 2 * δ) := by
    refine mul_pos hrpos ?_; linarith
  have hR'R : r * (1 - 2 * δ) < r * (1 - δ) := by
    have h : r * (1 - 2 * δ) = r * (1 - δ) - r * δ := by ring
    rw [h]
    have : 0 < r * δ := mul_pos hrpos hδ
    linarith
  have hε4 : r * δ / 4 ≤ (r * (1 - δ) - r * (1 - 2 * δ)) / 4 := by
    have h : r * (1 - δ) - r * (1 - 2 * δ) = r * δ := by ring
    rw [h]
  have hmid : (r * (1 - δ) + r * (1 - 2 * δ)) / 2 ≤ r * (1 - δ) := by
    have h : r * (1 - 2 * δ) ≤ r * (1 - δ) := le_of_lt hR'R
    linarith
  have hle : r * (1 - δ) ≤ r := by
    have h : r * (1 - δ) = r - r * δ := by ring
    rw [h]
    have : 0 < r * δ := mul_pos hrpos hδ
    linarith
  -- restriction of the polydiscs
  have hPds : Pd n (r * (1 - δ)) ⊆ Pd n r := Pd_mono hle
  -- the near-identity map `Φ = Phi v` is smooth
  have hΦsm : ∀ m : ℕ, ContDiffOn ℝ m (Phi v)
      (Pd n (r * (1 - δ))) := by
    intro m
    rw [contDiffOn_pi]
    intro l
    exact ((ContinuousLinearMap.proj l : Cn n →L[ℝ] ℂ).contDiff.contDiffOn).sub (hv l m)
  -- value and derivative bounds for `Φ`
  have hΦb := phiNormBounds (Ω := Pd n (r * (1 - δ))) (isOpen_Pd n _) hb0 hb
    (fun l => hv l 1)
  have hb_deriv : ∀ z ∈ Pd n (r * (1 - δ)),
      ‖fderiv ℝ (Phi v) z - ContinuousLinearMap.id ℝ (Cn n)‖ ≤ 1 / 2 :=
    fun z hz => le_trans (hΦb.2 z hz) (by linarith)
  -- `fderiv Φ = 1 - DvCLM`
  have hfderiv_phi : ∀ z ∈ Pd n (r * (1 - δ)), fderiv ℝ (Phi v) z = 1 - DvCLM v z :=
    fun z hz => fderiv_Phi v z (fun l =>
      ((hv l 1).contDiffAt ((isOpen_Pd n _).mem_nhds hz)).differentiableAt (by norm_num))
  -- the `C^{1,α}` data of `DvCLM`
  have hDv := DvCLM_data_le hα0 hRpos hv hb0 hb
  -- the Hölder bound for `fderiv Φ`
  have hh : ∀ z ∈ Pd n (r * (1 - δ)), ∀ z' ∈ Pd n (r * (1 - δ)),
      ‖fderiv ℝ (Phi v) z - fderiv ℝ (Phi v) z'‖ ≤ (1 / 16) * ‖z - z'‖ ^ α := by
    intro z hz z' hz'
    rw [hfderiv_phi z hz, hfderiv_phi z' hz']
    have h2 : (1 : Cn n →L[ℝ] Cn n) - DvCLM v z - (1 - DvCLM v z')
        = -(DvCLM v z - DvCLM v z') := by abel
    rw [h2, norm_neg]
    refine le_trans (hDv.2.2.2.1 z hz z' hz') ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) α)
    linarith
  -- the value bound for `Φ - id`
  have hc : ∀ z ∈ Pd n (r * (1 - δ)), ∀ j : Fin n, ‖(Phi v z) j - z j‖ ≤ r * δ / 4 := by
    intro z hz j
    have h1 : (Phi v z) j - z j = -v j z := by rw [Phi_apply]; ring
    rw [h1, norm_neg]
    have h2 : ENNReal.ofReal ‖v j z‖ ≤ ENNReal.ofReal b :=
      le_trans (Work.CR.Flat.norm_apply_le_holderNorm 2 α (v j) (Pd n (r * (1 - δ))) hz) (hb j)
    have h3 : ‖v j z‖ ≤ b := (ENNReal.ofReal_le_ofReal_iff hb0).mp h2
    linarith
  -- the inverse of the near-identity map
  obtain ⟨Ψ, hΨw, hΨmem, hΨuniq, hΨsm, hΨlip, hΨfd, hΨhold⟩ :=
    nearInverseThin hα0 hα1 hRpos hR'pos hR'R (by have h0 : 0 < r * δ := mul_pos hrpos hδ; linarith) hε4
      hΦsm hb_deriv hh hc
  -- restriction of the inverse to the outer polydisc
  have hΨmem' : ∀ ζ ∈ Pd n (r * (1 - 2 * δ)), Ψ ζ ∈ Pd n (r * (1 - δ)) :=
    fun ζ hζ => Pd_mono hmid (hΨmem ζ hζ)
  -- smoothness data of `Aop`
  have hAmono : ∀ m : ℕ, ContDiffOn ℝ m A (Pd n (r * (1 - δ))) :=
    fun m => (hA m).mono hPds
  have hunit : ∀ z ∈ Pd n (r * (1 - δ)), IsUnit (1 - DvCLM v z) := by
    intro z hz
    refine IsUnit.one_sub_of_norm_lt_one ?_
    have := hDv.2.1 z hz
    linarith
  have hu1 : ∀ z ∈ Pd n (r * (1 - δ)), Minv v z * (1 - DvCLM v z) = 1 :=
    fun z hz => (Minv_mul (hunit z hz)).1
  have hu2 : ∀ z ∈ Pd n (r * (1 - δ)), (1 - DvCLM v z) * Minv v z = 1 :=
    fun z hz => (Minv_mul (hunit z hz)).2
  have hACring : ∀ z ∈ Pd n (r * (1 - δ)), (Jc n + A z) * (Jc n + A z) = -1 :=
    fun z hz => ring_AC_of_pointwise (hAC z (hPds hz))
  have hAop_sm : ∀ m : ℕ, ContDiffOn ℝ m (fun z => Aop A v z) (Pd n (r * (1 - δ))) :=
    contDiffOn_Aop hAmono hv hunit
  -- the two structural facts at a point of the inner polydisc
  have hsq : ∀ ζ ∈ Pd n (r * (1 - 2 * δ)),
      (Jc n + Aop A v (Ψ ζ)) * (Jc n + Aop A v (Ψ ζ)) = -1 :=
    fun ζ hζ => (Aop_algebra A v (Ψ ζ) (hACring (Ψ ζ) (hΨmem' ζ hζ))
      (hu1 (Ψ ζ) (hΨmem' ζ hζ)) (hu2 (Ψ ζ) (hΨmem' ζ hζ))).2.2
  have hconj : ∀ ζ ∈ Pd n (r * (1 - 2 * δ)),
      (Jc n + Aop A v (Ψ ζ)) * (fderiv ℝ (Phi v) (Ψ ζ))
        = (fderiv ℝ (Phi v) (Ψ ζ)) * (Jc n + A (Ψ ζ)) :=
    fun ζ hζ => by
      rw [hfderiv_phi (Ψ ζ) (hΨmem' ζ hζ)]
      exact (Aop_algebra A v (Ψ ζ) (hACring (Ψ ζ) (hΨmem' ζ hζ))
        (hu1 (Ψ ζ) (hΨmem' ζ hζ)) (hu2 (Ψ ζ) (hΨmem' ζ hζ))).2.1
  refine ⟨Ψ, hΨsm, ?_, ?_, ?_, hΨlip, hΨfd, hΨhold, ?_⟩
  · intro ζ hζ; exact hΨw ζ hζ
  · intro z hz hz'; exact hΨuniq (Phi v z) hz' z hz rfl
  · intro ζ hζ; exact hΨmem' ζ hζ
  · refine ⟨fun ζ => Aop A v (Ψ ζ), ?_, ?_, ?_, ?_⟩
    · intro ζ hζ; rfl
    · intro m
      exact (hAop_sm m).comp (hΨsm m) (fun ζ hζ => hΨmem' ζ hζ)
    · intro z hz hz' h
      have hzr : Ψ (Phi v z) = z := hΨuniq (Phi v z) hz' z hz rfl
      have hconjz : (Jc n + Aop A v z) * (fderiv ℝ (Phi v) z)
          = (fderiv ℝ (Phi v) z) * (Jc n + A z) := by
        have hthis := hconj (Phi v z) hz'
        rwa [hzr] at hthis
      have hkey := congrArg (fun T : Cn n →L[ℝ] Cn n => T h) hconjz
      simp only [mul_apply_eq_comp] at hkey
      have hR : (JstdCn n + (fun ζ => Aop A v (Ψ ζ))) (Phi v z) = Jc n + Aop A v z := by
        show JstdCn n (Phi v z) + Aop A v (Ψ (Phi v z)) = Jc n + Aop A v z
        rw [JstdCn_apply_eq, hzr]
      have hL : (JstdCn n + A) z = Jc n + A z := by
        show JstdCn n z + A z = Jc n + A z
        rw [JstdCn_apply_eq]
      rw [hR, hL]
      exact hkey.symm
    · intro ζ hζ w
      have h1 : (JstdCn n + (fun ζ => Aop A v (Ψ ζ))) ζ = Jc n + Aop A v (Ψ ζ) := by
        show JstdCn n ζ + Aop A v (Ψ ζ) = Jc n + Aop A v (Ψ ζ)
        rw [JstdCn_apply_eq]
      rw [h1]
      have hsq' := congrArg (fun T : Cn n →L[ℝ] Cn n => T w) (hsq ζ hζ)
      simp only [mul_apply_eq_comp, neg_apply, one_apply_eq_self] at hsq'
      exact hsq'

end Work.NN.Newton
