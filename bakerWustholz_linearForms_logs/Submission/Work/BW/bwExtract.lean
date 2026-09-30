import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.bwScale
import Submission.Work.BW.linWeight_inj
import Submission.Work.BW.sum_smul_pow_eq_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Multihomogeneous components of an element of a torus-invariant ideal

If a prime ideal `p` of `MR N` is invariant under the torus action `scaleEnd`, then every
element of `p` has all its multihomogeneous components in `p` (i.e. `p` is multihomogeneous).
-/

namespace Work.BW

open MvPolynomial

variable {N : ℕ}

private lemma wtPow_add' (lam : Fin (N+1) → ℂ) (d d' : Fin (N+1) →₀ ℕ) :
    wtPow N lam (d + d') = wtPow N lam d * wtPow N lam d' := by
  simp only [wtPow, Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]

private lemma wtPow_smul_single (lam : Fin (N+1) → ℂ) (n : ℕ) (i : Fin (N+1)) :
    wtPow N lam (n • Finsupp.single i 1) = lam i ^ n := by
  rw [wtPow, Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne hj, smul_zero, pow_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma wtPow_weight_eq_prod (lam : Fin (N+1) → ℂ) (m : (Fin (N+1) × Fin 2) →₀ ℕ) :
    wtPow N lam (Finsupp.weight (mdeg N) m) = m.prod (fun v k => lam v.1 ^ k) := by
  classical
  induction m using Finsupp.induction with
  | zero => simp [wtPow]
  | single_add a b f haf hb ih =>
    have h1 : Finsupp.weight (mdeg N) ((fun₀ | a => b) + f)
        = b • Finsupp.single a.1 1 + Finsupp.weight (mdeg N) f := by
      rw [map_add, Finsupp.weight_single]
      rfl
    rw [h1, wtPow_add', wtPow_smul_single, ih,
      Finsupp.prod_add_index' (by intro x; simp) (by intro x y z; rw [pow_add]),
      Finsupp.prod_single_index (by simp)]

private lemma scaleEnd_monomial' (lam : Fin (N+1) → ℂ) (m : (Fin (N+1) × Fin 2) →₀ ℕ) (a : ℂ) :
    scaleEnd N lam (MvPolynomial.monomial m a)
      = wtPow N lam (Finsupp.weight (mdeg N) m) • MvPolynomial.monomial m a := by
  rw [MvPolynomial.monomial_eq, map_mul]
  have hC : (scaleEnd N lam) (MvPolynomial.C a) = MvPolynomial.C a := by simp [scaleEnd]
  rw [hC]
  have hP : (scaleEnd N lam) (m.prod fun n e => MvPolynomial.X n ^ e)
      = MvPolynomial.C (wtPow N lam (Finsupp.weight (mdeg N) m)) *
        (m.prod fun n e => MvPolynomial.X n ^ e) := by
    show (scaleEnd N lam) (m.support.prod fun n => MvPolynomial.X n ^ m n) = _
    rw [map_prod]
    rw [Finset.prod_congr rfl (fun n _ => by rw [map_pow, scaleEnd_X, mul_pow, ← map_pow])]
    rw [Finset.prod_mul_distrib]
    congr 1
    have hbridge : (∏ x ∈ m.support, lam x.1 ^ m x) = m.prod (fun v k => lam v.1 ^ k) := rfl
    rw [← map_prod, hbridge, wtPow_weight_eq_prod]
  rw [hP, ← MvPolynomial.C_mul']
  ring

private lemma scaleEnd_of_mem' (lam : Fin (N+1) → ℂ) {d : Fin (N+1) →₀ ℕ} {φ : MR N}
    (h : φ ∈ homPiece N d) : scaleEnd N lam φ = wtPow N lam d • φ := by
  have key : ∀ (p : MR N), p.IsWeightedHomogeneous (mdeg N) d →
      scaleEnd N lam p = wtPow N lam d • p := by
    intro p hp
    induction hp using IsWeightedHomogeneous.induction_on with
    | zero => simp
    | add p q hp hq ihp ihq => rw [map_add, ihp, ihq, smul_add]
    | monomial m a hm =>
      rw [scaleEnd_monomial']
      congr 1
      rw [show (Finsupp.weight (mdeg N) m) = d from hm]
  exact key φ h

private lemma sum_components_degSup' (φ : MR N) :
    ∑ d ∈ degSup N φ, MvPolynomial.weightedHomogeneousComponent (mdeg N) d φ = φ := by
  have h := MvPolynomial.sum_weightedHomogeneousComponent (mdeg N) φ
  rw [finsum_eq_sum_of_support_subset
    (f := fun d => MvPolynomial.weightedHomogeneousComponent (mdeg N) d φ)
    (s := degSup N φ) ?_] at h
  · exact h
  · intro d hd
    rw [Function.mem_support] at hd
    by_contra hmem
    rw [Finset.mem_coe] at hmem
    exact hd (MvPolynomial.weightedHomogeneousComponent_eq_zero' d φ
      (fun m hm hw => hmem (Finset.mem_image.mpr ⟨m, hm, hw⟩)))

private lemma scaleEnd_apply_local (lam : Fin (N+1) → ℂ) (φ : MR N) :
    scaleEnd N lam φ =
      ∑ d ∈ degSup N φ,
        wtPow N lam d • MvPolynomial.weightedHomogeneousComponent (mdeg N) d φ := by
  calc scaleEnd N lam φ
      = scaleEnd N lam (∑ d ∈ degSup N φ,
          MvPolynomial.weightedHomogeneousComponent (mdeg N) d φ) := by
        rw [sum_components_degSup']
    _ = ∑ d ∈ degSup N φ,
          scaleEnd N lam (MvPolynomial.weightedHomogeneousComponent (mdeg N) d φ) := by
        rw [map_sum]
    _ = ∑ d ∈ degSup N φ,
          wtPow N lam d • MvPolynomial.weightedHomogeneousComponent (mdeg N) d φ := by
        exact Finset.sum_congr rfl fun d _ =>
          scaleEnd_of_mem' lam (MvPolynomial.weightedHomogeneousComponent_mem (mdeg N) φ d)


/-- The torus scaling acts on a polynomial by scaling each multihomogeneous component by the
corresponding weight.  (Proved here from scratch so that this file is self-contained.) -/
theorem scaleEnd_components_formula {N : ℕ} (lam : Fin (N + 1) → ℂ) (φ : MR N) :
    scaleEnd N lam φ =
      ∑ d ∈ degSup N φ,
        wtPow N lam d • MvPolynomial.weightedHomogeneousComponent (mdeg N) d φ :=
  scaleEnd_apply_local lam φ

/-- Auxiliary form of `components_mem_of_scale_inv`, taking the diagonalisation formula for
`scaleEnd` as an explicit hypothesis. -/
theorem components_mem_of_scale_inv_aux (p : Ideal (MR N)) (hp : p.IsPrime)
    (hinv : ∀ (lam : Fin (N + 1) → ℂˣ) (r : MR N), r ∈ p →
      scaleEnd N (fun i => (lam i : ℂ)) r ∈ p)
    (hform : ∀ (lam : Fin (N + 1) → ℂ) (φ : MR N), scaleEnd N lam φ =
      ∑ d ∈ degSup N φ,
        wtPow N lam d • MvPolynomial.weightedHomogeneousComponent (mdeg N) d φ)
    {r : MR N} (hr : r ∈ p) (d : Fin (N + 1) →₀ ℕ) :
    MvPolynomial.weightedHomogeneousComponent (mdeg N) d r ∈ p := by
  classical
  haveI := hp
  by_cases hd : d ∈ degSup N r
  · obtain ⟨c, hc⟩ := linWeight_inj (degSup N r)
    have key : ∀ t : ℂ, t ≠ 0 → ∑ e ∈ degSup N r,
        (algebraMap ℂ (MR N ⧸ p) t) ^ (∑ i, c i * e i) *
          (Ideal.Quotient.mkₐ ℂ p)
            (MvPolynomial.weightedHomogeneousComponent (mdeg N) e r) = 0 := by
      intro t ht
      rw [← mk_scale_sum p (degSup N r) t c r]
      change Ideal.Quotient.mk p _ = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      have h1 : scaleEnd N (fun i => t ^ (c i)) r ∈ p := by
        have h2 := hinv (fun i => Units.mk0 (t ^ (c i)) (pow_ne_zero _ ht)) r hr
        simpa using h2
      rwa [hform] at h1
    have h3 := sum_smul_pow_eq_zero (s := degSup N r)
      (fun e => (Ideal.Quotient.mkₐ ℂ p)
        (MvPolynomial.weightedHomogeneousComponent (mdeg N) e r))
      (fun e => ∑ i, c i * e i) (fun a ha b hb h => hc a ha b hb h) key d hd
    change Ideal.Quotient.mk p
      (MvPolynomial.weightedHomogeneousComponent (mdeg N) d r) = 0 at h3
    rwa [Ideal.Quotient.eq_zero_iff_mem] at h3
  · rw [MvPolynomial.weightedHomogeneousComponent_eq_zero' _ _
      (fun m hm hw => hd (Finset.mem_image.mpr ⟨m, hm, hw⟩))]
    exact Submodule.zero_mem _

/-- Every multihomogeneous component of an element of a prime ideal invariant under the torus
action again lies in the ideal. -/
theorem components_mem_of_scale_inv (p : Ideal (MR N)) (hp : p.IsPrime)
    (hinv : ∀ (lam : Fin (N + 1) → ℂˣ) (r : MR N), r ∈ p →
      scaleEnd N (fun i => (lam i : ℂ)) r ∈ p)
    {r : MR N} (hr : r ∈ p) (d : Fin (N + 1) →₀ ℕ) :
    MvPolynomial.weightedHomogeneousComponent (mdeg N) d r ∈ p :=
  components_mem_of_scale_inv_aux p hp hinv scaleEnd_apply_local hr d

end Work.BW
