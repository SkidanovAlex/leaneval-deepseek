import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Submission.Commons.Analysis.MvPolynomial.realRooted_limit_closed

noncomputable section

open MvPolynomial UpperHalfPlane Polynomial Metric
open Filter
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Commons.Analysis.MvPolynomial

/-! # The top part in one variable of a stable polynomial is stable

If `p : MvPolynomial (Fin n) ℝ` is stable (zero or nonvanishing on `UpperHalfPlane^n`),
then the sum of the monomials of `p` whose `j`-th exponent equals the maximal possible
value `d` (the "top part in the variable `j`") is stable as well.

Proof: for `k : ℕ, k ≥ 1` the polynomials `p_k = (1/k)^d · p(…, k·x_j, …)` are stable
(positive dilations of `p`); as `k → ∞` they converge coefficientwise to the top part.
Since a coefficientwise limit of polynomials that are nonvanishing on the open upper half
plane either vanishes identically or is nonvanishing there (root-near / Hurwitz argument,
formalized by `rrl_root_in_closedBall`), the top part is stable.
-/

namespace TopInJ


-- --------------------------------------------------------------------------
-- 1. evaluation as a finite sum over the support, and evaluation along lines
-- --------------------------------------------------------------------------

lemma aeval_eq_sum_support {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (z : Fin n → ℂ) :
    MvPolynomial.aeval (R := ℝ) z p =
      ∑ m ∈ p.support, ((MvPolynomial.coeff (R := ℝ) m p : ℂ) *
        ∏ i : Fin n, (z i) ^ (m i)) := by
  calc
    MvPolynomial.aeval (R := ℝ) z p
        = MvPolynomial.aeval (R := ℝ) z
            (∑ m ∈ p.support, MvPolynomial.monomial m (MvPolynomial.coeff (R := ℝ) m p)) := by
            rw [p.support_sum_monomial_coeff]
    _ = ∑ m ∈ p.support,
          MvPolynomial.aeval (R := ℝ) z (MvPolynomial.monomial m (MvPolynomial.coeff (R := ℝ) m p)) := by
            rw [map_sum]
    _ = ∑ m ∈ p.support, ((MvPolynomial.coeff (R := ℝ) m p : ℂ) *
          ∏ i : Fin n, (z i) ^ (m i)) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [MvPolynomial.aeval_monomial]
          congr 1
          exact Finsupp.prod_pow m (fun i => z i)

lemma prod_update_eq_mul_pow {n : ℕ} (j : Fin n) (a : ℂ) (z : Fin n → ℂ) (m : Fin n →₀ ℕ) :
    (∏ i : Fin n, (if i = j then a * z i else z i) ^ (m i)) =
      (∏ i : Fin n, (z i) ^ (m i)) * a ^ (m j) := by
  classical
  have hmem : j ∈ (Finset.univ : Finset (Fin n)) := by simp
  let E : ℂ := ∏ i ∈ (Finset.univ.erase j : Finset (Fin n)), (z i) ^ (m i)
  have h1 : (∏ i : Fin n, (if i = j then a * z i else z i) ^ (m i)) =
      (a * z j) ^ (m j) * E := by
    rw [← Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => (if i = j then a * z i else z i) ^ (m i)) hmem]
    congr 1
    · simp
    · dsimp [E]
      apply Finset.prod_congr rfl
      intro i hi
      have hne : i ≠ j := (Finset.mem_erase.mp hi).1
      simp [hne]
  have h2 : (∏ i : Fin n, (z i) ^ (m i)) = (z j) ^ (m j) * E := by
    rw [← Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => (z i) ^ (m i)) hmem]
  have hmul : (a * z j) ^ (m j) * E = (z j) ^ (m j) * E * a ^ (m j) := by
    rw [mul_pow]
    ring
  calc
    (∏ i : Fin n, (if i = j then a * z i else z i) ^ (m i)) = (a * z j) ^ (m j) * E := h1
    _ = (z j) ^ (m j) * E * a ^ (m j) := hmul
    _ = (∏ i : Fin n, (z i) ^ (m i)) * a ^ (m j) := by rw [h2]

/-- A polynomial in one variable obtained by evaluating `p` at the affine point
`t ↦ a + t • b`. -/
noncomputable def affPoly {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (a b : Fin n → ℂ) :
    Polynomial ℂ :=
  MvPolynomial.aeval (R := ℝ) (fun i => Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X) p

lemma affPoly_eval {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (a b : Fin n → ℂ) (t : ℂ) :
    (affPoly p a b).eval t = MvPolynomial.aeval (R := ℝ) (fun i => a i + t * b i) p := by
  classical
  unfold affPoly
  induction p using MvPolynomial.induction_on with
  | C a0 => simp
  | add p q hp hq =>
      rw [map_add, Polynomial.eval_add, map_add]
      rw [hp, hq]
  | mul_X p i hp =>
      rw [map_mul, Polynomial.eval_mul, map_mul]
      simp only [MvPolynomial.aeval_X]
      rw [hp]
      congr 1
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      ring

-- --------------------------------------------------------------------------
-- 2. scaling the `j`-th variable by a real number
-- --------------------------------------------------------------------------

/-- `scaleVar j a p` is `p` with `x_j` replaced by `a • x_j`. -/
noncomputable def scaleVar {n : ℕ} (j : Fin n) (a : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ m ∈ p.support,
    MvPolynomial.monomial m (MvPolynomial.coeff (R := ℝ) m p * a ^ (m j))

lemma coeff_scaleVar {n : ℕ} (j : Fin n) (a : ℝ) (p : MvPolynomial (Fin n) ℝ)
    (m : Fin n →₀ ℕ) :
    (scaleVar j a p).coeff m = MvPolynomial.coeff (R := ℝ) m p * a ^ (m j) := by
  classical
  unfold scaleVar
  rw [MvPolynomial.coeff_sum]
  by_cases hm : m ∈ p.support
  · have hmain : (∑ x ∈ p.support,
        MvPolynomial.coeff m (MvPolynomial.monomial x (MvPolynomial.coeff (R := ℝ) x p * a ^ (x j)))) =
        MvPolynomial.coeff (R := ℝ) m p * a ^ (m j) := by
      rw [Finset.sum_eq_single m]
      · rw [MvPolynomial.coeff_monomial]
        simp
      · intro b hb hne
        rw [MvPolynomial.coeff_monomial]
        simp [hne]
      · intro hnot
        exact False.elim (hnot hm)
    simpa using hmain
  · have hc : MvPolynomial.coeff (R := ℝ) m p = 0 := by
      simpa [MvPolynomial.mem_support_iff] using hm
    rw [Finset.sum_eq_zero]
    · simp [hc]
    · intro b hb
      rw [MvPolynomial.coeff_monomial]
      by_cases h : b = m
      · subst b
        simp [hc]
      · simp [h]

lemma aeval_scaleVar {n : ℕ} (j : Fin n) (a : ℝ) (p : MvPolynomial (Fin n) ℝ)
    (z : Fin n → ℂ) :
    MvPolynomial.aeval (R := ℝ) z (scaleVar j a p) =
      MvPolynomial.aeval (R := ℝ) (fun i => if i = j then (a : ℂ) * z i else z i) p := by
  classical
  calc
    MvPolynomial.aeval (R := ℝ) z (scaleVar j a p)
        = MvPolynomial.aeval (R := ℝ) z
            (∑ m ∈ p.support,
              MvPolynomial.monomial m (MvPolynomial.coeff (R := ℝ) m p * a ^ (m j))) := rfl
    _ = ∑ m ∈ p.support,
          MvPolynomial.aeval (R := ℝ) z
            (MvPolynomial.monomial m (MvPolynomial.coeff (R := ℝ) m p * a ^ (m j))) := by
          rw [map_sum]
    _ = ∑ m ∈ p.support, ((MvPolynomial.coeff (R := ℝ) m p * a ^ (m j) : ℝ) : ℂ) *
          ∏ i : Fin n, (z i) ^ (m i) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [MvPolynomial.aeval_monomial]
          congr 1
          exact Finsupp.prod_pow m (fun i => z i)
    _ = MvPolynomial.aeval (R := ℝ) (fun i => if i = j then (a : ℂ) * z i else z i) p := by
          rw [aeval_eq_sum_support]
          apply Finset.sum_congr rfl
          intro m hm
          have hpow : ((a ^ (m j) : ℝ) : ℂ) = (a : ℂ) ^ (m j) := by simp
          rw [prod_update_eq_mul_pow]
          simp [hpow]
          ring

-- --------------------------------------------------------------------------
-- 3. positivity/closure facts for the upper half plane
-- --------------------------------------------------------------------------

lemma im_mul_pos_real {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.im) : 0 < (a * z).im := by
  have h : (a * z).im = a * z.im := by
    simp [Complex.mul_im]
  rw [h]
  exact mul_pos ha hz

-- --------------------------------------------------------------------------
-- 4. a nonzero polynomial is not identically zero on the upper half plane
-- --------------------------------------------------------------------------

lemma upperHalfPlaneSet_infinite : Set.Infinite {z : ℂ | 0 < z.im} := by
  exact Set.infinite_of_injective_forall_mem (s := {z : ℂ | 0 < z.im})
    (f := (fun z : UpperHalfPlane => (z : ℂ)))
    (by intro a b h; exact UpperHalfPlane.ext h)
    (fun z => z.coe_im_pos)

lemma exists_upper_aeval_ne_zero {n : ℕ} (q : MvPolynomial (Fin n) ℝ) (hq : q ≠ 0) :
    ∃ z : Fin n → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i => ((z i : UpperHalfPlane) : ℂ)) q ≠ 0 := by
  classical
  let Q : MvPolynomial (Fin n) ℂ := q.map (algebraMap ℝ ℂ)
  have hQ0 : Q ≠ 0 := by
    intro hQ
    apply hq
    have hinj : Function.Injective (MvPolynomial.map (algebraMap ℝ ℂ) :
        MvPolynomial (Fin n) ℝ → MvPolynomial (Fin n) ℂ) := by
      exact MvPolynomial.map_injective (algebraMap ℝ ℂ) (by
        intro a b h
        exact_mod_cast h)
    exact hinj (by simpa [Q] using hQ)
  by_contra hnone
  push Not at hnone
  have hall : ∀ x : Fin n → ℂ, (∀ i, x i ∈ {z : ℂ | 0 < z.im}) → MvPolynomial.eval x Q = 0 := by
    intro x hx
    let z : Fin n → UpperHalfPlane := fun i => ⟨x i, hx i⟩
    have h := hnone z
    have he : MvPolynomial.eval x Q = MvPolynomial.aeval (R := ℝ) (fun i => ((z i : UpperHalfPlane) : ℂ)) q := by
      simp [z, Q, ← MvPolynomial.aeval_map_algebraMap (R := ℝ) (A := ℂ) (B := ℂ) x q]
    rw [he]
    exact h
  have hQ : Q = 0 := by
    exact MvPolynomial.funext_set (p := Q) (q := 0)
      (s := fun _ : Fin n => {z : ℂ | 0 < z.im})
      (fun i => upperHalfPlaneSet_infinite)
      (by intro x hx; exact hall x (fun i => hx i trivial))
  exact hQ0 hQ



-- --------------------------------------------------------------------------
-- 5. the family of scaled polynomials and their coefficients
-- --------------------------------------------------------------------------

-- powers: `k^a * (k^b)⁻¹ = (k^(b-a))⁻¹` for `a ≤ b`, `k ≠ 0`
lemma pow_mul_inv_pow {k : ℝ} (hk : k ≠ 0) {a b : ℕ} (hab : a ≤ b) :
    k ^ a * (k ^ b)⁻¹ = (k ^ (b - a))⁻¹ := by
  have hb : b = a + (b - a) := (Nat.add_sub_of_le hab).symm
  rw [hb, pow_add]
  field_simp [pow_ne_zero a hk, pow_ne_zero (b - a) hk]
  congr 1
  omega

/-- `scaledTop j d k p = (1/k)^d · p` with `x_j` replaced by `k • x_j`. -/
noncomputable def scaledTop {n : ℕ} (j : Fin n) (d k : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ((k : ℝ) ^ d)⁻¹ • scaleVar j (k : ℝ) p

lemma coeff_scaledTop {n : ℕ} (j : Fin n) (d k : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (m : Fin n →₀ ℕ) :
    (scaledTop j d k p).coeff m = MvPolynomial.coeff (R := ℝ) m p * (k : ℝ) ^ (m j) /
      (k : ℝ) ^ d := by
  classical
  unfold scaledTop
  rw [MvPolynomial.coeff_smul]
  rw [coeff_scaleVar]
  simp only [smul_eq_mul]
  rw [div_eq_mul_inv]
  ring

/-- The top part coefficient: the coefficient of the monomials with `m j = d`. -/
noncomputable def topCoeff {n : ℕ} (j : Fin n) (d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (m : Fin n →₀ ℕ) : ℝ :=
  if m j = d then MvPolynomial.coeff (R := ℝ) m p else 0

lemma coeff_scaledTop_tendsto {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (j : Fin n)
    (d : ℕ) (m : Fin n →₀ ℕ) (hmd : m j ≤ d) :
    Tendsto (fun k : ℕ => (scaledTop j d k p).coeff m) atTop
      (nhds (if m j = d then MvPolynomial.coeff (R := ℝ) m p else 0)) := by
  classical
  by_cases h : m j = d
  · have hconst : Tendsto (fun _ : ℕ => MvPolynomial.coeff (R := ℝ) m p) atTop
        (nhds (MvPolynomial.coeff (R := ℝ) m p)) := tendsto_const_nhds
    have hev : (fun k : ℕ => (scaledTop j d k p).coeff m) =ᶠ[atTop]
        fun _ : ℕ => MvPolynomial.coeff (R := ℝ) m p := by
      change ∀ᶠ k in atTop, (scaledTop j d k p).coeff m = MvPolynomial.coeff (R := ℝ) m p
      rw [Filter.eventually_atTop]
      refine ⟨1, ?_⟩
      intro k hk
      rw [coeff_scaledTop]
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (by omega : 0 < k))
      have hc : MvPolynomial.coeff (R := ℝ) m p * (k : ℝ) ^ (m j) / (k : ℝ) ^ d =
          MvPolynomial.coeff (R := ℝ) m p := by
        rw [h]
        field_simp [pow_ne_zero (m j) hk0]
      exact hc
    simpa [h] using (tendsto_congr' hev).mpr hconst
  · have hlt : m j < d := lt_of_le_of_ne hmd h
    have he : d - m j ≠ 0 := by omega
    have hmain : Tendsto (fun k : ℕ => MvPolynomial.coeff (R := ℝ) m p /
        (k : ℝ) ^ (d - m j)) atTop (nhds (0 : ℝ)) :=
      tendsto_const_div_pow (MvPolynomial.coeff (R := ℝ) m p) (d - m j) he
    have hev : (fun k : ℕ => (scaledTop j d k p).coeff m) =ᶠ[atTop]
        (fun k : ℕ => MvPolynomial.coeff (R := ℝ) m p / (k : ℝ) ^ (d - m j)) := by
      change ∀ᶠ k in atTop, (scaledTop j d k p).coeff m =
          MvPolynomial.coeff (R := ℝ) m p / (k : ℝ) ^ (d - m j)
      rw [Filter.eventually_atTop]
      refine ⟨1, ?_⟩
      intro k hk
      rw [coeff_scaledTop]
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (by omega : 0 < k))
      have heq : MvPolynomial.coeff (R := ℝ) m p * (k : ℝ) ^ (m j) / (k : ℝ) ^ d =
          MvPolynomial.coeff (R := ℝ) m p / (k : ℝ) ^ (d - m j) := by
        have hb : d = m j + (d - m j) := (Nat.add_sub_of_le hmd).symm
        rw [hb, pow_add]
        field_simp [pow_ne_zero (m j) hk0, pow_ne_zero (d - m j) hk0]
        have : m j + (d - m j) - m j = d - m j := by omega
        rw [this]
      exact heq
    simpa [h] using (tendsto_congr' hev).mpr hmain

lemma tendsto_coeff_scaledTop_sub_topCoeff {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (j : Fin n) (d : ℕ) (m : Fin n →₀ ℕ) (hmd : m j ≤ d) :
    Tendsto (fun k : ℕ => (scaledTop j d k p).coeff m - topCoeff j d p m) atTop
      (nhds (0 : ℝ)) := by
  classical
  have h1 := coeff_scaledTop_tendsto p j d m hmd
  have hconst : Tendsto (fun _ : ℕ => topCoeff j d p m) atTop (nhds (topCoeff j d p m)) :=
    tendsto_const_nhds
  have hsub := h1.sub hconst
  simpa [topCoeff] using hsub

/-- Evaluation of the scaled family: `p` evaluated at a point whose `j`-coordinate is
multiplied by `k`, divided by `k^d`. -/
lemma aeval_scaledTop {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (j : Fin n) (d k : ℕ)
    (z : Fin n → ℂ) :
    MvPolynomial.aeval (R := ℝ) z (scaledTop j d k p) =
      (((k : ℝ) ^ d)⁻¹ : ℂ) *
        MvPolynomial.aeval (R := ℝ)
          (fun i => if i = j then (k : ℂ) * z i else z i) p := by
  classical
  unfold scaledTop
  rw [map_smul]
  have h := aeval_scaleVar (j := j) (a := (k : ℝ)) p z
  rw [h]
  simp [Complex.real_smul]

/-- The scaled family is stable: positive real dilations preserve stability. -/
lemma scaledTop_stable {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (j : Fin n) (d k : ℕ)
    (hk : 1 ≤ k)
    (hstab : ∀ z : Fin n → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0) :
    ∀ z : Fin n → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i => ((z i : UpperHalfPlane) : ℂ))
        (scaledTop j d k p) ≠ 0 := by
  classical
  intro z
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hk)
  have hk0 : (k : ℝ) ^ d ≠ 0 := pow_ne_zero d (ne_of_gt hkpos)
  let zU : Fin n → UpperHalfPlane := fun i =>
    if i = j then ⟨(k : ℂ) * (z i : ℂ), by
      have h : ((k : ℂ) * (z i : ℂ)).im = (k : ℝ) * (z i : ℂ).im := by
        rw [Complex.mul_im]
        simp
      rw [h]
      exact mul_pos hkpos (z i).coe_im_pos⟩ else z i
  have hzstab : MvPolynomial.aeval (R := ℝ) (fun i => ((zU i : UpperHalfPlane) : ℂ)) p ≠ 0 :=
    hstab zU
  have hfun : (fun i : Fin n => ((zU i : UpperHalfPlane) : ℂ)) =
      (fun i => if i = j then (k : ℂ) * ((z i : UpperHalfPlane) : ℂ)
        else ((z i : UpperHalfPlane) : ℂ)) := by
    funext i
    by_cases hij : i = j
    · simp [zU, hij]
    · simp [zU, hij]
  have h0 : MvPolynomial.aeval (R := ℝ)
      (fun i => if i = j then (k : ℂ) * ((z i : UpperHalfPlane) : ℂ)
        else ((z i : UpperHalfPlane) : ℂ)) p ≠ 0 := by
    rwa [← hfun]
  have hev : MvPolynomial.aeval (R := ℝ) (fun i => ((z i : UpperHalfPlane) : ℂ))
        (scaledTop j d k p) =
      (((k : ℝ) ^ d)⁻¹ : ℂ) *
        MvPolynomial.aeval (R := ℝ)
          (fun i => if i = j then (k : ℂ) * ((z i : UpperHalfPlane) : ℂ)
            else ((z i : UpperHalfPlane) : ℂ)) p := by
    simpa using aeval_scaledTop (p := p) (j := j) (d := d) (k := k)
      (z := fun i => ((z i : UpperHalfPlane) : ℂ))
  rw [hev]
  exact mul_ne_zero (by
      have h : (((k : ℝ) ^ d)⁻¹ : ℂ) ≠ 0 := by
        exact_mod_cast (inv_ne_zero hk0)
      exact h) h0

-- --------------------------------------------------------------------------
-- 6. root-free radius (Hurwitz preparation)
-- --------------------------------------------------------------------------

/-- A nonzero polynomial has a radius `η` such that there are no roots of positive norm
smaller than `η`. -/
lemma exists_punctured_rootfree (p : Polynomial ℂ) (hp : p ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ < η → p.eval z ≠ 0 := by
  classical
  let S : Set ℂ := {z | IsRoot p z}
  have hSfin : S.Finite := p.finite_setOfPred_isRoot hp
  let T : Finset ℂ := (hSfin.sdiff (t := ({0} : Set ℂ))).toFinset
  let s : Finset ℝ := T.image (fun w => ‖w‖)
  by_cases hs : s.Nonempty
  · let m : ℝ := s.min' hs
    have hm_pos : 0 < m := by
      have hmem : s.min' hs ∈ s := Finset.min'_mem s hs
      rcases Finset.mem_image.mp hmem with ⟨w, hw, hnorm⟩
      have hwS : w ∈ S \ {0} := by
        simpa [T, Set.Finite.mem_toFinset] using hw
      dsimp [m]
      rw [← hnorm]
      exact norm_pos_iff.mpr hwS.2
    have hm_le : ∀ x ∈ s, m ≤ x := fun x hx => Finset.min'_le s x hx
    refine ⟨m / 2, by linarith, ?_⟩
    intro z hz0 hzlt hzroot
    have hzIs : IsRoot p z := IsRoot.def.mpr hzroot
    have hzS : z ∈ S := by
      dsimp [S]
      exact hzIs
    have hzmem : z ∈ (S \ {0}) := ⟨hzS, hz0⟩
    have hzfin : z ∈ T := by
      simpa [T, Set.Finite.mem_toFinset] using hzmem
    have hnorm : ‖z‖ ∈ s := Finset.mem_image.mpr ⟨z, hzfin, rfl⟩
    have hmle : m ≤ ‖z‖ := hm_le ‖z‖ hnorm
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz0 hzlt hzroot
    have hzIs : IsRoot p z := IsRoot.def.mpr hzroot
    have hzS : z ∈ S := by
      dsimp [S]
      exact hzIs
    have hzmem : z ∈ (S \ {0}) := ⟨hzS, hz0⟩
    have hzfin : z ∈ T := by
      simpa [T, Set.Finite.mem_toFinset] using hzmem
    exact hs ⟨‖z‖, Finset.mem_image.mpr ⟨z, hzfin, rfl⟩⟩

-- --------------------------------------------------------------------------
-- 7. uniform closeness of evaluations along a segment
-- --------------------------------------------------------------------------

/-- For a finite family of monomials with coefficient sequences converging coefficientwise,
evaluations at points of the bounded segment `a + s • b` (`‖s‖ ≤ ρ`) converge uniformly. -/
lemma tendsto_uniform_eval_sub {n : ℕ} (S : Finset (Fin n →₀ ℕ))
    (c : ℕ → (Fin n →₀ ℕ) → ℝ) (cf : (Fin n →₀ ℕ) → ℝ)
    (hlim : ∀ m ∈ S, Tendsto (fun k : ℕ => c k m - cf m) atTop (nhds 0))
    (a b : Fin n → ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ s : ℂ, ‖s‖ ≤ ρ →
      ‖∑ m ∈ S, (((c k m : ℂ) - (cf m : ℂ)) *
            ∏ i : Fin n, (a i + s * b i) ^ (m i))‖ < ε := by
  classical
  let C : Fin n → ℝ := fun i => ‖a i‖ + ρ * ‖b i‖ + 1
  let B : (Fin n →₀ ℕ) → ℝ := fun m => ∏ i : Fin n, C i ^ (m i)
  have hbound (s : ℂ) (hs : ‖s‖ ≤ ρ) (i : Fin n) : ‖a i + s * b i‖ ≤ C i := by
    dsimp [C]
    calc
      ‖a i + s * b i‖ ≤ ‖a i‖ + ‖s * b i‖ := norm_add_le (a i) (s * b i)
      _ = ‖a i‖ + ‖s‖ * ‖b i‖ := by rw [norm_mul s (b i)]
      _ ≤ ‖a i‖ + ρ * ‖b i‖ := by
        exact add_le_add_right (mul_le_mul_of_nonneg_right hs (norm_nonneg (b i))) (‖a i‖)
      _ ≤ ‖a i‖ + ρ * ‖b i‖ + 1 := by linarith
  have hval (s : ℂ) (hs : ‖s‖ ≤ ρ) (m : Fin n →₀ ℕ) :
      ‖∏ i : Fin n, (a i + s * b i) ^ (m i)‖ ≤ B m := by
    dsimp [B]
    calc
      ‖∏ i ∈ (Finset.univ : Finset (Fin n)), (a i + s * b i) ^ (m i)‖
          ≤ ∏ i ∈ (Finset.univ : Finset (Fin n)), ‖(a i + s * b i) ^ (m i)‖ := by
            exact Finset.norm_prod_le (s := (Finset.univ : Finset (Fin n)))
              (f := fun i : Fin n => (a i + s * b i) ^ (m i))
      _ ≤ ∏ i ∈ (Finset.univ : Finset (Fin n)), C i ^ (m i) := by
          apply Finset.prod_le_prod
          · intro i hi
            exact norm_nonneg _
          · intro i hi
            calc
              ‖(a i + s * b i) ^ (m i)‖ = ‖a i + s * b i‖ ^ (m i) := by rw [norm_pow]
              _ ≤ C i ^ (m i) := pow_le_pow_left₀ (norm_nonneg ((a i + s * b i))) (hbound s hs i) (m i)
  have hsum_le (k : ℕ) (s : ℂ) (hs : ‖s‖ ≤ ρ) :
      ‖∑ m ∈ S, (((c k m : ℂ) - (cf m : ℂ)) *
            ∏ i : Fin n, (a i + s * b i) ^ (m i))‖ ≤
        ∑ m ∈ S, |c k m - cf m| * B m := by
    calc
      ‖∑ m ∈ S, (((c k m : ℂ) - (cf m : ℂ)) *
            ∏ i : Fin n, (a i + s * b i) ^ (m i))‖
          ≤ ∑ m ∈ S, ‖((c k m : ℂ) - (cf m : ℂ)) *
              ∏ i : Fin n, (a i + s * b i) ^ (m i)‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ S, |c k m - cf m| * B m := by
          apply Finset.sum_le_sum
          intro m hm
          calc
            ‖((c k m : ℂ) - (cf m : ℂ)) * ∏ i : Fin n, (a i + s * b i) ^ (m i)‖
                = ‖(c k m : ℂ) - (cf m : ℂ)‖ * ‖∏ i : Fin n, (a i + s * b i) ^ (m i)‖ := by
                  rw [norm_mul]
            _ = |c k m - cf m| * ‖∏ i : Fin n, (a i + s * b i) ^ (m i)‖ := by
                  have hcast : ‖(c k m : ℂ) - (cf m : ℂ)‖ = |c k m - cf m| := by
                    rw [← Complex.ofReal_sub]
                    exact rrl_norm_real_complex (c k m - cf m)
                  rw [hcast]
            _ ≤ |c k m - cf m| * B m := by
                  exact mul_le_mul_of_nonneg_left (hval s hs m) (abs_nonneg _)
  have hmul (m : Fin n →₀ ℕ) (hm : m ∈ S) :
      Tendsto (fun k : ℕ => |c k m - cf m| * B m) atTop (nhds (0 : ℝ)) := by
    have hc := hlim m hm
    have habs : Tendsto (fun k : ℕ => |c k m - cf m|) atTop (nhds (0 : ℝ)) := by
      simpa using hc.norm
    have hmul0 := habs.mul (tendsto_const_nhds (x := B m))
    simpa using hmul0
  have hcoeff : Tendsto (fun k : ℕ => ∑ m ∈ S, |c k m - cf m| * B m) atTop (nhds (0 : ℝ)) := by
    have hsum := tendsto_finsetSum S hmul
    simpa using hsum
  intro ε hε
  have hnn : ∀ k, 0 ≤ ∑ m ∈ S, |c k m - cf m| * B m := by
    intro k
    exact Finset.sum_nonneg (by intro m hm; positivity)
  have hball := hcoeff.eventually (Metric.ball_mem_nhds (0 : ℝ) hε)
  have hev : ∀ᶠ k in atTop, (∑ m ∈ S, |c k m - cf m| * B m) < ε := by
    filter_upwards [hball] with k hk
    have hnorm : ‖∑ m ∈ S, |c k m - cf m| * B m‖ < ε := by
      simpa [dist_eq_norm] using hk
    simpa [abs_of_nonneg (hnn k)] using hnorm
  filter_upwards [hev] with k hk
  intro s hs
  exact lt_of_le_of_lt (hsum_le k s hs) hk

-- --------------------------------------------------------------------------
-- 8. support and representation helpers used by the main theorem
-- --------------------------------------------------------------------------

lemma aeval_eq_sum_of_support_subset {n : ℕ} (S : Finset (Fin n →₀ ℕ))
    (p : MvPolynomial (Fin n) ℝ) (hS : p.support ⊆ S) (z : Fin n → ℂ) :
    MvPolynomial.aeval (R := ℝ) z p =
      ∑ m ∈ S, ((MvPolynomial.coeff (R := ℝ) m p : ℂ) *
        ∏ i : Fin n, (z i) ^ (m i)) := by
  classical
  rw [aeval_eq_sum_support]
  exact Finset.sum_subset hS (by
    intro m hmS hmnot
    have hc : MvPolynomial.coeff (R := ℝ) m p = 0 := by
      by_contra hc
      exact hmnot (MvPolynomial.mem_support_iff.mpr hc)
    simp [hc])

lemma aeval_sum_monomial {n : ℕ} (S : Finset (Fin n →₀ ℕ))
    (cf : (Fin n →₀ ℕ) → ℝ) (z : Fin n → ℂ) :
    MvPolynomial.aeval (R := ℝ) z (∑ m ∈ S, MvPolynomial.monomial m (cf m)) =
      ∑ m ∈ S, ((cf m : ℂ) * ∏ i : Fin n, (z i) ^ (m i)) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [MvPolynomial.aeval_monomial]
  congr 1
  exact Finsupp.prod_pow m (fun i => z i)

/-- If `k ≥ 1`, the scaled family has the same support as `p`. -/
lemma mem_support_scaledTop {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (j : Fin n) (d k : ℕ)
    (hk : 1 ≤ k) {m : Fin n →₀ ℕ} (hm : m ∈ (scaledTop j d k p).support) :
    m ∈ p.support := by
  classical
  have hc : (scaledTop j d k p).coeff m ≠ 0 := (MvPolynomial.mem_support_iff).mp hm
  rw [coeff_scaledTop] at hc
  exact (MvPolynomial.mem_support_iff).mpr (by
    intro hc0
    apply hc
    simp [hc0])

lemma scaledTop_support_subset {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (j : Fin n) (d k : ℕ)
    (hk : 1 ≤ k) : (scaledTop j d k p).support ⊆ p.support := by
  intro m hm
  exact mem_support_scaledTop p j d k hk hm

lemma scaledTop_eq_sum_coeff {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (j : Fin n) (d k : ℕ)
    (hk : 1 ≤ k) (S : Finset (Fin n →₀ ℕ)) (hS : p.support ⊆ S) :
    scaledTop j d k p = ∑ m ∈ S, MvPolynomial.monomial m ((scaledTop j d k p).coeff m) := by
  classical
  calc
    scaledTop j d k p
        = ∑ m ∈ (scaledTop j d k p).support,
            MvPolynomial.monomial m ((scaledTop j d k p).coeff m) := by
            rw [support_sum_monomial_coeff]
    _ = ∑ m ∈ S, MvPolynomial.monomial m ((scaledTop j d k p).coeff m) := by
          refine Finset.sum_subset ?_ ?_
          · exact Set.Subset.trans (scaledTop_support_subset p j d k hk) hS
          · intro m hmS hmnot
            have hc : (scaledTop j d k p).coeff m = 0 := by
              by_contra hc0
              exact hmnot (MvPolynomial.mem_support_iff.mpr hc0)
            simp [hc]

/-- The filter-sum (top part in variable `j`) equals the support-sum with the top coefficients. -/
lemma topPart_eq_sum_topCoeff {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (j : Fin n) (d : ℕ) :
    (∑ m ∈ p.support.filter (fun m : Fin n →₀ ℕ => m j = d),
        MvPolynomial.monomial m (MvPolynomial.coeff (R := ℝ) m p)) =
      ∑ m ∈ p.support, MvPolynomial.monomial m (topCoeff j d p m) := by
  classical
  simp only [topCoeff]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases h : m j = d
  · simp [h]
  · simp [h]

end TopInJ

/-- The top part in one variable of a stable polynomial is stable. -/
theorem top_in_j_stable_of_stable {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (j : Fin n)
    (hstab : p = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0) :
    let d : ℕ := p.support.sup (fun m : Fin n →₀ ℕ => m j)
    (∑ m ∈ p.support.filter (fun m : Fin n →₀ ℕ => m j = d),
        MvPolynomial.monomial m (p.coeff m)) = 0 ∨
      ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ))
          (∑ m ∈ p.support.filter (fun m : Fin n →₀ ℕ => m j = d),
            MvPolynomial.monomial m (p.coeff m)) ≠ 0 := by
  classical
  dsimp only
  by_cases hp0 : p = 0
  · left
    subst p
    simp
  · have hstabR : ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0 :=
        hstab.resolve_left hp0
    let d : ℕ := p.support.sup (fun m : Fin n →₀ ℕ => m j)
    let T : Finset (Fin n →₀ ℕ) := p.support.filter (fun m : Fin n →₀ ℕ => m j = d)
    let q : MvPolynomial (Fin n) ℝ :=
      ∑ m ∈ T, MvPolynomial.monomial m (MvPolynomial.coeff (R := ℝ) m p)
    change q = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) q ≠ 0
    by_cases hq0 : q = 0
    · left
      exact hq0
    · right
      intro w
      by_contra hw0
      let wc : Fin n → ℂ := fun i => ((w i : UpperHalfPlane) : ℂ)
      have hz0 : MvPolynomial.aeval (R := ℝ) wc q = 0 := by
        simpa [wc] using hw0
      obtain ⟨w2, hw2ne⟩ := TopInJ.exists_upper_aeval_ne_zero q hq0
      let w2c : Fin n → ℂ := fun i => ((w2 i : UpperHalfPlane) : ℂ)
      have hw2ne' : MvPolynomial.aeval (R := ℝ) w2c q ≠ 0 := by
        simpa [w2c] using hw2ne
      let Δ : Fin n → ℂ := fun i => w2c i - wc i
      let P : Polynomial ℂ := TopInJ.affPoly q wc Δ
      have hP0e : P.eval 0 = 0 := by
        dsimp [P]
        rw [TopInJ.affPoly_eval]
        have hfun : (fun i : Fin n => wc i + 0 * Δ i) = wc := by
          funext i
          simp
        rw [hfun]
        exact hz0
      have hP1ne : P.eval 1 ≠ 0 := by
        dsimp [P]
        rw [TopInJ.affPoly_eval]
        have hfun : (fun i : Fin n => wc i + 1 * Δ i) = w2c := by
          funext i
          simp [Δ, w2c, wc]
        rw [hfun]
        exact hw2ne'
      have hPne : P ≠ 0 := by
        intro hP0
        exact hP1ne (by rw [hP0]; simp)
      obtain ⟨η, hη0, hηrf⟩ := TopInJ.exists_punctured_rootfree P hPne
      have hneFin : (Finset.univ : Finset (Fin n)).Nonempty := ⟨j, by simp⟩
      let bound : Fin n → ℝ := fun i => (wc i).im / (‖Δ i‖ + 1)
      have himw (i : Fin n) : 0 < (wc i).im := by
        dsimp [wc]
        exact (w i).coe_im_pos
      have hbound_pos : ∀ i, 0 < bound i := by
        intro i
        dsimp [bound]
        exact div_pos (himw i) (by positivity)
      let ρ : ℝ := min (η / 2) (Finset.univ.inf' hneFin bound)
      have hρ0 : 0 < ρ := by
        dsimp [ρ]
        have hinf : 0 < Finset.univ.inf' hneFin bound := by
          rw [Finset.lt_inf'_iff]
          intro i hi
          exact hbound_pos i
        exact lt_min (by linarith) hinf
      have hρ_lt_η : ρ < η := by
        dsimp [ρ]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hρ_le_bound (i : Fin n) : ρ ≤ bound i := by
        dsimp [ρ]
        exact le_trans (min_le_right _ _) (Finset.inf'_le bound (Finset.mem_univ i))
      have hsphere (s : ℂ) (hs : s ∈ sphere (0 : ℂ) ρ) : P.eval s ≠ 0 := by
        have hn : ‖s‖ = ρ := by
          simpa using (mem_sphere_iff_norm.mp hs)
        exact hηrf s (by
          intro hs0
          have hz : ‖s‖ = 0 := by simp [hs0]
          linarith) (by rw [hn]; exact hρ_lt_η)
      obtain ⟨δ, hδ0, hδsphere⟩ := rrl_exists_pos_lower_bound_on_sphere P (r := (0 : ℂ))
        (ρ := ρ) hρ0 hsphere
      have hcoord (s : ℂ) (hs : ‖s‖ ≤ ρ) (i : Fin n) : 0 < (wc i + s * Δ i).im := by
        have hdenpos : 0 < ‖Δ i‖ + 1 := by positivity
        have hmul_le : ρ * (‖Δ i‖ + 1) ≤ (wc i).im := by
          exact (le_div_iff₀ hdenpos).mp (hρ_le_bound i)
        have hlt0 : ρ * ‖Δ i‖ < (wc i).im := by
          nlinarith
        have hsmul : ‖s * Δ i‖ ≤ ρ * ‖Δ i‖ := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right hs (norm_nonneg (Δ i))
        have himlt : ‖s * Δ i‖ < (wc i).im := lt_of_le_of_lt hsmul hlt0
        have habs : |(s * Δ i).im| ≤ ‖s * Δ i‖ := Complex.abs_im_le_norm (s * Δ i)
        have habslt : |(s * Δ i).im| < (wc i).im := lt_of_le_of_lt habs himlt
        have hims : (wc i + s * Δ i).im = (wc i).im + (s * Δ i).im := by
          rw [Complex.add_im]
        rw [hims]
        have hb := abs_lt.mp habslt
        linarith
      -- q written as a sum over the support with the top coefficients
      have hq_sum : q = ∑ m ∈ p.support,
          MvPolynomial.monomial m (TopInJ.topCoeff j d p m) := by
        dsimp [q, T]
        exact TopInJ.topPart_eq_sum_topCoeff p j d
      have hlim : ∀ m ∈ p.support,
          Tendsto (fun k : ℕ => (TopInJ.scaledTop j d k p).coeff m - TopInJ.topCoeff j d p m)
            atTop (nhds 0) := by
        intro m hm
        apply TopInJ.tendsto_coeff_scaledTop_sub_topCoeff p j d m
        simpa using (Finset.le_sup (f := fun m : Fin n →₀ ℕ => m j) hm)
      have hdiff (k : ℕ) (hk1 : 1 ≤ k) (s : ℂ) (hs : ‖s‖ ≤ ρ) :
          (TopInJ.affPoly (TopInJ.scaledTop j d k p) wc Δ).eval s - P.eval s =
            ∑ m ∈ p.support, ((MvPolynomial.coeff (R := ℝ) m (TopInJ.scaledTop j d k p) : ℂ) -
                (TopInJ.topCoeff j d p m : ℂ)) * ∏ i : Fin n, (wc i + s * Δ i) ^ (m i) := by
        dsimp [P]
        rw [TopInJ.affPoly_eval, TopInJ.affPoly_eval]
        have h1 : MvPolynomial.aeval (R := ℝ) (fun i => wc i + s * Δ i)
              (TopInJ.scaledTop j d k p) =
            ∑ m ∈ p.support, (MvPolynomial.coeff (R := ℝ) m (TopInJ.scaledTop j d k p) : ℂ) *
              ∏ i : Fin n, (wc i + s * Δ i) ^ (m i) := by
          exact TopInJ.aeval_eq_sum_of_support_subset p.support (TopInJ.scaledTop j d k p)
            (TopInJ.scaledTop_support_subset p j d k hk1) (fun i => wc i + s * Δ i)
        have h2 : MvPolynomial.aeval (R := ℝ) (fun i => wc i + s * Δ i) q =
            ∑ m ∈ p.support, (TopInJ.topCoeff j d p m : ℂ) *
              ∏ i : Fin n, (wc i + s * Δ i) ^ (m i) := by
          rw [hq_sum]
          rw [TopInJ.aeval_sum_monomial]
        rw [h1, h2]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro m hm
        ring
      have hclose_ev : ∀ᶠ k in atTop, ∀ s : ℂ, ‖s‖ ≤ ρ →
          ‖(TopInJ.affPoly (TopInJ.scaledTop j d k p) wc Δ).eval s - P.eval s‖ < δ / 2 := by
        have hU := TopInJ.tendsto_uniform_eval_sub p.support
            (fun k m => (TopInJ.scaledTop j d k p).coeff m) (TopInJ.topCoeff j d p) hlim
            wc Δ (le_of_lt hρ0) (δ / 2) (by linarith)
        filter_upwards [Filter.eventually_ge_atTop 1, hU] with k hk1 hkU
        intro s hs
        have hd := hdiff k hk1 s hs
        rw [hd]
        exact hkU s hs
      have hsmall_ev : ∀ᶠ k in atTop,
          ‖(TopInJ.affPoly (TopInJ.scaledTop j d k p) wc Δ).eval 0‖ < δ / 2 := by
        have hU := TopInJ.tendsto_uniform_eval_sub p.support
            (fun k m => (TopInJ.scaledTop j d k p).coeff m) (TopInJ.topCoeff j d p) hlim
            wc Δ (le_of_lt hρ0) (δ / 2) (by linarith)
        filter_upwards [Filter.eventually_ge_atTop 1, hU] with k hk1 hkU
        have hd := hdiff k hk1 0 (by simpa using hρ0.le)
        have hb := hkU 0 (by simpa using hρ0.le)
        rw [← hd] at hb
        simpa [hP0e] using hb
      have hall_ev : ∀ᶠ k in atTop, 1 ≤ k ∧
          (∀ s : ℂ, s ∈ sphere (0 : ℂ) ρ →
            ‖(TopInJ.affPoly (TopInJ.scaledTop j d k p) wc Δ).eval s - P.eval s‖ < δ / 2) ∧
          ‖(TopInJ.affPoly (TopInJ.scaledTop j d k p) wc Δ).eval 0‖ < δ / 2 := by
        filter_upwards [Filter.eventually_ge_atTop 1, hclose_ev, hsmall_ev] with k hk1 hc hs
        refine ⟨hk1, ?_, hs⟩
        intro s hsph
        have hnorm_le : ‖s‖ ≤ ρ := by
          have hn := mem_sphere_iff_norm.mp hsph
          exact le_of_eq (by simpa using hn)
        exact hc s hnorm_le
      rw [Filter.eventually_atTop] at hall_ev
      obtain ⟨N, hN⟩ := hall_ev
      have hkN := hN N (le_rfl)
      rcases hkN with ⟨hk1, hclose_k, hsmall_k⟩
      have hqsphere : ∀ z : ℂ, z ∈ sphere (0 : ℂ) ρ → δ ≤ ‖P.eval z‖ := hδsphere
      obtain ⟨s0, hball, hs0root⟩ := rrl_root_in_closedBall
          (TopInJ.affPoly (TopInJ.scaledTop j d N p) wc Δ) P (0 : ℂ) (ρ := ρ) (δ := δ)
          hρ0 hδ0 hP0e hclose_k hsmall_k hqsphere
      let zU : Fin n → UpperHalfPlane := fun i =>
        ⟨wc i + s0 * Δ i, hcoord s0 (by simpa using hball) i⟩
      have hstable : MvPolynomial.aeval (R := ℝ) (fun i => ((zU i : UpperHalfPlane) : ℂ))
          (TopInJ.scaledTop j d N p) ≠ 0 :=
        TopInJ.scaledTop_stable p j d N hk1 hstabR zU
      have hzero_aeval : MvPolynomial.aeval (R := ℝ) (fun i => ((zU i : UpperHalfPlane) : ℂ))
          (TopInJ.scaledTop j d N p) = 0 := by
        rw [TopInJ.affPoly_eval] at hs0root
        simpa [zU] using hs0root
      exact hstable hzero_aeval

end Commons.Analysis.MvPolynomial