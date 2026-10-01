import Mathlib
import Submission.Work.ZeroDensity.LogFree.GramProps
import Submission.Work.ZeroDensity.LogFree.PoleDefs
import Submission.Work.ZeroDensity.LogFree.poleResidue_mul_log_sq
import Submission.Work.ZeroDensity.LogFree.Defs
import Submission.Work.ZeroDensity.LogFree.DualitySetup
import Submission.Work.ZeroDensity.LogFree.GramSameProof
import Submission.Work.ZeroDensity.Jutila.halaszDualityFrame
open DirichletCharacter Complex Finset
open scoped Classical BigOperators
noncomputable section
namespace Work.ZeroDensity.LogFree.HalaszGram

open Work.ZeroDensity.LogFree

/-- Conjugation of a complex power of a positive real. -/
lemma conj_cpow_ofReal {x : ℝ} (hx : 0 < x) (z : ℂ) :
    starRingEnd ℂ ((x : ℂ) ^ z) = (x : ℂ) ^ (starRingEnd ℂ z) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.cpow_def_of_ne_zero hx0,
    (Complex.exp_conj (Complex.log (x : ℂ) * z)).symm]
  congr 1
  rw [map_mul, ← Complex.ofReal_log hx.le, Complex.conj_ofReal]

/-- Termwise: the product `a_i * conj(a_j)` of two summands of the Halász bilinear form. -/
lemma halasz_termwise {q : ℕ} [NeZero q] (χ χ' : DirichletCharacter ℂ q) {ρ ρ' : ℂ}
    (hρ : 1/2 < ρ.re) (hρ' : 1/2 < ρ'.re) (η η' : ℂ) (n : ℕ) :
    (η * (χ (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ)))
        * starRingEnd ℂ (η' * (χ' (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ')))
      = η * (starRingEnd ℂ η') * ((χ * χ'⁻¹) (n : ZMod q))
          * ((n : ℂ) ^ ((1 : ℂ) - ρ - (starRingEnd ℂ) ρ')) := by
  have hz : ((1/2 : ℂ) - ρ) + starRingEnd ℂ ((1/2 : ℂ) - ρ') = 1 - ρ - starRingEnd ℂ ρ' := by
    have h2 : starRingEnd ℂ ((1/2 : ℂ)) = 1/2 := by apply Complex.ext <;> simp
    rw [map_sub, h2]; ring
  by_cases hn : n = 0
  · have hne0 : (1/2 : ℂ) - ρ ≠ 0 := by
      intro h
      have h2 : (1/2 : ℝ) - ρ.re = 0 := by
        have := congrArg Complex.re h; simpa using this
      linarith
    have hne1 : (1 : ℂ) - ρ - starRingEnd ℂ ρ' ≠ 0 := by
      intro h
      have h2 : (1 : ℝ) - ρ.re - ρ'.re = 0 := by
        have := congrArg Complex.re h
        simpa [Complex.sub_re, Complex.one_re, Complex.conj_re] using this
      linarith
    subst hn
    simp only [Nat.cast_zero]
    rw [Complex.zero_cpow (x := (1/2 : ℂ) - ρ) hne0,
      Complex.zero_cpow (x := (1 : ℂ) - ρ - starRingEnd ℂ ρ') hne1]
    ring
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hconj : starRingEnd ℂ ((n : ℂ) ^ ((1/2 : ℂ) - ρ'))
        = (n : ℂ) ^ (starRingEnd ℂ ((1/2 : ℂ) - ρ')) := by
      rw [show (n : ℂ) = (((n : ℝ)) : ℂ) from by push_cast; ring]
      exact conj_cpow_ofReal hnpos _
    have hchar : starRingEnd ℂ (χ' (n : ZMod q)) = (χ'⁻¹) (n : ZMod q) := by
      simpa only [Complex.star_def] using MulChar.star_apply' χ' (n : ZMod q)
    have hstar : starRingEnd ℂ (η' * (χ' (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ')))
        = (starRingEnd ℂ η') * ((χ'⁻¹) (n : ZMod q))
            * ((n : ℂ) ^ (starRingEnd ℂ ((1/2 : ℂ) - ρ'))) := by
      rw [map_mul, map_mul, hchar, hconj]
    have hcomb : ((n : ℂ) ^ ((1/2 : ℂ) - ρ)) * ((n : ℂ) ^ (starRingEnd ℂ ((1/2 : ℂ) - ρ')))
        = (n : ℂ) ^ ((1 : ℂ) - ρ - (starRingEnd ℂ) ρ') := by
      rw [← Complex.cpow_add _ _ hn0, hz]
    rw [hstar]
    calc η * (χ (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ))
          * ((starRingEnd ℂ η') * ((χ'⁻¹) (n : ZMod q))
              * ((n : ℂ) ^ (starRingEnd ℂ ((1/2 : ℂ) - ρ'))))
        = (η * (starRingEnd ℂ η') * ((χ (n : ZMod q)) * ((χ'⁻¹) (n : ZMod q))))
            * (((n : ℂ) ^ ((1/2 : ℂ) - ρ))
                * ((n : ℂ) ^ (starRingEnd ℂ ((1/2 : ℂ) - ρ')))) := by ring
      _ = (η * (starRingEnd ℂ η') * ((χ (n : ZMod q)) * ((χ'⁻¹) (n : ZMod q))))
            * ((n : ℂ) ^ ((1 : ℂ) - ρ - (starRingEnd ℂ) ρ')) := by rw [hcomb]
      _ = η * (starRingEnd ℂ η') * ((χ * χ'⁻¹) (n : ZMod q))
            * ((n : ℂ) ^ ((1 : ℂ) - ρ - (starRingEnd ℂ) ρ')) := by
            rw [MulChar.mul_apply]

/-- Termwise product identity, `q`-free (no character). -/
lemma halasz_termwise_free {ρ ρ' : ℂ} (hρ : 1/2 < ρ.re) (hρ' : 1/2 < ρ'.re) (η η' : ℂ) (n : ℕ) :
    (η * ((n : ℂ) ^ ((1/2 : ℂ) - ρ))) * starRingEnd ℂ (η' * ((n : ℂ) ^ ((1/2 : ℂ) - ρ')))
      = η * (starRingEnd ℂ η') * ((n : ℂ) ^ ((1 : ℂ) - ρ - (starRingEnd ℂ) ρ')) := by
  have hz : ((1/2 : ℂ) - ρ) + starRingEnd ℂ ((1/2 : ℂ) - ρ') = 1 - ρ - starRingEnd ℂ ρ' := by
    have h2 : starRingEnd ℂ ((1/2 : ℂ)) = 1/2 := by apply Complex.ext <;> simp
    rw [map_sub, h2]; ring
  by_cases hn : n = 0
  · have hne0 : (1/2 : ℂ) - ρ ≠ 0 := by
      intro h
      have h2 : (1/2 : ℝ) - ρ.re = 0 := by
        have := congrArg Complex.re h; simpa using this
      linarith
    have hne1 : (1 : ℂ) - ρ - starRingEnd ℂ ρ' ≠ 0 := by
      intro h
      have h2 : (1 : ℝ) - ρ.re - ρ'.re = 0 := by
        have := congrArg Complex.re h
        simpa [Complex.sub_re, Complex.one_re, Complex.conj_re] using this
      linarith
    subst hn
    simp only [Nat.cast_zero]
    rw [Complex.zero_cpow (x := (1/2 : ℂ) - ρ) hne0,
      Complex.zero_cpow (x := (1 : ℂ) - ρ - starRingEnd ℂ ρ') hne1]
    ring
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hconj : starRingEnd ℂ ((n : ℂ) ^ ((1/2 : ℂ) - ρ'))
        = (n : ℂ) ^ (starRingEnd ℂ ((1/2 : ℂ) - ρ')) := by
      rw [show (n : ℂ) = (((n : ℝ)) : ℂ) from by push_cast; ring]
      exact conj_cpow_ofReal hnpos _
    have hstar : starRingEnd ℂ (η' * ((n : ℂ) ^ ((1/2 : ℂ) - ρ')))
        = (starRingEnd ℂ η') * ((n : ℂ) ^ (starRingEnd ℂ ((1/2 : ℂ) - ρ'))) := by
      rw [map_mul, hconj]
    have hcomb : ((n : ℂ) ^ ((1/2 : ℂ) - ρ)) * ((n : ℂ) ^ (starRingEnd ℂ ((1/2 : ℂ) - ρ')))
        = (n : ℂ) ^ ((1 : ℂ) - ρ - (starRingEnd ℂ) ρ') := by
      rw [← Complex.cpow_add _ _ hn0, hz]
    rw [hstar]
    calc η * ((n : ℂ) ^ ((1/2 : ℂ) - ρ))
          * ((starRingEnd ℂ η') * ((n : ℂ) ^ (starRingEnd ℂ ((1/2 : ℂ) - ρ'))))
        = (η * (starRingEnd ℂ η'))
            * (((n : ℂ) ^ ((1/2 : ℂ) - ρ))
                * ((n : ℂ) ^ (starRingEnd ℂ ((1/2 : ℂ) - ρ')))) := by ring
      _ = (η * (starRingEnd ℂ η')) * ((n : ℂ) ^ ((1 : ℂ) - ρ - (starRingEnd ℂ) ρ')) := by
            rw [hcomb]
      _ = η * (starRingEnd ℂ η') * ((n : ℂ) ^ ((1 : ℂ) - ρ - (starRingEnd ℂ) ρ')) := by ring

/-- The complex-valued expansion of the squared modulus of a sum. -/
lemma halasz_expand_complex {q : ℕ} [NeZero q] {ι : Type*} (s : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (ρ : ι → ℂ) (hρ : ∀ i ∈ s, 1/2 < (ρ i).re) (η : ι → ℂ)
    (n : ℕ) :
    ((‖∑ i ∈ s, η i * (χ i (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖ ^ 2 : ℝ) : ℂ)
      = ∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * ((χ i * (χ j)⁻¹) (n : ZMod q))
          * ((n : ℂ) ^ ((1 : ℂ) - ρ i - star (ρ j))) := by
  set a : ι → ℂ := fun i => η i * (χ i (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i)) with ha
  rw [Complex.sq_norm, ← Complex.mul_conj]
  rw [Complex.star_def, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => ?_))
  exact halasz_termwise (χ i) (χ j) (hρ i hi) (hρ j hj) (η i) (η j) n

/-- The real-valued expansion of the squared modulus of a sum. -/
lemma halasz_expand {q : ℕ} [NeZero q] {ι : Type*} (s : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (ρ : ι → ℂ) (hρ : ∀ i ∈ s, 1/2 < (ρ i).re) (η : ι → ℂ)
    (n : ℕ) :
    ‖∑ i ∈ s, η i * (χ i (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖ ^ 2
      = (∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * ((χ i * (χ j)⁻¹) (n : ZMod q))
          * ((n : ℂ) ^ ((1 : ℂ) - ρ i - star (ρ j)))).re := by
  have h := halasz_expand_complex s χ ρ hρ η n
  rw [← h, Complex.ofReal_re]

/-- The complex-valued expansion, `q`-free. -/
lemma halasz_expand_free_complex {ι : Type*} (s : Finset ι)
    (ρ : ι → ℂ) (hρ : ∀ i ∈ s, 1/2 < (ρ i).re) (η : ι → ℂ) (n : ℕ) :
    ((‖∑ i ∈ s, η i * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖ ^ 2 : ℝ) : ℂ)
      = ∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * ((n : ℂ) ^ ((1 : ℂ) - ρ i - star (ρ j))) := by
  set a : ι → ℂ := fun i => η i * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i)) with ha
  rw [Complex.sq_norm, ← Complex.mul_conj]
  rw [Complex.star_def, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => ?_))
  exact halasz_termwise_free (hρ i hi) (hρ j hj) (η i) (η j) n

/-- The real-valued expansion, `q`-free. -/
lemma halasz_expand_free {ι : Type*} (s : Finset ι)
    (ρ : ι → ℂ) (hρ : ∀ i ∈ s, 1/2 < (ρ i).re) (η : ι → ℂ) (n : ℕ) :
    ‖∑ i ∈ s, η i * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖ ^ 2
      = (∑ i ∈ s, ∑ j ∈ s, η i * star (η j)
          * ((n : ℂ) ^ ((1 : ℂ) - ρ i - star (ρ j)))).re := by
  have h := halasz_expand_free_complex s ρ hρ η n
  rw [← h, Complex.ofReal_re]

/-- Pointwise domination for a block of indices sharing one character: dropping the characters
can only increase the modulus. -/
lemma halasz_block_pointwise {q : ℕ} [NeZero q] {ι : Type*} (s : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (ρ : ι → ℂ) (η : ι → ℂ)
    (χ₀ : DirichletCharacter ℂ q) (hχ : ∀ i ∈ s, χ i = χ₀) (n : ℕ) :
    ‖∑ i ∈ s, η i * (χ i (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖
      ≤ ‖∑ i ∈ s, η i * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖ := by
  have hcongr : (∑ i ∈ s, η i * (χ i (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i)))
      = χ₀ (n : ZMod q) * ∑ i ∈ s, η i * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [hχ i hi]; ring
  rw [hcongr, norm_mul]
  calc ‖χ₀ (n : ZMod q)‖ * ‖∑ i ∈ s, η i * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖
      ≤ 1 * ‖∑ i ∈ s, η i * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖ :=
        mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one _ _) (norm_nonneg _)
    _ = ‖∑ i ∈ s, η i * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖ := one_mul _



/-- The Gram series is summable (with the `gfun` damping). -/
lemma summable_gramTerm (q : ℕ) [NeZero q] (W X U' : ℝ) (hX : 0 < X) (hU' : 0 < U')
    (hle : U' ≤ X) {ρ ρ' : ℂ} (hρρ' : 1 ≤ ρ.re + ρ'.re) :
    Summable (fun n : ℕ => ((thetaS W n : ℂ))^2 * ((n : ℂ) ^ ((1:ℂ) - ρ - star ρ'))
      * ((gfun X U' n : ℝ) : ℂ)) := by
  have hre : ((1:ℂ) - ρ - star ρ').re ≤ 0 := by
    have h1 : (star ρ').re = ρ'.re := by
      rw [Complex.star_def]; exact Complex.conj_re ρ'
    have h2 : ((1:ℂ) - ρ - star ρ').re = 1 - (ρ.re + ρ'.re) := by
      rw [Complex.sub_re, Complex.sub_re, Complex.one_re, h1]; ring
    rw [h2]
    linarith [hρρ']
  have hbase := summable_thetaS_sq_mul_exp W X hX (s₀ := (1:ℂ) - ρ - star ρ') hre
  refine Summable.of_norm_bounded (g := fun n : ℕ => ‖((thetaS W n : ℂ))^2
    * ((n : ℂ) ^ ((1:ℂ) - ρ - star ρ')) * ((Real.exp (-((n : ℝ)/X)) : ℝ) : ℂ)‖)
    hbase.norm (fun n => ?_)
  have hgf : |gfun X U' n| ≤ Real.exp (-((n:ℝ)/X)) := by
    rw [abs_of_nonneg (gfun_nonneg hU' hle n), gfun]
    linarith [Real.exp_nonneg (-((n:ℝ)/U'))]
  calc ‖((thetaS W n : ℂ))^2 * ((n : ℂ) ^ ((1:ℂ) - ρ - star ρ'))
        * ((gfun X U' n : ℝ) : ℂ)‖
      = ‖((thetaS W n : ℂ))^2‖ * ‖((n : ℂ) ^ ((1:ℂ) - ρ - star ρ'))‖ * |gfun X U' n| := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖((thetaS W n : ℂ))^2‖ * ‖((n : ℂ) ^ ((1:ℂ) - ρ - star ρ'))‖
          * Real.exp (-((n:ℝ)/X)) := by
        have h1 : (0:ℝ) ≤ ‖((thetaS W n : ℂ))^2‖ := norm_nonneg _
        have h2 : (0:ℝ) ≤ ‖((n : ℂ) ^ ((1:ℂ) - ρ - star ρ'))‖ := norm_nonneg _
        exact mul_le_mul_of_nonneg_left hgf (mul_nonneg h1 h2)
    _ = ‖((thetaS W n : ℂ))^2 * ((n : ℂ) ^ ((1:ℂ) - ρ - star ρ'))
          * ((Real.exp (-((n : ℝ)/X)) : ℝ) : ℂ)‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.exp_nonneg _)]


/-- The damped `θ`-weight of the Gram form. -/
def gramWeight (W X U' : ℝ) (n : ℕ) : ℝ := (thetaS W n)^2 * gfun X U' n

/-- The `(i,j)` inner summand of the Gram form. -/
def gramInner {q : ℕ} [NeZero q] (χ χ' : DirichletCharacter ℂ q) (ρ ρ' : ℂ) (n : ℕ) : ℂ :=
  ((χ * χ'⁻¹) (n : ZMod q)) * ((n : ℂ) ^ ((1 : ℂ) - ρ - star ρ'))

lemma gramWeight_re (W X U' : ℝ) (n : ℕ) :
    ((((thetaS W n : ℂ))^2 * ((gfun X U' n : ℝ) : ℂ))).re = gramWeight W X U' n := by
  simp only [Complex.mul_re, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im,
    gramWeight]
  ring

lemma gramWeight_im (W X U' : ℝ) (n : ℕ) :
    ((((thetaS W n : ℂ))^2 * ((gfun X U' n : ℝ) : ℂ))).im = 0 := by
  simp only [Complex.mul_im, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma gramEntry_eq_tsum {q : ℕ} [NeZero q] (W X U' : ℝ) (χ χ' : DirichletCharacter ℂ q)
    (ρ ρ' : ℂ) :
    gramEntry q W X U' χ χ' ρ ρ'
      = ∑' n, ((thetaS W n : ℂ))^2 * gramInner χ χ' ρ ρ' n * ((gfun X U' n : ℝ) : ℂ) := by
  unfold gramEntry
  refine tsum_congr (fun n => ?_)
  simp only [gramInner, gfun, Complex.ofReal_exp, Complex.star_def]
  push_cast
  ring


/-- The `n`-th summand of the Gram entry, with the `(i,j)` character factor. -/
def gramFull {q : ℕ} [NeZero q] (W X U' : ℝ) (χ χ' : DirichletCharacter ℂ q) (ρ ρ' : ℂ)
    (n : ℕ) : ℂ := ((thetaS W n : ℂ))^2 * gramInner χ χ' ρ ρ' n * ((gfun X U' n : ℝ) : ℂ)

lemma gramEntry_eq_tsum' {q : ℕ} [NeZero q] (W X U' : ℝ) (χ χ' : DirichletCharacter ℂ q)
    (ρ ρ' : ℂ) :
    gramEntry q W X U' χ χ' ρ ρ' = ∑' n, gramFull W X U' χ χ' ρ ρ' n := by
  unfold gramEntry
  refine tsum_congr (fun n => ?_)
  simp only [gramFull, gramInner, gfun, Complex.ofReal_exp, Complex.star_def]
  push_cast
  ring

lemma summable_gramFull {q : ℕ} [NeZero q] (W X U' : ℝ) (hX : 0 < X) (hU' : 0 < U')
    (hle : U' ≤ X) (χ χ' : DirichletCharacter ℂ q) {ρ ρ' : ℂ} (hρρ' : 1 ≤ ρ.re + ρ'.re) :
    Summable (fun n : ℕ => gramFull W X U' χ χ' ρ ρ' n) := by
  have hbase := summable_gramTerm q W X U' hX hU' hle hρρ'
  refine Summable.of_norm_bounded (g := fun n : ℕ => ‖((thetaS W n : ℂ))^2
    * ((n : ℂ) ^ ((1:ℂ) - ρ - star ρ')) * ((gfun X U' n : ℝ) : ℂ)‖) hbase.norm (fun n => ?_)
  have hchi : ‖(χ * χ'⁻¹) (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
  have hg : |gfun X U' n| = ‖((gfun X U' n : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hA : (0:ℝ) ≤ ‖((thetaS W n : ℂ))^2‖ := norm_nonneg _
  have hB : (0:ℝ) ≤ ‖((n : ℂ) ^ ((1:ℂ) - ρ - star ρ'))‖ := norm_nonneg _
  have hC : (0:ℝ) ≤ |gfun X U' n| := abs_nonneg _
  calc ‖gramFull W X U' χ χ' ρ ρ' n‖
      = ‖((thetaS W n : ℂ))^2‖ * ‖(χ * χ'⁻¹) (n : ZMod q)‖
          * ‖((n : ℂ) ^ ((1:ℂ) - ρ - star ρ'))‖ * |gfun X U' n| := by
        simp only [gramFull, gramInner, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        ring
    _ ≤ ‖((thetaS W n : ℂ))^2‖ * 1 * ‖((n : ℂ) ^ ((1:ℂ) - ρ - star ρ'))‖ * |gfun X U' n| := by
        have h1 : ‖((thetaS W n : ℂ))^2‖ * ‖(χ * χ'⁻¹) (n : ZMod q)‖
            ≤ ‖((thetaS W n : ℂ))^2‖ * 1 := mul_le_mul_of_nonneg_left hchi hA
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hB) hC
    _ = ‖((thetaS W n : ℂ))^2 * ((n : ℂ) ^ ((1:ℂ) - ρ - star ρ')) * ((gfun X U' n : ℝ) : ℂ)‖ := by
        rw [norm_mul, norm_mul, hg]
        ring

set_option maxHeartbeats 4000000 in
/-- **The Gram double sum is the `tsum` of the damped squared moduli.** -/
lemma gramForm_eq_tsum {q : ℕ} [NeZero q] {ι : Type*} (s : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (ρ : ι → ℂ) (hρ : ∀ i ∈ s, 1/2 < (ρ i).re)
    (η : ι → ℂ) (W X U' : ℝ) (hW : 1 < W) (hX : 0 < X) (hU' : 0 < U') (hle : U' ≤ X) :
    (∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j)).re
      = ∑' n, gramWeight W X U' n
          * ‖∑ i ∈ s, η i * (χ i (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖^2 := by
  classical
  have hsumm : ∀ i ∈ s, ∀ j ∈ s, Summable (fun n : ℕ =>
      η i * star (η j) * gramFull W X U' (χ i) (χ j) (ρ i) (ρ j) n) := by
    intro i hi j hj
    exact (summable_gramFull (q := q) W X U' hX hU' hle (χ i) (χ j)
      (by linarith [hρ i hi, hρ j hj])).mul_left _
  have hstep : ∀ i ∈ s, Summable (fun n : ℕ =>
      ∑ j ∈ s, η i * star (η j) * gramFull W X U' (χ i) (χ j) (ρ i) (ρ j) n) :=
    fun i hi => summable_sum (fun j hj => hsumm i hi j hj)
  have hLHS : (∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j))
      = ∑' n, ∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * gramFull W X U' (χ i) (χ j) (ρ i) (ρ j) n := by
    have h1 : ∀ i ∈ s, ∀ j ∈ s, η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j)
        = ∑' n, η i * star (η j) * gramFull W X U' (χ i) (χ j) (ρ i) (ρ j) n := by
      intro i hi j hj
      rw [gramEntry_eq_tsum' (q := q), tsum_mul_left]
    rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => h1 i hi j hj))]
    have step1 : (∑ i ∈ s, ∑ j ∈ s, ∑' n,
          η i * star (η j) * gramFull W X U' (χ i) (χ j) (ρ i) (ρ j) n)
        = ∑ i ∈ s, ∑' n, ∑ j ∈ s,
          η i * star (η j) * gramFull W X U' (χ i) (χ j) (ρ i) (ρ j) n :=
      Finset.sum_congr rfl (fun i hi => (Summable.tsum_finsetSum (s := s)
        (f := fun j n => η i * star (η j) * gramFull W X U' (χ i) (χ j) (ρ i) (ρ j) n)
        (fun j hj => hsumm i hi j hj)).symm)
    have step2 : (∑ i ∈ s, ∑' n, ∑ j ∈ s,
          η i * star (η j) * gramFull W X U' (χ i) (χ j) (ρ i) (ρ j) n)
        = ∑' n, ∑ i ∈ s, ∑ j ∈ s,
          η i * star (η j) * gramFull W X U' (χ i) (χ j) (ρ i) (ρ j) n :=
      (Summable.tsum_finsetSum (s := s)
        (f := fun i n => ∑ j ∈ s, η i * star (η j) * gramFull W X U' (χ i) (χ j) (ρ i) (ρ j) n)
        (fun i hi => hstep i hi)).symm
    rw [step1, step2]
  have hsummAll : Summable (fun n : ℕ =>
      ∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * gramFull W X U' (χ i) (χ j) (ρ i) (ρ j) n) :=
    summable_sum hstep
  rw [hLHS, Complex.re_tsum hsummAll]
  refine tsum_congr (fun n => ?_)
  have hfac : (∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * gramFull W X U' (χ i) (χ j) (ρ i) (ρ j) n)
      = (((thetaS W n : ℂ))^2 * ((gfun X U' n : ℝ) : ℂ))
          * (∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * gramInner (χ i) (χ j) (ρ i) (ρ j) n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [gramFull]
    ring
  have hexp : (∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * gramInner (χ i) (χ j) (ρ i) (ρ j) n).re
      = ‖∑ i ∈ s, η i * (χ i (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖^2 := by
    rw [halasz_expand s χ ρ hρ η n]
    refine congrArg Complex.re ?_
    refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => ?_))
    simp only [gramInner]
    ring
  rw [hfac, Complex.mul_re, gramWeight_re, gramWeight_im, hexp]
  ring


/-- The `n`-th summand of the `q`-free Gram entry. -/
def gramFullFree {q : ℕ} [NeZero q] (W X U' : ℝ) (ρ ρ' : ℂ) (n : ℕ) : ℂ :=
  ((thetaS W n : ℂ))^2 * ((n : ℂ) ^ ((1 : ℂ) - ρ - star ρ')) * ((gfun X U' n : ℝ) : ℂ)

lemma gramEntryFree_eq_tsum {q : ℕ} [NeZero q] (W X U' : ℝ) (ρ ρ' : ℂ) :
    gramEntryFree W X U' ρ ρ' = ∑' n, gramFullFree (q := q) W X U' ρ ρ' n := by
  unfold gramEntryFree
  refine tsum_congr (fun n => ?_)
  simp only [gramFullFree, gfun, Complex.ofReal_exp, Complex.star_def]

lemma summable_gramFullFree {q : ℕ} [NeZero q] (W X U' : ℝ) (hX : 0 < X) (hU' : 0 < U')
    (hle : U' ≤ X) {ρ ρ' : ℂ} (hρρ' : 1 ≤ ρ.re + ρ'.re) :
    Summable (fun n : ℕ => gramFullFree (q := q) W X U' ρ ρ' n) := by
  refine Summable.congr (summable_gramTerm q W X U' hX hU' hle hρρ') (fun n => ?_)
  simp only [gramFullFree, gfun, Complex.ofReal_exp, Complex.star_def]

set_option maxHeartbeats 4000000 in
/-- **The `q`-free Gram double sum is the `tsum` of the damped squared moduli.** -/
lemma gramFormFree_eq_tsum {q : ℕ} [NeZero q] {ι : Type*} (s : Finset ι)
    (ρ : ι → ℂ) (hρ : ∀ i ∈ s, 1/2 < (ρ i).re)
    (η : ι → ℂ) (W X U' : ℝ) (hW : 1 < W) (hX : 0 < X) (hU' : 0 < U') (hle : U' ≤ X) :
    (∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * gramEntryFree W X U' (ρ i) (ρ j)).re
      = ∑' n, gramWeight W X U' n * ‖∑ i ∈ s, η i * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖^2 := by
  classical
  have hsumm : ∀ i ∈ s, ∀ j ∈ s, Summable (fun n : ℕ =>
      η i * star (η j) * gramFullFree (q := q) W X U' (ρ i) (ρ j) n) := by
    intro i hi j hj
    exact (summable_gramFullFree (q := q) W X U' hX hU' hle
      (by linarith [hρ i hi, hρ j hj])).mul_left _
  have hstep : ∀ i ∈ s, Summable (fun n : ℕ =>
      ∑ j ∈ s, η i * star (η j) * gramFullFree (q := q) W X U' (ρ i) (ρ j) n) :=
    fun i hi => summable_sum (fun j hj => hsumm i hi j hj)
  have hLHS : (∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * gramEntryFree W X U' (ρ i) (ρ j))
      = ∑' n, ∑ i ∈ s, ∑ j ∈ s,
          η i * star (η j) * gramFullFree (q := q) W X U' (ρ i) (ρ j) n := by
    have h1 : ∀ i ∈ s, ∀ j ∈ s, η i * star (η j) * gramEntryFree W X U' (ρ i) (ρ j)
        = ∑' n, η i * star (η j) * gramFullFree (q := q) W X U' (ρ i) (ρ j) n := by
      intro i hi j hj
      rw [gramEntryFree_eq_tsum (q := q), tsum_mul_left]
    rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => h1 i hi j hj))]
    have step1 : (∑ i ∈ s, ∑ j ∈ s, ∑' n,
          η i * star (η j) * gramFullFree (q := q) W X U' (ρ i) (ρ j) n)
        = ∑ i ∈ s, ∑' n, ∑ j ∈ s,
          η i * star (η j) * gramFullFree (q := q) W X U' (ρ i) (ρ j) n :=
      Finset.sum_congr rfl (fun i hi => (Summable.tsum_finsetSum (s := s)
        (f := fun j n => η i * star (η j) * gramFullFree (q := q) W X U' (ρ i) (ρ j) n)
        (fun j hj => hsumm i hi j hj)).symm)
    have step2 : (∑ i ∈ s, ∑' n, ∑ j ∈ s,
          η i * star (η j) * gramFullFree (q := q) W X U' (ρ i) (ρ j) n)
        = ∑' n, ∑ i ∈ s, ∑ j ∈ s,
          η i * star (η j) * gramFullFree (q := q) W X U' (ρ i) (ρ j) n :=
      (Summable.tsum_finsetSum (s := s)
        (f := fun i n => ∑ j ∈ s, η i * star (η j) * gramFullFree (q := q) W X U' (ρ i) (ρ j) n)
        (fun i hi => hstep i hi)).symm
    rw [step1, step2]
  have hsummAll : Summable (fun n : ℕ =>
      ∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * gramFullFree (q := q) W X U' (ρ i) (ρ j) n) :=
    summable_sum hstep
  rw [hLHS, Complex.re_tsum hsummAll]
  refine tsum_congr (fun n => ?_)
  have hfac : (∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * gramFullFree (q := q) W X U' (ρ i) (ρ j) n)
      = (((thetaS W n : ℂ))^2 * ((gfun X U' n : ℝ) : ℂ))
          * (∑ i ∈ s, ∑ j ∈ s, η i * star (η j)
              * ((n : ℂ) ^ ((1 : ℂ) - ρ i - star (ρ j)))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [gramFullFree]
    ring
  have hexp : (∑ i ∈ s, ∑ j ∈ s, η i * star (η j)
      * ((n : ℂ) ^ ((1 : ℂ) - ρ i - star (ρ j)))).re
      = ‖∑ i ∈ s, η i * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖^2 :=
    (halasz_expand_free s ρ hρ η n).symm
  rw [hfac, Complex.mul_re, gramWeight_re, gramWeight_im, hexp]
  ring


/-- **The pole form over a block.**  If the pole form is bounded for every `1/L`-separated system
of indices, it is bounded over any sub-block `u` of a larger system (the indices of `u` being
`1/L`-separated among themselves). -/
lemma pole_block {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι] (ρ : ι → ℂ) (X U' L H C σ : ℝ)
    (hC : ∀ (m' : ℕ) (ρ' : Fin m' → ℂ) (z' : Fin m' → ℂ),
        (∀ i, σ ≤ (ρ' i).re) → (∀ i, (ρ' i).re < 1) → (∀ i, |(ρ' i).im| ≤ H) →
        (∀ i j, i ≠ j → 1 / L ≤ |(ρ' i).im - (ρ' j).im|) →
        (poleGram m' X U' ρ' z').re ≤ C * ∑ i, ‖z' i‖ ^ 2)
    (u : Finset ι) (hre : ∀ i ∈ u, σ ≤ (ρ i).re) (him : ∀ i ∈ u, |(ρ i).im| ≤ H)
    (hlt : ∀ i ∈ u, (ρ i).re < 1)
    (hsep : ∀ i ∈ u, ∀ j ∈ u, i ≠ j → 1 / L ≤ |(ρ i).im - (ρ j).im|)
    (z : ι → ℂ) :
    (∑ i ∈ u, ∑ j ∈ u, z i * star (z j) * poleK X U' (ρ i) (ρ j)).re
      ≤ C * ∑ i ∈ u, ‖z i‖ ^ 2 := by
  classical
  set e : ↥u ≃ Fin (Fintype.card ↥u) := Fintype.equivFin ↥u with he
  have hmain := hC (Fintype.card ↥u) (fun k => ρ (e.symm k).1) (fun k => z (e.symm k).1)
    (fun k => hre _ (e.symm k).2) (fun k => hlt _ (e.symm k).2) (fun k => him _ (e.symm k).2)
    (fun k l hkl => hsep (e.symm k).1 (e.symm k).2 (e.symm l).1 (e.symm l).2
      (fun hh => hkl (e.symm.injective (Subtype.ext hh))))
  have hnorm : (∑ k : Fin (Fintype.card ↥u), ‖z (e.symm k).1‖ ^ 2) = ∑ i ∈ u, ‖z i‖ ^ 2 := by
    rw [(Equiv.sum_comp e (fun k : Fin (Fintype.card ↥u) => ‖z (e.symm k).1‖ ^ 2)).symm]
    simp only [Equiv.symm_apply_apply]
    exact Finset.sum_attach u (fun i => ‖z i‖ ^ 2)
  have hform : (poleGram (Fintype.card ↥u) X U' (fun k => ρ (e.symm k).1)
        (fun k => z (e.symm k).1)).re
      = (∑ i ∈ u, ∑ j ∈ u, z i * star (z j) * poleK X U' (ρ i) (ρ j)).re := by
    have h1 : (∑ k : Fin (Fintype.card ↥u), ∑ l : Fin (Fintype.card ↥u),
          z (e.symm k).1 * (starRingEnd ℂ) (z (e.symm l).1)
            * poleK X U' (ρ (e.symm k).1) (ρ (e.symm l).1))
        = ∑ x : ↥u, ∑ y : ↥u, z x.1 * (starRingEnd ℂ) (z y.1) * poleK X U' (ρ x.1) (ρ y.1) := by
      rw [(Equiv.sum_comp e (fun k : Fin (Fintype.card ↥u) =>
        ∑ l : Fin (Fintype.card ↥u),
          z (e.symm k).1 * (starRingEnd ℂ) (z (e.symm l).1)
            * poleK X U' (ρ (e.symm k).1) (ρ (e.symm l).1))).symm]
      simp only [Equiv.symm_apply_apply]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [(Equiv.sum_comp e (fun l : Fin (Fintype.card ↥u) =>
        z x.1 * (starRingEnd ℂ) (z (e.symm l).1) * poleK X U' (ρ x.1) (ρ (e.symm l).1))).symm]
      simp only [Equiv.symm_apply_apply]
    have h2 : (∑ x : ↥u, ∑ y : ↥u, z x.1 * (starRingEnd ℂ) (z y.1) * poleK X U' (ρ x.1) (ρ y.1))
        = ∑ i ∈ u, ∑ j ∈ u, z i * (starRingEnd ℂ) (z j) * poleK X U' (ρ i) (ρ j) := by
      rw [Finset.univ_eq_attach]
      rw [Finset.sum_attach u (fun i => ∑ y ∈ u.attach,
        z i * (starRingEnd ℂ) (z y.1) * poleK X U' (ρ i) (ρ y.1))]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.sum_attach u (fun j => z i * (starRingEnd ℂ) (z j) * poleK X U' (ρ i) (ρ j))]
    unfold poleGram
    beta_reduce
    rw [h1, h2]
    simp only [Complex.star_def]
  rw [hform, hnorm] at hmain
  exact hmain

/-- **The pole bound for same-character sub-blocks**, from the `PoleLargeSieve` interface. -/
lemma pole_all_blocks {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι]
    (χ : ι → DirichletCharacter ℂ q) (ρ : ι → ℂ) (X U' L H C σ : ℝ)
    (hC : ∀ (m' : ℕ) (ρ' : Fin m' → ℂ) (z' : Fin m' → ℂ),
        (∀ i, σ ≤ (ρ' i).re) → (∀ i, (ρ' i).re < 1) → (∀ i, |(ρ' i).im| ≤ H) →
        (∀ i j, i ≠ j → 1 / L ≤ |(ρ' i).im - (ρ' j).im|) →
        (poleGram m' X U' ρ' z').re ≤ C * ∑ i, ‖z' i‖ ^ 2)
    (hσ : ∀ i, σ ≤ (ρ i).re) (hlt : ∀ i, (ρ i).re < 1) (him : ∀ i, |(ρ i).im| ≤ H)
    (hsep : ∀ i j, i ≠ j → χ i = χ j → 1 / L ≤ |(ρ i).im - (ρ j).im|)
    (u : Finset ι) (hc : ∀ i ∈ u, ∀ j ∈ u, χ i = χ j) (z : ι → ℂ) :
    (∑ i ∈ u, ∑ j ∈ u, z i * (starRingEnd ℂ) (z j) * poleK X U' (ρ i) (ρ j)).re
      ≤ C * ∑ i ∈ u, ‖z i‖ ^ 2 := by
  refine pole_block (q := q) ρ X U' L H C σ hC u (fun i _ => hσ i) (fun i _ => him i) (fun i _ => hlt i)
    (fun i hi j hj hij => hsep i j hij (hc i hi j hj)) z

lemma gramWeight_mul_normSq_free {q : ℕ} [NeZero q] {ι : Type*} (u : Finset ι)
    (ρ : ι → ℂ) (hρ : ∀ i ∈ u, 1/2 < (ρ i).re) (η : ι → ℂ) (W X U' : ℝ) (n : ℕ) :
    gramWeight W X U' n * ‖∑ i ∈ u, η i * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖^2
      = (∑ i ∈ u, ∑ j ∈ u,
          η i * star (η j) * gramFullFree (q := q) W X U' (ρ i) (ρ j) n).re := by
  have hfac : (∑ i ∈ u, ∑ j ∈ u, η i * star (η j) * gramFullFree (q := q) W X U' (ρ i) (ρ j) n)
      = (((thetaS W n : ℂ))^2 * ((gfun X U' n : ℝ) : ℂ))
          * (∑ i ∈ u, ∑ j ∈ u, η i * star (η j)
              * ((n : ℂ) ^ ((1 : ℂ) - ρ i - star (ρ j)))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [gramFullFree]
    ring
  have hexp : (∑ i ∈ u, ∑ j ∈ u, η i * star (η j)
      * ((n : ℂ) ^ ((1 : ℂ) - ρ i - star (ρ j)))).re
      = ‖∑ i ∈ u, η i * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖^2 :=
    (halasz_expand_free u ρ hρ η n).symm
  rw [hfac, Complex.mul_re, gramWeight_re, gramWeight_im, hexp]
  ring

/-- `gramWeight`-summability of the damped squared moduli, `q`-free. -/
lemma summable_gramFullFree_normSq {q : ℕ} [NeZero q] {ι : Type*} (u : Finset ι)
    (ρ : ι → ℂ) (hρ : ∀ i ∈ u, 1/2 < (ρ i).re) (η : ι → ℂ) (W X U' : ℝ)
    (hW : 1 < W) (hX : 0 < X) (hU' : 0 < U') (hle : U' ≤ X) :
    Summable (fun n : ℕ => gramWeight W X U' n
      * ‖∑ i ∈ u, η i * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖^2) := by
  classical
  have hsumm : ∀ i ∈ u, ∀ j ∈ u, Summable (fun n : ℕ =>
      η i * star (η j) * gramFullFree (q := q) W X U' (ρ i) (ρ j) n) := by
    intro i hi j hj
    exact (summable_gramFullFree (q := q) W X U' hX hU' hle
      (by linarith [hρ i hi, hρ j hj])).mul_left _
  have hstep : ∀ i ∈ u, Summable (fun n : ℕ =>
      ∑ j ∈ u, η i * star (η j) * gramFullFree (q := q) W X U' (ρ i) (ρ j) n) :=
    fun i hi => summable_sum (fun j hj => hsumm i hi j hj)
  have h0 : Summable (fun n : ℕ =>
      ∑ i ∈ u, ∑ j ∈ u, η i * star (η j) * gramFullFree (q := q) W X U' (ρ i) (ρ j) n) :=
    summable_sum hstep
  have h1 : Summable (fun n : ℕ =>
      (∑ i ∈ u, ∑ j ∈ u, η i * star (η j) * gramFullFree (q := q) W X U' (ρ i) (ρ j) n).re) :=
    Summable.of_norm_bounded h0.norm (fun n => by
      rw [Real.norm_eq_abs]
      exact Complex.abs_re_le_norm _)
  refine Summable.congr h1 (fun n => ?_)
  exact (gramWeight_mul_normSq_free u ρ hρ η W X U' n).symm

lemma gramWeight_mul_normSq {q : ℕ} [NeZero q] {ι : Type*} (s : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (ρ : ι → ℂ) (hρ : ∀ i ∈ s, 1/2 < (ρ i).re)
    (η : ι → ℂ) (W X U' : ℝ) (n : ℕ) :
    gramWeight W X U' n * ‖∑ i ∈ s, η i * (χ i (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖^2
      = (∑ i ∈ s, ∑ j ∈ s,
          η i * star (η j) * gramFull W X U' (χ i) (χ j) (ρ i) (ρ j) n).re := by
  have hfac : (∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * gramFull W X U' (χ i) (χ j) (ρ i) (ρ j) n)
      = (((thetaS W n : ℂ))^2 * ((gfun X U' n : ℝ) : ℂ))
          * (∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * gramInner (χ i) (χ j) (ρ i) (ρ j) n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [gramFull]
    ring
  have hexp : (∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * gramInner (χ i) (χ j) (ρ i) (ρ j) n).re
      = ‖∑ i ∈ s, η i * (χ i (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖^2 := by
    rw [halasz_expand s χ ρ hρ η n]
    refine congrArg Complex.re ?_
    refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => ?_))
    simp only [gramInner]
    ring
  rw [hfac, Complex.mul_re, gramWeight_re, gramWeight_im, hexp]
  ring

lemma summable_gramWeight_normSq {q : ℕ} [NeZero q] {ι : Type*} (s : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (ρ : ι → ℂ) (hρ : ∀ i ∈ s, 1/2 < (ρ i).re)
    (η : ι → ℂ) (W X U' : ℝ) (hW : 1 < W) (hX : 0 < X) (hU' : 0 < U') (hle : U' ≤ X) :
    Summable (fun n : ℕ => gramWeight W X U' n
      * ‖∑ i ∈ s, η i * (χ i (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖^2) := by
  classical
  have hsumm : ∀ i ∈ s, ∀ j ∈ s, Summable (fun n : ℕ =>
      η i * star (η j) * gramFull W X U' (χ i) (χ j) (ρ i) (ρ j) n) := by
    intro i hi j hj
    exact (summable_gramFull (q := q) W X U' hX hU' hle (χ i) (χ j)
      (by linarith [hρ i hi, hρ j hj])).mul_left _
  have hstep : ∀ i ∈ s, Summable (fun n : ℕ =>
      ∑ j ∈ s, η i * star (η j) * gramFull W X U' (χ i) (χ j) (ρ i) (ρ j) n) :=
    fun i hi => summable_sum (fun j hj => hsumm i hi j hj)
  have h0 : Summable (fun n : ℕ =>
      ∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * gramFull W X U' (χ i) (χ j) (ρ i) (ρ j) n) :=
    summable_sum hstep
  have h1 : Summable (fun n : ℕ =>
      (∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * gramFull W X U' (χ i) (χ j) (ρ i) (ρ j) n).re) :=
    Summable.of_norm_bounded h0.norm (fun n => by
      rw [Real.norm_eq_abs]
      exact Complex.abs_re_le_norm _)
  refine Summable.congr h1 (fun n => ?_)
  exact (gramWeight_mul_normSq s χ ρ hρ η W X U' n).symm

lemma gramWeight_nonneg {W X U' : ℝ} (hU' : 0 < U') (hle : U' ≤ X) (n : ℕ) :
    0 ≤ gramWeight W X U' n := by
  rw [gramWeight]
  exact mul_nonneg (sq_nonneg _) (gfun_nonneg hU' hle n)

/-- **The bilinear form over a single character-block.** -/
lemma bilinear_block {q : ℕ} [NeZero q] {ι : Type*} (u : Finset ι) [DecidableEq ι]
    (χ : ι → DirichletCharacter ℂ q) (ρ : ι → ℂ) (hρ : ∀ i ∈ u, 1/2 < (ρ i).re)
    (η : ι → ℂ)
    (χ₀ : DirichletCharacter ℂ q) (hχ : ∀ i ∈ u, χ i = χ₀)
    (W X U' : ℝ) (hW : 1 < W) (hX : 0 < X) (hU' : 0 < U') (hle : U' ≤ X)
    (κ CK : ℝ) (hκ0 : 0 ≤ κ) (hQ0 : 0 ≤ poleResidue W)
    (hsame : ∀ i ∈ u, ∀ j ∈ u,
      ‖gramEntryFree W X U' (ρ i) (ρ j) - ((poleResidue W : ℝ) : ℂ) * poleK X U' (ρ i) (ρ j)‖ ≤ κ)
    (hpole : (∑ i ∈ u, ∑ j ∈ u, η i * (starRingEnd ℂ) (η j) * poleK X U' (ρ i) (ρ j)).re
      ≤ CK * ∑ i ∈ u, ‖η i‖ ^ 2) :
    (∑ i ∈ u, ∑ j ∈ u, η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j)).re
      ≤ poleResidue W * CK * ∑ i ∈ u, ‖η i‖ ^ 2 + κ * u.card * ∑ i ∈ u, ‖η i‖ ^ 2 := by
  classical
  -- (1) the block form is the tsum of the damped moduli
  have h1 := gramForm_eq_tsum u χ ρ hρ η W X U' hW hX hU' hle
  -- (2) pointwise domination by the character-free modulus
  have h2 : ∀ n : ℕ, ‖∑ i ∈ u, η i * (χ i (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖
      ≤ ‖∑ i ∈ u, η i * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖ :=
    fun n => halasz_block_pointwise u χ ρ η χ₀ hχ n
  -- (3) summability of the free side
  have hsummFree : Summable (fun n : ℕ => gramWeight W X U' n
      * ‖∑ i ∈ u, η i * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖^2) :=
    summable_gramFullFree_normSq (q := q) u ρ hρ η W X U' hW hX hU' hle
  -- (4) the tsum comparison
  have h3 : (∑' n, gramWeight W X U' n
        * ‖∑ i ∈ u, η i * (χ i (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖^2)
      ≤ ∑' n, gramWeight W X U' n * ‖∑ i ∈ u, η i * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖^2 := by
    refine Summable.tsum_le_tsum (fun n => ?_) ?_ hsummFree
    · exact mul_le_mul_of_nonneg_left (by
        have := h2 n
        nlinarith [norm_nonneg (∑ i ∈ u, η i * (χ i (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))),
          norm_nonneg (∑ i ∈ u, η i * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))), this])
        (gramWeight_nonneg hU' hle n)
    · exact summable_gramWeight_normSq u χ ρ hρ η W X U' hW hX hU' hle
  -- (5) the free form as a tsum
  have h4 := gramFormFree_eq_tsum (q := q) u ρ hρ η W X U' hW hX hU' hle
  -- (6) the free form decomposition: pole term + remainder
  have h5 : (∑ i ∈ u, ∑ j ∈ u, η i * star (η j) * gramEntryFree W X U' (ρ i) (ρ j)).re
      = poleResidue W * (∑ i ∈ u, ∑ j ∈ u, η i * (starRingEnd ℂ) (η j) * poleK X U' (ρ i) (ρ j)).re
        + (∑ i ∈ u, ∑ j ∈ u, η i * star (η j) * (gramEntryFree W X U' (ρ i) (ρ j)
            - ((poleResidue W : ℝ) : ℂ) * poleK X U' (ρ i) (ρ j))).re := by
    have hsplit : (∑ i ∈ u, ∑ j ∈ u, η i * star (η j) * gramEntryFree W X U' (ρ i) (ρ j))
        = ((poleResidue W : ℝ) : ℂ)
            * (∑ i ∈ u, ∑ j ∈ u, η i * (starRingEnd ℂ) (η j) * poleK X U' (ρ i) (ρ j))
          + (∑ i ∈ u, ∑ j ∈ u, η i * star (η j) * (gramEntryFree W X U' (ρ i) (ρ j)
              - ((poleResidue W : ℝ) : ℂ) * poleK X U' (ρ i) (ρ j))) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      simp only [Complex.star_def]
      ring
    rw [hsplit, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  -- (7) the remainder bound
  have h6 : (∑ i ∈ u, ∑ j ∈ u, η i * star (η j) * (gramEntryFree W X U' (ρ i) (ρ j)
        - ((poleResidue W : ℝ) : ℂ) * poleK X U' (ρ i) (ρ j))).re
      ≤ κ * u.card * ∑ i ∈ u, ‖η i‖ ^ 2 := by
    have hb : ‖(∑ i ∈ u, ∑ j ∈ u, η i * star (η j) * (gramEntryFree W X U' (ρ i) (ρ j)
        - ((poleResidue W : ℝ) : ℂ) * poleK X U' (ρ i) (ρ j)))‖
        ≤ κ * (∑ i ∈ u, ‖η i‖) ^ 2 := by
      calc ‖(∑ i ∈ u, ∑ j ∈ u, η i * star (η j) * (gramEntryFree W X U' (ρ i) (ρ j)
            - ((poleResidue W : ℝ) : ℂ) * poleK X U' (ρ i) (ρ j)))‖
          ≤ ∑ i ∈ u, ‖∑ j ∈ u, η i * star (η j) * (gramEntryFree W X U' (ρ i) (ρ j)
              - ((poleResidue W : ℝ) : ℂ) * poleK X U' (ρ i) (ρ j))‖ :=
            norm_sum_le u (fun i => ∑ j ∈ u, η i * star (η j) * (gramEntryFree W X U' (ρ i) (ρ j)
              - ((poleResidue W : ℝ) : ℂ) * poleK X U' (ρ i) (ρ j)))
        _ ≤ ∑ i ∈ u, ∑ j ∈ u, ‖η i * star (η j) * (gramEntryFree W X U' (ρ i) (ρ j)
              - ((poleResidue W : ℝ) : ℂ) * poleK X U' (ρ i) (ρ j))‖ :=
            Finset.sum_le_sum (fun i hi => norm_sum_le u (fun j =>
              η i * star (η j) * (gramEntryFree W X U' (ρ i) (ρ j)
                - ((poleResidue W : ℝ) : ℂ) * poleK X U' (ρ i) (ρ j))))
        _ ≤ ∑ i ∈ u, ∑ j ∈ u, ‖η i‖ * ‖η j‖ * κ := by
            refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => ?_))
            rw [norm_mul, norm_mul, Complex.star_def, Complex.norm_conj]
            have h := hsame i hi j hj
            have h2' : (0:ℝ) ≤ ‖η i‖ * ‖η j‖ := by positivity
            calc ‖η i‖ * ‖η j‖ * ‖gramEntryFree W X U' (ρ i) (ρ j)
                  - ((poleResidue W : ℝ) : ℂ) * poleK X U' (ρ i) (ρ j)‖
                ≤ ‖η i‖ * ‖η j‖ * κ := mul_le_mul_of_nonneg_left h h2'
              _ = ‖η i‖ * ‖η j‖ * κ := rfl
        _ = κ * (∑ i ∈ u, ‖η i‖) ^ 2 := by
            rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun i hi => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun j hj => ?_)
            ring
    have habs : κ * (∑ i ∈ u, ‖η i‖) ^ 2 ≤ κ * u.card * ∑ i ∈ u, ‖η i‖ ^ 2 := by
      have hcs : (∑ i ∈ u, ‖η i‖) ^ 2 ≤ (∑ i ∈ u, ‖η i‖ ^ 2) * (u.card : ℝ) := by
        have h := Finset.sum_mul_sq_le_sq_mul_sq u (fun i => ‖η i‖) (fun _ => (1:ℝ))
        simpa using h
      calc κ * (∑ i ∈ u, ‖η i‖) ^ 2 ≤ κ * ((∑ i ∈ u, ‖η i‖ ^ 2) * (u.card : ℝ)) :=
            mul_le_mul_of_nonneg_left hcs hκ0
        _ = κ * u.card * ∑ i ∈ u, ‖η i‖ ^ 2 := by ring
    calc (∑ i ∈ u, ∑ j ∈ u, η i * star (η j) * (gramEntryFree W X U' (ρ i) (ρ j)
          - ((poleResidue W : ℝ) : ℂ) * poleK X U' (ρ i) (ρ j))).re
        ≤ ‖(∑ i ∈ u, ∑ j ∈ u, η i * star (η j) * (gramEntryFree W X U' (ρ i) (ρ j)
            - ((poleResidue W : ℝ) : ℂ) * poleK X U' (ρ i) (ρ j)))‖ := Complex.re_le_norm _
      _ ≤ κ * (∑ i ∈ u, ‖η i‖) ^ 2 := hb
      _ ≤ κ * u.card * ∑ i ∈ u, ‖η i‖ ^ 2 := habs
  -- (8) the pole term
  have h7 : poleResidue W * (∑ i ∈ u, ∑ j ∈ u, η i * (starRingEnd ℂ) (η j) * poleK X U' (ρ i) (ρ j)).re
      ≤ poleResidue W * CK * ∑ i ∈ u, ‖η i‖ ^ 2 := by
    calc poleResidue W * (∑ i ∈ u, ∑ j ∈ u,
            η i * (starRingEnd ℂ) (η j) * poleK X U' (ρ i) (ρ j)).re
        ≤ poleResidue W * (CK * ∑ i ∈ u, ‖η i‖ ^ 2) := mul_le_mul_of_nonneg_left hpole hQ0
      _ = poleResidue W * CK * ∑ i ∈ u, ‖η i‖ ^ 2 := by ring
  rw [h1]
  calc (∑' n, gramWeight W X U' n
        * ‖∑ i ∈ u, η i * (χ i (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖^2)
      ≤ ∑' n, gramWeight W X U' n * ‖∑ i ∈ u, η i * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖^2 := h3
    _ = (∑ i ∈ u, ∑ j ∈ u, η i * star (η j) * gramEntryFree W X U' (ρ i) (ρ j)).re := h4.symm
    _ = poleResidue W * (∑ i ∈ u, ∑ j ∈ u, η i * (starRingEnd ℂ) (η j) * poleK X U' (ρ i) (ρ j)).re
        + (∑ i ∈ u, ∑ j ∈ u, η i * star (η j) * (gramEntryFree W X U' (ρ i) (ρ j)
            - ((poleResidue W : ℝ) : ℂ) * poleK X U' (ρ i) (ρ j))).re := h5
    _ ≤ poleResidue W * CK * ∑ i ∈ u, ‖η i‖ ^ 2 + κ * u.card * ∑ i ∈ u, ‖η i‖ ^ 2 :=
        add_le_add h7 h6


set_option maxHeartbeats 4000000 in
/-- **The bilinear form bound of the Halász frame.** -/
lemma halasz_bilinear {q : ℕ} [NeZero q] {ι : Type*} (s : Finset ι) [DecidableEq ι]
    (χ : ι → DirichletCharacter ℂ q) (ρ : ι → ℂ) (hρ : ∀ i ∈ s, 1/2 < (ρ i).re)
    (η : ι → ℂ) (hη1 : ∑ i ∈ s, ‖η i‖ ^ 2 ≤ 1)
    (W X U' : ℝ) (hW : 1 < W) (hX : 0 < X) (hU' : 0 < U') (hle : U' ≤ X)
    (κ CK : ℝ) (hκ0 : 0 ≤ κ) (hCK0 : 0 ≤ CK) (hQ0 : 0 ≤ poleResidue W)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, χ i ≠ χ j →
      ‖gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j)‖ ≤ κ)
    (hsame : ∀ i ∈ s, ∀ j ∈ s, χ i = χ j →
      ‖gramEntryFree W X U' (ρ i) (ρ j) - ((poleResidue W : ℝ) : ℂ) * poleK X U' (ρ i) (ρ j)‖ ≤ κ)
    (hpole : ∀ u ∈ s.powerset, (∀ i ∈ u, ∀ j ∈ u, χ i = χ j) →
      (∑ i ∈ u, ∑ j ∈ u, η i * (starRingEnd ℂ) (η j) * poleK X U' (ρ i) (ρ j)).re
        ≤ CK * ∑ i ∈ u, ‖η i‖ ^ 2) :
    ∑' n, gramWeight W X U' n
        * ‖∑ i ∈ s, η i * (χ i (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖^2
      ≤ poleResidue W * CK + 2 * κ * s.card := by
  classical
  have hη0 : (0:ℝ) ≤ ∑ i ∈ s, ‖η i‖ ^ 2 := Finset.sum_nonneg (fun i _ => by positivity)
  rw [← gramForm_eq_tsum s χ ρ hρ η W X U' hW hX hU' hle]
  have hsplit : (∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j))
      = (∑ i ∈ s, ∑ j ∈ s.filter (fun j => χ j = χ i),
            η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j))
        + (∑ i ∈ s, ∑ j ∈ s.filter (fun j => ¬ (χ j = χ i)),
            η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j)) := by
    have hstep : ∀ i ∈ s, (∑ j ∈ s, η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j))
        = (∑ j ∈ s.filter (fun j => χ j = χ i),
              η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j))
          + (∑ j ∈ s.filter (fun j => ¬ (χ j = χ i)),
              η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j)) := by
      intro i hi
      exact (Finset.sum_filter_add_sum_filter_not (s := s) (p := fun j => χ j = χ i)
        (f := fun j => η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j))).symm
    calc (∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j))
        = ∑ i ∈ s, ((∑ j ∈ s.filter (fun j => χ j = χ i),
              η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j))
            + (∑ j ∈ s.filter (fun j => ¬ (χ j = χ i)),
              η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j))) :=
          Finset.sum_congr rfl hstep
      _ = _ := Finset.sum_add_distrib
  have hcrossb : ‖(∑ i ∈ s, ∑ j ∈ s.filter (fun j => ¬ (χ j = χ i)),
        η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j))‖
      ≤ κ * s.card * ∑ i ∈ s, ‖η i‖ ^ 2 := by
    have hterm : ∀ i ∈ s, ∀ j ∈ s.filter (fun j => ¬ (χ j = χ i)),
        ‖η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j)‖ ≤ ‖η i‖ * ‖η j‖ * κ := by
      intro i hi j hj
      have hne : χ i ≠ χ j := fun h => (Finset.mem_filter.mp hj).2 h.symm
      rw [norm_mul, norm_mul, Complex.star_def, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (hcross i hi j (Finset.mem_filter.mp hj).1 hne)
        (by positivity)
    calc ‖(∑ i ∈ s, ∑ j ∈ s.filter (fun j => ¬ (χ j = χ i)),
          η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j))‖
        ≤ ∑ i ∈ s, ‖∑ j ∈ s.filter (fun j => ¬ (χ j = χ i)),
            η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j)‖ :=
          norm_sum_le s _
      _ ≤ ∑ i ∈ s, ∑ j ∈ s.filter (fun j => ¬ (χ j = χ i)), ‖η i‖ * ‖η j‖ * κ :=
          Finset.sum_le_sum (fun i hi =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj => hterm i hi j hj)))
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖η i‖ * ‖η j‖ * κ := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j hj _ => ?_)
          positivity
      _ = κ * (∑ i ∈ s, ‖η i‖) ^ 2 := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j hj => ?_)
          ring
      _ ≤ κ * s.card * ∑ i ∈ s, ‖η i‖ ^ 2 := by
          have hcs : (∑ i ∈ s, ‖η i‖) ^ 2 ≤ (∑ i ∈ s, ‖η i‖ ^ 2) * (s.card : ℝ) := by
            have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖η i‖) (fun _ => (1:ℝ))
            simpa using h
          calc κ * (∑ i ∈ s, ‖η i‖) ^ 2 ≤ κ * ((∑ i ∈ s, ‖η i‖ ^ 2) * (s.card : ℝ)) :=
                mul_le_mul_of_nonneg_left hcs hκ0
            _ = κ * s.card * ∑ i ∈ s, ‖η i‖ ^ 2 := by ring
  have hfib : (∑ i ∈ s, ∑ j ∈ s.filter (fun j => χ j = χ i),
        η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j))
      = ∑ c ∈ s.image χ, ∑ i ∈ s.filter (fun i => χ i = c),
          ∑ j ∈ s.filter (fun j => χ j = c),
            η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image χ) (g := χ)
      (fun i hi => Finset.mem_image_of_mem χ hi)]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hχi : χ i = c := (Finset.mem_filter.mp hi).2
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    by_cases h : χ j = χ i
    · rw [if_pos h, if_pos (by rw [h, hχi])]
    · rw [if_neg h, if_neg (by rw [← hχi]; exact h)]
  have hsameb : (∑ i ∈ s, ∑ j ∈ s.filter (fun j => χ j = χ i),
        η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j)).re
      ≤ poleResidue W * CK * ∑ i ∈ s, ‖η i‖ ^ 2 + κ * s.card * ∑ i ∈ s, ‖η i‖ ^ 2 := by
    rw [hfib, Complex.re_sum]
    have hblock : ∀ c ∈ s.image χ,
        (∑ i ∈ s.filter (fun i => χ i = c), ∑ j ∈ s.filter (fun j => χ j = c),
            η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j)).re
          ≤ poleResidue W * CK * ∑ i ∈ s.filter (fun i => χ i = c), ‖η i‖ ^ 2
            + κ * (s.filter (fun i => χ i = c)).card
                * ∑ i ∈ s.filter (fun i => χ i = c), ‖η i‖ ^ 2 := by
      intro c hc
      have hsub : ∀ i ∈ s.filter (fun i => χ i = c), ∀ j ∈ s.filter (fun j => χ j = c), χ i = χ j := by
        intro i hi j hj
        rw [(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2]
      have hρi : ∀ i ∈ s.filter (fun i => χ i = c), 1/2 < (ρ i).re :=
        fun i hi => hρ i (Finset.mem_filter.mp hi).1
      have hsamei : ∀ i ∈ s.filter (fun i => χ i = c), ∀ j ∈ s.filter (fun j => χ j = c),
          ‖gramEntryFree W X U' (ρ i) (ρ j) - ((poleResidue W : ℝ) : ℂ) * poleK X U' (ρ i) (ρ j)‖ ≤ κ :=
        fun i hi j hj => hsame i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 (hsub i hi j hj)
      have hpolei : (∑ i ∈ s.filter (fun i => χ i = c), ∑ j ∈ s.filter (fun j => χ j = c),
            η i * (starRingEnd ℂ) (η j) * poleK X U' (ρ i) (ρ j)).re
          ≤ CK * ∑ i ∈ s.filter (fun i => χ i = c), ‖η i‖ ^ 2 :=
        hpole _ (Finset.mem_powerset.mpr (Finset.filter_subset _ _)) hsub
      exact bilinear_block (s.filter (fun i => χ i = c)) χ ρ hρi η c
        (fun i hi => (Finset.mem_filter.mp hi).2) W X U' hW hX hU' hle κ CK hκ0 hQ0 hsamei hpolei
    calc (∑ c ∈ s.image χ, (∑ i ∈ s.filter (fun i => χ i = c),
          ∑ j ∈ s.filter (fun j => χ j = c),
            η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j)).re)
        ≤ ∑ c ∈ s.image χ, (poleResidue W * CK * ∑ i ∈ s.filter (fun i => χ i = c), ‖η i‖ ^ 2
            + κ * (s.filter (fun i => χ i = c)).card
                * ∑ i ∈ s.filter (fun i => χ i = c), ‖η i‖ ^ 2) :=
          Finset.sum_le_sum hblock
      _ = poleResidue W * CK * (∑ c ∈ s.image χ, ∑ i ∈ s.filter (fun i => χ i = c), ‖η i‖ ^ 2)
            + (∑ c ∈ s.image χ, κ * (s.filter (fun i => χ i = c)).card
                * ∑ i ∈ s.filter (fun i => χ i = c), ‖η i‖ ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ poleResidue W * CK * ∑ i ∈ s, ‖η i‖ ^ 2 + κ * s.card * ∑ i ∈ s, ‖η i‖ ^ 2 := by
          have hsum_eq : (∑ c ∈ s.image χ, ∑ i ∈ s.filter (fun i => χ i = c), ‖η i‖ ^ 2)
              = ∑ i ∈ s, ‖η i‖ ^ 2 :=
            Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image χ) (g := χ)
              (fun i hi => Finset.mem_image_of_mem χ hi) (fun i => ‖η i‖ ^ 2)
          have hb1 : poleResidue W * CK * (∑ c ∈ s.image χ, ∑ i ∈ s.filter (fun i => χ i = c), ‖η i‖ ^ 2)
              = poleResidue W * CK * ∑ i ∈ s, ‖η i‖ ^ 2 := by rw [hsum_eq]
          have hb2 : (∑ c ∈ s.image χ, κ * (s.filter (fun i => χ i = c)).card
                * ∑ i ∈ s.filter (fun i => χ i = c), ‖η i‖ ^ 2)
              ≤ κ * s.card * ∑ i ∈ s, ‖η i‖ ^ 2 := by
            have h1 : (∑ c ∈ s.image χ, κ * (s.filter (fun i => χ i = c)).card
                  * ∑ i ∈ s.filter (fun i => χ i = c), ‖η i‖ ^ 2)
                ≤ ∑ c ∈ s.image χ, κ * s.card
                    * ∑ i ∈ s.filter (fun i => χ i = c), ‖η i‖ ^ 2 := by
              refine Finset.sum_le_sum (fun c hc => ?_)
              refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun i _ => by positivity))
              exact mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_filter_le s (fun i => χ i = c)) hκ0
            refine le_trans h1 ?_
            rw [← Finset.mul_sum, hsum_eq]
          rw [hb1]
          exact add_le_add le_rfl hb2
  have hsum : (∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j)).re
      ≤ poleResidue W * CK * ∑ i ∈ s, ‖η i‖ ^ 2 + 2 * κ * s.card * ∑ i ∈ s, ‖η i‖ ^ 2 := by
    rw [hsplit, Complex.add_re]
    have h2 : (∑ i ∈ s, ∑ j ∈ s.filter (fun j => ¬ (χ j = χ i)),
        η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j)).re
        ≤ κ * s.card * ∑ i ∈ s, ‖η i‖ ^ 2 := le_trans (Complex.re_le_norm _) hcrossb
    linarith
  calc (∑ i ∈ s, ∑ j ∈ s, η i * star (η j) * gramEntry q W X U' (χ i) (χ j) (ρ i) (ρ j)).re
      ≤ poleResidue W * CK * ∑ i ∈ s, ‖η i‖ ^ 2 + 2 * κ * s.card * ∑ i ∈ s, ‖η i‖ ^ 2 := hsum
    _ ≤ poleResidue W * CK + 2 * κ * s.card := by
        have h1 : poleResidue W * CK * ∑ i ∈ s, ‖η i‖ ^ 2 ≤ poleResidue W * CK * 1 :=
          mul_le_mul_of_nonneg_left hη1 (mul_nonneg hQ0 hCK0)
        have h2 : 2 * κ * s.card * ∑ i ∈ s, ‖η i‖ ^ 2 ≤ 2 * κ * s.card * 1 :=
          mul_le_mul_of_nonneg_left hη1
            (mul_nonneg (mul_nonneg (by norm_num) hκ0) (Nat.cast_nonneg _))
        linarith


/-- For every real `E` and `a > 0`, `(log D)^E ≤ D^a` for all large `D`. -/
lemma exists_log_rpow_le_rpow {E a : ℝ} (ha : 0 < a) :
    ∃ D₀ : ℝ, 1 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D → (Real.log D) ^ E ≤ D ^ a := by
  rcases le_or_gt E 0 with hE | hE
  · refine ⟨Real.exp 1, ?_, fun D hD => ?_⟩
    · rw [Real.one_le_exp_iff]; norm_num
    · have hD1 : 1 ≤ D := le_trans (by rw [Real.one_le_exp_iff]; norm_num) hD
      have hlog1 : 1 ≤ Real.log D := by
        rw [Real.le_log_iff_exp_le (by positivity)]
        exact hD
      calc (Real.log D) ^ E ≤ (Real.log D) ^ (0:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hlog1 hE
        _ = 1 := Real.rpow_zero _
        _ ≤ D ^ a := Real.one_le_rpow hD1 ha.le
  · set K₀ : ℝ := ((2 * E) / a) ^ E with hK₀
    have hK₀nn : 0 ≤ K₀ := Real.rpow_nonneg (div_nonneg (by linarith) ha.le) E
    refine ⟨max 1 (K₀ ^ (2 / a)), le_max_left _ _, fun D hD => ?_⟩
    have hD1 : 1 ≤ D := le_trans (le_max_left _ _) hD
    have hDpos : 0 < D := lt_of_lt_of_le one_pos hD1
    have hDK : K₀ ≤ D ^ (a / 2) := by
      have h1 : K₀ ^ (2 / a) ≤ D := le_trans (le_max_right _ _) hD
      calc K₀ = (K₀ ^ (2 / a)) ^ (a / 2) := by
            rw [← Real.rpow_mul hK₀nn, show (2 / a) * (a / 2) = 1 by field_simp, Real.rpow_one]
        _ ≤ D ^ (a / 2) := Real.rpow_le_rpow (Real.rpow_nonneg hK₀nn _) h1 (by positivity)
    set δ : ℝ := a / (2 * E) with hδ
    have hδpos : 0 < δ := div_pos ha (by linarith)
    have hlog : Real.log D ≤ D ^ δ / δ := Real.log_le_rpow_div hDpos.le hδpos
    have hlogE : (Real.log D) ^ E ≤ (D ^ δ / δ) ^ E :=
      Real.rpow_le_rpow (Real.log_nonneg hD1) hlog hE.le
    have hsplit : (D ^ δ / δ) ^ E = D ^ (a / 2) * K₀ := by
      rw [Real.div_rpow (x := D ^ δ) (y := δ) (Real.rpow_nonneg hDpos.le _) hδpos.le,
        ← Real.rpow_mul hDpos.le]
      rw [show δ * E = a / 2 by rw [hδ]; field_simp]
      rw [div_eq_mul_inv, ← Real.inv_rpow (x := δ) hδpos.le E]
      congr 1
      rw [hK₀, hδ]
      congr 1
      field_simp
    rw [hsplit] at hlogE
    calc (Real.log D) ^ E ≤ D ^ (a / 2) * K₀ := hlogE
      _ ≤ D ^ (a / 2) * D ^ (a / 2) :=
          mul_le_mul_of_nonneg_left hDK (Real.rpow_nonneg hDpos.le _)
      _ = D ^ a := by
          rw [← Real.rpow_add hDpos]
          congr 1
          ring


/-- The squared modulus of a sum of `halaszF`'s is `gramWeight` times the character-free modulus. -/
lemma norm_sum_halaszF (p : Params) (q : ℕ) [NeZero q] (T : ℝ) {ι : Type*} (s : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (ρ : ι → ℂ) (η : ι → ℂ) {n : ℕ}
    (hg : 0 ≤ gfun (Dpow q T p.x) (halaszU' p q T) n) :
    ‖∑ i ∈ s, η i * halaszF p q T (χ i) (ρ i) n‖^2
      = gramWeight (Dpow q T p.w) (Dpow q T p.x) (halaszU' p q T) n
        * ‖∑ i ∈ s, η i * (χ i (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))‖^2 := by
  have hfac : (∑ i ∈ s, η i * halaszF p q T (χ i) (ρ i) n)
      = (((thetaS (Dpow q T p.w) n : ℝ) : ℂ)
          * ((Real.sqrt (gfun (Dpow q T p.x) (halaszU' p q T) n) : ℝ) : ℂ))
        * (∑ i ∈ s, η i * (χ i (n : ZMod q)) * ((n : ℂ) ^ ((1/2 : ℂ) - ρ i))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    simp only [halaszF]
    ring
  have hsq : ‖(((thetaS (Dpow q T p.w) n : ℝ) : ℂ)
      * ((Real.sqrt (gfun (Dpow q T p.x) (halaszU' p q T) n) : ℝ) : ℂ))‖^2
      = gramWeight (Dpow q T p.w) (Dpow q T p.x) (halaszU' p q T) n := by
    rw [norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt hg, gramWeight]
  rw [hfac, norm_mul, mul_pow, hsq]


lemma norm_cpow_neg_half_sq (n : ℕ) : ‖((n : ℂ) ^ (-(1/2 : ℂ)))‖^2 = ((n : ℝ))⁻¹ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hz : (((0:ℕ)) : ℂ) = (0:ℂ) := by norm_num
    rw [hz, Complex.zero_cpow (x := -(1/2:ℂ)) (by norm_num)]
    norm_num
  · have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    rw [show ((n : ℂ)) = (((n:ℝ)) : ℂ) from by push_cast; ring]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    have hre : (-(1/2 : ℂ)).re = (-(1/2) : ℝ) := by norm_num
    rw [hre]
    have h2 : (n:ℝ) ^ (-(1/2) : ℝ) = (Real.sqrt (n:ℝ))⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity)]
    rw [h2, inv_pow, Real.sq_sqrt hnpos.le]

/-- The frame's summand `halaszA n * halaszF n` is the summand of the truncated Heath-Brown
detector. -/
lemma halasz_prod_eq (p : Params) (q : ℕ) [NeZero q] (T : ℝ) (χ : DirichletCharacter ℂ q)
    (ρ : ℂ) (n : ℕ) (hn : 1 ≤ n) (hg : 0 ≤ gfun (Dpow q T p.x) (halaszU' p q T) n) :
    halaszA p q T n * halaszF p q T χ ρ n
      = ((psiSum (Dpow q T p.u) (Dpow q T p.v) n : ℝ) : ℂ)
        * ((thetaS (Dpow q T p.w) n : ℝ) : ℂ) * χ (n : ZMod q)
        * ((n : ℂ) ^ (-ρ))
        * (((gfun (Dpow q T p.x) (halaszU' p q T) n : ℝ) : ℂ)) := by
  have hnne : n ≠ 0 := by omega
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hnne
  rw [halaszA, halaszF]
  set A : ℂ := ((psiSum (Dpow q T p.u) (Dpow q T p.v) n : ℝ) : ℂ) with hA
  set B : ℂ := ((n : ℂ) ^ (-(1 / 2 : ℂ))) with hB
  set Cc : ℂ := ((Real.sqrt (gfun (Dpow q T p.x) (halaszU' p q T) n) : ℝ) : ℂ) with hC
  set D : ℂ := ((thetaS (Dpow q T p.w) n : ℝ) : ℂ) with hD
  set E : ℂ := χ (n : ZMod q) with hE
  set F : ℂ := ((n : ℂ) ^ ((1 / 2 : ℂ) - ρ)) with hF
  have hsqrt : Cc * Cc = ((gfun (Dpow q T p.x) (halaszU' p q T) n : ℝ) : ℂ) := by
    rw [hC, ← Complex.ofReal_mul, Real.mul_self_sqrt hg]
  have hcpow : B * F = (n : ℂ) ^ (-ρ) := by
    rw [hB, hF, ← Complex.cpow_add _ _ hn0]
    congr 1
    ring
  have h1 : (A * B * Cc) * (D * E * F * Cc) = (A * D * E) * (B * F) * (Cc * Cc) := by ring
  rw [h1, hsqrt, hcpow]


end Work.ZeroDensity.LogFree.HalaszGram
