import Mathlib
import Submission.Work.Coherence.Inner

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

namespace Work.FeitSibley.Coherence

open Work.Coherence

/-- The character inner product is positive semidefinite: `(cfInner f f).re` is
`(1/|G|) ∑_x ‖f x‖²`. -/
theorem cfInner_self_re_nonneg {G : Type*} [Fintype G] (f : G → ℂ) :
    0 ≤ (cfInner f f).re := by
  have hterm : ∀ x, f x * starRingEnd ℂ (f x) = ((Complex.normSq (f x) : ℝ) : ℂ) :=
    fun x => Complex.mul_conj (f x)
  have hsum : (∑ x, f x * starRingEnd ℂ (f x)) = ((∑ x, Complex.normSq (f x) : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl (fun x _ => hterm x)
  rw [cfInner_apply, hsum, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun x _ => Complex.normSq_nonneg _)

/-- **Bessel's inequality** for an orthonormal finite family in the character inner product on a
finite group: the squared lengths of the Fourier coefficients of `T` along `S` sum to at most
`‖T‖² = (cfInner T T).re`. -/
theorem cfInner_bessel {G ι : Type*} [Fintype G] [DecidableEq ι]
    (S : Finset ι) (e : ι → G → ℂ) (T : G → ℂ)
    (horth : ∀ x ∈ S, ∀ y ∈ S, Work.Coherence.cfInner (e x) (e y) = if x = y then 1 else 0) :
    ∑ y ∈ S, Complex.normSq (Work.Coherence.cfInner T (e y)) ≤
      (Work.Coherence.cfInner T T).re := by
  classical
  -- the coefficients of `T` along `S`, and the corresponding "Fourier projection" `P` of `T`
  let c : ι → ℂ := fun y => cfInner T (e y)
  set P : G → ℂ := ∑ y ∈ S, c y • e y with hP
  -- `P` has the same coefficients along `S` as `T`
  have hTP : cfInner T P = ∑ y ∈ S, ((Complex.normSq (c y) : ℝ) : ℂ) := by
    rw [hP, cfInner_sum_right]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [cfInner_smul_right, mul_comm]
    exact Complex.mul_conj (c y)
  have hPT : cfInner P T = ∑ y ∈ S, ((Complex.normSq (c y) : ℝ) : ℂ) := by
    rw [cfInner_conj_symm, hTP, map_sum]
    exact Finset.sum_congr rfl fun y _ => Complex.conj_ofReal _
  have hPP : cfInner P P = ∑ y ∈ S, ((Complex.normSq (c y) : ℝ) : ℂ) := by
    rw [hP, cfInner_sum_smul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.sum_eq_single x]
    · rw [horth x hx x hx, ite_eq_left rfl, mul_one]
      exact Complex.mul_conj (c x)
    · intro b hb hbx
      rw [horth x hx b hb, ite_eq_right (fun h : x = b => hbx h.symm), mul_zero]
    · intro hx'
      exact absurd hx hx'
  have hsum : (∑ y ∈ S, ((Complex.normSq (c y) : ℝ) : ℂ)).re = ∑ y ∈ S, Complex.normSq (c y) := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun y _ => Complex.ofReal_re _
  -- expand `‖T - P‖²`
  have hre : (cfInner (T - P) (T - P)).re = (cfInner T T).re - ∑ y ∈ S, Complex.normSq (c y) := by
    have hexp : cfInner (T - P) (T - P) =
        (cfInner T T - cfInner T P) - (cfInner P T - cfInner P P) := by
      rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right]
    rw [hexp, Complex.sub_re, Complex.sub_re, Complex.sub_re, hTP, hPT, hPP, hsum]
    ring
  have hnn : 0 ≤ (cfInner (T - P) (T - P)).re := cfInner_self_re_nonneg _
  rw [hre] at hnn
  exact sub_nonneg.mp hnn

end Work.FeitSibley.Coherence
