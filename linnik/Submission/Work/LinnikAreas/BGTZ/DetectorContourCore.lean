/-
# Contour shift of the BGTZ detector: the algebraic and analytic core

This module collects the lemmas (proved here, not delegated) that the contour shift of
`Work.LinnikAreas.BGTZ.DetectorContour` needs:

* `detNum`, `detA_eq_mul` — the numerator `detA` of the integrand, with the pole at `s = 1-ρ`
  divided out (`LFunctionTrivChar₁ q` replacing `(s-(1-ρ))·L(ρ+s,χ₀)`);
* `detA_zero`, `detA_eq_mul_dslope` — vanishing at `s = 0` (from `L(ρ,χ) = 0` or `L(ρ,χχ₁) = 0`);
* `detInt_eq_detM`, `detInt_decomp` — `detInt s = detRes/(s-(1-ρ)) + detH s` off `{0, -1, 1-ρ}`;
* `differentiable_detA`, `differentiableOn_detM`, `differentiableOn_detH` — holomorphy of the
  pieces (the last one on every closed rectangle with `Re s > -1`);
* `detRes_eq` and `norm_detRes_le` — the value of the residue and its bound by `detResBound`.
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.BGTZ.DetectorDefs
import Submission.Work.LinnikAreas.BGTZ.DetContourDefs
import Submission.Work.LinnikAreas.BGTZ.DetTrivCharValue
import Submission.Work.ZeroDensity.Huxley.cardDivisorsLe
import Submission.Commons.Analysis.Complex.rectIntegral_sub_inv_inside
import Submission.Work.LinnikAreas.BGTZ.rectVertIdentity

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.BGTZ

variable {q : ℕ} [NeZero q]

/-! ## Elementary pieces -/

/-- `LFunctionTrivChar₁ q` is `(s-1)·L(s,χ₀)` away from `s = 1`. -/
lemma LFunctionTrivChar₁_of_ne {s : ℂ} (hs : s ≠ 1) :
    DirichletCharacter.LFunctionTrivChar₁ q s
      = (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s := by
  simp only [DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunctionTrivChar₁,
    Function.update_of_ne hs]

/-- The numerator of `detInt`, i.e. `detInt s · s(s+1)`. -/
def detNum (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ)
    (s : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ (ρ + s) * DirichletCharacter.LFunction (χ * χ₁) (ρ + s)
    * sieveG χ₁ R θw (ρ + s) χ * (N : ℂ) ^ s

/-- `detA s = (s-(1-ρ))·(numerator of detInt)` away from the pole `s = 1-ρ`. -/
lemma detA_eq_mul (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ)
    {s : ℂ} (hs : s ≠ 1 - ρ) :
    detA χ₁ χ R θw N ρ s = (s - (1 - ρ)) * detNum χ₁ χ R θw N ρ s := by
  unfold detA detNum
  by_cases hB : χ = 1 ∨ χ * χ₁ = 1
  · rw [if_pos hB]
    have hρs : ρ + s ≠ 1 := by
      intro hcon
      exact hs (by linear_combination hcon)
    rw [LFunctionTrivChar₁_of_ne (q := q) hρs]
    rcases hB with h | h
    · have hother : detOther χ₁ χ = χ * χ₁ := by simp only [detOther, if_pos h]
      rw [hother, h, one_mul]
      ring
    · have hother : detOther χ₁ χ = χ := by
        by_cases h1 : χ = 1
        · subst h1
          simp only [detOther, if_pos rfl]
          exact h
        · simp only [detOther, if_neg h1]
      rw [hother, h]
      ring
  · rw [if_neg hB]
    ring

/-- If `ρ` is a zero of `L(·,χ)` or of `L(·,χχ₁)` then the numerator vanishes at `s = 0`. -/
lemma detNum_zero (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ)
    (hzero : DirichletCharacter.LFunction χ ρ = 0
      ∨ DirichletCharacter.LFunction (χ * χ₁) ρ = 0) :
    detNum χ₁ χ R θw N ρ 0 = 0 := by
  unfold detNum
  rcases hzero with h | h
  · rw [show ρ + 0 = ρ by ring, h]
    ring
  · rw [show ρ + 0 = ρ by ring, h]
    ring

/-- The numerator `detA` vanishes at `s = 0`. -/
lemma detA_zero (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ)
    (hzero : DirichletCharacter.LFunction χ ρ = 0
      ∨ DirichletCharacter.LFunction (χ * χ₁) ρ = 0)
    (hρ1 : ρ ≠ 1) : detA χ₁ χ R θw N ρ 0 = 0 := by
  have h0u : (0 : ℂ) ≠ 1 - ρ := by
    intro hcon
    exact hρ1 (sub_eq_zero.mp hcon.symm).symm
  rw [detA_eq_mul χ₁ χ R θw N ρ h0u, detNum_zero χ₁ χ R θw N ρ hzero]
  ring

/-- `detA s = s·(dslope (detA) 0 s)`. -/
lemma detA_eq_mul_dslope (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ)
    (ρ : ℂ) (hzero : DirichletCharacter.LFunction χ ρ = 0
      ∨ DirichletCharacter.LFunction (χ * χ₁) ρ = 0) (hρ1 : ρ ≠ 1) (s : ℂ) :
    detA χ₁ χ R θw N ρ s = s * dslope (detA χ₁ χ R θw N ρ) 0 s := by
  have h := sub_smul_dslope (detA χ₁ χ R θw N ρ) 0 s
  simp only [sub_zero, smul_eq_mul] at h
  rw [h, detA_zero χ₁ χ R θw N ρ hzero hρ1]
  ring

/-- **The integrand as an analytic function divided by the pole**: for `s ∉ {0, -1, 1-ρ}`,
`detInt s = detM s/(s-(1-ρ))`. -/
lemma detInt_eq_detM (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ)
    (hzero : DirichletCharacter.LFunction χ ρ = 0
      ∨ DirichletCharacter.LFunction (χ * χ₁) ρ = 0)
    (hρ1 : ρ ≠ 1) {s : ℂ} (hs0 : s ≠ 0) (hsm : s ≠ -1) (hsu : s ≠ 1 - ρ) :
    detInt χ₁ χ R θw N ρ s = detM χ₁ χ R θw N ρ s / (s - (1 - ρ)) := by
  have hA : detA χ₁ χ R θw N ρ s = (s - (1 - ρ)) * detNum χ₁ χ R θw N ρ s :=
    detA_eq_mul χ₁ χ R θw N ρ hsu
  have hds : s * dslope (detA χ₁ χ R θw N ρ) 0 s = detA χ₁ χ R θw N ρ s :=
    (detA_eq_mul_dslope χ₁ χ R θw N ρ hzero hρ1 s).symm
  have hsu' : s - (1 - ρ) ≠ 0 := sub_ne_zero.mpr hsu
  have h1 : dslope (detA χ₁ χ R θw N ρ) 0 s * s
      = (s - (1 - ρ)) * detNum χ₁ χ R θw N ρ s := by
    rw [mul_comm, hds, hA]
  have h2 : detNum χ₁ χ R θw N ρ s
      = dslope (detA χ₁ χ R θw N ρ) 0 s * s / (s - (1 - ρ)) := by
    rw [eq_div_iff hsu', mul_comm (detNum χ₁ χ R θw N ρ s) (s - (1 - ρ))]
    exact h1.symm
  have hs1 : s + 1 ≠ 0 := by
    intro h
    exact hsm (by linear_combination h)
  rw [show detInt χ₁ χ R θw N ρ s = detNum χ₁ χ R θw N ρ s / (s * (s + 1)) from rfl, h2, detM]
  field_simp

/-- **The decomposition of the integrand**: away from `s ∈ {0, -1, 1-ρ}`,
`detInt s = detRes/(s - (1-ρ)) + detH s`. -/
lemma detInt_decomp (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ)
    (hzero : DirichletCharacter.LFunction χ ρ = 0
      ∨ DirichletCharacter.LFunction (χ * χ₁) ρ = 0)
    (hρ1 : ρ ≠ 1) {s : ℂ} (hs0 : s ≠ 0) (hsm : s ≠ -1) (hsu : s ≠ 1 - ρ) :
    detInt χ₁ χ R θw N ρ s
      = detRes χ₁ χ R θw N ρ / (s - (1 - ρ)) + detH χ₁ χ R θw N ρ s := by
  have hsu' : s - (1 - ρ) ≠ 0 := sub_ne_zero.mpr hsu
  have hdetH : detH χ₁ χ R θw N ρ s
      = (detM χ₁ χ R θw N ρ s - detRes χ₁ χ R θw N ρ) / (s - (1 - ρ)) := by
    rw [eq_div_iff hsu', detH, detRes]
    have h := sub_smul_dslope (detM χ₁ χ R θw N ρ) (1 - ρ) s
    simpa only [smul_eq_mul, mul_comm] using h
  rw [detInt_eq_detM χ₁ χ R θw N ρ hzero hρ1 hs0 hsm hsu, hdetH, ← add_div]
  ring

/-! ## Differentiability of the pieces -/

/-- Products of finitely many differentiable functions are differentiable. -/
lemma differentiable_finset_prod {ι : Type*} (u : Finset ι) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ u, Differentiable ℂ (f i)) :
    Differentiable ℂ (fun s : ℂ => ∏ i ∈ u, f i s) := by
  classical
  induction u using Finset.induction with
  | empty => simpa using differentiable_const (1 : ℂ)
  | insert a u ha ih =>
      have h1 : Differentiable ℂ (f a) := hf a (Finset.mem_insert_self a u)
      have h2 : Differentiable ℂ (fun s : ℂ => ∏ i ∈ u, f i s) :=
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have heq : (fun s : ℂ => ∏ i ∈ insert a u, f i s)
          = fun s : ℂ => f a s * ∏ i ∈ u, f i s := by
        funext s
        rw [Finset.prod_insert ha]
      rw [heq]
      exact h1.mul h2

lemma differentiable_sieveLocal' (χ₁ χ : DirichletCharacter ℂ q) (ρ : ℂ) {p : ℕ} (hp : p ≠ 0) :
    Differentiable ℂ (fun s : ℂ => sieveLocal χ₁ χ (ρ + s) p) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hpow : Differentiable ℂ (fun s : ℂ => (p : ℂ) ^ (-(ρ + s))) :=
    (differentiable_id.const_add ρ).neg.const_cpow (Or.inl hp0)
  have hpow2 : Differentiable ℂ (fun s : ℂ => (p : ℂ) ^ (-(2 * (ρ + s)))) :=
    ((differentiable_id.const_add ρ).const_mul 2).neg.const_cpow (Or.inl hp0)
  have hc1 : Differentiable ℂ (fun _ : ℂ => (1 + ((χ₁ (p : ZMod q)).re : ℂ)) * χ (p : ZMod q)) :=
    differentiable_const _
  have hc2 : Differentiable ℂ (fun _ : ℂ => ((χ₁ (p : ZMod q)).re : ℂ) * χ (p : ZMod q) ^ 2) :=
    differentiable_const _
  have heq : (fun s : ℂ => sieveLocal χ₁ χ (ρ + s) p)
      = fun s : ℂ => (1 + ((χ₁ (p : ZMod q)).re : ℂ)) * χ (p : ZMod q) * (p : ℂ) ^ (-(ρ + s))
          - ((χ₁ (p : ZMod q)).re : ℂ) * χ (p : ZMod q) ^ 2 * (p : ℂ) ^ (-(2 * (ρ + s))) := rfl
  rw [heq]
  exact (hc1.mul hpow).sub (hc2.mul hpow2)

lemma differentiable_detSieveG (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (ρ : ℂ) :
    Differentiable ℂ (fun s : ℂ => sieveG χ₁ R θw (ρ + s) χ) := by
  have hprod : ∀ d e : ℕ, Differentiable ℂ
      (fun s : ℂ => ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ (ρ + s) p) :=
    fun d e => differentiable_finset_prod (f := fun p s => sieveLocal χ₁ χ (ρ + s) p)
      ((Nat.lcm d e).primeFactors)
      (fun p hp => differentiable_sieveLocal' χ₁ χ ρ
        (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have hterm : ∀ d e : ℕ, Differentiable ℂ (fun s : ℂ =>
      (θw d : ℂ) * (θw e : ℂ)
        * ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ (ρ + s) p) := by
    intro d e
    have hc : Differentiable ℂ (fun _ : ℂ => (θw d : ℂ) * (θw e : ℂ)) := differentiable_const _
    exact hc.mul (hprod d e)
  have heq : (fun s : ℂ => sieveG χ₁ R θw (ρ + s) χ)
      = fun s : ℂ => ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
          (θw d : ℂ) * (θw e : ℂ)
            * ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ (ρ + s) p := rfl
  rw [heq]
  rw [show (fun s : ℂ => ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        (θw d : ℂ) * (θw e : ℂ)
          * ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ (ρ + s) p)
      = (∑ d ∈ Finset.Icc 1 R, fun s : ℂ => ∑ e ∈ Finset.Icc 1 R,
          (θw d : ℂ) * (θw e : ℂ)
            * ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ (ρ + s) p) from by
    funext s
    rw [Finset.sum_apply]]
  refine Differentiable.sum (𝕜 := ℂ) ?_
  intro d hd
  rw [show (fun s : ℂ => ∑ e ∈ Finset.Icc 1 R, (θw d : ℂ) * (θw e : ℂ)
        * ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ (ρ + s) p)
      = (∑ e ∈ Finset.Icc 1 R, fun s : ℂ => (θw d : ℂ) * (θw e : ℂ)
        * ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ (ρ + s) p) from by
    funext s
    rw [Finset.sum_apply]]
  refine Differentiable.sum (𝕜 := ℂ) ?_
  intro e he
  exact hterm d e

/-- `detA` is entire (in `s`). -/
lemma differentiable_detA (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ)
    (hχ₁ : χ₁ ^ 2 = 1) (hχ₁ne : χ₁ ≠ 1) (hN : (N : ℂ) ≠ 0) :
    Differentiable ℂ (detA χ₁ χ R θw N ρ) := by
  have hG := differentiable_detSieveG χ₁ χ R θw ρ
  have hN' : Differentiable ℂ (fun s : ℂ => (N : ℂ) ^ s) :=
    differentiable_id.const_cpow (Or.inl hN)
  by_cases hB : χ = 1 ∨ χ * χ₁ = 1
  · have hdet : Differentiable ℂ
        (fun s : ℂ => DirichletCharacter.LFunctionTrivChar₁ q (ρ + s)) :=
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).comp
        (differentiable_id.const_add ρ)
    have hχ' : detOther χ₁ χ ≠ 1 := by
      unfold detOther
      by_cases h1 : χ = 1
      · rw [if_pos h1, h1, one_mul]
        exact hχ₁ne
      · rw [if_neg h1]
        exact h1
    have hL : Differentiable ℂ
        (fun s : ℂ => DirichletCharacter.LFunction (detOther χ₁ χ) (ρ + s)) :=
      (DirichletCharacter.differentiable_LFunction hχ').comp (differentiable_id.const_add ρ)
    have hfun : detA χ₁ χ R θw N ρ = fun s : ℂ =>
        (DirichletCharacter.LFunctionTrivChar₁ q (ρ + s)
          * DirichletCharacter.LFunction (detOther χ₁ χ) (ρ + s))
          * sieveG χ₁ R θw (ρ + s) χ * (N : ℂ) ^ s := by
      funext s
      unfold detA
      rw [if_pos hB]
    rw [hfun]
    exact ((hdet.mul hL).mul hG).mul hN'
  · have hχ : χ ≠ 1 := fun h => hB (Or.inl h)
    have hχχ : χ * χ₁ ≠ 1 := fun h => hB (Or.inr h)
    have hL1 : Differentiable ℂ (fun s : ℂ => DirichletCharacter.LFunction χ (ρ + s)) :=
      (DirichletCharacter.differentiable_LFunction hχ).comp (differentiable_id.const_add ρ)
    have hL2 : Differentiable ℂ
        (fun s : ℂ => DirichletCharacter.LFunction (χ * χ₁) (ρ + s)) :=
      (DirichletCharacter.differentiable_LFunction hχχ).comp (differentiable_id.const_add ρ)
    have hfun : detA χ₁ χ R θw N ρ = fun s : ℂ =>
        ((s - (1 - ρ)) * DirichletCharacter.LFunction χ (ρ + s)
          * DirichletCharacter.LFunction (χ * χ₁) (ρ + s))
          * sieveG χ₁ R θw (ρ + s) χ * (N : ℂ) ^ s := by
      funext s
      unfold detA
      rw [if_neg hB]
    rw [hfun]
    exact (((differentiable_id.sub_const (1 - ρ)).mul hL1).mul hL2).mul hG |>.mul hN'

/-- If `f` is complex differentiable on an open set `V` containing `c`, then the difference
quotient `dslope f c` (which equals `deriv f c` at `c`) is complex differentiable on any subset
of `V`. -/
lemma differentiableOn_dslope_of_isOpen_mem {f : ℂ → ℂ} {V s : Set ℂ} {c : ℂ}
    (hV : IsOpen V) (hsub : s ⊆ V) (hc : c ∈ V) (hf : DifferentiableOn ℂ f V) :
    DifferentiableOn ℂ (dslope f c) s := by
  have hds : DifferentiableOn ℂ (dslope f c) V :=
    (Complex.differentiableOn_dslope (f := f) (c := c) (s := V) (hV.mem_nhds hc)).mpr hf
  intro p hp
  by_cases hpc : p = c
  · rw [hpc]
    exact (hds.differentiableAt (hV.mem_nhds hc)).differentiableWithinAt
  · exact (differentiableWithinAt_dslope_of_ne (f := f) (a := c) (s := s) hpc).mpr
      ((hf.mono hsub) p hp)

/-- `detM` is differentiable on the half-plane `Re s > -1`. -/
lemma differentiableOn_detM (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ)
    (ρ : ℂ) (hχ₁ : χ₁ ^ 2 = 1) (hχ₁ne : χ₁ ≠ 1) (hN : (N : ℂ) ≠ 0) :
    DifferentiableOn ℂ (detM χ₁ χ R θw N ρ) {s : ℂ | -1 < s.re} := by
  have hVopen : IsOpen {s : ℂ | -1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : (0 : ℂ) ∈ {s : ℂ | -1 < s.re} := by
    show (-1 : ℝ) < (0 : ℂ).re
    simp
  have hds : DifferentiableOn ℂ (dslope (detA χ₁ χ R θw N ρ) 0) {s : ℂ | -1 < s.re} :=
    differentiableOn_dslope_of_isOpen_mem hVopen (Set.Subset.refl _) hmem
      (differentiable_detA χ₁ χ R θw N ρ hχ₁ hχ₁ne hN).differentiableOn
  have hid : DifferentiableOn ℂ (fun s : ℂ => s + 1) {s : ℂ | -1 < s.re} :=
    (differentiableOn_id.add_const 1)
  have hne : ∀ s ∈ {s : ℂ | -1 < s.re}, s + 1 ≠ 0 := by
    intro s hs h
    have hs' : (-1 : ℝ) < s.re := hs
    have h2 : s.re + 1 = 0 := by
      have := congrArg Complex.re h
      simpa using this
    linarith
  exact hds.div hid hne

/-- `detH` is differentiable on every closed rectangle contained in the half-plane `Re s > -1`. -/
lemma differentiableOn_detH (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ)
    (ρ : ℂ) (hχ₁ : χ₁ ^ 2 = 1) (hχ₁ne : χ₁ ≠ 1) (hN : (N : ℂ) ≠ 0) (hρ : ρ.re < 2)
    {p q R' : ℝ} (hp : -1 < p) (hq : -1 < q) :
    DifferentiableOn ℂ (detH χ₁ χ R θw N ρ) (Set.uIcc p q ×ℂ Set.uIcc (-R') R') := by
  have hVopen : IsOpen {s : ℂ | -1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsub : (Set.uIcc p q ×ℂ Set.uIcc (-R') R') ⊆ {s : ℂ | -1 < s.re} := by
    intro w hw
    obtain ⟨hre, -⟩ := Complex.mem_reProdIm.mp hw
    exact (Set.ordConnected_Ioi (a := (-1 : ℝ))).uIcc_subset hp hq hre
  have hcV : (1 - ρ) ∈ {s : ℂ | -1 < s.re} := by
    show (-1 : ℝ) < (1 - ρ).re
    rw [Complex.sub_re, Complex.one_re]
    linarith
  exact differentiableOn_dslope_of_isOpen_mem hVopen hsub hcV
    (differentiableOn_detM χ₁ χ R θw N ρ hχ₁ hχ₁ne hN)


/-! ## The zero `ρ` lies in the critical strip, and is not `1` -/

/-- If `ρ` is a zero of `L(·,χ)` or of `L(·,χχ₁)` with `Re ρ > 1/2`, then `Re ρ < 1`
(and in particular `ρ ≠ 1`).  Uses the non-vanishing of Dirichlet `L`-functions on `Re ≥ 1`
(Mathlib's `DirichletCharacter.LFunction_ne_zero_of_one_le_re`), the non-vanishing at `s = 1` for
nontrivial characters, and the value `L(1,χ₀) ≠ 0` of the trivial character
(`DetTrivCharValue`). -/
lemma det_rho_re_lt_one {q : ℕ} [NeZero q] (hq : 400000 < q) (χ₁ χ : DirichletCharacter ℂ q)
    (hχ₁ne : χ₁ ≠ 1) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0
      ∨ DirichletCharacter.LFunction (χ * χ₁) ρ = 0) (hre : 1 / 2 < ρ.re) :
    ρ.re < 1 := by
  have hq2 : 2 ≤ q := by omega
  by_contra hcon
  push_neg at hcon
  have h1 : 1 ≤ ρ.re := hcon
  by_cases hρ1 : ρ = 1
  · subst hρ1
    rcases hzero with h | h
    · by_cases hχ : χ = 1
      · rw [hχ] at h
        exact absurd h (DetTrivCharValue q hq2)
      · exact absurd h (DirichletCharacter.LFunction_apply_one_ne_zero hχ)
    · by_cases hχχ : χ * χ₁ = 1
      · rw [hχχ] at h
        exact absurd h (DetTrivCharValue q hq2)
      · exact absurd h (DirichletCharacter.LFunction_apply_one_ne_zero hχχ)
  · rcases hzero with h | h
    · by_cases hχ : χ = 1
      · exact absurd h (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hρ1) h1)
      · exact absurd h (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h1)
    · by_cases hχχ : χ * χ₁ = 1
      · exact absurd h (DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ * χ₁) (Or.inr hρ1) h1)
      · exact absurd h (DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ * χ₁) (Or.inl hχχ) h1)


/-! ## Continuity / integrability of the integrand on vertical lines, and the horizontal edges -/

/-- The patched integrand equals the integrand minus the residue kernel, off `{0, -1, 1-ρ}`. -/
lemma detH_eq (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ)
    (hzero : DirichletCharacter.LFunction χ ρ = 0
      ∨ DirichletCharacter.LFunction (χ * χ₁) ρ = 0)
    (hρ1 : ρ ≠ 1) {s : ℂ} (hs0 : s ≠ 0) (hsm : s ≠ -1) (hsu : s ≠ 1 - ρ) :
    detH χ₁ χ R θw N ρ s
      = detInt χ₁ χ R θw N ρ s - detRes χ₁ χ R θw N ρ / (s - (1 - ρ)) := by
  have h := detInt_decomp χ₁ χ R θw N ρ hzero hρ1 hs0 hsm hsu
  rw [h]
  ring

/-- The `L`-function of any character mod `q` is continuous along a vertical line that avoids
`s = 1`. -/
lemma continuous_LFunction_line (χ : DirichletCharacter ℂ q) {ρ : ℂ} {c : ℝ}
    (hc : c + ρ.re ≠ 1) :
    Continuous (fun t : ℝ => DirichletCharacter.LFunction χ (ρ + (c + (t : ℂ) * Complex.I))) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hre : (ρ + (c + (t : ℂ) * Complex.I)).re = ρ.re + c := by simp
  have hs : ρ + (c + (t : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hre] at this
    simp only [Complex.one_re] at this
    exact hc (by linarith)
  have hd : DifferentiableAt ℂ (DirichletCharacter.LFunction χ)
      (ρ + (c + (t : ℂ) * Complex.I)) :=
    DirichletCharacter.differentiableAt_LFunction χ _ (Or.inl hs)
  have hcont : ContinuousAt (fun t : ℝ => ρ + (c + (t : ℂ) * Complex.I)) t := by fun_prop
  exact ContinuousAt.comp (g := DirichletCharacter.LFunction χ) hd.continuousAt hcont

/-- The integrand `detInt` is continuous along a vertical line `Re s = c` with `c ≠ 0`, `c ≠ -1`
and `c + Re ρ ≠ 1`. -/
lemma continuous_detInt_line (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ)
    (ρ : ℂ) (hN : (N : ℂ) ≠ 0) {c : ℝ} (hc0 : c ≠ 0) (hcm : c ≠ -1) (hc : c + ρ.re ≠ 1) :
    Continuous (fun t : ℝ => detInt χ₁ χ R θw N ρ ((c : ℂ) + (t : ℂ) * Complex.I)) := by
  have hline : Continuous (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
  have hL1 := continuous_LFunction_line (q := q) χ (ρ := ρ) (c := c) hc
  have hL2 := continuous_LFunction_line (q := q) (χ * χ₁) (ρ := ρ) (c := c) hc
  have hG : Continuous (fun t : ℝ => sieveG χ₁ R θw (ρ + (c + (t : ℂ) * Complex.I)) χ) :=
    (differentiable_detSieveG χ₁ χ R θw ρ).continuous.comp hline
  have hNc : Continuous (fun t : ℝ => (N : ℂ) ^ (c + (t : ℂ) * Complex.I)) :=
    hline.const_cpow (Or.inl hN)
  have hden : Continuous (fun t : ℝ => ((c : ℂ) + (t : ℂ) * Complex.I)
      * (((c : ℂ) + (t : ℂ) * Complex.I) + 1)) :=
    hline.mul (hline.add continuous_const)
  have hne : ∀ t : ℝ, ((c : ℂ) + (t : ℂ) * Complex.I)
      * (((c : ℂ) + (t : ℂ) * Complex.I) + 1) ≠ 0 := by
    intro t h
    rcases mul_eq_zero.mp h with h' | h'
    · have h2 : ((c : ℂ) + (t : ℂ) * Complex.I).re = 0 := by rw [h']; simp
      have h3 : ((c : ℂ) + (t : ℂ) * Complex.I).re = c := by simp
      rw [h3] at h2
      exact hc0 h2
    · have h2 : (((c : ℂ) + (t : ℂ) * Complex.I) + 1).re = 0 := by rw [h']; simp
      have h3 : (((c : ℂ) + (t : ℂ) * Complex.I) + 1).re = c + 1 := by simp
      rw [h3] at h2
      exact hcm (by linarith)
  have heq : (fun t : ℝ => detInt χ₁ χ R θw N ρ ((c : ℂ) + (t : ℂ) * Complex.I))
      = fun t : ℝ => (DirichletCharacter.LFunction χ (ρ + (c + (t : ℂ) * Complex.I))
          * DirichletCharacter.LFunction (χ * χ₁) (ρ + (c + (t : ℂ) * Complex.I))
          * sieveG χ₁ R θw (ρ + (c + (t : ℂ) * Complex.I)) χ
          * (N : ℂ) ^ (c + (t : ℂ) * Complex.I))
          / (((c : ℂ) + (t : ℂ) * Complex.I) * (((c : ℂ) + (t : ℂ) * Complex.I) + 1)) := rfl
  rw [heq]
  exact (((hL1.mul hL2).mul hG).mul hNc).div hden hne

/-- Integrability of the integrand on a vertical line, from a polynomial bound. -/
lemma integrable_detInt_of_bound (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ)
    (ρ : ℂ) (hN : (N : ℂ) ≠ 0) {c C A : ℝ} (hc0 : c ≠ 0) (hcm : c ≠ -1) (hc : c + ρ.re ≠ 1)
    (hA : A < -1) (hC : 0 < C)
    (hbd : ∀ t : ℝ, ‖detInt χ₁ χ R θw N ρ ((c : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ C * (1 + |t|) ^ A) :
    MeasureTheory.Integrable (fun t : ℝ => detInt χ₁ χ R θw N ρ ((c : ℂ) + (t : ℂ) * Complex.I)) := by
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => detInt χ₁ χ R θw N ρ ((c : ℂ) + (t : ℂ) * Complex.I)) :=
    (continuous_detInt_line χ₁ χ R θw N ρ hN hc0 hcm hc).aestronglyMeasurable
  have hdom : MeasureTheory.Integrable (fun t : ℝ => C * (1 + |t|) ^ A) := by
    have h1 : MeasureTheory.Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(-A))) :=
      integrable_one_add_norm (E := ℝ) (by simp; linarith)
    refine (h1.const_mul C).congr ?_
    filter_upwards with t
    simp only [Real.norm_eq_abs, neg_neg]
  exact hdom.mono' hmeas (Filter.Eventually.of_forall fun t => hbd t)

/-- `(1 + |T|)^A → 0` as `T → +∞`, for `A < 0`. -/
lemma tendsto_one_add_abs_rpow_atTop {A : ℝ} (hA : A < 0) :
    Filter.Tendsto (fun T : ℝ => (1 + |T|) ^ A) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun T : ℝ => |T| ^ A) Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun T : ℝ => |T| ^ (-(-A))) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (y := -A) (by linarith)).comp Filter.tendsto_abs_atTop_atTop
    simpa only [neg_neg] using h2
  refine squeeze_zero' (Filter.Eventually.of_forall fun T => Real.rpow_nonneg (by positivity) A) ?_ h1
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with T hT
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT
  have hpos : (0 : ℝ) < |T| := abs_pos.mpr hT0.ne'
  have hle : |T| ≤ 1 + |T| := by linarith
  exact Real.rpow_le_rpow_of_nonpos hpos hle hA.le

/-- `(1 + T)^A → 0` as `T → +∞`, for `A < 0`. -/
lemma tendsto_one_add_rpow_atTop {A : ℝ} (hA : A < 0) :
    Filter.Tendsto (fun T : ℝ => (1 + T) ^ A) Filter.atTop (nhds 0) := by
  refine (tendsto_one_add_abs_rpow_atTop hA).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
  rw [abs_of_nonneg hT]

/-- `K / (T - b) → 0` as `T → +∞`. -/
lemma tendsto_div_atTop_sub (K b : ℝ) :
    Filter.Tendsto (fun T : ℝ => K / (T - b)) Filter.atTop (nhds 0) := by
  have hsub : Filter.Tendsto (fun T : ℝ => T - b) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro a
    exact ⟨a + b, fun T hT => by linarith⟩
  have hinv : Filter.Tendsto (fun T : ℝ => (T - b)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsub
  simpa [div_eq_mul_inv] using hinv.const_mul K

/-- The horizontal edge integrals of the patched integrand tend to `0`. -/
lemma tendsto_detH_horizontal (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ)
    (ρ : ℂ) (hzero : DirichletCharacter.LFunction χ ρ = 0
      ∨ DirichletCharacter.LFunction (χ * χ₁) ρ = 0)
    (hρ1 : ρ ≠ 1) (hre : 0 < ρ.re) {C A : ℝ} (hA : A < 0) (hC : 0 < C)
    (hbd : ∀ x : ℝ, (1 / 2 - ρ.re) ≤ x → x ≤ 2 → ∀ T : ℝ, 1 + |ρ.im| ≤ |T| →
      ‖detInt χ₁ χ R θw N ρ ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤ C * (1 + |T|) ^ A) :
    Filter.Tendsto (fun T : ℝ => ∫ x : ℝ in (1 / 2 - ρ.re)..2,
        detH χ₁ χ R θw N ρ ((x : ℂ) + (T : ℂ) * Complex.I)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun T : ℝ => ∫ x : ℝ in (1 / 2 - ρ.re)..2,
        detH χ₁ χ R θw N ρ ((x : ℂ) - (T : ℂ) * Complex.I)) Filter.atTop (nhds 0) := by
  have hρim0 : (0 : ℝ) ≤ |ρ.im| := abs_nonneg ρ.im
  have hlen : (0 : ℝ) ≤ 2 - (1 / 2 - ρ.re) := by linarith
  have hlen' : (1 / 2 : ℝ) - ρ.re ≤ 2 := by linarith
  -- pointwise bound on the segment, upper edge
  have hseg : ∀ T : ℝ, 1 + |ρ.im| ≤ T → ∀ x ∈ Set.Icc (1 / 2 - ρ.re) 2,
      ‖detH χ₁ χ R θw N ρ ((x : ℂ) + (T : ℂ) * Complex.I)‖
        ≤ C * (1 + T) ^ A + ‖detRes χ₁ χ R θw N ρ‖ / (T - |ρ.im|) := by
    intro T hT x hx
    have hT0 : 0 < T := by linarith
    have hTabs : |T| = T := abs_of_nonneg hT0.le
    have hx1 : (1 / 2 - ρ.re) ≤ x := hx.1
    have hx2 : x ≤ 2 := hx.2
    have him : (((x : ℂ) + (T : ℂ) * Complex.I)).im = T := by simp
    have hs0 : ((x : ℂ) + (T : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have h2 := congrArg Complex.im h
      rw [him] at h2
      simp only [Complex.zero_im] at h2
      linarith
    have hsm : ((x : ℂ) + (T : ℂ) * Complex.I) ≠ -1 := by
      intro h
      have h2 := congrArg Complex.im h
      rw [him] at h2
      simp only [Complex.neg_im, Complex.one_im, neg_zero] at h2
      linarith
    have hsu : ((x : ℂ) + (T : ℂ) * Complex.I) ≠ 1 - ρ := by
      intro h
      have h2 := congrArg Complex.im h
      rw [him] at h2
      simp only [Complex.sub_im, Complex.one_im, zero_sub] at h2
      linarith [neg_le_abs ρ.im]
    rw [detH_eq χ₁ χ R θw N ρ hzero hρ1 hs0 hsm hsu]
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖detInt χ₁ χ R θw N ρ ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤ C * (1 + T) ^ A := by
      have h1' := hbd x hx1 hx2 T (by rw [hTabs]; exact hT)
      rwa [hTabs] at h1'
    have h2 : ‖detRes χ₁ χ R θw N ρ / (((x : ℂ) + (T : ℂ) * Complex.I) - (1 - ρ))‖
        ≤ ‖detRes χ₁ χ R θw N ρ‖ / (T - |ρ.im|) := by
      rw [norm_div]
      refine div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) ?_
      have h3 : (((x : ℂ) + (T : ℂ) * Complex.I) - (1 - ρ)).im = T + ρ.im := by simp
      calc T - |ρ.im| ≤ |T + ρ.im| := by
            have hh := abs_sub_abs_le_abs_sub T (-ρ.im)
            rw [abs_neg, abs_of_nonneg hT0.le] at hh
            simpa using hh
        _ = |(((x : ℂ) + (T : ℂ) * Complex.I) - (1 - ρ)).im| := by rw [h3]
        _ ≤ ‖((x : ℂ) + (T : ℂ) * Complex.I) - (1 - ρ)‖ := Complex.abs_im_le_norm _
    linarith
  -- pointwise bound on the segment, lower edge
  have hseg' : ∀ T : ℝ, 1 + |ρ.im| ≤ T → ∀ x ∈ Set.Icc (1 / 2 - ρ.re) 2,
      ‖detH χ₁ χ R θw N ρ ((x : ℂ) - (T : ℂ) * Complex.I)‖
        ≤ C * (1 + T) ^ A + ‖detRes χ₁ χ R θw N ρ‖ / (T - |ρ.im|) := by
    intro T hT x hx
    have hT0 : 0 < T := by linarith
    have hTabs : |T| = T := abs_of_nonneg hT0.le
    have hx1 : (1 / 2 - ρ.re) ≤ x := hx.1
    have hx2 : x ≤ 2 := hx.2
    have him : (((x : ℂ) - (T : ℂ) * Complex.I)).im = -T := by simp
    have hs0 : ((x : ℂ) - (T : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have h2 := congrArg Complex.im h
      rw [him] at h2
      simp only [Complex.zero_im] at h2
      linarith
    have hsm : ((x : ℂ) - (T : ℂ) * Complex.I) ≠ -1 := by
      intro h
      have h2 := congrArg Complex.im h
      rw [him] at h2
      simp only [Complex.neg_im, Complex.one_im, neg_zero] at h2
      linarith
    have hsu : ((x : ℂ) - (T : ℂ) * Complex.I) ≠ 1 - ρ := by
      intro h
      have h2 := congrArg Complex.im h
      rw [him] at h2
      simp only [Complex.sub_im, Complex.one_im, zero_sub] at h2
      linarith [neg_le_abs ρ.im, le_abs_self ρ.im, abs_nonneg ρ.im]
    rw [detH_eq χ₁ χ R θw N ρ hzero hρ1 hs0 hsm hsu]
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖detInt χ₁ χ R θw N ρ ((x : ℂ) - (T : ℂ) * Complex.I)‖ ≤ C * (1 + T) ^ A := by
      have h1' := hbd x hx1 hx2 (-T) (by rw [abs_neg, hTabs]; exact hT)
      have heq : ((x : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I) = (x : ℂ) - (T : ℂ) * Complex.I := by
        push_cast
        ring
      rw [heq, abs_neg, hTabs] at h1'
      exact h1'
    have h2 : ‖detRes χ₁ χ R θw N ρ / (((x : ℂ) - (T : ℂ) * Complex.I) - (1 - ρ))‖
        ≤ ‖detRes χ₁ χ R θw N ρ‖ / (T - |ρ.im|) := by
      rw [norm_div]
      refine div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) ?_
      have h3 : (((x : ℂ) - (T : ℂ) * Complex.I) - (1 - ρ)).im = -T + ρ.im := by simp
      calc T - |ρ.im| ≤ |(-T) + ρ.im| := by
            have hh := abs_sub_abs_le_abs_sub (-T) (-ρ.im)
            rw [abs_neg, abs_neg, abs_of_nonneg hT0.le] at hh
            simpa using hh
        _ = |(((x : ℂ) - (T : ℂ) * Complex.I) - (1 - ρ)).im| := by rw [h3]
        _ ≤ ‖((x : ℂ) - (T : ℂ) * Complex.I) - (1 - ρ)‖ := Complex.abs_im_le_norm _
    linarith
  have hmain : ∀ (f : ℝ → ℝ → ℂ), (∀ T : ℝ, 1 + |ρ.im| ≤ T → ∀ x ∈ Set.Icc (1 / 2 - ρ.re) 2,
        ‖f T x‖ ≤ C * (1 + T) ^ A + ‖detRes χ₁ χ R θw N ρ‖ / (T - |ρ.im|)) →
      Filter.Tendsto (fun T : ℝ => ∫ x : ℝ in (1 / 2 - ρ.re)..2, f T x) Filter.atTop (nhds 0) := by
    intro f hf
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero'
      (g := fun T : ℝ => (2 - (1 / 2 - ρ.re))
        * (C * (1 + T) ^ A + ‖detRes χ₁ χ R θw N ρ‖ / (T - |ρ.im|)))
      (Filter.Eventually.of_forall fun T => norm_nonneg _) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop (1 + |ρ.im|)] with T hT
      refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := C * (1 + T) ^ A + ‖detRes χ₁ χ R θw N ρ‖ / (T - |ρ.im|)) ?_) (le_of_eq ?_)
      · intro x hx
        rw [Set.uIoc_of_le hlen'] at hx
        exact hf T hT x ⟨le_of_lt hx.1, hx.2⟩
      · rw [abs_of_nonneg hlen]; ring
    · have hsum := (tendsto_one_add_rpow_atTop hA).const_mul C |>.add
        (tendsto_div_atTop_sub ‖detRes χ₁ χ R θw N ρ‖ |ρ.im|)
      simpa using hsum.const_mul (2 - (1 / 2 - ρ.re))
  constructor
  · exact hmain (fun T x => detH χ₁ χ R θw N ρ ((x : ℂ) + (T : ℂ) * Complex.I)) hseg
  · exact hmain (fun T x => detH χ₁ χ R θw N ρ ((x : ℂ) - (T : ℂ) * Complex.I)) hseg'

/-- The patched integrand minus the residue kernel equals the integrand, along a vertical line
`Re s = c` with `c ∉ {0, -1, 1 - Re ρ}`. -/
lemma detH_eq_line (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ)
    (hzero : DirichletCharacter.LFunction χ ρ = 0
      ∨ DirichletCharacter.LFunction (χ * χ₁) ρ = 0)
    (hρ1 : ρ ≠ 1) {c t : ℝ} (hc0 : c ≠ 0) (hcm : c ≠ -1) (hcu : c ≠ 1 - ρ.re) :
    detH χ₁ χ R θw N ρ ((c : ℂ) + (t : ℂ) * Complex.I)
      = detInt χ₁ χ R θw N ρ ((c : ℂ) + (t : ℂ) * Complex.I)
        - detRes χ₁ χ R θw N ρ / (((c : ℂ) + (t : ℂ) * Complex.I) - (1 - ρ)) := by
  refine detH_eq χ₁ χ R θw N ρ hzero hρ1 ?_ ?_ ?_
  · intro h
    have h2 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, Complex.zero_re] at h2
    exact hc0 (by linarith)
  · intro h
    have h2 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, Complex.neg_re,
      Complex.one_re] at h2
    exact hcm (by linarith)
  · intro h
    have h2 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, Complex.sub_re,
      Complex.one_re] at h2
    exact hcu (by linarith)

/-! ## Absolute convergence of the detector's Dirichlet series -/

lemma detCoeff_summable (χ₁ χ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) {R : ℕ}
    {θw : ℕ → ℝ} (hθ : IsSieveWeight R θw) {ρ : ℂ} (hρ : 1 / 2 < ρ.re) :
    Summable (fun n : ℕ => ‖detCoeff χ₁ χ θw n‖ / (n : ℝ) ^ (2 + ρ.re)) := by
  obtain ⟨C, hCpos, hC⟩ := Work.ZeroDensity.Huxley.cardDivisorsLe (δ := 1 / 4) (by norm_num)
  have ha : ∀ n : ℕ, ‖(aCoeff χ₁ n : ℂ)‖ ≤ ((n.divisors.card : ℕ) : ℝ) := by
    intro n
    rw [Complex.norm_real]
    have h1 : |aCoeff χ₁ n| ≤ ∑ d ∈ n.divisors, |(χ₁ d).re| := by
      rw [aCoeff]
      exact Finset.abs_sum_le_sum_abs _ _
    have h2 : ∑ d ∈ n.divisors, |(χ₁ d).re| ≤ ∑ d ∈ n.divisors, (1 : ℝ) := by
      refine Finset.sum_le_sum fun d hd => ?_
      have h3 : |(χ₁ (d : ZMod q)).re| ≤ ‖χ₁ (d : ZMod q)‖ := Complex.abs_re_le_norm _
      have h4 : ‖χ₁ (d : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ₁ _
      linarith
    calc |aCoeff χ₁ n| ≤ ∑ d ∈ n.divisors, |(χ₁ d).re| := h1
      _ ≤ ∑ d ∈ n.divisors, (1 : ℝ) := h2
      _ = ((n.divisors.card : ℕ) : ℝ) := by simp
  have htheta : ∀ n : ℕ, ‖∑ d ∈ n.divisors, (θw d : ℂ)‖ ≤ ((n.divisors.card : ℕ) : ℝ) := by
    intro n
    refine le_trans (norm_sum_le _ _) ?_
    have h2 : ∑ d ∈ n.divisors, ‖(θw d : ℂ)‖ ≤ ∑ d ∈ n.divisors, (1 : ℝ) := by
      refine Finset.sum_le_sum fun d hd => ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hθ.2.2 d
    calc ∑ d ∈ n.divisors, ‖(θw d : ℂ)‖ ≤ ∑ d ∈ n.divisors, (1 : ℝ) := h2
      _ = ((n.divisors.card : ℕ) : ℝ) := by simp
  have hcard : ∀ n : ℕ, ‖detCoeff χ₁ χ θw n‖ ≤ (((n.divisors.card : ℕ)) : ℝ) ^ 3 := by
    intro n
    simp only [detCoeff]
    rw [norm_mul, norm_mul, norm_pow]
    have hA := ha n
    have hB : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hC' := htheta n
    have hC2 : ‖∑ d ∈ n.divisors, (θw d : ℂ)‖ ^ 2 ≤ (((n.divisors.card : ℕ)) : ℝ) ^ 2 := by
      nlinarith [hC', norm_nonneg (∑ d ∈ n.divisors, (θw d : ℂ))]
    have hpos0 : (0 : ℝ) ≤ ((n.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
    calc ‖(aCoeff χ₁ n : ℂ)‖ * ‖χ (n : ZMod q)‖ * ‖∑ d ∈ n.divisors, (θw d : ℂ)‖ ^ 2
        ≤ ((n.divisors.card : ℕ) : ℝ) * 1 * (((n.divisors.card : ℕ) : ℝ) ^ 2) := by
          exact mul_le_mul (mul_le_mul hA hB (norm_nonneg _) (by positivity)) hC2 (by positivity)
            (by positivity)
      _ = (((n.divisors.card : ℕ)) : ℝ) ^ 3 := by ring
  have hbound : ∀ n : ℕ, 1 ≤ n → ‖detCoeff χ₁ χ θw n‖ ≤ C ^ 3 * (n : ℝ) ^ ((3 : ℝ) / 4) := by
    intro n hn1
    have hd : (((n.divisors.card : ℕ)) : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4) := hC n hn1
    have hd0 : (0 : ℝ) ≤ ((n.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    calc ‖detCoeff χ₁ χ θw n‖ ≤ (((n.divisors.card : ℕ)) : ℝ) ^ 3 := hcard n
      _ ≤ (C * (n : ℝ) ^ ((1 : ℝ) / 4)) ^ 3 := pow_le_pow_left₀ hd0 hd 3
      _ = C ^ 3 * (n : ℝ) ^ ((3 : ℝ) / 4) := by
          rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 4)) 3,
            ← Real.rpow_mul hn0]
          norm_num
  have hsummand : ∀ n : ℕ, ‖detCoeff χ₁ χ θw n‖ / (n : ℝ) ^ (2 + ρ.re)
      ≤ C ^ 3 * (n : ℝ) ^ (-(5 / 4 + ρ.re)) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · have h1 : ‖detCoeff χ₁ χ θw 0‖ = 0 := by
        rw [show detCoeff χ₁ χ θw 0 = 0 by simp [detCoeff, aCoeff, Nat.divisors_zero]]
        simp
      rw [h1, zero_div]
      simp only [Nat.cast_zero]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (le_refl 0) _)
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      have hpos : (0 : ℝ) < (n : ℝ) := by linarith
      calc ‖detCoeff χ₁ χ θw n‖ / (n : ℝ) ^ (2 + ρ.re)
          ≤ C ^ 3 * (n : ℝ) ^ ((3 : ℝ) / 4) / (n : ℝ) ^ (2 + ρ.re) := by
            apply div_le_div_of_nonneg_right (hbound n (Nat.one_le_iff_ne_zero.mpr hn))
            positivity
        _ = C ^ 3 * (n : ℝ) ^ ((3 : ℝ) / 4 - (2 + ρ.re)) := by
            rw [mul_div_assoc, ← Real.rpow_sub hpos]
        _ = C ^ 3 * (n : ℝ) ^ (-(5 / 4 + ρ.re)) := by ring_nf
  have hg : Summable (fun n : ℕ => C ^ 3 * (n : ℝ) ^ (-(5 / 4 + ρ.re))) := by
    have h := (Real.summable_nat_rpow_inv (p := 5 / 4 + ρ.re)).mpr (by linarith : (1 : ℝ) < 5 / 4 + ρ.re)
    refine (h.mul_left (C ^ 3)).congr fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
  exact Summable.of_nonneg_of_le (fun n => by positivity) hsummand hg


open MeasureTheory intervalIntegral Filter
open scoped Interval Topology

/-! ## The kernel computation for the vertical contour shift -/

/-- The kernel `(s + iT - u)⁻¹` on a horizontal edge is bounded by `1/(T - |Im u|)`. -/
lemma norm_kernel_top_le {u : ℂ} {s T : ℝ} (hT : |u.im| < T) :
    ‖(((s : ℂ) + (T : ℂ) * Complex.I) - u)⁻¹‖ ≤ 1 / (T - |u.im|) := by
  have hpos : 0 < T - |u.im| := by linarith
  have h1 : (((s : ℂ) + (T : ℂ) * Complex.I) - u).im = T - u.im := by simp
  have h2 : T - |u.im| ≤ ‖(((s : ℂ) + (T : ℂ) * Complex.I) - u)‖ := by
    have h3 : T - |u.im| ≤ |T - u.im| := by
      have h4 := abs_sub_abs_le_abs_sub T u.im
      rw [abs_of_nonneg (by linarith [abs_nonneg u.im] : (0 : ℝ) ≤ T)] at h4
      linarith
    calc T - |u.im| ≤ |T - u.im| := h3
      _ = |(((s : ℂ) + (T : ℂ) * Complex.I) - u).im| := by rw [h1]
      _ ≤ ‖(((s : ℂ) + (T : ℂ) * Complex.I) - u)‖ := Complex.abs_im_le_norm _
  rw [norm_inv, one_div, inv_le_inv₀ (lt_of_lt_of_le hpos h2) hpos]
  exact h2

/-- The kernel `(s - iT - u)⁻¹` on a horizontal edge is bounded by `1/(T - |Im u|)`. -/
lemma norm_kernel_bot_le {u : ℂ} {s T : ℝ} (hT : |u.im| < T) :
    ‖(((s : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - u)⁻¹‖ ≤ 1 / (T - |u.im|) := by
  have hpos : 0 < T - |u.im| := by linarith
  have h1 : (((s : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I) - u).im = -T - u.im := by simp
  have h2 : T - |u.im| ≤ ‖(((s : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I) - u)‖ := by
    have h3 : T - |u.im| ≤ |-T - u.im| := by
      have h4 := abs_sub_abs_le_abs_sub (-T) u.im
      rw [abs_neg, abs_of_nonneg (by linarith [abs_nonneg u.im] : (0 : ℝ) ≤ T)] at h4
      linarith
    calc T - |u.im| ≤ |-T - u.im| := h3
      _ = |(((s : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I) - u).im| := by rw [h1]
      _ ≤ ‖(((s : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I) - u)‖ := Complex.abs_im_le_norm _
  rw [norm_inv, one_div, inv_le_inv₀ (lt_of_lt_of_le hpos h2) hpos]
  exact h2

/-- The horizontal edge integrals of the kernel differ by at most `2(q-p)/(T - |Im u|)`. -/
lemma norm_kernel_horiz_diff_le {u : ℂ} {p q T : ℝ} (hpq : p ≤ q) (hT : |u.im| < T) :
    ‖(∫ x : ℝ in p..q, (((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - u)⁻¹)
      - (∫ x : ℝ in p..q, (((x : ℂ) + (T : ℂ) * Complex.I) - u)⁻¹)‖
      ≤ 2 * (q - p) / (T - |u.im|) := by
  have hpos : 0 < T - |u.im| := by linarith
  have hbot : ‖∫ x : ℝ in p..q, (((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - u)⁻¹‖
      ≤ 1 / (T - |u.im|) * (q - p) := by
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := 1 / (T - |u.im|)) (fun x hx => norm_kernel_bot_le hT)) ?_
    rw [show |q - p| = q - p from abs_of_nonneg (by linarith)]
  have htop : ‖∫ x : ℝ in p..q, (((x : ℂ) + (T : ℂ) * Complex.I) - u)⁻¹‖
      ≤ 1 / (T - |u.im|) * (q - p) := by
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := 1 / (T - |u.im|)) (fun x hx => norm_kernel_top_le hT)) ?_
    rw [show |q - p| = q - p from abs_of_nonneg (by linarith)]
  calc ‖(∫ x : ℝ in p..q, (((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - u)⁻¹)
        - (∫ x : ℝ in p..q, (((x : ℂ) + (T : ℂ) * Complex.I) - u)⁻¹)‖
      ≤ ‖∫ x : ℝ in p..q, (((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - u)⁻¹‖
        + ‖∫ x : ℝ in p..q, (((x : ℂ) + (T : ℂ) * Complex.I) - u)⁻¹‖ := norm_sub_le _ _
    _ ≤ 1 / (T - |u.im|) * (q - p) + 1 / (T - |u.im|) * (q - p) := add_le_add hbot htop
    _ = 2 * (q - p) / (T - |u.im|) := by
        field_simp
        ring

/-- **The kernel computation for the vertical contour shift**: the difference of the two
improper kernel integrals over the lines `Re s = q` and `Re s = p` tends to `2π`. -/
lemma kernelVertDiffTendsto (u : ℂ) (p q : ℝ) (hpq : p < q) (hu : p < u.re ∧ u.re < q) :
    Filter.Tendsto (fun T : ℝ =>
        (∫ y : ℝ in (-T)..T, (((q : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹)
      - (∫ y : ℝ in (-T)..T, (((p : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹))
      Filter.atTop (nhds (2 * (Real.pi : ℂ))) := by
  -- the rectangle identity, solved for the vertical difference
  have hrect : ∀ T : ℝ, |u.im| < T →
      Complex.I * ((∫ y : ℝ in (-T)..T, (((q : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹)
        - (∫ y : ℝ in (-T)..T, (((p : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹))
      = 2 * (Real.pi : ℂ) * Complex.I
        - ((∫ x : ℝ in p..q, (((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - u)⁻¹)
          - (∫ x : ℝ in p..q, (((x : ℂ) + (T : ℂ) * Complex.I) - u)⁻¹)) := by
    intro T hT
    have hT0 : 0 < T := lt_of_le_of_lt (abs_nonneg u.im) hT
    have h := Commons.Analysis.Complex.rectIntegral_sub_inv_inside
      (z := (p : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I)
      (w := (q : ℂ) + (T : ℂ) * Complex.I) (u := u)
      (by simp; exact hpq)
      (by simp; linarith)
      ⟨by simp; exact hu.1, by simp; exact hu.2, by simp; linarith [neg_abs_le u.im],
        by simp; linarith [le_abs_self u.im]⟩
    simp only [smul_eq_mul] at h
    rw [show ((p : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I).re = p by simp,
      show ((q : ℂ) + (T : ℂ) * Complex.I).re = q by simp,
      show ((p : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I).im = -T by simp,
      show ((q : ℂ) + (T : ℂ) * Complex.I).im = T by simp] at h
    linear_combination h
  -- the difference tends to `2π`, by comparison with the horizontal edges
  have hev : (fun T : ℝ =>
        Complex.I * ((∫ y : ℝ in (-T)..T, (((q : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹)
          - (∫ y : ℝ in (-T)..T, (((p : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹) - 2 * (Real.pi : ℂ)))
      =ᶠ[Filter.atTop] (fun T : ℝ =>
        -((∫ x : ℝ in p..q, (((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - u)⁻¹)
          - (∫ x : ℝ in p..q, (((x : ℂ) + (T : ℂ) * Complex.I) - u)⁻¹))) := by
    filter_upwards [Filter.eventually_gt_atTop |u.im|] with T hT
    have h := hrect T hT
    rw [mul_sub, h]
    ring
  have hzero : Filter.Tendsto (fun T : ℝ =>
      Complex.I * ((∫ y : ℝ in (-T)..T, (((q : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹)
        - (∫ y : ℝ in (-T)..T, (((p : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹) - 2 * (Real.pi : ℂ)))
      Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (g := fun T : ℝ => 2 * (q - p) / (T - |u.im|))
      (Filter.Eventually.of_forall fun T => norm_nonneg _) ?_ ?_
    · filter_upwards [hev, Filter.eventually_gt_atTop |u.im|] with T hT hTu
      rw [hT, norm_neg]
      exact norm_kernel_horiz_diff_le (u := u) (p := p) (q := q) (T := T) hpq.le hTu
    · refine (tendsto_div_atTop_sub (2 * (q - p)) |u.im|).congr fun T => ?_
      ring
  have hsub : Filter.Tendsto (fun T : ℝ =>
      (∫ y : ℝ in (-T)..T, (((q : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹)
        - (∫ y : ℝ in (-T)..T, (((p : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹) - 2 * (Real.pi : ℂ))
      Filter.atTop (nhds 0) := by
    have := hzero.const_mul (Complex.I)⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ Complex.I_ne_zero] using this
  have h2 : Filter.Tendsto (fun T : ℝ =>
      ((∫ y : ℝ in (-T)..T, (((q : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹)
        - (∫ y : ℝ in (-T)..T, (((p : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹) - 2 * (Real.pi : ℂ))
      + 2 * (Real.pi : ℂ)) Filter.atTop (nhds (0 + 2 * (Real.pi : ℂ))) :=
    hsub.add tendsto_const_nhds
  simpa using h2


/-! ## The patched vertical contour shift (correctly parenthesised) -/

/-- `y ↦ ((s + i y) - u)⁻¹` is continuous when `s ≠ u.re`. -/
lemma kernel_continuous {u : ℂ} {s : ℝ} (hsu : s ≠ u.re) :
    Continuous (fun y : ℝ => (((s : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹) := by
  refine Continuous.inv₀ ?_ ?_
  · fun_prop
  · intro y hy
    have hre : (((s : ℂ) + (y : ℂ) * Complex.I) - u).re = s - u.re := by simp
    have h0 : s - u.re = 0 := by rw [← hre, hy]; simp
    exact hsu (sub_eq_zero.mp h0)

/-- Splitting `H = F - a/(s-u)` (a.e. on the line `Re = s`) inside the interval integral. -/
lemma vertDecomp (H F : ℂ → ℂ) (a u : ℂ) (s T : ℝ) (hsu : s ≠ u.re)
    (hsae : ∀ᵐ t : ℝ, H ((s : ℂ) + (t : ℂ) * Complex.I)
        = F ((s : ℂ) + (t : ℂ) * Complex.I) - a / (((s : ℂ) + (t : ℂ) * Complex.I) - u))
    (hsint : MeasureTheory.Integrable (fun t : ℝ => F ((s : ℂ) + (t : ℂ) * Complex.I))) :
    (∫ y : ℝ in (-T)..T, H ((s : ℂ) + (y : ℂ) * Complex.I))
      = (∫ y : ℝ in (-T)..T, F ((s : ℂ) + (y : ℂ) * Complex.I))
        - a * (∫ y : ℝ in (-T)..T, (((s : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹) := by
  have hint : IntervalIntegrable (fun y : ℝ => (((s : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹)
      volume (-T) T := (kernel_continuous (u := u) hsu).intervalIntegrable (-T) T
  have h1 : (∫ y : ℝ in (-T)..T, H ((s : ℂ) + (y : ℂ) * Complex.I))
      = ∫ y : ℝ in (-T)..T,
          (F ((s : ℂ) + (y : ℂ) * Complex.I) - a / (((s : ℂ) + (y : ℂ) * Complex.I) - u)) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hsae] with t ht _
    exact ht
  rw [h1]
  simp only [div_eq_mul_inv]
  rw [intervalIntegral.integral_sub hsint.intervalIntegrable (hint.const_mul a)]
  rw [intervalIntegral.integral_const_mul]

/-- **Patched vertical contour shift**, correctly parenthesised:
`∫_ℝ F(q+it) dt = (∫_ℝ F(p+it) dt) + 2π a`. -/
theorem detContourShift (F H : ℂ → ℂ) (p q : ℝ) (hpq : p < q) (u a : ℂ)
    (hu : p < u.re ∧ u.re < q)
    (hH : ∀ R : ℝ, DifferentiableOn ℂ H (Set.uIcc p q ×ℂ Set.uIcc (-R) R))
    (hpae : ∀ᵐ t : ℝ, H ((p : ℂ) + (t : ℂ) * Complex.I)
        = F ((p : ℂ) + (t : ℂ) * Complex.I) - a / (((p : ℂ) + (t : ℂ) * Complex.I) - u))
    (hqae : ∀ᵐ t : ℝ, H ((q : ℂ) + (t : ℂ) * Complex.I)
        = F ((q : ℂ) + (t : ℂ) * Complex.I) - a / (((q : ℂ) + (t : ℂ) * Complex.I) - u))
    (htop : Filter.Tendsto (fun R : ℝ => ∫ x : ℝ in p..q, H ((x : ℂ) + (R : ℂ) * Complex.I))
      Filter.atTop (nhds 0))
    (hbot : Filter.Tendsto (fun R : ℝ => ∫ x : ℝ in p..q, H ((x : ℂ) - (R : ℂ) * Complex.I))
      Filter.atTop (nhds 0))
    (hpint : MeasureTheory.Integrable (fun t : ℝ => F ((p : ℂ) + (t : ℂ) * Complex.I)))
    (hqint : MeasureTheory.Integrable (fun t : ℝ => F ((q : ℂ) + (t : ℂ) * Complex.I))) :
    (∫ t : ℝ, F ((q : ℂ) + (t : ℂ) * Complex.I))
      = (∫ t : ℝ, F ((p : ℂ) + (t : ℂ) * Complex.I)) + 2 * Real.pi * a := by
  have hpne : p ≠ u.re := ne_of_lt hu.1
  have hqne : q ≠ u.re := ne_of_gt hu.2
  have hneg : Tendsto (fun T : ℝ => -T) atTop atBot := tendsto_neg_atTop_atBot
  have hFp := MeasureTheory.intervalIntegral_tendsto_integral hpint hneg tendsto_id
  have hFq := MeasureTheory.intervalIntegral_tendsto_integral hqint hneg tendsto_id
  have hker := kernelVertDiffTendsto u p q hpq hu
  have hpoint : ∀ T : ℝ,
      (∫ y : ℝ in (-T)..T, H ((q : ℂ) + (y : ℂ) * Complex.I))
        - (∫ y : ℝ in (-T)..T, H ((p : ℂ) + (y : ℂ) * Complex.I))
      = ((∫ y : ℝ in (-T)..T, F ((q : ℂ) + (y : ℂ) * Complex.I))
          - (∫ y : ℝ in (-T)..T, F ((p : ℂ) + (y : ℂ) * Complex.I)))
        - a * ((∫ y : ℝ in (-T)..T, (((q : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹)
          - (∫ y : ℝ in (-T)..T, (((p : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹)) := by
    intro T
    rw [vertDecomp H F a u q T hqne hqae hqint, vertDecomp H F a u p T hpne hpae hpint]
    ring
  have hVH : Tendsto (fun T : ℝ =>
      (∫ y : ℝ in (-T)..T, H ((q : ℂ) + (y : ℂ) * Complex.I))
        - (∫ y : ℝ in (-T)..T, H ((p : ℂ) + (y : ℂ) * Complex.I))) atTop (nhds 0) := by
    have h0 : Tendsto (fun T : ℝ => Complex.I *
        ((∫ x : ℝ in p..q, H ((x : ℂ) - (T : ℂ) * Complex.I))
          - (∫ x : ℝ in p..q, H ((x : ℂ) + (T : ℂ) * Complex.I)))) atTop (nhds 0) := by
      have h := (hbot.sub htop).const_mul Complex.I
      simpa using h
    refine h0.congr' ?_
    filter_upwards with T
    have h := rectVertIdentity H p q T (hH T)
    have hI : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
    have hBA : (∫ x : ℝ in p..q, H ((x : ℂ) - (T : ℂ) * Complex.I))
        - (∫ x : ℝ in p..q, H ((x : ℂ) + (T : ℂ) * Complex.I))
        = -(Complex.I * ((∫ y : ℝ in (-T)..T, H ((q : ℂ) + (y : ℂ) * Complex.I))
          - (∫ y : ℝ in (-T)..T, H ((p : ℂ) + (y : ℂ) * Complex.I)))) := by
      rw [h]; ring
    calc Complex.I * ((∫ x : ℝ in p..q, H ((x : ℂ) - (T : ℂ) * Complex.I))
          - (∫ x : ℝ in p..q, H ((x : ℂ) + (T : ℂ) * Complex.I)))
        = Complex.I * (-(Complex.I * ((∫ y : ℝ in (-T)..T, H ((q : ℂ) + (y : ℂ) * Complex.I))
            - (∫ y : ℝ in (-T)..T, H ((p : ℂ) + (y : ℂ) * Complex.I))))) := by rw [hBA]
      _ = (-(Complex.I * Complex.I)) * ((∫ y : ℝ in (-T)..T, H ((q : ℂ) + (y : ℂ) * Complex.I))
            - (∫ y : ℝ in (-T)..T, H ((p : ℂ) + (y : ℂ) * Complex.I))) := by ring
      _ = (∫ y : ℝ in (-T)..T, H ((q : ℂ) + (y : ℂ) * Complex.I))
            - (∫ y : ℝ in (-T)..T, H ((p : ℂ) + (y : ℂ) * Complex.I)) := by rw [hI]; ring
  have hN : Tendsto (fun T : ℝ =>
      ((∫ y : ℝ in (-T)..T, F ((q : ℂ) + (y : ℂ) * Complex.I))
        - (∫ y : ℝ in (-T)..T, F ((p : ℂ) + (y : ℂ) * Complex.I)))
      - a * ((∫ y : ℝ in (-T)..T, (((q : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹)
        - (∫ y : ℝ in (-T)..T, (((p : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹))) atTop
      (nhds (((∫ t : ℝ, F ((q : ℂ) + (t : ℂ) * Complex.I))
        - (∫ t : ℝ, F ((p : ℂ) + (t : ℂ) * Complex.I))) - a * (2 * (Real.pi : ℂ)))) :=
    (hFq.sub hFp).sub (hker.const_mul a)
  have heq2 : (fun T : ℝ =>
      ((∫ y : ℝ in (-T)..T, F ((q : ℂ) + (y : ℂ) * Complex.I))
        - (∫ y : ℝ in (-T)..T, F ((p : ℂ) + (y : ℂ) * Complex.I)))
      - a * ((∫ y : ℝ in (-T)..T, (((q : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹)
        - (∫ y : ℝ in (-T)..T, (((p : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹)))
      =ᶠ[atTop] (fun T : ℝ =>
      (∫ y : ℝ in (-T)..T, H ((q : ℂ) + (y : ℂ) * Complex.I))
        - (∫ y : ℝ in (-T)..T, H ((p : ℂ) + (y : ℂ) * Complex.I))) := by
    filter_upwards with T
    exact (hpoint T).symm
  have huniq : 0 = ((∫ t : ℝ, F ((q : ℂ) + (t : ℂ) * Complex.I))
        - (∫ t : ℝ, F ((p : ℂ) + (t : ℂ) * Complex.I))) - a * (2 * (Real.pi : ℂ)) :=
    tendsto_nhds_unique hVH (hN.congr' heq2)
  have hgoal : (∫ t : ℝ, F ((q : ℂ) + (t : ℂ) * Complex.I))
      - (∫ t : ℝ, F ((p : ℂ) + (t : ℂ) * Complex.I)) = 2 * Real.pi * a := by
    have h1 : (∫ t : ℝ, F ((q : ℂ) + (t : ℂ) * Complex.I))
        - (∫ t : ℝ, F ((p : ℂ) + (t : ℂ) * Complex.I)) = a * (2 * (Real.pi : ℂ)) := by
      linear_combination -huniq
    rw [h1]
    push_cast
    ring
  exact sub_eq_iff_eq_add'.mp hgoal


end Work.LinnikAreas.BGTZ
