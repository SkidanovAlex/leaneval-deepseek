/-
# `Work.FTS.GalBasis.exists_poly_approx_c4`

**Theorem** (`exists_poly_approx_c4`, the `C^4`-polynomial approximation lemma, item `T6` of
`FTS_ELL_GALERKIN.md` §3).  Let `f : ℝ → ℝ` be `C^4` at every point of `[a,b]`
(hypothesis `hf`, a *germ* condition).  Then for every `ε > 0` there are a finite set of
exponents `s : Finset ℕ` and coefficients `c : ℕ → ℝ` such that *all* derivatives of order
`≤ 4` of the polynomial `p x = ∑ k ∈ s, c k * (x - a) ^ k` are within `ε` of the
corresponding derivatives of `f` on `[a,b]`.

## The proof

1.  `hf` is a condition at each point separately.  By `ContDiffAt.eventually` every
    `x ∈ [a,b]` has a neighbourhood on which `f` is `C^4`; compactness of `[a,b]` gives a
    finite subcover, and then an interval `Ioo c d` around `[a,b]` contained in the union.
    This is the lemma
    `Work.FTS.GalBasis.PolyApprox.exists_contDiffOn_Ioo_of_contDiffAt_Icc`.
2.  Consequently `iteratedDeriv 4 f` is continuous on `[a,b]`
    (`Work.FTS.GalBasis.PolyApprox.continuousOn_iteratedDeriv_of_contDiffOn_Ioo`).
3.  Stone–Weierstrass on the compact set (the polynomial functions are dense in
    `C(Icc 0 (b-a), ℝ)`, applied to the shifted function `y ↦ f⁗(y + a)`) provides a
    polynomial `P : ℝ[X]` with `|P.eval (x - a) - iteratedDeriv 4 f x| < ε'` on `[a,b]`,
    where `ε' := ε / (2 * max 1 ((b-a)^4))`.  This is `gpa_weierstrass` below.
4.  The polynomial `p` is *integrated* from `f`:  take the Taylor polynomial of `f` of order
    `3` at `a` (whose coefficients are `A j = (j !)⁻¹ * iteratedDeriv j f a`, `j ≤ 3`) and
    add the fourfold antiderivative of `P`, i.e. the coefficients
    `c k = A k` for `k ≤ 3` and `c k = P.coeff (k-4) / k.descFactorial 4` for `k ≥ 4`, with
    `s = range 4 ∪ (range (P.natDegree + 1)).image (· + 4)`.  Then
    * `iteratedDeriv m p a = iteratedDeriv m f a` for `m ≤ 3` (`hp3`) and
    * `iteratedDeriv 4 p x = P.eval (x - a)` for every `x` (`hp4`);
    both rest on `iteratedDeriv_sum_pow_sub`, the computation of the iterated derivatives of
    a finite combination of powers of `(x - a)`.
5.  Hence `h := fun x => p x - f x` has `h^{(m)}(a) = 0` for `m < 4` and
    `|h^{(4)} y| ≤ ε'` on `[a,b]`; the Taylor ladder
    `Work.FTS.GalBasis.PolyApprox.iteratedDeriv_le_of_zero_taylor` (downward induction on the
    order using `iteratedDeriv_succ` and the fundamental theorem of calculus) gives
    `|h^{(i)} x| ≤ ε' * (b - a) ^ (4-i) ≤ ε' * max 1 ((b-a)^4) = ε/2 < ε`
    for `i ≤ 4`, which is the claim once `h^{(i)} = p^{(i)} - f^{(i)}` is rewritten with
    `iteratedDeriv_sub`.
-/
import Mathlib
import Submission.Work.FTS.GalBasis.Defs
import Submission.Work.FTS.GalBasis.PolyApprox.exists_contDiffOn_Ioo_of_contDiffAt_Icc
import Submission.Work.FTS.GalBasis.PolyApprox.continuousOn_iteratedDeriv_of_contDiffOn_Ioo
import Submission.Work.FTS.GalBasis.PolyApprox.iteratedDeriv_le_of_zero_taylor

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter Polynomial Finset

namespace Work.FTS.GalBasis

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The iterated derivatives of a finite combination of powers of `(x - a)` -/

/-- The iterated derivatives of `x ↦ ∑ k ∈ s, c k * (x - a) ^ k`:  the sum is differentiated
termwise, and `iteratedDeriv i (x ↦ (x - a) ^ k) x = k.descFactorial i * (x - a) ^ (k - i)`
(the descending factorial vanishes for `k < i`). -/
theorem iteratedDeriv_sum_pow_sub (s : Finset ℕ) (c : ℕ → ℝ) (a : ℝ) (i : ℕ) (x : ℝ) :
    iteratedDeriv i (fun y => ∑ k ∈ s, c k * (y - a) ^ k) x
      = ∑ k ∈ s, c k * ((k.descFactorial i : ℝ) * (x - a) ^ (k - i)) := by
  rw [iteratedDeriv_fun_sum (I := s) (f := fun k y => c k * (y - a) ^ k) (x := x) (n := i)]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDeriv_const_mul_field]
    congr 1
    have h := congr_fun (iteratedDeriv_comp_sub_const (𝕜 := ℝ) i (fun y : ℝ => y ^ k) a) x
    rw [h, iteratedDeriv_pow]
  · intro k hk
    fun_prop

/-! ## Uniform approximation of a continuous function on `[a,b]` by a polynomial in `x - a`

This is the Stone–Weierstrass theorem for the algebra of polynomial functions:  on the
compact set `Icc 0 (b - a)` the polynomial functions are dense in `C(Icc 0 (b-a), ℝ)`, and we
apply this to `y ↦ g (y + a)`. -/

theorem gpa_weierstrass {g : ℝ → ℝ} {a b : ℝ} (hg : ContinuousOn g (Set.Icc a b))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Polynomial ℝ, ∀ x ∈ Set.Icc a b, |P.eval (x - a) - g x| < ε := by
  have : CompactSpace (Set.Icc (0 : ℝ) (b - a)) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hmap : ∀ y : Set.Icc (0 : ℝ) (b - a), y.val + a ∈ Set.Icc a b := by
    intro y; exact ⟨by linarith [y.2.1], by linarith [y.2.2]⟩
  have hcont : Continuous (fun y : Set.Icc (0 : ℝ) (b - a) => y.val + a) :=
    continuous_subtype_val.add_const a
  have hc : Continuous (fun y : Set.Icc (0 : ℝ) (b - a) => g (y.val + a)) :=
    hg.comp_continuous hcont hmap
  obtain ⟨G, hG⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    (polynomialFunctions (Set.Icc (0 : ℝ) (b - a))) (polynomialFunctions_separatesPoints _)
    ⟨_, hc⟩ ε hε
  have hGs : (G : C(Set.Icc (0 : ℝ) (b - a), ℝ)) ∈
      Set.range (Polynomial.toContinuousMapOnAlgHom (Set.Icc (0 : ℝ) (b - a))) := by
    rw [← polynomialFunctions_coe]; exact G.2
  obtain ⟨P, hP⟩ := hGs
  refine ⟨P, ?_⟩
  intro x hx
  have hy : x - a ∈ Set.Icc (0 : ℝ) (b - a) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h1 : (G : C(Set.Icc (0 : ℝ) (b - a), ℝ)) ⟨x - a, hy⟩ = P.eval (x - a) := by
    rw [← hP, Polynomial.toContinuousMapOnAlgHom_apply, Polynomial.toContinuousMapOn_apply,
      Polynomial.toContinuousMap_apply]
  have h4 : (⟨fun y : Set.Icc (0 : ℝ) (b - a) => g (y.val + a), hc⟩ :
      C(Set.Icc (0 : ℝ) (b - a), ℝ)) ⟨x - a, hy⟩ = g x := by
    show g ((x - a) + a) = g x
    rw [show (x - a) + a = x by ring]
  have h2 := ContinuousMap.norm_coe_le_norm ((G : C(Set.Icc (0 : ℝ) (b - a), ℝ)) -
    ⟨fun y => g (y.val + a), hc⟩) ⟨x - a, hy⟩
  rw [ContinuousMap.sub_apply, h1] at h2
  rw [show ((⟨fun y : Set.Icc (0 : ℝ) (b - a) => g (y.val + a), hc⟩ :
      C(Set.Icc (0 : ℝ) (b - a), ℝ)) ⟨x - a, hy⟩) = g x from h4] at h2
  rw [Real.norm_eq_abs] at h2
  exact lt_of_le_of_lt h2 hG

/-! ## The approximation theorem -/

theorem exists_poly_approx_c4 {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 4 f x) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset ℕ) (c : ℕ → ℝ), ∀ i : ℕ, i ≤ 4 → ∀ x ∈ Set.Icc a b,
      |iteratedDeriv i (fun x => ∑ k ∈ s, c k * (x - a) ^ k) x - iteratedDeriv i f x| < ε := by
  classical
  -- Step 1: an open interval around `[a,b]` on which `f` is `C^4`.
  obtain ⟨c₀, d₀, hc₀a, hbd₀, hsub, hC⟩ :=
    Work.FTS.GalBasis.PolyApprox.exists_contDiffOn_Ioo_of_contDiffAt_Icc hab hf
  -- Step 2: continuity of the fourth derivative on `[a,b]`.
  have hcont4 : ContinuousOn (iteratedDeriv 4 f) (Set.Icc a b) :=
    Work.FTS.GalBasis.PolyApprox.continuousOn_iteratedDeriv_of_contDiffOn_Ioo hC hsub le_rfl
  -- Step 3: the constants and the polynomial approximation of `f⁗`.
  set D : ℝ := max 1 ((b - a) ^ 4) with hD
  have hDpos : 0 < D := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hDne : D ≠ 0 := ne_of_gt hDpos
  set ε' : ℝ := ε / (2 * D) with hε'def
  have hε'pos : 0 < ε' := by
    rw [hε'def]; exact div_pos hε (by linarith)
  obtain ⟨P, hP⟩ := gpa_weierstrass hcont4 hε'pos
  -- Step 4: the coefficients and the polynomial.
  let A : ℕ → ℝ := fun j => (j.factorial : ℝ)⁻¹ * iteratedDeriv j f a
  let cc : ℕ → ℝ := fun k => if k ≤ 3 then A k else P.coeff (k - 4) / (k.descFactorial 4 : ℝ)
  let ss : Finset ℕ := Finset.range 4 ∪ (Finset.range (P.natDegree + 1)).image (fun m => m + 4)
  refine ⟨ss, cc, ?_⟩
  have hpoly : ContDiff ℝ 4 (fun x : ℝ => ∑ k ∈ ss, cc k * (x - a) ^ k) := by
    apply ContDiff.sum
    intro k hk
    exact ContDiff.mul contDiff_const
      (ContDiff.pow (ContDiff.sub contDiff_id contDiff_const) k)
  -- the fourth derivative of `p` is `P (· - a)`
  have hp4 : ∀ x : ℝ, iteratedDeriv 4 (fun x : ℝ => ∑ k ∈ ss, cc k * (x - a) ^ k) x
      = P.eval (x - a) := by
    intro x
    rw [iteratedDeriv_sum_pow_sub]
    have hdisj : Disjoint (Finset.range 4)
        ((Finset.range (P.natDegree + 1)).image (fun m => m + 4)) := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [Finset.mem_range] at hk
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk'
      omega
    rw [Finset.sum_union hdisj]
    have hz : ∑ k ∈ Finset.range 4, cc k * ((k.descFactorial 4 : ℝ) * (x - a) ^ (k - 4)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_range] at hk
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : k < 4)]
      ring
    rw [hz, zero_add]
    have hinj : Set.InjOn (fun m => m + 4) (↑(Finset.range (P.natDegree + 1)) : Set ℕ) :=
      fun m _ n _ h => Nat.add_right_cancel h
    rw [Finset.sum_image hinj, Polynomial.eval_eq_sum_range]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [Finset.mem_range] at hm
    have hcm : cc (m + 4) = P.coeff m / ((m + 4).descFactorial 4 : ℝ) := by
      simp only [cc]
      rw [ite_eq_right (by omega : ¬ (m + 4 ≤ 3)), Nat.add_sub_cancel]
    rw [hcm]
    have hne : ((m + 4).descFactorial 4 : ℝ) ≠ 0 := by
      simp only [Nat.cast_ne_zero, ne_eq]
      exact fun h => absurd (Nat.descFactorial_eq_zero_iff_lt.mp h) (by omega)
    field_simp
    rw [Nat.add_sub_cancel]
  -- the lower derivatives of `p` match those of `f` at `a`
  have hp3 : ∀ m : ℕ, m ≤ 3 → iteratedDeriv m (fun x : ℝ => ∑ k ∈ ss, cc k * (x - a) ^ k) a
      = iteratedDeriv m f a := by
    intro m hm
    rw [iteratedDeriv_sum_pow_sub]
    have hsingle : ∑ k ∈ ss, cc k * ((k.descFactorial m : ℝ) * (a - a) ^ (k - m))
        = cc m * ((m.descFactorial m : ℝ) * (a - a) ^ (m - m)) := by
      apply Finset.sum_eq_single m
      · intro k hk hkm
        rcases lt_trichotomy k m with hlt | heq | hgt
        · have h1 : (k.descFactorial m : ℝ) = 0 := by
            rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]; norm_num
          rw [h1]; ring
        · exact absurd heq hkm
        · have h1 : (a - a) ^ (k - m) = 0 := by
            rw [sub_self, zero_pow (by omega : k - m ≠ 0)]
          rw [h1]; ring
      · intro hm'
        exact absurd (Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))) hm'
    rw [hsingle, Nat.sub_self, sub_self, pow_zero, mul_one]
    have hmm : ((m.descFactorial m : ℕ) : ℝ) = (m.factorial : ℝ) := by
      rw [Nat.descFactorial_self]
    rw [hmm]
    have hcm : cc m = A m := by simp only [cc]; rw [ite_eq_left hm]
    rw [hcm]
    simp only [A]
    have hf0 : (m.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  -- Step 5: the Taylor ladder for `h = p - f`.
  let hfun : ℝ → ℝ := fun x => (∑ k ∈ ss, cc k * (x - a) ^ k) - f x
  have hCh : ContDiffOn ℝ 4 hfun (Set.Ioo c₀ d₀) := hpoly.contDiffOn.sub hC
  have hMh : ∀ y ∈ Set.Icc a b, |iteratedDeriv 4 hfun y| ≤ ε' := by
    intro y hy
    have h4 : iteratedDeriv 4 hfun y
        = iteratedDeriv 4 (fun x : ℝ => ∑ k ∈ ss, cc k * (x - a) ^ k) y
          - iteratedDeriv 4 f y := by
      apply iteratedDeriv_sub
      · exact hpoly.contDiffAt
      · exact hf y hy
    rw [h4, hp4 y]
    exact le_of_lt (hP y hy)
  have h0h : ∀ m < 4, iteratedDeriv m hfun a = 0 := by
    intro m hm
    have h4 : iteratedDeriv m hfun a
        = iteratedDeriv m (fun x : ℝ => ∑ k ∈ ss, cc k * (x - a) ^ k) a
          - iteratedDeriv m f a := by
      apply iteratedDeriv_sub
      · exact hpoly.contDiffAt.of_le (by exact_mod_cast (le_of_lt hm))
      · exact (hf a (⟨le_rfl, hab⟩ : a ∈ Set.Icc a b)).of_le (by exact_mod_cast (le_of_lt hm))
    rw [h4, hp3 m (by omega), sub_self]
  have hladder : ∀ i : ℕ, i ≤ 4 → ∀ x ∈ Set.Icc a b,
      |iteratedDeriv i hfun x| ≤ ε' * (b - a) ^ (4 - i) :=
    Work.FTS.GalBasis.PolyApprox.iteratedDeriv_le_of_zero_taylor (c := c₀) (d := d₀)
      hab hCh hsub hε'pos.le hMh h0h
  -- Step 6: conclude.
  intro i hi x hx
  have hsubd : iteratedDeriv i hfun x
      = iteratedDeriv i (fun x : ℝ => ∑ k ∈ ss, cc k * (x - a) ^ k) x - iteratedDeriv i f x := by
    apply iteratedDeriv_sub
    · exact hpoly.contDiffAt.of_le (by exact_mod_cast hi)
    · exact (hf x hx).of_le (by exact_mod_cast hi)
  rw [← hsubd]
  refine lt_of_le_of_lt (hladder i hi x hx) ?_
  have hpow : (b - a) ^ (4 - i) ≤ D := by
    rw [hD]
    by_cases h : (b - a) ≤ 1
    · exact (pow_le_one₀ (by linarith [hx.1, hx.2]) h).trans (le_max_left _ _)
    · exact (pow_le_pow_right₀ (le_of_lt (lt_of_not_ge h)) (by omega)).trans (le_max_right _ _)
  have h2 : ε' * (b - a) ^ (4 - i) ≤ ε' * D := mul_le_mul_of_nonneg_left hpow hε'pos.le
  refine lt_of_le_of_lt h2 ?_
  have hcalc : ε' * D = ε / 2 := by
    rw [hε'def]
    field_simp
  rw [hcalc]
  linarith

end Work.FTS.GalBasis
