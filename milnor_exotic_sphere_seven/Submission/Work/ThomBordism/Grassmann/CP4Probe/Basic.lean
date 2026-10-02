import Mathlib
import Submission.Work.ThomBordism.Grassmann.CP4Probe.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace Work.ThomBordism.Grassmann

noncomputable section

/-! ## Inner products of standard basis vectors in `ℂⁿ` -/

theorem re_mul_conj (a b : ℂ) : (b * (starRingEnd ℂ) a).re = a.re * b.re + a.im * b.im := by
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem inner_single_single_c {n : ℕ} (i j : Fin n) (a b : ℂ) :
    inner ℝ (EuclideanSpace.single (𝕜 := ℂ) i a : EuclideanSpace ℂ (Fin n))
      (EuclideanSpace.single (𝕜 := ℂ) j b)
      = if i = j then (b * (starRingEnd ℂ) a).re else 0 := by
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  · rw [PiLp.single_apply, Complex.inner]
    by_cases h : i = j <;> simp [h, re_mul_conj]
  · intro j' _ hj'
    rw [Complex.inner, PiLp.single_apply]
    simp [hj']
  · intro h; exact absurd (Finset.mem_univ i) h

theorem I_mul_re (a : ℂ) : (Complex.I * a).re = -a.im := by simp [Complex.mul_re]

theorem I_mul_im (a : ℂ) : (Complex.I * a).im = a.re := by simp [Complex.mul_im]

theorem inner_coord_c {n : ℕ} (x y : EuclideanSpace ℂ (Fin n)) :
    inner ℝ x y = ∑ i : Fin n, (y.ofLp i * (starRingEnd ℂ) (x.ofLp i)).re := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun i _ => by rw [Complex.inner])

/-! ## The two projections preserve the inner product data -/

theorem inner_preC (x y : E5) :
    inner ℝ (preC x) (preC y)
      = ∑ i : Fin 3, (y.ofLp (idx3 i) * (starRingEnd ℂ) (x.ofLp (idx3 i))).re := by
  conv_lhs => rw [preC_single, preC_single]
  rw [sum_inner]
  conv_lhs => enter [2, i]; rw [inner_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i]
  · rw [inner_single_single_c, if_pos rfl]
  · intro j _ hj
    rw [inner_single_single_c, if_neg (fun h : i = j => hj h.symm)]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem inner_sufC (x y : E5) :
    inner ℝ (sufC x) (sufC y)
      = ∑ i : Fin 2, (y.ofLp (idx2 i) * (starRingEnd ℂ) (x.ofLp (idx2 i))).re := by
  conv_lhs => rw [sufC_single, sufC_single]
  rw [sum_inner]
  conv_lhs => enter [2, i]; rw [inner_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i]
  · rw [inner_single_single_c, if_pos rfl]
  · intro j _ hj
    rw [inner_single_single_c, if_neg (fun h : i = j => hj h.symm)]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem idx3_eq (i : Fin 3) :
    (finSumFinEquiv (m := 3) (n := 2) (Sum.inl i) : Fin 5) = idx3 i := by
  rw [finSumFinEquiv_apply_left]; exact Fin.ext rfl

theorem idx2_eq (i : Fin 2) :
    (finSumFinEquiv (m := 3) (n := 2) (Sum.inr i) : Fin 5) = idx2 i := by
  rw [finSumFinEquiv_apply_right]; exact Fin.ext rfl

theorem inner_split (x y : E5) :
    inner ℝ x y
      = (∑ i : Fin 3, (y.ofLp (idx3 i) * (starRingEnd ℂ) (x.ofLp (idx3 i))).re)
        + (∑ i : Fin 2, (y.ofLp (idx2 i) * (starRingEnd ℂ) (x.ofLp (idx2 i))).re) := by
  rw [inner_coord_c]
  have hsplit : (∑ i : Fin 5, (y.ofLp i * (starRingEnd ℂ) (x.ofLp i)).re)
      = ∑ p : Fin 3 ⊕ Fin 2,
          (y.ofLp (finSumFinEquiv (m := 3) (n := 2) p)
            * (starRingEnd ℂ) (x.ofLp (finSumFinEquiv (m := 3) (n := 2) p))).re :=
    (Equiv.sum_comp (finSumFinEquiv (m := 3) (n := 2))
      (fun i : Fin 5 => (y.ofLp i * (starRingEnd ℂ) (x.ofLp i)).re)).symm
  rw [hsplit, Fintype.sum_sum_type]
  simp only [idx3_eq, idx2_eq]

/-! ## The index facts for the two blocks -/

theorem probeAmbIdx_two_eight_val (i : Fin 6) :
    (probeAmbIdx 2 8 (by norm_num) (by norm_num) i).val = i.val := by
  fin_cases i <;> rfl

theorem probeAmbIdx_two_eight_lt_six (i : Fin 6) :
    (probeAmbIdx 2 8 (by norm_num) (by norm_num) i).val < 6 := by
  rw [probeAmbIdx_two_eight_val]; exact i.isLt

theorem idxB_val (j a : Fin 2) : (idxB j a).val = 6 + 2 * j.val + a.val := rfl

theorem probeAmbIdx_two_eight_ne_idxB (i : Fin 6) (j a : Fin 2) :
    probeAmbIdx 2 8 (by norm_num) (by norm_num) i ≠ idxB j a := by
  intro h
  have h1 := congrArg Fin.val h
  rw [probeAmbIdx_two_eight_val, idxB_val] at h1
  have := i.isLt
  omega


/-! ## The two blocks of the embedding -/

/-- The `a`-th standard basis vector of the block `B`. -/
abbrev eb (i a : Fin 2) : Amb 10 := EuclideanSpace.single (𝕜 := ℝ) (idxB i a) 1

theorem idxB_injective (a : Fin 2) : Function.Injective fun i : Fin 2 => idxB i a := by
  intro i j h
  have h1 := congrArg Fin.val h
  rw [idxB_val, idxB_val] at h1
  have hi := i.isLt
  exact Fin.ext (by omega)

theorem idxB_zero_ne_one (i j : Fin 2) : idxB i 0 ≠ idxB j 1 := by
  intro h
  have h1 := congrArg Fin.val h
  rw [idxB_val, idxB_val] at h1
  have hi := i.isLt
  have hj := j.isLt
  omega

theorem idxB_one_ne_zero (i j : Fin 2) : idxB i 1 ≠ idxB j 0 := by
  intro h
  exact idxB_zero_ne_one j i h.symm

theorem inner_single_one_self {n : ℕ} (a : Fin n) :
    inner ℝ (EuclideanSpace.single (𝕜 := ℝ) a (1 : ℝ) : EuclideanSpace ℝ (Fin n))
      (EuclideanSpace.single (𝕜 := ℝ) a 1) = 1 := by
  rw [inner_single_ite]; simp

theorem inner_single_one_of_ne {n : ℕ} {a b : Fin n} (h : a ≠ b) :
    inner ℝ (EuclideanSpace.single (𝕜 := ℝ) a (1 : ℝ) : EuclideanSpace ℝ (Fin n))
      (EuclideanSpace.single (𝕜 := ℝ) b 1) = 0 := by
  rw [inner_single_ite]; exact if_neg h

theorem inner_eb_same (i : Fin 2) (a : Fin 2) : inner ℝ (eb i a) (eb i a) = 1 := by
  rw [eb]; exact inner_single_one_self _

theorem inner_eb_ne (i j : Fin 2) (a : Fin 2) (h : i ≠ j) : inner ℝ (eb i a) (eb j a) = 0 := by
  rw [eb]
  exact inner_single_one_of_ne (fun hh => h (idxB_injective a hh))

theorem inner_eb_zero_one (i j : Fin 2) : inner ℝ (eb i 0) (eb j 1) = 0 := by
  rw [eb]
  exact inner_single_one_of_ne (idxB_zero_ne_one i j)

theorem inner_eb_one_zero (i j : Fin 2) : inner ℝ (eb i 1) (eb j 0) = 0 := by
  rw [eb]
  exact inner_single_one_of_ne (idxB_one_ne_zero i j)

/-! ## The first block -/

theorem inner_embA (u u' : E3) : inner ℝ (embA u) (embA u') = inner ℝ u u' := by
  rw [embA_apply, embA_apply, probeEmb_inner, cxE.inner_map_map]

theorem embA_complex (μ : ℂ) (u : E3) :
    embA (μ • u) = μ.re • embA u + μ.im • embA (Complex.I • u) := by
  rw [embA_apply, embA_apply, embA_apply, cxE_complex_smul, map_add, map_smul, map_smul]

theorem embA_apply_sum (u : E3) :
    embA u = ∑ i : Fin 6, (cxE u).ofLp i •
      (EuclideanSpace.single (𝕜 := ℝ)
        (probeAmbIdx 2 8 (by norm_num) (by norm_num) i) 1 : Amb 10) := by
  rw [embA_apply, probeEmb_apply]

/-! ## The second block -/

theorem embB_apply_eb (z : E2) :
    embB z = (∑ i : Fin 2, (z.ofLp i).re • eb i 0)
      + (∑ i : Fin 2, (z.ofLp i).im • eb i 1) :=
  embB_apply z

theorem inner_embB (z z' : E2) : inner ℝ (embB z) (embB z') = inner ℝ z z' := by
  rw [embB_apply_eb, embB_apply_eb, inner_add_left, inner_add_right, inner_add_right]
  have hA : inner ℝ (∑ i : Fin 2, (z.ofLp i).re • eb i 0)
      (∑ j : Fin 2, (z'.ofLp j).re • eb j 0) = ∑ i : Fin 2, (z.ofLp i).re * (z'.ofLp i).re := by
    rw [sum_inner]
    conv_lhs => enter [2, i]; rw [inner_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single i]
    · rw [real_inner_smul_left, real_inner_smul_right, inner_eb_same]; ring
    · intro j _ hj
      rw [real_inner_smul_left, real_inner_smul_right, inner_eb_ne i j 0 (fun h => hj h.symm)]
      ring
    · intro h; exact absurd (Finset.mem_univ i) h
  have hB : inner ℝ (∑ i : Fin 2, (z.ofLp i).re • eb i 0)
      (∑ j : Fin 2, (z'.ofLp j).im • eb j 1) = 0 := by
    conv_lhs => rw [sum_inner]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [inner_sum]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [real_inner_smul_left, real_inner_smul_right, inner_eb_zero_one i j]
    ring
  have hC : inner ℝ (∑ i : Fin 2, (z.ofLp i).im • eb i 1)
      (∑ j : Fin 2, (z'.ofLp j).re • eb j 0) = 0 := by
    conv_lhs => rw [sum_inner]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [inner_sum]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [real_inner_smul_left, real_inner_smul_right, inner_eb_one_zero i j]
    ring
  have hD : inner ℝ (∑ i : Fin 2, (z.ofLp i).im • eb i 1)
      (∑ j : Fin 2, (z'.ofLp j).im • eb j 1) = ∑ i : Fin 2, (z.ofLp i).im * (z'.ofLp i).im := by
    conv_lhs => rw [sum_inner]
    conv_lhs => enter [2, i]; rw [inner_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single i]
    · rw [real_inner_smul_left, real_inner_smul_right, inner_eb_same]; ring
    · intro j _ hj
      rw [real_inner_smul_left, real_inner_smul_right, inner_eb_ne i j 1 (fun h => hj h.symm)]
      ring
    · intro h; exact absurd (Finset.mem_univ i) h
  have hcoord : inner ℝ z z' = (∑ i : Fin 2, (z.ofLp i).re * (z'.ofLp i).re)
      + (∑ i : Fin 2, (z.ofLp i).im * (z'.ofLp i).im) := by
    rw [inner_coord_c (n := 2), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [re_mul_conj]
  rw [hA, hB, hC, hD, hcoord]
  ring

/-! ### Complex linearity of the second block -/

theorem embB_smul_re (μ : ℂ) (z : E2) :
    (∑ i : Fin 2, ((μ • z).ofLp i).re • eb i 0)
      = μ.re • (∑ i : Fin 2, (z.ofLp i).re • eb i 0)
        + μ.im • (∑ i : Fin 2, ((Complex.I • z).ofLp i).re • eb i 0) := by
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hμ : ((μ • z).ofLp i).re = μ.re * (z.ofLp i).re - μ.im * (z.ofLp i).im := by
    simp [WithLp.ofLp_smul, Pi.smul_apply, Complex.mul_re]
  have hI : ((Complex.I • z).ofLp i).re = -((z.ofLp i).im) := by
    simp [WithLp.ofLp_smul, Pi.smul_apply, I_mul_re]
  rw [smul_smul, smul_smul, ← add_smul, hμ, hI]
  try ring_nf

theorem embB_smul_im (μ : ℂ) (z : E2) :
    (∑ i : Fin 2, ((μ • z).ofLp i).im • eb i 1)
      = μ.re • (∑ i : Fin 2, (z.ofLp i).im • eb i 1)
        + μ.im • (∑ i : Fin 2, ((Complex.I • z).ofLp i).im • eb i 1) := by
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hμ : ((μ • z).ofLp i).im = μ.re * (z.ofLp i).im + μ.im * (z.ofLp i).re := by
    simp [WithLp.ofLp_smul, Pi.smul_apply, Complex.mul_im]
  have hI : ((Complex.I • z).ofLp i).im = (z.ofLp i).re := by
    simp [WithLp.ofLp_smul, Pi.smul_apply, I_mul_im]
  rw [smul_smul, smul_smul, ← add_smul, hμ, hI]
  try ring_nf

theorem embB_complex (μ : ℂ) (z : E2) :
    embB (μ • z) = μ.re • embB z + μ.im • embB (Complex.I • z) := by
  rw [embB_apply_eb, embB_apply_eb, embB_apply_eb, embB_smul_re, embB_smul_im,
    smul_add, smul_add]
  abel

/-! ## The cross term -/

theorem inner_embA_embB (u : E3) (z : E2) : inner ℝ (embA u) (embB z) = 0 := by
  rw [embA_apply_sum, embB_apply_eb, inner_add_right]
  have h1 : inner ℝ (∑ i : Fin 6, (cxE u).ofLp i •
      (EuclideanSpace.single (𝕜 := ℝ)
        (probeAmbIdx 2 8 (by norm_num) (by norm_num) i) 1 : Amb 10))
      (∑ j : Fin 2, (z.ofLp j).re • eb j 0) = 0 := by
    rw [sum_inner]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [inner_sum]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [real_inner_smul_left, real_inner_smul_right,
      inner_single_one_of_ne (probeAmbIdx_two_eight_ne_idxB i j 0)]
    ring
  have h2 : inner ℝ (∑ i : Fin 6, (cxE u).ofLp i •
      (EuclideanSpace.single (𝕜 := ℝ)
        (probeAmbIdx 2 8 (by norm_num) (by norm_num) i) 1 : Amb 10))
      (∑ j : Fin 2, (z.ofLp j).im • eb j 1) = 0 := by
    rw [sum_inner]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [inner_sum]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [real_inner_smul_left, real_inner_smul_right,
      inner_single_one_of_ne (probeAmbIdx_two_eight_ne_idxB i j 1)]
    ring
  rw [h1, h2, add_zero]

theorem inner_embB_embA (z : E2) (u : E3) : inner ℝ (embB z) (embA u) = 0 := by
  rw [real_inner_comm, inner_embA_embB]

/-! ## The embedding `ℂ⁵ → ℝ¹⁰` -/

theorem emb5_apply_eq (x : E5) : emb5 x = embA (preC x) + embB (sufC x) := rfl

theorem inner_emb5 (x y : E5) : inner ℝ (emb5 x) (emb5 y) = inner ℝ x y := by
  have h1 : inner ℝ x y = inner ℝ (preC x) (preC y) + inner ℝ (sufC x) (sufC y) := by
    rw [inner_split, inner_preC, inner_sufC]
  rw [emb5_apply_eq, emb5_apply_eq, h1, inner_add_left, inner_add_right, inner_add_right,
    inner_embA, inner_embA_embB, inner_embB_embA, inner_embB]
  abel

theorem emb5_complex_smul (μ : ℂ) (x : E5) :
    emb5 (μ • x) = μ.re • emb5 x + μ.im • emb5 (Complex.I • x) := by
  have h1 : embA (preC (μ • x))
      = μ.re • embA (preC x) + μ.im • embA (preC (Complex.I • x)) := by
    rw [map_smul preC μ x, embA_complex, map_smul preC Complex.I x]
  have h2 : embB (sufC (μ • x))
      = μ.re • embB (sufC x) + μ.im • embB (sufC (Complex.I • x)) := by
    rw [map_smul sufC μ x, embB_complex, map_smul sufC Complex.I x]
  rw [emb5_apply_eq, emb5_apply_eq, emb5_apply_eq, h1, h2, smul_add, smul_add]
  abel

end

end Work.ThomBordism.Grassmann
