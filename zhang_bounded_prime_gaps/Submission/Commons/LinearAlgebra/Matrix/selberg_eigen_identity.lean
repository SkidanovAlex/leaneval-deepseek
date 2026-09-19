import Mathlib.Analysis.Complex.Basic
import Submission.Commons.Data.Nat.sum_sum_mul_kernel

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Commons.LinearAlgebra.Matrix

open scoped BigOperators

variable {ι : Type*}

noncomputable def cauchyKernel (f : ι → ℝ) [DecidableEq ι] (i j : ι) : ℝ :=
  if i = j then 0 else (f i - f j)⁻¹

@[simp] lemma cauchyKernel_self (f : ι → ℝ) [DecidableEq ι] (i : ι) :
    cauchyKernel f i i = 0 := by simp [cauchyKernel]

lemma cauchyKernel_of_ne (f : ι → ℝ) [DecidableEq ι] {i j : ι} (h : i ≠ j) :
    cauchyKernel f i j = (f i - f j)⁻¹ := by simp [cauchyKernel, h]

lemma cauchyKernel_antisymm (f : ι → ℝ) [DecidableEq ι] (i j : ι) :
    cauchyKernel f j i = -cauchyKernel f i j := by
  rcases eq_or_ne i j with rfl | h
  · simp
  · rw [cauchyKernel_of_ne f h, cauchyKernel_of_ne f (Ne.symm h)]
    rw [show f j - f i = -(f i - f j) by ring, inv_neg]

lemma cauchyKernel_mul (f : ι → ℝ) [DecidableEq ι] (hinj : Function.Injective f)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    cauchyKernel f i j * cauchyKernel f i k
      = cauchyKernel f j k * (cauchyKernel f i j - cauchyKernel f i k) := by
  rw [cauchyKernel_of_ne f hij, cauchyKernel_of_ne f hik, cauchyKernel_of_ne f hjk]
  have ha : f i - f j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hinj h))
  have hb : f i - f k ≠ 0 := sub_ne_zero.mpr (fun h => hik (hinj h))
  have hc : f j - f k ≠ 0 := sub_ne_zero.mpr (fun h => hjk (hinj h))
  field_simp
  ring

lemma cauchyKernel_sq (f : ι → ℝ) [DecidableEq ι] (i j : ι) :
    cauchyKernel f i j ^ 2 = if i = j then 0 else ((f i - f j) ^ 2)⁻¹ := by
  rcases eq_or_ne i j with rfl | h
  · rw [cauchyKernel_self, if_pos rfl]; ring
  · rw [cauchyKernel_of_ne f h, if_neg h, inv_pow]

noncomputable def cauchyKernelC (f : ι → ℝ) [DecidableEq ι] (i j : ι) : ℂ := (cauchyKernel f i j : ℂ)

@[simp] lemma cauchyKernelC_self (f : ι → ℝ) [DecidableEq ι] (i : ι) :
    cauchyKernelC f i i = 0 := by simp [cauchyKernelC]

lemma cauchyKernelC_eq (f : ι → ℝ) [DecidableEq ι] (i j : ι) :
    cauchyKernelC f i j = if i = j then 0 else (((f i - f j : ℝ) : ℂ))⁻¹ := by
  rcases eq_or_ne i j with rfl | h
  · rw [cauchyKernelC_self, if_pos rfl]
  · rw [cauchyKernelC, cauchyKernel_of_ne f h, if_neg h, Complex.ofReal_inv]

lemma cauchyKernelC_antisymm (f : ι → ℝ) [DecidableEq ι] (i j : ι) :
    cauchyKernelC f j i = -cauchyKernelC f i j := by
  rw [cauchyKernelC, cauchyKernelC, cauchyKernel_antisymm f i j, Complex.ofReal_neg]

lemma cauchyKernelC_mul (f : ι → ℝ) [DecidableEq ι] (hinj : Function.Injective f)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    cauchyKernelC f i j * cauchyKernelC f i k
      = cauchyKernelC f j k * (cauchyKernelC f i j - cauchyKernelC f i k) := by
  show ((cauchyKernel f i j : ℝ) : ℂ) * ((cauchyKernel f i k : ℝ) : ℂ)
      = ((cauchyKernel f j k : ℝ) : ℂ) * (((cauchyKernel f i j : ℝ) : ℂ) - ((cauchyKernel f i k : ℝ) : ℂ))
  rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
      cauchyKernel_mul f hinj hij hik hjk]

lemma cauchyKernelC_star (f : ι → ℝ) [DecidableEq ι] (i j : ι) :
    star (cauchyKernelC f i j) = cauchyKernelC f i j := by
  rw [cauchyKernelC, Complex.star_def, Complex.conj_ofReal]

/-- Swapping the order of summation in a double sum over off-diagonal pairs. -/
lemma sum_erase_comm_gen {M : Type*} [AddCommGroup M] [DecidableEq ι]
    (s : Finset ι) (F : ι → ι → M) :
    (∑ a ∈ s, ∑ b ∈ s.erase a, F a b) = (∑ b ∈ s, ∑ a ∈ s.erase b, F a b) := by
  calc
    (∑ a ∈ s, ∑ b ∈ s.erase a, F a b)
        = (∑ a ∈ s, ((∑ b ∈ s, F a b) - F a a)) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            rw [Finset.sum_erase_eq_sub (s := s) (f := fun b => F a b) ha]
    _ = (∑ a ∈ s, ∑ b ∈ s, F a b) - (∑ a ∈ s, F a a) := by
            rw [Finset.sum_sub_distrib]
    _ = (∑ b ∈ s, ∑ a ∈ s, F a b) - (∑ a ∈ s, F a a) := by
            rw [Finset.sum_comm]
    _ = (∑ b ∈ s, ((∑ a ∈ s, F a b) - F b b)) := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ b ∈ s, ∑ a ∈ s.erase b, F a b := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            rw [Finset.sum_erase_eq_sub (s := s) (f := fun a => F a b) hb]

lemma sum_erase_univ_erase {M : Type*} [AddCommGroup M] [Fintype ι] [DecidableEq ι]
    {i j : ι} (hji : j ≠ i) (g : ι → M) :
    (∑ k ∈ (Finset.univ.erase i).erase j, g k) = (∑ k, g k) - g i - g j := by
  have hjs : j ∈ (Finset.univ.erase i : Finset ι) := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
  rw [Finset.sum_erase_eq_sub (s := Finset.univ.erase i) (f := g) hjs]
  rw [Finset.sum_erase_eq_sub (s := Finset.univ) (f := g) (Finset.mem_univ i)]

lemma star_I_mul_ofReal (mu : ℝ) :
    star (Complex.I * ((mu : ℝ) : ℂ)) = -(Complex.I * ((mu : ℝ) : ℂ)) := by
  rw [Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring

lemma star_neg_aux (a w : ℂ) (ha : star a = -a) : w * star (a * w) + star w * (a * w) = 0 := by
  rw [star_mul, ha]; ring

lemma mul_star_neg (a w : ℂ) (ha : star a = -a) : w * star (a * w) = -(star w) * (a * w) := by
  simpa only [neg_mul] using eq_neg_of_add_eq_zero_left (star_neg_aux a w ha)

lemma add_conj_mul (a b : ℂ) : a * star b + star a * b = ↑(2 * (star b * a).re) := by
  have h1 : a * star b + star a * b = (star b * a) + star (star b * a) := by
    rw [star_mul, star_star]; ring
  rw [h1]
  exact Complex.add_conj (star b * a)

lemma mul_self_star (w : ℂ) : w * star w = ↑(‖w‖ ^ 2) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]


lemma cauchy_inner_star (f : ι → ℝ) [Fintype ι] [DecidableEq ι] (z : ι → ℂ) (mu : ℝ)
    (hrel : ∀ j, ∑ k, cauchyKernelC f j k * z k = (Complex.I * ((mu : ℝ) : ℂ)) * z j)
    {i j : ι} (hji : j ≠ i) :
    (∑ k ∈ (Finset.univ.erase i).erase j, cauchyKernelC f j k * star (z k))
      = star ((Complex.I * ((mu : ℝ) : ℂ)) * z j) - cauchyKernelC f j i * star (z i) := by
  rw [sum_erase_univ_erase (M := ℂ) hji (fun k => cauchyKernelC f j k * star (z k))]
  have hsum : (∑ k, cauchyKernelC f j k * star (z k))
      = star ((Complex.I * ((mu : ℝ) : ℂ)) * z j) := by
    conv_rhs => rw [← hrel j]
    rw [star_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [star_mul, cauchyKernelC_star]
    ring
  rw [hsum, cauchyKernelC_self]
  ring

lemma cauchy_inner_id (f : ι → ℝ) [Fintype ι] [DecidableEq ι] (z : ι → ℂ) (mu : ℝ)
    (hrel : ∀ j, ∑ k, cauchyKernelC f j k * z k = (Complex.I * ((mu : ℝ) : ℂ)) * z j)
    {i j : ι} (hji : j ≠ i) :
    (∑ k ∈ (Finset.univ.erase i).erase j, cauchyKernelC f j k * z k)
      = (Complex.I * ((mu : ℝ) : ℂ)) * z j - cauchyKernelC f j i * z i := by
  rw [sum_erase_univ_erase (M := ℂ) hji (fun k => cauchyKernelC f j k * z k)]
  rw [hrel j, cauchyKernelC_self]
  ring


lemma inner_cancel (c w u a : ℂ) (ha : star a = -a) :
    w * (star (a * w) - c * star u) + star w * (a * w - c * u)
      = -c * (w * star u + star w * u) := by
  have h := star_neg_aux a w ha
  linear_combination h


/-- Selberg/Preissmann–Lévêque eigenvector identity for the Hilbert-type (Cauchy) kernel.
Let `f : ι → ℝ` be injective, `U i j = (f i - f j)⁻¹` off the diagonal and `0` on it, and let
`z : ι → ℂ` satisfy `∑ j, U i j * z j = (I * μ) * z i` for a real `μ`.  Then for every `i`,
`μ² ‖z i‖² = ∑_{j ≠ i} (f i - f j)⁻² (‖z j‖² + 2 Re(conj (z i) * z j))`. -/
theorem selberg_eigen_identity {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (hinj : Function.Injective f) (z : ι → ℂ) (mu : ℝ)
    (hrel : ∀ i, ∑ j, (if i = j then 0 else (((f i - f j : ℝ) : ℂ))⁻¹) * z j
              = (Complex.I * ((mu : ℝ) : ℂ)) * z i) :
    ∀ i, mu ^ 2 * ‖z i‖ ^ 2
      = ∑ j, (if i = j then 0 else ((f i - f j) ^ 2)⁻¹
          * (‖z j‖ ^ 2 + 2 * (star (z i) * z j).re)) := by
  intro i
  have hrelC : ∀ j, ∑ k, cauchyKernelC f j k * z k = (Complex.I * ((mu : ℝ) : ℂ)) * z j := by
    intro j
    rw [← hrel j]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [cauchyKernelC_eq]
  set s : Finset ι := Finset.univ.erase i with hs
  have hmem : ∀ j, j ∈ s ↔ j ≠ i := by intro j; rw [hs]; simp
  set Q : ℂ := (∑ j, cauchyKernelC f i j * z j) * star (∑ k, cauchyKernelC f i k * z k) with hQdef
  have hS : (∑ j, cauchyKernelC f i j * z j) = ∑ j ∈ s, cauchyKernelC f i j * z j := by
    rw [hs]
    exact (Finset.sum_erase (Finset.univ)
      (f := fun j => cauchyKernelC f i j * z j) (a := i) (by simp)).symm
  have hstarS : star (∑ k, cauchyKernelC f i k * z k) = ∑ k ∈ s, cauchyKernelC f i k * star (z k) := by
    rw [star_sum]
    have h1 : (∑ k, star (cauchyKernelC f i k * z k)) = ∑ k, cauchyKernelC f i k * star (z k) := by
      refine Finset.sum_congr rfl (fun k _ => ?_); rw [star_mul, cauchyKernelC_star]; ring
    rw [h1, hs]
    exact (Finset.sum_erase (Finset.univ)
      (f := fun k => cauchyKernelC f i k * star (z k)) (a := i) (by simp)).symm
  -- split off diagonal
  have hsplit : (∑ j ∈ s, ∑ k ∈ s, cauchyKernelC f i j * cauchyKernelC f i k * (z j * star (z k)))
      = (∑ j ∈ s, (cauchyKernelC f i j)^2 * (z j * star (z j)))
        + (∑ j ∈ s, ∑ k ∈ s.erase j, cauchyKernelC f i j * cauchyKernelC f i k * (z j * star (z k))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [← Finset.sum_erase_add (s := s)
      (f := fun k => cauchyKernelC f i j * cauchyKernelC f i k * (z j * star (z k))) hj]
    ring
  -- off-diagonal computation
  have hOff : (∑ j ∈ s, ∑ k ∈ s.erase j, cauchyKernelC f i j * cauchyKernelC f i k * (z j * star (z k)))
      = ∑ j ∈ s, (cauchyKernelC f i j)^2 * (z j * star (z i) + star (z j) * z i) := by
    have e1 : (∑ j ∈ s, ∑ k ∈ s.erase j, cauchyKernelC f i j * cauchyKernelC f i k * (z j * star (z k)))
        = ∑ j ∈ s, ∑ k ∈ s.erase j,
            cauchyKernelC f j k * (cauchyKernelC f i j - cauchyKernelC f i k) * (z j * star (z k)) := by
      refine Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun k hk => ?_))
      obtain ⟨hkj, hks⟩ := Finset.mem_erase.mp hk
      have hji : j ≠ i := (hmem j).mp hj
      have hki : k ≠ i := (hmem k).mp hks
      rw [cauchyKernelC_mul f hinj (Ne.symm hji) (Ne.symm hki) (Ne.symm hkj)]
    have e2 : (∑ j ∈ s, ∑ k ∈ s.erase j,
            cauchyKernelC f j k * (cauchyKernelC f i j - cauchyKernelC f i k) * (z j * star (z k)))
        = (∑ j ∈ s, ∑ k ∈ s.erase j, cauchyKernelC f j k * cauchyKernelC f i j * (z j * star (z k)))
          - (∑ j ∈ s, ∑ k ∈ s.erase j, cauchyKernelC f j k * cauchyKernelC f i k * (z j * star (z k))) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      ring
    have e3 : (∑ j ∈ s, ∑ k ∈ s.erase j, cauchyKernelC f j k * cauchyKernelC f i k * (z j * star (z k)))
        = - (∑ j ∈ s, ∑ k ∈ s.erase j, cauchyKernelC f j k * cauchyKernelC f i j * (z k * star (z j))) := by
      rw [sum_erase_comm_gen s (fun j k => cauchyKernelC f j k * cauchyKernelC f i k * (z j * star (z k)))]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [cauchyKernelC_antisymm f j k]
      ring
    have eT1T2 : (∑ j ∈ s, ∑ k ∈ s.erase j, cauchyKernelC f j k * cauchyKernelC f i j * (z j * star (z k)))
          - (∑ j ∈ s, ∑ k ∈ s.erase j, cauchyKernelC f j k * cauchyKernelC f i k * (z j * star (z k)))
        = ∑ j ∈ s, ∑ k ∈ s.erase j, cauchyKernelC f j k * cauchyKernelC f i j
            * (z j * star (z k) + z k * star (z j)) := by
      rw [e3, sub_neg_eq_add, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      ring
    have efactor : (∑ j ∈ s, ∑ k ∈ s.erase j, cauchyKernelC f j k * cauchyKernelC f i j
            * (z j * star (z k) + z k * star (z j)))
        = ∑ j ∈ s, cauchyKernelC f i j
            * (∑ k ∈ s.erase j, cauchyKernelC f j k * (z j * star (z k) + z k * star (z j))) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      ring
    have hinner : ∀ j ∈ s, (∑ k ∈ s.erase j, cauchyKernelC f j k * (z j * star (z k) + z k * star (z j)))
        = - cauchyKernelC f j i * (z j * star (z i) + star (z j) * z i) := by
      intro j hj
      have hji : j ≠ i := (hmem j).mp hj
      have hsplit2 : (∑ k ∈ s.erase j, cauchyKernelC f j k * (z j * star (z k) + z k * star (z j)))
          = z j * (∑ k ∈ s.erase j, cauchyKernelC f j k * star (z k))
            + star (z j) * (∑ k ∈ s.erase j, cauchyKernelC f j k * z k) := by
        rw [Finset.sum_congr rfl (fun k _ =>
          show cauchyKernelC f j k * (z j * star (z k) + z k * star (z j))
            = z j * (cauchyKernelC f j k * star (z k)) + star (z j) * (cauchyKernelC f j k * z k) by ring)]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [hsplit2, hs]
      rw [cauchy_inner_star f z mu hrelC hji, cauchy_inner_id f z mu hrelC hji]
      exact inner_cancel (cauchyKernelC f j i) (z j) (z i)
        (Complex.I * ((mu : ℝ) : ℂ)) (star_I_mul_ofReal mu)
    calc (∑ j ∈ s, ∑ k ∈ s.erase j, cauchyKernelC f i j * cauchyKernelC f i k * (z j * star (z k)))
        = ∑ j ∈ s, ∑ k ∈ s.erase j,
            cauchyKernelC f j k * (cauchyKernelC f i j - cauchyKernelC f i k) * (z j * star (z k)) := e1
      _ = (∑ j ∈ s, ∑ k ∈ s.erase j, cauchyKernelC f j k * cauchyKernelC f i j * (z j * star (z k)))
          - (∑ j ∈ s, ∑ k ∈ s.erase j, cauchyKernelC f j k * cauchyKernelC f i k * (z j * star (z k))) := e2
      _ = ∑ j ∈ s, ∑ k ∈ s.erase j, cauchyKernelC f j k * cauchyKernelC f i j
            * (z j * star (z k) + z k * star (z j)) := eT1T2
      _ = ∑ j ∈ s, cauchyKernelC f i j
            * (∑ k ∈ s.erase j, cauchyKernelC f j k * (z j * star (z k) + z k * star (z j))) := efactor
      _ = ∑ j ∈ s, cauchyKernelC f i j
            * (- cauchyKernelC f j i * (z j * star (z i) + star (z j) * z i)) := by
          refine Finset.sum_congr rfl (fun j hj => ?_); rw [hinner j hj]
      _ = ∑ j ∈ s, (cauchyKernelC f i j)^2 * (z j * star (z i) + star (z j) * z i) := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [cauchyKernelC_antisymm f i j]; ring
  have hQ1 : Q = ∑ j ∈ s, (cauchyKernelC f i j)^2
      * (z j * star (z j) + z j * star (z i) + star (z j) * z i) := by
    calc Q
        = ∑ j ∈ s, ∑ k ∈ s, cauchyKernelC f i j * cauchyKernelC f i k * (z j * star (z k)) := by
          rw [hQdef, hstarS, hS, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_)); ring
      _ = (∑ j ∈ s, (cauchyKernelC f i j)^2 * (z j * star (z j)))
            + (∑ j ∈ s, ∑ k ∈ s.erase j,
                cauchyKernelC f i j * cauchyKernelC f i k * (z j * star (z k))) := hsplit
      _ = (∑ j ∈ s, (cauchyKernelC f i j)^2 * (z j * star (z j)))
            + (∑ j ∈ s, (cauchyKernelC f i j)^2 * (z j * star (z i) + star (z j) * z i)) := by rw [hOff]
      _ = ∑ j ∈ s, (cauchyKernelC f i j)^2
            * (z j * star (z j) + z j * star (z i) + star (z j) * z i) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun j _ => ?_); ring
  have hQ2 : (∑ j ∈ s, (cauchyKernelC f i j)^2
        * (z j * star (z j) + z j * star (z i) + star (z j) * z i))
      = ((∑ j ∈ s, cauchyKernel f i j ^ 2
          * (‖z j‖ ^ 2 + 2 * (star (z i) * z j).re) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [cauchyKernelC, ← Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_add,
      ← mul_self_star (z j), ← add_conj_mul (z j) (z i)]
    ring
  have hQ3 : Q = ((mu ^ 2 * ‖z i‖ ^ 2 : ℝ) : ℂ) := by
    rw [hQdef, hrelC i, Complex.star_def, Complex.mul_conj]
    rw [show Complex.normSq ((Complex.I * ((mu : ℝ) : ℂ)) * z i) = mu ^ 2 * ‖z i‖ ^ 2 by
      rw [map_mul, map_mul, Complex.normSq_I, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
      ring]
  have hcast : ((mu ^ 2 * ‖z i‖ ^ 2 : ℝ) : ℂ)
      = ((∑ j ∈ s, cauchyKernel f i j ^ 2 * (‖z j‖ ^ 2 + 2 * (star (z i) * z j).re) : ℝ) : ℂ) := by
    rw [← hQ3, hQ1]
    exact hQ2
  have hreal : mu ^ 2 * ‖z i‖ ^ 2
      = ∑ j ∈ s, cauchyKernel f i j ^ 2 * (‖z j‖ ^ 2 + 2 * (star (z i) * z j).re) :=
    Complex.ofReal_inj.mp hcast
  have hterm : ∀ j, (if i = j then 0 else ((f i - f j) ^ 2)⁻¹
        * (‖z j‖ ^ 2 + 2 * (star (z i) * z j).re))
      = cauchyKernel f i j ^ 2 * (‖z j‖ ^ 2 + 2 * (star (z i) * z j).re) := by
    intro j
    rw [cauchyKernel_sq]
    by_cases h : i = j
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]
  have hRHS : (∑ j, (if i = j then 0 else ((f i - f j) ^ 2)⁻¹
        * (‖z j‖ ^ 2 + 2 * (star (z i) * z j).re)))
      = ∑ j ∈ s, cauchyKernel f i j ^ 2 * (‖z j‖ ^ 2 + 2 * (star (z i) * z j).re) := by
    simp_rw [hterm]
    rw [hs]
    rw [← Finset.sum_erase (Finset.univ)
      (f := fun j => cauchyKernel f i j ^ 2 * (‖z j‖ ^ 2 + 2 * (star (z i) * z j).re))
      (a := i) (by simp)]
  rw [hRHS]
  exact hreal

end Commons.LinearAlgebra.Matrix