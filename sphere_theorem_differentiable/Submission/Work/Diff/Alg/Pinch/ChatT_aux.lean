import Mathlib
import Submission.Work.Diff.Alg.q2p_defs
import Submission.Work.Diff.Alg.q2p_transform
import Submission.Work.Diff.Alg.Q2PR.orthonormal_basis
import Submission.Work.Diff.Alg.Pinch.inPIC2_cone_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary lemmas for `Work.Diff.Alg.Pinch.ChatT_one_step_pic`

The "one step" lemma needs the affine-in-`δ` inequality
`EFun S v + s * EFun X v - δ * EFun (Iso n) v ≥ 0` for all real four-tuples `v = (x,y,z,w)`, for
every small `s`.  Since all three forms are homogeneous quartics which vanish on the degenerate
directions `ζ∧η = 0` (here `ζ = x+iy`, `η = z+iw`), the natural normalisation is by the complex
`2`-frames: `EFun R v` only depends on `ζ∧η`, and the quotient `EFun R v / EFun (Iso n) v` is
attained on the compact set `K` of `cHerm`-orthonormal pairs of complex vectors.

This file collects the elementary dictionary between the real four-tuples and complex pairs, the
value of `EFunC (Iso n)`, and the compactness of `K`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg Work.Diff.Alg.Q2P Work.Diff.Alg.Q2PR

variable {n : ℕ}

/-! ## The complexified squared norm -/

/-- `cNSq` in terms of the real and imaginary parts. -/
theorem ChatT_cNSq_re (ζ : Fin n → ℂ) :
    cNSq ζ = dot (cRe ζ) (cRe ζ) + dot (cIm ζ) (cIm ζ) := by
  simp only [cNSq, dot, cRe, cIm, Complex.normSq_apply]
  rw [Finset.sum_add_distrib]

/-- `cNSq` is multiplicative for complex scalars. -/
theorem ChatT_cNSq_smul (w : ℂ) (ζ : Fin n → ℂ) :
    cNSq (w • ζ) = Complex.normSq w * cNSq ζ := by
  have h : (cNSq (w • ζ) : ℂ) = ((Complex.normSq w * cNSq ζ : ℝ) : ℂ) := by
    rw [← cHerm_self, cHerm_smul₁, cHerm_smul₂, cHerm_self]
    rw [show w * (star w * (cNSq ζ : ℂ)) = (w * star w) * (cNSq ζ : ℂ) from by ring]
    rw [Complex.star_def, Complex.mul_conj]
    push_cast
    ring
  exact_mod_cast h

/-- `cNSq` is homogeneous of degree `2` for real scalars. -/
theorem ChatT_cNSq_ofReal_smul (r : ℝ) (ζ : Fin n → ℂ) :
    cNSq ((r : ℂ) • ζ) = r ^ 2 * cNSq ζ := by
  rw [ChatT_cNSq_smul, Complex.normSq_ofReal]
  ring

/-! ## The value of `EFunC (Iso n)` -/

/-- `EFunC` of the round sphere is the Gram determinant of the two complex vectors. -/
theorem ChatT_EFunC_iso (ζ η : Fin n → ℂ) :
    EFunC (Iso n) ζ η = cNSq ζ * cNSq η - Complex.normSq (cHerm ζ η) := by
  have h := Cone.EF_iso n (cRe ζ) (cIm ζ) (cRe η) (cIm η)
  rw [show EFunC (Iso n) ζ η
      = Cone.EF (Iso n) (cRe ζ) (cIm ζ) (cRe η) (cIm η) from rfl, h,
    ChatT_cNSq_re ζ, ChatT_cNSq_re η, Complex.normSq_apply, cHerm_re, cHerm_im]
  ring

/-- `EFunC (Iso n)` is nonnegative. -/
theorem ChatT_EFunC_iso_nonneg (ζ η : Fin n → ℂ) : 0 ≤ EFunC (Iso n) ζ η :=
  Cone.inPIC2_iso n (cRe ζ) (cIm ζ) (cRe η) (cIm η)

/-- On the orthonormal set `K` the round sphere has value `1`. -/
theorem ChatT_EFunC_iso_eq_one {ζ η : Fin n → ℂ}
    (h1 : cNSq ζ = 1) (h2 : cNSq η = 1) (h3 : cHerm ζ η = 0) :
    EFunC (Iso n) ζ η = 1 := by
  rw [ChatT_EFunC_iso, h1, h2, h3]
  simp

/-! ## The dictionary between real four-tuples and complex pairs -/

theorem ChatT_cRe_mk (x y : Fin n → ℝ) :
    cRe (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) = x := by
  ext i; simp [cRe]

theorem ChatT_cIm_mk (x y : Fin n → ℝ) :
    cIm (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) = y := by
  ext i; simp [cIm]

/-- `EFunC` of the complexification of a real four-tuple is `EFun`. -/
theorem ChatT_EFunC_mk (R : Curv4 n) (x y z w : Fin n → ℝ) :
    EFunC R (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)
      (fun i => (z i : ℂ) + (w i : ℂ) * Complex.I) = EFun R x y z w := by
  have h1 : cRe (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) = x := ChatT_cRe_mk x y
  have h2 : cIm (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) = y := ChatT_cIm_mk x y
  have h3 : cRe (fun i => (z i : ℂ) + (w i : ℂ) * Complex.I) = z := ChatT_cRe_mk z w
  have h4 : cIm (fun i => (z i : ℂ) + (w i : ℂ) * Complex.I) = w := ChatT_cIm_mk z w
  simp only [EFunC, h1, h2, h3, h4]

/-- `InPIC2` in complex form. -/
theorem ChatT_inPIC2_EFunC {R : Curv4 n} (hR : InPIC2 R) (ζ η : Fin n → ℂ) :
    0 ≤ EFunC R ζ η := hR (cRe ζ) (cIm ζ) (cRe η) (cIm η)

/-- The strictness hypothesis in complex form. -/
theorem ChatT_strict_EFunC {S X : Curv4 n}
    (hstrict : ∀ x y z w : Fin n → ℝ, EFun S x y z w = 0 →
      EFun (Iso n) x y z w ≠ 0 → 0 < EFun X x y z w) {ζ η : Fin n → ℂ}
    (h1 : EFunC S ζ η = 0) (h2 : EFunC (Iso n) ζ η ≠ 0) : 0 < EFunC X ζ η :=
  hstrict (cRe ζ) (cIm ζ) (cRe η) (cIm η) h1 h2

/-! ## Continuity -/

theorem ChatT_continuous_EFunC (R : Curv4 n) :
    Continuous (fun p : (Fin n → ℂ) × (Fin n → ℂ) => EFunC R p.1 p.2) := by
  unfold EFunC cRe cIm EFun Submission.Diff.Alg.R4
  fun_prop

theorem ChatT_continuous_cNSq :
    Continuous (fun p : (Fin n → ℂ) × (Fin n → ℂ) => cNSq p.1) := by
  unfold cNSq
  fun_prop

theorem ChatT_continuous_cNSq' :
    Continuous (fun p : (Fin n → ℂ) × (Fin n → ℂ) => cNSq p.2) := by
  unfold cNSq
  fun_prop

theorem ChatT_continuous_cHerm :
    Continuous (fun p : (Fin n → ℂ) × (Fin n → ℂ) => cHerm p.1 p.2) := by
  unfold cHerm
  fun_prop

/-! ## The compact set of orthonormal complex `2`-frames -/

/-- The set of pairs of complex vectors whose real-and-imaginary parts split into two orthonormal
`2`-frames: equivalently `cHerm`-orthonormal pairs. -/
def ChatT_K (n : ℕ) : Set ((Fin n → ℂ) × (Fin n → ℂ)) :=
  {p | cNSq p.1 = 1 ∧ cNSq p.2 = 1 ∧ cHerm p.1 p.2 = 0}

theorem ChatT_K_compact (n : ℕ) : IsCompact (ChatT_K n) := by
  have hclosed : IsClosed (ChatT_K n) := by
    have h : ChatT_K n = (fun p : (Fin n → ℂ) × (Fin n → ℂ) =>
        (cNSq p.1, cNSq p.2, cHerm p.1 p.2)) ⁻¹' {((1 : ℝ), 1, 0)} := by
      ext p
      simp [ChatT_K]
    rw [h]
    exact IsClosed.preimage
      ((ChatT_continuous_cNSq.prodMk (ChatT_continuous_cNSq'.prodMk ChatT_continuous_cHerm)))
      isClosed_singleton
  refine (isCompact_univ_pi (fun _ : Fin n => isCompact_closedBall (0 : ℂ) 1)).prod
    (isCompact_univ_pi (fun _ : Fin n => isCompact_closedBall (0 : ℂ) 1)) |>.of_isClosed_subset
      hclosed ?_
  rintro p ⟨h1, h2, h3⟩
  have bound : ∀ (u : Fin n → ℂ), cNSq u = 1 → ∀ i, u i ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro u hu i
    rw [Metric.mem_closedBall, dist_zero_right]
    have hle : Complex.normSq (u i) ≤ 1 := by
      have := Finset.single_le_sum (f := fun j => Complex.normSq (u j)) (s := Finset.univ)
        (fun j _ => Complex.normSq_nonneg (u j)) (Finset.mem_univ i)
      rw [cNSq] at hu
      linarith [hu ▸ this]
    have h2 : ‖u i‖ ^ 2 ≤ 1 := by rw [← Complex.normSq_eq_norm_sq]; exact hle
    nlinarith [norm_nonneg (u i)]
  exact ⟨Set.mem_pi.mpr (fun i _ => bound p.1 h1 i), Set.mem_pi.mpr (fun i _ => bound p.2 h2 i)⟩

theorem ChatT_K_nonempty {n : ℕ} (hn : 2 ≤ n) : (ChatT_K n).Nonempty := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  refine ⟨(fun j => if j = i0 then (1 : ℂ) else 0, fun j => if j = i1 then (1 : ℂ) else 0),
    ?_, ?_, ?_⟩
  · show (∑ j, Complex.normSq (if j = i0 then (1 : ℂ) else 0)) = 1
    rw [Finset.sum_eq_single i0]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ i0) h
  · show (∑ j, Complex.normSq (if j = i1 then (1 : ℂ) else 0)) = 1
    rw [Finset.sum_eq_single i1]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ i1) h
  · show (∑ i, (if i = i0 then (1 : ℂ) else 0) * star (if i = i1 then (1 : ℂ) else 0)) = 0
    refine Finset.sum_eq_zero (fun i _ => ?_)
    by_cases hi : i = i0
    · subst hi; simp [h01]
    · simp [hi]

theorem ChatT_K_isZeroFree {n : ℕ} {p : (Fin n → ℂ) × (Fin n → ℂ)} (hp : p ∈ ChatT_K n) :
    EFunC (Iso n) p.1 p.2 = 1 :=
  ChatT_EFunC_iso_eq_one hp.1 hp.2.1 hp.2.2


/-! ## The complexification of a real four-tuple -/

/-- The complex vector `x + iy` attached to a pair of real vectors. -/
noncomputable def ChatT_cvec (x y : Fin n → ℝ) : Fin n → ℂ :=
  fun i => (x i : ℂ) + (y i : ℂ) * Complex.I

@[simp] theorem ChatT_cRe_cvec (x y : Fin n → ℝ) : cRe (ChatT_cvec x y) = x := by
  ext i; simp [ChatT_cvec, cRe]

@[simp] theorem ChatT_cIm_cvec (x y : Fin n → ℝ) : cIm (ChatT_cvec x y) = y := by
  ext i; simp [ChatT_cvec, cIm]

theorem ChatT_EFunC_cvec (R : Curv4 n) (x y z w : Fin n → ℝ) :
    EFunC R (ChatT_cvec x y) (ChatT_cvec z w) = EFun R x y z w := by
  simp only [EFunC, ChatT_cRe_cvec, ChatT_cIm_cvec]

/-! ## Invariance and scaling of `EFunC` -/

/-- `EFunC` does not change when a complex multiple of the first vector is subtracted from the
second (the unipotent matrix `[[1,0],[-c,1]]` of `q2p_transform`). -/
theorem ChatT_EFunC_sub_smul (R : Curv4 n) (hR : IsAlgCurv R) (ζ η : Fin n → ℂ) (c : ℂ) :
    EFunC R ζ (η - c • ζ) = EFunC R ζ η := by
  have h := Work.Diff.Alg.q2p_transform R hR ζ η 1 0 (-c) 1
  rw [Work.Diff.Alg.comb_eq_smul_add, Work.Diff.Alg.comb_eq_smul_add] at h
  have h1 : (1 : ℂ) • ζ + (0 : ℂ) • η = ζ := by simp
  have h2 : (-c) • ζ + (1 : ℂ) • η = η - c • ζ := by rw [neg_smul, one_smul]; abel
  rw [h1, h2] at h
  simpa using h

/-- Scaling the two arguments of `EFunC` by complex numbers scales it by the square of the
modulus of the determinant (the diagonal matrix of `q2p_transform`). -/
theorem ChatT_EFunC_smul_smul (R : Curv4 n) (hR : IsAlgCurv R) (ζ η : Fin n → ℂ) (a d : ℂ) :
    EFunC R (a • ζ) (d • η) = Complex.normSq (a * d) * EFunC R ζ η := by
  have h := Work.Diff.Alg.q2p_transform R hR ζ η a 0 0 d
  rw [Work.Diff.Alg.comb_eq_smul_add, Work.Diff.Alg.comb_eq_smul_add] at h
  simpa using h

/-- Scaling the two arguments by real square roots. -/
theorem ChatT_EFunC_sqrt_smul (R : Curv4 n) (hR : IsAlgCurv R) (u v : Fin n → ℂ)
    {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    EFunC R ((Real.sqrt t : ℂ) • u) ((Real.sqrt t' : ℂ) • v) = t * t' * EFunC R u v := by
  rw [ChatT_EFunC_smul_smul R hR u v (Real.sqrt t) (Real.sqrt t'), ← Complex.ofReal_mul,
    Complex.normSq_ofReal]
  have hsq : Real.sqrt t * Real.sqrt t' * (Real.sqrt t * Real.sqrt t') = t * t' := by
    rw [show Real.sqrt t * Real.sqrt t' * (Real.sqrt t * Real.sqrt t')
        = (Real.sqrt t * Real.sqrt t) * (Real.sqrt t' * Real.sqrt t') from by ring,
      Real.mul_self_sqrt ht, Real.mul_self_sqrt ht']
  rw [hsq]

theorem ChatT_EFunC_zero_left (R : Curv4 n) (η : Fin n → ℂ) : EFunC R 0 η = 0 := by
  simp [EFunC, EFun, Submission.Diff.Alg.R4, cRe, cIm]

theorem ChatT_EFunC_zero_right (R : Curv4 n) (ζ : Fin n → ℂ) : EFunC R ζ 0 = 0 := by
  simp [EFunC, EFun, Submission.Diff.Alg.R4, cRe, cIm]

/-- Linearity of `EFun` in the tensor argument. -/
theorem ChatT_EFun_lin (A B C : Curv4 n) (s d : ℝ) (x y z w : Fin n → ℝ) :
    EFun (A + s • B - d • C) x y z w
      = EFun A x y z w + s * EFun B x y z w - d * EFun C x y z w := by
  have h1 : A + s • B - d • C = A + (s • B + (-d) • C) := by
    ext i j k l
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h2 : EFun (A + (s • B + (-d) • C)) x y z w
      = EFun A x y z w + EFun (s • B + (-d) • C) x y z w :=
    Cone.EF_add A (s • B + (-d) • C) x y z w
  have h3 : EFun (s • B + (-d) • C) x y z w
      = EFun (s • B) x y z w + EFun ((-d) • C) x y z w :=
    Cone.EF_add (s • B) ((-d) • C) x y z w
  have h4 : EFun (s • B) x y z w = s * EFun B x y z w := Cone.EF_smul s B x y z w
  have h5 : EFun ((-d) • C) x y z w = (-d) * EFun C x y z w := Cone.EF_smul (-d) C x y z w
  rw [h1, h2, h3, h4, h5]
  ring

/-- Linearity of `EFunC` in the tensor argument. -/
theorem ChatT_EFunC_lin (A B C : Curv4 n) (s d : ℝ) (ζ η : Fin n → ℂ) :
    EFunC (A + s • B - d • C) ζ η
      = EFunC A ζ η + s * EFunC B ζ η - d * EFunC C ζ η := by
  simp only [EFunC]
  exact ChatT_EFun_lin A B C s d (cRe ζ) (cIm ζ) (cRe η) (cIm η)

/-! ## The round sphere as an algebraic curvature tensor -/

theorem ChatT_iso_isAlgCurv (n : ℕ) : IsAlgCurv (Iso n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j k l
    simp only [Iso]
    by_cases h1 : i = k <;> by_cases h2 : i = l <;> by_cases h3 : j = k <;>
      by_cases h4 : j = l <;> by_cases h5 : i = j <;> by_cases h6 : k = l <;>
      simp_all [eq_comm]
  · intro i j k l
    simp only [Iso]
    by_cases h1 : i = k <;> by_cases h2 : i = l <;> by_cases h3 : j = k <;>
      by_cases h4 : j = l <;> by_cases h5 : i = j <;> by_cases h6 : k = l <;>
      simp_all [eq_comm]
  · intro i j k l
    simp only [Iso]
    by_cases h1 : i = k <;> by_cases h2 : i = l <;> by_cases h3 : j = k <;>
      by_cases h4 : j = l <;> by_cases h5 : i = j <;> by_cases h6 : k = l <;>
      simp_all [eq_comm]

/-! ## Projection and normalisation of a complex pair -/

theorem ChatT_cNSq_pos {ζ : Fin n → ℂ} : 0 < cNSq ζ ↔ ζ ≠ 0 := by
  constructor
  · intro h hz; rw [hz, cNSq] at h; simp at h
  · intro hz
    refine lt_of_le_of_ne (cNSq_nonneg ζ) ?_
    exact fun h => hz (cNSq_eq_zero.mp h.symm)

/-- Subtracting from `η` its `cHerm`-projection on `ζ` makes the pair orthogonal. -/
theorem ChatT_cHerm_proj {ζ η : Fin n → ℂ} (hζ : cHerm ζ ζ ≠ 0) :
    cHerm (η - (cHerm η ζ / cHerm ζ ζ) • ζ) ζ = 0 := by
  rw [cHerm_sub₁, cHerm_smul₁, div_mul_cancel₀ _ hζ, sub_self]

/-- A `cHerm`-orthogonal pair of nonzero vectors can be rescaled (by real multiples) to a pair on
the compact set `ChatT_K`. -/
theorem ChatT_normalize {ζ η : Fin n → ℂ} (hζ : ζ ≠ 0) (hη : η ≠ 0)
    (horth : cHerm ζ η = 0) :
    ∃ (t t' : ℝ) (u v : Fin n → ℂ), 0 < t ∧ 0 < t' ∧ cNSq u = 1 ∧ cNSq v = 1 ∧
      cHerm u v = 0 ∧ ζ = (Real.sqrt t : ℂ) • u ∧ η = (Real.sqrt t' : ℂ) • v := by
  have ht : 0 < cNSq ζ := ChatT_cNSq_pos.mpr hζ
  have ht' : 0 < cNSq η := ChatT_cNSq_pos.mpr hη
  have hst : Real.sqrt (cNSq ζ) ≠ 0 := Real.sqrt_ne_zero'.mpr ht
  have hst' : Real.sqrt (cNSq η) ≠ 0 := Real.sqrt_ne_zero'.mpr ht'
  refine ⟨cNSq ζ, cNSq η, (((Real.sqrt (cNSq ζ))⁻¹ : ℝ) : ℂ) • ζ,
    (((Real.sqrt (cNSq η))⁻¹ : ℝ) : ℂ) • η, ht, ht', ?_, ?_, ?_, ?_, ?_⟩
  · rw [ChatT_cNSq_ofReal_smul]
    have : ((Real.sqrt (cNSq ζ))⁻¹) ^ 2 = (cNSq ζ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt ht.le]
    rw [this, inv_mul_cancel₀ (ne_of_gt ht)]
  · rw [ChatT_cNSq_ofReal_smul]
    have : ((Real.sqrt (cNSq η))⁻¹) ^ 2 = (cNSq η)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt ht'.le]
    rw [this, inv_mul_cancel₀ (ne_of_gt ht')]
  · rw [cHerm_smul₁, cHerm_smul₂]
    have hs : ((((Real.sqrt (cNSq η))⁻¹ : ℝ)) : ℂ)
        = star ((((Real.sqrt (cNSq η))⁻¹ : ℝ)) : ℂ) := by
      simp [Complex.star_def, Complex.conj_ofReal]
    rw [hs, horth, mul_zero, mul_zero]
  · ext i
    have h1 : (Real.sqrt (cNSq ζ) : ℂ) * (((Real.sqrt (cNSq ζ))⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hst, Complex.ofReal_one]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, h1, one_mul]
  · ext i
    have h1 : (Real.sqrt (cNSq η) : ℂ) * (((Real.sqrt (cNSq η))⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hst', Complex.ofReal_one]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, h1, one_mul]

/-! ## The compact margin lemma -/

/-- If `A ≥ 0` on a compact set `K` and `B > 0` at every zero of `A`, then for all small `s > 0`
the function `A + s * B` has a positive lower bound on `K`. -/
theorem ChatT_compact_eps_delta {X : Type*} [MetricSpace X] {K : Set X} (hK : IsCompact K)
    {A B : X → ℝ} (hAc : ContinuousOn A K) (hBc : ContinuousOn B K)
    (hA : ∀ x ∈ K, 0 ≤ A x) (hAB : ∀ x ∈ K, A x = 0 → 0 < B x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s ≤ ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ A x + s * B x := by
  by_cases hKne : K.Nonempty
  · have hpt : ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s ≤ ε → ∀ x ∈ K, 0 < A x + s * B x := by
      by_cases hWne : (K ∩ {x | B x ≤ 0}).Nonempty
      · have hWclosed : IsClosed (K ∩ {x | B x ≤ 0}) := by
          have h := hBc.preimage_isClosed_of_isClosed hK.isClosed
            (isClosed_Iic : IsClosed (Set.Iic (0 : ℝ)))
          convert h using 1
          ext x; simp
        have hWc : IsCompact (K ∩ {x | B x ≤ 0}) :=
          hK.of_isClosed_subset hWclosed Set.inter_subset_left
        obtain ⟨x₀, hx₀, hx₀min⟩ := hWc.exists_isMinOn hWne (hAc.mono Set.inter_subset_left)
        obtain ⟨y₀, hy₀, hy₀max⟩ := hWc.exists_isMaxOn hWne ((hBc.neg).mono Set.inter_subset_left)
        have hx₀B : B x₀ ≤ 0 := hx₀.2
        have hy₀B : B y₀ ≤ 0 := hy₀.2
        have hx₀A : 0 < A x₀ := by
          rcases lt_or_eq_of_le (hA x₀ hx₀.1) with h | h
          · exact h
          · exact absurd hx₀B (not_le.mpr (hAB x₀ hx₀.1 h.symm))
        have hM : 0 ≤ -B y₀ := by linarith
        refine ⟨A x₀ / (2 * (1 + -B y₀)), div_pos hx₀A (by linarith), fun s hs hse x hx => ?_⟩
        by_cases hxW : B x ≤ 0
        · have h1 : A x₀ ≤ A x := isMinOn_iff.mp hx₀min x ⟨hx, hxW⟩
          have h2 : -B x ≤ -B y₀ := isMaxOn_iff.mp hy₀max x ⟨hx, hxW⟩
          have h3 : s * -B x ≤ s * -B y₀ := mul_le_mul_of_nonneg_left h2 hs.le
          have h4 : s * -B y₀ ≤ (A x₀ / (2 * (1 + -B y₀))) * (-B y₀) :=
            mul_le_mul_of_nonneg_right hse hM
          have h5 : (A x₀ / (2 * (1 + -B y₀))) * (-B y₀) ≤ A x₀ / 2 := by
            rw [div_mul_eq_mul_div]
            rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 2 * (1 + -B y₀)) (by norm_num : (0 : ℝ) < 2)]
            nlinarith [hM, hx₀A]
          have h6 : A x + s * B x = A x - s * (-B x) := by ring
          rw [h6]
          linarith
        · have hBx : 0 < B x := not_le.mp hxW
          have hAx : 0 ≤ A x := hA x hx
          nlinarith [mul_pos hs hBx]
      · refine ⟨1, one_pos, fun s hs hse x hx => ?_⟩
        have hBx : 0 < B x := not_le.mp (fun h => hWne ⟨x, hx, h⟩)
        have hAx : 0 ≤ A x := hA x hx
        nlinarith [mul_pos hs hBx]
    obtain ⟨ε, hε0, hε⟩ := hpt
    refine ⟨ε, hε0, fun s hs hse => ?_⟩
    obtain ⟨z, hzK, hzmin⟩ := hK.exists_isMinOn hKne (hAc.add (hBc.const_mul s))
    exact ⟨A z + s * B z, hε s hs hse z hzK,
      fun x hx => isMinOn_iff.mp hzmin x hx⟩
  · exact ⟨1, one_pos, fun s hs hse => ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hKne⟩⟩

end Work.Diff.Alg.Pinch
