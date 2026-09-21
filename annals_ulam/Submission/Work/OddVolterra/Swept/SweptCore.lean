import Submission.Work.OddVolterra.SweptDefs
import Submission.Work.OddVolterra.Swept.Pder
import Submission.Work.OddVolterra.Swept.rpow_ident
import Submission.Work.OddVolterra.Swept.KsCalc
import Submission.Work.OddVolterra.Swept.KtCalc

/-!
# The `v`-form of the swept kernel

For `p = n + 1/2` the swept integral `∫_u^b (σ-u)^p A u σ dσ` is, after the substitution
`σ = u + (b-u)v²`, the integral over `v ∈ [0,1]` of the kernel `Gfun` below.  The point of this
form is that all powers of `v` occurring in `Gfun` are nonnegative *integers*, so that `Gfun` and
all its partial derivatives are honest smooth functions on the compact region; the singularity of
`(σ-u)^p` has been absorbed into the Jacobian `2(b-u)v`.
-/

noncomputable section

namespace Work.OddVolterra.Swept

open Work.OddVolterra
open Filter
open scoped Topology

/-- `p = n + 1/2`, the exponent of the swept kernel in the odd case. -/
def pk (n : ℕ) : ℝ := (n : ℝ) + 1/2

/-- Half the distance from `s` to the boundary of the smoothness region. -/
def ee (s b δ : ℝ) : ℝ := min (δ/2) ((b - s)/2)

/-- The neighbourhood of `s` on which the computation takes place. -/
def Uset (s b δ : ℝ) : Set ℝ := Set.Ioo (s - ee s b δ) (s + ee s b δ)

/-- The closed box on which all estimates are taken. -/
def Kset (s b δ : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc (s - ee s b δ) (s + ee s b δ) ×ˢ Set.Icc (s - ee s b δ) b

/-- The `v`-form of the swept kernel, defined with integer powers of `v`. -/
def Gfun (n : ℕ) (A : ℝ → ℝ → ℝ) (b : ℝ) (j : ℕ) (u v : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1),
    2 * lcoef j i (pk n) * (b - u) ^ (pk n - (i:ℝ) + 1) * v ^ (2*n+2-2*i) *
      pder A (j - i) u (u + (b - u) * v ^ 2)

theorem exponent_id {n i : ℕ} (hi : i ≤ n+1) :
    2 * (pk n - (i:ℝ)) + 1 = ((2*n+2-2*i : ℕ) : ℝ) := by
  have h2i : 2*i ≤ 2*n+2 := by omega
  rw [Nat.cast_sub h2i]
  simp only [pk]
  push_cast
  ring

/-- `(v^2)^z = v^(2z)` for `v ≥ 0`, kept in terms of the natural power `v^2`. -/
theorem sq_rpow_eq {v z : ℝ} (hv : 0 ≤ v) : (v^2)^z = v^(2*z) := by
  rw [show v^2 = v^(2:ℝ) from (Real.rpow_natCast v 2).symm, ← Real.rpow_mul hv 2 z]

theorem scalar_ident {n i : ℕ} (hi : i ≤ n+1) {b u v : ℝ} (hb : 0 < b - u) (hv : 0 < v) :
    (b - u) ^ (pk n - (i:ℝ) + 1) * v ^ (2*n+2-2*i)
      = v * (b - u) * ((b - u) * v ^ 2) ^ (pk n - (i:ℝ)) := by
  have h1 : (b - u) ^ (pk n - (i:ℝ) + 1) = (b - u) ^ (pk n - (i:ℝ)) * (b - u) := by
    rw [show pk n - (i:ℝ) + 1 = (pk n - (i:ℝ)) + 1 from by ring, Real.rpow_add hb, Real.rpow_one]
  have h2 : ((b - u) * v ^ 2) ^ (pk n - (i:ℝ)) =
      (b - u) ^ (pk n - (i:ℝ)) * v ^ (2*(pk n - (i:ℝ))) := by
    rw [Real.mul_rpow hb.le (sq_nonneg v), sq_rpow_eq (le_of_lt hv)]
  have h3 : v ^ (2*n+2-2*i) = v * v ^ (2*(pk n - (i:ℝ))) := by
    rw [show v ^ (2*n+2-2*i) = v ^ (((2*n+2-2*i : ℕ)) : ℝ) from (Real.rpow_natCast v _).symm]
    rw [← exponent_id hi]
    rw [show 2*(pk n - (i:ℝ)) + 1 = 1 + 2*(pk n - (i:ℝ)) from by ring, Real.rpow_add hv,
      Real.rpow_one]
  rw [h1, h2, h3]
  ring

/-- The `v`-form coincides with the shifted kernel `kt`, for `v > 0`. -/
theorem Gfun_eq_kt {n : ℕ} {A : ℝ → ℝ → ℝ} {b u v : ℝ} (hb : 0 < b - u) (hv : 0 < v)
    {j : ℕ} (hj : j ≤ n+1) :
    Gfun n A b j u v = 2 * v * (b - u) * kt A (pk n) j u ((b - u) * v ^ 2) := by
  rw [Gfun, kt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hle : i ≤ n+1 := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hj
  have h := scalar_ident hle hb hv
  calc 2 * lcoef j i (pk n) * (b - u) ^ (pk n - (i:ℝ) + 1) * v ^ (2*n+2-2*i) *
          pder A (j - i) u (u + (b - u) * v ^ 2)
      = 2 * lcoef j i (pk n) * ((b - u) ^ (pk n - (i:ℝ) + 1) * v ^ (2*n+2-2*i)) *
          pder A (j - i) u (u + (b - u) * v ^ 2) := by ring
    _ = 2 * lcoef j i (pk n) * (v * (b - u) * ((b - u) * v ^ 2) ^ (pk n - (i:ℝ))) *
          pder A (j - i) u (u + (b - u) * v ^ 2) := by rw [h]
    _ = 2 * v * (b - u) *
          (lcoef j i (pk n) * ((b - u) * v ^ 2) ^ (pk n - (i:ℝ)) *
            pder A (j - i) u (u + (b - u) * v ^ 2)) := by ring

/-- **The substitution identity**: the integral of the `v`-form over `[0,1]` is the swept
integral of the Leibniz expansion `ks`. -/
theorem integral_Gfun_eq_integral_ks {n : ℕ} {A : ℝ → ℝ → ℝ} {b u : ℝ} (hub : u < b)
    {j : ℕ} (hj : j ≤ n+1) :
    ∫ v in (0:ℝ)..1, Gfun n A b j u v = ∫ σ in u..b, ks A (pk n) j u σ := by
  have hf : ContinuousOn (fun v : ℝ => u + (b - u) * v ^ 2) (Set.uIcc (0:ℝ) 1) := by fun_prop
  have hff' : ∀ v ∈ Set.Ioo (min (0:ℝ) 1) (max (0:ℝ) 1),
      HasDerivAt (fun v : ℝ => u + (b - u) * v ^ 2) (2 * (b - u) * v) v := by
    intro v hv
    have h1 : HasDerivAt (fun v : ℝ => v ^ 2) (2 * v) v := by
      simpa using hasDerivAt_pow 2 v
    have h2 := (h1.const_mul (b - u)).const_add u
    refine h2.congr_deriv ?_
    ring
  have hf' : ∀ v ∈ Set.Ioo (min (0:ℝ) 1) (max (0:ℝ) 1), 0 ≤ 2 * (b - u) * v := by
    intro v hv
    rw [min_eq_left (by norm_num : (0:ℝ) ≤ 1), max_eq_right (by norm_num : (0:ℝ) ≤ 1)] at hv
    have hv0 : 0 < v := hv.1
    have hbu : 0 < b - u := sub_pos.mpr hub
    positivity
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun v : ℝ => u + (b - u) * v ^ 2) (f' := fun v : ℝ => 2 * (b - u) * v)
    (g := fun σ : ℝ => ks A (pk n) j u σ) (a := (0:ℝ)) (b := (1:ℝ)) hf hff' hf'
  simp only [Function.comp_apply] at hsub
  rw [show u + (b - u) * (0:ℝ)^2 = u by ring, show u + (b - u) * (1:ℝ)^2 = b by ring] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with v hv
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hv
  have hv0 : 0 < v := hv.1
  rw [Gfun_eq_kt (A := A) (b := b) (u := u) (v := v) (sub_pos.mpr hub) hv0 hj, kt_eq_ks]
  ring

/-- The `u`-derivative of the `v`-form, as a function of `(u,v)`. -/
def Gdu (n : ℕ) (A : ℝ → ℝ → ℝ) (b : ℝ) (j : ℕ) (q : ℝ × ℝ) : ℝ :=
  (fderiv ℝ (fun q : ℝ × ℝ => Gfun n A b j q.1 q.2) q) ((1:ℝ),(0:ℝ))

/-- The open rectangle on which `A` is smooth. -/
def Rset (s b δ : ℝ) : Set (ℝ × ℝ) := Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (b + δ)

/-- The open region of `(u,v)`-space on which the `v`-form is computed. -/
def Os (s b δ : ℝ) : Set (ℝ × ℝ) :=
  {q : ℝ × ℝ | q.1 ∈ Set.Ioo (s - δ) (s + δ) ∧ q.1 < b ∧
    q.1 + (b - q.1) * q.2 ^ 2 ∈ Set.Ioo (s - δ) (b + δ)}

theorem isOpen_Os (s b δ : ℝ) : IsOpen (Os s b δ) := by
  have hcont : Continuous (fun q : ℝ × ℝ => q.1 + (b - q.1) * q.2 ^ 2) := by fun_prop
  have h1 : IsOpen {q : ℝ × ℝ | q.1 ∈ Set.Ioo (s - δ) (s + δ)} :=
    isOpen_Ioo.preimage continuous_fst
  have h2 : IsOpen {q : ℝ × ℝ | q.1 < b} := isOpen_Iio.preimage continuous_fst
  have h3 : IsOpen {q : ℝ × ℝ | q.1 + (b - q.1) * q.2 ^ 2 ∈ Set.Ioo (s - δ) (b + δ)} :=
    (isOpen_Ioo (a := s - δ) (b := b + δ)).preimage hcont
  have heq : Os s b δ = {q : ℝ × ℝ | q.1 ∈ Set.Ioo (s - δ) (s + δ)} ∩
      {q : ℝ × ℝ | q.1 < b} ∩
      {q : ℝ × ℝ | q.1 + (b - q.1) * q.2 ^ 2 ∈ Set.Ioo (s - δ) (b + δ)} := by
    ext q
    simp only [Os, Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  rw [heq]
  exact (h1.inter h2).inter h3

/-- The `v`-form is smooth on `Os`. -/
theorem contDiffAt_Gfun {n j : ℕ} {s b δ : ℝ} {A : ℝ → ℝ → ℝ}
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => A q.1 q.2) (Rset s b δ)) {q : ℝ × ℝ}
    (hq : q ∈ Os s b δ) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => Gfun n A b j q.1 q.2) q := by
  have hq1 : b - q.1 ≠ 0 := ne_of_gt (sub_pos.mpr hq.2.1)
  have hmem : (q.1, q.1 + (b-q.1)*q.2^2) ∈ Rset s b δ := ⟨hq.1, hq.2.2⟩
  have hcurve : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => (q.1, q.1 + (b-q.1)*q.2^2)) q := by fun_prop
  simp only [Gfun]
  refine ContDiffAt.sum fun i hi => ?_
  have h_a : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => (b - q.1) ^ (pk n - (i:ℝ) + 1)) q := by
    have h1 : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => x ^ (pk n - (i:ℝ) + 1)) (b - q.1) :=
      Real.contDiffAt_rpow_const_of_ne hq1
    have h2 : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => b - q.1) q := by fun_prop
    simpa [Function.comp_def] using h1.comp q h2
  have h_v : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => q.2 ^ (2*n+2-2*i)) q := by fun_prop
  have h_p : ContDiffAt ℝ (↑(⊤ : ℕ∞))
      (fun q : ℝ × ℝ => pder A (j - i) q.1 (q.1 + (b-q.1)*q.2^2)) q := by
    have h1 := (contDiffOn_uncurried_pder (isOpen_Ioo.prod isOpen_Ioo) hA (j - i)).contDiffAt
      ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hmem)
    have h3 := h1.comp q hcurve
    simpa [Function.comp_def] using h3
  refine ContDiffAt.mul (ContDiffAt.mul (ContDiffAt.mul ?_ h_a) h_v) h_p
  exact contDiffAt_const

end Work.OddVolterra.Swept
