import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.Coercivity.CTDefs
import Submission.Work.Coercivity.EcommT_split
import Submission.Work.Coercivity.angRad_mixed
import Submission.Work.Coercivity.rpow_neg_sq
import Submission.Work.Coercivity.mixed_sep2
import Submission.Work.Coercivity.L12f_contDiffOn_infty
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Elementary helpers -/

/-- `sin(2θ) > 0` on the open angular interval. -/
lemma sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
    (by linarith [hθ.2, Real.pi_pos])

/-- `Γ(θ) = (sinθ cos²θ)^{α/3}` is `C^∞` on `(0,π/2)`. -/
lemma contDiffOn_Gam (α : ℝ) : ContDiffOn ℝ ⊤ (Spaces.Gam α) (Set.Ioo 0 (π / 2)) := by
  unfold Spaces.Gam
  apply ContDiffOn.rpow
  · fun_prop
  · fun_prop
  · intro θ hθ
    have hs : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hc : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos],
        by linarith [hθ.2, Real.pi_pos]⟩
    positivity

/-- `D_θ^{i+j} = D_θ^i ∘ D_θ^j` on functions of the angle alone. -/
lemma DthIterAng_comp (g : ℝ → ℝ) (i j : ℕ) :
    CT.DthIterAng i (CT.DthIterAng j g) = CT.DthIterAng (i + j) g := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [CT.DthIterAng_succ, ih, show i + 1 + j = (i + j) + 1 by ring, CT.DthIterAng_succ]

/-- `D_θΓ` agrees whether computed from the lifted angular profile or the raw `Γ`. -/
lemma DthGamF_eq_DthIterAng (α z θ : ℝ) :
    CT.DthGamF α z θ = CT.DthIterAng 1 (Spaces.Gam α) θ := by
  rw [CT.DthGamF_apply, CT.DthIterAng_succ]
  simp [CT.DthIterAng_zero]

/-- `(A · (W / s^{e/2}))² = A² W² s^{-e}` for `s ≥ 0`. -/
lemma div_weight_sq {A W s e : ℝ} (hs : 0 ≤ s) :
    (A * (W / s ^ (e / 2))) ^ 2 = A ^ 2 * W ^ 2 * s ^ (-e) := by
  have h : (s ^ (-(e / 2))) ^ 2 = s ^ (-e) := rpow_neg_sq s e hs
  rw [div_eq_mul_inv, ← Real.rpow_neg hs (e / 2)]
  calc (A * (W * s ^ (-(e / 2)))) ^ 2 = A ^ 2 * W ^ 2 * (s ^ (-(e / 2))) ^ 2 := by ring
    _ = A ^ 2 * W ^ 2 * s ^ (-e) := by rw [h]

/-- `(A · (W · s^{-e/2}))² = A² W² s^{-e}` for `s ≥ 0`. -/
lemma mul_weight_sq {A W s e : ℝ} (hs : 0 ≤ s) :
    (A * (W * s ^ (-(e / 2)))) ^ 2 = A ^ 2 * W ^ 2 * s ^ (-e) := by
  have h : (s ^ (-(e / 2))) ^ 2 = s ^ (-e) := rpow_neg_sq s e hs
  calc (A * (W * s ^ (-(e / 2)))) ^ 2 = A ^ 2 * W ^ 2 * (s ^ (-(e / 2))) ^ 2 := by ring
    _ = A ^ 2 * W ^ 2 * s ^ (-e) := by rw [h]

/-- The iterates of `D_z = z ∂_z` of a `C^∞` function on `(0,∞)` are again `C^∞`. -/
theorem DzRIter_contDiffOn (R : ℝ → ℝ) (hR : ContDiffOn ℝ ∞ R (Set.Ioi 0)) :
    ∀ k : ℕ, ContDiffOn ℝ ∞ (CT.DzRIter k R) (Set.Ioi 0) := by
  intro k
  induction k with
  | zero => simpa using hR
  | succ n ih =>
      have hd : ContDiffOn ℝ ∞ (deriv (CT.DzRIter n R)) (Set.Ioi 0) :=
        (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).1 ih |>.2
      have hfun : CT.DzRIter (n + 1) R = fun z => z * deriv (CT.DzRIter n R) z := by
        rw [CT.DzRIter_succ]; rfl
      rw [hfun]
      exact contDiffOn_id.mul hd

/-! ## Transfer of iterated derivatives across a local equality -/

theorem DzIter_eqOn_congr (A B : ℝ → ℝ → ℝ)
    (hAB : ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → A z θ = B z θ) :
    ∀ i z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Spaces.DzIter i A z θ = Spaces.DzIter i B z θ := by
  intro i
  induction i with
  | zero => intro z θ hz hθ; exact hAB z θ hz hθ
  | succ n ih =>
    intro z θ hz hθ
    show z * deriv (fun z' => Spaces.DzIter n A z' θ) z
        = z * deriv (fun z' => Spaces.DzIter n B z' θ) z
    congr 1
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact ih z' θ hz' hθ

theorem DthIter_eqOn_congr (A B : ℝ → ℝ → ℝ)
    (hAB : ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → A z θ = B z θ) :
    ∀ i z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Spaces.DthIter i A z θ = Spaces.DthIter i B z θ := by
  intro i
  induction i with
  | zero => intro z θ hz hθ; exact hAB z θ hz hθ
  | succ n ih =>
    intro z θ hz hθ
    show Real.sin (2 * θ) * deriv (fun θ' => Spaces.DthIter n A z θ') θ
        = Real.sin (2 * θ) * deriv (fun θ' => Spaces.DthIter n B z θ') θ
    congr 1
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact ih z θ' hz hθ'

/-! ## The algebraic core -/

/-- The pointwise bound of `HkIntegrand α n` of the separated function
`(z,θ) ↦ Γ(θ)R₁(z) + D_θΓ(θ)R₂(z)` by `Bound`.  Each summand is bounded by
`(a+b)² ≤ 2a²+2b²` and the weight identities `(w/s^{η/2})² = w² s^{-η}`,
`Wt² = w² s^{-γ}`. -/
theorem HkIntegrand_sep2_le_Bound (α : ℝ) (n : ℕ) (R1 R2 : ℝ → ℝ)
    (hR1 : ContDiffOn ℝ ∞ R1 (Set.Ioi 0)) (hR2 : ContDiffOn ℝ ∞ R2 (Set.Ioi 0)) :
    ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Spaces.HkIntegrand α n
        (fun z θ => CT.DthIterAng 0 (Spaces.Gam α) θ * R1 z
          + CT.DthIterAng 1 (Spaces.Gam α) θ * R2 z) z θ
        ≤ CT.Bound α n R1 R2 z θ := by
  intro z θ hz hθ
  have hsin : 0 ≤ Real.sin (2 * θ) := le_of_lt (sin_two_pos_of_mem_Ioo hθ)
  have hgm : ContDiffOn ℝ ⊤ (Spaces.Gam α) (Set.Ioo 0 (π / 2)) := contDiffOn_Gam α
  have hg1 : ContDiffOn ℝ ⊤ (CT.DthIterAng 0 (Spaces.Gam α)) (Set.Ioo 0 (π / 2)) := hgm
  have hg2 : ContDiffOn ℝ ⊤ (CT.DthIterAng 1 (Spaces.Gam α)) (Set.Ioo 0 (π / 2)) :=
    DthIterAng_contDiffOn_Ioo (Spaces.Gam α) hgm 1
  have hdR1 : ∀ k ≤ n, ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (CT.DzRIter k R1) z :=
    fun k _ z hz => ((DzRIter_contDiffOn R1 hR1 k).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  have hdR2 : ∀ k ≤ n, ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (CT.DzRIter k R2) z :=
    fun k _ z hz => ((DzRIter_contDiffOn R2 hR2 k).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  rw [Spaces.HkIntegrand, CT.Bound]
  apply add_le_add
  · -- pure `D_z` sum
    apply Finset.sum_le_sum
    intro i hi
    have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hmix := mixed_sep2 (CT.DthIterAng 0 (Spaces.Gam α)) (CT.DthIterAng 1 (Spaces.Gam α))
      R1 R2 i 0 hg1 hg2
      (fun k hk z hz => hdR1 k (le_trans hk hi_le) z hz)
      (fun k hk z hz => hdR2 k (le_trans hk hi_le) z hz) z θ hz hθ
    have hDz : Spaces.DzIter i
        (fun z θ => CT.DthIterAng 0 (Spaces.Gam α) θ * R1 z
          + CT.DthIterAng 1 (Spaces.Gam α) θ * R2 z) z θ
        = Spaces.Gam α θ * CT.DzRIter i R1 z
          + CT.DthIterAng 1 (Spaces.Gam α) θ * CT.DzRIter i R2 z := by
      rw [← Spaces.mixed_zero_right i _]
      simpa using hmix
    rw [hDz]
    have key1 : (Spaces.Gam α θ * CT.DzRIter i R1 z
          * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) ^ 2
        = (Spaces.Gam α θ * CT.DzRIter i R1 z) ^ 2 * (Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.eta) :=
      div_weight_sq (A := Spaces.Gam α θ * CT.DzRIter i R1 z) (W := Spaces.w z)
        (s := Real.sin (2 * θ)) (e := Spaces.eta) hsin
    have key2 : (CT.DthIterAng 1 (Spaces.Gam α) θ * CT.DzRIter i R2 z
          * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) ^ 2
        = (CT.DthIterAng 1 (Spaces.Gam α) θ * CT.DzRIter i R2 z) ^ 2 * (Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.eta) :=
      div_weight_sq (A := CT.DthIterAng 1 (Spaces.Gam α) θ * CT.DzRIter i R2 z)
        (W := Spaces.w z) (s := Real.sin (2 * θ)) (e := Spaces.eta) hsin
    calc ((Spaces.Gam α θ * CT.DzRIter i R1 z
            + CT.DthIterAng 1 (Spaces.Gam α) θ * CT.DzRIter i R2 z)
          * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) ^ 2
        = ((Spaces.Gam α θ * CT.DzRIter i R1 z)
              * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))
            + (CT.DthIterAng 1 (Spaces.Gam α) θ * CT.DzRIter i R2 z)
              * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) ^ 2 := by ring
      _ ≤ 2 * (((Spaces.Gam α θ * CT.DzRIter i R1 z)
              * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) ^ 2
            + ((CT.DthIterAng 1 (Spaces.Gam α) θ * CT.DzRIter i R2 z)
              * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) ^ 2) := add_sq_le
      _ = 2 * ((Spaces.Gam α θ) ^ 2 * (CT.DzRIter i R1 z) ^ 2
              * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
            + (CT.DthIterAng 1 (Spaces.Gam α) θ) ^ 2 * (CT.DzRIter i R2 z) ^ 2
              * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
            rw [key1, key2]; ring
      _ = 2 * ((CT.DthIterAng 0 (Spaces.Gam α) θ) ^ 2 * (CT.DzRIter i R1 z) ^ 2
              + (CT.DthIterAng 1 (Spaces.Gam α) θ) ^ 2 * (CT.DzRIter i R2 z) ^ 2)
            * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
            simp only [CT.DthIterAng_zero]; ring
  · -- mixed sum
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hj_le : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    by_cases hc : 1 ≤ i ∧ i + j ≤ n
    · simp only [if_pos hc]
      have hmix := mixed_sep2 (CT.DthIterAng 0 (Spaces.Gam α)) (CT.DthIterAng 1 (Spaces.Gam α))
        R1 R2 j i hg1 hg2
        (fun k hk z hz => hdR1 k (le_trans hk hj_le) z hz)
        (fun k hk z hz => hdR2 k (le_trans hk hj_le) z hz) z θ hz hθ
      have hmix' : Spaces.mixed j i
          (fun z θ => CT.DthIterAng 0 (Spaces.Gam α) θ * R1 z
            + CT.DthIterAng 1 (Spaces.Gam α) θ * R2 z) z θ
          = CT.DthIterAng i (Spaces.Gam α) θ * CT.DzRIter j R1 z
            + CT.DthIterAng (i + 1) (Spaces.Gam α) θ * CT.DzRIter j R2 z := by
        rw [hmix, DthIterAng_comp (Spaces.Gam α) i 1]
        simp
      rw [hmix']
      have keyA : (CT.DthIterAng i (Spaces.Gam α) θ * CT.DzRIter j R1 z
            * Spaces.Wt α z θ) ^ 2
          = (CT.DthIterAng i (Spaces.Gam α) θ * CT.DzRIter j R1 z) ^ 2
            * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
        simp only [Spaces.Wt, Spaces.wTheta]
        exact mul_weight_sq (A := CT.DthIterAng i (Spaces.Gam α) θ * CT.DzRIter j R1 z)
          (W := Spaces.w z) (s := Real.sin (2 * θ)) (e := Spaces.gam α) hsin
      have keyB : (CT.DthIterAng (i + 1) (Spaces.Gam α) θ * CT.DzRIter j R2 z
            * Spaces.Wt α z θ) ^ 2
          = (CT.DthIterAng (i + 1) (Spaces.Gam α) θ * CT.DzRIter j R2 z) ^ 2
            * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
        simp only [Spaces.Wt, Spaces.wTheta]
        exact mul_weight_sq (A := CT.DthIterAng (i + 1) (Spaces.Gam α) θ * CT.DzRIter j R2 z)
          (W := Spaces.w z) (s := Real.sin (2 * θ)) (e := Spaces.gam α) hsin
      calc ((CT.DthIterAng i (Spaces.Gam α) θ * CT.DzRIter j R1 z
              + CT.DthIterAng (i + 1) (Spaces.Gam α) θ * CT.DzRIter j R2 z)
            * Spaces.Wt α z θ) ^ 2
          = ((CT.DthIterAng i (Spaces.Gam α) θ * CT.DzRIter j R1 z) * Spaces.Wt α z θ
              + (CT.DthIterAng (i + 1) (Spaces.Gam α) θ * CT.DzRIter j R2 z)
                * Spaces.Wt α z θ) ^ 2 := by ring
        _ ≤ 2 * (((CT.DthIterAng i (Spaces.Gam α) θ * CT.DzRIter j R1 z)
                * Spaces.Wt α z θ) ^ 2
              + ((CT.DthIterAng (i + 1) (Spaces.Gam α) θ * CT.DzRIter j R2 z)
                * Spaces.Wt α z θ) ^ 2) := add_sq_le
        _ = 2 * ((CT.DthIterAng i (Spaces.Gam α) θ) ^ 2 * (CT.DzRIter j R1 z) ^ 2
                * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
              + (CT.DthIterAng (i + 1) (Spaces.Gam α) θ) ^ 2 * (CT.DzRIter j R2 z) ^ 2
                * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) := by
              rw [keyA, keyB]; ring
        _ = 2 * ((CT.DthIterAng i (Spaces.Gam α) θ) ^ 2 * (CT.DzRIter j R1 z) ^ 2
              + (CT.DthIterAng (i + 1) (Spaces.Gam α) θ) ^ 2 * (CT.DzRIter j R2 z) ^ 2)
            * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by ring
    · simp only [if_neg hc, le_refl]

/-! ## `C^∞`-regularity of the radial factors and the main theorem -/

/-- The coefficient `2z/(c(1+z)²)` is `C^∞` on `(0,∞)`. -/
theorem pcoef_contDiffOn_infty (α : ℝ) : ContDiffOn ℝ ∞ (CT.pcoef α) (Set.Ioi 0) := by
  rcases eq_or_ne (Spaces.c α) 0 with hc | hc
  · have h0 : CT.pcoef α = fun _ : ℝ => (0 : ℝ) := by
      funext z
      simp [CT.pcoef, hc]
    rw [h0]
    exact contDiffOn_const
  · have h1 : ContDiffOn ℝ ∞ (fun z : ℝ => 2 * z) (Set.Ioi 0) := by fun_prop
    have h2 : ContDiffOn ℝ ∞ (fun z : ℝ => Spaces.c α * (1 + z) ^ 2) (Set.Ioi 0) := by
      fun_prop
    have h3 : ∀ z ∈ Set.Ioi (0 : ℝ), Spaces.c α * (1 + z) ^ 2 ≠ 0 := by
      intro z hz
      exact mul_ne_zero hc (pow_ne_zero 2 (by have : (0:ℝ) < z := hz; linarith))
    have h := ContDiffOn.div h1 h2 h3
    refine h.congr (fun z _ => ?_)
    simp only [CT.pcoef, Pi.div_apply]

/-- The coefficient `2z²/(c(1+z)³)` is `C^∞` on `(0,∞)`. -/
theorem Wcoef_contDiffOn_infty (α : ℝ) : ContDiffOn ℝ ∞ (CT.Wcoef α) (Set.Ioi 0) := by
  rcases eq_or_ne (Spaces.c α) 0 with hc | hc
  · have h0 : CT.Wcoef α = fun _ : ℝ => (0 : ℝ) := by
      funext z
      simp [CT.Wcoef, hc]
    rw [h0]
    exact contDiffOn_const
  · have h1 : ContDiffOn ℝ ∞ (fun z : ℝ => 2 * z ^ 2) (Set.Ioi 0) := by fun_prop
    have h2 : ContDiffOn ℝ ∞ (fun z : ℝ => Spaces.c α * (1 + z) ^ 3) (Set.Ioi 0) := by
      fun_prop
    have h3 : ∀ z ∈ Set.Ioi (0 : ℝ), Spaces.c α * (1 + z) ^ 3 ≠ 0 := by
      intro z hz
      exact mul_ne_zero hc (pow_ne_zero 3 (by have : (0:ℝ) < z := hz; linarith))
    have h := ContDiffOn.div h1 h2 h3
    refine h.congr (fun z _ => ?_)
    simp only [CT.Wcoef, Pi.div_apply]

/-- The radial commutator factors `F₁`, `F₂` are `C^∞` on `(0,∞)` for `f` smooth on a
neighbourhood of the closed quadrant. -/
theorem F1F2_contDiffOn_infty (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : Work.Spaces.SmoothNbhd f) :
    ContDiffOn ℝ ∞ (CT.F1 α f) (Set.Ioi 0) ∧ ContDiffOn ℝ ∞ (CT.F2 α f) (Set.Ioi 0) := by
  have hDth : Work.Spaces.SmoothNbhd (Work.Spaces.Dth f) := hf.Dth
  have hA1 : ContDiffOn ℝ ∞ (fun z => L12f (Work.Spaces.Dth f) z) (Set.Ioi 0) :=
    L12f_contDiffOn_infty (Work.Spaces.Dth f) hDth
  have hA2 : ContDiffOn ℝ ∞ (fun z => L12f f z) (Set.Ioi 0) :=
    L12f_contDiffOn_infty f hf
  have hp : ContDiffOn ℝ ∞ (CT.pcoef α) (Set.Ioi 0) := pcoef_contDiffOn_infty α
  have hW : ContDiffOn ℝ ∞ (CT.Wcoef α) (Set.Ioi 0) := Wcoef_contDiffOn_infty α
  constructor
  · have h : CT.F1 α f
        = fun z => CT.pcoef α z * CT.A1 f z - CT.Wcoef α z * CT.KC1 f := by
      funext z
      simp only [CT.F1, CT.pcoef, CT.Wcoef]
    rw [h]
    exact (hp.mul hA1).sub (hW.mul contDiffOn_const)
  · have h : CT.F2 α f
        = fun z => CT.Wcoef α z * CT.KC0 f - CT.pcoef α z * CT.A2 f z := by
      funext z
      simp only [CT.F2, CT.pcoef, CT.Wcoef]
    rw [h]
    exact (hW.mul contDiffOn_const).sub (hp.mul hA2)

theorem HkIntegrand_EcommT_le_Bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (hn : 1 ≤ n)
    (f : ℝ → ℝ → ℝ) (hf : Work.Spaces.SmoothNbhd f) :
    ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.HkIntegrand α n (Work.Coercivity.CT.EcommT α f) z θ
        ≤ Work.Coercivity.CT.Bound α n (Work.Coercivity.CT.F1 α f) (Work.Coercivity.CT.F2 α f) z θ := by
  intro z θ hz hθ
  set F : ℝ → ℝ → ℝ := fun z θ => CT.DthIterAng 0 (Spaces.Gam α) θ * CT.F1 α f z
      + CT.DthIterAng 1 (Spaces.Gam α) θ * CT.F2 α f z with hFdef
  have hsep : ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → CT.EcommT α f z θ = F z θ := by
    intro z θ hz hθ
    have h := EcommT_split α f hf z θ hz hθ
    simp only [hFdef]
    rw [h, CT.GamF_apply, DthGamF_eq_DthIterAng, CT.DthIterAng_zero]
  have hFco : ContDiffOn ℝ ∞ (CT.F1 α f) (Set.Ioi 0)
      ∧ ContDiffOn ℝ ∞ (CT.F2 α f) (Set.Ioi 0) :=
    F1F2_contDiffOn_infty α hα hα1 f hf
  have hHk_eq : Spaces.HkIntegrand α n (CT.EcommT α f) z θ
      = Spaces.HkIntegrand α n F z θ := by
    rw [Spaces.HkIntegrand, Spaces.HkIntegrand]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [DzIter_eqOn_congr (CT.EcommT α f) F hsep i z θ hz hθ]
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hc : 1 ≤ i ∧ i + j ≤ n
      · simp only [if_pos hc]
        have hDth : ∀ z' θ', 0 < z' → θ' ∈ Set.Ioo 0 (π / 2) →
            Spaces.DthIter i (CT.EcommT α f) z' θ' = Spaces.DthIter i F z' θ' :=
          DthIter_eqOn_congr (CT.EcommT α f) F hsep i
        have hmix : Spaces.mixed j i (CT.EcommT α f) z θ = Spaces.mixed j i F z θ := by
          have h2 := DzIter_eqOn_congr (Spaces.DthIter i (CT.EcommT α f))
            (Spaces.DthIter i F) hDth j z θ hz hθ
          simpa only [Spaces.mixed] using h2
        rw [hmix]
      · simp only [if_neg hc]
  rw [hHk_eq]
  exact HkIntegrand_sep2_le_Bound α n (CT.F1 α f) (CT.F2 α f) hFco.1 hFco.2 z θ hz hθ

end Work.Coercivity
