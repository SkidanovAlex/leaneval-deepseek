/-
# `FTS/GalFields/Norm/Hk5SlotTriangle` — the pointwise `ℋ^k` triangle inequality

`Work.Spaces.HkIntegrand α k h z θ` is (by definition) the sum of the squares of the *slot
vector* `hk5_slotVec α k h z θ` (the weighted `D_z`-slots indexed by `Fin (k+1)` and the mixed
slots `D_z^j D_θ^i`, `1 ≤ i`, `i + j ≤ k`, indexed by `Fin (k+1) × Fin (k+1)`).

On the open quadrant the iterated operators are additive (`SmoothOpen.DzIter_add`,
`SmoothOpen.mixed_add`), hence so is the slot vector (`hk5_slotVec_add`), and the elementary
Euclidean inequality `√(∑ᵢ(xᵢ+yᵢ)²) ≤ √(∑ᵢxᵢ²) + √(∑ᵢyᵢ²)` gives

  `√(HkIntegrand (f+g)) ≤ √(HkIntegrand f) + √(HkIntegrand g)`     (`hk5_sqrt_HkIntegrand_add_le`)

on the open quadrant.  Together with the scalar homogeneity
`√(HkIntegrand (c·h)) = |c|·√(HkIntegrand h)` and the `SmoothOpen`-closure of finite linear
combinations, this upgrades to finite sums (`hk5_sqrt_HkIntegrand_finset_sum_le`), and then to
the whole quadrant for a Galerkin combination (`hk5_sqrt_galFun_le`), the two boundary lines
`z = 0` and `sin(2θ) = 0` being handled by the exact vanishing lemmas.

Everything here is `sorry`-free.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalFields.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.LocData.HkIntegrand_const_mul
import Submission.Work.Coercivity.HkIntegrand_endpoint_zero
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Norm

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## Elementary tools -/

/-- The Euclidean inequality for two finite sums of squares:

  `√(∑ᵢ (xᵢ + yᵢ)²) ≤ √(∑ᵢ xᵢ²) + √(∑ᵢ yᵢ²)`.

It is the discrete Cauchy–Schwarz `Finset.sum_mul_sq_le_sq_mul_sq` followed by
`Real.sqrt_le_sqrt`. -/
theorem hk5_sqrt_sum_sq_add_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ) :
    Real.sqrt (∑ i ∈ s, (x i + y i) ^ 2)
      ≤ Real.sqrt (∑ i ∈ s, x i ^ 2) + Real.sqrt (∑ i ∈ s, y i ^ 2) := by
  have hA : 0 ≤ ∑ i ∈ s, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ ∑ i ∈ s, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hCS : (∑ i ∈ s, x i * y i) ^ 2 ≤ (∑ i ∈ s, x i ^ 2) * (∑ i ∈ s, y i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq s x y
  have hC : ∑ i ∈ s, x i * y i
      ≤ Real.sqrt (∑ i ∈ s, x i ^ 2) * Real.sqrt (∑ i ∈ s, y i ^ 2) := by
    refine le_trans (Real.le_sqrt_of_sq_le hCS) ?_
    rw [Real.sqrt_mul hA]
  have hsum : ∑ i ∈ s, (x i + y i) ^ 2
      = (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, x i * y i) + ∑ i ∈ s, y i ^ 2 := by
    have h1 : ∑ i ∈ s, (x i + y i) ^ 2
        = ∑ i ∈ s, (x i ^ 2 + 2 * (x i * y i) + y i ^ 2) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  have hkey : (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, x i * y i) + ∑ i ∈ s, y i ^ 2
      ≤ (Real.sqrt (∑ i ∈ s, x i ^ 2) + Real.sqrt (∑ i ∈ s, y i ^ 2)) ^ 2 := by
    have hsqA := Real.sq_sqrt hA
    have hsqB := Real.sq_sqrt hB
    nlinarith [hC, Real.sqrt_nonneg (∑ i ∈ s, x i ^ 2),
      Real.sqrt_nonneg (∑ i ∈ s, y i ^ 2)]
  rw [hsum]
  calc Real.sqrt ((∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, x i * y i) + ∑ i ∈ s, y i ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∑ i ∈ s, x i ^ 2)
          + Real.sqrt (∑ i ∈ s, y i ^ 2)) ^ 2) := Real.sqrt_le_sqrt hkey
    _ = Real.sqrt (∑ i ∈ s, x i ^ 2) + Real.sqrt (∑ i ∈ s, y i ^ 2) :=
        Real.sqrt_sq (by positivity)

/-- The square-root form of the Cauchy–Schwarz inequality on a set: for nonnegative `A`, `B`
integrable on `s`, `∫_s √A·√B ≤ √(∫_s A)·√(∫_s B)`. -/
theorem hk5_cs_sqrt_le {s : Set ℝ} {A B : ℝ → ℝ}
    (hA : IntegrableOn A s) (hB : IntegrableOn B s)
    (hAnn : ∀ x, 0 ≤ A x) (hBnn : ∀ x, 0 ≤ B x) :
    (∫ x in s, Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt (∫ x in s, A x) * Real.sqrt (∫ x in s, B x) := by
  have hu_meas : AEStronglyMeasurable (fun x => Real.sqrt (A x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have hv_meas : AEStronglyMeasurable (fun x => Real.sqrt (B x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable
  have hu_sq : Integrable (fun x => Real.sqrt (A x) ^ 2) (volume.restrict s) :=
    hA.congr (Eventually.of_forall (fun x => (Real.sq_sqrt (hAnn x)).symm))
  have hv_sq : Integrable (fun x => Real.sqrt (B x) ^ 2) (volume.restrict s) :=
    hB.congr (Eventually.of_forall (fun x => (Real.sq_sqrt (hBnn x)).symm))
  have hu_lp : MemLp (fun x => Real.sqrt (A x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hu_meas).mpr hu_sq
  have hv_lp : MemLp (fun x => Real.sqrt (B x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hv_meas).mpr hv_sq
  have hcs := Work.Spaces.cs_integral hu_lp hv_lp
  have e1 : (∫ x in s, Real.sqrt (A x) ^ 2) = ∫ x in s, A x :=
    integral_congr_ae (Eventually.of_forall fun x => Real.sq_sqrt (hAnn x))
  have e2 : (∫ x in s, Real.sqrt (B x) ^ 2) = ∫ x in s, B x :=
    integral_congr_ae (Eventually.of_forall fun x => Real.sq_sqrt (hBnn x))
  rw [e1, e2] at hcs
  calc (∫ x in s, Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt ((∫ x in s, A x) * (∫ x in s, B x)) := Real.le_sqrt_of_sq_le hcs
    _ = Real.sqrt (∫ x in s, A x) * Real.sqrt (∫ x in s, B x) :=
        Real.sqrt_mul (integral_nonneg hAnn) _

/-- `SmoothQuad` (genuine `C^∞` on `z > -1`) restricts to `SmoothOpen` (`z > 0`). -/
theorem hk5_smoothOpen_of_smoothQuad {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad f) : Work.FTS.EllipticEst.SmoothOpen f := by
  refine h.mono ?_
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
  exact ⟨by linarith, hθ0, hθ1⟩

/-- Scalar multiples of `SmoothOpen` functions are `SmoothOpen`. -/
theorem hk5_smoothOpen_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  have h : Function.uncurry (fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := by
    funext p
    rcases p with ⟨z, θ⟩
    rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact (contDiffOn_const (c := c) (s := Work.FTS.EllipticEst.Q0)).mul hf

/-! ## The slot vector of the `ℋ^k`-integrand -/

/-- The weighted `D_z`-slot of order `i`. -/
def hk5_slotZ (h : ℝ → ℝ → ℝ) (z θ : ℝ) (i : ℕ) : ℝ :=
  Work.Spaces.DzIter i h z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))

/-- The mixed slot `D_z^{p.2} D_θ^{p.1}`, set to `0` outside the range `1 ≤ i`, `i + j ≤ k`. -/
def hk5_slotM (α : ℝ) (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) (p : ℕ × ℕ) : ℝ :=
  if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
    then Work.Spaces.mixed p.2 p.1 h z θ * Work.Spaces.Wt α z θ else 0

/-- The slot vector of the `ℋ^k`-integrand. -/
def hk5_slotVec (α : ℝ) (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (Fin (k + 1) ⊕ (Fin (k + 1) × Fin (k + 1))) → ℝ
  | Sum.inl i => hk5_slotZ h z θ (i : ℕ)
  | Sum.inr p => hk5_slotM α k h z θ ((p.1 : ℕ), (p.2 : ℕ))

/-- The `ℋ^k`-integrand is the sum of the squares of the entries of the slot vector. -/
theorem hk5_HkIntegrand_eq_sum_slotVec (α : ℝ) (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k h z θ
      = ∑ x : Fin (k + 1) ⊕ (Fin (k + 1) × Fin (k + 1)), (hk5_slotVec α k h z θ x) ^ 2 := by
  rw [Work.Spaces.HkIntegrand, Fintype.sum_sum_type]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => (Work.Spaces.DzIter i h z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) (k + 1)]
    rfl
  · rw [Fintype.sum_prod_type]
    rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i h z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) (k + 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => (if 1 ≤ (i : ℕ) ∧ (i : ℕ) + j ≤ k
      then (Work.Spaces.mixed j (i : ℕ) h z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) (k + 1)]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hc : 1 ≤ (i : ℕ) ∧ (i : ℕ) + (y : ℕ) ≤ k
    · simp only [hk5_slotVec, hk5_slotM, if_pos hc]
    · simp only [hk5_slotVec, hk5_slotM, if_neg hc]
      ring

/-- On the open quadrant the slot vector of a sum is the sum of the slot vectors. -/
theorem hk5_slotVec_add (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (h1 : 0 < θ) (h2 : θ < π / 2)
    (x : Fin (k + 1) ⊕ (Fin (k + 1) × Fin (k + 1))) :
    hk5_slotVec α k (fun z θ => f z θ + g z θ) z θ x
      = hk5_slotVec α k f z θ x + hk5_slotVec α k g z θ x := by
  cases x with
  | inl i =>
      simp only [hk5_slotVec, hk5_slotZ]
      rw [Work.FTS.EllipticEst.SmoothOpen.DzIter_add hf hg (i : ℕ) z θ hz h1 h2]
      ring
  | inr p =>
      simp only [hk5_slotVec, hk5_slotM]
      by_cases hc : 1 ≤ (p.1 : ℕ) ∧ (p.1 : ℕ) + (p.2 : ℕ) ≤ k
      · simp only [if_pos hc]
        rw [Work.FTS.EllipticEst.SmoothOpen.mixed_add hf hg (p.2 : ℕ) (p.1 : ℕ) z θ hz h1 h2]
        ring
      · simp only [if_neg hc]
        ring

/-- **The pointwise triangle inequality for the `ℋ^k`-integrand** on the open quadrant. -/
theorem hk5_sqrt_HkIntegrand_add_le (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Real.sqrt (Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
        ≤ Real.sqrt (Work.Spaces.HkIntegrand α k f z θ)
          + Real.sqrt (Work.Spaces.HkIntegrand α k g z θ) := by
  intro z θ hz h1 h2
  rw [hk5_HkIntegrand_eq_sum_slotVec α k (fun z θ => f z θ + g z θ) z θ,
    hk5_HkIntegrand_eq_sum_slotVec α k f z θ,
    hk5_HkIntegrand_eq_sum_slotVec α k g z θ]
  have hsum : (∑ x : Fin (k + 1) ⊕ (Fin (k + 1) × Fin (k + 1)),
        (hk5_slotVec α k (fun z θ => f z θ + g z θ) z θ x) ^ 2)
      = ∑ x : Fin (k + 1) ⊕ (Fin (k + 1) × Fin (k + 1)),
        (hk5_slotVec α k f z θ x + hk5_slotVec α k g z θ x) ^ 2 :=
    Finset.sum_congr rfl fun x _ => by rw [hk5_slotVec_add α k hf hg hz h1 h2 x]
  rw [hsum]
  exact hk5_sqrt_sum_sq_add_le Finset.univ (hk5_slotVec α k f z θ) (hk5_slotVec α k g z θ)

/-- Scalar homogeneity (in square-root form) of the `ℋ^k`-integrand. -/
theorem hk5_sqrt_HkIntegrand_const_mul (α : ℝ) (k : ℕ) (c : ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Real.sqrt (Work.Spaces.HkIntegrand α k (fun z θ => c * h z θ) z θ)
      = |c| * Real.sqrt (Work.Spaces.HkIntegrand α k h z θ) := by
  rw [Work.FTS.LocData.HkIntegrand_const_mul α k c h z θ, Real.sqrt_mul (sq_nonneg c),
    Real.sqrt_sq_eq_abs]

/-- The elementary step `HkIntegrand = (√HkIntegrand)² ≤ √HkIntegrand · W` from
`√HkIntegrand ≤ W`. -/
theorem hk5_HkIntegrand_le_sqrt_mul (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ W : ℝ)
    (hW : Real.sqrt (Work.Spaces.HkIntegrand α k f z θ) ≤ W) :
    Work.Spaces.HkIntegrand α k f z θ
      ≤ Real.sqrt (Work.Spaces.HkIntegrand α k f z θ) * W := by
  conv_lhs => rw [← Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k f z θ)]
  rw [pow_two]
  exact mul_le_mul_of_nonneg_left hW (Real.sqrt_nonneg _)

/-! ## The finite-sum upgrade -/

/-- `SmoothOpen` is closed under finite linear combinations. -/
theorem hk5_smoothOpen_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ → ℝ)
    (c : ι → ℝ) :
    (∀ i ∈ s, Work.FTS.EllipticEst.SmoothOpen (f i)) →
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => ∑ i ∈ s, c i * f i z θ) := by
  classical
  induction s using Finset.induction with
  | empty =>
      intro _
      have h0 : (fun z θ => ∑ i ∈ (∅ : Finset ι), c i * f i z θ) = fun _ _ => (0 : ℝ) := by
        funext z θ
        simp
      rw [h0]
      exact contDiffOn_const
  | insert i s hi ih =>
      intro hf
      have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => c i * f i z θ) :=
        hk5_smoothOpen_const_mul (c i) (hf i (Finset.mem_insert_self i s))
      have h2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => ∑ j ∈ s, c j * f j z θ) :=
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have hfun : (fun z θ => ∑ j ∈ insert i s, c j * f j z θ)
          = (fun z θ => c i * f i z θ + ∑ j ∈ s, c j * f j z θ) := by
        funext z θ
        rw [Finset.sum_insert hi]
      rw [hfun]
      exact Work.FTS.EllipticEst.smoothOpen_add h1 h2

/-- **The pointwise triangle inequality for a finite linear combination** on the open quadrant. -/
theorem hk5_sqrt_HkIntegrand_finset_sum_le (α : ℝ) (k : ℕ) {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℝ → ℝ) (c : ι → ℝ) :
    (∀ i ∈ s, Work.FTS.EllipticEst.SmoothOpen (f i)) →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Real.sqrt (Work.Spaces.HkIntegrand α k (fun z θ => ∑ i ∈ s, c i * f i z θ) z θ)
        ≤ ∑ i ∈ s, |c i| * Real.sqrt (Work.Spaces.HkIntegrand α k (f i) z θ) := by
  classical
  induction s using Finset.induction with
  | empty =>
      intro _ z θ _ _ _
      have h0 : (fun z θ => ∑ i ∈ (∅ : Finset ι), c i * f i z θ) = fun _ _ => (0 : ℝ) := by
        funext z θ
        simp
      rw [h0, Work.FTS.LocData.HkIntegrand_zero_fun α k z θ, Real.sqrt_zero,
        Finset.sum_empty]
  | insert i s hi ih =>
      intro hf z θ hz h1 h2
      have hfi : Work.FTS.EllipticEst.SmoothOpen (f i) := hf i (Finset.mem_insert_self i s)
      have hfs : ∀ j ∈ s, Work.FTS.EllipticEst.SmoothOpen (f j) :=
        fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have hA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => c i * f i z θ) :=
        hk5_smoothOpen_const_mul (c i) hfi
      have hB : Work.FTS.EllipticEst.SmoothOpen (fun z θ => ∑ j ∈ s, c j * f j z θ) :=
        hk5_smoothOpen_finset_sum s f c hfs
      have hfun : (fun z θ => ∑ j ∈ insert i s, c j * f j z θ)
          = (fun z θ => c i * f i z θ + ∑ j ∈ s, c j * f j z θ) := by
        funext z θ
        rw [Finset.sum_insert hi]
      rw [hfun, Finset.sum_insert hi]
      refine le_trans (hk5_sqrt_HkIntegrand_add_le α k hA hB z θ hz h1 h2) ?_
      have hhom : Real.sqrt (Work.Spaces.HkIntegrand α k (fun z θ => c i * f i z θ) z θ)
          = |c i| * Real.sqrt (Work.Spaces.HkIntegrand α k (f i) z θ) :=
        hk5_sqrt_HkIntegrand_const_mul α k (c i) (f i) z θ
      rw [hhom]
      linarith [ih hfs z θ hz h1 h2]

/-- **The pointwise triangle inequality for the `ℋ^k`-integrand of a Galerkin combination**, on
the whole quadrant `Iz × Iθ` (the two boundary lines are handled by exact vanishing). -/
theorem hk5_sqrt_galFun_le (α : ℝ) (k : ℕ) {n : ℕ} {φ : ℕ → ℝ → ℝ → ℝ} {c : Fin n → ℝ}
    (hφ : ∀ i : Fin n, Work.FTS.EllipticEst.SmoothOpen (φ (i : ℕ))) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Real.sqrt (Work.Spaces.HkIntegrand α k (Work.FTS.Galerkin.galFun φ c) z θ)
        ≤ ∑ i : Fin n, |c i| * Real.sqrt (Work.Spaces.HkIntegrand α k (φ (i : ℕ)) z θ) := by
  intro z hz θ hθ
  have hzbd : (0 : ℝ) ≤ z := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hz
  have hbnd : (0 : ℝ) ≤ θ ∧ θ ≤ π / 2 := by
    simpa only [Work.Spaces.Iθ, Set.mem_Icc] using hθ
  have hRHS : 0 ≤ ∑ i : Fin n, |c i| * Real.sqrt (Work.Spaces.HkIntegrand α k (φ (i : ℕ)) z θ) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  rcases eq_or_lt_of_le hzbd with h0 | hzpos
  · subst h0
    rw [Work.FTS.LocData.HkIntegrand_zero_fst α k (Work.FTS.Galerkin.galFun φ c) θ,
      Real.sqrt_zero]
    exact hRHS
  rcases eq_or_lt_of_le hbnd.1 with h1 | hθpos
  · subst h1
    rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k
      (Work.FTS.Galerkin.galFun φ c) z 0 (by simp), Real.sqrt_zero]
    exact hRHS
  rcases lt_or_eq_of_le hbnd.2 with h2 | h2
  · have hmain := hk5_sqrt_HkIntegrand_finset_sum_le α k (Finset.univ : Finset (Fin n))
      (fun i : Fin n => φ (i : ℕ)) c (fun i _ => hφ i) z θ hzpos hθpos h2
    have hfun : (fun z θ => ∑ i ∈ (Finset.univ : Finset (Fin n)),
        c i * (fun i : Fin n => φ (i : ℕ)) i z θ) = Work.FTS.Galerkin.galFun φ c := rfl
    rw [hfun] at hmain
    exact hmain
  · subst h2
    rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k
      (Work.FTS.Galerkin.galFun φ c) z (Real.pi / 2)
      (by rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]), Real.sqrt_zero]
    exact hRHS

end Work.FTS.GalFields.Norm
