import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.H2.DivQ.Defs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.DivQ.honestPoincarePoint
import Submission.Work.FTS.H2.DivQ.divSinIterMidBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The middle interval `[π/8, 3π/8]`

Throughout this file `midA = π/8` and `midB = 3π/8` are the two ends of the *middle* region, on
which `sin(2θ) ∈ [1/2, 1]`.  The two abbreviations are `abbrev`s, so they are definitionally the
literal expressions occurring in the statement of `middleRegionLHS`. -/

/-- The left end `π/8` of the middle region. -/
abbrev midA : ℝ := Real.pi / 8

/-- The right end `3π/8` of the middle region. -/
abbrev midB : ℝ := 3 * Real.pi / 8

/-- The middle region, as a set. -/
abbrev midSet : Set ℝ := Set.Icc midA midB

theorem midA_lt_midB : midA < midB := by
  change Real.pi / 8 < 3 * Real.pi / 8
  linarith [Real.pi_pos]

theorem midA_pos : 0 < midA := by
  change (0 : ℝ) < Real.pi / 8
  linarith [Real.pi_pos]

theorem midB_lt_pi_div_two : midB < Real.pi / 2 := by
  change 3 * Real.pi / 8 < Real.pi / 2
  linarith [Real.pi_pos]

/-- The middle region is contained in the open angular interval `(0, π/2)`. -/
theorem midSet_subset_Ioo : midSet ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  intro x hx
  exact ⟨lt_of_lt_of_le midA_pos hx.1, lt_of_le_of_lt hx.2 midB_lt_pi_div_two⟩

/-- The middle region is contained in `Iθ`. -/
theorem midSet_subset_Iθ : midSet ⊆ Work.Spaces.Iθ := by
  intro x hx
  exact ⟨le_trans midA_pos.le hx.1, le_trans hx.2 midB_lt_pi_div_two.le⟩

/-! ## Elementary bounds for `sin (2θ)` on the middle region -/

/-- `1/2 ≤ sin (2θ)` for `θ ∈ [π/8, 3π/8]`: indeed `2θ ∈ [π/4, 3π/4]` and `sin ≥ √2/2` there. -/
theorem half_le_sin_two_of_mem_mid {θ : ℝ} (hθ : θ ∈ midSet) :
    (1 : ℝ) / 2 ≤ Real.sin (2 * θ) := by
  have h1 : Real.pi / 4 ≤ 2 * θ := by
    have := hθ.1; change Real.pi / 8 ≤ θ at this; linarith [this, Real.pi_pos]
  have h2 : 2 * θ ≤ 3 * Real.pi / 4 := by
    have := hθ.2; change θ ≤ 3 * Real.pi / 8 at this; linarith [this, Real.pi_pos]
  have key : ∀ t : ℝ, Real.pi / 4 ≤ t → t ≤ 3 * Real.pi / 4 → (1 : ℝ) / 2 ≤ Real.sin t := by
    intro t ht1 ht2
    rcases le_total t (Real.pi / 2) with h | h
    · have h3 := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 4) (y := t)
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) ht1
      rw [Real.sin_pi_div_four] at h3
      have := Real.one_lt_sqrt_two; linarith
    · have h3 := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 4) (y := Real.pi - t)
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith)
      rw [Real.sin_pi_div_four, Real.sin_pi_sub] at h3
      have := Real.one_lt_sqrt_two; linarith
  exact key (2 * θ) h1 h2

/-- `0 < sin (2θ)` for `θ ∈ [π/8, 3π/8]`. -/
theorem sin_two_pos_of_mem_mid {θ : ℝ} (hθ : θ ∈ midSet) : 0 < Real.sin (2 * θ) :=
  lt_of_lt_of_le (by norm_num) (half_le_sin_two_of_mem_mid hθ)

/-- `sin (2θ) ≤ 1` for `θ ∈ [π/8, 3π/8]`. -/
theorem sin_two_le_one_mid {θ : ℝ} (_hθ : θ ∈ midSet) : Real.sin (2 * θ) ≤ 1 :=
  Real.sin_le_one _

/-! ## The weight `sin(2θ)^{-γ}` on the middle region -/

/-- On the middle region the weight `sin(2θ)^{-γ}` is bounded by `2^γ` (for `γ ≥ 0`). -/
theorem rpow_neg_sin_two_le_mid {γ : ℝ} (hγ : 0 ≤ γ) {θ : ℝ} (hθ : θ ∈ midSet) :
    (Real.sin (2 * θ)) ^ (-γ) ≤ 2 ^ γ := by
  have hhalf := half_le_sin_two_of_mem_mid hθ
  have h1 : (Real.sin (2 * θ)) ^ (-γ) ≤ ((1 : ℝ) / 2) ^ (-γ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hhalf (by linarith)
  have h2 : ((1 : ℝ) / 2) ^ (-γ) = 2 ^ γ := by
    rw [one_div, Real.inv_rpow (show (0 : ℝ) ≤ 2 by norm_num),
      Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num) γ, inv_inv]
  rwa [h2] at h1

/-- On the middle region, `sin(2θ)^{-γ} ≤ 2^γ · sin(2θ)^{-η}` for `γ ≥ η ≥ 0`: split off the
excess exponent `γ - η` (the factor `sin(2θ)^{-(γ-η)}` is at most `2^{γ-η} ≤ 2^γ` because
`sin(2θ) ≥ 1/2` there). -/
theorem rpow_neg_sin_two_le_mid_eta {γ : ℝ} (hγ : Work.Spaces.eta ≤ γ) {θ : ℝ}
    (hθ : θ ∈ midSet) :
    (Real.sin (2 * θ)) ^ (-γ) ≤ 2 ^ γ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs := sin_two_pos_of_mem_mid hθ
  have hhalf := half_le_sin_two_of_mem_mid hθ
  have hγη : 0 ≤ γ - Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
  have hsplit : (Real.sin (2 * θ)) ^ (-γ)
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Real.sin (2 * θ)) ^ (-(γ - Work.Spaces.eta)) := by
    rw [← Real.rpow_add hs]; ring_nf
  have hb : (Real.sin (2 * θ)) ^ (-(γ - Work.Spaces.eta))
      ≤ ((1 : ℝ) / 2) ^ (-(γ - Work.Spaces.eta)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hhalf (by linarith)
  have hb' : ((1 : ℝ) / 2) ^ (-(γ - Work.Spaces.eta)) = 2 ^ (γ - Work.Spaces.eta) := by
    rw [one_div, Real.inv_rpow (show (0 : ℝ) ≤ 2 by norm_num),
      Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num) (γ - Work.Spaces.eta), inv_inv]
  have hb2 : (Real.sin (2 * θ)) ^ (-(γ - Work.Spaces.eta)) ≤ 2 ^ (γ - Work.Spaces.eta) :=
    hb.trans_eq hb'
  have hb3 : (2 : ℝ) ^ (γ - Work.Spaces.eta) ≤ 2 ^ γ :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr
      (by linarith [Work.Spaces.eta_pos])
  have hnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs.le _
  calc (Real.sin (2 * θ)) ^ (-γ)
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Real.sin (2 * θ)) ^ (-(γ - Work.Spaces.eta)) := hsplit
    _ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * 2 ^ (γ - Work.Spaces.eta) :=
        mul_le_mul_of_nonneg_left hb2 hnn
    _ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * 2 ^ γ :=
        mul_le_mul_of_nonneg_left hb3 hnn
    _ = 2 ^ γ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by ring

/-! ## Smoothness of the pieces on the middle region -/

/-- The angular quotient `h / sin(2θ)` is `C^∞` on `(0, π/2)` when `h` is. -/
theorem contDiffOn_div_sin_two {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun θ => h θ / Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) := by
  apply hsm.div
  · fun_prop
  · intro θ hθ
    exact ne_of_gt (Work.FTS.H2.sin_two_pos_of_Ioo hθ)

/-- Every iterate `D_θ^m h` is `C^∞` on `(0, π/2)` when `h` is. -/
theorem contDiffOn_Dth1Iter {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) (m : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Work.Elliptic.Dth1Iter m h) (Set.Ioo 0 (Real.pi / 2)) := by
  induction m with
  | zero => simpa using hsm
  | succ k ih =>
    rw [Work.Elliptic.Dth1Iter_succ]
    exact (by fun_prop : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => Real.sin (2 * θ))
        (Set.Ioo 0 (Real.pi / 2))).mul (ih.deriv_of_isOpen isOpen_Ioo (by simp))

/-- The derivative of a `C^∞` slice is `C^∞` on `(0, π/2)`. -/
theorem contDiffOn_deriv_slice {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (deriv h) (Set.Ioo 0 (Real.pi / 2)) :=
  hsm.deriv_of_isOpen isOpen_Ioo (by simp)

/-- The weight `θ ↦ sin(2θ)^{-γ}` is continuous on the middle region. -/
theorem continuousOn_rpow_neg_sin_two (γ : ℝ) :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-γ)) midSet := by
  apply ContinuousOn.rpow
  · fun_prop
  · exact continuousOn_const
  · intro θ hθ
    exact Or.inl (ne_of_gt (sin_two_pos_of_mem_mid hθ))

/-- `h / sin(2θ)` is continuous on the middle region. -/
theorem continuousOn_div_sin_two {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun θ => h θ / Real.sin (2 * θ)) midSet :=
  ((contDiffOn_div_sin_two hsm).continuousOn).mono midSet_subset_Ioo

/-- `D_θ^m (∂_θ h)` is continuous on the middle region. -/
theorem continuousOn_Dth1Iter_deriv {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) (m : ℕ) :
    ContinuousOn (fun θ => Work.Elliptic.Dth1Iter m (deriv h) θ) midSet :=
  ((contDiffOn_Dth1Iter (contDiffOn_deriv_slice hsm) m).continuousOn).mono midSet_subset_Ioo

/-- `D_θ^i (h / sin(2θ))` is continuous on the middle region. -/
theorem continuousOn_Dth1Iter_div {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) (i : ℕ) :
    ContinuousOn
      (fun θ => Work.Elliptic.Dth1Iter i (fun θ => h θ / Real.sin (2 * θ)) θ) midSet :=
  ((contDiffOn_Dth1Iter (contDiffOn_div_sin_two hsm) i).continuousOn).mono midSet_subset_Ioo

/-- `∂_θ h` is continuous on the middle region. -/
theorem continuousOn_deriv_slice {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (deriv h) midSet :=
  ((contDiffOn_deriv_slice hsm).continuousOn).mono midSet_subset_Ioo

/-- The length of the middle interval: `|(π/8, 3π/8)| = π/4`. -/
theorem volume_real_Ioc_mid : (volume : MeasureTheory.Measure ℝ).real (Set.Ioc midA midB)
    = Real.pi / 4 := by
  rw [MeasureTheory.measureReal_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (by
      change (0 : ℝ) ≤ 3 * Real.pi / 8 - Real.pi / 8
      linarith [Real.pi_pos])]
  change 3 * Real.pi / 8 - Real.pi / 8 = Real.pi / 4
  ring

/-- **The middle-region bound for the left-hand side of `DivisionBySin` (the cheap piece).**

There is a universal constant `C` such that: for every `0 < α ≤ 1` and every slice `h` of class
`C^∞` on `(0,π/2)` with `h(θ) → 0` at both endpoints, and with the data integrals

  `Denη = ∫_{Iθ}(∂_θh)² sin(2θ)^{-η}`  and  `Denγ m = ∫_{Iθ}(D_θ^m(∂_θh))² sin(2θ)^{-γ}` (1 ≤ m ≤ 4)

honest (`η = 99/100`, `γ = 1+α/10`, `Iθ = [0,π/2]`, `D_θ^m = Work.Elliptic.Dth1Iter m`), and for
every `1 ≤ i ≤ 4`:

  `∫_{π/8}^{3π/8} (D_θ^i (fun θ => h θ / sin(2θ)) θ)² sin(2θ)^{-γ} dθ ≤ C (Denη + Σ_{1≤m≤i} Denγ m)`.

This is the *middle* piece, where no substitution is needed: on `[π/8, 3π/8]` we have
`sin(2θ) ∈ [1/√2, 1]`, so all weights are bounded above and below by universal constants, the
coefficients `D_θ^k (2 cos 2θ)` (`k ≤ 4`) are bounded there (crude explicit bounds suffice), and
`h/sin(2θ)` is smooth.

ROUTE (see `Submission/Work/FTS/H2/DivQ/NOTES.md` §5).

* `D_θ(h/sin 2θ) = ∂_θh - 2cos(2θ)·(h/sin 2θ)` pointwise on `(0,π/2)`, and by the Leibniz rule
  for the derivation `D_θ = sin(2θ)∂_θ`,
  `D_θ^i(h/sin 2θ) = D_θ^{i-1}(∂_θh) - Σ_{k<i} C(i-1,k)·D_θ^k(2cos 2θ)·D_θ^{i-1-k}(h/sin 2θ)`.
  Hence the pointwise bound
  `|D_θ^i(h/sin 2θ)(θ)| ≤ C_i(Σ_{m<i}|D_θ^m(∂_θh)(θ)| + |h(θ)/sin(2θ)|)` on `Iθ`, with `C_i`
  universal.
* Therefore `∫_{mid}(D_θ^i(h/sin 2θ))²sin(2θ)^{-γ} ≤ C_i(Σ_{m<i}∫_{mid}(D_θ^m(∂_θh))²sin(2θ)^{-γ}
  + ∫_{mid}(h/sin(2θ))²)`.  For `m ≥ 1` bound the middle integral by the full `Denγ m` times
  `2^{γ/2}` (on `Iθ` one has `sin(2θ)^{-γ} ≤ 2^{γ/2}sin(2θ)^{-η}`, since `γ ≥ η` and
  `sin(2θ) ≤ 1/2` on the two end intervals); the `m = 0` term needs only
  `∫_{mid}(∂_θh)² ≤ Denη` (`sin(2θ)^{-η} ≥ 1`).
* `∫_{mid}(h/sin(2θ))² ≤ 2∫_{Iθ}h²`, and the elementary Poincaré
  `|h(θ)|² ≤ min(θ, π/2-θ)·∫_{Iθ}(∂_θh)²` (from `h(θ) = ∫_0^θ ∂_θh = -∫_θ^{π/2}∂_θh`, both
  endpoint limits being `0`) gives `∫_{Iθ}h² ≤ (π²/16)∫_{Iθ}(∂_θh)² ≤ C Denη`. -/
theorem middleRegionLHS :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ →
      (∀ m : ℕ, m ∈ Finset.Icc 1 4 → MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) →
      ∀ i : ℕ, i ∈ Finset.Icc 1 4 →
        (∫ θ in (Real.pi / 8)..(3 * Real.pi / 8),
            (Work.Elliptic.Dth1Iter i (fun θ => h θ / Real.sin (2 * θ)) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ C * ((∫ θ in Work.Spaces.Iθ,
                (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
  obtain ⟨K, hKpos, hKb⟩ := divSinIterMidBound
  obtain ⟨C₁, hC₁pos, hC₁b⟩ := honestPoincarePoint
  refine ⟨100 * K * (C₁ + 1) + 1, by positivity, ?_⟩
  intro α h hα hα1 hsm ht0 ht1 hIntη hIntγ i hi
  let γ : ℝ := Work.Spaces.gam α
  let V : ℝ → ℝ := fun θ => h θ / Real.sin (2 * θ)
  let w : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-γ)
  let wη : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
  let Un : ℕ → ℝ → ℝ := fun m θ => Work.Elliptic.Dth1Iter m (deriv h) θ
  let Denη : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 * wη θ
  let Dens : ℝ := ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ, (Un m θ) ^ 2 * w θ)
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hi4 : i ≤ 4 := (Finset.mem_Icc.mp hi).2
  have hγdef : γ = Work.Spaces.gam α := rfl
  have hγpos : 0 < γ := by rw [hγdef, Work.Spaces.gam]; linarith
  have hγeta : Work.Spaces.eta ≤ γ := by
    rw [hγdef, Work.Spaces.gam, Work.Spaces.eta]; linarith
  have hγle : γ ≤ 1.1 := by rw [hγdef, Work.Spaces.gam]; linarith
  have h2γle : (2 : ℝ) ^ γ ≤ 4 := by
    have h1 : (2 : ℝ) ^ γ ≤ (2 : ℝ) ^ (2 : ℝ) :=
      (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr (by linarith)
    have h2 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
    linarith [h1, h2]
  have h2γ1 : (1 : ℝ) ≤ 2 ^ γ := Real.one_le_rpow (by norm_num) hγpos.le
  have h2γ_nn : (0 : ℝ) ≤ 2 ^ γ := le_trans zero_le_one h2γ1
  have hDenη_nn : 0 ≤ Denη :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ hθ) _))
  have hDens_nn : 0 ≤ Dens :=
    Finset.sum_nonneg (fun m _ =>
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ hθ) _)))
  show (∫ θ in midA..midB, (Work.Elliptic.Dth1Iter i V θ) ^ 2 * w θ)
      ≤ (100 * K * (C₁ + 1) + 1) * (Denη + Dens)
  rw [intervalIntegral.integral_of_le midA_lt_midB.le]
  -- ## integrability on the middle interval
  have hIc : ∀ m ∈ Finset.range i,
      IntegrableOn (fun θ => (Un m θ) ^ 2 * w θ) (Set.Ioc midA midB) := by
    intro m _
    exact (ContinuousOn.integrableOn_compact isCompact_Icc
      (((continuousOn_Dth1Iter_deriv hsm m).pow 2).mul
        (continuousOn_rpow_neg_sin_two γ))).mono_set Set.Ioc_subset_Icc_self
  have hIa : IntegrableOn (fun θ => (V θ) ^ 2 * w θ) (Set.Ioc midA midB) :=
    (ContinuousOn.integrableOn_compact isCompact_Icc
      (((continuousOn_div_sin_two hsm).pow 2).mul
        (continuousOn_rpow_neg_sin_two γ))).mono_set Set.Ioc_subset_Icc_self
  have hIb : IntegrableOn (fun θ => ∑ m ∈ Finset.range i, (Un m θ) ^ 2 * w θ)
      (Set.Ioc midA midB) :=
    (ContinuousOn.integrableOn_compact isCompact_Icc
      (continuousOn_finsetSum (Finset.range i) (fun m _ =>
        ((continuousOn_Dth1Iter_deriv hsm m).pow 2).mul
          (continuousOn_rpow_neg_sin_two γ)))).mono_set Set.Ioc_subset_Icc_self
  have hFint : IntegrableOn (fun θ => (Work.Elliptic.Dth1Iter i V θ) ^ 2 * w θ)
      (Set.Ioc midA midB) :=
    (ContinuousOn.integrableOn_compact isCompact_Icc
      (((continuousOn_Dth1Iter_div hsm i).pow 2).mul
        (continuousOn_rpow_neg_sin_two γ))).mono_set Set.Ioc_subset_Icc_self
  have hΨint : IntegrableOn
      (fun θ => K * ((V θ) ^ 2 * w θ + ∑ m ∈ Finset.range i, (Un m θ) ^ 2 * w θ))
      (Set.Ioc midA midB) :=
    (ContinuousOn.integrableOn_compact isCompact_Icc
      (continuousOn_const.mul ((((continuousOn_div_sin_two hsm).pow 2).mul
        (continuousOn_rpow_neg_sin_two γ)).add
        (continuousOn_finsetSum (Finset.range i) (fun m _ =>
          ((continuousOn_Dth1Iter_deriv hsm m).pow 2).mul
            (continuousOn_rpow_neg_sin_two γ)))))).mono_set Set.Ioc_subset_Icc_self
  -- ## the pointwise iterate bound
  have hpt : ∀ θ ∈ Set.Ioc midA midB,
      (Work.Elliptic.Dth1Iter i V θ) ^ 2 * w θ
        ≤ K * ((V θ) ^ 2 * w θ + ∑ m ∈ Finset.range i, (Un m θ) ^ 2 * w θ) := by
    intro θ hθ
    have hm : θ ∈ midSet := ⟨le_of_lt hθ.1, hθ.2⟩
    have hw : 0 ≤ w θ :=
      Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ (midSet_subset_Iθ hm)) _
    have h1 := hKb h hsm i hi θ hm
    calc (Work.Elliptic.Dth1Iter i V θ) ^ 2 * w θ
        ≤ (K * ((V θ) ^ 2 + ∑ m ∈ Finset.range i, (Un m θ) ^ 2)) * w θ :=
          mul_le_mul_of_nonneg_right h1 hw
      _ = K * ((V θ) ^ 2 * w θ + ∑ m ∈ Finset.range i, (Un m θ) ^ 2 * w θ) := by
          rw [← Finset.sum_mul]; ring
  -- ## evaluation of `∫ Ψ`
  have hΨeq : (∫ θ in Set.Ioc midA midB,
        K * ((V θ) ^ 2 * w θ + ∑ m ∈ Finset.range i, (Un m θ) ^ 2 * w θ))
      = K * ((∫ θ in Set.Ioc midA midB, (V θ) ^ 2 * w θ)
          + ∑ m ∈ Finset.range i, ∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_add hIa hIb, MeasureTheory.integral_finsetSum _ hIc]
  -- ## the `V`-term
  have hBV : (∫ θ in Set.Ioc midA midB, (V θ) ^ 2 * w θ) ≤ 16 * C₁ * Denη := by
    have hptV : ∀ θ ∈ Set.Ioc midA midB, (V θ) ^ 2 * w θ ≤ 16 * C₁ * Denη := by
      intro θ hθ
      have hm : θ ∈ midSet := ⟨le_of_lt hθ.1, hθ.2⟩
      have hhalf := half_le_sin_two_of_mem_mid hm
      have hC := hC₁b h hsm ht0 hIntη θ (midSet_subset_Ioo hm)
      have hw := rpow_neg_sin_two_le_mid hγpos.le hm
      have hV2 : (V θ) ^ 2 ≤ 4 * (h θ) ^ 2 := by
        have hs2 : (1 : ℝ) / 4 ≤ (Real.sin (2 * θ)) ^ 2 := by nlinarith [hhalf]
        rw [show V θ = h θ / Real.sin (2 * θ) from rfl, div_pow,
          div_le_iff₀ (by positivity : (0 : ℝ) < (Real.sin (2 * θ)) ^ 2)]
        nlinarith [hs2, sq_nonneg (h θ)]
      have h2 : (V θ) ^ 2 ≤ 4 * (C₁ * Denη) := by
        have := hV2; nlinarith [hC, hC₁pos.le, hDenη_nn]
      have h4 : (0 : ℝ) ≤ 4 * (C₁ * Denη) := by
        have := hC₁pos.le; nlinarith [hDenη_nn]
      calc (V θ) ^ 2 * w θ ≤ (4 * (C₁ * Denη)) * 2 ^ γ :=
            mul_le_mul h2 hw (Real.rpow_nonneg
              (Work.FTS.H2.sin_two_nonneg_Iθ (midSet_subset_Iθ hm)) _) h4
        _ ≤ (4 * (C₁ * Denη)) * 4 := mul_le_mul_of_nonneg_left h2γle h4
        _ = 16 * C₁ * Denη := by ring
    have hInt2 : IntegrableOn (fun _ : ℝ => 16 * C₁ * Denη) (Set.Ioc midA midB) :=
      integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    have haux := MeasureTheory.setIntegral_mono_on hIa hInt2 measurableSet_Ioc hptV
    rw [MeasureTheory.setIntegral_const, volume_real_Ioc_mid, smul_eq_mul] at haux
    refine haux.trans ?_
    have hnn : (0 : ℝ) ≤ 16 * C₁ * Denη := by have := hC₁pos.le; nlinarith [hDenη_nn]
    nlinarith [Real.pi_le_four, hnn]
  -- ## the `m = 0` term
  have hB0 : (∫ θ in Set.Ioc midA midB, (Un 0 θ) ^ 2 * w θ) ≤ 2 ^ γ * Denη := by
    have hpt0 : ∀ θ ∈ Set.Ioc midA midB,
        (Un 0 θ) ^ 2 * w θ ≤ 2 ^ γ * ((deriv h θ) ^ 2 * wη θ) := by
      intro θ hθ
      have hm : θ ∈ midSet := ⟨le_of_lt hθ.1, hθ.2⟩
      have hle := rpow_neg_sin_two_le_mid_eta hγeta hm
      calc (Un 0 θ) ^ 2 * w θ = (deriv h θ) ^ 2 * w θ := rfl
        _ ≤ (deriv h θ) ^ 2 * (2 ^ γ * wη θ) :=
            mul_le_mul_of_nonneg_left hle (sq_nonneg _)
        _ = 2 ^ γ * ((deriv h θ) ^ 2 * wη θ) := by ring
    have hInt3 : IntegrableOn (fun θ => 2 ^ γ * ((deriv h θ) ^ 2 * wη θ))
        (Set.Ioc midA midB) :=
      (ContinuousOn.integrableOn_compact isCompact_Icc
        (continuousOn_const.mul (((continuousOn_deriv_slice hsm).pow 2).mul
          (continuousOn_rpow_neg_sin_two (Work.Spaces.eta))))).mono_set Set.Ioc_subset_Icc_self
    have h0mem : (0 : ℕ) ∈ Finset.range i := Finset.mem_range.mpr hi1
    have haux := MeasureTheory.setIntegral_mono_on (hIc 0 h0mem) hInt3 measurableSet_Ioc hpt0
    refine haux.trans ?_
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ h2γ_nn
    have hmono : (∫ θ in Set.Ioc midA midB, (deriv h θ) ^ 2 * wη θ)
        ≤ (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 * wη θ) :=
      MeasureTheory.setIntegral_mono_set hIntη
        ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall
          (fun θ hθ => mul_nonneg (sq_nonneg _)
            (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ hθ) _))))
        (Filter.Eventually.of_forall (fun θ (hθ : θ ∈ Set.Ioc midA midB) => midSet_subset_Iθ ⟨le_of_lt hθ.1, hθ.2⟩))
    exact hmono
  -- ## the `m ≥ 1` terms
  have hBm : ∀ m : ℕ, 1 ≤ m → m ≤ i →
      (∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (Un m θ) ^ 2 * w θ := by
    intro m hm1 hmi
    have hm4 : m ∈ Finset.Icc 1 4 := Finset.mem_Icc.mpr ⟨hm1, le_trans hmi hi4⟩
    exact MeasureTheory.setIntegral_mono_set (hIntγ m hm4)
      ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall
        (fun θ hθ => mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ hθ) _))))
      (Filter.Eventually.of_forall (fun θ (hθ : θ ∈ Set.Ioc midA midB) => midSet_subset_Iθ ⟨le_of_lt hθ.1, hθ.2⟩))
  -- ## the sum
  have hSum : (∑ m ∈ Finset.range i, ∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ)
      ≤ (i : ℝ) * (2 ^ γ * (Denη + Dens)) := by
    have hterm : ∀ m ∈ Finset.range i,
        (∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ) ≤ 2 ^ γ * (Denη + Dens) := by
      intro m hm
      have hlt : m < i := Finset.mem_range.mp hm
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        calc (∫ θ in Set.Ioc midA midB, (Un 0 θ) ^ 2 * w θ) ≤ 2 ^ γ * Denη := hB0
          _ ≤ 2 ^ γ * (Denη + Dens) := by
              apply mul_le_mul_of_nonneg_left _ h2γ_nn
              linarith [hDens_nn]
      · have hmIcc : m ∈ Finset.Icc 1 i := Finset.mem_Icc.mpr ⟨hpos, le_of_lt hlt⟩
        have hsingle : (∫ θ in Work.Spaces.Iθ, (Un m θ) ^ 2 * w θ) ≤ Dens := by
          show (∫ θ in Work.Spaces.Iθ, (Un m θ) ^ 2 * w θ) ≤
            ∑ a ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ, (Un a θ) ^ 2 * w θ)
          exact Finset.single_le_sum (fun a _ => MeasureTheory.setIntegral_nonneg
            measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _)
              (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ hθ) _))) hmIcc
        have hb := hBm m hpos (le_of_lt hlt)
        have hS_nn : 0 ≤ Denη + Dens := by linarith
        have hfin : Dens ≤ 2 ^ γ * (Denη + Dens) := by
          have h1 := mul_le_mul_of_nonneg_right h2γ1 hS_nn
          nlinarith [h1, hDens_nn]
        calc (∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ)
            ≤ ∫ θ in Work.Spaces.Iθ, (Un m θ) ^ 2 * w θ := hb
          _ ≤ Dens := hsingle
          _ ≤ 2 ^ γ * (Denη + Dens) := hfin
    calc (∑ m ∈ Finset.range i, ∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ)
        ≤ ∑ m ∈ Finset.range i, (2 ^ γ * (Denη + Dens)) := Finset.sum_le_sum hterm
      _ = (Finset.range i).card • (2 ^ γ * (Denη + Dens)) := Finset.sum_const _
      _ = (i : ℝ) * (2 ^ γ * (Denη + Dens)) := by
          rw [Finset.card_range, nsmul_eq_mul]
  -- ## assembly
  calc (∫ θ in Set.Ioc midA midB, (Work.Elliptic.Dth1Iter i V θ) ^ 2 * w θ)
      ≤ ∫ θ in Set.Ioc midA midB,
          K * ((V θ) ^ 2 * w θ + ∑ m ∈ Finset.range i, (Un m θ) ^ 2 * w θ) :=
        MeasureTheory.setIntegral_mono_on hFint hΨint measurableSet_Ioc hpt
    _ = K * ((∫ θ in Set.Ioc midA midB, (V θ) ^ 2 * w θ)
          + ∑ m ∈ Finset.range i, ∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ) := hΨeq
    _ ≤ (100 * K * (C₁ + 1) + 1) * (Denη + Dens) := by
        have hS_nn : (0 : ℝ) ≤ Denη + Dens := by linarith
        have hsum : (∫ θ in Set.Ioc midA midB, (V θ) ^ 2 * w θ)
              + ∑ m ∈ Finset.range i, ∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ
            ≤ 16 * C₁ * Denη + 16 * (Denη + Dens) := by
          have h1 : (i : ℝ) * (2 ^ γ * (Denη + Dens)) ≤ 16 * (Denη + Dens) := by
            have hi4R : (i : ℝ) ≤ 4 := by exact_mod_cast hi4
            have h3 : 2 ^ γ * (Denη + Dens) ≤ 4 * (Denη + Dens) := by
              nlinarith [h2γle, hS_nn]
            have := mul_le_mul hi4R h3 (mul_nonneg h2γ_nn hS_nn) (by norm_num)
            nlinarith [this]
          linarith [hBV, hSum, h1]
        have hbig : K * (16 * C₁ * Denη + 16 * (Denη + Dens))
            ≤ (100 * K * (C₁ + 1) + 1) * (Denη + Dens) := by
          have hC1n : (0 : ℝ) ≤ C₁ + 1 := by linarith [hC₁pos.le]
          have h16 : 16 * C₁ * Denη + 16 * (Denη + Dens) ≤ 16 * (C₁ + 1) * (Denη + Dens) := by
            nlinarith [hC₁pos.le, hDenη_nn, hDens_nn, hS_nn]
          have h100 : 16 * (C₁ + 1) * (Denη + Dens) ≤ 100 * (C₁ + 1) * (Denη + Dens) := by
            have h16le : (16 : ℝ) ≤ 100 := by norm_num
            have hprod : 0 ≤ (C₁ + 1) * (Denη + Dens) := mul_nonneg hC1n hS_nn
            nlinarith [h16le, hprod]
          calc K * (16 * C₁ * Denη + 16 * (Denη + Dens))
              ≤ K * (16 * (C₁ + 1) * (Denη + Dens)) := mul_le_mul_of_nonneg_left h16 hKpos.le
            _ ≤ K * (100 * (C₁ + 1) * (Denη + Dens)) := mul_le_mul_of_nonneg_left h100 hKpos.le
            _ ≤ (100 * K * (C₁ + 1) + 1) * (Denη + Dens) := by
                have h1 : K * (100 * (C₁ + 1) * (Denη + Dens))
                    = 100 * K * (C₁ + 1) * (Denη + Dens) := by ring
                rw [h1]
                nlinarith [hS_nn, hKpos.le, hC1n]
        exact (mul_le_mul_of_nonneg_left hsum hKpos.le).trans hbig


end Work.FTS.H2.DivQ
