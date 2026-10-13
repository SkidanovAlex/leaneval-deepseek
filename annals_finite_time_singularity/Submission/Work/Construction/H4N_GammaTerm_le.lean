import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Construction.Defs
import Submission.Work.Construction.Basic
import Submission.Work.Construction.Apriori
import Submission.Work.Construction.GammaN0
import Submission.Work.Construction.GammaTermAux
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.bt_aux
import Submission.Work.Elliptic.WtoH
import Submission.Work.Elliptic.WtoH_IntZ
import Submission.Work.Construction.H4N_GammaTerm_rho_bound
import Submission.Work.Construction.H4N_GammaTerm_Lop_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Construction

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Assembly helpers for the `Γ`-term bound

These are the elementary one-variable facts used by the assembly of
`H4N_GammaTerm_le`; the two computational cores (`H4N_GammaTerm_rho_bound`,
`H4N_GammaTerm_Lop_bound`) are proved in the companion modules. -/

/-- `|c2m θ| ≤ 2`. -/
theorem abs_c2m_le_two (θ : ℝ) : |c2m θ| ≤ 2 := by
  have h1 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have h2 : |Real.sin θ ^ 2| ≤ 1 := by
    rw [abs_pow]
    have h := Real.abs_sin_le_one θ
    nlinarith [abs_nonneg (Real.sin θ)]
  have h3 : Real.cos (2 * θ) - Real.sin θ ^ 2
      ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := by
    calc Real.cos (2 * θ) - Real.sin θ ^ 2
        = Real.cos (2 * θ) + -(Real.sin θ ^ 2) := by ring
      _ ≤ |Real.cos (2 * θ)| + |-(Real.sin θ ^ 2)| :=
          le_trans (le_abs_self _) (abs_add_le _ _)
      _ = |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := by rw [abs_neg]
  rw [c2m]
  calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
      ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := abs_sub_le_iff.mpr ⟨h3, by
        calc Real.sin θ ^ 2 - Real.cos (2 * θ)
            = Real.sin θ ^ 2 + -(Real.cos (2 * θ)) := by ring
          _ ≤ |Real.sin θ ^ 2| + |-(Real.cos (2 * θ))| :=
              le_trans (le_abs_self _) (abs_add_le _ _)
          _ = |Real.sin θ ^ 2| + |Real.cos (2 * θ)| := by rw [abs_neg]
          _ = |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := by ring ⟩
    _ ≤ 1 + 1 := add_le_add h1 h2
    _ = 2 := by norm_num

/-- `|ψ(θ)| ≤ 2` on the domain. -/
theorem psiA_abs_le_two {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    |psiA α θ| ≤ 2 := by
  have hΓ : |Work.Spaces.Gam α θ| ≤ 1 := by
    rw [abs_of_nonneg (Gam_nonneg_of_Iθ hα hθ)]
    exact Gam_le_one_of_Iθ hα hθ
  rw [psiA, abs_mul]
  calc |c2m θ| * |Work.Spaces.Gam α θ| ≤ 2 * 1 :=
        mul_le_mul (abs_c2m_le_two θ) hΓ (abs_nonneg _) (by norm_num)
    _ = 2 := by ring

/-- `s ^ a * s ^ b = s ^ (a + b)` for `s ≥ 0`. -/
theorem rpow_mul_rpow_eq {s a b : ℝ} (hs : 0 ≤ s) (h : a + b ≠ 0) :
    s ^ a * s ^ b = s ^ (a + b) := (Real.rpow_add' (x := s) (y := a) (z := b) hs h).symm

/-- `sin(2θ)^e ≤ sin(2θ)^{-η}` for `0 ≤ sin(2θ) ≤ 1` and `0 < e`. -/
theorem rpow_le_neg_eta {s e : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (he : 0 < e) :
    s ^ e ≤ s ^ (-(Work.Spaces.eta)) := by
  rcases eq_or_lt_of_le hs0 with h | h
  · subst h
    rw [Real.zero_rpow (ne_of_gt he),
      Real.zero_rpow (by linarith [Work.Spaces.eta_pos] : (-(Work.Spaces.eta)) ≠ 0)]
  · have h1 : s ^ e ≤ 1 := Real.rpow_le_one hs0 hs1 he.le
    have h2 : 1 ≤ s ^ (-(Work.Spaces.eta)) := by
      have key : s ^ (0:ℝ) ≤ s ^ (-(Work.Spaces.eta)) :=
        Real.rpow_le_rpow_of_exponent_ge h hs1
          (by linarith [Work.Spaces.eta_pos] : -(Work.Spaces.eta) ≤ 0)
      simpa using key
    linarith

/-- The angular pair of a mixed term: if `|x| ≤ D Γ(θ)(sin²(2θ)+α)` then
`x² sin(2θ)^{-γ} ≤ 2D²(sin(2θ)^{-η} + α² sin(2θ)^{2α/3-γ})`. -/
theorem mixed_angle_le {α D x θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hD : 0 ≤ D)
    (hθ : θ ∈ Work.Spaces.Iθ)
    (hx : |x| ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)) :
    x ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ 2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) := by
  set s : ℝ := Real.sin (2 * θ) with hs
  have hs0 : 0 ≤ s := sin_two_nonneg_of_mem_Iθ hθ
  have hs1 : s ≤ 1 := Real.sin_le_one _
  have hγ1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
  have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := Gam_nonneg_of_Iθ hα hθ
  have hΓs : Work.Spaces.Gam α θ ≤ s ^ (α / 3) := Gam_le_sin_two_rpow hα hθ
  have hsnnη : 0 ≤ s ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs0 _
  have hsnnγ : 0 ≤ s ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs0 _
  -- (i) `x² ≤ D² Γ² (s²+α)²`
  have hx2 : x ^ 2 ≤ D ^ 2 * Work.Spaces.Gam α θ ^ 2 * (s ^ 2 + α) ^ 2 := by
    have h1 : x ^ 2 ≤ (D * Work.Spaces.Gam α θ * (s ^ 2 + α)) ^ 2 := by
      rw [sq_le_sq,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ D * Work.Spaces.Gam α θ * (s ^ 2 + α))]
      exact hx
    calc x ^ 2 ≤ (D * Work.Spaces.Gam α θ * (s ^ 2 + α)) ^ 2 := h1
      _ = D ^ 2 * Work.Spaces.Gam α θ ^ 2 * (s ^ 2 + α) ^ 2 := by ring
  -- (ii) `Γ² ≤ s^{2α/3}`
  have hΓ2 : Work.Spaces.Gam α θ ^ 2 ≤ s ^ (2 * α / 3) := by
    have hne : α / 3 + α / 3 ≠ 0 := by intro h; linarith
    calc Work.Spaces.Gam α θ ^ 2 ≤ (s ^ (α / 3)) ^ 2 := pow_le_pow_left₀ hΓ0 hΓs 2
      _ = s ^ (α / 3) * s ^ (α / 3) := by ring
      _ = s ^ (α / 3 + α / 3) := rpow_mul_rpow_eq hs0 hne
      _ = s ^ (2 * α / 3) := by congr 1; ring
  -- (iii) `(s²+α)² ≤ 2(s⁴+α²)`
  have hsqa : (s ^ 2 + α) ^ 2 ≤ 2 * (s ^ 4 + α ^ 2) := by nlinarith [sq_nonneg (s ^ 2 - α)]
  -- (iv) the two exponents
  have hne1 : 2 * α / 3 + (4:ℝ) ≠ 0 := by intro h; linarith
  have hne2 : 2 * α / 3 + 4 + (-(Work.Spaces.gam α)) ≠ 0 := by
    rw [Work.Spaces.gam]; intro h; linarith
  have hne3 : 2 * α / 3 + (-(Work.Spaces.gam α)) ≠ 0 := by
    rw [Work.Spaces.gam]; intro h; linarith
  have hpow : s ^ (2 * α / 3 + 4 + (-(Work.Spaces.gam α))) ≤ s ^ (-(Work.Spaces.eta)) :=
    rpow_le_neg_eta hs0 hs1 (by rw [Work.Spaces.gam]; ring_nf; linarith)
  -- the θ-weighted combination
  have hcombine : s ^ (2 * α / 3) * (2 * (s ^ 4 + α ^ 2)) * s ^ (-(Work.Spaces.gam α))
      ≤ 2 * (s ^ (-(Work.Spaces.eta))
          + α ^ 2 * s ^ (2 * α / 3 + (-(Work.Spaces.gam α)))) := by
    have hcast : s ^ (4 : ℝ) = s ^ 4 := Real.rpow_natCast s 4
    have hsig : s ^ (2 * α / 3 + 4 + (-(Work.Spaces.gam α)))
        ≤ s ^ (-(Work.Spaces.eta)) := hpow
    calc s ^ (2 * α / 3) * (2 * (s ^ 4 + α ^ 2)) * s ^ (-(Work.Spaces.gam α))
        = 2 * ((s ^ (2 * α / 3) * s ^ (4:ℝ)) * s ^ (-(Work.Spaces.gam α))
            + α ^ 2 * (s ^ (2 * α / 3) * s ^ (-(Work.Spaces.gam α)))) := by
          rw [← hcast]; ring
      _ = 2 * (s ^ (2 * α / 3 + 4 + (-(Work.Spaces.gam α)))
            + α ^ 2 * s ^ (2 * α / 3 + (-(Work.Spaces.gam α)))) := by
          rw [rpow_mul_rpow_eq hs0 hne1, rpow_mul_rpow_eq hs0 hne2,
            rpow_mul_rpow_eq hs0 hne3]
      _ ≤ 2 * (s ^ (-(Work.Spaces.eta))
            + α ^ 2 * s ^ (2 * α / 3 + (-(Work.Spaces.gam α)))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact add_le_add hsig le_rfl
  -- combine everything
  calc x ^ 2 * s ^ (-(Work.Spaces.gam α))
      ≤ (D ^ 2 * Work.Spaces.Gam α θ ^ 2 * (s ^ 2 + α) ^ 2) * s ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_right hx2 hsnnγ
    _ ≤ (D ^ 2 * s ^ (2 * α / 3) * (2 * (s ^ 4 + α ^ 2))) * s ^ (-(Work.Spaces.gam α)) := by
        apply mul_le_mul_of_nonneg_right _ hsnnγ
        have hstep : Work.Spaces.Gam α θ ^ 2 * (s ^ 2 + α) ^ 2
            ≤ s ^ (2 * α / 3) * (2 * (s ^ 4 + α ^ 2)) :=
          mul_le_mul hΓ2 hsqa (sq_nonneg _) (Real.rpow_nonneg hs0 _)
        calc D ^ 2 * Work.Spaces.Gam α θ ^ 2 * (s ^ 2 + α) ^ 2
            = D ^ 2 * (Work.Spaces.Gam α θ ^ 2 * (s ^ 2 + α) ^ 2) := by ring
          _ ≤ D ^ 2 * (s ^ (2 * α / 3) * (2 * (s ^ 4 + α ^ 2))) :=
              mul_le_mul_of_nonneg_left hstep (sq_nonneg D)
          _ = D ^ 2 * s ^ (2 * α / 3) * (2 * (s ^ 4 + α ^ 2)) := by ring
    _ = D ^ 2 * (s ^ (2 * α / 3) * (2 * (s ^ 4 + α ^ 2)) * s ^ (-(Work.Spaces.gam α))) := by ring
    _ ≤ D ^ 2 * (2 * (s ^ (-(Work.Spaces.eta))
          + α ^ 2 * s ^ (2 * α / 3 + (-(Work.Spaces.gam α))))) :=
        mul_le_mul_of_nonneg_left hcombine (sq_nonneg D)
    _ = 2 * D ^ 2 * (s ^ (-(Work.Spaces.eta))
          + α ^ 2 * s ^ (2 * α / 3 - Work.Spaces.gam α)) := by
        rw [show (2 * α / 3 + (-(Work.Spaces.gam α))) = (2 * α / 3 - Work.Spaces.gam α) by ring]
        ring

/-- Every term of `HkIntegrand` vanishes where `sin(2θ) = 0`. -/
theorem HkIntegrand_eq_zero_of_sin_two_eq_zero {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hα : 0 < α) (h : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α k f z θ = 0 := by
  have h1 : ∀ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = 0 := by
    intro i hi
    rw [h, Real.zero_rpow (by linarith [Work.Spaces.eta_pos] : Work.Spaces.eta / 2 ≠ 0),
      div_zero, mul_zero]
    ring
  have h2 : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) = 0 := by
    intro i hi j hj
    split_ifs with hc
    · rw [Work.Spaces.Wt, Work.Spaces.wTheta, h,
        Real.zero_rpow (by intro hz; have := Work.Spaces.gam_pos hα; linarith), mul_zero,
        mul_zero]
      ring
    · rfl
  rw [Work.Spaces.HkIntegrand, Finset.sum_eq_zero h1,
    Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero (h2 i hi), add_zero]


/-! ## The assembly

Given the two computational cores, the `ℋ⁴`-norm of the `Γ`-term is bounded by a
universal constant times `α²`.  The proof separates variables
(`F = Kfac α · ρ(z) · ψ(θ)`) and uses the two cores term by term inside
`HkIntegrand`, then integrates: the `z`-integral of `(1+z)^{-4}` is `≤ 2`
(`Work.Elliptic.WtoH_IntZ`) and the `θ`-integrals are bounded by
`Work.Spaces.sin_two_rpow`. -/

theorem H4N_GammaTerm_le_of_cores (M D : ℝ) (hM : 0 < M) (hD : 0 < D)
    (hMr : ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 ≤ z →
      |(Work.Spaces.Zop^[j] rhoR) z * Work.Spaces.w z| ≤ M / (1 + z) ^ 2)
    (hDl : ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(Work.Spaces.Lop^[i] (psiA α)) θ|
          ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      H4N α
        (fun z θ => 8 * α ^ 2 * c2m θ * z ^ 2 * Work.Spaces.Gam α θ
          / (Work.Spaces.c α * (1 + z) ^ 4)) ≤ C * α ^ 2 := by
  set Cθ : ℝ := (20 + 50 * D ^ 2) * 10000 + 50 * D ^ 2 * (3000 / 17) with hCθdef
  have hCθ : 0 < Cθ := by rw [hCθdef]; positivity
  refine ⟨Real.sqrt (6400 * M ^ 2 * (2 * Cθ)), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro α hα hα1
  have hc1 : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hMnn : 0 ≤ M := hM.le
  have hDnn : 0 ≤ D := hD.le
  -- the two short hands
  set Kf : ℝ := Kfac α with hKfdef
  have hKfnn : 0 ≤ Kf := by rw [hKfdef, Kfac]; positivity
  have hKfSq : Kf ^ 2 ≤ 6400 * α ^ 4 := by
    have hc2 : (1 / 100 : ℝ) ≤ (Work.Spaces.c α) ^ 2 := by nlinarith
    have hα4 : (0:ℝ) < α ^ 4 := pow_pos hα 4
    rw [hKfdef, Kfac, div_pow]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (Work.Spaces.c α) ^ 2)]
    nlinarith [hc2, hα4]
  set F : ℝ → ℝ → ℝ := fun z θ => 8 * α ^ 2 * c2m θ * z ^ 2 * Work.Spaces.Gam α θ
      / (Work.Spaces.c α * (1 + z) ^ 4) with hFdef
  have hFsep : F = sepF (fun z => Kf * rhoR z) (psiA α) := by
    funext z θ
    rw [hFdef, hKfdef]
    simp only [sepF, Kfac, rhoR, psiA]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
    ring
  set Big : ℝ → ℝ := fun θ => (20 + 50 * D ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + 50 * D ^ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) with hBigdef
  -- pointwise bound on the integrand
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 F z θ
        ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2 * Big θ := by
    intro z hz θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
    have h1z : 0 < 1 + z := by have hz0 : (0:ℝ) ≤ z := hz; linarith
    rcases em (θ ∈ Set.Ioo 0 (π / 2)) with hθi | hθi
    · -- interior: use the two cores termwise
      have hbnd : ∀ j : ℕ, j ≤ 4 →
          ((Work.Spaces.Zop^[j] rhoR) z * Work.Spaces.w z) ^ 2 ≤ (M / (1 + z) ^ 2) ^ 2 := by
        intro j hj
        have hb := hMr j hj z hz
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0:ℝ) ≤ M / (1 + z) ^ 2)]
        exact hb
      have hψ2 : (psiA α θ) ^ 2 ≤ 4 := by
        have h := mul_self_le_mul_self (abs_nonneg (psiA α θ)) (psiA_abs_le_two hα hθ)
        have h2 := sq_abs (psiA α θ)
        nlinarith [h, h2]
      have hpure : ∀ i : ℕ, i ≤ 4 →
          (Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
        intro i hi
        have hsep : Work.Spaces.DzIter i F z θ
            = Kf * (Work.Spaces.Zop^[i] rhoR) z * psiA α θ := by
          rw [hFsep, sepF_DzIter, Zop_iter_const_mul, sepF]
        have hsq := hbnd i hi
        have hψs : (Kf * psiA α θ) ^ 2 ≤ Kf ^ 2 * 4 := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_left hψ2 (sq_nonneg Kf)
        calc (Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            = ((Work.Spaces.Zop^[i] rhoR) z * Work.Spaces.w z) ^ 2
                * (Kf * psiA α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
              rw [hsep]
              rw [Work.Elliptic.sq_mul_div_sin (z := z) (θ := θ)
                (a := Kf * (Work.Spaces.Zop^[i] rhoR) z * psiA α θ) hθ]
              ring
          _ ≤ (M / (1 + z) ^ 2) ^ 2 * (Kf ^ 2 * 4)
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul hsq hψs (sq_nonneg _) (sq_nonneg _))
                (Real.rpow_nonneg hs0 _)
          _ = Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
                * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
      have hmixed : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 4 →
          (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
            ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
        intro i j hi hij
        have hsep : Work.Spaces.mixed j i F z θ
            = Kf * (Work.Spaces.Zop^[j] rhoR) z * (Work.Spaces.Lop^[i] (psiA α)) θ := by
          rw [hFsep, sepF_mixed, Zop_iter_const_mul, sepF]
        have hsq := hbnd j (by omega)
        have hcore := hDl α hα hα1 i hi (by omega) θ hθi
        have hang := mixed_angle_le hα hα1 hDnn hθ hcore
        calc (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
            = Kf ^ 2 * ((Work.Spaces.Zop^[j] rhoR) z * Work.Spaces.w z) ^ 2
                * (((Work.Spaces.Lop^[i] (psiA α)) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
              rw [hsep, mul_pow, Work.Spaces.bt_Wt_sq α z θ hα hθ]
              ring
          _ ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
                * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                    + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hsq (sq_nonneg Kf)) hang
                (by positivity) (by positivity)
      rw [Work.Spaces.HkIntegrand]
      have hZsum : (∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (20 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
        calc ∑ i ∈ Finset.range (4 + 1),
              (Work.Spaces.DzIter i F z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            ≤ ∑ _i ∈ Finset.range (4 + 1),
                (Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
                  * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) :=
              Finset.sum_le_sum fun i hi =>
                hpure i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
          _ = 5 * (Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
                  * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              norm_num
          _ = Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
                  * (20 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
      have hMsum : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (50 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
        set Y : ℝ := Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
            * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) with hYdef
        have hYnn : 0 ≤ Y := by rw [hYdef]; positivity
        calc ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
            ≤ ∑ _i ∈ Finset.range (4 + 1), ∑ _j ∈ Finset.range (4 + 1), Y :=
              Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
                by_cases hc : 1 ≤ i ∧ i + j ≤ 4
                · rw [if_pos hc]; exact hmixed i j hc.1 hc.2
                · rw [if_neg hc]; exact hYnn
          _ = 25 * Y := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
          _ = Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (50 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
              rw [hYdef]; ring
      calc ∑ i ∈ Finset.range (4 + 1),
              (Work.Spaces.DzIter i F z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            + ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (20 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (50 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) :=
            add_le_add hZsum hMsum
        _ = Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2 * Big θ := by simp only [hBigdef]; ring
    · -- boundary: every term vanishes
      have hs : Real.sin (2 * θ) = 0 :=
        Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
      rw [HkIntegrand_eq_zero_of_sin_two_eq_zero hα hs]
      have h0 : Big θ = 0 := by
        simp only [hBigdef, hs,
          Real.zero_rpow (by linarith [Work.Spaces.eta_pos] : (-(Work.Spaces.eta)) ≠ 0),
          Real.zero_rpow (by rw [Work.Spaces.gam]; intro hh; linarith :
            (2 * α / 3 - Work.Spaces.gam α) ≠ 0)]
        ring
      rw [h0]; norm_num
  -- integrability and value of the angular majorant
  have hint1 : Integrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by linarith [Work.Spaces.eta_lt_one])
      (by linarith [Work.Spaces.eta_nonneg])).1
  have hval1 : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ≤ 10000 := by
    have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_nonneg])).2
    have hden : (-(Work.Spaces.eta)) + 1 = 1 / 100 := by rw [Work.Spaces.eta]; norm_num
    rw [hden] at h
    norm_num at h
    linarith
  have hp : 2 * α / 3 - Work.Spaces.gam α = -1 + 17 * α / 30 := by
    rw [Work.Spaces.gam]; ring
  have hpe1 : -1 < 2 * α / 3 - Work.Spaces.gam α := by rw [hp]; linarith
  have hpe2 : 2 * α / 3 - Work.Spaces.gam α ≤ 0 := by rw [hp]; linarith
  have hint2 : Integrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
      (volume.restrict Work.Spaces.Iθ) :=
    (Work.Spaces.sin_two_rpow (2 * α / 3 - Work.Spaces.gam α) hpe1 hpe2).1
  have hnn2 : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _
  have hval2 : α ^ 2 * (∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) ≤ 3000 / 17 := by
    have h := (Work.Spaces.sin_two_rpow (2 * α / 3 - Work.Spaces.gam α) hpe1 hpe2).2
    have hden : (2 * α / 3 - Work.Spaces.gam α) + 1 = 17 * α / 30 := by
      rw [Work.Spaces.gam]; ring
    rw [hden] at h
    calc α ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
        ≤ α ^ 2 * (100 / (17 * α / 30)) := mul_le_mul_of_nonneg_left h (sq_nonneg α)
      _ = 3000 * α / 17 := by field_simp; ring
      _ ≤ 3000 / 17 := by nlinarith [hα1]
  have hBignnI : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Big θ := by
    intro θ hθ
    simp only [hBigdef]
    exact add_nonneg
      (mul_nonneg (by positivity) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _))
      (mul_nonneg (by positivity) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _))
  have hBignn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Big θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc hBignnI
  have hBigint : Integrable (fun θ : ℝ => Big θ) (volume.restrict Work.Spaces.Iθ) := by
    simp only [hBigdef]
    exact (hint1.const_mul _).add (hint2.const_mul _)
  have hBigval : ∫ θ in Work.Spaces.Iθ, Big θ ≤ Cθ := by
    simp only [hBigdef, hCθdef]
    rw [MeasureTheory.integral_add (hint1.const_mul _) (hint2.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have h1 : (20 + 50 * D ^ 2) * (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ (20 + 50 * D ^ 2) * 10000 := mul_le_mul_of_nonneg_left hval1 (by positivity)
    have h2 : 50 * D ^ 2 * α ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
        ≤ 50 * D ^ 2 * (3000 / 17) := by
      calc 50 * D ^ 2 * α ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
          = 50 * D ^ 2 * (α ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by ring
        _ ≤ 50 * D ^ 2 * (3000 / 17) := mul_le_mul_of_nonneg_left hval2 (by positivity)
    linarith
  -- the `z`-integral of the weight
  have hzmeas : AEStronglyMeasurable (fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    measurability
  have hzint : Integrable (fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    refine Integrable.mono' Work.Elliptic.WtoH_IntZ.1 hzmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    have hz0 : (0:ℝ) ≤ z := hz
    have h2 : 1 / (1 + z) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have h3 : (0:ℝ) ≤ 1 / (1 + z) ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [h2, h3]
  have hWint : 0 ≤ ∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ici fun z hz => by positivity
  have hzval : ∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2 ≤ 2 := by
    have hle : (fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2)
        ≤ᵐ[volume.restrict Work.Spaces.Iz] (fun z : ℝ => 1 / (1 + z) ^ 2) := by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      have hz0 : (0:ℝ) ≤ z := hz
      have h2 : 1 / (1 + z) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      have h3 : (0:ℝ) ≤ 1 / (1 + z) ^ 2 := by positivity
      nlinarith [h2, h3]
    exact le_trans (MeasureTheory.integral_mono_of_nonneg
        (Eventually.of_forall fun z => by positivity) Work.Elliptic.WtoH_IntZ.1 hle)
      Work.Elliptic.WtoH_IntZ.2
  -- the inner integral identity
  have hinner_eq : ∀ z : ℝ, ∫ θ in Work.Spaces.Iθ,
        Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2 * Big θ
      = Kf ^ 2 * M ^ 2 * (∫ θ in Work.Spaces.Iθ, Big θ) * (1 / (1 + z) ^ 2) ^ 2 := by
    intro z
    rw [MeasureTheory.integral_const_mul]
    ring
  have houter_eq : ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2 * Big θ
      = Kf ^ 2 * M ^ 2 * (∫ θ in Work.Spaces.Iθ, Big θ)
          * (∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2) := by
    rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2 * Big θ)
        = fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2
            * (Kf ^ 2 * M ^ 2 * (∫ θ in Work.Spaces.Iθ, Big θ)) from by
      funext z; rw [hinner_eq z]; ring]
    rw [MeasureTheory.integral_mul_const]
    ring
  have hMajint : Integrable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2 * Big θ) (volume.restrict Work.Spaces.Iz) := by
    rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2 * Big θ)
        = fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2
            * (Kf ^ 2 * M ^ 2 * (∫ θ in Work.Spaces.Iθ, Big θ)) from by
      funext z; rw [hinner_eq z]; ring]
    exact hzint.mul_const _
  -- the `ℋ⁴`-square bound
  have hHkSq : Work.Spaces.HkSq α 4 F ≤ 6400 * M ^ 2 * (2 * Cθ) * α ^ 4 := by
    rw [Work.Spaces.HkSq]
    have hstep : ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 F z θ
        ≤ Kf ^ 2 * M ^ 2 * (∫ θ in Work.Spaces.Iθ, Big θ)
            * (∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2) := by
      calc ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F z θ
          ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
              Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2 * Big θ :=
            MeasureTheory.integral_mono_of_nonneg
              (Eventually.of_forall fun z => MeasureTheory.setIntegral_nonneg measurableSet_Icc
                (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 F z θ))
              hMajint
              (ae_restrict_of_forall_mem measurableSet_Ici
                (fun z hz => MeasureTheory.integral_mono_of_nonneg
                  (ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ =>
                    Work.Spaces.HkIntegrand_nonneg α 4 F z θ))
                  (hBigint.const_mul _)
                  (ae_restrict_of_forall_mem measurableSet_Icc (hpt z hz))))
        _ = Kf ^ 2 * M ^ 2 * (∫ θ in Work.Spaces.Iθ, Big θ)
            * (∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2) := houter_eq
    have hA : Kf ^ 2 * M ^ 2 * (∫ θ in Work.Spaces.Iθ, Big θ) ≤ Kf ^ 2 * M ^ 2 * Cθ :=
      mul_le_mul_of_nonneg_left hBigval (by positivity)
    have h1 : Kf ^ 2 * M ^ 2 * (∫ θ in Work.Spaces.Iθ, Big θ)
          * (∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2) ≤ Kf ^ 2 * M ^ 2 * Cθ * 2 :=
      mul_le_mul hA hzval hWint (by positivity)
    have h2 : Kf ^ 2 * M ^ 2 * Cθ * 2 ≤ 6400 * M ^ 2 * (2 * Cθ) * α ^ 4 := by
      have hnn : (0:ℝ) ≤ M ^ 2 * Cθ * 2 := by positivity
      calc Kf ^ 2 * M ^ 2 * Cθ * 2 = Kf ^ 2 * (M ^ 2 * Cθ * 2) := by ring
        _ ≤ (6400 * α ^ 4) * (M ^ 2 * Cθ * 2) := mul_le_mul_of_nonneg_right hKfSq hnn
        _ = 6400 * M ^ 2 * (2 * Cθ) * α ^ 4 := by ring
    linarith
  rw [H4N, Work.Spaces.HkNorm]
  calc Real.sqrt (Work.Spaces.HkSq α 4 F)
      ≤ Real.sqrt (6400 * M ^ 2 * (2 * Cθ) * α ^ 4) := Real.sqrt_le_sqrt hHkSq
    _ = Real.sqrt (6400 * M ^ 2 * (2 * Cθ)) * α ^ 2 := by
        rw [Real.sqrt_mul (by positivity),
          show Real.sqrt (α ^ 4) = α ^ 2 by
            rw [show α ^ 4 = (α ^ 2) ^ 2 by ring]
            exact Real.sqrt_sq (by positivity)]

/-- **The requested lemma**: the `ℋ⁴`-norm of the `Γ`-term
`8α²c2m(θ)z²Γ(θ)/(c(α)(1+z)⁴)` is `O(α²)`, uniformly for `0 < α ≤ 1` (the "direct
calculation" of Elgindi, tex 1398--1402, for `I^{N₀}_1 + I^{N₀}_2`). -/
theorem H4N_GammaTerm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Construction.H4N α
        (fun z θ => 8 * α ^ 2 * Work.Construction.c2m θ * z ^ 2 * Work.Spaces.Gam α θ
          / (Work.Spaces.c α * (1 + z) ^ 4)) ≤ C * α ^ 2 := by
  obtain ⟨M, hM, hMr⟩ := H4N_GammaTerm_rho_bound
  obtain ⟨D, hD, hDl⟩ := H4N_GammaTerm_Lop_bound
  exact H4N_GammaTerm_le_of_cores M D hM hD hMr hDl

end Work.Construction
