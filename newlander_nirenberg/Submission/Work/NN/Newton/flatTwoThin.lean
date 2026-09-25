import Mathlib
import Submission.Work.NN.Newton.FTdefs
import Submission.Work.NN.Newton.FTcut.ftBmRow_bound
import Submission.Work.NN.Newton.FTs2.ftS2_bound
import Submission.Work.NN.Newton.FTedat.ftEdat_bound_sum
import Submission.Work.NN.Newton.FTscale.dilateNorm_le
import Submission.Work.NN.Newton.FTscale.dilate_dbarCoord

namespace Work.NN.Newton

open scoped ENNReal ContDiff
open Set

/-- The thin-gap `(0,2)`-Poincaré statement on the unit polydisc, obtained from the assembly and
the three quantitative estimates. -/
theorem flatTwoThin_one {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4)
      (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ j l (m : ℕ), ContDiffOn ℝ m (η j l) (Work.CR.Flat.polydisc 0 (fun _ => 1))) →
      (∀ j l z, η j l z = - η l j z) →
      (∀ j l k z, z ∈ Work.CR.Flat.polydisc 0 (fun _ => 1) →
        Work.CR.Flat.dbarCoord j (η l k) z - Work.CR.Flat.dbarCoord l (η j k) z
          + Work.CR.Flat.dbarCoord k (η j l) z = 0) →
      ∃ ψ : Fin n → (Fin n → ℂ) → ℂ,
        (∀ j (m : ℕ), ContDiffOn ℝ m (ψ j) (Work.CR.Flat.polydisc 0 (fun _ => 1 - δ))) ∧
        (∀ j l z, z ∈ Work.CR.Flat.polydisc 0 (fun _ => 1 - δ) →
          Work.CR.Flat.dbarCoord j (ψ l) z - Work.CR.Flat.dbarCoord l (ψ j) z = η j l z) ∧
        (∀ j, Work.CR.Flat.holderNorm 1 α (ψ j) (Work.CR.Flat.polydisc 0 (fun _ => 1 - δ))
          ≤ ENNReal.ofReal (C / δ ^ N) * ∑ j, ∑ l,
              Work.CR.Flat.holderNorm 0 α (η j l) (Work.CR.Flat.polydisc 0 (fun _ => 1))) :=
  flatTwoThin_assembly hn hα0 hα1
    (Work.NN.Newton.FTcut.ftBmRow_bound hn hα0 hα1)
    (Work.NN.Newton.FTs2.ftS2_bound hn hα0 hα1)
    (Work.NN.Newton.FTedat.ftEdat_bound_sum hn hα0 hα1)

/-- Transport of the unit-polydisc result to arbitrary radii `r ∈ [1/2, 4]`. -/
theorem flatTwoThin_of_one {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (h1 : ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4)
      (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ j l (m : ℕ), ContDiffOn ℝ m (η j l) (Work.CR.Flat.polydisc 0 (fun _ => 1))) →
      (∀ j l z, η j l z = - η l j z) →
      (∀ j l k z, z ∈ Work.CR.Flat.polydisc 0 (fun _ => 1) →
        Work.CR.Flat.dbarCoord j (η l k) z - Work.CR.Flat.dbarCoord l (η j k) z
          + Work.CR.Flat.dbarCoord k (η j l) z = 0) →
      ∃ ψ : Fin n → (Fin n → ℂ) → ℂ,
        (∀ j (m : ℕ), ContDiffOn ℝ m (ψ j) (Work.CR.Flat.polydisc 0 (fun _ => 1 - δ))) ∧
        (∀ j l z, z ∈ Work.CR.Flat.polydisc 0 (fun _ => 1 - δ) →
          Work.CR.Flat.dbarCoord j (ψ l) z - Work.CR.Flat.dbarCoord l (ψ j) z = η j l z) ∧
        (∀ j, Work.CR.Flat.holderNorm 1 α (ψ j) (Work.CR.Flat.polydisc 0 (fun _ => 1 - δ))
          ≤ ENNReal.ofReal (C / δ ^ N) * ∑ j, ∑ l,
              Work.CR.Flat.holderNorm 0 α (η j l) (Work.CR.Flat.polydisc 0 (fun _ => 1)))) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ (r δ : ℝ), 1 / 2 ≤ r → r ≤ 4 → 0 < δ → δ ≤ 1 / 4 →
      ∀ (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
        (∀ j l (m : ℕ), ContDiffOn ℝ m (η j l) (Work.CR.Flat.polydisc 0 (fun _ => r))) →
        (∀ j l z, η j l z = - η l j z) →
        (∀ j l k z, z ∈ Work.CR.Flat.polydisc 0 (fun _ => r) →
          Work.CR.Flat.dbarCoord j (η l k) z - Work.CR.Flat.dbarCoord l (η j k) z
            + Work.CR.Flat.dbarCoord k (η j l) z = 0) →
        ∃ ψ : Fin n → (Fin n → ℂ) → ℂ,
          (∀ j (m : ℕ), ContDiffOn ℝ m (ψ j) (Work.CR.Flat.polydisc 0 (fun _ => r * (1 - δ)))) ∧
          (∀ j l z, z ∈ Work.CR.Flat.polydisc 0 (fun _ => r * (1 - δ)) →
            Work.CR.Flat.dbarCoord j (ψ l) z - Work.CR.Flat.dbarCoord l (ψ j) z = η j l z) ∧
          (∀ j, Work.CR.Flat.holderNorm 1 α (ψ j)
              (Work.CR.Flat.polydisc 0 (fun _ => r * (1 - δ)))
            ≤ ENNReal.ofReal (C / δ ^ N) * ∑ j, ∑ l,
                Work.CR.Flat.holderNorm 0 α (η j l)
                  (Work.CR.Flat.polydisc 0 (fun _ => r))) := by
  obtain ⟨C₁, hC₁0, N₁, h1⟩ := h1
  refine ⟨512 * C₁ + 1, by positivity, N₁, ?_⟩
  intro r δ hr1 hr4 hδ0 hδ4 η hη hanti hcl
  have hr0 : 0 < r := by linarith
  set lam : ℝ := 1 / r with hlamdef
  have hlam0 : 0 < lam := by positivity
  have hlamr : lam * r = 1 := by rw [hlamdef]; field_simp
  have hlamr2 : r * lam = 1 := by rw [mul_comm]; exact hlamr
  -- membership transfers
  have hmem1 : ∀ w : Fin n → ℂ, w ∈ Work.CR.Flat.polydisc 0 (fun _ => 1) →
      (lam⁻¹ • w) ∈ Work.CR.Flat.polydisc 0 (fun _ => r) := by
    intro w hw
    refine (smul_mem_polydisc_iff (inv_pos.mpr hlam0) (fun _ => r) w).mpr ?_
    have h2 : (fun _ : Fin n => r / lam⁻¹) = fun _ => (1 : ℝ) := by
      funext j
      rw [div_eq_mul_inv, show (lam⁻¹)⁻¹ = lam by rw [inv_inv]]
      exact hlamr2
    rw [h2]
    exact hw
  have hmem2 : ∀ z : Fin n → ℂ, z ∈ Work.CR.Flat.polydisc 0 (fun _ => r * (1 - δ)) →
      (lam • z) ∈ Work.CR.Flat.polydisc 0 (fun _ => 1 - δ) := by
    intro z hz
    refine (smul_mem_polydisc_iff hlam0 (fun _ => 1 - δ) z).mpr ?_
    have h2 : (fun _ : Fin n => (1 - δ) / lam) = fun _ => r * (1 - δ) := by
      funext j
      rw [div_eq_mul_inv, show lam⁻¹ = r by rw [hlamdef]; field_simp]
      ring
    rw [h2]
    exact hz
  have hcomp_inner : ∀ j l (m : ℕ), ContDiffOn ℝ m (fun w : Fin n → ℂ => η j l (lam⁻¹ • w))
      (Work.CR.Flat.polydisc 0 (fun _ => 1)) := by
    intro j l m
    exact (hη j l m).comp
      ((contDiff_const_smul (lam⁻¹) : ContDiff ℝ m (fun w : Fin n → ℂ => lam⁻¹ • w)).contDiffOn)
      hmem1
  -- the dilated datum
  have hη'sm : ∀ j l (m : ℕ), ContDiffOn ℝ m
      (fun w : Fin n → ℂ => (lam : ℂ) * η j l (lam⁻¹ • w))
      (Work.CR.Flat.polydisc 0 (fun _ => 1)) :=
    fun j l m => contDiffOn_const.mul (hcomp_inner j l m)
  have hη'anti : ∀ j l z, (lam : ℂ) * η j l (lam⁻¹ • z)
      = - ((lam : ℂ) * η l j (lam⁻¹ • z)) := by
    intro j l z
    rw [hanti l j]
    ring
  have hη'cl : ∀ j l k z, z ∈ Work.CR.Flat.polydisc 0 (fun _ => 1) →
      Work.CR.Flat.dbarCoord j (fun w : Fin n → ℂ => (lam : ℂ) * η l k (lam⁻¹ • w)) z
        - Work.CR.Flat.dbarCoord l (fun w : Fin n → ℂ => (lam : ℂ) * η j k (lam⁻¹ • w)) z
        + Work.CR.Flat.dbarCoord k (fun w : Fin n → ℂ => (lam : ℂ) * η j l (lam⁻¹ • w)) z = 0 := by
    intro j l k z hz
    have hzr := hmem1 z hz
    have hcoef : (lam : ℂ) * ((lam⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hlam0)]
      norm_num
    have hkey : ∀ (a : Fin n) (f : (Fin n → ℂ) → ℂ),
        Work.CR.Flat.dbarCoord a (fun w : Fin n → ℂ => (lam : ℂ) * f (lam⁻¹ • w)) z
          = Work.CR.Flat.dbarCoord a f (lam⁻¹ • z) := by
      intro a f
      rw [Work.NN.Newton.FTscale.dilate_dbarCoord (inv_pos.mpr hlam0) a (c := (lam : ℂ)) f z,
        hcoef, one_mul]
    rw [hkey j (η l k), hkey l (η j k), hkey k (η j l)]
    exact hcl j l k (lam⁻¹ • z) hzr
  obtain ⟨ψ', hψ'sm, hψ'eq, hψ'bd⟩ :=
    h1 δ hδ0 hδ4 (fun j l w => (lam : ℂ) * η j l (lam⁻¹ • w)) hη'sm hη'anti hη'cl
  -- the datum estimate
  have hdat : (∑ j : Fin n, ∑ l : Fin n,
        Work.CR.Flat.holderNorm 0 α (fun w : Fin n → ℂ => (lam : ℂ) * η j l (lam⁻¹ • w))
          (Work.CR.Flat.polydisc 0 (fun _ => 1)))
      ≤ ENNReal.ofReal (lam * max 1 (r ^ α))
        * ∑ j : Fin n, ∑ l : Fin n, Work.CR.Flat.holderNorm 0 α (η j l)
            (Work.CR.Flat.polydisc 0 (fun _ => r)) := by
    calc (∑ j : Fin n, ∑ l : Fin n,
          Work.CR.Flat.holderNorm 0 α (fun w : Fin n → ℂ => (lam : ℂ) * η j l (lam⁻¹ • w))
            (Work.CR.Flat.polydisc 0 (fun _ => 1)))
        ≤ ∑ j : Fin n, ∑ l : Fin n, ENNReal.ofReal (lam * max 1 (r ^ α))
            * Work.CR.Flat.holderNorm 0 α (η j l) (Work.CR.Flat.polydisc 0 (fun _ => r)) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ =>
            (Work.NN.Newton.FTscale.dilateNorm_le (n := n) hα0.le hlam0 hr0 hlamr).1 _
      _ = ENNReal.ofReal (lam * max 1 (r ^ α))
            * ∑ j : Fin n, ∑ l : Fin n, Work.CR.Flat.holderNorm 0 α (η j l)
                (Work.CR.Flat.polydisc 0 (fun _ => r)) := by
          rw [Finset.mul_sum]
          congr 1
          ext j
          rw [Finset.mul_sum]
  -- the transported candidate
  refine ⟨fun j z => (r : ℂ) ^ 2 * ψ' j (lam • z), ?_, ?_, ?_⟩
  · -- smoothness
    intro j m
    exact contDiffOn_const.mul
      ((hψ'sm j m).comp
        ((contDiff_const_smul lam : ContDiff ℝ m (fun z : Fin n → ℂ => lam • z)).contDiffOn)
        hmem2)
  · -- the equation
    intro j l z hz
    have hz2 := hmem2 z hz
    have hback : lam⁻¹ • (lam • z) = z := by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hlam0), one_smul]
    have hgoal : Work.CR.Flat.dbarCoord j (ψ' l) (lam • z)
        - Work.CR.Flat.dbarCoord l (ψ' j) (lam • z) = (lam : ℂ) * η j l z := by
      have h := hψ'eq j l (lam • z) hz2
      rwa [hback] at h
    have hcoef : ((r : ℂ) * (lam : ℂ)) * ((r : ℂ) * (lam : ℂ)) = 1 := by
      rw [← Complex.ofReal_mul, hlamr2]
      norm_num
    have hkey : ∀ (a : Fin n) (f : (Fin n → ℂ) → ℂ),
        Work.CR.Flat.dbarCoord a (fun z : Fin n → ℂ => (r : ℂ) ^ 2 * f (lam • z)) z
          = (r : ℂ) ^ 2 * ((lam : ℂ) * Work.CR.Flat.dbarCoord a f (lam • z)) :=
      fun a f => by
        simpa only [mul_assoc] using
          (Work.NN.Newton.FTscale.dilate_dbarCoord hlam0 a (c := (r : ℂ) ^ 2) f z)
    rw [hkey j (ψ' l), hkey l (ψ' j)]
    rw [show (r : ℂ) ^ 2 * ((lam : ℂ) * Work.CR.Flat.dbarCoord j (ψ' l) (lam • z))
        - (r : ℂ) ^ 2 * ((lam : ℂ) * Work.CR.Flat.dbarCoord l (ψ' j) (lam • z))
        = ((r : ℂ) ^ 2 * (lam : ℂ))
          * (Work.CR.Flat.dbarCoord j (ψ' l) (lam • z)
              - Work.CR.Flat.dbarCoord l (ψ' j) (lam • z)) from by ring]
    rw [hgoal]
    rw [show ((r : ℂ) ^ 2 * (lam : ℂ)) * ((lam : ℂ) * η j l z)
        = (((r : ℂ) * (lam : ℂ)) * ((r : ℂ) * (lam : ℂ))) * η j l z from by ring]
    rw [hcoef, one_mul]

  · -- the bound
    intro j
    have hbd := hψ'bd j
    have hscl := (Work.NN.Newton.FTscale.dilateNorm_le (n := n) hα0.le hlam0 hr0 hlamr).2 hδ0 (ψ' j)
    have hnum : r ^ 2 * max 1 (lam ^ ((1 : ℝ) + α)) * (lam * max 1 (r ^ α)) ≤ 512 := by
      have h1a : lam ^ ((1 : ℝ) + α) ≤ 4 := by
        have h2 : lam ≤ 2 := by rw [hlamdef, div_le_iff₀ hr0]; linarith
        calc lam ^ ((1 : ℝ) + α) ≤ 2 ^ ((1 : ℝ) + α) :=
              Real.rpow_le_rpow hlam0.le h2 (by positivity)
          _ ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) (by linarith)
          _ = 4 := by norm_num
      have h1b : r ^ α ≤ 4 := by
        calc r ^ α ≤ 4 ^ α := Real.rpow_le_rpow (by linarith) hr4 hα0.le
          _ ≤ 4 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (x := 4) (by norm_num) hα1.le
          _ = 4 := Real.rpow_one 4
      have hA : max 1 (lam ^ ((1 : ℝ) + α)) ≤ 4 := max_le (by norm_num) h1a
      have hB : max 1 (r ^ α) ≤ 4 := max_le (by norm_num) h1b
      have hC : r ^ 2 ≤ 16 := by nlinarith
      have hlam2 : lam ≤ 2 := by rw [hlamdef, div_le_iff₀ hr0]; linarith
      have hmax1 : (0:ℝ) ≤ lam ^ ((1 : ℝ) + α) := Real.rpow_nonneg hlam0.le _
      have hmax2 : (0:ℝ) ≤ r ^ α := Real.rpow_nonneg (by linarith) _
      have hprod : max 1 (lam ^ ((1 : ℝ) + α)) * (lam * max 1 (r ^ α)) ≤ 32 := by
        have h1 : lam * max 1 (r ^ α) ≤ 2 * 4 :=
          mul_le_mul hlam2 hB (le_trans zero_le_one (le_max_left _ _)) (by norm_num)
        calc max 1 (lam ^ ((1 : ℝ) + α)) * (lam * max 1 (r ^ α)) ≤ 4 * (2 * 4) :=
              mul_le_mul hA h1 (by positivity) (by norm_num)
          _ = 32 := by norm_num
      calc r ^ 2 * max 1 (lam ^ ((1 : ℝ) + α)) * (lam * max 1 (r ^ α))
          = r ^ 2 * (max 1 (lam ^ ((1 : ℝ) + α)) * (lam * max 1 (r ^ α))) := by ring
        _ ≤ 16 * 32 := mul_le_mul hC hprod (by positivity) (by norm_num)
        _ = 512 := by norm_num
    calc Work.CR.Flat.holderNorm 1 α
          (fun z : Fin n → ℂ => (r : ℂ) ^ 2 * ψ' j (lam • z))
          (Work.CR.Flat.polydisc 0 (fun _ => r * (1 - δ)))
        ≤ ENNReal.ofReal (r ^ 2 * max 1 (lam ^ ((1 : ℝ) + α)))
          * Work.CR.Flat.holderNorm 1 α (ψ' j)
              (Work.CR.Flat.polydisc 0 (fun _ => 1 - δ)) := hscl
      _ ≤ ENNReal.ofReal (r ^ 2 * max 1 (lam ^ ((1 : ℝ) + α)))
          * (ENNReal.ofReal (C₁ / δ ^ N₁) * ∑ j, ∑ l,
              Work.CR.Flat.holderNorm 0 α (fun w : Fin n → ℂ => (lam : ℂ) * η j l (lam⁻¹ • w))
                (Work.CR.Flat.polydisc 0 (fun _ => 1))) :=
          mul_le_mul_right hbd (ENNReal.ofReal (r ^ 2 * max 1 (lam ^ ((1 : ℝ) + α))))
      _ ≤ ENNReal.ofReal (r ^ 2 * max 1 (lam ^ ((1 : ℝ) + α)))
          * (ENNReal.ofReal (C₁ / δ ^ N₁) * (ENNReal.ofReal (lam * max 1 (r ^ α))
              * ∑ j : Fin n, ∑ l : Fin n, Work.CR.Flat.holderNorm 0 α (η j l)
                  (Work.CR.Flat.polydisc 0 (fun _ => r)))) :=
          mul_le_mul_right (mul_le_mul_right hdat (ENNReal.ofReal (C₁ / δ ^ N₁)))
            (ENNReal.ofReal (r ^ 2 * max 1 (lam ^ ((1 : ℝ) + α))))
      _ = ENNReal.ofReal (r ^ 2 * max 1 (lam ^ ((1 : ℝ) + α)) * (C₁ / δ ^ N₁
            * (lam * max 1 (r ^ α))))
          * ∑ j : Fin n, ∑ l : Fin n, Work.CR.Flat.holderNorm 0 α (η j l)
              (Work.CR.Flat.polydisc 0 (fun _ => r)) := by
          rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (512 * C₁ / δ ^ N₁)
          * ∑ j : Fin n, ∑ l : Fin n, Work.CR.Flat.holderNorm 0 α (η j l)
              (Work.CR.Flat.polydisc 0 (fun _ => r)) := by
          refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
          calc r ^ 2 * max 1 (lam ^ ((1 : ℝ) + α)) * (C₁ / δ ^ N₁ * (lam * max 1 (r ^ α)))
              = (r ^ 2 * max 1 (lam ^ ((1 : ℝ) + α)) * (lam * max 1 (r ^ α)))
                  * (C₁ / δ ^ N₁) := by ring
            _ ≤ 512 * (C₁ / δ ^ N₁) := mul_le_mul_of_nonneg_right hnum (by positivity)
            _ = 512 * C₁ / δ ^ N₁ := by ring
      _ ≤ ENNReal.ofReal ((512 * C₁ + 1) / δ ^ N₁)
          * ∑ j : Fin n, ∑ l : Fin n, Work.CR.Flat.holderNorm 0 α (η j l)
              (Work.CR.Flat.polydisc 0 (fun _ => r)) := by
          refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
          have hpos : 0 < δ ^ N₁ := by positivity
          rw [div_le_div_iff₀ hpos hpos]
          nlinarith

/-- **Thin-gap `(0,2)`-Poincaré on concentric polydiscs, with a polynomial constant.**

For a smooth antisymmetric `(0,2)`-form `η` which is `∂̄`-closed on the polydisc of radius `r`,
there is a smooth `(0,1)`-form `ψ` on the polydisc of radius `r (1 - δ)` with
`∂̄_j ψ_l - ∂̄_l ψ_j = η_{jl}` there and the gain `C^{0,α} → C^{1,α}`, with a constant `C / δ ^ N`.
This is `Work.NN.Final.flatTwoTunableLinear` (proved, every ratio `c > 1`, unspecified constant)
with the dependence of the constant on the ratio made explicit. -/
theorem flatTwoThin {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ r δ : ℝ, 1 / 2 ≤ r → r ≤ 4 → 0 < δ → δ ≤ 1 / 4 →
      ∀ η : Fin n → Fin n → Work.NN.Core.Cn n → ℂ,
        (∀ j l, ∀ m : ℕ, ContDiffOn ℝ m (η j l)
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))) →
        (∀ j l z, η j l z = - η l j z) →
        (∀ j l k z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) →
          Work.CR.Flat.dbarCoord j (η l k) z - Work.CR.Flat.dbarCoord l (η j k) z
            + Work.CR.Flat.dbarCoord k (η j l) z = 0) →
        ∃ ψ : Fin n → Work.NN.Core.Cn n → ℂ,
          (∀ j, ∀ m : ℕ, ContDiffOn ℝ m (ψ j)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)))) ∧
          (∀ j l z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)) →
            Work.CR.Flat.dbarCoord j (ψ l) z - Work.CR.Flat.dbarCoord l (ψ j) z = η j l z) ∧
          (∀ j, Work.CR.Flat.holderNorm 1 α (ψ j)
              (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)))
            ≤ ENNReal.ofReal (C / δ ^ N) *
              ∑ j, ∑ l, Work.CR.Flat.holderNorm 0 α (η j l)
                (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))) :=
  flatTwoThin_of_one hn hα0 hα1 (flatTwoThin_one hn hα0 hα1)

end Work.NN.Newton
