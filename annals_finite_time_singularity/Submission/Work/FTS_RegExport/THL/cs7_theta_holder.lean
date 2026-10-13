import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS_RegExport.THL.ropStar_theta_holder
import Submission.Work.FTS_RegExport.THL.vopStar_theta_holder
import Submission.Work.FTS_RegExport.THL.ropPert_theta_holder
import Submission.Work.FTS_RegExport.THL.vopPert_theta_holder
import Submission.Work.FTS_RegExport.THL.cs7_rop_split
import Submission.Work.FTS_RegExport.RXT.Sys.L12FK_family_jets

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set

namespace Work.FTS_RegExport.THL

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp)
open Work.FTS.FinalV2 (gS tauExt)
open Work.FTS.RegExportIface (cs7 psiR phiTil)
open Work.FTS.Final (maxMu)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS_RegExport.RXT (v2_PhiT)
open Work.Construction (Rop PhiTil Ftau Fstar FK)
open Work.FTS.VocabO2 (PhiTs)

/-- Power comparison with a shifted weight: for `0 < P`, `0 ≤ t ≤ P` and `0 < p` with `q ≤ p`,
`t ^ p ≤ P ^ (p - q) * t ^ q`. -/
private lemma rpow_le_const_mul_rpow {P t p q : ℝ} (hP : 0 < P) (ht : 0 ≤ t) (htP : t ≤ P)
    (hp : 0 < p) (hpq : 0 ≤ p - q) :
    t ^ p ≤ P ^ (p - q) * t ^ q := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h, Real.zero_rpow (ne_of_gt hp)]
    exact mul_nonneg (Real.rpow_nonneg hP.le _) (Real.rpow_nonneg le_rfl q)
  · have hdec : t ^ p = t ^ (p - q) * t ^ q := by
      rw [← Real.rpow_add h, show p - q + q = p by ring]
    rw [hdec]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht htP hpq) (Real.rpow_nonneg ht q)

theorem cs7_theta_holder {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    {g : Work.FTS.Galerkin.Fam} (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∀ S > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), ∀ θ' ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
        |Work.FTS.RegExportIface.cs7 (Work.FTS.Regularity.pExp α)
            (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g)
            (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
            (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) z θ τ
          - Work.FTS.RegExportIface.cs7 (Work.FTS.Regularity.pExp α)
            (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g)
            (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
            (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) z θ' τ|
          ≤ K * |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20) := by
  intro S hS
  have hαG : 0 < pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- ### the star slot of `ℛ` (A4) at `αG = pExp α`
  obtain ⟨Csta, hCsta0, hSta⟩ :=
    ropStar_theta_holder (αG := pExp α) (Cs := Cs) hαG hαG1 hStar
  -- ### the perturbation slot of `ℛ` (A5)
  obtain ⟨M, hM0, hPert⟩ :=
    ropPert_theta_holder (α := α) (Ce := Ce) (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hSol hOK S hS
  -- ### the uniform bound on the angular moment `𝔽K(F(τ))`
  obtain ⟨CFK, hCFK0, hFK1, -, -, -, -⟩ :=
    Work.FTS_RegExport.RXT.Sys.L12FK_family_jets (α := α) (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
      hα hα13 hOK.2 S hS
  have hFKb : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      |FK (Ftau (pExp α) (gS α (tauExt g)) τ) z| ≤ CFK := by
    intro τ hτ z hz
    simpa only [Work.Spaces.DzIter_zero] using hFK1 τ hτ 0 (by norm_num) z hz
  have hPpos : (0:ℝ) < Real.pi / 2 := by positivity
  refine ⟨2 * (Real.pi / 2) ^ (1 - pExp α / 20) * CFK
      + 2 * Csta * (Real.pi / 2) ^ (3 * (pExp α / 20))
      + 2 * M, ?_, ?_⟩
  · -- ### nonnegativity of the constant
    have h1 : (0:ℝ) ≤ (Real.pi / 2) ^ (1 - pExp α / 20) := Real.rpow_nonneg hPpos.le _
    have h2 : (0:ℝ) ≤ (Real.pi / 2) ^ (3 * (pExp α / 20)) := Real.rpow_nonneg hPpos.le _
    exact add_nonneg
      (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) hCFK0)
        (mul_nonneg (mul_nonneg (by norm_num) hCsta0) h2))
      (mul_nonneg (by norm_num) hM0)
  · -- ### the Hölder estimate
    intro τ hτ z hz θ hθ θ' hθ'
    have hε0 : (0:ℝ) ≤ pExp α / 20 := div_nonneg hαG.le (by norm_num)
    have hε1 : pExp α / 20 ≤ 1 := by
      rw [Work.FTS.Regularity.pExp]; linarith
    have hΔ0 : (0:ℝ) ≤ |θ - θ'| := abs_nonneg _
    have hΔP : |θ - θ'| ≤ Real.pi / 2 := by
      rw [abs_le]
      constructor <;> linarith [hθ.1, hθ.2, hθ'.1, hθ'.2]
    have hΔε0 : (0:ℝ) ≤ |θ - θ'| ^ (pExp α / 20) := Real.rpow_nonneg hΔ0 _
    -- ## the two exponent comparisons
    have hconv_sin : |θ - θ'|
        ≤ (Real.pi / 2) ^ (1 - pExp α / 20) * |θ - θ'| ^ (pExp α / 20) := by
      simpa using rpow_le_const_mul_rpow (P := Real.pi / 2) (t := |θ - θ'|) (p := 1)
        (q := pExp α / 20) hPpos hΔ0 hΔP (by norm_num) (by linarith)
    have hpq : pExp α / 5 - pExp α / 20 = 3 * (pExp α / 20) := by
      rw [Work.FTS.Regularity.pExp]; ring
    have hconv_star : |θ - θ'| ^ (pExp α / 5)
        ≤ (Real.pi / 2) ^ (3 * (pExp α / 20)) * |θ - θ'| ^ (pExp α / 20) := by
      have h := rpow_le_const_mul_rpow (P := Real.pi / 2) (t := |θ - θ'|) (p := pExp α / 5)
        (q := pExp α / 20) hPpos hΔ0 hΔP (div_pos hαG (by norm_num)) (by rw [hpq]; positivity)
      rwa [hpq] at h
    -- ## the `sin²` term
    have hsin : |Real.sin θ ^ 2 - Real.sin θ' ^ 2| ≤ 2 * |θ - θ'| := by
      have hs : Real.sin θ ^ 2 - Real.sin θ' ^ 2
          = (Real.sin θ - Real.sin θ') * (Real.sin θ + Real.sin θ') := by ring
      rw [hs, abs_mul]
      have h1 : |Real.sin θ - Real.sin θ'| ≤ |θ - θ'| := Real.abs_sin_sub_sin_le θ θ'
      have h2 : |Real.sin θ + Real.sin θ'| ≤ 2 := by
        calc |Real.sin θ + Real.sin θ'| ≤ |Real.sin θ| + |Real.sin θ'| := abs_add_le _ _
          _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one θ) (Real.abs_sin_le_one θ')
          _ = 2 := by norm_num
      calc |Real.sin θ - Real.sin θ'| * |Real.sin θ + Real.sin θ'|
          ≤ |θ - θ'| * 2 := mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)
        _ = 2 * |θ - θ'| := by ring
    have hsin2 : |Real.sin θ ^ 2 - Real.sin θ' ^ 2|
        ≤ 2 * ((Real.pi / 2) ^ (1 - pExp α / 20) * |θ - θ'| ^ (pExp α / 20)) := by
      calc |Real.sin θ ^ 2 - Real.sin θ' ^ 2| ≤ 2 * |θ - θ'| := hsin
        _ ≤ 2 * ((Real.pi / 2) ^ (1 - pExp α / 20) * |θ - θ'| ^ (pExp α / 20)) :=
            mul_le_mul_of_nonneg_left hconv_sin (by norm_num)
    -- ## the definitional identity for `cs7` (the `θ`-free terms cancel)
    have hKey : cs7 (pExp α) (maxMu (pExp α) (PsiCan Φs E g) g) (gS α (tauExt g))
          (psiR α Φs E (tauExt g)) z θ τ
        - cs7 (pExp α) (maxMu (pExp α) (PsiCan Φs E g) g) (gS α (tauExt g))
          (psiR α Φs E (tauExt g)) z θ' τ
        = (Real.sin θ ^ 2 - Real.sin θ' ^ 2) * FK (Ftau (pExp α) (gS α (tauExt g)) τ) z
          - 2 * (Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
                 - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ') := by
      have hφ : ∀ a b : ℝ,
          Rop (pExp α) (phiTil (pExp α) (gS α (tauExt g)) (psiR α Φs E (tauExt g)) τ) a b
            = Rop (pExp α) (v2_PhiT α Φs E g τ) a b := fun a b => rfl
      simp only [cs7]
      simp only [hφ]
      ring
    -- ## the `ℛ`-difference: split into star + perturbation and apply A4/A5
    have hRop : |Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
          - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ'|
        ≤ Csta * ((Real.pi / 2) ^ (3 * (pExp α / 20)) * |θ - θ'| ^ (pExp α / 20))
          + M * |θ - θ'| ^ (pExp α / 20) := by
      have hsub : Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
            - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ'
          = (Rop (pExp α) (PhiTs (pExp α) Φs) z θ - Rop (pExp α) (PhiTs (pExp α) Φs) z θ')
            + (Rop (pExp α) (PhiTil (pExp α) (slice g τ) (E (slice g τ))) z θ
               - Rop (pExp α) (PhiTil (pExp α) (slice g τ) (E (slice g τ))) z θ') := by
        rw [cs7_rop_split hα hα13 hEL3 hStar hOK τ hτ.1 z θ hz hθ.1 hθ.2,
          cs7_rop_split hα hα13 hEL3 hStar hOK τ hτ.1 z θ' hz hθ'.1 hθ'.2]
        ring
      have htri : |Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
            - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ'|
          ≤ |Rop (pExp α) (PhiTs (pExp α) Φs) z θ - Rop (pExp α) (PhiTs (pExp α) Φs) z θ'|
            + |Rop (pExp α) (PhiTil (pExp α) (slice g τ) (E (slice g τ))) z θ
               - Rop (pExp α) (PhiTil (pExp α) (slice g τ) (E (slice g τ))) z θ'| := by
        rw [hsub]
        exact abs_add_le _ _
      refine le_trans htri (add_le_add ?_ ?_)
      · exact le_trans (hSta z hz θ hθ θ' hθ') (mul_le_mul_of_nonneg_left hconv_star hCsta0)
      · refine le_trans (hPert τ hτ z hz θ hθ θ' hθ') ?_
        have hstep : M * min z 1 * |θ - θ'| ^ (pExp α / 20)
            ≤ M * |θ - θ'| ^ (pExp α / 20) := by
          have h1 : M * min z 1 ≤ M * 1 := mul_le_mul_of_nonneg_left (min_le_right z 1) hM0
          rw [mul_one] at h1
          exact mul_le_mul_of_nonneg_right h1 hΔε0
        exact hstep
    -- ## the two summands of the difference
    have hFKterm : |Real.sin θ ^ 2 - Real.sin θ' ^ 2|
          * |FK (Ftau (pExp α) (gS α (tauExt g)) τ) z|
        ≤ 2 * ((Real.pi / 2) ^ (1 - pExp α / 20) * |θ - θ'| ^ (pExp α / 20)) * CFK :=
      mul_le_mul hsin2 (hFKb τ hτ z hz) (abs_nonneg _)
        (mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg hPpos.le _) hΔε0))
    have h2term : 2 * |Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
          - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ'|
        ≤ 2 * (Csta * ((Real.pi / 2) ^ (3 * (pExp α / 20)) * |θ - θ'| ^ (pExp α / 20))
          + M * |θ - θ'| ^ (pExp α / 20)) :=
      mul_le_mul_of_nonneg_left hRop (by norm_num)
    -- ## the triangle inequality and the final normalisation
    have hcomb : |(Real.sin θ ^ 2 - Real.sin θ' ^ 2)
            * FK (Ftau (pExp α) (gS α (tauExt g)) τ) z
          - 2 * (Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
                 - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ')|
        ≤ 2 * ((Real.pi / 2) ^ (1 - pExp α / 20) * |θ - θ'| ^ (pExp α / 20)) * CFK
          + 2 * (Csta * ((Real.pi / 2) ^ (3 * (pExp α / 20)) * |θ - θ'| ^ (pExp α / 20))
              + M * |θ - θ'| ^ (pExp α / 20)) := by
      have h1 : |(Real.sin θ ^ 2 - Real.sin θ' ^ 2)
            * FK (Ftau (pExp α) (gS α (tauExt g)) τ) z|
          = |Real.sin θ ^ 2 - Real.sin θ' ^ 2|
            * |FK (Ftau (pExp α) (gS α (tauExt g)) τ) z| := abs_mul _ _
      have h2 : |(2:ℝ) * (Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
            - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ')|
          = 2 * |Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
            - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ'| := by
        rw [abs_mul, show |(2:ℝ)| = 2 by norm_num]
      have htri : |(Real.sin θ ^ 2 - Real.sin θ' ^ 2)
              * FK (Ftau (pExp α) (gS α (tauExt g)) τ) z
            - 2 * (Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
                   - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ')|
          ≤ |Real.sin θ ^ 2 - Real.sin θ' ^ 2|
              * |FK (Ftau (pExp α) (gS α (tauExt g)) τ) z|
            + 2 * |Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
                   - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ'| := by
        rw [abs_sub_le_iff]
        constructor <;>
          linarith [h1, h2,
            le_abs_self ((Real.sin θ ^ 2 - Real.sin θ' ^ 2)
              * FK (Ftau (pExp α) (gS α (tauExt g)) τ) z),
            neg_abs_le ((Real.sin θ ^ 2 - Real.sin θ' ^ 2)
              * FK (Ftau (pExp α) (gS α (tauExt g)) τ) z),
            le_abs_self (2 * (Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
              - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ')),
            neg_abs_le (2 * (Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
              - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ'))]
      exact le_trans htri (add_le_add hFKterm h2term)
    rw [hKey]
    refine le_trans hcomb (le_of_eq ?_)
    ring

end Work.FTS_RegExport.THL
