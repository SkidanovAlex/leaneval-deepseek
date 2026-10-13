import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Majorant6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.RawE6Aux

open MeasureTheory Set Filter

/-- **The `𝒲^{6,∞}`-priced level-six product, in squared-norm form.**  For a coefficient `A` which
is `C^∞` on the open quadrant and `𝒲^{6,∞}` with `WlInf α 6 A ≤ K` (the price carried by the star
fields of `StarPkg6`, e.g. `Rop α (PhiTs α Φs)`, `Vop (PhiTs α Φs)`,
`Uop α (PhiTs α Φs)/sin 2θ` and their `(z+1)/z`-weighted versions) and a datum `P` which is `C^∞`
on the open quadrant and honest in `ℋ⁶`, the level-six energy of the product is linear in the
level-six energy of `P`:
`HkSq α 6 (A·P) ≤ C α^{-1} K² (1 + HkSq α 6 P)`
(the `α^{-1}` is forced by the `(γ-1)^{-1} = 10/α` factor of the majorant; in the application
`K = O(α)` for the star fields, so the net factor is `O(α)`).

Route: the pointwise majorant `H6Rows.WProd6.prod_majorant_winf6`
(`HkIntegrand α 6 (A·P) ≤ (7Cz+49Cm)·(WlInf α 6 A)²·GmajW6 α P`) followed by the integral bound
`H6Rows.WProd6.GmajW6_z_integral_le`
(`∫∫ GmajW6 α P ≤ (1 + 700(1 + 6(γ-1)⁻¹))·HkSq α 6 P`); monotone integration plus `HkSq_nonneg`.
(The membership half is the proved `H6Pair6Aux.HkMem_mul_of_WlInf6`.) -/
theorem wlInfMul6 : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (A P : ℝ → ℝ → ℝ) (K : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.WlInfMem α 6 A →
      Work.Spaces.WlInf α 6 A ≤ K →
      Work.FTS.EllipticEst.SmoothOpen P → Work.Spaces.HkMem α 6 P →
      Work.Spaces.HkSq α 6 (fun z θ => A z θ * P z θ)
        ≤ C * α ^ (-(1 : ℝ)) * K ^ 2 * (1 + Work.Spaces.HkSq α 6 P) := by
  -- the three slot constants of the `𝒲^{6,∞}`-priced product rule
  obtain ⟨Cz, hCzpos, hZ⟩ := Work.FTS.StrongPersist.H6Rows.wprod6.zslot_le_winf6
  obtain ⟨CB, _hCBpos, hMe⟩ := Work.FTS.StrongPersist.H6Rows.wprod6.dzIter_w_mean_le6
  obtain ⟨Cm, hCmpos, hMx⟩ := Work.FTS.StrongPersist.H6Rows.wprod6.mslot_le_winf6 CB
  set K0 : ℝ := 7 * Cz + 49 * Cm with hK0def
  have hK0pos : 0 < K0 := by rw [hK0def]; linarith
  refine ⟨50000 * K0 + 1, by positivity, ?_⟩
  intro α hα A P K hA hAm hAK hP hPm
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hWnn : 0 ≤ Work.Spaces.WlInf α 6 A := Work.Spaces.WlInf_nonneg α 6 A hAm
  have hKnn : 0 ≤ K := le_trans hWnn hAK
  have hPnn : 0 ≤ Work.Spaces.HkSq α 6 P := Work.Spaces.HkSq_nonneg α 6 P
  -- the pointwise majorant of the `ℋ⁶`-integrand of the product
  have hmajor : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => A z θ * P z θ) z θ
        ≤ K0 * (Work.Spaces.WlInf α 6 A) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α P z θ := by
    intro z hz θ hθ
    rw [hK0def]
    exact Work.FTS.StrongPersist.H6Rows.WProd6.prod_majorant_winf6 hα0 hα1 hA hAm hP hPm
      hCzpos hCmpos
      (fun i hi z' θ' hz' hθ1 hθ2 => hZ α A P hα0 hα1 hA hAm hP i hi z' θ' hz' hθ1 hθ2)
      (fun I J hI hIJ z' θ' hz' hθ1 hθ2 =>
        hMx α A P hα0 hα1 hA hAm hP hPm
          (fun d hd z'' θ'' hz'' hθ1' hθ2' =>
            hMe α P d hα0 hα1 hP hPm hd z'' θ'' hz'' hθ1' hθ2')
          I J hI hIJ z' θ' hz' hθ1 hθ2)
      z hz θ hθ
  set Kg : ℝ := 1 + 700 * (1 + 6 * (Work.Spaces.gam α - 1)⁻¹) with hKgdef
  -- the angular integral of the majorant at each radius
  have hbdd : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
          (fun z θ => A z θ * P z θ) z θ)
        ≤ (K0 * (Work.Spaces.WlInf α 6 A) ^ 2 * Kg)
            * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α P z := by
    intro z hz
    have hint : IntegrableOn (fun θ => (K0 * (Work.Spaces.WlInf α 6 A) ^ 2)
        * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α P z θ) Work.Spaces.Iθ :=
      (Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_integrableOn_theta hα0 hα1 hPm hz).const_mul _
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
          (fun z θ => A z θ * P z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (K0 * (Work.Spaces.WlInf α 6 A) ^ 2)
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α P z θ :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ) hint
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hmajor z hz θ hθ))
    rw [MeasureTheory.integral_const_mul] at h1
    have h2 : (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α P z θ)
        ≤ Kg * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α P z := by
      simpa only [hKgdef] using
        Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_theta_integral_le (α := α) (g := P)
          hα0 hα1 hPm hz
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
            (fun z θ => A z θ * P z θ) z θ)
        ≤ (K0 * (Work.Spaces.WlInf α 6 A) ^ 2)
            * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α P z θ) := h1
      _ ≤ (K0 * (Work.Spaces.WlInf α 6 A) ^ 2)
            * (Kg * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α P z) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hK0pos.le (sq_nonneg _))
      _ = (K0 * (Work.Spaces.WlInf α 6 A) ^ 2 * Kg)
            * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α P z := by ring
  -- monotone integration in `z`
  have hdom : IntegrableOn (fun z => (K0 * (Work.Spaces.WlInf α 6 A) ^ 2 * Kg)
      * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α P z) Work.Spaces.Iz :=
    hPm.2.const_mul _
  have hcongr : (∫ z in Work.Spaces.Iz, (K0 * (Work.Spaces.WlInf α 6 A) ^ 2 * Kg)
        * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α P z)
      = (K0 * (Work.Spaces.WlInf α 6 A) ^ 2 * Kg) * Work.Spaces.HkSq α 6 P := by
    rw [MeasureTheory.integral_const_mul,
      Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6_z_integral]
  have hstep1 : Work.Spaces.HkSq α 6 (fun z θ => A z θ * P z θ)
      ≤ (K0 * (Work.Spaces.WlInf α 6 A) ^ 2 * Kg) * Work.Spaces.HkSq α 6 P := by
    rw [Work.Spaces.HkSq, ← hcongr]
    exact setIntegral_mono_of_nonneg
      (fun z _ => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
      (fun z hz => hbdd z hz) hdom
  -- arithmetic: `K0 * Kg ≤ C α^{-1}`, `|A|²_𝒲 ≤ K²`, `HkSq ≥ 0`
  have hKg_le : Kg ≤ 42701 * α⁻¹ := by
    have hsub : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
    have hinv : (Work.Spaces.gam α - 1)⁻¹ = 10 * α⁻¹ := by
      rw [hsub, inv_div, div_eq_mul_inv]
    rw [hKgdef, hinv]
    have h1 : (1 : ℝ) ≤ α⁻¹ := (one_le_inv₀ hα0).mpr hα1
    nlinarith
  have hCKg : K0 * Kg ≤ (50000 * K0 + 1) * α ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg_one]
    calc K0 * Kg ≤ K0 * (42701 * α⁻¹) := mul_le_mul_of_nonneg_left hKg_le hK0pos.le
      _ = (K0 * 42701) * α⁻¹ := by ring
      _ ≤ (50000 * K0 + 1) * α⁻¹ := by
          refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hα0.le)
          nlinarith [hK0pos]
  have hW2K : (Work.Spaces.WlInf α 6 A) ^ 2 ≤ K ^ 2 := by
    have h := mul_self_le_mul_self hWnn hAK
    simpa [sq] using h
  have hfinal : (K0 * (Work.Spaces.WlInf α 6 A) ^ 2 * Kg) * Work.Spaces.HkSq α 6 P
      ≤ (50000 * K0 + 1) * α ^ (-(1 : ℝ)) * K ^ 2 * (1 + Work.Spaces.HkSq α 6 P) := by
    have h1 : (Work.Spaces.WlInf α 6 A) ^ 2 * Work.Spaces.HkSq α 6 P
        ≤ K ^ 2 * (1 + Work.Spaces.HkSq α 6 P) :=
      mul_le_mul hW2K (by linarith) hPnn (sq_nonneg K)
    calc (K0 * (Work.Spaces.WlInf α 6 A) ^ 2 * Kg) * Work.Spaces.HkSq α 6 P
        = (K0 * Kg) * ((Work.Spaces.WlInf α 6 A) ^ 2 * Work.Spaces.HkSq α 6 P) := by ring
      _ ≤ ((50000 * K0 + 1) * α ^ (-(1 : ℝ)))
            * (K ^ 2 * (1 + Work.Spaces.HkSq α 6 P)) :=
          mul_le_mul hCKg h1 (mul_nonneg (sq_nonneg _) hPnn)
            (mul_nonneg (by linarith [hK0pos]) (Real.rpow_nonneg hα0.le _))
      _ = (50000 * K0 + 1) * α ^ (-(1 : ℝ)) * K ^ 2
            * (1 + Work.Spaces.HkSq α 6 P) := by ring
  exact le_trans hstep1 hfinal

end Work.FTS.StrongEps.E4R3.RawE6Aux
