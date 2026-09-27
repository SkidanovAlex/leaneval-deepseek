import Mathlib
import Submission.Work.EKLProd.prodBox_div_subset_shape
import Submission.Work.EKLProd.ProdFlowerDefs
import Submission.Work.EKLComp.LeafDefs

namespace Work.EKLProd

/-- **The shapes of a product-box flower grow with the radius, uniformly on the base, with an
explicit constant.**  This is the `∃C`-free form of `Work.EKLProd.prodBox_div_subset_shape`: the
constant `C = 10⁹` displayed there is the one produced by its proof (the two arithmetic side
conditions `hineqA`, `hineqB` hold for it whenever `hf.R ≥ 5000`), so the same argument runs
verbatim with the existential instantiated at `10⁹`. -/
theorem prodBox_div_subset_shape_exp {H T U : Subgroup Work.EKLContract.SL3} (hTH : T ≤ H) (hUH : U ≤ H) (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1) (t₀ : Fin 3 → ℝ) (hcent : ∀ g ∈ T, Work.EKLContract.aDiag t₀ * g = g * Work.EKLContract.aDiag t₀) (hcontr : ∀ u ∈ U, Filter.Tendsto (fun k : ℕ => Work.EKLContract.aDiag t₀ ^ k * u * (Work.EKLContract.aDiag t₀ ^ k)⁻¹) Filter.atTop (nhds 1)) {μ : MeasureTheory.Measure Work.EKLContract.X3} (hf : Work.EKLProd.ProdFlowerFam H T U μ) (hR : 5000 ≤ hf.R) (n : ℕ) {x : Work.EKLContract.X3} (hx : x ∈ hf.Z n) {t : Work.EKLContract.SL3} (ht : t ∈ Work.EKLComp.Ucl H 1) (hco : hf.co n x = t⁻¹) : Work.EKLProd.prodBox T U (hf.R / (10:ℝ)^9) ⊆ Work.EKLContract.shape (hf.mH n) H x := by
  classical
  -- entry bounds on the `T`-coordinate `τ = hT T U t` of the plaque coordinate `t⁻¹`
  have hτb : ∀ i j : Fin 3, |(Work.EKLProd.hT T U t) i j| ≤ 2 ∧
      |(Work.EKLProd.hT T U t) i j - t i j| ≤ 1 :=
    (hT_entry_block_part hcop hdisj t₀ hcent hcontr ht).2
  -- the two arithmetic side conditions for the factor bounds, at `C = 10⁹`
  have hineqA : 3 * (8 * (hf.R / (10 : ℝ) ^ 9)) + 9 < hf.R := by
    have h10 : (10 : ℝ) ^ 9 = 1000000000 := by norm_num
    rw [h10]; linarith
  have hineqB : 3 * (1153 * (48 * (hf.R / (10 : ℝ) ^ 9))) + 1152 < hf.R := by
    have h10 : (10 : ℝ) ^ 9 = 1000000000 := by norm_num
    rw [h10]; linarith
  intro g hg
  obtain ⟨t', ht', u', hu', rfl⟩ := hg
  rw [hf.shapeH n x hx]
  refine ⟨Work.EKLProd.prodBox_subset_H hTH hUH ⟨t', ht', u', hu', rfl⟩, ?_⟩
  rw [hco]
  -- the two factors of `(t' * u') * t⁻¹`
  obtain ⟨hA, hB⟩ :=
    Work.EKLProd.mul_inv_mem_V_of_hT_bounds hcop ⟨t, ht⟩ hineqA hineqB ht'.1 hu'.1 hτb
  obtain ⟨gd, hgdT, ud, hudU, hgdud⟩ := hcop t ht.1
  have hτT₀ : Work.EKLProd.hT T U t ∈ T := Work.EKLProd.hT_mem ⟨gd, hgdT, ud, hudU, hgdud⟩
  have hυU₀ : Work.EKLProd.hU T U t ∈ U := Work.EKLProd.hU_mem ⟨gd, hgdT, ud, hudU, hgdud⟩
  have hdec₀ : Work.EKLProd.hT T U t * Work.EKLProd.hU T U t = t :=
    Work.EKLProd.hT_mul_hU ⟨gd, hgdT, ud, hudU, hgdud⟩
  let τ : Work.EKLContract.SL3 := Work.EKLProd.hT T U t
  let υ : Work.EKLContract.SL3 := Work.EKLProd.hU T U t
  have hdec : τ * υ = t := hdec₀
  have hτT : τ ∈ T := hτT₀
  have hυU : υ ∈ U := hυU₀
  -- the second factor is the `hnorm`-conjugate `τ * (u' * υ⁻¹) * τ⁻¹`
  have hBmem : τ * u' * t⁻¹ ∈ U := by
    have htinv : t⁻¹ = υ⁻¹ * τ⁻¹ := by rw [← hdec, mul_inv_rev]
    have h1 : τ * u' * t⁻¹ = τ * (u' * υ⁻¹) * τ⁻¹ := by rw [htinv]; group
    rw [h1]
    exact hnorm τ hτT (u' * υ⁻¹) (U.mul_mem hu'.2 (U.inv_mem hυU))
  refine ⟨t' * τ⁻¹, ⟨hA, T.mul_mem ht'.2 (T.inv_mem hτT)⟩,
    τ * u' * t⁻¹, ⟨hB, hBmem⟩, ?_⟩
  group

end Work.EKLProd
