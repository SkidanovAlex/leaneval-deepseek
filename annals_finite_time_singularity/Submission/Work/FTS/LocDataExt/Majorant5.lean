/-
# `Work.FTS.LocDataExt.Majorant5` — the pointwise `ℋ⁵`-majorants and the order-`5` membership

The design (`Submission/Work/FTS/N45_DESIGN_LEAD.md` §2.4, §6, node `N9-ext`) asks for the
localised datum in the class `RegQ α 5`, i.e. `SmoothQuad ∧ HkMem α 5 ∧ BdryTraces α 5`.  The
traces are `Traces.lean`'s (`bdryTraces_locG`, at `k = 5` with the angular jet bound
`DthIter_Gam_abs_le5`); this module supplies the **`ℋ⁵`-membership**.

Since `locG` is *separable*, `locG = locR(z)·Γ(θ)`, the whole content is a pointwise bound of the
`ℋ⁵`-integrand by the integrable majorant `K·angMaj α θ/(1+z)²`, exactly as in the delivered
order-`4` chapter of N9, with the two new jets (one more `D_z`-derivative of the two radial
factors, one more `D_θ`-derivative of `Γ`):

* `HkIntegrand_sepGam_le` — the generic term-by-term bound for a separable datum
  `ρ(z)·Γ(θ)`, from a radial bound `((D_z^jρ)(z)·w z)² ≤ R/(1+z)²` and an angular bound
  `(D_θ^iΓ)² ≤ Rθ·Γ²`;
* `DzIter_bumpZ_bound5` — the `D_z`-jets of the bump `bumpZ = χ(4·-5)` up to order `5` are
  bounded (the delivered bound stops at `4`);
* `hB_bumpZ5`, `hLoc_majorant5` — the radial bound and the majorant of the bump;
* `hB_zfar5`, `zfar_hB5` — the same for the far factor `-(α/c)·zfarR L`: on `[L,2L]` from the
  (delegated) uniform jet bound `zfarR_jet_le5`, beyond `2L` from the jets of `FM.Fstar`
  (where `zfarR` agrees with `FM.Fstar`), below `L` from the vanishing of the cut-off;
* `HkIntegrand_locG_le5`, `HkMem_locG5` — the assembly for `locG`, and the membership.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.LocDataExt.SepFactor
import Submission.Work.FTS.LocDataExt.DthIter_Gam_abs_le5
import Submission.Work.FTS.LocData.Main
import Submission.Work.FTS.LocData.hLoc_hk

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocDataExt

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The generic separable majorant -/

/-- The angular jet bound `(D_θ^iΓ)² ≤ 10¹⁰·Γ²` on `Iθ`, for `i ≤ 5`, from
`DthIter_Gam_abs_le5`. -/
theorem hGam5 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {i : ℕ} (hi : i ≤ 5) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
      ≤ (10 : ℝ) ^ 10 * (Work.Spaces.Gam α θ) ^ 2 := by
  have h := DthIter_Gam_abs_le5 i hi α hα hα1 hθ
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs, mul_pow] at h2
  have h10 : ((100000 : ℝ)) ^ 2 = (10 : ℝ) ^ 10 := by norm_num
  calc (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
      ≤ (100000 : ℝ) ^ 2 * (Work.Spaces.Gam α θ) ^ 2 := h2
    _ = (10 : ℝ) ^ 10 * (Work.Spaces.Gam α θ) ^ 2 := by rw [h10]

/-- **The generic pointwise majorant of the `ℋ^k`-integrand of a separable datum.**  If the
radial factor satisfies `((D_z^jρ)(z)·w z)² ≤ R/(1+z)²` for `j ≤ k` and the angular factor the
jet bound `(D_θ^iΓ)² ≤ Rθ·Γ²` for `i ≤ k`, then the `ℋ^k`-integrand of `ρ(z)·Γ(θ)` is bounded
by `((k+1) + (k+1)²Rθ)·R·angMaj α θ/(1+z)²`. -/
theorem HkIntegrand_sepGam_le (α : ℝ) (hα : 0 < α) (k : ℕ) {ρ : ℝ → ℝ} {R Rθ : ℝ}
    (hR : 0 ≤ R) (hRθ : 0 ≤ Rθ)
    (hB : ∀ j ≤ k, ∀ z ∈ Work.Spaces.Iz, ∀ θ' : ℝ,
      (Work.Spaces.DzIter j (fun z _ => ρ z) z θ' * Work.Spaces.w z) ^ 2 ≤ R / (1 + z) ^ 2)
    (hΓ : ∀ i ≤ k, ∀ θ' ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ') ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ') ^ 2)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => ρ z * Work.Spaces.Gam α θ) z θ
      ≤ (((k + 1 : ℕ) : ℝ) + (((k + 1) ^ 2 : ℕ) : ℝ) * Rθ) * R
          * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.LocData.ZFBase.sin_two_nonneg_Iθ hθ
  have hang0 : 0 ≤ Work.FTS.LocData.angMaj α θ := Work.FTS.LocData.angMaj_nonneg hθ
  have hden : 0 ≤ (1 + z) ^ 2 := by positivity
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  -- the `D_z`-block
  have hT1 : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => ρ z * Work.Spaces.Gam α θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ∑ _i ∈ Finset.range (k + 1), (R / (1 + z) ^ 2 * Work.FTS.LocData.angMaj α θ) := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hik : i ≤ k := by rw [Finset.mem_range] at hi; omega
    rw [congrFun (congrFun (DzIter_sepGam α ρ i) z) θ,
      Work.FTS.LocData.sep_sq1 (Work.Spaces.DzIter i (fun z _ => ρ z) z θ)
        (Work.Spaces.Gam α θ) (Work.Spaces.w z) (Real.sin (2 * θ)) (Work.Spaces.eta) hs0]
    have h1 := hB i hik z hz θ
    have h2 : (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ Work.FTS.LocData.angMaj α θ :=
      Work.FTS.LocData.Gam_sq_rpow_le_angMaj_eta α hθ
    have h3 : 0 ≤ (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
    exact mul_le_mul h1 h2 h3 (by positivity)
  -- the mixed block
  have hT2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => ρ z * Work.Spaces.Gam α θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ ∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1),
          (R * Rθ * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) := by
    refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => ?_))
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc]
      rw [Finset.mem_range] at hi hj
      rw [congrFun (congrFun (mixed_sepGam α ρ j i) z) θ, Work.Spaces.Wt, Work.Spaces.wTheta,
        Work.FTS.LocData.sep_sq2 (Work.Spaces.DzIter j (fun z _ => ρ z) z θ)
          (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) (Work.Spaces.w z)
          (Real.sin (2 * θ)) (Work.Spaces.gam α) hs0]
      have h1 := hB j (by omega) z hz θ
      have h2 := hΓ i (by omega) θ hθ
      have h3 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs0 _
      have h4 : 0 ≤ (Work.Spaces.DzIter j (fun z _ => ρ z) z θ * Work.Spaces.w z) ^ 2 :=
        sq_nonneg _
      calc (Work.Spaces.DzIter j (fun z _ => ρ z) z θ * Work.Spaces.w z) ^ 2
            * ((Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ (R / (1 + z) ^ 2) * (Rθ * (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^
              (-(Work.Spaces.gam α))) := by
            refine mul_le_mul h1 ?_ (mul_nonneg (sq_nonneg _) h3) (by positivity)
            exact mul_le_mul_of_nonneg_right h2 h3
        _ = R * Rθ * (((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
              / (1 + z) ^ 2 := by ring
        _ ≤ R * Rθ * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
            refine div_le_div_of_nonneg_right ?_ hden
            exact mul_le_mul_of_nonneg_left (Work.FTS.LocData.Gam_sq_rpow_le_angMaj_gam α hθ)
              (by positivity)
    · rw [if_neg hc]
      exact div_nonneg (mul_nonneg (mul_nonneg hR hRθ) hang0) hden
  -- putting the two blocks together
  have hHk : Work.Spaces.HkIntegrand α k (fun z θ => ρ z * Work.Spaces.Gam α θ) z θ
      = (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => ρ z * Work.Spaces.Gam α θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i (fun z θ => ρ z * Work.Spaces.Gam α θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0) := rfl
  rw [hHk]
  refine le_trans (add_le_add hT1 hT2) ?_
  have h1 : (∑ _i ∈ Finset.range (k + 1), (R / (1 + z) ^ 2 * Work.FTS.LocData.angMaj α θ))
      = ((k + 1 : ℕ) : ℝ) * (R * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have h2 : (∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1),
        (R * Rθ * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2))
      = (((k + 1) ^ 2 : ℕ) : ℝ) * (Rθ * (R * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  rw [h1, h2]
  have h3 : (0 : ℝ) ≤ R * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 :=
    div_nonneg (mul_nonneg hR hang0) hden
  have h4 : ((k + 1 : ℕ) : ℝ) ≤ (((k + 1 : ℕ) : ℝ) + (((k + 1) ^ 2 : ℕ) : ℝ) * Rθ) := by
    have : (0 : ℝ) ≤ (((k + 1) ^ 2 : ℕ) : ℝ) * Rθ := by positivity
    linarith
  have h5 : ((k + 1 : ℕ) : ℝ) * (R * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)
        + (((k + 1) ^ 2 : ℕ) : ℝ) * (Rθ * (R * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2))
      ≤ (((k + 1 : ℕ) : ℝ) + (((k + 1) ^ 2 : ℕ) : ℝ) * Rθ)
          * (R * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) := by
    nlinarith [h3, hRθ, h4, Nat.cast_nonneg (α := ℝ) (k + 1),
      Nat.cast_nonneg (α := ℝ) ((k + 1) ^ 2)]
  refine le_trans h5 ?_
  rw [show (((k + 1 : ℕ) : ℝ) + (((k + 1) ^ 2 : ℕ) : ℝ) * Rθ)
        * (R * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)
      = (((k + 1 : ℕ) : ℝ) + (((k + 1) ^ 2 : ℕ) : ℝ) * Rθ) * R
        * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 from by ring]

/-! ## The bump at order `5` -/

/-- The `D_z`-jets of the bump `bumpZ = χ(4·-5)` up to order `5` are bounded. -/
theorem DzIter_bumpZ_bound5 :
    ∃ C : ℝ, ∀ c : ℕ, c ≤ 5 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => Work.FTS.LocData.bumpZ z) z θ| ≤ C := by
  classical
  refine ⟨∑ c ∈ Finset.range 6,
    Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c), ?_⟩
  intro c hc z _ θ
  have hM : ∀ d : ℕ, 0 ≤ Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d) ∧
      ∀ w : ℝ, |(Work.FTS.LocData.T1^[d]) Work.FTS.LocData.bumpZ w|
        ≤ Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d) :=
    fun d => Classical.choose_spec (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d)
  rw [Work.FTS.LocData.DzIter_bumpZ_eq c θ z]
  have h1 : |(Work.FTS.LocData.T1^[c]) Work.FTS.LocData.bumpZ z|
      ≤ Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c) := (hM c).2 z
  have h2 : Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c)
      ≤ ∑ d ∈ Finset.range 6,
          Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d) :=
    Finset.single_le_sum (fun d _ => (hM d).1) (Finset.mem_range.mpr (by omega))
  linarith

/-- The radial bound needed by `HkIntegrand_sepGam_le` for the bump `bumpZ`. -/
theorem hB_bumpZ5 :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ j ≤ 5, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ * Work.Spaces.w z) ^ 2
        ≤ R / (1 + z) ^ 2 := by
  obtain ⟨D, hD⟩ := DzIter_bumpZ_bound5
  have hD0 : 0 ≤ D := by
    have h := hD 0 (by norm_num) 0 (by simp [Work.Spaces.Iz]) 0
    have h1 : |Work.Spaces.DzIter 0 (fun z _ => Work.FTS.LocData.bumpZ z) 0 0| = 0 := by
      rw [Work.FTS.LocData.DzIter_bumpZ_eq 0 0 0, Function.iterate_zero_apply,
        Work.FTS.LocData.bumpZ_zero, abs_zero]
    linarith [h1 ▸ h]
  refine ⟨D ^ 2 * (1771561 / 1296 : ℝ), by positivity, fun j hj z hz θ => ?_⟩
  by_cases hsupp : z ∈ Set.Icc (3 / 4 : ℝ) (7 / 4)
  · have hw := Work.FTS.LocData.w_sq_le_on_support hsupp
    have h1 : (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ) ^ 2 ≤ D ^ 2 := by
      have h := hD j hj z hz θ
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      rwa [sq_abs] at h2
    rw [mul_pow]
    calc (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2
        ≤ D ^ 2 * ((1771561 / 1296 : ℝ) / (1 + z) ^ 2) :=
          mul_le_mul h1 hw (sq_nonneg _) (by positivity)
      _ = D ^ 2 * (1771561 / 1296 : ℝ) / (1 + z) ^ 2 := by ring
  · rw [Work.FTS.LocData.DzIter_bumpZ_eq j θ z,
      Work.FTS.LocData.T1_iterate_bumpZ_eq_zero hsupp j]
    have hD2 : 0 ≤ D ^ 2 * (1771561 / 1296 : ℝ) / (1 + z) ^ 2 :=
      div_nonneg (mul_nonneg (sq_nonneg D) (by norm_num)) (sq_nonneg _)
    simpa using hD2

/-- The `ℋ⁵`-majorant of the bump `hLoc α = bumpZ·Γ`. -/
theorem hLoc_majorant5 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 5 (Work.FTS.LocData.hLoc α) z θ
        ≤ K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
  obtain ⟨R, hR, hB⟩ := hB_bumpZ5
  refine ⟨(6 + 36 * 10 ^ 10) * R, by positivity, fun z hz θ hθ => ?_⟩
  have hΓ : ∀ i ≤ 5, ∀ θ' ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ') ^ 2
        ≤ (10 : ℝ) ^ 10 * (Work.Spaces.Gam α θ') ^ 2 :=
    fun i hi θ' hθ' => hGam5 α hα hα1 hi hθ'
  have hmain := HkIntegrand_sepGam_le α hα 5 (ρ := fun z => Work.FTS.LocData.bumpZ z)
    (R := R) (Rθ := (10 : ℝ) ^ 10) hR (by positivity) hB hΓ hz hθ
  have hfun : (fun z θ => Work.FTS.LocData.bumpZ z * Work.Spaces.Gam α θ)
      = Work.FTS.LocData.hLoc α := by
    funext z θ
    rw [Work.FTS.LocData.hLoc_apply]
  rw [hfun] at hmain
  refine hmain.trans_eq ?_
  push_cast
  ring

end Work.FTS.LocDataExt
