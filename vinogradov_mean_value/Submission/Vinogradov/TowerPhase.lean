/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.PlateLower
import Submission.Vinogradov.DescentLevel
import Submission.Vinogradov.Tower

/-!
# The scale descent with the anisotropic torsion constant (`PlateLower`)

This module is the parallel version of `OneStep.descentStep`, `DescentLevel.lvl2_step` and
`Tower.curveDec_tower` in which the Gram-determinant torsion hypothesis `CurveTorsion` (and its
dimensional constant `tubeK`/`tubeCG`) is replaced by the **scale-covariant** anisotropic
condition `PlateLower` (`PlateLower.lean`).  Only the torsion constant used in the tube lemma
changes; the rest of the two proofs is identical.

The point of the replacement is that `PlateLower` transports under the reparametrisation
`intervalCurve` with the loss `c^l` (`plateLower_intervalCurve`), while the Gram determinant
transports with the loss `c^{l(l+1)}`; the latter would force the tube parameter `ε` (hence the
model enlargement `Λ₁`, hence the induction hypothesis) to depend on the scale.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

theorem descentStepM {l : ℕ} (hl : 1 ≤ l) (D : ℕ → ℝ → E l)
    {ct R : ℝ} (hct : 0 < ct) (hlow : PlateLower l D ct)
    (htay : CurveTaylorTop l D R) (hR : 0 ≤ R)
    {c_I κ : ℝ} (hcI : c_I ∈ Set.Icc (0 : ℝ) 1) (hcIk : c_I + κ ≤ 1) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    {M : ℕ} (hM : 1 ≤ M) {Λ : ℝ} (hΛ : 1 ≤ Λ) {Λ₁ ε : ℝ} (hε : 0 < ε)
    (hΛ₁ : Λ * (1 + ε) * Ctube l ≤ Λ₁)
    {C₁ : ℝ≥0∞} (hdec : DecLinScale l M Λ₁ C₁)
    {ι : Type*} [Fintype ι] {s : Finset ι} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδκ : δ ≤ Λ * (κ / (2 * M)))
    {u : ι → ℝ} (huc : ∀ i ∈ s, |u i - c_I| ≤ κ) (hui : ∀ i ∈ s, u i ∈ Set.Icc (0 : ℝ) 1)
    {blk : ι → Fin M}
    (hblk : ∀ i ∈ s, |u i - (c_I + κ * pieceCenter M (blk i))| ≤ κ / (2 * M))
    (hnum : ∀ i ∈ s, 2 * (R * ((l : ℝ) + 1) * (max δ |u i - c_I|) ^ (l + 1))
      < ε * tubeRhoP l ct (Λ * (κ / (2 * M))))
    {f : ι → E l → ℂ} (hf : ∀ i ∈ s, IsFourierRep l (curvePlate l D δ (u i)) (f i)) :
    lpNorm l (pE l) (fun x => ∑ i ∈ s, f i x)
      ≤ C₁ * l2Norm (fun r : Fin M =>
          lpNorm l (pE l) (fun x => ∑ i ∈ s.filter (fun i => blk i = r), f i x)) := by
  classical
  set σ : ℝ := κ / (2 * M) with hσdef
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hσ0 : 0 < σ := by rw [hσdef]; positivity
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hΛσ1 : (0 : ℝ) < Λ * σ := by positivity
  set cr : Fin M → ℝ := fun r => c_I + κ * pieceCenter M r with hcrdef
  have hcr_mem : ∀ r : Fin M, cr r ∈ Set.Icc (0 : ℝ) 1 := by
    intro r
    have hp0 : 0 ≤ pieceCenter M r := by rw [pieceCenter]; positivity
    have hp1 : pieceCenter M r ≤ 1 := by
      rw [pieceCenter]
      have hlt : ((r : ℕ) : ℝ) + 1 ≤ (M : ℝ) := by
        have := r.isLt
        exact_mod_cast Nat.succ_le_of_lt this
      exact div_le_of_le_mul₀ (by positivity) (by positivity) (by linarith)
    constructor
    · rw [hcrdef]
      nlinarith [hcI.1, hκ0.le, hp0, mul_nonneg hκ0.le hp0]
    · rw [hcrdef]
      have hle : κ * pieceCenter M r ≤ κ := by
        have := mul_le_mul_of_nonneg_left hp1 hκ0.le
        linarith
      linarith [hcIk]
  -- the tube lemma
  have htube : ∀ i ∈ s, curvePlate l D δ (u i)
      ⊆ curvePlate l (taylorDeriv l D c_I) (Λ₁ * σ) (cr (blk i)) := by
    intro i hi
    have h1 := curvePlate_subset_taylorPlate_pl (D := D) hl hct hlow htay hR
      (c_I := c_I) (c := cr (blk i)) (c_i := u i) (δ := δ) (σ := Λ * σ) (ε := ε)
      hcI (hcr_mem (blk i)) (hui i hi) hδ0 hδ1 hΛσ1 hε
      (by
        refine max_le ?_ ?_
        · linarith [hδκ]
        · rw [hcrdef]
          simp only []
          have := hblk i hi
          have h2 : σ ≤ Λ * σ := by nlinarith [hσ0.le, hΛ]
          linarith)
      (by nlinarith [huc i hi, hκ1])
      (by simpa only [hσdef, mul_div_assoc'] using hnum i hi)
    refine subset_trans h1 (curvePlate_mono (D := taylorDeriv l D c_I)
      (δ := (1 + ε) * (Ctube l * (Λ * σ))) (δ' := Λ₁ * σ)
      (mul_nonneg (by linarith) (mul_nonneg (Ctube_pos l).le hΛσ1.le)) ?_)
    nlinarith [hΛ₁, hσ0, hε, hΛ, Ctube_pos l]
  -- the plates of the model, via the straightening map
  have hP : ∀ r : Fin M, curveAff l D κ c_I '' (plate l (Λ₁ / (2 * M)) (pieceCenter M r))
      = curvePlate l (taylorDeriv l D c_I) (Λ₁ * σ) (cr r) := by
    intro r
    rw [curveAff_image_plate, hcrdef, hσdef]
    congr 1
    field_simp
  -- the sub-block sums
  set F : Fin M → E l → ℂ := fun r x => ∑ i ∈ s.filter (fun i => blk i = r), f i x with hFdef
  have hFrep : ∀ r : Fin M,
      IsFourierRep l (curvePlate l (taylorDeriv l D c_I) (Λ₁ * σ) (cr r)) (F r) := by
    intro r
    have hsub : (⋃ i ∈ s.filter (fun i => blk i = r),
          curvePlate l (taylorDeriv l D c_I) (Λ₁ * σ) (cr (blk i)))
        ⊆ curvePlate l (taylorDeriv l D c_I) (Λ₁ * σ) (cr r) := by
      refine Set.iUnion₂_subset fun i hi => ?_
      have hblk_eq : blk i = r := (Finset.mem_filter.mp hi).2
      rw [hblk_eq]
    show IsFourierRep l (curvePlate l (taylorDeriv l D c_I) (Λ₁ * σ) (cr r))
      (fun x => ∑ i ∈ s.filter (fun i => blk i = r), f i x)
    have h := (IsFourierRep.sum (s.filter (fun i => blk i = r))
      (fun i hi => IsFourierRep.mono (htube i (Finset.mem_of_mem_filter i hi))
        (hf i (Finset.mem_of_mem_filter i hi)))).mono hsub
    have hfun : (fun x : E l => ∑ i ∈ s.filter (fun i => blk i = r), f i x)
        = (∑ i ∈ s.filter (fun i => blk i = r), f i) := by
      funext x
      rw [Finset.sum_apply]
    rw [hfun]
    exact h
  -- the straightening linear map and its adjoint
  set Linv : E l →ₗ[ℝ] E l := curveAffLin l D κ c_I with hLinvdef
  set Mt : E l →ₗ[ℝ] E l := LinearMap.adjoint Linv with hMtdef
  have hLinv_inj : Function.Injective Linv :=
    curveAffLin_injective_of_plateLowerAt hct (hlow c_I hcI) hκ0 hκ1
  have hadj : ∀ x y : E l, ⟪Mt x, y⟫ = ⟪x, Linv y⟫ := by
    intro x y
    rw [hMtdef]
    exact LinearMap.adjoint_inner_left Linv y x
  have hHrep : ∀ r : Fin M, IsFourierRep l
      (curveAff l D κ c_I '' plate l (Λ₁ / (2 * M)) (pieceCenter M r)) (F r) := by
    intro r
    rw [hP r]
    exact hFrep r
  have hex : ∀ r : Fin M, ∃ g : E l → ℂ,
      IsFourierRep l (plate l (Λ₁ / (2 * M)) (pieceCenter M r)) g ∧
        F r = fun x => chat l x (D 0 c_I) * g (Mt x) := by
    intro r
    refine exists_isFourierRep_preimage l Linv Mt hadj hLinv_inj (D 0 c_I) ?_
    have h := hHrep r
    rw [show curveAff l D κ c_I = (fun ξ => D 0 c_I + Linv ξ) from by
      funext ξ; rw [curveAff, hLinvdef]] at h
    exact h
  choose G hG hGeq using hex
  -- the model theorem
  have hmodel : lpNorm l (pE l) (fun x => ∑ r, G r x)
      ≤ C₁ * l2Norm (fun r => lpNorm l (pE l) (G r)) := hdec G hG
  -- the change of variables
  have hMt_inj : Function.Injective Mt := by
    intro x y hxy
    have h0 : Mt (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hz : x - y = 0 := by
      have hsurj : Function.Surjective Linv :=
        (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
          (rfl : Module.finrank ℝ (E l) = Module.finrank ℝ (E l))).mp hLinv_inj
      have hperp : ∀ v : E l, ⟪x - y, v⟫ = 0 := by
        intro v
        obtain ⟨w, rfl⟩ := hsurj v
        rw [← hadj (x - y) w, h0, inner_zero_left]
      have hself := hperp (x - y)
      exact inner_self_eq_zero.mp hself
    exact sub_eq_zero.mp hz
  have hdet : LinearMap.det Mt ≠ 0 := by
    intro h0
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, LinearMap.ker_eq_bot.mpr hMt_inj] at h0
    exact h0 rfl
  set kk : ℝ≥0∞ := (ENNReal.ofReal |(LinearMap.det Mt)⁻¹|) ^ (1 / pE l).toReal with hkk
  have hphase : ∀ (A : E l → ℂ), AEStronglyMeasurable A volume →
      lpNorm l (pE l) (fun x => chat l x (D 0 c_I) * A (Mt x)) = kk * lpNorm l (pE l) A :=
    fun A hA => lpNorm_phase_comp_linearMap l (pE_ne_top l) hdet (D 0 c_I) hA
  have hGsum_meas : AEStronglyMeasurable (fun y => ∑ r, G r y) volume :=
    (continuous_finsetSum _ fun r _ => (hG r).continuous).aestronglyMeasurable
  have hLHS : lpNorm l (pE l) (fun x => ∑ r, F r x)
      = kk * lpNorm l (pE l) (fun y => ∑ r, G r y) := by
    have h1 : (fun x => ∑ r, F r x) = fun x => chat l x (D 0 c_I) * (∑ r, G r (Mt x)) := by
      funext x
      have h2 : ∀ r : Fin M, F r x = chat l x (D 0 c_I) * G r (Mt x) :=
        fun r => congrFun (hGeq r) x
      rw [Finset.sum_congr rfl (fun r _ => h2 r), Finset.mul_sum]
    rw [h1]
    exact hphase (fun y => ∑ r, G r y) hGsum_meas
  have hnormF : ∀ r : Fin M, lpNorm l (pE l) (F r) = kk * lpNorm l (pE l) (G r) := by
    intro r
    rw [hGeq r]
    exact hphase (G r) ((hG r).aestronglyMeasurable)
  have hl2 : l2Norm (fun r => lpNorm l (pE l) (F r))
      = kk * l2Norm (fun r => lpNorm l (pE l) (G r)) := by
    have h1 : (fun r => lpNorm l (pE l) (F r)) = fun r => kk * lpNorm l (pE l) (G r) :=
      funext fun r => hnormF r
    rw [h1, l2Norm_mul_const]
  -- the identification of the sums
  have hfiber : (fun x => ∑ r, F r x) = fun x => ∑ i ∈ s, f i x := by
    funext x
    rw [hFdef]
    simp only
    rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := Finset.univ)
      (g := blk) (fun i _ => Finset.mem_univ _) (fun i => f i x)]
  have hfinal : lpNorm l (pE l) (fun x => ∑ r, F r x)
      ≤ C₁ * l2Norm (fun r => lpNorm l (pE l) (F r)) := by
    rw [hLHS, hl2]
    calc kk * lpNorm l (pE l) (fun y => ∑ r, G r y)
        ≤ kk * (C₁ * l2Norm (fun r => lpNorm l (pE l) (G r))) :=
          mul_le_mul_of_nonneg_left hmodel (by simp : (0 : ℝ≥0∞) ≤ kk)
      _ = C₁ * (kk * l2Norm (fun r => lpNorm l (pE l) (G r))) := by ring
  rw [← hfiber]
  exact hfinal

lemma tube_num_condition_Λ_pl {l : ℕ} (hl : 1 ≤ l) {c R ε δ x Λ : ℝ} {n M : ℕ}
    (hM : 1 ≤ M) (hn : 1 ≤ n) (hε : 0 < ε) (hc : 0 < c) (hR : 0 ≤ R)
    (hΛ : 1 ≤ Λ)
    (hx : max δ |x| ≤ Λ / (n : ℝ))
    (ha : 2 * (2 ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1)) ≤ ε * tubeCGP l c)
    (hb : (M : ℝ) ^ l ≤ (Ctube l) ^ l * (n : ℝ)) :
    2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1))
      < ε * tubeRhoP l c (Λ / (2 * ((n * M : ℕ) : ℝ))) := by
  set σ : ℝ := Λ / (2 * ((n * M : ℕ) : ℝ)) with hσ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hs0 : 0 < σ := by rw [hσ]; positivity
  have hCG0 : 0 < tubeCGP l c := tubeCGP_pos hl hc
  have hCt1 : (1 : ℝ) ≤ Ctube l := one_le_Ctube l
  have hCt0 : 0 < Ctube l := Ctube_pos l
  have hMl0 : (0 : ℝ) ≤ (M : ℝ) ^ l := by positivity
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hΛl : (1 : ℝ) ≤ Λ ^ l := one_le_pow₀ hΛ
  -- the condition (b) implies the scaled sub-block constraint
  have h3 : (2 : ℝ) ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1) * (M : ℝ) ^ l
      < ε * tubeCGP l c * (Ctube l) ^ l * (n : ℝ) * Λ ^ l := by
    have hmul1 : (2 * (2 ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1))) * (M : ℝ) ^ l
        ≤ (ε * tubeCGP l c) * (M : ℝ) ^ l := mul_le_mul_of_nonneg_right ha hMl0
    have hmul2 : (ε * tubeCGP l c) * (M : ℝ) ^ l
        ≤ (ε * tubeCGP l c) * ((Ctube l) ^ l * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    have h := le_trans hmul1 hmul2
    have h4 : ε * tubeCGP l c * (Ctube l) ^ l * (n : ℝ)
        ≤ ε * tubeCGP l c * (Ctube l) ^ l * (n : ℝ) * Λ ^ l := by
      have h2 : (0 : ℝ) ≤ ε * tubeCGP l c * (Ctube l) ^ l * (n : ℝ) := by positivity
      nlinarith [h2, hΛl]
    have h5 : (2 * (2 ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1))) * (M : ℝ) ^ l
        = 2 * ((2 : ℝ) ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1) * (M : ℝ) ^ l) := by
      ring
    rw [h5] at h
    have hP : (0 : ℝ) < ε * tubeCGP l c * (Ctube l) ^ l * (n : ℝ) := by positivity
    linarith [h, h4, hP]
  have hx0 : 0 ≤ max δ |x| := le_trans (abs_nonneg x) (le_max_right _ _)
  have hL : 2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1))
      ≤ 2 * (R * ((l : ℝ) + 1)) * Λ ^ (l + 1) / (n : ℝ) ^ (l + 1) := by
    have h1 : (max δ |x|) ^ (l + 1) ≤ (Λ / (n : ℝ)) ^ (l + 1) :=
      pow_le_pow_left₀ hx0 hx _
    rw [div_pow] at h1
    have h2 : R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1)
        ≤ R * ((l : ℝ) + 1) * (Λ ^ (l + 1) / (n : ℝ) ^ (l + 1)) :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg hR (by positivity))
    calc 2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1))
        = 2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1)) := rfl
      _ ≤ 2 * (R * ((l : ℝ) + 1) * (Λ ^ (l + 1) / (n : ℝ) ^ (l + 1))) :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 2 * (R * ((l : ℝ) + 1)) * Λ ^ (l + 1) / (n : ℝ) ^ (l + 1) := by ring
  have hCtsig : (Ctube l * σ) ^ l
      = (Ctube l) ^ l * Λ ^ l / ((2 : ℝ) ^ l * (n : ℝ) ^ l * (M : ℝ) ^ l) := by
    rw [hσ]
    have h : Ctube l * (Λ / (2 * ((n * M : ℕ) : ℝ))) = Ctube l * Λ / (2 * ((n * M : ℕ) : ℝ)) := by
      ring
    rw [h]
    rw [div_pow, mul_pow]
    push_cast
    ring
  have hY : (2 : ℝ) ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1) * (M : ℝ) ^ l * (n : ℝ) ^ l
      < ε * tubeCGP l c * (Ctube l) ^ l * Λ ^ l * (n : ℝ) ^ (l + 1) := by
    have h := mul_lt_mul_of_pos_right h3 (by positivity : (0 : ℝ) < (n : ℝ) ^ l)
    have hp : (n : ℝ) * (n : ℝ) ^ l = (n : ℝ) ^ (l + 1) := by rw [pow_succ']
    have he : ε * tubeCGP l c * (Ctube l) ^ l * (n : ℝ) * Λ ^ l * (n : ℝ) ^ l
        = ε * tubeCGP l c * (Ctube l) ^ l * Λ ^ l * (n : ℝ) ^ (l + 1) := by
      rw [show ε * tubeCGP l c * (Ctube l) ^ l * (n : ℝ) * Λ ^ l * (n : ℝ) ^ l
        = ε * tubeCGP l c * (Ctube l) ^ l * Λ ^ l * ((n : ℝ) * (n : ℝ) ^ l) by ring, hp]
    rwa [he] at h
  rcases le_total (Ctube l * σ) 1 with hcase | hcase
  · have hmin : min (Ctube l * σ) 1 = Ctube l * σ := min_eq_left hcase
    have hρ : tubeCGP l c * (Ctube l * σ) ^ l ≤ tubeRhoP l c σ := by
      have h := tubeRhoP_ge l c σ
      rwa [hmin] at h
    have hgoal : 2 * (R * ((l : ℝ) + 1)) * Λ ^ (l + 1) / (n : ℝ) ^ (l + 1)
        < ε * (tubeCGP l c * ((Ctube l) ^ l * Λ ^ l
            / ((2 : ℝ) ^ l * (n : ℝ) ^ l * (M : ℝ) ^ l))) := by
      have hD : (0 : ℝ) < (2 : ℝ) ^ l * (n : ℝ) ^ l * (M : ℝ) ^ l := by positivity
      rw [show ε * (tubeCGP l c * ((Ctube l) ^ l * Λ ^ l
            / ((2 : ℝ) ^ l * (n : ℝ) ^ l * (M : ℝ) ^ l)))
          = ε * (tubeCGP l c * ((Ctube l) ^ l * Λ ^ l))
            / ((2 : ℝ) ^ l * (n : ℝ) ^ l * (M : ℝ) ^ l) from by ring]
      rw [div_lt_div_iff₀ (by positivity) hD]
      have hring : (2 * (R * ((l : ℝ) + 1)) * Λ ^ (l + 1))
            * ((2 : ℝ) ^ l * (n : ℝ) ^ l * (M : ℝ) ^ l)
          = (2 : ℝ) ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1) * (M : ℝ) ^ l
              * (n : ℝ) ^ l := by
        rw [pow_succ]
        ring
      have hring2 : ε * (tubeCGP l c * ((Ctube l) ^ l * Λ ^ l)) * (n : ℝ) ^ (l + 1)
          = ε * tubeCGP l c * (Ctube l) ^ l * Λ ^ l * (n : ℝ) ^ (l + 1) := by ring
      rw [hring, hring2]
      exact hY
    calc 2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1))
        ≤ 2 * (R * ((l : ℝ) + 1)) * Λ ^ (l + 1) / (n : ℝ) ^ (l + 1) := hL
      _ < ε * (tubeCGP l c * ((Ctube l) ^ l * Λ ^ l
            / ((2 : ℝ) ^ l * (n : ℝ) ^ l * (M : ℝ) ^ l))) := hgoal
      _ = ε * (tubeCGP l c * (Ctube l * σ) ^ l) := by rw [hCtsig]
      _ ≤ ε * tubeRhoP l c σ := mul_le_mul_of_nonneg_left hρ hε.le
  · have hmin : min (Ctube l * σ) 1 = 1 := min_eq_right hcase
    have hρ : tubeCGP l c * (1 : ℝ) ^ l ≤ tubeRhoP l c σ := by
      have h := tubeRhoP_ge l c σ
      rwa [hmin] at h
    have ha' : 4 * (R * ((l : ℝ) + 1) * Λ ^ (l + 1)) ≤ ε * tubeCGP l c := by
      have h1 : (4 : ℝ) ≤ 2 * (2 : ℝ) ^ (l + 1) := by
        have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ l + 1)
        linarith
      have hRl : (0 : ℝ) ≤ R * ((l : ℝ) + 1) * Λ ^ (l + 1) := by positivity
      have key : 4 * (R * ((l : ℝ) + 1) * Λ ^ (l + 1))
          ≤ (2 * (2 : ℝ) ^ (l + 1)) * (R * ((l : ℝ) + 1) * Λ ^ (l + 1)) :=
        mul_le_mul_of_nonneg_right h1 hRl
      have key2 : 4 * (R * ((l : ℝ) + 1) * Λ ^ (l + 1))
          ≤ 2 * ((2 : ℝ) ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1)) := by
        calc 4 * (R * ((l : ℝ) + 1) * Λ ^ (l + 1))
            ≤ (2 * (2 : ℝ) ^ (l + 1)) * (R * ((l : ℝ) + 1) * Λ ^ (l + 1)) := key
          _ = 2 * ((2 : ℝ) ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1)) := by ring
      exact le_trans key2 ha
    have hx1 : (max δ |x|) ^ (l + 1) ≤ Λ ^ (l + 1) := by
      have h1 : max δ |x| ≤ Λ := by
        have h2 : Λ / (n : ℝ) ≤ Λ := by
          rw [div_le_iff₀ hn0]
          have h3 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          nlinarith [hΛ, h3]
        linarith [hx]
      exact pow_le_pow_left₀ hx0 h1 _
    have hone : (1 : ℝ) ^ l = 1 := one_pow l
    rw [hone, mul_one] at hρ
    have hεC : 0 < ε * tubeCGP l c := by positivity
    have hlt : 2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1)) < ε * tubeCGP l c := by
      have h1 : R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1)
          ≤ R * ((l : ℝ) + 1) * Λ ^ (l + 1) :=
        mul_le_mul_of_nonneg_left hx1 (mul_nonneg hR (by positivity))
      have h2 : 2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1))
          ≤ 2 * (R * ((l : ℝ) + 1) * Λ ^ (l + 1)) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
      have h3 : 2 * (R * ((l : ℝ) + 1) * Λ ^ (l + 1)) < ε * tubeCGP l c := by
        have hRl : (0 : ℝ) ≤ R * ((l : ℝ) + 1) * Λ ^ (l + 1) := by positivity
        linarith [ha', hRl, hεC]
      exact lt_of_le_of_lt h2 h3
    calc 2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1))
        < ε * tubeCGP l c := hlt
      _ ≤ ε * tubeRhoP l c σ := mul_le_mul_of_nonneg_left hρ hε.le

/-! ## 4. The level sums, and the one-step of the tower -/

theorem lvl2_stepM {l : ℕ} (hl : 1 ≤ l) (D : ℕ → ℝ → E l)
    {ct R : ℝ} (hct : 0 < ct) (hlow : PlateLower l D ct)
    (htay : CurveTaylorTop l D R) (hR : 0 ≤ R)
    {m n M : ℕ} (hm : 0 < m) (hn : 0 < n) (hM : 0 < M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {Λ₁ ε : ℝ} (hε : 0 < ε) (hΛ₁ : Λ * (1 + ε) * Ctube l ≤ Λ₁)
    {C₁ : ℝ≥0∞} (hdec : DecLinScale l M Λ₁ C₁)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδΛ : δ ≤ Λ / (2 * ((n * M : ℕ) : ℝ)))
    (ha : 2 * (2 ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1)) ≤ ε * tubeCGP l ct)
    (hb : (M : ℝ) ^ l ≤ (Ctube l) ^ l * (n : ℝ))
    {f : Fin m → E l → ℂ}
    (hf : ∀ i, IsFourierRep l (curvePlate l D δ (pieceCenter m i)) (f i)) :
    lvl2 l m n f ≤ C₁ * lvl2 l m (n * M) f := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : 1 ≤ M := hM
  -- the per-block one-step
  have hper : ∀ I : Fin n,
      lpNorm l (pE l) (blkSum l m n f I)
        ≤ C₁ * l2Norm (fun r : Fin M =>
            lpNorm l (pE l) (blkSum l m (n * M) f (finIdx I r))) := by
    intro I
    set s : Finset (Fin m) := Finset.univ.filter (fun i => blkIdx m n i = I.val) with hs
    have hsmem : ∀ i : Fin m, i ∈ s ↔ blkIdx m n i = I.val := by
      intro i
      rw [hs]
      simp
    have hcI : ((I.val : ℝ) / (n : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · rw [div_le_one hnR]
        exact_mod_cast I.isLt.le
    have hcIk : (I.val : ℝ) / (n : ℝ) + 1 / (n : ℝ) ≤ 1 := by
      rw [← add_div, div_le_one hnR]
      exact_mod_cast I.isLt
    have hκ0 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    have hκ1 : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one hnR]
      exact_mod_cast hn
    have huc : ∀ i ∈ s, |pieceCenter m i - (I.val : ℝ) / (n : ℝ)| ≤ 1 / (n : ℝ) := by
      intro i hi
      have h := abs_pieceCenter_sub_blkIdx_le hn i
      rw [(hsmem i).mp hi] at h
      exact h
    have hui : ∀ i ∈ s, pieceCenter m i ∈ Set.Icc (0 : ℝ) 1 := by
      intro i _
      rw [pieceCenter]
      constructor
      · positivity
      · rw [div_le_one (by exact_mod_cast hm)]
        have h : (i.val : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast i.isLt
        linarith
    have hblksub : ∀ i ∈ s, |pieceCenter m i - ((I.val : ℝ) / (n : ℝ)
        + (1 / (n : ℝ)) * pieceCenter M (lvlSubBlk m n M hM i))|
        ≤ (1 / (n : ℝ)) / (2 * (M : ℝ)) := by
      intro i hi
      have h := abs_pieceCenter_sub_subBlkIdx_le hn hM i
      rw [(hsmem i).mp hi] at h
      have he : (1 : ℝ) / (2 * ((n * M : ℕ) : ℝ)) = (1 / (n : ℝ)) / (2 * (M : ℝ)) := by
        push_cast
        ring
      rwa [he] at h
    have hnum : ∀ i ∈ s, 2 * (R * ((l : ℝ) + 1)
        * (max δ |pieceCenter m i - (I.val : ℝ) / (n : ℝ)|) ^ (l + 1))
        < ε * tubeRhoP l ct (Λ * ((1 / (n : ℝ)) / (2 * (M : ℝ)))) := by
      intro i hi
      have hx : max δ |pieceCenter m i - (I.val : ℝ) / (n : ℝ)| ≤ Λ / (n : ℝ) := by
        refine max_le ?_ ?_
        · have hle : Λ / (2 * ((n * M : ℕ) : ℝ)) ≤ Λ / (n : ℝ) := by
            rw [div_le_div_iff₀ (by positivity) hnR]
            push_cast
            have hM1' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
            have h2 : (1 : ℝ) ≤ 2 * (M : ℝ) := by linarith
            have h3 : (n : ℝ) ≤ 2 * ((n : ℝ) * (M : ℝ)) := by
              calc (n : ℝ) = (n : ℝ) * 1 := by ring
                _ ≤ (n : ℝ) * (2 * (M : ℝ)) := mul_le_mul_of_nonneg_left h2 hnR.le
                _ = 2 * ((n : ℝ) * (M : ℝ)) := by ring
            exact mul_le_mul_of_nonneg_left h3 (by linarith)
          exact le_trans hδΛ hle
        · have hle : 1 / (n : ℝ) ≤ Λ / (n : ℝ) := by
            rw [div_le_div_iff₀ hnR hnR]
            have h3 : (n : ℝ) ≤ Λ * (n : ℝ) := by
              calc (n : ℝ) = 1 * (n : ℝ) := by ring
                _ ≤ Λ * (n : ℝ) := mul_le_mul_of_nonneg_right hΛ hnR.le
            linarith
          exact le_trans (huc i hi) hle
      have h := tube_num_condition_Λ_pl (l := l) hl hM1 hn hε hct hR hΛ hx ha hb
      have he : Λ / (2 * ((n * M : ℕ) : ℝ)) = Λ * ((1 / (n : ℝ)) / (2 * (M : ℝ))) := by
        push_cast
        ring
      rwa [he] at h
    have hδκ : δ ≤ Λ * ((1 / (n : ℝ)) / (2 * (M : ℝ))) := by
      have he : Λ / (2 * ((n * M : ℕ) : ℝ)) = Λ * ((1 / (n : ℝ)) / (2 * (M : ℝ))) := by
        push_cast
        ring
      rw [← he]
      exact hδΛ
    have hmain := descentStepM (l := l) hl D hct hlow htay hR
      (c_I := (I.val : ℝ) / (n : ℝ)) (κ := 1 / (n : ℝ)) (M := M)
      (Λ := Λ) (Λ₁ := Λ₁) (ε := ε) (C₁ := C₁) (s := s) (δ := δ)
      (u := fun i : Fin m => pieceCenter m i)
      (blk := fun i : Fin m => lvlSubBlk m n M hM i) (f := f)
      hcI hcIk hκ0 hκ1 hM1 hΛ hε hΛ₁ hdec hδ0 hδ1 hδκ huc hui hblksub hnum
      (fun i _ => hf i)
    have hL : blkSum l m n f I = fun x => ∑ i ∈ s, f i x := by
      funext x
      simp only [blkSum]
      rw [hs]
    have hR : ∀ r : Fin M,
        (fun x => ∑ i ∈ s.filter (fun i => lvlSubBlk m n M hM i = r), f i x)
          = blkSum l m (n * M) f (finIdx I r) := by
      intro r
      funext x
      simp only [blkSum]
      congr 1
      rw [hs]
      have hfil : (Finset.univ.filter (fun i : Fin m => blkIdx m n i = I.val)).filter
            (fun i => lvlSubBlk m n M hM i = r)
          = (Finset.univ.filter (fun i : Fin m => blkIdx m n i = I.val)).filter
            (fun i => lvlSubBlkIdx m n M i = r.val) := by
        apply Finset.filter_congr
        intro i _
        simp only [Fin.ext_iff, lvlSubBlk_val]
      rw [hfil, filter_subBlk_eq (m := m) hM I r]
    have hRfun : (fun r : Fin M => lpNorm l (pE l)
          (fun x => ∑ i ∈ s.filter (fun i => lvlSubBlk m n M hM i = r), f i x))
        = fun r : Fin M => lpNorm l (pE l) (blkSum l m (n * M) f (finIdx I r)) := by
      funext r
      rw [hR r]
    rw [hL, ← hRfun]
    exact hmain
  -- square and sum
  have hsum : (∑ I : Fin n, (lpNorm l (pE l) (blkSum l m n f I)) ^ (2 : ℝ))
      ≤ C₁ ^ (2 : ℝ)
        * ∑ R : Fin (n * M), (lpNorm l (pE l) (blkSum l m (n * M) f R)) ^ (2 : ℝ) := by
    calc (∑ I : Fin n, (lpNorm l (pE l) (blkSum l m n f I)) ^ (2 : ℝ))
        ≤ ∑ I : Fin n, (C₁ ^ (2 : ℝ) * ∑ r : Fin M,
            (lpNorm l (pE l) (blkSum l m (n * M) f (finIdx I r))) ^ (2 : ℝ)) := by
          refine Finset.sum_le_sum fun I _ => ?_
          have h := ENNReal.rpow_le_rpow (hper I) (by norm_num : (0 : ℝ) ≤ 2)
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), l2Norm_rpow_two] at h
          exact h
      _ = C₁ ^ (2 : ℝ) * ∑ I : Fin n, ∑ r : Fin M,
            (lpNorm l (pE l) (blkSum l m (n * M) f (finIdx I r))) ^ (2 : ℝ) := by
          rw [Finset.mul_sum]
      _ = C₁ ^ (2 : ℝ)
            * ∑ R : Fin (n * M), (lpNorm l (pE l) (blkSum l m (n * M) f R)) ^ (2 : ℝ) := by
          congr 1
          exact sum_finIdx (g := fun R : Fin (n * M) =>
            (lpNorm l (pE l) (blkSum l m (n * M) f R)) ^ (2 : ℝ))
  rw [lvl2, lvl2, l2Norm, l2Norm]
  have hC1 : (C₁ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = C₁ := by
    rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
  have h2 := ENNReal.rpow_le_rpow hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), hC1] at h2
  exact h2

theorem curveDec_towerM {l : ℕ} (hl : 1 ≤ l) (D : ℕ → ℝ → E l)
    {ct R : ℝ} (hct : 0 < ct) (hlow : PlateLower l D ct)
    (htay : CurveTaylorTop l D R) (hR : 0 ≤ R)
    {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {εt Λ₁ : ℝ} (hεt : 0 < εt) (hΛ₁ : Λ * (1 + εt) * Ctube l ≤ Λ₁)
    (ha : 2 * (2 ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1)) ≤ εt * tubeCGP l ct)
    {a : ℝ} (ha1 : 1 ≤ a) {εm : ℝ} (hεm : 0 < εm)
    (hmod : ∀ M : ℕ, 1 ≤ M → DecLinScale l M Λ₁ (ENNReal.ofReal (a * (M : ℝ) ^ εm)))
    {m : ℕ} (hm : 4 ≤ m) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδΛ : δ ≤ Λ / (2 * (m : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ {f : Fin m → E l → ℂ},
      (∀ i, IsFourierRep l (curvePlate l D δ (pieceCenter m i)) (f i)) →
      lpNorm l (pE l) (fun x => ∑ i, f i x)
        ≤ ENNReal.ofReal C * (m : ℝ≥0∞) ^ (2 * εm) * l2Norm (fun i => lpNorm l (pE l) (f i)) := by
  classical
  have hm0 : 0 < m := by omega
  have hm1 : 1 ≤ m := by omega
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  obtain ⟨Cabs, hCabs, habs⟩ := Commons.Analysis.Asymptotics.pow_const_le_mul_rpow
    (a := max 1 a) (b := εm) (le_max_left 1 a) hεm (L := 2 * (l : ℝ) + 1) (by positivity)
  refine ⟨3 * Cabs, by positivity, ?_⟩
  intro f hf
  -- the curve constants
  have hCt2 : (2 : ℝ) ≤ Ctube l := by
    rw [Ctube]
    have h3 : (1 : ℝ) ≤ (l : ℝ) * (l.factorial : ℝ) := by
      have h4 : (1 : ℕ) ≤ l * l.factorial := by
        have h5 : 1 ≤ l := hl
        have h6 : 1 ≤ l.factorial := Nat.factorial_pos l
        nlinarith
      exact_mod_cast h4
    linarith
  -- the tower reaches the fine level
  have h0 : 2 ≤ towerN l m 1 := by
    rw [towerN_succ, towerN_zero, towerNext]
    rw [if_pos (by omega)]
    by_cases h2 : 1 * lvlStep l 1 ≤ m
    · rw [if_pos h2]
      simpa using lvlStep_two_le l 1
    · rw [if_neg h2]
      omega
  obtain ⟨K, hK, hmK⟩ := Commons.Combinatorics.LevelBlocks.pow_step_reaches_half (l := l) hl hm
    (n := fun j => towerN l m (j + 1)) h0 (fun j hj => towerN_growth hl hm (j + 1) hj)
  -- the per-step bound
  have hbound : ∀ j : ℕ, lvl2 l m (towerN l m j) f
      ≤ ENNReal.ofReal (a * ((towerN l m (j + 1) / towerN l m j : ℕ) : ℝ) ^ εm)
        * lvl2 l m (towerN l m (j + 1)) f := by
    intro j
    set M : ℕ := towerN l m (j + 1) / towerN l m j with hM
    have hn1 : 1 ≤ towerN l m j := one_le_towerN l m j
    have hMpos : 0 < M := by
      rcases Nat.eq_zero_or_pos M with h0M | h0M
      · exfalso
        have h1 := towerN_mul_div l m j
        rw [← hM, h0M, mul_zero] at h1
        have := one_le_towerN l m (j + 1)
        omega
      · exact h0M
    have hMtower : towerN l m j * M = towerN l m (j + 1) := by
      rw [hM]
      exact towerN_mul_div l m j
    have hδ1' : δ ≤ Λ / (2 * ((towerN l m j * M : ℕ) : ℝ)) := by
      rw [hMtower]
      have ht : (0 : ℝ) < (towerN l m (j + 1) : ℕ) := by
        exact_mod_cast one_le_towerN l m (j + 1)
      have hle : Λ / (2 * (m : ℝ)) ≤ Λ / (2 * ((towerN l m (j + 1) : ℕ) : ℝ)) := by
        apply div_le_div_of_nonneg_left (le_trans zero_le_one hΛ)
        · positivity
        · have h2 : (towerN l m (j + 1) : ℝ) ≤ (m : ℝ) := by
            exact_mod_cast towerN_le l m (j + 1) hm1
          linarith
      exact le_trans hδΛ hle
    have hb : (M : ℝ) ^ l ≤ (Ctube l) ^ l * ((towerN l m j : ℕ) : ℝ) := by
      have hMle : M ≤ max 1 (lvlStep l (towerN l m j)) := by
        rw [hM]
        exact towerN_div_le l m j
      rcases lt_or_ge 1 M with hM2 | hM1
      · have hMle' : M ≤ lvlStep l (towerN l m j) := by
          rcases le_max_iff.mp hMle with h | h
          · omega
          · exact h
        have hlvl : (lvlStep l (towerN l m j)) ^ l ≤ 2 ^ l * towerN l m j :=
          lvlStep_pow_le hl hn1
        have hreal : (M : ℝ) ^ l ≤ (2 : ℝ) ^ l * ((towerN l m j : ℕ) : ℝ) := by
          have h1 : (M : ℝ) ≤ ((lvlStep l (towerN l m j) : ℕ) : ℝ) := by exact_mod_cast hMle'
          have h2 : (M : ℝ) ^ l ≤ ((lvlStep l (towerN l m j) : ℕ) : ℝ) ^ l :=
            pow_le_pow_left₀ (by positivity) h1 l
          have h3 : (((lvlStep l (towerN l m j)) ^ l : ℕ) : ℝ)
              ≤ ((2 ^ l * towerN l m j : ℕ) : ℝ) := by exact_mod_cast hlvl
          calc (M : ℝ) ^ l ≤ ((lvlStep l (towerN l m j) : ℕ) : ℝ) ^ l := h2
            _ = (((lvlStep l (towerN l m j)) ^ l : ℕ) : ℝ) := by push_cast; ring
            _ ≤ ((2 ^ l * towerN l m j : ℕ) : ℝ) := h3
            _ = (2 : ℝ) ^ l * ((towerN l m j : ℕ) : ℝ) := by push_cast; ring
        exact hreal.trans (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by norm_num) hCt2 l) (by positivity))
      · have h1 : M = 1 := le_antisymm hM1 hMpos
        rw [h1, Nat.cast_one, one_pow]
        have hn1' : (1 : ℝ) ≤ (towerN l m j : ℕ) := by exact_mod_cast hn1
        have hCt1 : (1 : ℝ) ≤ (Ctube l) ^ l := one_le_pow₀ (le_trans (by norm_num) hCt2)
        nlinarith
    have hstep := lvl2_stepM (l := l) hl D hct hlow htay hR hm0 hn1 hMpos
      hΛ hεt hΛ₁ (hmod M hMpos) hδ0 hδ1 hδ1' ha hb (fun i => hf i)
    rwa [hMtower] at hstep
  -- the telescoping of the product of constants
  have hprod : ∀ J : ℕ, (∏ j ∈ Finset.range J,
        ENNReal.ofReal (a * ((towerN l m (j + 1) / towerN l m j : ℕ) : ℝ) ^ εm))
      = ENNReal.ofReal (a ^ J * ((towerN l m J : ℕ) : ℝ) ^ εm) := by
    intro J
    induction J with
    | zero =>
        rw [Finset.prod_range_zero, towerN_zero]
        simp
    | succ J ih =>
        have hnn : (0 : ℝ) ≤ a ^ J * ((towerN l m J : ℕ) : ℝ) ^ εm :=
          mul_nonneg (pow_nonneg (by linarith [ha1]) J) (Real.rpow_nonneg (by positivity) εm)
        rw [Finset.prod_range_succ, ih, ← ENNReal.ofReal_mul hnn]
        congr 1
        have hM := towerN_mul_div l m J
        have hcast : ((towerN l m (J + 1) : ℕ) : ℝ)
            = (towerN l m J : ℝ) * ((towerN l m (J + 1) / towerN l m J : ℕ) : ℝ) := by
          rw [← Nat.cast_mul, towerN_mul_div]
        have htJ : (0 : ℝ) < (towerN l m J : ℕ) := by
          exact_mod_cast one_le_towerN l m J
        have htm : (0 : ℝ) < ((towerN l m (J + 1) / towerN l m J : ℕ) : ℝ) := by
          rcases Nat.eq_zero_or_pos (towerN l m (J + 1) / towerN l m J) with h0M | h0M
          · exfalso
            have h1 : towerN l m J * (towerN l m (J + 1) / towerN l m J) = towerN l m (J + 1) :=
              towerN_mul_div l m J
            rw [h0M, mul_zero] at h1
            have h2 := one_le_towerN l m (J + 1)
            omega
          · exact_mod_cast h0M
        rw [hcast, Real.mul_rpow htJ.le htm.le, pow_succ']
        ring
  -- the chain
  have hchain := lvl2_chain (l := l) (m := m) f (n := fun j => towerN l m j)
    (C := fun j => ENNReal.ofReal (a * ((towerN l m (j + 1) / towerN l m j : ℕ) : ℝ) ^ εm))
    (towerN_zero l m) hbound (K + 1)
  rw [hprod (K + 1)] at hchain
  -- the product bound
  have hpb : ENNReal.ofReal (a ^ (K + 1) * ((towerN l m (K + 1) : ℕ) : ℝ) ^ εm)
      ≤ ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) := by
    apply ENNReal.ofReal_le_ofReal
    have hlog1 : (1 : ℝ) ≤ Real.log (Real.log (m : ℝ) + 2) + 1 := by
      have h4 : (0 : ℝ) ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
      have h5 : (1 : ℝ) ≤ Real.log (m : ℝ) + 2 := by linarith
      have h6 : (0 : ℝ) ≤ Real.log (Real.log (m : ℝ) + 2) := Real.log_nonneg h5
      linarith
    have hK' : ((K + 1 : ℕ) : ℝ)
        ≤ 2 + (2 * (l : ℝ) + 1) * (Real.log (Real.log (m : ℝ) + 2) + 1) := by
      have h1 : ((K : ℕ) : ℝ) ≤ 2 + 2 * (l : ℝ) * (Real.log (Real.log (m : ℝ) + 2) + 1) := hK
      have hL0 : (0 : ℝ) ≤ 2 * (l : ℝ) := by positivity
      push_cast
      nlinarith [h1, hL0, hlog1]
    have h1 : a ^ (K + 1) ≤ Cabs * (m : ℝ) ^ εm := by
      calc a ^ (K + 1) ≤ (max 1 a) ^ (K + 1) :=
            pow_le_pow_left₀ (by positivity) (le_max_right 1 a) _
        _ ≤ Cabs * (m : ℝ) ^ εm := habs (K + 1) m (by omega) hK'
    have h2 : ((towerN l m (K + 1) : ℕ) : ℝ) ^ εm ≤ (m : ℝ) ^ εm := by
      refine Real.rpow_le_rpow (by positivity) ?_ hεm.le
      exact_mod_cast towerN_le l m (K + 1) hm1
    have h3 : (m : ℝ) ^ εm * (m : ℝ) ^ εm = (m : ℝ) ^ (2 * εm) := by
      rw [← Real.rpow_add (by exact_mod_cast hm0)]
      ring_nf
    calc a ^ (K + 1) * ((towerN l m (K + 1) : ℕ) : ℝ) ^ εm
        ≤ (Cabs * (m : ℝ) ^ εm) * ((towerN l m (K + 1) : ℕ) : ℝ) ^ εm :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (Cabs * (m : ℝ) ^ εm) * (m : ℝ) ^ εm :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Cabs * (m : ℝ) ^ (2 * εm) := by rw [← h3]; ring
  -- the final comparison
  have hfin : lvl2 l m (towerN l m (K + 1)) f
      ≤ (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * lvl2 l m m f :=
    lvl2_le_self (l := l) hl hm0 (one_le_towerN l m (K + 1)) hmK
      (fun i => (hf i).aestronglyMeasurable)
  have hcomb : lvl2 l m 1 f
      ≤ (ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ))
        * lvl2 l m m f := by
    calc lvl2 l m 1 f
        ≤ ENNReal.ofReal (a ^ (K + 1) * ((towerN l m (K + 1) : ℕ) : ℝ) ^ εm)
            * lvl2 l m (towerN l m (K + 1)) f := hchain
      _ ≤ ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * lvl2 l m (towerN l m (K + 1)) f :=
          mul_le_mul_of_nonneg_right hpb (by simp)
      _ ≤ ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm))
            * ((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * lvl2 l m m f) :=
          mul_le_mul_of_nonneg_left hfin (by simp)
      _ = (ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ))
            * lvl2 l m m f := by ring
  rw [lvl2_one] at hcomb
  refine hcomb.trans ?_
  have hob : (ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ))
      ≤ ENNReal.ofReal (3 * Cabs) * (m : ℝ≥0∞) ^ (2 * εm) := by
    have h3 : (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ (3 : ℝ≥0∞) := by
      calc (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt 3) := by
            rw [Real.sqrt_eq_rpow, show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by simp,
              ← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num)]
        _ ≤ ENNReal.ofReal (3 : ℝ) := ENNReal.ofReal_le_ofReal (by
            nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3])
        _ = (3 : ℝ≥0∞) := by simp
    calc (ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ))
        = (ENNReal.ofReal Cabs * (m : ℝ≥0∞) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) := by
          rw [ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
          norm_num
      _ ≤ (ENNReal.ofReal Cabs * (m : ℝ≥0∞) ^ (2 * εm)) * 3 :=
          mul_le_mul_of_nonneg_left h3 (by simp)
      _ = ENNReal.ofReal (3 * Cabs) * (m : ℝ≥0∞) ^ (2 * εm) := by
          have h3e : ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) := by simp
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), h3e]
          ring
  calc (ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ))
        * lvl2 l m m f
      ≤ (ENNReal.ofReal (3 * Cabs) * (m : ℝ≥0∞) ^ (2 * εm)) * lvl2 l m m f :=
        mul_le_mul_of_nonneg_right hob (by simp)
    _ = ENNReal.ofReal (3 * Cabs) * (m : ℝ≥0∞) ^ (2 * εm)
          * l2Norm (fun i => lpNorm l (pE l) (f i)) := by rw [lvl2_self]


end Submission.Vinogradov
