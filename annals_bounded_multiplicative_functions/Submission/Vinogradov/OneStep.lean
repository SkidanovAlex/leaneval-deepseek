/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.Descent
import Submission.Vinogradov.DescentStep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The one-step of the scale descent (GLYZ §3.3)

`descentStep` is the localised form of the induction step of GLYZ Lemma 3.6: in the coordinates of a
coarse block of length `κ` (rescaled to `[0,1]`), the sum of the fine pieces (plate scale `δ`,
centres `u i`, attached to the sub-blocks by `blk`) is bounded by the `ℓ²` norm of the *sub-block
sums*, with the constant of the model decoupling theorem at scale `M` and enlargement `Λ₁`.

The proof:

1. **The tube lemma** (`Descent.curvePlate_subset_taylorPlate`) puts each fine plate inside the
   plate of the *Taylor polynomial* at the physical sub-block centre `c_I + κ·pieceCenter M (blk i)`
   with scale `Λ₁ * κ/(2M)`; the arithmetic constraint `2R(l+1)(max δ |u i - c_I|)^{l+1} <
   tubeRho l A cT (κ/(2M))` is exactly the hypothesis of the tube lemma (with `ε = 1`), and the
   enlargement `Λ₁ ≥ 2·Ctube l` absorbs the constant of the moment-curve tube.
2. **The sum closure** puts each sub-block sum in the class over that plate
   (`IsFourierRep.sum` + `mono`).
3. **The straightening identity** `Straighten.curveAff_image_plate` identifies that plate with
   `curveAff l D κ c_I '' plate l (Λ₁/(2M)) (pieceCenter M r)` — i.e. with the image of a *model*
   plate under the straightening map.
4. **The class transfer** (`DescentStep.exists_isFourierRep_preimage`, using the injectivity of
   `curveAffLin l D κ c_I` from the torsion) produces the functions `G r` in the class over the
   model plates with `F r = e(⟪·,D 0 c_I⟫)·(G r ∘ Λᵀ)`; the model theorem `DecLinScale l M Λ₁ C₁`
   applied to `(G r)` then transfers back through
   `DescentStep.lpNorm_phase_comp_linearMap`, the `|det Λ|^{-1/p}` factors cancelling.
5. **The fibres**: `∑ r, ∑_{i ∈ blk⁻¹ r} f i = ∑ i, f i` (`Finset.sum_fiberwise_of_maps_to`).

Supporting declaration: `curveAffLin_injective` (the straightening linear map of a curve with
torsion is injective, from `Straighten.curveAffLin_norm_lower_bound`), and `blkSet`.
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

/-- The straightening linear map of a curve with torsion is injective. -/
theorem curveAffLin_injective {l : ℕ} (hl : 1 ≤ l) (D : ℕ → ℝ → E l) {A cT ρ t₀ : ℝ}
    (hbd : CurveBounded l D A) (hA : 1 ≤ A) (htor : CurveTorsion l D cT) (hcT : 0 < cT)
    (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    Function.Injective (curveAffLin l D ρ t₀) := by
  intro x y hxy
  have h := curveAffLin_norm_lower_bound (D := D) (A := A) (c := cT) (ρ := ρ) (t₀ := t₀)
    hl hcT hA (fun i hi j => hbd i hi t₀ ht₀ j) (htor t₀ ht₀) hρ0 hρ1 (x - y)
  rw [map_sub, hxy, sub_self, norm_zero] at h
  have hcpos : 0 < cT / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
      * Real.sqrt l) * ρ ^ l * ((l.factorial : ℝ))⁻¹ := by
    have hK := tubeK_pos hl hA
    have hρl : 0 < ρ ^ l := pow_pos hρ0 l
    have hf : (0 : ℝ) < ((l.factorial : ℝ))⁻¹ := inv_pos.mpr (by positivity)
    exact mul_pos (mul_pos (div_pos hcT hK) hρl) hf
  have h2 : ‖x - y‖ = 0 := by
    by_contra hne
    have h3 : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have h4 : 0 < (cT / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
        * Real.sqrt l) * ρ ^ l * ((l.factorial : ℝ))⁻¹) * ‖x - y‖ := mul_pos hcpos h3
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp h2)

/-- The set of fine pieces attached to a sub-block. -/
def blkSet {ι : Type*} [Fintype ι] {M : ℕ} (blk : ι → Fin M) (r : Fin M) : Finset ι :=
  Finset.univ.filter (fun i => blk i = r)

/-- **The one-step of the scale descent.**  In the coordinates of a coarse block of length `κ`
(rescaled to `[0,1]`), the sum of the fine pieces (plate scale `δ`, centres `u i`, assigned to the
sub-blocks by `blk`) is bounded by the `ℓ²` norm of the sub-block sums, with the constant of the
model decoupling theorem at scale `M` and enlargement `Λ₁`. -/
theorem descentStep {l : ℕ} (hl : 1 ≤ l) (D : ℕ → ℝ → E l)
    {A cT R : ℝ} (hbd : CurveBounded l D A) (hA : 1 ≤ A) (htor : CurveTorsion l D cT)
    (hcT : 0 < cT) (htay : CurveTaylor l D R) (hR : 0 ≤ R)
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
      < ε * tubeRho l A cT (Λ * (κ / (2 * M))))
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
    have h1 := curvePlate_subset_taylorPlate (D := D) hl hbd hA htor hcT htay hR
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
    curveAffLin_injective hl D hbd hA htor hcT hcI hκ0 hκ1
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

end Submission.Vinogradov
