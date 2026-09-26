import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.tangencyBadSet
import Submission.Work.Drive.trigBasis_five_independent
import Submission.Work.Drive.scalar_five_surjective_of_independent
import Submission.Work.Drive.space_five_surjective_of_scalar
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv

/-!
# The five-point collinearity map of the perturbation family

This module collects the vocabulary for the statement
`Work.Drive.noFiveCollinear_bad_interior_empty`: the perturbed curve is `pertV r c`
(`Submission/Work/Drive/tangencyBadSet.lean`), and the "five collinear points" condition on five
separated parameters `w : Fin 5 → ℝ` is the vanishing of

  `fivePsi r (c, w) = (cross3 (p₁ - p₀) (p₂ - p₀), cross3 (p₁ - p₀) (p₃ - p₀),
                        cross3 (p₁ - p₀) (p₄ - p₀))`   with `pᵢ = pertV r c (w i)`.

The three factors are the three independent slots `p₂, p₃, p₄` of the "collinear with `p₀, p₁`"
condition.  `valMap r` is the value map `(c, w) ↦ (pertV r c (w i))ᵢ` and `valLin w` its
coefficient derivative; `valLin` is surjective on the separated region, by
`Work.Drive.trigBasis_five_independent` (the Vandermonde/trig-independence of the five value
functionals) together with the scalar-to-`Space` lifting lemmas proved below.
-/

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-! ## The value map and its coefficient derivative -/

/-- Five real parameters. -/
abbrev Param5 := Fin 5 → ℝ

/-- The value map of the perturbation family at five parameters. -/
def valMap (r : ℝ → Space) : Coeff × Param5 → (Fin 5 → Space) :=
  fun z => fun i => pertV r z.1 (z.2 i)

@[simp] lemma valMap_apply (r : ℝ → Space) (z : Coeff × Param5) (i : Fin 5) :
    valMap r z i = pertV r z.1 (z.2 i) := rfl

/-- The coefficient derivative of the value map at five parameters: the five evaluation
functionals of the trigonometric basis. -/
def valLin (w : Param5) : Coeff →L[ℝ] (Fin 5 → Space) :=
  ContinuousLinearMap.pi fun i => linSum (fun j => trigBasis j (w i))

lemma valLin_apply (w : Param5) (c : Coeff) (i : Fin 5) :
    valLin w c i = ∑ j : Fin 9, (trigBasis j (w i)) • (eCoeff c) j := by
  rw [valLin, ContinuousLinearMap.pi_apply, linSum_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [coeffProj_apply]

/-- The coefficient derivative of the value map at five parameters. -/
theorem hasFDerivAt_valMap_slice (r : ℝ → Space) (w : Param5) (c₀ : Coeff) :
    HasFDerivAt (fun c : Coeff => valMap r (c, w)) (valLin w) c₀ := by
  refine hasFDerivAt_pi'' (Φ := fun c : Coeff => valMap r (c, w)) fun i => ?_
  exact hasFDerivAt_pertV_slice r (w i) c₀

/-- The derivative of the value map along a line in its coefficient variable. -/
theorem hasDerivAt_valMap_axis (r : ℝ → Space) (w : Param5) (c₀ dc : Coeff) :
    HasDerivAt (fun s : ℝ => valMap r (c₀ + s • dc, w)) (valLin w dc) 0 := by
  have hdiff : DifferentiableAt ℝ (fun c : Coeff => valMap r (c, w)) c₀ :=
    (hasFDerivAt_valMap_slice r w c₀).differentiableAt
  have h := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := fun c : Coeff => valMap r (c, w)) (p := c₀) (e := dc) hdiff
  rw [(hasFDerivAt_valMap_slice r w c₀).fderiv] at h
  exact h

lemma valLin_apply_eq_linSum (w : Param5) (c : Coeff) (i : Fin 5) :
    valLin w c i = linSum (fun j => trigBasis j (w i)) c := by
  rw [linSum_apply, valLin_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [coeffProj_apply]

/-- The derivative of one component of the perturbed curve along a coefficient line. -/
theorem hasDerivAt_pertV_axis (r : ℝ → Space) (a : ℝ) (c₀ dc : Coeff) :
    HasDerivAt (fun s : ℝ => pertV r (c₀ + s • dc) a)
      ((linSum (fun j => trigBasis j a)) dc) 0 := by
  have hdiff : DifferentiableAt ℝ (fun c : Coeff => pertV r c a) c₀ :=
    (hasFDerivAt_pertV_slice r a c₀).differentiableAt
  have h := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := fun c : Coeff => pertV r c a) (p := c₀) (e := dc) hdiff
  rwa [(hasFDerivAt_pertV_slice r a c₀).fderiv] at h

/-- The derivative of the `i`-th component of the value map along a coefficient line. -/
theorem hasDerivAt_valMap_axis_apply (r : ℝ → Space) (w : Param5) (c₀ dc : Coeff) (i : Fin 5) :
    HasDerivAt (fun s : ℝ => valMap r (c₀ + s • dc, w) i) (valLin w dc i) 0 := by
  rw [valLin_apply_eq_linSum]
  exact hasDerivAt_pertV_axis r (w i) c₀ dc

/-- Joint continuity/smoothness of the value map. -/
theorem contDiff_valMap {r : ℝ → Space} (hr : IsSmoothKnot r) : ContDiff ℝ 1 (valMap r) := by
  have hV : ContDiff ℝ 1 (fun z : Coeff × ℝ => pertV r z.1 z.2) :=
    (contDiff_pertV_joint hr.smooth).of_le le_top
  refine contDiff_pi' (Φ := valMap r) fun i => ?_
  have hg : ContDiff ℝ 1 (fun z : Coeff × Param5 => (z.1, z.2 i)) := by fun_prop
  exact hV.comp hg

/-- Surjectivity of `valLin` from the scalar statement. -/
theorem valLin_surjective_of_scalar {w : Param5}
    (h : ∀ A : Fin 5 → Space, ∃ c : Fin 9 → Space,
      ∀ i : Fin 5, ∑ j : Fin 9, (trigBasis j (w i)) • c j = A i) :
    Function.Surjective (valLin w) := by
  intro A
  obtain ⟨c, hc⟩ := h A
  refine ⟨eCoeff.symm c, ?_⟩
  funext i
  rw [valLin_apply]
  simpa using hc i

/-! ## The five-point collinearity map -/

/-- **The five-point collinearity map.**  It vanishes exactly when the four chords from the first
point are pairwise parallel, i.e. (for distinct points) when the five points are collinear. -/
def collMap5 (P : Fin 5 → Space) : Space × Space × Space :=
  (cross3 (P (1 : Fin 5) - P (0 : Fin 5)) (P (2 : Fin 5) - P (0 : Fin 5)),
   cross3 (P (1 : Fin 5) - P (0 : Fin 5)) (P (3 : Fin 5) - P (0 : Fin 5)),
   cross3 (P (1 : Fin 5) - P (0 : Fin 5)) (P (4 : Fin 5) - P (0 : Fin 5)))

/-- The five-point collinearity map of the perturbation family. -/
def fivePsi (r : ℝ → Space) : Coeff × Param5 → Space × Space × Space :=
  fun z => collMap5 (valMap r z)

@[simp] lemma fivePsi_apply (r : ℝ → Space) (z : Coeff × Param5) :
    fivePsi r z = collMap5 (valMap r z) := rfl

lemma contDiff_collMap5 : ContDiff ℝ 1 collMap5 := by
  have hcross : ContDiff ℝ 1 (fun p : Space × Space => cross3 p.1 p.2) := by
    simpa [cross3] using (Commons.Analysis.CrossProduct.cross3_contDiff).of_le le_top
  have h12 : ContDiff ℝ 1 (fun P : Fin 5 → Space =>
      (P (1 : Fin 5) - P (0 : Fin 5), P (2 : Fin 5) - P (0 : Fin 5))) := by fun_prop
  have h13 : ContDiff ℝ 1 (fun P : Fin 5 → Space =>
      (P (1 : Fin 5) - P (0 : Fin 5), P (3 : Fin 5) - P (0 : Fin 5))) := by fun_prop
  have h14 : ContDiff ℝ 1 (fun P : Fin 5 → Space =>
      (P (1 : Fin 5) - P (0 : Fin 5), P (4 : Fin 5) - P (0 : Fin 5))) := by fun_prop
  unfold collMap5
  exact (hcross.comp h12).prodMk ((hcross.comp h13).prodMk (hcross.comp h14))

theorem contDiff_fivePsi {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ContDiff ℝ 1 (fivePsi r) :=
  contDiff_collMap5.comp (contDiff_valMap hr)

/-- Five points on a line give a vanishing collinearity map. -/
lemma collMap5_eq_zero_of_line {P : Fin 5 → Space} {p v : Space} {t : Fin 5 → ℝ}
    (h : ∀ i : Fin 5, P i = p + t i • v) : collMap5 P = 0 := by
  have h1 : P (1 : Fin 5) - P (0 : Fin 5) = (t 1 - t 0) • v := by rw [h 1, h 0]; module
  have h2 : P (2 : Fin 5) - P (0 : Fin 5) = (t 2 - t 0) • v := by rw [h 2, h 0]; module
  have h3 : P (3 : Fin 5) - P (0 : Fin 5) = (t 3 - t 0) • v := by rw [h 3, h 0]; module
  have h4 : P (4 : Fin 5) - P (0 : Fin 5) = (t 4 - t 0) • v := by rw [h 4, h 0]; module
  simp only [collMap5, h1, h2, h3, h4, cross3_smul_left, cross3_smul_right, cross3_self,
    smul_zero]
  rfl

/-! ## The separated region of five parameters, and its compactness -/

/-- The parameters lie in `[0, 2π]`. -/
def box5 : Set Param5 := Set.univ.pi fun _ => Set.Icc (0 : ℝ) (2 * Real.pi)

/-- The pairwise circular separation condition at scale `k`. -/
def sep5 (k : ℕ) : Set Param5 :=
  {v : Param5 | ∀ i j : Fin 5, i ≠ j → (1 : ℝ) / (k + 1) ≤ csep (v i) (v j)}

/-- The compact region of five separated parameters in `[0, 2π]`. -/
def K5 (k : ℕ) : Set Param5 := box5 ∩ sep5 k

/-- The same region, transported to the configuration space `Cfg` of `tangencyBadSet.lean`. -/
def Kc5 (k : ℕ) : Set Cfg := cfgHomeo ⁻¹' K5 k

theorem isCompact_box5 : IsCompact box5 := isCompact_univ_pi fun _ => isCompact_Icc

theorem isClosed_sep5 (k : ℕ) : IsClosed (sep5 k) := by
  have heq : sep5 k = ⋂ (i : Fin 5) (j : Fin 5) (_ : i ≠ j),
      {v : Param5 | (1 : ℝ) / (k + 1) ≤ csep (v i) (v j)} := by
    ext v
    simp [sep5]
  rw [heq]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  have hcont : Continuous (fun v : Param5 => csep (v i) (v j)) := by
    unfold csep
    exact (((continuous_apply i).sub (continuous_apply j)).abs).min
      (continuous_const.sub (((continuous_apply i).sub (continuous_apply j)).abs))
  exact isClosed_Ici.preimage hcont

theorem isCompact_K5 (k : ℕ) : IsCompact (K5 k) :=
  isCompact_box5.inter_right (isClosed_sep5 k)

theorem isCompact_Kc5 (k : ℕ) : IsCompact (Kc5 k) := by
  have himg : cfgHomeo.symm '' K5 k = Kc5 k := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa [Kc5, cfgHomeo.symm_apply_apply] using hv
    · intro hw
      exact ⟨cfgHomeo w, hw, cfgHomeo.symm_apply_apply w⟩
  rw [← himg]
  exact (isCompact_K5 k).image cfgHomeo.symm.continuous

lemma mem_box5 {v : Param5} : v ∈ box5 ↔ ∀ i : Fin 5, v i ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
  constructor
  · intro h i
    exact h i (Set.mem_univ i)
  · intro h i _
    exact h i

lemma mem_sep5 {k : ℕ} {v : Param5} :
    v ∈ sep5 k ↔ ∀ i j : Fin 5, i ≠ j → (1 : ℝ) / (k + 1) ≤ csep (v i) (v j) := Iff.rfl

lemma mem_K5 {k : ℕ} {v : Param5} : v ∈ K5 k ↔
    (∀ i : Fin 5, v i ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) ∧
      ∀ i j : Fin 5, i ≠ j → (1 : ℝ) / (k + 1) ≤ csep (v i) (v j) := by
  rw [K5, Set.mem_inter_iff, mem_box5]
  rfl

lemma mem_Kc5 {k : ℕ} {w : Cfg} : w ∈ Kc5 k ↔ cfgHomeo w ∈ K5 k := Iff.rfl

/-! ## From the separated region to the surjectivity of `valLin` -/

/-- **Surjectivity of the coefficient derivative of the value map over the separated region.** -/
theorem valLin_surjective {w : Param5}
    (hw : ∀ i : Fin 5, w i ∈ Set.Icc (0 : ℝ) (2 * Real.pi))
    (hsep : ∀ i j : Fin 5, i ≠ j → 0 < csep (w i) (w j)) :
    Function.Surjective (valLin w) := by
  refine valLin_surjective_of_scalar fun A => ?_
  refine space_five_surjective_of_scalar (ℓ := fun i j => trigBasis j (w i)) ?_ A
  refine scalar_five_surjective_of_independent (ℓ := fun i j => trigBasis j (w i)) ?_
  intro c hc
  exact trigBasis_five_independent w hw hsep c fun j => hc j

/-- The separated region of the statement gives the hypotheses of `valLin_surjective`. -/
theorem valLin_surjective_of_mem_K5 {k : ℕ} {w : Param5} (hw : w ∈ K5 k) :
    Function.Surjective (valLin w) := by
  obtain ⟨h1, h2⟩ := mem_K5.mp hw
  exact valLin_surjective h1 fun i j hij => lt_of_lt_of_le (by positivity) (h2 i j hij)

/-! ## The configuration-space version -/

/-- The continuous linear identification of `Cfg` with `ℝ⁵`. -/
def cfgEquiv : Cfg ≃L[ℝ] Param5 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 5 => ℝ)

@[simp] lemma cfgEquiv_apply (w : Cfg) : cfgEquiv w = cfgHomeo w := rfl

lemma cfgEquiv_apply_apply (w : Cfg) (i : Fin 5) : cfgEquiv w i = cfgLin i w := rfl

/-- The five-point collinearity map of the perturbation family, parametrised by `Cfg`. -/
def fivePsiC (r : ℝ → Space) : Coeff × Cfg → Space × Space × Space :=
  fun z => fivePsi r (z.1, cfgEquiv z.2)

theorem contDiff_fivePsiC {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ContDiff ℝ 1 (fivePsiC r) := by
  refine (contDiff_fivePsi hr).comp ?_
  exact contDiff_fst.prodMk
    ((cfgEquiv : Cfg →L[ℝ] Param5).contDiff.comp contDiff_snd)

end

end Work.Drive
