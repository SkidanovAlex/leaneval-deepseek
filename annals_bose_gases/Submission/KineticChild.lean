import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.RCLike.Inner
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Submission.PoincareOne
import Submission.Potential
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Task: prove `Submission.BoseGases.boxInt_kinetic_term_lower`

    {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) (i : Fin N) :
      (6 / L ^ 2) * ⟪(Ψ : X N → ℝ), (Ψ : X N → ℝ)⟫_[N,L]
        ≤ ∫ x in box N L, (Ψ : X N → ℝ) x * (-(Δ[i] (Ψ : X N → ℝ) x))

Proof strategy (whole-space integrals throughout; Ψ vanishes outside the box):

  1. Decompose the partial Laplacian `Δ[i]` into the three *coordinate* second
     directional derivatives, using the coordinate orthonormal basis
     `EuclideanSpace.basisFun (Fin 3) ℝ` (Bridge-style chain rule).
  2. Integration by parts on the whole space in each direction
     `u := kcDir (N) i k` (the k-th scalar coordinate axis of particle i):
     `∫ Ψ·(−D_u²Ψ) = ∫ (D_uΨ)²`.
  3. Fibre Poincaré: peel the scalar coordinate `(i, k)` with the
     measure-preserving insertion `kcInsAll` (`piFinSuccAbove` twice,
     particle peel and coordinate peel) and apply the one-dimensional Poincaré
     inequality fibre-wise (in ENNReal/lintegral form), obtaining
     `(2/L²)·∫Ψ² ≤ ∫(D_uΨ)²` in each direction `u`.
  4. Sum over `k : Fin 3` to get `(6/L²)·∫Ψ² ≤ ∫Ψ·(−Δ[i]Ψ)`.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped NNReal ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

local notation "Δ[" i "]" => partialLaplacian i

local notation "⟪" f ", " g "⟫_["N "," L"]" => ∫ x in box N L, f x * g x

abbrev kcE3 := EuclideanSpace ℝ (Fin 3)
abbrev kcE2 := Fin 2 → ℝ

noncomputable def kcStdBasis (k : Fin 3) : kcE3 := EuclideanSpace.single k (1 : ℝ)

noncomputable def kcDir (N : ℕ) (i : Fin N) (k : Fin 3) : X N :=
  Function.update (0 : X N) i (kcStdBasis k)

lemma kc_meas_ofReal_sq {α : Type*} [MeasurableSpace α] {g : α → ℝ} (hg : Measurable g) :
    Measurable (fun x => ENNReal.ofReal ((g x) ^ 2)) := by
  have hpow : Measurable (fun x : α => (g x) ^ 2) :=
    Measurable.pow hg (measurable_const : Measurable (fun _ : α => (2 : ℕ)))
  exact (ENNReal.continuous_ofReal.measurable).comp hpow

lemma kc_basisFun_eq_single (k : Fin 3) :
    ((EuclideanSpace.basisFun (Fin 3) ℝ k : kcE3)) = kcStdBasis k := by
  simp [kcStdBasis]

/-! ## support of squares of functions vanishing outside (0,L) -/

lemma kc_vanishes_of_not_mem_Icc {L : ℝ} {f : ℝ → ℝ}
    (hvan : ∀ x : ℝ, x ≤ 0 ∨ L ≤ x → f x = 0) {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) L) :
    f x = 0 := by
  have hle : x ≤ 0 ∨ L ≤ x := by
    by_contra h
    push Not at h
    exact hx ⟨le_of_lt h.1, le_of_lt h.2⟩
  exact hvan x hle

lemma kc_deriv_zero_of_not_mem_Icc {L : ℝ} (hL0 : 0 ≤ L) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hvan : ∀ x : ℝ, x ≤ 0 ∨ L ≤ x → f x = 0) {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) L) :
    deriv f x = 0 := by
  have hle : x ≤ 0 ∨ L ≤ x := by
    by_contra h
    push Not at h
    exact hx ⟨le_of_lt h.1, le_of_lt h.2⟩
  rcases hle with hxle | hxge
  · have hxlt : x < 0 := by
      apply lt_of_not_ge
      intro h0x
      exact hx ⟨h0x, le_trans hxle hL0⟩
    have hEq : (Set.Iio (0 : ℝ)).EqOn f (fun _ : ℝ => 0) := by
      intro y hy
      exact hvan y (Or.inl (le_of_lt hy))
    have hEq' : (Set.Iio (0 : ℝ)).EqOn (deriv f) (fun _ : ℝ => 0) := by
      intro y hy
      have hd : deriv (fun _ : ℝ => (0 : ℝ)) y = 0 := deriv_const y (0 : ℝ)
      simpa [hd] using (hEq.deriv isOpen_Iio) hy
    simpa using (hEq' hxlt)
  · have hxgt : L < x := by
      apply lt_of_not_ge
      intro hxL
      exact hx ⟨le_trans hL0 hxge, hxL⟩
    have hEq : (Set.Ioi L).EqOn f (fun _ : ℝ => 0) := by
      intro y hy
      exact hvan y (Or.inr (le_of_lt hy))
    have hEq' : (Set.Ioi L).EqOn (deriv f) (fun _ : ℝ => 0) := by
      intro y hy
      have hd : deriv (fun _ : ℝ => (0 : ℝ)) y = 0 := deriv_const y (0 : ℝ)
      simpa [hd] using (hEq.deriv isOpen_Ioi) hy
    simpa using (hEq' hxgt)

lemma kc_hcs_sq {L : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hvan : ∀ x : ℝ, x ≤ 0 ∨ L ≤ x → f x = 0) :
    HasCompactSupport (fun x : ℝ => (f x) ^ 2) := by
  refine IsCompact.of_isClosed_subset (s := Set.Icc (0 : ℝ) L) ?_ (isClosed_tsupport _) ?_
  · exact isCompact_Icc
  · refine closure_minimal ?_ isClosed_Icc
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hxI
    exact hx (by simp [kc_vanishes_of_not_mem_Icc (f := f) hvan hxI])

lemma kc_hcs_deriv_sq {L : ℝ} (hL0 : 0 ≤ L) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hvan : ∀ x : ℝ, x ≤ 0 ∨ L ≤ x → f x = 0) :
    HasCompactSupport (fun x : ℝ => (deriv f x) ^ 2) := by
  refine IsCompact.of_isClosed_subset (s := Set.Icc (0 : ℝ) L) ?_ (isClosed_tsupport _) ?_
  · exact isCompact_Icc
  · refine closure_minimal ?_ isClosed_Icc
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hxI
    exact hx (by simp [kc_deriv_zero_of_not_mem_Icc (L := L) hL0 hf hvan hxI])

/-! ## ENNReal 1D Poincaré -/

lemma kc_poincare_enn {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hvan : ∀ x : ℝ, x ≤ 0 ∨ L ≤ x → f x = 0) :
    (ENNReal.ofReal (2 / L ^ 2)) * (∫⁻ x : ℝ, ENNReal.ofReal ((f x) ^ 2)) ≤
      ∫⁻ x : ℝ, ENNReal.ofReal ((deriv f x) ^ 2) := by
  let I1 : ENNReal := ∫⁻ x : ℝ, ENNReal.ofReal ((f x) ^ 2)
  let I2 : ENNReal := ∫⁻ x : ℝ, ENNReal.ofReal ((deriv f x) ^ 2)
  let R1 : ℝ := ∫ x : ℝ, (f x) ^ 2
  let R2 : ℝ := ∫ x : ℝ, (deriv f x) ^ 2
  have hf2c : Continuous (fun x : ℝ => (f x) ^ 2) := (hf.continuous).pow 2
  have hfd2c : Continuous (fun x : ℝ => (deriv f x) ^ 2) :=
    (hf.continuous_deriv (by norm_num : (1 : WithTop ℕ∞) ≤ 1)).pow 2
  have hInt1 : Integrable (fun x : ℝ => (f x) ^ 2) :=
    Continuous.integrable_of_hasCompactSupport hf2c (kc_hcs_sq hf.continuous hvan)
  have hInt2 : Integrable (fun x : ℝ => (deriv f x) ^ 2) :=
    Continuous.integrable_of_hasCompactSupport hfd2c (kc_hcs_deriv_sq hL.le hf hvan)
  have hI1fin : I1 < ⊤ := by simpa [I1] using (Integrable.lintegral_lt_top hInt1)
  have hI2fin : I2 < ⊤ := by simpa [I2] using (Integrable.lintegral_lt_top hInt2)
  have hR1 : R1 = I1.toReal := by
    dsimp [R1, I1]
    exact integral_eq_lintegral_of_nonneg_ae (μ := volume)
      (f := fun x : ℝ => (f x) ^ 2)
      (ae_of_all _ (fun x => sq_nonneg (f x))) hf2c.aestronglyMeasurable
  have hR2 : R2 = I2.toReal := by
    dsimp [R2, I2]
    exact integral_eq_lintegral_of_nonneg_ae (μ := volume)
      (f := fun x : ℝ => (deriv f x) ^ 2)
      (ae_of_all _ (fun x => sq_nonneg (deriv f x))) hfd2c.aestronglyMeasurable
  have hc0 : 0 ≤ (2 / L ^ 2) := by positivity
  have hreal : (2 / L ^ 2) * R1 ≤ R2 := by
    dsimp [R1, R2]
    exact poincare_two hL hf hvan
  have hI1 : I1 = ENNReal.ofReal R1 := by
    rw [hR1]
    exact (ENNReal.ofReal_toReal (ne_of_lt hI1fin)).symm
  have hI2 : I2 = ENNReal.ofReal R2 := by
    rw [hR2]
    exact (ENNReal.ofReal_toReal (ne_of_lt hI2fin)).symm
  have hcalc : (ENNReal.ofReal (2 / L ^ 2)) * I1 ≤ I2 := by
    calc
      (ENNReal.ofReal (2 / L ^ 2)) * I1 = ENNReal.ofReal ((2 / L ^ 2) * R1) := by
        rw [hI1]
        rw [ENNReal.ofReal_mul hc0]
      _ ≤ ENNReal.ofReal R2 := ENNReal.ofReal_le_ofReal hreal
      _ = I2 := hI2.symm
  change (ENNReal.ofReal (2 / L ^ 2)) * I1 ≤ I2
  exact hcalc

noncomputable def kcIns3 (k : Fin 3) : (ℝ × kcE2) ≃ᵐ kcE3 :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) k).symm.trans
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))

lemma kc_mp_ins3 (k : Fin 3) : MeasurePreserving (⇑(kcIns3 k)) := by
  change MeasurePreserving (⇑(MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) ∘
      ⇑((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) k).symm))
  have hPi : MeasurePreserving (⇑((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) k).symm)) := by
    exact (MeasurePreserving.symm (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) k)
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) k))
  have hToLp : MeasurePreserving (⇑(MeasurableEquiv.toLp 2 (Fin 3 → ℝ))) := by
    simpa [MeasurableEquiv.coe_toLp] using (PiLp.volume_preserving_toLp (Fin 3))
  exact (MeasurePreserving.comp hToLp hPi)

lemma kc_ins3_apply_same (k : Fin 3) (t : ℝ) (c : kcE2) :
    (kcIns3 k (t, c)).ofLp k = t := by
  dsimp [kcIns3]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]

lemma kc_ins3_apply_succ (k : Fin 3) (t : ℝ) (c : kcE2) (j : Fin 2) :
    (kcIns3 k (t, c)).ofLp (k.succAbove j) = c j := by
  dsimp [kcIns3]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]

lemma kc_ins3_affine (k : Fin 3) (t : ℝ) (c : kcE2) :
    kcIns3 k (t, c) = kcIns3 k (0, c) + t • (kcStdBasis k) := by
  ext m
  by_cases hm : m = k
  · subst m
    simp [kc_ins3_apply_same, kcStdBasis]
  · rcases Fin.exists_succAbove_eq hm with ⟨z, hz⟩
    rw [← hz]
    simp [kc_ins3_apply_succ, kcStdBasis]

noncomputable def kcInsN (n : ℕ) (i : Fin (n + 1)) : (kcE3 × X n) ≃ᵐ X (n + 1) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => kcE3) i).symm

lemma kc_mp_insN (n : ℕ) (i : Fin (n + 1)) : MeasurePreserving (⇑(kcInsN n i)) := by
  dsimp [kcInsN]
  exact (MeasurePreserving.symm (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => kcE3) i)
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => kcE3) i))

lemma kc_insN_apply_same (n : ℕ) (i : Fin (n + 1)) (y : kcE3) (r : X n) :
    kcInsN n i (y, r) i = y := by
  dsimp [kcInsN]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]

lemma kc_insN_apply_succ (n : ℕ) (i : Fin (n + 1)) (y : kcE3) (r : X n) (j : Fin n) :
    kcInsN n i (y, r) (i.succAbove j) = r j := by
  dsimp [kcInsN]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]

lemma kc_insN_other_indep (n : ℕ) (i : Fin (n + 1)) (y y' : kcE3) (r : X n) (j : Fin (n+1))
    (hj : j ≠ i) : kcInsN n i (y, r) j = kcInsN n i (y', r) j := by
  rcases Fin.exists_succAbove_eq hj with ⟨z, hz⟩
  rw [← hz]
  simp [kc_insN_apply_succ]

noncomputable def kcInsAll (n : ℕ) (i : Fin (n + 1)) (k : Fin 3) :
    (ℝ × (kcE2 × X n)) ≃ᵐ X (n + 1) :=
  ((MeasurableEquiv.prodAssoc.symm).trans
      ((kcIns3 k).prodCongr (MeasurableEquiv.refl (X n)))).trans (kcInsN n i)

lemma kc_mp_insAll (n : ℕ) (i : Fin (n + 1)) (k : Fin 3) : MeasurePreserving (⇑(kcInsAll n i k)) := by
  have h1 : MeasurePreserving (⇑((MeasurableEquiv.prodAssoc :
      ((ℝ × kcE2) × X n) ≃ᵐ ℝ × (kcE2 × X n)).symm)) := by
    exact (MeasurePreserving.symm (MeasurableEquiv.prodAssoc)
      (volume_preserving_prodAssoc))
  have h2 : MeasurePreserving (⇑((kcIns3 k).prodCongr (MeasurableEquiv.refl (X n)))) := by
    exact MeasurePreserving.prod (kc_mp_ins3 k) (MeasurePreserving.id volume)
  have h3 : MeasurePreserving (⇑(kcInsN n i)) := kc_mp_insN n i
  change MeasurePreserving (⇑(kcInsN n i) ∘ ⇑((kcIns3 k).prodCongr (MeasurableEquiv.refl (X n))) ∘
    ⇑(MeasurableEquiv.prodAssoc.symm))
  exact MeasurePreserving.comp h3 (MeasurePreserving.comp h2 h1)

lemma kc_insAll_coord (n : ℕ) (i : Fin (n + 1)) (k : Fin 3) (t : ℝ) (c : kcE2) (r : X n) :
    ((kcInsAll n i k (t, (c, r)) i)) k = t := by
  change ((kcInsAll n i k (t, (c, r)) i).ofLp) k = t
  change ((kcInsN n i ((kcIns3 k).prodCongr (MeasurableEquiv.refl (X n))
      ((MeasurableEquiv.prodAssoc.symm) (t, (c, r)))) i).ofLp) k = t
  change ((kcInsN n i ((kcIns3 k).prodCongr (MeasurableEquiv.refl (X n)) ((t, c), r)) i).ofLp) k = t
  change ((kcInsN n i (kcIns3 k (t, c), (MeasurableEquiv.refl (X n)) r) i).ofLp) k = t
  change ((kcInsN n i (kcIns3 k (t, c), r) i).ofLp) k = t
  simp [kc_insN_apply_same, kc_ins3_apply_same]

lemma kc_insAll_affine (n : ℕ) (i : Fin (n + 1)) (k : Fin 3) (t : ℝ) (c : kcE2) (r : X n) :
    kcInsAll n i k (t, (c, r)) = kcInsAll n i k (0, (c, r)) + t • (kcDir (n + 1) i k) := by
  funext j
  by_cases hj : j = i
  · subst j
    change kcInsN n i (kcIns3 k (t, c), r) i =
      (kcInsN n i (kcIns3 k (0, c), r) + t • kcDir (n + 1) i k) i
    simp [kc_insN_apply_same, kcDir]
    exact kc_ins3_affine k t c
  · change kcInsN n i (kcIns3 k (t, c), r) j =
      (kcInsN n i (kcIns3 k (0, c), r) + t • kcDir (n + 1) i k) j
    rw [kc_insN_other_indep n i (kcIns3 k (t, c)) (kcIns3 k (0, c)) r j hj]
    simp [kcDir, hj]

lemma kc_hasDerivAt_insAll (n : ℕ) (i : Fin (n + 1)) (k : Fin 3) (c : kcE2) (r : X n) (t0 : ℝ) :
    HasDerivAt (fun t : ℝ => kcInsAll n i k (t, (c, r))) (kcDir (n + 1) i k) t0 := by
  have hAeq : (fun t : ℝ => kcInsAll n i k (t, (c, r))) =
      fun t : ℝ => kcInsAll n i k (0, (c, r)) + t • (kcDir (n + 1) i k) := by
    funext t
    exact kc_insAll_affine n i k t c r
  rw [hAeq]
  have hcst : HasDerivAt (fun _ : ℝ => kcInsAll n i k (0, (c, r))) 0 t0 := hasDerivAt_const _ _
  have hid : HasDerivAt (fun t : ℝ => t • kcDir (n + 1) i k) (kcDir (n + 1) i k) t0 := by
    simpa using (hasDerivAt_id t0).smul_const (kcDir (n + 1) i k)
  have htotal := hcst.add hid
  rw [zero_add] at htotal
  exact htotal

lemma kc_slice_deriv (n : ℕ) (i : Fin (n + 1)) (k : Fin 3) (c : kcE2) (r : X n) (t0 : ℝ)
    {f : X (n + 1) → ℝ} (hf : ContDiff ℝ ∞ f) :
    deriv (fun t : ℝ => f (kcInsAll n i k (t, (c, r)))) t0 =
      fderiv ℝ f (kcInsAll n i k (t0, (c, r))) (kcDir (n + 1) i k) := by
  have hfdiff : DifferentiableAt ℝ f (kcInsAll n i k (t0, (c, r))) := by
    exact hf.differentiable (by norm_num : ∞ ≠ 0) _
  have hmain := HasFDerivAt.comp_hasDerivAt t0
    (l := f) (f := (fun t : ℝ => kcInsAll n i k (t, (c, r)))) hfdiff.hasFDerivAt
    (kc_hasDerivAt_insAll n i k c r t0)
  exact (HasDerivAt.deriv hmain)


/-! ## Fibered Poincaré (ENNReal) -/

lemma kc_poincare_fiber_enn {n : ℕ} {L : ℝ} (hL : 0 < L) (i : Fin (n + 1)) (k : Fin 3)
    {f : X (n + 1) → ℝ} (hf : ContDiff ℝ ∞ f) (hcs : HasCompactSupport f)
    (hvan : ∀ x : X (n + 1), (x i) k ≤ 0 ∨ L ≤ (x i) k → f x = 0) :
    (ENNReal.ofReal (2 / L ^ 2)) * (∫⁻ x : X (n + 1), ENNReal.ofReal ((f x) ^ 2)) ≤
      ∫⁻ x : X (n + 1), ENNReal.ofReal ((fderiv ℝ f x (kcDir (n + 1) i k)) ^ 2) := by
  classical
  -- measurability of the transported integrands
  have hfmeas : Measurable (fun x : X (n + 1) => f x) := hf.continuous.measurable
  have hfdirmeas : Measurable (fun x : X (n + 1) => fderiv ℝ f x (kcDir (n + 1) i k)) :=
    (firstDir_contDiff hf (kcDir (n + 1) i k)).continuous.measurable
  have hFp : Measurable (fun p : ℝ × (kcE2 × X n) => f (kcInsAll n i k p)) :=
    hfmeas.comp (kcInsAll n i k).measurable
  have hGp : Measurable (fun p : ℝ × (kcE2 × X n) =>
      fderiv ℝ f (kcInsAll n i k p) (kcDir (n + 1) i k)) :=
    hfdirmeas.comp (kcInsAll n i k).measurable
  -- transport whole-space lintegrals to the peeled product
  have htr2 : (∫⁻ x : X (n + 1), ENNReal.ofReal ((f x) ^ 2)) =
      ∫⁻ p : ℝ × (kcE2 × X n), ENNReal.ofReal ((f (kcInsAll n i k p)) ^ 2) := by
    exact (MeasurePreserving.lintegral_comp (kc_mp_insAll n i k)
      (kc_meas_ofReal_sq hfmeas)).symm
  have htrD : (∫⁻ x : X (n + 1),
      ENNReal.ofReal ((fderiv ℝ f x (kcDir (n + 1) i k)) ^ 2)) =
      ∫⁻ p : ℝ × (kcE2 × X n),
        ENNReal.ofReal ((fderiv ℝ f (kcInsAll n i k p) (kcDir (n + 1) i k)) ^ 2) := by
    exact (MeasurePreserving.lintegral_comp (kc_mp_insAll n i k)
      (kc_meas_ofReal_sq hfdirmeas)).symm
  -- per-fibre 1D Poincaré
  have hfib : ∀ c : kcE2, ∀ r : X n,
      (ENNReal.ofReal (2 / L ^ 2)) *
          (∫⁻ t : ℝ, ENNReal.ofReal ((f (kcInsAll n i k (t, (c, r)))) ^ 2)) ≤
        ∫⁻ t : ℝ, ENNReal.ofReal
          ((fderiv ℝ f (kcInsAll n i k (t, (c, r))) (kcDir (n + 1) i k)) ^ 2) := by
    intro c r
    have hA : ContDiff ℝ ∞ (fun t : ℝ => kcInsAll n i k (t, (c, r))) := by
      rw [show (fun t : ℝ => kcInsAll n i k (t, (c, r))) =
          fun t : ℝ => kcInsAll n i k (0, (c, r)) + t • (kcDir (n + 1) i k) by
        funext t
        exact kc_insAll_affine n i k t c r]
      fun_prop
    have hu1 : ContDiff ℝ 1 (fun t : ℝ => f (kcInsAll n i k (t, (c, r)))) := by
      change ContDiff ℝ 1 (f ∘ (fun t : ℝ => kcInsAll n i k (t, (c, r))))
      exact ContDiff.comp (hf.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞))
        (hA.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞))
    have hvanu : ∀ t : ℝ, t ≤ 0 ∨ L ≤ t → f (kcInsAll n i k (t, (c, r))) = 0 := by
      intro t ht
      apply hvan
      rw [kc_insAll_coord n i k t c r]
      exact ht
    have hineq := kc_poincare_enn (L := L) hL hu1 hvanu
    have hder : ∀ t : ℝ, deriv (fun s : ℝ => f (kcInsAll n i k (s, (c, r)))) t =
        fderiv ℝ f (kcInsAll n i k (t, (c, r))) (kcDir (n + 1) i k) := by
      intro t
      exact kc_slice_deriv n i k c r t (f := f) hf
    calc
      (ENNReal.ofReal (2 / L ^ 2)) *
          (∫⁻ t : ℝ, ENNReal.ofReal ((f (kcInsAll n i k (t, (c, r)))) ^ 2))
          ≤ ∫⁻ t : ℝ, ENNReal.ofReal ((deriv (fun s : ℝ => f (kcInsAll n i k (s, (c, r)))) t) ^ 2) :=
            hineq
      _ = ∫⁻ t : ℝ, ENNReal.ofReal
            ((fderiv ℝ f (kcInsAll n i k (t, (c, r))) (kcDir (n + 1) i k)) ^ 2) := by
          apply lintegral_congr
          intro t
          rw [hder t]
  have hfibq : ∀ q : kcE2 × X n,
      (ENNReal.ofReal (2 / L ^ 2)) *
          (∫⁻ t : ℝ, ENNReal.ofReal ((f (kcInsAll n i k (t, q))) ^ 2)) ≤
        ∫⁻ t : ℝ, ENNReal.ofReal
          ((fderiv ℝ f (kcInsAll n i k (t, q)) (kcDir (n + 1) i k)) ^ 2) := by
    intro q
    rcases q with ⟨c, r⟩
    exact hfib c r
  -- Fubini on the product (q outer)
  have hprod2 : (∫⁻ p : ℝ × (kcE2 × X n), ENNReal.ofReal ((f (kcInsAll n i k p)) ^ 2)) =
      ∫⁻ q : kcE2 × X n, ∫⁻ t : ℝ, ENNReal.ofReal ((f (kcInsAll n i k (t, q))) ^ 2) := by
    exact lintegral_prod_symm' (μ := (volume : Measure ℝ)) (ν := (volume : Measure (kcE2 × X n)))
      (fun p : ℝ × (kcE2 × X n) => ENNReal.ofReal ((f (kcInsAll n i k p)) ^ 2))
      (kc_meas_ofReal_sq hFp)
  have hprodD : (∫⁻ p : ℝ × (kcE2 × X n),
      ENNReal.ofReal ((fderiv ℝ f (kcInsAll n i k p) (kcDir (n + 1) i k)) ^ 2)) =
      ∫⁻ q : kcE2 × X n, ∫⁻ t : ℝ,
        ENNReal.ofReal ((fderiv ℝ f (kcInsAll n i k (t, q)) (kcDir (n + 1) i k)) ^ 2) := by
    exact lintegral_prod_symm' (μ := (volume : Measure ℝ)) (ν := (volume : Measure (kcE2 × X n)))
      (fun p : ℝ × (kcE2 × X n) =>
        ENNReal.ofReal ((fderiv ℝ f (kcInsAll n i k p) (kcDir (n + 1) i k)) ^ 2))
      (kc_meas_ofReal_sq hGp)
  -- assemble
  calc
    (ENNReal.ofReal (2 / L ^ 2)) * (∫⁻ x : X (n + 1), ENNReal.ofReal ((f x) ^ 2))
        ≤ ∫⁻ x : X (n + 1), ENNReal.ofReal
            ((fderiv ℝ f x (kcDir (n + 1) i k)) ^ 2) := by
      rw [htr2, htrD, hprod2, hprodD]
      calc
        (ENNReal.ofReal (2 / L ^ 2)) *
            (∫⁻ q : kcE2 × X n, ∫⁻ t : ℝ,
              ENNReal.ofReal ((f (kcInsAll n i k (t, q))) ^ 2))
            = ∫⁻ q : kcE2 × X n, (ENNReal.ofReal (2 / L ^ 2)) *
                (∫⁻ t : ℝ, ENNReal.ofReal ((f (kcInsAll n i k (t, q))) ^ 2)) := by
              exact (lintegral_const_mul' (r := ENNReal.ofReal (2 / L ^ 2))
                (fun q : kcE2 × X n => ∫⁻ t : ℝ, ENNReal.ofReal ((f (kcInsAll n i k (t, q))) ^ 2))
                (ENNReal.ofReal_ne_top)).symm
        _ ≤ ∫⁻ q : kcE2 × X n, ∫⁻ t : ℝ,
              ENNReal.ofReal ((fderiv ℝ f (kcInsAll n i k (t, q)) (kcDir (n + 1) i k)) ^ 2) := by
              exact lintegral_mono hfibq


/-! ## Fibered Poincaré (real) -/

lemma kc_poincare_fiber {n : ℕ} {L : ℝ} (hL : 0 < L) (i : Fin (n + 1)) (k : Fin 3)
    {f : X (n + 1) → ℝ} (hf : ContDiff ℝ ∞ f) (hcs : HasCompactSupport f)
    (hvan : ∀ x : X (n + 1), (x i) k ≤ 0 ∨ L ≤ (x i) k → f x = 0) :
    (2 / L ^ 2) * ∫ x : X (n + 1), (f x) ^ 2 ≤
      ∫ x : X (n + 1), (fderiv ℝ f x (kcDir (n + 1) i k)) ^ 2 := by
  let c : ℝ := 2 / L ^ 2
  let I2 : ENNReal := ∫⁻ x : X (n + 1), ENNReal.ofReal ((f x) ^ 2)
  let ID : ENNReal := ∫⁻ x : X (n + 1),
      ENNReal.ofReal ((fderiv ℝ f x (kcDir (n + 1) i k)) ^ 2)
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  -- continuity and compact support
  have hf2c : Continuous (fun x : X (n + 1) => (f x) ^ 2) := hf.continuous.pow 2
  have hfdir_c : Continuous (fun x : X (n + 1) => fderiv ℝ f x (kcDir (n + 1) i k)) :=
    (firstDir_contDiff hf (kcDir (n + 1) i k)).continuous
  have hfdir2c : Continuous (fun x : X (n + 1) =>
      (fderiv ℝ f x (kcDir (n + 1) i k)) ^ 2) := hfdir_c.pow 2
  have hsup2 : Function.support (fun x : X (n + 1) => (f x) ^ 2) ⊆ Function.support f := by
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro hz
    exact hx (by simp [hz])
  have hcs2 : HasCompactSupport (fun x : X (n + 1) => (f x) ^ 2) := by
    refine IsCompact.of_isClosed_subset hcs (isClosed_tsupport _) ?_
    exact closure_mono hsup2
  have hcsD : HasCompactSupport (fun x : X (n + 1) => fderiv ℝ f x (kcDir (n + 1) i k)) := by
    exact IsCompact.of_isClosed_subset hcs (isClosed_tsupport _)
      (tsupport_firstDir_subset (f := f) (kcDir (n + 1) i k))
  have hsupD2 : Function.support (fun x : X (n + 1) =>
      (fderiv ℝ f x (kcDir (n + 1) i k)) ^ 2) ⊆
        Function.support (fun x : X (n + 1) => fderiv ℝ f x (kcDir (n + 1) i k)) := by
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro hz
    exact hx (by simp [hz])
  have hcsD2 : HasCompactSupport (fun x : X (n + 1) =>
      (fderiv ℝ f x (kcDir (n + 1) i k)) ^ 2) := by
    refine IsCompact.of_isClosed_subset hcsD (isClosed_tsupport _) ?_
    exact closure_mono hsupD2
  have hInt2 : Integrable (fun x : X (n + 1) => (f x) ^ 2) :=
    Continuous.integrable_of_hasCompactSupport hf2c hcs2
  have hIntD : Integrable (fun x : X (n + 1) => (fderiv ℝ f x (kcDir (n + 1) i k)) ^ 2) :=
    Continuous.integrable_of_hasCompactSupport hfdir2c hcsD2
  have hI2fin : I2 < ⊤ := by simpa [I2] using (Integrable.lintegral_lt_top hInt2)
  have hIDfin : ID < ⊤ := by simpa [ID] using (Integrable.lintegral_lt_top hIntD)
  have hR2 : (∫ x : X (n + 1), (f x) ^ 2) = I2.toReal := by
    dsimp [I2]
    exact integral_eq_lintegral_of_nonneg_ae (μ := volume)
      (f := fun x : X (n + 1) => (f x) ^ 2)
      (ae_of_all _ (fun x => sq_nonneg (f x))) hf2c.aestronglyMeasurable
  have hRD : (∫ x : X (n + 1), (fderiv ℝ f x (kcDir (n + 1) i k)) ^ 2) = ID.toReal := by
    dsimp [ID]
    exact integral_eq_lintegral_of_nonneg_ae (μ := volume)
      (f := fun x : X (n + 1) => (fderiv ℝ f x (kcDir (n + 1) i k)) ^ 2)
      (ae_of_all _ (fun x => sq_nonneg (fderiv ℝ f x (kcDir (n + 1) i k))))
      hfdir2c.aestronglyMeasurable
  -- the ENNReal inequality
  have hI := kc_poincare_fiber_enn (L := L) (i := i) (k := k) (f := f) hL hf hcs hvan
  have hconv := ENNReal.toReal_mono (b := ID) (ne_of_lt hIDfin) hI
  -- hconv : (ofReal c * I2).toReal ≤ ID.toReal
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0] at hconv
  -- hconv : c * I2.toReal ≤ ID.toReal
  calc
    c * (∫ x : X (n + 1), (f x) ^ 2) = c * I2.toReal := by rw [hR2]
    _ ≤ ID.toReal := by
      -- c * I2.toReal: hconv is (c * I2.toReal) ≤ ID.toReal? careful: hconv after rw: ((ofReal c)*I2).toReal = c * I2.toReal ≤ ...
      simpa using hconv
    _ = ∫ x : X (n + 1), (fderiv ℝ f x (kcDir (n + 1) i k)) ^ 2 := hRD.symm



/-! ## interior of the box: positive coordinates -/

lemma kc_norm_dir (N : ℕ) (i : Fin N) (k : Fin 3) : ‖kcDir N i k‖ = 1 := by
  rw [Pi.norm_def]
  have hsup : (Finset.univ.sup fun b : Fin N => ‖kcDir N i k b‖₊) = 1 := by
    apply le_antisymm
    · apply Finset.sup_le_iff.mpr
      intro b hb
      by_cases h : b = i
      · subst b
        simp [kcDir, kcStdBasis]
      · simp [kcDir, h]
    · calc
        (1 : ℝ≥0) = ‖(kcStdBasis k : kcE3)‖₊ := by simp [kcStdBasis]
        _ = ‖kcDir N i k i‖₊ := by simp [kcDir]
        _ ≤ Finset.univ.sup (fun b : Fin N => ‖kcDir N i k b‖₊) :=
          Finset.le_sup (s := Finset.univ) (f := fun b : Fin N => ‖kcDir N i k b‖₊) (Finset.mem_univ i)
  simpa [hsup]

/-- coordinates of an interior point of the box lie in `(0, L)`. -/
lemma kc_interior_box_coord {N : ℕ} {L : ℝ} (hL : 0 < L) {x : X N}
    (hx : x ∈ interior (box N L)) (i : Fin N) (k : Fin 3) :
    0 < (x i) k ∧ (x i) k < L := by
  constructor
  · by_contra hneg
    have hle : (x i) k ≤ 0 := le_of_not_gt hneg
    rcases (Metric.isOpen_iff.mp isOpen_interior) x hx with ⟨ε, hε, hball⟩
    let δ : ℝ := ε / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδε : δ < ε := by dsimp [δ]; linarith
    have hnorm : ‖kcDir N i k‖ = 1 := kc_norm_dir N i k
    have hy : x - δ • kcDir N i k ∈ Metric.ball x ε := by
      rw [mem_ball, dist_eq_norm]
      have hsim : (x - δ • kcDir N i k) - x = -(δ • kcDir N i k) := by abel
      rw [hsim, norm_neg, norm_smul]
      have hδn : ‖δ‖ = δ := by simp [Real.norm_eq_abs, abs_of_pos hδ]
      simpa [hδn, hnorm, hδε]
    have hx2 : x - δ • kcDir N i k ∈ box N L := interior_subset (hball hy)
    have hbad : x - δ • kcDir N i k ∉ box N L := by
      intro hz
      have hz0 : 0 ≤ ((x - δ • kcDir N i k) i) k := (hz i k).1
      have hcoord : ((x - δ • kcDir N i k) i) k = (x i) k - δ := by simp [kcDir, kcStdBasis]
      rw [hcoord] at hz0
      linarith
    exact hbad hx2
  · by_contra hneg
    have hle : L ≤ (x i) k := le_of_not_gt hneg
    rcases (Metric.isOpen_iff.mp isOpen_interior) x hx with ⟨ε, hε, hball⟩
    let δ : ℝ := ε / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδε : δ < ε := by dsimp [δ]; linarith
    have hnorm : ‖kcDir N i k‖ = 1 := kc_norm_dir N i k
    have hy : x + δ • kcDir N i k ∈ Metric.ball x ε := by
      rw [mem_ball, dist_eq_norm]
      have hsim : (x + δ • kcDir N i k) - x = δ • kcDir N i k := by abel
      rw [hsim, norm_smul]
      have hδn : ‖δ‖ = δ := by simp [Real.norm_eq_abs, abs_of_pos hδ]
      simpa [hδn, hnorm, hδε]
    have hx2 : x + δ • kcDir N i k ∈ box N L := interior_subset (hball hy)
    have hbad : x + δ • kcDir N i k ∉ box N L := by
      intro hz
      have hcoord : ((x + δ • kcDir N i k) i) k = (x i) k + δ := by simp [kcDir, kcStdBasis]
      have hzL : ((x + δ • kcDir N i k) i) k ≤ L := (hz i k).2
      rw [hcoord] at hzL
      linarith
    exact hbad hx2

/-- vanishing of Ψ when one coordinate is outside `(0, L)`. -/
lemma kc_vanishes_outside_Ioo {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L)
    (i : Fin N) (k : Fin 3) :
    ∀ x : X N, (x i) k ≤ 0 ∨ L ≤ (x i) k → (Ψ : X N → ℝ) x = 0 := by
  intro x hx
  exact psi_eq_zero_of_not_mem_interior Ψ (by
    intro hxint
    rcases hx with hx | hx
    · have hpos := (kc_interior_box_coord hL hxint i k).1
      linarith
    · have hlt := (kc_interior_box_coord hL hxint i k).2
      linarith)

/-! ## coordinate decomposition of the partial Laplacian -/

lemma kc_sliceSecondDirTerm {N : ℕ} (i : Fin N) (x : X N) {f : X N → ℝ}
    (hf : ContDiff ℝ 2 f) (b : kcE3) :
    fderiv ℝ (fun y : kcE3 =>
        fderiv ℝ (fun z : kcE3 => f (Function.update x i z)) y b) (x i) b =
      fderiv ℝ (fun z : X N => fderiv ℝ f z (Function.update (0 : X N) i b)) x
        (Function.update (0 : X N) i b) := by
  let T : kcE3 → X N := fun y => Function.update x i y
  let v : X N := Function.update (0 : X N) i b
  let h : X N → ℝ := fun w => fderiv ℝ f w v
  have hT2 : ContDiff ℝ 2 T := by
    dsimp [T]
    change ContDiff ℝ 2 (Function.update x i)
    exact contDiff_update 2 x i
  have hfd_h : DifferentiableAt ℝ h (T (x i)) := by
    have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := bridgeContDiffFderivOne N hf
    have heval : ContDiff ℝ 1 (fun (L : X N →L[ℝ] ℝ) => L v) := by
      exact (ContinuousLinearMap.apply (𝕜 := ℝ) (Fₗ := ℝ) v : (X N →L[ℝ] ℝ) →L[ℝ] ℝ).contDiff
    have hcont : ContDiff ℝ 1 (fun w : X N => fderiv ℝ f w v) := by
      change ContDiff ℝ 1 ((fun (L : X N →L[ℝ] ℝ) => L v) ∘ (fun w : X N => fderiv ℝ f w))
      exact heval.comp hf1
    dsimp [h]
    exact (hcont.differentiable (by norm_num)) (T (x i))
  have hTdiff : DifferentiableAt ℝ T (x i) :=
    (hT2.differentiable (by norm_num)).differentiableAt
  have hchain := fderiv_comp (x := x i) (f := T) (g := h) hfd_h hTdiff
  have hfun :
      (fun y : kcE3 => fderiv ℝ (fun z : kcE3 => f (Function.update x i z)) y b) = h ∘ T := by
    funext y
    rw [bridgeSliceFderivApply N i x hf y b]
    have hu : Function.update (0 : X N) i b = v := by dsimp [v]
    rw [hu]
    rfl
  calc
    fderiv ℝ (fun y : kcE3 =>
        fderiv ℝ (fun z : kcE3 => f (Function.update x i z)) y b) (x i) b
        = fderiv ℝ (h ∘ T) (x i) b := by rw [hfun]
    _ = fderiv ℝ h (T (x i)) (fderiv ℝ T (x i) b) := by
          rw [hchain]
          rfl
    _ = (fderiv ℝ (fun z : X N => fderiv ℝ f z (Function.update (0 : X N) i b)) x)
          (Function.update (0 : X N) i b) := by
          have hTx : T (x i) = x := by
            dsimp [T]
            simp
          rw [hTx]
          have hdT : fderiv ℝ T (x i) b = v := by
            dsimp [T, v]
            rw [bridgeFderivUpdate N i x (x i) b]
          rw [hdT]

/-- Δ[i] as a sum of three coordinate second derivatives. -/
lemma kc_partialLaplacian_eq {N : ℕ} (i : Fin N) {f : X N → ℝ} (hf : ContDiff ℝ 2 f) :
    partialLaplacian i f = fun x : X N => ∑ k : Fin 3,
      (fderiv ℝ (fun z : X N => fderiv ℝ f z (kcDir N i k)) x) (kcDir N i k) := by
  ext x
  let g : kcE3 → ℝ := fun y => f (Function.update x i y)
  have hg : ContDiff ℝ 2 g := by
    dsimp [g]
    exact bridgeSliceContDiff N i x hf
  have hmain := InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f := g)
    (EuclideanSpace.basisFun (Fin 3) ℝ)
  calc
    partialLaplacian i f x = Δ g (x i) := by
      dsimp [partialLaplacian, g]
    _ = ∑ k : Fin 3, iteratedFDeriv ℝ 2 g (x i) ![EuclideanSpace.basisFun (Fin 3) ℝ k,
        EuclideanSpace.basisFun (Fin 3) ℝ k] := by
      simpa using congrFun hmain (x i)
    _ = ∑ k : Fin 3,
        (fderiv ℝ (fun z : X N => fderiv ℝ f z (kcDir N i k)) x) (kcDir N i k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [bridgeSecondDirIteratedFDeriv (f := g) (x := x i)
        (b := (EuclideanSpace.basisFun (Fin 3) ℝ k : kcE3)) hg]
      have hb : (EuclideanSpace.basisFun (Fin 3) ℝ k : kcE3) = kcStdBasis k := kc_basisFun_eq_single k
      have hterm := kc_sliceSecondDirTerm i x hf (EuclideanSpace.basisFun (Fin 3) ℝ k)
      rw [hterm]
      have hu : Function.update (0 : X N) i (EuclideanSpace.basisFun (Fin 3) ℝ k) = kcDir N i k := by
        rw [hb]
        rfl
      rw [hu]

/-! ## whole-space integration by parts -/

/-- `∫ f·(−D_u²f) = ∫ (D_u f)²` for smooth compactly supported f. -/
lemma kc_ws_dir2_eq {N : ℕ} {f : X N → ℝ} {u : X N} (hf : ContDiff ℝ ∞ f)
    (hcs : HasCompactSupport f) :
    (∫ x : X N, f x * (-(fderiv ℝ (fun z : X N => fderiv ℝ f z u) x u))) =
      ∫ x : X N, (fderiv ℝ f x u) ^ 2 := by
  let g : X N → ℝ := fun z => fderiv ℝ f z u
  have hg_cd : ContDiff ℝ ∞ g := by
    dsimp [g]
    exact firstDir_contDiff hf u
  have hg_c : Continuous g := hg_cd.continuous
  have hf_c : Continuous f := hf.continuous
  have hD2_cd : ContDiff ℝ ∞ (fun x : X N => fderiv ℝ g x u) := by
    dsimp [g]
    exact secondDir_contDiff_u hf u
  have hD2_c : Continuous (fun x : X N => fderiv ℝ g x u) := hD2_cd.continuous
  have hg_hcs : HasCompactSupport g := by
    exact IsCompact.of_isClosed_subset hcs (isClosed_tsupport g) (by
      simpa [g] using (tsupport_firstDir_subset (f := f) u))
  have hD2_hcs : HasCompactSupport (fun x : X N => fderiv ℝ g x u) := by
    exact IsCompact.of_isClosed_subset hcs (isClosed_tsupport (fun x : X N => fderiv ℝ g x u)) (by
      simpa [g] using (tsupport_secondDir_subset (f := f) u))
  have hfg_c : Continuous (fun x : X N => f x * g x) := hf_c.mul hg_c
  have hfg_h : HasCompactSupport (fun x : X N => f x * g x) := hcs.mul_right
  have hfg : Integrable (fun x : X N => f x * g x) volume :=
    integrable_cont_hcs hfg_c hfg_h
  have hfD2_c : Continuous (fun x : X N => f x * fderiv ℝ g x u) := hf_c.mul hD2_c
  have hfD2_h : HasCompactSupport (fun x : X N => f x * fderiv ℝ g x u) := hcs.mul_right
  have hfD2 : Integrable (fun x : X N => f x * fderiv ℝ g x u) volume :=
    integrable_cont_hcs hfD2_c hfD2_h
  have hgg_c : Continuous (fun x : X N => fderiv ℝ f x u * g x) := hg_c.mul hg_c
  have hgg_h : HasCompactSupport (fun x : X N => fderiv ℝ f x u * g x) := hg_hcs.mul_right
  have hgg : Integrable (fun x : X N => fderiv ℝ f x u * g x) volume :=
    integrable_cont_hcs hgg_c hgg_h
  have hf_diff : ∀ x ∈ tsupport g, DifferentiableAt ℝ f x := fun x hx =>
    hf.differentiable (by norm_num : ∞ ≠ 0) x
  have hg_diff : ∀ x ∈ tsupport f, DifferentiableAt ℝ g x := fun x hx =>
    hg_cd.differentiable (by norm_num : ∞ ≠ 0) x
  have hmain := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (f := f) (g := g) (v := u)
    (μ := volume) hgg hfD2 hfg hf_diff hg_diff
  calc
    (∫ x : X N, f x * (-(fderiv ℝ (fun z : X N => fderiv ℝ f z u) x u)))
        = ∫ x : X N, -(f x * fderiv ℝ g x u) := by
          apply integral_congr_ae
          filter_upwards with x
          dsimp [g]
          ring
    _ = -(∫ x : X N, f x * fderiv ℝ g x u) := by rw [integral_neg]
    _ = ∫ x : X N, (g x) ^ 2 := by
          rw [hmain]
          calc
            -(-(∫ x : X N, fderiv ℝ f x u * g x)) = ∫ x : X N, fderiv ℝ f x u * g x := by simp
            _ = ∫ x : X N, (g x) ^ 2 := by
                  apply integral_congr_ae
                  filter_upwards with x
                  dsimp [g]
                  rw [pow_two]
    _ = ∫ x : X N, (fderiv ℝ f x u) ^ 2 := by
          apply integral_congr_ae
          filter_upwards with x
          dsimp [g]

/-! ## kinetic whole-space identity -/

lemma kc_kinetic_whole {n : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box (n + 1) L) (i : Fin (n + 1)) :
    (∫ x : X (n + 1), (Ψ : X (n + 1) → ℝ) x * (-(partialLaplacian i (Ψ : X (n + 1) → ℝ) x))) =
      ∑ k : Fin 3, ∫ x : X (n + 1),
        (fderiv ℝ (Ψ : X (n + 1) → ℝ) x (kcDir (n + 1) i k)) ^ 2 := by
  have hbr := kc_partialLaplacian_eq i (f := (Ψ : X (n + 1) → ℝ)) (psi_contDiff_two Ψ)
  have hpoint : (fun x : X (n + 1) =>
      (Ψ : X (n + 1) → ℝ) x * (-(partialLaplacian i (Ψ : X (n + 1) → ℝ) x)))
      = fun x : X (n + 1) => ∑ k : Fin 3,
          (Ψ : X (n + 1) → ℝ) x * (-(fderiv ℝ
            (fun z : X (n + 1) => fderiv ℝ (Ψ : X (n + 1) → ℝ) z (kcDir (n + 1) i k)) x)
              (kcDir (n + 1) i k)) := by
    funext x
    have hbrx : partialLaplacian i (Ψ : X (n + 1) → ℝ) x =
        ∑ k : Fin 3, (fderiv ℝ (fun z : X (n + 1) => fderiv ℝ (Ψ : X (n + 1) → ℝ) z
          (kcDir (n + 1) i k)) x) (kcDir (n + 1) i k) := by
      simpa using congrFun hbr x
    rw [hbrx]
    rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  rw [hpoint]
  rw [integral_finsetSum (s := Finset.univ) (μ := volume)
    (f := fun (k : Fin 3) (x : X (n + 1)) => (Ψ : X (n + 1) → ℝ) x * (-(fderiv ℝ
      (fun z : X (n + 1) => fderiv ℝ (Ψ : X (n + 1) → ℝ) z (kcDir (n + 1) i k)) x)
        (kcDir (n + 1) i k)))]
  · apply Finset.sum_congr rfl
    intro k hk
    have hb2 := kc_ws_dir2_eq (f := (Ψ : X (n + 1) → ℝ)) (u := kcDir (n + 1) i k)
      (psi_contDiff Ψ) (hasCompactSupport_Ψ hL Ψ)
    exact hb2
  · intro k hk
    have hS_cd : ContDiff ℝ ∞ (fun x : X (n + 1) => (fderiv ℝ
        (fun z : X (n + 1) => fderiv ℝ (Ψ : X (n + 1) → ℝ) z (kcDir (n + 1) i k)) x)
          (kcDir (n + 1) i k)) :=
      secondDir_contDiff_u (psi_contDiff Ψ) (kcDir (n + 1) i k)
    have hcont : Continuous (fun x : X (n + 1) => (Ψ : X (n + 1) → ℝ) x * (-(fderiv ℝ
        (fun z : X (n + 1) => fderiv ℝ (Ψ : X (n + 1) → ℝ) z (kcDir (n + 1) i k)) x)
          (kcDir (n + 1) i k))) :=
      (psi_contDiff Ψ).continuous.mul hS_cd.continuous.neg
    have hcs : HasCompactSupport (fun x : X (n + 1) => (Ψ : X (n + 1) → ℝ) x * (-(fderiv ℝ
        (fun z : X (n + 1) => fderiv ℝ (Ψ : X (n + 1) → ℝ) z (kcDir (n + 1) i k)) x)
          (kcDir (n + 1) i k))) :=
      (hasCompactSupport_Ψ hL Ψ).mul_right
    exact Continuous.integrable_of_hasCompactSupport hcont hcs

/-! ## final assembly -/

/-- Per-particle kinetic term of an admissible state is at least the 1-particle
Dirichlet kinetic bound: `∫_{box} Ψ·(−Δ[i]Ψ) ≥ (6/L²)·‖Ψ‖²` (box integrals). -/
lemma boxInt_kinetic_term_lower {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L)
    (i : Fin N) :
    (6 / L ^ 2) * ⟪(Ψ : X N → ℝ), (Ψ : X N → ℝ)⟫_[N,L] ≤
      ∫ x in box N L, (Ψ : X N → ℝ) x * (-(Δ[i] (Ψ : X N → ℝ) x)) := by
  cases N with
  | zero =>
      exact False.elim (Nat.not_lt_zero i.1 i.isLt)
  | succ n =>
      -- whole-space equals box-restricted integrals (Ψ vanishes outside the box)
      have hbox2 : (∫ x in box (n + 1) L, ((Ψ : X (n + 1) → ℝ) x) ^ 2) =
          ∫ x : X (n + 1), ((Ψ : X (n + 1) → ℝ) x) ^ 2 := by
        exact setIntegral_eq_integral_of_forall_compl_eq_zero (by
          intro x hx
          have hz : (Ψ : X (n + 1) → ℝ) x = 0 := psi_eq_zero_of_not_mem_interior Ψ (by
            intro hxint
            exact hx (interior_subset hxint))
          simp [hz])
      have hboxD : (∫ x in box (n + 1) L,
          (Ψ : X (n + 1) → ℝ) x * (-(partialLaplacian i (Ψ : X (n + 1) → ℝ) x))) =
          ∫ x : X (n + 1),
            (Ψ : X (n + 1) → ℝ) x * (-(partialLaplacian i (Ψ : X (n + 1) → ℝ) x)) := by
        exact setIntegral_eq_integral_of_forall_compl_eq_zero (by
          intro x hx
          have hz : (Ψ : X (n + 1) → ℝ) x = 0 := psi_eq_zero_of_not_mem_interior Ψ (by
            intro hxint
            exact hx (interior_subset hxint))
          simp [hz])
      let A : ℝ := ∫ x : X (n + 1), ((Ψ : X (n + 1) → ℝ) x) ^ 2
      have hvan : ∀ k : Fin 3,
          ∀ x : X (n + 1), (x i) k ≤ 0 ∨ L ≤ (x i) k → (Ψ : X (n + 1) → ℝ) x = 0 := by
        intro k
        exact kc_vanishes_outside_Ioo hL Ψ i k
      have hk_ineq : ∀ k : Fin 3, (2 / L ^ 2) * A ≤
          ∫ x : X (n + 1), (fderiv ℝ (Ψ : X (n + 1) → ℝ) x (kcDir (n + 1) i k)) ^ 2 := by
        intro k
        dsimp [A]
        exact kc_poincare_fiber hL i k (f := (Ψ : X (n + 1) → ℝ)) (psi_contDiff Ψ)
          (hasCompactSupport_Ψ hL Ψ) (hvan k)
      have hkin := kc_kinetic_whole hL Ψ i
      have hAlhs : ⟪(Ψ : X (n + 1) → ℝ), (Ψ : X (n + 1) → ℝ)⟫_[n+1, L] = A := by
        dsimp [A]
        calc
          (∫ x in box (n + 1) L, (Ψ : X (n + 1) → ℝ) x * (Ψ : X (n + 1) → ℝ) x)
              = ∫ x in box (n + 1) L, ((Ψ : X (n + 1) → ℝ) x) ^ 2 := by
                apply integral_congr_ae
                filter_upwards with x
                rw [pow_two]
          _ = ∫ x : X (n + 1), ((Ψ : X (n + 1) → ℝ) x) ^ 2 := hbox2
      have hthree : ∑ k : Fin 3, (2 / L ^ 2) * A = (6 / L ^ 2) * A := by
        have hL2 : L ^ 2 ≠ (0 : ℝ) := pow_ne_zero 2 (ne_of_gt hL)
        calc
          (∑ k : Fin 3, (2 / L ^ 2) * A) = (∑ _k : Fin 3, (2 / L ^ 2)) * A := by
            rw [Finset.sum_mul]
          _ = (6 / L ^ 2) * A := by
            congr 1
            have hc : (∑ _k : Fin 3, (2 / L ^ 2)) = 3 * (2 / L ^ 2) := by
              rw [Finset.sum_const]
              norm_num
            rw [hc]
            field_simp [hL2]
            ring
      calc
        (6 / L ^ 2) * ⟪(Ψ : X (n + 1) → ℝ), (Ψ : X (n + 1) → ℝ)⟫_[n+1, L]
            = (6 / L ^ 2) * A := by
              rw [hAlhs]
        _ = ∑ k : Fin 3, (2 / L ^ 2) * A := hthree.symm
        _ ≤ ∑ k : Fin 3,
              ∫ x : X (n + 1), (fderiv ℝ (Ψ : X (n + 1) → ℝ) x (kcDir (n + 1) i k)) ^ 2 := by
              exact Finset.sum_le_sum (fun k hk => hk_ineq k)
        _ = ∫ x : X (n + 1),
              (Ψ : X (n + 1) → ℝ) x * (-(partialLaplacian i (Ψ : X (n + 1) → ℝ) x)) := hkin.symm
        _ = ∫ x in box (n + 1) L,
              (Ψ : X (n + 1) → ℝ) x * (-(partialLaplacian i (Ψ : X (n + 1) → ℝ) x)) := hboxD.symm

end BoseGases

end Submission
