import Mathlib
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.CR.Flat.Holder.iDN_add_le
import Submission.Work.CR.Flat.Holder.comp_linear_le
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.fderiv_eq_dzC_add_dbarC

set_option maxHeartbeats 1600000

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.CR.Flat.Cauchy

open Work.CR.Flat.Holder

/-! ## The Wirtinger decomposition of the real differential

The identity `du = ∂u · dz + ∂̄u · dz̄` (see `fderiv_eq_dzC_add_dbarC`) says that the real
differential of `u` is obtained from the pair `(∂u, ∂̄u)` by the *fixed* pair of linear maps
`v ↦ a * v` and `v ↦ b * star v`.  Consequently the iterated derivatives of `u` are obtained
from those of `∂u` and `∂̄u` by the same fixed linear maps and are therefore controlled by
them linearly.  This file records the two maps `PhiC`, `PsiC` and the resulting estimate. -/

/-- The continuous bilinear map `ℂ × ℂ → ℂ`, as a continuous linear map
`ℂ →L[ℝ] (ℂ →L[ℝ] ℂ)`: `PhiC a` is the map `v ↦ a * v`. -/
def PhiC : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) := ContinuousLinearMap.mul ℝ ℂ

/-- The continuous linear map `ℂ →L[ℝ] (ℂ →L[ℝ] ℂ)` sending `b` to the map `v ↦ b * conj v`,
i.e. the `(0,1)` part of the decomposition `du = ∂u · dz + ∂̄u · dz̄`. -/
def PsiC : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  (ContinuousLinearMap.apply ℝ (ℂ →L[ℝ] ℂ) (Complex.conjCLE : ℂ →L[ℝ] ℂ)).comp
    (ContinuousLinearMap.precompR ℂ (ContinuousLinearMap.mul ℝ ℂ))

@[simp] lemma PhiC_apply (a v : ℂ) : PhiC a v = a * v := rfl

@[simp] lemma PsiC_apply (b v : ℂ) : PsiC b v = b * star v := by
  simp [PsiC, ContinuousLinearMap.compL_apply]

lemma norm_PhiC : ‖PhiC‖ = 1 := ContinuousLinearMap.opNorm_mul ℝ ℂ

lemma norm_PsiC_le : ‖PsiC‖ ≤ 1 := by
  rw [ContinuousLinearMap.opNorm_le_iff (by norm_num : (0:ℝ) ≤ 1)]
  intro b
  calc ‖PsiC b‖ ≤ ‖(ContinuousLinearMap.mul ℝ ℂ) b‖ * ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖b‖ * 1 := by rw [ContinuousLinearMap.opNorm_mul_apply, Complex.conjCLE_norm]
    _ = 1 * ‖b‖ := by rw [one_mul, mul_one]

/-- The continuous linear map recovering `∂u = dzC u` from the real differential `du`:
`dzCLM L = (1/2) * (L 1 - i * L i)`. -/
def dzCLM : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1/2 : ℝ) • ((ContinuousLinearMap.apply ℝ ℂ (1:ℂ)) -
    (ContinuousLinearMap.lsmul ℝ ℂ Complex.I).comp (ContinuousLinearMap.apply ℝ ℂ Complex.I))

/-- The continuous linear map recovering `∂̄u = dbarC u` from the real differential `du`:
`dbarCLM L = (1/2) * (L 1 + i * L i)`. -/
def dbarCLM : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1/2 : ℝ) • ((ContinuousLinearMap.apply ℝ ℂ (1:ℂ)) +
    (ContinuousLinearMap.lsmul ℝ ℂ Complex.I).comp (ContinuousLinearMap.apply ℝ ℂ Complex.I))

lemma dzC_eq_dzCLM (u : ℂ → ℂ) : (fun z => dzC u z) = dzCLM ∘ (fderiv ℝ u) := by
  funext z
  simp only [Function.comp_apply, dzCLM, Work.CR.Flat.dzC, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.lsmul_apply,
    ContinuousLinearMap.apply_apply]
  norm_num

lemma dbarC_eq_dbarCLM (u : ℂ → ℂ) : (fun z => dbarC u z) = dbarCLM ∘ (fderiv ℝ u) := by
  funext z
  simp only [Function.comp_apply, dbarCLM, Work.CR.Flat.dbarC, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.lsmul_apply,
    ContinuousLinearMap.apply_apply, Complex.real_smul]
  norm_num

lemma contDiffOn_dzC {Ω : Set ℂ} (hΩ : IsOpen Ω) {k : ℕ} {u : ℂ → ℂ} (hu : ContDiff ℝ (k+1) u) :
    ContDiffOn ℝ (k:ℕ∞) (fun z => dzC u z) Ω := by
  have hm : ((k:ℕ):WithTop ℕ∞) + 1 ≤ (((k+1:ℕ):WithTop ℕ∞)) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
  have hfu : ContDiffOn ℝ (((k+1:ℕ)):WithTop ℕ∞) u Ω := hu.contDiffOn.mono (Set.subset_univ Ω)
  have hfd : ContDiffOn ℝ (k:ℕ∞) (fun z => fderiv ℝ u z) Ω := ContDiffOn.fderiv_of_isOpen hfu hΩ hm
  have hcomp := ContDiff.comp_contDiffOn dzCLM.contDiff hfd
  rw [dzC_eq_dzCLM u]
  exact hcomp

lemma contDiffOn_dbarC {Ω : Set ℂ} (hΩ : IsOpen Ω) {k : ℕ} {u : ℂ → ℂ} (hu : ContDiff ℝ (k+1) u) :
    ContDiffOn ℝ (k:ℕ∞) (fun z => dbarC u z) Ω := by
  have hm : ((k:ℕ):WithTop ℕ∞) + 1 ≤ (((k+1:ℕ):WithTop ℕ∞)) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
  have hfu : ContDiffOn ℝ (((k+1:ℕ)):WithTop ℕ∞) u Ω := hu.contDiffOn.mono (Set.subset_univ Ω)
  have hfd : ContDiffOn ℝ (k:ℕ∞) (fun z => fderiv ℝ u z) Ω := ContDiffOn.fderiv_of_isOpen hfu hΩ hm
  have hcomp := ContDiff.comp_contDiffOn dbarCLM.contDiff hfd
  rw [dbarC_eq_dbarCLM u]
  exact hcomp

/-- The Wirtinger decomposition of the real differential on an open set. -/
lemma fderivWithin_eq_PhiC_add_PsiC {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → ℂ}
    (hu : Differentiable ℝ u) {z : ℂ} (hz : z ∈ Ω) :
    fderivWithin ℝ u Ω z = PhiC (dzC u z) + PsiC (dbarC u z) := by
  rw [fderivWithin_of_isOpen hΩ hz]
  ext v
  rw [ContinuousLinearMap.add_apply, PhiC_apply, PsiC_apply]
  exact fderiv_eq_dzC_add_dbarC u z v (hu z)

/-! ## The two bounds -/

/-- Bound on the sup norms of the derivatives of `u` of order `1 ≤ i ≤ k+1`. -/
private lemma iterDerivNorm_le_wirtinger {Ω : Set ℂ} (hΩ : IsOpen Ω) (k : ℕ) (α : ℝ)
    {u : ℂ → ℂ} (hu : ContDiff ℝ (k + 1) u) {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k + 1) :
    iterDerivNorm i u Ω ≤ holderNorm k α (fun z => dzC u z) Ω
      + holderNorm k α (fun z => dbarC u z) Ω := by
  have hΩu : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  have hpred : i - 1 ≤ k := by rw [Nat.sub_le_iff_le_add]; exact hik
  have hsucc : i - 1 + 1 = i := by omega
  have hu' : Differentiable ℝ u := hu.differentiable (by simp)
  have hdz : ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => dzC u z) Ω :=
    (contDiffOn_dzC hΩ hu).of_le (WithTop.coe_le_coe.mpr (ENat.coe_le_coe.mpr hpred))
  have hdb : ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => dbarC u z) Ω :=
    (contDiffOn_dbarC hΩ hu).of_le (WithTop.coe_le_coe.mpr (ENat.coe_le_coe.mpr hpred))
  have hΦ : ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => PhiC (dzC u z)) Ω :=
    ContDiff.comp_contDiffOn PhiC.contDiff hdz
  have hΨ : ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => PsiC (dbarC u z)) Ω :=
    ContDiff.comp_contDiffOn PsiC.contDiff hdb
  calc iterDerivNorm i u Ω
      = iDN i u Ω := rfl
    _ = iDN ((i-1)+1) u Ω := by rw [hsucc]
    _ = iDN (i-1) (fun z => fderivWithin ℝ u Ω z) Ω :=
        (iDN_fderivWithin (i-1) u Ω hΩu).symm
    _ = iDN (i-1) (fun z => PhiC (dzC u z) + PsiC (dbarC u z)) Ω :=
        iDN_congr (fun z hz => fderivWithin_eq_PhiC_add_PsiC hΩ hu' hz)
    _ ≤ iDN (i-1) (fun z => PhiC (dzC u z)) Ω + iDN (i-1) (fun z => PsiC (dbarC u z)) Ω :=
        iDN_add_le (i-1) hΦ hΨ hΩu
    _ ≤ ENNReal.ofReal ‖PhiC‖ * iDN (i-1) (fun z => dzC u z) Ω
          + ENNReal.ofReal ‖PsiC‖ * iDN (i-1) (fun z => dbarC u z) Ω :=
        add_le_add (comp_linear_le PhiC (i-1) α hdz hΩu).1 (comp_linear_le PsiC (i-1) α hdb hΩu).1
    _ ≤ iDN (i-1) (fun z => dzC u z) Ω + iDN (i-1) (fun z => dbarC u z) Ω := by
        rw [norm_PhiC, ENNReal.ofReal_one, one_mul]
        refine add_le_add le_rfl ?_
        calc ENNReal.ofReal ‖PsiC‖ * iDN (i-1) (fun z => dbarC u z) Ω
            ≤ 1 * iDN (i-1) (fun z => dbarC u z) Ω :=
              mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_one.mpr norm_PsiC_le) bot_le
          _ = iDN (i-1) (fun z => dbarC u z) Ω := one_mul _
    _ ≤ holderNorm k α (fun z => dzC u z) Ω + holderNorm k α (fun z => dbarC u z) Ω :=
        add_le_add (iterDerivNorm_le_holderNorm k α _ Ω hpred) (iterDerivNorm_le_holderNorm k α _ Ω hpred)

/-- Bound on the Hölder seminorms of the derivatives of `u` of order `1 ≤ i ≤ k+1`. -/
private lemma holderSeminorm_le_wirtinger {Ω : Set ℂ} (hΩ : IsOpen Ω) (k : ℕ) (α : ℝ)
    {u : ℂ → ℂ} (hu : ContDiff ℝ (k + 1) u) {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k + 1) :
    holderSeminorm i α u Ω ≤ holderNorm k α (fun z => dzC u z) Ω
      + holderNorm k α (fun z => dbarC u z) Ω := by
  have hΩu : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  have hpred : i - 1 ≤ k := by rw [Nat.sub_le_iff_le_add]; exact hik
  have hsucc : i - 1 + 1 = i := by omega
  have hu' : Differentiable ℝ u := hu.differentiable (by simp)
  have hdz : ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => dzC u z) Ω :=
    (contDiffOn_dzC hΩ hu).of_le (WithTop.coe_le_coe.mpr (ENat.coe_le_coe.mpr hpred))
  have hdb : ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => dbarC u z) Ω :=
    (contDiffOn_dbarC hΩ hu).of_le (WithTop.coe_le_coe.mpr (ENat.coe_le_coe.mpr hpred))
  have hΦ : ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => PhiC (dzC u z)) Ω :=
    ContDiff.comp_contDiffOn PhiC.contDiff hdz
  have hΨ : ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => PsiC (dbarC u z)) Ω :=
    ContDiff.comp_contDiffOn PsiC.contDiff hdb
  calc holderSeminorm i α u Ω
      = hSN i α u Ω := rfl
    _ = hSN ((i-1)+1) α u Ω := by rw [hsucc]
    _ = hSN (i-1) α (fun z => fderivWithin ℝ u Ω z) Ω :=
        (hSN_fderivWithin (i-1) α u Ω hΩu).symm
    _ = hSN (i-1) α (fun z => PhiC (dzC u z) + PsiC (dbarC u z)) Ω :=
        hSN_congr (fun z hz => fderivWithin_eq_PhiC_add_PsiC hΩ hu' hz)
    _ ≤ hSN (i-1) α (fun z => PhiC (dzC u z)) Ω + hSN (i-1) α (fun z => PsiC (dbarC u z)) Ω :=
        hSN_add_le (i-1) α hΦ hΨ hΩu
    _ ≤ ENNReal.ofReal ‖PhiC‖ * hSN (i-1) α (fun z => dzC u z) Ω
          + ENNReal.ofReal ‖PsiC‖ * hSN (i-1) α (fun z => dbarC u z) Ω :=
        add_le_add (comp_linear_le PhiC (i-1) α hdz hΩu).2 (comp_linear_le PsiC (i-1) α hdb hΩu).2
    _ ≤ hSN (i-1) α (fun z => dzC u z) Ω + hSN (i-1) α (fun z => dbarC u z) Ω := by
        rw [norm_PhiC, ENNReal.ofReal_one, one_mul]
        refine add_le_add le_rfl ?_
        calc ENNReal.ofReal ‖PsiC‖ * hSN (i-1) α (fun z => dbarC u z) Ω
            ≤ 1 * hSN (i-1) α (fun z => dbarC u z) Ω :=
              mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_one.mpr norm_PsiC_le) bot_le
          _ = hSN (i-1) α (fun z => dbarC u z) Ω := one_mul _
    _ ≤ holderNorm k α (fun z => dzC u z) Ω + holderNorm k α (fun z => dbarC u z) Ω :=
        add_le_add (holderSeminorm_le_holderNorm k α _ Ω hpred) (holderSeminorm_le_holderNorm k α _ Ω hpred)

/-! ## The Wirtinger (Newlander–Nirenberg) estimate -/

theorem holderNorm_le_wirtinger {Ω : Set ℂ} (hΩ : IsOpen Ω) (k : ℕ) (α : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : ℂ → ℂ, ContDiff ℝ (k + 1) u →
      holderNorm (k + 1) α u Ω ≤ ENNReal.ofReal K *
        (holderNorm 0 α u Ω + holderNorm k α (fun z => dzC u z) Ω
          + holderNorm k α (fun z => dbarC u z) Ω) := by
  refine ⟨2 * (k + 2), by positivity, ?_⟩
  intro u hu
  set A := holderNorm 0 α u Ω with hA
  set B := holderNorm k α (fun z => dzC u z) Ω with hB
  set C := holderNorm k α (fun z => dbarC u z) Ω with hC
  have hBC : B + C ≤ A + B + C := by
    calc B + C ≤ (A + B) + C := add_le_add_left (le_add_left le_rfl) C
      _ = A + B + C := rfl
  have hterm : ∀ i ∈ Finset.range ((k+1)+1),
      iterDerivNorm i u Ω + holderSeminorm i α u Ω ≤ 2 * (A + B + C) := by
    intro i hi
    rw [Finset.mem_range] at hi
    obtain h0 | hpos := Nat.eq_zero_or_pos i
    · subst h0
      have h1 : iterDerivNorm 0 u Ω ≤ A := iterDerivNorm_le_holderNorm 0 α u Ω le_rfl
      have h2 : holderSeminorm 0 α u Ω ≤ A := holderSeminorm_le_holderNorm 0 α u Ω le_rfl
      calc iterDerivNorm 0 u Ω + holderSeminorm 0 α u Ω ≤ A + A := add_le_add h1 h2
        _ = 2 * A := (two_mul A).symm
        _ ≤ 2 * (A + B + C) := by gcongr; exact le_add_right (le_add_right le_rfl)
    · have hi1 : 1 ≤ i := hpos
      have hik : i ≤ k + 1 := by omega
      have h1 := iterDerivNorm_le_wirtinger hΩ k α hu hi1 hik
      have h2 := holderSeminorm_le_wirtinger hΩ k α hu hi1 hik
      calc iterDerivNorm i u Ω + holderSeminorm i α u Ω ≤ (B + C) + (B + C) := add_le_add h1 h2
        _ = 2 * (B + C) := (two_mul (B + C)).symm
        _ ≤ 2 * (A + B + C) := by gcongr
  calc holderNorm (k + 1) α u Ω
      = ∑ i ∈ Finset.range ((k+1)+1), (iterDerivNorm i u Ω + holderSeminorm i α u Ω) := rfl
    _ ≤ ∑ i ∈ Finset.range ((k+1)+1), (2 * (A + B + C)) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (2 * (k + 2)) * (A + B + C) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← mul_assoc]
        rw [show (2:ℝ≥0∞) = ((2:ℕ):ℝ≥0∞) from by norm_num, ← Nat.cast_mul]
        rw [show ENNReal.ofReal (2 * (k+2) : ℝ) = ((2*(k+2):ℕ) : ℝ≥0∞) from by
          rw [show (2*(k+2):ℝ) = ((2*(k+2):ℕ):ℝ) from by norm_num, ENNReal.ofReal_natCast]]
        congr 1
        ring_nf

end Work.CR.Flat.Cauchy
