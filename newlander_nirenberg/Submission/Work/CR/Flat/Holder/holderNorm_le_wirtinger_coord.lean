import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.CR.Flat.Holder.comp_linear_le
import Submission.Work.CR.Flat.Holder.iDN_add_le
import Submission.Work.CR.Flat.Polydisc

/-!
# The `n`-dimensional Wirtinger (Newlander–Nirenberg) estimate

For `u : ℂⁿ → ℂ` (with `ℂⁿ = Fin n → ℂ`), the real differential decomposes into the
Wirtinger derivatives,

  `du_z(v) = Σ_j ( ∂_j u (z) · v_j + ∂̄_j u (z) · conj v_j )`,

where `∂_j u = dCoord j u` and `∂̄_j u = dbarCoord j u` are the `(1,0)` and `(0,1)`
coordinate derivatives.  Consequently `du` — and therefore every derivative of `u` —
is obtained from the `2n` functions `∂_j u`, `∂̄_j u` by the fixed pair of continuous
linear maps `PhiN j a : v ↦ a * v_j` and `PsiN j b : v ↦ b * conj v_j` (summed over `j`),
which are all of norm `≤ 1`.

This yields the estimate `‖u‖_{C^{k+1,α}} ≤ K (‖u‖_{C^{0,α}} + Σ_j (‖∂_j u‖_{C^{k,α}} +
‖∂̄_j u‖_{C^{k,α}}))`, the `n`-dimensional analogue of
`Work.CR.Flat.Cauchy.holderNorm_le_wirtinger`.
-/

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.CR.Flat.Holder

/-! ### The reconstruction maps -/

/-- The reconstruction map of the `(1,0)` part in the `j`-th coordinate:
`PhiN j a` is the continuous linear map `v ↦ a * v j`. -/
def PhiN {n : ℕ} (j : Fin n) : ℂ →L[ℝ] ((Fin n → ℂ) →L[ℝ] ℂ) :=
  (ContinuousLinearMap.apply ℝ ((Fin n → ℂ) →L[ℝ] ℂ) (ContinuousLinearMap.proj j)).comp
    (ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ))

/-- The reconstruction map of the `(0,1)` part in the `j`-th coordinate:
`PsiN j b` is the continuous linear map `v ↦ b * conj (v j)`. -/
def PsiN {n : ℕ} (j : Fin n) : ℂ →L[ℝ] ((Fin n → ℂ) →L[ℝ] ℂ) :=
  (ContinuousLinearMap.apply ℝ ((Fin n → ℂ) →L[ℝ] ℂ)
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj j))).comp
    (ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ))

@[simp] lemma PhiN_apply {n : ℕ} (j : Fin n) (a : ℂ) (v : Fin n → ℂ) :
    PhiN j a v = a * v j := by simp [PhiN]

@[simp] lemma PsiN_apply {n : ℕ} (j : Fin n) (a : ℂ) (v : Fin n → ℂ) :
    PsiN j a v = a * star (v j) := by simp [PsiN]

lemma norm_PhiN_le {n : ℕ} (j : Fin n) : ‖PhiN j‖ ≤ 1 := by
  rw [ContinuousLinearMap.opNorm_le_iff (zero_le_one)]
  intro a
  rw [one_mul]
  rw [ContinuousLinearMap.opNorm_le_iff (norm_nonneg a)]
  intro v
  rw [show PhiN j a v = a * v j from by simp [PhiN], norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg a)

lemma norm_PsiN_le {n : ℕ} (j : Fin n) : ‖PsiN j‖ ≤ 1 := by
  rw [ContinuousLinearMap.opNorm_le_iff (zero_le_one)]
  intro a
  rw [one_mul]
  rw [ContinuousLinearMap.opNorm_le_iff (norm_nonneg a)]
  intro v
  rw [show PsiN j a v = a * star (v j) from by simp [PsiN], norm_mul, norm_star]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg a)

/-! ### The Wirtinger decomposition of the real differential -/

/-- The elementary algebraic identity behind the Wirtinger decomposition: for an
`ℝ`-linear map `ℂ → ℂ` with `p = L 1`, `q = L i`, one has
`L w = ((1/2)(p - i q)) w + ((1/2)(p + i q)) conj w`. -/
lemma wirtinger_arith (p q w : ℂ) :
    (w.re : ℂ) * p + (w.im : ℂ) * q
      = ((1/2 : ℂ) * (p - Complex.I * q)) * w
        + ((1/2 : ℂ) * (p + Complex.I * q)) * star w := by
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im] <;>
    ring

/-- The Wirtinger decomposition of the real differential in a single coordinate
direction: `du_z(e_j w) = ∂_j u (z) · w + ∂̄_j u (z) · conj w`. -/
lemma fderiv_single_eq {n : ℕ} (u : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) (j : Fin n) (w : ℂ) :
    fderiv ℝ u z (Pi.single j w) =
      Work.CR.Flat.dCoord j u z * w + Work.CR.Flat.dbarCoord j u z * star w := by
  have hsplit : (Pi.single j w : Fin n → ℂ)
      = (w.re : ℝ) • (Pi.single j (1:ℂ) : Fin n → ℂ)
        + (w.im : ℝ) • (Pi.single j (Complex.I) : Fin n → ℂ) := by
    ext k
    by_cases hk : k = j
    · subst hk
      simp only [Pi.single_eq_same, Pi.add_apply]
      rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same]
      simp [Complex.re_add_im]
    · simp [Pi.single_eq_of_ne hk]
  rw [hsplit, map_add, map_smul, map_smul]
  simp only [Complex.real_smul]
  rw [Work.CR.Flat.dCoord, Work.CR.Flat.dbarCoord]
  exact wirtinger_arith _ _ w

/-- The Wirtinger decomposition of the real differential, evaluated at an arbitrary
tangent vector `v`. -/
lemma fderiv_eq_sum {n : ℕ} (u : (Fin n → ℂ) → ℂ) (z v : Fin n → ℂ) :
    fderiv ℝ u z v = ∑ j : Fin n,
      (Work.CR.Flat.dCoord j u z * v j + Work.CR.Flat.dbarCoord j u z * star (v j)) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact fderiv_single_eq u z j (v j)

/-- The Wirtinger decomposition as an identity of continuous linear maps. -/
lemma fderiv_eq_sum_PhiN_PsiN {n : ℕ} (u : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    fderiv ℝ u z =
      ∑ j : Fin n,
        (PhiN j (Work.CR.Flat.dCoord j u z) + PsiN j (Work.CR.Flat.dbarCoord j u z)) := by
  ext v
  rw [fderiv_eq_sum, sum_apply]
  simp

/-! ### Subadditivity of `iDN` and `hSN` over finite sums -/

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

lemma iDN_sum_le {ι : Type*} (s : Finset ι) (i : ℕ) {g : ι → X → A} {Ω : Set X}
    (hg : ∀ j ∈ s, ContDiffOn ℝ (i:ℕ∞) (g j) Ω) (hΩ : UniqueDiffOn ℝ Ω) :
    iDN i (fun x => ∑ j ∈ s, g j x) Ω ≤ ∑ j ∈ s, iDN i (g j) Ω := by
  refine iSup₂_le fun x hx => ?_
  have hfun : (fun x => ∑ j ∈ s, g j x) = (∑ j ∈ s, g j) := by
    funext x; exact (Finset.sum_apply x s g).symm
  rw [hfun]
  rw [iteratedFDerivWithin_sum_apply hΩ hx (fun j hj => (hg j hj).contDiffWithinAt hx)]
  calc ENNReal.ofReal ‖∑ j ∈ s, iteratedFDerivWithin ℝ i (g j) Ω x‖
      ≤ ENNReal.ofReal (∑ j ∈ s, ‖iteratedFDerivWithin ℝ i (g j) Ω x‖) :=
        ENNReal.ofReal_le_ofReal (norm_sum_le _ _)
    _ = ∑ j ∈ s, ENNReal.ofReal ‖iteratedFDerivWithin ℝ i (g j) Ω x‖ :=
        ENNReal.ofReal_sum_of_nonneg (fun j _ => norm_nonneg _)
    _ ≤ ∑ j ∈ s, iDN i (g j) Ω := Finset.sum_le_sum (fun j hj => le_iDN i hx)

lemma hSN_sum_le {ι : Type*} (s : Finset ι) (i : ℕ) (α : ℝ) {g : ι → X → A} {Ω : Set X}
    (hg : ∀ j ∈ s, ContDiffOn ℝ (i:ℕ∞) (g j) Ω) (hΩ : UniqueDiffOn ℝ Ω) :
    hSN i α (fun x => ∑ j ∈ s, g j x) Ω ≤ ∑ j ∈ s, hSN i α (g j) Ω := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  have hfun : (fun x => ∑ j ∈ s, g j x) = (∑ j ∈ s, g j) := by
    funext x; exact (Finset.sum_apply x s g).symm
  rw [hfun]
  rw [iteratedFDerivWithin_sum_apply hΩ hx (fun j hj => (hg j hj).contDiffWithinAt hx),
      iteratedFDerivWithin_sum_apply hΩ hy (fun j hj => (hg j hj).contDiffWithinAt hy)]
  have hd : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  have hsplit : (∑ j ∈ s, iteratedFDerivWithin ℝ i (g j) Ω x)
      - (∑ j ∈ s, iteratedFDerivWithin ℝ i (g j) Ω y)
      = ∑ j ∈ s, (iteratedFDerivWithin ℝ i (g j) Ω x
          - iteratedFDerivWithin ℝ i (g j) Ω y) :=
    (Finset.sum_sub_distrib
      (f := fun j => iteratedFDerivWithin ℝ i (g j) Ω x)
      (g := fun j => iteratedFDerivWithin ℝ i (g j) Ω y)).symm
  rw [hsplit]
  calc ENNReal.ofReal (‖∑ j ∈ s, (iteratedFDerivWithin ℝ i (g j) Ω x
            - iteratedFDerivWithin ℝ i (g j) Ω y)‖ / ‖x - y‖ ^ α)
      ≤ ENNReal.ofReal ((∑ j ∈ s, ‖iteratedFDerivWithin ℝ i (g j) Ω x
            - iteratedFDerivWithin ℝ i (g j) Ω y‖) / ‖x - y‖ ^ α) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (norm_sum_le _ _) hd)
    _ = ENNReal.ofReal (∑ j ∈ s, ‖iteratedFDerivWithin ℝ i (g j) Ω x
            - iteratedFDerivWithin ℝ i (g j) Ω y‖ / ‖x - y‖ ^ α) := by
        rw [Finset.sum_div]
    _ = ∑ j ∈ s, ENNReal.ofReal (‖iteratedFDerivWithin ℝ i (g j) Ω x
            - iteratedFDerivWithin ℝ i (g j) Ω y‖ / ‖x - y‖ ^ α) :=
        ENNReal.ofReal_sum_of_nonneg (fun j _ => div_nonneg (norm_nonneg _) hd)
    _ ≤ ∑ j ∈ s, hSN i α (g j) Ω := Finset.sum_le_sum (fun j hj => le_hSN i α hx hy hxy)

/-! ### Smoothness of the coordinate Wirtinger derivatives -/

section ContDiff

variable {n : ℕ}

lemma contDiffOn_dCoord {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω) {K : ℕ}
    {u : (Fin n → ℂ) → ℂ} (hu : ContDiff ℝ (K+1) u) (j : Fin n) :
    ContDiffOn ℝ (K:ℕ∞) (fun z => Work.CR.Flat.dCoord j u z) Ω := by
  have hm : ((K:ℕ):WithTop ℕ∞) + 1 ≤ (((K+1:ℕ):WithTop ℕ∞)) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
  have hfu : ContDiffOn ℝ (((K+1:ℕ)):WithTop ℕ∞) u Ω := hu.contDiffOn.mono (Set.subset_univ Ω)
  have hfd : ContDiffOn ℝ (K:ℕ∞) (fun z => fderiv ℝ u z) Ω :=
    ContDiffOn.fderiv_of_isOpen hfu hΩ hm
  have h1 : ContDiffOn ℝ (K:ℕ∞) (fun z => fderiv ℝ u z (Pi.single j (1:ℂ))) Ω :=
    (ContinuousLinearMap.apply ℝ ℂ (Pi.single j (1:ℂ) : Fin n → ℂ)).contDiff.comp_contDiffOn hfd
  have h2 : ContDiffOn ℝ (K:ℕ∞) (fun z => fderiv ℝ u z (Pi.single j (Complex.I))) Ω :=
    (ContinuousLinearMap.apply ℝ ℂ (Pi.single j (Complex.I) : Fin n → ℂ)).contDiff.comp_contDiffOn hfd
  have h3 : ContDiffOn ℝ (K:ℕ∞)
      (fun z => Complex.I * fderiv ℝ u z (Pi.single j (Complex.I))) Ω :=
    contDiffOn_const.mul h2
  have h4 : ContDiffOn ℝ (K:ℕ∞) (fun z => fderiv ℝ u z (Pi.single j (1:ℂ))
      - Complex.I * fderiv ℝ u z (Pi.single j (Complex.I))) Ω := h1.sub h3
  have h5 : ContDiffOn ℝ (K:ℕ∞) (fun z => (1/2:ℂ) * (fderiv ℝ u z (Pi.single j (1:ℂ))
      - Complex.I * fderiv ℝ u z (Pi.single j (Complex.I)))) Ω := contDiffOn_const.mul h4
  simpa [Work.CR.Flat.dCoord] using h5

lemma contDiffOn_dbarCoord {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω) {K : ℕ}
    {u : (Fin n → ℂ) → ℂ} (hu : ContDiff ℝ (K+1) u) (j : Fin n) :
    ContDiffOn ℝ (K:ℕ∞) (fun z => Work.CR.Flat.dbarCoord j u z) Ω := by
  have hm : ((K:ℕ):WithTop ℕ∞) + 1 ≤ (((K+1:ℕ):WithTop ℕ∞)) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
  have hfu : ContDiffOn ℝ (((K+1:ℕ)):WithTop ℕ∞) u Ω := hu.contDiffOn.mono (Set.subset_univ Ω)
  have hfd : ContDiffOn ℝ (K:ℕ∞) (fun z => fderiv ℝ u z) Ω :=
    ContDiffOn.fderiv_of_isOpen hfu hΩ hm
  have h1 : ContDiffOn ℝ (K:ℕ∞) (fun z => fderiv ℝ u z (Pi.single j (1:ℂ))) Ω :=
    (ContinuousLinearMap.apply ℝ ℂ (Pi.single j (1:ℂ) : Fin n → ℂ)).contDiff.comp_contDiffOn hfd
  have h2 : ContDiffOn ℝ (K:ℕ∞) (fun z => fderiv ℝ u z (Pi.single j (Complex.I))) Ω :=
    (ContinuousLinearMap.apply ℝ ℂ (Pi.single j (Complex.I) : Fin n → ℂ)).contDiff.comp_contDiffOn hfd
  have h3 : ContDiffOn ℝ (K:ℕ∞)
      (fun z => Complex.I * fderiv ℝ u z (Pi.single j (Complex.I))) Ω :=
    contDiffOn_const.mul h2
  have h4 : ContDiffOn ℝ (K:ℕ∞) (fun z => fderiv ℝ u z (Pi.single j (1:ℂ))
      + Complex.I * fderiv ℝ u z (Pi.single j (Complex.I))) Ω := h1.add h3
  have h5 : ContDiffOn ℝ (K:ℕ∞) (fun z => (1/2:ℂ) * (fderiv ℝ u z (Pi.single j (1:ℂ))
      + Complex.I * fderiv ℝ u z (Pi.single j (Complex.I)))) Ω := contDiffOn_const.mul h4
  simpa [Work.CR.Flat.dbarCoord] using h5

end ContDiff

/-! ### The two estimates -/

section Estimate

variable {n : ℕ}

/-- Bound on the sup norms of the derivatives of `u` of order `1 ≤ i ≤ k+1`. -/
private lemma iterDerivNorm_le_wirtinger {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    (k : ℕ) (α : ℝ) {u : (Fin n → ℂ) → ℂ} (hu : ContDiff ℝ (k + 1) u)
    {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k + 1) :
    iterDerivNorm i u Ω ≤ ∑ j : Fin n, (holderNorm k α (fun z => dCoord j u z) Ω
        + holderNorm k α (fun z => dbarCoord j u z) Ω) := by
  have hΩu : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  have hpred : i - 1 ≤ k := by omega
  have hsucc : i - 1 + 1 = i := by omega
  have hdz : ∀ j : Fin n, ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => dCoord j u z) Ω := fun j =>
    (contDiffOn_dCoord hΩ hu j).of_le (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hpred))
  have hdb : ∀ j : Fin n, ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => dbarCoord j u z) Ω := fun j =>
    (contDiffOn_dbarCoord hΩ hu j).of_le (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hpred))
  have hg : ∀ j : Fin n, ContDiffOn ℝ (((i-1):ℕ):ℕ∞)
      (fun z => PhiN j (dCoord j u z) + PsiN j (dbarCoord j u z)) Ω := fun j =>
    ((PhiN j).contDiff.comp_contDiffOn (hdz j)).add
      ((PsiN j).contDiff.comp_contDiffOn (hdb j))
  have hperj : ∀ j : Fin n,
      iDN (i - 1) (fun z => PhiN j (dCoord j u z) + PsiN j (dbarCoord j u z)) Ω
        ≤ holderNorm k α (fun z => dCoord j u z) Ω
          + holderNorm k α (fun z => dbarCoord j u z) Ω := by
    intro j
    have hφ : ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => PhiN j (dCoord j u z)) Ω :=
      (PhiN j).contDiff.comp_contDiffOn (hdz j)
    have hψ : ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => PsiN j (dbarCoord j u z)) Ω :=
      (PsiN j).contDiff.comp_contDiffOn (hdb j)
    calc iDN (i - 1) (fun z => PhiN j (dCoord j u z) + PsiN j (dbarCoord j u z)) Ω
        ≤ iDN (i - 1) (fun z => PhiN j (dCoord j u z)) Ω
          + iDN (i - 1) (fun z => PsiN j (dbarCoord j u z)) Ω :=
          iDN_add_le (i - 1) hφ hψ hΩu
      _ ≤ ENNReal.ofReal ‖PhiN j‖ * iDN (i - 1) (fun z => dCoord j u z) Ω
          + ENNReal.ofReal ‖PsiN j‖ * iDN (i - 1) (fun z => dbarCoord j u z) Ω :=
          add_le_add (comp_linear_le (PhiN j) (i - 1) α (hdz j) hΩu).1
            (comp_linear_le (PsiN j) (i - 1) α (hdb j) hΩu).1
      _ ≤ iDN (i - 1) (fun z => dCoord j u z) Ω
          + iDN (i - 1) (fun z => dbarCoord j u z) Ω := by
          refine add_le_add ?_ ?_
          · calc ENNReal.ofReal ‖PhiN j‖ * iDN (i - 1) (fun z => dCoord j u z) Ω
                ≤ 1 * iDN (i - 1) (fun z => dCoord j u z) Ω :=
                  mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_one.mpr (norm_PhiN_le j)) bot_le
              _ = iDN (i - 1) (fun z => dCoord j u z) Ω := one_mul _
          · calc ENNReal.ofReal ‖PsiN j‖ * iDN (i - 1) (fun z => dbarCoord j u z) Ω
                ≤ 1 * iDN (i - 1) (fun z => dbarCoord j u z) Ω :=
                  mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_one.mpr (norm_PsiN_le j)) bot_le
              _ = iDN (i - 1) (fun z => dbarCoord j u z) Ω := one_mul _
      _ ≤ holderNorm k α (fun z => dCoord j u z) Ω
          + holderNorm k α (fun z => dbarCoord j u z) Ω :=
          add_le_add (iterDerivNorm_le_holderNorm k α _ Ω hpred)
            (iterDerivNorm_le_holderNorm k α _ Ω hpred)
  calc iterDerivNorm i u Ω
      = iDN i u Ω := rfl
    _ = iDN ((i-1)+1) u Ω := by rw [hsucc]
    _ = iDN (i-1) (fun z => fderivWithin ℝ u Ω z) Ω := (iDN_fderivWithin (i-1) u Ω hΩu).symm
    _ = iDN (i-1)
          (fun z => ∑ j : Fin n, (PhiN j (dCoord j u z) + PsiN j (dbarCoord j u z))) Ω :=
        iDN_congr (fun z hz => by
          rw [fderivWithin_of_isOpen hΩ hz, fderiv_eq_sum_PhiN_PsiN])
    _ ≤ ∑ j : Fin n,
          iDN (i-1) (fun z => PhiN j (dCoord j u z) + PsiN j (dbarCoord j u z)) Ω :=
        iDN_sum_le Finset.univ (i-1) (fun j _ => hg j) hΩu
    _ ≤ ∑ j : Fin n, (holderNorm k α (fun z => dCoord j u z) Ω
          + holderNorm k α (fun z => dbarCoord j u z) Ω) :=
        Finset.sum_le_sum (fun j _ => hperj j)

/-- Bound on the Hölder seminorms of the derivatives of `u` of order `1 ≤ i ≤ k+1`. -/
private lemma holderSeminorm_le_wirtinger {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    (k : ℕ) (α : ℝ) {u : (Fin n → ℂ) → ℂ} (hu : ContDiff ℝ (k + 1) u)
    {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k + 1) :
    holderSeminorm i α u Ω ≤ ∑ j : Fin n, (holderNorm k α (fun z => dCoord j u z) Ω
        + holderNorm k α (fun z => dbarCoord j u z) Ω) := by
  have hΩu : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  have hpred : i - 1 ≤ k := by omega
  have hsucc : i - 1 + 1 = i := by omega
  have hdz : ∀ j : Fin n, ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => dCoord j u z) Ω := fun j =>
    (contDiffOn_dCoord hΩ hu j).of_le (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hpred))
  have hdb : ∀ j : Fin n, ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => dbarCoord j u z) Ω := fun j =>
    (contDiffOn_dbarCoord hΩ hu j).of_le (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hpred))
  have hg : ∀ j : Fin n, ContDiffOn ℝ (((i-1):ℕ):ℕ∞)
      (fun z => PhiN j (dCoord j u z) + PsiN j (dbarCoord j u z)) Ω := fun j =>
    ((PhiN j).contDiff.comp_contDiffOn (hdz j)).add
      ((PsiN j).contDiff.comp_contDiffOn (hdb j))
  have hperj : ∀ j : Fin n,
      hSN (i - 1) α (fun z => PhiN j (dCoord j u z) + PsiN j (dbarCoord j u z)) Ω
        ≤ holderNorm k α (fun z => dCoord j u z) Ω
          + holderNorm k α (fun z => dbarCoord j u z) Ω := by
    intro j
    have hφ : ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => PhiN j (dCoord j u z)) Ω :=
      (PhiN j).contDiff.comp_contDiffOn (hdz j)
    have hψ : ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => PsiN j (dbarCoord j u z)) Ω :=
      (PsiN j).contDiff.comp_contDiffOn (hdb j)
    calc hSN (i - 1) α (fun z => PhiN j (dCoord j u z) + PsiN j (dbarCoord j u z)) Ω
        ≤ hSN (i - 1) α (fun z => PhiN j (dCoord j u z)) Ω
          + hSN (i - 1) α (fun z => PsiN j (dbarCoord j u z)) Ω :=
          hSN_add_le (i - 1) α hφ hψ hΩu
      _ ≤ ENNReal.ofReal ‖PhiN j‖ * hSN (i - 1) α (fun z => dCoord j u z) Ω
          + ENNReal.ofReal ‖PsiN j‖ * hSN (i - 1) α (fun z => dbarCoord j u z) Ω :=
          add_le_add (comp_linear_le (PhiN j) (i - 1) α (hdz j) hΩu).2
            (comp_linear_le (PsiN j) (i - 1) α (hdb j) hΩu).2
      _ ≤ hSN (i - 1) α (fun z => dCoord j u z) Ω
          + hSN (i - 1) α (fun z => dbarCoord j u z) Ω := by
          refine add_le_add ?_ ?_
          · calc ENNReal.ofReal ‖PhiN j‖ * hSN (i - 1) α (fun z => dCoord j u z) Ω
                ≤ 1 * hSN (i - 1) α (fun z => dCoord j u z) Ω :=
                  mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_one.mpr (norm_PhiN_le j)) bot_le
              _ = hSN (i - 1) α (fun z => dCoord j u z) Ω := one_mul _
          · calc ENNReal.ofReal ‖PsiN j‖ * hSN (i - 1) α (fun z => dbarCoord j u z) Ω
                ≤ 1 * hSN (i - 1) α (fun z => dbarCoord j u z) Ω :=
                  mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_one.mpr (norm_PsiN_le j)) bot_le
              _ = hSN (i - 1) α (fun z => dbarCoord j u z) Ω := one_mul _
      _ ≤ holderNorm k α (fun z => dCoord j u z) Ω
          + holderNorm k α (fun z => dbarCoord j u z) Ω :=
          add_le_add (holderSeminorm_le_holderNorm k α _ Ω hpred)
            (holderSeminorm_le_holderNorm k α _ Ω hpred)
  calc holderSeminorm i α u Ω
      = hSN i α u Ω := rfl
    _ = hSN ((i-1)+1) α u Ω := by rw [hsucc]
    _ = hSN (i-1) α (fun z => fderivWithin ℝ u Ω z) Ω := (hSN_fderivWithin (i-1) α u Ω hΩu).symm
    _ = hSN (i-1) α
          (fun z => ∑ j : Fin n, (PhiN j (dCoord j u z) + PsiN j (dbarCoord j u z))) Ω :=
        hSN_congr (fun z hz => by
          rw [fderivWithin_of_isOpen hΩ hz, fderiv_eq_sum_PhiN_PsiN])
    _ ≤ ∑ j : Fin n,
          hSN (i-1) α (fun z => PhiN j (dCoord j u z) + PsiN j (dbarCoord j u z)) Ω :=
        hSN_sum_le Finset.univ (i-1) α (fun j _ => hg j) hΩu
    _ ≤ ∑ j : Fin n, (holderNorm k α (fun z => dCoord j u z) Ω
          + holderNorm k α (fun z => dbarCoord j u z) Ω) :=
        Finset.sum_le_sum (fun j _ => hperj j)

end Estimate

theorem holderNorm_le_wirtinger_coord {n : ℕ} {α : ℝ} (k : ℕ) {Ω : Set (Fin n → ℂ)}
    (hΩ : IsOpen Ω) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : (Fin n → ℂ) → ℂ, ContDiff ℝ (k + 1) u →
      Work.CR.Flat.holderNorm (k + 1) α u Ω
        ≤ ENNReal.ofReal K * (Work.CR.Flat.holderNorm 0 α u Ω
            + ∑ j : Fin n, (Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dCoord j u z) Ω
                + Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dbarCoord j u z) Ω)) := by
  refine ⟨2 * (k + 2), by positivity, ?_⟩
  intro u hu
  set A := Work.CR.Flat.holderNorm 0 α u Ω with hA
  set B := ∑ j : Fin n, (Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dCoord j u z) Ω
      + Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dbarCoord j u z) Ω) with hB
  have hterm : ∀ i ∈ Finset.range ((k+1)+1),
      iterDerivNorm i u Ω + holderSeminorm i α u Ω ≤ 2 * (A + B) := by
    intro i hi
    rw [Finset.mem_range] at hi
    obtain h0 | hpos := Nat.eq_zero_or_pos i
    · subst h0
      have h1 : iterDerivNorm 0 u Ω ≤ A := iterDerivNorm_le_holderNorm 0 α u Ω le_rfl
      have h2 : holderSeminorm 0 α u Ω ≤ A := holderSeminorm_le_holderNorm 0 α u Ω le_rfl
      calc iterDerivNorm 0 u Ω + holderSeminorm 0 α u Ω ≤ A + A := add_le_add h1 h2
        _ = 2 * A := (two_mul A).symm
        _ ≤ 2 * (A + B) := by gcongr; exact le_add_right le_rfl
    · have hi1 : 1 ≤ i := hpos
      have hik : i ≤ k + 1 := by omega
      have h1 := iterDerivNorm_le_wirtinger hΩ k α hu hi1 hik
      have h2 := holderSeminorm_le_wirtinger hΩ k α hu hi1 hik
      calc iterDerivNorm i u Ω + holderSeminorm i α u Ω ≤ B + B := add_le_add h1 h2
        _ = 2 * B := (two_mul B).symm
        _ ≤ 2 * (A + B) := by gcongr; exact le_add_left le_rfl
  calc Work.CR.Flat.holderNorm (k + 1) α u Ω
      = ∑ i ∈ Finset.range ((k+1)+1), (iterDerivNorm i u Ω + holderSeminorm i α u Ω) := rfl
    _ ≤ ∑ i ∈ Finset.range ((k+1)+1), (2 * (A + B)) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (2 * (k + 2)) * (A + B) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← mul_assoc]
        rw [show (2:ℝ≥0∞) = ((2:ℕ):ℝ≥0∞) from by norm_num, ← Nat.cast_mul]
        rw [show ENNReal.ofReal (2 * (k+2) : ℝ) = ((2*(k+2):ℕ) : ℝ≥0∞) from by
          rw [show (2*(k+2):ℝ) = ((2*(k+2):ℕ):ℝ) from by norm_num, ENNReal.ofReal_natCast]]
        congr 1
        ring_nf

end Work.CR.Flat.Holder
