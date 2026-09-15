import Submission.FUP.WirtingerCalc
import Submission.FUP.DbarAdjoint

open MeasureTheory
open scoped BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {d : ℕ}

/-!
# The Kohn--Morrey (Bochner--Kodaira--Nakano) identity and estimate

For a smooth real weight `φ` and a smooth compactly supported `(0,1)`-form `u : (Fin d → ℂ) → (Fin d → ℂ)`
we prove the *exact identity*

  `‖∂̄u‖²_{e^{-φ}} + ‖ϑu‖²_{e^{-φ}} = ∑_{j,k} ∫ ‖∂̄_j u_k‖² e^{-φ} + ∑_{j,k} ∫ (∂_j∂̄_k φ) u_j \bar u_k e^{-φ}`

where `ϑ = ∂̄^*` is the formal adjoint of `∂̄` w.r.t. the weighted inner product.  Combined with
Hörmander's pointwise positivity `∂∂̄φ ≥ κ` this yields the basic estimate
`∫ κ |u|² e^{-φ} ≤ ‖∂̄u‖² + ‖ϑu‖²` of the `∂̄`-theory.
-/

namespace Submission.FUP

section Adjoint

/-- **Weighted integration by parts for the holomorphic Wirtinger derivative `∂_j`.**
Obtained from `integral_dbar_mul_weighted_eq_neg` by conjugating everything. -/
theorem integral_partialZ_mul_weighted_eq_neg {F G ψ : (Fin d → ℂ) → ℂ} (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G) (hψ : ContDiff ℝ 1 ψ) (hsF : HasCompactSupport F)
    (hsG : HasCompactSupport G) (j : Fin d) :
    (∫ z, partialZ j F z * G z * Complex.exp (-(ψ z)))
      = - (∫ z, F z * partialZ j G z * Complex.exp (-(ψ z)))
        + (∫ z, F z * G z * partialZ j ψ z * Complex.exp (-(ψ z))) := by
  have hF' : ContDiff ℝ 1 (fun z => star (F z)) :=
    (Complex.conjCLE.contDiff (n := 1)).comp hF
  have hG' : ContDiff ℝ 1 (fun z => star (G z)) :=
    (Complex.conjCLE.contDiff (n := 1)).comp hG
  have hψ' : ContDiff ℝ 1 (fun z => star (ψ z)) :=
    (Complex.conjCLE.contDiff (n := 1)).comp hψ
  have hsF' : HasCompactSupport (fun z => star (F z)) := hsF.comp_left (by simp)
  have hsG' : HasCompactSupport (fun z => star (G z)) := hsG.comp_left (by simp)
  have h := integral_dbar_mul_weighted_eq_neg (F := fun z => star (F z))
    (G := fun z => star (G z)) (ψ := fun z => star (ψ z)) hF' hG' hψ' hsF' hsG' j
  -- rewrite the three integrals as conjugates
  have hexp : ∀ z, Complex.exp (-(star (ψ z))) = star (Complex.exp (-(ψ z))) := by
    intro z
    rw [show -(star (ψ z)) = star (-(ψ z)) from (map_neg (starRingEnd ℂ) (ψ z)).symm]
    exact Complex.exp_conj (-(ψ z))
  have hA : (∫ z, partialZbar j (fun z => star (F z)) z * star (G z)
        * Complex.exp (-(star (ψ z))))
      = star (∫ z, partialZ j F z * G z * Complex.exp (-(ψ z))) := by
    have hpt : ∀ z, partialZbar j (fun z => star (F z)) z * star (G z)
        * Complex.exp (-(star (ψ z)))
        = star (partialZ j F z * G z * Complex.exp (-(ψ z))) := by
      intro z
      rw [partialZbar_star j F, hexp z, star_mul, star_mul]
      ring
    rw [integral_congr_ae (μ := volume) (Filter.Eventually.of_forall hpt)]
    exact integral_conj
  have hB : (∫ z, star (F z) * partialZbar j (fun z => star (G z)) z
        * Complex.exp (-(star (ψ z))))
      = star (∫ z, F z * partialZ j G z * Complex.exp (-(ψ z))) := by
    have hpt : ∀ z, star (F z) * partialZbar j (fun z => star (G z)) z
        * Complex.exp (-(star (ψ z)))
        = star (F z * partialZ j G z * Complex.exp (-(ψ z))) := by
      intro z
      rw [partialZbar_star j G, hexp z, star_mul, star_mul]
      ring
    rw [integral_congr_ae (μ := volume) (Filter.Eventually.of_forall hpt)]
    exact integral_conj
  have hC : (∫ z, star (F z) * star (G z) * partialZbar j (fun z => star (ψ z)) z
        * Complex.exp (-(star (ψ z))))
      = star (∫ z, F z * G z * partialZ j ψ z * Complex.exp (-(ψ z))) := by
    have hpt : ∀ z, star (F z) * star (G z) * partialZbar j (fun z => star (ψ z)) z
        * Complex.exp (-(star (ψ z)))
        = star (F z * G z * partialZ j ψ z * Complex.exp (-(ψ z))) := by
      intro z
      rw [partialZbar_star j ψ, hexp z, star_mul, star_mul, star_mul]
      ring
    rw [integral_congr_ae (μ := volume) (Filter.Eventually.of_forall hpt)]
    exact integral_conj
  rw [hA, hB, hC] at h
  have h2 : star (∫ z, partialZ j F z * G z * Complex.exp (-(ψ z)))
      = star (- (∫ z, F z * partialZ j G z * Complex.exp (-(ψ z)))
        + (∫ z, F z * G z * partialZ j ψ z * Complex.exp (-(ψ z)))) := by
    rw [h]
    simp only [star_add, star_neg]
  exact star_injective h2

end Adjoint

end Submission.FUP

namespace Submission.FUP

section Covariant

/-- The complexification of a real weight. -/
noncomputable def phiC (φ : (Fin d → ℂ) → ℝ) : (Fin d → ℂ) → ℂ := fun z => (φ z : ℂ)

@[simp] lemma phiC_apply (φ : (Fin d → ℂ) → ℝ) (z : (Fin d → ℂ)) : phiC φ z = ((φ z : ℝ) : ℂ) := rfl

lemma contDiff_phiC {φ : (Fin d → ℂ) → ℝ} {n : ℕ∞ω} (hφ : ContDiff ℝ n φ) : ContDiff ℝ n (phiC φ) :=
  Complex.ofRealCLM.contDiff.comp hφ

/-- The covariant holomorphic derivative `D_j = ∂_j - ∂_jφ` (the `(1,0)`-part of the Chern
connection of the trivial line bundle with metric `e^{-φ}`). -/
noncomputable def covD (j : Fin d) (φ : (Fin d → ℂ) → ℝ) (f : (Fin d → ℂ) → ℂ) : (Fin d → ℂ) → ℂ :=
  fun z => partialZ j f z - f z * partialZ j (phiC φ) z

lemma covD_apply (j : Fin d) (φ : (Fin d → ℂ) → ℝ) (f : (Fin d → ℂ) → ℂ) (z : (Fin d → ℂ)) :
    covD j φ f z = partialZ j f z - f z * partialZ j (phiC φ) z := rfl

/-- **The weighted adjoint rule for the covariant derivative.**
`(D_j)^* = -∂̄_j` with respect to the pairing `⟨F,G⟩ = ∫ F conj G e^{-φ}`. -/
theorem integral_covD_mul_star_eq_neg {F G : (Fin d → ℂ) → ℂ} {φ : (Fin d → ℂ) → ℝ}
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) (hφ : ContDiff ℝ 1 φ)
    (hsF : HasCompactSupport F) (hsG : HasCompactSupport G) (j : Fin d) :
    (∫ z, covD j φ F z * star (G z) * Complex.exp (-(phiC φ z)))
      = - (∫ z, F z * star (partialZbar j G z) * Complex.exp (-(phiC φ z))) := by
  have hπ : ContDiff ℝ 1 (phiC φ) := contDiff_phiC hφ
  have hGs : ContDiff ℝ 1 (fun z => star (G z)) :=
    (Complex.conjCLE.contDiff (n := 1)).comp hG
  have hsGs : HasCompactSupport (fun z => star (G z)) := hsG.comp_left (by simp)
  have h := integral_partialZ_mul_weighted_eq_neg (F := F) (G := fun z => star (G z))
    (ψ := phiC φ) hF hGs hπ hsF hsGs j
  have hI1 : Integrable (fun z => partialZ j F z * star (G z) * Complex.exp (-(phiC φ z))) :=
    (((continuous_partialZ hF j).mul hGs.continuous).mul
      (Complex.continuous_exp.comp hπ.continuous.neg)).integrable_of_hasCompactSupport
      ((hsGs.mul_left (f := fun z => partialZ j F z)).mul_right
        (f' := fun z => Complex.exp (-(phiC φ z))))
  have hI2 : Integrable (fun z => F z * partialZ j (phiC φ) z * star (G z)
      * Complex.exp (-(phiC φ z))) :=
    (((hF.continuous.mul (continuous_partialZ hπ j)).mul hGs.continuous).mul
      (Complex.continuous_exp.comp hπ.continuous.neg)).integrable_of_hasCompactSupport
      (((hsF.mul_right (f' := fun z => partialZ j (phiC φ) z)).mul_right
        (f' := fun z => star (G z))).mul_right (f' := fun z => Complex.exp (-(phiC φ z))))
  have hI3 : Integrable (fun z => F z * star (G z) * partialZ j (phiC φ) z
      * Complex.exp (-(phiC φ z))) :=
    (((hF.continuous.mul hGs.continuous).mul (continuous_partialZ hπ j)).mul
      (Complex.continuous_exp.comp hπ.continuous.neg)).integrable_of_hasCompactSupport
      ((((hsF.mul_right (f' := fun z => star (G z)))).mul_right
        (f' := fun z => partialZ j (phiC φ) z)).mul_right (f' := fun z => Complex.exp (-(phiC φ z))))
  have hsplit : (∫ z, covD j φ F z * star (G z) * Complex.exp (-(phiC φ z)))
      = (∫ z, partialZ j F z * star (G z) * Complex.exp (-(phiC φ z)))
        - (∫ z, F z * partialZ j (phiC φ) z * star (G z)
            * Complex.exp (-(phiC φ z))) := by
    rw [← integral_sub hI1 hI2]
    apply integral_congr_ae
    filter_upwards with z
    rw [covD_apply]; ring
  have hpt : (∫ z, F z * partialZ j (phiC φ) z * star (G z) * Complex.exp (-(phiC φ z)))
      = (∫ z, F z * star (G z) * partialZ j (phiC φ) z * Complex.exp (-(phiC φ z))) := by
    apply integral_congr_ae
    filter_upwards with z
    ring
  have hstar : (∫ z, F z * partialZ j (fun z => star (G z)) z * Complex.exp (-(phiC φ z)))
      = (∫ z, F z * star (partialZbar j G z) * Complex.exp (-(phiC φ z))) := by
    apply integral_congr_ae
    filter_upwards with z
    rw [partialZ_star j G]
  rw [hsplit, hpt, h, hstar]
  ring

/-- **Commutator of `∂̄_j` and the covariant derivative.**  For a `C²` weight `φ` and a `C²`
function `g`,
`∂̄_j (D_k g) = D_k (∂̄_j g) - g · ∂̄_j ∂_k φ`. -/
theorem partialZbar_covD_apply {g : (Fin d → ℂ) → ℂ} (hg : ContDiff ℝ 2 g) (φ : (Fin d → ℂ) → ℝ)
    (hφ : ContDiff ℝ 2 φ) (j k : Fin d) (z : (Fin d → ℂ)) :
    partialZbar j (covD k φ g) z
      = covD k φ (fun w => partialZbar j g w) z
        - g z * partialZbar j (fun w => partialZ k (phiC φ) w) z := by
  have hg1 : DifferentiableAt ℝ g z := hg.contDiffAt.differentiableAt (by norm_num)
  have hga : DifferentiableAt ℝ (fun w => partialZ k g w) z :=
    (contDiff_partialZ_one (f := g) hg k).differentiable_one.differentiableAt
  have hφ1 : ContDiff ℝ 1 (fun w => partialZ k (phiC φ) w) :=
    contDiff_partialZ_one (contDiff_phiC (hφ.of_le (by norm_num))) k
  have hπd : DifferentiableAt ℝ (fun w => partialZ k (phiC φ) w) z :=
    hφ1.differentiable_one.differentiableAt
  have hsub : (fun w => covD k φ g w)
      = fun w => partialZ k g w - g w * partialZ k (phiC φ) w := rfl
  show partialZbar j (fun w => partialZ k g w - g w * partialZ k (phiC φ) w) z = _
  rw [partialZbar_sub (j := j) (f := fun w => partialZ k g w)
    (g := fun w => g w * partialZ k (phiC φ) w) hga (hg1.mul hπd)]
  rw [partialZbar_mul (j := j) (f := g) (g := fun w => partialZ k (phiC φ) w) hg1 hπd]
  rw [(partialZ_partialZbar_comm hg j k z).symm]
  rw [covD_apply]
  ring

end Covariant

end Submission.FUP

namespace Submission.FUP

section Helpers

/-- The complex exponential of a real weight is real-valued. -/
lemma exp_neg_phiC_eq (φ : (Fin d → ℂ) → ℝ) (z : (Fin d → ℂ)) :
    Complex.exp (-(phiC φ z)) = ((Real.exp (-(φ z)) : ℝ) : ℂ) := by
  rw [phiC_apply, ← Complex.ofReal_neg, Complex.ofReal_exp]

lemma star_exp_neg_phiC (φ : (Fin d → ℂ) → ℝ) (z : (Fin d → ℂ)) :
    star (Complex.exp (-(phiC φ z))) = Complex.exp (-(phiC φ z)) := by
  rw [exp_neg_phiC_eq, show star (((Real.exp (-(φ z)) : ℝ)) : ℂ)
    = (((Real.exp (-(φ z)) : ℝ)) : ℂ) from by
      simp only [Complex.star_def]; exact Complex.conj_ofReal _]

/-- The conjugate of `∂̄_j ∂_k φ` is the Hermitian Hessian `∂_j ∂̄_k φ` (for real `φ`). -/
lemma star_partialZbar_partialZ (φ : (Fin d → ℂ) → ℝ) (j k : Fin d) :
    (fun z => star (partialZbar j (fun w => partialZ k (phiC φ) w) z))
      = hermHess j k φ := by
  have h1 : (fun z => star (phiC φ z)) = phiC φ := by
    funext z; rw [phiC_apply]
    simp only [Complex.star_def]; rw [Complex.conj_ofReal]
  have h2 : (fun w => partialZ k (phiC φ) w) = fun w => star (partialZbar k (phiC φ) w) := by
    have h := partialZ_star k (phiC φ)
      -- partialZ k (fun z => star (phiC φ z)) = fun z => star (partialZbar k (phiC φ) z)
    rw [h1] at h
    exact h
  rw [show (fun z => star (partialZbar j (fun w => partialZ k (phiC φ) w) z))
      = fun z => star (partialZbar j (fun w => star (partialZbar k (phiC φ) w)) z) from by
        rw [h2]]
  rw [partialZbar_star j (partialZbar k (phiC φ))]
  funext z
  simp only [hermHess, star_star]
  rfl

end Helpers

end Submission.FUP

namespace Submission.FUP

section Identity

variable {u : (Fin d → ℂ) → (Fin d → ℂ)} {φ : (Fin d → ℂ) → ℝ}

/-- The `j`-th component of a `(0,1)`-form. -/
noncomputable def fComp (u : (Fin d → ℂ) → (Fin d → ℂ)) (j : Fin d) : (Fin d → ℂ) → ℂ := fun z => u z j

/-- `∂̄_j u_k`. -/
noncomputable def dbComp (u : (Fin d → ℂ) → (Fin d → ℂ)) (j k : Fin d) : (Fin d → ℂ) → ℂ :=
  fun z => partialZbar j (fComp u k) z

/-- The covariant derivative `D_j u_j`. -/
noncomputable def covComp (u : (Fin d → ℂ) → (Fin d → ℂ)) (φ : (Fin d → ℂ) → ℝ) (j : Fin d) : (Fin d → ℂ) → ℂ :=
  covD j φ (fComp u j)

@[simp] lemma fComp_apply (u : (Fin d → ℂ) → (Fin d → ℂ)) (j : Fin d) (z : (Fin d → ℂ)) :
    fComp u j z = u z j := rfl

@[simp] lemma dbComp_apply (u : (Fin d → ℂ) → (Fin d → ℂ)) (j k : Fin d) (z : (Fin d → ℂ)) :
    dbComp u j k z = partialZbar j (fComp u k) z := rfl

@[simp] lemma covComp_apply (u : (Fin d → ℂ) → (Fin d → ℂ)) (φ : (Fin d → ℂ) → ℝ) (j : Fin d) (z : (Fin d → ℂ)) :
    covComp u φ j z = covD j φ (fComp u j) z := rfl

lemma contDiff_dbComp {u : (Fin d → ℂ) → (Fin d → ℂ)} (hu : ∀ j, ContDiff ℝ 2 (fComp u j))
    (j k : Fin d) : ContDiff ℝ 1 (dbComp u j k) :=
  contDiff_partialZbar_one (hu k) j

lemma hasCompactSupport_dbComp {u : (Fin d → ℂ) → (Fin d → ℂ)}
    (hsu : ∀ j, HasCompactSupport (fComp u j)) (j k : Fin d) :
    HasCompactSupport (dbComp u j k) := hasCompactSupport_partialZbar (hsu k) j

lemma contDiff_covD_one {g : (Fin d → ℂ) → ℂ} (hg : ContDiff ℝ 2 g) {φ : (Fin d → ℂ) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (j : Fin d) : ContDiff ℝ 1 (covD j φ g) := by
  have h1 : ContDiff ℝ 1 (fun z => partialZ j g z) := contDiff_partialZ_one hg j
  have h2 : ContDiff ℝ 1 (fun z => partialZ j (phiC φ) z) :=
    contDiff_partialZ_one (contDiff_phiC (hφ.of_le (by norm_num))) j
  have h3 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hfun : covD j φ g = fun z => partialZ j g z - g z * partialZ j (phiC φ) z := rfl
  rw [hfun]
  exact h1.sub (h3.mul h2)

lemma hasCompactSupport_covD {g : (Fin d → ℂ) → ℂ} (hs : HasCompactSupport g) (φ : (Fin d → ℂ) → ℝ)
    (j : Fin d) : HasCompactSupport (covD j φ g) := by
  apply hs.mono'
  intro z hz
  by_contra hzf
  have h0 : fderiv ℝ g z = 0 := fderiv_of_notMem_tsupport ℝ hzf
  have hgz : g z = 0 := image_eq_zero_of_notMem_tsupport hzf
  exact hz (by simp only [covD, partialZ, h0, hgz, ContinuousLinearMap.zero_apply, mul_zero,
    zero_mul, sub_zero, zero_div])

lemma contDiff_covComp {u : (Fin d → ℂ) → (Fin d → ℂ)} (hu : ∀ j, ContDiff ℝ 2 (fComp u j))
    {φ : (Fin d → ℂ) → ℝ} (hφ : ContDiff ℝ 2 φ) (j : Fin d) : ContDiff ℝ 1 (covComp u φ j) :=
  contDiff_covD_one (hu j) hφ j

lemma hasCompactSupport_covComp {u : (Fin d → ℂ) → (Fin d → ℂ)}
    (hsu : ∀ j, HasCompactSupport (fComp u j)) (φ : (Fin d → ℂ) → ℝ) (j : Fin d) :
    HasCompactSupport (covComp u φ j) := hasCompactSupport_covD (hsu j) φ j

end Identity

end Submission.FUP

namespace Submission.FUP

section Pointwise

variable {u : (Fin d → ℂ) → (Fin d → ℂ)} {φ : (Fin d → ℂ) → ℝ}

/-- `(‖w‖² : ℂ) = w * star w`. -/
lemma ofReal_normSq_eq_mul_star (w : ℂ) : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * star w := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]
  ring


/-- `Re(a conj b) = Re(b conj a)`. -/
lemma mul_star_re_comm (a b : ℂ) : (a * star b).re = (b * star a).re := by
  simp only [Complex.mul_re]
  simp
  ring

lemma sum_sum_swap_norm (z : (Fin d → ℂ)) :
    (∑ j : Fin d, ∑ k : Fin d, ‖dbComp u k j z‖ ^ 2)
      = ∑ j : Fin d, ∑ k : Fin d, ‖dbComp u j k z‖ ^ 2 :=
  Finset.sum_comm

lemma sum_sum_swap_norm' (z : (Fin d → ℂ)) :
    (∑ j : Fin d, ∑ k : Fin d, (dbComp u k j z * star (dbComp u j k z)).re)
      = ∑ j : Fin d, ∑ k : Fin d, (dbComp u j k z * star (dbComp u k j z)).re := by
  rw [Finset.sum_comm]

/-- The pointwise identity behind the `A`-side of the Kohn--Morrey identity. -/
lemma kA_pointwise (z : (Fin d → ℂ)) :
    (1 / 2 : ℝ) * ∑ j : Fin d, ∑ k : Fin d, ‖dbComp u k j z - dbComp u j k z‖ ^ 2
      = (∑ j : Fin d, ∑ k : Fin d, ‖dbComp u j k z‖ ^ 2)
        - ∑ j : Fin d, ∑ k : Fin d, (dbComp u j k z * star (dbComp u k j z)).re := by
  have hterm : ∀ j k : Fin d, ‖dbComp u k j z - dbComp u j k z‖ ^ 2
      = ‖dbComp u k j z‖ ^ 2 + ‖dbComp u j k z‖ ^ 2
        - 2 * (dbComp u k j z * star (dbComp u j k z)).re := by
    intro j k
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_sub]
    simp only [Complex.star_def]
  have hsum : (∑ j : Fin d, ∑ k : Fin d, ‖dbComp u k j z - dbComp u j k z‖ ^ 2)
      = 2 * (∑ j : Fin d, ∑ k : Fin d, ‖dbComp u j k z‖ ^ 2)
        - 2 * (∑ j : Fin d, ∑ k : Fin d,
            (dbComp u j k z * star (dbComp u k j z)).re) := by
    simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sum_sum_swap_norm, sum_sum_swap_norm']
    ring
  rw [hsum]; ring

end Pointwise

section Integrability

variable {φ : (Fin d → ℂ) → ℝ}

lemma integrable_mul_exp {f : (Fin d → ℂ) → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    (hφ : Continuous φ) :
    Integrable (fun z => f z * Complex.exp (-(phiC φ z))) :=
  (hf.mul (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hφ).neg)))
    |>.integrable_of_hasCompactSupport
      (hs.mul_right (f' := fun z => Complex.exp (-(phiC φ z))))

lemma integrable_mul_exp_real {f : (Fin d → ℂ) → ℝ} (hf : Continuous f) (hs : HasCompactSupport f)
    (hφ : Continuous φ) :
    Integrable (fun z => f z * Real.exp (-(φ z))) :=
  (hf.mul (Real.continuous_exp.comp hφ.neg)).integrable_of_hasCompactSupport
    (hs.mul_right (f' := fun z => Real.exp (-(φ z))))

/-- `∫ (g : ℂ) e^{-φ} = (∫ g e^{-φ} : ℂ)` for a real-valued `g` (with the real exponential). -/
lemma integral_ofReal_mul_exp (g : (Fin d → ℂ) → ℝ) (φ : (Fin d → ℂ) → ℝ) :
    (∫ z, ((g z : ℝ) : ℂ) * Complex.exp (-(phiC φ z)))
      = Complex.ofReal (∫ z, g z * Real.exp (-(φ z))) := by
  have h1 : (∫ z, ((g z : ℝ) : ℂ) * Complex.exp (-(phiC φ z)))
      = ∫ z, ((g z * Real.exp (-(φ z)) : ℝ) : ℂ) := by
    apply integral_congr_ae
    filter_upwards with z
    rw [exp_neg_phiC_eq]; push_cast; ring
  rw [h1]
  exact integral_ofReal (𝕜 := ℂ) (μ := volume) (f := fun z : (Fin d → ℂ) => g z * Real.exp (-(φ z)))

lemma re_mul_exp_neg_phiC (a : ℂ) (φ : (Fin d → ℂ) → ℝ) (z : (Fin d → ℂ)) :
    RCLike.re (a * Complex.exp (-(phiC φ z))) = a.re * Real.exp (-(φ z)) := by
  rw [show Complex.exp (-(phiC φ z)) = ((Real.exp (-(φ z)) : ℝ) : ℂ) from exp_neg_phiC_eq φ z]
  rw [show RCLike.re (a * ((Real.exp (-(φ z)) : ℝ) : ℂ))
    = (a * ((Real.exp (-(φ z)) : ℝ) : ℂ)).re from rfl]
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- The real part of a weighted integral. -/
lemma integral_re_mul_exp {f : (Fin d → ℂ) → ℂ} {φ : (Fin d → ℂ) → ℝ}
    (hf : Integrable (fun z => f z * Complex.exp (-(phiC φ z)))) :
    (∫ z, f z * Complex.exp (-(phiC φ z))).re = ∫ z, (f z).re * Real.exp (-(φ z)) := by
  rw [show (∫ z, f z * Complex.exp (-(phiC φ z))).re
    = RCLike.re (∫ z, f z * Complex.exp (-(phiC φ z))) from rfl]
  rw [← integral_re hf]
  apply integral_congr_ae (μ := volume) (Filter.Eventually.of_forall fun z => ?_)
  exact re_mul_exp_neg_phiC (f z) φ z

end Integrability

end Submission.FUP

namespace Submission.FUP

section PerPair

/-- The conjugation relation for the weighted pairing. -/
lemma integral_mul_star_exp_conj {f g : (Fin d → ℂ) → ℂ} {φ : (Fin d → ℂ) → ℝ} :
    (∫ z, star (f z) * g z * Complex.exp (-(phiC φ z)))
      = star (∫ z, f z * star (g z) * Complex.exp (-(phiC φ z))) := by
  have h1 : (fun z => star (f z) * g z * Complex.exp (-(phiC φ z)))
      = fun z => star (f z * star (g z) * Complex.exp (-(phiC φ z))) := by
    funext z
    rw [star_mul, star_mul, star_star, star_exp_neg_phiC]
    ring
  rw [h1]
  exact integral_conj (μ := volume)

/-- **The per-pair step of the Kohn--Morrey identity.**
`∫ (D_j u_j) conj(D_k u_k) e^{-φ} = ∫ conj(∂̄_j u_k) ∂̄_k u_j e^{-φ} + ∫ u_j conj(u_k) (∂_j∂̄_kφ) e^{-φ}`. -/
lemma kohn_morrey_pair {u : (Fin d → ℂ) → (Fin d → ℂ)} {φ : (Fin d → ℂ) → ℝ}
    (hu : ∀ j, ContDiff ℝ 2 (fComp u j)) (hφ : ContDiff ℝ 2 φ)
    (hsu : ∀ j, HasCompactSupport (fComp u j)) (j k : Fin d) :
    (∫ z, covComp u φ j z * star (covComp u φ k z) * Complex.exp (-(phiC φ z)))
      = (∫ z, star (dbComp u j k z) * dbComp u k j z * Complex.exp (-(phiC φ z)))
        + (∫ z, fComp u j z * star (fComp u k z) * hermHess j k φ z
            * Complex.exp (-(phiC φ z))) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hφc : Continuous φ := hφ.continuous
  have hfcomp : ∀ j, Continuous (fComp u j) := fun j => (hu j).continuous
  have hZ : ContDiff ℝ 1 (fun w => partialZ k (phiC φ) w) :=
    contDiff_partialZ_one (contDiff_phiC hφ) k
  have hΩ : Continuous (covD k φ (dbComp u j k)) :=
    (continuous_partialZ (contDiff_dbComp hu j k) k).sub
      ((contDiff_dbComp hu j k).continuous.mul (continuous_partialZ (contDiff_phiC hφ1) k))
  have hstep1 : (∫ z, covComp u φ j z * star (covComp u φ k z) * Complex.exp (-(phiC φ z)))
      = - (∫ z, fComp u j z * star (partialZbar j (covComp u φ k) z)
          * Complex.exp (-(phiC φ z))) :=
    integral_covD_mul_star_eq_neg (F := fComp u j) (G := covComp u φ k)
      ((hu j).of_le (by norm_num)) (contDiff_covComp hu hφ k) hφ1 (hsu j)
      (hasCompactSupport_covComp hsu φ k) j
  have hcomm : ∀ z, partialZbar j (covComp u φ k) z
      = covD k φ (dbComp u j k) z - fComp u k z
          * partialZbar j (fun w => partialZ k (phiC φ) w) z :=
    fun z => partialZbar_covD_apply (g := fComp u k) (hu k) φ hφ j k z
  have hint1 : Integrable (fun z => fComp u j z * star (covD k φ (dbComp u j k) z)
      * Complex.exp (-(phiC φ z))) :=
    integrable_mul_exp ((hfcomp j).mul hΩ.star)
      ((hsu j).mul_right (f' := fun z => star (covD k φ (dbComp u j k) z))) hφc
  have hint2 : Integrable (fun z => fComp u j z * star (fComp u k z
      * partialZbar j (fun w => partialZ k (phiC φ) w) z) * Complex.exp (-(phiC φ z))) :=
    integrable_mul_exp ((hfcomp j).mul ((hfcomp k).mul (continuous_partialZbar hZ j)).star)
      ((hsu j).mul_right (f' := fun z => star (fComp u k z
        * partialZbar j (fun w => partialZ k (phiC φ) w) z))) hφc
  have hsplit : (∫ z, fComp u j z * star (partialZbar j (covComp u φ k) z)
        * Complex.exp (-(phiC φ z)))
      = (∫ z, fComp u j z * star (covD k φ (dbComp u j k) z) * Complex.exp (-(phiC φ z)))
        - (∫ z, fComp u j z * star (fComp u k z
            * partialZbar j (fun w => partialZ k (phiC φ) w) z)
          * Complex.exp (-(phiC φ z))) := by
    rw [← integral_sub hint1 hint2]
    apply integral_congr_ae (μ := volume) (Filter.Eventually.of_forall fun z => ?_)
    rw [hcomm z, star_sub]
    ring
  have hcurv : (∫ z, fComp u j z * star (fComp u k z
          * partialZbar j (fun w => partialZ k (phiC φ) w) z) * Complex.exp (-(phiC φ z)))
      = (∫ z, fComp u j z * star (fComp u k z) * hermHess j k φ z
          * Complex.exp (-(phiC φ z))) := by
    apply integral_congr_ae (μ := volume) (Filter.Eventually.of_forall fun z => ?_)
    rw [star_mul]
    rw [show star (partialZbar j (fun w => partialZ k (phiC φ) w) z) = hermHess j k φ z from
      congrFun (star_partialZbar_partialZ φ j k) z]
    ring
  have hQ := integral_covD_mul_star_eq_neg (F := dbComp u j k) (G := fComp u j)
    (contDiff_dbComp hu j k) ((hu j).of_le (by norm_num)) hφ1
    (hasCompactSupport_dbComp hsu j k) (hsu j) k
  have hQ' : (∫ z, star (fComp u j z) * covD k φ (dbComp u j k) z
        * Complex.exp (-(phiC φ z)))
      = - (∫ z, dbComp u j k z * star (dbComp u k j z)
          * Complex.exp (-(phiC φ z))) := by
    have h1 : (∫ z, star (fComp u j z) * covD k φ (dbComp u j k) z
          * Complex.exp (-(phiC φ z)))
        = (∫ z, covD k φ (dbComp u j k) z * star (fComp u j z)
            * Complex.exp (-(phiC φ z))) := by
      apply integral_congr_ae (μ := volume) (Filter.Eventually.of_forall fun z => ?_)
      ring
    rw [h1, hQ]
    simp only [dbComp_apply]
  have hc1 : (∫ z, star (fComp u j z) * covD k φ (dbComp u j k) z
        * Complex.exp (-(phiC φ z)))
      = star (∫ z, fComp u j z * star (covD k φ (dbComp u j k) z)
          * Complex.exp (-(phiC φ z))) := integral_mul_star_exp_conj
  have hc2 : (∫ z, star (dbComp u j k z) * dbComp u k j z * Complex.exp (-(phiC φ z)))
      = star (∫ z, dbComp u j k z * star (dbComp u k j z)
          * Complex.exp (-(phiC φ z))) := integral_mul_star_exp_conj
  have hstep5 : - (∫ z, fComp u j z * star (covD k φ (dbComp u j k) z)
        * Complex.exp (-(phiC φ z)))
      = (∫ z, star (dbComp u j k z) * dbComp u k j z * Complex.exp (-(phiC φ z))) := by
    rw [hc1] at hQ'
    rw [hc2]
    have h2 := congrArg star hQ'
    simp only [star_star, star_neg] at h2
    rw [h2, neg_neg]
  rw [hstep1, hsplit, hcurv, ← hstep5]
  ring

end PerPair

end Submission.FUP

namespace Submission.FUP

section BSide

variable {u : (Fin d → ℂ) → (Fin d → ℂ)} {φ : (Fin d → ℂ) → ℝ}

/-- `Re(conj a · b) = Re(a · conj b)`. -/
lemma star_mul_re_comm (a b : ℂ) : (star a * b).re = (a * star b).re := by
  simp only [Complex.mul_re]
  simp

/-- The pointwise identity `Re(w conj w e^{-φ}) = ‖w‖² e^{-φ}`. -/
lemma re_normSq_mul_exp (w : ℂ) (φ : (Fin d → ℂ) → ℝ) (z : (Fin d → ℂ)) :
    RCLike.re (w * star w * Complex.exp (-(phiC φ z))) = ‖w‖ ^ 2 * Real.exp (-(φ z)) := by
  rw [← ofReal_normSq_eq_mul_star w,
    show Complex.exp (-(phiC φ z)) = ((Real.exp (-(φ z)) : ℝ) : ℂ) from exp_neg_phiC_eq φ z,
    show RCLike.re (((‖w‖ ^ 2 : ℝ) : ℂ) * ((Real.exp (-(φ z)) : ℝ) : ℂ))
      = (((‖w‖ ^ 2 : ℝ) : ℂ) * ((Real.exp (-(φ z)) : ℝ) : ℂ)).re from rfl,
    Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- The complex expansion of the `B`-term, before taking real parts. -/
lemma kohn_morrey_B_aux {u : (Fin d → ℂ) → (Fin d → ℂ)} {φ : (Fin d → ℂ) → ℝ}
    (hu : ∀ j, ContDiff ℝ 2 (fComp u j)) (hφ : ContDiff ℝ 2 φ)
    (hsu : ∀ j, HasCompactSupport (fComp u j)) :
    (∫ z, (∑ j, covComp u φ j z) * star (∑ k, covComp u φ k z)
        * Complex.exp (-(phiC φ z)))
      = (∑ j, ∑ k, ∫ z, star (dbComp u j k z) * dbComp u k j z
            * Complex.exp (-(phiC φ z)))
        + (∑ j, ∑ k, ∫ z, fComp u j z * star (fComp u k z) * hermHess j k φ z
            * Complex.exp (-(phiC φ z))) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hφc : Continuous φ := hφ.continuous
  have hfcomp : ∀ j, Continuous (fComp u j) := fun j => (hu j).continuous
  have hIntc : ∀ j k, Integrable (fun z => covComp u φ j z * star (covComp u φ k z)
      * Complex.exp (-(phiC φ z))) := fun j k =>
    integrable_mul_exp (((contDiff_covComp hu hφ j).continuous).mul
        ((contDiff_covComp hu hφ k).continuous).star)
      ((hasCompactSupport_covComp hsu φ j).mul_right
        (f' := fun z => star (covComp u φ k z))) hφc
  have hfun : (fun z => (∑ j, covComp u φ j z) * star (∑ k, covComp u φ k z)
        * Complex.exp (-(phiC φ z)))
      = fun z => ∑ j, ∑ k, covComp u φ j z * star (covComp u φ k z)
          * Complex.exp (-(phiC φ z)) := by
    funext z
    have h1 : (∑ j, covComp u φ j z) * star (∑ k, covComp u φ k z)
        = ∑ j, ∑ k, covComp u φ j z * star (covComp u φ k z) := by
      rw [star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
    rw [h1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
  have hstep : (∫ z, ∑ j, ∑ k, covComp u φ j z * star (covComp u φ k z)
        * Complex.exp (-(phiC φ z)))
      = ∑ j, ∑ k, ∫ z, covComp u φ j z * star (covComp u φ k z)
          * Complex.exp (-(phiC φ z)) := by
    rw [integral_finsetSum Finset.univ
      (fun j _ => integrable_finsetSum _ (fun k _ => hIntc j k))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum Finset.univ (fun k _ => hIntc j k)]
  rw [hfun, hstep]
  have hpair : ∀ j k, (∫ z, covComp u φ j z * star (covComp u φ k z)
        * Complex.exp (-(phiC φ z)))
      = (∫ z, star (dbComp u j k z) * dbComp u k j z * Complex.exp (-(phiC φ z)))
        + (∫ z, fComp u j z * star (fComp u k z) * hermHess j k φ z
            * Complex.exp (-(phiC φ z))) := fun j k => kohn_morrey_pair hu hφ hsu j k
  have hL1 : (∑ j, ∑ k, ∫ z, covComp u φ j z * star (covComp u φ k z) * Complex.exp (-(phiC φ z)))
      = (∑ j, ∑ k, (∫ z, star (dbComp u j k z) * dbComp u k j z * Complex.exp (-(phiC φ z)))
          + (∑ j, ∑ k, ∫ z, fComp u j z * star (fComp u k z) * hermHess j k φ z * Complex.exp (-(phiC φ z)))) := by
    rw [show (∑ j, ∑ k, ∫ z, covComp u φ j z * star (covComp u φ k z) * Complex.exp (-(phiC φ z)))
        = (∑ j, ∑ k, ((∫ z, star (dbComp u j k z) * dbComp u k j z * Complex.exp (-(phiC φ z)))
            + (∫ z, fComp u j z * star (fComp u k z) * hermHess j k φ z * Complex.exp (-(phiC φ z))))) from by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      exact hpair j k]
    simp only [Finset.sum_add_distrib]
  rw [hL1]

end BSide

end Submission.FUP

namespace Submission.FUP

end Submission.FUP
namespace Submission.FUP

section Assemble

variable {u : (Fin d → ℂ) → (Fin d → ℂ)} {φ : (Fin d → ℂ) → ℝ}

lemma integrable_sum_sum_mul_exp_real {F : Fin d → Fin d → (Fin d → ℂ) → ℝ}
    {φc : (Fin d → ℂ) → ℝ} (hFc : ∀ j k, Continuous (F j k))
    (hFs : ∀ j k, HasCompactSupport (F j k)) (hφ : Continuous φc) :
    Integrable (fun z => (∑ j, ∑ k, F j k z) * Real.exp (-(φc z))) := by
  have h2 : Integrable (fun z => ∑ j, ∑ k, F j k z * Real.exp (-(φc z))) :=
    integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
      integrable_mul_exp_real (hFc j k) (hFs j k) hφ))
  refine h2.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Finset.sum_mul]

/-- Converting an integral of a double sum (with a real weight) into a double sum of integrals. -/
lemma integral_sum_sum_mul_exp_real {F : Fin d → Fin d → (Fin d → ℂ) → ℝ}
    {φc : (Fin d → ℂ) → ℝ}
    (hF : ∀ j k, Integrable (fun z => F j k z * Real.exp (-(φc z)))) :
    (∫ z, (∑ j, ∑ k, F j k z) * Real.exp (-(φc z)))
      = ∑ j, ∑ k, ∫ z, F j k z * Real.exp (-(φc z)) := by
  have h1 : (fun z => (∑ j, ∑ k, F j k z) * Real.exp (-(φc z)))
      = fun z => ∑ j, ∑ k, F j k z * Real.exp (-(φc z)) := by
    funext z; simp only [Finset.sum_mul]
  rw [h1, integral_finsetSum Finset.univ
    (fun j _ => integrable_finsetSum _ (fun k _ => hF j k))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum Finset.univ (fun k _ => hF j k)]

/-- The `A`-side of the Kohn--Morrey identity, in the form used for assembly. -/
lemma kohn_morrey_A {u : (Fin d → ℂ) → (Fin d → ℂ)} {φ : (Fin d → ℂ) → ℝ}
    (hu : ∀ j, ContDiff ℝ 2 (fComp u j)) (hφ : ContDiff ℝ 2 φ)
    (hsu : ∀ j, HasCompactSupport (fComp u j)) :
    (∫ z, ((1 / 2 : ℝ) * ∑ j, ∑ k, ‖dbComp u k j z - dbComp u j k z‖ ^ 2)
        * Real.exp (-(φ z)))
      = (∑ j, ∑ k, ∫ z, ‖dbComp u j k z‖ ^ 2 * Real.exp (-(φ z)))
        - (∑ j, ∑ k, ∫ z, (dbComp u j k z * star (dbComp u k j z)).re
            * Real.exp (-(φ z))) := by
  have hφc : Continuous φ := hφ.continuous
  have hfun : (fun z => ((1 / 2 : ℝ) * ∑ j, ∑ k, ‖dbComp u k j z - dbComp u j k z‖ ^ 2)
        * Real.exp (-(φ z)))
      = fun z => ((∑ j, ∑ k, ‖dbComp u j k z‖ ^ 2)
          - ∑ j, ∑ k, (dbComp u j k z * star (dbComp u k j z)).re) * Real.exp (-(φ z)) := by
    funext z; rw [kA_pointwise]
  have hsub : (fun z => ((∑ j, ∑ k, ‖dbComp u j k z‖ ^ 2)
          - ∑ j, ∑ k, (dbComp u j k z * star (dbComp u k j z)).re) * Real.exp (-(φ z)))
      = fun z => (∑ j, ∑ k, ‖dbComp u j k z‖ ^ 2) * Real.exp (-(φ z))
        - (∑ j, ∑ k, (dbComp u j k z * star (dbComp u k j z)).re) * Real.exp (-(φ z)) := by
    funext z; rw [sub_mul]
  have hnorm : ∀ j k, Continuous (fun z => ‖dbComp u j k z‖ ^ 2) :=
    fun j k => ((contDiff_dbComp hu j k).continuous.norm).pow 2
  have hsup : ∀ j k, HasCompactSupport (fun z => ‖dbComp u j k z‖ ^ 2) :=
    fun j k => (hasCompactSupport_dbComp hsu j k).comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)
  have hre : ∀ j k, Continuous (fun z => (dbComp u j k z * star (dbComp u k j z)).re) :=
    fun j k => Complex.continuous_re.comp ((contDiff_dbComp hu j k).continuous.mul
      (contDiff_dbComp hu k j).continuous.star)
  have hresup : ∀ j k, HasCompactSupport (fun z => (dbComp u j k z * star (dbComp u k j z)).re) :=
    fun j k => ((hasCompactSupport_dbComp hsu j k).mul_right
      (f' := fun z => star (dbComp u k j z))).comp_left (g := Complex.re) (by simp)
  have hI1 : Integrable (fun z => (∑ j, ∑ k, ‖dbComp u j k z‖ ^ 2) * Real.exp (-(φ z))) :=
    integrable_sum_sum_mul_exp_real hnorm hsup hφc
  have hI2 : Integrable (fun z => (∑ j, ∑ k,
        (dbComp u j k z * star (dbComp u k j z)).re) * Real.exp (-(φ z))) :=
    integrable_sum_sum_mul_exp_real hre hresup hφc
  have hS := integral_sum_sum_mul_exp_real (φc := φ)
    (F := fun j k z => ‖dbComp u j k z‖ ^ 2) (fun j k => integrable_mul_exp_real
      (hnorm j k) (hsup j k) hφc)
  have hSR := integral_sum_sum_mul_exp_real (φc := φ)
    (F := fun j k z => (dbComp u j k z * star (dbComp u k j z)).re)
    (fun j k => integrable_mul_exp_real (hre j k) (hresup j k) hφc)
  rw [hfun, hsub, integral_sub hI1 hI2, hS, hSR]

/-- The Hermitian Hessian of a `C²` function is continuous. -/
lemma continuous_hermHess {φ : (Fin d → ℂ) → ℝ} (hφ : ContDiff ℝ 2 φ) (j k : Fin d) :
    Continuous (hermHess j k φ) := by
  have h1 : ContDiff ℝ 1 (fun w => partialZbar k (phiC φ) w) :=
    contDiff_partialZbar_one (contDiff_phiC hφ) k
  have h2 : Continuous (fun z => partialZ j (fun w => partialZbar k (phiC φ) w) z) :=
    continuous_partialZ h1 j
  convert h2 using 1
  funext z
  rfl

/-- Expanding a product of sums. -/
lemma mul_star_eq_sum_sum {ι : Type*} [Fintype ι] (A : ι → ℂ) :
    (∑ j, A j) * star (∑ k, A k) = ∑ j, ∑ k, A j * star (A k) := by
  rw [star_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]

lemma sum_sum_mul_star_mul {ι : Type*} [Fintype ι] (A : ι → ℂ) (e : ℂ) :
    (∑ j, ∑ k, A j * star (A k) * e) = (∑ j, A j) * star (∑ k, A k) * e := by
  rw [mul_star_eq_sum_sum A, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]

/-- The `B`-side of the Kohn--Morrey identity (real form). -/
lemma kohn_morrey_B {u : (Fin d → ℂ) → (Fin d → ℂ)} {φ : (Fin d → ℂ) → ℝ}
    (hu : ∀ j, ContDiff ℝ 2 (fComp u j)) (hφ : ContDiff ℝ 2 φ)
    (hsu : ∀ j, HasCompactSupport (fComp u j)) :
    (∫ z, (‖∑ j, covComp u φ j z‖ ^ 2) * Real.exp (-(φ z)))
      = (∑ j, ∑ k, ∫ z, (dbComp u j k z * star (dbComp u k j z)).re
            * Real.exp (-(φ z)))
        + (∑ j, ∑ k, ∫ z, (fComp u j z * star (fComp u k z) * hermHess j k φ z).re
            * Real.exp (-(φ z))) := by
  have hφc : Continuous φ := hφ.continuous
  have hIntc : ∀ j k, Integrable (fun z => covComp u φ j z * star (covComp u φ k z)
      * Complex.exp (-(phiC φ z))) := fun j k =>
    integrable_mul_exp (((contDiff_covComp hu hφ j).continuous).mul
      ((contDiff_covComp hu hφ k).continuous).star)
      ((hasCompactSupport_covComp hsu φ j).mul_right
        (f' := fun z => star (covComp u φ k z))) hφc
  have hIntX : Integrable (fun z => (∑ j, covComp u φ j z) * star (∑ k, covComp u φ k z)
      * Complex.exp (-(phiC φ z))) := by
    have h2 : Integrable (fun z => ∑ j, ∑ k, covComp u φ j z * star (covComp u φ k z)
        * Complex.exp (-(phiC φ z))) :=
      integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hIntc j k))
    refine h2.congr (Filter.Eventually.of_forall fun z => ?_)
    exact sum_sum_mul_star_mul (fun j => covComp u φ j z) (Complex.exp (-(phiC φ z)))
  have hB1 : (∫ z, (‖∑ j, covComp u φ j z‖ ^ 2) * Real.exp (-(φ z)))
      = (∫ z, (∑ j, covComp u φ j z) * star (∑ k, covComp u φ k z)
          * Complex.exp (-(phiC φ z))).re := by
    rw [show (∫ z, (∑ j, covComp u φ j z) * star (∑ k, covComp u φ k z)
          * Complex.exp (-(phiC φ z))).re
        = RCLike.re (∫ z, (∑ j, covComp u φ j z) * star (∑ k, covComp u φ k z)
          * Complex.exp (-(phiC φ z))) from rfl]
    rw [← integral_re hIntX]
    apply integral_congr_ae (μ := volume) (Filter.Eventually.of_forall fun z => ?_)
    exact (re_normSq_mul_exp (∑ j, covComp u φ j z) φ z).symm
  have hintW : ∀ j k, Integrable (fun z => star (dbComp u j k z) * dbComp u k j z
      * Complex.exp (-(phiC φ z))) := fun j k =>
    integrable_mul_exp (((contDiff_dbComp hu j k).continuous).star.mul
      (contDiff_dbComp hu k j).continuous)
      ((hasCompactSupport_dbComp hsu k j).mul_left
        (f := fun z => star (dbComp u j k z))) hφc
  have hintC : ∀ j k, Integrable (fun z => fComp u j z * star (fComp u k z)
      * hermHess j k φ z * Complex.exp (-(phiC φ z))) := fun j k =>
    integrable_mul_exp (((hu j).continuous.mul (hu k).continuous.star).mul
      (continuous_hermHess hφ j k))
      (((hsu j).mul_right (f' := fun z => star (fComp u k z))).mul_right
        (f' := fun z => hermHess j k φ z)) hφc
  rw [hB1, kohn_morrey_B_aux hu hφ hsu, Complex.add_re]
  congr 1
  · rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_re_mul_exp (hf := hintW j k)]
    apply integral_congr_ae (μ := volume) (Filter.Eventually.of_forall fun z => ?_)
    rw [star_mul_re_comm]
  · rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_re_mul_exp (hf := hintC j k)]

/-- **The Kohn--Morrey (Bochner--Kodaira--Nakano) identity.**
For a smooth real weight `φ` and a smooth compactly supported `(0,1)`-form `u`,

`‖∂̄u‖²_{e^{-φ}} + ‖ϑu‖²_{e^{-φ}} = ∑_{j,k} ∫ ‖∂̄_j u_k‖² e^{-φ} + ∑_{j,k} ∫ (∂_j∂̄_k φ) u_j ar u_k e^{-φ}`,

the right-hand side being written with real parts. -/
theorem kohn_morrey_identity {u : (Fin d → ℂ) → (Fin d → ℂ)} {φ : (Fin d → ℂ) → ℝ}
    (hu : ∀ j, ContDiff ℝ 2 (fComp u j)) (hφ : ContDiff ℝ 2 φ)
    (hsu : ∀ j, HasCompactSupport (fComp u j)) :
    (∫ z, ((1 / 2 : ℝ) * ∑ j, ∑ k, ‖dbComp u k j z - dbComp u j k z‖ ^ 2)
        * Real.exp (-(φ z)))
      + (∫ z, (‖∑ j, covComp u φ j z‖ ^ 2) * Real.exp (-(φ z)))
    = (∑ j, ∑ k, ∫ z, ‖dbComp u j k z‖ ^ 2 * Real.exp (-(φ z)))
      + (∑ j, ∑ k, ∫ z, (fComp u j z * star (fComp u k z) * hermHess j k φ z).re
          * Real.exp (-(φ z))) := by
  rw [kohn_morrey_A hu hφ hsu, kohn_morrey_B hu hφ hsu]
  ring

/-- **The Kohn--Morrey estimate.**
Hoermander's basic estimate for the `∂̄`-complex: the pointwise positivity of the Hermitian Hessian
of `φ` bounds the weighted `L²`-norm of a compactly supported `(0,1)`-form by
`‖∂̄u‖²_{e^{-φ}} + ‖ϑu‖²_{e^{-φ}}`. -/
theorem kohn_morrey_estimate {u : (Fin d → ℂ) → (Fin d → ℂ)} {φ : (Fin d → ℂ) → ℝ}
    {κ : (Fin d → ℂ) → ℝ}
    (hu : ∀ j, ContDiff ℝ 2 (fComp u j)) (hφ : ContDiff ℝ 2 φ)
    (hsu : ∀ j, HasCompactSupport (fComp u j))
    (hκc : Continuous κ)
    (hpos : ∀ z (w : Fin d → ℂ), κ z * (∑ j, ‖w j‖ ^ 2)
      ≤ ∑ j, ∑ k, (hermHess j k φ z * w j * star (w k)).re) :
    (∫ z, κ z * (∑ j, ‖u z j‖ ^ 2) * Real.exp (-(φ z)))
      ≤ (∫ z, ((1 / 2 : ℝ) * ∑ j, ∑ k, ‖dbComp u k j z - dbComp u j k z‖ ^ 2)
            * Real.exp (-(φ z)))
        + (∫ z, (‖∑ j, covComp u φ j z‖ ^ 2) * Real.exp (-(φ z))) := by
  have hφc : Continuous φ := hφ.continuous
  have hU : ∀ j, Continuous (fun z => u z j) := fun j => (hu j).continuous
  rw [kohn_morrey_identity hu hφ hsu]
  have hSnn : 0 ≤ (∑ j, ∑ k, ∫ z, ‖dbComp u j k z‖ ^ 2 * Real.exp (-(φ z))) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
      integral_nonneg fun z => by positivity
  have hκInt : Integrable (fun z => κ z * (∑ j, ‖u z j‖ ^ 2) * Real.exp (-(φ z))) := by
    have h2 : Integrable (fun z => ∑ j, κ z * ‖u z j‖ ^ 2 * Real.exp (-(φ z))) :=
      integrable_finsetSum _ (fun j _ => integrable_mul_exp_real
        (hκc.mul ((hU j).norm.pow 2))
        (((hsu j).comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)).mul_left
          (f := fun z => κ z)) hφc)
    refine h2.congr (Filter.Eventually.of_forall fun z => ?_)
    show (∑ j, κ z * ‖u z j‖ ^ 2 * Real.exp (-(φ z)))
      = κ z * (∑ j, ‖u z j‖ ^ 2) * Real.exp (-(φ z))
    rw [Finset.mul_sum, Finset.sum_mul]
  have hcurvC : ∀ j k, Continuous (fun z =>
      (fComp u j z * star (fComp u k z) * hermHess j k φ z).re) := fun j k =>
    Complex.continuous_re.comp (((hu j).continuous.mul (hu k).continuous.star).mul
      (continuous_hermHess hφ j k))
  have hcurvS : ∀ j k, HasCompactSupport (fun z =>
      (fComp u j z * star (fComp u k z) * hermHess j k φ z).re) := fun j k =>
    (((hsu j).mul_right (f' := fun z => star (fComp u k z))).mul_right
      (f' := fun z => hermHess j k φ z)).comp_left (g := Complex.re) (by simp)
  have hCInt : Integrable (fun z => (∑ j, ∑ k,
      (fComp u j z * star (fComp u k z) * hermHess j k φ z).re)
      * Real.exp (-(φ z))) :=
    integrable_sum_sum_mul_exp_real hcurvC hcurvS hφc
  have hmono : (∫ z, κ z * (∑ j, ‖u z j‖ ^ 2) * Real.exp (-(φ z)))
      ≤ ∫ z, (∑ j, ∑ k, (fComp u j z * star (fComp u k z) * hermHess j k φ z).re)
          * Real.exp (-(φ z)) := by
    refine integral_mono hκInt hCInt fun z => ?_
    have h1 := hpos z (fun j => u z j)
    have h2 : (∑ j, ∑ k, (hermHess j k φ z * u z j * star (u z k)).re)
        = ∑ j, ∑ k, (fComp u j z * star (fComp u k z) * hermHess j k φ z).re := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      simp only [fComp_apply]
      ring_nf
    rw [h2] at h1
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
  have hCeq : (∑ j, ∑ k, ∫ z, (fComp u j z * star (fComp u k z) * hermHess j k φ z).re
        * Real.exp (-(φ z)))
      = ∫ z, (∑ j, ∑ k, (fComp u j z * star (fComp u k z) * hermHess j k φ z).re)
          * Real.exp (-(φ z)) :=
    (integral_sum_sum_mul_exp_real (φc := φ)
      (F := fun j k z => (fComp u j z * star (fComp u k z) * hermHess j k φ z).re)
      (fun j k => integrable_mul_exp_real (hcurvC j k) (hcurvS j k) hφc)).symm
  rw [hCeq]
  linarith

end Assemble

end Submission.FUP
