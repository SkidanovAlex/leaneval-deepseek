import Mathlib
import Submission.Work.Drive.intersection_parity

/-!
# Regularity of the chain difference map from transversality

The mod-2 intersection theory used in the chain route (`Submission/Work/Drive/intersection_parity.lean`)
rests on the hypothesis that the zeros of the difference map

`chainDiff D N : ℝ^5 → ℝ^4,  x ↦ D (sqPart x) - N (cbPart x)`

of a 2-chain `D : ℝ² → ℝ⁴` and a 3-chain `N : ℝ³ → ℝ⁴` are *regular* zeros, i.e. that
`fderiv ℝ (chainDiff D N) x` is surjective at every zero `x` in the box.  This file provides that
input from the geometric transversality hypothesis: `fderiv ℝ D` and `fderiv ℝ N` have together full
range at a zero.

The reason is elementary: `sqPart` and `cbPart` are the two coordinate projections of `ℝ⁵ = ℝ² × ℝ³`,
so `fderiv ℝ (chainDiff D N) x` factorises as

`(fderiv ℝ D (sqPart x)) ∘ sqPart − (fderiv ℝ N (cbPart x)) ∘ cbPart`

(square block first, cube block last), and since the two blocks can be prescribed independently, the
range of this difference is exactly the sum of the two ranges, `A.range ⊔ B.range`.

The two projections are packaged as the continuous linear maps `sqPartCLM` and `cbPartCLM`, and the
abstract linear-algebra facts are proved in a section of their own (`fderiv_comp_sub_comp`,
`range_comp_sub_comp`).
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology

noncomputable section

/-! ## The two block projections as continuous linear maps -/

/-- The projection of the five-box onto its "square" block, as a continuous linear map. -/
def sqPartCLM : EuclideanSpace ℝ (Fin 5) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ContinuousLinearMap.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm
    (ContinuousLinearMap.pi (fun i : Fin 2 => PiLp.proj 2 (fun _ : Fin 5 => ℝ) (sqIdx i)))

/-- The projection of the five-box onto its "cube" block, as a continuous linear map. -/
def cbPartCLM : EuclideanSpace ℝ (Fin 5) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearMap.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
    (ContinuousLinearMap.pi (fun j : Fin 3 => PiLp.proj 2 (fun _ : Fin 5 => ℝ) (cbIdx j)))

lemma sqPartCLM_apply (x : EuclideanSpace ℝ (Fin 5)) (i : Fin 2) :
    sqPartCLM x i = x (sqIdx i) := by
  simp [sqPartCLM, PiLp.proj_apply]

lemma cbPartCLM_apply (x : EuclideanSpace ℝ (Fin 5)) (j : Fin 3) :
    cbPartCLM x j = x (cbIdx j) := by
  simp [cbPartCLM, PiLp.proj_apply]

@[simp] lemma sqPartCLM_eq_sqPart (x : EuclideanSpace ℝ (Fin 5)) :
    sqPartCLM x = sqPart x := by
  ext i
  rw [sqPartCLM_apply, sqPart_apply]

@[simp] lemma cbPartCLM_eq_cbPart (x : EuclideanSpace ℝ (Fin 5)) :
    cbPartCLM x = cbPart x := by
  ext j
  rw [cbPartCLM_apply, cbPart_apply]

/-- The point of the five-box with prescribed square block `p` and cube block `q`. -/
def mkPart (p : EuclideanSpace ℝ (Fin 2)) (q : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 (Fin.addCases (motive := fun _ => ℝ) (fun i : Fin 2 => p i)
    (fun j : Fin 3 => q j))

@[simp] lemma sqPartCLM_mkPart (p : EuclideanSpace ℝ (Fin 2)) (q : EuclideanSpace ℝ (Fin 3)) :
    sqPartCLM (mkPart p q) = p := by
  ext i
  simp only [sqPartCLM_apply, mkPart, sqIdx, Fin.addCases_left]

@[simp] lemma cbPartCLM_mkPart (p : EuclideanSpace ℝ (Fin 2)) (q : EuclideanSpace ℝ (Fin 3)) :
    cbPartCLM (mkPart p q) = q := by
  ext j
  simp only [cbPartCLM_apply, mkPart, cbIdx, Fin.addCases_right]

/-- The two block projections jointly parametrise the five-box. -/
lemma exists_mkPart_eq (p : EuclideanSpace ℝ (Fin 2)) (q : EuclideanSpace ℝ (Fin 3)) :
    ∃ v : EuclideanSpace ℝ (Fin 5), sqPartCLM v = p ∧ cbPartCLM v = q :=
  ⟨mkPart p q, sqPartCLM_mkPart p q, cbPartCLM_mkPart p q⟩

/-! ## Abstract form of the two ingredients -/

section Abstract

variable {E E₁ E₂ F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The derivative of `x ↦ D (P x) - N (Q x)`.**  For smooth `D`, `N` and continuous linear
`P`, `Q`, the derivative is `(fderiv D (P x)) ∘ P - (fderiv N (Q x)) ∘ Q`. -/
lemma fderiv_comp_sub_comp (D : E₁ → F) (N : E₂ → F)
    (P : E →L[ℝ] E₁) (Q : E →L[ℝ] E₂)
    (hD : ContDiff ℝ Ctop D) (hN : ContDiff ℝ Ctop N) (x : E) :
    fderiv ℝ (fun y => D (P y) - N (Q y)) x
      = (fderiv ℝ D (P x)).comp P - (fderiv ℝ N (Q x)).comp Q := by
  have hDd : DifferentiableAt ℝ D (P x) := (hD.differentiable (by simp)) (P x)
  have hNd : DifferentiableAt ℝ N (Q x) := (hN.differentiable (by simp)) (Q x)
  have h : HasFDerivAt (fun y => D (P y) - N (Q y))
      ((fderiv ℝ D (P x)).comp P - (fderiv ℝ N (Q x)).comp Q) x :=
    (hDd.hasFDerivAt.comp x P.hasFDerivAt).sub (hNd.hasFDerivAt.comp x Q.hasFDerivAt)
  exact h.fderiv

/-- **The range of `A ∘ P - B ∘ Q`.**  If the pair `(P, Q)` is jointly surjective, the range of the
difference of the two composites is the sum of the ranges of `A` and `B`. -/
lemma range_comp_sub_comp (A : E₁ →L[ℝ] F) (B : E₂ →L[ℝ] F)
    (P : E →L[ℝ] E₁) (Q : E →L[ℝ] E₂)
    (hPQ : ∀ p q, ∃ v, P v = p ∧ Q v = q) :
    (A.comp P - B.comp Q).range = A.range ⊔ B.range := by
  refine le_antisymm ?_ ?_
  · rintro w ⟨v, rfl⟩
    exact Submodule.sub_mem _
      (Submodule.mem_sup_left (LinearMap.mem_range.mpr ⟨P v, rfl⟩))
      (Submodule.mem_sup_right (LinearMap.mem_range.mpr ⟨Q v, rfl⟩))
  · intro w hw
    rw [Submodule.mem_sup] at hw
    obtain ⟨a, ha, b, hb, hab⟩ := hw
    obtain ⟨p, hp⟩ := LinearMap.mem_range.mp ha
    obtain ⟨q, hq⟩ := LinearMap.mem_range.mp (Submodule.neg_mem _ hb)
    obtain ⟨v, hv₁, hv₂⟩ := hPQ p q
    have hp' : A p = a := hp
    have hq' : B q = -b := hq
    refine ⟨v, ?_⟩
    show A (P v) - B (Q v) = w
    rw [hv₁, hv₂, hp', hq', sub_neg_eq_add, hab]

end Abstract

/-! ## The target -/

/-- **The derivative of the chain difference map.**  Splitting the five-box into its square and cube
blocks, the derivative of `chainDiff D N` is the difference of the two block derivatives. -/
lemma fderiv_chainDiff (D : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (N : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hD : ContDiff ℝ Ctop D) (hN : ContDiff ℝ Ctop N) (x : EuclideanSpace ℝ (Fin 5)) :
    fderiv ℝ (chainDiff D N) x
      = (fderiv ℝ D (sqPart x)).comp sqPartCLM
        - (fderiv ℝ N (cbPart x)).comp cbPartCLM := by
  have hchain : chainDiff D N = fun y => D (sqPartCLM y) - N (cbPartCLM y) := by
    funext y
    simp only [chainDiff, sqPartCLM_eq_sqPart, cbPartCLM_eq_cbPart]
  rw [hchain, fderiv_comp_sub_comp D N sqPartCLM cbPartCLM hD hN x,
    sqPartCLM_eq_sqPart x, cbPartCLM_eq_cbPart x]

/-- **The range of the derivative of the chain difference map.**  At every point of the five-box, the
range of `fderiv ℝ (chainDiff D N) x` is the sum of the ranges of the two block derivatives. -/
lemma range_fderiv_chainDiff (D : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (N : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hD : ContDiff ℝ Ctop D) (hN : ContDiff ℝ Ctop N) (x : EuclideanSpace ℝ (Fin 5)) :
    (fderiv ℝ (chainDiff D N) x).range
      = (fderiv ℝ D (sqPart x)).range ⊔ (fderiv ℝ N (cbPart x)).range := by
  rw [fderiv_chainDiff D N hD hN x,
    range_comp_sub_comp _ _ _ _ (fun p q => exists_mkPart_eq p q)]

theorem regular_of_transverse
    (D : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (N : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) N)
    (hT : ∀ x ∈ Submission.Drive.unitBox 4, Work.Drive.chainDiff D N x = 0 →
      (fderiv ℝ D (Work.Drive.sqPart x)).range
        ⊔ (fderiv ℝ N (Work.Drive.cbPart x)).range = ⊤) :
    ∀ x ∈ Submission.Drive.unitBox 4, Work.Drive.chainDiff D N x = 0 →
      Function.Surjective (fderiv ℝ (Work.Drive.chainDiff D N) x) := by
  intro x hx hzero w
  have hw : w ∈ (fderiv ℝ D (sqPart x)).range ⊔ (fderiv ℝ N (cbPart x)).range := by
    rw [hT x hx hzero]
    exact Submodule.mem_top
  rw [Submodule.mem_sup] at hw
  obtain ⟨a, ha, b, hb, hab⟩ := hw
  obtain ⟨p, hp⟩ := LinearMap.mem_range.mp ha
  obtain ⟨q, hq⟩ := LinearMap.mem_range.mp (Submodule.neg_mem _ hb)
  obtain ⟨v, hv₁, hv₂⟩ := exists_mkPart_eq p q
  have hp' : (fderiv ℝ D (sqPart x)) p = a := hp
  have hq' : (fderiv ℝ N (cbPart x)) q = -b := hq
  refine ⟨v, ?_⟩
  rw [fderiv_chainDiff D N hD hN x]
  show (fderiv ℝ D (sqPart x)) (sqPartCLM v) - (fderiv ℝ N (cbPart x)) (cbPartCLM v) = w
  rw [hv₁, hv₂, hp', hq', sub_neg_eq_add, hab]

end

end Work.Drive
