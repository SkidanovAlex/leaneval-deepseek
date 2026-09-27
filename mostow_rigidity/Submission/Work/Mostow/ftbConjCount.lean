import Mathlib
import Submission.Work.Mostow.gapAEvenDefs
import Submission.Work.Mostow.conjCount
import Submission.Work.Mostow.conjCountCard
import Submission.Work.Mostow.frobeniusCommute
import Submission.Work.Mostow.zassenhausNilpotent
import Submission.Work.Mostow.linPartAux
import Submission.Work.Mostow.linPartExists
import Submission.Work.Mostow.isomNormTrace

set_option maxHeartbeats 2000000

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## Eigenvalues of the complexified linear part and the characteristic polynomial

For an isometry `g` of `ℍⁿ` fixing the base point, the chart action is a linear isometry `R`
(`linPartExists`).  Its lift `LambdaMat g` is `diag (Rmat R, 1)` (`Lam_map_eq_fromBlocks`), so the
characteristic polynomial of `(LambdaMat g).map ℂ` is that of the complexified matrix of `R`.  The
lemma below identifies the complex eigenvalues of `cAct R` with the roots of that polynomial. -/

private lemma csmulC (c : ℂ) (a b : ℝ) :
    ((↑(c.re * a - c.im * b) : ℂ) + Complex.I * ↑(c.im * a + c.re * b))
      = c * (↑a + Complex.I * ↑b) := by
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring

/-- The `ℂ`-linear coordinates of the complexification `E n × E n`: `(u, v) ↦ u + i v`. -/
def cplxCoords (n : ℕ) : (E n × E n) →ₗ[ℂ] (Fin n → ℂ) where
  toFun x := fun i => (x.1 i : ℂ) + Complex.I * (x.2 i : ℂ)
  map_add' x y := by
    ext i
    show ((↑((x.1 + y.1) i) : ℂ) + Complex.I * ↑((x.2 + y.2) i))
      = ((x.1 i : ℂ) + Complex.I * (x.2 i : ℂ)) + ((y.1 i : ℂ) + Complex.I * (y.2 i : ℂ))
    simp only [Pi.add_apply]
    rw [WithLp.ofLp_add, WithLp.ofLp_add]
    simp only [Pi.add_apply]
    push_cast
    ring
  map_smul' c x := by
    ext i
    rw [Margulis.csmul_apply]
    show ((↑((c.re • x.1 - c.im • x.2) i) : ℂ) + Complex.I * ↑((c.im • x.1 + c.re • x.2) i))
      = c * ((x.1 i : ℂ) + Complex.I * (x.2 i : ℂ))
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [WithLp.ofLp_sub, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_smul,
      WithLp.ofLp_smul, WithLp.ofLp_smul]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact csmulC c (x.1 i) (x.2 i)

@[simp] private lemma cplxCoords_apply (n : ℕ) (x : E n × E n) (i : Fin n) :
    cplxCoords n x i = (x.1 i : ℂ) + Complex.I * (x.2 i : ℂ) := rfl

private lemma cplxCoords_eq_zero {n : ℕ} {v : E n × E n} (h : cplxCoords n v = 0) : v = 0 := by
  have h1 : ∀ i : Fin n, (v.1 i : ℂ) + Complex.I * (v.2 i : ℂ) = 0 := by
    intro i
    have hh := congrFun h i
    simpa [cplxCoords_apply] using hh
  have hr : ∀ i : Fin n, v.1 i = 0 := by
    intro i
    have := congrArg Complex.re (h1 i)
    simpa [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] using this
  have hi : ∀ i : Fin n, v.2 i = 0 := by
    intro i
    have := congrArg Complex.im (h1 i)
    simpa [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] using this
  have hv1 : v.1 = 0 := by apply WithLp.ofLp_injective; funext i; simpa using hr i
  have hv2 : v.2 = 0 := by apply WithLp.ofLp_injective; funext i; simpa using hi i
  exact Prod.ext hv1 hv2

/-- `cplxCoords` intertwines `cAct R` with the complexified matrix of `R`. -/
lemma cplxCoords_cAct (n : ℕ) (R : E n ≃ₗᵢ[ℝ] E n) (x : E n × E n) :
    cplxCoords n (Margulis.cAct R x) =
      (Matrix.toLin' ((Rmat n R).map (algebraMap ℝ ℂ))) (cplxCoords n x) := by
  funext i
  rw [Matrix.toLin'_apply, Matrix.mulVec_apply_eq_sum]
  simp only [cplxCoords_apply, Margulis.cAct_apply, Matrix.map_apply, Complex.coe_algebraMap]
  have key : ((↑((R x.1) i) : ℂ) + Complex.I * ↑((R x.2) i))
      = ∑ j : Fin n, ((Rmat n R i j : ℝ) : ℂ) * ((x.1 j : ℂ) + Complex.I * (x.2 j : ℂ)) := by
    rw [← Rmat_apply R x.1 i, ← Rmat_apply R x.2 i]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  exact key

/-- If `μ` is an eigenvalue of the complexification `cAct R` of the real linear isometry `R`, then
`μ` is a root of the characteristic polynomial of the complexified matrix of `R`. -/
theorem ftb_cAct_eigen_root_charpoly (n : ℕ) (R : E n ≃ₗᵢ[ℝ] E n) (μ : ℂ)
    (hμ : Module.End.HasEigenvalue
      (Margulis.cAct R : (E n × E n) →ₗ[ℂ] (E n × E n)) μ) :
    (Matrix.charpoly ((Rmat n R).map (algebraMap ℝ ℂ))).IsRoot μ := by
  have hne : Module.End.eigenspace
      (Margulis.cAct R : (E n × E n) →ₗ[ℂ] (E n × E n)) μ ≠ ⊥ :=
    Module.End.hasEigenvalue_iff.mp hμ
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Module.End.mem_eigenspace_iff] at hv
  have hw0 : cplxCoords n v ≠ 0 := fun h => hv0 (cplxCoords_eq_zero h)
  have heig : Matrix.toLin' ((Rmat n R).map (algebraMap ℝ ℂ)) (cplxCoords n v)
      = μ • (cplxCoords n v) := by
    rw [← cplxCoords_cAct n R v]
    show cplxCoords n ((Margulis.cAct R : (E n × E n) →ₗ[ℂ] (E n × E n)) v)
      = μ • cplxCoords n v
    rw [hv, map_smul]
  have hne2 : Module.End.eigenspace
      (Matrix.toLin' ((Rmat n R).map (algebraMap ℝ ℂ))) μ ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr
      ⟨cplxCoords n v, (Module.End.mem_eigenspace_iff).mpr heig, hw0⟩
  have hμ2 : Module.End.HasEigenvalue
      (Matrix.toLin' ((Rmat n R).map (algebraMap ℝ ℂ))) μ :=
    Module.End.hasEigenvalue_iff.mpr hne2
  have hroot : (Matrix.toLin' ((Rmat n R).map (algebraMap ℝ ℂ))).charpoly.IsRoot μ :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).mp hμ2
  rwa [Matrix.charpoly_toLin'] at hroot

/-! ## Entry bounds for the spatial block -/

lemma ftb_Rmat_sub_dE_eq (R : E n ≃ₗᵢ[ℝ] E n) (i j : Fin n) :
    Rmat n R i j - dE n (Sum.inl i) (Sum.inl j)
      = inner ℝ (EuclideanSpace.single i (1:ℝ))
          (((R : E n →L[ℝ] E n) - 1) (EuclideanSpace.single j (1:ℝ))) := by
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_right,
    inner_single, inner_single, dE_apply, EuclideanSpace.single, PiLp.single_apply]
  simp [Rmat, Matrix.of_apply, Sum.inl.injEq]

lemma ftb_Rmat_sub_dE_abs_le (R : E n ≃ₗᵢ[ℝ] E n) (i j : Fin n) :
    |Rmat n R i j - dE n (Sum.inl i) (Sum.inl j)| ≤ ‖(R : E n →L[ℝ] E n) - 1‖ := by
  rw [ftb_Rmat_sub_dE_eq]
  have hn : ∀ k : Fin n, ‖EuclideanSpace.single k (1:ℝ)‖ = 1 := by
    intro k; rw [EuclideanSpace.norm_single, norm_one]
  calc |inner ℝ (EuclideanSpace.single i (1:ℝ))
        (((R : E n →L[ℝ] E n) - 1) (EuclideanSpace.single j (1:ℝ)))|
      ≤ ‖EuclideanSpace.single i (1:ℝ)‖
          * ‖((R : E n →L[ℝ] E n) - 1) (EuclideanSpace.single j (1:ℝ))‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ 1 * (‖(R : E n →L[ℝ] E n) - 1‖ * ‖EuclideanSpace.single j (1:ℝ)‖) := by
        rw [hn i]
        exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) zero_le_one
    _ = ‖(R : E n →L[ℝ] E n) - 1‖ := by
        rw [hn j, mul_one, one_mul]

/-! ## The bundle `tmpLPB` (with the characteristic-polynomial part proved) -/

/-- Bundle of facts about an isometry `g` fixing the base point, with linear part `R`:
the matrix `LambdaMat g` fixes the time vector, its spatial block is `R`, its trace is `tr R + 1`,
it is entrywise near the identity once `R` is near the identity in operator norm, and the complex
eigenvalues of `R` are roots of its characteristic polynomial. -/
theorem ftb_linPartBundle (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (g : PO n 1) (R : E n ≃ₗᵢ[ℝ] E n) (hR : ∀ u : E n, g • u = R u) :
    ((LambdaMat g).mulVec (Hyper.etime n) = Hyper.etime n) ∧
    (∀ u : E n, (LambdaMat g).mulVec (wvec u) = wvec (R u)) ∧
    ((LambdaMat g).trace = LinearMap.trace ℝ (E n) (R : E n →ₗ[ℝ] E n) + 1) ∧
    (∀ q : ℝ, ‖(R : E n →L[ℝ] E n) - 1‖ ≤ q → Near1 (ToO g) q) ∧
    (∀ μ : ℂ, Module.End.HasEigenvalue
        ((Margulis.cAct R : (E n × E n) →ₗ[ℂ] (E n × E n))) μ →
      (Matrix.charpoly ((LambdaMat g).map (algebraMap ℝ ℂ))).IsRoot μ) := by
  have hfix : Matrix.mulVec (LambdaMat g) (Hyper.etime n) = Hyper.etime n := by
    have h := hlift_LambdaMat hA g (0 : E n)
    rw [hR 0, R.map_zero, Hyper.hlift_zero] at h
    exact h.symm
  refine ⟨hfix, ?_, ?_, ?_, ?_⟩
  · intro u
    have hub := hlift_LambdaMat hA g u
    rw [hR u] at hub
    rw [hlift_eq_wvec_add u, Matrix.mulVec_add, Matrix.mulVec_smul, hfix] at hub
    rw [hlift_eq_wvec_add (R u), tpart_linIso] at hub
    exact (add_right_cancel hub).symm
  · have htr : LinearMap.trace ℝ (E n) (R : E n →ₗ[ℝ] E n) = ∑ i : Fin n, Rmat n R i i := by
      rw [LinearMap.trace_eq_sum_inner (R : E n →ₗ[ℝ] E n) (EuclideanSpace.basisFun (Fin n) ℝ)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [EuclideanSpace.basisFun_apply, inner_single]
      rfl
    have h1 : (LambdaMat g).trace = (∑ i : Fin n, Rmat n R i i) + 1 := by
      rw [Matrix.trace]
      simp only [Matrix.diag_apply]
      rw [Fintype.sum_sum_type]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Lam_inl_inl hA g R hR i i]
      · rw [Fin.sum_univ_one, Lam_inr_inr hA g R hR]
    rw [h1, ← htr]
  · intro q hq
    have hq0 : 0 ≤ q := le_trans (norm_nonneg ((R : E n →L[ℝ] E n) - 1)) hq
    intro i j
    rw [mat_ToO]
    rcases i with i | i <;> rcases j with j | j
    · rw [Lam_inl_inl hA g R hR i j]
      exact le_trans (ftb_Rmat_sub_dE_abs_le R i j) hq
    · rw [show j = (0 : Fin 1) from Subsingleton.elim j 0, Lam_inl_inr hA g R hR i]
      simpa [dE_apply, Sum.inl_ne_inr] using hq0
    · rw [show i = (0 : Fin 1) from Subsingleton.elim i 0, Lam_inr_inl hA g R hR j]
      simpa [dE_apply, Sum.inr_ne_inl] using hq0
    · rw [show i = (0 : Fin 1) from Subsingleton.elim i 0,
        show j = (0 : Fin 1) from Subsingleton.elim j 0, Lam_inr_inr hA g R hR]
      simpa [dE_apply] using hq0
  · intro μ hμ
    have h1 := ftb_cAct_eigen_root_charpoly n R μ hμ
    have h2 : (LambdaMat g).map (algebraMap ℝ ℂ)
        = Matrix.fromBlocks ((Rmat n R).map (algebraMap ℝ ℂ)) 0 0 1 :=
      Lam_map_eq_fromBlocks hA g R hR
    rw [h2, Matrix.charpoly_fromBlocks_zero₂₁]
    exact Polynomial.root_mul_right_of_isRoot
      (Matrix.charpoly (1 : Matrix (Fin 1) (Fin 1) ℂ)) h1

theorem ftbSmallAt (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (θ : ℝ) (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (g : PO n 1) (w p : E n), (∃ q : E n, g • q = q) → g • p = p →
      NearIdAt g w δ → NearIdAt g p θ := by
  obtain ⟨Ctr, hCtrpos, hCtr⟩ := (isomNormTrace n hA hI).2
  obtain ⟨q, hqpos, hq⟩ := Margulis.near1NearId n hn hA hI θ hθ
  have hCtr1 : 0 < Ctr + 1 := by linarith
  set δ : ℝ := min 1 (q ^ 2 / (2 * (Ctr + 1))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min one_pos (div_pos (pow_pos hqpos 2) (by linarith))
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_left _ _
  have hδq : 2 * Ctr * δ ≤ q ^ 2 := by
    have h1 : δ ≤ q ^ 2 / (2 * (Ctr + 1)) := by rw [hδdef]; exact min_le_right _ _
    have h5 : 2 * Ctr * δ ≤ 2 * Ctr * (q ^ 2 / (2 * (Ctr + 1))) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have h6 : 2 * Ctr * (q ^ 2 / (2 * (Ctr + 1))) ≤ q ^ 2 := by
      rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
      nlinarith [hCtrpos, sq_nonneg q]
    linarith [h5, h6]
  refine ⟨δ, hδpos, ?_⟩
  intro g w p hell hpfix hnear
  have hone : ∀ u : E n, (1 : PO n 1) • u = u := hA.2.2.2.1
  have hmul : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u) := hA.2.2.2.2.1
  obtain ⟨B, hB⟩ := (BoostTransitive n hA).1 p
  set h : PO n 1 := B⁻¹ * g * B with hhdef
  have hfix0 : h • (0 : E n) = 0 := by
    have hstep : h • (0 : E n) = B⁻¹ • (g • (B • (0 : E n))) := by
      rw [hhdef, hmul (B⁻¹ * g) B, hmul B⁻¹ g]
    rw [hstep, hB, hpfix]
    have hp0 : B⁻¹ • p = 0 := by
      rw [← hB, ← hmul B⁻¹ B (0 : E n), inv_mul_cancel, hone]
    exact hp0
  obtain ⟨R, hR⟩ := linPartExists n hA hI h hfix0
  obtain ⟨hL1, hL2, hL3, hL4, hL5⟩ := ftb_linPartBundle n hA hI h R hR
  have hnear' : NearIdAt h (B⁻¹ • w) δ := by
    have hw : B • (B⁻¹ • w) = w := by rw [← hmul B B⁻¹ w, mul_inv_cancel, hone]
    rw [hhdef]
    refine (nearIdAt_conj_point hA hI B g (B⁻¹ • w) δ).mpr ?_
    rw [hw]; exact hnear
  have htr : |(LambdaMat h).trace - ((n : ℝ) + 1)| ≤ Ctr * δ :=
    hCtr h (B⁻¹ • w) δ hδpos hδ1 hnear'
  have hnorm : ‖(R : E n →L[ℝ] E n) - 1‖ ≤ q := by
    have h1 : ‖(R : E n →L[ℝ] E n) - 1‖ ^ 2 ≤ 2 * ((n : ℝ) - LinearMap.trace ℝ (E n)
        (R : E n →ₗ[ℝ] E n)) := (isomNormTrace n hA hI).1 R
    have h2 : (n : ℝ) + 1 - (LambdaMat h).trace ≤ Ctr * δ := by
      have := abs_le.mp htr
      linarith [this.2]
    have h4 : ‖(R : E n →L[ℝ] E n) - 1‖ ^ 2 ≤ q ^ 2 := by
      have : (n : ℝ) - LinearMap.trace ℝ (E n) (R : E n →ₗ[ℝ] E n)
          = (n : ℝ) + 1 - (LambdaMat h).trace := by linarith [hL3]
      rw [this] at h1
      linarith [h1, h2, hδq]
    calc ‖(R : E n →L[ℝ] E n) - 1‖ = Real.sqrt ((‖(R : E n →L[ℝ] E n) - 1‖) ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (q ^ 2) := Real.sqrt_le_sqrt h4
      _ = q := Real.sqrt_sq hqpos.le
  have hnear1 : Near1 (ToO h) q := hL4 q hnorm
  have hth : NearIdAt h (0 : E n) θ := hq h hnear1
  have hback : NearIdAt (B⁻¹ * g * B) (0 : E n) θ := by
    rw [hhdef] at hth
    exact hth
  exact (gapA.nearIdAt_conj_iff hA hI hB θ g).mp hback




theorem ftbConjCountAux (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) :
    ∃ η₁ : ℝ, 0 < η₁ ∧ ∃ C : ℕ, ∀ Γ : Subgroup (PO n 1), IsDiscrete (SetLike.coe Γ) →
      ∀ b ∈ Γ, (∃ p : E n, b • p = p) → ∀ w : E n, NearIdAt b w η₁ →
        {c : PO n 1 | NearIdAt c w η₁ ∧ ∃ γ ∈ Γ, c = γ⁻¹ * b * γ}.Finite ∧
        {c : PO n 1 | NearIdAt c w η₁ ∧ ∃ γ ∈ Γ, c = γ⁻¹ * b * γ}.ncard ≤ C := by
  classical
  obtain ⟨θZ, hθZpos, hθZ⟩ := gapA.nilpotentPairNearIdAt n hn hA hI
  obtain ⟨θF, hθFpos, hθF⟩ := frobeniusCommute n hn hA hI
  obtain ⟨δ, hδpos, hδ⟩ := ftbSmallAt n hn hA hI θF hθFpos
  obtain ⟨θZs, hθZspos, hθZs⟩ := zassenhausNilpotent n hn hA hI
  set η₀ : ℝ := min (min θZ δ) (min θZs 1) with hη₀def
  have hη₀pos : 0 < η₀ := by
    rw [hη₀def]; exact lt_min (lt_min hθZpos hδpos) (lt_min hθZspos one_pos)
  have hη₀Z : η₀ ≤ θZ := by rw [hη₀def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hη₀δ : η₀ ≤ δ := by rw [hη₀def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hη₀Zs : η₀ ≤ θZs := by rw [hη₀def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  refine ⟨η₀, hη₀pos, (n + 2) ^ (2 * n + 1), ?_⟩
  intro Γ hdisc b hb hbFix w hbN
  have hone : ∀ u : E n, (1 : PO n 1) • u = u := hA.2.2.2.1
  have hmul : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u) := hA.2.2.2.2.1
  obtain ⟨p0, hp0⟩ := hbFix
  have hbtor : IsOfFinOrder b := gapA.isOfFinOrder_of_fixes_point n hA hI Γ hdisc b hb p0 hp0
  have key : ∀ F : Finset (PO n 1),
      (∀ c ∈ F, NearIdAt c w η₀ ∧ ∃ γ ∈ Γ, c = γ⁻¹ * b * γ) →
      F.card ≤ (n + 2) ^ (2 * n + 1) := by
    intro F hF
    set F' : Finset (PO n 1) := insert b F with hF'def
    have hTnear : ∀ c ∈ F, NearIdAt c w η₀ := fun c hc => (hF c hc).1
    have hTconj : ∀ c ∈ F, ∃ γ ∈ Γ, c = γ⁻¹ * b * γ := fun c hc => (hF c hc).2
    have hF'conj : ∀ c ∈ F', ∃ γ ∈ Γ, c = γ⁻¹ * b * γ := by
      intro c hc
      rw [hF'def, Finset.mem_insert] at hc
      rcases hc with rfl | hc
      · exact ⟨1, Γ.one_mem, by simp⟩
      · exact hTconj c hc
    have hF'sub : ∀ c ∈ F', c ∈ Γ := by
      intro c hc
      rw [hF'def, Finset.mem_insert] at hc
      rcases hc with rfl | hc
      · exact hb
      · obtain ⟨γ, hγ, hceq⟩ := hTconj c hc
        rw [hceq]
        exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) hb) hγ
    have hF'near : ∀ c ∈ F', NearIdAt c w η₀ := by
      intro c hc
      rw [hF'def, Finset.mem_insert] at hc
      rcases hc with rfl | hc
      · exact hbN
      · exact hTnear c hc
    have hF'tor : ∀ c ∈ F', IsOfFinOrder c := by
      intro c hc
      rw [hF'def, Finset.mem_insert] at hc
      rcases hc with rfl | hc
      · exact hbtor
      · obtain ⟨γ, hγ, hceq⟩ := hTconj c hc
        rw [hceq]
        obtain ⟨k, hkpos, hk⟩ := isOfFinOrder_iff_pow_eq_one.mp hbtor
        refine isOfFinOrder_iff_pow_eq_one.mpr ⟨k, hkpos, ?_⟩
        have hconj : (γ⁻¹ * b * γ) = (MulAut.conj γ⁻¹) b := by
          rw [MulAut.conj_apply]; simp
        rw [hconj, ← map_pow, hk, map_one]
    have hF'ell : ∀ c ∈ F', ∃ p : E n, c • p = p := by
      intro c hc
      rw [hF'def, Finset.mem_insert] at hc
      rcases hc with rfl | hc
      · exact ⟨p0, hp0⟩
      · obtain ⟨γ, hγ, hceq⟩ := hTconj c hc
        refine ⟨γ⁻¹ • p0, ?_⟩
        have hγinv : γ • (γ⁻¹ • p0) = p0 := by
          rw [← hmul γ γ⁻¹ p0, mul_inv_cancel, hone]
        rw [hceq, hmul, hmul, hγinv, hp0]
    have hF'comm : ∀ c ∈ F', ∀ c' ∈ F', c * c' = c' * c := fun c hc c' hc' =>
      pairCommute n hn hA hI θZs θF δ η₀ hθZspos hη₀Zs hη₀δ hθZs hθF hδ Γ hdisc w c c'
        (hF'sub c hc) (hF'sub c' hc') (hF'ell c hc) (hF'ell c' hc')
        (hF'near c hc) (hF'near c' hc')
    -- the finite subgroup generated by `F'` inside `Γ`
    let G : Finset Γ := F'.attach.image (fun c => (⟨c.1, hF'sub c.1 c.2⟩ : Γ))
    have hGnear : ∀ σ ∈ G, NearIdAt (σ : PO n 1) w θZs := by
      intro σ hσ
      obtain ⟨c, hc, hcσ⟩ := Finset.mem_image.mp hσ
      rw [← hcσ]
      exact fun u hu => lt_of_lt_of_le (hF'near c.1 c.2 u hu) hη₀Zs
    have hGell : ∀ σ ∈ G, ∃ p : E n, (σ : PO n 1) • p = p := by
      intro σ hσ
      obtain ⟨c, hc, hcσ⟩ := Finset.mem_image.mp hσ
      rw [← hcσ]
      exact hF'ell c.1 c.2
    haveI hfinHG : Finite ↥(Subgroup.closure (↑G : Set Γ)) :=
      finiteClosureNearIdAt n hn hA hI θZs hθZspos hθZs Γ hdisc G w hGnear hGell
    set Hp : Subgroup (PO n 1) := (Subgroup.closure (↑G : Set Γ)).map (Subgroup.subtype Γ)
      with hHpdef
    haveI hfinHp : Finite ↥Hp := by
      refine Finite.of_surjective
        (fun x : ↥(Subgroup.closure (↑G : Set Γ)) => (⟨(x : Γ), ⟨x, x.2, rfl⟩⟩ : ↥Hp)) ?_
      intro y
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    obtain ⟨p, hp⟩ := fixPoint_of_finite hA Hp hfinHp
    have hpF' : ∀ c ∈ F', c • p = p := by
      intro c hc
      apply hp
      refine Subgroup.mem_map.mpr ⟨⟨c, hF'sub c hc⟩, ?_, rfl⟩
      exact Subgroup.subset_closure (Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨⟨c, hc⟩, Finset.mem_attach F' ⟨c, hc⟩, rfl⟩))
    -- the boost at `p` and the linear parts
    obtain ⟨B, hB⟩ := (BoostTransitive n hA).1 p
    have hfix0 : ∀ c ∈ F', (B⁻¹ * c * B) • (0 : E n) = 0 := by
      intro c hc
      have hstep : (B⁻¹ * c * B) • (0 : E n) = B⁻¹ • (c • (B • (0 : E n))) := by
        rw [hmul (B⁻¹ * c) B, hmul B⁻¹ c]
      rw [hstep, hB, hpF' c hc]
      rw [← hB, ← hmul B⁻¹ B (0 : E n), inv_mul_cancel, hone]
    have hRex : ∀ c ∈ F', ∃ R : E n ≃ₗᵢ[ℝ] E n, ∀ u : E n, (B⁻¹ * c * B) • u = R u :=
      fun c hc => linPartExists n hA hI _ (hfix0 c hc)
    let Rof : ↥F' → E n ≃ₗᵢ[ℝ] E n := fun c => Classical.choose (hRex c.1 c.2)
    have hRof : ∀ (c : ↥F') (u : E n), (B⁻¹ * c.1 * B) • u = Rof c u :=
      fun c => Classical.choose_spec (hRex c.1 c.2)
    let A' : Finset (E n ≃ₗᵢ[ℝ] E n) := F'.attach.image Rof
    have hinjRof : Function.Injective Rof := by
      intro x y hxy
      have hact : ∀ u : E n, (B⁻¹ * x.1 * B) • u = (B⁻¹ * y.1 * B) • u := by
        intro u
        rw [hRof x u, hRof y u, hxy]
      exact Subtype.ext (eq_of_conj_smul_eq hA hact)
    have hA'card : A'.card = F'.card := by
      have h := Finset.card_image_of_injective (f := Rof) F'.attach hinjRof
      rw [Finset.card_attach] at h
      exact h
    -- the spectrum bound
    let Mb : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ := (LambdaMat b).map (algebraMap ℝ ℂ)
    let Sb : Finset ℂ := (Matrix.charpoly Mb).roots.toFinset
    have hScard : Sb.card ≤ n + 1 := by
      have h1 : Sb.card ≤ (Matrix.charpoly Mb).roots.card := Multiset.toFinset_card_le _
      have h2 : (Matrix.charpoly Mb).roots.card ≤ (Matrix.charpoly Mb).natDegree :=
        Polynomial.card_roots' _
      have h3 : (Matrix.charpoly Mb).natDegree = n + 1 := by
        rw [Matrix.charpoly_natDegree_eq_dim]; simp
      omega
    have hspec : ∀ a ∈ A', ∀ μ : ℂ,
        Module.End.HasEigenvalue ((Margulis.cAct a : (E n × E n) →ₗ[ℂ] (E n × E n))) μ →
        μ ∈ Sb := by
      intro a ha μ hμ
      obtain ⟨c, hc, hac⟩ := Finset.mem_image.mp ha
      rw [← hac] at hμ
      obtain ⟨-, -, -, -, hL5⟩ := ftb_linPartBundle n hA hI (B⁻¹ * c.1 * B) (Rof c) (hRof c)
      have hroot : (Matrix.charpoly ((LambdaMat (B⁻¹ * c.1 * B)).map (algebraMap ℝ ℂ))).IsRoot μ :=
        hL5 μ hμ
      have hchar : (Matrix.charpoly ((LambdaMat (B⁻¹ * c.1 * B)).map (algebraMap ℝ ℂ)))
          = (Matrix.charpoly Mb) := by
        obtain ⟨γ, hγ, hceq⟩ := hF'conj c.1 c.2
        have hinvB : LambdaMat B⁻¹ * LambdaMat B = 1 := by
          rw [← LambdaMat_mul hA, inv_mul_cancel, LambdaMat_one hA]
        have hinvB' : LambdaMat B * LambdaMat B⁻¹ = 1 := by
          rw [← LambdaMat_mul hA, mul_inv_cancel, LambdaMat_one hA]
        have hinvγ : LambdaMat γ⁻¹ * LambdaMat γ = 1 := by
          rw [← LambdaMat_mul hA, inv_mul_cancel, LambdaMat_one hA]
        have hinvγ' : LambdaMat γ * LambdaMat γ⁻¹ = 1 := by
          rw [← LambdaMat_mul hA, mul_inv_cancel, LambdaMat_one hA]
        have hLc : LambdaMat c.1 = LambdaMat γ⁻¹ * LambdaMat b * LambdaMat γ := by
          rw [hceq, LambdaMat_mul hA, LambdaMat_mul hA]
        have hLB : LambdaMat (B⁻¹ * c.1 * B) = LambdaMat B⁻¹ * LambdaMat c.1 * LambdaMat B := by
          rw [LambdaMat_mul hA, LambdaMat_mul hA]
        have eqB : LambdaMat (B⁻¹ * c.1 * B)
            = (LambdaMat B⁻¹ * LambdaMat γ⁻¹) * LambdaMat b * (LambdaMat γ * LambdaMat B) := by
          rw [hLB, hLc]; noncomm_ring
        have eqinv : (LambdaMat γ * LambdaMat B) * (LambdaMat B⁻¹ * LambdaMat γ⁻¹) = 1 := by
          have hstep : (LambdaMat γ * LambdaMat B) * (LambdaMat B⁻¹ * LambdaMat γ⁻¹)
              = LambdaMat γ * (LambdaMat B * LambdaMat B⁻¹) * LambdaMat γ⁻¹ := by noncomm_ring
          rw [hstep, hinvB']
          simp [hinvγ']
        set X : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ :=
          (LambdaMat γ * LambdaMat B).map (algebraMap ℝ ℂ) with hX
        set Y : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ :=
          (LambdaMat B⁻¹ * LambdaMat γ⁻¹).map (algebraMap ℝ ℂ) with hY
        have hmap (M N : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) :
            (M * N).map (algebraMap ℝ ℂ) = M.map (algebraMap ℝ ℂ) * N.map (algebraMap ℝ ℂ) :=
          Matrix.map_mul
        have hXY : X * Y = 1 := by
          rw [hX, hY, ← hmap, eqinv]
          rw [Matrix.map_one]
          · exact map_zero _
          · exact map_one _
        have hexp : (LambdaMat (B⁻¹ * c.1 * B)).map (algebraMap ℝ ℂ) = Y * Mb * X := by
          rw [eqB, hX, hY]
          simp only [Matrix.map_mul]
          noncomm_ring
        rw [hexp]
        have hcycle : Matrix.charpoly (Y * Mb * X) = Mb.charpoly := by
          rw [show Y * Mb * X = (Y * Mb) * X from rfl, Matrix.charpoly_mul_comm (Y * Mb) X]
          have h2 : X * (Y * Mb) = Mb := by rw [← mul_assoc, hXY, one_mul]
          rw [h2]
        rw [hcycle]
      rw [hchar] at hroot
      change μ ∈ (Matrix.charpoly Mb).roots.toFinset
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic Mb).ne_zero]
      exact hroot
    have hcommA : ∀ a ∈ A', ∀ a' ∈ A', a * a' = a' * a := by
      intro a ha a' ha'
      obtain ⟨c, hc, hac⟩ := Finset.mem_image.mp ha
      obtain ⟨d, hd, had⟩ := Finset.mem_image.mp ha'
      rw [← hac, ← had]
      have hcd : c.1 * d.1 = d.1 * c.1 := hF'comm c.1 c.2 d.1 d.2
      ext u
      have e1 : (Rof c * Rof d) u = (B⁻¹ * (c.1 * d.1) * B) • u := by
        show Rof c (Rof d u) = _
        rw [← hRof c (Rof d u), ← hRof d u]
        rw [← hmul (B⁻¹ * c.1 * B) (B⁻¹ * d.1 * B) u]
        congr 1
        group
      have e2 : (Rof d * Rof c) u = (B⁻¹ * (d.1 * c.1) * B) • u := by
        show Rof d (Rof c u) = _
        rw [← hRof d (Rof c u), ← hRof c u]
        rw [← hmul (B⁻¹ * d.1 * B) (B⁻¹ * c.1 * B) u]
        congr 1
        group
      rw [e1, e2, hcd]
    have hcardA := conjCountCard n Sb A' hcommA hspec
    rw [hA'card] at hcardA
    have hcardF' : F.card ≤ F'.card := by
      rw [hF'def]
      exact Finset.card_le_card (Finset.subset_insert b F)
    calc F.card ≤ F'.card := hcardF'
      _ ≤ (Sb.card + 1) ^ (2 * n + 1) := hcardA
      _ ≤ ((n + 2)) ^ (2 * n + 1) := by
          apply Nat.pow_le_pow_left
          omega
  constructor
  · by_contra hT
    rw [Set.not_finite] at hT
    obtain ⟨t, ht, htcard⟩ := hT.exists_subset_card_eq ((n + 2) ^ (2 * n + 1) + 1)
    have h1 := key t (fun c hc => ht hc)
    omega
  · have hfin : ({c : PO n 1 | NearIdAt c w η₀ ∧ ∃ γ ∈ Γ, c = γ⁻¹ * b * γ} : Set (PO n 1)).Finite := by
      by_contra hT
      rw [Set.not_finite] at hT
      obtain ⟨t, ht, htcard⟩ := hT.exists_subset_card_eq ((n + 2) ^ (2 * n + 1) + 1)
      have h1 := key t (fun c hc => ht hc)
      omega
    have h2 := key hfin.toFinset (fun c hc => hfin.mem_toFinset.mp hc)
    rwa [Set.ncard_eq_toFinset_card _ hfin]

end

/-- **Bounded number of short conjugates (G2 / ConjCount of the strata design).**
For `b ∈ Γ` elliptic (`∃ p, b • p = p`) in a *discrete* `Γ ≤ PO n 1` there are `η₁ > 0` and `C : ℕ`
such that at every point `w` at which `b` is `η₁`-near-identity, the set of conjugates
`γ⁻¹ b γ` (`γ ∈ Γ`) that are also `η₁`-near-identity at `w` is **finite** of cardinal at most `C`.

This is exactly the conclusion of `Work.Mostow.conjCount`
(`Submission/Work/Mostow/conjCount.lean`), whose proof is written out there except for three
*placeholder* lemmas at the top of that file (`tmpCC`, `tmpLPB`, `tmpINT`) which must be replaced by
the real lemmas (`Work.Mostow.conjCountCard` is proved: it is `tmpCC`; the `LambdaMat`/`Near1`/trace
statements `tmpLPB`, `tmpINT` show that the eigenvalues of `b` are roots of unity, that
`Near1 (ToO b) q ⟸ rotN ≤ q`, and that `|trace Λ(g) − (n+1)| ≤ C η₀`; look for proved counterparts
in `Submission/Work/Mostow/`).  Provable also directly: `zassenhausNilpotent` + `frobeniusCommute`
make the conjugates near `b` generate a finite abelian subgroup of `PO n 1`; counting its joint
characters bounds the number of conjugates. -/
theorem ftbConjCount (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) :
    ∃ η₁ : ℝ, 0 < η₁ ∧ ∃ C : ℕ, ∀ (Γ : Subgroup (PO n 1)) (b : PO n 1),
      IsDiscrete (SetLike.coe Γ) → b ∈ Γ → (∃ p : E n, b • p = p) → ∀ w : E n, NearIdAt b w η₁ →
        {c : PO n 1 | NearIdAt c w η₁ ∧ ∃ γ ∈ Γ, c = γ⁻¹ * b * γ}.Finite ∧
        {c : PO n 1 | NearIdAt c w η₁ ∧ ∃ γ ∈ Γ, c = γ⁻¹ * b * γ}.ncard ≤ C := by
  obtain ⟨η₁, hη, C, hC⟩ := ftbConjCountAux n hn hA hI
  exact ⟨η₁, hη, C, fun Γ b hdisc hb => hC Γ hdisc b hb⟩

end Work.Mostow
