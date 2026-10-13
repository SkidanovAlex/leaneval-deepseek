import Mathlib
import Submission.Work.WilE3.Taylor.CaseII.sphAux
import Submission.Work.WilE3.Taylor.CaseII.eaEval_pertMinor3_eq_smul_shfun
import Submission.Work.WilE3.Taylor.CaseII.contDiffOn_master_data
import Submission.Work.WilE5.Strat.flatConormalTools
import Submission.Work.WilE3.API.hasFDerivAt_eaEval

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / CaseII: **the determinant bridge for the boundary
  system** (`sphSys`).

  On `Uset = {μ ≠ 0}` the radial minor factors as `pertMinor3 l = G μ · shfun l`
  (`eaEval_pertMinor3_eq_smul_shfun`), where `G = sqGrad c Φ`.  Hence at a point `x ∈ Uset` at
  which the shear equations `shfun l v = 0` hold, the rows of the Jacobian of `sphSys` are the
  rows of the master Jacobian `fderiv (MasterFun c Φ y i₀ j₀ v) x`, with the rows different from
  `i₀` and `j₀` rescaled by the common nonzero factor `(G μ)(x)`.  A row rescaling by a common
  nonzero factor preserves injectivity, so `sysDet ≠ 0`.
-/

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
open WilkiesDesign.E

namespace Work.WilE3.Taylor.CaseII

variable {k r : ℕ}

/-! ## Elementary facts -/

/-- Componentwise value of `bmas`. -/
lemma bmas_apply_aux (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ : Fin k)
    (x : Fin k → ℝ) (θ : Fin 2 → ℝ) (i : Fin k) :
    (bmas c Φ y i₀ j₀ x θ) i
      = if i = i₀ ∨ i = j₀ then 0
        else shB1 c Φ y i₀ j₀ i x * θ 0 + shB2 c Φ y i₀ j₀ i x * θ 1 := by
  by_cases h : i = i₀ ∨ i = j₀
  · simp [bmas, h]
  · simp [bmas, h, ContinuousLinearMap.pi_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- The first coordinate of `shearParam`. -/
lemma shearParam_zero (v : Fin k → ℝ) (i₀ j₀ : Fin k) : shearParam v i₀ j₀ 0 = v i₀ := by
  simp [shearParam]

/-- The second coordinate of `shearParam`. -/
lemma shearParam_one (v : Fin k → ℝ) (i₀ j₀ : Fin k) : shearParam v i₀ j₀ 1 = v j₀ := by
  have h10 : ¬((1 : Fin 2) = 0) := by decide
  simp [shearParam, h10]

/-- Evaluation of the sphere polynomial. -/
lemma eaEval_sphereP_aux (c : EAChain k r) (y : Fin k → ℝ) (δ2 : ℝ) (x : Fin k → ℝ) :
    eaEval c (sphereP y δ2) x = Sq y x - δ2 := by
  simp [sphereP, Sq, Tq, eaEval, map_sum, map_sub, map_pow]

/-- On `Uset` the squared gradient `G = sqGrad c Φ` does not vanish. -/
lemma Gq_ne_zero_of_mem_Uset_aux (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ)
    (i₀ j₀ : Fin k) {x : Fin k → ℝ} (hx : x ∈ Uset c Φ y i₀ j₀) : Gq c Φ x ≠ 0 := by
  intro hG
  have hsum : ∑ l : Fin k, (Wq c Φ l x) ^ 2 = 0 := by
    rw [← hG, Gq, Work.WilE3.Taylor.eaEval_sqGrad]
    simp [Wq]
  have hzero : ∀ i : Fin k, Wq c Φ i x = 0 := by
    intro i
    have hle : (Wq c Φ i x) ^ 2 ≤ ∑ l : Fin k, (Wq c Φ l x) ^ 2 :=
      Finset.single_le_sum (fun l _ => sq_nonneg (Wq c Φ l x)) (Finset.mem_univ i)
    rw [hsum] at hle
    exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))
  exact hx (by simp [muq, hzero i₀, hzero j₀])

/-- `Uset = {μ ≠ 0}` is open. -/
lemma isOpen_Uset_aux (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ : Fin k) :
    IsOpen (Uset c Φ y i₀ j₀) := by
  rw [Uset]
  refine isOpen_compl_singleton.preimage ?_
  have hcont : Continuous fun z : Fin k → ℝ => muq c Φ y i₀ j₀ z := by
    unfold muq Wq Tq
    refine Continuous.sub (Continuous.mul ?_ ?_) (Continuous.mul ?_ ?_)
    · exact continuous_iff_continuousAt.mpr fun z =>
        (Work.WilE3.API.hasFDerivAt_eaEval c (eaD c i₀ Φ) z).continuousAt
    · exact (continuous_apply j₀).sub continuous_const
    · exact continuous_iff_continuousAt.mpr fun z =>
        (Work.WilE3.API.hasFDerivAt_eaEval c (eaD c j₀ Φ) z).continuousAt
    · exact (continuous_apply i₀).sub continuous_const
  exact hcont

/-! ## The coordinates of `MasterFun` -/

/-- The coordinates of `MasterFun`: row `i₀` is `Φ`, row `j₀` is `Sq y`, and row `l ∉ {i₀, j₀}`
is `shfun l v - v l`. -/
lemma MasterFun_apply_val (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ : Fin k)
    (v : Fin k → ℝ) (z : Fin k → ℝ) (i : Fin k) :
    MasterFun c Φ y i₀ j₀ v z i
      = if i = i₀ then eaEval c Φ z else if i = j₀ then Sq y z
        else shfun c Φ y i₀ j₀ i v z - v i := by
  by_cases h₁ : i = i₀
  · simp [MasterFun, Amas, bmas_apply_aux, shearParam, h₁]
  · by_cases h₂ : i = j₀
    · simp [MasterFun, Amas, bmas_apply_aux, shearParam, h₂]
    · have hnot : ¬(i = i₀ ∨ i = j₀) := not_or.mpr ⟨h₁, h₂⟩
      simp only [MasterFun, Amas, if_neg h₁, if_neg h₂, Pi.add_apply, bmas_apply_aux, hnot,
        ↓reduceIte, shearParam_zero, shearParam_one, shfun, Pi.add_apply]
      ring

/-! ## Derivatives of `MasterFun` -/

/-- The `i`-th coordinate of a linear map is the derivative of the `i`-th coordinate function. -/
lemma fderiv_apply_apply_aux (F : (Fin k → ℝ) → (Fin k → ℝ)) (x η : Fin k → ℝ) (i : Fin k)
    (hF : DifferentiableAt ℝ F x) :
    (fderiv ℝ F x η) i = (fderiv ℝ (fun z => F z i) x) η := by
  have h' : HasFDerivAt (fun z : Fin k → ℝ => F z i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).comp (fderiv ℝ F x)) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).hasFDerivAt.comp x
      hF.hasFDerivAt
  rw [h'.fderiv]
  rfl

/-- `MasterFun` is differentiable on `Uset`. -/
lemma differentiableAt_MasterFun (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ)
    (i₀ j₀ : Fin k) (v : Fin k → ℝ) {x : Fin k → ℝ} (hx : x ∈ Uset c Φ y i₀ j₀) :
    DifferentiableAt ℝ (MasterFun c Φ y i₀ j₀ v) x := by
  obtain ⟨hA, hb, _⟩ := contDiffOn_master_data c Φ y i₀ j₀
  have hxU : Uset c Φ y i₀ j₀ ∈ 𝓝 x := (isOpen_Uset_aux c Φ y i₀ j₀).mem_nhds hx
  have hA' : ContDiffAt ℝ 1 (Amas c Φ y i₀ j₀) x := hA.contDiffAt hxU
  have hb' : ContDiffAt ℝ 1 (bmas c Φ y i₀ j₀) x := hb.contDiffAt hxU
  have hcomp : ContDiffAt ℝ 1 (fun z => bmas c Φ y i₀ j₀ z (shearParam v i₀ j₀)) x :=
    hb'.clm_apply contDiffAt_const
  have hsum : ContDiffAt ℝ 1 (fun z => Amas c Φ y i₀ j₀ z
      + bmas c Φ y i₀ j₀ z (shearParam v i₀ j₀)) x := hA'.add hcomp
  exact hsum.differentiableAt one_ne_zero

/-- Reading off one coordinate of the master Jacobian on the standard basis vectors. -/
lemma MasterFun_fderiv_single (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ)
    (i₀ j₀ : Fin k) (v : Fin k → ℝ) (δ2 : ℝ) {x : Fin k → ℝ}
    (hx : x ∈ Uset c Φ y i₀ j₀) (j i : Fin k) :
    (fderiv ℝ (MasterFun c Φ y i₀ j₀ v) x) (Pi.single j 1) i
      = if i = i₀ then eaEval c (eaD c j Φ) x
        else if i = j₀ then eaEval c (eaD c j (sphereP y δ2)) x
        else (fderiv ℝ (fun z => shfun c Φ y i₀ j₀ i v z) x) (Pi.single j 1) := by
  have hMF := differentiableAt_MasterFun c Φ y i₀ j₀ v hx
  rw [fderiv_apply_apply_aux _ x _ i hMF]
  by_cases h₁ : i = i₀
  · rw [if_pos h₁]
    rw [show (fun z => MasterFun c Φ y i₀ j₀ v z i) = (fun z => eaEval c Φ z) from
      funext fun z => by rw [MasterFun_apply_val, if_pos h₁]]
    exact Work.WilE5.Strat.fderiv_eaEval_apply_single c Φ x j
  · by_cases h₂ : i = j₀
    · rw [if_neg h₁, if_pos h₂]
      rw [show (fun z => MasterFun c Φ y i₀ j₀ v z i)
            = (fun z => Sq y z) from
        funext fun z => by rw [MasterFun_apply_val, if_neg h₁, if_pos h₂]]
      rw [show (fun z : Fin k → ℝ => Sq y z)
            = (fun z : Fin k → ℝ => eaEval c (sphereP y δ2) z + δ2) from
        funext fun z => by rw [eaEval_sphereP_aux]; ring]
      rw [fderiv_add_const]
      exact Work.WilE5.Strat.fderiv_eaEval_apply_single c (sphereP y δ2) x j
    · rw [if_neg h₁, if_neg h₂]
      rw [show (fun z => MasterFun c Φ y i₀ j₀ v z i)
            = (fun z => shfun c Φ y i₀ j₀ i v z - v i) from
        funext fun z => by rw [MasterFun_apply_val, if_neg h₁, if_neg h₂]]
      rw [fderiv_sub_const]

/-! ## The derivative form of the shear identity -/

/-- Differentiability of the shear row. -/
lemma differentiableAt_shfun (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ)
    (i₀ j₀ : Fin k) (v : Fin k → ℝ) (l : Fin k) {x : Fin k → ℝ}
    (hx : x ∈ Uset c Φ y i₀ j₀) (h₁ : l ≠ i₀) (h₂ : l ≠ j₀) :
    DifferentiableAt ℝ (fun z => shfun c Φ y i₀ j₀ l v z) x := by
  have hMF := differentiableAt_MasterFun c Φ y i₀ j₀ v hx
  have hcomp : DifferentiableAt ℝ (fun z => MasterFun c Φ y i₀ j₀ v z l) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) l).differentiableAt.comp x hMF
  refine (hcomp.add_const (v l)).congr_of_eventuallyEq ?_
  filter_upwards with z
  rw [MasterFun_apply_val]
  simp [h₁, h₂]

/-- **The derivative form of the shear identity** for the boundary system: at a point of `Uset`
where the shear row vanishes, the gradient of the radial minor is `G μ` times the gradient of
the shear row. -/
lemma fderiv_pertMinor3_eq_smul_fderiv_shfun (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ)
    (v : Fin k → ℝ) (i₀ j₀ l : Fin k) {x : Fin k → ℝ} (hx : x ∈ Uset c Φ y i₀ j₀)
    (h₁ : l ≠ i₀) (h₂ : l ≠ j₀) (hl : shfun c Φ y i₀ j₀ l v x = 0) :
    fderiv ℝ (fun z => eaEval c (pertMinor3 c Φ v y i₀ j₀ l) z) x
      = (Gq c Φ x * muq c Φ y i₀ j₀ x) • fderiv ℝ (fun z => shfun c Φ y i₀ j₀ l v z) x := by
  have hxU : Uset c Φ y i₀ j₀ ∈ 𝓝 x := (isOpen_Uset_aux c Φ y i₀ j₀).mem_nhds hx
  -- the shear identity on the neighbourhood `Uset`
  have hFE : (fun z => eaEval c (pertMinor3 c Φ v y i₀ j₀ l) z) =ᶠ[𝓝 x]
      (fun z => (Gq c Φ z * muq c Φ y i₀ j₀ z) * shfun c Φ y i₀ j₀ l v z) := by
    filter_upwards [hxU] with z hz
    exact eaEval_pertMinor3_eq_smul_shfun c Φ y v i₀ j₀ l hz
  rw [hFE.fderiv_eq]
  -- the two factors are differentiable
  have hDdiff : DifferentiableAt ℝ (fun z => Gq c Φ z * muq c Φ y i₀ j₀ z) x := by
    have hG : DifferentiableAt ℝ (fun z : Fin k → ℝ => Gq c Φ z) x :=
      (Work.WilE3.API.hasFDerivAt_eaEval c (sqGrad c Φ) x).differentiableAt
    have hA : DifferentiableAt ℝ (fun z : Fin k → ℝ => Wq c Φ i₀ z) x :=
      (Work.WilE3.API.hasFDerivAt_eaEval c (eaD c i₀ Φ) x).differentiableAt
    have hB : DifferentiableAt ℝ (fun z : Fin k → ℝ => Wq c Φ j₀ z) x :=
      (Work.WilE3.API.hasFDerivAt_eaEval c (eaD c j₀ Φ) x).differentiableAt
    have hT₁ : DifferentiableAt ℝ (fun z : Fin k → ℝ => Tq y j₀ z) x :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) j₀).differentiableAt.sub_const
        (y j₀)
    have hT₂ : DifferentiableAt ℝ (fun z : Fin k → ℝ => Tq y i₀ z) x :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i₀).differentiableAt.sub_const
        (y i₀)
    exact hG.mul ((hA.mul hT₁).sub (hB.mul hT₂))
  have hSdiff : DifferentiableAt ℝ (fun z => shfun c Φ y i₀ j₀ l v z) x :=
    differentiableAt_shfun c Φ y i₀ j₀ v l hx h₁ h₂
  have hprod := hDdiff.hasFDerivAt.mul hSdiff.hasFDerivAt
  change fderiv ℝ (((fun z : Fin k → ℝ => Gq c Φ z * muq c Φ y i₀ j₀ z))
    * (fun z : Fin k → ℝ => shfun c Φ y i₀ j₀ l v z)) x = _
  rw [hprod.fderiv, hl, zero_smul, add_zero]

/-! ## The determinant bridge -/

/-- Row rescaling by a common nonzero factor, with two unscaled rows, preserves invertibility. -/
theorem det_ne_zero_of_mulVec_shear_two {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (L : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (i₀ j₀ : Fin k) (D : ℝ) (hD : D ≠ 0)
    (hL : Function.Injective L)
    (hrow : ∀ ξ : Fin k → ℝ, A.mulVec ξ = fun i => if i = i₀ ∨ i = j₀ then L ξ i else D * L ξ i) :
    A.det ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro ξ η hξη
  have hsub : A.mulVec (ξ - η) = 0 := by
    rw [Matrix.mulVec_sub, hξη, sub_self]
  have hcoord : ∀ i : Fin k,
      (if i = i₀ ∨ i = j₀ then L (ξ - η) i else D * L (ξ - η) i) = 0 := by
    intro i
    have h0 : (A.mulVec (ξ - η)) i = 0 := by rw [hsub]; rfl
    have h := congr_fun (hrow (ξ - η)) i
    rw [h] at h0
    simpa using h0
  have hLzero : L (ξ - η) = 0 := by
    funext i
    by_cases hi : i = i₀ ∨ i = j₀
    · have h := hcoord i
      rw [if_pos hi] at h
      exact h
    · have h := hcoord i
      rw [if_neg hi] at h
      exact (mul_eq_zero.mp h).resolve_left hD
  have hz : ξ - η = 0 := hL (by rw [hLzero, map_zero])
  exact sub_eq_zero.mp hz

/-! ## The entries of the system matrix -/

/-- The entrywise form of the shear identity at a solution: the `(i,j)` entry of the Jacobian of
`sphSys` is the `(i,j)` entry of the master Jacobian, except in the rows `l ∉ {i₀, j₀}` where it
is `G μ` times it. -/
lemma sysDetMatrix_entry (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (v : Fin k → ℝ)
    (δ2 : ℝ) (i₀ j₀ : Fin k) (hij : i₀ ≠ j₀) {x : Fin k → ℝ} (hx : x ∈ Uset c Φ y i₀ j₀)
    (hl : ∀ l : Fin k, l ≠ i₀ → l ≠ j₀ → shfun c Φ y i₀ j₀ l v x = 0) (i j : Fin k) :
    eaEval c (eaD c j (sphSys c Φ v y δ2 i₀ j₀ i)) x
      = if i = i₀ ∨ i = j₀ then (fderiv ℝ (MasterFun c Φ y i₀ j₀ v) x) (Pi.single j 1) i
        else (Gq c Φ x * muq c Φ y i₀ j₀ x)
          * (fderiv ℝ (MasterFun c Φ y i₀ j₀ v) x) (Pi.single j 1) i := by
  by_cases hi : i = i₀ ∨ i = j₀
  · rw [if_pos hi]
    rcases hi with hi | hi
    · simp only [sphSys, if_pos hi]
      rw [MasterFun_fderiv_single c Φ y i₀ j₀ v δ2 hx j i, if_pos hi]
    · have hne : ¬(i = i₀) := fun h => hij (h.symm.trans hi)
      simp only [sphSys, if_neg hne, if_pos hi]
      rw [MasterFun_fderiv_single c Φ y i₀ j₀ v δ2 hx j i, if_neg hne, if_pos hi]
  · rw [if_neg hi]
    have h₁ : i ≠ i₀ := fun h => hi (Or.inl h)
    have h₂ : i ≠ j₀ := fun h => hi (Or.inr h)
    rw [sphSys, if_neg h₁, if_neg h₂]
    rw [MasterFun_fderiv_single c Φ y i₀ j₀ v δ2 hx j i, if_neg h₁, if_neg h₂]
    rw [← Work.WilE5.Strat.fderiv_eaEval_apply_single c (pertMinor3 c Φ v y i₀ j₀ i) x j]
    rw [fderiv_pertMinor3_eq_smul_fderiv_shfun c Φ y v i₀ j₀ i hx h₁ h₂ (hl i h₁ h₂)]
    rfl

/-! ## The main lemma -/

set_option maxHeartbeats 2000000 in
theorem sysDet_sphSys_ne_zero_aux {k r : ℕ} (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ)
    (v : Fin k → ℝ) (δ2 : ℝ) (i₀ j₀ : Fin k) (hij : i₀ ≠ j₀) {x : Fin k → ℝ}
    (hx : x ∈ Uset c Φ y i₀ j₀)
    (hl : ∀ l : Fin k, l ≠ i₀ → l ≠ j₀ → shfun c Φ y i₀ j₀ l v x = 0)
    (hinj : Function.Injective (fderiv ℝ (MasterFun c Φ y i₀ j₀ v) x)) :
    sysDet c (sphSys c Φ v y δ2 i₀ j₀) x ≠ 0 := by
  have hG : Gq c Φ x ≠ 0 := Gq_ne_zero_of_mem_Uset_aux c Φ y i₀ j₀ hx
  have hD : Gq c Φ x * muq c Φ y i₀ j₀ x ≠ 0 := mul_ne_zero hG hx
  have hdet : sysDet c (sphSys c Φ v y δ2 i₀ j₀) x
      = (Matrix.of fun i j => eaEval c (eaD c j (sphSys c Φ v y δ2 i₀ j₀ i)) x).det := rfl
  rw [hdet]
  refine det_ne_zero_of_mulVec_shear_two
    (Matrix.of fun i j => eaEval c (eaD c j (sphSys c Φ v y δ2 i₀ j₀ i)) x)
    ((fderiv ℝ (MasterFun c Φ y i₀ j₀ v) x).toLinearMap) i₀ j₀
    (Gq c Φ x * muq c Φ y i₀ j₀ x) hD hinj ?_
  intro ξ
  funext i
  rw [Matrix.mulVec_apply, dotProduct]
  show ∑ j : Fin k, eaEval c (eaD c j (sphSys c Φ v y δ2 i₀ j₀ i)) x * ξ j
      = if i = i₀ ∨ i = j₀ then (fderiv ℝ (MasterFun c Φ y i₀ j₀ v) x) ξ i
        else (Gq c Φ x * muq c Φ y i₀ j₀ x) * (fderiv ℝ (MasterFun c Φ y i₀ j₀ v) x) ξ i
  have hLξ : (fderiv ℝ (MasterFun c Φ y i₀ j₀ v) x) ξ i
      = ∑ j : Fin k, (fderiv ℝ (MasterFun c Φ y i₀ j₀ v) x) (Pi.single j 1) i * ξ j := by
    have hξ : ξ = ∑ j : Fin k, ξ j • (Pi.single j 1 : Fin k → ℝ) := by
      funext t
      simp [Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]
    conv_lhs => rw [hξ]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hLξ]
  by_cases hi : i = i₀ ∨ i = j₀
  · rw [if_pos hi]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sysDetMatrix_entry c Φ y v δ2 i₀ j₀ hij hx hl i j, if_pos hi]
  · rw [if_neg hi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sysDetMatrix_entry c Φ y v δ2 i₀ j₀ hij hx hl i j, if_neg hi]
    ring

end Work.WilE3.Taylor.CaseII
