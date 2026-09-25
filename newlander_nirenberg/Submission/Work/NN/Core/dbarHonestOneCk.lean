import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.dbarHonestTwo
import Submission.Work.NN.Core.dbarHonestOne
import Submission.Work.NN.Core.dbarOneshotCk
import Submission.Work.NN.Core.recUHolderNormLevel
import Submission.Work.NN.Core.dbarSolverHonest
import Submission.Work.NN.Ratio.recULinearCont
import Submission.Work.NN.Ratio.contDiffOn_recU
import Submission.Work.NN.Ratio.contDiff_recU
import Submission.Work.NN.Ratio.recU_solves_local
import Submission.Work.NN.Ratio.Scale
import Submission.Work.NN.Ratio.PullBack
import Submission.Work.NN.Core.HonestAux
import Submission.Work.NN.Core.ratioRecUHolderNormLevel
import Submission.Work.NN.Core.dataOfHolderNormLevel
import Submission.Work.NN.Final.holderNorm_comp_linear

namespace Work.NN.Core

open scoped NNReal ENNReal ContDiff
open Set
open Work.CR.Flat

/-! ## Additivity and homogeneity of the telescoping operator on continuous data -/

/-- `G.recU` is additive on continuous data. -/
lemma recU_add_of_cont {n : ℕ} (G : Work.NN.Ratio.Geom n)
    {f g : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ j, Continuous (f j))
    (hg : ∀ j, Continuous (g j)) : G.recU (f + g) = G.recU f + G.recU g := by
  funext z
  have h := Work.NN.Ratio.recULinearCont G (1 : ℝ) f g hf hg z
  have hL : (fun j y => (1 : ℝ) • f j y + g j y) = f + g := by funext j y; simp
  rw [hL] at h
  simpa only [Pi.add_apply, one_smul] using h

/-- `G.recU` vanishes at every point on the zero datum. -/
lemma recU_zero_apply {n : ℕ} (G : Work.NN.Ratio.Geom n)
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ j, Continuous (f j)) (z : Fin n → ℂ) :
    G.recU (0 : Fin n → (Fin n → ℂ) → ℂ) z = 0 := by
  have h := Work.NN.Ratio.recULinearCont G (-1 : ℝ) f f hf hf z
  have hL : (fun j y => (-1 : ℝ) • f j y + f j y) = (0 : Fin n → (Fin n → ℂ) → ℂ) := by
    funext j y; simp
  rw [hL] at h
  simpa using h

/-- `G.recU` is homogeneous on continuous data. -/
lemma recU_smul_of_cont {n : ℕ} (G : Work.NN.Ratio.Geom n) (c : ℝ)
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ j, Continuous (f j)) :
    G.recU (c • f) = c • G.recU f := by
  funext z
  have hzero := recU_zero_apply G hf z
  have h := Work.NN.Ratio.recULinearCont G c f (0 : Fin n → (Fin n → ℂ) → ℂ) hf
    (fun _ => continuous_const) z
  have hL : (fun j y => c • f j y + (0 : Fin n → (Fin n → ℂ) → ℂ) j y) = c • f := by
    funext j y; simp
  rw [hL] at h
  rw [hzero, add_zero] at h
  simpa only [Pi.smul_apply] using h

/-! ## The telescoping operator on data continuous on a polydisc

The operator of the target is the linear extension (from the submodule of data which are
*continuous* on `polydisc 0 ρ`) of the explicit rescaled telescoping formula

  `f ↦ (geomOf η).recU (dataOf η ρ f) ∘ Ψ (scale η ρ)`.

Continuity on the polydisc is the weakest hypothesis under which the formula is linear, and it
covers all data of class `C^k` with `k ≥ 1` appearing in the statement. -/

/-- The datum families that are continuous on the polydisc `polydisc 0 ρ`, as a submodule. -/
def contOnPd0 (n : ℕ) (ρ : Fin n → ℝ) : Submodule ℝ (Fin n → (Fin n → ℂ) → ℂ) where
  carrier := {f | ∀ j, ContinuousOn (f j) (polydisc 0 ρ)}
  zero_mem' := fun _ => continuousOn_const
  add_mem' := fun hf hg j => (hf j).add (hg j)
  smul_mem' := fun c _ hf j => (hf j).const_smul c

lemma mem_contOnPd0 {n : ℕ} {ρ : Fin n → ℝ} {f : Fin n → (Fin n → ℂ) → ℂ} :
    f ∈ contOnPd0 n ρ ↔ ∀ j, ContinuousOn (f j) (polydisc 0 ρ) := Iff.rfl

/-- The rescaled telescoping formula on data continuous on the polydisc. -/
noncomputable def telOp {n : ℕ} (η : ℝ) (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) : contOnPd0 n ρ →ₗ[ℝ] ((Fin n → ℂ) → ℂ) where
  toFun f := fun z => (Work.NN.Ratio.geomOf η h0 h1).recU (Work.NN.Ratio.dataOf η ρ f.1)
    (Work.NN.Ratio.Psi (Work.NN.Ratio.scale η ρ) z)
  map_add' f g := by
    funext z
    have hcf : ∀ j, Continuous (Work.NN.Ratio.dataOf η ρ f.1 j) := fun j =>
      (contDiff_dataOfHonest (η := η) h0 h1 hρ (m := 0)
        (fun j => contDiffOn_zero.mpr (f.2 j)) j).continuous
    have hcg : ∀ j, Continuous (Work.NN.Ratio.dataOf η ρ g.1 j) := fun j =>
      (contDiff_dataOfHonest (η := η) h0 h1 hρ (m := 0)
        (fun j => contDiffOn_zero.mpr (g.2 j)) j).continuous
    have hdat : Work.NN.Ratio.dataOf η ρ (f + g).1
        = Work.NN.Ratio.dataOf η ρ f.1 + Work.NN.Ratio.dataOf η ρ g.1 := by
      rw [show (f + g).1 = f.1 + g.1 from rfl]
      show Work.NN.Ratio.pull (Work.NN.Ratio.scale η ρ)
          (Work.NN.Ratio.cutMul (Work.NN.Ratio.polCut η ρ) (f.1 + g.1))
        = Work.NN.Ratio.pull (Work.NN.Ratio.scale η ρ)
            (Work.NN.Ratio.cutMul (Work.NN.Ratio.polCut η ρ) f.1)
          + Work.NN.Ratio.pull (Work.NN.Ratio.scale η ρ)
            (Work.NN.Ratio.cutMul (Work.NN.Ratio.polCut η ρ) g.1)
      rw [map_add, Work.NN.Ratio.pull_add]
    rw [hdat, recU_add_of_cont _ hcf hcg]
    rfl
  map_smul' c f := by
    funext z
    have hcf : ∀ j, Continuous (Work.NN.Ratio.dataOf η ρ f.1 j) := fun j =>
      (contDiff_dataOfHonest (η := η) h0 h1 hρ (m := 0)
        (fun j => contDiffOn_zero.mpr (f.2 j)) j).continuous
    have hdat : Work.NN.Ratio.dataOf η ρ (c • f).1
        = c • Work.NN.Ratio.dataOf η ρ f.1 := by
      rw [show (c • f).1 = c • f.1 from rfl]
      show Work.NN.Ratio.pull (Work.NN.Ratio.scale η ρ)
          (Work.NN.Ratio.cutMul (Work.NN.Ratio.polCut η ρ) (c • f.1))
        = c • Work.NN.Ratio.pull (Work.NN.Ratio.scale η ρ)
            (Work.NN.Ratio.cutMul (Work.NN.Ratio.polCut η ρ) f.1)
      rw [map_smul, Work.NN.Ratio.pull_smul]
    rw [hdat, recU_smul_of_cont _ c hcf]
    rfl

/-- The `∂̄`-Poincaré operator of the target: the linear extension of the telescoping formula
from the data continuous on `polydisc 0 ρ` to all data. -/
noncomputable def T1Lin {n : ℕ} (η : ℝ) (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) : (Fin n → (Fin n → ℂ) → ℂ) →ₗ[ℝ] ((Fin n → ℂ) → ℂ) :=
  Classical.choose (LinearMap.exists_extend (telOp (n := n) η h0 h1 hρ))

lemma T1Lin_apply {n : ℕ} (η : ℝ) (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) (f : Fin n → (Fin n → ℂ) → ℂ) (hf : f ∈ contOnPd0 n ρ) :
    T1Lin η h0 h1 hρ f = fun z => (Work.NN.Ratio.geomOf η h0 h1).recU (Work.NN.Ratio.dataOf η ρ f)
      (Work.NN.Ratio.Psi (Work.NN.Ratio.scale η ρ) z) := by
  have h := Classical.choose_spec (LinearMap.exists_extend (telOp (n := n) η h0 h1 hρ))
  exact congrFun (congrArg DFunLike.coe h) ⟨f, hf⟩

/-! ## The equation solved by the operator, and its smoothness -/

/-- **Clause (A)**: on the polydisc where the rescaled datum is read from `f`, the operator `T1`
solves `∂̄ (T1 f) = f`, for data of class `C¹` which are closed on `polydisc 0 ρ`. -/
theorem T1_solves {n : ℕ} (η : ℝ) (hη0 : 0 < η) (hηhalf : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) {ρ'' : Fin n → ℝ}
    (hgeo : ∀ j, ρ'' j < Work.NN.Ratio.thre η * Work.NN.Ratio.scale η ρ j) :
    ∀ f : Fin n → (Fin n → ℂ) → ℂ,
      (∀ j, ContDiffOn ℝ 1 (f j) (polydisc 0 ρ)) →
      (∀ j l (z : Fin n → ℂ), z ∈ polydisc 0 ρ →
        dbarCoord j (f l) z = dbarCoord l (f j) z) →
      ∀ (j : Fin n) (z : Fin n → ℂ), z ∈ polydisc 0 ρ'' →
        dbarCoord j (T1Lin η hη0 hηhalf hρ f) z = f j z := by
  intro f hf hcl j z hz
  have hmem : f ∈ contOnPd0 n ρ := fun i => (hf i).continuousOn
  rw [T1Lin_apply η hη0 hηhalf hρ f hmem]
  show dbarCoord j
    (fun z => (Work.NN.Ratio.geomOf (n := n) η hη0 hηhalf).recU (Work.NN.Ratio.dataOf η ρ f)
      (Work.NN.Ratio.Psi (Work.NN.Ratio.scale η ρ) z)) z = f j z
  have hcont : ∀ i, ContDiff ℝ 1 (Work.NN.Ratio.dataOf η ρ f i) :=
    fun i => contDiff_dataOfHonest (m := 1) hη0 hηhalf hρ hf i
  have hUdiff : DifferentiableAt ℝ
      (fun z => (Work.NN.Ratio.geomOf (n := n) η hη0 hηhalf).recU (Work.NN.Ratio.dataOf η ρ f) z)
      (Work.NN.Ratio.Psi (Work.NN.Ratio.scale η ρ) z) :=
    ((Work.NN.Ratio.contDiff_recU (G := Work.NN.Ratio.geomOf (n := n) η hη0 hηhalf) (k := 0)
      hcont).differentiable one_ne_zero).differentiableAt
  rw [Work.NN.Ratio.dbarCoord_Psi (Work.NN.Ratio.scale η ρ) j hUdiff]
  have hdatacl : ∀ j l (y : Fin n → ℂ),
      (∀ m, ‖y m‖ < (Work.NN.Ratio.geomOf (n := n) η hη0 hηhalf).T) →
      dbarCoord l (Work.NN.Ratio.dataOf η ρ f j) y
        = dbarCoord j (Work.NN.Ratio.dataOf η ρ f l) y := by
    intro j l y hy
    refine dataOf_closedOn hη0 hηhalf hρ hf hcl j l y ?_
    simpa [Work.NN.Ratio.geomOf_T, Work.CR.Flat.polydisc] using hy
  have hR : (Work.NN.Ratio.geomOf (n := n) η hη0 hηhalf).b
      < (Work.NN.Ratio.geomOf (n := n) η hη0 hηhalf).T := by
    rw [Work.NN.Ratio.geomOf_b, Work.NN.Ratio.geomOf_T]
    exact Work.NN.Ratio.thrb_lt_thrT hη0
  have hsol := Work.NN.Ratio.recU_solves_local
    (Work.NN.Ratio.geomOf (n := n) η hη0 hηhalf) hR hcont hdatacl
  rw [hsol j (Work.NN.Ratio.Psi (Work.NN.Ratio.scale η ρ) z) (fun l => by
    rw [Work.NN.Ratio.geomOf_e]
    exact Work.NN.Ratio.psi_mem_solve hη0 hηhalf hρ
      (fun l => lt_trans (by simpa using hz l) (hgeo l)) l)]
  have hzcut : ∀ l, ‖z l‖ ≤ Work.NN.Ratio.cutIn η ρ l := by
    intro l
    refine le_of_lt (lt_trans (lt_trans (by simpa using hz l) (hgeo l)) ?_)
    rw [Work.NN.Ratio.cutIn]
    exact mul_lt_mul_of_pos_right (Work.NN.Ratio.thre_lt_thrT hη0)
      (Work.NN.Ratio.scale_pos hη0 hηhalf hρ l)
  have hpz : Work.NN.Ratio.polCut η ρ z = 1 :=
    Work.NN.Ratio.polCut_eq_one_of_norm_le_cutIn hη0 hηhalf hρ hzcut
  have hPhiPsi : Work.NN.Ratio.Phi (Work.NN.Ratio.scale η ρ)
      (Work.NN.Ratio.Psi (Work.NN.Ratio.scale η ρ) z) = z :=
    Work.NN.Ratio.Phi_Psi (fun l => Work.NN.Ratio.scale_ne_zero hη0 hηhalf hρ l) z
  have hdata : Work.NN.Ratio.dataOf η ρ f j (Work.NN.Ratio.Psi (Work.NN.Ratio.scale η ρ) z)
      = (Work.NN.Ratio.scale η ρ j : ℂ) * f j z := by
    rw [Work.NN.Ratio.dataOf_apply, hPhiPsi, hpz, one_mul]
  rw [hdata, ← mul_assoc, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (Work.NN.Ratio.scale_ne_zero hη0 hηhalf hρ j), Complex.ofReal_one, one_mul]

/-- The rescaled datum is of class `C^m` on the tracking polydisc for data of class `C^m` on
`polydisc 0 ρ`. -/
lemma dataOf_contDiffOn {n : ℕ} {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) {m : ℕ} {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiffOn ℝ m (f j) (polydisc 0 ρ)) :
    ∀ j, ContDiffOn ℝ m (Work.NN.Ratio.dataOf η ρ f j)
      (polydisc 0 (fun _ => Work.NN.Ratio.thrT η)) :=
  fun j => Work.NN.Ratio.contDiffOn_dataOf h0 h1 hρ hf j

/-- The map `Ψ (scale η ρ)` sends the polydisc of multiradius `ρ''` into the equation polydisc
`polydisc 0 (fun _ => thre η)` of the construction, when `ρ'' < thre η * scale η ρ`. -/
lemma psi_mem_thre {n : ℕ} {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ ρ'' : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hgeo : ∀ j, ρ'' j < Work.NN.Ratio.thre η * Work.NN.Ratio.scale η ρ j) :
    MapsTo (Work.NN.Ratio.Psi (Work.NN.Ratio.scale η ρ)) (polydisc 0 ρ'')
      (polydisc 0 (fun _ => Work.NN.Ratio.thre η)) := by
  intro z hz l
  simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]
  rw [Work.NN.Ratio.Psi_apply, norm_mul]
  have hS : 0 < Work.NN.Ratio.scale η ρ l := Work.NN.Ratio.scale_pos h0 h1 hρ l
  have hS0 : Work.NN.Ratio.scale η ρ l ≠ 0 := ne_of_gt hS
  have hSl : ‖(((Work.NN.Ratio.scale η ρ l)⁻¹ : ℝ) : ℂ)‖ = (Work.NN.Ratio.scale η ρ l)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hS.le)]
  rw [hSl]
  have hzl : ‖z l‖ < ρ'' l := by simpa using hz l
  calc (Work.NN.Ratio.scale η ρ l)⁻¹ * ‖z l‖
      < (Work.NN.Ratio.scale η ρ l)⁻¹ * ρ'' l :=
        mul_lt_mul_of_pos_left hzl (inv_pos.mpr hS)
    _ < (Work.NN.Ratio.scale η ρ l)⁻¹ * (Work.NN.Ratio.thre η * Work.NN.Ratio.scale η ρ l) :=
        mul_lt_mul_of_pos_left (hgeo l) (inv_pos.mpr hS)
    _ = Work.NN.Ratio.thre η := by
        rw [mul_comm (Work.NN.Ratio.thre η) (Work.NN.Ratio.scale η ρ l),
          inv_mul_cancel_left₀ hS0]

/-- **Smoothness at a finite level**: `T1` preserves the class `C^m` on the polydisc. -/
theorem T1_contDiffOn {n : ℕ} (η : ℝ) (hη0 : 0 < η) (hηhalf : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) {ρ'' : Fin n → ℝ}
    (hgeo : ∀ j, ρ'' j < Work.NN.Ratio.thre η * Work.NN.Ratio.scale η ρ j) {m : ℕ}
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ j, ContDiffOn ℝ m (f j) (polydisc 0 ρ)) :
    ContDiffOn ℝ m (T1Lin η hη0 hηhalf hρ f) (polydisc 0 ρ'') := by
  have hmem : f ∈ contOnPd0 n ρ := fun j => (hf j).continuousOn
  rw [T1Lin_apply η hη0 hηhalf hρ f hmem]
  have hrec : ContDiffOn ℝ m
      (fun z => (Work.NN.Ratio.geomOf (n := n) η hη0 hηhalf).recU (Work.NN.Ratio.dataOf η ρ f) z)
      (polydisc 0 (fun _ => Work.NN.Ratio.thre η)) := by
    have h := Work.NN.Ratio.contDiffOn_recU (G := Work.NN.Ratio.geomOf (n := n) η hη0 hηhalf)
      (m := m) (f := Work.NN.Ratio.dataOf η ρ f) (dataOf_contDiffOn hη0 hηhalf hρ hf)
    simpa only [Work.NN.Ratio.geomOf_e] using h
  have hpsi : ContDiff ℝ m (Work.NN.Ratio.Psi (Work.NN.Ratio.scale η ρ)) :=
    (Work.NN.Ratio.contDiff_Psi (Work.NN.Ratio.scale η ρ)).of_le (Work.NN.Ratio.le_infty m)
  exact hrec.comp hpsi.contDiffOn (psi_mem_thre hη0 hηhalf hρ hgeo)

/-- **Clause (C)**: `T1` maps smooth closed data to smooth data on the smaller polydisc. -/
theorem T1_contDiffOn_infty {n : ℕ} (η : ℝ) (hη0 : 0 < η) (hηhalf : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) {ρ'' : Fin n → ℝ}
    (hgeo : ∀ j, ρ'' j < Work.NN.Ratio.thre η * Work.NN.Ratio.scale η ρ j) :
    ∀ f : Fin n → (Fin n → ℂ) → ℂ,
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (f j) (polydisc 0 ρ)) →
      (∀ j l (z : Fin n → ℂ), z ∈ polydisc 0 ρ →
        dbarCoord j (f l) z = dbarCoord l (f j) z) →
      ContDiffOn ℝ (⊤ : ℕ∞) (T1Lin η hη0 hηhalf hρ f) (polydisc 0 ρ'') := by
  intro f hf _
  rw [contDiffOn_infty]
  intro m
  exact T1_contDiffOn η hη0 hηhalf hρ hgeo
    (fun j => (contDiffOn_infty.mp (hf j)) m)

/-! ## The dilation `Ψ S` as a continuous linear map -/

/-- The dilation `Ψ S` (a diagonal scaling by the real numbers `(S l)⁻¹`) as a continuous
`ℝ`-linear map. -/
noncomputable def PsiCLM {n : ℕ} (S : Fin n → ℝ) : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi (fun l : Fin n =>
    (ContinuousLinearMap.lsmul ℝ ℂ (((S l)⁻¹ : ℝ) : ℂ)).comp (ContinuousLinearMap.proj l))

lemma PsiCLM_apply {n : ℕ} (S : Fin n → ℝ) (z : Fin n → ℂ) :
    PsiCLM S z = Work.NN.Ratio.Psi S z := by
  funext l
  simp only [PsiCLM, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.lsmul_apply, Pi.smul_apply,
    Work.NN.Ratio.Psi_apply, smul_eq_mul]

/-! ## The a priori `C^{k,α}` estimate for the operator -/

/-- **The a priori estimate**: the `C^{k,α}`-norm of `T1 f` on any polydisc strictly inside the
equation region is controlled by the `C^{k,α}`-norm of `f` on `polydisc 0 ρ` (no closedness is
needed here: this is an estimate for the explicit telescoping formula). -/
lemma T1_holderNorm_le {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (η : ℝ) (hη0 : 0 < η) (hηhalf : η ≤ 1 / 2) {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {ρ'' : Fin n → ℝ} (hρ'' : ∀ j, 0 < ρ'' j)
    (hgeo : ∀ j, ρ'' j < Work.NN.Ratio.thre η * Work.NN.Ratio.scale η ρ j) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (f : Fin n → (Fin n → ℂ) → ℂ),
        (∀ j, ContDiffOn ℝ k (f j) (polydisc 0 ρ)) →
        holderNorm k α (T1Lin η hη0 hηhalf hρ f) (polydisc 0 ρ'')
          ≤ ENNReal.ofReal (C k) *
              ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := by
  classical
  -- the telescope estimate at the geometry `geomOf η`
  obtain ⟨C₁, hC₁pos, hC₁⟩ :
      ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
        ∀ (k : ℕ) (g : Fin n → (Fin n → ℂ) → ℂ), (∀ j, ContDiff ℝ k (g j)) →
          holderNorm k α (fun z => (Work.NN.Ratio.geomOf η hη0 hηhalf).recU g z)
              (polydisc 0 (fun _ => Work.NN.Ratio.thre η))
            ≤ ENNReal.ofReal (C k) *
                ∑ j, holderNorm k α (g j) (polydisc 0 (fun _ => Work.NN.Ratio.thrb η)) := by
    have h := ratioRecUHolderNormLevel (n := n) hα hα1 (Work.NN.Ratio.geomOf η hη0 hηhalf)
    simpa only [Work.NN.Ratio.geomOf_e, Work.NN.Ratio.geomOf_b] using h
  -- the datum estimate
  obtain ⟨C₂, hC₂pos, hC₂⟩ : ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (f : Fin n → (Fin n → ℂ) → ℂ),
        (∀ j, ContDiffOn ℝ k (f j) (polydisc 0 ρ)) →
        ∑ j, holderNorm k α (Work.NN.Ratio.dataOf η ρ f j)
              (polydisc 0 (fun _ => Work.NN.Ratio.thrb η))
          ≤ ENNReal.ofReal (C k) * ∑ j, holderNorm k α (f j) (polydisc 0 ρ) :=
    dataOfHolderNormLevel (n := n) hα hα1 hη0 hηhalf hρ
  -- the dilation estimate, as a family of constants
  let ex : ∀ k : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ u : (Fin n → ℂ) → ℂ, ContDiffOn ℝ k u (polydisc 0 (fun _ => Work.NN.Ratio.thre η)) →
        holderNorm k α (fun z => u (PsiCLM (Work.NN.Ratio.scale η ρ) z))
            (PsiCLM (Work.NN.Ratio.scale η ρ) ⁻¹'
              (polydisc 0 (fun _ => Work.NN.Ratio.thre η)))
          ≤ ENNReal.ofReal c *
              holderNorm k α u (polydisc 0 (fun _ => Work.NN.Ratio.thre η)) := fun k =>
    Work.NN.Final.holderNorm_comp_linear (n := n) k hα
      (PsiCLM (Work.NN.Ratio.scale η ρ)) (isOpen_polydisc 0 (fun _ => Work.NN.Ratio.thre η))
  refine ⟨fun k => Classical.choose (ex k) * C₁ k * C₂ k + 1, ?_, ?_⟩
  · intro k
    have h1 : 0 < Classical.choose (ex k) := (Classical.choose_spec (ex k)).1
    have h2 : 0 < C₁ k := hC₁pos k
    have h3 : 0 < C₂ k := hC₂pos k
    positivity
  · intro k hk f hf
    have hmem : f ∈ contOnPd0 n ρ := fun j => (hf j).continuousOn
    have hdat_sm : ∀ j, ContDiff ℝ k (Work.NN.Ratio.dataOf η ρ f j) := fun j =>
      contDiff_dataOfHonest (η := η) hη0 hηhalf hρ hf j
    have hU_sm : ContDiffOn ℝ k
        (fun z => (Work.NN.Ratio.geomOf η hη0 hηhalf).recU (Work.NN.Ratio.dataOf η ρ f) z)
        (polydisc 0 (fun _ => Work.NN.Ratio.thre η)) := by
      have h := Work.NN.Ratio.contDiffOn_recU (G := Work.NN.Ratio.geomOf η hη0 hηhalf)
        (m := k) (f := Work.NN.Ratio.dataOf η ρ f) (dataOf_contDiffOn hη0 hηhalf hρ hf)
      simpa only [Work.NN.Ratio.geomOf_e] using h
    -- the dilation
    have hdil := (Classical.choose_spec (ex k)).2
      (fun z => (Work.NN.Ratio.geomOf η hη0 hηhalf).recU (Work.NN.Ratio.dataOf η ρ f) z) hU_sm
    -- the set inclusion `polydisc 0 ρ'' ⊆ Ψ ⁻¹' polydisc 0 (fun _ => thre η)`
    have hsub : polydisc 0 ρ'' ⊆ PsiCLM (Work.NN.Ratio.scale η ρ) ⁻¹'
        (polydisc 0 (fun _ => Work.NN.Ratio.thre η)) := by
      intro z hz
      rw [Set.mem_preimage, PsiCLM_apply]
      exact psi_mem_thre hη0 hηhalf hρ hgeo hz
    have hopen : IsOpen (PsiCLM (Work.NN.Ratio.scale η ρ) ⁻¹'
        (polydisc 0 (fun _ => Work.NN.Ratio.thre η))) :=
      (isOpen_polydisc 0 (fun _ => Work.NN.Ratio.thre η)).preimage
        (PsiCLM (Work.NN.Ratio.scale η ρ)).continuous
    have hmono := holderNorm_mono_set hopen (isOpen_polydisc 0 ρ'') hsub k α
      (fun z => (Work.NN.Ratio.geomOf η hη0 hηhalf).recU (Work.NN.Ratio.dataOf η ρ f)
        (PsiCLM (Work.NN.Ratio.scale η ρ) z))
    -- the telescope bound
    have hrec := hC₁ k (Work.NN.Ratio.dataOf η ρ f) hdat_sm
    -- the datum bound
    have hdat := hC₂ k hk f hf
    rw [T1Lin_apply η hη0 hηhalf hρ f hmem]
    calc holderNorm k α (fun z => (Work.NN.Ratio.geomOf η hη0 hηhalf).recU
            (Work.NN.Ratio.dataOf η ρ f) (Work.NN.Ratio.Psi (Work.NN.Ratio.scale η ρ) z))
          (polydisc 0 ρ'')
        = holderNorm k α (fun z => (Work.NN.Ratio.geomOf η hη0 hηhalf).recU
            (Work.NN.Ratio.dataOf η ρ f) (PsiCLM (Work.NN.Ratio.scale η ρ) z))
          (polydisc 0 ρ'') := by
          refine holderNorm_congr_gen fun z _ => ?_
          rw [PsiCLM_apply]
      _ ≤ holderNorm k α (fun z => (Work.NN.Ratio.geomOf η hη0 hηhalf).recU
            (Work.NN.Ratio.dataOf η ρ f) (PsiCLM (Work.NN.Ratio.scale η ρ) z))
          (PsiCLM (Work.NN.Ratio.scale η ρ) ⁻¹'
            (polydisc 0 (fun _ => Work.NN.Ratio.thre η))) := hmono
      _ ≤ ENNReal.ofReal (Classical.choose (ex k)) *
            holderNorm k α (fun z => (Work.NN.Ratio.geomOf η hη0 hηhalf).recU
              (Work.NN.Ratio.dataOf η ρ f) z)
              (polydisc 0 (fun _ => Work.NN.Ratio.thre η)) := hdil
      _ ≤ ENNReal.ofReal (Classical.choose (ex k)) *
            (ENNReal.ofReal (C₁ k) *
              ∑ j, holderNorm k α (Work.NN.Ratio.dataOf η ρ f j)
                (polydisc 0 (fun _ => Work.NN.Ratio.thrb η))) :=
          mul_le_mul' le_rfl hrec
      _ ≤ ENNReal.ofReal (Classical.choose (ex k)) *
            (ENNReal.ofReal (C₁ k) * (ENNReal.ofReal (C₂ k) *
              ∑ j, holderNorm k α (f j) (polydisc 0 ρ))) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl hdat)
      _ = ENNReal.ofReal (Classical.choose (ex k) * C₁ k * C₂ k) *
            ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := by
          have hbc : ENNReal.ofReal (C₁ k) *
                (ENNReal.ofReal (C₂ k) * ∑ j, holderNorm k α (f j) (polydisc 0 ρ))
              = ENNReal.ofReal (C₁ k * C₂ k) *
                  ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (hC₁pos k))]
          rw [hbc, ← mul_assoc,
            ← ENNReal.ofReal_mul (le_of_lt (Classical.choose_spec (ex k)).1), mul_assoc]
      _ ≤ ENNReal.ofReal (Classical.choose (ex k) * C₁ k * C₂ k + 1) *
            ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          have h1 : 0 < Classical.choose (ex k) := (Classical.choose_spec (ex k)).1
          have h2 : 0 < C₁ k := hC₁pos k
          have h3 : 0 < C₂ k := hC₂pos k
          have h4 : 0 ≤ Classical.choose (ex k) * C₁ k * C₂ k := by positivity
          linarith


/-- The target statement (statement unchanged). -/
theorem dbarHonestOneCk {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j) (hlt : ∀ j, ρ' j < ρ j) :
    ∃ (T1 : (Fin n → (Fin n → ℂ) → ℂ) →ₗ[ℝ] ((Fin n → ℂ) → ℂ)) (C : ℕ → ℝ),
      (∀ k, 0 < C k) ∧
      (∀ f, (∀ j, ContDiffOn ℝ 1 (f j) (Work.CR.Flat.polydisc 0 ρ)) →
        (∀ j l z, z ∈ Work.CR.Flat.polydisc 0 ρ →
          Work.CR.Flat.dbarCoord j (f l) z = Work.CR.Flat.dbarCoord l (f j) z) →
        ∀ j (z : Fin n → ℂ), z ∈ Work.CR.Flat.polydisc 0 ρ' →
          Work.CR.Flat.dbarCoord j (T1 f) z = f j z) ∧
      (∀ (k : ℕ) (hk : 1 ≤ k) (f : Fin n → (Fin n → ℂ) → ℂ),
        (∀ j, ContDiffOn ℝ k (f j) (Work.CR.Flat.polydisc 0 ρ)) →
        (∀ j l z, z ∈ Work.CR.Flat.polydisc 0 ρ →
          Work.CR.Flat.dbarCoord j (f l) z = Work.CR.Flat.dbarCoord l (f j) z) →
        (∑ j, Work.CR.Flat.holderNorm k α (f j) (Work.CR.Flat.polydisc 0 ρ)) ≠ ⊤ →
        Work.CR.Flat.holderNorm (k + 1) α (T1 f) (Work.CR.Flat.polydisc 0 ρ')
          ≤ ENNReal.ofReal (C k) *
              ∑ j, Work.CR.Flat.holderNorm k α (f j) (Work.CR.Flat.polydisc 0 ρ)) ∧
      (∀ f, (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (f j) (Work.CR.Flat.polydisc 0 ρ)) →
        (∀ j l z, z ∈ Work.CR.Flat.polydisc 0 ρ →
          Work.CR.Flat.dbarCoord j (f l) z = Work.CR.Flat.dbarCoord l (f j) z) →
        ContDiffOn ℝ (⊤ : ℕ∞) (T1 f) (Work.CR.Flat.polydisc 0 ρ')) := by
  classical
  -- the small parameter `η` of the construction, so that `ρ' < thre η * scale η ρ`
  obtain ⟨η, hη0, hηhalf, hηrho⟩ := Work.NN.Ratio.exists_eta hn hρ hlt
  have hρ'geo : ∀ j, ρ' j < Work.NN.Ratio.thre η * Work.NN.Ratio.scale η ρ j :=
    fun j => Work.NN.Ratio.rho''_lt_thre_mul_scale hη0 hηhalf hρ hηrho j
  have hthre_ρ : ∀ j, Work.NN.Ratio.thre η * Work.NN.Ratio.scale η ρ j < ρ j := fun j =>
    lt_of_lt_of_le (mul_lt_mul_of_pos_right (Work.NN.Ratio.thre_lt_thrT hη0)
      (Work.NN.Ratio.scale_pos hη0 hηhalf hρ j)) (le_of_lt (Work.NN.Ratio.thrT_mul_scale_lt hη0 hηhalf hρ j))
  -- the intermediate polydisc, strictly between `ρ'` and the equation region
  set ρm : Fin n → ℝ := fun j =>
    ρ' j + (Work.NN.Ratio.thre η * Work.NN.Ratio.scale η ρ j - ρ' j) / 2 with hρm
  have hρ'm : ∀ j, ρ' j < ρm j := fun j => by
    rw [hρm]; have := hρ'geo j; simp only; linarith
  have hmgeo : ∀ j, ρm j < Work.NN.Ratio.thre η * Work.NN.Ratio.scale η ρ j := fun j => by
    rw [hρm]; have := hρ'geo j; simp only; linarith
  have hmρ : ∀ j, ρm j < ρ j := fun j => lt_trans (hmgeo j) (hthre_ρ j)
  have hmpos : ∀ j, 0 < ρm j := fun j => lt_trans (hρ' j) (hρ'm j)
  -- the a priori estimate on the intermediate polydisc
  obtain ⟨C0, hC0pos, hC0⟩ := T1_holderNorm_le (n := n) (α := α) hα hα1 η hη0 hηhalf hρ
    (ρ'' := ρm) hmpos hmgeo
  -- the level-`k` estimate
  have hclaim : ∀ (k : ℕ), 1 ≤ k → ∃ c : ℝ, 0 < c ∧
      ∀ (f : Fin n → (Fin n → ℂ) → ℂ),
        (∀ j, ContDiffOn ℝ k (f j) (polydisc 0 ρ)) →
        (∀ j l z, z ∈ polydisc 0 ρ → dbarCoord j (f l) z = dbarCoord l (f j) z) →
        (∑ j, holderNorm k α (f j) (polydisc 0 ρ)) ≠ ⊤ →
        holderNorm (k + 1) α (T1Lin η hη0 hηhalf hρ f) (polydisc 0 ρ')
          ≤ ENNReal.ofReal c * ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := by
    intro k hk
    obtain ⟨C1, hC1pos, hC1⟩ := dbarOneshotCk (n := n) hn (c := 0) (ρi := ρ') (ρo := ρm)
      hρ'm hmpos hα hα1 k hk
    refine ⟨C1 * (1 + C0 k) + 1, ?_, ?_⟩
    · have hk1 : 0 < C1 * (1 + C0 k) := by
        have : 0 < 1 + C0 k := by linarith [hC0pos k]
        positivity
      linarith
    intro f hf hfcl hS
    have hf1 : ∀ j, ContDiffOn ℝ 1 (f j) (polydisc 0 ρ) := fun j =>
      (hf j).of_le (by exact_mod_cast hk)
    have hf_mono : ∀ j, ContDiffOn ℝ k (f j) (polydisc 0 ρm) := fun j =>
      (hf j).mono (polydisc_mono (fun l => le_of_lt (hmρ l)))
    have hfcl_mono : ∀ j l z, z ∈ polydisc 0 ρm →
        dbarCoord l (f j) z = dbarCoord j (f l) z := fun j l z hz =>
      (hfcl j l z (fun m => lt_trans (hz m) (hmρ m))).symm
    have hu_sm : ContDiffOn ℝ k (T1Lin η hη0 hηhalf hρ f) (polydisc 0 ρm) :=
      T1_contDiffOn η hη0 hηhalf hρ hmgeo hf
    have hu_eq : ∀ j (z : Fin n → ℂ), z ∈ polydisc 0 ρm →
        dbarCoord j (T1Lin η hη0 hηhalf hρ f) z = f j z :=
      T1_solves η hη0 hηhalf hρ hmgeo f hf1 hfcl
    have h1 := hC1 (T1Lin η hη0 hηhalf hρ f) f hu_sm hf_mono hfcl_mono hu_eq
    have h2 := hC0 k hk f hf
    have hsum_mono : (∑ j, holderNorm k α (f j) (polydisc 0 ρm))
        ≤ ∑ j, holderNorm k α (f j) (polydisc 0 ρ) :=
      Finset.sum_le_sum fun j _ =>
        holderNorm_mono_set (isOpen_polydisc 0 ρ) (isOpen_polydisc 0 ρm)
          (fun z hz l => lt_trans (hz l) (hmρ l)) k α (f j)
    calc holderNorm (k + 1) α (T1Lin η hη0 hηhalf hρ f) (polydisc 0 ρ')
        ≤ ENNReal.ofReal C1 * ((∑ j, holderNorm k α (f j) (polydisc 0 ρm))
            + holderNorm k α (T1Lin η hη0 hηhalf hρ f) (polydisc 0 ρm)) := h1
      _ ≤ ENNReal.ofReal C1 * ((∑ j, holderNorm k α (f j) (polydisc 0 ρ))
            + ENNReal.ofReal (C0 k) * ∑ j, holderNorm k α (f j) (polydisc 0 ρ)) :=
          mul_le_mul' le_rfl (add_le_add hsum_mono h2)
      _ = ENNReal.ofReal (C1 * (1 + C0 k)) *
            ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := by
          have h1S : (∑ j, holderNorm k α (f j) (polydisc 0 ρ))
                + ENNReal.ofReal (C0 k) * (∑ j, holderNorm k α (f j) (polydisc 0 ρ))
              = ENNReal.ofReal (1 + C0 k) * (∑ j, holderNorm k α (f j) (polydisc 0 ρ)) := by
            calc (∑ j, holderNorm k α (f j) (polydisc 0 ρ))
                  + ENNReal.ofReal (C0 k) * (∑ j, holderNorm k α (f j) (polydisc 0 ρ))
                = 1 * (∑ j, holderNorm k α (f j) (polydisc 0 ρ))
                  + ENNReal.ofReal (C0 k) * (∑ j, holderNorm k α (f j) (polydisc 0 ρ)) := by
                  rw [one_mul]
              _ = (1 + ENNReal.ofReal (C0 k)) * (∑ j, holderNorm k α (f j) (polydisc 0 ρ)) :=
                  (add_mul _ _ _).symm
              _ = ENNReal.ofReal (1 + C0 k) * (∑ j, holderNorm k α (f j) (polydisc 0 ρ)) := by
                  rw [← ENNReal.ofReal_one,
                    ← ENNReal.ofReal_add (by norm_num) (le_of_lt (hC0pos k))]
          rw [h1S, ← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hC1pos)]
      _ ≤ ENNReal.ofReal (C1 * (1 + C0 k) + 1) *
            ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          have h4 : 0 ≤ C1 * (1 + C0 k) := by
            have : 0 < 1 + C0 k := by linarith [hC0pos k]
            positivity
          linarith
  refine ⟨T1Lin η hη0 hηhalf hρ,
    fun k => if h : 1 ≤ k then Classical.choose (hclaim k h) else 1, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : 1 ≤ k
    · simpa only [dif_pos hk] using (Classical.choose_spec (hclaim k hk)).1
    · simpa only [dif_neg hk] using (show (0 : ℝ) < 1 by norm_num)
  · intro f hf hfcl j z hz
    exact T1_solves η hη0 hηhalf hρ hρ'geo f hf hfcl j z hz
  · intro k hk f hf hfcl hS
    have h := (Classical.choose_spec (hclaim k hk)).2 f hf hfcl hS
    simpa only [dif_pos hk] using h
  · intro f hf hfcl
    exact T1_contDiffOn_infty η hη0 hηhalf hρ hρ'geo f hf hfcl

end Work.NN.Core
