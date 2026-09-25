import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Ratio.Scale
import Submission.Work.NN.Ratio.PullBack
import Submission.Work.NN.Ratio.recU_linear
import Submission.Work.NN.Ratio.recU_solves_local
import Submission.Work.NN.Ratio.recU_estimate_nc
import Submission.Work.NN.Ratio.contDiff_recU
import Submission.Work.NN.Ratio.contDiffOn_recU
import Submission.Work.NN.Ratio.holderNorm_zero_le_of_bounds
import Submission.Work.NN.Core.HonestAux
import Submission.Work.CR.Flat.Holder.holderNorm_zero_comp_le
import Submission.Work.CR.Flat.Holder.holderNorm_smul

namespace Work.NN.Core

open scoped NNReal ENNReal ContDiff
open Set
open Work.CR.Flat
open Work.NN.Ratio

/-- The honest solution formula `f ↦ G.recU (pull S f) ∘ Ψ`, extended linearly from the
subspace of globally `C¹` data to all data. -/
private lemma exists_solver_lin {n : ℕ} (G : Geom n) (S : Fin n → ℝ) :
    ∃ T : (Fin n → (Fin n → ℂ) → ℂ) →ₗ[ℝ] ((Fin n → ℂ) → ℂ),
      ∀ (f : Fin n → (Fin n → ℂ) → ℂ), (∀ j, ContDiff ℝ 1 (f j)) →
        T f = fun z => G.recU (pull S f) (Psi S z) := by
  classical
  let V : Submodule ℝ (Fin n → (Fin n → ℂ) → ℂ) :=
    { carrier := {f | ∀ j, ContDiff ℝ 1 (f j)}
      zero_mem' := by intro j; exact contDiff_zero_fun
      add_mem' := by intro x y hx hy j; exact (hx j).add (hy j)
      smul_mem' := by intro c x hx j; exact (hx j).const_smul c }
  let q : Submodule ℝ (Fin n → (Fin n → ℂ) → ℂ) := (Submodule.exists_isCompl V).choose
  have hq : IsCompl V q := (Submodule.exists_isCompl V).choose_spec
  have hpullmem : ∀ a : V, ∀ j, ContDiff ℝ 1 ((pull S a.val) j) :=
    fun a j => contDiff_pull (S := S) (k := 1) (fun i => a.property i) j
  have hrecU_zero : ∀ (A : Fin n → (Fin n → ℂ) → ℂ), (∀ j, ContDiff ℝ 1 (A j)) →
      ∀ z, G.recU (0 : Fin n → (Fin n → ℂ) → ℂ) z = 0 := by
    intro A hA z
    have h := recU_linear G (-1) A A hA hA z
    have hd : (fun j y => (-1 : ℝ) • A j y + A j y) = (0 : Fin n → (Fin n → ℂ) → ℂ) := by
      funext j y; simp
    rw [hd] at h
    simpa using h
  let Lhom : V →ₗ[ℝ] ((Fin n → ℂ) → ℂ) :=
    { toFun := fun a z => G.recU (pull S a.val) (Psi S z)
      map_add' := by
        intro a b
        funext z
        have hA := hpullmem a
        have hB := hpullmem b
        have h := recU_linear G 1 (pull S a.val) (pull S b.val) hA hB (Psi S z)
        rw [one_smul] at h
        have hAB : pull S (a + b).val = pull S a.val + pull S b.val := by
          rw [show (a + b).val = a.val + b.val from rfl, pull_add]
        rw [hAB]
        have hd : (fun j y => (1 : ℝ) • (pull S a.val) j y + (pull S b.val) j y)
            = pull S a.val + pull S b.val := by
          funext j y; simp only [one_smul, Pi.add_apply]
        rw [← hd]
        simpa only [one_smul, Pi.add_apply] using h
      map_smul' := by
        intro c a
        funext z
        have hA := hpullmem a
        have h0 : ∀ j, ContDiff ℝ 1 ((0 : Fin n → (Fin n → ℂ) → ℂ) j) :=
          fun j => contDiff_zero_fun
        have h := recU_linear G c (pull S a.val) (0 : Fin n → (Fin n → ℂ) → ℂ) hA h0 (Psi S z)
        have hz0 : G.recU (0 : Fin n → (Fin n → ℂ) → ℂ) (Psi S z) = 0 :=
          hrecU_zero (pull S a.val) hA (Psi S z)
        have hd : (fun j y => c • (pull S a.val) j y
            + (0 : Fin n → (Fin n → ℂ) → ℂ) j y) = c • (pull S a.val) := by
          funext j y; simp
        rw [hd, hz0, add_zero] at h
        rw [show (c • a).val = c • a.val from rfl, pull_smul]
        exact h }
  let Lext : (Fin n → (Fin n → ℂ) → ℂ) →ₗ[ℝ] ((Fin n → ℂ) → ℂ) :=
    Lhom.comp (Submodule.projectionOnto V q hq)
  refine ⟨Lext, fun f hf => ?_⟩
  have h1 : (Submodule.projectionOnto V q hq) f = ⟨f, hf⟩ :=
    Submodule.projectionOnto_apply_left hq ⟨f, hf⟩
  show Lext f = _
  rw [show Lext f = Lhom ((Submodule.projectionOnto V q hq) f) from rfl, h1]
  rfl

private noncomputable def mkSolver {n : ℕ} (G : Geom n) (S : Fin n → ℝ) :
    (Fin n → (Fin n → ℂ) → ℂ) →ₗ[ℝ] ((Fin n → ℂ) → ℂ) :=
  (exists_solver_lin G S).choose

private lemma mkSolver_apply {n : ℕ} (G : Geom n) (S : Fin n → ℝ)
    (f : Fin n → (Fin n → ℂ) → ℂ) (hf : ∀ j, ContDiff ℝ 1 (f j)) :
    mkSolver G S f = fun z => G.recU (pull S f) (Psi S z) :=
  (exists_solver_lin G S).choose_spec f hf

theorem dbarSolverHonest {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {ρ ρ'' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ'' : ∀ j, 0 < ρ'' j) (hlt : ∀ j, ρ'' j < ρ j) :
    ∃ (T : (Fin n → Cn n → ℂ) →ₗ[ℝ] (Cn n → ℂ)) (C : ℝ),
      0 < C ∧
      (∀ f, (∀ j, ContDiffOn ℝ 1 (f j) (polydisc 0 ρ)) →
        (∀ j l z, z ∈ polydisc 0 ρ → dbarCoord j (f l) z = dbarCoord l (f j) z) →
        ∀ j (z : Cn n), z ∈ polydisc 0 ρ'' → dbarCoord j (T f) z = f j z) ∧
      (∀ f, (∀ j, ContDiffOn ℝ 1 (f j) (polydisc 0 ρ)) →
        holderNorm 0 α (T f) (polydisc 0 ρ'')
          ≤ ENNReal.ofReal C * ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ)) ∧
      (∀ (k : ℕ) (f : Fin n → Cn n → ℂ), (∀ j, ContDiffOn ℝ (k + 1) (f j) (polydisc 0 ρ)) →
        ContDiffOn ℝ (k + 1) (T f) (polydisc 0 ρ'')) ∧
      (∀ f, (∀ j, ContDiffOn ℝ ∞ (f j) (polydisc 0 ρ)) →
        ContDiffOn ℝ ∞ (T f) (polydisc 0 ρ'')) := by
  classical
  obtain ⟨η, hη0, hηhalf, hηrho⟩ := Work.NN.Ratio.exists_eta hn hρ hlt
  let S : Fin n → ℝ := scale η ρ
  have hSpos : ∀ l, 0 < S l := fun l => scale_pos hη0 hηhalf hρ l
  have hSnn : ∀ l, 0 ≤ S l := fun l => le_of_lt (hSpos l)
  let G : Geom n := geomOf η hη0 hηhalf
  have hGb : G.b = thrb η := rfl
  have hGe : G.e = thre η := rfl
  have hGT : G.T = thrT η := rfl
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.NN.Ratio.recU_estimate_nc (n := n) hα hα1 G
  set KS : ℝ := ∑ l, S l with hKS
  set K1 : ℝ := ∑ l, (S l)⁻¹ with hK1
  set Mα : ℝ := max 1 (KS ^ α) with hMα
  set Bc : ℝ := ∑ j, S j * Mα with hBc
  set Cst : ℝ := max 1 (K1 ^ α) * (2 * C₁ * Bc) + 1 with hCst
  have hKSnn : 0 ≤ KS := by rw [hKS]; exact Finset.sum_nonneg fun l _ => hSnn l
  have hK1nn : 0 ≤ K1 := by rw [hK1]; exact Finset.sum_nonneg fun l _ => inv_nonneg.mpr (hSnn l)
  have hMαnn : 0 ≤ Mα := le_trans zero_le_one (le_max_left _ _)
  have hBcnn : 0 ≤ Bc := by rw [hBc]; exact Finset.sum_nonneg fun j _ => mul_nonneg (hSnn j) hMαnn
  have hCpos : 0 < Cst := by
    rw [hCst]
    have h1 : 0 ≤ max 1 (K1 ^ α) := le_trans zero_le_one (le_max_left _ _)
    have h2 : 0 ≤ 2 * C₁ * Bc := by
      have := le_of_lt hC₁pos; positivity
    have h3 : 0 ≤ max 1 (K1 ^ α) * (2 * C₁ * Bc) := mul_nonneg h1 h2
    linarith
  let T : (Fin n → (Fin n → ℂ) → ℂ) →ₗ[ℝ] ((Fin n → ℂ) → ℂ) :=
    (mkSolver G S).comp (cutMul (polCut η ρ))
  have T_apply : ∀ (f : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, ContDiff ℝ 1 ((cutMul (polCut η ρ)) f j)) →
      T f = fun z => G.recU (dataOf η ρ f) (Psi S z) := by
    intro f hf
    show mkSolver G S ((cutMul (polCut η ρ)) f) = _
    rw [mkSolver_apply G S ((cutMul (polCut η ρ)) f) hf]
    rfl
  have hmemGlobal : ∀ (f : Fin n → (Fin n → ℂ) → ℂ), (∀ j, ContDiff ℝ 1 (f j)) →
      ∀ j, ContDiff ℝ 1 ((cutMul (polCut η ρ)) f j) := by
    intro f hf j
    exact ((contDiff_polCut ρ).of_le (le_infty 1)).mul (hf j)
  have hmemLocal : ∀ (f : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, ContDiffOn ℝ ∞ (f j) (polydisc 0 ρ)) →
      ∀ j, ContDiff ℝ 1 ((cutMul (polCut η ρ)) f j) := by
    intro f hf j
    show ContDiff ℝ 1 (fun y => polydiscCut (cutIn η ρ) (cutOut η ρ) y * f j y)
    refine Work.NN.Ratio.contDiff_polydiscCut_mul (fun j => cutIn_nonneg hη0 hηhalf hρ j)
      (fun j => cutIn_lt_cutOut hη0 hηhalf hρ j) (isOpen_polydisc 0 ρ) ?_ ((hf j).of_le (le_infty 1))
    intro z hz l
    show ‖z l - 0‖ < ρ l
    rw [sub_zero]
    exact lt_of_le_of_lt (hz l) (cutOut_lt_rho hη0 hηhalf hρ l)
  have hmemLocal' : ∀ (m : ℕ) (f : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, ContDiffOn ℝ (↑m) (f j) (polydisc 0 ρ)) →
      ∀ j, ContDiff ℝ (↑m) ((cutMul (polCut η ρ)) f j) :=
    fun m f hf j => contDiff_cutMul_polCut hη0 hηhalf hρ hf j
  have hEqStrong : ∀ (f : Fin n → (Fin n → ℂ) → ℂ), (∀ j, ContDiffOn ℝ 1 (f j) (polydisc 0 ρ)) →
      (∀ j l z, z ∈ polydisc 0 ρ → dbarCoord j (f l) z = dbarCoord l (f j) z) →
      ∀ (j : Fin n) (z : Fin n → ℂ),
        (∀ l, ‖z l‖ < thre η * S l) → dbarCoord j (T f) z = f j z := by
    intro f hf hfcl j z hz
    have hdat_closed : ∀ i l (y : Fin n → ℂ), (∀ m, ‖y m‖ < G.T) →
        dbarCoord l (dataOf η ρ f i) y = dbarCoord i (dataOf η ρ f l) y := by
      intro i l y hy
      refine dataOf_closedOn hη0 hηhalf hρ hf hfcl i l y ?_
      exact mem_polydisc_const.mpr (fun m => by simpa only [hGT] using hy m)
    have hdat_c1 : ∀ i, ContDiff ℝ 1 (dataOf η ρ f i) :=
      fun i => contDiff_dataOfHonest hη0 hηhalf hρ hf i
    have hR : G.b < G.T := by rw [hGb, hGT]; exact thrb_lt_thrT hη0
    have hpsi : (∀ l, ‖Psi S z l‖ < G.e) := by
      intro l
      rw [hGe]
      exact Work.NN.Ratio.psi_mem_solve hη0 hηhalf hρ hz l
    have hsolve : dbarCoord j (fun z => G.recU (dataOf η ρ f) z) (Psi S z)
        = dataOf η ρ f j (Psi S z) :=
      Work.NN.Ratio.recU_solves_local G hR hdat_c1 hdat_closed j (Psi S z) hpsi
    have hU : DifferentiableAt ℝ (fun z => G.recU (dataOf η ρ f) z) (Psi S z) :=
      ((Work.NN.Ratio.contDiff_recU G hdat_c1).contDiffAt).differentiableAt (by simp)
    have hcut1 : polCut η ρ z = 1 := by
      refine polCut_eq_one_of_norm_le_cutIn hη0 hηhalf hρ (fun l => ?_)
      have h1 : ρ'' l < thre η * S l := Work.NN.Ratio.rho''_lt_thre_mul_scale hη0 hηhalf hρ hηrho l
      have h2 : thre η * S l < cutIn η ρ l :=
        mul_lt_mul_of_pos_right (thre_lt_thrT hη0) (hSpos l)
      linarith [hz l]
    have hPhi : Phi S (Psi S z) = z := Phi_Psi (fun l => ne_of_gt (hSpos l)) z
    rw [T_apply f (hmemLocal' 1 f hf), Work.NN.Ratio.dbarCoord_Psi S j hU, hsolve,
      dataOf_apply, hPhi, hcut1, one_mul]
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt (hSpos j)),
      Complex.ofReal_one, one_mul]
  refine ⟨T, Cst, hCpos, ?_, ?_, ?_, ?_⟩
  · intro f hf hfcl j z hz
    refine hEqStrong f hf hfcl j z (fun l => ?_)
    have h1 := hz l
    rw [Pi.zero_apply, sub_zero] at h1
    exact lt_trans h1 (Work.NN.Ratio.rho''_lt_thre_mul_scale hη0 hηhalf hρ hηrho l)
  · intro f hf
    by_cases htop : (∑ j, holderNorm 0 α (f j) (polydisc 0 ρ)) = ⊤
    · rw [htop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hCpos)]
      exact le_top
    · have hHj : ∀ j, holderNorm 0 α (f j) (polydisc 0 ρ) ≠ ⊤ := fun j =>
        ne_top_of_le_ne_top htop (Finset.single_le_sum
          (f := fun i => holderNorm 0 α (f i) (polydisc 0 ρ)) (fun i _ => bot_le) (Finset.mem_univ j))
      have hfOn : ∀ j, ContDiffOn ℝ 1 (f j) (polydisc 0 ρ) := hf
      have hdat_c1 : ∀ i, ContDiff ℝ 1 (dataOf η ρ f i) :=
        fun i => contDiff_dataOfHonest hη0 hηhalf hρ hf i
      have hTf := T_apply f (hmemLocal' 1 f hf)
      have hbound : ∀ j, holderNorm 0 α (dataOf η ρ f j) (polydisc 0 (fun _ => thrT η))
          ≤ ENNReal.ofReal (S j * Mα * (holderNorm 0 α (f j) (polydisc 0 ρ)).toReal) := by
        intro j
        have hle := Work.NN.Ratio.holderNorm_dataOf_le hα hη0 hηhalf hρ hfOn j
        have e1 : holderNorm 0 α (f j) (polydisc 0 ρ)
            = ENNReal.ofReal (holderNorm 0 α (f j) (polydisc 0 ρ)).toReal :=
          (ENNReal.ofReal_toReal (hHj j)).symm
        have e2 : (∑ l, scale η ρ l) ^ α = KS ^ α := by
          show (∑ l, S l) ^ α = KS ^ α
          rw [← hKS]
        have e3 : max 1 (ENNReal.ofReal (KS ^ α)) = ENNReal.ofReal Mα := by
          rw [hMα, ENNReal.ofReal_max, ENNReal.ofReal_one]
        have hone : ENNReal.ofReal (scale η ρ j)
              * (max 1 (ENNReal.ofReal ((∑ l, scale η ρ l) ^ α))
                * holderNorm 0 α (f j) (polydisc 0 ρ))
            ≤ ENNReal.ofReal (S j * Mα * (holderNorm 0 α (f j) (polydisc 0 ρ)).toReal) := by
          rw [e2, e3]
          nth_rewrite 1 [e1]
          rw [← ENNReal.ofReal_mul hMαnn, ← ENNReal.ofReal_mul (hSnn j)]
          exact ENNReal.ofReal_le_ofReal (le_of_eq (mul_assoc (scale η ρ j) Mα
            (holderNorm 0 α (f j) (polydisc 0 ρ)).toReal).symm)
        exact hle.trans hone
      have hstep : ∀ j,
          (holderNorm 0 α (dataOf η ρ f j) (polydisc 0 (fun _ => thrT η))).toReal
            ≤ S j * Mα * (holderNorm 0 α (f j) (polydisc 0 ρ)).toReal := by
        intro j
        have hfin : holderNorm 0 α (dataOf η ρ f j) (polydisc 0 (fun _ => thrT η)) ≠ ⊤ :=
          ne_top_of_le_ne_top
            (b := ENNReal.ofReal (S j * Mα * (holderNorm 0 α (f j) (polydisc 0 ρ)).toReal))
            ENNReal.ofReal_ne_top (hbound j)
        have h2 := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr (hbound j)
        rwa [ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg (hSnn j) hMαnn)
          ENNReal.toReal_nonneg)] at h2
      have hS₀nn : 0 ≤ ∑ j, (holderNorm 0 α (dataOf η ρ f j)
          (polydisc 0 (fun _ => thrT η))).toReal :=
        Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg
      have hS₀ne : (∑ j, holderNorm 0 α (dataOf η ρ f j)
          (polydisc 0 (fun _ => thrT η))) ≠ ⊤ := by
        have hsum : (∑ j, holderNorm 0 α (dataOf η ρ f j) (polydisc 0 (fun _ => thrT η)))
            ≤ ENNReal.ofReal (∑ j, S j * Mα * (holderNorm 0 α (f j) (polydisc 0 ρ)).toReal) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg
            (mul_nonneg (hSnn j) hMαnn) ENNReal.toReal_nonneg)]
          exact Finset.sum_le_sum fun j _ => hbound j
        exact ne_of_lt (lt_of_le_of_lt hsum ENNReal.ofReal_lt_top)
      have hS₀sum : (∑ j, (holderNorm 0 α (dataOf η ρ f j)
            (polydisc 0 (fun _ => thrT η))).toReal)
          ≤ Bc * (∑ j, holderNorm 0 α (f j) (polydisc 0 ρ)).toReal := by
        rw [hBc, ENNReal.toReal_sum fun j _ => hHj j]
        calc ∑ j, (holderNorm 0 α (dataOf η ρ f j) (polydisc 0 (fun _ => thrT η))).toReal
            ≤ ∑ j, S j * Mα * (holderNorm 0 α (f j) (polydisc 0 ρ)).toReal :=
              Finset.sum_le_sum fun j _ => hstep j
          _ ≤ ∑ j, S j * Mα * (∑ i, (holderNorm 0 α (f i) (polydisc 0 ρ)).toReal) :=
              Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
                (Finset.single_le_sum
                  (f := fun i => (holderNorm 0 α (f i) (polydisc 0 ρ)).toReal)
                  (fun i _ => ENNReal.toReal_nonneg) (Finset.mem_univ j))
                (mul_nonneg (hSnn j) hMαnn)
          _ = (∑ j, S j * Mα) * (∑ i, (holderNorm 0 α (f i) (polydisc 0 ρ)).toReal) :=
              (Finset.sum_mul _ _ _).symm
      obtain ⟨hb1, hb2⟩ := hC₁ (dataOf η ρ f) hdat_c1 (by rw [hGT]; exact hS₀ne)
      have hrecEst : holderNorm 0 α (fun z => G.recU (dataOf η ρ f) z)
            (polydisc 0 (fun _ => thre η))
          ≤ ENNReal.ofReal (C₁ * ∑ j, (holderNorm 0 α (dataOf η ρ f j)
              (polydisc 0 (fun _ => thrT η))).toReal)
            + ENNReal.ofReal (C₁ * ∑ j, (holderNorm 0 α (dataOf η ρ f j)
              (polydisc 0 (fun _ => thrT η))).toReal) := by
        refine Work.NN.Ratio.holderNorm_zero_le_of_bounds
          (mul_nonneg (le_of_lt hC₁pos) hS₀nn) (mul_nonneg (le_of_lt hC₁pos) hS₀nn)
          (fun z hz => ?_) (fun x hx y hy => ?_)
        · refine hb1 z (fun l => ?_)
          have h1 := hz l
          simp only [Pi.zero_apply, sub_zero] at h1
          simpa only [hGe] using h1
        · refine hb2 x y (fun l => ?_) (fun l => ?_)
          · have h1 := hx l
            simp only [Pi.zero_apply, sub_zero] at h1
            simpa only [hGe] using h1
          · have h1 := hy l
            simp only [Pi.zero_apply, sub_zero] at h1
            simpa only [hGe] using h1
      have hcompT : holderNorm 0 α (T f) (polydisc 0 (fun j => thre η * S j))
          ≤ max 1 (ENNReal.ofReal (K1 ^ α)) * holderNorm 0 α
              (fun z => G.recU (dataOf η ρ f) z) (polydisc 0 (fun _ => thre η)) := by
        rw [hTf]
        refine Work.CR.Flat.Holder.holderNorm_zero_comp_le (hα := hα) (hM := hK1nn)
          (Ω := polydisc 0 (fun j => thre η * S j)) (Ω' := polydisc 0 (fun _ => thre η))
          (Φ := Psi S) (U := fun z => G.recU (dataOf η ρ f) z) (M := K1) ?_ ?_
        · intro z hz
          exact Work.NN.Ratio.psi_mem_polydisc hη0 hηhalf hρ (by
            intro l
            have h1 := hz l
            simp only [Pi.zero_apply, sub_zero] at h1
            exact h1)
        · intro x _ y _
          show ‖Psi S x - Psi S y‖ ≤ K1 * ‖x - y‖
          rw [hK1]
          exact norm_Psi_sub_le hSnn x y
      have hC₁nn : 0 ≤ C₁ := le_of_lt hC₁pos
      have hinner : ENNReal.ofReal (C₁ * ∑ j, (holderNorm 0 α (dataOf η ρ f j)
              (polydisc 0 (fun _ => thrT η))).toReal)
            + ENNReal.ofReal (C₁ * ∑ j, (holderNorm 0 α (dataOf η ρ f j)
              (polydisc 0 (fun _ => thrT η))).toReal)
          ≤ ENNReal.ofReal (2 * C₁ * Bc) * ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ) := by
        have h1 : ENNReal.ofReal (C₁ * ∑ j, (holderNorm 0 α (dataOf η ρ f j)
                (polydisc 0 (fun _ => thrT η))).toReal)
              + ENNReal.ofReal (C₁ * ∑ j, (holderNorm 0 α (dataOf η ρ f j)
                (polydisc 0 (fun _ => thrT η))).toReal)
            = ENNReal.ofReal (2 * C₁ * (∑ j, (holderNorm 0 α (dataOf η ρ f j)
                (polydisc 0 (fun _ => thrT η))).toReal)) := by
          rw [← ENNReal.ofReal_add (mul_nonneg hC₁nn hS₀nn) (mul_nonneg hC₁nn hS₀nn)]
          congr 1
          ring_nf
        have h2 : ENNReal.ofReal (2 * C₁ * (∑ j, (holderNorm 0 α (dataOf η ρ f j)
                (polydisc 0 (fun _ => thrT η))).toReal))
            ≤ ENNReal.ofReal (2 * C₁ * (Bc * (∑ j, holderNorm 0 α (f j) (polydisc 0 ρ)).toReal)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hS₀sum (by linarith [hC₁pos]))
        have h3 : ENNReal.ofReal (2 * C₁ * Bc) * ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ)
            = ENNReal.ofReal (2 * C₁ * (Bc * (∑ j, holderNorm 0 α (f j) (polydisc 0 ρ)).toReal)) := by
          nth_rewrite 1 [← ENNReal.ofReal_toReal htop]
          rw [← ENNReal.ofReal_mul (mul_nonneg (by positivity) hBcnn)]
          congr 1
          ring_nf
        rw [h1]
        exact h2.trans (le_of_eq h3.symm)
      have hc2 : holderNorm 0 α (T f) (polydisc 0 (fun j => thre η * S j))
          ≤ ENNReal.ofReal (max 1 (K1 ^ α) * (2 * C₁ * Bc))
            * ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ) := by
        have hZ : max 1 (ENNReal.ofReal (K1 ^ α))
              * (ENNReal.ofReal (2 * C₁ * Bc)
                * ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ))
            = ENNReal.ofReal (max 1 (K1 ^ α) * (2 * C₁ * Bc))
              * ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ) := by
          rw [show max 1 (ENNReal.ofReal (K1 ^ α)) = ENNReal.ofReal (max 1 (K1 ^ α)) by
                rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_max],
            ← mul_assoc, ← ENNReal.ofReal_mul (le_trans zero_le_one (le_max_left _ _))]
        exact (hcompT.trans (mul_le_mul' le_rfl (hrecEst.trans hinner))).trans (le_of_eq hZ)
      have hmonoT : holderNorm 0 α (T f) (polydisc 0 ρ'')
          ≤ holderNorm 0 α (T f) (polydisc 0 (fun j => thre η * S j)) :=
        holderNorm_mono_set (isOpen_polydisc 0 (fun j => thre η * S j)) (isOpen_polydisc 0 ρ'')
          (fun z hz l => by
            have h1 := hz l
            simp only [Pi.zero_apply, sub_zero] at h1 ⊢
            exact lt_trans h1 (Work.NN.Ratio.rho''_lt_thre_mul_scale hη0 hηhalf hρ hηrho l))
          0 α (T f)
      calc holderNorm 0 α (T f) (polydisc 0 ρ'')
          ≤ holderNorm 0 α (T f) (polydisc 0 (fun j => thre η * S j)) := hmonoT
        _ ≤ ENNReal.ofReal (max 1 (K1 ^ α) * (2 * C₁ * Bc))
              * ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ) := hc2
        _ ≤ ENNReal.ofReal Cst * ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ) := by
            refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
            rw [hCst]; linarith
  · intro k f hf
    have hmem := hmemLocal' (k + 1) f hf
    have hTf := T_apply f (fun j => (hmem j).of_le
      (by norm_num : (1 : WithTop ℕ∞) ≤ (↑(k + 1) : WithTop ℕ∞)))
    rw [hTf]
    have hdat : ∀ i, ContDiffOn ℝ (↑(k + 1)) (dataOf η ρ f i)
        (polydisc 0 (fun _ => thrT η)) := by
      intro i
      exact Work.NN.Ratio.contDiffOn_dataOf hη0 hηhalf hρ hf i
    have hrecU := Work.NN.Ratio.contDiffOn_recU G hdat
    have hcomp : ContDiffOn ℝ (↑(k + 1)) (fun z => G.recU (dataOf η ρ f) (Psi S z))
        (polydisc 0 ρ'') := by
      refine hrecU.comp (((contDiff_Psi S).of_le (le_infty (k + 1))).contDiffOn) ?_
      intro z hz
      refine Work.NN.Ratio.mem_solveSet_of_rho'' hη0 hηhalf hρ hηrho (fun l => ?_)
      have := hz l
      simpa only [Pi.zero_apply, sub_zero] using this
    exact hcomp
  · intro f hf
    have hmem := hmemLocal' 1 f (fun j => (hf j).of_le (le_infty 1))
    have hTf := T_apply f hmem
    rw [contDiffOn_infty]
    intro m
    have hdat : ∀ i, ContDiffOn ℝ m (dataOf η ρ f i) (polydisc 0 (fun _ => G.T)) := by
      intro i
      have := Work.NN.Ratio.contDiffOn_dataOf hη0 hηhalf hρ (fun j => (hf j).of_le (le_infty m)) i
      simpa only [hGT] using this
    have hrecU := Work.NN.Ratio.contDiffOn_recU G hdat
    rw [hTf]
    refine hrecU.comp (((contDiff_Psi S).of_le (le_infty m)).contDiffOn) ?_
    intro z hz
    refine Work.NN.Ratio.mem_solveSet_of_rho'' hη0 hηhalf hρ hηrho (fun l => ?_)
    have := hz l
    simpa only [Pi.zero_apply, sub_zero] using this

end Work.NN.Core
