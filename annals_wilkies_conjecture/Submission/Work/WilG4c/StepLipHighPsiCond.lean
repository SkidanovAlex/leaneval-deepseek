import Mathlib
import Submission.Work.WilG4a.F1AffineW
import Submission.Work.WilG4c.StepLipHighOuter
import Submission.Work.WilG4c.GoodCellChartsCond
import Submission.Work.WilG4c.StepLipHighGlue
import Submission.Work.WilG4c.StepLipHighPsiAux2
import Submission.Work.WilG4c.StepLipHighAux
import Submission.Work.WilG4c.JointC1LocMem
import Submission.Work.WilG4c.BadCellCharts
import Submission.Work.WilG4c.C1AllComplThin
import Submission.Work.WilG4c.badCurveStrip_interior_emptyW
import Submission.Work.WilG4c.ChartsOK_clamp
import Submission.Work.WilG4c.IteFamGraphMemGen
import Submission.Work.WilG4c.TmEqSetMem
import Submission.Work.WilG4c.StepLipHighPsiCell
import Submission.Work.WilG4c.StepLipHighPsiAux3
import Submission.Work.WilG4c.StepLipHighPsiPack
import Submission.Work.WilG1.Cell.thin_union

set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

-- The per-`ψ` step of the §5.3 assembly (`Work.WilkG4c.PsiHyp`), with the corrected
-- `ψ`-interface: the cover of the single chart `ψ` is a condition on the target.
theorem StepLipHighPsiCond (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (n p : ℕ) (hn : 1 ≤ n) (h1 : ∀ q, Work.WilG4a.F1AffineW S q)
    (ih : ∀ q, WilkiesDesign.CG.FLem S q n) (hchoice : Work.WilkG4c.ChoiceHyp S)
    (hbdd : Work.WilkG4c.BddDxHyp S)
    (hP1 : Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PYLip p n))
    (hind : ∀ q : ℕ, q < p → Work.WilkG4c.FLemPHigh S q (n + 1) (Work.WilkG4c.PY q n)) :
    Work.WilkG4c.PsiHyp S hcd hder n p hn h1 ih hchoice hbdd hP1 hind := by
  intro aψ bψ F0
  obtain ⟨a_v, c_v, hValMem⟩ := Work.WilG4c.valSetMemG S p (n + 1)
  obtain ⟨A_pb, C_pb, hPB⟩ := YPullbackGraphUniform S p n
  set dFam : MvPolynomial (Fin 2) ℕ := MvPolynomial.C 3 * MvPolynomial.X 0
    + MvPolynomial.C (2 * c_v + 5) with hdFam
  have hdFamLe : ∀ D r : ℕ, D ≤ MvPolynomial.eval ![D, r] dFam := by
    intro D r
    rw [hdFam]
    simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_C, Matrix.cons_val_zero]
    omega
  set F0c : ℕ := F0 + (F0 + a_v) + 3 * (p + (n + 1) + 1) + 3 * p + 6 with hF0c
  set F0pb : ℕ := F0c + aψ + A_pb with hF0pb
  obtain ⟨Ag, Bg, hCurve⟩ := Work.WilkG4c.CurveFam S hder hchoice n p F0pb
  set qPb : MvPolynomial (Fin 2) ℕ := MvPolynomial.X 0
    + MvPolynomial.C (p + (n + 1)) * (bψ + MvPolynomial.C C_pb) + MvPolynomial.C C_pb
    with hqPb
  set dG : MvPolynomial (Fin 2) ℕ := MvPolynomial.aeval ![qPb, MvPolynomial.X 1]
    (MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.C 0] Bg) with hdG
  obtain ⟨At, Bt, hTuple⟩ := Work.WilkG4c.stepTupleMemU S p n F0pb Ag Bg
  set dtup : MvPolynomial (Fin 2) ℕ := MvPolynomial.aeval ![qPb, dG] Bt with hdtup
  obtain ⟨aGs, bGs, hGsMem⟩ := Work.WilG4c.famContDiffAt_mem S hcd (p + 1) At
  set qGs : MvPolynomial (Fin 2) ℕ := MvPolynomial.aeval ![dtup, MvPolynomial.X 1]
    (Polynomial.toMvPolynomial (0 : Fin 2) bGs) with hqGs
  obtain ⟨aC1, bC1, hC1Mem⟩ := Work.WilG4c.C1AllMem S hder p n F0pb
  set qC1 : MvPolynomial (Fin 2) ℕ := MvPolynomial.aeval ![qPb, MvPolynomial.X 1] bC1
    with hqC1
  obtain ⟨a1, bder, hderMem⟩ := hder F0pb (p + (n + 1))
  set qBad : MvPolynomial (Fin 2) ℕ := MvPolynomial.C 3
      * MvPolynomial.aeval ![qPb, MvPolynomial.C 1] bder
    + MvPolynomial.C (Work.WilkG4c.Cx p n + 32 * ((p + 1) + n + (p + (n + 1))) + 32)
    with hqBad
  set qCube : MvPolynomial (Fin 2) ℕ := MvPolynomial.C 6 with hqCube
  obtain ⟨aAq, bAq, hAqMem⟩ := Work.WilG4c.TmEqSetMem S hder p At dtup
  set dStar : MvPolynomial (Fin 2) ℕ := qC1 + qGs + qBad + bAq + qCube + MvPolynomial.C 1
    with hdStar
  set Fbad : ℕ := Work.WilkG4c.Fx p n a1 + 64 * ((p + 1) + n + (p + (n + 1))) + 64 + n + 1
    with hFbad
  set Fstar : ℕ := max (max aC1 aGs) (max Fbad (max aAq (p + (n + 1) + 4))) with hFstar
  obtain ⟨a_cells, bList, cList, hcdC⟩ := hcd Fstar (p + 1)
  set dc : MvPolynomial (Fin 2) ℕ := MvPolynomial.aeval ![dStar, MvPolynomial.X 1]
    (Polynomial.toMvPolynomial (0 : Fin 2) cList) with hdc
  obtain ⟨qk, hqk⟩ : ∃ qk : MvPolynomial (Fin 1) ℕ,
      ∀ k : ℕ, Fintype.card (Fin 1 ⊕ Fin k ⊕ Fin k ⊕ Fin (1 + k * n + k)
        ⊕ (Fin (1 + k * n + k) × Fin (1 + k * n + k)))
        ≤ MvPolynomial.eval ![k] qk := by
    refine ⟨MvPolynomial.C 5 * ((MvPolynomial.C (n + 1) * (MvPolynomial.X 0 + MvPolynomial.C 1))
      * (MvPolynomial.C (n + 1) * (MvPolynomial.X 0 + MvPolynomial.C 1))) + MvPolynomial.C 5, ?_⟩
    intro k
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, MvPolynomial.eval_add,
      MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, Matrix.cons_val_zero]
    set M : ℕ := (n + 1) * (k + 1) with hM
    have h1 : 1 + k * n + k ≤ M := by rw [hM]; nlinarith
    have h3 : k ≤ M := by omega
    have h5 : M ≤ M * M := by nlinarith
    have hA2 : (1 + k * n + k) * (1 + k * n + k) ≤ M * M := Nat.mul_le_mul h1 h1
    have h6 : (1 : ℕ) ≤ M * M := by nlinarith
    nlinarith [h1, h3, h5, hA2, h6]
  set dFam3 : MvPolynomial (Fin 3) ℕ :=
    MvPolynomial.rename (Fin.castLE (by norm_num : 2 ≤ 3)) dFam with hdFam3
  set dStar3 : MvPolynomial (Fin 3) ℕ :=
    MvPolynomial.aeval ![dFam3, (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℕ)] dStar with hdStar3
  set qk3 : MvPolynomial (Fin 3) ℕ :=
    MvPolynomial.aeval (fun _ : Fin 1 => (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℕ)) qk
    with hqk3
  set cA3 : MvPolynomial (Fin 3) ℕ := MvPolynomial.aeval ![dStar3, qk3] bList with hcA3
  set cA : MvPolynomial (Fin 4) ℝ := MvPolynomial.rename (Fin.castLE (by norm_num : 3 ≤ 4))
    (MvPolynomial.map (Nat.castRingHom ℝ) cA3) with hcA
  obtain ⟨aFin, bFin, cMerge, hcell⟩ :=
    psiCellDispatch S hcd hder n p hn hP1 hchoice ih hind h1 F0c a_cells At aψ Ag bψ dG dtup dc
      dFam
  obtain ⟨bFinal, hbFinal⟩ := Work.WilG4c.PolySubstFirst dFam bFin
  obtain ⟨cMid, hcMid⟩ := Work.WilG4c.PolySubstFirst4 dFam cMerge
  set cFin : MvPolynomial (Fin 4) ℝ :=
    (cA * cA + cMid * cMid) + (cA + cMid) + 1 with hcFin
  refine ⟨aFin, bFinal, cFin, ?_⟩
  intro D r k ε hε hε1 hr Λ F hΩg hPY hval ψ hψg hψcube hψsm hψnm
  set valS : Fin k → Set (Fin p → ℝ) :=
    fun i => {l | ∀ w ∈ WilkiesDesign.openCube (n + 1), F i l w ∈ Set.Ioo (0 : ℝ) 1}
    with hvalS
  have hvalSmem : ∀ i, valS i ∈ S.Ω (F0 + a_v) (D + c_v) p := by
    intro i
    have h := hValMem F0 D (F i) (hΩg i)
    rw [hvalS]
    exact h
  set Fc : Work.WilkG4c.Family k p (n + 1) :=
    fun i => Work.WilkG4c.paramClamp (valS i) (1 / 2 : ℝ) (F i) with hFc
  set Dc : ℕ := MvPolynomial.eval ![D, r] dFam with hDc
  have hDcE : Dc = 3 * D + 2 * c_v + 5 := by
    rw [hDc, hdFam]
    simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_C, Matrix.cons_val_zero]
    ring
  have hΩFc : ∀ i, WilkiesDesign.CG.famGraph (Fc i) ∈ S.Ω F0c Dc (p + (n + 1) + 1) := by
    intro i
    have h := Work.WilG4c.IteFamGraphMem S (valS i) (1 / 2 : ℝ) F Fc i
      (F0 + a_v) (D + c_v) F0 D (hvalSmem i) (hΩg i)
      (fun l t hl => by simp [hFc, Work.WilkG4c.paramClamp, hl])
      (fun l t hl => by simp [hFc, Work.WilkG4c.paramClamp, hl])
    have hdeg : D + 2 * (D + c_v) + 5 = Dc := by rw [hDcE]; ring
    rw [← hF0c, hdeg] at h
    exact h
  have hPYc : Work.WilkG4c.PY p n r k Fc := by
    rw [hFc]
    exact Work.WilkG4c.PY_paramClamp valS (1 / 2 : ℝ) (by norm_num) r F hPY
  have hvalU : Work.WilkG4c.ValuesIn01 (Set.univ : Set (Fin p → ℝ)) Fc := by
    intro i l _ x hx
    rw [hFc]
    simp only [Work.WilkG4c.paramClamp]
    by_cases hl : l ∈ valS i
    · rw [if_pos hl]
      rw [hvalS] at hl
      exact hl x hx
    · rw [if_neg hl]; norm_num
  have hvalΛ : Work.WilkG4c.ValuesIn01 Λ Fc :=
    fun i l _ x hx => hvalU i l (Set.mem_univ l) x hx
  have hψsmc : ∀ i, ∀ l, ∀ x ∈ Work.WilkG4c.I,
      ContDiffOn ℝ r (fun t => Fc i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)))
        (WilkiesDesign.openCube n) := by
    intro i l x hx
    by_cases hl : l ∈ valS i
    · rw [show (fun t => Fc i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)))
          = (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t))) from by
        funext t; simp only [hFc, Work.WilkG4c.paramClamp, if_pos hl]]
      exact hψsm i l x hx
    · rw [show (fun t => Fc i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)))
          = fun _ => (1 / 2 : ℝ) from by
        funext t; simp only [hFc, Work.WilkG4c.paramClamp, if_neg hl]]
      exact contDiffOn_const
  have hψnmc : ∀ i, ∀ l, ∀ x ∈ Work.WilkG4c.I, ∀ m, m ≤ r →
      ∀ t ∈ WilkiesDesign.openCube n,
      ‖iteratedFDeriv ℝ m (fun t => Fc i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t))) t‖ ≤ 1 := by
    intro i l x hx m hm t ht
    by_cases hl : l ∈ valS i
    · rw [show (fun t => Fc i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)))
          = (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t))) from by
        funext t; simp only [hFc, Work.WilkG4c.paramClamp, if_pos hl]]
      exact hψnm i l x hx m hm t ht
    · rw [show (fun t => Fc i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)))
          = fun _ => (1 / 2 : ℝ) from by
        funext t; simp only [hFc, Work.WilkG4c.paramClamp, if_neg hl]]
      cases m with
      | zero => rw [norm_iteratedFDeriv_zero]; norm_num
      | succ m' => rw [iteratedFDeriv_succ_const]; simp
  have hψgD : ∀ j, WilkiesDesign.CG.famGraph (ψ j) ∈
      S.Ω aψ (MvPolynomial.eval ![Dc, r] bψ) ((p + 1) + n + 1) := by
    intro j
    refine Work.WilkG4c.Omega_mono_D_le S ?_ (hψg j)
    refine Work.WilkG4c.eval_mono bψ (fun i => ?_)
    fin_cases i
    · show D ≤ Dc
      rw [hDcE]; omega
    · show r ≤ r
      exact le_rfl
  have hPBs := hPB F0c Dc aψ (MvPolynomial.eval ![Dc, r] bψ) Fc ψ hΩFc hψgD
  have hqPbE : MvPolynomial.eval ![Dc, r] qPb
      = Dc + (p + (n + 1)) * (MvPolynomial.eval ![Dc, r] bψ + C_pb) + C_pb := by
    rw [hqPb]
    simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_C, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hGpmem : ∀ i, WilkiesDesign.CG.famGraph (Work.WilkG4c.yPullback Fc ψ i)
      ∈ S.Ω F0pb (MvPolynomial.eval ![Dc, r] qPb) (p + (n + 1) + 1) := by
    intro i
    have h1 : F0c + aψ + A_pb ≤ F0pb := by rw [hF0pb]
    have h2 : Dc + (p + (n + 1)) * (MvPolynomial.eval ![Dc, r] bψ + C_pb) + C_pb
        ≤ MvPolynomial.eval ![Dc, r] qPb := le_of_eq hqPbE.symm
    exact Work.WilkG4c.Omega_mono_le S h1 h2 (hPBs.2 i)
  have hγdata : ∀ i : Fin k, ∃ γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ),
      (∀ j, WilkiesDesign.graphOf (fun w : Fin (p + 1) → ℝ =>
          γ (Fin.init w) (w (Fin.last p)) j)
        ∈ S.Ω Ag (MvPolynomial.eval ![MvPolynomial.eval ![Dc, r] qPb, 0] Bg)
            (p + 1 + 1)) ∧
      (∀ l, ∀ x, Work.WilkG4c.NearMax (Work.WilkG4c.yPullback Fc ψ i) l x →
        γ l x ∈ WilkiesDesign.openCube n ∧
        Work.WilkG4c.xPt l x (γ l x) ∈
          interior {z | ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat
            (Work.WilkG4c.yPullback Fc ψ i)) z} ∧
        ∀ y' ∈ WilkiesDesign.openCube n,
          Work.WilkG4c.xPt l x y' ∈
            interior {z | ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat
              (Work.WilkG4c.yPullback Fc ψ i)) z} →
          |Work.WilkG4c.xDeriv (Work.WilkG4c.yPullback Fc ψ i) l x y'| ≤
            2 * |Work.WilkG4c.xDeriv (Work.WilkG4c.yPullback Fc ψ i) l x (γ l x)|) := by
    intro i
    have hC := hCurve (MvPolynomial.eval ![Dc, r] qPb) Set.univ
      (Work.WilkG4c.yPullback Fc ψ i) (hGpmem i)
    refine ⟨hC.choose, ?_, ?_⟩
    · intro j
      simpa only [Fin.init_def] using hC.choose_spec.1 j
    · intro l x h
      exact hC.choose_spec.2 l (Set.mem_univ l) x h
  set γ : Fin k → (Fin p → ℝ) → ℝ → (Fin n → ℝ) := fun i => (hγdata i).choose with hγdef
  have hγg : ∀ i j, WilkiesDesign.graphOf (fun w : Fin (p + 1) → ℝ =>
      γ i (Fin.init w) (w (Fin.last p)) j)
      ∈ S.Ω Ag (MvPolynomial.eval ![MvPolynomial.eval ![Dc, r] qPb, 0] Bg) (p + 1 + 1) :=
    fun i j => ((hγdata i).choose_spec).1 j
  have hγmax : ∀ i l x, Work.WilkG4c.NearMax (Work.WilkG4c.yPullback Fc ψ i) l x →
      γ i l x ∈ WilkiesDesign.openCube n ∧
      Work.WilkG4c.xPt l x (γ i l x) ∈
        interior {z | ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat
          (Work.WilkG4c.yPullback Fc ψ i)) z} ∧
      ∀ y' ∈ WilkiesDesign.openCube n,
        Work.WilkG4c.xPt l x y' ∈
          interior {z | ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat
            (Work.WilkG4c.yPullback Fc ψ i)) z} →
        |Work.WilkG4c.xDeriv (Work.WilkG4c.yPullback Fc ψ i) l x y'| ≤
          2 * |Work.WilkG4c.xDeriv (Work.WilkG4c.yPullback Fc ψ i) l x (γ i l x)| :=
    fun i l x h => ((hγdata i).choose_spec).2 l x h
  have hdGe : MvPolynomial.eval ![Dc, r] dG
      = MvPolynomial.eval ![MvPolynomial.eval ![Dc, r] qPb, 0] Bg := by
    rw [hdG, Work.WilG4c.eval_aeval_eq]
    have h1 : (fun i : Fin 2 => MvPolynomial.eval ![Dc, r] (![qPb, MvPolynomial.X 1] i))
        = ![MvPolynomial.eval ![Dc, r] qPb, r] := by
      funext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
    rw [h1, Work.WilG4c.eval_aeval_eq]
    have h2 : (fun i : Fin 2 => MvPolynomial.eval
        ![MvPolynomial.eval ![Dc, r] qPb, r] (![MvPolynomial.X 0, MvPolynomial.C 0] i))
        = ![MvPolynomial.eval ![Dc, r] qPb, 0] := by
      funext i
      fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [h2]
  have hγgD : ∀ i j, WilkiesDesign.graphOf (fun w : Fin (p + 1) → ℝ =>
      γ i (Fin.init w) (w (Fin.last p)) j)
      ∈ S.Ω Ag (MvPolynomial.eval ![Dc, r] dG) (p + 1 + 1) := by
    intro i j
    rw [hdGe]
    exact hγg i j
  let Ix : Type := Fin 1 ⊕ (Fin k × Fin n) ⊕ Fin k
  have hIxcard : Fintype.card Ix = 1 + k * n + k := by
    show Fintype.card (Fin 1 ⊕ (Fin k × Fin n) ⊕ Fin k) = 1 + k * n + k
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    ring
  let kt : ℕ := 1 + k * n + k
  let eIx : Ix ≃ Fin kt := (Fintype.equivFin Ix).trans (finCongr hIxcard)
  let Tfun : Ix → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ := psiTfun Fc ψ γ
  let Tm : Fin kt → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ := psiTm Fc ψ γ eIx
  have hdtupE : MvPolynomial.eval ![Dc, r] dtup
      = MvPolynomial.eval ![MvPolynomial.eval ![Dc, r] qPb,
          MvPolynomial.eval ![MvPolynomial.eval ![Dc, r] qPb, 0] Bg] Bt := by
    rw [hdtup, Work.WilG4c.eval_aeval_eq]
    have h1 : (fun i : Fin 2 => MvPolynomial.eval ![Dc, r] (![qPb, dG] i))
        = ![MvPolynomial.eval ![Dc, r] qPb, MvPolynomial.eval ![Dc, r] dG] := by
      funext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
    rw [h1, hdGe]
  have hTupleC := hTuple k (MvPolynomial.eval ![Dc, r] qPb)
    (fun i => Work.WilkG4c.yPullback Fc ψ i) γ (fun i => hGpmem i) (fun i j => hγg i j)
  have hTmΩ : ∀ a : Fin kt, WilkiesDesign.CG.famGraph (Tm a)
      ∈ S.Ω At (MvPolynomial.eval ![Dc, r] dtup) (p + 1 + 1) := by
    intro a
    rw [hdtupE]
    show WilkiesDesign.CG.famGraph (Tfun (eIx.symm a)) ∈ _
    rcases eIx.symm a with x | (s | i)
    · show WilkiesDesign.CG.famGraph (fun _ (u : Fin 1 → ℝ) => u 0) ∈ _
      exact hTupleC.1
    · obtain ⟨i, j⟩ := s
      show WilkiesDesign.CG.famGraph (fun l (u : Fin 1 → ℝ) => γ i l (u 0) j) ∈ _
      exact hTupleC.2.1 i j
    · show WilkiesDesign.CG.famGraph (fun l (u : Fin 1 → ℝ) =>
          Work.WilkG4c.yPullback Fc ψ i l (Fin.cons (u 0) (γ i l (u 0)))) ∈ _
      exact hTupleC.2.2 i
  have hidT : ∃ a : Fin kt, ∀ (l : Fin p → ℝ) (u : Fin 1 → ℝ), Tm a l u = u 0 := by
    refine ⟨eIx (Sum.inl 0), ?_⟩
    intro l u
    show Tfun (eIx.symm (eIx (Sum.inl 0))) l u = u 0
    rw [Equiv.symm_apply_apply]
    simp only [Tfun, psiTfun]
  have hγxT : ∀ i j, ∃ a : Fin kt, ∀ (l : Fin p → ℝ) (u : Fin 1 → ℝ),
      Tm a l u = γ i l (u 0) j := by
    intro i j
    refine ⟨eIx (Sum.inr (Sum.inl (i, j))), ?_⟩
    intro l u
    show Tfun (eIx.symm (eIx (Sum.inr (Sum.inl (i, j))))) l u = γ i l (u 0) j
    rw [Equiv.symm_apply_apply]
    simp only [Tfun, psiTfun]
  have hcxT : ∀ i, ∃ a : Fin kt, ∀ (l : Fin p → ℝ) (u : Fin 1 → ℝ),
      Tm a l u = Work.WilkG4c.yPullback Fc ψ i l (Fin.cons (u 0) (γ i l (u 0))) := by
    intro i
    refine ⟨eIx (Sum.inr (Sum.inr i)), ?_⟩
    intro l u
    show Tfun (eIx.symm (eIx (Sum.inr (Sum.inr i)))) l u = _
    rw [Equiv.symm_apply_apply]
    simp only [Tfun, psiTfun]
  have hqGsE : MvPolynomial.eval ![Dc, r] qGs = bGs.eval (MvPolynomial.eval ![Dc, r] dtup) := by
    rw [hqGs, Work.WilG4c.eval_aeval_eq]
    have h1 : (fun i : Fin 2 => MvPolynomial.eval ![Dc, r] (![dtup, MvPolynomial.X 1] i))
        = ![MvPolynomial.eval ![Dc, r] dtup, r] := by
      funext i
      fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [h1, MvPolynomial.eval_toMvPolynomial]
    simp [Matrix.cons_val_zero]
  have hGsMem' : ∀ a : Fin kt, {w : Fin (p + 1) → ℝ | ContDiffAt ℝ 1
      (fun z : Fin (p + 1) → ℝ => Tm a (Fin.init z) (fun _ => z (Fin.last p))) w}
      ∈ S.Ω aGs (MvPolynomial.eval ![Dc, r] qGs) (p + 1) := by
    intro a
    have hf : WilkiesDesign.graphOf (fun z : Fin (p + 1) → ℝ =>
        Tm a (Fin.init z) (fun _ => z (Fin.last p))) ∈
        S.Ω At (MvPolynomial.eval ![Dc, r] dtup) (p + 1 + 1) := by
      rw [show (fun z : Fin (p + 1) → ℝ => Tm a (Fin.init z) (fun _ => z (Fin.last p)))
          = Work.WilkG4c.flatFam (Tm a) from rfl]
      rw [← Work.WilkG4c.famGraph_eq_graphOf_flatFam]
      exact hTmΩ a
    rw [hqGsE]
    exact hGsMem (MvPolynomial.eval ![Dc, r] dtup) _ hf
  set DS : ℕ := MvPolynomial.eval ![Dc, r] dStar with hDS
  have hDSqC1 : MvPolynomial.eval ![Dc, r] qC1 ≤ DS := by
    rw [hDS, hdStar]; simp only [MvPolynomial.eval_add]; omega
  have hDSqGs : MvPolynomial.eval ![Dc, r] qGs ≤ DS := by
    rw [hDS, hdStar]; simp only [MvPolynomial.eval_add]; omega
  have hDSqBad : MvPolynomial.eval ![Dc, r] qBad ≤ DS := by
    rw [hDS, hdStar]; simp only [MvPolynomial.eval_add]; omega
  have hDS6 : 6 ≤ DS := by
    rw [hDS, hdStar, hqCube]
    simp only [MvPolynomial.eval_add, MvPolynomial.eval_C]
    omega
  have hCubeMem : Work.WilG4c.inCubeSet p 1 ∈ S.Ω Fstar DS (p + 1) := by
    refine Work.WilkG4c.Omega_mono_le S ?_ ?_ (Work.WilG4c.inCubeSet_mem S p 1)
    · rw [hFstar]; omega
    · exact le_trans (le_of_eq (by norm_num : 6 * 1 = 6)) hDS6
  have hBadMem : ∀ i, Work.WilkG4c.badCurve (Work.WilkG4c.yPullback Fc ψ i)
      ∈ S.Ω Fstar DS (p + 1) := by
    intro i
    have hgraph : WilkiesDesign.graphOf (Work.WilkG4c.famFunHat (Work.WilkG4c.yPullback Fc ψ i))
        ∈ S.Ω F0pb (MvPolynomial.eval ![Dc, r] qPb) (p + (n + 1) + 1) := by
      rw [← Work.WilkG4c.famGraph_eq_graphOf_famFunHat]
      exact hGpmem i
    have hDg := hderMem (MvPolynomial.eval ![Dc, r] qPb)
      (Work.WilkG4c.famFunHat (Work.WilkG4c.yPullback Fc ψ i)) hgraph 1
      (fun _ : Fin 1 => Work.WilkG4c.xDirHat p n)
    have hbad := Work.WilkG4c.badCurve_mem hDg
    refine Work.WilkG4c.Omega_mono_le S ?_ ?_ hbad
    · rw [hFstar]; omega
    · have hqBadE : MvPolynomial.eval ![Dc, r] qBad
          = 3 * MvPolynomial.eval ![MvPolynomial.eval ![Dc, r] qPb, 1] bder
            + Work.WilkG4c.Cx p n + 32 * ((p + 1) + n + (p + (n + 1))) + 32 := by
        rw [hqBad]
        simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
        rw [Work.WilG4c.eval_aeval_eq]
        have h1 : (fun i : Fin 2 => MvPolynomial.eval ![Dc, r] (![qPb, MvPolynomial.C 1] i))
            = ![MvPolynomial.eval ![Dc, r] qPb, 1] := by
          funext i
          fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        rw [h1]
        omega
      have hDx : Work.WilkG4c.Dx p n
          (MvPolynomial.eval ![MvPolynomial.eval ![Dc, r] qPb, 1] bder)
          = 3 * MvPolynomial.eval ![MvPolynomial.eval ![Dc, r] qPb, 1] bder
            + Work.WilkG4c.Cx p n := rfl
      rw [hDx]
      exact le_trans (le_of_eq hqBadE.symm) hDSqBad
  have hC1Mem'' : ∀ i, Work.WilkG4c.C1All (Work.WilkG4c.yPullback Fc ψ i)
      ∈ S.Ω Fstar DS (p + 1) := by
    intro i
    have h := hC1Mem (MvPolynomial.eval ![Dc, r] qPb) r (Work.WilkG4c.yPullback Fc ψ i)
      (hGpmem i)
    refine Work.WilkG4c.Omega_mono_le S ?_ ?_ h
    · rw [hFstar]; omega
    · have hqC1E : MvPolynomial.eval ![Dc, r] qC1
          = MvPolynomial.eval ![MvPolynomial.eval ![Dc, r] qPb, r] bC1 := by
        rw [hqC1, Work.WilG4c.eval_aeval_eq]
        have h1 : (fun i : Fin 2 => MvPolynomial.eval ![Dc, r] (![qPb, MvPolynomial.X 1] i))
            = ![MvPolynomial.eval ![Dc, r] qPb, r] := by
          funext i
          fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        rw [h1]
      exact le_trans (le_of_eq hqC1E.symm) hDSqC1
  have hEqMem : ∀ a b : Fin kt, {w : Fin (p + 1) → ℝ |
      |(fderiv ℝ (fun z : Fin (p + 1) → ℝ =>
          Tm a (Fin.init z) (fun _ => z (Fin.last p))) w) (Pi.single (Fin.last p) 1)|
      = |(fderiv ℝ (fun z : Fin (p + 1) → ℝ =>
          Tm b (Fin.init z) (fun _ => z (Fin.last p))) w) (Pi.single (Fin.last p) 1)|}
      ∈ S.Ω Fstar DS (p + 1) := by
    intro a b
    refine Work.WilkG4c.Omega_mono_le S ?_ ?_
      (hAqMem (Fin kt) Dc r Tm (fun a => hTmΩ a) a b)
    · rw [hFstar]; omega
    · rw [hDS, hdStar]; simp only [MvPolynomial.eval_add]; omega
  let ιX : Type := Fin 1 ⊕ Fin k ⊕ Fin k ⊕ Fin kt ⊕ (Fin kt × Fin kt)
  let Xfun : ιX → Set (Fin (p + 1) → ℝ) := psiXfun Fc ψ Tm
  have hXmem : ∀ s : ιX, Xfun s ∈ S.Ω Fstar DS (p + 1) := by
    intro s
    rcases s with x | (i | (i | (a | ab)))
    · exact hCubeMem
    · exact hBadMem i
    · exact hC1Mem'' i
    · refine Work.WilkG4c.Omega_mono_le S ?_ ?_ (hGsMem' a)
      · rw [hFstar]; omega
      · rw [hDS, hdStar]; simp only [MvPolynomial.eval_add]; omega
    · exact hEqMem ab.1 ab.2
  let eX : ιX ≃ Fin (Fintype.card ιX) := Fintype.equivFin ιX
  let X : Fin (Fintype.card ιX) → Set (Fin (p + 1) → ℝ) := fun i => Xfun (eX.symm i)
  have hXmem' : ∀ i : Fin (Fintype.card ιX), X i ∈ S.Ω Fstar DS (p + 1) :=
    fun i => hXmem (eX.symm i)
  obtain ⟨C, hCdec, href, hCcard, hCΩ⟩ := hcdC DS (Fintype.card ιX) X hXmem'
  have hcard_le : Fintype.card ιX ≤ MvPolynomial.eval ![k] qk := hqk k
  have hXdisj : ∀ s : ιX, ∀ κ ∈ C, κ ⊆ Xfun s ∨ Disjoint κ (Xfun s) := by
    intro s κ hκ
    have h := href (eX s) κ hκ
    simpa only [X, Xfun, Equiv.symm_apply_apply] using h
  have hdcE' : MvPolynomial.eval ![Dc, r] dc = cList.eval DS := by
    rw [hdc, Work.WilG4c.eval_aeval_eq_gen]
    have h1 : (fun i : Fin 2 => MvPolynomial.eval ![Dc, r] (![dStar, MvPolynomial.X 1] i))
        = ![DS, r] := by
      funext i
      fin_cases i
      · simp only [Matrix.cons_val_zero]; rfl
      · simp [Matrix.cons_val_one, Matrix.head_cons]
    rw [h1, MvPolynomial.eval_toMvPolynomial]
    simp [Matrix.cons_val_zero]
  have hCΩ' : ∀ κ ∈ C, κ ∈ S.Ω a_cells (MvPolynomial.eval ![Dc, r] dc) (p + 1) := by
    intro κ hκ
    rw [hdcE']
    exact hCΩ κ hκ
  have hcellκ := hcell D r k ε hε hε1 hr Λ Fc ψ γ kt eIx F0pb Dc qPb hdFamLe hΩFc hPYc hvalU
    hψgD hψcube hψsmc hψnmc hγgD hγmax hTmΩ hidT hγxT hcxT hGpmem C hCdec hCΩ' hXdisj
  have hFc_eq : ∀ (i : Fin k) (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ), l ∈ Λ →
      Fc i l t = F i l t := by
    intro i l t hl
    have hl' : l ∈ valS i := by
      rw [hvalS]
      exact fun w hw => hval i l hl w hw
    simp only [hFc, Work.WilkG4c.paramClamp, if_pos hl']
  have hA : (C.card : ℝ) ≤
      MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cA := by
    have hAev : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cA
        = ((MvPolynomial.eval ![D, r, k] cA3 : ℕ) : ℝ) := by
      rw [hcA]
      exact Work.WilG4c.eval_cast_rename3 cA3 D r k (-Real.log ε)
    have hA3 : MvPolynomial.eval ![D, r, k] cA3
        = bList.eval ![DS, MvPolynomial.eval ![k] qk] := by
      rw [hcA3, Work.WilG4c.eval_aeval_eq_gen]
      have h1 : (fun i : Fin 2 => MvPolynomial.eval ![D, r, k] (![dStar3, qk3] i))
          = ![DS, MvPolynomial.eval ![k] qk] := by
        funext i
        fin_cases i
        · show MvPolynomial.eval ![D, r, k] dStar3 = DS
          rw [hdStar3, Work.WilG4c.eval_aeval_eq_gen]
          have h2 : (fun i : Fin 2 => MvPolynomial.eval ![D, r, k]
              (![dFam3, (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℕ)] i))
              = ![MvPolynomial.eval ![D, r] dFam, r] := by
            funext i
            fin_cases i
            · show MvPolynomial.eval ![D, r, k] dFam3 = MvPolynomial.eval ![D, r] dFam
              have hpt : (![D, r, k] ∘ (Fin.castLE (by norm_num : 2 ≤ 3))) = ![D, r] := by
                funext j
                fin_cases j <;> simp [Fin.castLE]
              rw [hdFam3, MvPolynomial.eval_rename, hpt]
            · simp [Matrix.cons_val_one, Matrix.head_cons]
          rw [h2]
        · show MvPolynomial.eval ![D, r, k] qk3 = MvPolynomial.eval ![k] qk
          rw [hqk3, Work.WilG4c.eval_aeval_eq_gen]
          have h3 : (fun _ : Fin 1 => MvPolynomial.eval ![D, r, k]
              (MvPolynomial.X (2 : Fin 3))) = ![k] := by
            funext i
            fin_cases i
            simp [Matrix.cons_val]
          rw [h3]
      rw [h1]
    rw [hAev, hA3]
    exact_mod_cast le_trans hCcard (Work.WilkG4c.eval_mono bList (fun i => by
      fin_cases i
      · exact le_rfl
      · exact hcard_le))
  have hMidEq : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cMid
      = MvPolynomial.eval ![(Dc : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cMerge :=
    hcMid D r k (-Real.log ε)
  exact Work.WilG4c.psiCellPack S C hCdec Fc F Λ ψ ε D Dc r aFin bFin bFinal cMerge cA cMid cFin
    hcellκ hA hMidEq hcFin (hbFinal D r) hFc_eq

end Work.WilG4c
