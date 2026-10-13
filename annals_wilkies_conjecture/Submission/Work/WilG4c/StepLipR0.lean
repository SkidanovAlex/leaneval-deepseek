/-
  WilG4c / StepLipR0 — the `r = 0` case of the §5.3 reduction of BNZ.

  The proof reduces to a sharply chosen cylindrical decomposition of `ℝ^{p+N+1}` that is
  compatible with the graphs of the family members: for such a decomposition, the restriction
  of every member to every cell of the *projected* decomposition of `ℝ^{p+N}` is continuous
  (`continuousOn_of_mem_projDeg`, module `StepLipR0Aux2`), so the nested-interpolation
  parametrisation of the cell (`CellTowerCont`) is a legitimate chart with a continuous
  composite, and its surjectivity gives the value `ε`-cover by exact hitting.
-/
import Mathlib
import Submission.Work.WilG4a.F1AffineW
import Submission.Work.WilG4c.StepLipR0Aux1
import Submission.Work.WilG4c.StepLipR0Aux2

set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilkG4c

theorem StepLipR0 (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (n p : ℕ) (hn : 1 ≤ n)
    (h1 : ∀ q, Work.WilG4a.F1AffineW S q) (ih : ∀ q, WilkiesDesign.CG.FLem S q n)
    (hchoice : Work.WilkG4c.ChoiceHyp S) (hbdd : Work.WilkG4c.BddDxHyp S)
    (hP1 : Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PYLip p n)) :
    ∀ (F0 : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
      ∀ (D k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
      ∀ (Λ : Set (Fin p → ℝ)) (F : Work.WilkG4c.Family k p (n + 1)),
        Work.WilkG4c.PY p n 0 k F →
        (∀ i, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (p + (n + 1) + 1)) →
        Work.WilkG4c.ValuesIn01 Λ F →
        ∃ Φ : Finset (Work.WilkG4c.ChartTuple p (n + 1)),
          (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (0 : ℝ), (k : ℝ), -Real.log ε] c ∧
          Work.WilkG4c.ChartsOK S a (MvPolynomial.eval ![D, 0] b) 0 Λ F Φ ∧
          Work.WilkG4c.Covers Λ F Φ ε := by
  classical
  intro F0
  obtain ⟨a_cd, b_cd, c_cd, hcdA⟩ := hcd (max (p + (n + 1) + 5) F0) (p + (n + 1) + 1)
  obtain ⟨a_T, b_T, hTower⟩ := CellTowerCont S p (n + 1) (a_cd + 1)
  -- the degree of the lifted cube is the constant `6 * (n+1)`, so everything is shifted by it
  set K : ℕ := 6 * (n + 1) with hK
  set c_cdS : Polynomial ℕ := c_cd.comp (Polynomial.X + Polynomial.C K) with hc_cdS
  obtain ⟨B_T, hB_T₀⟩ := polyCompEval' b_T c_cdS
  obtain ⟨B_P, hB_P₀⟩ := polyCompEval' (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℕ) c_cdS
  obtain ⟨c_fin, hc_fin⟩ := polyCountEval_shift b_cd K
  have hB_T : ∀ D : ℕ, MvPolynomial.eval ![D, 0] B_T
      = MvPolynomial.eval ![(c_cd.eval (D + K)), 1] b_T := by
    intro D
    rw [hB_T₀ D, hc_cdS, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
  have hB_P : ∀ D : ℕ, MvPolynomial.eval ![D, 0] B_P = c_cd.eval (D + K) := by
    intro D
    rw [hB_P₀ D, hc_cdS, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    simp [MvPolynomial.eval_X]
  set aΛ : ℕ := a_cd + 1 + (n + 1) + p with haΛ
  refine ⟨max (max (a_T + 4) (p + (n + 1) + 4))
      (max (aΛ + (p + (n + 1)) + (p + (n + 1)) + 1 + p + 4) 5),
    MvPolynomial.C 4 * (B_T + B_P + MvPolynomial.C 5), c_fin, ?_⟩
  intro D k ε hε hε1 Λ F hPY hΩg hval
  set X : Fin (k + 1) → Set (Fin (p + (n + 1) + 1) → ℝ) :=
    fun i => Fin.cases {z | Fin.init z ∈ inCubeSet p (n + 1)} (fun j => famGraph (F j)) i with hX
  have hXmem : ∀ i : Fin (k + 1),
      X i ∈ S.Ω (max (p + (n + 1) + 5) F0) (D + K) (p + (n + 1) + 1) := by
    intro i
    induction i using Fin.cases with
    | zero =>
      have h0 : X 0 = {z : Fin (p + (n + 1) + 1) → ℝ | Fin.init z ∈ inCubeSet p (n + 1)} := by
        rw [hX]; rfl
      rw [h0]
      refine Omega_mono_le S ?_ ?_ (lift_inCubeSet_mem' S p (n + 1))
      · refine le_trans (by omega : p + (n + 1) + 4 + 1 ≤ p + (n + 1) + 5) (le_max_left _ _)
      · rw [hK]; exact Nat.le_add_left _ _
    | succ j =>
      have hs : X (Fin.succ j) = famGraph (F j) := by rw [hX]; rfl
      rw [hs]
      refine Omega_mono_le S (le_max_right _ _) ?_ (hΩg j)
      rw [hK]; exact Nat.le_add_right _ _
  obtain ⟨C_D, hCD_dec, hCD_comp, hCD_card, hCD_Ω⟩ := hcdA (D + K) (k + 1) X hXmem
  set C : Finset (Set (Fin (p + (n + 1)) → ℝ)) := C_D.image (fun c => Fin.init '' c) with hC
  have hC_dec : IsCylDecomp (p + (n + 1)) C := by
    have h := (IsCylDecomp.eq_2 (p + (n + 1)) C_D).mp hCD_dec
    exact h.2.2.2
  have hC_Ω : ∀ κ ∈ C, κ ∈ S.Ω (a_cd + 1) (c_cd.eval (D + K)) (p + (n + 1)) := by
    intro κ hκ
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hκ
    rw [image_init_eq_projLast]
    exact S.proj (hCD_Ω c hc)
  have hC_comp : ∀ κ ∈ C, κ ⊆ inCubeSet p (n + 1) ∨ Disjoint κ (inCubeSet p (n + 1)) := by
    intro κ hκ
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hκ
    have h0 : X 0 = {z : Fin (p + (n + 1) + 1) → ℝ | Fin.init z ∈ inCubeSet p (n + 1)} := by
      rw [hX]; rfl
    have h := hCD_comp 0 c hc
    rw [h0] at h
    exact image_init_subset_or_disjoint h
  have hC_cont : ∀ (i : Fin k) (κ : Set (Fin (p + (n + 1)) → ℝ)), κ ∈ C →
      ContinuousOn (famFun (F i)) κ := by
    intro i κ hκ
    refine continuousOn_of_mem_projDecomp' (f := famFun (F i)) hCD_dec ?_ κ hκ
    intro c hc
    have hs : X (Fin.succ i) = famGraph (F i) := by rw [hX]; rfl
    have h := hCD_comp (Fin.succ i) c hc
    rw [hs] at h
    rw [graphOf_famFun]
    exact h
  have hcell : ∀ κ : Set (Fin (p + (n + 1)) → ℝ), κ ∈ C →
      ∃ Φκ : Finset (ChartTuple p (n + 1)),
        (Φκ.card : ℝ) ≤ 1 ∧
        ChartsOK S (max (max (a_T + 4) (p + (n + 1) + 4))
              (max (aΛ + (p + (n + 1)) + (p + (n + 1)) + 1 + p + 4) 5))
          (MvPolynomial.eval ![D, 0]
            (MvPolynomial.C 4 * (B_T + B_P + MvPolynomial.C 5))) 0 Λ F Φκ ∧
        (∀ l ∈ Λ, ∀ x : Fin (n + 1) → ℝ, x ∈ openCube (n + 1) → Fin.append l x ∈ κ →
          ∃ φ ∈ Φκ, ∃ t ∈ openCube (n + 1), ∀ i, |F i l (fun j => φ j l t) - F i l x| < ε) := by
    intro κ hκ
    by_cases hsub : κ ⊆ inCubeSet p (n + 1)
    · obtain ⟨Ψ, hΨg, hΨc, hΨκ, hΨs, hΨcont⟩ :=
        hTower (c_cd.eval (D + K)) C hC_dec hC_Ω κ hκ hsub
          {l : Fin p → ℝ | ∃ y : Fin (n + 1) → ℝ, Fin.append l y ∈ κ}
          (fun l hl => hl)
      have hΛmem : {l : Fin p → ℝ | ∃ y : Fin (n + 1) → ℝ, Fin.append l y ∈ κ} ∈
          S.Ω aΛ (c_cd.eval (D + K)) p := by
        have hset : {l : Fin p → ℝ | ∃ y : Fin (n + 1) → ℝ, Fin.append l y ∈ κ}
            = Work.WilG0.projLastIter p (n + 1) κ := by
          rw [Work.WilG0.projLastIter_eq]
          ext l
          constructor
          · rintro ⟨y, hy⟩
            exact ⟨y, by rwa [snocIt_eq_append']⟩
          · rintro ⟨w, hw⟩
            exact ⟨w, by rwa [snocIt_eq_append'] at hw⟩
        rw [hset, haΛ]
        exact Work.WilG0.projLastIter_mem S p (n + 1) (a_cd + 1) (c_cd.eval (D + K)) κ
          (hC_Ω κ hκ)
      obtain ⟨hOK, hcov⟩ :=
        cell_chart_cont_single' S F Λ κ
          {l : Fin p → ℝ | ∃ y : Fin (n + 1) → ℝ, Fin.append l y ∈ κ} rfl
          aΛ (c_cd.eval (D + K)) hΛmem a_T b_T Ψ hΨg hΨc hΨκ hΨs hΨcont hsub
          (fun i => hC_cont i κ hκ)
          (fun i l hl z hz => hval i l hl z hz)
          (fun i l z hz => abs_le_one_of_YBound_zero (show YBound F 0 from hPY) hz) ε hε
      have hE : MvPolynomial.eval ![(c_cd.eval (D + K)), 0]
            (MvPolynomial.eval₂ MvPolynomial.C
              (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 else 1) b_T)
          = MvPolynomial.eval ![(c_cd.eval (D + K)), 1] b_T := by
        rw [eval_eval₂_C_nat]
        have hfun : (fun s : Fin 2 => MvPolynomial.eval ![(c_cd.eval (D + K)), 0]
            (if s = 0 then MvPolynomial.X 0 else 1)) = ![(c_cd.eval (D + K)), 1] := by
          funext i
          fin_cases i <;> simp
        rw [hfun]
      refine ⟨{fun j l t => cellChartFun {l : Fin p → ℝ |
          ∃ y : Fin (n + 1) → ℝ, Fin.append l y ∈ κ} Ψ l t j}, ?_, ?_, ?_⟩
      · rw [Finset.card_singleton]; norm_num
      · refine ChartsOK.mono hOK le_rfl ?_
        simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
        rw [hE, hB_T D, hB_P D]
        omega
      · intro l hl x hx hmem
        obtain ⟨t, ht, hv⟩ := hcov l hl x hx hmem
        exact ⟨_, Finset.mem_singleton_self _, t, ht, hv⟩
    · refine ⟨∅, ?_, ?_, ?_⟩
      · simp
      · intro φ hφ
        exact absurd hφ (by simp)
      · intro l hl x hx hmem
        exfalso
        rcases hC_comp κ hκ with h | h
        · exact hsub h
        · have h1 : Fin.append l x ∈ inCubeSet p (n + 1) := by
            rw [mem_inCubeSet_iff]
            intro j
            rw [Fin.append_right]
            exact hx j
          exact Set.disjoint_left.mp h hmem h1
  set Φf : Set (Fin (p + (n + 1)) → ℝ) → Finset (ChartTuple p (n + 1)) :=
    fun κ => if h : κ ∈ C then (hcell κ h).choose else ∅ with hΦf
  have hΦf_eq : ∀ (κ : Set (Fin (p + (n + 1)) → ℝ)) (hκ : κ ∈ C),
      Φf κ = (hcell κ hκ).choose := by
    intro κ hκ
    rw [hΦf]
    exact dif_pos hκ
  refine ⟨C.biUnion Φf, ?_, ?_, ?_⟩
  · have h1 : ((C.biUnion Φf).card : ℝ) ≤ ∑ κ ∈ C, ((Φf κ).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le (s := C) (t := Φf)
    have h2 : ∑ κ ∈ C, ((Φf κ).card : ℝ) ≤ ∑ _κ ∈ C, (1 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro κ hκ
      rw [hΦf_eq κ hκ]
      exact (hcell κ hκ).choose_spec.1
    have h3 : ∑ _κ ∈ C, (1 : ℝ) = (C.card : ℝ) := by simp
    have h4 : (C.card : ℝ) ≤ ((MvPolynomial.eval ![D + K, k + 1] b_cd : ℕ) : ℝ) := by
      have hle : C.card ≤ C_D.card := by
        rw [hC]; exact Finset.card_image_le
      exact_mod_cast le_trans hle hCD_card
    have h5 := hc_fin D k ε hε hε1
    linarith
  · refine ChartsOK.biUnion ?_
    intro κ hκ
    rw [hΦf_eq κ hκ]
    exact (hcell κ hκ).choose_spec.2.1
  · intro l hl x hx
    have hcov := (IsCylDecomp.eq_2 (p + n) C).mp hC_dec
    obtain ⟨κ, hκ, hmem⟩ := hcov.2.2.1 (Fin.append (m := p) (n := n + 1) l x)
    obtain ⟨φ, hφ, t, ht, hcv⟩ := (hcell κ hκ).choose_spec.2.2 l hl x hx hmem
    exact ⟨φ, Finset.mem_biUnion.mpr ⟨κ, hκ, by rw [hΦf_eq κ hκ]; exact hφ⟩, t, ht, hcv⟩

end Work.WilG4c
