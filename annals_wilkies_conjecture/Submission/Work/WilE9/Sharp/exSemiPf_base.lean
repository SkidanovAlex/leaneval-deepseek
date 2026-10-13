import Mathlib
import Submission.Work.WilE9.Sharp.Vocab
import Submission.Work.WilE9.Sharp.graph_rel
import Submission.Work.WilE9.Sharp.ExSndAux
import Submission.Work.WilE9.Sharp.eaEval_exRaise
import Submission.Work.WilE9.Psi.psi_psiInv
import Submission.Work.WilE9.Sharp.AE.exStrat_mem

set_option autoImplicit false
noncomputable section
namespace Work.WilE9.Sharp

open WilkiesDesign WilkiesDesign.E

/-! ## The stratum coordinates of a point of the extended ambient

`exStrat z` reads a point `z` of the extended ambient `ℝ^{Next n m}` in the stratum's own
coordinates `(y, τ, aux)`.  The two lemmas below locate the stratum's coordinates inside the
extended ambient, and the last one computes the projection `stratProj` of `exStrat z`: it is
`Fin.snoc` of the `y`-coordinates and `τ`. -/

theorem sIdxE_lt {n m : ℕ} (i : Fin (n + (1 + m))) (hi : (i : ℕ) < n) :
    sIdxE n m i = exY n m ⟨(i : ℕ), hi⟩ := by
  simp only [sIdxE]
  rw [dif_pos hi]

theorem sIdxE_last {n m : ℕ} (i : Fin (n + (1 + m))) (hi : (i : ℕ) = n) :
    sIdxE n m i = exT n m := by
  simp only [sIdxE]
  rw [dif_neg (by omega), dif_pos hi]

theorem stratProj_exStrat {n m : ℕ} (z : Fin (Next n m) → ℝ) :
    stratProj (exStrat z) = Fin.snoc (fun i : Fin n => z (exY n m i)) (z (exT n m)) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.snoc_last, stratProj_apply]
    show exStrat z ⟨(Fin.last n : ℕ), by omega⟩ = z (exT n m)
    simp only [exStrat]
    congr 1
    exact sIdxE_last _ (by simp)
  · intro j
    rw [Fin.snoc_castSucc, stratProj_apply]
    show exStrat z ⟨(Fin.castSucc j : ℕ), by omega⟩ = z (exY n m j)
    simp only [exStrat]
    congr 1
    exact sIdxE_lt _ (by simpa using j.isLt)

/-- `psiV` is a left inverse of `psiInvV` on the open cube. -/
theorem psiV_psiInvV {n : ℕ} {y : Fin n → ℝ} (hy : ∀ i, |y i| < 1) :
    WilkiesDesign.E.psiV (Work.WilE9.Sharp.psiInvV y) = y := by
  funext i
  simp only [WilkiesDesign.E.psiV, Work.WilE9.Sharp.psiInvV]
  exact Work.WilE9.Psi.psi_psiInv (y i) (hy i)

theorem exSemiPf_base_gen {n m : ℕ} {f : (Fin n → ℝ) → ℝ} {Z : Set (Fin (n + 1) → ℝ)}
    (hZ : WilkiesDesign.graphOf f = WilkiesDesign.E.psiV ⁻¹' Z)
    (E : Work.WilE9.Sharp.EffStratum n m) (Q : Set (Fin (n + (1 + m)) → ℝ))
    (hπ : ∀ w ∈ Q, Work.WilE9.Sharp.stratProj w ∈ Z)
    (L : List (Fin n)) (y : Fin n → ℝ) (σ : ℝ)
    (h : ∃ z ∈ (Work.WilE9.Sharp.exSemiPf n m E L).set,
      Work.WilE9.Sharp.exOut z = Fin.snoc y σ ∧ Work.WilE9.Sharp.exStrat z ∈ Q) :
    (∀ i : Fin n, |y i| < 1) ∧
      ∃ w ∈ Q, Work.WilE9.Sharp.stratProj w =
        Fin.snoc (WilkiesDesign.E.psiV (Work.WilE9.Sharp.psiInvV y))
          (WilkiesDesign.E.psi (f (Work.WilE9.Sharp.psiInvV y))) := by
  obtain ⟨z, hzmem, hzout, hzQ⟩ := h
  -- the stratum coordinates of `z` lie in `E.X.set`, and by hypothesis in `Q`
  have hXmem0 : exStrat z ∈ E.X.set := exStrat_mem_of_mem_exSemiPf E L hzmem
  obtain ⟨hzcube, B, hBmem, hB⟩ := hzmem
  obtain ⟨B0, hB0mem, hB0eq⟩ := List.mem_map.mp hBmem
  rw [← hB0eq] at hB
  obtain ⟨hBeqs, hBpos⟩ := hB
  -- the `y`-coordinates of `z`
  have hy : ∀ i : Fin n, z (exY n m i) = y i := fun i => by
    have h1 := congrFun hzout (Fin.castSucc i)
    rw [Fin.snoc_castSucc] at h1
    change z (Fin.castAdd (n + m + 3) (Fin.castSucc i)) = y i at h1
    rw [exY_eq_castAdd]
    exact h1
  -- the extended equations and inequalities hold at `z`
  have hBeq : ∀ g ∈ exEqList E.X.c E.h L, eaEval (exChain E.X.c) g z = 0 := fun g hg =>
    hBeqs g (show g ∈ (exBasic E.X.c E.h L B0).eqs from
      List.mem_append.mpr (Or.inl hg))
  have hBpo : ∀ g ∈ exPosList (n := n) (m := m) (r := E.X.r) B0,
      0 < eaEval (exChain E.X.c) g z := fun g hg =>
    hBpos g (show g ∈ (exBasic E.X.c E.h L B0).pos from hg)
  have hyw : ∀ i, z (exY n m i) ^ 2 + z (exW n m i) ^ 2 = 1 := fun i => by
    have h1 := hBeq _ (mem_exEqList_yw E.X.c E.h L i)
    simp only [eaEval_sub, eaEval_add, eaEval_pow, eaEval_X_inl, eaEval_one] at h1
    linarith
  have htu : z (exT n m) ^ 2 + z (exU n m) ^ 2 = 1 := by
    have h1 := hBeq _ (mem_exEqList_tu E.X.c E.h L)
    simp only [eaEval_sub, eaEval_add, eaEval_pow, eaEval_X_inl, eaEval_one] at h1
    linarith
  have hwpos : ∀ i, 0 < z (exW n m i) := fun i => by
    have h1 := hBpo _ (mem_exPosList_w B0 i)
    simpa only [eaEval_X_inl] using h1
  have hupos : 0 < z (exU n m) := by
    have h1 := hBpo _ (mem_exPosList_u B0)
    simpa only [eaEval_X_inl] using h1
  -- the strict inequalities
  have hy_lt : ∀ i : Fin n, |y i| < 1 := fun i => by
    have h2 : z (exY n m i) ^ 2 < 1 := by linarith [hyw i, pow_pos (hwpos i) 2]
    rw [← hy i]
    exact (sq_lt_one_iff_abs_lt_one _).mp h2
  have hτ_lt : |z (exT n m)| < 1 := by
    have h2 : z (exT n m) ^ 2 < 1 := by linarith [htu, pow_pos hupos 2]
    exact (sq_lt_one_iff_abs_lt_one _).mp h2
  -- the stratum point `exStrat z` lies in `E.X.set` (and hence, by hypothesis, in `Q`)
  have hXmem : exStrat z ∈ E.X.set := hXmem0
  -- the projection of `exStrat z`
  have hyfun : (fun i : Fin n => z (exY n m i)) = y := funext hy
  have hpsiV : WilkiesDesign.E.psiV (Work.WilE9.Sharp.psiInvV y) = y := psiV_psiInvV hy_lt
  have hstratfun : stratProj (exStrat z) =
      Fin.snoc (WilkiesDesign.E.psiV (Work.WilE9.Sharp.psiInvV y)) (z (exT n m)) := by
    rw [stratProj_exStrat, hyfun, hpsiV]
  -- its projection lies in `Z`, so the graph relation pins `τ`
  have hZmem : Fin.snoc (WilkiesDesign.E.psiV (Work.WilE9.Sharp.psiInvV y)) (z (exT n m)) ∈ Z :=
    hstratfun ▸ hπ _ hzQ
  have hτ : z (exT n m) = WilkiesDesign.E.psi (f (Work.WilE9.Sharp.psiInvV y)) :=
    graph_rel hZ hτ_lt hZmem
  refine ⟨hy_lt, exStrat z, hzQ, ?_⟩
  rw [hstratfun, hτ]

/-- The unrestricted statement, the instance `Q = E.X.set` of `exSemiPf_base_gen`. -/
theorem exSemiPf_base {n m : ℕ} {f : (Fin n → ℝ) → ℝ} {Z : Set (Fin (n + 1) → ℝ)}
    (hZ : WilkiesDesign.graphOf f = WilkiesDesign.E.psiV ⁻¹' Z)
    (E : Work.WilE9.Sharp.EffStratum n m)
    (hπ : ∀ w ∈ E.X.set, Work.WilE9.Sharp.stratProj w ∈ Z)
    (L : List (Fin n)) (y : Fin n → ℝ) (σ : ℝ)
    (h : ∃ z ∈ (Work.WilE9.Sharp.exSemiPf n m E L).set,
      Work.WilE9.Sharp.exOut z = Fin.snoc y σ) :
    (∀ i : Fin n, |y i| < 1) ∧
      ∃ w ∈ E.X.set, Work.WilE9.Sharp.stratProj w =
        Fin.snoc (WilkiesDesign.E.psiV (Work.WilE9.Sharp.psiInvV y))
          (WilkiesDesign.E.psi (f (Work.WilE9.Sharp.psiInvV y))) := by
  obtain ⟨z, hzmem, hzout⟩ := h
  exact exSemiPf_base_gen hZ E E.X.set hπ L y σ
    ⟨z, hzmem, hzout, exStrat_mem_of_mem_exSemiPf E L hzmem⟩

end Work.WilE9.Sharp
