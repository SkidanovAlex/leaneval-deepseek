import Mathlib
import Submission.Work.WilG4c.StepLipHighAux
import Submission.Work.WilG4c.StepLipPieces
import Submission.Work.WilG4c.PiecePYLipOfChartPw
import Submission.Work.WilG4c.ExactChartDeriv
import Submission.Work.WilkG4c.YPullbackBound
import Submission.Work.WilG4c.GoodCellChartsGAux
import Submission.Work.WilG4c.SlicePrimaryLe

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- **The per-cell good branch.**  From the exact cell chart `χ` of the cell `κ` (its facts on
the parameter projection `PK`), the global smoothness of the `y`-chart `ψ`, the near-maximising
curve `γ` and the tuple `Tm`, the piece family `pieceFam (yPullback F ψ) (chartFun χ)` satisfies
the `PY` bounds and is Lipschitz (with the constant `Cpc`) on `PK`. -/
theorem GoodCellPieceData (S : WilkiesDesign.SOMin) (n p : ℕ)
    (Cpc : ℝ) (hCpc_ge : max (2 * ((n : ℝ) + 1)) 1 * ((n : ℝ) + 1) ≤ Cpc) :
    ∀ (κ : Set (Fin (p + 1) → ℝ)) (PK : Set (Fin p → ℝ))
      (k kt r D : ℕ) (hr : 1 ≤ r)
      (F : Work.WilkG4c.Family k p (n + 1)) (ψ : Work.WilkG4c.ChartTuple (p + 1) n)
      (χ : Work.WilkG4c.ChartTuple p 1)
      (Tm : Fin kt → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ)
      (γ : Fin k → (Fin p → ℝ) → ℝ → (Fin n → ℝ)),
      (∀ i, ∀ l, ∀ x ∈ Work.WilkG4c.I, ∀ m, m ≤ r →
          ∀ t ∈ WilkiesDesign.openCube n,
          ‖iteratedFDeriv ℝ m (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t))) t‖ ≤ 1) →
      (∀ l ∈ PK, ∀ t ∈ WilkiesDesign.openCube 1,
          χ 0 l t ∈ Set.Ioo (0 : ℝ) 1 ∧ Fin.snoc l (χ 0 l t) ∈ κ) →
      (∀ a : Fin kt, ∀ l ∈ PK, ∀ τ ∈ Set.Ioo (0 : ℝ) 1,
          DifferentiableAt ℝ (fun τ' : ℝ => Tm a l (fun _ => χ 0 l (fun _ => τ'))) τ ∧
          |deriv (fun τ' : ℝ => Tm a l (fun _ => χ 0 l (fun _ => τ'))) τ| ≤ 1) →
      (∃ a : Fin kt, ∀ l u, Tm a l u = u 0) →
      (∀ i l x, Work.WilkG4c.NearMax (Work.WilkG4c.yPullback F ψ i) l x →
          γ i l x ∈ WilkiesDesign.openCube n ∧
          Work.WilkG4c.xPt l x (γ i l x) ∈
            interior {z | ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat (Work.WilkG4c.yPullback F ψ i)) z} ∧
          ∀ y' ∈ WilkiesDesign.openCube n,
            Work.WilkG4c.xPt l x y' ∈
              interior {z | ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat (Work.WilkG4c.yPullback F ψ i)) z} →
            |Work.WilkG4c.xDeriv (Work.WilkG4c.yPullback F ψ i) l x y'| ≤
              2 * |Work.WilkG4c.xDeriv (Work.WilkG4c.yPullback F ψ i) l x (γ i l x)|) →
      (∀ i, Disjoint κ (Work.WilkG4c.badCurve (Work.WilkG4c.yPullback F ψ i))) →
      (∀ i, κ ⊆ Work.WilkG4c.C1All (Work.WilkG4c.yPullback F ψ i)) →
      (∀ a : Fin kt, ∀ w ∈ κ,
          ContDiffAt ℝ 1 (fun z : Fin (p + 1) → ℝ => Tm a (Fin.init z) (fun _ => z (Fin.last p))) w) →
      (∀ i, ∃ a : Fin kt, ∀ l u,
          Tm a l u = Work.WilkG4c.yPullback F ψ i l (Fin.cons (u 0) (γ i l (u 0)))) →
      (∀ i j, ∃ a : Fin kt, ∀ l u, Tm a l u = γ i l (u 0) j) →
      (∀ i j, ∀ w ∈ κ, DifferentiableAt ℝ (fun s : ℝ => γ i (Fin.init w) s j) (w (Fin.last p))) →
      (∀ i, ∀ l ∈ PK, ∀ t ∈ Work.WilkG4c.I, ∀ m, m ≤ r →
          ∀ y ∈ WilkiesDesign.openCube n,
          ‖iteratedFDeriv ℝ m (Work.WilkG4c.slice (Work.WilkG4c.pieceFam
            (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ) i l) t) y‖ ≤ 1) ∧
      (∀ i l, l ∈ PK → ∀ z ∈ WilkiesDesign.openCube (n + 1),
          ∀ z' ∈ WilkiesDesign.openCube (n + 1),
          |Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ) i l z
            - Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ) i l z'|
          ≤ Cpc * dist z z') := by
  intro κ PK k kt r D hr F ψ χ Tm γ hψnm hχmem hχdiff hid hγmax hκbad hκC1 hTsm hcx hγx hγd
  have hφI : ∀ l ∈ PK, ∀ t ∈ Work.WilkG4c.I, Work.WilG4c.chartFun χ l t ∈ Work.WilkG4c.I := by
    intro l hl t ht
    have ht' : (fun _ : Fin 1 => t) ∈ WilkiesDesign.openCube 1 := by
      intro j; exact ht
    exact (hχmem l hl (fun _ : Fin 1 => t) ht').1
  have hφfib : ∀ l ∈ PK, ∀ t ∈ Work.WilkG4c.I,
      Fin.snoc l (Work.WilG4c.chartFun χ l t) ∈ κ := by
    intro l hl t ht
    have ht' : (fun _ : Fin 1 => t) ∈ WilkiesDesign.openCube 1 := by
      intro j; exact ht
    exact (hχmem l hl (fun _ : Fin 1 => t) ht').2
  obtain ⟨a0id, ha0id⟩ := hid
  have hφdb : ∀ l ∈ PK, ∀ t ∈ Work.WilkG4c.I,
      DifferentiableAt ℝ (Work.WilG4c.chartFun χ l) t ∧
        |deriv (Work.WilG4c.chartFun χ l) t| ≤ 1 :=
    Work.WilG4c.chartFun_diff Tm a0id ha0id χ (fun l hl τ hτ => hχdiff a0id l hl τ hτ)
  have hφd : ∀ l ∈ PK, ∀ t ∈ Work.WilkG4c.I,
      DifferentiableAt ℝ (Work.WilG4c.chartFun χ l) t :=
    fun l hl t ht => (hφdb l hl t ht).1
  have hφb : ∀ l ∈ PK, ∀ t ∈ Work.WilkG4c.I, |deriv (Work.WilG4c.chartFun χ l) t| ≤ 1 :=
    fun l hl t ht => (hφdb l hl t ht).2
  -- ## the piece data
  have hYpk : ∀ i, ∀ l ∈ PK, ∀ t ∈ Work.WilkG4c.I, ∀ m, m ≤ r →
      ∀ y ∈ WilkiesDesign.openCube n,
      ‖iteratedFDeriv ℝ m (Work.WilkG4c.slice (Work.WilkG4c.yPullback F ψ i l)
        (Work.WilG4c.chartFun χ l t)) y‖ ≤ 1 := by
    intro i l hl t ht m hm y hy
    rw [Work.WilkG4c.slice_yPullback]
    exact hψnm i l (Work.WilG4c.chartFun χ l t) (hφI l hl t ht) m hm y hy
  have hC1pk : ∀ i, ∀ l ∈ PK, ∀ t ∈ Work.WilkG4c.I, ∀ y ∈ WilkiesDesign.openCube n,
      ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat (Work.WilkG4c.yPullback F ψ i))
        (Work.WilkG4c.xPt l (Work.WilG4c.chartFun χ l t) y) := by
    intro i l hl t ht y hy
    have h := (Work.WilkG4c.c1All_iff (Work.WilkG4c.yPullback F ψ i) l
      (Work.WilG4c.chartFun χ l t)).mp (hκC1 i (hφfib l hl t ht)) y hy
    exact interior_subset h
  have hnm : ∀ i, ∀ l ∈ PK, ∀ t ∈ Work.WilkG4c.I,
      Work.WilkG4c.NearMax (Work.WilkG4c.yPullback F ψ i) l (Work.WilG4c.chartFun χ l t) := by
    intro i l hl t ht
    have hnot := Set.disjoint_left.mp (hκbad i) (hφfib l hl t ht)
    simp only [Work.WilkG4c.badCurve, Set.mem_ofPred_eq, not_not] at hnot
    simpa [Fin.snoc_castSucc, Fin.snoc_last] using hnot
  have hγcpk : ∀ i, ∀ l ∈ PK, ∀ t ∈ Work.WilkG4c.I,
      γ i l (Work.WilG4c.chartFun χ l t) ∈ WilkiesDesign.openCube n :=
    fun i l hl t ht => (hγmax i l (Work.WilG4c.chartFun χ l t) (hnm i l hl t ht)).1
  have hmaxp : ∀ i, ∀ l ∈ PK, ∀ t ∈ Work.WilkG4c.I, ∀ y ∈ WilkiesDesign.openCube n,
      |Work.WilkG4c.xDeriv (Work.WilkG4c.yPullback F ψ i) l (Work.WilG4c.chartFun χ l t) y| ≤
        2 * |Work.WilkG4c.xDeriv (Work.WilkG4c.yPullback F ψ i) l
          (Work.WilG4c.chartFun χ l t) (γ i l (Work.WilG4c.chartFun χ l t))| := by
    intro i l hl t ht y hy
    refine Work.WilkG4c.xDeriv_le_two_mul_of_c1All
      (hγmax i l (Work.WilG4c.chartFun χ l t) (hnm i l hl t ht)).2 ?_ y hy
    intro y' hy'
    exact (Work.WilkG4c.c1All_iff (Work.WilkG4c.yPullback F ψ i) l
      (Work.WilG4c.chartFun χ l t)).mp (hκC1 i (hφfib l hl t ht)) y' hy'
  have hyb : ∀ i, ∀ l ∈ PK, ∀ t ∈ Work.WilkG4c.I, ∀ y ∈ WilkiesDesign.openCube n,
      ∀ j : Fin n,
      |fderiv ℝ (Work.WilkG4c.famFunHat (Work.WilkG4c.yPullback F ψ i))
        (Work.WilkG4c.xPt l (Work.WilG4c.chartFun χ l t) y) (Pi.single (Fin.natAdd p j.succ) 1)| ≤ 1 :=
    fun i l hl t ht y hy j =>
      famFunHat_yDir_le_of_slice_norm (Work.WilkG4c.yPullback F ψ i) l
        (Work.WilG4c.chartFun χ l t) y (hYpk i l hl t ht 1 hr y hy) j
  have hγdpk : ∀ i, ∀ j : Fin n, ∀ l ∈ PK, ∀ t ∈ Work.WilkG4c.I,
      DifferentiableAt ℝ (fun s : ℝ => γ i l s j) (Work.WilG4c.chartFun χ l t) := by
    intro i j l hl t ht
    have h := hγd i j (Fin.snoc l (Work.WilG4c.chartFun χ l t)) (hφfib l hl t ht)
    simpa [Fin.init_snoc, Fin.snoc_last] using h
  have hγφ : ∀ i, ∀ j : Fin n, ∀ l ∈ PK, ∀ t ∈ Work.WilkG4c.I,
      |deriv (fun τ : ℝ => γ i l (Work.WilG4c.chartFun χ l τ) j) t| ≤ 1 := by
    intro i j l hl t ht
    obtain ⟨aγ, haγ⟩ := hγx i j
    have h := (hχdiff aγ l hl t ht).2
    have hfun : (fun τ' : ℝ => Tm aγ l (fun _ : Fin 1 => χ 0 l (fun _ => τ')))
        = (fun τ' : ℝ => γ i l (Work.WilG4c.chartFun χ l τ') j) := by
      funext τ'
      rw [haγ l (fun _ : Fin 1 => χ 0 l (fun _ => τ'))]
      simp only [Work.WilG4c.chartFun_apply]
    rwa [hfun] at h
  have hcφ : ∀ i, ∀ l ∈ PK, ∀ t ∈ Work.WilkG4c.I,
      |deriv (fun τ : ℝ => Work.WilkG4c.yPullback F ψ i l
        (Fin.cons (Work.WilG4c.chartFun χ l τ) (γ i l (Work.WilG4c.chartFun χ l τ)))) t| ≤ 1 := by
    intro i l hl t ht
    obtain ⟨ac, hac⟩ := hcx i
    have h := (hχdiff ac l hl t ht).2
    have hfun : (fun τ' : ℝ => Tm ac l (fun _ : Fin 1 => χ 0 l (fun _ => τ')))
        = (fun τ' : ℝ => Work.WilkG4c.yPullback F ψ i l
            (Fin.cons (Work.WilG4c.chartFun χ l τ') (γ i l (Work.WilG4c.chartFun χ l τ')))) := by
      funext τ'
      rw [hac l (fun _ : Fin 1 => χ 0 l (fun _ => τ'))]
      simp only [Work.WilG4c.chartFun_apply]
    rwa [hfun] at h
  have hfd : ∀ i, ∀ l ∈ PK, ∀ t ∈ Work.WilkG4c.I,
      DifferentiableAt ℝ (fun s : ℝ => Work.WilkG4c.yPullback F ψ i l
        (Fin.cons s (γ i l s))) (Work.WilG4c.chartFun χ l t) := by
    intro i l hl t ht
    obtain ⟨ac, hac⟩ := hcx i
    have hsm := hTsm ac (Fin.snoc l (Work.WilG4c.chartFun χ l t)) (hφfib l hl t ht)
    have hg : DifferentiableAt ℝ (fun s : ℝ => (Fin.snoc l s : Fin (p + 1) → ℝ))
        (Work.WilG4c.chartFun χ l t) := by
      refine differentiableAt_pi.mpr (fun j => ?_)
      induction j using Fin.lastCases with
      | last => simpa using differentiableAt_id
      | cast i => simpa using differentiableAt_const (c := l i)
    have hd : DifferentiableAt ℝ ((fun z : Fin (p + 1) → ℝ =>
        Tm ac (Fin.init z) (fun _ => z (Fin.last p)))
        ∘ (fun s : ℝ => (Fin.snoc l s : Fin (p + 1) → ℝ))) (Work.WilG4c.chartFun χ l t) :=
      DifferentiableAt.comp (Work.WilG4c.chartFun χ l t) hsm.differentiableAt_one hg
    have hfun : ((fun z : Fin (p + 1) → ℝ => Tm ac (Fin.init z) (fun _ => z (Fin.last p)))
        ∘ (fun s : ℝ => (Fin.snoc l s : Fin (p + 1) → ℝ)))
        = (fun s : ℝ => Work.WilkG4c.yPullback F ψ i l (Fin.cons s (γ i l s))) := by
      funext s
      simp only [Function.comp_apply]
      rw [hac]
      simp [Fin.init_snoc, Fin.snoc_last]
    rwa [hfun] at hd
  have hγb : ∀ i, ∀ l ∈ PK, ∀ t ∈ Work.WilkG4c.I, ∀ j : Fin n,
      |deriv (fun s : ℝ => γ i l s j) (Work.WilG4c.chartFun χ l t)| *
        |deriv (Work.WilG4c.chartFun χ l) t| ≤ 1 := by
    intro i l hl t ht j
    refine deriv_mul_le_of_comp (hγdpk i j l hl t ht) (hφd l hl t ht) ?_
    rw [show (fun s : ℝ => γ i l s j) ∘ (Work.WilG4c.chartFun χ l)
        = (fun τ : ℝ => γ i l (Work.WilG4c.chartFun χ l τ) j) from rfl]
    exact hγφ i j l hl t ht
  have hcb : ∀ i, ∀ l ∈ PK, ∀ t ∈ Work.WilkG4c.I,
      |deriv (fun s : ℝ => Work.WilkG4c.yPullback F ψ i l (Fin.cons s (γ i l s)))
          (Work.WilG4c.chartFun χ l t)| *
        |deriv (Work.WilG4c.chartFun χ l) t| ≤ 1 := by
    intro i l hl t ht
    refine deriv_mul_le_of_comp (hfd i l hl t ht) (hφd l hl t ht) ?_
    rw [show (fun s : ℝ => Work.WilkG4c.yPullback F ψ i l (Fin.cons s (γ i l s)))
        ∘ (Work.WilG4c.chartFun χ l)
        = (fun τ : ℝ => Work.WilkG4c.yPullback F ψ i l
            (Fin.cons (Work.WilG4c.chartFun χ l τ) (γ i l (Work.WilG4c.chartFun χ l τ))))
        from rfl]
    exact hcφ i l hl t ht
  obtain ⟨hYpiece, hLpiece⟩ :=
    Work.WilG4c.PiecePYLipOfChartPw PK (Work.WilkG4c.yPullback F ψ) γ
      (Work.WilG4c.chartFun χ) Cpc hCpc_ge hφI hφd hφb hYpk hC1pk hyb hmaxp hγcpk hγdpk
      hγb hfd hcb
  exact ⟨hYpiece, hLpiece⟩

end Work.WilG4c
