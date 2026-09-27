import Mathlib

namespace Work.Isotopy

open scoped Manifold ContDiff
open Topology Set Function Filter

theorem exists_global_retraction {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]
    (O : Set ℝ) (W : Set (EuclideanSpace ℝ (Fin N))) (hO : IsOpen O) (hW : IsOpen W)
    (s₀ : ℝ) (w₀ : EuclideanSpace ℝ (Fin N)) (hs : s₀ ∈ O) (hw : w₀ ∈ W)
    (ρ : ℝ → EuclideanSpace ℝ (Fin N) → M)
    (hρ : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (Function.uncurry ρ) (O ×ˢ W)) :
    ∃ (O' : Set ℝ) (W' : Set (EuclideanSpace ℝ (Fin N)))
      (ρ' : ℝ → EuclideanSpace ℝ (Fin N) → M),
      IsOpen O' ∧ s₀ ∈ O' ∧ O' ⊆ O ∧ IsOpen W' ∧ w₀ ∈ W' ∧ W' ⊆ W ∧
      Bornology.IsBounded W' ∧
      ContMDiff ((modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (Function.uncurry ρ') ∧
      (∀ s ∈ O', ∀ w ∈ W', ρ' s w = ρ s w) := by
  classical
  -- ## Notation
  let p₀ : M := ρ s₀ w₀
  let e : PartialEquiv M (EuclideanSpace ℝ (Fin n)) := extChartAt (𝓡 n) p₀
  let ρu : ℝ × EuclideanSpace ℝ (Fin N) → M := Function.uncurry ρ
  -- the region on which `e ∘ ρ` is smooth
  let V : Set (ℝ × EuclideanSpace ℝ (Fin N)) :=
    (O ×ˢ W) ∩ ρu ⁻¹' (extChartAt (𝓡 n) p₀).source
  have hVdef : V = (O ×ˢ W) ∩ ρu ⁻¹' (extChartAt (𝓡 n) p₀).source := rfl
  have hρc : ContinuousOn ρu (O ×ˢ W) := hρ.continuousOn
  -- ## `V` is open
  have hVopen : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    rw [hVdef] at hp ⊢
    refine inter_mem ((hO.prod hW).mem_nhds hp.1) ?_
    exact ContinuousAt.preimage_mem_nhds
      (hρc.continuousAt ((hO.prod hW).mem_nhds hp.1))
      ((isOpen_extChartAt_source (I := 𝓡 n) p₀).mem_nhds hp.2)
  have hqV : (s₀, w₀) ∈ V := by
    rw [hVdef]
    exact ⟨⟨hs, hw⟩, mem_extChartAt_source (I := 𝓡 n) p₀⟩
  -- ## A radius on which the chart is defined
  obtain ⟨δ, hδpos, hδball⟩ : ∃ δ > 0, Metric.ball (e p₀) δ ⊆ e.target :=
    (Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := 𝓡 n) p₀)) (e p₀)
      (mem_extChartAt_target (I := 𝓡 n) p₀)
  -- ## A product neighbourhood of `(s₀, w₀)` on which everything is good
  have hρu_cont : ContinuousAt ρu (s₀, w₀) :=
    hρc.continuousAt ((hO.prod hW).mem_nhds ⟨hs, hw⟩)
  have he_cont : ContinuousAt (fun x : M => e x) p₀ :=
    (contMDiffAt_extChartAt (I := 𝓡 n) (n := ∞) (x := p₀)).continuousAt
  have hge_cont : ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin N) => e (ρu p)) (s₀, w₀) :=
    ContinuousAt.comp (f := ρu) (g := fun x : M => e x) (x := (s₀, w₀))
      he_cont hρu_cont
  have hU_mem : V ∩ (fun p : ℝ × EuclideanSpace ℝ (Fin N) => e (ρu p)) ⁻¹'
        Metric.ball (e p₀) δ ∈ 𝓝 (s₀, w₀) :=
    inter_mem (hVopen.mem_nhds hqV)
      (hge_cont.preimage_mem_nhds
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδpos)))
  obtain ⟨U₀, hU₀sub, hU₀open, hqU₀⟩ := mem_nhds_iff.mp hU_mem
  obtain ⟨u, v, huopen, hvopen, hsu, hwv, huv⟩ :=
    (isOpen_prod_iff.mp hU₀open) s₀ w₀ hqU₀
  obtain ⟨ε, hεpos, hεu⟩ : ∃ ε > 0, Metric.ball s₀ ε ⊆ u :=
    Metric.isOpen_iff.mp huopen s₀ hsu
  obtain ⟨ε', hε'pos, hε'v⟩ : ∃ ε' > 0, Metric.ball w₀ ε' ⊆ v :=
    Metric.isOpen_iff.mp hvopen w₀ hwv
  -- ## The cut-off function
  let φ : ContDiffBump s₀ := ContDiffBump.mk (ε / 4) (ε / 2) (by linarith) (by linarith)
  let ψ : ContDiffBump w₀ := ContDiffBump.mk (ε' / 4) (ε' / 2) (by linarith) (by linarith)
  let β : ℝ × EuclideanSpace ℝ (Fin N) → ℝ := fun p => φ p.1 * ψ p.2
  have hφrIn : φ.rIn = ε / 4 := rfl
  have hφrOut : φ.rOut = ε / 2 := rfl
  have hψrIn : ψ.rIn = ε' / 4 := rfl
  have hψrOut : ψ.rOut = ε' / 2 := rfl
  have hβnn : ∀ p, 0 ≤ β p := fun p => mul_nonneg (φ.nonneg) (ψ.nonneg)
  have hβle : ∀ p, β p ≤ 1 := fun p => by
    show φ p.1 * ψ p.2 ≤ 1
    calc φ p.1 * ψ p.2 ≤ 1 * 1 := mul_le_mul (φ.le_one) (ψ.le_one) (ψ.nonneg) (by norm_num)
      _ = 1 := by norm_num
  have hβone : ∀ s ∈ Metric.ball s₀ φ.rIn, ∀ w ∈ Metric.ball w₀ ψ.rIn,
      β (s, w) = 1 := by
    intro s hs' w hw'
    have h1 : φ s = 1 := φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hs')
    have h2 : ψ w = 1 := ψ.one_of_mem_closedBall (Metric.ball_subset_closedBall hw')
    show φ s * ψ w = 1
    rw [h1, h2, mul_one]
  -- the support of `β` sits inside the good region
  have hsuppK : Function.support β ⊆
      Metric.closedBall s₀ (ε / 2) ×ˢ Metric.closedBall w₀ (ε' / 2) := by
    intro p hp
    have hp' : φ p.1 * ψ p.2 ≠ 0 := hp
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hp'
    refine mem_prod.mpr ⟨?_, ?_⟩
    · have hh : p.1 ∈ Function.support φ := Function.mem_support.mpr h1
      rw [ContDiffBump.support_eq, hφrOut] at hh
      exact Metric.ball_subset_closedBall hh
    · have hh : p.2 ∈ Function.support ψ := Function.mem_support.mpr h2
      rw [ContDiffBump.support_eq, hψrOut] at hh
      exact Metric.ball_subset_closedBall hh
  have hKU : Metric.closedBall s₀ (ε / 2) ×ˢ Metric.closedBall w₀ (ε' / 2) ⊆ U₀ := by
    intro p hp
    obtain ⟨h1, h2⟩ := mem_prod.mp hp
    exact huv (mem_prod.mpr ⟨hεu (Metric.closedBall_subset_ball (by linarith) h1),
      hε'v (Metric.closedBall_subset_ball (by linarith) h2)⟩)
  have hclosV : closure (Function.support β) ⊆ V := by
    refine subset_trans (closure_minimal hsuppK
      (Metric.isClosed_closedBall.prod Metric.isClosed_closedBall)) ?_
    intro p hp
    exact (hU₀sub (hKU hp)).1
  have hgood : ∀ p, β p ≠ 0 →
      ρu p ∈ e.source ∧ e (ρu p) ∈ Metric.ball (e p₀) δ := by
    intro p hp
    have hpU : p ∈ V ∩ (fun p : ℝ × EuclideanSpace ℝ (Fin N) => e (ρu p)) ⁻¹'
        Metric.ball (e p₀) δ := hU₀sub (hKU (hsuppK (Function.mem_support.mpr hp)))
    have hpV : p ∈ V := hpU.1
    rw [hVdef] at hpV
    exact ⟨hpV.2, hpU.2⟩
  -- ## Smoothness of `e ∘ ρ` on `V`
  have hVsubOW : V ⊆ O ×ˢ W := by
    intro p hp; rw [hVdef] at hp; exact hp.1
  have hρV : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓡 n) ∞ ρu V := hρ.mono hVsubOW
  have hsrc : e.source ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) p₀).source := by
    intro x hx
    rw [← extChartAt_source (𝓡 n) p₀]
    exact hx
  have hchart : ContMDiffOn (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun x : M => e x)
      e.source :=
    (contMDiffOn_extChartAt (I := 𝓡 n) (n := ∞) (x := p₀)).mono hsrc
  have hgV : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 N)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin N) => e (ρu p)) V :=
    hchart.comp hρV (fun p hp => by rw [hVdef] at hp; exact hp.2)
  -- ## The cut-off function is smooth
  have hβ : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) 𝓘(ℝ, ℝ) ∞ β := by
    have hf : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) 𝓘(ℝ, ℝ) ∞
        (Prod.fst : ℝ × EuclideanSpace ℝ (Fin N) → ℝ) :=
      contMDiff_fst (I := 𝓘(ℝ, ℝ)) (J := 𝓡 N)
    have hg : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓡 N) ∞
        (Prod.snd : ℝ × EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) :=
      contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := 𝓡 N)
    have h1 : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => φ p.1) :=
      ((φ.contDiff (n := ⊤)).contMDiff).comp hf
    have h2 : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => ψ p.2) :=
      ((ψ.contDiff (n := ⊤)).contMDiff).comp hg
    show ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin N) => φ p.1 * ψ p.2)
    exact h1.mul h2
  -- ## The globally smooth extension `F` in chart coordinates
  let g : ℝ × EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n) := fun p => e (ρu p)
  let F : ℝ × EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n) :=
    fun p => e p₀ + β p • (g p - e p₀)
  have hFV : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 N)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ F V := by
    intro x hx
    have hgx : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓡 N)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g V x := hgV x hx
    have hβx : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓡 N)) 𝓘(ℝ, ℝ) ∞ β V x := (hβ.contMDiffAt).contMDiffWithinAt
    have h2 : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓡 N)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (fun y => g y - e p₀) V x := hgx.sub contMDiffWithinAt_const
    have h3 : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓡 N)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (fun y => β y • (g y - e p₀)) V x := hβx.smul h2
    exact contMDiffWithinAt_const.add h3
  have hFW : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 N)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ F
      (closure (Function.support β))ᶜ := by
    refine ContMDiffOn.congr (contMDiffOn_const (c := e p₀)) (fun y hy => ?_)
    have hyβ : β y = 0 := by
      by_contra h
      exact hy (subset_closure (Function.mem_support.mpr h))
    show e p₀ + β y • (g y - e p₀) = e p₀
    rw [hyβ, zero_smul, add_zero]
  have hWopen : IsOpen (closure (Function.support β))ᶜ := isClosed_closure.isOpen_compl
  have hFglob : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ F := by
    intro x
    by_cases hx : x ∈ V
    · exact hFV.contMDiffAt (hVopen.mem_nhds hx)
    · exact hFW.contMDiffAt (hWopen.mem_nhds (fun h => hx (hclosV h)))
  -- ## `F` takes values in the chart target
  have hFtarget : ∀ p, F p ∈ e.target := by
    intro p
    by_cases hp : β p = 0
    · have hconst : F p = e p₀ := by
        show e p₀ + β p • (g p - e p₀) = e p₀
        rw [hp, zero_smul, add_zero]
      rw [hconst]
      exact mem_extChartAt_target (I := 𝓡 n) p₀
    · obtain ⟨-, hball⟩ := hgood p hp
      have hdist : dist (g p) (e p₀) < δ := Metric.mem_ball.mp hball
      have hd : ‖g p - e p₀‖ < δ := by rwa [dist_eq_norm] at hdist
      have hnorm : ‖F p - e p₀‖ < δ := by
        have hFeq : F p - e p₀ = β p • (g p - e p₀) := by
          show (e p₀ + β p • (g p - e p₀)) - e p₀ = β p • (g p - e p₀)
          abel
        rw [hFeq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hβnn p)]
        calc β p * ‖g p - e p₀‖ ≤ 1 * ‖g p - e p₀‖ :=
              mul_le_mul_of_nonneg_right (hβle p) (norm_nonneg _)
          _ = ‖g p - e p₀‖ := one_mul _
          _ < δ := hd
      exact hδball (Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hnorm))
  -- ## Smoothness of the composed map
  have hsymm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞
      (fun x : EuclideanSpace ℝ (Fin n) => e.symm x) e.target :=
    contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) p₀
  have hFin : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 N)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ F univ :=
    contMDiffOn_univ.mpr hFglob
  have hcomp : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓡 n) ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin N) => e.symm (F p)) univ :=
    hsymm.comp hFin (fun p _ => hFtarget p)
  have hρ'glob : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓡 n) ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin N) => e.symm (F p)) := contMDiffOn_univ.mp hcomp
  -- ## Assembly
  have huncurry : Function.uncurry (fun s w => e.symm (F (s, w))) =
      fun p : ℝ × EuclideanSpace ℝ (Fin N) => e.symm (F p) := by
    funext p
    cases p
    rfl
  refine ⟨Metric.ball s₀ φ.rIn, Metric.ball w₀ ψ.rIn, (fun s w => e.symm (F (s, w))),
    Metric.isOpen_ball, Metric.mem_ball_self φ.rIn_pos, ?_, Metric.isOpen_ball,
    Metric.mem_ball_self ψ.rIn_pos, ?_, Metric.isBounded_ball, ?_, ?_⟩
  · intro s hs'
    have hs4 : s ∈ Metric.ball s₀ (ε / 4) := by rwa [hφrIn] at hs'
    have hsu' : s ∈ u := hεu (Metric.ball_subset_ball (by linarith) hs4)
    have hsw : (s, w₀) ∈ V := (hU₀sub (huv (mem_prod.mpr ⟨hsu', hwv⟩))).1
    rw [hVdef] at hsw
    exact (mem_prod.mp hsw.1).1
  · intro w hw'
    have hw4 : w ∈ Metric.ball w₀ (ε' / 4) := by rwa [hψrIn] at hw'
    have hwv' : w ∈ v := hε'v (Metric.ball_subset_ball (by linarith) hw4)
    have hsw : (s₀, w) ∈ V := (hU₀sub (huv (mem_prod.mpr ⟨hsu, hwv'⟩))).1
    rw [hVdef] at hsw
    exact (mem_prod.mp hsw.1).2
  · rw [huncurry]
    exact hρ'glob
  · intro s hs' w hw'
    have hβ1 : β (s, w) = 1 := hβone s hs' w hw'
    have hs4 : s ∈ Metric.ball s₀ (ε / 4) := by rwa [hφrIn] at hs'
    have hw4 : w ∈ Metric.ball w₀ (ε' / 4) := by rwa [hψrIn] at hw'
    have hsu' : s ∈ u := hεu (Metric.ball_subset_ball (by linarith) hs4)
    have hwv' : w ∈ v := hε'v (Metric.ball_subset_ball (by linarith) hw4)
    have hswU : (s, w) ∈ U₀ := huv (mem_prod.mpr ⟨hsu', hwv'⟩)
    have hswV : (s, w) ∈ V := (hU₀sub hswU).1
    rw [hVdef] at hswV
    have hsrcm : ρu (s, w) ∈ e.source := hswV.2
    have hFsw : F (s, w) = e (ρu (s, w)) := by
      show e p₀ + β (s, w) • (g (s, w) - e p₀) = e (ρu (s, w))
      rw [hβ1, one_smul]
      abel
    show e.symm (F (s, w)) = ρ s w
    rw [hFsw, PartialEquiv.left_inv e hsrcm]
    rfl

end Work.Isotopy
