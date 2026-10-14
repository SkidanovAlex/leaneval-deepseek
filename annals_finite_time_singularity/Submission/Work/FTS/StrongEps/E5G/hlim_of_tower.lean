import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E5Aux3.contDiffOn_two_E_of_EllLimOK3
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.E5G.epsWP_tendsto_tower
import Submission.Work.FTS.StrongEps.E5G.muDyn_lamDyn_tendsto_tower
import Submission.Work.FTS.StrongEps.E5G.weak_slots_tendsto_open
import Submission.Work.FTS.StrongEps.EpsHlim4
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam
import Submission.Work.FTS.StrongEps.smoothOpen_epsWP
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS_EllLimOK.ProducerH.pzIterTwo_shiftSing_eq_PhiTil_add
import Submission.Work.FTS_RegExport.THL.L.DzDthSG_C1Jet_of_inputs
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice)

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

theorem hlim_of_tower {α C₀ Ce Cs T : ℝ} {K' : ℕ → ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {e : ℕ → ℝ} {G : ℕ → ℕ → Work.FTS.Galerkin.Fam} {Maj : ℕ → ℝ → ℝ}
    {ι : ℕ → ℕ → ℕ} {Fc : ℝ → Work.FTS.Galerkin.Fn}
    (n : ℕ) (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hc₁ : 1 / 10 ≤ Work.Spaces.c α) (hc₂ : Work.Spaces.c α ≤ 10)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hELL3 : Work.FTS.StrongEps.EllLimOK3 α E)
    (hsmΦ : ContDiffOn ℝ 1 (Function.uncurry Φs) Work.FTS.EllipticEst.Q0)
    (hL12g₀ : Work.Construction.L12 g₀ 0 = 0)
    (hεe : ∀ k : ℕ, e k ∈ Set.Ioc (0 : ℝ) 1)
    (hε0 : Filter.Tendsto e Filter.atTop (nhds 0))
    (hTower : ∀ n k : ℕ, n ≤ k → Work.FTS.StrongEps.E5G.TowerAt α C₀ ρ Φs E g₀ n (e k) (K' n) (G n k))
    (hMaj : ∀ n : ℕ, MeasureTheory.IntegrableOn (fun z => Maj n z / z) (Set.Ioi 0))
    (hDec : ∀ k : ℕ, n ≤ k → ∀ τ ∈ Set.Icc (0 : ℝ) (Work.FTS.StrongEps.E5G.Tn n),
      Work.FTS.StrongEps.EpsDecay α ρ Φs E (e k) τ (G n k) (Maj n))
    (hι : StrictMono (ι n)) (hadm : ∀ k : ℕ, n ≤ ι n k)
    (hconv : ∀ τ ∈ Set.Icc (0 : ℝ) (Work.FTS.StrongEps.E5G.Tn n),
      Work.FTS.StrongEps.ConvLocUnifH6 α (K' n) (fun k => Work.FTS.Galerkin.slice (G n (ι n k)) τ) (Fc τ))
    (hT : 0 < T) (hTT : T ≤ Work.FTS.StrongEps.E5G.Tn n) :
    ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → ∀ s ∈ Set.Icc (0 : ℝ) T,
      Filter.Tendsto (fun k : ℕ =>
          Work.FTS.StrongEps.epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s p.1 p.2)
        Filter.atTop (nhds (Work.FTS.StrongEps.rhsFun α Φs E (Work.FTS.StrongEps.clampQ Fc g₀) s p.1 p.2)) := by

  intro p hp s hs
  obtain ⟨hpz, hpθ0, hpθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have hpθ : p.2 ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hpθ0, hpθ1⟩
  -- ## the tower along the extraction
  have hTn : 0 < Tn n := Tn_pos n
  have hs' : s ∈ Set.Icc (0 : ℝ) (Tn n) := ⟨hs.1, le_trans hs.2 hTT⟩
  have htw : ∀ k : ℕ, TowerAt α C₀ ρ Φs E g₀ n (e (ι n k)) (K' n) (G n (ι n k)) :=
    fun k => hTower n (ι n k) (hadm k)
  have hεI : ∀ k : ℕ, e (ι n k) ∈ Set.Ioc (0 : ℝ) 1 := fun k => hεe (ι n k)
  have hεp : ∀ k : ℕ, 0 < e (ι n k) := fun k => (hεI k).1
  have hε0' : Filter.Tendsto (fun k : ℕ => e (ι n k)) Filter.atTop (nhds 0) :=
    hε0.comp hι.tendsto_atTop
  have hK'0 : 0 ≤ K' n :=
    le_trans (Work.Spaces.HkNorm_nonneg α 6 (slice (G n n) 0))
      ((hTower n n le_rfl).hb6 0 ⟨le_rfl, hTn.le⟩)
  have hsmK : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) (Tn n), ∀ m : ℕ,
      ContDiffOn ℝ m (Function.uncurry (slice (G n (ι n k)) σ)) Quad :=
    fun k σ hσ m => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp ((htw k).hsm σ hσ) m
  have hmem6 : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) (Tn n),
      Work.Spaces.HkMem α 6 (slice (G n (ι n k)) σ) := fun k σ hσ => (htw k).hmem6 σ hσ
  have hb6K : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) (Tn n),
      Work.FTS.StrongGlobal.Xn6 α (slice (G n (ι n k)) σ) ≤ K' n :=
    fun k σ hσ => (htw k).hb6 σ hσ
  have hCq : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) (Tn n),
      Work.FTS.ClassC.ClassC α (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ) :=
    fun k σ hσ => (htw k).hC σ hσ
  have hb4q : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) (Tn n),
      Work.FTS.Nonlin.Xn α (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ) ≤ C₀ * α ^ 2 :=
    fun k σ hσ => (htw k).hb4 σ hσ
  -- ## the projected ℋ⁶-bound of the tower
  obtain ⟨A, hA0, hA⟩ := Work.FTS.StrongEps.HkNorm_JfamP_le (ρ := ρ) hρ
  have hEll' : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α (max Ce (A * K' n)) u (E u) ∧
        Work.FTS.ClassC.EllPkgK α 6 (max Ce (A * K' n)) u (E u) :=
    fun u hu => ⟨Work.FTS.ClassC.EllPkgGo_mono hα.1 (hEll u hu).1 (le_max_left _ _),
      Work.FTS.ClassC.EllPkgK_mono (hEll u hu).2 (le_max_left _ _)⟩
  have hb6p : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) (Tn n),
      Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ) ≤
        max Ce (A * K' n) := by
    intro k σ hσ
    have h1 := hA (α := α) (ε := e (ι n k)) hα (hεI k) (g := G n (ι n k)) (s := σ)
      (fun m => hsmK k σ hσ m) (hmem6 k σ hσ)
    exact le_trans (le_trans h1.2 (mul_le_mul_of_nonneg_left (hb6K k σ hσ) hA0))
      (le_max_right _ _)
  -- ## the ℋ⁴-data of `epsWP` along the tower (for the Morrey equicontinuity)
  have hsmWT : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) (Tn n),
      Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ) :=
    fun k => Work.FTS.StrongEps.smoothOpen_epsWP (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (T := Tn n) (ρ := ρ) (Φs := Φs) (E := E) (g := G n (ι n k)) (ε := e (ι n k))
      hα hEll hstar (fun σ hσ => hCq k σ hσ)
  have hsmW : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ) :=
    fun k σ hσ => hsmWT k σ ⟨hσ.1, le_trans hσ.2 hTT⟩
  obtain ⟨KW, hKWpos, hKW⟩ := Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam (α := α) (C₀ := C₀)
    (Ce := max Ce (A * K' n)) (Cs := Cs) (T := T) (ρ := ρ) (Φs := Φs) (E := E)
    (G := fun k => G n (ι n k)) (ε := fun k => e (ι n k))
    hα hEll' hstar hml
    (fun k σ hσ => hCq k σ ⟨hσ.1, le_trans hσ.2 hTT⟩)
    (fun k σ hσ => hb4q k σ ⟨hσ.1, le_trans hσ.2 hTT⟩)
    (fun k σ hσ => hb6p k σ ⟨hσ.1, le_trans hσ.2 hTT⟩)
  have hmemW : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 4 (epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ) :=
    fun k σ hσ => (hKW k σ hσ).1
  have hbW : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 4 (epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ) ≤ KW :=
    fun k σ hσ => (hKW k σ hσ).2
  -- ## the local Hölder modulus of `epsWP` on a ball around `p`
  have hminpos : 0 < min (p.1 / 2) (min (p.2 / 2) ((π / 2 - p.2) / 2)) := by
    refine lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hballQ : Metric.closedBall p (min (p.1 / 2) (min (p.2 / 2) ((π / 2 - p.2) / 2)))
      ⊆ Work.FTS.EllipticEst.Q0 := by
    intro q hq
    have hq' : dist q p ≤ min (p.1 / 2) (min (p.2 / 2) ((π / 2 - p.2) / 2)) := hq
    rw [Prod.dist_eq] at hq'
    have h1 : dist q.1 p.1 ≤ min (p.1 / 2) (min (p.2 / 2) ((π / 2 - p.2) / 2)) :=
      le_trans (le_max_left _ _) hq'
    have h2 : dist q.2 p.2 ≤ min (p.1 / 2) (min (p.2 / 2) ((π / 2 - p.2) / 2)) :=
      le_trans (le_max_right _ _) hq'
    rw [Real.dist_eq] at h1 h2
    have hρz : min (p.1 / 2) (min (p.2 / 2) ((π / 2 - p.2) / 2)) ≤ p.1 / 2 := min_le_left _ _
    have hρθ : min (p.1 / 2) (min (p.2 / 2) ((π / 2 - p.2) / 2)) ≤ p.2 / 2 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have hρθ2 : min (p.1 / 2) (min (p.2 / 2) ((π / 2 - p.2) / 2)) ≤ (π / 2 - p.2) / 2 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    refine Work.FTS.EllipticEst.mem_Q0.mpr ⟨?_, ?_, ?_⟩
    · have := abs_le.mp h1
      linarith [this.1, le_trans hρz le_rfl]
    · have := abs_le.mp h2
      linarith [this.1, le_trans hρθ le_rfl]
    · have := abs_le.mp h2
      linarith [this.2, le_trans hρθ2 le_rfl]
  have hKρ : IsCompact (Metric.closedBall p (min (p.1 / 2) (min (p.2 / 2) ((π / 2 - p.2) / 2)))) :=
    isCompact_closedBall p _
  obtain ⟨C, hCpos, hequiHB⟩ := epsWP_equicont_tower (α := α) (B4 := KW) (T := T) (ρ := ρ)
    (Φs := Φs) (E := E) (ε := fun k => e (ι n k)) (G := fun k => G n (ι n k))
    (K := Metric.closedBall p (min (p.1 / 2) (min (p.2 / 2) ((π / 2 - p.2) / 2))))
    hα hKρ hballQ hsmW hmemW hbW
  have hAmul0 : 0 ≤ C * (1 + KW) := by positivity
  have hholder : ∀ k : ℕ,
      ∀ q ∈ Metric.closedBall p (min (p.1 / 2) (min (p.2 / 2) ((π / 2 - p.2) / 2))),
      ∀ q' ∈ Metric.closedBall p (min (p.1 / 2) (min (p.2 / 2) ((π / 2 - p.2) / 2))),
      |epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s q.1 q.2
        - epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s q'.1 q'.2|
        ≤ (C * (1 + KW)) * Real.sqrt ‖q - q'‖ :=
    fun k q hq q' hq' => hequiHB k s hs q hq q' hq'
  have hequi : ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℕ, ∀ q : ℝ × ℝ, ‖q‖ ≤ δ →
        |epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s
            (Work.FTS.StrongEps.zShift p.1 q.1) (Work.FTS.StrongEps.thShift p.2 q.2)
          - epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s p.1 p.2| ≤ η :=
    shift_modulus_of_holder (A := C * (1 + KW)) hAmul0 hpz hpθ hminpos hballQ hholder
  -- ## continuity on the open quadrant
  have hcontW : ∀ k : ℕ,
      ContinuousOn (Function.uncurry (epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s)) Quad :=
    fun k => contDiffOn_zero.mp ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
      (hsmW k s hs) (0 : ℕ))
  -- ## the pointwise convergence of `epsWP` along the tower
  have hwp : Filter.Tendsto (fun k : ℕ =>
      epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s p.1 p.2) Filter.atTop
      (nhds (rhsFun α Φs E (clampQ Fc g₀) s p.1 p.2)) :=
    epsWP_tendsto_tower n hα hρ hc₁ hc₂ hEll hstar hml hELL3 hsmΦ hL12g₀ hεe hε0 hTower
      hMaj hDec hι hadm hconv hT hTT hp hs
  -- ## the mollified sequence converges
  have hJeps : Filter.Tendsto (fun k : ℕ => Jeps ρ (e (ι n k))
      (epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s) p.1 p.2) Filter.atTop
      (nhds (rhsFun α Φs E (clampQ Fc g₀) s p.1 p.2)) :=
    Work.FTS.StrongEps.E5G.Jeps_tendsto_of_modulus hρ.moll hpz hpθ hεp hε0' hcontW hequi hwp
  -- ## the `P₀`-correction vanishes
  have hcorr0 : Filter.Tendsto (fun k : ℕ => Work.Construction.L12 (Jeps ρ (e (ι n k))
      (epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s)) 0 / pzNorm) Filter.atTop (nhds 0) :=
    L12_Jeps_epsWP_tendsto_tower n hα hρ hEll hstar hml hεe hε0 hTower hι hadm hT hTT hs
  have hcorr : Filter.Tendsto (fun k : ℕ => (Work.Construction.L12 (Jeps ρ (e (ι n k))
      (epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s)) 0 / pzNorm) * bump p.1 p.2)
      Filter.atTop (nhds 0) := by
    have := hcorr0.mul_const (bump p.1 p.2)
    simpa using this
  -- ## the algebraic split of `epsRHSP`
  have hsplit : (fun k : ℕ => epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s p.1 p.2)
      = fun k : ℕ => Jeps ρ (e (ι n k)) (epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s) p.1 p.2
          - (Work.Construction.L12 (Jeps ρ (e (ι n k))
              (epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s)) 0 / pzNorm) * bump p.1 p.2 := by
    funext k
    rw [Work.FTS.StrongEps.epsRHSP_eq_Pz_Jeps_epsWP]
    have hsmJ : Work.FTS.EllipticEst.SmoothOpen
        (Jeps ρ (e (ι n k)) (epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s)) :=
      Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ (hεp k)
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hsmWT k s hs'))
    have hmp := Work.FTS.StrongEps.PZeroAux.mixed_Pz
      (f := Jeps ρ (e (ι n k)) (epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s))
      hsmJ hpz hpθ 0 0
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
      Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] using hmp
  rw [hsplit]
  simpa using hJeps.sub hcorr

end Work.FTS.StrongEps.E5G
