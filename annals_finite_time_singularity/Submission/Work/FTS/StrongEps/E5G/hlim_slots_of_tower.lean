import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E5G.epsRHSP_hkMem5_bnd_fam
import Submission.Work.FTS.StrongEps.E5G.hWc_of_tower
import Submission.Work.FTS.StrongEps.E5G.hlim_of_tower
import Submission.Work.FTS.StrongEps.E5G.morrey_five_slots
import Submission.Work.FTS.StrongEps.E5G.weak_slots_tendsto_open
import Submission.Work.FTS.StrongEps.EpsE4Thr.epsRHSP_hkMem_fam
import Submission.Work.FTS.StrongEps.EpsHbdd
import Submission.Work.FTS.StrongEps.EpsHlim4
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup
import Submission.Work.FTS.StrongEps.PZeroAux.bumpHkNormBound
import Submission.Work.FTS.StrongEps.PZeroAux.mixed_Pz
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS_EllLimOK.ProducerH.pzIterTwo_shiftSing_eq_PhiTil_add
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXVP.thLip
import Submission.Work.FTS_RegExport.THL.L.DzDthSG_C1Jet_of_inputs
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

namespace Work.FTS.StrongEps.E5G

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

theorem hlim_slots_of_tower {α C₀ Ce Cs Cs6 T : ℝ} {K' : ℕ → ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g₀ : Work.FTS.Galerkin.Fn} {e : ℕ → ℝ} {G : ℕ → ℕ → Work.FTS.Galerkin.Fam}
    {Maj : ℕ → ℝ → ℝ} {ι : ℕ → ℕ → ℕ} {Fc : ℝ → Work.FTS.Galerkin.Fn}
    (n : ℕ) (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hc₁ : 1 / 10 ≤ Work.Spaces.c α) (hc₂ : Work.Spaces.c α ≤ 10)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hstar6 : Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
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
      ∀ (j i : ℕ), j + i ≤ 3 →
        Filter.Tendsto (fun k : ℕ => Work.Spaces.mixed j i
            (Work.FTS.StrongEps.epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed j i
            (Work.FTS.StrongEps.rhsFun α Φs E (Work.FTS.StrongEps.clampQ Fc g₀) s) p.1 p.2)) := by
  intro p hp s hs j i hji
  -- ## notation: the sequence and its limit
  set V : ℕ → Fn := fun k => Work.FTS.StrongEps.epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s
    with hVdef
  set R : Fn := Work.FTS.StrongEps.rhsFun α Φs E (Work.FTS.StrongEps.clampQ Fc g₀) s with hRdef
  -- ## the horizon
  have hTn : 0 < Tn n := Tn_pos n
  have hT0 : (0 : ℝ) ≤ T := hT.le
  have hs' : s ∈ Set.Icc (0 : ℝ) (Tn n) := ⟨hs.1, le_trans hs.2 hTT⟩
  -- ## the tower along the extraction
  have htw : ∀ k : ℕ, TowerAt α C₀ ρ Φs E g₀ n (e (ι n k)) (K' n) (G n (ι n k)) :=
    fun k => hTower n (ι n k) (hadm k)
  have hεIc : ∀ k : ℕ, e (ι n k) ∈ Set.Ioc (0 : ℝ) 1 := fun k => hεe (ι n k)
  have hεposc : ∀ k : ℕ, 0 < e (ι n k) := fun k => (hεIc k).1
  have hK'0 : 0 ≤ K' n :=
    le_trans (Work.Spaces.HkNorm_nonneg α 6 (slice (G n n) 0))
      ((hTower n n le_rfl).hb6 0 ⟨le_rfl, hTn.le⟩)
  -- ## the elliptic constant raised to the tower's level-`6` bound
  obtain ⟨A, hA0, hA⟩ := Work.FTS.StrongEps.HkNorm_JfamP_le (ρ := ρ) hρ
  have hEll' : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α (max Ce (A * K' n)) u (E u) ∧
        Work.FTS.ClassC.EllPkgK α 6 (max Ce (A * K' n)) u (E u) :=
    fun u hu => ⟨Work.FTS.ClassC.EllPkgGo_mono hα.1 (hEll u hu).1 (le_max_left _ _),
      Work.FTS.ClassC.EllPkgK_mono (hEll u hu).2 (le_max_left _ _)⟩
  have hb6p : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.StrongGlobal.Xn6 α (slice (Work.FTS.StrongEps.JfamP ρ (e (ι n k)) (G n (ι n k))) σ)
        ≤ max Ce (A * K' n) := by
    intro k σ hσ
    have hσ' : σ ∈ Set.Icc (0 : ℝ) (Tn n) := ⟨hσ.1, le_trans hσ.2 hTT⟩
    have h1 := hA (α := α) (ε := e (ι n k)) hα (hεIc k) (g := G n (ι n k)) (s := σ)
      (fun m => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp ((htw k).hsm σ hσ') m)
      ((htw k).hmem6 σ hσ')
    exact le_trans (le_trans h1.2 (mul_le_mul_of_nonneg_left ((htw k).hb6 σ hσ') hA0))
      (le_max_right _ _)
  -- ## the tower's class-`C` data for the projected slices
  have hCc : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.ClassC.ClassC α (slice (Work.FTS.StrongEps.JfamP ρ (e (ι n k)) (G n (ι n k))) σ) :=
    fun k σ hσ => (htw k).hC σ ⟨hσ.1, le_trans hσ.2 hTT⟩
  have hb4c : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ (e (ι n k)) (G n (ι n k))) σ)
        ≤ C₀ * α ^ 2 :=
    fun k σ hσ => (htw k).hb4 σ ⟨hσ.1, le_trans hσ.2 hTT⟩
  -- ## smoothness and `ℋ⁶`-honesty of the sequence
  have hV6 : ∀ k : ℕ,
      Work.FTS.EllipticEst.SmoothOpen (V k) ∧ Work.Spaces.HkMem α 6 (V k) := by
    intro k
    have h := Work.FTS.StrongEps.EpsE4Thr.epsRHSP_smoothOpen_hkMem6_fam (α := α) (C₀ := C₀)
      (Ce := max Ce (A * K' n)) (Cs := Cs) (B := K' n) (ρ := ρ) (Φs := Φs) (E := E)
      (g := G n (ι n k)) (ε := e (ι n k)) (T := T)
      hα hρ (hεposc k) (hεIc k).2 hEll' hstar hml hK'0
      (fun σ hσ => (htw k).hsm σ ⟨hσ.1, le_trans hσ.2 hTT⟩)
      (fun σ hσ => (htw k).hmem6 σ ⟨hσ.1, le_trans hσ.2 hTT⟩)
      (fun σ hσ => (htw k).hb6 σ ⟨hσ.1, le_trans hσ.2 hTT⟩)
      (fun σ hσ => by simpa only [Work.FTS.StrongEps.slice_JfamP] using hCc k σ hσ)
      (fun σ hσ => by simpa only [Work.FTS.StrongEps.slice_JfamP] using hb4c k σ hσ)
      s hs
    simpa only [hVdef] using h
  -- ## the uniform `ℋ⁵`-bound of the sequence
  obtain ⟨KW5, hKW5pos, hKW5⟩ :=
    Work.FTS.StrongEps.E5G.epsRHSP_hkMem5_bnd_fam (α := α) (C₀ := C₀)
      (Ce := max Ce (A * K' n)) (Cs := Cs) (Cs6 := Cs6) (T := T) (ρ := ρ) (Φs := Φs)
      (E := E) (G := fun k => G n (ι n k)) (ε := fun k => e (ι n k))
      hα hρ hεIc hEll' hstar hstar6 hml
      (fun k σ hσ => hCc k σ hσ) (fun k σ hσ => hb4c k σ hσ) (fun k σ hσ => hb6p k σ hσ)
  have hV5mem : ∀ k : ℕ, Work.Spaces.HkMem α 5 (V k) := by
    intro k
    have h := (hKW5 k s hs).1
    simpa only [hVdef] using h
  have hV5bnd : ∀ k : ℕ, Work.Spaces.HkNorm α 5 (V k) ≤ KW5 := by
    intro k
    have h := (hKW5 k s hs).2
    simpa only [hVdef] using h
  -- ## pointwise convergence of the sequence on the open quadrant
  have hVconv : ∀ q ∈ Work.FTS.EllipticEst.Q0,
      Filter.Tendsto (fun k : ℕ => V k q.1 q.2) Filter.atTop (nhds (R q.1 q.2)) := by
    intro q hq
    have h := hlim_of_tower n hα hρ hc₁ hc₂ hEll hstar hml hELL3 hsmΦ hL12g₀ hεe hε0
      hTower hMaj hDec hι hadm hconv hT hTT q hq s hs
    simpa only [hVdef, hRdef] using h
  -- ## continuity of the limit on the open quadrant
  have hRcont : ContinuousOn (Function.uncurry R) Work.FTS.EllipticEst.Q0 := by
    have h := hWc_of_tower (α₄ := α) n hα.1 hα.2 ⟨hα.1, le_rfl⟩ hρ hc₁ hc₂ hEll hstar hstar6
      hml hELL3 hsmΦ hL12g₀ hεe hε0 hTower hMaj hDec hι hadm hconv hT hTT
    have hmem : ∀ q ∈ Work.FTS.EllipticEst.Q0, (q.1, q.2, s) ∈
        Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T := by
      intro q hq
      have hq' := Work.FTS.EllipticEst.mem_Q0.mp hq
      exact ⟨hq'.1, ⟨hq'.2.1, hq'.2.2⟩, hs⟩
    have hfun : Function.uncurry R = fun q : ℝ × ℝ =>
        Work.FTS.StrongEps.rhsFun α Φs E (Work.FTS.StrongEps.clampQ Fc g₀) s q.1 q.2 := by
      funext q
      simp only [Function.uncurry, hRdef]
    rw [hfun]
    have hpair : ContinuousOn (fun r : ℝ × ℝ => (r.1, r.2, s)) Work.FTS.EllipticEst.Q0 := by
      fun_prop
    have hcomp := h.comp hpair (fun y hy => hmem y hy)
    simpa only [Function.comp_def] using hcomp
  -- ## a uniform value bound on compact subsets
  have hVbnd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, ∀ k : ℕ, ∀ q ∈ K, |V k q.1 q.2| ≤ C := by
    intro K hK hKQ
    obtain ⟨K'', hK''c, hK''Q, hKK'', hshift⟩ :=
      Work.FTS.StrongEps.exists_shift_window_compact (ε := (1 : ℝ)) one_pos le_rfl hK hKQ
    obtain ⟨B, hBpos, hB⟩ := Work.FTS.StrongEps.epsWP_sup_le_fam (α := α) (C₀ := C₀)
      (Ce := max Ce (A * K' n)) (Cs := Cs) (T := T) (ρ := ρ) (Φs := Φs) (E := E)
      (G := fun k => G n (ι n k)) (ε := fun k => e (ι n k))
      hα hρ hεIc hT0 hc₁ hc₂ hEll' hstar hml
      (fun k σ hσ => hCc k σ hσ) (fun k σ hσ => hb4c k σ hσ) (fun k σ hσ => hb6p k σ hσ)
      hK''c hK''Q
    obtain ⟨KW4, hKW4pos, hKW4⟩ :=
      Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam (α := α) (C₀ := C₀)
        (Ce := max Ce (A * K' n)) (Cs := Cs) (T := T) (ρ := ρ) (Φs := Φs) (E := E)
        (G := fun k => G n (ι n k)) (ε := fun k => e (ι n k))
        hα hEll' hstar hml
        (fun k σ hσ => hCc k σ hσ) (fun k σ hσ => hb4c k σ hσ) (fun k σ hσ => hb6p k σ hσ)
    obtain ⟨Cb, hCb0, hbump⟩ := Work.FTS.StrongEps.exists_bound_mixed_bump K hK
    obtain ⟨CL, hCL0, hCL⟩ := Work.FTS.StrongEps.abs_L12_Jeps_le (ρ := ρ) hρ
    have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
    refine ⟨B + (CL * KW4 / Work.FTS.StrongEps.pzNorm) * Cb, fun k q hq => ?_⟩
    have hqQ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hq)
    -- the smoothness of `epsWP`
    have hWsm : Work.FTS.EllipticEst.SmoothOpen
        (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s) :=
      Work.FTS.StrongEps.smoothOpen_epsWP (α := α) (C₀ := C₀) (Ce := max Ce (A * K' n))
        (Cs := Cs) (T := T) (ρ := ρ) (Φs := Φs) (E := E) (g := G n (ι n k))
        (ε := e (ι n k)) hα hEll' hstar (fun σ hσ => hCc k σ hσ) s hs
    have hmodel : Work.FTS.StrongEps.Jeps ρ (e (ι n k))
        (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s) q.1 q.2
        = Work.FTS.StrongEps.Jeps ρ (e (ι n k))
          (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s) q.1 q.2 := rfl
    have hmain : |Work.FTS.StrongEps.Jeps ρ (e (ι n k))
        (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s) q.1 q.2| ≤ B := by
      refine Work.FTS.StrongEps.abs_Jeps_le_sup ρ hρ.moll (hεposc k) hqQ.1
        ⟨hqQ.2.1, hqQ.2.2⟩ ?_ hBpos.le
      intro r hr1 hr2
      exact hB k s hs (Work.FTS.StrongEps.zShift q.1 r.1, Work.FTS.StrongEps.thShift q.2 r.2) (hshift q hq r (le_trans hr1 (hεIc k).2) (le_trans hr2 (hεIc k).2))
    have hcorr : |(Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
          (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s)) 0
            / Work.FTS.StrongEps.pzNorm) * Work.FTS.StrongEps.bump q.1 q.2|
        ≤ (CL * KW4 / Work.FTS.StrongEps.pzNorm) * Cb := by
      rw [abs_mul]
      have hL : |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
          (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s)) 0| ≤ CL * KW4 :=
        hCL hα (hεposc k) (hεIc k).2 hKW4pos.le (fun m => hWsm.forall m)
          (hKW4 k s hs).1 (hKW4 k s hs).2
      have hal : |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
          (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s)) 0
            / Work.FTS.StrongEps.pzNorm| ≤ CL * KW4 / Work.FTS.StrongEps.pzNorm := by
        rw [abs_div, abs_of_pos hpzpos]
        exact div_le_div_of_nonneg_right hL hpzpos.le
      have hb : |Work.FTS.StrongEps.bump q.1 q.2| ≤ Cb := by
        have h := hbump 0 0 (by norm_num) q hq
        simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
          Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] using h
      exact mul_le_mul hal hb (abs_nonneg _)
        (div_nonneg (mul_nonneg hCL0 hKW4pos.le) hpzpos.le)
    have hsplit : V k q.1 q.2 = Work.FTS.StrongEps.Jeps ρ (e (ι n k))
        (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s) q.1 q.2
        - (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
            (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s)) 0
              / Work.FTS.StrongEps.pzNorm) * Work.FTS.StrongEps.bump q.1 q.2 := by
      rw [hVdef]
      rfl
    rw [hsplit]
    calc |Work.FTS.StrongEps.Jeps ρ (e (ι n k))
            (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s) q.1 q.2
          - (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
              (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s)) 0
                / Work.FTS.StrongEps.pzNorm) * Work.FTS.StrongEps.bump q.1 q.2|
        ≤ |Work.FTS.StrongEps.Jeps ρ (e (ι n k))
              (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s) q.1 q.2|
          + |(Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
              (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s)) 0
                / Work.FTS.StrongEps.pzNorm) * Work.FTS.StrongEps.bump q.1 q.2| := by
          have h := abs_add_le (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
              (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s) q.1 q.2)
            (-((Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
                (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s)) 0
                  / Work.FTS.StrongEps.pzNorm) * Work.FTS.StrongEps.bump q.1 q.2))
          simpa only [sub_eq_add_neg, abs_neg] using h
      _ ≤ B + (CL * KW4 / Work.FTS.StrongEps.pzNorm) * Cb := add_le_add hmain hcorr
  -- ## the equi-Hölder bound on the slots, from the level-`5` Morrey bound
  have hequi : ∀ (j' i' : ℕ), j' + i' ≤ 3 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Work.FTS.EllipticEst.Q0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ∀ p ∈ K, ∀ q ∈ K,
        |Work.Spaces.mixed j' i' (V k) p.1 p.2 - Work.Spaces.mixed j' i' (V k) q.1 q.2|
          ≤ C * dist p q ^ (1 / 2 : ℝ) := by
    intro j' i' hji' K hK hKQ
    obtain ⟨C, hCpos, hC⟩ := morrey_five_slots hK hKQ
    refine ⟨C * (1 + KW5), by positivity, fun k p hp q hq => ?_⟩
    have h1 := hC α hα (V k) (hV6 k).1 (hV5mem k) j' i' hji' p hp q hq
    have h2 : Work.Spaces.HkNorm α 5 (V k) ≤ KW5 := hV5bnd k
    have h3 : Real.sqrt ‖p - q‖ = dist p q ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, dist_eq_norm]
    rw [h3] at h1
    calc |Work.Spaces.mixed j' i' (V k) p.1 p.2 - Work.Spaces.mixed j' i' (V k) q.1 q.2|
        ≤ C * (1 + Work.Spaces.HkNorm α 5 (V k)) * dist p q ^ (1 / 2 : ℝ) := h1
      _ ≤ C * (1 + KW5) * dist p q ^ (1 / 2 : ℝ) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hCpos.le)
            (Real.rpow_nonneg dist_nonneg _)
          linarith
  -- ## the weak convergence of the slots
  have hweakOf : ∀ (j' i' : ℕ), j' + i' ≤ 3 → ∀ φ : ℝ → ℝ → ℝ,
      (∀ m : ℕ, ContDiff ℝ m (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ L : ℝ, Filter.Tendsto (fun k : ℕ => ∫ q in Work.FTS.EllipticEst.Q0,
        Work.Spaces.mixed j' i' (V k) q.1 q.2 * φ q.1 q.2) Filter.atTop (nhds L) :=
    fun j' i' _ φ hφ hcs hts => weak_slots_tendsto_open (V := V) (R := R) j' i'
      (fun k => (hV6 k).1) hVconv hRcont hVbnd φ hφ hcs hts
  -- ## the Arzela-Ascoli step: the slots converge pointwise
  have hAA : ∀ (j' i' : ℕ), j' + i' ≤ 3 → ∃ Φ : Fn,
      ContinuousOn (Function.uncurry Φ) Work.FTS.EllipticEst.Q0 ∧
      ∀ q ∈ Work.FTS.EllipticEst.Q0, Filter.Tendsto (fun k : ℕ =>
        Work.Spaces.mixed j' i' (V k) q.1 q.2) Filter.atTop (nhds (Φ q.1 q.2)) :=
    fun j' i' hji' => exists_tendsto_of_equiholder_of_weak (V := V) j' i'
      (fun k => (hV6 k).1) (hequi j' i' hji') (hweakOf j' i' hji')
  -- ## the slot limits, as a two-index family
  let Φ : ℕ → ℕ → Fn := fun j' i' =>
    if h : j' + i' ≤ 3 then Classical.choose (hAA j' i' h) else R
  have hΦspec : ∀ (j' i' : ℕ) (h : j' + i' ≤ 3),
      ContinuousOn (Function.uncurry (Φ j' i')) Work.FTS.EllipticEst.Q0 ∧
      ∀ q ∈ Work.FTS.EllipticEst.Q0, Filter.Tendsto (fun k : ℕ =>
        Work.Spaces.mixed j' i' (V k) q.1 q.2) Filter.atTop (nhds (Φ j' i' q.1 q.2)) := by
    intro j' i' h
    have hΦeq : Φ j' i' = Classical.choose (hAA j' i' h) := by
      show (if h' : j' + i' ≤ 3 then Classical.choose (hAA j' i' h') else R)
        = Classical.choose (hAA j' i' h)
      rw [dif_pos h]
    rw [hΦeq]
    exact Classical.choose_spec (hAA j' i' h)
  -- ## pointwise bounds on the slots of the sequence
  have hbnd : ∀ (j' i' : ℕ), j' + i' ≤ 3 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Work.FTS.EllipticEst.Q0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ∀ q ∈ K,
        |Work.Spaces.mixed j' i' (V k) q.1 q.2| ≤ C :=
    fun j' i' hji' => pointwise_bound_of_tendsto_of_equiholder (V := V) (Φ := Φ j' i') j' i'
      (fun k => (hV6 k).1) (hequi j' i' hji') (hΦspec j' i' hji').2 (hΦspec j' i' hji').1
  -- ## identification of the classical slots of the limit
  have hident : ∀ (j' i' : ℕ), j' + i' ≤ 3 → ∀ q ∈ Work.FTS.EllipticEst.Q0,
      Work.Spaces.mixed j' i' R q.1 q.2 = Φ j' i' q.1 q.2 :=
    slots_eq_of_convergent_jets (V := V) (R := R) (Φ := Φ)
      (fun k => (hV6 k).1) hVconv (fun j' i' hji' q hq => (hΦspec j' i' hji').2 q hq)
      hequi hbnd
  -- ## conclusion
  have hfin : Filter.Tendsto (fun k : ℕ => Work.Spaces.mixed j i (V k) p.1 p.2) Filter.atTop
      (nhds (Work.Spaces.mixed j i R p.1 p.2)) := by
    have h1 := (hΦspec j i hji).2 p hp
    rw [← hident j i hji p hp] at h1
    exact h1
  simpa only [hVdef, hRdef] using hfin

end Work.FTS.StrongEps.E5G
