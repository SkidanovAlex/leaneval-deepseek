import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.E5G.PkgOfHlim
import Submission.Work.FTS.StrongEps.E5G.hWc_aux
import Submission.Work.FTS.StrongEps.E5G.hapx_of_tower
import Submission.Work.FTS.StrongEps.E5G.hlim_of_tower
import Submission.Work.FTS.StrongEps.E5G.slice_lip5_norm
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsE4Thr.epsRHSP_hkMem_fam
import Submission.Work.FTS.StrongEps.EpsHbdd
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup_val
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaData
import Submission.Work.FTS.StrongEps.EpsRLX.N0DiffClassC
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartAux
import Submission.Work.FTS.StrongEps.EpsSqTools.Shift
import Submission.Work.FTS.StrongEps.JfamP_norm
import Submission.Work.FTS.StrongEps.RhsCont
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam
import Submission.Work.FTS.StrongEps.smoothOpen_epsWP
import Submission.Work.FTS.StrongEps.wtZ_shift_le
import Submission.Work.FTS.StrongPersist.H6Rows.NZzero6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.starSlotShift
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_EllLimOK.ProducerH.pzIterTwo_shiftSing_eq_PhiTil_add
import Submission.Work.FTS_RegExport.RXR5L.coef_tau_lip
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXVP.thLip
import Submission.Work.FTS_RegExport.THL.angular_L2_noTrace
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.AsmPkg =====
section

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

set_option autoImplicit false


end Work.FTS.StrongEps.E5G
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.hcontR_of_tower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice famOf)

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 2000000

theorem hcontR_of_tower {α₄ α C₀ Ce Cs Cs6 T : ℝ} {K' : ℕ → ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g₀ : Work.FTS.Galerkin.Fn} {e : ℕ → ℝ} {G : ℕ → ℕ → Work.FTS.Galerkin.Fam}
    {Maj : ℕ → ℝ → ℝ} {ι : ℕ → ℕ → ℕ} {Fc : ℝ → Work.FTS.Galerkin.Fn}
    (n : ℕ) (hα₄ : 0 < α₄) (hα₄1 : α₄ ≤ 1) (hα : α ∈ Set.Ioc (0 : ℝ) α₄)
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
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      ContinuousOn (fun s : ℝ =>
        Work.FTS.StrongEps.rhsFun α Φs E (Work.FTS.StrongEps.clampQ Fc g₀) s z θ)
        (Set.Icc 0 T) := by
  -- ## elementary consequences of the parameters
  have hα1 : α ≤ 1 := le_trans hα.2 hα₄1
  have hαI : α ∈ Set.Ioc (0 : ℝ) 1 := ⟨hα.1, hα1⟩
  have hTn : 0 < Tn n := Tn_pos n
  have hT0 : (0 : ℝ) ≤ T := hT.le
  have hIcc' : Set.Icc (0 : ℝ) T ⊆ Set.Icc (0 : ℝ) (Tn n) := Set.Icc_subset_Icc le_rfl hTT
  -- ## the tower along the extraction
  have htw : ∀ k : ℕ, TowerAt α C₀ ρ Φs E g₀ n (e (ι n k)) (K' n) (G n (ι n k)) :=
    fun k => hTower n (ι n k) (hadm k)
  have hεI : ∀ k : ℕ, e (ι n k) ∈ Set.Ioc (0 : ℝ) 1 := fun k => hεe (ι n k)
  have hεpos : ∀ k : ℕ, 0 < e (ι n k) := fun k => (hεI k).1
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
      Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ)
        ≤ max Ce (A * K' n) := by
    intro k σ hσ
    have hσ' : σ ∈ Set.Icc (0 : ℝ) (Tn n) := ⟨hσ.1, le_trans hσ.2 hTT⟩
    have h1 := hA (α := α) (ε := e (ι n k)) hαI (hεI k) (g := G n (ι n k)) (s := σ)
      (fun m => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp ((htw k).hsm σ hσ') m)
      ((htw k).hmem6 σ hσ')
    exact le_trans (le_trans h1.2 (mul_le_mul_of_nonneg_left ((htw k).hb6 σ hσ') hA0))
      (le_max_right _ _)
  -- ## the data of `epsWP` along the extraction
  have hVsm : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen
        (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ) :=
    fun k σ hσ => Work.FTS.StrongEps.smoothOpen_epsWP (C₀ := C₀) (T := T) (ε := e (ι n k))
      (g := G n (ι n k)) hαI hEll' hstar
      (fun s hs => (htw k).hC s ⟨hs.1, le_trans hs.2 hTT⟩) σ hσ
  obtain ⟨KW4, hKW4pos, hKW4⟩ :=
    Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam (α := α) (C₀ := C₀) (Ce := max Ce (A * K' n))
      (Cs := Cs) (T := T) (ρ := ρ) (Φs := Φs) (E := E)
      (G := fun k => G n (ι n k)) (ε := fun k => e (ι n k)) hαI hEll' hstar hml
      (fun k s hs => (htw k).hC s ⟨hs.1, le_trans hs.2 hTT⟩)
      (fun k s hs => (htw k).hb4 s ⟨hs.1, le_trans hs.2 hTT⟩)
      (fun k s hs => hb6p k s hs)
  have hVmem4 : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ) :=
    fun k σ hσ => (hKW4 k σ hσ).1
  obtain ⟨KW5, hKW5pos, hKW5⟩ :=
    epsWP_hkMem5_bnd_fam (α := α) (C₀ := C₀) (Ce := max Ce (A * K' n)) (Cs := Cs)
      (Cs6 := Cs6) (T := T) (ρ := ρ) (Φs := Φs) (E := E)
      (G := fun k => G n (ι n k)) (ε := fun k => e (ι n k)) hαI hρ hEll' hstar hstar6 hml
      (fun k s hs => (htw k).hC s ⟨hs.1, le_trans hs.2 hTT⟩)
      (fun k s hs => (htw k).hb4 s ⟨hs.1, le_trans hs.2 hTT⟩)
      (fun k s hs => hb6p k s hs)
  -- ## smoothness of the projected slices, and the level-`6` data of `epsRHSP`
  have hproj_mem6 : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 6 (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ) := by
    intro k σ hσ
    have hσ' : σ ∈ Set.Icc (0 : ℝ) (Tn n) := ⟨hσ.1, le_trans hσ.2 hTT⟩
    exact (hA (α := α) (ε := e (ι n k)) hαI (hεI k) (g := G n (ι n k)) (s := σ)
      (fun m => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp ((htw k).hsm σ hσ') m)
      ((htw k).hmem6 σ hσ')).1
  have hR6 : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen
          (Work.FTS.StrongEps.epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ) ∧
        Work.Spaces.HkMem α 6
          (Work.FTS.StrongEps.epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ) :=
    fun k σ hσ => Work.FTS.StrongEps.EpsE4Thr.epsRHSP_smoothOpen_hkMem6_fam
      (α := α) (C₀ := C₀) (Ce := max Ce (A * K' n)) (Cs := Cs) (B := K' n) (ρ := ρ)
      (Φs := Φs) (E := E) (g := G n (ι n k)) (ε := e (ι n k)) (T := T)
      hαI hρ (hεpos k) (hεI k).2 hEll' hstar hml hK'0
      (fun s hs => (htw k).hsm s ⟨hs.1, le_trans hs.2 hTT⟩)
      (fun s hs => (htw k).hmem6 s ⟨hs.1, le_trans hs.2 hTT⟩)
      (fun s hs => (htw k).hb6 s ⟨hs.1, le_trans hs.2 hTT⟩)
      (fun s hs => by simpa only [slice_JfamP] using (htw k).hC s ⟨hs.1, le_trans hs.2 hTT⟩)
      (fun s hs => by simpa only [slice_JfamP] using (htw k).hb4 s ⟨hs.1, le_trans hs.2 hTT⟩)
      σ hσ
  have hcontK : ∀ k : ℕ, ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ =>
        Work.FTS.StrongEps.epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s z θ)
        (Set.Icc (0 : ℝ) T) :=
    fun k z θ hzθ => ((Work.FTS.StrongEps.continuousOn_epsRHSP_of_regP hTn (htw k).hsol
      (htw k).toEpsRegP) (z, θ) hzθ).mono hIcc'
  -- ## level-`5` slot bounds of `epsRHSP` on compacta (uniform in the fake time)
  have hslot5 : ∀ k : ℕ, ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (j i : ℕ), j + i ≤ 5 → ∀ p ∈ K,
        |Work.Spaces.mixed j i
          (Work.FTS.StrongEps.epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s) p.1 p.2| ≤ C := by
    intro k K hK hKQ
    obtain ⟨K'', hK''c, hK''Q, hKK'', hshift⟩ :=
      Work.FTS.StrongEps.exists_shift_window_compact (ε := 1) one_pos le_rfl hK hKQ
    obtain ⟨B'', hB''0, hB''⟩ :=
      Work.FTS.StrongEps.epsWP_sup_le_fam (α := α) (C₀ := C₀) (Ce := max Ce (A * K' n))
        (Cs := Cs) (T := T) (ρ := ρ) (Φs := Φs) (E := E)
        (G := fun k => G n (ι n k)) (ε := fun k => e (ι n k))
        hαI hρ (fun k => hεI k) hT0 hc₁ hc₂ hEll' hstar hml
        (fun k s hs => (htw k).hC s ⟨hs.1, le_trans hs.2 hTT⟩)
        (fun k s hs => (htw k).hb4 s ⟨hs.1, le_trans hs.2 hTT⟩)
        (fun k s hs => hb6p k s hs) hK''c hK''Q
    obtain ⟨C, hC0, hCb⟩ := EpsRHSP_slotSup_val5 (α := α) (T := T) (ε := e (ι n k))
      (ρ := ρ) (Φs := Φs) (E := E) (g := G n (ι n k)) hαI hρ (hεI k)
      (fun s hs => hVsm k s hs) hK hKQ
      ⟨K'', hK''c, hK''Q, hKK'', hshift, B'', hB''0.le, fun s hs p hp => hB'' k s hs p hp⟩
      ⟨KW4, hKW4pos.le, fun s hs => hKW4 k s hs⟩
    exact ⟨C, hC0, fun s hs j i hji p hp => hCb j i hji s hs p hp⟩
  -- ## the level-`5` norm bound of `epsRHSP`
  obtain ⟨A5, hA5pos, hA5⟩ := hkNorm_PzJeps_le_gen ρ hρ
  have hb5 : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 5
        (Work.FTS.StrongEps.epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ) ≤ A5 * KW5 := by
    intro k σ hσ
    have h := hA5 α hαI 5 (by norm_num) (by norm_num) (e (ι n k)) (hεI k)
      (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ)
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _ |>.mp (hVsm k σ hσ))
      (hKW5 k σ hσ).1
    show Work.Spaces.HkNorm α 5
      (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
        (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ))) ≤ A5 * KW5
    exact le_trans h (mul_le_mul_of_nonneg_left (hKW5 k σ hσ).2 hA5pos.le)
  -- ## the `ℋ⁵`-Lipschitz bound in the fake time for the tower slices
  have hSlice5 : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T, ∀ σ' ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 5 (fun z θ =>
          slice (G n (ι n k)) σ z θ - slice (G n (ι n k)) σ' z θ) ≤ A5 * KW5 * |σ - σ'| :=
    fun k => slice_lip5_norm (α := α) (T := T) (ε := e (ι n k)) (B := A5 * KW5)
      (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀) (g := G n (ι n k))
      (IsEpsSolP_mono (htw k).hsol hTT) (hcontK k)
      (fun s hs => (hR6 k s hs).1)
      (fun s hs => Work.FTS.OpenPkg.HkMem_mono_open (hR6 k s hs).1 5 (by norm_num) (hR6 k s hs).2)
      (fun s hs => hb5 k s hs)
      (fun K hK hKQ => by
        obtain ⟨C, _hC0, hC⟩ := hslot5 k K hK hKQ
        exact ⟨C, hC⟩)
  -- ## the projected difference at level `5`
  have hProj : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T, ∀ σ' ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 5 (fun z θ =>
          slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ z θ
            - slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ' z θ)
        ≤ A5 * (A5 * KW5 * |σ - σ'|) := by
    intro k σ hσ σ' hσ'
    have hsub := hSlice5 k σ hσ σ' hσ'
    have hsmσ : Work.FTS.EllipticEst.SmoothOpen (slice (G n (ι n k)) σ) :=
      (htw k).hsm σ ⟨hσ.1, le_trans hσ.2 hTT⟩
    have hsmσ' : Work.FTS.EllipticEst.SmoothOpen (slice (G n (ι n k)) σ') :=
      (htw k).hsm σ' ⟨hσ'.1, le_trans hσ'.2 hTT⟩
    have hmem6σ : Work.Spaces.HkMem α 6 (slice (G n (ι n k)) σ) :=
      (htw k).hmem6 σ ⟨hσ.1, le_trans hσ.2 hTT⟩
    have hmem6σ' : Work.Spaces.HkMem α 6 (slice (G n (ι n k)) σ') :=
      (htw k).hmem6 σ' ⟨hσ'.1, le_trans hσ'.2 hTT⟩
    have hmem5σ : Work.Spaces.HkMem α 5 (slice (G n (ι n k)) σ) :=
      Work.FTS.OpenPkg.HkMem_mono_open hsmσ 5 (by norm_num) hmem6σ
    have hmem5σ' : Work.Spaces.HkMem α 5 (slice (G n (ι n k)) σ') :=
      Work.FTS.OpenPkg.HkMem_mono_open hsmσ' 5 (by norm_num) hmem6σ'
    have hmem5D : Work.Spaces.HkMem α 5 (fun z θ =>
        slice (G n (ι n k)) σ z θ - slice (G n (ι n k)) σ' z θ) :=
      Work.FTS.GalBasis.hkMem_sub_open α 5 hsmσ hsmσ' hmem5σ hmem5σ'
    -- ## the projected difference is the projection of the mollified difference
    have hJsmσ' : Work.FTS.EllipticEst.SmoothOpen
        (Work.FTS.StrongEps.Jeps ρ (e (ι n k)) (slice (G n (ι n k)) σ)) :=
      Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ (hεpos k)
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsmσ)
    have hJsmσ'' : Work.FTS.EllipticEst.SmoothOpen
        (Work.FTS.StrongEps.Jeps ρ (e (ι n k)) (slice (G n (ι n k)) σ')) :=
      Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ (hεpos k)
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsmσ')
    have hmem4σ : Work.Spaces.HkMem α 4 (slice (G n (ι n k)) σ) :=
      Work.FTS.OpenPkg.HkMem_mono_open hsmσ 4 (by norm_num) hmem6σ
    have hmem4σ' : Work.Spaces.HkMem α 4 (slice (G n (ι n k)) σ') :=
      Work.FTS.OpenPkg.HkMem_mono_open hsmσ' 4 (by norm_num) hmem6σ'
    have hJmemσ : Work.Spaces.HkMem α 4
        (Work.FTS.StrongEps.Jeps ρ (e (ι n k)) (slice (G n (ι n k)) σ)) :=
      Work.FTS.StrongEps.HkMem_Jeps hρ.moll hαI (hεpos k)
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsmσ) hmem4σ
    have hJmemσ' : Work.Spaces.HkMem α 4
        (Work.FTS.StrongEps.Jeps ρ (e (ι n k)) (slice (G n (ι n k)) σ')) :=
      Work.FTS.StrongEps.HkMem_Jeps hρ.moll hαI (hεpos k)
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsmσ') hmem4σ'
    have h1 : Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
            (slice (G n (ι n k)) σ))
          - Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
            (slice (G n (ι n k)) σ'))
        = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ (e (ι n k)) (slice (G n (ι n k)) σ)
            - Work.FTS.StrongEps.Jeps ρ (e (ι n k)) (slice (G n (ι n k)) σ')) :=
      Work.FTS.StrongEps.EpsRLX.Pz_sub_eq
        (Work.FTS.StrongEps.EComparison.L12_sub_HkMem hJsmσ' hJsmσ'' hJmemσ hJmemσ' 0
          (by simp [Work.Spaces.Iz]))
    have h2 : Work.FTS.StrongEps.Jeps ρ (e (ι n k)) (slice (G n (ι n k)) σ)
          - Work.FTS.StrongEps.Jeps ρ (e (ι n k)) (slice (G n (ι n k)) σ')
        = Work.FTS.StrongEps.Jeps ρ (e (ι n k)) (fun z θ =>
            slice (G n (ι n k)) σ z θ - slice (G n (ι n k)) σ' z θ) :=
      Work.FTS.StrongEps.EpsRLX.Jeps_sub_eq hρ.moll (hεpos k) hsmσ hsmσ'
    have hkey : (fun z θ => slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ z θ
          - slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ' z θ)
        = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ (e (ι n k)) (fun z θ =>
            slice (G n (ι n k)) σ z θ - slice (G n (ι n k)) σ' z θ)) := by
      have hpre : (fun z θ => slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ z θ
            - slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ' z θ)
          = (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
                (slice (G n (ι n k)) σ))
              - Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
                (slice (G n (ι n k)) σ'))) := by
        funext z θ
        rfl
      rw [hpre, h1, h2]
    rw [hkey]
    refine le_trans (hA5 α hαI 5 (by norm_num) (by norm_num) (e (ι n k)) (hεI k)
      (fun z θ => slice (G n (ι n k)) σ z θ - slice (G n (ι n k)) σ' z θ)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
        (Work.FTS.NonlinRows.smoothOpen_sub hsmσ hsmσ')) hmem5D) ?_
    exact mul_le_mul_of_nonneg_left hsub hA5pos.le
  -- ## the master Lipschitz estimate for `rhsFun`
  obtain ⟨Lrhs, hLrhspos, hLrhs⟩ := rhsFun_lipschitz_H4 (α := α) (C₀ := C₀) (Ce := Ce)
    (Cs := Cs) (B := max Ce (A * K' n)) (T := T) hα₄ hα₄1 hα hEll hstar hml
    (le_trans (mul_nonneg hA0 hK'0) (le_max_right _ _))
  have hVsub : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T, ∀ σ' ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 4 (fun z θ =>
          Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ z θ
            - Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ' z θ)
        ≤ Lrhs * (A5 * (A5 * KW5 * |σ - σ'|)) := by
    intro k σ hσ σ' hσ'
    have hσT : σ ∈ Set.Icc (0 : ℝ) (Tn n) := ⟨hσ.1, le_trans hσ.2 hTT⟩
    have hσ'T : σ' ∈ Set.Icc (0 : ℝ) (Tn n) := ⟨hσ'.1, le_trans hσ'.2 hTT⟩
    have hVR : Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ
        = Work.FTS.StrongEps.rhsFun α Φs E
            (famOf (fun _ : ℝ => slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ)) 0 := by
      rw [rhsFun_eq_profRHS α Φs E
        (famOf (fun _ : ℝ => slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ)) 0]
      exact rhsFun_eq_profRHS α Φs E (JfamP ρ (e (ι n k)) (G n (ι n k))) σ
    have hVR' : Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ'
        = Work.FTS.StrongEps.rhsFun α Φs E
            (famOf (fun _ : ℝ => slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ')) 0 := by
      rw [rhsFun_eq_profRHS α Φs E
        (famOf (fun _ : ℝ => slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ')) 0]
      exact rhsFun_eq_profRHS α Φs E (JfamP ρ (e (ι n k)) (G n (ι n k))) σ'
    have hfun : (fun z θ =>
          Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ z θ
            - Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ' z θ)
        = fun z θ =>
          Work.FTS.StrongEps.rhsFun α Φs E
              (famOf (fun _ : ℝ => slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ)) 0 z θ
            - Work.FTS.StrongEps.rhsFun α Φs E
              (famOf (fun _ : ℝ => slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ')) 0 z θ := by
      funext z θ
      rw [hVR, hVR']
    rw [hfun]
    refine le_trans (hLrhs _ _ (fun τ hτ => ?_) (fun τ hτ => ?_) 0 ⟨le_rfl, hT.le⟩)
      (mul_le_mul_of_nonneg_left (hProj k σ hσ σ' hσ') hLrhspos.le)
    · exact ⟨(htw k).hC σ hσT |>.reg, hproj_mem6 k σ hσ, (htw k).hC σ hσT,
        (htw k).hb4 σ hσT, hb6p k σ hσ⟩
    · exact ⟨(htw k).hC σ' hσ'T |>.reg, hproj_mem6 k σ' hσ', (htw k).hC σ' hσ'T,
        (htw k).hb4 σ' hσ'T, hb6p k σ' hσ'⟩
  -- ## the pointwise bound for the projected, mollified right-hand side
  obtain ⟨CPz, hCPzpos, hCPz⟩ := PzJeps_abs_le_unif hα.1 hα1 hρ
  have hYabs : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T, ∀ σ' ∈ Set.Icc (0 : ℝ) T,
      ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        |Work.FTS.StrongEps.epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ z θ
            - Work.FTS.StrongEps.epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ' z θ|
          ≤ CPz * Work.Spaces.HkNorm α 4 (fun z θ =>
              Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ z θ
                - Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ' z θ) := by
    intro k σ hσ σ' hσ' z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have hθ : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ0, hθ1⟩
    have hsmσ : Work.FTS.EllipticEst.SmoothOpen
        (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ) := hVsm k σ hσ
    have hsmσ' : Work.FTS.EllipticEst.SmoothOpen
        (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ') := hVsm k σ' hσ'
    have hmemσ : Work.Spaces.HkMem α 4
        (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ) := hVmem4 k σ hσ
    have hmemσ' : Work.Spaces.HkMem α 4
        (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ') := hVmem4 k σ' hσ'
    have hJsmσ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
        (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ)) :=
      Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ (hεpos k)
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsmσ)
    have hJsmσ' : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
        (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ')) :=
      Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ (hεpos k)
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsmσ')
    have hJmemσ : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
        (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ)) :=
      Work.FTS.StrongEps.HkMem_Jeps hρ.moll hαI (hεpos k)
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsmσ) hmemσ
    have hJmemσ' : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
        (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ')) :=
      Work.FTS.StrongEps.HkMem_Jeps hρ.moll hαI (hεpos k)
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsmσ') hmemσ'
    have h1 : Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
            (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ))
          - Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
            (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ'))
        = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
            (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ)
              - Work.FTS.StrongEps.Jeps ρ (e (ι n k))
                (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ')) :=
      Work.FTS.StrongEps.EpsRLX.Pz_sub_eq
        (Work.FTS.StrongEps.EComparison.L12_sub_HkMem hJsmσ hJsmσ' hJmemσ hJmemσ' 0
          (by simp [Work.Spaces.Iz]))
    have h2 : Work.FTS.StrongEps.Jeps ρ (e (ι n k))
            (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ)
          - Work.FTS.StrongEps.Jeps ρ (e (ι n k))
            (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ')
        = Work.FTS.StrongEps.Jeps ρ (e (ι n k)) (fun z θ =>
            Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ z θ
              - Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ' z θ) :=
      Work.FTS.StrongEps.EpsRLX.Jeps_sub_eq hρ.moll (hεpos k) hsmσ hsmσ'
    have hpt : Work.FTS.StrongEps.epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ z θ
        - Work.FTS.StrongEps.epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ' z θ
        = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ (e (ι n k)) (fun z θ =>
            Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ z θ
              - Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ' z θ)) z θ := by
      have hfun : (fun z θ =>
          Work.FTS.StrongEps.epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ z θ
            - Work.FTS.StrongEps.epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ' z θ)
          = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ (e (ι n k)) (fun z θ =>
              Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ z θ
                - Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ' z θ)) := by
        have hpre : (fun z θ =>
            Work.FTS.StrongEps.epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ z θ
              - Work.FTS.StrongEps.epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ' z θ)
            = (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
                  (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ))
                - Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
                  (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ'))) := by
          funext z' θ'
          rfl
        rw [hpre, h1, h2]
      exact congrFun (congrFun hfun z) θ
    rw [hpt]
    exact hCPz (e (ι n k)) (hεI k)
      (fun z θ => Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ z θ
        - Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) σ' z θ)
      (Work.FTS.NonlinRows.smoothOpen_sub hsmσ hsmσ')
      (Work.FTS.GalBasis.hkMem_sub_open α 4 hsmσ hsmσ' hmemσ hmemσ') z θ hz hθ

  -- ## the assembly
  intro z θ hzθ
  have hzθQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hzθ
  have hlimK : ∀ s ∈ Set.Icc (0 : ℝ) T, Filter.Tendsto (fun k : ℕ =>
      Work.FTS.StrongEps.epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s z θ)
      Filter.atTop
      (nhds (Work.FTS.StrongEps.rhsFun α Φs E (Work.FTS.StrongEps.clampQ Fc g₀) s z θ)) :=
    fun s hs => hlim_of_tower n hαI hρ hc₁ hc₂ hEll hstar hml hELL3 hsmΦ hL12g₀ hεe hε0
      hTower hMaj hDec hι hadm hconv hT hTT (z, θ) hzθQ s hs
  have hLC0 : 0 ≤ CPz * (Lrhs * (A5 * (A5 * KW5))) := by
    have h1 : 0 ≤ A5 * KW5 := mul_nonneg hA5pos.le hKW5pos.le
    have h1' : 0 ≤ A5 * (A5 * KW5) := mul_nonneg hA5pos.le h1
    have h2 : 0 ≤ Lrhs * (A5 * (A5 * KW5)) := mul_nonneg hLrhspos.le h1'
    exact mul_nonneg hCPzpos.le h2
  have hLipR : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ s' ∈ Set.Icc (0 : ℝ) T,
      |Work.FTS.StrongEps.rhsFun α Φs E (Work.FTS.StrongEps.clampQ Fc g₀) s z θ
          - Work.FTS.StrongEps.rhsFun α Φs E (Work.FTS.StrongEps.clampQ Fc g₀) s' z θ|
        ≤ CPz * (Lrhs * (A5 * (A5 * KW5))) * |s - s'| := by
    intro s hs s' hs'
    have h1 : Filter.Tendsto (fun k : ℕ =>
        |Work.FTS.StrongEps.epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s z θ
            - Work.FTS.StrongEps.epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s' z θ|)
        Filter.atTop
        (nhds |Work.FTS.StrongEps.rhsFun α Φs E (Work.FTS.StrongEps.clampQ Fc g₀) s z θ
            - Work.FTS.StrongEps.rhsFun α Φs E (Work.FTS.StrongEps.clampQ Fc g₀) s' z θ|) :=
      ((hlimK s hs).sub (hlimK s' hs')).abs
    refine le_of_tendsto h1 (Filter.Eventually.of_forall (fun k => ?_))
    refine le_trans (hYabs k s hs s' hs' z θ hzθ) ?_
    refine le_trans (mul_le_mul_of_nonneg_left (hVsub k s hs s' hs') hCPzpos.le) ?_
    exact le_of_eq (by ring)
  refine LipschitzOnWith.continuousOn (K := ⟨CPz * (Lrhs * (A5 * (A5 * KW5))), hLC0⟩) ?_
  refine lipschitzOnWith_iff_dist_le_mul.mpr ?_
  intro s hs s' hs'
  simp only [NNReal.coe_mk, Real.dist_eq]
  exact hLipR s hs s' hs'

end Work.FTS.StrongEps.E5G
end
