import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.StrongEps.E5Aux3.contDiffOn_two_E_of_EllLimOK3
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.E5G.Xn_JfamP_lip_fam
import Submission.Work.FTS.StrongEps.E5G.hWc_aux
import Submission.Work.FTS.StrongEps.E5G.morrey_five_slots
import Submission.Work.FTS.StrongEps.E5G.muDyn_lamDyn_tendsto_tower
import Submission.Work.FTS.StrongEps.E5G.weak_slots_tendsto_open
import Submission.Work.FTS.StrongEps.EpsE4Thr.epsRHSP_hkMem_fam
import Submission.Work.FTS.StrongEps.EpsRHSPBdd_unif
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup_val
import Submission.Work.FTS.StrongEps.RhsCont
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.NZzero6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzSlot
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS_EllLimOK.ProducerH.pzIterTwo_shiftSing_eq_PhiTil_add
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.RXVP.thLip

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
set_option maxHeartbeats 4000000

/-! ## The target -/

private theorem smoothOpen_sub_dev {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ - g z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h : Function.uncurry (fun z θ => f z θ - g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p - Function.uncurry g p := rfl
  rw [h]
  exact ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf n).sub
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hg n)

private theorem convLocUnifH6_mono_dev {α B B' : ℝ} {G : ℕ → Fn} {f : Fn}
    (h : Work.FTS.StrongEps.ConvLocUnifH6 α B G f) (hle : B ≤ B') :
    Work.FTS.StrongEps.ConvLocUnifH6 α B' G f :=
  ⟨h.1, h.2.1, le_trans h.2.2 hle⟩

private theorem EllPkgK_mono_dev {α : ℝ} {k : ℕ} {Ce Ce' : ℝ} {g Φg : Fn}
    (h : Work.FTS.ClassC.EllPkgK α k Ce g Φg) (hle : Ce ≤ Ce') :
    Work.FTS.ClassC.EllPkgK α k Ce' g Φg := by
  obtain ⟨h1, h2, ⟨hRm, hRb⟩, ⟨hUm, hUb⟩, ⟨hVm, hVb⟩⟩ := h
  have hgnn : 0 ≤ Work.Spaces.HkNorm α k g := Work.Spaces.HkNorm_nonneg α k g
  have hmon : ∀ X : ℝ, X ≤ Ce * Work.Spaces.HkNorm α k g →
      X ≤ Ce' * Work.Spaces.HkNorm α k g :=
    fun X hX => le_trans hX (mul_le_mul_of_nonneg_right hle hgnn)
  exact ⟨h1, h2, ⟨hRm, hmon _ hRb⟩, ⟨hUm, hmon _ hUb⟩, ⟨hVm, hmon _ hVb⟩⟩

private theorem EllPkgGo_mono_dev {α Ce Ce' : ℝ} {g Φg : Fn} (hα : 0 < α)
    (h : Work.FTS.VocabO.EllPkgGo α Ce g Φg) (hle : Ce ≤ Ce') :
    Work.FTS.VocabO.EllPkgGo α Ce' g Φg := by
  obtain ⟨h1, h2, ⟨hRm, hRb⟩, ⟨hUm, hUb⟩, ⟨hVm, hVb⟩, hv, ⟨hTm, hTb⟩⟩ := h
  have hgnn : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hαp : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  refine ⟨h1, h2, ⟨hRm, ?_⟩, ⟨hUm, ?_⟩, ⟨hVm, ?_⟩, hv, ⟨hTm, ?_⟩⟩
  · exact le_trans hRb (mul_le_mul_of_nonneg_right hle hgnn)
  · exact le_trans hUb (mul_le_mul_of_nonneg_right hle hgnn)
  · exact le_trans hVb (mul_le_mul_of_nonneg_right hle hgnn)
  · refine le_trans hTb ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hαp) hgnn

theorem hapx_of_tower {α C₀ Ce Cs T : ℝ} {K' : ℕ → ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
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
    ∀ T' : ℝ, 0 < T' → T' ≤ T →
      Work.FTS.StrongEps.LimApproxOn α C₀ T' Φs E (Work.FTS.StrongEps.clampQ Fc g₀) := by
  intro T' hT'0 hT'T
  classical
  have hTn : 0 < Tn n := Tn_pos n
  have hT'Tn : T' ≤ Tn n := le_trans hT'T hTT
  have htw : ∀ k : ℕ, TowerAt α C₀ ρ Φs E g₀ n (e (ι n k)) (K' n) (G n (ι n k)) :=
    fun k => hTower n (ι n k) (hadm k)
  have hεI : ∀ k : ℕ, e (ι n k) ∈ Set.Ioc (0 : ℝ) 1 := fun k => hεe (ι n k)
  have hεp : ∀ k : ℕ, 0 < e (ι n k) := fun k => (hεI k).1
  have hε0' : Filter.Tendsto (fun k : ℕ => e (ι n k)) Filter.atTop (nhds 0) :=
    hε0.comp hι.tendsto_atTop
  have hK'0 : 0 ≤ K' n := le_trans (Work.Spaces.HkNorm_nonneg α 6 (slice (G n n) 0))
    ((hTower n n le_rfl).hb6 0 ⟨le_rfl, hTn.le⟩)
  -- ## the raised elliptic constant and the projected `ℋ⁶`-bound
  obtain ⟨A, hA0, hA⟩ := Work.FTS.StrongEps.HkNorm_JfamP_le (ρ := ρ) hρ
  have hEll' : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α (max Ce (A * K' n)) u (E u) ∧
        Work.FTS.ClassC.EllPkgK α 6 (max Ce (A * K' n)) u (E u) :=
    fun u hu => ⟨EllPkgGo_mono_dev hα.1 (hEll u hu).1 (le_max_left _ _),
      EllPkgK_mono_dev (hEll u hu).2 (le_max_left _ _)⟩
  have hb6pT : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) (Tn n),
      Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) τ)
        ≤ max Ce (A * K' n) := by
    intro k τ hτ
    have h1 := hA (α := α) (ε := e (ι n k)) hα (hεI k) (g := G n (ι n k)) (s := τ)
      (fun m => ((htw k).hsm τ hτ).forall m) ((htw k).hmem6 τ hτ)
    exact le_trans (le_trans h1.2 (mul_le_mul_of_nonneg_left ((htw k).hb6 τ hτ) hA0))
      (le_max_right _ _)
  have hb6p : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T',
      Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) τ)
        ≤ max Ce (A * K' n) :=
    fun k τ hτ => hb6pT k τ ⟨hτ.1, le_trans hτ.2 hT'Tn⟩
  -- ## the `ε`-uniform `ℋ⁴`-bound of the scheme's right-hand side
  obtain ⟨R4, hR4pos, hR4⟩ :=
    Work.FTS.StrongEps.EpsRHSPBdd_unif (α := α) (C₀ := C₀) (Ce := max Ce (A * K' n))
      (Cs := Cs) (B := K' n) (ρ := ρ) (Φs := Φs) (E := E) hα hρ hEll' hstar hml hK'0
  -- ## smoothness, honesty and size of `epsRHSP` along the extraction
  have hRHS : ∀ k : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T',
      Work.FTS.EllipticEst.SmoothOpen (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s) ∧
      Work.Spaces.HkMem α 6 (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s) ∧
      Work.Spaces.HkNorm α 4 (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s) ≤ R4 := by
    intro k s hs
    have hsT : s ∈ Set.Icc (0 : ℝ) (Tn n) := ⟨hs.1, le_trans hs.2 hT'Tn⟩
    have hsk := Work.FTS.StrongEps.EpsE4Thr.epsRHSP_smoothOpen_hkMem6_fam
      (α := α) (C₀ := C₀) (Ce := max Ce (A * K' n)) (Cs := Cs) (B := K' n)
      (ρ := ρ) (Φs := Φs) (E := E) (g := G n (ι n k)) (ε := e (ι n k)) (T := T')
      hα hρ (hεp k) (hεI k).2 hEll' hstar hml hK'0
      (fun s hs => (htw k).hsm s ⟨hs.1, le_trans hs.2 hT'Tn⟩)
      (fun s hs => (htw k).hmem6 s ⟨hs.1, le_trans hs.2 hT'Tn⟩)
      (fun s hs => (htw k).hb6 s ⟨hs.1, le_trans hs.2 hT'Tn⟩)
      (fun s hs => (htw k).hC s ⟨hs.1, le_trans hs.2 hT'Tn⟩)
      (fun s hs => (htw k).hb4 s ⟨hs.1, le_trans hs.2 hT'Tn⟩)
    refine ⟨(hsk s hs).1, (hsk s hs).2, ?_⟩
    have hR := hR4 (e (ι n k)) (hεI k) s (slice (G n (ι n k)) s)
      ((htw k).hsm s hsT) ((htw k).hmem6 s hsT) ((htw k).hb6 s hsT)
      (by simpa only [slice_JfamP] using (htw k).hC s hsT)
      (by simpa only [slice_JfamP] using (htw k).hb4 s hsT)
    simpa only [Work.FTS.StrongEps.epsRHSP_eq_slice α ρ (e (ι n k)) Φs E s (G n (ι n k))]
      using hR
  -- ## the slot bounds of `epsRHSP` (per extraction index)
  have hslot : ∀ k : ℕ, ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T', ∀ (j i : ℕ), j + i ≤ 4 → ∀ p : ℝ × ℝ, p ∈ K →
        |Work.Spaces.mixed j i (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s) p.1 p.2|
          ≤ C := by
    intro k K hK hKQ
    obtain ⟨KW, hKW0, hKW⟩ :=
      Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam (α := α) (C₀ := C₀)
        (Ce := max Ce (A * K' n)) (Cs := Cs) (T := T') (ρ := ρ) (Φs := Φs) (E := E)
        (G := fun k => G n (ι n k)) (ε := fun k => e (ι n k))
        hα hEll' hstar hml
        (fun k s hs => (htw k).hC s ⟨hs.1, le_trans hs.2 hT'Tn⟩)
        (fun k s hs => (htw k).hb4 s ⟨hs.1, le_trans hs.2 hT'Tn⟩)
        (fun k s hs => hb6p k s hs)
    obtain ⟨K'', hK''c, hK''Q, hKK'', hshift⟩ :=
      Work.FTS.StrongEps.exists_shift_window_compact (ε := 1) one_pos le_rfl hK hKQ
    obtain ⟨B'', hB''0, hB''⟩ :=
      Work.FTS.StrongEps.epsWP_sup_le_fam (α := α) (C₀ := C₀) (Ce := max Ce (A * K' n))
        (Cs := Cs) (T := T') (ρ := ρ) (Φs := Φs) (E := E)
        (G := fun k => G n (ι n k)) (ε := fun k => e (ι n k))
        hα hρ (fun k => hεI k) hT'0.le hc₁ hc₂ hEll' hstar hml
        (fun k s hs => (htw k).hC s ⟨hs.1, le_trans hs.2 hT'Tn⟩)
        (fun k s hs => (htw k).hb4 s ⟨hs.1, le_trans hs.2 hT'Tn⟩)
        (fun k s hs => hb6p k s hs) hK''c hK''Q
    obtain ⟨C, hC0, hCb⟩ := Work.FTS.StrongEps.EpsRHSP_slotSup_val
      (α := α) (T := T') (ε := e (ι n k)) (ρ := ρ) (Φs := Φs) (E := E) (g := G n (ι n k))
      hα hρ (hεI k)
      (fun s hs => Work.FTS.StrongEps.smoothOpen_epsWP (α := α) (C₀ := C₀)
        (Ce := max Ce (A * K' n)) (Cs := Cs) (T := T') (ρ := ρ) (Φs := Φs) (E := E)
        (g := G n (ι n k)) (ε := e (ι n k)) hα hEll' hstar
        (fun s hs => (htw k).hC s ⟨hs.1, le_trans hs.2 hT'Tn⟩) s hs)
      hK hKQ
      ⟨K'', hK''c, hK''Q, hKK'', hshift, B'', hB''0.le,
        fun s hs p hp => hB'' k s hs p hp⟩
      ⟨KW, hKW0.le, fun s hs => hKW k s hs⟩
    exact ⟨C, fun s hs j i hji p hp => hCb j i hji s hs p hp⟩
  -- ## the per-slice regularity of the raw tower slices
  have hreg : ∀ k : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T',
      Work.FTS.EllipticEst.SmoothOpen (slice (G n (ι n k)) s) ∧
        Work.Spaces.HkMem α 4 (slice (G n (ι n k)) s) := by
    intro k s hs
    have hsT : s ∈ Set.Icc (0 : ℝ) (Tn n) := ⟨hs.1, le_trans hs.2 hT'Tn⟩
    exact ⟨(htw k).hsm s hsT,
      Work.FTS.OpenPkg.HkMem_mono_open ((htw k).hsm s hsT) 4 (by norm_num)
        ((htw k).hmem6 s hsT)⟩
  have hsmD : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T', ∀ τ' ∈ Set.Icc (0 : ℝ) T',
      Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => slice (G n (ι n k)) τ z θ - slice (G n (ι n k)) τ' z θ) :=
    fun k τ hτ τ' hτ' => smoothOpen_sub_dev (hreg k τ hτ).1 (hreg k τ' hτ').1
  have hsl : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T', ∀ τ' ∈ Set.Icc (0 : ℝ) T',
      Work.Spaces.HkMem α 4
          (fun z θ => slice (G n (ι n k)) τ z θ - slice (G n (ι n k)) τ' z θ) ∧
        Work.FTS.Nonlin.Xn α
          (fun z θ => slice (G n (ι n k)) τ z θ - slice (G n (ι n k)) τ' z θ)
          ≤ R4 * |τ - τ'| := by
    intro k τ hτ τ' hτ'
    have hmem : Work.Spaces.HkMem α 4
        (fun z θ => slice (G n (ι n k)) τ z θ - slice (G n (ι n k)) τ' z θ) := by
      have hsum := Work.FTS.EllipticEst.HkMem_add_open (hreg k τ hτ).1
        (Work.FTS.GalBasis.smoothOpen_neg (hreg k τ' hτ').1) (hreg k τ hτ).2
        (Work.FTS.StrongEps.EpsLocalPStar.hkMem_neg_fts (hreg k τ' hτ').2)
      exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hsum
        (fun z _ θ _ => by ring)
    refine ⟨hmem, ?_⟩
    have hsol : Work.FTS.StrongEps.IsEpsSolP α ρ (e (ι n k)) T' Φs E g₀ (G n (ι n k)) :=
      IsEpsSolP_mono (htw k).hsol hT'Tn
    have hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        ContinuousOn (fun s : ℝ => epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s z θ)
          (Set.Icc (0 : ℝ) T') :=
      fun z θ hzθ =>
        ((continuousOn_epsRHSP_of_regP hTn (htw k).hsol (htw k).toEpsRegP) (z, θ) hzθ).mono
          (Set.Icc_subset_Icc le_rfl hT'Tn)
    have h4 : ∀ s ∈ Set.Icc (0 : ℝ) T',
        Work.Spaces.HkMem α 4 (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s) :=
      fun s hs => Work.FTS.OpenPkg.HkMem_mono_open (hRHS k s hs).1 4 (by norm_num)
        (hRHS k s hs).2.1
    have hb4 : ∀ s ∈ Set.Icc (0 : ℝ) T',
        Work.Spaces.HkNorm α 4 (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s) ≤ R4 :=
      fun s hs => (hRHS k s hs).2.2
    exact slice_lip_norm hsol hcont (fun s hs => (hRHS k s hs).1) h4 hb4 (hslot k) τ hτ τ' hτ'
  obtain ⟨L, hLpos, hLip⟩ := Xn_JfamP_lip_fam (α := α) (T := T') (B := R4)
    (ρ := ρ) (Φs := Φs) (E := E) (G := fun k => G n (ι n k)) (ε := fun k => e (ι n k))
    hρ hα (fun k => hεI k) hreg hsmD hsl
  -- ## `hl12` along the extraction
  have hl12 : ∀ τ ∈ Set.Icc (0 : ℝ) (Tn n), Filter.Tendsto (fun k : ℕ =>
      Work.Construction.L12 (Jeps ρ (e (ι n k)) (slice (G n (ι n k)) τ)) 0)
      Filter.atTop (nhds 0) :=
    fun τ hτ => HL12RawTower (α := α) (C₀ := C₀) (Ce := max Ce (A * K' n)) (Cs := Cs)
      (T := Tn n) (B := K' n) hα hρ hc₁ hc₂ hEll' hstar hml hεI hε0' hTn hL12g₀
      (fun k => (htw k).hsol) (fun k => (htw k).hjoint) (fun k τ hτ => (htw k).hsm τ hτ)
      (fun k τ hτ => (htw k).hmem6 τ hτ) (fun k τ hτ => (htw k).hb6 τ hτ)
      (fun k τ hτ => (htw k).hC τ hτ) (fun k τ hτ => (htw k).hb4 τ hτ)
      (fun k τ hτ => hb6pT k τ hτ) (s := τ) hτ
  -- ## the jet convergence
  have hjet : ∀ τ ∈ Set.Icc (0 : ℝ) T', ∀ (j i : ℕ), j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun k : ℕ =>
          Work.Spaces.mixed j i (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) τ) z θ)
        Filter.atTop (nhds (Work.Spaces.mixed j i (slice (clampQ Fc g₀) τ) z θ)) := by
    intro τ hτ j i hji z θ hzθ
    have hτT : τ ∈ Set.Icc (0 : ℝ) (Tn n) := ⟨hτ.1, le_trans hτ.2 hT'Tn⟩
    exact mixed_JfamP_tendsto (ρ := ρ) hρ
      (G := fun k => G n (ι n k)) (g := clampQ Fc g₀) (ε := fun k => e (ι n k)) (τ := τ)
      (fun k m => ((htw k).hsm τ hτT).forall m)
      (Work.FTS.StrongEps.E5Asm.ConvLocUnifH6.clampQ_congr (hconv τ hτT))
      hεp hε0' (hl12 τ hτT) hzθ hji
  -- ## the elliptic image of the limit slice is `C¹`
  have hsmE : ∀ τ ∈ Set.Icc (0 : ℝ) T',
      ContDiffOn ℝ 1 (Function.uncurry (E (slice (clampQ Fc g₀) τ)))
        Work.FTS.EllipticEst.Q0 := by
    intro τ hτ
    have hτT : τ ∈ Set.Icc (0 : ℝ) (Tn n) := ⟨hτ.1, le_trans hτ.2 hT'Tn⟩
    have h2 := contDiffOn_two_E_of_EllLimOK3 (α := α) (E := E) hELL3
      (fn := fun k => slice (JfamP ρ (e (ι n k)) (G n (ι n k))) τ)
      (f := slice (clampQ Fc g₀) τ) (B := max Ce (A * K' n))
      (fun k => (htw k).hC τ hτT) (fun k => hb6pT k τ hτT)
      (Work.FTS.StrongEps.E5Asm.ConvLocUnifH6.clampQ_congr (hconv τ hτT)).contDiffOn
      (fun j i hji z θ hzθ => hjet τ hτ j i hji z θ hzθ)
    exact h2.of_le (by norm_num)
  -- ## the modulation clause
  have hmu : ∀ τ ∈ Set.Icc (0 : ℝ) T',
      Filter.Tendsto (fun k : ℕ =>
          Work.FTS.Galerkin.muDyn α
            (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ (e (ι n k)) (G n (ι n k))))
            (JfamP ρ (e (ι n k)) (G n (ι n k))) τ)
        Filter.atTop (nhds (Work.FTS.Galerkin.muDyn α
          (Work.FTS.Nonlin.PsiCan Φs E (clampQ Fc g₀)) (clampQ Fc g₀) τ)) := by
    intro τ hτ
    have hτT : τ ∈ Set.Icc (0 : ℝ) (Tn n) := ⟨hτ.1, le_trans hτ.2 hT'Tn⟩
    exact (muDyn_lamDyn_tendsto_tower (α := α) (C₀ := C₀) (Ce := max Ce (A * K' n))
      (Cs := Cs) (T := T') (B := max (K' n) (max Ce (A * K' n))) (ρ := ρ) (Φs := Φs)
      (E := E)
      (ε := fun k => e (ι n k)) (G := fun k => G n (ι n k)) (g := clampQ Fc g₀)
      (Maj := Maj n) (s := τ)
      hα hρ hEll' hstar hml hELL3 hsmΦ (hsmE τ hτ) hεI hε0'
      (fun k m => ((htw k).hsm τ hτT).forall m)
      (convLocUnifH6_mono_dev
        (Work.FTS.StrongEps.E5Asm.ConvLocUnifH6.clampQ_congr (hconv τ hτT))
        (le_max_left _ _))
      (fun k => (htw k).hC τ hτT) (fun k => (htw k).hb4 τ hτT)
      (fun k => le_trans (hb6pT k τ hτT) (le_max_right _ _))
      (hMaj n) (fun k => hDec (ι n k) (hadm k) τ hτT) (hl12 τ hτT)).1
  -- ## the approximation clause
  exact ⟨fun k => JfamP ρ (e (ι n k)) (G n (ι n k)), max Ce (A * K' n), L,
    (fun k τ hτ => ⟨(htw k).hC τ ⟨hτ.1, le_trans hτ.2 hT'Tn⟩,
      (htw k).hb4 τ ⟨hτ.1, le_trans hτ.2 hT'Tn⟩, hb6p k τ hτ⟩),
    (fun k τ hτ τ' hτ' => hLip k τ hτ τ' hτ'),
    (fun τ hτ j i hji z θ hzθ => hjet τ hτ j i hji z θ hzθ),
    (fun τ hτ => hmu τ hτ)⟩

end Work.FTS.StrongEps.E5G
