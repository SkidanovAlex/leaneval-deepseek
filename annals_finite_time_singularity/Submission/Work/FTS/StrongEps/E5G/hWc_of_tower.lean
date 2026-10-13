import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E5G.hlim_of_tower
import Submission.Work.FTS.StrongEps.E5G.hapx_of_tower
import Submission.Work.FTS.StrongEps.E5G.rhsFun_lipschitz_H4
import Submission.Work.FTS.StrongEps.E5G.epsWP_hkMem5_bnd_fam
import Submission.Work.FTS.StrongEps.E5G.slice_lip5_norm
import Submission.Work.FTS.StrongEps.E5G.slice_lip_norm
import Submission.Work.FTS.StrongEps.E5G.Xn_JfamP_lip
import Submission.Work.FTS.StrongEps.E5G.morrey_four
import Submission.Work.FTS.StrongEps.E5G.Jeps_tendsto_of_modulus
import Submission.Work.FTS.StrongEps.E5G.epsWP_equicont_tower
import Submission.Work.FTS.StrongEps.E5G.hkNorm_Pz_le_five
import Submission.Work.FTS.StrongEps.E5G.EpsRHSP_slotSup_val5
import Submission.Work.FTS.StrongEps.E5G.epsRHSP_hkMem5_bnd_fam
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.epsRHSP_hkMem_fam
import Submission.Work.FTS.StrongEps.exists_shift_window_compact
import Submission.Work.FTS.StrongEps.epsWP_sup_le_fam
import Submission.Work.FTS.StrongEps.E5Clamp
import Submission.Work.FTS.StrongEps.E5G.Coherence
import Submission.Work.FTS.StrongEps.E5G.hWc_aux
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn Fam slice)

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## The target -/

theorem hWc_of_tower {α₄ α C₀ Ce Cs Cs6 T : ℝ} {K' : ℕ → ℝ} {ρ : ℝ × ℝ → ℝ}
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
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        Work.FTS.StrongEps.rhsFun α Φs E (Work.FTS.StrongEps.clampQ Fc g₀) p.2.2 p.1 p.2.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T) := by
  classical
  have hα0 : 0 < α := hα.1
  have hα1 : α ∈ Set.Ioc (0 : ℝ) 1 := ⟨hα.1, le_trans hα.2 hα₄1⟩
  have hαle : α ≤ 1 := hα1.2
  have hTn : 0 < Tn n := Tn_pos n
  -- ## the extracted tower
  let fam : ℕ → Fam := fun k => G n (ι n k)
  let eps : ℕ → ℝ := fun k => e (ι n k)
  have htw : ∀ k : ℕ, TowerAt α C₀ ρ Φs E g₀ n (eps k) (K' n) (fam k) :=
    fun k => hTower n (ι n k) (hadm k)
  have hεI : ∀ k : ℕ, eps k ∈ Set.Ioc (0 : ℝ) 1 := fun k => hεe (ι n k)
  have hεp : ∀ k : ℕ, 0 < eps k := fun k => (hεI k).1
  have hK'0 : 0 ≤ K' n := le_trans (Work.Spaces.HkNorm_nonneg α 6 (slice (G n n) 0))
    ((hTower n n le_rfl).hb6 0 ⟨le_rfl, hTn.le⟩)
  -- ## the tower data on `[0,T]`
  have hsmK : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T, ∀ m : ℕ,
      ContDiffOn ℝ m (Function.uncurry (slice (fam k) σ)) Work.FTS.StrongEps.Quad :=
    fun k σ hσ m => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
      ((htw k).hsm σ ⟨hσ.1, le_trans hσ.2 hTT⟩) m
  have hsmT : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (slice (fam k) σ) :=
    fun k σ hσ => (htw k).hsm σ ⟨hσ.1, le_trans hσ.2 hTT⟩
  have hmem6 : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α 6 (slice (fam k) σ) :=
    fun k σ hσ => (htw k).hmem6 σ ⟨hσ.1, le_trans hσ.2 hTT⟩
  have hb6K : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.StrongGlobal.Xn6 α (slice (fam k) σ) ≤ K' n :=
    fun k σ hσ => (htw k).hb6 σ ⟨hσ.1, le_trans hσ.2 hTT⟩
  have hCT : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.ClassC.ClassC α (slice (JfamP ρ (eps k) (fam k)) σ) :=
    fun k σ hσ => (htw k).hC σ ⟨hσ.1, le_trans hσ.2 hTT⟩
  have hb4T : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (slice (JfamP ρ (eps k) (fam k)) σ) ≤ C₀ * α ^ 2 :=
    fun k σ hσ => (htw k).hb4 σ ⟨hσ.1, le_trans hσ.2 hTT⟩
  -- ## the raised elliptic constant and the projected `ℋ⁶`-data
  obtain ⟨A, hA0, hA⟩ := Work.FTS.StrongEps.HkNorm_JfamP_le (ρ := ρ) hρ
  have hM0 : 0 ≤ max Ce (A * K' n) := le_trans (mul_nonneg hA0 hK'0) (le_max_right _ _)
  have hEll' : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α (max Ce (A * K' n)) u (E u) ∧
        Work.FTS.ClassC.EllPkgK α 6 (max Ce (A * K' n)) u (E u) :=
    fun u hu => ⟨Work.FTS.ClassC.EllPkgGo_mono hα0 (hEll u hu).1 (le_max_left _ _),
      Work.FTS.ClassC.EllPkgK_mono (hEll u hu).2 (le_max_left _ _)⟩
  have hproj : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 6 (slice (JfamP ρ (eps k) (fam k)) σ) ∧
        Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (eps k) (fam k)) σ)
          ≤ max Ce (A * K' n) := by
    intro k σ hσ
    have h1 := hA (α := α) (ε := eps k) hα1 (hεI k) (g := fam k) (s := σ)
      (hsmK k σ hσ) (hmem6 k σ hσ)
    exact ⟨h1.1, le_trans (le_trans h1.2 (mul_le_mul_of_nonneg_left (hb6K k σ hσ) hA0))
      (le_max_right _ _)⟩
  have hsmP : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (slice (JfamP ρ (eps k) (fam k)) σ) :=
    fun k σ hσ => Work.FTS.StrongEps.EpsSqTools.LinAux.smoothOpen_Pz
      (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ (hεp k) (hsmK k σ hσ))
  -- ## the `ℋ⁴`-data of the scheme's pre-mollified right-hand side
  obtain ⟨KW, hKW0, hKW⟩ := Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam (α := α) (C₀ := C₀)
    (Ce := max Ce (A * K' n)) (Cs := Cs) (T := T) (ρ := ρ) (Φs := Φs) (E := E)
    (G := fam) (ε := eps) hα1 hEll' hstar hml hCT hb4T (fun k s hs => (hproj k s hs).2)
  have hsmW : ∀ k : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s) :=
    fun k s hs => Work.FTS.StrongEps.smoothOpen_epsWP (α := α) (C₀ := C₀)
      (Ce := max Ce (A * K' n))
      (Cs := Cs) (T := T) (ρ := ρ) (Φs := Φs) (E := E) (g := fam k) (ε := eps k)
      hα1 hEll' hstar (fun s hs => hCT k s hs) s hs
  have hmemW : ∀ k : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s) :=
    fun k s hs => (hKW k s hs).1
  have hbndW : ∀ k : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s) ≤ KW :=
    fun k s hs => (hKW k s hs).2
  -- ## the pointwise convergence of the approximants to the clamped limit
  have hpt : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → ∀ s ∈ Set.Icc (0 : ℝ) T,
      Filter.Tendsto (fun k : ℕ => Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s p.1 p.2)
        Filter.atTop (nhds (Work.FTS.StrongEps.rhsFun α Φs E
          (Work.FTS.StrongEps.clampQ Fc g₀) s p.1 p.2)) :=
    fun p hp s hs => epsWP_tendsto_tower n hα1 hρ hc₁ hc₂ hEll hstar hml hELL3 hsmΦ hL12g₀
      hεe hε0 hTower hMaj hDec hι hadm hconv hT hTT hp hs
  -- ## the spatial equicontinuity of the approximants (uniform in `k` and `s`)
  have hequi : ∀ {K : Set (ℝ × ℝ)}, IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ p ∈ K, ∀ q ∈ K,
        |Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s p.1 p.2
          - Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s q.1 q.2|
          ≤ C * Real.sqrt ‖p - q‖ := by
    intro K hK hKQ
    obtain ⟨C, hCpos, hCB⟩ := epsWP_equicont_tower (α := α) (B4 := KW) (T := T) (ρ := ρ)
      (Φs := Φs) (E := E) (ε := eps) (G := fam) (K := K) hα1 hK hKQ hsmW hmemW hbndW
    exact ⟨C * (1 + KW), mul_pos hCpos (by linarith), fun k s hs p hp q hq =>
      hCB k s hs p hp q hq⟩
  -- ## the level-`5` honesty and bound of the scheme's right-hand side
  obtain ⟨B5, hB5pos, hB5⟩ := epsRHSP_hkMem5_bnd_fam (α := α) (C₀ := C₀)
    (Ce := max Ce (A * K' n)) (Cs := Cs) (Cs6 := Cs6) (T := T) (ρ := ρ) (Φs := Φs)
    (E := E) (G := fam) (ε := eps) hα1 hρ hεI hEll' hstar hstar6 hml hCT hb4T
    (fun k s hs => (hproj k s hs).2)
  -- ## the value bound of the pre-mollified right-hand side on a compact window
  have hval : ∀ {K : Set (ℝ × ℝ)}, IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ B : ℝ, 0 < B ∧ ∀ k : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ p ∈ K,
        |Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s p.1 p.2| ≤ B :=
    fun {K} hK hKQ => Work.FTS.StrongEps.epsWP_sup_le_fam (α := α) (C₀ := C₀)
      (Ce := max Ce (A * K' n)) (Cs := Cs) (T := T) (ρ := ρ) (Φs := Φs) (E := E)
      (G := fam) (ε := eps) hα1 hρ hεI hT.le hc₁ hc₂ hEll' hstar hml hCT hb4T
      (fun k s hs => (hproj k s hs).2) hK hKQ
  -- ## the `ℋ⁵`-Lipschitzity of the tower slices in the fake time, uniform in `k`
  have hraw5 : ∀ k : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ s' ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 5 (fun z θ => slice (fam k) s z θ - slice (fam k) s' z θ)
        ≤ B5 * |s - s'| := by
    intro k s hs s' hs'
    refine Work.FTS.StrongEps.E5G.slice_lip5_norm (α := α) (T := T) (ε := eps k) (B := B5)
      (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀) (g := fam k)
      (Work.FTS.StrongEps.E5G.IsEpsSolP_mono (htw k).hsol hTT) ?_ ?_ ?_ ?_ ?_ s hs s' hs'
    · intro z θ hzθ
      exact (Work.FTS.StrongEps.continuousOn_epsRHSP_of_regP hTn (htw k).hsol
        (htw k).toEpsRegP (z, θ) hzθ).mono (Set.Icc_subset_Icc le_rfl hTT)
    · intro σ hσ
      exact (Work.FTS.StrongEps.EpsE4Thr.epsRHSP_smoothOpen_hkMem6_fam (α := α) (C₀ := C₀)
        (Ce := max Ce (A * K' n)) (Cs := Cs) (B := K' n) (ρ := ρ) (Φs := Φs) (E := E)
        (g := fam k) (ε := eps k) (T := T) hα1 hρ (hεp k) (hεI k).2 hEll' hstar hml hK'0
        (hsmT k) (hmem6 k) (hb6K k) (fun σ hσ => hCT k σ hσ) (fun σ hσ => hb4T k σ hσ)
        σ hσ).1
    · intro σ hσ
      exact (hB5 k σ hσ).1
    · intro σ hσ
      exact (hB5 k σ hσ).2
    · intro K hK hKQ
      obtain ⟨K', hK'c, hK'Q, hKK', hshift⟩ :=
        Work.FTS.StrongEps.exists_shift_window_compact (ε := 1) one_pos le_rfl hK hKQ
      obtain ⟨B, hBpos, hBle⟩ := hval (K := K') hK'c hK'Q
      obtain ⟨C5, hC5, hslot⟩ := Work.FTS.StrongEps.E5G.EpsRHSP_slotSup_val5
        (α := α) (T := T) (ε := eps k)
        (ρ := ρ) (Φs := Φs) (E := E) (g := fam k) hα1 hρ (hεI k)
        (hsmW k) hK hKQ
        ⟨K', hK'c, hK'Q, hKK', hshift, B, hBpos.le, fun s hs p hp => hBle k s hs p hp⟩
        ⟨KW, hKW0.le, fun s hs => ⟨(hKW k s hs).1, (hKW k s hs).2⟩⟩
      exact ⟨C5, fun s hs j i hji p hp => hslot j i hji s hs p hp⟩
  -- ## the projected `ℋ⁵`-bound and the master Lipschitzity
  obtain ⟨CW, hCWpos, hCW⟩ := hkNorm5_Wp_sub_le_fam (α := α) (ρ := ρ) hρ hα1 hεI
  obtain ⟨L, hLpos, hL⟩ := Work.FTS.StrongEps.E5G.rhsFun_lipschitz_H4 (α := α) (C₀ := C₀)
    (Ce := max Ce (A * K' n)) (Cs := Cs) (B := max Ce (A * K' n)) (T := T) (α₄ := α₄)
    hα₄ hα₄1 hα hEll' hstar hml hM0
  have hproj5 : ∀ k : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ s' ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 5 (fun z θ => slice (JfamP ρ (eps k) (fam k)) s z θ
          - slice (JfamP ρ (eps k) (fam k)) s' z θ)
        ≤ CW * Work.Spaces.HkNorm α 5 (fun z θ => slice (fam k) s z θ - slice (fam k) s' z θ) :=
    fun k s hs s' hs' => hCW k (hsmT k s hs) (hsmT k s' hs') (hmem6 k s hs) (hmem6 k s' hs')
  have hlip4 : ∀ k : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ s' ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 4 (fun z θ => Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s z θ
          - Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s' z θ)
        ≤ (L * CW * B5) * |s - s'| := by
    intro k s hs s' hs'
    have hdata₁ : ∀ τ ∈ Set.Icc (0 : ℝ) T,
        Work.FTS.EllipticEst.SmoothOpen (slice (JfamP ρ (eps k) (fam k)) τ) ∧
          Work.Spaces.HkMem α 6 (slice (JfamP ρ (eps k) (fam k)) τ) ∧
          Work.FTS.ClassC.ClassC α (slice (JfamP ρ (eps k) (fam k)) τ) ∧
          Work.FTS.Nonlin.Xn α (slice (JfamP ρ (eps k) (fam k)) τ) ≤ C₀ * α ^ 2 ∧
          Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (eps k) (fam k)) τ)
            ≤ max Ce (A * K' n) :=
      fun τ hτ => ⟨hsmP k τ hτ, (hproj k τ hτ).1, hCT k τ hτ, hb4T k τ hτ, (hproj k τ hτ).2⟩
    have hdata₂ : ∀ τ ∈ Set.Icc (0 : ℝ) T,
        Work.FTS.EllipticEst.SmoothOpen
            (slice (fun z θ _ => slice (JfamP ρ (eps k) (fam k)) s' z θ) τ) ∧
          Work.Spaces.HkMem α 6 (slice (fun z θ _ => slice (JfamP ρ (eps k) (fam k)) s' z θ) τ) ∧
          Work.FTS.ClassC.ClassC α
            (slice (fun z θ _ => slice (JfamP ρ (eps k) (fam k)) s' z θ) τ) ∧
          Work.FTS.Nonlin.Xn α
              (slice (fun z θ _ => slice (JfamP ρ (eps k) (fam k)) s' z θ) τ) ≤ C₀ * α ^ 2 ∧
          Work.FTS.StrongGlobal.Xn6 α
              (slice (fun z θ _ => slice (JfamP ρ (eps k) (fam k)) s' z θ) τ)
            ≤ max Ce (A * K' n) :=
      fun τ _ => hdata₁ s' hs'
    have hkey := hL (JfamP ρ (eps k) (fam k))
      (fun z θ _ => slice (JfamP ρ (eps k) (fam k)) s' z θ) hdata₁ hdata₂ s hs
    have hrhs : (fun z θ => Work.FTS.StrongEps.rhsFun α Φs E (JfamP ρ (eps k) (fam k)) s z θ
          - Work.FTS.StrongEps.rhsFun α Φs E
              (fun z θ _ => slice (JfamP ρ (eps k) (fam k)) s' z θ) s z θ)
        = (fun z θ => Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s z θ
            - Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s' z θ) := by
      have h1 : Work.FTS.StrongEps.rhsFun α Φs E (JfamP ρ (eps k) (fam k)) s
          = Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s := rfl
      have h2 : Work.FTS.StrongEps.rhsFun α Φs E
            (fun z θ _ => slice (JfamP ρ (eps k) (fam k)) s' z θ) s
          = Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s' := by
        rw [Work.FTS.StrongEps.E5G.rhsFun_eq_profRHS α Φs E
              (fun z θ _ => slice (JfamP ρ (eps k) (fam k)) s' z θ) s]
        rfl
      rw [h1, h2]
    have hkey' : Work.Spaces.HkNorm α 4 (fun z θ =>
          Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s z θ
          - Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s' z θ)
        ≤ L * Work.Spaces.HkNorm α 5 (fun z θ => slice (JfamP ρ (eps k) (fam k)) s z θ
            - slice (JfamP ρ (eps k) (fam k)) s' z θ) := by
      rw [hrhs] at hkey
      exact hkey
    calc Work.Spaces.HkNorm α 4 (fun z θ =>
            Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s z θ
            - Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s' z θ)
        ≤ L * Work.Spaces.HkNorm α 5 (fun z θ => slice (JfamP ρ (eps k) (fam k)) s z θ
            - slice (JfamP ρ (eps k) (fam k)) s' z θ) := hkey'
      _ ≤ L * (CW * Work.Spaces.HkNorm α 5 (fun z θ => slice (fam k) s z θ - slice (fam k) s' z θ)) :=
          mul_le_mul_of_nonneg_left (hproj5 k s hs s' hs') hLpos.le
      _ ≤ L * (CW * (B5 * |s - s'|)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hraw5 k s hs s' hs') hCWpos.le) hLpos.le
      _ = (L * CW * B5) * |s - s'| := by ring
  -- ## the temporal Lipschitzity of the approximants at a point of the quadrant
  have htime : ∃ Ct : ℝ, 0 < Ct ∧ ∀ k : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ s' ∈ Set.Icc (0 : ℝ) T,
      ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
        |Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s p.1 p.2
          - Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s' p.1 p.2| ≤ Ct * |s - s'| := by
    obtain ⟨Cpt, hCpt0, hCpt⟩ :=
      Work.FTS.StrongEps.EpsLocalPStar.pointwise_le_HkNorm hα0 hαle
    have hprod : 0 < L * CW * B5 := by positivity
    refine ⟨(Cpt + 1) * (L * CW * B5), by positivity, ?_⟩
    intro k s hs s' hs' p hp
    have hpQ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hmem : Work.Spaces.HkMem α 4 (fun z θ =>
        Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s z θ
          - Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s' z θ) :=
      Work.FTS.GalBasis.hkMem_sub_open α 4 (hsmW k s hs) (hsmW k s' hs')
        (hmemW k s hs) (hmemW k s' hs')
    have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
        Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s z θ
          - Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s' z θ) :=
      smoothOpen_sub (hsmW k s hs) (hsmW k s' hs')
    have h := hCpt hsm hmem hpQ.1 hpQ.2.1 hpQ.2.2
    calc |Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s p.1 p.2
          - Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s' p.1 p.2|
        ≤ Cpt * Work.Spaces.HkNorm α 4 (fun z θ =>
            Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s z θ
              - Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s' z θ) := h
      _ ≤ Cpt * ((L * CW * B5) * |s - s'|) :=
          mul_le_mul_of_nonneg_left (hlip4 k s hs s' hs') hCpt0
      _ ≤ (Cpt + 1) * ((L * CW * B5) * |s - s'|) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (Cpt + 1) * (L * CW * B5) * |s - s'| := by ring
  obtain ⟨Ct, hCtpos, htim⟩ := htime
  -- ## the limiting right-hand side
  let Φ : ℝ × ℝ → ℝ → ℝ := fun p s => Work.FTS.StrongEps.rhsFun α Φs E
    (Work.FTS.StrongEps.clampQ Fc g₀) s p.1 p.2
  have hlimt : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∀ s' ∈ Set.Icc (0 : ℝ) T, |Φ p s - Φ p s'| ≤ Ct * |s - s'| := by
    intro p hp s hs s' hs'
    have h1 := hpt p hp s hs
    have h2 := hpt p hp s' hs'
    have habs : Filter.Tendsto (fun k : ℕ =>
        |Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s p.1 p.2
          - Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s' p.1 p.2|) Filter.atTop
        (nhds |Φ p s - Φ p s'|) := (h1.sub h2).abs
    exact le_of_tendsto_of_tendsto' habs tendsto_const_nhds (fun k => htim k s hs s' hs' p hp)
  have hlimspace : ∀ {K : Set (ℝ × ℝ)}, IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ p ∈ K, ∀ q ∈ K,
        |Φ p s - Φ q s| ≤ A₀ * Real.sqrt ‖p - q‖ := by
    intro K hK hKQ
    obtain ⟨C, hCpos, hCB⟩ := hequi hK hKQ
    refine ⟨C, hCpos.le, fun s hs p hp q hq => ?_⟩
    have h1 := hpt p (hKQ hp) s hs
    have h2 := hpt q (hKQ hq) s hs
    have habs : Filter.Tendsto (fun k : ℕ =>
        |Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s p.1 p.2
          - Work.FTS.StrongEps.epsWP α ρ (eps k) Φs E (fam k) s q.1 q.2|) Filter.atTop
        (nhds |Φ p s - Φ q s|) := (h1.sub h2).abs
    exact le_of_tendsto_of_tendsto' habs tendsto_const_nhds (fun k => hCB k s hs p hp q hq)
  -- ## the `ε`-`δ` argument
  change ContinuousOn (fun p : ℝ × ℝ × ℝ => Φ (p.1, p.2.1) p.2.2)
    (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T)
  rw [Metric.continuousOn_iff]
  intro p₀ hp₀ ε hε
  have hp₀z : 0 < p₀.1 := hp₀.1
  have hp₀θ : p₀.2.1 ∈ Set.Ioo (0 : ℝ) (π / 2) := hp₀.2.1
  have hp₀s : p₀.2.2 ∈ Set.Icc (0 : ℝ) T := hp₀.2.2
  set ρ₀ : ℝ := min (p₀.1 / 2) (min (p₀.2.1 / 2) ((π / 2 - p₀.2.1) / 2)) with hρ₀def
  have hρ₀pos : 0 < ρ₀ := by
    rw [hρ₀def]
    exact lt_min (by linarith) (lt_min (by linarith [hp₀θ.1]) (by linarith [hp₀θ.2]))
  set K : Set (ℝ × ℝ) := Metric.closedBall (p₀.1, p₀.2.1) ρ₀ with hKdef
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hKQ : K ⊆ Work.FTS.EllipticEst.Q0 := by
    intro q hq
    rw [hKdef, Metric.mem_closedBall] at hq
    rw [Prod.dist_eq] at hq
    have h1 : dist q.1 p₀.1 ≤ ρ₀ := le_trans (le_max_left _ _) hq
    have h2 : dist q.2 p₀.2.1 ≤ ρ₀ := le_trans (le_max_right _ _) hq
    rw [Real.dist_eq] at h1 h2
    have hle1 : ρ₀ ≤ p₀.1 / 2 := by rw [hρ₀def]; exact min_le_left _ _
    have hle2 : ρ₀ ≤ p₀.2.1 / 2 := by
      rw [hρ₀def]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hle3 : ρ₀ ≤ (π / 2 - p₀.2.1) / 2 := by
      rw [hρ₀def]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    refine Work.FTS.EllipticEst.mem_Q0.mpr ⟨?_, ?_, ?_⟩
    · have := (abs_le.mp h1).1; linarith
    · have := (abs_le.mp h2).1; linarith
    · have := (abs_le.mp h2).2; linarith
  obtain ⟨A₀, hA₀0, hA₀⟩ := hlimspace hKc hKQ
  set δ : ℝ := min ρ₀ (min (ε / (2 * (Ct + 1))) ((ε / (2 * (A₀ + 1))) ^ 2)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min hρ₀pos (lt_min (by positivity) (by positivity))
  have hδ1 : δ ≤ ρ₀ := by
    rw [hδdef]
    exact min_le_left _ _
  have hδ2 : δ ≤ ε / (2 * (Ct + 1)) := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ3 : δ ≤ (ε / (2 * (A₀ + 1))) ^ 2 := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨δ, hδpos, fun q hq hqdist => ?_⟩
  have hz : dist q.1 p₀.1 ≤ dist q p₀ := by
    rw [Prod.dist_eq]; exact le_max_left _ _
  have hth : dist q.2.1 p₀.2.1 ≤ dist q p₀ := by
    rw [Prod.dist_eq, Prod.dist_eq]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hqK : (q.1, q.2.1) ∈ K := by
    rw [hKdef, Metric.mem_closedBall, Prod.dist_eq]
    exact le_trans (le_trans (max_le hz hth) hqdist.le) hδ1
  have hqQ : (q.1, q.2.1) ∈ Work.FTS.EllipticEst.Q0 := hKQ hqK
  have hp₀K : (p₀.1, p₀.2.1) ∈ K := by
    rw [hKdef, Metric.mem_closedBall, dist_self]
    exact hρ₀pos.le
  have hdp : dist (q.1, q.2.1) (p₀.1, p₀.2.1) < δ := by
    rw [Prod.dist_eq]
    exact lt_of_le_of_lt (max_le hz hth) hqdist
  have hq2dist : |q.2.2 - p₀.2.2| < δ := by
    have hz2 : dist q.2.2 p₀.2.2 ≤ dist q p₀ := by
      rw [Prod.dist_eq, Prod.dist_eq]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have h := lt_of_le_of_lt hz2 hqdist
    rwa [Real.dist_eq] at h
  have e1 := hlimt (q.1, q.2.1) hqQ q.2.2 hq.2.2 p₀.2.2 hp₀s
  have e2 := hA₀ p₀.2.2 hp₀s (q.1, q.2.1) hqK (p₀.1, p₀.2.1) hp₀K
  have hb1 : Ct * |q.2.2 - p₀.2.2| < ε / 2 := by
    have h1 := hq2dist
    have h3 : |q.2.2 - p₀.2.2| ≤ ε / (2 * (Ct + 1)) := le_trans (le_of_lt h1) hδ2
    have h4 : Ct * |q.2.2 - p₀.2.2| ≤ Ct * (ε / (2 * (Ct + 1))) :=
      mul_le_mul_of_nonneg_left h3 hCtpos.le
    have h5 : Ct / (Ct + 1) < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    calc Ct * |q.2.2 - p₀.2.2| ≤ Ct * (ε / (2 * (Ct + 1))) := h4
      _ = (ε / 2) * (Ct / (Ct + 1)) := by
          have h6 : Ct + 1 ≠ 0 := by positivity
          field_simp
      _ < ε / 2 * 1 := mul_lt_mul_of_pos_left h5 (by linarith)
      _ = ε / 2 := by ring
  have hb2 : A₀ * Real.sqrt ‖(q.1, q.2.1) - (p₀.1, p₀.2.1)‖ < ε / 2 := by
    have h1 : ‖(q.1, q.2.1) - (p₀.1, p₀.2.1)‖ < δ := by
      rw [← dist_eq_norm]; exact hdp
    have h2 : δ ≤ (ε / (2 * (A₀ + 1))) ^ 2 := hδ3
    have h3 : Real.sqrt ‖(q.1, q.2.1) - (p₀.1, p₀.2.1)‖ ≤ ε / (2 * (A₀ + 1)) := by
      refine le_trans (Real.sqrt_le_sqrt (le_of_lt h1)) ?_
      calc Real.sqrt δ ≤ Real.sqrt ((ε / (2 * (A₀ + 1))) ^ 2) := Real.sqrt_le_sqrt h2
        _ = ε / (2 * (A₀ + 1)) := Real.sqrt_sq (by positivity)
    have h4 : A₀ * Real.sqrt ‖(q.1, q.2.1) - (p₀.1, p₀.2.1)‖ ≤ A₀ * (ε / (2 * (A₀ + 1))) :=
      mul_le_mul_of_nonneg_left h3 hA₀0
    have h5 : A₀ / (A₀ + 1) < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    calc A₀ * Real.sqrt ‖(q.1, q.2.1) - (p₀.1, p₀.2.1)‖ ≤ A₀ * (ε / (2 * (A₀ + 1))) := h4
      _ = (ε / 2) * (A₀ / (A₀ + 1)) := by
          have h6 : A₀ + 1 ≠ 0 := by positivity
          field_simp
      _ < ε / 2 * 1 := mul_lt_mul_of_pos_left h5 (by linarith)
      _ = ε / 2 := by ring
  calc dist (Φ (q.1, q.2.1) q.2.2) (Φ (p₀.1, p₀.2.1) p₀.2.2)
      = |Φ (q.1, q.2.1) q.2.2 - Φ (p₀.1, p₀.2.1) p₀.2.2| := Real.dist_eq _ _
    _ ≤ |Φ (q.1, q.2.1) q.2.2 - Φ (q.1, q.2.1) p₀.2.2|
          + |Φ (q.1, q.2.1) p₀.2.2 - Φ (p₀.1, p₀.2.1) p₀.2.2| := abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (lt_of_le_of_lt e1 hb1) (lt_of_le_of_lt e2 hb2)
    _ = ε := by ring

end Work.FTS.StrongEps.E5G
