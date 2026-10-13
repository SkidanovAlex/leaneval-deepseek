import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E5G.hcontR_of_tower
import Submission.Work.FTS.StrongEps.EpsLimVolterraP
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongEps.EpsE4Thr.epsRHSP_hkMem_fam
import Submission.Work.FTS.StrongEps.EpsRHSPBdd_unif
import Submission.Work.FTS.StrongEps.E5G.Coherence
import Submission.Work.FTS.StrongEps.EpsStructP
import Submission.Work.FTS.StrongEps.EpsHbdd
import Submission.Work.FTS.StrongEps.RhsCont
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.StrongEps.E5G.HkIntegrand_three_perz_le
import Submission.Work.FTS.StrongEps.E5G.hkMem_three_of_slot_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn Fam slice gdot)

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

theorem hdbd_of_tower {α₂ α₄ α C₀ Ce Cs Cs6 C3 Cpow T : ℝ} {K' : ℕ → ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g₀ : Work.FTS.Galerkin.Fn} {e : ℕ → ℝ} {G : ℕ → ℕ → Work.FTS.Galerkin.Fam}
    {Maj : ℕ → ℝ → ℝ} {ι : ℕ → ℕ → ℕ} {Fc : ℝ → Work.FTS.Galerkin.Fn}
    (n : ℕ) (hα₄ : 0 < α₄) (hα₄1 : α₄ ≤ 1) (hα : α ∈ Set.Ioc (0 : ℝ) α₄)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hL3 : Work.FTS.StrongPersist.L3Data α₂ Ce C3 Cpow) (hα₂ : α ∈ Set.Ioc (0 : ℝ) α₂)
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
    (hT : 0 < T) (hTT : T ≤ Work.FTS.StrongEps.E5G.Tn n)
    (hslots : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∀ (j i : ℕ), j + i ≤ 3 →
        Filter.Tendsto (fun k : ℕ => Work.Spaces.mixed j i
            (Work.FTS.StrongEps.epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed j i
            (Work.FTS.StrongEps.rhsFun α Φs E (Work.FTS.StrongEps.clampQ Fc g₀) s) p.1 p.2))) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ τ : ℝ, 0 < τ → τ < T →
      Work.Spaces.HkMem α 3 (Work.FTS.Galerkin.gdot (Work.FTS.StrongEps.clampQ Fc g₀) τ) ∧
        Work.Spaces.HkNorm α 3 (Work.FTS.Galerkin.gdot (Work.FTS.StrongEps.clampQ Fc g₀) τ) ≤ Cd := by
  classical
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := le_trans hα.2 hα₄1
  have hαI1 : α ∈ Set.Ioc (0 : ℝ) 1 := ⟨hα.1, hα1⟩
  have hTn : 0 < Tn n := Tn_pos n
  -- ## the extracted tower
  have htw : ∀ k : ℕ, TowerAt α C₀ ρ Φs E g₀ n (e (ι n k)) (K' n) (G n (ι n k)) :=
    fun k => hTower n (ι n k) (hadm k)
  have hεI : ∀ k : ℕ, e (ι n k) ∈ Set.Ioc (0 : ℝ) 1 := fun k => hεe (ι n k)
  have hK'0 : 0 ≤ K' n := le_trans (Work.Spaces.HkNorm_nonneg α 6 (slice (G n n) 0))
    ((hTower n n le_rfl).hb6 0 ⟨le_rfl, hTn.le⟩)
  -- ## the tower data on `[0,T]`
  have hsmT : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (slice (G n (ι n k)) σ) :=
    fun k σ hσ => (htw k).hsm σ ⟨hσ.1, le_trans hσ.2 hTT⟩
  have hmem6T : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 6 (slice (G n (ι n k)) σ) :=
    fun k σ hσ => (htw k).hmem6 σ ⟨hσ.1, le_trans hσ.2 hTT⟩
  have hb6T : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.StrongGlobal.Xn6 α (slice (G n (ι n k)) σ) ≤ K' n :=
    fun k σ hσ => (htw k).hb6 σ ⟨hσ.1, le_trans hσ.2 hTT⟩
  have hCT : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.ClassC.ClassC α (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ) :=
    fun k σ hσ => (htw k).hC σ ⟨hσ.1, le_trans hσ.2 hTT⟩
  have hb4T : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ) ≤ C₀ * α ^ 2 :=
    fun k σ hσ => (htw k).hb4 σ ⟨hσ.1, le_trans hσ.2 hTT⟩
  -- ## the raised elliptic constant, and the projected `ℋ⁶`-bound
  obtain ⟨A, hA0, hA⟩ := Work.FTS.StrongEps.HkNorm_JfamP_le (ρ := ρ) hρ
  have hEll' : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α (max Ce (A * K' n)) u (E u) ∧
        Work.FTS.ClassC.EllPkgK α 6 (max Ce (A * K' n)) u (E u) :=
    fun u hu => ⟨Work.FTS.ClassC.EllPkgGo_mono hα0 (hEll u hu).1 (le_max_left _ _),
      Work.FTS.ClassC.EllPkgK_mono (hEll u hu).2 (le_max_left _ _)⟩
  have hb6pT : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ)
        ≤ max Ce (A * K' n) := by
    intro k σ hσ
    have h1 := hA (α := α) (ε := e (ι n k)) hαI1 (hεI k) (g := G n (ι n k)) (s := σ)
      (fun m => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hsmT k σ hσ) m)
      (hmem6T k σ hσ)
    exact le_trans (le_trans h1.2 (mul_le_mul_of_nonneg_left (hb6T k σ hσ) hA0))
      (le_max_right _ _)
  -- ## fake-time continuity of the scheme's right-hand side
  have hcontT : ∀ k : ℕ, ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s p.1 p.2)
        (Set.Icc 0 T) :=
    fun k p hp => Work.FTS.StrongEps.continuousOn_epsRHSP_of_regP hT
      (IsEpsSolP_mono (htw k).hsol hTT) ((htw k).toEpsRegP.mono hTT) p hp
  -- ## a pointwise uniform bound of the right-hand sides along the tower
  have hbddT : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → ∃ C : ℝ, ∀ k : ℕ,
      ∀ s ∈ Set.Icc (0 : ℝ) T,
        |epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s p.1 p.2| ≤ C := by
    intro p hp
    have hKQ : ({p} : Set (ℝ × ℝ)) ⊆ Work.FTS.EllipticEst.Q0 := by
      intro q hq
      rw [Set.mem_singleton_iff] at hq
      subst hq
      exact hp
    obtain ⟨C, _hC0, hC⟩ := Work.FTS.StrongEps.hbdd_of_mem_compact (α := α) (C₀ := C₀)
      (Ce := max Ce (A * K' n)) (Cs := Cs) (T := T) (ρ := ρ) (Φs := Φs) (E := E)
      (G := fun k => G n (ι n k)) (ε := fun k => e (ι n k)) hαI1 hρ hεI hT.le hc₁ hc₂
      hEll' hstar hml (fun k s hs => hCT k s hs) (fun k s hs => hb4T k s hs)
      (fun k s hs => hb6pT k s hs) isCompact_singleton hKQ
    exact ⟨C, fun k s hs => hC k s hs p (Set.mem_singleton p)⟩
  -- ## pointwise convergence of the right-hand sides
  have hlimT : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → ∀ s ∈ Set.Icc (0 : ℝ) T,
      Filter.Tendsto (fun k : ℕ => epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s p.1 p.2)
        Filter.atTop (nhds (rhsFun α Φs E (clampQ Fc g₀) s p.1 p.2)) := by
    intro p hp s hs
    have h := hslots p hp s hs 0 0 (by norm_num)
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero] using h
  -- ## pointwise convergence of the families
  have hconv0 : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Filter.Tendsto (fun k : ℕ => G n (ι n k) p.1 p.2 σ) Filter.atTop
        (nhds (clampQ Fc g₀ p.1 p.2 σ)) := by
    intro p hp σ hσ
    have hKQ : ({p} : Set (ℝ × ℝ)) ⊆ Work.FTS.EllipticEst.Q0 := by
      intro q hq
      rw [Set.mem_singleton_iff] at hq
      subst hq
      exact hp
    have hpt : Filter.Tendsto (fun k : ℕ => slice (G n (ι n k)) σ p.1 p.2) Filter.atTop
        (nhds (Fc σ p.1 p.2)) := by
      have h1 := ((hconv σ ⟨hσ.1, le_trans hσ.2 hTT⟩).conv {p} isCompact_singleton hKQ 0 0
        (by norm_num)).tendsto_at (Set.mem_singleton p)
      simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero,
        Work.FTS.Galerkin.slice_apply] using h1
    have hpQ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hcp : clampQ Fc g₀ p.1 p.2 σ = Fc σ p.1 p.2 :=
      clampQ_of_mem hpQ.1 ⟨hpQ.2.1, hpQ.2.2⟩
    simpa only [hcp, Work.FTS.Galerkin.slice_apply] using hpt
  -- ## continuity in the fake time of the limiting right-hand side
  have hcontR' : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => rhsFun α Φs E (clampQ Fc g₀) s p.1 p.2) (Set.Icc 0 T) :=
    fun p hp => hcontR_of_tower n hα₄ hα₄1 hα hρ hc₁ hc₂ hEll hstar hstar6 hml hELL3 hsmΦ
      hL12g₀ hεe hε0 hTower hMaj hDec hι hadm hconv hT hTT p.1 p.2 hp
  -- ## the limiting Volterra equation, from the tower
  have heqT : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → ∀ σ ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s : ℝ => clampQ Fc g₀ p.1 p.2 s)
        (rhsFun α Φs E (clampQ Fc g₀) σ p.1 p.2) (Set.Icc 0 T) σ :=
    Work.FTS.StrongEps.EpsLimVolterraP (α := α) (T := T) (ρ := ρ) (Φs := Φs) (E := E)
      (g₀ := g₀) (ε := fun k => e (ι n k)) (G := fun k => G n (ι n k)) (g := clampQ Fc g₀)
      hT (fun k => IsEpsSolP_mono (htw k).hsol hTT) hcontT hlimT hbddT hconv0 hcontR'
  -- ## the uniform `ℋ³`-bound of the scheme's right-hand side along the tower
  obtain ⟨R, hRpos, hRbd⟩ := Work.FTS.StrongEps.EpsRHSPBdd_unif (α := α) (C₀ := C₀) (Ce := Ce)
    (Cs := Cs) (B := K' n) (ρ := ρ) (Φs := Φs) (E := E) hαI1 hρ hEll hstar hml hK'0
  refine ⟨R, hRpos, ?_⟩
  intro τ hτ0 hτT
  have hτI : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ0.le, hτT.le⟩
  -- ## smoothness and `ℋ⁶`-honesty of the approximants at `τ`
  have hS6 : ∀ k : ℕ, Work.FTS.EllipticEst.SmoothOpen
        (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) τ) ∧
      Work.Spaces.HkMem α 6 (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) τ) := by
    intro k
    exact Work.FTS.StrongEps.EpsE4Thr.epsRHSP_smoothOpen_hkMem6_fam (α := α) (C₀ := C₀) (Ce := Ce)
      (Cs := Cs) (B := K' n) (ρ := ρ) (Φs := Φs) (E := E) (g := G n (ι n k))
      (ε := e (ι n k)) (T := T) hαI1 hρ (hεI k).1 (hεI k).2 hEll hstar hml hK'0
      (fun s hs => hsmT k s hs) (fun s hs => hmem6T k s hs) (fun s hs => hb6T k s hs)
      (fun s hs => hCT k s hs) (fun s hs => hb4T k s hs) τ hτI
  have hsmfs : ∀ k : ℕ, Work.FTS.EllipticEst.SmoothOpen
      (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) τ) := fun k => (hS6 k).1
  have hmem6fs : ∀ k : ℕ, Work.Spaces.HkMem α 6
      (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) τ) := fun k => (hS6 k).2
  have hmem3fs : ∀ k : ℕ, Work.Spaces.HkMem α 3
      (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) τ) :=
    fun k => Work.FTS.OpenPkg.HkMem_mono_open (hsmfs k) 3 (by norm_num) (hmem6fs k)
  have hmem4fs : ∀ k : ℕ, Work.Spaces.HkMem α 4
      (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) τ) :=
    fun k => Work.FTS.OpenPkg.HkMem_mono_open (hsmfs k) 4 (by norm_num) (hmem6fs k)
  have h4fs : ∀ k : ℕ, Work.Spaces.HkNorm α 4
      (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) τ) ≤ R := by
    intro k
    rw [Work.FTS.StrongEps.epsRHSP_eq_slice]
    exact hRbd (e (ι n k)) (hεI k) τ (slice (G n (ι n k)) τ) (hsmT k τ hτI) (hmem6T k τ hτI)
      (hb6T k τ hτI) (hCT k τ hτI) (hb4T k τ hτI)
  have h3fs : ∀ k : ℕ, Work.Spaces.HkNorm α 3
      (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) τ) ≤ R := fun k =>
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 4) (k' := 3) (by norm_num)
      (hmem4fs k)) (h4fs k)
  -- ## the uniform per-`z` bounds of the angular energies of the approximants
  obtain ⟨C3, hC3pos, hC3bd⟩ := HkIntegrand_three_perz_le
  have hzfs : ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ, ∀ k : ℕ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 3
        (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) τ) z θ) ≤ Bz := by
    intro z hz'
    refine ⟨C3 * (1 + (Work.Spaces.w z) ^ 2) * (1 + R) ^ 2, fun k => ?_⟩
    refine le_trans (hC3bd α (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) τ) hαI1 (hsmfs k)
      (hmem4fs k) z hz') ?_
    have h1 : 1 + Work.Spaces.HkNorm α 4 (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) τ)
        ≤ 1 + R := by linarith [h4fs k]
    have h2 : (0 : ℝ) ≤ 1 + Work.Spaces.HkNorm α 4
        (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) τ) := by
      have := Work.Spaces.HkNorm_nonneg α 4 (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) τ)
      linarith
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h2 h1 2) ?_
    have hw := sq_nonneg (Work.Spaces.w z)
    nlinarith [hC3pos]
  -- ## the `ℋ³`-membership and bound of the limiting right-hand side
  have hslot : ∀ (j i : ℕ), j + i ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun k : ℕ => Work.Spaces.mixed j i
          (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) τ) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i (rhsFun α Φs E (clampQ Fc g₀) τ) z θ)) :=
    fun j i hji z θ hzθ => hslots (z, θ) hzθ τ hτI j i hji
  have hsm3fs : ∀ k : ℕ, ∀ m : ℕ, ContDiffOn ℝ m
      (Function.uncurry (epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) τ))
      Work.FTS.EllipticEst.Q0 :=
    fun k m => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hsmfs k) m
  obtain ⟨hMemLim, hNormLim⟩ := hkMem_three_of_slot_tendsto (α := α) (R := R)
    (fs := fun k => epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) τ)
    (f := rhsFun α Φs E (clampQ Fc g₀) τ) hmem3fs h3fs hsm3fs hslot hzfs
  -- ## transfer to the fake-time derivative at `τ`
  have hgd : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      gdot (clampQ Fc g₀) τ z θ = rhsFun α Φs E (clampQ Fc g₀) τ z θ := by
    intro z θ hzθ
    rw [gdot]
    exact ((heqT (z, θ) hzθ τ hτI).hasDerivAt (Icc_mem_nhds hτ0 hτT)).deriv
  refine ⟨?_, ?_⟩
  · exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 3 hMemLim
      (fun z hz θ hθ => (hgd z θ ⟨hz, hθ⟩).symm)
  · rw [Work.Spaces.HkNorm, Work.FTS.EllipticEst.HkSq_congr_open α 3
      (fun z θ hz hθ hlt => hgd z θ ⟨hz, hθ, hlt⟩)]
    exact hNormLim

end Work.FTS.StrongEps.E5G
