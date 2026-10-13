import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.E5Aux2.epsWP_tendsto_of_muH
import Submission.Work.FTS.StrongEps.E5G.muDyn_lamDyn_tendsto_tower
import Submission.Work.FTS.StrongEps.E5G.HL12RawTower
import Submission.Work.FTS.StrongEps.E5G.TowerFacts
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam
import Submission.Work.FTS.StrongEps.smoothOpen_epsWP
import Submission.Work.FTS.StrongEps.E5Aux3.contDiffOn_two_E_of_EllLimOK3
import Submission.Work.FTS.StrongEps.E5Asm.Defs
import Submission.Work.FTS.StrongEps.mixed_JfamP_tendsto
import Submission.Work.FTS.StrongEps.JfamP_norm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice)

theorem epsWP_tendsto_tower {α C₀ Ce Cs T : ℝ} {K' : ℕ → ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn}
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
    (hT : 0 < T) (hTT : T ≤ Work.FTS.StrongEps.E5G.Tn n)
    {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    Filter.Tendsto (fun k : ℕ =>
        Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s p.1 p.2)
      Filter.atTop (nhds (Work.FTS.StrongEps.rhsFun α Φs E (Work.FTS.StrongEps.clampQ Fc g₀)
        s p.1 p.2)) := by
  classical
  -- ## the tower instances along the extraction, and their interface clauses
  have hTn : 0 < Tn n := Tn_pos n
  have hsT : s ∈ Set.Icc (0 : ℝ) (Tn n) := ⟨hs.1, le_trans hs.2 hTT⟩
  have htw : ∀ k : ℕ, TowerAt α C₀ ρ Φs E g₀ n (e (ι n k)) (K' n) (G n (ι n k)) :=
    fun k => hTower n (ι n k) (hadm k)
  have hεI : ∀ k : ℕ, e (ι n k) ∈ Set.Ioc (0 : ℝ) 1 := fun k => hεe (ι n k)
  have hεp : ∀ k : ℕ, 0 < e (ι n k) := fun k => (hεI k).1
  have hε0' : Filter.Tendsto (fun k : ℕ => e (ι n k)) Filter.atTop (nhds 0) :=
    hε0.comp hι.tendsto_atTop
  have hK'0 : 0 ≤ K' n := le_trans (Work.Spaces.HkNorm_nonneg α 6 (slice (G n n) 0))
    ((hTower n n le_rfl).hb6 0 ⟨le_rfl, hTn.le⟩)
  have hsmK : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) (Tn n), ∀ m : ℕ,
      ContDiffOn ℝ m (Function.uncurry (slice (G n (ι n k)) σ)) Work.FTS.StrongEps.Quad :=
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
  -- ## the projected `ℋ⁶`-bound, at the enlarged elliptic constant
  -- (the tower bounds only the *plain* slices by `K' n`; `HkNorm_JfamP_le` turns that into a
  -- bound on the projected ones, and `EllPkgGo_mono` raises the interface constant accordingly)
  obtain ⟨A, hA0, hA⟩ := Work.FTS.StrongEps.HkNorm_JfamP_le (ρ := ρ) hρ
  have hEll' : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α (max Ce (A * K' n)) u (E u) ∧
        Work.FTS.ClassC.EllPkgK α 6 (max Ce (A * K' n)) u (E u) :=
    fun u hu => ⟨Work.FTS.ClassC.EllPkgGo_mono hα.1 (hEll u hu).1 (le_max_left _ _),
      Work.FTS.ClassC.EllPkgK_mono (hEll u hu).2 (le_max_left _ _)⟩
  have hb6p : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) (Tn n),
      Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ)
        ≤ max Ce (A * K' n) := by
    intro k σ hσ
    have h1 := hA (α := α) (ε := e (ι n k)) hα (hεI k) (g := G n (ι n k)) (s := σ)
      (fun m => hsmK k σ hσ m) (hmem6 k σ hσ)
    exact le_trans (le_trans h1.2 (mul_le_mul_of_nonneg_left (hb6K k σ hσ) hA0))
      (le_max_right _ _)
  -- ## the convergence package towards the *clamped* limit
  have hconvC : ∀ τ ∈ Set.Icc (0 : ℝ) (Tn n),
      Work.FTS.StrongEps.ConvLocUnifH6 α (K' n) (fun k => slice (G n (ι n k)) τ)
        (slice (Work.FTS.StrongEps.clampQ Fc g₀) τ) :=
    fun τ hτ => Work.FTS.StrongEps.E5Asm.ConvLocUnifH6.clampQ_congr (hconv τ hτ)
  have hconvCB : ∀ τ ∈ Set.Icc (0 : ℝ) (Tn n),
      Work.FTS.StrongEps.ConvLocUnifH6 α (max (K' n) (max Ce (A * K' n)))
        (fun k => slice (G n (ι n k)) τ) (slice (Work.FTS.StrongEps.clampQ Fc g₀) τ) :=
    fun τ hτ => ⟨(hconvC τ hτ).conv, (hconvC τ hτ).contDiffOn,
      le_trans (hconvC τ hτ).hkNorm_le (le_max_left _ _)⟩
  have hb6pB : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) (Tn n),
      Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ)
        ≤ max (K' n) (max Ce (A * K' n)) :=
    fun k σ hσ => le_trans (hb6p k σ hσ) (le_max_right _ _)
  -- ## the `L₁₂`-zero-mode convergence along the extraction (the C2 leaf + the mollifier error)
  have hl12s : Filter.Tendsto (fun k : ℕ => Work.Construction.L12
      (Work.FTS.StrongEps.Jeps ρ (e (ι n k)) (slice (G n (ι n k)) s)) 0)
      Filter.atTop (nhds 0) :=
    HL12RawTower (α := α) (C₀ := C₀) (Ce := max Ce (A * K' n)) (Cs := Cs)
      (T := Tn n) (B := K' n) hα hρ hc₁ hc₂ hEll' hstar hml hεI hε0' hTn hL12g₀
      (fun k => (htw k).hsol) (fun k => (htw k).hjoint) (fun k σ hσ => (htw k).hsm σ hσ)
      hmem6 hb6K hCq hb4q hb6p hsT
  -- ## the slot convergence of the projected family at the fixed fake time `s`
  have hslotS : ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun k : ℕ => Work.Spaces.mixed j i
          (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) s) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i (slice (Work.FTS.StrongEps.clampQ Fc g₀) s) z θ)) :=
    fun j i hji z θ hzθ => Work.FTS.StrongEps.mixed_JfamP_tendsto (ρ := ρ)
      (g := Work.FTS.StrongEps.clampQ Fc g₀) (G := fun k => G n (ι n k)) hρ
      (fun k m => hsmK k s hsT m) (hconvC s hsT) hεp hε0' hl12s hzθ hji
  -- ## the elliptic image of the limit slice is `C¹` (Gap 1, from `EllLimOK3`)
  have hsmE : ContDiffOn ℝ 1
      (Function.uncurry (E (slice (Work.FTS.StrongEps.clampQ Fc g₀) s)))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongEps.contDiffOn_two_E_of_EllLimOK3 hELL3 (fun k => hCq k s hsT)
      (fun k => hb6p k s hsT) (hconvC s hsT).contDiffOn
      (fun j i hji z θ hzθ => hslotS j i hji z θ hzθ)).of_le (by norm_num)
  -- ## the modulation constants (`mubar`, `muDyn`, `lamDyn`) along the extraction
  have hmulam := muDyn_lamDyn_tendsto_tower (α := α) (C₀ := C₀) (Ce := max Ce (A * K' n))
    (Cs := Cs) (T := T) (B := max (K' n) (max Ce (A * K' n))) (ρ := ρ) (Φs := Φs) (E := E)
    (ε := fun k => e (ι n k)) (G := fun k => G n (ι n k))
    (g := Work.FTS.StrongEps.clampQ Fc g₀) (Maj := Maj n) (s := s)
    hα hρ hEll' hstar hml hELL3 hsmΦ hsmE hεI hε0'
    (fun k m => hsmK k s hsT m) (hconvCB s hsT)
    (fun k => hCq k s hsT) (fun k => hb4q k s hsT) (fun k => hb6pB k s hsT)
    (hMaj n) (fun k => hDec (ι n k) (hadm k) s hsT) hl12s
  -- ## the assembly: the pointwise convergence of the scheme's pre-mollified right-hand side
  exact Work.FTS.StrongEps.E5Aux2.epsWP_tendsto_of_muH (α := α) (C₀ := C₀)
    (B := max (K' n) (max Ce (A * K' n))) (Ce := max Ce (A * K' n)) (ρ := ρ) (Φs := Φs)
    (E := E) (g := Work.FTS.StrongEps.clampQ Fc g₀) (ε := fun k => e (ι n k))
    (G := fun k => G n (ι n k)) (s := s) (Maj := Maj n)
    hρ hα (Work.FTS.StrongEps.EllLimOK3.toEllLimOK hELL3) hEll' hsmΦ hsmE hεI hε0'
    (fun k m => hsmK k s hsT m) (hconvCB s hsT) (fun k => hCq k s hsT)
    (fun k => hb4q k s hsT) (fun k => hb6pB k s hsT) (hMaj n)
    (fun k => hDec (ι n k) (hadm k) s hsT) hl12s hmulam.1 hmulam.2.2 hp

end Work.FTS.StrongEps.E5G
