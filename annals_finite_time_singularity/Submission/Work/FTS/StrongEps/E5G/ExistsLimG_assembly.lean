import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E5G.TowerDecay
import Submission.Work.FTS.StrongEps.E5G.Tower
import Submission.Work.FTS.StrongEps.E5G.Nest
import Submission.Work.FTS.StrongEps.E5G.Coherence
import Submission.Work.FTS.StrongEps.E5G.ExistsLimG_of_horizon_pkgs
import Submission.Work.FTS.StrongEps.E5G.EpsLimPkg_of_horizon_full
import Submission.Work.FTS.StrongEps.E5G.hdbd_of_tower
import Submission.Work.FTS.StrongEps.E5G.hlim_slots_of_tower
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsLimitDefsG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

theorem ExistsLimG_assembly {α₂ α₄ α C₀ K Ce Cs Cs6 C3 Cpow : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    (hα₂ : 0 < α₂) (hα₂1 : α₂ ≤ 1 / 4) (hα : α ∈ Set.Ioc (0 : ℝ) α₂)
    (hα₄ : α < α₄) (hα₄2 : α₄ ≤ α₂)
    (hL3 : Work.FTS.StrongPersist.L3Data α₂ Ce C3 Cpow)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hELL3 : Work.FTS.StrongEps.EllLimOK3 α E) (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hstar6 : Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hU : Work.FTS.StrongEps.EpsUniformMem α ρ Φs E g₀ C₀ K) :
    Work.FTS.StrongEps.ExistsLimG α C₀ K Φs E g₀ := by
  classical
  -- ## the parameter range
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := by linarith [hα.2, hα₄2, hα₂1]
  have hαI1 : α ∈ Set.Ioc (0 : ℝ) 1 := ⟨hα0, hα1⟩
  have hα₄0 : 0 < α₄ := lt_trans hα0 hα₄
  have hα₄1 : α₄ ≤ 1 := by linarith [hα₄2, hα₂1]
  have hαIα₄ : α ∈ Set.Ioc (0 : ℝ) α₄ := ⟨hα0, le_of_lt hα₄⟩
  obtain ⟨hc₁, hc₂⟩ := Work.Spaces.c_bounds α hα0 hα1
  -- ## the datum clauses carried by the interface
  have hvan := hU.1
  have hL12g₀ := hU.2.1
  -- ## smoothness of `Φs` from the star package
  have hsmΦ : ContDiffOn ℝ 1 (Function.uncurry Φs) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Φs).mp hstar.smooth 1
  -- ## the tower of `ε`-solutions, with the decay majorant
  obtain ⟨e, G, K', Maj, hεe, hε0, hMaj, hTD⟩ :=
    tower_exists_decay (α := α) (C₀ := C₀) (K := K) (ρ := ρ) (Φs := Φs) (E := E)
      (g₀ := g₀) hU
  have hTower : ∀ n k : ℕ, n ≤ k → TowerAt α C₀ ρ Φs E g₀ n (e k) (K' n) (G n k) :=
    fun n k h => (hTD n k h).1
  have hDec : ∀ n k : ℕ, n ≤ k → ∀ τ ∈ Set.Icc (0 : ℝ) (Tn n),
      EpsDecay α ρ Φs E (e k) τ (G n k) (Maj n) :=
    fun n k h => (hTD n k h).2
  -- ## the nested extraction and the coherence of the horizons
  obtain ⟨ι, F, hιmono, hlow, hnest, hconv⟩ :=
    tower_extract (α := α) (C₀ := C₀) (K := K) (Ce := Ce) (Cs := Cs) (ρ := ρ) (Φs := Φs)
      (E := E) (g₀ := g₀) (e := e) (G := G) (K' := K') hαI1 hρ hc₁ hc₂ hEll hstar hml
      hεe hTower
  have hcoh := tower_coherent (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (ρ := ρ) (Φs := Φs)
    (E := E) (g₀ := g₀) (e := e) (G := G) (K' := K') (ι := ι) (F := F)
    hαI1 hρ hEll hstar hml hεe hTower hιmono hlow hnest hconv
  -- ## the glue: one family carrying the package on every horizon
  refine ExistsLimG_of_horizon_pkgs (α := α) (C₀ := C₀) (K := K) (Φs := Φs) (E := E)
    (g₀ := g₀) (Tn := Tn) (F := F) Tn_pos Tn_mono ?_ ?_ ?_
  · -- the horizons cover every positive time
    intro T _hT
    refine ⟨Nat.ceil T, ?_⟩
    have h := Nat.le_ceil T
    simp only [Tn]
    linarith
  · -- coherence of the limit curves on the overlaps
    intro m n τ hτ z θ hzθ
    exact hcoh m n τ hτ z θ hzθ.1 hzθ.2
  · -- the per-horizon package
    intro N T hT hTN
    have hιN : StrictMono (ι N) := hιmono N
    have hadmN : ∀ k : ℕ, N ≤ ι N k := fun k => le_trans (Nat.le_add_right N k) (hlow N k)
    have hDecN : ∀ k : ℕ, N ≤ k → ∀ τ ∈ Set.Icc (0 : ℝ) (Tn N),
        EpsDecay α ρ Φs E (e k) τ (G N k) (Maj N) := fun k hk => hDec N k hk
    -- the slot convergence of the scheme's right-hand side along the tower
    have hslots := hlim_slots_of_tower (n := N) (T := T) (hα := hαI1) (hρ := hρ)
      (hc₁ := hc₁) (hc₂ := hc₂) (hEll := hEll) (hstar := hstar) (hstar6 := hstar6)
      (hml := hml) (hELL3 := hELL3) (hsmΦ := hsmΦ) (hL12g₀ := hL12g₀) (hεe := hεe)
      (hε0 := hε0) (hTower := hTower) (hMaj := hMaj) (hDec := hDecN) (hι := hιN)
      (hadm := hadmN) (hconv := hconv N) (hT := hT) (hTT := hTN)
    -- the `ℋ³`-bound of `∂_τ` at the limit
    have hdbd := hdbd_of_tower (n := N) (hα₄ := hα₄0) (hα₄1 := hα₄1) (hα := hαIα₄)
      (hρ := hρ) (hL3 := hL3) (hα₂ := hα) (hc₁ := hc₁) (hc₂ := hc₂) (hEll := hEll)
      (hstar := hstar) (hstar6 := hstar6) (hml := hml) (hELL3 := hELL3) (hsmΦ := hsmΦ)
      (hL12g₀ := hL12g₀) (hεe := hεe) (hε0 := hε0) (hTower := hTower) (hMaj := hMaj)
      (hDec := hDecN) (hι := hιN) (hadm := hadmN) (hconv := hconv N) (hT := hT)
      (hTT := hTN) (hslots := hslots)
    exact EpsLimPkg_of_horizon_full (n := N) (Fc := F N) (hα₄ := hα₄0) (hα₄1 := hα₄1)
      (hα := hαIα₄) (hρ := hρ) (hL3 := hL3) (hα₂ := hα) (hvan := hvan) (hc₁ := hc₁)
      (hc₂ := hc₂) (hEll := hEll) (hstar := hstar) (hstar6 := hstar6) (hml := hml)
      (hELL3 := hELL3) (hsmΦ := hsmΦ) (hL12g₀ := hL12g₀) (hεe := hεe) (hε0 := hε0)
      (hTower := hTower) (hMaj := hMaj) (hDec := hDecN) (hι := hιN) (hadm := hadmN)
      (hconv := hconv N) (hT := hT) (hTT := hTN) (hdbd := hdbd)

end Work.FTS.StrongEps.E5G
