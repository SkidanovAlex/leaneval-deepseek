/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5G/Coherence.lean` — the horizons of the tower agree

The nested extraction (`E5G/Nest.lean`) gives index maps `ι n` with `n + k ≤ ι n k` and the nesting
`ι (n+1) = ι n ∘ (strictly increasing)`, together with limit curves `F n` on `[0, Tn n]`.  Because of
the nesting, for `m ≤ n` the horizon-`n` sequence `k ↦ G n (ι n k)` is the horizon-`m` sequence
`k' ↦ G m (ι m k')` re-indexed by the iterated strictly increasing map; and because the two tower
solutions at the *same* datum index `ι n k` agree on the overlap by the fixed-`ε` uniqueness **D1**
(`Work.FTS.StrongEps.IsEpsSolP_eq_of_epsClass`), the two limits agree on the open quadrant.

This is what lets the single family `τ ↦ F (⌊τ⌋₊) τ` carry `EpsLimPkg` on every horizon.

Everything here is `sorry`-free (modulo D1).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E5G.Nest
import Submission.Work.FTS.StrongEps.IsEpsSolP_eq_of_epsClass

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
set_option linter.unusedVariables false

/-! ## The horizon monotonicity of the scheme -/

/-- A `P₀`-solution on `[0,T']` is one on every shorter interval `[0,T]`. -/
theorem IsEpsSolP_mono {α ε T T' : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : Fam} (h : IsEpsSolP α ρ ε T' Φs E g₀ g) (hTT' : T ≤ T') :
    IsEpsSolP α ρ ε T Φs E g₀ g :=
  ⟨h.1, fun z θ τ hz hθ hτ =>
    (h.2 z θ τ hz hθ ⟨hτ.1, le_trans hτ.2 hTT'⟩).mono (Set.Icc_subset_Icc le_rfl hTT')⟩

/-! ## Re-indexing a convergence package -/

/-- Uniform convergence on a set is preserved by re-indexing a sequence along a map tending to
infinity. -/
theorem tendstoUniformlyOn_comp_atTop {γ β : Type*} [UniformSpace β] {s : Set γ} {F : ℕ → γ → β}
    {f : γ → β} {θ : ℕ → ℕ} (hF : TendstoUniformlyOn F f atTop s) (hθ : Tendsto θ atTop atTop) :
    TendstoUniformlyOn (fun n => F (θ n)) f atTop s :=
  fun u hu => hθ.eventually (hF u hu)

/-- The convergence package `ConvLocUnifH6` is preserved by re-indexing. -/
theorem ConvLocUnifH6.comp_atTop {α B : ℝ} {u : ℕ → Fn} {f : Fn} {θ : ℕ → ℕ}
    (h : ConvLocUnifH6 α B u f) (hθ : Tendsto θ atTop atTop) :
    ConvLocUnifH6 α B (fun n => u (θ n)) f :=
  ⟨fun K hK hKQ j i hji => tendstoUniformlyOn_comp_atTop (h.1 K hK hKQ j i hji) hθ, h.2.1, h.2.2⟩

/-- Pointwise convergence of the profiles, read off `ConvLocUnifH6` at a singleton. -/
theorem ConvLocUnifH6.conv_pt {α B : ℝ} {u : ℕ → Fn} {f : Fn} {p : ℝ × ℝ}
    (h : ConvLocUnifH6 α B u f) (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    Tendsto (fun k => u k p.1 p.2) atTop (nhds (f p.1 p.2)) := by
  have hsub : ({p} : Set (ℝ × ℝ)) ⊆ Work.FTS.EllipticEst.Q0 := by
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact hp
  have h1 := (h.conv {p} isCompact_singleton hsub 0 0 (by norm_num)).tendsto_at
    (Set.mem_singleton p)
  simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero] using h1

/-! ## The iterated nesting -/

/-- The nesting of the index maps, iterated: for `m ≤ n` the map `ι n` factors through `ι m`. -/
theorem nest_iter {ι : ℕ → ℕ → ℕ} (hι : ∀ n : ℕ, StrictMono (ι n))
    (hnest : ∀ n : ℕ, ∃ θ : ℕ → ℕ, StrictMono θ ∧ ι (n + 1) = ι n ∘ θ) :
    ∀ m n : ℕ, m ≤ n → ∃ θ : ℕ → ℕ, StrictMono θ ∧ ι n = ι m ∘ θ := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨id, strictMono_id, by funext k; rfl⟩
  | succ n hmn ih =>
      obtain ⟨θ₁, hθ₁, h₁⟩ := ih
      obtain ⟨θ₂, hθ₂, h₂⟩ := hnest n
      exact ⟨θ₁ ∘ θ₂, hθ₁.comp hθ₂, by rw [h₂, h₁]; rfl⟩

/-! ## Coherence of the horizons -/

/-- **The limit curves of the tower agree on the overlaps.**  For `m ≤ n` the horizon-`n` sequence is
the horizon-`m` sequence re-indexed (the iterated nesting), and the values at the same datum index
agree on the open quadrant by D1; hence the two limits agree there. -/
theorem tower_coherent {α C₀ Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {e : ℕ → ℝ} {G : ℕ → ℕ → Fam} {K' : ℕ → ℝ} {ι : ℕ → ℕ → ℕ} {F : ℕ → ℝ → Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : MuLamOK α C₀ Φs E)
    (hεe : ∀ k : ℕ, e k ∈ Set.Ioc 0 1)
    (hTower : ∀ n k : ℕ, n ≤ k → TowerAt α C₀ ρ Φs E g₀ n (e k) (K' n) (G n k))
    (hι : ∀ n : ℕ, StrictMono (ι n)) (hlow : ∀ n k : ℕ, n + k ≤ ι n k)
    (hnest : ∀ n : ℕ, ∃ θ : ℕ → ℕ, StrictMono θ ∧ ι (n + 1) = ι n ∘ θ)
    (hconv : ∀ n : ℕ, ∀ τ ∈ Set.Icc 0 (Tn n),
      ConvLocUnifH6 α (K' n) (fun k => slice (G n (ι n k)) τ) (F n τ)) :
    ∀ m n : ℕ, ∀ τ ∈ Set.Icc 0 (min (Tn m) (Tn n)), ∀ z θ : ℝ,
      0 < z → θ ∈ Set.Ioo 0 (π / 2) → F m τ z θ = F n τ z θ := by
  have hnonneg : ∀ n : ℕ, 0 ≤ K' n := fun n =>
    le_trans (Work.Spaces.HkNorm_nonneg α 6 (slice (G n n) 0))
      ((hTower n n le_rfl).hb6 0 ⟨le_rfl, (Tn_pos n).le⟩)
  have coh_le : ∀ m n : ℕ, m ≤ n → ∀ τ ∈ Set.Icc 0 (min (Tn m) (Tn n)), ∀ z θ : ℝ,
      0 < z → θ ∈ Set.Ioo 0 (π / 2) → F m τ z θ = F n τ z θ := by
    intro m n hmn τ hτ z θ hz hθ
    obtain ⟨thetaT, hthetaT, hιeq⟩ := nest_iter hι hnest m n hmn
    have hτm : τ ∈ Set.Icc 0 (Tn m) := ⟨hτ.1, le_trans hτ.2 (min_le_left _ _)⟩
    have hτn : τ ∈ Set.Icc 0 (Tn n) := ⟨hτ.1, le_trans hτ.2 (min_le_right _ _)⟩
    have hsubP : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ⟩
    -- the two numerical limits
    have hu : Tendsto (fun k => slice (G n (ι n k)) τ z θ) atTop (nhds (F n τ z θ)) :=
      ConvLocUnifH6.conv_pt (hconv n τ hτn) hsubP
    have hm : Tendsto (fun k => slice (G m (ι n k)) τ z θ) atTop (nhds (F m τ z θ)) := by
      have h2 := ConvLocUnifH6.conv_pt (ConvLocUnifH6.comp_atTop (hconv m τ hτm)
        hthetaT.tendsto_atTop) hsubP
      refine h2.congr' (Filter.Eventually.of_forall fun k => ?_)
      show slice (G m (ι m (thetaT k))) τ z θ = slice (G m (ι n k)) τ z θ
      rw [show ι n k = ι m (thetaT k) from congrFun hιeq k]
    -- the values agree at every index by D1
    have heq : ∀ k : ℕ, slice (G n (ι n k)) τ z θ = slice (G m (ι n k)) τ z θ := by
      intro k
      have hkl : n ≤ ι n k := le_trans (Nat.le_add_right n k) (hlow n k)
      have hkm : m ≤ ι n k := le_trans hmn hkl
      have hB0 : 0 ≤ max (K' m) (K' n) := le_trans (hnonneg m) (le_max_left _ _)
      have hd := IsEpsSolP_eq_of_epsClass (α := α) (C₁ := C₀) (Ce := Ce) (Cs := Cs)
        (B := max (K' m) (K' n)) (T := min (Tn m) (Tn n)) (ε := e (ι n k))
        hα hρ (hεe (ι n k)).1 (hεe (ι n k)).2 (lt_min (Tn_pos m) (Tn_pos n))
        hEll hstar hml hB0
        (IsEpsSolP_mono (hTower n (ι n k) hkl).hsol (min_le_right _ _))
        (IsEpsSolP_mono (hTower m (ι n k) hkm).hsol (min_le_left _ _))
        (fun σ hσ => (hTower n (ι n k) hkl).epsClass (T := min (Tn m) (Tn n))
          (le_max_right _ _) (min_le_right _ _) σ hσ)
        (fun σ hσ => (hTower m (ι n k) hkm).epsClass (T := min (Tn m) (Tn n))
          (le_max_left _ _) (min_le_left _ _) σ hσ)
        ((hTower n (ι n k) hkl).hjoint.mono (by
          intro q hq
          exact ⟨hq.1, hq.2.1, hq.2.2.1, le_trans hq.2.2.2 (min_le_right _ _)⟩))
        ((hTower m (ι n k) hkm).hjoint.mono (by
          intro q hq
          exact ⟨hq.1, hq.2.1, hq.2.2.1, le_trans hq.2.2.2 (min_le_left _ _)⟩))
        τ hτ z θ hz hθ
      simpa only [Work.FTS.Galerkin.slice_apply] using hd
    have heqev : (fun k => slice (G n (ι n k)) τ z θ) = fun k => slice (G m (ι n k)) τ z θ :=
      funext heq
    rw [heqev] at hu
    exact (tendsto_nhds_unique hu hm).symm
  intro m n τ hτ z θ hz hθ
  rcases le_total m n with hmn | hnm
  · exact coh_le m n hmn τ hτ z θ hz hθ
  · have hτ' : τ ∈ Set.Icc 0 (min (Tn n) (Tn m)) := by
      rwa [min_comm] at hτ
    exact (coh_le n m hnm τ hτ' z θ hz hθ).symm

end Work.FTS.StrongEps.E5G
