/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5G/L12_Jeps_epsWP_tendsto_tower.lean` — the vanishing of the
# `P₀`-correction along the tower (PROVED)

The `P₀`-corrected `ε`-scheme's solution is projected by `Pz f = f − (L₁₂ f 0 / pzNorm) • bump`, so
the `E5` limit identity needs

  `hl12 s : Tendsto (fun k => L₁₂ (J_ε (epsWP …)) 0 / pzNorm) atTop (nhds 0)`

along the tower, at every fake time `s ∈ [0, T]`.  This module proves exactly that.

## Route

The zero mode of the *unmollified* right-hand side vanishes along every `ε`-solution of the class-`C`
package (`EpsZeroMode`, packaged for the tower as `E5G.epsWP_zero_tower`), and the mollifier error of
`L₁₂(·)(0)` is of order `ε` at level **4** (`L12_Jeps_sub_le4`, the C3 re-route — no `ℋ⁵` input is
needed because `L₁₂(·)(0)` is a single linear functional whose kernel is a `θ`-weight):

  `|L₁₂(J_ε f) 0 − L₁₂ f 0| ≤ C ε ‖f‖_{ℋ⁴}`.

Both are wrapped into `EpsCorr_tendsto_zero4`, and this file supplies its four inputs for the
tower at the selected indices `k ↦ ι n k`:

* `hε`: `e (ι n k) ∈ (0,1]` and `e (ι n k) → 0` (from `hεe`, `hε0` and `StrictMono.tendsto_atTop`);
* `hsm`: `SmoothOpen (epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s)` — `smoothOpen_epsWP` on the
  projected slices `slice (JfamP … ) τ`, which are class-`C` on `[0,T]` by `TowerAt.hC`
  (`hTT : T ≤ Tn n` restricts the horizon-`n` interval);
* `h4`/`hb`: `HkMem α 4`, `HkNorm α 4 ≤ KW` — `epsWP_hkMem4_bnd_fam`.  Its level-6 hypothesis is
  *shared* with the elliptic package `EllPkgK α 6 Ce`, so the constant is first moved up to
  `max Ce (A * K' n)` (`EllPkgGo_mono`, `EllPkgK_mono`), where `A` is the constant of
  `HkNorm_JfamP_le` and `K' n` the tower's level-6 bound of the *plain* slices;
* `h0`: `L₁₂ (epsWP …) 0 = 0` — `EpsZeroMode` through `E5G.epsWP_zero_tower`.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`
(record: `_axcheck_L12_Jeps_epsWP_tendsto_tower.lean`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.EpsHlim4
import Submission.Work.FTS.StrongEps.E5G.TowerFacts
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam
import Submission.Work.FTS.StrongEps.smoothOpen_epsWP
import Submission.Work.FTS.StrongEps.JfamP_norm

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

set_option maxHeartbeats 1600000

theorem L12_Jeps_epsWP_tendsto_tower {α C₀ Ce Cs T : ℝ} {K' : ℕ → ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {e : ℕ → ℝ} {G : ℕ → ℕ → Work.FTS.Galerkin.Fam} {ι : ℕ → ℕ → ℕ}
    (n : ℕ) (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hεe : ∀ k : ℕ, e k ∈ Set.Ioc (0 : ℝ) 1)
    (hε0 : Filter.Tendsto e Filter.atTop (nhds 0))
    (hTower : ∀ n k : ℕ, n ≤ k → Work.FTS.StrongEps.E5G.TowerAt α C₀ ρ Φs E g₀ n (e k) (K' n) (G n k))
    (hι : StrictMono (ι n)) (hadm : ∀ k : ℕ, n ≤ ι n k)
    (hT : 0 < T) (hTT : T ≤ Work.FTS.StrongEps.E5G.Tn n)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    Filter.Tendsto (fun k : ℕ => Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ (e (ι n k))
        (Work.FTS.StrongEps.epsWP α ρ (e (ι n k)) Φs E (G n (ι n k)) s)) 0
        / Work.FTS.StrongEps.pzNorm) Filter.atTop (nhds 0) := by
  -- ## Step 1: the tower data at the selected indices `ι n k`
  have hTow : ∀ k : ℕ, TowerAt α C₀ ρ Φs E g₀ n (e (ι n k)) (K' n) (G n (ι n k)) :=
    fun k => hTower n (ι n k) (hadm k)
  -- the horizon-`n` interval contains `[0, T]`
  have hI : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T, τ ∈ Set.Icc (0 : ℝ) (Tn n) :=
    fun _ τ hτ => ⟨hτ.1, le_trans hτ.2 hTT⟩
  have hclass : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.ClassC.ClassC α
        (slice (Work.FTS.StrongEps.JfamP ρ (e (ι n k)) (G n (ι n k))) τ) :=
    fun k τ hτ => (hTow k).hC τ (hI k τ hτ)
  have hb4 : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α
        (slice (Work.FTS.StrongEps.JfamP ρ (e (ι n k)) (G n (ι n k))) τ) ≤ C₀ * α ^ 2 :=
    fun k τ hτ => (hTow k).hb4 τ (hI k τ hτ)
  -- ## Step 2: the `ℋ⁶`-bound of the *projected* slices, from `HkNorm_JfamP_le`
  obtain ⟨A, hA0, hAle⟩ := Work.FTS.StrongEps.HkNorm_JfamP_le (ρ := ρ) hρ
  have hb6 : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.StrongGlobal.Xn6 α
        (slice (Work.FTS.StrongEps.JfamP ρ (e (ι n k)) (G n (ι n k))) τ) ≤ A * K' n := by
    intro k τ hτ
    have hsm : ∀ m : ℕ,
        ContDiffOn ℝ m (Function.uncurry (slice (G n (ι n k)) τ)) Work.FTS.StrongEps.Quad :=
      fun m => Work.FTS.EllipticEst.SmoothOpen.forall ((hTow k).hsm τ (hI k τ hτ)) m
    have hmem : Work.Spaces.HkMem α 6 (slice (G n (ι n k)) τ) := (hTow k).hmem6 τ (hI k τ hτ)
    have hstep := (hAle (α := α) (ε := e (ι n k)) hα (hεe (ι n k)) (s := τ) hsm hmem).2
    have h6 : Work.FTS.StrongGlobal.Xn6 α (slice (G n (ι n k)) τ) ≤ K' n :=
      (hTow k).hb6 τ (hI k τ hτ)
    exact le_trans hstep (mul_le_mul_of_nonneg_left h6 hA0)
  -- ## Step 3: the `ℋ⁴`-membership and size of `epsWP` along the tower.
  -- The level-6 constant of `epsWP_hkMem4_bnd_fam` is *shared* between the elliptic package
  -- `hEll` and the projected `ℋ⁶`-bound, so both are moved up to `max Ce (A * K' n)`.
  obtain ⟨KW, _hKW, hKey⟩ := Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam (α := α) (C₀ := C₀)
    (Ce := max Ce (A * K' n)) (Cs := Cs) (T := T) (ρ := ρ) (Φs := Φs) (E := E)
    (G := fun k => G n (ι n k)) (ε := fun k => e (ι n k))
    hα (fun u hu => ⟨Work.FTS.ClassC.EllPkgGo_mono hα.1 (hEll u hu).1 (le_max_left _ _),
        Work.FTS.ClassC.EllPkgK_mono (hEll u hu).2 (le_max_left _ _)⟩)
    hstar hml hclass hb4 (fun k τ hτ => le_trans (hb6 k τ hτ) (le_max_right _ _))
  -- ## Step 4: the level-4 correction vanishes along the tower
  refine Work.FTS.StrongEps.EpsCorr_tendsto_zero4 (α := α) (Cs := Cs) (B := KW) (ρ := ρ)
    (Φs := Φs) (E := E) (ε := fun k => e (ι n k)) (G := fun k => G n (ι n k)) (τ := s)
    hρ hα hstar ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k
    exact (hεe (ι n k)).1
  · intro k
    exact (hεe (ι n k)).2
  · exact hε0.comp hι.tendsto_atTop
  · intro k
    exact Work.FTS.StrongEps.smoothOpen_epsWP (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (T := T) (ρ := ρ) (Φs := Φs) (E := E) (g := G n (ι n k)) (ε := e (ι n k))
      hα hEll hstar (fun τ hτ => hclass k τ hτ) s hs
  · intro k
    exact (hKey k s hs).1
  · intro k
    exact (hKey k s hs).2
  · intro k
    exact epsWP_zero_tower (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (T := T) (ρ := ρ)
      (Φs := Φs) (E := E) (ε := fun k => e (ι n k)) (G := fun k => G n (ι n k))
      hα hρ (fun k => hεe (ι n k)) hEll hstar hml hclass hb4 k s hs

end Work.FTS.StrongEps.E5G
