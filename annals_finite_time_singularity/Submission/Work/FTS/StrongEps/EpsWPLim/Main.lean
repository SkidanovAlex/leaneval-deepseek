/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsWPLim/Main.lean`

**`epsWP_tendsto` with the modulation constant `λ` hypothesised to converge.**

The requested statement

`epsWP_tendsto` (file `Submission/Work/FTS/StrongEps/epsWP_tendsto.lean`) asks, from
`hmu : muDyn α (PsiCan Φs E (JfamP ρ (ε n) (G n))) (JfamP ρ (ε n) (G n)) s → muDyn α
(PsiCan Φs E g) g s`, for the convergence of `epsWP α ρ (ε n) Φs E (G n) s p` to
`rhsFun α Φs E g s p`.  Since

`dynRHS α Φ gg τ = gRHS α (muDyn α Φ gg τ) (lamDyn α Φ gg τ) (Ftau α gg τ) (slice Φ τ)
(slice gg τ)`,   `lamDyn α Φ gg τ = lamfun (muDyn α Φ gg τ)`,

both sides contain `Nstar` at `λ = lamfun μ`, and the conclusion therefore requires

`μ n + lamfun (μ n) + μ n·lamfun (μ n) → μ l + lamfun (μ l) + μ l·lamfun (μ l)`

from `μ n → μ l` alone.  **That is false**: `Work.FTS.Nonlin.lamfun_add` gives
`μ + lamfun μ + μ·lamfun μ = -μ` for `μ ≠ -1`, while `lamfun (-1) = 0` (Lean's totalised
division) gives `-1` at `μ = -1`; the coefficient of `D_z w` in `Nstar` *jumps by 2* at
`μ = -1`.  Hence the statement of `epsWP_tendsto` is missing the convergence of `λ` (the sibling
`Submission/Work/FTS/StrongEps/gRHS_tendsto.lean` carries it as its hypothesis `hlam`).  This
file proves the corrected form: **the same statement with the extra hypothesis**

`hlam : lamDyn α (PsiCan Φs E (JfamP ρ (ε n) (G n))) (JfamP ρ (ε n) (G n)) s →
lamDyn α (PsiCan Φs E g) g s`.

Equivalently one may assume `∀ n, muDyn … ≠ -1` together with `muDyn α (PsiCan Φs E g) g s ≠ -1`
(or, as in the intended use, `|muDyn …| ≤ 1/2`, which is what `MuLamOK` provides on the
class-`C` small ball); with `hlam` both cases are covered.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsWPLim.gRHSStep
import Submission.Work.FTS.StrongEps.L12.linPart_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsWPLim

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **`epsWP_tendsto` with the convergence of the modulation constant `λ` hypothesised.** -/
theorem epsWP_tendsto_of_lam {α C₀ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g : Fam} {ε : ℕ → ℝ} {G : ℕ → Fam} {s : ℝ}
    (hα : α ∈ Set.Ioc 0 1)
    (hQ : ∀ n : ℕ, Work.FTS.VocabO.HQo α 4
      (slice (JfamP ρ (ε n) (G n)) s))
    (hQg : Work.FTS.VocabO.HQo α 4 (slice g s))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 4 (slice (JfamP ρ (ε n) (G n)) s) ≤ C₀)
    (hbg : Work.Spaces.HkNorm α 4 (slice g s) ≤ C₀)
    (hconv : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∀ j i : ℕ, j + i ≤ 1 →
        TendstoUniformlyOn (fun n : ℕ => fun p : ℝ × ℝ => Work.Spaces.mixed j i
            (slice (JfamP ρ (ε n) (G n)) s) p.1 p.2)
          (fun p : ℝ × ℝ => Work.Spaces.mixed j i (slice g s) p.1 p.2)
          Filter.atTop K)
    (hL12 : ∀ z ∈ Work.Spaces.Iz, Filter.Tendsto (fun n : ℕ => Work.Construction.L12
      (slice (JfamP ρ (ε n) (G n)) s) z) Filter.atTop
      (nhds (Work.Construction.L12 (slice g s) z)))
    (hL12T : Filter.Tendsto (fun n : ℕ => Work.Coercivity.L12f (Work.Coercivity.Transport
      (slice (JfamP ρ (ε n) (G n)) s)) 0) Filter.atTop
      (nhds (Work.Coercivity.L12f (Work.Coercivity.Transport (slice g s)) 0)))
    (hFK : ∀ z ∈ Work.Spaces.Iz, Filter.Tendsto (fun n : ℕ => Work.Construction.FK
      (slice (JfamP ρ (ε n) (G n)) s) z) Filter.atTop
      (nhds (Work.Construction.FK (slice g s) z)))
    (hTil : ∀ j i : ℕ, j + i ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (Work.Construction.PhiTil α
            (Work.Construction.Ftau α (JfamP ρ (ε n) (G n)) s)
            (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ (ε n) (G n))) s)) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i
          (Work.Construction.PhiTil α (Work.Construction.Ftau α g s)
            (slice (Work.FTS.Nonlin.PsiCan Φs E g) s)) z θ)))
    (hmu : Filter.Tendsto (fun n : ℕ => Work.FTS.Galerkin.muDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ (ε n) (G n)))
      (JfamP ρ (ε n) (G n)) s) Filter.atTop
      (nhds (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)))
    (hlam : Filter.Tendsto (fun n : ℕ => Work.FTS.Galerkin.lamDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ (ε n) (G n)))
      (JfamP ρ (ε n) (G n)) s) Filter.atTop
      (nhds (Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)))
    (hmubar : Filter.Tendsto (fun n : ℕ => Work.Construction.mubar
      (Work.Construction.N0 α (Work.Construction.Ftau α
        (JfamP ρ (ε n) (G n)) s)
        (slice (JfamP ρ (ε n) (G n)) s))
      (Work.Construction.N α (Work.Construction.Ftau α
        (JfamP ρ (ε n) (G n)) s)
        (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ (ε n) (G n))) s))) Filter.atTop
      (nhds (Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftau α g s) (slice g s))
        (Work.Construction.N α (Work.Construction.Ftau α g s)
          (slice (Work.FTS.Nonlin.PsiCan Φs E g) s)))))
    {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    Filter.Tendsto (fun n : ℕ => epsWP α ρ (ε n) Φs E (G n) s p.1 p.2)
      Filter.atTop (nhds (rhsFun α Φs E g s p.1 p.2)) := by
  obtain ⟨hz, hθ0, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have hpqd : (p.1, p.2) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ2⟩
  -- the slot convergence of the raw slices `w n = slice (JfamP ρ (ε n) (G n)) s`
  have hwslots : ∀ j i : ℕ, j + i ≤ 1 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (slice (JfamP ρ (ε n) (G n)) s) p.1 p.2) Filter.atTop
        (nhds (Work.Spaces.mixed j i (slice g s) p.1 p.2)) :=
    fun j i hji => tendsto_mixed_at (f := fun n => slice (JfamP ρ (ε n) (G n)) s)
      (fl := slice g s) hp hconv j i hji
  -- the slot convergence of the full profiles `Ftau α (JfamP ρ (ε n) (G n)) s = F_* + w n`
  have hFslots : ∀ j i : ℕ, j + i ≤ 1 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (Work.Construction.Ftau α (JfamP ρ (ε n) (G n)) s) p.1 p.2) Filter.atTop
        (nhds (Work.Spaces.mixed j i (Work.Construction.Ftau α g s) p.1 p.2)) := by
    intro j i hji
    have hcongr : (fun n : ℕ => Work.Spaces.mixed j i
          (Work.Construction.Ftau α (JfamP ρ (ε n) (G n)) s) p.1 p.2)
        = fun n : ℕ => Work.Spaces.mixed j i (Work.Construction.Fstar α) p.1 p.2
            + Work.Spaces.mixed j i (slice (JfamP ρ (ε n) (G n)) s) p.1 p.2 := by
      funext n
      exact mixed_Fstar_add hz ⟨hθ0, hθ2⟩ (hQ n).1 j i
    have hlimF : Work.Spaces.mixed j i (Work.Construction.Ftau α g s) p.1 p.2
        = Work.Spaces.mixed j i (Work.Construction.Fstar α) p.1 p.2
            + Work.Spaces.mixed j i (slice g s) p.1 p.2 :=
      mixed_Fstar_add hz ⟨hθ0, hθ2⟩ hQg.1 j i
    rw [hcongr, hlimF]
    exact tendsto_const_nhds.add (hwslots j i hji)
  -- the angular moment `FK` of the full profiles
  have hFKslots : Filter.Tendsto (fun n : ℕ => Work.Construction.FK
        (Work.Construction.Ftau α (JfamP ρ (ε n) (G n)) s) p.1) Filter.atTop
      (nhds (Work.Construction.FK (Work.Construction.Ftau α g s) p.1)) := by
    have hcongr : (fun n : ℕ => Work.Construction.FK
          (Work.Construction.Ftau α (JfamP ρ (ε n) (G n)) s) p.1)
        = fun n : ℕ => Work.Construction.FK (Work.Construction.Fstar α) p.1
            + Work.Construction.FK (slice (JfamP ρ (ε n) (G n)) s) p.1 := by
      funext n
      exact FK_Fstar_add_of_SmoothOpen_HkMem (hQ n).1 (hQ n).2 hz
    have hlimK : Work.Construction.FK (Work.Construction.Ftau α g s) p.1
        = Work.Construction.FK (Work.Construction.Fstar α) p.1
            + Work.Construction.FK (slice g s) p.1 :=
      FK_Fstar_add_of_SmoothOpen_HkMem hQg.1 hQg.2 hz
    rw [hcongr, hlimK]
    exact tendsto_const_nhds.add (hFK p.1 (le_of_lt hz))
  -- the slots of `PhiTil` are exactly the hypothesis `hTil`
  have hTilslots : ∀ j i : ℕ, j + i ≤ 1 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (Work.Construction.PhiTil α (Work.Construction.Ftau α (JfamP ρ (ε n) (G n)) s)
            (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ (ε n) (G n))) s)) p.1 p.2)
        Filter.atTop
        (nhds (Work.Spaces.mixed j i
          (Work.Construction.PhiTil α (Work.Construction.Ftau α g s)
            (slice (Work.FTS.Nonlin.PsiCan Φs E g) s)) p.1 p.2)) :=
    fun j i hji => hTil j i hji p.1 p.2 hpqd
  -- the `gRHS` block
  have hgRHS := gRHS_tendsto (α := α)
    (μ := fun n : ℕ => Work.FTS.Galerkin.muDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ (ε n) (G n))) (JfamP ρ (ε n) (G n)) s)
    (μl := Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)
    (lam := fun n : ℕ => Work.FTS.Galerkin.lamDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ (ε n) (G n))) (JfamP ρ (ε n) (G n)) s)
    (laml := Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)
    (F := fun n : ℕ => Work.Construction.Ftau α (JfamP ρ (ε n) (G n)) s)
    (Fl := Work.Construction.Ftau α g s)
    (Ψ := fun n : ℕ => slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ (ε n) (G n))) s)
    (Ψl := slice (Work.FTS.Nonlin.PsiCan Φs E g) s)
    (w := fun n : ℕ => slice (JfamP ρ (ε n) (G n)) s) (wl := slice g s)
    hz ⟨hθ0, hθ2⟩ hmu hlam hFslots hwslots hTilslots hFKslots hL12 hmubar
  -- the linear block `-𝓛_Γ^T`
  have hlin := Work.FTS.StrongEps.L12.linPart_tendsto (α := α) (B := C₀)
    (f := fun n : ℕ => slice (JfamP ρ (ε n) (G n)) s) (g := slice g s)
    hα.1 hα.2 hQ hb hQg hbg hconv hL12T p hp
  -- the two sides, unfolded
  have hterm : (fun n : ℕ => epsWP α ρ (ε n) Φs E (G n) s p.1 p.2)
      = fun n : ℕ => Work.FTS.StrongPersist.linPart α
            (slice (JfamP ρ (ε n) (G n)) s) p.1 p.2
          + Work.Construction.gRHS α
              (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E
                (JfamP ρ (ε n) (G n))) (JfamP ρ (ε n) (G n)) s)
              (Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E
                (JfamP ρ (ε n) (G n))) (JfamP ρ (ε n) (G n)) s)
              (Work.Construction.Ftau α (JfamP ρ (ε n) (G n)) s)
              (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ (ε n) (G n))) s)
              (slice (JfamP ρ (ε n) (G n)) s) p.1 p.2 := by
    funext n
    simp only [epsWP, Work.FTS.StrongPersist.dynLin_eq_linPart, Work.FTS.Galerkin.dynRHS]
  have hlim : rhsFun α Φs E g s p.1 p.2
      = Work.FTS.StrongPersist.linPart α (slice g s) p.1 p.2
          + Work.Construction.gRHS α
              (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)
              (Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)
              (Work.Construction.Ftau α g s)
              (slice (Work.FTS.Nonlin.PsiCan Φs E g) s) (slice g s) p.1 p.2 := by
    simp only [rhsFun, Work.FTS.StrongPersist.dynLin_eq_linPart, Work.FTS.Galerkin.dynRHS]
  rw [hterm, hlim]
  exact hlin.add hgRHS

end Work.FTS.StrongEps.EpsWPLim
