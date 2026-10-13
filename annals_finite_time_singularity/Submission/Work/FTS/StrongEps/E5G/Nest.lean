/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5G/Nest.lean` — the nested extraction of the tower

At each horizon `Tn n` the tower (`E5G/Tower.lean`) provides a sequence of `ε`-solutions; applying
the extraction `E5Extract_of_mem_seq` to it yields a strictly increasing index map and a limit curve
on `[0, Tn n]`.  To be able to *glue* the horizons into one family, the extractions are nested: the
horizon-`(n+1)` extraction is applied to the subsequence picked at horizon `n`, so that the index map
`ι (n+1)` is `ι n ∘ (strictly increasing)` and the limit curve at horizon `n+1` is the limit of a
*subsequence* of the horizon-`n` sequence on the overlap.

Two invariants make the gluing work:

* `n + k ≤ ι n k` — the datum indices at horizon `n` are admissible: `ι n k ≥ n` for every `k`, which
  is exactly the range in which the tower gives a solution at horizon `Tn n`;
* the nesting `ι (n+1) = ι n ∘ θ` with `θ` strictly increasing — so that for `m ≤ n` the horizon-`n`
  sequence is a *subsequence* of the horizon-`m` sequence (through the iterated `θ`), and the fixed-`ε`
  uniqueness D1 identifies the two limits on the overlap (`E5G/Coherence.lean`).

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.E5G.Tower
import Submission.Work.FTS.StrongEps.E5ExtractMem

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
set_option maxHeartbeats 2000000

/-- The state of the nested extraction at level `lvl`: the index map `ι`, the index map `θ` of the
step that produced it (so that `ι = ι_previous ∘ θ`), the limit curve, the admissibility invariant
`lvl + k ≤ ι k`, and the convergence package. -/
structure NestSt (α C₀ : ℝ) (ρ : ℝ × ℝ → ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (e : ℕ → ℝ) (G : ℕ → ℕ → Fam) (K' : ℕ → ℝ) (lvl : ℕ) where
  /-- the index map at this horizon. -/
  ι : ℕ → ℕ
  /-- the index map of the last step. -/
  θ : ℕ → ℕ
  /-- the limit curve. -/
  F : ℝ → Fn
  /-- strict monotonicity of `ι`. -/
  hι : StrictMono ι
  /-- strict monotonicity of `θ`. -/
  hθ : StrictMono θ
  /-- the admissibility invariant. -/
  hlow : ∀ k : ℕ, lvl + k ≤ ι k
  /-- the convergence package at this horizon. -/
  hconv : ∀ τ ∈ Set.Icc 0 (Tn lvl),
    ConvLocUnifH6 α (K' lvl) (fun k => slice (G lvl (ι k)) τ) (F τ)

/-- **The extraction at one horizon, along a given admissible subsequence.** -/
theorem tower_extract_step {α C₀ Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {e : ℕ → ℝ} {G : ℕ → ℕ → Fam} {K' : ℕ → ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ)
    (hc₁ : 1 / 10 ≤ Work.Spaces.c α) (hc₂ : Work.Spaces.c α ≤ 10)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : MuLamOK α C₀ Φs E)
    (hεe : ∀ k : ℕ, e k ∈ Set.Ioc 0 1)
    (hTower : ∀ n k : ℕ, n ≤ k → TowerAt α C₀ ρ Φs E g₀ n (e k) (K' n) (G n k))
    (n : ℕ) (ι : ℕ → ℕ) (hι : StrictMono ι) (hadm : ∀ k : ℕ, n ≤ ι k) :
    ∃ (θ : ℕ → ℕ) (F : ℝ → Fn), StrictMono θ ∧
      (∀ τ ∈ Set.Icc 0 (Tn n), ConvLocUnifH6 α (K' n)
        (fun k => slice (G n (ι (θ k))) τ) (F τ)) := by
  obtain ⟨A, hA0, hA⟩ := Work.FTS.StrongEps.HkNorm_JfamP_le (ρ := ρ) hρ
  set Cen : ℝ := max Ce (A * K' n) with hCen
  have hEll' : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Cen u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Cen u (E u) :=
    fun u hu => ⟨Work.FTS.ClassC.EllPkgGo_mono hα.1 (hEll u hu).1 (le_max_left _ _),
      Work.FTS.ClassC.EllPkgK_mono (hEll u hu).2 (le_max_left _ _)⟩
  have hb6p : ∀ k : ℕ, ∀ s ∈ Set.Icc 0 (Tn n),
      Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (e (ι k)) (G n (ι k))) s) ≤ Cen := by
    intro k s hs
    have h := hA (α := α) (ε := e (ι k)) hα (hεe (ι k)) (g := G n (ι k)) (s := s)
      (fun m => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
        ((hTower n (ι k) (hadm k)).hsm s hs) m)
      ((hTower n (ι k) (hadm k)).hmem6 s hs)
    exact le_trans (le_trans h.2 (mul_le_mul_of_nonneg_left
      ((hTower n (ι k) (hadm k)).hb6 s hs) hA0)) (le_max_right _ _)
  exact E5Extract_of_mem_seq (α := α) (C₀ := C₀) (Ce := Cen) (Cs := Cs) (K' := K' n)
    (T := Tn n) (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀)
    (ε := fun k => e (ι k)) (G := fun k => G n (ι k))
    hα hρ hc₁ hc₂ hEll' hstar hml (fun k => hεe _) (Tn_pos n)
    (fun k => (hTower n (ι k) (hadm k)).hsol)
    (fun k => (hTower n (ι k) (hadm k)).toEpsRegP)
    (fun k s hs => (hTower n (ι k) (hadm k)).hC s hs)
    (fun k s hs => (hTower n (ι k) (hadm k)).hb4 s hs)
    (fun k s hs => hb6p k s hs)
    (fun k τ hτ => (hTower n (ι k) (hadm k)).hsm τ hτ)
    (fun k τ hτ => (hTower n (ι k) (hadm k)).hmem6 τ hτ)
    (fun k τ hτ => (hTower n (ι k) (hadm k)).hb6 τ hτ)

/-- **The nested extraction.**  From the tower data there are index maps `ι n` (each strictly
increasing with `n + k ≤ ι n k`, nested: `ι (n+1) = ι n ∘ (strictly increasing)`) and limit curves
`F n` such that at horizon `n` the profiles `slice (G n (ι n k)) τ` converge to `F n τ` locally
uniformly with all slots of order `≤ 4`, for every `τ ∈ [0, Tn n]`. -/
theorem tower_extract {α C₀ K Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {e : ℕ → ℝ} {G : ℕ → ℕ → Fam} {K' : ℕ → ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ)
    (hc₁ : 1 / 10 ≤ Work.Spaces.c α) (hc₂ : Work.Spaces.c α ≤ 10)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : MuLamOK α C₀ Φs E)
    (hεe : ∀ k : ℕ, e k ∈ Set.Ioc 0 1)
    (hTower : ∀ n k : ℕ, n ≤ k → TowerAt α C₀ ρ Φs E g₀ n (e k) (K' n) (G n k)) :
    ∃ (ι : ℕ → ℕ → ℕ) (F : ℕ → ℝ → Fn),
      (∀ n : ℕ, StrictMono (ι n)) ∧
      (∀ n k : ℕ, n + k ≤ ι n k) ∧
      (∀ n : ℕ, ∃ θ : ℕ → ℕ, StrictMono θ ∧ ι (n + 1) = ι n ∘ θ) ∧
      ∀ n : ℕ, ∀ τ ∈ Set.Icc 0 (Tn n),
        ConvLocUnifH6 α (K' n) (fun k => slice (G n (ι n k)) τ) (F n τ) := by
  classical
  -- the extraction data at each level, as an explicit function of the previous state
  let step : (n : ℕ) → NestSt α C₀ ρ Φs E g₀ e G K' n → NestSt α C₀ ρ Φs E g₀ e G K' (n + 1) :=
    fun n st =>
      let h := tower_extract_step (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (ρ := ρ) (Φs := Φs)
        (E := E) (g₀ := g₀) (e := e) (G := G) (K' := K')
        hα hρ hc₁ hc₂ hEll hstar hml hεe hTower (n + 1) (fun k => st.ι (k + 1))
        (fun a b hab => st.hι (Nat.add_lt_add_right hab 1))
        (fun k => le_trans (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le k)) n)
          (st.hlow (k + 1)))
      let θ' : ℕ → ℕ := Classical.choose h
      let θ'p : StrictMono θ' := (Classical.choose_spec (Classical.choose_spec h)).1
      { ι := fun k => st.ι (θ' k + 1)
        θ := fun k => θ' k + 1
        F := Classical.choose (Classical.choose_spec h)
        hι := fun a b hab => st.hι (Nat.add_lt_add_right (θ'p hab) 1)
        hθ := fun a b hab => Nat.add_lt_add_right (θ'p hab) 1
        hlow := fun k => by
          have h1 : k + 1 ≤ θ' k + 1 := Nat.add_le_add_right (θ'p.id_le k) 1
          calc n + 1 + k = n + (k + 1) := by ring
            _ ≤ st.ι (k + 1) := st.hlow (k + 1)
            _ ≤ st.ι (θ' k + 1) := st.hι.monotone h1
        hconv := (Classical.choose_spec (Classical.choose_spec h)).2 }
  -- the initial state: the extraction at horizon `0` along the identity
  let init : NestSt α C₀ ρ Φs E g₀ e G K' 0 :=
    let h := tower_extract_step (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (ρ := ρ) (Φs := Φs)
      (E := E) (g₀ := g₀) (e := e) (G := G) (K' := K')
      hα hρ hc₁ hc₂ hEll hstar hml hεe hTower 0 id strictMono_id (fun k => Nat.zero_le _)
    { ι := Classical.choose h
      θ := Classical.choose h
      F := Classical.choose (Classical.choose_spec h)
      hι := (Classical.choose_spec (Classical.choose_spec h)).1
      hθ := (Classical.choose_spec (Classical.choose_spec h)).1
      hlow := fun k => by
        simpa using (Classical.choose_spec (Classical.choose_spec h)).1.id_le k
      hconv := (Classical.choose_spec (Classical.choose_spec h)).2 }
  let nest : (n : ℕ) → NestSt α C₀ ρ Φs E g₀ e G K' n :=
    fun n => Nat.rec init (fun m ih => step m ih) n
  exact ⟨fun n => (nest n).ι, fun n => (nest n).F, fun n => (nest n).hι,
    fun n k => (nest n).hlow k, fun n => ⟨(nest (n + 1)).θ, (nest (n + 1)).hθ, by
      funext k
      rfl⟩,
    fun n => (nest n).hconv⟩

end Work.FTS.StrongEps.E5G
