import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.PkgK6.vopTransferKSharp
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.E5G.morrey_step_four
import Submission.Work.FTS.StrongEps.E5G.weak_slots_tendsto_open
import Submission.Work.FTS.StrongEps.EpsHlim4
import Submission.Work.FTS.StrongEps.IsEpsSolP_eq_of_epsClass
import Submission.Work.FTS.StrongEps.JfamP_norm
import Submission.Work.FTS.StrongEps.LocUnif.D5.deriv_slot_lintegral_bounds
import Submission.Work.FTS.StrongEps.LocUnif.D5.rounds
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam
import Submission.Work.FTS.StrongEps.smoothOpen_epsWP
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_StreamBdry.SB6.clauses3
import Submission.Work.FTS_StreamBdry.SBpsiP.SelfUprime
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.L12_Jeps_epsWP_tendsto_tower =====
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
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.Nest =====
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
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.TowerDecay =====
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
set_option linter.unusedVariables false

/-- **The tower together with the radial decay majorant.**  Same conclusion as `tower_exists`,
plus a per-horizon majorant `Maj n` which is `1/z`-integrable and whose `EpsDecay` clause holds for
the whole horizon-`n` sequence at every fake time of `[0, Tn n]`. -/
theorem tower_exists_decay {α C₀ K : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    (hU : EpsUniformMem α ρ Φs E g₀ C₀ K) :
    ∃ (e : ℕ → ℝ) (G : ℕ → ℕ → Fam) (K' : ℕ → ℝ) (Maj : ℕ → ℝ → ℝ),
      (∀ k : ℕ, e k ∈ Set.Ioc 0 1) ∧ Tendsto e atTop (nhds 0) ∧
      (∀ n : ℕ, MeasureTheory.IntegrableOn (fun z => Maj n z / z) (Set.Ioi 0)) ∧
      (∀ n k : ℕ, n ≤ k → TowerAt α C₀ ρ Φs E g₀ n (e k) (K' n) (G n k) ∧
        ∀ τ ∈ Set.Icc 0 (Tn n), EpsDecay α ρ Φs E (e k) τ (G n k) (Maj n)) := by
  classical
  -- ## the per-horizon interface data, *keeping* the majorant
  have hper : ∀ n : ℕ, ∃ K' ε₁ : ℝ, ∃ Maj : ℝ → ℝ, K ≤ K' ∧ 0 < ε₁ ∧
      MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0) ∧
      ∀ ε ∈ Set.Ioc 0 ε₁, ∃ g : Fam, TowerAt α C₀ ρ Φs E g₀ n ε K' g ∧
        ∀ τ ∈ Set.Icc 0 (Tn n), EpsDecay α ρ Φs E ε τ g Maj := by
    intro n
    obtain ⟨K', hK', ε₁, hε₁, Maj, hMaj, hg⟩ := hU.2.2 (Tn n) (Tn_pos n)
    refine ⟨K', ε₁, Maj, hK', hε₁, hMaj, fun ε hε => ?_⟩
    obtain ⟨g, hsol, hcl⟩ := hg ε hε
    have h0 := hcl 0 ⟨le_rfl, (Tn_pos n).le⟩
    exact ⟨g, ⟨hsol, fun τ hτ => (hcl τ hτ).1, fun τ hτ => (hcl τ hτ).2.1,
      fun τ hτ => (hcl τ hτ).2.2.1, fun τ hτ => (hcl τ hτ).2.2.2.1,
      fun τ hτ => (hcl τ hτ).2.2.2.2.1, fun τ hτ => (hcl τ hτ).2.2.2.2.2.1,
      h0.2.2.2.2.2.2.1⟩,
      fun τ hτ => (hcl τ hτ).2.2.2.2.2.2.2⟩
  let K' : ℕ → ℝ := fun n => Classical.choose (hper n)
  let ε₁ : ℕ → ℝ := fun n => Classical.choose (Classical.choose_spec (hper n))
  let Maj : ℕ → ℝ → ℝ := fun n =>
    Classical.choose (Classical.choose_spec (Classical.choose_spec (hper n)))
  have hspec : ∀ n : ℕ, K ≤ K' n ∧ 0 < ε₁ n ∧
      MeasureTheory.IntegrableOn (fun z => Maj n z / z) (Set.Ioi 0) ∧
      ∀ ε ∈ Set.Ioc 0 (ε₁ n), ∃ g : Fam, TowerAt α C₀ ρ Φs E g₀ n ε (K' n) g ∧
        ∀ τ ∈ Set.Icc 0 (Tn n), EpsDecay α ρ Φs E ε τ g (Maj n) := fun n =>
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hper n)))
  have hε₁pos : ∀ n : ℕ, 0 < ε₁ n := fun n => (hspec n).2.1
  have hMajint : ∀ n : ℕ,
      MeasureTheory.IntegrableOn (fun z => Maj n z / z) (Set.Ioi 0) :=
    fun n => (hspec n).2.2.1
  have hg : ∀ n : ℕ, ∀ ε ∈ Set.Ioc 0 (ε₁ n), ∃ g : Fam,
      TowerAt α C₀ ρ Φs E g₀ n ε (K' n) g ∧
        ∀ τ ∈ Set.Icc 0 (Tn n), EpsDecay α ρ Φs E ε τ g (Maj n) :=
    fun n => (hspec n).2.2.2
  -- ## the global datum sequence
  refine ⟨dataSeq ε₁, fun n k => if h : n ≤ k then
      Classical.choose (hg n (dataSeq ε₁ k)
        ⟨dataSeq_pos hε₁pos k, dataSeq_le (fun k => (hε₁pos k).le) h⟩)
      else fun z θ _ => g₀ z θ,
    K', Maj, ⟨fun k => ⟨dataSeq_pos hε₁pos k, dataSeq_le_one ε₁⟩,
      dataSeq_tendsto (fun k => (hε₁pos k).le), hMajint, ?_⟩⟩
  intro n k hnk
  have h := Classical.choose_spec (hg n (dataSeq ε₁ k)
    ⟨dataSeq_pos hε₁pos k, dataSeq_le (fun k => (hε₁pos k).le) hnk⟩)
  simpa only [dif_pos hnk] using h

end Work.FTS.StrongEps.E5G
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.epsWP_equicont_tower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

/-!
# `Work.FTS.StrongEps.E5G.epsWP_equicont_tower`

The Hölder-`1/2` equicontinuity of the tower family `n ↦ epsWP α ρ (ε n) Φs E (G n)` on every
compact `K ⊆ Q0`, uniformly in the piece index `n` and in the fake time `s ∈ [0,T]`, with the
constant `(1 + B4)` coming from the uniform `ℋ⁴`-ball `B4`.

## Route

1. **Morrey at level 4 on a compact.**  A compact `K ⊆ Q0 = (0,∞)×(0,π/2)` sits in a box
   `[zlo,zhi] × [tlo,thi]` whose two-fold enlargement `[zlo/2, zhi+1] × [tlo/2, (thi+π/2)/2]`
   still lies in `Q0` (`FTS_EllLimOK.box_of_compact_inside_Q0` plus padding); a `C²` cut-off `χ`
   equal to `1` on the box and vanishing outside the enlargement
   (`Sobolev.EqcAux.exists_cutoff_rect_C2`) makes `χ · F` a `C²` function with compact support,
   to which Morrey `W^{2,2}(ℝ²) ⊂ C^{0,1/2}` (`Sobolev.holder_half_of_W22_real`) applies.
2. **The two `L²`-inputs of Morrey.**  On the enlargement the plain partials of `F` up to order
   two — `F`, `pz F`, `pth F`, `pz(pz F)`, `pz(pth F)`, `pth(pz F)`, `pth(pth F)` — are
   dominated by `C · HkSq α 4 F`: this is `E5G.mixed_rect_L2_bounds_level` at `k = 4`,
   `(j,i) = (0,0)` (which in turn inverts the plain partials into the mixed slots via
   `LocUnif.mixed_partials_of_smoothOpen` and dominates each slot pointwise by
   `HkIntegrand α 4 F`).  Feeding these seven bounds into `E5G.morrey_step_four` (the slot-`(0,0)`
   level-`4` Morrey step) yields the bound with an `α`- and `F`-free constant.
3. **Assembly.**  The constant is chosen before `n`, `s`, `F`; the only remaining step is
   `HkNorm α 4 F ≤ B4` and square-root bookkeeping (`dist p q ^ (1/2:ℝ) = √‖p-q‖`).

`T` (and hence the time interval), the scale sequence `ε`, and the family `G` enter only through
the three hypotheses `hsm`, `hmem`, `hb`, so the result is uniform in the tower.
-/

/-- **Morrey's estimate at level `4` on a compact subset of the open quadrant.**

For a compact `K ⊆ Q0` there is a constant `C > 0` such that every `F` which is `C^∞` on the
open quadrant and lies in `ℋ⁴` satisfies, for all `p, q ∈ K`,

  `|F p - F q| ≤ C · (1 + |F|_{ℋ⁴}) · √‖p - q‖`.

This is the `χ`-cut-off version of the classical `W^{2,2}(ℝ²) ⊂ C^{0,1/2}` Morrey estimate with
the `W^{2,2}`-norm priced by `|F|_{ℋ⁴}`: at level `4` the only slot whose *second* derivatives are
still controlled is the value `D_z^0D_θ^0 F`. -/
private theorem holder_on_compact_of_HkMem_four {α : ℝ} (hα : 0 < α)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen F →
      Work.Spaces.HkMem α 4 F → ∀ p ∈ K, ∀ q ∈ K,
        |F p.1 p.2 - F q.1 q.2| ≤ C * (1 + Work.Spaces.HkNorm α 4 F)
          * Real.sqrt ‖p - q‖ := by
  classical
  rcases Set.eq_empty_or_nonempty K with hKe | hne
  · subst hKe
    exact ⟨1, one_pos, fun F _ _ p hp => absurd hp (by simp)⟩
  · -- ## the box containing `K`, and its two-fold enlargement
    obtain ⟨zlo, zhi, tlo, thi, hzlopos, hzlole, htlopos, htlole, hthilt, hKbox⟩ :=
      Work.FTS_EllLimOK.box_of_compact_inside_Q0 hK hKQ hne
    have hzlo'pos : 0 < zlo / 2 := by linarith
    have hzlo'lt : zlo / 2 < zlo := by linarith
    have hzhi'lt : zhi < zhi + 1 := by linarith
    have hzlo'le : zlo / 2 ≤ zhi + 1 := by linarith
    have htlo'pos : 0 < tlo / 2 := by linarith
    have htlo'lt : tlo / 2 < tlo := by linarith
    have hthi'lt : thi < (thi + Real.pi / 2) / 2 := by linarith [Real.pi_pos]
    have hthi'pi : (thi + Real.pi / 2) / 2 < Real.pi / 2 := by linarith
    have hboxsub : Set.Icc (zlo / 2) (zhi + 1) ×ˢ Set.Icc (tlo / 2) ((thi + Real.pi / 2) / 2)
        ⊆ Work.FTS.EllipticEst.Q0 := by
      rintro ⟨z, θ⟩ ⟨hz, hθ⟩
      exact Work.FTS.EllipticEst.mem_Q0.mpr
        ⟨by linarith [hz.1], by linarith [hθ.1], by linarith [hθ.2]⟩
    -- ## the cut-off
    obtain ⟨χ, M, hMpos, hχsm, hχcs, hχnn, hχle1, hχone, hχzero, hM1, hM2⟩ :=
      Work.FTS.StrongLWP.Sobolev.EqcAux.exists_cutoff_rect_C2
        (a := zlo) (b := zhi) (c := tlo) (d := thi)
        (a' := zlo / 2) (b' := zhi + 1) (c' := tlo / 2) (d' := (thi + Real.pi / 2) / 2)
        hzlo'pos hzlo'lt hzlole hzhi'lt htlo'pos htlo'lt htlole hthi'lt hthi'pi
    have hχ2 : ContDiff ℝ 2 χ := by simpa using hχsm 2
    -- ## the level-`4` rectangle bounds on the support of `χ`
    obtain ⟨Cl, hClpos, hClbound⟩ :=
      mixed_rect_L2_bounds_level (a := zlo / 2) (b := zhi + 1) (c := tlo / 2)
        (d := (thi + Real.pi / 2) / 2) hzlo'pos hzlo'le htlo'pos hthi'pi
    -- ## Morrey
    obtain ⟨Km, hKmpos, hMor⟩ := Work.FTS.StrongLWP.Sobolev.holder_half_of_W22_real
    refine ⟨Km * (2 * Real.sqrt (Cl + 3 * Cl * (16 + 17 * M ^ 2))) + 1, by positivity, ?_⟩
    intro F hFsm hFmem p hp q hq
    obtain ⟨hmix, hpz1, hpth1, hpz2, hpzpth, hpthpz, hpth2⟩ :=
      hClbound 4 α hα F hFsm hFmem 0 0 (by norm_num)
    have hm := morrey_step_four (χ := χ) (F := F) (α := α) (C := Cl)
      (C₀ := Work.Spaces.HkNorm α 4 F) (M := M) (Km := Km)
      (a := zlo) (b := zhi) (c := tlo) (d := thi)
      (a' := zlo / 2) (b' := zhi + 1) (c' := tlo / 2) (d' := (thi + Real.pi / 2) / 2)
      hMor (le_of_lt hKmpos) hα hClpos (Work.Spaces.HkNorm_nonneg α 4 F) hχ2 hχcs hχnn
      hχle1 hχone hχzero hM1 hM2 hboxsub hFsm hFmem le_rfl
      ⟨hmix, hpz1, hpth1,
        by simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
          Work.Spaces.DzIter_zero, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using hpz2,
        hpzpth, hpthpz,
        by simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
          Work.Spaces.DzIter_zero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hpth2⟩
      p (hKbox hp) q (hKbox hq)
    have hdist : dist p q ^ (1 / 2 : ℝ) = Real.sqrt ‖p - q‖ := by
      rw [Real.sqrt_eq_rpow, dist_eq_norm]
    have hAnn : 0 ≤ Km * (2 * Real.sqrt (Cl + 3 * Cl * (16 + 17 * M ^ 2))) := by positivity
    have hMnn : 0 ≤ Work.Spaces.HkNorm α 4 F := Work.Spaces.HkNorm_nonneg α 4 F
    calc |F p.1 p.2 - F q.1 q.2|
        ≤ Km * (2 * Real.sqrt (Cl + 3 * Cl * (16 + 17 * M ^ 2)) * Work.Spaces.HkNorm α 4 F)
            * dist p q ^ (1 / 2 : ℝ) := hm
      _ = Km * (2 * Real.sqrt (Cl + 3 * Cl * (16 + 17 * M ^ 2)))
            * Work.Spaces.HkNorm α 4 F * Real.sqrt ‖p - q‖ := by rw [hdist]; ring
      _ ≤ (Km * (2 * Real.sqrt (Cl + 3 * Cl * (16 + 17 * M ^ 2))) + 1)
            * (1 + Work.Spaces.HkNorm α 4 F) * Real.sqrt ‖p - q‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          nlinarith [hAnn, hMnn]

theorem epsWP_equicont_tower {α B4 T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam}
    {K : Set (ℝ × ℝ)}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hK : IsCompact K)
    (hKQ : K ⊆ Work.FTS.EllipticEst.Q0)
    (hsm : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s))
    (hmem : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s))
    (hb : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s) ≤ B4) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ p ∈ K, ∀ q ∈ K,
      |Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s p.1 p.2
        - Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s q.1 q.2|
        ≤ C * (1 + B4) * Real.sqrt ‖p - q‖ := by
  obtain ⟨C, hCpos, hkey⟩ := holder_on_compact_of_HkMem_four (α := α) hα.1 hK hKQ
  refine ⟨C, hCpos, ?_⟩
  intro n s hs p hp q hq
  have hbF : Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s) ≤ B4 :=
    hb n s hs
  have hB4nn : 0 ≤ B4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 _) hbF
  have h := hkey (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s) (hsm n s hs)
    (hmem n s hs) p hp q hq
  have h1 : 1 + Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)
      ≤ 1 + B4 := by linarith
  have h2 : C * (1 + Work.Spaces.HkNorm α 4
        (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)) ≤ C * (1 + B4) :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt hCpos)
  exact h.trans (mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _))

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.morrey_four =====
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

set_option autoImplicit false


end Work.FTS.StrongEps.E5G
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.pzIterTwo_shiftSing_eq_PhiTil_add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

/-- **The second `z`-derivative of the shifted singular unknown, split off from `PhiTil`.**
`shiftSing α g Ψ = PhiTil α g Ψ + Gbar α g · sin 2θ` on the open quadrant (`Gbar` is the `z`-only
`Elliptic.Gbar`).  Hence at `z = 1` the `θ`-only factor pulls out of `pzIter 2 = ∂_z²`:
`∂_z²(shiftSing) = ∂_z²(PhiTil) + (Gbar)''(1) · sin 2θ`.
Route: the function identity `Construction.PhiTil α g Ψ = shiftSing α g Ψ - Gbar α g · sin 2θ`
(unfold `PhiTil`, `Theta`, `Gsing`, `Gstar`; note `Work.Elliptic.EllResid = Construction.PhiTil`
definitionally, and there may already be a proved identity such as `ellResid_eq_shiftSing_add`),
then rewriting `pzIter` on the open set and `GalBasis.GalApprox.pzIter_add`
(needs `ContDiffAt ℝ 2` of both `z`-slices at `1`, from `SmoothOpen` resp. `ContDiffOn ℝ 2` at
`1 ∈ Ioi 0`), finally `H2.STFacts.pzIter_const_mul` with the `θ`-only factor `c θ = sin 2θ`
(after commuting the product) and two `deriv_const_mul`-style steps.  Consumed by
`Work.FTS_EllLimOK.ProducerH.kappa_eq_zero`. -/
theorem pzIterTwo_shiftSing_eq_PhiTil_add {α : ℝ} {g Ψ : ℝ → ℝ → ℝ}
    (hΦ : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.PhiTil α g Ψ))
    (hG : ContDiffOn ℝ 2 (Work.Elliptic.Gbar α g) (Set.Ioi 0))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pzIter 2 (Work.FTS.EllExist.shiftSing α g Ψ) 1 θ
      = Work.Spaces.pzIter 2 (Work.Construction.PhiTil α g Ψ) 1 θ
        + (deriv (fun z => deriv (Work.Elliptic.Gbar α g) z) 1) * Real.sin (2 * θ) := by
  -- `shiftSing α g Ψ = PhiTil α g Ψ + Gbar α g · sin 2θ`, by unfolding the four definitions
  -- (`Elliptic.L12` and `Construction.L12` are definitionally equal).
  have hid : Work.FTS.EllExist.shiftSing α g Ψ
      = fun z θ => Work.Construction.PhiTil α g Ψ z θ
        + Work.Elliptic.Gbar α g z * Real.sin (2 * θ) := by
    funext z θ
    have hL : Work.Elliptic.L12 g z = Work.Construction.L12 g z := rfl
    simp only [Work.FTS.EllExist.shiftSing_apply, Work.Construction.PhiTil,
      Work.Construction.Theta, Work.Construction.s2, Work.Elliptic.Gsing,
      Work.Elliptic.Gstar, hL]
    ring
  rw [hid]
  -- the two `z`-slices are `C²` at `z = 1`: `PhiTil` from `SmoothOpen` on the open quadrant,
  -- `Gbar · sin 2θ` from `ContDiffOn` at `1 ∈ Ioi 0` and a constant `θ`-factor.
  have hsliceA : ContDiffAt ℝ 2 (fun z' => Work.Construction.PhiTil α g Ψ z' θ) 1 := by
    have hQ0 : (1, θ) ∈ Work.FTS.EllipticEst.Q0 := by
      rw [Work.FTS.EllipticEst.mem_Q0]
      exact ⟨by norm_num, hθ.1, hθ.2⟩
    have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Construction.PhiTil α g Ψ)) (1, θ) :=
      (hΦ.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hQ0)
    have hlin : ContDiffAt ℝ 2 (fun z' : ℝ => (z', θ)) (1 : ℝ) := by fun_prop
    have hcomp := hcd.comp (1 : ℝ) hlin
    simpa only [Function.comp_def, Function.uncurry] using hcomp
  have hsliceB : ContDiffAt ℝ 2 (fun z' => Work.Elliptic.Gbar α g z' * Real.sin (2 * θ)) 1 := by
    have h1 : ContDiffAt ℝ 2 (Work.Elliptic.Gbar α g) 1 :=
      hG.contDiffAt (isOpen_Ioi.mem_nhds (by norm_num : (1 : ℝ) ∈ Set.Ioi 0))
    exact h1.mul contDiffAt_const
  rw [Work.FTS.GalBasis.GalApprox.pzIter_add (i := 2)
    (X := Work.Construction.PhiTil α g Ψ)
    (Y := fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) (z := 1) (θ := θ)
    hsliceA hsliceB]
  -- the `θ`-only factor pulls out of `∂_z²`
  have hB : Work.Spaces.pzIter 2 (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) 1 θ
      = (deriv (fun z => deriv (Work.Elliptic.Gbar α g) z) 1) * Real.sin (2 * θ) := by
    have hGB : Work.Spaces.pzIter 2 (fun z θ => Work.Elliptic.Gbar α g z) 1 θ
        = deriv (fun z => deriv (Work.Elliptic.Gbar α g) z) 1 := rfl
    rw [show (fun z θ : ℝ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ))
        = (fun z θ => Real.sin (2 * θ) * Work.Elliptic.Gbar α g z) from by
          funext z θ; ring]
    rw [Work.FTS.H2.pzIter_const_mul (fun θ => Real.sin (2 * θ))
      (fun z _ => Work.Elliptic.Gbar α g z) 2 1 θ]
    rw [hGB]
    ring
  rw [hB]

end Work.FTS_EllLimOK.ProducerH
end
