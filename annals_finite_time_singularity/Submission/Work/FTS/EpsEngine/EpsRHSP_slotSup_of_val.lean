/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/EpsRHSP_slotSup_of_val.lean` — the slot sup bounds of the
# scheme's right-hand side, from **value** bounds of `epsWP`

`EpsEngine/NOTES_BallClause.md` §7 identified the `hsup` input of the interval-integral
`HkMem`-lemma as an interface item, and `EpsRHSP_slotSup_fam` discharges it from **slot** bounds of
the pre-mollified right-hand side `epsWP` — which are not in the tree (the `epsWP`-slot chapter).

This module removes that dependency: because `epsRHSP = Pz ∘ J_ε (epsWP)` is a *fixed-scale*
mollification, **all** the derivatives in a slot `D_z^j D_θ^i (J_ε X)` can be routed onto the
mollifier kernel (`mixed_Jeps_kernel_partial` at `j' = i' = 0`), so the slot is bounded by
`2^i · Kmass ρ ε j i · sup_{K'} |X|` — a **value** bound of `X` alone
(`abs_mixed_Jeps_le_sup`, proved).  Value bounds of `epsWP` *are* in the tree, uniformly in the
family and in the fake time, on every compact subset of the open quadrant
(`epsWP_sup_le_fam`, from `hEll`/`hstar`/`hml` and the class data).

Hence, for every compact `K ⊆ Q0`, there is a single `C ≥ 0` with

    |D_z^j D_θ^i (epsRHSP α ρ ε Φs E g s) p| ≤ C    (p ∈ K, s ∈ [0,T], j + i ≤ 4).

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.epsWP_sup_le_fam
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup
import Submission.Work.FTS.EpsEngine.abs_mixed_Jeps_le_sup
import Submission.Work.FTS.StrongEps.EpsE4Thr.AesmJfamP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The slot sup bounds of the scheme's right-hand side, from value bounds of `epsWP`.** -/
theorem EpsRHSP_slotSup_of_val {α C₀ Ce Cs T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g : Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hT : 0 ≤ T)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : MuLamOK α C₀ Φs E)
    (hC : ∀ s ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α (slice (JfamP ρ ε g) s))
    (hb4 : ∀ s ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ ε g) s) ≤ Ce)
    (hreg : ∀ s ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ ε Φs E g s))
    (hnorm : ∃ KW : ℝ, 0 ≤ KW ∧ ∀ s ∈ Set.Icc 0 T,
      Work.Spaces.HkMem α 4 (epsWP α ρ ε Φs E g s) ∧
        Work.Spaces.HkNorm α 4 (epsWP α ρ ε Φs E g s) ≤ KW)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j i : ℕ), j + i ≤ 4 → ∀ s ∈ Set.Icc 0 T, ∀ p ∈ K,
      |Work.Spaces.mixed j i (epsRHSP α ρ ε Φs E g s) p.1 p.2| ≤ C := by
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα.1 hα.2
  obtain ⟨CL, hCL0, hCL⟩ := abs_L12_Jeps_le (ρ := ρ) hρ
  obtain ⟨Cb, hCb0, hbump⟩ := exists_bound_mixed_bump K hK
  obtain ⟨KW, hKW0, hnorm'⟩ := hnorm
  have hc0 : 0 < pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  -- ### one bound per slot
  have key : ∀ j i : ℕ, j + i ≤ 4 → ∃ Cji : ℝ, 0 ≤ Cji ∧ ∀ s ∈ Set.Icc 0 T, ∀ p ∈ K,
      |Work.Spaces.mixed j i (Pz (Jeps ρ ε (epsWP α ρ ε Φs E g s))) p.1 p.2| ≤ Cji := by
    intro j i hji
    obtain ⟨K', hK'c, hK'Q, hKK', Csl, hCsl0, hsl⟩ :=
      abs_mixed_Jeps_le_sup (ρ := ρ) hρ (ε := ε) hε j i K hK hKQ
    obtain ⟨B, hBpos, hBval⟩ :=
      epsWP_sup_le_fam (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (T := T)
        (ρ := ρ) (Φs := Φs) (E := E) (G := fun _ => g) (ε := fun _ => ε)
        hα hρ (fun _ => ⟨hε, hε1⟩) hT hc1 hc2 hEll hstar hml
        (fun _ _ hs => hC _ hs) (fun _ _ hs => hb4 _ hs) (fun _ _ hs => hb6 _ hs) hK'c hK'Q
    refine ⟨Csl * B + (CL * KW / pzNorm) * Cb, by positivity, ?_⟩
    intro s hs p hp
    have hXsm : Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ ε Φs E g s) := hreg s hs
    obtain ⟨hmem, hnb⟩ := hnorm' s hs
    -- the slot of the mollified profile, from the *value* bound of `epsWP`
    have h1 : |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2| ≤ Csl * B :=
      hsl (epsWP α ρ ε Φs E g s) hXsm B hBpos.le (fun q hq => hBval 0 s hs q hq) p hp
    -- the coefficient of the rank-one correction
    have h2 : |Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0| ≤ CL * KW :=
      hCL hα hε hε1 hKW0 ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hXsm) hmem hnb
    -- the slots of the correction profile
    have h3 : |Work.Spaces.mixed j i bump p.1 p.2| ≤ Cb := hbump j i hji p hp
    -- the slot identity of the projection
    have hJsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Jeps ρ ε (epsWP α ρ ε Φs E g s)))
        Quad := (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
          (smoothOpen_Jeps ρ hρ hε ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hXsm))
    have hsplit := Work.FTS.StrongEps.EpsE4Thr.mixed_Pz_eq (n := 4) (a := j) (b := i)
      (w := Jeps ρ ε (epsWP α ρ ε Φs E g s)) (hJsm 4) (by omega) (hKQ hp)
    rw [hsplit]
    calc |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2
          - (Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
            * Work.Spaces.mixed j i bump p.1 p.2|
        ≤ |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2|
          + |(Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
            * Work.Spaces.mixed j i bump p.1 p.2| := by
          calc |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2
                - (Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
                  * Work.Spaces.mixed j i bump p.1 p.2|
              = |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2
                  + -((Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
                    * Work.Spaces.mixed j i bump p.1 p.2)| := by rw [sub_eq_add_neg]
            _ ≤ |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2|
                  + |-((Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
                    * Work.Spaces.mixed j i bump p.1 p.2)| := abs_add_le _ _
            _ = |Work.Spaces.mixed j i (Jeps ρ ε (epsWP α ρ ε Φs E g s)) p.1 p.2|
                  + |(Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
                    * Work.Spaces.mixed j i bump p.1 p.2| := by rw [abs_neg]
      _ ≤ Csl * B + (CL * KW / pzNorm) * Cb := by
          refine add_le_add h1 ?_
          rw [abs_mul]
          have hfac : |Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm|
              ≤ CL * KW / pzNorm := by
            rw [abs_div, abs_of_pos hc0]
            exact div_le_div_of_nonneg_right h2 hc0.le
          exact mul_le_mul hfac h3 (abs_nonneg _) (div_nonneg (mul_nonneg hCL0 hKW0) hc0.le)
  have key2 : ∀ j i : ℕ, ∃ Cji : ℝ, 0 ≤ Cji ∧ (j + i ≤ 4 → ∀ s ∈ Set.Icc 0 T, ∀ p ∈ K,
      |Work.Spaces.mixed j i (Pz (Jeps ρ ε (epsWP α ρ ε Φs E g s))) p.1 p.2| ≤ Cji) := by
    intro j i
    by_cases h : j + i ≤ 4
    · obtain ⟨C, hC0, hC⟩ := key j i h
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' h⟩
  choose Csl hCsl using key2
  refine ⟨∑ j ∈ Finset.range 5, ∑ i ∈ Finset.range 5, Csl j i, ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => (hCsl j i).1
  · intro j i hji s hs p hp
    have hmem : j ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
    have hmem2 : i ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
    have hsingle : Csl j i ≤ ∑ j' ∈ Finset.range 5, ∑ i' ∈ Finset.range 5, Csl j' i' := by
      refine le_trans (Finset.single_le_sum (f := fun i' => Csl j i')
        (fun i' _ => (hCsl j i').1) hmem2) ?_
      exact Finset.single_le_sum (f := fun j' => ∑ i' ∈ Finset.range 5, Csl j' i')
        (fun j' _ => Finset.sum_nonneg fun i' _ => (hCsl j' i').1) hmem
    exact le_trans ((hCsl j i).2 hji s hs p hp) hsingle

end Work.FTS.EpsEngine
