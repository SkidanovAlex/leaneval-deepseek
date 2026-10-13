/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/Feps_gates_of_xball_curve.lean`

**The three gates of the projected `ε`-scheme's right-hand side along an `XBall` curve.**

`NOTES_perz_intervalIntegral.md` §7 lists three inputs of the interval-integral `ℋ`-lemma as
"discharged producers" for the scheme's right-hand side `epsRHSP α ρ ε Φs E g s`, along a curve
`s ↦ slice g s` whose slices lie in the `XBall α ρ ε R C₀` invariant and are `EpsSq`-Lipschitz in
the fake time (`hEq`):

* **(meas)** the *sliced* a.e. strong measurability in `s` of every jet
  `mixed j i (epsRHSP … g s) z θ` at a point `(z,θ)` of the open quadrant
  (`EpsEngine/hmeas_slot_epsRHSP_fam_of_gate.lean`);
* **(joint)** the *joint* a.e. strong measurability of `(s,z,θ) ↦ HkIntegrand α 4 (epsRHSP … g s) z θ`
  for the triple product of the horizon and the quadrant measures
  (`EpsEngine/hjoint_HkIntegrand_epsRHSP_fam_of_gate.lean`, at `k = 4`);
* **(sup)** the uniform (in `s ∈ Icc 0 δ` and in the slot order `j + i ≤ 4`) bound of the slots on
  each compact `K ⊆ Q0` (`EpsEngine/EpsRHSP_slotSup_of_val.lean`).

The first two are instances of the siblings, verbatim.  The third needs one observation: the
producer `EpsRHSP_slotSup_of_val` (via `epsWP_sup_le_fam`) asks for a *uniform* `ℋ⁶`-bound of the
projected slices against the **same** constant `Ce` that occurs in `hEll`, and `hEll` says nothing
about the size of the profile.  But `XBall` carries the `EpsSq`-size `EpsSq α (slice g s) ≤ R`, and
`EpsSqTools.HkSq_JepsPz_le` turns it into the explicit uniform bound

  `Xn6 α (slice (JfamP ρ ε g) s) = HkNorm α 6 (Pz (J_ε (slice g s))) ≤ √(CJ (CJ/ε)¹² R) =: B6`

(the helper `Xn6_JfamP_le_of_XBall` below — the `(H4-norm)` shape of the notes).  So one runs the
producer at the *enlarged* constant `Ce' := max Ce B6`: the packages `EllPkgGo`/`EllPkgK` are
monotone in their constant (`ClassC.A4.EllPkgGo_mono`, `EllPkgK_mono`), and the `ℋ⁶`-bound
`≤ B6 ≤ Ce'` is available at every fake time.  The remaining two inputs of the producer are the
uniform open-quadrant smoothness of `epsWP` (`StrongEps.smoothOpen_epsWP`) and its uniform
`ℋ⁴`-size (`StrongEps.epsWP_hkMem4_bnd_fam`), both of which depend only on the three interface
hypotheses `hEll`, `hstar`, `hml` and on the class-`C`/ball clauses of `XBall`.

The negative-horizon case `δ < 0` is vacuous (`Icc 0 δ = ∅`), as in the `meas` sibling.

Everything here is complete (axioms `[propext, Classical.choice, Quot.sound]`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.EpsRHSP_slotSup_of_val
import Submission.Work.FTS.EpsEngine.hmeas_slot_epsRHSP_fam_of_gate
import Submission.Work.FTS.EpsEngine.hjoint_HkIntegrand_epsRHSP_fam_of_gate
import Submission.Work.FTS.EpsEngine.FepsData
import Submission.Work.FTS.StrongEps.smoothOpen_epsWP
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam
import Submission.Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le
import Submission.Work.FTS.ClassC.A4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open MeasureTheory Set Filter
open scoped Real Topology
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The uniform `ℋ⁶`-bound of the projected slices -/

/-- **The `ℋ⁶`-size of the projected slice `slice (JfamP ρ ε g) s = Pz (J_ε (slice g s))`, from the
`EpsSq`-size of the raw slice.**  There is `CJ > 0` (depending only on the kernel `ρ`) such that for
every `α ∈ (0,1]`, every `ε ∈ (0,1]` and every profile `u` in the `XBall α ρ ε R C₀` invariant,

  `Xn6 α (Pz (J_ε u)) ≤ √(CJ · (CJ/ε)¹² · R)`.

This is the `hb6` slot of the slot-sup gate (`EpsRHSP_slotSup_of_val`): the needed uniform `ℋ⁶`-bound
of the projected slices is *not* the elliptic constant `Ce` of `hEll` but the explicit `R`-dependent
number above.  No sign hypothesis on `R` is needed: for `R < 0` the hypothesis `XBall` is
unsatisfiable, since `0 ≤ EpsSq α u ≤ R` (`EpsSpace.EpsSq_nonneg`). -/
theorem Xn6_JfamP_le_of_XBall {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ CJ : ℝ, 0 < CJ ∧ ∀ {α ε R C₀ : ℝ}, α ∈ Set.Ioc 0 1 → 0 < ε → ε ≤ 1 →
      ∀ {g : Work.FTS.Galerkin.Fam} {s : ℝ},
        XBall α ρ ε R C₀ (Work.FTS.Galerkin.slice g s) →
        Work.FTS.StrongGlobal.Xn6 α
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)
          ≤ Real.sqrt (CJ * (CJ / ε) ^ (2 * 6) * R) := by
  obtain ⟨CJ, hCJpos, hCJ⟩ := Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le ρ hρ
  refine ⟨CJ, hCJpos, ?_⟩
  intro α ε R C₀ hα hε hε1 g s hX
  have hratio : 0 ≤ CJ / ε := div_nonneg hCJpos.le hε.le
  have hle : Work.Spaces.HkSq α 6
      (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s)))
      ≤ CJ * (CJ / ε) ^ (2 * 6) * R :=
    le_trans (hCJ α hα ε hε hε1 6 (by norm_num) (Work.FTS.Galerkin.slice g s)
        hX.smoothOpen hX.mem)
      (mul_le_mul_of_nonneg_left hX.sq_le (mul_nonneg hCJpos.le (pow_nonneg hratio _)))
  have hsq : Work.Spaces.HkSq α 6
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)
      ≤ CJ * (CJ / ε) ^ (2 * 6) * R := by
    simpa only [Work.FTS.StrongEps.slice_JfamP] using hle
  exact Real.sqrt_le_sqrt hsq

/-! ## The three gates -/

theorem Feps_gates_of_xball_curve {α C₀ R Ce Cs Lw δ ε : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (hP : ∀ s ∈ Set.Icc (0 : ℝ) δ,
      Work.FTS.EpsEngine.XBall α ρ ε R C₀ (Work.FTS.Galerkin.slice g s))
    (hEq : ∀ s ∈ Set.Icc (0 : ℝ) δ, ∀ t ∈ Set.Icc (0 : ℝ) δ,
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g t z θ)
        ≤ Lw * (s - t) ^ 2) :
    (∀ (j i : ℕ), j + i ≤ 4 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        MeasureTheory.AEStronglyMeasurable
          (fun s : ℝ => Work.Spaces.mixed j i
            (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) z θ)
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) δ)))
    ∧ MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ × ℝ => Work.Spaces.HkIntegrand α 4
          (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g p.1) p.2.1 p.2.2)
        ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) δ)).prod
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    ∧ (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) δ, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ 4 →
          |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) q.1 q.2| ≤ C) := by
  refine ⟨?_, ?_, ?_⟩
  · -- ## (meas): the sliced a.e. strong measurability of every jet (the sibling gate, verbatim)
    intro j i hji z θ hQ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
    exact hmeas_slot_epsRHSP_fam_of_gate hα hρ hε hε1 hEll hstar hml hR hLw hP hEq j i hz
      ⟨hθ0, hθ1⟩
  · -- ## (joint): the joint a.e. strong measurability of the `ℋ⁴`-integrand (the sibling gate)
    exact hjoint_HkIntegrand_epsRHSP_fam_of_gate (k := 4) hα hρ hε hε1 hEll hstar hml hR hLw
      hP hEq
  · -- ## (sup): the uniform slot bound on a compact subset of the open quadrant
    intro K hK hKQ
    rcases lt_or_ge δ 0 with hδneg | hδnonneg
    · -- the horizon is empty: the bound is vacuous
      have hemp : Set.Icc (0 : ℝ) δ = ∅ := Set.Icc_eq_empty_of_lt hδneg
      refine ⟨0, le_rfl, ?_⟩
      intro s hs
      rw [hemp] at hs
      exact absurd hs (by simp)
    · -- ## the uniform `ℋ⁶`-bound of the projected slices, from `EpsSq α (slice g s) ≤ R`
      obtain ⟨CJ, _hCJpos, hXn6⟩ := Xn6_JfamP_le_of_XBall (ρ := ρ) hρ
      set B6 : ℝ := Real.sqrt (CJ * (CJ / ε) ^ (2 * 6) * R) with hB6def
      set Ce' : ℝ := max Ce B6 with hCe'def
      have hb6 : ∀ s ∈ Set.Icc (0 : ℝ) δ,
          Work.FTS.StrongGlobal.Xn6 α
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ Ce' :=
        fun s hs => le_trans (hXn6 hα hε hε1 (hP s hs)) (le_max_right _ _)
      -- ## the elliptic packages at the enlarged constant `Ce'`
      have hEll' : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
          Work.FTS.VocabO.EllPkgGo α Ce' u (E u) ∧
            Work.FTS.ClassC.EllPkgK α 6 Ce' u (E u) :=
        fun u hu =>
          ⟨Work.FTS.ClassC.EllPkgGo_mono hα.1 (hEll u hu).1
              (by rw [hCe'def]; exact le_max_left _ _),
           Work.FTS.ClassC.EllPkgK_mono (hEll u hu).2
              (by rw [hCe'def]; exact le_max_left _ _)⟩
      -- ## the class-`C` and ball clauses of the projected slices, from `XBall`
      have hC : ∀ s ∈ Set.Icc (0 : ℝ) δ, Work.FTS.ClassC.ClassC α
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) :=
        fun s hs => (hP s hs).classC
      have hb4 : ∀ s ∈ Set.Icc (0 : ℝ) δ, Work.FTS.Nonlin.Xn α
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ C₀ * α ^ 2 :=
        fun s hs => (hP s hs).ball
      -- ## the uniform open-quadrant smoothness and `ℋ⁴`-size of `epsWP`
      have hreg : ∀ s ∈ Set.Icc (0 : ℝ) δ,
          Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) :=
        Work.FTS.StrongEps.smoothOpen_epsWP (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (ρ := ρ)
          (Φs := Φs) (E := E) (g := g) (ε := ε) hα hEll hstar hC
      obtain ⟨KW, hKW, hn⟩ := Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam
        (α := α) (C₀ := C₀) (Ce := Ce') (Cs := Cs) (T := δ) (ρ := ρ) (Φs := Φs) (E := E)
        (G := fun _ => g) (ε := fun _ => ε) hα hEll' hstar hml
        (fun _ s hs => hC s hs) (fun _ s hs => hb4 s hs) (fun _ s hs => hb6 s hs)
      have hnorm : ∃ KW' : ℝ, 0 ≤ KW' ∧ ∀ s ∈ Set.Icc (0 : ℝ) δ,
          Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) ∧
            Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) ≤ KW' :=
        ⟨KW, hKW.le, fun s hs => hn 0 s hs⟩
      -- ## the producer of the slot-sup gate
      obtain ⟨C, hC0, hCb⟩ := EpsRHSP_slotSup_of_val (α := α) (C₀ := C₀) (Ce := Ce')
        (Cs := Cs) (T := δ) (ε := ε) (ρ := ρ) (Φs := Φs) (E := E) (g := g)
        hα hρ hε hε1 hδnonneg hEll' hstar hml hC hb4 hb6 hreg hnorm hK hKQ
      exact ⟨C, hC0, fun s hs q hq j i hji => hCb j i hji s hs q hq⟩

end Work.FTS.EpsEngine
