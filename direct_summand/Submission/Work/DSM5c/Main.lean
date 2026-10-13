import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5c.Basic
import Submission.Work.DSM5c.CharP
import Submission.Work.DSM5c.chartRing_eq_bot_of_subsingleton
import Submission.Work.DSM5c.Main.area_M5c_of_LpInput
import Submission.Work.DSM5c.Eta.exists_chartMapU
import Submission.Work.DSM5c.Lp.almostAcyc_chartLQU
import Submission.Work.DSM5c.G2.isSMulRegular_chartUntiltU
import Submission.Work.DSM5c.M5bProved

/-!
# DSM5c — mixed-characteristic area (M3-free route): the M5c node

This module is the assembly point of the subproject `DSM5c`.  The requested deliverable is
`DSMap.Mix2.area_M5c_proved`, a theorem *type-identical* to the frozen node

`DSMap.Mix2.area_M5c` (`Submission/Work/DSMap/Mix2.lean`, M5c of the MIX2 design,
`sources/dsmap/direct_summand_mix2.md` Task 1 (4) and `sources/dsmap/direct_summand_mix_design.md`
§3):

> `W` is a perfectoid ring in the sense of `DSMap.PerfectoidData p W`, `t : ι → W` is a finite
> family with a compatible system `tr : ι → ℕ → W` of `p`-power roots, and `t j₀ = QW.ϖ 0 ^ e`;
> then there are a presheaf `Dp` of `W`-modules on the Čech index category `(Finset ι)ᵒᵖᵒᵖ` and a
> natural map `η` from the chart presheaf to `Dp` such that for every `m` the coaugmented Čech
> complex `W → Č(Dp)` is `⇑ϖ`-almost acyclic modulo `(p ^ m)`.

**Status.**  The node is *proved conditional on the characteristic-`p` input*, and both the
conditional statement and the discharged deliverable live in this file:

* **`DSMap.Mix2.area_M5c_of_M5bInterface`** (below) is the frozen conclusion of
  `DSMap.Mix2.area_M5c`, at an arbitrary universe, from `Work.DSM5c.M5bInterface.{a}` alone — the
  pinned interface of the sibling subproject `DSM5b`.  `#print axioms` =
  `[propext, Classical.choice, Quot.sound]`, and the statement is the frozen one verbatim plus that
  one hypothesis.  It is importable today (`lake env lean Submission/Work/DSM5c/Main.lean`
  succeeds), so `area_M5d`/`area_M6G` can be wired against it at once;
* **`DSMap.Mix2.area_M5c_proved`** (below, the last declaration of this file) is that statement
  applied to `Work.DSM5c.m5bInterface_proved` (`Submission/Work/DSM5c/M5bProved.lean`) — the
  requested deliverable, type-identical to the frozen node (`rfl`-checked at the end of the file).
  Its *only* axiom beyond `[propext, Classical.choice, Quot.sound]` is the `sorryAx` inherited from
  the sibling's `DSMap.Mix2.area_M5b_proved`, whose single remaining hole is
  `Work.DSM5b.chartCechH0_root_killing` (`Submission/Work/DSM5b/chartCechH0_root_killing.lean`);
  nothing of *this* directory contributes a `sorry`, and the theorem becomes axiom-clean with no
  edit here as soon as that sibling lemma is proved.  The thin module
  `Submission/Work/DSM5c/M5cProved.lean` re-exports it for continuity (it is where the declaration
  used to sit).

Everything else of the node is proved here, all axiom-clean (audit:
`Submission/Work/DSM5c/AxiomCheckFinal.lean`): the chart presheaf `Dp = Work.DSM5c.chartD`; the
chart map `η` (gap G1: `Work.DSM5c.Eta.exists_chartMapU`); the `p`-torsion-freeness of the chart
untilts (gap G2: `Work.DSM5c.G2.isSMulRegular_chartUntiltU`); PB2 and the mod-`p` charts
(`Work.DSM5c.pb2Equiv`, `chartLAlg`, `chartLMap`); the surjection `Dp ⟶ Lp` with kernel `(p)·⊤`
(`Work.DSM5c.Lp.chartDToLp_existsU`); the characteristic-`p` input on the mod-`p` chart complex
(`Work.DSM5c.Lp.almostAcyc_chartLQU`); the cocycle condition
(`Work.DSM5c.Cech.chartCoaug_isCocycleU`); the transport and the dévissage
(`Work.DSM5c.Devissage.almostAcyc_of_surjective_kernel_v2`, `Work.DSM5c.almostAcyc_span_pow`); and
the assembly `Work.DSM5c.Main.area_M5c_of_LpInput`.  See `Submission/Work/DSM5c/NOTES.md` §§21–25
for the account of the proof and §26 for the verification performed on it, the location of the
deliverable and the exact state of the one external dependency.

## Contents

* `Work.DSM5c.area_M5c_of_honest_charts` — the frozen conclusion, *reduced* to the honest chart
  complex: it is enough that `W → Č(chartPresheaf t)` itself is almost acyclic mod every `p ^ m`
  (witnesses `Dp := chartPresheaf t`, `η := 𝟙`).  This isolates the exact place where the
  perfection/untilt of the charts is needed (the honest chart complex is *not* almost acyclic in
  general: the blowup of `W` in `(t i)` has non-vanishing higher cohomology, cf. `NOTES.md` §3).
* `Work.DSM5c.chartRing_eq_bot_of_subsingleton` (`Submission/Work/DSM5c/chartRing_eq_bot_of_subsingleton.lean`)
  — for a subsingleton index type the chart ring is `⊥` (an early ingredient of the one-chart case;
  the general argument assembled below covers *every* index type with `[Finite ι]`, so it is not
  needed by the assembly).
* `Work.DSM5c.area_M5c_of_subsingleton` — the fully degenerate case where `W` is the zero ring
  (equivalently, by `Work.DSM5c.not_isUnit_of_nontrivial`, the case in which `p` is a unit).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.DSM5c

universe a

open CategoryTheory
open DSMap DSMap.Mix DSMap.Mix2

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W]

/-! ## A fully degenerate case: the zero ring -/

section SubsigletonRing

/-- **Every module over a subsingleton (commutative) ring is a subsingleton**: in the zero ring
`1 = 0`, whence `x = 1 • x = 0 • x = 0`. -/
theorem subsingleton_of_subsingleton_ring (W : Type a) [CommRing W] [Subsingleton W]
    (M : Type a) [AddCommGroup M] [Module W M] : Subsingleton M :=
  ⟨fun x y => by
    have h : (1 : W) = 0 := Subsingleton.elim _ _
    calc x = (1 : W) • x := (one_smul W x).symm
      _ = (0 : W) • x := by rw [h]
      _ = 0 := zero_smul W x
      _ = (0 : W) • y := (zero_smul W y).symm
      _ = (1 : W) • y := by rw [← h]
      _ = y := one_smul W y⟩

/-- **The M5c conclusion for the zero ring.**  If `W` is a subsingleton, the conclusion of the
frozen `DSMap.Mix2.area_M5c` holds for every choice of `t`, `tr`, `j₀`, `e`: all modules are
subsingletons, so all three clauses of `AlmostAcyc` are automatic (take `w = 0`, `y = 0`).

This is exactly the case `p` a unit: for a nontrivial `PerfectoidData`, `p` is never a unit
(`Work.DSM5c.not_isUnit_of_nontrivial`), so the tilt `PreTilt W p` of the characteristic-`p` input
is available in all the cases not covered here. -/
theorem area_M5c_of_subsingleton (Q : PerfectoidData p W) [Subsingleton W]
    {ι : Type a} [DecidableEq ι] (t : ι → W) :
    ∃ (Dp : (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat.{a} W) (η : chartPresheaf t ⟶ Dp),
      ∀ m, AlmostAcyc Q.ϖ (Ideal.span {(p : W) ^ m})
        ((cechComplexFunctor (chartIdx ι)).obj Dp)
        (chartCoaugW t ≫ ((cechComplexFunctor (chartIdx ι)).map η).f 0) := by
  refine ⟨(Functor.const ((Finset ι)ᵒᵖᵒᵖ)).obj (ModuleCat.of W W), ?_, fun m => ?_⟩
  · refine { app := fun _ => 0, naturality := fun S T f => ?_ }
    haveI : Subsingleton
        (↑(((Functor.const ((Finset ι)ᵒᵖᵒᵖ)).obj (ModuleCat.of W W)).obj T)) :=
      subsingleton_of_subsingleton_ring W _
    ext x
    exact Subsingleton.elim _ _
  · -- all three clauses of `AlmostAcyc` are automatic: every element of `W` is `0`, and so is
    -- every element of every `W`-module (`1 = 0`)
    refine ⟨fun w _ k => ?_, fun z _ k => ?_, fun q z _ k => ?_⟩
    · have h0 : Q.ϖ k * w = 0 := Subsingleton.elim _ _
      rw [h0]
      exact Ideal.zero_mem _
    · refine ⟨0, ?_⟩
      have hz : z = 0 := by
        rw [← one_smul W z, (Subsingleton.elim (1 : W) 0 : (1 : W) = 0), zero_smul]
      rw [hz, smul_zero, map_zero, sub_zero]
      exact Submodule.zero_mem _
    · refine ⟨0, ?_⟩
      have hz : z = 0 := by
        rw [← one_smul W z, (Subsingleton.elim (1 : W) 0 : (1 : W) = 0), zero_smul]
      rw [hz, smul_zero, map_zero, sub_zero]
      exact Submodule.zero_mem _

end SubsigletonRing

/-! ## Reduction to the honest chart complex -/

section Honest

/-- **The frozen M5c conclusion, reduced to the honest chart complex.**  If the coaugmented chart
Čech complex `W → Č(chartPresheaf t)` is itself almost acyclic modulo every `p ^ m` with respect to
`⇑ϖ`, then the conclusion of `DSMap.Mix2.area_M5c` holds (witnesses: `Dp := chartPresheaf t` and
`η := 𝟙`).

This is the exact shape of the statement that the characteristic-`p` input would have to produce
*if* the honest charts were used; the design instead replaces `chartPresheaf t` by the untilts of
the completed perfections of the *tilted* charts, precisely because the honest chart complex has
non-vanishing higher cohomology in general. -/
theorem area_M5c_of_honest_charts (Q : PerfectoidData p W) {ι : Type a} [Finite ι]
    [DecidableEq ι] (t : ι → W)
    (h : ∀ m, AlmostAcyc Q.ϖ (Ideal.span {(p : W) ^ m}) (chartCech t) (chartCoaugW t)) :
    ∃ (Dp : (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat.{a} W) (η : chartPresheaf t ⟶ Dp),
      ∀ m, AlmostAcyc Q.ϖ (Ideal.span {(p : W) ^ m})
        ((cechComplexFunctor (chartIdx ι)).obj Dp)
        (chartCoaugW t ≫ ((cechComplexFunctor (chartIdx ι)).map η).f 0) := by
  refine ⟨chartPresheaf t, 𝟙 _, fun m => ?_⟩
  simpa using h m

end Honest

/-! ## What the characteristic-`p` half already provides

`Work.DSM5c.M5bInput`/`M5bInterface` (`Submission/Work/DSM5c/CharP.lean`) record the input
`DSMap.Mix2.area_M5b` as an interface and instantiate it at the tilted datum of the M5c
hypotheses (`Work.DSM5c.m5bInput_tilt`); `Work.DSM5c.chartRing_eq_bot_of_subsingleton` is the
chart-ring computation for a one-element index set.  The remaining nodes (untilt functor PB3,
Tor-independence PB4, the chart-level comparison and the dévissage) are listed with precise
statements in `Submission/Work/DSM5c/NOTES.md`. -/

/-! ## The assembly: the frozen conclusion from the pinned mod-`p`-chart input

`Work.DSM5c.Main.area_M5c_of_LpInput` (`Submission/Work/DSM5c/Main/area_M5c_of_LpInput.lean`) is the
frozen conclusion of `DSMap.Mix2.area_M5c` (at an arbitrary universe) obtained from the pinned
mod-`p`-chart input (transport steps 3–4), under the non-degeneracy hypothesis
`Fact (¬IsUnit (p : W))`.  The theorem below removes that hypothesis by the degeneracy split
`Nontrivial W` / `Subsingleton W`, and so has *exactly* the hypotheses of the frozen node apart from
the pinned input `hL` (which is being proved as
`Work.DSM5c.Lp.almostAcyc_chartLQU` from `Work.DSM5c.M5bInterface`).

The final `DSMap.Mix2.area_M5c_proved` (the last declaration of this file) is then this statement with
the pinned input discharged through `Work.DSM5c.Lp.almostAcyc_chartLQU` at
`Work.DSM5c.m5bInterface_proved` (`Submission/Work/DSM5c/M5bProved.lean`); that step is valid, but the
resulting axiom set carries the sibling's `sorryAx` until
`Work.DSM5b.chartCechH0_root_killing` is proved. -/

section Assembly

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W]

/-! ### The assembly

`Work.DSM5c.Main.area_M5c_of_LpInput`
(`Submission/Work/DSM5c/Main/area_M5c_of_LpInput.lean`) gives the frozen conclusion (at an
arbitrary universe) from the hypotheses of `DSMap.Mix2.area_M5c` together with
`Fact (¬IsUnit (p : W))`, the surjectivity of Fontaine's theta map (derivable from `QW` as
`Work.DSM5c.G2.U.surjective_fontaineTheta_of_perfectoidData QW`) and the *pinned* mod-`p`-chart
input of transport steps 3–4 — which is exactly `Work.DSM5c.Lp.almostAcyc_chartLQU` applied to the
chart map `η` of `Work.DSM5c.Eta.exists_chartMapU`.

The frozen statement has neither `[Fact ¬IsUnit (p : W)]` nor
`[IsAdicComplete (Ideal.span {(p : W)}) W]`, so the proof begins with the degeneracy split
`Nontrivial W` / `Subsingleton W`; in the `Nontrivial` branch the two instances are installed with
`haveI` (`Work.DSM5c.not_isUnit_of_nontrivial`, and `QW.complete`), which is why the split is inline
here rather than in a separate instance-free lemma. -/

end Assembly

end Work.DSM5c

namespace DSMap.Mix2

open CategoryTheory DSMap DSMap.Mix

universe a

/-- **The M5c node of the MIX2 route, from the characteristic-`p` input**: the frozen conclusion of
`DSMap.Mix2.area_M5c`, proved from `Work.DSM5c.M5bInterface.{a}` (the sibling subproject DSM5b's
interface for the characteristic-`p` input `area_M5b`).

The only pieces used are the ones proved in this directory:

* `Work.DSM5c.Eta.exists_chartMapU` — the chart map `η` with `η_S (algebraMap w) = w • 1`
  (gap G1);
* `Work.DSM5c.Lp.almostAcyc_chartLQU` — the characteristic-`p` input on the mod-`p` chart complex,
  pinned by the `he`-equation of the transport (transport steps 3–4);
* `Work.DSM5c.Lp.chartDToLp_existsU` — the surjection `Dp ⟶ Lp` with kernel `(p)·⊤` (step 5);
* `Work.DSM5c.Devissage.almostAcyc_of_surjective_kernel_v2` — the transport;
* `Work.DSM5c.Cech.chartCoaug_isCocycleU` — the cocycle condition;
* `Work.DSM5c.G2.isSMulRegular_chartUntiltU` — `p`-torsion-freeness of the chart untilts;
* `Work.DSM5c.almostAcyc_span_pow` — the dévissage `(p) ↦ (p^m)`;
* and the degenerate case `Work.DSM5c.area_M5c_of_subsingleton`. -/
theorem area_M5c_of_M5bInterface (p : ℕ) [Fact p.Prime] (W : Type a) [CommRing W]
    (QW : PerfectoidData p W) {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k)
    (j₀ : ι) (e : ℕ) (hj₀ : t j₀ = QW.ϖ 0 ^ e)
    (hM5b : Work.DSM5c.M5bInterface.{a}) :
    ∃ (Dp : (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat.{a} W) (η : chartPresheaf t ⟶ Dp),
      ∀ m, AlmostAcyc QW.ϖ (Ideal.span {(p : W) ^ m})
        ((cechComplexFunctor (chartIdx ι)).obj Dp)
        (chartCoaugW t ≫ ((cechComplexFunctor (chartIdx ι)).map η).f 0) := by
  by_cases hW : Nontrivial W
  · haveI := hW
    haveI hfact : Fact ¬IsUnit (p : W) := ⟨Work.DSM5c.not_isUnit_of_nontrivial QW⟩
    haveI hadic : IsAdicComplete (Ideal.span {(p : W)}) W := QW.complete
    have hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)) :=
      Work.DSM5c.G2.U.surjective_fontaineTheta_of_perfectoidData QW
    exact Work.DSM5c.Main.area_M5c_of_LpInput QW t tr htr0 htr j₀ e hj₀ hθ
      (fun η hη => Work.DSM5c.Lp.almostAcyc_chartLQU hM5b QW hθ t tr htr0 htr j₀ e η hη)
  · haveI hsub : Subsingleton W := not_nontrivial_iff_subsingleton.mp hW
    exact Work.DSM5c.area_M5c_of_subsingleton QW t

/-- **The requested deliverable `DSMap.Mix2.area_M5c_proved`**: the frozen M5c node
`DSMap.Mix2.area_M5c` (`Submission/Work/DSMap/Mix2.lean`, read-only) discharged with the
characteristic-`p` input of the sibling subproject `DSM5b`, `DSMap.Mix2.area_M5b_proved`, which
enters as `Work.DSM5c.m5bInterface_proved` (`Submission/Work/DSM5c/M5bProved.lean`).

Everything *outside* the characteristic-`p` input is proved in this directory and is axiom-clean;
`#print axioms` of this declaration is
`[propext, sorryAx, Classical.choice, Quot.sound]`, the `sorryAx` coming solely from the sibling's
`Work.DSM5b.chartCechH0_root_killing`, which is the one hole left in `DSMap.Mix2.area_M5b_proved`.
As soon as that sibling lemma is proved, this declaration is `[propext, Classical.choice,
Quot.sound]` with no change here; the assembly is `area_M5c_of_M5bInterface` above.

The frozen-statement identity is checked by the `rfl` at the end of the file. -/
theorem area_M5c_proved (p : ℕ) [Fact p.Prime] (W : Type a) [CommRing W] (QW : PerfectoidData p W)
    {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k)
    (j₀ : ι) (e : ℕ) (hj₀ : t j₀ = QW.ϖ 0 ^ e) :
    ∃ (Dp : (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat.{a} W) (η : chartPresheaf t ⟶ Dp),
      ∀ m, AlmostAcyc QW.ϖ (Ideal.span {(p : W) ^ m})
        ((cechComplexFunctor (chartIdx ι)).obj Dp)
        (chartCoaugW t ≫ ((cechComplexFunctor (chartIdx ι)).map η).f 0) :=
  area_M5c_of_M5bInterface p W QW t tr htr0 htr j₀ e hj₀ Work.DSM5c.m5bInterface_proved

/-- **Type-identity check**: the discharged node is *definitionally* the frozen node
`DSMap.Mix2.area_M5c` (`Submission/Work/DSMap/Mix2.lean`), so the deliverable has exactly the frozen
statement (no extra hypotheses, no weakened conclusion).  This uses only the *statements*. -/
example : @area_M5c_proved.{a} = @area_M5c.{a} := rfl

/-- **Type-identity check, conditional form**: `area_M5c_of_M5bInterface` is the frozen node with the
single extra argument `Work.DSM5c.M5bInterface.{a}` and nothing else changed. -/
example : @area_M5c_of_M5bInterface.{a} =
    fun (p : ℕ) (_ : Fact p.Prime) (W : Type a) (_ : CommRing W) (QW : PerfectoidData p W)
      (ι : Type a) (_ : Finite ι) (_ : DecidableEq ι) (t : ι → W) (tr : ι → ℕ → W)
      (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k)
      (j₀ : ι) (e : ℕ) (hj₀ : t j₀ = QW.ϖ 0 ^ e) (_ : Work.DSM5c.M5bInterface.{a}) =>
      @area_M5c.{a} p _ W _ QW ι _ _ t tr htr0 htr j₀ e hj₀ := rfl

end DSMap.Mix2
