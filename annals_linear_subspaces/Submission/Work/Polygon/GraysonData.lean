import Mathlib
import Submission.GeometryOfNumbers.CovolPluecker
import Submission.GeometryOfNumbers.SubLatticeCovol

/-!
# Grayson data on submodules: `latticeCovol` and the Euclidean Lemma-3 socket

The §3 Grayson polygon of a lattice `Λ ≤ ℝᵈ` (de Saxcé, paper §3) is built from the data
`φ(W) = log‖W‖` over the discrete subgroups `W ≤ Λ`, where `‖W‖` is the covolume of `W`
measured **inside its own real span** `span ℝ W` (in the Euclidean model the quadratic
rank term is unnecessary — `log covol` is already exactly submodular).

This module pins the **consumer socket** for the P1 engine
(`Submission.CovolPluecker.covolPluecker_aligned_log`): the covolume of an actual
`ℤ`-submodule of `ℝᵈ` (`latticeCovol`, an intrinsic quantity independent of any ambient
lattice), its identification with the wedge norm / `covolFamily` for `ℤ`-spans of
`ℝ`-independent ambient families (`latticeCovol_span`), and the **Grayson-data
submodularity lemma** `graysonData_log_submodularity`: for two saturated `ℤ`-submodules
`W₁, W₂ ≤ ℝᵈ` whose `ℤ`-bases are aligned (`u ++ x` of `W₁`, `u ++ y` of `W₂` over a
common `ℤ`-basis `u` of `W₁ ⊓ W₂`, `(u ++ x) ++ y` of `W₁ ⊔ W₂`):

    log covol(W₁) + log covol(W₂) ≥ log covol(W₁ ⊓ W₂) + log covol(W₁ ⊔ W₂)

— the Euclidean Lemma-3 inequality in the exact quantity the Grayson data consumes,
instantiated from the aligned-family engine.  Consumers obtain the aligned bases from the
Commons pure-basis-extension theorems; here we take them as explicit inputs (all variables
explicit, no hidden instances).
-/

noncomputable section

open Set Filter Metric MeasureTheory Module Real BigOperators exteriorPower
open scoped ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Submission.GraysonData

/-- The standard Euclidean space `ℝᵈ`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- **Intrinsic covolume of a `ℤ`-submodule**: the covolume of `W` measured inside its own
real span `span ℝ W` (i.e. `W` as a full-rank lattice of `V := span ℝ (W : Set E)`).
Equals the fundamental-domain volume of `W` in `V` whenever `W` is discrete there; the raw
function is defined unconditionally. -/
noncomputable def latticeCovol {d : ℕ} (W : Submodule ℤ (E d)) : ℝ :=
  let V : Submodule ℝ (E d) := Submodule.span ℝ (W : Set (E d))
  ZLattice.covolume (E := V) (Submodule.comap (V.subtype.restrictScalars ℤ) W)

/-- **Covol-wedge bridge, subgroup form**: for an `ℝ`-independent ambient family
`v : Fin r → E` (`0 < r`), the intrinsic covolume of the `ℤ`-span of `v` equals the
ambient wedge norm `‖ιMulti ℝ r v‖` (equivalently `covolFamily v` of the engine). -/
lemma latticeCovol_span {d r : ℕ} (hr : 0 < r) (v : Fin r → E d)
    (hv : LinearIndependent ℝ v) :
    latticeCovol (Submodule.span ℤ (Set.range v)) =
      ‖exteriorPower.ιMulti ℝ r v‖ := by
  classical
  let W : Submodule ℤ (E d) := Submodule.span ℤ (Set.range v)
  let V : Submodule ℝ (E d) := Submodule.span ℝ (W : Set (E d))
  have hVs : V = Submodule.span ℝ (Set.range v) := by
    dsimp [V, W]
    rw [Submodule.span_span_of_tower (R := ℤ) (S := ℝ) (M := E d) (s := Set.range v)]
  have hmemV : ∀ i : Fin r, v i ∈ V := by
    intro i
    rw [hVs]
    exact Submodule.subset_span (Set.mem_range_self i)
  let uV : Fin r → V := fun i => ⟨v i, hmemV i⟩
  have huV : LinearIndependent ℝ uV := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hcE : (∑ i : Fin r, c i • v i) = 0 := by
      have hc' := congrArg (fun x : V => (V.subtype x)) hc
      simpa [uV] using hc'
    exact (Fintype.linearIndependent_iff.mp hv) c hcE
  have hfinV : Module.finrank ℝ V = r := by
    let V' : Submodule ℝ (E d) := Submodule.span ℝ (Set.range v)
    let e : V ≃ₗ[ℝ] V' := LinearEquiv.ofEq V V' hVs
    have h1 : Module.finrank ℝ V = Module.finrank ℝ V' := LinearEquiv.finrank_eq e
    have h2 : Module.finrank ℝ V' = r := by
      dsimp [V']
      rw [finrank_span_eq_card (R := ℝ) (b := v) hv]
      simp
    exact h1.trans h2
  have hspV : ⊤ ≤ Submodule.span ℝ (Set.range uV) := by
    exact Submission.SubLatticeCovol.span_top_of_linearIndependent uV huV hfinV
  let bV : Basis (Fin r) ℝ V := Module.Basis.mk huV hspV
  have hbv : ∀ i : Fin r, (bV i : V) = uV i := congr_fun (Module.Basis.coe_mk huV hspV)
  let f : V →ₗ[ℤ] E d := V.subtype.restrictScalars ℤ
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.coe_injective
    exact hxy
  have hfr : (fun i : Fin r => f (bV i)) = v := by
    funext i
    calc
      f (bV i) = ((bV i : V) : E d) := rfl
      _ = ((uV i : V) : E d) := by rw [hbv i]
      _ = v i := rfl
  have himg : f '' Set.range bV = Set.range v := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      rcases hy with ⟨i, hyi⟩
      refine ⟨i, ?_⟩
      calc
        v i = f (bV i) := (congr_fun hfr i).symm
        _ = f y := by rw [← hyi]
        _ = x := hxy
    · intro hx
      rcases hx with ⟨i, rfl⟩
      refine ⟨bV i, ⟨i, rfl⟩, ?_⟩
      exact congr_fun hfr i
  have hLmap : W = (Submodule.span ℤ (Set.range bV)).map f := by
    dsimp [W]
    rw [Submodule.map_span, himg]
  have hEq : Submodule.comap f W = Submodule.span ℤ (Set.range bV) := by
    rw [hLmap]
    exact Submodule.comap_map_eq_of_injective hinj (Submodule.span ℤ (Set.range bV))
  have hfam : (fun i : Fin r => ((bV i : V) : E d)) = v := by
    funext i
    calc
      ((bV i : V) : E d) = ((uV i : V) : E d) := by rw [hbv i]
      _ = v i := rfl
  calc
    latticeCovol (Submodule.span ℤ (Set.range v))
        = ZLattice.covolume (E := V) (Submodule.comap f W) := by
          rfl
    _ = ZLattice.covolume (E := V) (Submodule.span ℤ (Set.range bV)) := by
          rw [hEq]
    _ = ‖exteriorPower.ιMulti ℝ r (fun i : Fin r => ((bV i : V) : E d))‖ := by
          exact Submission.SubLatticeCovol.covol_wedge_of_submodule_basis (d := d) (r := r) hr V bV
    _ = ‖exteriorPower.ιMulti ℝ r v‖ := by
          rw [hfam]

/-- **Grayson-data submodularity (Euclidean Lemma 3, subgroup socket).**  Let
`W₁, W₂ ≤ ℝᵈ` be saturated `ℤ`-submodules whose `ℤ`-bases are aligned as `u ++ x` (of
`W₁`) and `u ++ y` (of `W₂`) over a common `ℤ`-basis `u` of `W₁ ⊓ W₂`, with
`(u ++ x) ++ y` a `ℤ`-basis of `W₁ ⊔ W₂`.  Then the log-covolumes are submodular:

`log covol(W₁) + log covol(W₂) ≥ log covol(W₁ ⊓ W₂) + log covol(W₁ ⊔ W₂)`.

This is the inequality the Grayson data (`φ(W) = log covol(W)` over saturated subgroups
of the flow lattice) consumes; its right-hand side involves `W₁ ⊓ W₂` and `W₁ ⊔ W₂` —
both subgroups of the ambient lattice — measured intrinsically in their own real spans. -/
theorem graysonData_log_submodularity {d m a b : ℕ} (hm : 0 < m)
    (u : Fin m → E d) (x : Fin a → E d) (y : Fin b → E d)
    (hu : LinearIndependent ℝ u) (hux : LinearIndependent ℝ (Fin.append u x))
    (huy : LinearIndependent ℝ (Fin.append u y))
    (huxy : LinearIndependent ℝ (Fin.append (Fin.append u x) y))
    (W₁ W₂ : Submodule ℤ (E d))
    (hW₁ : W₁ = Submodule.span ℤ (Set.range (Fin.append u x)))
    (hW₂ : W₂ = Submodule.span ℤ (Set.range (Fin.append u y)))
    (hI : W₁ ⊓ W₂ = Submodule.span ℤ (Set.range u))
    (hS : W₁ ⊔ W₂ = Submodule.span ℤ (Set.range (Fin.append (Fin.append u x) y))) :
    Real.log (latticeCovol W₁) + Real.log (latticeCovol W₂) ≥
      Real.log (latticeCovol (W₁ ⊓ W₂)) + Real.log (latticeCovol (W₁ ⊔ W₂)) := by
  rw [hI, hS, hW₁, hW₂]
  rw [latticeCovol_span (hr := (by omega : 0 < m + a)) (v := Fin.append u x) hux]
  rw [latticeCovol_span (hr := (by omega : 0 < m + b)) (v := Fin.append u y) huy]
  rw [latticeCovol_span hm u hu]
  rw [latticeCovol_span (hr := (by omega : 0 < m + a + b))
    (v := Fin.append (Fin.append u x) y) huxy]
  have hcv1 := Submission.SubLatticeCovol.covol_saturated_wedge (d := d)
    (hr := (by omega : 0 < m + a)) (u := Fin.append u x) hux
  have hcv2 := Submission.SubLatticeCovol.covol_saturated_wedge (d := d)
    (hr := (by omega : 0 < m + b)) (u := Fin.append u y) huy
  have hcv3 := Submission.SubLatticeCovol.covol_saturated_wedge (d := d) hm u hu
  have hcv4 := Submission.SubLatticeCovol.covol_saturated_wedge (d := d)
    (hr := (by omega : 0 < m + a + b)) (u := Fin.append (Fin.append u x) y) huxy
  -- rewrite each wedge norm to its covolume (`covolFamily`-shaped) term, matching the engine
  rw [← hcv1, ← hcv2, ← hcv3, ← hcv4]
  exact Submission.CovolPluecker.covolPluecker_aligned_log (d := d) hm u x y hu hux huy huxy

end Submission.GraysonData
