import Mathlib
import Submission.Work.RatHurewicz.excisionDefs
import Submission.Work.RatHurewicz.Triad.Basic
import Submission.Work.RatHurewicz.Triad.Helpers
import Submission.Work.RatHurewicz.homotopyFibreMap_exists

/-!
# The dictionary between maps into the homotopy fibre of `C ↪ X` and maps of the triad

For a triad `(X; B, C)` with base point `x₀ ∈ B ∩ C` put
`F = homotopyFibre (setIncl C) x₀` — the space of pairs `(c, γ)` with `c ∈ C` and `γ` a path in
`X` from `x₀` to `c`.  A map `f : Iⁿ → F` corresponds, by adjunction, to a map
`Φ : Iⁿ × I → X` which starts at `x₀` (`Φ x 0 = x₀`) and ends in `C` (`Φ x 1 ∈ C`).  A map into
the subspace `Set.range (excisionComparison B C x₀)` corresponds to a map whose paths lie in `B`
and end in `B ∩ C`.

This file records that dictionary.  The type `F` is written `Ffibre X C x₀` so that the
topology instance is found by unification.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Triad

noncomputable section

open Work.Stems.Cubical

variable {X : Type} [TopologicalSpace X]

/-- The homotopy fibre of `C ↪ X` over the base point, written with `x₀ : X` explicit so that the
type class instance for the topology is found by unification. -/
abbrev Ffibre (X : Type) [TopologicalSpace X] (C : Set X) (x : X) : Type :=
  Work.StemsB.bundlePullback X x ↥C (setIncl C)

/-- The path of an element of `F`. -/
def Fpath {C : Set X} {x : X} (p : Ffibre X C x) : C(I, X) := p.1.2.1

@[simp] theorem Fpath_apply {C : Set X} {x : X} (p : Ffibre X C x) (t : I) :
    Fpath p t = p.1.2.1 t := rfl

theorem Fpath_zero {C : Set X} {x : X} (p : Ffibre X C x) : Fpath p 0 = x := p.1.2.2

theorem Fpath_one {C : Set X} {x : X} (p : Ffibre X C x) : Fpath p 1 = (p.1.1 : X) := p.2

theorem Fendpoint_mem {C : Set X} {x : X} (p : Ffibre X C x) : (p.1.1 : X) ∈ C := p.1.1.2

/-- The projection `F → C(I, X)`, as a continuous map. -/
def FpathCMap (X : Type) [TopologicalSpace X] (C : Set X) (x : X) :
    C(Ffibre X C x, C(I, X)) where
  toFun p := Fpath p
  continuous_toFun :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)

/-- The map into `C(I, X)` underlying a continuous map into `F`. -/
def FpathCM {C : Set X} {x : X} {n : ℕ} (f : C(ICube n, Ffibre X C x)) :
    C(ICube n, C(I, X)) := (FpathCMap X C x).comp f

@[simp] theorem FpathCM_apply {C : Set X} {x : X} {n : ℕ} (f : C(ICube n, Ffibre X C x))
    (u : ICube n) : FpathCM f u = Fpath (f u) := rfl

/-- The reindexing `I^{n+1} → Iⁿ × I` (last coordinate as the second factor). -/
def splitCM (n : ℕ) : C(ICube (n + 1), ICube n × I) where
  toFun z := (initC n z, z (Fin.last n))
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · refine continuous_pi fun i => ?_
      exact continuous_apply i.castSucc
    · exact continuous_apply (Fin.last n)

@[simp] theorem splitCM_apply (n : ℕ) (z : ICube (n + 1)) :
    splitCM n z = (initC n z, z (Fin.last n)) := rfl

theorem splitCM_snoc (n : ℕ) (u : ICube n) (t : I) :
    splitCM n (Fin.snoc u t) = (u, t) := by
  simp [splitCM]

/-- **The uncurried form of a map into `F`**: a map `I^{n+1} → X`, the last coordinate being the
parameter of the path. -/
def uncurryF {C : Set X} {x : X} {n : ℕ} (f : C(ICube n, Ffibre X C x)) :
    C(ICube (n + 1), X) := (FpathCM f).uncurry.comp (splitCM n)

@[simp] theorem uncurryF_apply {C : Set X} {x : X} {n : ℕ} (f : C(ICube n, Ffibre X C x))
    (z : ICube (n + 1)) : uncurryF f z = Fpath (f (initC n z)) (z (Fin.last n)) := rfl

@[simp] theorem uncurryF_snoc {C : Set X} {x : X} {n : ℕ} (f : C(ICube n, Ffibre X C x))
    (u : ICube n) (t : I) :
    uncurryF f (Fin.snoc u t) = Fpath (f u) t := by
  simp [uncurryF]

variable {B C : Set X} {x₀ : ↥(B ∩ C)}

/-- The homotopy fibre of `B ∩ C ↪ B` over the base point: the source of the excision comparison
map. -/
abbrev Fbase (B C : Set X) (x₀ : ↥(B ∩ C)) : Type :=
  Work.StemsB.bundlePullback ↥B ⟨x₀.1, x₀.2.1⟩ ↥(B ∩ C) (interInclLeft B C)

/-- The path of `excisionComparison`: it is the composition of the path in `B` with the inclusion
of `B` in `X`. -/
theorem Fpath_excisionComparison (p : Fbase B C x₀) :
    Fpath (excisionComparison B C x₀ p) = (setIncl B).comp p.1.2.1 :=
  homotopyFibreMap_snd (interInclLeft B C) (setIncl C) (setIncl B) (interInclRight B C)
    (excision_square B C) x₀ p

/-- **The "wall" of an uncurried map whose boundary values lie in the image of the comparison
map lies in `B`.** -/
theorem uncurryF_mem_B {n : ℕ} (f : C(ICube n, Ffibre X C (x₀ : X)))
    (hf : ∀ u, u ∈ Cube.boundary (Fin n) → f u ∈ Set.range (excisionComparison B C x₀))
    (u : ICube n) (hu : u ∈ Cube.boundary (Fin n)) (t : I) :
    uncurryF f (Fin.snoc u t) ∈ B := by
  obtain ⟨p, hp⟩ := hf u hu
  rw [uncurryF_snoc, ← hp]
  change ((setIncl B).comp p.1.2.1) t ∈ B
  exact (p.1.2.1 t).2

theorem uncurryF_mem_B_inter_C {n : ℕ} (f : C(ICube n, Ffibre X C (x₀ : X)))
    (hf : ∀ u, u ∈ Cube.boundary (Fin n) → f u ∈ Set.range (excisionComparison B C x₀))
    (u : ICube n) (hu : u ∈ Cube.boundary (Fin n)) :
    uncurryF f (Fin.snoc u 1) ∈ B ∩ C :=
  ⟨uncurryF_mem_B f hf u hu 1, by
    rw [uncurryF_snoc, Fpath_one]
    exact Fendpoint_mem (f u)⟩

/-- **A map into `F` whose boundary values lie in the image of the comparison map uncurries to an
admissible map of the triad.** -/
theorem triadAdmissible_uncurryF {n : ℕ} (f : C(ICube n, Ffibre X C (x₀ : X)))
    (hf : ∀ u, u ∈ Cube.boundary (Fin n) → f u ∈ Set.range (excisionComparison B C x₀)) :
    TriadAdmissible B C x₀ (uncurryF f) :=
  ⟨fun u => by rw [uncurryF_snoc, Fpath_zero],
   fun u => by rw [uncurryF_snoc, Fpath_one]; exact Fendpoint_mem (f u),
   fun u hu t => uncurryF_mem_B f hf u hu t⟩

end

end Work.RatHurewicz.Triad
