/-
  WilC4/ClusterSelf/Tool : copy of `WilC4/ClusterTool` under the namespace `Work.WilC4.CESAux`.

  See `Submission/Work/WilC4/ClusterER_definable_self.lean` for why the `ClusterDefs` family
  (`ClusterTool`/`ClusterSets`/`ClusterCoord`) is reproduced verbatim under a fresh namespace:
  the public names declared by `ClusterCoord` clash with those of `WilC4/monoDefinable_W`, so no
  module may import both families, while `WilC4/ulpm_E_finite` needs the definability of
  `ClusterER` *and* the `mono_real` machinery.
-/
import Mathlib
import Submission.Work.WilC2.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Work.WilC4.CESAux

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language

open WilkiesDesign WilkiesDesign.CG
open Work.WilC2 (ringToLRc leF leF_realize leF_realize_le liftR liftR_realize)

/-! ## 1. Ring terms are `LRc`-definable functions -/

/-- Every ring term, realised on `ℝ`, is an `LRc`-definable function of the tuple. -/
theorem defFun_ringTerm {ρ : Type} (t : Language.ring.Term ρ) :
    (∅ : Set ℝ).DefinableFun LRc (fun u : ρ → ℝ => t.realize u) := by
  have h := Term.definableFun_realize (L := LRc) (M := ℝ) (α := ρ) (ringToLRc.onTerm t)
  convert h using 1
  ext u
  exact (LHom.realize_onTerm ringToLRc t u).symm

/-- Coordinate arithmetic is `∅`-definable. -/
theorem defFun_mul {ρ : Type} (i j : ρ) :
    (∅ : Set ℝ).DefinableFun LRc (fun u : ρ → ℝ => u i * u j) := by
  have h := defFun_ringTerm ((Term.var i) * (Term.var j) : Language.ring.Term ρ)
  simpa using h

theorem defFun_add {ρ : Type} (i j : ρ) :
    (∅ : Set ℝ).DefinableFun LRc (fun u : ρ → ℝ => u i + u j) := by
  have h := defFun_ringTerm ((Term.var i) + (Term.var j) : Language.ring.Term ρ)
  simpa using h

theorem defFun_neg {ρ : Type} (i : ρ) :
    (∅ : Set ℝ).DefinableFun LRc (fun u : ρ → ℝ => -u i) := by
  have h := defFun_ringTerm (-(Term.var i) : Language.ring.Term ρ)
  simpa using h

theorem defFun_sub {ρ : Type} (i j : ρ) :
    (∅ : Set ℝ).DefinableFun LRc (fun u : ρ → ℝ => u i - u j) := by
  have h := defFun_ringTerm ((Term.var i) + (-(Term.var j)) : Language.ring.Term ρ)
  simpa [sub_eq_add_neg] using h

/-- A constant function with an arbitrary real value is `∅`-definable (`LRc` names every real). -/
theorem defFun_const {ρ : Type} (c : ℝ) :
    (∅ : Set ℝ).DefinableFun LRc (fun _ : ρ → ℝ => c) := by
  have h := Term.definableFun_realize (L := LRc) (M := ℝ) (α := ρ) (LR.con c).term
  convert h using 1
  ext u
  rw [Term.realize_constants]
  rfl

/-! ## 2. The order and the comparison sets -/

theorem exists_sq_of_nonneg (x : ℝ) (hx : 0 ≤ x) : ∃ z : ℝ, x = z * z :=
  ⟨Real.sqrt x, by rw [← pow_two]; exact (Real.sq_sqrt hx).symm⟩

/-- `{z : Fin 2 → ℝ | z 0 ≤ z 1}`, the order of `ℝ` read in the ring language. -/
def LE2 : Set (Fin 2 → ℝ) := {z | z 0 ≤ z 1}

theorem LE2_definable : (∅ : Set ℝ).Definable LRc LE2 := by
  rw [Set.empty_definable_iff]
  refine ⟨liftR ![(0 : Fin 2), 1] leF, ?_⟩
  ext z
  show z 0 ≤ z 1 ↔ (liftR ![(0 : Fin 2), 1] leF).Realize z
  rw [liftR_realize]
  have h : z ∘ ![(0 : Fin 2), 1] = ![z 0, z 1] := by funext i; fin_cases i <;> rfl
  rw [h, leF_realize_le exists_sq_of_nonneg]

/-- `{u | f u ≤ g u}` is definable when `f` and `g` are. -/
theorem definable_le_fun {ρ : Type} {f g : (ρ → ℝ) → ℝ}
    (hf : (∅ : Set ℝ).DefinableFun LRc f) (hg : (∅ : Set ℝ).DefinableFun LRc g) :
    (∅ : Set ℝ).Definable LRc {u : ρ → ℝ | f u ≤ g u} := by
  have hmap : (∅ : Set ℝ).DefinableMap LRc
      (fun u : ρ → ℝ => fun i : Fin 2 => ![f u, g u] i) := by
    intro i
    fin_cases i
    · simpa using hf
    · simpa using hg
  have h := LE2_definable.preimage_map hmap
  convert h using 1
  ext u
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, LE2, Set.mem_setOf_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one]

/-- `{u | f u < g u}` is definable when `f` and `g` are. -/
theorem definable_lt_fun {ρ : Type} {f g : (ρ → ℝ) → ℝ}
    (hf : (∅ : Set ℝ).DefinableFun LRc f) (hg : (∅ : Set ℝ).DefinableFun LRc g) :
    (∅ : Set ℝ).Definable LRc {u : ρ → ℝ | f u < g u} := by
  have h := (definable_le_fun hf hg).inter ((hf.ofPred_eq hg).compl)
  convert h using 1
  ext u
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_setOf_eq]
  exact ⟨fun h => ⟨le_of_lt h, ne_of_lt h⟩, fun h => lt_of_le_of_ne h.1 h.2⟩

/-- `{u | f u = g u}` is definable when `f` and `g` are. -/
theorem definable_eq_fun {ρ : Type} {f g : (ρ → ℝ) → ℝ}
    (hf : (∅ : Set ℝ).DefinableFun LRc f) (hg : (∅ : Set ℝ).DefinableFun LRc g) :
    (∅ : Set ℝ).Definable LRc {u : ρ → ℝ | f u = g u} :=
  hf.ofPred_eq hg

/-- `{u | f u ≠ g u}` is definable when `f` and `g` are. -/
theorem definable_ne_fun {ρ : Type} {f g : (ρ → ℝ) → ℝ}
    (hf : (∅ : Set ℝ).DefinableFun LRc f) (hg : (∅ : Set ℝ).DefinableFun LRc g) :
    (∅ : Set ℝ).Definable LRc {u : ρ → ℝ | f u ≠ g u} :=
  (hf.ofPred_eq hg).compl


end Work.WilC4.CESAux
