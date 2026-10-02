import Mathlib
import Submission.Work.StemsB.Fibrations

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `π₁`-torsor structure of the path space (the algebra half of
`Work.Serre.pathSpaceAaction`)

For a based topological space `(X, pt)` the space `E = PathSpace X pt` of paths starting at `pt`
carries the path–loop fibration `evalOne : E → X`, and the homotopy classes (relative to the
endpoints) of paths from `pt` to a fixed `x : X` form a *torsor* under the fundamental group
`π₁(X, pt)`: concatenating a loop on the left is free and transitive.

This file contains the path-algebraic part of that statement, phrased entirely in Mathlib's
`Path` / `Path.Homotopic.Quotient` vocabulary:

* `psToPath` — the path underlying a point of the path space;
* `psConcatMap` — the continuous map `e ↦ ℓ * e` given by left concatenation with a fixed loop
  `ℓ : Path pt pt`, together with `psEvalOne_psConcatMap` (`evalOne` is preserved) and
  `psActPath` (`psConcatMap ℓ e` as a `Path pt (evalOne e)`);
* `ps_exists_homotopy_iff_homotopic` — the translation between an explicit homotopy
  `H : I × I → X` from `p` to `q` relative to the endpoints and Mathlib's `Path.Homotopic`;
* `ps_eq_of_trans_homotopic` — right cancellation (`u * p ≈ v * p ⟹ u ≈ v`);
* `ps_homotopic_of_trans_eq` — existence of `u` with `u * p ≈ q` given `[u] = [q] [p]⁻¹`.
-/

open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

open Work.StemsB

variable {X : Type} [TopologicalSpace X] (pt : X)

/-- The path underlying a point of the path space (a continuous map `I → X` starting at `pt`),
regarded as a `Path` from `pt` to its endpoint. -/
def psToPath (e : PathSpace X pt) : Path pt ((evalOne X pt) e) := ⟨e.1, e.2, rfl⟩

@[simp] lemma psToPath_apply (e : PathSpace X pt) (t : unitInterval) : psToPath pt e t = e.1 t :=
  rfl

/-- Left concatenation with a fixed loop `ℓ : Path pt pt`, as a continuous self-map of the path
space.  This is the concrete model of the action of `π₁(X, pt)` on the path space. -/
def psConcatMap (ℓ : Path pt pt) : C(PathSpace X pt, PathSpace X pt) where
  toFun e := ⟨(ℓ.trans (psToPath pt e)).toContinuousMap, (ℓ.trans (psToPath pt e)).source'⟩
  continuous_toFun :=
   Continuous.subtype_mk (f := fun e => (ℓ.trans (psToPath pt e)).toContinuousMap)
    (by
      apply ContinuousMap.continuous_of_continuous_uncurry
      rw [show (Function.uncurry fun x y => ((fun e : PathSpace X pt =>
            (ℓ.trans (psToPath pt e)).toContinuousMap) x) y) =
          (fun w : PathSpace X pt × unitInterval =>
            if (w.2 : ℝ) ≤ 1/2 then ℓ.extend (2 * (w.2 : ℝ))
            else (psToPath pt w.1).extend (2 * (w.2 : ℝ) - 1)) from rfl]
      have hf' : Continuous (fun w : PathSpace X pt × unitInterval => ℓ.extend (2 * (w.2 : ℝ))) :=
        ℓ.continuous_extend.comp (by fun_prop)
      refine Continuous.if_le hf' ?_ (by fun_prop) (by fun_prop) ?_
      · exact continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk
          ((continuous_projIcc (h := zero_le_one)).comp (by fun_prop)))
      · intro w hw
        have h2 : (2:ℝ) * (w.2 : ℝ) = 1 := by rw [hw]; norm_num
        rw [h2, show (1:ℝ) - 1 = 0 by norm_num, Path.extend_one, Path.extend_zero])
    (fun e => (ℓ.trans (psToPath pt e)).source')

@[simp] lemma psConcatMap_coe (ℓ : Path pt pt) (e : PathSpace X pt) :
    (psConcatMap pt ℓ e).1 = (ℓ.trans (psToPath pt e)).toContinuousMap :=
  rfl

/-- `psConcatMap ℓ e` as a path from `pt` to `evalOne e`. -/
def psActPath (ℓ : Path pt pt) (e : PathSpace X pt) : Path pt ((evalOne X pt) e) where
  toContinuousMap := (psConcatMap pt ℓ e).1
  source' := (psConcatMap pt ℓ e).2
  target' := (ℓ.trans (psToPath pt e)).target

lemma psActPath_eq_trans (ℓ : Path pt pt) (e : PathSpace X pt) :
    psActPath pt ℓ e = ℓ.trans (psToPath pt e) := Path.ext rfl

/-- Left concatenation with a loop does not change the endpoint of a path: `psConcatMap ℓ` is a
map of the path–loop fibration to itself. -/
lemma psEvalOne_psConcatMap (ℓ : Path pt pt) :
    (evalOne X pt).comp (psConcatMap pt ℓ) = evalOne X pt := by
  ext e
  exact (ℓ.trans (psToPath pt e)).target

/-- The class of `psActPath ℓ e` in the fundamental groupoid is the product of the class of `ℓ`
with the class of `e` (left concatenation acts by multiplication on the left). -/
lemma psMk_psActPath (ℓ : Path pt pt) (e : PathSpace X pt) :
    Path.Homotopic.Quotient.mk (psActPath pt ℓ e)
      = (Path.Homotopic.Quotient.mk ℓ).trans (Path.Homotopic.Quotient.mk (psToPath pt e)) := by
  rw [psActPath_eq_trans, Path.Homotopic.Quotient.mk_trans]

/-- An explicit homotopy `H : I × I → X` with `H (0, ·) = p`, `H (1, ·) = q` and the two boundary
values `pt` and `x` fixed is exactly a path-homotopy relative to the endpoints. -/
lemma ps_exists_homotopy_iff_homotopic {x : X} (p q : Path pt x) :
    (∃ H : C(unitInterval × unitInterval, X),
      (∀ t : unitInterval, H (0, t) = p t) ∧
      (∀ t : unitInterval, H (1, t) = q t) ∧
      (∀ s : unitInterval, H (s, 0) = pt) ∧
      (∀ s : unitInterval, H (s, 1) = x)) ↔ p.Homotopic q := by
  constructor
  · rintro ⟨H, h0, h1, hs0, hs1⟩
    refine ⟨⟨⟨H, ?_, ?_⟩, ?_⟩⟩
    · intro t; exact h0 t
    · intro t; exact h1 t
    · intro t y hy
      rcases hy with hy | hy
      · subst hy; exact (hs0 t).trans (by simp)
      · subst hy; exact (hs1 t).trans (by simp)
  · rintro ⟨H⟩
    exact ⟨H.toContinuousMap, fun t => H.apply_zero t, fun t => H.apply_one t,
      fun s => (H.eq_fst s (by simp)).trans (by simp),
      fun s => (H.eq_fst s (by simp)).trans (by simp)⟩

/-- Right cancellation: if `u * p` and `v * p` are homotopic relative to the endpoints then the
loops `u` and `v` are (freely homotopic, hence) equal in `π₁`. -/
lemma ps_eq_of_trans_homotopic {x : X} (u v : Path pt pt) (p : Path pt x)
    (h : (u.trans p).Homotopic (v.trans p)) :
    Path.Homotopic.Quotient.mk u = Path.Homotopic.Quotient.mk v := by
  have h' : (Path.Homotopic.Quotient.mk u).trans (Path.Homotopic.Quotient.mk p) =
      (Path.Homotopic.Quotient.mk v).trans (Path.Homotopic.Quotient.mk p) := by
    rw [← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.eq.mpr h]
  calc Path.Homotopic.Quotient.mk u
      = (Path.Homotopic.Quotient.mk u).trans (Path.Homotopic.Quotient.refl pt) :=
        (Path.Homotopic.Quotient.trans_refl _).symm
    _ = (Path.Homotopic.Quotient.mk u).trans
          ((Path.Homotopic.Quotient.mk p).trans (Path.Homotopic.Quotient.mk p).symm) := by
        rw [Path.Homotopic.Quotient.trans_symm]
    _ = ((Path.Homotopic.Quotient.mk u).trans (Path.Homotopic.Quotient.mk p)).trans
          (Path.Homotopic.Quotient.mk p).symm :=
        (Path.Homotopic.Quotient.trans_assoc _ _ _).symm
    _ = ((Path.Homotopic.Quotient.mk v).trans (Path.Homotopic.Quotient.mk p)).trans
          (Path.Homotopic.Quotient.mk p).symm := by rw [h']
    _ = (Path.Homotopic.Quotient.mk v).trans
          ((Path.Homotopic.Quotient.mk p).trans (Path.Homotopic.Quotient.mk p).symm) :=
        Path.Homotopic.Quotient.trans_assoc _ _ _
    _ = (Path.Homotopic.Quotient.mk v).trans (Path.Homotopic.Quotient.refl pt) := by
        rw [Path.Homotopic.Quotient.trans_symm]
    _ = Path.Homotopic.Quotient.mk v := Path.Homotopic.Quotient.trans_refl _

/-- Transitivity: if the class of the loop `u` is the class of `q` times the inverse of the class
of `p`, then `u * p` is homotopic to `q` relative to the endpoints. -/
lemma ps_homotopic_of_trans_eq {x : X} (u : Path pt pt) (p q : Path pt x)
    (h : Path.Homotopic.Quotient.mk u =
      (Path.Homotopic.Quotient.mk q).trans (Path.Homotopic.Quotient.mk p).symm) :
    (u.trans p).Homotopic q := by
  refine Path.Homotopic.Quotient.eq.mp ?_
  rw [Path.Homotopic.Quotient.mk_trans, h]
  calc ((Path.Homotopic.Quotient.mk q).trans (Path.Homotopic.Quotient.mk p).symm).trans
        (Path.Homotopic.Quotient.mk p)
      = (Path.Homotopic.Quotient.mk q).trans
          ((Path.Homotopic.Quotient.mk p).symm.trans (Path.Homotopic.Quotient.mk p)) :=
        Path.Homotopic.Quotient.trans_assoc _ _ _
    _ = (Path.Homotopic.Quotient.mk q).trans (Path.Homotopic.Quotient.refl x) := by
        rw [Path.Homotopic.Quotient.symm_trans]
    _ = Path.Homotopic.Quotient.mk q := Path.Homotopic.Quotient.trans_refl _

end

end Work.Serre
