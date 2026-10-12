import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB4.Ann_ann_comm
import Submission.Work.BoseB4.Ann_cre_ccr
import Submission.Work.BoseB4.DGamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.totNumOp_comp_annOf` — the number operator shifts the mode annihilation

The total number operator `totNumOp m = Σ_i a_i†a_i` (`Work.BoseB4.DGamma`) is the
second quantisation of the identity, and the annihilation `annOf m v = Σ_l v_l a_l`
of a superposition is the second quantisation of the one-particle annihilation
`|v⟩` (`Work.BoseB4.ModeFock`).  On the bosonic Fock space one has

  `[N, a(v)] = -a(v)`,

i.e. `N a(v) = a(v) N - a(v)`: annihilating one particle lowers the particle number
by one, so `N` and `a(v)` commute only up to `-a(v)`.  This is the
number-operator row used in the Bogolubov layer of FS §8 (the `n₊`/`a₀` bookkeeping
of `Work.BoseB4.K2ndDefs`), and the `ann` counterpart of the creation identity
`Work.BoseB4.totNumOp_comp_creOf` (`N a†(v) = a†(v) N + a†(v)`).

The proof is the finite-mode commutator, done pointwise on `RealFock m` so that no
statement has to be rearranged at the level of `Module.End`:

* `totNumOpAnnOf_ann_cre_apply` — the CCR `a_l a_i† = a_i† a_l + δ_{li}` (`Ann_cre_ccr`)
  evaluated at a state;
* `totNumOpAnnOf_modeNumOp_apply_ann` — the one-mode commutator `[n_i, a_l] = -δ_{il} a_i`,
  obtained from the CCR and from `[a_i, a_l] = 0` (`Ann_ann_comm`) alone;
* `totNumOpAnnOf_totNumOp_apply_ann` — the same summed over the modes `i`, where
  `Σ_i (if i = l then 1 else 0) • a_i x = a_l x` collapses the Kronecker symbol;
* the weighted sum over `l` with weights `v`.

The helper statements are public (they are the `ann`-half of the mode algebra and are
reusable), but their names are prefixed so that they cannot clash with the symmetric
`cre` development.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB4

set_option autoImplicit false

/-- The one-mode canonical commutation relation `a_l a_i† = a_i† a_l + δ_{li}`
(`Work.BoseB4.Ann_cre_ccr`), evaluated at a state: the operator identity is first
applied through `DFunLike.congr_fun`, after which the goal is an identity in the
Fock space itself. -/
lemma totNumOpAnnOf_ann_cre_apply (m : ℕ) (l i : Fin m) (y : RealFock m) :
    ann m l (cre m i y) = cre m i (ann m l y) + (if l = i then (1:ℝ) else 0) • y := by
  have h := DFunLike.congr_fun (Ann_cre_ccr (m := m) l i) y
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h
  rw [h]

/-- The one-mode commutator of the number operator with an annihilation,
`[n_i, a_l] = n_i a_l - a_l n_i = -δ_{il} a_i`, evaluated at a state.
Indeed `n_i a_l = a_i† (a_i a_l) = a_i† (a_l a_i) = (a_i† a_l) a_i`, and the CCR gives
`a_i† a_l = a_l a_i† - δ_{li}`; so `n_i a_l = a_l n_i - δ_{il} a_i`. -/
lemma totNumOpAnnOf_modeNumOp_apply_ann (m : ℕ) (i l : Fin m) (x : RealFock m) :
    modeNumOp m i (ann m l x)
      = ann m l (modeNumOp m i x) - (if i = l then (1:ℝ) else 0) • ann m i x := by
  have hann : ann m i (ann m l x) = ann m l (ann m i x) :=
    DFunLike.congr_fun (Ann_ann_comm (m := m) i l) x
  have hccr := totNumOpAnnOf_ann_cre_apply m l i (ann m i x)
  have key : cre m i (ann m l (ann m i x))
      = ann m l (cre m i (ann m i x)) - (if l = i then (1:ℝ) else 0) • (ann m i x) :=
    (eq_sub_iff_add_eq).mpr hccr.symm
  simp only [modeNumOp, LinearMap.comp_apply]
  rw [hann, key, if_congr eq_comm rfl rfl]

/-- The summed one-mode commutator: `[N, a_l] = -a_l`, i.e.
`totNumOp m (ann m l x) = ann m l (totNumOp m x) - ann m l x`.
The Kronecker symbol is absorbed by `Σ_i (if i = l then 1 else 0) • a_i x = a_l x`. -/
lemma totNumOpAnnOf_totNumOp_apply_ann (m : ℕ) (l : Fin m) (x : RealFock m) :
    totNumOp m (ann m l x) = ann m l (totNumOp m x) - ann m l x := by
  have hdelta : (∑ i : Fin m, (if i = l then (1:ℝ) else 0) • ann m i x) = ann m l x := by
    have hterm : ∀ i : Fin m,
        (if i = l then (1:ℝ) else 0) • ann m i x = if i = l then ann m i x else 0 := by
      intro i; by_cases h : i = l <;> simp [h]
    simp only [hterm, Finset.sum_ite_eq']
    simp
  calc totNumOp m (ann m l x)
      = ∑ i : Fin m, modeNumOp m i (ann m l x) := by
            rw [totNumOp, LinearMap.sum_apply]
    _ = ∑ i : Fin m, (ann m l (modeNumOp m i x)
            - (if i = l then (1:ℝ) else 0) • ann m i x) :=
            Finset.sum_congr rfl fun i _ => totNumOpAnnOf_modeNumOp_apply_ann m i l x
    _ = (∑ i : Fin m, ann m l (modeNumOp m i x))
          - ∑ i : Fin m, (if i = l then (1:ℝ) else 0) • ann m i x := by
            rw [Finset.sum_sub_distrib]
    _ = ann m l (∑ i : Fin m, modeNumOp m i x) - ann m l x := by
            rw [hdelta, ← map_sum]
    _ = ann m l ((∑ i : Fin m, modeNumOp m i) x) - ann m l x := by
            rw [← LinearMap.sum_apply]
    _ = ann m l (totNumOp m x) - ann m l x := by rw [totNumOp]

theorem totNumOp_comp_annOf (m : ℕ) (v : Fin m → ℝ) :
    (Work.BoseB4.totNumOp m).comp (Work.BoseB4.annOf m v)
      = (Work.BoseB4.annOf m v).comp (Work.BoseB4.totNumOp m) - Work.BoseB4.annOf m v := by
  have hannOf : ∀ y : RealFock m, annOf m v y = ∑ l : Fin m, v l • ann m l y := by
    intro y
    simp [annOf, LinearMap.sum_apply, LinearMap.smul_apply]
  apply LinearMap.ext
  intro x
  calc ((totNumOp m).comp (annOf m v)) x
      = totNumOp m (annOf m v x) := rfl
    _ = totNumOp m (∑ l : Fin m, v l • ann m l x) := by rw [hannOf x]
    _ = ∑ l : Fin m, v l • totNumOp m (ann m l x) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun l _ => by rw [map_smul]
    _ = ∑ l : Fin m, v l • (ann m l (totNumOp m x) - ann m l x) :=
          Finset.sum_congr rfl fun l _ => by rw [totNumOpAnnOf_totNumOp_apply_ann]
    _ = (∑ l : Fin m, v l • ann m l (totNumOp m x)) - ∑ l : Fin m, v l • ann m l x := by
          have hs : (∑ l : Fin m, v l • (ann m l (totNumOp m x) - ann m l x))
              = ∑ l : Fin m, (v l • ann m l (totNumOp m x) - v l • ann m l x) :=
            Finset.sum_congr rfl fun l _ => smul_sub (v l) _ _
          rw [hs, Finset.sum_sub_distrib]
    _ = annOf m v (totNumOp m x) - annOf m v x := by
          rw [← hannOf (totNumOp m x), ← hannOf x]
    _ = ((annOf m v).comp (totNumOp m) - annOf m v) x := rfl

end Work.BoseB4
