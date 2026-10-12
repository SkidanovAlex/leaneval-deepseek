import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Finsupp.Weight
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseB4.AntiNormal
import Submission.Work.BoseB4.DGamma_diag
import Submission.Work.BoseB4.DGamma_one
import Submission.Work.BoseB4.DGamma_quadform
import Submission.Work.BoseB4.Kafz_lower_bound_H2nd
import Submission.Work.BoseB4.Kafz_lower_bound_pointwise
import Submission.Work.BoseB4.TildeDataInst
import Submission.Work.BoseB4.a0_comp_a0d_sq
import Submission.Work.BoseB4.annC_creC_ccr
import Submission.Work.BoseB4.dGamma_diag_nonneg
import Submission.Work.BoseB4.monoOp_11_00_numOp
import Submission.Work.BoseB4.monoOp_lift_basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDict.dGamma_degree` — second quantisation preserves the degree

`Work.BoseB4.dGamma m T` is the second quantisation `∑_{ij} (T e_j)_i a_i† a_j` of a
one-particle operator `T` on the mode space `Fin m → ℝ`, acting on the real bosonic
Fock space `RealFock m = (Fin m → ₀ ℕ) →₀ ℝ` (`Work.BoseB4.DGamma`).  The lemma proved
here says that it **preserves the particle number**: if every basis vector in the
support of `Ψ` has total occupation `∑_k α_k = d`, then so does every basis vector in
the support of `dGamma m T Ψ`.

This is the degree hypothesis `hΨ` used all over the box ↔ model dictionary of node B4:
`boxRealise e d` realises the degree-`d` component of the model on the box's `d`-particle
space, and the dictionary identities (`boxRealise_ann`, `boxRealise_cre`, `boxRealise_cIPn`,
`boxRealise_dGamma`, …) only make sense when both sides are carried by the same degree.
Since `dGamma T` moves one particle from the mode `j` to the mode `i`, the degree is
unchanged — that is the content of the computation below.

## Proof

The degree-`d` vectors form the submodule `degSub m d = {Φ | ∀ α ∈ Φ.support, ∑_k α_k = d}`
over `ℝ` (closed under addition because over a domain `Φ γ + Ψ γ = 0` with both terms
non-zero forces ... nothing, but a *non-zero* sum does force one of the two terms to be
non-zero; that is the only direction needed).  Two steps:

* On a basis monomial, `dGamma m T (single α 1) = ∑_{ij} (T e_j)_i · (α j) • single (α - e_j + e_i) 1`
  by `Work.BoseB4.ann_single_basis` and `Work.BoseB4.cre_single`, and the shifted index
  `α - e_j + e_i` has the same total degree as `α` whenever `α j ≠ 0`
  (`deg_tsub_e_add_e`, from `tsub_add_cancel_of_le`); if `α j = 0` the whole term is `0`.
* A general `Ψ` is the finite sum `∑_{α ∈ Ψ.support} Ψ α • single α 1` (`Finsupp.sum_single`),
  and `dGamma m T` is linear, so the general case follows from closure of `degSub` under
  finite sums and scalar multiples.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseDict

set_option autoImplicit false

open Work.BoseB4

/-- **The degree-`d` part of the Fock space**: the vectors all of whose basis vectors
(multi-indices) have total occupation `∑_k α_k = d`.  This is a submodule of
`RealFock m`, closed under sums and scalar multiples. -/
private def degSub (m d : ℕ) : Submodule ℝ (RealFock m) where
  carrier := {Φ | ∀ α ∈ Φ.support, α.sum (fun _ k => k) = d}
  zero_mem' := by
    intro α hα
    simp at hα
  add_mem' := by
    intro f g hf hg γ hγ
    have h : f γ + g γ ≠ 0 := by
      rw [← Finsupp.add_apply]
      exact Finsupp.mem_support_iff.mp hγ
    rcases eq_or_ne (f γ) 0 with h0 | h0
    · exact hg γ (Finsupp.mem_support_iff.mpr (by rwa [h0, zero_add] at h))
    · exact hf γ (Finsupp.mem_support_iff.mpr h0)
  smul_mem' := by
    intro c f hf γ hγ
    have h : (c • f) γ ≠ 0 := Finsupp.mem_support_iff.mp hγ
    rw [Finsupp.smul_apply] at h
    exact hf γ (Finsupp.mem_support_iff.mpr (fun h0 => h (by rw [h0, smul_zero])))

/-- Raising the occupation of one mode by one raises the total degree by one. -/
private lemma deg_add_e {m : ℕ} (β : Fin m →₀ ℕ) (l : Fin m) :
    (β + e m l).sum (fun _ k => k) = β.sum (fun _ k => k) + 1 := by
  rw [show (β + e m l).sum (fun _ k => k) = (β + e m l).degree from rfl,
      show β.sum (fun _ k => k) = β.degree from rfl,
      map_add, show (e m l).degree = 1 from by rw [e, Finsupp.degree_single]]

/-- **The degree is invariant under `α ↦ α - e_j + e_i`** when the `j`-occupation of `α`
is non-zero (the shift of one particle from the mode `j` to the mode `i`): the
`− e_j` lowers the degree by one (the truncation does not bite, `α j ≠ 0`), the
`+ e_i` raises it back. -/
private lemma deg_tsub_e_add_e {m : ℕ} (α : Fin m →₀ ℕ) (i j : Fin m) (hj : α j ≠ 0) :
    ((α - e m j) + e m i).sum (fun _ k => k) = α.sum (fun _ k => k) := by
  have hα : (α - e m j) + e m j = α :=
    tsub_add_cancel_of_le ((Finsupp.single_le_iff).mpr (Nat.pos_of_ne_zero hj))
  have h1 := deg_add_e (α - e m j) i
  have h2 : α.sum (fun _ k => k) = (α - e m j).sum (fun _ k => k) + 1 := by
    conv_lhs => rw [← hα]
    exact deg_add_e (α - e m j) j
  rw [h1, h2]

/-- The basis monomial `single β 1` lies in `degSub m d` when `β` has degree `d`
(its support is contained in `{β}`). -/
private lemma single_mem_degSub {m d : ℕ} (β : Fin m →₀ ℕ)
    (hβ : β.sum (fun _ k => k) = d) :
    (Finsupp.single β (1 : ℝ) : RealFock m) ∈ degSub m d := by
  intro γ hγ
  have h : (Finsupp.single β (1 : ℝ) : RealFock m) γ ≠ 0 := Finsupp.mem_support_iff.mp hγ
  have hγβ : γ = β := by
    by_contra hne
    exact h (Finsupp.single_eq_of_ne hne)
  rw [hγβ, hβ]

/-- **`dGamma` on a basis monomial stays in degree `d`.**  Expanding the definition,
`dGamma m T (single α 1) = ∑_{ij} (T e_j)_i • (α j) • single (α - e_j + e_i) 1`: each
term is a scalar multiple of a monomial of degree `d` (or is `0`, when `α j = 0`). -/
private lemma dGamma_single_mem {m d : ℕ} (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (α : Fin m →₀ ℕ) (hα : α.sum (fun _ k => k) = d) :
    dGamma m T (Finsupp.single α (1 : ℝ)) ∈ degSub m d := by
  have hexp : dGamma m T (Finsupp.single α (1 : ℝ))
      = ∑ i : Fin m, ∑ j : Fin m,
          (T (evec m j) i) • (cre m i (ann m j (Finsupp.single α (1 : ℝ)))) := by
    rw [dGamma]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [hexp]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  rw [ann_single_basis, map_smul, cre_single]
  by_cases hj : α j = 0
  · rw [hj]
    simp
  · refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (single_mem_degSub _ ?_))
    rw [deg_tsub_e_add_e α i j hj, hα]

theorem dGamma_degree {m : ℕ} (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Ψ : Work.BoseB4.RealFock m)
    (d : ℕ) (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d) :
    ∀ α ∈ (Work.BoseB4.dGamma m T Ψ).support, α.sum (fun _ k => k) = d := by
  -- `Ψ` is the finite sum of its basis monomials, all of degree `d`
  have hexp : Ψ = Ψ.support.sum (fun α => Ψ α • (Finsupp.single α (1 : ℝ) : RealFock m)) := by
    conv_lhs => rw [← Finsupp.sum_single (f := Ψ)]
    rw [Finsupp.sum]
    exact Finset.sum_congr rfl (fun α _ => by rw [Finsupp.smul_single, smul_eq_mul, mul_one])
  -- hence `dGamma m T Ψ` is a finite sum of `degSub`-elements by linearity of `dGamma`
  have hlin : dGamma m T Ψ
      = Ψ.support.sum (fun α => Ψ α • dGamma m T (Finsupp.single α (1 : ℝ))) := by
    conv_lhs => rw [hexp]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun α _ => by rw [map_smul])
  have hmem : dGamma m T Ψ ∈ degSub m d := by
    rw [hlin]
    exact Submodule.sum_mem _
      (fun α hα => Submodule.smul_mem _ _ (dGamma_single_mem T α (hΨ α hα)))
  exact fun α hα => hmem α hα

end Work.BoseDict
