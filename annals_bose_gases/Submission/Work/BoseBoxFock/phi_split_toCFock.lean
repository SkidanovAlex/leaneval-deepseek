import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseBoxFock.KzOpC
import Submission.Work.BoseBoxFock.window_ops
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.phi_split_toCFock` — the coherent-state transform of a window vector
is finitely supported in the excited multi-index

The box ↔ model bridge (`box_to_model`, `model_kafz`, `NodeB7`, …) evaluates FS `thm:Kafz`
on the `⟨condensate | excited⟩` picture of a window vector `Ψ : RealFock m`
(`Work.BoseBoxFock.ExcWindow M n Ψ`), i.e. on the spectator vector

    `v(z) = Phi (split Ψ) z ∈ cfock (Excited m)`,

the coherent-state transform (`Work.BoseB4.Phi`, `Work.BoseB4.split`) of the mode-lattice
state at the complex condensate parameter `z`.  For the later estimates one needs to know
that `v(z)` is a *finite* combination of the occupation basis vectors `|β⟩` of the spectator
Fock core and that only multi-indices `β` with

    `|β| = degree β ≤ ⌊M⌋₊`

occur — this is the coordinate form of `n₊ ≤ M` on the state, and it is exactly what makes
the spectator operator `nPlusC` act diagonally with eigenvalues `≤ ⌊M⌋₊` (comparison
`excWindow_nPlusC_le`).

## Proof

`split` is the `Finsupp.lsum` of the weighted basis vectors `splitInnerB`/`splitVec`
(`Split_ann_excited.split_single_basis`), so expanding a general `Ψ` over its support
(`window_ops.sum_single_support`) and applying the `ℂ`-linear `PhiLin z`
(`Phi_single`) gives

    `Phi (split Ψ) z = Σ_{α ∈ supp Ψ} (Ψ α) · (z̄^{(α 0)}/√((α 0)!)) · splitVec α`
                     `= Σ_{α ∈ supp Ψ} (Ψ α) · (z̄^{(α 0)}/√((α 0)!)) · √((α 0)! · (α|₀)!) · |α|₀⟩`

with `splitVec α = √((α 0)! (α|₀)!) · toCFock (single (restOf α) 1)` (`splitVec_eq`).
Hence the coefficient vector is the explicit `Finsupp`

    `phiCoeff Ψ z = Σ_{α ∈ supp Ψ} (Ψ α · z̄^{(α 0)}/√((α 0)!) · √((α 0)! (α|₀)!)) • single (α|₀) 1`,

and its support consists of the multi-indices `α|₀ = restOf α` with `α ∈ supp Ψ`.  The
degree of such a multi-index is `|α| - (α 0)` (`degree_restOf`, the `n₊ = N - n₀` identity
in coordinates), which the window hypothesis bounds by `⌊M⌋₊`.

Everything is `sorry`-free and rests on the standard axioms only.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false

/-! ## 1. The explicit spectator coefficient vector -/

/-- **The spectator coefficient vector of `Phi (split Ψ) z`.**  A `Finsupp` on the excited
multi-indices whose monomial `β = restOf α` carries the weight
`(Ψ α) · z̄^{(α 0)}/√((α 0)!) · √((α 0)! β!)` — the product of the Fock weight of `split`
with the coherent-state weight of `Phi`. -/
noncomputable def phiCoeff {m : ℕ} [NeZero m] (Ψ : RealFock m) (z : ℂ) :
    (Excited m →₀ ℕ) →₀ ℂ :=
  ∑ α ∈ Ψ.support,
    (((Ψ α : ℂ) * cohWeight (α 0) z * ((fockW (α 0) (restOf α) : ℝ) : ℂ))) •
      Finsupp.single (restOf α) 1

/-! ## 2. `split` on a general vector, expanded over its support -/

/-- **`split` expanded over the support.**  Since `split` is the `Finsupp.lsum` of the
weighted basis vectors `Finsupp.single (α 0) (splitVec α)`, a general `Ψ` is the sum of
those contributions over its support.  The `ℝ`-scalar `Ψ α` of the mode lattice is read as
the `ℂ`-scalar it is (`RCLike.real_smul_eq_coe_smul`), so that the `ℂ`-linear `Phi` applies
below. -/
lemma split_eq_sum_support {m : ℕ} [NeZero m] (Ψ : RealFock m) :
    split Ψ
      = ∑ α ∈ Ψ.support, ((Ψ α : ℂ)) • Finsupp.single (α 0) (splitVec α) := by
  conv_lhs => rw [← Work.BoseBoxFock.sum_single_support Ψ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [split_single_basis]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) (E := ℕ →₀ cfock (Excited m)) (Ψ α) _).symm

/-! ## 3. The weighted basis vector `splitVec α` on the occupation basis -/

/-- **`splitVec α` is the occupation basis vector `|α|₀⟩` up to the Fock weight**
`√((α 0)! · (α|₀)!)`: the `single`-coefficient `fockW (α 0) (restOf α)` is a scalar for the
`Finsupp` (over `ℂ`). -/
lemma splitVec_eq_smul_single {m : ℕ} [NeZero m] (α : Fin m →₀ ℕ) :
    splitVec α
      = ((fockW (α 0) (restOf α) : ℝ) : ℂ) •
          toCFock (Excited m) (Finsupp.single (restOf α) 1) := by
  rw [splitVec, ← Finsupp.smul_single_one, map_smul]

/-! ## 4. The coherent-state transform of `split Ψ` -/

/-- **The coherent-state transform expanded over the support of `Ψ`.**  `Phi` is `ℂ`-linear
and on a condensate level `single n v` it is multiplication by `cohWeight n z`
(`Phi_single`), so pushing it through the expansion of `split Ψ` produces one spectator
vector per monomial of `Ψ`. -/
lemma Phi_split_eq_sum {m : ℕ} [NeZero m] (Ψ : RealFock m) (z : ℂ) :
    Phi (split Ψ) z
      = ∑ α ∈ Ψ.support, (((Ψ α : ℂ) * cohWeight (α 0) z) • splitVec α) := by
  rw [split_eq_sum_support]
  show PhiLin (E := cfock (Excited m)) z (∑ α ∈ Ψ.support, _) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_smul]
  rw [show PhiLin (E := cfock (Excited m)) z (Finsupp.single (α 0) (splitVec α))
        = Phi (Finsupp.single (α 0) (splitVec α)) z from rfl]
  rw [Phi_single]
  rw [smul_smul]

/-- **`toCFock` of the coefficient vector.**  `toCFock` is `ℂ`-linear and `splitVec α` is
the occupation basis vector with the Fock weight (`splitVec_eq_smul_single`), so the
`Finsupp`-level coefficients `phiCoeff Ψ z` map exactly onto the expansion of
`Phi (split Ψ) z`. -/
lemma toCFock_phiCoeff {m : ℕ} [NeZero m] (Ψ : RealFock m) (z : ℂ) :
    toCFock (Excited m) (phiCoeff Ψ z)
      = ∑ α ∈ Ψ.support, (((Ψ α : ℂ) * cohWeight (α 0) z) • splitVec α) := by
  rw [phiCoeff, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_smul, splitVec_eq_smul_single, smul_smul]

/-! ## 5. The degree of the excited part of a multi-index -/

/-- `Σ_{j ≠ 0} α j` as a sum over the complement of the condensate coordinate. -/
lemma sum_excited_val {m : ℕ} [NeZero m] (α : Fin m →₀ ℕ) :
    (∑ j : Excited m, α j.val) = ∑ i ∈ (Finset.univ.erase (0 : Fin m)), α i := by
  rw [Finset.sum_subtype (p := fun x : Fin m => x ≠ 0)
    (Finset.univ.erase (0 : Fin m)) (fun x => by simp) (fun i => α i)]

/-- **The excited occupation of a multi-index.**  The `Finsupp.degree` of the excited part
`restOf α` is the total occupation minus the condensate occupation — the coordinate form of
`n₊ = N - n₀`.  (Stated additively to avoid `ℕ`-truncated subtraction.) -/
lemma degree_restOf {m : ℕ} [NeZero m] (α : Fin m →₀ ℕ) :
    Finsupp.degree (restOf α) + α 0 = deg α := by
  have h1 : Finsupp.degree (restOf α) = ∑ j : Excited m, α j.val := by
    rw [Finsupp.degree_eq_sum]
    exact Finset.sum_congr rfl fun j _ => Finsupp.subtypeDomain_apply
  rw [h1, sum_excited_val, deg_eq_sum, add_comm]
  exact Finset.add_sum_erase Finset.univ α (Finset.mem_univ 0)

/-! ## 6. The support of the coefficient vector -/

/-- **Where the spectator coefficients live.**  Every multi-index in the support of
`phiCoeff Ψ z` is the excited part `restOf α` of a monomial `α` of `Ψ`. -/
lemma mem_support_phiCoeff {m : ℕ} [NeZero m] (Ψ : RealFock m) (z : ℂ)
    {β : Excited m →₀ ℕ} (hβ : β ∈ (phiCoeff Ψ z).support) :
    ∃ α ∈ Ψ.support, β = restOf α := by
  rw [phiCoeff] at hβ
  have hsub := Finsupp.support_finsetSum (s := Ψ.support)
    (f := fun α : Fin m →₀ ℕ => (((Ψ α : ℂ) * cohWeight (α 0) z *
      ((fockW (α 0) (restOf α) : ℝ) : ℂ))) • Finsupp.single (restOf α) (1 : ℂ))
  obtain ⟨α, hα, hβα⟩ := Finset.mem_biUnion.mp (hsub hβ)
  refine ⟨α, hα, ?_⟩
  have h1 : β ∈ (Finsupp.single (restOf α) (1 : ℂ)).support :=
    Finsupp.support_smul (g := Finsupp.single (restOf α) (1 : ℂ))
      (b := ((Ψ α : ℂ) * cohWeight (α 0) z * ((fockW (α 0) (restOf α) : ℝ) : ℂ))) hβα
  exact Finset.mem_singleton.mp (Finsupp.support_single_subset h1)

/-- **The degree bound on the spectator coefficients.**  If every monomial of `Ψ` carries
at most `⌊M⌋₊` particles outside the condensate mode, then the coefficients of
`Phi (split Ψ) z` are supported on the excited multi-indices of degree `≤ ⌊M⌋₊`. -/
lemma degree_le_of_mem_support_phiCoeff {m : ℕ} [NeZero m] {M : ℝ} {Ψ : RealFock m}
    (z : ℂ) (hΨ : ∀ α ∈ Ψ.support, deg α ≤ ⌊M⌋₊ + α 0) :
    ∀ β ∈ (phiCoeff Ψ z).support, Finsupp.degree β ≤ ⌊M⌋₊ := by
  intro β hβ
  obtain ⟨α, hα, rfl⟩ := mem_support_phiCoeff Ψ z hβ
  rw [← Nat.add_le_add_iff_right (n := α 0), degree_restOf]
  exact hΨ α hα

/-! ## 7. The target -/

/-- **The coherent-state transform of a window vector is finitely supported in the excited
multi-index, with degrees bounded by `⌊M⌋₊`.**  The witness is the explicit coefficient
vector `phiCoeff Ψ z`: `Phi (split Ψ) z` is its `toCFock` image, and its support consists of
excited parts of monomials of `Ψ`, whose degrees are `|α| - (α 0) ≤ ⌊M⌋₊` by the window
hypothesis (`excwindow_iff`). -/
theorem phi_split_toCFock {m : ℕ} [NeZero m] {M : ℝ} {n : ℕ} {Ψ : Work.BoseB4.RealFock m}
    (hΨ : Work.BoseBoxFock.ExcWindow M n Ψ) (z : ℂ) :
    ∃ f : (Work.BoseB4.Excited m →₀ ℕ) →₀ ℂ,
      Work.BoseB4.Phi (Work.BoseB4.split Ψ) z
          = Work.BoseB4.toCFock (Work.BoseB4.Excited m) f ∧
        ∀ β ∈ f.support, Finsupp.degree β ≤ ⌊M⌋₊ := by
  obtain ⟨_, hwin⟩ := (excwindow_iff M n Ψ).mp hΨ
  refine ⟨phiCoeff Ψ z, ?_, degree_le_of_mem_support_phiCoeff z hwin⟩
  rw [Phi_split_eq_sum]
  exact (toCFock_phiCoeff Ψ z).symm

end Work.BoseBoxFock
