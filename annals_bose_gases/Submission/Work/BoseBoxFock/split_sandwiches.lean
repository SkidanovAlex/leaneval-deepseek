import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseBoxFock.KafzHonest

/-!
# `Work.BoseBoxFock.split_sandwiches` — the three transported dictionary shapes

The three "sandwich" shapes of the dictionary of `Work.BoseBoxFock.KafzHonest`, in the
form in which FS's kinetic row `∫ Ŵ₁ a_k†a_k`, the Bogoliubov rows
`a₀†a₀†a_ka_{−k}` and the `χ̂`-rows `L₀ a_k† a₀` occur: the condensate ladder
operators are transported to `a₀`, `a₀†` on the spectator core, and the resulting word
is put in anti-normal form `monoOp p q B` (FS `eq:subst-z`).  The three identities are

* `a₀† (a_k† a_k) a₀ ↦ monoOp 1 1 B − monoOp 0 0 B`,
* `(a₀†)² (a_k a_{−k}) ↦ monoOp 0 2 B`,
* `a₀† a₀ (a_k†) a₀ ↦ monoOp 2 1 B − 2 monoOp 1 0 B`,

with `B` the weighted sum of the transported spectator words
(`Work.BoseB4.monoOp`, `Work.BoseB4.a0d_comp_a0_sq`, `Work.BoseB4.monoOp_two_one`).
-/

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

section Helpers

variable {m : ℕ} [NeZero m]
open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000


/-! ## 1. Auxiliary dictionary lemmas -/

/-- `split` of `annOf φ ∘ annOf ψ`. -/
theorem ss_split_annOf_annOf (φ ψ : Fin m → ℝ) (hφ : φ 0 = 0) (hψ : ψ 0 = 0)
    (x : RealFock m) :
    split (annOf m φ (annOf m ψ x)) = lift (annOfE φ ∘ₗ annOfE ψ) (split x) := by
  rw [split_annOf φ hφ, split_annOf ψ hψ]
  exact congrArg (fun f => f (split x)) (lift_comp (annOfE φ) (annOfE ψ)).symm

/-- A weighted sum of dictionary-correct spectator words transports under `split`. -/
theorem ss_lift_weighted {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (s : Finset Mode) (c : Mode → ℝ)
    (A : Mode → RealFock m →ₗ[ℝ] RealFock m)
    (B : Mode → cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (hAB : ∀ k ∈ s, ∀ y, split (A k y) = lift (B k) (split y)) (x : RealFock m) :
    split ((∑ k ∈ s, c k • A k) x) = lift (∑ k ∈ s, ((c k : ℝ) : ℂ) • B k) (split x) := by
  have h1 : (∑ k ∈ s, c k • A k) x = ∑ k ∈ s, c k • (A k x) := by
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [LinearMap.smul_apply]
  rw [h1, map_sum]
  have h2 : ∀ k ∈ s, split (c k • (A k x)) = c k • lift (B k) (split x) := by
    intro k hk
    rw [map_smul, hAB k hk]
  rw [Finset.sum_congr rfl h2, lift_sum]
  simp only [lift_smul, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.smul_apply]
  exact (Complex.coe_smul (c k) (lift (B k) (split x))).symm

/-! ## 2. The three condensate-monomial identities -/

/-- `a₀† ⊗ B ⊗ a₀ = a₀a₀† ⊗ B − B`. -/
theorem ss_atom_11 (B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) :
    (a0d : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m))).comp
        ((lift B).comp a0) = monoOp 1 1 B - monoOp 0 0 B := by
  rw [lift_comm_a0 B, ← LinearMap.comp_assoc, ← monoOp_one_one_sub_zero_zero B]

/-- `(a₀†)² ⊗ B = (a₀†)² ⊗ B`. -/
theorem ss_atom_02 (B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) :
    (a0d : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m))).comp
        ((a0d : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m))).comp
          (lift B))
      = monoOp 0 2 B := by
  simp [monoOp, a0pow_zero, a0dpow_succ, a0dpow_zero, one_comp_lm, LinearMap.comp_assoc]

/-- `a₀† a₀ ⊗ B ⊗ a₀ = a₀² a₀† ⊗ B − 2 a₀ ⊗ B`. -/
theorem ss_atom_21 (B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) :
    (a0d : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m))).comp
        (a0.comp ((lift B).comp a0))
      = monoOp 2 1 B - (2 : ℂ) • monoOp 1 0 B := by
  have h1 : a0.comp (a0.comp (lift B)) = (a0.comp a0).comp (lift B) :=
    (LinearMap.comp_assoc (lift B) a0 a0).symm
  calc (a0d.comp (a0.comp ((lift B).comp a0)))
      = a0d.comp (a0.comp (a0.comp (lift B))) := by rw [lift_comm_a0 B]
    _ = a0d.comp ((a0.comp a0).comp (lift B)) := by rw [h1]
    _ = (a0d.comp (a0.comp a0)).comp (lift B) := (LinearMap.comp_assoc _ _ _).symm
    _ = ((a0.comp a0).comp a0d - (2 : ℂ) • a0).comp (lift B) := by rw [a0d_comp_a0_sq]
    _ = ((a0.comp a0).comp a0d).comp (lift B) - (2 : ℂ) • (a0.comp (lift B)) := by
        rw [LinearMap.sub_comp, LinearMap.smul_comp]
    _ = (a0.comp a0).comp (a0d.comp (lift B)) - (2 : ℂ) • monoOp 1 0 B := by
        rw [LinearMap.comp_assoc, monoOp_one_zero]
    _ = monoOp 2 1 B - (2 : ℂ) • monoOp 1 0 B := by
        rw [← monoOp_two_one]

/-! ## 3. The sum reassembly -/

/-- Reassembling a weighted sum of transported monomials (two slots, with a scalar on
the second). -/
theorem ss_sum_diff {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℝ)
    (B : ι → cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (y : FockCore (cfock (Excited m))) (p q p' q' : ℕ) (z : ℂ) :
    (∑ k ∈ s, c k • ((monoOp p q (B k) - z • monoOp p' q' (B k)) y))
      = (monoOp p q (∑ k ∈ s, ((c k : ℝ) : ℂ) • B k)
          - z • monoOp p' q' (∑ k ∈ s, ((c k : ℝ) : ℂ) • B k)) y := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    monoOp_sum, monoOp_smul, Complex.coe_smul, smul_sub, Finset.sum_sub_distrib,
    Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => smul_comm (c k) z _

/-- Reassembling a weighted sum of transported monomials (one slot). -/
theorem ss_sum_single {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℝ)
    (B : ι → cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (y : FockCore (cfock (Excited m))) (p q : ℕ) :
    (∑ k ∈ s, c k • ((monoOp p q (B k)) y))
      = (monoOp p q (∑ k ∈ s, ((c k : ℝ) : ℂ) • B k)) y := by
  rw [monoOp_sum]
  simp only [monoOp_smul, LinearMap.sum_apply, LinearMap.smul_apply, Complex.coe_smul]
  rfl

/-! ## 4. The three conjuncts -/

/-- The first conjunct. -/
theorem ss_conj1 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (s : Finset Mode) (c : Mode → ℝ) (φ : Mode → Fin m → ℝ) (hφ : ∀ k ∈ s, φ k 0 = 0)
    (x : RealFock m) :
    split ((∑ k ∈ s, c k • ((cre m 0).comp ((creOf m (φ k)).comp
            ((annOf m (φ k)).comp (ann m 0))))) x)
      = (monoOp 1 1 (∑ k ∈ s, ((c k : ℝ) : ℂ) •
            ((creOfE (φ k)).comp (annOfE (φ k))))
          - monoOp 0 0 (∑ k ∈ s, ((c k : ℝ) : ℂ) •
            ((creOfE (φ k)).comp (annOfE (φ k))))) (split x) := by
  have hstep : ∀ k ∈ s,
      split (((cre m 0).comp ((creOf m (φ k)).comp
        ((annOf m (φ k)).comp (ann m 0)))) x)
        = ((monoOp 1 1 ((creOfE (φ k)).comp (annOfE (φ k)))
            - monoOp 0 0 ((creOfE (φ k)).comp (annOfE (φ k)))) (split x)) := by
    intro k hk
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      split_cre_zero, split_creOf_annOf (φ k) (φ k) (hφ k hk) (hφ k hk), split_ann_zero]
    simpa only [LinearMap.comp_apply]
      using LinearMap.congr_fun (ss_atom_11 ((creOfE (φ k)).comp (annOfE (φ k)))) (split x)
  have hsum : (∑ k ∈ s, c k • ((cre m 0).comp ((creOf m (φ k)).comp
        ((annOf m (φ k)).comp (ann m 0))))) x
      = ∑ k ∈ s, c k • (((cre m 0).comp ((creOf m (φ k)).comp
        ((annOf m (φ k)).comp (ann m 0)))) x) := by
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [LinearMap.smul_apply]
  rw [hsum, map_sum]
  have h2 : ∀ k ∈ s, split (c k • (((cre m 0).comp ((creOf m (φ k)).comp
        ((annOf m (φ k)).comp (ann m 0)))) x))
      = c k • ((monoOp 1 1 ((creOfE (φ k)).comp (annOfE (φ k)))
          - monoOp 0 0 ((creOfE (φ k)).comp (annOfE (φ k)))) (split x)) := by
    intro k hk
    rw [map_smul, hstep k hk]
  rw [Finset.sum_congr rfl h2]
  simpa only [one_smul] using
    ss_sum_diff s c (fun k => (creOfE (φ k)).comp (annOfE (φ k))) (split x) 1 1 0 0 1

/-- The second conjunct. -/
theorem ss_conj2 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (s : Finset Mode) (c : Mode → ℝ) (φ ψ : Mode → Fin m → ℝ)
    (hφ : ∀ k ∈ s, φ k 0 = 0) (hψ : ∀ k ∈ s, ψ k 0 = 0) (x : RealFock m) :
    split ((∑ k ∈ s, c k • ((cre m 0).comp ((cre m 0).comp
            ((annOf m (φ k)).comp (annOf m (ψ k)))))) x)
      = (monoOp 0 2 (∑ k ∈ s, ((c k : ℝ) : ℂ) •
            ((annOfE (φ k)).comp (annOfE (ψ k))))) (split x) := by
  have hstep : ∀ k ∈ s,
      split (((cre m 0).comp ((cre m 0).comp
        ((annOf m (φ k)).comp (annOf m (ψ k))))) x)
        = ((monoOp 0 2 ((annOfE (φ k)).comp (annOfE (ψ k)))) (split x)) := by
    intro k hk
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      split_cre_zero, split_cre_zero,
      ss_split_annOf_annOf (φ k) (ψ k) (hφ k hk) (hψ k hk)]
    simpa only [LinearMap.comp_apply]
      using LinearMap.congr_fun (ss_atom_02 ((annOfE (φ k)).comp (annOfE (ψ k)))) (split x)
  have hsum : (∑ k ∈ s, c k • ((cre m 0).comp ((cre m 0).comp
        ((annOf m (φ k)).comp (annOf m (ψ k)))))) x
      = ∑ k ∈ s, c k • (((cre m 0).comp ((cre m 0).comp
        ((annOf m (φ k)).comp (annOf m (ψ k))))) x) := by
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [LinearMap.smul_apply]
  rw [hsum, map_sum]
  have h2 : ∀ k ∈ s, split (c k • (((cre m 0).comp ((cre m 0).comp
        ((annOf m (φ k)).comp (annOf m (ψ k))))) x))
      = c k • ((monoOp 0 2 ((annOfE (φ k)).comp (annOfE (ψ k)))) (split x)) := by
    intro k hk
    rw [map_smul, hstep k hk]
  rw [Finset.sum_congr rfl h2]
  exact ss_sum_single s c (fun k => (annOfE (φ k)).comp (annOfE (ψ k))) (split x) 0 2

/-- The third conjunct. -/
theorem ss_conj3 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (s : Finset Mode) (c : Mode → ℝ) (φ : Mode → Fin m → ℝ) (hφ : ∀ k ∈ s, φ k 0 = 0)
    (x : RealFock m) :
    split ((∑ k ∈ s, c k • ((cre m 0).comp ((ann m 0).comp
            ((creOf m (φ k)).comp (ann m 0))))) x)
      = (monoOp 2 1 (∑ k ∈ s, ((c k : ℝ) : ℂ) • creOfE (φ k))
          - (2 : ℂ) • monoOp 1 0 (∑ k ∈ s, ((c k : ℝ) : ℂ) • creOfE (φ k)))
          (split x) := by
  have hstep : ∀ k ∈ s,
      split (((cre m 0).comp ((ann m 0).comp ((creOf m (φ k)).comp (ann m 0)))) x)
        = ((monoOp 2 1 (creOfE (φ k)) - (2 : ℂ) • monoOp 1 0 (creOfE (φ k)))
            (split x)) := by
    intro k hk
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      split_cre_zero, split_ann_zero, split_creOf (φ k) (hφ k hk), split_ann_zero]
    simpa only [LinearMap.comp_apply]
      using LinearMap.congr_fun (ss_atom_21 (creOfE (φ k))) (split x)
  have hsum : (∑ k ∈ s, c k • ((cre m 0).comp ((ann m 0).comp
        ((creOf m (φ k)).comp (ann m 0))))) x
      = ∑ k ∈ s, c k • (((cre m 0).comp ((ann m 0).comp
        ((creOf m (φ k)).comp (ann m 0)))) x) := by
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [LinearMap.smul_apply]
  rw [hsum, map_sum]
  have h2 : ∀ k ∈ s, split (c k • (((cre m 0).comp ((ann m 0).comp
        ((creOf m (φ k)).comp (ann m 0)))) x))
      = c k • ((monoOp 2 1 (creOfE (φ k)) - (2 : ℂ) • monoOp 1 0 (creOfE (φ k)))
          (split x)) := by
    intro k hk
    rw [map_smul, hstep k hk]
  rw [Finset.sum_congr rfl h2]
  exact ss_sum_diff s c (fun k => creOfE (φ k)) (split x) 2 1 1 0 2

end Helpers

theorem split_sandwiches {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {m : ℕ} [NeZero m]
    (s : Finset Mode) (c : Mode → ℝ) (φ ψ : Mode → Fin m → ℝ)
    (hφ : ∀ k ∈ s, φ k 0 = 0) (hψ : ∀ k ∈ s, ψ k 0 = 0) (x : Work.BoseB4.RealFock m) :
    (Work.BoseB4.split ((∑ k ∈ s, c k •
          ((Work.BoseB4.cre m 0).comp ((Work.BoseB4.creOf m (φ k)).comp
            ((Work.BoseB4.annOf m (φ k)).comp (Work.BoseB4.ann m 0))))) x)
      = (Work.BoseB4.monoOp 1 1 (∑ k ∈ s, ((c k : ℝ) : ℂ) •
            ((Work.BoseBoxFock.creOfE (φ k)).comp (Work.BoseBoxFock.annOfE (φ k))))
          - Work.BoseB4.monoOp 0 0 (∑ k ∈ s, ((c k : ℝ) : ℂ) •
            ((Work.BoseBoxFock.creOfE (φ k)).comp (Work.BoseBoxFock.annOfE (φ k))))) (Work.BoseB4.split x))
    ∧
    (Work.BoseB4.split ((∑ k ∈ s, c k •
          ((Work.BoseB4.cre m 0).comp ((Work.BoseB4.cre m 0).comp
            ((Work.BoseB4.annOf m (φ k)).comp (Work.BoseB4.annOf m (ψ k)))))) x)
      = (Work.BoseB4.monoOp 0 2 (∑ k ∈ s, ((c k : ℝ) : ℂ) •
            ((Work.BoseBoxFock.annOfE (φ k)).comp (Work.BoseBoxFock.annOfE (ψ k)))))
          (Work.BoseB4.split x))
    ∧
    (Work.BoseB4.split ((∑ k ∈ s, c k •
          ((Work.BoseB4.cre m 0).comp ((Work.BoseB4.ann m 0).comp
            ((Work.BoseB4.creOf m (φ k)).comp (Work.BoseB4.ann m 0))))) x)
      = (Work.BoseB4.monoOp 2 1 (∑ k ∈ s, ((c k : ℝ) : ℂ) • Work.BoseBoxFock.creOfE (φ k))
          - (2 : ℂ) • Work.BoseB4.monoOp 1 0 (∑ k ∈ s, ((c k : ℝ) : ℂ) • Work.BoseBoxFock.creOfE (φ k)))
          (Work.BoseB4.split x)) := by
  exact ⟨ss_conj1 s c φ hφ x, ss_conj2 s c φ ψ hφ hψ x, ss_conj3 s c φ hφ x⟩

end Work.BoseBoxFock

