import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.varLapStarDef
import Submission.Work.Diff.STE.B3.VarCoef.varLapStarOp_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.VarCoefAssembly
import Submission.Work.Diff.STE.B3.VarCoef.isOrd_pow_sub

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `POpStar c c' A B k - POpStar c c' A (-B) k` is an operator of order `2k - 1`

The formal adjoint of `varLap A B` is

  `varLapStar A B h = -(Σ_{ab} ∂_a∂_b (A_ab · h) + Σ_a ∂_a (B_a · h))`,

and `POpStar c c' A B k = M_c ∘ (varLapStar A B)^k ∘ M_{c'}` is the composite that the
adjoint-side estimates of `ENormB_pair_J_commutator_v2` are stated with.

The point of this file is the *antisymmetry defect* `B ↦ -B`: since `varLapStar A B` is **linear in
`B`** (only the first-order part involves `B`), the difference

  `varLapStar A B - varLapStar A (-B) = -2 · Σ_a ∂_a (M_{B_a} ·)`

is an operator of **order one** (its second-order part cancels identically, even more trivially than
in the `varLap - varLapStar` case, where the cancellation is a Leibniz expansion).  Consequently,
by the telescoping identity `D^k - E^k = Σ_i D^i (D - E) E^{k-1-i}` of `VarCoef/isOrd_pow_sub.lean`,
the difference of the `k`-th powers has order `2k - 1`, and the two *outer* multipliers `M_c`, `M_c'`
are the **same** on both sides, so no commutator with the multiplier enters:

  `POpStar c c' A B k - POpStar c c' A (-B) k
     = M_c ∘ ((varLapStar A B)^k - (varLapStar A (-B))^k) ∘ M_{c'}`.

The main result is `POpStar_negB_isOrd`.
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3.VarCoef

/-- The partial derivative of a negated function. -/
theorem negB_pd_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (g : (ι → ℝ) → ℂ) :
    Work.Diff.STE.pd i (-g) = -Work.Diff.STE.pd i g := by
  funext x
  simp only [Work.Diff.STE.pd, Pi.neg_apply, fderiv_neg, neg_apply]

/-- `1`-periodicity of a negated real-valued function. -/
theorem negB_periodic1_neg {ι : Type*} [Fintype ι] [DecidableEq ι] {m : (ι → ℝ) → ℝ}
    (hm : Work.Diff.STE.Periodic1 m) : Work.Diff.STE.Periodic1 (-m) := by
  intro i x
  simp only [Pi.neg_apply, hm i x]

/-- **The pointwise identity**: the difference of `varLapStar A B` and `varLapStar A (-B)` is
`-2 = -1 - 1` times the first-order operator `Σ_a ∂_a (M_{B_a} ·)`, because `varLapStar` is linear
in the first-order coefficient `B`. -/
theorem negB_varLapStar_sub_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ) (f : (ι → ℝ) → ℂ) :
    (varLapStarOp A B - varLapStarOp A (fun a => -B a)) f
      = -(((∑ a, compOp (pdOp a) (mulOp (B a))) f)
          + ((∑ a, compOp (pdOp a) (mulOp (B a))) f)) := by
  -- the `B`-sum of the negated coefficient is the negative of the `B`-sum
  have hY' : ∀ a : ι,
      Work.Diff.STE.pd a (fun y => ((((fun a => -B a) a) y : ℝ) : ℂ) * f y)
        = - Work.Diff.STE.pd a (fun y => ((B a y : ℝ) : ℂ) * f y) := by
    intro a
    have hfun : (fun y : ι → ℝ => ((((fun a => -B a) a) y : ℝ) : ℂ) * f y)
        = -(fun y : ι → ℝ => ((B a y : ℝ) : ℂ) * f y) := by
      funext y
      simp only [Pi.neg_apply, Complex.ofReal_neg]
      ring
    rw [hfun]
    exact negB_pd_neg a _
  -- the first-order part as an operator sum
  have hE0 : ((∑ a, compOp (pdOp a) (mulOp (B a))) f)
      = ∑ a, Work.Diff.STE.pd a (fun y => ((B a y : ℝ) : ℂ) * f y) := by
    rw [finset_sumOp_apply]
    funext x
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun a _ => rfl)
  set X : (ι → ℝ) → ℂ := (∑ a, ∑ b, Work.Diff.STE.pd a (Work.Diff.STE.pd b
      (fun y => ((A a b y : ℝ) : ℂ) * f y))) with hX
  set Y : (ι → ℝ) → ℂ := (∑ a, Work.Diff.STE.pd a
      (fun y => ((B a y : ℝ) : ℂ) * f y)) with hY
  set Y' : (ι → ℝ) → ℂ := (∑ a, Work.Diff.STE.pd a
      (fun y => ((((fun a => -B a) a) y : ℝ) : ℂ) * f y)) with hY'def
  have hY'eq : Y' = -Y := by
    rw [hY'def, hY, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun a _ => hY' a)
  have hL : varLapStarOp A B f = -(X + Y) := rfl
  have hL' : varLapStarOp A (fun a => -B a) f = -(X + Y') := rfl
  have h1 : (varLapStarOp A B - varLapStarOp A (fun a => -B a)) f
      = varLapStarOp A B f - varLapStarOp A (fun a => -B a) f := rfl
  rw [h1, hL, hL', hY'eq, hE0]
  ring

/-- **The `B`-difference of `varLapStar` has order one.** -/
theorem negB_varLapStar_sub_isOrd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Work.Diff.STE.Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Work.Diff.STE.Periodic1 (B a)) :
    ∃ C : ℤ → ℝ, IsOrd 1 C (varLapStarOp A B - varLapStarOp A (fun a => -B a)) := by
  classical
  -- `Σ_a ∂_a M_{B_a}` has order `1 + 0 = 1`
  have hE : ∃ C : ℤ → ℝ, IsOrd 1 C (∑ a, compOp (pdOp a) (mulOp (B a))) := by
    choose Cb hCb using fun a : ι => mulOp_isOrd (B a) (hB a) (hBp a)
    choose Cp hCp using fun a : ι => pdOp_isOrd a
    exact ⟨_, IsOrd.sum Finset.univ (fun a => compOp (pdOp a) (mulOp (B a)))
      (fun a t => Cp a (t - 0) * Cb a t)
      (fun a _ => IsOrd.mono_d
        (IsOrd.comp (T := pdOp a) (U := mulOp (B a)) (hCp a) (hCb a)) (by norm_num))⟩
  obtain ⟨CE, hCE⟩ := hE
  -- hence its negative two-fold sum `-(E + E)` has order `1` and is the difference
  refine ⟨fun t => 2 * (CE t + CE t), ?_⟩
  refine IsOrd.congr (T := -((∑ a, compOp (pdOp a) (mulOp (B a)))
      + (∑ a, compOp (pdOp a) (mulOp (B a)))))
    (IsOrd.neg (IsOrd.add hCE hCE)) (fun f _ => ?_)
  exact (negB_varLapStar_sub_eq A B f).symm

theorem POpStar_negB_isOrd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 1 ≤ k)
    {A : ι → ι → (ι → ℝ) → ℝ} {B : ι → (ι → ℝ) → ℝ} {c c' : (ι → ℝ) → ℝ}
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Work.Diff.STE.Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Work.Diff.STE.Periodic1 (B a))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcp : Work.Diff.STE.Periodic1 c)
    (hc' : ContDiff ℝ (⊤ : ℕ∞) c') (hc'p : Work.Diff.STE.Periodic1 c') :
    ∃ C : ℤ → ℝ, Work.Diff.STE.B3.VarCoef.IsOrd (2 * (k : ℤ) - 1) C
      (Work.Diff.STE.B3.VarCoef.POpStar c c' A B k
        - Work.Diff.STE.B3.VarCoef.POpStar c c' A (fun a => -B a) k) := by
  classical
  -- order certificates for the two outer multipliers
  obtain ⟨Cc, hCc⟩ := mulOp_isOrd c hc hcp
  obtain ⟨Cc', hCc'⟩ := mulOp_isOrd c' hc' hc'p
  -- order certificates for the two adjoint Laplacians
  obtain ⟨CD, hD⟩ := varLapStarOp_isOrd A B hA hAp hB hBp
  obtain ⟨CE, hE⟩ := varLapStarOp_isOrd A (fun a => -B a) hA hAp
    (fun a => (hB a).neg) (fun a => negB_periodic1_neg (hBp a))
  -- the difference of the two Laplacians has order one
  obtain ⟨CDE, hDE⟩ := negB_varLapStar_sub_isOrd A B hA hAp hB hBp
  -- hence the difference of the `k`-th powers has order `2k - 1`
  obtain ⟨Cde, hde⟩ := isOrd_pow_sub (D := varLapStarOp A B)
    (E := varLapStarOp A (fun a => -B a)) hD hE hDE k
  -- compose with `M_{c'}` on the right and `M_c` on the left (both of order `0`)
  obtain ⟨Cmid, hmid⟩ : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (compOp ((varLapStarOp A B)^[k] - (varLapStarOp A (fun a => -B a))^[k])
        (mulOp c')) :=
    ⟨_, IsOrd.mono_d (IsOrd.comp
      (T := (varLapStarOp A B)^[k] - (varLapStarOp A (fun a => -B a))^[k])
      (U := mulOp c') hde hCc') (by omega)⟩
  obtain ⟨Cfin, hfin⟩ : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (compOp (mulOp c) (compOp ((varLapStarOp A B)^[k]
        - (varLapStarOp A (fun a => -B a))^[k]) (mulOp c'))) :=
    ⟨_, IsOrd.mono_d (IsOrd.comp (T := mulOp c)
      (U := compOp ((varLapStarOp A B)^[k] - (varLapStarOp A (fun a => -B a))^[k]) (mulOp c'))
      hCc hmid) (by omega)⟩
  refine ⟨Cfin, IsOrd.congr hfin (fun f hf => ?_)⟩
  -- `POpStar` is `M_c ∘ D^k ∘ M_{c'}`; the two `M_c`'s coincide, so only the linearity of `M_c`
  -- is needed to split the difference
  obtain ⟨CDk, hDk⟩ := isOrd_iterate hD k
  obtain ⟨CEk, hEk⟩ := isOrd_iterate hE k
  have hcm : SmoothPer (mulOp c' f) := hCc'.pres f hf
  have hx : SmoothPer ((varLapStarOp A B)^[k] (mulOp c' f)) := hDk.pres _ hcm
  have hy : SmoothPer ((varLapStarOp A (fun a => -B a))^[k] (mulOp c' f)) := hEk.pres _ hcm
  simp only [POpStar, compOp_apply, Pi.sub_apply]
  exact linSP_map_sub hCc.lin hx hy

end Work.Diff.STE.B3.VarCoef
