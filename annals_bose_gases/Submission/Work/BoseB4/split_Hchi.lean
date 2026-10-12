import Mathlib
import Submission.Work.BoseB4.K2ndDefs
import Submission.Work.BoseB4.lift_sum
import Submission.Work.BoseB4.monoOp_apply_lift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.split_Hchi` — the `χ̂_Λ` rows of FS `eq:HLambdaSecond` under `split`

`Work.BoseB4.split` identifies the mode lattice `RealFock m` with the abstract §8
carrier `FockCore (cfock (Excited m))` (condensate occupation in the `ℕ` index,
excited modes in the complex Fock core).  The row

```
Hchi D = ((ℓ⁻³ a₀†a₀ − μ) Ŵ₁(0) χ̂_Λ)( a_k†a₀ + a₀†a_k )  +  h.c.
```

of the box Hamiltonian is transportable across `split`; the present lemma is the
dictionary statement, i.e. FS `eq:HLambdaSecond`'s `χ̂_Λ` rows in the anti-normal
form consumed by `Work.BoseB4.Kafz_lattice`:

    split (Hchi D x) = (monoOp 2 1 (KchiA D) + monoOp 1 0 (KchiB D)
                        + monoOp 1 2 (KchiC D) + monoOp 0 1 (KchiD D)) (split x).

## The proof

`Hchi` is the product of the condensate factor

    A = ℓ⁻³ a₀†a₀ − μ·1 = ℓ⁻³ (cre m 0) ∘ (ann m 0) − μ·1

with the spectator sum `W10 • Σ_{k≠0} χ̂_Λ(k)( a_k†a₀ + a₀†a_k )`; write the two
halves of the latter as `shchiA` (`a_k† a₀`) and `shchiB` (`a₀† a_k`).  The four
`Split_*` transport lemmas move every mode operator to the abstract side:

    split (shchiA D x) = lift (Schi D) (a₀ (split x)),
    split (shchiB D x) = lift (Tchi D) (a₀† (split x)),
    split (A y)        = ℓ⁻³ • a₀†a₀ (split y) − μ • split y,

where `Schi = Σ_{k≠0} Ŵ₁(0)χ̂_Λ(k) a_k†` and `Tchi = Σ_{k≠0} Ŵ₁(0)χ̂_Λ(k) a_k` are
the spectator sums on the complex core (`lift` of a finite sum is the sum of the
lifts, `Work.BoseB4.lift_sum`).  Since the spectator operators `lift (Schi D)`,
`lift (Tchi D)` commute with `a₀` and `a₀†`, the condensate factor acts on the
condensate part alone, and the identity turns into the elementary algebra

    a₀† a₀² = a₀² a₀† − 2 a₀,      a₀† a₀ a₀† = a₀ a₀†² − a₀†

of `[a₀, a₀†] = 1` (`Defs.ccr`), which is exactly the splitting of the
`(2,1) : (1,0)` and `(1,2) : (0,1)` slots recorded in `KchiA … KchiD`.  Both
regroupings are proved on the core in `a0d_a0sq_apply` / `a0d_a0_apply` and the
final combinatorial step is `module`.
-/

noncomputable section

open scoped lp BigOperators

namespace Work.BoseB4

set_option autoImplicit false

/-! The transport identities below are proved by long `rw` chains on terms with
heavily nested `lift`s; the default heartbeat budget is too small for the
definitional-equality checks those `rw`s perform. -/
set_option maxHeartbeats 1000000

variable {m : ℕ} [NeZero m]

/-! ## The two halves of the `χ̂_Λ` rows, and their condensate factor -/

/-- The first half `Ŵ₁(0) Σ_{k≠0} χ̂_Λ(k) a_k† a₀` of `Hchi`. -/
private noncomputable def shchiA (D : H2ndData m) : RealFock m →ₗ[ℝ] RealFock m :=
  D.W10 • ∑ k ∈ exc m, D.chiHat k • ((cre m k).comp (ann m 0))

/-- The `h.c.` half `Ŵ₁(0) Σ_{k≠0} χ̂_Λ(k) a₀† a_k` of `Hchi`. -/
private noncomputable def shchiB (D : H2ndData m) : RealFock m →ₗ[ℝ] RealFock m :=
  D.W10 • ∑ k ∈ exc m, D.chiHat k • ((cre m 0).comp (ann m k))

/-- The condensate factor `ℓ⁻³ a₀†a₀ − μ` multiplying the two halves. -/
private noncomputable def shchiPre (D : H2ndData m) : RealFock m →ₗ[ℝ] RealFock m :=
  D.ell ^ (-(3 : ℝ)) • ((cre m 0).comp (ann m 0)) - D.mu • (1 : RealFock m →ₗ[ℝ] RealFock m)

/-! ## The spectator sums on the complex Fock core -/

/-- The spectator operator `Σ_{k≠0} Ŵ₁(0)χ̂_Λ(k) a_k†`. -/
private noncomputable def Schi (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, ((D.W10 * D.chiHat k : ℝ) : ℂ) • creX m k

/-- The spectator operator `Σ_{k≠0} Ŵ₁(0)χ̂_Λ(k) a_k`. -/
private noncomputable def Tchi (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, ((D.W10 * D.chiHat k : ℝ) : ℂ) • annX m k

/-! ## `KchiA … KchiD` are the scalar multiples of `Schi`, `Tchi` of the slots -/

private lemma KchiA_eq (D : H2ndData m) : KchiA D = ((i3 D : ℝ) : ℂ) • Schi D := by
  rw [KchiA, Schi, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul]
  congr 1
  push_cast
  ring

private lemma KchiB_eq (D : H2ndData m) :
    KchiB D = ((-(2 * i3 D + D.mu) : ℝ) : ℂ) • Schi D := by
  rw [KchiB, Schi, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul]
  congr 1
  push_cast
  ring

private lemma KchiC_eq (D : H2ndData m) : KchiC D = ((i3 D : ℝ) : ℂ) • Tchi D := by
  rw [KchiC, Tchi, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul]
  congr 1
  push_cast
  ring

private lemma KchiD_eq (D : H2ndData m) :
    KchiD D = ((-(i3 D + D.mu) : ℝ) : ℂ) • Tchi D := by
  rw [KchiD, Tchi, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul]
  congr 1
  push_cast
  ring

/-! ## The spectator sums are sums of lifts -/

private lemma lift_Schi (D : H2ndData m) :
    lift (Schi D) = ∑ k ∈ exc m, ((D.W10 * D.chiHat k : ℝ) : ℂ) • lift (creX m k) := by
  rw [Schi, lift_sum]
  exact Finset.sum_congr rfl fun k _ => lift_smul _ _

private lemma lift_Tchi (D : H2ndData m) :
    lift (Tchi D) = ∑ k ∈ exc m, ((D.W10 * D.chiHat k : ℝ) : ℂ) • lift (annX m k) := by
  rw [Tchi, lift_sum]
  exact Finset.sum_congr rfl fun k _ => lift_smul _ _

/-! ## The mode operators under `split` -/

private lemma split_ann_zero' (y : RealFock m) : split ((ann m 0) y) = a0 (split y) := by
  have h := LinearMap.congr_fun (Split_ann_zero (m := m)) y
  simpa [LinearMap.comp_apply] using h

private lemma split_cre_zero' (y : RealFock m) : split ((cre m 0) y) = a0d (split y) := by
  have h := LinearMap.congr_fun (Split_cre_zero (m := m)) y
  simpa [LinearMap.comp_apply] using h

private lemma split_ann_exc' {k : Fin m} (hk : k ≠ 0) (y : RealFock m) :
    split ((ann m k) y) = lift (annX m k) (split y) := by
  have h := LinearMap.congr_fun (Split_ann_excited (m := m) ⟨k, hk⟩) y
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at h
  rw [h]
  congr 1
  simp [annX, dif_neg hk]

private lemma split_cre_exc' {k : Fin m} (hk : k ≠ 0) (y : RealFock m) :
    split ((cre m k) y) = lift (creX m k) (split y) := by
  have h := LinearMap.congr_fun (Split_cre_excited (m := m) ⟨k, hk⟩) y
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at h
  rw [h]
  congr 1
  simp [creX, dif_neg hk]

/-! ## The condensate CCR in applied form -/

private lemma a0d_a0_apply (v : FockCore (cfock (Excited m))) :
    a0d (a0 v) = a0 (a0d v) - v := by
  have h := LinearMap.congr_fun (ccr (E := cfock (Excited m))) v
  simp only [LinearMap.comp_apply, LinearMap.add_apply, Module.End.one_apply] at h
  rw [h, add_sub_cancel_right]

private lemma a0d_a0sq_apply (v : FockCore (cfock (Excited m))) :
    a0d (a0 (a0 v)) = a0 (a0 (a0d v)) - (2 : ℂ) • a0 v := by
  rw [a0d_a0_apply (a0 v), a0d_a0_apply v, map_sub]
  module

/-! ## The two halves transported across `split` -/

private lemma split_shchiA (D : H2ndData m) (x : RealFock m) :
    split ((shchiA D) x) = lift (Schi D) (a0 (split x)) := by
  rw [lift_Schi, LinearMap.sum_apply]
  simp only [shchiA, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    LinearMap.comp_apply]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
  rw [split_cre_exc' hk0, split_ann_zero', ← mul_smul]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) (E := FockCore (cfock (Excited m))) (D.W10 * D.chiHat k) _

private lemma split_shchiB (D : H2ndData m) (x : RealFock m) :
    split ((shchiB D) x) = lift (Tchi D) (a0d (split x)) := by
  rw [lift_Tchi, LinearMap.sum_apply]
  simp only [shchiB, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    LinearMap.comp_apply]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
  rw [split_cre_zero', split_ann_exc' hk0, ← lift_a0d, ← mul_smul]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) (E := FockCore (cfock (Excited m))) (D.W10 * D.chiHat k) _

/-- The condensate factor under `split`: `a₀†a₀` becomes `a0d ∘ a0` and the
identity stays put. -/
private lemma split_shchiPre (D : H2ndData m) (y : RealFock m) :
    split ((shchiPre D) y)
      = ((i3 D : ℝ) : ℂ) • (a0d (a0 (split y))) - ((D.mu : ℝ) : ℂ) • (split y) := by
  rw [shchiPre, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_smul, map_smul, LinearMap.comp_apply,
    split_cre_zero', split_ann_zero']
  rw [i3]
  congr 1

/-! ## `Hchi` as a composition -/

private lemma Hchi_apply (D : H2ndData m) (x : RealFock m) :
    Hchi D x = (shchiPre D) ((shchiA D) x) + (shchiPre D) ((shchiB D) x) := by
  simp only [Hchi, shchiPre, shchiA, shchiB, LinearMap.comp_apply, LinearMap.add_apply]

/-! ## The two halves of the dictionary statement -/

/-- The `a_k† a₀` half: the `(2,1)` and `(1,0)` slots of `KchiA`, `KchiB`. -/
private lemma split_HchiA (D : H2ndData m) (x : RealFock m) :
    split ((shchiPre D) ((shchiA D) x))
      = lift (KchiA D) (a0 (a0 (a0d (split x)))) + lift (KchiB D) (a0 (split x)) := by
  rw [split_shchiPre, split_shchiA, KchiA_eq, KchiB_eq, lift_smul, lift_smul,
    LinearMap.smul_apply, LinearMap.smul_apply,
    ← lift_a0, ← lift_a0d, a0d_a0sq_apply, map_sub, map_smul]
  rw [smul_sub]
  push_cast
  module

/-- The `a₀† a_k` half: the `(1,2)` and `(0,1)` slots of `KchiC`, `KchiD`. -/
private lemma split_HchiB (D : H2ndData m) (x : RealFock m) :
    split ((shchiPre D) ((shchiB D) x))
      = lift (KchiC D) (a0 (a0d (a0d (split x)))) + lift (KchiD D) (a0d (split x)) := by
  rw [split_shchiPre, split_shchiB, KchiC_eq, KchiD_eq, lift_smul, lift_smul,
    LinearMap.smul_apply, LinearMap.smul_apply,
    ← lift_a0, ← lift_a0d, a0d_a0_apply, map_sub]
  rw [smul_sub]
  push_cast
  module

/-! ## The dictionary statement -/

theorem split_Hchi {m : ℕ} [NeZero m] (D : Work.BoseB4.H2ndData m) (x : Work.BoseB4.RealFock m) :
    Work.BoseB4.split (Work.BoseB4.Hchi D x)
      = (Work.BoseB4.monoOp 2 1 (Work.BoseB4.KchiA D)
          + Work.BoseB4.monoOp 1 0 (Work.BoseB4.KchiB D)
          + Work.BoseB4.monoOp 1 2 (Work.BoseB4.KchiC D)
          + Work.BoseB4.monoOp 0 1 (Work.BoseB4.KchiD D)) (Work.BoseB4.split x) := by
  rw [Hchi_apply, map_add, split_HchiA, split_HchiB]
  rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.add_apply]
  rw [monoOp_apply_lift, monoOp_apply_lift, monoOp_apply_lift, monoOp_apply_lift]
  simp only [a0pow_succ, a0pow_zero, a0dpow_succ, a0dpow_zero, Module.End.one_apply,
    LinearMap.comp_apply]
  abel

end Work.BoseB4
