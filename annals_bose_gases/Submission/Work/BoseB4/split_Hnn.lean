import Mathlib
import Submission.Work.BoseB4.K2ndDefs
import Submission.Work.BoseB4.a0d_comp_a0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.split_Hnn` — the `Hnn` row of `eq:HLambdaSecond` under the split

FS `eq:HLambdaSecond`'s last row is

    `((ℓ⁻³a₀†a₀ − μ)Ŵ₁(0) + ℓ⁻³a₀†a₀Ŵ₁ω(0)) ℓ⁻³ ∫ a_k†a_k dk`,

the operator `Work.BoseB4.Hnn` on the mode lattice `RealFock m`.  Under the
`⟨condensate | excited⟩` split `Work.BoseB4.split` the two factors translate as

* the condensate factor `ℓ⁻³ a₀†a₀ − μ` (resp. `ℓ⁻³a₀†a₀`) becomes the abstract
  operator `(ℓ⁻³ • numOp − μ • 1)` (the `Split_ann_zero`/`Split_cre_zero`
  dictionary), and
* the excitation factor `Ŵ₁(0) ℓ⁻³ Σ_{k≠0} a_k†a_k` becomes the levelwise lift of
  the spectator operator `Sn = Σ_{k≠0} a_k†a_k`
  (the `Split_ann_excited`/`Split_cre_excited` dictionary).

The anti-normal reordering of the product is the single CCR fact
`a₀†a₀ = a₀a₀† − 1`, i.e. `numOp ∘ lift B = monoOp 1 1 B − monoOp 0 0 B`
(`numOp_comp_lift` below): the `monoOp 1 1` slot carries the `a₀†a₀` part and the
`monoOp 0 0` slot the vacuum commutator `−ℓ⁻³B`, which merges with the `−μ` term
into the coefficient `−(ℓ⁻³+μ)Ŵ₁(0)ℓ⁻³` of `Work.BoseB4.KnnB`.  The very same
computation with `Ŵ₁ω(0)` in place of `Ŵ₁(0)` gives the `KnnC`/`KnnD` slots.

## Structure

The reusable pieces are

* `numOp_lift_apply` / `numOp_comp_lift` — the CCR reordering of `a₀†a₀`;
* `split_number_mode`, `split_number_sum` — the excited-mode dictionary for
  `Σ_{k≠0} a_k†a_k` (with `Sn` the abstract spectator sum);
* `split_numOp` — the condensate dictionary for `a₀†a₀`;
* the two row lemmas `split_Hnn_row1` / `split_Hnn_row2`, one for each of the two
  `comp` summands of `Hnn`, and the scalar identities `KnnA_eq` … `KnnD_eq`
  rewriting the four `K**` operators as scalar multiples of `Sn`.

The `RCLike.real_smul_eq_coe_smul` bookkeeping (`real_smul_eq_coe_smul`) is the
only place where the real scalars of the mode lattice meet the complex scalars of
the abstract Fock core; after it, the two sides of the identity are matched by
`module` (pure `smul` algebra over `ℂ`).
-/

noncomputable section

open scoped lp BigOperators

namespace Work.BoseB4

set_option autoImplicit false

-- The two row lemmas below match on the large composite terms of `Hnn`, whose
-- comparison exceeds the default elaboration budget.
set_option maxHeartbeats 1000000

variable {m : ℕ} [NeZero m]

/-! ## Two algebraic helpers -/

/-- The real scalar action on a `ℂ`-module is the complex action of the coerced
scalar.  This is the only bridge needed between the (real) mode lattice and the
(complex) abstract Fock core. -/
private lemma real_smul_eq_coe_smul {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] (r : ℝ) (v : E) : r • v = ((r : ℂ)) • v :=
  RCLike.real_smul_eq_coe_smul (K := ℂ) r v

/-! ## The two operators of `Hnn` on the mode lattice -/

/-- The mode-lattice number operator of the condensate, `a₀†a₀`. -/
private noncomputable def Nmode : RealFock m →ₗ[ℝ] RealFock m := (cre m 0).comp (ann m 0)

/-- The mode-lattice number operator of the excited modes, `Σ_{k≠0} a_k†a_k`. -/
private noncomputable def Sel : RealFock m →ₗ[ℝ] RealFock m :=
  ∑ k ∈ exc m, (cre m k).comp (ann m k)

/-! ## The abstract spectator number sum -/

/-- The abstract spectator operator `Σ_{k≠0} a_k†a_k` whose scalar multiples are
`Work.BoseB4.KnnA`–`KnnD`. -/
private noncomputable def Sn : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, CX k

private lemma lift_zero : lift (0 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) = 0 := by
  ext x n
  simp

/-- `lift` commutes with finite sums of spectator operators. -/
private lemma lift_sum {ι : Type*} (s : Finset ι)
    (B : ι → cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) :
    lift (∑ i ∈ s, B i) = ∑ i ∈ s, lift (B i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty, lift_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, lift_add, ih]

/-- The levelwise lift of a composite is the composite of the lifts. -/
private lemma lift_lift (B B' : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (v : FockCore (cfock (Excited m))) :
    lift B (lift B' v) = lift (B.comp B') v := by
  rw [← LinearMap.comp_apply, ← lift_comp]

/-! ## The mode dictionary of `split` -/

private lemma annX_of_ne (k : Fin m) (hk : k ≠ 0) :
    annX m k = annC (Excited m) ⟨k, hk⟩ := by
  rw [annX, dif_neg (show ¬ (k = 0) from hk)]

private lemma creX_of_ne (k : Fin m) (hk : k ≠ 0) :
    creX m k = creC (Excited m) ⟨k, hk⟩ := by
  rw [creX, dif_neg (show ¬ (k = 0) from hk)]

/-- An excited mode's number operator under `split`: `a_k†a_k` corresponds to the
levelwise lift of `CX k = creX k ∘ annX k`. -/
private lemma split_number_mode (k : Fin m) (hk : k ≠ 0) (x : RealFock m) :
    split (((cre m k).comp (ann m k)) x) = lift (CX k) (split x) := by
  have h1 := LinearMap.congr_fun (Split_ann_excited (m := m) ⟨k, hk⟩) x
  have h2 := LinearMap.congr_fun (Split_cre_excited (m := m) ⟨k, hk⟩) ((ann m k) x)
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at h1 h2 ⊢
  rw [h2, h1, lift_lift, CX, annX_of_ne k hk, creX_of_ne k hk]

/-- `Σ_{k≠0} a_k†a_k` under `split`. -/
private lemma split_number_sum (x : RealFock m) :
    split (Sel x) = lift Sn (split x) := by
  rw [Sel, LinearMap.sum_apply, map_sum, Sn, lift_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun k hk => split_number_mode k (Finset.mem_erase.mp hk).1 x

/-- The condensate number operator under `split`: `a₀†a₀ ↦ numOp`. -/
private lemma split_numOp (x : RealFock m) :
    split (Nmode x) = numOp (split x) := by
  have h1 := LinearMap.congr_fun (Split_ann_zero (m := m)) x
  have h2 := LinearMap.congr_fun (Split_cre_zero (m := m)) ((ann m 0) x)
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at h1 h2
  rw [Nmode, LinearMap.comp_apply, h2, h1, numOp, LinearMap.comp_apply]

/-! ## The CCR reordering of the condensate number operator -/

private lemma one_comp_core (f : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m))) :
    (1 : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m))).comp f = f := by
  rw [show (1 : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m))) = LinearMap.id
    from rfl, LinearMap.id_comp]

/-- `monoOp 1 1 B` is `a₀a₀† ⊗ B` on the core (`a0pow 1 = a₀`, `a0dpow 1 = a₀†`). -/
private lemma monoOp_one_one (B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) :
    monoOp 1 1 B = a0.comp (a0d.comp (lift B)) := by
  simp only [monoOp, a0pow_zero, a0pow_succ, a0dpow_zero, a0dpow_succ]
  rw [one_comp_core, one_comp_core]

/-- **The CCR reordering**: `numOp ∘ lift B = monoOp 1 1 B − monoOp 0 0 B`, i.e.
`a₀†a₀ ⊗ B = a₀a₀† ⊗ B − B` on the core. -/
private lemma numOp_comp_lift (B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) :
    (numOp (E := cfock (Excited m))).comp (lift B) = monoOp 1 1 B - monoOp 0 0 B := by
  rw [monoOp_one_one B, monoOp_zero_zero B, numOp, a0d_comp_a0, LinearMap.sub_comp,
    LinearMap.comp_assoc, one_comp_core]

/-- Pointwise form of `numOp_comp_lift`. -/
private lemma numOp_lift_apply (B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (v : FockCore (cfock (Excited m))) :
    numOp (lift B v) = (monoOp 1 1 B - monoOp 0 0 B) v := by
  rw [← LinearMap.comp_apply, numOp_comp_lift]

/-! ## The four `K**` operators of `Hnn` as scalar multiples of `Sn` -/

private lemma KnnA_eq (D : H2ndData m) :
    KnnA D = ((↑(D.ell ^ (-(3 : ℝ))) : ℂ) * (↑(D.W10) : ℂ)
      * (↑(D.ell ^ (-(3 : ℝ))) : ℂ)) • (Sn (m := m)) := by
  rw [KnnA, Sn, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp only [i3]
  push_cast
  ring

private lemma KnnB_eq (D : H2ndData m) :
    KnnB D = (-((↑(D.ell ^ (-(3 : ℝ))) : ℂ) + (↑(D.mu) : ℂ)) * (↑(D.W10) : ℂ)
      * (↑(D.ell ^ (-(3 : ℝ))) : ℂ)) • (Sn (m := m)) := by
  rw [KnnB, Sn, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp only [i3]
  push_cast
  ring

private lemma KnnC_eq (D : H2ndData m) :
    KnnC D = ((↑(D.ell ^ (-(3 : ℝ))) : ℂ) * (↑(D.W1omega0) : ℂ)
      * (↑(D.ell ^ (-(3 : ℝ))) : ℂ)) • (Sn (m := m)) := by
  rw [KnnC, Sn, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp only [i3]
  push_cast
  ring

private lemma KnnD_eq (D : H2ndData m) :
    KnnD D = (-((↑(D.ell ^ (-(3 : ℝ))) : ℂ) * (↑(D.W1omega0) : ℂ)
      * (↑(D.ell ^ (-(3 : ℝ))) : ℂ))) • (Sn (m := m)) := by
  rw [KnnD, Sn, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp only [i3]
  push_cast
  ring

/-! ## The two rows of `Hnn` -/

/-- The `Ŵ₁(0)` row of `Hnn`. -/

private lemma split_Hnn_row1 (D : H2ndData m) (x : RealFock m) :
    split (((D.ell ^ (-(3 : ℝ))) • Nmode - D.mu • 1)
        (((D.W10) • ((D.ell ^ (-(3 : ℝ))) • Sel)) x))
      = (monoOp 1 1 (KnnA D) + monoOp 0 0 (KnnB D)) (split x) := by
  have happ : ∀ z : RealFock m,
      ((D.ell ^ (-(3 : ℝ))) • Nmode - D.mu • 1) z
        = (D.ell ^ (-(3 : ℝ))) • (Nmode z) - D.mu • z := by
    intro z
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply]
  have hz : split (((D.W10) • ((D.ell ^ (-(3 : ℝ))) • Sel)) x)
      = ((↑(D.W10) : ℂ)) • ((↑(D.ell ^ (-(3 : ℝ))) : ℂ) • lift Sn (split x)) := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul, split_number_sum,
      real_smul_eq_coe_smul (E := FockCore (cfock (Excited m))), real_smul_eq_coe_smul (E := FockCore (cfock (Excited m)))]
  have hnum : numOp (split (((D.W10) • ((D.ell ^ (-(3 : ℝ))) • Sel)) x))
      = ((↑(D.W10) : ℂ)) • ((↑(D.ell ^ (-(3 : ℝ))) : ℂ) •
          (monoOp 1 1 Sn (split x) - lift Sn (split x))) := by
    rw [hz, map_smul, map_smul, numOp_lift_apply, LinearMap.sub_apply, monoOp_zero_zero]
  rw [happ, map_sub, map_smul, map_smul, split_numOp, hnum, hz,
    real_smul_eq_coe_smul (E := FockCore (cfock (Excited m))), real_smul_eq_coe_smul (E := FockCore (cfock (Excited m))), LinearMap.add_apply, KnnA_eq D, KnnB_eq D,
    monoOp_smul, monoOp_zero_zero, lift_smul, LinearMap.smul_apply, LinearMap.smul_apply]
  module

/-- The `Ŵ₁ω(0)` row of `Hnn`. -/

private lemma split_Hnn_row2 (D : H2ndData m) (x : RealFock m) :
    split (((D.ell ^ (-(3 : ℝ))) • Nmode)
        (((D.W1omega0) • ((D.ell ^ (-(3 : ℝ))) • Sel)) x))
      = (monoOp 1 1 (KnnC D) + monoOp 0 0 (KnnD D)) (split x) := by
  have happ : ∀ z : RealFock m,
      ((D.ell ^ (-(3 : ℝ))) • Nmode) z = (D.ell ^ (-(3 : ℝ))) • (Nmode z) := by
    intro z
    rw [LinearMap.smul_apply]
  have hz : split (((D.W1omega0) • ((D.ell ^ (-(3 : ℝ))) • Sel)) x)
      = ((↑(D.W1omega0) : ℂ)) • ((↑(D.ell ^ (-(3 : ℝ))) : ℂ) • lift Sn (split x)) := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul, split_number_sum,
      real_smul_eq_coe_smul (E := FockCore (cfock (Excited m))), real_smul_eq_coe_smul (E := FockCore (cfock (Excited m)))]
  have hnum : numOp (split (((D.W1omega0) • ((D.ell ^ (-(3 : ℝ))) • Sel)) x))
      = ((↑(D.W1omega0) : ℂ)) • ((↑(D.ell ^ (-(3 : ℝ))) : ℂ) •
          (monoOp 1 1 Sn (split x) - lift Sn (split x))) := by
    rw [hz, map_smul, map_smul, numOp_lift_apply, LinearMap.sub_apply, monoOp_zero_zero]
  rw [happ, map_smul, split_numOp, hnum,
    real_smul_eq_coe_smul (E := FockCore (cfock (Excited m))), LinearMap.add_apply, KnnC_eq D, KnnD_eq D, monoOp_smul,
    monoOp_zero_zero, lift_smul, LinearMap.smul_apply, LinearMap.smul_apply]
  module

theorem split_Hnn {m : ℕ} [NeZero m] (D : Work.BoseB4.H2ndData m) (x : Work.BoseB4.RealFock m) :
    Work.BoseB4.split (Work.BoseB4.Hnn D x)
      = (Work.BoseB4.monoOp 1 1 (Work.BoseB4.KnnA D)
          + Work.BoseB4.monoOp 0 0 (Work.BoseB4.KnnB D)
          + Work.BoseB4.monoOp 1 1 (Work.BoseB4.KnnC D)
          + Work.BoseB4.monoOp 0 0 (Work.BoseB4.KnnD D)) (Work.BoseB4.split x) := by
  rw [Hnn, show (∑ k ∈ exc m, (cre m k).comp (ann m k)) = Sel from rfl,
    show ((cre m 0).comp (ann m 0)) = Nmode from rfl]
  rw [LinearMap.add_apply]
  simp only [LinearMap.comp_apply]
  rw [map_add, split_Hnn_row1 D x, split_Hnn_row2 D x]
  simp only [LinearMap.add_apply]
  abel

end Work.BoseB4
