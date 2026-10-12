import Mathlib
import Submission.Work.BoseB4.K2ndDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.split_HW` — the `a₀†a_k†a_k a₀` row of FS `eq:HLambdaSecond` under `split`

The mode lattice `RealFock m = (Fin m →₀ ℕ) →₀ ℝ` splits, through the `ℝ`-linear
isometry `Work.BoseB4.split`, as `𝔉(ℂθ) ⊗ 𝔉(excited)`:
the basis multi-index `α` is sent to the Fock weight `√((α 0)! · (α|_{j≠0})!)`
times the pair `(α 0, α|_{j≠0})`.  Under it the lattice operators correspond to the
abstract ones (`Split_ann_zero`, `Split_cre_zero`, `Split_ann_excited`,
`Split_cre_excited`):

    split ∘ ann m 0   = a0 ∘ split,             split ∘ cre m 0 = a0d ∘ split,
    split ∘ ann m j   = lift (annC j) ∘ split   (j ≠ 0),
    split ∘ cre m j   = lift (creC j) ∘ split   (j ≠ 0).

This module transports the **`a₀†a_k†a_k a₀` row** of FS's second-quantised box
Hamiltonian, i.e. the `Work.BoseB4.HW D = Σ_k (Ŵ₁(k)+Ŵ₁ω(k)) a₀†a_k†a_k a₀` part of
`Work.BoseB4.H2nd`, into the anti-normal slots of `Work.BoseB4.K2ndDefs`:

    split (HW D x)
      = (monoOp 1 1 (KHW1 D) + monoOp 0 0 (KHW2 D)) (split x).

## How it goes

For a fixed excited mode `k ≠ 0` the word `cre m 0 ∘ cre m k ∘ ann m k ∘ ann m 0`
transports — by the four dictionary lemmas, the fact that `lift` commutes with
`a0` (`lift_comm_a0`) and that `lift` turns composition into composition
(`lift_comp`) — to

    a0d ∘ lift (creC k) ∘ lift (annC k) ∘ a0 = numOp ∘ lift (CX k),

which is the per-mode identity `splitHW_mode`.  Summing it against the coefficients
`Ŵ₁(k)+Ŵ₁ω(k)` gives, for the right-hand side of the target, the sum
`Σ_k (Ŵ₁(k)+Ŵ₁ω(k)) · numOp (lift (CX k) ·)` — because the two anti-normal slots
collapse: `KHW2 D = −KHW1 D` (`splitHW_KHW2`) and

    monoOp 1 1 A + monoOp 0 0 (−A) = numOp ∘ lift A      (`splitHW_monoOp_11_00`),

which is `[a₀,a₀†] = 1` (`ccr`) rewritten: `a₀a₀† − 1 = a₀†a₀ = n₀`.

Everything here is `sorry`-free and rests only on the already-proved modules
`Defs`, `CFock`, `Split`, `Split_ann_zero`, `Split_cre_zero`, `Split_ann_excited`,
`Split_cre_excited` (all reached through `K2ndDefs`).
-/

noncomputable section

open scoped lp BigOperators

namespace Work.BoseB4

set_option autoImplicit false

variable {m : ℕ} [NeZero m]

/-! ## The dictionary in applied form

The four transport lemmas `Split_*` are stated as identities of `ℝ`-linear maps;
below we record their applied form, which is what the computations use. -/

/-- The condensate annihilation of the mode lattice corresponds to `a0`:
applied form of `Work.BoseB4.Split_ann_zero`. -/
lemma splitHW_ann_zero_apply (v : RealFock m) : split (ann m 0 v) = a0 (split v) := by
  have h := DFunLike.congr_fun (Split_ann_zero (m := m)) v
  simpa [LinearMap.comp_apply] using h

/-- The condensate creation of the mode lattice corresponds to `a0d`:
applied form of `Work.BoseB4.Split_cre_zero`. -/
lemma splitHW_cre_zero_apply (v : RealFock m) : split (cre m 0 v) = a0d (split v) := by
  have h := DFunLike.congr_fun (Split_cre_zero (m := m)) v
  simpa [LinearMap.comp_apply] using h

/-- The lattice annihilation of an excited mode corresponds to `lift (annC ·)`:
applied form of `Work.BoseB4.Split_ann_excited`. -/
lemma splitHW_ann_excited_apply (j : Excited m) (v : RealFock m) :
    split (ann m j.1 v) = lift (annC (Excited m) j) (split v) := by
  have h := DFunLike.congr_fun (Split_ann_excited (m := m) j) v
  simpa [LinearMap.comp_apply] using h

/-- The lattice creation of an excited mode corresponds to `lift (creC ·)`:
applied form of `Work.BoseB4.Split_cre_excited`. -/
lemma splitHW_cre_excited_apply (j : Excited m) (v : RealFock m) :
    split (cre m j.1 v) = lift (creC (Excited m) j) (split v) := by
  have h := DFunLike.congr_fun (Split_cre_excited (m := m) j) v
  simpa [LinearMap.comp_apply] using h

/-- `lift` commutes with the condensate annihilation `a0` (applied form). -/
lemma splitHW_lift_a0 (B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (v : FockCore (cfock (Excited m))) : lift B (a0 v) = a0 (lift B v) :=
  DFunLike.congr_fun (lift_comm_a0 B) v

/-- `lift` turns composition of spectators into composition (applied form). -/
lemma splitHW_lift_lift (B B' : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (v : FockCore (cfock (Excited m))) : lift B (lift B' v) = lift (B.comp B') v :=
  (DFunLike.congr_fun (lift_comp B B') v).symm

/-- The excited-mode number operator `CX k` in the abstract picture: for `k ≠ 0`,
`CX k = creC k ∘ annC k`. -/
lemma splitHW_CX_eq_of_ne (k : Fin m) (hk : k ≠ 0) :
    CX k = (creC (Excited m) ⟨k, hk⟩).comp (annC (Excited m) ⟨k, hk⟩) := by
  rw [CX, annX, creX, dif_neg hk, dif_neg hk]

/-! ## The per-mode identity -/

/-- **The `a₀†a_k†a_k a₀` word transported**: for an excited mode `k ≠ 0`, the
lattice word `cre m 0 ∘ cre m k ∘ ann m k ∘ ann m 0` corresponds under `split` to
`numOp ∘ lift (CX k)`. -/
lemma splitHW_mode (k : Fin m) (hk : k ≠ 0) (x : RealFock m) :
    split (((cre m 0).comp ((cre m k).comp ((ann m k).comp (ann m 0)))) x)
      = numOp (lift (CX k) (split x)) := by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  have hliftA : lift (annC (Excited m) ⟨k, hk⟩) (a0 (split x))
      = a0 (lift (annC (Excited m) ⟨k, hk⟩) (split x)) := splitHW_lift_a0 _ _
  have hliftC : lift (creC (Excited m) ⟨k, hk⟩)
        (a0 (lift (annC (Excited m) ⟨k, hk⟩) (split x)))
      = a0 (lift (creC (Excited m) ⟨k, hk⟩)
          (lift (annC (Excited m) ⟨k, hk⟩) (split x))) := splitHW_lift_a0 _ _
  have hcomp : lift (creC (Excited m) ⟨k, hk⟩)
        (lift (annC (Excited m) ⟨k, hk⟩) (split x))
      = lift ((creC (Excited m) ⟨k, hk⟩).comp (annC (Excited m) ⟨k, hk⟩)) (split x) :=
    splitHW_lift_lift _ _ _
  calc split (cre m 0 (cre m k (ann m k (ann m 0 x))))
      = a0d (split (cre m k (ann m k (ann m 0 x)))) := splitHW_cre_zero_apply _
    _ = a0d (lift (creC (Excited m) ⟨k, hk⟩) (split (ann m k (ann m 0 x)))) := by
          rw [splitHW_cre_excited_apply ⟨k, hk⟩]
    _ = a0d (lift (creC (Excited m) ⟨k, hk⟩)
            (lift (annC (Excited m) ⟨k, hk⟩) (split (ann m 0 x)))) := by
          rw [splitHW_ann_excited_apply ⟨k, hk⟩]
    _ = a0d (lift (creC (Excited m) ⟨k, hk⟩)
            (lift (annC (Excited m) ⟨k, hk⟩) (a0 (split x)))) := by
          rw [splitHW_ann_zero_apply]
    _ = a0d (lift (creC (Excited m) ⟨k, hk⟩)
            (a0 (lift (annC (Excited m) ⟨k, hk⟩) (split x)))) := by
          rw [hliftA]
    _ = a0d (a0 (lift (creC (Excited m) ⟨k, hk⟩)
            (lift (annC (Excited m) ⟨k, hk⟩) (split x)))) := by
          rw [hliftC]
    _ = a0d (a0 (lift ((creC (Excited m) ⟨k, hk⟩).comp (annC (Excited m) ⟨k, hk⟩))
            (split x))) := by
          rw [hcomp]
    _ = numOp (lift (CX k) (split x)) := by rw [splitHW_CX_eq_of_ne k hk]; rfl

/-! ## The two anti-normal slots collapse -/

/-- **`monoOp 1 1 A + monoOp 0 0 (−A) = numOp ∘ lift A`** — the anti-normal form of
`[a₀,a₀†] = 1`: `a₀a₀† − 1 = a₀†a₀ = n₀`. -/
lemma splitHW_monoOp_11_00 (A : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (y : FockCore (cfock (Excited m))) :
    (monoOp 1 1 A + monoOp 0 0 (-A)) y = numOp (lift A y) := by
  show (monoOp 1 1 A + monoOp 0 0 (-A)) y = a0d (a0 (lift A y))
  simp only [monoOp, a0pow_succ, a0dpow_succ, a0pow_zero, a0dpow_zero, Module.End.one_eq_id,
    LinearMap.id_comp, LinearMap.comp_apply, LinearMap.add_apply]
  have hliftneg : lift (-A) y = -(lift A y) := by
    have h : lift (-A) = -lift A := by
      rw [← neg_one_smul ℂ A, lift_smul]
      exact neg_one_smul ℂ (lift A)
    rw [h, LinearMap.neg_apply]
  have hccr : a0 (a0d (lift A y)) = a0d (a0 (lift A y)) + lift A y := by
    have h := DFunLike.congr_fun (ccr (E := cfock (Excited m))) (lift A y)
    simpa [LinearMap.comp_apply] using h
  rw [hliftneg, hccr, add_assoc, add_neg_cancel, add_zero]

/-- `KHW2 D = −KHW1 D`: the two spectator operators of the `a₀†a_k†a_k a₀` row carry
opposite coefficients, so their anti-normal slots cancel. -/
lemma splitHW_KHW2 (D : H2ndData m) : KHW2 D = -KHW1 D := by
  rw [KHW2, KHW1]
  refine (Finset.sum_congr rfl fun k _ => ?_).trans (Finset.sum_neg_distrib (f := fun k => ((D.W1 k + D.W1omega k : ℝ) : ℂ) • CX k))
  rw [Complex.ofReal_neg]
  exact neg_smul (↑(D.W1 k + D.W1omega k) : ℂ) (CX k)

/-! ## The row -/

/-- **The `a₀†a_k†a_k a₀` row of FS `eq:HLambdaSecond` under the split**: the
mode-lattice operator `Work.BoseB4.HW D = Σ_k (Ŵ₁(k)+Ŵ₁ω(k)) a₀†a_k†a_k a₀`
corresponds to the anti-normal pair of slots `(1,1)` and `(0,0)` with spectator
operators `KHW1 D` and `KHW2 D`. -/
theorem split_HW {m : ℕ} [NeZero m] (D : Work.BoseB4.H2ndData m) (x : Work.BoseB4.RealFock m) :
    Work.BoseB4.split (Work.BoseB4.HW D x)
      = (Work.BoseB4.monoOp 1 1 (Work.BoseB4.KHW1 D)
          + Work.BoseB4.monoOp 0 0 (Work.BoseB4.KHW2 D)) (Work.BoseB4.split x) := by
  -- the per-mode identity, upgraded to the whole finite sum over the excited modes
  have hstep : ∀ k ∈ exc m,
      split (((cre m 0).comp ((cre m k).comp ((ann m k).comp (ann m 0)))) x)
        = numOp (lift (CX k) (split x)) := by
    intro k hk
    have hk0 : k ≠ 0 := by
      have h : k ∈ Finset.univ.erase (0 : Fin m) := by simpa [exc] using hk
      exact (Finset.mem_erase.mp h).1
    exact splitHW_mode k hk0 x
  have hL : split (HW D x)
      = ∑ k ∈ exc m, (D.W1 k + D.W1omega k) •
          split (((cre m 0).comp ((cre m k).comp ((ann m k).comp (ann m 0)))) x) := by
    rw [HW]
    simp only [LinearMap.sum_apply, map_sum, map_smul, LinearMap.smul_apply]
  have hL2 : split (HW D x)
      = ∑ k ∈ exc m, (D.W1 k + D.W1omega k) • numOp (lift (CX k) (split x)) := by
    rw [hL]
    exact Finset.sum_congr rfl fun k hk => by rw [hstep k hk]
  -- the right-hand side, collapsed to `numOp ∘ lift (KHW1 D)`
  have hR : (monoOp 1 1 (KHW1 D) + monoOp 0 0 (KHW2 D)) (split x)
      = numOp (lift (KHW1 D) (split x)) := by
    rw [splitHW_KHW2]
    exact splitHW_monoOp_11_00 (KHW1 D) (split x)
  -- and expanded mode by mode
  have hNum : numOp (lift (KHW1 D) (split x))
      = ∑ k ∈ exc m, (((D.W1 k + D.W1omega k : ℝ)) : ℂ) •
          numOp (lift (CX k) (split x)) := by
    have hLift : lift (KHW1 D) (split x)
        = ∑ k ∈ exc m, (((D.W1 k + D.W1omega k : ℝ)) : ℂ) • lift (CX k) (split x) := by
      refine Finsupp.ext fun n => ?_
      simp only [KHW1, lift_apply, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply',
        Finsupp.smul_apply]
    rw [hLift, map_sum]
    simp only [map_smul]
  rw [hR, hNum, hL2]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (Complex.coe_smul (E := FockCore (cfock (Excited m))) (D.W1 k + D.W1omega k) _).symm

end Work.BoseB4
