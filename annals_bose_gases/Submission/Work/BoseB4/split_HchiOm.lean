import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseB4.K2ndDefs
import Submission.Work.BoseB4.a0d_comp_a0
import Submission.Work.BoseB4.a0d_comp_a0_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.split_HchiOm` — the `χ̂_Λ^ω` row of FS `eq:HLambdaSecond` under `split`

The mode-lattice operator `HchiOm` of `Work.BoseB4.H2nd` is the `ω`-variant of the
linear (condensate) row of FS `eq:HLambdaSecond`,

    `(ℓ⁻³ a₀†a₀ W₁ω(0) χ̂_Λ) a_k† a₀ + h.c.`,

i.e. the sum of the two composites

    `A ∘ (W₁ω(0) Σ_k χ̂_Λ(k) cre k ∘ ann 0)`  and  `A ∘ (W₁ω(0) Σ_k χ̂_Λ(k) cre 0 ∘ ann k)`

with `A = ℓ⁻³ (cre 0 ∘ ann 0)` the condensate number operator times `ℓ⁻³`.  Under the
`⟨condensate | excited⟩` split of `Work.BoseB4.Split`, `ann 0 ↦ a₀`, `cre 0 ↦ a₀†` and
`cre k ↦ lift (creX k)` / `ann k ↦ lift (annX k)` (`Split_ann_zero`, `Split_cre_zero`,
`Split_ann_excited`, `Split_cre_excited`), so the first composite becomes
`ℓ⁻³ W₁ω(0) · lift B ∘ a₀† a₀ a₀` — which, by the canonical commutation relation
`[a₀, a₀†] = 1` (`Defs.ccr`), is the anti-normal monomial combination
`monoOp 2 1 B − 2 · monoOp 1 0 B`:

    `a₀† a₀ a₀ = a₀² a₀† − 2 a₀`,  resp.  `a₀† a₀ a₀† = a₀ (a₀†)² − a₀†`

(the identities `Work.BoseB4.a0d_comp_a0_sq` and `Work.BoseB4.a0d_comp_a0` of the
condensate ladder calculus), which is exactly the statement below with
`B = KchiOmA D`, `KchiOmB D`, `KchiOmC D`, `KchiOmD D` the `c`-number spectators of
`Work.BoseB4.K2ndDefs`.
-/

noncomputable section

open scoped lp BigOperators

namespace Work.BoseB4

set_option autoImplicit false
set_option maxHeartbeats 300000

variable {m : ℕ} [NeZero m]

/-! ## The `split` dictionary, pointwise

The four transport lemmas `Split_ann_zero`, `Split_cre_zero`, `Split_ann_excited`,
`Split_cre_excited` are stated as identities of operators composed with `split`; the
pointwise forms below are what the computation uses. -/

lemma split_ann_zero_apply (y : RealFock m) : split (ann m 0 y) = a0 (split y) := by
  have h := LinearMap.congr_fun (Split_ann_zero (m := m)) y
  simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] using h

lemma split_cre_zero_apply (y : RealFock m) : split (cre m 0 y) = a0d (split y) := by
  have h := LinearMap.congr_fun (Split_cre_zero (m := m)) y
  simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] using h

lemma split_ann_excited_apply (j : Excited m) (y : RealFock m) :
    split (ann m j.1 y) = lift (annC (Excited m) j) (split y) := by
  have h := LinearMap.congr_fun (Split_ann_excited (m := m) j) y
  simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] using h

lemma split_cre_excited_apply (j : Excited m) (y : RealFock m) :
    split (cre m j.1 y) = lift (creC (Excited m) j) (split y) := by
  have h := LinearMap.congr_fun (Split_cre_excited (m := m) j) y
  simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] using h

/-! ## The lattice operators `creX`, `annX` at a non-zero mode -/

lemma creX_eq_creC {k : Fin m} (hk : k ≠ 0) :
    creX m k = creC (Excited m) ⟨k, hk⟩ := by
  rw [creX, dif_neg hk]

lemma annX_eq_annC {k : Fin m} (hk : k ≠ 0) :
    annX m k = annC (Excited m) ⟨k, hk⟩ := by
  rw [annX, dif_neg hk]

/-! ## Composition with the identity -/

@[simp] lemma one_comp_lm {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (f : M →ₗ[ℂ] M) : (1 : M →ₗ[ℂ] M).comp f = f := by
  ext x
  simp

@[simp] lemma comp_one_lm {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (f : M →ₗ[ℂ] M) : f.comp (1 : M →ₗ[ℂ] M) = f := by
  ext x
  simp

/-! ## Scalar actions, made explicit

`split` is `ℝ`-linear and `lift B` is levelwise complex linear; the two smul
lemmas below keep the scalar type of every rewrite explicit (the generic
`map_smul` is ambiguous on a complex module regarded as a real one). -/

lemma split_map_smul (r : ℝ) (y : RealFock m) : split (r • y) = r • split y :=
  map_smul split r y

/-- The same, with the scalar written as a complex number. -/
lemma split_map_smul_c (r : ℝ) (y : RealFock m) :
    split (r • y) = (((r : ℝ) : ℂ)) • split y :=
  map_smul split r y

lemma lift_smul_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (r : ℝ) (B : E →ₗ[ℂ] E) : lift (r • B) = r • lift B :=
  lift_smul (((r : ℝ) : ℂ)) B

/-- The scalar extracted from a composite of two smul'd operators. -/
lemma comp_smul_pair {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (c w : ℝ) (T U : M →ₗ[ℝ] M) (y : M) :
    ((c • T).comp (w • U)) y = (c * w) • (T (U y)) := by
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_smul, mul_comm]

/-! ## Sums through `lift` -/

/-- `lift 0 = 0`. -/
@[simp] lemma lift_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    lift (0 : E →ₗ[ℂ] E) = 0 := by
  ext Ψ n
  simp

/-- `lift` is additive over a finite sum of spectators. -/
lemma lift_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}
    (s : Finset ι) (B : ι → E →ₗ[ℂ] E) :
    lift (∑ i ∈ s, B i) = ∑ i ∈ s, lift (B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, lift_add, ih]

/-- The scalar `χ̂_Λ(k)` may be moved under the `lift`. -/
lemma lift_sum_creX (D : H2ndData m) :
    (∑ k ∈ exc m, D.chiHat k • lift (creX m k))
      = lift (∑ k ∈ exc m, D.chiHat k • creX m k) := by
  rw [lift_sum]
  exact Finset.sum_congr rfl fun k _ => (lift_smul_left (D.chiHat k) (creX m k)).symm

/-- The scalar `χ̂_Λ(k)` may be moved under the `lift`, `annX` version. -/
lemma lift_sum_annX (D : H2ndData m) :
    (∑ k ∈ exc m, D.chiHat k • lift (annX m k))
      = lift (∑ k ∈ exc m, D.chiHat k • annX m k) := by
  rw [lift_sum]
  exact Finset.sum_congr rfl fun k _ => (lift_smul_left (D.chiHat k) (annX m k)).symm

/-- Pulling a real scalar through `a₀†`. -/
lemma a0d_real_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (r : ℝ) (z : FockCore E) : a0d (r • z) = r • a0d z :=
  map_smul a0d (((r : ℝ) : ℂ)) z

/-- Pulling a real scalar through `a₀`. -/
lemma a0_real_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (r : ℝ) (z : FockCore E) : a0 (r • z) = r • a0 z :=
  map_smul a0 (((r : ℝ) : ℂ)) z

/-! ## The two transports of the `χ̂_Λ^ω` row -/

/-- The `cre k ∘ ann 0` half of the row: under `split`, `Σ_k χ̂_Λ(k) cre k ∘ ann 0`
becomes `lift (Σ_k χ̂_Λ(k) creX k) ∘ a₀`. -/
lemma split_sum_cre_ann (D : H2ndData m) (y : RealFock m) :
    split ((∑ k ∈ exc m, D.chiHat k • ((cre m k).comp (ann m 0))) y)
      = lift (∑ k ∈ exc m, D.chiHat k • creX m k) (a0 (split y)) := by
  rw [LinearMap.sum_apply, map_sum]
  trans ∑ k ∈ exc m, D.chiHat k • (lift (creX m k) (a0 (split y)))
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
    rw [LinearMap.smul_apply, LinearMap.comp_apply, split_map_smul,
      split_cre_excited_apply ⟨k, hk0⟩, ← creX_eq_creC hk0, split_ann_zero_apply]
  · rw [← lift_sum_creX D, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ =>
      (LinearMap.smul_apply (D.chiHat k) (lift (creX m k)) (a0 (split y))).symm

/-- The `cre 0 ∘ ann k` half of the row: under `split`,
`Σ_k χ̂_Λ(k) cre 0 ∘ ann k` becomes `a₀† ∘ lift (Σ_k χ̂_Λ(k) annX k)`. -/
lemma split_sum_cre0_ann (D : H2ndData m) (y : RealFock m) :
    split ((∑ k ∈ exc m, D.chiHat k • ((cre m 0).comp (ann m k))) y)
      = a0d (lift (∑ k ∈ exc m, D.chiHat k • annX m k) (split y)) := by
  rw [LinearMap.sum_apply, map_sum]
  trans ∑ k ∈ exc m, D.chiHat k • a0d (lift (annX m k) (split y))
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
    rw [LinearMap.smul_apply, LinearMap.comp_apply, split_map_smul, split_cre_zero_apply,
      split_ann_excited_apply ⟨k, hk0⟩, ← annX_eq_annC hk0]
  · rw [← lift_sum_annX D, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.smul_apply]
    exact (a0d_real_smul (D.chiHat k) (lift (annX m k) (split y))).symm

/-! ## The abstract ladder identities with `lift` on the outside -/

/-- `lift A` commutes with `a₀ ∘ a₀`. -/
lemma lift_comp_a0_a0 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ[ℂ] E) : (lift A).comp (a0.comp a0) = (a0.comp a0).comp (lift A) := by
  rw [← LinearMap.comp_assoc, lift_comm_a0, LinearMap.comp_assoc, lift_comm_a0,
    ← LinearMap.comp_assoc]

/-- `lift A` commutes with `a₀ ∘ a₀†`. -/
lemma lift_comp_a0_a0d {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ[ℂ] E) : (lift A).comp (a0.comp a0d) = (a0.comp a0d).comp (lift A) := by
  rw [← LinearMap.comp_assoc, lift_comm_a0, LinearMap.comp_assoc, lift_comm_a0d,
    ← LinearMap.comp_assoc]

lemma monoOp_two_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ[ℂ] E) :
    monoOp 2 1 A = (a0.comp a0).comp (a0d.comp (lift A)) := by
  simp [monoOp, a0pow_succ, one_comp_lm]

lemma monoOp_one_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ[ℂ] E) : monoOp 1 0 A = a0.comp (lift A) := by
  simp [monoOp, a0pow_succ, one_comp_lm]

lemma monoOp_one_two {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ[ℂ] E) :
    monoOp 1 2 A = a0.comp ((a0d.comp a0d).comp (lift A)) := by
  simp [monoOp, a0dpow_succ, one_comp_lm]

lemma monoOp_zero_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ[ℂ] E) : monoOp 0 1 A = a0d.comp (lift A) := by
  simp [monoOp, a0dpow_succ, one_comp_lm]

/-- **`a₀† a₀ a₀ = a₀² a₀† − 2 a₀`** with the spectator inserted: the anti-normal
reordering of the composite `a₀† ∘ a₀ ∘ a₀` (the `lift A` commutes with both `a₀`
and `a₀†`, so it may be placed on the outside). -/
lemma a0d_a0_a0_lift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ[ℂ] E) :
    (lift A).comp (a0d.comp (a0.comp a0))
      = monoOp 2 1 A - (2 : ℂ) • monoOp 1 0 A := by
  have h := a0d_comp_a0_sq (E := E)
  calc (lift A).comp (a0d.comp (a0.comp a0))
      = ((lift A).comp a0d).comp (a0.comp a0) :=
        (LinearMap.comp_assoc _ _ _).symm
    _ = (a0d.comp (lift A)).comp (a0.comp a0) := by rw [lift_comm_a0d]
    _ = a0d.comp ((lift A).comp (a0.comp a0)) := LinearMap.comp_assoc _ _ _
    _ = a0d.comp ((a0.comp a0).comp (lift A)) := by rw [lift_comp_a0_a0]
    _ = (a0d.comp (a0.comp a0)).comp (lift A) :=
        (LinearMap.comp_assoc _ _ _).symm
    _ = ((a0.comp a0).comp a0d - (2 : ℂ) • a0).comp (lift A) := by rw [h]
    _ = ((a0.comp a0).comp a0d).comp (lift A) - (2 : ℂ) • (a0.comp (lift A)) := by
        rw [LinearMap.sub_comp, LinearMap.smul_comp]
    _ = monoOp 2 1 A - (2 : ℂ) • monoOp 1 0 A := by
        rw [monoOp_two_one, monoOp_one_zero, LinearMap.comp_assoc]

/-- **`a₀† a₀ a₀† = a₀ (a₀†)² − a₀†`** with the spectator inserted. -/
lemma a0d_a0_a0d_lift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ[ℂ] E) :
    (lift A).comp (a0d.comp (a0.comp a0d))
      = monoOp 1 2 A - monoOp 0 1 A := by
  have h : (a0d : FockCore E →ₗ[ℂ] FockCore E).comp (a0.comp a0d)
      = (a0.comp (a0d.comp a0d)) - (a0d : FockCore E →ₗ[ℂ] FockCore E) := by
    calc a0d.comp (a0.comp a0d) = (a0d.comp a0).comp a0d :=
          (LinearMap.comp_assoc _ _ _).symm
      _ = (a0.comp a0d - 1).comp a0d := by rw [a0d_comp_a0 (E := E)]
      _ = (a0.comp a0d).comp a0d - (1 : FockCore E →ₗ[ℂ] FockCore E).comp a0d := by
          rw [LinearMap.sub_comp]
      _ = a0.comp (a0d.comp a0d) - a0d := by
          rw [LinearMap.comp_assoc, one_comp_lm]
  calc (lift A).comp (a0d.comp (a0.comp a0d))
      = ((lift A).comp a0d).comp (a0.comp a0d) :=
        (LinearMap.comp_assoc _ _ _).symm
    _ = (a0d.comp (lift A)).comp (a0.comp a0d) := by rw [lift_comm_a0d]
    _ = a0d.comp ((lift A).comp (a0.comp a0d)) := LinearMap.comp_assoc _ _ _
    _ = a0d.comp ((a0.comp a0d).comp (lift A)) := by rw [lift_comp_a0_a0d]
    _ = (a0d.comp (a0.comp a0d)).comp (lift A) :=
        (LinearMap.comp_assoc _ _ _).symm
    _ = (a0.comp (a0d.comp a0d) - a0d).comp (lift A) := by rw [h]
    _ = (a0.comp (a0d.comp a0d)).comp (lift A) - a0d.comp (lift A) := by
        rw [LinearMap.sub_comp]
    _ = monoOp 1 2 A - monoOp 0 1 A := by
        rw [monoOp_one_two, monoOp_zero_one, LinearMap.comp_assoc]

/-! ## The `c`-number spectators of the two halves -/

/-- The spectator `Σ_k χ̂_Λ(k) creX k` of the `a_k† a₀` half. -/
noncomputable def chiXsum (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, (((D.chiHat k : ℝ) : ℂ)) • creX m k

/-- The spectator `Σ_k χ̂_Λ(k) annX k` of the `a_k a₀†` half. -/
noncomputable def chiAsum (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, (((D.chiHat k : ℝ) : ℂ)) • annX m k

lemma split_sum_cre_ann' (D : H2ndData m) (y : RealFock m) :
    split ((∑ k ∈ exc m, D.chiHat k • ((cre m k).comp (ann m 0))) y)
      = lift (chiXsum D) (a0 (split y)) := by
  rw [chiXsum]
  exact split_sum_cre_ann D y

lemma split_sum_cre0_ann' (D : H2ndData m) (y : RealFock m) :
    split ((∑ k ∈ exc m, D.chiHat k • ((cre m 0).comp (ann m k))) y)
      = a0d (lift (chiAsum D) (split y)) := by
  rw [chiAsum]
  exact split_sum_cre0_ann D y

/-! ## The coefficient bookkeeping -/

/-- A real scalar acting on a complex module is the complex scalar of its image. -/
lemma real_smul_eq_complex_smul {M : Type*} [AddCommGroup M] [Module ℂ M] (r : ℝ) (x : M) :
    r • x = (((r : ℝ) : ℂ)) • x := rfl

lemma complex_smul_eq_real_smul {M : Type*} [AddCommGroup M] [Module ℂ M] (r : ℝ) (x : M) :
    (((r : ℝ) : ℂ)) • x = r • x := rfl

lemma KchiOmA_eq_smul (D : H2ndData m) :
    KchiOmA D = (((D.ell ^ (-(3:ℝ)) * D.W1omega0 : ℝ) : ℂ)) • chiXsum D := by
  rw [KchiOmA, chiXsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show i3 D = D.ell ^ (-(3:ℝ)) from rfl, smul_smul, ← Complex.ofReal_mul]

lemma KchiOmB_eq_smul (D : H2ndData m) :
    KchiOmB D = (((-(2 * (D.ell ^ (-(3:ℝ)) * D.W1omega0)) : ℝ) : ℂ)) • chiXsum D := by
  rw [KchiOmB, chiXsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show i3 D = D.ell ^ (-(3:ℝ)) from rfl, smul_smul, ← Complex.ofReal_mul]
  congr 1
  push_cast
  ring

lemma KchiOmC_eq_smul (D : H2ndData m) :
    KchiOmC D = (((D.ell ^ (-(3:ℝ)) * D.W1omega0 : ℝ) : ℂ)) • chiAsum D := by
  rw [KchiOmC, chiAsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show i3 D = D.ell ^ (-(3:ℝ)) from rfl, smul_smul, ← Complex.ofReal_mul]

lemma KchiOmD_eq_smul (D : H2ndData m) :
    KchiOmD D = (((-(D.ell ^ (-(3:ℝ)) * D.W1omega0) : ℝ) : ℂ)) • chiAsum D := by
  rw [KchiOmD, chiAsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show i3 D = D.ell ^ (-(3:ℝ)) from rfl, smul_smul, ← Complex.ofReal_mul]
  congr 1
  push_cast
  ring

/-! ## Distributing a real scalar over the anti-normal monomials -/

/-- `B ↦ monoOp p q B` as a linear map: the anti-normal monomials are linear in the
spectator operator (`monoOp_add`, `monoOp_smul`). -/
noncomputable def monoOpLM {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (p q : ℕ) : (E →ₗ[ℂ] E) →ₗ[ℂ] (FockCore E →ₗ[ℂ] FockCore E) where
  toFun := monoOp p q
  map_add' := monoOp_add p q
  map_smul' := monoOp_smul p q

lemma smul_monoOp_diff_map {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (r : ℝ) (A : E →ₗ[ℂ] E) :
    (((r : ℝ) : ℂ)) • (monoOp 2 1 A - (2 : ℂ) • monoOp 1 0 A)
      = monoOp 2 1 (((r : ℝ) : ℂ) • A)
        + monoOp 1 0 ((((-(2 * r) : ℝ) : ℂ)) • A) := by
  have h2 : monoOp 2 1 (((r : ℝ) : ℂ) • A) = (((r : ℝ) : ℂ)) • monoOp 2 1 A :=
    map_smul (monoOpLM 2 1) (((r : ℝ) : ℂ)) A
  have h1 : monoOp 1 0 ((((-(2 * r) : ℝ) : ℂ)) • A)
      = (((-(2 * r) : ℝ) : ℂ)) • monoOp 1 0 A :=
    map_smul (monoOpLM 1 0) (((-(2 * r) : ℝ) : ℂ)) A
  have hs : (((-(2 * r) : ℝ) : ℂ)) = -(((r : ℝ) : ℂ) * 2) := by push_cast; ring
  rw [h2, h1, hs, smul_sub, smul_smul, sub_eq_add_neg, ← neg_smul]

lemma smul_monoOp_diff_map2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (r : ℝ) (A : E →ₗ[ℂ] E) :
    (((r : ℝ) : ℂ)) • (monoOp 1 2 A - monoOp 0 1 A)
      = monoOp 1 2 (((r : ℝ) : ℂ) • A)
        + monoOp 0 1 ((((-r : ℝ) : ℂ)) • A) := by
  have h2 : monoOp 1 2 (((r : ℝ) : ℂ) • A) = (((r : ℝ) : ℂ)) • monoOp 1 2 A :=
    map_smul (monoOpLM 1 2) (((r : ℝ) : ℂ)) A
  have h1 : monoOp 0 1 ((((-r : ℝ) : ℂ)) • A) = ((((-r : ℝ) : ℂ))) • monoOp 0 1 A :=
    map_smul (monoOpLM 0 1) (((-r : ℝ) : ℂ)) A
  have hs : ((((-r : ℝ) : ℂ))) = -(((r : ℝ) : ℂ)) := by push_cast; ring
  rw [h2, h1, hs, smul_sub, sub_eq_add_neg, ← neg_smul]

/-! ## The two halves of the `χ̂_Λ^ω` row -/

/-- The `a_k† a₀` half of `HchiOm`: it produces the `(2,1)` and `(1,0)` slots. -/
lemma split_HchiOm_first (D : H2ndData m) (x : RealFock m) :
    split ((((D.ell ^ (-(3:ℝ))) • ((cre m 0).comp (ann m 0))).comp
        (D.W1omega0 • ∑ k ∈ exc m, D.chiHat k • ((cre m k).comp (ann m 0)))) x)
      = (monoOp 2 1 (KchiOmA D) + monoOp 1 0 (KchiOmB D)) (split x) := by
  set N0 : RealFock m →ₗ[ℝ] RealFock m := (cre m 0).comp (ann m 0) with hN0
  set S1 : RealFock m →ₗ[ℝ] RealFock m :=
    ∑ k ∈ exc m, D.chiHat k • ((cre m k).comp (ann m 0)) with hS1
  have step1 : (((D.ell ^ (-(3:ℝ))) • N0).comp (D.W1omega0 • S1)) x
      = (D.ell ^ (-(3:ℝ)) * D.W1omega0) • (N0 (S1 x)) :=
    comp_smul_pair _ _ N0 S1 x
  have step2 : split (N0 (S1 x)) = a0d (a0 (split (S1 x))) := by
    rw [hN0, LinearMap.comp_apply, split_cre_zero_apply, split_ann_zero_apply]
  have step3 : split (S1 x) = lift (chiXsum D) (a0 (split x)) := by
    rw [hS1]
    exact split_sum_cre_ann' D x
  have step4 : a0d (a0 (lift (chiXsum D) (a0 (split x))))
      = (monoOp 2 1 (chiXsum D) - (2 : ℂ) • monoOp 1 0 (chiXsum D)) (split x) := by
    have h1 : a0 (lift (chiXsum D) (a0 (split x)))
        = lift (chiXsum D) (a0 (a0 (split x))) :=
      (LinearMap.congr_fun (lift_comm_a0 (chiXsum D)) (a0 (split x))).symm
    have h2 : a0d (lift (chiXsum D) (a0 (a0 (split x))))
        = lift (chiXsum D) (a0d (a0 (a0 (split x)))) :=
      (LinearMap.congr_fun (lift_comm_a0d (chiXsum D)) (a0 (a0 (split x)))).symm
    rw [h1, h2]
    have h3 := LinearMap.congr_fun
      (a0d_a0_a0_lift (E := cfock (Excited m)) (chiXsum D)) (split x)
    simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply] using h3
  have hdiff := smul_monoOp_diff_map (E := cfock (Excited m))
    (D.ell ^ (-(3:ℝ)) * D.W1omega0) (chiXsum D)
  rw [step1, split_map_smul_c, step2, step3, step4, LinearMap.add_apply,
    ← LinearMap.smul_apply, hdiff, LinearMap.add_apply,
    ← KchiOmA_eq_smul D, ← KchiOmB_eq_smul D]

/-- The `a_k a₀†` half of `HchiOm`: it produces the `(1,2)` and `(0,1)` slots. -/
lemma split_HchiOm_second (D : H2ndData m) (x : RealFock m) :
    split ((((D.ell ^ (-(3:ℝ))) • ((cre m 0).comp (ann m 0))).comp
        (D.W1omega0 • ∑ k ∈ exc m, D.chiHat k • ((cre m 0).comp (ann m k)))) x)
      = (monoOp 1 2 (KchiOmC D) + monoOp 0 1 (KchiOmD D)) (split x) := by
  set N0 : RealFock m →ₗ[ℝ] RealFock m := (cre m 0).comp (ann m 0) with hN0
  set S2 : RealFock m →ₗ[ℝ] RealFock m :=
    ∑ k ∈ exc m, D.chiHat k • ((cre m 0).comp (ann m k)) with hS2
  have step1 : (((D.ell ^ (-(3:ℝ))) • N0).comp (D.W1omega0 • S2)) x
      = (D.ell ^ (-(3:ℝ)) * D.W1omega0) • (N0 (S2 x)) :=
    comp_smul_pair _ _ N0 S2 x
  have step2 : split (N0 (S2 x)) = a0d (a0 (split (S2 x))) := by
    rw [hN0, LinearMap.comp_apply, split_cre_zero_apply, split_ann_zero_apply]
  have step3 : split (S2 x) = a0d (lift (chiAsum D) (split x)) := by
    rw [hS2]
    exact split_sum_cre0_ann' D x
  have step4 : a0d (a0 (a0d (lift (chiAsum D) (split x))))
      = (monoOp 1 2 (chiAsum D) - monoOp 0 1 (chiAsum D)) (split x) := by
    have h1 : a0d (lift (chiAsum D) (split x)) = lift (chiAsum D) (a0d (split x)) :=
      (LinearMap.congr_fun (lift_comm_a0d (chiAsum D)) (split x)).symm
    have h2 : a0 (lift (chiAsum D) (a0d (split x)))
        = lift (chiAsum D) (a0 (a0d (split x))) :=
      (LinearMap.congr_fun (lift_comm_a0 (chiAsum D)) (a0d (split x))).symm
    have h3 : a0d (lift (chiAsum D) (a0 (a0d (split x))))
        = lift (chiAsum D) (a0d (a0 (a0d (split x)))) :=
      (LinearMap.congr_fun (lift_comm_a0d (chiAsum D)) (a0 (a0d (split x)))).symm
    rw [h1, h2, h3]
    have h4 := LinearMap.congr_fun
      (a0d_a0_a0d_lift (E := cfock (Excited m)) (chiAsum D)) (split x)
    simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply] using h4
  have hdiff := smul_monoOp_diff_map2 (E := cfock (Excited m))
    (D.ell ^ (-(3:ℝ)) * D.W1omega0) (chiAsum D)
  rw [step1, split_map_smul_c, step2, step3, step4, LinearMap.add_apply,
    ← LinearMap.smul_apply, hdiff, LinearMap.add_apply,
    ← KchiOmC_eq_smul D, ← KchiOmD_eq_smul D]

theorem split_HchiOm {m : ℕ} [NeZero m] (D : Work.BoseB4.H2ndData m) (x : Work.BoseB4.RealFock m) :
    Work.BoseB4.split (Work.BoseB4.HchiOm D x)
      = (Work.BoseB4.monoOp 2 1 (Work.BoseB4.KchiOmA D)
          + Work.BoseB4.monoOp 1 0 (Work.BoseB4.KchiOmB D)
          + Work.BoseB4.monoOp 1 2 (Work.BoseB4.KchiOmC D)
          + Work.BoseB4.monoOp 0 1 (Work.BoseB4.KchiOmD D)) (Work.BoseB4.split x) := by
  rw [HchiOm, LinearMap.add_apply, map_add, split_HchiOm_first D x, split_HchiOm_second D x]
  simp only [LinearMap.add_apply]
  abel

end Work.BoseB4


