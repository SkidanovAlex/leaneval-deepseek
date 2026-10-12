import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseBoxFock.KafzHonest
import Submission.Work.BoseBoxFock.monoOp_sum_real_smul
import Submission.Work.BoseBoxFock.split_L0_row1_core
import Submission.Work.BoseBoxFock.split_L0_row2_core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.kf_HchiGen` — the `Hchi` row of FS `eq:HLambdaSecond`, summed

FS `eq:HLambdaSecond`'s `χ̂_Λ`-row is `Σ_k χ̂_k (L₀ a_k†a₀ + a₀†a_k L₀)` with the condensate
factor `L₀ = c₁·n₀ − c₂·1`.  Under the ⟨condensate | excited⟩ split `Work.BoseB4.split` each
summand is the anti-normal monomial combination

    c₁·monoOp 2 1 (creOfE (φ k)) − (2c₁+c₂)·monoOp 1 0 (creOfE (φ k))
      + c₁·monoOp 1 2 (annOfE (φ k)) − (2c₁+c₂)·monoOp 0 1 (annOfE (φ k)) ,

which is what the present lemma records, for a finite weighted family of modes `s` with weights
`χ` and modes `φ k` (`φ k 0 = 0`, i.e. the superposed mode is an excited mode).

The proof is three steps:

* **per mode** (`kf_HchiGen_perMode`): `L₀ ∘ (a_k† ∘ a₀) + a₀† ∘ a_k ∘ L₀` transports to the
  monomial combination above; the four monomial slots come from the two halves,
  `a₀†a₀a_k†a₀ = c₁(monoOp 2 1 − 2 monoOp 1 0) − c₂ monoOp 1 0` and
  `a₀†a_k a₀†a₀ = c₁(monoOp 1 2 − 2 monoOp 0 1) − c₂ monoOp 0 1`, whose core identities are
  `split_L0_row1_core` / `split_L0_row2_core` (the CCR `[a₀,a₀†] = 1`);
* **reassembly** (`kf_HchiGen_reassemble`): `monoOp p q` is ℝ-linear in its spectator slot
  (`monoOp_sum_real_smul`), so the weighted sum of the four slots is `monoOp p q` of the
  corresponding weighted spectator sums;
* **assembly**: `split` is ℝ-linear, so it commutes with the weighted sum.
-/

noncomputable section

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {m : ℕ} [NeZero m]

open Work.BoseB4

/-- The transported `χ̂`-row slot combination: the `(2,1)`- and `(1,0)`-slots of the creation
half with coefficient `c₁` and `2c₁+c₂`, and the `(1,2)`- and `(0,1)`-slots of the annihilation
half. -/
private noncomputable def chiK (c1 c2 : ℝ)
    (B C : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) :
    FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m)) :=
  (c1 : ℂ) • monoOp 2 1 B - (((2 * c1 + c2 : ℝ)) : ℂ) • monoOp 1 0 B
    + (c1 : ℂ) • monoOp 1 2 C - (((2 * c1 + c2 : ℝ)) : ℂ) • monoOp 0 1 C

/-- Splitting a finite sum of differences.  (`Finset.sum_sub_distrib` requires a
`SubtractionCommMonoid`, which the additive-group-valued sums occurring here do not have.) -/
private theorem sum_sub_split {ι : Type*} {M : Type*} [AddCommGroup M] [DecidableEq ι]
    (s : Finset ι) (f g : ι → M) :
    (∑ k ∈ s, (f k - g k)) = ∑ k ∈ s, f k - ∑ k ∈ s, g k := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha, ih]
      abel

/-- **The per-mode dictionary of the `χ̂`-row.**  For a single excited mode `φ k` (`φ k 0 = 0`)
the transported row `L₀ ∘ (a_k† ∘ a₀) + a₀† ∘ a_k ∘ L₀` is the four-slot monomial combination
`chiK`. -/
private theorem kf_HchiGen_perMode {Mode : Type*}
    (φ : Mode → Fin m → ℝ) (k : Mode) (hφ : φ k 0 = 0) (c1 c2 : ℝ) (x : RealFock m) :
    split ((((c1 • n0 - c2 • (1 : RealFock m →ₗ[ℝ] RealFock m)).comp ((creOf m (φ k)) ∘ₗ (ann m 0)))
        + ((cre m 0) ∘ₗ (annOf m (φ k)) ∘ₗ (c1 • n0 - c2 • (1 : RealFock m →ₗ[ℝ] RealFock m)))) x)
      = chiK c1 c2 (creOfE (φ k)) (annOfE (φ k)) (split x) := by
  -- The four dictionary rows: `a₀†a₀a_k†a₀`, `a_k†a₀`, `a₀†a_k a₀†a₀`, `a₀†a_k`.
  have h1 : split ((cre m 0) ((ann m 0) ((creOf m (φ k)) ((ann m 0) x))))
      = (monoOp 2 1 (creOfE (φ k)) - (2 : ℂ) • monoOp 1 0 (creOfE (φ k))) (split x) := by
    rw [split_cre_zero, split_ann_zero, split_creOf (φ k) hφ, split_ann_zero]
    exact split_L0_row1_core (creOfE (φ k)) (split x)
  have h2 : split ((creOf m (φ k)) ((ann m 0) x)) = (monoOp 1 0 (creOfE (φ k))) (split x) := by
    rw [split_creOf (φ k) hφ, split_ann_zero, monoOp_one_zero, LinearMap.comp_apply, lift_a0]
  have h3 : split ((cre m 0) ((annOf m (φ k)) ((cre m 0) ((ann m 0) x))))
      = (monoOp 1 2 (annOfE (φ k)) - (2 : ℂ) • monoOp 0 1 (annOfE (φ k))) (split x) := by
    rw [split_cre_zero, split_annOf (φ k) hφ, split_cre_zero, split_ann_zero]
    exact split_L0_row2_core (annOfE (φ k)) (split x)
  have h4 : split ((cre m 0) ((annOf m (φ k)) x)) = (monoOp 0 1 (annOfE (φ k))) (split x) := by
    rw [split_cre_zero, split_annOf (φ k) hφ, monoOp_zero_one, LinearMap.comp_apply]
  -- The two halves, expanded through the linearity of `L₀`.
  have hx : (((c1 • n0 - c2 • (1 : RealFock m →ₗ[ℝ] RealFock m)).comp ((creOf m (φ k)) ∘ₗ (ann m 0)))
        + ((cre m 0) ∘ₗ (annOf m (φ k)) ∘ₗ (c1 • n0 - c2 • (1 : RealFock m →ₗ[ℝ] RealFock m)))) x
      = c1 • ((cre m 0) ((ann m 0) ((creOf m (φ k)) ((ann m 0) x))))
        - c2 • ((creOf m (φ k)) ((ann m 0) x))
        + (c1 • ((cre m 0) ((annOf m (φ k)) ((cre m 0) ((ann m 0) x))))
          - c2 • ((cre m 0) ((annOf m (φ k)) x))) := by
    simp only [n0, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]
  rw [hx]
  simp only [map_sub, map_add, map_smul]
  rw [h1, h2, h3, h4]
  simp only [chiK, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_sub,
    Complex.ofReal_add, Complex.ofReal_mul]
  module

/-- **Reassembly of the weighted four-slot sum.**  Because `monoOp p q` is ℝ-linear in its
spectator slot (`monoOp_sum_real_smul`), the weighted sum of the four monomial slots of `chiK`
collapses to `monoOp` of the corresponding weighted spectator sums (the slot coefficients
`2c₁+c₂` carry the `2` of the second-order CCR). -/
private theorem kf_HchiGen_reassemble {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (χ : ι → ℝ) (c1 c2 : ℝ)
    (B C : ι → cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (v : FockCore (cfock (Excited m))) :
    (∑ k ∈ s, χ k • chiK c1 c2 (B k) (C k)) v
      = ((monoOp 2 1 (∑ k ∈ s, ((c1 * χ k : ℝ) : ℂ) • B k))
          - monoOp 1 0 (∑ k ∈ s, (((2 * c1 + c2) * χ k : ℝ) : ℂ) • B k)
          + monoOp 1 2 (∑ k ∈ s, ((c1 * χ k : ℝ) : ℂ) • C k)
          - monoOp 0 1 (∑ k ∈ s, (((2 * c1 + c2) * χ k : ℝ) : ℂ) • C k)) v := by
  -- One weighted spectator sum is `monoOp` of the assembled spectator.
  have keyv : ∀ (c : ℝ) (D : ι → cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) (p q : ℕ),
      (∑ k ∈ s, (c * χ k) • ((monoOp p q (D k)) v))
        = (monoOp p q (∑ k ∈ s, ((c * χ k : ℝ) : ℂ) • D k)) v := by
    intro c D p q
    have h1 : (∑ k ∈ s, (c * χ k) • ((monoOp p q (D k)) v))
        = (∑ k ∈ s, (c * χ k) • monoOp p q (D k)) v := by
      rw [LinearMap.sum_apply]
      exact Finset.sum_congr rfl fun k _ =>
        (LinearMap.smul_apply (c * χ k) (monoOp p q (D k)) v).symm
    rw [h1]
    exact congrArg (fun F => F v)
      (monoOp_sum_real_smul p q s (fun k => c * χ k) D).symm
  -- The weighted summand expands to the four (weighted) slots.
  have hstep : ∀ k ∈ s,
      (χ k • chiK c1 c2 (B k) (C k)) v
        = (c1 * χ k) • ((monoOp 2 1 (B k)) v)
          - ((2 * c1 + c2) * χ k) • ((monoOp 1 0 (B k)) v)
          + (c1 * χ k) • ((monoOp 1 2 (C k)) v)
          - ((2 * c1 + c2) * χ k) • ((monoOp 0 1 (C k)) v) := by
    intro k _
    simp only [LinearMap.smul_apply, chiK, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, smul_sub, smul_add]
    module
  rw [LinearMap.sum_apply, Finset.sum_congr rfl hstep]
  rw [sum_sub_split (f := fun k => (c1 * χ k) • ((monoOp 2 1 (B k)) v)
        - ((2 * c1 + c2) * χ k) • ((monoOp 1 0 (B k)) v)
        + (c1 * χ k) • ((monoOp 1 2 (C k)) v)),
      Finset.sum_add_distrib, sum_sub_split]
  rw [keyv c1 B 2 1, keyv (2 * c1 + c2) B 1 0, keyv c1 C 1 2, keyv (2 * c1 + c2) C 0 1]
  simp only [LinearMap.sub_apply, LinearMap.add_apply]

theorem kf_HchiGen {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (s : Finset Mode) (χ : Mode → ℝ) (φ : Mode → Fin m → ℝ)
    (hφ : ∀ k ∈ s, φ k 0 = 0) (c1 c2 : ℝ) (x : Work.BoseB4.RealFock m) :
    Work.BoseB4.split ((∑ k ∈ s, χ k •
        ((((c1 • Work.BoseBoxFock.n0 - c2 • (1 : Work.BoseB4.RealFock m →ₗ[ℝ] Work.BoseB4.RealFock m)).comp ((Work.BoseB4.creOf m (φ k)) ∘ₗ (Work.BoseB4.ann m 0)))
          + ((Work.BoseB4.cre m 0) ∘ₗ (Work.BoseB4.annOf m (φ k)) ∘ₗ (c1 • Work.BoseBoxFock.n0 - c2 • (1 : Work.BoseB4.RealFock m →ₗ[ℝ] Work.BoseB4.RealFock m)))) x)))
      = ((Work.BoseB4.monoOp 2 1 (∑ k ∈ s, ((c1 * χ k : ℝ) : ℂ) • Work.BoseBoxFock.creOfE (φ k)))
          - Work.BoseB4.monoOp 1 0 (∑ k ∈ s, (((2 * c1 + c2) * χ k : ℝ) : ℂ) • Work.BoseBoxFock.creOfE (φ k))
          + Work.BoseB4.monoOp 1 2 (∑ k ∈ s, ((c1 * χ k : ℝ) : ℂ) • Work.BoseBoxFock.annOfE (φ k))
          - Work.BoseB4.monoOp 0 1 (∑ k ∈ s, (((2 * c1 + c2) * χ k : ℝ) : ℂ) • Work.BoseBoxFock.annOfE (φ k))) (Work.BoseB4.split x) := by
  have hsum : (∑ k ∈ s, χ k • chiK c1 c2 (creOfE (φ k)) (annOfE (φ k))) (split x)
      = ∑ k ∈ s, χ k • (chiK c1 c2 (creOfE (φ k)) (annOfE (φ k)) (split x)) := by
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun k _ => LinearMap.smul_apply _ _ _)
  rw [map_sum]
  trans ∑ k ∈ s, χ k • chiK c1 c2 (creOfE (φ k)) (annOfE (φ k)) (split x)
  · exact Finset.sum_congr rfl
      (fun k hk => by rw [map_smul, kf_HchiGen_perMode φ k (hφ k hk) c1 c2 x])
  · rw [← hsum]
    exact kf_HchiGen_reassemble s χ c1 c2 (fun k => creOfE (φ k)) (fun k => annOfE (φ k))
      (split x)

end Work.BoseBoxFock
