import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseB4.K2ndDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.split_number_sum` — the excited-mode number operator under `split`

The mode lattice `RealFock m = (Fin m →₀ ℕ) →₀ ℝ` splits through
`Work.BoseB4.split` into `𝔉(ℂθ) ⊗ 𝔉(θ^⊥)`, and the per-mode correspondence of
FS §8 (`Split_cre_zero`, `Split_ann_zero`, `Split_cre_excited`,
`Split_ann_excited`) reads the lattice operators `ann m k`, `cre m k` as the
abstract `a0`, `a0†` (mode `0`) and `lift (annC j)`, `lift (creC j)` (excited
mode `j ≠ 0`).

This module assembles those correspondences into the *weighted sum of excited
number operators*: for a finite set `s` of *excited* modes (`0 ∉ s`) and real
weights `w`,

    `split ((∑ k ∈ s, w k • (cre m k ∘ ann m k)) x)
      = (monoOp 0 0 (∑ k ∈ s, (w k : ℂ) • (creX m k ∘ annX m k))) (split x)`,

i.e. the number operator `∑_{k ∈ s} w k · N_k` is carried by `split` to the
levelwise lift of the complex spectator operator `∑_{k ∈ s} (w k : ℂ) · N_k^{C}`.
Since `monoOp 0 0 B = lift B`, this is the `(p,q) = (0,0)` slot of the anti-normal
dictionary used by FS `thm:Kafz`.

## Route

* `lift_zero`, `lift_sum` — `lift` is additive in the spectator operator;
* `split_mode_compose` — the per-mode identity for `k ≠ 0`, obtained from
  `Split_cre_excited`/`Split_ann_excited`, `LinearMap.restrictScalars_comp` and
  `lift_comp`;
* `split_sum_modes` — the finite-sum version, by `Finset.induction_on`, using the
  linearity of `LinearMap.comp` in its second argument and the (definitional)
  agreement of the real and complex scalar actions on `ℝ`-linear maps;
* `split_number_sum` — evaluate at `x` and rewrite `monoOp 0 0 B = lift B`.
-/

noncomputable section

open scoped lp BigOperators

namespace Work.BoseB4

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Additivity of `lift` -/

/-- The levelwise lift of the zero spectator operator is zero. -/
@[simp] lemma lift_zero : lift (E := E) (0 : E →ₗ[ℂ] E) = 0 := by
  apply LinearMap.ext
  intro Ψ
  apply Finsupp.ext
  intro n
  simp [lift_apply]

/-- The levelwise lift is additive in the spectator operator. -/
lemma lift_sum {ι : Type*} (s : Finset ι) (f : ι → E →ₗ[ℂ] E) :
    lift (∑ i ∈ s, f i) = ∑ i ∈ s, lift (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, lift_add, ih]

/-! ## The per-mode identity -/

/-- **The composition `cre m k ∘ ann m k` of an excited lattice mode corresponds
under `split` to the lift of the complex number operator `creX m k ∘ annX m k`.**
This is `Split_cre_excited` composed with `Split_ann_excited`. -/
lemma split_mode_compose {m : ℕ} [NeZero m] (k : Fin m) (hk : k ≠ 0) :
    split.comp ((cre m k).comp (ann m k))
      = (LinearMap.restrictScalars ℝ (lift ((creX m k).comp (annX m k)))).comp split := by
  have hcreX : creX m k = creC (Excited m) ⟨k, hk⟩ := by rw [creX, dif_neg hk]
  have hannX : annX m k = annC (Excited m) ⟨k, hk⟩ := by rw [annX, dif_neg hk]
  have hcre := Split_cre_excited (m := m) (⟨k, hk⟩ : Excited m)
  have hann := Split_ann_excited (m := m) (⟨k, hk⟩ : Excited m)
  have hmid :
      LinearMap.restrictScalars ℝ (lift (creC (Excited m) (⟨k, hk⟩ : Excited m))) ∘ₗ
          LinearMap.restrictScalars ℝ (lift (annC (Excited m) (⟨k, hk⟩ : Excited m)))
        = LinearMap.restrictScalars ℝ
            (lift ((creC (Excited m) (⟨k, hk⟩ : Excited m)) ∘ₗ
              (annC (Excited m) (⟨k, hk⟩ : Excited m)))) := by
    rw [← LinearMap.restrictScalars_comp, lift_comp]
  rw [hcreX, hannX]
  calc split ∘ₗ ((cre m k) ∘ₗ (ann m k))
      = (split ∘ₗ cre m k) ∘ₗ ann m k := by rw [LinearMap.comp_assoc]
    _ = (LinearMap.restrictScalars ℝ (lift (creC (Excited m) (⟨k, hk⟩ : Excited m))) ∘ₗ split) ∘ₗ ann m k := by
          rw [hcre]
    _ = LinearMap.restrictScalars ℝ (lift (creC (Excited m) (⟨k, hk⟩ : Excited m))) ∘ₗ (split ∘ₗ ann m k) := by
          rw [LinearMap.comp_assoc]
    _ = LinearMap.restrictScalars ℝ (lift (creC (Excited m) (⟨k, hk⟩ : Excited m))) ∘ₗ
          (LinearMap.restrictScalars ℝ (lift (annC (Excited m) (⟨k, hk⟩ : Excited m))) ∘ₗ split) := by
          rw [hann]
    _ = (LinearMap.restrictScalars ℝ (lift (creC (Excited m) (⟨k, hk⟩ : Excited m))) ∘ₗ
          LinearMap.restrictScalars ℝ (lift (annC (Excited m) (⟨k, hk⟩ : Excited m)))) ∘ₗ split := by
          rw [LinearMap.comp_assoc]
    _ = LinearMap.restrictScalars ℝ
          (lift ((creC (Excited m) (⟨k, hk⟩ : Excited m)) ∘ₗ
            (annC (Excited m) (⟨k, hk⟩ : Excited m)))) ∘ₗ split := by
          rw [hmid]

/-! ## The finite-sum identity -/

/-- **The weighted sum of excited number operators commutes with `split`.**
For a finite set `s` of excited modes and real weights `w`,
`split ∘ ∑_{k∈s} w_k (cre_k ∘ ann_k) = (↑ℝ lift (∑_{k∈s} (w_k : ℂ) (creX_k ∘ annX_k))) ∘ split`. -/
lemma split_sum_modes {m : ℕ} [NeZero m] (w : Fin m → ℝ) :
    ∀ s : Finset (Fin m), (∀ k ∈ s, k ≠ 0) →
      split.comp (∑ k ∈ s, w k • ((cre m k).comp (ann m k)))
        = (LinearMap.restrictScalars ℝ
            (lift (∑ k ∈ s, ((w k : ℂ)) • ((creX m k).comp (annX m k))))).comp split := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp
  | insert a s ha ih =>
      intro hs
      have ha0 : a ≠ 0 := hs a (Finset.mem_insert_self a s)
      have hs' : ∀ k ∈ s, k ≠ 0 := fun k hk => hs k (Finset.mem_insert_of_mem hk)
      have hper := split_mode_compose (m := m) a ha0
      have hih := ih hs'
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        LinearMap.comp_add, LinearMap.comp_smul,
        lift_add, lift_smul,
        LinearMap.restrictScalars_add, LinearMap.restrictScalars_smul,
        LinearMap.add_comp, LinearMap.smul_comp, hper, hih]
      rfl

/-! ## The target -/

theorem split_number_sum {m : ℕ} [NeZero m] (s : Finset (Fin m)) (h0 : (0 : Fin m) ∉ s)
    (w : Fin m → ℝ) (x : Work.BoseB4.RealFock m) :
    Work.BoseB4.split ((∑ k ∈ s, w k • ((Work.BoseB4.cre m k).comp (Work.BoseB4.ann m k))) x)
      = (Work.BoseB4.monoOp 0 0
          (∑ k ∈ s, ((w k : ℂ)) • (Work.BoseB4.creX m k).comp (Work.BoseB4.annX m k)))
        (Work.BoseB4.split x) := by
  have hs : ∀ k ∈ s, k ≠ 0 := fun k hk hk0 => h0 (hk0 ▸ hk)
  have hmap := split_sum_modes (m := m) w s hs
  rw [monoOp_zero_zero]
  simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] using
    LinearMap.congr_fun hmap x

end Work.BoseB4
