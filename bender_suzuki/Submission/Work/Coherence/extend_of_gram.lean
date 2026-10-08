import Mathlib
import Submission.Work.Coherence.Basic
import Submission.Work.Coherence.Isometry

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedSectionVars false

noncomputable section

open Classical

namespace Work.Coherence

universe u v

section Helpers

/-- A common denominator for a finite family of rationals: there is `N ≠ 0` and integer
coefficients `d` with `d i / N = c i`, i.e. `(d i : ℚ) = (N : ℚ) * c i`. -/
theorem exists_int_common_multiple {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℚ) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ d : ι → ℤ, ∀ i, (d i : ℚ) = (N : ℚ) * c i := by
  refine ⟨∏ i : ι, ((c i).den : ℤ),
    Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast Rat.den_nz (c i)),
    fun i => (c i).num * ∏ j ∈ Finset.univ.erase i, ((c j).den : ℤ), ?_⟩
  intro i
  have key : ((c i).den : ℚ) * c i = ((c i).num : ℚ) := by
    have hd : ((c i).den : ℚ) ≠ 0 := by exact_mod_cast Rat.den_nz (c i)
    have h := congrArg (fun t : ℚ => ((c i).den : ℚ) * t) (Rat.num_div_den (c i))
    rw [mul_div_cancel₀ _ hd] at h
    exact h.symm
  have hprod := Finset.prod_erase_mul Finset.univ (fun j => ((c j).den : ℚ)) (Finset.mem_univ i)
  simp only [Int.cast_mul, Int.cast_prod, Int.cast_natCast]
  rw [← hprod, mul_assoc, key, mul_comm]

/-- The `ℚ`-linear "linear combination" map `c ↦ ∑ i, c i • x i` attached to a finite family `x`. -/
def ratCombination {ι X : Type*} [Fintype ι] [AddCommGroup X] [Module ℚ X] (x : ι → X) :
    (ι → ℚ) →ₗ[ℚ] X where
  toFun c := ∑ i, c i • x i
  map_add' c d := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, add_smul]
  map_smul' a c := by
    rw [RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, smul_assoc]

/-- Rational and complex scalars agree on functions into `ℂ`. -/
theorem rat_smul_eq_complex_smul {ι : Type*} (q : ℚ) (z : ι → ℂ) :
    q • z = (q : ℂ) • z := by
  ext g; simp only [Pi.smul_apply, smul_eq_mul, Rat.smul_def]

end Helpers

theorem extend_of_gram {H G : Type*} [Group H] [Fintype H] [Group G] [Fintype G]
    {S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)} {φ : (H → ℂ) → (G → ℂ)}
    (hgram : ∀ x ∈ S, ∀ y ∈ S, cfInner (φ x) (φ y) = cfInner x y)
    (hcompat : ∀ c : ↥S → ℤ, (∑ x : ↥S, (c x : ℂ) • (x : H → ℂ)) 1 = 0 →
      ∑ x : ↥S, (c x : ℂ) • φ x = τ (∑ x : ↥S, (c x : ℂ) • (x : H → ℂ))) :
    ∃ T : (H → ℂ) →ₗ[ℤ] (G → ℂ),
      (∀ α ∈ ZSpan0 S, T α = τ α) ∧ IsometryOnAll S T ∧ ∀ x ∈ S, T x = φ x := by
  classical
  -- The two rational coefficient maps attached to `S` (the elements and their images `φ`).
  let lin : (↥S → ℚ) →ₗ[ℚ] (H → ℂ) := ratCombination (fun x : ↥S => (x : H → ℂ))
  let psi : (↥S → ℚ) →ₗ[ℚ] (G → ℂ) := ratCombination (fun x : ↥S => φ (x : H → ℂ))
  have hlin : ∀ c, lin c = ∑ x : ↥S, c x • (x : H → ℂ) := fun c => rfl
  have hpsi : ∀ c, psi c = ∑ x : ↥S, c x • φ (x : H → ℂ) := fun c => rfl
  -- Integer coefficients: combinations summing to `0` are killed.
  have hZ : ∀ c : ↥S → ℤ, (∑ x : ↥S, (c x : ℂ) • (x : H → ℂ)) = 0 →
      (∑ x : ↥S, (c x : ℂ) • φ x) = 0 := by
    intro c hc
    have h1 : (∑ x : ↥S, (c x : ℂ) • (x : H → ℂ)) 1 = 0 := by rw [hc]; rfl
    have h2 := hcompat c h1
    rwa [hc, map_zero] at h2
  -- Rational coefficients: combinations summing to `0` are killed.
  have hQ : ∀ c : ↥S → ℚ, lin c = 0 → psi c = 0 := by
    intro c hc
    obtain ⟨N, hN, d, hd⟩ := exists_int_common_multiple c
    have hdc : ∀ x : ↥S, (d x : ℂ) = (N : ℂ) * (c x : ℂ) := by
      intro x
      have h := congrArg (fun t : ℚ => (t : ℂ)) (hd x)
      push_cast at h
      exact h
    have hcc : (∑ x : ↥S, (c x : ℂ) • (x : H → ℂ)) = lin c := by
      rw [hlin]
      exact Finset.sum_congr rfl fun x _ => (rat_smul_eq_complex_smul (c x) (x : H → ℂ)).symm
    have h1 : (∑ x : ↥S, (d x : ℂ) • (x : H → ℂ)) = (N : ℂ) • lin c := by
      rw [hlin, Finset.smul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        rw [rat_smul_eq_complex_smul (c x) (x : H → ℂ), ← mul_smul, ← hdc x]
    have hdZ : (∑ x : ↥S, (d x : ℂ) • (x : H → ℂ)) = 0 := by rw [h1, hc, smul_zero]
    have h2 : (∑ x : ↥S, (d x : ℂ) • φ x) = (N : ℂ) • psi c := by
      rw [hpsi, Finset.smul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        rw [rat_smul_eq_complex_smul (c x) (φ (x : H → ℂ)), ← mul_smul, ← hdc x]
    have hy := hZ d hdZ
    rw [h2, smul_eq_zero] at hy
    rcases hy with h | h
    · exact absurd h (by exact_mod_cast hN)
    · exact h
  -- The rational coefficient map factors through `lin`.
  have hker : LinearMap.ker lin ≤ LinearMap.ker psi := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    exact hQ c hc
  -- The induced rational-linear map on `lin.range = ℚ[S]`.
  let liftQlin : (↥S → ℚ) ⧸ LinearMap.ker lin →ₗ[ℚ] (G → ℂ) :=
    Submodule.liftQ (LinearMap.ker lin) psi hker
  let ΨQ : LinearMap.range lin →ₗ[ℚ] (G → ℂ) :=
    liftQlin.comp (LinearMap.quotKerEquivRange lin).symm.toLinearMap
  have hΨQ : ∀ (c : ↥S → ℚ) (h : lin c ∈ LinearMap.range lin),
      ΨQ ⟨lin c, h⟩ = psi c := by
    intro c h
    have h1 : (LinearMap.quotKerEquivRange lin).symm (⟨lin c, h⟩ : LinearMap.range lin)
        = Submodule.Quotient.mk c := LinearMap.quotKerEquivRange_symm_apply_image lin c h
    simp only [ΨQ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [h1]
    exact Submodule.liftQ_apply (LinearMap.ker lin) psi c
  -- Extend `ΨQ` to all of `H → ℂ` using a complement of `lin.range`.
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range lin)
  let LQ : (H → ℂ) →ₗ[ℚ] (G → ℂ) :=
    ΨQ.comp ((LinearMap.fst ℚ (LinearMap.range lin) C).comp
      ((LinearMap.range lin).prodEquivOfIsCompl C hC).symm.toLinearMap)
  have hLQ : ∀ (v : H → ℂ) (hv : v ∈ LinearMap.range lin), LQ v = ΨQ ⟨v, hv⟩ := by
    intro v hv
    have h1 : ((LinearMap.range lin).prodEquivOfIsCompl C hC).symm v = (⟨v, hv⟩, 0) :=
      Submodule.prodEquivOfIsCompl_symm_apply_left (LinearMap.range lin) C hC ⟨v, hv⟩
    simp only [LQ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.fst_apply, h1]
  -- Values at the generators, via the indicator coefficients.
  have hsingle_lin : ∀ s₀ : ↥S, lin (fun y : ↥S => if y = s₀ then 1 else 0) = (s₀ : H → ℂ) := by
    intro s₀
    rw [hlin, Finset.sum_eq_single s₀]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ s₀) h
  have hsingle_psi : ∀ s₀ : ↥S, psi (fun y : ↥S => if y = s₀ then 1 else 0) = φ (s₀ : H → ℂ) := by
    intro s₀
    rw [hpsi, Finset.sum_eq_single s₀]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ s₀) h
  have hmem_range : ∀ x ∈ S, (x : H → ℂ) ∈ LinearMap.range lin := by
    intro x hx
    exact LinearMap.mem_range.mpr
      ⟨fun y : ↥S => if y = (⟨x, hx⟩ : ↥S) then 1 else 0, hsingle_lin ⟨x, hx⟩⟩
  have hLQmem : ∀ x ∈ S, LQ (x : H → ℂ) = φ x := by
    intro x hx
    rw [hLQ (x : H → ℂ) (hmem_range x hx)]
    have heq : (⟨(x : H → ℂ), hmem_range x hx⟩ : LinearMap.range lin)
        = ⟨lin (fun y : ↥S => if y = (⟨x, hx⟩ : ↥S) then 1 else 0),
            LinearMap.mem_range.mpr ⟨_, rfl⟩⟩ :=
      Subtype.ext (hsingle_lin ⟨x, hx⟩).symm
    rw [heq, hΨQ, hsingle_psi]
  -- The value of `LQ` on an integral combination.
  have hZSpan_val : ∀ (α : H → ℂ) (c : ↥S → ℤ),
      α = ∑ x : ↥S, (c x : ℂ) • (x : H → ℂ) →
      LQ α = ∑ x : ↥S, (c x : ℂ) • φ x := by
    intro α c hc
    have hcQ : lin (fun x : ↥S => (c x : ℚ)) = α := by
      rw [hlin, hc]
      apply Finset.sum_congr rfl
      intro x _
      rw [rat_smul_eq_complex_smul]
      simp
    have hmem : α ∈ LinearMap.range lin := LinearMap.mem_range.mpr ⟨_, hcQ⟩
    have heq : (⟨α, hmem⟩ : LinearMap.range lin)
        = ⟨lin (fun x : ↥S => (c x : ℚ)), LinearMap.mem_range.mpr ⟨_, rfl⟩⟩ :=
      Subtype.ext hcQ.symm
    rw [hLQ α hmem, heq, hΨQ, hpsi]
    exact Finset.sum_congr rfl fun x _ => by rw [rat_smul_eq_complex_smul]; simp
  -- Agreement with `τ` on the degree-zero lattice.
  have hagree : ∀ α ∈ ZSpan0 S, (LQ.restrictScalars ℤ) α = τ α := by
    intro α hα
    rw [LinearMap.restrictScalars_apply]
    obtain ⟨c, hc⟩ := hα.1
    rw [hZSpan_val α c hc]
    have h1 : (∑ x : ↥S, (c x : ℂ) • (x : H → ℂ)) 1 = 0 := hc ▸ hα.2
    rw [hcompat c h1, ← hc]
  -- Values at the generators.
  have hval : ∀ x ∈ S, (LQ.restrictScalars ℤ) x = φ x := by
    intro x hx
    rw [LinearMap.restrictScalars_apply]
    exact hLQmem x hx
  -- Isometry on the whole lattice.
  have hiso : IsometryOnAll S (LQ.restrictScalars ℤ) := by
    apply isometryOnAll_of_gram
    intro x hx y hy
    rw [hval x hx, hval y hy]
    exact hgram x hx y hy
  exact ⟨LQ.restrictScalars ℤ, hagree, hiso, hval⟩

end Work.Coherence
