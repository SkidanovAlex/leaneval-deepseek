import Mathlib
import Submission.Work.ThomBordism.Grassmann.p1RatAux
import Submission.Work.ThomBordism.Grassmann.p1CruxRatNeZero
import Submission.Work.ThomBordism.Grassmann.zStd_complexification_iso
import Submission.Work.ThomBordism.Grassmann.Probe2.p1RatNeZero_of_twoTwo
import Submission.Work.Thom.pontryagin1_comap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# Assembly lemmas for `Work.ThomBordism.Grassmann.p1RatNeZero`

Two sorry-free reduction lemmas, leaving only the geometric probe as an input:

* `p1Rat_ne_zero_of_probe` — an existential probe statement `∃ σ : C(ℂP², G̃r_k(ℝ^{k+m})),
  σ*(p₁ γ) = ± p₁ zStd` implies `p1Rat k m ≠ 0` (rationalisation + `P1Crux.chernReducedRatNeZero`).
* `p1RatNeZero_of_base` — the **stabilisation** of the base case `p1Rat 2 4 ≠ 0` to every
  `k, m ≥ 4` along the sorry-free one-step maps `CohMap_p1_addLine` (increasing `k`) and
  `CohMap_p1_incl` (increasing `m`) of `p1RatNeZero_of_twoTwo.lean` (those steps are stated for
  *all* `k, m`, so they run from any base case, not only from `(2,2)`).
-/

namespace Work.ThomBordism.Grassmann.Probe2

open scoped TensorProduct

noncomputable section

/-- `p₁` of the standard bundle is `∓` the reduced Chern class. -/
theorem pontryagin1_zStd :
    Work.Thom.pontryagin1 Work.ThomBordism.Grassmann.zStd
      = - Work.ThomBordism.Grassmann.chernReduced := by
  rw [Work.Thom.pontryagin1_def]
  congr 1
  exact Work.Thom.chernClass_BundleIso _ _
    (Classical.choice zStd_complexification_iso)

/-- **The probe assembly**: if `σ : ℂP² → G̃r_k(ℝ^{k+m})` pulls `p₁(γ)` back to `± p₁(zStd)`, then
`p1Rat k m ≠ 0`.  Rationalising `p1Rat k m = 1 ⊗ p₁(γ)` along the pullback map, transporting the
non-vanishing of `chernReduced = -p₁(zStd)` across the (nonzero) rationalised pullback. -/
theorem p1Rat_ne_zero_of_probe (k m : ℕ)
    (h : ∃ σ : C(Work.Projective.CP 2, OG k m),
      (Work.Thom.CohMap σ ℤ 4).hom (p1 k m) = Work.Thom.pontryagin1 zStd ∨
      (Work.Thom.CohMap σ ℤ 4).hom (p1 k m) = - Work.Thom.pontryagin1 zStd) :
    p1Rat k m ≠ 0 := by
  obtain ⟨σ, hσ | hσ⟩ := h
  · have h4 : (1 : ℚ) ⊗ₜ[ℤ] ((Work.Thom.CohMap σ ℤ 4).hom (p1 k m)) ≠ 0 := by
      rw [hσ, pontryagin1_zStd, TensorProduct.tmul_neg]
      exact neg_ne_zero.mpr P1Crux.chernReducedRatNeZero
    have h5 : TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ) ((Work.Thom.CohMap σ ℤ 4).hom)
        (p1Rat k m) ≠ 0 := by
      rw [show p1Rat k m = (1 : ℚ) ⊗ₜ[ℤ] p1 k m from rfl, TensorProduct.map_tmul]
      simpa using h4
    intro h0
    exact h5 (by rw [h0, map_zero])
  · have h4 : (1 : ℚ) ⊗ₜ[ℤ] ((Work.Thom.CohMap σ ℤ 4).hom (p1 k m)) ≠ 0 := by
      rw [hσ, pontryagin1_zStd]
      simp only [neg_neg]
      exact P1Crux.chernReducedRatNeZero
    have h5 : TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ) ((Work.Thom.CohMap σ ℤ 4).hom)
        (p1Rat k m) ≠ 0 := by
      rw [show p1Rat k m = (1 : ℚ) ⊗ₜ[ℤ] p1 k m from rfl, TensorProduct.map_tmul]
      simpa using h4
    intro h0
    exact h5 (by rw [h0, map_zero])

/-- **Stabilisation of a base case**: `p1Rat k m ≠ 0` propagates upwards in `k` and in `m` along the
one-step maps of the oriented Grassmannian. -/
theorem p1RatNeZero_of_base (h : p1Rat 2 4 ≠ 0) :
    ∀ k m : ℕ, 4 ≤ k → 4 ≤ m → p1Rat k m ≠ 0 := by
  have stepK : ∀ k m : ℕ, p1Rat k m ≠ 0 → p1Rat (k + 1) m ≠ 0 := by
    intro k m hk
    obtain ⟨φ, hφ⟩ := CohMap_p1_addLine k m
    have hrat : TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ) ((Work.Thom.CohMap φ ℤ 4).hom)
        (p1Rat (k + 1) m) = p1Rat k m := by
      rw [show p1Rat (k + 1) m = (1 : ℚ) ⊗ₜ[ℤ] p1 (k + 1) m from rfl,
        show p1Rat k m = (1 : ℚ) ⊗ₜ[ℤ] p1 k m from rfl]
      exact ratCohMap_tmul φ hφ
    intro h0
    exact hk (by rw [← hrat, h0, map_zero])
  have stepM : ∀ k m : ℕ, p1Rat k m ≠ 0 → p1Rat k (m + 1) ≠ 0 := by
    intro k m hk
    obtain ⟨φ, hφ⟩ := CohMap_p1_incl k m
    have hrat : TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ) ((Work.Thom.CohMap φ ℤ 4).hom)
        (p1Rat k (m + 1)) = p1Rat k m := by
      rw [show p1Rat k (m + 1) = (1 : ℚ) ⊗ₜ[ℤ] p1 k (m + 1) from rfl,
        show p1Rat k m = (1 : ℚ) ⊗ₜ[ℤ] p1 k m from rfl]
      exact ratCohMap_tmul φ hφ
    intro h0
    exact hk (by rw [← hrat, h0, map_zero])
  have hkBase : ∀ j : ℕ, p1Rat (2 + j) 4 ≠ 0 := by
    intro j
    induction j with
    | zero => simpa using h
    | succ j ih =>
        rw [Nat.add_succ]
        exact stepK (2 + j) 4 ih
  have hkm : ∀ k : ℕ, 2 ≤ k → p1Rat k 4 ≠ 0 := by
    intro k hk2
    have hh := hkBase (k - 2)
    rwa [Nat.add_sub_of_le hk2] at hh
  intro k m _ hm
  have hmBase : ∀ j : ℕ, p1Rat k (4 + j) ≠ 0 := by
    intro j
    induction j with
    | zero => simpa using hkm k (by omega)
    | succ j ih =>
        rw [Nat.add_succ]
        exact stepM k (4 + j) ih
  have hh := hmBase (m - 4)
  rwa [Nat.add_sub_of_le hm] at hh

end

end Work.ThomBordism.Grassmann.Probe2
