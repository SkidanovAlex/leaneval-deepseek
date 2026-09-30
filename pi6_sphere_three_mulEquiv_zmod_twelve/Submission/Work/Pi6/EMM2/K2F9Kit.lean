import Mathlib
import Submission.Work.Pi6.EMM2.Statements
import Submission.Work.Pi6.EMM2.finiteType
import Submission.Work.Pi6.EMM2.SerreKit
import Submission.Work.Pi6.K2Z.transfer
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Cohomology.gradedComm
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-!
# Support lemmas for the threshold-`9` `K(ℤ/2,2)` forcing (`Work.Pi6.EMM2.k2forcing9`)

Elementary toolkit: vanishing/one-dimensionality transfer across homotopy equivalences, the
non-vanishing of the unit of the cup ring, the non-vanishing of `b ⊗ 1`, and the dimension bounds
`dim H³, H⁴ ≤ 1` for the `K(ℤ/2,2)` forcing.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.EMM2
namespace K2F9

noncomputable section

/-- A vanishing module has dimension zero. -/
theorem finrank_eq_zero_of_isZero {𝕜 M : Type} [Field 𝕜] [AddCommGroup M] [Module 𝕜 M]
    (h : IsZero (ModuleCat.of 𝕜 M)) : Module.finrank 𝕜 M = 0 := by
  haveI : Subsingleton (ModuleCat.of 𝕜 M) := ModuleCat.subsingleton_of_isZero h
  exact Module.finrank_zero_of_subsingleton

/-- A `Subsingleton` module is a zero object. -/
theorem isZero_of_subsingleton {𝕜 M : Type} [Field 𝕜] [AddCommGroup M] [Module 𝕜 M]
    [Subsingleton M] : IsZero (ModuleCat.of 𝕜 M) :=
  ModuleCat.isZero_of_subsingleton _

/-- The cohomology of a homotopy equivalence is an isomorphism in each degree. -/
theorem isIso_cmap_of_homotopyEquiv {𝕜 : Type} [Field 𝕜] {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    CategoryTheory.IsIso (Work.Cohomology.singularCohomologyMap 𝕜 (TopCat.of X) (TopCat.of Y)
      (TopCat.ofHom e.toFun) n) :=
  Work.Cohomology.homotopyEquiv 𝕜 (TopCat.of X) (TopCat.of Y) (TopCat.ofHom e.toFun)
    (TopCat.ofHom e.invFun) e.left_inv.some e.right_inv.some n

/-- Vanishing of cohomology transfers along a homotopy equivalence. -/
theorem isZero_coh_of_homotopyEquiv {𝕜 : Type} [Field 𝕜] {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ)
    (h : IsZero (Coh 𝕜 X n)) : IsZero (Coh 𝕜 Y n) := by
  haveI h1 := isIso_cmap_of_homotopyEquiv (𝕜 := 𝕜) e n
  have hY : Subsingleton (Coh 𝕜 X n) := ModuleCat.isZero_iff_subsingleton.mp h
  rw [ModuleCat.isZero_iff_subsingleton]
  exact ⟨fun a b => (CategoryTheory.asIso (Work.Cohomology.singularCohomologyMap 𝕜 (TopCat.of X)
    (TopCat.of Y) (TopCat.ofHom e.toFun) n)).toLinearEquiv.injective
      (Subsingleton.elim _ _)⟩

/-- Dimensions transfer along a homotopy equivalence. -/
theorem finrank_coh_of_homotopyEquiv {𝕜 : Type} [Field 𝕜] {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    Module.finrank 𝕜 (Coh 𝕜 X n) = Module.finrank 𝕜 (Coh 𝕜 Y n) := by
  haveI h1 := isIso_cmap_of_homotopyEquiv (𝕜 := 𝕜) e n
  exact (LinearEquiv.finrank_eq (CategoryTheory.asIso (Work.Cohomology.singularCohomologyMap 𝕜
    (TopCat.of X) (TopCat.of Y) (TopCat.ofHom e.toFun) n)).toLinearEquiv).symm

/-- The unit of the cup ring of a space with one-dimensional `H⁰` is nonzero. -/
theorem one_ne_zero {𝕜 : Type} [Field 𝕜] {X : Type} [TopologicalSpace X]
    (hco : Work.Pi6.EMM2.CupOneStatement)
    (h0 : Module.finrank 𝕜 (Coh 𝕜 X 0) = 1)
    (hfin : FiniteDimensional 𝕜 (Coh 𝕜 X 0)) : one 𝕜 X ≠ 0 := by
  intro hz
  haveI : FiniteDimensional 𝕜 (Coh 𝕜 X 0) := hfin
  have hsub : Subsingleton (Coh 𝕜 X 0) := ⟨fun a b => by
    have ha := (hco 𝕜 0 a).2
    have hb := (hco 𝕜 0 b).2
    rw [hz, map_zero] at ha hb
    rw [← ha, ← hb]⟩
  haveI : Subsingleton (Coh 𝕜 X 0) := hsub
  rw [Module.finrank_zero_of_subsingleton (R := 𝕜) (M := Coh 𝕜 X 0)] at h0
  exact absurd h0 (by norm_num)

/-- The dimension of a one-dimensional module is `≤ 1` (for use with `finrank_le_one_iff`). -/
theorem finrank_le_one_iff_of_finrank {𝕜 V : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (h : Module.finrank 𝕜 V = 1) : Module.finrank 𝕜 V ≤ 1 := le_of_eq h

/-- If `N` is one-dimensional and `u ≠ 0`, then `b ⊗ u = 0` forces `b = 0`. -/
theorem eq_zero_of_tmul_eq_zero {𝕜 : Type} [Field 𝕜] {M N : Type} [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup N] [Module 𝕜 N] (u : N) (hu : u ≠ 0) (b : M) (h : b ⊗ₜ[𝕜] u = 0) :
    b = 0 := by
  have hker : (LinearMap.toSpanSingleton 𝕜 N u).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    have hc' : c • u = 0 := hc
    rcases smul_eq_zero.mp hc' with h' | h'
    · exact h'
    · exact absurd h' hu
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  have hφu : φ u = 1 := by
    have := congrArg (fun f : 𝕜 →ₗ[𝕜] 𝕜 => f 1) hφ
    simpa [LinearMap.toSpanSingleton_apply] using this
  have h2 : b ⊗ₜ[𝕜] (1 : 𝕜) = 0 := by
    have h3 : (TensorProduct.map (LinearMap.id : M →ₗ[𝕜] M) φ) (b ⊗ₜ[𝕜] u)
        = b ⊗ₜ[𝕜] (φ u) := TensorProduct.map_tmul _ _ _ _
    rw [h, map_zero, hφu] at h3
    exact h3.symm
  have h4 : (TensorProduct.rid 𝕜 M) (b ⊗ₜ[𝕜] (1 : 𝕜)) = b := by
    rw [TensorProduct.rid_tmul, one_smul]
  rw [← h4, h2, map_zero]

/-- `cpow w 2 = w ⌣ w` (the second cup power is the cup square), using the left unit law. -/
theorem cpow_two_eq_cup {𝕜 : Type} [Field 𝕜] {X : Type} [TopologicalSpace X]
    (hco : Work.Pi6.EMM2.CupOneStatement) (w : Coh 𝕜 X 2) :
    Work.Pi6.cpow w 2 = Work.Pi6.cup 𝕜 X 2 2 w w := by
  have h1 : Work.Pi6.cup 𝕜 X (2 * 0) 2 (Work.Pi6.one 𝕜 X) w = w := by
    simpa using (hco 𝕜 2 w).1
  simp only [Work.Pi6.cpow]
  rw [h1]

/-- A class of degree `2` with nonvanishing square (a nonzero second cup power). -/
theorem cup_sq_ne_zero_of_cpow_two {𝕜 : Type} [Field 𝕜] {X : Type} [TopologicalSpace X]
    (hco : Work.Pi6.EMM2.CupOneStatement) (w : Coh 𝕜 X 2)
    (h : Work.Pi6.cpow w 2 ≠ 0) : Work.Pi6.cup 𝕜 X 2 2 w w ≠ 0 := by
  intro hc
  exact h (by rw [cpow_two_eq_cup hco w, hc])

/-- In `ZMod 2` every element is idempotent. -/
theorem zmodTwo_mul_self (x : ZMod 2) : x * x = x := by
  have h : x = 0 ∨ x = 1 := by
    have hlt : x.val < 2 := ZMod.val_lt x
    have hval : x.val = 0 ∨ x.val = 1 := by omega
    rcases hval with h | h
    · left
      have : ((x.val : ℕ) : ZMod 2) = ((0 : ℕ) : ZMod 2) := by rw [h]
      simpa using this
    · right
      have : ((x.val : ℕ) : ZMod 2) = ((1 : ℕ) : ZMod 2) := by rw [h]
      simpa using this
  rcases h with h | h <;> rw [h] <;> decide


/-! ## Spectral-sequence page helpers -/

open CategoryTheory CategoryTheory.Limits

/-- In a module of dimension `≤ 1` any element is a multiple of any nonzero element. -/
theorem exists_smul_eq_of_finrank_le_one {𝕜 : Type} [Field 𝕜] {V : Type} [AddCommGroup V]
    [Module 𝕜 V] [FiniteDimensional 𝕜 V] (h : Module.finrank 𝕜 V ≤ 1) {z x : V} (hz : z ≠ 0) :
    ∃ c : 𝕜, x = c • z := by
  have hpos : 0 < Module.finrank 𝕜 V := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨z, hz⟩
  have h1 : Module.finrank 𝕜 V = 1 := le_antisymm h (Nat.succ_le_of_lt hpos)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' z hz).mp h1 x
  exact ⟨c, hc.symm⟩

/-- The differential out of the row `q = 0` vanishes (its target has negative `q`). -/
theorem d_row0_eq_zero {𝕜 : Type} [Field 𝕜] (S : Work.Pi6.CohSS 𝕜) (r : ℕ) (hr : 2 ≤ r)
    (s : ℤ) :
    S.d r (s, 0) ((s, 0) + Work.Pi6.vr r) = 0 :=
  S.d_eq_zero_of_isZero (S.quad r ((s, 0) + Work.Pi6.vr r) (Or.inr (by simp [Work.Pi6.vr]; omega)))

/-- The page quotient `proj r a` is injective when the incoming differential vanishes. -/
theorem proj_injective {𝕜 : Type} [Field 𝕜] (S : Work.Pi6.CohSS 𝕜) (r : ℕ) (hr : 2 ≤ r)
    (a : ℤ × ℤ) (hzero : IsZero (S.E r (a - Work.Pi6.vr r))) :
    Function.Injective (S.proj r a) := by
  have hd : S.d r (a - Work.Pi6.vr r) a = 0 := hzero.eq_of_src _ _
  intro x y hxy
  have h1 : S.proj r a (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h2 : ((x - y : ↥(LinearMap.ker (S.d r a (a + Work.Pi6.vr r)).hom)) : S.E r a)
      ∈ LinearMap.range (S.d r (a - Work.Pi6.vr r) a).hom := (S.proj_ker r a hr (x - y)).mp h1
  rw [hd] at h2
  simp only [ModuleCat.hom_zero, LinearMap.range_zero, Submodule.mem_bot] at h2
  exact sub_eq_zero.mp (Subtype.ext h2)

/-- A finite-dimensional module of dimension zero is a zero object. -/
theorem isZero_of_finrank_eq_zero {𝕜 : Type} [Field 𝕜] {M : Type} [AddCommGroup M] [Module 𝕜 M]
    [FiniteDimensional 𝕜 M] (h : Module.finrank 𝕜 M = 0) : Subsingleton M :=
  Module.finrank_zero_iff.mp h

end

end K2F9
end Work.Pi6.EMM2
