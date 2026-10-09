import Mathlib
import Submission.NK.GlobalCFTdeep.LogLattice.LogLatticeMain
import Submission.NK.GlobalCFTdeep.Herbrand.finrank_tUnits
import Submission.NK.GlobalCFTdeep.LogLattice.finite_ker_logVecLin
import Submission.NK.GlobalCFTdeep.LogLattice.span_logVecLin_oneVec
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.LogLattice

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The log lattice is the range of the log map.**  These are the same subset of `↥T → ℝ` (the
image of `logVecLin T`), one presented as an `AddSubgroup` and the other as a `ℤ`-submodule; the
identity map between the two subtypes is `ℤ`-linear, so the two have the same `ℤ`-rank. -/
noncomputable def logLatticeEquivRange (T : Set (Place L)) [Fintype ↥T] :
    ↥(NK.GlobalCFTdeep.logLattice T) ≃ₗ[ℤ]
      ↥(LinearMap.range (NK.GlobalCFTdeep.logVecLin (L := L) T)) where
  toFun x := ⟨(x : ↥T → ℝ), by
    obtain ⟨a, ha⟩ := (NK.GlobalCFTdeep.mem_logLattice (T := T)).mp x.2
    exact LinearMap.mem_range.mpr ⟨a, ha⟩⟩
  invFun y := ⟨(y : ↥T → ℝ),
    (NK.GlobalCFTdeep.mem_logLattice (T := T)).mpr (LinearMap.mem_range.mp y.2)⟩
  left_inv x := Subtype.ext rfl
  right_inv y := Subtype.ext rfl
  map_add' x y := Subtype.ext rfl
  map_smul' c x := Subtype.ext rfl

/-- **The additive map `M' × ℤ → M = M' + ℤ·e`**, `(y, n) ↦ y + n·e`, exhibiting the full log
lattice as an extension of the log lattice by `ℤ`.  It is bijective (see `finrank_lattices`):
surjective by definition of `unitLattice`, injective because `M'` lies in the sum-zero hyperplane
and `∑_{w ∈ T} 1 = |T| ≠ 0`. -/
noncomputable def unitLatticeProdHom (T : Set (Place L)) [Fintype ↥T] :
    (↥(NK.GlobalCFTdeep.logLattice T) × ℤ) →+ ↥(NK.GlobalCFTdeep.unitLattice T) where
  toFun x := ⟨(x.1 : ↥T → ℝ) + x.2 • NK.GlobalCFTdeep.oneVec T,
    (NK.GlobalCFTdeep.mem_unitLattice_iff (T := T)).mpr ⟨x.1, x.1.2, x.2, rfl⟩⟩
  map_zero' := by
    refine Subtype.ext ?_
    simp
  map_add' := by
    rintro ⟨y, n⟩ ⟨y', n'⟩
    refine Subtype.ext ?_
    funext w
    simp only [AddSubgroup.coe_add, Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.smul_apply,
      NK.GlobalCFTdeep.oneVec, add_zsmul]
    ring

/-- **The ranks of the three lattices of Milne's proof of Proposition 3.1.**

* the log lattice has `ℤ`-rank `|T| - 1` (the `S`-unit theorem: `TUnits` has rank `|T| - 1` by
  `NK.GlobalCFTdeep.Herbrand.finrank_tUnits` and the kernel of the log map is finite,
  `NK.GlobalCFTdeep.LogLattice.finite_ker_logVecLin`);
* the full log lattice `M = M' + ℤ·e` has `ℤ`-rank `|T| = finrank ℝ (↥T → ℝ)`: its `ℝ`-span is
  everything (`NK.GlobalCFTdeep.LogLattice.span_logVecLin_oneVec`) and `e ∉ sumZero` because
  `∑_{w ∈ T} 1 = |T| ≠ 0` (T is nonempty: it contains all infinite places and a number field has
  an infinite place), so `M' ∩ ℤ·e = 0` and the sum is direct;
* the divisor lattice (`↥T → ℤ` inside `↥T → ℝ`) has `ℤ`-rank `|T| = finrank ℝ (↥T → ℝ)`, since it
  spans (`NK.GlobalCFTdeep.span_divisorLattice`) and is `ℤ`-free of rank `|T|`.

Useful ingredients: `Module.finrank_baseChange`
(`finrank ℚ (ℚ ⊗[ℤ] M) = finrank ℤ M`), flatness of `ℚ` over `ℤ`, `ℚ ⊗[ℤ] K = 0` for finite `K`,
`Module.finrank_pi`, `Module.finrank_prod`, and `Submodule.finrank_lt`-style inequalities for the
span of a lattice (the `ℝ`-dimension of the span of a `ℤ`-free module of rank `d` is at most `d`,
with equality iff the module maps injectively into its `ℚ`-span). -/
theorem finrank_lattices {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (T : Set (NK.GlobalCFT.Place L)) [Fintype ↥T]
    (hTinf : ∀ w : NK.GlobalCFT.Place L, w.IsInfinite → w ∈ T) :
    Module.finrank ℤ ↥(NK.GlobalCFTdeep.logLattice T) = Nat.card T - 1 ∧
      Module.finrank ℤ ↥(NK.GlobalCFTdeep.unitLattice T) = Module.finrank ℝ (↥T → ℝ) ∧
      Module.finrank ℤ ↥(NK.GlobalCFTdeep.divisorLattice T) = Module.finrank ℝ (↥T → ℝ) := by
  classical
  -- `T` is nonempty (it contains every infinite place, and there is one).
  have hTne : Nonempty ↥T := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace L))
    exact ⟨⟨Place.ofInfinite w, hTinf _ trivial⟩⟩
  haveI : Finite ↥T := Finite.of_fintype ↥T
  have hTnz : Nat.card ↥T ≠ 0 := Nat.card_ne_zero.mpr ⟨hTne, inferInstance⟩
  have hpos : 0 < Fintype.card ↥T := Fintype.card_pos_iff.mpr hTne
  -- The log lattice lies in the sum-zero hyperplane (product formula).
  have hlog_sumZero : (logLattice T : Set (↥T → ℝ)) ⊆ sumZero T := by
    intro y hy
    obtain ⟨a, rfl⟩ := (mem_logLattice (T := T)).mp hy
    exact (mem_sumZero (T := T) (f := logVecLin T a)).mpr
      (by rw [logVecLin_apply]
          exact sum_logVec_eq_zero (K := K) T hTinf _ (Additive.toMul a).2)
  -- The coordinate sum of `n • e` is `n * |T|`.
  have hone_sum : ∀ n : ℤ, (∑ w : ↥T, (n • oneVec T : ↥T → ℝ) w) = n * (Nat.card ↥T : ℝ) := by
    intro n
    have h : ∀ w : ↥T, (n • oneVec T : ↥T → ℝ) w = (n : ℝ) := by intro w; simp [oneVec]
    rw [Finset.sum_congr rfl (fun w _ => h w)]
    rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
    rw [nsmul_eq_mul, mul_comm]
  -- **The kernel of the log map is finite, hence of rank `0`.**
  have hkerfin : Module.finrank ℤ ↥(LinearMap.ker (logVecLin T)) = 0 := by
    haveI : Finite ↥(LinearMap.ker (logVecLin T)) := finite_ker_logVecLin (K := K) T hTinf
    haveI : Module.IsTorsion ℤ ↥(LinearMap.ker (logVecLin T)) :=
      isAddTorsion_iff_isTorsion_int.mp (isAddTorsion_of_finite)
    exact Module.IsTorsion.finrank_eq_zero ‹_›
  -- **Rank-nullity**: `finrank M' = finrank U(T) - finrank ker = |T| - 1`.
  have hTU := NK.GlobalCFTdeep.Herbrand.finrank_tUnits (L := L) T hTinf
  haveI : Module.Finite ℤ (Additive (TUnits T)) := hTU.1
  have hrange : Module.finrank ℤ ↥(LinearMap.range (logVecLin T)) = Nat.card T - 1 := by
    have hd := Submodule.finrank_quotient_add_finrank (LinearMap.ker (logVecLin T))
    have hq := LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange (logVecLin T))
    rw [hq] at hd
    omega
  have h1 : Module.finrank ℤ ↥(logLattice T) = Nat.card T - 1 := by
    rw [← hrange]
    exact LinearEquiv.finrank_eq (logLatticeEquivRange T)
  refine ⟨h1, ?_, ?_⟩
  · -- **The full log lattice** `M = M' + ℤ·e` is `M' × ℤ`, so has rank `(|T| - 1) + 1 = |T|`.
    haveI : Module.Free ℤ ↥(logLattice T) := free_logLattice T hTinf
    haveI : Module.Finite ℤ ↥(logLattice T) := finite_logLattice T hTinf
    have hinj : Function.Injective (unitLatticeProdHom T) := by
      rintro ⟨y, n⟩ ⟨y', n'⟩ h
      have hfun : (y : ↥T → ℝ) + n • oneVec T = (y' : ↥T → ℝ) + n' • oneVec T := by
        have h' := congrArg (fun z : ↥(unitLattice T) => (z : ↥T → ℝ)) h
        simpa [unitLatticeProdHom] using h'
      have hy0 : ∑ w : ↥T, (y : ↥T → ℝ) w = 0 :=
        (mem_sumZero (T := T) (f := (y : ↥T → ℝ))).mp (hlog_sumZero y.2)
      have hy0' : ∑ w : ↥T, (y' : ↥T → ℝ) w = 0 :=
        (mem_sumZero (T := T) (f := (y' : ↥T → ℝ))).mp (hlog_sumZero y'.2)
      have hn : n = n' := by
        have hsum := congrArg (fun g : ↥T → ℝ => ∑ w : ↥T, g w) hfun
        simp only [Pi.add_apply, Finset.sum_add_distrib] at hsum
        rw [hy0, hy0', zero_add, zero_add, hone_sum n, hone_sum n'] at hsum
        exact Int.cast_injective (mul_right_cancel₀ (Nat.cast_ne_zero.mpr hTnz) hsum)
      have hy : y = y' := by
        have h2 := hfun
        rw [hn] at h2
        exact Subtype.ext (add_right_cancel h2)
      exact Prod.ext hy hn
    have hsurj : Function.Surjective (unitLatticeProdHom T) := by
      rintro ⟨z, hz⟩
      obtain ⟨y, hy, n, rfl⟩ := (mem_unitLattice_iff (T := T)).mp hz
      exact ⟨(⟨y, hy⟩, n), Subtype.ext rfl⟩
    have equ : (↥(logLattice T) × ℤ) ≃ₗ[ℤ] ↥(unitLattice T) :=
      AddEquiv.toIntLinearEquiv (AddEquiv.ofBijective (unitLatticeProdHom T) ⟨hinj, hsurj⟩)
    rw [← LinearEquiv.finrank_eq equ]
    rw [Module.finrank_prod, Module.finrank_self, h1]
    rw [Module.finrank_pi, Nat.card_eq_fintype_card (α := ↥T)]
    omega
  · -- **The divisor lattice** is `∏_{w ∈ T} ℤ`.
    have e : (↥T → ℤ) ≃ₗ[ℤ] ↥(divisorLattice T) :=
      AddEquiv.toIntLinearEquiv (AddEquiv.ofBijective (divisorHom T) (divisorHom_bijective T))
    rw [← LinearEquiv.finrank_eq e]
    rw [Module.finrank_pi, Module.finrank_pi]

end NK.GlobalCFTdeep.LogLattice
