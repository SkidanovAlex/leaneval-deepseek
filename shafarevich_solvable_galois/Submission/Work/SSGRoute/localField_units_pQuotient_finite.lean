import Mathlib.Algebra.Order.Ring.Units
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.GlobalCFT.Place
import Submission.Work.SSGRoute.LocalFieldArith.finite_units_quotient_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness of `K_wˣ / (K_wˣ)^p` for a number field place `w`

For a number field `K`, a place `w` of `K` and a prime `p`, the quotient of the unit group
`K_wˣ` of the local field `K_w` by its subgroup of `p`-th powers is finite.

At a finite place `w = ofFinite 𝔭` this is the arithmetic statement
`Work.SSGRoute.LocalFieldArith.finite_units_quotient_adicCompletion`: `K_w = 𝔭.adicCompletion K`
is a local field, so `𝒪_wˣ ⧸ (𝒪_wˣ)^p` is finite (the deep principal units are `p`-th powers and
the principal units have finite index in `𝒪_wˣ`), and `K_wˣ ⧸ 𝒪_wˣ ≅ ℤ` shows that
`K_wˣ ⧸ (K_wˣ)^p` is `p` times that.

At an archimedean place `w` the local field is `ℝ` or `ℂ` (`InfinitePlace.isReal_or_isComplex`
together with `ringEquivRealOfIsReal` / `ringEquivComplexOfIsComplex`).  For `ℂ` the quotient is
trivial, since `ℂ` is algebraically closed so that `ℂˣ` is divisible.  For `ℝ` every positive
real is a `p`-th power (`exp (log x / p) ^ p = x`), and `ℝˣ ⧸ ℝ_{>0}` has two elements, so the
`p`-power subgroup `(ℝˣ)^p ⊇ ℝ_{>0}` has index at most `2`.
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute

noncomputable section

/-- **Every positive real is a `p`-th power.**  Hence the `p`-power subgroup of `ℝˣ` contains the
subgroup of positive units. -/
theorem posSubgroup_le_nthPowerSubgroup_real (p : ℕ) [Fact p.Prime] :
    Units.posSubgroup ℝ ≤ Work.Kummer.nthPowerSubgroup p ℝˣ := by
  intro u hu
  rw [Units.mem_posSubgroup] at hu
  rw [Work.Kummer.mem_nthPowerSubgroup]
  refine ⟨Units.mk0 (Real.exp (Real.log (u : ℝ) / p)) (Real.exp_ne_zero _), ?_⟩
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h1 : (p : ℝ) * (Real.log (u : ℝ) / p) = Real.log (u : ℝ) := by
    field_simp
  ext
  rw [Units.val_pow_eq_pow_val, Units.val_mk0]
  calc (Real.exp (Real.log (↑u) / ↑p)) ^ p
      = Real.exp ((p : ℝ) * (Real.log (↑u) / p)) := (Real.exp_nat_mul _ p).symm
    _ = Real.exp (Real.log (↑u)) := by rw [h1]
    _ = (↑u : ℝ) := Real.exp_log hu

/-- **The `p`-power quotient of `ℝˣ` is finite**: it is a quotient of `ℝˣ ⧸ ℝ_{>0}`, which has
two elements. -/
theorem finite_units_quotient_real (p : ℕ) [Fact p.Prime] :
    Finite (ℝˣ ⧸ Work.Kummer.nthPowerSubgroup p ℝˣ) := by
  have hle := posSubgroup_le_nthPowerSubgroup_real p
  haveI : (Units.posSubgroup ℝ).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, Units.index_posSubgroup]; norm_num
  haveI : (Work.Kummer.nthPowerSubgroup p ℝˣ).FiniteIndex := Subgroup.finiteIndex_of_le hle
  exact Subgroup.finite_quotient_of_finiteIndex

/-- **The `p`-power quotient of `ℂˣ` is trivial**: `ℂ` is algebraically closed, so every unit of
`ℂ` has a `p`-th root. -/
theorem nthPowerSubgroup_complex_eq_top (p : ℕ) [Fact p.Prime] :
    Work.Kummer.nthPowerSubgroup p ℂˣ = ⊤ := by
  ext x
  rw [Work.Kummer.mem_nthPowerSubgroup]
  constructor
  · intro _; exact Subgroup.mem_top x
  · intro _
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : ℂ) (Fact.out : p.Prime).pos
    have hz0 : z ≠ 0 := by
      intro hzz
      have hx0 : (x : ℂ) = 0 := by rw [← hz, hzz, zero_pow (Fact.out : p.Prime).ne_zero]
      exact Units.ne_zero x hx0
    exact ⟨Units.mk0 z hz0,
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0]; exact hz)⟩

/-- **The `p`-power quotient of `ℂˣ` is finite** (in fact trivial). -/
theorem finite_units_quotient_complex (p : ℕ) [Fact p.Prime] :
    Finite (ℂˣ ⧸ Work.Kummer.nthPowerSubgroup p ℂˣ) := by
  rw [nthPowerSubgroup_complex_eq_top p]
  exact Subgroup.finite_quotient_of_finiteIndex

/-- **Finiteness of `Gˣ ⧸ (Gˣ)^p` is invariant under ring isomorphisms.**  A ring isomorphism
`e : A ≃+* B` restricts to a group isomorphism `Aˣ ≃* Bˣ` carrying `p`-th powers to `p`-th
powers, hence inducing an isomorphism of the `p`-power quotients; the `p`-power subgroup of
`Bˣ` therefore has finite index iff that of `Aˣ` does. -/
theorem finite_units_quotient_nthPowerSubgroup_of_ringEquiv {A B : Type*} [Field A] [Field B]
    (e : A ≃+* B) (p : ℕ) (h : Finite (Bˣ ⧸ Work.Kummer.nthPowerSubgroup p Bˣ)) :
    Finite (Aˣ ⧸ Work.Kummer.nthPowerSubgroup p Aˣ) := by
  have he : Subgroup.map (Units.mapEquiv e.toMulEquiv) (Work.Kummer.nthPowerSubgroup p Aˣ) =
      Work.Kummer.nthPowerSubgroup p Bˣ := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rw [Work.Kummer.mem_nthPowerSubgroup] at hy ⊢
      obtain ⟨z, hz⟩ := hy
      refine ⟨Units.mapEquiv e.toMulEquiv z, ?_⟩
      rw [← hyx, ← hz]
      exact (map_pow _ z p).symm
    · intro hx
      rw [Work.Kummer.mem_nthPowerSubgroup] at hx
      obtain ⟨z, hz⟩ := hx
      rw [Subgroup.mem_map]
      refine ⟨((Units.mapEquiv e.toMulEquiv).symm z) ^ p,
        ⟨(Units.mapEquiv e.toMulEquiv).symm z, rfl⟩, ?_⟩
      calc (Units.mapEquiv e.toMulEquiv) (((Units.mapEquiv e.toMulEquiv).symm z) ^ p)
          = ((Units.mapEquiv e.toMulEquiv) ((Units.mapEquiv e.toMulEquiv).symm z)) ^ p :=
            map_pow _ _ _
        _ = z ^ p := by rw [MulEquiv.apply_symm_apply]
        _ = x := hz
  have hB : (Work.Kummer.nthPowerSubgroup p Bˣ).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hidx : (Work.Kummer.nthPowerSubgroup p Bˣ).index =
      (Work.Kummer.nthPowerSubgroup p Aˣ).index := by
    rw [← he]; exact Subgroup.index_map_equiv _ (Units.mapEquiv e.toMulEquiv)
  have hA : (Work.Kummer.nthPowerSubgroup p Aˣ).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff] at hB ⊢
    rw [← hidx]; exact hB
  haveI := hA
  exact Subgroup.finite_quotient_of_finiteIndex

/-- **The units of a number field local field, modulo `p`-th powers, are finite.**

At a finite place this is `Work.SSGRoute.LocalFieldArith.finite_units_quotient_adicCompletion`; at
an archimedean place the local field is `ℝ` or `ℂ` and we transport the corresponding finiteness
(`finite_units_quotient_real`, `finite_units_quotient_complex`) along the ring isomorphism
`ringEquivRealOfIsReal` / `ringEquivComplexOfIsComplex` using
`finite_units_quotient_nthPowerSubgroup_of_ringEquiv`. -/
theorem localField_units_pQuotient_finite (K : Type) [Field K] [NumberField K]
    (w : NK.GlobalCFT.Place K) (p : ℕ) [Fact p.Prime] :
    Finite ((NK.GlobalCFT.Place.localField K w)ˣ ⧸
      Work.Kummer.nthPowerSubgroup p ((NK.GlobalCFT.Place.localField K w)ˣ)) := by
  cases w with
  | inl wi =>
      rcases NumberField.InfinitePlace.isReal_or_isComplex wi with hreal | hcomplex
      · exact finite_units_quotient_nthPowerSubgroup_of_ringEquiv
          (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal) p
          (finite_units_quotient_real p)
      · exact finite_units_quotient_nthPowerSubgroup_of_ringEquiv
          (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hcomplex) p
          (finite_units_quotient_complex p)
  | inr q =>
      exact Work.SSGRoute.LocalFieldArith.finite_units_quotient_adicCompletion K q p

end

end Work.SSGRoute
