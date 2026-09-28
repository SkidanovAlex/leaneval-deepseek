import Mathlib

/-!
# Structure of a finitely generated `ℤ`-module whose rationalisation embeds into `ℚ`

If `M` is a finitely generated `ℤ`-module and `ℚ ⊗[ℤ] M` admits an injective `ℚ`-linear map
into `ℚ`, then the free rank of `M` is at most one: `M ≃+ ℤ^r × F` with `r ≤ 1` and `F` finite.

The proof uses the structure theorem for finitely generated modules over a PID to write
`M ≃ₗ[ℤ] (Fin n →₀ ℤ) × T` with `T` a finite torsion module.  Tensoring the resulting
injection `ℤ^n ↪ M` by the flat `ℤ`-module `ℚ` produces an injection `ℚ^n ↪ ℚ ⊗[ℤ] M`, which
composed with the given injection gives an injection `ℚ^n ↪ ℚ`; two distinct rational numbers
are always `ℤ`-linearly dependent, so `n ≤ 1`.
-/

namespace Work.Rat.RankOneC1

open scoped DirectSum

set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

/-- Any rational number admits a common nonzero integer denominator: for `x : ℚ` there are
`q ≠ 0` and `p` with `q * x = p`. -/
lemma exists_int_mul_eq_of_rat (x : ℚ) : ∃ q : ℤ, q ≠ 0 ∧ ∃ p : ℤ, (q:ℚ) * x = (p:ℚ) := by
  refine ⟨(x.den : ℤ), by simp, x.num, ?_⟩
  have h := Rat.num_div_den x
  have hden : (x.den : ℚ) ≠ 0 := by simp
  rw [div_eq_iff hden] at h
  push_cast
  rw [mul_comm]
  exact h.symm

/-- There is no injective `ℤ`-linear map `ℚ^n → ℚ` for `n ≥ 2`: any two rationals are
`ℤ`-linearly dependent. -/
lemma nat_le_one_of_injective_rat_fin {n : ℕ} (F : (Fin n → ℚ) →ₗ[ℤ] ℚ)
    (hF : Function.Injective F) : n ≤ 1 := by
  by_contra hn
  rw [not_le] at hn
  have h0 : 0 < n := by omega
  have h1 : 1 < n := hn
  set i0 : Fin n := ⟨0, h0⟩ with hi0
  set i1 : Fin n := ⟨1, h1⟩ with hi1
  have hne : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [hi0, hi1] at this
  have ha : F (Pi.single i0 (1:ℚ)) ≠ 0 := by
    intro h
    have h1' : (Pi.single i0 (1:ℚ) : Fin n → ℚ) = 0 := hF (by simpa using h)
    have h2 := congrFun h1' i0
    simp [Pi.single_eq_same] at h2
  obtain ⟨q, hq, p, hpq⟩ := exists_int_mul_eq_of_rat
    (F (Pi.single i1 (1:ℚ)) / F (Pi.single i0 (1:ℚ)))
  have hprob : (q:ℚ) * F (Pi.single i1 (1:ℚ)) = (p:ℚ) * F (Pi.single i0 (1:ℚ)) := by
    have hcm := div_mul_cancel₀ (F (Pi.single i1 (1:ℚ))) ha
    calc (q:ℚ) * F (Pi.single i1 (1:ℚ))
        = (q:ℚ) * ((F (Pi.single i1 (1:ℚ)) / F (Pi.single i0 (1:ℚ))) *
            F (Pi.single i0 (1:ℚ))) := by rw [hcm]
      _ = ((q:ℚ) * (F (Pi.single i1 (1:ℚ)) / F (Pi.single i0 (1:ℚ)))) *
            F (Pi.single i0 (1:ℚ)) := by ring
      _ = (p:ℚ) * F (Pi.single i0 (1:ℚ)) := by rw [hpq]
  have hrel : p • F (Pi.single i0 (1:ℚ)) + (-q) • F (Pi.single i1 (1:ℚ)) = 0 := by
    rw [← Int.cast_smul_eq_zsmul (R := ℚ) p _, ← Int.cast_smul_eq_zsmul (R := ℚ) (-q) _]
    simp only [smul_eq_mul]
    push_cast
    linarith [hprob]
  have hz : p • (Pi.single i0 (1:ℚ) : Fin n → ℚ) + (-q) • (Pi.single i1 (1:ℚ) : Fin n → ℚ) = 0 := by
    apply hF
    rw [map_add, map_smul, map_smul, map_zero]
    exact hrel
  have hp0 : p = 0 := by
    have h := congrFun hz i0
    simp [Pi.single_eq_same, Pi.single_eq_of_ne hne] at h
    exact_mod_cast h
  have hq0 : q = 0 := by
    have h := congrFun hz i1
    simp [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne)] at h
    exact_mod_cast h
  exact hq hq0

theorem fg_ratModule_structure_of_ratEmbedding
    {M : Type*} [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M]
    {f : (↥((ModuleCat.extendScalars (Int.castRingHom ℚ)).obj (ModuleCat.of ℤ M))) →ₗ[ℚ] ℚ}
    (hf : Function.Injective f) :
    ∃ (r : ℕ) (F : Type) (_ : AddCommGroup F) (_ : Finite F), r ≤ 1 ∧
      Nonempty (M ≃+ (Fin r → ℤ) × F) := by
  obtain ⟨n, ι, fι, p, hp, e, ⟨φ⟩⟩ := Module.equiv_free_prod_directSum (R := ℤ) (M := M)
  let T := (⨁ i : ι, ℤ ⧸ Ideal.span {p i ^ e i})
  let l : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n →₀ ℤ) := (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).symm
  let los0 : (Fin n → ℤ) →+ ((Fin n →₀ ℤ) × T) :=
    { toFun := fun z => (l z, (0 : T))
      map_zero' := by simp
      map_add' := by intro a b; simp [map_add] }
  let s : (Fin n → ℤ) →ₗ[ℤ] M := φ.symm.toLinearMap.comp los0.toIntLinearMap
  have hs : Function.Injective s := by
    intro z1 z2 h
    have h2 : ((l z1, (0 : T)) : (Fin n →₀ ℤ) × T) = (l z2, 0) := φ.symm.injective h
    have h3 : l z1 = l z2 := (Prod.mk.injEq _ _ _ _).mp h2 |>.1
    exact l.injective h3
  let F' : TensorProduct ℤ ℚ M →ₗ[ℚ] ℚ := f
  let e' := TensorProduct.piScalarRight ℤ ℚ ℚ (Fin n)
  let H : (Fin n → ℚ) →ₗ[ℤ] ℚ :=
    (F'.restrictScalars ℤ).comp
      ((LinearMap.lTensor ℚ s).comp (e'.symm.toLinearMap.restrictScalars ℤ))
  have hH : Function.Injective H := by
    intro a b hab
    have h1 : LinearMap.lTensor ℚ s (e'.symm a) = LinearMap.lTensor ℚ s (e'.symm b) := hf hab
    have h2 : e'.symm a = e'.symm b :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := ℚ) s hs h1
    exact e'.symm.injective h2
  have hn : n ≤ 1 := nat_le_one_of_injective_rat_fin H hH
  have hfin : Finite T := by
    haveI : ∀ i : ι, Finite (ℤ ⧸ Ideal.span {p i ^ e i}) := fun i => by
      haveI : NeZero (p i ^ e i).natAbs :=
        ⟨Int.natAbs_ne_zero.mpr (pow_ne_zero (e i) (hp i).ne_zero)⟩
      exact Finite.of_equiv (ZMod (p i ^ e i).natAbs)
        (Int.quotientSpanEquivZMod (p i ^ e i)).symm.toEquiv
    exact Finite.of_equiv (Π i, ℤ ⧸ Ideal.span {p i ^ e i}) DFinsupp.equivFunOnFintype.symm
  exact ⟨n, T, inferInstance, hfin, hn,
    ⟨φ.toAddEquiv.trans ((l.toAddEquiv.symm).prodCongr (AddEquiv.refl T))⟩⟩

end Work.Rat.RankOneC1
