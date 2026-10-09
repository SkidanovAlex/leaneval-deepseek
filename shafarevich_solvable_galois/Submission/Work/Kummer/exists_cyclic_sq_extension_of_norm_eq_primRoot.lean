/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Existence of a cyclic extension of degree `n ^ 2` containing a cyclic Kummer extension

Let `L/K` be a finite cyclic Galois extension of degree `n`, let `ζ` be a primitive `n`-th root
of unity in `K`, and let `η : Lˣ` be a unit of norm `ζ`.  Then `L` is contained in a cyclic
Galois extension `M/K` of degree `n ^ 2`.

The construction is the classical Kummer-theoretic one: by Hilbert 90 there is `μ : Lˣ` with
`σ μ = η ^ n · μ` (where `σ` generates `Gal(L/K)`), and one takes `M = L(β)` with `β ^ n = μ`.
The map `σ` extends to an automorphism `τ` of `M` with `τ β = η β`; its `n`-th power sends `β`
to `ζ β`, so `τ` has order `n ^ 2 = [M : K]`, and hence `M/K` is cyclic Galois of degree `n ^ 2`.
-/
import Mathlib
import Submission.Work.Kummer.Defs
import Submission.Work.Kummer.exists_algEquiv_div_of_norm_eq_one
import Submission.Work.Kummer.norm_eq_prod_zpowers
import Submission.Work.Kummer.irreducible_X_pow_sub_C_iff_of_isPrimitiveRoot
import Submission.Work.Kummer.dvd_of_pow_eq_nth_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Kummer

open Polynomial

universe u v w

theorem exists_cyclic_sq_extension_of_norm_eq_primRoot {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hn : Module.finrank K L = n)
    (η : Lˣ) (hη : Algebra.norm K (η : L) = ζ) :
    ∃ (M : Type v) (_ : Field M) (_ : Algebra K M) (_ : Algebra L M) (_ : IsScalarTower K L M)
      (_ : FiniteDimensional K M) (_ : IsGalois K M) (_ : IsCyclic Gal(M/K)),
      Module.finrank K M = n ^ 2 := by
  classical
  rcases eq_or_ne n 1 with hn1 | hn1
  · subst hn1
    refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, ?_⟩
    rw [hn]; norm_num
  · have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hn2 : 2 ≤ n := by omega
    have hζne : ζ ≠ 1 := hζ.ne_one hn2
    obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
    have hσorder : orderOf σ = n := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank, hn]
    have hσpow : σ ^ n = 1 := by
      rw [← hσorder]; exact pow_orderOf_eq_one σ
    have hnorm : Algebra.norm K ((η : L) ^ n) = 1 := by
      rw [map_pow, hη, hζ.pow_eq_one]
    obtain ⟨μ, hμ0⟩ := exists_algEquiv_div_of_norm_eq_one hσ hnorm
    have hμ : (σ : L ≃ₐ[K] L) (μ : L) = (η : L) ^ n * (μ : L) := by
      rw [hμ0, div_mul_cancel₀ _ (Units.ne_zero μ)]
    have hμne : (μ : L) ≠ 0 := Units.ne_zero μ
    let zL : L := algebraMap K L ζ
    have hzL : IsPrimitiveRoot zL n := hζ.map_of_injective (algebraMap K L).injective
    have hirr : Irreducible (Polynomial.X ^ n - Polynomial.C (μ : L)) := by
      refine (irreducible_X_pow_sub_C_iff_of_isPrimitiveRoot (K := L) (a := (μ : L)) (ζ := zL) hzL).mpr ?_
      intro m hmpos hmlt c hc
      have hcne : c ≠ 0 := by
        intro hc0
        rw [hc0, zero_pow (NeZero.ne n)] at hc
        exact hμne ((pow_eq_zero_iff (show m ≠ 0 by omega)).mp hc.symm)
      have hc' : μ ^ m = (Units.mk0 c hcne) ^ n := by
        apply Units.ext
        simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
        exact hc.symm
      have hdvd : n ∣ m := dvd_of_pow_eq_nth_pow hζ hn η hη hμ hc'
      have := Nat.le_of_dvd hmpos hdvd
      omega
    let f : Polynomial L := Polynomial.X ^ n - Polynomial.C (μ : L)
    have hfmonic : f.Monic := Polynomial.monic_X_pow_sub_C (μ : L) (NeZero.ne n)
    have hfne : f ≠ 0 := hfmonic.ne_zero
    haveI : Fact (Irreducible f) := ⟨hirr⟩
    let M : Type v := AdjoinRoot f
    haveI hFLM : FiniteDimensional L M := by
      haveI := hfmonic.finite_adjoinRoot; infer_instance
    haveI hFKM : FiniteDimensional K M := FiniteDimensional.trans K L M
    let β : M := AdjoinRoot.root f
    have hβ : β ^ n = algebraMap L M (μ : L) := root_X_pow_sub_C_pow n (μ : L)
    have hβne : β ≠ 0 := by
      intro h
      rw [h, zero_pow (NeZero.ne n)] at hβ
      exact hμne ((map_eq_zero (algebraMap L M)).mp hβ.symm)
    let i : L →ₐ[K] M := (IsScalarTower.toAlgHom K L M).comp (σ : L →ₐ[K] L)
    have hx : Polynomial.eval₂ i ((algebraMap L M) (η : L) * β) f = 0 := by
      have h1 : Polynomial.eval₂ i ((algebraMap L M) (η : L) * β) f
          = ((algebraMap L M) (η : L) * β) ^ n - i (μ : L) := by simp [f]
      rw [h1, sub_eq_zero, mul_pow, hβ]
      have hiμ : i (μ : L) = (algebraMap L M) (η : L) ^ n * (algebraMap L M) (μ : L) := by
        change (IsScalarTower.toAlgHom K L M) ((σ : L ≃ₐ[K] L) (μ : L)) = _
        rw [IsScalarTower.toAlgHom_apply, hμ, map_mul, map_pow]
      rw [hiμ]
    let τa : M →ₐ[K] M := AdjoinRoot.liftAlgHom f i ((algebraMap L M) (η : L) * β) hx
    have hτa_inj : Function.Injective τa := (τa.toRingHom).injective
    have hτa_surj : Function.Surjective τa :=
      LinearMap.surjective_of_injective (f := τa.toLinearMap) hτa_inj
    let τ : M ≃ₐ[K] M := AlgEquiv.ofBijective τa ⟨hτa_inj, hτa_surj⟩
    have hτβ : τ β = (algebraMap L M) (η : L) * β :=
      AdjoinRoot.liftAlgHom_root (p := f) (i := i) (x := (algebraMap L M) (η : L) * β) hx
    have hτof : ∀ l : L, τ (algebraMap L M l) = algebraMap L M ((σ : L ≃ₐ[K] L) l) := by
      intro l
      show (AdjoinRoot.liftAlgHom f i ((algebraMap L M) (η : L) * β) hx) (AdjoinRoot.of f l)
        = algebraMap L M ((σ : L ≃ₐ[K] L) l)
      rw [AdjoinRoot.liftAlgHom_of]
      change (IsScalarTower.toAlgHom K L M) ((σ : L ≃ₐ[K] L) l)
        = algebraMap L M ((σ : L ≃ₐ[K] L) l)
      rw [IsScalarTower.toAlgHom_apply]
    have hτk_of : ∀ k : ℕ, ∀ l : L, (τ ^ k) (algebraMap L M l)
        = algebraMap L M (((σ : L ≃ₐ[K] L) ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        have step : (τ ^ (k+1)) (algebraMap L M l)
            = (τ ^ k) (algebraMap L M ((σ : L ≃ₐ[K] L) l)) := by
          rw [pow_succ, AlgEquiv.mul_apply, hτof l]
        rw [step, ih]
        congr 1
    have hPk : ∀ k : ℕ, (∏ j ∈ Finset.range (k+1), ((σ : L ≃ₐ[K] L) ^ j) (η : L))
        = ((σ : L ≃ₐ[K] L) ^ k) (η : L) * (∏ j ∈ Finset.range k, ((σ : L ≃ₐ[K] L) ^ j) (η : L)) := by
      intro k
      rw [Finset.prod_range_succ, mul_comm]
    have hτpowβ : ∀ k : ℕ, (τ ^ k) β
        = (algebraMap L M) (∏ j ∈ Finset.range k, ((σ : L ≃ₐ[K] L) ^ j) (η : L)) * β := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have step : (τ ^ (k+1)) β = (τ ^ k) ((algebraMap L M) (η : L)) * (τ ^ k) β := by
          rw [pow_succ, AlgEquiv.mul_apply, hτβ, map_mul]
        rw [step, hτk_of k (η : L), ih, ← mul_assoc, ← map_mul, ← hPk k]
    have hτnβ : (τ ^ n) β = (algebraMap L M) zL * β := by
      rw [hτpowβ n]
      congr 1
      rw [← hn, ← norm_eq_prod_zpowers hσ (η : L), hη]
    have hzLn : zL ^ n = 1 := by
      show (algebraMap K L ζ) ^ n = 1
      rw [← map_pow, hζ.pow_eq_one, map_one]
    have hζM : ((algebraMap L M) zL) ^ n = 1 := by
      rw [← map_pow, hzLn, map_one]
    have hτn_ne : (τ ^ n) ≠ 1 := by
      intro h
      have hb := congrArg (fun g : M ≃ₐ[K] M => g β) h
      simp only [AlgEquiv.one_apply] at hb
      rw [hτnβ] at hb
      have h1 : (algebraMap L M) zL = 1 := mul_right_cancel₀ hβne (by rw [hb, one_mul])
      have h2 : zL = 1 := (algebraMap L M).injective (by rw [h1, map_one])
      exact hζne ((algebraMap K L).injective (by rw [map_one]; exact h2))
    have hρpowβ : ∀ k : ℕ, ((τ ^ n) ^ k) β = ((algebraMap L M) zL) ^ k * β := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have step : ((τ ^ n) ^ (k+1)) β = ((τ ^ n) ^ k) ((algebraMap L M) zL * β) := by
          rw [pow_succ, AlgEquiv.mul_apply, hτnβ]
        rw [step, map_mul]
        have hfix : ((τ ^ n) ^ k) ((algebraMap L M) zL) = (algebraMap L M) zL := by
          rw [← pow_mul, hτk_of (n*k) zL]
          rw [show (σ : L ≃ₐ[K] L) ^ (n*k) = 1 from by rw [pow_mul, hσpow, one_pow],
            AlgEquiv.one_apply]
        rw [hfix, ih, ← mul_assoc, ← pow_succ']
    have hgen : ∀ g : M ≃ₐ[K] M,
        (∀ l : L, g (algebraMap L M l) = algebraMap L M l) → g β = β → g = 1 := by
      intro g hfixl hβg
      have h1 : g.toRingHom = (1 : M →+* M) := by
        apply AdjoinRoot.ringHom_ext
        · ext l
          show g (algebraMap L M l) = algebraMap L M l
          exact hfixl l
        · show g β = β
          exact hβg
      apply AlgEquiv.ext
      intro x
      have h2 := congrArg (fun f : M →+* M => f x) h1
      show g x = x
      simpa using h2
    have hτnsq : τ ^ (n ^ 2) = 1 := by
      have hρn : (τ ^ n) ^ n = 1 := by
        apply hgen
        · intro l
          rw [← pow_mul, hτk_of (n*n) l]
          rw [show (σ : L ≃ₐ[K] L) ^ (n*n) = 1 from by rw [pow_mul, hσpow, one_pow],
            AlgEquiv.one_apply]
        · rw [hρpowβ n, hζM, one_mul]
      rw [pow_two, pow_mul, hρn]
    have horder : orderOf τ = n ^ 2 := by
      rw [orderOf_eq_iff (by positivity)]
      refine ⟨hτnsq, ?_⟩
      intro m hm hpos hm1
      have hσm : (σ : L ≃ₐ[K] L) ^ m = 1 := by
        apply AlgEquiv.ext
        intro l
        have h := congrArg (fun g : M ≃ₐ[K] M => g (algebraMap L M l)) hm1
        rw [hτk_of m l] at h
        simp only [AlgEquiv.one_apply] at h
        exact (algebraMap L M).injective h
      have hnm : n ∣ m := by
        rw [← hσorder]; exact orderOf_dvd_iff_pow_eq_one.mpr hσm
      obtain ⟨k, rfl⟩ := hnm
      have hk : k < n := by
        have : n * k < n * n := by rw [← pow_two]; exact hm
        exact Nat.lt_of_mul_lt_mul_left this
      have hb := congrArg (fun g : M ≃ₐ[K] M => g β) hm1
      simp only [AlgEquiv.one_apply] at hb
      rw [pow_mul τ n k, hρpowβ k] at hb
      have h1 : ((algebraMap L M) zL) ^ k = 1 := mul_right_cancel₀ hβne (by rw [hb, one_mul])
      have h2 : zL ^ k = 1 := (algebraMap L M).injective (by rw [map_pow, h1, map_one])
      have hzk : ζ ^ k = 1 := (algebraMap K L).injective (by rw [map_pow, map_one]; exact h2)
      have hnk : n ∣ k := hζ.dvd_of_pow_eq_one k hzk
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · rw [hk0, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
        · exact hk0
      have := Nat.le_of_dvd hkpos hnk
      omega
    have hfinL : Module.finrank L M = n := by
      show Module.finrank L (AdjoinRoot f) = n
      rw [PowerBasis.finrank (AdjoinRoot.powerBasis hfne), AdjoinRoot.powerBasis_dim hfne]
      exact Polynomial.natDegree_X_pow_sub_C
    have hfinK : Module.finrank K M = n ^ 2 := by
      rw [← Module.finrank_mul_finrank K L M, hn, hfinL, pow_two]
    have hcard_le : Nat.card Gal(M/K) ≤ Module.finrank K M := by
      rw [Nat.card_eq_fintype_card]
      exact AlgEquiv.card_le
    have hcard : Nat.card Gal(M/K) = Module.finrank K M :=
      le_antisymm hcard_le (by
        rw [hfinK]
        calc n ^ 2 = orderOf τ := horder.symm
          _ = Nat.card (Subgroup.zpowers τ) := (Nat.card_zpowers τ).symm
          _ ≤ Nat.card Gal(M/K) :=
              Nat.card_le_card_of_injective (fun x : ↥(Subgroup.zpowers τ) => (x : Gal(M/K)))
                Subtype.val_injective)
    haveI : IsGalois K M := IsGalois.of_card_aut_eq_finrank K M hcard
    haveI : IsCyclic Gal(M/K) := by
      rw [isCyclic_iff_exists_zpowers_eq_top]
      exact ⟨τ, Subgroup.eq_top_of_card_eq (Subgroup.zpowers τ) (by
        rw [Nat.card_zpowers, horder, hcard]; exact hfinK.symm)⟩
    exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, hfinK⟩

end Work.Kummer
