import Mathlib
import Submission.Work.Kummer.Defs
import Submission.Work.Kummer.exists_algEquiv_apply_eq_mul_of_pow_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Kummer

theorem exists_zpowers_generator_apply_eq_primRoot_mul {K : Type u} {L : Type v} [Field K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hn : Module.finrank K L = n) :
    ∃ (α : L) (a : K) (σ : Gal(L/K)), α ^ n = algebraMap K L a ∧
      IntermediateField.adjoin K {α} = ⊤ ∧ (∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ) ∧
      (σ : L ≃ₐ[K] L) α = algebraMap K L ζ * α := by
  classical
  -- A primitive `finrank`-th root of unity of `K`.
  have hK : (primitiveRoots (Module.finrank K L) K).Nonempty :=
    hn.symm ▸ primitiveRoots_nonempty hζ
  -- The Kummer generator supplied by Kummer theory: `K⟮α⟯ = ⊤` with `α ^ [L:K] ∈ K`.
  obtain ⟨α, hαpow, hαtop⟩ := exists_root_adjoin_eq_top_of_isCyclic K L hK
  obtain ⟨a, ha⟩ := hαpow
  have ha' : α ^ n = algebraMap K L a := by rw [← hn]; exact ha.symm
  -- `ζ` viewed as an element of the group of `n`-th roots of unity of `K`.
  let μ : rootsOfUnity n K :=
    ⟨primRootUnit hζ, by
      rw [mem_rootsOfUnity', primRootUnit_coe hζ]
      exact hζ.pow_eq_one⟩
  have hμcoe : (((μ : rootsOfUnity n K) : Kˣ) : K) = ζ := by
    change ((primRootUnit hζ : Kˣ) : K) = ζ
    exact primRootUnit_coe hζ
  -- A `K`-automorphism of `L` sending `α` to `ζ * α`.
  obtain ⟨σ, hσmul⟩ := exists_algEquiv_apply_eq_mul_of_pow_eq hζ ha' hαtop hn μ
  rw [hμcoe] at hσmul
  -- The order of `σ` is `n`.
  have hcard : Nat.card Gal(L/K) = n := (IsGalois.card_aut_eq_finrank K L).trans hn
  have hσn : σ ^ n = 1 := by
    have := pow_card_eq_one' (G := Gal(L/K)) (x := σ)
    rwa [hcard] at this
  have hdvd1 : orderOf σ ∣ n := orderOf_dvd_iff_pow_eq_one.mpr hσn
  -- Powers of the eigenvector.
  have hσpow : ∀ k : ℕ, (σ ^ k) α = (algebraMap K L ζ) ^ k * α := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, AlgEquiv.commutes, hσmul,
        ← mul_assoc, pow_succ]
  -- `n` divides the order of `σ`.
  have hdvd2 : n ∣ orderOf σ := by
    rcases eq_or_ne n 1 with hn1 | hn1
    · rw [hn1]; exact one_dvd _
    · -- since `n ≠ 1` the generator `α` cannot vanish
      have hαne : α ≠ 0 := by
        intro h0
        have hfin1 : Module.finrank K L = 1 := by
          have htopbot : (⊤ : IntermediateField K L) = ⊥ := by
            rw [← hαtop, h0, IntermediateField.adjoin_zero]
          have h2 : Module.finrank K (⊤ : IntermediateField K L) = Module.finrank K L :=
            (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv.finrank_eq
          rw [← h2, htopbot, IntermediateField.finrank_bot]
        omega
      have hfix : (algebraMap K L ζ) ^ orderOf σ * α = α := by
        have h := hσpow (orderOf σ)
        rw [pow_orderOf_eq_one, AlgEquiv.one_apply] at h
        exact h.symm
      have hζpow : (algebraMap K L ζ) ^ orderOf σ = 1 :=
        mul_right_cancel₀ hαne (by rw [hfix, one_mul])
      have hζpow' : ζ ^ orderOf σ = 1 := by
        apply (algebraMap K L).injective
        rw [map_pow, map_one]
        exact hζpow
      exact (hζ.pow_eq_one_iff_dvd (orderOf σ)).mp hζpow'
  have hσorder : orderOf σ = n := Nat.dvd_antisymm hdvd1 hdvd2
  -- Hence `σ` generates `Gal(L/K)`.
  haveI : Finite (Subgroup.zpowers σ) :=
    Nat.finite_of_card_ne_zero
      (by rw [Nat.card_zpowers, hσorder]; exact NeZero.ne n)
  have hgen : Subgroup.zpowers σ = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, hσorder, hcard]
  exact ⟨α, a, σ, ha', hαtop, fun x => by rw [hgen]; exact Subgroup.mem_top x, hσmul⟩

end Work.Kummer
