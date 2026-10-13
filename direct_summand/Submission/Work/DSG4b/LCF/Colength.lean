import Submission.Work.DSG4b.LCF.Basic
import Submission.Work.DSG4b.LCF.injective_lTensor_of_sup_span

/-!
# The colength case of the local criterion of flatness

If `M ⊗[R] I → M ⊗[R] R` is injective for the maximal ideal `𝔪` of a local ring `R`, then it is
injective for every ideal `J` containing a power of `𝔪` (`R/J` of finite length).  This is
Stacks 00MJ (the easy direction of the local criterion of flatness).

The proof is the "infinite descent" argument: if `J` is a counterexample, take a maximal
counterexample `K ≥ J`, note that `K ⊊ R` is impossible because one can always enlarge `K` by an
element `x ∈ 𝔪^j \ K` with `𝔪 x ⊆ K` (this is the step lemma
`injective_lTensor_of_sup_span`), and finally enlarge `K` to `R`.
-/

namespace Work.DSG4b.LCF

open TensorProduct LinearMap

section Top

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The inclusion `⊤ → R` induces an injective map after tensoring with any module `M`. -/
lemma injective_lTensor_subtype_top :
    Function.Injective (LinearMap.lTensor M (Submodule.subtype (⊤ : Ideal R))) := by
  have hg : (Submodule.topEquiv (R := R) (M := R)).symm.toLinearMap ∘ₗ
      Submodule.subtype (⊤ : Ideal R) = LinearMap.id := by
    ext x
    simp [Submodule.topEquiv]
  intro x y hxy
  have h : ∀ z, LinearMap.lTensor M ((Submodule.topEquiv (R := R) (M := R)).symm.toLinearMap)
      (LinearMap.lTensor M (Submodule.subtype (⊤ : Ideal R)) z) = z := by
    intro z
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hg, LinearMap.lTensor_id]
    rfl
  rw [← h x, hxy, h y]

end Top

section Colength

variable {R M : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup M]
  [Module R M]

/-- **Colength case of the local criterion of flatness** (Stacks 00MJ).  If tensoring the
inclusion `𝔪 → R` with `M` is injective, then tensoring the inclusion `J → R` with `M` is
injective for every ideal `J` containing a power of `𝔪`. -/
theorem injective_lTensor_subtype_of_pow_le
    (h𝔪 : Function.Injective (LinearMap.lTensor M (IsLocalRing.maximalIdeal R).subtype))
    (J : Ideal R) (n : ℕ) (hn : IsLocalRing.maximalIdeal R ^ n ≤ J) :
    Function.Injective (LinearMap.lTensor M (Submodule.subtype J)) := by
  by_contra hJ
  set S : Set (Ideal R) :=
    {K | J ≤ K ∧ ¬ Function.Injective (LinearMap.lTensor M (Submodule.subtype K))} with hSdef
  obtain ⟨K, hKS, hKmax⟩ :=
    (inferInstance : WellFoundedGT (Ideal R)).exists_maximal S ⟨J, le_rfl, hJ⟩
  have hJK : J ≤ K := hKS.1
  have hKbad : ¬ Function.Injective (LinearMap.lTensor M (Submodule.subtype K)) := hKS.2
  -- main claim: `𝔪 ^ j ≤ K` for all `j ≤ n`
  have key : ∀ j, j ≤ n → IsLocalRing.maximalIdeal R ^ (n - j) ≤ K := by
    intro j
    induction j with
    | zero => intro _; simpa using hn.trans hJK
    | succ j ih =>
      intro hj
      by_contra hnot
      obtain ⟨x, hxmem, hxK⟩ :
          ∃ x, x ∈ IsLocalRing.maximalIdeal R ^ (n - (j + 1)) ∧ x ∉ K := by
        simpa [SetLike.le_def, not_forall] using hnot
      have hj' : j ≤ n := Nat.le_of_succ_le hj
      have hprev : IsLocalRing.maximalIdeal R ^ (n - j) ≤ K := ih hj'
      have hmul : ∀ a ∈ IsLocalRing.maximalIdeal R, a * x ∈ K := by
        intro a ha
        have h2 : a * x ∈
            IsLocalRing.maximalIdeal R * IsLocalRing.maximalIdeal R ^ (n - (j + 1)) :=
          Ideal.mul_mem_mul ha hxmem
        have h3 : IsLocalRing.maximalIdeal R *
            IsLocalRing.maximalIdeal R ^ (n - (j + 1)) =
              IsLocalRing.maximalIdeal R ^ (n - j) := by
          rw [← pow_succ', show (n - (j + 1)) + 1 = n - j from by omega]
        exact hprev (h3 ▸ h2)
      have hbad' : ¬ Function.Injective
          (LinearMap.lTensor M (Submodule.subtype (K ⊔ Ideal.span {x}))) := fun hinj =>
        hKbad (injective_lTensor_of_sup_span K x hxK hmul h𝔪 hinj)
      have hle : K ≤ K ⊔ Ideal.span {x} := le_sup_left
      have hmem : (K ⊔ Ideal.span {x}) ∈ S := ⟨hJK.trans hle, hbad'⟩
      have hback : K ⊔ Ideal.span {x} ≤ K := hKmax hmem hle
      exact hxK (hback (Submodule.mem_sup_right (Ideal.mem_span_singleton_self x)))
  have htopK : K = ⊤ := le_antisymm le_top (by have := key n le_rfl; simpa using this)
  rw [htopK] at hKbad
  exact hKbad (injective_lTensor_subtype_top (M := M) (R := R))

end Colength

end Work.DSG4b.LCF
