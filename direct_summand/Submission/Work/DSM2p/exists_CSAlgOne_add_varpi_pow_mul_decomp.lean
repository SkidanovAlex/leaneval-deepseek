import Mathlib
import Submission.Work.DSM2p.LamOne
import Submission.Work.DSM2p.Basic

/-!
# The `Λ + ϖ ^ p A_∞` decomposition of the one-polynomial Česnavičius–Scholze ring

This is the one-variable counterpart of
`Submission/Work.DSM2p.exists_eq_add_varpi_mul_of_pow_mem_CSAlgPos`'s helper
`exists_rootAlg_add_varpi_pow_mul_decomp`: the construction ring

`A_∞ = CSAlgOne A p ϖ F = Λ[F(T_F)/ϖ ^ m | m]`  (`Λ = Lam1 A p = A[T^{1/p^∞}]`)

is the subring `Λ + ϖ ^ p A_∞` of `Λ[1/ϖ]`: each generator `F(T_F)/ϖ ^ m` equals
`ϖ ^ p · (F(T_F)/ϖ ^ (m + p))`, and the second factor is again in `A_∞`.

The proof is the same as in the multi-variable case and uses nothing about `F`.
-/

open scoped Classical

-- The rings `Lam1 A p` and `Lam1Loc A p ϖ` are a quotient of an `MvPolynomial` ring and a
-- localization, so the default heartbeat budget is not enough for the instance searches below.
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

namespace Work.DSM2p

universe u

/-- **The `Λ + ϖ ^ p A_∞` decomposition of `A_∞ = CSAlgOne`.** -/
theorem exists_CSAlgOne_add_varpi_pow_mul_decomp (p : ℕ) (A : Type*) [CommRing A] (ϖ : A)
    (F : Polynomial A) :
    ∀ x ∈ CSAlgOne A p ϖ F, ∃ (l : Lam1 A p) (y : Lam1Loc A p ϖ),
      y ∈ CSAlgOne A p ϖ F ∧
      x = algebraMap (Lam1 A p) (Lam1Loc A p ϖ) l
        + (algebraMap A (Lam1Loc A p ϖ) ϖ) ^ p * y := by
  have hmap : algebraMap A (Lam1Loc A p ϖ) ϖ
      = algebraMap (Lam1 A p) (Lam1Loc A p ϖ) (algebraMap A (Lam1 A p) ϖ) :=
    IsScalarTower.algebraMap_apply A (Lam1 A p) (Lam1Loc A p ϖ) ϖ
  have hmemΛ : ∀ l : Lam1 A p,
      algebraMap (Lam1 A p) (Lam1Loc A p ϖ) l ∈ CSAlgOne A p ϖ F :=
    fun l => Subring.subset_closure (Set.mem_union_left _ ⟨l, rfl⟩)
  have hmemϖ : algebraMap A (Lam1Loc A p ϖ) ϖ ∈ CSAlgOne A p ϖ F := by
    rw [hmap]; exact hmemΛ _
  have hmemGen : ∀ m : ℕ,
      frac A p ϖ (Polynomial.aeval (T1 A p 0) F) m ∈ CSAlgOne A p ϖ F :=
    fun m => Subring.subset_closure (Set.mem_union_right _ ⟨m, rfl⟩)
  -- the set of elements admitting such a decomposition is a subring of `Λ[1/ϖ]`
  let D : Subring (Lam1Loc A p ϖ) :=
    { carrier := {x | ∃ (l : Lam1 A p) (y : Lam1Loc A p ϖ),
        y ∈ CSAlgOne A p ϖ F ∧
        x = algebraMap (Lam1 A p) (Lam1Loc A p ϖ) l
          + (algebraMap A (Lam1Loc A p ϖ) ϖ) ^ p * y}
      mul_mem' := by
        rintro a b ⟨l₁, y₁, hy₁, h₁⟩ ⟨l₂, y₂, hy₂, h₂⟩
        refine ⟨l₁ * l₂,
          y₁ * algebraMap (Lam1 A p) (Lam1Loc A p ϖ) l₂
            + (algebraMap (Lam1 A p) (Lam1Loc A p ϖ) l₁ * y₂
              + (algebraMap A (Lam1Loc A p ϖ) ϖ) ^ p * (y₁ * y₂)), ?_, ?_⟩
        · exact add_mem (mul_mem hy₁ (hmemΛ l₂)) (add_mem (mul_mem (hmemΛ l₁) hy₂)
            (mul_mem (pow_mem hmemϖ p) (mul_mem hy₁ hy₂)))
        · rw [h₁, h₂, map_mul]
          ring
      add_mem' := by
        rintro a b ⟨l₁, y₁, hy₁, h₁⟩ ⟨l₂, y₂, hy₂, h₂⟩
        exact ⟨l₁ + l₂, y₁ + y₂, add_mem hy₁ hy₂, by rw [h₁, h₂, map_add]; ring⟩
      zero_mem' := ⟨0, 0, (CSAlgOne A p ϖ F).zero_mem, by simp⟩
      one_mem' := ⟨1, 0, (CSAlgOne A p ϖ F).zero_mem, by simp⟩
      neg_mem' := by
        rintro a ⟨l, y, hy, h⟩
        exact ⟨-l, -y, neg_mem hy, by rw [h, map_neg]; ring⟩ }
  -- each generator of `CSAlgOne` lies in `D`
  have hgen : (Set.range (algebraMap (Lam1 A p) (Lam1Loc A p ϖ)) ∪
      Set.range (fun m : ℕ => frac A p ϖ (Polynomial.aeval (T1 A p 0) F) m)) ⊆ (D : Set _) := by
    rintro y (⟨l, rfl⟩ | ⟨m, rfl⟩)
    · exact ⟨l, 0, (CSAlgOne A p ϖ F).zero_mem, by simp⟩
    · change frac A p ϖ (Polynomial.aeval (T1 A p 0) F) m ∈ (D : Set _)
      rw [frac]
      have hmul : (algebraMap A (Lam1Loc A p ϖ) ϖ) *
          IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ) = 1 := by
        rw [hmap]
        exact IsLocalization.Away.mul_invSelf (R := Lam1 A p)
          (S := Lam1Loc A p ϖ) (algebraMap A (Lam1 A p) ϖ)
      have hpow : (algebraMap A (Lam1Loc A p ϖ) ϖ) ^ p *
          IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ) ^ p = 1 := by
        rw [← mul_pow, hmul, one_pow]
      have h1 : IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ) ^ m
          = (algebraMap A (Lam1Loc A p ϖ) ϖ) ^ p *
            IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ) ^ (m + p) := by
        calc IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ) ^ m
            = IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ) ^ m * 1 :=
              (mul_one _).symm
          _ = IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ) ^ m *
                ((algebraMap A (Lam1Loc A p ϖ) ϖ) ^ p *
                  IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ) ^ p) := by
              rw [hpow]
          _ = (algebraMap A (Lam1Loc A p ϖ) ϖ) ^ p *
                (IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ) ^ m *
                  IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ) ^ p) := by
              ring
          _ = (algebraMap A (Lam1Loc A p ϖ) ϖ) ^ p *
                IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ) ^ (m + p) := by
              rw [pow_add]
      exact ⟨0, algebraMap (Lam1 A p) (Lam1Loc A p ϖ)
          (Polynomial.aeval (T1 A p 0) F) *
          IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ) ^ (m + p),
        hmemGen (m + p), by rw [map_zero, zero_add, h1]; ring⟩
  intro x hx
  exact Subring.closure_le.mpr hgen hx

end Work.DSM2p
