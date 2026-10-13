/-
Area DSCOH — a single-generator description of the degree-zero part of a chart localization.

`degZero ℳ S` is defined as the supremum `⨆_k ℳ(k·|S|)/X_S^k` of the images of the graded
pieces `ℳ (k·|S|)` under `m ↦ m / X_S^k`.  For a graded module (`SetLike.GradedSMul (homSub A n) ℳ`)
multiplication by `X_S = ∏_{i∈S} Xᵢ` shifts the grading by exactly `|S|`, so
`X_S · ℳ(k·|S|) ⊆ ℳ((k+1)·|S|)` and `X_S·m / X_S^{k+1} = m / X_S^k`; the pieces therefore form
an increasing chain and the supremum is a *directed union*.  Consequently every element of
`degZero ℳ S` is `m / X_S^k` for a **single** `k` and `m ∈ ℳ(k·|S|)`.
-/
import Mathlib
import Submission.Work.DSCOH.Basic
import Submission.Work.DSCOH.divPow_toLoc_mem

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
  [IsScalarTower A (Poly A n) M]

/-! ## Elementary lemmas about the generators `m / X_S^k` -/

/-- `m / X_S^k` is the explicit fraction with denominator `(∏_{i∈S} Xᵢ)^k`. -/
private lemma dz_divPow_toLoc_eq_mk (S : Finset (Fin n)) (k : ℕ) (m : M) :
    divPow (A := A) (M := M) S k (toLoc (A := A) (M := M) S m) =
      LocalizedModule.mk m ⟨monomial (A := A) S ^ k,
        Submonoid.pow_mem (subS (A := A) S) (monomial_mem (A := A) S) k⟩ := by
  unfold divPow toLoc
  simp only [LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply,
    LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk, one_mul]

/-- The presentation of a generator is stable under raising the index:
`m / X_S^k = (X_S^j · m) / X_S^{k+j}`. -/
private lemma dz_divPow_toLoc_smul_monomial_pow (S : Finset (Fin n)) (k j : ℕ) (m : M) :
    divPow (A := A) (M := M) S (k + j)
        (toLoc (A := A) (M := M) S ((monomial (A := A) S) ^ j • m)) =
      divPow (A := A) (M := M) S k (toLoc (A := A) (M := M) S m) := by
  have h1 := dz_divPow_toLoc_eq_mk (A := A) (M := M) (S := S) (k := k + j)
    (m := (monomial (A := A) S) ^ j • m)
  have h2 := dz_divPow_toLoc_eq_mk (A := A) (M := M) (S := S) (k := k) (m := m)
  rw [h1, h2, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, smul_smul, ← pow_add]

/-! ## Homogeneity of `X_S` -/

/-- The product of the variables in `S` is homogeneous of degree `|S|`. -/
private lemma dz_monomial_mem_homSub (S : Finset (Fin n)) :
    monomial (A := A) S ∈ homSub A n S.card := by
  rw [homSub, MvPolynomial.mem_homogeneousSubmodule]
  unfold monomial Var
  simpa using MvPolynomial.IsHomogeneous.prod (R := A) S (fun i => MvPolynomial.X i)
    (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X A i)

/-- Its `j`-th power is homogeneous of degree `j·|S|`. -/
private lemma dz_monomial_pow_mem_homSub (S : Finset (Fin n)) (j : ℕ) :
    (monomial (A := A) S) ^ j ∈ homSub A n (j * S.card) := by
  rw [homSub, MvPolynomial.mem_homogeneousSubmodule]
  have h1 : (monomial (A := A) S).IsHomogeneous S.card := by
    unfold monomial Var
    simpa using MvPolynomial.IsHomogeneous.prod (R := A) S (fun i => MvPolynomial.X i)
      (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X A i)
  simpa only [mul_comm] using h1.pow j

/-! ## The single-generator description -/

theorem degZero_exists_repr {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ]
    (S : Finset (Fin n)) {x : locAt (A := A) (M := M) S} (hx : x ∈ degZero ℳ S) :
    ∃ (k : ℕ) (m : M), m ∈ ℳ (k * S.card) ∧
      x = divPow (A := A) (M := M) S k (toLoc (A := A) (M := M) S m) := by
  -- The pieces `ℳ(k|S|)/X_S^k` are increasing in `k`.
  have hmono : Monotone (fun k : ℕ => Submodule.map
      ((divPow (A := A) (M := M) S k).comp (toLoc (A := A) (M := M) S))
      (ℳ (k * S.card))) := by
    apply monotone_nat_of_le_succ
    intro k
    rintro _ ⟨m, hm, rfl⟩
    refine Submodule.mem_map.mpr ⟨(monomial (A := A) S) ^ 1 • m, ?_, ?_⟩
    · rw [pow_one]
      have hsm := SetLike.GradedSMul.smul_mem (dz_monomial_mem_homSub (A := A) (n := n) S) hm
      rwa [show S.card +ᵥ (k * S.card) = (k + 1) * S.card from by
        rw [show S.card +ᵥ (k * S.card) = S.card + k * S.card from rfl]; ring] at hsm
    · show divPow (A := A) (M := M) S (k + 1)
          (toLoc (A := A) (M := M) S ((monomial (A := A) S) ^ 1 • m)) =
        divPow (A := A) (M := M) S k (toLoc (A := A) (M := M) S m)
      exact dz_divPow_toLoc_smul_monomial_pow (A := A) (M := M) S k 1 m
  have hx' : x ∈ ⨆ k : ℕ, Submodule.map
      ((divPow (A := A) (M := M) S k).comp (toLoc (A := A) (M := M) S))
      (ℳ (k * S.card)) := hx
  obtain ⟨k, m, hm, hmy⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hx'
  exact ⟨k, m, hm, hmy.symm⟩

end Work.DSCOH
