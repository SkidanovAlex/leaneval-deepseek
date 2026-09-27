import Mathlib

namespace Work.KT.D2

open Matrix LinearMap

/-- **An idempotent complex matrix is conjugate to a standard diagonal one.**  If `e` is
idempotent then there are `k, m` with `k + m = n`, an index reindexing
`ε : Fin k ⊕ Fin m ≃ Fin n` and an invertible `c` with `c * e = diag(1_k, 0_m) * c`, where
`diag(1_k, 0_m)` is `Matrix.fromBlocks 1 0 0 0` reindexed along `ε`.

Route: `E := Matrix.toLin' e` is idempotent, so `LinearMap.IsIdempotentElem.isProj_range` gives
`LinearMap.IsProj (LinearMap.range E) E` and `LinearMap.IsProj.isCompl` gives the complementary
pair `(range E, ker E)`; `LinearMap.IsProj.eq_conj_prodMap` exhibits
`E = P.conj (LinearMap.prodMap id 0)` for `P := (range E).prodEquivOfIsCompl (ker E) _`.  Take
`k := Module.finrank ℂ (range E)`, `m := Module.finrank ℂ (ker E)`
(`LinearMap.finrank_range_add_finrank_ker` gives `k + m = n` since `finrank ℂ (Fin n → ℂ) = n`),
identify `range E ≃ₗ (Fin k → ℂ)` and `ker E ≃ₗ (Fin m → ℂ)` by `LinearEquiv.ofFinrankEq`, and
build the linear equivalence `L : (Fin n → ℂ) ≃ₗ (Fin n → ℂ)` whose conjugate of `E` is the
standard projection; then `c := LinearMap.toMatrix' L` (with `Matrix.toLin'_toMatrix'`) satisfies
the identity because `toLin'` is injective, and `IsUnit c` because `L` is invertible. -/
theorem conj_std_idem (n : ℕ) (e : Matrix (Fin n) (Fin n) ℂ) (he : e * e = e) :
    ∃ (k m : ℕ) (ε : Fin k ⊕ Fin m ≃ Fin n) (c : Matrix (Fin n) (Fin n) ℂ),
      IsUnit c ∧
        c * e = Matrix.reindex ε ε
          (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0) * c := by
  classical
  set E : Module.End ℂ (Fin n → ℂ) := Matrix.toLin' e with hEdef
  have hE : IsIdempotentElem E := by
    rw [IsIdempotentElem, hEdef, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he]
  let k : ℕ := Module.finrank ℂ (LinearMap.range E)
  let m : ℕ := Module.finrank ℂ (LinearMap.ker E)
  have hkm : k + m = n := by
    have h := LinearMap.finrank_range_add_finrank_ker E
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    simpa [k, m] using h
  let ε : Fin k ⊕ Fin m ≃ Fin n := Fintype.equivOfCardEq (by simp [Fintype.card_sum, hkm])
  let φ : (LinearMap.range E) ≃ₗ[ℂ] (Fin k → ℂ) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [k, Module.finrank_fintype_fun_eq_card])
  let ψ : (LinearMap.ker E) ≃ₗ[ℂ] (Fin m → ℂ) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [m, Module.finrank_fintype_fun_eq_card])
  let P : (LinearMap.range E × LinearMap.ker E) ≃ₗ[ℂ] (Fin n → ℂ) :=
    (LinearMap.range E).prodEquivOfIsCompl (LinearMap.ker E) hE.isProj_range.isCompl
  have hconj : E = P.conj (LinearMap.id.prodMap 0) := hE.isProj_range.eq_conj_prodMap
  let R : (LinearMap.range E × LinearMap.ker E) ≃ₗ[ℂ]
      ((Fin k → ℂ) × (Fin m → ℂ)) := φ.prodCongr ψ
  let S : ((Fin k → ℂ) × (Fin m → ℂ)) ≃ₗ[ℂ]
      ((Fin k ⊕ Fin m) → ℂ) :=
    (LinearEquiv.sumArrowLequivProdArrow (Fin k) (Fin m) ℂ ℂ).symm
  let Mf : (Fin n → ℂ) ≃ₗ[ℂ] ((Fin k ⊕ Fin m) → ℂ) := P.symm.trans (R.trans S)
  let T : (Fin n → ℂ) ≃ₗ[ℂ] ((Fin k ⊕ Fin m) → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ ε
  let A : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℂ :=
    Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0
  -- the two projections `id × 0` on the two isomorphic models of the source
  let P0 : (LinearMap.range E × LinearMap.ker E) →ₗ[ℂ] (LinearMap.range E × LinearMap.ker E) :=
    LinearMap.prodMap LinearMap.id 0
  let P1 : ((Fin k → ℂ) × (Fin m → ℂ)) →ₗ[ℂ] ((Fin k → ℂ) × (Fin m → ℂ)) :=
    LinearMap.prodMap LinearMap.id 0
  -- `R` intertwines the two projections
  have hR_prod : ∀ z : (LinearMap.range E × LinearMap.ker E), R (P0 z) = P1 (R z) := by
    rintro ⟨a, b⟩
    simp [P0, P1, R, LinearEquiv.prodCongr_apply, LinearMap.prodMap_apply]
  -- and `S` conjugates `id × 0` to the standard block projection
  have hS_prod : ∀ w : ((Fin k → ℂ) × (Fin m → ℂ)),
      S (P1 w) = Matrix.toLin' A (S w) := by
    rintro ⟨a, b⟩
    ext i
    rcases i with p | p
    · simp [P1, S, A, Matrix.toLin'_apply, Matrix.fromBlocks_mulVec, LinearMap.prodMap_apply]
    · simp [P1, S, A, Matrix.toLin'_apply, Matrix.fromBlocks_mulVec, LinearMap.prodMap_apply]
  -- hence `Mf` turns `E` into the standard block projection
  have hM : ∀ x, Mf (E x) = Matrix.toLin' A (Mf x) := by
    intro x
    have hconjx : E x = P (P0 (P.symm x)) := by
      have h1 := congrArg (fun U : Module.End ℂ (Fin n → ℂ) => U x) hconj
      rw [LinearEquiv.conj_apply] at h1
      simpa [P0] using h1
    calc Mf (E x) = S (R (P0 (P.symm x))) := by
          rw [hconjx]
          simp [Mf, LinearEquiv.trans_apply]
      _ = S (P1 (R (P.symm x))) := by rw [hR_prod (P.symm x)]
      _ = Matrix.toLin' A (S (R (P.symm x))) := hS_prod (R (P.symm x))
      _ = Matrix.toLin' A (Mf x) := by
          rw [show Mf x = S (R (P.symm x)) from by simp [Mf, LinearEquiv.trans_apply]]
  -- reindexing `A` along `ε` conjugates by `T`
  have hQlin : Matrix.toLin' (Matrix.reindex ε ε A) =
      (T.symm : ((Fin k ⊕ Fin m) → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ Matrix.toLin' A ∘ₗ
        (T : (Fin n → ℂ) →ₗ[ℂ] ((Fin k ⊕ Fin m) → ℂ)) := by
    rw [Matrix.toLin'_reindex]
    simp [T, LinearEquiv.funCongrLeft_symm]
  -- the conjugating linear equivalence
  let L : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) := Mf.trans T.symm
  have hLint : ∀ x, L (E x) = Matrix.toLin' (Matrix.reindex ε ε A) (L x) := by
    intro x
    have hLx : (T : (Fin n → ℂ) →ₗ[ℂ] ((Fin k ⊕ Fin m) → ℂ)) (L x) = Mf x := by
      simp [L, LinearEquiv.trans_apply]
    calc L (E x) = T.symm (Mf (E x)) := by simp [L, LinearEquiv.trans_apply]
      _ = T.symm (Matrix.toLin' A (Mf x)) := by rw [hM x]
      _ = T.symm (Matrix.toLin' A ((T : (Fin n → ℂ) →ₗ[ℂ] ((Fin k ⊕ Fin m) → ℂ)) (L x))) := by
            rw [← hLx]
      _ = (T.symm ∘ₗ Matrix.toLin' A ∘ₗ T) (L x) := rfl
      _ = Matrix.toLin' (Matrix.reindex ε ε A) (L x) := by rw [hQlin]
  -- convert `L` into an invertible matrix
  let c : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (L : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
  have hcm : Matrix.toLin' c = (L : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) := Matrix.toLin'_toMatrix' _
  have heq : c * e = Matrix.reindex ε ε A * c := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, hcm, ← hEdef]
    apply LinearMap.ext
    intro x
    exact hLint x
  have hunit : IsUnit c := by
    let Ls : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) := L.symm
    let c' : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (Ls : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    have hc' : Matrix.toLin' c' = (Ls : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) := Matrix.toLin'_toMatrix' _
    have hmul1 : c * c' = 1 := by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_one, hcm, hc']
      ext x
      simp [Ls]
    have hmul2 : c' * c = 1 := by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_one, hc', hcm]
      ext x
      simp [Ls]
    exact ⟨⟨c, c', hmul1, hmul2⟩, rfl⟩
  exact ⟨k, m, ε, c, hunit, heq⟩

end Work.KT.D2
