import Mathlib

namespace Work.KT.D2

/-- The standard projection `diag(1_k, 0_m)` displayed in block form: its `(inl, inl)` block is
`Y`'s `(inl, inl)` block and all other blocks vanish.  Here `d₀ * Y * d₀` keeps the `(inl, inl)`
block of `Y`, and `1 - d₀` is the complementary diagonal projection. -/
private lemma blk_left (k m : ℕ) (Y : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℂ) :
    Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0 * Y
        * Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0
      + (1 - Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0)
      = Matrix.fromBlocks (Y.submatrix Sum.inl Sum.inl) 0 0 1 := by
  have hone : (1 : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℂ)
      - Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0
      = Matrix.fromBlocks (0 : Matrix (Fin k) (Fin k) ℂ) 0 0 (1 : Matrix (Fin m) (Fin m) ℂ) := by
    have h1 : (1 : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℂ)
        = Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) (0 : Matrix (Fin k) (Fin m) ℂ)
            (0 : Matrix (Fin m) (Fin k) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) :=
      Matrix.fromBlocks_one.symm
    rw [h1, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
    simp
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks Y]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, hone, Matrix.fromBlocks_add,
    Matrix.fromBlocks_inj]
  simp
  rfl

/-- The complementary case: `(1 - d₀) * Y * (1 - d₀) + d₀` keeps the `(inr, inr)` block of `Y`. -/
private lemma blk_right (k m : ℕ) (Y : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℂ) :
    (1 - Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0) * Y
        * (1 - Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0)
      + Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0
      = Matrix.fromBlocks 1 0 0 (Y.submatrix Sum.inr Sum.inr) := by
  have hone : (1 : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℂ)
      - Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0
      = Matrix.fromBlocks (0 : Matrix (Fin k) (Fin k) ℂ) 0 0 (1 : Matrix (Fin m) (Fin m) ℂ) := by
    have h1 : (1 : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℂ)
        = Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) (0 : Matrix (Fin k) (Fin m) ℂ)
            (0 : Matrix (Fin m) (Fin k) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) :=
      Matrix.fromBlocks_one.symm
    rw [h1, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
    simp
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks Y]
  rw [hone, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add,
    Matrix.fromBlocks_inj]
  simp
  rfl

/-- The two "block determinants" of a conjugating matrix are the determinants of the two
diagonal blocks.  If `c = ↑u` conjugates the idempotent `e` to `diag(1_k, 0_m)` (as in
`Work.KT.D2.conj_std_idem`, with the same `ε`), then for every matrix `X` the determinants
of `e * (u⁻¹ X u) * e + (1 - e)` and `(1 - e) * (u⁻¹ X u) * (1 - e) + e` equal the determinants of
the `(inl, inl)`- and `(inr, inr)`- blocks of `reindex ε.symm ε.symm X`.

Route: `e = u⁻¹ * d * u` where `d = reindex ε ε (fromBlocks 1 0 0 0)`; hence
`e X' e + (1 - e) = u⁻¹ * (d Y d + (1 - d)) * u` with `Y := reindex ε.symm ε.symm X`, and
`d * Y * d + (1 - d) = reindex ε ε (d₀ * Y * d₀ + (1 - d₀))` with `d₀ = fromBlocks 1 0 0 0`.
Since `d₀ * Y * d₀` has the same `(inl, inl)` block as `Y` and its other blocks vanish, and
`d₀ * Y * d₀ + (1 - d₀) = fromBlocks (Y.submatrix inl inl) 0 0 1`, `Matrix.det_fromBlocks_zero₂₁`
finishes the first identity; the second is symmetric with `1 - d₀` and `Matrix.det_fromBlocks_zero₁₂`.
Determinants are unchanged by `Matrix.reindex` (`Matrix.det_reindex_self`) and by conjugation
(`Matrix.det_mul`). -/
theorem det_block_std_idem (n k m : ℕ) (ε : Fin k ⊕ Fin m ≃ Fin n)
    (e : Matrix (Fin n) (Fin n) ℂ) (he : e * e = e) (u : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (X : Matrix (Fin n) (Fin n) ℂ)
    (hce : (↑u : Matrix (Fin n) (Fin n) ℂ) * e
      = Matrix.reindex ε ε (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0)
        * (↑u : Matrix (Fin n) (Fin n) ℂ)) :
    (e * ((↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ) * X * (↑u : Matrix (Fin n) (Fin n) ℂ)) * e
        + (1 - e)).det
        = ((Matrix.reindex ε.symm ε.symm X).submatrix Sum.inl Sum.inl).det ∧
      ((1 - e) * ((↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ) * X * (↑u : Matrix (Fin n) (Fin n) ℂ))
          * (1 - e) + e).det
        = ((Matrix.reindex ε.symm ε.symm X).submatrix Sum.inr Sum.inr).det := by
  -- Abbreviate `c = ↑u`, `ci = ↑u⁻¹`, the standard projection `d` and the reindexed matrix `Y`.
  set c : Matrix (Fin n) (Fin n) ℂ := (↑u : Matrix (Fin n) (Fin n) ℂ) with hc
  set ci : Matrix (Fin n) (Fin n) ℂ := (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ) with hci
  set d : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.reindex ε ε (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0) with hd
  set Y : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℂ := Matrix.reindex ε.symm ε.symm X with hY
  have hcic : ci * c = 1 := by simp [hc, hci]
  have hcci : c * ci = 1 := by simp [hc, hci]
  have hXe : Matrix.reindex ε ε Y = X := by
    rw [hY]
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  -- `e = ci * d * c`, `e * ci = ci * d`.
  have heq : e = ci * d * c := by
    calc e = ci * (c * e) := by rw [← mul_assoc, hcic, one_mul]
      _ = ci * (d * c) := by rw [hce]
      _ = ci * d * c := by rw [mul_assoc]
  have heci : e * ci = ci * d := by
    calc e * ci = ci * c * (e * ci) := by rw [hcic, one_mul]
      _ = ci * (c * e) * ci := by noncomm_ring
      _ = ci * (d * c) * ci := by rw [hce]
      _ = ci * d * (c * ci) := by noncomm_ring
      _ = ci * d := by rw [hcci, mul_one]
  have hA : e * (ci * X * c) * e = ci * (d * X * d) * c := by
    calc e * (ci * X * c) * e = (e * ci) * X * (c * e) := by noncomm_ring
      _ = (ci * d) * X * (d * c) := by rw [heci, hce]
      _ = ci * (d * X * d) * c := by noncomm_ring
  have hB : (1 : Matrix (Fin n) (Fin n) ℂ) - e = ci * (1 - d) * c := by
    calc (1 : Matrix (Fin n) (Fin n) ℂ) - e = ci * c - e := by rw [hcic]
      _ = ci * c - ci * d * c := by rw [heq]
      _ = ci * (1 - d) * c := by noncomm_ring
  have hkey : e * (ci * X * c) * e + (1 - e) = ci * (d * X * d + (1 - d)) * c := by
    rw [hA, hB]
    noncomm_ring
  have h1eci : (1 - e) * ci = ci * (1 - d) := by
    calc (1 - e) * ci = (ci * (1 - d) * c) * ci := by rw [hB]
      _ = ci * (1 - d) * (c * ci) := by noncomm_ring
      _ = ci * (1 - d) := by rw [hcci, mul_one]
  have hc1e : c * (1 - e) = (1 - d) * c := by
    calc c * (1 - e) = c * (ci * (1 - d) * c) := by rw [hB]
      _ = (c * ci) * (1 - d) * c := by noncomm_ring
      _ = (1 - d) * c := by rw [hcci, one_mul]
  have hA2 : (1 - e) * (ci * X * c) * (1 - e) = ci * ((1 - d) * X * (1 - d)) * c := by
    calc (1 - e) * (ci * X * c) * (1 - e) = ((1 - e) * ci) * X * (c * (1 - e)) := by noncomm_ring
      _ = (ci * (1 - d)) * X * ((1 - d) * c) := by rw [h1eci, hc1e]
      _ = ci * ((1 - d) * X * (1 - d)) * c := by noncomm_ring
  have hkey2 : (1 - e) * (ci * X * c) * (1 - e) + e
      = ci * ((1 - d) * X * (1 - d) + d) * c := by
    rw [hA2, heq]
    noncomm_ring
  -- Push `d` and `X` in terms of the standard blocks through the reindexing equivalence.
  have hmap : Matrix.reindex ε ε (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0 * Y
        * Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0
        + (1 - Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0))
      = Matrix.reindex ε ε (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0)
          * Matrix.reindex ε ε Y
          * Matrix.reindex ε ε (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0)
        + (1 - Matrix.reindex ε ε (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0)) := by
    change (Matrix.reindexAlgEquiv ℂ ℂ ε)
        (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0 * Y
          * Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0
          + (1 - Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0))
        = (Matrix.reindexAlgEquiv ℂ ℂ ε) (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0)
            * (Matrix.reindexAlgEquiv ℂ ℂ ε) Y
            * (Matrix.reindexAlgEquiv ℂ ℂ ε)
                (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0)
          + (1 - (Matrix.reindexAlgEquiv ℂ ℂ ε)
                (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0))
    rw [map_add, map_sub, map_one, map_mul, map_mul]
  have hmap' : Matrix.reindex ε ε (Matrix.fromBlocks (Y.submatrix Sum.inl Sum.inl) 0 0 1)
      = Matrix.reindex ε ε (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0)
          * Matrix.reindex ε ε Y
          * Matrix.reindex ε ε (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0)
        + (1 - Matrix.reindex ε ε (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0)) := by
    rw [← hmap, blk_left]
  have hM : d * X * d + (1 - d)
      = Matrix.reindex ε ε (Matrix.fromBlocks (Y.submatrix Sum.inl Sum.inl) 0 0 1) := by
    rw [hd, ← hXe, ← hmap']
  have hmap2 : Matrix.reindex ε ε ((1 - Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0) * Y
        * (1 - Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0)
        + Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0)
      = (1 - Matrix.reindex ε ε (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0))
          * Matrix.reindex ε ε Y
          * (1 - Matrix.reindex ε ε (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0))
        + Matrix.reindex ε ε (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0) := by
    change (Matrix.reindexAlgEquiv ℂ ℂ ε)
        ((1 - Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0) * Y
          * (1 - Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0)
          + Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0)
        = (1 - (Matrix.reindexAlgEquiv ℂ ℂ ε)
                (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0))
            * (Matrix.reindexAlgEquiv ℂ ℂ ε) Y
            * (1 - (Matrix.reindexAlgEquiv ℂ ℂ ε)
                (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0))
          + (Matrix.reindexAlgEquiv ℂ ℂ ε) (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0)
    rw [map_add, map_mul, map_mul, map_sub, map_one]
  have hmap2' : Matrix.reindex ε ε (Matrix.fromBlocks 1 0 0 (Y.submatrix Sum.inr Sum.inr))
      = (1 - Matrix.reindex ε ε (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0))
          * Matrix.reindex ε ε Y
          * (1 - Matrix.reindex ε ε (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0))
        + Matrix.reindex ε ε (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0) := by
    rw [← hmap2, blk_right]
  have hM2 : (1 - d) * X * (1 - d) + d
      = Matrix.reindex ε ε (Matrix.fromBlocks 1 0 0 (Y.submatrix Sum.inr Sum.inr)) := by
    rw [hd, ← hXe, ← hmap2']
  constructor
  · rw [hkey, hM]
    have hd1 : ci.det * c.det = 1 := by rw [← Matrix.det_mul, hcic, Matrix.det_one]
    have hr : ci.det * (Y.submatrix Sum.inl Sum.inl).det * c.det
        = (ci.det * c.det) * (Y.submatrix Sum.inl Sum.inl).det := by ring
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, mul_one, hr, hd1, one_mul]
  · rw [hkey2, hM2]
    have hd1 : ci.det * c.det = 1 := by rw [← Matrix.det_mul, hcic, Matrix.det_one]
    have hr : ci.det * (Y.submatrix Sum.inr Sum.inr).det * c.det
        = (ci.det * c.det) * (Y.submatrix Sum.inr Sum.inr).det := by ring
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂,
      Matrix.det_one, one_mul, hr, hd1, one_mul]

end Work.KT.D2
