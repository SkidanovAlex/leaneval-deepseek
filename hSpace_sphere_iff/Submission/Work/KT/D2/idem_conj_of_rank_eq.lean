import Mathlib

namespace Work.KT.D2

open Matrix LinearMap

/-- **Idempotent complex matrices of equal rank are conjugate.**  If `E` and `F` are idempotent
`n × n` complex matrices with `E.rank = F.rank`, there is an invertible `c` with `c * E = F * c`.

Route: `E` and `1 - E` give the direct sum decomposition `ℂ^n = range E ⊕ range (1-E)` (with
`v ↦ (E v, v - E v)`, inverse `(x, y) ↦ x + y`), and likewise for `F`; the summands `range E`,
`range F` have the same dimension (`E.rank`, `F.rank`) and so do the complements (`n - rank`), so
`LinearEquiv.ofFinrankEq` produces the middle isomorphisms of a linear equivalence `c` with
`c (E v) = F (c v)` for all `v`.  Converting `c` into a matrix (with the standard basis
`Pi.basisFun`) and using `c * c.symm = 1` gives invertibility.  (Mathlib's
`LinearMap.IsProj.isCompl` and `LinearMap.IsProj.eq_conj_prod_map'` may shorten the work.) -/
theorem idem_conj_of_rank_eq (n : ℕ) (E F : Matrix (Fin n) (Fin n) ℂ)
    (hE : E * E = E) (hF : F * F = F) (h : E.rank = F.rank) :
    ∃ c : Matrix (Fin n) (Fin n) ℂ, IsUnit c ∧ c * E = F * c := by
  classical
  let V := Fin n → ℂ
  -- The associated linear endomorphisms, which are idempotents.
  set e : Module.End ℂ V := Matrix.toLin' E with he_def
  set f : Module.End ℂ V := Matrix.toLin' F with hf_def
  have he : IsIdempotentElem e := by
    rw [IsIdempotentElem, he_def, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hE]
  have hf : IsIdempotentElem f := by
    rw [IsIdempotentElem, hf_def, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hF]
  -- `Matrix.rank` is the dimension of the range.
  have hrank : Module.finrank ℂ (range e) = Module.finrank ℂ (range f) := by
    have h1 : E.rank = Module.finrank ℂ (range e) := by
      rw [Matrix.rank, ← Matrix.toLin'_apply' E, ← he_def]
    have h2 : F.rank = Module.finrank ℂ (range f) := by
      rw [Matrix.rank, ← Matrix.toLin'_apply' F, ← hf_def]
    rw [h1, h2] at h
    exact h
  -- Dimensions of the kernels agree as well (they are the complements).
  have hker : Module.finrank ℂ (ker e) = Module.finrank ℂ (ker f) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker e
    have h2 := LinearMap.finrank_range_add_finrank_ker f
    omega
  -- The two projections onto the first coordinate of the direct sum decompositions.
  let g : (range e × ker e) →ₗ[ℂ] (range e × ker e) :=
    LinearMap.id.prodMap (0 : (ker e) →ₗ[ℂ] (ker e))
  let gf : (range f × ker f) →ₗ[ℂ] (range f × ker f) :=
    LinearMap.id.prodMap (0 : (ker f) →ₗ[ℂ] (ker f))
  let P : (range e × ker e) ≃ₗ[ℂ] V := (range e).prodEquivOfIsCompl (ker e) he.isCompl
  let Q : (range f × ker f) ≃ₗ[ℂ] V := (range f).prodEquivOfIsCompl (ker f) hf.isCompl
  -- Middle isomorphisms, using equality of the dimensions of the summands.
  let φ : (range e) ≃ₗ[ℂ] (range f) := LinearEquiv.ofFinrankEq _ _ hrank
  let ψ : (ker e) ≃ₗ[ℂ] (ker f) := LinearEquiv.ofFinrankEq _ _ hker
  let R : (range e × ker e) ≃ₗ[ℂ] (range f × ker f) := φ.prodCongr ψ
  -- Both idempotents are conjugate to the same projection `(x, y) ↦ (x, 0)`.
  have he_conj : e = P.conj g := LinearMap.IsProj.eq_conj_prodMap he.isProj_range
  have hf_conj : f = Q.conj gf := LinearMap.IsProj.eq_conj_prodMap hf.isProj_range
  -- The conjugating linear equivalence.
  let c : V ≃ₗ[ℂ] V := P.symm.trans (R.trans Q)
  have hce : ∀ x : V, c (e x) = f (c x) := by
    intro x
    set y : range e × ker e := P.symm x with hy
    have hPe : P.symm (e x) = g y := by
      have h1 := congrArg (fun T : Module.End ℂ V => T x) he_conj
      rw [LinearEquiv.conj_apply] at h1
      have h2 := congrArg (fun z : V => P.symm z) h1
      simpa [LinearMap.comp_apply] using h2
    -- `R` intertwines the two projections.
    have hR : R (g y) = gf (R y) := by
      obtain ⟨a, b⟩ := y
      simp [g, gf, R, LinearMap.prodMap_apply, LinearEquiv.prodCongr_apply]
    have hf_apply : ∀ z : V, f z = Q (gf (Q.symm z)) := by
      intro z
      have h1 := congrArg (fun T : Module.End ℂ V => T z) hf_conj
      rw [LinearEquiv.conj_apply] at h1
      simpa [LinearMap.comp_apply] using h1
    have hcval : c x = Q (R y) := by
      simp only [c, LinearEquiv.trans_apply]
      rfl
    calc c (e x) = Q (R (P.symm (e x))) := by simp only [c, LinearEquiv.trans_apply]
      _ = Q (R (g y)) := by rw [hPe]
      _ = Q (gf (R y)) := by rw [hR]
      _ = f (Q (R y)) := by rw [hf_apply (Q (R y))]; simp
      _ = f (c x) := by rw [hcval]
  -- Convert the linear equivalence into an invertible matrix.
  let cm : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (c : V →ₗ[ℂ] V)
  let dm : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (c.symm : V →ₗ[ℂ] V)
  have hcm : Matrix.toLin' cm = (c : V →ₗ[ℂ] V) := Matrix.toLin'_toMatrix' _
  have hdm : Matrix.toLin' dm = (c.symm : V →ₗ[ℂ] V) := Matrix.toLin'_toMatrix' _
  have hmul1 : cm * dm = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, hcm, hdm, Matrix.toLin'_one]
    apply LinearMap.ext
    intro z
    simp
  have hmul2 : dm * cm = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, hdm, hcm, Matrix.toLin'_one]
    apply LinearMap.ext
    intro z
    simp
  have hunit : IsUnit cm := ⟨⟨cm, dm, hmul1, hmul2⟩, rfl⟩
  have heq : cm * E = F * cm := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, hcm, ← he_def, ← hf_def]
    apply LinearMap.ext
    intro z
    simpa [LinearMap.comp_apply] using hce z
  exact ⟨cm, hunit, heq⟩

end Work.KT.D2
