import Mathlib
import Submission.Work.TMC14Core.ceyTraceOdd
import Submission.Work.TMC14Core.Assembly
import Submission.Work.TMC14Core.ceyDerivBound
import Submission.Work.TMC14Core.adjugateHermitianRankOne
import Submission.Work.TMC14Core.traceUnitaryLe

/-!
# `Work.TMC14Core.ceyOddDiscDeriv`

The Choi–Elliott–Yui lower bound for the derivative of the discriminant at a point of
the rational union spectrum, in the odd case `q = 2m+1` (Avila–Jitomirskaya (7.2)):

  `q λ^m ≤ ‖Δ'(a)‖` whenever `Δ(a) = c` with `‖c‖ ≤ 2 + 2λ^q`.

Mathematically: `‖Δ(a)‖ ≤ 2 + 2λ^q` means that `a` lies in the union spectrum
`Σ_{p/q}` of the rational approximant, so `a` is an eigenvalue of a suitable Bloch
matrix `M(θ,k)`.  The CEY trace identity produces a unitary `W` with
`‖tr(adj(a - M) W)‖ = q λ^m`.  Since `a - M` is Hermitian and singular, its adjugate is
rank one, so `‖tr(adj(a - M) W)‖ ≤ ‖tr adj(a - M)‖`; Jacobi's formula identifies the
latter with `‖Δ'(a)‖`.

The file is self-contained: it proves the two auxiliary facts it needs (existence of
`θ, k` with `det (a - M(θ,k)) = 0`, and Jacobi's formula for Hermitian matrices) from
`Mathlib` and the already verified part of the C14 chapter.
-/

open Matrix
open scoped BigOperators Polynomial

namespace Work.TMC14Core

/-- Product rule for a finite product of polynomials. -/
lemma ceyDerivativeProdFinset {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Polynomial ℂ) :
    (∏ i ∈ s, f i).derivative = ∑ i ∈ s, (f i).derivative * ∏ j ∈ s.erase i, f j := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Polynomial.derivative_mul, ih, Finset.mul_sum,
      Finset.erase_insert ha]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hai : a ≠ i := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hai, Finset.prod_insert]
    · ring
    · simp [Finset.mem_erase, ha]

/-- Derivative at `z` of a product of linear factors. -/
lemma ceyProdLinearDerivEval {n : ℕ} (lam : Fin n → ℂ) (z : ℂ) :
    (∏ i, (Polynomial.X - Polynomial.C (lam i))).derivative.eval z
      = ∑ i, ∏ j ∈ Finset.univ.erase i, (z - lam j) := by
  rw [ceyDerivativeProdFinset, Polynomial.eval_finsetSum]
  simp only [Polynomial.derivative_X_sub_C, one_mul, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

/-- `U * (z • 1 - D) * U^* = z • 1 - U * D * U^*` for a unitary `U`. -/
lemma ceySmulOneSubConj {n : ℕ} (U D : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (z : ℂ) :
    U * (z • 1 - D) * star U = z • 1 - U * D * star U := by
  have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h1]

/-- The adjugate commutes with conjugation by a unitary matrix. -/
lemma ceyAdjugateConj {n : ℕ} (U Y : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (U * Y * star U).adjugate = U * Y.adjugate * star U := by
  have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hdet : (star U).det * U.det = 1 := by rw [← Matrix.det_mul, h2, Matrix.det_one]
  have hA : (Matrix.adjugate U) = U.det • star U := by
    calc Matrix.adjugate U = Matrix.adjugate U * U * star U := by
          rw [Matrix.mul_assoc, h1, Matrix.mul_one]
      _ = (U.det • (1 : Matrix (Fin n) (Fin n) ℂ)) * star U := by rw [Matrix.adjugate_mul]
      _ = U.det • star U := by rw [Matrix.smul_mul, Matrix.one_mul]
  have hB : (Matrix.adjugate (star U)) = (star U).det • U := by
    calc Matrix.adjugate (star U) = Matrix.adjugate (star U) * star U * U := by
          rw [Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = ((star U).det • (1 : Matrix (Fin n) (Fin n) ℂ)) * U := by rw [Matrix.adjugate_mul]
      _ = (star U).det • U := by rw [Matrix.smul_mul, Matrix.one_mul]
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hA, hB]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, hdet, one_smul,
    Matrix.mul_assoc]

/-- The trace is invariant under conjugation by a unitary matrix. -/
lemma ceyTraceConj {n : ℕ} (U Y : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (U * Y * star U).trace = Y.trace := by
  have h2 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  rw [Matrix.trace_mul_comm (U * Y) (star U), ← Matrix.mul_assoc, h2, Matrix.one_mul]

/-- Jacobi's formula for Hermitian matrices: the derivative of the characteristic
polynomial at `z` is the trace of the adjugate of `z • 1 - M`. -/
lemma ceyCharpolyDerivAdjHerm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : M.IsHermitian) (z : ℂ) :
    (M.charpoly).derivative.eval z = (Matrix.adjugate (z • 1 - M)).trace := by
  classical
  set U : Matrix (Fin n) (Fin n) ℂ := ↑(hM.eigenvectorUnitary) with hUdef
  set D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ((hM.eigenvalues i : ℝ) : ℂ)) with hDdef
  have hUmem : U ∈ Matrix.unitaryGroup (Fin n) ℂ := (hM.eigenvectorUnitary).2
  have hMUD : M = U * D * star U := by
    rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply, hUdef, hDdef]
    rfl
  have hchar : (M.charpoly).derivative.eval z
      = ∑ i, ∏ j ∈ Finset.univ.erase i, (z - ((hM.eigenvalues j : ℝ) : ℂ)) := by
    rw [hM.charpoly_eq]
    exact ceyProdLinearDerivEval (fun i => ((hM.eigenvalues i : ℝ) : ℂ)) z
  have hz : z • 1 - M = U * (z • 1 - D) * star U := by
    rw [hMUD, ceySmulOneSubConj U D hUmem z]
  have hadj : Matrix.adjugate (z • 1 - M) = U * Matrix.adjugate (z • 1 - D) * star U := by
    rw [hz, ceyAdjugateConj U _ hUmem]
  have htr : (U * Matrix.adjugate (z • 1 - D) * star U).trace
      = (Matrix.adjugate (z • 1 - D)).trace := ceyTraceConj U _ hUmem
  have hdiag : z • 1 - D = Matrix.diagonal (fun i => z - ((hM.eigenvalues i : ℝ) : ℂ)) := by
    rw [hDdef]
    ext i j
    rw [Matrix.sub_apply, Matrix.smul_one_eq_diagonal, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases h : i = j <;> simp [h]
  have hadjdiag : (Matrix.adjugate (z • 1 - D)).trace
      = ∑ i, ∏ j ∈ Finset.univ.erase i, (z - ((hM.eigenvalues j : ℝ) : ℂ)) := by
    rw [hdiag, Matrix.adjugate_diagonal, Matrix.trace_diagonal]
  calc (M.charpoly).derivative.eval z
      = ∑ i, ∏ j ∈ Finset.univ.erase i, (z - ((hM.eigenvalues j : ℝ) : ℂ)) := hchar
    _ = (Matrix.adjugate (z • 1 - D)).trace := hadjdiag.symm
    _ = (U * Matrix.adjugate (z • 1 - D) * star U).trace := htr.symm
    _ = (Matrix.adjugate (z • 1 - M)).trace := by rw [hadj]
noncomputable def ceyBlochMatR (p : ℤ) (q : ℕ) (lam : ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j =>
    (if i = j then 2*lam*Real.cos (2*Real.pi*(1/(4*(q:ℝ)) + (i:ℝ)*(p:ℝ)/(q:ℝ))) else 0)
    + (if (i:ℕ)+1 = (j:ℕ) then 1 else 0)
    + (if (j:ℕ)+1 = (i:ℕ) then 1 else 0)
    + (if (i:ℕ) = q-1 ∧ (j:ℕ) = 0 then 1 else 0)
    + (if (i:ℕ) = 0 ∧ (j:ℕ) = q-1 then 1 else 0)

lemma ceyBlochMat_eq_map (p : ℤ) (q : ℕ) (lam : ℝ) :
    blochMat p q lam (1/(4*(q:ℝ))) 0 = (ceyBlochMatR p q lam).map Complex.ofRealHom := by
  ext i j
  simp only [blochMat, ceyBlochMatR, Matrix.map_apply]
  split_ifs <;> simp [Complex.exp_zero]

lemma ceyEvalMapOfReal {P : ℝ[X]} (a : ℝ) :
    (P.map Complex.ofRealHom).eval ((a : ℝ) : ℂ) = ((P.eval a : ℝ) : ℂ) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (p := P) Complex.ofRealHom a

lemma ceyDiscEvalIsReal (p : ℤ) (q : ℕ) (lam : ℝ) (a : ℝ) :
    ∃ r : ℝ, (disc p q lam).eval (a : ℂ) = (r : ℂ) := by
  refine ⟨(((ceyBlochMatR p q lam).charpoly + Polynomial.C 2).eval a), ?_⟩
  have hdisc : disc p q lam
      = ((ceyBlochMatR p q lam).charpoly + Polynomial.C 2).map Complex.ofRealHom := by
    rw [disc, ceyBlochMat_eq_map, Matrix.charpoly_map, Polynomial.map_add, Polynomial.map_C]
    simp
  rw [hdisc, ceyEvalMapOfReal]

lemma ceyChamCoefEq (p : ℤ) (q m : ℕ) (hm : q = 2*m+1) (lam : ℝ) :
    chamCoef p q lam = ((-(2*lam^q) : ℝ) : ℂ) := by
  unfold chamCoef
  have hj : p * ((q:ℤ) - 1) = 2 * (p * (m:ℤ)) := by rw [hm]; push_cast; ring
  have hodd : Odd q := ⟨m, by omega⟩
  have hpow : (-(lam:ℂ))^q = ((-(lam^q) : ℝ) : ℂ) := by
    have h1 : (-(lam:ℂ)) = (-1:ℂ) * (lam:ℂ) := by ring
    rw [h1, mul_pow, hodd.neg_one_pow, ← Complex.ofReal_pow]
    push_cast
    ring
  have h1 : (-1:ℂ)^(2 * (p * (m:ℤ))) = 1 := by
    rw [zpow_mul (-1:ℂ) 2 (p * (m:ℤ))]
    norm_num
  rw [hj, h1, mul_one, hpow]
  push_cast
  ring

lemma ceyExistsCosTwoPi (u : ℝ) (hu : -1 ≤ u) (hu' : u ≤ 1) :
    ∃ k : ℝ, Real.cos (2 * Real.pi * k) = u := by
  refine ⟨Real.arccos u / (2 * Real.pi), ?_⟩
  have h : 2 * Real.pi * (Real.arccos u / (2 * Real.pi)) = Real.arccos u := by
    field_simp
  rw [h, Real.cos_arccos hu hu']

lemma ceyExistsCosCombo (q : ℕ) (hq : 0 < q) (A r : ℝ) (hA : 0 ≤ A) (hr : |r| ≤ 2 + A) :
    ∃ θ k : ℝ, 2 * Real.cos (2 * Real.pi * k) + A * Real.cos (2 * Real.pi * (q:ℝ) * θ) = r := by
  have hq' : (q:ℝ) ≠ 0 := by positivity
  have keyθ : ∀ v : ℝ, -1 ≤ v → v ≤ 1 →
      ∃ θ : ℝ, Real.cos (2 * Real.pi * (q:ℝ) * θ) = v := by
    intro v hv hv'
    refine ⟨Real.arccos v / (2 * Real.pi * (q:ℝ)), ?_⟩
    have h : 2 * Real.pi * (q:ℝ) * (Real.arccos v / (2 * Real.pi * (q:ℝ))) = Real.arccos v := by
      field_simp
    rw [h, Real.cos_arccos hv hv']
  have hcosquarter : Real.cos (2 * Real.pi * (1/4 : ℝ)) = 0 := by
    rw [show 2 * Real.pi * (1/4 : ℝ) = Real.pi / 2 by ring, Real.cos_pi_div_two]
  by_cases hA0 : A = 0
  · subst hA0
    have hr2 : |r| ≤ 2 := by simpa using hr
    obtain ⟨k, hk⟩ := ceyExistsCosTwoPi (r/2)
      (by linarith [(abs_le.mp hr2).1]) (by linarith [(abs_le.mp hr2).2])
    exact ⟨0, k, by rw [hk]; ring⟩
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  by_cases h1 : |r| ≤ A
  · obtain ⟨θ, hθ⟩ := keyθ (r/A)
      (by rw [le_div_iff₀ hApos]; linarith [neg_abs_le r])
      (by rw [div_le_one hApos]; linarith [le_abs_self r])
    refine ⟨θ, 1/4, ?_⟩
    rw [hcosquarter, hθ]
    field_simp
    ring
  · have h2 : A < r ∨ r < -A := by
      rcases lt_abs.mp (not_le.mp h1) with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    rcases h2 with h2 | h2
    · obtain ⟨k, hk⟩ := ceyExistsCosTwoPi ((r - A)/2)
        (by linarith)
        (by linarith [le_abs_self r])
      refine ⟨0, k, ?_⟩
      rw [show 2 * Real.pi * (q:ℝ) * 0 = 0 by ring, Real.cos_zero, mul_one, hk]
      ring
    · obtain ⟨k, hk⟩ := ceyExistsCosTwoPi ((r + A)/2)
        (by linarith [neg_abs_le r])
        (by linarith)
      refine ⟨1/(2*(q:ℝ)), k, ?_⟩
      have hcosθ : Real.cos (2 * Real.pi * (q:ℝ) * (1/(2*(q:ℝ)))) = -1 := by
        rw [show 2 * Real.pi * (q:ℝ) * (1/(2*(q:ℝ))) = Real.pi by
          field_simp, Real.cos_pi]
      rw [hcosθ, hk]
      ring

lemma ceyBlochRoot (p : ℤ) (q m : ℕ) (hm : q = 2*m+1) (hpq : Nat.Coprime p.natAbs q)
    (lam : ℝ) (hlam : 0 < lam) (a : ℝ) (c : ℂ) (hc : ‖c‖ ≤ 2 + 2*lam^q)
    (ha : (disc p q lam).eval (a : ℂ) = c) :
    ∃ θ k : ℝ, (blochMat p q lam θ k).charpoly.eval (a : ℂ) = 0 := by
  obtain ⟨r, hr⟩ := ceyDiscEvalIsReal p q lam a
  have hcr : c = (r : ℂ) := by rw [← ha, hr]
  have hrabs : |r| ≤ 2 + 2*lam^q := by
    have h2 : ‖(r : ℂ)‖ ≤ 2 + 2*lam^q := by rw [← hcr]; exact hc
    rw [show ‖(r : ℂ)‖ = |r| from RCLike.norm_ofReal r] at h2
    exact h2
  obtain ⟨θ, k, hcos⟩ := ceyExistsCosCombo q (by omega) (2*lam^q) r (by positivity) hrabs
  refine ⟨θ, k, ?_⟩
  have hC : (2 * ((Real.cos (2 * Real.pi * k) : ℝ) : ℂ)
      - chamCoef p q lam * ((Real.cos (2 * Real.pi * (q:ℝ) * θ) : ℝ) : ℂ)) = ((r:ℝ) : ℂ) := by
    rw [ceyChamCoefEq p q m hm lam]
    have hcast : 2 * ((Real.cos (2*Real.pi*k) : ℝ) : ℂ)
        - ((-(2*lam^q) : ℝ) : ℂ) * ((Real.cos (2*Real.pi*(q:ℝ)*θ) : ℝ) : ℂ)
        = ((2 * Real.cos (2*Real.pi*k) + 2*lam^q * Real.cos (2*Real.pi*(q:ℝ)*θ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, hcos]
  have hsplit : (disc p q lam).eval (a:ℂ) = (blochMat p q lam θ k).charpoly.eval (a:ℂ)
      + (2 * ((Real.cos (2*Real.pi*k) : ℝ) : ℂ)
        - chamCoef p q lam * ((Real.cos (2*Real.pi*(q:ℝ)*θ) : ℝ) : ℂ)) := by
    rw [disc_eq_charpoly_add p q m hm hpq lam θ k, Polynomial.eval_add, Polynomial.eval_C]
  have h1 : (blochMat p q lam θ k).charpoly.eval (a:ℂ)
      = (disc p q lam).eval (a:ℂ)
        - (2 * ((Real.cos (2*Real.pi*k) : ℝ) : ℂ)
          - chamCoef p q lam * ((Real.cos (2*Real.pi*(q:ℝ)*θ) : ℝ) : ℂ)) := by
    rw [hsplit]; ring
  rw [h1, ha, hC, hcr]
  ring

/-- **Choi–Elliott–Yui (odd case).**  If `Δ(a) = c` with `‖c‖ ≤ 2 + 2λ^q` and `q = 2m+1`, then
`‖Δ'(a)‖ ≥ q λ^m`. -/
theorem ceyOddDiscDeriv (p : ℤ) (q m : ℕ) (hm : q = 2*m+1) (hpq : Nat.Coprime p.natAbs q)
    (lam : ℝ) (hlam : 0 < lam) (a : ℝ) (c : ℂ) (hc : ‖c‖ ≤ 2 + 2*lam^q)
    (ha : (disc p q lam).eval (a : ℂ) = c) :
    (q : ℝ) * lam ^ m ≤ ‖(disc p q lam).derivative.eval (a : ℂ)‖ := by
  -- `a` is an eigenvalue of a suitable Bloch matrix `M(θ,k)`.
  obtain ⟨θ, k, hroot⟩ := ceyBlochRoot p q m hm hpq lam hlam a c hc ha
  -- CEY trace identity for that Bloch matrix.
  obtain ⟨W, hW, hWtr⟩ := ceyTraceOdd p q m hm hpq lam θ k (a : ℂ)
  set N : Matrix (Fin q) (Fin q) ℂ :=
    (a : ℂ) • (1 : Matrix (Fin q) (Fin q) ℂ) - blochMat p q lam θ k with hN
  have hscalar : Matrix.scalar (Fin q) (a : ℂ) = (a : ℂ) • (1 : Matrix (Fin q) (Fin q) ℂ) := by
    ext i j
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal, Matrix.diagonal_apply]
  have hsa : IsSelfAdjoint ((a : ℂ)) := by
    rw [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]
  have hNherm : N.IsHermitian := by
    rw [hN]
    exact (Matrix.isHermitian_one.smul hsa).sub (blochMat_isHermitian p q lam θ k)
  have hNdet : N.det = 0 := by
    rw [hN, ← hscalar, ← Matrix.eval_charpoly, hroot]
  -- a nonzero kernel vector, hence `adj N` has rank one.
  obtain ⟨v, hv0, hvN⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hNdet
  obtain ⟨cc, hcc⟩ := adjugateHermitianRankOne N hNherm v hv0 hvN
  have hle : ‖(N.adjugate * W).trace‖ ≤ ‖N.adjugate.trace‖ := by
    rw [hcc]
    exact traceUnitaryLe cc v W hW
  -- Jacobi's formula: `tr adj N = Δ'(a)`.
  have hdisc : (disc p q lam).derivative.eval (a : ℂ) = N.adjugate.trace := by
    rw [hN, disc_derivative_eq p q m hm hpq lam θ k]
    exact ceyCharpolyDerivAdjHerm (blochMat p q lam θ k) (blochMat_isHermitian p q lam θ k) (a:ℂ)
  have hWtr' : ‖(N.adjugate * W).trace‖ = (q : ℝ) * lam ^ m := by
    rw [hWtr, abs_of_pos hlam]
  calc (q : ℝ) * lam ^ m = ‖(N.adjugate * W).trace‖ := hWtr'.symm
    _ ≤ ‖N.adjugate.trace‖ := hle
    _ = ‖(disc p q lam).derivative.eval (a : ℂ)‖ := by rw [hdisc]

end Work.TMC14Core
