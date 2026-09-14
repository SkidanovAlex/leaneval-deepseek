import Mathlib
import Submission.Subspace.MaxRankChart
import Submission.Subspace.FamilyReduction
import Submission.Subspace.HyperplaneHeight
import Submission.Subspace.GapPrinciple
import Submission.Commons.Algebra.MvPolynomial.exists_flat_int_poly_le
import Submission.Commons.RingTheory.Algebraic.integral_nat_smul_of_algebraic

/-!
# The maximal-rank finiteness theorem (Evertse's Theorem C, maximal-rank case)

If `L : Matrix (Fin (n+1)) (Fin (n+1)) ℂ` is invertible with algebraic entries, if `γ i ≤ 1`
for all `i` and `∑ γ i < 0`, then there are only finitely many distinct *hyperplanes*
`V(Q) = approxSpace L γ Q` (`Q ≥ Q₀`, `Q₀` a suitable threshold).

The proof is by contradiction: assuming infinitely many, one takes a large finite subfamily of
hyperplanes together with witnessing scales, applies the height dichotomy
(`hyperplane_height_dichotomy`) and discards the bounded-height members
(`exists_certified_subfamily`), pigeonholes over the finitely many charts (`pair_reduction`)
to fix the chart `(0,1)`, and then applies the chain contradiction `no_long_chain_chart`.  The
scales of the extracted chain are pushed above the threshold `exp (mrA …)` by the gap principle,
via `exists_chain_large` (extraction of a subchain at large scales) and `exists_gap_chain`
(iteration of the gap).

The Siegel constant is made uniform over the finitely many charts by `siegelBound_uniform`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

open scoped BigOperators

namespace Submission.Subspace

/-- The Siegel bound is monotone in the constant `C`. -/
lemma siegelBound_mono {K : IntermediateField ℚ ℂ} [FiniteDimensional ℚ ↥K]
    {N : ℕ} {Λ : Matrix (Fin N) (Fin N) ↥K} {M C C' : ℝ}
    (hC : C ≤ C') (hC0 : 0 ≤ C) (hM : 1 ≤ M) (h : SiegelBound K Λ M C) :
    SiegelBound K Λ M C' := by
  intro mm d hd S' hS
  obtain ⟨F, hFne, hhom, hflat, hbound⟩ := h d hd S' hS
  refine ⟨F, hFne, hhom, hflat, fun u => ?_⟩
  refine le_trans (hbound u) ?_
  have hM0 : (0:ℝ) ≤ M := le_trans zero_le_one hM
  have hP0 : (0:ℝ) ≤ ∏ h : Fin mm, (((d h + N - 1).choose (N - 1) : ℕ) : ℝ) := by positivity
  have hCM0 : (0:ℝ) ≤ C * M := by positivity
  have h1 : C * (∏ h : Fin mm, (((d h + N - 1).choose (N - 1) : ℕ) : ℝ))
      ≤ C' * (∏ h : Fin mm, (((d h + N - 1).choose (N - 1) : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_right hC hP0
  have h2 : (C * M) ^ (∑ h : Fin mm, d h) ≤ (C' * M) ^ (∑ h : Fin mm, d h) :=
    pow_le_pow_left₀ hCM0 (mul_le_mul_of_nonneg_right hC hM0) _
  calc C * (∏ h : Fin mm, (((d h + N - 1).choose (N - 1) : ℕ) : ℝ)) * (C * M) ^ (∑ h : Fin mm, d h)
      ≤ C' * (∏ h : Fin mm, (((d h + N - 1).choose (N - 1) : ℕ) : ℝ))
          * (C * M) ^ (∑ h : Fin mm, d h) :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg hCM0 _)
    _ ≤ C' * (∏ h : Fin mm, (((d h + N - 1).choose (N - 1) : ℕ) : ℝ))
          * (C' * M) ^ (∑ h : Fin mm, d h) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg (le_trans hC0 hC) hP0)

/-- The entries of `lambdaMat` can be cleared to integers by a single positive integer. -/
lemma exists_integral_scaling (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ ↥K]
    {n : ℕ} (L : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hLK : ∀ i j, L i j ∈ K) :
    ∃ cc : ℕ, 0 < cc ∧ ∀ i j, IsIntegral ℤ ((cc : ↥K) * lambdaMat K L hLK i j) := by
  classical
  haveI : Algebra.IsAlgebraic ℚ ↥K := Algebra.IsAlgebraic.of_finite ℚ ↥K
  have hp : ∀ p : Fin (n+1) × Fin (n+1), ∃ m : ℕ, 0 < m ∧
      IsIntegral ℤ ((m : ↥K) * lambdaMat K L hLK p.1 p.2) := fun p =>
    Commons.RingTheory.Algebraic.integral_nat_smul_of_algebraic
      (K := ↥K) (Algebra.IsAlgebraic.isAlgebraic (lambdaMat K L hLK p.1 p.2))
  choose cc0 hcc0pos hcc0int using hp
  refine ⟨∏ p, cc0 p, Finset.prod_pos (fun p _ => hcc0pos p), fun i j => ?_⟩
  have hdvd : cc0 (i,j) ∣ ∏ p, cc0 p := Finset.dvd_prod_of_mem _ (Finset.mem_univ (i,j))
  obtain ⟨k, hk⟩ := hdvd
  have hsplit : ((∏ p : Fin (n+1) × Fin (n+1), cc0 p : ℕ) : ↥K) * lambdaMat K L hLK i j
      = (k : ↥K) * ((cc0 (i,j) : ↥K) * lambdaMat K L hLK i j) := by
    rw [hk, Nat.cast_mul]
    ring
  rw [hsplit]
  exact IsIntegral.mul (isIntegral_natCast k) (hcc0int (i,j))

/-- **Extraction of a long chain at large scales.**  If a finite family of pairwise distinct
hyperplanes of dimension `n` has scales `≥ Qb ≥ 2` and at least `Lc + 1 + k` elements, then it
contains a strictly increasing chain of `Lc` distinct hyperplanes whose scales are all
`≥ Qb ^ ((1 + ε/2) ^ k)`.  (The growth comes from the gap principle.) -/
theorem exists_chain_large {n : ℕ} (hn : 1 ≤ n)
    (L : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hL : L.det ≠ 0)
    (γ : Fin (n+1) → ℝ) (hγ1 : ∀ i, γ i ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hsum : ∑ i, γ i ≤ -ε) (Qb : ℝ) (hQb2 : 2 ≤ Qb)
    (hbig : (Nat.factorial (n+1) : ℝ) < ‖L.det‖ * Qb ^ (ε/2))
    {ι : Type*} [Fintype ι] (s : Finset ι) (Q : ι → ℝ)
    (hQ : ∀ i ∈ s, Qb ≤ Q i)
    (hfr : ∀ i ∈ s, Module.finrank ℚ (approxSpace L γ (Q i)) = n)
    (hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → approxSpace L γ (Q i) ≠ approxSpace L γ (Q j))
    {Lc k : ℕ} (hLc1 : 1 ≤ Lc) (hcard : Lc + 1 + k ≤ s.card) :
    ∃ f : Fin Lc → ι, (∀ j, Qb ^ ((1 + ε/2) ^ k) ≤ Q (f j)) ∧ StrictMono (fun j => Q (f j)) ∧
      (∀ j, Module.finrank ℚ (approxSpace L γ (Q (f j))) = n) ∧
      (∀ j j', j ≠ j' → approxSpace L γ (Q (f j)) ≠ approxSpace L γ (Q (f j'))) := by
  classical
  have hn1 : 2 ≤ n + 1 := by omega
  have hc1 : 1 ≤ 1 + ε / 2 := by linarith
  have hQb1 : 1 ≤ Qb := le_trans one_le_two hQb2
  set S : Finset ℝ := s.image Q with hSdef
  obtain ⟨g, hgmono, hgmem⟩ := exists_strictMono_fin_finset S
  have hwit : ∀ j : Fin S.card, ∃ i ∈ s, Q i = g j := fun j => by
    obtain ⟨i, hi, hQi⟩ := Finset.mem_image.mp (hgmem j)
    exact ⟨i, hi, hQi⟩
  let idx : Fin S.card → ι := fun j => Classical.choose (hwit j)
  have hidx : ∀ j, idx j ∈ s ∧ Q (idx j) = g j := fun j => Classical.choose_spec (hwit j)
  have hcardS : S.card = s.card := by
    rw [hSdef, Finset.card_image_of_injOn]
    intro i hi j hj hij
    by_contra hne
    exact hdist i hi j hj hne (by rw [hij])
  have hSpos : 0 < S.card := by
    rw [hcardS]
    omega
  have hstep : ∀ a b : Fin S.card, a < b → (g a) ^ (1 + ε / 2) ≤ g b := by
    intro a b hab
    by_contra hcon
    push_neg at hcon
    obtain ⟨hsa, hQa⟩ := hidx a
    obtain ⟨hsb, hQb⟩ := hidx b
    have hgab : g a < g b := hgmono hab
    have hQa1 : 1 ≤ g a := by rw [← hQa]; exact le_trans hQb1 (hQ _ hsa)
    have hga : Qb ≤ g a := by rw [← hQa]; exact hQ _ hsa
    have hbig' : (Nat.factorial (n+1) : ℝ) < ‖L.det‖ * (g a) ^ (ε/2) := by
      have h1 : Qb ^ (ε/2) ≤ (g a) ^ (ε/2) :=
        Real.rpow_le_rpow (le_trans (by norm_num) hQb1) hga (by linarith)
      have h2 : (0:ℝ) ≤ ‖L.det‖ := norm_nonneg _
      have h3 := mul_le_mul_of_nonneg_left h1 h2
      linarith [hbig, h3]
    have hfr' : Module.finrank ℚ (approxSpace L γ (g a)) = (n+1) - 1 := by
      rw [← hQa, Nat.add_sub_cancel]; exact hfr _ hsa
    have hle := approxSpace_le_of_gap hn1 L hL γ hγ1 ε hε hsum (g a) (g b) hQa1
      (le_of_lt hgab) (le_of_lt hcon) hbig' hfr'
    have heq : approxSpace L γ (g b) = approxSpace L γ (g a) :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [← hQb, ← hQa, hfr _ hsb, hfr _ hsa])
    have hne : idx a ≠ idx b := by
      intro hh
      rw [hh] at hQa
      exact hgab.ne (hQa.symm.trans hQb)
    exact hdist (idx a) hsa (idx b) hsb hne (by rw [hQa, hQb]; exact heq.symm)
  have hpos : ∀ j : Fin S.card, 0 < g j := fun j => lt_of_lt_of_le zero_lt_one
    (le_trans hQb1 (by rw [← (hidx j).2]; exact hQ _ (hidx j).1))
  -- the growth: the last index of a chain has scale at least `Qb ^ ((1+ε/2)^(index))`
  have hkS : k < S.card := by rw [hcardS]; omega
  have hLcS : Lc ≤ S.card := by rw [hcardS]; omega
  have hj0 : S.card - Lc < S.card := by omega
  have hgrow : (g ⟨0, hSpos⟩) ^ ((1 + ε/2) ^ k) ≤ g ⟨k, hkS⟩ := by
    have h := fin_rpow_iter g (1 + ε/2) hc1 hpos hstep 0 k (by simpa using hkS)
    simpa using h
  have hbase : Qb ^ ((1 + ε/2) ^ k) ≤ (g ⟨0, hSpos⟩) ^ ((1 + ε/2) ^ k) := by
    have h0 : Qb ≤ g ⟨0, hSpos⟩ := by
      rw [← (hidx ⟨0, hSpos⟩).2]
      exact hQ _ (hidx ⟨0, hSpos⟩).1
    exact Real.rpow_le_rpow (le_trans (by norm_num) hQb1) h0 (by positivity)
  have hkey : Qb ^ ((1 + ε/2) ^ k) ≤ g ⟨S.card - Lc, hj0⟩ := by
    have h2 : g ⟨k, hkS⟩ ≤ g ⟨S.card - Lc, hj0⟩ := by
      apply hgmono.le_iff_le.mpr
      exact Fin.le_iff_val_le_val.mpr (by simp only; omega)
    exact le_trans (le_trans hbase hgrow) h2
  have hfidx : ∀ j : Fin Lc, S.card - Lc + (j : ℕ) < S.card := by
    intro j; have := j.isLt; omega
  refine ⟨fun j => idx ⟨S.card - Lc + (j : ℕ), hfidx j⟩, ?_, ?_, ?_, ?_⟩
  · intro j
    have h0 : Q (idx ⟨S.card - Lc + (j : ℕ), hfidx j⟩)
        = g ⟨S.card - Lc + (j : ℕ), hfidx j⟩ := (hidx _).2
    rw [h0]
    exact le_trans hkey (hgmono.le_iff_le.mpr (Fin.le_iff_val_le_val.mpr (by
      simpa only [Fin.val_mk] using Nat.le_add_right (S.card - Lc) (j : ℕ))))
  · intro j j' hjj
    show Q (idx ⟨S.card - Lc + (j : ℕ), hfidx j⟩)
        < Q (idx ⟨S.card - Lc + (j' : ℕ), hfidx j'⟩)
    have h0 : Q (idx ⟨S.card - Lc + (j : ℕ), hfidx j⟩)
        = g ⟨S.card - Lc + (j : ℕ), hfidx j⟩ := (hidx _).2
    have h0' : Q (idx ⟨S.card - Lc + (j' : ℕ), hfidx j'⟩)
        = g ⟨S.card - Lc + (j' : ℕ), hfidx j'⟩ := (hidx _).2
    rw [h0, h0']
    refine hgmono (Fin.lt_iff_val_lt_val.mpr ?_)
    show (⟨S.card - Lc + (j : ℕ), hfidx j⟩ : Fin S.card).val
        < (⟨S.card - Lc + (j' : ℕ), hfidx j'⟩ : Fin S.card).val
    simp only [Fin.val_mk]
    exact Nat.add_lt_add_left hjj (S.card - Lc)
  · intro j
    exact hfr (idx ⟨S.card - Lc + (j : ℕ), hfidx j⟩)
      (hidx ⟨S.card - Lc + (j : ℕ), hfidx j⟩).1
  · intro j j' hjj heq
    have hidxne : idx ⟨S.card - Lc + (j : ℕ), hfidx j⟩ ≠
        idx ⟨S.card - Lc + (j' : ℕ), hfidx j'⟩ := by
      intro hh
      have h1 : g ⟨S.card - Lc + (j : ℕ), hfidx j⟩
          = g ⟨S.card - Lc + (j' : ℕ), hfidx j'⟩ := by
        rw [← (hidx ⟨S.card - Lc + (j : ℕ), hfidx j⟩).2,
            ← (hidx ⟨S.card - Lc + (j' : ℕ), hfidx j'⟩).2]
        exact congrArg (fun i => Q i) hh
      have h2 : (⟨S.card - Lc + (j : ℕ), hfidx j⟩ : Fin S.card)
          = ⟨S.card - Lc + (j' : ℕ), hfidx j'⟩ := hgmono.injective h1
      refine hjj (Fin.ext (Nat.add_left_cancel (n := S.card - Lc) ?_))
      simpa only [Fin.val_mk] using congrArg Fin.val h2
    refine hdist (idx ⟨S.card - Lc + (j : ℕ), hfidx j⟩)
        (hidx ⟨S.card - Lc + (j : ℕ), hfidx j⟩).1
        (idx ⟨S.card - Lc + (j' : ℕ), hfidx j'⟩)
        (hidx ⟨S.card - Lc + (j' : ℕ), hfidx j'⟩).1 hidxne ?_
    exact heq

/-- **The gap chain.**  From a strictly increasing chain of `Lc = 1 + (m-1)·t` scales
satisfying the elementary gap step, extract `m` of them (indices `t` apart) with the iterated
gaps `(Q j) ^ (c ^ (t·(j-i))) ≤ Q i` for `i ≤ j`. -/
theorem exists_gap_chain {ι : Type*} {Lc m t : ℕ} (hLc : Lc = 1 + (m - 1) * t)
    (Q : ι → ℝ) (f : Fin Lc → ι) (c : ℝ) (hc : 1 ≤ c)
    (hpos : ∀ j, 0 < Q (f j))
    (hstep : ∀ a b : Fin Lc, a < b → (Q (f a)) ^ c ≤ Q (f b)) :
    ∃ φ : Fin m → Fin Lc, ∀ i j : Fin m, i ≤ j →
      (Q (f (φ j))) ^ (c ^ (t * ((j : ℕ) - (i : ℕ)))) ≤ Q (f (φ i)) := by
  have hidx : ∀ h : Fin m, (m - 1 - (h : ℕ)) * t < Lc := by
    intro h
    have h2 : (m - 1 - (h : ℕ)) * t ≤ (m - 1) * t := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have h3 : (m - 1) * t < Lc := by rw [hLc]; omega
    exact lt_of_le_of_lt h2 h3
  refine ⟨fun h => ⟨(m - 1 - (h : ℕ)) * t, hidx h⟩, ?_⟩
  intro i j hij
  have hij' : (i : ℕ) ≤ (j : ℕ) := hij
  have hsub : (m - 1 - (j : ℕ)) * t + t * ((j : ℕ) - (i : ℕ)) = (m - 1 - (i : ℕ)) * t := by
    have hkey : (m - 1 - (j : ℕ)) + ((j : ℕ) - (i : ℕ)) = (m - 1 - (i : ℕ)) := by
      have hj : (j : ℕ) ≤ m - 1 := by have := j.isLt; omega
      omega
    rw [Nat.mul_comm (m - 1 - (j : ℕ)) t, ← Nat.mul_add, hkey, Nat.mul_comm t]
  have hlt : (m - 1 - (j : ℕ)) * t + t * ((j : ℕ) - (i : ℕ)) < Lc := by
    rw [hsub]
    exact hidx i
  have hinst := fin_rpow_iter (fun j => Q (f j)) c hc hpos hstep ((m - 1 - (j : ℕ)) * t)
    (t * ((j : ℕ) - (i : ℕ))) hlt
  have hidxe : (⟨(m - 1 - (j : ℕ)) * t + t * ((j : ℕ) - (i : ℕ)), hlt⟩ : Fin Lc)
      = (⟨(m - 1 - (i : ℕ)) * t, hidx i⟩ : Fin Lc) := Fin.ext hsub
  rw [hidxe] at hinst
  exact hinst

/-- **Per-chart Siegel bound.**  For a single chart `σ` the matrix `lambdaMat K (L.submatrix σ σ)`
satisfies the quantitative Siegel lemma. -/
lemma exists_siegelBound_chart {n : ℕ} (hn : 1 ≤ n)
    (L : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hL : L.det ≠ 0)
    (K : IntermediateField ℚ ℂ) (hKfin : FiniteDimensional ℚ K) (hLK : ∀ i j, L i j ∈ K)
    (MΛ : ℝ) (hMΛ1 : 1 ≤ MΛ) (hMΛ : ∀ i j, ‖lambdaMatC K L hLK i j‖ ≤ MΛ)
    (cc : ℕ) (hcc : 0 < cc) (hint : ∀ i j, IsIntegral ℤ ((cc : ↥K) * lambdaMat K L hLK i j))
    (σ : Equiv.Perm (Fin (n+1))) :
    ∃ Cst : ℝ, 1 ≤ Cst ∧
      SiegelBound K (lambdaMat K (L.submatrix σ σ) (fun i j => hLK (σ i) (σ j))) MΛ Cst := by
  classical
  haveI hKfd : FiniteDimensional ℚ ↥K := hKfin
  have hn1 : 1 ≤ n + 1 := by omega
  have hL' : (L.submatrix σ σ).det ≠ 0 := by
    rw [Matrix.det_submatrix_equiv_self σ L]; exact hL
  have hcoeff : coeffMatrix K (L.submatrix σ σ) (fun i j => hLK (σ i) (σ j))
      = (coeffMatrix K L hLK).submatrix σ σ := by ext i j; rfl
  have hlam : lambdaMat K (L.submatrix σ σ) (fun i j => hLK (σ i) (σ j))
      = (lambdaMat K L hLK).submatrix σ σ := by
    simp only [lambdaMat]
    rw [hcoeff, Commons.LinearAlgebra.Matrix.inv_submatrix_perm, Matrix.transpose_submatrix]
  have hlamC : lambdaMatC K (L.submatrix σ σ) (fun i j => hLK (σ i) (σ j))
      = (lambdaMatC K L hLK).submatrix σ σ := by
    simp only [lambdaMatC, hlam]; ext i j; rfl
  have hMΛ' : ∀ i j, ‖lambdaMatC K (L.submatrix σ σ) (fun i j => hLK (σ i) (σ j)) i j‖ ≤ MΛ := by
    intro i j
    have h1 : lambdaMatC K (L.submatrix σ σ) (fun i j => hLK (σ i) (σ j)) i j
        = lambdaMatC K L hLK (σ i) (σ j) := by rw [hlamC]; rfl
    rw [h1]; exact hMΛ (σ i) (σ j)
  have hint' : ∀ i j, IsIntegral ℤ
      ((cc : ↥K) * lambdaMat K (L.submatrix σ σ) (fun i j => hLK (σ i) (σ j)) i j) := by
    intro i j
    have h1 : lambdaMat K (L.submatrix σ σ) (fun i j => hLK (σ i) (σ j)) i j
        = lambdaMat K L hLK (σ i) (σ j) := by rw [hlam]; rfl
    rw [h1]; exact hint (σ i) (σ j)
  have hLdet : (lambdaMat K (L.submatrix σ σ) (fun i j => hLK (σ i) (σ j))).det ≠ 0 := by
    rw [hlam, Matrix.det_submatrix_equiv_self σ (lambdaMat K L hLK)]
    exact lambdaMat_det_ne_zero K L hLK hL
  obtain ⟨Cst, hCpos, hCb⟩ := Commons.Algebra.MvPolynomial.exists_flat_int_poly_le ↥K hn1
    (lambdaMat K (L.submatrix σ σ) (fun i j => hLK (σ i) (σ j))) hLdet cc hcc hint'
    MΛ hMΛ1 hMΛ'
  exact ⟨max 1 Cst, le_max_left _ _,
    siegelBound_mono (le_max_right _ _) (le_of_lt hCpos) hMΛ1 hCb⟩

/-- **The Siegel constant, uniform over the finitely many charts.**  Taking the maximum over the
finitely many permutations of the chart-wise constants makes one constant work for all charts. -/
lemma siegelBound_uniform {n : ℕ} (hn : 1 ≤ n)
    (L : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hL : L.det ≠ 0)
    (K : IntermediateField ℚ ℂ) (hKfin : FiniteDimensional ℚ K) (hLK : ∀ i j, L i j ∈ K)
    (MΛ : ℝ) (hMΛ1 : 1 ≤ MΛ) (hMΛ : ∀ i j, ‖lambdaMatC K L hLK i j‖ ≤ MΛ)
    (cc : ℕ) (hcc : 0 < cc) (hint : ∀ i j, IsIntegral ℤ ((cc : ↥K) * lambdaMat K L hLK i j)) :
    ∃ Cst : ℝ, 1 ≤ Cst ∧ ∀ σ : Equiv.Perm (Fin (n+1)),
      SiegelBound K (lambdaMat K (L.submatrix σ σ) (fun i j => hLK (σ i) (σ j))) MΛ Cst := by
  classical
  choose Cch hCchpos hCchb using fun σ =>
    exists_siegelBound_chart hn L hL K hKfin hLK MΛ hMΛ1 hMΛ cc hcc hint σ
  refine ⟨max 1 ((Finset.univ : Finset (Equiv.Perm (Fin (n+1)))).sup' Finset.univ_nonempty Cch),
    le_max_left _ _, fun σ => ?_⟩
  refine siegelBound_mono ?_ (le_trans zero_le_one (hCchpos σ)) hMΛ1 (hCchb σ)
  exact le_trans (Finset.le_sup'
    (s := (Finset.univ : Finset (Equiv.Perm (Fin (n+1))))) (f := Cch) (Finset.mem_univ σ))
    (le_max_right _ _)


/-- **The maximal-rank finiteness theorem.**  For `L` invertible with algebraic entries, `γ i ≤ 1`
and `∑ γ i < 0`, there is `Q₀ ≥ 1` such that only finitely many distinct spaces
`V(Q) = approxSpace L γ Q` of dimension `n` occur at scales `Q ≥ Q₀`. -/
theorem maximal_rank_finiteness {n : ℕ} (hn : 1 ≤ n)
    (L : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hL : L.det ≠ 0)
    (hLa : ∀ i j, IsAlgebraic ℚ (L i j))
    (γ : Fin (n+1) → ℝ) (hγ1 : ∀ i, γ i ≤ 1) (hsum : ∑ i, γ i < 0) :
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∃ S : Set (Submodule ℚ (Fin (n+1) → ℚ)), S.Finite ∧
      ∀ Q : ℝ, Q₀ ≤ Q → Module.finrank ℚ (approxSpace L γ Q) = n → approxSpace L γ Q ∈ S := by
  classical
  have hn2 : 2 ≤ n + 1 := by omega
  set ε : ℝ := -∑ i, γ i with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  set δ : ℝ := ∑ i, |γ i| with hδdef
  have hsumabs : -(∑ i, γ i) ≤ ∑ i, |γ i| := by
    calc -(∑ i, γ i) = ∑ i, -(γ i) := (Finset.sum_neg_distrib _).symm
      _ ≤ ∑ i, |γ i| := Finset.sum_le_sum (fun i _ => neg_le_abs (γ i))
  have hδpos : 0 < δ := by rw [hδdef]; linarith [hεdef]
  -- ### the height dichotomy and the coefficient field
  obtain ⟨Qa, θa, Mb, hQa1, hθa0, hMb0, hdich⟩ := hyperplane_height_dichotomy hn L hL hLa γ hsum
  set θ : ℝ := min θa 1 with hθdef
  have hθ0 : 0 < θ := lt_min hθa0 one_pos
  have hθ1 : θ ≤ 1 := min_le_right _ _
  have hθa : θ ≤ θa := min_le_left _ _
  obtain ⟨K, hKfin, hLK⟩ := exists_numberField_of_algebraic_coefficients L hLa
  haveI hKfd : FiniteDimensional ℚ ↥K := hKfin
  obtain ⟨MΛ, hMΛ1, hMΛ⟩ := exists_lambdaMatC_bound K L hLK
  obtain ⟨cc, hccpos, hintcc⟩ := exists_integral_scaling K L hLK
  obtain ⟨Cst, hCst1, hCboundAll⟩ :=
    siegelBound_uniform hn L hL K hKfin hLK MΛ hMΛ1 hMΛ cc hccpos hintcc
  -- ### the parameters
  have hΘpos : 0 < mrTheta n ε δ := mrTheta_pos hεpos hδpos
  have hηpos : 0 < mrEta n ε δ := mrEta_pos hεpos hδpos
  have hmexists : ∃ m : ℕ, 2 ≤ m ∧
      2 * (Module.finrank ℚ ↥K : ℝ) ≤ (m : ℝ) * (mrTheta n ε δ) ^ 2 := by
    obtain ⟨m, hm⟩ := exists_nat_ge (2 * (Module.finrank ℚ ↥K : ℝ) / (mrTheta n ε δ) ^ 2 + 2)
    have h2m : (2:ℝ) ≤ (m:ℝ) := by
      have h0 : (0:ℝ) ≤ 2 * (Module.finrank ℚ ↥K : ℝ) / (mrTheta n ε δ) ^ 2 := by positivity
      linarith
    refine ⟨m, by exact_mod_cast h2m, ?_⟩
    have h3 : 2 * (Module.finrank ℚ ↥K : ℝ) / (mrTheta n ε δ) ^ 2 ≤ (m:ℝ) := by linarith
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (mrTheta n ε δ)^2)] at h3
    linarith
  set m : ℕ := Classical.choose hmexists with hmdef
  have hm2 : 2 ≤ m := (Classical.choose_spec hmexists).1
  have hmW : 2 * (Module.finrank ℚ ↥K : ℝ) ≤ (m : ℝ) * (mrTheta n ε δ) ^ 2 :=
    (Classical.choose_spec hmexists).2
  set A : ℝ := mrA n ε δ θ MΛ Cst m with hAdef
  have hsexists : ∃ s : ℕ, 2 ≤ (1 + ε/2)^s * mrEta n ε δ ^ (2 ^ (m - 1)) := by
    have h2 : (0:ℝ) < mrEta n ε δ ^ (2 ^ (m - 1)) := pow_pos hηpos _
    obtain ⟨N, hN⟩ := (((tendsto_pow_atTop_atTop_of_one_lt
      (show (1:ℝ) < 1 + ε/2 by linarith)).eventually_ge_atTop
      (2 / mrEta n ε δ ^ (2 ^ (m - 1)))).exists)
    refine ⟨N, ?_⟩
    rw [div_le_iff₀ h2] at hN
    linarith
  set s : ℕ := Classical.choose hsexists with hsdef
  have hs2 : 2 ≤ (1 + ε/2)^s * mrEta n ε δ ^ (2 ^ (m - 1)) := Classical.choose_spec hsexists
  set R : ℝ := (1 + ε/2)^s with hRdef
  have hR2 : 2 ≤ R * mrEta n ε δ ^ (2 ^ (m - 1)) := hs2
  set Lc : ℕ := 1 + (m - 1) * s with hLcdef
  have hLc1 : 1 ≤ Lc := by rw [hLcdef]; omega
  have hLcEq : Lc = 1 + (m - 1) * s := hLcdef
  -- ### the threshold
  set Qdt : ℝ := (Nat.factorial (n+1) / ‖L.det‖ + 1) ^ (2/ε) with hQdtdef
  set Qb : ℝ := max (max Qa 2) Qdt with hQbdef
  have hQb2 : 2 ≤ Qb := by
    rw [hQbdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hQbQa : Qa ≤ Qb := by
    rw [hQbdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hQb1 : 1 ≤ Qb := le_trans one_le_two hQb2
  have hQbQdt : Qdt ≤ Qb := by rw [hQbdef]; exact le_max_right _ _
  have hdetpos : 0 < ‖L.det‖ := norm_pos_iff.mpr hL
  have hbigQb : (Nat.factorial (n+1) : ℝ) < ‖L.det‖ * Qb ^ (ε/2) := by
    have hX1 : (1:ℝ) ≤ Nat.factorial (n+1) / ‖L.det‖ + 1 := by
      have h0 : (0:ℝ) ≤ Nat.factorial (n+1) / ‖L.det‖ := by positivity
      linarith
    have hdt1 : 1 ≤ Qdt := Real.one_le_rpow hX1 (by positivity)
    have h1 : Qdt ^ (ε/2) ≤ Qb ^ (ε/2) :=
      Real.rpow_le_rpow (le_trans zero_le_one hdt1) hQbQdt (by positivity)
    have h2 : Nat.factorial (n+1) / ‖L.det‖ + 1 ≤ Qdt ^ (ε/2) := by
      rw [hQdtdef, ← Real.rpow_mul (le_trans zero_le_one hX1),
        show (2/ε) * (ε/2) = 1 from by field_simp, Real.rpow_one]
    calc (Nat.factorial (n+1) : ℝ) < ‖L.det‖ * (Nat.factorial (n+1) / ‖L.det‖ + 1) := by
          rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hdetpos)]; linarith
      _ ≤ ‖L.det‖ * Qdt ^ (ε/2) := mul_le_mul_of_nonneg_left h2 (le_of_lt hdetpos)
      _ ≤ ‖L.det‖ * Qb ^ (ε/2) := mul_le_mul_of_nonneg_left h1 (le_of_lt hdetpos)
  have hAexists : ∃ k : ℕ, A ≤ (1 + ε/2)^k * Real.log Qb := by
    have hlog : 0 < Real.log Qb := Real.log_pos (by linarith)
    obtain ⟨N, hN⟩ := (((tendsto_pow_atTop_atTop_of_one_lt
      (show (1:ℝ) < 1 + ε/2 by linarith)).eventually_ge_atTop (A / Real.log Qb)).exists)
    refine ⟨N, ?_⟩
    rw [div_le_iff₀ hlog] at hN
    linarith
  set k₀ : ℕ := Classical.choose hAexists with hkdef
  have hk₀ : A ≤ (1 + ε/2)^k₀ * Real.log Qb := Classical.choose_spec hAexists
  set Q₀ : ℝ := Qb ^ ((1 + ε/2)^k₀) with hQ₀def
  have hQ₀1 : 1 ≤ Q₀ := Real.one_le_rpow hQb1 (by positivity)
  have hQ₀pos : 0 < Q₀ := lt_of_lt_of_le one_pos hQ₀1
  have hQ₀log : A ≤ Real.log Q₀ := by
    rw [hQ₀def, Real.log_rpow (by linarith : (0:ℝ) < Qb)]
    exact hk₀
  have hQbQ₀ : Qb ≤ Q₀ := by
    rw [hQ₀def]
    calc Qb = Qb ^ (1:ℝ) := (Real.rpow_one _).symm
      _ ≤ Qb ^ ((1 + ε/2)^k₀) :=
          Real.rpow_le_rpow_of_exponent_le hQb1 (one_le_pow₀ (by linarith))
  -- ### the family of maximal-rank spaces
  set T : Set (Submodule ℚ (Fin (n+1) → ℚ)) :=
    {V | ∃ Q : ℝ, Q₀ ≤ Q ∧ Module.finrank ℚ (approxSpace L γ Q) = n ∧ approxSpace L γ Q = V}
    with hTdef
  refine ⟨Q₀, hQ₀1, T, ?_, fun Q hQ hfr => ⟨Q, hQ, hfr, rfl⟩⟩
  by_contra hTfin
  have hTinf : T.Infinite := hTfin
  -- ### the finite subfamily
  set Kb : ℕ := Nat.card {c : Fin (n+1) → ℤ // ‖c‖ ≤ Mb} with hKbdef
  set KC : ℕ := (n+1)^2 * (Lc + 1 + k₀) + Kb + 1 with hKCdef
  obtain ⟨t, htT, htfin, htcard⟩ := hTinf.exists_subset_ncard_eq KC
  haveI : Fintype ↥t := htfin.fintype
  have htcardU : (Finset.univ : Finset ↥t).card = KC := by
    rw [Finset.card_univ]
    exact Nat.card_eq_fintype_card.symm.trans htcard
  -- ### the witnesses and normals
  have hwit : ∀ V : ↥t, ∃ Q : ℝ, Qb ≤ Q ∧
      Module.finrank ℚ (approxSpace L γ Q) = n ∧ approxSpace L γ Q = (V : Submodule ℚ _) := by
    intro V
    obtain ⟨Q, hQ, hfr, hsp⟩ := htT V.2
    exact ⟨Q, le_trans hQbQ₀ hQ, hfr, hsp⟩
  let Qw : ↥t → ℝ := fun V => Classical.choose (hwit V)
  have hQw : ∀ V : ↥t, Qb ≤ Qw V ∧ Module.finrank ℚ (approxSpace L γ (Qw V)) = n ∧
      approxSpace L γ (Qw V) = (V : Submodule ℚ _) := fun V => Classical.choose_spec (hwit V)
  have hdistU : ∀ i j : ↥t, i ≠ j → approxSpace L γ (Qw i) ≠ approxSpace L γ (Qw j) := by
    intro i j hij heq
    exact hij (Subtype.ext (by rw [← (hQw i).2.2, ← (hQw j).2.2, heq]))
  have hVne : ∀ V : ↥t, approxSpace L γ (Qw V) ≠ ⊤ := by
    intro V htop
    have h1 : Module.finrank ℚ (approxSpace L γ (Qw V)) = Module.finrank ℚ (Fin (n+1) → ℚ) := by
      rw [htop, finrank_top]
    rw [(hQw V).2.1, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
    omega
  have hnorm : ∀ V : ↥t, ∃ b : Fin (n+1) → ℤ, b ≠ 0 ∧ ∀ x : Fin (n+1) → ℚ,
      x ∈ approxSpace L γ (Qw V) ↔ ∑ j, (b j : ℚ) * x j = 0 := by
    intro V
    obtain ⟨c, hc0, hcorth⟩ := exists_int_normal_of_proper (approxSpace L γ (Qw V)) (hVne V)
    refine ⟨c, hc0, fun x => ⟨fun hx => hcorth x hx, fun hx => ?_⟩⟩
    set φ : (Fin (n+1) → ℚ) →ₗ[ℚ] ℚ := dotLin (fun j => (c j : ℚ)) with hφ
    have hφne : φ ≠ 0 := by
      apply dotLin_ne_zero
      intro hh
      apply hc0
      funext j
      have := congrFun hh j
      simpa using this
    have hkerfin : Module.finrank ℚ (LinearMap.ker φ) = n := by
      have h := Module.Dual.finrank_ker_add_one_of_ne_zero hφne
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
      omega
    have heq : approxSpace L γ (Qw V) = LinearMap.ker φ :=
      Submodule.eq_of_le_of_finrank_eq
        (fun y hy => by rw [LinearMap.mem_ker]; simpa [hφ] using hcorth y hy)
        (by rw [hkerfin, (hQw V).2.1])
    rw [heq, LinearMap.mem_ker]
    simpa [hφ] using hx
  let Bw : ↥t → (Fin (n+1) → ℤ) := fun V => Classical.choose (hnorm V)
  have hBw0 : ∀ V : ↥t, Bw V ≠ 0 := fun V => (Classical.choose_spec (hnorm V)).1
  have hBwker : ∀ (V : ↥t) (x : Fin (n+1) → ℚ),
      x ∈ approxSpace L γ (Qw V) ↔ ∑ j, (Bw V j : ℚ) * x j = 0 :=
    fun V => (Classical.choose_spec (hnorm V)).2
  have hdichU : ∀ V : ↥t, (∃ a j, a ≠ j ∧ Bw V a ≠ 0 ∧
      θ * Real.log (Qw V) ≤ Height.logHeight₁ (((Bw V j : ℤ) : ℚ) / ((Bw V a : ℤ) : ℚ)))
      ∨ (∃ c : Fin (n+1) → ℤ, c ≠ 0 ∧ ‖c‖ ≤ Mb ∧
          ∀ x : Fin (n+1) → ℚ, x ∈ approxSpace L γ (Qw V) ↔ ∑ j, (c j : ℚ) * x j = 0) := by
    intro V
    have hQ1 : 1 ≤ Qw V := le_trans hQb1 (hQw V).1
    have hQaQ : Qa ≤ Qw V := le_trans hQbQa (hQw V).1
    rcases hdich (Qw V) (Bw V) hQaQ (hBw0 V) (hQw V).2.1 (hBwker V) with
      ⟨a, j, haj, hba, hle⟩ | h
    · left
      exact ⟨a, j, haj, hba,
        le_trans (mul_le_mul_of_nonneg_right hθa (Real.log_nonneg hQ1)) hle⟩
    · exact Or.inr h
  -- ### the chart reduction
  obtain ⟨τ, t', ht'sub, hcard2, hchart⟩ :=
    family_reduction hn L γ θ Mb (Finset.univ : Finset ↥t) Qw Bw
      (fun V _ => hBw0 V) (fun V _ => hBwker V)
      (fun V _ => (hQw V).2.1) (fun i _ j _ hij => hdistU i j hij)
      (fun V _ => hdichU V)
  have ht'card : Lc + 1 + k₀ ≤ t'.card := by
    have h1 : KC ≤ (n+1)^2 * t'.card + Kb := by rw [← htcardU]; exact hcard2
    rw [hKCdef] at h1
    have h2 : (n+1)^2 * (Lc + 1 + k₀) + 1 ≤ (n+1)^2 * t'.card := by omega
    have h3 : (n+1)^2 * (Lc + 1 + k₀) < (n+1)^2 * t'.card := by omega
    have h4 : Lc + 1 + k₀ < t'.card :=
      (Nat.mul_lt_mul_left (by positivity : 0 < (n+1)^2)).mp h3
    omega
  -- ### the chain of `Lc` scales at large height
  have hcard' : Lc + 1 + k₀ ≤ (Finset.univ : Finset ↥t').card := by
    rw [Finset.card_univ, Fintype.card_coe]; exact ht'card
  obtain ⟨f, hfbig, hfmono, hffr, hfdist⟩ :=
    exists_chain_large hn L hL γ hγ1 ε hεpos (le_of_eq (neg_neg (∑ i, γ i)).symm) Qb hQb2 hbigQb
      (Finset.univ : Finset ↥t') (fun V => Qw (V : ↥t))
      (fun V _ => (hQw (V : ↥t)).1)
      (fun V _ => (hQw (V : ↥t)).2.1)
      (fun i _ j _ hij => hdistU (i : ↥t) (j : ↥t) (fun hh => hij (Subtype.ext hh)))
      hLc1 hcard'
  have hstep : ∀ a b : Fin Lc, a < b → (Qw ((f a : ↥t)))^(1 + ε/2) ≤ Qw ((f b : ↥t)) := by
    intro a b hab
    by_contra hcon
    push_neg at hcon
    have hlt : Qw ((f a : ↥t)) < Qw ((f b : ↥t)) := hfmono hab
    have hQ1 : 1 ≤ Qw ((f a : ↥t)) := le_trans hQb1 (hQw (f a : ↥t)).1
    have hbig' : (Nat.factorial (n+1) : ℝ) < ‖L.det‖ * (Qw ((f a : ↥t)))^(ε/2) := by
      have h1 : Qb ≤ Qw ((f a : ↥t)) := (hQw (f a : ↥t)).1
      have h2 : Qb ^ (ε/2) ≤ (Qw ((f a : ↥t))) ^ (ε/2) :=
        Real.rpow_le_rpow (le_trans zero_le_one hQb1) h1 (by positivity)
      have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg L.det)
      linarith [hbigQb, h3]
    have hfr' : Module.finrank ℚ (approxSpace L γ (Qw ((f a : ↥t)))) = (n+1) - 1 := by
      rw [Nat.add_sub_cancel]; exact (hQw (f a : ↥t)).2.1
    have hle := approxSpace_le_of_gap hn2 L hL γ hγ1 ε hεpos
      (le_of_eq (neg_neg (∑ i, γ i)).symm)
      (Qw ((f a : ↥t))) (Qw ((f b : ↥t))) hQ1 (le_of_lt hlt) (le_of_lt hcon) hbig' hfr'
    have heq : approxSpace L γ (Qw ((f b : ↥t))) = approxSpace L γ (Qw ((f a : ↥t))) :=
      Submodule.eq_of_le_of_finrank_eq hle
        (by rw [(hQw (f a : ↥t)).2.1, (hQw (f b : ↥t)).2.1])
    exact hfdist a b hab.ne heq.symm
  obtain ⟨φ, hφgap⟩ := exists_gap_chain hLcEq (fun V : ↥t' => Qw (V : ↥t)) f (1 + ε/2)
    (by linarith) (fun j => lt_of_lt_of_le zero_lt_one
      (le_trans hQb1 (hQw (f j : ↥t)).1)) hstep
  -- ### the assembled contradiction
  refine no_long_chain_chart hn hm2 L hL hLa γ hγ1 hsum ε δ hεdef hδdef θ hθ0 hθ1 MΛ hMΛ1
    K hKfin hLK hMΛ cc hccpos hintcc τ Cst hCst1 (hCboundAll τ) hmW R hR2
    (fun h => Qw ((f (φ h) : ↥t') : ↥t)) ?_ ?_ ?_
    (fun h => Bw ((f (φ h) : ↥t') : ↥t)) ?_ ?_ ?_ ?_
  · intro h
    exact le_trans hQb1 (hQw ((f (φ h) : ↥t') : ↥t)).1
  · intro h
    have h1 : Q₀ ≤ Qw ((f (φ h) : ↥t') : ↥t) := hfbig (φ h)
    exact le_trans hQ₀log (Real.log_le_log hQ₀pos h1)
  · intro i j hij
    have h1 := hφgap i j hij
    rw [hRdef, ← pow_mul]
    exact h1
  · intro h
    have h1 := (hchart ((f (φ h) : ↥t')) (f (φ h)).2).2.1
    simpa using h1
  · intro h x
    exact hBwker ((f (φ h) : ↥t') : ↥t) x
  · intro h
    exact (hQw ((f (φ h) : ↥t') : ↥t)).2.1
  · intro h
    have h1 := (hchart ((f (φ h) : ↥t')) (f (φ h)).2).2.2.2.2
    simpa using h1

end Submission.Subspace
