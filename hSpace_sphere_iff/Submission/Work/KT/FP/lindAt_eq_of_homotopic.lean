import Mathlib
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.FP.SliceAux
import Submission.Work.KT.FP.laurent_homotopy_lift
import Submission.Work.KT.FP.lindAt_slice_eq
import Submission.Work.KT.FP.lindAt_pad_step
import Submission.Work.KT.FP.lindDefs
import Submission.Work.KT.FP.lindAt_adm_mono

/-!
# `Work.KT.FP.lindAt_eq_of_homotopic`

`Work.KT.FP.lindAt X n m P ρ` is the candidate index of a Laurent clutching function `P` of degree
bound `m`: the `K₀`-class of the Riesz projection of the `(2m+1)`-block `W` linearisation of the
coefficient sequence `coeffSeq X n m P`, corrected by `m · [1_n]`.  Here we show that it only
depends on the homotopy class of the clutching function: if `H` is a homotopy of units over
`(X × [0,1]) × S¹` whose two ends are the images of `P₀` and `P₁`, and if the linearised pencils are
admissible on the annuli of radii `ρ₀`, `ρ₁`, then `lindAt X n m P₀ ρ₀ = lindAt X n m P₁ ρ₁`.

The proof has four steps.

1. `Work.KT.FP.laurent_homotopy_lift` replaces `H` by a Laurent polynomial matrix `Q` over
   `C(X × [0,1], ℂ)` with invertible image and the same two ends.
2. `exists_degree_bound` provides a degree bound `M ≥ m` for `Q`; the two slices of `Q` are the
   given matrices `P₀`, `P₁` (`matSlice_eq_of_slice_map_eq`, using the injectivity
   `laurentMap_injective_aux` of the Laurent model `Work.KT.laurentMap`).
3. `Work.KT.FP.lindAt_slice_eq`, applied at the bound `M`, gives
   `lindAt X n M (matSlice X 0 Q) ρ₀ = lindAt X n M (matSlice X 1 Q) ρ₁`.
4. `lindAt_pad_chain` lowers the degree bound from `M` back to `m` (both sides at the radii `ρ₀`,
   `ρ₁` of the statement, via the degree-padding step `Work.KT.FP.lindAt_pad_step`), using
   `lindAt_adm_mono` to transfer admissibility from the bound `m` to every intermediate bound.
-/

namespace Work.KT.FP

noncomputable section

/-! ## A degree bound for an arbitrary Laurent matrix -/

/-- The maximal absolute value of a non-zero Laurent coefficient of a matrix of Laurent
polynomials, as a natural number. -/
def degB (X : Type) [TopologicalSpace X] (n : ℕ)
    (Q : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) : ℕ :=
  Finset.univ.sup
    (fun p : Fin n × Fin n => (Q p.1 p.2).coeff.support.sup (fun k : ℤ => k.natAbs))

lemma coeff_eq_zero_of_degB_lt (X : Type) [TopologicalSpace X] (n : ℕ)
    (Q : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) {k : ℤ} (i j : Fin n)
    (h : degB X n Q < k.natAbs) : (Q i j).coeff k = 0 := by
  by_contra hne
  have hmem : k ∈ (Q i j).coeff.support := Finsupp.mem_support_iff.mpr hne
  have h1 : k.natAbs ≤ (Q i j).coeff.support.sup (fun k : ℤ => k.natAbs) :=
    Finset.le_sup (f := fun k : ℤ => k.natAbs) hmem
  have h2 : (Q i j).coeff.support.sup (fun k : ℤ => k.natAbs) ≤ degB X n Q :=
    Finset.le_sup
      (f := fun p : Fin n × Fin n => (Q p.1 p.2).coeff.support.sup (fun k : ℤ => k.natAbs))
      (Finset.mem_univ (i, j))
  exact absurd (le_trans h1 h2) (not_le.mpr h)

/-- **A degree bound for a Laurent matrix**: every matrix of Laurent polynomials has a degree
bound, which can be taken at least as large as any prescribed `m`. -/
theorem exists_degree_bound (X : Type) [TopologicalSpace X] (n m : ℕ)
    (Q : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) :
    ∃ M : ℕ, m ≤ M ∧
      ∀ (i j : Fin n) (k : ℤ), (M : ℤ) < k ∨ k < -(M : ℤ) → (Q i j).coeff k = 0 := by
  refine ⟨max m (degB X n Q), le_max_left _ _, ?_⟩
  intro i j k hk
  refine coeff_eq_zero_of_degB_lt X n Q i j ?_
  have hle : (degB X n Q : ℕ) ≤ max m (degB X n Q) := le_max_right _ _
  rcases hk with h | h
  · have hB : (degB X n Q : ℤ) < k := by
      have h' : (degB X n Q : ℤ) ≤ (max m (degB X n Q) : ℤ) := by exact_mod_cast hle
      omega
    omega
  · have hB : (degB X n Q : ℤ) < k.natAbs := by
      have h' : (degB X n Q : ℤ) ≤ (max m (degB X n Q) : ℤ) := by exact_mod_cast hle
      omega
    omega

/-! ## Slices of the Laurent model -/

/-- The points `t + i·√(1-t²)`, for `t ∈ (-1,1)`, are distinct points of the unit circle. -/
lemma circle_point_mem (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    ((t : ℂ) + Complex.I * ((Real.sqrt (1 - t ^ 2) : ℝ) : ℂ)) ∈ Metric.sphere (0 : ℂ) 1 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  have h1 : 0 ≤ 1 - t ^ 2 := by
    have h2 : |t| < 1 := by rw [abs_lt]; exact ⟨ht.1, ht.2⟩
    nlinarith [sq_abs t, abs_nonneg t, sq_nonneg t]
  have hs : (Real.sqrt (1 - t ^ 2)) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt h1
  have hns : Complex.normSq ((t : ℂ) + Complex.I * ((Real.sqrt (1 - t ^ 2) : ℝ) : ℂ))
      = t ^ 2 + (Real.sqrt (1 - t ^ 2)) ^ 2 := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, mul_one, zero_mul, sub_zero, add_zero]
    ring
  have hsq : ‖(t : ℂ) + Complex.I * ((Real.sqrt (1 - t ^ 2) : ℝ) : ℂ)‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, hns, hs]
    ring
  nlinarith [norm_nonneg ((t : ℂ) + Complex.I * ((Real.sqrt (1 - t ^ 2) : ℝ) : ℂ))]

/-- **The unit circle is infinite.**  The points `t + i·√(1-t²)`, `t ∈ (-1,1)`, are distinct points
of it (their real parts are `t`). -/
lemma infinite_sph : (Metric.sphere (0 : ℂ) 1).Infinite := by
  have hI : (Set.Ioo (-1 : ℝ) 1).Infinite := Set.Ioo_infinite (by norm_num)
  have hinj : Set.InjOn
      (fun t : ℝ => (t : ℂ) + Complex.I * ((Real.sqrt (1 - t ^ 2) : ℝ) : ℂ))
      (Set.Ioo (-1 : ℝ) 1) := by
    intro t _ s _ h
    have hre := congrArg Complex.re h
    simpa using hre
  exact Set.Infinite.mono (by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact circle_point_mem t ht) (hI.image hinj)

/-- **A Laurent polynomial over `ℂ` vanishing on the unit circle is zero.**  More precisely: if the
finite linear combination `∑_{k ∈ s} c k · z^k` vanishes for every `z` on the unit circle, then every
coefficient `c k`, `k ∈ s`, is zero. -/
lemma poly_eval_eq_zero_of_vanishes (s : Finset ℤ) (c : ℤ → ℂ)
    (h : ∀ z : ℂ, ‖z‖ = 1 → ∑ k ∈ s, c k * z ^ k = 0) :
    ∀ k ∈ s, c k = 0 := by
  classical
  set N : ℕ := s.sup (fun k : ℤ => k.natAbs) with hN
  have habs : ∀ k ∈ s, k.natAbs ≤ N := by
    intro k hk; rw [hN]; exact Finset.le_sup (f := fun k : ℤ => k.natAbs) hk
  have hnonneg : ∀ k ∈ s, (0 : ℤ) ≤ k + N := by
    intro k hk
    have h1 : -((k.natAbs : ℤ)) ≤ k := by
      have h2 := Int.le_natAbs (a := -k)
      rw [Int.natAbs_neg] at h2
      omega
    have h3 : (k.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast habs k hk
    omega
  set P : Polynomial ℂ := ∑ k ∈ s, Polynomial.monomial ((k + N).toNat) (c k) with hP
  have hroot : ∀ z : ℂ, ‖z‖ = 1 → P.IsRoot z := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hz; exact one_ne_zero hz.symm
    have hpow : ∀ k ∈ s, z ^ ((k + N).toNat) = z ^ k * z ^ N := by
      intro k hk
      have hkn := hnonneg k hk
      have hcast : (((k + N).toNat : ℤ)) = k + N := Int.toNat_of_nonneg hkn
      calc z ^ ((k + N).toNat) = z ^ (((k + N).toNat : ℤ)) := (zpow_natCast z _).symm
        _ = z ^ (k + N) := by rw [hcast]
        _ = z ^ k * z ^ N := zpow_add₀ hz0 k N
    rw [Polynomial.IsRoot, Polynomial.eval_finsetSum]
    have hstep : ∀ k ∈ s, (Polynomial.monomial ((k + N).toNat) (c k)).eval z
        = c k * z ^ k * z ^ N := by
      intro k hk
      rw [Polynomial.eval_monomial, hpow k hk]
      ring
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul, h z hz, zero_mul]
  have hP0 : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P (by
    refine Set.Infinite.mono ?_ infinite_sph
    intro w hw
    exact hroot w (by simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hw))
  intro k hk
  have hkn := hnonneg k hk
  have hcoeff : P.coeff ((k + N).toNat) = c k := by
    rw [hP, Polynomial.finsetSum_coeff]
    have hpt : ∀ b ∈ s,
        (Polynomial.monomial ((b + N).toNat) (c b)).coeff ((k + N).toNat)
          = if b = k then c b else 0 := by
      intro b hb
      rw [Polynomial.coeff_monomial]
      by_cases hbk : b = k
      · rw [if_pos hbk, if_pos]
        congr 1
        rw [hbk]
      · rw [if_neg hbk, if_neg]
        intro hcon
        have h1 : ((b + N).toNat : ℤ) = ((k + N).toNat : ℤ) := by exact_mod_cast hcon
        rw [Int.toNat_of_nonneg (hnonneg b hb), Int.toNat_of_nonneg (hnonneg k hk)] at h1
        omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_ite_eq', if_pos hk]
  rw [hP0, Polynomial.coeff_zero] at hcoeff
  exact hcoeff.symm

/-- **The Laurent model of a clutching function is injective.** -/
theorem laurentMap_injective_aux (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (p q : LaurentPolynomial C(X, ℂ)) (h : Work.KT.laurentMap X p = Work.KT.laurentMap X q) :
    p = q := by
  have hd : Work.KT.laurentMap X (p - q) = 0 := by rw [map_sub, h, sub_self]
  have key : ∀ k : ℤ, (p - q).coeff k = 0 := by
    intro k
    refine ContinuousMap.ext fun x => ?_
    by_cases hk : k ∈ (p - q).coeff.support
    · refine poly_eval_eq_zero_of_vanishes (p - q).coeff.support
          (fun k => ((p - q).coeff k) x) ?_ k hk
      intro z hz
      have hsum := laurentMap_apply_eq_sum (Y := X) (p - q) x
        (⟨z, by rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hz⟩ : Sph ℂ)
      rw [hd] at hsum
      simpa using hsum.symm
    · rw [Finsupp.notMem_support_iff.mp hk]
  have hcoeffs : (p - q).coeff = (0 : ℤ →₀ C(X, ℂ)) := Finsupp.ext key
  have hpq : p - q = 0 := by
    have h := congrArg AddMonoidAlgebra.ofCoeff hcoeffs
    simpa using h
  exact sub_eq_zero.mp hpq



/-- The slice `lapSlice` of a Laurent polynomial is the coefficient-wise slice `laurentCoeff`. -/
lemma lapSlice_eq_laurentCoeff (X : Type) [TopologicalSpace X] (t : unitInterval) :
    lapSlice X t = laurentCoeff (sliceHom X t) := by
  funext q
  ext k
  simp only [laurentCoeff, lapSlice]
  rw [AddMonoidAlgebra.coeff_mapRingHom]
  rfl

/-- **The value of a slice of a Laurent polynomial**: slicing at `t` and evaluating at `(x, z)` is
the same as evaluating the original Laurent polynomial at `((x,t), z)`. -/
lemma laurentMap_lapSlice_apply (X : Type) [TopologicalSpace X] (t : unitInterval)
    (q : LaurentPolynomial C(X × unitInterval, ℂ)) (x : X) (z : Sph ℂ) :
    Work.KT.laurentMap X (lapSlice X t q) (x, z)
      = Work.KT.laurentMap (X × unitInterval) q ((x, t), z) := by
  have hsl : sliceHom X t = (Work.KT.pullAlg (sliceCm X t)).toRingHom := by
    ext f
    rfl
  have h1 : lapSlice X t q
      = laurentCoeff (Work.KT.pullAlg (sliceCm X t)).toRingHom q := by
    rw [← hsl]
    exact congrFun (lapSlice_eq_laurentCoeff X t) q
  have h2 : Work.KT.laurentMap X
        (laurentCoeff (Work.KT.pullAlg (sliceCm X t)).toRingHom q) (x, z)
      = Work.KT.laurentMap (X × unitInterval) q ((x, t), z) := by
    rw [← laurentMap_natural (sliceCm X t) q]
    rfl
  rw [h1, h2]

/-- **The endpoints of the lifted homotopy determine the slices.**  If the image of a Laurent
matrix `Q` over `C(X × [0,1], ℂ)` agrees with the image of a Laurent matrix `P` over `C(X, ℂ)` on
the slice `t`, then the `t`-slice of `Q` *is* `P`. -/
lemma matSlice_eq_of_slice_map_eq (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {n : ℕ} (Q : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X × unitInterval, ℂ)))
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) (t : unitInterval)
    (h : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (Q.map (Work.KT.laurentMap (X × unitInterval))) i j ((x, t), z)
        = (P.map (Work.KT.laurentMap X)) i j (x, z)) :
    matSlice X t Q = P := by
  refine Matrix.ext fun i j => ?_
  refine laurentMap_injective_aux X ((matSlice X t Q) i j) (P i j) ?_
  refine ContinuousMap.ext fun p => ?_
  obtain ⟨x, z⟩ := p
  show Work.KT.laurentMap X (lapSlice X t (Q i j)) (x, z) = Work.KT.laurentMap X (P i j) (x, z)
  rw [laurentMap_lapSlice_apply]
  exact h i j x z

/-! ## Lowering the degree bound from `M` to `m` -/

/-- **The index is independent of the degree bound.**  If `P` has degree bound `m ≤ M` and the
linearised pencils at *every* intermediate bound are admissible on the annulus of radius `ρ`, then
the index computed with the bound `M` agrees with the one computed with the bound `m`. -/
theorem lindAt_pad_chain (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
    {m M : ℕ} (hmM : m ≤ M)
    (hb : ∀ (i j : Fin n) (k : ℤ), (m : ℤ) < k ∨ k < -(m : ℤ) → (P i j).coeff k = 0)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hadm : ∀ j : ℕ, m ≤ j → j ≤ M → ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • linAf X n j + linBf X n j P)) :
    lindAt X n M P ρ = lindAt X n m P ρ := by
  have hb' : ∀ j : ℕ, m ≤ j →
      ∀ (i i' : Fin n) (k : ℤ), (j : ℤ) < k ∨ k < -(j : ℤ) → (P i i').coeff k = 0 := by
    intro j hmj i i' k hk
    refine hb i i' k ?_
    rcases hk with h | h
    · exact Or.inl (lt_of_le_of_lt (by exact_mod_cast hmj) h)
    · refine Or.inr (lt_of_lt_of_le h ?_)
      have : (m : ℤ) ≤ (j : ℤ) := by exact_mod_cast hmj
      omega
  have key : ∀ s : ℕ, m + s ≤ M → lindAt X n (m + s) P ρ = lindAt X n m P ρ := by
    intro s
    induction s with
    | zero => intro _; simp
    | succ s ih =>
      intro hs
      have h1 : lindAt X n (m + s + 1) P ρ = lindAt X n (m + s) P ρ :=
        lindAt_pad_step X n (m + s) P (hb' (m + s) (by omega)) hρ0 hρ1 hρ0 hρ1
          (fun z hz1 hz2 => hadm (m + s) (by omega) (by omega) z hz1 hz2)
          (fun z hz1 hz2 => hadm (m + s + 1) (by omega) (by omega) z hz1 hz2)
      rw [show m + (s + 1) = m + s + 1 from by omega, h1, ih (by omega)]
  have := key (M - m) (by omega)
  rwa [Nat.add_sub_cancel' hmM] at this

/-! ## The main theorem -/

/-- **The index of a Laurent clutching function only depends on its homotopy class.** -/
theorem lindAt_eq_of_homotopic (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n m : ℕ)
    (P₀ P₁ : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
    (hb₀ : ∀ (i j : Fin n) (k : ℤ), (m : ℤ) < k ∨ k < -(m : ℤ) → (P₀ i j).coeff k = 0)
    (hb₁ : ∀ (i j : Fin n) (k : ℤ), (m : ℤ) < k ∨ k < -(m : ℤ) → (P₁ i j).coeff k = 0)
    (H : (Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))ˣ)
    (h₀ : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ)) i j ((x, 0), z)
        = (P₀.map (Work.KT.laurentMap X)) i j (x, z))
    (h₁ : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ)) i j ((x, 1), z)
        = (P₁.map (Work.KT.laurentMap X)) i j (x, z))
    {ρ₀ ρ₁ : ℝ} (hρ₀0 : 0 < ρ₀) (hρ₀1 : ρ₀ ≤ 1) (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ ≤ 1)
    (hadm₀ : ∀ z : ℂ, ρ₀ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • linAf X n m + linBf X n m P₀))
    (hadm₁ : ∀ z : ℂ, ρ₁ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • linAf X n m + linBf X n m P₁)) :
    lindAt X n m P₀ ρ₀ = lindAt X n m P₁ ρ₁ := by
  obtain ⟨Q, hQunit, hQ0, hQ1⟩ := laurent_homotopy_lift X n H P₀ P₁ h₀ h₁
  obtain ⟨M, hmM, hbQ⟩ := exists_degree_bound (X × unitInterval) n m Q
  -- the two ends of `Q` are the two given Laurent matrices
  have hs0 : matSlice X 0 Q = P₀ := matSlice_eq_of_slice_map_eq X Q P₀ 0 hQ0
  have hs1 : matSlice X 1 Q = P₁ := matSlice_eq_of_slice_map_eq X Q P₁ 1 hQ1
  -- admissibility is transferred from the bound `m` to every intermediate bound
  have hadm₀' : ∀ j : ℕ, m ≤ j → j ≤ M → ∀ z : ℂ, ρ₀ ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • linAf X n j + linBf X n j P₀) :=
    fun j hmj _ => lindAt_adm_mono X n m j hmj P₀ hb₀ hρ₀0 hadm₀
  have hadm₁' : ∀ j : ℕ, m ≤ j → j ≤ M → ∀ z : ℂ, ρ₁ ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • linAf X n j + linBf X n j P₁) :=
    fun j hmj _ => lindAt_adm_mono X n m j hmj P₁ hb₁ hρ₁0 hadm₁
  -- homotopy invariance of the index at the degree bound `M`
  have hslice : lindAt X n M P₀ ρ₀ = lindAt X n M P₁ ρ₁ := by
    have h := lindAt_slice_eq X n M Q hbQ hQunit hρ₀0 hρ₀1 hρ₁0 hρ₁1 ?_ ?_
    · rwa [hs0, hs1] at h
    · rw [hs0]
      exact hadm₀' M hmM le_rfl
    · rw [hs1]
      exact hadm₁' M hmM le_rfl
  -- lower the degree bound
  have hch0 : lindAt X n M P₀ ρ₀ = lindAt X n m P₀ ρ₀ :=
    lindAt_pad_chain X n P₀ hmM hb₀ hρ₀0 hρ₀1 (fun j hmj hjM => hadm₀' j hmj hjM)
  have hch1 : lindAt X n M P₁ ρ₁ = lindAt X n m P₁ ρ₁ :=
    lindAt_pad_chain X n P₁ hmM hb₁ hρ₁0 hρ₁1 (fun j hmj hjM => hadm₁' j hmj hjM)
  rw [← hch0, ← hch1]
  exact hslice

end

end Work.KT.FP
