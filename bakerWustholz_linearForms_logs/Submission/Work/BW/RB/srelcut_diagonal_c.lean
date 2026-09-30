import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.RB.mvpoly_dim_formula

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The "diagonal" ideal of `MR N = ℂ[X_{i,0}, X_{i,1}]_{i : Fin (N+1)}`

For a point `y : Fin (N+1) × Fin 2 → ℂ` whose first coordinates `y (i,0)` do not vanish, we
consider the ideal `K` of `MR N` spanned by the `N+1` "diagonal" linear forms

  `L_i = C (y (i,0)) * X (i,1) - C (y (i,1)) * X (i,0)`   (`i : Fin (N+1)`),

and prove that `K` is prime of height `N+1`, multihomogeneous, and that no monomial
`∏_i X (i,0) ^ (t * D i)` lies in it.

## Route

Let `c i = y (i,1) / y (i,0)`.  The substitution `Φ : MR N →+* ℂ[X_0,…,X_N]` with
`X (i,0) ↦ X i` and `X (i,1) ↦ C (c i) * X i` is surjective (the section `s`, `X i ↦ X (i,0)`,
satisfies `Φ ∘ s = id`) and its kernel is exactly `K`: one inclusion is immediate, and for the
other we show `F - s (Φ F) ∈ K` for every `F` — the substitution `s ∘ Φ` replaces `X (i,1)` by
`C (c i) * X (i,0)`, which differs from `X (i,1)` by a unit multiple of the generator `L_i`.
Hence `MR N ⧸ K ≅ ℂ[X_0,…,X_N]`, which gives primality, the multihomogeneity (through the
multidegree grading), the height `2(N+1) - (N+1) = N+1` and the monomial statement.
-/

namespace Work.BW.RB

open MvPolynomial

noncomputable section

/-! ## The substitution and the ideal -/

/-- The substitution `X (i,0) ↦ X i`, `X (i,1) ↦ C (y (i,1) / y (i,0)) * X i`. -/
noncomputable def diagΦ (N : ℕ) (y : Fin (N + 1) × Fin 2 → ℂ) :
    MR N →+* MvPolynomial (Fin (N + 1)) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun v : Fin (N + 1) × Fin 2 =>
      if (v.2 : Fin 2) = 0 then (MvPolynomial.X v.1 : MvPolynomial (Fin (N + 1)) ℂ)
      else MvPolynomial.C (y (v.1, 1) / y (v.1, 0)) * MvPolynomial.X v.1)

/-- The section `X i ↦ X (i,0)`. -/
noncomputable def diagSec (N : ℕ) : MvPolynomial (Fin (N + 1)) ℂ →+* MR N :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i : Fin (N + 1) => (MvPolynomial.X (i, 0) : MR N))

/-- The substitution `X (i,0) ↦ X (i,0)`, `X (i,1) ↦ C (y (i,1) / y (i,0)) * X (i,0)`. -/
noncomputable def diagρ (N : ℕ) (y : Fin (N + 1) × Fin 2 → ℂ) : MR N →+* MR N :=
  (diagSec N).comp (diagΦ N y)

/-- The ideal spanned by the diagonal forms
`C (y (i,0)) * X (i,1) - C (y (i,1)) * X (i,0)`. -/
noncomputable def diagIdeal (N : ℕ) (y : Fin (N + 1) × Fin 2 → ℂ) : Ideal (MR N) :=
  Ideal.span (Set.range (fun i : Fin (N + 1) =>
    (MvPolynomial.C (y (i, 0)) : MR N) * (MvPolynomial.X (i, 1) : MR N)
      - (MvPolynomial.C (y (i, 1)) : MR N) * (MvPolynomial.X (i, 0) : MR N)))

lemma diagΦ_X_zero (N : ℕ) (y : Fin (N + 1) × Fin 2 → ℂ) (i : Fin (N + 1)) :
    diagΦ N y (MvPolynomial.X (i, 0)) = MvPolynomial.X i := by
  simp [diagΦ]

lemma diagΦ_X_one (N : ℕ) (y : Fin (N + 1) × Fin 2 → ℂ) (i : Fin (N + 1)) :
    diagΦ N y (MvPolynomial.X (i, 1))
      = MvPolynomial.C (y (i, 1) / y (i, 0)) * MvPolynomial.X i := by
  simp [diagΦ]

lemma diagΦ_C (N : ℕ) (y : Fin (N + 1) × Fin 2 → ℂ) (a : ℂ) :
    diagΦ N y (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [diagΦ]

lemma diagSec_X (N : ℕ) (i : Fin (N + 1)) :
    diagSec N (MvPolynomial.X i) = (MvPolynomial.X (i, 0) : MR N) := by
  simp [diagSec]

lemma diagSec_C (N : ℕ) (a : ℂ) : diagSec N (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [diagSec]

lemma diagρ_X_zero (N : ℕ) (y : Fin (N + 1) × Fin 2 → ℂ) (i : Fin (N + 1)) :
    diagρ N y (MvPolynomial.X (i, 0)) = (MvPolynomial.X (i, 0) : MR N) := by
  simp [diagρ, diagΦ_X_zero, diagSec_X]

lemma diagρ_X_one (N : ℕ) (y : Fin (N + 1) × Fin 2 → ℂ) (i : Fin (N + 1)) :
    diagρ N y (MvPolynomial.X (i, 1))
      = (MvPolynomial.C (y (i, 1) / y (i, 0)) : MR N) * MvPolynomial.X (i, 0) := by
  simp [diagρ, diagΦ_X_one, diagSec]

lemma diagρ_C (N : ℕ) (y : Fin (N + 1) × Fin 2 → ℂ) (a : ℂ) :
    diagρ N y (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [diagρ, diagΦ_C, diagSec_C]

lemma diagΦ_comp_diagSec (N : ℕ) (y : Fin (N + 1) × Fin 2 → ℂ) :
    (diagΦ N y).comp (diagSec N) = RingHom.id (MvPolynomial (Fin (N + 1)) ℂ) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp [diagΦ_C, diagSec_C]
  · simp [diagΦ_X_zero, diagSec_X]

/-! ## The reduction `F - (s ∘ Φ) F ∈ K` -/

/-- The generator corresponding to `i` lies in `K`, multiplied by the unit `C (y (i,0))⁻¹`. -/
lemma diag_sub_X1 (N : ℕ) (y : Fin (N + 1) × Fin 2 → ℂ)
    (hy : ∀ i : Fin (N + 1), y (i, 0) ≠ 0) (i : Fin (N + 1)) :
    (MvPolynomial.X (i, 1) : MR N)
        - (MvPolynomial.C (y (i, 1) / y (i, 0)) : MR N) * MvPolynomial.X (i, 0)
      ∈ diagIdeal N y := by
  have hg : (MvPolynomial.C (y (i, 0)) : MR N) * MvPolynomial.X (i, 1)
      - (MvPolynomial.C (y (i, 1)) : MR N) * MvPolynomial.X (i, 0) ∈ diagIdeal N y :=
    Ideal.subset_span ⟨i, rfl⟩
  have h2 := Ideal.mul_mem_left (diagIdeal N y) (MvPolynomial.C ((y (i, 0))⁻¹)) hg
  convert h2 using 1
  rw [mul_sub, ← mul_assoc, ← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ (hy i),
    MvPolynomial.C_1, one_mul, ← MvPolynomial.C_mul]
  rw [div_eq_inv_mul]

/-- For every `F`, the difference `F - (s ∘ Φ) F` lies in `K`. -/
lemma diag_reduce (N : ℕ) (y : Fin (N + 1) × Fin 2 → ℂ)
    (hy : ∀ i : Fin (N + 1), y (i, 0) ≠ 0) :
    ∀ F : MR N, F - diagρ N y F ∈ diagIdeal N y := by
  intro F
  have hvar0 : ∀ i : Fin (N + 1),
      MvPolynomial.X (i, 0) - diagρ N y (MvPolynomial.X (i, 0)) ∈ diagIdeal N y := by
    intro i; rw [diagρ_X_zero, sub_self]; exact (diagIdeal N y).zero_mem
  have hvar1 : ∀ i : Fin (N + 1),
      MvPolynomial.X (i, 1) - diagρ N y (MvPolynomial.X (i, 1)) ∈ diagIdeal N y := by
    intro i; rw [diagρ_X_one]; exact diag_sub_X1 N y hy i
  have hvar : ∀ v : Fin (N + 1) × Fin 2,
      MvPolynomial.X v - diagρ N y (MvPolynomial.X v) ∈ diagIdeal N y := by
    rintro ⟨i, j⟩
    fin_cases j
    · exact hvar0 i
    · exact hvar1 i
  refine MvPolynomial.induction_on (motive := fun F => F - diagρ N y F ∈ diagIdeal N y) F
    (fun a => ?_) (fun p q hp hq => ?_) (fun p n hp => ?_)
  · rw [diagρ_C, sub_self]
    exact (diagIdeal N y).zero_mem
  · rw [map_add]
    convert (diagIdeal N y).add_mem hp hq using 1
    ring
  · rw [map_mul]
    have hx := hvar n
    have : p * MvPolynomial.X n - diagρ N y p * diagρ N y (MvPolynomial.X n)
        = (p - diagρ N y p) * MvPolynomial.X n
          + diagρ N y p * (MvPolynomial.X n - diagρ N y (MvPolynomial.X n)) := by
      ring
    rw [this]
    exact (diagIdeal N y).add_mem ((diagIdeal N y).mul_mem_right _ hp)
      ((diagIdeal N y).mul_mem_left _ hx)

/-- **The ideal is the kernel of `Φ`.** -/
lemma diagIdeal_eq_ker (N : ℕ) (y : Fin (N + 1) × Fin 2 → ℂ)
    (hy : ∀ i : Fin (N + 1), y (i, 0) ≠ 0) :
    diagIdeal N y = RingHom.ker (diagΦ N y) := by
  refine le_antisymm ?_ ?_
  · rw [diagIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    refine RingHom.mem_ker.mpr ?_
    simp only [map_sub, map_mul, diagΦ_C, diagΦ_X_zero, diagΦ_X_one]
    rw [← mul_assoc, ← MvPolynomial.C_mul, mul_div_cancel₀ (y (i, 1)) (hy i), sub_self]
  · intro F hF
    have hF0 : diagΦ N y F = 0 := RingHom.mem_ker.mp hF
    have h := diag_reduce N y hy F
    have h0 : diagρ N y F = 0 := by rw [diagρ, RingHom.comp_apply, hF0, map_zero]
    rwa [h0, sub_zero] at h

/-! ## Multihomogeneity -/

/-- An ideal generated by multihomogeneous elements is multihomogeneous. -/
lemma srelDiag_multiHom_span {N : ℕ} (S : Set (MR N))
    (hS : ∀ x ∈ S, ∃ d : Fin (N + 1) →₀ ℕ, x ∈ homPiece N d) :
    MultiHom N (Ideal.span S) := by
  letI : GradedAlgebra (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N)) :=
    MvPolynomial.weightedGradedAlgebra ℂ (mdeg N)
  have hgen : ∀ x ∈ S,
      SetLike.IsHomogeneousElem (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N)) x :=
    fun x hx => hS x hx
  have hI : (Ideal.span S).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N)) :=
    Ideal.homogeneous_span _ _ hgen
  intro p hp d
  exact (MvPolynomial.mem_iff_weightedHomogeneousComponent_mem ℂ (mdeg N) hI p).mp hp d

/-- Each diagonal generator is multihomogeneous of multidegree `e_i`. -/
lemma srelDiag_gen_homPiece (N : ℕ) (y : Fin (N + 1) × Fin 2 → ℂ) :
    ∀ x ∈ Set.range (fun i : Fin (N + 1) =>
      (MvPolynomial.C (y (i, 0)) : MR N) * (MvPolynomial.X (i, 1) : MR N)
        - (MvPolynomial.C (y (i, 1)) : MR N) * (MvPolynomial.X (i, 0) : MR N)),
    ∃ d, x ∈ homPiece N d := by
  rintro _ ⟨i, rfl⟩
  refine ⟨Finsupp.single i 1, ?_⟩
  rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]
  have hA : MvPolynomial.IsWeightedHomogeneous (mdeg N)
      ((MvPolynomial.C (y (i, 0)) : MR N) * MvPolynomial.X (i, 1)) (Finsupp.single i 1) := by
    have h := (MvPolynomial.isWeightedHomogeneous_C (mdeg N) (y (i, 0))).mul
      (MvPolynomial.isWeightedHomogeneous_X ℂ (mdeg N) (i, 1))
    simpa [mdeg] using h
  have hB : MvPolynomial.IsWeightedHomogeneous (mdeg N)
      ((MvPolynomial.C (y (i, 1)) : MR N) * MvPolynomial.X (i, 0)) (Finsupp.single i 1) := by
    have h := (MvPolynomial.isWeightedHomogeneous_C (mdeg N) (y (i, 1))).mul
      (MvPolynomial.isWeightedHomogeneous_X ℂ (mdeg N) (i, 0))
    simpa [mdeg] using h
  exact hA.sub hB

lemma diagIdeal_multiHom (N : ℕ) (y : Fin (N + 1) × Fin 2 → ℂ) :
    MultiHom N (diagIdeal N y) :=
  srelDiag_multiHom_span _ (srelDiag_gen_homPiece N y)

/-! ## Primality and height -/

lemma diagIdeal_isPrime (N : ℕ) (y : Fin (N + 1) × Fin 2 → ℂ)
    (hy : ∀ i : Fin (N + 1), y (i, 0) ≠ 0) : (diagIdeal N y).IsPrime :=
  (diagIdeal_eq_ker N y hy).symm ▸ RingHom.ker_isPrime (diagΦ N y)

/-- `dim ℂ[X_0, …, X_{n-1}] = n`. -/
lemma srelDiag_ringKrullDim_mvPoly (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) ℂ) = ((n : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite (ι := Fin n) (R := ℂ),
    ringKrullDim_eq_zero_of_field]
  simp [Nat.card_eq_fintype_card]

lemma diagIdeal_height (N : ℕ) (y : Fin (N + 1) × Fin 2 → ℂ)
    (hy : ∀ i : Fin (N + 1), y (i, 0) ≠ 0) :
    (diagIdeal N y).height = ((N + 1 : ℕ) : ℕ∞) := by
  have hK := diagIdeal_eq_ker N y hy
  haveI hprime : (diagIdeal N y).IsPrime := hK.symm ▸ RingHom.ker_isPrime (diagΦ N y)
  have hsurj : Function.Surjective (diagΦ N y) := fun q =>
    ⟨diagSec N q, by
      have h := DFunLike.congr_fun (diagΦ_comp_diagSec N y) q
      simpa using h⟩
  have e : MR N ⧸ diagIdeal N y ≃+* MvPolynomial (Fin (N + 1)) ℂ :=
    hK.symm ▸ RingHom.quotientKerEquivOfSurjective hsurj
  have hdim := mvpoly_dim_formula (σ := Fin (N + 1) × Fin 2) (p := diagIdeal N y)
  have hR : ringKrullDim (MR N) = ((2 * (N + 1) : ℕ) : WithBot ℕ∞) := by
    show ringKrullDim (MvPolynomial (Fin (N + 1) × Fin 2) ℂ) = _
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite
        (ι := Fin (N + 1) × Fin 2) (R := ℂ),
      ringKrullDim_eq_zero_of_field]
    simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_ofNat, zero_add]
    ring
  rw [hR, ringKrullDim_eq_of_ringEquiv e, srelDiag_ringKrullDim_mvPoly (N + 1)] at hdim
  have hcoe : ((diagIdeal N y).height : WithBot ℕ∞) + ((N + 1 : ℕ) : WithBot ℕ∞)
      = (((diagIdeal N y).height + ((N + 1 : ℕ) : ℕ∞)) : WithBot ℕ∞) :=
    (WithBot.coe_add (diagIdeal N y).height (((N + 1 : ℕ) : ℕ∞))).symm
  rw [hcoe] at hdim
  have hnat : (diagIdeal N y).height + ((N + 1 : ℕ) : ℕ∞) = (((2 * (N + 1) : ℕ)) : ℕ∞) :=
    WithBot.coe_inj.mp hdim
  have hne : (diagIdeal N y).height ≠ ⊤ := by
    intro h
    rw [h] at hnat
    rw [top_add] at hnat
    exact ENat.natCast_ne_top (2 * (N + 1)) hnat.symm
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hn] at hnat
  rw [← Nat.cast_add] at hnat
  have h2 : n + (N + 1) = 2 * (N + 1) := ENat.natCast_inj.mp hnat
  rw [← hn, show n = N + 1 from by omega]

/-! ## The monomials `∏ X (i,0) ^ (t * D i)` are not in the ideal -/

lemma diag_mono_notMem (N : ℕ) (y : Fin (N + 1) × Fin 2 → ℂ)
    (hy : ∀ i : Fin (N + 1), y (i, 0) ≠ 0) (D : Fin (N + 1) →₀ ℕ) (t : ℕ) :
    (∏ i : Fin (N + 1), (MvPolynomial.X (i, 0) : MR N) ^ (t * D i))
      ∉ diagIdeal N y := by
  intro hF
  have hF0 : diagΦ N y (∏ i : Fin (N + 1), (MvPolynomial.X (i, 0) : MR N) ^ (t * D i)) = 0 :=
    RingHom.mem_ker.mp ((diagIdeal_eq_ker N y hy) ▸ hF)
  rw [map_prod] at hF0
  simp only [map_pow, diagΦ_X_zero] at hF0
  exact (Finset.prod_ne_zero_iff.mpr
    (fun i _ => pow_ne_zero _ (MvPolynomial.X_ne_zero i))) hF0

end

end Work.BW.RB

namespace Work.BW.RB

theorem srelcut_diagonal_c {N : ℕ} (D : Fin (N + 1) →₀ ℕ)
    (y : Fin (N + 1) × Fin 2 → ℂ) (hy : ∀ i : Fin (N + 1), y (i, 0) ≠ 0) :
    (Ideal.span (Set.range (fun i : Fin (N + 1) =>
      (MvPolynomial.C (y (i, 0)) : MR N) * (MvPolynomial.X (i, 1) : MR N)
        - (MvPolynomial.C (y (i, 1)) : MR N) * (MvPolynomial.X (i, 0) : MR N)))).IsPrime ∧
    (Ideal.span (Set.range (fun i : Fin (N + 1) =>
      (MvPolynomial.C (y (i, 0)) : MR N) * (MvPolynomial.X (i, 1) : MR N)
        - (MvPolynomial.C (y (i, 1)) : MR N) * (MvPolynomial.X (i, 0) : MR N)))).height = ((N + 1 : ℕ) : ℕ∞) ∧
    MultiHom N (Ideal.span (Set.range (fun i : Fin (N + 1) =>
      (MvPolynomial.C (y (i, 0)) : MR N) * (MvPolynomial.X (i, 1) : MR N)
        - (MvPolynomial.C (y (i, 1)) : MR N) * (MvPolynomial.X (i, 0) : MR N)))) ∧
    (∀ t : ℕ, (∏ i : Fin (N + 1), (MvPolynomial.X (i, 0) : MR N) ^ (t * D i)) ∉
      Ideal.span (Set.range (fun i : Fin (N + 1) =>
        (MvPolynomial.C (y (i, 0)) : MR N) * (MvPolynomial.X (i, 1) : MR N)
          - (MvPolynomial.C (y (i, 1)) : MR N) * (MvPolynomial.X (i, 0) : MR N)))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact diagIdeal_isPrime N y hy
  · exact diagIdeal_height N y hy
  · exact diagIdeal_multiHom N y
  · intro t
    exact diag_mono_notMem N y hy D t

end Work.BW.RB
