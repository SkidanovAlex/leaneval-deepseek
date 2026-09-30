import Mathlib
import Submission.Work.BW.GradedHilbDefs
import Submission.Work.BW.HilbSerreDefs


/-!
# The quotient of a multihomogeneous ideal is a graded module

Let `R = MR N = ℂ[X_{i,j}]` be the coordinate ring of `(P¹)^{N+1}`, multigraded by
`Fin (N+1) →₀ ℤ` through `wZ N` (both variables of an `i`-th factor receive weight `eᵢ`),
with graded pieces `pieceZ N u`.  For a multihomogeneous ideal `I`, the quotient `R ⧸ I` is
again a `wZ`-graded `R`-module, its graded pieces are the images of the `pieceZ N u`, they are
finite dimensional over `ℂ`, and their dimensions are the values of `hilbIdeal`.

The main mathematical content is that a multihomogeneous ideal is the sum of its graded pieces
(`iSup_pieceZ_inf`), together with the identification of the `ℤ`-grading `wZ` with the
`ℕ`-grading `mdeg` on the non-negative cone (`weight_wZ_eq_iff`, `pieceZ_castF_eq_homPiece`).
-/

namespace Work.BW

open MvPolynomial
open HilbSerre

variable {N : ℕ}

/-! ### Weight computations for the two gradings `wZ` (into `ℤ^{N+1}`) and `mdeg` (into `ℕ^{N+1}`) -/

theorem castF_mdeg (v : Fin (N + 1) × Fin 2) : castF (mdeg N v) = wZ N v := by
  ext i
  rw [castF_apply, mdeg, wZ, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp

theorem castF_injective : Function.Injective (castF (N := N)) := by
  intro a b h
  ext i
  have h2 := congrArg (fun f : Fin (N + 1) →₀ ℤ => f i) h
  simp only [castF_apply] at h2
  exact_mod_cast h2

private theorem weight_mdeg_apply (D : Fin (N + 1) × Fin 2 →₀ ℕ) (i : Fin (N + 1)) :
    (Finsupp.weight (mdeg N) D) i = ∑ x, D x * (mdeg N x) i := by
  rw [Finsupp.weight_eq_sum]
  rw [show (∑ i, D i • mdeg N i)
      = ∑ i ∈ (Finset.univ : Finset (Fin (N + 1) × Fin 2)), D i • mdeg N i from rfl]
  rw [Finset.sum_apply']
  exact Finset.sum_congr rfl fun v _ => by rw [Finsupp.smul_apply, smul_eq_mul]

theorem weight_wZ_apply (D : Fin (N + 1) × Fin 2 →₀ ℕ) (i : Fin (N + 1)) :
    (Finsupp.weight (wZ N) D) i = ∑ x, (D x : ℤ) * (wZ N x) i := by
  rw [Finsupp.weight_eq_sum]
  rw [show (∑ i, D i • wZ N i)
      = ∑ i ∈ (Finset.univ : Finset (Fin (N + 1) × Fin 2)), D i • wZ N i from rfl]
  rw [Finset.sum_apply']
  exact Finset.sum_congr rfl fun v _ => by rw [Finsupp.smul_apply, nsmul_eq_mul]

/-- The two weight functions agree, after casting `ℕ^{N+1}` to `ℤ^{N+1}`. -/
theorem castF_weight (D : Fin (N + 1) × Fin 2 →₀ ℕ) :
    castF (Finsupp.weight (mdeg N) D) = Finsupp.weight (wZ N) D := by
  ext i
  rw [castF_apply, weight_mdeg_apply, weight_wZ_apply, Nat.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Nat.cast_mul]; congr 1
  rw [mdeg, wZ, Finsupp.single_apply, Finsupp.single_apply]; split_ifs <;> simp

/-- Every coordinate of `weight (wZ N) D` is non-negative. -/
theorem weight_wZ_nonneg (D : Fin (N + 1) × Fin 2 →₀ ℕ) (i : Fin (N + 1)) :
    0 ≤ (Finsupp.weight (wZ N) D) i := by
  rw [weight_wZ_apply]
  refine Finset.sum_nonneg fun x _ => ?_
  refine mul_nonneg (by positivity) ?_
  rw [wZ, Finsupp.single_apply]; split_ifs <;> norm_num

/-- On a non-negative multidegree, the `wZ`-grading coincides with the `mdeg`-grading. -/
theorem weight_wZ_eq_iff (u : Fin (N + 1) →₀ ℤ) (hu : ∀ i, 0 ≤ u i)
    (d : Fin (N + 1) × Fin 2 →₀ ℕ) :
    (Finsupp.weight (wZ N) d = u) ↔ (Finsupp.weight (mdeg N) d = toNatF u) := by
  constructor
  · intro h
    have h2 : castF (Finsupp.weight (mdeg N) d) = u := by rw [castF_weight]; exact h
    have h3 : toNatF (castF (Finsupp.weight (mdeg N) d)) = toNatF u := congrArg toNatF h2
    rw [toNatF_castF] at h3
    exact h3
  · intro h
    rw [← castF_weight, h, castF_toNatF u hu]

/-- Summing the coordinates of `weight (mdeg N) D` gives the ordinary total degree. -/
theorem weight_sum_coord_mdeg (D : Fin (N + 1) × Fin 2 →₀ ℕ) :
    Finsupp.weight (fun v : Fin (N + 1) × Fin 2 => ∑ i, (mdeg N v) i) D
      = ∑ i, (Finsupp.weight (mdeg N) D) i := by
  have h1 : Finsupp.weight (fun v : Fin (N + 1) × Fin 2 => ∑ i, (mdeg N v) i) D
      = ∑ v, ∑ i, D v * (mdeg N v) i := by
    rw [Finsupp.weight_eq_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul]
  have h2 : ∑ i, (Finsupp.weight (mdeg N) D) i = ∑ i, ∑ v, D v * (mdeg N v) i :=
    Finset.sum_congr rfl fun i _ => weight_mdeg_apply D i
  rw [h1, h2, Finset.sum_comm]

/-! ### The graded pieces of `MR N` -/

/-- Each multigraded piece of the `mdeg`-grading is finite dimensional over `ℂ`. -/
theorem homPiece_finite (d : Fin (N + 1) →₀ ℕ) :
    Module.Finite ℂ ↥(homPiece N d) := by
  have hW0 : ∀ v : Fin (N + 1) × Fin 2, (∑ i, (mdeg N v) i) ≠ 0 := by
    intro v
    have hv : ∑ i, (mdeg N v) i = 1 := by
      simp only [mdeg, Finsupp.single_apply]
      rw [Finset.sum_ite_eq Finset.univ v.1 (fun _ => 1), ite_eq_left (Finset.mem_univ v.1)]
    rw [hv]; norm_num
  have hfin : ({(D : Fin (N + 1) × Fin 2 →₀ ℕ) | Finsupp.weight (mdeg N) D = d}).Finite := by
    refine Set.Finite.subset
      (Finsupp.finite_of_nat_weight_eq (fun v => ∑ i, (mdeg N v) i) hW0 (∑ i, d i)) ?_
    intro D hD
    simp only [Set.mem_ofPred_eq] at hD ⊢
    rw [weight_sum_coord_mdeg, hD]
  rw [homPiece, MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported,
    ← MvPolynomial.restrictSupport]
  haveI := hfin.to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport ℂ _)

/-- Every `wZ`-graded piece of `MR N` is contained in the corresponding `mdeg`-graded piece. -/
theorem pieceZ_le_homPiece (u : Fin (N + 1) →₀ ℤ) : pieceZ N u ≤ homPiece N (toNatF u) := by
  intro p hp
  rw [mem_pieceZ] at hp
  rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]
  intro d hd
  have h1 : Finsupp.weight (wZ N) d = u := hp hd
  have h2 : castF (Finsupp.weight (mdeg N) d) = u := by rw [castF_weight]; exact h1
  have h3 : toNatF (castF (Finsupp.weight (mdeg N) d)) = toNatF u := congrArg toNatF h2
  rw [toNatF_castF] at h3
  exact h3

/-- On the non-negative cone the two gradings have the same pieces. -/
theorem pieceZ_castF_eq_homPiece (d : Fin (N + 1) →₀ ℕ) :
    pieceZ N (castF d) = homPiece N d := by
  apply le_antisymm
  · calc pieceZ N (castF d) ≤ homPiece N (toNatF (castF d)) := pieceZ_le_homPiece (castF d)
      _ = homPiece N d := by rw [toNatF_castF]
  · intro p hp
    rw [mem_pieceZ]
    rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule] at hp
    intro m hm
    have h1 : Finsupp.weight (mdeg N) m = d := hp hm
    have h2 : Finsupp.weight (wZ N) m = castF d := by rw [← castF_weight, h1]
    exact h2

/-- Every `wZ`-graded piece of `MR N` is finite dimensional over `ℂ`. -/
theorem pieceZ_finite (u : Fin (N + 1) →₀ ℤ) : Module.Finite ℂ ↥(pieceZ N u) :=
  Module.Finite.iff_fg.mpr
    (Submodule.FG.of_le (Module.Finite.iff_fg.mp (homPiece_finite (toNatF u)))
      (pieceZ_le_homPiece u))

/-- Graded pieces of negative multidegree vanish. -/
theorem pieceZ_eq_bot_of_neg (u : Fin (N + 1) →₀ ℤ) (h : ∃ i, u i < 0) :
    pieceZ N u = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro p hp
  rw [mem_pieceZ] at hp
  ext d
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra hd
  have hw := hp hd
  obtain ⟨i, hi⟩ := h
  have h2 := congrArg (fun f : Fin (N + 1) →₀ ℤ => f i) hw
  have h3 : 0 ≤ (Finsupp.weight (wZ N) d) i := weight_wZ_nonneg d i
  rw [h2] at h3
  omega

/-! ### Weighted homogeneous components -/

/-- On a non-negative multidegree the `wZ`- and `mdeg`-components agree. -/
theorem weightedHomogeneousComponent_wZ_eq_of_nonneg (u : Fin (N + 1) →₀ ℤ)
    (hu : ∀ i, 0 ≤ u i) (p : MR N) :
    MvPolynomial.weightedHomogeneousComponent (wZ N) u p
      = MvPolynomial.weightedHomogeneousComponent (mdeg N) (toNatF u) p := by
  ext d
  rw [MvPolynomial.coeff_weightedHomogeneousComponent (w := wZ N) u p d,
    MvPolynomial.coeff_weightedHomogeneousComponent (w := mdeg N) (toNatF u) p d]
  by_cases h : Finsupp.weight (wZ N) d = u
  · rw [if_pos h, if_pos ((weight_wZ_eq_iff u hu d).mp h)]
  · rw [if_neg h, if_neg]
    intro hc
    exact h ((weight_wZ_eq_iff u hu d).mpr hc)

/-- Components of negative multidegree vanish. -/
theorem weightedHomogeneousComponent_wZ_eq_zero_of_neg (u : Fin (N + 1) →₀ ℤ)
    (h : ∃ i, u i < 0) (p : MR N) :
    MvPolynomial.weightedHomogeneousComponent (wZ N) u p = 0 := by
  apply MvPolynomial.weightedHomogeneousComponent_eq_zero'
  intro d _ hc
  obtain ⟨i, hi⟩ := h
  have h2 := congrArg (fun f : Fin (N + 1) →₀ ℤ => f i) hc
  have h3 : 0 ≤ (Finsupp.weight (wZ N) d) i := weight_wZ_nonneg d i
  rw [h2] at h3
  omega

/-! ### The ideal is the sum of its graded pieces -/

/-- A multihomogeneous ideal is the sum of its `mdeg`-graded pieces. -/
theorem iSup_homPiece_inf (I : Ideal (MR N)) (hI : MultiHom N I) :
    (⨆ d : Fin (N + 1) →₀ ℕ, homPiece N d ⊓ I.restrictScalars ℂ) = I.restrictScalars ℂ := by
  classical
  apply le_antisymm
  · exact iSup_le fun d => inf_le_right
  · intro x hx
    letI : DirectSum.Decomposition (homPiece N) := MvPolynomial.weightedDecomposition ℂ (mdeg N)
    rw [← DirectSum.sum_support_decompose (homPiece N) x]
    refine Submodule.sum_mem _ fun d _ => ?_
    refine Submodule.mem_iSup_of_mem d ?_
    refine ⟨(DirectSum.decompose (homPiece N) x d).2, ?_⟩
    have hdec : ((DirectSum.decompose (homPiece N) x) d : MR N)
        = MvPolynomial.weightedHomogeneousComponent (mdeg N) d x := by
      rw [← DirectSum.Decomposition.decompose'_eq]
      exact MvPolynomial.weightedDecomposition.decompose'_apply ℂ (mdeg N) x d
    rw [hdec]
    exact hI x hx d

/-- A multihomogeneous ideal is the sum of its `wZ`-graded pieces. -/
theorem iSup_pieceZ_inf (I : Ideal (MR N)) (hI : MultiHom N I) :
    (⨆ u : Fin (N + 1) →₀ ℤ, pieceZ N u ⊓ I.restrictScalars ℂ) = I.restrictScalars ℂ := by
  apply le_antisymm
  · exact iSup_le fun u => inf_le_right
  · calc I.restrictScalars ℂ
        = ⨆ d : Fin (N + 1) →₀ ℕ, homPiece N d ⊓ I.restrictScalars ℂ :=
          (iSup_homPiece_inf I hI).symm
      _ ≤ ⨆ u : Fin (N + 1) →₀ ℤ, pieceZ N u ⊓ I.restrictScalars ℂ := by
          refine iSup_le fun d => ?_
          rw [← pieceZ_castF_eq_homPiece d]
          exact le_iSup (fun u => pieceZ N u ⊓ I.restrictScalars ℂ) (castF d)

/-! ### The main statement -/

set_option maxHeartbeats 4000000 in
theorem quotient_isGrading (N : ℕ) (I : Ideal (MR N)) (hI : MultiHom N I) :
    IsGrading N (fun u => Submodule.map (Ideal.Quotient.mkₐ ℂ I).toLinearMap (pieceZ N u)) ∧
      Module.Finite (MR N) (MR N ⧸ I) ∧
      (∀ u, Module.Finite ℂ
        ↥(Submodule.map (Ideal.Quotient.mkₐ ℂ I).toLinearMap (pieceZ N u))) ∧
      (∀ u, Module.finrank ℂ
          ↥(Submodule.map (Ideal.Quotient.mkₐ ℂ I).toLinearMap (pieceZ N u)) = hilbIdeal N I u) := by
  classical
  have hA : DirectSum.IsInternal (pieceZ N) := by
    letI : DirectSum.Decomposition (pieceZ N) := MvPolynomial.weightedDecomposition ℂ (wZ N)
    exact DirectSum.Decomposition.isInternal (pieceZ N)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- the images of the graded pieces form an internal direct sum
    have h := isInternal_map_mkQ (pieceZ N) (fun u => pieceZ N u ⊓ I.restrictScalars ℂ)
      (fun u => inf_le_left) hA
    rw [iSup_pieceZ_inf I hI] at h
    exact h
  · -- multiplication by a variable shifts the grading
    intro v u m hm
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hm
    refine Submodule.mem_map.mpr ⟨(MvPolynomial.X v : MR N) * x, ?_, ?_⟩
    · rw [mem_pieceZ, show u + wZ N v = wZ N v + u from add_comm _ _]
      exact (MvPolynomial.isWeightedHomogeneous_X ℂ (wZ N) v).mul ((mem_pieceZ N u x).mp hx)
    · show (Ideal.Quotient.mkₐ ℂ I) ((MvPolynomial.X v : MR N) * x)
          = (MvPolynomial.X v) • (Ideal.Quotient.mkₐ ℂ I) x
      first
      | (rw [map_mul, Algebra.smul_def]; rfl)
      | (rw [map_mul]
         exact (Algebra.smul_def (MvPolynomial.X v) ((Ideal.Quotient.mkₐ ℂ I) x)).symm)
      | (rw [← Ideal.Quotient.mk_eq_mk,
            ← Submodule.Quotient.mk_smul (p := (I : Submodule (MR N) (MR N)))
              (MvPolynomial.X v) x]
         simp)
  · -- pieces of negative multidegree vanish
    intro u hu
    rw [pieceZ_eq_bot_of_neg u hu, Submodule.map_bot]
  · exact Module.Finite.quotient (MR N) I
  · intro u
    haveI : Module.Finite ℂ ↥(pieceZ N u) := pieceZ_finite u
    exact Module.Finite.map (pieceZ N u) (Ideal.Quotient.mkₐ ℂ I).toLinearMap
  · intro u
    rw [hilbIdeal]
    have hkerm : (Ideal.Quotient.mkₐ ℂ I).toLinearMap.ker = I.restrictScalars ℂ := by
      ext x
      rw [LinearMap.mem_ker, Submodule.restrictScalars_mem,
        show (Ideal.Quotient.mkₐ ℂ I).toLinearMap x = Ideal.Quotient.mk I x from rfl]
      exact Ideal.Quotient.eq_zero_iff_mem
    have hker : ((Ideal.Quotient.mkₐ ℂ I).toLinearMap.comp (pieceZ N u).subtype).ker
        = Submodule.comap (pieceZ N u).subtype (I.restrictScalars ℂ) := by
      rw [LinearMap.ker_comp, hkerm]
    have hrange : ((Ideal.Quotient.mkₐ ℂ I).toLinearMap.comp (pieceZ N u).subtype).range
        = Submodule.map (Ideal.Quotient.mkₐ ℂ I).toLinearMap (pieceZ N u) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    rw [← hrange]
    rw [← hker]
    exact (LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange
      ((Ideal.Quotient.mkₐ ℂ I).toLinearMap.comp (pieceZ N u).subtype))).symm

end Work.BW
