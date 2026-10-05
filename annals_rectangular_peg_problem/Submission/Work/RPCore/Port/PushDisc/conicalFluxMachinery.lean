import Mathlib

/-!
# The conical flux machinery

Shared machinery for the signed-volume route to the degree of a self-map of an even sphere:
the determinant calculus, the divergence theorem on `EuclideanSpace ℝ (Fin N)`, the conical flux
field, the annular cut-off, and the pointwise divergence identity
`divE (chi • fluxT Φ t) = chi * ∂_t det (jacM Φ)`.

Extracted from `exists_sphereDegree_even_sphere.lean` so that the later stages of the argument can
be developed and delegated independently of the target theorem.
-/

/-!
# The sphere degree on the even spheres

The missing chapter of the odd-`n` drop-region obstruction: the existence of a `ℤ`-valued
homotopy invariant of the self-maps of the unit sphere of `ℝ^{2k+1}` with `deg id = 1` and
`deg (-id) = -1`.

As `Work.RPCore.Port.PushDisc.no_homotopy_of_sphereDegree` shows, this is *equivalent* to the statement
that the identity and the antipodal map of `S^{2k}` are not homotopic — the classical degree
theorem.  This file builds it from scratch: a smooth homotopy of sphere self-maps is turned into a
conical (radially `1`-homogeneous) family `Φ : ℝ × E → E` of norm-preserving maps, and the
invariant is the signed volume `∫ χ(‖y‖) det (D_yΦ_t(y)) dy`; the key point is that the flux field
`W_t := adj(D_yΦ_t) · ∂_tΦ_t` is tangential and satisfies `div W_t = ∂_t det (D_yΦ_t)`, so the
divergence identity (on a box, available in Mathlib) makes the invariant constant in `t`.

The bookkeeping below is the determinant calculus of a family of matrices: Jacobi's formula (the
multilinear expansion of the determinant), the Piola cancellation (the antisymmetry of the
determinant under exchanging two columns) and the resulting flux identity. -/

namespace Work.RPCore.Port.PushDisc

open scoped Matrix

/-! ## The determinant calculus of a matrix-valued family -/

/-- **The multilinear expansion of the determinant.**  The determinant of the matrix with columns
`w` is the Leibniz sum. -/
lemma det_updateCol_eq {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) (z : Fin d → ℝ) :
    (M.updateCol j z).det
      = ∑ σ : Equiv.Perm (Fin d),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * (z (σ j) * ∏ i ∈ Finset.univ.erase j, M (σ i) i) := by
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ j)]
  rw [← Finset.erase_eq, Matrix.updateCol_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  have hij : i ≠ j := (Finset.mem_erase.mp hi).1
  rw [Matrix.updateCol_ne hij]

/-- **Jacobi's formula for a family of matrices.**  The derivative of the determinant of a family
of matrices is the sum of the determinants obtained by replacing one column by the derivative of
that column. -/
theorem fderiv_det_apply {d : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P → Matrix (Fin d) (Fin d) ℝ) (A' : Fin d → Fin d → P →L[ℝ] ℝ)
    (p : P) (w : P) (hA : ∀ i j, HasFDerivAt (fun q => A q i j) (A' i j) p) :
    fderiv ℝ (fun q => (A q).det) p w = ∑ j, ((A p).updateCol j (fun i => A' i j w)).det := by
  have hsum : HasFDerivAt
      (∑ σ : Equiv.Perm (Fin d), fun q => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A q (σ i) i)
      (∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℝ) •
        (∑ i, (∏ l ∈ Finset.univ.erase i, A p (σ l) l) • (A' (σ i) i))) p := by
    refine HasFDerivAt.sum (fun σ _ => ?_)
    exact (HasFDerivAt.finsetProd (fun i _ => hA (σ i) i)).const_mul _
  have hfun : (fun q => (A q).det)
      = (∑ σ : Equiv.Perm (Fin d),
          fun q => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A q (σ i) i) := by
    funext q
    rw [Finset.sum_apply, Matrix.det_apply']
  rw [hfun, hsum.fderiv, sum_apply]
  simp only [smul_apply, smul_eq_mul, sum_apply]
  simp only [det_updateCol_eq]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun σ _ => ?_
  ring

/-- Replacing two distinct columns commutes. -/
lemma updateCol_updateCol_comm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) {i j : Fin d} (hij : i ≠ j)
    (x y : Fin d → ℝ) :
    (M.updateCol i x).updateCol j y = (M.updateCol j y).updateCol i x := by
  refine Matrix.ext fun a b => ?_
  simp only [Matrix.updateCol_apply]
  by_cases h1 : b = i <;> by_cases h2 : b = j <;> simp_all

/-- Replacing the same column twice: only the last replacement counts. -/
lemma updateCol_updateCol_same {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (j : Fin d)
    (x y : Fin d → ℝ) : (M.updateCol j x).updateCol j y = M.updateCol j y := by
  refine Matrix.ext fun a b => ?_
  simp only [Matrix.updateCol_apply]
  by_cases h : b = j <;> simp_all

/-- **Exchanging two replaced columns flips the sign.**  This is the antisymmetry of the
determinant in the form needed for the Piola cancellation. -/
lemma det_updateCol_swap {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) {i j : Fin d} (hij : i ≠ j)
    (x y : Fin d → ℝ) :
    ((M.updateCol i x).updateCol j y).det = - ((M.updateCol j x).updateCol i y).det := by
  -- the matrix `M` with columns `i`, `j` replaced by `x+y` has two equal columns
  have hzero : ((M.updateCol i (x + y)).updateCol j (x + y)).det = 0 := by
    have h := Matrix.det_updateCol_eq_zero (M := M.updateCol i (x + y)) (i := i) (j := j) hij
    rw [show (fun k => (M.updateCol i (x + y)) k i) = (x + y) from
      funext fun k => Matrix.updateCol_self] at h
    exact h
  have e1 : (M.updateCol j (x + y)).updateCol i (x + y)
      = (M.updateCol i (x + y)).updateCol j (x + y) :=
    (updateCol_updateCol_comm M hij (x + y) (x + y)).symm
  have e2 : (M.updateCol j (x + y)).updateCol i x = (M.updateCol i x).updateCol j (x + y) :=
    (updateCol_updateCol_comm M hij x (x + y)).symm
  have e3 : (M.updateCol j (x + y)).updateCol i y = (M.updateCol i y).updateCol j (x + y) :=
    (updateCol_updateCol_comm M hij y (x + y)).symm
  have hspliti := Matrix.det_updateCol_add (M.updateCol j (x + y)) i x y
  rw [e1, e2, e3] at hspliti
  have hsplitj : ∀ z : Fin d → ℝ,
      ((M.updateCol i z).updateCol j (x + y)).det
        = ((M.updateCol i z).updateCol j x).det + ((M.updateCol i z).updateCol j y).det :=
    fun z => Matrix.det_updateCol_add (M.updateCol i z) j x y
  have hz1 : ((M.updateCol i x).updateCol j x).det = 0 := by
    have h := Matrix.det_updateCol_eq_zero (M := M.updateCol i x) (i := i) (j := j) hij
    rw [show (fun k => (M.updateCol i x) k i) = x from
      funext fun k => Matrix.updateCol_self] at h
    exact h
  have hz2 : ((M.updateCol i y).updateCol j y).det = 0 := by
    have h := Matrix.det_updateCol_eq_zero (M := M.updateCol i y) (i := i) (j := j) hij
    rw [show (fun k => (M.updateCol i y) k i) = y from
      funext fun k => Matrix.updateCol_self] at h
    exact h
  have hfirst : ((M.updateCol i x).updateCol j (x + y)).det = ((M.updateCol i x).updateCol j y).det := by
    rw [hsplitj x, hz1, zero_add]
  have hsecond : ((M.updateCol i y).updateCol j (x + y)).det = ((M.updateCol j x).updateCol i y).det := by
    rw [hsplitj y, hz2, add_zero]
    rw [← updateCol_updateCol_comm M hij y x]
  rw [hspliti, hfirst, hsecond] at hzero
  linarith

/-- **The Piola cancellation.**  If the summand is antisymmetric off the diagonal, the sum over
`j` and `l ≠ j` vanishes. -/
lemma sum_offDiag_antisymm_eq_zero {d : ℕ} (T : Fin d → Fin d → ℝ)
    (hanti : ∀ j l : Fin d, j ≠ l → T j l + T l j = 0) :
    ∑ j : Fin d, ∑ l ∈ Finset.univ.erase j, T j l = 0 := by
  have hstep : ∀ j : Fin d, (∑ l ∈ Finset.univ.erase j, T j l)
      = ∑ l : Fin d, (if j ≠ l then T j l else 0) := by
    intro j
    rw [← Finset.filter_ne Finset.univ j, Finset.sum_filter]
  simp only [hstep]
  have hanti' : ∀ j l : Fin d, (if j ≠ l then T j l else 0)
      = - (if l ≠ j then T l j else 0) := by
    intro j l
    by_cases h : j ≠ l
    · rw [if_pos h, if_pos (Ne.symm h)]
      have := hanti j l h
      linarith
    · rw [if_neg h, if_neg (fun h' => h h'.symm), neg_zero]
  have hS : (∑ j : Fin d, ∑ l : Fin d, (if j ≠ l then T j l else 0))
      = - (∑ j : Fin d, ∑ l : Fin d, (if j ≠ l then T j l else 0)) := by
    have hren : (∑ j : Fin d, ∑ l : Fin d, (if l ≠ j then T l j else 0))
        = ∑ j : Fin d, ∑ l : Fin d, (if j ≠ l then T j l else 0) := by
      rw [Finset.sum_comm]
    calc (∑ j : Fin d, ∑ l : Fin d, (if j ≠ l then T j l else 0))
        = ∑ j : Fin d, ∑ l : Fin d, - (if l ≠ j then T l j else 0) := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
          rw [hanti' j l]
      _ = - (∑ j : Fin d, ∑ l : Fin d, (if l ≠ j then T l j else 0)) := by
          have hinner : ∀ j : Fin d, (∑ l : Fin d, -(if l ≠ j then T l j else 0))
              = - (∑ l : Fin d, (if l ≠ j then T l j else 0)) :=
            fun j => Finset.sum_neg_distrib _
          rw [Finset.sum_congr rfl (fun j _ => hinner j), Finset.sum_neg_distrib]
      _ = - (∑ j : Fin d, ∑ l : Fin d, (if j ≠ l then T j l else 0)) := by rw [hren]
  linarith

/-- **The flux identity (abstract form).**  For a family of matrices whose entries have the mixed
partial symmetry of a Jacobian, the derivative in the `t`-direction of the determinant equals the
divergence of the flux field (the determinant with one column replaced by the velocity). -/
theorem fderiv_flux_identity {d : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P → Matrix (Fin d) (Fin d) ℝ) (v : P → Fin d → ℝ)
    (A' : Fin d → Fin d → P →L[ℝ] ℝ) (V' : Fin d → P →L[ℝ] ℝ)
    (tdir : P) (ydir : Fin d → P) (p : P)
    (hA : ∀ i l, HasFDerivAt (fun q => A q i l) (A' i l) p)
    (hv : ∀ i, HasFDerivAt (fun q => v q i) (V' i) p)
    (ht : ∀ i l, (A' i l) tdir = (V' i) (ydir l))
    (hs : ∀ i j l, (A' i l) (ydir j) = (A' i j) (ydir l)) :
    fderiv ℝ (fun q => (A q).det) p tdir
      = ∑ j, fderiv ℝ (fun q => ((A q).updateCol j (v q)).det) p (ydir j) := by
  rw [fderiv_det_apply A A' p tdir hA]
  -- the derivative of each column replacement in the `t`-direction
  have hL : ∀ l : Fin d, ((A p).updateCol l (fun i => A' i l tdir)).det
      = ((A p).updateCol l (fun i => (V' i) (ydir l))).det := by
    intro l
    rw [show (fun i => A' i l tdir) = (fun i => (V' i) (ydir l)) from funext fun i => ht i l]
  simp only [hL]
  have hR : ∀ j : Fin d, fderiv ℝ (fun q => ((A q).updateCol j (v q)).det) p (ydir j)
      = ((A p).updateCol j (fun i => (V' i) (ydir j))).det
        + ∑ l ∈ Finset.univ.erase j,
            (((A p).updateCol j (v p)).updateCol l (fun i => (A' i l) (ydir j))).det := by
    intro j
    have hif : ∀ i m : Fin d, HasFDerivAt (fun q => (A q).updateCol j (v q) i m)
        ((if m = j then (V' i) else (A' i m)) : P →L[ℝ] ℝ) p := by
      intro i m
      by_cases hm : m = j
      · have hfun : (fun q => (A q).updateCol j (v q) i m) = fun q => v q i := by
          funext q
          rw [hm, Matrix.updateCol_self]
        rw [if_pos hm, hfun]
        exact hv i
      · have hfun : (fun q => (A q).updateCol j (v q) i m) = fun q => A q i m := by
          funext q
          rw [Matrix.updateCol_ne hm]
        rw [if_neg hm, hfun]
        exact hA i m
    rw [fderiv_det_apply (fun q => (A q).updateCol j (v q))
      (fun i m => (if m = j then (V' i) else (A' i m))) p (ydir j) hif]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
    congr 1
    · rw [updateCol_updateCol_same]
      rw [show (fun i => (if j = j then (V' i) else (A' i j)) (ydir j)) = (fun i => (V' i) (ydir j))
        from by funext i; rw [if_pos rfl]]
    · refine Finset.sum_congr rfl fun l hl => ?_
      have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
      rw [show (fun i => (if l = j then (V' i) else (A' i l)) (ydir j)) = (fun i => (A' i l) (ydir j))
        from by funext i; rw [if_neg hlj]]
  rw [Finset.sum_congr rfl (fun j _ => hR j)]
  rw [Finset.sum_add_distrib]
  have hsame : ∀ j : Fin d, ((A p).updateCol j (fun i => (V' i) (ydir j))).det
      = ((A p).updateCol j (fun i => A' i j tdir)).det := by
    intro j
    rw [show (fun i => (V' i) (ydir j)) = (fun i => A' i j tdir) from funext fun i => (ht i j).symm]
  rw [Finset.sum_congr rfl (fun j _ => hsame j)]
  have hcancel : (∑ x : Fin d, ∑ l ∈ Finset.univ.erase x,
      (((A p).updateCol x (v p)).updateCol l (fun i => (A' i l) (ydir x))).det) = 0 :=
    sum_offDiag_antisymm_eq_zero
      (fun x l => (((A p).updateCol x (v p)).updateCol l (fun i => (A' i l) (ydir x))).det)
      (by
        intro x l hxl
        rw [det_updateCol_swap (A p) hxl (v p) (fun i => (A' i l) (ydir x))]
        rw [show (fun i => (A' i x) (ydir l)) = (fun i => (A' i l) (ydir x)) from
          funext fun i => (hs i x l).symm]
        ring)
  rw [hcancel, add_zero]

open scoped Matrix
open MeasureTheory Filter
open scoped Topology

/-! ## The divergence identity on a Euclidean space -/

/-- The divergence of a vector field on `EuclideanSpace ℝ (Fin N)` in the standard orthonormal
basis. -/
noncomputable def divE {N : ℕ} (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (y : EuclideanSpace ℝ (Fin N)) : ℝ :=
  ∑ i : Fin N, (fderiv ℝ V y (EuclideanSpace.single i 1)) i

/-- The coordinate isometry `EuclideanSpace ℝ (Fin N) ≃L[ℝ] (Fin N → ℝ)`. -/
noncomputable def coordE (N : ℕ) : EuclideanSpace ℝ (Fin N) ≃L[ℝ] (Fin N → ℝ) :=
  EuclideanSpace.equiv (Fin N) ℝ

lemma coordE_symm_apply {N : ℕ} (z : Fin N → ℝ) :
    (coordE N).symm z = WithLp.toLp 2 z := rfl

lemma coordE_apply_apply {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    (coordE N) x i = x i := rfl

/-- **The divergence identity for compactly supported fields on `EuclideanSpace ℝ (Fin N)`.**
Mathlib's box divergence identity, transported along the coordinate isometry and extended to the
whole space by compact support. -/
theorem integral_divergence_eq_zero {N : ℕ}
    (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (s : Set (EuclideanSpace ℝ (Fin N))) (hs : s.Countable)
    (hVc : Continuous V) (hVsupp : HasCompactSupport V)
    (hVd : ∀ x, x ∉ s → HasFDerivAt V (fderiv ℝ V x) x)
    (hInt : MeasureTheory.Integrable (fun x => divE V x)) :
    ∫ x, divE V x = 0 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [divE]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  set W : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
    fun z => coordE (n + 1) (V ((coordE (n + 1)).symm z)) with hW
  have hWcont : Continuous W :=
    (coordE (n + 1)).continuous.comp (hVc.comp (coordE (n + 1)).symm.continuous)
  have hsupp : ∀ z : Fin (n + 1) → ℝ, z ∉ tsupport W → W z = 0 :=
    fun z hz => Function.notMem_support.mp fun h => hz (subset_tsupport _ h)
  -- the support is bounded in the coordinate (sup) norm
  obtain ⟨R₀, hR₀⟩ : ∃ R, coordE (n + 1) '' tsupport V ⊆ Metric.closedBall (0 : Fin (n + 1) → ℝ) R :=
    (hVsupp.isCompact.image (coordE (n + 1)).continuous).isBounded.subset_closedBall 0
  obtain ⟨R, hR⟩ : ∃ R, ∀ z ∈ tsupport W, ‖z‖ ≤ R := by
    refine ⟨R₀, fun z hz => ?_⟩
    have hz' : z ∈ coordE (n + 1) '' tsupport V := by
      have h1 : z ∈ closure (Function.support W) := hz
      refine closure_minimal ?_ (hVsupp.isCompact.image (coordE (n + 1)).continuous).isClosed h1
      intro z hz0
      refine ⟨(coordE (n + 1)).symm z, subset_tsupport V ?_, by simp⟩
      rw [Function.mem_support] at hz0 ⊢
      intro hV
      exact hz0 (by simp [hW, hV])
    simpa [Metric.mem_closedBall, dist_eq_norm] using hR₀ hz'
  set c : ℝ := max (max R R₀) 0 + 1 with hc
  have hcR : R < c := by rw [hc]; linarith [le_trans (le_max_left R R₀) (le_max_left (max R R₀) 0)]
  have hcR₀ : R₀ < c := by
    rw [hc]; linarith [le_trans (le_max_right R R₀) (le_max_left (max R R₀) 0)]
  have hcpos : 0 < c := by rw [hc]; linarith [le_max_right (max R R₀) 0]
  set a : Fin (n + 1) → ℝ := fun _ => -c with ha
  set b : Fin (n + 1) → ℝ := fun _ => c with hb
  have hle : a ≤ b := by intro i; simp only [ha, hb]; linarith [hcpos.le]
  set s' : Set (Fin (n + 1) → ℝ) := (coordE (n + 1)) '' s with hs'
  have hs'c : s'.Countable := hs'.symm ▸ hs.image _
  -- chain rule for the conjugate field
  have hchain : ∀ z : Fin (n + 1) → ℝ, (coordE (n + 1)).symm z ∉ s → HasFDerivAt W
      (((coordE (n + 1) : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] (Fin (n + 1) → ℝ))).comp
        ((fderiv ℝ V ((coordE (n + 1)).symm z)).comp
          (((coordE (n + 1)).symm : (Fin (n + 1) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))))) z := by
    intro z hz
    have h0 : HasFDerivAt V (fderiv ℝ V ((coordE (n + 1)).symm z)) ((coordE (n + 1)).symm z) :=
      hVd _ hz
    have h1 : HasFDerivAt (fun u : Fin (n + 1) → ℝ => V ((coordE (n + 1)).symm u))
        ((fderiv ℝ V ((coordE (n + 1)).symm z)).comp
          (((coordE (n + 1)).symm : (Fin (n + 1) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))))) z :=
      h0.comp z ((coordE (n + 1)).symm.hasFDerivAt (x := z))
    exact (coordE (n + 1)).hasFDerivAt.comp (x := z) h1
  have hsingle : ∀ i : Fin (n + 1), ((coordE (n + 1)).symm (Pi.single i 1) : EuclideanSpace ℝ (Fin (n + 1)))
      = EuclideanSpace.single i 1 := fun i => rfl
  -- the conjugated divergence is the coordinate trace
  have hsum : ∀ z : Fin (n + 1) → ℝ, (coordE (n + 1)).symm z ∉ s →
      (∑ i : Fin (n + 1), (fderiv ℝ W z (Pi.single i 1)) i)
        = divE V ((coordE (n + 1)).symm z) := by
    intro z hz
    have hpt : ∀ i : Fin (n + 1), (fderiv ℝ W z (Pi.single i 1)) i
        = (fderiv ℝ V ((coordE (n + 1)).symm z) (EuclideanSpace.single i 1)) i := by
      intro i
      rw [(hchain z hz).fderiv]
      simp only [ContinuousLinearMap.comp_apply]
      rfl
    exact Finset.sum_congr rfl fun i _ => hpt i
  -- off the box the field vanishes
  have hoffbox : ∀ z : Fin (n + 1) → ℝ, z ∉ Set.Icc a b → divE V ((coordE (n + 1)).symm z) = 0 := by
    intro z hz
    have hz1 : ¬ (a ≤ z ∧ z ≤ b) := by simpa [Set.mem_Icc] using hz
    rw [Pi.le_def, Pi.le_def, not_and_or] at hz1
    have hc_lt : c < ‖z‖ := by
      rcases hz1 with h1 | h1
      · obtain ⟨i, hi⟩ := not_forall.mp h1
        rw [not_le] at hi
        have h2 : z i < -c := by simpa [ha] using hi
        have h3 : c < ‖z i‖ := by
          rw [Real.norm_eq_abs]
          exact lt_abs.mpr (Or.inr (by linarith))
        linarith [norm_le_pi_norm z i]
      · obtain ⟨i, hi⟩ := not_forall.mp h1
        rw [not_le] at hi
        have h2 : c < z i := by simpa [hb] using hi
        have h3 : c < ‖z i‖ := by
          rw [Real.norm_eq_abs]
          exact lt_abs.mpr (Or.inl h2)
        linarith [norm_le_pi_norm z i]
    have hnotV : (coordE (n + 1)).symm z ∉ tsupport V := by
      intro hmem
      have h2 : z ∈ coordE (n + 1) '' tsupport V := ⟨(coordE (n + 1)).symm z, hmem, by simp⟩
      have h3 : ‖z‖ ≤ R₀ := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hR₀ h2
      linarith
    have hloc : V =ᶠ[𝓝 ((coordE (n + 1)).symm z)] 0 := by
      filter_upwards [(isClosed_tsupport V).isOpen_compl.mem_nhds hnotV] with u hu
      exact Function.notMem_support.mp fun h => hu (subset_tsupport V h)
    have hf : fderiv ℝ V ((coordE (n + 1)).symm z) = 0 := by rw [hloc.fderiv_eq]; simp
    simp only [divE, hf, ContinuousLinearMap.zero_apply, WithLp.ofLp_zero, Pi.zero_apply,
      Finset.sum_const_zero]
  have Hd : ∀ z ∈ (Set.pi Set.univ fun i => Set.Ioo (a i) (b i)) \ s',
      HasFDerivAt W (fderiv ℝ W z) z := by
    rintro z ⟨-, hzs⟩
    have hzS : (coordE (n + 1)).symm z ∉ s := by
      intro hmem
      exact hzs (by rw [hs']; exact ⟨(coordE (n + 1)).symm z, hmem, by simp⟩)
    exact (hchain z hzS).fderiv ▸ hchain z hzS
  have hmp : MeasureTheory.MeasurePreserving (⇑(MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)))
      volume volume := by
    simpa [MeasurableEquiv.coe_toLp] using PiLp.volume_preserving_toLp (Fin (n + 1))
  have hemb : MeasurableEmbedding (⇑(MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ))) :=
    (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).measurableEmbedding
  have hint' : MeasureTheory.Integrable
      (fun z : Fin (n + 1) → ℝ => divE V ((coordE (n + 1)).symm z)) := by
    have h2 := (hmp.integrable_comp_emb hemb).mpr hInt
    simpa only [MeasurableEquiv.coe_toLp, coordE_symm_apply, Function.comp_def] using h2
  have haeeq : (fun z : Fin (n + 1) → ℝ => ∑ i, (fderiv ℝ W z (Pi.single i 1)) i)
      =ᵐ[volume.restrict (Set.Icc a b)]
        (fun z => divE V ((coordE (n + 1)).symm z)) := by
    filter_upwards [hs'c.ae_notMem (volume.restrict (Set.Icc a b))] with z hz
    exact hsum z (fun hmem => hz ⟨(coordE (n + 1)).symm z, hmem, by simp⟩)
  have Hi : MeasureTheory.IntegrableOn
      (fun z : Fin (n + 1) → ℝ => ∑ i, (fderiv ℝ W z (Pi.single i 1)) i) (Set.Icc a b) :=
    hint'.integrableOn.congr haeeq.symm
  have key : (∫ z in Set.Icc a b, ∑ i, (fderiv ℝ W z (Pi.single i 1)) i) = 0 := by
    have hmain := MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable
      (n := n) a b hle W (fun z => fderiv ℝ W z) s' hs'c hWcont.continuousOn Hd Hi
    rw [hmain]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hzero : ∀ x : Fin n → ℝ,
        W (Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i (b i) x) i = 0 := by
      intro x
      have hqi : (Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i (b i) x) i = c :=
        Fin.insertNth_apply_same (α := fun _ : Fin (n + 1) => ℝ) i (b i) x
      have hnorm : c ≤ ‖Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i (b i) x‖ := by
        have h1 := norm_le_pi_norm (Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i (b i) x) i
        rw [hqi, Real.norm_eq_abs, abs_of_pos hcpos] at h1
        exact h1
      have hnot : Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i (b i) x ∉ tsupport W := by
        intro hmem
        have h2 : ‖Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i (b i) x‖ ≤ R := hR _ hmem
        linarith
      rw [hsupp _ hnot]
      rfl
    have hzero' : ∀ x : Fin n → ℝ,
        W (Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i (a i) x) i = 0 := by
      intro x
      have hqi : (Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i (a i) x) i = -c :=
        Fin.insertNth_apply_same (α := fun _ : Fin (n + 1) => ℝ) i (a i) x
      have hnorm : c ≤ ‖Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i (a i) x‖ := by
        have h1 := norm_le_pi_norm (Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i (a i) x) i
        rw [hqi, Real.norm_eq_abs] at h1
        have h4 : c ≤ |(-c : ℝ)| := by rw [abs_neg, abs_of_pos hcpos]
        linarith
      have hnot : Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i (a i) x ∉ tsupport W := by
        intro hmem
        have h2 : ‖Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i (a i) x‖ ≤ R := hR _ hmem
        linarith
      rw [hsupp _ hnot]
      rfl
    simp only [hzero, hzero', MeasureTheory.integral_zero, sub_zero]
  have hbox : (∫ z in Set.Icc a b, divE V ((coordE (n + 1)).symm z)) = 0 := by
    rw [MeasureTheory.integral_congr_ae haeeq.symm, key]
  have htrans : (∫ x : EuclideanSpace ℝ (Fin (n + 1)), divE V x)
      = ∫ z : Fin (n + 1) → ℝ, divE V ((coordE (n + 1)).symm z) := by
    have h := hmp.integral_comp' (f := MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ))
      (fun x : EuclideanSpace ℝ (Fin (n + 1)) => divE V x)
    simpa only [MeasurableEquiv.coe_toLp, coordE_symm_apply] using h.symm
  calc (∫ x : EuclideanSpace ℝ (Fin (n + 1)), divE V x)
      = ∫ z : Fin (n + 1) → ℝ, divE V ((coordE (n + 1)).symm z) := htrans
    _ = ∫ z in Set.Icc a b, divE V ((coordE (n + 1)).symm z) :=
        (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hoffbox).symm
    _ = 0 := hbox

/-! ## The flux identity for a conical family -/

section Conical

variable {d : ℕ}

/-- The `i`-th standard basis vector of `EuclideanSpace ℝ (Fin d)`. -/
noncomputable def stdV (i : Fin d) : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1

/-- The coordinate matrix of the derivative of the slice `y ↦ Φ (t,y)`. -/
noncomputable def jacM (Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (q : ℝ × EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  fun i l => (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => Φ (q.1, z)) q.2 (stdV l)) i

/-- The coordinate velocity `∂_tΦ`. -/
noncomputable def velV (Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (q : ℝ × EuclideanSpace ℝ (Fin d)) : Fin d → ℝ :=
  fun i => (fderiv ℝ Φ q (1, 0)) i

/-- The flux field: the adjugate of the Jacobian applied to the velocity (in coordinates). -/
noncomputable def fluxV (Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (q : ℝ × EuclideanSpace ℝ (Fin d)) : Fin d → ℝ :=
  fun j => ((jacM Φ q).updateCol j (velV Φ q)).det

/-- The flux field as a vector of the Euclidean space. -/
noncomputable def fluxE (Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (q : ℝ × EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (coordE d).symm (fluxV Φ q)

lemma fluxE_apply (Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (q : ℝ × EuclideanSpace ℝ (Fin d)) (j : Fin d) : fluxE Φ q j = fluxV Φ q j := rfl

lemma le_top_add_aux : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp

section Identifications

variable {Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}

lemma contDiffAt_uncurried
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    {p : ℝ × EuclideanSpace ℝ (Fin d)} (hp : p.2 ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ p :=
  hsm.contDiffAt ((isOpen_compl_singleton.preimage continuous_snd).mem_nhds (by simpa using hp))

/-- The derivative of a vertical slice is the restriction of the full derivative. -/
lemma fderiv_slice_eq {p : ℝ × EuclideanSpace ℝ (Fin d)} (hd : DifferentiableAt ℝ Φ p) :
    fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => Φ (p.1, z)) p.2
      = (fderiv ℝ Φ p).comp (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin d))) := by
  have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) => (p.1, z))
      (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin d))) p.2 :=
    (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id p.2)
  exact (hd.hasFDerivAt.comp p.2 h1).fderiv

/-- A coordinate of the slice derivative. -/
lemma jacM_eq_partial {p : ℝ × EuclideanSpace ℝ (Fin d)} (hd : DifferentiableAt ℝ Φ p)
    (i l : Fin d) :
    jacM Φ p i l = (fderiv ℝ (fun q' : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q') i) p) (0, stdV l) := by
  rw [jacM, fderiv_slice_eq (Φ := Φ) hd]
  have hproj : HasFDerivAt (fun q' : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q') i)
      ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).comp (fderiv ℝ Φ p)) p :=
    ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).hasFDerivAt).comp p hd.hasFDerivAt
  rw [hproj.fderiv]
  rfl

/-- A coordinate of the velocity. -/
lemma velV_eq_partial {p : ℝ × EuclideanSpace ℝ (Fin d)} (hd : DifferentiableAt ℝ Φ p)
    (i : Fin d) :
    velV Φ p i = (fderiv ℝ (fun q' : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q') i) p) (1, 0) := by
  rw [velV]
  have hproj : HasFDerivAt (fun q' : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q') i)
      ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).comp (fderiv ℝ Φ p)) p :=
    ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).hasFDerivAt).comp p hd.hasFDerivAt
  rw [hproj.fderiv]
  rfl

/-- The derivative of `q ↦ f q v`. -/
lemma fderiv_apply_eq {f : ℝ × EuclideanSpace ℝ (Fin d) → ((ℝ × EuclideanSpace ℝ (Fin d)) →L[ℝ] ℝ)}
    {p : ℝ × EuclideanSpace ℝ (Fin d)} (hf : DifferentiableAt ℝ f p) (v : ℝ × EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun q => f q v) p
      = (ContinuousLinearMap.apply ℝ ℝ v) ∘L (fderiv ℝ f p) := by
  have h := ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt).comp p hf.hasFDerivAt
  simpa [ContinuousLinearMap.comp_apply, Function.comp_def] using h.fderiv

/-- Differentiability of the coordinate of the Jacobian. -/
lemma differentiableAt_jacM_entry
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    {p : ℝ × EuclideanSpace ℝ (Fin d)} (hp : p.2 ≠ 0) (i l : Fin d) :
    DifferentiableAt ℝ (fun q => jacM Φ q i l) p := by
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hΨ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q) i) p :=
    ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff.contDiffAt).comp p
      (contDiffAt_uncurried (Φ := Φ) hsm hp)
  have hf : DifferentiableAt ℝ (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q) i)) p :=
    (hΨ.fderiv_right le_top_add_aux).differentiableAt htop
  have hcomp : DifferentiableAt ℝ (fun q =>
      (fderiv ℝ (fun q' : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q') i) q) (0, stdV l)) p := by
    have h := (ContinuousLinearMap.apply ℝ ℝ (0, stdV l)).differentiableAt.comp p hf
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using h
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_compl_singleton.preimage continuous_snd).mem_nhds (by simpa using hp)]
    with q hq
  exact jacM_eq_partial (Φ := Φ)
    ((contDiffAt_uncurried (Φ := Φ) hsm hq).differentiableAt htop) i l

end Identifications

end Conical

/-! ## The geometry of a conical norm-preserving family -/

section Geometry

variable {d : ℕ}
variable {Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}

/-- **Euler's identity** for a family which is `1`-homogeneous in the second variable. -/
lemma cone_euler (hcone : ∀ (t r : ℝ) (y : EuclideanSpace ℝ (Fin d)), 0 < r → Φ (t, r • y) = r • Φ (t, y))
    (t : ℝ) (y : EuclideanSpace ℝ (Fin d))
    (hd : DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin d) => Φ (t, z)) y) :
    (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => Φ (t, z)) y) y = Φ (t, y) := by
  have hγ : HasDerivAt (fun r : ℝ => Φ (t, r • y))
      ((fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => Φ (t, z)) y) y) 1 := by
    have h1 : HasDerivAt (fun r : ℝ => r • y) y 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const y
    have h2 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) => Φ (t, z))
        (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => Φ (t, z)) y) ((1 : ℝ) • y) := by
      simpa using hd.hasFDerivAt
    exact h2.comp_hasDerivAt 1 h1
  have h2 : HasDerivWithinAt (fun r : ℝ => r • Φ (t, y)) (Φ (t, y)) (Set.Ioi 0) 1 := by
    have h : HasDerivAt (fun r : ℝ => r • Φ (t, y)) (Φ (t, y)) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const (Φ (t, y))
    exact h.hasDerivWithinAt
  have h3 : HasDerivWithinAt (fun r : ℝ => Φ (t, r • y)) (Φ (t, y)) (Set.Ioi 0) 1 := by
    refine h2.congr_of_eventuallyEq_of_mem ?_ (by norm_num)
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hcone t r y hr
  exact hγ.unique (h3.hasDerivAt (isOpen_Ioi.mem_nhds (by norm_num)))

/-- **The norm identity** for a norm-preserving family: the adjoint of the derivative sends the
value to the argument. -/
lemma cone_adjoint (hnorm : ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin d)), ‖Φ (t, y)‖ = ‖y‖)
    (t : ℝ) (y : EuclideanSpace ℝ (Fin d))
    (hd : DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin d) => Φ (t, z)) y)
    (δ : EuclideanSpace ℝ (Fin d)) :
    inner ℝ ((fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => Φ (t, z)) y) δ) (Φ (t, y))
      = inner ℝ δ y := by
  have hγ0 : HasDerivAt (fun r : ℝ => ‖Φ (t, y + r • δ)‖ ^ 2 - ‖y + r • δ‖ ^ 2) 0 0 := by
    have heq : (fun r : ℝ => ‖Φ (t, y + r • δ)‖ ^ 2 - ‖y + r • δ‖ ^ 2) = fun _ => (0 : ℝ) := by
      funext r; rw [hnorm, sub_self]
    rw [heq]; exact hasDerivAt_const (𝕜 := ℝ) (c := (0 : ℝ)) (x := 0)
  have h1 : HasDerivAt (fun r : ℝ => y + r • δ) δ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add y
  have h2 : HasDerivAt (fun r : ℝ => Φ (t, y + r • δ))
      ((fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => Φ (t, z)) y) δ) 0 := by
    have hf : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) => Φ (t, z))
        (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => Φ (t, z)) y) (y + (0 : ℝ) • δ) := by
      simpa using hd.hasFDerivAt
    simpa [Function.comp_def] using hf.comp_hasDerivAt 0 h1
  have hA := h2.norm_sq
  have hB := h1.norm_sq
  have hsub := hA.sub hB
  have hzero := hγ0.unique hsub
  have hkey : (2 : ℝ) * inner ℝ (Φ (t, y)) ((fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => Φ (t, z)) y) δ)
      = (2 : ℝ) * inner ℝ (y + (0 : ℝ) • δ) δ := by
    simpa [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul] using (sub_eq_zero.mp hzero.symm)
  rw [zero_smul, add_zero] at hkey
  have hmain := mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hkey
  rw [(real_inner_comm (Φ (t, y)) ((fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => Φ (t, z)) y) δ)).symm,
    (real_inner_comm y δ).symm] at hmain
  exact hmain

/-- **The velocity is orthogonal to the value** for a norm-preserving family. -/
lemma cone_vel_orth (hnorm : ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin d)), ‖Φ (t, y)‖ = ‖y‖)
    (t : ℝ) (y : EuclideanSpace ℝ (Fin d))
    (hd : DifferentiableAt ℝ Φ (t, y))
    (hd2 : HasDerivAt (fun τ : ℝ => Φ (τ, y)) ((fderiv ℝ Φ (t, y)) (1, 0)) t) :
    inner ℝ ((fderiv ℝ Φ (t, y)) (1, 0)) (Φ (t, y)) = 0 := by
  have hγ : HasDerivAt (fun τ : ℝ => ‖Φ (τ, y)‖ ^ 2 - ‖y‖ ^ 2) 0 t := by
    have heq : (fun τ : ℝ => ‖Φ (τ, y)‖ ^ 2 - ‖y‖ ^ 2) = fun _ => (0 : ℝ) := by
      funext τ; rw [hnorm, sub_self]
    rw [heq]; exact hasDerivAt_const (𝕜 := ℝ) (c := (0 : ℝ)) (x := t)
  have h1 := hd2.norm_sq
  have h2 : HasDerivAt (fun _ : ℝ => ‖y‖ ^ 2) 0 t :=
    hasDerivAt_const (𝕜 := ℝ) (c := ‖y‖ ^ 2) (x := t)
  have hsub := h1.sub h2
  have hzero := hγ.unique hsub
  have hkey : (2 : ℝ) * inner ℝ (Φ (t, y)) ((fderiv ℝ Φ (t, y)) (1, 0)) = 0 := by
    simpa [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul] using (sub_eq_zero.mp hzero.symm)
  have h0 : inner ℝ (Φ (t, y)) ((fderiv ℝ Φ (t, y)) (1, 0)) = 0 := by
    have h' : (2 : ℝ) * inner ℝ (Φ (t, y)) ((fderiv ℝ Φ (t, y)) (1, 0)) = (2 : ℝ) * 0 := by
      rw [hkey, mul_zero]
    exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) h'
  rwa [(real_inner_comm (Φ (t, y)) ((fderiv ℝ Φ (t, y)) (1, 0))).symm] at h0

end Geometry

/-! ## The flux identity for a conical family, and the tangency -/

section FluxIdentity

variable {d : ℕ}
variable {Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}

lemma differentiableAt_velV_entry
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    {p : ℝ × EuclideanSpace ℝ (Fin d)} (hp : p.2 ≠ 0) (i : Fin d) :
    DifferentiableAt ℝ (fun q => velV Φ q i) p := by
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hΨ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q) i) p :=
    ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff.contDiffAt).comp p
      (contDiffAt_uncurried (Φ := Φ) hsm hp)
  have hf : DifferentiableAt ℝ (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q) i)) p :=
    (hΨ.fderiv_right le_top_add_aux).differentiableAt htop
  have hcomp : DifferentiableAt ℝ (fun q =>
      (fderiv ℝ (fun q' : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q') i) q) (1, 0)) p := by
    have h := (ContinuousLinearMap.apply ℝ ℝ (1, 0)).differentiableAt.comp p hf
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using h
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_compl_singleton.preimage continuous_snd).mem_nhds (by simpa using hp)]
    with q hq
  exact velV_eq_partial (Φ := Φ)
    ((contDiffAt_uncurried (Φ := Φ) hsm hq).differentiableAt htop) i

lemma fderiv_jacM_entry_eq
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    {p : ℝ × EuclideanSpace ℝ (Fin d)} (hp : p.2 ≠ 0) (i l : Fin d) :
    fderiv ℝ (fun q => jacM Φ q i l) p
      = (ContinuousLinearMap.apply ℝ ℝ (0, stdV l)) ∘L
        (fderiv ℝ (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q) i)) p) := by
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hf : DifferentiableAt ℝ (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q) i)) p :=
    ((((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff.contDiffAt).comp p
      (contDiffAt_uncurried (Φ := Φ) hsm hp)).fderiv_right le_top_add_aux).differentiableAt htop
  rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (x := p) ?_]
  · exact fderiv_apply_eq hf (0, stdV l)
  · filter_upwards [(isOpen_compl_singleton.preimage continuous_snd).mem_nhds (by simpa using hp)]
      with q hq
    exact jacM_eq_partial (Φ := Φ)
      ((contDiffAt_uncurried (Φ := Φ) hsm hq).differentiableAt htop) i l

lemma fderiv_velV_entry_eq
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    {p : ℝ × EuclideanSpace ℝ (Fin d)} (hp : p.2 ≠ 0) (i : Fin d) :
    fderiv ℝ (fun q => velV Φ q i) p
      = (ContinuousLinearMap.apply ℝ ℝ (1, 0)) ∘L
        (fderiv ℝ (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q) i)) p) := by
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hf : DifferentiableAt ℝ (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q) i)) p :=
    ((((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff.contDiffAt).comp p
      (contDiffAt_uncurried (Φ := Φ) hsm hp)).fderiv_right le_top_add_aux).differentiableAt htop
  rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (x := p) ?_]
  · exact fderiv_apply_eq hf (1, 0)
  · filter_upwards [(isOpen_compl_singleton.preimage continuous_snd).mem_nhds (by simpa using hp)]
      with q hq
    exact velV_eq_partial (Φ := Φ)
      ((contDiffAt_uncurried (Φ := Φ) hsm hq).differentiableAt htop) i

/-- **The flux identity for a conical family.**  The `t`-derivative of the determinant of the
Jacobian is the divergence of the flux field. -/
theorem flux_identity_conical
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    {p : ℝ × EuclideanSpace ℝ (Fin d)} (hp : p.2 ≠ 0) :
    fderiv ℝ (fun q => (jacM Φ q).det) p (1, 0)
      = ∑ j, fderiv ℝ (fun q => ((jacM Φ q).updateCol j (velV Φ q)).det) p (0, stdV j) := by
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hΨ : ∀ i : Fin d, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q) i) p := fun i =>
    ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff.contDiffAt).comp p
      (contDiffAt_uncurried (Φ := Φ) hsm hp)
  have hsym : ∀ i : Fin d, IsSymmSndFDerivAt ℝ
      (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q) i) p := fun i =>
    (hΨ i).isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)
  refine fderiv_flux_identity (fun q => jacM Φ q) (fun q => velV Φ q)
    (fun i l => fderiv ℝ (fun q => jacM Φ q i l) p)
    (fun i => fderiv ℝ (fun q => velV Φ q i) p) (1, 0) (fun j => (0, stdV j)) p ?_ ?_ ?_ ?_
  · intro i l
    exact (differentiableAt_jacM_entry hsm hp i l).hasFDerivAt
  · intro i
    exact (differentiableAt_velV_entry hsm hp i).hasFDerivAt
  · intro i l
    rw [fderiv_jacM_entry_eq hsm hp i l, fderiv_velV_entry_eq hsm hp i]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    exact (hsym i).eq (1, 0) (0, stdV l)
  · intro i j l
    rw [fderiv_jacM_entry_eq hsm hp i l, fderiv_jacM_entry_eq hsm hp i j]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    exact (hsym i).eq (0, stdV j) (0, stdV l)

end FluxIdentity

/-! ## The tangency of the flux field -/

section Tangency

variable {d : ℕ}

/-- The inner product of `EuclideanSpace ℝ (Fin d)` in coordinates. -/
lemma inner_eq_sum_coords (x y : EuclideanSpace ℝ (Fin d)) :
    inner ℝ x y = ∑ i : Fin d, (y : Fin d → ℝ) i * (x : Fin d → ℝ) i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct]

/-- The matrix–vector pairing identity `∑ j (M v)_j w_j = ∑ i v_i (Mᵀ w)_i`. -/
lemma sum_mulVec_mul (M : Matrix (Fin d) (Fin d) ℝ) (v w : Fin d → ℝ) :
    ∑ j, (M *ᵥ v) j * w j = ∑ i, v i * (Mᵀ *ᵥ w) i := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The expansion of a vector in the standard basis. -/
lemma basis_expansion (y : EuclideanSpace ℝ (Fin d)) :
    y = ∑ l, (y : Fin d → ℝ) l • (EuclideanSpace.single l 1 : EuclideanSpace ℝ (Fin d)) := by
  refine PiLp.ext fun j => ?_
  simp only [Finset.sum_apply, Pi.smul_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro x _ hx
    rw [if_neg (fun h : j = x => hx h.symm), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- A linear map is determined on the sum expansion. -/
lemma map_basis_expansion (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (y : EuclideanSpace ℝ (Fin d)) :
    L y = ∑ l, (y : Fin d → ℝ) l • L (EuclideanSpace.single l 1 : EuclideanSpace ℝ (Fin d)) := by
  conv_lhs => rw [basis_expansion y]
  rw [map_sum]
  simp

/-- The transpose of the adjugate applied to `Aᵀ y` is `det A • y`. -/
lemma adjugate_transpose_mulVec (A : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) :
    A.adjugateᵀ *ᵥ (Aᵀ *ᵥ y) = A.det • y := by
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.mul_adjugate, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- The determinant with a replaced column is the corresponding entry of the adjugate. -/
lemma det_updateCol_eq_adjugate_mulVec (M : Matrix (Fin d) (Fin d) ℝ) (z : Fin d → ℝ)
    (j : Fin d) : (M.updateCol j z).det = (M.adjugate *ᵥ z) j := by
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]

/-- **The flux field is tangential.**  For a conical norm-preserving family, the flux field
`adj(D_yΦ_t)·∂_tΦ_t` is orthogonal to `y`. -/
theorem fluxV_tangent {Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    (hcone : ∀ (t r : ℝ) (y : EuclideanSpace ℝ (Fin d)), 0 < r → Φ (t, r • y) = r • Φ (t, y))
    (hnorm : ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin d)), ‖Φ (t, y)‖ = ‖y‖)
    {p : ℝ × EuclideanSpace ℝ (Fin d)} (hp : p.2 ≠ 0) :
    ∑ j, fluxV Φ p j * (p.2 : Fin d → ℝ) j = 0 := by
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hd : DifferentiableAt ℝ Φ p := (contDiffAt_uncurried hsm hp).differentiableAt htop
  have hsl : DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin d) => Φ (p.1, z)) p.2 := by
    have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) => (p.1, z))
        (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin d))) p.2 :=
      (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id p.2)
    exact (hd.hasFDerivAt.comp p.2 h1).differentiableAt
  -- (a) Euler, in coordinates
  have ha : (jacM Φ p) *ᵥ (fun l => (p.2 : Fin d → ℝ) l) = fun i => (Φ p : Fin d → ℝ) i := by
    have hL : (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => Φ (p.1, z)) p.2) p.2 = Φ p :=
      cone_euler hcone p.1 p.2 hsl
    have hsum := congrArg (fun v : EuclideanSpace ℝ (Fin d) => (v : Fin d → ℝ))
      (map_basis_expansion (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => Φ (p.1, z)) p.2) p.2)
    funext i
    have hgoal : (∑ l, ((((fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => Φ (p.1, z)) p.2)
            (EuclideanSpace.single l 1) : EuclideanSpace ℝ (Fin d)) : Fin d → ℝ) i)
        * (p.2 : Fin d → ℝ) l)
        = (Φ p : Fin d → ℝ) i := by
      have h2 := congrFun hsum i
      rw [hL] at h2
      rw [h2]
      simp only [Finset.sum_apply, Pi.smul_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, smul_eq_mul]
      exact Finset.sum_congr rfl fun l _ => by ring
    simpa [jacM, Matrix.mulVec, dotProduct, stdV] using hgoal
  -- (b) the adjoint identity, in coordinates
  have hb : (jacM Φ p)ᵀ *ᵥ (fun i => (Φ p : Fin d → ℝ) i) = fun l => (p.2 : Fin d → ℝ) l := by
    funext l
    have h := cone_adjoint hnorm p.1 p.2 hsl (stdV l)
    rw [inner_eq_sum_coords, inner_eq_sum_coords] at h
    have hR : (∑ i : Fin d,
        (p.2 : Fin d → ℝ) i * ((stdV l : EuclideanSpace ℝ (Fin d)) : Fin d → ℝ) i)
        = (p.2 : Fin d → ℝ) l := by
      rw [Finset.sum_eq_single l]
      · simp [stdV, PiLp.single_apply]
      · intro i _ hi
        simp [stdV, PiLp.single_apply, hi]
      · intro hh
        exact absurd (Finset.mem_univ l) hh
    rw [hR] at h
    have hgoal : (∑ i : Fin d, (jacM Φ p) i l * (Φ p : Fin d → ℝ) i)
        = (p.2 : Fin d → ℝ) l := by
      rw [← h]
      exact Finset.sum_congr rfl fun i _ => by simp only [jacM, stdV]; ring
    simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply] using hgoal
  -- (c) the velocity is orthogonal to the value
  have hc : ∑ i, velV Φ p i * (Φ p : Fin d → ℝ) i = 0 := by
    have h2 : HasDerivAt (fun τ : ℝ => (τ, p.2)) (1, (0 : EuclideanSpace ℝ (Fin d))) p.1 := by
      have h := ((hasFDerivAt_id (𝕜 := ℝ) p.1).prodMk
        (hasFDerivAt_const (𝕜 := ℝ) p.2 p.1)).hasDerivAt
      simpa using h
    have h3 : HasDerivAt (fun τ : ℝ => Φ (τ, p.2)) ((fderiv ℝ Φ p) (1, 0)) p.1 := by
      have h4 := hd.hasFDerivAt.comp_hasDerivAt p.1 h2
      simpa [Function.comp_def] using h4
    have h := cone_vel_orth hnorm p.1 p.2 hd h3
    rw [inner_eq_sum_coords] at h
    rw [show (∑ i, velV Φ p i * (Φ p : Fin d → ℝ) i)
        = ∑ i, (Φ p : Fin d → ℝ) i * velV Φ p i from
      Finset.sum_congr rfl fun i _ => mul_comm _ _]
    simpa [velV] using h
  have hflux : ∀ j, fluxV Φ p j = ((jacM Φ p).adjugate *ᵥ (velV Φ p)) j := by
    intro j
    simp only [fluxV]
    rw [det_updateCol_eq_adjugate_mulVec]
  calc ∑ j, fluxV Φ p j * (p.2 : Fin d → ℝ) j
      = ∑ j, ((jacM Φ p).adjugate *ᵥ (velV Φ p)) j * (p.2 : Fin d → ℝ) j :=
        Finset.sum_congr rfl fun j _ => by rw [hflux j]
    _ = ∑ i, (velV Φ p) i * ((jacM Φ p).adjugateᵀ *ᵥ (fun l => (p.2 : Fin d → ℝ) l)) i :=
        sum_mulVec_mul _ _ _
    _ = ∑ i, (velV Φ p) i * ((jacM Φ p).adjugateᵀ
          *ᵥ ((jacM Φ p)ᵀ *ᵥ (fun i => (Φ p : Fin d → ℝ) i))) i := by rw [← hb]
    _ = ∑ i, (velV Φ p) i * ((jacM Φ p).det • (fun i => (Φ p : Fin d → ℝ) i)) i := by
        rw [adjugate_transpose_mulVec]
    _ = (jacM Φ p).det * ∑ i, (velV Φ p) i * (Φ p : Fin d → ℝ) i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply]; ring
    _ = 0 := by rw [hc, mul_zero]

end Tangency

/-! ## The radially cut off flux field and its divergence -/

section Cutoff

variable {d : ℕ}

/-- The annular cutoff: nonnegative, equal to `1` on `3/4 ≤ ‖y‖² ≤ 1`, and vanishing outside
`1/4 ≤ ‖y‖² ≤ 2`. -/
noncomputable def chi (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.smoothTransition (2 - ‖y‖ ^ 2) * Real.smoothTransition (2 * ‖y‖ ^ 2 - 1 / 2)

/-- The smooth profile of the cutoff as a function of `‖y‖²`. -/
noncomputable def chiProf (s : ℝ) : ℝ :=
  Real.smoothTransition (2 - s) * Real.smoothTransition (2 * s - 1 / 2)

lemma chi_eq_prof (y : EuclideanSpace ℝ (Fin d)) : chi y = chiProf (‖y‖ ^ 2) := rfl

lemma chi_eq_prof_fun : (chi : EuclideanSpace ℝ (Fin d) → ℝ) = fun y => chiProf (‖y‖ ^ 2) := rfl

lemma chiProf_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chiProf : ℝ → ℝ) := by
  unfold chiProf
  exact (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)).mul
    (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const))

lemma contDiff_chi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chi : EuclideanSpace ℝ (Fin d) → ℝ) :=
  chiProf_contDiff.comp (contDiff_norm_sq ℝ)

lemma chi_nonneg (y : EuclideanSpace ℝ (Fin d)) : 0 ≤ chi y :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma chi_eq_zero_of_small {y : EuclideanSpace ℝ (Fin d)} (h : ‖y‖ ^ 2 ≤ 1 / 4) : chi y = 0 := by
  rw [chi_eq_prof]
  unfold chiProf
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2 * ‖y‖ ^ 2 - 1 / 2 ≤ 0), mul_zero]

lemma chi_eq_zero_of_large {y : EuclideanSpace ℝ (Fin d)} (h : 2 ≤ ‖y‖ ^ 2) : chi y = 0 := by
  rw [chi_eq_prof]
  unfold chiProf
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2 - ‖y‖ ^ 2 ≤ 0), zero_mul]

lemma chi_eq_one {y : EuclideanSpace ℝ (Fin d)} (h1 : 3 / 4 ≤ ‖y‖ ^ 2) (h2 : ‖y‖ ^ 2 ≤ 1) :
    chi y = 1 := by
  rw [chi_eq_prof]
  unfold chiProf
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 - ‖y‖ ^ 2),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 * ‖y‖ ^ 2 - 1 / 2), mul_one]

lemma chi_pos_of_mem {y : EuclideanSpace ℝ (Fin d)} (h1 : 1 / 4 < ‖y‖ ^ 2) (h2 : ‖y‖ ^ 2 < 2) :
    0 < chi y := by
  rw [chi_eq_prof]
  unfold chiProf
  exact mul_pos (Real.smoothTransition.pos_of_pos (by linarith))
    (Real.smoothTransition.pos_of_pos (by linarith))

/-- The derivative of the cutoff: it is a scalar multiple of `y`. -/
lemma hasFDerivAt_chi (y : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (chi : EuclideanSpace ℝ (Fin d) → ℝ)
      ((deriv chiProf (‖y‖ ^ 2)) • (2 • innerSL ℝ y)) y := by
  have hf : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖ ^ 2) (2 • innerSL ℝ y) y := by
    have h := (contDiff_norm_sq ℝ (E := EuclideanSpace ℝ (Fin d))).differentiable
      (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
    have h2 : fderiv ℝ (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 2) y = 2 • innerSL ℝ y := by
      rw [fderiv_norm_sq (F := EuclideanSpace ℝ (Fin d))]
      rfl
    exact (h.differentiableAt.hasFDerivAt).congr_fderiv h2
  have hpsi : HasDerivAt (chiProf : ℝ → ℝ) (deriv chiProf (‖y‖ ^ 2)) (‖y‖ ^ 2) :=
    (chiProf_contDiff.differentiable (by simp)).differentiableAt.hasDerivAt
  simpa [chi_eq_prof_fun, Function.comp_def] using hpsi.comp_hasFDerivAt y hf

/-- The cutoff is nonnegative, vanishes off an annulus, and is positive there. -/
lemma chi_support_subset :
    Function.support (chi : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ {y | 1 / 4 < ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 < 2} := by
  intro y hy
  rw [Function.mem_support] at hy
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hy (chi_eq_zero_of_small (not_lt.mp h))
  · by_contra h
    exact hy (chi_eq_zero_of_large (not_lt.mp h))

lemma chi_hasCompactSupport : HasCompactSupport (chi : EuclideanSpace ℝ (Fin d) → ℝ) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Metric.closedBall 0 (Real.sqrt 2)) (isCompact_closedBall _ _) fun y hy => ?_
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have h := (chi_support_subset hy).2
  calc ‖y‖ = Real.sqrt (‖y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg y)).symm
    _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt h.le

lemma chi_zero_near_zero : ∀ᶠ y : EuclideanSpace ℝ (Fin d) in 𝓝 0, chi y = 0 := by
  refine Filter.mem_of_superset (Metric.ball_mem_nhds 0 (by norm_num : (0:ℝ) < 1/2)) ?_
  intro y hy
  refine chi_eq_zero_of_small ?_
  have h : ‖y‖ < 1 / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hy
  nlinarith [norm_nonneg y]

end Cutoff

section CutoffField

variable {d : ℕ}

/-- The flux field at a fixed time, as a vector field. -/
noncomputable def fluxT (Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (t : ℝ) (y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) := fluxE Φ (t, y)

lemma fluxT_apply (Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (t : ℝ) (y : EuclideanSpace ℝ (Fin d)) : fluxT Φ t y = fluxE Φ (t, y) := rfl

/-- The cut-off flux field. -/
noncomputable def cutoffField (Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (t : ℝ) (y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) := chi y • fluxT Φ t y

lemma cutoffField_apply (Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (t : ℝ) (y : EuclideanSpace ℝ (Fin d)) : cutoffField Φ t y = chi y • fluxT Φ t y := rfl

/-- The coordinate of the flux field is `fluxV`. -/
lemma fluxT_coord (Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (t : ℝ) (y : EuclideanSpace ℝ (Fin d)) (j : Fin d) : (fluxT Φ t y : Fin d → ℝ) j = fluxV Φ (t, y) j :=
  rfl

end CutoffField

/-! ## Smoothness of the conical Jacobian data -/

section Smoothness

variable {d : ℕ}

/-- A finite product of smooth functions is smooth. -/
lemma contDiffAt_finset_prod {ι : Type*} [Fintype ι] {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] (f : ι → P → ℝ) (p : P) {n : WithTop ℕ∞}
    (h : ∀ i, ContDiffAt ℝ n (f i) p) :
    ContDiffAt ℝ n (fun q => ∏ i, f i q) p := by
  classical
  have hmain : ∀ s : Finset ι, ContDiffAt ℝ n (fun q => ∏ i ∈ s, f i q) p := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (contDiffAt_const (𝕜 := ℝ) (c := (1 : ℝ)) (x := p))
    | insert a s ha ih =>
        have hfun : (fun q => ∏ i ∈ insert a s, f i q) = fun q => f a q * ∏ i ∈ s, f i q := by
          funext q; rw [Finset.prod_insert ha]
        rw [hfun]
        exact (h a).mul ih
  simpa using hmain Finset.univ

/-- The determinant of a smooth family of matrices is smooth. -/
lemma contDiffAt_det_of_entries {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {A : P → Matrix (Fin d) (Fin d) ℝ} {p : P}
    (hA : ∀ i j, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q => A q i j) p) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q => (A q).det) p := by
  have hfun : (fun q => (A q).det) = fun q => ∑ σ : Equiv.Perm (Fin d),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A q (σ i) i := by
    funext q; rw [Matrix.det_apply']
  rw [hfun]
  refine ContDiffAt.sum fun σ _ => ?_
  exact (contDiffAt_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))).mul
    (contDiffAt_finset_prod (fun i q => A q (σ i) i) p (fun i => hA (σ i) i))

/-- Smoothness of the Jacobian entries of a conical family. -/
lemma contDiffAt_jacM_entry
    {Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    {p : ℝ × EuclideanSpace ℝ (Fin d)} (hp : p.2 ≠ 0) (i l : Fin d) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q => jacM Φ q i l) p := by
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hΨ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q) i) p :=
    ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff.contDiffAt).comp p
      (contDiffAt_uncurried (Φ := Φ) hsm hp)
  have hfd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q) i)) p :=
    hΨ.fderiv_right le_top_add_aux
  have hcomp := (ContinuousLinearMap.apply ℝ ℝ (0, stdV l)).contDiff.contDiffAt.comp p hfd
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_compl_singleton.preimage continuous_snd).mem_nhds (by simpa using hp)]
    with q hq
  exact (jacM_eq_partial (Φ := Φ)
    ((contDiffAt_uncurried (Φ := Φ) hsm hq).differentiableAt htop) i l).trans
    ((ContinuousLinearMap.apply_apply (𝕜 := ℝ) (Fₗ := ℝ) (0, stdV l)
      ((fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q) i)) q)).symm)

/-- Smoothness of the velocity entries of a conical family. -/
lemma contDiffAt_velV_entry
    {Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    {p : ℝ × EuclideanSpace ℝ (Fin d)} (hp : p.2 ≠ 0) (i : Fin d) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q => velV Φ q i) p := by
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hΨ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q) i) p :=
    ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff.contDiffAt).comp p
      (contDiffAt_uncurried (Φ := Φ) hsm hp)
  have hfd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q) i)) p :=
    hΨ.fderiv_right le_top_add_aux
  have hcomp := (ContinuousLinearMap.apply ℝ ℝ (1, 0)).contDiff.contDiffAt.comp p hfd
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_compl_singleton.preimage continuous_snd).mem_nhds (by simpa using hp)]
    with q hq
  exact (velV_eq_partial (Φ := Φ)
    ((contDiffAt_uncurried (Φ := Φ) hsm hq).differentiableAt htop) i).trans
    ((ContinuousLinearMap.apply_apply (𝕜 := ℝ) (Fₗ := ℝ) (1, 0)
      ((fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (Φ q) i)) q)).symm)

/-- Smoothness of the flux field entries of a conical family. -/
lemma contDiffAt_fluxV_entry
    {Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    {p : ℝ × EuclideanSpace ℝ (Fin d)} (hp : p.2 ≠ 0) (j : Fin d) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q => fluxV Φ q j) p := by
  have hentry : ∀ i l : Fin d,
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q => ((jacM Φ q).updateCol j (velV Φ q)) i l) p := by
    intro i l
    by_cases hl : l = j
    · rw [hl]
      have hfun : (fun q => ((jacM Φ q).updateCol j (velV Φ q)) i j) = fun q => velV Φ q i := by
        funext q; rw [Matrix.updateCol_self]
      rw [hfun]
      exact contDiffAt_velV_entry hsm hp i
    · have hfun : (fun q => ((jacM Φ q).updateCol j (velV Φ q)) i l) = fun q => jacM Φ q i l := by
        funext q; rw [Matrix.updateCol_ne hl]
      rw [hfun]
      exact contDiffAt_jacM_entry hsm hp i l
  have := contDiffAt_det_of_entries (A := fun q => (jacM Φ q).updateCol j (velV Φ q)) hentry
  simpa [fluxV] using this

end Smoothness

/-! ## The derivative of the flux field -/

section FluxDeriv

variable {d : ℕ}

/-- The slice conversion for the flux entries (as a linear map). -/
lemma fderiv_fluxV_slice_CLM {Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    {p : ℝ × EuclideanSpace ℝ (Fin d)} (hp : p.2 ≠ 0) (j : Fin d) :
    fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin d) => fluxV Φ (p.1, y') j) p.2
      = (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => fluxV Φ q j) p).comp
          (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin d))) := by
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have h1 : HasFDerivAt (fun y' : EuclideanSpace ℝ (Fin d) => (p.1, y'))
      (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin d))) p.2 :=
    (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have h2 : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin d) => fluxV Φ q j)
      (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => fluxV Φ q j) p) p :=
    ((contDiffAt_fluxV_entry hsm hp j).differentiableAt htop).hasFDerivAt
  have hfun : (fun y' : EuclideanSpace ℝ (Fin d) => fluxV Φ (p.1, y') j)
      = (fun q : ℝ × EuclideanSpace ℝ (Fin d) => fluxV Φ q j) ∘ (fun y' => (p.1, y')) := rfl
  rw [hfun]
  exact (h2.comp p.2 h1).fderiv

/-- The slice conversion for the flux entries, evaluated. -/
lemma fderiv_fluxV_slice {Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    {p : ℝ × EuclideanSpace ℝ (Fin d)} (hp : p.2 ≠ 0) (j : Fin d) :
    fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin d) => fluxV Φ (p.1, y') j) p.2 (stdV j)
      = fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => fluxV Φ q j) p (0, stdV j) := by
  rw [fderiv_fluxV_slice_CLM hsm hp j]
  rfl

/-- The derivative of the flux field at a fixed time, in coordinates. -/
lemma hasFDerivAt_fluxT {Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    {p : ℝ × EuclideanSpace ℝ (Fin d)} (hp : p.2 ≠ 0) :
    HasFDerivAt (fluxT Φ p.1)
      ((coordE d).symm ∘L (ContinuousLinearMap.pi fun j : Fin d =>
        fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin d) => fluxV Φ (p.1, y') j) p.2)) p.2 := by
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hcoord : ∀ j : Fin d,
      HasFDerivAt (fun y' : EuclideanSpace ℝ (Fin d) => fluxV Φ (p.1, y') j)
        (fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin d) => fluxV Φ (p.1, y') j) p.2) p.2 := by
    intro j
    rw [fderiv_fluxV_slice_CLM hsm hp j]
    have h1 : HasFDerivAt (fun y' : EuclideanSpace ℝ (Fin d) => (p.1, y'))
        (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin d))) p.2 :=
      (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id p.2)
    have h2 : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin d) => fluxV Φ q j)
        (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => fluxV Φ q j) p) p :=
      ((contDiffAt_fluxV_entry hsm hp j).differentiableAt htop).hasFDerivAt
    exact h2.comp p.2 h1
  have hpi : HasFDerivAt
      (fun y' : EuclideanSpace ℝ (Fin d) => fun j : Fin d => fluxV Φ (p.1, y') j)
      (ContinuousLinearMap.pi fun j : Fin d =>
        fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin d) => fluxV Φ (p.1, y') j) p.2) p.2 :=
    hasFDerivAt_pi.mpr hcoord
  have hcomp := ((coordE d).symm.hasFDerivAt (x := _)).comp p.2 hpi
  have hfun : (fluxT Φ p.1)
      = fun y' : EuclideanSpace ℝ (Fin d) => (coordE d).symm (fun j : Fin d => fluxV Φ (p.1, y') j) := by
    funext y'
    rfl
  rw [hfun]
  simpa [Function.comp_def] using hcomp

/-- The concrete form of the trace. -/
lemma trace_fderiv_fluxT {Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    {p : ℝ × EuclideanSpace ℝ (Fin d)} (hp : p.2 ≠ 0) :
    (∑ j : Fin d, ((fderiv ℝ (fluxT Φ p.1) p.2 (stdV j) :
        EuclideanSpace ℝ (Fin d)) : Fin d → ℝ) j)
      = ∑ j : Fin d, fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin d) => fluxV Φ (p.1, y') j) p.2 (stdV j) := by
  have hd : fderiv ℝ (fluxT Φ p.1) p.2
      = (coordE d).symm ∘L (ContinuousLinearMap.pi fun j : Fin d =>
          fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin d) => fluxV Φ (p.1, y') j) p.2) :=
    (hasFDerivAt_fluxT hsm hp).fderiv
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hd]
  rfl

end FluxDeriv

/-! ## The pointwise divergence identity for the cut-off flux field -/

section DivIdentity

variable {d : ℕ}

/-- The `innerSL` pairing against a standard basis vector. -/
lemma innerSL_stdV {d : ℕ} (y : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    (innerSL ℝ y) (stdV i) = (y : Fin d → ℝ) i := by
  rw [show (innerSL ℝ y) (stdV i) = inner ℝ y (stdV i) from rfl]
  rw [inner_eq_sum_coords]
  rw [Finset.sum_eq_single i]
  · simp [stdV, PiLp.single_apply]
  · intro b _ hb
    simp [stdV, PiLp.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **The pointwise divergence identity.**  The divergence of the cut-off flux field is the
cut-off `t`-derivative of the determinant of the Jacobian. -/
theorem divE_cutoffField {Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    (hcone : ∀ (t r : ℝ) (y : EuclideanSpace ℝ (Fin d)), 0 < r → Φ (t, r • y) = r • Φ (t, y))
    (hnorm : ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin d)), ‖Φ (t, y)‖ = ‖y‖)
    (t : ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    divE (cutoffField Φ t) y
      = chi y * fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (jacM Φ q).det) (t, y) (1, 0) := by
  rcases eq_or_ne y 0 with rfl | hy
  · have hzero : (fun y' : EuclideanSpace ℝ (Fin d) => cutoffField Φ t y') =ᶠ[𝓝 0] 0 := by
      filter_upwards [chi_zero_near_zero] with y' hy'
      simp [cutoffField_apply, hy']
    have hf : fderiv ℝ (cutoffField Φ t) 0 = 0 := by rw [hzero.fderiv_eq]; simp
    have hchi : chi (0 : EuclideanSpace ℝ (Fin d)) = 0 := chi_eq_zero_of_small (by simp)
    simp only [divE, hf, hchi, ContinuousLinearMap.zero_apply, WithLp.ofLp_zero, Pi.zero_apply,
      Finset.sum_const_zero, zero_mul]
  · have hp : ((t, y) : ℝ × EuclideanSpace ℝ (Fin d)).2 ≠ 0 := hy
    -- the product rule
    have hchi_diff : HasFDerivAt (chi : EuclideanSpace ℝ (Fin d) → ℝ) (fderiv ℝ chi y) y :=
      (hasFDerivAt_chi y).congr_fderiv (hasFDerivAt_chi y).fderiv.symm
    have hflux_diff : HasFDerivAt (fluxT Φ t) (fderiv ℝ (fluxT Φ t) y) y :=
      (hasFDerivAt_fluxT hsm hp).differentiableAt.hasFDerivAt
    have hprod : fderiv ℝ (cutoffField Φ t) y
        = chi y • fderiv ℝ (fluxT Φ t) y
          + (fderiv ℝ chi y).smulRight (fluxT Φ t y) := by
      have h := hchi_diff.smul hflux_diff
      have hfun : cutoffField Φ t = fun y' : EuclideanSpace ℝ (Fin d) => chi y' • fluxT Φ t y' := rfl
      rw [hfun]
      exact h.fderiv
    -- the trace of the product
    have htr : ∀ i : Fin d,
        (((fderiv ℝ (cutoffField Φ t) y) (stdV i) : EuclideanSpace ℝ (Fin d)) : Fin d → ℝ) i
          = chi y * (((fderiv ℝ (fluxT Φ t) y) (stdV i) : EuclideanSpace ℝ (Fin d)) : Fin d → ℝ) i
            + (fderiv ℝ chi y) (stdV i) * (fluxT Φ t y : Fin d → ℝ) i := by
      intro i
      rw [hprod]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
        WithLp.ofLp_add, WithLp.ofLp_smul]
    -- the first sum is `∂_t det`
    have hfirst : (∑ i : Fin d,
          ((fderiv ℝ (fluxT Φ t) y (stdV i) : EuclideanSpace ℝ (Fin d)) : Fin d → ℝ) i)
        = fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (jacM Φ q).det) (t, y) (1, 0) := by
      rw [trace_fderiv_fluxT hsm hp]
      have h2 : (∑ j : Fin d, fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin d) => fluxV Φ (t, y') j)
            y (stdV j))
          = ∑ j : Fin d, fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => fluxV Φ q j)
              (t, y) (0, stdV j) :=
        Finset.sum_congr rfl fun j _ => fderiv_fluxV_slice hsm hp j
      rw [h2]
      simp only [fluxV]
      rw [← flux_identity_conical hsm hp]
    -- the second sum vanishes by tangency
    have hsecond : (∑ i : Fin d,
          (fderiv ℝ chi y) (stdV i) * (fluxT Φ t y : Fin d → ℝ) i) = 0 := by
      have hd : fderiv ℝ chi y = (deriv chiProf (‖y‖ ^ 2)) • (2 • innerSL ℝ y) :=
        (hasFDerivAt_chi y).fderiv
      have hstep : ∀ i : Fin d,
          (fderiv ℝ chi y) (stdV i)
            = deriv chiProf (‖y‖ ^ 2) * (2 * (y : Fin d → ℝ) i) := by
        intro i
        rw [hd]
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
        rw [innerSL_stdV]
        ring
      rw [Finset.sum_congr rfl fun i _ => by rw [hstep i]]
      have h3 : (∑ i : Fin d, deriv chiProf (‖y‖ ^ 2) * (2 * (y : Fin d → ℝ) i)
            * (fluxT Φ t y : Fin d → ℝ) i)
          = ∑ i : Fin d, deriv chiProf (‖y‖ ^ 2) * (2 * (y : Fin d → ℝ) i)
              * (fluxV Φ (t, y)) i :=
        Finset.sum_congr rfl fun i _ => by rw [fluxT_coord]
      have h4 : (∑ i : Fin d, deriv chiProf (‖y‖ ^ 2) * (2 * (y : Fin d → ℝ) i)
            * (fluxV Φ (t, y)) i)
          = deriv chiProf (‖y‖ ^ 2) * 2
              * (∑ i : Fin d, (fluxV Φ (t, y)) i * (y : Fin d → ℝ) i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [h3, h4, fluxV_tangent hsm hcone hnorm hp, mul_zero]
    rw [divE]
    simp only [stdV] at htr hfirst hsecond ⊢
    rw [Finset.sum_congr rfl fun i _ => htr i, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, hfirst, hsecond, add_zero]

end DivIdentity
