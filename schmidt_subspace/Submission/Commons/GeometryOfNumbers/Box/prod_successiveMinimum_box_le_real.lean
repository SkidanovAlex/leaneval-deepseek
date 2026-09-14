import Mathlib
import Submission.Commons.GeometryOfNumbers.SuccessiveMinima.minkowski_second_upper_of_exclusion
import Submission.Commons.GeometryOfNumbers.SuccessiveMinima.successive_minima_unimodular
import Submission.Commons.GeometryOfNumbers.SuccessiveMinima.exists_unimodular_flag
import Submission.Commons.GeometryOfNumbers.Box.volume_real_box

set_option maxHeartbeats 4000000

open MeasureTheory Set Filter
open scoped Pointwise BigOperators Topology

namespace Commons.GeometryOfNumbers.Box

open Commons.GeometryOfNumbers.SuccessiveMinima

/-- **Minkowski's second theorem, upper bound, for the lattice `ℤ^N`.**

For a closed, bounded, convex, symmetric set `K ⊆ ℝ^N` with nonempty interior, the product of
the successive minima of `K` with respect to `ℤ^N` is at most `2^N / vol K`.  This is the general
form (no straightening hypothesis); it is the statement proved internally in
`Commons.GeometryOfNumbers.SuccessiveMinima.minkowski_second_upper_of_exclusion`. -/
theorem minkowski_second_upper_general (N : ℕ) (K : Set (Fin N → ℝ))
    (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K) (hclosed : IsClosed K)
    (hbdd : Bornology.IsBounded K) (hint : (interior K).Nonempty) :
    (∏ i : Fin N, lam N K (i.val + 1)) * (volume K).toReal ≤ 2 ^ N := by
  classical
  obtain ⟨v, hvLI, _hvmin, hvexc⟩ := gauge_realizers_exclusion N K hconv hsym hclosed hbdd hint
  obtain ⟨U, hUZ, hUZi, hUdet, hUflag⟩ := exists_unimodular_flag N v hvLI
  have hUdet_ne : LinearMap.det U ≠ 0 := abs_ne_zero.mp (by rw [hUdet]; exact one_ne_zero)
  let Ue : (Fin N → ℝ) ≃ₗ[ℝ] (Fin N → ℝ) := U.equivOfDetNeZero hUdet_ne
  have hUe : ∀ x : Fin N → ℝ, Ue x = U x := fun x => rfl
  set K' : Set (Fin N → ℝ) := U '' K with hK'def
  have hconv' : Convex ℝ K' := by rw [hK'def]; exact hconv.linear_image U
  have hsym' : ∀ x ∈ K', -x ∈ K' := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨-y, hsym y hy, by rw [map_neg]⟩
  have hclosed' : IsClosed K' := by
    rw [hK'def]
    have hset : U '' K = (Ue.symm : (Fin N → ℝ) → (Fin N → ℝ)) ⁻¹' K := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        show Ue.symm (Ue y) ∈ K
        rwa [LinearEquiv.symm_apply_apply]
      · intro hx
        exact ⟨Ue.symm x, hx, (hUe (Ue.symm x)).trans (LinearEquiv.apply_symm_apply Ue x)⟩
    rw [hset, show (Ue.symm : (Fin N → ℝ) → (Fin N → ℝ)) = ⇑(Ue.symm : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) from rfl]
    exact hclosed.preimage (LinearMap.continuous_of_finiteDimensional _)
  have hbdd' : Bornology.IsBounded K' := by
    rw [hK'def]
    have h := Bornology.IsBounded.image
      (f := (Ue.toContinuousLinearEquiv : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) hbdd
    simpa [hUe] using h
  have hcoe : (⇑Ue.toContinuousLinearEquiv.toHomeomorph : (Fin N → ℝ) → (Fin N → ℝ)) = U := by
    funext x
    exact hUe x
  have hint' : (interior K').Nonempty := by
    rw [hK'def]
    have h := (Homeomorph.image_interior Ue.toContinuousLinearEquiv.toHomeomorph K).symm
    rw [hcoe] at h
    rw [h]
    exact Set.Nonempty.image _ hint
  have hexcl' : ∀ (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓN : ℓ ≤ N) (y : Fin N → ℤ),
      gauge K' (cZ y) < lam N K' ℓ → ∀ j : Fin N, ℓ - 1 ≤ j.val → y j = 0 := by
    intro ℓ hℓ1 hℓN y hyg j hj
    obtain ⟨x, hx⟩ := hUZi y
    obtain ⟨hlam, -, hgauge⟩ := successive_minima_unimodular N K hconv hsym hclosed hint
      U hUZ hUZi hUdet ℓ
    have hlam' : lam N K' ℓ = lam N K ℓ := by simpa [lam, hK'def] using hlam
    have h3 := hgauge (fun k => (x k : ℝ))
    have hg : gauge K (fun k => (x k : ℝ)) = gauge K' (fun k => (y k : ℝ)) := by
      have h3' : gauge K' (fun k => (y k : ℝ)) = gauge K (fun k => (x k : ℝ)) := by
        rw [← hx]
        exact h3
      exact h3'.symm
    have hlt : gauge K (fun k => (x k : ℝ)) < lam N K ℓ := by
      rw [hg, ← hlam']
      change gauge K' (cZ y) < lam N K' ℓ
      exact hyg
    have hspan := hvexc ℓ hℓ1 hℓN x (by simpa [lam] using hlt)
    have hmemU : U (fun k => (x k : ℝ)) ∈ U '' (Submodule.span ℝ (Set.range (fun j : Fin (ℓ - 1) =>
        (fun k => (v (Fin.castLE (by omega) j) k : ℝ))))) := ⟨_, hspan, rfl⟩
    rw [hUflag (ℓ - 1) (by omega)] at hmemU
    rw [hx] at hmemU
    exact eq_zero_of_mem_span_prefix (by omega) hmemU j hj
  have hflag := minkowski_second_upper_flag N K' hconv' hsym' hclosed' hbdd' hint' hexcl'
  have hlamall : ∀ ℓ : ℕ, lam N K' ℓ = lam N K ℓ := by
    intro ℓ
    obtain ⟨h1, -, -⟩ := successive_minima_unimodular N K hconv hsym hclosed hint U hUZ hUZi hUdet ℓ
    simpa [lam, hK'def] using h1
  have hvol : (volume K').toReal = (volume K).toReal := by
    obtain ⟨-, h2, -⟩ := successive_minima_unimodular N K hconv hsym hclosed hint U hUZ hUZi hUdet 0
    rw [Measure.real_def, Measure.real_def] at h2
    simpa [hK'def] using h2
  rw [Finset.prod_congr rfl (fun i _ => hlamall (i.val+1)), hvol] at hflag
  exact hflag


/-- Convenience abbreviation: the successive-minima functional of
`Commons.GeometryOfNumbers.SuccessiveMinima` with respect to the lattice `ℤ^N`. -/
noncomputable abbrev lamK (N : ℕ) (K : Set (Fin N → ℝ)) (ℓ : ℕ) : ℝ :=
  Commons.GeometryOfNumbers.SuccessiveMinima.lam N K ℓ

theorem prod_successiveMinimum_box_le_real {N : ℕ} (hN : 1 ≤ N) (L : Fin N → Fin N → ℂ)
    (hdet : (Matrix.of L).det ≠ 0) (hreal : ∀ i j, ∃ r : ℝ, L i j = (r : ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ) (hQ : 1 ≤ Q) (c : Fin N → ℝ), (∑ i, c i < 0) →
      ∀ (lam : Fin N → ℝ),
        (∀ j : Fin N, lam j = sInf {t : ℝ | 0 ≤ t ∧ (j.val + 1) ≤ Module.finrank ℚ
          (Submodule.span ℚ (Set.image (fun y : Fin N → ℤ => fun k => (y k : ℚ))
            {y : Fin N → ℤ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ t * Q ^ (c i)}))}) →
      (∏ j : Fin N, lam j) ≤ C * Q ^ (-(∑ i, c i)) := by
  classical
  let M : Matrix (Fin N) (Fin N) ℝ := fun i j => Classical.choose (hreal i j)
  have hM : ∀ i j, L i j = (M i j : ℂ) := fun i j => Classical.choose_spec (hreal i j)
  have hdetM : M.det ≠ 0 := by
    intro h
    apply hdet
    have hmap : (Matrix.of L) = M.map (algebraMap ℝ ℂ) := by
      ext i j; simp [hM i j]
    have hdetmap : (M.map (algebraMap ℝ ℂ)).det = (M.det : ℂ) :=
      (RingHom.map_det (algebraMap ℝ ℂ) M).symm
    rw [hmap, hdetmap, h]
    simp
  refine ⟨|M.det|, abs_pos.mpr hdetM, ?_⟩
  intro Q hQ c hc lam hlam
  have hQpos : 0 < Q := lt_of_lt_of_le one_pos hQ
  -- The norm of the `i`-th complex form on an integer vector is the absolute value of the
  -- corresponding real form.
  have norm_eq : ∀ (i : Fin N) (y : Fin N → ℤ),
      ‖∑ k, L i k * (y k : ℂ)‖ = |∑ k, M i k * (y k : ℝ)| := by
    intro i y
    have h1 : (∑ k, L i k * (y k : ℂ))
        = Complex.ofReal (∑ k, M i k * ((y k : ℤ) : ℝ)) := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [hM i k, Complex.ofReal_mul]
      push_cast
      rfl
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
  -- The symmetric convex body `K` and the linear equivalence `e = M.mulVecLin`.
  set K : Set (Fin N → ℝ) := {x : Fin N → ℝ | ∀ i, |∑ k, M i k * x k| ≤ Q ^ (c i)}
    with hKdef
  have hMl_inj : Function.Injective (Matrix.mulVecLin M) := by
    have hunit : IsUnit M :=
      (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdetM)
    have hinj : Function.Injective M.mulVec := (Matrix.mulVec_injective_iff_isUnit).mpr hunit
    intro x y hxy
    exact hinj (by simpa [Matrix.mulVecLin_apply] using hxy)
  let e : (Fin N → ℝ) ≃ₗ[ℝ] (Fin N → ℝ) :=
    LinearMap.linearEquivOfInjective (Matrix.mulVecLin M) hMl_inj (by simp)
  have he_apply : ∀ (x : Fin N → ℝ) (i : Fin N), (e x) i = ∑ k, M i k * x k := by
    intro x i
    show (Matrix.mulVecLin M x) i = _
    rw [Matrix.mulVecLin_apply]
    rfl
  set B : Set (Fin N → ℝ) := Set.Icc (fun i => -(Q ^ (c i))) (fun i => Q ^ (c i))
    with hBdef
  have memB : ∀ z : Fin N → ℝ, z ∈ B ↔ ∀ i, |z i| ≤ Q ^ (c i) := by
    intro z
    rw [hBdef]
    simp only [Set.mem_Icc, Pi.le_def]
    constructor
    · rintro ⟨h1, h2⟩ i
      exact abs_le.mpr ⟨h1 i, h2 i⟩
    · intro h
      exact ⟨fun i => (abs_le.mp (h i)).1, fun i => (abs_le.mp (h i)).2⟩
  have hKpre : K = e ⁻¹' B := by
    ext x
    rw [hKdef, Set.mem_preimage, memB]
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hx i; rw [he_apply x i]; exact hx i
    · intro hx i
      have h := hx i
      rw [he_apply x i] at h
      exact h
  have hcont : Continuous (e : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) :=
    LinearMap.continuous_of_finiteDimensional _
  have hconv : Convex ℝ K := by
    rw [hKpre, hBdef]
    exact (convex_Icc _ _).linear_preimage (e : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))
  have hsym : ∀ x ∈ K, -x ∈ K := by
    intro x hx
    rw [hKpre] at hx
    rw [hKpre]
    rw [Set.mem_preimage] at hx ⊢
    rw [memB] at hx ⊢
    intro i
    have hneg : (e (-x)) i = -((e x) i) := by rw [map_neg, Pi.neg_apply]
    rw [hneg, abs_neg]
    exact hx i
  have hclosed : IsClosed K := by
    rw [hKpre, hBdef]
    exact isClosed_Icc.preimage hcont
  have hBbdd : Bornology.IsBounded B := by
    rw [hBdef]
    exact (isCompact_Icc (a := (fun i : Fin N => -(Q ^ (c i))))
      (b := (fun i : Fin N => Q ^ (c i)))).isBounded
  have hKe : K = e.symm '' B := by
    rw [hKpre]
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      show e (e.symm y) ∈ B
      rwa [LinearEquiv.apply_symm_apply]
  have hbdd : Bornology.IsBounded K := by
    rw [hKe]
    simpa using Bornology.IsBounded.image
      (f := (e.symm.toContinuousLinearEquiv : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) hBbdd
  have hint : (interior K).Nonempty := by
    refine ⟨0, ?_⟩
    set V : Set (Fin N → ℝ) := Set.pi Set.univ (fun i => Set.Ioo (-(Q ^ (c i))) (Q ^ (c i)))
      with hVdef
    have hVopen : IsOpen V := by
      rw [hVdef]
      exact isOpen_set_pi Set.finite_univ (fun i _ => isOpen_Ioo)
    have hUsub : e ⁻¹' V ⊆ K := by
      intro x hx
      rw [hKpre]
      rw [Set.mem_preimage]
      rw [memB]
      intro i
      have hxV : e x ∈ V := Set.mem_preimage.mp hx
      have hmem := (Set.mem_pi.mp hxV) i (Set.mem_univ i)
      rw [Set.mem_Ioo] at hmem
      rw [he_apply x i]
      exact abs_le.mpr ⟨le_of_lt hmem.1, le_of_lt hmem.2⟩
    have h0U : (0 : Fin N → ℝ) ∈ e ⁻¹' V := by
      rw [Set.mem_preimage]
      show e 0 ∈ V
      rw [map_zero, hVdef, Set.mem_pi]
      intro i _
      rw [Set.mem_Ioo, Pi.zero_apply]
      have hq : 0 < Q ^ (c i) := Real.rpow_pos_of_pos hQpos _
      exact ⟨by linarith, by linarith⟩
    exact interior_maximal hUsub (hVopen.preimage hcont) h0U
  -- Membership dictionary between the box and the dilated body.
  have boxmem : ∀ (b : ℝ) (hb : 0 < b) (y : Fin N → ℤ),
      (∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ b * Q ^ (c i)) ↔
        (fun k => ((y k : ℤ) : ℝ)) ∈ b • K := by
    intro b hb y
    have hsumfac : ∀ i : Fin N,
        (∑ k, M i k * (b⁻¹ • (fun k => ((y k : ℤ) : ℝ))) k)
        = b⁻¹ * (∑ k, M i k * ((y k : ℤ) : ℝ)) := by
      intro i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hb), hKdef]
    constructor
    · intro hy i
      have h := hy i
      rw [norm_eq i y] at h
      rw [hsumfac i, abs_mul, abs_of_pos (inv_pos.mpr hb), inv_mul_le_iff₀ hb]
      exact h
    · intro hy i
      have h := hy i
      rw [hsumfac i, abs_mul, abs_of_pos (inv_pos.mpr hb), inv_mul_le_iff₀ hb] at h
      rw [norm_eq i y]
      exact h
  -- The comparison of the box successive minima with the body's successive minima.
  let lamBox : ℝ → ℕ := fun t => Module.finrank ℚ (Submodule.span ℚ
    (Set.image (fun y : Fin N → ℤ => fun k => (y k : ℚ))
      {y : Fin N → ℤ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ t * Q ^ (c i)}))
  have hlamj : ∀ j : Fin N, lam j = sInf {t : ℝ | 0 ≤ t ∧ (j.val + 1) ≤ lamBox t} :=
    fun j => hlam j
  have hkey : ∀ j : Fin N, lam j ≤ lamK N K (j.val + 1) := by
    intro j
    rw [hlamj j]
    set ℓ : ℕ := j.val + 1 with hℓdef
    have hℓN : ℓ ≤ N := by have := j.isLt; omega
    have hne : ({t : ℝ | 0 < t ∧ ∃ v : Fin ℓ → (Fin N → ℤ),
        LinearIndependent ℝ (fun a => fun k => (v a k : ℝ)) ∧
        ∀ a, (fun k => (v a k : ℝ)) ∈ t • K}).Nonempty := by
      obtain ⟨r, hr, hball⟩ := exists_ball_subset hconv hsym hint
      exact lam_set_nonempty_of_mem_interior N K hr hball ℓ hℓN
    refine le_csInf hne ?_
    intro b hb
    obtain ⟨hbpos, v, hvLI, hvb⟩ := hb
    refine csInf_le ⟨0, fun x hx => hx.1⟩ ⟨le_of_lt hbpos, ?_⟩
    change ℓ ≤ Module.finrank ℚ (Submodule.span ℚ
      (Set.image (fun y : Fin N → ℤ => fun k => (y k : ℚ))
        {y : Fin N → ℤ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ b * Q ^ (c i)}))
    have hmem : ∀ a : Fin ℓ, v a ∈ {y : Fin N → ℤ |
        ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ b * Q ^ (c i)} := by
      intro a i
      exact (boxmem b hbpos (v a)).mpr (hvb a) i
    have hLIQ : LinearIndependent ℚ (fun a : Fin ℓ => fun k => (v a k : ℚ)) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg a
      have hgR : (∑ i, (g i : ℝ) • (fun k => (v i k : ℝ))) = 0 := by
        funext k
        have hk := congrFun hg k
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk ⊢
        have hk' := congrArg (fun x : ℚ => (x : ℝ)) hk
        push_cast at hk'
        simpa using hk'
      have hz := (Fintype.linearIndependent_iff.mp hvLI) (fun i => (g i : ℝ)) hgR a
      exact_mod_cast hz
    have hspan_le : Submodule.span ℚ (Set.range (fun a : Fin ℓ => fun k => (v a k : ℚ)))
        ≤ Submodule.span ℚ (Set.image (fun y : Fin N → ℤ => fun k => (y k : ℚ))
          {y : Fin N → ℤ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ b * Q ^ (c i)}) := by
      apply Submodule.span_mono
      rintro x ⟨a, rfl⟩
      exact ⟨v a, hmem a, rfl⟩
    have hfin1 : Module.finrank ℚ (Submodule.span ℚ
        (Set.range (fun a : Fin ℓ => fun k => (v a k : ℚ)))) = ℓ := by
      have := finrank_span_eq_card hLIQ
      simpa using this
    have hfin2 := Submodule.finrank_mono hspan_le
    rw [hfin1] at hfin2
    exact hfin2
  have hprod_le : ∏ j : Fin N, lam j ≤ ∏ j : Fin N, lamK N K (j.val + 1) := by
    apply Finset.prod_le_prod
    · intro j _
      rw [hlamj j]
      exact Real.sInf_nonneg (fun x hx => hx.1)
    · intro j _; exact hkey j
  -- Minkowski's second theorem and the volume computation.
  have hmink := minkowski_second_upper_general N K hconv hsym hclosed hbdd hint
  have hvolK : (volume K).toReal = 2 ^ N * Q ^ (∑ i, c i) / |M.det| := by
    rw [hKdef]
    exact volume_real_box hN M hdetM Q hQpos c
  have hvolpos : 0 < (volume K).toReal := by
    rw [hvolK]; positivity
  have hμle : ∏ j : Fin N, lamK N K (j.val + 1) ≤ 2 ^ N / (volume K).toReal :=
    (le_div_iff₀ hvolpos).mpr hmink
  have hfinal : 2 ^ N / (volume K).toReal = |M.det| * Q ^ (-(∑ i, c i)) := by
    rw [hvolK, Real.rpow_neg hQpos.le]
    have h2N : (0 : ℝ) < 2 ^ N := by positivity
    have hQc : (0 : ℝ) < Q ^ (∑ i, c i) := Real.rpow_pos_of_pos hQpos _
    have hDne : (M.det : ℝ) ≠ 0 := hdetM
    field_simp
  calc ∏ j : Fin N, lam j ≤ ∏ j : Fin N, lamK N K (j.val + 1) := hprod_le
    _ ≤ 2 ^ N / (volume K).toReal := hμle
    _ = |M.det| * Q ^ (-(∑ i, c i)) := hfinal

end Commons.GeometryOfNumbers.Box
