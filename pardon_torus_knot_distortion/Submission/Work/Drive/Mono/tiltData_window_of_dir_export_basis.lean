import Mathlib
import Submission.Work.Drive.Mono.tiltData_in_window_export
import Submission.Work.Drive.Mono.Band.BandChartDefs
import Submission.Work.Drive.Mono.Band.clauseTwo_exists

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
open Work.Drive.Mono.Band

noncomputable section

/-!
# The thin-slab tilt data with a wall functional killing no coordinate direction

`Work.Drive.Mono.tiltData_window_of_dir_export` produces, at a prescribed orthonormal pair
`v ⊥ n`, a half-width `h` in a prescribed window and a unit direction `nn ⊥ v`, close to `n`,
together with the full tilt genericity and the face regularity.  In the construction `nn` is the
direction `dirOf τ a₀ b₀` of the projective chart at a parameter `τ` chosen to avoid the null set
of bad chart values.

For the junction route one needs the extra clause that the wall functional `innerSL ℝ nn` kills no
coordinate direction `e_{σ i}`.  If `v` is parallel to no `e_{σ i}` (hypothesis `hvax`, i.e. all
coordinates of `v` are non-zero), the set of parameters `τ` with `⟪dirOf τ a₀ b₀, e_{σ i}⟫ = 0` is
finite — it is contained in the (at most three) zero sets of the affine maps
`τ ↦ τ ⟪a₀, e_{σ i}⟫ + ⟪b₀, e_{σ i}⟫`, whose two coefficients cannot both vanish because
`v, a₀, b₀` is an orthonormal basis.  Adding the corresponding vertical lines to the null set of
chart values avoided by `Work.Drive.Mono.Band.exists_window_avoiding` therefore costs nothing.

The hypothesis `hvax` is necessary: if `v = ± e_{σ i}` then `v^⊥` is the coordinate hyperplane
`{x : x_{σ i} = 0}`, so every unit `nn ⊥ v` has `⟪nn, e_{σ i}⟫ = 0` and the extra clause is
unsatisfiable.
-/

/-- **Two orthonormal vectors of `v^⊥` cannot both be orthogonal to a standard basis vector.**  If
`v, a₀, b₀` is an orthonormal triple of `ℝ³`, `e_j` is a standard basis vector and `⟪v, e_j⟫ ≠ 0`,
then `a₀` or `b₀` has a non-zero `j`-th inner product with `e_j`.

Proof: if both vanished then, writing `X := e_j - ⟪v,e_j⟫ • v`, the vector `X` is orthogonal to
`v, a₀` and `b₀`, hence `X = 0` by `projV_coord_eq_zero`; thus `e_j` is a multiple of `v`, so `v`
has a zero coordinate in every direction different from `j`, contradicting `⟪v, e_k⟫ ≠ 0` for some
`k ≠ j`. -/
theorem coord_ne_zero_of_orthonormal {v a₀ b₀ : R3}
    (hv : ‖v‖ = 1) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0)
    (hvne : ∀ k : Fin 3, inner ℝ v (EuclideanSpace.single k (1 : ℝ)) ≠ 0) (j : Fin 3) :
    inner ℝ a₀ (EuclideanSpace.single j (1 : ℝ)) ≠ 0 ∨
      inner ℝ b₀ (EuclideanSpace.single j (1 : ℝ)) ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨h0, h1⟩ := h
  set e : R3 := EuclideanSpace.single j (1 : ℝ) with he
  set c : ℝ := inner ℝ v e with hc
  have hX : e - c • v = 0 := by
    refine projV_coord_eq_zero hv ha hb hab hva hvb ?_ ?_ ?_
    · rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hv, hc]
      ring
    · rw [inner_sub_right, real_inner_smul_right, real_inner_comm v a₀, hva, h0]
      ring
    · rw [inner_sub_right, real_inner_smul_right, real_inner_comm v b₀, hvb, h1]
      ring
  have hev : e = c • v := sub_eq_zero.mp hX
  have hcne : c ≠ 0 := by rw [hc, he]; exact hvne j
  have hv_eq : v = c⁻¹ • e := by
    rw [hev, smul_smul, inv_mul_cancel₀ hcne, one_smul]
  obtain ⟨k, hkj⟩ := exists_ne j
  have hzero : inner ℝ v (EuclideanSpace.single k (1 : ℝ)) = 0 := by
    rw [hv_eq, real_inner_smul_left, he]
    have h2 : inner ℝ (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single k (1 : ℝ)) = 0 := by
      rw [EuclideanSpace.inner_single_left]
      simp [hkj]
    rw [h2, mul_zero]
  exact hvne k hzero

/-- **The parameters at which the projective direction `dirOf τ a₀ b₀` kills a coordinate
direction form a finite set.**  For each `i` the map
`τ ↦ ⟪dirOf τ a₀ b₀, e_{σ i}⟫ = ‖τ • a₀ + b₀‖⁻¹ * (τ * ⟪a₀, e_{σ i}⟫ + ⟪b₀, e_{σ i}⟫)`
vanishes on at most one point, because the affine map in the parentheses is non-constant by
`coord_ne_zero_of_orthonormal`. -/
theorem finite_bad_tau {v a₀ b₀ : R3} (σ : Equiv.Perm (Fin 3))
    (hv : ‖v‖ = 1) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0)
    (hvne : ∀ k : Fin 3, inner ℝ v (EuclideanSpace.single k (1 : ℝ)) ≠ 0) :
    {τ : ℝ | ∃ i : Fin 3,
      inner ℝ (dirOf τ a₀ b₀) (EuclideanSpace.single (σ i) (1 : ℝ)) = 0}.Finite := by
  have hkey : ∀ (j : Fin 3) (τ : ℝ),
      inner ℝ (dirOf τ a₀ b₀) (EuclideanSpace.single j (1 : ℝ))
        = (‖τ • a₀ + b₀‖)⁻¹ * (τ * inner ℝ a₀ (EuclideanSpace.single j (1 : ℝ))
            + inner ℝ b₀ (EuclideanSpace.single j (1 : ℝ))) := by
    intro j τ
    rw [dirOf, real_inner_smul_left, inner_add_left, real_inner_smul_left]
  have hset : {τ : ℝ | ∃ i : Fin 3,
        inner ℝ (dirOf τ a₀ b₀) (EuclideanSpace.single (σ i) (1 : ℝ)) = 0}
      = ⋃ i : Fin 3,
        {τ : ℝ | inner ℝ (dirOf τ a₀ b₀) (EuclideanSpace.single (σ i) (1 : ℝ)) = 0} := by
    ext τ; simp
  rw [hset]
  refine Set.finite_iUnion (fun i => ?_)
  by_cases hA : inner ℝ a₀ (EuclideanSpace.single (σ i) (1 : ℝ)) = 0
  · have hB : inner ℝ b₀ (EuclideanSpace.single (σ i) (1 : ℝ)) ≠ 0 := by
      rcases coord_ne_zero_of_orthonormal hv ha hb hab hva hvb hvne (σ i) with h | h
      · exact absurd hA h
      · exact h
    refine Set.Subsingleton.finite (fun τ₁ hτ₁ τ₂ hτ₂ => ?_)
    have hτ₁' : inner ℝ (dirOf τ₁ a₀ b₀) (EuclideanSpace.single (σ i) (1 : ℝ)) = 0 := hτ₁
    rw [hkey (σ i) τ₁] at hτ₁'
    have hs : (‖τ₁ • a₀ + b₀‖)⁻¹ ≠ 0 :=
      inv_ne_zero (norm_ne_zero_iff.mpr (dirOf_denom_ne_zero ha hb hab τ₁))
    have h2 : τ₁ * inner ℝ a₀ (EuclideanSpace.single (σ i) (1 : ℝ))
        + inner ℝ b₀ (EuclideanSpace.single (σ i) (1 : ℝ)) = 0 :=
      (mul_eq_zero.mp hτ₁').resolve_left hs
    rw [hA, mul_zero, zero_add] at h2
    exact absurd h2 hB
  · refine Set.Subsingleton.finite (fun τ₁ hτ₁ τ₂ hτ₂ => ?_)
    have hτ₁' : inner ℝ (dirOf τ₁ a₀ b₀) (EuclideanSpace.single (σ i) (1 : ℝ)) = 0 := hτ₁
    have hτ₂' : inner ℝ (dirOf τ₂ a₀ b₀) (EuclideanSpace.single (σ i) (1 : ℝ)) = 0 := hτ₂
    rw [hkey (σ i) τ₁] at hτ₁'
    rw [hkey (σ i) τ₂] at hτ₂'
    have hs1 : (‖τ₁ • a₀ + b₀‖)⁻¹ ≠ 0 :=
      inv_ne_zero (norm_ne_zero_iff.mpr (dirOf_denom_ne_zero ha hb hab τ₁))
    have hs2 : (‖τ₂ • a₀ + b₀‖)⁻¹ ≠ 0 :=
      inv_ne_zero (norm_ne_zero_iff.mpr (dirOf_denom_ne_zero ha hb hab τ₂))
    have e1 : τ₁ * inner ℝ a₀ (EuclideanSpace.single (σ i) (1 : ℝ))
        + inner ℝ b₀ (EuclideanSpace.single (σ i) (1 : ℝ)) = 0 :=
      (mul_eq_zero.mp hτ₁').resolve_left hs1
    have e2 : τ₂ * inner ℝ a₀ (EuclideanSpace.single (σ i) (1 : ℝ))
        + inner ℝ b₀ (EuclideanSpace.single (σ i) (1 : ℝ)) = 0 :=
      (mul_eq_zero.mp hτ₂').resolve_left hs2
    have hzero : inner ℝ a₀ (EuclideanSpace.single (σ i) (1 : ℝ)) * (τ₁ - τ₂) = 0 := by
      nlinarith [e1, e2]
    have : τ₁ - τ₂ = 0 := (mul_eq_zero.mp hzero).resolve_left hA
    linarith

/-- **The exported thin-slab band data, with a wall functional that kills no coordinate
direction.**  This is the *proved* `Work.Drive.Mono.tiltData_window_of_dir_export` with one extra
conjunct: the wall normal `nn` produced by the construction (the direction `dirOf τ a₀ b₀` of the
projective chart) has all three coordinates nonzero, i.e. `(innerSL ℝ nn) (e_{σ i}) ≠ 0` for every
`i`.

The hypothesis `hvax` (`v` is parallel to no standard basis direction) is necessary: if `v = ± e_{σ i}`
then `v^⊥` is the coordinate hyperplane `{x : x_{σ i} = 0}`, so *no* unit `nn ⊥ v` has `nn_{σ i} ≠ 0`
and the conjunct is unsatisfiable.  Under `hvax` the affine map `τ ↦ (τ a₀ + b₀)(σ i)` is
non-constant, so the set of parameters `τ` with `(τ a₀ + b₀)(σ i) = 0` is a single point (or empty);
adding those three lines (as the vertical strips `ℝ × {τ}`) to the null set `S` of chart values
avoided by `Work.Drive.Mono.Band.exists_window_avoiding` in `tiltData_window_of_dir_export`'s final
step costs nothing and gives the clause, since the returned `nn` is `dirOf τ a₀ b₀` at the chosen
`τ`. -/
theorem tiltData_window_of_dir_export_basis
    (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u A B ρ : ℝ) (v n : R3)
    (hA : 0 < A) (hAB : A < B) (hB : B ≤ Work.Drive.Mono.boxWidth s σ v - |u|) (hρ : 0 < ρ)
    (hv1 : ‖v‖ = 1) (hn1 : ‖n‖ = 1) (hvn : inner ℝ v n = 0)
    (hvax : ∀ i : Fin 3, inner ℝ v (EuclideanSpace.single (σ i) (1 : ℝ)) ≠ 0)
    (hgood : Work.Drive.Mono.Band.HeightGood ψ n) :
    ∃ (h : ℝ) (nn : R3) (exc : Finset ℝ), A < h ∧ h < B ∧
      h + |u| < Work.Drive.Mono.boxWidth s σ v ∧
      ‖nn - n‖ < ρ ∧ ‖nn‖ = 1 ∧ inner ℝ v nn = 0 ∧
      (∀ i : Fin 3, (innerSL ℝ) nn (EuclideanSpace.single (σ i) (1 : ℝ)) ≠ 0) ∧
      Work.Drive.Final.TiltedGenericity ψ s c σ u v h ((innerSL ℝ) nn) exc ∧
      (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
        z ∈ Submission.PBox s c σ →
        |inner ℝ v z - (inner ℝ v c + u)| = h →
        ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
          fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0) := by
  classical
  -- ## 1. the adapted orthonormal basis of `v^⊥`: `n` has projective coordinate `1` in it
  obtain ⟨a₀, b₀, ha, hb, hab, hva, hvb, hnb⟩ := exists_adapted_basis hv1 hn1 hvn
  -- ## 2. an interval of good parameters `τ` around `1`
  have hgood1 : HeightGood ψ (dirOf 1 a₀ b₀) := by
    rw [dirOf_one ha hb hab hnb]; exact hgood
  obtain ⟨ρh, hρh0, hρhgood⟩ := heightGood_open ψ hgood1
  have hdene : ∀ τ : ℝ, ‖τ • a₀ + b₀‖ ≠ 0 := by
    intro τ
    have h1 : inner ℝ b₀ (τ • a₀ + b₀) = 1 := inner_b₀_add_dirOf ha hb hab τ
    intro h0
    rw [norm_eq_zero] at h0
    rw [h0, inner_zero_right] at h1
    exact one_ne_zero h1.symm
  have hcont : Continuous fun τ : ℝ => dirOf τ a₀ b₀ := by
    unfold dirOf
    exact ((continuous_norm.comp (by fun_prop)).inv₀ hdene).smul (by fun_prop)
  have hmix : {τ : ℝ | HeightGood ψ (dirOf τ a₀ b₀) ∧
      ‖dirOf τ a₀ b₀ - n‖ < ρ} ∈ nhds (1 : ℝ) := by
    have hev1 : ∀ᶠ τ in nhds (1 : ℝ), HeightGood ψ (dirOf τ a₀ b₀) := by
      have hev : ∀ᶠ τ in nhds (1 : ℝ), ‖dirOf τ a₀ b₀ - dirOf 1 a₀ b₀‖ < ρh :=
        hcont.continuousAt.eventually (Metric.ball_mem_nhds (dirOf 1 a₀ b₀) hρh0)
      filter_upwards [hev] with τ hτ
      exact hρhgood _ hτ
    have hev2 : ∀ᶠ τ in nhds (1 : ℝ), ‖dirOf τ a₀ b₀ - n‖ < ρ := by
      have hn' : n = dirOf 1 a₀ b₀ := (dirOf_one ha hb hab hnb).symm
      rw [hn']
      exact hcont.continuousAt.eventually (Metric.ball_mem_nhds (dirOf 1 a₀ b₀) hρ)
    exact hev1.and hev2
  obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhds_iff.mp hmix
  have hgoodτ : ∀ τ : ℝ, |τ - 1| < δ → HeightGood ψ (dirOf τ a₀ b₀) := by
    intro τ hτ
    exact (hδ (Metric.mem_ball.mpr (by rwa [Real.dist_eq]))).1
  have hcloseτ : ∀ τ : ℝ, |τ - 1| < δ → ‖dirOf τ a₀ b₀ - n‖ < ρ := by
    intro τ hτ
    exact (hδ (Metric.mem_ball.mpr (by rwa [Real.dist_eq]))).2
  -- ## 3'. the window of half-widths is the prescribed interval `(A, B)`
  -- ## 4. the fundamental compact set and the null set of chart values
  set Kc : Set (ℝ × ℝ) := (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi)) ∩
    {p : ℝ × ℝ | Work.BoxShrink.Pinch.par ψ p ∈ closure (Submission.PBox s c σ)} with hKcdef
  have hKc : IsCompact Kc := by
    rw [hKcdef]
    exact (isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_closure.preimage (Work.BoxShrink.Pinch.par_continuous ψ))
  have hKN : ∀ N : ℕ, IsCompact (Kc ∩ {p : ℝ × ℝ | ((N : ℝ) + 1)⁻¹ ≤ |betaV ψ v b₀ p|}) := by
    intro N
    refine hKc.inter_right ?_
    exact isClosed_le continuous_const (continuous_abs.comp (contDiff_betaV ψ v b₀).continuous)
  have hNull : ∀ N : ℕ, MeasureTheory.volume {y : ℝ × ℝ |
      (((bandChart ψ v a₀ b₀) ⁻¹' {y}) ∩
        (Kc ∩ {p : ℝ × ℝ | ((N : ℝ) + 1)⁻¹ ≤ |betaV ψ v b₀ p|})).Infinite} = 0 := by
    intro N
    refine chartSard_null ψ v a₀ b₀ (hKN N) ?_
    intro p hp
    have h1 : (0 : ℝ) < ((N : ℝ) + 1)⁻¹ := by positivity
    exact abs_pos.mp (lt_of_lt_of_le h1 hp.2)
  set Nbad : Set (ℝ × ℝ) := ⋃ N : ℕ, {y : ℝ × ℝ |
      (((bandChart ψ v a₀ b₀) ⁻¹' {y}) ∩
        (Kc ∩ {p : ℝ × ℝ | ((N : ℝ) + 1)⁻¹ ≤ |betaV ψ v b₀ p|})).Infinite} with hNbaddef
  have hNbad0 : MeasureTheory.volume Nbad = 0 := by
    rw [hNbaddef]
    exact MeasureTheory.measure_iUnion_null hNull
  -- ## 5. the critical values of the height in the direction `v`
  set CV : Set ℝ := {y : ℝ | ∃ p : ℝ × ℝ, heightV ψ v p = y ∧ fderiv ℝ (heightV ψ v) p = 0}
    with hCVdef
  have hCV0 : MeasureTheory.volume CV = 0 := by
    rw [hCVdef]
    refine Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic
      (contDiff_heightV ψ v) ?_ ?_
    · intro p
      show heightV ψ v (p.1 + 2 * Real.pi, p.2) = heightV ψ v p
      simp only [heightV]
      rw [par_add_two_pi_left ψ p]
    · intro p
      show heightV ψ v (p.1, p.2 + 2 * Real.pi) = heightV ψ v p
      simp only [heightV]
      rw [par_add_two_pi_right ψ p]
  -- ## 6. the avoidance
  -- ## 5'. the parameters `τ` for which `dirOf τ a₀ b₀` kills a coordinate direction
  have hvne : ∀ k : Fin 3, inner ℝ v (EuclideanSpace.single k (1 : ℝ)) ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ : ∃ i : Fin 3, σ i = k := ⟨σ.symm k, σ.apply_symm_apply k⟩
    rw [← hi]
    exact hvax i
  set T : Set ℝ := {τ : ℝ | ∃ i : Fin 3,
      inner ℝ (dirOf τ a₀ b₀) (EuclideanSpace.single (σ i) (1 : ℝ)) = 0} with hTdef
  have hTfin : T.Finite := by
    rw [hTdef]
    exact finite_bad_tau σ hv1 ha hb hab hva hvb hvne
  have hT0 : MeasureTheory.volume T = 0 := hTfin.measure_zero MeasureTheory.volume
  have hTv0 : MeasureTheory.volume ((Set.univ : Set ℝ) ×ˢ T) = 0 := by
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, hT0, mul_zero]
  have hSnull : MeasureTheory.volume (Nbad ∪ Set.univ ×ˢ T) = 0 :=
    MeasureTheory.measure_union_null hNbad0 hTv0
  -- ## 6. the avoidance
  obtain ⟨h, τ, hh1, hh2, hτ1, hτ2, hnoA, hnoB, hnoF1', hnoF2'⟩ :=
    exists_window_avoiding hSnull hCV0 (a := inner ℝ v c + u) (hmin := A) (hmax := B)
      (tmin := 1 - δ) (tmax := 1 + δ) hAB (by linarith)
  have hnoF1 : (inner ℝ v c + u + h, τ) ∉ Nbad := fun hc => hnoF1' (Or.inl hc)
  have hnoF2 : (inner ℝ v c + u - h, τ) ∉ Nbad := fun hc => hnoF2' (Or.inl hc)
  have hτT : τ ∉ T := fun hc => hnoF1' (Or.inr ⟨trivial, hc⟩)
  set nf : R3 := dirOf τ a₀ b₀ with hnfdef
  have hnf1 : ‖nf‖ = 1 := norm_dirOf ha hb hab τ
  have hvnf : inner ℝ v nf = 0 := inner_v_dirOf hva hvb τ
  have hgoodf : HeightGood ψ nf := hgoodτ τ (by rw [abs_lt]; exact ⟨by linarith, by linarith⟩)
  have hclosen : ‖nf - n‖ < ρ := by
    rw [hnfdef]
    exact hcloseτ τ (by rw [abs_lt]; exact ⟨by linarith, by linarith⟩)
  -- ## 8. regularity at the two face levels
  have hregA : ∀ p : ℝ × ℝ, p ∈ Kc → heightV ψ v p = inner ℝ v c + u + h →
      fderiv ℝ (heightV ψ v) p ≠ 0 := by
    intro p _ hval hd
    exact hnoA ⟨p, hval, hd⟩
  have hregB : ∀ p : ℝ × ℝ, p ∈ Kc → heightV ψ v p = inner ℝ v c + u - h →
      fderiv ℝ (heightV ψ v) p ≠ 0 := by
    intro p _ hval hd
    exact hnoB ⟨p, hval, hd⟩
  -- ## 9. the finiteness of the bad values
  have hfib1 := chartFibre_finite ψ v a₀ b₀ hv1 ha hb hab hva hvb hKc
    (y := (inner ℝ v c + u + h, τ)) hnoF1 hregA
  have hfib2 := chartFibre_finite ψ v a₀ b₀ hv1 ha hb hab hva hvb hKc
    (y := (inner ℝ v c + u - h, τ)) hnoF2 hregB
  have hbadfin : ({y : ℝ | ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ ∧
      |heightV ψ v p - (inner ℝ v c + u)| = h ∧
      inner ℝ (Work.Drive.Generic.crossE v nf)
        (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) = 0 ∧
      heightIn ψ nf p = y}).Finite := by
    refine Set.Finite.subset ((hfib1.image (heightIn ψ nf)).union (hfib2.image (heightIn ψ nf))) ?_
    rintro y ⟨p, hpbox, hface, hcross, rfl⟩
    -- the fundamental representative of `p`
    obtain ⟨p₀, hp₀box, hp₀par, hp₀fd⟩ := fundamentalDomain_reduction ψ p
    have hp₀K : p₀ ∈ Kc := by
      rw [hKcdef]
      refine ⟨hp₀box, ?_⟩
      show Work.BoxShrink.Pinch.par ψ p₀ ∈ closure (Submission.PBox s c σ)
      rw [hp₀par]
      exact subset_closure hpbox
    have hnorm : Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p₀
        = Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p := by
      simp only [Work.Drive.Generic.normal, Work.Drive.Generic.d1, Work.Drive.Generic.d2]
      rw [hp₀fd]
    have hα : alphaV ψ v a₀ p₀ = alphaV ψ v a₀ p := by
      simp only [alphaV, projVv, projV, hnorm, hp₀fd]
    have hβ : betaV ψ v b₀ p₀ = betaV ψ v b₀ p := by
      simp only [betaV, projVv, projV, hnorm, hp₀fd]
    have hf0 : heightV ψ v p₀ = heightV ψ v p := by simp only [heightV, hp₀par]
    -- the projective coordinate is `τ`
    have hproj : projV (Work.BoxShrink.Pinch.par ψ) v p ≠ 0 := by
      intro h0
      have hd : fderiv ℝ (heightV ψ v) p = 0 := by
        have h := (fderiv_par_height_eq_zero_iff_projV ψ (v := v) hv1 p).mpr h0
        change fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p = 0
        exact h
      have habs : heightV ψ v p = inner ℝ v c + u + h ∨
          heightV ψ v p = inner ℝ v c + u - h := by
        have hlt : 0 < h := lt_trans hA hh1
        have := hface
        rw [abs_eq hlt.le] at this
        rcases this with h' | h'
        · left; linarith [h']
        · right; linarith [h']
      rcases habs with h' | h'
      · exact hnoA ⟨p, h'.symm ▸ rfl, hd⟩
      · exact hnoB ⟨p, h'.symm ▸ rfl, hd⟩
    have hbad := badPoint_chart ψ hv1 ha hb hab hva hvb (τ := τ) (p := p)
      (by simpa only [← hnfdef] using hcross) hproj
    have hratio : alphaV ψ v a₀ p / betaV ψ v b₀ p = τ := hbad.1
    have hb0' : betaV ψ v b₀ p ≠ 0 := hbad.2
    have hstep : ∀ z : ℝ, heightV ψ v p = z →
        bandChart ψ v a₀ b₀ p₀ = (z, τ) := by
      intro z hz
      show (heightV ψ v p₀, alphaV ψ v a₀ p₀ / betaV ψ v b₀ p₀) = (z, τ)
      rw [Prod.ext_iff]
      exact ⟨by rw [hf0, hz], by rw [hα, hβ, hratio]⟩
    have habs : heightV ψ v p = inner ℝ v c + u + h ∨
        heightV ψ v p = inner ℝ v c + u - h := by
      have hlt : 0 < h := lt_trans hA hh1
      have := hface
      rw [abs_eq hlt.le] at this
      rcases this with h' | h'
      · left; linarith [h']
      · right; linarith [h']
    rcases habs with h' | h'
    · refine Set.mem_union_left _ ?_
      have hmem : p₀ ∈ ((bandChart ψ v a₀ b₀) ⁻¹' {(inner ℝ v c + u + h, τ)}) ∩ Kc
          ∩ chartDomain ψ v b₀ := ⟨⟨hstep _ h', hp₀K⟩, by
            show betaV ψ v b₀ p₀ ≠ 0
            rw [hβ]; exact hb0'⟩
      rw [show heightIn ψ nf p = heightIn ψ nf p₀ from by
        show inner ℝ nf (Work.BoxShrink.Pinch.par ψ p)
          = inner ℝ nf (Work.BoxShrink.Pinch.par ψ p₀)
        rw [hp₀par]]
      exact Set.mem_image_of_mem _ hmem
    · refine Set.mem_union_right _ ?_
      have hmem : p₀ ∈ ((bandChart ψ v a₀ b₀) ⁻¹' {(inner ℝ v c + u - h, τ)}) ∩ Kc
          ∩ chartDomain ψ v b₀ := ⟨⟨hstep _ h', hp₀K⟩, by
            show betaV ψ v b₀ p₀ ≠ 0
            rw [hβ]; exact hb0'⟩
      rw [show heightIn ψ nf p = heightIn ψ nf p₀ from by
        show inner ℝ nf (Work.BoxShrink.Pinch.par ψ p)
          = inner ℝ nf (Work.BoxShrink.Pinch.par ψ p₀)
        rw [hp₀par]]
      exact Set.mem_image_of_mem _ hmem
  -- ## 10. the exceptional set
  have hcritfin : ({p : ℝ × ℝ | fderiv ℝ (heightIn ψ nf) p = 0} ∩
      (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi))).Finite :=
    Work.Drive.EpsForm.finite_critSet_box (heightIn_contDiff_two ψ nf) hgoodf.1
  -- ## 11. the four data conditions
  have hMorse : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf)) p = 0 →
      Function.Injective
        (fderiv ℝ (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf))) p) := by
    intro p _ hcrit
    have hcrit' : fderiv ℝ (heightIn ψ nf) p = 0 := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hcrit
    have h := hgoodf.1 p hcrit'
    rwa [Work.Drive.EpsForm.sweepHeight_innerSL]
  have hdistinct : ∀ p p' : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      Work.BoxShrink.Pinch.par ψ p' ∈ Submission.PBox s c σ →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf)) p = 0 →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf)) p' = 0 →
      (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf)) p
        = (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf)) p' →
      Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ p' := by
    intro p p' _ _ hcrit hcrit' hval
    have h1 : fderiv ℝ (heightIn ψ nf) p = 0 := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hcrit
    have h2 : fderiv ℝ (heightIn ψ nf) p' = 0 := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hcrit'
    have h3 : heightIn ψ nf p = heightIn ψ nf p' := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hval
    exact hgoodf.2 p p' h1 h2 h3
  have hcritMem : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf)) p = 0 →
      (innerSL ℝ) nf (Work.BoxShrink.Pinch.par ψ p) ∈
        hcritfin.toFinset.image (heightIn ψ nf) ∪ hbadfin.toFinset := by
    intro p hpbox hcrit
    have hcrit' : fderiv ℝ (heightIn ψ nf) p = 0 := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hcrit
    obtain ⟨p₀, hp₀box, hp₀crit, hp₀par⟩ :=
      Work.Drive.EpsForm.exists_fundamental_of_crit ψ (innerSL ℝ nf) hcrit
    have hp₀crit' : fderiv ℝ (heightIn ψ nf) p₀ = 0 := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hp₀crit
    have hmem : p₀ ∈ hcritfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨hp₀crit', hp₀box⟩
    have hval : heightIn ψ nf p₀ ∈ hcritfin.toFinset.image (heightIn ψ nf) :=
      Finset.mem_image.mpr ⟨p₀, hmem, rfl⟩
    exact Finset.mem_union_left _ (by simpa only [innerSL_apply_apply, ← hp₀par] using hval)
  have hface : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| = h →
      inner ℝ (Work.Drive.Generic.crossE v nf)
        (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) = 0 →
      (innerSL ℝ) nf (Work.BoxShrink.Pinch.par ψ p) ∈
        hcritfin.toFinset.image (heightIn ψ nf) ∪ hbadfin.toFinset := by
    intro p hpbox hfacept hcross
    refine Finset.mem_union_right _ ?_
    rw [hbadfin.mem_toFinset]
    exact ⟨p, hpbox, hfacept, hcross, rfl⟩

  have hfaceReg : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ Submission.PBox s c σ →
      |inner ℝ v z - (inner ℝ v c + u)| = h →
      ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 := by
    intro z hzcarrier hzbox hzlevel
    rw [Work.BoxShrink.Pinch.carrier_eq_range] at hzcarrier
    obtain ⟨p, hp⟩ := hzcarrier
    obtain ⟨p₀, hp₀mem, hp₀par, _⟩ := fundamentalDomain_reduction ψ p
    have hp₀K : p₀ ∈ Kc := by
      rw [hKcdef]
      refine ⟨hp₀mem, ?_⟩
      show Work.BoxShrink.Pinch.par ψ p₀ ∈ closure (Submission.PBox s c σ)
      rw [hp₀par, hp]
      exact subset_closure hzbox
    have hzlevel' : |heightV ψ v p₀ - (inner ℝ v c + u)| = h := by
      simp only [heightV]
      rw [hp₀par, hp]
      exact hzlevel
    have habs : heightV ψ v p₀ = inner ℝ v c + u + h ∨
        heightV ψ v p₀ = inner ℝ v c + u - h := by
      have hlt : 0 < h := lt_trans hA hh1
      have h := hzlevel'
      rw [abs_eq hlt.le] at h
      rcases h with h' | h'
      · left; linarith
      · right; linarith
    refine ⟨p₀, by rw [hp₀par, hp], ?_⟩
    rcases habs with h' | h'
    · exact hregA p₀ hp₀K h'
    · exact hregB p₀ hp₀K h'
  refine ⟨h, nf, hcritfin.toFinset.image (heightIn ψ nf) ∪ hbadfin.toFinset,
    hh1, hh2, ?_, hclosen, hnf1, hvnf, ?_, ?_, hfaceReg⟩
  · have h3 : h < boxWidth s σ v - |u| := lt_of_lt_of_le hh2 hB
    linarith
  · intro i h0
    exact hτT ⟨i, by rwa [innerSL_apply_apply, hnfdef] at h0⟩
  · exact Work.Drive.Mono.Band.tiltedGenericity_of_data ψ s c σ u v nf h
      (hcritfin.toFinset.image (heightIn ψ nf) ∪ hbadfin.toFinset)
      hv1 hnf1 hvnf hMorse hdistinct hcritMem hface


end

end Work.Drive.Mono
