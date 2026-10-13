import Mathlib
import Submission.Work.WilC4aRW.Defs

/-!
  Area `WilC4aRW`, lemma `prep_conj`: a classical Weierstrass preparation is stable under
  composing with the coordinatewise complex conjugation.

  The proof needs one genuine analytic ingredient: if `F` is `ℂ`-analytic at `0`, then so is
  `z ↦ star (F (conjVec z))` (Schwarz reflection at the level of power series).  We build that
  here from scratch (`conj_analytic_pi`, `conj_analytic_ambient`), since Mathlib has no lemma
  that transports analyticity across an antilinear conjugation.
-/

namespace Work.WilC4aRW.WPT

open ClassicalComplexWPT Work.WilC4aRW
open scoped Topology BigOperators ComplexConjugate

noncomputable section

/-! ## Conjugation helpers on `Fin k → ℂ` -/

theorem conjVec_eq_star {k : ℕ} (y : Fin k → ℂ) : conjVec y = star y := by
  ext i; simp [conjVec]

theorem norm_conjVec {k : ℕ} (y : Fin k → ℂ) : ‖conjVec y‖ = ‖y‖ := by
  rw [conjVec_eq_star, norm_star]

theorem isometry_conjVec {k : ℕ} : Isometry (conjVec : (Fin k → ℂ) → (Fin k → ℂ)) := by
  rw [isometry_iff_dist_eq]
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have h : conjVec x - conjVec y = star (x - y) := by ext i; simp [conjVec]
  rw [h, norm_star]

/-- `conjVec` distributes over `Function.update`. -/
theorem conjVec_update {k N : ℕ} (m : Fin N → (Fin k → ℂ)) (i : Fin N) (x : Fin k → ℂ) :
    (fun j => conjVec (Function.update m i x j)) =
      Function.update (fun j => conjVec (m j)) i (conjVec x) := by
  ext j
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [Function.update_of_ne hj]

/-! ## Analyticity of `star ∘ F ∘ conjVec`

For a ℂ-analytic `F : (Fin k → ℂ) → ℂ` we build the conjugated power series.  If
`p` is the formal power series of `F`, then the `n`-th coefficient of `star ∘ F ∘ conjVec`
is the continuous multilinear map `v ↦ star (p n (conjVec v))`; conjugation is an isometry,
so this series has the same radius of convergence and converges to the wanted function. -/

theorem conj_analytic_pi {k : ℕ} {F : (Fin k → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0) :
    AnalyticAt ℂ (fun z : Fin k → ℂ => star (F (conjVec z))) 0 := by
  obtain ⟨p, r, hr⟩ := hF
  have hupd : ∀ (N : ℕ) (m : Fin N → (Fin k → ℂ)) (i : Fin N) (x : Fin k → ℂ),
      (fun j => conjVec (Function.update m i x j)) =
        Function.update (fun j => conjVec (m j)) i (conjVec x) :=
    fun N m i x => conjVec_update m i x
  let q : FormalMultilinearSeries ℂ (Fin k → ℂ) ℂ := fun N =>
    (MultilinearMap.mk' (fun m : Fin N → (Fin k → ℂ) => star (p N (fun j => conjVec (m j))))
        (fun m i x y => by
          rw [hupd N m i (x + y),
            show conjVec (x + y) = conjVec x + conjVec y from by ext j; simp [conjVec],
            hupd N m i x, hupd N m i y, ContinuousMultilinearMap.map_update_add]
          simp only [Complex.star_def, map_add])
        (fun m i c x => by
          rw [hupd N m i (c • x),
            show conjVec (c • x) = star c • conjVec x from by ext j; simp [conjVec],
            hupd N m i x, ContinuousMultilinearMap.map_update_smul]
          simp)).mkContinuous ‖p N‖ (by
            intro m
            change ‖star (p N (fun j => conjVec (m j)))‖ ≤ ‖p N‖ * ∏ j, ‖m j‖
            rw [norm_star]
            calc ‖p N (fun j => conjVec (m j))‖
                ≤ ‖p N‖ * ∏ j, ‖conjVec (m j)‖ := ContinuousMultilinearMap.le_opNorm _ _
              _ = ‖p N‖ * ∏ j, ‖m j‖ := by simp [norm_conjVec])
  have hq_apply : ∀ (N : ℕ) (m : Fin N → (Fin k → ℂ)),
      q N m = star (p N (fun j => conjVec (m j))) := fun N m => rfl
  have hqnorm : ∀ N, ‖q N‖ ≤ ‖p N‖ := fun N =>
    MultilinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  refine ⟨q, r, le_trans hr.r_le (FormalMultilinearSeries.radius_le_of_le hqnorm), hr.r_pos, ?_⟩
  intro y hy
  have hy' : conjVec y ∈ Metric.eball (0 : Fin k → ℂ) r := by
    rw [Metric.mem_eball] at hy ⊢
    have : edist (conjVec y) (0 : Fin k → ℂ) = edist y 0 := by
      simpa using isometry_conjVec y 0
    rwa [this]
  have hmap := (hr.hasSum hy').map (starRingEnd ℂ) Complex.continuous_conj
  simpa [hq_apply, Function.comp_def, Complex.star_def] using hmap

/-! ## The `(init, last)` projection `ℂ^{n+1} → ℂⁿ × ℂ` -/

/-- The continuous ℂ-linear projection `ℂ^{n+1} → ℂⁿ × ℂ = Ambient n`, the inverse of
`snocCLM`. -/
def psiCLM (n : ℕ) : (Fin (n+1) → ℂ) →L[ℂ] Ambient n :=
  (ContinuousLinearMap.pi fun j : Fin n =>
      (ContinuousLinearMap.proj (R := ℂ) j.castSucc : (Fin (n+1) → ℂ) →L[ℂ] ℂ)).prod
    (ContinuousLinearMap.proj (R := ℂ) (Fin.last n))

@[simp] theorem psiCLM_apply_fst (n : ℕ) (w : Fin (n+1) → ℂ) :
    (psiCLM n w).1 = fun j : Fin n => w j.castSucc := rfl

@[simp] theorem psiCLM_apply_snd (n : ℕ) (w : Fin (n+1) → ℂ) :
    (psiCLM n w).2 = w (Fin.last n) := rfl

theorem psiCLM_conjVec_snocCLM (n : ℕ) (x : Ambient n) :
    psiCLM n (conjVec (snocCLM n x)) = conjAmb x := by
  ext <;> simp [conjVec, snocCLM_apply_castSucc, snocCLM_apply_last]

/-! ## Analyticity of `star ∘ F ∘ conjAmb` -/

theorem conj_analytic_ambient {n : ℕ} {F : Ambient n → ℂ} (hF : AnalyticAt ℂ F 0) :
    AnalyticAt ℂ (fun z : Ambient n => star (F (conjAmb z))) 0 := by
  have hF' : AnalyticAt ℂ (F ∘ (psiCLM n)) 0 :=
    hF.compContinuousLinearMap (u := psiCLM n) (x := (0 : Fin (n+1) → ℂ))
  have hT' := conj_analytic_pi (k := n+1) hF'
  have hTL : AnalyticAt ℂ
      ((fun z : Fin (n+1) → ℂ => star ((F ∘ psiCLM n) (conjVec z))) ∘ (snocCLM n)) 0 := by
    have hG : AnalyticAt ℂ ((fun z : Fin (n+1) → ℂ => star ((F ∘ psiCLM n) (conjVec z))))
        (snocCLM n (0 : Ambient n)) := by simpa using hT'
    exact hG.compContinuousLinearMap (u := snocCLM n) (x := (0 : Ambient n))
  refine hTL.congr ?_
  filter_upwards with x
  simp only [Function.comp_apply]
  rw [psiCLM_conjVec_snocCLM]

/-- `conjAmb` is continuous (it is coordinatewise complex conjugation). -/
theorem continuous_conjAmb {n : ℕ} : Continuous (conjAmb : Ambient n → Ambient n) := by
  have h : (star : Ambient n → Ambient n) = conjAmb := by ext x <;> simp [conjAmb, conjVec]
  rw [← h]; exact continuous_star

/-! ## The main lemma -/

theorem prep_conj {n d : ℕ} {f : ClassicalComplexWPT.Ambient n → ℂ}
    {a : Fin d → ClassicalComplexWPT.Base n → ℂ} {u : ClassicalComplexWPT.Ambient n → ℂ}
    (hprep : ClassicalComplexWPT.IsWeierstrassPreparation f d a u) :
    ClassicalComplexWPT.IsWeierstrassPreparation
      (fun x : ClassicalComplexWPT.Ambient n => star (f (Work.WilC4aRW.conjAmb x))) d
      (fun i y => star (a i (Work.WilC4aRW.conjVec y)))
      (fun x : ClassicalComplexWPT.Ambient n => star (u (Work.WilC4aRW.conjAmb x))) := by
  obtain ⟨ha, h0, hu, hu0, hf⟩ := hprep
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact conj_analytic_pi (ha i)
  · intro i
    show star (a i (conjVec (0 : Base n))) = 0
    simp [h0 i]
  · exact conj_analytic_ambient hu
  · show star (u (conjAmb (0 : Ambient n))) ≠ 0
    rw [conjAmb_zero]
    intro h
    exact hu0 (star_eq_zero.mp h)
  · have hpoly : ∀ x : Ambient n, star (preparedPolynomial d a (conjAmb x)) =
        preparedPolynomial d (fun i y => star (a i (conjVec y))) x := fun x => by
      simp only [preparedPolynomial, conjAmb_fst, conjAmb_snd, Complex.star_def, map_add, map_sum,
        map_mul, map_pow, starRingEnd_self_apply]
    have htend : Filter.Tendsto (conjAmb : Ambient n → Ambient n) (𝓝 0) (𝓝 0) := by
      simpa [conjAmb_zero] using (continuous_conjAmb (n := n)).tendsto 0
    filter_upwards [hf.comp_tendsto htend] with x hx
    have hx' : f (conjAmb x) = u (conjAmb x) * preparedPolynomial d a (conjAmb x) := hx
    have hp2 : (starRingEnd ℂ) (preparedPolynomial d a (conjAmb x)) =
        preparedPolynomial d (fun i y => (starRingEnd ℂ) (a i (conjVec y))) x := hpoly x
    rw [hx']
    simp only [Complex.star_def, map_mul]
    rw [hp2]

end

end Work.WilC4aRW.WPT
