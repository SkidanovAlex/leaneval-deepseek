import Mathlib
import Submission.Work.RPB.B5.kappaSmallAux

namespace Work.RPB.B5

/-- For `σ ∈ [0,δ]` the target circle `ktarg δ k σ` (whose phase offset `kphc` has vanished) is
`√2·δ`-close to the reference family `kGam CI 0 = √2 • CI.c 0`, both in value and in `t`-derivative.
Both are `const · e^{i t}` with constants `krd σ = √(2+2σ)` and `√2` respectively, and
`|krd σ - √2| ≤ √2·σ ≤ √2·δ`. -/
private theorem ktarg_close_kGam_aux (CI : Work.RPV.CurveIsotopy) (δ : ℝ) (k : ℤ)
    (hδ : 0 < δ) :
    ∀ σ ∈ Set.Icc (0 : ℝ) δ, ∀ t : ℝ,
      ‖ktarg δ k σ t - kGam CI 0 t‖ ≤ Real.sqrt 2 * δ ∧
      ‖deriv (fun s : ℝ => ktarg δ k σ s) t
        - deriv (fun s : ℝ => kGam CI 0 s) t‖ ≤ Real.sqrt 2 * δ := by
  intro σ hσ t
  have hσ0 : 0 ≤ σ := hσ.1
  have hσδ : σ ≤ δ := hσ.2
  have hkdr : |krd σ - Real.sqrt 2| ≤ Real.sqrt 2 * δ :=
    le_trans (abs_krd_sub_sqrt_two_le hσ0)
      (mul_le_mul_of_nonneg_left hσδ (Real.sqrt_nonneg 2))
  have he : HasDerivAt (fun s : ℝ => Complex.exp (↑s * Complex.I))
      (Complex.exp (↑t * Complex.I) * Complex.I) t := by
    have hlin : HasDerivAt (fun s : ℝ => (↑s : ℂ) * Complex.I) Complex.I t := by
      have h : HasDerivAt (fun s : ℝ => (↑s : ℂ)) (1 : ℂ) t := Complex.ofRealCLM.hasDerivAt
      simpa using h.mul_const Complex.I
    have h := (Complex.hasDerivAt_exp (↑t * Complex.I)).comp t hlin
    simpa only [Function.comp_def] using h
  have hderiv : ∀ c : ℂ, deriv (fun s : ℝ => c * Complex.exp (↑s * Complex.I)) t
      = c * (Complex.exp (↑t * Complex.I) * Complex.I) := by
    intro c
    simpa only [Function.comp_def, mul_one] using (he.const_mul c).deriv
  constructor
  · rw [ktarg_of_le hδ k hσδ, kGam_apply, CI.start]
    have h1 : (krd σ : ℂ) * Complex.exp (↑t * Complex.I)
        - (Real.sqrt 2 : ℂ) * Complex.exp (↑t * Complex.I)
        = ((krd σ - Real.sqrt 2 : ℝ) : ℂ) * Complex.exp (↑t * Complex.I) := by
      rw [← sub_mul, ← Complex.ofReal_sub]
    rw [h1, Complex.norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]
    exact hkdr
  · have hTf : (fun s : ℝ => ktarg δ k σ s)
        = fun s : ℝ => (krd σ : ℂ) * Complex.exp (↑s * Complex.I) := by
      funext s; exact ktarg_of_le hδ k hσδ
    have hGf : (fun s : ℝ => kGam CI 0 s)
        = fun s : ℝ => (Real.sqrt 2 : ℂ) * Complex.exp (↑s * Complex.I) := by
      funext s; rw [kGam_apply, CI.start]
    rw [hTf, hGf, hderiv (krd σ : ℂ), hderiv (Real.sqrt 2 : ℂ)]
    have h1 : (krd σ : ℂ) * (Complex.exp (↑t * Complex.I) * Complex.I)
        - (Real.sqrt 2 : ℂ) * (Complex.exp (↑t * Complex.I) * Complex.I)
        = ((krd σ - Real.sqrt 2 : ℝ) : ℂ) * (Complex.exp (↑t * Complex.I) * Complex.I) := by
      rw [← sub_mul, ← Complex.ofReal_sub]
    rw [h1, Complex.norm_mul, Complex.norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I,
      one_mul, mul_one, Complex.norm_real]
    exact hkdr

theorem kshape_near_close (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) (δ A : ℝ) (k : ℤ) (hδ : 0 < δ) (hA : 0 < A)
    (hδA : Real.sqrt 2 * δ ≤ A / 8)
    (hchart : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, |σ| ≤ δ → ∀ t : ℝ,
      ‖Work.RPV.uproj (W τ t (ρh τ t σ)) - (Real.sqrt 2 : ℂ) * CI.c τ t‖ < A / 8 ∧
      ‖deriv (fun u : ℝ => Work.RPV.uproj (W τ u (ρh τ u σ))) t
        - deriv (fun u : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ u) t‖ < A / 8)
    (hslice : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, |σ| ≤ δ →
      ContDiff ℝ 1 (fun t : ℝ => Work.RPV.uproj (W τ t (ρh τ t σ)))) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ ∈ Set.Icc (0 : ℝ) δ, ∀ t : ℝ,
      DifferentiableAt ℝ (fun s : ℝ => Work.RPB.B5.knear CI W ρh δ k τ σ s) t ∧
      ‖Work.RPB.B5.knear CI W ρh δ k τ σ t - (Real.sqrt 2 : ℂ) * CI.c τ t‖ ≤ 3 * A / 8 ∧
      ‖deriv (fun s : ℝ => Work.RPB.B5.knear CI W ρh δ k τ σ s) t
        - deriv (fun s : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ s) t‖ ≤ 3 * A / 8 := by
  intro τ hτ σ hσ t
  have hσ0 : 0 ≤ σ := hσ.1
  have hσδ : σ ≤ δ := hσ.2
  have hx1 : xfade δ σ = 1 := xfade_one hδ hσ0
  have hcl : |kclamp δ σ| ≤ δ := abs_kclamp_le hδ
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  -- the three pieces of `knear`
  set N : ℝ → ℂ := fun s => Work.RPV.uproj (W τ s (ρh τ s (kclamp δ σ))) with hNdef
  set N0 : ℝ → ℂ := fun s => Work.RPV.uproj (W 0 s (ρh 0 s (kclamp δ σ))) with hN0def
  set T : ℝ → ℂ := fun s => ktarg δ k σ s with hTdef
  set M : ℝ → ℂ := fun s => kbbmp δ τ * (T s - N0 s) with hMdef
  -- differentiability of the pieces
  have hNd : DifferentiableAt ℝ N t := by
    have h : ContDiff ℝ 1 N := by rw [hNdef]; exact hslice τ hτ (kclamp δ σ) hcl
    exact (h.differentiable (by norm_num)).differentiableAt
  have hN0d : DifferentiableAt ℝ N0 t := by
    have h : ContDiff ℝ 1 N0 := by rw [hN0def]; exact hslice 0 h0mem (kclamp δ σ) hcl
    exact (h.differentiable (by norm_num)).differentiableAt
  have hTd : DifferentiableAt ℝ T t := by
    have h : T = fun s : ℝ => (krd σ : ℂ) * Complex.exp (↑s * Complex.I) := by
      funext s
      simp only [hTdef]
      exact ktarg_of_le hδ k hσδ
    rw [h]; fun_prop
  have hMd : DifferentiableAt ℝ M t := by
    rw [hMdef]
    exact (hTd.sub hN0d).const_mul (kbbmp δ τ)
  -- the pointwise shape identity
  have hpoint : ∀ s : ℝ, knear CI W ρh δ k τ σ s = N s + M s := by
    intro s
    simp only [knear, hx1, hNdef, hN0def, hTdef, hMdef, Complex.ofReal_one, mul_one]
  have hfun : (fun s : ℝ => knear CI W ρh δ k τ σ s) = N + M := by
    funext s; exact hpoint s
  -- chart closeness (the hypothesis, transported to `N`, `N0`)
  have hNv : ‖N t - (Real.sqrt 2 : ℂ) * CI.c τ t‖ < A / 8 := by
    rw [hNdef]; exact (hchart τ hτ (kclamp δ σ) hcl t).1
  have hNdv : ‖deriv N t - deriv (fun u : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ u) t‖ < A / 8 := by
    rw [hNdef]; exact (hchart τ hτ (kclamp δ σ) hcl t).2
  have hN0v : ‖N0 t - (Real.sqrt 2 : ℂ) * CI.c 0 t‖ < A / 8 := by
    rw [hN0def]; exact (hchart 0 h0mem (kclamp δ σ) hcl t).1
  have hN0dv : ‖deriv N0 t - deriv (fun u : ℝ => (Real.sqrt 2 : ℂ) * CI.c 0 u) t‖ < A / 8 := by
    rw [hN0def]; exact (hchart 0 h0mem (kclamp δ σ) hcl t).2
  -- target-circle closeness
  have hTv0 : ‖ktarg δ k σ t - kGam CI 0 t‖ ≤ Real.sqrt 2 * δ :=
    (ktarg_close_kGam_aux CI δ k hδ σ hσ t).1
  have hTdv0 : ‖deriv (fun s : ℝ => ktarg δ k σ s) t
      - deriv (fun s : ℝ => kGam CI 0 s) t‖ ≤ Real.sqrt 2 * δ :=
    (ktarg_close_kGam_aux CI δ k hδ σ hσ t).2
  have hTv : ‖T t - (Real.sqrt 2 : ℂ) * CI.c 0 t‖ ≤ Real.sqrt 2 * δ := by
    simpa only [hTdef, kGam_apply] using hTv0
  have hTdv : ‖deriv T t - deriv (fun u : ℝ => (Real.sqrt 2 : ℂ) * CI.c 0 u) t‖
      ≤ Real.sqrt 2 * δ := by
    simpa only [hTdef, kGam_apply] using hTdv0
  -- the coefficient bound and the two "difference estimates"
  have hcabs : ‖((kbbmp δ τ : ℝ) : ℂ)‖ ≤ 1 := by
    have h1 : ‖((kbbmp δ τ : ℝ) : ℂ)‖ = |kbbmp δ τ| := RCLike.norm_ofReal _
    rw [h1, abs_le]
    exact ⟨by linarith [kbbmp_nonneg δ τ], kbbmp_le_one δ τ⟩
  have hT0 : ‖T t - N0 t‖ ≤ A / 4 := by
    have hsplit : T t - N0 t = (T t - (Real.sqrt 2 : ℂ) * CI.c 0 t)
        + ((Real.sqrt 2 : ℂ) * CI.c 0 t - N0 t) := by ring
    rw [hsplit]
    calc ‖(T t - (Real.sqrt 2 : ℂ) * CI.c 0 t) + ((Real.sqrt 2 : ℂ) * CI.c 0 t - N0 t)‖
        ≤ ‖T t - (Real.sqrt 2 : ℂ) * CI.c 0 t‖
            + ‖(Real.sqrt 2 : ℂ) * CI.c 0 t - N0 t‖ := norm_add_le _ _
      _ ≤ A / 8 + A / 8 := by
          apply add_le_add
          · exact le_trans hTv hδA
          · rw [norm_sub_rev]; exact le_of_lt hN0v
      _ = A / 4 := by ring
  have hT0d : ‖deriv T t - deriv N0 t‖ ≤ A / 4 := by
    have hsplit : deriv T t - deriv N0 t
        = (deriv T t - deriv (fun u : ℝ => (Real.sqrt 2 : ℂ) * CI.c 0 u) t)
          + (deriv (fun u : ℝ => (Real.sqrt 2 : ℂ) * CI.c 0 u) t - deriv N0 t) := by ring
    rw [hsplit]
    calc ‖(deriv T t - deriv (fun u : ℝ => (Real.sqrt 2 : ℂ) * CI.c 0 u) t)
            + (deriv (fun u : ℝ => (Real.sqrt 2 : ℂ) * CI.c 0 u) t - deriv N0 t)‖
        ≤ ‖deriv T t - deriv (fun u : ℝ => (Real.sqrt 2 : ℂ) * CI.c 0 u) t‖
            + ‖deriv (fun u : ℝ => (Real.sqrt 2 : ℂ) * CI.c 0 u) t - deriv N0 t‖ :=
          norm_add_le _ _
      _ ≤ A / 8 + A / 8 := by
          apply add_le_add
          · exact le_trans hTdv hδA
          · rw [norm_sub_rev]; exact le_of_lt hN0dv
      _ = A / 4 := by ring
  have hMnv : ‖M t‖ = ‖((kbbmp δ τ : ℝ) : ℂ)‖ * ‖T t - N0 t‖ := by
    rw [hMdef]; simp only [norm_mul]
  have hMderiv : deriv M t = kbbmp δ τ * (deriv T t - deriv N0 t) := by
    have h : HasDerivAt (fun s : ℝ => (kbbmp δ τ : ℂ) * (T s - N0 s))
        ((kbbmp δ τ : ℂ) * (deriv T t - deriv N0 t)) t :=
      (hTd.hasDerivAt.sub hN0d.hasDerivAt).const_mul ((kbbmp δ τ : ℝ) : ℂ)
    rw [hMdef]
    exact h.deriv
  have hderiv_knear : deriv (fun s : ℝ => knear CI W ρh δ k τ σ s) t = deriv N t + deriv M t := by
    rw [hfun, deriv_add hNd hMd]
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]; exact hNd.add hMd
  · rw [hpoint t]
    have hsplit : N t + M t - (Real.sqrt 2 : ℂ) * CI.c τ t
        = (N t - (Real.sqrt 2 : ℂ) * CI.c τ t) + M t := by ring
    rw [hsplit]
    calc ‖(N t - (Real.sqrt 2 : ℂ) * CI.c τ t) + M t‖
        ≤ ‖N t - (Real.sqrt 2 : ℂ) * CI.c τ t‖ + ‖M t‖ := norm_add_le _ _
      _ = ‖N t - (Real.sqrt 2 : ℂ) * CI.c τ t‖
            + ‖((kbbmp δ τ : ℝ) : ℂ)‖ * ‖T t - N0 t‖ := by rw [hMnv]
      _ ≤ A / 8 + 1 * (A / 4) :=
          add_le_add (le_of_lt hNv) (mul_le_mul hcabs hT0 (norm_nonneg _) (by norm_num))
      _ = 3 * A / 8 := by ring
  · rw [hderiv_knear, hMderiv]
    have hsplit : deriv N t + kbbmp δ τ * (deriv T t - deriv N0 t)
          - deriv (fun s : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ s) t
        = (deriv N t - deriv (fun s : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ s) t)
          + kbbmp δ τ * (deriv T t - deriv N0 t) := by ring
    rw [hsplit]
    calc ‖(deriv N t - deriv (fun s : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ s) t)
            + kbbmp δ τ * (deriv T t - deriv N0 t)‖
        ≤ ‖deriv N t - deriv (fun s : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ s) t‖
            + ‖kbbmp δ τ * (deriv T t - deriv N0 t)‖ := norm_add_le _ _
      _ = ‖deriv N t - deriv (fun s : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ s) t‖
            + ‖((kbbmp δ τ : ℝ) : ℂ)‖ * ‖deriv T t - deriv N0 t‖ := by rw [norm_mul]
      _ ≤ A / 8 + 1 * (A / 4) :=
          add_le_add (le_of_lt hNdv) (mul_le_mul hcabs hT0d (norm_nonneg _) (by norm_num))
      _ = 3 * A / 8 := by ring

end Work.RPB.B5
