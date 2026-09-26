import Mathlib

/-!
# The image of a set of second-order flatness is null

Let `G : ℝ × ℝ → ℝ` be `C²` and let `A` be bounded.  If the gradient of `G` and its two
coordinate partial derivatives vanish on `A`, then the image `G '' A` is Lebesgue-null.

The hypotheses mean that at every `p ∈ A` both the first Fréchet derivative `fderiv ℝ G p` and the
full second derivative `fderiv ℝ (fderiv ℝ G) p` vanish.  Hence `G` is *second-order flat* at `A`:
for every `ε > 0` there is a uniform `δ > 0` with
`‖G q - G p‖ ≤ ε * ‖q - p‖ ^ 2` whenever `p ∈ A` and `‖q - p‖ ≤ δ`.  Covering the bounded set `A`
by `≈ (2R/ℓ)²` boxes of side `ℓ` (with `2ℓ ≤ δ`) and using flatness on each box shows that the
image is covered by intervals of total length `O(ε)`, which tends to `0`.

The proof is organised in three independent ingredients:

* `fderiv_fderiv_eq_zero_of_partial_fderivs` : the two coordinate hypotheses force the vanishing of
  the full second derivative;
* `second_order_bound_of_fderiv_fderiv_eq_zero` : second-order flatness from `DG = D²G = 0` on the
  bounded set (mean value theorem applied twice, using uniform continuity of `D²G`);
* `volume_image_null_of_uniform_second_order_bound` : such a uniform flatness bound forces the
  image to be null (explicit grid covering).
-/

namespace Work.Smooth.BoxGeneric.Sard

/-- **1-D grid covering.**  If `ℓ > 0` and `M` is a natural number with `2R ≤ M * ℓ`, then every
point of `[-R, R]` is within `ℓ / 2` of one of the grid points `-R + i * ℓ`, `i < M + 1`. -/
private lemma grid1d {R ℓ : ℝ} (hℓ : 0 < ℓ) {M : ℕ} (hM : 2 * R ≤ (M : ℝ) * ℓ) {x : ℝ}
    (hx1 : -R ≤ x) (hx2 : x ≤ R) :
    ∃ i : Fin (M + 1), |x - (-R + (i : ℝ) * ℓ)| ≤ ℓ / 2 := by
  have hxR : 0 ≤ x + R := by linarith
  have htM : (x + R) / ℓ ≤ (M : ℝ) := by rw [div_le_iff₀ hℓ]; linarith
  set t : ℝ := (x + R) / ℓ with ht
  set i : ℕ := Nat.floor (t + 1 / 2) with hi
  have hi_le : (i : ℝ) ≤ t + 1 / 2 := Nat.floor_le (by positivity)
  have hi_lt : t + 1 / 2 < (i : ℝ) + 1 := Nat.lt_floor_add_one (t + 1 / 2)
  have hiM : i ≤ M := by
    have h3 : (i : ℝ) < ((M + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact Nat.lt_succ_iff.mp (by exact_mod_cast h3)
  refine ⟨⟨i, Nat.lt_succ_of_le hiM⟩, ?_⟩
  have habs : |t - (i : ℝ)| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  have hkey : x - (-R + (i : ℝ) * ℓ) = ℓ * (t - (i : ℝ)) := by rw [ht]; field_simp; ring
  rw [hkey, abs_mul, abs_of_pos hℓ]
  calc ℓ * |t - (i : ℝ)| ≤ ℓ * (1 / 2) := mul_le_mul_of_nonneg_left habs hℓ.le
    _ = ℓ / 2 := by ring

/-- **2-D grid covering.**  With `ℓ`, `M` as above, the closed ball of radius `R` in `ℝ × ℝ` is
covered by the balls of radius `ℓ` around the grid points `(-R + i ℓ, -R + j ℓ)`, `i, j < M + 1`. -/
private lemma grid2d {R ℓ : ℝ} (hℓ : 0 < ℓ) {M : ℕ} (hM : 2 * R ≤ (M : ℝ) * ℓ) {q : ℝ × ℝ}
    (hq : q ∈ Metric.closedBall (0 : ℝ × ℝ) R) :
    ∃ c : Fin (M + 1) × Fin (M + 1),
      q ∈ Metric.closedBall ((-R + (c.1 : ℝ) * ℓ, -R + (c.2 : ℝ) * ℓ)) ℓ := by
  rw [Metric.mem_closedBall, dist_zero_right] at hq
  have hq1 : |q.1| ≤ R := by
    have := norm_fst_le q; rw [Real.norm_eq_abs] at this; linarith
  have hq2 : |q.2| ≤ R := by
    have := norm_snd_le q; rw [Real.norm_eq_abs] at this; linarith
  rw [abs_le] at hq1 hq2
  obtain ⟨i, hi⟩ := grid1d hℓ hM hq1.1 hq1.2
  obtain ⟨j, hj⟩ := grid1d hℓ hM hq2.1 hq2.2
  refine ⟨(i, j), ?_⟩
  rw [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff]
  exact ⟨le_trans hi (by linarith), le_trans hj (by linarith)⟩

/-- The vanishing of the two coordinate partial derivatives of the gradient on `A` forces the full
second derivative `fderiv ℝ (fderiv ℝ G)` to vanish on `A`. -/
private lemma fderiv_fderiv_eq_zero_of_partial_fderivs {G : ℝ × ℝ → ℝ} {A : Set (ℝ × ℝ)}
    (h1 : ∀ p ∈ A, fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ G q ((1 : ℝ), 0)) p = 0)
    (h2 : ∀ p ∈ A, fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ G q ((0 : ℝ), 1)) p = 0) :
    ∀ p ∈ A, fderiv ℝ (fderiv ℝ G) p = 0 := by
  intro p hp
  -- A linear functional on `ℝ × ℝ` vanishing on the two standard basis vectors is zero.
  have basis : ∀ L : ℝ × ℝ →L[ℝ] ℝ, L ((1 : ℝ), 0) = 0 → L ((0 : ℝ), 1) = 0 → L = 0 := by
    intro L hL1 hL2
    refine ContinuousLinearMap.ext (fun w => ?_)
    rw [ContinuousLinearMap.zero_apply]
    have hw : w = w.1 • ((1 : ℝ), 0) + w.2 • ((0 : ℝ), 1) := by ext <;> simp
    rw [hw, map_add, map_smul, map_smul, hL1, hL2]
    simp
  -- The derivative of `q ↦ (fderiv ℝ G q) y` is `(fderiv ℝ (fderiv ℝ G) p)` evaluated at `y`.
  have aux : ∀ y : ℝ × ℝ, fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ G q y) p = 0 →
      ∀ v, ((fderiv ℝ (fderiv ℝ G) p) v) y = 0 := by
    intro y hy v
    by_cases hd : DifferentiableAt ℝ (fderiv ℝ G) p
    · have h := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.apply ℝ ℝ y)).comp p
        hd.hasFDerivAt
      have hcompA : HasFDerivAt (fun q : ℝ × ℝ => fderiv ℝ G q y)
          ((ContinuousLinearMap.apply ℝ ℝ y).comp (fderiv ℝ (fderiv ℝ G) p)) p :=
        h.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun q => ContinuousLinearMap.apply_apply y (fderiv ℝ G q))
      have hcomp := hcompA.fderiv
      have hzero : (ContinuousLinearMap.apply ℝ ℝ y).comp (fderiv ℝ (fderiv ℝ G) p) = 0 := by
        rw [← hcomp]; exact hy
      have hv := congrArg (fun (L : ℝ × ℝ →L[ℝ] ℝ) => L v) hzero
      simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] using hv
    · rw [fderiv_zero_of_not_differentiableAt hd]
      simp
  have hD1 := aux ((1 : ℝ), 0) (h1 p hp)
  have hD2 := aux ((0 : ℝ), 1) (h2 p hp)
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.zero_apply]
  have hw : w = w.1 • ((1 : ℝ), (0 : ℝ)) + w.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  rw [hw]
  simp only [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul, hD1 v, hD2 v,
    smul_zero, add_zero]

/-- **Second-order flatness.**  A `C²` function whose gradient and second derivative vanish on a
bounded set `A` is uniformly second-order flat on `A`. -/
private lemma second_order_bound_of_fderiv_fderiv_eq_zero {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 2 G)
    {A : Set (ℝ × ℝ)} {R : ℝ} (hR : ∀ x ∈ A, ‖x‖ ≤ R)
    (h0 : ∀ p ∈ A, fderiv ℝ G p = 0)
    (hH : ∀ p ∈ A, fderiv ℝ (fderiv ℝ G) p = 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ p ∈ A, ∀ q : ℝ × ℝ,
      ‖q - p‖ ≤ δ → ‖G q - G p‖ ≤ ε * ‖q - p‖ ^ 2 := by
  intro ε hε
  have hd1 : ContDiff ℝ 1 (fderiv ℝ G) := hG.fderiv_right (m := 1) (by norm_num)
  have hHcont : Continuous fun z => fderiv ℝ (fderiv ℝ G) z := hd1.continuous_fderiv (by norm_num)
  have huc : UniformContinuousOn (fun z : ℝ × ℝ => fderiv ℝ (fderiv ℝ G) z)
      (Metric.closedBall (0 : ℝ × ℝ) (R + 1)) :=
    (isCompact_closedBall (0 : ℝ × ℝ) (R + 1)).uniformContinuousOn_of_continuous hHcont.continuousOn
  have hδ : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Metric.closedBall (0 : ℝ × ℝ) (R + 1),
      ∀ y ∈ Metric.closedBall (0 : ℝ × ℝ) (R + 1),
      dist x y < δ → dist (fderiv ℝ (fderiv ℝ G) x) (fderiv ℝ (fderiv ℝ G) y) < ε :=
    Metric.uniformContinuousOn_iff.mp huc
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hδ ε hε
  refine ⟨min (δ₀ / 2) 1, lt_min (by linarith) one_pos, ?_⟩
  intro p hp q hpq
  have hεle : 0 ≤ ε := hε.le
  have hp_norm : ‖p‖ ≤ R := hR p hp
  have hp_ball : p ∈ Metric.closedBall (0 : ℝ × ℝ) (R + 1) := by
    rw [Metric.mem_closedBall, dist_zero_right]; linarith
  -- On the segment `[p, q]` the second derivative is bounded by `ε`.
  have hbound : ∀ z ∈ segment ℝ p q, ‖fderiv ℝ (fderiv ℝ G) z‖ ≤ ε := by
    intro z hz
    have hzp : ‖z - p‖ ≤ ‖q - p‖ := norm_sub_le_of_mem_segment hz
    have hzq : ‖z - p‖ ≤ 1 := le_trans hzp (le_trans hpq (min_le_right (δ₀ / 2) 1))
    have hzδ : ‖z - p‖ < δ₀ :=
      lt_of_le_of_lt (le_trans hzp (le_trans hpq (min_le_left (δ₀ / 2) 1))) (by linarith)
    have hzball : z ∈ Metric.closedBall (0 : ℝ × ℝ) (R + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖z‖ ≤ ‖z - p‖ + ‖p‖ := by
        calc ‖z‖ = ‖(z - p) + p‖ := by rw [sub_add_cancel z p]
          _ ≤ ‖z - p‖ + ‖p‖ := norm_add_le (z - p) p
      linarith
    have hlt := hδ₀ z hzball p hp_ball (by rw [dist_eq_norm]; exact hzδ)
    have hlt' : ‖fderiv ℝ (fderiv ℝ G) z‖ < ε := by
      rw [hH p hp] at hlt
      rwa [dist_zero_right (fderiv ℝ (fderiv ℝ G) z)] at hlt
    linarith
  -- First mean value theorem: `fderiv ℝ G` is `ε`-Lipschitz on the segment.
  have hderiv_bound : ∀ z ∈ segment ℝ p q, ‖fderiv ℝ G z - fderiv ℝ G p‖ ≤ ε * ‖z - p‖ := by
    intro z hz
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => (ContDiff.differentiable hd1 (by norm_num)).differentiableAt)
      (fun w hw => hbound w hw) (convex_segment p q) (left_mem_segment ℝ p q) hz
  -- Second mean value theorem, applied to `x ↦ G x - (fderiv ℝ G p) x`.
  let L : ℝ × ℝ →L[ℝ] ℝ := fderiv ℝ G p
  have hL0 : L = 0 := h0 p hp
  have hg_bound : ∀ z ∈ segment ℝ p q,
      ‖fderiv ℝ (fun x => G x - L x) z‖ ≤ ε * ‖q - p‖ := by
    intro z hz
    have hfd : fderiv ℝ (fun x => G x - L x) z = fderiv ℝ G z - fderiv ℝ G p := by
      have h := ((ContDiff.differentiable hG (by norm_num)).differentiableAt (x := z)).hasFDerivAt.sub
        (ContinuousLinearMap.hasFDerivAt (x := z) L)
      exact h.fderiv
    rw [hfd]
    calc ‖fderiv ℝ G z - fderiv ℝ G p‖ ≤ ε * ‖z - p‖ := hderiv_bound z hz
      _ ≤ ε * ‖q - p‖ := mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hεle
  have hfinal := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => ((ContDiff.differentiable hG (by norm_num)).differentiableAt).sub
      (ContinuousLinearMap.differentiableAt L))
    hg_bound (convex_segment p q) (left_mem_segment ℝ p q) (right_mem_segment ℝ p q)
  have hfin2 : ‖G q - G p‖ ≤ (ε * ‖q - p‖) * ‖q - p‖ := by
    have key : (G q - L q) - (G p - L p) = G q - G p := by rw [hL0]; simp
    rw [← key]
    exact hfinal
  calc ‖G q - G p‖ ≤ (ε * ‖q - p‖) * ‖q - p‖ := hfin2
    _ = ε * ‖q - p‖ ^ 2 := by ring

/-- **Null image from uniform second-order flatness.**  If `A` is contained in the closed ball of
radius `R` and `f` is uniformly second-order flat on `A`, then `f '' A` is Lebesgue-null. -/
private lemma volume_image_null_of_uniform_second_order_bound {f : ℝ × ℝ → ℝ} {A : Set (ℝ × ℝ)}
    {R : ℝ} (hRpos : 0 < R) (hR : ∀ x ∈ A, ‖x‖ ≤ R)
    (hflat : ∀ ε > 0, ∃ δ > 0, ∀ p ∈ A, ∀ q : ℝ × ℝ,
      ‖q - p‖ ≤ δ → ‖f q - f p‖ ≤ ε * ‖q - p‖ ^ 2) :
    MeasureTheory.volume (f '' A) = 0 := by
  have hmain : ∀ ε : ℝ, 0 < ε →
      MeasureTheory.volume (f '' A) ≤ ENNReal.ofReal (128 * R ^ 2 * ε) := by
    intro ε hε
    classical
    obtain ⟨δ, hδpos, hδ⟩ := hflat ε hε
    set ℓ : ℝ := min (δ / 2) R with hℓ
    have hℓpos : 0 < ℓ := by rw [hℓ]; exact lt_min (by linarith) hRpos
    have hℓR : ℓ ≤ R := by rw [hℓ]; exact min_le_right _ _
    have h2ℓδ : 2 * ℓ ≤ δ := by
      have h : ℓ ≤ δ / 2 := by rw [hℓ]; exact min_le_left _ _
      linarith
    set M : ℕ := Nat.ceil (2 * R / ℓ) with hMdef
    have hM : 2 * R ≤ (M : ℝ) * ℓ := by
      have h : 2 * R / ℓ ≤ (M : ℝ) := Nat.le_ceil _
      have h2 : (2 * R / ℓ) * ℓ = 2 * R := by field_simp
      calc 2 * R = (2 * R / ℓ) * ℓ := h2.symm
        _ ≤ (M : ℝ) * ℓ := mul_le_mul_of_nonneg_right h hℓpos.le
    set G : Fin (M + 1) × Fin (M + 1) → ℝ × ℝ :=
      fun c => (-R + (c.1 : ℝ) * ℓ, -R + (c.2 : ℝ) * ℓ) with hG
    set S : Fin (M + 1) × Fin (M + 1) → Set (ℝ × ℝ) :=
      fun c => Metric.closedBall (G c) ℓ with hS
    -- an anchor point of `A` in each grid cell
    set anchor : Fin (M + 1) × Fin (M + 1) → ℝ × ℝ :=
      fun c => if h : (S c ∩ A).Nonempty then h.choose else 0 with hanchor_def
    have hanchor : ∀ c, (S c ∩ A).Nonempty → anchor c ∈ S c ∩ A := by
      intro c h
      have : anchor c = h.choose := by rw [hanchor_def]; exact dif_pos h
      rw [this]; exact h.choose_spec
    have hcover : A ⊆ ⋃ c, S c := by
      intro q hq
      have hqR : q ∈ Metric.closedBall (0 : ℝ × ℝ) R := by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hR q hq
      obtain ⟨c, hc⟩ := grid2d hℓpos hM hqR
      exact Set.mem_iUnion.mpr ⟨c, by rw [hS]; exact hc⟩
    -- the image of each cell is contained in a short interval
    have hcell : ∀ c, f '' (S c ∩ A) ⊆ Metric.closedBall (f (anchor c)) (4 * ε * ℓ ^ 2) := by
      intro c y hy
      obtain ⟨z, ⟨hzS, hzA⟩, rfl⟩ := hy
      have hne : (S c ∩ A).Nonempty := ⟨z, hzS, hzA⟩
      have ha := hanchor c hne
      have hdist : dist z (anchor c) ≤ 2 * ℓ := by
        have h1 : dist z (G c) ≤ ℓ := hzS
        have h2 : dist (anchor c) (G c) ≤ ℓ := ha.1
        calc dist z (anchor c) ≤ dist z (G c) + dist (G c) (anchor c) := dist_triangle _ _ _
          _ ≤ ℓ + ℓ := by rw [dist_comm (G c) (anchor c)]; exact add_le_add h1 h2
          _ = 2 * ℓ := by ring
      have hnorm : ‖z - anchor c‖ ≤ 2 * ℓ := by rw [← dist_eq_norm]; exact hdist
      have hzp : ‖z - anchor c‖ ≤ δ := le_trans hnorm h2ℓδ
      have hb := hδ (anchor c) ha.2 z hzp
      rw [Metric.mem_closedBall]
      calc dist (f z) (f (anchor c)) = ‖f z - f (anchor c)‖ := dist_eq_norm _ _
        _ ≤ ε * ‖z - anchor c‖ ^ 2 := hb
        _ ≤ ε * (2 * ℓ) ^ 2 := mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hε.le
        _ = 4 * ε * ℓ ^ 2 := by ring
    have himg : f '' A ⊆ ⋃ c ∈ (Finset.univ : Finset (Fin (M + 1) × Fin (M + 1))),
        Metric.closedBall (f (anchor c)) (4 * ε * ℓ ^ 2) := by
      rintro y ⟨z, hzA, rfl⟩
      obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hcover hzA)
      exact Set.mem_biUnion (Finset.mem_univ c) (hcell c ⟨z, ⟨hc, hzA⟩, rfl⟩)
    calc MeasureTheory.volume (f '' A)
        ≤ MeasureTheory.volume (⋃ c ∈ (Finset.univ : Finset (Fin (M + 1) × Fin (M + 1))),
            Metric.closedBall (f (anchor c)) (4 * ε * ℓ ^ 2)) :=
            MeasureTheory.measure_mono himg
      _ ≤ ∑ c ∈ (Finset.univ : Finset (Fin (M + 1) × Fin (M + 1))),
            MeasureTheory.volume (Metric.closedBall (f (anchor c)) (4 * ε * ℓ ^ 2)) :=
            MeasureTheory.measure_biUnion_finset_le _ _
      _ = ∑ _c ∈ (Finset.univ : Finset (Fin (M + 1) × Fin (M + 1))),
            ENNReal.ofReal (8 * ε * ℓ ^ 2) := by
            apply Finset.sum_congr rfl; intro c _
            rw [Real.volume_closedBall]; congr 1; ring
      _ = ((M + 1) * (M + 1)) • ENNReal.ofReal (8 * ε * ℓ ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      _ = ENNReal.ofReal ((((M + 1) * (M + 1) : ℕ) : ℝ) * (8 * ε * ℓ ^ 2)) := by
            rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (128 * R ^ 2 * ε) := by
            apply ENNReal.ofReal_le_ofReal
            have hMlt : (M : ℝ) < 2 * R / ℓ + 1 := by
              rw [hMdef]; exact Nat.ceil_lt_add_one (by positivity)
            have hMl : (M : ℝ) * ℓ < 2 * R + ℓ := by
              have := mul_lt_mul_of_pos_right hMlt hℓpos
              rwa [add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hℓpos)] at this
            have hbound : ((M : ℝ) + 1) * ℓ ≤ 4 * R := by nlinarith
            have hsq : (((M : ℝ) + 1) * ℓ) ^ 2 ≤ (4 * R) ^ 2 := sq_le_sq' (by nlinarith) hbound
            have hkey : ((((M + 1) * (M + 1) : ℕ) : ℝ)) * (8 * ε * ℓ ^ 2)
                = 8 * ε * (((M : ℝ) + 1) * ℓ) ^ 2 := by push_cast; ring
            rw [hkey]
            nlinarith [hsq, hε.le]
  have hzero : MeasureTheory.volume (f '' A) ≤ 0 := by
    refine ENNReal.le_of_forall_pos_le_add (fun η hη _ => ?_)
    have hεpos : 0 < (η : ℝ) / (128 * R ^ 2 + 1) := by positivity
    have h1 := hmain _ hεpos
    have hle : 128 * R ^ 2 * ((η : ℝ) / (128 * R ^ 2 + 1)) ≤ (η : ℝ) := by
      rw [show 128 * R ^ 2 * ((η : ℝ) / (128 * R ^ 2 + 1))
          = (η : ℝ) * (128 * R ^ 2 / (128 * R ^ 2 + 1)) by ring]
      calc (η : ℝ) * (128 * R ^ 2 / (128 * R ^ 2 + 1)) ≤ (η : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left
              (by rw [div_le_one (by positivity)]; linarith) (by positivity)
        _ = (η : ℝ) := by ring
    have h2 : ENNReal.ofReal (128 * R ^ 2 * ((η : ℝ) / (128 * R ^ 2 + 1))) ≤ (η : ENNReal) :=
      le_trans (ENNReal.ofReal_le_ofReal hle) (le_of_eq ENNReal.ofReal_coe_nnreal)
    simpa using le_trans h1 h2
  exact le_antisymm hzero (by positivity)

theorem volume_image_null_of_partials_fderiv_eq_zero {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 2 G)
    {A : Set (ℝ × ℝ)} (hA : Bornology.IsBounded A)
    (h0 : ∀ p ∈ A, fderiv ℝ G p = 0)
    (h1 : ∀ p ∈ A, fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ G q ((1:ℝ), 0)) p = 0)
    (h2 : ∀ p ∈ A, fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ G q ((0:ℝ), 1)) p = 0) :
    MeasureTheory.volume (G '' A) = 0 := by
  obtain ⟨R, hRpos, hR⟩ := hA.exists_pos_norm_le
  have hH : ∀ p ∈ A, fderiv ℝ (fderiv ℝ G) p = 0 :=
    fderiv_fderiv_eq_zero_of_partial_fderivs h1 h2
  have hflat := second_order_bound_of_fderiv_fderiv_eq_zero hG hR h0 hH
  exact volume_image_null_of_uniform_second_order_bound hRpos hR hflat

end Work.Smooth.BoxGeneric.Sard
