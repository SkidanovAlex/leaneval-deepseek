import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.ContinuousMap.Compact

set_option maxHeartbeats 1000000

/-!
# Composition with an analytic map is analytic on `C(K, M)`

This file proves `Commons.Analysis.ContinuousMap.contDiff_omega_compContinuousMap`:
for a compact space `K` and an analytic map `F : M → E` between real normed spaces, the
composition operator `g ↦ F ∘ g` on `C(K, M)` is analytic (`C^ω`).

The proof follows the classical power series argument.  At a point `g₀ : C(K, M)` the candidate
power series is built from the Taylor coefficients `(n!)⁻¹ • DⁿF` of `F` at the points of
`Set.range g₀`, composed pointwise with the arguments.  Uniformity over `s : K` is obtained from
uniform Cauchy estimates on the compact set `Set.range g₀`, and the convergence of the
power series to `F (g₀ s + y s)` at every `s` comes from the fact that the canonical Taylor
series of an analytic function converges wherever its radius of convergence allows.
-/

namespace Commons.Analysis.ContinuousMap

open scoped Topology ContDiff ENNReal NNReal
open Set Filter

section PointwiseMultilinear

variable {K M E : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [CompactSpace K] in
/-- Pointwise evaluation of a continuous family of continuous multilinear maps along continuous
families of arguments is continuous. -/
private lemma continuous_pointwise_apply_cml {n : ℕ} (u : C(K, M [×n]→L[ℝ] E))
    (v : Fin n → C(K, M)) : Continuous fun s : K => u s (fun i => v i s) :=
  u.continuous.eval (continuous_pi fun i => (v i).continuous)

/-- The multilinear map `(v₁,…,vₙ) ↦ (s ↦ u s (v₁ s, …, vₙ s))` on `C(K, M)`. -/
private noncomputable def pointwiseMultilinearMap {n : ℕ} (u : C(K, M [×n]→L[ℝ] E)) :
    MultilinearMap ℝ (fun _ : Fin n => C(K, M)) C(K, E) where
  toFun v := ⟨fun s => u s (fun i => v i s), continuous_pointwise_apply_cml u v⟩
  map_update_add' v i x y := by
    ext s
    simp only [ContinuousMap.coe_mk, ContinuousMap.coe_add, Pi.add_apply]
    have h : (fun j : Fin n => (Function.update v i (x + y)) j s)
        = Function.update (fun j => v j s) i ((x + y) s) := by
      funext j
      by_cases hji : j = i <;> simp [Function.update, hji]
    have hx : (fun j : Fin n => (Function.update v i x) j s)
        = Function.update (fun j => v j s) i (x s) := by
      funext j
      by_cases hji : j = i <;> simp [Function.update, hji]
    have hy : (fun j : Fin n => (Function.update v i y) j s)
        = Function.update (fun j => v j s) i (y s) := by
      funext j
      by_cases hji : j = i <;> simp [Function.update, hji]
    rw [h, hx, hy, ContinuousMap.add_apply]
    exact ContinuousMultilinearMap.map_update_add (u s) (fun j => v j s) i (x s) (y s)
  map_update_smul' v i c x := by
    ext s
    simp only [ContinuousMap.coe_mk, ContinuousMap.coe_smul, Pi.smul_apply]
    have h : (fun j : Fin n => (Function.update v i (c • x)) j s)
        = Function.update (fun j => v j s) i ((c • x) s) := by
      funext j
      by_cases hji : j = i <;> simp [Function.update, hji]
    have hx : (fun j : Fin n => (Function.update v i x) j s)
        = Function.update (fun j => v j s) i (x s) := by
      funext j
      by_cases hji : j = i <;> simp [Function.update, hji]
    rw [h, hx, ContinuousMap.smul_apply]
    exact ContinuousMultilinearMap.map_update_smul (u s) (fun j => v j s) i c (x s)

/-- The continuous multilinear map `(v₁,…,vₙ) ↦ (s ↦ u s (v₁ s, …, vₙ s))` on `C(K, M)`. -/
private noncomputable def pointwiseContinuousMultilinearMap {n : ℕ} (u : C(K, M [×n]→L[ℝ] E)) :
    (C(K, M)) [×n]→L[ℝ] C(K, E) :=
  (pointwiseMultilinearMap u).mkContinuous ‖u‖ fun v => by
    refine (ContinuousMap.norm_le (f := (pointwiseMultilinearMap u) v)
      (C := ‖u‖ * ∏ i, ‖v i‖)
      (mul_nonneg (norm_nonneg u)
        (Finset.prod_nonneg fun i _ => norm_nonneg (v i)))).2 fun s => ?_
    calc ‖(pointwiseMultilinearMap u) v s‖
        = ‖u s (fun i => v i s)‖ := rfl
      _ ≤ ‖u s‖ * ∏ i, ‖v i s‖ := ContinuousMultilinearMap.le_opNorm (u s) _
      _ ≤ ‖u‖ * ∏ i, ‖v i‖ := by
          gcongr
          · exact ContinuousMap.norm_coe_le_norm u s
          · exact ContinuousMap.norm_coe_le_norm (v i) s

private lemma pointwiseContinuousMultilinearMap_apply {n : ℕ} (u : C(K, M [×n]→L[ℝ] E))
    (v : Fin n → C(K, M)) (s : K) :
    pointwiseContinuousMultilinearMap u v s = u s (fun i => v i s) := rfl

private lemma norm_pointwiseContinuousMultilinearMap_le {n : ℕ} (u : C(K, M [×n]→L[ℝ] E)) :
    ‖pointwiseContinuousMultilinearMap u‖ ≤ ‖u‖ := by
  rw [pointwiseContinuousMultilinearMap]
  exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg u) _

end PointwiseMultilinear

section DiagonalCoefficients

variable {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The diagonal values of a power series of an analytic function are the canonical Taylor
coefficients. -/
private theorem powerSeries_diagonal_eq {F : M → E} (hA : AnalyticOn ℝ F univ)
    {q : FormalMultilinearSeries ℝ M E} {u : M} {r : ENNReal}
    (hq : HasFPowerSeriesOnBall F q u r) (n : ℕ) (z : M) :
    q n (fun _ => z) = ((n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F u) (fun _ => z) := by
  have h1 := hq.iteratedFDeriv_eq_sum hA (v := fun _ : Fin n => z)
  have h2 : iteratedFDeriv ℝ n F u (fun _ => z) = (n.factorial : ℝ) • (q n (fun _ => z)) := by
    rw [h1]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    rw [Nat.cast_smul_eq_nsmul]
  have h3 : ((n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F u) (fun _ => z) = q n (fun _ => z) := by
    rw [smul_apply, h2, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_smul]
  exact h3.symm

end DiagonalCoefficients

section ChangeOriginBound

variable {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If the coefficients of a formal multilinear series `p` grow at most like `B (a/R)ⁿ`
(with `0 < a < 1`), then the coefficients of `p.changeOrigin x` for
`‖x‖ ≤ min (R/2) (R/(4a))` grow at most like `2B (2a/R)ⁿ`. -/
private theorem norm_changeOrigin_le {p : FormalMultilinearSeries ℝ M E} {R a B : ℝ} (hR : 0 < R)
    (ha : a ∈ Set.Ioo 0 1) (hB : 0 < B) (h : ∀ n, ‖p n‖ * R ^ n ≤ B * a ^ n) {x : M}
    (hx : ‖x‖ ≤ min (R / 2) (R / (4 * a))) (n : ℕ) :
    ‖p.changeOrigin x n‖ ≤ 2 * B * (2 * a / R) ^ n := by
  have ha0 : 0 < a := ha.1
  have hcoeff : ∀ m : ℕ, ‖p m‖ ≤ B * (a / R) ^ m := by
    intro m
    have hm := (le_div_iff₀ (pow_pos hR m)).2 (h m)
    simpa only [div_pow, mul_div_assoc'] using hm
  have hx1 : ‖x‖ ≤ R / (4 * a) := le_trans hx (min_le_right _ _)
  have hterm : ∀ l : ℕ, ‖(p.changeOriginSeries n) l (fun _ => x)‖ ≤
      B * (a / R) ^ n * 2 ^ n * (1 / 2) ^ l := by
    intro l
    have h0 : ‖(p.changeOriginSeries n) l (fun _ => x)‖₊ ≤
        (Fintype.card {s : Finset (Fin (n + l)) // s.card = l} : ℝ≥0) *
          (‖p (n + l)‖₊ * ‖x‖₊ ^ l) := by
      simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
        FormalMultilinearSeries.nnnorm_changeOriginSeries_apply_le_tsum p n l x
    have h1' : ‖(p.changeOriginSeries n) l (fun _ => x)‖ ≤
        (Fintype.card {s : Finset (Fin (n + l)) // s.card = l} : ℝ) * (‖p (n + l)‖ * ‖x‖ ^ l) := by
      have hc := NNReal.coe_le_coe.mpr h0
      push_cast at hc
      exact hc
    have h2 : (Fintype.card {s : Finset (Fin (n + l)) // s.card = l} : ℝ) ≤ 2 ^ (n + l) := by
      rw [Fintype.card_finset_len, Fintype.card_fin]
      exact_mod_cast Nat.choose_le_two_pow (n + l) l
    have h3 : ‖p (n + l)‖ ≤ B * (a / R) ^ n * (a / R) ^ l := by
      rw [mul_assoc, ← pow_add]
      exact hcoeff (n + l)
    have h4 : ‖x‖ ^ l ≤ (R / (4 * a)) ^ l := pow_le_pow_left₀ (norm_nonneg x) hx1 l
    calc ‖(p.changeOriginSeries n) l (fun _ => x)‖
        ≤ (Fintype.card {s : Finset (Fin (n + l)) // s.card = l} : ℝ) * (‖p (n + l)‖ * ‖x‖ ^ l) := h1'
      _ ≤ 2 ^ (n + l) * ((B * (a / R) ^ n * (a / R) ^ l) * (R / (4 * a)) ^ l) := by
          gcongr
      _ = B * (a / R) ^ n * 2 ^ n * (1 / 2) ^ l := by
          have key : 2 * (a / R) * (R / (4 * a)) = 1 / 2 := by field_simp; norm_num
          rw [← key]
          rw [mul_pow, mul_pow, pow_add]
          ring
  have hgeom : Summable fun l : ℕ => B * (a / R) ^ n * 2 ^ n * (1 / 2 : ℝ) ^ l :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  have hsum : Summable fun l : ℕ => ‖(p.changeOriginSeries n) l (fun _ => x)‖ :=
    Summable.of_nonneg_of_le (fun l => norm_nonneg _) hterm hgeom
  calc ‖p.changeOrigin x n‖
      = ‖∑' l, (p.changeOriginSeries n) l (fun _ => x)‖ := rfl
    _ ≤ ∑' l, ‖(p.changeOriginSeries n) l (fun _ => x)‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' l, B * (a / R) ^ n * 2 ^ n * (1 / 2 : ℝ) ^ l :=
        Summable.tsum_le_tsum hterm hsum hgeom
    _ = 2 * B * (2 * a / R) ^ n := by
        rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
        field_simp
        ring

end ChangeOriginBound

section IteratedFDerivBound

variable {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The canonical Taylor coefficient `(n!)⁻¹ • DⁿF(u)` is bounded in operator norm by the
`n`-th coefficient of any power series of `F` at `u`. -/
private theorem norm_smul_iteratedFDeriv_le {F : M → E} (hA : AnalyticOn ℝ F univ)
    {q : FormalMultilinearSeries ℝ M E} {u : M} {r : ENNReal}
    (hq : HasFPowerSeriesOnBall F q u r) (n : ℕ) :
    ‖(n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F u‖ ≤ ‖q n‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (f := (n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F u) (M := ‖q n‖) (norm_nonneg _) fun v => ?_
  rw [smul_apply]
  have h1 := hq.iteratedFDeriv_eq_sum hA v
  rw [h1]
  calc ‖(n.factorial : ℝ)⁻¹ • ∑ σ : Equiv.Perm (Fin n), q n (fun i => v (σ i))‖
      = (n.factorial : ℝ)⁻¹ * ‖∑ σ : Equiv.Perm (Fin n), q n (fun i => v (σ i))‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ (n.factorial : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin n), ‖q n‖ * ∏ i, ‖v i‖ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro σ _
        calc ‖q n (fun i => v (σ i))‖ ≤ ‖q n‖ * ∏ i, ‖v (σ i)‖ :=
              ContinuousMultilinearMap.le_opNorm _ _
          _ = ‖q n‖ * ∏ i, ‖v i‖ := by
              congr 1
              exact Equiv.prod_comp σ (fun i => ‖v i‖)
    _ = ‖q n‖ * ∏ i, ‖v i‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero),
          one_mul]

end IteratedFDerivBound

section UniformBound

variable {K M E : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {F : M → E}

/-- **Uniform Cauchy estimates on a compact set** (complete target space): for an analytic map
`F` and `g₀ : C(K, M)` there are `ρ > 0` and `C` with `‖DⁿF(g₀ s)‖ ρⁿ ≤ C n!` for every `n` and
every `s`. -/
private theorem uniform_iteratedFDeriv_bound_of_completeSpace (hF : ContDiff ℝ ω F) (g₀ : C(K, M)) :
    ∃ ρ > 0, ∃ C : ℝ, ∀ n : ℕ, ∀ s : K,
      ‖iteratedFDeriv ℝ n F (g₀ s)‖ * ρ ^ n ≤ C * (n.factorial : ℝ) := by
  have hA : AnalyticOnNhd ℝ F univ := contDiff_omega_iff_analyticOnNhd.mp hF
  have hAon : AnalyticOn ℝ F univ := hA.analyticOn
  have hex : ∀ s : K, ∃ (q : FormalMultilinearSeries ℝ M E) (ρ : ℝ≥0) (a B : ℝ),
      0 < ρ ∧ a ∈ Set.Ioo 0 1 ∧ 0 < B ∧ (∀ n, ‖q n‖ * ((ρ:ℝ)) ^ n ≤ B * a ^ n) ∧
        HasFPowerSeriesOnBall F q (g₀ s) (ρ : ENNReal) := by
    intro s
    obtain ⟨q, r, hq⟩ := hA (g₀ s) (mem_univ _)
    obtain ⟨ρ, hρpos, hρr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq.r_pos
    obtain ⟨a, ha, B, hB, hbound⟩ :=
      q.norm_mul_pow_le_mul_pow_of_lt_radius (r := ρ) (lt_of_lt_of_le hρr hq.r_le)
    exact ⟨q, ρ, a, B, ENNReal.coe_pos.mp hρpos, ha, hB, hbound, hq.mono hρpos hρr.le⟩
  choose q ρ a B hρpos ha hB hcoeff hseries using hex
  let W : K → ℝ := fun s => min ((ρ s : ℝ) / 2) ((ρ s : ℝ) / (4 * a s))
  have hρreal : ∀ s, (0:ℝ) < (ρ s : ℝ) := fun s => by exact_mod_cast hρpos s
  have hWpos : ∀ s, 0 < W s := fun s => lt_min (div_pos (hρreal s) two_pos)
    (div_pos (hρreal s) (mul_pos (by norm_num) (by have := (ha s).1; positivity)))
  let w : K → ℝ≥0 := fun s => Real.toNNReal (W s)
  have hwcoe : ∀ s, ((w s : ℝ≥0) : ℝ) = W s := fun s =>
    Real.coe_toNNReal _ (le_of_lt (hWpos s))
  have hwpos : ∀ s, 0 < w s := fun s => Real.toNNReal_pos.mpr (hWpos s)
  have hcover : Set.range g₀ ⊆ ⋃ s : K, Metric.eball (g₀ s) (w s : ENNReal) := by
    rintro y ⟨s, rfl⟩
    exact mem_iUnion.2 ⟨s, Metric.mem_eball_self (ENNReal.coe_pos.mpr (hwpos s))⟩
  obtain ⟨t, ht⟩ := (isCompact_range g₀.continuous).elim_finite_subcover
      (fun s : K => Metric.eball (g₀ s) (w s : ENNReal)) (fun s => Metric.isOpen_eball) hcover
  rcases t.eq_empty_or_nonempty with ht0 | htne
  · have hrange : Set.range g₀ = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨y, hy⟩
      obtain ⟨s, rfl⟩ := hy
      have h1 := ht (Set.mem_range_self s)
      rw [ht0] at h1
      simp at h1
    have hne : ¬ Nonempty K := fun ⟨s⟩ => by
      have : g₀ s ∈ Set.range g₀ := ⟨s, rfl⟩
      rw [hrange] at this
      exact this
    exact ⟨1, one_pos, 0, fun n s => absurd ⟨s⟩ hne⟩
  · have htne' : (t.image (fun s => (ρ s : ℝ) / (2 * a s))).Nonempty := htne.image _
    let δ : ℝ := (t.image (fun s => (ρ s : ℝ) / (2 * a s))).min' htne'
    have hδmem : δ ∈ t.image (fun s => (ρ s : ℝ) / (2 * a s)) := by
      dsimp only [δ]
      exact Finset.min'_mem _ _
    have hδpos : 0 < δ := by
      obtain ⟨x, hx, hxδ⟩ := Finset.mem_image.mp hδmem
      calc 0 < (ρ x : ℝ) / (2 * a x) :=
            div_pos (by exact_mod_cast hρpos x) (by have := (ha x).1; positivity)
        _ = δ := hxδ
    have hδle : ∀ s ∈ t, δ ≤ (ρ s : ℝ) / (2 * a s) := fun s hs =>
      Finset.min'_le _ _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
    refine ⟨δ, hδpos, ∑ s ∈ t, 2 * B s, fun n s => ?_⟩
    obtain ⟨i, hi, hsi⟩ : ∃ i ∈ t, g₀ s ∈ Metric.eball (g₀ i) (w i : ENNReal) := by
      have h1 := ht (Set.mem_range_self s)
      simpa [Set.mem_iUnion, exists_prop] using h1
    have hdist_nn : ‖g₀ s - g₀ i‖₊ < w i := by
      have h2 : edist (g₀ s) (g₀ i) < (w i : ENNReal) := Metric.mem_eball.mp hsi
      rw [edist_eq_enorm_sub, enorm_eq_nnnorm, ENNReal.coe_lt_coe] at h2
      exact h2
    have hwle : w i ≤ ρ i := by
      rw [← NNReal.coe_le_coe, hwcoe i]
      refine le_trans (min_le_left _ _) ?_
      have h0 : (0:ℝ) < (ρ i : ℝ) := by exact_mod_cast hρpos i
      linarith
    have hwit : (‖g₀ s - g₀ i‖₊ : ENNReal) < (ρ i : ENNReal) := by
      rw [ENNReal.coe_lt_coe]
      exact lt_of_lt_of_le hdist_nn hwle
    have hdistW : ‖g₀ s - g₀ i‖ ≤ min ((ρ i : ℝ) / 2) ((ρ i : ℝ) / (4 * a i)) := by
      calc ‖g₀ s - g₀ i‖ = ((‖g₀ s - g₀ i‖₊ : ℝ≥0) : ℝ) := by simp
        _ ≤ ((w i : ℝ≥0) : ℝ) := by exact_mod_cast hdist_nn.le
        _ = W i := hwcoe i
    have hnew : HasFPowerSeriesOnBall F ((q i).changeOrigin (g₀ s - g₀ i)) (g₀ s)
        ((ρ i : ENNReal) - (‖g₀ s - g₀ i‖₊ : ENNReal)) := by
      have hh := (hseries i).changeOrigin hwit
      rw [add_sub_cancel] at hh
      exact hh
    have hbound := norm_changeOrigin_le (p := q i) (R := (ρ i : ℝ)) (a := a i) (B := B i)
      (by exact_mod_cast hρpos i) (ha i) (hB i) (hcoeff i) hdistW n
    have hle := norm_smul_iteratedFDeriv_le hAon hnew n
    have hifd : ‖iteratedFDeriv ℝ n F (g₀ s)‖ =
        (n.factorial : ℝ) * ‖(n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F (g₀ s)‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      field_simp
    calc ‖iteratedFDeriv ℝ n F (g₀ s)‖ * δ ^ n
        = (n.factorial : ℝ) *
            (‖(n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F (g₀ s)‖ * δ ^ n) := by
          rw [hifd]; ring
      _ ≤ (n.factorial : ℝ) * (2 * B i * (2 * a i / (ρ i : ℝ)) ^ n * δ ^ n) := by
          gcongr
          exact hle.trans hbound
      _ ≤ (n.factorial : ℝ) * (2 * B i) := by
          have ha0 : 0 < a i := (ha i).1
          have h2a : (0:ℝ) ≤ 2 * a i := by linarith
          have hcol : (0:ℝ) ≤ 2 * a i / (ρ i : ℝ) := div_nonneg h2a (le_of_lt (hρreal i))
          have hprod : (2 * a i / (ρ i : ℝ)) ^ n * δ ^ n ≤ 1 := by
            rw [← mul_pow]
            refine pow_le_one₀ (mul_nonneg hcol (le_of_lt hδpos)) ?_
            calc 2 * a i / (ρ i : ℝ) * δ ≤
                  2 * a i / (ρ i : ℝ) * ((ρ i : ℝ) / (2 * a i)) :=
                  mul_le_mul_of_nonneg_left (hδle i hi) hcol
              _ = 1 := by
                  have ha0' : a i ≠ 0 := ha0.ne'
                  have hρ0 : (ρ i : ℝ) ≠ 0 := (hρreal i).ne'
                  field_simp
          have hBnn : (0:ℝ) ≤ 2 * B i := by have := hB i; positivity
          have hfac : (0:ℝ) ≤ (n.factorial : ℝ) := by positivity
          calc (n.factorial : ℝ) * (2 * B i * (2 * a i / (ρ i : ℝ)) ^ n * δ ^ n)
              = (n.factorial : ℝ) * (2 * B i) *
                  ((2 * a i / (ρ i : ℝ)) ^ n * δ ^ n) := by ring
            _ ≤ (n.factorial : ℝ) * (2 * B i) * 1 := by gcongr
            _ = (n.factorial : ℝ) * (2 * B i) := by ring
      _ ≤ (∑ s ∈ t, 2 * B s) * (n.factorial : ℝ) := by
          have hsum : 2 * B i ≤ ∑ s ∈ t, 2 * B s := by
            refine Finset.single_le_sum (f := fun s => 2 * B s) ?_ hi
            intro j _
            have := hB j
            positivity
          have hfac : (0:ℝ) ≤ (n.factorial : ℝ) := by positivity
          calc (n.factorial : ℝ) * (2 * B i) = (2 * B i) * (n.factorial : ℝ) := by ring
            _ ≤ (∑ s ∈ t, 2 * B s) * (n.factorial : ℝ) :=
                mul_le_mul_of_nonneg_right hsum hfac

end UniformBound

section CanonicalSeries

variable {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Transfer of convergence from the completion back to `E` (both spaces carry the same norm). -/
lemma HasSum.of_completion {f : ℕ → E} {a : E}
    (hf : HasSum (fun n => (UniformSpace.Completion.toComplₗᵢ : E →ₗᵢ[ℝ] UniformSpace.Completion E)
      (f n)) ((UniformSpace.Completion.toComplₗᵢ : E →ₗᵢ[ℝ] UniformSpace.Completion E) a))
    (hS : Summable fun n => ‖f n‖) : HasSum f a := by
  rw [hasSum_iff_tendsto_nat_of_summable_norm hS, Metric.tendsto_nhds]
  intro ε hε
  have h2 : Tendsto (fun N => (UniformSpace.Completion.toComplₗᵢ : E →ₗᵢ[ℝ] UniformSpace.Completion E)
      (∑ n ∈ Finset.range N, f n)) atTop
      (𝓝 ((UniformSpace.Completion.toComplₗᵢ : E →ₗᵢ[ℝ] UniformSpace.Completion E) a)) :=
    (hf.tendsto_sum_nat).congr' (Eventually.of_forall fun N => (map_sum _ _ _).symm)
  have h6 : Tendsto (fun N => (UniformSpace.Completion.toComplₗᵢ : E →ₗᵢ[ℝ] UniformSpace.Completion E)
      (∑ n ∈ Finset.range N, f n) -
        (UniformSpace.Completion.toComplₗᵢ : E →ₗᵢ[ℝ] UniformSpace.Completion E) a) atTop
      (𝓝 ((UniformSpace.Completion.toComplₗᵢ : E →ₗᵢ[ℝ] UniformSpace.Completion E) a -
        (UniformSpace.Completion.toComplₗᵢ : E →ₗᵢ[ℝ] UniformSpace.Completion E) a)) :=
    h2.sub tendsto_const_nhds
  have h5 : Tendsto (fun N => ‖(UniformSpace.Completion.toComplₗᵢ : E →ₗᵢ[ℝ] UniformSpace.Completion E)
      (∑ n ∈ Finset.range N, f n) -
        (UniformSpace.Completion.toComplₗᵢ : E →ₗᵢ[ℝ] UniformSpace.Completion E) a‖) atTop (𝓝 0) := by
    simpa using h6.norm
  have h7 : Tendsto (fun N => ‖(∑ n ∈ Finset.range N, f n) - a‖) atTop (𝓝 0) :=
    h5.congr' (Eventually.of_forall fun N => by
      rw [← map_sub]
      exact LinearIsometry.norm_map _ _)
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 h7 ε hε
  filter_upwards [eventually_ge_atTop N₀] with N hN
  simpa [dist_eq_norm] using hN₀ N hN

/-- The canonical Taylor series of an analytic function is a power series with the radius given by
a geometric bound on the canonical Taylor coefficients (complete target space). -/
private theorem hasFPowerSeriesOnBall_canonicalSeries_of_completeSpace [CompleteSpace E] {F : M → E}
    (hA : AnalyticOnNhd ℝ F univ) {u : M} {ρ : ℝ≥0} (hρ : 0 < ρ) {C : ℝ}
    (hbd : ∀ n : ℕ, ‖(n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F u‖ * (ρ:ℝ) ^ n ≤ C) :
    HasFPowerSeriesOnBall F
      (fun n : ℕ => (n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F u) u (ρ : ENNReal) := by
  have hAon : AnalyticOn ℝ F univ := hA.analyticOn
  have hρr : (0:ℝ) < (ρ:ℝ) := by exact_mod_cast hρ
  have hρe : (0:ENNReal) < (ρ:ENNReal) := ENNReal.coe_pos.mpr hρ
  let p : FormalMultilinearSeries ℝ M E :=
    fun n : ℕ => (n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F u
  have hp : p = fun n : ℕ => (n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F u := rfl
  have hrad : (ρ:ENNReal) ≤ p.radius := p.le_radius_of_bound C hbd
  obtain ⟨q, r, hq⟩ := hA u (mem_univ u)
  have hdiag : ∀ (m : ℕ) (z : M), q m (fun _ => z) = p m (fun _ => z) := by
    intro m z
    rw [hp]
    exact powerSeries_diagonal_eq hAon hq m z
  have hsmall : p.sum =ᶠ[𝓝 (0:M)] (fun z => F (u + z)) := by
    filter_upwards [Metric.eball_mem_nhds (0:M) hq.r_pos] with z hz
    have h1 : HasSum (fun m : ℕ => p m (fun _ => z)) (F (u + z)) := by
      simpa only [hdiag] using hq.hasSum hz
    simpa only [FormalMultilinearSeries.sum] using h1.tsum_eq
  have h1 : AnalyticOnNhd ℝ p.sum (Metric.ball (0:M) (ρ:ℝ)) := by
    refine (FormalMultilinearSeries.analyticOnNhd (p := p)).mono ?_
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    refine Metric.mem_eball.mpr ?_
    rw [edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm]
    exact lt_of_lt_of_le (by rw [ENNReal.coe_lt_coe]; exact_mod_cast hz) hrad
  have h2 : AnalyticOnNhd ℝ (fun z : M => F (u + z)) (Metric.ball (0:M) (ρ:ℝ)) := by
    intro z _
    exact (hA (u + z) (mem_univ _)).comp (analyticAt_const.add analyticAt_id)
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq h1 h2
    (convex_ball (0:M) (ρ:ℝ)).isPreconnected (Metric.mem_ball_self hρr) hsmall
  refine ⟨hrad, hρe, fun {y} hy => ?_⟩
  have hy' : ‖y‖ < (ρ:ℝ) := by
    have h := Metric.mem_eball.mp hy
    rw [edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm, ENNReal.coe_lt_coe] at h
    exact_mod_cast h
  have hval : p.sum y = F (u + y) := heq (by
    rw [Metric.mem_ball, dist_zero_right]
    exact hy')
  have hC0 : 0 ≤ C := by
    have h1 := hbd 0
    simp only [pow_zero, mul_one] at h1
    exact le_trans (norm_nonneg (p 0)) h1
  have hS : Summable fun m : ℕ => ‖p m (fun _ => y)‖ := by
    have hb : ∀ m : ℕ, ‖p m (fun _ => y)‖ ≤ C * (‖y‖ / (ρ:ℝ)) ^ m := by
      intro m
      have h1 : ‖p m‖ ≤ C * ((ρ:ℝ))⁻¹ ^ m := by
        have h2 := (le_div_iff₀ (pow_pos hρr m)).2 (hbd m)
        simpa only [div_eq_mul_inv, inv_pow] using h2
      calc ‖p m (fun _ => y)‖ ≤ ‖p m‖ * ‖y‖ ^ m := by
            simpa only [Fin.prod_const] using ContinuousMultilinearMap.le_opNorm (p m) (fun _ => y)
        _ ≤ C * ((ρ:ℝ))⁻¹ ^ m * ‖y‖ ^ m := by gcongr
        _ = C * (‖y‖ / (ρ:ℝ)) ^ m := by rw [div_pow, div_eq_mul_inv, inv_pow]; ring
    have hr : ‖‖y‖ / (ρ:ℝ)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg y) (le_of_lt hρr))]
      exact (div_lt_one hρr).2 hy'
    exact Summable.of_nonneg_of_le (fun m => norm_nonneg _) hb
      ((summable_geometric_of_norm_lt_one hr).mul_left C)
  have hsumm : Summable fun m : ℕ => p m (fun _ => y) := hS.of_norm
  have hfin := hsumm.hasSum
  rwa [show (∑' m, p m (fun _ => y)) = F (u + y) from by rw [← hval]; rfl] at hfin

end CanonicalSeries


section GeneralCase

variable {K M E : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Uniform Cauchy estimates on a compact set**: for an analytic map `F` and `g₀ : C(K, M)`
there are `ρ > 0` and `C` with `‖DⁿF(g₀ s)‖ ρⁿ ≤ C n!` for every `n` and every `s`. -/
private theorem uniform_iteratedFDeriv_bound {F : M → E} (hF : ContDiff ℝ ω F) (g₀ : C(K, M)) :
    ∃ ρ > 0, ∃ C : ℝ, ∀ n : ℕ, ∀ s : K,
      ‖iteratedFDeriv ℝ n F (g₀ s)‖ * ρ ^ n ≤ C * (n.factorial : ℝ) := by
  have hFc : ContDiff ℝ ω (fun x : M =>
      (UniformSpace.Completion.toComplₗᵢ : E →ₗᵢ[ℝ] UniformSpace.Completion E) (F x)) :=
    ((UniformSpace.Completion.toComplL : E →L[ℝ] UniformSpace.Completion E)).contDiff.comp hF
  obtain ⟨ρ, hρ, C, hC⟩ :=
    uniform_iteratedFDeriv_bound_of_completeSpace (E := UniformSpace.Completion E) hFc g₀
  refine ⟨ρ, hρ, C, fun n s => ?_⟩
  have hnorm : ‖iteratedFDeriv ℝ n (fun x : M =>
      (UniformSpace.Completion.toComplₗᵢ : E →ₗᵢ[ℝ] UniformSpace.Completion E) (F x)) (g₀ s)‖ =
      ‖iteratedFDeriv ℝ n F (g₀ s)‖ :=
    LinearIsometry.norm_iteratedFDeriv_comp_left
      (UniformSpace.Completion.toComplₗᵢ : E →ₗᵢ[ℝ] UniformSpace.Completion E)
      hF.contDiffAt le_top
  rw [← hnorm]
  exact hC n s

/-- Norm-summability of the canonical Taylor series of an analytic function on the ball where its
coefficients are geometrically bounded. -/
private lemma summable_canonical_series_norm {F : M → E} {u : M} {ρ : ℝ≥0} (hρ : 0 < ρ) {C : ℝ}
    (hbd : ∀ n : ℕ, ‖(n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F u‖ * (ρ:ℝ) ^ n ≤ C)
    {y : M} (hy : ‖y‖ < (ρ:ℝ)) :
    Summable fun n : ℕ => ‖((n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F u) (fun _ => y)‖ := by
  have hρr : (0:ℝ) < (ρ:ℝ) := by exact_mod_cast hρ
  have hb : ∀ n : ℕ, ‖((n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F u) (fun _ => y)‖ ≤
      C * (‖y‖ / (ρ:ℝ)) ^ n := by
    intro n
    have h1 : ‖(n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F u‖ ≤ C * ((ρ:ℝ))⁻¹ ^ n := by
      have h2 := (le_div_iff₀ (pow_pos hρr n)).2 (hbd n)
      simpa only [div_eq_mul_inv, inv_pow] using h2
    calc ‖((n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F u) (fun _ => y)‖ ≤
          ‖(n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F u‖ * ‖y‖ ^ n := by
          simpa only [Fin.prod_const] using
            ContinuousMultilinearMap.le_opNorm ((n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F u)
              (fun _ => y)
      _ ≤ C * ((ρ:ℝ))⁻¹ ^ n * ‖y‖ ^ n := by gcongr
      _ = C * (‖y‖ / (ρ:ℝ)) ^ n := by rw [div_pow, div_eq_mul_inv, inv_pow]; ring
  have hr : ‖‖y‖ / (ρ:ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg y) (le_of_lt hρr))]
    exact (div_lt_one hρr).2 hy
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb
    ((summable_geometric_of_norm_lt_one hr).mul_left C)

/-- **The canonical Taylor series of an analytic function is a power series** with the radius
provided by a geometric bound on its coefficients. -/
private theorem hasFPowerSeriesOnBall_canonicalSeries {F : M → E} (hA : AnalyticOnNhd ℝ F univ) {u : M}
    {ρ : ℝ≥0} (hρ : 0 < ρ) {C : ℝ}
    (hbd : ∀ n : ℕ, ‖(n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F u‖ * (ρ:ℝ) ^ n ≤ C) :
    HasFPowerSeriesOnBall F
      (fun n : ℕ => (n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F u) u (ρ : ENNReal) := by
  let ê : E →ₗᵢ[ℝ] UniformSpace.Completion E := UniformSpace.Completion.toComplₗᵢ
  have hAω : ContDiff ℝ ω F := hA.contDiff
  have hêc : ContDiff ℝ ω (fun x : M => ê (F x)) :=
    ê.toContinuousLinearMap.contDiff.comp hAω
  have hA' : AnalyticOnNhd ℝ (fun x : M => ê (F x)) univ :=
    contDiff_omega_iff_analyticOnNhd.mp hêc
  have hiter : ∀ n : ℕ, ‖(n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n (fun x : M => ê (F x)) u‖ =
      ‖(n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F u‖ := by
    intro n
    rw [norm_smul, norm_smul]
    congr 1
    exact LinearIsometry.norm_iteratedFDeriv_comp_left ê hAω.contDiffAt le_top
  have hbd' : ∀ n : ℕ,
      ‖(n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n (fun x : M => ê (F x)) u‖ * (ρ:ℝ) ^ n ≤ C :=
    fun n => by rw [hiter n]; exact hbd n
  have hP := hasFPowerSeriesOnBall_canonicalSeries_of_completeSpace hA' hρ hbd'
  have hy' : ∀ {y : M}, y ∈ Metric.eball (0:M) (ρ : ENNReal) → ‖y‖ < (ρ:ℝ) := by
    intro y hy
    have h := Metric.mem_eball.mp hy
    rw [edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm, ENNReal.coe_lt_coe] at h
    exact_mod_cast h
  refine ⟨FormalMultilinearSeries.le_radius_of_bound _ C hbd, hP.r_pos, fun {y} hy => ?_⟩
  refine HasSum.of_completion ?_ (summable_canonical_series_norm hρ hbd (hy' hy))
  have hterm : ∀ n : ℕ, ((n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n (fun x : M => ê (F x)) u)
        (fun _ => y) =
      ê (((n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F u) (fun _ => y)) := by
    intro n
    have hcomp : (fun x : M => ê (F x)) = ⇑(ê.toContinuousLinearMap) ∘ F := rfl
    rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_left ê.toContinuousLinearMap hAω.contDiffAt
      le_top]
    rw [smul_apply]
    show (n.factorial : ℝ)⁻¹ • (ê (iteratedFDeriv ℝ n F u (fun _ => y))) =
      ê ((n.factorial : ℝ)⁻¹ • (iteratedFDeriv ℝ n F u (fun _ => y)))
    rw [← map_smul]
  simpa only [hterm] using hP.hasSum hy

end GeneralCase


section Main

variable {K M E : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem contDiff_omega_compContinuousMap_aux {F : M → E} (hF : ContDiff ℝ ω F) :
    ContDiff ℝ ω (fun g : C(K, M) => (⟨F, hF.continuous⟩ : C(M, E)).comp g) := by
  rw [contDiff_omega_iff_analyticOnNhd]
  intro g₀ _
  have hA : AnalyticOnNhd ℝ F univ := contDiff_omega_iff_analyticOnNhd.mp hF
  obtain ⟨ρ, hρpos, C₀, hC₀⟩ := uniform_iteratedFDeriv_bound (K := K) hF g₀
  set C : ℝ := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ n : ℕ, ∀ s : K, ‖iteratedFDeriv ℝ n F (g₀ s)‖ * ρ ^ n ≤ C * (n.factorial : ℝ) :=
    fun n s => le_trans (hC₀ n s) (by gcongr; exact le_max_left _ _)
  let ρ' : ℝ≥0 := ⟨ρ, hρpos.le⟩
  have hρ'pos : 0 < ρ' := by rw [← NNReal.coe_pos]; exact hρpos
  -- coefficient bound for the canonical Taylor coefficients of `F` at the points `g₀ s`
  have hbd_pt : ∀ (s : K) (n : ℕ),
      ‖(n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F (g₀ s)‖ * ρ ^ n ≤ C := by
    intro s n
    have h1 : (n.factorial : ℝ)⁻¹ * (‖iteratedFDeriv ℝ n F (g₀ s)‖ * ρ ^ n) ≤
        (n.factorial : ℝ)⁻¹ * (C * (n.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (hC n s) (by positivity)
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc (n.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ n F (g₀ s)‖ * ρ ^ n
        = (n.factorial : ℝ)⁻¹ * (‖iteratedFDeriv ℝ n F (g₀ s)‖ * ρ ^ n) := by ring
      _ ≤ (n.factorial : ℝ)⁻¹ * (C * (n.factorial : ℝ)) := h1
      _ = C := by field_simp
  have hu_cont (n : ℕ) : Continuous fun s : K =>
      (n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F (g₀ s) :=
    (continuous_const : Continuous fun _ : K => ((n.factorial : ℝ)⁻¹)).smul
      ((hF.continuous_iteratedFDeriv (m := n) le_top).comp g₀.continuous)
  let u : (n : ℕ) → C(K, M [×n]→L[ℝ] E) := fun n =>
    ⟨fun s => (n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F (g₀ s), hu_cont n⟩
  let P : FormalMultilinearSeries ℝ (C(K, M)) (C(K, E)) := fun n =>
    pointwiseContinuousMultilinearMap (u n)
  have hP_apply : ∀ (n : ℕ) (v : Fin n → C(K, M)) (s : K),
      P n v s = u n s (fun i => v i s) :=
    fun n v s => pointwiseContinuousMultilinearMap_apply (u n) v s
  have hP_norm : ∀ n : ℕ, ‖P n‖ ≤ ‖u n‖ := fun n =>
    norm_pointwiseContinuousMultilinearMap_le (u n)
  have hu_bound : ∀ n : ℕ, ‖u n‖ ≤ C * ρ⁻¹ ^ n := by
    intro n
    refine (ContinuousMap.norm_le (f := u n) (C := C * ρ⁻¹ ^ n)
      (mul_nonneg hC0 (by positivity))).mpr fun s => ?_
    have h3 := (le_div_iff₀ (pow_pos hρpos n)).2 (hbd_pt s n)
    exact h3.trans_eq (by rw [div_eq_mul_inv, inv_pow])
  have hP_bound : ∀ n : ℕ, ‖P n‖ * ρ ^ n ≤ C := by
    intro n
    have h2 : ‖P n‖ ≤ C * ρ⁻¹ ^ n :=
      (hP_norm n).trans (hu_bound n)
    calc ‖P n‖ * ρ ^ n ≤ C * ρ⁻¹ ^ n * ρ ^ n :=
          mul_le_mul_of_nonneg_right h2 (pow_nonneg hρpos.le n)
      _ = C := by
          rw [inv_pow]
          have hne : ρ ^ n ≠ 0 := pow_ne_zero _ hρpos.ne'
          field_simp
  -- summability of the series in `C(K,E)`
  have hgeom : ∀ {y : C(K, M)}, ‖y‖ < ρ → Summable fun n : ℕ => ‖P n (fun _ => y)‖ := by
    intro y hy
    have hr : ‖‖y‖ / ρ‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg y) hρpos.le)]
      exact (div_lt_one hρpos).2 hy
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_
      ((summable_geometric_of_norm_lt_one hr).mul_left C)
    intro n
    have h1 : ‖P n‖ ≤ C * ρ⁻¹ ^ n := (hP_norm n).trans (hu_bound n)
    calc ‖P n (fun _ => y)‖ ≤ ‖P n‖ * ‖y‖ ^ n := by
          simpa only [Fin.prod_const] using
            ContinuousMultilinearMap.le_opNorm (P n) (fun _ => y)
      _ ≤ C * ρ⁻¹ ^ n * ‖y‖ ^ n := mul_le_mul_of_nonneg_right h1 (pow_nonneg (norm_nonneg y) n)
      _ = C * (‖y‖ / ρ) ^ n := by rw [div_pow, div_eq_mul_inv, inv_pow]; ring
  -- uniform tail bound
  have htail : ∀ {y : C(K, M)} (hy : ‖y‖ < ρ) (N : ℕ),
      ‖(∑ n ∈ Finset.range N, P n (fun _ => y)) - (⟨F, hF.continuous⟩ : C(M, E)).comp (g₀ + y)‖ ≤
        C * (‖y‖ / ρ) ^ N / (1 - ‖y‖ / ρ) := by
    intro y hy N
    have hr : ‖y‖ / ρ < 1 := (div_lt_one hρpos).2 hy
    refine (ContinuousMap.norm_le (f := (∑ n ∈ Finset.range N, P n (fun _ => y)) -
      (⟨F, hF.continuous⟩ : C(M, E)).comp (g₀ + y))
      (C := C * (‖y‖ / ρ) ^ N / (1 - ‖y‖ / ρ))
      (div_nonneg (mul_nonneg hC0 (pow_nonneg (div_nonneg (norm_nonneg y) hρpos.le) N))
        (by linarith))).mpr fun s => ?_
    have hys : y s ∈ Metric.eball (0 : M) (ρ' : ENNReal) := by
      refine Metric.mem_eball.mpr ?_
      rw [edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm, ENNReal.coe_lt_coe]
      rw [← NNReal.coe_lt_coe]
      exact lt_of_le_of_lt (ContinuousMap.norm_coe_le_norm y s) hy
    have hps := hasFPowerSeriesOnBall_canonicalSeries hA hρ'pos (hbd_pt s)
    have hgs : ∀ n : ℕ, ‖((n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F (g₀ s)) (fun _ => y s)‖ ≤
        C * (‖y‖ / ρ) ^ n := by
      intro n
      have h1 : ‖((n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F (g₀ s)) (fun _ => y s)‖ ≤
          ‖(n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F (g₀ s)‖ * ‖y s‖ ^ n := by
        simpa only [Fin.prod_const] using
          ContinuousMultilinearMap.le_opNorm
            ((n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F (g₀ s)) (fun _ => y s)
      have h2 : ‖(n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F (g₀ s)‖ ≤ C * ρ⁻¹ ^ n :=
        ((le_div_iff₀ (pow_pos hρpos n)).2 (hbd_pt s n)).trans_eq (by
          rw [div_eq_mul_inv, inv_pow])
      have h3 : ‖y s‖ ^ n ≤ ‖y‖ ^ n := pow_le_pow_left₀ (norm_nonneg _)
        (ContinuousMap.norm_coe_le_norm y s) n
      calc ‖((n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F (g₀ s)) (fun _ => y s)‖
          ≤ ‖(n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F (g₀ s)‖ * ‖y s‖ ^ n := h1
        _ ≤ C * ρ⁻¹ ^ n * ‖y‖ ^ n :=
            mul_le_mul h2 h3 (pow_nonneg (norm_nonneg (y s)) n) (by positivity)
        _ = C * (‖y‖ / ρ) ^ n := by rw [div_pow, div_eq_mul_inv, inv_pow]; ring
    have hsum_eq : (∑ n ∈ Finset.range N, P n (fun _ => y)) s =
        ∑ n ∈ Finset.range N,
          ((n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n F (g₀ s)) (fun _ => y s) := by
      rw [ContinuousMap.sum_apply]
      exact Finset.sum_congr rfl fun n _ => hP_apply n (fun _ => y) s
    have hcomp : ((⟨F, hF.continuous⟩ : C(M, E)).comp (g₀ + y)) s = F (g₀ s + y s) :=
      rfl
    rw [ContinuousMap.sub_apply, hsum_eq, hcomp]
    exact norm_sub_le_of_geometric_bound_of_hasSum hr hgs (hps.hasSum hys) N
  -- assemble the power series
  refine ⟨P, ⟨(ρ' : ENNReal), FormalMultilinearSeries.le_radius_of_bound P C hP_bound,
    ENNReal.coe_pos.mpr hρ'pos, fun {y} hy => ?_⟩⟩
  have hy : ‖y‖ < ρ := by
    have h := Metric.mem_eball.mp hy
    rw [edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm, ENNReal.coe_lt_coe] at h
    rw [← NNReal.coe_lt_coe] at h
    exact_mod_cast h
  refine (hasSum_iff_tendsto_nat_of_summable_norm (hgeom hy)).mpr ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hlim : Tendsto (fun N : ℕ => C * (‖y‖ / ρ) ^ N / (1 - ‖y‖ / ρ)) atTop (𝓝 0) := by
    have hr : ‖‖y‖ / ρ‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg y) hρpos.le)]
      exact (div_lt_one hρpos).2 hy
    have h1 : Tendsto (fun N : ℕ => (‖y‖ / ρ) ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr
    have h2 : Tendsto (fun N : ℕ => C * (‖y‖ / ρ) ^ N) atTop (𝓝 (C * 0)) :=
      h1.const_mul C
    have h3 : Tendsto (fun N : ℕ => C * (‖y‖ / ρ) ^ N / (1 - ‖y‖ / ρ)) atTop
        (𝓝 (C * 0 / (1 - ‖y‖ / ρ))) := h2.div_const _
    simpa using h3
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hlim ε hε
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hN' := hN₀ N hN
  rw [dist_eq_norm, sub_zero] at hN'
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (htail hy N) ?_
  have hlt : ‖y‖ / ρ < 1 := (div_lt_one hρpos).2 hy
  rwa [Real.norm_of_nonneg (div_nonneg (mul_nonneg hC0
    (pow_nonneg (div_nonneg (norm_nonneg y) hρpos.le) N)) (by linarith))] at hN'

end Main

/-- **Composition with an analytic map is analytic on the Banach space `C(K,M)`.**

For a compact space `K` and an analytic map `F : M → E` between real normed spaces, the
composition operator `g ↦ F ∘ g` on `C(K, M)` is analytic, i.e. `C^ω`.

Suggested approach: reduce to `AnalyticAt ℝ (fun g : C(K,M) => F ∘ g) g₀` for each `g₀`, using
`contDiff_omega_iff_analyticOnNhd`.  Build the power series of the composition operator at `g₀`
from the power series of `F` at the points of `Set.range g₀`: the coefficient of order `n` is the
continuous `n`-multilinear map `(h₁,…,hₙ) ↦ (s ↦ p (g₀ s) n (h₁ s, …, hₙ s))`, where
`p x n = (n!)⁻¹ • iteratedFDeriv ℝ n F x` are the (canonical) Taylor coefficients of `F` at `x`.
Uniformity over `s ∈ K` comes from compactness of `Set.range g₀` together with the fact that
analytic functions have uniform Cauchy estimates on compact sets; see
`HasFPowerSeriesOnBall.changeOrigin`, `FormalMultilinearSeries.nnnorm_changeOrigin_le`,
`HasFPowerSeriesOnBall.uniform_geometric_approx'` and `HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum` in Mathlib. -/
theorem contDiff_omega_compContinuousMap {K M E : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : M → E} (hF : ContDiff ℝ ω F) :
    ContDiff ℝ ω (fun g : C(K, M) => (⟨F, hF.continuous⟩ : C(M, E)).comp g) :=
  contDiff_omega_compContinuousMap_aux (K := K) (M := M) (E := E) hF

end Commons.Analysis.ContinuousMap