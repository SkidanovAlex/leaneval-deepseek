import Mathlib
import Submission.Work.ThomBordism.Transversality.Sard.Strat
import Submission.Work.ThomBordism.Transversality.Sard.volume_eq_zero_of_dimH_lt

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The flat stratum is null, locally (the flat case of Sard's theorem on an open set)

`Sard.volume_image_eq_zero_of_isFlat` proves: for a **globally** `C^K` map `f : ℝⁿ → ℝᵐ` whose
iterated derivatives of orders `1, …, K-1` vanish on a **bounded** set `S`, and with `K·m > n`, the
image `f '' S` is Lebesgue-null.  The present file removes both global hypotheses, in the form
needed by the stratification argument of Sard's theorem for a map that is only `C^K` on an open set
`U ⊆ ℝⁿ`: the `(K-1)`-flat set `Zk f (K-1) ∩ U` is typically unbounded and `f` is only smooth on
`U`.

Mathematically nothing changes: flatness of order `K-1` makes `f` *locally* Hölder on `S` with
exponent `K`, and a locally Hölder map raises Hausdorff dimension at most by the factor `1/K`, so
`dimH (f '' S) ≤ dimH S / K ≤ n/K < m`.  The point of the file is that the Hölder estimate is a
**local** statement, so no global bound on the derivatives and no boundedness of `S` is needed.

The pieces:

* `localFlat_taylor_bound` — the flat Taylor estimate of `Sard.norm_sub_le_of_iteratedFDeriv_eq_zero`
  on a ball of **arbitrary radius** `R` (instead of the unit ball), with `f` only required to be
  `C^K` on a set containing that ball: the input of the Hölder estimate at scale `R`.
* `localFlat_locally_holder` — flatness of order `K-1` on `S` makes `f` locally `K`-Hölder on `S`.
* `localFlat_volume_eq_zero` — the dimension argument (`volume_eq_zero_of_dimH_lt`).
* `localFlat` — the requested statement.
-/

open scoped Topology NNReal
open MeasureTheory Metric Set

namespace Work.ThomBordism.Transversality.Sard

/-- **The flat Taylor estimate on a ball of radius `R`.**  If `f` is `C^K` on a set containing the
closed ball `B = closedBall x₀ R`, all iterated derivatives of `f` of orders `1, …, K-1` vanish at
`x₀`, and `C` bounds the `K`-th iterated derivative on `B`, then for `y ∈ B`
`‖f y - f x₀‖ ≤ C ‖y - x₀‖^K`.

This is `Sard.norm_sub_le_of_iteratedFDeriv_eq_zero` with the unit ball replaced by `B` and the
global smoothness hypothesis replaced by `ContDiffOn` on a set containing `B` (Mathlib's Taylor
formula with integral remainder only needs `ContDiffAt` along the segment, which the openness of the
ambient set supplies). -/
theorem localFlat_taylor_bound {n m K : ℕ} (hK : 1 ≤ K)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hf : ContDiffOn ℝ K f U)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hflat : ∀ j, 1 ≤ j → j < K → iteratedFDeriv ℝ j f x₀ = 0)
    {C R : ℝ} (hR : Metric.closedBall x₀ R ⊆ U)
    (hC' : ∀ y ∈ Metric.closedBall x₀ R, ‖iteratedFDeriv ℝ K f y‖ ≤ C)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ Metric.closedBall x₀ R) :
    ‖f y - f x₀‖ ≤ C * ‖y - x₀‖ ^ K := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  -- the displacement and its size
  set v : EuclideanSpace ℝ (Fin n) := y - x₀ with hv
  have hvy : y = x₀ + v := by rw [hv]; abel
  have hvnorm : ‖v‖ ≤ R := by
    rw [hv]
    simpa [dist_eq_norm] using hy
  -- Taylor's formula with integral remainder along the segment from `x₀` to `y`
  have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, x₀ + t • v ∈ Metric.closedBall x₀ R := by
    intro t ht
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    calc t * ‖v‖ ≤ 1 * R := mul_le_mul ht.2 hvnorm (norm_nonneg _) zero_le_one
      _ = R := one_mul R
  have htaylor := map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := x₀) (y := v) (n := k)
    (fun t ht => hf.contDiffAt (hU.mem_nhds (hR (hseg t ht))))
  -- the Taylor sum collapses to `f x₀` because the intermediate derivatives vanish
  have hsum : (∑ j ∈ Finset.range (k + 1), (j.factorial : ℝ)⁻¹ •
      (iteratedFDeriv ℝ j f x₀) (fun _ => v)) = f x₀ := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j hj hj0
      have hjlt : j < k + 1 := Finset.mem_range.mp hj
      have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      rw [hflat j hj1 hjlt]
      simp
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega : 0 < k + 1)) h
  -- the integrand is bounded by `C * ‖v‖^(k+1)`
  have hpt : ∀ t ∈ Set.uIoc (0:ℝ) 1,
      ‖(1 - t) ^ k • (iteratedFDeriv ℝ (k + 1) f (x₀ + t • v)) (fun _ => v)‖
        ≤ C * ‖v‖ ^ (k + 1) := by
    intro t ht
    have ht0 : 0 ≤ t := by
      have h := ht.1
      simp only [min_eq_left zero_le_one] at h
      linarith
    have ht1 : t ≤ 1 := by
      have h := ht.2
      simp only [max_eq_right zero_le_one] at h
      linarith
    have h1t : 0 ≤ 1 - t := by linarith
    have h3 : ‖(iteratedFDeriv ℝ (k + 1) f (x₀ + t • v)) (fun _ => v)‖ ≤ C * ‖v‖ ^ (k + 1) := by
      calc ‖(iteratedFDeriv ℝ (k + 1) f (x₀ + t • v)) (fun _ => v)‖
          ≤ ‖iteratedFDeriv ℝ (k + 1) f (x₀ + t • v)‖ * ∏ _ : Fin (k + 1), ‖v‖ :=
            ContinuousMultilinearMap.le_opNorm _ _
        _ = ‖iteratedFDeriv ℝ (k + 1) f (x₀ + t • v)‖ * ‖v‖ ^ (k + 1) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ C * ‖v‖ ^ (k + 1) :=
            mul_le_mul_of_nonneg_right (hC' _ (hseg t ⟨ht0, ht1⟩)) (by positivity)
    have h1 : (1 - t) ^ k ≤ 1 := pow_le_one₀ h1t (by linarith)
    have h2 : 0 ≤ (1 - t) ^ k := pow_nonneg h1t k
    calc ‖(1 - t) ^ k • (iteratedFDeriv ℝ (k + 1) f (x₀ + t • v)) (fun _ => v)‖
        = (1 - t) ^ k * ‖(iteratedFDeriv ℝ (k + 1) f (x₀ + t • v)) (fun _ => v)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h2]
      _ ≤ 1 * (C * ‖v‖ ^ (k + 1)) := mul_le_mul h1 h3 (norm_nonneg _) zero_le_one
      _ = C * ‖v‖ ^ (k + 1) := one_mul _
  have hI : ‖∫ t in (0:ℝ)..1,
      (1 - t) ^ k • (iteratedFDeriv ℝ (k + 1) f (x₀ + t • v)) (fun _ => v)‖
      ≤ C * ‖v‖ ^ (k + 1) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
      (C := C * ‖v‖ ^ (k + 1)) hpt
    simpa using this
  have hfin : f y - f x₀ = (k.factorial : ℝ)⁻¹ • ∫ t in (0:ℝ)..1,
      (1 - t) ^ k • (iteratedFDeriv ℝ (k + 1) f (x₀ + t • v)) (fun _ => v) := by
    rw [hvy, htaylor, hsum, add_sub_cancel_left]
  rw [hfin, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (k.factorial : ℝ))]
  have hfac : ((k.factorial : ℝ))⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    exact_mod_cast (show (1:ℕ) ≤ k.factorial from Nat.succ_le_of_lt (Nat.factorial_pos k))
  calc (k.factorial : ℝ)⁻¹ * ‖∫ t in (0:ℝ)..1,
        (1 - t) ^ k • (iteratedFDeriv ℝ (k + 1) f (x₀ + t • v)) (fun _ => v)‖
      ≤ 1 * (C * ‖v‖ ^ (k + 1)) := mul_le_mul hfac hI (norm_nonneg _) zero_le_one
    _ = C * ‖y - x₀‖ ^ (k + 1) := by rw [one_mul, hv]

/-- **Flatness of order `K-1` makes `f` locally `K`-Hölder.**  If `f` is `C^K` on an open set `U`
and all iterated derivatives of `f` of orders `1, …, K-1` vanish at every point of `S ⊆ U`, then at
every point of `S` the map `f` is Hölder of exponent `K` on a relative neighbourhood of that point.

This is the local form of the Hölder estimate behind the flat case of Sard's theorem: the
neighbouring constant is the maximum of `‖iteratedFDeriv ℝ K f‖` on a ball around the point of `S`
contained in `U`. -/
theorem localFlat_locally_holder {n m K : ℕ} (hK : 1 ≤ K)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hf : ContDiffOn ℝ K f U)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSU : S ⊆ U)
    (hflat : ∀ x ∈ S, ∀ j, 1 ≤ j → j < K → iteratedFDeriv ℝ j f x = 0) :
    ∀ x ∈ S, ∃ C : ℝ≥0, ∃ t ∈ 𝓝[S] x, HolderOnWith C (K : ℝ≥0) f t := by
  intro x hx
  -- a ball around `x` contained in `U`
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hSU hx))
  set ρ : ℝ := ε / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  have hρU : Metric.closedBall x ρ ⊆ U := fun z hz =>
    hεU (Metric.closedBall_subset_ball (by rw [hρdef]; linarith) hz)
  -- the derivative of order `K` is continuous on `U`, hence bounded on the compact ball
  have hcontU : ContinuousOn (iteratedFDeriv ℝ K f) U :=
    ContinuousOn.continuousOn_iteratedFDeriv hf hU le_rfl
  have hcont : ContinuousOn (fun z => ‖iteratedFDeriv ℝ K f z‖) (Metric.closedBall x ρ) :=
    (hcontU.mono hρU).norm
  have hne : (Metric.closedBall x ρ).Nonempty := ⟨x, Metric.mem_closedBall_self (le_of_lt hρ)⟩
  obtain ⟨xM, -, hmax⟩ := (isCompact_closedBall x ρ).exists_isMaxOn hne hcont
  set C : ℝ := ‖iteratedFDeriv ℝ K f xM‖ with hCdef
  have hC0 : 0 ≤ C := norm_nonneg _
  have hCmax : ∀ z ∈ Metric.closedBall x ρ, ‖iteratedFDeriv ℝ K f z‖ ≤ C := fun z hz => hmax hz
  have hcoe : ENNReal.ofReal C = (C.toNNReal : ENNReal) := by
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal C hC0]
  refine ⟨C.toNNReal, S ∩ Metric.closedBall x (ρ / 3), ?_, ?_⟩
  · -- the relative neighbourhood
    exact Filter.inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x (by linarith)))
  · intro x' hx' y hy
    obtain ⟨hx'S, hx'd⟩ := hx'
    obtain ⟨hyS, hyd⟩ := hy
    rw [Metric.mem_closedBall] at hx'd hyd
    have hyd' : dist x y ≤ ρ / 3 := by rw [dist_comm]; exact hyd
    -- all points of the relative neighbourhood are within `ρ` of `x`
    have hxy : dist x' y ≤ 2 * ρ / 3 := by
      calc dist x' y ≤ dist x' x + dist x y := dist_triangle x' x y
        _ ≤ ρ / 3 + ρ / 3 := add_le_add hx'd hyd'
        _ = 2 * ρ / 3 := by ring
    -- the ball of radius `dist x' y` around `x'` lies in the ball on which `C` bounds `d^K f`
    have hball : Metric.closedBall x' (dist x' y) ⊆ Metric.closedBall x ρ := by
      intro z hz
      rw [Metric.mem_closedBall] at hz ⊢
      calc dist z x ≤ dist z x' + dist x' x := dist_triangle z x' x
        _ ≤ dist x' y + ρ / 3 := add_le_add hz hx'd
        _ ≤ 2 * ρ / 3 + ρ / 3 := add_le_add hxy le_rfl
        _ = ρ := by ring
    -- the flat Taylor estimate at `x'`
    have hmem : y ∈ Metric.closedBall x' (dist x' y) :=
      Metric.mem_closedBall.mpr (by rw [dist_comm])
    have hT := localFlat_taylor_bound (y := y) hK hU hf (hflat x' hx'S)
      (fun z hz => hρU (hball hz)) (fun z hz => hCmax z (hball hz)) hmem
    have hreal : dist (f x') (f y) ≤ C * dist x' y ^ K := by
      rw [dist_comm (f x') (f y), dist_comm x' y, dist_eq_norm, dist_eq_norm]
      exact hT
    calc edist (f x') (f y)
        = ENNReal.ofReal (dist (f x') (f y)) := edist_dist _ _
      _ ≤ ENNReal.ofReal (C * dist x' y ^ K) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal C * ENNReal.ofReal (dist x' y ^ K) := ENNReal.ofReal_mul hC0
      _ = (C.toNNReal : ENNReal) * (ENNReal.ofReal (dist x' y)) ^ K := by
            rw [ENNReal.ofReal_pow dist_nonneg, hcoe]
      _ = (C.toNNReal : ENNReal) * ENNReal.ofReal (dist x' y) ^ ((K : ℝ≥0) : ℝ) := by
            rw [← ENNReal.rpow_natCast, NNReal.coe_natCast]
      _ = (C.toNNReal : ENNReal) * edist x' y ^ ((K : ℝ≥0) : ℝ) := by rw [edist_dist]

/-- **The flat case of Sard's theorem on an open set.**  If `f : ℝⁿ → ℝᵐ` is `C^K` on an open set
`U`, the iterated derivatives of `f` of orders `1, …, K-1` vanish at every point of a set
`S ⊆ U`, and `K·m > n`, then `f '' S` is Lebesgue-null.

Neither `S` is assumed bounded nor `f` globally `C^K`: the estimate is local, so Hausdorff
dimension does the bookkeeping. -/
theorem localFlat_volume_eq_zero {n m K : ℕ} (hK : 1 ≤ K) (hKm : n < K * m)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hf : ContDiffOn ℝ K f U)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSU : S ⊆ U)
    (hflat : ∀ x ∈ S, ∀ j, 1 ≤ j → j < K → iteratedFDeriv ℝ j f x = 0) :
    MeasureTheory.volume (f '' S) = 0 := by
  refine volume_eq_zero_of_dimH_lt (d := m) ?_
  have hholder := localFlat_locally_holder hK hU hf hSU hflat
  have hdim_image : dimH (f '' S) ≤ dimH S / (K : ℝ≥0) :=
    dimH_image_le_of_locally_holder_on (by exact_mod_cast hK) hholder
  have hdimS : dimH S ≤ (n : ENNReal) := by
    calc dimH S ≤ dimH (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := dimH_mono (Set.subset_univ S)
      _ = (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ENNReal) := Real.dimH_univ_eq_finrank _
      _ = (n : ENNReal) := by simp
  have hlt : (n : ENNReal) / (K : ENNReal) < (m : ENNReal) := by
    rw [ENNReal.div_lt_iff (Or.inl (by positivity)) (Or.inl (ENNReal.natCast_ne_top K))]
    rw [← Nat.cast_mul]
    exact_mod_cast (Nat.mul_comm K m ▸ hKm)
  refine lt_of_le_of_lt ?_ hlt
  calc dimH (f '' S) ≤ dimH S / (K : ℝ≥0) := hdim_image
    _ ≤ (n : ENNReal) / (K : ℝ≥0) := ENNReal.div_le_div_right hdimS _
    _ = (n : ENNReal) / (K : ENNReal) := by simp

theorem localFlat {n m K : ℕ} (hK : 1 ≤ K) (hKm : n < K * m)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hf : ContDiffOn ℝ K f U) :
    MeasureTheory.volume (f '' (Work.ThomBordism.Transversality.Zk f (K-1) ∩ U)) = 0 :=
  localFlat_volume_eq_zero hK hKm hU hf (fun _ hx => hx.2)
    (fun x hx j hj1 hjK => hx.1 j hj1 (by omega))

end Work.ThomBordism.Transversality.Sard
