import Mathlib
import Submission.Work.Lattice.poissonBasics

/-!
# A summable majorant for the translates of a Schwartz function

For a Schwartz function `f` on `ℝⁿ` and a base point `x₀`, the translates
`v ↦ f (x + v)` (`v ∈ ℤⁿ`) are uniformly dominated, for `x` near `x₀`, by a
single summable function of `v`.  This is the elementary input used to
justify term-by-term manipulations of the periodization `∑_{v ∈ ℤⁿ} f (x + v)`
(sum of a locally-uniformly dominated family of continuous functions).

The proof is soft: a Schwartz function decays faster than any polynomial,
`‖f y‖ ≤ C / (1 + ‖y‖) ^ (n+1)`, and for `x` in a small ball around `x₀` the
translated argument `x + v` still has norm at least `‖v‖ - M`.  Hence the
majorant `v ↦ C * (2M) ^ (n+1) / (1 + ‖v‖) ^ (n+1)` is both a bound and
summable over `ℤⁿ`.
-/

namespace Work.Lattice

open scoped SchwartzMap Topology

theorem exists_summable_bound_periodization {n : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (x₀ : Fin n → ℝ) :
    ∃ u : (Fin n → ℤ) → ℝ, Summable u ∧
      ∀ᶠ x in 𝓝 x₀, ∀ v, ‖f (WithLp.toLp 2 (x + Work.Lattice.intVecToReal v))‖ ≤ u v := by
  classical
  -- Decay bound for `f` with exponent `n + 1`.
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : EuclideanSpace ℝ (Fin n), ‖f y‖ ≤ C / (1 + ‖y‖) ^ (n + 1) := by
    refine ⟨2 ^ (n + 1) * ((Finset.Iic ((n + 1 : ℕ), 0)).sup
        fun m => SchwartzMap.seminorm ℝ m.1 m.2) f, by positivity, fun y => ?_⟩
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := ((n + 1 : ℕ), 0)) (k := n + 1) (n := 0) le_rfl le_rfl f y
    rw [norm_iteratedFDeriv_zero] at h
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact h
  -- Summability of the comparison series `∑_v ‖v‖ ^ (-(n+1))` over `ℤⁿ`.
  have hsumm_raw : Summable fun v : Fin n → ℤ =>
      ‖Work.Lattice.intVecToReal v‖ ^ (-((n + 1 : ℕ) : ℤ)) := by
    let L : Submodule ℤ (Fin n → ℝ) :=
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))
    haveI : DiscreteTopology L := by
      change DiscreteTopology (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))))
      infer_instance
    have hrank : Module.finrank ℤ L = n := by
      change Module.finrank ℤ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))) = n
      rw [ZLattice.rank ℝ]; simp
    have hL : Summable fun z : L => ‖z‖ ^ (-((n + 1 : ℕ) : ℤ)) :=
      ZLattice.summable_norm_zpow L (-((n + 1 : ℕ) : ℤ)) (by rw [hrank]; simp)
    have hmem : ∀ v : Fin n → ℤ, Work.Lattice.intVecToReal v ∈ L := by
      intro v
      change (fun i => (v i : ℝ)) ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))
      rw [show (fun i => (v i : ℝ))
            = ∑ i, (v i) • (Pi.basisFun ℝ (Fin n) i) from by
          funext j; simp [Pi.basisFun, Finset.sum_apply, Pi.single_apply]]
      exact Submodule.sum_mem _ (fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    have hinj : Function.Injective
        (fun v : Fin n → ℤ => (⟨Work.Lattice.intVecToReal v, hmem v⟩ : L)) := by
      intro v w h
      have h2 : Work.Lattice.intVecToReal v = Work.Lattice.intVecToReal w :=
        Subtype.ext_iff.mp h
      funext i
      have := congrFun h2 i
      simp only [intVecToReal_apply] at this
      exact_mod_cast this
    exact (hL.comp_injective hinj).congr (fun v => by
      rw [Function.comp_apply, Submodule.coe_norm])
  -- Replace `‖v‖` by `1 + ‖v‖` (harmless at the origin).
  have hsumm_one : Summable fun v : Fin n → ℤ =>
      (1 + ‖Work.Lattice.intVecToReal v‖) ^ (-((n + 1 : ℕ) : ℤ)) := by
    refine hsumm_raw.of_norm_bounded_eventually ?_
    rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton (0 : Fin n → ℤ)).subset ?_
    intro v hv
    by_contra hv0
    apply hv
    have ht : 0 < ‖Work.Lattice.intVecToReal v‖ := by
      rw [norm_pos_iff]
      intro hzero
      exact hv0 (funext fun i => by
        have := congrFun hzero i
        simpa [intVecToReal_apply] using this)
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast,
      Real.norm_of_nonneg (by positivity)]
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr
      (pow_le_pow_left₀ ht.le (by linarith) _)
  -- The pointwise majorant.
  set M : ℝ := ‖x₀‖ + 1 with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  have hM1 : 1 ≤ M := by rw [hM]; linarith [norm_nonneg x₀]
  let u : (Fin n → ℤ) → ℝ :=
    fun v => C * (2 * M) ^ (n + 1) / (1 + ‖Work.Lattice.intVecToReal v‖) ^ (n + 1)
  have hu : Summable u := by
    refine (hsumm_one.mul_left (C * (2 * M) ^ (n + 1))).congr (fun v => ?_)
    simp only [u, zpow_neg, zpow_natCast, div_eq_mul_inv]
  refine ⟨u, hu, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x₀ (show (0 : ℝ) < 1 by norm_num)] with x hx
  intro v
  have hx1 : ‖x - x₀‖ < 1 := by
    rw [Metric.mem_ball, dist_eq_norm] at hx; exact hx
  have hxM : ‖x‖ ≤ M := by
    have h1 : ‖x‖ ≤ ‖x₀‖ + ‖x - x₀‖ := by
      have := norm_add_le x₀ (x - x₀)
      rwa [show x₀ + (x - x₀) = x from by abel] at this
    rw [hM]; linarith
  set t : ℝ := ‖Work.Lattice.intVecToReal v‖ with ht
  set W : ℝ := ‖(WithLp.toLp 2 (x + Work.Lattice.intVecToReal v) :
    EuclideanSpace ℝ (Fin n))‖ with hW
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hWsup : ‖x + Work.Lattice.intVecToReal v‖ ≤ W := by
    rw [hW, pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    have h := PiLp.norm_apply_le
      (WithLp.toLp 2 (x + Work.Lattice.intVecToReal v) : EuclideanSpace ℝ (Fin n)) i
    simpa using h
  have ht_le_W : t - M ≤ W := by
    have h1 : ‖Work.Lattice.intVecToReal v‖ ≤ ‖x + Work.Lattice.intVecToReal v‖ + ‖x‖ := by
      have := norm_sub_le (x + Work.Lattice.intVecToReal v) x
      simpa using this
    have h2 : t ≤ W + M := by
      rw [ht]; linarith
    linarith
  have hf_bound : ‖f (WithLp.toLp 2 (x + Work.Lattice.intVecToReal v))‖ ≤
      C / (1 + W) ^ (n + 1) := by
    rw [hW]; exact hC _
  have hmain : ‖f (WithLp.toLp 2 (x + Work.Lattice.intVecToReal v))‖ ≤
      C * (2 * M) ^ (n + 1) / (1 + t) ^ (n + 1) := by
    by_cases hcase : t ≤ 2 * M - 1
    · -- Small `v`: the constant majorant `C` suffices.
      have hleC : C / (1 + W) ^ (n + 1) ≤ C := by
        rw [div_le_iff₀ (by positivity)]
        have h1 : (1 : ℝ) ≤ (1 + W) ^ (n + 1) := one_le_pow₀ (by linarith)
        nlinarith [hC0, h1]
      have hCu : C ≤ C * (2 * M) ^ (n + 1) / (1 + t) ^ (n + 1) := by
        rw [le_div_iff₀ (by positivity)]
        have hle : (1 + t) ^ (n + 1) ≤ (2 * M) ^ (n + 1) :=
          pow_le_pow_left₀ (by linarith) (by linarith) _
        nlinarith [hle, hC0]
      linarith
    · -- Large `v`: the decaying majorant dominates.
      have hcase' : 2 * M - 1 ≤ t := le_of_lt (not_le.mp hcase)
      have hkey : (1 + t) / 2 ≤ 1 + W := by linarith
      have hkey2 : 1 + t ≤ 2 * M * (1 + W) := by nlinarith [hkey, hM1, hW0]
      have hpow : (1 + t) ^ (n + 1) ≤ (2 * M) ^ (n + 1) * (1 + W) ^ (n + 1) := by
        have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + t) hkey2 (n + 1)
        rwa [mul_pow] at this
      have h4 : C / (1 + W) ^ (n + 1) ≤ C * (2 * M) ^ (n + 1) / (1 + t) ^ (n + 1) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hpow, hC0]
      linarith
  have hu_v : C * (2 * M) ^ (n + 1) / (1 + t) ^ (n + 1) = u v := by
    simp only [u]; rw [ht]
  rwa [hu_v] at hmain
