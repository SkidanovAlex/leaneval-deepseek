import Mathlib
import Submission.Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_open_of_locallyBounded
import Submission.Commons.Analysis.Complex.weyl_dbar
import Submission.Commons.Measure.EuclideanSpace.integral_fderiv_mul_weighted_eq_neg

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

noncomputable section
open MeasureTheory Metric Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace Commons.Analysis.Complex.Montel

/-! ## Bounds coming from the local `L²` estimates -/

/-- The pointwise mean-value inequality on a polydisc, in the form used below. -/
private theorem norm_sq_le_of_integral_bound {d : ℕ} {g : (Fin d → ℂ) → ℂ}
    (hg : Differentiable ℂ g) {z : Fin d → ℂ} {r M : ℝ} (hr : 0 < r)
    (hM : ∫ w in Metric.closedBall z r, ‖g w‖ ^ 2
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) ≤ M) :
    ‖g z‖ ^ 2 ≤ ((Real.pi * r ^ 2) ^ d)⁻¹ * M := by
  have h1 := Commons.Analysis.Complex.norm_le_integral_of_differentiable_complex hg (z := z) hr
  rw [Commons.Analysis.Complex.polydisc_volume z hr] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_left hM (by positivity))

/-- Uniform bound on a closed ball, from the local `L²` bounds. -/
private theorem closedBall_bound_of_integral_bound {d : ℕ} {f : ℕ → (Fin d → ℂ) → ℂ}
    (hf : ∀ n, Differentiable ℂ (f n))
    (hb : ∀ (z : Fin d → ℂ) (R : ℝ), ∃ M : ℝ, ∀ n : ℕ,
      ∫ w in Metric.closedBall z R, ‖f n w‖ ^ 2
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) ≤ M) :
    ∀ R : ℝ, ∃ C : ℝ, ∀ n, ∀ y ∈ Metric.closedBall (0 : Fin d → ℂ) R, ‖f n y‖ ≤ C := by
  intro R
  obtain ⟨M, hM⟩ := hb 0 (R + 1)
  refine ⟨Real.sqrt ((Real.pi ^ d)⁻¹ * max M 0), fun n y hy => ?_⟩
  have hπ : (Real.pi * (1 : ℝ) ^ 2) ^ d = Real.pi ^ d := by rw [one_pow, mul_one]
  have hint : IntegrableOn (fun w : Fin d → ℂ => ‖f n w‖ ^ 2)
      (Metric.closedBall (0 : Fin d → ℂ) (R + 1)) (MeasureTheory.volume) :=
    (((hf n).continuous.norm.pow 2).continuousOn).integrableOn_compact
      (isCompact_closedBall 0 (R + 1))
  have hmono : ∫ w in Metric.closedBall y (1 : ℝ), ‖f n w‖ ^ 2 ≤ M := by
    refine le_trans ?_ (hM n)
    refine setIntegral_mono_set hint ?_ ?_
    · exact Filter.Eventually.of_forall fun w => by positivity
    · refine Filter.Eventually.of_forall fun w (hw : w ∈ Metric.closedBall y 1) => ?_
      have hw' : dist w y ≤ 1 := Metric.mem_closedBall.mp hw
      have hy' : dist y 0 ≤ R := Metric.mem_closedBall.mp hy
      exact Metric.mem_closedBall.mpr (by
        calc dist w 0 ≤ dist w y + dist y 0 := dist_triangle w y 0
          _ ≤ 1 + R := by linarith
          _ = R + 1 := by ring)
  have h2 := norm_sq_le_of_integral_bound (hf n) (z := y) (r := 1) one_pos hmono
  rw [hπ] at h2
  have h3 : ‖f n y‖ ^ 2 ≤ (Real.pi ^ d)⁻¹ * max M 0 :=
    le_trans h2 (mul_le_mul_of_nonneg_left (le_max_left M 0) (by positivity))
  have h4 : Real.sqrt (‖f n y‖ ^ 2) ≤ Real.sqrt ((Real.pi ^ d)⁻¹ * max M 0) :=
    Real.sqrt_le_sqrt h3
  rwa [Real.sqrt_sq (norm_nonneg _)] at h4

/-- Uniform Lipschitz bound on a closed ball, from the local `L²` bounds. -/
private theorem closedBall_lipschitz_bound_of_integral_bound {d : ℕ} {f : ℕ → (Fin d → ℂ) → ℂ}
    (hf : ∀ n, Differentiable ℂ (f n))
    (hb : ∀ (z : Fin d → ℂ) (R : ℝ), ∃ M : ℝ, ∀ n : ℕ,
      ∫ w in Metric.closedBall z R, ‖f n w‖ ^ 2
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) ≤ M) :
    ∀ R : ℝ, ∃ L : ℝ, ∀ n, ∀ y ∈ Metric.closedBall (0 : Fin d → ℂ) R,
      ∀ z ∈ Metric.closedBall (0 : Fin d → ℂ) R, ‖f n y - f n z‖ ≤ L * ‖y - z‖ := by
  intro R
  obtain ⟨M, hM⟩ := hb 0 (R + 1)
  obtain ⟨C1, hC1pos, hC1⟩ :=
    Commons.Analysis.Complex.fderiv_bound_uniform_of_differentiable_complex (d := d) (R := 1) one_pos
  refine ⟨Real.sqrt (C1 * max M 0), fun n y hy z hz => ?_⟩
  have hbnd : ∀ u ∈ Metric.closedBall (0 : Fin d → ℂ) R,
      ‖fderiv ℂ (f n) u‖ ≤ Real.sqrt (C1 * max M 0) := by
    intro u hu
    have hint : IntegrableOn (fun w : Fin d → ℂ => ‖f n w‖ ^ 2)
        (Metric.closedBall (0 : Fin d → ℂ) (R + 1)) (MeasureTheory.volume) :=
      (((hf n).continuous.norm.pow 2).continuousOn).integrableOn_compact
        (isCompact_closedBall 0 (R + 1))
    have hmono : ∫ w in Metric.closedBall u (1 : ℝ), ‖f n w‖ ^ 2 ≤ M := by
      refine le_trans ?_ (hM n)
      refine setIntegral_mono_set hint ?_ ?_
      · exact Filter.Eventually.of_forall fun w => by positivity
      · refine Filter.Eventually.of_forall fun w (hw : w ∈ Metric.closedBall u 1) => ?_
        have hw' : dist w u ≤ 1 := Metric.mem_closedBall.mp hw
        have hu' : dist u 0 ≤ R := Metric.mem_closedBall.mp hu
        exact Metric.mem_closedBall.mpr (by
          calc dist w 0 ≤ dist w u + dist u 0 := dist_triangle w u 0
            _ ≤ 1 + R := by linarith
            _ = R + 1 := by ring)
    have h2 := hC1 (f n) (hf n) u
    have h3 : ‖fderiv ℂ (f n) u‖ ^ 2 ≤ C1 * max M 0 :=
      le_trans h2 (mul_le_mul_of_nonneg_left (le_trans hmono (le_max_left M 0)) hC1pos.le)
    have h4 : Real.sqrt (‖fderiv ℂ (f n) u‖ ^ 2) ≤ Real.sqrt (C1 * max M 0) :=
      Real.sqrt_le_sqrt h3
    rwa [Real.sqrt_sq (norm_nonneg _)] at h4
  have := Convex.norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℂ) (s := Metric.closedBall (0 : Fin d → ℂ) R) (f := f n)
    (fun x _ => hf n x) hbnd (convex_closedBall 0 R) hz hy
  simpa [dist_eq_norm] using this

/-! ## Montel extraction (Arzelà–Ascoli + diagonal) along `K_k = closedBall 0 (k+1)` -/

private theorem exists_subseq_tendstoLocallyUniformlyOn_of_bounded_lipschitz {d : ℕ}
    {f : ℕ → (Fin d → ℂ) → ℂ}
    (hc : ∀ n, Continuous (f n))
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ n, ∀ y ∈ Metric.closedBall (0 : Fin d → ℂ) R, ‖f n y‖ ≤ C)
    (hl : ∀ R : ℝ, ∃ L : ℝ, ∀ n, ∀ y ∈ Metric.closedBall (0 : Fin d → ℂ) R,
        ∀ z ∈ Metric.closedBall (0 : Fin d → ℂ) R, ‖f n y - f n z‖ ≤ L * ‖y - z‖) :
    ∃ (φ : ℕ → ℕ) (g : (Fin d → ℂ) → ℂ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g Filter.atTop Set.univ := by
  classical
  let r : ℕ → ℝ := fun k => (k : ℝ) + 1
  let K : ℕ → Set (Fin d → ℂ) := fun k => Metric.closedBall 0 (r k)
  have hK_compact : ∀ k, IsCompact (K k) := fun k => isCompact_closedBall 0 (r k)
  haveI hKcpt : ∀ k, CompactSpace (K k) := fun k => isCompact_iff_compactSpace.mp (hK_compact k)
  let Fn : (k : ℕ) → ℕ → (K k →ᵇ ℂ) := fun k n =>
    BoundedContinuousFunction.mkOfCompact
      { toFun := fun x : K k => f n x
        continuous_toFun := ((hc n).continuousOn.mono (Set.subset_univ (K k))).domRestrict }
  have hFn_apply : ∀ (k n : ℕ) (x : K k), Fn k n x = f n x := by
    intro k n x
    simp only [Fn, BoundedContinuousFunction.mkOfCompact_apply]; rfl
  have hlip : ∀ k n, ∀ z w : Fin d → ℂ, z ∈ K k → w ∈ K k →
      ‖f n z - f n w‖ ≤ (Classical.choose (hl (r k))) * ‖z - w‖ :=
    fun k n z w hz hw => (Classical.choose_spec (hl (r k))) n z hz w hw
  have heqcont : ∀ k, Equicontinuous ((↑) : Set.range (Fn k) → K k → ℂ) := by
    intro k
    refine Metric.equicontinuous_of_continuity_modulus
      (fun t : ℝ => (Classical.choose (hl (r k))) * t) ?_ _ ?_
    · have : Tendsto (fun t : ℝ => (Classical.choose (hl (r k))) * t) (𝓝 0)
          (𝓝 ((Classical.choose (hl (r k))) * 0)) := tendsto_const_nhds.mul tendsto_id
      simpa using this
    · intro x y i
      obtain ⟨n, hn⟩ := i.2
      have hcoe : (i : K k → ℂ) = fun x : K k => f n (x : Fin d → ℂ) := by
        rw [← hn]; funext x; exact hFn_apply k n x
      rw [hcoe]
      have h := hlip k n (x : Fin d → ℂ) (y : Fin d → ℂ) x.2 y.2
      simpa [Subtype.dist_eq, dist_eq_norm] using h
  have hcompact : ∀ k, IsCompact (closure (Set.range (Fn k))) := by
    intro k
    refine BoundedContinuousFunction.arzela_ascoli
      (Metric.closedBall (0 : ℂ) (Classical.choose (hb (r k))))
      (isCompact_closedBall 0 _) (Set.range (Fn k)) ?_ (heqcont k)
    intro g x hg
    obtain ⟨n, hn⟩ := hg
    rw [← hn, hFn_apply k n x]
    simpa [Metric.mem_closedBall, dist_eq_norm] using
      (Classical.choose_spec (hb (r k))) n (x : Fin d → ℂ) x.2
  have exists_good : ∀ (k : ℕ) (u : ℕ → ℕ), ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ a : K k →ᵇ ℂ, Tendsto (fun n => Fn k (u (ψ n))) Filter.atTop (𝓝 a) := by
    intro k u
    have hmem : ∀ n, Fn k (u n) ∈ closure (Set.range (Fn k)) :=
      fun n => subset_closure (Set.mem_range_self (u n))
    obtain ⟨a, _, ψ, hψ, hψlim⟩ := (hcompact k).tendsto_subseq hmem
    exact ⟨ψ, hψ, a, by simpa [Function.comp_def] using hψlim⟩
  let psi : ℕ → (ℕ → ℕ) → (ℕ → ℕ) := fun k u => Classical.choose (exists_good k u)
  have psi_strict : ∀ (k : ℕ) (u : ℕ → ℕ), StrictMono (psi k u) := by
    intro k u
    exact (Classical.choose_spec (exists_good k u)).1
  have psi_conv : ∀ (k : ℕ) (u : ℕ → ℕ), ∃ a : K k →ᵇ ℂ,
      Tendsto (fun n => Fn k (u (psi k u n))) Filter.atTop (𝓝 a) := by
    intro k u
    exact (Classical.choose_spec (exists_good k u)).2
  let phi : ℕ → (ℕ → ℕ) :=
    Nat.rec (motive := fun _ => ℕ → ℕ) id (fun k rec => rec ∘ psi (k + 1) rec)
  have phi_zero : phi 0 = id := rfl
  have phi_succ : ∀ k, phi (k + 1) = phi k ∘ psi (k + 1) (phi k) := by
    intro k
    rfl
  have phi_strict : ∀ k, StrictMono (phi k) := by
    intro k
    induction k with
    | zero => rw [phi_zero]; exact strictMono_id
    | succ k ih => rw [phi_succ k]; exact ih.comp (psi_strict (k + 1) (phi k))
  have phi_range : ∀ n m, m ≤ n → ∀ i, ∃ k ≥ i, phi n i = phi m k := by
    intro n
    induction n with
    | zero =>
        intro m hm i
        have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
        subst hm0
        exact ⟨i, le_refl i, rfl⟩
    | succ n ih =>
        intro m hm i
        rcases Nat.lt_or_ge m (n + 1) with hlt | hge
        · have hmle : m ≤ n := Nat.le_of_lt_succ hlt
          have happ : phi (n + 1) i = phi n (psi (n + 1) (phi n) i) := by
            rw [phi_succ n]; rfl
          obtain ⟨k, hk, hkeq⟩ := ih m hmle (psi (n + 1) (phi n) i)
          refine ⟨k, ?_, ?_⟩
          · have : i ≤ psi (n + 1) (phi n) i := (psi_strict (n + 1) (phi n)).id_le i
            omega
          · rw [happ, hkeq]
        · have hmn : m = n + 1 := le_antisymm hm hge
          subst hmn
          exact ⟨i, le_refl i, rfl⟩
  let diag : ℕ → ℕ := fun n => phi n n
  have diag_strict : StrictMono diag := by
    apply strictMono_nat_of_lt_succ
    intro n
    have hsucc : phi (n + 1) = phi n ∘ psi (n + 1) (phi n) := phi_succ n
    have hidle : n + 1 ≤ psi (n + 1) (phi n) (n + 1) := (psi_strict (n + 1) (phi n)).id_le (n + 1)
    have h1 : phi n (n + 1) ≤ phi n (psi (n + 1) (phi n) (n + 1)) :=
      (phi_strict n).monotone hidle
    have h2 : phi n n < phi n (n + 1) := (phi_strict n) (Nat.lt_succ_self n)
    have hdiag : diag (n + 1) = phi n (psi (n + 1) (phi n) (n + 1)) := by
      simp only [diag]
      rw [hsucc]; rfl
    rw [hdiag]
    exact lt_of_lt_of_le h2 h1
  let Alim : (j : ℕ) → K (j + 1) →ᵇ ℂ := fun j => Classical.choose (psi_conv (j + 1) (phi j))
  have Alim_spec : ∀ j, Tendsto (fun n => Fn (j + 1) (phi j (psi (j + 1) (phi j) n)))
      Filter.atTop (𝓝 (Alim j)) :=
    fun j => Classical.choose_spec (psi_conv (j + 1) (phi j))
  have Alim_spec' : ∀ j, Tendsto (fun n => Fn (j + 1) (phi (j + 1) n))
      Filter.atTop (𝓝 (Alim j)) := by
    intro j
    have h := Alim_spec j
    simpa [phi_succ j, Function.comp_apply] using h
  have diag_conv : ∀ j, Tendsto (fun n => Fn (j + 1) (diag n)) Filter.atTop (𝓝 (Alim j)) := by
    intro j
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (Alim_spec' j) ε hε
    refine ⟨max (j + 1) N, ?_⟩
    intro n hn
    have hn1 : j + 1 ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : N ≤ n := le_trans (le_max_right _ _) hn
    obtain ⟨k, hk, hkeq⟩ := phi_range n (j + 1) hn1 n
    have heq : Fn (j + 1) (diag n) = Fn (j + 1) (phi (j + 1) k) := by
      simp only [diag, hkeq]
    rw [heq]
    exact hN k (le_trans hn2 hk)
  have hAunifsub : ∀ j, TendstoUniformly (fun n (x : K (j + 1)) => f (diag n) x)
      (fun x => (Alim j) x) Filter.atTop := by
    intro j
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have h := diag_conv j
    rw [Metric.tendsto_atTop] at h
    obtain ⟨N, hN⟩ := h ε hε
    filter_upwards [eventually_ge_atTop N] with n hn
    intro x
    have hdist := BoundedContinuousFunction.dist_coe_le_dist (f := Alim j)
      (g := Fn (j + 1) (diag n)) x
    calc dist ((Alim j) x) (f (diag n) x)
        = dist ((Alim j) x) ((Fn (j + 1) (diag n)) x) := by rw [hFn_apply]
      _ ≤ dist (Alim j) (Fn (j + 1) (diag n)) := hdist
      _ = dist (Fn (j + 1) (diag n)) (Alim j) := dist_comm _ _
      _ < ε := hN n hn
  let g : (Fin d → ℂ) → ℂ := fun z => Filter.limUnder Filter.atTop (fun n => f (diag n) z)
  have hg_eq : ∀ (j : ℕ) (x : K (j + 1)), g x = (Alim j) x := by
    intro j x
    have hpt : Tendsto (fun n => f (diag n) (x : Fin d → ℂ)) Filter.atTop (𝓝 ((Alim j) x)) :=
      (hAunifsub j).tendsto_at x
    show Filter.limUnder Filter.atTop (fun n => f (diag n) (x : Fin d → ℂ)) = (Alim j) x
    exact Filter.Tendsto.limUnder_eq hpt
  have hgunifsub : ∀ j, TendstoUniformly (fun n (x : K (j + 1)) => f (diag n) x)
      (fun x : K (j + 1) => g x) Filter.atTop := by
    intro j
    rw [← tendstoUniformlyOn_univ]
    refine (tendstoUniformlyOn_univ.mpr (hAunifsub j)).congr_right fun x _ => (hg_eq j x).symm
  have hgunif : ∀ j, TendstoUniformlyOn (fun n => f (diag n)) g Filter.atTop (K (j + 1)) := by
    intro j
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    simpa [Function.comp_def] using hgunifsub j
  refine ⟨diag, g, diag_strict, ?_⟩
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds ?_
  intro x hx
  obtain ⟨j, hj⟩ : ∃ j : ℕ, ‖x‖ < r (j + 1) := by
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    exact ⟨n, by simp only [r]; push_cast; linarith⟩
  have hj' : ‖x‖ < r (j + 1) := hj
  refine ⟨K (j + 1), ?_, hgunif j⟩
  apply nhdsWithin_le_nhds
  refine Filter.mem_of_superset (Metric.ball_mem_nhds x (sub_pos.mpr hj')) ?_
  intro y hy
  simp only [K, Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have hyx : ‖y - x‖ < r (j + 1) - ‖x‖ := by
    simpa [dist_eq_norm] using (Metric.mem_ball.mp hy)
  have hy' : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
    calc ‖y‖ = ‖x + (y - x)‖ := by ring_nf
      _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
  linarith

/-! ## Differentiability of a locally uniform limit of holomorphic functions -/

/-- The Cauchy–Riemann equation, at the level of the real Fréchet derivative. -/
private theorem fderiv_apply_single_I {d : ℕ} {u : (Fin d → ℂ) → ℂ} (hu : Differentiable ℂ u)
    (j : Fin d) (x : Fin d → ℂ) :
    fderiv ℝ u x (Pi.single j Complex.I) = Complex.I * fderiv ℝ u x (Pi.single j (1 : ℂ)) := by
  have hd : DifferentiableAt ℂ u x := hu x
  rw [hd.fderiv_restrictScalars (𝕜 := ℝ), ContinuousLinearMap.coe_restrictScalars']
  rw [show (Pi.single j Complex.I : Fin d → ℂ) = Complex.I • (Pi.single j (1 : ℂ) : Fin d → ℂ) by
    ext i; simp [Pi.single_apply]]
  rw [map_smul]
  simp

/-- A complex-differentiable function of several variables is real `C¹`. -/
private theorem contDiff_one_of_differentiable_complex {d : ℕ} {u : (Fin d → ℂ) → ℂ}
    (hu : Differentiable ℂ u) : ContDiff ℝ 1 u := by
  have hana : AnalyticOnNhd ℂ u Set.univ := fun z _ =>
    Commons.Analysis.Complex.analyticAt_of_differentiableOn_closedBall (R := 1) one_pos
      hu.differentiableOn
  have h1 : ContDiff ℂ (1 : ℕ∞) u := hana.contDiff
  exact h1.restrict_scalars ℝ

/-- **Wirtinger integration by parts.** For a complex-differentiable `u` and a compactly supported
smooth test function `ξ`, the integral of `u` against the `∂̄`-derivative of `ξ` in the `j`-th
variable vanishes. -/
private theorem integral_mul_wirtinger_eq_zero {d : ℕ} {u : (Fin d → ℂ) → ℂ}
    (hu : Differentiable ℂ u) (j : Fin d) {ξ : (Fin d → ℂ) → ℂ}
    (hξC : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) ξ) (hξs : HasCompactSupport ξ) :
    ∫ x, u x * ((fderiv ℝ ξ x (Pi.single j (1 : ℂ))
        + Complex.I * fderiv ℝ ξ x (Pi.single j Complex.I)) / 2)
      ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) = 0 := by
  have huC : ContDiff ℝ 1 u := contDiff_one_of_differentiable_complex hu
  have hξC1 : ContDiff ℝ 1 ξ := hξC.of_le (by norm_num)
  have hcont_du : ∀ v : Fin d → ℂ, Continuous (fun x => fderiv ℝ u x v) := fun v =>
    (huC.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcont_dξ : ∀ v : Fin d → ℂ, Continuous (fun x => fderiv ℝ ξ x v) := fun v =>
    (hξC1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcs_dξ : ∀ v : Fin d → ℂ, HasCompactSupport (fun x => fderiv ℝ ξ x v) := fun v =>
    hξs.fderiv_apply ℝ v
  have hIBP : ∀ v : Fin d → ℂ,
      ∫ x, u x * fderiv ℝ ξ x v = - ∫ x, fderiv ℝ u x v * ξ x := by
    intro v
    refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) ?_ ?_ ?_ ?_ ?_
    · exact ((hcont_du v).mul hξC1.continuous).integrable_of_hasCompactSupport hξs.mul_left
    · exact (huC.continuous.mul (hcont_dξ v)).integrable_of_hasCompactSupport (hcs_dξ v).mul_left
    · exact (huC.continuous.mul hξC1.continuous).integrable_of_hasCompactSupport hξs.mul_left
    · intro x _
      exact (hu x).restrictScalars ℝ
    · intro x _
      exact hξC1.differentiable_one.differentiableAt
  have hIntA : Integrable (fun x => u x * fderiv ℝ ξ x (Pi.single j (1 : ℂ))) volume :=
    (huC.continuous.mul (hcont_dξ (Pi.single j (1 : ℂ)))).integrable_of_hasCompactSupport
      (hcs_dξ (Pi.single j (1 : ℂ))).mul_left
  have hIntB : Integrable (fun x => u x * fderiv ℝ ξ x (Pi.single j Complex.I)) volume :=
    (huC.continuous.mul (hcont_dξ (Pi.single j Complex.I))).integrable_of_hasCompactSupport
      (hcs_dξ (Pi.single j Complex.I)).mul_left
  have hIntIB : Integrable
      (fun x => Complex.I * (u x * fderiv ℝ ξ x (Pi.single j Complex.I))) volume :=
    hIntB.const_mul Complex.I
  have hIntuA : Integrable (fun x => fderiv ℝ u x (Pi.single j (1 : ℂ)) * ξ x) volume :=
    ((hcont_du (Pi.single j (1 : ℂ))).mul hξC1.continuous).integrable_of_hasCompactSupport
      hξs.mul_left
  have hIntuB : Integrable (fun x => fderiv ℝ u x (Pi.single j Complex.I) * ξ x) volume :=
    ((hcont_du (Pi.single j Complex.I)).mul hξC1.continuous).integrable_of_hasCompactSupport
      hξs.mul_left
  have hIntuIB : Integrable
      (fun x => Complex.I * (fderiv ℝ u x (Pi.single j Complex.I) * ξ x)) volume :=
    hIntuB.const_mul Complex.I
  have hzero : ∀ x, fderiv ℝ u x (Pi.single j (1 : ℂ))
      + Complex.I * fderiv ℝ u x (Pi.single j Complex.I) = 0 := by
    intro x
    rw [fderiv_apply_single_I hu j x, ← mul_assoc, Complex.I_mul_I]
    ring
  have key : ∫ x, u x * (fderiv ℝ ξ x (Pi.single j (1 : ℂ))
        + Complex.I * fderiv ℝ ξ x (Pi.single j Complex.I)) = 0 := by
    have hL : ∫ x, u x * (fderiv ℝ ξ x (Pi.single j (1 : ℂ))
          + Complex.I * fderiv ℝ ξ x (Pi.single j Complex.I))
        = (∫ x, u x * fderiv ℝ ξ x (Pi.single j (1 : ℂ)))
          + Complex.I * (∫ x, u x * fderiv ℝ ξ x (Pi.single j Complex.I)) := by
      rw [show (fun x => u x * (fderiv ℝ ξ x (Pi.single j (1 : ℂ))
              + Complex.I * fderiv ℝ ξ x (Pi.single j Complex.I)))
            = fun x => u x * fderiv ℝ ξ x (Pi.single j (1 : ℂ))
              + Complex.I * (u x * fderiv ℝ ξ x (Pi.single j Complex.I)) by
          funext x; ring]
      rw [integral_add hIntA hIntIB, integral_const_mul]
    have hR : (∫ x, fderiv ℝ u x (Pi.single j (1 : ℂ)) * ξ x)
        + Complex.I * (∫ x, fderiv ℝ u x (Pi.single j Complex.I) * ξ x) = 0 := by
      have h1 : ∫ x, Complex.I * (fderiv ℝ u x (Pi.single j Complex.I) * ξ x)
          = Complex.I * (∫ x, fderiv ℝ u x (Pi.single j Complex.I) * ξ x) :=
        integral_const_mul Complex.I _
      rw [← h1, ← integral_add hIntuA hIntuIB]
      rw [show (fun x => fderiv ℝ u x (Pi.single j (1 : ℂ)) * ξ x
              + Complex.I * (fderiv ℝ u x (Pi.single j Complex.I) * ξ x))
            = fun x => (fderiv ℝ u x (Pi.single j (1 : ℂ))
              + Complex.I * fderiv ℝ u x (Pi.single j Complex.I)) * ξ x by
          funext x; ring]
      rw [show (fun x => (fderiv ℝ u x (Pi.single j (1 : ℂ))
              + Complex.I * fderiv ℝ u x (Pi.single j Complex.I)) * ξ x)
            = fun _ => (0 : ℂ) by
          funext x; rw [hzero x, zero_mul]]
      simp
    rw [hL, hIBP (Pi.single j (1 : ℂ)), hIBP (Pi.single j Complex.I)]
    have : -(∫ x, fderiv ℝ u x (Pi.single j (1 : ℂ)) * ξ x)
        + Complex.I * (-(∫ x, fderiv ℝ u x (Pi.single j Complex.I) * ξ x))
        = -((∫ x, fderiv ℝ u x (Pi.single j (1 : ℂ)) * ξ x)
          + Complex.I * (∫ x, fderiv ℝ u x (Pi.single j Complex.I) * ξ x)) := by
      ring
    rw [this, hR, neg_zero]
  have hfin : (fun x => u x * ((fderiv ℝ ξ x (Pi.single j (1 : ℂ))
        + Complex.I * fderiv ℝ ξ x (Pi.single j Complex.I)) / 2))
      = fun x => (1 / 2 : ℂ) * (u x * (fderiv ℝ ξ x (Pi.single j (1 : ℂ))
        + Complex.I * fderiv ℝ ξ x (Pi.single j Complex.I))) := by
    funext x; ring
  rw [hfin, integral_const_mul, key]
  simp

/-- **Local uniform limits of holomorphic functions are holomorphic** (in several variables). -/
private theorem differentiable_of_tendstoLocallyUniformlyOn_aux {d : ℕ}
    {f : ℕ → (Fin d → ℂ) → ℂ} {g : (Fin d → ℂ) → ℂ}
    (hf : ∀ n, Differentiable ℂ (f n))
    (hconv : TendstoLocallyUniformlyOn f g Filter.atTop Set.univ) :
    Differentiable ℂ g := by
  classical
  have hgcont : Continuous g := continuousOn_univ.mp
    (hconv.continuousOn ((Eventually.of_forall fun n =>
      (hf n).continuous.continuousOn (s := Set.univ)).frequently))
  have hweak : ∀ (j : Fin d) (ξ : (Fin d → ℂ) → ℂ),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) ξ → HasCompactSupport ξ →
      ∫ x, g x * ((fderiv ℝ ξ x (Pi.single j (1 : ℂ))
        + Complex.I * fderiv ℝ ξ x (Pi.single j Complex.I)) / 2)
        ∂(volume : MeasureTheory.Measure (Fin d → ℂ)) = 0 := by
    intro j ξ hξC hξs
    set w : (Fin d → ℂ) → ℂ := fun x =>
      (fderiv ℝ ξ x (Pi.single j (1 : ℂ)) + Complex.I * fderiv ℝ ξ x (Pi.single j Complex.I)) / 2
      with hw
    have hξC1 : ContDiff ℝ 1 ξ := hξC.of_le (by norm_num)
    have hwcont : Continuous w := by
      rw [hw]; fun_prop
    have hwcs : HasCompactSupport w := by
      rw [hw]
      have heq : (fun x : Fin d → ℂ =>
            ((fderiv ℝ ξ x) (Pi.single j 1) + Complex.I * (fderiv ℝ ξ x) (Pi.single j Complex.I)) / 2)
          = (fun _ : Fin d → ℂ => (1 / 2 : ℂ)) *
            (fun x => (fderiv ℝ ξ x) (Pi.single j 1)
              + Complex.I * (fderiv ℝ ξ x) (Pi.single j Complex.I)) := by
        funext x; simp only [Pi.mul_apply]; ring
      rw [heq]
      exact (((hξs.fderiv_apply ℝ (Pi.single j (1 : ℂ))).add
        ((hξs.fderiv_apply ℝ (Pi.single j Complex.I)).mul_left))).mul_left
    have hzero : ∀ n, ∫ x, f n x * w x = 0 := fun n =>
      integral_mul_wirtinger_eq_zero (hf n) j hξC hξs
    have hlim : Tendsto (fun n => ∫ x, f n x * w x) Filter.atTop
        (𝓝 (∫ x, g x * w x)) := by
      refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (l := Filter.atTop)
        (F := fun n x => f n x * w x) (f := fun x => g x * w x)
        (bound := fun x => ‖w x‖ * (‖g x‖ + 1)) ?_ ?_ ?_ ?_
      · exact Eventually.of_forall fun n => ((hf n).continuous.mul hwcont).aestronglyMeasurable
      · have hunif : TendstoUniformlyOn f g Filter.atTop (tsupport w) :=
          (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hconv (tsupport w)
            (subset_univ _) hwcs.isCompact
        rw [Metric.tendstoUniformlyOn_iff] at hunif
        filter_upwards [hunif 1 zero_lt_one] with n hn
        refine Eventually.of_forall fun x => ?_
        calc ‖f n x * w x‖ = ‖f n x‖ * ‖w x‖ := norm_mul _ _
          _ ≤ (‖g x‖ + 1) * ‖w x‖ := by
              by_cases h : x ∈ tsupport w
              · have h1 : dist (g x) (f n x) < 1 := hn x h
                rw [dist_eq_norm, norm_sub_rev] at h1
                have h2 : ‖f n x‖ ≤ ‖g x‖ + 1 := by
                  calc ‖f n x‖ = ‖g x + (f n x - g x)‖ := by ring_nf
                    _ ≤ ‖g x‖ + ‖f n x - g x‖ := norm_add_le _ _
                    _ ≤ ‖g x‖ + 1 := by linarith
                exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
              · have h0 : w x = 0 := image_eq_zero_of_notMem_tsupport h
                simp [h0]
          _ = ‖w x‖ * (‖g x‖ + 1) := by ring
      · refine ((hwcont.norm).mul (hgcont.norm.add continuous_const)).integrable_of_hasCompactSupport ?_
        exact (hwcs.comp_left (g := fun z : ℂ => ‖z‖) (by simp)).mul_right
      · refine Eventually.of_forall fun x => ?_
        exact (hconv.tendsto_at (mem_univ x)).mul_const _
    have hzero_lim : Tendsto (fun n => ∫ x, f n x * w x) Filter.atTop (𝓝 0) := by
      have : (fun n => ∫ x, f n x * w x) = fun _ => (0 : ℂ) := funext hzero
      rw [this]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim hzero_lim
  obtain ⟨H, hH, hHeq⟩ := weyl_dbar (d := d) hgcont.locallyIntegrable
    ((hgcont.norm.pow 2).locallyIntegrable) hweak
  have hEq : g = H := MeasureTheory.Measure.eq_of_ae_eq hHeq hgcont hH.continuous
  rw [hEq]
  exact hH

/-- **Montel's theorem for locally `L²`-bounded sequences of entire functions of several complex
variables.** A sequence `f n` of entire functions on `Fin d → ℂ` whose squared moduli are locally
uniformly integrable admits a subsequence converging locally uniformly to a differentiable
function. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_locallyL2Bounded {d : ℕ}
    {f : ℕ → (Fin d → ℂ) → ℂ} (hf : ∀ n, Differentiable ℂ (f n))
    (hb : ∀ (z : Fin d → ℂ) (R : ℝ), ∃ M : ℝ, ∀ n : ℕ,
      ∫ w in Metric.closedBall z R, ‖f n w‖ ^ 2 ≤ M) :
    ∃ (φ : ℕ → ℕ) (g : (Fin d → ℂ) → ℂ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g Filter.atTop Set.univ ∧
      Differentiable ℂ g := by
  obtain ⟨φ, g, hφ, hconv⟩ := exists_subseq_tendstoLocallyUniformlyOn_of_bounded_lipschitz
    (fun n => (hf n).continuous)
    (closedBall_bound_of_integral_bound hf hb)
    (closedBall_lipschitz_bound_of_integral_bound hf hb)
  exact ⟨φ, g, hφ, hconv,
    differentiable_of_tendstoLocallyUniformlyOn_aux (fun n => hf (φ n)) hconv⟩

end Commons.Analysis.Complex.Montel
