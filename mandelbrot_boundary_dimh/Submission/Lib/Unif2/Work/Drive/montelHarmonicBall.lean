import Mathlib
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.harnack_inequality
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.circleAverage_tendsto_of_tendstoUniformlyOn
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.harmonic_of_circleAverage
import Submission.Lib.Unif2.Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic

noncomputable section
open Set Metric Filter Topology
open scoped Topology BoundedContinuousFunction

namespace Work.Drive

/-! ## Tools: Harnack oscillation bounds for harmonic functions -/

/-- Translation invariance of harmonicity: if `F` is harmonic in a neighbourhood of the closed
ball of centre `a` and radius `R`, then `ζ ↦ F (ζ + a)` is harmonic in a neighbourhood of the
closed ball of centre `0` and radius `R`. -/
theorem harmonicOnNhd_shift_closedBall {F : ℂ → ℝ} {a : ℂ} {R : ℝ}
    (hF : InnerProductSpace.HarmonicOnNhd F (Metric.closedBall a R)) :
    InnerProductSpace.HarmonicOnNhd (fun ζ : ℂ => F (ζ + a)) (Metric.closedBall (0 : ℂ) R) := by
  intro ζ hζ
  have hζ' : ζ + a ∈ Metric.closedBall a R := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hζ ⊢
    simpa using hζ
  exact Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic
    (f := fun z : ℂ => z + a) (x := ζ) (analyticAt_id.add analyticAt_const) (hF (ζ + a) hζ')

/-- **Harnack's inequality at an arbitrary centre.**  If `f ≥ 0` is harmonic on the closed disc
`closedBall c ρ` (`ρ > 0`), then for `x` strictly inside that disc,
`((ρ - ‖x - c‖)/(ρ + ‖x - c‖)) * f c ≤ f x ≤ ((ρ + ‖x - c‖)/(ρ - ‖x - c‖)) * f c`. -/
theorem harnack_inequality_center {f : ℂ → ℝ} {c : ℂ} {ρ : ℝ} (_hρ : 0 < ρ)
    (hf : InnerProductSpace.HarmonicOnNhd f (Metric.closedBall c ρ))
    (hpos : ∀ z ∈ Metric.closedBall c ρ, 0 ≤ f z) {x : ℂ} (hx : ‖x - c‖ < ρ) :
    ((ρ - ‖x - c‖) / (ρ + ‖x - c‖)) * f c ≤ f x ∧
      f x ≤ ((ρ + ‖x - c‖) / (ρ - ‖x - c‖)) * f c := by
  have hshift := harmonicOnNhd_shift_closedBall (a := c) (R := ρ) hf
  have hpos' : ∀ z : ℂ, ‖z‖ ≤ ρ → 0 ≤ (fun ζ : ℂ => f (ζ + c)) z := by
    intro z hz
    exact hpos (z + c) (by rw [Metric.mem_closedBall, dist_eq_norm]; simpa using hz)
  have h := Commons.Analysis.Complex.Harmonic.harnack_inequality hshift hpos' (w := x - c) hx
  simpa using h

/-- **Oscillation bound for harmonic functions.**  If `f` is harmonic on the closed disc
`closedBall p ρ` and `|f| ≤ M` there, then for `x` strictly inside,
`|f x - f p| ≤ (2 ‖x - p‖ / (ρ - ‖x - p‖)) * (2 M)`.
(Apply Harnack's inequality to the non-negative harmonic function `f + M`.) -/
theorem abs_sub_le_of_harmonic {f : ℂ → ℝ} {p : ℂ} {ρ M : ℝ} (hρ : 0 < ρ)
    (hharm : InnerProductSpace.HarmonicOnNhd f (Metric.closedBall p ρ))
    (hbd : ∀ z ∈ Metric.closedBall p ρ, |f z| ≤ M) {x : ℂ} (hx : ‖x - p‖ < ρ) :
    |f x - f p| ≤ (2 * ‖x - p‖ / (ρ - ‖x - p‖)) * (2 * M) := by
  have hp_mem : p ∈ Metric.closedBall p ρ := Metric.mem_closedBall_self hρ.le
  have hx_mem : x ∈ Metric.closedBall p ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hx.le
  have hpnn : 0 ≤ f p + M := by have h := hbd p hp_mem; rw [abs_le] at h; linarith [h.1]
  have hpM : f p + M ≤ 2 * M := by have h := hbd p hp_mem; rw [abs_le] at h; linarith [h.2]
  have hharm_u : InnerProductSpace.HarmonicOnNhd (f + fun _ : ℂ => M) (Metric.closedBall p ρ) :=
    fun z hz => (hharm z hz).add (InnerProductSpace.harmonicAt_const M)
  have hpos : ∀ z ∈ Metric.closedBall p ρ, 0 ≤ (f + fun _ : ℂ => M) z := by
    intro z hz
    have h := hbd z hz
    simp only [Pi.add_apply]
    rw [abs_le] at h
    linarith [h.1]
  obtain ⟨hlo, hhi⟩ := harnack_inequality_center hρ hharm_u hpos (x := x) hx
  simp only [Pi.add_apply] at hlo hhi
  have hden : 0 < ρ - ‖x - p‖ := by linarith
  have hratio_nn : 0 ≤ 2 * ‖x - p‖ / (ρ - ‖x - p‖) := by positivity
  have hA : f x + M - (f p + M) ≤ (2 * ‖x - p‖ / (ρ - ‖x - p‖)) * (2 * M) := by
    have h1 : ((ρ + ‖x - p‖) / (ρ - ‖x - p‖)) * (f p + M) - (f p + M)
        = (2 * ‖x - p‖ / (ρ - ‖x - p‖)) * (f p + M) := by
      field_simp
      ring
    calc f x + M - (f p + M)
        ≤ ((ρ + ‖x - p‖) / (ρ - ‖x - p‖)) * (f p + M) - (f p + M) := by linarith
      _ = (2 * ‖x - p‖ / (ρ - ‖x - p‖)) * (f p + M) := h1
      _ ≤ (2 * ‖x - p‖ / (ρ - ‖x - p‖)) * (2 * M) := mul_le_mul_of_nonneg_left hpM hratio_nn
  have hB : f p + M - (f x + M) ≤ (2 * ‖x - p‖ / (ρ - ‖x - p‖)) * (2 * M) := by
    have hsplit : 2 * ‖x - p‖ / (ρ + ‖x - p‖) ≤ 2 * ‖x - p‖ / (ρ - ‖x - p‖) :=
      div_le_div_of_nonneg_left (by positivity) hden (by nlinarith [norm_nonneg (x - p)])
    have h2 : (f p + M) - ((ρ - ‖x - p‖) / (ρ + ‖x - p‖)) * (f p + M)
        = (2 * ‖x - p‖ / (ρ + ‖x - p‖)) * (f p + M) := by
      field_simp
      ring
    have h3 : (f p + M) - (f x + M) ≤
        (f p + M) - ((ρ - ‖x - p‖) / (ρ + ‖x - p‖)) * (f p + M) := by
      linarith
    calc (f p + M) - (f x + M)
        ≤ (f p + M) - ((ρ - ‖x - p‖) / (ρ + ‖x - p‖)) * (f p + M) := h3
      _ = (2 * ‖x - p‖ / (ρ + ‖x - p‖)) * (f p + M) := h2
      _ ≤ (2 * ‖x - p‖ / (ρ - ‖x - p‖)) * (f p + M) := mul_le_mul_of_nonneg_right hsplit hpnn
      _ ≤ (2 * ‖x - p‖ / (ρ - ‖x - p‖)) * (2 * M) := mul_le_mul_of_nonneg_left hpM hratio_nn
  rw [abs_le]
  constructor <;> linarith

/-! ## Montel compactness on a disc centred at the origin -/

/-- **Montel compactness for real-valued harmonic functions on a disc** (the case of a disc
centred at `0`).  A sequence of functions harmonic on `ball 0 R`, uniformly bounded on every
strictly smaller concentric disc, has a subsequence converging locally uniformly on `ball 0 R`
to a function harmonic there.

The proof extracts, on each member `K k = closedBall 0 (r k)` of a compact exhaustion of the
disc (`r k = R - R/(k+2) ↑ R`), a uniformly convergent subsequence by Arzela–Ascoli: the family
is bounded on `K k` and equicontinuous there by the Harnack oscillation bound
`abs_sub_le_of_harmonic`; the subsequences are then diagonalised.  The diagonal limit satisfies
the circle mean value identity (circle averages pass to uniform limits on each circle, and each
`v n` has the mean value property), hence is harmonic by `harmonic_of_circleAverage`. -/
theorem montelHarmonicBall_zero {R : ℝ} (hR : 0 < R)
    {v : ℕ → ℂ → ℝ} (hv : ∀ n, InnerProductSpace.HarmonicOnNhd (v n) (Metric.ball (0 : ℂ) R))
    (hb : ∀ r : ℝ, r < R → ∃ M : ℝ, ∀ n : ℕ, ∀ z ∈ Metric.ball (0 : ℂ) r, |v n z| ≤ M) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℝ), StrictMono φ ∧
      InnerProductSpace.HarmonicOnNhd g (Metric.ball (0 : ℂ) R) ∧
      TendstoLocallyUniformlyOn (fun n => v (φ n)) g Filter.atTop (Metric.ball (0 : ℂ) R) := by
  classical
  -- ## Radii and the compact exhaustion of the disc
  let r : ℕ → ℝ := fun k => R - R / ((k : ℝ) + 2)
  have hr_lt : ∀ k, r k < R := by
    intro k
    have hpos : 0 < R / ((k : ℝ) + 2) := by positivity
    simp only [r]; linarith
  have hr_pos : ∀ k, 0 < r k := by
    intro k
    have h2 : (2 : ℝ) ≤ (k : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h : R / ((k : ℝ) + 2) ≤ R / 2 := div_le_div_of_nonneg_left hR.le (by norm_num) h2
    simp only [r]; linarith
  have hr_lt_succ : ∀ k, r k < r (k + 1) := by
    intro k
    have h : R / ((k : ℝ) + 3) < R / ((k : ℝ) + 2) :=
      div_lt_div_of_pos_left hR (by positivity) (by linarith)
    have h1 : ((k + 1 : ℕ) : ℝ) + 2 = (k : ℝ) + 3 := by push_cast; ring
    simp only [r]
    rw [h1]
    linarith
  have hr_tend : Tendsto r Filter.atTop (𝓝 R) := by
    have hk : Tendsto (fun k : ℕ => ((k : ℝ) + 2)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right Filter.atTop (f := fun k : ℕ => ((k : ℝ))) (2 : ℝ)
        tendsto_natCast_atTop_atTop
    have hlim : Tendsto (fun k : ℕ => (((k : ℝ) + 2))⁻¹) Filter.atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hk
    have hlim' : Tendsto (fun k : ℕ => R / ((k : ℝ) + 2)) Filter.atTop (𝓝 0) := by
      have hc : Tendsto (fun _ : ℕ => R) Filter.atTop (𝓝 R) := tendsto_const_nhds
      have h := hc.mul hlim
      simpa [div_eq_mul_inv] using h
    have hRc : Tendsto (fun _ : ℕ => R) Filter.atTop (𝓝 R) := tendsto_const_nhds
    have h2 := hRc.sub hlim'
    simpa [r] using h2
  let K : ℕ → Set ℂ := fun k => Metric.closedBall (0 : ℂ) (r k)
  have hK_compact : ∀ k, IsCompact (K k) := fun k => isCompact_closedBall 0 (r k)
  have hK_sub : ∀ k, K k ⊆ Metric.ball (0 : ℂ) R := fun k =>
    Metric.closedBall_subset_ball (hr_lt k)
  have hK_sub_next : ∀ k, K k ⊆ Metric.ball (0 : ℂ) (r (k+1)) := fun k =>
    Metric.closedBall_subset_ball (hr_lt_succ k)
  have hKcpt : ∀ k, CompactSpace (K k) := fun k => isCompact_iff_compactSpace.mp (hK_compact k)
  haveI := hKcpt
  -- ## A uniform bound on each member of the exhaustion
  have hbound : ∀ k, ∃ M : ℝ, 0 ≤ M ∧
      ∀ n : ℕ, ∀ z ∈ Metric.ball (0:ℂ) (r (k+1)), |v n z| ≤ M := by
    intro k
    obtain ⟨M, hM⟩ := hb (r (k+1)) (hr_lt (k+1))
    exact ⟨max M 0, le_max_right _ _, fun n z hz => le_trans (hM n z hz) (le_max_left _ _)⟩
  choose Mb hMb using hbound
  let ρ : ℕ → ℝ := fun k => (r (k+1) - r k) / 2
  let C : ℕ → ℝ := fun k => 8 * Mb k / ρ k
  have hρpos : ∀ k, 0 < ρ k := fun k => by
    have := hr_lt_succ k; simp only [ρ]; linarith
  -- ## Uniform Lipschitz bounds on every member of the exhaustion
  have hosc : ∀ k n, ∀ z w : ℂ, z ∈ K k → w ∈ K k → |v n z - v n w| ≤ C k * ‖z - w‖ := by
    intro k n z w hz hw
    have hMk : 0 ≤ Mb k := (hMb k).1
    have hbnd_z : |v n z| ≤ Mb k := (hMb k).2 n z (hK_sub_next k hz)
    have hbnd_w : |v n w| ≤ Mb k := (hMb k).2 n w (hK_sub_next k hw)
    have htriv : |v n z - v n w| ≤ 2 * Mb k := by
      have h1 := abs_le.mp hbnd_z
      have h2 := abs_le.mp hbnd_w
      rw [abs_le]
      constructor <;> linarith
    by_cases hsmall : ‖z - w‖ ≤ ρ k / 2
    · -- the Harnack regime: the two points are close together
      have hsub : Metric.closedBall z (ρ k) ⊆ Metric.ball (0:ℂ) (r (k+1)) := by
        intro y hy
        have hyz : ‖y - z‖ ≤ ρ k := by
          have := hy; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        have h1 : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
          calc ‖y‖ = ‖(y - z) + z‖ := by ring_nf
            _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
        have hzr : ‖z‖ ≤ r k := by
          have h := (Metric.mem_closedBall.mp hz); rwa [dist_eq_norm, sub_zero] at h
        have h2 : ρ k + r k < r (k+1) := by
          have h3 := hr_lt_succ k
          have h4 : (r (k+1) - r k) / 2 + r k = (r (k+1) + r k)/2 := by ring
          rw [h4]; linarith
        linarith
      have hharm : InnerProductSpace.HarmonicOnNhd (v n) (Metric.closedBall z (ρ k)) :=
        (hv n).mono (fun y hy => Metric.ball_subset_ball (le_of_lt (hr_lt (k+1))) (hsub hy))
      have hbd : ∀ y ∈ Metric.closedBall z (ρ k), |v n y| ≤ Mb k :=
        fun y hy => (hMb k).2 n y (hsub hy)
      have hxlt : ‖w - z‖ < ρ k :=
        lt_of_le_of_lt (by simpa [norm_sub_rev] using hsmall) (by linarith [hρpos k])
      have hH := abs_sub_le_of_harmonic (hρ := hρpos k) hharm hbd hxlt
      have hd_le : ‖w - z‖ ≤ ρ k / 2 := by simpa [norm_sub_rev] using hsmall
      have hden : 0 < ρ k - ‖w - z‖ := by linarith
      have hratio : 2 * ‖w - z‖ / (ρ k - ‖w - z‖) ≤ 4 * ‖w - z‖ / ρ k := by
        rw [div_le_div_iff₀ hden (hρpos k)]
        nlinarith [norm_nonneg (w - z), hd_le]
      have hstep : (2 * ‖w - z‖ / (ρ k - ‖w - z‖)) * (2 * Mb k) ≤
          (4 * ‖w - z‖ / ρ k) * (2 * Mb k) :=
        mul_le_mul_of_nonneg_right hratio (by linarith)
      have hfin : (4 * ‖w - z‖ / ρ k) * (2 * Mb k) = C k * ‖z - w‖ := by
        have hρne : ρ k ≠ 0 := ne_of_gt (hρpos k)
        simp only [C]
        rw [norm_sub_rev w z]
        field_simp
        ring
      calc |v n z - v n w| = |v n w - v n z| := abs_sub_comm _ _
        _ ≤ (2 * ‖w - z‖ / (ρ k - ‖w - z‖)) * (2 * Mb k) := hH
        _ ≤ (4 * ‖w - z‖ / ρ k) * (2 * Mb k) := hstep
        _ = C k * ‖z - w‖ := hfin
    · -- the two points are far apart: use the crude bound
      push Not at hsmall
      have h2 : 2 * Mb k ≤ C k * ‖z - w‖ := by
        have hC : C k * (ρ k / 2) = 4 * Mb k := by
          have hρne : ρ k ≠ 0 := ne_of_gt (hρpos k)
          simp only [C]
          field_simp
          ring
        have hCnn : 0 ≤ C k := by
          simp only [C]; exact div_nonneg (by linarith) (le_of_lt (hρpos k))
        have hle : C k * (ρ k / 2) ≤ C k * ‖z - w‖ :=
          mul_le_mul_of_nonneg_left (le_of_lt hsmall) hCnn
        linarith
      linarith
  -- ## The functions restricted to each member of the exhaustion
  let Fn : (k : ℕ) → ℕ → (K k →ᵇ ℝ) := fun k n =>
    BoundedContinuousFunction.mkOfCompact
      { toFun := fun x : K k => v n x
        continuous_toFun := ((hv n).continuousOn.mono (hK_sub k)).domRestrict }
  have hFn_apply : ∀ (k n : ℕ) (x : K k), Fn k n x = v n x := by
    intro k n x
    simp only [Fn, BoundedContinuousFunction.mkOfCompact_apply]
    rfl
  -- ## Equicontinuity of the family on each member of the exhaustion
  have heqcont : ∀ k, Equicontinuous ((↑) : Set.range (Fn k) → K k → ℝ) := by
    intro k
    refine Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => C k * t) ?_ _ ?_
    · have ht : Tendsto (fun t : ℝ => C k * t) (𝓝 0) (𝓝 (C k * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      simpa using ht
    · intro x y i
      obtain ⟨n, hn⟩ := i.2
      have hcoe : (i : K k → ℝ) = fun x : K k => v n x := by
        rw [← hn]
        funext x
        exact hFn_apply k n x
      rw [hcoe]
      have h := hosc k n (x : ℂ) (y : ℂ) x.2 y.2
      simpa [Subtype.dist_eq, Real.dist_eq, dist_eq_norm] using h
  -- ## Arzela–Ascoli: the closure of the family on each member is compact
  have hcompact : ∀ k, IsCompact (closure (Set.range (Fn k))) := by
    intro k
    refine BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℝ) (Mb k))
      (isCompact_closedBall 0 (Mb k)) (Set.range (Fn k)) ?_ (heqcont k)
    intro g x hg
    obtain ⟨n, hn⟩ := hg
    have hx : (x : ℂ) ∈ Metric.ball (0:ℂ) (r (k+1)) := hK_sub_next k x.2
    have h1 : |v n (x : ℂ)| ≤ Mb k := (hMb k).2 n (x : ℂ) hx
    rw [← hn, hFn_apply k n x]
    simpa [Metric.mem_closedBall, Real.dist_eq] using h1
  -- ## Sequential extraction of a convergent subsequence on each member
  have exists_good : ∀ (k : ℕ) (u : ℕ → ℕ), ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ a : K k →ᵇ ℝ, Tendsto (fun n => Fn k (u (ψ n))) Filter.atTop (𝓝 a) := by
    intro k u
    have hmem : ∀ n, Fn k (u n) ∈ closure (Set.range (Fn k)) :=
      fun n => subset_closure (Set.mem_range_self (u n))
    obtain ⟨a, _, ψ, hψ, hψlim⟩ := (hcompact k).tendsto_subseq hmem
    exact ⟨ψ, hψ, a, by simpa [Function.comp_def] using hψlim⟩
  let psi : ℕ → (ℕ → ℕ) → (ℕ → ℕ) := fun k u => Classical.choose (exists_good k u)
  have psi_strict : ∀ (k : ℕ) (u : ℕ → ℕ), StrictMono (psi k u) := by
    intro k u
    exact (Classical.choose_spec (exists_good k u)).1
  have psi_conv : ∀ (k : ℕ) (u : ℕ → ℕ), ∃ a : K k →ᵇ ℝ,
      Tendsto (fun n => Fn k (u (psi k u n))) Filter.atTop (𝓝 a) := by
    intro k u
    exact (Classical.choose_spec (exists_good k u)).2
  -- ## The nested subsequences and their diagonal
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
  -- ## The limit of the diagonal on each member of the exhaustion
  let Alim : (j : ℕ) → K (j + 1) →ᵇ ℝ := fun j => Classical.choose (psi_conv (j + 1) (phi j))
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
  -- ## Uniform convergence on each member of the exhaustion
  have hAunifsub : ∀ j, TendstoUniformly (fun n (x : K (j + 1)) => v (diag n) x)
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
    calc dist ((Alim j) x) (v (diag n) x)
        = dist ((Alim j) x) ((Fn (j + 1) (diag n)) x) := by rw [hFn_apply]
      _ ≤ dist (Alim j) (Fn (j + 1) (diag n)) := hdist
      _ = dist (Fn (j + 1) (diag n)) (Alim j) := dist_comm _ _
      _ < ε := hN n hn
  -- ## The limit function on the disc
  let g : ℂ → ℝ := fun z =>
    if z ∈ Metric.ball (0 : ℂ) R then Filter.limUnder Filter.atTop (fun n => v (diag n) z) else 0
  have hg_eq : ∀ (j : ℕ) (x : K (j + 1)), g x = (Alim j) x := by
    intro j x
    have hxball : (x : ℂ) ∈ Metric.ball (0 : ℂ) R := hK_sub (j + 1) x.2
    have hpt : Tendsto (fun n => v (diag n) (x : ℂ)) Filter.atTop (𝓝 ((Alim j) x)) :=
      (hAunifsub j).tendsto_at x
    show g (x : ℂ) = (Alim j) x
    simp only [g]
    rw [if_pos hxball]
    exact Filter.Tendsto.limUnder_eq hpt
  have hgunifsub : ∀ j, TendstoUniformly (fun n (x : K (j + 1)) => v (diag n) x)
      (fun x : K (j + 1) => g x) Filter.atTop := by
    intro j
    rw [← tendstoUniformlyOn_univ]
    refine (tendstoUniformlyOn_univ.mpr (hAunifsub j)).congr_right fun x _ => (hg_eq j x).symm
  have hgunif : ∀ j, TendstoUniformlyOn (fun n => v (diag n)) g Filter.atTop (K (j + 1)) := by
    intro j
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    simpa [Function.comp_def] using hgunifsub j
  -- ## Local uniformity on the disc
  have hconv : TendstoLocallyUniformlyOn (fun n => v (diag n)) g Filter.atTop
      (Metric.ball (0 : ℂ) R) := by
    refine tendstoLocallyUniformlyOn_of_forall_exists_nhds ?_
    intro x hx
    have hxnorm : ‖x‖ < R := by simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hx
    have hshift : Tendsto (fun j : ℕ => j + 1) Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      exact ⟨b, fun a ha => le_trans ha (Nat.le_succ a)⟩
    have hrt : Tendsto (fun j : ℕ => r (j + 1)) Filter.atTop (𝓝 R) := hr_tend.comp hshift
    have hev : ∀ᶠ j in Filter.atTop, ‖x‖ < r (j + 1) :=
      hrt.eventually (isOpen_Ioi.mem_nhds hxnorm)
    obtain ⟨j, hj⟩ := Filter.eventually_atTop.mp hev
    have hj' : ‖x‖ < r (j + 1) := hj j le_rfl
    refine ⟨K (j + 1), ?_, hgunif j⟩
    apply nhdsWithin_le_nhds
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x (sub_pos.mpr hj')) ?_
    intro y hy
    have hyx : ‖y - x‖ < r (j + 1) - ‖x‖ := by
      simpa [dist_eq_norm] using (Metric.mem_ball.mp hy)
    have hy' : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
      calc ‖y‖ = ‖x + (y - x)‖ := by ring_nf
        _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
    have : y ∈ Metric.closedBall (0 : ℂ) (r (j + 1)) := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      linarith
    exact this
  -- ## The limit is harmonic
  have hsphere_sub : ∀ p : ℂ, ∀ q : ℝ, ‖p‖ + q < R → Metric.sphere p q ⊆ Metric.ball (0:ℂ) R := by
    intro p q hpq x hx
    have hxp : ‖x - p‖ = q := by
      have := Metric.mem_sphere.mp hx
      simpa [dist_eq_norm] using this
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    calc ‖x‖ = ‖(x - p) + p‖ := by ring_nf
      _ ≤ ‖x - p‖ + ‖p‖ := norm_add_le _ _
      _ = q + ‖p‖ := by rw [hxp]
      _ < R := by linarith
  have hclosed_sub : ∀ p : ℂ, ∀ q : ℝ, ‖p‖ + q < R →
      Metric.closedBall p q ⊆ Metric.ball (0:ℂ) R := by
    intro p q hpq x hx
    have hxp : ‖x - p‖ ≤ q := by
      have := Metric.mem_closedBall.mp hx
      simpa [dist_eq_norm] using this
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    calc ‖x‖ = ‖(x - p) + p‖ := by ring_nf
      _ ≤ ‖x - p‖ + ‖p‖ := norm_add_le _ _
      _ ≤ q + ‖p‖ := by linarith
      _ < R := by linarith
  have hcont : ContinuousOn g (Metric.ball (0:ℂ) R) :=
    hconv.continuousOn
      ((Filter.Eventually.of_forall fun n => (hv (diag n)).continuousOn).frequently)
  have hMV : ∀ p : ℂ, ‖p‖ < R → ∀ q : ℝ, 0 < q → ‖p‖ + q < R →
      Real.circleAverage g p q = g p := by
    intro p hp q hq hpq
    have hsubsph := hsphere_sub p q hpq
    have hsubcl := hclosed_sub p q hpq
    -- uniformity of the convergence on the circle
    have hunif : TendstoUniformlyOn (fun n => v (diag n)) g Filter.atTop (Metric.sphere p q) :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere p q)).mp
        (hconv.mono hsubsph)
    -- circle averages of the members converge to the circle average of the limit
    have hca := Commons.Analysis.Complex.Harmonic.circleAverage_tendsto_of_tendstoUniformlyOn hq
      (fun n => ((hv (diag n)).continuousOn.mono hsubsph)) hunif
    -- the members have the mean value property
    have hconst : ∀ n, Real.circleAverage (v (diag n)) p q = v (diag n) p := by
      intro n
      have hnhd : InnerProductSpace.HarmonicOnNhd (v (diag n)) (Metric.closedBall p |q|) := by
        rw [abs_of_pos hq]
        exact (hv (diag n)).mono hsubcl
      exact InnerProductSpace.HarmonicOnNhd.circleAverage_eq hnhd
    have hp_ball : p ∈ Metric.ball (0 : ℂ) R := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hp
    have hpt : Tendsto (fun n => v (diag n) p) Filter.atTop (𝓝 (g p)) := hconv.tendsto_at hp_ball
    have h2 : Tendsto (fun n => Real.circleAverage (v (diag n)) p q) Filter.atTop (𝓝 (g p)) := by
      simpa only [hconst] using hpt
    exact tendsto_nhds_unique hca h2
  have hharm : InnerProductSpace.HarmonicOnNhd g (Metric.ball (0 : ℂ) R) :=
    Commons.Analysis.Complex.Harmonic.harmonic_of_circleAverage hcont hMV
  exact ⟨diag, g, diag_strict, hharm, hconv⟩

/-! ## Montel compactness on an arbitrary disc -/

/-- **Montel compactness for real-valued harmonic functions on a disc.**  A sequence of functions
harmonic on the disc `ball c R`, uniformly bounded on every strictly smaller concentric disc, has a
subsequence converging locally uniformly on `ball c R` to a function harmonic there. -/
theorem montelHarmonicBall {c : ℂ} {R : ℝ} (hR : 0 < R)
    {v : ℕ → ℂ → ℝ} (hv : ∀ n, InnerProductSpace.HarmonicOnNhd (v n) (Metric.ball c R))
    (hb : ∀ r : ℝ, r < R → ∃ M : ℝ, ∀ n : ℕ, ∀ z ∈ Metric.ball c r, |v n z| ≤ M) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℝ), StrictMono φ ∧
      InnerProductSpace.HarmonicOnNhd g (Metric.ball c R) ∧
      TendstoLocallyUniformlyOn (fun n => v (φ n)) g Filter.atTop (Metric.ball c R) := by
  -- shift the centre of the disc to the origin
  have hv' : ∀ n, InnerProductSpace.HarmonicOnNhd (fun z : ℂ => v n (z + c))
      (Metric.ball (0 : ℂ) R) := by
    intro n z hz
    have hzc : z + c ∈ Metric.ball c R := by
      rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
      simpa using hz
    exact Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic
      (f := fun w : ℂ => w + c) (x := z) (analyticAt_id.add analyticAt_const) (hv n (z + c) hzc)
  have hb' : ∀ r : ℝ, r < R → ∃ M : ℝ, ∀ n : ℕ, ∀ z ∈ Metric.ball (0:ℂ) r,
      |(fun z : ℂ => v n (z + c)) z| ≤ M := by
    intro r hr
    obtain ⟨M, hM⟩ := hb r hr
    exact ⟨M, fun n z hz => hM n (z + c) (by
      rw [Metric.mem_ball, dist_eq_norm] at hz ⊢; simpa using hz)⟩
  obtain ⟨φ, G, hφ, hG, hconv⟩ := montelHarmonicBall_zero hR hv' hb'
  refine ⟨φ, fun z => G (z - c), hφ, ?_, ?_⟩
  · -- harmonicity of the shifted-back limit
    intro z hz
    have hzc : z - c ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
      simpa using hz
    exact Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic
      (f := fun w : ℂ => w - c) (x := z) (analyticAt_id.sub analyticAt_const) (hG (z - c) hzc)
  · -- push the local uniform convergence back along `z ↦ z - c`
    have hmap : MapsTo (fun z : ℂ => z - c) (Metric.ball c R) (Metric.ball (0 : ℂ) R) := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
      simpa using hz
    have hcont : ContinuousOn (fun z : ℂ => z - c) (Metric.ball c R) := by fun_prop
    have hcomp := hconv.comp (fun z : ℂ => z - c) hmap hcont
    refine hcomp.congr (fun n z hz => ?_)
    simp only [Function.comp_apply]
    rw [sub_add_cancel]

end Work.Drive
