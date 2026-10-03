/-
# The Fatou coordinate in the lift (`Work.L62.lift_fatou`)

`H` is a holomorphic self-map of the half-plane `{y < im}` of the shape `H w = w + β + ρ w`, with
`ρ` holomorphic, `1`-periodic, bounded by `M`, tending to `c` at the upper end `+i∞`, and with a
uniform positive drift `κ ≤ Im (H w - w)`.  The map is asymptotically the translation
`w ↦ w + (β + c)`, and a Fatou coordinate is obtained from the absolutely convergent series

`L w = w + ∑' n, (ρ (H^n w) - c)`,

which satisfies `L (H w) = L w + (β + c)` by telescoping.  The series converges because `ρ - c`
decays exponentially at the upper end (`decay_deriv`), so its `n`-th term is bounded by
`C * exp (-2 * π * n * κ)` (`iterate_im`); Cauchy's estimate gives the same bound for the
derivatives, whence `‖L' - 1‖ ≤ 1/2` deep in the half-plane (`tsum_geom`).  Injectivity is then the
mean value inequality on the convex half-plane, and the derivative bound on `H` follows from the
same exponential decay.
-/
import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.end_fourier

namespace Work.L62

open Complex Filter Set Topology
open scoped Topology

noncomputable section

/-! ## Auxiliary analysis lemmas -/

/-- `M * Real.exp (-2 * π * (g z - a))` tends to `0` along any filter on which `g` tends to `+∞`. -/
lemma tendsto_const_mul_exp_neg {α : Type*} {l : Filter α} {g : α → ℝ} {M a : ℝ}
    (hg : Tendsto g l atTop) :
    Tendsto (fun z => M * Real.exp (-2 * Real.pi * (g z - a))) l (nhds 0) := by
  have h1 : Tendsto (fun z => -(2 * Real.pi * (g z - a))) l atBot := by
    rw [tendsto_neg_atBot_iff]
    exact (tendsto_atTop_add_const_right _ (-a) hg).const_mul_atTop (by positivity)
  have h2 : Tendsto (fun z => Real.exp (-(2 * Real.pi * (g z - a)))) l (nhds 0) :=
    Real.tendsto_exp_atBot.comp h1
  simpa only [neg_mul, mul_zero] using h2.const_mul M

/-- `Real.exp (-2 * π * t)` is antitone. -/
lemma exp_neg_two_pi_anti {a b : ℝ} (h : a ≤ b) :
    Real.exp (-2 * Real.pi * b) ≤ Real.exp (-2 * Real.pi * a) := by
  rw [Real.exp_le_exp]
  nlinarith [Real.pi_pos]

/-- A holomorphic `1`-periodic function on the half-plane `{Y < im}` which is bounded there and
tends to `0` at the upper end decays exponentially, together with its derivative. -/
lemma decay_deriv {ψ : ℂ → ℂ} {Y B : ℝ}
    (hper : ∀ w : ℂ, Y < w.im → ψ (w + 1) = ψ w)
    (hhol : DifferentiableOn ℂ ψ {w : ℂ | Y < w.im})
    (hbd : ∀ w : ℂ, Y < w.im → ‖ψ w‖ ≤ B)
    (hlim : Tendsto ψ (comap Complex.im atTop) (nhds 0)) :
    ∃ C T : ℝ, 0 ≤ C ∧ ∀ z : ℂ, T ≤ z.im →
      ‖ψ z‖ ≤ C * Real.exp (-2 * Real.pi * z.im) ∧
      ‖deriv ψ z‖ ≤ C * Real.exp (-2 * Real.pi * z.im) := by
  set φ : ℂ → ℂ := fun w => ψ (w + Complex.I) with hφdef
  have himI : ∀ w : ℂ, (w + Complex.I).im = w.im + 1 := fun w => by simp
  have hper' : ∀ w : ℂ, Y ≤ w.im → φ (w + 1) = φ w := by
    intro w hw
    simp only [hφdef]
    have h1 : (w + 1) + Complex.I = (w + Complex.I) + 1 := by ring
    rw [h1, hper (w + Complex.I) (by rw [himI]; linarith)]
  have hhol' : DifferentiableOn ℂ φ {w : ℂ | Y ≤ w.im} := by
    intro w hw
    have hw' : Y ≤ w.im := hw
    have hmem : {z : ℂ | Y < z.im} ∈ 𝓝 (w + Complex.I) :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds
        (show Y < (w + Complex.I).im from by rw [himI]; linarith)
    simp only [hφdef]
    have h := (hhol.differentiableAt hmem).comp w (differentiableAt_id.add_const Complex.I)
    simpa [Function.comp_def] using h.differentiableWithinAt
  have hbd' : ∀ w : ℂ, Y ≤ w.im → ‖φ w‖ ≤ B := by
    intro w hw
    rw [hφdef]
    exact hbd (w + Complex.I) (by rw [himI]; linarith)
  obtain ⟨c₀, M₀, hM₀⟩ := end_fourier hper' hhol' hbd'
  have hφlim : Tendsto φ (comap Complex.im atTop) (nhds 0) := by
    have hcomp : Tendsto (fun w : ℂ => w + Complex.I) (comap Complex.im atTop)
        (comap Complex.im atTop) := by
      rw [Filter.tendsto_comap_iff]
      have h1 : Tendsto (fun w : ℂ => w.im + 1) (comap Complex.im atTop) atTop :=
        tendsto_atTop_add_const_right _ 1 (Filter.tendsto_comap (f := Complex.im) (x := atTop))
      simpa [himI, Function.comp_def] using h1
    have h := hlim.comp hcomp
    simpa [hφdef, Function.comp_def] using h
  have hc₀ : c₀ = 0 := by
    have hcomap : (comap Complex.im atTop).NeBot :=
      Filter.comap_neBot fun t ht => by
        obtain ⟨a, ha⟩ := Filter.mem_atTop_sets.mp ht
        exact ⟨(a : ℂ) * Complex.I, ha _ (by simp [Complex.mul_im])⟩
    have hsubst : ∀ w : ℂ, w.im - (Y + 1) = w.im - Y - 1 := fun w => by ring
    have hbnd : ∀ᶠ w : ℂ in comap Complex.im atTop,
        ‖φ w - c₀‖ ≤ M₀ * Real.exp (-2 * Real.pi * (w.im - (Y + 1))) := by
      refine Filter.eventually_iff_exists_mem.mpr ⟨{w : ℂ | Y + 1 ≤ w.im}, ?_, ?_⟩
      · rw [Filter.mem_comap]
        exact ⟨Set.Ici (Y + 1), Ici_mem_atTop (Y + 1), fun x hx => hx⟩
      · intro w hw
        rw [hsubst]
        exact hM₀ w hw
    have hupper : Tendsto (fun w : ℂ => M₀ * Real.exp (-2 * Real.pi * (w.im - (Y + 1))))
        (comap Complex.im atTop) (nhds 0) :=
      tendsto_const_mul_exp_neg (M := M₀) (a := Y + 1)
        (Filter.tendsto_comap (f := Complex.im) (x := atTop))
    have hsub : Tendsto (fun w : ℂ => φ w - c₀) (comap Complex.im atTop) (nhds 0) :=
      squeeze_zero_norm' hbnd hupper
    have htend : Tendsto φ (comap Complex.im atTop) (nhds c₀) := by
      simpa only [sub_add_cancel, zero_add] using hsub.add_const c₀
    exact tendsto_nhds_unique htend hφlim
  have hM₀nn : 0 ≤ M₀ := by
    have hz₀ : (((Y + 2 : ℝ) : ℂ) * Complex.I).im = Y + 2 := by simp [Complex.mul_im]
    have h1 : ‖φ (((Y + 2 : ℝ) : ℂ) * Complex.I)‖ ≤ M₀ * Real.exp (-2 * Real.pi) := by
      have h := hM₀ (((Y + 2 : ℝ) : ℂ) * Complex.I) (by rw [hz₀]; linarith)
      rw [hc₀, sub_zero] at h
      have h2 : (((Y + 2 : ℝ) : ℂ) * Complex.I).im - Y - 1 = 1 := by rw [hz₀]; ring
      rw [h2, mul_one] at h
      exact h
    have h3 : 0 ≤ M₀ * Real.exp (-2 * Real.pi) := le_trans (norm_nonneg _) h1
    exact nonneg_of_mul_nonneg_right (by rw [mul_comm] at h3; exact h3) (Real.exp_pos _)
  set C₁ : ℝ := M₀ * Real.exp (2 * Real.pi * (Y + 2)) with hC₁def
  have hC₁nn : 0 ≤ C₁ := mul_nonneg hM₀nn (Real.exp_pos _).le
  set C₂ : ℝ := 2 * C₁ * Real.exp Real.pi with hC₂def
  have hval : ∀ z : ℂ, Y + 2 ≤ z.im → ‖ψ z‖ ≤ C₁ * Real.exp (-2 * Real.pi * z.im) := by
    intro z hz
    have h := hM₀ (z - Complex.I) (by rw [Complex.sub_im, Complex.I_im]; linarith)
    have hφz : φ (z - Complex.I) = ψ z := by rw [hφdef]; simp
    rw [hφz, hc₀, sub_zero] at h
    have him : (z - Complex.I).im = z.im - 1 := by rw [Complex.sub_im, Complex.I_im]
    rw [him] at h
    calc ‖ψ z‖ ≤ M₀ * Real.exp (-2 * Real.pi * (z.im - 1 - Y - 1)) := h
      _ = C₁ * Real.exp (-2 * Real.pi * z.im) := by
          rw [hC₁def]
          have hexp : -2 * Real.pi * (z.im - 1 - Y - 1)
              = 2 * Real.pi * (Y + 2) + (-2 * Real.pi * z.im) := by ring
          rw [hexp, Real.exp_add]
          ring
  have hder : ∀ z : ℂ, Y + 3 ≤ z.im → ‖deriv ψ z‖ ≤ C₂ * Real.exp (-2 * Real.pi * z.im) := by
    intro z hz
    have hR : (0 : ℝ) < 1 / 2 := by norm_num
    have hcl : closure (Metric.ball z (1 / 2)) ⊆ {w : ℂ | Y < w.im} := by
      intro w hw
      have hd : dist w z ≤ 1 / 2 :=
        Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hw)
      have hle : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
      have h4 : (w - z).im = w.im - z.im := Complex.sub_im w z
      have h5 : ‖w - z‖ ≤ 1 / 2 := by rw [dist_eq_norm] at hd; exact hd
      have h6 : -(‖w - z‖) ≤ (w - z).im := (abs_le.mp hle).1
      simp only [Set.mem_ofPred_eq]
      linarith
    have hdC : DiffContOnCl ℂ ψ (Metric.ball z (1 / 2)) :=
      DifferentiableOn.diffContOnCl (hhol.mono hcl)
    have hCsphere : ∀ w ∈ Metric.sphere z (1 / 2),
        ‖ψ w‖ ≤ C₁ * Real.exp (-2 * Real.pi * (z.im - 1 / 2)) := by
      intro w hw
      have hd : dist w z = 1 / 2 := Metric.mem_sphere.mp hw
      have hle : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
      have h5 : ‖w - z‖ = 1 / 2 := by rw [dist_eq_norm] at hd; exact hd
      have h6 : -(‖w - z‖) ≤ (w - z).im := (abs_le.mp hle).1
      have h4 : (w - z).im = w.im - z.im := Complex.sub_im w z
      have hwim : z.im - 1 / 2 ≤ w.im := by linarith
      calc ‖ψ w‖ ≤ C₁ * Real.exp (-2 * Real.pi * w.im) := hval w (by linarith)
        _ ≤ C₁ * Real.exp (-2 * Real.pi * (z.im - 1 / 2)) :=
            mul_le_mul_of_nonneg_left (exp_neg_two_pi_anti hwim) hC₁nn
    have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := ψ) hR hdC hCsphere
    have haux : (C₁ * Real.exp (-2 * Real.pi * (z.im - 1 / 2))) / (1 / 2)
        = C₂ * Real.exp (-2 * Real.pi * z.im) := by
      rw [hC₂def]
      have hexp : -2 * Real.pi * (z.im - 1 / 2) = Real.pi + (-2 * Real.pi * z.im) := by ring
      rw [hexp, Real.exp_add]
      ring
    rw [haux] at hcauchy
    exact hcauchy
  refine ⟨max C₁ C₂, Y + 3, le_max_of_le_left hC₁nn, ?_⟩
  intro z hz
  exact ⟨(hval z (by linarith)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le),
    (hder z hz).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)⟩

/-- A series of holomorphic functions on the half-plane `{Y - 1 < im}` dominated there by the
geometric progression `n ↦ A * r ^ n` (`0 ≤ r < 1`, `0 ≤ A`) converges on the deeper half-plane
`{Y < im}`; its sum is holomorphic there and its derivative is bounded by `2 * A / (1 - r)`
(Cauchy's estimate on the disc of radius `1 / 2`). -/
lemma tsum_geom {g : ℕ → ℂ → ℂ} {Y A r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hA : 0 ≤ A)
    (hdiff : ∀ n : ℕ, DifferentiableOn ℂ (g n) {z : ℂ | Y - 1 < z.im})
    (hbd : ∀ (n : ℕ) (z : ℂ), Y - 1 < z.im → ‖g n z‖ ≤ A * r ^ n) :
    (∀ z : ℂ, Y < z.im → Summable fun n => g n z) ∧
    DifferentiableOn ℂ (fun z => ∑' n, g n z) {z : ℂ | Y < z.im} ∧
    (∀ z : ℂ, Y < z.im → ‖deriv (fun z => ∑' n, g n z) z‖ ≤ 2 * A / (1 - r)) := by
  have h1r : 0 < 1 - r := by linarith
  have htopen : IsOpen {z : ℂ | Y < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have htopen' : IsOpen {z : ℂ | Y - 1 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have htconv : Convex ℝ {z : ℂ | Y < z.im} := convex_halfSpace_im_gt Y
  have hbd' : ∀ (n : ℕ) (z : ℂ), Y < z.im → ‖deriv (g n) z‖ ≤ 2 * A * r ^ n := by
    intro n z hz
    have hR : (0 : ℝ) < 1 / 2 := by norm_num
    have hcl : closure (Metric.ball z (1 / 2)) ⊆ {w : ℂ | Y - 1 < w.im} := by
      intro w hw
      have hd : dist w z ≤ 1 / 2 :=
        Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hw)
      have hle : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
      have h4 : (w - z).im = w.im - z.im := Complex.sub_im w z
      have h5 : ‖w - z‖ ≤ 1 / 2 := by rw [dist_eq_norm] at hd; exact hd
      have h6 : -(‖w - z‖) ≤ (w - z).im := (abs_le.mp hle).1
      simp only [Set.mem_ofPred_eq]
      linarith
    have hdC : DiffContOnCl ℂ (g n) (Metric.ball z (1 / 2)) :=
      DifferentiableOn.diffContOnCl ((hdiff n).mono hcl)
    have hsphere : ∀ w ∈ Metric.sphere z (1 / 2), ‖g n w‖ ≤ A * r ^ n := by
      intro w hw
      apply hbd n w
      have hd : dist w z = 1 / 2 := Metric.mem_sphere.mp hw
      have hle : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
      have h5 : ‖w - z‖ = 1 / 2 := by rw [dist_eq_norm] at hd; exact hd
      have h6 : -(‖w - z‖) ≤ (w - z).im := (abs_le.mp hle).1
      have h4 : (w - z).im = w.im - z.im := Complex.sub_im w z
      linarith
    have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := g n) hR hdC hsphere
    have haux : (A * r ^ n) / (1 / 2) = 2 * A * r ^ n := by ring
    rw [haux] at hcauchy
    exact hcauchy
  have hAgeo : Summable (fun n : ℕ => A * r ^ n) := by
    simpa using (summable_geometric_of_lt_one hr0 hr1).mul_left A
  have hmaj : Summable (fun n : ℕ => 2 * A * r ^ n) := by
    simpa using (summable_geometric_of_lt_one hr0 hr1).mul_left (2 * A)
  have hz₀ : (((Y + 1 : ℝ) : ℂ) * Complex.I).im = Y + 1 := by simp [Complex.mul_im]
  have hz₀mem : Y < (((Y + 1 : ℝ) : ℂ) * Complex.I).im := by rw [hz₀]; linarith
  have hbase : Summable (fun n : ℕ => g n (((Y + 1 : ℝ) : ℂ) * Complex.I)) :=
    Summable.of_norm_bounded hAgeo (fun n => hbd n _ (by rw [hz₀]; linarith))
  have hmain : ∀ z : ℂ, Y < z.im →
      HasDerivAt (fun z => ∑' n, g n z) (∑' n, deriv (g n) z) z := by
    intro z hz
    refine hasDerivAt_tsum_of_isPreconnected hmaj htopen htconv.isPreconnected
      (fun n u hu => ((hdiff n).differentiableAt (htopen'.mem_nhds (by
        rw [Set.mem_ofPred_eq] at hu ⊢; linarith))).hasDerivAt)
      (fun n u hu => hbd' n u hu) hz₀mem hbase hz
  refine ⟨fun z hz => Summable.of_norm_bounded hAgeo (fun n => hbd n z (by linarith)),
    fun z hz => ((hmain z hz).differentiableAt).differentiableWithinAt, fun z hz => ?_⟩
  rw [(hmain z hz).deriv]
  have hsumm : Summable (fun n : ℕ => deriv (g n) z) :=
    Summable.of_norm_bounded hmaj (fun n => hbd' n z hz)
  calc ‖∑' n, deriv (g n) z‖ ≤ ∑' n, ‖deriv (g n) z‖ := norm_tsum_le_tsum_norm hsumm.norm
    _ ≤ ∑' n, 2 * A * r ^ n := Summable.tsum_le_tsum (fun n => hbd' n z hz) hsumm.norm hmaj
    _ = 2 * A / (1 - r) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

/-! ## Growth of the iterates -/

/-- Iterates of a self-map of the half-plane `{y < im}` with uniform positive drift `κ` stay in the
half-plane, and their heights grow at least linearly. -/
lemma iterate_im {H : ℂ → ℂ} {y κ : ℝ} {w : ℂ}
    (hmap : ∀ z : ℂ, y < z.im → y < (H z).im)
    (hdrift : ∀ z : ℂ, y < z.im → κ ≤ (H z - z).im) (hw : y < w.im) (n : ℕ) :
    y < ((H^[n]) w).im ∧ w.im + n * κ ≤ ((H^[n]) w).im := by
  induction n with
  | zero => exact ⟨by simpa using hw, by simp⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have h3 : y < (H ((H^[n]) w)).im := hmap _ h1
    have h4 : κ ≤ (H ((H^[n]) w) - (H^[n]) w).im := hdrift _ h1
    have h5 : (H ((H^[n]) w) - (H^[n]) w).im
        = (H ((H^[n]) w)).im - ((H^[n]) w).im := Complex.sub_im _ _
    rw [Function.iterate_succ_apply']
    exact ⟨h3, by push_cast; linarith⟩

/-- A map carrying a set into itself has all its iterates carrying the set into itself. -/
lemma iterate_mapsTo {H : ℂ → ℂ} {s : Set ℂ} (h : Set.MapsTo H s s) (n : ℕ) :
    Set.MapsTo (H^[n]) s s := by
  induction n with
  | zero => intro x hx; exact hx
  | succ n ih => intro x hx; rw [Function.iterate_succ_apply']; exact h (ih hx)

/-- Iterates of a function holomorphic on the half-plane `{y < im}` which maps it into itself are
holomorphic there. -/
lemma iterate_diff {H : ℂ → ℂ} {y : ℝ}
    (hH : DifferentiableOn ℂ H {z : ℂ | y < z.im})
    (hmap : ∀ z : ℂ, y < z.im → y < (H z).im) (n : ℕ) :
    DifferentiableOn ℂ (H^[n]) {z : ℂ | y < z.im} := by
  induction n with
  | zero => simpa using differentiableOn_id
  | succ n ih =>
    have hmt : Set.MapsTo (H^[n]) {z : ℂ | y < z.im} {z : ℂ | y < z.im} :=
      iterate_mapsTo (fun z hz => hmap z hz) n
    have h := hH.comp ih hmt
    rwa [Function.iterate_succ']

/-! ## The Fatou coordinate -/

/-- **Fatou coordinate in the lift.**  `H` is a holomorphic self-map of the half-plane
`Y = {y < im}` with increment `H w = w + β + ρ w` (`ρ` holomorphic, `1`-periodic on `Y`,
bounded by `M`, with limit `c` at the upper end `upperEnd = comap im atTop`) and uniform positive
drift `κ ≤ Im (H w - w)` on `Y`.  Then there are a deeper half-plane `{y' < im}` and a "Fatou
coordinate" `L` there with `L (H w) = L w + (β + c)`, `‖L' - 1‖ ≤ 1/2`, `‖H'‖ ≤ 3/2`, and `L`
injective there. -/
theorem lift_fatou {y κ M : ℝ} {β c : ℂ} {H ρ : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H {w : ℂ | y < Complex.im w})
    (hmap : ∀ w : ℂ, y < Complex.im w → y < Complex.im (H w))
    (hinc : ∀ w : ℂ, y < Complex.im w → H w = w + β + ρ w)
    (hρd : DifferentiableOn ℂ ρ {w : ℂ | y < Complex.im w})
    (hρper : ∀ w : ℂ, y < Complex.im w → ρ (w + 1) = ρ w)
    (hρbd : ∀ w : ℂ, y < Complex.im w → ‖ρ w‖ ≤ M)
    (hρlim : Filter.Tendsto ρ (Filter.comap Complex.im Filter.atTop) (nhds c))
    (hκ : 0 < κ) (hdrift : ∀ w : ℂ, y < Complex.im w → κ ≤ Complex.im (H w - w)) :
    ∃ (L : ℂ → ℂ) (y' : ℝ), y ≤ y' ∧
      (∀ w : ℂ, y' < Complex.im w → DifferentiableAt ℂ L w ∧ L (H w) = L w + (β + c) ∧
        y' < Complex.im (H w) ∧ ‖deriv L w - 1‖ ≤ 1 / 2) ∧
      (∀ w : ℂ, y' < Complex.im w → ‖deriv (fun u => H u) w‖ ≤ 3 / 2) ∧
      Set.InjOn L {w : ℂ | y' < Complex.im w} := by
  set ψ : ℂ → ℂ := fun w => ρ w - c with hψdef
  have hψper : ∀ w : ℂ, y < w.im → ψ (w + 1) = ψ w := by
    intro w hw
    simp only [hψdef]
    rw [hρper w hw]
  have hψhol : DifferentiableOn ℂ ψ {w : ℂ | y < w.im} := by
    have h := hρd.sub_const c
    simpa [hψdef] using h
  have hψbd : ∀ w : ℂ, y < w.im → ‖ψ w‖ ≤ M + ‖c‖ := by
    intro w hw
    rw [hψdef]
    exact (norm_sub_le (ρ w) c).trans (by linarith [hρbd w hw])
  have hψlim : Tendsto ψ (comap Complex.im atTop) (nhds 0) := by
    have h := hρlim.sub_const c
    simpa [hψdef, sub_self] using h
  obtain ⟨C, T, hCnn, hdec⟩ := decay_deriv hψper hψhol hψbd hψlim
  -- the geometric rate at which the orbit escapes
  set r : ℝ := Real.exp (-2 * Real.pi * κ) with hrdef
  have hr0 : 0 ≤ r := Real.exp_nonneg _
  have hr1 : r < 1 := by
    rw [hrdef, Real.exp_lt_one_iff]
    have : (0 : ℝ) < 2 * Real.pi * κ := by positivity
    linarith
  have h1r : 0 < 1 - r := by linarith
  -- the depth of the half-plane
  have hev1 : ∀ᶠ Y : ℝ in atTop, C * Real.exp (-2 * Real.pi * (Y - 1)) < (1 - r) / 4 :=
    (tendsto_const_mul_exp_neg (g := fun Y : ℝ => Y) (M := C) (a := 1)
      tendsto_id).eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < (1 - r) / 4))
  have hev2' : ∀ᶠ Y : ℝ in atTop, C * Real.exp (-2 * Real.pi * (Y - 0)) < 1 / 2 :=
    (tendsto_const_mul_exp_neg (g := fun Y : ℝ => Y) (M := C) (a := 0)
      tendsto_id).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hev2 : ∀ᶠ Y : ℝ in atTop, C * Real.exp (-2 * Real.pi * Y) < 1 / 2 := by
    simpa using hev2'
  have hev : ∀ᶠ Y : ℝ in atTop, y ≤ Y ∧ y + 1 ≤ Y ∧ T + 1 ≤ Y ∧
      C * Real.exp (-2 * Real.pi * (Y - 1)) < (1 - r) / 4 ∧
      C * Real.exp (-2 * Real.pi * Y) < 1 / 2 :=
    (eventually_ge_atTop y).and ((eventually_ge_atTop (y + 1)).and
      ((eventually_ge_atTop (T + 1)).and (hev1.and hev2)))
  obtain ⟨Y, hY1, hY2, hY3, hY4, hY5⟩ := hev.exists
  have hA : 0 ≤ C * Real.exp (-2 * Real.pi * (Y - 1)) := mul_nonneg hCnn (Real.exp_pos _).le
  have hAle : C * Real.exp (-2 * Real.pi * (Y - 1)) ≤ (1 - r) / 4 := le_of_lt hY4
  set g : ℕ → ℂ → ℂ := fun n z => ψ ((H^[n]) z) with hgdef
  have hgdiff : ∀ n : ℕ, DifferentiableOn ℂ (g n) {z : ℂ | Y - 1 < z.im} := by
    intro n
    have hsub : {z : ℂ | Y - 1 < z.im} ⊆ {z : ℂ | y < z.im} := by
      intro z hz; rw [Set.mem_ofPred_eq] at hz ⊢; linarith
    have hmt : Set.MapsTo (H^[n]) {z : ℂ | Y - 1 < z.im} {z : ℂ | y < z.im} :=
      fun z hz => iterate_mapsTo (fun u hu => hmap u hu) n (hsub hz)
    have h := hψhol.comp ((iterate_diff hH hmap n).mono hsub) hmt
    simpa [hgdef, Function.comp_def] using h
  have hgbd : ∀ (n : ℕ) (z : ℂ), Y - 1 < z.im →
      ‖g n z‖ ≤ (C * Real.exp (-2 * Real.pi * (Y - 1))) * r ^ n := by
    intro n z hz
    have hzy : y < z.im := by linarith
    obtain ⟨-, h2⟩ := iterate_im hmap hdrift hzy n
    have hnk : 0 ≤ (n : ℝ) * κ := mul_nonneg (Nat.cast_nonneg n) hκ.le
    have hT' : T ≤ ((H^[n]) z).im := by linarith
    have hd1 := (hdec ((H^[n]) z) hT').1
    rw [hgdef]
    calc ‖ψ ((H^[n]) z)‖ ≤ C * Real.exp (-2 * Real.pi * ((H^[n]) z).im) := hd1
      _ ≤ C * Real.exp (-2 * Real.pi * (z.im + n * κ)) :=
          mul_le_mul_of_nonneg_left (exp_neg_two_pi_anti (by linarith)) hCnn
      _ = C * (Real.exp (-2 * Real.pi * z.im) * r ^ n) := by
          rw [hrdef]
          have hexp : Real.exp (-2 * Real.pi * (z.im + n * κ))
              = Real.exp (-2 * Real.pi * z.im) * Real.exp (-2 * Real.pi * κ) ^ n := by
            rw [← Real.exp_nat_mul, ← Real.exp_add]
            congr 1
            ring
          rw [hexp]
      _ = (C * Real.exp (-2 * Real.pi * z.im)) * r ^ n := by ring
      _ ≤ (C * Real.exp (-2 * Real.pi * (Y - 1))) * r ^ n :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (exp_neg_two_pi_anti (by linarith)) hCnn)
            (pow_nonneg hr0 n)
  obtain ⟨hsumm, hSdiff, hSderiv⟩ := tsum_geom hr0 hr1 hA hgdiff hgbd
  set S : ℂ → ℂ := fun z => ∑' n, g n z with hSdef
  have hSdiff' : DifferentiableOn ℂ S {z : ℂ | Y < z.im} := by rwa [hSdef]
  have hS_at : ∀ z : ℂ, Y < z.im → DifferentiableAt ℂ S z := by
    intro z hz
    exact hSdiff'.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)
  have hSderiv' : ∀ z : ℂ, Y < z.im →
      ‖deriv S z‖ ≤ 2 * (C * Real.exp (-2 * Real.pi * (Y - 1))) / (1 - r) := by
    intro z hz
    rw [hSdef]
    exact hSderiv z hz
  have hSsumm : ∀ z : ℂ, Y < z.im → Summable fun n => ψ ((H^[n]) z) := by
    intro z hz
    have h := hsumm z hz
    simpa [hgdef] using h
  have hSbound : 2 * (C * Real.exp (-2 * Real.pi * (Y - 1))) / (1 - r) ≤ 1 / 2 := by
    rw [div_le_iff₀ h1r]
    linarith
  set L : ℂ → ℂ := fun z => z + S z with hLdef
  have hLdiff : ∀ z : ℂ, Y < z.im → DifferentiableAt ℂ L z := by
    intro z hz
    have h := differentiableAt_id.add (hS_at z hz)
    rwa [hLdef]
  have hLderiv : ∀ z : ℂ, Y < z.im → deriv L z = 1 + deriv S z := by
    intro z hz
    have h1 : HasDerivAt (fun z : ℂ => z + S z) (1 + deriv S z) z :=
      (hasDerivAt_id z).add (hS_at z hz).hasDerivAt
    rw [hLdef]
    exact h1.deriv
  have hLderiv1 : ∀ w : ℂ, Y < w.im → ‖deriv L w - 1‖ ≤ 1 / 2 := by
    intro w hw
    rw [hLderiv w hw]
    have h : (1 + deriv S w) - 1 = deriv S w := by ring
    rw [h]
    exact le_trans (hSderiv' w hw) hSbound
  have hfun : ∀ w : ℂ, Y < w.im → L (H w) = L w + (β + c) := by
    intro w hw
    have hyw : y < w.im := by linarith
    have hsm : Summable (fun n : ℕ => ψ ((H^[n]) w)) := hSsumm w hw
    have hshift : (∑' n : ℕ, ψ ((H^[n]) (H w))) = (∑' n : ℕ, ψ ((H^[n]) w)) - ψ w := by
      have h1 : ∀ n : ℕ, ψ ((H^[n]) (H w)) = ψ ((H^[n + 1]) w) := by
        intro n
        have h2 : (H^[n]) (H w) = (H^[n + 1]) w := by
          simpa [Nat.succ_eq_add_one] using (Function.iterate_succ_apply H n w).symm
        rw [h2]
      calc (∑' n : ℕ, ψ ((H^[n]) (H w))) = ∑' n : ℕ, ψ ((H^[n + 1]) w) := tsum_congr h1
        _ = (∑' n : ℕ, ψ ((H^[n]) w)) - ψ w := by
            have h3 : (∑' b : ℕ, ψ ((H^[b + 1]) w)) + ψ w
                = ∑' b : ℕ, ψ ((H^[b]) w) := by
              have h4 := (Summable.tsum_eq_zero_add hsm).symm
              simpa [add_comm] using h4
            exact eq_sub_of_add_eq h3
    have hSeq : S (H w) = S w - ψ w := by
      simp only [hSdef, hgdef]
      exact hshift
    have hincw : H w = w + β + ρ w := hinc w hyw
    simp only [hLdef]
    rw [hSeq, hincw]
    simp only [hψdef]
    ring
  have hHderiv : ∀ w : ℂ, Y < w.im → ‖deriv (fun u => H u) w‖ ≤ 3 / 2 := by
    intro w hw
    have hyw : y < w.im := by linarith
    have hmem : {u : ℂ | y < u.im} ∈ 𝓝 w :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hyw
    have heq : (fun u : ℂ => H u) =ᶠ[𝓝 w] fun u : ℂ => u + β + ρ u := by
      filter_upwards [hmem] with u hu
      exact hinc u hu
    have hρ_at : DifferentiableAt ℂ ρ w := hρd.differentiableAt hmem
    have hderiv_eq : deriv (fun u : ℂ => u + β + ρ u) w = 1 + deriv ρ w := by
      have h2 : HasDerivAt ((fun u : ℂ => u + β) + ρ) (1 + deriv ρ w) w :=
        (hasDerivAt_id w).add_const β |>.add hρ_at.hasDerivAt
      have h6 : ((fun u : ℂ => u + β) + ρ) = fun u : ℂ => u + β + ρ u := by
        funext u; simp
      rw [h6] at h2
      exact h2.deriv
    have hdH : deriv (fun u : ℂ => H u) w = 1 + deriv ρ w := by
      rw [heq.deriv_eq, hderiv_eq]
    have hψeq : deriv ψ w = deriv ρ w := by
      rw [hψdef]
      exact deriv_sub_const c
    have hsmall : ‖deriv ρ w‖ ≤ 1 / 2 := by
      have h1 := (hdec w (by linarith : T ≤ w.im)).2
      have h2 : C * Real.exp (-2 * Real.pi * w.im) ≤ C * Real.exp (-2 * Real.pi * Y) :=
        mul_le_mul_of_nonneg_left (exp_neg_two_pi_anti (by linarith)) hCnn
      have h3 : ‖deriv ρ w‖ = ‖deriv ψ w‖ := by rw [hψeq]
      linarith [hY5]
    rw [hdH]
    calc ‖1 + deriv ρ w‖ ≤ 1 + ‖deriv ρ w‖ := by
          simpa using norm_add_le (1 : ℂ) (deriv ρ w)
      _ ≤ 3 / 2 := by linarith
  have hinj : Set.InjOn L {z : ℂ | Y < z.im} := by
    intro a ha b hb hab
    by_contra hne
    have hconv : Convex ℝ {z : ℂ | Y < z.im} := convex_halfSpace_im_gt Y
    have hD : ∀ x ∈ {z : ℂ | Y < z.im}, DifferentiableAt ℂ S x := fun x hx => hS_at x hx
    have hbnd : ∀ x ∈ {z : ℂ | Y < z.im}, ‖fderiv ℂ S x‖ ≤ 1 / 2 := by
      intro x hx
      rw [← norm_deriv_eq_norm_fderiv]
      exact le_trans (hSderiv' x hx) hSbound
    have hmvt : ‖S b - S a‖ ≤ (1 / 2) * ‖b - a‖ :=
      hconv.norm_image_sub_le_of_norm_fderiv_le hD hbnd ha hb
    have h1 : b + S b = a + S a := by
      simpa only [hLdef] using hab.symm
    have hkey : b - a = S a - S b :=
      sub_eq_sub_iff_add_eq_add.mpr (by rw [add_comm (S a)]; exact h1)
    have hle : ‖b - a‖ ≤ (1 / 2) * ‖b - a‖ := by
      calc ‖b - a‖ = ‖S a - S b‖ := by rw [hkey]
        _ = ‖S b - S a‖ := norm_sub_rev _ _
        _ ≤ (1 / 2) * ‖b - a‖ := hmvt
    have hzero : ‖b - a‖ = 0 := by linarith [norm_nonneg (b - a)]
    exact hne (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm
  refine ⟨L, Y, hY1, ?_, hHderiv, hinj⟩
  intro w hw
  have hyw : y < w.im := by linarith
  have hHw : Y < (H w).im := by
    have h := hdrift w hyw
    have h2 : (H w - w).im = (H w).im - w.im := Complex.sub_im _ _
    linarith
  exact ⟨hLdiff w hw, hfun w hw, hHw, hLderiv1 w hw⟩

end

end Work.L62
