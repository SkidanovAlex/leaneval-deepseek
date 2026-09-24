import ChallengeDeps
import Submission.Commons.Analysis.Complex.Koebe.growth_bound
import Submission.Commons.Analysis.Complex.Koebe.weak_koebe_of_landau
import Submission.Commons.Analysis.Complex.Landau.landau_theorem
import Submission.Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_ball
import Submission.Commons.Analysis.Complex.Analytic.injOn_or_const_of_tendstoLocallyUniformlyOn

/-!
# Compactness of normalised univalent families on the disc

Anghel–Bruin–Stan, *Uniformization of Riemann surfaces revisited*, Appendix AC: a sequence of
*injective* holomorphic functions on the unit disc, normalised by `f n 0 = 0` and `deriv (f n) 0 = 1`,
has a subsequence converging locally uniformly to an injective holomorphic limit with the same
normalisations.  This is the engine of the exhaustion argument (the "diagonal limit" in §7 of the
paper).

The classical proof of that lemma rescales the family by the inner radius and uses a square root
trick to obtain a bound.  Here we instead use the **distortion bound** that the shared commons now
provides: Landau's theorem (`Commons.Analysis.Complex.Landau.landau_theorem`) gives a lower bound
`c₀ > 0` for the modulus of an omitted value of a normalised function, the weak Koebe inequality
(`Commons.Analysis.Complex.Koebe.weak_koebe_of_landau`) converts it into `c₀/π`, and the growth
bound (`Commons.Analysis.Complex.Koebe.growth_bound`, proved by a Grönwall estimate) turns it into

  `‖f z‖ + 1 ≤ ((1 + ‖z‖) / (1 - ‖z‖)) ^ C`

for a universal constant `C`.  In particular a normalised univalent family is *locally bounded with a
bound independent of the family member*, so Montel's theorem applies on each disc `‖z‖ ≤ ρ < 1` and
a diagonal extraction over the exhaustion `ρ k = 1 - 1/(k+2)` produces a subsequence converging
locally uniformly on all of `𝔻`; Hurwitz's theorem (in the ball form
`Commons.Analysis.Complex.Analytic.injOn_or_const_of_tendstoLocallyUniformlyOn`) then gives
injectivity of the limit, the constant alternative being excluded by the derivative normalisation.
-/

open Filter Metric Set
open scoped Topology

noncomputable section

open Classical

namespace Submission

theorem TendstoLocallyUniformlyOn.const_mul {α : Type*} [TopologicalSpace α] {F : ℕ → α → ℂ}
    {g : α → ℂ} {s : Set α} (h : TendstoLocallyUniformlyOn F g Filter.atTop s) (c : ℂ) :
    TendstoLocallyUniformlyOn (fun n x => c * F n x) (fun x => c * g x) Filter.atTop s := by
  intro u hu x hx
  have hv : {p : ℂ × ℂ | (c * p.1, c * p.2) ∈ u} ∈ uniformity ℂ := by
    rw [Metric.mem_uniformity_dist] at hu ⊢
    obtain ⟨ε, hε, hu'⟩ := hu
    refine ⟨ε / (‖c‖ + 1), by positivity, fun a b hab => ?_⟩
    have h2 : dist a b < ε / (‖c‖ + 1) := hab
    have hkey : ‖c‖ * (ε / (‖c‖ + 1)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < ‖c‖ + 1)]
      nlinarith [norm_nonneg c]
    have h1 : dist (c * a) (c * b) < ε := by
      rw [dist_eq_norm, ← mul_sub, norm_mul]
      have h3 : ‖a - b‖ = dist a b := by rw [dist_eq_norm]
      rw [h3]
      rcases eq_or_lt_of_le (norm_nonneg c) with hc0 | hcpos
      · rw [← hc0, zero_mul]; exact hε
      · exact lt_of_lt_of_le (mul_lt_mul_of_pos_left h2 hcpos) hkey
    exact hu' (a := c * a) (b := c * b) h1
  obtain ⟨t, ht, H⟩ := h _ hv x hx
  exact ⟨t, ht, H.mono fun n hn y hy => hn y hy⟩

/-- **Growth bound for normalized injective functions on the disc.**  There is a constant `C > 0`
such that every injective holomorphic `f` on `𝔻` with `f 0 = 0` and `deriv f 0 = 1` satisfies
`‖f z‖ + 1 ≤ ((1 + ‖z‖)/(1 - ‖z‖)) ^ C`. -/
theorem exists_growth_bound_normalized_injective :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ, (∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z) →
      Set.InjOn f (Metric.ball (0 : ℂ) 1) → f 0 = 0 → deriv f 0 = 1 →
      ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ + 1 ≤ ((1 + ‖z‖) / (1 - ‖z‖)) ^ C := by
  obtain ⟨c₀, hc₀, hlandau⟩ := Commons.Analysis.Complex.Landau.landau_theorem
  have hkoebe := Commons.Analysis.Complex.Koebe.weak_koebe_of_landau hc₀ hlandau
  have hpos : 0 < c₀ / Real.pi := by positivity
  exact ⟨1 / (c₀ / Real.pi), by positivity,
    fun f hf hinj h0 h1 => Commons.Analysis.Complex.Koebe.growth_bound hpos hkoebe hf hinj h0 h1⟩


/-- Composing a locally uniformly convergent sequence with a map tending to `atTop`. -/
theorem tendstoLocallyUniformlyOn_comp_tendsto_atTop' {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    {s : Set ℂ} {Θ : ℕ → ℕ} (h : TendstoLocallyUniformlyOn F g Filter.atTop s)
    (hΘ : Tendsto Θ Filter.atTop Filter.atTop) :
    TendstoLocallyUniformlyOn (fun n => F (Θ n)) g Filter.atTop s := by
  intro u hu x hx
  obtain ⟨t, ht, H⟩ := h u hu x hx
  exact ⟨t, ht, hΘ.eventually H⟩

/-- Shifting the index does not affect locally uniform convergence. -/
theorem tendstoLocallyUniformlyOn_shift' {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {s : Set ℂ} (c : ℕ) :
    TendstoLocallyUniformlyOn (fun n => F (n + c)) g Filter.atTop s ↔
      TendstoLocallyUniformlyOn F g Filter.atTop s := by
  refine ⟨fun h => ?_, fun h => tendstoLocallyUniformlyOn_comp_tendsto_atTop' h
    (tendsto_add_atTop_nat c)⟩
  intro u hu x hx
  obtain ⟨t, ht, H⟩ := h u hu x hx
  rw [Filter.eventually_atTop] at H
  obtain ⟨N, hN⟩ := H
  refine ⟨t, ht, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨N + c, fun m hm y hy => ?_⟩
  have hcm : c ≤ m := le_trans (Nat.le_add_left c N) hm
  have hsub : (m - c) + c = m := Nat.sub_add_cancel hcm
  have hN' : N ≤ m - c := by omega
  simpa [hsub] using hN (m - c) hN' y hy

/-- **Compactness of normalised injective holomorphic maps on the disc.** -/
theorem exists_subseq_tendstoLocallyUniformlyOn_of_injOn_deriv_one {f : ℕ → ℂ → ℂ}
    (hf : ∀ n, ∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ (f n) z)
    (hinj : ∀ n, Set.InjOn (f n) (Metric.ball (0 : ℂ) 1))
    (h0 : ∀ n, f n 0 = 0) (h1 : ∀ n, deriv (f n) 0 = 1) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g Filter.atTop (Metric.ball (0 : ℂ) 1) ∧
      AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) 1) ∧ Set.InjOn g (Metric.ball (0 : ℂ) 1) ∧
      g 0 = 0 ∧ deriv g 0 = 1 := by
  classical
  obtain ⟨C, hC, hgrowth⟩ := exists_growth_bound_normalized_injective
  -- radii 1/2, 2/3, 3/4, ... increasing to 1
  let ρ : ℕ → ℝ := fun k => 1 - ((k : ℝ) + 2)⁻¹
  have hρpos : ∀ k, 0 < ρ k := by
    intro k
    have h : (0:ℝ) < (k:ℝ) + 2 := by positivity
    have h2 : ((k:ℝ)+2)⁻¹ < 1 := by
      rw [inv_lt_one₀ h]; linarith
    simp only [ρ]; linarith
  have hρlt1 : ∀ k, ρ k < 1 := by
    intro k
    have h : 0 < (k:ℝ) + 2 := by positivity
    have : 0 < ((k:ℝ)+2)⁻¹ := inv_pos.mpr h
    simp only [ρ]; linarith
  let M : ℕ → ℝ := fun k => ((1 + ρ k) / (1 - ρ k)) ^ C
  have hMpos : ∀ k, 0 < M k := by
    intro k
    have h1 : 0 < 1 - ρ k := by linarith [hρlt1 k]
    have h2 : 0 < (1 + ρ k) / (1 - ρ k) := div_pos (by linarith [hρpos k]) h1
    exact Real.rpow_pos_of_pos h2 C
  have hMgt1 : ∀ k, 1 ≤ M k := by
    intro k
    have h1 : 0 < 1 - ρ k := by linarith [hρlt1 k]
    have h2 : (1 : ℝ) ≤ (1 + ρ k) / (1 - ρ k) := by
      rw [le_div_iff₀ h1]; linarith [hρpos k]
    calc (1:ℝ) = 1 ^ C := (Real.one_rpow C).symm
      _ ≤ ((1 + ρ k) / (1 - ρ k)) ^ C := Real.rpow_le_rpow (by norm_num) h2 hC.le
  -- the pointwise bound on the ball of radius `ρ k`
  have hbound : ∀ k n z, z ∈ Metric.ball (0:ℂ) (ρ k) → ‖f n z‖ ≤ M k := by
    intro k n z hz
    have hzk : ‖z‖ < ρ k := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hgr := hgrowth (f n) (hf n) (hinj n) (h0 n) (h1 n) z (by
      simp only [Metric.mem_ball, dist_eq_norm, sub_zero]
      linarith [hzk, hρlt1 k])
    have hD : ‖f n z‖ ≤ ((1 + ‖z‖) / (1 - ‖z‖)) ^ C - 1 := by linarith
    refine le_trans hD ?_
    have h1z : 0 < 1 - ‖z‖ := by linarith [hρlt1 k]
    have h2z : 0 < 1 - ρ k := by linarith [hρlt1 k]
    have hle : (1 + ‖z‖) / (1 - ‖z‖) ≤ (1 + ρ k) / (1 - ρ k) := by
      rw [div_le_div_iff₀ h1z h2z]
      nlinarith [norm_nonneg z]
    have hnn : 0 ≤ (1 + ‖z‖) / (1 - ‖z‖) := by positivity
    have hmono : ((1 + ‖z‖) / (1 - ‖z‖)) ^ C ≤ ((1 + ρ k) / (1 - ρ k)) ^ C :=
      Real.rpow_le_rpow hnn hle hC.le
    linarith
  -- the extraction at each level
  have hex : ∀ (k : ℕ) (u : ℕ → ℕ), ∃ (ψ : ℕ → ℕ) (G : ℂ → ℂ), StrictMono ψ ∧
      TendstoLocallyUniformlyOn (fun m => f (u (ψ m))) G Filter.atTop (Metric.ball 0 (ρ k)) ∧
      AnalyticOnNhd ℂ G (Metric.ball 0 (ρ k)) := by
    intro k u
    set c : ℝ := 2 * M k with hc
    have hcpos : 0 < c := by rw [hc]; exact mul_pos two_pos (hMpos k)
    have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
    have hf' : ∀ n z, z ∈ Metric.ball (0:ℂ) (ρ k) →
        AnalyticAt ℂ (fun w => f (u n) w / (c : ℂ)) z := by
      intro n z hz
      have hz1 : z ∈ Metric.ball (0:ℂ) 1 := by
        simp only [Metric.mem_ball, dist_eq_norm, sub_zero] at hz ⊢
        linarith [hρlt1 k]
      exact (hf (u n) z hz1).div_const
    have hb' : ∀ n z, z ∈ Metric.ball (0:ℂ) (ρ k) → ‖f (u n) z / (c : ℂ)‖ ≤ 1 := by
      intro n z hz
      have h1' : ‖f (u n) z‖ ≤ M k := hbound k (u n) z hz
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
      rw [div_le_iff₀ hcpos]
      nlinarith [hMgt1 k]
    obtain ⟨ψ, H, hψ, hconv, hH⟩ :=
      Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_ball
        (c := 0) (R := ρ k) (hρpos k) (f := fun n z => f (u n) z / (c : ℂ)) hf' hb'
    refine ⟨ψ, fun z => (c : ℂ) * H z, hψ, ?_, ?_⟩
    · have h1'' := Submission.TendstoLocallyUniformlyOn.const_mul hconv (c : ℂ)
      exact TendstoLocallyUniformlyOn.congr h1'' (fun m z hz => mul_div_cancel₀ _ hcne)
    · intro z hz
      exact analyticAt_const.mul (hH z hz)
  -- the diagonal recursion
  let psiOf : ℕ → (ℕ → ℕ) → (ℕ → ℕ) := fun k u => Classical.choose (hex k u)
  have psiOf_strict : ∀ k u, StrictMono (psiOf k u) :=
    fun k u => (Classical.choose_spec (Classical.choose_spec (hex k u))).1
  let GOf : ℕ → (ℕ → ℕ) → (ℂ → ℂ) :=
    fun k u => Classical.choose (Classical.choose_spec (hex k u))
  have GOf_spec : ∀ k u, TendstoLocallyUniformlyOn
      (fun m => f (u (psiOf k u m))) (GOf k u) Filter.atTop (Metric.ball 0 (ρ k)) :=
    fun k u => (Classical.choose_spec (Classical.choose_spec (hex k u))).2.1
  have GOf_ana : ∀ k u, AnalyticOnNhd ℂ (GOf k u) (Metric.ball 0 (ρ k)) :=
    fun k u => (Classical.choose_spec (Classical.choose_spec (hex k u))).2.2
  let U : ℕ → (ℕ → ℕ) := Nat.rec (motive := fun _ => ℕ → ℕ) id (fun k rec => rec ∘ psiOf k rec)
  have U_zero : U 0 = id := rfl
  have U_succ : ∀ k, U (k + 1) = U k ∘ psiOf k (U k) := fun k => rfl
  have U_strict : ∀ k, StrictMono (U k) := by
    intro k
    induction k with
    | zero => rw [U_zero]; exact strictMono_id
    | succ k ih => rw [U_succ k]; exact ih.comp (psiOf_strict k (U k))
  let diag : ℕ → ℕ := fun n => U n n
  have diag_strict : StrictMono diag := by
    apply strictMono_nat_of_lt_succ
    intro n
    have h1 : diag (n + 1) = U n (psiOf n (U n) (n + 1)) := by
      simp only [diag]; rw [U_succ n]; rfl
    have h2 : diag n = U n n := rfl
    rw [h1, h2]
    exact (U_strict n) (lt_of_lt_of_le (Nat.lt_succ_self n) ((psiOf_strict n (U n)).id_le (n + 1)))
  have range_succ : ∀ k, Set.range (U (k + 1)) ⊆ Set.range (U k) := by
    intro k
    rw [U_succ k]
    rintro y ⟨m, rfl⟩
    exact ⟨psiOf k (U k) m, rfl⟩
  have range_mono : ∀ k n, k ≤ n → Set.range (U n) ⊆ Set.range (U k) := by
    intro k n hkn
    induction hkn with
    | refl => exact subset_rfl
    | step h ih => exact (range_succ _).trans ih
  have diag_mem : ∀ k n, k + 1 ≤ n → diag n ∈ Set.range (U (k + 1)) := by
    intro k n hn
    exact range_mono (k + 1) n hn ⟨n, rfl⟩
  have ThetaSpec : ∀ k n, ∃ m, U (k + 1) m = diag (n + (k + 1)) :=
    fun k n => diag_mem k (n + (k + 1)) (Nat.le_add_left _ _)
  let Theta : ℕ → ℕ → ℕ := fun k n => Classical.choose (ThetaSpec k n)
  have Theta_eq : ∀ k n, U (k + 1) (Theta k n) = diag (n + (k + 1)) :=
    fun k n => Classical.choose_spec (ThetaSpec k n)
  have Theta_strict : ∀ k, StrictMono (Theta k) := by
    intro k
    apply strictMono_nat_of_lt_succ
    intro n
    have hlt : diag (n + (k + 1)) < diag (n + 1 + (k + 1)) :=
      diag_strict (show n + (k + 1) < n + 1 + (k + 1) by omega)
    rw [← Theta_eq k n, ← Theta_eq k (n + 1)] at hlt
    exact (U_strict (k + 1)).lt_iff_lt.mp hlt
  have Theta_tendsto : ∀ k, Tendsto (Theta k) Filter.atTop Filter.atTop := by
    intro k
    rw [Filter.tendsto_atTop_atTop]
    exact fun b => ⟨b, fun a ha => le_trans ha ((Theta_strict k).id_le a)⟩
  -- convergence on each member of the exhaustion
  have hconv_ball : ∀ k, TendstoLocallyUniformlyOn (fun n => f (diag n)) (GOf k (U k))
      Filter.atTop (Metric.ball 0 (ρ k)) := by
    intro k
    have h2 : TendstoLocallyUniformlyOn
        (fun m => f (U (k + 1) m)) (GOf k (U k)) Filter.atTop (Metric.ball 0 (ρ k)) := by
      have := GOf_spec k (U k)
      rw [U_succ k]
      simpa only [Function.comp_apply] using this
    have h3 := tendstoLocallyUniformlyOn_comp_tendsto_atTop' h2 (Theta_tendsto k)
    have h4 : TendstoLocallyUniformlyOn
        (fun n => f (diag (n + (k + 1)))) (GOf k (U k)) Filter.atTop (Metric.ball 0 (ρ k)) :=
      h3.congr fun n => fun z _ => by simp only [Theta_eq k n]
    exact (tendstoLocallyUniformlyOn_shift' (k + 1)).mp h4
  -- the limit
  let g : ℂ → ℂ := fun z => Filter.limUnder Filter.atTop (fun n => f (diag n) z)
  have hg_eq : ∀ k, EqOn (GOf k (U k)) g (Metric.ball 0 (ρ k)) := by
    intro k z hz
    have htend : Tendsto (fun n => f (diag n) z) Filter.atTop (𝓝 (GOf k (U k) z)) :=
      (hconv_ball k).tendsto_at hz
    show GOf k (U k) z = g z
    rw [show g z = Filter.limUnder Filter.atTop (fun n => f (diag n) z) from rfl]
    exact (Filter.Tendsto.limUnder_eq htend).symm
  have hcover : (⋃ k, Metric.ball (0:ℂ) (ρ k)) = Metric.ball (0:ℂ) 1 := by
    ext z
    simp only [mem_iUnion, Metric.mem_ball, dist_eq_norm, sub_zero]
    constructor
    · rintro ⟨k, hk⟩; exact lt_trans hk (hρlt1 k)
    · intro hz
      have hpos : 0 < 1 - ‖z‖ := by linarith
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 - ‖z‖))
      refine ⟨N, ?_⟩
      have hK : (0:ℝ) < (N:ℝ) + 2 := by positivity
      have h3 : 1 / (1 - ‖z‖) < (N:ℝ) + 2 := by linarith
      have h5 : 1 < ((N:ℝ) + 2) * (1 - ‖z‖) := by
        rw [div_lt_iff₀ hpos] at h3
        linarith
      have h4 : ((N:ℝ) + 2)⁻¹ < 1 - ‖z‖ := by
        rw [inv_eq_one_div, div_lt_iff₀ hK]
        linarith [h5, mul_comm ((N:ℝ) + 2) (1 - ‖z‖)]
      simp only [ρ]
      linarith
  have hconv_all : TendstoLocallyUniformlyOn (fun n => f (diag n)) g Filter.atTop
      (⋃ k, Metric.ball (0:ℂ) (ρ k)) :=
    tendstoLocallyUniformlyOn_iUnion (fun k => Metric.isOpen_ball) fun k =>
      (hconv_ball k).congr_right (hg_eq k)
  rw [hcover] at hconv_all
  -- the limit is analytic
  have hgana : AnalyticOnNhd ℂ g (Metric.ball (0:ℂ) 1) := by
    intro z hz
    have hz' : z ∈ ⋃ k, Metric.ball (0:ℂ) (ρ k) := by rw [hcover]; exact hz
    obtain ⟨k, hk⟩ := mem_iUnion.mp hz'
    have h1 : AnalyticAt ℂ (GOf k (U k)) z := GOf_ana k (U k) z hk
    refine h1.congr ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hk] with w hw
    exact (hg_eq k hw)
  -- injectivity
  have hg0 : g 0 = 0 := by
    have hmem : (0:ℂ) ∈ Metric.ball (0:ℂ) 1 := by simp
    have hmem' : (0:ℂ) ∈ (⋃ k, Metric.ball (0:ℂ) (ρ k)) := by
      rw [hcover]; simp
    have htend : Tendsto (fun n => f (diag n) 0) Filter.atTop (𝓝 (g 0)) :=
      hconv_all.tendsto_at hmem
    have h2 : Tendsto (fun n => f (diag n) 0) Filter.atTop (𝓝 0) := by
      simpa [h0] using tendsto_const_nhds (f := Filter.atTop) (x := (0:ℂ))
    exact tendsto_nhds_unique htend h2
  have hderiv : deriv g 0 = 1 := by
    have hdiff : ∀ᶠ n in Filter.atTop,
        DifferentiableOn ℂ (f (diag n)) (Metric.ball (0:ℂ) 1) := by
      refine Eventually.of_forall fun n => ?_
      intro z hz
      exact ((hf (diag n) z hz)).differentiableWithinAt
    have hder := hconv_all.deriv hdiff Metric.isOpen_ball
    have htend : Tendsto (fun n => deriv (f (diag n)) 0) Filter.atTop (𝓝 (deriv g 0)) :=
      hder.tendsto_at (by simp)
    have hconst : (fun n => deriv (f (diag n)) 0) = fun _ => (1:ℂ) := funext fun n => h1 (diag n)
    rw [hconst] at htend
    exact tendsto_nhds_unique htend (tendsto_const_nhds (f := Filter.atTop) (x := (1:ℂ)))
  have hinjOn : Set.InjOn g (Metric.ball (0:ℂ) 1) := by
    rcases Commons.Analysis.Complex.Analytic.injOn_or_const_of_tendstoLocallyUniformlyOn
      (R := 1) one_pos (fun n => hf (diag n)) (fun z hz => hgana z hz) hconv_all
      (fun n => hinj (diag n)) with h | h
    · exact h
    · exfalso
      obtain ⟨c, hc⟩ := h
      have hzero : deriv g 0 = 0 := by
        have hconst : g =ᶠ[𝓝 (0:ℂ)] fun _ => c := by
          filter_upwards [Metric.isOpen_ball.mem_nhds (by simp : (0:ℂ) ∈ Metric.ball (0:ℂ) 1)]
            with z hz
          exact hc z hz
        rw [Filter.EventuallyEq.deriv_eq hconst, deriv_const]
      rw [hzero] at hderiv
      exact one_ne_zero hderiv.symm
  exact ⟨diag, g, diag_strict, hconv_all, hgana, hinjOn, hg0, hderiv⟩

end Submission
