import Submission.NBody.LYZRatio
import Submission.NBody.CalibratingCurve
import Submission.Commons.Topology.Metric.exists_strictMono_tendstoUniformlyOn_compacts_of_holder
import Mathlib

/-!
# Liu--Yan--Zhou §7-§8: the limiting geodesic ray

This module builds the curve `γ : [0,∞) → Eᴺ` obtained as the limit of the `h`-minimisers
`γ_n : [0, 2^n/√(2h) • a]` of Liu--Yan--Zhou, and proves the properties needed for the final
theorem: `γ` is an `h`-minimiser on every `[0,T]`, it avoids collisions for large times, and
`γ(t) = √(2h) t a + o(t)`.

The first ingredient is the *limit-minimiser lemma*: the uniform limit of a family of
`h`-minimisers (with a uniform `L²` bound on the velocities) is again an `h`-minimiser.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-! ## The uniform limit of `h`-minimisers is an `h`-minimiser -/

/-- If `g n → g` with a uniform Hölder modulus, then the values `Φ (g n)` tend to `Φ g`. -/
lemma tendsto_actionPot_snd_of_tendsto {m : Fin N → ℝ} {h : ℝ} {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hest : ∀ x y : EN E N, actionPot m h x y ≤ ENNReal.ofReal
      (Real.sqrt (α * ‖x - y‖ + h * β * ‖x - y‖ ^ 2)))
    (x : EN E N) {z : EN E N} {zs : ℕ → EN E N} (hz : Tendsto zs atTop (𝓝 z)) :
    Tendsto (fun n => actionPot m h x (zs n)) atTop (𝓝 (actionPot m h x z)) := by
  have hfin : ∀ p q : EN E N, actionPot m h p q < ⊤ :=
    fun p q => lt_of_le_of_lt (hest p q) ENNReal.ofReal_lt_top
  have hd : Tendsto (fun n => ‖zs n - z‖) atTop (𝓝 0) := by
    have h' : Tendsto (fun n => zs n - z) atTop (𝓝 (z - z)) := hz.sub tendsto_const_nhds
    simpa using h'.norm
  have hs : Tendsto (fun n => Real.sqrt (α * ‖zs n - z‖ + h * β * ‖zs n - z‖ ^ 2)) atTop (𝓝 0) := by
    have hp : Tendsto (fun n => α * ‖zs n - z‖ + h * β * ‖zs n - z‖ ^ 2) atTop
        (𝓝 (α * 0 + h * β * 0 ^ 2)) :=
      (tendsto_const_nhds.mul hd).add (tendsto_const_nhds.mul (hd.pow 2))
    have h3 := (Real.continuous_sqrt.tendsto (α * 0 + h * β * 0 ^ 2)).comp hp
    have h4 : Real.sqrt (α * 0 + h * β * 0 ^ 2) = 0 := by simp
    rwa [h4] at h3
  have hsub : Tendsto (fun n => (actionPot m h x (zs n)).toReal) atTop
      (𝓝 ((actionPot m h x z).toReal)) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa [Real.norm_eq_abs] using hs)
    rw [Real.norm_eq_abs]
    exact actionPot_toReal_sub_le' hα hβ hfin hest x _ _
  have h2 : Tendsto (fun n => ENNReal.ofReal ((actionPot m h x (zs n)).toReal)) atTop
      (𝓝 (ENNReal.ofReal ((actionPot m h x z).toReal))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hsub
  have h3 : (fun n => ENNReal.ofReal ((actionPot m h x (zs n)).toReal))
      = fun n => actionPot m h x (zs n) := by
    funext n; exact ENNReal.ofReal_toReal (hfin x (zs n)).ne
  rw [h3, ENNReal.ofReal_toReal (hfin x z).ne] at h2
  exact h2

/-- **The uniform limit of `h`-minimisers is an `h`-minimiser.** -/
theorem isHMinimizer_of_tendstoUniformlyOn {m : Fin N → ℝ} {h : ℝ} (hN : 0 < N) (hh : 0 < h)
    (hm : ∀ i, 0 < m i) {cc : ℝ} (hcc : 0 < cc) (hmc : ∀ i, cc ≤ m i)
    {x₀ : EN E N} {T M0 : ℝ} (hT : 0 < T) (hM0 : 0 ≤ M0)
    {F : ℕ → ℝ → EN E N} {G : ℝ → EN E N}
    (hF0 : ∀ n, F n 0 = x₀) (hG0 : G 0 = x₀) (hGcont : ContinuousOn G (Set.Icc 0 T))
    (hconv : TendstoUniformlyOn F G atTop (Set.Icc 0 T))
    (hFcont : ∀ n, ContinuousOn (F n) (Set.Icc 0 T))
    (hAC : ∀ n, AbsolutelyContinuousOnInterval (F n) 0 T)
    (hkin : ∀ n, ∫⁻ t in Set.Ioc 0 T, ENNReal.ofReal (kinetic m (deriv (F n) t))
        ≤ ENNReal.ofReal (M0 ^ 2))
    (hminT : ∀ n, IsHMinimizer m h (F n) 0 T) :
    IsHMinimizer m h G 0 T := by
  classical
  have hm0 : ∀ i, 0 ≤ m i := fun i => le_trans hcc.le (hmc i)
  obtain ⟨α, β, hα, hβ, hest⟩ := actionPot_le_holder (E := E) (N := N) hN hm hh.le
  have hfin : ∀ x y : EN E N, actionPot m h x y < ⊤ :=
    fun x y => lt_of_le_of_lt (hest x y) ENNReal.ofReal_lt_top
  -- uniform convergence on `[0,T]` implies uniform convergence on any subinterval
  have huni : ∀ s ∈ Set.Icc (0:ℝ) T, Tendsto (fun n => F n s) atTop (𝓝 (G s)) :=
    fun s hs => hconv.tendsto_at hs
  -- lower semicontinuity of the kinetic and potential parts
  have hMWT := Commons.MeasureTheory.Integral.massWeighted_kinetic_le_liminf (m := m) (c := cc)
    hcc hmc hT.le hM0 hGcont hconv hAC hkin
  have hp : (∫⁻ t in Set.Ioc 0 T, pairPot m (G t))
      ≤ liminf (fun n => ∫⁻ t in Set.Ioc 0 T, pairPot m (F n t)) atTop :=
    lintegral_pairPot_le_liminf' hm0
      (fun t ht => huni t ⟨ht.1.le, ht.2⟩)
      (fun n => (hFcont n).mono (fun s hs => ⟨hs.1.le, hs.2⟩))
  have hpmeas : AEMeasurable (fun t => pairPot m (G t)) (volume.restrict (Set.Ioc 0 T)) :=
    aemeasurable_pairPot_comp (hGcont.mono (fun s hs => ⟨hs.1.le, hs.2⟩)) measurableSet_Ioc
  have hmain : actionOn m h G 0 T ≤ liminf (fun n => actionOn m h (F n) 0 T) atTop :=
    actionOn_le_liminf hm hh.le hpmeas hMWT.2 hp
  -- the actions of the minimisers converge
  have heq : (fun n => actionOn m h (F n) 0 T) = fun n => actionPot m h x₀ (F n T) := by
    funext n
    rw [hminT n, hF0 n]
  have hAlim : Tendsto (fun n => actionOn m h (F n) 0 T) atTop (𝓝 (actionPot m h x₀ (G T))) := by
    rw [heq]
    exact tendsto_actionPot_snd_of_tendsto (m := m) (h := h) hα.le hβ.le hest x₀
      (huni T ⟨hT.le, le_rfl⟩)
  refine le_antisymm ?_ ?_
  · rw [hG0]
    calc actionOn m h G 0 T ≤ liminf (fun n => actionOn m h (F n) 0 T) atTop := hmain
      _ = actionPot m h x₀ (G T) := hAlim.liminf_eq
  · rw [hG0]
    exact actionPot_le_of_interval hT hG0 rfl hMWT.1


/-! ## The uniform Hölder bound for the LYZ family -/

/-- Reverse symmetry of the mass norm of a difference. -/
lemma weightedNorm_sub_rev {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (v w : EN E N) :
    ‖v - w‖_[m] = ‖w - v‖_[m] := by
  rw [weightedNorm_eq_norm_massScale hm, weightedNorm_eq_norm_massScale hm,
    massScale_sub, massScale_sub, norm_sub_rev]

/-- **The uniform Hölder bound.**  Let `γ n` be an absolutely continuous curve on `[0, τ n]` whose
squared speed has `∫⁻`-integral at most `A + B t` on `[0,t]`.  Then, after truncating `γ n` at
`T n`, the family is uniformly Hölder-`1/2` on `[0, T j]` with constant `√(A + B T j)`. -/
theorem lyz_holder_bound {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    {τ : ℕ → ℝ} {γ : ℕ → ℝ → EN E N} {T : ℕ → ℝ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hTmono : Monotone T) (hTnn : ∀ j, 0 ≤ T j)
    (hτ : ∀ n, T n ≤ τ n)
    (hac : ∀ n, AbsolutelyContinuousOnInterval (γ n) 0 (τ n))
    (hL2 : ∀ n t, t ∈ Set.Icc 0 (τ n) →
      ∫⁻ u in Set.Ioc 0 t, ENNReal.ofReal (‖deriv (γ n) u‖_[m] ^ 2)
        ≤ ENNReal.ofReal (A + B * t)) :
    ∀ j n (s t : ℝ), s ∈ Set.Icc 0 (T j) → t ∈ Set.Icc 0 (T j) →
      ‖γ n (min s (T n)) - γ n (min t (T n))‖_[m]
        ≤ Real.sqrt (A + B * T j) * Real.sqrt |s - t| := by
  intro j n s t hs ht
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hMnn : 0 ≤ Real.sqrt (A + B * T j) := Real.sqrt_nonneg _
  have habs : |min s (T n) - min t (T n)| ≤ |s - t| := by
    have h := abs_min_sub_min_le_max s (T n) t (T n)
    rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at h
    exact h
  -- the bound for arguments `a ≤ b` inside `[0, T n]` with `a, b ≤ T j`
  have hkey : ∀ a b : ℝ, a ∈ Set.Icc 0 (T n) → b ∈ Set.Icc 0 (T n) → a ≤ b →
      a ≤ T j → b ≤ T j →
      ‖γ n a - γ n b‖_[m] ≤ Real.sqrt (A + B * T j) * Real.sqrt |a - b| := by
    intro a b ha hb hab _ hbT
    have haτ : a ≤ τ n := le_trans ha.2 (hτ n)
    have hbτ : b ≤ τ n := le_trans hb.2 (hτ n)
    have hAc : AbsolutelyContinuousOnInterval (γ n) a b := (hac n).mono (by
      rw [uIcc_of_le hab, uIcc_of_le (le_trans ha.1 haτ)]
      exact Set.Icc_subset_Icc ha.1 hbτ)
    have hint : ∫⁻ u in Set.Ioc a b, ENNReal.ofReal (‖deriv (γ n) u‖_[m] ^ 2)
        ≤ ENNReal.ofReal (A + B * T j) := by
      refine (lintegral_mono_set (s := Set.Ioc a b) (t := Set.Ioc (0:ℝ) b)
        (f := fun u => ENNReal.ofReal (‖deriv (γ n) u‖_[m] ^ 2)) ?_).trans
        ((hL2 n b ⟨hb.1, hbτ⟩).trans ?_)
      · exact fun x hx => ⟨lt_of_le_of_lt ha.1 hx.1, hx.2⟩
      · exact ENNReal.ofReal_le_ofReal (by nlinarith [hA, hB, hbT])
    have h0 : 0 ≤ A + B * T j := by nlinarith [hA, hB, hTnn j]
    have hmain := weightedNorm_sub_le_sqrt_mul_sqrt hm hab h0 hAc hint
    have hsqrt : Real.sqrt (b - a) = Real.sqrt |a - b| := by
      rw [abs_of_nonpos (by linarith : a - b ≤ 0), neg_sub]
    rw [hsqrt] at hmain
    rwa [weightedNorm_sub_rev hm0] at hmain
  have ha_mem : min s (T n) ∈ Set.Icc 0 (T n) := ⟨le_min hs.1 (hTnn n), min_le_right _ _⟩
  have hb_mem : min t (T n) ∈ Set.Icc 0 (T n) := ⟨le_min ht.1 (hTnn n), min_le_right _ _⟩
  have haT : min s (T n) ≤ T j := le_trans (min_le_left _ _) hs.2
  have hbT : min t (T n) ≤ T j := le_trans (min_le_left _ _) ht.2
  rcases le_total (min s (T n)) (min t (T n)) with hle | hle
  · exact (hkey _ _ ha_mem hb_mem hle haT hbT).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt habs) hMnn)
  · have habs' : |min t (T n) - min s (T n)| ≤ |s - t| := by
      rw [abs_sub_comm]; exact habs
    have h := hkey _ _ hb_mem ha_mem hle hbT haT
    exact (le_of_eq (weightedNorm_sub_rev hm0 _ _).symm).trans
      (h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt habs') hMnn))


/-! ## The scale of Liu--Yan--Zhou -/

/-- The scale of Liu--Yan--Zhou: `2^j / (2√(2h))`. -/
noncomputable def lyzScale (h : ℝ) (j : ℕ) : ℝ := (2:ℝ) ^ j / (2 * Real.sqrt (2 * h))

lemma lyzScale_pos {h : ℝ} (hh : 0 < h) (j : ℕ) : 0 < lyzScale h j := by
  unfold lyzScale; positivity

lemma lyzScale_nonneg {h : ℝ} (hh : 0 < h) (j : ℕ) : 0 ≤ lyzScale h j :=
  (lyzScale_pos hh j).le

/-- The scale is nondecreasing in the exponent. -/
lemma lyzScale_mono {h : ℝ} (hh : 0 < h) : Monotone (lyzScale h) := by
  intro i j hij
  unfold lyzScale
  have h1 : (2:ℝ) ^ i ≤ (2:ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hij
  exact div_le_div_of_nonneg_right h1 (by positivity)

/-- The scale tends to infinity. -/
lemma tendsto_lyzScale {h : ℝ} (hh : 0 < h) : Tendsto (lyzScale h) atTop atTop := by
  have h1 : Tendsto (fun j : ℕ => (2:ℝ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)
  have h2 : Tendsto (fun j : ℕ => (2 * Real.sqrt (2 * h))⁻¹ * (2:ℝ) ^ j) atTop atTop :=
    h1.const_mul_atTop (by positivity)
  refine h2.congr' ?_
  filter_upwards with j
  unfold lyzScale
  rw [div_eq_inv_mul]


/-! ## The properties of the limiting curve -/

/-- **The properties of the limiting curve.**  Assuming the diagonal extraction produced `G` as the
uniform limit, on every `[0, lyzScale h j]`, of the family of `h`-minimisers `γ (φ k)`, the curve
`G` is an `h`-minimiser (hence absolutely continuous) on every `[0,T]`, it is collision free for
`t ≥ lyzScale h (n₀+2)`, and it satisfies the asymptotic shape estimate. -/
theorem exists_lyz_limit {m : Fin N → ℝ} {h : ℝ} (hN : 0 < N) (hh : 0 < h) (hm : ∀ i, 0 < m i)
    {cc : ℝ} (hcc : 0 < cc) (hmc : ∀ i, cc ≤ m i)
    {x₀ xstar a : EN E N} {ν : ℝ} (hν : 0 < ν) {n₀ : ℕ}
    {τ : ℕ → ℝ} {γ : ℕ → ℝ → EN E N} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hτ : ∀ n, lyzScale h n ≤ τ n) (hac : ∀ n, AbsolutelyContinuousOnInterval (γ n) 0 (τ n))
    (hfin : ∀ n, actionOn m h (γ n) 0 (τ n) < ⊤)
    (hγ0 : ∀ n, γ n 0 = x₀) (hmin : ∀ n, IsHMinimizer m h (γ n) 0 (τ n))
    (hInt : ∀ n t, t ∈ Set.Icc 0 (τ n) →
      ∫⁻ u in Set.Ioc 0 t, ENNReal.ofReal (‖deriv (γ n) u‖_[m] ^ 2)
        ≤ ENNReal.ofReal (A + B * t))
    (hsep : ∀ n t, t ∈ Set.Icc (lyzScale h (n₀ + 2)) (τ n) → Separated (γ n t) ν)
    {Ψb : ℝ → ℝ} (hΨbnn : ∀ t, 0 ≤ Ψb t)
    (hshape : ∀ n t, t ∈ Set.Icc (lyzScale h (n₀ + 2)) (τ n) →
      ‖γ n t - xstar - (Real.sqrt (2 * h) * t) • a‖_[m] ^ 2
        ≤ 2 ^ 22 * Ψb (Real.sqrt (2 * h) * t / 2) ^ 2 * (Real.sqrt (2 * h) * t) ^ 2)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {G : ℝ → EN E N} (hG0 : G 0 = x₀)
    (hGcont : ContinuousOn G (Set.Ici 0))
    (hGconv : ∀ j, TendstoUniformlyOn (fun k => γ (φ k)) G atTop (Set.Icc 0 (lyzScale h j))) :
    (∀ T : ℝ, 0 < T → IsHMinimizer m h G 0 T ∧ AbsolutelyContinuousOnInterval G 0 T) ∧
    (∀ t : ℝ, lyzScale h (n₀ + 2) ≤ t → WithoutCollisions (G t)) ∧
    (∀ t : ℝ, lyzScale h (n₀ + 2) ≤ t →
      ‖G t - xstar - (Real.sqrt (2 * h) * t) • a‖_[m]
        ≤ 2 ^ 11 * Ψb (Real.sqrt (2 * h) * t / 2) * (Real.sqrt (2 * h) * t)) := by
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hg_pos : (0:ℝ) < 2 * Real.sqrt (2 * h) := by positivity
  have hTend : Tendsto (lyzScale h) atTop atTop := tendsto_lyzScale hh
  -- a scale beyond a given time, at least `n₀ + 2`
  have hex : ∀ t : ℝ, ∃ j : ℕ, n₀ + 2 ≤ j ∧ t ≤ lyzScale h j := by
    intro t
    obtain ⟨j₀, hj₀⟩ : ∃ j : ℕ, ∀ j' ≥ j, t ≤ lyzScale h j' :=
      eventually_atTop.mp (hTend.eventually_ge_atTop t)
    exact ⟨max j₀ (n₀ + 2), le_max_right _ _, hj₀ _ (le_max_left _ _)⟩
  -- the `∫⁻`-to-`kinetic` bridge
  have hbridge : ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc 0 (τ n) →
      ∫⁻ u in Set.Ioc 0 t, ENNReal.ofReal (kinetic m (deriv (γ n) u))
        = ENNReal.ofReal ((1:ℝ) / 2) * ∫⁻ u in Set.Ioc 0 t,
            ENNReal.ofReal (‖deriv (γ n) u‖_[m] ^ 2) := by
    intro n t _
    rw [← lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top (r := (1:ℝ)/2))]
    refine lintegral_congr fun u => ?_
    rw [kinetic_eq_half_weightedNorm_sq' hm0,
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
  -- (b) and (c): the collision freeness and the asymptotic shape
  have hb : ∀ t : ℝ, lyzScale h (n₀ + 2) ≤ t → WithoutCollisions (G t) := by
    intro t ht i j' hij
    obtain ⟨j, hj⟩ := hex t
    have htmem : t ∈ Set.Icc (0:ℝ) (lyzScale h j) := ⟨le_trans (lyzScale_nonneg hh (n₀ + 2)) ht, hj.2⟩
    have htend := (hGconv j).tendsto_at htmem
    have hmemτ : ∀ᶠ k in atTop, t ∈ Set.Icc (lyzScale h (n₀ + 2)) (τ (φ k)) := by
      filter_upwards [Filter.eventually_ge_atTop j] with k hk
      exact ⟨ht, le_trans (le_trans hj.2 (lyzScale_mono hh (le_trans hk (hφ.id_le k)))) (hτ _)⟩
    have h1 : Tendsto (fun k => (γ (φ k) t) i) atTop (𝓝 ((G t) i)) :=
      ((PiLp.continuous_apply 2 (fun _ : Fin N => E) i).tendsto (G t)).comp htend
    have h2 : Tendsto (fun k => (γ (φ k) t) j') atTop (𝓝 ((G t) j')) :=
      ((PiLp.continuous_apply 2 (fun _ : Fin N => E) j').tendsto (G t)).comp htend
    have hle : ν ≤ dist ((G t) i) ((G t) j') :=
      le_of_tendsto_of_tendsto tendsto_const_nhds (h1.dist h2)
        (hmemτ.mono fun k hk => hsep (φ k) t hk i j' hij)
    exact ne_of_gt (lt_of_lt_of_le hν hle)
  have hc : ∀ t : ℝ, lyzScale h (n₀ + 2) ≤ t →
      ‖G t - xstar - (Real.sqrt (2 * h) * t) • a‖_[m]
        ≤ 2 ^ 11 * Ψb (Real.sqrt (2 * h) * t / 2) * (Real.sqrt (2 * h) * t) := by
    intro t ht
    obtain ⟨j, hj⟩ := hex t
    have htmem : t ∈ Set.Icc (0:ℝ) (lyzScale h j) := ⟨le_trans (lyzScale_nonneg hh (n₀ + 2)) ht, hj.2⟩
    have hmemτ : ∀ᶠ k in atTop, t ∈ Set.Icc (lyzScale h (n₀ + 2)) (τ (φ k)) := by
      filter_upwards [Filter.eventually_ge_atTop j] with k hk
      exact ⟨ht, le_trans (le_trans hj.2 (lyzScale_mono hh (le_trans hk (hφ.id_le k)))) (hτ _)⟩
    have hsq : Tendsto (fun k => ‖γ (φ k) t - xstar - (Real.sqrt (2 * h) * t) • a‖_[m] ^ 2)
        atTop (𝓝 (‖G t - xstar - (Real.sqrt (2 * h) * t) • a‖_[m] ^ 2)) := by
      have h1 : Tendsto (fun k => γ (φ k) t - xstar - (Real.sqrt (2 * h) * t) • a) atTop
          (𝓝 (G t - xstar - (Real.sqrt (2 * h) * t) • a)) :=
        (((hGconv j).tendsto_at htmem).sub tendsto_const_nhds).sub tendsto_const_nhds
      exact (((continuous_weightedNorm' m).tendsto _).comp h1).pow 2
    have hle : ‖G t - xstar - (Real.sqrt (2 * h) * t) • a‖_[m] ^ 2
        ≤ (2 ^ 11 * Ψb (Real.sqrt (2 * h) * t / 2) * (Real.sqrt (2 * h) * t)) ^ 2 := by
      refine le_of_tendsto hsq ?_
      refine hmemτ.mono fun k hk => ?_
      refine (hshape (φ k) t hk).trans ?_
      have h2 : (2:ℝ) ^ 22 = (2 ^ 11 : ℝ) ^ 2 := by norm_num
      calc (2:ℝ) ^ 22 * Ψb (Real.sqrt (2 * h) * t / 2) ^ 2 * (Real.sqrt (2 * h) * t) ^ 2
          = (2 ^ 11 * Ψb (Real.sqrt (2 * h) * t / 2) * (Real.sqrt (2 * h) * t)) ^ 2 := by
            rw [h2]; ring
        _ ≤ _ := le_rfl
    have h3 : (0:ℝ) ≤ 2 ^ 11 * Ψb (Real.sqrt (2 * h) * t / 2) * (Real.sqrt (2 * h) * t) := by
      have h4 : (0:ℝ) ≤ Real.sqrt (2 * h) * t :=
        mul_nonneg (Real.sqrt_nonneg _) (le_trans (lyzScale_nonneg hh (n₀ + 2)) ht)
      have h5 : (0:ℝ) ≤ Ψb (Real.sqrt (2 * h) * t / 2) := hΨbnn _
      positivity
    calc ‖G t - xstar - (Real.sqrt (2 * h) * t) • a‖_[m]
        = Real.sqrt (‖G t - xstar - (Real.sqrt (2 * h) * t) • a‖_[m] ^ 2) :=
          (Real.sqrt_sq (weightedNorm_nonneg m _)).symm
      _ ≤ Real.sqrt ((2 ^ 11 * Ψb (Real.sqrt (2 * h) * t / 2)
            * (Real.sqrt (2 * h) * t)) ^ 2) := Real.sqrt_le_sqrt hle
      _ = 2 ^ 11 * Ψb (Real.sqrt (2 * h) * t / 2) * (Real.sqrt (2 * h) * t) :=
          Real.sqrt_sq h3
  refine ⟨?_, hb, hc⟩
  -- (a): the limit is an `h`-minimiser on every `[0,T]`
  intro T hT
  obtain ⟨j, hj⟩ := hex T
  have h0T : (0:ℝ) ≤ T := hT.le
  have hΦmono : ∀ k : ℕ, j ≤ φ (k + j) := fun k =>
    le_trans (Nat.le_add_left j k) (hφ.id_le (k + j))
  have hΦτ : ∀ k : ℕ, T ≤ τ (φ (k + j)) := fun k =>
    le_trans (le_trans hj.2 (lyzScale_mono hh (hΦmono k))) (hτ _)
  have hconvT : TendstoUniformlyOn (fun k => γ (φ (k + j))) G atTop (Set.Icc 0 T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp (hGconv j)) ε hε)
    refine eventually_atTop.mpr ⟨N, fun k hk x hx => ?_⟩
    exact hN (k + j) (le_trans hk (Nat.le_add_right k j)) x ⟨hx.1, le_trans hx.2 hj.2⟩
  have hAC : ∀ k : ℕ, AbsolutelyContinuousOnInterval (γ (φ (k + j))) 0 T := fun k =>
    (hac _).mono (by
      rw [uIcc_of_le h0T, uIcc_of_le (le_trans h0T (hΦτ k))]
      exact Set.Icc_subset_Icc_right (hΦτ k))
  have hM0sq : Real.sqrt ((A + B * T) / 2) ^ 2 = (A + B * T) / 2 :=
    Real.sq_sqrt (by nlinarith)
  have hkin : ∀ k : ℕ,
      ∫⁻ t in Set.Ioc 0 T, ENNReal.ofReal (kinetic m (deriv (γ (φ (k + j))) t))
        ≤ ENNReal.ofReal (Real.sqrt ((A + B * T) / 2) ^ 2) := by
    intro k
    rw [hM0sq, hbridge _ T ⟨h0T, hΦτ k⟩]
    calc ENNReal.ofReal ((1:ℝ) / 2)
          * ∫⁻ u in Set.Ioc 0 T, ENNReal.ofReal (‖deriv (γ (φ (k + j))) u‖_[m] ^ 2)
        ≤ ENNReal.ofReal ((1:ℝ) / 2) * ENNReal.ofReal (A + B * T) :=
          mul_le_mul' le_rfl (hInt _ T ⟨h0T, hΦτ k⟩)
      _ = ENNReal.ofReal ((A + B * T) / 2) := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1 / 2)]
          congr 1
          ring
  have hminT : ∀ k : ℕ, IsHMinimizer m h (γ (φ (k + j))) 0 T := fun k =>
    IsHMinimizer.sub_left_of_le (hac _) (hmin _) (hfin _) hT (hΦτ k)
  have hmain := isHMinimizer_of_tendstoUniformlyOn (N := N) (F := fun k => γ (φ (k + j)))
    (G := G) (M0 := Real.sqrt ((A + B * T) / 2)) hN hh hm hcc hmc hT
    (Real.sqrt_nonneg _) (fun k => hγ0 _) hG0
    (hGcont.mono (fun x hx => hx.1)) hconvT
    (fun k => by simpa [uIcc_of_le h0T] using (hAC k).continuousOn) hAC hkin hminT
  refine ⟨hmain, ?_⟩
  exact (Commons.MeasureTheory.Integral.massWeighted_kinetic_le_liminf (m := m) (c := cc)
    hcc hmc hT.le (Real.sqrt_nonneg _) (hGcont.mono (fun x hx => hx.1)) hconvT hAC hkin).1

end Submission.NBody
