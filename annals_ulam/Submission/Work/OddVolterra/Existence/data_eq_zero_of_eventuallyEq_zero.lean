import Mathlib
import Submission.Work.OddVolterra.Defs

/-!
# The odd data agrees with the data of `h ≡ 0` where `h` vanishes

If `h` vanishes on a right-neighbourhood of `s` -- in the situation of the odd
transition-slope argument this means that `h` is supported to the *left* of the
window -- then every object of `Defs.lean` that is attached to a slope `u > s - δ`
(and to a second slope `σ ≥ s`, i.e. also `σ > s - δ`) coincides with the object
built from `h ≡ 0`.

The point is that all the kernels `J₁`, `J₂`, `Kden`, `K₁`, `K₂`, `Kvec`, `G2`,
and all the inhomogeneities `E₁`, `E₂`, `Q`, `Q̃`, `𝚵` depend on `h` only through
the values `line h u t`, `lineSlope h u t`, `deriv h (·)` and the iterated
`s`-derivatives of `u ↦ ψ(h, σ, u, t)` at points where `h` is locally zero.  The
only place where the integration range matters is the Abel transform in `Qtilde`;
there the extra case `u > 1` is handled separately, where the integrand vanishes
identically because `√(v - u) = 0` for `v < u`.
-/

open Work.OddVolterra Commons.Geometry.Ulam

open MeasureTheory Set Filter

open scoped Topology Interval

namespace Work.OddVolterra.Existence

variable {h : ℝ → ℝ} {a : ℝ}

/-! ## Elementary consequences of `h` vanishing on `(a, ∞)` -/

lemma deriv_eq_zero_of_gt (hz : ∀ x, a < x → h x = 0) {x : ℝ} (hx : a < x) :
    deriv h x = 0 := by
  have hev : h =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) :=
    Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Ioi hx) (fun y hy => hz y hy)
  rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]

/-- A convex combination of `u` and `σ` is at least `min u σ`. -/
lemma min_le_of_convex (u σ τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    min u σ ≤ u + τ * (σ - u) := by
  have h2 : 0 ≤ 1 - τ := by linarith
  have h3 : u + τ * (σ - u) = (1 - τ) * u + τ * σ := by ring
  rw [h3]
  nlinarith [min_le_left u σ, min_le_right u σ,
    mul_nonneg h2 (sub_nonneg.mpr (min_le_left u σ)),
    mul_nonneg h0 (sub_nonneg.mpr (min_le_right u σ))]

lemma line_eq_of_gt (hz : ∀ x, a < x → h x = 0) {u : ℝ} (hu : a < u) (t : ℝ) :
    line h u t = line 0 u t := by
  unfold line
  rw [hz u hu]
  simp

lemma lineSlope_eq_of_gt (hz : ∀ x, a < x → h x = 0) {u : ℝ} (hu : a < u) (t : ℝ) :
    lineSlope h u t = lineSlope 0 u t := by
  unfold lineSlope
  rw [deriv_eq_zero_of_gt hz hu]
  simp

lemma hquot_eq_zero_of_gt (hz : ∀ x, a < x → h x = 0) {u σ : ℝ} (hu : a < u) (hσ : a < σ) :
    hquot h u σ = 0 := by
  unfold hquot
  have hcongr : (∫ τ in (0:ℝ)..1, deriv h (u + τ * (σ - u))) = ∫ τ in (0:ℝ)..1, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro τ hτ
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
    exact deriv_eq_zero_of_gt hz
      (lt_of_lt_of_le (lt_min hu hσ) (min_le_of_convex u σ τ hτ.1 hτ.2))
  rw [hcongr]
  simp

lemma hquot_eq_of_gt (hz : ∀ x, a < x → h x = 0) {u σ : ℝ} (hu : a < u) (hσ : a < σ) :
    hquot h u σ = hquot 0 u σ := by
  rw [hquot_eq_zero_of_gt hz hu hσ]
  unfold hquot
  simp

lemma psi_eq_of_gt (hz : ∀ x, a < x → h x = 0) {σ : ℝ} (hσ : a < σ) {u : ℝ} (hu : a < u)
    (t : ℝ) : psi h (fun t' => line h σ t') u t = psi 0 (fun t' => line 0 σ t') u t := by
  unfold psi
  simp only [line_eq_of_gt hz hσ t, line_eq_of_gt hz hu t]

lemma psi_semicircle_eq_of_gt (hz : ∀ x, a < x → h x = 0) {u : ℝ} (hu : a < u) (t : ℝ) :
    psi h semicircle u t = psi 0 semicircle u t := by
  unfold psi
  simp only [line_eq_of_gt hz hu t]

/-! ## The Abel kernels -/

lemma J1_diag (n : ℕ) (h : ℝ → ℝ) (s t : ℝ) :
    J1 n h s s t = (Nat.doubleFactorial (2 * n + 1) : ℝ) *
      (-(line h s t * lineSlope h s t)) ^ (n + 1) := by
  unfold J1
  split_ifs with h1
  · rfl
  · exact absurd rfl h1

lemma J1_offdiag (n : ℕ) (h : ℝ → ℝ) {s σ : ℝ} (hne : σ ≠ s) (t : ℝ) :
    J1 n h s σ t = iteratedDeriv (n + 1) (fun u : ℝ => psi h (fun t' => line h σ t') u t ^ n *
        Real.sqrt (psi h (fun t' => line h σ t') u t)) s *
      Real.sqrt (psi h (fun t' => line h σ t') s t) := by
  unfold J1
  split_ifs with h1
  · exact absurd h1 hne
  · rfl

lemma J1_eq_of_gt (n : ℕ) (hz : ∀ x, a < x → h x = 0) {u σ : ℝ} (hu : a < u) (hσ : a < σ)
    (t : ℝ) : J1 n h u σ t = J1 n 0 u σ t := by
  by_cases hcase : σ = u
  · rw [hcase]
    rw [J1_diag n h u t, J1_diag n 0 u t, line_eq_of_gt hz hu t, lineSlope_eq_of_gt hz hu t]
  · rw [J1_offdiag n h hcase t, J1_offdiag n 0 hcase t]
    have hev : (fun u' : ℝ => psi h (fun t' => line h σ t') u' t ^ n *
        Real.sqrt (psi h (fun t' => line h σ t') u' t)) =ᶠ[𝓝 u]
        (fun u' : ℝ => psi 0 (fun t' => line 0 σ t') u' t ^ n *
        Real.sqrt (psi 0 (fun t' => line 0 σ t') u' t)) :=
      Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Ioi hu)
        (fun u' hu' => by simp only [psi_eq_of_gt hz hσ hu' t])
    rw [Filter.EventuallyEq.iteratedDeriv_eq (n + 1) hev]
    simp only [psi_eq_of_gt hz hσ hu t]

lemma J2_diag (n : ℕ) (h : ℝ → ℝ) (s t : ℝ) :
    J2 n h s s t = (Nat.doubleFactorial (2 * n - 1) : ℝ) *
      (-(line h s t * lineSlope h s t)) ^ n * lineSlope h s t := by
  unfold J2
  split_ifs with h1
  · rfl
  · exact absurd rfl h1

lemma J2_offdiag (n : ℕ) (h : ℝ → ℝ) {s σ : ℝ} (hne : σ ≠ s) (t : ℝ) :
    J2 n h s σ t = iteratedDeriv n (fun u : ℝ =>
        psi h (fun t' => line h σ t') u t ^ (n - 1) *
        Real.sqrt (psi h (fun t' => line h σ t') u t) * lineSlope h u t) s *
      Real.sqrt (psi h (fun t' => line h σ t') s t) := by
  unfold J2
  split_ifs with h1
  · exact absurd h1 hne
  · rfl

lemma J2_eq_of_gt (n : ℕ) (hz : ∀ x, a < x → h x = 0) {u σ : ℝ} (hu : a < u) (hσ : a < σ)
    (t : ℝ) : J2 n h u σ t = J2 n 0 u σ t := by
  by_cases hcase : σ = u
  · rw [hcase]
    rw [J2_diag n h u t, J2_diag n 0 u t, line_eq_of_gt hz hu t, lineSlope_eq_of_gt hz hu t]
  · rw [J2_offdiag n h hcase t, J2_offdiag n 0 hcase t]
    have hev : (fun u' : ℝ => psi h (fun t' => line h σ t') u' t ^ (n - 1) *
        Real.sqrt (psi h (fun t' => line h σ t') u' t) * lineSlope h u' t) =ᶠ[𝓝 u]
        (fun u' : ℝ => psi 0 (fun t' => line 0 σ t') u' t ^ (n - 1) *
        Real.sqrt (psi 0 (fun t' => line 0 σ t') u' t) * lineSlope 0 u' t) :=
      Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Ioi hu)
        (fun u' hu' => by
          simp only [psi_eq_of_gt hz hσ hu' t, lineSlope_eq_of_gt hz hu' t])
    rw [Filter.EventuallyEq.iteratedDeriv_eq n hev]
    simp only [psi_eq_of_gt hz hσ hu t]

lemma Kden_eq_of_gt (hz : ∀ x, a < x → h x = 0) {u σ : ℝ} (hu : a < u) (hσ : a < σ) (t : ℝ) :
    Kden h u σ t = Kden 0 u σ t := by
  unfold Kden
  rw [hquot_eq_of_gt hz hu hσ, line_eq_of_gt hz hσ t, line_eq_of_gt hz hu t]

lemma K1_eq_of_gt (n : ℕ) (hz : ∀ x, a < x → h x = 0) {u σ : ℝ} (hu : a < u) (hσ : a < σ)
    (t : ℝ) : K1 n h u σ t = K1 n 0 u σ t := by
  unfold K1
  rw [J1_eq_of_gt n hz hu hσ t, Kden_eq_of_gt hz hu hσ t]

lemma K2_eq_of_gt (n : ℕ) (hz : ∀ x, a < x → h x = 0) {u σ : ℝ} (hu : a < u) (hσ : a < σ)
    (t : ℝ) : K2 n h u σ t = K2 n 0 u σ t := by
  unfold K2
  rw [J2_eq_of_gt n hz hu hσ t, Kden_eq_of_gt hz hu hσ t]

lemma Kvec_eq_of_gt (n : ℕ) (hz : ∀ x, a < x → h x = 0) {u σ : ℝ} (hu : a < u) (hσ : a < σ)
    (x y x' y' : ℝ) : Kvec n h u σ x y x' y' = Kvec n 0 u σ x y x' y' := by
  funext i
  fin_cases i <;>
    simp [Kvec, K1_eq_of_gt n hz hu hσ, K2_eq_of_gt n hz hu hσ]

lemma G2_eq_of_gt (n : ℕ) (hz : ∀ x, a < x → h x = 0) {u σ : ℝ} (hu : a < u) (hσ : a < σ)
    (x y x' y' : ℝ) : G2 n h u σ x y x' y' = G2 n 0 u σ x y x' y' := by
  funext i
  simp only [G2]
  apply intervalIntegral.integral_congr
  intro τ hτ
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
  simp only []
  rw [Kvec_eq_of_gt n hz (lt_of_lt_of_le (lt_min hu hσ) (min_le_of_convex u σ τ hτ.1 hτ.2)) hσ]

/-! ## The inhomogeneities `E₁`, `E₂`, `Q`, `Q̃`, `𝚵` -/

lemma E1_eq_of_gt (n : ℕ) (hz : ∀ x, a < x → h x = 0) {s : ℝ} (hs : a < s) :
    E1 n h s = E1 n 0 s := by
  unfold E1
  apply intervalIntegral.integral_congr
  intro t ht
  have hev : (fun u : ℝ => psi h semicircle u t ^ n * Real.sqrt (psi h semicircle u t)) =ᶠ[𝓝 s]
      (fun u : ℝ => psi 0 semicircle u t ^ n * Real.sqrt (psi 0 semicircle u t)) :=
    Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Ioi hs)
      (fun u hu => by simp only [psi_semicircle_eq_of_gt hz hu t])
  exact Filter.EventuallyEq.iteratedDeriv_eq (n + 1) hev

lemma E2_eq_of_gt (n : ℕ) (hz : ∀ x, a < x → h x = 0) {s : ℝ} (hs : a < s) :
    E2 n h s = E2 n 0 s := by
  unfold E2
  apply intervalIntegral.integral_congr
  intro t ht
  have hev : (fun u : ℝ => psi h semicircle u t ^ (n - 1) * Real.sqrt (psi h semicircle u t) *
        lineSlope h u t) =ᶠ[𝓝 s]
      (fun u : ℝ => psi 0 semicircle u t ^ (n - 1) * Real.sqrt (psi 0 semicircle u t) *
        lineSlope 0 u t) :=
    Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Ioi hs)
      (fun u hu => by
        simp only [psi_semicircle_eq_of_gt hz hu t, lineSlope_eq_of_gt hz hu t])
  exact Filter.EventuallyEq.iteratedDeriv_eq n hev

lemma Q_eq_of_gt (n : ℕ) (hz : ∀ x, a < x → h x = 0) {s : ℝ} (hs : a < s) :
    Q n h s = Q n 0 s := by
  funext i
  fin_cases i <;> simp [Q, E1_eq_of_gt n hz hs, E2_eq_of_gt n hz hs]

/-- For `u > 1` the Abel integrand is identically zero, because `√(v - u) = 0`
on the (reversed) integration interval. -/
lemma integral_div_sqrt_eq_zero_of_one_lt (f : ℝ → ℝ) {u : ℝ} (hu : 1 < u) :
    (∫ v in u..(1:ℝ), f v / Real.sqrt (v - u)) = 0 := by
  have hcongr : (∫ v in u..(1:ℝ), f v / Real.sqrt (v - u))
      = ∫ v in u..(1:ℝ), (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro v hv
    simp only [Set.uIcc_of_ge (le_of_lt hu)] at hv
    simp only []
    rw [Real.sqrt_eq_zero_of_nonpos (by linarith [hv.2])]
    simp
  rw [hcongr]
  simp

lemma deriv_abel_eq_of_gt (n : ℕ) (hz : ∀ x, a < x → h x = 0) {s : ℝ} (hs : a < s) (i : Fin 2) :
    deriv (fun u : ℝ => ∫ v in u..(1:ℝ), (Q n h v) i / Real.sqrt (v - u)) s =
    deriv (fun u : ℝ => ∫ v in u..(1:ℝ), (Q n 0 v) i / Real.sqrt (v - u)) s := by
  apply Filter.EventuallyEq.deriv_eq
  refine Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Ioi hs) ?_
  intro u hu
  show (∫ v in u..(1:ℝ), (Q n h v) i / Real.sqrt (v - u)) =
    ∫ v in u..(1:ℝ), (Q n 0 v) i / Real.sqrt (v - u)
  by_cases h1 : u ≤ 1
  · apply intervalIntegral.integral_congr
    intro v hv
    simp only [Set.uIcc_of_le h1] at hv
    simp only []
    rw [Q_eq_of_gt n hz (lt_of_lt_of_le hu hv.1)]
  · push Not at h1
    rw [integral_div_sqrt_eq_zero_of_one_lt _ h1, integral_div_sqrt_eq_zero_of_one_lt _ h1]

lemma Qtilde_apply (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (i : Fin 2) :
    (Qtilde n h s) i = deriv (fun u : ℝ => ∫ v in u..(1:ℝ), (Q n h v) i / Real.sqrt (v - u)) s := by
  fin_cases i <;> simp [Qtilde]

lemma Qtilde_eq_of_gt (n : ℕ) (hz : ∀ x, a < x → h x = 0) {s : ℝ} (hs : a < s) :
    Qtilde n h s = Qtilde n 0 s := by
  funext i
  rw [Qtilde_apply n h s i, Qtilde_apply n 0 s i]
  exact deriv_abel_eq_of_gt n hz hs i

lemma Xi_eq_of_gt (n : ℕ) (hz : ∀ x, a < x → h x = 0) {s : ℝ} (hs : a < s) :
    Xi n h s = Xi n 0 s := by
  funext i
  fin_cases i <;> simp [Xi, Qtilde_eq_of_gt n hz hs]

/-! ## `𝐆` and `𝚯` -/

lemma Godd_eq_of_gt (n : ℕ) (hz : ∀ x, a < x → h x = 0) {s : ℝ} (hs : a < s) (Z : St) :
    Godd n h s Z = Godd n 0 s Z := by
  have hcomp : G2 n h s s (Z 0) (Z 1) (Z 2) (Z 3) = G2 n 0 s s (Z 0) (Z 1) (Z 2) (Z 3) :=
    G2_eq_of_gt n hz hs hs (Z 0) (Z 1) (Z 2) (Z 3)
  funext j
  fin_cases j <;> simp [Godd, hcomp]

lemma Theta_eq_of_gt (n : ℕ) (hz : ∀ x, a < x → h x = 0) {s σ : ℝ} (hs : a < s) (hσ : a < σ)
    (Z : St) : Theta n h s σ Z = Theta n 0 s σ Z := by
  have hcomp : ∀ i : Fin 2,
      deriv (fun u : ℝ => (G2 n h u σ (Z 0) (Z 1) (Z 2) (Z 3)) i) s =
      deriv (fun u : ℝ => (G2 n 0 u σ (Z 0) (Z 1) (Z 2) (Z 3)) i) s := by
    intro i
    apply Filter.EventuallyEq.deriv_eq
    refine Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Ioi hs) ?_
    intro u hu
    show (G2 n h u σ (Z 0) (Z 1) (Z 2) (Z 3)) i = (G2 n 0 u σ (Z 0) (Z 1) (Z 2) (Z 3)) i
    rw [G2_eq_of_gt n hz hu hσ]
  funext j
  fin_cases j <;> simp [Theta, hcomp]

/-! ## The target -/

theorem data_eq_zero_of_eventuallyEq_zero (n : ℕ) {h : ℝ → ℝ} {s σ : ℝ} (hsσ : s ≤ σ)
    (hloc : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, s - δ < x → x < σ + δ → h x = 0)
    (hright : ∀ x : ℝ, s ≤ x → h x = 0) (z : Work.OddVolterra.St) :
    Work.OddVolterra.Godd n h s z = Work.OddVolterra.Godd n 0 s z ∧
    Work.OddVolterra.Xi n h s = Work.OddVolterra.Xi n 0 s ∧
    Work.OddVolterra.Theta n h s σ z = Work.OddVolterra.Theta n 0 s σ z := by
  obtain ⟨δ, hδpos, hδ⟩ := hloc
  have hz : ∀ x : ℝ, s - δ < x → h x = 0 := by
    intro x hx
    by_cases hxσ : x < σ + δ
    · exact hδ x hx hxσ
    · have h1 : σ + δ ≤ x := not_lt.mp hxσ
      exact hright x (by linarith)
  have hs : s - δ < s := by linarith
  have hσ : s - δ < σ := by linarith
  exact ⟨Godd_eq_of_gt n hz hs z, Xi_eq_of_gt n hz hs, Theta_eq_of_gt n hz hs hσ z⟩

end Work.OddVolterra.Existence
