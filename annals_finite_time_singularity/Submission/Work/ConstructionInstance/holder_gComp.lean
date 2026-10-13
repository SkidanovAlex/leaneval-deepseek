import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.ConstructionInstance.Basic
import Submission.Work.ConstructionInstance.GCompDefs
import Submission.Work.ConstructionInstance.A0_rho_pow_diff
import Submission.Work.ConstructionInstance.AuxOmegaStar
import Submission.Work.ConstructionInstance.rpow_sub_le_mul
import Submission.Work.ConstructionInstance.g_psi_eq
import Submission.Work.ConstructionInstance.psi_sub_le
import Submission.Work.ConstructionInstance.g_taylor_bounds
import Submission.Work.ConstructionInstance.g_slice_lipschitz
import Submission.Work.Stability.holderWith_of_dist_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Metric
open scoped Topology

namespace Work.ConstructionInstance

/-! ## Elementary metric and trigonometric facts -/

/-- `ρ = ‖·‖` is `1`-Lipschitz on `ℝ³`. -/
lemma abs_rho_sub_rho_le_dist (x y : R3) :
    |Work.Cyl.rho x - Work.Cyl.rho y| ≤ dist x y := by
  rw [Work.Cyl.rho_eq_norm x, Work.Cyl.rho_eq_norm y, dist_eq_norm]
  exact abs_norm_sub_norm_le x y

/-- `max ρ ≤ min ρ + dist`. -/
lemma max_rho_le_min_rho_add_dist (x y : R3) :
    max (Work.Cyl.rho x) (Work.Cyl.rho y)
      ≤ min (Work.Cyl.rho x) (Work.Cyl.rho y) + dist x y := by
  have h := abs_rho_sub_rho_le_dist x y
  rcases le_total (Work.Cyl.rho x) (Work.Cyl.rho y) with hle | hle
  · have h' : -(Work.Cyl.rho x - Work.Cyl.rho y) ≤ dist x y := by
      rw [abs_of_nonpos (by linarith : Work.Cyl.rho x - Work.Cyl.rho y ≤ 0)] at h
      exact h
    rw [min_eq_left hle, max_eq_right hle]
    linarith
  · have h' : Work.Cyl.rho x - Work.Cyl.rho y ≤ dist x y := by
      rw [abs_of_nonneg (by linarith : 0 ≤ Work.Cyl.rho x - Work.Cyl.rho y)] at h
      exact h
    rw [min_eq_right hle, max_eq_left hle]
    linarith

/-- `|θ x| ∈ [0, π/2]`. -/
lemma abs_theta_mem_Iθ (x : R3) : |Work.Cyl.theta x| ∈ Work.Spaces.Iθ := by
  refine ⟨abs_nonneg _, ?_⟩
  rw [abs_le]
  exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _), le_of_lt (Real.arctan_lt_pi_div_two _)⟩

/-! ## `rpow` arithmetic -/

/-- For `1 ≤ a ≤ b` and `0 < s ≤ 1`: `b^s - a^s ≤ s (b - a)`. -/
lemma rpow_sub_le_mul_of_one_le {s a b : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (ha : 1 ≤ a) (hab : a ≤ b) : b ^ s - a ^ s ≤ s * (b - a) := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have h := rpow_sub_le_mul hs hs1 ha0 hab
  have h1 : a ^ (s - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha (by linarith)
  calc b ^ s - a ^ s ≤ s * a ^ (s - 1) * (b - a) := h
    _ ≤ s * 1 * (b - a) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left h1 hs.le
    _ = s * (b - a) := by ring

/-- Two-sided form: for `a, b ≥ 1` and `0 < s ≤ 1`, `|a^s - b^s| ≤ s |a - b|`. -/
lemma abs_rpow_sub_le_mul_of_one_le {s a b : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (ha : 1 ≤ a) (hb : 1 ≤ b) : |a ^ s - b ^ s| ≤ s * |a - b| := by
  rcases le_total a b with h | h
  · have hle : a ^ s ≤ b ^ s := Real.rpow_le_rpow (by linarith) h hs.le
    have h' := rpow_sub_le_mul_of_one_le hs hs1 ha h
    rw [abs_of_nonpos (by linarith : a ^ s - b ^ s ≤ 0),
      abs_of_nonpos (by linarith : a - b ≤ 0)]
    linarith
  · have hle : b ^ s ≤ a ^ s := Real.rpow_le_rpow (by linarith) h hs.le
    have h' := rpow_sub_le_mul_of_one_le hs hs1 hb h
    rw [abs_of_nonneg (by linarith : 0 ≤ a ^ s - b ^ s),
      abs_of_nonneg (by linarith : 0 ≤ a - b)]
    linarith

/-- The near-origin radial bound: for `2d ≤ ρ` and `d ≤ 1`, `ρ^{3α}/ρ · d ≤ 2^{3α-1} d^α`. -/
lemma rho_pow_div_mul_le {α ρ d : ℝ} (hα : 0 < α) (h31 : 3 * α ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1)
    (hρd : 2 * d ≤ ρ) : ρ ^ (3 * α) / ρ * d ≤ 2 ^ (3 * α - 1) * d ^ α := by
  have hρ : 0 < ρ := lt_of_lt_of_le (by linarith) hρd
  have h1 : 3 * α - 1 ≤ 0 := by linarith
  calc ρ ^ (3 * α) / ρ * d = ρ ^ (3 * α - 1) * d := by
        rw [Real.rpow_sub_one hρ.ne']
    _ ≤ (2 * d) ^ (3 * α - 1) * d := by
        apply mul_le_mul_of_nonneg_right _ hd.le
        exact Real.rpow_le_rpow_of_nonpos (by linarith) hρd h1
    _ = 2 ^ (3 * α - 1) * (d ^ (3 * α - 1) * d) := by
        rw [Real.mul_rpow (by norm_num) hd.le]
        ring
    _ = 2 ^ (3 * α - 1) * d ^ (3 * α) := by
        rw [← Real.rpow_add_one hd.ne']
        congr 1
        ring
    _ ≤ 2 ^ (3 * α - 1) * d ^ α := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
        exact Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)

/-! ## Two elementary inequalities between the three quantities `ρ x`, `ρ y`, `dist x y` -/

lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have := abs_add_le a (-b)
  simpa [sub_eq_add_neg] using this

/-! ## The main theorem -/

/-- The perturbation composite `ĝ : x ↦ g (ρ x ^ (3α)) (|θ x|)` is `α`-Hölder on `ℝ³`.

Scalar core of `holder_omegaS_of_data`: on the closed half space `x₃ ≥ 0` the self-similar
vorticity is `ω x = (3α / c(3α)) • omegaStar α x + ĝ x • e_θ x` (the first term by
`Gamma_mul_Fstar_eq_Aom`), so this Hölder bound (together with the vanishing bound
`gComp_abs_le`) is what `holder_smul_eTheta` consumes for the perturbation.

Intended proof (all constants may depend on `α`, `Cv`, `Lg`, `Lθ` and a free `δ > 0`):

* WLOG `x₃, y₃ ≥ 0` (both `ρ x ^ (3α)` and `|θ x|` are even in `x₃`), and WLOG `‖x-y‖ < 1`
  (`|g| ≤ Cv` from `hvan` and `Γ ≤ 1` gives the trivial bound otherwise).
* `hsm` (`C²` on an open set containing `[0,δ]×[0,π/2]`), `hquad0`, `hquad1` and `hvt` give
  uniform Taylor bounds for `0 ≤ z ≤ δ`, `θ ∈ [0,π/2]`:
  `|g z θ| ≤ K z²`, `|∂_θ g (z,θ)| ≤ K z²`, `|∂_z g (z,θ)| ≤ K z`
  (`g(0,θ) = 0` makes `∂_θ g (0,θ) = 0`, and `∂_z g (0,θ) = 0` makes `∂_z ∂_θ g (0,θ) = 0`).
* `z = ρ^{3α}` is `(3α)`-Hölder and, on `ρ ≥ δ`, `3αδ^{3α-1}`-Lipschitz (`3α ≤ 1`); `θ` has
  `|∇θ| = 1/ρ` off the axis, while `g z 0 = g z (π/2) = 0` kills the axis/plane singularities
  (`|π/2 - |θ|| = arcsin (r/ρ) ≤ 2r/ρ`, `||θ|| = arccos (r/ρ)`); `r = Cyl.radial`, `ρ = Cyl.rho`.
* split on `d = ‖x-y‖ ≤ ρ_min/2` (`ρ_min = min (ρ x) (ρ y)`) vs `d > ρ_min/2`:
  for `d > ρ_min/2` one has `ρ_max < 3d` so the sup bound `|ĝ| ≤ Cv` (far from the origin) resp.
  `|ĝ| ≤ K ρ^{6α}` (near the origin) closes it; for `d ≤ ρ_min/2` bound
  `|ĝ x - ĝ y| ≤ Lg |z x - z y|^α + Lθ |θ x - θ y|^α` (using `hzk`, `hzth` at the intermediate
  points), with the local gradients (`ρ ≥ ρ_min/2` on the segment) giving
  `|Δz| ≤ 3α ρ_min^{3α-1} d ≤ C d` resp. `|Δθ| ≤ C d/ρ_min ≤ C d` — and for `ρ_min ≤ δ`
  replacing the radial part by the Taylor bound `K ρ_min^{6α-1} d`. -/
theorem holder_gComp {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1/3) {g : ℝ → ℝ → ℝ}
    {Cv Lg Lθ : ℝ} (hCv : 0 ≤ Cv) (hLg : 0 ≤ Lg) (hLθ : 0 ≤ Lθ)
    (hvt : Work.Spaces.VanishTheta g)
    (hquad0 : ∀ θ : ℝ, g 0 θ = 0)
    (hquad1 : ∀ θ : ℝ, Work.Spaces.pz g 0 θ = 0)
    (hvan : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ Cv * Work.ConstructionInstance.Gamma α θ)
    (hzk : ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |g z θ - g z' θ| ≤ Lg * |z - z'| ^ α)
    (hzth : ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ - g z θ'| ≤ Lθ * |θ - θ'| ^ α)
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1))) :
    Holder ⟨α, hα.le⟩ (fun x : R3 => g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)) := by
  have h3α : 0 < 3 * α := by linarith
  have h3α1 : 3 * α ≤ 1 := by linarith
  -- the Taylor bounds at the origin, and the resulting slice-Lipschitz bounds
  obtain ⟨K, hK0, hK⟩ := g_taylor_bounds hsm hquad0 hquad1
  have hzK : ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz g z θ| ≤ K * z :=
    fun z θ hz h2 hθ => (hK z θ hz h2 hθ).2.1
  have hthK : ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pth g z θ| ≤ K * z :=
    fun z θ hz h2 hθ => (hK z θ hz h2 hθ).2.2
  obtain ⟨hslicez, hsliceθ⟩ := g_slice_lipschitz hsm hzK hthK
  -- the two global bounds of the composite
  have hsup : ∀ z : R3, |g (Work.Cyl.rho z ^ (3 * α)) (psi z)| ≤ Cv := by
    intro z
    have hθ := psi_mem_Iθ z
    have h1 := hvan (Work.Cyl.rho z ^ (3 * α)) (psi z)
      (Real.rpow_nonneg (Work.Cyl.rho_nonneg z) _) hθ
    have h2 : Gamma α (psi z) ≤ 1 := Gamma_le_one hα.le hθ
    have h3 : 0 ≤ Gamma α (psi z) := Gamma_nonneg hθ
    nlinarith [hCv]
  have hquadbound : ∀ z : R3, Work.Cyl.rho z ≤ 2 →
      |g (Work.Cyl.rho z ^ (3 * α)) (psi z)| ≤ K * (Work.Cyl.rho z) ^ (6 * α) := by
    intro z hz
    have hρ0 := Work.Cyl.rho_nonneg z
    have hZ0 : 0 ≤ Work.Cyl.rho z ^ (3 * α) := Real.rpow_nonneg hρ0 _
    have hZ2 : Work.Cyl.rho z ^ (3 * α) ≤ 2 := by
      calc Work.Cyl.rho z ^ (3 * α) ≤ 2 ^ (3 * α) := Real.rpow_le_rpow hρ0 hz h3α.le
        _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
        _ = 2 := Real.rpow_one 2
    have h1 := (hK _ _ hZ0 hZ2 (psi_mem_Iθ z)).1
    have h2 : (Work.Cyl.rho z ^ (3 * α)) ^ 2 = (Work.Cyl.rho z) ^ (6 * α) := by
      rw [← Real.rpow_natCast (Work.Cyl.rho z ^ (3 * α)) 2, ← Real.rpow_mul hρ0]
      congr 1
      ring
    calc |g (Work.Cyl.rho z ^ (3 * α)) (psi z)|
        ≤ K * (Work.Cyl.rho z ^ (3 * α)) ^ 2 := h1
      _ = K * (Work.Cyl.rho z) ^ (6 * α) := by rw [h2]
  -- the Hölder constant
  set C : ℝ := 2 * Cv + (2 * Cv * (3/2) ^ α
      + (2 * K * 3 ^ (6 * α) + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1))))) with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hC1 : 2 * Cv ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv * (3/2) ^ α
      + (2 * K * 3 ^ (6 * α) + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)))) by positivity]
  have hC2 : 2 * Cv * (3/2) ^ α ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv
      + (2 * K * 3 ^ (6 * α) + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)))) by positivity]
  have hC3 : 2 * K * 3 ^ (6 * α) ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv
      + (2 * Cv * (3/2) ^ α + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)))) by positivity]
  have hC4 : Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv + (2 * Cv * (3/2) ^ α + (2 * K * 3 ^ (6 * α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)))) by positivity]
  have hC5 : K * (3/2) * 3 ^ α * (3/2) ^ (2 * α) ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv + (2 * Cv * (3/2) ^ α + (2 * K * 3 ^ (6 * α)
      + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)))) by positivity]
  have hC6 : K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1) ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv + (2 * Cv * (3/2) ^ α + (2 * K * 3 ^ (6 * α)
      + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)))) by positivity]
  have hC56 : K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)
      + K * (3/2) * 3 ^ α * (3/2) ^ (2 * α) ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv + (2 * Cv * (3/2) ^ α + (2 * K * 3 ^ (6 * α)
      + (Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α))) by positivity]
  refine ⟨⟨C, hCnn⟩, ?_⟩
  refine Work.Stability.holderWith_of_dist_le (fun x y => ?_)
  rw [Real.dist_eq, g_psi_eq hquad0 hvt x, g_psi_eq hquad0 hvt y]
  show |g (Work.Cyl.rho x ^ (3 * α)) (psi x) - g (Work.Cyl.rho y ^ (3 * α)) (psi y)|
      ≤ C * dist x y ^ α
  by_cases hxy : x = y
  · subst hxy
    simp only [dist_self, sub_self, abs_zero]
    positivity
  have hdpos : 0 < dist x y := dist_pos.mpr hxy
  have hdnn : 0 ≤ dist x y := dist_nonneg
  have htri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := abs_sub_le_abs_add
  rcases le_or_gt 1 (dist x y) with hd1 | hd1
  · -- far away (or exactly at distance one): the sup bound suffices
    have h1 : (1 : ℝ) ≤ dist x y ^ α := Real.one_le_rpow hd1 hα.le
    calc |g (Work.Cyl.rho x ^ (3 * α)) (psi x) - g (Work.Cyl.rho y ^ (3 * α)) (psi y)|
        ≤ |g (Work.Cyl.rho x ^ (3 * α)) (psi x)|
          + |g (Work.Cyl.rho y ^ (3 * α)) (psi y)| := htri _ _
      _ ≤ 2 * Cv := by linarith [hsup x, hsup y]
      _ ≤ C * dist x y ^ α := by
          calc 2 * Cv ≤ C := hC1
            _ = C * 1 := by ring
            _ ≤ C * dist x y ^ α := by
                simpa using mul_le_mul_of_nonneg_left h1 hCnn
  · rcases le_or_gt (min (Work.Cyl.rho x) (Work.Cyl.rho y)) (2 * dist x y) with hfar | hnear
    · -- the radii are not large compared with `d`: use the two pointwise bounds
      have hmax3 : max (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ 3 * dist x y := by
        have := max_rho_le_min_rho_add_dist x y
        linarith
      by_cases hsmall : max (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ 2
      · -- both radii at most two: the quadratic vanishing of `g` at `z = 0`
        have hρx2 : Work.Cyl.rho x ≤ 2 := le_trans (le_max_left _ _) hsmall
        have hρy2 : Work.Cyl.rho y ≤ 2 := le_trans (le_max_right _ _) hsmall
        have hρx3 : Work.Cyl.rho x ≤ 3 * dist x y := le_trans (le_max_left _ _) hmax3
        have hρy3 : Work.Cyl.rho y ≤ 3 * dist x y := le_trans (le_max_right _ _) hmax3
        have hpow : dist x y ^ (6 * α) ≤ dist x y ^ α :=
          Real.rpow_le_rpow_of_exponent_ge hdpos (le_of_lt hd1) (by linarith)
        calc |g (Work.Cyl.rho x ^ (3 * α)) (psi x) - g (Work.Cyl.rho y ^ (3 * α)) (psi y)|
            ≤ |g (Work.Cyl.rho x ^ (3 * α)) (psi x)|
              + |g (Work.Cyl.rho y ^ (3 * α)) (psi y)| := htri _ _
          _ ≤ K * (Work.Cyl.rho x) ^ (6 * α) + K * (Work.Cyl.rho y) ^ (6 * α) :=
              add_le_add (hquadbound x hρx2) (hquadbound y hρy2)
          _ ≤ K * (3 * dist x y) ^ (6 * α) + K * (3 * dist x y) ^ (6 * α) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) hρx3 (by linarith)) hK0
              · exact mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow (Work.Cyl.rho_nonneg y) hρy3 (by linarith)) hK0
          _ = 2 * K * 3 ^ (6 * α) * dist x y ^ (6 * α) := by
              rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hdnn]; ring
          _ ≤ 2 * K * 3 ^ (6 * α) * dist x y ^ α :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ ≤ C * dist x y ^ α := by
              exact mul_le_mul_of_nonneg_right hC3 (Real.rpow_nonneg hdnn α)
      · -- both radii large: then `d > 2/3` and the sup bound suffices
        have hd23 : 2 / 3 ≤ dist x y := by
          have := max_rho_le_min_rho_add_dist x y
          linarith [not_le.mp hsmall, hfar]
        have h1 : (1 : ℝ) ≤ (3 / 2) ^ α * dist x y ^ α := by
          have h2 : (3 / 2 : ℝ) ^ α * (2 / 3) ^ α = 1 := by
            rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3 / 2) (by norm_num : (0:ℝ) ≤ 2 / 3),
              show (3:ℝ)/2 * (2/3) = 1 by ring, Real.one_rpow]
          have h3 : (2 / 3 : ℝ) ^ α ≤ dist x y ^ α :=
            Real.rpow_le_rpow (by norm_num) hd23 hα.le
          have h4 : 0 ≤ (3 / 2 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) _
          calc (1 : ℝ) = (3 / 2 : ℝ) ^ α * (2 / 3) ^ α := h2.symm
            _ ≤ (3 / 2 : ℝ) ^ α * dist x y ^ α := mul_le_mul_of_nonneg_left h3 h4
        calc |g (Work.Cyl.rho x ^ (3 * α)) (psi x) - g (Work.Cyl.rho y ^ (3 * α)) (psi y)|
            ≤ |g (Work.Cyl.rho x ^ (3 * α)) (psi x)|
              + |g (Work.Cyl.rho y ^ (3 * α)) (psi y)| := htri _ _
          _ ≤ 2 * Cv := by linarith [hsup x, hsup y]
          _ = 2 * Cv * 1 := by ring
          _ ≤ 2 * Cv * ((3 / 2) ^ α * dist x y ^ α) :=
              mul_le_mul_of_nonneg_left h1 (by linarith)
          _ = 2 * Cv * (3 / 2) ^ α * dist x y ^ α := by ring
          _ ≤ C * dist x y ^ α := by
              exact mul_le_mul_of_nonneg_right hC2 (Real.rpow_nonneg hdnn α)
    · -- close together and away from the origin
      have hρmin2d : 2 * dist x y < min (Work.Cyl.rho x) (Work.Cyl.rho y) := hnear
      have hρminpos : 0 < min (Work.Cyl.rho x) (Work.Cyl.rho y) :=
        lt_of_lt_of_le (by linarith [dist_nonneg (x := x) (y := y)]) (le_of_lt hρmin2d)
      have hminx : min (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ Work.Cyl.rho x := min_le_left _ _
      have hminy : min (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ Work.Cyl.rho y := min_le_right _ _
      have hρxmax : Work.Cyl.rho x ≤ max (Work.Cyl.rho x) (Work.Cyl.rho y) := le_max_left _ _
      have hρymax : Work.Cyl.rho y ≤ max (Work.Cyl.rho x) (Work.Cyl.rho y) := le_max_right _ _
      have hmax32 : max (Work.Cyl.rho x) (Work.Cyl.rho y)
          ≤ 3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2 := by
        have := max_rho_le_min_rho_add_dist x y
        linarith
      have hpsi : |psi x - psi y|
          ≤ 4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y) :=
        psi_sub_le x y hρminpos hminx hminy
      have hpsi_nn : 0 ≤ |psi x - psi y| := abs_nonneg _
      have hZx0 : 0 ≤ Work.Cyl.rho x ^ (3 * α) := Real.rpow_nonneg (Work.Cyl.rho_nonneg x) _
      have hZy0 : 0 ≤ Work.Cyl.rho y ^ (3 * α) := Real.rpow_nonneg (Work.Cyl.rho_nonneg y) _
      have hsplit : |g (Work.Cyl.rho x ^ (3 * α)) (psi x)
            - g (Work.Cyl.rho y ^ (3 * α)) (psi y)|
          ≤ |g (Work.Cyl.rho x ^ (3 * α)) (psi x) - g (Work.Cyl.rho x ^ (3 * α)) (psi y)|
            + |g (Work.Cyl.rho x ^ (3 * α)) (psi y)
                - g (Work.Cyl.rho y ^ (3 * α)) (psi y)| := by
        have := abs_add_le
          (g (Work.Cyl.rho x ^ (3 * α)) (psi x) - g (Work.Cyl.rho x ^ (3 * α)) (psi y))
          (g (Work.Cyl.rho x ^ (3 * α)) (psi y) - g (Work.Cyl.rho y ^ (3 * α)) (psi y))
        rwa [show g (Work.Cyl.rho x ^ (3 * α)) (psi x)
              - g (Work.Cyl.rho x ^ (3 * α)) (psi y)
            + (g (Work.Cyl.rho x ^ (3 * α)) (psi y) - g (Work.Cyl.rho y ^ (3 * α)) (psi y))
            = g (Work.Cyl.rho x ^ (3 * α)) (psi x)
              - g (Work.Cyl.rho y ^ (3 * α)) (psi y) from by ring] at this
      by_cases hB1 : 1 ≤ min (Work.Cyl.rho x) (Work.Cyl.rho y)
      · -- both points at radius at least one: `hzk`/`hzth` and the Lipschitz bound for `psi`
        have hρx1 : 1 ≤ Work.Cyl.rho x := le_trans hB1 hminx
        have hρy1 : 1 ≤ Work.Cyl.rho y := le_trans hB1 hminy
        have hZd : |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)| ≤ 3 * α * dist x y := by
          calc |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|
              ≤ 3 * α * |Work.Cyl.rho x - Work.Cyl.rho y| :=
                abs_rpow_sub_le_mul_of_one_le h3α h3α1 hρx1 hρy1
            _ ≤ 3 * α * dist x y :=
                mul_le_mul_of_nonneg_left (abs_rho_sub_rho_le_dist x y) h3α.le
        have hdψ : |psi x - psi y| ≤ 4 * Real.pi * dist x y := by
          rw [le_div_iff₀ hρminpos] at hpsi
          have h1 : |psi x - psi y|
              ≤ |psi x - psi y| * min (Work.Cyl.rho x) (Work.Cyl.rho y) :=
            le_mul_of_one_le_right (abs_nonneg _) hB1
          linarith
        calc |g (Work.Cyl.rho x ^ (3 * α)) (psi x) - g (Work.Cyl.rho y ^ (3 * α)) (psi y)|
            ≤ |g (Work.Cyl.rho x ^ (3 * α)) (psi x) - g (Work.Cyl.rho x ^ (3 * α)) (psi y)|
              + |g (Work.Cyl.rho x ^ (3 * α)) (psi y)
                  - g (Work.Cyl.rho y ^ (3 * α)) (psi y)| := hsplit
          _ ≤ Lθ * |psi x - psi y| ^ α + Lg * |Work.Cyl.rho x ^ (3 * α)
                - Work.Cyl.rho y ^ (3 * α)| ^ α :=
              add_le_add (hzth _ _ _ hZx0 (psi_mem_Iθ x) (psi_mem_Iθ y))
                (hzk _ _ _ hZx0 hZy0 (psi_mem_Iθ y))
          _ ≤ Lθ * (4 * Real.pi * dist x y) ^ α + Lg * (3 * α * dist x y) ^ α := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow hpsi_nn hdψ hα.le) hLθ
              · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hZd hα.le) hLg
          _ = (Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α) * dist x y ^ α := by
              rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 4 * Real.pi) hdnn,
                Real.mul_rpow (by linarith : (0:ℝ) ≤ 3 * α) hdnn]
              ring
          _ ≤ C * dist x y ^ α := by
              exact mul_le_mul_of_nonneg_right hC4 (Real.rpow_nonneg hdnn α)
      · -- both points at radius below one: the slice bounds of the Taylor expansion
        have hρmin1 : min (Work.Cyl.rho x) (Work.Cyl.rho y) < 1 := lt_of_not_ge hB1
        have hmax2 : max (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ 2 := by linarith
        have hρx32 : Work.Cyl.rho x ≤ 3 / 2 := by
          have := le_trans hρxmax hmax32
          linarith
        have hρy32 : Work.Cyl.rho y ≤ 3 / 2 := by
          have := le_trans hρymax hmax32
          linarith
        have hZx2 : Work.Cyl.rho x ^ (3 * α) ≤ 2 := by
          calc Work.Cyl.rho x ^ (3 * α) ≤ (2 : ℝ) ^ (3 * α) :=
                Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) (le_trans hρxmax hmax2) h3α.le
            _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
            _ = 2 := Real.rpow_one 2
        have hZy2 : Work.Cyl.rho y ^ (3 * α) ≤ 2 := by
          calc Work.Cyl.rho y ^ (3 * α) ≤ (2 : ℝ) ^ (3 * α) :=
                Real.rpow_le_rpow (Work.Cyl.rho_nonneg y) (le_trans hρymax hmax2) h3α.le
            _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
            _ = 2 := Real.rpow_one 2
        have hZx32 : Work.Cyl.rho x ^ (3 * α) ≤ 3 / 2 := by
          calc Work.Cyl.rho x ^ (3 * α) ≤ (3 / 2 : ℝ) ^ (3 * α) :=
                Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) hρx32 h3α.le
            _ ≤ (3 / 2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
            _ = 3 / 2 := Real.rpow_one (3 / 2)
        have hZy32 : Work.Cyl.rho y ^ (3 * α) ≤ 3 / 2 := by
          calc Work.Cyl.rho y ^ (3 * α) ≤ (3 / 2 : ℝ) ^ (3 * α) :=
                Real.rpow_le_rpow (Work.Cyl.rho_nonneg y) hρy32 h3α.le
            _ ≤ (3 / 2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
            _ = 3 / 2 := Real.rpow_one (3 / 2)
        have hmaxZ : max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α)) ≤ 3 / 2 :=
          max_le hZx32 hZy32
        have hZxle : Work.Cyl.rho x ^ (3 * α)
            ≤ (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α) :=
          Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) (le_trans hρxmax hmax32) h3α.le
        have hZd : |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|
            ≤ 3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α :=
          A0_rho_pow_diff (β := α) hα (le_trans hα13 (by norm_num)) (Work.Cyl.rho_nonneg x)
            (Work.Cyl.rho_nonneg y) hρx32 hρy32 (abs_rho_sub_rho_le_dist x y)
        have hzslice := hslicez (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α)) (psi y)
          hZx0 hZx2 hZy0 hZy2 (psi_mem_Iθ y)
        have hθslice := hsliceθ (Work.Cyl.rho x ^ (3 * α)) (psi x) (psi y)
          hZx0 hZx2 (psi_mem_Iθ x) (psi_mem_Iθ y)
        -- the two gradient steps
        have hstep1 : K * (Work.Cyl.rho x ^ (3 * α)) * |psi x - psi y|
            ≤ K * ((3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
              * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y))) := by
          have h1 : K * (Work.Cyl.rho x ^ (3 * α))
              ≤ K * (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α) :=
            mul_le_mul_of_nonneg_left hZxle hK0
          calc K * (Work.Cyl.rho x ^ (3 * α)) * |psi x - psi y|
              ≤ K * (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
                * |psi x - psi y| := mul_le_mul_of_nonneg_right h1 hpsi_nn
            _ = K * ((3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
                * |psi x - psi y|) := by ring
            _ ≤ K * ((3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
                * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y))) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ K)
                exact mul_le_mul_of_nonneg_left hpsi (by positivity)
        have hstep2 : K * max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α))
              * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|
            ≤ K * ((3 / 2) * (3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α)) := by
          have h1 : K * max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α))
              ≤ K * (3 / 2) := mul_le_mul_of_nonneg_left hmaxZ hK0
          calc K * max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α))
                * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|
              ≤ K * (3 / 2) * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)| :=
                mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
            _ = K * ((3 / 2) * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|) := by ring
            _ ≤ K * ((3 / 2) * (3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ K)
                exact mul_le_mul_of_nonneg_left hZd (by positivity)
        have hstep1' : (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
              * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y))
            ≤ (3 / 2) ^ (3 * α) * 4 * Real.pi * (2 ^ (3 * α - 1) * dist x y ^ α) := by
          have h1 : (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
              = (3 / 2) ^ (3 * α) * min (Work.Cyl.rho x) (Work.Cyl.rho y) ^ (3 * α) := by
            rw [show 3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2
                = 3 / 2 * min (Work.Cyl.rho x) (Work.Cyl.rho y) by ring,
              Real.mul_rpow (by norm_num) hρminpos.le]
          rw [h1]
          have h2 := rho_pow_div_mul_le hα h3α1 hdpos (le_of_lt hd1) (le_of_lt hρmin2d)
          have h3 : (3 / 2) ^ (3 * α) * min (Work.Cyl.rho x) (Work.Cyl.rho y) ^ (3 * α)
                * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y))
              = (3 / 2) ^ (3 * α) * 4 * Real.pi
                * (min (Work.Cyl.rho x) (Work.Cyl.rho y) ^ (3 * α)
                  / min (Work.Cyl.rho x) (Work.Cyl.rho y) * dist x y) := by ring
          rw [h3]
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
        calc |g (Work.Cyl.rho x ^ (3 * α)) (psi x) - g (Work.Cyl.rho y ^ (3 * α)) (psi y)|
            ≤ |g (Work.Cyl.rho x ^ (3 * α)) (psi x) - g (Work.Cyl.rho x ^ (3 * α)) (psi y)|
              + |g (Work.Cyl.rho x ^ (3 * α)) (psi y)
                  - g (Work.Cyl.rho y ^ (3 * α)) (psi y)| := hsplit
          _ ≤ K * (Work.Cyl.rho x ^ (3 * α)) * |psi x - psi y|
              + K * max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α))
                * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)| :=
              add_le_add hθslice hzslice
          _ ≤ K * ((3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
                * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y)))
              + K * ((3 / 2) * (3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α)) :=
              add_le_add hstep1 hstep2
          _ ≤ K * ((3 / 2) ^ (3 * α) * 4 * Real.pi * (2 ^ (3 * α - 1) * dist x y ^ α))
              + K * ((3 / 2) * (3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α)) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left hstep1' hK0
              · exact le_refl _
          _ = (K * (3 / 2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)
                + K * (3 / 2) * 3 ^ α * (3 / 2) ^ (2 * α)) * dist x y ^ α := by ring_nf
          _ ≤ C * dist x y ^ α :=
              mul_le_mul_of_nonneg_right hC56 (Real.rpow_nonneg hdnn α)

end Work.ConstructionInstance
