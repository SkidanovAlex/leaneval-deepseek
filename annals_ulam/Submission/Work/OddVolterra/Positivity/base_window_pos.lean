import Mathlib
import Submission.Work.OddVolterra.Defs

/-!
# Positivity of `ψ` on a *closed* base window, uniform in the slope

This file proves `Work.OddVolterra.Positivity.base_window_pos`, the input that
lets the odd-case Volterra argument differentiate the moment integrals of the
section `(-x s, y s)` under the integral sign on a *closed* `t`-window
(compare `Work.OddVolterra.window_iteratedDeriv_of_eventually_pos`, whose
hypothesis is exactly the conclusion proved here, with `c = -1/√2`,
`d = 1/√2` and `Ψ = psi h semicircle`).

Recall `psi h f s t = f t ^ 2 - line h s t ^ 2` with `line h s t = s * t + h s`,
so that for `f = semicircle` and `|t| ≤ 1` the quantity `psi h semicircle s t`
equals `1 - t^2 - (s * t + h s)^2`: the difference between the (squared) upper
unit semicircle and the (squared) cutting line `L_s`.

## Mathematics

Fix `s` in the base window `[a, c]`, with `a > 0` and `c < 1`.  We must produce
a neighbourhood of `s` in which `psi h semicircle u t > 0` for **every**
`t ∈ [-1/√2, 1/√2]`.  Because `t ↦ psi h semicircle u t` is a concave quadratic
in `t`, it is enough to control the two endpoints `t = ±1/√2`:

* `hxy` at `u = 1` together with `hxb`, `hyb` and `hfb` force `1 * 1/√2 + h 1 = 1/√2`,
  hence `h 1 = 0`; so `L_1` is the diagonal `t ↦ t` and hits the semicircle at
  `t = ±1/√2`, where both sides equal `1/√2`.
* `hKden` at `σ = 1` — the positivity of the Abel denominators of the odd
  transition-slope system, at the *right endpoint* of the slope window — then
  reads, with `H = hquot h s 1 = (h 1 - h s)/(1 - s) = -h s/(1-s)`,
  `0 < (1/√2 + H) (1/√2 + L_s(1/√2))` and
  `0 < (-1/√2 + H) (-1/√2 + L_s(-1/√2))`, i.e., after writing
  `L_s(±1/√2) = ±1/√2 ∓ (1-s)(1/√2 ± H)`,
  `0 < u (2P - c u)` with `P = 1/√2`, `c = 1 - s > 0`, `u = 1/√2 ± H`.
  `0 < u (2P - c u)` forces `0 < u` and `c u < 2 P`, hence `|P - c u| < P`:
  that is, `|L_s(±1/√2)| < 1/√2` **strictly**.  (This is where `c < 1` is
  used: at `s = 1` the endpoint value degenerates to `0`.)

Consequently both endpoint values of the concave quadratic are strictly
positive, hence the quadratic is strictly positive on the whole closed window,
and a compactness (thickening) argument in `u` upgrades this to a uniform
neighbourhood of `s`.

Note that `c < 1` is essential: on `[a, 1]` the conclusion can only be stated
with the *open* window `(-1/√2, 1/√2)` (see
`Work.OddVolterra.RowIdentity.psi_base_window_pos`), whereas on `[a, c]` with
`c < 1` there is a positive margin at both endpoints, which is exactly what the
closed-window differentiation lemma needs.
-/

namespace Work.OddVolterra.Positivity

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Commons.Geometry.Ulam

noncomputable section

/-! ## Elementary positivity helpers -/

/-- A positive-product condition of the shape produced by `hKden` at the right
endpoint `σ = 1`: if `0 < u (2 P - c u)` with `P > 0` and `c > 0`, then
`|P - c u| < P`.  (Indeed `u > 0` and `c u < 2P`.) -/
lemma abs_sub_lt_of_mul_pos {P c u : ℝ} (hP : 0 < P) (hc : 0 < c)
    (h : 0 < u * (2 * P - c * u)) : |P - c * u| < P := by
  have hu_pos : 0 < u := by
    by_contra hle
    have hle' : u ≤ 0 := le_of_not_gt hle
    rcases lt_or_eq_of_le hle' with hlt | heq
    · have hcu : c * u < 0 := mul_neg_of_pos_of_neg hc hlt
      have hpos : 0 < 2 * P - c * u := by linarith
      have hneg : u * (2 * P - c * u) < 0 := mul_neg_of_neg_of_pos hlt hpos
      linarith
    · subst heq
      simp at h
  have hcu_pos : 0 < c * u := mul_pos hc hu_pos
  have hcu_lt : c * u < 2 * P := by
    have h2 : 0 < 2 * P - c * u := pos_of_mul_pos_right h (le_of_lt hu_pos)
    linarith
  rw [abs_lt]
  constructor <;> linarith

/-- The chord identity for the concave quadratic `g(t) = 1 - t² - (A t + B)²`:
writing `t = u p + v (-p)` with `u + v = 1`, the value at `t` is the
corresponding convex combination of the endpoint values plus the strictly
positive curvature term `(1 + A²) (p² - t²)`. -/
lemma phi_chord_identity (A B p t u v : ℝ) (huv : u + v = 1)
    (ht : t = u * p + v * (-p)) :
    1 - t ^ 2 - (A * t + B) ^ 2
      = u * (1 - p ^ 2 - (A * p + B) ^ 2) + v * (1 - p ^ 2 - (A * (-p) + B) ^ 2)
        + (1 + A ^ 2) * (p ^ 2 - t ^ 2) := by
  subst ht
  have hv : v = 1 - u := by linarith
  subst hv
  ring

/-! ## The main statement -/

theorem base_window_pos {a c s : ℝ} (ha : 0 < a) (hac : a ≤ c) (hc1 : c < 1) {h x y f : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hx : ContDiffOn ℝ (⊤ : ℕ∞) x (Set.Ioi 0)) (hy : ContDiffOn ℝ (⊤ : ℕ∞) y (Set.Ioi 0))
    (hxy : ∀ u ∈ Set.Ioc (0 : ℝ) 1, f (y u) = u * y u + h u ∧ f (-(x u)) = -(u * (-(x u)) + h u))
    (hxb : x 1 = Commons.Geometry.Ulam.profileX 1)
    (hyb : y 1 = Commons.Geometry.Ulam.profileX 1)
    (hfb : ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
      f t = Commons.Geometry.Ulam.semicircle t)
    (hxle : ∀ s ∈ Set.Icc a 1, x 1 ≤ x s) (hyle : ∀ s ∈ Set.Icc a 1, y 1 ≤ y s)
    (hmid : ∀ s ∈ Set.Icc a 1, ∀ t ∈ Set.Ioo (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
      0 < psi h Commons.Geometry.Ulam.semicircle s t)
    (hKden : ∀ s σ : ℝ, a ≤ s → s ≤ σ → σ ≤ 1 →
      0 < (y σ + hquot h s σ) * (line h σ (y σ) + line h s (y σ)) ∧
      0 < (-(x σ) + hquot h s σ) * (line h σ (-(x σ)) + line h s (-(x σ))))
    (hs : s ∈ Set.Icc a c) :
    ∃ ε > 0, ∀ u : ℝ, |u - s| < ε →
      ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
        0 < psi h Commons.Geometry.Ulam.semicircle u t := by
  -- ### The endpoint `P = profileX 1 = 1/√2`
  have hp_pos : 0 < profileX 1 := profileX_pos 1 (by norm_num)
  have hp_sq : (profileX 1) ^ 2 = (1 : ℝ) / 2 := by rw [profileX_sq]; norm_num
  have hp_le_one : profileX 1 ≤ 1 := (profileX_mem_Icc 1).2
  have hsemi_p : semicircle (profileX 1) = profileX 1 := by
    have h1 := semicircle_sq_of_mem_Icc (profileX_mem_Icc 1)
    have h2 : semicircle (profileX 1) ^ 2 = (profileX 1) ^ 2 := by rw [h1, hp_sq]; norm_num
    have hnn : 0 ≤ semicircle (profileX 1) := Real.sqrt_nonneg _
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with hh' | hh'
    · exact hh'
    · rw [hh'] at hnn; linarith
  have hmem_p : profileX 1 ∈ Set.Icc (-(profileX 1)) (profileX 1) := ⟨by linarith, le_rfl⟩
  have hs_lt_one : s < 1 := lt_of_le_of_lt hs.2 hc1
  -- ### Step 1: `h 1 = 0`
  obtain ⟨h1b, _⟩ := hxy 1 ⟨by norm_num, le_rfl⟩
  have hfb_p : f (profileX 1) = profileX 1 := by rw [hfb _ hmem_p, hsemi_p]
  rw [hyb, hfb_p] at h1b
  have hh1 : h 1 = 0 := by linarith
  -- ### Step 2: `hKden` at `σ = 1` gives the strict endpoint inequalities
  obtain ⟨hk1, hk2⟩ := hKden s 1 hs.1 (le_of_lt hs_lt_one) le_rfl
  set H := hquot h s 1 with hH
  have hline1 : line h 1 (profileX 1) = profileX 1 := by unfold line; rw [hh1]; ring
  have hline2 : line h 1 (-(profileX 1)) = -(profileX 1) := by unfold line; rw [hh1]; ring
  rw [hyb, hline1] at hk1
  rw [hxb, hline2] at hk2
  have hHs : h s = -(1 - s) * H := by
    have hsub := sub_mul_hquot (h := h) ((contDiff_infty.mp hh) 1) s 1
    rw [hh1, ← hH] at hsub
    linarith
  have hsp : line h s (profileX 1) = profileX 1 - (1 - s) * (profileX 1 + H) := by
    unfold line; rw [hHs]; ring
  have hsmp : line h s (-(profileX 1)) = -(profileX 1) + (1 - s) * (profileX 1 - H) := by
    unfold line; rw [hHs]; ring
  have hkey1 : 0 < (profileX 1 + H) * (2 * profileX 1 - (1 - s) * (profileX 1 + H)) := by
    have hsum : profileX 1 + line h s (profileX 1)
        = 2 * profileX 1 - (1 - s) * (profileX 1 + H) := by
      rw [hsp]; ring
    rwa [hsum] at hk1
  have hkey2 : 0 < (profileX 1 - H) * (2 * profileX 1 - (1 - s) * (profileX 1 - H)) := by
    have hsum : (-(profileX 1) + H) * (-(profileX 1) + line h s (-(profileX 1)))
        = (profileX 1 - H) * (2 * profileX 1 - (1 - s) * (profileX 1 - H)) := by
      rw [hsmp]; ring
    rwa [hsum] at hk2
  have hLp : |line h s (profileX 1)| < profileX 1 := by
    have habs := abs_sub_lt_of_mul_pos (P := profileX 1) (c := 1 - s) (u := profileX 1 + H)
      hp_pos (by linarith) hkey1
    rwa [← hsp] at habs
  have hLn : |line h s (-(profileX 1))| < profileX 1 := by
    have habs := abs_sub_lt_of_mul_pos (P := profileX 1) (c := 1 - s) (u := profileX 1 - H)
      hp_pos (by linarith) hkey2
    have heq' : line h s (-(profileX 1)) = -(profileX 1 - (1 - s) * (profileX 1 - H)) := by
      rw [hsmp]; ring
    rw [heq', abs_neg]
    exact habs
  -- ### Step 3: both endpoint values of the concave quadratic are positive at `s`
  have hGp : 0 < 1 - (profileX 1) ^ 2 - (s * (profileX 1) + h s) ^ 2 := by
    have hsq : (s * (profileX 1) + h s) ^ 2 < (profileX 1) ^ 2 := by
      have habs : |s * (profileX 1) + h s| < |profileX 1| := by
        rw [abs_of_pos hp_pos]
        exact hLp
      exact sq_lt_sq.mpr habs
    linarith [hp_sq]
  have hGn : 0 < 1 - (profileX 1) ^ 2 - (s * (-(profileX 1)) + h s) ^ 2 := by
    have hsq : (s * (-(profileX 1)) + h s) ^ 2 < (profileX 1) ^ 2 := by
      have habs : |s * (-(profileX 1)) + h s| < |profileX 1| := by
        rw [abs_of_pos hp_pos]
        exact hLn
      exact sq_lt_sq.mpr habs
    linarith [hp_sq]
  -- ### Step 4: concavity propagates the endpoint positivity to the whole closed window
  have hPhi_s : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
      0 < 1 - t ^ 2 - (s * t + h s) ^ 2 := by
    intro t ht
    rcases lt_or_eq_of_le ht.1 with hlt | heq
    · rcases lt_or_eq_of_le ht.2 with hlt2 | heq2
      · have hup : 0 < (t + profileX 1) / (2 * profileX 1) := by
          apply div_pos <;> linarith
        have hvp : 0 < (profileX 1 - t) / (2 * profileX 1) := by
          apply div_pos <;> linarith
        have huv : (t + profileX 1) / (2 * profileX 1)
            + (profileX 1 - t) / (2 * profileX 1) = 1 := by
          field_simp; ring
        have ht' : t = (t + profileX 1) / (2 * profileX 1) * profileX 1
            + ((profileX 1 - t) / (2 * profileX 1)) * (-(profileX 1)) := by
          field_simp; ring
        have hkey := phi_chord_identity s (h s) (profileX 1) t
          ((t + profileX 1) / (2 * profileX 1))
          ((profileX 1 - t) / (2 * profileX 1)) huv ht'
        rw [hkey]
        have h1 : 0 < (t + profileX 1) / (2 * profileX 1)
            * (1 - (profileX 1) ^ 2 - (s * (profileX 1) + h s) ^ 2) :=
          mul_pos hup hGp
        have h2 : 0 ≤ (profileX 1 - t) / (2 * profileX 1)
            * (1 - (profileX 1) ^ 2 - (s * (-(profileX 1)) + h s) ^ 2) :=
          mul_nonneg (le_of_lt hvp) (le_of_lt hGn)
        have h3 : 0 ≤ (1 + s ^ 2) * ((profileX 1) ^ 2 - t ^ 2) := by
          have hsq : t ^ 2 < (profileX 1) ^ 2 := by
            have habs : |t| < |profileX 1| := by
              rw [abs_of_pos hp_pos]
              exact abs_lt.mpr ⟨hlt, hlt2⟩
            exact sq_lt_sq.mpr habs
          have h4 : 0 ≤ (profileX 1) ^ 2 - t ^ 2 := by linarith
          positivity
        linarith
      · rw [heq2]; exact hGp
    · rw [← heq]
      have hsq : (-(profileX 1)) ^ 2 = (profileX 1) ^ 2 := by ring
      rw [hsq]
      exact hGn
  -- ### Step 5: compactness upgrades pointwise positivity at `s` to a neighbourhood in `u`
  set Φ : ℝ × ℝ → ℝ := fun q => 1 - q.2 ^ 2 - (q.1 * q.2 + h q.1) ^ 2 with hΦdef
  have hΦcont : Continuous Φ := by
    rw [hΦdef]
    fun_prop
  have hΦs : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1), 0 < Φ (s, t) := by
    intro t ht
    simpa [hΦdef] using hPhi_s t ht
  let K : Set (ℝ × ℝ) :=
    ({s} : Set ℝ) ×ˢ Set.Icc (-(profileX 1)) (profileX 1)
  have hKcomp : IsCompact K := isCompact_singleton.prod isCompact_Icc
  have hKsub : K ⊆ {q : ℝ × ℝ | 0 < Φ q} := by
    rintro ⟨u, t⟩ ⟨hu, ht⟩
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact hΦs t ht
  have hUopen : IsOpen {q : ℝ × ℝ | 0 < Φ q} := isOpen_lt continuous_const hΦcont
  obtain ⟨ρ, hρ, hρK⟩ := hKcomp.exists_thickening_subset_open hUopen hKsub
  refine ⟨ρ, hρ, ?_⟩
  intro u hu t ht
  have hmem : (u, t) ∈ Metric.thickening ρ K := by
    rw [Metric.mem_thickening_iff]
    refine ⟨(s, t), ⟨by simp, ht⟩, ?_⟩
    rw [Prod.dist_eq, dist_self, Real.dist_eq]
    exact max_lt hu hρ
  have hpos : 0 < Φ (u, t) := hρK hmem
  have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · linarith [ht.1, hp_le_one]
    · linarith [ht.2, hp_le_one]
  have hΦut : Φ (u, t) = 1 - t ^ 2 - (u * t + h u) ^ 2 := by simp [hΦdef]
  rw [psi, line, semicircle_sq_of_mem_Icc htIcc, ← hΦut]
  exact hpos

end

end Work.OddVolterra.Positivity
