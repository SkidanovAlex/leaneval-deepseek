import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Smooth.E1_E2_continuousOn_Icc

/-!
# The model radicand and the graph composites for `E₁`, `E₂`

This module is a self-contained copy of the model data used for the odd inhomogeneities `E₁`,
`E₂`.  The radicand `ψ_h(u,t) = semicircle t ² - (u t + h u)²` equals the *polynomial*
`mRad u (h u) t = 1 - t² - (u t + h u)²` as soon as `|t| ≤ 1`, so on the box
`[c, 1-τ] × [-1/100, 1/100] × [-√2⁻¹, √2⁻¹]` (on which `mRad` stays positive) the two
inhomogeneities are parametric integrals of the graph composites
`u ↦ mPhiF n (u, h u, t)` and `u ↦ mPhiB n (u, h u, t) * lineSlope h u t` of the *fixed* smooth
model functions `mPhiF n`, `mPhiB n`.

The module also records the uniform bound `m_ball_slice_bounds` for the unperturbed (`h = 0`)
slices, which is what turns the three-variable jet tool
(`exists_bound_comp_pair_sub_param`) into an unconditional bound for the perturbed slices.
-/

namespace Work.OddVolterra.DiffBounds

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Commons.Geometry.Ulam

/-! ## The model data -/

/-- The polynomial model `1 - t² - (x t + y)²` of the radicand, with `y` the value of the
perturbation at the slope `x`. -/
def mRad (x y t : ℝ) : ℝ := 1 - t ^ 2 - (x * t + y) ^ 2

/-- The `E₁` integrand as a function of the triple `(slope, perturbation value, section)`. -/
def mPhiF (n : ℕ) (p : ℝ × ℝ × ℝ) : ℝ :=
  mRad p.1 p.2.1 p.2.2 ^ n * Real.sqrt (mRad p.1 p.2.1 p.2.2)

/-- The radicand part of the `E₂` integrand as a function of the triple
`(slope, perturbation value, section)`. -/
def mPhiB (n : ℕ) (p : ℝ × ℝ × ℝ) : ℝ :=
  mRad p.1 p.2.1 p.2.2 ^ (n - 1) * Real.sqrt (mRad p.1 p.2.1 p.2.2)

/-- The open set of triples on which the model radicand is positive. -/
def mUpos : Set (ℝ × ℝ × ℝ) := {p | 0 < mRad p.1 p.2.1 p.2.2}

lemma mRad_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℝ => mRad p.1 p.2.1 p.2.2) := by
  unfold mRad
  fun_prop

lemma isOpen_mUpos : IsOpen mUpos :=
  isOpen_lt continuous_const mRad_contDiff.continuous

lemma contDiffOn_mPhiF (n : ℕ) : ContDiffOn ℝ (⊤ : ℕ∞) (mPhiF n) mUpos := by
  have hrad : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℝ => mRad p.1 p.2.1 p.2.2) mUpos :=
    mRad_contDiff.contDiffOn
  exact (hrad.pow n).mul (hrad.sqrt (fun p hp => ne_of_gt hp))

lemma contDiffOn_mPhiB (n : ℕ) : ContDiffOn ℝ (⊤ : ℕ∞) (mPhiB n) mUpos := by
  have hrad : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℝ => mRad p.1 p.2.1 p.2.2) mUpos :=
    mRad_contDiff.contDiffOn
  exact (hrad.pow (n - 1)).mul (hrad.sqrt (fun p hp => ne_of_gt hp))

/-! ## Elementary facts about the profile `profileX 1` -/

lemma profileX_one_pos' : (0 : ℝ) < profileX 1 := profileX_pos 1 (by norm_num)

lemma profileX_one_sq' : (profileX 1) ^ 2 = (1 : ℝ) / 2 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [Commons.Geometry.Ulam.profileX, show (1 : ℝ) + 1 ^ 2 = 2 by norm_num, div_pow,
    one_pow, Real.sq_sqrt h2.le]

lemma half_lt_profileX_one : (1 : ℝ) / 2 < profileX 1 := by
  have h := profileX_one_sq'
  have hp := profileX_one_pos'
  nlinarith

lemma profileX_one_le_one : profileX 1 ≤ 1 := by
  rw [Commons.Geometry.Ulam.profileX,
    div_le_one (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 1 + 1 ^ 2))]
  rw [show (1 : ℝ) + 1 ^ 2 = 2 by norm_num]
  exact Real.one_le_sqrt.mpr (by norm_num)

lemma profileX_one_lt_one : profileX 1 < 1 := by
  rw [Commons.Geometry.Ulam.profileX,
    div_lt_one (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 1 + 1 ^ 2))]
  rw [show (1 : ℝ) + 1 ^ 2 = 2 by norm_num]
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hsq := Real.sq_sqrt h2
  have hnn := Real.sqrt_nonneg 2
  nlinarith

/-- `1 - τ = 9/10`, with `τ = 1/10` the half-width of the transition window. -/
lemma one_sub_tau_eq : (1 : ℝ) - tau = 9 / 10 := by
  norm_num [Work.OddVolterra.tau]

lemma abs_le_one_of_mem_uIcc_profileX {t : ℝ}
    (ht : t ∈ Set.uIcc (-(profileX 1)) (profileX 1)) : |t| ≤ 1 := by
  rw [Set.uIcc_of_le (by linarith [profileX_one_pos'])] at ht
  have h1 := profileX_one_le_one
  rw [abs_le]
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- On `|t| ≤ 1` the radicand `ψ_h` agrees with the polynomial model. -/
lemma psi_eq_quad {h : ℝ → ℝ} {u t : ℝ} (ht : |t| ≤ 1) :
    psi h semicircle u t = 1 - t ^ 2 - (u * t + h u) ^ 2 := by
  have ht2 : t ^ 2 ≤ 1 := by
    have h := abs_le.mp ht
    nlinarith [h.1, h.2]
  have h1 : 0 ≤ 1 - t ^ 2 := by linarith
  unfold psi line Commons.Geometry.Ulam.semicircle
  rw [Real.sq_sqrt h1]

/-! ## Positivity of the model radicand on the box -/

/-- On the box `[c, 1-τ] × [-1/100, 1/100] × [-√2⁻¹, √2⁻¹]` (with `0 < c ≤ 1-τ`) the model
radicand is positive. -/
lemma m_box_pos {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 - tau)
    {x y t : ℝ} (hx : x ∈ Set.Icc c (1 - tau)) (hy : |y| ≤ 1 / 100)
    (ht : |t| ≤ profileX 1) : 0 < mRad x y t := by
  have hp : (0 : ℝ) < profileX 1 := profileX_one_pos'
  have hp2 := profileX_one_sq'
  have hphalf := half_lt_profileX_one
  have ht9 : (1 : ℝ) - tau = 9 / 10 := one_sub_tau_eq
  have hx1 : |x| ≤ 1 - tau := by
    rw [abs_le]
    exact ⟨by linarith [hx.1, hc], hx.2⟩
  have hb : |x * t + y| ≤ (1 - tau) * profileX 1 + 1 / 100 := by
    calc |x * t + y| ≤ |x * t| + |y| := abs_add_le _ _
      _ = |x| * |t| + |y| := by rw [abs_mul]
      _ ≤ (1 - tau) * profileX 1 + 1 / 100 := by
          have h1 : |x| * |t| ≤ (1 - tau) * profileX 1 :=
            mul_le_mul hx1 ht (abs_nonneg _) (by linarith [hx.1, hc])
          linarith
  have hkey : (1 - tau) * profileX 1 + 1 / 100 < profileX 1 := by
    rw [ht9]
    nlinarith
  have hsq : (x * t + y) ^ 2 < profileX 1 ^ 2 := by
    rw [sq_lt_sq, abs_of_pos hp]
    exact hb.trans_lt hkey
  have ht2 : t ^ 2 ≤ profileX 1 ^ 2 := by
    rw [sq_le_sq, abs_of_pos hp]
    exact ht
  rw [mRad, hp2] at *
  linarith

/-- The box is contained in the positivity region of the model radicand. -/
lemma m_box_subset_mUpos {c R p : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 - tau)
    (hR : R ≤ 1 / 100) (hp : p = profileX 1) :
    (Set.Icc c (1 - tau) ×ˢ Set.Icc (-R) R ×ˢ Set.Icc (-p) p : Set (ℝ × ℝ × ℝ))
      ⊆ mUpos := by
  rintro ⟨x, y, t⟩ ⟨hx, hy, ht⟩
  have hy' : |y| ≤ 1 / 100 := by
    rw [abs_le]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have ht' : |t| ≤ profileX 1 := by
    rw [abs_le]
    exact ⟨by linarith [ht.1, hp], by linarith [ht.2, hp]⟩
  exact m_box_pos hc hc1 hx hy' ht'

/-! ## The inhomogeneities as parametric integrals of the graph composites -/

lemma m_psi_eq (n : ℕ) {h : ℝ → ℝ} {t : ℝ} (ht : |t| ≤ 1) :
    (fun u : ℝ => psi h semicircle u t ^ n * Real.sqrt (psi h semicircle u t)) =
      fun u : ℝ => mPhiF n (u, h u, t) := by
  funext u
  rw [psi_eq_quad ht]
  rfl

lemma m_psi_eq' (n : ℕ) {h : ℝ → ℝ} {t : ℝ} (ht : |t| ≤ 1) :
    (fun u : ℝ => psi h semicircle u t ^ (n - 1) * Real.sqrt (psi h semicircle u t)
        * lineSlope h u t) =
      fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t := by
  funext u
  rw [psi_eq_quad ht]
  rfl

/-- `E₁` as the parametric integral of the graph composite of `mPhiF`. -/
lemma mE1_eq (n : ℕ) (h : ℝ → ℝ) (x : ℝ) :
    E1 n h x = ∫ t in (-(profileX 1))..(profileX 1),
      iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) x := by
  rw [E1]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [m_psi_eq n (abs_le_one_of_mem_uIcc_profileX ht)]

/-- `E₂` as the parametric integral of the graph composite of `mPhiB`. -/
lemma mE2_eq (n : ℕ) (h : ℝ → ℝ) (x : ℝ) :
    E2 n h x = ∫ t in (-(profileX 1))..(profileX 1),
      iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) x := by
  rw [E2]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [m_psi_eq' n (abs_le_one_of_mem_uIcc_profileX ht)]

/-! ## Uniform bounds for the unperturbed slices -/

/-- Uniform bounds on the ball slices `u ↦ mPhiB n (u, 0, t)` on the box. -/
lemma m_ball_slice_bounds (n : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 - tau) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ v ∈ Set.Icc c (1 - tau),
      ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
      |iteratedDeriv k (fun u : ℝ => mPhiB n (u, 0, t)) v| ≤ M := by
  set U : Set (ℝ × ℝ) := {q : ℝ × ℝ | 0 < mRad q.2 0 q.1} with hUdef
  have hU : IsOpen U := by
    rw [hUdef]
    exact isOpen_lt continuous_const (by unfold mRad; fun_prop)
  have hF : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => mPhiB n (q.2, 0, q.1)) U := by
    have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => mRad q.2 0 q.1) U :=
      (by unfold mRad; fun_prop : ContDiff ℝ (⊤ : ℕ∞)
        (fun q : ℝ × ℝ => mRad q.2 0 q.1)).contDiffOn
    exact (hcomp.pow (n - 1)).mul (hcomp.sqrt (fun q hq => ne_of_gt hq))
  set K : Set (ℝ × ℝ) := Set.Icc (-(profileX 1)) (profileX 1) ×ˢ Set.Icc c (1 - tau)
    with hKdef
  have hK : IsCompact K := by rw [hKdef]; exact isCompact_Icc.prod isCompact_Icc
  have hKU : K ⊆ U := by
    rintro ⟨t, v⟩ ⟨ht, hv⟩
    have ht' : |t| ≤ profileX 1 := by
      rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩
    exact m_box_pos hc hc1 hv (by norm_num) ht'
  obtain ⟨M, hM⟩ := Work.OddVolterra.Smooth.parametric_iteratedDeriv_bound_smooth
    (F := fun t u : ℝ => mPhiB n (u, 0, t)) hU hF hK hKU k
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro v hv t ht
  have hmem : (t, v) ∈ K := by
    rw [hKdef]
    exact ⟨⟨by linarith [ht.1], ht.2⟩, hv⟩
  have h1 : |iteratedDeriv k (fun u : ℝ => mPhiB n (u, 0, t)) v| ≤ M := hM (t, v) hmem
  exact le_trans h1 (le_max_left M 0)

/-! ## The graph of `h` over the positivity region -/

/-- The graph of `h` over the positivity region `mUpos` of the model radicand: the set of pairs
`(u, t)` for which the slice `u' ↦ mPhiF n (u', h u', t)` is a smooth graph composite. -/
def graphPos (h : ℝ → ℝ) : Set (ℝ × ℝ) := (fun q : ℝ × ℝ => (q.1, h q.1, q.2)) ⁻¹' mUpos

lemma mem_graphPos {h : ℝ → ℝ} {u t : ℝ} : (u, t) ∈ graphPos h ↔ 0 < mRad u (h u) t :=
  Iff.rfl

lemma isOpen_graphPos {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) : IsOpen (graphPos h) := by
  have hcont : Continuous fun q : ℝ × ℝ => (q.1, h q.1, q.2) := by fun_prop
  exact isOpen_mUpos.preimage hcont

lemma contDiff_graphCurve {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => (q.1, h q.1, q.2)) := by
  fun_prop

lemma contDiffOn_graphPhiF (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => mPhiF n (q.1, h q.1, q.2)) (graphPos h) := by
  exact (contDiffOn_mPhiF n).comp (contDiff_graphCurve hh).contDiffOn (fun q hq => hq)

lemma contDiffOn_graphPhiB (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => mPhiB n (q.1, h q.1, q.2)) (graphPos h) := by
  exact (contDiffOn_mPhiB n).comp (contDiff_graphCurve hh).contDiffOn (fun q hq => hq)

/-- Membership in `graphPos` from the box bounds. -/
lemma mem_graphPos_of_box {h : ℝ → ℝ} {c v t : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 - tau)
    (hv : v ∈ Set.Icc c (1 - tau)) (hh : |h v| ≤ 1 / 100) (ht : |t| ≤ profileX 1) :
    (v, t) ∈ graphPos h := by
  rw [mem_graphPos]
  exact m_box_pos hc hc1 hv hh ht

/-! ## The `E₂` graph composite -/

/-- The `E₂` integrand as a function of the plane `(u, t)`, for a fixed perturbation `h`:
`u ↦ mPhiB n (u, h u, t) * lineSlope h u t`. -/
def graphPhiH (n : ℕ) (h : ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun q => mPhiB n (q.1, h q.1, q.2) * lineSlope h q.1 q.2

lemma graphPhiH_apply (n : ℕ) (h : ℝ → ℝ) (u t : ℝ) :
    graphPhiH n h (u, t) = mPhiB n (u, h u, t) * lineSlope h u t :=
  rfl

/-- The derivative of a `C^∞` function is `C^∞`. -/
lemma contDiff_deriv_of_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv h) := by
  rw [← contDiffOn_univ]
  exact hh.contDiffOn.deriv_of_isOpen isOpen_univ Work.OddVolterra.Smooth.top_coe_add_one_le

lemma contDiffOn_graphLineSlope {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => lineSlope h q.1 q.2) (graphPos h) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv h) := contDiff_deriv_of_contDiff hh
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => q.2 + deriv h q.1) := by
    exact contDiff_snd.add (hd.comp contDiff_fst)
  refine h1.contDiffOn.mono (subset_univ _) |>.congr ?_
  intro q _
  rfl

lemma contDiffOn_graphPhiH (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiffOn ℝ (⊤ : ℕ∞) (graphPhiH n h) (graphPos h) := by
  exact (contDiffOn_graphPhiB n hh).mul (contDiffOn_graphLineSlope hh)

/-- Smoothness of the graph-composite slice `u ↦ mPhiB n (u, h u, t)`. -/
lemma contDiffAt_graphPhiB_slice (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {v t : ℝ}
    (hvt : (v, t) ∈ graphPos h) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => mPhiB n (u, h u, t)) v := by
  have hcurve : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => (u, h u, t)) v := by fun_prop
  have hF : ContDiffAt ℝ (⊤ : ℕ∞) (mPhiB n) (v, h v, t) :=
    (contDiffOn_mPhiB n).contDiffAt (isOpen_mUpos.mem_nhds hvt)
  exact ContDiffAt.fun_comp v hF hcurve

end

end Work.OddVolterra.DiffBounds
