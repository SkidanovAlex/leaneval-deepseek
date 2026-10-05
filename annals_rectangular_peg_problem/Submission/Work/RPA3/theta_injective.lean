import Mathlib
import Submission.Work.RPA3.TubularDefs
import Submission.Work.RPA3.Symp
import Submission.Work.RPA3.InjectiveDefs
import Submission.Work.RPA3.theta_std
import Submission.Work.RPA3.theta_per
import Submission.Work.RPA3.theta_per_int
import Submission.Work.RPA3.ell_per_int
import Submission.Work.RPA3.contDiff_thetaP
import Submission.Work.RPA3.int_tendsto_eventually_const
import Submission.Work.RPA3.theta_injective_compact
import Submission.Work.RPA3.theta_coord_bounds

open Filter Set
open scoped ContDiff Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPA3

/-! ## Auxiliary lemmas for the global injectivity of the tubular map -/

namespace ThInj

/-- `Tk k`, spelled out. -/
theorem Tk_apply' (k : ℤ) (z : PS) : Tk k z = ((z.1.1, z.1.2 + 2 * Real.pi * k), z.2) := rfl

/-- If `Tk k` fixes a point then `k = 0`. -/
theorem Tk_int_injective (z : PS) {k m : ℤ} (h : Tk k z = Tk m z) : k = m := by
  have h1 : z.1.2 + 2 * Real.pi * (k : ℝ) = z.1.2 + 2 * Real.pi * (m : ℝ) := by
    have := congrArg (fun p : PS => p.1.2) h
    simpa only [Tk_fst_snd] using this
  have h2 : 2 * Real.pi * (k : ℝ) = 2 * Real.pi * (m : ℝ) := by linarith
  have h3 : (k : ℝ) = (m : ℝ) := by
    have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact mul_left_cancel₀ hπ h2
  exact_mod_cast h3

/-- In the standard region, `q₁ ∘ θ` is the `x`-coordinate. -/
theorem q1_theta_of_std (L : LagFamilyAll) {τ x t : ℝ} (ξ : ℝ × ℝ) (hx : L.X0 ≤ |x|) :
    (theta L τ x t ξ).1.1 = x := by
  rw [theta_std L τ x t ξ hx]

/-- In the standard region, `q₂ ∘ θ` is the `t`-coordinate. -/
theorem q2_theta_of_std (L : LagFamilyAll) {τ x t : ℝ} (ξ : ℝ × ℝ) (hx : L.X0 ≤ |x|) :
    (theta L τ x t ξ).1.2 = t := by
  rw [theta_std L τ x t ξ hx]

/-- **In the standard region an equality `θ = Tk k θ'` is a good pair.**  If `|x| ≥ X₀` and
`|x'| ≥ X₀` then `θ = ((x,t),(-ξ₁,-ξ₂))` on both sides, so the equality reads `x = x'`, `ξ = ξ'`
and `t = t' + 2πk`. -/
theorem good_of_std (L : LagFamilyAll) {τ x t x' t' : ℝ} {ξ ξ' : ℝ × ℝ} {k : ℤ}
    (hx : L.X0 ≤ |x|) (hx' : L.X0 ≤ |x'|)
    (h : theta L τ x t ξ = Tk k (theta L τ x' t' ξ')) :
    x = x' ∧ ξ = ξ' ∧ ∃ m : ℤ, t' = t + 2 * Real.pi * m := by
  rw [theta_std L τ x t ξ hx, theta_std L τ x' t' ξ' hx', Tk_apply'] at h
  have h1 : (x, t) = (x', t' + 2 * Real.pi * k) := congrArg Prod.fst h
  have h2 : (-ξ.1, -ξ.2) = (-ξ'.1, -ξ'.2) := congrArg Prod.snd h
  have hxeq : x = x' := (Prod.ext_iff.mp h1).1
  have hteq : t = t' + 2 * Real.pi * k := (Prod.ext_iff.mp h1).2
  have hξeq : ξ = ξ' := by
    have h3 := Prod.ext_iff.mp h2
    exact Prod.ext (neg_inj.mp h3.1) (neg_inj.mp h3.2)
  exact ⟨hxeq, hξeq, ⟨-k, by rw [hteq]; push_cast; ring⟩⟩

/-- **Bound on the `x`-coordinates of a bad pair.**  Suppose `q₁ ∘ θ` is bounded by `M` on the
compact region `τ ∈ [-1,2]`, `|x| ≤ X`, `t ∈ [0,2π]`, `‖ξ‖ ≤ ε`, where `0 ≤ X` and `L.X0 ≤ X`.  If a
pair with `t, t' ∈ [0,2π]`, `‖ξ‖, ‖ξ'‖ ≤ ε` satisfies `θ = Tk k θ'` and is *not* a standard pair
(`|x| ≥ X₀` and `|x'| ≥ X₀` on both sides), then both `x` and `x'` are bounded by `max X M`:
`q₁` is `Tk`-invariant, so one of the two coordinates is the `q₁`-value of a point in the compact
box, and the other is either bounded by the same value (in the standard region, where `q₁ = x`) or
lies in the box. -/
theorem bad_x_bound (L : LagFamilyAll) {X M ε : ℝ} (hX0 : L.X0 ≤ X)
    (hM : ∀ τ x t (ξ : ℝ × ℝ), τ ∈ Set.Icc (-1 : ℝ) 2 → |x| ≤ X →
      t ∈ Set.Icc 0 (2 * Real.pi) → ‖ξ‖ ≤ ε → |(theta L τ x t ξ).1.1| ≤ M)
    {τ x t x' t' : ℝ} {ξ ξ' : ℝ × ℝ} {k : ℤ}
    (hτ : τ ∈ Set.Icc (-1 : ℝ) 2) (ht : t ∈ Set.Icc 0 (2 * Real.pi))
    (ht' : t' ∈ Set.Icc 0 (2 * Real.pi)) (hξ : ‖ξ‖ ≤ ε) (hξ' : ‖ξ'‖ ≤ ε)
    (h : theta L τ x t ξ = Tk k (theta L τ x' t' ξ'))
    (hnot : ¬ (L.X0 ≤ |x| ∧ L.X0 ≤ |x'|)) :
    |x| ≤ max X M ∧ |x'| ≤ max X M := by
  have hq1 : (theta L τ x t ξ).1.1 = (theta L τ x' t' ξ').1.1 := by
    rw [h]; rfl
  have hXle : X ≤ max X M := le_max_left _ _
  have hMle : M ≤ max X M := le_max_right _ _
  by_cases hx : L.X0 ≤ |x|
  · -- `|x| ≥ X₀`: then `|x'| < X₀`, so `x'` lies in the box
    have hx'lt : ¬ L.X0 ≤ |x'| := fun h' => hnot ⟨hx, h'⟩
    have hx'le : |x'| ≤ X := le_trans (le_of_lt (not_le.mp hx'lt)) hX0
    have hb' : |(theta L τ x' t' ξ').1.1| ≤ M := hM τ x' t' ξ' hτ hx'le ht' hξ'
    have hxstd : (theta L τ x t ξ).1.1 = x := q1_theta_of_std L ξ hx
    refine ⟨?_, le_trans hx'le hXle⟩
    calc |x| = |(theta L τ x t ξ).1.1| := by rw [hxstd]
      _ = |(theta L τ x' t' ξ').1.1| := by rw [hq1]
      _ ≤ M := hb'
      _ ≤ max X M := hMle
  · -- `|x| < X₀`: then `x` lies in the box
    have hxle : |x| ≤ X := le_trans (le_of_lt (not_le.mp hx)) hX0
    have hb : |(theta L τ x t ξ).1.1| ≤ M := hM τ x t ξ hτ hxle ht hξ
    refine ⟨le_trans hxle hXle, ?_⟩
    by_cases hx' : L.X0 ≤ |x'|
    · have hx'std : (theta L τ x' t' ξ').1.1 = x' := q1_theta_of_std L ξ' hx'
      calc |x'| = |(theta L τ x' t' ξ').1.1| := by rw [hx'std]
        _ = |(theta L τ x t ξ).1.1| := by rw [hq1]
        _ ≤ M := hb
        _ ≤ max X M := hMle
    · exact le_trans (le_trans (le_of_lt (not_le.mp hx')) hX0) hXle

/-- **Bound on the integer `k` of a bad pair.**  On the compact region with `|x|, |x'| ≤ B` the
`q₂`-coordinate of `θ` is bounded by `M₂`; since `q₂ ∘ θ = q₂ ∘ (Tk k θ') = q₂ ∘ θ' + 2πk`, the
integer `k` is bounded by `M₂/π`. -/
theorem bad_k_bound (L : LagFamilyAll) {B M2 ε : ℝ}
    (hM2 : ∀ τ x t (ξ : ℝ × ℝ), τ ∈ Set.Icc (-1 : ℝ) 2 → |x| ≤ B →
      t ∈ Set.Icc 0 (2 * Real.pi) → ‖ξ‖ ≤ ε → |(theta L τ x t ξ).1.2| ≤ M2)
    {τ x t x' t' : ℝ} {ξ ξ' : ℝ × ℝ} {k : ℤ}
    (hτ : τ ∈ Set.Icc (-1 : ℝ) 2) (ht : t ∈ Set.Icc 0 (2 * Real.pi))
    (ht' : t' ∈ Set.Icc 0 (2 * Real.pi)) (hξ : ‖ξ‖ ≤ ε) (hξ' : ‖ξ'‖ ≤ ε)
    (hxB : |x| ≤ B) (hx'B : |x'| ≤ B)
    (h : theta L τ x t ξ = Tk k (theta L τ x' t' ξ')) :
    |(k : ℝ)| ≤ M2 / Real.pi := by
  have hq2 : (theta L τ x t ξ).1.2 = (theta L τ x' t' ξ').1.2 + 2 * Real.pi * (k : ℝ) := by
    rw [h]; rfl
  have hb1 := hM2 τ x t ξ hτ hxB ht hξ
  have hb2 := hM2 τ x' t' ξ' hτ hx'B ht' hξ'
  have h2 : 2 * Real.pi * (k : ℝ) = (theta L τ x t ξ).1.2 - (theta L τ x' t' ξ').1.2 := by
    linarith
  have h3 : |2 * Real.pi * (k : ℝ)| ≤ 2 * M2 := by
    rw [h2]
    have h4 : |(theta L τ x t ξ).1.2 - (theta L τ x' t' ξ').1.2|
        ≤ |(theta L τ x t ξ).1.2| + |(theta L τ x' t' ξ').1.2| := by
      rw [sub_eq_add_neg]
      simpa using abs_add_le ((theta L τ x t ξ).1.2) (-(theta L τ x' t' ξ').1.2)
    linarith
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h3
  rw [le_div_iff₀ Real.pi_pos]
  nlinarith [h3]

end ThInj

open ThInj

/-- The strip property: injectivity of the tubular map up to the `2π`-periodicity of the angle,
with `ξ`-radius `ε'`, on the whole strip `τ ∈ [-1,2]`, `x ∈ ℝ`. -/
def InjUpToAll (L : LagFamilyAll) (ε' : ℝ) : Prop :=
  ∀ τ ∈ Set.Icc (-1 : ℝ) 2, ∀ x t x' t' (ξ ξ' : ℝ × ℝ), t ∈ Set.Icc 0 (2 * Real.pi) →
    t' ∈ Set.Icc 0 (2 * Real.pi) → ‖ξ‖ < ε' → ‖ξ'‖ < ε' → ∀ k : ℤ,
    theta L τ x t ξ = Tk k (theta L τ x' t' ξ') →
    (x = x' ∧ ξ = ξ' ∧ ∃ m : ℤ, t' = t + 2 * Real.pi * m)

/-- **D2, injectivity of the tubular map (global in `x`).**  If `thetaP L` is a local
diffeomorphism at the points `ξ = 0` of the strip, then for some `ε' ∈ (0, ε]` the tubular map is
injective (modulo the `2π`-periodicity of the angle) on the *whole* strip
`τ ∈ [-1,2]`, `x ∈ ℝ`, `t ∈ [0,2π]`, `‖ξ‖ < ε'`: `θ(x,t,ξ) = Tk k (θ(x',t',ξ'))` forces `x = x'`,
`ξ = ξ'` and `t' = t + 2πm`.

Proof sketch (contradiction).  Take bad pairs with `‖ξ‖, ‖ξ'‖ < 1/n`.  If *both* `|x|, |x'| ≥ X₀`,
then `theta = ((x,t),(-ξ₁,-ξ₂))` there (`theta_std`) and the equality of `Tk`-translated points
gives `x = x'`, `ξ = ξ'`, `t ≡ t'`, so the pair is good: hence at least one of `x, x'` has
`|x| < X₀`.  The `q₁`-coordinate of `θ` is unchanged by `Tk`, is continuous in the compact region
`τ ∈ [-1,2]`, `|x| ≤ X₀`, `t ∈ [0,2π]`, `‖ξ‖ ≤ ε`, and equals `x` in the standard region `|x| ≥ X₀`;
hence the other variable is bounded by the supremum `M` of `|q₁ ∘ θ|` over that compact region, so
both are bounded, and a subsequence converges to `p* = (x*,t*,0)`, `q* = (x'*,t'*,0)` with
`θ(p*) = Tk k (θ(q*))` for the eventually constant integer `k` (boundedness of `k` from the same
`q₂`-argument).  At `ξ = 0` this is `ℓ(x*,t*) = ℓ(x'*,t'*+2πk)`, so `L.inj` gives `x* = x'*` and
`t'* + 2πk ≡ t*`, which forces `m = k` and hence the two normalised parametrisations converge to the
same point of `ℝ⁴`; local injectivity of `thetaP` at that point (`hdiff0`) forces them to agree for
large `n`, contradicting the failure of the conclusion. -/
theorem theta_injective (L : Work.RPA3.LagFamilyAll) (ε : ℝ) (hε : 0 < ε)
    (hdiff0 : ∀ τ ∈ Set.Icc (-1 : ℝ) 2, ∀ x t, Work.RPA3.IsLocDiffeoAt L (τ, ((x, t), (0, 0)))) :
    ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∀ τ ∈ Set.Icc (-1 : ℝ) 2, ∀ x t x' t' (ξ ξ' : ℝ × ℝ), t ∈ Set.Icc 0 (2 * Real.pi) →
        t' ∈ Set.Icc 0 (2 * Real.pi) → ‖ξ‖ < ε' → ‖ξ'‖ < ε' → ∀ k : ℤ,
        Work.RPA3.theta L τ x t ξ = Work.RPA3.Tk k (Work.RPA3.theta L τ x' t' ξ') →
        (x = x' ∧ ξ = ξ' ∧ ∃ m : ℤ, t' = t + 2 * Real.pi * m) := by
  by_contra hcon
  have hfail : ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε → ¬ InjUpToAll L ε' :=
    fun ε' h1 h2 h3 => hcon ⟨ε', h1, h2, h3⟩
  -- a bad configuration for every `n`
  have hwit : ∀ n : ℕ, ∃ (τ : ℝ) (x t x' t' : ℝ) (ξ ξ' : ℝ × ℝ) (k : ℤ),
      τ ∈ Set.Icc (-1 : ℝ) 2 ∧ t ∈ Set.Icc 0 (2 * Real.pi) ∧ t' ∈ Set.Icc 0 (2 * Real.pi) ∧
      ‖ξ‖ < min ε (1 / ((n : ℝ) + 1)) ∧ ‖ξ'‖ < min ε (1 / ((n : ℝ) + 1)) ∧
      theta L τ x t ξ = Tk k (theta L τ x' t' ξ') ∧
      ¬ (x = x' ∧ ξ = ξ' ∧ ∃ m : ℤ, t' = t + 2 * Real.pi * m) := by
    intro n
    have hpos : 0 < min ε (1 / ((n : ℝ) + 1)) := lt_min hε (by positivity)
    have hle : min ε (1 / ((n : ℝ) + 1)) ≤ ε := min_le_left _ _
    by_contra hc
    refine hfail (min ε (1 / ((n : ℝ) + 1))) hpos hle ?_
    intro τ hτ x t x' t' ξ ξ' ht ht' hξ hξ' k heq
    by_contra hconj
    exact hc ⟨τ, x, t, x', t', ξ, ξ', k, hτ, ht, ht', hξ, hξ', heq, hconj⟩
  choose τf xf tf xf' tf' ξf ξf' kf hP using hwit
  -- the two compact boxes and the bounds
  set X : ℝ := max L.X0 0 with hXdef
  have hX0le : L.X0 ≤ X := le_max_left _ _
  have hX0nonneg : 0 ≤ X := le_max_right _ _
  obtain ⟨M, hM⟩ := (theta_coord_bounds L (X := X) (R := ε) hX0nonneg hε.le).1
  set B : ℝ := max X M with hBdef
  have hB0 : 0 ≤ B := le_trans hX0nonneg (le_max_left _ _)
  obtain ⟨M2, hM2⟩ := (theta_coord_bounds L (X := B) (R := ε) hB0 hε.le).2
  set K : ℝ := max (M2 / Real.pi) 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  -- bounds on the `x`-coordinates of the bad configurations
  have hxbound : ∀ n, |xf n| ≤ B ∧ |xf' n| ≤ B := by
    intro n
    obtain ⟨hτn, htn, htn', hξn, hξn', heqn, hnotgood⟩ := hP n
    refine ThInj.bad_x_bound L hX0le hM hτn htn htn'
      (le_of_lt (lt_of_lt_of_le hξn (min_le_left _ _)))
      (le_of_lt (lt_of_lt_of_le hξn' (min_le_left _ _))) heqn ?_
    intro hboth
    exact hnotgood (ThInj.good_of_std L hboth.1 hboth.2 heqn)
  -- bounds on the integers
  have hkbound : ∀ n, |(kf n : ℝ)| ≤ K := by
    intro n
    obtain ⟨hτn, htn, htn', hξn, hξn', heqn, -⟩ := hP n
    refine le_trans (ThInj.bad_k_bound L hM2 hτn htn htn'
      (le_of_lt (lt_of_lt_of_le hξn (min_le_left _ _)))
      (le_of_lt (lt_of_lt_of_le hξn' (min_le_left _ _)))
      (hxbound n).1 (hxbound n).2 heqn) ?_
    exact le_max_left _ _
  -- the compact set of configurations
  let A : ℕ → ℝ × PS := fun n => (τf n, ((xf n, tf n), ξf n))
  let Bs : ℕ → PS := fun n => ((xf' n, tf' n), ξf' n)
  set S : Set (((ℝ × PS) × PS) × ℝ) :=
    ((Set.Icc (-1 : ℝ) 2 ×ˢ ((Set.Icc (-B) B ×ˢ Set.Icc 0 (2 * Real.pi)) ×ˢ
        Metric.closedBall (0 : ℝ × ℝ) ε)) ×ˢ
      ((Set.Icc (-B) B ×ˢ Set.Icc 0 (2 * Real.pi)) ×ˢ Metric.closedBall (0 : ℝ × ℝ) ε)) ×ˢ
      Set.Icc (-K) K with hSdef
  have hScompact : IsCompact S := by
    rw [hSdef]
    exact ((isCompact_Icc.prod ((isCompact_Icc.prod isCompact_Icc).prod
        (isCompact_closedBall (0 : ℝ × ℝ) ε))).prod
      ((isCompact_Icc.prod isCompact_Icc).prod
        (isCompact_closedBall (0 : ℝ × ℝ) ε))).prod isCompact_Icc
  have hmem : ∀ n, ((A n, Bs n), (kf n : ℝ)) ∈ S := by
    intro n
    rw [hSdef]
    obtain ⟨hτn, htn, htn', hξn, hξn', -, -⟩ := hP n
    have hξnle : ‖ξf n‖ ≤ ε := le_of_lt (lt_of_lt_of_le hξn (min_le_left _ _))
    have hξn'le : ‖ξf' n‖ ≤ ε := le_of_lt (lt_of_lt_of_le hξn' (min_le_left _ _))
    refine ⟨⟨⟨hτn, ⟨⟨abs_le.mp (hxbound n).1, htn⟩, ?_⟩⟩,
      ⟨⟨abs_le.mp (hxbound n).2, htn'⟩, ?_⟩⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]; exact hξnle
    · rw [Metric.mem_closedBall, dist_zero_right]; exact hξn'le
    · rw [Set.mem_Icc]; exact abs_le.mp (hkbound n)
  obtain ⟨a, ha, φ, hφmono, hφtend⟩ :=
    IsCompact.tendsto_subseq hScompact
      (x := fun n => ((A n, Bs n), (kf n : ℝ))) hmem
  -- componentwise convergence along the subsequence
  have h1 := hφtend
  rw [nhds_prod_eq] at h1
  have hAB : Tendsto (fun n => (A (φ n), Bs (φ n))) atTop (𝓝 a.1) := by
    simpa only [Function.comp_apply] using h1.fst
  have hkf_tend : Tendsto (fun n => (kf (φ n) : ℝ)) atTop (𝓝 a.2) := by
    simpa only [Function.comp_apply] using h1.snd
  have h2 := hAB
  rw [nhds_prod_eq] at h2
  have hA_tend : Tendsto (fun n => A (φ n)) atTop (𝓝 a.1.1) := h2.fst
  have hBs_tend : Tendsto (fun n => Bs (φ n)) atTop (𝓝 a.1.2) := h2.snd
  have h3 := hA_tend
  rw [nhds_prod_eq] at h3
  have hτ_tend : Tendsto (fun n => τf (φ n)) atTop (𝓝 a.1.1.1) := h3.fst
  have hz_tend : Tendsto (fun n => ((xf (φ n), tf (φ n)), ξf (φ n))) atTop
      (𝓝 a.1.1.2) := h3.snd
  have h4 := hz_tend
  rw [nhds_prod_eq] at h4
  have hxt_tend : Tendsto (fun n => xf (φ n)) atTop (𝓝 a.1.1.2.1.1) := by
    have h5 := h4.fst
    rw [nhds_prod_eq] at h5
    exact h5.fst
  have htt_tend : Tendsto (fun n => tf (φ n)) atTop (𝓝 a.1.1.2.1.2) := by
    have h5 := h4.fst
    rw [nhds_prod_eq] at h5
    exact h5.snd
  have hξt_tend : Tendsto (fun n => ξf (φ n)) atTop (𝓝 a.1.1.2.2) := h4.snd
  have h5' := hBs_tend
  rw [nhds_prod_eq] at h5'
  have hx't_tend : Tendsto (fun n => xf' (φ n)) atTop (𝓝 a.1.2.1.1) := by
    have h6 := h5'.fst
    rw [nhds_prod_eq] at h6
    exact h6.fst
  have ht't_tend : Tendsto (fun n => tf' (φ n)) atTop (𝓝 a.1.2.1.2) := by
    have h6 := h5'.fst
    rw [nhds_prod_eq] at h6
    exact h6.snd
  have hξ't_tend : Tendsto (fun n => ξf' (φ n)) atTop (𝓝 a.1.2.2) := h5'.snd
  -- the first coordinate of the limit point
  have hτs_mem : a.1.1.1 ∈ Set.Icc (-1 : ℝ) 2 := by
    rw [hSdef] at ha
    exact ha.1.1.1
  -- the `ξ`-coordinates vanish in the limit
  have hξs_zero : a.1.1.2.2 = 0 := by
    have hlim0 : Tendsto (fun n => ξf (φ n)) atTop (𝓝 (0 : ℝ × ℝ)) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφmono.tendsto_atTop)
      obtain ⟨-, -, -, hξn, -, -, -⟩ := hP (φ n)
      exact le_of_lt (lt_of_lt_of_le hξn (min_le_right _ _))
    exact tendsto_nhds_unique hξt_tend hlim0
  have hξs'_zero : a.1.2.2 = 0 := by
    have hlim0 : Tendsto (fun n => ξf' (φ n)) atTop (𝓝 (0 : ℝ × ℝ)) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφmono.tendsto_atTop)
      obtain ⟨-, -, -, -, hξn, -, -⟩ := hP (φ n)
      exact le_of_lt (lt_of_lt_of_le hξn (min_le_right _ _))
    exact tendsto_nhds_unique hξ't_tend hlim0
  -- the integers are eventually constant along the subsequence
  obtain ⟨N, hN⟩ := int_tendsto_eventually_const hkf_tend
  set k : ℤ := kf (φ N) with hkdef
  have hk_const : ∀ n ≥ N, kf (φ n) = k := hN
  -- the equality passes to the limit
  have hθ₁ : Tendsto (fun n => theta L (τf (φ n)) (xf (φ n)) (tf (φ n)) (ξf (φ n))) atTop
      (𝓝 (theta L a.1.1.1 a.1.1.2.1.1 a.1.1.2.1.2 a.1.1.2.2)) :=
    ((continuous_thetaZ L).tendsto a.1.1).comp hA_tend
  have hθ₂' : Tendsto (fun n => theta L (τf (φ n)) (xf' (φ n)) (tf' (φ n)) (ξf' (φ n))) atTop
      (𝓝 (theta L a.1.1.1 a.1.2.1.1 a.1.2.1.2 a.1.2.2)) := by
    have hcont2 : Continuous (fun p : (ℝ × PS) × PS => theta L p.1.1 p.2.1.1 p.2.1.2 p.2.2) := by
      have hc : Continuous (fun p : (ℝ × PS) × PS => (p.1.1, p.2)) := by fun_prop
      have h := (continuous_thetaZ L).comp hc
      simpa only [Function.comp_def, thetaZ] using h
    exact (hcont2.tendsto (a.1.1, a.1.2)).comp (hA_tend.prodMk_nhds hBs_tend)
  have hθ₂ : Tendsto (fun n => Tk k (theta L (τf (φ n)) (xf' (φ n)) (tf' (φ n)) (ξf' (φ n))))
      atTop (𝓝 (Tk k (theta L a.1.1.1 a.1.2.1.1 a.1.2.1.2 a.1.2.2))) :=
    ((continuous_Tk k).tendsto _).comp hθ₂'
  have hev : (fun n => theta L (τf (φ n)) (xf (φ n)) (tf (φ n)) (ξf (φ n)))
      =ᶠ[atTop] (fun n => Tk k (theta L (τf (φ n)) (xf' (φ n)) (tf' (φ n)) (ξf' (φ n)))) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    obtain ⟨-, -, -, -, -, heqn, -⟩ := hP (φ n)
    rw [← hk_const n hn]
    exact heqn
  have hlim_eq : theta L a.1.1.1 a.1.1.2.1.1 a.1.1.2.1.2 a.1.1.2.2
      = Tk k (theta L a.1.1.1 a.1.2.1.1 a.1.2.1.2 a.1.2.2) :=
    tendsto_nhds_unique hθ₁ (hθ₂.congr' hev.symm)
  -- at `ξ = 0`, `theta` is `ℓ`
  have hℓ : L.ℓ a.1.1.1 (a.1.1.2.1.1, a.1.1.2.1.2)
      = Tk k (L.ℓ a.1.1.1 (a.1.2.1.1, a.1.2.1.2)) := by
    have h := hlim_eq
    rw [hξs_zero, hξs'_zero] at h
    simp only [← theta_zero]
    exact h
  obtain ⟨hxs_eq, m, hm⟩ :=
    L.inj a.1.1.1 a.1.2.1.1 a.1.2.1.2 a.1.1.2.1.1 a.1.1.2.1.2 k hℓ
  -- comparing the angular coordinates forces `k = m`
  have hkm : k = m := by
    have h1' : L.ℓ a.1.1.1 (a.1.1.2.1.1, a.1.1.2.1.2)
        = Tk m (L.ℓ a.1.1.1 (a.1.2.1.1, a.1.2.1.2)) := by
      rw [hm, ell_per_int, hxs_eq]
    exact ThInj.Tk_int_injective _ (hℓ.symm.trans h1')
  have htk : a.1.2.1.2 + 2 * Real.pi * (k : ℝ) = a.1.1.2.1.2 := by
    rw [hkm]; linarith
  -- the two parametrisations converge to the same point
  have hX_tend : Tendsto (fun n => (τf (φ n), ((xf (φ n), tf (φ n)), ξf (φ n)))) atTop
      (𝓝 (a.1.1.1, ((a.1.1.2.1.1, a.1.1.2.1.2), (0 : ℝ × ℝ)))) := by
    have h2' : Tendsto (fun n => (xf (φ n), tf (φ n))) atTop
        (𝓝 (a.1.1.2.1.1, a.1.1.2.1.2)) := hxt_tend.prodMk_nhds htt_tend
    have h3' : Tendsto (fun n => ((xf (φ n), tf (φ n)), ξf (φ n))) atTop
        (𝓝 ((a.1.1.2.1.1, a.1.1.2.1.2), a.1.1.2.2)) := h2'.prodMk_nhds hξt_tend
    have h4' := hτ_tend.prodMk_nhds h3'
    simpa only [hξs_zero] using h4'
  have hY_tend : Tendsto (fun n =>
      (τf (φ n), ((xf' (φ n), tf' (φ n) + 2 * Real.pi * (k : ℝ)), ξf' (φ n)))) atTop
      (𝓝 (a.1.1.1, ((a.1.1.2.1.1, a.1.1.2.1.2), (0 : ℝ × ℝ)))) := by
    have h2' : Tendsto (fun n => (xf' (φ n), tf' (φ n) + 2 * Real.pi * (k : ℝ))) atTop
        (𝓝 (a.1.2.1.1, a.1.2.1.2 + 2 * Real.pi * (k : ℝ))) :=
      hx't_tend.prodMk_nhds (ht't_tend.add tendsto_const_nhds)
    have h3' : Tendsto (fun n =>
        ((xf' (φ n), tf' (φ n) + 2 * Real.pi * (k : ℝ)), ξf' (φ n))) atTop
        (𝓝 ((a.1.2.1.1, a.1.2.1.2 + 2 * Real.pi * (k : ℝ)), a.1.2.2)) :=
      h2'.prodMk_nhds hξ't_tend
    have h4' := hτ_tend.prodMk_nhds h3'
    simpa only [← hxs_eq, ← htk, ← hξs'_zero] using h4'
  -- local injectivity at the common limit
  obtain ⟨δ, hδpos, hinj⟩ :=
    local_inj_of_isLocDiffeoAt L (a.1.1.1, ((a.1.1.2.1.1, a.1.1.2.1.2), (0 : ℝ × ℝ)))
      (hdiff0 a.1.1.1 hτs_mem a.1.1.2.1.1 a.1.1.2.1.2)
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hX_tend δ hδpos
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hY_tend δ hδpos
  have hNle : N ≤ max N (max N₁ N₂) := le_max_left _ _
  have hN₁le : N₁ ≤ max N (max N₁ N₂) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hN₂le : N₂ ≤ max N (max N₁ N₂) := le_trans (le_max_right _ _) (le_max_right _ _)
  have hdistX : dist (τf (φ (max N (max N₁ N₂))), ((xf (φ (max N (max N₁ N₂))),
      tf (φ (max N (max N₁ N₂)))), ξf (φ (max N (max N₁ N₂)))))
      (a.1.1.1, ((a.1.1.2.1.1, a.1.1.2.1.2), (0 : ℝ × ℝ))) < δ :=
    hN₁ _ hN₁le
  have hdistY : dist (τf (φ (max N (max N₁ N₂))), ((xf' (φ (max N (max N₁ N₂))),
      tf' (φ (max N (max N₁ N₂))) + 2 * Real.pi * (k : ℝ)), ξf' (φ (max N (max N₁ N₂)))))
      (a.1.1.1, ((a.1.1.2.1.1, a.1.1.2.1.2), (0 : ℝ × ℝ))) < δ :=
    hN₂ _ hN₂le
  have hθPeq : thetaP L (τf (φ (max N (max N₁ N₂))),
        ((xf (φ (max N (max N₁ N₂))), tf (φ (max N (max N₁ N₂)))),
          ξf (φ (max N (max N₁ N₂)))))
      = thetaP L (τf (φ (max N (max N₁ N₂))),
        ((xf' (φ (max N (max N₁ N₂))), tf' (φ (max N (max N₁ N₂))) + 2 * Real.pi * (k : ℝ)),
          ξf' (φ (max N (max N₁ N₂))))) := by
    simp only [thetaP, thetaZ]
    congr 1
    rw [theta_per_int, ← hk_const _ hNle]
    exact (hP (φ (max N (max N₁ N₂)))).2.2.2.2.2.1
  have hpt_eq := hinj _ _ hdistX hdistY hθPeq
  have hx_fin : xf (φ (max N (max N₁ N₂))) = xf' (φ (max N (max N₁ N₂))) := by
    simpa using congrArg (fun q : ℝ × PS => q.2.1.1) hpt_eq
  have hξ_fin : ξf (φ (max N (max N₁ N₂))) = ξf' (φ (max N (max N₁ N₂))) := by
    simpa using congrArg (fun q : ℝ × PS => q.2.2) hpt_eq
  have ht_fin : tf (φ (max N (max N₁ N₂)))
      = tf' (φ (max N (max N₁ N₂))) + 2 * Real.pi * (k : ℝ) := by
    simpa using congrArg (fun q : ℝ × PS => q.2.1.2) hpt_eq
  -- contradiction with the failure of the conclusion
  obtain ⟨-, -, -, -, -, -, hnotgood⟩ := hP (φ (max N (max N₁ N₂)))
  exact hnotgood ⟨hx_fin, hξ_fin, ⟨-k, by rw [ht_fin]; push_cast; ring⟩⟩

end Work.RPA3
