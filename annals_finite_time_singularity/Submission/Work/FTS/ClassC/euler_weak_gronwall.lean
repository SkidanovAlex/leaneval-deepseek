/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weak Gronwall bound for the Euler-type chain on `(0, ∞)`

Let `v : ℝ → ℝ` satisfy the integral relation

`v z - v s = ∫ r in s..z, (-(5 + α) / (α * r)) * v r`   for all `0 < s ≤ z`     (E)

i.e. `v` is a (weak) solution of the Euler-type ODE `v' = -β v / r` on `(0,∞)`, where
`β = (5 + α)/α > 0`.  The exact solutions are `v r = C r^{-β}`, so
`|v b| = |v a| (a/b)^β`; the statement below is the (weaker, but sufficient for the paper)
Gronwall consequence `|v b| ≤ |v a| (b/a)^β` for `0 < a ≤ b`.

The proof does not need any a priori regularity of `v`.  The two ingredients are

* `locallyIntegrableOn_of_chain`: the relation (E) at *every* pair `0 < s ≤ z` forces the
  integrand `r ↦ (-(5+α)/(α r)) v r` to be locally integrable on `(0,∞)` (a rigidity argument:
  if it failed at `x`, then (E) would force `v` to be constant on a punctured neighbourhood of
  `x`, whence the integrand is a.e. equal to a continuous function there — a contradiction);
* the *unconditional* integral inequality `|v z| ≤ |v s| + ∫_s^z ((5+α)/(α r)) |v r| dr`
  (if the integrand is not integrable over `s..z` the interval integral is `0` and (E) gives
  `v z = v s`; otherwise it is `intervalIntegral.norm_integral_le_integral_norm`).

Then `|v|` is bounded on `[a,b]` (since `g := ((5+α)/(α r))|v r|` is integrable there), and the
classical Gronwall argument with `Λ := sup_{[a,b]} |v z| / (z/a)^β` gives `Λ ≤ |v a|`, because for
every `z ∈ [a,b]`

`ψ z ≤ (|v a| + Λ ((z/a)^β - 1)) / (z/a)^β = Λ + (|v a| - Λ) / (z/a)^β`,

the estimate `∫_a^z g ≤ Λ ((z/a)^β - 1)` coming from `∫_a^z (β/r)(r/a)^β = (z/a)^β - 1`
(`integral_alpha_div_mul_rpow`).  The absurdity `Λ > |v a|` follows by taking `ε → 0` in the
defining property of the supremum.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.ClassC.locallyIntegrableOn_of_chain
import Submission.Work.FTS.ClassC.integral_alpha_div_mul_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.ClassC

theorem euler_weak_gronwall {α : ℝ} {v : ℝ → ℝ} (hα : 0 < α)
    (hchain1 : ∀ s z : ℝ, 0 < s → s ≤ z →
      v z - v s = ∫ r in s..z, (-(5 + α) / (α * r)) * v r) :
    ∀ a b : ℝ, 0 < a → a ≤ b → |v b| ≤ |v a| * (b / a) ^ ((5 + α) / α) := by
  intro a b ha hab
  have h5a : 0 < 5 + α := by linarith
  set β : ℝ := (5 + α) / α with hβ
  have hβpos : 0 < β := by rw [hβ]; exact div_pos h5a hα
  set F : ℝ → ℝ := fun r => (-(5 + α) / (α * r)) * v r with hF
  set g : ℝ → ℝ := fun r => ((5 + α) / (α * r)) * |v r| with hg
  set φ : ℝ → ℝ := fun z => (z / a) ^ β with hφ
  -- the integrand of the chain is locally integrable on `(0, ∞)`
  have hloc : LocallyIntegrableOn F (Ioi (0 : ℝ)) := by
    change LocallyIntegrableOn (fun r : ℝ => (-(5 + α) / (α * r)) * v r) (Set.Ioi 0)
    exact locallyIntegrableOn_of_chain hα hchain1
  have hFint : IntegrableOn F (Icc a b) :=
    hloc.integrableOn_compact_subset (fun r hr => lt_of_lt_of_le ha hr.1) isCompact_Icc
  have hg_eq : ∀ r ∈ Icc a b, g r = ‖F r‖ := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le ha hr.1
    have hpos : 0 < (5 + α) / (α * r) := div_pos h5a (mul_pos hα hr0)
    simp only [hg, hF]
    rw [Real.norm_eq_abs, abs_mul, neg_div, abs_neg, abs_of_pos hpos]
  have hg_int : IntegrableOn g (Icc a b) :=
    MeasureTheory.IntegrableOn.congr_fun hFint.norm (fun r hr => (hg_eq r hr).symm) measurableSet_Icc
  -- the unconditional integral inequality
  have hbound : ∀ s z : ℝ, 0 < s → s ≤ z → |v z| ≤ |v s| + ∫ r in s..z, g r := by
    intro s z hs hsz
    have hsplit : v z - v s = ∫ r in s..z, F r := hchain1 s z hs hsz
    have h1 : |v z| ≤ |v s| + |∫ r in s..z, F r| := by
      have : v z = v s + ∫ r in s..z, F r := by linarith
      rw [this]; exact abs_add_le _ _
    have h2 : |∫ r in s..z, F r| ≤ ∫ r in s..z, ‖F r‖ := by
      simpa only [Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_integral_norm (f := F) (a := s) (b := z) hsz
    have h3 : ∫ r in s..z, ‖F r‖ = ∫ r in s..z, g r := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hrs : s ≤ r := by
        rw [Set.uIcc_of_le hsz] at hr; exact hr.1
      have hr0 : 0 < r := lt_of_lt_of_le hs hrs
      have hpos : 0 < (5 + α) / (α * r) := div_pos h5a (mul_pos hα hr0)
      simp only [hg, hF, Real.norm_eq_abs, abs_mul, neg_div, abs_neg, abs_of_pos hpos]
    linarith
  -- elementary properties of the weight `φ z = (z / a) ^ β`
  have hφpos : ∀ z : ℝ, 0 < z → 0 < φ z := by
    intro z hz
    rw [hφ]
    exact Real.rpow_pos_of_pos (div_pos hz ha) β
  have hφa : φ a = 1 := by
    simp only [hφ]
    rw [div_self (ne_of_gt ha), Real.one_rpow]
  have hφ1 : ∀ z ∈ Icc a b, 1 ≤ φ z := by
    intro z hz
    rw [hφ]
    change 1 ≤ (z / a) ^ β
    apply Real.one_le_rpow
    · rw [le_div_iff₀ ha]; linarith [hz.1]
    · exact hβpos.le
  have hφmono : ∀ z ∈ Icc a b, φ z ≤ φ b := by
    intro z hz
    rw [hφ]
    change (z / a) ^ β ≤ (b / a) ^ β
    apply Real.rpow_le_rpow
    · exact div_nonneg (le_of_lt (lt_of_lt_of_le ha hz.1)) ha.le
    · rw [div_le_div_iff_of_pos_right ha]; exact hz.2
    · exact hβpos.le
  -- the sup of the weighted ratio
  set ψ : ℝ → ℝ := fun z => |v z| / φ z with hψ
  set S : Set ℝ := ψ '' (Icc a b) with hS
  have hSne : S.Nonempty := ⟨ψ a, a, ⟨le_rfl, hab⟩, rfl⟩
  have hgnn : 0 ≤ᵐ[volume.restrict (Ioc a b)] g := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with r hr
    rw [hg]
    exact mul_nonneg (div_pos h5a (mul_pos hα (lt_trans ha hr.1))).le (abs_nonneg _)
  have hSbdd : BddAbove S := by
    refine ⟨|v a| + ∫ r in a..b, g r, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    have h1 : |v z| ≤ |v a| + ∫ r in a..z, g r := hbound a z ha hz.1
    have hint : IntervalIntegrable g volume a b :=
      ⟨hg_int.mono_set (fun x hx => ⟨le_of_lt hx.1, hx.2⟩),
       hg_int.mono_set (fun x hx => absurd (lt_of_le_of_lt hab hx.1) (not_lt_of_ge hx.2))⟩
    have h2 : ∫ r in a..z, g r ≤ ∫ r in a..b, g r :=
      intervalIntegral.integral_mono_interval le_rfl hz.1 hz.2 hgnn hint
    have hφp : 0 < φ z := hφpos z (lt_of_lt_of_le ha hz.1)
    have h3 : |v z| / φ z ≤ |v z| := by
      rw [div_le_iff₀ hφp]
      calc |v z| = |v z| * 1 := (mul_one _).symm
        _ ≤ |v z| * φ z := mul_le_mul_of_nonneg_left (hφ1 z hz) (abs_nonneg _)
    change ψ z ≤ |v a| + ∫ r in a..b, g r
    rw [hψ]
    change |v z| / φ z ≤ |v a| + ∫ r in a..b, g r
    linarith
  set Λ : ℝ := sSup S with hΛ
  have hΛub : ∀ z ∈ Icc a b, ψ z ≤ Λ := by
    intro z hz
    rw [hΛ]
    exact le_csSup hSbdd ⟨z, hz, rfl⟩
  -- the Gronwall estimate
  have hstep : ∀ z ∈ Icc a b, ψ z ≤ Λ + (|v a| - Λ) / φ z := by
    intro z hz
    obtain ⟨haz, hzb⟩ := hz
    have hφp : 0 < φ z := hφpos z (lt_of_lt_of_le ha haz)
    have h1 : |v z| ≤ |v a| + ∫ r in a..z, g r := hbound a z ha haz
    have hint_z : IntervalIntegrable g volume a z :=
      ⟨hg_int.mono_set (fun x hx => ⟨le_of_lt hx.1, le_trans hx.2 hzb⟩),
       hg_int.mono_set (fun x hx => absurd hx.1 (not_lt_of_ge (le_trans hx.2 haz)))⟩
    have hKcont : ContinuousOn (fun r : ℝ => ((5 + α) / (α * r)) * Λ * (r / a) ^ β)
        (Set.uIcc a z) := by
      have hmemz : ∀ r ∈ Set.uIcc a z, 0 < r := by
        intro r hr
        rw [Set.uIcc_of_le haz] at hr
        exact lt_of_lt_of_le ha hr.1
      have h1' : ContinuousOn (fun r : ℝ => (5 + α) / (α * r)) (Set.uIcc a z) :=
        ContinuousOn.div continuousOn_const (continuousOn_const.mul continuousOn_id)
          (fun r hr => ne_of_gt (mul_pos hα (hmemz r hr)))
      have h2' : ContinuousOn (fun r : ℝ => (r / a) ^ β) (Set.uIcc a z) :=
        ContinuousOn.rpow_const
          (ContinuousOn.div continuousOn_id continuousOn_const (fun r _ => ne_of_gt ha))
          (fun r hr => Or.inl (ne_of_gt (div_pos (hmemz r hr) ha)))
      have h3' : ContinuousOn (fun r : ℝ => (5 + α) / (α * r) * Λ) (Set.uIcc a z) :=
        h1'.mul continuousOn_const
      change ContinuousOn
        ((fun r : ℝ => (5 + α) / (α * r) * Λ) * (fun r : ℝ => (r / a) ^ β)) (Set.uIcc a z)
      exact h3'.mul h2'
    have hcomp : ∫ r in a..z, g r ≤ ∫ r in a..z, ((5 + α) / (α * r)) * Λ * (r / a) ^ β := by
      apply intervalIntegral.integral_mono_on haz hint_z hKcont.intervalIntegrable
      intro r hr
      have hr0 : 0 < r := lt_of_lt_of_le ha hr.1
      have hφr : 0 < φ r := hφpos r hr0
      have hψr : ψ r ≤ Λ := hΛub r ⟨hr.1, le_trans hr.2 hzb⟩
      have hvr : |v r| = ψ r * φ r := by rw [hψ]; field_simp
      have hc0 : 0 ≤ (5 + α) / (α * r) := (div_pos h5a (mul_pos hα hr0)).le
      change ((5 + α) / (α * r)) * |v r| ≤ ((5 + α) / (α * r)) * Λ * φ r
      rw [hvr]
      calc ((5 + α) / (α * r)) * (ψ r * φ r)
          ≤ ((5 + α) / (α * r)) * (Λ * φ r) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hψr hφr.le) hc0
        _ = ((5 + α) / (α * r)) * Λ * φ r := by ring
    have hKval : ∫ r in a..z, ((5 + α) / (α * r)) * Λ * (r / a) ^ β = Λ * (φ z - 1) := by
      have hc : ∫ r in a..z, ((5 + α) / (α * r)) * (r / a) ^ β = (z / a) ^ β - 1 := by
        have h0 := integral_alpha_div_mul_rpow hα ha haz
        rw [hβ]
        exact h0
      have h1 : ∫ r in a..z, ((5 + α) / (α * r)) * Λ * (r / a) ^ β
          = ∫ r in a..z, Λ * (((5 + α) / (α * r)) * (r / a) ^ β) :=
        intervalIntegral.integral_congr (fun r _ => by ring)
      rw [h1, intervalIntegral.integral_const_mul, hc]
    have h2 : ∫ r in a..z, g r ≤ Λ * (φ z - 1) := hcomp.trans_eq hKval
    have h3 : |v z| ≤ |v a| + Λ * (φ z - 1) := by linarith
    rw [hψ]
    change |v z| / φ z ≤ Λ + (|v a| - Λ) / φ z
    rw [div_le_iff₀ hφp]
    have hexp : (Λ + (|v a| - Λ) / φ z) * φ z = Λ * φ z + (|v a| - Λ) := by
      field_simp
    rw [hexp]
    linarith
  -- the sup is at most `|v a|`, by the `ε → 0` characterization of `sSup`
  have hΛle : Λ ≤ |v a| := by
    have hcnonneg : 0 ≤ |v a| - Λ := by
      by_contra hneg
      have hneg' : |v a| - Λ < 0 := not_le.mp hneg
      have hφbp : 0 < φ b := hφpos b (lt_of_lt_of_le ha hab)
      have hd : (|v a| - Λ) / φ b < 0 := div_neg_of_neg_of_pos hneg' hφbp
      have key : ∀ ε : ℝ, 0 < ε → -ε < (|v a| - Λ) / φ b := by
        intro ε hε
        have hlt : Λ - ε < sSup S := by rw [← hΛ]; linarith
        obtain ⟨y, hyS, hygt⟩ := (lt_csSup_iff hSbdd hSne).mp hlt
        obtain ⟨z, hz, rfl⟩ := hyS
        have hzφp : 0 < φ z := hφpos z (lt_of_lt_of_le ha hz.1)
        have h1 : -ε < (|v a| - Λ) / φ z := by linarith [hstep z hz]
        have h2 : (|v a| - Λ) / φ z ≤ (|v a| - Λ) / φ b := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonpos_left
            (by simpa [one_div] using one_div_le_one_div_of_le hzφp (hφmono z hz)) hneg'.le
        linarith
      have hd2 : 0 ≤ (|v a| - Λ) / φ b :=
        le_of_forall_pos_lt_add (fun ε hε => by linarith [key ε hε])
      exact absurd hd2 (not_le.mpr hd)
    linarith
  -- conclusion
  have hb_mem : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hψb : ψ b ≤ |v a| := le_trans (hΛub b hb_mem) hΛle
  have hφbp : 0 < φ b := hφpos b (lt_of_lt_of_le ha hab)
  change |v b| / φ b ≤ |v a| at hψb
  rw [div_le_iff₀ hφbp] at hψb
  have hφbv : φ b = (b / a) ^ β := rfl
  rw [hφbv] at hψb
  exact hψb

end Work.FTS.ClassC
