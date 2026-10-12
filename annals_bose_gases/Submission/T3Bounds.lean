import ChallengeDeps
import Mathlib.RingTheory.TotallySplit
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Order.Interval.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Order.Star.Real
import Submission.RegChild
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Maximum-principle bounds for the canonical scattering profile (Layer 3, T3)

For a radial weak scattering solution `w` of a **non-negative radial**
potential `v` (`tsupport v ⊆ ball 0 R`), the canonical profile
`U(r) := canonicalProfile v w R r` of `ProfileFormula` satisfies the a.e.
Carathéodory equation `U'' = (radialProfile v/2)·(U − id)` a.e. on `(0,R)`
(`Submission.RegChild.canonicalProfile_reg`), with `U 0 = 0`,
`U → 0` at `0⁺`, differentiability on `(0,R)`, `deriv U` absolutely
continuous on compact subintervals, and `HasDerivAt U 0 R`
(`ProfileFormula.canonicalProfile_hasDerivAt_R`).

This module runs the classical maximum-principle / comparison sandwich
(see `ClassicalScat.nonneg_of_concave_neg` — there for `C²` profiles) in the
**a.e.** form made available by `ProfileConvex`:

  (U ≥ 0)   the function `f := U` satisfies `f 0 = 0`, is continuous on
            `[0,R]`, differentiable on `(0,R)`, and is *concave wherever it is
            negative* (`f'' = (vprof/2)(f − id) ≤ 0` a.e. on `{f < 0}`, using
            `v ≥ 0`); a concave function negative somewhere on `(0,R)` would
            force a negative minimum in the interior or at `R`, contradicting
            the endpoint data.
  (U ≤ id)  the function `f := id − U` satisfies `f 0 = 0`,
            `HasDerivAt f 1 R`, and is *concave wherever negative*
            (`f'' = −U'' = (vprof/2)·f ≤ 0` a.e. on `{f < 0}`).

The generic a.e. sandwich is `ae_nonneg_of_concave_neg`; both bounds follow.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian Set
open scoped ContDiff Topology Real Interval

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- A function which is differentiable on `(l,r)`, with derivative antitone
there, is concave on `(l,r)`. -/
lemma concaveOn_Ioo_of_antitone_deriv {f : ℝ → ℝ} {l r : ℝ}
    (hfdiff : ∀ x : ℝ, x ∈ Ioo l r → DifferentiableAt ℝ f x)
    (h_anti : AntitoneOn (deriv f) (Ioo l r)) : ConcaveOn ℝ (Ioo l r) f := by
  have hint : AntitoneOn (deriv f) (interior (Ioo l r)) := by
    simpa [interior_Ioo] using h_anti
  refine AntitoneOn.concaveOn_of_deriv (D := Ioo l r) (convex_Ioo l r) ?_ ?_ hint
  · intro x hx
    exact (hfdiff x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioo]
    intro x hx
    exact (hfdiff x hx).differentiableWithinAt

/-- `{x | x ∈ Ioo a b ∧ f x < 0}` is open when `f` is continuous on `Ioo a b`. -/
lemma isOpen_Ioo_inter_lt {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Ioo a b)) :
    IsOpen (Ioo a b ∩ {x | f x < 0}) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases hx with ⟨hxab, hxlt⟩
  have hxcont : ContinuousAt f x := ContinuousOn.continuousAt hf (Ioo_mem_nhds hxab.1 hxab.2)
  have hn : {y : ℝ | f y < 0} ∈ 𝓝 x := by
    exact hxcont.preimage_mem_nhds ((isOpen_lt continuous_id continuous_const).mem_nhds hxlt)
  exact Filter.mem_of_superset (inter_mem (Ioo_mem_nhds hxab.1 hxab.2) hn) (by intro y hy; exact hy)

/-- If `deriv f` is absolutely continuous on `uIcc a b`, its a.e. second
derivative is `q`, and `q ≤ 0` pointwise on the open interval `(a,b)`, then
`deriv f` is antitone on `uIcc a b` (endpoints are negligible). -/
lemma antitoneOn_deriv_of_ae_second_nonpos_of_interior {f q : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hac : AbsolutelyContinuousOnInterval (deriv f) a b)
    (hsecond : ∀ᵐ x : ℝ, x ∈ Set.uIcc a b → HasDerivAt (deriv f) (q x) x)
    (hq : ∀ x : ℝ, a < x → x < b → q x ≤ 0) :
    AntitoneOn (deriv f) (Set.uIcc a b) := by
  refine antitoneOn_deriv_of_ae_second_nonpos hac hsecond ?_
  rw [MeasureTheory.ae_iff]
  have hsub : {x : ℝ | ¬(x ∈ Set.uIcc a b → q x ≤ 0)} ⊆ {a, b} := by
    intro x hx
    have hxmem : x ∈ Set.uIcc a b := by
      by_contra hn
      exact hx (fun hmem => False.elim (hn hmem))
    have hqpos : 0 < q x := by
      by_contra hnq
      have hle : q x ≤ 0 := le_of_not_gt hnq
      exact hx (fun _ => hle)
    by_cases hxa : x = a
    · simp [hxa]
    · by_cases hxb : x = b
      · simp [hxb]
      · have hxab : x ∈ Set.Icc a b := by
          rw [uIcc_of_le hab] at hxmem
          exact hxmem
        have hxa' : a < x := lt_of_le_of_ne hxab.1 (Ne.symm hxa)
        have hxb' : x < b := lt_of_le_of_ne hxab.2 hxb
        exact False.elim (not_lt_of_ge (hq x hxa' hxb') hqpos)
  have hfinite : (volume : Measure ℝ) ({a, b} : Set ℝ) = 0 := by
    exact (Set.countable_insert.mpr (Set.countable_singleton b)).measure_zero (volume : Measure ℝ)
  exact measure_mono_null hsub hfinite

/-- **Generic a.e. sandwich.**  `f` continuous on `[0,R]` with `f 0 = 0`,
`f` differentiable on `(0,R)`, `deriv f` absolutely continuous on compact
subintervals, a.e. second derivative `q` (with `q ≤ 0` wherever `f < 0`), and
`HasDerivAt f c R` for some `c ≥ 0`, then `0 ≤ f` on `(0,R)`. -/
lemma ae_nonneg_of_concave_neg {f q : ℝ → ℝ} {R c : ℝ} (hR : 0 < R) (hc0 : 0 ≤ c)
    (hf0 : f 0 = 0)
    (hfcont : ContinuousOn f (Icc (0 : ℝ) R))
    (hfdiff : ∀ x : ℝ, x ∈ Ioo (0 : ℝ) R → DifferentiableAt ℝ f x)
    (hac : ∀ ⦃a b : ℝ⦄, 0 < a → a ≤ b → b ≤ R →
      AbsolutelyContinuousOnInterval (deriv f) a b)
    (hsecond : ∀ ⦃a b : ℝ⦄, 0 < a → a ≤ b → b ≤ R → ∀ᵐ x : ℝ, x ∈ Set.uIcc a b →
      HasDerivAt (deriv f) (q x) x)
    (hq : ∀ x : ℝ, x ∈ Ioo (0 : ℝ) R → f x < 0 → q x ≤ 0)
    (hfderR : HasDerivAt f c R) :
    ∀ r : ℝ, r ∈ Ioo (0 : ℝ) R → 0 ≤ f r := by
  have hfcont_open : ContinuousOn f (Ioo (0 : ℝ) R) := by
    refine continuousOn_of_forall_continuousAt ?_
    intro y hy
    exact (hfdiff y hy).continuousAt
  intro x hx
  by_contra hxneg
  have hxneg' : f x < 0 := lt_of_not_ge hxneg
  have hxcc : x ∈ Icc (0 : ℝ) R := Ioo_subset_Icc_self hx
  have hS : IsCompact (Icc (0 : ℝ) R) := isCompact_Icc
  have hSne : (Icc (0 : ℝ) R).Nonempty := ⟨0, by simp [hR.le]⟩
  rcases (hS.exists_isMinOn hSne hfcont) with ⟨xm, hxm, hxmisMin⟩
  have hnegxm : f xm < 0 := lt_of_le_of_lt (hxmisMin hxcc) hxneg'
  let S0 : Set ℝ := Icc (0 : ℝ) R ∩ {x | f x = f xm}
  have hS0_nonempty : S0.Nonempty := ⟨xm, ⟨hxm, rfl⟩⟩
  have hS0_compact : IsCompact S0 := by
    have hclosed : IsClosed S0 := by
      dsimp [S0]
      exact ContinuousOn.preimage_isClosed_of_isClosed hfcont isClosed_Icc isClosed_singleton
    exact IsCompact.of_isClosed_subset isCompact_Icc hclosed (by intro x hx; exact hx.1)
  rcases hS0_compact.exists_isLeast hS0_nonempty with ⟨x1, hx1least⟩
  have hx1S0 : x1 ∈ S0 := hx1least.1
  have hx1le : ∀ y : ℝ, y ∈ S0 → x1 ≤ y := by
    intro y hy
    exact hx1least.2 hy
  have hx1cc : x1 ∈ Icc (0 : ℝ) R := hx1S0.1
  have hx1eqm : f x1 = f xm := hx1S0.2
  have hx1neg : f x1 < 0 := by simpa [hx1eqm] using hnegxm
  have hx10 : 0 < x1 := by
    have : x1 ≠ 0 := by
      intro hz
      have : f 0 = f xm := by simpa [hz] using hx1eqm
      linarith [hf0]
    exact lt_of_le_of_ne hx1cc.1 (Ne.symm this)
  by_cases hx1eqR : x1 = R
  · -- component touching R : excluded by HasDerivAt f 0 R
    have hnegR : f R < 0 := by simpa [hx1eqR] using hx1neg
    have hcontR : ContinuousAt f R := hfderR.differentiableAt.continuousAt
    have hUR : {x : ℝ | f x < 0} ∈ 𝓝 R := by
      exact hcontR.preimage_mem_nhds ((isOpen_lt continuous_id continuous_const).mem_nhds hnegR)
    rcases (Filter.Eventually.exists_Ioo_subset (a := R) hUR) with ⟨a, b, hab, hsubneg⟩
    have haR : a < R := (mem_Ioo.mp hab).1
    have hRb : R < b := (mem_Ioo.mp hab).2
    let δ : ℝ := min ((R - a) / 2) (R / 2)
    have hδpos : 0 < δ := by
      dsimp [δ]
      exact lt_min (div_pos (sub_pos.mpr haR) (by norm_num)) (div_pos hR (by norm_num))
    have hδa : δ ≤ (R - a) / 2 := min_le_left _ _
    have hδR : δ ≤ R / 2 := min_le_right _ _
    let D : Set ℝ := Icc (R - δ) R
    have hD_int : interior D = Ioo (R - δ) R := by simp [D]
    have hRD : R ∈ D := by
      dsimp [D]
      constructor <;> linarith [hδpos]
    have hD0 : 0 < R - δ := by linarith [hR, hδR]
    have hnegD : ∀ x : ℝ, x ∈ D → f x < 0 := by
      intro x hx
      have h2 : (R - a) / 2 ≤ R - a :=
        le_of_lt (half_lt_self (sub_pos.mpr haR))
      have hxa : a < x := by linarith [hx.1]
      have hxb : x < b := lt_of_le_of_lt hx.2 hRb
      exact hsubneg ⟨hxa, hxb⟩
    have hx0D : ∀ x : ℝ, x ∈ D → 0 < x := by
      intro x hx
      have hxpos : 0 ≤ R - δ := by linarith [hR, hδR]
      linarith [hx.1]
    have hanti : AntitoneOn (deriv f) D := by
      dsimp [D]
      have hanti_u : AntitoneOn (deriv f) (Set.uIcc (R - δ) R) := by
        exact antitoneOn_deriv_of_ae_second_nonpos_of_interior (f := f) (q := q)
          (a := R - δ) (b := R) (by linarith [hδpos])
          (hac hD0 (by linarith [hδpos]) (le_rfl))
          (hsecond hD0 (by linarith [hδpos]) (le_rfl))
          (fun t ht1 ht2 =>
            hq t ⟨hx0D t ⟨ht1.le, ht2.le⟩, ht2⟩ (hnegD t ⟨ht1.le, ht2.le⟩))
      rwa [← Set.uIcc_of_le (by linarith [hδpos])]
    have hf'_nonneg : ∀ x : ℝ, x ∈ interior D → 0 ≤ deriv f x := by
      intro x hx
      have hxD : x ∈ D := interior_subset hx
      by_cases hxeqR : x = R
      · subst x
        rw [hfderR.deriv]
        exact hc0
      · have hxleR : x ≤ R := hxD.2
        have hmain := hanti hxD hRD hxleR
        have hderR : deriv f R = c := hfderR.deriv
        linarith
    have hfcontD : ContinuousOn f D := by
      refine continuousOn_of_forall_continuousAt ?_
      intro y hy
      by_cases hyR : y = R
      · subst y
        exact hfderR.differentiableAt.continuousAt
      · have hyR' : y < R := lt_of_le_of_ne hy.2 hyR
        exact (hfdiff y ⟨hx0D y hy, hyR'⟩).continuousAt
    have hfdiffD : DifferentiableOn ℝ f (interior D) := by
      rw [hD_int]
      intro y hy
      have hy0 : 0 < y := hx0D y ⟨(mem_Ioo.mp hy).1.le, (mem_Ioo.mp hy).2.le⟩
      exact (hfdiff y ⟨hy0, (mem_Ioo.mp hy).2⟩).differentiableWithinAt
    have hmono : MonotoneOn f D := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc (R - δ) R) hfcontD hfdiffD ?_
      intro x hx
      exact hf'_nonneg x hx
    let y0 : ℝ := R - δ / 2
    have hy0D : y0 ∈ D := by
      dsimp [D, y0]
      constructor <;> linarith
    have hy0leR : y0 ≤ R := by dsimp [y0]; linarith
    have hmono_le : f y0 ≤ f R := hmono hy0D hRD hy0leR
    have hy0eq : f y0 = f xm := by
      have h1 : f xm ≤ f y0 := by
        apply hxmisMin
        dsimp [y0]
        constructor <;> linarith
      have h2 : f y0 ≤ f R := hmono_le
      have h3 : f R = f xm := by
        rw [← hx1eqR]
        exact hx1eqm
      linarith
    have hy0S0 : y0 ∈ S0 := by
      refine ⟨?_, ?_⟩
      · dsimp [y0]
        constructor <;> linarith
      · exact hy0eq
    have hx1le_y0 : x1 ≤ y0 := hx1le y0 hy0S0
    have hy0ltx1 : y0 < x1 := by
      rw [hx1eqR]
      dsimp [y0]
      linarith [hδpos]
    linarith
  · -- x1 interior : concavity on a component of {f < 0}
    have hx1ltR : x1 < R := lt_of_le_of_ne hx1cc.2 hx1eqR
    have hx1int : x1 ∈ Ioo (0 : ℝ) R := ⟨hx10, hx1ltR⟩
    let U : Set ℝ := Ioo (0 : ℝ) R ∩ {x | f x < 0}
    have hU : IsOpen U := isOpen_Ioo_inter_lt hfcont_open
    have hx1U : x1 ∈ U := ⟨hx1int, hx1neg⟩
    have hUnhds : U ∈ 𝓝 x1 := hU.mem_nhds hx1U
    rcases (Filter.Eventually.exists_Ioo_subset (a := x1) hUnhds) with ⟨l, r, hlr, hsub⟩
    have hlx1 : l < x1 := (mem_Ioo.mp hlr).1
    have hx1r : x1 < r := (mem_Ioo.mp hlr).2
    have hprop : ∀ x : ℝ, x ∈ Ioo l r → x ∈ Ioo (0 : ℝ) R ∧ f x < 0 := hsub
    have hl0 : 0 ≤ l := by
      by_contra hnot
      have hneg : l < 0 := lt_of_not_ge hnot
      have hmid : l < l / 2 := by linarith
      have hmidr : l / 2 < r := by linarith
      have hpos : 0 < l / 2 := (hprop (l / 2) ⟨hmid, hmidr⟩).1.1
      linarith
    have hrR : r ≤ R := by
      by_contra hnot
      have hRr : R < r := lt_of_not_ge hnot
      have h1 : l < (R + r) / 2 := by
        have : R < (R + r) / 2 := by linarith
        linarith [hlx1, hx1ltR]
      have h2 : (R + r) / 2 < r := by linarith
      have hltR : (R + r) / 2 < R := (hprop ((R + r) / 2) ⟨h1, h2⟩).1.2
      linarith
    let l₁ : ℝ := (l + x1) / 2
    have hl₁l : l < l₁ := by
      dsimp [l₁]
      linarith
    have hl₁pos : 0 < l₁ := by
      dsimp [l₁]
      have hsumpos : 0 < l + x1 := by linarith
      exact div_pos hsumpos (by norm_num)
    have hl₁x1 : l₁ < x1 := by
      dsimp [l₁]
      linarith
    have hl₁r : l₁ < r := lt_trans hl₁x1 hx1r
    have hprop₁ : ∀ x : ℝ, x ∈ Ioo l₁ r → x ∈ Ioo (0 : ℝ) R ∧ f x < 0 := by
      intro x hx
      exact hprop x ⟨lt_trans hl₁l hx.1, hx.2⟩
    have hanti_lr : AntitoneOn (deriv f) (Ioo l₁ r) := by
      intro x hx y hy hxy
      have hxpos : 0 < x := lt_trans hl₁pos hx.1
      have hyR : y ≤ R := le_of_lt (lt_of_lt_of_le hy.2 hrR)
      have hantxy : AntitoneOn (deriv f) (Set.uIcc x y) := by
        refine antitoneOn_deriv_of_ae_second_nonpos_of_interior (a := x) (b := y) hxy
          (hac hxpos hxy hyR) (hsecond hxpos hxy hyR) ?_
        intro t ht1 ht2
        have htI : t ∈ Ioo l₁ r := ⟨lt_trans hx.1 ht1, lt_trans ht2 hy.2⟩
        exact hq t (hprop₁ t htI).1 (hprop₁ t htI).2
      exact hantxy Set.left_mem_uIcc Set.right_mem_uIcc hxy
    have hconc : ConcaveOn ℝ (Ioo l₁ r) f := by
      refine concaveOn_Ioo_of_antitone_deriv (l := l₁) (r := r) ?_ hanti_lr
      intro t ht
      exact hfdiff t (hprop₁ t ht).1
    let p : ℝ := (l₁ + x1) / 2
    let q : ℝ := (x1 + r) / 2
    have hp : p ∈ Ioo l₁ r := by
      dsimp [p]
      constructor <;> linarith
    have hq : q ∈ Ioo l₁ r := by
      dsimp [q]
      constructor <;> linarith
    have hpx1 : p < x1 := by dsimp [p]; linarith
    have hx1q : x1 < q := by dsimp [q]; linarith
    have hminI : ∀ y : ℝ, y ∈ Ioo l₁ r → f x1 ≤ f y := by
      intro y hy
      have hycc : y ∈ Icc (0 : ℝ) R := Ioo_subset_Icc_self (hprop₁ y hy).1
      have : f xm ≤ f y := hxmisMin hycc
      simpa [hx1eqm] using this
    have hp_eq : f p = f x1 := by
      have hpq : p < q := lt_trans hpx1 hx1q
      have hqp_ne : q - p ≠ 0 := by linarith
      let a : ℝ := (q - x1) / (q - p)
      let b : ℝ := (x1 - p) / (q - p)
      have ha0 : 0 ≤ a := by
        dsimp [a]
        exact div_nonneg (sub_nonneg.mpr hx1q.le) (sub_nonneg.mpr hpq.le)
      have hb0 : 0 ≤ b := by
        dsimp [b]
        exact div_nonneg (sub_nonneg.mpr hpx1.le) (sub_nonneg.mpr hpq.le)
      have hsum : a + b = 1 := by
        dsimp [a, b]
        field_simp [hqp_ne]
        ring
      have hcombo : a * p + b * q = x1 := by
        dsimp [a, b]
        field_simp [hqp_ne]
        ring
      have hm1 : f x1 ≤ f p := hminI p hp
      have hm2 : f x1 ≤ f q := hminI q hq
      have hineq := hconc.2 hp hq ha0 hb0 hsum
      simp only [smul_eq_mul] at hineq
      rw [hcombo] at hineq
      have hlo : f x1 ≤ a * f p + b * f q := by
        calc
          f x1 = (a + b) * f x1 := by rw [hsum, one_mul]
          _ = a * f x1 + b * f x1 := by ring
          _ ≤ a * f p + b * f q := add_le_add (mul_le_mul_of_nonneg_left hm1 ha0) (mul_le_mul_of_nonneg_left hm2 hb0)
      have heq : a * f p + b * f q = f x1 := le_antisymm hineq hlo
      have hA : a * (f p - f x1) + b * (f q - f x1) = 0 := by
        calc
          a * (f p - f x1) + b * (f q - f x1) = (a * f p + b * f q) - (a * f x1 + b * f x1) := by ring
          _ = f x1 - f x1 := by
            rw [heq]
            rw [← add_mul, hsum, one_mul]
          _ = 0 := by ring
      have hA1 : 0 ≤ a * (f p - f x1) := mul_nonneg ha0 (sub_nonneg.mpr hm1)
      have hB1 : 0 ≤ b * (f q - f x1) := mul_nonneg hb0 (sub_nonneg.mpr hm2)
      have hAz : a * (f p - f x1) = 0 := by
        by_contra hz
        have hAzpos : 0 < a * (f p - f x1) := lt_of_le_of_ne hA1 (Ne.symm hz)
        have : 0 < a * (f p - f x1) + b * (f q - f x1) := lt_of_lt_of_le hAzpos (le_add_of_nonneg_right hB1)
        linarith
      have hapos : 0 < a := by
        dsimp [a]
        exact div_pos (sub_pos.mpr hx1q) (sub_pos.mpr hpq)
      exact sub_eq_zero.mp ((mul_eq_zero.mp hAz).resolve_left hapos.ne')
    have hpS0 : p ∈ S0 := by
      refine ⟨?_, ?_⟩
      · exact Ioo_subset_Icc_self (hprop₁ p hp).1
      · change f p = f xm
        rw [hp_eq]
        exact hx1eqm
    have hx1le_p : x1 ≤ p := hx1le p hpS0
    linarith


-- ============================================================
-- PLACEHOLDER: to be replaced by import of Submission.RegChild
-- ============================================================
/-- AC is unchanged when two functions agree on the interval. -/
lemma absolutelyContinuousOnInterval_congr {f g : ℝ → ℝ} {a b : ℝ}
    (hfg : ∀ x : ℝ, x ∈ Set.uIcc a b → f x = g x)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  rcases hg ε hε with ⟨δ, hδ, hgδ⟩
  refine ⟨δ, hδ, ?_⟩
  intro E hE hlen
  have hsum : (∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2)) < ε := hgδ E hE hlen
  -- all endpoints are in uIcc a b (from hE ∈ disjWithin a b)
  have hpts : ∀ i : ℕ, i < E.1 → (E.2 i).1 ∈ Set.uIcc a b ∧ (E.2 i).2 ∈ Set.uIcc a b := by
    intro i hi
    exact hE.1 i (Finset.mem_range.mpr hi)
  have hEq : (∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2)) =
      (∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi' : i < E.1 := by simpa using (Finset.mem_range.mp hi)
    rcases hpts i hi' with ⟨hp1, hp2⟩
    rw [hfg (E.2 i).1 hp1, hfg (E.2 i).2 hp2]
  rwa [hEq]

/-- A constant function is absolutely continuous. -/
lemma absolutelyContinuousOnInterval_const (c : ℝ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro E hE hlen
  simp [hε]

/-- If `g` is AC, then so is `c − g`. -/
lemma absolutelyContinuousOnInterval_sub_const_left {g : ℝ → ℝ} {a b c : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun x => c - g x) a b := by
  have hneg : AbsolutelyContinuousOnInterval (fun x => -g x) a b := AbsolutelyContinuousOnInterval.neg hg
  have hadd : AbsolutelyContinuousOnInterval (fun x => -g x + c) a b :=
    AbsolutelyContinuousOnInterval.add hneg (absolutelyContinuousOnInterval_const c a b)
  refine absolutelyContinuousOnInterval_congr ?_ hadd
  intro x hx
  ring


/-- `r ↦ r − U r` has derivative `1 − v` at `x` when `U` has derivative `v`. -/
lemma hasDerivAt_id_sub {U : ℝ → ℝ} {x v : ℝ} (hU : HasDerivAt U v x) :
    HasDerivAt (fun r : ℝ => r - U r) (1 - v) x := by
  have h' : HasDerivAt (id - U) (1 - v) x := by
    simpa using (hasDerivAt_id x).sub hU
  convert h' using 1
  funext r
  simp

/-- For a function `U` differentiable at `x`, the derivative of
`r ↦ r − U r` at `x` is `1 − deriv U x`. -/
lemma deriv_id_sub {U : ℝ → ℝ} {x : ℝ} (hU : DifferentiableAt ℝ U x) :
    deriv (fun r : ℝ => r - U r) x = 1 - deriv U x := by
  have h : HasDerivAt (fun r : ℝ => r - U r) (1 - deriv U x) x :=
    hasDerivAt_id_sub hU.hasDerivAt
  exact h.deriv

/-- **Lower bound** `0 ≤ canonicalProfile v w R r` for `0 < r < R`. -/
theorem canonicalProfile_nonneg {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) :
    ∀ r : ℝ, 0 < r → r < R → 0 ≤ canonicalProfile v w R r := by
  let U : ℝ → ℝ := canonicalProfile v w R
  let q : ℝ → ℝ := fun x => (radialProfile v x / 2) * (U x - x)
  have hreg := canonicalProfile_reg hR hvrad hv_supp hrad hw
  rcases hreg with ⟨hU0, hUcont0, hUdiff0, hUac0, hUsecond0⟩
  have hU0' : U 0 = 0 := by simpa [U] using hU0
  have hUcont : ContinuousOn U (Icc (0 : ℝ) R) := by simpa [U] using hUcont0
  have hUdiff : ∀ x : ℝ, x ∈ Ioo (0 : ℝ) R → DifferentiableAt ℝ U x := by
    intro x hx
    simpa [U] using hUdiff0 x hx.1 hx.2
  have hUac : ∀ ⦃a b : ℝ⦄, 0 < a → a ≤ b → b ≤ R →
      AbsolutelyContinuousOnInterval (deriv U) a b := by
    intro a b ha hab hbR
    simpa [U] using hUac0 ha hab hbR
  have hUsecond : ∀ ⦃a b : ℝ⦄, 0 < a → a ≤ b → b ≤ R → ∀ᵐ x : ℝ, x ∈ Set.uIcc a b →
      HasDerivAt (deriv U) (q x) x := by
    intro a b ha hab hbR
    filter_upwards [hUsecond0 ha hab hbR] with x hx hmem
    dsimp [q, U]
    exact hx hmem
  have hvprof : ∀ x : ℝ, 0 ≤ radialProfile v x := by
    intro x
    dsimp [radialProfile]
    exact hv_nonneg (x • radU0)
  have hq : ∀ x : ℝ, x ∈ Ioo (0 : ℝ) R → U x < 0 → q x ≤ 0 := by
    intro x hx hneg
    dsimp [q]
    have hsub : U x - x < 0 := sub_neg.mpr (lt_of_le_of_lt hneg.le hx.1)
    exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg (hvprof x) (by norm_num)) hsub.le
  have hderR : HasDerivAt U 0 R := by
    simpa [U] using canonicalProfile_hasDerivAt_R hR hvrad hv_supp hrad hw
  have hnonneg := ae_nonneg_of_concave_neg (f := U) (q := q) (c := 0) hR (by norm_num)
    hU0' hUcont hUdiff hUac hUsecond hq hderR
  intro r hr0 hrR
  have hUr := hnonneg r ⟨hr0, hrR⟩
  simpa [U] using hUr

/-- **Upper bound** `canonicalProfile v w R r ≤ r` for `0 < r < R`. -/
theorem canonicalProfile_le_r {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) :
    ∀ r : ℝ, 0 < r → r < R → canonicalProfile v w R r ≤ r := by
  let U : ℝ → ℝ := canonicalProfile v w R
  let f : ℝ → ℝ := fun x => x - U x
  let q : ℝ → ℝ := fun x => (radialProfile v x / 2) * (x - U x)
  have hreg := canonicalProfile_reg hR hvrad hv_supp hrad hw
  rcases hreg with ⟨hU0, hUcont0, hUdiff0, hUac0, hUsecond0⟩
  have hU0' : U 0 = 0 := by simpa [U] using hU0
  have hUcont : ContinuousOn U (Icc (0 : ℝ) R) := by simpa [U] using hUcont0
  have hUdiff : ∀ x : ℝ, x ∈ Ioo (0 : ℝ) R → DifferentiableAt ℝ U x := by
    intro x hx
    simpa [U] using hUdiff0 x hx.1 hx.2
  have hUac : ∀ ⦃a b : ℝ⦄, 0 < a → a ≤ b → b ≤ R →
      AbsolutelyContinuousOnInterval (deriv U) a b := by
    intro a b ha hab hbR
    simpa [U] using hUac0 ha hab hbR
  have hUsecond : ∀ ⦃a b : ℝ⦄, 0 < a → a ≤ b → b ≤ R → ∀ᵐ x : ℝ, x ∈ Set.uIcc a b →
      HasDerivAt (deriv U) ((radialProfile v x / 2) * (U x - x)) x := by
    intro a b ha hab hbR
    filter_upwards [hUsecond0 ha hab hbR] with x hx hmem
    dsimp [U]
    exact hx hmem
  have hderR0 : HasDerivAt U 0 R := by
    simpa [U] using canonicalProfile_hasDerivAt_R hR hvrad hv_supp hrad hw
  have hUderR : deriv U R = 0 := hderR0.deriv
  have hfderR : HasDerivAt f 1 R := by
    dsimp [f]
    simpa using hasDerivAt_id_sub hderR0
  have hf0 : f 0 = 0 := by
    dsimp [f]
    simp [hU0']
  have hfcont : ContinuousOn f (Icc (0 : ℝ) R) := by
    dsimp [f]
    exact continuous_id.continuousOn.sub hUcont
  have hfdiff : ∀ x : ℝ, x ∈ Ioo (0 : ℝ) R → DifferentiableAt ℝ f x := by
    intro x hx
    dsimp [f]
    exact differentiableAt_id.sub (hUdiff x hx)
  have hderfU (x : ℝ) (hx0 : 0 < x) (hxR : x ≤ R) : deriv f x = 1 - deriv U x := by
    by_cases hxeqR : x = R
    · subst x
      rw [hfderR.deriv, hUderR]
      norm_num
    · have hxR' : x < R := lt_of_le_of_ne hxR hxeqR
      have hUx : DifferentiableAt ℝ U x := hUdiff x ⟨hx0, hxR'⟩
      have hd : deriv (fun r : ℝ => r - U r) x = 1 - deriv U x := deriv_id_sub hUx
      simpa [f] using hd
  have hfac : ∀ ⦃a b : ℝ⦄, 0 < a → a ≤ b → b ≤ R →
      AbsolutelyContinuousOnInterval (deriv f) a b := by
    intro a b ha hab hbR
    have hg_ac : AbsolutelyContinuousOnInterval (fun x => 1 - deriv U x) a b := by
      exact absolutelyContinuousOnInterval_sub_const_left (hUac ha hab hbR)
    refine absolutelyContinuousOnInterval_congr ?_ hg_ac
    intro x hx
    have hxab : x ∈ Set.Icc a b := by
      rw [uIcc_of_le hab] at hx
      exact hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hxab.1
    exact hderfU x hx0 (le_trans hxab.2 hbR)
  have hq : ∀ x : ℝ, x ∈ Ioo (0 : ℝ) R → f x < 0 → q x ≤ 0 := by
    intro x hx hneg
    dsimp [q, f]
    exact mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg (by dsimp [radialProfile]; exact hv_nonneg (x • radU0)) (by norm_num)) hneg.le
  have hfsecond : ∀ ⦃a b : ℝ⦄, 0 < a → a ≤ b → b ≤ R → ∀ᵐ x : ℝ, x ∈ Set.uIcc a b →
      HasDerivAt (deriv f) (q x) x := by
    intro a b ha hab hbR
    have hne_a : ∀ᵐ x : ℝ, x ≠ a := by
      rw [MeasureTheory.ae_iff]
      simp [measure_singleton]
    have hne_b : ∀ᵐ x : ℝ, x ≠ b := by
      rw [MeasureTheory.ae_iff]
      simp [measure_singleton]
    filter_upwards [hUsecond ha hab hbR, hne_a, hne_b] with x hx hxa hxb hmem
    have hmemIcc : x ∈ Set.Icc a b := by
      rw [uIcc_of_le hab] at hmem
      exact hmem
    have hxltb : x < b := lt_of_le_of_ne hmemIcc.2 hxb
    have hax : a < x := lt_of_le_of_ne hmemIcc.1 (Ne.symm hxa)
    have hx0 : 0 < x := lt_trans ha hax
    have hU2 : HasDerivAt (deriv U) ((radialProfile v x / 2) * (U x - x)) x := hx hmem
    have hnegder : HasDerivAt (fun y : ℝ => 1 - deriv U y)
        (-((radialProfile v x / 2) * (U x - x))) x := by
      have hc : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x := hasDerivAt_const x (1 : ℝ)
      have hsub1 : HasDerivAt ((fun _ : ℝ => (1 : ℝ)) - deriv U)
          (0 - ((radialProfile v x / 2) * (U x - x))) x := hc.sub hU2
      have hEqf : (fun _ : ℝ => (1 : ℝ)) - deriv U = fun y : ℝ => 1 - deriv U y := by
        funext y
        simp
      have hEqv : 0 - ((radialProfile v x / 2) * (U x - x)) =
          -((radialProfile v x / 2) * (U x - x)) := by ring
      simpa [hEqf, hEqv] using hsub1
    have hcong : (fun y : ℝ => 1 - deriv U y) =ᶠ[𝓝 x] deriv f := by
      have hxR : x < R := lt_of_lt_of_le hxltb hbR
      filter_upwards [Ioo_mem_nhds hx0 hxR] with y hy
      symm
      exact hderfU y hy.1 (le_of_lt hy.2)
    have hmain : HasDerivAt (deriv f) (-((radialProfile v x / 2) * (U x - x))) x :=
      hnegder.congr_of_eventuallyEq hcong.symm
    have hval : -((radialProfile v x / 2) * (U x - x)) = q x := by
      dsimp [q, f]
      ring
    rwa [hval] at hmain
  have hnonneg := ae_nonneg_of_concave_neg (f := f) (q := q) (c := 1) hR (by norm_num)
    hf0 hfcont hfdiff hfac hfsecond hq hfderR
  intro r hr0 hrR
  have hfr := hnonneg r ⟨hr0, hrR⟩
  have hmain : 0 ≤ r - canonicalProfile v w R r := by
    simpa [f, U] using hfr
  linarith

end Submission.BoseGases
