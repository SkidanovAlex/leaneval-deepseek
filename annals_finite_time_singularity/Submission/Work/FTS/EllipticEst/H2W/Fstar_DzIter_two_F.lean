/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W/Fstar_DzIter_two_F` — the level-`2` moment of the source in the weak class

The lemma requested at this path is

```
theorem Fstar_DzIter_two_F (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z = 0
```

i.e. `F_*(D_z²F) ≡ 0` **pointwise** on `(0,∞)` for every datum of the weak class
`EllWeakPos α 2 F Ψ`.  This file records the outcome of the attempt.

* `Fstar_DzIter_two_F_ae` (proved below, `sorry`-free) is the statement the class *does* yield:
  the same conclusion **almost everywhere**.
* The pointwise statement is not reachable: it lies exactly one level of `ℋ^k`-honesty beyond
  everything `EllWeakPos α 2` controls.  See the detailed note at the end of this docstring.

## What the chain rule gives (and what it does not)

For a source `C^∞` on the open quadrant and honestly in `ℋ^k`, the only bridge from the moment
conditions to the moments of the radially differentiated source is the moment chain
(`Cert.GbarSin.FstarDzIter_chain_open`, equivalently `radIter_bmom_chain`)

  `F_*(D_z^j F)(z) - F_*(D_z^j F)(s) = ∫_s^z F_*(D_z^{j+1} F)(r)/r dr`,   `0 < s ≤ z`,

whose hypotheses are `HkMem α k F` and **`j + 1 ≤ k`**.  At `k = 2` it reaches `j = 1` only,
and the available input there is the already proved `remov.Fstar_DzIter_one_F_ge_two`
(whose own hypothesis is `2 ≤ k`; the level-`1` version `remov.Fstar_DzIter_one_F`, with only
`1 ≤ k`, is *itself still an open `sorry`*):

  `F_*(D_z²F)(r)/r` has vanishing integral over every interval `[s,z] ⊆ (0,∞)`, because
  `∫_s^z F_*(D_z²F)(r)/r dr = F_*(D_zF)(z) - F_*(D_zF)(s) = 0`.

Since `r ↦ F_*(D_z²F)(r)/r` is locally integrable when `HkMem α 2 F` holds
(`integrableOn_Bmom_div`), this yields `F_*(D_z²F) = 0` **a.e.** — the lemma below.

## Why a.e. cannot be upgraded with the given hypotheses

`F_*(D_z²F)` is the primitive of `F_*(D_z³F)/r` (the moment chain at `j = 2`), so its
*continuity* — which is what turns "a.e. zero" into "everywhere zero", and is exactly how
`remov.Fstar_DzIter_one_F_ge_two` upgrades `F_*(D_zF)` — requires the local integrability of
`D_z³F·sinθcos²θ`, i.e. honesty at level `3`.  Likewise the quantitative mean-value upgrade
(`remov.Fstar_DzIter_one_Psi_estimate`, `|moment(z₀)| ≤ C√h` from a.e. vanishing on
`(z₀-h,z₀)`) bounds `moment(z₀) - moment(z)` by an integral of `∂_r(D_z²F) = D_z³F/r` and
therefore needs the same level-`3` control.

The class supplies neither.  `HkMem α 2 F` controls `D_z^iF` for `i ≤ 2` only, and the two
`Ψ`-side hypotheses `HkMem α 2 (z²∂_z²Ψ)`, `HkMem α 2 (∂_θ²Ψ)` control `z^j∂_z^jΨ` up to
`j = 4` (`D_z²(z²∂_z²Ψ) = 4z²∂_z²Ψ + 5z³∂_z³Ψ + z⁴∂_z⁴Ψ`), whereas
`D_z³F = bslOp α(D_z³Ψ) = -α²z²∂_z²(D_z³Ψ) - α(5+α)z∂_z(D_z³Ψ) + Lzero1(D_z³Ψ)`
involves `z²∂_z²(D_z³Ψ) = z⁵∂_z⁵Ψ + …`.  So the missing ingredient is a *hypothesis*, not
machinery: no lemma about `EllWeakPos α 2 F Ψ` as defined can close the gap.

A second, independent obstruction of the same family is documented in the tree:
`remov/NOTES_Fstar_DzIter_one_eq_zero.md` shows that the θ-integration-by-parts identity
`F_*(bslOp α Ψ) = -(α²z²)F_*(∂_zzΨ) - (α(5+α)z)F_*(∂_zΨ)` is *false* under `EllWeakPos` as
defined (the point value `Ψ z 0 = 0` does not constrain the interior limit at `θ = 0`, and the
`ℋ^k`-weights do not see the resulting jump).  The same obstruction was recorded for the
consumer of the present lemma, `H2W/shiftWeak`.

## The fix

State the conclusion a.e. (`Fstar_DzIter_two_F_ae` below), or strengthen the class by one
level of honesty (e.g. add `Work.Spaces.HkMem α 3 F` to `EllWeakPos`, or require the θ-slices
to be `C²` up to the closed interval `[0,π/2]`), or weaken the moment conditions of
`EllWeakPos` — and of `H2W.shiftWeak`, the consumer — to hold only a.e. in `z`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.OpenQAux
import Submission.Work.FTS.EllipticEst.Cert.radIter_Bmom_ae
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.remov.smoothOpen_slices_weak
import Submission.Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The level-`2` moment of the source vanishes almost everywhere** (the sharp conclusion
carried by `EllWeakPos α 2 F Ψ`).

The moment chain at `j = 1` (available because `1 + 1 ≤ 2`) together with the proved vanishing
of `F_*(D_zF)` says that `r ↦ F_*(D_z²F)(r)/r` has vanishing integral over every interval
`[s,z] ⊆ (0,∞)`; that function is locally integrable by `HkMem α 2 F`, so it vanishes a.e. -/
theorem Fstar_DzIter_two_F_ae (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z = 0 := by
  have hF : Work.FTS.EllipticEst.SmoothOpen F :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).1
  have h1 : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0 :=
    fun z hz => Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two (α := α) (k := 2)
      (by norm_num) h z hz
  have hfr : (fun r : ℝ => Work.FTS.EllipticEst.Bmom F 2 r / r)
      = fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) r / r := by
    funext r
    rw [Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter]
  -- the moment chain at `j = 1`: the primitive of `B_2/r` vanishes identically
  have hchain : ∀ s z : ℝ, 0 < s → 0 < z →
      ∫ r in s..z, Work.FTS.EllipticEst.Bmom F 2 r / r = 0 := by
    intro s z hs hz
    rw [hfr]
    rcases le_total s z with hsz | hzs
    · have hcr := Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open α 2 F hF h.memF 1
        (by norm_num : 1 + 1 ≤ 2) hs hsz
      rw [← hcr, h1 z hz, h1 s hs, sub_zero]
    · have hcr := Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open α 2 F hF h.memF 1
        (by norm_num : 1 + 1 ≤ 2) hz hzs
      have hcr' : ∫ r in z..s, Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) r / r = 0 := by
        rw [← hcr]
        rw [h1 s hs, h1 z hz, sub_zero]
      rw [intervalIntegral.integral_symm, hcr', neg_zero]
  -- on each compact `[a,b] ⊆ (0,∞)`, the primitive of `B_2/r` is identically zero near every
  -- point of `[a,b]`, so the Lebesgue differentiation theorem forces `B_2 = 0` a.e. there
  have key : ∀ n : ℕ, ∀ᵐ x ∂(MeasureTheory.volume.restrict
      (Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2))),
      Work.FTS.EllipticEst.Bmom F 2 x = 0 := by
    intro n
    set a : ℝ := 1 / ((n : ℝ) + 1) with ha
    set b : ℝ := (n : ℝ) + 2 with hb
    have hpos : 0 < a := by rw [ha]; positivity
    have hlt : a < b := by
      have hbpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [ha, hb, div_lt_iff₀ hbpos]
      nlinarith
    have hle : a ≤ b := hlt.le
    have hInt : IntervalIntegrable (fun r : ℝ => Work.FTS.EllipticEst.Bmom F 2 r / r)
        volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
      exact Work.FTS.EllipticEst.integrableOn_Bmom_div α 2 hF h.memF 2 le_rfl a b hpos hlt
    have hldt := IntervalIntegrable.ae_hasDerivAt_integral hInt
    rw [Set.uIcc_of_le hle] at hldt
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hldt] with x hx
    intro hxmem
    have hxpos : 0 < x := lt_of_lt_of_le hpos hxmem.1
    have hder : HasDerivAt (fun y : ℝ => ∫ t in a..y, Work.FTS.EllipticEst.Bmom F 2 t / t)
        (Work.FTS.EllipticEst.Bmom F 2 x / x) x :=
      hx hxmem a ⟨le_rfl, hle⟩
    have hev : (fun y : ℝ => ∫ t in a..y, Work.FTS.EllipticEst.Bmom F 2 t / t)
        =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hxpos] with y hy
      exact hchain a y hpos hy
    have h0 : HasDerivAt (fun _ : ℝ => (0 : ℝ))
        (Work.FTS.EllipticEst.Bmom F 2 x / x) x := hev.hasDerivAt_iff.mp hder
    have hval : Work.FTS.EllipticEst.Bmom F 2 x / x = 0 :=
      (h0.unique (hasDerivAt_const x 0))
    rw [div_eq_zero_iff] at hval
    rcases hval with h' | h'
    · exact h'
    · exact absurd h' hxpos.ne'
  have keynull : ∀ n : ℕ, volume {x | x ∈ Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2)
      ∧ ¬ (Work.FTS.EllipticEst.Bmom F 2 x = 0)} = 0 := by
    intro n
    have hh := key n
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff] at hh
    have hset : {x | x ∈ Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2)
        ∧ ¬ (Work.FTS.EllipticEst.Bmom F 2 x = 0)}
        = {x | ¬ (x ∈ Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) →
            Work.FTS.EllipticEst.Bmom F 2 x = 0)} := by
      ext x
      simp only [Set.mem_setOf_eq, not_imp]
    rw [hset]
    exact hh
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi, MeasureTheory.ae_iff]
  refine measure_mono_null ?_ (measure_iUnion_null keynull)
  intro x hx
  have hx' : x ∈ Set.Ioi 0 ∧ ¬ (Work.FTS.EllipticEst.Bmom F 2 x = 0) := by
    have hx'' : x ∈ Set.Ioi 0 ∧ ¬ (Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) x = 0) := by
      simpa only [Set.mem_setOf_eq, not_imp] using hx
    refine ⟨hx''.1, ?_⟩
    intro hb
    exact hx''.2 (by rwa [← Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter])
  obtain ⟨hx0, hxn⟩ := hx'
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ,
      1 / ((n : ℝ) + 1) ≤ x ∧ x ≤ (n : ℝ) + 2 := by
    obtain ⟨n, hn⟩ := exists_nat_ge (max x (1 / x))
    refine ⟨n, ?_, ?_⟩
    · have hx1 : 1 / x ≤ (n : ℝ) := le_trans (le_max_right _ _) hn
      have : 1 ≤ x * (n : ℝ) := by
        rw [div_le_iff₀ hx0] at hx1
        linarith
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      nlinarith
    · have hxn' : x ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
      linarith
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  exact ⟨⟨hn1, hn2⟩, hxn⟩

/-- **The pointwise statement under one extra level of honesty.**

If, on top of the weak class, the source is honestly in `ℋ³` (`Work.Spaces.HkMem α 3 F`), then
`F_*(D_z²F) ≡ 0` on `(0,∞)`.  This is the *fix* for the mis-stated request: with `ℋ³`-honesty
the moment chain at `j = 2` (`2 + 1 ≤ 3`) makes `F_*(D_z²F)` the primitive of the locally
integrable function `F_*(D_z³F)/r` (via `radIter_bmom_continuousOn`, i.e. the chain rule at
`j = 2`), hence continuous, and it vanishes a.e. by `Fstar_DzIter_two_F_ae`; a continuous
function vanishing a.e. on `(0,∞)` vanishes everywhere. -/
theorem Fstar_DzIter_two_F_of_HkMem_three (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ)
    (h3 : Work.Spaces.HkMem α 3 F) :
    ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z = 0 := by
  have hF : Work.FTS.EllipticEst.SmoothOpen F :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).1
  -- the moment `B_2` is continuous on `(0,∞)`, being the primitive of the locally integrable
  -- function `B_3/r` (moment chain at `j = 2`, which needs `ℋ³`)
  have hcont : ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.Bmom F 2 z) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.radIter_bmom_continuousOn α 3 hF h3 2 (by norm_num)
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.FTS.EllipticEst.Bmom F 2 z = 0 := by
    filter_upwards [Fstar_DzIter_two_F_ae α F Ψ h] with z hz
    rw [Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter]
    exact hz
  have hEq := MeasureTheory.Measure.eqOn_of_ae_eq hae hcont continuousOn_const
    (fun x hx => by rw [interior_Ioi]; exact subset_closure hx)
  intro z hz
  rw [← Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter]
  exact hEq hz

/-- **The requested lemma.**  *Not proved*: see the module docstring.  `EllWeakPos α 2 F Ψ`
yields only the a.e. statement `Fstar_DzIter_two_F_ae`; the pointwise upgrade requires one
further level of `ℋ`-honesty (e.g. `HkMem α 3 F`, cf. `Fstar_DzIter_two_F_of_HkMem_three`)
which the class does not provide. -/
theorem Fstar_DzIter_two_F (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z = 0 := by
  sorry

end Work.FTS.EllipticEst.H2W
