/-
# `Work.FinalFix.Nonreal` — the root-parabolic parameter is not real

Area `Submission/Work/FinalFix/` of the mandelbar project.  This module proves

```lean
Work.FinalFix.nonreal (d : Work.EL.RootParabolic c) : c.im ≠ 0
```

i.e. **`Work.EL.RootParabolic` is uninhabitable at real parameters**.  This is the
`nonreal` field of `Work.Final.FinalInputs` of `Submission/Work/Final/`, which is thereby
*derived* rather than assumed (`NOTES_LEAD_mandelbar_residuals.md` §0.6 and §4, row `nonreal`).

## Why it is true, and why it needs no portrait

Let `c` be real.  Then `T_c` commutes with complex conjugation, and the Böttcher coordinate
(in the dynamical plane) is conjugation-equivariant: `φ (conj z) = conj (φ z)` on the escaping
set (`phi_conj`, from the *uniqueness* of the Böttcher coordinate).  Consequently the escaping
points of the real axis are exactly the points of the two rays of angles `0` and `1/2`:

* a real escaping point `y` has `φ y = conj (φ y)` real, so `y` lies on `R_c(0)` or `R_c(1/2)`
  (`real_mem_paramRay_zero_or_half`);

and conversely, a real point of a ray `R_c(θ)` forces `2θ ∈ ℤ`
(`exists_int_two_mul_of_mem_paramRay`), so the ray pair of the root portrait
(`α₁ = 371/1023`, `α₂ = 404/1023`, both with `2αᵢ ∉ ℤ`) is **disjoint from the real axis**.

Now the contradiction.  Let `P` be the `α`-pair of `d` (the two root rays `371/1023`, `404/1023`
landing at `z₁`), with its two sides `pairSide P` and `pairSideNear P` (`Work.EL.PairSides`,
supplied by `Work.Final.exists_alphaPair_pairSides`).  The wake condition `d.wake` at `k = 1`
reads

  `c ∈ wakeSide d.hN z₁ 0 = pairSide P`,

i.e. the *critical value* `c = T_c 0` lies in the far side of the pair curve.  Since `c` is real,
so is every point of the real segment joining `c` to any real point `x` far out on the real axis
(chosen so that the segment misses `z₁`), and by the previous paragraph that segment misses the
pair curve.  The segment is connected, so

  `x ∈ pairSide P`   (`x` is connected to `c` inside the complement of the pair curve).

But `x` is real and escaping, so `x ∈ R_c(0) ∪ R_c(1/2)`, and both angles `0` and `1/2` lie in the
complementary arc `(P.b, P.a + 1)`; `PairSides.paramRay_near` therefore puts `x` in the *other*
side `pairSideNear P`, contradicting `PairSides.disjoint`.

Nothing here uses a bound on the number of rays landing at a point: the real axis itself is the
contradiction.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.Final.exists_alphaPair_pairSides
import Submission.Work.ParamRays.Phi_conj
import Submission.Work.Escape.tendsto_norm_Tantibar_iterate_atTop
import Submission.Work.ParamRays.IsDynBottcher_modulus
import Submission.Work.ParamRays.isDynBottcher_unique
import Submission.Work.ParamRays.greenFun_pos_of_lt
import Submission.Work.Landing.Family.tantibar_star
import Submission.Work.TopJordan.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology ComplexConjugate

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.FinalFix

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ}

/-! ## Böttcher coordinates of a real parameter are conjugation-equivariant -/

/-- **The escaping set is conjugation-invariant at a real parameter.** -/
theorem escaping_conj_iff (hreal : c.im = 0) (z : ℂ) :
    Work.ParamRays.Escaping c (conj z) ↔ Work.ParamRays.Escaping c z := by
  have h := Work.ParamRays.escaping_conj_conj (c := c) (w := conj z)
  simpa only [Complex.conj_eq_iff_im.mpr hreal, Complex.conj_conj] using h

/-- For a real parameter, `z ↦ conj (φ (conj z))` is again a Böttcher coordinate: conjugation
intertwines the escaping set, the functional equation `φ (T_c z) = conj (φ z)²` and the
asymptotic `φ z / z → 1`.  This is the dynamical-plane analogue of
`Work.ParamRaysCrit.CritTransport.isCritBottcher_conj`. -/
theorem isDynBottcher_conj (hreal : c.im = 0) {φ : ℂ → ℂ}
    (h : Work.ParamRays.IsDynBottcher c φ) :
    Work.ParamRays.IsDynBottcher c (fun z => conj (φ (conj z))) := by
  have hc : conj c = c := Complex.conj_eq_iff_im.mpr hreal
  have hconj : ∀ z : ℂ, Work.ParamRays.Escaping c z → Work.ParamRays.Escaping c (conj z) :=
    fun z hz => (escaping_conj_iff hreal z).mpr hz
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ContinuousOn (fun z : ℂ => φ (conj z)) (Work.ParamRays.escapingSet c) :=
      h.1.comp Complex.continuous_conj.continuousOn (fun z hz => hconj z hz)
    simpa [Function.comp_def] using Complex.continuous_conj.comp_continuousOn h1
  · intro z hz
    have hz' : Work.ParamRays.Escaping c (conj z) := hconj z hz
    have hT : conj (Tantibar c z) = Tantibar c (conj z) := by
      simp only [LeanEval.ComplexAnalysis.Tantibar, map_add, map_pow, Complex.conj_conj, hc]
    show conj (φ (conj (Tantibar c z))) = conj (conj (φ (conj z))) ^ 2
    rw [hT, h.2.1 (conj z) hz']
    simp only [map_pow, Complex.conj_conj]
  · intro ε hε
    have htend : Filter.Tendsto (starRingEnd ℂ) (Filter.cocompact ℂ) (Filter.cocompact ℂ) :=
      Filter.tendsto_cocompact_cocompact_of_norm (f := starRingEnd ℂ)
        (fun ε => ⟨ε, fun x hx => by rwa [Complex.norm_conj]⟩)
    have h3 : ∀ᶠ z : ℂ in Filter.cocompact ℂ, ‖φ (conj z) - conj z‖ ≤ ε * ‖conj z‖ :=
      htend.eventually (h.2.2 ε hε)
    filter_upwards [h3] with z hz
    have hz'' : ‖conj (φ (conj z)) - z‖ = ‖φ (conj z) - conj z‖ := by
      rw [show conj (φ (conj z)) - z = conj (φ (conj z) - conj z) by
        rw [map_sub, Complex.conj_conj], Complex.norm_conj]
    rw [hz'']
    simpa only [Complex.norm_conj] using hz

/-- **The Böttcher coordinate of a real parameter commutes with conjugation** on the escaping
set.  This is the uniqueness of the Böttcher coordinate (`isDynBottcher_unique`) applied to the
conjugated coordinate `isDynBottcher_conj`. -/
theorem phi_conj (hreal : c.im = 0) {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ)
    {z : ℂ} (hz : Work.ParamRays.Escaping c z) : φ (conj z) = conj (φ z) := by
  have h' := Work.ParamRays.isDynBottcher_unique hφ (isDynBottcher_conj hreal hφ)
    ((escaping_conj_iff hreal z).mpr hz)
  simpa [Function.comp_def] using h'

/-- **A real escaping point has a real Böttcher coordinate.** -/
theorem phi_real_of_real (hreal : c.im = 0) {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ)
    {x : ℝ} (hx : Work.ParamRays.Escaping c (x : ℂ)) : (φ (x : ℂ)).im = 0 := by
  have h1 := phi_conj hreal hφ hx
  rw [Complex.conj_ofReal] at h1
  have h2 : (φ (x : ℂ)).im = -(φ (x : ℂ)).im := by
    have h3 := congrArg Complex.im h1
    simpa using h3
  linarith

/-! ## The rays through the real axis -/

/-- `rayPoint θ t = t * exp (2πiθ)`; its imaginary part is `t * sin (2πθ)`. -/
theorem rayPoint_im (θ t : ℝ) :
    (Work.Top.NakaneData.rayPoint θ t).im = t * Real.sin (2 * Real.pi * θ) := by
  have hexp : (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I)
      = ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [Work.Top.NakaneData.rayPoint, hexp, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_im]
  ring

theorem rayPoint_zero (t : ℝ) : Work.Top.NakaneData.rayPoint 0 t = (t : ℂ) := by
  rw [Work.Top.NakaneData.rayPoint]
  simp

/-- The ray of angle `1/2` is the negative half of the real axis. -/
theorem rayPoint_half (t : ℝ) : Work.Top.NakaneData.rayPoint (1 / 2) t = -(t : ℂ) := by
  have hexp : (2 * (Real.pi : ℂ) * ((1 / 2 : ℝ) : ℂ) * Complex.I)
      = (Real.pi : ℂ) * Complex.I := by push_cast; ring
  rw [Work.Top.NakaneData.rayPoint, hexp]
  simp

/-- **A real point of an external ray has a half-integer angle.**  For a real parameter the
Böttcher coordinate is real on the real axis, so a real point of a ray `R_c(θ)` forces
`e^{2πiθ} = ±1`. -/
theorem exists_int_two_mul_of_mem_paramRay (hreal : c.im = 0) {φ : ℂ → ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) {hN : Work.EL.DynB c φ} {θ : ℝ} {x : ℝ}
    (hx : (x : ℂ) ∈ Work.EL.paramRay hN θ) : ∃ n : ℤ, 2 * θ = (n : ℝ) := by
  have hxK : (x : ℂ) ∉ Work.EL.K c := Work.EL.paramRay_subset_compl hN θ hx
  obtain ⟨-, t, ht, hteq⟩ := hx
  have hxEsc : Work.ParamRays.Escaping c (x : ℂ) := by
    rw [Work.ParamRays.escaping_iff_not_bounded]
    exact fun hb => hxK hb
  have hφreal : (φ (x : ℂ)).im = 0 := phi_real_of_real hreal hφ hxEsc
  have hval : φ (x : ℂ) = Work.Top.NakaneData.rayPoint θ t := by
    rw [← Work.EL.dynPhi_of_notMem (φ := φ) hxK]
    exact hteq
  have him : (Work.Top.NakaneData.rayPoint θ t).im = 0 := by rw [← hval]; exact hφreal
  rw [rayPoint_im] at him
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hsin : Real.sin (2 * Real.pi * θ) = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact absurd h ht0
    · exact h
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
  refine ⟨n, ?_⟩
  have h2 : (n : ℝ) * Real.pi = (2 * θ) * Real.pi := by rw [hn]; ring
  exact (mul_right_cancel₀ Real.pi_ne_zero h2).symm

/-- **A real escaping point lies on the ray of angle `0` or `1/2`** (for a real parameter). -/
theorem real_mem_paramRay_zero_or_half (hreal : c.im = 0) {φ : ℂ → ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) {hN : Work.EL.DynB c φ} {x : ℝ}
    (hbig : max 2 ‖c‖ < |x|) :
    (x : ℂ) ∈ Work.EL.paramRay hN 0 ∨ (x : ℂ) ∈ Work.EL.paramRay hN (1 / 2) := by
  have hbig' : max 2 ‖c‖ < ‖(x : ℂ)‖ := by simpa using hbig
  have hxEsc : Work.ParamRays.Escaping c (x : ℂ) :=
    Work.Escape.tendsto_norm_Tantibar_iterate_atTop c (x : ℂ) hbig'
  have hxK : (x : ℂ) ∉ Work.EL.K c := fun hb =>
    (Work.ParamRays.escaping_iff_not_bounded c (x : ℂ)).mp hxEsc hb
  have hφx : (φ (x : ℂ)).im = 0 := phi_real_of_real hreal hφ hxEsc
  have hmod : ‖φ (x : ℂ)‖ = Real.exp (Work.ParamRays.greenFun c (x : ℂ)) :=
    Work.ParamRays.IsDynBottcher_modulus hφ hxEsc
  have hgpos : 0 < Work.ParamRays.greenFun c (x : ℂ) :=
    Work.ParamRays.greenFun_pos_of_lt c (x : ℂ) hbig'
  have hnorm1 : 1 < ‖φ (x : ℂ)‖ := by rw [hmod]; exact Real.one_lt_exp_iff.mpr hgpos
  have hre : φ (x : ℂ) = ((φ (x : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [hφx]
  have habs : ‖φ (x : ℂ)‖ = |(φ (x : ℂ)).re| := by
    rw [hre, Complex.norm_real]
    simp
  rcases lt_trichotomy (φ (x : ℂ)).re 0 with hlt | heq | hgt
  · -- the Böttcher coordinate is a negative real: angle `1/2`
    right
    refine ⟨hxK, -(φ (x : ℂ)).re, ?_, ?_⟩
    · rw [abs_of_neg hlt] at habs
      linarith
    · rw [Work.EL.dynPhi_of_notMem (φ := φ) hxK, rayPoint_half, hre]
      simp
  · exfalso
    rw [hre, heq] at hnorm1
    norm_num at hnorm1
  · -- the Böttcher coordinate is a positive real: angle `0`
    left
    refine ⟨hxK, (φ (x : ℂ)).re, ?_, ?_⟩
    · rw [abs_of_pos hgt] at habs
      linarith
    · rw [Work.EL.dynPhi_of_notMem (φ := φ) hxK, rayPoint_zero, hre]
      simp

/-! ## The arithmetic of the root angles -/

theorem not_exists_int_two_mul_alpha1 : ¬ ∃ n : ℤ, 2 * Work.EL.alpha1 = (n : ℝ) := by
  rintro ⟨n, hn⟩
  have hR : (742 : ℝ) = 1023 * (n : ℝ) := by
    have h : 2 * (371 / 1023 : ℝ) = (n : ℝ) := by simpa [Work.EL.alpha1] using hn
    linarith
  have hZ : (742 : ℤ) = 1023 * n := by exact_mod_cast hR
  omega

theorem not_exists_int_two_mul_alpha2 : ¬ ∃ n : ℤ, 2 * Work.EL.alpha2 = (n : ℝ) := by
  rintro ⟨n, hn⟩
  have hR : (808 : ℝ) = 1023 * (n : ℝ) := by
    have h : 2 * (404 / 1023 : ℝ) = (n : ℝ) := by simpa [Work.EL.alpha2] using hn
    linarith
  have hZ : (808 : ℤ) = 1023 * n := by exact_mod_cast hR
  omega

/-! ## The wake side of index `0` is the far side of the `α`-pair -/

/-- The wake side `X₀` of the root portrait, in the vocabulary of the root-parabolic parameter,
is the far side of the `α`-pair. -/
theorem wakeSide_zero_eq_pairSide {c : ℂ} (d : Work.EL.RootParabolic c) (P : Work.EL.CoPair d.hN)
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁) :
    Work.EL.wakeSide d.hN d.z₁ 0 = Work.EL.pairSide P := by
  have hP : P.toRawPair = ⟨Work.EL.alpha1, Work.EL.alpha2, d.z₁⟩ := by
    rw [show P.toRawPair = ⟨P.a, P.b, P.y⟩ from rfl, hPa, hPb, hPy]
  have hmin : min Work.EL.alpha1 Work.EL.alpha2 = Work.EL.alpha1 :=
    min_eq_left (by norm_num [Work.EL.alpha1, Work.EL.alpha2])
  have hmax : max Work.EL.alpha1 Work.EL.alpha2 = Work.EL.alpha2 :=
    max_eq_right (by norm_num [Work.EL.alpha1, Work.EL.alpha2])
  have hlo : Work.EL.wakeLo 0 = Work.EL.alpha1 := rfl
  have hhi : Work.EL.wakeHi 0 = Work.EL.alpha2 := rfl
  simp only [Work.EL.wakeSide, Work.EL.RawPair.sideThrough,
    Work.EL.pairSide, Work.EL.pairSideThroughArc, Work.EL.alphaPairRaw, hlo, hhi, hmin, hmax,
    Function.iterate_zero, id_eq]
  rw [hP]

/-! ## A large real point avoiding a given point -/

/-- For every `a : ℝ`, every `w : ℂ` with `w ≠ a` and every bound `R`, there is a real `x` with
`|x| > R` whose real segment from `a` misses `w`. -/
theorem exists_large_real_avoiding (a : ℝ) (w : ℂ) (R : ℝ) (hne : w ≠ (a : ℂ)) :
    ∃ x : ℝ, R < |x| ∧ (w.im ≠ 0 ∨ w.re ∉ Set.uIcc a x) := by
  have hNnonneg : 0 ≤ max R (|a| + |w.re|) :=
    le_trans (add_nonneg (abs_nonneg a) (abs_nonneg w.re)) (le_max_right _ _)
  have hNpos : 0 < max R (|a| + |w.re|) + 1 := by linarith
  have hNR : R ≤ max R (|a| + |w.re|) := le_max_left _ _
  have hNa : a ≤ max R (|a| + |w.re|) + 1 := by
    have h1 : |a| ≤ |a| + |w.re| := le_add_of_nonneg_right (abs_nonneg w.re)
    have h2 : |a| + |w.re| ≤ max R (|a| + |w.re|) := le_max_right _ _
    have h3 : |a| ≤ max R (|a| + |w.re|) := le_trans h1 h2
    linarith [le_abs_self a]
  have hNneg : -a ≤ max R (|a| + |w.re|) := by
    have h1 : |a| ≤ |a| + |w.re| := le_add_of_nonneg_right (abs_nonneg w.re)
    have h2 : |a| + |w.re| ≤ max R (|a| + |w.re|) := le_max_right _ _
    linarith [neg_le_abs a]
  by_cases him : w.im = 0
  · have hw : w = (w.re : ℂ) := Complex.ext rfl (by simpa using him)
    have hne' : w.re ≠ a := fun h => hne (by rw [hw, h])
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · refine ⟨max R (|a| + |w.re|) + 1, ?_, Or.inr ?_⟩
      · rw [abs_of_pos hNpos]; linarith
      · intro hmem
        rw [Set.mem_uIcc] at hmem
        rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h1 (not_le.mpr hlt)
        · linarith [h1, h2, hNa, hlt]
    · refine ⟨-(max R (|a| + |w.re|) + 1), ?_, Or.inr ?_⟩
      · rw [abs_neg, abs_of_pos hNpos]; linarith
      · have hx : -(max R (|a| + |w.re|) + 1) < a := by linarith [hNneg]
        intro hmem
        rw [Set.mem_uIcc] at hmem
        rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · linarith [hx, h2, hgt]
        · exact absurd h2 (not_le.mpr hgt)
  · exact ⟨max R (|a| + |w.re|) + 1, by rw [abs_of_pos hNpos]; linarith, Or.inl him⟩

/-! ## The root-parabolic parameter is not real -/

/-- **At a real parameter there is no root-parabolic data** (`NOTES_LEAD_mandelbar_residuals.md`
§0.6 and §4, row `nonreal`).

Suppose `c` were real.  Then the dynamical plane is conjugation-symmetric: the Böttcher
coordinate is conjugation-equivariant (`phi_conj`), the escaping points of the real axis are
exactly the points of the rays of angles `0` and `1/2` (`real_mem_paramRay_zero_or_half`), and a
real point of a ray `R_c(θ)` forces `2θ ∈ ℤ` (`exists_int_two_mul_of_mem_paramRay`), so the real
axis meets the `α`-pair curve only possibly at `z₁`.

Now the wake condition `d.wake` at `k = 1` says that the critical value `c = T_c 0` lies in the
wake side `X₀`, which is the far side `pairSide P` of the `α`-pair.  The real segment from `c` to
a far-out real point `x` (chosen so that it misses `z₁`) is connected and avoids the pair curve,
so `x` lies in `pairSide P` as well.  But `x` is a real escaping point, hence lies on `R_c(0)` or
`R_c(1/2)`, and both of these angles lie in the complementary arc `(P.b, P.a + 1)`, so
`PairSides.paramRay_near` puts `x` in the other side `pairSideNear P` — contradicting the
disjointness of the two sides. -/
theorem nonreal {c : ℂ} (d : Work.EL.RootParabolic c) : c.im ≠ 0 := by
  intro hreal
  obtain ⟨P, hPa, hPb, hPy, hPS⟩ :=
    Work.Final.exists_alphaPair_pairSides d Work.TopJordan.jordanForm
  -- the critical value lies in the far side of the α-pair
  have hcX : c ∈ Work.EL.pairSide P := by
    have h := d.wake 1 le_rfl
    have h0 : (1 - 1) % 5 = 0 := by norm_num
    rw [h0] at h
    have h1 : (Tantibar c)^[1] 0 = c := by simp
    rw [h1] at h
    rwa [wakeSide_zero_eq_pairSide d P hPa hPb hPy] at h
  -- real coordinate of `c`
  set a : ℝ := c.re with ha
  have hc_eq : c = (a : ℂ) := Complex.ext (by simp [ha]) (by simp [ha, hreal])
  have hz1ne : d.z₁ ≠ c := by
    intro h
    exact d.crit.2 0 (by rw [Function.iterate_zero]; exact h.symm)
  -- a far-out real point whose segment from `c` misses `z₁`
  obtain ⟨x, hxbig, hxav⟩ :=
    exists_large_real_avoiding a d.z₁ (max 2 ‖c‖) (by rw [← hc_eq]; exact hz1ne)
  -- the real segment avoids the pair curve
  have hnotRay : ∀ θ : ℝ, (¬ ∃ n : ℤ, 2 * θ = (n : ℝ)) → ∀ y : ℝ,
      (y : ℂ) ∉ Work.EL.paramRay d.hN θ := by
    intro θ hθ y hy
    exact hθ (exists_int_two_mul_of_mem_paramRay hreal d.bottcher hy)
  have hz1avoid : ∀ y ∈ Set.uIcc a x, (y : ℂ) ≠ d.z₁ := by
    intro y hy hyz
    rcases hxav with him | hre
    · exact him (by rw [← hyz]; simp)
    · have h1 : d.z₁.re = y := by rw [← hyz]; simp
      rw [← h1] at hy
      exact hre hy
  have hseg : ∀ y ∈ Set.uIcc a x, (y : ℂ) ∉ Work.EL.pairCurve P := by
    intro y hy
    rw [Work.EL.mem_pairCurve_iff]
    rintro (h | h | h)
    · exact hnotRay Work.EL.alpha1 not_exists_int_two_mul_alpha1 y (by rwa [hPa] at h)
    · exact hz1avoid y hy (by rw [h, hPy])
    · exact hnotRay Work.EL.alpha2 not_exists_int_two_mul_alpha2 y (by rwa [hPb] at h)
  -- hence `x` lies in the far side as well
  have hx_mem : (x : ℂ) ∈ Work.EL.pairSide P := by
    have hSpre : IsPreconnected ((fun y : ℝ => (y : ℂ)) '' Set.uIcc a x) :=
      isPreconnected_uIcc.image _ Complex.continuous_ofReal.continuousOn
    have hSsub : ((fun y : ℝ => (y : ℂ)) '' Set.uIcc a x) ⊆ (Work.EL.pairCurve P)ᶜ := by
      rintro z ⟨y, hy, rfl⟩
      exact hseg y hy
    have hcS : c ∈ ((fun y : ℝ => (y : ℂ)) '' Set.uIcc a x) :=
      ⟨a, Set.left_mem_uIcc, hc_eq.symm⟩
    have hxS : (x : ℂ) ∈ ((fun y : ℝ => (y : ℂ)) '' Set.uIcc a x) :=
      ⟨x, Set.right_mem_uIcc, rfl⟩
    have hcomp := hSpre.subset_connectedComponentIn hcS hSsub
    have h2 : connectedComponentIn (Work.EL.pairCurve P)ᶜ c = Work.EL.pairSide P :=
      (connectedComponentIn_eq hcX).symm
    exact h2 ▸ hcomp hxS
  -- but `x` lies on one of the two real rays, which are in the near side
  have hInArc0 : Work.EL.InArc 0 P.b (P.a + 1) := by
    rw [hPb, hPa]
    norm_num [Work.EL.InArc, Work.EL.arcLen, Work.EL.alpha1, Work.EL.alpha2]
  have hInArcH : Work.EL.InArc (1 / 2) P.b (P.a + 1) := by
    rw [hPb, hPa]
    norm_num [Work.EL.InArc, Work.EL.arcLen, Work.EL.alpha1, Work.EL.alpha2]
  rcases real_mem_paramRay_zero_or_half hreal d.bottcher hxbig with h0 | hh
  · exact (Set.disjoint_left.mp hPS.disjoint hx_mem)
      (hPS.paramRay_near 0 hInArc0 h0)
  · exact (Set.disjoint_left.mp hPS.disjoint hx_mem)
      (hPS.paramRay_near (1 / 2) hInArcH hh)

end Work.FinalFix
