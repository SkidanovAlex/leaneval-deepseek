/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# `d1Chart` is **not** sound as stated, and is sound once `U,V ≥ 0` are also required

`Work.SeedCert.d1Chart W P U V L` (file `Submission/Work/SeedCertNum/D1.lean`) is the kernel-checkable
test behind the interval pull-back chain of `NOTES_LEAD_mandelbar_noncusp.md` §2.4.  Its intended
meaning is that `U` is an *upper* witness for `√(x₂²+M²)` and `V` an upper witness for
`√(x₁²+M²)`, so that the emitted square-root box `symBox P` encloses the preimage of `W`.

The kernel test, however, only compares *squares*: it checks `x₂²+M² ≤ U²` and `x₁²+M² ≤ V²`
(conditions `hC4`,`hC5` of `D1.lean`) and never `0 ≤ U`, `0 ≤ V`.  Since `(-U)² = U²`, a negative
witness passes the test, and then `√(x₂²+M²) ≤ U` *fails*: the enclosure conclusion is false.
`d1Chart_sound_counterexample` below is a machine-checked counterexample to the statement
`Work.SeedCertNum.d1Chart_sound` exactly as it is written in
`Submission/Work/SeedCertNum/d1Chart_sound.lean`.

The repair is minimal: keep the test as it is and require `Dya.nonneg U`, `Dya.nonneg V` of the
*witnesses* (as the design of the generator guarantees them: it emits `U ≥ √(x₂²+M²) ≥ 0`).  This is
what `d1Chart_sound_nonneg` proves: with `0 ≤ U`, `0 ≤ V` the intended soundness statement is true,
for arbitrary boxes `W`, `P`.

## Contents

* `sqrt_sq_add_sq_add_nonneg`, `sqrt_sq_add_sq_add_mono`, `sqrt_sq_add_sq_sub_mono` — the real
  monotonicity facts for `f(x,y) = √(x²+y²) + x` (`f` is increasing in `x` and in `|y|`; it is `≥ 0`);
* `Dya.toReal_maxAbs`, `Dya.maxAbs_nonneg`, `abs_le_maxAbs`, `abs_minAbs_toReal_le_abs` — the
  endpoint bounds `|y| ≤ maxAbs` and `|minAbs| ≤ |y|` for `y` in a dyadic interval;
* `d1Chart_sound_counterexample` — the refutation of `d1Chart_sound` as written;
* `d1Chart_sound_nonneg` — the corrected soundness statement.
-/
import Submission.Work.SeedCertNum.D1
import Submission.Work.SeedCertNum.Box
import Submission.Work.SeedCertNum.Dyadic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

open Work.SeedCert

theorem toReal_maxAbs (a b : Dya) : (Dya.maxAbs a b).toReal = max |a.toReal| |b.toReal| := by
  simp only [Dya.maxAbs, Dya.toReal_max, Dya.toReal_abs]

theorem maxAbs_nonneg (a b : Dya) : 0 ≤ (Dya.maxAbs a b).toReal := by
  rw [toReal_maxAbs]
  exact le_trans (abs_nonneg a.toReal) (le_max_left _ _)

/-! ## Real monotonicity of `√(x²+y²) + x` -/

/-- `√(x²+y²) + x ≥ 0`: indeed `√(x²+y²) ≥ |x| ≥ -x`. -/
theorem sqrt_sq_add_sq_add_nonneg (x y : ℝ) : 0 ≤ Real.sqrt (x ^ 2 + y ^ 2) + x := by
  have h : |x| ≤ Real.sqrt (x ^ 2 + y ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])
  linarith [neg_abs_le x]

/-- `x ↦ √(x²+y²) + x` is nondecreasing.  (The key point: `√(x²+y²) + x ≥ 0` for *all* `x`, so
`√(x'²+y²) - √(x²+y²) = (x'-x)(x'+x)/(√(x'²+y²)+√(x²+y²))` can be compared with `x' - x` even when
`x < 0`.) -/
theorem sqrt_sq_add_sq_add_mono_x {x x' y : ℝ} (h : x ≤ x') :
    Real.sqrt (x ^ 2 + y ^ 2) + x ≤ Real.sqrt (x' ^ 2 + y ^ 2) + x' := by
  set s := Real.sqrt (x ^ 2 + y ^ 2) with hs
  set t := Real.sqrt (x' ^ 2 + y ^ 2) with ht
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hs2 : s ^ 2 = x ^ 2 + y ^ 2 := by rw [hs]; exact Real.sq_sqrt (by positivity)
  have ht2 : t ^ 2 = x' ^ 2 + y ^ 2 := by rw [ht]; exact Real.sq_sqrt (by positivity)
  have hFs : 0 ≤ s + x := by rw [hs]; exact sqrt_sq_add_sq_add_nonneg x y
  have hFt : 0 ≤ t + x' := by rw [ht]; exact sqrt_sq_add_sq_add_nonneg x' y
  have hkey : (s - t) * (s + t) ≤ (x' - x) * (s + t) := by
    have h1 : 0 ≤ (x' - x) * ((s + x) + (t + x')) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hs2, ht2, h1]
  rcases lt_or_eq_of_le (by linarith : (0 : ℝ) ≤ s + t) with hpos | heq
  · have := le_of_mul_le_mul_right hkey hpos
    linarith
  · have hse : s = 0 := by linarith
    have hte : t = 0 := by linarith
    linarith

/-- `(x,y) ↦ √(x²+y²) + x` is nondecreasing in `x` and in `|y|`. -/
theorem sqrt_sq_add_sq_add_mono {x x' y y' : ℝ} (hx : x ≤ x') (hy : |y| ≤ |y'|) :
    Real.sqrt (x ^ 2 + y ^ 2) + x ≤ Real.sqrt (x' ^ 2 + y' ^ 2) + x' := by
  have h1 := sqrt_sq_add_sq_add_mono_x (y := y) hx
  have h2 : Real.sqrt (x' ^ 2 + y ^ 2) + x' ≤ Real.sqrt (x' ^ 2 + y' ^ 2) + x' := by
    have hsq : y ^ 2 ≤ y' ^ 2 := (sq_le_sq).mpr hy
    have := Real.sqrt_le_sqrt (show x' ^ 2 + y ^ 2 ≤ x' ^ 2 + y' ^ 2 by linarith)
    linarith
  linarith

/-- `(x,y) ↦ √(x²+y²) - x` is nonincreasing in `x` (it is `f(-x,y)`) and nondecreasing in `|y|`. -/
theorem sqrt_sq_add_sq_sub_mono {x x' y y' : ℝ} (hx : x' ≤ x) (hy : |y| ≤ |y'|) :
    Real.sqrt (x ^ 2 + y ^ 2) - x ≤ Real.sqrt (x' ^ 2 + y' ^ 2) - x' := by
  have hh := sqrt_sq_add_sq_add_mono (x := -x) (x' := -x') (y := y) (y' := y') (by linarith) hy
  simp only [neg_sq] at hh
  linarith

/-! ## Endpoint bounds for a dyadic interval -/


/-- `|x| ≤ maxAbs` for `x` in the interval. -/
theorem abs_le_maxAbs {a b : Dya} {x : ℝ} (ha : a.toReal ≤ x) (hb : x ≤ b.toReal) :
    |x| ≤ (Dya.maxAbs a b).toReal := by
  rw [toReal_maxAbs]
  exact abs_le_max_abs_abs ha hb

/-- `|minAbs| ≤ |x|` for `x` in the interval: `minAbs` is the element of the interval of minimal
absolute value.  (Note that `Dya.minAbs` itself may be *negative*, so this is strictly stronger than
`Dya.minAbs_le_abs`, which gives `minAbs ≤ |x|`; the square-root test needs `minAbs² ≤ x²`.) -/
theorem abs_minAbs_toReal_le_abs {a b : Dya} {x : ℝ} (ha : a.toReal ≤ x) (hb : x ≤ b.toReal) :
    |(Dya.minAbs a b).toReal| ≤ |x| := by
  rw [Dya.toReal_minAbs]
  rcases le_total 0 a.toReal with h0a | h0a
  · have h0b : 0 ≤ b.toReal := le_trans h0a (le_trans ha hb)
    rw [min_eq_right h0b, max_eq_left h0a, abs_of_nonneg h0a]
    exact le_trans ha (le_abs_self x)
  · rcases le_total 0 b.toReal with h0b | h0b
    · rw [min_eq_right h0b, max_eq_right h0a]
      simp
    · have hab : a.toReal ≤ b.toReal := le_trans ha hb
      have hxle : x ≤ 0 := le_trans hb h0b
      rw [min_eq_left h0b, max_eq_right hab, abs_of_nonpos h0b, abs_of_nonpos hxle]
      linarith

/-! ## `d1Chart_sound` as written is false -/

/-- **The statement `Work.SeedCertNum.d1Chart_sound` of
`Submission/Work/SeedCertNum/d1Chart_sound.lean` is false.**  The test of `D1.lean` checks the
*witnesses' squares* (`x₂²+M² ≤ U²`, `x₁²+M² ≤ V²`) but never their *signs*, although the soundness
argument needs `U ≥ √(x₂²+M²) ≥ 0` and `V ≥ √(x₁²+M²) ≥ 0`.  Because `(-U)² = U²`, a negative
witness `U` passes the test and destroys the conclusion.

Explicit counterexample: `W = [4,5] × {0}`, `P = [1,1] × [0,1]`, `U = -5`, `V = 4`, `L = 4`.  Then
`d1Chart W P U V L = true`, but `w = 5 ∈ W` has the square root `v = √5`, whose real part
`√5 > 1 = P.rhi` rules out both `v ∈ symBox P = [1,1]×[-1,1]` and `v ∈ (symBox P).neg =
[-1,-1]×[-1,1]`. -/
theorem d1Chart_sound_counterexample :
    ∃ (W P : CBox) (U V L : Dya) (w v : ℂ),
      d1Chart W P U V L = true ∧ w ∈ W.toSet ∧ v ^ 2 = w ∧
      ¬ (v ∈ (symBox P).toSet ∨ v ∈ (symBox P).neg.toSet) := by
  refine ⟨{ rlo := Dya.ofInt 4, rhi := Dya.ofInt 5, ilo := Dya.ofInt 0, ihi := Dya.ofInt 0 },
    { rlo := Dya.ofInt 1, rhi := Dya.ofInt 1, ilo := Dya.ofInt 0, ihi := Dya.ofInt 1 },
    Dya.ofInt (-5), Dya.ofInt 4, Dya.ofInt 4, (5 : ℂ), (Real.sqrt 5 : ℂ), by decide, ?_, ?_, ?_⟩
  · norm_num [CBox.toSet, Dya.toReal_ofInt]
  · rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  · have h5 : (1 : ℝ) < Real.sqrt 5 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
    rintro (h | h)
    · simp only [symBox, CBox.toSet, Dya.toReal_ofInt, Dya.toReal_neg, Set.mem_ofPred_eq,
        Complex.ofReal_re, Complex.ofReal_im] at h
      obtain ⟨_, hle, _⟩ := h
      norm_num at hle
    · simp only [symBox, CBox.neg, CBox.toSet, Dya.toReal_ofInt, Dya.toReal_neg, Dya.neg_neg,
        Set.mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im] at h
      obtain ⟨_, hle, _⟩ := h
      norm_num at hle
      linarith

/-! ## The corrected soundness statement -/

/-- **Soundness of the D1 square-root enclosure test, with the missing sign hypotheses.**  If
`d1Chart W P U V L = true` *and* the witnesses `U`, `V` are nonnegative, then every square root of
every `w ∈ W` lies in `C = symBox P = [P.rlo,P.rhi] × [-P.ihi,P.ihi]` or in `-C`.

The proof follows the sketch of `NOTES_LEAD_mandelbar_noncusp.md` §2.4, but note that the step
"`x ≤ x₂` and `|y| ≤ M` give `√(x²+y²) ≤ √(x₂²+M²)`" used there needs the *sum* form
`√(x²+y²)+x ≤ √(x₂²+M²)+x₂` (`sqrt_sq_add_sq_add_mono`), which is true even for negative `x`
whereas the displayed inequality is not. -/
theorem d1Chart_sound_nonneg {W P : CBox} {U V L : Dya}
    (h : d1Chart W P U V L = true) (hUnn : Dya.nonneg U = true) (hVnn : Dya.nonneg V = true) :
    ∀ w : ℂ, w ∈ W.toSet → ∀ v : ℂ, v ^ 2 = w →
      v ∈ (symBox P).toSet ∨ v ∈ (symBox P).neg.toSet := by
  -- unpack the kernel test
  have hh := h
  simp only [d1Chart, Bool.and_eq_true] at hh
  obtain ⟨hPg, hCg⟩ := hh
  obtain ⟨⟨⟨hP1, hP2⟩, hP3⟩, hP4⟩ := hPg
  obtain ⟨hXg, hC6⟩ := hCg
  obtain ⟨⟨⟨⟨hC1, hC2⟩, hC3⟩, hC4⟩, hC5⟩ := hXg
  have hP1' : 0 < P.rlo.toReal := (Dya.toReal_pos_iff P.rlo).mp hP1
  have hP2' : P.rlo.toReal ≤ P.rhi.toReal := (Dya.toReal_le_iff P.rlo P.rhi).mp hP2
  have hP3' : 0 < P.ihi.toReal := (Dya.toReal_pos_iff P.ihi).mp hP3
  have hP4' : 0 ≤ L.toReal := (Dya.toReal_nonneg_iff L).mp hP4
  have hP_rhi_pos : 0 < P.rhi.toReal := lt_of_lt_of_le hP1' hP2'
  have hUnn' : 0 ≤ U.toReal := (Dya.toReal_nonneg_iff U).mp hUnn
  have hVnn' : 0 ≤ V.toReal := (Dya.toReal_nonneg_iff V).mp hVnn
  have hC1' : U.toReal + W.rhi.toReal ≤ 2 * (P.rhi.toReal * P.rhi.toReal) := by
    have := (Dya.toReal_le_iff _ _).mp hC1
    simpa [Dya.toReal_add, Dya.toReal_twice, Dya.toReal_mul] using this
  have hC2' : V.toReal - W.rlo.toReal ≤ 2 * (P.ihi.toReal * P.ihi.toReal) := by
    have := (Dya.toReal_le_iff _ _).mp hC2
    simpa [Dya.toReal_sub, Dya.toReal_twice, Dya.toReal_mul] using this
  have hC3' : 2 * (P.rlo.toReal * P.rlo.toReal) ≤ L.toReal + W.rlo.toReal := by
    have := (Dya.toReal_le_iff _ _).mp hC3
    simpa [Dya.toReal_add, Dya.toReal_twice, Dya.toReal_mul] using this
  have hC4' : W.rhi.toReal ^ 2 + (Dya.maxAbs W.ilo W.ihi).toReal ^ 2 ≤ U.toReal ^ 2 := by
    have := (Dya.toReal_le_iff _ _).mp hC4
    simpa [Dya.toReal_add, Dya.toReal_mul, pow_two] using this
  have hC5' : W.rlo.toReal ^ 2 + (Dya.maxAbs W.ilo W.ihi).toReal ^ 2 ≤ V.toReal ^ 2 := by
    have := (Dya.toReal_le_iff _ _).mp hC5
    simpa [Dya.toReal_add, Dya.toReal_mul, pow_two] using this
  have hC6' : L.toReal ^ 2 ≤ W.rlo.toReal ^ 2 + (Dya.minAbs W.ilo W.ihi).toReal ^ 2 := by
    have := (Dya.toReal_le_iff _ _).mp hC6
    simpa [Dya.toReal_add, Dya.toReal_mul, pow_two] using this
  intro w hw v hv
  rw [CBox.mem_toSet] at hw
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
  -- endpoint bounds of the imaginary coordinate
  have hMnonneg : 0 ≤ (Dya.maxAbs W.ilo W.ihi).toReal := maxAbs_nonneg W.ilo W.ihi
  have hyM : |w.im| ≤ (Dya.maxAbs W.ilo W.ihi).toReal := abs_le_maxAbs hw3 hw4
  have hyM' : |w.im| ≤ |(Dya.maxAbs W.ilo W.ihi).toReal| := by
    rwa [abs_of_nonneg hMnonneg]
  have hmabs : |(Dya.minAbs W.ilo W.ihi).toReal| ≤ |w.im| := abs_minAbs_toReal_le_abs hw3 hw4
  -- complex algebra of `v² = w`
  have hre : v.re ^ 2 - v.im ^ 2 = w.re := by
    have := congrArg Complex.re hv
    simpa [pow_two, Complex.mul_re] using this
  have hnorm : ‖w‖ = v.re ^ 2 + v.im ^ 2 := by
    rw [← hv, norm_pow, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hnsqrt : ‖w‖ = Real.sqrt (w.re ^ 2 + w.im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    ring
  have ha2 : v.re ^ 2 = (Real.sqrt (w.re ^ 2 + w.im ^ 2) + w.re) / 2 := by linarith
  have hb2 : v.im ^ 2 = (Real.sqrt (w.re ^ 2 + w.im ^ 2) - w.re) / 2 := by linarith
  -- the two square-root witnesses
  have hsqrtU : Real.sqrt (W.rhi.toReal ^ 2 + (Dya.maxAbs W.ilo W.ihi).toReal ^ 2) ≤ U.toReal := by
    rw [Real.sqrt_le_iff]
    exact ⟨hUnn', hC4'⟩
  have hsqrtV : Real.sqrt (W.rlo.toReal ^ 2 + (Dya.maxAbs W.ilo W.ihi).toReal ^ 2) ≤ V.toReal := by
    rw [Real.sqrt_le_iff]
    exact ⟨hVnn', hC5'⟩
  have hLsqrt : L.toReal ≤ Real.sqrt (W.rlo.toReal ^ 2 + (Dya.minAbs W.ilo W.ihi).toReal ^ 2) := by
    rw [Real.le_sqrt hP4' (by positivity)]
    exact hC6'
  -- the three real bounds
  have hFup : Real.sqrt (w.re ^ 2 + w.im ^ 2) + w.re ≤ U.toReal + W.rhi.toReal := by
    have h1 := sqrt_sq_add_sq_add_mono (x := w.re) (x' := W.rhi.toReal) (y := w.im)
      (y' := (Dya.maxAbs W.ilo W.ihi).toReal) hw2 hyM'
    linarith [h1, hsqrtU]
  have hFdn : Real.sqrt (w.re ^ 2 + w.im ^ 2) - w.re ≤ V.toReal - W.rlo.toReal := by
    have h1 := sqrt_sq_add_sq_sub_mono (x := w.re) (x' := W.rlo.toReal) (y := w.im)
      (y' := (Dya.maxAbs W.ilo W.ihi).toReal) hw1 hyM'
    linarith [h1, hsqrtV]
  have hFlo : L.toReal + W.rlo.toReal ≤ Real.sqrt (w.re ^ 2 + w.im ^ 2) + w.re := by
    have h1 := sqrt_sq_add_sq_add_mono (x := W.rlo.toReal) (x' := w.re)
      (y := (Dya.minAbs W.ilo W.ihi).toReal) (y' := w.im) hw1 hmabs
    linarith [h1, hLsqrt]
  -- the modulus bounds on `v`
  have habs_hi : |v.re| ≤ P.rhi.toReal := by
    have h1 : v.re ^ 2 ≤ P.rhi.toReal ^ 2 := by
      have h2 : Real.sqrt (w.re ^ 2 + w.im ^ 2) + w.re ≤ 2 * (P.rhi.toReal * P.rhi.toReal) :=
        le_trans hFup hC1'
      rw [ha2]; linarith
    have := (sq_le_sq).mp h1
    rwa [abs_of_pos hP_rhi_pos] at this
  have habs_lo : P.rlo.toReal ≤ |v.re| := by
    have h1 : P.rlo.toReal ^ 2 ≤ v.re ^ 2 := by
      have h2 : 2 * (P.rlo.toReal * P.rlo.toReal) ≤ Real.sqrt (w.re ^ 2 + w.im ^ 2) + w.re :=
        le_trans hC3' hFlo
      rw [ha2]; linarith
    have := (sq_le_sq).mp h1
    rwa [abs_of_pos hP1'] at this
  have hbabs : |v.im| ≤ P.ihi.toReal := by
    have h1 : v.im ^ 2 ≤ P.ihi.toReal ^ 2 := by
      have h2 : Real.sqrt (w.re ^ 2 + w.im ^ 2) - w.re ≤ 2 * (P.ihi.toReal * P.ihi.toReal) :=
        le_trans hFdn hC2'
      rw [hb2]; linarith
    have := (sq_le_sq).mp h1
    rwa [abs_of_pos hP3'] at this
  -- assemble
  rcases le_total 0 v.re with ha | ha
  · left
    rw [CBox.mem_toSet]
    simp only [symBox, Dya.toReal_neg]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hva : |v.re| = v.re := abs_of_nonneg ha
      linarith
    · exact le_trans (le_abs_self v.re) habs_hi
    · linarith [(abs_le.mp hbabs).1]
    · linarith [(abs_le.mp hbabs).2]
  · right
    have hva : |v.re| = -v.re := abs_of_nonpos ha
    have hneg : -v ∈ (symBox P).toSet := by
      rw [CBox.mem_toSet]
      simp only [symBox, Dya.toReal_neg, Complex.neg_re, Complex.neg_im]
      refine ⟨?_, ?_, ?_, ?_⟩
      · linarith [habs_lo, hva]
      · linarith [habs_hi, hva]
      · linarith [(abs_le.mp hbabs).2]
      · linarith [(abs_le.mp hbabs).1]
    simpa using CBox.mem_neg hneg

end Work.SeedCertNum
