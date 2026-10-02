/-
# (P1) One-step pull-back of a co-landing pair, critical value *off* the arc side

`Work.ELPull.pb1_of_notMem` is the "critical value not in the side of the arc" form of the
one-step pull-back of a co-landing pair.  The pull-back statement itself (the existence of a
preimage `y'` of the landing point `Q.y` at which the two rays of the `T`-preimage arc
`preArc k I` of `I` co-land) is the content of `Work.ELPull.pb1Top`, which asks for the
critical value `c` to lie in the *other* side of the pair curve, `arcSide hN Q I.2 I.1`.

Here that membership is *derived*: the two sides of a pair curve exhaust its complement
(the hypothesis `hunion`, the two-sidedness of a co-landing pair), the critical value lies off
the pair curve — it is a point of the filled Julia set `K c` (`hN.paramRay_subset_compl`),
while the pair curve consists of the two rays (off `K c`) and the landing point `Q.y ≠ c` —
and `hcv` says that `c` is not in the side met by the arc `I`.  Hence `c` lies in the other
side, and `pb1Top` applies.

The two sides `arcSide hN Q I.1 I.2` and `arcSide hN Q I.2 I.1` of the *unwrapped* arc `I`
are identified with `arcSide hN Q Q.a Q.b` resp. `arcSide hN Q Q.b Q.a` (in the order imposed
by `IsUnwrappedArcOf`); this is the elementary `arcLen` arithmetic of
`rayPt_unwrap_fst`/`nb_rayPt_unwrap_snd` below, in which the ray points in the middle of the two
arcs are shown to be equal (the definition of `arcSide` only depends on that point).
-/
import Mathlib
import Submission.Work.ELPull.Defs
import Submission.Work.ELPull.pb1Top

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Set Function Filter
open scoped Topology

namespace Work.ELPull

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Elementary arithmetic of `arcLen` along an unwrapped arc -/

/-- The length of the arc from `a` to the *unwrapped* endpoint `a + arcLen a b` is `arcLen a b`:
the unwrapped endpoint represents the same angle as `b`. -/
private lemma nb_arcLen_self_add (a b : ℝ) : arcLen a (a + arcLen a b) = arcLen a b := by
  rw [arcLen, arcLen]
  rw [show a + Int.fract (b - a) - a = Int.fract (b - a) by ring]
  exact Int.fract_fract (b - a)

/-- The complementary arc lengths add up to `1`. -/
private lemma nb_arcLen_symm {a b : ℝ} (h : arcLen a b ≠ 0) : arcLen b a = 1 - arcLen a b := by
  rw [arcLen, arcLen]
  rw [show a - b = -(b - a) by ring]
  exact Int.fract_neg h

/-- An arc length is always `< 1`. -/
private lemma nb_arcLen_lt_one (a b : ℝ) : arcLen a b < 1 := Int.fract_lt_one (b - a)

/-- The complementary arc has non-zero length when the arc does (the two angles are not
congruent modulo `ℤ`). -/
private lemma nb_arcLen_ne_zero_of {a b : ℝ} (h : arcLen a b ≠ 0) : arcLen b a ≠ 0 := by
  have h1 := nb_arcLen_symm h
  have h2 := nb_arcLen_lt_one a b
  have h3 : 0 < arcLen a b := lt_of_le_of_ne (Int.fract_nonneg (b - a)) (Ne.symm h)
  linarith

/-! ## The two arc sides of an unwrapped arc are the two arc sides of the pair -/

/-- Replacing the unwrapped endpoint `b` of an arc by its representative `a + arcLen a b` does
not move the midpoint of the arc, hence does not move the ray point defining `arcSide`. -/
private lemma rayPt_unwrap_fst {c : ℂ} (hN : DynB c) (a b : ℝ) :
    hN.rayPt (a + arcLen a (a + arcLen a b) / 2) 2 = hN.rayPt (a + arcLen a b / 2) 2 := by
  rw [nb_arcLen_self_add]

/-- The midpoint of the *complementary* arc of the unwrapped arc `(a, a + arcLen a b)` is the
midpoint of the arc `(b, a)`, modulo `1`; the ray points therefore agree. -/
private lemma nb_rayPt_unwrap_snd {c : ℂ} (hN : DynB c) {a b : ℝ} (hab : arcLen a b ≠ 0) :
    hN.rayPt (a + arcLen a b + arcLen (a + arcLen a b) a / 2) 2
      = hN.rayPt (b + arcLen b a / 2) 2 := by
  set L := arcLen a b with hL
  have hLne : L ≠ 0 := hab
  have hself : arcLen a (a + L) = L := by rw [hL]; exact nb_arcLen_self_add a b
  have h1 : arcLen (a + L) a = 1 - L := by
    have h := nb_arcLen_symm (a := a) (b := a + L) (by rw [hself]; exact hLne)
    rwa [hself] at h
  have h2 : arcLen b a = 1 - L := nb_arcLen_symm hab
  have hfloor : (⌊b - a⌋ : ℝ) + L = b - a := by
    rw [hL, arcLen, Int.floor_add_fract]
  have hsign : a + L + (1 - L) / 2 = (b + (1 - L) / 2) + ((-⌊b - a⌋ : ℤ) : ℝ) := by
    push_cast; linarith
  rw [h1, h2, hsign, rayPt_periodic hN (b + (1 - L) / 2) 2 (-⌊b - a⌋) (by norm_num)]

/-- `arcSide` only depends on the ray point at the midpoint of the arc. -/
private lemma nb_arcSide_congr {c : ℂ} {hN : DynB c} (P : CoPair hN) {p q p' q' : ℝ}
    (h : hN.rayPt (p + arcLen p q / 2) 2 = hN.rayPt (p' + arcLen p' q' / 2) 2) :
    arcSide hN P p q = arcSide hN P p' q' := by
  simp only [arcSide, h]

/-! ## The reduction -/

theorem pb1_of_notMem {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) (hN : DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c)) (htop : PB1Top hN)
    (hunion : ∀ P : CoPair hN, arcLen P.a P.b ≠ 0 →
      arcSide hN P P.a P.b ∪ arcSide hN P P.b P.a = (pairCurve hN P)ᶜ)
    (Q : CoPair hN) (hab : arcLen Q.a Q.b ≠ 0) (I : ℝ × ℝ) (hI : IsUnwrappedArcOf Q I)
    (hcv : c ∉ arcSide hN Q I.1 I.2) (hy : Q.y ≠ c) (k : Fin 2) :
    ∃ y' : ℂ, LeanEval.ComplexAnalysis.Tantibar c y' = Q.y ∧
      LandsN hN (preArc k I).1 y' ∧ LandsN hN (preArc k I).2 y' := by
  -- The critical value is on the filled Julia set, hence off the pair curve: the pair curve
  -- consists of the two rays, which are off the filled Julia set, and the point `Q.y ≠ c`.
  have hcK : c ∈ K c := by
    have hb : Work.ParamRays.BoundedOrbit c 0 := (Work.ParamRays.mem_mandelbar_iff_bounded c).mp hc
    have h1 := hb.shift 1
    rw [show Work.ParamRays.orbit c 0 1 = c from Work.ParamRays.critOrbit_one c] at h1
    simpa [K, Work.ParamRays.filledJulia] using h1
  have hcRay : ∀ θ : ℝ, c ∉ hN.paramRay θ :=
    fun θ h => (hN.paramRay_subset_compl θ h) hcK
  have hcComp : c ∈ (pairCurve hN Q)ᶜ := by
    simp only [Set.mem_compl_iff, pairCurve, Set.mem_union, Set.mem_singleton_iff, not_or]
    exact ⟨⟨hcRay Q.a, fun h => hy h.symm⟩, hcRay Q.b⟩
  -- The two sides of `Q` exhaust the complement of its pair curve.
  have hUnion := hunion Q hab
  -- Hence `c` lies in the side complementary to the one it does not lie in, i.e. in
  -- `arcSide hN Q I.2 I.1`, which is what `pb1Top` needs.
  have hmain : c ∈ arcSide hN Q I.2 I.1 := by
    rcases hI with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- `I` is the arc from `Q.a` to `Q.b` (unwrapped)
      have hAB : arcSide hN Q I.1 I.2 = arcSide hN Q Q.a Q.b :=
        nb_arcSide_congr Q (by rw [h1, h2]; exact rayPt_unwrap_fst hN Q.a Q.b)
      have hBA : arcSide hN Q I.2 I.1 = arcSide hN Q Q.b Q.a :=
        nb_arcSide_congr Q (by rw [h1, h2]; exact nb_rayPt_unwrap_snd hN hab)
      have hcu : c ∈ arcSide hN Q Q.a Q.b ∪ arcSide hN Q Q.b Q.a := by
        rw [hUnion]; exact hcComp
      have hcA : c ∉ arcSide hN Q Q.a Q.b := by rw [← hAB]; exact hcv
      have hB : c ∈ arcSide hN Q Q.b Q.a := by
        rcases hcu with h | h; exacts [absurd h hcA, h]
      rwa [hBA]
    · -- `I` is the arc from `Q.b` to `Q.a` (unwrapped)
      have hba : arcLen Q.b Q.a ≠ 0 := nb_arcLen_ne_zero_of hab
      have hBA : arcSide hN Q I.1 I.2 = arcSide hN Q Q.b Q.a :=
        nb_arcSide_congr Q (by rw [h1, h2]; exact rayPt_unwrap_fst hN Q.b Q.a)
      have hAB : arcSide hN Q I.2 I.1 = arcSide hN Q Q.a Q.b :=
        nb_arcSide_congr Q (by rw [h1, h2]; exact nb_rayPt_unwrap_snd hN hba)
      have hcu : c ∈ arcSide hN Q Q.a Q.b ∪ arcSide hN Q Q.b Q.a := by
        rw [hUnion]; exact hcComp
      have hcB : c ∉ arcSide hN Q Q.b Q.a := by rw [← hBA]; exact hcv
      have hA : c ∈ arcSide hN Q Q.a Q.b := by
        rcases hcu with h | h; exacts [h, absurd h hcB]
      rwa [hAB]
  exact pb1Top hc hN hφ htop Q hab I hI hmain k

end Work.ELPull
