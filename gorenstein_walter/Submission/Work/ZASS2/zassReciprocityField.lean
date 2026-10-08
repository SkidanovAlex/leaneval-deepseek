import Mathlib
import Submission.Work.ZASS.Leaf9

namespace Work.ZASS2

open Work.GW2

/-! # ZASS2 leaf Z6.5': the reciprocity field statement (`Work.GW2.ZassReciprocityFieldProp`, `Submission/Work/ZASS/Leaf9.lean`)

Pure field theory, independent of all group theory.  Model-checked exhaustively (all
`(c₊, c₋)`) for `q = 5, 7, 9, 11, 13, 17, 19, 23, 25, 27, 29, 49`, and by the reviewers for
the prime fields `q ≤ 47`; the three-point rule `(ZassStep S a)^3 = id` is what forces
`c₊ = c₋`.

Route (refined after review):
1. Equivariance gives `S x = c₊/x` on squares and `S x = c₋/x` on non-squares (pick a
   non-square `ρ`; the two orbits of square-scaling are `E²∖0` and `ρE²`).
2. The involution law at a square forces `c₋ = c₊` if `c₊` is a non-square (and symmetrically);
   so `c₊` and `c₋` always lie in the same square class.
3. `¬ IsSquare (-1)`: if `c₊ = r^2` then one of `±r` is a square and is a fixed point of `S`,
   excluded. So `c₊` is a non-square and step 2 applies (HB 1.12).
4. `IsSquare (-1)`: assume both constants are squares.  Take `a` with `a^2 = -1/c₊` **with the
   original `S`** (no conjugation needed): then `ZassStep S a` sends `none ↦ some 1` (always),
   `some 0 ↦ none` (always) and `some 1 ↦ some (a^2 * c₊ + 1) = some 0`, so `(ZassStep S a)^3`
   fixes `none`, `some 0`, `some 1` and the third hypothesis gives `(ZassStep S a)^3 = id`.
   Pick a square `e` with `e - 1` a non-square (exists: otherwise `E² ∪ {0}` would be closed
   under `-1` and under square scaling, hence additive, but `(q+1)/2 ∤ q`); evaluating
   `(ZassStep S a)^3 e = e` gives `k = -c₋/c₊ = -1`, i.e. `c₋ = c₊` (HB 1.11, p. 179).
5. `-c` is a square: for `d` even use the fixed point `x₀` (`c = x₀^2` and `-1` is a square);
   for `d` odd both `c` and `-1` are non-squares.
Finally take `c := c₊` (`= c₋`); note `(2 : E) ≠ 0` supplies `-1 ≠ 1` and `(-x)^2 = x^2`.

The formalisation below follows this route.  The one place where we deviate from the sketch
above is the existence of `e`: instead of the "`E² ∪ {0}` is a subfield" argument, we use the
Möbius substitution `x = (t + 1)/(1 - t)` for a nonsquare `t`, which gives `x² - 1` a
nonsquare at once. -/

section Aux

/-- In a finite field of odd characteristic, a product of two nonzero elements is a square
iff the two factors are both squares or both nonsquares. -/
lemma isSqMulIff (E : Type*) [Field E] [Fintype E] (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) :
    (IsSquare (x * y) ↔ (IsSquare x ↔ IsSquare y)) := by
  classical
  have hx1 := quadraticChar_one_iff_isSquare hx
  have hy1 := quadraticChar_one_iff_isSquare hy
  have hxy1 := quadraticChar_one_iff_isSquare (mul_ne_zero hx hy)
  have hmul := map_mul (quadraticChar E) x y
  constructor
  · intro h
    have hq : quadraticChar E (x * y) = 1 := hxy1.mpr h
    rw [hmul] at hq
    constructor
    · intro hxs; rw [hx1.mpr hxs, one_mul] at hq; exact hy1.mp hq
    · intro hys; rw [hy1.mpr hys, mul_one] at hq; exact hx1.mp hq
  · intro h
    apply hxy1.mp
    rw [hmul]
    rcases h with ⟨h1, h2⟩
    by_cases hxs : IsSquare x
    · rw [hx1.mpr hxs, hy1.mpr (h1 hxs)]; norm_num
    · rw [quadraticChar_neg_one_iff_not_isSquare.mpr hxs,
          quadraticChar_neg_one_iff_not_isSquare.mpr (fun hy' => hxs (h2 hy'))]; norm_num

/-- The inverse of a square is a square. -/
lemma inv_sq {E : Type*} [Field E] (b : E) (h : IsSquare b) : IsSquare b⁻¹ := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s⁻¹, by rw [hs, mul_inv_rev]⟩

/-- A finite field of odd characteristic has a nonsquare. -/
lemma exists_not_isSquare (E : Type*) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0) :
    ∃ ρ : E, ¬ IsSquare ρ := by
  by_contra h
  push Not at h
  have hsurj : Function.Surjective (fun x : E => x * x) := fun y => by
    obtain ⟨r, hr⟩ := h y
    exact ⟨r, hr.symm⟩
  have hinj : Function.Injective (fun x : E => x * x) :=
    Finite.injective_iff_surjective.mpr hsurj
  have h1 : (1 : E) = -1 := hinj (by show (1 : E) * 1 = (-1) * (-1); ring)
  have hh : (1 : E) + 1 = (-1) + 1 := congrArg (fun x : E => x + 1) h1
  exact h2 (by rw [show (2 : E) = 1 + 1 by norm_num, hh]; ring)

/-- In a finite field of odd characteristic in which `-1` is a square, there is a nonzero
square `e` with `e - 1` a nonsquare. -/
lemma exists_isSquare_sub_one_not_isSquare (E : Type*) [Field E] [Fintype E]
    (h2 : (2 : E) ≠ 0) (hneg : IsSquare (-1 : E)) :
    ∃ e : E, e ≠ 0 ∧ IsSquare e ∧ ¬ IsSquare (e - 1) := by
  obtain ⟨t, ht⟩ := exists_not_isSquare E h2
  have ht1 : t ≠ 1 := fun h => ht (by rw [h]; exact IsSquare.one)
  have h1mt : (1 : E) - t ≠ 0 := sub_ne_zero.mpr (fun h => ht1 h.symm)
  have hx0 : (t + 1) / (1 - t) ≠ 0 := by
    intro hx
    rcases div_eq_zero_iff.mp hx with h | h
    · exact ht (by rw [eq_neg_of_add_eq_zero_left h]; exact hneg)
    · exact absurd h h1mt
  refine ⟨((t + 1) / (1 - t)) ^ 2, pow_ne_zero 2 hx0,
    ⟨(t + 1) / (1 - t), by rw [sq]⟩, ?_⟩
  have hee : ((t + 1) / (1 - t)) ^ 2 - 1 = (2 / (1 - t)) ^ 2 * t := by
    field_simp; ring
  rw [hee]
  have hs2 : IsSquare ((2 / (1 - t)) ^ 2) := ⟨2 / (1 - t), by ring⟩
  have ht0 : t ≠ 0 := fun h => ht (by rw [h]; exact IsSquare.zero)
  have h2' : (2 / (1 - t)) ^ 2 ≠ 0 := pow_ne_zero 2 (div_ne_zero h2 h1mt)
  rw [isSqMulIff E ((2 / (1 - t)) ^ 2) t h2' ht0]
  intro hcon; exact absurd (hcon.mp hs2) ht

lemma iterate_three {α : Type*} (f : α → α) (x : α) : f^[3] x = f (f (f x)) := by
  simp [Function.iterate_succ_apply']

lemma zassStep_none {E : Type} [Field E] (S : E → E) (a : E) :
    ZassStep S a none = some 1 := by simp [ZassStep, ZassSbar]

lemma zassStep_zero {E : Type} [Field E] (S : E → E) (a : E) :
    ZassStep S a (some 0) = none := by simp [ZassStep, ZassSbar]

lemma zassStep_some {E : Type} [Field E] (S : E → E) (a y : E) (hy : y ≠ 0) :
    ZassStep S a (some y) = some (a ^ 2 * S y + 1) := by simp [ZassStep, ZassSbar, hy]

end Aux

theorem zassReciprocityField : Work.GW2.ZassReciprocityFieldProp := by
  intro E _ _ S h2 hS0 hSS hEqv hNoFix hThree hFix
  classical
  obtain ⟨ρ, hρ⟩ := exists_not_isSquare E h2
  have hρ0 : ρ ≠ 0 := fun h => hρ (by rw [h]; exact IsSquare.zero)
  let cp : E := S 1
  let cm : E := S ρ * ρ
  have hcp : cp = S 1 := rfl
  have hcm : cm = S ρ * ρ := rfl
  have hcp0 : cp ≠ 0 := by rw [hcp]; exact hS0 1 one_ne_zero
  have hcm0 : cm ≠ 0 := by
    rw [hcm]; exact mul_ne_zero (hS0 ρ hρ0) hρ0
  -- `S x = cp / x` on nonzero squares
  have hform_sq : ∀ x, x ≠ 0 → IsSquare x → S x = cp / x := by
    intro x hx0 hxsq
    obtain ⟨b, hb⟩ := hxsq
    have hb0 : b ≠ 0 := fun h => hx0 (by rw [hb, h, mul_zero])
    have h1 : S (b ^ 2 * 1) = S 1 / b ^ 2 := hEqv b 1 hb0 one_ne_zero
    rw [mul_one, ← hcp] at h1
    rw [show x = b ^ 2 by rw [hb]; ring, h1]
  -- `S x = cm / x` on nonzero nonsquares
  have hform_ns : ∀ x, x ≠ 0 → ¬ IsSquare x → S x = cm / x := by
    intro x hx0 hxns
    have hsq : IsSquare (x / ρ) := by
      rw [div_eq_mul_inv]
      apply (isSqMulIff E x ρ⁻¹ hx0 (inv_ne_zero hρ0)).mpr
      exact ⟨fun hx' => absurd hx' hxns,
        fun h => absurd (by have := inv_sq ρ⁻¹ h; rwa [inv_inv] at this) hρ⟩
    obtain ⟨b, hb⟩ := hsq
    have hb0 : b ≠ 0 := fun h => (div_ne_zero hx0 hρ0) (by rw [hb, h, mul_zero])
    have hxeq : x = b ^ 2 * ρ := by
      have h1 : x / ρ = b ^ 2 := by rw [hb]; ring
      rw [show x = (x / ρ) * ρ from (div_mul_cancel₀ x hρ0).symm, h1]
    have hSx : S x = S ρ / b ^ 2 := by rw [hxeq, hEqv b ρ hb0 hρ0]
    have hdiv : cm / x = S ρ / b ^ 2 := by rw [hcm, hxeq]; field_simp
    rw [hSx, hdiv]
  -- Step B: the involution law relates `cp` and `cm`
  have hBp : ¬ IsSquare cp → cp = cm := by
    intro hnc
    have hSS1 : S cp = 1 := by
      have := hSS 1 one_ne_zero
      rwa [show S 1 = cp from hcp.symm] at this
    have hone : cm / cp = 1 := by
      rw [← hform_ns cp hcp0 hnc]; exact hSS1
    exact ((div_eq_one_iff_eq hcp0).mp hone).symm
  have hBm : ¬ IsSquare cm → cp = cm := by
    intro hnc
    have hSρ : S ρ = cm / ρ := hform_ns ρ hρ0 hρ
    have hSSρ : S (cm / ρ) = ρ := by
      have := hSS ρ hρ0
      rwa [hSρ] at this
    have hcn : cm / ρ ≠ 0 := div_ne_zero hcm0 hρ0
    have hsq : IsSquare (cm / ρ) := by
      rw [div_eq_mul_inv]
      apply (isSqMulIff E cm ρ⁻¹ hcm0 (inv_ne_zero hρ0)).mpr
      exact ⟨fun hc => absurd hc hnc,
        fun h => absurd (by have := inv_sq ρ⁻¹ h; rwa [inv_inv] at this) hρ⟩
    have hval : cp / (cm / ρ) = ρ := by rw [← hform_sq (cm / ρ) hcn hsq]; exact hSSρ
    have hmul : cp = ρ * (cm / ρ) := (div_eq_iff hcn).mp hval
    rw [mul_div_cancel₀ cm hρ0] at hmul
    exact hmul
  have hclass : IsSquare cp ↔ IsSquare cm := by
    constructor
    · intro hs; by_contra hn; exact hn (hBm hn ▸ hs)
    · intro hs; by_contra hn; exact hn (hBp hn ▸ hs)
  rcases em (IsSquare (-1 : E)) with hneg | hneg
  · -- Case `IsSquare (-1)`: the `d`-even branch, using the three-point rule.
    obtain ⟨x₀, hx₀0, hx₀⟩ := hFix hneg
    have hcpsq : IsSquare cp := by
      rcases em (IsSquare x₀) with hs | hns
      · have hSx : S x₀ = cp / x₀ := hform_sq x₀ hx₀0 hs
        have hc : cp = x₀ * x₀ := by rw [hSx] at hx₀; exact (div_eq_iff hx₀0).mp hx₀
        exact ⟨x₀, hc⟩
      · have hcmsq : IsSquare cm := by
          have hSx : S x₀ = cm / x₀ := hform_ns x₀ hx₀0 hns
          have hc : cm = x₀ * x₀ := by rw [hSx] at hx₀; exact (div_eq_iff hx₀0).mp hx₀
          exact ⟨x₀, hc⟩
        exact hclass.mpr hcmsq
    have hsqneg : IsSquare (-1 / cp) := by
      rw [show (-1 / cp : E) = (-1) * cp⁻¹ by rw [div_eq_mul_inv]]
      exact IsSquare.mul hneg (inv_sq cp hcpsq)
    obtain ⟨a, ha⟩ := hsqneg
    have ha0 : a ≠ 0 := fun h =>
      (div_ne_zero (neg_ne_zero.mpr one_ne_zero) hcp0) (by rw [ha, h, mul_zero])
    have hak : a ^ 2 * cp = -1 := by rw [sq, ← ha, div_mul_cancel₀ (-1) hcp0]
    have hak2 : a ^ 2 * cm = -cm / cp := by
      have h1 : (a ^ 2 * cp) * (cm / cp) = a ^ 2 * cm := by field_simp
      rw [← h1, hak]; ring
    have hz0 : a ^ 2 * S 1 + 1 = 0 := by rw [← hcp, hak]; ring
    -- `g = ZassStep S a` is a permutation of order dividing `3`
    have hg3 : ∀ y : Option E, (ZassStep S a)^[3] y = y := by
      refine hThree a ha0 ?_ ?_ ?_
      · rw [iterate_three, zassStep_none, zassStep_some S a 1 one_ne_zero, hz0, zassStep_zero]
      · rw [iterate_three, zassStep_zero, zassStep_none,
            zassStep_some S a 1 one_ne_zero, hz0]
      · rw [iterate_three, zassStep_some S a 1 one_ne_zero, hz0, zassStep_zero, zassStep_none]
    obtain ⟨e, he0, hesq, hensq⟩ := exists_isSquare_sub_one_not_isSquare E h2 hneg
    have hene1 : e - 1 ≠ 0 := fun h => hensq (by rw [h]; exact IsSquare.zero)
    have h1e : (1 : E) - e ≠ 0 := by
      rw [show (1 : E) - e = -(e - 1) by ring]; exact neg_ne_zero.mpr hene1
    have hy1 : (e - 1) / e ≠ 0 := div_ne_zero hene1 he0
    have hy1ns : ¬ IsSquare ((e - 1) / e) := by
      rw [div_eq_mul_inv, isSqMulIff E (e - 1) e⁻¹ hene1 (inv_ne_zero he0)]
      intro hcon
      exact hensq (hcon.mpr (inv_sq e hesq))
    have hA : ZassStep S a (some e) = some ((e - 1) / e) := by
      rw [zassStep_some S a e he0, hform_sq e he0 hesq]
      congr 1
      rw [← mul_div_assoc, hak]
      field_simp
      ring
    have hB : ZassStep S a (some ((e - 1) / e)) =
        some (((-cm / cp + 1) * e - 1) / (e - 1)) := by
      rw [zassStep_some S a ((e - 1) / e) hy1, hform_ns ((e - 1) / e) hy1 hy1ns]
      congr 1
      rw [← mul_div_assoc, hak2]
      field_simp
      ring
    have hgy2 : ZassStep S a
        (some (((-cm / cp + 1) * e - 1) / (e - 1))) = some e := by
      have h3 := hg3 (some e)
      rw [iterate_three, hA, hB] at h3
      exact h3
    have hy2ne0 : (((-cm / cp + 1) * e - 1) / (e - 1)) ≠ 0 := by
      intro hcon
      rw [hcon, zassStep_zero] at hgy2
      simp at hgy2
    have hSy2 : S (((-cm / cp + 1) * e - 1) / (e - 1)) = cp * (1 - e) := by
      rw [zassStep_some S a _ hy2ne0] at hgy2
      have hraw : a ^ 2 * S (((-cm / cp + 1) * e - 1) / (e - 1)) + 1 = e :=
        Option.some.inj hgy2
      have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha0
      have h1 : a ^ 2 * S (((-cm / cp + 1) * e - 1) / (e - 1)) = e - 1 :=
        eq_sub_of_add_eq hraw
      have h2 : S (((-cm / cp + 1) * e - 1) / (e - 1)) = (e - 1) / a ^ 2 :=
        (eq_div_iff ha2).mpr (by rw [mul_comm]; exact h1)
      rw [h2, show a ^ 2 = -1 / cp from (eq_div_iff hcp0).mpr hak]
      field_simp
      ring
    have hz2 : (((-cm / cp + 1) * e - 1) / (e - 1)) = (-cm / cp) / (e - 1) := by
      have hy2eq : (((-cm / cp + 1) * e - 1) / (e - 1)) = S (cp * (1 - e)) := by
        rw [← hSy2]; exact (hSS _ hy2ne0).symm
      rw [hy2eq]
      have hcl : ¬ IsSquare (cp * (1 - e)) := by
        rw [show cp * (1 - e) = (cp * (-1)) * (e - 1) by ring]
        have hA2 : cp * (-1) ≠ 0 := mul_ne_zero hcp0 (neg_ne_zero.mpr one_ne_zero)
        have hsq : IsSquare (cp * (-1)) := IsSquare.mul hcpsq hneg
        rw [isSqMulIff E (cp * (-1)) (e - 1) hA2 hene1]
        intro hcon; exact hensq (hcon.mp hsq)
      have hne : cp * (1 - e) ≠ 0 := mul_ne_zero hcp0 h1e
      rw [hform_ns (cp * (1 - e)) hne hcl]
      field_simp
      ring
    have hz3 : ((-cm / cp + 1) * e - 1) = (-cm / cp) :=
      mul_right_cancel₀ hene1 ((div_eq_div_iff hene1 hene1).mp hz2)
    have hz4 : (-cm / cp + 1) * (e - 1) = 0 := by linear_combination hz3
    have hceq : cm = cp := by
      rcases mul_eq_zero.mp hz4 with h4 | h4
      · have h5 : (-cm) / cp = -1 := by linear_combination h4
        have h6 : -cm = -cp := by
          have := (div_eq_iff hcp0).mp h5; rwa [neg_one_mul] at this
        exact neg_inj.mp h6
      · exact absurd h4 hene1
    refine ⟨cp, hcp0, ?_, ?_⟩
    · rw [show (-cp : E) = (-1) * cp by ring]
      exact IsSquare.mul hneg hcpsq
    · intro x hx0
      rcases em (IsSquare x) with hxs | hxns
      · exact hform_sq x hx0 hxs
      · rw [hform_ns x hx0 hxns, hceq]
  · -- Case `¬ IsSquare (-1)`: the `d`-odd branch.
    have hncp : ¬ IsSquare cp := by
      intro hsc
      obtain ⟨r, hr⟩ := hsc
      have hr0 : r ≠ 0 := fun h => hcp0 (by rw [hr, h, mul_zero])
      rcases em (IsSquare r) with hsr | hnsr
      · have hfix : S r = r := by rw [hform_sq r hr0 hsr, hr]; field_simp
        exact hNoFix hneg r hr0 hfix
      · have hnr : IsSquare (-r) := by
          rw [show (-r : E) = (-1) * r by ring]
          exact (isSqMulIff E (-1) r (neg_ne_zero.mpr one_ne_zero) hr0).mpr
            ⟨fun h => absurd h hneg, fun h => absurd h hnsr⟩
        have hfix : S (-r) = -r := by
          rw [hform_sq (-r) (neg_ne_zero.mpr hr0) hnr, hr]; field_simp
        exact hNoFix hneg (-r) (neg_ne_zero.mpr hr0) hfix
    have hceq : cp = cm := hBp hncp
    refine ⟨cp, hcp0, ?_, ?_⟩
    · rw [show (-cp : E) = (-1) * cp by ring]
      exact (isSqMulIff E (-1) cp (neg_ne_zero.mpr one_ne_zero) hcp0).mpr
        ⟨fun h => absurd h hneg, fun h => absurd h hncp⟩
    · intro x hx0
      rcases em (IsSquare x) with hxs | hxns
      · exact hform_sq x hx0 hxs
      · rw [hform_ns x hx0 hxns, hceq]

end Work.ZASS2
