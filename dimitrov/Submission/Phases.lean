import Mathlib.Analysis.Complex.Angle
import Mathlib.Analysis.Complex.Arg

/-!
# Phase counting lemmas

For a finite set `S` of nonzero complex numbers (intended to be the
conjugates of an algebraic number, a set closed under complex
conjugation), we compare the number of distinct principal arguments of
the elements of `S`, of `S² = {z² | z ∈ S}`, and of `S⁴`.

Basic facts about `Complex.arg` you may use freely:
`Complex.arg_mem_Ioc`, `Complex.arg_eq_arg_iff`, `Complex.arg_conj`,
`Complex.arg_eq_zero_iff`, `Complex.arg_eq_pi_iff`, `Complex.arg_real_mul`.
All lemmas here are over a field of characteristic zero? No: plain `ℂ`.
-/

noncomputable section

open scoped Complex

namespace Submission.Phases

/-- Squaring maps each phase-line to a phase-line: if two complex numbers
have the same principal argument, so do their squares. -/
lemma arg_sq_of_arg_eq {x y : ℂ} (h : x.arg = y.arg) : (x ^ 2).arg = (y ^ 2).arg := by
  have hx2 : (Complex.arg (x ^ 2) : Real.Angle) = (Complex.arg (y ^ 2) : Real.Angle) := by
    rw [Complex.arg_pow_coe_angle, Complex.arg_pow_coe_angle, h]
  exact Complex.arg_coe_angle_eq_iff.mp hx2

/-- If `g` is constant on the fibres of `f` inside `S`, then the image of `S`
under `g` has cardinality at most that of the image of `S` under `f`. -/
lemma card_image_le_of_forall_eq {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (f : α → β) (g : α → γ)
    (hg : ∀ ⦃x : α⦄, x ∈ S → ∀ ⦃y : α⦄, y ∈ S → f x = f y → g x = g y) :
    (S.image g).card ≤ (S.image f).card := by
  classical
  let ψ : {v : γ // v ∈ S.image g} → β := fun v =>
    f (Classical.choose (Finset.mem_image.mp v.property))
  have hψ_mem : ∀ v : {v : γ // v ∈ S.image g}, ψ v ∈ S.image f := by
    intro v
    have hspec := Classical.choose_spec (Finset.mem_image.mp v.property)
    exact Finset.mem_image.mpr ⟨Classical.choose (Finset.mem_image.mp v.property), hspec.1, rfl⟩
  have hψ_inj : Set.InjOn ψ ↑(S.image g).attach := by
    intro v1 hv1 v2 hv2 heq
    apply Subtype.ext
    have hspec1 := Classical.choose_spec (Finset.mem_image.mp v1.property)
    have hspec2 := Classical.choose_spec (Finset.mem_image.mp v2.property)
    have hg12 :
        g (Classical.choose (Finset.mem_image.mp v1.property)) =
          g (Classical.choose (Finset.mem_image.mp v2.property)) :=
      hg hspec1.1 hspec2.1 heq
    exact hspec1.2.symm.trans (hg12.trans hspec2.2)
  have hcard :=
    Finset.card_le_card_of_injOn (s := (S.image g).attach) (t := S.image f) ψ
      (fun v hv => hψ_mem v) hψ_inj
  simpa [Finset.card_attach] using hcard

/-- Squaring can only merge phases: the number of distinct phases of
`{z² | z ∈ S}` is at most the number of distinct phases of `S`. -/
lemma card_arg_image_sq_le (S : Finset ℂ) :
    ((S.image fun z : ℂ => z ^ 2).image Complex.arg).card ≤
      (S.image Complex.arg).card := by
  classical
  rw [Finset.image_image]
  exact card_image_le_of_forall_eq S Complex.arg (fun z : ℂ => Complex.arg (z ^ 2)) (by
    intro x hx y hy harg
    exact arg_sq_of_arg_eq harg)

/-- The principal argument of `z ^ 2` equals `2 • arg z` reduced modulo `2π`. -/
lemma arg_sq_eq_toReal_two_smul (z : ℂ) :
    Complex.arg (z ^ 2) = (2 • (Complex.arg z : Real.Angle)).toReal := by
  have h := congrArg Real.Angle.toReal (Complex.arg_pow_coe_angle z 2)
  rw [Complex.arg_coe_angle_toReal_eq_arg] at h
  exact h

/-- Two principal arguments that lie in the same (closed) half-circle cannot
differ by `π` as angles. -/
lemma same_half_add_pi_false {θ₁ θ₂ : ℝ}
    (h₁ : θ₁ ∈ Set.Ioc (-Real.pi) Real.pi) (h₂ : θ₂ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hs : (θ₁ ≤ 0 ↔ θ₂ ≤ 0))
    (hc : (θ₁ : Real.Angle) = (θ₂ : Real.Angle) + (Real.pi : Real.Angle)) : False := by
  have hsin := congrArg Real.Angle.sin hc
  simp at hsin
  by_cases hθ₁ : θ₁ ≤ 0
  · have hθ₂ : θ₂ ≤ 0 := hs.mp hθ₁
    have hsin1le : Real.sin θ₁ ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le hθ₁ (le_of_lt (Set.mem_Ioc.mp h₁).1)
    have hsin2le : Real.sin θ₂ ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le hθ₂ (le_of_lt (Set.mem_Ioc.mp h₂).1)
    have hsin1ge : 0 ≤ Real.sin θ₁ := by
      rw [hsin]
      exact neg_nonneg.mpr hsin2le
    have hz₁ : Real.sin θ₁ = 0 := le_antisymm hsin1le hsin1ge
    have hz₂ : Real.sin θ₂ = 0 := by linarith
    have hθ₁₀ : θ₁ = 0 := by
      exact (Real.sin_eq_zero_iff_of_lt_of_lt (Set.mem_Ioc.mp h₁).1
        (lt_of_le_of_lt hθ₁ Real.pi_pos)).mp hz₁
    have hθ₂₀ : θ₂ = 0 := by
      exact (Real.sin_eq_zero_iff_of_lt_of_lt (Set.mem_Ioc.mp h₂).1
        (lt_of_le_of_lt hθ₂ Real.pi_pos)).mp hz₂
    have hc' : (0 : Real.Angle) = (Real.pi : Real.Angle) := by
      rw [hθ₁₀, hθ₂₀] at hc
      simpa using hc
    have htr := congrArg Real.Angle.toReal hc'
    rw [Real.Angle.toReal_zero, Real.Angle.toReal_pi] at htr
    exact Real.pi_ne_zero htr.symm
  · have hθ₁pos : 0 < θ₁ := lt_of_not_ge hθ₁
    have hθ₂pos : 0 < θ₂ := by
      by_contra hc0
      have hθ₂le : θ₂ ≤ 0 := le_of_not_gt hc0
      exact hθ₁ (hs.mpr hθ₂le)
    have hsin1ge : 0 ≤ Real.sin θ₁ :=
      Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt hθ₁pos) (Set.mem_Ioc.mp h₁).2
    have hsin2ge : 0 ≤ Real.sin θ₂ :=
      Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt hθ₂pos) (Set.mem_Ioc.mp h₂).2
    have hsin1le : Real.sin θ₁ ≤ 0 := by
      rw [hsin]
      exact neg_nonpos.mpr hsin2ge
    have hz₁ : Real.sin θ₁ = 0 := le_antisymm hsin1le hsin1ge
    have hz₂ : Real.sin θ₂ = 0 := by linarith
    have hθ₁π : θ₁ = Real.pi := by
      apply le_antisymm (Set.mem_Ioc.mp h₁).2
      by_contra hlt
      have hlt' : θ₁ < Real.pi := lt_of_not_ge hlt
      have hpos : 0 < Real.sin θ₁ := Real.sin_pos_of_pos_of_lt_pi hθ₁pos hlt'
      linarith
    have hθ₂π : θ₂ = Real.pi := by
      apply le_antisymm (Set.mem_Ioc.mp h₂).2
      by_contra hlt
      have hlt' : θ₂ < Real.pi := lt_of_not_ge hlt
      have hpos : 0 < Real.sin θ₂ := Real.sin_pos_of_pos_of_lt_pi hθ₂pos hlt'
      linarith
    have hc' : (Real.pi : Real.Angle) = (0 : Real.Angle) := by
      rw [hθ₁π, hθ₂π] at hc
      simpa using hc
    have htr := congrArg Real.Angle.toReal hc'
    rw [Real.Angle.toReal_pi, Real.Angle.toReal_zero] at htr
    exact Real.pi_ne_zero htr

/-- The doubling map `θ ↦ 2θ mod 2π` is injective on arguments lying in the
same half-circle (both in `(0, π]` or both in `(-π, 0]`). -/
lemma two_smul_toReal_inj_same_half {θ₁ θ₂ : ℝ}
    (h₁ : θ₁ ∈ Set.Ioc (-Real.pi) Real.pi) (h₂ : θ₂ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hs : (θ₁ ≤ 0 ↔ θ₂ ≤ 0))
    (h : (2 • (θ₁ : Real.Angle)).toReal = (2 • (θ₂ : Real.Angle)).toReal) :
    θ₁ = θ₂ := by
  have hangle : (2 : ℕ) • (θ₁ : Real.Angle) = (2 : ℕ) • (θ₂ : Real.Angle) :=
    Real.Angle.toReal_inj.mp h
  rcases Real.Angle.two_nsmul_eq_iff.mp hangle with hc | hc
  · have ht₁ : (θ₁ : Real.Angle).toReal = θ₁ :=
      Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr h₁
    have ht₂ : (θ₂ : Real.Angle).toReal = θ₂ :=
      Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr h₂
    have htr := congrArg Real.Angle.toReal hc
    exact ht₁.symm.trans (htr.trans ht₂)
  · exact False.elim (same_half_add_pi_false h₁ h₂ hs hc)

/-- The number of distinct phases of `{z² | z ∈ S}` is at least half the
number of distinct phases of `S`.  (The map `θ ↦ 2θ mod 2π` on principal
arguments has fibres of size at most 2.) -/
lemma half_le_card_arg_image_sq (S : Finset ℂ) (hS : ∀ z ∈ S, z ≠ 0) :
    (S.image Complex.arg).card ≤
      2 * ((S.image fun z : ℂ => z ^ 2).image Complex.arg).card := by
  classical
  let A : Finset ℝ := S.image Complex.arg
  let B : Finset ℝ := (S.image fun z : ℂ => z ^ 2).image Complex.arg
  let ang2 : ℝ → ℝ := fun θ => (2 • (θ : Real.Angle)).toReal
  change A.card ≤ 2 * B.card
  have hmemIoc : ∀ θ ∈ A, θ ∈ Set.Ioc (-Real.pi) Real.pi := by
    intro θ hθ
    rcases Finset.mem_image.mp hθ with ⟨z, hzS, rfl⟩
    exact Complex.arg_mem_Ioc z
  have hsq : ∀ z ∈ S, Complex.arg (z ^ 2) = ang2 (Complex.arg z) := by
    intro z hz
    change Complex.arg (z ^ 2) = (2 • (Complex.arg z : Real.Angle)).toReal
    exact arg_sq_eq_toReal_two_smul z
  have hB : B = A.image ang2 := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨u, huSq, hvu⟩
      rcases Finset.mem_image.mp huSq with ⟨w, hwS, huw⟩
      refine Finset.mem_image.mpr ⟨Complex.arg w, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨w, hwS, rfl⟩
      · calc
          ang2 (Complex.arg w) = Complex.arg (w ^ 2) := (hsq w hwS).symm
          _ = Complex.arg u := by rw [huw]
          _ = v := hvu
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨θ, hθA, hvθ⟩
      rcases Finset.mem_image.mp hθA with ⟨w, hwS, hθw⟩
      refine Finset.mem_image.mpr ⟨w ^ 2, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨w, hwS, rfl⟩
      · calc
          Complex.arg (w ^ 2) = ang2 (Complex.arg w) := hsq w hwS
          _ = ang2 θ := by rw [hθw]
          _ = v := hvθ
  let Ap : Finset ℝ := A.filter (fun θ => 0 < θ)
  let An : Finset ℝ := A.filter (fun θ => θ ≤ 0)
  have hAunion : A = Ap ∪ An := by
    ext θ
    constructor
    · intro hθ
      by_cases hp : 0 < θ
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hθ, hp⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hθ, le_of_not_gt hp⟩))
    · intro hθ
      rcases Finset.mem_union.mp hθ with hθp | hθn
      · exact (Finset.mem_filter.mp hθp).1
      · exact (Finset.mem_filter.mp hθn).1
  have hApB : Ap.card ≤ B.card := by
    have hinjAp : Set.InjOn ang2 ↑Ap := by
      intro θ₁ hθ₁Ap θ₂ hθ₂Ap h
      have hθ₁A : θ₁ ∈ A := (Finset.mem_filter.mp hθ₁Ap).1
      have hθ₁pos : 0 < θ₁ := (Finset.mem_filter.mp hθ₁Ap).2
      have hθ₂A : θ₂ ∈ A := (Finset.mem_filter.mp hθ₂Ap).1
      have hθ₂pos : 0 < θ₂ := (Finset.mem_filter.mp hθ₂Ap).2
      have hsame : (θ₁ ≤ 0 ↔ θ₂ ≤ 0) :=
        iff_of_false (not_le_of_gt hθ₁pos) (not_le_of_gt hθ₂pos)
      exact two_smul_toReal_inj_same_half (hmemIoc θ₁ hθ₁A) (hmemIoc θ₂ hθ₂A) hsame h
    have hcardAp : (Ap.image ang2).card = Ap.card := Finset.card_image_of_injOn hinjAp
    have hsub : Ap.image ang2 ⊆ B := by
      rw [hB]
      exact Finset.image_subset_image (Finset.filter_subset (fun θ : ℝ => 0 < θ) A)
    calc
      Ap.card = (Ap.image ang2).card := hcardAp.symm
      _ ≤ B.card := Finset.card_le_card hsub
  have hAnB : An.card ≤ B.card := by
    have hinjAn : Set.InjOn ang2 ↑An := by
      intro θ₁ hθ₁An θ₂ hθ₂An h
      have hθ₁A : θ₁ ∈ A := (Finset.mem_filter.mp hθ₁An).1
      have hθ₁le : θ₁ ≤ 0 := (Finset.mem_filter.mp hθ₁An).2
      have hθ₂A : θ₂ ∈ A := (Finset.mem_filter.mp hθ₂An).1
      have hθ₂le : θ₂ ≤ 0 := (Finset.mem_filter.mp hθ₂An).2
      have hsame : (θ₁ ≤ 0 ↔ θ₂ ≤ 0) := iff_of_true hθ₁le hθ₂le
      exact two_smul_toReal_inj_same_half (hmemIoc θ₁ hθ₁A) (hmemIoc θ₂ hθ₂A) hsame h
    have hcardAn : (An.image ang2).card = An.card := Finset.card_image_of_injOn hinjAn
    have hsub : An.image ang2 ⊆ B := by
      rw [hB]
      exact Finset.image_subset_image (Finset.filter_subset (fun θ : ℝ => θ ≤ 0) A)
    calc
      An.card = (An.image ang2).card := hcardAn.symm
      _ ≤ B.card := Finset.card_le_card hsub
  calc
    A.card = (Ap ∪ An).card := by rw [hAunion]
    _ ≤ Ap.card + An.card := Finset.card_union_le _ _
    _ ≤ B.card + B.card := add_le_add hApB hAnB
    _ = 2 * B.card := by omega

/-- The principal argument of `z ^ 4` depends only on the principal argument
of `z`: if two complex numbers have the same argument then so do their fourth
powers. -/
lemma arg_pow4_eq_of_arg_eq {x y : ℂ} (h : x.arg = y.arg) : (x ^ 4).arg = (y ^ 4).arg := by
  have hx4 : (Complex.arg (x ^ 4) : Real.Angle) = (Complex.arg (y ^ 4) : Real.Angle) := by
    rw [Complex.arg_pow_coe_angle, Complex.arg_pow_coe_angle, h]
  exact Complex.arg_coe_angle_eq_iff.mp hx4

/-- The phases of `{z⁴ | z ∈ S}` are at most as many as the phases of `S`. -/
lemma card_arg_image_pow4_le (S : Finset ℂ) :
    ((S.image fun z : ℂ => z ^ 4).image Complex.arg).card ≤
      (S.image Complex.arg).card := by
  classical
  rw [Finset.image_image]
  exact card_image_le_of_forall_eq S Complex.arg (fun z : ℂ => Complex.arg (z ^ 4)) (by
    intro x hx y hy harg
    exact arg_pow4_eq_of_arg_eq harg)

/-- The union of the phases of `S²` and `S⁴` has size at most twice the
number of phases of `S`. -/
lemma card_arg_sq_union_pow4_le (S : Finset ℂ) :
    (((S.image fun z : ℂ => z ^ 2) ∪ (S.image fun z : ℂ => z ^ 4)).image Complex.arg).card ≤
      2 * (S.image Complex.arg).card := by
  classical
  have hsq : ((S.image fun z : ℂ => z ^ 2).image Complex.arg).card ≤
      (S.image Complex.arg).card := card_arg_image_sq_le S
  have h4 : ((S.image fun z : ℂ => z ^ 4).image Complex.arg).card ≤
      (S.image Complex.arg).card := card_arg_image_pow4_le S
  calc
    (((S.image fun z : ℂ => z ^ 2) ∪ (S.image fun z : ℂ => z ^ 4)).image Complex.arg).card
        = (((S.image fun z : ℂ => z ^ 2).image Complex.arg) ∪
           ((S.image fun z : ℂ => z ^ 4).image Complex.arg)).card := by
          rw [Finset.image_union]
    _ ≤ ((S.image fun z : ℂ => z ^ 2).image Complex.arg).card +
          ((S.image fun z : ℂ => z ^ 4).image Complex.arg).card := by
          exact Finset.card_union_le _ _
    _ ≤ 2 * (S.image Complex.arg).card := by
          nlinarith

/-- For a set closed under complex conjugation, the phases come in ± pairs:
`z.arg` and `(star z).arg` are either equal (both `π`) or negatives.
Formally: if `S = star S` then the set of phases is closed under the map
`θ ↦ if θ = π then π else -θ`. -/
lemma argSet_conj_closed (S : Finset ℂ) (hS : S.image (fun z : ℂ => star z) = S) :
    ∀ θ ∈ S.image Complex.arg,
      (if θ = Real.pi then Real.pi else -θ) ∈ S.image Complex.arg := by
  classical
  intro θ hθ
  rcases Finset.mem_image.mp hθ with ⟨z, hzS, rfl⟩
  have hzstar : star z ∈ S := by
    rw [← hS]
    exact Finset.mem_image.mpr ⟨z, hzS, rfl⟩
  have hif : (if Complex.arg z = Real.pi then Real.pi else -Complex.arg z) =
      Complex.arg (star z) := by
    rw [← Complex.arg_conj z, starRingEnd_apply]
  rw [hif]
  exact Finset.mem_image.mpr ⟨star z, hzstar, rfl⟩

end Submission.Phases

end
