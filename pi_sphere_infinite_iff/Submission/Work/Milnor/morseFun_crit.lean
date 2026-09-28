import Mathlib
import Submission.Work.Milnor.MorseFun
import Submission.Work.Milnor.Base
import Submission.Work.Milnor.morseFun
import Submission.Work.Milnor.MorseHessian
import Submission.Work.Morse.Basic
import Submission.Work.Glue.hasNondegHessian_iotaY_gen
import Submission.Work.Glue.mdifferentiable_iota_smooth
import Submission.Work.Milnor.morseChart1_nocrit
import Submission.Work.Milnor.morseChart2_crit_iff

namespace Work.Milnor

open scoped Manifold ContDiff Topology
open TopologicalSpace Set
open Submission.Milnor

noncomputable section

/-- The model with corners of `Mk (-2)`, namely `𝓡 4 × 𝓡 3`. -/
abbrev morseModel : ModelWithCorners ℝ (E4 × E3) (ModelProd E4 E3) := (𝓡 4).prod (𝓡 3)

/-- The point `-1` of `S³ ⊂ ℍ`. -/
def negOneQS3 : QS3 := ⟨(-1 : Quaternion ℝ), by simp⟩

@[simp] lemma oneQS3_coe : (oneQS3 : Quaternion ℝ) = 1 := rfl

@[simp] lemma negOneQS3_coe : (negOneQS3 : Quaternion ℝ) = -1 := rfl

/-! ## Auxiliary lemmas about `Mk (-2)` -/

/-- A function on `Mk (-2)` is determined by its two chart expressions: `Mk (-2)` is covered by
the two pieces. -/
lemma eq_of_iota (f g : Mk (-2) → ℝ)
    (hfX : ∀ p : MSpace, f ((clutchData (-2)).ιX p) = morseChart1 p)
    (hfY : ∀ p : MSpace, f ((clutchData (-2)).ιY p) = morseChart2 p)
    (hgX : ∀ p : MSpace, g ((clutchData (-2)).ιX p) = morseChart1 p)
    (hgY : ∀ p : MSpace, g ((clutchData (-2)).ιY p) = morseChart2 p) : f = g := by
  funext x
  have hx : x ∈ Set.range (clutchData (-2)).ιX ∪ Set.range (clutchData (-2)).ιY := by
    rw [(clutchData (-2)).range_ιX_union_range_ιY]; exact Set.mem_univ x
  rcases hx with ⟨p, hp⟩ | ⟨q, hq⟩
  · rw [← hp, hfX p, hgX p]
  · rw [← hq, hfY q, hgY q]

/-- Any function whose two chart expressions are those of the Morse function is smooth. -/
theorem contMDiff_of_charts {f : Mk (-2) → ℝ}
    (hfX : ∀ p : MSpace, f ((clutchData (-2)).ιX p) = morseChart1 p)
    (hfY : ∀ p : MSpace, f ((clutchData (-2)).ιY p) = morseChart2 p) :
    ContMDiff morseModel 𝓘(ℝ, ℝ) ∞ f := by
  obtain ⟨F', hF'sm, hF'X, hF'Y⟩ := morseFun
  rw [eq_of_iota f F' hfX hfY hF'X hF'Y]
  exact hF'sm

/-! ## Critical points on the two pieces -/

/-- On the `Y`-piece, the critical points of `F` are exactly those of `F ∘ ιY`: this is the chain
rule together with the fact that `ιY` is a local diffeomorphism. -/
lemma mfderiv_iotaY_eq_zero_iff {F : Mk (-2) → ℝ} {y : MSpace}
    (hF : MDifferentiableAt morseModel 𝓘(ℝ, ℝ) F ((clutchData (-2)).ιY y))
    (hι : MDifferentiableAt morseModel morseModel (clutchData (-2)).ιY y)
    (hsurj : Function.Surjective (mfderiv morseModel morseModel (clutchData (-2)).ιY y)) :
    mfderiv morseModel 𝓘(ℝ, ℝ) F ((clutchData (-2)).ιY y) = 0 ↔
      mfderiv morseModel 𝓘(ℝ, ℝ) (F ∘ (clutchData (-2)).ιY) y = 0 := by
  rw [mfderiv_comp y hF hι]
  constructor
  · intro h
    rw [h]
    exact ContinuousLinearMap.zero_comp _
  · intro h
    ext v
    obtain ⟨w, rfl⟩ := hsurj v
    have h2 := congrArg (fun L => L w) h
    simpa [ContinuousLinearMap.comp_apply] using h2

/-- On the `X`-piece the chain rule gives one direction of the same statement: a critical point of
`F` in the image of `ιX` is a critical point of `F ∘ ιX`. -/
lemma mfderiv_iotaX_eq_zero_of_eq_zero {F : Mk (-2) → ℝ} {x : MSpace}
    (hF : MDifferentiableAt morseModel 𝓘(ℝ, ℝ) F ((clutchData (-2)).ιX x))
    (hι : MDifferentiableAt morseModel morseModel (clutchData (-2)).ιX x)
    (h : mfderiv morseModel 𝓘(ℝ, ℝ) F ((clutchData (-2)).ιX x) = 0) :
    mfderiv morseModel 𝓘(ℝ, ℝ) (F ∘ (clutchData (-2)).ιX) x = 0 := by
  rw [mfderiv_comp x hF hι, h]
  exact ContinuousLinearMap.zero_comp _

/-! ## The remaining ingredients -/

lemma morseChart1_nocrit_local (p : MSpace) :
    mfderiv morseModel 𝓘(ℝ, ℝ) morseChart1 p ≠ 0 :=
  morseChart1_nocrit p

lemma morseChart2_crit_iff_local (q : MSpace) :
    mfderiv morseModel 𝓘(ℝ, ℝ) morseChart2 q = 0 ↔
      q.1 = 0 ∧ ((q.2 : Quaternion ℝ) = 1 ∨ (q.2 : Quaternion ℝ) = -1) :=
  morseChart2_crit_iff q

lemma mdifferentiable_iota_local :
    (∀ x : MSpace, MDifferentiableAt morseModel morseModel (clutchData (-2)).ιX x) ∧
    (∀ y : MSpace, MDifferentiableAt morseModel morseModel (clutchData (-2)).ιY y) ∧
    (∀ y : MSpace,
      Function.Surjective (mfderiv morseModel morseModel (clutchData (-2)).ιY y)) :=
  Work.Glue.mdifferentiable_iota_smooth (clutchData (-2))

lemma hasNondegHessian_iotaY_local {F : Mk (-2) → ℝ} {g : MSpace → ℝ}
    (h : ∀ y : MSpace, F ((clutchData (-2)).ιY y) = g y) {y : MSpace}
    (hy : HasNondegHessian (I := morseModel) (n := ∞) g y) :
    HasNondegHessian (I := morseModel) (n := ∞) F ((clutchData (-2)).ιY y) :=
  Work.Glue.hasNondegHessian_iotaY_gen (clutchData (-2)) h hy

/-! ## The critical points of the Morse function on `Mk (-2)` -/

theorem morseFun_crit (F : Mk (-2) → ℝ)
    (hX : ∀ p : MSpace, F ((clutchData (-2)).ιX p) = morseChart1 p)
    (hY : ∀ p : MSpace, F ((clutchData (-2)).ιY p) = morseChart2 p) :
    (∀ x : Mk (-2), mfderiv ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, ℝ) F x = 0 →
        HasNondegHessian (I := (𝓡 4).prod (𝓡 3)) (n := ∞) F x) ∧
    (∃ p q : Mk (-2), p ≠ q ∧
        mfderiv ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, ℝ) F p = 0 ∧
        mfderiv ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, ℝ) F q = 0 ∧
        ∀ x : Mk (-2), mfderiv ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, ℝ) F x = 0 → x = p ∨ x = q) := by
  have hFsm : ContMDiff morseModel 𝓘(ℝ, ℝ) ∞ F := contMDiff_of_charts hX hY
  have hFmd : ∀ x : Mk (-2), MDifferentiableAt morseModel 𝓘(ℝ, ℝ) F x :=
    fun x => hFsm.mdifferentiableAt (by simp)
  obtain ⟨hιXmd, hιYmd, hιYsurj⟩ := mdifferentiable_iota_local
  -- critical points of the two chart expressions
  have hcrit2 : ∀ y : MSpace, mfderiv morseModel 𝓘(ℝ, ℝ) F ((clutchData (-2)).ιY y) = 0 ↔
      mfderiv morseModel 𝓘(ℝ, ℝ) morseChart2 y = 0 := by
    intro y
    have h2 : mfderiv morseModel 𝓘(ℝ, ℝ) (F ∘ (clutchData (-2)).ιY) y
        = mfderiv morseModel 𝓘(ℝ, ℝ) morseChart2 y := mfderiv_congr (funext hY)
    rw [mfderiv_iotaY_eq_zero_iff (hFmd _) (hιYmd y) (hιYsurj y), h2]
    exact Iff.rfl
  have hcrit1 : ∀ p : MSpace, mfderiv morseModel 𝓘(ℝ, ℝ) F ((clutchData (-2)).ιX p) = 0 →
      mfderiv morseModel 𝓘(ℝ, ℝ) morseChart1 p = 0 := by
    intro p h
    have h2 : mfderiv morseModel 𝓘(ℝ, ℝ) (F ∘ (clutchData (-2)).ιX) p
        = mfderiv morseModel 𝓘(ℝ, ℝ) morseChart1 p := mfderiv_congr (funext hX)
    rw [← h2]
    exact mfderiv_iotaX_eq_zero_of_eq_zero (hFmd _) (hιXmd p) h
  -- the two critical points and their uniqueness
  have huniq : ∀ x : Mk (-2), mfderiv morseModel 𝓘(ℝ, ℝ) F x = 0 →
      x = (clutchData (-2)).ιY (0, oneQS3) ∨ x = (clutchData (-2)).ιY (0, negOneQS3) := by
    intro x hx
    have hmem : x ∈ Set.range (clutchData (-2)).ιX ∪ Set.range (clutchData (-2)).ιY := by
      rw [(clutchData (-2)).range_ιX_union_range_ιY]; exact Set.mem_univ x
    rcases hmem with ⟨p, hp⟩ | ⟨q, hq⟩
    · rw [← hp] at hx
      exact absurd (hcrit1 p hx) (morseChart1_nocrit_local p)
    · rw [← hq] at hx
      have hq0 : mfderiv morseModel 𝓘(ℝ, ℝ) morseChart2 q = 0 := (hcrit2 q).mp hx
      obtain ⟨hq1, hq2⟩ := (morseChart2_crit_iff_local q).mp hq0
      have hqeq : q = ((0 : E4), oneQS3) ∨ q = ((0 : E4), negOneQS3) := by
        rcases hq2 with h | h
        · left; exact Prod.ext hq1 (Subtype.ext (by simpa using h))
        · right; exact Prod.ext hq1 (Subtype.ext (by simpa using h))
      rcases hqeq with h | h
      · left; rw [← hq, h]
      · right; rw [← hq, h]
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases huniq x hx with h | h
    · rw [h]
      exact hasNondegHessian_iotaY_local hY (hasNondegHessian_chart2 oneQS3 (Or.inl rfl))
    · rw [h]
      exact hasNondegHessian_iotaY_local hY (hasNondegHessian_chart2 negOneQS3 (Or.inr rfl))
  · refine ⟨(clutchData (-2)).ιY (0, oneQS3), (clutchData (-2)).ιY (0, negOneQS3),
      ?_, ?_, ?_, huniq⟩
    · intro hcon
      have hy : ((0 : E4), oneQS3) = ((0 : E4), negOneQS3) := (clutchData (-2)).ιY_injective hcon
      have h1 : (1 : Quaternion ℝ) = -1 := by
        have := congrArg (fun z : MSpace => (z.2 : Quaternion ℝ)) hy
        simpa using this
      have h2 : (1 : ℝ) = -1 := by
        have h3 := congrArg (fun q : Quaternion ℝ => q.re) h1
        simpa only [Quaternion.re_one, Quaternion.re_neg] using h3
      norm_num at h2
    · exact (hcrit2 (0, oneQS3)).mpr ((morseChart2_crit_iff_local (0, oneQS3)).mpr ⟨rfl, Or.inl rfl⟩)
    · exact (hcrit2 (0, negOneQS3)).mpr
        ((morseChart2_crit_iff_local (0, negOneQS3)).mpr ⟨rfl, Or.inr rfl⟩)

end

end Work.Milnor
