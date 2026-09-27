/-
A6 `Geo/DualStretch` — the relations satisfied by the bookkeeping objects under the stretch.

Let `y = stretch P hP β p α M x`.  The hypothesis `hwt` says that the barycentric mass
decomposition of `y` is the rescaled decomposition `wtOf …` on the *same* chain of level sets
`posCands P hP x` as `x` (and zero elsewhere).  Then the low part, the high part, the total high
mass and the join segment transform by the explicit factors:

* `S(y) = taperM x * S(x) / d`  with `d = denOf x = 1 + (taperM x - 1) * S(x)`,
* `A(y) = d⁻¹ • A(x)`,
* `B(y) = (taperM x / d) • B(x)`,
* `segOf y = segOf x`.

The two identities behind the join-segment statement are `d = (1 - S) + taperM x * S` and
`S(y) = d⁻¹ * taperM x * S`; they give `1 - S(y) = (1 - S) * d⁻¹` and hence, since `d > 0`,
`uOf` and `wOf` are unchanged.
-/
import Mathlib
import Submission.Work.Geo.DualStretch.Defs
import Submission.Work.Geo.DualStretch.Basic
import Submission.Work.Geo.DualStretch.carrier_spec
import Submission.Work.Geo.DualStretch.massG_api
import Submission.Work.Geo.DualStretch.stretch_defs

open Set Metric
open scoped Classical

namespace Work.Geo.DualStretch

open _root_.PL (E Cx)

variable {n : ℕ}

/-! ### Elementary API for `cands`, `posCands`, `massG` -/

private lemma mem_cands {P : Cx n} {hP : P.faces.Finite} {τ : Finset (E n)} :
    τ ∈ cands P hP ↔ ∃ σ ∈ P.faces, τ ⊆ σ := by
  rw [cands, Finset.mem_biUnion]
  constructor
  · rintro ⟨σ, hσ, hτ⟩
    exact ⟨σ, (Set.Finite.mem_toFinset hP).mp hσ, Finset.mem_powerset.mp hτ⟩
  · rintro ⟨σ, hσ, hτ⟩
    exact ⟨σ, (Set.Finite.mem_toFinset hP).mpr hσ, Finset.mem_powerset.mpr hτ⟩

private lemma massG_nonneg (P : Cx n) (hP : P.faces.Finite) (x : E n) (τ : Finset (E n)) :
    0 ≤ massG P hP x τ := le_max_left _ _

/-- Off the level sets of positive mass of `x` the mass of `x` vanishes. -/
private lemma massG_eq_zero_of_not_mem_posCands (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hx : x ∈ P.space) {τ : Finset (E n)} (h : τ ∉ posCands P hP x) : massG P hP x τ = 0 := by
  by_cases hc : τ ∈ cands P hP
  · have hnn := massG_nonneg P hP x τ
    by_contra hne
    exact h (Finset.mem_filter.mpr ⟨hc, lt_of_le_of_ne hnn (Ne.symm hne)⟩)
  · refine (massG_api P hP hx).2.2.2.1 τ ?_
    intro hsub
    exact hc (mem_cands.mpr ⟨carrier P x, (carrier_spec P hP hx).1, hsub⟩)

/-! ### The total high mass of a point of `P.space` -/

private theorem SOf_nonneg {β : ℝ} {p : ℕ} (P : Cx n) (hP : P.faces.Finite) (x : E n) :
    0 ≤ SOf β p P hP x := by
  rw [SOf]
  exact Finset.sum_nonneg (fun τ _ => by
    by_cases hL : LowFace β p τ
    · rw [if_pos hL]
    · rw [if_neg hL]; exact massG_nonneg P hP x τ)

private theorem SOf_le_one {β : ℝ} {p : ℕ} (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hx : x ∈ P.space) : SOf β p P hP x ≤ 1 := by
  have h1 : SOf β p P hP x ≤ ∑ τ ∈ cands P hP, massG P hP x τ := by
    rw [SOf]
    exact Finset.sum_le_sum (fun τ _ => by
      by_cases hL : LowFace β p τ
      · rw [if_pos hL]; exact massG_nonneg P hP x τ
      · rw [if_neg hL])
  calc SOf β p P hP x ≤ ∑ τ ∈ cands P hP, massG P hP x τ := h1
    _ = 1 := (massG_api P hP hx).2.1

/-- The renormalisation factor `d` of the stretch is positive. -/
private theorem denOf_pos {β α M : ℝ} {p : ℕ} (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hM : 0 < M) (hs0 : 0 ≤ SOf β p P hP x) (hs1 : SOf β p P hP x ≤ 1) :
    0 < denOf β p P hP α M x := by
  have ht : 0 < taperM β p P hP α M x := taperM_pos hM p P hP x
  rw [denOf]
  by_cases h : (1 : ℝ) ≤ taperM β p P hP α M x
  · have h2 : 0 ≤ (taperM β p P hP α M x - 1) * SOf β p P hP x :=
      mul_nonneg (by linarith) hs0
    linarith
  · have hlt : taperM β p P hP α M x < 1 := not_le.mp h
    have hle : (1 - taperM β p P hP α M x) * SOf β p P hP x ≤ 1 - taperM β p P hP α M x :=
      mul_le_of_le_one_right (by linarith) hs1
    nlinarith [ht]

/-! ### The three sums transform by the explicit factors -/

private theorem SOf_stretch {β α M : ℝ} {p : ℕ} (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hx : x ∈ P.space)
    (hwt : ∀ τ : Finset (E n), massG P hP (stretch P hP β p α M x) τ =
      if τ ∈ posCands P hP x then wtOf β p P hP α M x τ else 0) :
    SOf β p P hP (stretch P hP β p α M x) =
      taperM β p P hP α M x * (denOf β p P hP α M x)⁻¹ * SOf β p P hP x := by
  have hterm : ∀ τ : Finset (E n),
      (if LowFace β p τ then (0 : ℝ) else massG P hP (stretch P hP β p α M x) τ) =
        taperM β p P hP α M x * (denOf β p P hP α M x)⁻¹ *
          (if LowFace β p τ then 0 else massG P hP x τ) := by
    intro τ
    rw [hwt τ]
    by_cases hL : LowFace β p τ
    · rw [if_pos hL, if_pos hL, mul_zero]
    · rw [if_neg hL, if_neg hL]
      by_cases hp : τ ∈ posCands P hP x
      · rw [if_pos hp, wtOf, if_neg hL]
      · rw [if_neg hp, massG_eq_zero_of_not_mem_posCands P hP hx hp, mul_zero]
  calc SOf β p P hP (stretch P hP β p α M x)
      = ∑ τ ∈ cands P hP,
          (if LowFace β p τ then (0 : ℝ) else massG P hP (stretch P hP β p α M x) τ) := rfl
    _ = ∑ τ ∈ cands P hP, taperM β p P hP α M x * (denOf β p P hP α M x)⁻¹ *
          (if LowFace β p τ then 0 else massG P hP x τ) :=
        Finset.sum_congr rfl (fun τ _ => hterm τ)
    _ = taperM β p P hP α M x * (denOf β p P hP α M x)⁻¹ *
          ∑ τ ∈ cands P hP, (if LowFace β p τ then 0 else massG P hP x τ) :=
        (Finset.mul_sum _ _ _).symm
    _ = taperM β p P hP α M x * (denOf β p P hP α M x)⁻¹ * SOf β p P hP x := rfl

private theorem AOf_stretch {β α M : ℝ} {p : ℕ} (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hx : x ∈ P.space)
    (hwt : ∀ τ : Finset (E n), massG P hP (stretch P hP β p α M x) τ =
      if τ ∈ posCands P hP x then wtOf β p P hP α M x τ else 0) :
    AOf β p P hP (stretch P hP β p α M x) = (denOf β p P hP α M x)⁻¹ • AOf β p P hP x := by
  have hterm : ∀ τ : Finset (E n),
      (if LowFace β p τ then massG P hP (stretch P hP β p α M x) τ • bary τ else 0) =
        (denOf β p P hP α M x)⁻¹ •
          (if LowFace β p τ then massG P hP x τ • bary τ else 0) := by
    intro τ
    rw [hwt τ]
    by_cases hL : LowFace β p τ
    · rw [if_pos hL, if_pos hL]
      by_cases hp : τ ∈ posCands P hP x
      · rw [if_pos hp, wtOf, if_pos hL, smul_smul]
      · rw [if_neg hp, zero_smul, massG_eq_zero_of_not_mem_posCands P hP hx hp, zero_smul,
          smul_zero]
    · rw [if_neg hL, if_neg hL, smul_zero]
  calc AOf β p P hP (stretch P hP β p α M x)
      = ∑ τ ∈ cands P hP,
          (if LowFace β p τ then massG P hP (stretch P hP β p α M x) τ • bary τ else 0) := rfl
    _ = ∑ τ ∈ cands P hP, (denOf β p P hP α M x)⁻¹ •
          (if LowFace β p τ then massG P hP x τ • bary τ else 0) :=
        Finset.sum_congr rfl (fun τ _ => hterm τ)
    _ = (denOf β p P hP α M x)⁻¹ •
          ∑ τ ∈ cands P hP, (if LowFace β p τ then massG P hP x τ • bary τ else 0) :=
        (Finset.smul_sum).symm
    _ = (denOf β p P hP α M x)⁻¹ • AOf β p P hP x := rfl

private theorem BOf_stretch {β α M : ℝ} {p : ℕ} (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hx : x ∈ P.space)
    (hwt : ∀ τ : Finset (E n), massG P hP (stretch P hP β p α M x) τ =
      if τ ∈ posCands P hP x then wtOf β p P hP α M x τ else 0) :
    BOf β p P hP (stretch P hP β p α M x) =
      (taperM β p P hP α M x * (denOf β p P hP α M x)⁻¹) • BOf β p P hP x := by
  have hterm : ∀ τ : Finset (E n),
      (if LowFace β p τ then (0 : E n) else massG P hP (stretch P hP β p α M x) τ • bary τ) =
        (taperM β p P hP α M x * (denOf β p P hP α M x)⁻¹) •
          (if LowFace β p τ then 0 else massG P hP x τ • bary τ) := by
    intro τ
    rw [hwt τ]
    by_cases hL : LowFace β p τ
    · rw [if_pos hL, if_pos hL, smul_zero]
    · rw [if_neg hL, if_neg hL]
      by_cases hp : τ ∈ posCands P hP x
      · rw [if_pos hp, wtOf, if_neg hL, smul_smul]
      · rw [if_neg hp, zero_smul, massG_eq_zero_of_not_mem_posCands P hP hx hp, zero_smul,
          smul_zero]
  calc BOf β p P hP (stretch P hP β p α M x)
      = ∑ τ ∈ cands P hP,
          (if LowFace β p τ then (0 : E n) else massG P hP (stretch P hP β p α M x) τ • bary τ) :=
        rfl
    _ = ∑ τ ∈ cands P hP, (taperM β p P hP α M x * (denOf β p P hP α M x)⁻¹) •
          (if LowFace β p τ then 0 else massG P hP x τ • bary τ) :=
        Finset.sum_congr rfl (fun τ _ => hterm τ)
    _ = (taperM β p P hP α M x * (denOf β p P hP α M x)⁻¹) •
          ∑ τ ∈ cands P hP, (if LowFace β p τ then 0 else massG P hP x τ • bary τ) :=
        (Finset.smul_sum).symm
    _ = (taperM β p P hP α M x * (denOf β p P hP α M x)⁻¹) • BOf β p P hP x := rfl

/-- The renormalised complementary mass: `1 - S(y) = (1 - S(x)) / d`. -/
private theorem one_sub_SOf_stretch {β α M : ℝ} {p : ℕ} (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hx : x ∈ P.space) (hdne : denOf β p P hP α M x ≠ 0)
    (hwt : ∀ τ : Finset (E n), massG P hP (stretch P hP β p α M x) τ =
      if τ ∈ posCands P hP x then wtOf β p P hP α M x τ else 0) :
    1 - SOf β p P hP (stretch P hP β p α M x) =
      (1 - SOf β p P hP x) * (denOf β p P hP α M x)⁻¹ := by
  have hmul : denOf β p P hP α M x * (denOf β p P hP α M x)⁻¹ = 1 := mul_inv_cancel₀ hdne
  have hkey : 1 - SOf β p P hP x = denOf β p P hP α M x - taperM β p P hP α M x * SOf β p P hP x := by
    rw [denOf]; ring
  rw [SOf_stretch P hP hx hwt, hkey, sub_mul, hmul]
  ring

/-! ### The target -/

theorem stretch_relations {n : ℕ} (P : PL.Cx n) (hP : P.faces.Finite) {β α M : ℝ} (hM : 0 < M)
    {p : ℕ} {x : PL.E n} (hx : x ∈ P.space)
    (hwt : ∀ τ : Finset (PL.E n),
      Work.Geo.DualStretch.massG P hP (Work.Geo.DualStretch.stretch P hP β p α M x) τ =
        if τ ∈ Work.Geo.DualStretch.posCands P hP x then
          Work.Geo.DualStretch.wtOf β p P hP α M x τ else 0) :
    Work.Geo.DualStretch.SOf β p P hP (Work.Geo.DualStretch.stretch P hP β p α M x) =
        Work.Geo.DualStretch.taperM β p P hP α M x * Work.Geo.DualStretch.SOf β p P hP x /
          Work.Geo.DualStretch.denOf β p P hP α M x ∧
      Work.Geo.DualStretch.AOf β p P hP (Work.Geo.DualStretch.stretch P hP β p α M x) =
        (Work.Geo.DualStretch.denOf β p P hP α M x)⁻¹ •
          Work.Geo.DualStretch.AOf β p P hP x ∧
      Work.Geo.DualStretch.BOf β p P hP (Work.Geo.DualStretch.stretch P hP β p α M x) =
        (Work.Geo.DualStretch.taperM β p P hP α M x / Work.Geo.DualStretch.denOf β p P hP α M x) •
          Work.Geo.DualStretch.BOf β p P hP x ∧
      Work.Geo.DualStretch.segOf β p P hP (Work.Geo.DualStretch.stretch P hP β p α M x) =
        Work.Geo.DualStretch.segOf β p P hP x := by
  classical
  have ht : 0 < taperM β p P hP α M x := taperM_pos hM p P hP x
  have htne : taperM β p P hP α M x ≠ 0 := ne_of_gt ht
  have hs0 : 0 ≤ SOf β p P hP x := SOf_nonneg P hP x
  have hs1 : SOf β p P hP x ≤ 1 := SOf_le_one P hP hx
  have hdpos : 0 < denOf β p P hP α M x := denOf_pos P hP hM hs0 hs1
  have hdne : denOf β p P hP α M x ≠ 0 := ne_of_gt hdpos
  have hS := SOf_stretch P hP hx hwt
  have hA := AOf_stretch P hP hx hwt
  have hB := BOf_stretch P hP hx hwt
  have h1S := one_sub_SOf_stretch P hP hx hdne hwt
  have hu : uOf β p P hP (stretch P hP β p α M x) = uOf β p P hP x := by
    rw [uOf, uOf]
    by_cases hs : SOf β p P hP x = 1
    · have hx0 : 1 - SOf β p P hP x = 0 := by rw [hs]; ring
      have hy0 : 1 - SOf β p P hP (stretch P hP β p α M x) = 0 := by
        rw [h1S, hx0, zero_mul]
      rw [if_pos hy0, if_pos hx0]
    · have hxne : 1 - SOf β p P hP x ≠ 0 := by
        intro hc
        exact hs (by linarith)
      have hyne : 1 - SOf β p P hP (stretch P hP β p α M x) ≠ 0 := by
        rw [h1S]
        exact mul_ne_zero hxne (inv_ne_zero hdne)
      have hprod : denOf β p P hP α M x * (1 - SOf β p P hP (stretch P hP β p α M x)) =
          1 - SOf β p P hP x := by
        rw [h1S]
        have htmp : denOf β p P hP α M x * ((1 - SOf β p P hP x) * (denOf β p P hP α M x)⁻¹) =
            (1 - SOf β p P hP x) * (denOf β p P hP α M x * (denOf β p P hP α M x)⁻¹) := by
          ring
        rw [htmp, mul_inv_cancel₀ hdne, mul_one]
      have h2 : (1 - SOf β p P hP (stretch P hP β p α M x))⁻¹ * (denOf β p P hP α M x)⁻¹ =
          (1 - SOf β p P hP x)⁻¹ := by
        rw [← mul_inv_rev, hprod]
      rw [if_neg hyne, if_neg hxne, hA, smul_smul, h2]
  have hw : wOf β p P hP (stretch P hP β p α M x) = wOf β p P hP x := by
    rw [wOf, wOf]
    by_cases hs : SOf β p P hP x = 0
    · have hy0 : SOf β p P hP (stretch P hP β p α M x) = 0 := by rw [hS, hs, mul_zero]
      rw [if_pos hy0, if_pos hs]
    · have hyne : SOf β p P hP (stretch P hP β p α M x) ≠ 0 := by
        rw [hS]
        exact mul_ne_zero (mul_ne_zero htne (inv_ne_zero hdne)) hs
      have h2 : (SOf β p P hP (stretch P hP β p α M x))⁻¹ *
          (taperM β p P hP α M x * (denOf β p P hP α M x)⁻¹) = (SOf β p P hP x)⁻¹ := by
        rw [hS, mul_inv_rev, mul_assoc,
          inv_mul_cancel₀ (mul_ne_zero htne (inv_ne_zero hdne)), mul_one]
      rw [if_neg hyne, if_neg hs, hB, smul_smul, h2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hS, div_eq_mul_inv]; ring
  · rw [hA]
  · rw [hB, div_eq_mul_inv]
  · rw [segOf, segOf]
    exact Prod.ext hu hw

end Work.Geo.DualStretch
