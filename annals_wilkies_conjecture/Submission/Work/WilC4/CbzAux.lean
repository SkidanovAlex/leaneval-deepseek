import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.ErealDefs
import Submission.Work.WilC4.ULPMRoute
import Submission.Work.WilC4.ULPMExp

set_option autoImplicit false
noncomputable section
open Classical Set
namespace Work.WilC4

open Work.WilC4.Route

variable {k : ℕ}

/-! ## Basic facts about the doubling ratio at deep points -/

/-- At the inner window of an `M`-deep point (`M ≥ 2`), every point is `2`-deep: the scale-`2`
forbidden window sits inside the scale-`M` one. -/
theorem cbz_two_of_window {B : Set (Fin (k + 1) → ℝ)} {c : Fin k → ℝ} {M x t : ℝ}
    (hM : 2 ≤ M) (hx : 0 < x) (hdeep : IsDeepR B c M x)
    (ht1 : 2 * x / M ≤ t) (ht2 : t ≤ M * x / 2) : IsDeepR B c 2 t := by
  intro b hb hb'
  have hMpos : 0 < M := by linarith
  have hden : (0 : ℝ) < 2 * M := by positivity
  exact hdeep b hb ⟨by
      have h1 : x / (2 * M) ≤ t / 4 := by
        rw [div_le_iff₀ hden]
        have h3 : 2 * x ≤ t * M := by
          rw [div_le_iff₀ hMpos] at ht1
          linarith [ht1]
        nlinarith [h3]
      linarith [h1, hb'.1], by
      have h2 : 2 * 2 * t ≤ 2 * M * x := by nlinarith [ht2, hMpos, hx]
      linarith [hb'.2, h2]⟩

/-- The doubling ratio `ratioY` is a genuine `RatW` value at every point of the window
`(x/(2β), βx)` of a `β`-deep point `x`. -/
theorem cbz_ratW_ratioY_of_deep {Y : Set (Fin (k + 2) → ℝ)} {B : Set (Fin (k + 1) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    (hgf : GoodFibre Y B) {c : Fin k → ℝ} {β x : ℝ} (hβ : 1 < β) (hx : 0 < x)
    (hdeep : IsDeepR B c β x) {z : ℝ} (hz : z ∈ Set.Ioo (x / (2 * β)) (β * x)) :
    RatW Y c z (ratioY Y c z) := by
  have hβ1 : 1 ≤ β := le_of_lt hβ
  have hβ0 : 0 < β := by linarith
  have hz1 : x / (2 * β) < z := hz.1
  have hz2 : z < β * x := hz.2
  have hzpos : 0 < z := lt_trans (div_pos hx (by positivity)) hz1
  obtain ⟨hg1, hnz⟩ := deep_val hgf hβ1 hx hdeep
    (show z ∈ Set.Ioo (x / (2 * β)) (2 * β * x) from ⟨hz1, by nlinarith [hz2, hx, hβ0]⟩)
  obtain ⟨hg2, -⟩ := deep_val hgf hβ1 hx hdeep
    (show 2 * z ∈ Set.Ioo (x / (2 * β)) (2 * β * x) from
      ⟨by linarith, by nlinarith [hz2, hx, hβ0]⟩)
  exact (ratW_iff_valY hfun c z (ratioY Y c z)).mpr ⟨hg1, hg2, hnz, rfl⟩

/-- At a point where the fibre is a function, the `RatW` value is literally `ratioY`. -/
theorem cbz_ratW_eq_ratioY {Y : Set (Fin (k + 2) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    {c : Fin k → ℝ} {x w : ℝ} (hrat : RatW Y c x w) : w = ratioY Y c x :=
  ((ratW_iff_valY hfun c x w).mp hrat).2.2.2

/-- The doubling ratio at a `2`-deep point is positive (`GoodFibre` gives constant sign on the
deep window). -/
theorem cbz_ratW_pos {Y : Set (Fin (k + 2) → ℝ)} {B : Set (Fin (k + 1) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    (hgf : GoodFibre Y B) {c : Fin k → ℝ} {M x w : ℝ} (hM : 2 ≤ M) (hx : 0 < x)
    (hdeep : IsDeepR B c M x) (hrat : RatW Y c x w) : 0 < w := by
  obtain ⟨hg1, hg2, hnz, hw⟩ := (ratW_iff_valY hfun c x w).mp hrat
  rw [hw, ratioY, div_pos_iff]
  have hM1 : 1 ≤ M := by linarith
  have hMpos : 0 < M := by linarith
  have hxw : x ∈ Set.Ioo (x / (2 * M)) (2 * M * x) := by
    refine ⟨?_, by nlinarith [hx, hMpos]⟩
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * M)]
    nlinarith [hx, hM]
  have h2xw : 2 * x ∈ Set.Ioo (x / (2 * M)) (2 * M * x) := by
    refine ⟨?_, by nlinarith [hx, hMpos]⟩
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * M)]
    nlinarith [hx, hM]
  have hsign := deep_sign hgf hM1 hx hdeep hxw h2xw hg1 hg2
  rcases mul_pos_iff.mp hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h2, h1⟩
  · exact Or.inr ⟨h2, h1⟩

/-- The "window avoids the geometric midpoints of `E`" hypothesis of `caseA_bad_bounded_zero`. -/
def CbzAvoid {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (E : Set ℝ) (M : ℝ) (c : Fin k → ℝ)
    (x : ℝ) : Prop :=
  ∀ z ∈ Set.Ioo (x / (2 * M)) (2 * M * x), ∀ u : ℝ, RatW Y c z u → u ∉ Mid E

/-- The "the rescaled ratio is monotone on `(1/M, M)`" hypothesis. -/
def CbzMono {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (M : ℝ) (c : Fin k → ℝ) (x : ℝ) : Prop :=
  (MonotoneOn (fun s : ℝ => ratioY Y c (x * s)) (Set.Ioo (1 / M) M) ∨
    AntitoneOn (fun s : ℝ => ratioY Y c (x * s)) (Set.Ioo (1 / M) M))

lemma cbz_rpow_inv {N m : ℕ} {W : ℝ} (hN : 0 < N) (hm : 0 < m)
    (h : (N : ℝ) ^ (2 * m) ≤ W) : (N : ℝ) ^ 2 ≤ W ^ ((1 : ℝ) / (m : ℝ)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have h1 : (((N : ℝ) ^ (2 * m) : ℝ)) ^ ((1 : ℝ) / (m : ℝ)) ≤ W ^ ((1 : ℝ) / (m : ℝ)) :=
    Real.rpow_le_rpow (by positivity) h (by positivity)
  have h2 : (((N : ℝ) ^ (2 * m) : ℝ)) ^ ((1 : ℝ) / (m : ℝ)) = (N : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
    have : ((2 * m : ℕ) : ℝ) * ((1 : ℝ) / (m : ℝ)) = 2 := by
      push_cast
      field_simp
    rw [this, Real.rpow_two]
  rw [h2] at h1
  exact h1

/-- Being strictly between `a` and `b` is symmetric. -/
lemma cbz_between_comm {a b m : ℝ} (h : min a b < m ∧ m < max a b) :
    min b a < m ∧ m < max b a := by
  rwa [min_comm, max_comm]

/-- `ratioY` is continuous on the one-sided deep window `(x/(2M), M x)`. -/
theorem cbz_ratioY_cont {Y : Set (Fin (k + 2) → ℝ)} {B : Set (Fin (k + 1) → ℝ)}
    (hgf : GoodFibre Y B) {c : Fin k → ℝ} {M x : ℝ} (hM : 1 ≤ M) (hx : 0 < x)
    (hdeep : IsDeepR B c M x) :
    ContinuousOn (fun t : ℝ => ratioY Y c t) (Set.Ioo (x / (2 * M)) (M * x)) := by
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM
  have hsub : Set.Ioo (x / (2 * M)) (M * x) ⊆ Set.Ioo (x / (2 * M)) (2 * M * x) := by
    intro t ht
    exact ⟨ht.1, by nlinarith [ht.2, hx, hMpos]⟩
  have hcont : ContinuousOn (fun t : ℝ => valY Y c t) (Set.Ioo (x / (2 * M)) (2 * M * x)) :=
    deep_cont hgf hM hx hdeep
  have hden : ContinuousOn (fun t : ℝ => valY Y c t) (Set.Ioo (x / (2 * M)) (M * x)) :=
    hcont.mono hsub
  have hne : ∀ t ∈ Set.Ioo (x / (2 * M)) (M * x), valY Y c t ≠ 0 :=
    fun t ht => (deep_val hgf hM hx hdeep (hsub ht)).2
  have h2cont : ContinuousOn (fun t : ℝ => 2 * t) (Set.Ioo (x / (2 * M)) (M * x)) :=
    (continuous_const.mul continuous_id).continuousOn
  have hnum : ContinuousOn (fun t : ℝ => valY Y c (2 * t)) (Set.Ioo (x / (2 * M)) (M * x)) :=
    hcont.comp h2cont
      (fun t ht => ⟨by
        have hxp : 0 < x / (2 * M) := by positivity
        nlinarith [ht.1, hxp, hx, hMpos],
        by nlinarith [ht.2, hx, hMpos]⟩)
  have hdiv := hnum.div hden hne
  exact hdiv


end Work.WilC4
