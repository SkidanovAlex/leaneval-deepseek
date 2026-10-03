import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.l62c_basic

/-!
# L62 (c): the end choice and the uniform drift of Lemma 6.2

Shishikura's Lemma 6.2 pairs every `β` with the end (`Bu` or `Bl`) that *avoids the critical
value* of `ĥ = d.E - β`.  This file contains the elementary bookkeeping of that choice:

* `AvailableUp d hd β` / `AvailableDown d hd β`: `Bu` (resp. `Bl`) misses the critical class
  `v + ℤ - β`;
* at least one of the two always holds (`Bu`, `Bl` are disjoint and `T`-invariant, so their
  `piExp`-images are disjoint, while the critical class is a single `T`-orbit);
* both sets of `β` are closed and invariant under `β ↦ β + 1`.

The last two properties, together with the strict sign implications proved elsewhere
(`avail_up`: `AvailableUp β → 0 < β.im`; `avail_down`: `AvailableDown β → β.im < cl.im`) give a
**uniform** drift `κ > 0`: for every `β` there is an available end on which the branch of `ĥ` has
drift at least `κ` in the direction of that end.  That is what makes the constants of Lemma 6.2
independent of `β`.
-/

namespace Work.L62

open MandelDim Set Filter Topology Complex
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-! ## Integer shifts -/

/-- A predicate invariant under `β ↦ β + 1` is invariant under all natural shifts. -/
theorem prop_add_nat {P : ℂ → Prop} (h : ∀ β : ℂ, P β ↔ P (β + 1)) (β : ℂ) :
    ∀ n : ℕ, (P β ↔ P (β + (n : ℂ))) := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
      have hstep : β + ((m + 1 : ℕ) : ℂ) = (β + (m : ℂ)) + 1 := by push_cast; ring
      rw [hstep, ← h (β + (m : ℂ))]
      exact ih

/-- A predicate invariant under `β ↦ β + 1` is invariant under all integer shifts. -/
theorem prop_add_int {P : ℂ → Prop} (h : ∀ β : ℂ, P β ↔ P (β + 1)) (β : ℂ) (k : ℤ) :
    (P β ↔ P (β + (k : ℂ))) := by
  rcases lt_or_ge 0 k with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk.le
    exact prop_add_nat h β n
  · obtain ⟨n, hkn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -k by omega)
    have hk' : k = -(n : ℤ) := by omega
    have hz : β + (k : ℂ) + (n : ℂ) = β := by
      rw [hk']; push_cast; ring
    have h1 := prop_add_nat h (β + (k : ℂ)) n
    rw [hz] at h1
    exact h1.symm

/-- A `T`-invariant set is invariant under all integer shifts. -/
theorem IsTInvariant.mem_add_int {U : Set ℂ} (h : IsTInvariant U) (w : ℂ) (k : ℤ) :
    (w ∈ U ↔ w + (k : ℂ) ∈ U) :=
  prop_add_int (fun z => h z) w k

/-! ## `piExp` and the two horns -/

/-- `piExp` is the quotient map `ℂ → ℂ/ℤ`. -/
theorem piExp_eq_iff_exists_int (a b : ℂ) : piExp a = piExp b ↔ ∃ k : ℤ, a = b + (k : ℂ) := by
  have hne : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [hpi, Complex.I_ne_zero]
  constructor
  · intro heq
    rw [piExp, piExp, Complex.exp_eq_exp_iff_exists_int] at heq
    obtain ⟨n, hn⟩ := heq
    refine ⟨n, ?_⟩
    refine mul_left_cancel₀ hne ?_
    rw [hn]
    ring
  · rintro ⟨n, rfl⟩
    rw [piExp, piExp, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨n, ?_⟩
    ring

/-- The two horns are disjoint in the cylinder. -/
theorem disjoint_piExp_image (d : ParabData g₀ D) (hd : HornData d) :
    Disjoint (piExp '' hd.Bu) (piExp '' hd.Bl) := by
  refine Set.disjoint_left.mpr fun ζ hζu hζl => ?_
  obtain ⟨w₁, hw₁, rfl⟩ := hζu
  obtain ⟨w₂, hw₂, hweq⟩ := hζl
  obtain ⟨k, hk⟩ := (piExp_eq_iff_exists_int w₂ w₁).mp hweq
  have hmem : w₁ ∈ hd.Bl := by
    refine (IsTInvariant.mem_add_int hd.Bl_T w₁ k).mpr ?_
    rw [← hk]
    exact hw₂
  exact (Set.disjoint_left.mp hd.disj) hw₁ hmem

/-! ## Availability of an end -/

/-- `Bu` avoids the critical values of `ĥ = d.E - β`, so that `ĥ` has a global inverse branch
over `Bu` (`exists_section_horn`). -/
def AvailableUp (d : ParabData g₀ D) (hd : HornData d) (β : ℂ) : Prop :=
  ∀ w ∈ hd.Bu, ∀ k : ℤ, w + β ≠ hd.v + (k : ℂ)

/-- `Bl` avoids the critical values of `ĥ = d.E - β`. -/
def AvailableDown (d : ParabData g₀ D) (hd : HornData d) (β : ℂ) : Prop :=
  ∀ w ∈ hd.Bl, ∀ k : ℤ, w + β ≠ hd.v + (k : ℂ)

/-- **At least one end is available.**  `Bu` and `Bl` are disjoint and `T`-invariant, so a single
`T`-orbit (`v + ℤ`) cannot meet both. -/
theorem availableUp_or_availableDown (d : ParabData g₀ D) (hd : HornData d) (β : ℂ) :
    AvailableUp d hd β ∨ AvailableDown d hd β := by
  rcases em (∃ w ∈ hd.Bu, ∃ k : ℤ, w + β = hd.v + (k : ℂ)) with ⟨w₁, hw₁, k₁, hk₁⟩ | hno
  · right
    intro w₂ hw₂ k₂ hk₂
    have hw' : w₁ + ((k₂ - k₁ : ℤ) : ℂ) = w₂ := by
      have hsum : (w₁ + ((k₂ - k₁ : ℤ) : ℂ)) + β = w₂ + β := by
        have hcast : ((k₂ - k₁ : ℤ) : ℂ) = (k₂ : ℂ) - (k₁ : ℂ) := by push_cast; ring
        rw [hcast]
        linear_combination hk₁ - hk₂
      exact add_right_cancel hsum
    have hmem : w₁ + ((k₂ - k₁ : ℤ) : ℂ) ∈ hd.Bl := by rw [hw']; exact hw₂
    have hmem' : w₁ ∈ hd.Bl := (IsTInvariant.mem_add_int hd.Bl_T w₁ (k₂ - k₁)).mpr hmem
    exact (Set.disjoint_left.mp hd.disj) hw₁ hmem'
  · left
    intro w hw k hne
    exact hno ⟨w, hw, k, hne⟩

/-- The set of `β` for which `Bu` is available is closed: its complement is
`⋃ k, (v + k - ·) '' Bu`, a union of open sets. -/
theorem isClosed_availableUp (d : ParabData g₀ D) (hd : HornData d) :
    IsClosed {β : ℂ | AvailableUp d hd β} := by
  have hset : {β : ℂ | AvailableUp d hd β}
      = (⋃ k : ℤ, (fun w : ℂ => hd.v + (k : ℂ) - w) '' hd.Bu)ᶜ := by
    ext β
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_image, AvailableUp]
    constructor
    · intro h hmem
      obtain ⟨k, w, hw, hwβ⟩ := hmem
      exact h w hw k (by rw [← hwβ]; ring)
    · rintro h w hw k hwk
      exact h ⟨k, w, hw, by rw [← hwk]; ring⟩
  rw [hset]
  refine isClosed_compl_iff.mpr (isOpen_iUnion fun k => ?_)
  have himg : (fun w : ℂ => hd.v + (k : ℂ) - w) '' hd.Bu
      = (fun w : ℂ => hd.v + (k : ℂ) - w) ⁻¹' hd.Bu := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hfix : hd.v + (k : ℂ) - (hd.v + (k : ℂ) - w) = w := by ring
      simpa only [Set.mem_preimage, hfix] using hw
    · intro hx
      exact ⟨hd.v + (k : ℂ) - x, hx, by ring⟩
  rw [himg]
  exact hd.Bu_open.preimage (by continuity)

/-- The set of `β` for which `Bl` is available is closed. -/
theorem isClosed_availableDown (d : ParabData g₀ D) (hd : HornData d) :
    IsClosed {β : ℂ | AvailableDown d hd β} := by
  have hset : {β : ℂ | AvailableDown d hd β}
      = (⋃ k : ℤ, (fun w : ℂ => hd.v + (k : ℂ) - w) '' hd.Bl)ᶜ := by
    ext β
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_image, AvailableDown]
    constructor
    · intro h hmem
      obtain ⟨k, w, hw, hwβ⟩ := hmem
      exact h w hw k (by rw [← hwβ]; ring)
    · rintro h w hw k hwk
      exact h ⟨k, w, hw, by rw [← hwk]; ring⟩
  rw [hset]
  refine isClosed_compl_iff.mpr (isOpen_iUnion fun k => ?_)
  have himg : (fun w : ℂ => hd.v + (k : ℂ) - w) '' hd.Bl
      = (fun w : ℂ => hd.v + (k : ℂ) - w) ⁻¹' hd.Bl := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hfix : hd.v + (k : ℂ) - (hd.v + (k : ℂ) - w) = w := by ring
      simpa only [Set.mem_preimage, hfix] using hw
    · intro hx
      exact ⟨hd.v + (k : ℂ) - x, hx, by ring⟩
  rw [himg]
  exact hd.Bl_open.preimage (by continuity)

/-- Availability of `Bu` is invariant under `β ↦ β + 1` (the critical class and `Bu` are both
`T`-invariant). -/
theorem availableUp_add_one (d : ParabData g₀ D) (hd : HornData d) (β : ℂ) :
    AvailableUp d hd β ↔ AvailableUp d hd (β + 1) := by
  constructor
  · intro h w hw k hcontra
    have hw1 : w + 1 ∈ hd.Bu := (hd.Bu_T w).mp hw
    have hkey : (w + 1) + β = hd.v + (k : ℂ) := by
      have h' : w + (β + 1) = hd.v + (k : ℂ) := hcontra
      linear_combination h'
    exact h (w + 1) hw1 k hkey
  · intro h w hw k hcontra
    have hwm : w - 1 ∈ hd.Bu := (hd.Bu_T (w - 1)).mpr (by simpa using hw)
    have hkey : (w - 1) + (β + 1) = hd.v + (k : ℂ) := by
      have h' : w + β = hd.v + (k : ℂ) := hcontra
      linear_combination h'
    exact h (w - 1) hwm k hkey

/-- Availability of `Bl` is invariant under `β ↦ β + 1`. -/
theorem availableDown_add_one (d : ParabData g₀ D) (hd : HornData d) (β : ℂ) :
    AvailableDown d hd β ↔ AvailableDown d hd (β + 1) := by
  constructor
  · intro h w hw k hcontra
    have hw1 : w + 1 ∈ hd.Bl := (hd.Bl_T w).mp hw
    have hkey : (w + 1) + β = hd.v + (k : ℂ) := by
      have h' : w + (β + 1) = hd.v + (k : ℂ) := hcontra
      linear_combination h'
    exact h (w + 1) hw1 k hkey
  · intro h w hw k hcontra
    have hwm : w - 1 ∈ hd.Bl := (hd.Bl_T (w - 1)).mpr (by simpa using hw)
    have hkey : (w - 1) + (β + 1) = hd.v + (k : ℂ) := by
      have h' : w + β = hd.v + (k : ℂ) := hcontra
      linear_combination h'
    exact h (w - 1) hwm k hkey

/-! ## Uniform drift -/

/-- A closed, `1`-periodic set which avoids a horizontal line is bounded away from it. -/
theorem exists_dist_to_line {S : Set ℂ} {t : ℝ} (hScl : IsClosed S)
    (hSp : ∀ β : ℂ, β ∈ S ↔ β + 1 ∈ S) (hav : ∀ β ∈ S, β.im ≠ t) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ β ∈ S, ε ≤ |β.im - t| := by
  have box_compact : ∀ lo hi : ℝ,
      IsCompact {z : ℂ | z.re ∈ Icc (0:ℝ) 1 ∧ z.im ∈ Icc lo hi} := by
    intro lo hi
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · have h1 : IsClosed {z : ℂ | z.re ∈ Icc (0:ℝ) 1} := isClosed_Icc.preimage Complex.continuous_re
      have h2 : IsClosed {z : ℂ | z.im ∈ Icc lo hi} := isClosed_Icc.preimage Complex.continuous_im
      simpa [Set.setOf_and] using h1.inter h2
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + |lo| + |hi|)).subset ?_
      intro z hz
      obtain ⟨hre, him⟩ := hz
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      have h2 : |z.re| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [hre.1], hre.2⟩
      have h3 : |z.im| ≤ |lo| + |hi| := by
        rw [abs_le]
        exact ⟨by linarith [him.1, neg_abs_le lo, neg_abs_le hi, abs_nonneg lo, abs_nonneg hi],
               by linarith [him.2, le_abs_self lo, le_abs_self hi, abs_nonneg lo, abs_nonneg hi]⟩
      linarith
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ n : ℕ, ∃ β ∈ S, |β.im - t| < 1 / (n + 1) :=
    fun n => hcon (1 / (n + 1)) (by positivity)
  choose u huS huim using hseq
  set u' : ℕ → ℂ := fun n => u n + ((-(⌊(u n).re⌋) : ℤ) : ℂ) with hu'def
  have hu'S : ∀ n, u' n ∈ S := by
    intro n
    have h := (prop_add_int hSp (u n) (-(⌊(u n).re⌋))).mp (huS n)
    simpa [hu'def] using h
  have hre : ∀ n, (u' n).re ∈ Icc (0:ℝ) 1 := by
    intro n
    have h1 : (u' n).re = (u n).re - (⌊(u n).re⌋ : ℝ) := by
      show (u n + ((-(⌊(u n).re⌋) : ℤ) : ℂ)).re = _
      rw [Complex.add_re, Complex.intCast_re]
      push_cast
      ring
    constructor
    · rw [h1]; exact sub_nonneg.mpr (Int.floor_le _)
    · rw [h1]
      have := Int.lt_floor_add_one (u n).re
      linarith
  have him : ∀ n, (u' n).im = (u n).im := by
    intro n
    show (u n + ((-(⌊(u n).re⌋) : ℤ) : ℂ)).im = _
    rw [Complex.add_im, Complex.intCast_im]
    ring
  have huim' : ∀ n, |(u' n).im - t| < 1 / (n + 1) := by
    intro n
    rw [him n]
    exact huim n
  have hsmall : ∀ n, |(u' n).im - t| < 1 := by
    intro n
    refine lt_of_lt_of_le (huim' n) ?_
    rw [div_le_one (by positivity)]
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hKmem : ∀ n, u' n ∈ {z : ℂ | z.re ∈ Icc (0:ℝ) 1 ∧ z.im ∈ Icc (t - 1) (t + 1)} := by
    intro n
    refine ⟨hre n, ?_, ?_⟩
    · have := neg_abs_le ((u' n).im - t)
      linarith [hsmall n]
    · have := le_abs_self ((u' n).im - t)
      linarith [hsmall n]
  obtain ⟨a, haK, φ, hφ, htend⟩ := (box_compact (t - 1) (t + 1)).tendsto_subseq hKmem
  have haS : a ∈ S := hScl.mem_of_tendsto htend (Eventually.of_forall fun n => hu'S (φ n))
  have hlim : Tendsto (fun n : ℕ => |(u' (φ n)).im - t|) atTop (𝓝 |a.im - t|) := by
    have h1 : Tendsto (fun n : ℕ => (u' (φ n)).im) atTop (𝓝 a.im) :=
      (Complex.continuous_im.tendsto a).comp htend
    exact (h1.sub tendsto_const_nhds).abs
  have hbound : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((φ n : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_mono (fun n => le_add_of_nonneg_right zero_le_one)
        (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
    have h2 : Tendsto (fun n : ℕ => (((φ n : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h1
    simpa [one_div] using h2
  have hle : ∀ n : ℕ, |(u' (φ n)).im - t| ≤ 1 / ((φ n : ℝ) + 1) := by
    intro n
    exact (huim' (φ n)).le
  have hzero : |a.im - t| ≤ 0 := le_of_tendsto_of_tendsto' hlim hbound hle
  have haeq : a.im = t := by
    have h2 : |a.im - t| = 0 := le_antisymm hzero (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp h2)
  exact hav a haS haeq

/-- **Uniform drift from a closed, `1`-periodic cover of the `β`-plane.**  If `A ∪ B = ℂ`, both
`A` and `B` are closed and periodic, `A ⊆ {0 < Im}` and `B ⊆ {Im < c}`, then there is `κ > 0`
with `κ ≤ Im β` on `A` and `κ ≤ c - Im β` on `B`.  This is the compactness step that makes the
constants of Lemma 6.2 independent of `β`. -/
theorem uniform_drift {A B : Set ℂ} {c : ℝ}
    (hAc : IsClosed A) (hBc : IsClosed B) (hcov : ∀ β : ℂ, β ∈ A ∨ β ∈ B)
    (hAp : ∀ β : ℂ, β ∈ A ↔ β + 1 ∈ A) (hBp : ∀ β : ℂ, β ∈ B ↔ β + 1 ∈ B)
    (hA : ∀ β ∈ A, 0 < β.im) (hB : ∀ β ∈ B, β.im < c) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ β : ℂ, (β ∈ A ∧ κ ≤ β.im) ∨ (β ∈ B ∧ κ ≤ c - β.im) := by
  obtain ⟨εA, hεA0, hεA⟩ := exists_dist_to_line hAc hAp (fun β hβ => ne_of_gt (hA β hβ))
  obtain ⟨εB, hεB0, hεB⟩ := exists_dist_to_line hBc hBp (fun β hβ => ne_of_lt (hB β hβ))
  refine ⟨min εA εB, lt_min hεA0 hεB0, fun β => ?_⟩
  rcases hcov β with hβ | hβ
  · refine Or.inl ⟨hβ, le_trans (min_le_left _ _) ?_⟩
    have h := hεA β hβ
    rw [sub_zero, abs_of_pos (hA β hβ)] at h
    exact h
  · refine Or.inr ⟨hβ, le_trans (min_le_right _ _) ?_⟩
    have h := hεB β hβ
    have hneg : β.im - c < 0 := sub_neg.mpr (hB β hβ)
    rw [abs_of_neg hneg] at h
    linarith

/-- **The uniform drift of Lemma 6.2.**  With the two strict sign implications (`avail_up`,
`avail_down`) the two available ends give, for every `β`, a branch of `ĥ = d.E - β` whose drift
in the direction of that end is at least a fixed `κ > 0`. -/
theorem exists_uniform_drift (d : ParabData g₀ D) (hd : HornData d) {cl : ℂ}
    (hup : ∀ β : ℂ, AvailableUp d hd β → 0 < β.im)
    (hdn : ∀ β : ℂ, AvailableDown d hd β → β.im < cl.im) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ β : ℂ,
      (AvailableUp d hd β ∧ κ ≤ β.im) ∨ (AvailableDown d hd β ∧ κ ≤ cl.im - β.im) :=
  uniform_drift (isClosed_availableUp d hd) (isClosed_availableDown d hd)
    (availableUp_or_availableDown d hd) (availableUp_add_one d hd) (availableDown_add_one d hd)
    hup hdn

end

end Work.L62
