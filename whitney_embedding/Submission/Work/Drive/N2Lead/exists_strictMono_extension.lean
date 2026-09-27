import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2Lead.extend_strictMono

namespace Work.Drive.N2Lead

/-- The smooth plateau `x ↦ smoothTransition ((x - A)/s) * smoothTransition ((B - x)/s)`: it is `1`
on the closed interval `[A + s, B - s]` and `0` off the open interval `(A, B)`. -/
noncomputable def smoothPlateau (A B s : ℝ) (x : ℝ) : ℝ :=
  Real.smoothTransition ((x - A) / s) * Real.smoothTransition ((B - x) / s)

theorem contDiff_smoothPlateau {A B s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (smoothPlateau A B s) := by
  have hs' : s ≠ 0 := ne_of_gt hs
  unfold smoothPlateau
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem smoothPlateau_eq_one {A B s x : ℝ} (hs : 0 < s) (hx : A + s ≤ x) (hx' : x ≤ B - s) :
    smoothPlateau A B s x = 1 := by
  have h1 : (1 : ℝ) ≤ (x - A) / s := by rw [le_div_iff₀ hs, one_mul]; linarith
  have h2 : (1 : ℝ) ≤ (B - x) / s := by rw [le_div_iff₀ hs, one_mul]; linarith
  unfold smoothPlateau
  rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, mul_one]

theorem smoothPlateau_eq_zero_left {A B s x : ℝ} (hs : 0 < s) (hx : x ≤ A) :
    smoothPlateau A B s x = 0 := by
  have h1 : (x - A) / s ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ hs.le; linarith
  unfold smoothPlateau
  rw [Real.smoothTransition.zero_of_nonpos h1, zero_mul]

theorem smoothPlateau_eq_zero_right {A B s x : ℝ} (hs : 0 < s) (hx : B ≤ x) :
    smoothPlateau A B s x = 0 := by
  have h1 : (B - x) / s ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ hs.le; linarith
  unfold smoothPlateau
  rw [Real.smoothTransition.zero_of_nonpos h1, mul_zero]

/-- **Globalising a function that is `C^∞` on an open set.**  If `g` is `C^∞` on the open set `J`
and the closed interval `[a,b]` (`a < b`) lies in `J`, then there is a globally `C^∞` function `ĝ`
which agrees with `g`, and with `deriv g`, on `[a,b]`. -/
theorem exists_contDiff_extension_of_Icc {g : ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J) {a b : ℝ}
    (hab : Set.Icc a b ⊆ J) (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g J) (hab' : a < b) :
    ∃ ĝ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ĝ ∧
      (∀ x ∈ Set.Icc a b, ĝ x = g x) ∧
      (∀ x ∈ Set.Icc a b, deriv ĝ x = deriv g x) := by
  obtain ⟨δ, hδ, hδsub⟩ := isCompact_Icc.exists_cthickening_subset_open hJ hab
  -- `[a - δ, b + δ]` is contained in `J`
  have hsub : Set.Icc (a - δ) (b + δ) ⊆ J := by
    intro x hx
    rcases le_or_gt x a with hxa | hxa
    · refine hδsub (Metric.mem_cthickening_of_dist_le x a δ (Set.Icc a b) ⟨le_rfl, hab'.le⟩ ?_)
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]
      linarith [hx.1]
    · rcases le_or_gt b x with hxb | hxb
      · refine hδsub (Metric.mem_cthickening_of_dist_le x b δ (Set.Icc a b) ⟨hab'.le, le_rfl⟩ ?_)
        rw [Real.dist_eq, abs_of_nonneg (by linarith)]
        linarith [hx.2]
      · exact hab ⟨hxa.le, hxb.le⟩
  have hδ4 : (0 : ℝ) < δ / 4 := by linarith
  -- the plateau bump: `1` on `[a - δ/4, b + δ/4]`, `0` off `(a - δ/2, b + δ/2)`
  have hχ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (smoothPlateau (a - δ / 2) (b + δ / 2) (δ / 4)) :=
    contDiff_smoothPlateau hδ4
  have hχ_one : ∀ x ∈ Set.Icc (a - δ / 4) (b + δ / 4),
      smoothPlateau (a - δ / 2) (b + δ / 2) (δ / 4) x = 1 := by
    intro x hx
    refine smoothPlateau_eq_one hδ4 ?_ ?_ <;> linarith [hx.1, hx.2]
  have hχ_zero_left : ∀ x ≤ a - δ / 2, smoothPlateau (a - δ / 2) (b + δ / 2) (δ / 4) x = 0 :=
    fun x hx => smoothPlateau_eq_zero_left hδ4 hx
  have hχ_zero_right : ∀ x, b + δ / 2 ≤ x →
      smoothPlateau (a - δ / 2) (b + δ / 2) (δ / 4) x = 0 :=
    fun x hx => smoothPlateau_eq_zero_right hδ4 hx
  have hχg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => smoothPlateau (a - δ / 2) (b + δ / 2) (δ / 4) x * g x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Set.Icc (a - δ) (b + δ)
    · exact hχ_smooth.contDiffAt.mul (hg.contDiffAt (hJ.mem_nhds (hsub hx)))
    · have hx' : x < a - δ ∨ b + δ < x := by
        rcases lt_or_ge x (a - δ) with h | h
        · exact Or.inl h
        · by_cases h2 : b + δ < x
          · exact Or.inr h2
          · exact absurd ⟨h, le_of_not_gt h2⟩ hx
      have hχ0 : ∀ᶠ y in nhds x, smoothPlateau (a - δ / 2) (b + δ / 2) (δ / 4) y = 0 := by
        rw [Metric.eventually_nhds_iff]
        refine ⟨δ / 2, by linarith, fun y hy => ?_⟩
        rcases hx' with h | h
        · refine hχ_zero_left y ?_
          rw [Real.dist_eq] at hy
          have := le_abs_self (y - x)
          linarith
        · refine hχ_zero_right y ?_
          rw [Real.dist_eq] at hy
          have := neg_le_abs (y - x)
          linarith
      have hev : (fun y => smoothPlateau (a - δ / 2) (b + δ / 2) (δ / 4) y * g y)
          =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
        filter_upwards [hχ0] with y hy
        simp [hy]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
  refine ⟨fun x => smoothPlateau (a - δ / 2) (b + δ / 2) (δ / 4) x * g x, hχg_smooth, ?_, ?_⟩
  · intro x hx
    have hxI : x ∈ Set.Icc (a - δ / 4) (b + δ / 4) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    simp [hχ_one x hxI]
  · intro x hx
    have hxint : x ∈ Set.Ioo (a - δ / 4) (b + δ / 4) :=
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hev : (fun y => smoothPlateau (a - δ / 2) (b + δ / 2) (δ / 4) y * g y) =ᶠ[nhds x] g := by
      have hmem : Set.Ioo (a - δ / 4) (b + δ / 4) ∈ nhds x := isOpen_Ioo.mem_nhds hxint
      filter_upwards [hmem] with y hy
      rw [hχ_one y ⟨hy.1.le, hy.2.le⟩, one_mul]
    exact hev.deriv_eq

open scoped Manifold ContDiff Topology in
/-- **A strictly increasing chart function extends to a globally strictly increasing smooth
function** (§3.1 (a) of `N2Lead/NOTES_LEAD_saddlePacket.md`).

If `g` is `C^∞` on an open `J` with `deriv g > 0` there, and the closed interval `[a, b]` is
contained in `J`, then `g` agrees on `[a, b]` with a function `G` that is `C^∞` on all of `ℝ` with
`deriv G > 0` everywhere.  Route: `G' = χ · g' + (1 - χ)` with a bump `χ` that is `1` on `[a, b]`
and supported in `J`, then `G x = g a + ∫_a^x G'`.  The close sibling
`Work.Drive.N2Lead.extend_strictMono` (`Submission/Work/Drive/N2Lead/extend_strictMono.lean`,
PROVED) does this for a globally smooth `g`; the gain here is the local domain.

This is the tool that lets the packet's angle functions (defined and monotone only on the two
pinned intervals) be fed to `Work.Drive.N2.circleArcExtension`, whose inputs are globally
monotone. -/
theorem exists_strictMono_extension {g : ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J) {a b : ℝ}
    (hab : Set.Icc a b ⊆ J) (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g J)
    (hg' : ∀ x ∈ J, 0 < deriv g x) :
    ∃ G : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G ∧ (∀ x : ℝ, 0 < deriv G x) ∧
      ∀ x ∈ Set.Icc a b, G x = g x := by
  rcases le_or_gt b a with hba | hab'
  · -- the interval is a single point (or empty): an affine function does the job
    refine ⟨fun x => x + (g a - a), ?_, ?_, ?_⟩
    · exact contDiff_id.add contDiff_const
    · intro x
      have h1 : deriv (fun y : ℝ => y + (g a - a)) x = 1 := by
        simp [deriv_add_const (f := fun y : ℝ => y) (g a - a) (x := x), deriv_id'']
      rw [h1]
      norm_num
    · intro x hx
      have hx' : x = a := le_antisymm (hx.2.trans hba) hx.1
      rw [hx']
      show a + (g a - a) = g a
      ring
  · -- globalise `g` near `[a,b]`, then apply the sibling for a globally smooth function
    obtain ⟨ĝ, hĝsm, hĝeq, hĝder⟩ := exists_contDiff_extension_of_Icc hJ hab hg hab'
    obtain ⟨G, hGsm, hGder, hGeq⟩ :=
      extend_strictMono hab' hĝsm (fun x hx => by rw [hĝder x hx]; exact hg' x (hab hx))
    exact ⟨G, hGsm, hGder, fun x hx => by rw [hGeq x hx, hĝeq x hx]⟩

end Work.Drive.N2Lead
