import Mathlib

/-!
# Persistence of the number of "ray-meeting" zeros of a one-dimensional `C¹` function

This is the one-dimensional engine of `Work.Surf.ncard_rayMeet_persist`.

Let `g : ℝ → ℝ` be `C¹` and `h : ℝ → ℝ` continuous.  Think of `t ↦ (g t, h t)` as the coordinates of
a plane vector, so that the *ray-meeting* set of the pair `(g, h)` on `[0,1]` is

`S := {t ∈ [0,1] | g t = 0 ∧ 0 < h t}`.

Assume

* `S` is finite and contained in `(0,1)`;
* every `t ∈ S` is a *simple* zero of `g`, i.e. `deriv g t ≠ 0`;
* the remaining zeros of `g` in `[0,1]` (the "anti-ray" ones, where `h ≤ 0`) are *strictly* negative:
  `h ≤ -m < 0` on `{t ∈ [0,1] | g t = 0, h t ≤ 0}`.

Then there is `δ > 0` with the following property: for every pair `(g', h')` of a `C¹` function `g'`
and a continuous `h'` which are `δ`-close to `(g, h)` on `[0,1]` — `g'` in the `C¹` sense, `h'` in the
`C⁰` sense — the ray-meeting set of `(g', h')` is finite, contained in `(0,1)`, and has exactly as
many points as `S`.

## Proof plan

Let `m₁ > 0` be a lower bound for `h` on the finite set `S` (`m₁ := 1` if `S = ∅`).  Since the points
of `S` are simple zeros of `g` lying in the interior of `[0,1]`, for each `p ∈ S` one chooses an
interval `I_p = [p - e_p, p + e_p]`, contained in `(0,1)`, small enough that

* the `I_p` are pairwise disjoint (possible because `S` is finite);
* `deriv g` keeps a constant *strict* sign on `I_p`, with `|deriv g| ≥ |deriv g p| / 2` there;
* `h ≥ 3 m₁ / 4` on `I_p`;
* `g` changes sign across `p` (mean value theorem).

Put `V := ⋃_{p ∈ S} I_p`.  Then, for a `δ`-perturbation with `δ` small enough:

* on `V` the set `{t | g' t = 0}` meets each `I_p` in exactly one point `z_p`: existence from the
  intermediate value theorem, uniqueness from Rolle's theorem and `|deriv g'| > 0` on `I_p`; and
  `h' z_p > 0`;
* on `[0,1] \ V` there is no ray-meeting point of `(g', h')`.  For `t ∈ [0,1] \ V` either
  `h t < -m/2`, in which case `h' t < 0`; or `h t ≥ -m/2`, in which case `t` lies in the compact set
  `K := {t ∈ [0,1] | h t ≥ -m/2}`.  The zeros of `g` in `K` are exactly the points of `S`, so `g` has
  no zero on the compact set `K ∩ (Vᵒ)ᶜ` (`Vᵒ` the union of the *open* intervals), whence
  `|g| ≥ m₄ > 0` there and `g' ≠ 0` on that set.

Consequently the ray-meeting set of `(g', h')` is exactly `{z_p : p ∈ S}`, a set in bijection with
`S`, and it is contained in `(0,1)`.
-/

namespace Work.Surf

open Set Filter

open scoped Topology

/-- A positive lower bound of a positive function on a finite set. -/
lemma zsp_exists_pos_le_of_finite {α : Type*} {s : Set α} (hs : s.Finite) {f : α → ℝ}
    (hpos : ∀ x ∈ s, 0 < f x) : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ s, m ≤ f x := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · refine ⟨hs.toFinset.inf' (hs.toFinset_nonempty.mpr hne) f, ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro x hx
      exact hpos x ((hs.mem_toFinset).mp hx)
    · intro x hx
      exact Finset.inf'_le f ((hs.mem_toFinset).mpr hx)

/-- A uniform separation radius for a finite set of reals. -/
lemma zsp_sep {s : Set ℝ} (hs : s.Finite) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ p ∈ s, ∀ q ∈ s, p ≠ q → 2 * ρ ≤ |p - q| := by
  classical
  by_cases h1 : ∀ p ∈ s, ∀ q ∈ s, p = q
  · exact ⟨1, one_pos, fun p hp q hq hpq => absurd (h1 p hp q hq) hpq⟩
  · push Not at h1
    obtain ⟨p₀, hp₀, q₀, hq₀, hne₀⟩ := h1
    set T : Finset ℝ := hs.toFinset with hT
    have hTm : ∀ x : ℝ, x ∈ T ↔ x ∈ s := fun x => hs.mem_toFinset
    set P : Finset ℝ := ((T.product T).filter (fun z : ℝ × ℝ => z.1 ≠ z.2)).image
      (fun z : ℝ × ℝ => |z.1 - z.2|) with hP
    have hPne : P.Nonempty := by
      refine ⟨|p₀ - q₀|, ?_⟩
      rw [hP]
      apply Finset.mem_image.mpr
      refine ⟨(p₀, q₀), ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(hTm p₀).mpr hp₀, (hTm q₀).mpr hq₀⟩, hne₀⟩
    have hPpos : 0 < P.min' hPne := by
      obtain ⟨z, hz, hz2⟩ := Finset.mem_image.mp (Finset.min'_mem P hPne)
      rw [← hz2]
      exact abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hz).2)
    refine ⟨P.min' hPne / 2, by linarith, ?_⟩
    intro p hp q hq hpq
    have hmem : |p - q| ∈ P := by
      rw [hP]
      apply Finset.mem_image.mpr
      refine ⟨(p, q), ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(hTm p).mpr hp, (hTm q).mpr hq⟩, hpq⟩
    have hle := Finset.min'_le P _ hmem
    have hpos : 0 < |p - q| := abs_pos.mpr (sub_ne_zero.mpr hpq)
    linarith

/-- If `y` is within `|x|/2` of a non-zero `x`, then `x` and `y` have the same strict sign. -/
lemma zsp_mul_pos_of_abs_sub_le {x y : ℝ} (hx : x ≠ 0) (h : |y - x| ≤ |x| / 2) : 0 < x * y := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · rw [abs_of_neg hneg] at h2
    have hy : y < 0 := by linarith
    exact mul_pos_of_neg_of_neg hneg hy
  · rw [abs_of_pos hpos] at h1
    have hy : 0 < y := by linarith
    exact mul_pos hpos hy

/-- On an interval on which `deriv g` never vanishes, `deriv g` has the same sign as at any point of
the interval. -/
lemma zsp_deriv_same_sign {g : ℝ → ℝ} (hgc : Continuous (deriv g)) {a b p s : ℝ}
    (hp : p ∈ Set.Icc a b) (hs : s ∈ Set.Icc a b) (hne : ∀ x ∈ Set.Icc a b, deriv g x ≠ 0) :
    0 < deriv g s * deriv g p := by
  rcases eq_or_ne s p with hsp_eq | hsp
  · rw [hsp_eq]; exact mul_self_pos.mpr (hne p hp)
  · by_contra hcon
    have hs0 : deriv g s ≠ 0 := hne s hs
    have hp0 : deriv g p ≠ 0 := hne p hp
    have hlt : deriv g s * deriv g p < 0 :=
      lt_of_le_of_ne (not_lt.mp hcon) (mul_ne_zero hs0 hp0)
    rcases lt_or_gt_of_ne hs0 with hsn | hspos
    · have hpp : 0 < deriv g p := by nlinarith
      rcases lt_or_gt_of_ne hsp with hsp' | hps'
      · have hsub : Set.Icc s p ⊆ Set.Icc a b := fun x hx => ⟨le_trans hs.1 hx.1, le_trans hx.2 hp.2⟩
        obtain ⟨x, hx, hxv⟩ := intermediate_value_Icc (le_of_lt hsp') hgc.continuousOn
          (show (0:ℝ) ∈ Set.Icc (deriv g s) (deriv g p) from ⟨le_of_lt hsn, le_of_lt hpp⟩)
        exact hne x (hsub hx) hxv
      · have hsub : Set.Icc p s ⊆ Set.Icc a b := fun x hx => ⟨le_trans hp.1 hx.1, le_trans hx.2 hs.2⟩
        obtain ⟨x, hx, hxv⟩ := intermediate_value_Icc' (le_of_lt hps') hgc.continuousOn
          (show (0:ℝ) ∈ Set.Icc (deriv g s) (deriv g p) from ⟨le_of_lt hsn, le_of_lt hpp⟩)
        exact hne x (hsub hx) hxv
    · have hpp : deriv g p < 0 := by nlinarith
      rcases lt_or_gt_of_ne hsp with hsp' | hps'
      · have hsub : Set.Icc s p ⊆ Set.Icc a b := fun x hx => ⟨le_trans hs.1 hx.1, le_trans hx.2 hp.2⟩
        obtain ⟨x, hx, hxv⟩ := intermediate_value_Icc' (le_of_lt hsp') hgc.continuousOn
          (show (0:ℝ) ∈ Set.Icc (deriv g p) (deriv g s) from ⟨le_of_lt hpp, le_of_lt hspos⟩)
        exact hne x (hsub hx) hxv
      · have hsub : Set.Icc p s ⊆ Set.Icc a b := fun x hx => ⟨le_trans hp.1 hx.1, le_trans hx.2 hs.2⟩
        obtain ⟨x, hx, hxv⟩ := intermediate_value_Icc (le_of_lt hps') hgc.continuousOn
          (show (0:ℝ) ∈ Set.Icc (deriv g p) (deriv g s) from ⟨le_of_lt hpp, le_of_lt hspos⟩)
        exact hne x (hsub hx) hxv

/-- The sign of an increment of `C¹` function is that of the derivative, on an interval where the
derivative keeps the sign of `deriv g p`. -/
lemma zsp_mvt {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {a b p : ℝ}
    (hsig : ∀ s ∈ Set.Icc a b, 0 < deriv g s * deriv g p)
    {s s' : ℝ} (hs : s ∈ Set.Icc a b) (hs' : s' ∈ Set.Icc a b) (hss' : s < s') :
    0 < (g s' - g s) * deriv g p := by
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope g hss' hg.continuous.continuousOn
    ((hg.differentiable (by norm_num)).differentiableOn)
  have hcmem : c ∈ Set.Icc a b := ⟨le_trans hs.1 (le_of_lt hc.1), le_trans (le_of_lt hc.2) hs'.2⟩
  have h1 : 0 < deriv g c * deriv g p := hsig c hcmem
  have h2 : 0 < s' - s := by linarith
  have h3 : deriv g c * (s' - s) = g s' - g s := by
    rw [hcd, div_mul_eq_mul_div, mul_div_cancel_right₀ _ (ne_of_gt h2)]
  calc 0 < (deriv g c * deriv g p) * (s' - s) := mul_pos h1 h2
    _ = deriv g c * (s' - s) * deriv g p := by ring
    _ = (g s' - g s) * deriv g p := by rw [h3]

/-- **The local data at a simple zero.**  At a point `p` with `g p = 0` and `deriv g p ≠ 0` there is
an arbitrarily small interval `[p - e, p + e]` on which `deriv g` has constant sign, keeps at least
half of its modulus at `p`, `g` is strictly monotone (hence changes sign at `p`). -/
lemma zsp_simple_interval (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) {p : ℝ} (hgp : g p = 0)
    (hd : deriv g p ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∃ e : ℝ, 0 < e ∧ e ≤ R ∧
      (∀ s ∈ Set.Icc (p - e) (p + e), |deriv g p| / 2 ≤ |deriv g s|) ∧
      (∀ s ∈ Set.Icc (p - e) (p + e), 0 < deriv g s * deriv g p) ∧
      (∀ s ∈ Set.Icc (p - e) (p + e), ∀ s' ∈ Set.Icc (p - e) (p + e),
        s < s' → 0 < (g s' - g s) * deriv g p) ∧
      g (p - e) * g (p + e) < 0 := by
  have hgc : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hγ : 0 < |deriv g p| := abs_pos.mpr hd
  obtain ⟨η, hηpos, hη⟩ : ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, |s - p| < η →
      |deriv g s - deriv g p| < |deriv g p| / 2 := by
    have h1 : ∀ᶠ s in 𝓝 p, |deriv g s - deriv g p| < |deriv g p| / 2 := by
      have h2 := hgc.continuousAt.eventually
        (Metric.ball_mem_nhds (deriv g p) (ε := |deriv g p| / 2) (by linarith))
      filter_upwards [h2] with s hs
      simpa [Real.dist_eq] using hs
    obtain ⟨η, hη, hη'⟩ := Metric.mem_nhds_iff.mp h1
    exact ⟨η, hη, fun s hs => hη' (by simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hs)⟩
  set e : ℝ := min (η / 2) R with he
  have hepos : 0 < e := lt_min (by linarith) hR
  have heleη : e < η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have heR : e ≤ R := min_le_right _ _
  have hbnd : ∀ s : ℝ, s ∈ Set.Icc (p - e) (p + e) → |s - p| < η := by
    intro s hs
    have h1 : |s - p| ≤ e := by
      rw [abs_le]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    linarith
  have hderiv_lb : ∀ s : ℝ, s ∈ Set.Icc (p - e) (p + e) → |deriv g p| / 2 ≤ |deriv g s| := by
    intro s hs
    have h1 := hη s (hbnd s hs)
    have h2 := abs_sub_abs_le_abs_sub (deriv g p) (deriv g s)
    have h3 : |deriv g p - deriv g s| = |deriv g s - deriv g p| := abs_sub_comm _ _
    linarith [h1, h2]
  have hne : ∀ s : ℝ, s ∈ Set.Icc (p - e) (p + e) → deriv g s ≠ 0 := by
    intro s hs h0
    have h1 := hderiv_lb s hs
    rw [h0, abs_zero] at h1
    linarith
  have hsig : ∀ s ∈ Set.Icc (p - e) (p + e), 0 < deriv g s * deriv g p := fun s hs =>
    zsp_deriv_same_sign hgc ⟨by linarith [hepos], by linarith [hepos]⟩ hs hne
  refine ⟨e, hepos, heR, hderiv_lb, hsig, ?_, ?_⟩
  · intro s hs s' hs' hlt
    exact zsp_mvt hg hsig hs hs' hlt
  · have hmem1 : p - e ∈ Set.Icc (p - e) (p + e) := ⟨le_refl _, by linarith [hepos]⟩
    have hmem2 : p ∈ Set.Icc (p - e) (p + e) := ⟨by linarith [hepos], by linarith [hepos]⟩
    have hmem3 : p + e ∈ Set.Icc (p - e) (p + e) := ⟨by linarith [hepos], le_refl _⟩
    have hA := zsp_mvt hg hsig hmem1 hmem2 (by linarith [hepos])
    have hB := zsp_mvt hg hsig hmem2 hmem3 (by linarith [hepos])
    rw [hgp] at hA hB
    have hA' : 0 < (-g (p - e)) * deriv g p := by simpa using hA
    have hB' : 0 < g (p + e) * deriv g p := by simpa using hB
    have hD : 0 < deriv g p ^ 2 := sq_pos_of_ne_zero hd
    have hmul : 0 < ((-g (p - e)) * deriv g p) * (g (p + e) * deriv g p) := mul_pos hA' hB'
    have heq : ((-g (p - e)) * deriv g p) * (g (p + e) * deriv g p)
        = ((-g (p - e)) * g (p + e)) * deriv g p ^ 2 := by ring
    rw [heq] at hmul
    have hAB : 0 < (-g (p - e)) * g (p + e) := by
      have h := div_pos hmul hD
      rwa [mul_div_cancel_right₀ _ hD.ne'] at h
    linarith

/-- **A sign change plus a nowhere-vanishing derivative gives a unique zero** (existence from the
intermediate value theorem, uniqueness from Rolle's theorem). -/
lemma zsp_unique_zero (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) {a b : ℝ} (hab : a < b)
    (hne : ∀ s ∈ Set.Icc a b, deriv φ s ≠ 0) (hsign : φ a * φ b < 0) :
    ∃! z : ℝ, z ∈ Set.Ioo a b ∧ φ z = 0 := by
  have hcont : ContinuousOn φ (Set.Icc a b) := hφ.continuous.continuousOn
  have hsub : ∀ {u v : ℝ}, a ≤ u → v ≤ b → ContinuousOn φ (Set.Icc u v) :=
    fun {u v} hu hv => hcont.mono (fun x hx => ⟨le_trans hu hx.1, le_trans hx.2 hv⟩)
  have key : ∀ {z : ℝ}, z ∈ Set.Icc a b → φ z = 0 → z ∈ Set.Ioo a b := by
    intro z hz hz0
    rcases mul_neg_iff.mp hsign with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact ⟨lt_of_le_of_ne hz.1 (Ne.symm (fun h => absurd (h ▸ hz0) (ne_of_gt ha))),
        lt_of_le_of_ne hz.2 (fun h => absurd (h ▸ hz0) (ne_of_lt hb))⟩
    · exact ⟨lt_of_le_of_ne hz.1 (Ne.symm (fun h => absurd (h ▸ hz0) (ne_of_lt ha))),
        lt_of_le_of_ne hz.2 (fun h => absurd (h ▸ hz0) (ne_of_gt hb))⟩
  have hex : ∃ z : ℝ, z ∈ Set.Icc a b ∧ φ z = 0 := by
    rcases mul_neg_iff.mp hsign with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have h0x : (0:ℝ) ∈ Set.Icc (φ b) (φ a) := ⟨hb.le, ha.le⟩
      obtain ⟨z, hzmem, hz0⟩ := intermediate_value_Icc' hab.le hcont h0x
      exact ⟨z, hzmem, hz0⟩
    · have h0x : (0:ℝ) ∈ Set.Icc (φ a) (φ b) := ⟨ha.le, hb.le⟩
      obtain ⟨z, hzmem, hz0⟩ := intermediate_value_Icc hab.le hcont h0x
      exact ⟨z, hzmem, hz0⟩
  obtain ⟨z, hzmem, hz0⟩ := hex
  have hzint := key hzmem hz0
  refine ⟨z, ⟨hzint, hz0⟩, ?_⟩
  rintro w ⟨hw, hw0⟩
  rcases lt_trichotomy w z with h | h | h
  · obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero (f := φ) h
      (hsub hw.1.le hzint.2.le) (by rw [hw0, hz0])
    exact absurd hc0 (hne c ⟨le_trans hw.1.le (le_of_lt hc.1), le_trans (le_of_lt hc.2) hzint.2.le⟩)
  · exact h
  · obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero (f := φ) h
      (hsub hzint.1.le hw.2.le) (by rw [hz0, hw0])
    exact absurd hc0 (hne c ⟨le_trans hzint.1.le (le_of_lt hc.1), le_trans (le_of_lt hc.2) hw.2.le⟩)

/-- **Persistence of the number of ray-meeting zeros in one dimension.**  See the module docstring. -/
theorem zeroSet_persist_one_dim
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (h : ℝ → ℝ) (hh : Continuous h)
    (hfin : ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ g t = 0 ∧ 0 < h t}).Finite)
    (hint : ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ g t = 0 ∧ 0 < h t}) ⊆ Set.Ioo 0 1)
    (htrans : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t = 0 → 0 < h t → deriv g t ≠ 0)
    (hanti : ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, g t = 0 → h t ≤ 0 → h t ≤ -m) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (g' : ℝ → ℝ) (h' : ℝ → ℝ), ContDiff ℝ 1 g' → Continuous h' →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, |g' t - g t| ≤ δ) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, |deriv g' t - deriv g t| ≤ δ) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, |h' t - h t| ≤ δ) →
      ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ g' t = 0 ∧ 0 < h' t}).Finite ∧
        ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ g' t = 0 ∧ 0 < h' t}).ncard =
          ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ g t = 0 ∧ 0 < h t}).ncard ∧
        ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ g' t = 0 ∧ 0 < h' t}) ⊆ Set.Ioo 0 1 := by
  classical
  set S : Set ℝ := {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ g t = 0 ∧ 0 < h t} with hSdef
  have hSmem : ∀ t : ℝ, t ∈ S ↔ t ∈ Set.Icc (0 : ℝ) 1 ∧ g t = 0 ∧ 0 < h t := by
    intro t; rw [hSdef]; rfl
  have hSfin : S.Finite := by rw [hSdef]; exact hfin
  have hSint : S ⊆ Set.Ioo (0 : ℝ) 1 := by rw [hSdef]; exact hint
  obtain ⟨m₁, hm₁pos, hm₁⟩ := zsp_exists_pos_le_of_finite hSfin (f := h)
    (fun t ht => ((hSmem t).mp ht).2.2)
  obtain ⟨m₃, hm₃pos, hm₃⟩ := hanti
  obtain ⟨ρ, hρpos, hρ⟩ := zsp_sep hSfin
  have hdata : ∀ p ∈ S, ∃ e : ℝ, 0 < e ∧ e ≤ ρ / 2 ∧
      Set.Icc (p - e) (p + e) ⊆ Set.Ioo (0 : ℝ) 1 ∧
      (∀ s ∈ Set.Icc (p - e) (p + e), |deriv g p| / 2 ≤ |deriv g s|) ∧
      (∀ s ∈ Set.Icc (p - e) (p + e), 0 < deriv g s * deriv g p) ∧
      (∀ s ∈ Set.Icc (p - e) (p + e), ∀ s' ∈ Set.Icc (p - e) (p + e),
        s < s' → 0 < (g s' - g s) * deriv g p) ∧
      g (p - e) * g (p + e) < 0 ∧
      (∀ s ∈ Set.Icc (p - e) (p + e), 3 * m₁ / 4 ≤ h s) := by
    intro p hp
    obtain ⟨hpinIcc, hg0, hh0⟩ := (hSmem p).mp hp
    have hpin : p ∈ Set.Ioo (0 : ℝ) 1 := hSint hp
    have hpm₁ : m₁ ≤ h p := hm₁ p hp
    have hd : deriv g p ≠ 0 := htrans p hpinIcc hg0 hh0
    obtain ⟨rh, hrhpos, hrh⟩ : ∃ rh : ℝ, 0 < rh ∧ ∀ s : ℝ, |s - p| ≤ rh → |h s - h p| ≤ m₁ / 4 := by
      have h1 : ∀ᶠ s in 𝓝 p, |h s - h p| < m₁ / 4 := by
        have h2 := hh.continuousAt.eventually
          (Metric.ball_mem_nhds (h p) (ε := m₁ / 4) (by linarith))
        filter_upwards [h2] with s hs
        simpa [Real.dist_eq] using hs
      obtain ⟨rh₀, hrh₀, hrh₀'⟩ := Metric.mem_nhds_iff.mp h1
      refine ⟨rh₀ / 2, by linarith, fun s hs => ?_⟩
      refine le_of_lt (hrh₀' ?_)
      have h3 : |s - p| < rh₀ := by linarith
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using h3
    have hRpos : 0 < min (ρ / 2) (min (min (p / 2) ((1 - p) / 2)) rh) :=
      lt_min (by linarith) (lt_min (lt_min (by linarith [hpin.1]) (by linarith [hpin.2])) hrhpos)
    obtain ⟨e, hepos, heR, hderiv, hsign, hmono, hchg⟩ :=
      zsp_simple_interval (g := g) (hg := hg) (p := p) hg0 hd
        (R := min (ρ / 2) (min (min (p / 2) ((1 - p) / 2)) rh)) hRpos
    have heρ : e ≤ ρ / 2 := le_trans heR (min_le_left _ _)
    have hep1 : e ≤ p / 2 :=
      le_trans heR ((min_le_right (ρ / 2) (min (min (p / 2) ((1 - p) / 2)) rh)).trans
        ((min_le_left (min (p / 2) ((1 - p) / 2)) rh).trans (min_le_left (p / 2) ((1 - p) / 2))))
    have hep2 : e ≤ (1 - p) / 2 :=
      le_trans heR ((min_le_right (ρ / 2) (min (min (p / 2) ((1 - p) / 2)) rh)).trans
        ((min_le_left (min (p / 2) ((1 - p) / 2)) rh).trans (min_le_right (p / 2) ((1 - p) / 2))))
    have herh : e ≤ rh := le_trans heR ((min_le_right (ρ / 2) (min (min (p / 2) ((1 - p) / 2)) rh)).trans
      (min_le_right (min (p / 2) ((1 - p) / 2)) rh))
    refine ⟨e, hepos, heρ, ?_, hderiv, hsign, hmono, hchg, ?_⟩
    · intro s hs
      have h1 : |s - p| ≤ e := by
        rw [abs_le]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      obtain ⟨h2, h3⟩ := abs_le.mp h1
      exact ⟨by linarith, by linarith⟩
    · intro s hs
      have h1 : |s - p| ≤ rh := by
        have h2 : |s - p| ≤ e := by
          rw [abs_le]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
        linarith
      have h2 := (abs_le.mp (hrh s h1)).1
      linarith
  choose e he using hdata
  let ef : ℝ → ℝ := fun p => if hp : p ∈ S then e p hp else 1
  have hef : ∀ (p : ℝ) (hp : p ∈ S), ef p = e p hp := fun p hp => dif_pos hp
  have hepos : ∀ p ∈ S, 0 < ef p := fun p hp => by rw [hef p hp]; exact (he p hp).1
  have heρ : ∀ p ∈ S, ef p ≤ ρ / 2 := fun p hp => by rw [hef p hp]; exact (he p hp).2.1
  have hsubI : ∀ p ∈ S, Set.Icc (p - ef p) (p + ef p) ⊆ Set.Ioo (0 : ℝ) 1 := fun p hp => by
    rw [hef p hp]; exact (he p hp).2.2.1
  have hderivlb : ∀ p ∈ S, ∀ s ∈ Set.Icc (p - ef p) (p + ef p), |deriv g p| / 2 ≤ |deriv g s| :=
    fun p hp => by rw [hef p hp]; exact (he p hp).2.2.2.1
  have hsig : ∀ p ∈ S, ∀ s ∈ Set.Icc (p - ef p) (p + ef p), 0 < deriv g s * deriv g p :=
    fun p hp => by rw [hef p hp]; exact (he p hp).2.2.2.2.1
  have hmono : ∀ p ∈ S, ∀ s ∈ Set.Icc (p - ef p) (p + ef p),
      ∀ s' ∈ Set.Icc (p - ef p) (p + ef p), s < s' → 0 < (g s' - g s) * deriv g p :=
    fun p hp => by rw [hef p hp]; exact (he p hp).2.2.2.2.2.1
  have hchg : ∀ p ∈ S, g (p - ef p) * g (p + ef p) < 0 :=
    fun p hp => by rw [hef p hp]; exact (he p hp).2.2.2.2.2.2.1
  have hhlb : ∀ p ∈ S, ∀ s ∈ Set.Icc (p - ef p) (p + ef p), 3 * m₁ / 4 ≤ h s :=
    fun p hp => by rw [hef p hp]; exact (he p hp).2.2.2.2.2.2.2
  set V : Set ℝ := ⋃ p ∈ S, Set.Icc (p - ef p) (p + ef p) with hVdef
  have hVmem : ∀ t : ℝ, t ∈ V ↔ ∃ p ∈ S, t ∈ Set.Icc (p - ef p) (p + ef p) := by
    intro t; rw [hVdef]; simp only [Set.mem_iUnion, exists_prop]
  set Vo : Set ℝ := ⋃ p ∈ S, Set.Ioo (p - ef p) (p + ef p) with hVodef
  have hVomem : ∀ t : ℝ, t ∈ Vo ↔ ∃ p ∈ S, t ∈ Set.Ioo (p - ef p) (p + ef p) := by
    intro t; rw [hVodef]; simp only [Set.mem_iUnion, exists_prop]
  have hVoopen : IsOpen Vo := by
    rw [hVodef]
    exact isOpen_iUnion fun p => isOpen_iUnion fun hp => isOpen_Ioo
  set K : Set ℝ := {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ -m₃ / 2 ≤ h t} with hKdef
  have hKclosed : IsClosed K := by
    rw [hKdef]
    exact isClosed_Icc.inter (isClosed_le continuous_const hh)
  have hKcompact : IsCompact K :=
    IsCompact.of_isClosed_subset isCompact_Icc hKclosed (fun t ht => ht.1)
  obtain ⟨m₄, hm₄pos, hm₄⟩ : ∃ m₄ : ℝ, 0 < m₄ ∧ ∀ t ∈ K \ Vo, m₄ ≤ |g t| := by
    have hcomp : IsCompact (K \ Vo) :=
      IsCompact.of_isClosed_subset hKcompact (hKclosed.sdiff hVoopen) (fun t ht => ht.1)
    rcases (K \ Vo).eq_empty_or_nonempty with hem | hne
    · exact ⟨1, one_pos, by simp [hem]⟩
    · have hpos : ∀ t ∈ K \ Vo, 0 < |g t| := by
        rintro t ⟨htK, htVo⟩
        rw [abs_pos]
        intro hg0
        have hht : 0 < h t := by
          by_contra hcon
          push Not at hcon
          have h1 := hm₃ t htK.1 hg0 hcon
          linarith [htK.2, h1]
        have htS : t ∈ S := (hSmem t).mpr ⟨htK.1, hg0, hht⟩
        have hmem : t ∈ Vo := by
          rw [hVomem]
          exact ⟨t, htS, ⟨by linarith [hepos t htS], by linarith [hepos t htS]⟩⟩
        exact htVo hmem
      obtain ⟨t₀, ht₀, hmin⟩ := hcomp.exists_isMinOn hne (hg.continuous.abs).continuousOn
      exact ⟨|g t₀|, hpos t₀ ht₀, fun t ht => hmin ht⟩
  obtain ⟨m₅, hm₅pos, hm₅⟩ := zsp_exists_pos_le_of_finite hSfin (f := fun p => |deriv g p| / 4)
    (fun p hp => by
      have hd : deriv g p ≠ 0 :=
        htrans p ((hSmem p).mp hp).1 ((hSmem p).mp hp).2.1 ((hSmem p).mp hp).2.2
      exact div_pos (abs_pos.mpr hd) (by norm_num))
  obtain ⟨m₆, hm₆pos, hm₆⟩ := zsp_exists_pos_le_of_finite hSfin (f := fun p => |g (p - ef p)| / 2)
    (fun p hp => by
      have h2 := hchg p hp
      have h3 : g (p - ef p) ≠ 0 := by
        intro h0; rw [h0, zero_mul] at h2; exact absurd h2 (lt_irrefl 0)
      exact div_pos (abs_pos.mpr h3) (by norm_num))
  obtain ⟨m₇, hm₇pos, hm₇⟩ := zsp_exists_pos_le_of_finite hSfin (f := fun p => |g (p + ef p)| / 2)
    (fun p hp => by
      have h2 := hchg p hp
      have h3 : g (p + ef p) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at h2; exact absurd h2 (lt_irrefl 0)
      exact div_pos (abs_pos.mpr h3) (by norm_num))
  set δ : ℝ := min (min (m₁ / 4) (min (m₃ / 4) (m₄ / 2))) (min m₅ (min m₆ m₇)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
      (lt_min hm₅pos (lt_min hm₆pos hm₇pos))
  have hδm₁ : δ ≤ m₁ / 4 := by rw [hδdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hδm₃ : δ ≤ m₃ / 4 := by
    rw [hδdef]; exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδm₄ : δ ≤ m₄ / 2 := by
    rw [hδdef]; exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδm₅ : δ ≤ m₅ := by rw [hδdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hδm₆ : δ ≤ m₆ := by
    rw [hδdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδm₇ : δ ≤ m₇ := by
    rw [hδdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ, hδpos, ?_⟩
  intro g' h' hg' hh' hcl1 hcl2 hcl3
  set S' : Set ℝ := {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ g' t = 0 ∧ 0 < h' t} with hS'def
  have hS'mem : ∀ t : ℝ, t ∈ S' ↔ t ∈ Set.Icc (0 : ℝ) 1 ∧ g' t = 0 ∧ 0 < h' t := by
    intro t; rw [hS'def]; rfl
  have hderiv'_ne : ∀ p ∈ S, ∀ s ∈ Set.Icc (p - ef p) (p + ef p), deriv g' s ≠ 0 := by
    intro p hp s hs
    have h1 : |deriv g p| / 2 ≤ |deriv g s| := hderivlb p hp s hs
    have h2 : |deriv g' s - deriv g s| ≤ δ := hcl2 s (Set.Ioo_subset_Icc_self (hsubI p hp hs))
    have h3 : δ ≤ |deriv g p| / 4 := le_trans hδm₅ (hm₅ p hp)
    have h4 : 0 < |deriv g p| :=
      abs_pos.mpr (htrans p ((hSmem p).mp hp).1 ((hSmem p).mp hp).2.1 ((hSmem p).mp hp).2.2)
    intro h0
    rw [h0, zero_sub, abs_neg] at h2
    linarith
  have hsign' : ∀ p ∈ S, g' (p - ef p) * g' (p + ef p) < 0 := by
    intro p hp
    have hmem1 : p - ef p ∈ Set.Icc (p - ef p) (p + ef p) := ⟨le_refl _, by linarith [hepos p hp]⟩
    have hmem2 : p + ef p ∈ Set.Icc (p - ef p) (p + ef p) := ⟨by linarith [hepos p hp], le_refl _⟩
    have ha : |g' (p - ef p) - g (p - ef p)| ≤ δ :=
      hcl1 _ (Set.Ioo_subset_Icc_self (hsubI p hp hmem1))
    have hb : |g' (p + ef p) - g (p + ef p)| ≤ δ :=
      hcl1 _ (Set.Ioo_subset_Icc_self (hsubI p hp hmem2))
    have h0 : g (p - ef p) * g (p + ef p) < 0 := hchg p hp
    have h3a : g (p - ef p) ≠ 0 := by
      intro hmm; rw [hmm, zero_mul] at h0; exact absurd h0 (lt_irrefl 0)
    have h3b : g (p + ef p) ≠ 0 := by
      intro hmm; rw [hmm, mul_zero] at h0; exact absurd h0 (lt_irrefl 0)
    have s1 : 0 < g (p - ef p) * g' (p - ef p) :=
      zsp_mul_pos_of_abs_sub_le h3a (le_trans ha (le_trans hδm₆ (hm₆ p hp)))
    have s2 : 0 < g (p + ef p) * g' (p + ef p) :=
      zsp_mul_pos_of_abs_sub_le h3b (le_trans hb (le_trans hδm₇ (hm₇ p hp)))
    have hnum : 0 < (g (p - ef p) * g (p + ef p)) * (g' (p - ef p) * g' (p + ef p)) := by
      have h5 : 0 < (g (p - ef p) * g' (p - ef p)) * (g (p + ef p) * g' (p + ef p)) :=
        mul_pos s1 s2
      have h6 : (g (p - ef p) * g' (p - ef p)) * (g (p + ef p) * g' (p + ef p))
          = (g (p - ef p) * g (p + ef p)) * (g' (p - ef p) * g' (p + ef p)) := by ring
      rwa [h6] at h5
    rcases mul_pos_iff.mp hnum with ⟨hbad, -⟩ | ⟨-, hgood⟩
    · exact absurd hbad (not_lt.mpr h0.le)
    · exact hgood
  have hper : ∀ p ∈ S, ∃! w : ℝ, w ∈ Set.Ioo (p - ef p) (p + ef p) ∧ g' w = 0 := fun p hp =>
    zsp_unique_zero g' hg' (by linarith [hepos p hp]) (hderiv'_ne p hp) (hsign' p hp)
  choose z hz using hper
  let zf : ℝ → ℝ := fun p => if hp : p ∈ S then z p hp else 0
  have hzf : ∀ (p : ℝ) (hp : p ∈ S), zf p = z p hp := fun p hp => dif_pos hp
  have hzmem : ∀ p ∈ S, zf p ∈ Set.Ioo (p - ef p) (p + ef p) ∧ g' (zf p) = 0 := fun p hp => by
    rw [hzf p hp]; exact (hz p hp).1
  have hzuniq : ∀ p ∈ S, ∀ y : ℝ, y ∈ Set.Ioo (p - ef p) (p + ef p) → g' y = 0 → y = zf p :=
    fun p hp y hy hy0 => by rw [hzf p hp]; exact (hz p hp).2 y ⟨hy, hy0⟩
  have hzS' : ∀ p ∈ S, zf p ∈ S' := by
    intro p hp
    obtain ⟨hzint, hz0⟩ := hzmem p hp
    refine (hS'mem (zf p)).mpr ⟨Set.Ioo_subset_Icc_self (hsubI p hp (Set.Ioo_subset_Icc_self hzint)),
      hz0, ?_⟩
    have h1 : 3 * m₁ / 4 ≤ h (zf p) := hhlb p hp (zf p) (Set.Ioo_subset_Icc_self hzint)
    have h2 : |h' (zf p) - h (zf p)| ≤ δ :=
      hcl3 _ (Set.Ioo_subset_Icc_self (hsubI p hp (Set.Ioo_subset_Icc_self hzint)))
    have h3 : δ ≤ m₁ / 4 := hδm₁
    have h4 := (abs_le.mp h2).1
    linarith
  have hz_inj : Set.InjOn zf S := by
    intro p hp q hq hpq
    by_contra hne
    have hpint := (hzmem p hp).1
    have hqint := (hzmem q hq).1
    have h1 : |p - zf p| ≤ ef p := by
      rw [abs_le]; exact ⟨by linarith [hpint.2], by linarith [hpint.1]⟩
    have h2 : |q - zf q| ≤ ef q := by
      rw [abs_le]; exact ⟨by linarith [hqint.2], by linarith [hqint.1]⟩
    have h3 : |zf q - q| ≤ ef q := by rw [abs_sub_comm]; exact h2
    have h4 : |p - q| ≤ ef p + ef q := by
      have h5 : p - q = (p - zf p) + (zf q - q) := by rw [hpq]; ring
      rw [h5]
      exact le_trans (abs_add_le _ _) (add_le_add h1 h3)
    have h6 : ef p + ef q ≤ ρ := by
      have h7 := heρ p hp
      have h8 := heρ q hq
      linarith
    have h9 : 2 * ρ ≤ |p - q| := hρ p hp q hq hne
    linarith
  have hS'sub : S' ⊆ zf '' S := by
    intro t ht
    obtain ⟨htIcc, htg', hth'⟩ := (hS'mem t).mp ht
    have htV : t ∈ V := by
      by_contra htV
      by_cases hcase : h t < -m₃ / 2
      · have h2 : h' t - h t ≤ δ := (abs_le.mp (hcl3 t htIcc)).2
        have h3 : δ ≤ m₃ / 4 := hδm₃
        linarith
      · push Not at hcase
        have htK : t ∈ K := ⟨htIcc, hcase⟩
        have htVo : t ∉ Vo := fun hcon => htV (by
          rw [hVmem]
          obtain ⟨p, hp, htp⟩ := (hVomem t).mp hcon
          exact ⟨p, hp, Set.Ioo_subset_Icc_self htp⟩)
        have h4 : m₄ ≤ |g t| := hm₄ t ⟨htK, htVo⟩
        have h2 : |g t| ≤ δ := by
          have h5 := hcl1 t htIcc
          rw [htg', zero_sub, abs_neg] at h5
          exact h5
        have h5 : δ ≤ m₄ / 2 := hδm₄
        linarith
    obtain ⟨p, hp, htp⟩ := (hVmem t).mp htV
    have hne1 : t ≠ p - ef p := by
      intro hcon
      have h6 := hsign' p hp
      rw [← hcon, htg', zero_mul] at h6
      exact absurd h6 (lt_irrefl 0)
    have hne2 : t ≠ p + ef p := by
      intro hcon
      have h6 := hsign' p hp
      rw [← hcon, htg', mul_zero] at h6
      exact absurd h6 (lt_irrefl 0)
    have htint : t ∈ Set.Ioo (p - ef p) (p + ef p) :=
      ⟨lt_of_le_of_ne htp.1 (Ne.symm hne1), lt_of_le_of_ne htp.2 hne2⟩
    exact ⟨p, hp, (hzuniq p hp t htint htg').symm⟩
  have hS'eq : S' = zf '' S := Set.Subset.antisymm hS'sub (by rintro t ⟨p, hp, rfl⟩; exact hzS' p hp)
  refine ⟨?_, ?_, ?_⟩
  · rw [hS'eq]; exact hSfin.image zf
  · rw [hS'eq, Set.InjOn.ncard_image hz_inj]
  · intro t ht
    rw [hS'eq] at ht
    obtain ⟨p, hp, rfl⟩ := ht
    exact hsubI p hp (Set.Ioo_subset_Icc_self (hzmem p hp).1)

end Work.Surf
