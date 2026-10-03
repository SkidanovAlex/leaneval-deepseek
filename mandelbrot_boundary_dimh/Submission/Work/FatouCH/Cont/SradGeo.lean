import Mathlib
import Submission.Work.FatouCH.Cont.Defs

/-!
# The geometry of Shishikura's region `Qreg b₁ b₂` and the safe radius `srad b₁ b₂`

`MandelDim.Qreg b₁ b₂` (`Submission/Work/Interfaces/Fatou.lean`) is the complement of at most two
closed right cones: for a vertex `a ∈ b₁` the excluded cone is `{z | Re (z - a) + |Im (z - a)| ≤ 0}`,
for `b ∈ b₂` it is `{z | Re (z - b) ≥ |Im (z - b)|}` (`none` = the corresponding vertex at
infinity).  The admissibility hypothesis `MandelDim.QAdm b₁ b₂` (`a.re + 4 < b.re`) keeps the two
cones strictly separated.

`Work.FatouCH.spineRe b₁ b₂` is an explicit real number whose vertical line lies well inside the
region, and `Work.FatouCH.srad b₁ b₂ z` is an explicit lower bound for the distance of `z` to the
complement of the region.

This file proves `Work.FatouCH.Cont.SradGeo`, the bundle of geometric facts consumed by the
Koebe-chain proof of `MandelDim.FatouContinuity` (see `Work.FatouCH.Cont.WalkExists`):

* `Qreg` is open and preconnected;
* the vertical spine `{spineRe + i t}` lies in `Qreg` with a safe radius `≥ 1`;
* `srad` is a safety radius everywhere, positive on the region, and drops at most down to
  `min 1 (srad z)` when moving horizontally from `z` towards the spine — more precisely the whole
  horizontal segment from `z` to the spine stays in `Qreg` with `srad ≥ min 1 (srad z)`;
* any two points of `Qreg` are enclosed in an open preconnected set with compact closure inside
  `Qreg` (obtained as a union of three convex tubes around the polyline through the spine).

The proof is a case analysis on the two `Option ℂ` vertices; the four cases
`(none,none), (none,some), (some,none), (some,some)` are handled after unfolding the
`match`-definitions with the characterisation lemmas below.
-/

open Set Metric Complex
open scoped Topology

namespace Work.FatouCH.Cont

/-! ## Unfolding the `match`-definitions in each of the four cases -/

private lemma mem_Qreg_none_none (z : ℂ) : z ∈ MandelDim.Qreg (none : Option ℂ) none := by
  simp [MandelDim.Qreg, Option.mem_def]

private lemma mem_Qreg_some_none (a z : ℂ) :
    (z ∈ MandelDim.Qreg (some a) none) ↔ -|(z - a).im| < (z - a).re := by
  simp [MandelDim.Qreg, Option.mem_def]

private lemma mem_Qreg_none_some (b z : ℂ) :
    (z ∈ MandelDim.Qreg none (some b)) ↔ (z - b).re < |(z - b).im| := by
  simp [MandelDim.Qreg, Option.mem_def]

private lemma mem_Qreg_some_some (a b z : ℂ) :
    (z ∈ MandelDim.Qreg (some a) (some b)) ↔
      (-|(z - a).im| < (z - a).re ∧ (z - b).re < |(z - b).im|) := by
  simp [MandelDim.Qreg, Option.mem_def]

private lemma srad_none_none (z : ℂ) :
    Work.FatouCH.srad (none : Option ℂ) none z = 1 + ‖z‖ := by
  simp [Work.FatouCH.srad]

private lemma srad_some_none (a z : ℂ) :
    Work.FatouCH.srad (some a) none z = (1 / 2) * ((z - a).re + |(z - a).im|) := by
  simp [Work.FatouCH.srad]

private lemma srad_none_some (b z : ℂ) :
    Work.FatouCH.srad none (some b) z = (1 / 2) * (|(z - b).im| - (z - b).re) := by
  simp [Work.FatouCH.srad]

private lemma srad_some_some (a b z : ℂ) :
    Work.FatouCH.srad (some a) (some b) z =
      min ((1 / 2) * ((z - a).re + |(z - a).im|))
        ((1 / 2) * (|(z - b).im| - (z - b).re)) := by
  simp [Work.FatouCH.srad]

private lemma spineRe_none_none : Work.FatouCH.spineRe (none : Option ℂ) none = 0 := by
  simp [Work.FatouCH.spineRe]

private lemma spineRe_some_none (a : ℂ) : Work.FatouCH.spineRe (some a) none = a.re + 2 := by
  simp [Work.FatouCH.spineRe]

private lemma spineRe_none_some (b : ℂ) : Work.FatouCH.spineRe none (some b) = b.re - 2 := by
  simp [Work.FatouCH.spineRe]

private lemma spineRe_some_some (a b : ℂ) :
    Work.FatouCH.spineRe (some a) (some b) = (a.re + b.re) / 2 := by
  simp [Work.FatouCH.spineRe]

private lemma qAdm_some_some {a b : ℂ} (h : MandelDim.QAdm (some a) (some b)) :
    a.re + 4 < b.re := by
  simpa only [MandelDim.QAdm, Option.mem_def, Option.some.injEq, forall_eq', forall_eq] using h

/-! ## positivity of `srad` -/

/-- A positive safe radius forces membership in the region. -/
private theorem sradPosImp {b₁ b₂ : Option ℂ} {z : ℂ}
    (h : 0 < Work.FatouCH.srad b₁ b₂ z) : z ∈ MandelDim.Qreg b₁ b₂ := by
  rcases b₁ with _ | a
  · rcases b₂ with _ | b
    · exact mem_Qreg_none_none z
    · rw [srad_none_some] at h
      rw [mem_Qreg_none_some]
      linarith
  · rcases b₂ with _ | b
    · rw [srad_some_none] at h
      rw [mem_Qreg_some_none]
      linarith
    · rw [srad_some_some] at h
      rw [mem_Qreg_some_some]
      obtain ⟨h1, h2⟩ := lt_min_iff.mp h
      constructor <;> linarith

/-- The safe radius is positive on the region. -/
private theorem sradPos_of_mem {b₁ b₂ : Option ℂ} {z : ℂ}
    (hz : z ∈ MandelDim.Qreg b₁ b₂) : 0 < Work.FatouCH.srad b₁ b₂ z := by
  rcases b₁ with _ | a
  · rcases b₂ with _ | b
    · rw [srad_none_none]
      linarith [norm_nonneg z]
    · rw [mem_Qreg_none_some] at hz
      rw [srad_none_some]
      linarith
  · rcases b₂ with _ | b
    · rw [mem_Qreg_some_none] at hz
      rw [srad_some_none]
      linarith
    · rw [mem_Qreg_some_some] at hz
      rw [srad_some_some]
      obtain ⟨h1, h2⟩ := hz
      exact lt_min (by linarith) (by linarith)

/-! ## continuity of `srad` and openness of `Qreg` -/

private theorem continuous_srad (b₁ b₂ : Option ℂ) :
    Continuous (Work.FatouCH.srad b₁ b₂) := by
  rcases b₁ with _ | a
  · rcases b₂ with _ | b
    · rw [show Work.FatouCH.srad (none : Option ℂ) none = fun z : ℂ => 1 + ‖z‖ from
        funext srad_none_none]
      continuity
    · rw [show Work.FatouCH.srad (none : Option ℂ) (some b) =
          fun z : ℂ => (1 / 2) * (|(z - b).im| - (z - b).re) from funext (srad_none_some b)]
      continuity
  · rcases b₂ with _ | b
    · rw [show Work.FatouCH.srad (some a) (none : Option ℂ) =
          fun z : ℂ => (1 / 2) * ((z - a).re + |(z - a).im|) from funext (srad_some_none a)]
      continuity
    · rw [show Work.FatouCH.srad (some a) (some b) = fun z : ℂ =>
          min ((1 / 2) * ((z - a).re + |(z - a).im|))
            ((1 / 2) * (|(z - b).im| - (z - b).re)) from funext (srad_some_some a b)]
      continuity

private theorem isOpen_Qreg (b₁ b₂ : Option ℂ) : IsOpen (MandelDim.Qreg b₁ b₂) := by
  have h : MandelDim.Qreg b₁ b₂ = {z : ℂ | 0 < Work.FatouCH.srad b₁ b₂ z} := by
    ext z
    exact ⟨sradPos_of_mem, sradPosImp⟩
  rw [h]
  exact isOpen_lt continuous_const (continuous_srad b₁ b₂)

/-! ## the safety ball -/

/-- The two model functions `z ↦ ½(Re(z-a) + |Im(z-a)|)` and `z ↦ ½(|Im(z-b)| - Re(z-b))` are
`1`-Lipschitz in the only direction ever needed. -/
private lemma s1_dist_le (a z w : ℂ) :
    (1 / 2) * ((z - a).re + |(z - a).im|) - (1 / 2) * ((w - a).re + |(w - a).im|) ≤
      ‖z - w‖ := by
  have h1 : (z - a).re - (w - a).re ≤ ‖z - w‖ := by
    have h := Complex.abs_re_le_norm (z - w)
    rw [Complex.sub_re] at h
    simp only [Complex.sub_re]
    linarith [le_abs_self (z.re - w.re), h]
  have h2 : |(z - a).im| - |(w - a).im| ≤ ‖z - w‖ := by
    have him : (z - a).im - (w - a).im = z.im - w.im := by
      rw [Complex.sub_im, Complex.sub_im]; ring
    have h := Complex.abs_im_le_norm (z - w)
    rw [Complex.sub_im] at h
    have h4 : |(z - a).im - (w - a).im| ≤ ‖z - w‖ := by rw [him]; exact h
    have h5 := abs_abs_sub_abs_le_abs_sub (z - a).im (w - a).im
    linarith [le_abs_self (|(z - a).im| - |(w - a).im|), h5, h4]
  linarith

private lemma s2_dist_le (b z w : ℂ) :
    (1 / 2) * (|(z - b).im| - (z - b).re) - (1 / 2) * (|(w - b).im| - (w - b).re) ≤
      ‖z - w‖ := by
  have h1 : (w - b).re - (z - b).re ≤ ‖z - w‖ := by
    have h := Complex.abs_re_le_norm (z - w)
    rw [Complex.sub_re] at h
    simp only [Complex.sub_re]
    linarith [neg_le_abs (z.re - w.re), h]
  have h2 : |(z - b).im| - |(w - b).im| ≤ ‖z - w‖ := by
    have him : (z - b).im - (w - b).im = z.im - w.im := by
      rw [Complex.sub_im, Complex.sub_im]; ring
    have h := Complex.abs_im_le_norm (z - w)
    rw [Complex.sub_im] at h
    have h4 : |(z - b).im - (w - b).im| ≤ ‖z - w‖ := by rw [him]; exact h
    have h5 := abs_abs_sub_abs_le_abs_sub (z - b).im (w - b).im
    linarith [le_abs_self (|(z - b).im| - |(w - b).im|), h5, h4]
  linarith

/-- `srad` is a safety radius: the ball of radius `srad z` around `z` stays in the region. -/
private theorem ball_srad_subset (b₁ b₂ : Option ℂ) :
    ∀ z : ℂ, Metric.ball z (Work.FatouCH.srad b₁ b₂ z) ⊆ MandelDim.Qreg b₁ b₂ := by
  intro z w hw
  rw [Metric.mem_ball, Complex.dist_eq, norm_sub_rev] at hw
  rcases b₁ with _ | a
  · rcases b₂ with _ | b
    · exact mem_Qreg_none_none w
    · rw [srad_none_some] at hw
      rw [mem_Qreg_none_some]
      have h := s2_dist_le b z w
      linarith
  · rcases b₂ with _ | b
    · rw [srad_some_none] at hw
      rw [mem_Qreg_some_none]
      have h := s1_dist_le a z w
      linarith
    · rw [srad_some_some] at hw
      rw [mem_Qreg_some_some]
      have hw' : ‖z - w‖ < (1 / 2) * ((z - a).re + |(z - a).im|) ∧
          ‖z - w‖ < (1 / 2) * (|(z - b).im| - (z - b).re) := by
        rw [lt_min_iff] at hw; exact hw
      obtain ⟨hwa, hwb⟩ := hw'
      constructor
      · have h := s1_dist_le a z w; linarith
      · have h := s2_dist_le b z w; linarith

/-! ## the spine -/

/-- The spine lies to the right of every left vertex. -/
private theorem spineLtLeft {b₁ b₂ : Option ℂ} (hAdm : MandelDim.QAdm b₁ b₂) :
    ∀ a ∈ b₁, a.re < Work.FatouCH.spineRe b₁ b₂ := by
  rcases b₁ with _ | a
  · intro x hx
    exact absurd hx (Option.not_mem_none x)
  · rcases b₂ with _ | b
    · intro x hx
      rw [Option.mem_def, Option.some.injEq] at hx
      subst hx
      rw [spineRe_some_none]
      linarith
    · intro x hx
      rw [Option.mem_def, Option.some.injEq] at hx
      subst hx
      have hAdm' := qAdm_some_some hAdm
      rw [spineRe_some_some]
      linarith

/-- The spine lies to the left of every right vertex. -/
private theorem spineLtRight {b₁ b₂ : Option ℂ} (hAdm : MandelDim.QAdm b₁ b₂) :
    ∀ b ∈ b₂, Work.FatouCH.spineRe b₁ b₂ < b.re := by
  rcases b₂ with _ | b
  · intro x hx
    exact absurd hx (Option.not_mem_none x)
  · rcases b₁ with _ | a
    · intro x hx
      rw [Option.mem_def, Option.some.injEq] at hx
      subst hx
      rw [spineRe_none_some]
      linarith
    · intro x hx
      rw [Option.mem_def, Option.some.injEq] at hx
      subst hx
      have hAdm' := qAdm_some_some hAdm
      rw [spineRe_some_some]
      linarith

/-- The whole spine line lies in the region. -/
private theorem spineMemQreg {b₁ b₂ : Option ℂ} (hAdm : MandelDim.QAdm b₁ b₂) :
    ∀ t : ℝ, Work.FatouCH.spineRe b₁ b₂ + t * Complex.I ∈ MandelDim.Qreg b₁ b₂ := by
  rcases b₁ with _ | a
  · rcases b₂ with _ | b
    · intro t; exact mem_Qreg_none_none _
    · intro t
      rw [mem_Qreg_none_some, spineRe_none_some]
      simp
      linarith [abs_nonneg (t - b.im)]
  · rcases b₂ with _ | b
    · intro t
      rw [mem_Qreg_some_none, spineRe_some_none]
      simp
      linarith [abs_nonneg (t - a.im)]
    · intro t
      have hAdm' := qAdm_some_some hAdm
      rw [mem_Qreg_some_some, spineRe_some_some]
      constructor <;> simp <;> linarith [abs_nonneg (t - a.im), abs_nonneg (t - b.im)]

/-- The safe radius is at least `1` on the spine. -/
private theorem spineSrad {b₁ b₂ : Option ℂ} (hAdm : MandelDim.QAdm b₁ b₂) :
    ∀ t : ℝ, (1 : ℝ) ≤
      Work.FatouCH.srad b₁ b₂ (Work.FatouCH.spineRe b₁ b₂ + t * Complex.I) := by
  rcases b₁ with _ | a
  · rcases b₂ with _ | b
    · intro t
      rw [srad_none_none, spineRe_none_none]
      simp only [Complex.ofReal_zero, zero_add]
      linarith [norm_nonneg ((t : ℂ) * Complex.I)]
    · intro t
      rw [srad_none_some, spineRe_none_some]
      simp
      linarith [abs_nonneg (t - b.im)]
  · rcases b₂ with _ | b
    · intro t
      rw [srad_some_none, spineRe_some_none]
      simp
      linarith [abs_nonneg (t - a.im)]
    · intro t
      have hAdm' := qAdm_some_some hAdm
      rw [srad_some_some, spineRe_some_some, min_def]
      split <;> simp <;> linarith [abs_nonneg (t - a.im), abs_nonneg (t - b.im)]

/-! ## horizontal parameter bounds -/

private lemma seg_re_le_right {z m t q : ℝ} (hp : q = z + t * (m - z)) (h0 : 0 ≤ t) (hm : z ≤ m) :
    z ≤ q := by
  have : 0 ≤ t * (m - z) := mul_nonneg h0 (by linarith)
  rw [hp]; linarith

private lemma seg_re_le_left {z m t q : ℝ} (hp : q = z + t * (m - z)) (h1 : t ≤ 1) (hm : z ≤ m) :
    q ≤ m := by
  have h : t * (m - z) ≤ m - z := by
    simpa using mul_le_mul_of_nonneg_right h1 (sub_nonneg.mpr hm)
  rw [hp]; linarith

private lemma seg_re_ge_left {z m t q : ℝ} (hp : q = z + t * (m - z)) (h1 : t ≤ 1) (hm : m ≤ z) :
    m ≤ q := by
  have h : t * (z - m) ≤ z - m := by
    simpa using mul_le_mul_of_nonneg_right h1 (sub_nonneg.mpr hm)
  have h' : z + t * (m - z) = z - t * (z - m) := by ring
  rw [hp, h']; linarith

private lemma seg_re_ge_right {z m t q : ℝ} (hp : q = z + t * (m - z)) (h0 : 0 ≤ t) (hm : m ≤ z) :
    q ≤ z := by
  have h : 0 ≤ t * (z - m) := mul_nonneg h0 (by linarith)
  have h' : z + t * (m - z) = z - t * (z - m) := by ring
  rw [hp, h']; linarith

/-! ## monotonicity of the two model functions under a horizontal move -/

private lemma s1_mono {a z w : ℂ} (him : w.im = z.im) (hre : z.re ≤ w.re) :
    (1 / 2) * ((z - a).re + |(z - a).im|) ≤ (1 / 2) * ((w - a).re + |(w - a).im|) := by
  rw [Complex.sub_re, Complex.sub_re, Complex.sub_im, Complex.sub_im, him]
  linarith

private lemma s2_anti {b z w : ℂ} (him : w.im = z.im) (hre : w.re ≤ z.re) :
    (1 / 2) * (|(z - b).im| - (z - b).re) ≤ (1 / 2) * (|(w - b).im| - (w - b).re) := by
  rw [Complex.sub_re, Complex.sub_re, Complex.sub_im, Complex.sub_im, him]
  linarith

/-! ## the horizontal segment from a point to the spine -/

/-- Along the horizontal segment from `z ∈ Qreg` to the spine, the safe radius never drops below
`min 1 (srad z)`, and the segment stays inside `Qreg`. -/
private theorem sradSegment {b₁ b₂ : Option ℂ} (hAdm : MandelDim.QAdm b₁ b₂) :
    ∀ z : ℂ, z ∈ MandelDim.Qreg b₁ b₂ → ∀ p : ℂ,
      p ∈ segment ℝ z (Work.FatouCH.spineRe b₁ b₂ + ↑z.im * Complex.I) →
      min (1 : ℝ) (Work.FatouCH.srad b₁ b₂ z) ≤ Work.FatouCH.srad b₁ b₂ p ∧
        p ∈ MandelDim.Qreg b₁ b₂ := by
  intro z hz p hp
  rw [segment_eq_image'] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  set m : ℝ := Work.FatouCH.spineRe b₁ b₂ with hm
  set q : ℂ := z + t • (↑m + ↑z.im * Complex.I - z) with hqdef
  have hq_re : q.re = z.re + t * (m - z.re) := by
    rw [hqdef]
    simp only [Complex.add_re, Complex.sub_re, Complex.smul_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_add,
      smul_eq_mul]
    ring
  have hq_im : q.im = z.im := by
    rw [hqdef]
    simp only [Complex.add_im, Complex.sub_im, Complex.smul_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_add,
      sub_self, smul_eq_mul]
    ring
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  rcases b₁ with _ | a
  · rcases b₂ with _ | b
    · -- (none, none)
      rw [srad_none_none, srad_none_none]
      exact ⟨by linarith [min_le_left (1 : ℝ) (1 + ‖z‖), norm_nonneg q], mem_Qreg_none_none q⟩
    · -- (none, some b)
      rw [spineRe_none_some] at hm
      simp only [mem_Qreg_none_some, Complex.sub_re, Complex.sub_im] at hz
      rw [srad_none_some, srad_none_some]
      have hb_im : (q - b).im = z.im - b.im := by rw [Complex.sub_im, hq_im]
      have hb_re : (q - b).re = q.re - b.re := Complex.sub_re q b
      by_cases hzm : z.re ≤ m
      · have h2 : q.re ≤ m := seg_re_le_left hq_re ht1 hzm
        have hsp : (1 : ℝ) ≤ (1 / 2) * (|(q - b).im| - (q - b).re) := by
          rw [hb_im, hb_re]
          linarith [hm, h2, abs_nonneg (z.im - b.im)]
        exact ⟨le_trans (min_le_left (1 : ℝ) _) hsp,
          by rw [mem_Qreg_none_some, hb_im, hb_re]
             linarith [hm, h2, abs_nonneg (z.im - b.im)]⟩
      · have hzm' : m ≤ z.re := le_of_lt (not_le.mp hzm)
        have h2 : q.re ≤ z.re := seg_re_ge_right hq_re ht0 hzm'
        have hmono : (1 / 2) * (|(z - b).im| - (z - b).re) ≤
            (1 / 2) * (|(q - b).im| - (q - b).re) := s2_anti (by rw [hq_im]) h2
        exact ⟨le_trans (min_le_right (1 : ℝ) _) hmono,
          by rw [mem_Qreg_none_some, hb_im, hb_re]
             linarith [hz, h2]⟩
  · rcases b₂ with _ | b
    · -- (some a, none)
      rw [spineRe_some_none] at hm
      simp only [mem_Qreg_some_none, Complex.sub_re, Complex.sub_im] at hz
      rw [srad_some_none, srad_some_none]
      have ha_im : (q - a).im = z.im - a.im := by rw [Complex.sub_im, hq_im]
      have ha_re : (q - a).re = q.re - a.re := Complex.sub_re q a
      by_cases hzm : z.re ≤ m
      · have h1 : z.re ≤ q.re := seg_re_le_right hq_re ht0 hzm
        have hmono : (1 / 2) * ((z - a).re + |(z - a).im|) ≤
            (1 / 2) * ((q - a).re + |(q - a).im|) := s1_mono (by rw [hq_im]) h1
        exact ⟨le_trans (min_le_right (1 : ℝ) _) hmono,
          by rw [mem_Qreg_some_none, ha_im, ha_re]
             linarith [hz, h1]⟩
      · have hzm' : m ≤ z.re := le_of_lt (not_le.mp hzm)
        have h1 : m ≤ q.re := seg_re_ge_left hq_re ht1 hzm'
        have hsp : (1 : ℝ) ≤ (1 / 2) * ((q - a).re + |(q - a).im|) := by
          rw [ha_im, ha_re]
          linarith [hm, h1, abs_nonneg (z.im - a.im)]
        exact ⟨le_trans (min_le_left (1 : ℝ) _) hsp,
          by rw [mem_Qreg_some_none, ha_im, ha_re]
             linarith [hm, h1, abs_nonneg (z.im - a.im)]⟩
    · -- (some a, some b)
      have hAdm' : a.re + 4 < b.re := qAdm_some_some hAdm
      rw [spineRe_some_some] at hm
      simp only [mem_Qreg_some_some, Complex.sub_re, Complex.sub_im] at hz
      obtain ⟨hza, hzb⟩ := hz
      rw [srad_some_some, srad_some_some]
      have ha_im : (q - a).im = z.im - a.im := by rw [Complex.sub_im, hq_im]
      have ha_re : (q - a).re = q.re - a.re := Complex.sub_re q a
      have hb_im : (q - b).im = z.im - b.im := by rw [Complex.sub_im, hq_im]
      have hb_re : (q - b).re = q.re - b.re := Complex.sub_re q b
      by_cases hzm : z.re ≤ m
      · have h1 : z.re ≤ q.re := seg_re_le_right hq_re ht0 hzm
        have h2 : q.re ≤ m := seg_re_le_left hq_re ht1 hzm
        have hmono1 : (1 / 2) * ((z - a).re + |(z - a).im|) ≤
            (1 / 2) * ((q - a).re + |(q - a).im|) := s1_mono (by rw [hq_im]) h1
        have hsp2 : (1 : ℝ) ≤ (1 / 2) * (|(q - b).im| - (q - b).re) := by
          rw [hb_im, hb_re]
          linarith [hm, h2, hAdm', abs_nonneg (z.im - b.im)]
        refine ⟨le_min (le_trans (le_trans (min_le_right (1 : ℝ) _) (min_le_left _ _)) hmono1)
          (le_trans (min_le_left (1 : ℝ) _) hsp2), ?_⟩
        rw [mem_Qreg_some_some]
        refine ⟨?_, ?_⟩
        · rw [ha_im, ha_re]
          linarith [hza, h1]
        · rw [hb_im, hb_re]
          linarith [hm, h2, hAdm', abs_nonneg (z.im - b.im)]
      · have hzm' : m ≤ z.re := le_of_lt (not_le.mp hzm)
        have h1 : m ≤ q.re := seg_re_ge_left hq_re ht1 hzm'
        have h2 : q.re ≤ z.re := seg_re_ge_right hq_re ht0 hzm'
        have hsp1 : (1 : ℝ) ≤ (1 / 2) * ((q - a).re + |(q - a).im|) := by
          rw [ha_im, ha_re]
          linarith [hm, h1, hAdm', abs_nonneg (z.im - a.im)]
        have hmono2 : (1 / 2) * (|(z - b).im| - (z - b).re) ≤
            (1 / 2) * (|(q - b).im| - (q - b).re) := s2_anti (by rw [hq_im]) h2
        refine ⟨le_min (le_trans (min_le_left (1 : ℝ) _) hsp1)
          (le_trans (le_trans (min_le_right (1 : ℝ) _) (min_le_right _ _)) hmono2), ?_⟩
        rw [mem_Qreg_some_some]
        refine ⟨?_, ?_⟩
        · rw [ha_im, ha_re]
          linarith [hm, h1, hAdm', abs_nonneg (z.im - a.im)]
        · rw [hb_im, hb_re]
          linarith [hzb, h2]

/-! ## the spine-segment lemmas -/

private lemma eq_spine_of_re {m : ℝ} {z : ℂ} (hz : z.re = m) :
    z = ↑m + ↑z.im * Complex.I := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    exact hz
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, add_zero]

private lemma re_of_mem_segment_spine {m a c : ℝ} {p : ℂ}
    (hp : p ∈ segment ℝ (↑m + ↑a * Complex.I) (↑m + ↑c * Complex.I)) : p.re = m := by
  rw [segment_eq_image'] at hp
  obtain ⟨s, hs, rfl⟩ := hp
  simp only [Complex.add_re, Complex.sub_re, Complex.smul_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_add,
    sub_self, smul_eq_mul]
  ring

private lemma mem_Qreg_segment_spine {b₁ b₂ : Option ℂ} (hAdm : MandelDim.QAdm b₁ b₂)
    {m : ℝ} (hm : m = Work.FatouCH.spineRe b₁ b₂) {a c : ℝ} {p : ℂ}
    (hp : p ∈ segment ℝ (↑m + ↑a * Complex.I) (↑m + ↑c * Complex.I)) :
    p ∈ MandelDim.Qreg b₁ b₂ ∧ (1 : ℝ) ≤ Work.FatouCH.srad b₁ b₂ p := by
  have hpre : p.re = m := re_of_mem_segment_spine hp
  have hpe : p = ↑m + ↑p.im * Complex.I := eq_spine_of_re hpre
  have h1 := spineMemQreg hAdm p.im
  have h2 := spineSrad hAdm p.im
  rw [← hm] at h1 h2
  rw [hpe]
  exact ⟨h1, h2⟩

private lemma isCompact_segmentC (x y : ℂ) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (by continuity)

/-! ## tubes around a set -/

/-- The open tube of radius `r` around a set. -/
private def tube (A : Set ℂ) (r : ℝ) : Set ℂ := {z | ∃ a ∈ A, dist z a < r}

private lemma tube_eq_iUnion (A : Set ℂ) (r : ℝ) :
    tube A r = ⋃ a ∈ A, Metric.ball a r := by
  ext z
  constructor
  · rintro ⟨a, ha, hza⟩
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, by rwa [Metric.mem_ball]⟩⟩
  · intro hz
    rw [Set.mem_iUnion] at hz
    obtain ⟨a, hz⟩ := hz
    rw [Set.mem_iUnion] at hz
    obtain ⟨ha, hz⟩ := hz
    exact ⟨a, ha, by rwa [Metric.mem_ball] at hz⟩

private lemma isOpen_tube (A : Set ℂ) (r : ℝ) : IsOpen (tube A r) := by
  rw [tube_eq_iUnion]
  exact isOpen_biUnion fun a _ => Metric.isOpen_ball

private lemma convex_tube {A : Set ℂ} (hA : Convex ℝ A) (r : ℝ) : Convex ℝ (tube A r) := by
  intro u hu v hv a b ha hb hab
  obtain ⟨p, hpA, hpu⟩ := hu
  obtain ⟨q, hqA, hqv⟩ := hv
  refine ⟨a • p + b • q, hA hpA hqA ha hb hab, ?_⟩
  rw [dist_eq_norm]
  have hpu' : ‖u - p‖ < r := by rwa [dist_eq_norm] at hpu
  have hqv' : ‖v - q‖ < r := by rwa [dist_eq_norm] at hqv
  have hsub : a • u + b • v - (a • p + b • q) = a • (u - p) + b • (v - q) := by module
  rw [hsub]
  have hmax : max ‖u - p‖ ‖v - q‖ < r := max_lt hpu' hqv'
  calc ‖a • (u - p) + b • (v - q)‖
      ≤ ‖a • (u - p)‖ + ‖b • (v - q)‖ := norm_add_le _ _
    _ = a * ‖u - p‖ + b * ‖v - q‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
          abs_of_nonneg hb]
    _ ≤ a * max ‖u - p‖ ‖v - q‖ + b * max ‖u - p‖ ‖v - q‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
    _ = max ‖u - p‖ ‖v - q‖ := by rw [← add_mul, hab, one_mul]
    _ < r := hmax

private lemma closure_tube_subset {A : Set ℂ} {r : ℝ} (hr : 0 < r) :
    closure (tube A r) ⊆ tube A (2 * r) := by
  intro z hz
  rw [Metric.mem_closure_iff] at hz
  obtain ⟨w, hw, hzw⟩ := hz r hr
  obtain ⟨p, hpA, hwp⟩ := hw
  exact ⟨p, hpA, by linarith [dist_triangle z w p]⟩

private lemma isCompact_closure_tube {A : Set ℂ} (hA : IsCompact A) {r : ℝ} (hr : 0 < r) :
    IsCompact (closure (tube A r)) := by
  obtain ⟨R, hAR⟩ := hA.isBounded.subset_closedBall 0
  refine IsCompact.of_isClosed_subset (isCompact_closedBall 0 (R + 2 * r)) isClosed_closure ?_
  refine Set.Subset.trans (closure_tube_subset hr) ?_
  intro z hz
  obtain ⟨p, hpA, hzp⟩ := hz
  have hp' : dist p 0 ≤ R := Metric.mem_closedBall.mp (hAR hpA)
  rw [Metric.mem_closedBall]
  have hfin : dist z 0 < R + 2 * r := by
    calc dist z 0 ≤ dist z p + dist p 0 := dist_triangle z p 0
      _ < 2 * r + R := by linarith
      _ = R + 2 * r := by ring
  linarith

private lemma tube_subset_Qreg {b₁ b₂ : Option ℂ} {A : Set ℂ} {r : ℝ}
    (hrC : ∀ p ∈ A, 2 * r ≤ Work.FatouCH.srad b₁ b₂ p) :
    tube A (2 * r) ⊆ MandelDim.Qreg b₁ b₂ := by
  intro z hz
  obtain ⟨p, hpA, hzp⟩ := hz
  refine ball_srad_subset b₁ b₂ p ?_
  rw [Metric.mem_ball, Complex.dist_eq]
  rw [Complex.dist_eq] at hzp
  linarith [hrC p hpA]

/-! ## a path inside the region -/

/-- Any two points of the region are joined by a path inside the region: go horizontally to the
spine, along the spine, and horizontally out again. -/
private lemma joinedIn_Qreg {b₁ b₂ : Option ℂ} (hAdm : MandelDim.QAdm b₁ b₂) :
    ∀ x y : ℂ, x ∈ MandelDim.Qreg b₁ b₂ → y ∈ MandelDim.Qreg b₁ b₂ →
      JoinedIn (MandelDim.Qreg b₁ b₂) x y := by
  intro x y hx hy
  set m : ℝ := Work.FatouCH.spineRe b₁ b₂ with hm
  set sx : ℂ := ↑m + ↑x.im * Complex.I with hsx
  set sy : ℂ := ↑m + ↑y.im * Complex.I with hsy
  have hA : IsPathConnected (segment ℝ x sx) :=
    (convex_segment x sx).isPathConnected ⟨x, left_mem_segment ℝ x sx⟩
  have hB : IsPathConnected (segment ℝ sx sy) :=
    (convex_segment sx sy).isPathConnected ⟨sx, left_mem_segment ℝ sx sy⟩
  have hC : IsPathConnected (segment ℝ sy y) :=
    (convex_segment sy y).isPathConnected ⟨y, right_mem_segment ℝ sy y⟩
  have hAB : IsPathConnected (segment ℝ x sx ∪ segment ℝ sx sy) :=
    hA.union hB ⟨sx, right_mem_segment ℝ x sx, left_mem_segment ℝ sx sy⟩
  have hABC : IsPathConnected ((segment ℝ x sx ∪ segment ℝ sx sy) ∪ segment ℝ sy y) :=
    hAB.union hC ⟨sy, Or.inr (right_mem_segment ℝ sx sy), left_mem_segment ℝ sy y⟩
  have hsub : (segment ℝ x sx ∪ segment ℝ sx sy) ∪ segment ℝ sy y ⊆
      MandelDim.Qreg b₁ b₂ := by
    refine Set.union_subset (Set.union_subset ?_ ?_) ?_
    · intro p hp
      exact (sradSegment hAdm x hx p (by simpa only [hsx, hm] using hp)).2
    · intro p hp
      rw [hsx, hsy] at hp
      exact (mem_Qreg_segment_spine hAdm hm hp).1
    · intro p hp
      have hp2 : p ∈ segment ℝ y sy := by rwa [segment_symm (𝕜 := ℝ)] at hp
      exact (sradSegment hAdm y hy p (by simpa only [hsy, hm] using hp2)).2
  have hxABC : x ∈ (segment ℝ x sx ∪ segment ℝ sx sy) ∪ segment ℝ sy y :=
    Or.inl (Or.inl (left_mem_segment ℝ x sx))
  have hyABC : y ∈ (segment ℝ x sx ∪ segment ℝ sx sy) ∪ segment ℝ sy y :=
    Or.inr (right_mem_segment ℝ sy y)
  obtain ⟨x₀, hx₀, hrest⟩ := hABC
  exact ((hrest hxABC).symm.trans (hrest hyABC)).mono hsub

/-- The region is preconnected. -/
private theorem QregPreconnected {b₁ b₂ : Option ℂ} (hAdm : MandelDim.QAdm b₁ b₂) :
    IsPreconnected (MandelDim.Qreg b₁ b₂) := by
  have hne : (MandelDim.Qreg b₁ b₂).Nonempty := ⟨_, spineMemQreg hAdm 0⟩
  obtain ⟨x₀, hx₀⟩ := hne
  exact (IsPathConnected.isConnected
    ⟨x₀, hx₀, fun y hy => joinedIn_Qreg hAdm x₀ y hx₀ hy⟩).isPreconnected

/-! ## a compact connected neighbourhood of two points -/

/-- Two points of the region are enclosed in an open preconnected set whose closure is compact and
inside the region (a union of three convex tubes around the polyline through the spine). -/
private theorem QregNbhd {b₁ b₂ : Option ℂ} (hAdm : MandelDim.QAdm b₁ b₂) :
    ∀ x y : ℂ, x ∈ MandelDim.Qreg b₁ b₂ → y ∈ MandelDim.Qreg b₁ b₂ →
      ∃ U : Set ℂ, IsOpen U ∧ IsPreconnected U ∧ x ∈ U ∧ y ∈ U ∧
        IsCompact (closure U) ∧ closure U ⊆ MandelDim.Qreg b₁ b₂ := by
  intro x y hx hy
  set m : ℝ := Work.FatouCH.spineRe b₁ b₂ with hm
  set sx : ℂ := ↑m + ↑x.im * Complex.I with hsx
  set sy : ℂ := ↑m + ↑y.im * Complex.I with hsy
  set r : ℝ := min (min 1 (Work.FatouCH.srad b₁ b₂ x))
    (min 1 (Work.FatouCH.srad b₁ b₂ y)) / 4 with hr
  have hxpos : 0 < Work.FatouCH.srad b₁ b₂ x := sradPos_of_mem hx
  have hypos : 0 < Work.FatouCH.srad b₁ b₂ y := sradPos_of_mem hy
  have hNpos : 0 < min (min 1 (Work.FatouCH.srad b₁ b₂ x))
      (min 1 (Work.FatouCH.srad b₁ b₂ y)) :=
    lt_min (lt_min one_pos hxpos) (lt_min one_pos hypos)
  have hrpos : 0 < r := by rw [hr]; linarith
  have h4x : 4 * r ≤ min 1 (Work.FatouCH.srad b₁ b₂ x) := by
    rw [hr]; linarith [min_le_left (min 1 (Work.FatouCH.srad b₁ b₂ x))
      (min 1 (Work.FatouCH.srad b₁ b₂ y))]
  have h4y : 4 * r ≤ min 1 (Work.FatouCH.srad b₁ b₂ y) := by
    rw [hr]; linarith [min_le_right (min 1 (Work.FatouCH.srad b₁ b₂ x))
      (min 1 (Work.FatouCH.srad b₁ b₂ y))]
  have h4h : 4 * r ≤ 1 := by
    rw [hr]
    linarith [min_le_left (min 1 (Work.FatouCH.srad b₁ b₂ x))
      (min 1 (Work.FatouCH.srad b₁ b₂ y)), min_le_left (1 : ℝ) (Work.FatouCH.srad b₁ b₂ x)]
  have hsegX : ∀ p ∈ segment ℝ x sx,
      p ∈ segment ℝ x (Work.FatouCH.spineRe b₁ b₂ + ↑x.im * Complex.I) :=
    fun p hp => by simpa only [hsx, hm] using hp
  have hsegY : ∀ p ∈ segment ℝ sy y,
      p ∈ segment ℝ y (Work.FatouCH.spineRe b₁ b₂ + ↑y.im * Complex.I) := by
    intro p hp
    have hp2 : p ∈ segment ℝ y sy := by rwa [segment_symm (𝕜 := ℝ)] at hp
    simpa only [hsy, hm] using hp2
  have hsegM : ∀ p ∈ segment ℝ sx sy,
      p ∈ segment ℝ (↑m + ↑x.im * Complex.I) (↑m + ↑y.im * Complex.I) := by
    intro p hp
    rwa [hsx, hsy] at hp
  have hAr : tube (segment ℝ x sx) (2 * r) ⊆ MandelDim.Qreg b₁ b₂ := by
    refine tube_subset_Qreg ?_
    intro p hp
    linarith [(sradSegment hAdm x hx p (hsegX p hp)).1, h4x]
  have hBr : tube (segment ℝ sx sy) (2 * r) ⊆ MandelDim.Qreg b₁ b₂ := by
    refine tube_subset_Qreg ?_
    intro p hp
    linarith [(mem_Qreg_segment_spine hAdm hm (hsegM p hp)).2, h4h]
  have hCr : tube (segment ℝ sy y) (2 * r) ⊆ MandelDim.Qreg b₁ b₂ := by
    refine tube_subset_Qreg ?_
    intro p hp
    linarith [(sradSegment hAdm y hy p (hsegY p hp)).1, h4y]
  have hX1 : IsPreconnected (tube (segment ℝ x sx) r) :=
    (convex_tube (convex_segment x sx) r).isPreconnected
  have hX2 : IsPreconnected (tube (segment ℝ sx sy) r) :=
    (convex_tube (convex_segment sx sy) r).isPreconnected
  have hX3 : IsPreconnected (tube (segment ℝ sy y) r) :=
    (convex_tube (convex_segment sy y) r).isPreconnected
  have hm1 : sx ∈ tube (segment ℝ x sx) r :=
    ⟨sx, right_mem_segment ℝ x sx, by simpa using hrpos⟩
  have hm2 : sx ∈ tube (segment ℝ sx sy) r :=
    ⟨sx, left_mem_segment ℝ sx sy, by simpa using hrpos⟩
  have hm3 : sy ∈ tube (segment ℝ sx sy) r :=
    ⟨sy, right_mem_segment ℝ sx sy, by simpa using hrpos⟩
  have hm4 : sy ∈ tube (segment ℝ sy y) r :=
    ⟨sy, left_mem_segment ℝ sy y, by simpa using hrpos⟩
  have hU12 : IsPreconnected (tube (segment ℝ x sx) r ∪ tube (segment ℝ sx sy) r) :=
    IsPreconnected.union sx hm1 hm2 hX1 hX2
  refine ⟨tube (segment ℝ x sx) r ∪ tube (segment ℝ sx sy) r ∪ tube (segment ℝ sy y) r,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact IsOpen.union (IsOpen.union (isOpen_tube _ r) (isOpen_tube _ r)) (isOpen_tube _ r)
  · exact IsPreconnected.union sy
      (show sy ∈ tube (segment ℝ x sx) r ∪ tube (segment ℝ sx sy) r from Or.inr hm3)
      hm4 hU12 hX3
  · exact Or.inl (Or.inl ⟨x, left_mem_segment ℝ x sx, by simpa using hrpos⟩)
  · exact Or.inr ⟨y, right_mem_segment ℝ sy y, by simpa using hrpos⟩
  · rw [closure_union, closure_union]
    exact ((isCompact_closure_tube (isCompact_segmentC x sx) hrpos).union
        (isCompact_closure_tube (isCompact_segmentC sx sy) hrpos)).union
      (isCompact_closure_tube (isCompact_segmentC sy y) hrpos)
  · rw [closure_union, closure_union]
    refine Set.union_subset (Set.union_subset ?_ ?_) ?_
    · exact Set.Subset.trans (closure_tube_subset hrpos) hAr
    · exact Set.Subset.trans (closure_tube_subset hrpos) hBr
    · exact Set.Subset.trans (closure_tube_subset hrpos) hCr

/-! ## the theorem -/

/-- Geometry of Shishikura's region `𝒬(b₁,b₂)`: it is open and preconnected, it contains the
vertical spine `{spineRe + i t}` together with a safe disc of radius `≥ 1`, `srad` is a safety
radius everywhere, positive on the region, monotone (up to the clipping at `1`) along the
horizontal motion towards the spine, and any two of its points can be enclosed in a compact
connected open set inside the region. -/
theorem SradGeo {b₁ b₂ : Option ℂ} (hAdm : MandelDim.QAdm b₁ b₂) :
    IsOpen (MandelDim.Qreg b₁ b₂) ∧ IsPreconnected (MandelDim.Qreg b₁ b₂) ∧
    (∀ a ∈ b₁, a.re < Work.FatouCH.spineRe b₁ b₂) ∧
    (∀ b ∈ b₂, Work.FatouCH.spineRe b₁ b₂ < b.re) ∧
    (∀ t : ℝ, Work.FatouCH.spineRe b₁ b₂ + t * Complex.I ∈ MandelDim.Qreg b₁ b₂ ∧
      (1 : ℝ) ≤ Work.FatouCH.srad b₁ b₂ (Work.FatouCH.spineRe b₁ b₂ + t * Complex.I)) ∧
    (∀ z : ℂ, Metric.ball z (Work.FatouCH.srad b₁ b₂ z) ⊆ MandelDim.Qreg b₁ b₂) ∧
    (∀ z : ℂ, z ∈ MandelDim.Qreg b₁ b₂ → 0 < Work.FatouCH.srad b₁ b₂ z) ∧
    (∀ z p : ℂ, z ∈ MandelDim.Qreg b₁ b₂ →
      p ∈ segment ℝ z (Work.FatouCH.spineRe b₁ b₂ + z.im * Complex.I) →
      min (1 : ℝ) (Work.FatouCH.srad b₁ b₂ z) ≤ Work.FatouCH.srad b₁ b₂ p ∧
        p ∈ MandelDim.Qreg b₁ b₂) ∧
    (∀ x y : ℂ, x ∈ MandelDim.Qreg b₁ b₂ → y ∈ MandelDim.Qreg b₁ b₂ →
      ∃ U : Set ℂ, IsOpen U ∧ IsPreconnected U ∧ x ∈ U ∧ y ∈ U ∧
        IsCompact (closure U) ∧ closure U ⊆ MandelDim.Qreg b₁ b₂) := by
  refine ⟨isOpen_Qreg b₁ b₂, QregPreconnected hAdm, spineLtLeft hAdm, spineLtRight hAdm, ?_,
    ball_srad_subset b₁ b₂, fun z hz => sradPos_of_mem hz, ?_, QregNbhd hAdm⟩
  · intro t
    exact ⟨spineMemQreg hAdm t, spineSrad hAdm t⟩
  · intro z p hz hp
    exact ⟨(sradSegment hAdm z hz p hp).1, (sradSegment hAdm z hz p hp).2⟩

end Work.FatouCH.Cont
