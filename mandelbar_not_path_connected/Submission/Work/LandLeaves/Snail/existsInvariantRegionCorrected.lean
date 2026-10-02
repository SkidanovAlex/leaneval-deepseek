import Mathlib
import Submission.Work.LandLeaves.Snail.barrierDefs
import Submission.Work.LandLeaves.Snail.exists_barrier_min
import Submission.Work.LandLeaves.Snail.leftCross_bddBelow_on_Icc
import Submission.Work.LandLeaves.Snail.leftCross_tendsto_atBot
import Submission.Work.LandLeaves.Snail.pathTail_isClosed
import Submission.Work.LandLeaves.Snail.deriv_re_pos_deep
import Submission.Work.LandLeaves.Snail.pathStaysLeftOfBarrier

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The invariant region cut off by a snail path

(The statement is untouched; helpers live above it.)
-/

set_option linter.unusedVariables false

open Filter Set
open Complex
open scoped Topology

namespace Work.LandLeaves.Snail

/-- The open half-strip `{Re Z < M} ∩ {m < Im Z < m + 2π + 1}`, whose exponential is the punctured
disc of radius `e^M`. -/
def strip (M m : ℝ) : Set ℂ := {Z : ℂ | Z.re < M ∧ m < Z.im ∧ Z.im < m + (2 * Real.pi + 1)}

theorem mem_strip {M m : ℝ} {Z : ℂ} :
    Z ∈ strip M m ↔ Z.re < M ∧ m < Z.im ∧ Z.im < m + (2 * Real.pi + 1) := Iff.rfl

/-- Every real number lies in some translate `(m, m + 2π]` of the half-open period interval. -/
theorem exists_int_height (m a : ℝ) : ∃ k : ℤ, m < a + (k:ℝ) * (2 * Real.pi) ∧
    a + (k:ℝ) * (2 * Real.pi) ≤ m + 2 * Real.pi := by
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  refine ⟨⌊(m - a) / (2 * Real.pi)⌋ + 1, ?_, ?_⟩
  · have h1 : (m - a) / (2 * Real.pi) < ((⌊(m - a) / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have h3 : (m - a) / (2 * Real.pi) * (2 * Real.pi) = m - a := by field_simp
    push_cast
    nlinarith [mul_lt_mul_of_pos_right h1 hpi, h3]
  · have h1 : ((⌊(m - a) / (2 * Real.pi)⌋ : ℤ) : ℝ) ≤ (m - a) / (2 * Real.pi) :=
      Int.floor_le _
    have h3 : (m - a) / (2 * Real.pi) * (2 * Real.pi) = m - a := by field_simp
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right h1 (le_of_lt hpi), h3]

/-- The half-strip is convex, in particular preconnected. -/
theorem convex_strip (M m : ℝ) : Convex ℝ (strip M m) := by
  rw [convex_iff_forall_pos]
  intro Z hZ W hW a b ha hb hab
  obtain ⟨h1, h2, h3⟩ := mem_strip.mp hZ
  obtain ⟨h4, h5, h6⟩ := mem_strip.mp hW
  have hre : (a • Z + b • W).re = a * Z.re + b * W.re := by simp
  have him : (a • Z + b • W).im = a * Z.im + b * W.im := by simp
  have hsumM : a * M + b * M = M := by rw [← add_mul, hab, one_mul]
  have hsumm : a * m + b * m = m := by rw [← add_mul, hab, one_mul]
  refine mem_strip.mpr ⟨?_, ?_, ?_⟩
  · rw [hre]
    have e1 : a * Z.re < a * M := mul_lt_mul_of_pos_left h1 ha
    have e2 : b * W.re < b * M := mul_lt_mul_of_pos_left h4 hb
    linarith
  · rw [him]
    have e1 : a * m < a * Z.im := mul_lt_mul_of_pos_left h2 ha
    have e2 : b * m < b * W.im := mul_lt_mul_of_pos_left h5 hb
    linarith
  · rw [him]
    have e1 : a * Z.im < a * (m + (2 * Real.pi + 1)) := mul_lt_mul_of_pos_left h3 ha
    have e2 : b * W.im < b * (m + (2 * Real.pi + 1)) := mul_lt_mul_of_pos_left h6 hb
    have hsum : a * (m + (2 * Real.pi + 1)) + b * (m + (2 * Real.pi + 1))
        = m + (2 * Real.pi + 1) := by rw [← add_mul, hab, one_mul]
    linarith

/-- **The exponential of a half-strip of height `2π + 1` is the punctured disc.** -/
theorem exp_image_strip {M m : ℝ} :
    Complex.exp '' strip M m = {w : ℂ | w ≠ 0 ∧ ‖w‖ < Real.exp M} := by
  ext w
  constructor
  · rintro ⟨Z, hZ, rfl⟩
    obtain ⟨h1, h2, h3⟩ := mem_strip.mp hZ
    exact ⟨Complex.exp_ne_zero Z, by rw [Complex.norm_exp, Real.exp_lt_exp]; exact h1⟩
  · rintro ⟨hw, hwM⟩
    obtain ⟨k, hk1, hk2⟩ := exists_int_height m w.arg
    refine ⟨((Real.log ‖w‖ : ℝ) : ℂ) + ((w.arg : ℂ) + (k : ℂ) * (2 * Real.pi)) * I, ?_, ?_⟩
    · refine mem_strip.mpr ⟨?_, ?_, ?_⟩
      · simpa using (Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hw)).mpr hwM
      · simpa using hk1
      · have : w.arg + (k:ℝ) * (2 * Real.pi) < m + (2 * Real.pi + 1) := by linarith
        simpa using this
    · rw [Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I,
        Complex.cos_add_int_mul_two_pi, Complex.sin_add_int_mul_two_pi,
        Real.exp_log (norm_pos_iff.mpr hw)]
      exact Complex.norm_mul_cos_add_sin_mul_I w

/-- The ambient domain: the part of the deep-left half plane above the foot of the barrier, with
the barrier removed. -/
def barrierRegion (P : ℝ → ℂ) (X t₀ : ℝ) : Set ℂ :=
  {Z : ℂ | Z.re < X ∧ (P t₀).im < Z.im} \ pathTail P t₀

/-- The base point of the construction. -/
def barrierBase (P : ℝ → ℂ) (M t₀ : ℝ) : ℂ := ⟨M - 1, (P t₀).im + 1⟩

/-- The part of `barrierRegion` that lies strictly to the left of the barrier at its own height. -/
def leftRegion (P : ℝ → ℂ) (X t₀ : ℝ) : Set ℂ :=
  {Z : ℂ | Z.re < X ∧ (P t₀).im < Z.im ∧ Z.re < leftCross P t₀ Z.im}

theorem mapsTo_pathTail {F : ℂ → ℂ} {P : ℝ → ℂ} {T t₀ : ℝ} (htT : T ≤ t₀)
    (hPinv : ∀ t ∈ Set.Ici T, F (P t) = P (t + 1)) :
    Set.MapsTo F (pathTail P t₀) (pathTail P t₀) := by
  intro W hW
  rw [pathTail] at hW ⊢
  obtain ⟨u, hu, rfl⟩ := hW
  exact ⟨u + 1, by simp only [Set.mem_Ici] at hu ⊢; linarith, (hPinv u (le_trans htT hu)).symm⟩

/-- `{z | z.re < X}` is preconnected. -/
theorem isPreconnected_re_lt (X : ℝ) : IsPreconnected {Z : ℂ | Z.re < X} :=
  (convex_halfSpace_re_lt X).isPreconnected

/-- **The open mapping property of `F` on the half-plane.** -/
theorem isOpen_image_of_subset {F : ℂ → ℂ} {X : ℝ}
    (hdiff : DifferentiableOn ℂ F {Z : ℂ | Z.re < X})
    (hinj : Set.InjOn F {Z : ℂ | Z.re < X}) :
    ∀ s : Set ℂ, s ⊆ {Z : ℂ | Z.re < X} → IsOpen s → IsOpen (F '' s) := by
  intro s hs hso
  have hXo : IsOpen {Z : ℂ | Z.re < X} := isOpen_lt Complex.continuous_re continuous_const
  have hpc : IsPreconnected {Z : ℂ | Z.re < X} := isPreconnected_re_lt X
  have hana : AnalyticOnNhd ℂ F {Z : ℂ | Z.re < X} := hdiff.analyticOnNhd hXo
  rcases hana.is_constant_or_isOpen hpc with hconst | hopen
  · exfalso
    obtain ⟨w, hw⟩ := hconst
    have h1 : (⟨X - 1, 0⟩ : ℂ) ∈ {Z : ℂ | Z.re < X} := by
      simp only [Set.mem_ofPred_eq]; simp
    have h2 : (⟨X - 2, 0⟩ : ℂ) ∈ {Z : ℂ | Z.re < X} := by
      simp only [Set.mem_ofPred_eq]; simp
    have hne : (⟨X - 1, 0⟩ : ℂ) ≠ ⟨X - 2, 0⟩ := by
      intro h; simpa using congrArg Complex.re h
    exact hne (hinj h1 h2 (by rw [hw _ h1, hw _ h2]))
  · exact hopen s hs hso

/-- The leftmost barrier point at height `h` bounds the real part of every barrier point at that
height from below. -/
theorem leftCross_le_of_mem {F : ℂ → ℂ} {X₁ : ℝ} {c : ℂ} {P : ℝ → ℂ} {T t₀ : ℝ}
    (hc_im : 0 < c.im) (hPc : ContinuousOn P (Set.Ici T)) (hT : T ≤ t₀)
    (hheight : ∀ Z : ℂ, Z.re < X₁ → Z.im + c.im / 2 ≤ (F Z).im)
    (hPinv : ∀ t ∈ Set.Ici T, F (P t) = P (t + 1))
    (hPt : ∀ t : ℝ, t₀ ≤ t → (P t).re < X₁)
    {h : ℝ} (hh : (P t₀).im ≤ h) {W : ℂ} (hW : W ∈ pathTail P t₀) (him : W.im = h) :
    leftCross P t₀ h ≤ W.re := by
  obtain ⟨Wm, hWm, hWmim, hWmre, hWmmin⟩ := exists_barrier_min (F := F) (P := P) (c := c)
    (T := T) (X₀ := X₁) (t₀ := t₀) hc_im hPc hT hheight hPinv hPt hh
  rw [← hWmre]
  exact hWmmin W hW him

/-- **CRUX 1 (planar separation).**  The component of the deep corner in the region cut out by the
barrier stays in the deep half plane `{re < X₁}`. -/
theorem component_re_lt {F : ℂ → ℂ} {X X₁ : ℝ} {c : ℂ} {P : ℝ → ℂ} {T t₀ M : ℝ}
    (hc_re : c.re = 0) (hc_im : 0 < c.im) (hX₁X : X₁ < X)
    (hdiff : DifferentiableOn ℂ F {Z : ℂ | Z.re < X})
    (hinj : Set.InjOn F {Z : ℂ | Z.re < X})
    (hper : ∀ Z : ℂ, Z.re < X → F (Z + 2 * (Real.pi : ℂ) * Complex.I) = F Z + 2 * (Real.pi : ℂ) * Complex.I)
    (hd : ∀ Z : ℂ, Z.re < X₁ → (F Z).re < X ∧ |(F Z).re - Z.re| < c.im / 4 ∧
      |(F Z).im - Z.im - c.im| < c.im / 4)
    (hmono : ∀ Z : ℂ, Z.re < X₁ → 0 < (deriv F Z).re)
    (hPc : ContinuousOn P (Set.Ici T)) (htT : T + 1 ≤ t₀)
    (hPinv : ∀ t ∈ Set.Ici T, F (P t) = P (t + 1))
    (hPt : ∀ t : ℝ, t₀ ≤ t → (P t).re < X₁)
    (hPre : Filter.Tendsto (fun t : ℝ => (P t).re) Filter.atTop Filter.atBot)
    (hM : ∀ h ∈ Set.Icc ((P t₀).im) ((P t₀).im + (2 * Real.pi + 1)), M ≤ leftCross P t₀ h) :
    ∀ Z ∈ connectedComponentIn (barrierRegion P X t₀) (barrierBase P M t₀), Z.re < X₁ := by
  classical
  have hT : T ≤ t₀ := by linarith
  have hheight : ∀ Z : ℂ, Z.re < X₁ → Z.im + c.im / 2 ≤ (F Z).im := fun Z hZ =>
    by linarith [(abs_lt.mp (hd Z hZ).2.2).1]
  have hbase : barrierBase P M t₀ ∈ barrierRegion P X t₀ := by
    obtain ⟨Wm, hWm, hWmim, hWmre, -⟩ := exists_barrier_min (F := F) (P := P) (c := c)
      (T := T) (X₀ := X₁) (t₀ := t₀) hc_im hPc hT hheight hPinv hPt (h := (P t₀).im + 1)
      (by linarith)
    have hWmX : Wm.re < X₁ := by
      rw [pathTail] at hWm; obtain ⟨u, hu, rfl⟩ := hWm; exact hPt u hu
    have hMX₁ : M < X₁ := by
      have h1 := hM ((P t₀).im + 1) ⟨by linarith, by linarith [Real.pi_pos]⟩
      rw [← hWmre] at h1; linarith
    refine ⟨⟨by rw [barrierBase]; simp only; linarith, by rw [barrierBase]; simp only; linarith⟩, ?_⟩
    intro hmem
    rw [pathTail] at hmem
    obtain ⟨u, hu, hueq⟩ := hmem
    have him : (P u).im = (P t₀).im + 1 := by rw [hueq, barrierBase]
    have h1 : leftCross P t₀ ((P t₀).im + 1) ≤ (P u).re :=
      leftCross_le_of_mem hc_im hPc hT hheight hPinv hPt (by linarith) ⟨u, hu, rfl⟩ him
    have h2 : M ≤ leftCross P t₀ ((P t₀).im + 1) :=
      hM ((P t₀).im + 1) ⟨by linarith, by linarith [Real.pi_pos]⟩
    have h3 : (P u).re = M - 1 := by rw [hueq, barrierBase]
    linarith
  have hGopen : IsOpen (barrierRegion P X t₀) := by
    rw [barrierRegion]
    have h1 : IsOpen {Z : ℂ | Z.re < X} := isOpen_lt Complex.continuous_re continuous_const
    have h2 : IsOpen {Z : ℂ | (P t₀).im < Z.im} :=
      isOpen_lt continuous_const Complex.continuous_im
    have hset : {Z : ℂ | Z.re < X ∧ (P t₀).im < Z.im}
        = {Z : ℂ | Z.re < X} ∩ {Z : ℂ | (P t₀).im < Z.im} := by ext Z; simp
    rw [hset]
    exact (h1.inter h2).sdiff (pathTail_isClosed (F := F) (P := P) (c := c) (T := T)
      (X₀ := X₁) (t₀ := t₀) hc_im hPc hT hheight hPinv hPt)
  intro Z hZ
  have hCopen : IsOpen (connectedComponentIn (barrierRegion P X t₀) (barrierBase P M t₀)) :=
    hGopen.connectedComponentIn
  have hCconn : IsConnected (connectedComponentIn (barrierRegion P X t₀) (barrierBase P M t₀)) :=
    ⟨⟨barrierBase P M t₀, mem_connectedComponentIn hbase⟩, isPreconnected_connectedComponentIn⟩
  obtain ⟨γ, hγF⟩ := ((hCopen.isConnected_iff_isPathConnected).mp hCconn).joinedIn
    (barrierBase P M t₀) (mem_connectedComponentIn hbase) Z hZ
  exact path_re_lt_of_mem_region_h hc_im hX₁X hheight hPc htT hPinv hPt hM γ
    (fun t => connectedComponentIn_subset _ _ (hγF t))

/-- Above a sufficiently large height, every point of the barrier has real part `< b`. -/
theorem exists_height_of_barrier_re_lt {P : ℝ → ℂ} {T t₀ : ℝ} (hPc : ContinuousOn P (Set.Ici T))
    (htT : T ≤ t₀) (hPre : Filter.Tendsto (fun t : ℝ => (P t).re) Filter.atTop Filter.atBot)
    (b : ℝ) :
    ∃ H : ℝ, ∀ W ∈ pathTail P t₀, H < W.im → W.re < b := by
  have hev : ∀ᶠ t : ℝ in Filter.atTop, (P t).re ≤ b - 1 :=
    hPre.eventually (Filter.mem_atBot (b - 1))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨S, hS⟩ := hev
  have hcont : ContinuousOn (fun t : ℝ => (P t).im) (Set.Icc t₀ (max S t₀)) :=
    Complex.continuous_im.comp_continuousOn (hPc.mono (fun t ht => le_trans htT ht.1))
  obtain ⟨x, -, hxmax⟩ := isCompact_Icc.exists_isMaxOn
    (⟨t₀, le_rfl, le_max_right _ _⟩ : (Set.Icc t₀ (max S t₀)).Nonempty) hcont
  refine ⟨(P x).im, fun W hW him => ?_⟩
  rw [pathTail] at hW
  obtain ⟨u, hu, rfl⟩ := hW
  have huS : S ≤ u := by
    by_contra hlt
    rw [not_le] at hlt
    have hmem : u ∈ Set.Icc t₀ (max S t₀) :=
      ⟨hu, by linarith [le_max_left S t₀, le_of_lt hlt]⟩
    exact absurd (hxmax hmem) (not_le.mpr him)
  linarith [hS u huS]

/-- The imaginary parts of the iterates grow at least linearly while the iterates stay in the
half plane `{re < X₁}`. -/
theorem im_iterate_ge {F : ℂ → ℂ} {c : ℂ} {X₁ : ℝ} {Z : ℂ}
    (hd : ∀ Z : ℂ, Z.re < X₁ → Z.im + c.im / 2 ≤ (F Z).im)
    (hre : ∀ n : ℕ, ((F^[n]) Z).re < X₁) :
    ∀ n : ℕ, Z.im + n * (c.im / 2) ≤ ((F^[n]) Z).im := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 := hd ((F^[k]) Z) (hre k)
    rw [Function.iterate_succ_apply']
    push_cast
    nlinarith [h1, ih]

end Work.LandLeaves.Snail

namespace Work.LandLeaves.Snail

/-- **The reduction (proved).**  If every point of the component stays in `{re < X₁}`, then every
point of the component has a barrier point of its own height strictly to its right. -/
theorem existsBarrierRight_of_re_lt {X X₁ : ℝ} {P : ℝ → ℂ} {t₀ M : ℝ} (hX₁X : X₁ < X)
    (hT : ∀ Z ∈ connectedComponentIn (barrierRegion P X t₀) (barrierBase P M t₀), Z.re < X₁)
    {Z : ℂ} (hZ : Z ∈ connectedComponentIn (barrierRegion P X t₀) (barrierBase P M t₀)) :
    ∃ W ∈ pathTail P t₀, W.im = Z.im ∧ Z.re < W.re := by
  by_contra hcon
  push Not at hcon
  have hZmem : Z ∈ barrierRegion P X t₀ := connectedComponentIn_subset _ _ hZ
  obtain ⟨⟨hZlt, hZgt⟩, hZnotin⟩ := hZmem
  set h : ℝ := Z.im with hh
  have hY : (P t₀).im < h := hZgt
  have hZX : Z.re < X := hZlt
  set c0 : ℝ := max Z.re X₁ with hc0
  have hc0X : c0 < X := by rw [hc0]; exact max_lt hZX hX₁X
  set x : ℝ := (c0 + X) / 2 with hx
  have hc0x : c0 < x := by rw [hx]; linarith
  have hxX : x < X := by rw [hx]; linarith
  have hZrec0 : Z.re ≤ c0 := le_max_left _ _
  have hX₁c0 : X₁ ≤ c0 := le_max_right _ _
  have hZ'x : Z.re < x := lt_of_le_of_lt hZrec0 hc0x
  have hX₁x : X₁ < x := lt_of_le_of_lt hX₁c0 hc0x
  set S : Set ℂ := {w : ℂ | w.im = h ∧ Z.re ≤ w.re ∧ w.re ≤ x} with hS
  have hSpre : IsPreconnected S := by
    have heq : S = (fun y : ℝ => (y : ℂ) + (h : ℂ) * Complex.I) '' Set.Icc Z.re x := by
      ext w; constructor
      · rintro ⟨hwim, hw1, hw2⟩
        refine ⟨w.re, ⟨hw1, hw2⟩, ?_⟩
        apply Complex.ext <;> simp [hwim]
      · rintro ⟨y, hy, rfl⟩
        refine ⟨?_, ?_, ?_⟩ <;> simp_all
    rw [heq]
    exact isPreconnected_Icc.image _ (by fun_prop)
  have hSsub : S ⊆ barrierRegion P X t₀ := by
    intro w hw
    obtain ⟨hwim, hw1, hw2⟩ := hw
    refine ⟨⟨by linarith [hw2, hxX], by rw [hwim]; exact hY⟩, ?_⟩
    intro hwB
    obtain ⟨u, hu, hueq⟩ := hwB
    have him : (P u).im = h := by rw [hueq, hwim]
    have hle := hcon (P u) ⟨u, hu, rfl⟩ him
    have hre : (P u).re = w.re := by rw [hueq]
    rw [hre] at hle
    have hwz : w.re = Z.re := le_antisymm hle hw1
    have hwZ : w = Z := by
      apply Complex.ext
      · exact hwz
      · rw [hwim, hh]
    exact hZnotin ⟨u, hu, hueq.trans hwZ⟩
  have hZS : Z ∈ S := ⟨hh.symm, le_rfl, hZ'x.le⟩
  have hZ'S : (⟨x, h⟩ : ℂ) ∈ S := ⟨rfl, hZ'x.le, le_rfl⟩
  have hZ'comp : (⟨x, h⟩ : ℂ) ∈ connectedComponentIn (barrierRegion P X t₀) Z :=
    hSpre.subset_connectedComponentIn hZS hSsub hZ'S
  have hcomp : connectedComponentIn (barrierRegion P X t₀) Z
      = connectedComponentIn (barrierRegion P X t₀) (barrierBase P M t₀) :=
    (connectedComponentIn_eq hZ).symm
  have hZ'base : (⟨x, h⟩ : ℂ) ∈ connectedComponentIn (barrierRegion P X t₀)
      (barrierBase P M t₀) := hcomp ▸ hZ'comp
  have hlt : (⟨x, h⟩ : ℂ).re < X₁ := hT _ hZ'base
  have hxre : (⟨x, h⟩ : ℂ).re = x := rfl
  linarith [hX₁x, hlt]

/-- **The separation (proved from `component_re_lt`).** -/
theorem component_separated {F : ℂ → ℂ} {X X₁ : ℝ} {c : ℂ} {P : ℝ → ℂ} {T t₀ M : ℝ}
    (hc_re : c.re = 0) (hc_im : 0 < c.im) (hX₁X : X₁ < X)
    (hdiff : DifferentiableOn ℂ F {Z : ℂ | Z.re < X})
    (hinj : Set.InjOn F {Z : ℂ | Z.re < X})
    (hper : ∀ Z : ℂ, Z.re < X → F (Z + 2 * (Real.pi : ℂ) * Complex.I) = F Z + 2 * (Real.pi : ℂ) * Complex.I)
    (hd : ∀ Z : ℂ, Z.re < X₁ → (F Z).re < X ∧ |(F Z).re - Z.re| < c.im / 4 ∧
      |(F Z).im - Z.im - c.im| < c.im / 4)
    (hmono : ∀ Z : ℂ, Z.re < X₁ → 0 < (deriv F Z).re)
    (hPc : ContinuousOn P (Set.Ici T)) (htT : T + 1 ≤ t₀)
    (hPinv : ∀ t ∈ Set.Ici T, F (P t) = P (t + 1))
    (hPt : ∀ t : ℝ, t₀ ≤ t → (P t).re < X₁)
    (hPre : Filter.Tendsto (fun t : ℝ => (P t).re) Filter.atTop Filter.atBot)
    (hM : ∀ h ∈ Set.Icc ((P t₀).im) ((P t₀).im + (2 * Real.pi + 1)), M ≤ leftCross P t₀ h) :
    ∀ Z ∈ connectedComponentIn (barrierRegion P X t₀) (barrierBase P M t₀),
      ∃ W ∈ pathTail P t₀, W.im = Z.im ∧ Z.re < W.re :=
  fun Z hZ => existsBarrierRight_of_re_lt hX₁X
    (fun W hW => component_re_lt hc_re hc_im hX₁X hdiff hinj hper hd hmono hPc htT hPinv hPt hPre hM W hW)
    hZ

end Work.LandLeaves.Snail

namespace Work.LandLeaves.Snail

/-- The three-segment set joining a point `W` to the base point, all inside the region (provided `W`
lies strictly left of the barrier at its own height and at height `≥ (P t₀).im + 1`). -/
theorem mem_component_of_left {F : ℂ → ℂ} {X X₁ : ℝ} {c : ℂ} {P : ℝ → ℂ} {T t₀ M : ℝ}
    (hc_im : 0 < c.im) (hX₁X : X₁ < X)
    (hd : ∀ Z : ℂ, Z.re < X₁ → Z.im + c.im / 2 ≤ (F Z).im ∧ (F Z).re < X ∧
      |(F Z).re - Z.re| < c.im / 4)
    (hPc : ContinuousOn P (Set.Ici T)) (htT : T + 1 ≤ t₀)
    (hPinv : ∀ t ∈ Set.Ici T, F (P t) = P (t + 1))
    (hPt : ∀ t : ℝ, t₀ ≤ t → (P t).re < X₁)
    (hM : ∀ h ∈ Set.Icc ((P t₀).im) ((P t₀).im + (2 * Real.pi + 1)), M ≤ leftCross P t₀ h)
    {W : ℂ} (hW : W ∈ barrierRegion P X t₀) (him : (P t₀).im + 1 ≤ W.im)
    (hleft : ∀ W' ∈ pathTail P t₀, W'.im = W.im → W.re < W'.re) :
    W ∈ connectedComponentIn (barrierRegion P X t₀) (barrierBase P M t₀) := by
  have hT : T ≤ t₀ := by linarith
  have hheight : ∀ Z : ℂ, Z.re < X₁ → Z.im + c.im / 2 ≤ (F Z).im := fun Z hZ => (hd Z hZ).1
  obtain ⟨⟨hWre, hWim⟩, hWnotin⟩ := hW
  -- a lower bound for the barrier's leftmost real part on the band `[Y, W.im]`
  obtain ⟨MZ, hMZ⟩ := leftCross_bddBelow_on_Icc (F := F) (P := P) (c := c) (T := T) (X₀ := X₁)
    (t₀ := t₀) hc_im hPc hT hheight hPinv hPt (a := (P t₀).im) (b := W.im) le_rfl
  -- the leftmost barrier point at a height, and the bound `leftCross h ≤ re W'`
  have hcross_le : ∀ h : ℝ, (P t₀).im ≤ h → ∀ W' ∈ pathTail P t₀, W'.im = h →
      leftCross P t₀ h ≤ W'.re := by
    intro h hh W' hW' hW'im
    obtain ⟨Wm, hWm, hWmim, hWmre, hWmmin⟩ := exists_barrier_min (F := F) (P := P) (c := c)
      (T := T) (X₀ := X₁) (t₀ := t₀) hc_im hPc hT hheight hPinv hPt hh
    rw [← hWmre]
    exact hWmmin W' hW' hW'im
  -- `M < X₁` (so that the base point is in the deep half plane)
  have hMX₁ : M < X₁ := by
    have h1 := hM ((P t₀).im + 1) ⟨by linarith, by linarith [Real.pi_pos]⟩
    obtain ⟨Wm, hWm, hWmim, hWmre, -⟩ := exists_barrier_min (F := F) (P := P) (c := c)
      (T := T) (X₀ := X₁) (t₀ := t₀) hc_im hPc hT hheight hPinv hPt (h := (P t₀).im + 1)
      (by linarith)
    have h2 : Wm.re < X₁ := by
      rw [pathTail] at hWm; obtain ⟨u, hu, rfl⟩ := hWm; exact hPt u hu
    rw [← hWmre] at h1; linarith
  have hMZlt : MZ < X₁ := by
    have h1 : MZ ≤ leftCross P t₀ W.im := hMZ W.im ⟨by linarith, le_rfl⟩
    obtain ⟨Wm, hWm, hWmim, hWmre, -⟩ := exists_barrier_min (F := F) (P := P) (c := c)
      (T := T) (X₀ := X₁) (t₀ := t₀) hc_im hPc hT hheight hPinv hPt (h := W.im) (by linarith)
    have h2 : Wm.re < X₁ := by
      rw [pathTail] at hWm; obtain ⟨u, hu, rfl⟩ := hWm; exact hPt u hu
    rw [← hWmre] at h1; linarith
  set N : ℝ := min MZ (min W.re (M - 1)) - 1 with hN
  have hNlt : N < MZ := by rw [hN]; linarith [min_le_left MZ (min W.re (M - 1))]
  have hNleW : N ≤ W.re := by
    rw [hN]; linarith [le_trans (min_le_right MZ _) (min_le_left W.re (M - 1))]
  have hNleM : N ≤ M - 1 := by
    rw [hN]; linarith [le_trans (min_le_right MZ _) (min_le_right W.re (M - 1))]
  have hNltX : N < X := lt_of_lt_of_le (lt_trans hNlt (lt_of_lt_of_le hMZlt (le_of_lt hX₁X))) le_rfl
  -- the three segments
  set s1 : Set ℂ := {w : ℂ | w.im = W.im ∧ N ≤ w.re ∧ w.re ≤ W.re} with hs1
  set s2 : Set ℂ := {w : ℂ | w.re = N ∧ (P t₀).im + 1 ≤ w.im ∧ w.im ≤ W.im} with hs2
  set s3 : Set ℂ := {w : ℂ | w.im = (P t₀).im + 1 ∧ N ≤ w.re ∧ w.re ≤ M - 1} with hs3
  have hpre1 : IsPreconnected s1 := by
    have heq : s1 = (fun y : ℝ => (y : ℂ) + (W.im : ℂ) * Complex.I) '' Set.Icc N W.re := by
      ext w; constructor
      · rintro ⟨hwim, hw1, hw2⟩
        refine ⟨w.re, ⟨hw1, hw2⟩, ?_⟩
        apply Complex.ext <;> simp [hwim]
      · rintro ⟨y, hy, rfl⟩
        refine ⟨by simp, by simpa using hy.1, by simpa using hy.2⟩
    rw [heq]; exact isPreconnected_Icc.image _ (by fun_prop)
  have hpre2 : IsPreconnected s2 := by
    have heq : s2 = (fun y : ℝ => (N : ℂ) + (y : ℂ) * Complex.I) ''
        Set.Icc ((P t₀).im + 1) W.im := by
      ext w; constructor
      · rintro ⟨hwre, hw1, hw2⟩
        refine ⟨w.im, ⟨hw1, hw2⟩, ?_⟩
        apply Complex.ext <;> simp [hwre]
      · rintro ⟨y, hy, rfl⟩
        refine ⟨by simp, by simpa using hy.1, by simpa using hy.2⟩
    rw [heq]; exact isPreconnected_Icc.image _ (by fun_prop)
  have hpre3 : IsPreconnected s3 := by
    have heq : s3 = (fun y : ℝ => (y : ℂ) + (((P t₀).im + 1 : ℝ) : ℂ) * Complex.I) ''
        Set.Icc N (M - 1) := by
      ext w; constructor
      · rintro ⟨hwim, hw1, hw2⟩
        refine ⟨w.re, ⟨hw1, hw2⟩, ?_⟩
        apply Complex.ext <;> simp [hwim]
      · rintro ⟨y, hy, rfl⟩
        refine ⟨by simp, by simpa using hy.1, by simpa using hy.2⟩
    rw [heq]; exact isPreconnected_Icc.image _ (by fun_prop)
  -- membership in the region
  have hs1sub : s1 ⊆ barrierRegion P X t₀ := by
    intro w hw
    obtain ⟨hwim, hw1, hw2⟩ := hw
    refine ⟨⟨lt_of_le_of_lt hw2 hWre, by rw [hwim]; exact hWim⟩, ?_⟩
    intro hwB
    rw [pathTail] at hwB
    obtain ⟨u, hu, hueq⟩ := hwB
    exact absurd (hleft (P u) ⟨u, hu, rfl⟩ (by rw [hueq]; exact hwim)) (not_lt.mpr (by
      have : (P u).re = w.re := congrArg Complex.re hueq
      linarith [this, hw2]))
  have hs2sub : s2 ⊆ barrierRegion P X t₀ := by
    intro w hw
    obtain ⟨hwre, hw1, hw2⟩ := hw
    have hband : w.im ∈ Set.Icc ((P t₀).im) W.im := ⟨by linarith, hw2⟩
    refine ⟨⟨by rw [hwre]; exact hNltX, by linarith⟩, ?_⟩
    intro hwB
    rw [pathTail] at hwB
    obtain ⟨u, hu, hueq⟩ := hwB
    have h1 : leftCross P t₀ w.im ≤ w.re := by
      have h1' := hcross_le w.im (by linarith) (P u) ⟨u, hu, rfl⟩ (by rw [hueq])
      rwa [hueq] at h1'
    have h2 : MZ ≤ leftCross P t₀ w.im := hMZ w.im hband
    linarith [hNlt, h2, h1, hwre]
  have hs3sub : s3 ⊆ barrierRegion P X t₀ := by
    intro w hw
    obtain ⟨hwim, hw1, hw2⟩ := hw
    have hband : w.im ∈ Set.Icc ((P t₀).im) ((P t₀).im + (2 * Real.pi + 1)) :=
      ⟨by rw [hwim]; linarith, by rw [hwim]; linarith [Real.pi_pos]⟩
    refine ⟨⟨by linarith [hw2, hMX₁, hX₁X], by rw [hwim]; linarith⟩, ?_⟩
    intro hwB
    rw [pathTail] at hwB
    obtain ⟨u, hu, hueq⟩ := hwB
    have h1 : leftCross P t₀ w.im ≤ w.re := by
      have h1' := hcross_le w.im (by rw [hwim]; linarith) (P u) ⟨u, hu, rfl⟩ (by rw [hueq])
      rwa [hueq] at h1'
    have h2 : M ≤ leftCross P t₀ w.im := hM w.im hband
    linarith [h2, h1, hw2]
  -- preconnectedness of the union
  have hmem12 : (s1 ∩ s2).Nonempty := by
    refine ⟨(⟨N, W.im⟩ : ℂ), ⟨?_, ?_⟩⟩
    · exact ⟨rfl, le_rfl, hNleW⟩
    · exact ⟨rfl, him, le_rfl⟩
  have hmem23 : ((s1 ∪ s2) ∩ s3).Nonempty := by
    refine ⟨(⟨N, (P t₀).im + 1⟩ : ℂ), ⟨?_, ?_⟩⟩
    · exact Or.inr ⟨rfl, le_rfl, him⟩
    · exact ⟨rfl, le_rfl, hNleM⟩
  have hpre12 : IsPreconnected (s1 ∪ s2) := IsPreconnected.union' hmem12 hpre1 hpre2
  have hpre123 : IsPreconnected (s1 ∪ s2 ∪ s3) := IsPreconnected.union' hmem23 hpre12 hpre3
  have hsub : s1 ∪ s2 ∪ s3 ⊆ barrierRegion P X t₀ :=
    fun w hw => hw.elim (fun h => h.elim (fun h1 => hs1sub h1) (fun h2 => hs2sub h2))
      (fun h3 => hs3sub h3)
  have hmemW : W ∈ s1 ∪ s2 ∪ s3 := Or.inl (Or.inl ⟨rfl, hNleW, le_rfl⟩)
  have hmemB : barrierBase P M t₀ ∈ s1 ∪ s2 ∪ s3 :=
    Or.inr ⟨rfl, hNleM, by simp [barrierBase]⟩
  exact hpre123.subset_connectedComponentIn hmemB hsub hmemW

end Work.LandLeaves.Snail

namespace Work.LandLeaves.Snail

theorem existsInvariantRegionCorrected {F : ℂ → ℂ} {X : ℝ} {c : ℂ} {P : ℝ → ℂ} {T : ℝ}
    (hc_re : c.re = 0) (hc_im : 0 < c.im)
    (hdiff : DifferentiableOn ℂ F {Z : ℂ | Z.re < X})
    (hinj : Set.InjOn F {Z : ℂ | Z.re < X})
    (hper : ∀ Z : ℂ, Z.re < X → F (Z + 2 * (Real.pi : ℂ) * Complex.I) = F Z + 2 * (Real.pi : ℂ) * Complex.I)
    (hdrift : Filter.Tendsto (fun Z : ℂ => F Z - Z)
      (Filter.comap Complex.re Filter.atBot) (nhds c))
    (hPc : ContinuousOn P (Set.Ici T))
    (hPX : ∀ t ∈ Set.Ici T, (P t).re < X)
    (hPre : Filter.Tendsto (fun t : ℝ => (P t).re) Filter.atTop Filter.atBot)
    (hPim : Filter.Tendsto (fun t : ℝ => (P t).im) Filter.atTop Filter.atTop)
    (hPinv : ∀ t ∈ Set.Ici T, F (P t) = P (t + 1)) :
    ∃ V₀ : Set ℂ, IsOpen V₀ ∧ V₀ ⊆ {Z : ℂ | Z.re < X} ∧ Set.MapsTo F V₀ V₀ ∧
      (∀ Z ∈ V₀, Filter.Tendsto (fun n : ℕ => ((F^[n]) Z).re) Filter.atTop Filter.atBot) ∧
      (∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (0 : ℂ) ρ ⊆ Complex.exp '' V₀ ∪ {0}) := by
  classical
  -- ## the drift threshold
  obtain ⟨Xa, hXaX, hdXa⟩ : ∃ Xa : ℝ, Xa < X ∧ ∀ Z : ℂ, Z.re < Xa →
      |(F Z).re - Z.re| < c.im / 4 ∧ |(F Z).im - Z.im - c.im| < c.im / 4 ∧ (F Z).re < X := by
    have hc4 : 0 < c.im / 4 := by linarith
    have hε : 0 < min (c.im / 4) 1 := lt_min hc4 one_pos
    have h : ∀ᶠ Z in Filter.comap Complex.re Filter.atBot,
        F Z - Z ∈ Metric.ball c (min (c.im / 4) 1) :=
      hdrift.eventually (Metric.ball_mem_nhds c hε)
    rw [Filter.eventually_comap] at h
    rw [Filter.eventually_atBot] at h
    obtain ⟨β, hβ⟩ := h
    refine ⟨min β (X - min (c.im / 4) 1),
      lt_of_le_of_lt (min_le_right _ _) (by linarith), fun Z hZ => ?_⟩
    have hZβ : Z.re < β := lt_of_lt_of_le hZ (min_le_left _ _)
    have hZX : Z.re < X - min (c.im / 4) 1 := lt_of_lt_of_le hZ (min_le_right _ _)
    have hb := hβ Z.re (le_of_lt hZβ) Z rfl
    rw [Metric.mem_ball, dist_eq_norm] at hb
    have hre : |(F Z - Z - c).re| < min (c.im / 4) 1 :=
      lt_of_le_of_lt (Complex.abs_re_le_norm _) hb
    have him : |(F Z - Z - c).im| < min (c.im / 4) 1 :=
      lt_of_le_of_lt (Complex.abs_im_le_norm _) hb
    have e1 : (F Z - Z - c).re = (F Z).re - Z.re - c.re := by simp
    have e2 : (F Z - Z - c).im = (F Z).im - Z.im - c.im := by simp
    rw [e1, hc_re, sub_zero] at hre
    rw [e2] at him
    refine ⟨lt_of_lt_of_le hre (min_le_left _ _), lt_of_lt_of_le him (min_le_left _ _), ?_⟩
    have hm3 : (F Z).re - Z.re < min (c.im / 4) 1 := (abs_lt.mp hre).2
    linarith [min_le_left (c.im / 4) 1]
  -- ## positivity of the derivative on a (possibly deeper) half plane
  obtain ⟨Xb, hXbX, hmono⟩ := deriv_re_pos_deep (F := F) (X := X) (c := c) hdiff (by
    intro ε hε
    have h : ∀ᶠ Z in Filter.comap Complex.re Filter.atBot, F Z - Z ∈ Metric.ball c ε :=
      hdrift.eventually (Metric.ball_mem_nhds c hε)
    rw [Filter.eventually_comap] at h
    rw [Filter.eventually_atBot] at h
    obtain ⟨β, hβ⟩ := h
    refine ⟨min β (X - 1), lt_of_le_of_lt (min_le_right _ _) (by linarith), fun Z hZ => ?_⟩
    have : Z.re < β := lt_of_lt_of_le hZ (min_le_left _ _)
    have := hβ Z.re (le_of_lt this) Z rfl
    simpa [Metric.mem_ball, dist_eq_norm] using this)
  set Xo : ℝ := min Xa Xb with hXo
  have hXoX : Xo < X := by rw [hXo]; exact lt_of_le_of_lt (min_le_left _ _) hXaX
  have hdo : ∀ Z : ℂ, Z.re < Xo →
      (F Z).re < X ∧ |(F Z).re - Z.re| < c.im / 4 ∧ |(F Z).im - Z.im - c.im| < c.im / 4 :=
    fun Z hZ => by
      obtain ⟨h1, h2, h3⟩ := hdXa Z (lt_of_lt_of_le hZ (min_le_left _ _))
      exact ⟨h3, h1, h2⟩
  have hmonoO : ∀ Z : ℂ, Z.re < Xo → 0 < (deriv F Z).re := fun Z hZ =>
    hmono Z (lt_of_lt_of_le hZ (min_le_right _ _))
  have hheightO : ∀ Z : ℂ, Z.re < Xo → Z.im + c.im / 2 ≤ (F Z).im := by
    intro Z hZ
    have h := (hdo Z hZ).2.2
    have := (abs_lt.mp h).1
    linarith
  -- ## the tail of the path in the deep half plane, and a "record" time `t₀`
  obtain ⟨S, hS⟩ : ∃ S : ℝ, ∀ t : ℝ, S ≤ t → (P t).re < Xo := by
    have h : ∀ᶠ t : ℝ in Filter.atTop, (P t).re ≤ Xo - 1 :=
      hPre.eventually (Filter.mem_atBot (Xo - 1))
    rw [Filter.eventually_atTop] at h
    exact ⟨h.choose, fun t ht => lt_of_le_of_lt (h.choose_spec t ht) (by linarith)⟩
  have hTS : T + 1 ≤ max (T + 1) S := le_max_left _ _
  have hcontUB : ContinuousOn (fun t : ℝ => (P t).im) (Set.Icc (T + 1) (max (T + 2) S)) :=
    Complex.continuous_im.comp_continuousOn
      (hPc.mono (fun t ht => le_trans (by linarith) ht.1))
  obtain ⟨x₀, hx₀mem, hx₀max⟩ := isCompact_Icc.exists_isMaxOn
    (⟨T + 1, le_rfl, by linarith [le_max_left (T + 2) S, le_max_right (T + 2) S]⟩ :
      (Set.Icc (T + 1) (max (T + 2) S)).Nonempty) hcontUB
  obtain ⟨t₁, ht₁ge, ht₁gt⟩ : ∃ t₁ : ℝ, T + 1 ≤ t₁ ∧ (P x₀).im < (P t₁).im := by
    have h : ∀ᶠ t : ℝ in Filter.atTop, (P x₀).im < (P t).im :=
      hPim.eventually (Filter.eventually_gt_atTop ((P x₀).im))
    rw [Filter.eventually_atTop] at h
    obtain ⟨s, hs⟩ := h
    exact ⟨max s (T + 1), le_max_right _ _, hs _ (le_max_left _ _)⟩
  have hcontUB' : ContinuousOn (fun t : ℝ => (P t).im) (Set.Icc (T + 1) t₁) :=
    Complex.continuous_im.comp_continuousOn (hPc.mono (fun t ht => le_trans (by linarith) ht.1))
  obtain ⟨t₀, ht₀mem, ht₀max'⟩ := isCompact_Icc.exists_isMaxOn
    (⟨T + 1, le_rfl, ht₁ge⟩ : (Set.Icc (T + 1) t₁).Nonempty) hcontUB'
  have ht₀ge : T + 1 ≤ t₀ := ht₀mem.1
  have ht₀le : t₀ ≤ t₁ := ht₀mem.2
  have hbig : max (T + 2) S < t₀ := by
    by_contra hcon
    rw [not_lt] at hcon
    have h1 : t₀ ∈ Set.Icc (T + 1) (max (T + 2) S) := ⟨ht₀ge, hcon⟩
    have h2 : (P t₀).im ≤ (P x₀).im := hx₀max h1
    have h3 : (P t₀).im ≥ (P t₁).im := ht₀max' ⟨ht₁ge, le_rfl⟩
    linarith [ht₁gt]
  have hto : ∀ t : ℝ, t₀ ≤ t → (P t).re < Xo := fun t ht =>
    hS t (le_trans (le_trans (le_max_right (T + 2) S) (le_of_lt hbig)) ht)
  have hhook : ∀ t ∈ Set.Icc (t₀ - 1) t₀, (P t).im ≤ (P t₀).im := by
    rintro t ⟨ht1, ht2⟩
    exact ht₀max' ⟨by linarith [le_max_left (T + 2) S, le_of_lt hbig, ht1],
      le_trans ht2 ht₀le⟩
  have hTt₀ : T ≤ t₀ := by linarith
  -- ## the leftCross lower bound on a band wide enough for the reader
  obtain ⟨M, hM⟩ := leftCross_bddBelow_on_Icc (F := F) (P := P) (c := c) (T := T) (X₀ := Xo)
    (t₀ := t₀) hc_im hPc hTt₀ hheightO hPinv hto
    (a := (P t₀).im) (b := (P t₀).im + (2 * Real.pi + 1 + (5 * c.im / 4 + 1))) le_rfl
  have hMs : ∀ h ∈ Set.Icc ((P t₀).im) ((P t₀).im + (2 * Real.pi + 1)),
      M ≤ leftCross P t₀ h := fun h hh =>
    hM h ⟨hh.1, by linarith [hh.2]⟩
  have hcross_le : ∀ h : ℝ, (P t₀).im ≤ h → ∀ W ∈ pathTail P t₀, W.im = h →
      leftCross P t₀ h ≤ W.re := fun h hh W hW him =>
    leftCross_le_of_mem hc_im hPc hTt₀ hheightO hPinv hto hh hW him
  -- ## `M < Xo`
  have hMY : M < Xo := by
    have h1 := hMs ((P t₀).im + 1) ⟨by linarith, by linarith [Real.pi_pos]⟩
    obtain ⟨Wm, hWm, hWmim, hWmre, -⟩ := exists_barrier_min (F := F) (P := P) (c := c)
      (T := T) (X₀ := Xo) (t₀ := t₀) hc_im hPc hTt₀ hheightO hPinv hto (h := (P t₀).im + 1)
      (by linarith)
    have h2 : Wm.re < Xo := by
      rw [pathTail] at hWm; obtain ⟨u, hu, rfl⟩ := hWm; exact hto u hu
    rw [← hWmre] at h1; linarith
  -- ## the ambient region, the base point and the component
  set Vc : Set ℂ := connectedComponentIn (barrierRegion P X t₀) (barrierBase P M t₀) with hVc
  have hVcopen : IsOpen Vc := by
    rw [hVc]
    refine IsOpen.connectedComponentIn ?_
    rw [barrierRegion]
    have h1 : IsOpen {Z : ℂ | Z.re < X} := isOpen_lt Complex.continuous_re continuous_const
    have h2 : IsOpen {Z : ℂ | (P t₀).im < Z.im} :=
      isOpen_lt continuous_const Complex.continuous_im
    have hset : {Z : ℂ | Z.re < X ∧ (P t₀).im < Z.im}
        = {Z : ℂ | Z.re < X} ∩ {Z : ℂ | (P t₀).im < Z.im} := by ext Z; simp
    have hcl : IsClosed (pathTail P t₀) :=
      pathTail_isClosed (F := F) (P := P) (c := c) (T := T) (X₀ := Xo) (t₀ := t₀)
        hc_im hPc hTt₀ hheightO hPinv hto
    rw [hset]
    exact (h1.inter h2).sdiff hcl
  have huniv : ∀ Z ∈ Vc, Z.re < Xo := fun Z hZ =>
    component_re_lt hc_re hc_im hXoX hdiff hinj hper hdo hmonoO hPc (by linarith) hPinv hto hPre hMs Z hZ
  have hVcreg : ∀ Z ∈ Vc, Z ∈ barrierRegion P X t₀ := fun Z hZ =>
    connectedComponentIn_subset _ _ hZ
  -- ## `F` maps `Vc` into the region (using the hook hypothesis)
  have hFreg : ∀ Z ∈ Vc, F Z ∈ barrierRegion P X t₀ := by
    intro Z hZ
    obtain ⟨⟨hZre, hZim⟩, hZnotin⟩ := hVcreg Z hZ
    have hZXo : Z.re < Xo := huniv Z hZ
    obtain ⟨h1, h2, h3⟩ := hdo Z hZXo
    have ht₀ge2 : T + 1 ≤ t₀ := by linarith [le_max_left (T + 2) S, le_of_lt hbig]
    refine ⟨⟨h1, by linarith [hZim, (abs_lt.mp h3).1]⟩, ?_⟩
    intro hFγ
    rw [pathTail] at hFγ
    obtain ⟨s, hs, hseq⟩ := hFγ
    have hst : t₀ ≤ s := hs
    have hs1T : T ≤ s - 1 := by linarith [ht₀ge2, hst]
    have hPs : F (P (s - 1)) = P (s - 1 + 1) := hPinv (s - 1) hs1T
    have hFs : F Z = F (P (s - 1)) := by rw [hseq.symm, hPs]; congr 1; ring
    have heq : Z = P (s - 1) := hinj hZre (hPX (s - 1) hs1T) hFs
    by_cases hsge : t₀ ≤ s - 1
    · exact hZnotin ⟨s - 1, hsge, heq.symm⟩
    · have hslt : s - 1 < t₀ := not_le.mp hsge
      have himZ : (P (s - 1)).im = Z.im := by rw [← heq]
      have hle := hhook (s - 1) ⟨by linarith [hst], le_of_lt hslt⟩
      rw [himZ] at hle
      linarith [hZim]
  -- ## the witness: a deep point of the strip whose image is again in the component
  set K : ℝ := c.im / 4 + 1 with hK
  set Zw : ℂ := ⟨M - 1 - K, (P t₀).im + 1⟩ with hZw
  have hZwreg : Zw ∈ barrierRegion P X t₀ := by
    have him : (P t₀).im + 1 = Zw.im := rfl
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hZw]; simp only; linarith [hMY, hXoX]
    · rw [hZw]; simp only; linarith
    · intro hmem
      rw [pathTail] at hmem
      obtain ⟨u, hu, hueq⟩ := hmem
      have h1 : leftCross P t₀ ((P t₀).im + 1) ≤ (P u).re :=
        hcross_le ((P t₀).im + 1) (by linarith) (P u) ⟨u, hu, rfl⟩ (by rw [hueq])
      have h2 : M ≤ leftCross P t₀ ((P t₀).im + 1) :=
        hMs ((P t₀).im + 1) ⟨by linarith, by linarith [Real.pi_pos]⟩
      have h3 : (P u).re = M - 1 - K := congrArg Complex.re hueq
      linarith [h1, h2, h3, hK]
  have hZwleft : ∀ W' ∈ pathTail P t₀, W'.im = Zw.im → Zw.re < W'.re := by
    intro W' hW' him
    have h1 : leftCross P t₀ Zw.im ≤ W'.re :=
      hcross_le Zw.im (by rw [hZw]; simp only; linarith) W' hW' him
    have h2 : M ≤ leftCross P t₀ Zw.im :=
      hMs Zw.im ⟨by rw [hZw]; simp only; linarith,
        by rw [hZw]; simp only; linarith [Real.pi_pos]⟩
    have h3 : Zw.re = M - 1 - K := rfl
    linarith [h1, h2, h3, hK]
  have ht₀ge2 : T + 1 ≤ t₀ := by linarith [le_max_left (T + 2) S, le_of_lt hbig]
  have hdo' : ∀ Z : ℂ, Z.re < Xo → Z.im + c.im / 2 ≤ (F Z).im ∧ (F Z).re < X ∧
      |(F Z).re - Z.re| < c.im / 4 := fun Z hZ =>
    ⟨by linarith [(abs_lt.mp (hdo Z hZ).2.2).1], (hdo Z hZ).1, (hdo Z hZ).2.1⟩
  have hZwVc : Zw ∈ Vc :=
    mem_component_of_left hc_im hXoX hdo' hPc ht₀ge2 hPinv hto hMs hZwreg
      (by rw [hZw]) hZwleft
  have hFZwreg : F Zw ∈ barrierRegion P X t₀ := hFreg Zw hZwVc
  have hFZwleft : ∀ W' ∈ pathTail P t₀, W'.im = (F Zw).im → (F Zw).re < W'.re := by
    intro W' hW' him
    have hZW : Zw.re < Xo := huniv Zw hZwVc
    obtain ⟨h1, h2, h3⟩ := hdo Zw hZW
    have himb : (P t₀).im ≤ (F Zw).im := by
      rw [hZw] at h3; simp only at h3; linarith [(abs_lt.mp h3).1]
    have hle := hcross_le (F Zw).im himb W' hW' him
    have hband : (F Zw).im ≤ (P t₀).im + (2 * Real.pi + 1 + (5 * c.im / 4 + 1)) := by
      rw [hZw] at h3; simp only at h3
      linarith [(abs_lt.mp h3).2, Real.pi_pos]
    have hMband : M ≤ leftCross P t₀ (F Zw).im := hM (F Zw).im ⟨himb, hband⟩
    have hre : (F Zw).re < M - 1 - K + c.im / 4 := by
      rw [hZw] at h2; simp only at h2
      linarith [(abs_lt.mp h2).2]
    linarith [hZw, hK, hre, hMband, hle]
  have hFZwVc : F Zw ∈ Vc :=
    mem_component_of_left hc_im hXoX hdo' hPc ht₀ge2 hPinv hto hMs hFZwreg
      (by
        have hZW : Zw.re < Xo := huniv Zw hZwVc
        obtain ⟨-, -, h3⟩ := hdo Zw hZW
        rw [hZw] at h3; simp only at h3
        linarith [(abs_lt.mp h3).1])
      hFZwleft
  -- ## `F` maps the component into itself
  have hmapsTo : Set.MapsTo F Vc Vc := by
    have hpre : IsPreconnected (F '' Vc) := by
      rw [hVc]
      exact (isPreconnected_connectedComponentIn (F := barrierRegion P X t₀)
        (x := barrierBase P M t₀)).image F
        (hdiff.continuousOn.mono (fun z hz => (connectedComponentIn_subset _ _ hz).1.1))
    have hmem : F Zw ∈ F '' Vc ∩ Vc := ⟨⟨Zw, hZwVc, rfl⟩, hFZwVc⟩
    have hsub : F '' Vc ⊆ connectedComponentIn (barrierRegion P X t₀) (F Zw) :=
      hpre.subset_connectedComponentIn hmem.1 (fun z hz => by
        obtain ⟨y, hy, rfl⟩ := hz
        exact hFreg y hy)
    intro Z hZ
    have h1 : F Z ∈ connectedComponentIn (barrierRegion P X t₀) (F Zw) := hsub ⟨Z, hZ, rfl⟩
    have h2 : connectedComponentIn (barrierRegion P X t₀) (F Zw)
        = connectedComponentIn (barrierRegion P X t₀) (barrierBase P M t₀) :=
      (connectedComponentIn_eq hmem.2).symm
    rw [h2] at h1
    exact h1
  -- ## the drift
  have hSep : ∀ Z ∈ Vc, ∃ W ∈ pathTail P t₀, W.im = Z.im ∧ Z.re < W.re :=
    fun Z hZ => existsBarrierRight_of_re_lt hXoX (fun W hW => huniv W hW) hZ
  have hdrift' : ∀ Z ∈ Vc, Filter.Tendsto (fun n : ℕ => ((F^[n]) Z).re) Filter.atTop Filter.atBot := by
    intro Z hZ
    have hheight : ∀ Z : ℂ, Z.re < Xo → Z.im + c.im / 2 ≤ (F Z).im := hheightO
    have hdich : (∀ n : ℕ, (F^[n]) Z ∈ Vc) ∨ ∃ n : ℕ, (F^[n]) Z ∈ pathTail P t₀ := by
      by_cases hex : ∃ n : ℕ, (F^[n]) Z ∈ pathTail P t₀
      · exact Or.inr hex
      · push Not at hex
        refine Or.inl (fun n => ?_)
        induction n with
        | zero => exact hZ
        | succ k ih =>
          have h := hmapsTo ih
          · rw [Function.iterate_succ_apply']; exact h
    rcases hdich with hall | ⟨n, hn⟩
    · have hre₁ : ∀ k : ℕ, ((F^[k]) Z).re < Xo := fun k => huniv _ (hall k)
      have him : ∀ k : ℕ, Z.im + k * (c.im / 2) ≤ ((F^[k]) Z).im := im_iterate_ge hheight hre₁
      have hc2 : 0 < c.im / 2 := by linarith
      rw [Filter.tendsto_atBot]
      intro b
      obtain ⟨H, hH⟩ := exists_height_of_barrier_re_lt hPc hTt₀ hPre b
      obtain ⟨N, hN⟩ : ∃ N : ℕ, H < Z.im + N * (c.im / 2) := by
        obtain ⟨N, hN⟩ := exists_nat_gt ((H - Z.im) / (c.im / 2))
        exact ⟨N, by rw [div_lt_iff₀ hc2] at hN; linarith⟩
      rw [Filter.eventually_atTop]
      refine ⟨N, fun k hk => ?_⟩
      have hkH : H < ((F^[k]) Z).im := by
        have hle : Z.im + N * (c.im / 2) ≤ Z.im + k * (c.im / 2) := by
          have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
          nlinarith [hc2]
        linarith [him k]
      obtain ⟨W', hW', hW'im, hW're⟩ := hSep ((F^[k]) Z) (hall k)
      have hW'b : W'.re < b := hH W' hW' (by rw [hW'im]; exact hkH)
      linarith
    · rw [pathTail] at hn
      obtain ⟨u, hu, hPueq⟩ := hn
      have hstep : ∀ j : ℕ, (F^[n + j]) Z = P (u + (j : ℝ)) := by
        intro j
        induction j with
        | zero => simpa using hPueq.symm
        | succ i ih =>
          rw [Nat.add_succ, Function.iterate_succ_apply', ih]
          rw [hPinv (u + (i : ℝ))
            (le_trans hTt₀ (le_trans hu (by have h0 : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i; linarith)))]
          congr 1
          push_cast
          ring
      have hmap : Filter.Tendsto (fun j : ℕ => u + (j : ℝ)) Filter.atTop Filter.atTop := by
        rw [Filter.tendsto_atTop_atTop]
        intro s
        refine ⟨Nat.ceil (s - u), fun j hj => ?_⟩
        have h1 : s - u ≤ (j : ℝ) := le_trans (Nat.le_ceil (s - u)) (by exact_mod_cast hj)
        linarith
      have htail : Filter.Tendsto (fun j : ℕ => (P (u + (j : ℝ))).re) Filter.atTop Filter.atBot :=
        hPre.comp hmap
      have hsub : Filter.Tendsto (fun m : ℕ => m - n) Filter.atTop Filter.atTop := by
        rw [Filter.tendsto_atTop_atTop]
        exact fun s => ⟨s + n, fun m hm => by omega⟩
      have heq : (fun m : ℕ => (P (u + ((m - n : ℕ) : ℝ))).re) =ᶠ[Filter.atTop]
          (fun m : ℕ => ((F^[m]) Z).re) := by
        filter_upwards [Filter.eventually_ge_atTop n] with m hm
        obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = n + j := ⟨m - n, (Nat.add_sub_of_le hm).symm⟩
        rw [hstep j, Nat.add_sub_cancel_left]
      exact (htail.comp hsub).congr' heq
  -- ## the ball clause
  have hbase_strip : barrierBase P M t₀ ∈ strip M ((P t₀).im) := by
    rw [barrierBase]
    refine mem_strip.mpr ⟨?_, ?_, ?_⟩
    · simp only; linarith
    · simp only; linarith
    · simp only; linarith [Real.pi_pos]
  have hstrip_sub : strip M ((P t₀).im) ⊆ barrierRegion P X t₀ := by
    intro Z hZ
    obtain ⟨h1, h2, h3⟩ := mem_strip.mp hZ
    have hband : Z.im ∈ Set.Icc ((P t₀).im) ((P t₀).im + (2 * Real.pi + 1)) :=
      ⟨le_of_lt h2, by linarith [h3, Real.pi_pos]⟩
    refine ⟨⟨by linarith [h1, hMY, hXoX], h2⟩, ?_⟩
    intro hmem
    rw [pathTail] at hmem
    obtain ⟨u, hu, hueq⟩ := hmem
    have h1' : leftCross P t₀ Z.im ≤ (P u).re :=
      hcross_le Z.im (le_of_lt h2) (P u) ⟨u, hu, rfl⟩ (by rw [hueq])
    have h2' : M ≤ leftCross P t₀ Z.im := hMs Z.im hband
    have h3' : (P u).re = Z.re := congrArg Complex.re hueq
    linarith [h1', h2', h3', h1]
  have hstripVc : strip M ((P t₀).im) ⊆ Vc := by
    rw [hVc]
    exact (convex_strip M ((P t₀).im)).isPreconnected.subset_connectedComponentIn
      hbase_strip hstrip_sub
  refine ⟨Vc, hVcopen, (fun Z hZ => by
      have := hVcreg Z hZ
      exact this.1.1), hmapsTo, hdrift', ?_⟩
  refine ⟨Real.exp M, Real.exp_pos M, ?_⟩
  intro w hw
  rw [Metric.mem_ball, dist_zero_right] at hw
  rcases eq_or_ne w 0 with rfl | hw0
  · exact Or.inr rfl
  · left
    have : w ∈ {w : ℂ | w ≠ 0 ∧ ‖w‖ < Real.exp M} := ⟨hw0, hw⟩
    rw [← exp_image_strip] at this
    obtain ⟨Z, hZ, hZw⟩ := this
    exact ⟨Z, hstripVc hZ, hZw⟩

end Work.LandLeaves.Snail
