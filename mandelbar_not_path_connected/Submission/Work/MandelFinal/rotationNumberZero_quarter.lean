import Mathlib
import Submission.Work.LandLeaves.All
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq
import Submission.Work.LANDCL.Defs
import Submission.Work.LANDCL.Quarter.isParabolic_one_eq_half
import Submission.Work.LANDCL.Quarter.isParabolic_quarter_half
import Submission.Work.LANDCL.Quarter.not_periodicAngle_two
import Submission.Work.FSeed.Rays.landsAt_periodic
import Submission.Work.ParamRays.MbDefs
import Submission.Work.MandelFinal.Quarter.landsAt_quarter_zero_half
import Submission.Work.MandelFinal.Quarter.tsq_quarter_localModel
import Submission.Work.MandelFinal.Quarter.angleInjective_quarter
import Submission.Work.MandelFinal.Quarter.ccBet_angDouble_two_quarter

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MandelFinal

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

/-! ## The angle arithmetic of the second return map `θ ↦ Int.fract (4 θ)` -/

/-- The two-fold angle doubling is multiplication by `4` modulo `1`. -/
theorem angDouble_two_eq (θ : ℝ) :
    (Work.Landing.angDouble)^[2] θ = Int.fract (4 * θ) := by
  have h := Work.LandLeaves.angDouble_iterate_two_mul (k := 1) (by norm_num) θ
  simpa using h

theorem fract_four_eq_sub_floor (t : ℝ) :
    Int.fract (4 * t) = 4 * t - ((⌊4 * t⌋ : ℤ) : ℝ) := by
  have := Int.self_sub_fract (4 * t); linarith

theorem floor_four_eq_zero {t : ℝ} (h1 : 0 < t) (h2 : t < 1 / 4) : ⌊4 * t⌋ = 0 := by
  rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith

theorem floor_four_eq_one {t : ℝ} (h1 : 1 / 4 < t) (h2 : t < 1 / 2) : ⌊4 * t⌋ = 1 := by
  rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith

theorem floor_four_eq_two {t : ℝ} (h1 : 1 / 2 < t) (h2 : t < 3 / 4) : ⌊4 * t⌋ = 2 := by
  rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith

theorem floor_four_eq_three {t : ℝ} (h1 : 3 / 4 < t) (h2 : t < 1) : ⌊4 * t⌋ = 3 := by
  rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith

/-- **The fixed points of `θ ↦ Int.fract (4 θ)` on `[0,1)` are `0`, `1/3`, `2/3`.** -/
theorem fract_four_eq_self_iff {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    Int.fract (4 * t) = t ↔ t = 0 ∨ t = 1 / 3 ∨ t = 2 / 3 := by
  constructor
  · intro h
    rw [Int.fract_eq_iff] at h
    obtain ⟨-, -, m, hm⟩ := h
    have h3 : 3 * t = (m : ℝ) := by linarith [hm]
    have hm0 : m = 0 ∨ m = 1 ∨ m = 2 := by
      have hlt : (m : ℝ) < 3 := by linarith [h3, h1]
      have hge : (0 : ℝ) ≤ (m : ℝ) := by linarith [h3, h0]
      have hm0' : (0 : ℤ) ≤ m := by exact_mod_cast hge
      have hm3' : m < 3 := by exact_mod_cast hlt
      omega
    rcases hm0 with rfl | rfl | rfl
    · left; norm_num at h3 ⊢; linarith
    · right; left; norm_num at h3 ⊢; linarith
    · right; right; norm_num at h3 ⊢; linarith
  · rintro (rfl | rfl | rfl) <;> norm_num [Int.fract_eq_self]

/-- **No strictly monotone orbit of `θ ↦ Int.fract (4 θ)` inside `[0,1)`.**

The sequence is bounded and monotone, hence converges to some `L ∈ [0,1]`; writing
`4 * t n = t (n+1) + ⌊4 * t n⌋` with the integral part `⌊4 * t n⌋ ∈ {0,1,2,3}` in scope, the
integrality of `⌊4 * t n⌋` forces `3 * L = lim ⌊4 * t n⌋ ∈ {0,1,2,3}`; but near each of the
fixed points `0`, `1/3`, `2/3`, `1` the map `t ↦ Int.fract (4 t)` pushes strictly against the
assumed monotonicity. -/
theorem no_monotone_orbit_fract_four (t : ℕ → ℝ)
    (hrec : ∀ n : ℕ, t (n + 1) = Int.fract (4 * t n))
    (hrange : ∀ n : ℕ, 0 ≤ t n ∧ t n < 1) :
    ¬ ((∀ n : ℕ, t n < t (n + 1)) ∨ (∀ n : ℕ, t (n + 1) < t n)) := by
  have hkey : ∀ n : ℕ, 4 * t n = t (n + 1) + ((⌊4 * t n⌋ : ℤ) : ℝ) := by
    intro n
    have h := Int.self_sub_fract (4 * t n)
    rw [← hrec n] at h
    linarith
  have hkval : ∀ n : ℕ, ⌊4 * t n⌋ = 0 ∨ ⌊4 * t n⌋ = 1 ∨ ⌊4 * t n⌋ = 2 ∨ ⌊4 * t n⌋ = 3 := by
    intro n
    have ha : (0 : ℤ) ≤ ⌊4 * t n⌋ := Int.floor_nonneg.mpr (by linarith [(hrange n).1])
    have hb : ⌊4 * t n⌋ < 4 := by rw [Int.floor_lt]; push_cast; linarith [(hrange n).2]
    omega
  have hlim : ∀ (L : ℝ), Filter.Tendsto t Filter.atTop (nhds L) →
      ∃ N : ℕ, 3 * L = ((⌊4 * t N⌋ : ℤ) : ℝ) := by
    intro L hL
    have h1 : Filter.Tendsto (fun n : ℕ => 4 * t n - t (n + 1)) Filter.atTop
        (nhds (4 * L - L)) :=
      (hL.const_mul 4).sub (hL.comp (Filter.tendsto_add_atTop_nat 1))
    have h2 : (fun n : ℕ => 4 * t n - t (n + 1)) = fun n : ℕ => ((⌊4 * t n⌋ : ℤ) : ℝ) := by
      funext n; have := hkey n; push_cast; linarith
    have hkt : Filter.Tendsto (fun n : ℕ => ((⌊4 * t n⌋ : ℤ) : ℝ)) Filter.atTop
        (nhds (3 * L)) := by
      rw [h2] at h1
      convert h1 using 2
      ring
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hkt (1 / 2) (by norm_num)
    refine ⟨N, ?_⟩
    have hev : ∀ᶠ n in Filter.atTop,
        ((⌊4 * t n⌋ : ℤ) : ℝ) = ((⌊4 * t N⌋ : ℤ) : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have h1 := hN n hn
      have h2 := hN N le_rfl
      rw [Real.dist_eq] at h1 h2
      have h3 : |((⌊4 * t n⌋ : ℤ) : ℝ) - ((⌊4 * t N⌋ : ℤ) : ℝ)| < 1 := by
        rw [abs_lt] at h1 h2 ⊢; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      have h4 : |⌊4 * t n⌋ - ⌊4 * t N⌋| < 1 := by
        have h5 : |((⌊4 * t n⌋ - ⌊4 * t N⌋ : ℤ) : ℝ)| < 1 := by push_cast; linarith [h3]
        rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at h5
        exact_mod_cast h5
      have h6 : ⌊4 * t n⌋ - ⌊4 * t N⌋ = 0 := by
        have := abs_lt.mp h4
        omega
      show ((⌊4 * t n⌋ : ℤ) : ℝ) = ((⌊4 * t N⌋ : ℤ) : ℝ)
      rw [← sub_eq_zero, ← Int.cast_sub, h6, Int.cast_zero]
    exact tendsto_nhds_unique (hkt.congr' hev) tendsto_const_nhds
  intro h
  obtain ⟨L, hL⟩ : ∃ L : ℝ, Filter.Tendsto t Filter.atTop (nhds L) := by
    rcases h with h | h
    · exact ⟨_, tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => le_of_lt (h n))
        ⟨1, by rintro _ ⟨n, rfl⟩; exact le_of_lt (hrange n).2⟩⟩
    · exact ⟨_, tendsto_atTop_ciInf (antitone_nat_of_succ_le fun n => le_of_lt (h n))
        ⟨0, by rintro _ ⟨n, rfl⟩; exact (hrange n).1⟩⟩
  obtain ⟨N, hN⟩ := hlim L hL
  have hkv := hkval N
  rcases h with hinc | hdec
  · have hm : Monotone t := monotone_nat_of_le_succ fun n => le_of_lt (hinc n)
    have hle : ∀ n, t n ≤ L := fun n => hm.ge_of_tendsto hL n
    have hLt : ∀ n, t n < L := by
      intro n
      refine lt_of_le_of_ne (hle n) (fun heq => ?_)
      have h1 := hinc n; have h2 := hle (n + 1); linarith [heq, h1, h2]
    rcases hkv with hk | hk | hk | hk
    · have hL0 : L = 0 := by push_cast at hN; rw [hk] at hN; norm_num at hN; linarith
      have h1 := hle 1; rw [hL0] at h1
      have h3 := hinc 0
      linarith [(hrange 0).1]
    · have hL0 : L = 1 / 3 := by push_cast at hN; rw [hk] at hN; norm_num at hN; linarith
      obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hL (1 / 12) (by norm_num)
      have hM' := hM (M + 1) (by omega)
      rw [Real.dist_eq, hL0] at hM'
      have ha : 1 / 4 < t (M + 1) := by rw [abs_lt] at hM'; linarith [hM'.1]
      have hb : t (M + 1) < 1 / 3 := by have := hLt (M + 1); rw [hL0] at this; exact this
      have hstep : t (M + 2) < t (M + 1) := by
        rw [hrec (M + 1), fract_four_eq_sub_floor, floor_four_eq_one ha (by linarith)]
        norm_num
        linarith
      linarith [hinc (M + 1), hstep]
    · have hL0 : L = 2 / 3 := by push_cast at hN; rw [hk] at hN; norm_num at hN; linarith
      obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hL (1 / 12) (by norm_num)
      have hM' := hM (M + 1) (by omega)
      rw [Real.dist_eq, hL0] at hM'
      have ha : 1 / 2 < t (M + 1) := by rw [abs_lt] at hM'; linarith [hM'.1]
      have hb : t (M + 1) < 2 / 3 := by have := hLt (M + 1); rw [hL0] at this; exact this
      have hstep : t (M + 2) < t (M + 1) := by
        rw [hrec (M + 1), fract_four_eq_sub_floor, floor_four_eq_two ha (by linarith)]
        norm_num
        linarith
      linarith [hinc (M + 1), hstep]
    · have hL0 : L = 1 := by push_cast at hN; rw [hk] at hN; norm_num at hN; linarith
      obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hL (1 / 8) (by norm_num)
      have hM' := hM (M + 1) (by omega)
      rw [Real.dist_eq, hL0] at hM'
      have ha : 3 / 4 < t (M + 1) := by rw [abs_lt] at hM'; linarith [hM'.1]
      have hb : t (M + 1) < 1 := by have := hLt (M + 1); rw [hL0] at this; exact this
      have hstep : t (M + 2) < t (M + 1) := by
        rw [hrec (M + 1), fract_four_eq_sub_floor, floor_four_eq_three ha hb]
        norm_num
        linarith
      linarith [hinc (M + 1), hstep]
  · have hm : Antitone t := antitone_nat_of_succ_le fun n => le_of_lt (hdec n)
    have hge : ∀ n, L ≤ t n := fun n => hm.le_of_tendsto hL n
    have hLt : ∀ n, L < t n := by
      intro n
      refine lt_of_le_of_ne (hge n) (fun heq => ?_)
      have h1 := hdec n; have h2 := hge (n + 1); linarith [heq, h1, h2]
    rcases hkv with hk | hk | hk | hk
    · have hL0 : L = 0 := by push_cast at hN; rw [hk] at hN; norm_num at hN; linarith
      obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hL (1 / 8) (by norm_num)
      have hM' := hM (M + 1) (by omega)
      rw [Real.dist_eq, hL0] at hM'
      have hb : t (M + 1) < 1 / 4 := by rw [abs_lt] at hM'; linarith [hM'.2]
      have ha : 0 < t (M + 1) := by have := hLt (M + 1); rw [hL0] at this; exact this
      have hstep : t (M + 1) < t (M + 2) := by
        rw [hrec (M + 1), fract_four_eq_sub_floor, floor_four_eq_zero ha hb]
        norm_num
        linarith
      linarith [hdec (M + 1), hstep]
    · have hL0 : L = 1 / 3 := by push_cast at hN; rw [hk] at hN; norm_num at hN; linarith
      obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hL (1 / 12) (by norm_num)
      have hM' := hM (M + 1) (by omega)
      rw [Real.dist_eq, hL0] at hM'
      have ha : 1 / 3 < t (M + 1) := by have := hLt (M + 1); rw [hL0] at this; exact this
      have hb : t (M + 1) < 1 / 2 := by rw [abs_lt] at hM'; linarith [hM'.2]
      have hstep : t (M + 1) < t (M + 2) := by
        rw [hrec (M + 1), fract_four_eq_sub_floor, floor_four_eq_one (by linarith) hb]
        norm_num
        linarith
      linarith [hdec (M + 1), hstep]
    · have hL0 : L = 2 / 3 := by push_cast at hN; rw [hk] at hN; norm_num at hN; linarith
      obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hL (1 / 12) (by norm_num)
      have hM' := hM (M + 1) (by omega)
      rw [Real.dist_eq, hL0] at hM'
      have ha : 2 / 3 < t (M + 1) := by have := hLt (M + 1); rw [hL0] at this; exact this
      have hb : t (M + 1) < 3 / 4 := by rw [abs_lt] at hM'; linarith [hM'.2]
      have hstep : t (M + 1) < t (M + 2) := by
        rw [hrec (M + 1), fract_four_eq_sub_floor, floor_four_eq_two (by linarith) hb]
        norm_num
        linarith
      linarith [hdec (M + 1), hstep]
    · have hL0 : L = 1 := by push_cast at hN; rw [hk] at hN; norm_num at hN; linarith
      have h1 := hge 0
      rw [hL0] at h1
      linarith [(hrange 0).2]

/-! ## The cyclic order of the rays landing at the cusp -/

/-- If `s n` and `s (n+1)` are both in `[0,1)` and non-zero, the angle betweenness
`ccBet (s n) 0 (s (n+1))` is exactly the inequality `s n < s (n+1)`. -/
theorem ccBet_link {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n ∧ s n < 1) (hne0 : ∀ n, s n ≠ 0)
    (n : ℕ) : s n < s (n+1) ↔ Work.LandLeaves.ccBet (s n) 0 (s (n+1)) := by
  obtain ⟨h0, h1⟩ := hs n
  obtain ⟨h0', h1'⟩ := hs (n + 1)
  have hn0 : 0 < s n := lt_of_le_of_ne h0 (Ne.symm (hne0 n))
  have hfr : Int.fract (0 - s n) = 1 - s n := by
    rw [show (0:ℝ) - s n = -(s n) by ring,
      Int.fract_neg (by rw [Int.fract_eq_self.mpr ⟨le_of_lt hn0, h1⟩]; linarith),
      Int.fract_eq_self.mpr ⟨le_of_lt hn0, h1⟩]
  rw [Work.LandLeaves.ccBet, hfr]
  constructor
  · intro h
    have hpos : 0 < Int.fract (s (n+1) - s n) := by
      rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]; linarith
    have hlt : Int.fract (s (n+1) - s n) < 1 - s n := by
      rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]; linarith
    exact ⟨hpos, hlt⟩
  · rintro ⟨h2, h3⟩
    by_contra hcon
    push_neg at hcon
    rcases lt_or_eq_of_le hcon with hlt | heq
    · rw [show s (n+1) - s n = (s (n+1) - s n + 1) + ((-1:ℤ):ℝ) by push_cast; ring,
        Int.fract_add_intCast,
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩] at h3
      linarith
    · rw [heq, sub_self, Int.fract_zero] at h2; linarith

/-- The reversed form of `ccBet_link`. -/
theorem ccBet_link' {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n ∧ s n < 1) (hne0 : ∀ n, s n ≠ 0)
    (n : ℕ) : s (n+1) < s n ↔ Work.LandLeaves.ccBet (s (n+1)) 0 (s n) := by
  obtain ⟨h0, h1⟩ := hs n
  obtain ⟨h0', h1'⟩ := hs (n + 1)
  have hn0 : 0 < s (n+1) := lt_of_le_of_ne h0' (Ne.symm (hne0 (n+1)))
  have hfr : Int.fract (0 - s (n+1)) = 1 - s (n+1) := by
    rw [show (0:ℝ) - s (n+1) = -(s (n+1)) by ring,
      Int.fract_neg (by rw [Int.fract_eq_self.mpr ⟨le_of_lt hn0, h1'⟩]; linarith),
      Int.fract_eq_self.mpr ⟨le_of_lt hn0, h1'⟩]
  rw [Work.LandLeaves.ccBet, hfr]
  constructor
  · intro h
    have hpos : 0 < Int.fract (s n - s (n+1)) := by
      rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]; linarith
    have hlt : Int.fract (s n - s (n+1)) < 1 - s (n+1) := by
      rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]; linarith
    exact ⟨hpos, hlt⟩
  · rintro ⟨h2, h3⟩
    by_contra hcon
    push_neg at hcon
    rcases lt_or_eq_of_le hcon with hlt | heq
    · rw [show s n - s (n+1) = (s n - s (n+1) + 1) + ((-1:ℤ):ℝ) by push_cast; ring,
        Int.fract_add_intCast,
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩] at h3
      linarith
    · rw [heq, sub_self, Int.fract_zero] at h2; linarith

/-! ## The assembly -/

/-- The second return map `Tsq (1/4) = (T_{1/4})^[2]` fixes the cusp. -/
theorem tsq_quarter_half : (Tantibar (1 / 4 : ℂ))^[2] (1 / 2) = 1 / 2 := by
  norm_num [Function.iterate_succ, Function.iterate_zero, LeanEval.ComplexAnalysis.Tantibar,
    map_ofNat]

/-- The image of a ray landing at `1/2` under the second return map again lands at `1/2`
(the angle becomes `Int.fract (4 * ·)`). -/
theorem landsAt_fract_four_of_landsAt {u : ℝ}
    (h : Work.Landing.landsAt (1 / 4 : ℂ) u (1 / 2)) :
    Work.Landing.landsAt (1 / 4 : ℂ) (Int.fract (4 * u)) (1 / 2) := by
  have h2 := Work.Landing.landsAt_iterate h 2
  rw [angDouble_two_eq u, tsq_quarter_half] at h2
  exact h2

/-- **`RotationNumberZero (1/4) 1`, from the three geometric inputs.**  The inputs are

* `hzero`: the dynamic ray of angle `0` lands at the cusp `1/2` of `T_{1/4}`;
* `hcop`: the second return map preserves the cyclic order of the rays landing at `1/2`
  (Goldberg–Milnor, *Fixed points of polynomial maps II*, Lemma 2.2);
* `hinj`: the angle map `θ ↦ Int.fract (4 θ)` is injective on the angles of the rays landing at
  `1/2` (the local biholomorphy of `Tsq` at `1/2`).

The argument is Goldberg–Milnor's Lemma 2.2: starting from the fixed ray `R(0)`, the orbit
`θ, Int.fract (4 θ), Int.fract (16 θ), …` of a ray landing at `1/2` would be strictly monotone by
the cyclic-order preservation, which is impossible for the expanding map `θ ↦ Int.fract (4 θ)`. -/
theorem rotationNumberZero_quarter_of_inputs
    (hzero : Work.Landing.landsAt (1 / 4 : ℂ) 0 (1 / 2))
    (hcop : ∀ a b x : ℝ, Work.Landing.landsAt (1 / 4 : ℂ) a (1 / 2) →
      Work.Landing.landsAt (1 / 4 : ℂ) b (1 / 2) → Work.Landing.landsAt (1 / 4 : ℂ) x (1 / 2) →
      Work.LandLeaves.ccBet a b x →
      Work.LandLeaves.ccBet (Int.fract (4 * a)) (Int.fract (4 * b)) (Int.fract (4 * x)))
    (hinj : ∀ θ θ' : ℝ, Work.Landing.landsAt (1 / 4 : ℂ) θ (1 / 2) →
      Work.Landing.landsAt (1 / 4 : ℂ) θ' (1 / 2) →
      (∃ m : ℤ, (4 : ℝ) * θ = (4 : ℝ) * θ' + m) → ∃ mm : ℤ, θ = θ' + mm) :
    Work.Landing.RotationNumberZero (1 / 4 : ℂ) 1 := by
  intro z hz θ hland
  rw [Work.LANDCL.Quarter.isParabolic_one_eq_half hz] at hland
  rw [Work.Landing.PeriodicAngle, angDouble_two_eq]
  set t : ℝ := Int.fract θ with htdef
  have htIco : t ∈ Set.Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg θ, Int.fract_lt_one θ⟩
  have hland' : Work.Landing.landsAt (1 / 4 : ℂ) t (1 / 2) :=
    (Work.FSeed.landsAt_fract_iff (c := (1 / 4 : ℂ)) (z := (1 / 2 : ℂ))).mpr hland
  by_contra hne
  have ht0 : t ≠ 0 := by
    intro h0
    exact hne (by rw [h0]; simp [Int.fract_zero])
  let s : ℕ → ℝ := Nat.rec t (fun _ x => Int.fract (4 * x))
  have hs0 : s 0 = t := rfl
  have hsrec : ∀ n : ℕ, s (n + 1) = Int.fract (4 * s n) := fun n => rfl
  have hsrange : ∀ n : ℕ, 0 ≤ s n ∧ s n < 1 := by
    intro n
    induction n with
    | zero => exact htIco
    | succ k ih => exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hsland : ∀ n : ℕ, Work.Landing.landsAt (1 / 4 : ℂ) (s n) (1 / 2) := by
    intro n
    induction n with
    | zero => exact hland'
    | succ k ih => exact landsAt_fract_four_of_landsAt ih
  have hs1ne : s 1 ≠ t := by
    intro h
    refine hne ?_
    calc Int.fract (4 * t) = Int.fract (4 * s 0) := by rw [hs0]
      _ = s 1 := (hsrec 0).symm
      _ = t := h
  -- no element of the orbit is `0`: the angle map is injective on the portrait
  have hsne : ∀ n : ℕ, s n ≠ 0 := by
    intro n
    induction n with
    | zero => rw [hs0]; exact ht0
    | succ k ih =>
      intro h0
      have hkey4 : ∃ m : ℤ, (4 : ℝ) * s k = (4 : ℝ) * 0 + m := by
        refine ⟨⌊4 * s k⌋, ?_⟩
        have h := Int.self_sub_fract (4 * s k)
        rw [← hsrec k, h0] at h
        linarith
      obtain ⟨mm, hmm⟩ := hinj (s k) 0 (hsland k) hzero hkey4
      have hmmZ : mm = 0 := by
        obtain ⟨l0, l1⟩ := hsrange k
        have h3 : mm < 1 := by exact_mod_cast (by linarith [hmm, l1] : (mm:ℝ) < 1)
        have h4 : (-1 : ℤ) < mm := by
          exact_mod_cast (by linarith [hmm, l0] : (-1:ℝ) < (mm:ℝ))
        omega
      have hk0 : s k = 0 := by
        rw [hmmZ, Int.cast_zero] at hmm
        simpa using hmm
      exact ih hk0
  -- the monotonicity pattern propagates
  have hstepP : ∀ n : ℕ, s n < s (n + 1) → s (n + 1) < s (n + 2) := by
    intro n h
    have hcb : Work.LandLeaves.ccBet (s n) 0 (s (n + 1)) := (ccBet_link hsrange hsne n).mp h
    have hres := hcop (s n) 0 (s (n + 1)) (hsland n) hzero (hsland (n + 1)) hcb
    rw [← hsrec n, ← hsrec (n + 1)] at hres
    have h0 : Int.fract (4 * (0:ℝ)) = 0 := by rw [mul_zero]; exact Int.fract_zero
    rw [h0] at hres
    have hres' : Work.LandLeaves.ccBet (s (n + 1)) 0 (s (n + 2)) := by
      simpa [Nat.add_assoc] using hres
    exact (ccBet_link hsrange hsne (n + 1)).mpr hres'
  have hstepQ : ∀ n : ℕ, s (n + 1) < s n → s (n + 2) < s (n + 1) := by
    intro n h
    have hcb : Work.LandLeaves.ccBet (s (n + 1)) 0 (s n) := (ccBet_link' hsrange hsne n).mp h
    have hres := hcop (s (n + 1)) 0 (s n) (hsland (n + 1)) hzero (hsland n) hcb
    rw [← hsrec n, ← hsrec (n + 1)] at hres
    have h0 : Int.fract (4 * (0:ℝ)) = 0 := by rw [mul_zero]; exact Int.fract_zero
    rw [h0] at hres
    have hres' : Work.LandLeaves.ccBet (s (n + 2)) 0 (s (n + 1)) := by
      simpa [Nat.add_assoc] using hres
    exact (ccBet_link' hsrange hsne (n + 1)).mpr hres'
  have hs01 : s 0 ≠ s 1 := by
    rw [hs0]
    intro h
    exact hs1ne h.symm
  rcases lt_or_gt_of_ne hs01 with h | h
  · refine no_monotone_orbit_fract_four s hsrec hsrange (Or.inl ?_)
    intro n
    induction n with
    | zero => exact h
    | succ k ih => exact hstepP k ih
  · refine no_monotone_orbit_fract_four s hsrec hsrange (Or.inr ?_)
    intro n
    induction n with
    | zero => exact h
    | succ k ih => exact hstepQ k ih

/-- **The rotation-number-zero portrait at `c = 1/4`**, in the *repaired* form of
`Work.Landing.RotationNumberZero` (the angle is taken modulo `1`).

The period-`1` parabolic parameter `c = 1/4` of the tricorn family has the single parabolic point
`z = 1/2`, and the statement says that every dynamic ray `R_{1/4}(θ)` landing at such a point has
an angle `θ` whose class in `ℝ/ℤ` is periodic of period dividing `2` under angle doubling
`angDouble θ = Int.fract (-2 θ)`, i.e. `PeriodicAngle (Int.fract θ) (2 * 1)`.

This is Goldberg–Milnor, *Fixed points of polynomial maps II*, Lemma 2.2, at the cusp of the main
component: the second return map `Tsq (1/4) = (T_{1/4})^[2]` is holomorphic with multiplier `1` at
the parabolic point `1/2`; the ray of angle `0` lands there
(`Work.MandelFinal.Quarter.landsAt_quarter_zero_half`, from the landing theorem
`Work.LandLeaves.periodicRaysLand` and the conjugation symmetry of the tricorn for real
parameters), the return map preserves the cyclic order of the rays landing there
(`Work.MandelFinal.Quarter.ccBet_angDouble_two_quarter`, the port of
`Work.LandLeaves.ccBet_angDouble_of_typeSet`), and the angle map `θ ↦ Int.fract (4 θ)` is
injective on those angles (`Work.MandelFinal.Quarter.angleInjective_quarter`, from the local
biholomorphy of `Tsq (1/4)` at `1/2`,
`Work.MandelFinal.Quarter.tsq_quarter_localModel`).  Hence the orbit of any landing angle under
`θ ↦ Int.fract (4 θ)` would be strictly monotone against the fixed ray, which is impossible for
the expanding map `θ ↦ Int.fract (4 θ)`
(`Work.MandelFinal.no_monotone_orbit_fract_four`); so every landing angle is fixed by
`θ ↦ Int.fract (4 θ)`, i.e. lies in `{0, 1/3, 2/3}` modulo `1`. -/
theorem rotationNumberZero_quarter : Work.Landing.RotationNumberZero (1 / 4 : ℂ) 1 := by
  have hfix : Work.Landing.Tsq (1 / 4 : ℂ) (1 / 2) = 1 / 2 :=
    Work.MandelFinal.Quarter.tsq_quarter_localModel.1
  have hlocal : ∃ (r r' : ℝ) (g : ℂ → ℂ), 0 < r ∧ 0 < r' ∧ ∀ z : ℂ,
      ‖z - (1 / 2 : ℂ)‖ ≤ r → ‖Work.Landing.Tsq (1 / 4 : ℂ) z - (1 / 2 : ℂ)‖ ≤ r' →
      g (Work.Landing.Tsq (1 / 4 : ℂ) z) = z :=
    Work.MandelFinal.Quarter.tsq_quarter_localModel.2.2.2
  have hinj : ∀ θ θ' : ℝ, Work.Landing.landsAt (1 / 4 : ℂ) θ (1 / 2) →
      Work.Landing.landsAt (1 / 4 : ℂ) θ' (1 / 2) →
      (∃ m : ℤ, (4 : ℝ) * θ = (4 : ℝ) * θ' + m) → ∃ mm : ℤ, θ = θ' + mm :=
    fun θ θ' hθ hθ' h =>
      Work.MandelFinal.Quarter.angleInjective_quarter hfix hlocal hθ hθ' h
  have hcop : ∀ a b x : ℝ, Work.Landing.landsAt (1 / 4 : ℂ) a (1 / 2) →
      Work.Landing.landsAt (1 / 4 : ℂ) b (1 / 2) →
      Work.Landing.landsAt (1 / 4 : ℂ) x (1 / 2) →
      Work.LandLeaves.ccBet a b x →
      Work.LandLeaves.ccBet (Int.fract (4 * a)) (Int.fract (4 * b)) (Int.fract (4 * x)) :=
    fun a b x ha hb hx habc =>
      Work.MandelFinal.Quarter.ccBet_angDouble_two_quarter hfix hlocal hinj ha hb hx habc
  exact rotationNumberZero_quarter_of_inputs
    Work.MandelFinal.Quarter.landsAt_quarter_zero_half hcop hinj

end

end Work.MandelFinal
