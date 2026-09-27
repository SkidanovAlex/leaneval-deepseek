import Mathlib
import Submission.Work.Drive.N2.roundConfigDefs

/-!
# `Work.Drive.N2.roundConfigPath`

A smooth path of disjoint labelled round configurations joining any two of them
(`Work.Drive.N2.roundConfigPath`).

Every `circle` of a `RoundConfig` is the *horizontal* round circle of radius `rad i` around
`pos i`, i.e. it lies in the plane `{z = (pos i) 2}` (`roundPic t = (cos t, sin t, 0)`).
Consequently two such circles are automatically disjoint when their two planes differ, and they
are disjoint when they have the same centre and different radii.  The path below uses exactly
these two mechanisms:

* phase 1: the height labels (third coordinate) are spread to the *order compatible* values
  `z i + ε₀ * i`, so that all heights become pairwise different (this is the only place where the
  disjointness of the *initial* configuration is used);
* phase 2: with all heights different, every circle is moved to the common centre `(0,0)` and to
  the distinct radii `1 + i` (this keeps disjointness because different heights separate them);
* phase 3: at the common centre with distinct radii the heights may be moved arbitrarily, in
  particular to and from the canonical value;
* phases 4-6: the mirror images of phases 1-3, for the final configuration.

The schedule is carried out with `Real.smoothTransition`, so that every coordinate is `C^∞`
and the path is constant near `-∞` and `+∞`.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology

noncomputable section

variable {m : ℕ}

/-! ## Coordinates of `ℝ³` -/

/-- The vector of `ℝ³` with the three given coordinates. -/
abbrev rcMk (x y z : ℝ) : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![x, y, z]

/-- The first coordinate of a vector of `ℝ³`. -/
abbrev rcX (v : EuclideanSpace ℝ (Fin 3)) : ℝ := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0 v
/-- The second coordinate of a vector of `ℝ³`. -/
abbrev rcY (v : EuclideanSpace ℝ (Fin 3)) : ℝ := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1 v
/-- The third coordinate of a vector of `ℝ³`. -/
abbrev rcZ (v : EuclideanSpace ℝ (Fin 3)) : ℝ := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2 v

@[simp] lemma rcX_mk (x y z : ℝ) : rcX (rcMk x y z) = x := by simp [rcMk, rcX]
@[simp] lemma rcY_mk (x y z : ℝ) : rcY (rcMk x y z) = y := by simp [rcMk, rcY]
@[simp] lemma rcZ_mk (x y z : ℝ) : rcZ (rcMk x y z) = z := by simp [rcMk, rcZ]

lemma rcZ_add (a b : EuclideanSpace ℝ (Fin 3)) : rcZ (a + b) = rcZ a + rcZ b := map_add _ _ _
lemma rcZ_smul (r : ℝ) (a : EuclideanSpace ℝ (Fin 3)) : rcZ (r • a) = r * rcZ a :=
  map_smul _ _ _

lemma rcMk_eta (v : EuclideanSpace ℝ (Fin 3)) : rcMk (rcX v) (rcY v) (rcZ v) = v := by
  rw [rcMk, ← WithLp.toLp_ofLp 2 v]
  congr 1
  funext k
  fin_cases k <;> simp [rcX, rcY, rcZ]

/-! ## The round picture and its circles -/

lemma norm_roundPic (t : ℝ) : ‖roundPic t‖ = 1 := by
  have h : ‖roundPic t‖ ^ 2 = 1 := by
    rw [roundPic, PiLp.norm_sq_eq_of_L2]
    simp [Fin.sum_univ_three, Real.cos_sq_add_sin_sq]
  nlinarith [norm_nonneg (roundPic t)]

@[simp] lemma rcZ_roundPic (t : ℝ) : rcZ (roundPic t) = 0 := by simp [roundPic, rcZ]

lemma circle_sub_pos (D : RoundConfig m) (i : Fin m) (t : ℝ) :
    D.circle i t - D.pos i = D.rad i • roundPic (D.phase i + 2 * Real.pi * t) := by
  simp [RoundConfig.circle]

lemma norm_circle_sub (D : RoundConfig m) (i : Fin m) (t : ℝ) :
    ‖D.circle i t - D.pos i‖ = D.rad i := by
  rw [circle_sub_pos, norm_smul, norm_roundPic, mul_one, Real.norm_eq_abs,
    abs_of_pos (D.hrad i)]

@[simp] lemma rcZ_circle (D : RoundConfig m) (i : Fin m) (t : ℝ) :
    rcZ (D.circle i t) = rcZ (D.pos i) := by
  rw [RoundConfig.circle, rcZ_add, rcZ_smul, rcZ_roundPic, mul_zero, add_zero]

/-- Circles at different heights are disjoint. -/
lemma circle_ne_of_rcZ_ne {D : RoundConfig m} {i j : Fin m}
    (h : rcZ (D.pos i) ≠ rcZ (D.pos j)) (s t : ℝ) : D.circle i s ≠ D.circle j t := by
  intro hEq
  apply h
  rw [← rcZ_circle D i s, hEq, rcZ_circle D j t]

/-- Circles with the same centre and different radii are disjoint. -/
lemma circle_ne_of_pos_eq_rad_ne {D : RoundConfig m} {i j : Fin m}
    (hpos : D.pos i = D.pos j) (hrad : D.rad i ≠ D.rad j) (s t : ℝ) :
    D.circle i s ≠ D.circle j t := by
  intro hEq
  apply hrad
  have h : ‖D.circle i s - D.pos i‖ = ‖D.circle j t - D.pos j‖ := by rw [hpos, hEq]
  rwa [norm_circle_sub, norm_circle_sub] at h

/-! ## An order compatible spread of the height labels -/

/-- The index of `i : Fin m` as a real number. -/
def rcIdx (i : Fin m) : ℝ := ((i : ℕ) : ℝ)

lemma rcIdx_nonneg (i : Fin m) : 0 ≤ rcIdx i := by simp [rcIdx]

lemma rcIdx_injective : Function.Injective (rcIdx : Fin m → ℝ) := by
  intro i j h
  exact Fin.ext (Nat.cast_injective h)

lemma rcIdx_lt {i j : Fin m} (h : i < j) : rcIdx i < rcIdx j := by
  rw [rcIdx, rcIdx]
  exact_mod_cast h

/-- The candidate upper bound for `ε` attached to the pair `q = (i,j)`. -/
def rcGap (z : Fin m → ℝ) (q : Fin m × Fin m) : ℝ :=
  (z q.2 - z q.1) / (rcIdx q.1 - rcIdx q.2)

lemma rcGap_pos {z : Fin m → ℝ} {q : Fin m × Fin m} (h1 : q.2 < q.1) (h2 : z q.1 < z q.2) :
    0 < rcGap z q := by
  rw [rcGap]
  apply div_pos (sub_pos.mpr h2)
  have : rcIdx q.2 < rcIdx q.1 := rcIdx_lt h1
  linarith

/-- There is a positive `ε` making the map `i ↦ z i + ε * i` strictly increasing along `z`. -/
lemma exists_spread (z : Fin m → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i j : Fin m, z i < z j → z i + ε * rcIdx i < z j + ε * rcIdx j := by
  classical
  by_cases h : ∃ p : Fin m × Fin m, p.2 < p.1 ∧ z p.1 < z p.2
  · obtain ⟨p, hp⟩ := h
    let T : Finset (Fin m × Fin m) := Finset.univ.filter (fun q => q.2 < q.1 ∧ z q.1 < z q.2)
    have hT : T.Nonempty := ⟨p, by simp [T, hp]⟩
    have hcpos : 0 < T.inf' hT (rcGap z) := by
      obtain ⟨q, hq, hqe⟩ := Finset.exists_mem_eq_inf' hT (rcGap z)
      have hq' : q.2 < q.1 ∧ z q.1 < z q.2 := by simpa [T] using hq
      rw [hqe]
      exact rcGap_pos hq'.1 hq'.2
    refine ⟨T.inf' hT (rcGap z) / 2, by linarith, ?_⟩
    intro i j hij
    by_cases hji : j < i
    · have hmem : (i, j) ∈ T := by simp [T, hji, hij]
      have hden : 0 < rcIdx i - rcIdx j := by
        have : rcIdx j < rcIdx i := rcIdx_lt hji
        linarith
      have hle : T.inf' hT (rcGap z) ≤ (z j - z i) / (rcIdx i - rcIdx j) := by
        have := Finset.inf'_le (rcGap z) hmem
        simpa only [rcGap] using this
      rw [le_div_iff₀ hden] at hle
      have : T.inf' hT (rcGap z) / 2 * (rcIdx i - rcIdx j) < z j - z i := by nlinarith
      linarith
    · have hijne : i ≠ j := fun hh => by rw [hh] at hij; exact lt_irrefl _ hij
      have hij' : i < j := by
        rcases lt_trichotomy i j with h' | h' | h'
        · exact h'
        · exact absurd h' hijne
        · exact absurd h' hji
      have hlt : rcIdx i < rcIdx j := rcIdx_lt hij'
      nlinarith [hcpos]
  · refine ⟨1, one_pos, ?_⟩
    intro i j hij
    have hijne : i ≠ j := fun hh => by rw [hh] at hij; exact lt_irrefl _ hij
    have hnot : ¬ j < i := fun hji => h ⟨(i, j), hji, hij⟩
    have hij' : i < j := lt_of_le_of_ne (le_of_not_gt hnot) hijne
    have hlt : rcIdx i < rcIdx j := rcIdx_lt hij'
    nlinarith

/-- Injectivity of `i ↦ z i + t * i` for `0 < t ≤ ε` when `ε` makes the spread order compatible. -/
lemma spread_inj {z : Fin m → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hord : ∀ i j : Fin m, z i < z j → z i + ε * rcIdx i < z j + ε * rcIdx j)
    {t : ℝ} (ht0 : 0 < t) (htε : t ≤ ε) {i j : Fin m} (hij : i ≠ j) :
    z i + t * rcIdx i ≠ z j + t * rcIdx j := by
  intro hEq
  have hdiff : z j - z i = t * (rcIdx i - rcIdx j) := by linarith
  rcases lt_trichotomy (z i) (z j) with hlt | heq | hgt
  · have h1 : ε * (rcIdx i - rcIdx j) < z j - z i := by linarith [hord i j hlt]
    rcases le_or_gt (rcIdx i - rcIdx j) 0 with h2 | h2
    · have : t * (rcIdx i - rcIdx j) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht0) h2
      linarith
    · have : t * (rcIdx i - rcIdx j) < ε * (rcIdx i - rcIdx j) := by nlinarith
      linarith
  · have hf : rcIdx i = rcIdx j := by
      have h0 : t * (rcIdx i - rcIdx j) = 0 := by linarith
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact absurd h' (ne_of_gt ht0)
      · linarith
    exact hij (rcIdx_injective hf)
  · have h1 : ε * (rcIdx j - rcIdx i) < z i - z j := by linarith [hord j i hgt]
    rcases le_or_gt (rcIdx j - rcIdx i) 0 with h2 | h2
    · have : t * (rcIdx j - rcIdx i) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht0) h2
      linarith
    · have : t * (rcIdx j - rcIdx i) < ε * (rcIdx j - rcIdx i) := by nlinarith
      linarith

/-- The linear interpolation version of `spread_inj`. -/
lemma lerp_spread_ne {z : Fin m → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hord : ∀ i j : Fin m, z i < z j → z i + ε * rcIdx i < z j + ε * rcIdx j)
    {i j : Fin m} (hij : i ≠ j) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (1 - s) * z i + s * (z i + ε * rcIdx i) ≠
      (1 - s) * z j + s * (z j + ε * rcIdx j) := by
  have ht0 : 0 < s * ε := mul_pos hs0 hε
  have htε : s * ε ≤ ε := by nlinarith
  have h := spread_inj hε hord ht0 htε hij
  intro hh
  apply h
  nlinarith [hh]

/-! ## A generic smooth transition -/

/-- The `k`-th smooth stage function, flat on `(-∞, k/6]` and equal to `1` on `[(k+1)/6, ∞)`. -/
def rcS (k : ℝ) (u : ℝ) : ℝ := Real.smoothTransition (6 * u - k)

@[fun_prop]
lemma contDiff_rcS (k : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => rcS k u) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => 6 * u - k) := by fun_prop
  have h2 := (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp h1
  simpa [rcS, Function.comp_def] using h2

lemma rcS_nonneg (k : ℝ) (u : ℝ) : 0 ≤ rcS k u := Real.smoothTransition.nonneg _
lemma rcS_le_one (k : ℝ) (u : ℝ) : rcS k u ≤ 1 := Real.smoothTransition.le_one _
lemma rcS_eq_zero_iff (k : ℝ) (u : ℝ) : rcS k u = 0 ↔ 6 * u ≤ k := by simp [rcS]
lemma rcS_eq_one_iff (k : ℝ) (u : ℝ) : rcS k u = 1 ↔ k + 1 ≤ 6 * u := by
  rw [rcS, Real.smoothTransition.eq_one_iff_one_le]
  constructor <;> intro h <;> linarith
lemma rcS_pos_of (k : ℝ) (u : ℝ) (h : k < 6 * u) : 0 < rcS k u := by
  rw [rcS]; exact Real.smoothTransition.pos_of_pos (by linarith)
lemma rcS_lt_one_of (k : ℝ) (u : ℝ) (h : 6 * u < k + 1) : rcS k u < 1 := by
  rw [rcS]; exact Real.smoothTransition.lt_one_of_lt_one (by linarith)

/-! ## The path of configurations -/

/-- A positive convex combination of two positive numbers is positive. -/
lemma pos_convex_combo {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < (1 - t) * a + t * b := by
  rcases le_total t (1 / 2) with h | h
  · nlinarith
  · nlinarith

/-- The canonical radius of the `i`-th circle in the middle phase. -/
def rcRcan (i : Fin m) : ℝ := 1 + rcIdx i

/-- The canonical height of the `i`-th circle in the middle phase. -/
def rcWcan (i : Fin m) : ℝ := rcIdx i

lemma rcRcan_pos (i : Fin m) : 0 < rcRcan i := by
  rw [rcRcan]; have := rcIdx_nonneg i; linarith

/-- The first coordinate of the centre of the `i`-th circle along the path. -/
def rcPathX (D₀ D₁ : RoundConfig m) (u : ℝ) (i : Fin m) : ℝ :=
  (1 - rcS 4 u) * ((1 - rcS 1 u) * rcX (D₀.pos i) + rcS 1 u * 0)
    + rcS 4 u * rcX (D₁.pos i)

/-- The second coordinate of the centre of the `i`-th circle along the path. -/
def rcPathY (D₀ D₁ : RoundConfig m) (u : ℝ) (i : Fin m) : ℝ :=
  (1 - rcS 4 u) * ((1 - rcS 1 u) * rcY (D₀.pos i) + rcS 1 u * 0)
    + rcS 4 u * rcY (D₁.pos i)

/-- The radius of the `i`-th circle along the path. -/
def rcPathR (D₀ D₁ : RoundConfig m) (u : ℝ) (i : Fin m) : ℝ :=
  (1 - rcS 4 u) * ((1 - rcS 1 u) * D₀.rad i + rcS 1 u * rcRcan i)
    + rcS 4 u * D₁.rad i

/-- The phase of the `i`-th circle along the path. -/
def rcPathP (D₀ D₁ : RoundConfig m) (u : ℝ) (i : Fin m) : ℝ :=
  (1 - rcS 4 u) * ((1 - rcS 1 u) * D₀.phase i + rcS 1 u * 0)
    + rcS 4 u * D₁.phase i

/-- The height of the `i`-th circle along the path (the only coordinate with all six stages). -/
def rcPathZ (D₀ D₁ : RoundConfig m) (ε₀ ε₁ : ℝ) (u : ℝ) (i : Fin m) : ℝ :=
  (1 - rcS 5 u) * ((1 - rcS 3 u) * ((1 - rcS 2 u) *
      ((1 - rcS 0 u) * rcZ (D₀.pos i) + rcS 0 u * (rcZ (D₀.pos i) + ε₀ * rcIdx i))
    + rcS 2 u * rcWcan i)
    + rcS 3 u * (rcZ (D₁.pos i) + ε₁ * rcIdx i))
  + rcS 5 u * rcZ (D₁.pos i)

lemma rcPathR_pos (D₀ D₁ : RoundConfig m) (u : ℝ) (i : Fin m) : 0 < rcPathR D₀ D₁ u i := by
  rw [rcPathR]
  have h1 := pos_convex_combo (D₀.hrad i) (rcRcan_pos i) (rcS_nonneg 1 u) (rcS_le_one 1 u)
  exact pos_convex_combo h1 (D₁.hrad i) (rcS_nonneg 4 u) (rcS_le_one 4 u)

/-- The configuration at parameter `u`. -/
def pathConfig (D₀ D₁ : RoundConfig m) (ε₀ ε₁ : ℝ) (u : ℝ) : RoundConfig m where
  pos := fun i => rcMk (rcPathX D₀ D₁ u i) (rcPathY D₀ D₁ u i) (rcPathZ D₀ D₁ ε₀ ε₁ u i)
  rad := fun i => rcPathR D₀ D₁ u i
  hrad := fun i => rcPathR_pos D₀ D₁ u i
  phase := fun i => rcPathP D₀ D₁ u i

@[simp] lemma pathConfig_pos (D₀ D₁ : RoundConfig m) (ε₀ ε₁ u : ℝ) (i : Fin m) :
    (pathConfig D₀ D₁ ε₀ ε₁ u).pos i
      = rcMk (rcPathX D₀ D₁ u i) (rcPathY D₀ D₁ u i) (rcPathZ D₀ D₁ ε₀ ε₁ u i) := rfl

@[simp] lemma pathConfig_rad (D₀ D₁ : RoundConfig m) (ε₀ ε₁ u : ℝ) (i : Fin m) :
    (pathConfig D₀ D₁ ε₀ ε₁ u).rad i = rcPathR D₀ D₁ u i := rfl

@[simp] lemma pathConfig_phase (D₀ D₁ : RoundConfig m) (ε₀ ε₁ u : ℝ) (i : Fin m) :
    (pathConfig D₀ D₁ ε₀ ε₁ u).phase i = rcPathP D₀ D₁ u i := rfl

lemma pathConfig_rcZ (D₀ D₁ : RoundConfig m) (ε₀ ε₁ u : ℝ) (i : Fin m) :
    rcZ ((pathConfig D₀ D₁ ε₀ ε₁ u).pos i) = rcPathZ D₀ D₁ ε₀ ε₁ u i := by
  simp [pathConfig]

/-! ## The phase identities -/

lemma rcPathZ_early (D₀ D₁ : RoundConfig m) {ε₀ ε₁ u : ℝ} (h2 : rcS 2 u = 0)
    (h3 : rcS 3 u = 0) (h5 : rcS 5 u = 0) (i : Fin m) :
    rcPathZ D₀ D₁ ε₀ ε₁ u i = rcZ (D₀.pos i) + (rcS 0 u * ε₀) * rcIdx i := by
  simp only [rcPathZ, h2, h3, h5]
  ring

lemma rcPathZ_late (D₀ D₁ : RoundConfig m) {ε₀ ε₁ u : ℝ} (h2 : rcS 2 u = 1)
    (h3 : rcS 3 u = 1) (i : Fin m) :
    rcPathZ D₀ D₁ ε₀ ε₁ u i = rcZ (D₁.pos i) + ((1 - rcS 5 u) * ε₁) * rcIdx i := by
  simp only [rcPathZ, h2, h3]
  ring

lemma rcPathX_mid (D₀ D₁ : RoundConfig m) {u : ℝ} (h1 : rcS 1 u = 1) (h4 : rcS 4 u = 0)
    (i : Fin m) : rcPathX D₀ D₁ u i = 0 := by
  simp only [rcPathX, h1, h4]
  ring

lemma rcPathY_mid (D₀ D₁ : RoundConfig m) {u : ℝ} (h1 : rcS 1 u = 1) (h4 : rcS 4 u = 0)
    (i : Fin m) : rcPathY D₀ D₁ u i = 0 := by
  simp only [rcPathY, h1, h4]
  ring

lemma rcPathR_mid (D₀ D₁ : RoundConfig m) {u : ℝ} (h1 : rcS 1 u = 1) (h4 : rcS 4 u = 0)
    (i : Fin m) : rcPathR D₀ D₁ u i = rcRcan i := by
  simp only [rcPathR, h1, h4]
  ring

/-! ## Smoothness of the path -/

lemma contDiff_rcPathX (D₀ D₁ : RoundConfig m) (i : Fin m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => rcPathX D₀ D₁ u i) := by
  simp only [rcPathX]
  fun_prop

lemma contDiff_rcPathY (D₀ D₁ : RoundConfig m) (i : Fin m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => rcPathY D₀ D₁ u i) := by
  simp only [rcPathY]
  fun_prop

lemma contDiff_rcPathR (D₀ D₁ : RoundConfig m) (i : Fin m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => rcPathR D₀ D₁ u i) := by
  simp only [rcPathR]
  fun_prop

lemma contDiff_rcPathP (D₀ D₁ : RoundConfig m) (i : Fin m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => rcPathP D₀ D₁ u i) := by
  simp only [rcPathP]
  fun_prop

lemma contDiff_rcPathZ (D₀ D₁ : RoundConfig m) (ε₀ ε₁ : ℝ) (i : Fin m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => rcPathZ D₀ D₁ ε₀ ε₁ u i) := by
  simp only [rcPathZ]
  fun_prop

lemma contDiff_rcMk {f g h : ℝ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => rcMk (f u) (g u) (h u)) := by
  refine (contDiff_piLp (p := 2) (𝕜 := ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).mpr ?_
  intro k
  fin_cases k
  · simpa [rcMk] using hf
  · simpa [rcMk] using hg
  · simpa [rcMk] using hh

lemma contDiff_pathConfig_pos (D₀ D₁ : RoundConfig m) (ε₀ ε₁ : ℝ) (i : Fin m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => (pathConfig D₀ D₁ ε₀ ε₁ u).pos i) := by
  have h : (fun u : ℝ => (pathConfig D₀ D₁ ε₀ ε₁ u).pos i)
      = fun u : ℝ => rcMk (rcPathX D₀ D₁ u i) (rcPathY D₀ D₁ u i) (rcPathZ D₀ D₁ ε₀ ε₁ u i) :=
    rfl
  rw [h]
  exact contDiff_rcMk (contDiff_rcPathX D₀ D₁ i) (contDiff_rcPathY D₀ D₁ i)
    (contDiff_rcPathZ D₀ D₁ ε₀ ε₁ i)

lemma contDiff_pathConfig_rad (D₀ D₁ : RoundConfig m) (ε₀ ε₁ : ℝ) (i : Fin m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => (pathConfig D₀ D₁ ε₀ ε₁ u).rad i) :=
  contDiff_rcPathR D₀ D₁ i

lemma contDiff_pathConfig_phase (D₀ D₁ : RoundConfig m) (ε₀ ε₁ : ℝ) (i : Fin m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => (pathConfig D₀ D₁ ε₀ ε₁ u).phase i) :=
  contDiff_rcPathP D₀ D₁ i

/-! ## The endpoints of the path -/

lemma RoundConfig.eq_of_ext {D E : RoundConfig m} (h1 : D.pos = E.pos) (h2 : D.rad = E.rad)
    (h3 : D.phase = E.phase) : D = E := by
  cases D
  cases E
  simp_all

lemma pathConfig_of_nonpos (D₀ D₁ : RoundConfig m) (ε₀ ε₁ : ℝ) {u : ℝ} (h : 6 * u ≤ 0) :
    pathConfig D₀ D₁ ε₀ ε₁ u = D₀ := by
  have h0 : rcS 0 u = 0 := (rcS_eq_zero_iff 0 u).mpr (by linarith)
  have h1 : rcS 1 u = 0 := (rcS_eq_zero_iff 1 u).mpr (by linarith)
  have h2 : rcS 2 u = 0 := (rcS_eq_zero_iff 2 u).mpr (by linarith)
  have h3 : rcS 3 u = 0 := (rcS_eq_zero_iff 3 u).mpr (by linarith)
  have h4 : rcS 4 u = 0 := (rcS_eq_zero_iff 4 u).mpr (by linarith)
  have h5 : rcS 5 u = 0 := (rcS_eq_zero_iff 5 u).mpr (by linarith)
  have hx : ∀ i, rcPathX D₀ D₁ u i = rcX (D₀.pos i) := by
    intro i
    simp only [rcPathX, h1, h4]
    ring
  have hy : ∀ i, rcPathY D₀ D₁ u i = rcY (D₀.pos i) := by
    intro i
    simp only [rcPathY, h1, h4]
    ring
  have hz : ∀ i, rcPathZ D₀ D₁ ε₀ ε₁ u i = rcZ (D₀.pos i) := by
    intro i
    simp only [rcPathZ, h0, h2, h3, h5]
    ring
  have hr : ∀ i, rcPathR D₀ D₁ u i = D₀.rad i := by
    intro i
    simp only [rcPathR, h1, h4]
    ring
  have hp : ∀ i, rcPathP D₀ D₁ u i = D₀.phase i := by
    intro i
    simp only [rcPathP, h1, h4]
    ring
  refine RoundConfig.eq_of_ext ?_ ?_ ?_
  · funext i
    rw [show (pathConfig D₀ D₁ ε₀ ε₁ u).pos i
        = rcMk (rcPathX D₀ D₁ u i) (rcPathY D₀ D₁ u i) (rcPathZ D₀ D₁ ε₀ ε₁ u i) from rfl,
      hx i, hy i, hz i]
    exact rcMk_eta (D₀.pos i)
  · funext i
    rw [show (pathConfig D₀ D₁ ε₀ ε₁ u).rad i = rcPathR D₀ D₁ u i from rfl, hr i]
  · funext i
    rw [show (pathConfig D₀ D₁ ε₀ ε₁ u).phase i = rcPathP D₀ D₁ u i from rfl, hp i]

lemma pathConfig_of_one_le (D₀ D₁ : RoundConfig m) (ε₀ ε₁ : ℝ) {u : ℝ} (h : 6 ≤ 6 * u) :
    pathConfig D₀ D₁ ε₀ ε₁ u = D₁ := by
  have h0 : rcS 0 u = 1 := (rcS_eq_one_iff 0 u).mpr (by linarith)
  have h1 : rcS 1 u = 1 := (rcS_eq_one_iff 1 u).mpr (by linarith)
  have h2 : rcS 2 u = 1 := (rcS_eq_one_iff 2 u).mpr (by linarith)
  have h3 : rcS 3 u = 1 := (rcS_eq_one_iff 3 u).mpr (by linarith)
  have h4 : rcS 4 u = 1 := (rcS_eq_one_iff 4 u).mpr (by linarith)
  have h5 : rcS 5 u = 1 := (rcS_eq_one_iff 5 u).mpr (by linarith)
  have hx : ∀ i, rcPathX D₀ D₁ u i = rcX (D₁.pos i) := by
    intro i
    simp only [rcPathX, h1, h4]
    ring
  have hy : ∀ i, rcPathY D₀ D₁ u i = rcY (D₁.pos i) := by
    intro i
    simp only [rcPathY, h1, h4]
    ring
  have hz : ∀ i, rcPathZ D₀ D₁ ε₀ ε₁ u i = rcZ (D₁.pos i) := by
    intro i
    simp only [rcPathZ, h0, h2, h3, h5]
    ring
  have hr : ∀ i, rcPathR D₀ D₁ u i = D₁.rad i := by
    intro i
    simp only [rcPathR, h1, h4]
    ring
  have hp : ∀ i, rcPathP D₀ D₁ u i = D₁.phase i := by
    intro i
    simp only [rcPathP, h1, h4]
    ring
  refine RoundConfig.eq_of_ext ?_ ?_ ?_
  · funext i
    rw [show (pathConfig D₀ D₁ ε₀ ε₁ u).pos i
        = rcMk (rcPathX D₀ D₁ u i) (rcPathY D₀ D₁ u i) (rcPathZ D₀ D₁ ε₀ ε₁ u i) from rfl,
      hx i, hy i, hz i]
    exact rcMk_eta (D₁.pos i)
  · funext i
    rw [show (pathConfig D₀ D₁ ε₀ ε₁ u).rad i = rcPathR D₀ D₁ u i from rfl, hr i]
  · funext i
    rw [show (pathConfig D₀ D₁ ε₀ ε₁ u).phase i = rcPathP D₀ D₁ u i from rfl, hp i]

/-! ## Disjointness along the path -/

theorem pathConfig_disjoint {D₀ D₁ : RoundConfig m} {ε₀ ε₁ : ℝ}
    (hε₀ : 0 < ε₀)
    (hord₀ : ∀ i j : Fin m, rcZ (D₀.pos i) < rcZ (D₀.pos j) →
      rcZ (D₀.pos i) + ε₀ * rcIdx i < rcZ (D₀.pos j) + ε₀ * rcIdx j)
    (hε₁ : 0 < ε₁)
    (hord₁ : ∀ i j : Fin m, rcZ (D₁.pos i) < rcZ (D₁.pos j) →
      rcZ (D₁.pos i) + ε₁ * rcIdx i < rcZ (D₁.pos j) + ε₁ * rcIdx j)
    (h₀ : D₀.Disjoint) (h₁ : D₁.Disjoint) (u : ℝ) :
    (pathConfig D₀ D₁ ε₀ ε₁ u).Disjoint := by
  intro i j hij s t
  by_cases hw0 : 6 * u ≤ 0
  · rw [pathConfig_of_nonpos D₀ D₁ ε₀ ε₁ hw0]
    exact h₀ i j hij s t
  by_cases hw6 : 6 ≤ 6 * u
  · rw [pathConfig_of_one_le D₀ D₁ ε₀ ε₁ hw6]
    exact h₁ i j hij s t
  have hw0' : 0 < 6 * u := lt_of_not_ge hw0
  have hw6' : 6 * u < 6 := lt_of_not_ge hw6
  have key : ∀ v : ℝ, rcPathZ D₀ D₁ ε₀ ε₁ u i ≠ rcPathZ D₀ D₁ ε₀ ε₁ u j →
      (pathConfig D₀ D₁ ε₀ ε₁ u).circle i v ≠ (pathConfig D₀ D₁ ε₀ ε₁ u).circle j t := by
    intro v hv hEq
    apply hv
    have h := congrArg rcZ hEq
    simp only [rcZ_circle, pathConfig_rcZ] at h
    exact h
  by_cases h2 : 6 * u ≤ 2
  · have h2z : rcS 2 u = 0 := (rcS_eq_zero_iff 2 u).mpr (by linarith)
    have h3z : rcS 3 u = 0 := (rcS_eq_zero_iff 3 u).mpr (by linarith)
    have h5z : rcS 5 u = 0 := (rcS_eq_zero_iff 5 u).mpr (by linarith)
    have hz : rcPathZ D₀ D₁ ε₀ ε₁ u i ≠ rcPathZ D₀ D₁ ε₀ ε₁ u j := by
      rw [rcPathZ_early D₀ D₁ h2z h3z h5z, rcPathZ_early D₀ D₁ h2z h3z h5z]
      refine spread_inj hε₀ hord₀ (mul_pos (rcS_pos_of 0 u (by linarith)) hε₀) ?_ hij
      have := rcS_le_one 0 u
      nlinarith
    exact fun hEq => key s hz hEq
  by_cases h4 : 6 * u ≤ 4
  · have h1 : rcS 1 u = 1 := (rcS_eq_one_iff 1 u).mpr (by linarith)
    have h4' : rcS 4 u = 0 := (rcS_eq_zero_iff 4 u).mpr (by linarith)
    by_cases hzeq : rcPathZ D₀ D₁ ε₀ ε₁ u i = rcPathZ D₀ D₁ ε₀ ε₁ u j
    · have hxi := rcPathX_mid D₀ D₁ h1 h4' i
      have hyi := rcPathY_mid D₀ D₁ h1 h4' i
      have hxj := rcPathX_mid D₀ D₁ h1 h4' j
      have hyj := rcPathY_mid D₀ D₁ h1 h4' j
      have hri := rcPathR_mid D₀ D₁ h1 h4' i
      have hrj := rcPathR_mid D₀ D₁ h1 h4' j
      have hpos : (pathConfig D₀ D₁ ε₀ ε₁ u).pos i
          = (pathConfig D₀ D₁ ε₀ ε₁ u).pos j := by
        simp only [pathConfig_pos, hxi, hyi, hxj, hyj, hzeq]
      have hrad : (pathConfig D₀ D₁ ε₀ ε₁ u).rad i
          ≠ (pathConfig D₀ D₁ ε₀ ε₁ u).rad j := by
        simp only [pathConfig_rad, hri, hrj, rcRcan]
        intro hh
        exact hij (rcIdx_injective (by linarith))
      exact circle_ne_of_pos_eq_rad_ne hpos hrad s t
    · exact fun hEq => key s hzeq hEq
  · have h2 : rcS 2 u = 1 := (rcS_eq_one_iff 2 u).mpr (by linarith)
    have h3 : rcS 3 u = 1 := (rcS_eq_one_iff 3 u).mpr (by linarith)
    have h5lt : rcS 5 u < 1 := rcS_lt_one_of 5 u (by linarith)
    have h5nn : 0 ≤ rcS 5 u := rcS_nonneg 5 u
    have hz : rcPathZ D₀ D₁ ε₀ ε₁ u i ≠ rcPathZ D₀ D₁ ε₀ ε₁ u j := by
      rw [rcPathZ_late D₀ D₁ h2 h3, rcPathZ_late D₀ D₁ h2 h3]
      refine spread_inj hε₁ hord₁ ?_ ?_ hij
      · nlinarith
      · nlinarith
    exact fun hEq => key s hz hEq

/-! ## The main theorem -/

theorem roundConfigPath {m : ℕ} (D₀ D₁ : Work.Drive.N2.RoundConfig m)
    (h₀ : D₀.Disjoint) (h₁ : D₁.Disjoint) :
    ∃ D : ℝ → Work.Drive.N2.RoundConfig m,
      D 0 = D₀ ∧ D 1 = D₁ ∧
      (∀ s : ℝ, s ≤ 0 → D s = D₀) ∧ (∀ s : ℝ, 1 ≤ s → D s = D₁) ∧
      (∀ s : ℝ, (D s).Disjoint) ∧
      (∀ i : Fin m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (D s).pos i)) ∧
      (∀ i : Fin m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (D s).rad i)) ∧
      (∀ i : Fin m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (D s).phase i)) := by
  obtain ⟨ε₀, hε₀, hord₀⟩ := exists_spread (fun i => rcZ (D₀.pos i))
  obtain ⟨ε₁, hε₁, hord₁⟩ := exists_spread (fun i => rcZ (D₁.pos i))
  refine ⟨fun s => pathConfig D₀ D₁ ε₀ ε₁ s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pathConfig_of_nonpos D₀ D₁ ε₀ ε₁ (by norm_num)
  · exact pathConfig_of_one_le D₀ D₁ ε₀ ε₁ (by norm_num)
  · intro s hs
    exact pathConfig_of_nonpos D₀ D₁ ε₀ ε₁ (by linarith)
  · intro s hs
    exact pathConfig_of_one_le D₀ D₁ ε₀ ε₁ (by linarith)
  · intro s
    exact pathConfig_disjoint hε₀ hord₀ hε₁ hord₁ h₀ h₁ s
  · intro i
    exact contDiff_pathConfig_pos D₀ D₁ ε₀ ε₁ i
  · intro i
    exact contDiff_pathConfig_rad D₀ D₁ ε₀ ε₁ i
  · intro i
    exact contDiff_pathConfig_phase D₀ D₁ ε₀ ε₁ i

end

end Work.Drive.N2
