/-
# `Submission.Work.FIArea3.JointCount.jointPieceLat_basis`

A two-element ℤ-basis of the lattice `jointPieceLat z₁ w e` with the paper's size bound.

`jointPieceLat z₁ w e = (yLat A B e) · w` where `A = im(star z₁ * w)`, `B = re(star z₁ * w)`
(`pieces.lean`): the lattice of the piece `w ℤ[i]` cut by the joint congruence
`e ∣ im(star z₁ · w · y)`.  Since `yLat A B e = {y | e ∣ A·y.im + B·y.re}` is a full-rank
sublattice of `ℤ[i] = ℤ²` of index `q = e / gcd e (gcd |A| |B|)`, it has a two-element ℤ-basis.
The Hermite normal form of the congruence gives an explicit one,

  `m₁ = ⟨γ/g, t₀⟩`,  `m₂ = ⟨0, e/γ⟩`,  `γ = gcd e |A|`,  `g = gcd γ |B|`,  `t₀ ∈ [0, e/γ)`,

where `γ/g` generates the possible `re`-coordinates of `yLat`, `e/γ` is the vertical period, and
`t₀` is any solution of `B·(γ/g) ≡ -A·t₀ (mod e)` reduced modulo `e/γ`.  Its determinant is
`γ/g · e/γ = q`, and its lengths satisfy
`√|m₁|² + √|m₂|² ≤ γ/g + t₀ + e/γ ≤ γ/g + 2·e/γ - 1 ≤ 5 q`.

Multiplying by `w` multiplies the determinant by `|w|² = gnorm w` (so the determinant is the
index `gnorm w · q = index (jointPieceLat z₁ w e)`, `index_jointPieceLat`) and the lengths by
`√(gnorm w)`, which converts the `5 q` bound into `5 · index / √(gnorm w)`.  The carrier of
`jointPieceLat z₁ w e` is the image of the carrier of `yLat A B e` under `y ↦ y * w`, i.e. the
ℤ-span of `m₁ w`, `m₂ w`.
-/
import Mathlib
import Submission.Work.FIArea3.JointCount.pieces
import Submission.Work.FIArea3.JointCount.index_jointPieceLat

namespace Work.FIArea3.JointCount

open Work.FIPlan

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Elementary Gaussian-integer arithmetic -/

/-- `gnorm` is multiplicative. -/
lemma jpl_gnorm_mul (z w : GaussianInt) : gnorm (z * w) = gnorm z * gnorm w := by
  simp [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- `gnorm` vanishes only at `0`. -/
lemma jpl_gnorm_eq_zero_iff (z : GaussianInt) : gnorm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hz : z.norm = 0 := by
      rw [Work.FIPlan.gnorm] at h
      exact Int.natAbs_eq_zero.mp h
    exact (Zsqrtd.norm_eq_zero (by intro n _; nlinarith [sq_nonneg n]) z).mp hz
  · rintro rfl; simp [Work.FIPlan.gnorm]

lemma jpl_gnorm_pos {w : GaussianInt} (hw : w ≠ 0) : 0 < gnorm w :=
  Nat.pos_of_ne_zero (fun h => hw ((jpl_gnorm_eq_zero_iff w).mp h))

/-- `gnorm z` as an integer is `z.re ^ 2 + z.im ^ 2`. -/
lemma jpl_gnorm_eq_int (z : GaussianInt) : (gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := by
  rw [Work.FIPlan.gnorm, Zsqrtd.norm_def]
  have h : (0 : ℤ) ≤ z.re * z.re - -1 * z.im * z.im := by
    nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  rw [Int.natAbs_of_nonneg h]; ring

/-- The determinant `Im(star m₁ * m₂)` is multiplied by `gnorm w` when both arguments are
multiplied by `w`. -/
lemma jpl_det_mul (m₁ m₂ w : GaussianInt) :
    ((m₁ * w).re * (m₂ * w).im - (m₁ * w).im * (m₂ * w).re).natAbs
      = (m₁.re * m₂.im - m₁.im * m₂.re).natAbs * gnorm w := by
  have h1 : (m₁ * w).re = m₁.re * w.re - m₁.im * w.im := by rw [Zsqrtd.re_mul]; ring
  have h2 : (m₁ * w).im = m₁.re * w.im + m₁.im * w.re := by rw [Zsqrtd.im_mul]
  have h3 : (m₂ * w).re = m₂.re * w.re - m₂.im * w.im := by rw [Zsqrtd.re_mul]; ring
  have h4 : (m₂ * w).im = m₂.re * w.im + m₂.im * w.re := by rw [Zsqrtd.im_mul]
  have hkey : (m₁ * w).re * (m₂ * w).im - (m₁ * w).im * (m₂ * w).re
      = (m₁.re * m₂.im - m₁.im * m₂.re) * (w.re ^ 2 + w.im ^ 2) := by
    rw [h1, h2, h3, h4]; ring
  have hnorm : gnorm w = (w.re ^ 2 + w.im ^ 2).natAbs := by
    rw [Work.FIPlan.gnorm, Zsqrtd.norm_def]; congr 1; ring
  rw [hkey, Int.natAbs_mul, hnorm]

/-- `(a : ℤ) ∣ b` reduces to a natural divisibility. -/
lemma jpl_int_dvd_natAbs_iff (a : ℕ) (b : ℤ) : (a : ℤ) ∣ b ↔ a ∣ b.natAbs := by
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]

/-! ## The Hermite normal form of `yLat A B e`

`yLat A B e = {y | e ∣ A·y.im + B·y.re}`.  With `γ = gcd e |A|`, the `re`-coordinates of its
points are the multiples of `γ/g`, `g = gcd γ |B|`; the `im`-coordinates of its points with
`re = 0` are the multiples of `e/γ`; and a point with `re = γ/g` exists by the solvability
criterion.  The three lemmas below establish exactly these facts. -/

/-- The period facts for `yLat A B e`: the minimal `re`-coordinate `x₀ = γ / gcd γ |B|`, the
vertical period `a = e / γ`, the divisibility `e ∣ A · a`, the product identity
`x₀ · a = e / gcd e (gcd |A| |B|)`, and the criterion `e ∣ A t ↔ a ∣ t`. -/
lemma jpl_period_basic (A B : ℤ) (e : ℕ) (he : 1 ≤ e) (γ h x₀ a : ℕ)
    (hγ : γ = Nat.gcd e A.natAbs) (hh : h = Nat.gcd γ B.natAbs)
    (hx₀ : x₀ = γ / h) (ha : a = e / γ) :
    0 < x₀ ∧ 0 < a ∧ (e : ℤ) ∣ A * (a : ℤ) ∧
    x₀ * a = e / Nat.gcd e (Nat.gcd A.natAbs B.natAbs) ∧
    (∀ t : ℤ, (e : ℤ) ∣ A * t ↔ (a : ℤ) ∣ t) := by
  have hepos : 0 < e := by omega
  have hγpos : 0 < γ := by rw [hγ]; exact Nat.gcd_pos_of_pos_left _ hepos
  have hhpos : 0 < h := by rw [hh]; exact Nat.gcd_pos_of_pos_left _ hγpos
  have hhγ : h ∣ γ := by rw [hh]; exact Nat.gcd_dvd_left _ _
  have hγe : γ ∣ e := by rw [hγ]; exact Nat.gcd_dvd_left _ _
  have hγA : γ ∣ A.natAbs := by rw [hγ]; exact Nat.gcd_dvd_right _ _
  have hx0pos : 0 < x₀ := by rw [hx₀]; exact Nat.div_pos (Nat.le_of_dvd hγpos hhγ) hhpos
  have hapos : 0 < a := by rw [ha]; exact Nat.div_pos (Nat.le_of_dvd hepos hγe) hγpos
  have hγAdvd : (γ : ℤ) ∣ A := by
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]; exact hγA
  have hea : e = γ * a := by rw [ha, mul_comm]; exact (Nat.div_mul_cancel hγe).symm
  have hEA : (e : ℤ) ∣ A * (a : ℤ) := by
    obtain ⟨A₁, hA₁⟩ := hγAdvd
    exact ⟨A₁, by rw [hA₁, hea]; push_cast; ring⟩
  have hh_eq : h = Nat.gcd e (Nat.gcd A.natAbs B.natAbs) := by rw [hh, hγ, Nat.gcd_assoc]
  have hγmul : γ = x₀ * h := by rw [hx₀, Nat.div_mul_cancel hhγ]
  have hprod : x₀ * a = e / h := by
    have : e = (x₀ * a) * h := by rw [hea, hγmul]; ring
    exact (Nat.div_eq_of_eq_mul_left hhpos this).symm
  have hA₁eq : A.natAbs = γ * (A.natAbs / γ) := by
    rw [mul_comm]; exact (Nat.div_mul_cancel hγA).symm
  have hcop : a.Coprime (A.natAbs / γ) := by
    rw [ha, hγ]
    exact Nat.coprime_div_gcd_div_gcd (by rw [← hγ]; exact hγpos)
  have hta : ∀ t : ℤ, (e : ℤ) ∣ A * t ↔ (a : ℤ) ∣ t := by
    intro t
    constructor
    · intro hd
      have h1 : e ∣ (A * t).natAbs := (jpl_int_dvd_natAbs_iff e (A * t)).mp hd
      rw [Int.natAbs_mul] at h1
      have h2 : γ * a ∣ γ * ((A.natAbs / γ) * t.natAbs) := by
        have hEq : γ * ((A.natAbs / γ) * t.natAbs) = A.natAbs * t.natAbs := by
          conv_rhs => rw [hA₁eq]
          ring
        rw [hEq, ← hea]; exact h1
      have h3 : a ∣ (A.natAbs / γ) * t.natAbs := (Nat.mul_dvd_mul_iff_left hγpos).mp h2
      have h4 : a ∣ t.natAbs := hcop.dvd_of_dvd_mul_left h3
      exact (jpl_int_dvd_natAbs_iff a t).mpr h4
    · rintro ⟨c, hc⟩
      obtain ⟨A₁, hA₁⟩ := hγAdvd
      refine ⟨A₁ * c, ?_⟩
      rw [hc, hA₁, hea]
      push_cast
      ring
  exact ⟨hx0pos, hapos, hEA, by rw [hprod, hh_eq], hta⟩

/-- The `re`-coordinates of `yLat A B e`: `x` occurs iff `e ∣ B x + A t` is solvable in `t`, iff
the minimal `re`-coordinate `x₀ = γ / gcd γ |B|` divides `x`. -/
lemma jpl_period_xiff (A B : ℤ) (e : ℕ) (he : 1 ≤ e) (γ h x₀ : ℕ)
    (hγ : γ = Nat.gcd e A.natAbs) (hh : h = Nat.gcd γ B.natAbs) (hx₀ : x₀ = γ / h) :
    ∀ x : ℤ, (∃ t : ℤ, (e : ℤ) ∣ B * x + A * t) ↔ (x₀ : ℤ) ∣ x := by
  have hepos : 0 < e := by omega
  have hγpos : 0 < γ := by rw [hγ]; exact Nat.gcd_pos_of_pos_left _ hepos
  have hhpos : 0 < h := by rw [hh]; exact Nat.gcd_pos_of_pos_left _ hγpos
  have hhγ : h ∣ γ := by rw [hh]; exact Nat.gcd_dvd_left _ _
  have hhB : h ∣ B.natAbs := by rw [hh]; exact Nat.gcd_dvd_right _ _
  have hγgcd : (((e : ℤ).gcd A : ℕ) : ℤ) = (γ : ℤ) := by rw [hγ]; rfl
  have hBdvd : (h : ℤ) ∣ B := by
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]; exact hhB
  have hBeq : B.natAbs = h * (B.natAbs / h) := by
    rw [mul_comm]; exact (Nat.div_mul_cancel hhB).symm
  have hγeq : γ = h * x₀ := by rw [hx₀, mul_comm]; exact (Nat.div_mul_cancel hhγ).symm
  have hcop : x₀.Coprime (B.natAbs / h) := by
    rw [hx₀, hh]
    exact Nat.coprime_div_gcd_div_gcd (by rw [← hh]; exact hhpos)
  intro x
  have step1 : (∃ t : ℤ, (e : ℤ) ∣ B * x + A * t) ↔ (γ : ℤ) ∣ B * x := by
    constructor
    · rintro ⟨t, ht⟩
      have hmem : B * x ∈ AddSubgroup.zmultiples (e : ℤ) ⊔ AddSubgroup.zmultiples A := by
        rw [AddSubgroup.mem_sup]
        exact ⟨B * x + A * t, Int.mem_zmultiples_iff.mpr ht, -(A * t),
          Int.mem_zmultiples_iff.mpr (dvd_neg.mpr (dvd_mul_right A t)), by ring⟩
      rw [Int.zmultiples_sup, Int.mem_zmultiples_iff, hγgcd] at hmem
      exact hmem
    · intro hd
      have hmem : B * x ∈ AddSubgroup.zmultiples (e : ℤ) ⊔ AddSubgroup.zmultiples A := by
        rw [Int.zmultiples_sup, Int.mem_zmultiples_iff, hγgcd]
        exact hd
      rw [AddSubgroup.mem_sup] at hmem
      obtain ⟨p, hp, q, hq, hpq⟩ := hmem
      obtain ⟨m2, hm2⟩ := Int.mem_zmultiples_iff.mp hq
      refine ⟨-m2, ?_⟩
      have hkey : B * x + A * (-m2) = p := by rw [← hpq, hm2]; ring
      rw [hkey]
      exact Int.mem_zmultiples_iff.mp hp
  rw [step1]
  constructor
  · intro hd
    have h1 : γ ∣ B.natAbs * x.natAbs := by
      have := (jpl_int_dvd_natAbs_iff γ (B * x)).mp hd
      rwa [Int.natAbs_mul] at this
    have h2 : γ ∣ h * ((B.natAbs / h) * x.natAbs) := by
      have hEq : h * ((B.natAbs / h) * x.natAbs) = B.natAbs * x.natAbs := by
        conv_rhs => rw [hBeq]
        ring
      rw [hEq]; exact h1
    rw [hγeq] at h2
    have h3 : x₀ ∣ (B.natAbs / h) * x.natAbs := (Nat.mul_dvd_mul_iff_left hhpos).mp h2
    have h4 : x₀ ∣ x.natAbs := hcop.dvd_of_dvd_mul_left h3
    exact (jpl_int_dvd_natAbs_iff x₀ x).mpr h4
  · rintro ⟨c, hc⟩
    obtain ⟨B₁, hB₁⟩ := hBdvd
    refine ⟨B₁ * c, ?_⟩
    rw [hc, hγeq, hB₁]
    push_cast
    ring

/-- A point of `yLat A B e` with minimal `re`-coordinate `x₀`, reduced in the `im`-coordinate
modulo the vertical period `a`. -/
lemma jpl_period_t0 (A B : ℤ) (e : ℕ) (x₀ a : ℕ)
    (hA : (e : ℤ) ∣ A * (a : ℤ))
    (hxiff : ∀ x : ℤ, (∃ t : ℤ, (e : ℤ) ∣ B * x + A * t) ↔ (x₀ : ℤ) ∣ x)
    (ha : 0 < a) :
    ∃ t₀ : ℤ, 0 ≤ t₀ ∧ t₀ < (a : ℤ) ∧ (e : ℤ) ∣ B * (x₀ : ℤ) + A * t₀ := by
  obtain ⟨t, ht⟩ := (hxiff (x₀ : ℤ)).mpr (dvd_refl (x₀ : ℤ))
  refine ⟨t % (a : ℤ), Int.emod_nonneg t (by exact_mod_cast (ne_of_gt ha)), ?_, ?_⟩
  · exact Int.emod_lt_of_pos t (by exact_mod_cast ha)
  · have hmod : t % (a : ℤ) = t - (a : ℤ) * (t / (a : ℤ)) := by
      have h := Int.mul_ediv_add_emod t (a : ℤ); linarith
    rw [hmod]
    have hkey : B * (x₀ : ℤ) + A * (t - (a : ℤ) * (t / (a : ℤ)))
        = (B * (x₀ : ℤ) + A * t) - (A * (a : ℤ)) * (t / (a : ℤ)) := by ring
    rw [hkey]
    exact dvd_sub ht (dvd_mul_of_dvd_left hA _)

/-- **The ℤ-span of the Hermite basis.**  For `x₀` generating the `re`-coordinates, `a` the
vertical period, `t₀` a reduced solution of the congruence, the points of `yLat A B e` are
exactly the ℤ-linear combinations of `⟨x₀, t₀⟩` and `⟨0, a⟩`. -/
lemma jpl_span_yLat (A B : ℤ) (e : ℕ) (x₀ a : ℕ) (t₀ : ℤ)
    (hxiff : ∀ x : ℤ, (∃ t : ℤ, (e : ℤ) ∣ B * x + A * t) ↔ (x₀ : ℤ) ∣ x)
    (htiff : ∀ t : ℤ, (e : ℤ) ∣ A * t ↔ (a : ℤ) ∣ t)
    (hA : (e : ℤ) ∣ A * (a : ℤ))
    (ht₀ : (e : ℤ) ∣ B * (x₀ : ℤ) + A * t₀) :
    ∀ z : GaussianInt, z ∈ yLat A B e ↔
      ∃ p q : ℤ, z = (p : GaussianInt) * (⟨(x₀ : ℤ), t₀⟩ : GaussianInt)
        + (q : GaussianInt) * (⟨0, (a : ℤ)⟩ : GaussianInt) := by
  intro z
  constructor
  · intro hz
    have hz' : (e : ℤ) ∣ A * z.im + B * z.re := hz
    have hx : ∃ t : ℤ, (e : ℤ) ∣ B * z.re + A * t := ⟨z.im, by rw [add_comm]; exact hz'⟩
    obtain ⟨k, hk⟩ := (hxiff z.re).mp hx
    have hr : (e : ℤ) ∣ A * (z.im - k * t₀) := by
      have h2 : (e : ℤ) ∣ k * (B * (x₀ : ℤ) + A * t₀) := dvd_mul_of_dvd_right ht₀ k
      have hkey : A * (z.im - k * t₀)
          = (A * z.im + B * z.re) - k * (B * (x₀ : ℤ) + A * t₀) := by
        rw [hk]; ring
      rw [hkey]; exact dvd_sub hz' h2
    obtain ⟨j, hj⟩ := (htiff _).mp hr
    refine ⟨k, j, ?_⟩
    apply Zsqrtd.ext
    · simp only [Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]
      rw [hk]; ring
    · simp only [Zsqrtd.im_add, Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]
      linarith [hj]
  · rintro ⟨p, q, rfl⟩
    have hm1 : (⟨(x₀ : ℤ), t₀⟩ : GaussianInt) ∈ yLat A B e := by
      show (e : ℤ) ∣ A * t₀ + B * (x₀ : ℤ)
      rw [add_comm]; exact ht₀
    have hm2 : (⟨(0 : ℤ), (a : ℤ)⟩ : GaussianInt) ∈ yLat A B e := by
      show (e : ℤ) ∣ A * (a : ℤ) + B * 0
      rw [mul_zero, add_zero]; exact hA
    rw [show (p : GaussianInt) * (⟨(x₀ : ℤ), t₀⟩ : GaussianInt)
          + (q : GaussianInt) * (⟨0, (a : ℤ)⟩ : GaussianInt)
        = p • (⟨(x₀ : ℤ), t₀⟩ : GaussianInt) + q • (⟨0, (a : ℤ)⟩ : GaussianInt) from by
      rw [zsmul_eq_mul, zsmul_eq_mul]]
    exact AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _ hm1 p) (AddSubgroup.zsmul_mem _ hm2 q)

/-- The length bound `√|⟨x₀,t₀⟩|² + √|⟨0,a⟩|² ≤ 5 q` for the Hermite basis. -/
lemma jpl_basis_bound (x₀ a : ℕ) (t₀ : ℤ) (q : ℕ) (hx0 : 0 < x₀) (ha : 0 < a)
    (ht0nn : 0 ≤ t₀) (ht0lt : t₀ < (a : ℤ)) (hq : x₀ * a = q) :
    Real.sqrt ((gnorm (⟨(x₀ : ℤ), t₀⟩ : GaussianInt) : ℕ) : ℝ)
      + Real.sqrt ((gnorm (⟨(0 : ℤ), (a : ℤ)⟩ : GaussianInt) : ℕ) : ℝ) ≤ 5 * (q : ℝ) := by
  have hg1 : ((gnorm (⟨(x₀ : ℤ), t₀⟩ : GaussianInt) : ℕ) : ℝ) = (x₀ : ℝ) ^ 2 + (t₀ : ℝ) ^ 2 := by
    have h : ((gnorm (⟨(x₀ : ℤ), t₀⟩ : GaussianInt) : ℤ) : ℝ) = ((x₀ : ℝ) ^ 2 + (t₀ : ℝ) ^ 2) := by
      rw [jpl_gnorm_eq_int]; push_cast; ring
    simpa using h
  have hg2 : ((gnorm (⟨(0 : ℤ), (a : ℤ)⟩ : GaussianInt) : ℕ) : ℝ) = (a : ℝ) ^ 2 := by
    have h : ((gnorm (⟨(0 : ℤ), (a : ℤ)⟩ : GaussianInt) : ℤ) : ℝ) = ((0 : ℝ) ^ 2 + (a : ℝ) ^ 2) := by
      rw [jpl_gnorm_eq_int]; push_cast; ring
    simpa using h
  rw [hg1, hg2]
  set X : ℝ := (x₀ : ℝ) with hX
  set T : ℝ := (t₀ : ℝ) with hT
  set Aa : ℝ := (a : ℝ) with hAa
  have hX1 : 1 ≤ X := by rw [hX]; exact_mod_cast hx0
  have hA1 : 1 ≤ Aa := by rw [hAa]; exact_mod_cast ha
  have hT0 : 0 ≤ T := by rw [hT]; exact_mod_cast ht0nn
  have hTle : T ≤ Aa - 1 := by
    have h1 : t₀ ≤ (a : ℤ) - 1 := by omega
    have h2 : (t₀ : ℝ) ≤ (((a : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast h1
    rw [hT, hAa]; push_cast at h2 ⊢; linarith
  have hs1 : Real.sqrt (X ^ 2 + T ^ 2) ≤ X + T := by
    rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ X + T)]
    exact Real.sqrt_le_sqrt (by nlinarith [hT0, hX1])
  have hs2 : Real.sqrt (Aa ^ 2) = Aa := Real.sqrt_sq (by linarith)
  rw [hs2]
  have hq' : X * Aa = (q : ℝ) := by rw [hX, hAa, ← Nat.cast_mul, hq]
  have hfin : X + 2 * Aa - 1 ≤ 5 * (X * Aa) := by
    nlinarith [hX1, hA1, mul_nonneg (sub_nonneg.mpr hX1) (sub_nonneg.mpr hA1)]
  linarith [hs1, hTle, hfin, hq']

/-- **Existence of a two-element ℤ-basis of `yLat A B e` with determinant the index and length
bound `5 · index`.** -/
lemma jpl_yLat_basis (A B : ℤ) (e : ℕ) (he : 1 ≤ e) :
    ∃ m₁ m₂ : GaussianInt,
      (∀ z : GaussianInt, z ∈ yLat A B e ↔
        ∃ a b : ℤ, z = (a : GaussianInt) * m₁ + (b : GaussianInt) * m₂)
      ∧ (m₁.re * m₂.im - m₁.im * m₂.re).natAbs
          = e / Nat.gcd e (Nat.gcd A.natAbs B.natAbs)
      ∧ Real.sqrt ((gnorm m₁ : ℕ) : ℝ) + Real.sqrt ((gnorm m₂ : ℕ) : ℝ)
          ≤ 5 * ((e / Nat.gcd e (Nat.gcd A.natAbs B.natAbs) : ℕ) : ℝ) := by
  set γ : ℕ := Nat.gcd e A.natAbs with hγ
  set h : ℕ := Nat.gcd γ B.natAbs with hh
  set x₀ : ℕ := γ / h with hx₀
  set a : ℕ := e / γ with ha
  obtain ⟨hx0, hapos, hEA, hprod, hta⟩ := jpl_period_basic A B e he γ h x₀ a hγ hh hx₀ ha
  have hxiff := jpl_period_xiff A B e he γ h x₀ hγ hh hx₀
  obtain ⟨t₀, ht0nn, ht0lt, ht₀⟩ := jpl_period_t0 A B e x₀ a hEA hxiff hapos
  refine ⟨⟨(x₀ : ℤ), t₀⟩, ⟨(0 : ℤ), (a : ℤ)⟩, ?_, ?_, ?_⟩
  · exact jpl_span_yLat A B e x₀ a t₀ hxiff hta hEA ht₀
  · have hdet : ((⟨(x₀ : ℤ), t₀⟩ : GaussianInt).re * (⟨(0 : ℤ), (a : ℤ)⟩ : GaussianInt).im
        - (⟨(x₀ : ℤ), t₀⟩ : GaussianInt).im * (⟨(0 : ℤ), (a : ℤ)⟩ : GaussianInt).re)
        = ((x₀ * a : ℕ) : ℤ) := by push_cast; ring
    rw [hdet, Int.natAbs_natCast, hprod]
  · exact jpl_basis_bound x₀ a t₀ (e / Nat.gcd e (Nat.gcd A.natAbs B.natAbs)) hx0 hapos ht0nn
      ht0lt hprod

/-! ## The transfer from `yLat` to `jointPieceLat` -/

/-- **Transfer step.**  A two-element ℤ-basis `m₁, m₂` of `yLat A B e` (with `A = im(star z₁ * w)`,
`B = re(star z₁ * w)`) whose determinant is `q = e / gcd e (gcd |A| |B|)` and whose lengths sum
to at most `5 q`, when multiplied by `w`, gives the requested determinant, carrier and length
bound for `jointPieceLat z₁ w e`. -/
lemma jpl_jointPieceLat_basis_aux (z₁ w : GaussianInt) (e : ℕ) (hw : w ≠ 0) (he : 1 ≤ e)
    {m₁ m₂ : GaussianInt}
    (hmem : ∀ z : GaussianInt, z ∈ yLat (star z₁ * w).im (star z₁ * w).re e ↔
      ∃ a b : ℤ, z = (a : GaussianInt) * m₁ + (b : GaussianInt) * m₂)
    (hdet : (m₁.re * m₂.im - m₁.im * m₂.re).natAbs
      = e / Nat.gcd e (Nat.gcd (star z₁ * w).im.natAbs (star z₁ * w).re.natAbs))
    (hbound : Real.sqrt ((gnorm m₁ : ℕ) : ℝ) + Real.sqrt ((gnorm m₂ : ℕ) : ℝ)
      ≤ 5 * ((e / Nat.gcd e (Nat.gcd (star z₁ * w).im.natAbs (star z₁ * w).re.natAbs) : ℕ) : ℝ)) :
    ((m₁ * w).re * (m₂ * w).im - (m₁ * w).im * (m₂ * w).re).natAbs
        = (jointPieceLat z₁ w e).index
      ∧ (jointPieceLat z₁ w e).carrier
          = {z : GaussianInt | ∃ a b : ℤ,
              z = (a : GaussianInt) * (m₁ * w) + (b : GaussianInt) * (m₂ * w)}
      ∧ Real.sqrt ((gnorm (m₁ * w) : ℕ) : ℝ) + Real.sqrt ((gnorm (m₂ * w) : ℕ) : ℝ)
          ≤ ((jointPieceLat z₁ w e).index : ℝ) * (5 / Real.sqrt ((gnorm w : ℕ) : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [jpl_det_mul, hdet, index_jointPieceLat z₁ w e he hw, mul_comm]
  · ext z
    simp only [Set.mem_ofPred_eq]
    change z ∈ jointPieceLat z₁ w e ↔
      ∃ a b : ℤ, z = (a : GaussianInt) * (m₁ * w) + (b : GaussianInt) * (m₂ * w)
    rw [show jointPieceLat z₁ w e
          = (yLat (star z₁ * w).im (star z₁ * w).re e).map (AddMonoidHom.mulRight w) from rfl,
      AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, b, rfl⟩ := (hmem y).mp hy
      exact ⟨a, b, by rw [AddMonoidHom.mulRight_apply]; ring⟩
    · rintro ⟨a, b, rfl⟩
      refine ⟨(a : GaussianInt) * m₁ + (b : GaussianInt) * m₂, (hmem _).mpr ⟨a, b, rfl⟩, ?_⟩
      rw [AddMonoidHom.mulRight_apply]
      ring
  · have hindex := index_jointPieceLat z₁ w e he hw
    have hsw : 0 < (gnorm w : ℝ) := by exact_mod_cast jpl_gnorm_pos hw
    have e1 : Real.sqrt ((gnorm (m₁ * w) : ℕ) : ℝ)
        = Real.sqrt ((gnorm m₁ : ℕ) : ℝ) * Real.sqrt ((gnorm w : ℕ) : ℝ) := by
      rw [jpl_gnorm_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
    have e2 : Real.sqrt ((gnorm (m₂ * w) : ℕ) : ℝ)
        = Real.sqrt ((gnorm m₂ : ℕ) : ℝ) * Real.sqrt ((gnorm w : ℕ) : ℝ) := by
      rw [jpl_gnorm_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
    rw [e1, e2, hindex]
    have hrhs : ((gnorm w * (e / Nat.gcd e (Nat.gcd (star z₁ * w).im.natAbs
            (star z₁ * w).re.natAbs)) : ℕ) : ℝ) * (5 / Real.sqrt ((gnorm w : ℕ) : ℝ))
        = 5 * ((e / Nat.gcd e (Nat.gcd (star z₁ * w).im.natAbs
            (star z₁ * w).re.natAbs) : ℕ) : ℝ) * Real.sqrt ((gnorm w : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
      have hs2 : Real.sqrt ((gnorm w : ℕ) : ℝ) ^ 2 = ((gnorm w : ℕ) : ℝ) :=
        Real.sq_sqrt (Nat.cast_nonneg _)
      field_simp
      rw [hs2]; ring
    rw [hrhs]
    nlinarith [hbound, Real.sqrt_nonneg ((gnorm w : ℕ) : ℝ)]

/-! ## The main theorem -/

theorem jointPieceLat_basis (z₁ w : GaussianInt) (e : ℕ) (hw : w ≠ 0) (he : 1 ≤ e) :
    ∃ g₁ g₂ : GaussianInt,
      (g₁.re * g₂.im - g₁.im * g₂.re).natAbs
          = (Work.FIArea3.JointCount.jointPieceLat z₁ w e).index
        ∧ (Work.FIArea3.JointCount.jointPieceLat z₁ w e).carrier
            = {z : GaussianInt | ∃ a b : ℤ,
                z = (a : GaussianInt) * g₁ + (b : GaussianInt) * g₂}
        ∧ Real.sqrt ((Work.FIPlan.gnorm g₁ : ℝ)) + Real.sqrt ((Work.FIPlan.gnorm g₂ : ℝ))
            ≤ ((Work.FIArea3.JointCount.jointPieceLat z₁ w e).index : ℝ)
                * (5 / Real.sqrt ((Work.FIPlan.gnorm w : ℝ))) := by
  obtain ⟨m₁, m₂, hmem, hdet, hbound⟩ :=
    jpl_yLat_basis (star z₁ * w).im (star z₁ * w).re e he
  exact ⟨m₁ * w, m₂ * w, jpl_jointPieceLat_basis_aux z₁ w e hw he hmem hdet hbound⟩

end

end Work.FIArea3.JointCount
