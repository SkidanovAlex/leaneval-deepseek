/-
# `Submission.Work.FIArea6b.convexHull_volume_le`

The lattice points of `A` lie in a disc of radius `R` centred at `c` and in the strip
`|r y - s x| ≤ W` (the direction `(r,s)` of the strip has length `d = √(r²+s²)`, so the strip has
width `2W/d`).  Its convex hull is therefore contained in the intersection of the disc with the
strip, whose area is at most the diameter `2R` times the strip width `2W/d`, namely

`volume (convexHull ℝ A) ≤ 4 R W / √(r²+s²)`.

The geometric heart is the orthogonal change of coordinates
`(x,y) ↦ ((-s x + r y)/d, (r x + s y)/d)`, an involution with `|det| = 1`, that turns the strip
into the coordinate strip `|·| ≤ W/d` and keeps the disc a disc; the image of the hull then lies in
the rectangle of dimensions `2W/d × 2R`, and the determinant-one map preserves Lebesgue measure.
-/
import Mathlib

set_option autoImplicit false

namespace Work.FIArea6b

open MeasureTheory

noncomputable section

/-- The `ℝ`-linear map `(x, y) ↦ ((-a x + b y)/d, (b x + a y)/d)`.  When `d² = a² + b²` and
`d ≠ 0` it is an involution of `ℝ × ℝ` with `|det| = 1`; with `a = s`, `b = r`, `d = √(r²+s²)`
it is the orthogonal change of variables that straightens the strip `|r y - s x| ≤ W`. -/
def Tlin (a b d : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := ((-a * p.1 + b * p.2) / d, (b * p.1 + a * p.2) / d)
  map_add' p q := by
    show ((-a * (p.1 + q.1) + b * (p.2 + q.2)) / d, (b * (p.1 + q.1) + a * (p.2 + q.2)) / d)
        = ((-a * p.1 + b * p.2) / d, (b * p.1 + a * p.2) / d)
          + ((-a * q.1 + b * q.2) / d, (b * q.1 + a * q.2) / d)
    ext <;> simp only [Prod.mk_add_mk] <;> ring
  map_smul' t p := by
    show ((-a * (t * p.1) + b * (t * p.2)) / d, (b * (t * p.1) + a * (t * p.2)) / d)
        = t • ((-a * p.1 + b * p.2) / d, (b * p.1 + a * p.2) / d)
    ext <;> simp only [Prod.smul_mk, smul_eq_mul] <;> ring

@[simp] theorem Tlin_apply (a b d : ℝ) (p : ℝ × ℝ) :
    Tlin a b d p = ((-a * p.1 + b * p.2) / d, (b * p.1 + a * p.2) / d) := rfl

/-- `Tlin a b d` is an involution when `d² = a² + b²` and `d ≠ 0`. -/
theorem Tlin_comp_self (a b d : ℝ) (hd : d ≠ 0) (hsq : d ^ 2 = a ^ 2 + b ^ 2) :
    (Tlin a b d).comp (Tlin a b d) = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  rw [LinearMap.comp_apply, LinearMap.id_apply, Tlin_apply, Tlin_apply]
  simp only [Prod.mk.injEq]
  constructor <;> (field_simp; rw [hsq]; ring)

/-- An involution has determinant `±1`, hence `|det| = 1`. -/
theorem Tlin_det_abs (a b d : ℝ) (hd : d ≠ 0) (hsq : d ^ 2 = a ^ 2 + b ^ 2) :
    |LinearMap.det (Tlin a b d)| = 1 := by
  have hmul : LinearMap.det (Tlin a b d) * LinearMap.det (Tlin a b d) = 1 := by
    have hh := congrArg LinearMap.det (Tlin_comp_self a b d hd hsq)
    rw [LinearMap.det_comp, LinearMap.det_id] at hh
    exact hh
  have h2 : (LinearMap.det (Tlin a b d)) ^ 2 = 1 := by rw [pow_two]; exact hmul
  rw [← Real.sqrt_sq_eq_abs, h2, Real.sqrt_one]

/-- The closed disc `{(x,y) : (x-c₁)² + (y-c₂)² ≤ R²}` is convex. -/
theorem convex_disk (c : ℝ × ℝ) (R : ℝ) :
    Convex ℝ {p : ℝ × ℝ | (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 ≤ R ^ 2} := by
  intro p hp q hq a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hp hq ⊢
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] at ⊢
  simp only [smul_eq_mul] at ⊢
  have e1 : a * p.1 + b * q.1 - c.1 = a * (p.1 - c.1) + b * (q.1 - c.1) := by
    rw [show b = 1 - a from by linarith]; ring
  have e2 : a * p.2 + b * q.2 - c.2 = a * (p.2 - c.2) + b * (q.2 - c.2) := by
    rw [show b = 1 - a from by linarith]; ring
  rw [e1, e2]
  have hid : a * ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2) + b * ((q.1 - c.1) ^ 2 + (q.2 - c.2) ^ 2)
      - ((a * (p.1 - c.1) + b * (q.1 - c.1)) ^ 2 + (a * (p.2 - c.2) + b * (q.2 - c.2)) ^ 2)
      = a * b * (((p.1 - c.1) - (q.1 - c.1)) ^ 2 + ((p.2 - c.2) - (q.2 - c.2)) ^ 2) := by
    rw [show b = 1 - a from by linarith]; ring
  have hnn : 0 ≤ a * b * (((p.1 - c.1) - (q.1 - c.1)) ^ 2 + ((p.2 - c.2) - (q.2 - c.2)) ^ 2) :=
    mul_nonneg (mul_nonneg ha hb) (by positivity)
  nlinarith [hid, hnn, hp, hq, ha, hb, hab, sq_nonneg R]

/-- The strip `{|r y - s x| ≤ W}` is convex. -/
theorem convex_strip (r s W : ℝ) :
    Convex ℝ {p : ℝ × ℝ | |r * p.2 - s * p.1| ≤ W} := by
  intro p hp q hq a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hp hq ⊢
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] at ⊢
  simp only [smul_eq_mul] at ⊢
  calc |r * (a * p.2 + b * q.2) - s * (a * p.1 + b * q.1)|
      = |a * (r * p.2 - s * p.1) + b * (r * q.2 - s * q.1)| := by congr 1; ring
    _ ≤ |a * (r * p.2 - s * p.1)| + |b * (r * q.2 - s * q.1)| := abs_add_le _ _
    _ = a * |r * p.2 - s * p.1| + b * |r * q.2 - s * q.1| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * W + b * W :=
          add_le_add (mul_le_mul_of_nonneg_left hp ha) (mul_le_mul_of_nonneg_left hq hb)
    _ = W := by rw [← add_mul, hab, one_mul]

/-- Cauchy–Schwarz in two variables: if `a² + b² ≤ R²` then `|r a + s b| ≤ √(r²+s²) · R`. -/
theorem abs_linear_le (r s d a b R : ℝ) (hd : 0 < d) (hdsq : d ^ 2 = r ^ 2 + s ^ 2)
    (hR : 0 ≤ R) (hab : a ^ 2 + b ^ 2 ≤ R ^ 2) : |r * a + s * b| ≤ d * R := by
  have hcs : (r * a + s * b) ^ 2 ≤ (r ^ 2 + s ^ 2) * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (r * b - s * a)]
  have h2 : (r ^ 2 + s ^ 2) * (a ^ 2 + b ^ 2) ≤ (r ^ 2 + s ^ 2) * R ^ 2 :=
    mul_le_mul_of_nonneg_left hab (by positivity)
  have h3 : (r ^ 2 + s ^ 2) * R ^ 2 = (d * R) ^ 2 := by rw [← hdsq]; ring
  have h1 : (r * a + s * b) ^ 2 ≤ (d * R) ^ 2 := by linarith [hcs, h2, h3]
  have h4 : 0 ≤ d * R := mul_nonneg hd.le hR
  have := (sq_le_sq).mp h1
  rwa [abs_of_nonneg h4] at this

/-- The Lebesgue measure of the axis-parallel rectangle `[-u,u] × [y₀-R, y₀+R]`. -/
theorem rect_volume (u R y0 : ℝ) (hu : 0 ≤ u) :
    MeasureTheory.volume (Set.Icc (-u) u ×ˢ Set.Icc (y0 - R) (y0 + R))
      = ENNReal.ofReal (2 * u * (2 * R)) := by
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, MeasureTheory.Measure.prod_prod,
      Real.volume_Icc, Real.volume_Icc]
  rw [← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ u - (-u))]
  congr 1
  ring

/-- **Geometric core.**  A set contained in the disc of radius `R` about `c` and in the strip
`|r y - s x| ≤ W` has measure at most `4 R W / √(r²+s²)`. -/
theorem volume_le_of_subset_disk_strip
    (r s R W : ℝ) (hR : 0 ≤ R) (hW : 0 ≤ W) (hd : 0 < r ^ 2 + s ^ 2)
    (c : ℝ × ℝ) (S : Set (ℝ × ℝ))
    (hS : S ⊆ {p : ℝ × ℝ | (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 ≤ R ^ 2} ∩
              {p : ℝ × ℝ | |r * p.2 - s * p.1| ≤ W}) :
    MeasureTheory.volume S ≤ ENNReal.ofReal (4 * R * (W / Real.sqrt (r ^ 2 + s ^ 2))) := by
  set d := Real.sqrt (r ^ 2 + s ^ 2) with hddef
  have hdpos : 0 < d := Real.sqrt_pos.mpr hd
  have hdsq : d ^ 2 = r ^ 2 + s ^ 2 := by
    rw [hddef, Real.sq_sqrt (le_of_lt hd)]
  have hdsq' : d ^ 2 = s ^ 2 + r ^ 2 := by linarith
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hWd : 0 ≤ W / d := div_nonneg hW hdpos.le
  have hdet : |LinearMap.det (Tlin s r d)| = 1 := Tlin_det_abs s r d hdne hdsq'
  have hrect : Tlin s r d '' S ⊆
      Set.Icc (-(W / d)) (W / d) ×ˢ
        Set.Icc ((Tlin s r d c).2 - R) ((Tlin s r d c).2 + R) := by
    rintro w ⟨p, hp, rfl⟩
    obtain ⟨hpdisk, hpstrip⟩ := hS hp
    simp only [Set.mem_ofPred_eq] at hpdisk hpstrip
    rw [Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rw [Set.mem_Icc]
      have h1 : (Tlin s r d p).1 = (r * p.2 - s * p.1) / d := by
        simp only [Tlin_apply]; ring
      have h1' : |(Tlin s r d p).1| ≤ W / d := by
        rw [h1, abs_div, abs_of_pos hdpos]
        exact div_le_div_of_nonneg_right hpstrip hdpos.le
      exact abs_le.mp h1'
    · rw [Set.mem_Icc]
      have h2 : (Tlin s r d p).2 - (Tlin s r d c).2
          = (r * (p.1 - c.1) + s * (p.2 - c.2)) / d := by
        simp only [Tlin_apply]; ring
      have h2' : |(Tlin s r d p).2 - (Tlin s r d c).2| ≤ R := by
        rw [h2, abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos]
        have := abs_linear_le r s d (p.1 - c.1) (p.2 - c.2) R hdpos hdsq hR hpdisk
        linarith
      obtain ⟨ha, hb⟩ := abs_le.mp h2'
      exact ⟨by linarith, by linarith⟩
  have himg : MeasureTheory.volume (Tlin s r d '' S) = MeasureTheory.volume S := by
    rw [MeasureTheory.Measure.addHaar_image_linearMap (μ := MeasureTheory.volume) (Tlin s r d) S,
      hdet]
    simp
  calc MeasureTheory.volume S
      = MeasureTheory.volume (Tlin s r d '' S) := himg.symm
    _ ≤ MeasureTheory.volume (Set.Icc (-(W / d)) (W / d) ×ˢ
          Set.Icc ((Tlin s r d c).2 - R) ((Tlin s r d c).2 + R)) := measure_mono hrect
    _ = ENNReal.ofReal (2 * (W / d) * (2 * R)) := rect_volume (W / d) R (Tlin s r d c).2 hWd
    _ = ENNReal.ofReal (4 * R * (W / Real.sqrt (r ^ 2 + s ^ 2))) := by
        congr 1
        rw [hddef]
        ring

/-- **Target lemma.**  Lattice points lying in a disc of radius `R` and in the strip
`|r y - s x| ≤ W` have convex hull of area at most `4 R W / √(r²+s²)`. -/
theorem convexHull_volume_le (r s : ℤ) (hne : r ≠ 0 ∨ s ≠ 0) (R W : ℝ) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (c : ℝ × ℝ) (A : Finset (ℤ × ℤ))
    (hball : ∀ x ∈ A, ((x.1 : ℝ) - c.1) ^ 2 + ((x.2 : ℝ) - c.2) ^ 2 ≤ R ^ 2)
    (hstrip : ∀ x ∈ A, |(r : ℝ) * (x.2 : ℝ) - (s : ℝ) * (x.1 : ℝ)| ≤ W) :
    (MeasureTheory.volume
        (convexHull ℝ ((A.image (fun x : ℤ × ℤ => ((x.1 : ℝ), (x.2 : ℝ)))) : Set (ℝ × ℝ)))).toReal
      ≤ 4 * R * (W / Real.sqrt ((r : ℝ) ^ 2 + (s : ℝ) ^ 2)) := by
  have hd : 0 < (r : ℝ) ^ 2 + (s : ℝ) ^ 2 := by
    rcases hne with h | h
    · have : (r : ℝ) ≠ 0 := by exact_mod_cast h
      nlinarith [sq_pos_of_ne_zero this, sq_nonneg (s : ℝ)]
    · have : (s : ℝ) ≠ 0 := by exact_mod_cast h
      nlinarith [sq_pos_of_ne_zero this, sq_nonneg (r : ℝ)]
  have hsub : ((A.image (fun x : ℤ × ℤ => ((x.1 : ℝ), (x.2 : ℝ)))) : Set (ℝ × ℝ)) ⊆
      {p : ℝ × ℝ | (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 ≤ R ^ 2} ∩
        {p : ℝ × ℝ | |(r : ℝ) * p.2 - (s : ℝ) * p.1| ≤ W} := by
    intro p hp
    rw [Finset.mem_coe, Finset.mem_image] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    exact ⟨hball a ha, hstrip a ha⟩
  have hconv : Convex ℝ ({p : ℝ × ℝ | (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 ≤ R ^ 2} ∩
        {p : ℝ × ℝ | |(r : ℝ) * p.2 - (s : ℝ) * p.1| ≤ W}) :=
    (convex_disk c R).inter (convex_strip (r : ℝ) (s : ℝ) W)
  have hSc : convexHull ℝ ((A.image (fun x : ℤ × ℤ => ((x.1 : ℝ), (x.2 : ℝ)))) : Set (ℝ × ℝ))
      ⊆ {p : ℝ × ℝ | (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 ≤ R ^ 2} ∩
        {p : ℝ × ℝ | |(r : ℝ) * p.2 - (s : ℝ) * p.1| ≤ W} :=
    (Convex.convexHull_subset_iff hconv).mpr hsub
  have hmain := volume_le_of_subset_disk_strip (r : ℝ) (s : ℝ) R W hR hW hd c
      (convexHull ℝ ((A.image (fun x : ℤ × ℤ => ((x.1 : ℝ), (x.2 : ℝ)))) : Set (ℝ × ℝ))) hSc
  have hfin : (ENNReal.ofReal (4 * R * (W / Real.sqrt ((r : ℝ) ^ 2 + (s : ℝ) ^ 2)))).toReal
      = 4 * R * (W / Real.sqrt ((r : ℝ) ^ 2 + (s : ℝ) ^ 2)) := by
    rw [ENNReal.toReal_ofReal]
    positivity
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
  rw [hfin] at hle
  exact hle

end

end Work.FIArea6b
