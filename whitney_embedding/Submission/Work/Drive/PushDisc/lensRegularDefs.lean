import Mathlib
import Submission.Work.Drive.Whitney.whitneyDiscDefs
import Submission.Work.Drive.PushDisc.milnorLens

/-!
# The `L0` regularity machinery: the lens, its bumps and the bad parameter sets

This file sets up the data of the lead's `L0` (`exists_regularDisc`, see
`Drive/PushDisc/NOTES_LEAD_L0.md`): the *lens* region between the `x`-axis and the arch
`arch x = 1 - x ^ 2` over `|x| ≤ 1`, a family of four smooth bumps on it vanishing on the two
edges, the perturbed map `lensMap Δ₀ ρ v = Δ₀ + Σ k, lensBump k • v k`, and the four "bad"
parameter sets (immersion, injectivity, and the two collar-transversality conditions).

The bumps are *polynomial* in `(x, y)` off the cutoff:

    lensBump ρ (i,j) (x,y) = lensChi ρ x * lensAlpha j x * lensZeta i y (arch x)

with `lensChi ρ x = smoothTransition ((1 - x^2)/ρ)` (identically `0` for `|x| ≥ 1`, identically `1`
for `1 - x^2 ≥ ρ`), `lensAlpha 0 x = 1 - x^2`, `lensAlpha 1 x = (1 - x^2)(1+x)`,
`lensZeta 0 y u = y (u - y)`, `lensZeta 1 y u = y (u - y)^2`.

The two `lensZeta`s satisfy `lensZeta 1 = lensZeta 0 * (u - y)`, which is what gives both the
point separation on the open lens and the *injectivity of the derivative-coefficient map*

    (U,W) ↦ (U * ∂ₓ (lensBump k) p 1 + W * ∂_y (lensBump k) p 1)_k

needed for the immersion-bad-set dimension count: it holds as soon as `∃ k, ∂ₓ (lensBump k) p ≠ 0`,
which holds at every point of `lensOpen` (see `lensBump_coeff_injective`).
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff ENNReal
open Set Metric MeasureTheory Topology Filter

noncomputable section

/-- The closed lens: between the `x`-axis and the arch, over `|x| ≤ 1`. -/
def lens : Set (ℝ × ℝ) := {p | |p.1| ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ arch p.1}

/-- The open lens (the region where all the bumps are nondegenerate). -/
def lensOpen : Set (ℝ × ℝ) := {p | |p.1| < 1 ∧ 0 < p.2 ∧ p.2 < arch p.1}

theorem lensOpen_subset_lens : lensOpen ⊆ lens := by
  rintro ⟨x, y⟩ ⟨hx, hy0, hy1⟩
  exact ⟨le_of_lt hx, le_of_lt hy0, le_of_lt hy1⟩

/-- The plateau cutoff: `lensChi ρ x = 0` for `|x| ≥ 1` and `= 1` for `1 - x^2 ≥ ρ`. -/
def lensChi (ρ x : ℝ) : ℝ := Real.smoothTransition ((1 - x ^ 2) / ρ)

theorem lensChi_eq_zero_of_one_le_abs {ρ x : ℝ} (hρ : 0 < ρ) (hx : 1 ≤ |x|) :
    lensChi ρ x = 0 := by
  rw [lensChi, Real.smoothTransition.zero_iff_nonpos]
  have h : x ^ 2 ≥ 1 := by
    have h2 : (1 : ℝ) ^ 2 ≤ |x| ^ 2 := by nlinarith [hx, abs_nonneg x]
    simpa [sq_abs] using h2
  exact div_nonpos_of_nonpos_of_nonneg (by linarith [h]) hρ.le

theorem lensChi_pos_of_abs_lt_one {ρ x : ℝ} (hρ : 0 < ρ) (hx : |x| < 1) :
    0 < lensChi ρ x := by
  rw [lensChi]
  have h : x ^ 2 < 1 := by
    rw [abs_lt] at hx; nlinarith [hx.1, hx.2]
  exact Real.smoothTransition.pos_of_pos (div_pos (by linarith [h]) hρ)

theorem lensChi_one_of_le {ρ x : ℝ} (hρ : 0 < ρ) (h : ρ ≤ 1 - x ^ 2) : lensChi ρ x = 1 := by
  rw [lensChi, Real.smoothTransition.one_of_one_le]
  exact (one_le_div hρ).mpr h

theorem contDiff_lensChi {ρ : ℝ} : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lensChi ρ) := by
  unfold lensChi; fun_prop

/-- The `x`-factors of the bumps: `lensAlpha 0 x = 1 - x^2`, `lensAlpha 1 x = (1-x^2)(1+x)`. -/
def lensAlpha (j : Fin 2) (x : ℝ) : ℝ :=
  if j = 0 then 1 - x ^ 2 else (1 - x ^ 2) * (1 + x)

@[simp] theorem lensAlpha_zero_fun : lensAlpha 0 = fun x : ℝ => 1 - x ^ 2 := by
  funext x; rw [lensAlpha, if_pos rfl]

@[simp] theorem lensAlpha_one_fun : lensAlpha 1 = fun x : ℝ => (1 - x ^ 2) * (1 + x) := by
  funext x; rw [lensAlpha, if_neg (by decide : (1 : Fin 2) ≠ 0)]

theorem contDiff_lensAlpha (j : Fin 2) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lensAlpha j) := by
  by_cases h : j = 0
  · rw [h, lensAlpha_zero_fun]; fun_prop
  · have hj : j = 1 := by omega
    rw [hj, lensAlpha_one_fun]; fun_prop

theorem lensAlpha_ne_zero {j : Fin 2} {x : ℝ} (hx : |x| < 1) : lensAlpha j x ≠ 0 := by
  have h2 : 0 < 1 - x ^ 2 := by rw [abs_lt] at hx; nlinarith [hx.1, hx.2]
  by_cases h : j = 0
  · rw [h, lensAlpha_zero_fun]; exact ne_of_gt h2
  · have hj : j = 1 := by omega
    rw [hj, lensAlpha_one_fun]
    exact mul_ne_zero (ne_of_gt h2) (by linarith [(abs_lt.mp hx).1])

/-- The ratio of the two `x`-factors: `lensAlpha 1 x / lensAlpha 0 x = 1 + x`. -/
theorem lensAlpha_ratio {x : ℝ} (hx : |x| < 1) :
    lensAlpha 1 x = (1 + x) * lensAlpha 0 x := by
  have h2 : 0 < 1 - x ^ 2 := by rw [abs_lt] at hx; nlinarith [hx.1, hx.2]
  have hne : lensAlpha 0 x ≠ 0 := lensAlpha_ne_zero (j := 0) hx
  rw [lensAlpha_zero_fun, lensAlpha_one_fun]
  field_simp

/-- Radial separation of the `x`-factors. -/
theorem lensAlpha_radial {x y c : ℝ} (hx : |x| < 1) (hy : |y| < 1) (hc : 0 < c)
    (h0 : lensAlpha 0 y = c * lensAlpha 0 x) (h1 : lensAlpha 1 y = c * lensAlpha 1 x) :
    x = y := by
  have hny : lensAlpha 0 y ≠ 0 := lensAlpha_ne_zero (j := 0) hy
  have e1 : (1 + y) * lensAlpha 0 y = c * lensAlpha 1 x := by
    rw [← h1, lensAlpha_ratio hy]
  have e2 : (1 + y) * lensAlpha 0 y = (1 + x) * lensAlpha 0 y := by
    rw [e1, lensAlpha_ratio hx, h0]; ring
  have h3 : 1 + y = 1 + x := mul_right_cancel₀ hny e2
  linarith

/-- The `y`-shapes of the bumps, as polynomials in `(y, u)` with `u = arch x`:

    `lensZeta 0 y u = y (u - y)`,  `lensZeta 1 y u = y (u - y) (1 + u - y)`.

Both vanish on the two edges `y = 0` and `y = u`; `lensZeta 1 = lensZeta 0 * (1 + u - y)`. -/
def lensZeta (i : Fin 2) (y u : ℝ) : ℝ :=
  if i = 0 then y * (u - y) else y * (u - y) * (1 + u - y)

@[simp] theorem lensZeta_zero_fun :
    lensZeta 0 = fun y u : ℝ => y * (u - y) := by
  funext y u; rw [lensZeta, if_pos rfl]

@[simp] theorem lensZeta_one_fun :
    lensZeta 1 = fun y u : ℝ => y * (u - y) * (1 + u - y) := by
  funext y u; rw [lensZeta, if_neg (by decide : (1 : Fin 2) ≠ 0)]

theorem lensZeta_one_eq (y u : ℝ) :
    lensZeta 1 y u = lensZeta 0 y u * (1 + (u - y)) := by
  rw [lensZeta_zero_fun, lensZeta_one_fun]; ring

theorem contDiff_lensZeta (i : Fin 2) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => lensZeta i p.1 p.2) := by
  by_cases h : i = 0
  · rw [h, lensZeta_zero_fun]; fun_prop
  · have hi : i = 1 := by omega
    rw [hi, lensZeta_one_fun]; fun_prop

theorem lensZeta_pos {i : Fin 2} {y u : ℝ} (h0 : 0 < y) (h1 : y < u) :
    0 < lensZeta i y u := by
  have hu : 0 < u - y := by linarith
  by_cases h : i = 0
  · rw [h, lensZeta_zero_fun]; positivity
  · have hi : i = 1 := by omega
    rw [hi, lensZeta_one_fun]
    exact mul_pos (mul_pos h0 hu) (by linarith)

theorem lensZeta_ne_zero {i : Fin 2} {y u : ℝ} (h0 : 0 < y) (h1 : y < u) :
    lensZeta i y u ≠ 0 := ne_of_gt (lensZeta_pos h0 h1)

/-- **The bumps of the lens**. -/
def lensBump (ρ : ℝ) (k : Fin 2 × Fin 2) (p : ℝ × ℝ) : ℝ :=
  lensChi ρ p.1 * lensAlpha k.2 p.1 * lensZeta k.1 p.2 (arch p.1)

/-- The generic perturbation. -/
def lensPert {n : ℕ} (ρ : ℝ) (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n)))
    (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin (2 * n)) :=
  ∑ k : Fin 2 × Fin 2, lensBump ρ k p • v k

/-- The perturbed map. -/
def lensMap {n : ℕ} (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (ρ : ℝ)
    (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) :
    ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n)) :=
  fun p => Δ₀ p + lensPert ρ v p

theorem lensBump_eq_zero_bot (ρ : ℝ) (k : Fin 2 × Fin 2) (x : ℝ) :
    lensBump ρ k (x, 0) = 0 := by
  simp only [lensBump, lensZeta]
  by_cases h : k.1 = 0
  · rw [if_pos h]; ring
  · rw [if_neg h]; ring

theorem lensBump_eq_zero_top (ρ : ℝ) (k : Fin 2 × Fin 2) (x : ℝ) :
    lensBump ρ k (x, arch x) = 0 := by
  simp only [lensBump, lensZeta]
  by_cases h : k.1 = 0
  · rw [if_pos h]; ring
  · rw [if_neg h]; ring

theorem lensBump_eq_zero_of_abs_one_le {ρ x : ℝ} (hρ : 0 < ρ) {y : ℝ}
    (hx : 1 ≤ |x|) {k : Fin 2 × Fin 2} : lensBump ρ k (x, y) = 0 := by
  rw [lensBump, lensChi_eq_zero_of_one_le_abs hρ hx, zero_mul, zero_mul]

theorem lensPert_eq_zero_bot {n : ℕ} (ρ : ℝ)
    (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) (x : ℝ) :
    lensPert ρ v (x, 0) = 0 := by
  simp only [lensPert]
  exact Finset.sum_eq_zero fun k _ => by rw [lensBump_eq_zero_bot, zero_smul]

theorem lensPert_eq_zero_top {n : ℕ} (ρ : ℝ)
    (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) (x : ℝ) :
    lensPert ρ v (x, arch x) = 0 := by
  simp only [lensPert]
  exact Finset.sum_eq_zero fun k _ => by rw [lensBump_eq_zero_top, zero_smul]

theorem contDiff_lensBump (ρ : ℝ) (k : Fin 2 × Fin 2) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lensBump ρ k) := by
  rw [show lensBump ρ k = fun p : ℝ × ℝ =>
      lensChi ρ p.1 * lensAlpha k.2 p.1 * lensZeta k.1 p.2 (arch p.1) from rfl]
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => lensChi ρ p.1) :=
    contDiff_lensChi.comp contDiff_fst
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => lensAlpha k.2 p.1) :=
    (contDiff_lensAlpha k.2).comp contDiff_fst
  have harch : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => arch p.1) := by
    rw [show (fun p : ℝ × ℝ => arch p.1) = fun p : ℝ × ℝ => 1 - p.1 ^ 2 from rfl]
    fun_prop
  have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => lensZeta k.1 p.2 (arch p.1)) :=
    (contDiff_lensZeta k.1).comp (contDiff_snd.prodMk harch)
  exact (h1.mul h2).mul h3

/-- **Point separation of the bumps on the open lens.** -/
theorem lensBump_sep {ρ : ℝ} (hρ : 0 < ρ) {p q : ℝ × ℝ} (hp : p ∈ lensOpen)
    (hq : q ∈ lensOpen) (h : ∀ k : Fin 2 × Fin 2, lensBump ρ k p = lensBump ρ k q) :
    p = q := by
  obtain ⟨px, py⟩ := p
  obtain ⟨qx, qy⟩ := q
  obtain ⟨hpx, hpy0, hpy1⟩ := hp
  obtain ⟨hqx, hqy0, hqy1⟩ := hq
  have h0eq : lensChi ρ px * lensAlpha 0 px * lensZeta 0 py (arch px)
      = lensChi ρ qx * lensAlpha 0 qx * lensZeta 0 qy (arch qx) := h (0, 0)
  have h1eq : lensChi ρ px * lensAlpha 1 px * lensZeta 0 py (arch px)
      = lensChi ρ qx * lensAlpha 1 qx * lensZeta 0 qy (arch qx) := h (0, 1)
  set A := lensChi ρ px * lensZeta 0 py (arch px) with hA
  set B := lensChi ρ qx * lensZeta 0 qy (arch qx) with hB
  have hApos : 0 < A := by
    rw [hA]
    exact mul_pos (lensChi_pos_of_abs_lt_one hρ hpx) (lensZeta_pos hpy0 hpy1)
  have hBpos : 0 < B := by
    rw [hB]
    exact mul_pos (lensChi_pos_of_abs_lt_one hρ hqx) (lensZeta_pos hqy0 hqy1)
  have e0 : lensAlpha 0 qx = (A / B) * lensAlpha 0 px := by
    have hBB : B * lensAlpha 0 qx = A * lensAlpha 0 px := by
      rw [hB, hA]; linear_combination -h0eq
    field_simp
    linarith [hBB]
  have e1 : lensAlpha 1 qx = (A / B) * lensAlpha 1 px := by
    have hBB : B * lensAlpha 1 qx = A * lensAlpha 1 px := by
      rw [hB, hA]; linear_combination -h1eq
    field_simp
    linarith [hBB]
  have hx : px = qx := lensAlpha_radial hpx hqx (div_pos hApos hBpos) e0 e1
  subst hx
  -- the `y`-coordinates
  have hpx' : |px| < 1 := hpx
  have g0 : lensChi ρ px * lensAlpha 0 px * lensZeta 0 py (arch px)
      = lensChi ρ px * lensAlpha 0 px * lensZeta 0 qy (arch px) := h (0, 0)
  have g1 : lensChi ρ px * lensAlpha 0 px * lensZeta 1 py (arch px)
      = lensChi ρ px * lensAlpha 0 px * lensZeta 1 qy (arch px) := h (1, 0)
  have hc0 : lensChi ρ px * lensAlpha 0 px ≠ 0 :=
    mul_ne_zero (ne_of_gt (lensChi_pos_of_abs_lt_one hρ hpx')) (lensAlpha_ne_zero (j := 0) hpx')
  have z0 : lensZeta 0 py (arch px) = lensZeta 0 qy (arch px) := by
    rw [show lensChi ρ px * lensAlpha 0 px * lensZeta 0 py (arch px)
        = (lensChi ρ px * lensAlpha 0 px) * lensZeta 0 py (arch px) by ring,
      show lensChi ρ px * lensAlpha 0 px * lensZeta 0 qy (arch px)
        = (lensChi ρ px * lensAlpha 0 px) * lensZeta 0 qy (arch px) by ring] at g0
    exact mul_left_cancel₀ hc0 g0
  have z1 : lensZeta 1 py (arch px) = lensZeta 1 qy (arch px) := by
    rw [show lensChi ρ px * lensAlpha 0 px * lensZeta 1 py (arch px)
        = (lensChi ρ px * lensAlpha 0 px) * lensZeta 1 py (arch px) by ring,
      show lensChi ρ px * lensAlpha 0 px * lensZeta 1 qy (arch px)
        = (lensChi ρ px * lensAlpha 0 px) * lensZeta 1 qy (arch px) by ring] at g1
    exact mul_left_cancel₀ hc0 g1
  have hzq : lensZeta 0 qy (arch px) ≠ 0 := by
    rw [← z0]; exact lensZeta_ne_zero hpy0 (by simpa using hpy1)
  have hy : py = qy := by
    rw [lensZeta_one_eq, lensZeta_one_eq, z0] at z1
    have := mul_left_cancel₀ hzq z1
    linarith
  subst hy
  rfl

end

end Work.Drive.PushDisc
