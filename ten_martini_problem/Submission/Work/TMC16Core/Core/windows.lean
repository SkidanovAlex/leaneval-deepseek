import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.lemma_9_2

/-!
# The two windows of the localization estimate (AJ §9, `pd_window`)

For the localization estimate we need, for every sufficiently large site `y`, a scale `K`,
(a) a set `I₂` of sites in the *balanced* window around `y` (`3K ≤ 10 (y-x) ≤ 7K` and
`K ≤ 40 (x+K-1-y)`), which is what makes the Cramér/Green step produce a positive rate, and
(b) a set `I₁` of sites in the interval `[-(13/16)K, -(3/16)K]` around `0` — whose continuants
are exponentially small, produced either by the singularity of `0` (AJ Lemma 9.2 with
`δ = 3/16`) or, in the resonant case, by AJ's Lemma 9.11 (whose `A`-block
`[-13q_n/8, -3q_n/8]` is exactly `[-(13/16)(K+1), -(3/16)(K+1)]` for `K = 2q_n-1`) —
with `|I₁| + |I₂| = K+1`, so that the non-generation lemma (AJ Lemma 9.3) applies to the
`K+1` phases.

`I₁` is the *leftmost* part of `[-(13/16)K, -(3/16)K]` and `I₂` the balanced window with
three points removed from its left end, which guarantees disjointness in all geometries (in
particular for `y ≈ K/2`, which occurs in the resonant case with `ℓ = 1`).
-/

noncomputable section

namespace Work.TMC16Core.Core

open Work.TMC16Core

/-- `⌊7K/10⌋`. -/
def b7 (K : ℕ) : ℤ := ⌊(7 : ℝ) * (K : ℝ) / 10⌋

/-- `⌈3K/10⌉`. -/
def b3 (K : ℕ) : ℤ := ⌈(3 : ℝ) * (K : ℝ) / 10⌉

/-- `⌊13K/16⌋` (the left end of the `A`-window is `-b1316 K`). -/
def b1316 (K : ℕ) : ℤ := ⌊(13 : ℝ) * (K : ℝ) / 16⌋

/-- `⌈3K/16⌉` (the right end of the `A`-window is `-b316 K`). -/
def b316 (K : ℕ) : ℤ := ⌈(3 : ℝ) * (K : ℝ) / 16⌉

/-- The balanced window around the site `y`, with three points of slack at its left end. -/
def I2set (y : ℤ) (K : ℕ) : Finset ℤ := Finset.Icc (y - b7 K + 3) (y - b3 K)

/-- The number of sites in `I₂`. -/
def m2 (K : ℕ) : ℤ := b7 K - b3 K - 2

/-- The number of sites in `I₁`, namely `K+1-|I₂|`. -/
def n1 (K : ℕ) : ℤ := (K : ℤ) + 1 - m2 K

/-- The `A`-interval `[-(13/16)K, -(3/16)K]` of the singularity estimates (AJ Lemma 9.2). -/
def A2blk (K : ℕ) : Finset ℤ := Finset.Icc (-b1316 K) (-b316 K)

/-- The first window: the leftmost `K+1-|I₂|` sites of `A2blk K`. -/
def I1set (K : ℕ) : Finset ℤ := Finset.Icc (-b1316 K) (-b1316 K + n1 K - 1)

lemma ten_mul_b7_le (K : ℕ) : 10 * b7 K ≤ 7 * (K : ℤ) := by
  have h : ((b7 K : ℤ) : ℝ) ≤ (7 : ℝ) * (K : ℝ) / 10 := by
    rw [b7]; exact Int.floor_le _
  have h' : 10 * ((b7 K : ℤ) : ℝ) ≤ 7 * (K : ℝ) := by linarith
  exact_mod_cast h'

lemma b3_le_ten_mul (K : ℕ) : 3 * (K : ℤ) ≤ 10 * b3 K := by
  have h : (3 : ℝ) * (K : ℝ) / 10 ≤ ((b3 K : ℤ) : ℝ) := by
    rw [b3]; exact Int.le_ceil _
  have h' : 3 * (K : ℝ) ≤ 10 * ((b3 K : ℤ) : ℝ) := by linarith
  exact_mod_cast h'

lemma m2_bounds {K : ℕ} (hK : 240 ≤ K) : 0 ≤ m2 K ∧ m2 K ≤ (K : ℤ) + 1 := by
  have hb7' : ((b7 K : ℤ) : ℝ) ≤ 7 * (K : ℝ) / 10 := Int.floor_le _
  have hb3' : (3 : ℝ) * (K : ℝ) / 10 ≤ ((b3 K : ℤ) : ℝ) := Int.le_ceil _
  have hb7'' : (7 : ℝ) * (K : ℝ) / 10 < ((b7 K : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hb3'' : ((b3 K : ℤ) : ℝ) < (3 : ℝ) * (K : ℝ) / 10 + 1 := Int.ceil_lt_add_one _
  have hK' : (240 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hcast : (((m2 K : ℤ) : ℝ)) = ((b7 K : ℤ) : ℝ) - ((b3 K : ℤ) : ℝ) - 2 := by
    unfold m2; push_cast; ring
  constructor
  · have : (0:ℝ) ≤ ((m2 K : ℤ) : ℝ) := by rw [hcast]; linarith
    exact_mod_cast this
  · have : ((m2 K : ℤ) : ℝ) ≤ (((K : ℤ) + 1 : ℤ) : ℝ) := by rw [hcast]; push_cast; linarith
    exact_mod_cast this

lemma n1_bounds {K : ℕ} (hK : 240 ≤ K) : 0 ≤ n1 K ∧ n1 K ≤ (K : ℤ) + 1 := by
  obtain ⟨h1, h2⟩ := m2_bounds hK
  unfold n1
  constructor <;> omega

lemma card_I2set (y : ℤ) (K : ℕ) : (I2set y K).card = (m2 K).toNat := by
  rw [I2set, Int.card_Icc]
  unfold m2
  ring_nf

lemma card_I1set (K : ℕ) : (I1set K).card = (n1 K).toNat := by
  rw [I1set, Int.card_Icc]
  ring_nf

/-- The balanced conditions (AJ §9) for the sites of `I₂`. -/
lemma I2set_balanced {y : ℤ} {K : ℕ} {x : ℤ} (hx : x ∈ I2set y K) :
    3 * (K : ℤ) ≤ 10 * (y - x) ∧ 10 * (y - x) ≤ 7 * (K : ℤ) ∧
      (K : ℤ) ≤ 40 * ((x + (K : ℤ) - 1) - y) := by
  have hb7 := ten_mul_b7_le K
  have hb3 := b3_le_ten_mul K
  simp only [I2set, Finset.mem_Icc] at hx
  obtain ⟨h1, h2⟩ := hx
  refine ⟨by omega, by omega, by omega⟩

/-- `I₁` is contained in `A2blk K`. -/
lemma I1set_subset_A2blk {K : ℕ} (hK : 240 ≤ K) : I1set K ⊆ A2blk K := by
  have hb7lo : ((b7 K : ℤ) : ℝ) > 7 * (K : ℝ) / 10 - 1 := by
    have := Int.lt_floor_add_one ((7:ℝ) * (K:ℝ) / 10)
    rw [b7]; linarith [this]
  have hb3hi : ((b3 K : ℤ) : ℝ) < 3 * (K : ℝ) / 10 + 1 := by
    have := Int.ceil_lt_add_one ((3:ℝ) * (K:ℝ) / 10)
    rw [b3]; linarith [this]
  have hK' : (240 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hcast : ((n1 K : ℤ) : ℝ) = (K : ℝ) + 3 - ((b7 K : ℤ) : ℝ) + ((b3 K : ℤ) : ℝ) := by
    unfold n1 m2; push_cast; ring
  have hkeyR : ((n1 K : ℤ) : ℝ) ≤ (b1316 K : ℝ) - (b316 K : ℝ) + 1 := by
    have hL : (b1316 K : ℝ) > (13 : ℝ) * (K : ℝ) / 16 - 1 := by
      have := Int.lt_floor_add_one ((13:ℝ) * (K:ℝ)/16)
      rw [b1316]; linarith [this]
    have hC : (b316 K : ℝ) < (3 : ℝ) * (K : ℝ) / 16 + 1 := by
      have := Int.ceil_lt_add_one ((3:ℝ) * (K:ℝ)/16)
      rw [b316]; linarith [this]
    rw [hcast]
    nlinarith
  have hkey : n1 K ≤ b1316 K - b316 K + 1 := by exact_mod_cast hkeyR
  intro x hx
  simp only [I1set, A2blk, Finset.mem_Icc] at hx ⊢
  constructor <;> omega

lemma n1_pos {K : ℕ} (hK : 240 ≤ K) : 0 < n1 K := by
  have hb7' : ((b7 K : ℤ) : ℝ) ≤ 7 * (K : ℝ) / 10 := Int.floor_le _
  have hb3' : (3 : ℝ) * (K : ℝ) / 10 ≤ ((b3 K : ℤ) : ℝ) := Int.le_ceil _
  have hK' : (240 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hcast : ((n1 K : ℤ) : ℝ) = (K : ℝ) + 3 - ((b7 K : ℤ) : ℝ) + ((b3 K : ℤ) : ℝ) := by
    unfold n1 m2; push_cast; ring
  have : (0:ℝ) < ((n1 K : ℤ) : ℝ) := by rw [hcast]; linarith
  exact_mod_cast this

/-- `I₁` and `I₂` are disjoint when `y` is large enough (hypothesis: `I₁.max < I₂.min`). -/
lemma disjoint_I1_I2 {y : ℤ} {K : ℕ} (h : -b1316 K + n1 K - 1 < y - b7 K + 3) :
    Disjoint (I1set K) (I2set y K) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [I1set, Finset.mem_Icc] at hx1
  simp only [I2set, Finset.mem_Icc] at hx2
  omega

lemma card_union_I1_I2 {y : ℤ} {K : ℕ} (hK : 240 ≤ K)
    (h : -b1316 K + n1 K - 1 < y - b7 K + 3) :
    (I1set K ∪ I2set y K).card = K + 1 := by
  obtain ⟨hm1, hm2⟩ := m2_bounds hK
  obtain ⟨hn1, hn2⟩ := n1_bounds hK
  rw [Finset.card_union_of_disjoint (disjoint_I1_I2 h), card_I1set, card_I2set,
    ← Int.toNat_add hn1 hm1]
  have : n1 K + m2 K = (K : ℤ) + 1 := by unfold n1; ring
  rw [this]
  simp

/-! ## AJ's resonant windows (phase-index coordinates)

AJ's resonant case (`martini.tex`, Lemma `final` and Lemma `res`) uses the two
*phase-index* windows `J₁ = [-⌊5qₙ/8⌋, ⌊5qₙ/8⌋-1]` (centred at 0) and
`J₂ = [(ℓ-1)qₙ+⌊5qₙ/8⌋, (ℓ+1)qₙ-⌊5qₙ/8⌋-1]` (centred at `ℓ qₙ`).  Their union has
`2qₙ` elements, the "gap" between them is `(ℓ-1)qₙ` — a *multiple of `qₙ`* — and that is
exactly what makes AJ's uniformity estimate work (a gap that is not a multiple of `qₙ`
lets the free numerator phase excise `Θ(qₙ)` of the deficit; see `DESIGN.md`).

The phase index `j` is related to the *site* `x` by `j = x + (k-1)/2 = x + qₙ - 1`
(scale `k = 2qₙ-1`); the family used by `Uniform` is `θ + j α`. -/

/-- `⌊5q/8⌋`, the half-length parameter of AJ's resonant windows. -/
def resH (qn : ℕ) : ℕ := 5 * qn / 8

/-- AJ's first resonant window, in phase-index coordinates. -/
def J1res (qn : ℕ) : Finset ℤ := Finset.Icc (-(resH qn : ℤ)) ((resH qn : ℤ) - 1)

/-- AJ's second resonant window, in phase-index coordinates. -/
def J2res (qn ℓ : ℕ) : Finset ℤ :=
  Finset.Icc (((ℓ : ℤ) - 1) * (qn : ℤ) + (resH qn : ℤ))
    (((ℓ : ℤ) + 1) * (qn : ℤ) - (resH qn : ℤ) - 1)

/-- The same windows in *site* coordinates (`x = j - (qₙ-1)`). -/
def J1resSite (qn : ℕ) : Finset ℤ :=
  Finset.Icc (-(resH qn : ℤ) - (qn : ℤ) + 1) ((resH qn : ℤ) - (qn : ℤ))

/-- The same windows in *site* coordinates. -/
def J2resSite (qn ℓ : ℕ) : Finset ℤ :=
  Finset.Icc (((ℓ : ℤ) - 2) * (qn : ℤ) + (resH qn : ℤ) + 1)
    ((ℓ : ℤ) * (qn : ℤ) - (resH qn : ℤ))

/-- AJ's first resonant window in *site* coordinates, presented as the image of `J1res`
under `j ↦ j - (qₙ-1)`: this is exactly the shape `Core.Uniform_shift` consumes. -/
def I1res (qn : ℕ) : Finset ℤ := (J1res qn).image (fun j => j - ((qn : ℤ) - 1))

/-- AJ's second resonant window in *site* coordinates, as the image of `J2res`. -/
def I2res (qn ℓ : ℕ) : Finset ℤ := (J2res qn ℓ).image (fun j => j - ((qn : ℤ) - 1))

/-- The two resonant windows together (site coordinates). -/
def Ires (qn ℓ : ℕ) : Finset ℤ := I1res qn ∪ I2res qn ℓ

/-! ### AJ's resonant windows with a general half-length

`J1resG h` / `J2resG q h ℓ` are AJ's windows with the half-length `h` of `J₁` (and hence
`q n - h` of `J₂`) left free.  AJ take `h = ⌊5q/8⌋`, which exactly fills `A2blk (2q-1)`; the
freedom in `h` is what allows the common translate needed to fit `I₂` into `I2set y (2q-1)`
(see `DESIGN.md`, "the resonant window-fitting computation").  Keeping the *same* `h` in the
size of `J₁` and in the offset of `J₂` is what makes the gap `(ℓ-1)q` a multiple of `q`,
which the numerator estimate requires. -/

/-- AJ's first resonant window with half-length `h`, in phase-index coordinates. -/
def J1resG (h : ℕ) : Finset ℤ := Finset.Icc (-(h : ℤ)) ((h : ℤ) - 1)

/-- AJ's second resonant window with half-length `h`, in phase-index coordinates. -/
def J2resG (qn h ℓ : ℕ) : Finset ℤ :=
  Finset.Icc (((ℓ : ℤ) - 1) * (qn : ℤ) + (h : ℤ))
    (((ℓ : ℤ) + 1) * (qn : ℤ) - (h : ℤ) - 1)

/-- The first resonant window in site coordinates, as an image (for `Core.Uniform_shift`). -/
def I1resG (qn h : ℕ) : Finset ℤ := (J1resG h).image (fun j => j - ((qn : ℤ) - 1))

/-- The second resonant window in site coordinates, as an image. -/
def I2resG (qn h ℓ : ℕ) : Finset ℤ := (J2resG qn h ℓ).image (fun j => j - ((qn : ℤ) - 1))

end Work.TMC16Core.Core
