/-
  WilG4c — definitions for the §5.4 reduction `StepHigher` (BNZ §5.4, "controlling higher
  derivatives").

  `StepHigher` reduces `FLemP PYLipDef → FLemP PYLip` by (i) choosing near-maximising curves
  `γ_{i,α}`, (ii) pulling the family back along the affine `x`-charts `φ_η` produced by
  BNZ Corollary 19 (our `F1Affine`), and (iii) a final *diagonal* subdivision of the cube,
  which turns the bounds `|∂^α| = O_n(r^{|α|})` into operator norms `≤ 1` (BNZ Lemma 5.4,
  our `TnormRescale`; here `subdiv_normle`).

  This file fixes the subdivision.  For `N ≥ 1` and `s : Fin (n+1) → Fin (3(N-1)+1)` the map

      `subdivMap N s t = fun j => ((s j : ℝ) + 3 * t j) / (3 * N)`

  is the diagonal affine map `t ↦ b + (1/N) • t` with `b j = (s j)/(3N)`; its image is the cube
  `Π_j ( s j /(3N), s j /(3N) + 1/N )`, which lies strictly inside `openCube (n+1)`, and the
  images over all `s` cover `openCube (n+1)`.  The number of maps is `(3N-2)^(n+1)`, a
  polynomial in `N` (and hence in `r`, since `N = ⌈K r⌉`).
-/
import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.Engine
import Submission.Work.WilG4c.LipDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- The number of distinguished (`x`-)directions of a multiindex, i.e. the number of entries
equal to `0 : Fin (n+1)`. -/
def xcount {n : ℕ} (L : List (Fin (n + 1))) : ℕ := (L.filter (fun i => decide (i = 0))).length

@[simp] theorem xcount_nil {n : ℕ} : xcount (n := n) [] = 0 := rfl

theorem xcount_le_length {n : ℕ} (L : List (Fin (n + 1))) : xcount L ≤ L.length :=
  List.length_filter_le _ _

/-! ## Multiindices of BNZ §5.4 as lists of ambient directions

BNZ §5.4 chooses one curve `γ_{i,α}` for each multiindex `α` with `|α| ≤ r`.  We index `α` by
its `x`-length `j` and its `y`-part `M`, so that the associated derivative is
`iterDir (midx p n j M)`.  Keeping the `x`-directions on the left is what makes the engine
`tnorm_curve_system_w` applicable. -/

/-- The multiindex `(j, M)` of BNZ §5.4 as a list of ambient directions of `ℝ^{p+(n+1)}`:
`j` copies of the `x`-direction followed by the `y`-directions of `M`. -/
def midx (p n : ℕ) (j : ℕ) (M : List (Fin n)) : List (Fin (p + (n + 1))) :=
  List.replicate j (xDirHat p n) ++ M.map (fun i : Fin n => Fin.natAdd p i.succ)

@[simp] theorem midx_length (p n j M) : (midx p n j M).length = j + M.length := by
  simp [midx, add_comm]

/-- The threshold alternative for the `γ`-choice of BNZ §5.4: either the chosen point does not
satisfy the near-maximality condition, or it is a near-maximiser of `∂^{(j,M)}` over the
`C^{j+|M|}`-locus of the fibre.  (`2E` rather than `E` so that an engine bound `|∂^α| ≤ E` at the
chosen point rules the non-generic alternative out, forcing the near-maximiser property.) -/
def threshAlt (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (j : ℕ) (M : List (Fin n))
    (E : ℝ) (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) : Prop :=
  (iterDir (midx p n j M) (famFunHat f) (xPt l x y) ≥ 2 * E ∨
    iterDir (midx p n j M) (famFunHat f) (xPt l x y) ≤ -(2 * E) ∨
    ∀ y' : Fin n → ℝ, y' ∈ openCube n →
      xPt l x y' ∈ interior {z | ContDiffAt ℝ (j + M.length) (famFunHat f) z} →
      |iterDir (midx p n j M) (famFunHat f) (xPt l x y')| ≤
        2 * |iterDir (midx p n j M) (famFunHat f) (xPt l x y)|)

/-- The threshold alternative together with an engine bound `|∂^{(j,M)}| ≤ E` at the chosen
point forces the near-maximiser property: the two "large value" disjuncts of `threshAlt` are
incompatible with `|∂^{(j,M)}| ≤ E` because `E < 2E`. -/
theorem threshAlt_nearmax {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ} {j : ℕ}
    {M : List (Fin n)} {E : ℝ} (hE : 0 < E) {l : Fin p → ℝ} {x : ℝ} {y : Fin n → ℝ}
    (hT : threshAlt p n f j M E l x y)
    (hb : |iterDir (midx p n j M) (famFunHat f) (xPt l x y)| ≤ E) :
    ∀ y' : Fin n → ℝ, y' ∈ openCube n →
      xPt l x y' ∈ interior {z | ContDiffAt ℝ (j + M.length) (famFunHat f) z} →
      |iterDir (midx p n j M) (famFunHat f) (xPt l x y')| ≤
        2 * |iterDir (midx p n j M) (famFunHat f) (xPt l x y)| := by
  rcases hT with h1 | h2 | h3
  · exfalso
    rw [abs_of_nonneg (by linarith :
      (0 : ℝ) ≤ iterDir (midx p n j M) (famFunHat f) (xPt l x y))] at hb
    linarith
  · exfalso
    rw [abs_of_nonpos (by linarith :
      iterDir (midx p n j M) (famFunHat f) (xPt l x y) ≤ 0)] at hb
    linarith
  · exact h3

/-- The ambient lift of a cube direction list: a cube direction `c : Fin (n+1)` becomes the
ambient direction `Fin.natAdd p c` (the parameter directions are untouched). -/
def liftDir {p n : ℕ} (L : List (Fin (n + 1))) : List (Fin (p + (n + 1))) :=
  L.map (Fin.natAdd p)

/-- `threshAltL` is `threshAlt` indexed by an arbitrary cube multiindex `L` instead of by the
canonical `(j, M)` split: the derivative is `iterDir (liftDir L) (famFunHat f)`, i.e. the
multiindex `L` read in ambient coordinates. -/
def threshAltL (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (n + 1))) (E : ℝ) (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) : Prop :=
  (iterDir (liftDir L) (famFunHat f) (xPt l x y) ≥ 2 * E ∨
    iterDir (liftDir L) (famFunHat f) (xPt l x y) ≤ -(2 * E) ∨
    ∀ y' : Fin n → ℝ, y' ∈ openCube n →
      xPt l x y' ∈ interior {z | ContDiffAt ℝ L.length (famFunHat f) z} →
      |iterDir (liftDir L) (famFunHat f) (xPt l x y')| ≤
        2 * |iterDir (liftDir L) (famFunHat f) (xPt l x y)|)

/-- The threshold alternative together with an engine bound at the chosen point forces the
near-maximiser property (multiindex form). -/
theorem threshAltL_nearmax {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {L : List (Fin (n + 1))} {E : ℝ} (hE : 0 < E) {l : Fin p → ℝ} {x : ℝ} {y : Fin n → ℝ}
    (hT : threshAltL p n f L E l x y)
    (hb : |iterDir (liftDir L) (famFunHat f) (xPt l x y)| ≤ E) :
    ∀ y' : Fin n → ℝ, y' ∈ openCube n →
      xPt l x y' ∈ interior {z | ContDiffAt ℝ L.length (famFunHat f) z} →
      |iterDir (liftDir L) (famFunHat f) (xPt l x y')| ≤
        2 * |iterDir (liftDir L) (famFunHat f) (xPt l x y)| := by
  rcases hT with h1 | h2 | h3
  · exfalso
    rw [abs_of_nonneg (by linarith :
      (0 : ℝ) ≤ iterDir (liftDir L) (famFunHat f) (xPt l x y))] at hb
    linarith
  · exfalso
    rw [abs_of_nonpos (by linarith :
      iterDir (liftDir L) (famFunHat f) (xPt l x y) ≤ 0)] at hb
    linarith
  · exact h3

/-- Finite-sum subadditivity of the jet norm: `‖Σᵢ fᵢ‖_{T,r} ≤ Σᵢ ‖fᵢ‖_{T,r}` at a point.
This is `WilkiesDesign.CG.tnorm_add_le` iterated over a `Finset`. -/
theorem tnorm_sum_le {ι E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℕ) (s : Finset ι) (f : ι → E → ℝ) (x : E) (hf : ∀ i, ContDiffAt ℝ r (f i) x) :
    tnorm r (fun y => ∑ i ∈ s, f i y) x ≤ ∑ i ∈ s, tnorm r (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have : (fun y : E => (0 : ℝ)) = fun _ : E => (0 : ℝ) := rfl
    rw [this, tnorm_eq_sum_jetCoeff]
    simp [jetCoeff]
  | insert a s ha ih =>
    have hsplit : (fun y : E => ∑ i ∈ insert a s, f i y)
        = fun y : E => f a y + ∑ i ∈ s, f i y := by
      funext y; rw [Finset.sum_insert ha]
    have hsm : ContDiffAt ℝ (r : WithTop ℕ∞) (fun y : E => ∑ i ∈ s, f i y) x := by
      simpa using ContDiffAt.sum (s := s) (f := fun i (y : E) => f i y) (fun i _ => hf i)
    have h1 : tnorm r (fun y : E => f a y + ∑ i ∈ s, f i y) x
        ≤ tnorm r (f a) x + tnorm r (fun y : E => ∑ i ∈ s, f i y) x :=
      tnorm_add_le r (f a) (fun y : E => ∑ i ∈ s, f i y) x (hf a) hsm
    rw [hsplit, Finset.sum_insert ha]
    calc tnorm r (fun y : E => f a y + ∑ i ∈ s, f i y) x
        ≤ tnorm r (f a) x + tnorm r (fun y : E => ∑ i ∈ s, f i y) x := h1
      _ ≤ tnorm r (f a) x + ∑ i ∈ s, tnorm r (f i) x := add_le_add le_rfl ih

/-! ## The diagonal subdivision -/

/-- The number `N` of subdivision intervals: `N = ⌈K r⌉` where
`K = 2 e (1 + n e) (n+1) + 1` (BNZ's constant, polluted by the `N^m` of the multilinear
expansion `norm_iteratedFDeriv_le_of_dirs`). -/
def subdivN (n r : ℕ) : ℕ :=
  Nat.ceil ((2 * Real.exp 1 * (1 + n * Real.exp 1) * ((n : ℝ) + 1) + 1) * (r : ℝ))

/-- The base point of the `s`-th subdivision cube. -/
def subdivBase {n : ℕ} (N : ℕ) (s : Fin (n + 1) → Fin (3 * (N - 1) + 1)) :
    Fin (n + 1) → ℝ :=
  fun j => ((s j : ℕ) : ℝ) / (3 * (N : ℝ))

/-- The `s`-th subdivision chart of the unit cube: the diagonal affine map
`t ↦ s/(3N) + t/N`. -/
def subdivMap {n : ℕ} (N : ℕ) (s : Fin (n + 1) → Fin (3 * (N - 1) + 1)) (t : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun j => (((s j : ℕ) : ℝ) + 3 * t j) / (3 * (N : ℝ))

theorem subdivMap_eq {n : ℕ} (N : ℕ) (s : Fin (n + 1) → Fin (3 * (N - 1) + 1))
    (t : Fin (n + 1) → ℝ) :
    subdivMap N s t = subdivBase N s + (N : ℝ)⁻¹ • t := by
  funext j
  simp only [subdivMap, subdivBase, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · have h3N : (3 * (N : ℝ)) ≠ 0 := by
      have : (0:ℝ) < (N:ℝ) := by exact_mod_cast h
      positivity
    field_simp

theorem subdivBase_nonneg {n : ℕ} (N : ℕ) (s : Fin (n + 1) → Fin (3 * (N - 1) + 1)) :
    ∀ j, 0 ≤ subdivBase N s j := by
  intro j
  exact div_nonneg (Nat.cast_nonneg _) (by positivity)

theorem subdivBase_lt {n : ℕ} {N : ℕ} (hN : 1 ≤ N)
    (s : Fin (n + 1) → Fin (3 * (N - 1) + 1)) : ∀ j, subdivBase N s j < 1 := by
  intro j
  have hsj : (s j : ℕ) ≤ 3 * (N - 1) := by
    have := (s j).2
    omega
  have hcast : ((3 * (N - 1) : ℕ) : ℝ) = 3 * (N : ℝ) - 3 := by
    rw [Nat.cast_mul, Nat.cast_sub hN, Nat.cast_one]
    ring
  have hle : (((s j : ℕ)) : ℝ) ≤ 3 * (N : ℝ) - 3 := by
    have : (((s j : ℕ)) : ℝ) ≤ ((3 * (N - 1) : ℕ) : ℝ) := by exact_mod_cast hsj
    rw [hcast] at this
    exact this
  have h3N : (0 : ℝ) < 3 * (N : ℝ) := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    linarith
  rw [subdivBase, div_lt_one h3N]
  linarith

/-- The subdivision chart maps the open cube strictly into itself. -/
theorem subdivMap_mem_openCube {n : ℕ} {N : ℕ} (hN : 1 ≤ N)
    (s : Fin (n + 1) → Fin (3 * (N - 1) + 1)) {t : Fin (n + 1) → ℝ}
    (ht : t ∈ openCube (n + 1)) : subdivMap N s t ∈ openCube (n + 1) := by
  intro j
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have ht1 : t j ∈ Set.Ioo (0 : ℝ) 1 := ht j
  -- `subdivBase N s j + 1/N ≤ 1`
  have hsum : subdivBase N s j + (N : ℝ)⁻¹ ≤ 1 := by
    have h3N : (0:ℝ) < 3 * (N:ℝ) := by linarith
    have hsj : (s j : ℕ) ≤ 3 * (N - 1) := by have := (s j).2; omega
    have hcast : (((s j : ℕ)) : ℝ) ≤ 3 * ((N : ℝ) - 1) := by
      have h : (((s j : ℕ)) : ℝ) ≤ ((3 * (N - 1) : ℕ) : ℝ) := by exact_mod_cast hsj
      rw [Nat.cast_mul, Nat.cast_sub hN, Nat.cast_one] at h
      simpa using h
    have key : subdivBase N s j + (N : ℝ)⁻¹
        = ((((s j : ℕ)) : ℝ) + 3) / (3 * (N : ℝ)) := by
      rw [subdivBase, show (N:ℝ)⁻¹ = 3 / (3 * (N:ℝ)) by field_simp, ← add_div]
    rw [key, div_le_one h3N]
    linarith
  rw [subdivMap_eq]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · have hb := subdivBase_nonneg N s j
    have : (0:ℝ) < (N:ℝ)⁻¹ * t j := mul_pos (inv_pos.mpr hNpos) ht1.1
    linarith
  · have : (N:ℝ)⁻¹ * t j < (N:ℝ)⁻¹ * 1 := mul_lt_mul_of_pos_left ht1.2 (inv_pos.mpr hNpos)
    have h2 : (N:ℝ)⁻¹ * 1 = (N:ℝ)⁻¹ := mul_one _
    linarith [hsum, this, h2]

/-- The coordinate `s_j` of a subdivision chart, chosen so that `3N z_j` lies in
`(s_j, s_j + 3)`. -/
theorem exists_subdivBase {n : ℕ} {N : ℕ} (hN : 1 ≤ N) {z : Fin (n + 1) → ℝ}
    (hz : z ∈ openCube (n + 1)) :
    ∃ s : Fin (n + 1) → Fin (3 * (N - 1) + 1),
      ∀ j, ((s j : ℕ) : ℝ) < 3 * (N : ℝ) * z j ∧ 3 * (N : ℝ) * z j < ((s j : ℕ) : ℝ) + 3 := by
  have key : ∀ j : Fin (n + 1), ∃ sj : Fin (3 * (N - 1) + 1),
      ((sj : ℕ) : ℝ) < 3 * (N : ℝ) * z j ∧ 3 * (N : ℝ) * z j < ((sj : ℕ) : ℝ) + 3 := by
    intro j
    have hz1 : z j ∈ Set.Ioo (0 : ℝ) 1 := hz j
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    set u : ℝ := 3 * (N : ℝ) * z j with hu
    have hu0 : 0 < u := by
      rw [hu]
      have : (0:ℝ) < 3 * (N:ℝ) := by linarith
      exact mul_pos this hz1.1
    have huN : u < 3 * (N : ℝ) := by rw [hu]; nlinarith [hz1.2]
    have hceil : (⌈u⌉₊ : ℝ) < u + 1 := Nat.ceil_lt_add_one (le_of_lt hu0)
    have hceilN : ⌈u⌉₊ ≤ 3 * N := Nat.ceil_le.mpr (by push_cast; linarith)
    by_cases h : ⌈u⌉₊ ≤ 3 * N - 2
    · have hlt : (((⌈u⌉₊ - 2 : ℕ)) : ℝ) < u := by
        by_cases hk : ⌈u⌉₊ ≤ 2
        · have hz' : ⌈u⌉₊ - 2 = 0 := by omega
          rw [hz']; simpa using hu0
        · have hkk : 2 ≤ ⌈u⌉₊ := by omega
          rw [Nat.cast_sub hkk]; push_cast; linarith
      have hgt : u < (((⌈u⌉₊ - 2 : ℕ)) : ℝ) + 3 := by
        have hk' : (⌈u⌉₊ : ℝ) ≤ (((⌈u⌉₊ - 2 : ℕ)) : ℝ) + 2 := by
          by_cases hk2 : ⌈u⌉₊ ≤ 2
          · have hz' : ⌈u⌉₊ - 2 = 0 := by omega
            rw [hz']; push_cast
            exact_mod_cast hk2
          · have h2 : 2 ≤ ⌈u⌉₊ := by omega
            rw [Nat.cast_sub h2]; push_cast; linarith
        linarith [Nat.le_ceil u]
      exact ⟨⟨⌈u⌉₊ - 2, by omega⟩, hlt, hgt⟩
    · have h3 : 3 * (N : ℝ) - 1 ≤ (⌈u⌉₊ : ℝ) := by
        have h2 : (3 * N - 1 : ℕ) ≤ ⌈u⌉₊ := by omega
        have hh : (((3 * N - 1 : ℕ)) : ℝ) ≤ (⌈u⌉₊ : ℝ) := by exact_mod_cast h2
        rwa [show (((3 * N - 1 : ℕ)) : ℝ) = 3 * (N : ℝ) - 1 from by
          rw [Nat.cast_sub (by omega : 1 ≤ 3 * N), Nat.cast_mul, Nat.cast_one]
          push_cast; ring] at hh
      have h4 : (⌈u⌉₊ : ℝ) - 1 < u := by linarith
      have hlt : (((3 * (N - 1) : ℕ)) : ℝ) < u := by
        have h5 : ((3 * (N - 1) : ℕ) : ℝ) = 3 * (N : ℝ) - 3 := by
          rw [Nat.cast_mul, Nat.cast_sub hN, Nat.cast_one]; ring
        rw [h5]; linarith
      have hgt : u < (((3 * (N - 1) : ℕ)) : ℝ) + 3 := by
        have h5 : ((3 * (N - 1) : ℕ) : ℝ) + 3 = 3 * (N : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_sub hN, Nat.cast_one]; push_cast; ring
        rw [h5]; exact huN
      exact ⟨⟨3 * (N - 1), by omega⟩, hlt, hgt⟩
  choose s hs using key
  exact ⟨s, hs⟩

/-- The subdivision maps cover the open cube. -/
theorem subdivMap_covers {n : ℕ} {N : ℕ} (hN : 1 ≤ N) {z : Fin (n + 1) → ℝ}
    (hz : z ∈ openCube (n + 1)) :
    ∃ s : Fin (n + 1) → Fin (3 * (N - 1) + 1), ∃ t ∈ openCube (n + 1), subdivMap N s t = z := by
  obtain ⟨s, hs⟩ := exists_subdivBase hN hz
  refine ⟨s, fun j => (3 * (N : ℝ) * z j - ((s j : ℕ) : ℝ)) / 3, fun j => ?_, ?_⟩
  · have h1 := (hs j).1
    have h2 := (hs j).2
    constructor <;> linarith
  · funext j
    have h3 : subdivMap N s (fun j => (3 * (N : ℝ) * z j - ((s j : ℕ) : ℝ)) / 3) j
        = (((s j : ℕ) : ℝ) + 3 * ((3 * (N : ℝ) * z j - ((s j : ℕ) : ℝ)) / 3))
            / (3 * (N : ℝ)) := rfl
    rw [h3]
    have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
    have h3N : (3 * (N : ℝ)) ≠ 0 := by positivity
    field_simp
    ring

/-- `N = subdivN n r` grows at least linearly in `r`. -/
theorem subdivN_ge (n r : ℕ) :
    (2 * Real.exp 1 * (1 + n * Real.exp 1) * ((n : ℝ) + 1) + 1) * (r : ℝ) ≤ (subdivN n r : ℝ) :=
  Nat.le_ceil _

theorem subdivN_pos {n r : ℕ} (hr : 1 ≤ r) : 1 ≤ subdivN n r := by
  have h := subdivN_ge n r
  have hK : (1:ℝ) ≤ 2 * Real.exp 1 * (1 + n * Real.exp 1) * ((n : ℝ) + 1) + 1 := by
    have : (0:ℝ) ≤ 2 * Real.exp 1 * (1 + n * Real.exp 1) * ((n : ℝ) + 1) := by positivity
    linarith
  have hr' : (1:ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have : (1:ℝ) ≤ (subdivN n r : ℝ) := by
    calc (1:ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ (2 * Real.exp 1 * (1 + n * Real.exp 1) * ((n : ℝ) + 1) + 1) * (r : ℝ) :=
          mul_le_mul hK hr' zero_le_one (by linarith)
      _ ≤ (subdivN n r : ℝ) := h
  exact_mod_cast this

end Work.WilkG4c

namespace Work.WilkG4c

/-! ## The surrogate family member of BNZ §5.4

BNZ feed Corollary 19 the tuple of the pure-`y` composites `F^{(β)}∘(λ,x,γ_{i,α})`, which lie
in `[-1,1]` rather than in `(0,1)`; the surrogate `(∂_M f + 2)/4` repairs that at the cost of a
factor `4`.  The `else`-branch (`1/2`) turns the surrogate into a *total* `Ω`-definable function
even where the curve point `(l,x,γ(l,x))` is off the `C^{|M|}`-locus; on the locus it is exactly
`(∂_M f + 2)/4`. -/

/-- The surrogate of the composite `(l,x) ↦ ∂_M f (l,x,γ(l,x))`, clamped into `(0,1)` by the
fallback value `1/2` off the `C^{|M|}`-locus. -/
noncomputable def surrogate (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)) (M : List (Fin n)) (l : Fin p → ℝ) (x : ℝ) : ℝ :=
  if xPt l x (γ l x) ∈ interior {z | ContDiffAt ℝ M.length (famFunHat f) z} then
    (iterDir (M.map (fun i : Fin n => Fin.natAdd p i.succ)) (famFunHat f) (xPt l x (γ l x))
      + 2) / 4
  else 1 / 2

/-- On the `C^{|M|}`-locus the surrogate is `(∂_M f + 2)/4`. -/
theorem surrogate_of_mem {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)} {M : List (Fin n)} {l : Fin p → ℝ} {x : ℝ}
    (h : xPt l x (γ l x) ∈ interior {z | ContDiffAt ℝ M.length (famFunHat f) z}) :
    surrogate p n f γ M l x =
      (iterDir (M.map (fun i : Fin n => Fin.natAdd p i.succ)) (famFunHat f)
        (xPt l x (γ l x)) + 2) / 4 := by
  rw [surrogate, if_pos h]

/-- The surrogate takes values in `(0,1)` as soon as the curve value is bounded by `1` on the
locus. -/
theorem surrogate_mem_Ioo {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)} {M : List (Fin n)} {l : Fin p → ℝ} {x : ℝ}
    (hb : xPt l x (γ l x) ∈ interior {z | ContDiffAt ℝ M.length (famFunHat f) z} →
      |iterDir (M.map (fun i : Fin n => Fin.natAdd p i.succ)) (famFunHat f)
        (xPt l x (γ l x))| ≤ 1) :
    surrogate p n f γ M l x ∈ Set.Ioo (0 : ℝ) 1 := by
  rw [surrogate]
  by_cases h : xPt l x (γ l x) ∈ interior {z | ContDiffAt ℝ M.length (famFunHat f) z}
  · rw [if_pos h]
    have := hb h
    constructor <;> linarith [abs_le.mp this]
  · rw [if_neg h]; norm_num

end Work.WilkG4c
