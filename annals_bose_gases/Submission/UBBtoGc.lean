import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.GCBoxBound
import Submission.LhyMin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# UBB -> hboxg : the density-window interface (FS §7 assembly step)

`theorem_1_2` is reduced (Submission.lean) to a single open input `hpres`
(pressure-level LHY-Background at the FS chemical potential `8πa v · ρ`).
`GCBoxBound.hpres_of_gcTwoTerm` turns `hpres` into the **per-box
grand-canonical two-term bound** `hboxg`, and this module closes the last
interface step: the **uniform dilute canonical box bound (UBB)** implies
`hboxg` by minimising the canonical LHY expression over the density window
`s = x/ρ ∈ [0,2]` (FS: pass from the canonical bound (eq:EnergyBoxRes1) to
the grand-canonical bound (eq:EnergyBoxRes2) by the Legendre transformation).

Mathematical content (all lemmas are proved here):

1. Pure calculus (`lhy_window`): for `0 ≤ s ≤ 2`, `0 ≤ q ≤ 1`,
   `0 < s₀ ≤ 1`, `0 ≤ C`, `0 ≤ c`, `c√q ≤ 4/5`:

       (s−1)² + c√q·s^{5/2} − C·q^{s₀}·s^{2+s₀}
           ≥ c√q − (C·2^{2+s₀} + (25/16)c²)·q^{s₀}

   (from `Submission.LhyMin.lhyMinCore`: the minimum over `s ∈ [0,2]` of
   `(s−1)² + B·s^{5/2}` with `B := c√q` is at `B − (25/16)B²`).

2. Algebra (`lhyRhs_window`): for `x := ρ·s`,

       lhyRhs A C s₀ x − 8πAρ·x
         = 4πAρ²·[(s−1)² − 1 + c√(ρA³)·s^{5/2} − C·(ρA³)^{s₀}·s^{2+s₀}]
   with `c := 128/(15√π)` the LHY constant.

3. Per-N bound (`gcTwoTerm_le_lhy_sub`): for each admissible `N ≥ 1`
   (`x := N/L³ ∈ (0, 2ρ]`, `xA³ ≤ ε₀`), the UBB canonical bound
   `lhyRhs A C s₀ x ≤ E(N,L,v)/L³` gives

       gcTwoTerm A (C·2^{2+s₀} + (25/16)c²) s₀ ρ ≤ (E(N,L,v) − 8πAρ·N)/L³.

4. Per-box bound (`gcDensity_ge_gcTwoTerm_of_UBB`): summing over all
   admissible `N` (`le_gcBox_of_forall`):

       gcTwoTerm A Cw s₀ ρ ≤ gcDensity v (8πAρ) (2ρ) L   (all L ≥ 1).

5. The interface theorem `hboxg_of_uniform_box` (eventual in `ρ`) and the
   chain `hpres_of_UBB` feeding `GCBoxBound.hpres_of_gcTwoTerm`, i.e. UBB
   (FS Theorem LHY-Box) + absorption yields `hpres`.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Pure calculus: the density-window minimum -/

/-- `s²·√s = s^(5/2)` for `s ≥ 0` (rpow bookkeeping). -/
private lemma nat_sq_mul_sqrt {s : ℝ} (hs : 0 ≤ s) : s ^ 2 * √s = s ^ (5 / 2 : ℝ) := by
  have hs2 : s ^ 2 = s ^ (2 : ℝ) := (Real.rpow_natCast s 2).symm
  rw [hs2, Real.sqrt_eq_rpow]
  rw [← Real.rpow_add' hs]
  · congr 1
    norm_num
  · norm_num

/-- Density-window minimum.  For `0 ≤ s ≤ 2`, `0 ≤ q ≤ 1`, `0 < s₀ ≤ 1`,
`0 ≤ C`, `0 ≤ c`, `c√q ≤ 4/5`:

    (s−1)² + c√q·s^(5/2) − C·q^s₀·s^(2+s₀) ≥ c√q − (C·2^(2+s₀) + (25/16)c²)·q^s₀ . -/
lemma lhy_window {c C s₀ q s : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hs0pos : 0 < s₀) (hs₀le : s₀ ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hB : c * √q ≤ 4 / 5)
    (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    (s - 1) ^ 2 + c * √q * s ^ (5 / 2 : ℝ) - C * q ^ s₀ * s ^ (2 + s₀)
      ≥ c * √q - (C * 2 ^ (2 + s₀) + (25 / 16) * c ^ 2) * q ^ s₀ := by
  have hcore := lhyMinCore (c := c) (q := q) hc hq0 hB s hs0 hs2
  have he2 : 0 ≤ 2 + s₀ := by linarith [hs0pos]
  have hsle : s ^ (2 + s₀) ≤ 2 ^ (2 + s₀) :=
    Real.rpow_le_rpow hs0 hs2 he2
  have hqsn : 0 ≤ q ^ s₀ := Real.rpow_nonneg hq0 s₀
  have hcoef : 0 ≤ C * q ^ s₀ := mul_nonneg hC hqsn
  have hterm : C * q ^ s₀ * s ^ (2 + s₀) ≤ C * q ^ s₀ * 2 ^ (2 + s₀) :=
    mul_le_mul_of_nonneg_left hsle hcoef
  have hqpow1 : q ^ (1 : ℝ) ≤ q ^ s₀ :=
    Real.rpow_le_rpow_of_exponent_ge' hq0 hq1 (le_of_lt hs0pos) hs₀le
  have hqpow : q ≤ q ^ s₀ := by
    calc
      q = q ^ (1 : ℝ) := (Real.rpow_one q).symm
      _ ≤ q ^ s₀ := hqpow1
  have hsq2 : 0 ≤ (25 / 16) * c ^ 2 := mul_nonneg (by norm_num) (sq_nonneg c)
  have hqpow2 : (25 / 16) * c ^ 2 * q ≤ (25 / 16) * c ^ 2 * q ^ s₀ :=
    mul_le_mul_of_nonneg_left hqpow hsq2
  calc
    (s - 1) ^ 2 + c * √q * s ^ (5 / 2 : ℝ) - C * q ^ s₀ * s ^ (2 + s₀)
        = ((s - 1) ^ 2 + c * √q * s ^ (5 / 2 : ℝ)) - C * q ^ s₀ * s ^ (2 + s₀) := by ring
    _ ≥ (c * √q - (25 / 16) * c ^ 2 * q) - C * q ^ s₀ * s ^ (2 + s₀) := by
        exact sub_le_sub_right hcore (C * q ^ s₀ * s ^ (2 + s₀))
    _ ≥ (c * √q - (25 / 16) * c ^ 2 * q) - C * q ^ s₀ * 2 ^ (2 + s₀) := by
        exact sub_le_sub_left hterm (c * √q - (25 / 16) * c ^ 2 * q)
    _ ≥ c * √q - (25 / 16) * c ^ 2 * q ^ s₀ - C * q ^ s₀ * 2 ^ (2 + s₀) := by
        exact sub_le_sub_right (sub_le_sub_left hqpow2 (c * √q)) (C * q ^ s₀ * 2 ^ (2 + s₀))
    _ = c * √q - (C * 2 ^ (2 + s₀) + (25 / 16) * c ^ 2) * q ^ s₀ := by ring

/-! ## 2. Algebra: expand the canonical LHY expression on the window -/

/-- The canonical bound at density `x = ρ·s` minus the chemical-potential term:
`lhyRhs A C s₀ (ρs) − 8πAρ·(ρs)` equals `4πAρ²` times the window expression. -/
lemma lhyRhs_window {A C s₀ ρ s : ℝ} (hρ : 0 < ρ) (hA : 0 ≤ A) (hs : 0 ≤ s)
    (hs₀ : 0 < s₀) :
    lhyRhs A C s₀ (ρ * s) - (8 * π * A * ρ) * (ρ * s)
      = (4 * π * A * ρ ^ 2) *
          ((s - 1) ^ 2 - 1 + (128 / (15 * √π)) * √(ρ * A ^ 3) * s ^ (5 / 2 : ℝ)
            - C * (ρ * A ^ 3) ^ s₀ * s ^ (2 + s₀)) := by
  unfold lhyRhs
  have hρA : 0 ≤ ρ * A ^ 3 := mul_nonneg hρ.le (pow_nonneg hA 3)
  have hsq : s ^ 2 * √((ρ * s) * A ^ 3) = √(ρ * A ^ 3) * s ^ (5 / 2 : ℝ) := by
    calc
      s ^ 2 * √((ρ * s) * A ^ 3) = s ^ 2 * (√(ρ * A ^ 3) * √s) := by
        congr 1
        calc
          √((ρ * s) * A ^ 3) = √((ρ * A ^ 3) * s) := by congr 1; ring
          _ = √(ρ * A ^ 3) * √s := by rw [Real.sqrt_mul hρA s]
      _ = √(ρ * A ^ 3) * (s ^ 2 * √s) := by ring
      _ = √(ρ * A ^ 3) * s ^ (5 / 2 : ℝ) := by rw [nat_sq_mul_sqrt hs]
  have hsp : s ^ 2 * ((ρ * s) * A ^ 3) ^ s₀ = (ρ * A ^ 3) ^ s₀ * s ^ (2 + s₀) := by
    calc
      s ^ 2 * ((ρ * s) * A ^ 3) ^ s₀ = s ^ 2 * ((ρ * A ^ 3) * s) ^ s₀ := by
        congr 1
        congr 1
        ring
      _ = s ^ 2 * ((ρ * A ^ 3) ^ s₀ * s ^ s₀) := by
        congr 1
        rw [Real.mul_rpow hρA hs]
      _ = (ρ * A ^ 3) ^ s₀ * (s ^ 2 * s ^ s₀) := by ring
      _ = (ρ * A ^ 3) ^ s₀ * s ^ (2 + s₀) := by
        congr 1
        have hs2 : s ^ 2 = s ^ (2 : ℝ) := (Real.rpow_natCast s 2).symm
        have hne : (2 : ℝ) + s₀ ≠ 0 := by linarith [hs₀]
        rw [hs2]
        rw [← Real.rpow_add' (x := s) (y := (2 : ℝ)) (z := s₀) hs hne]
  calc
    4 * π * (ρ * s) ^ 2 * A * (1 + (128 / (15 * √π)) * √((ρ * s) * A ^ 3) -
        C * ((ρ * s) * A ^ 3) ^ s₀) - 8 * π * A * ρ * (ρ * s)
        = 4 * π * A * ρ ^ 2 * s ^ 2 * (1 + (128 / (15 * √π)) * √((ρ * s) * A ^ 3) -
            C * ((ρ * s) * A ^ 3) ^ s₀) - 8 * π * A * ρ ^ 2 * s := by ring
    _ = 4 * π * A * ρ ^ 2 * s ^ 2
        + (128 / (15 * √π)) * 4 * π * A * ρ ^ 2 * (s ^ 2 * √((ρ * s) * A ^ 3))
        - C * 4 * π * A * ρ ^ 2 * (s ^ 2 * ((ρ * s) * A ^ 3) ^ s₀)
        - 8 * π * A * ρ ^ 2 * s := by ring
    _ = 4 * π * A * ρ ^ 2 * (s ^ 2 - 2 * s + (128 / (15 * √π)) * √(ρ * A ^ 3) * s ^ (5 / 2 : ℝ)
          - C * (ρ * A ^ 3) ^ s₀ * s ^ (2 + s₀)) := by
        rw [hsq, hsp]
        ring
    _ = (4 * π * A * ρ ^ 2) * ((s - 1) ^ 2 - 1 +
          (128 / (15 * √π)) * √(ρ * A ^ 3) * s ^ (5 / 2 : ℝ)
            - C * (ρ * A ^ 3) ^ s₀ * s ^ (2 + s₀)) := by ring

/-! ## 3. The per-N inequality -/

/-- Per admissible `N ≥ 1` (`x := N/L³ ∈ (0,2ρ]`), the two-term grand-canonical
value is below the canonical UBB expression minus the chemical potential. -/
lemma gcTwoTerm_le_lhy_sub {A C s₀ ρ x : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hs₀pos : 0 < s₀) (hs₀le : s₀ ≤ 1)
    (hρ : 0 < ρ) (hx : 0 < x) (hx2 : x ≤ 2 * ρ)
    (hq1 : ρ * A ^ 3 ≤ 1)
    (hB : (128 / (15 * √π)) * √(ρ * A ^ 3) ≤ 4 / 5) :
    gcTwoTerm A (C * 2 ^ (2 + s₀) + (25 / 16) * (128 / (15 * √π)) ^ 2) s₀ ρ
      ≤ lhyRhs A C s₀ x - 8 * π * A * ρ * x := by
  let s : ℝ := x / ρ
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact div_nonneg hx.le hρ.le
  have hs2 : s ≤ 2 := by
    dsimp [s]
    exact (div_le_iff₀ hρ).mpr hx2
  have hxs : x = ρ * s := by
    dsimp [s]
    field_simp [ne_of_gt hρ]
  have hc : 0 ≤ 128 / (15 * √π) := by positivity
  have hq0 : 0 ≤ ρ * A ^ 3 := mul_nonneg hρ.le (pow_nonneg hA 3)
  have hwin := lhy_window (c := 128 / (15 * √π)) hc hC hs₀pos hs₀le hq0 hq1 hB hs0 hs2
  have hmain : (4 * π * A * ρ ^ 2) *
        (-1 + (128 / (15 * √π)) * √(ρ * A ^ 3)
          - (C * 2 ^ (2 + s₀) + (25 / 16) * (128 / (15 * √π)) ^ 2) * (ρ * A ^ 3) ^ s₀)
      ≤ (4 * π * A * ρ ^ 2) *
          ((s - 1) ^ 2 - 1 + (128 / (15 * √π)) * √(ρ * A ^ 3) * s ^ (5 / 2 : ℝ)
            - C * (ρ * A ^ 3) ^ s₀ * s ^ (2 + s₀)) := by
    have hpre : 0 ≤ 4 * π * A * ρ ^ 2 := by
      positivity
    have hinner : -1 + (128 / (15 * √π)) * √(ρ * A ^ 3)
            - (C * 2 ^ (2 + s₀) + (25 / 16) * (128 / (15 * √π)) ^ 2) * (ρ * A ^ 3) ^ s₀
          ≤ (s - 1) ^ 2 - 1 + (128 / (15 * √π)) * √(ρ * A ^ 3) * s ^ (5 / 2 : ℝ)
            - C * (ρ * A ^ 3) ^ s₀ * s ^ (2 + s₀) := by
      nlinarith [hwin]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hinner hpre
  calc
    gcTwoTerm A (C * 2 ^ (2 + s₀) + (25 / 16) * (128 / (15 * √π)) ^ 2) s₀ ρ
        = (4 * π * A * ρ ^ 2) *
            (-1 + (128 / (15 * √π)) * √(ρ * A ^ 3)
              - (C * 2 ^ (2 + s₀) + (25 / 16) * (128 / (15 * √π)) ^ 2) * (ρ * A ^ 3) ^ s₀) := by
          dsimp [gcTwoTerm]
    _ ≤ (4 * π * A * ρ ^ 2) *
          ((s - 1) ^ 2 - 1 + (128 / (15 * √π)) * √(ρ * A ^ 3) * s ^ (5 / 2 : ℝ)
            - C * (ρ * A ^ 3) ^ s₀ * s ^ (2 + s₀)) := hmain
    _ = lhyRhs A C s₀ (ρ * s) - (8 * π * A * ρ) * (ρ * s) := by
          rw [lhyRhs_window (hρ := hρ) (hA := hA) (hs := hs0) (hs₀ := hs₀pos)]
    _ = lhyRhs A C s₀ x - 8 * π * A * ρ * x := by
          rw [hxs]

/-! ## 4. The per-box (grand-canonical density) bound -/

/-- In the dilute regime the two-term grand-canonical value is ≤ the empty
state (`N = 0` contributes its nonnegative energy; the two-term value is
nonpositive). -/
lemma gcTwoTerm_nonpos {A C s₀ ρ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hρ : 0 < ρ)
    (hB : (128 / (15 * √π)) * √(ρ * A ^ 3) ≤ 4 / 5) :
    gcTwoTerm A (C * 2 ^ (2 + s₀) + (25 / 16) * (128 / (15 * √π)) ^ 2) s₀ ρ ≤ 0 := by
  dsimp [gcTwoTerm]
  have hpre : 0 ≤ 4 * π * A * ρ ^ 2 := by positivity
  have hcw : 0 ≤ (C * 2 ^ (2 + s₀) + (25 / 16) * (128 / (15 * √π)) ^ 2) * (ρ * A ^ 3) ^ s₀ := by
    have h1 : 0 ≤ C * 2 ^ (2 + s₀) := mul_nonneg hC (Real.rpow_nonneg (by norm_num) (2 + s₀))
    have h2 : 0 ≤ (25 / 16) * (128 / (15 * √π)) ^ 2 := by positivity
    have h3 : 0 ≤ (ρ * A ^ 3) ^ s₀ := Real.rpow_nonneg (mul_nonneg hρ.le (pow_nonneg hA 3)) s₀
    exact mul_nonneg (add_nonneg h1 h2) h3
  have h1 : -1 + (128 / (15 * √π)) * √(ρ * A ^ 3) ≤ -1 / 5 := by nlinarith [hB]
  have hinner : -1 + (128 / (15 * √π)) * √(ρ * A ^ 3)
        - (C * 2 ^ (2 + s₀) + (25 / 16) * (128 / (15 * √π)) ^ 2) * (ρ * A ^ 3) ^ s₀ ≤ 0 := by
    nlinarith [h1, hcw]
  exact mul_nonpos_of_nonneg_of_nonpos hpre hinner

/-- `E(N,L,v)/L³ − μ·(N/L³) = (E(N,L,v) − μN)/L³`. -/
lemma boxEnergy_density_sub {v : ℝ³ → ℝ} {N : ℕ} {L : ℝ} (hL : 0 < L) (μ : ℝ) :
    boxEnergy N L v / L ^ 3 - μ * ((N : ℝ) / L ^ 3) = (boxEnergy N L v - μ * (N : ℝ)) / L ^ 3 := by
  have hmul : μ * ((N : ℝ) / L ^ 3) = (μ * (N : ℝ)) / L ^ 3 := by
    field_simp [ne_of_gt hL]
  rw [hmul]
  rw [div_sub_div_same]

/-- UBB at one box: from the uniform canonical dilute bound
`lhyRhs A C s₀ x ≤ E(N,L,v)/L³` (all `N` with `xA³ ≤ ε₀`), the truncated
grand-canonical density in the window `ρmax := 2ρ` is at least
`gcTwoTerm A (C·2^(2+s₀) + (25/16)c²) s₀ ρ`. -/
lemma gcDensity_ge_gcTwoTerm_of_UBB {v : ℝ³ → ℝ} (hv : 0 ≤ v) {A C s₀ ε₀ ρ L : ℝ}
    (hA : 0 < A) (hC : 0 ≤ C) (hs₀pos : 0 < s₀) (hs₀le : s₀ ≤ 1)
    (hρ : 0 < ρ) (hL : 1 ≤ L)
    (hq1 : ρ * A ^ 3 ≤ 1)
    (hB : (128 / (15 * √π)) * √(ρ * A ^ 3) ≤ 4 / 5)
    (hsmall : (2 * ρ) * A ^ 3 ≤ ε₀)
    (hbox : ∀ N : ℕ, ((N : ℝ) / L ^ 3) * A ^ 3 ≤ ε₀ →
        lhyRhs A C s₀ ((N : ℝ) / L ^ 3) ≤ boxEnergy N L v / L ^ 3) :
    gcTwoTerm A (C * 2 ^ (2 + s₀) + (25 / 16) * (128 / (15 * √π)) ^ 2) s₀ ρ
      ≤ gcDensity v (8 * π * A * ρ) (2 * ρ) L := by
  have hLpos : 0 < L := by linarith
  have hL3 : 0 < L ^ 3 := pow_pos hLpos 3
  dsimp [gcDensity]
  rw [le_div_iff₀ hL3]
  apply le_gcBox_of_forall (μ := 8 * π * A * ρ) (ρmax := 2 * ρ) (L := L)
    (a := gcTwoTerm A (C * 2 ^ (2 + s₀) + (25 / 16) * (128 / (15 * √π)) ^ 2) s₀ ρ * L ^ 3)
  · positivity
  · exact hLpos.le
  · intro y hy
    rcases hy with ⟨N, hNad, rfl⟩
    by_cases hN0 : N = 0
    · subst N
      have hE0 : 0 ≤ boxEnergy 0 L v := boxEnergy_nonneg hLpos hv
      have htwo : gcTwoTerm A (C * 2 ^ (2 + s₀) + (25 / 16) * (128 / (15 * √π)) ^ 2) s₀ ρ ≤ 0 :=
        gcTwoTerm_nonpos (A := A) (C := C) (s₀ := s₀) (ρ := ρ) hA.le hC hρ hB
      have hneg : gcTwoTerm A (C * 2 ^ (2 + s₀) + (25 / 16) * (128 / (15 * √π)) ^ 2) s₀ ρ * L ^ 3 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg htwo (pow_nonneg hLpos.le 3)
      simpa using (le_trans hneg hE0)
    · have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hN0)
      let x : ℝ := (N : ℝ) / L ^ 3
      have hxpos : 0 < x := by
        dsimp [x]
        exact div_pos hNpos hL3
      have hx2 : x ≤ 2 * ρ := by
        dsimp [x]
        have hNd : (N : ℝ) ≤ (2 * ρ) * L ^ 3 := by
          dsimp [gcAdmissible] at hNad
          simpa using hNad
        exact (div_le_iff₀ hL3).mpr hNd
      have hUA : x * A ^ 3 ≤ ε₀ := by
        calc
          x * A ^ 3 ≤ (2 * ρ) * A ^ 3 := mul_le_mul_of_nonneg_right hx2 (pow_nonneg hA.le 3)
          _ ≤ ε₀ := hsmall
      have hboxN : lhyRhs A C s₀ x ≤ boxEnergy N L v / L ^ 3 := by
        simpa [x] using hbox N hUA
      have perN := gcTwoTerm_le_lhy_sub (A := A) (C := C) (s₀ := s₀) (ρ := ρ) (x := x)
        hA.le hC hs₀pos hs₀le hρ hxpos hx2 hq1 hB
      have hsub : lhyRhs A C s₀ x - 8 * π * A * ρ * x
          ≤ (boxEnergy N L v - (8 * π * A * ρ) * (N : ℝ)) / L ^ 3 := by
        have h0 := sub_le_sub_right hboxN (8 * π * A * ρ * x)
        have heq : boxEnergy N L v / L ^ 3 - 8 * π * A * ρ * x
            = (boxEnergy N L v - (8 * π * A * ρ) * (N : ℝ)) / L ^ 3 := by
          dsimp [x]
          rw [boxEnergy_density_sub (v := v) hLpos]
        rwa [heq] at h0
      have htwo : gcTwoTerm A (C * 2 ^ (2 + s₀) + (25 / 16) * (128 / (15 * √π)) ^ 2) s₀ ρ
          ≤ (boxEnergy N L v - (8 * π * A * ρ) * (N : ℝ)) / L ^ 3 :=
        le_trans perN hsub
      exact (le_div_iff₀ hL3).mp htwo

/-! ## 5. The interface theorems -/

/-- The uniform dilute canonical box bound (UBB, FS thm:LHY-Box in corpus
form) implies the per-box grand-canonical two-term bound `hboxg` (eventual
in the window density `ρ`).  `Cw := C·2^(2+s₀) + (25/16)c²`, `s₀ := 1/2+η₀`,
absorbs the error of the density window. -/
theorem hboxg_of_uniform_box {v : ℝ³ → ℝ} (hv : 0 ≤ v) {A C η₀ ε₀ : ℝ}
    (hA : 0 < A) (hC : 0 ≤ C) (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hε₀ : 0 < ε₀)
    (hbox : ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ,
        ((N : ℝ) / L ^ 3) * A ^ 3 ≤ ε₀ →
        lhyRhs A C (1 / 2 + η₀) ((N : ℝ) / L ^ 3) ≤ boxEnergy N L v / L ^ 3) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ L₀ : ℝ, 1 ≤ L₀ ∧
      ∀ L : ℝ, L₀ ≤ L →
        gcTwoTerm A (C * 2 ^ (2 + (1 / 2 + η₀)) + (25 / 16) * (128 / (15 * √π)) ^ 2)
          (1 / 2 + η₀) ρ ≤ gcDensity v (8 * π * A * ρ) (2 * ρ) L := by
  have htA : Tendsto (fun ρ : ℝ => ρ * A ^ 3) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hid : Tendsto (fun ρ : ℝ => ρ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa using hid.mul tendsto_const_nhds
  have hq1e : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ * A ^ 3 ≤ 1 := by
    have hlt : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ * A ^ 3 < 1 :=
      htA.eventually (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1))
    exact hlt.mono (fun ρ h => le_of_lt h)
  have htB : Tendsto (fun ρ : ℝ => (128 / (15 * √π)) * √(ρ * A ^ 3))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hsq : Tendsto (fun ρ : ℝ => √(ρ * A ^ 3)) (𝓝[>] (0 : ℝ)) (𝓝 (√(0 : ℝ))) := htA.sqrt
    simpa using (tendsto_const_nhds.mul hsq)
  have hBe : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (128 / (15 * √π)) * √(ρ * A ^ 3) ≤ 4 / 5 := by
    have hlt : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (128 / (15 * √π)) * √(ρ * A ^ 3) < 4 / 5 :=
      htB.eventually (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 4 / 5))
    exact hlt.mono (fun ρ h => le_of_lt h)
  have hse : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (2 * ρ) * A ^ 3 ≤ ε₀ := by
    have hδ : 0 < ε₀ / 2 := half_pos hε₀
    have hlt : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ * A ^ 3 < ε₀ / 2 :=
      htA.eventually (isOpen_Iio.mem_nhds hδ)
    refine hlt.mono ?_
    intro ρ hlt
    nlinarith
  filter_upwards [self_mem_nhdsWithin, hq1e, hBe, hse] with ρ hρpos hq1 hB hsmall
  have hρ0 : 0 < ρ := by simpa using hρpos
  refine ⟨1, by norm_num, ?_⟩
  intro L hL1
  have hs₀pos : 0 < 1 / 2 + η₀ := by linarith [hη₀]
  have hs₀le : 1 / 2 + η₀ ≤ 1 := by linarith [hη₀le]
  exact gcDensity_ge_gcTwoTerm_of_UBB (v := v) hv (A := A) (C := C)
    (s₀ := 1 / 2 + η₀) (ε₀ := ε₀) (ρ := ρ) (L := L)
    hA hC hs₀pos hs₀le hρ0 hL1 hq1 hB hsmall (hbox := fun N hN => hbox L hL1 N hN)

/-- UBB (any coefficient `C ≥ 0`, exponent `1/2+η₀`) with the domination
`Cw·(ρA³)^(η₀−η) ≤ K` (automatic eventually: `eventually_absorp`) yields the
pressure-level LHY-Background `hpres` at the FS chemical potential `8πAρ`
(with truncation `ρmax := 2ρ`). -/
theorem hpres_of_UBB {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {A η₀ η K C : ℝ} (hA : 0 < A) (hC : 0 ≤ C)
    (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hη : 0 < η) (hηlt : η < η₀) (hK : 0 < K)
    (hubb : ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ,
        ((N : ℝ) / L ^ 3) * A ^ 3 ≤ ε₀ →
        lhyRhs A C (1 / 2 + η₀) ((N : ℝ) / L ^ 3) ≤ boxEnergy N L v / L ^ 3) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs A K (1 / 2 + η) ρ ≤ gcPressure v ρmax (8 * π * A * ρ) + 8 * π * A * ρ * ρ := by
  rcases hubb with ⟨ε₀, hε₀, hbox⟩
  let Cw : ℝ := C * 2 ^ (2 + (1 / 2 + η₀)) + (25 / 16) * (128 / (15 * √π)) ^ 2
  have hCw : 0 ≤ Cw := by
    dsimp [Cw]
    positivity
  have hb := hboxg_of_uniform_box (v := v) hv (A := A) (C := C) (η₀ := η₀) (ε₀ := ε₀)
    hA hC hη₀ hη₀le hε₀ hbox
  have hdom : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), Cw * (ρ * A ^ 3) ^ (η₀ - η) ≤ K := by
    exact eventually_absorp (Cw := C * 2 ^ (2 + (1 / 2 + η₀)) + (25 / 16) * (128 / (15 * √π)) ^ 2)
      hCw hK hA (by linarith)
  simpa [Cw] using hpres_of_gcTwoTerm (v := v) (hv := hv) (hv1 := hv1) (R := R)
    (hR := hR) (hv_supp := hv_supp) (A := A) (η₀ := η₀) (η := η)
    (Cw := C * 2 ^ (2 + (1 / 2 + η₀)) + (25 / 16) * (128 / (15 * √π)) ^ 2) (K := K)
    hA hη₀ hη hηlt hCw hK hb hdom

/-! ## 6. The trivial `a v = 0` branch of `hpres` -/

/-- When the scattering length vanishes, `hpres` holds trivially: the LHY
right-hand side is `0` (`lhyRhs_eq_zero_of_A_eq_zero`) and the grand-canonical
pressure at chemical potential `0` is nonnegative (its density is `sInf` of
nonnegative canonical energies). -/
lemma hpres_of_av_zero {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {K s : ℝ} (hav : a v = 0) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K s ρ ≤ gcPressure v ρmax (8 * π * a v * ρ) + 8 * π * a v * ρ * ρ := by
  filter_upwards [self_mem_nhdsWithin] with ρ hρpos
  have hρ0 : 0 < ρ := by simpa using hρpos
  let ρmax : ℝ := 2 * ρ
  have hρmax0 : 0 < ρmax := by
    dsimp [ρmax]
    positivity
  have hρlt : ρ < ρmax := by
    dsimp [ρmax]
    linarith
  refine ⟨ρmax, hρmax0, hρlt, ?_⟩
  have hgc : 0 ≤ gcPressure v ρmax 0 := by
    unfold gcPressure
    apply gcLiminf_ge_of_eventually_ge (v := v) (μ := 0) (ρmax := ρmax)
      (by norm_num) hv hv1 hρmax0.le
    have hposL : ∀ᶠ L : ℝ in atTop, 0 < L := eventually_ge_atTop 1 |>.mono (fun L hL => by linarith)
    refine hposL.mono ?_
    intro L hL
    have hb := gcBox_density_ge (v := v) (μ := 0) (ρmax := ρmax) (by norm_num) hρmax0.le hL hv
    simpa [gcDensity] using hb
  have hRhs : gcPressure v ρmax (8 * π * a v * ρ) + 8 * π * a v * ρ * ρ =
      gcPressure v ρmax 0 := by
    rw [hav]
    norm_num
  have hLHS : lhyRhs (a v) K s ρ = 0 := by
    rw [hav]
    exact lhyRhs_eq_zero_of_A_eq_zero K s ρ
  rw [hLHS, hRhs]
  exact hgc

end Submission.BoseGases
