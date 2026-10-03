/-
# Area 4 (round 6): the §15 vocabulary and the exact splitting of `Vcut`

This module carries the *mechanical* part of the round-6 §15 reduction of the corrected middle sum
`Work.FITop4.Vcut` (the sharp cut `X < d ∧ 4dX < |Δ|` on the ratio symbol `(z₂/z₁|d)`):

* the `Work.FITop4.Tcut` book-keeping (`Tcut_eq_sum_ofReal`, additivity, subtractivity, locality) —
  identical to the round-3 `Work.FIArea7.TcutMod_eq_sum_ofReal` etc., because `Tcut` and `TcutMod`
  differ only in the symbol;
* the pointwise cut identity `cut_identity` and the resulting **exact** splitting of the sharp
  middle sum into finitely many *smooth* pieces plus one remainder (`Vcut_split`,
  `Vcut_eq_sum_psi`), by the telescoping family `S15u`, `S15psi`, `S15E` of `Work.FIArea4.S15u`.

The two analytic inputs (the smooth-piece bound and the remainder bound) are *not* proved here;
they are the hypotheses `A6PieceBound` / `A6RemBound` consumed by the assembly.
-/
import Mathlib
import Submission.Work.FITop4.Defs6
import Submission.Work.FIArea4.S15u
import Submission.Work.FIArea4.S15arith
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm
import Submission.Work.FIArea7.WBcutTools

set_option maxHeartbeats 1000000

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The bracket and the energy -/

/-- The §15 bracket of Proposition 15.1, with the `+1` and the outer factor `N` that
`endgame_absorb` consumes. -/
def S15Bracket6 (Pa : Work.FITop.Params) (X : ℕ) : ℝ :=
  ((((X : ℝ) ^ (-(1 : ℝ) / 2) * Pa.N)
    + (Pa.N ^ ((1 : ℝ) / 3) * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3))
    + Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 1000) + 1) * Pa.N)

/-- The energy `Σ_{z ∈ boxN} τ(|Re z|)‖β z‖²` of FI §15. -/
def En6 (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) : ℝ :=
  ∑ z ∈ Work.FITop.boxN Pa,
    ((z.re.natAbs.divisors.card : ℕ) : ℝ) * Complex.normSq (β z)

lemma S15Bracket6_nonneg (Pa : Work.FITop.Params) (X : ℕ) : 0 ≤ S15Bracket6 Pa X := by
  unfold S15Bracket6
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have h1 : 0 ≤ (X : ℝ) ^ (-(1 : ℝ) / 2) * Pa.N :=
    mul_nonneg (Real.rpow_nonneg hX0 _) hN0
  have h2 : 0 ≤ Pa.N ^ ((1 : ℝ) / 3) * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg hX0 _))
      (Real.rpow_nonneg hN0 _)
  have h3 : 0 ≤ Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 1000) := Real.rpow_nonneg hN0 _
  positivity

lemma En6_nonneg (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) : 0 ≤ En6 Pa β := by
  unfold En6
  refine Finset.sum_nonneg (fun z _ => ?_)
  exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

/-- The round-6 contract `Work.FITop4.Area4_6`, stated in this module's vocabulary (a verbatim
copy of the definition, so that `A6Core` and `Area4_6` are definitionally equal and the assembly
does not have to import `Areas6`). -/
def A6Core : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
  ∃ c x0 : ℝ, 0 < c ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
  ∀ (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
    Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ X → (X : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 9) →
    ‖Work.FITop4.Vcut (Work.FITop.radN Pa) X β‖
      ≤ c * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ) ^ (-(1 : ℝ) / 3)) * Pa.N ^ 2

/-! ## 2. `Tcut` book-keeping -/

/-- `Work.FITop4.Tcut` as the coercion of the corresponding `ℝ`-valued inner sum (the round-6
analogue of `Work.FIArea7.TcutMod_eq_sum_ofReal`). -/
theorem Tcut_eq_sum_ofReal (Rz : ℤ) (cut : GaussianInt → GaussianInt → ℕ → ℝ)
    (β : GaussianInt → ℂ) :
    Work.FITop4.Tcut Rz cut β
      = 2 * ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            β z1 * star (β z2)
              * ((∑ d ∈ Work.FITop4.Sset z1 z2,
                    ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                      * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)
           else 0) := by
  simp only [Work.FITop4.Tcut]
  congr 1
  apply Finset.sum_congr rfl; intro z1 _
  apply Finset.sum_congr rfl; intro z2 _
  by_cases hg : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hg, if_true]
    congr 1
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl; intro d _
    push_cast; ring
  · simp only [hg, if_false]

/-- `Work.FITop4.Tcut` is additive in its cut. -/
theorem Tcut_add_cut (Rz : ℤ) (c1 c2 : GaussianInt → GaussianInt → ℕ → ℝ)
    (β : GaussianInt → ℂ) :
    Work.FITop4.Tcut Rz c1 β + Work.FITop4.Tcut Rz c2 β
      = Work.FITop4.Tcut Rz (fun z1 z2 d => c1 z1 z2 d + c2 z1 z2 d) β := by
  rw [Tcut_eq_sum_ofReal Rz c1 β, Tcut_eq_sum_ofReal Rz c2 β,
    Tcut_eq_sum_ofReal Rz (fun z1 z2 d => c1 z1 z2 d + c2 z1 z2 d) β]
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro z1 _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro z2 _
  by_cases hg : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hg, if_true]
    rw [← mul_add, ← Complex.ofReal_add]
    congr 1
    rw [Complex.ofReal_inj, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro d _
    ring
  · simp only [hg, if_false]; ring

/-- `Work.FITop4.Tcut` with the zero cut vanishes. -/
theorem Tcut_zero_cut (Rz : ℤ) (β : GaussianInt → ℂ) :
    Work.FITop4.Tcut Rz (fun _ _ _ => (0 : ℝ)) β = 0 := by
  rw [Tcut_eq_sum_ofReal]; simp

/-- `Work.FITop4.Tcut` is additive over a finite sum of cuts. -/
theorem Tcut_sum_cut {ι : Type*} (s : Finset ι) (Rz : ℤ)
    (c : ι → GaussianInt → GaussianInt → ℕ → ℝ) (β : GaussianInt → ℂ) :
    (∑ i ∈ s, Work.FITop4.Tcut Rz (c i) β)
      = Work.FITop4.Tcut Rz (fun z1 z2 d => ∑ i ∈ s, c i z1 z2 d) β := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty]
      have hz : (fun z1 z2 d => ∑ i ∈ (∅ : Finset ι), c i z1 z2 d)
          = (fun _ _ _ => (0 : ℝ)) := by funext z1 z2 d; simp
      rw [hz, Tcut_zero_cut]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, ih, Tcut_add_cut]
      apply congrArg (fun c => Work.FITop4.Tcut Rz c β)
      funext z1 z2 d
      rw [Finset.sum_insert ha]

/-- `Work.FITop4.Tcut` is subtractive in its cut. -/
theorem Tcut_sub_cut (Rz : ℤ) (c1 c2 : GaussianInt → GaussianInt → ℕ → ℝ)
    (β : GaussianInt → ℂ) :
    Work.FITop4.Tcut Rz c1 β - Work.FITop4.Tcut Rz c2 β
      = Work.FITop4.Tcut Rz (fun z1 z2 d => c1 z1 z2 d - c2 z1 z2 d) β := by
  have h := Tcut_add_cut Rz (fun z1 z2 d => c1 z1 z2 d - c2 z1 z2 d) c2 β
  have hc : (fun z1 z2 d => (c1 z1 z2 d - c2 z1 z2 d) + c2 z1 z2 d) = c1 := by
    funext z1 z2 d; ring
  rw [hc] at h
  exact (eq_sub_iff_add_eq).mpr h |>.symm

/-- `Work.FITop4.Tcut` only depends on the values of the cut on the summed range. -/
theorem Tcut_congr_cut_local (Rz : ℤ) (c1 c2 : GaussianInt → GaussianInt → ℕ → ℝ)
    (β : GaussianInt → ℂ)
    (h : ∀ z1 z2 d, z1 ∈ Work.FIPlan.gBox Rz → z2 ∈ Work.FIPlan.gBox Rz →
      d ∈ Work.FITop4.Sset z1 z2 → c1 z1 z2 d = c2 z1 z2 d) :
    Work.FITop4.Tcut Rz c1 β = Work.FITop4.Tcut Rz c2 β := by
  simp only [Work.FITop4.Tcut]
  congr 1
  apply Finset.sum_congr rfl; intro z1 hz1
  apply Finset.sum_congr rfl; intro z2 hz2
  by_cases hg : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hg, if_true]
    congr 1
    apply Finset.sum_congr rfl; intro d hd
    rw [h z1 z2 d hz1 hz2 hd]
  · simp only [hg, if_false]

/-! ## 3. The pointwise cut identity and the exact splitting -/

/-- The bump cut is the `S15psi`-cut, up to the index shift `j ↦ j+1`. -/
lemma S15bump_eq_psi6 (X : ℕ) (j : ℕ) :
    (fun z1 z2 d => if X < d then
        S15u ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * (d : ℝ)) / 2 ^ j)
          - S15u ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * (d : ℝ)) / 2 ^ (j + 1))
      else 0)
      = (fun z1 z2 d => if X < d then
          S15psi ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * (d : ℝ)) / 2 ^ (j + 1))
        else 0) := by
  funext z1 z2 d
  by_cases h : X < d
  · simp only [h, if_true]
    unfold S15psi
    have hpos : (0 : ℝ) < 2 ^ (j + 1) := pow_pos (by norm_num) _
    have h2 : 2 * ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * (d : ℝ)) / 2 ^ (j + 1))
        = (Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * (d : ℝ)) / 2 ^ j := by
      field_simp
      ring
    rw [h2]
  · simp only [h, if_false]

/-! ## 4. The two analytic inputs -/

/-- **The smooth-piece bound** (FI §15, the engine): for every fixed `η ∈ (0, 3/32)` there are
`c > 0` and `x₀` such that for every admissible datum with `x ≥ x₀`, `Pa.η = η`, every smooth `ψ`
supported in `(1/2, 5/2)`, every round-6 coefficient, every `j` and every `1 ≤ X ≤ N^{1/9}`,

  `‖Tcut (radN Pa) (1{X < d}·ψ(|Δ|/(4X2^j d))) β‖ ≤ c·θ²(log N+1)^{2^20}·S15Bracket6 Pa X`. -/
def A6PieceBound : Prop :=
  ∀ ψ : ℝ → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) ψ → (∀ y : ℝ, 0 ≤ ψ y) → (∀ y : ℝ, ψ y ≤ 1) →
    (∀ y : ℝ, (y ≤ 1 / 2 ∨ 5 / 2 ≤ y) → ψ y = 0) →
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
  ∃ c x0 : ℝ, 0 < c ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
  ∀ (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (j : ℕ) (β : GaussianInt → ℂ),
    Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ X → (X : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 9) →
    ‖Work.FITop4.Tcut (Work.FITop.radN Pa)
        (fun z1 z2 d => if X < d then
          ψ ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * 2 ^ j * (d : ℝ))) else 0) β‖
      ≤ c * Pa.θ ^ 2 * (Real.log Pa.N + 1) ^ (2 ^ 20) * S15Bracket6 Pa X

/-- **The remainder bound** (FI §15): the `S15E`-piece of the splitting obeys the same estimate. -/
def A6RemBound : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
  ∃ c x0 : ℝ, 0 < c ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
  ∀ (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
    Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ X → (X : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 9) →
    ‖Work.FITop4.Tcut (Work.FITop.radN Pa)
        (fun z1 z2 d => if X < d then
          S15E ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * (d : ℝ))) else 0) β‖
      ≤ c * Pa.θ ^ 2 * (Real.log Pa.N + 1) ^ (2 ^ 20) * S15Bracket6 Pa X

/-! ## Elementary box / log lemmas (self-contained copies, to avoid a heavy import) -/

/-- The coordinates of a member of `gBox R` are bounded by `R`. -/
lemma mem_gBox_coords {R : ℤ} {z : GaussianInt} (hz : z ∈ Work.FIPlan.gBox R) :
    |z.re| ≤ R ∧ |z.im| ≤ R := by
  rw [Work.FIPlan.gBox] at hz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  rw [Finset.mem_Icc] at hp1 hp2
  constructor
  · have h : (⟨p.1, p.2⟩ : GaussianInt).re = p.1 := rfl
    rw [h, abs_le]; exact ⟨hp1.1, hp1.2⟩
  · have h : (⟨p.1, p.2⟩ : GaussianInt).im = p.2 := rfl
    rw [h, abs_le]; exact ⟨hp2.1, hp2.2⟩

/-- `|Δ(z₁,z₂)| ≤ 2R²` for `z₁, z₂ ∈ gBox R` and `0 ≤ R`. -/
lemma absDelta_le_two_mul_sq {R : ℤ} {z1 z2 : GaussianInt} (hR : 0 ≤ R)
    (h1 : z1 ∈ Work.FIPlan.gBox R) (h2 : z2 ∈ Work.FIPlan.gBox R) :
    ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ) ≤ 2 * R ^ 2 := by
  obtain ⟨ha1, hb1⟩ := mem_gBox_coords h1
  obtain ⟨ha2, hb2⟩ := mem_gBox_coords h2
  have hD : Work.FIPlan.Delta z1 z2 = z1.re * z2.im - z1.im * z2.re := by
    rw [Work.FIPlan.Delta, Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star]; ring
  have habs : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ) = |Work.FIPlan.Delta z1 z2| := by
    rw [Work.FIPlan.absDelta]
    rcases Int.natAbs_eq (Work.FIPlan.Delta z1 z2) with h | h
    · rw [h, Int.natAbs_natCast]; simp
    · rw [h]; simp
  rw [habs, hD]
  have hA : |z1.re * z2.im| ≤ R * R := by
    rw [abs_mul]; exact mul_le_mul ha1 hb2 (abs_nonneg _) hR
  have hB : |z1.im * z2.re| ≤ R * R := by
    rw [abs_mul]; exact mul_le_mul hb1 ha2 (abs_nonneg _) hR
  calc |z1.re * z2.im - z1.im * z2.re| ≤ |z1.re * z2.im| + |z1.im * z2.re| := abs_sub _ _
    _ ≤ 2 * R ^ 2 := by linarith [hA, hB]

/-- `Nat.log2 n ≤ log n / log 2` as real numbers, for `1 ≤ n`. -/
lemma nat_log2_cast_le (n : ℕ) (hn : 1 ≤ n) :
    (Nat.log2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
  have hn0 : n ≠ 0 := by omega
  have h2 : 2 ^ Nat.log2 n ≤ n := (Nat.le_log2 hn0).mp (le_refl _)
  have hcast : ((2 : ℝ) ^ Nat.log2 n) ≤ (n : ℝ) := by exact_mod_cast h2
  have hlog : Real.log ((2 : ℝ) ^ Nat.log2 n) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) hcast
  rw [Real.log_pow] at hlog
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc (Nat.log2 n : ℝ) = ((Nat.log2 n : ℝ) * Real.log 2) / Real.log 2 := by field_simp
    _ ≤ Real.log (n : ℝ) / Real.log 2 := div_le_div_of_nonneg_right hlog hlog2.le

/-- The box radius `radN Pa = ⌈√(4N)⌉₊` is at most `4√N`. -/
lemma radN_toNat_le (Pa : Work.FITop.Params) :
    ((Work.FITop.radN Pa).toNat : ℝ) ≤ 4 * Real.sqrt Pa.N := by
  have hN1 : (1 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have h0 : (0 : ℝ) ≤ Real.sqrt (4 * Pa.N) := Real.sqrt_nonneg _
  have h := Nat.ceil_lt_add_one h0
  have htoNat : ((Work.FITop.radN Pa).toNat : ℝ)
      = ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ) := by
    rw [Work.FITop.radN, Int.toNat_natCast]
  have hs : Real.sqrt (4 * Pa.N) = 2 * Real.sqrt Pa.N := by
    rw [show (4 : ℝ) * Pa.N = 4 * Pa.N by ring, Real.sqrt_mul (by norm_num) Pa.N]
    norm_num
  have h2 : (2 : ℝ) ≤ Real.sqrt (4 * Pa.N) := by
    rw [hs]
    have : (1 : ℝ) ≤ Real.sqrt Pa.N := Real.one_le_sqrt.mpr hN1
    linarith
  have h3 : Real.sqrt (4 * Pa.N) + 1 ≤ 4 * Real.sqrt Pa.N := by rw [hs]; linarith
  rw [htoNat]
  linarith

/-- `S15psi` satisfies the support hypothesis of the §15 piece bound. -/
lemma S15psi_support_half (y : ℝ) (hy : y ≤ 1 / 2 ∨ 5 / 2 ≤ y) : S15psi y = 0 := by
  by_contra h
  have := S15psi_support h
  rcases hy with h1 | h2 <;> linarith [this.1, this.2]

/-- The two parenthesisations of the bump argument agree. -/
lemma psiArg_eq (X j M d : ℕ) :
    (M : ℝ) / (4 * (X : ℝ) * 2 ^ (j + 1) * (d : ℝ))
      = (M : ℝ) / (4 * (X : ℝ) * (d : ℝ)) / 2 ^ (j + 1) := by
  rw [div_div]
  congr 1
  ring

/-- The `(radN Pa).toNat` cast back to `radN Pa`. -/
lemma radN_cast_toNat (Pa : Work.FITop.Params) :
    ((((Work.FITop.radN Pa).toNat : ℕ) : ℤ)) = Work.FITop.radN Pa :=
  Int.toNat_of_nonneg (by unfold Work.FITop.radN; exact Int.natCast_nonneg _)

/-- `2 ≤ (radN Pa).toNat`. -/
lemma two_le_radN_toNat (Pa : Work.FITop.Params) : 2 ≤ (Work.FITop.radN Pa).toNat := by
  have hN1 : (1 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have h4 : (4 : ℝ) ≤ 4 * Pa.N := by linarith
  have hs : (2 : ℝ) ≤ Real.sqrt (4 * Pa.N) := by
    rw [show (4 : ℝ) * Pa.N = 2 ^ 2 * Pa.N by norm_num, Real.sqrt_mul (by norm_num) Pa.N,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    have : (1 : ℝ) ≤ Real.sqrt Pa.N := Real.one_le_sqrt.mpr hN1
    linarith
  have hc := Nat.le_ceil (Real.sqrt (4 * Pa.N))
  have h2 : (2 : ℝ) ≤ ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ) := le_trans hs hc
  have h3 : 2 ≤ ⌈Real.sqrt (4 * Pa.N)⌉₊ := by exact_mod_cast h2
  have : (Work.FITop.radN Pa).toNat = ⌈Real.sqrt (4 * Pa.N)⌉₊ := by
    rw [Work.FITop.radN, Int.toNat_natCast]
  rw [this]; exact h3

/-- The number of dyadic pieces is `≤ 12 (log N + 1)²`. -/
lemma J_le_log_sq (Pa : Work.FITop.Params) :
    ((Nat.log2 ((Work.FITop.radN Pa).toNat ^ 2) + 2 : ℕ) : ℝ)
      ≤ 12 * (Real.log Pa.N + 1) ^ 2 := by
  have hNpos : (0 : ℝ) < Pa.N := by linarith [Pa.hN1]
  have hL : (0 : ℝ) ≤ Real.log Pa.N := Real.log_nonneg (by linarith [Pa.hN1])
  have hm16 : ((((Work.FITop.radN Pa).toNat ^ 2 : ℕ)) : ℝ) ≤ 16 * Pa.N := by
    have h0 : (0 : ℝ) ≤ ((Work.FITop.radN Pa).toNat : ℝ) := Nat.cast_nonneg _
    have h1 : ((Work.FITop.radN Pa).toNat : ℝ) ^ 2 ≤ (4 * Real.sqrt Pa.N) ^ 2 :=
      pow_le_pow_left₀ h0 (radN_toNat_le Pa) 2
    have hsq : (4 * Real.sqrt Pa.N) ^ 2 = 16 * Pa.N := by
      rw [mul_pow, Real.sq_sqrt hNpos.le]; ring
    rw [hsq] at h1
    rw [Nat.cast_pow]
    exact h1
  have hmpos : (0 : ℝ) < ((((Work.FITop.radN Pa).toNat ^ 2 : ℕ)) : ℝ) := by
    have h2 : 2 ≤ (Work.FITop.radN Pa).toNat := two_le_radN_toNat Pa
    have : (0 : ℕ) < (Work.FITop.radN Pa).toNat ^ 2 := by positivity
    exact_mod_cast this
  have hm1 : 1 ≤ (Work.FITop.radN Pa).toNat ^ 2 := by
    have h2 : 2 ≤ (Work.FITop.radN Pa).toNat := two_le_radN_toNat Pa
    nlinarith
  have hlog2le : ((Nat.log2 ((Work.FITop.radN Pa).toNat ^ 2) : ℕ) : ℝ)
      ≤ Real.log ((((Work.FITop.radN Pa).toNat ^ 2 : ℕ)) : ℝ) / Real.log 2 :=
    nat_log2_cast_le _ hm1
  have hlogm : Real.log ((((Work.FITop.radN Pa).toNat ^ 2 : ℕ)) : ℝ) ≤ Real.log (16 * Pa.N) :=
    Real.log_le_log hmpos hm16
  have hlog16 : Real.log (16 * Pa.N) = Real.log 16 + Real.log Pa.N :=
    Real.log_mul (by norm_num) hNpos.ne'
  have hlog16eq : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    push_cast; ring
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2half : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hsplit1 : (4 * Real.log 2 + Real.log Pa.N) / Real.log 2
      = 4 + Real.log Pa.N / Real.log 2 := by
    rw [add_div, mul_div_cancel_right₀ (4:ℝ) hlog2pos.ne']
  have hdivle : Real.log Pa.N / Real.log 2 ≤ Real.log Pa.N / (1 / 2) :=
    div_le_div_of_nonneg_left hL (by norm_num) hlog2half
  have hdiv2 : Real.log Pa.N / (1 / 2) = 2 * Real.log Pa.N := by ring
  have hkey : ((Nat.log2 ((Work.FITop.radN Pa).toNat ^ 2) : ℕ) : ℝ)
      ≤ 4 + 2 * Real.log Pa.N := by
    have hm_le : Real.log ((((Work.FITop.radN Pa).toNat ^ 2 : ℕ)) : ℝ)
        ≤ 4 * Real.log 2 + Real.log Pa.N := by
      have h := hlogm
      rw [hlog16, hlog16eq] at h
      exact h
    have h1 : ((Nat.log2 ((Work.FITop.radN Pa).toNat ^ 2) : ℕ) : ℝ)
        ≤ (4 * Real.log 2 + Real.log Pa.N) / Real.log 2 :=
      le_trans hlog2le (div_le_div_of_nonneg_right hm_le hlog2pos.le)
    rw [hsplit1] at h1
    linarith [h1, hdivle, hdiv2]
  have hfin : (4 + 2 * Real.log Pa.N) + 2 ≤ 12 * (Real.log Pa.N + 1) ^ 2 := by
    nlinarith [sq_nonneg (Real.log Pa.N), hL]
  have hcast : (((Nat.log2 ((Work.FITop.radN Pa).toNat ^ 2) + 2 : ℕ)) : ℝ)
      = ((Nat.log2 ((Work.FITop.radN Pa).toNat ^ 2) : ℕ) : ℝ) + 2 := by push_cast; ring
  linarith [hkey, hfin, hcast]


end

end Work.FIArea4
