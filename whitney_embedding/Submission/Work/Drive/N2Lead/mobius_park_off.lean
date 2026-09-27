import Mathlib
import Submission.Work.Drive.N2Lead.mobiusGeomDefs
import Submission.Work.Drive.N2Lead.mobius_lowerProfile
import Submission.Work.Drive.N2Lead.twistDefs
import Submission.Work.Drive.N2Lead.twistIsometry

namespace Work.Drive.N2Lead

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function

/-- The set `πℤ` of integer multiples of `π` is closed in `ℝ`. -/
lemma isClosed_range_int_mul_pi :
    IsClosed (Set.range (fun k : ℤ => (k : ℝ) * Real.pi)) := by
  have h : Set.range (fun k : ℤ => (k : ℝ) * Real.pi)
      = (fun x : ℝ => x / Real.pi) ⁻¹' (Set.range ((↑) : ℤ → ℝ)) := by
    ext x
    simp only [Set.mem_range, Set.mem_preimage]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [← hk, mul_div_cancel_right₀ (k : ℝ) Real.pi_ne_zero]
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [hk]
      exact div_mul_cancel₀ x Real.pi_ne_zero
  rw [h]
  exact Real.isClosed_range_intCast.preimage (continuous_id.div_const _)

/-- **A bridge zone meets `πℤ`.**  If `φ` is within `φE` of the set `πℤ`, then there is an integer
`k` with `|φ - k π| ≤ φE`. -/
lemma exists_int_mul_pi_sub_le {φ φE : ℝ} (h : mobiusDist φ ≤ φE) :
    ∃ k : ℤ, |φ - (k : ℝ) * Real.pi| ≤ φE := by
  have h' : Metric.infDist φ (Set.range fun k : ℤ => (k : ℝ) * Real.pi) ≤ φE := h
  obtain ⟨y, hy, hyd⟩ := isClosed_range_int_mul_pi.exists_infDist_eq_dist ⟨0, ⟨0, by simp⟩⟩ φ
  obtain ⟨k, rfl⟩ := hy
  have hdist : dist φ ((k : ℝ) * Real.pi) ≤ φE := by rw [← hyd]; exact h'
  rw [Real.dist_eq] at hdist
  exact ⟨k, hdist⟩

/-- **Positive shifts**: a `c`-periodic function is fixed by the shifts `n * c`, `n ≥ 0`. -/
lemma r_shift_nat {r : ℝ → ℝ} {c : ℝ} (h : ∀ φ : ℝ, r (φ + c) = r φ) (n : ℕ) :
    ∀ ψ : ℝ, r (ψ + (n : ℝ) * c) = r ψ := by
  induction n with
  | zero => intro ψ; simp
  | succ m ih =>
      intro ψ
      rw [Nat.cast_succ]
      have he : ψ + ((m : ℝ) + 1) * c = (ψ + (m : ℝ) * c) + c := by ring
      rw [he, h, ih]

/-- **Negative shifts**: the same for `- n * c`. -/
lemma r_sub_nat_mul {r : ℝ → ℝ} {c : ℝ} (h : ∀ φ : ℝ, r (φ + c) = r φ) (n : ℕ) :
    ∀ ψ : ℝ, r (ψ - (n : ℝ) * c) = r ψ := by
  induction n with
  | zero => intro ψ; simp
  | succ m ih =>
      intro ψ
      rw [Nat.cast_succ]
      have he : ψ - ((m : ℝ) + 1) * c = (ψ - (m : ℝ) * c) - c := by ring
      rw [he]
      have hback : r ((ψ - (m : ℝ) * c) - c) = r (ψ - (m : ℝ) * c) := by
        have hh := h ((ψ - (m : ℝ) * c) - c)
        rw [show (ψ - (m : ℝ) * c) - c + c = ψ - (m : ℝ) * c by ring] at hh
        exact hh.symm
      rw [hback, ih]

/-- **Integer shifts**: a `π`-periodic function is fixed by every integer multiple of `π`. -/
lemma r_add_int_mul_pi {r : ℝ → ℝ} (hrper : ∀ φ : ℝ, r (φ + Real.pi) = r φ) (k : ℤ) :
    ∀ ψ : ℝ, r (ψ + (k : ℝ) * Real.pi) = r ψ := by
  have hneg : ∀ φ : ℝ, r (φ + (-Real.pi)) = r φ := by
    intro φ
    have hh := hrper (φ + (-Real.pi))
    rw [show φ + (-Real.pi) + Real.pi = φ by ring] at hh
    exact hh.symm
  intro ψ
  rcases Int.eq_nat_or_neg k with ⟨n, hn | hn⟩
  · rw [hn]
    simpa using r_shift_nat hrper n ψ
  · rw [hn]
    have he : ψ + ((-(n : ℤ) : ℤ) : ℝ) * Real.pi = ψ + (n : ℝ) * (-Real.pi) := by
      push_cast; ring
    rw [he]
    exact r_shift_nat hneg n ψ

/-- The complex planar inclusion `cE3 : ℂ → ℝ³` is an isometry onto the plane `z = 0`. -/
lemma norm_cE3 (z : ℂ) : ‖Work.Drive.N2.cE3 z‖ = ‖z‖ := by
  have h2 : ‖Work.Drive.N2.cE3 z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Complex.sq_norm, Complex.normSq_apply]
    simp only [Fin.sum_univ_three]
    simp only [Work.Drive.N2.cE3_apply_zero, Work.Drive.N2.cE3_apply_one,
      Work.Drive.N2.cE3_apply_two]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, sq_abs]
    norm_num
    ring
  have h3 := congrArg Real.sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3

/-- The norm squared of the planar point `cE3 (t · exp (i φ))` is `t ^ 2`. -/
lemma norm_sq_cE3_mul_exp (t φ : ℝ) :
    ‖Work.Drive.N2.cE3 ((t : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))‖ ^ 2 = t ^ 2 := by
  rw [norm_cE3, Complex.sq_norm, Complex.normSq_mul, Complex.normSq_ofReal]
  have hexp : Complex.normSq (Complex.exp ((φ : ℂ) * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  rw [hexp, mul_one]
  ring

open scoped Manifold ContDiff Topology in
/-- **The relaxed off-pin row of the Möbius park** (§4 `D2d.4` of `N2Lead/NOTES_LEAD_mobiusSaddle.md`,
last item; the *bridge-zone* restriction is recorded in
`N2Lead/NOTES_H8_packetConstruction_interface.md` §4.2 and §1 of
`N2Lead/NOTES_H8_mobiusNote_gap_and_relaxedCrossRow.md`).  Let `r` be the polar profile of
`Work.Drive.N2Lead.mobius_lowerProfile` (positive; `π`-periodic and even; equal to the hyperbola
branch `√(η / -cos (2φ))` on the arc range `[φE, π - φE]`; and on the *bridge zone* — `mobiusDist φ ≤
mobiusPhiE η m`, i.e. `φ` within `φE` of a multiple of `π` — satisfying
`√(η² + m²) ≤ r φ ^ 2 ≤ R²`).  Then, provided `c₀ + 2η < √(η² + m²)`, on the bridge zone

* the profile stays above the off-pin ball: `c₀ + 2η < (r φ)²`, and
* the *twisted* park point `A φ = twistY a' 1 (cE3 (r φ · exp (i φ)))` satisfies the relaxed off-pin
  row `(A φ) 2 ≠ 0 ∨ c₀ + 2η < ‖A φ‖²`.

The restriction to the bridge zone is necessary: on the arcs `r φ = √(η / -cos (2φ))` drops to `√η`
at `φ = π/2`, *below* `c₀ + 2η` — and the off-pin row is only required off the pinned set
`{|Im (Z·)²| ≤ m}`, i.e. on the bridges.  Proof of the first conjunct: `mobiusDist φ ≤ φE` gives
`k : ℤ` with `|φ - k π| ≤ φE`; π-periodicity (`hrper`) and evenness (`hreven`) reduce it to
`[0, φE]`, where `hprof` gives `√(η² + m²) ≤ (r φ)²`, and `habove` converts that.  The second conjunct
follows because `rot02` is an orthogonal map fixing the second coordinate, so
`‖A φ‖² = ‖cE3 (r φ · exp (i φ))‖² = (r φ)²`, and `(A φ) 2 = 0` forces nothing more than the first
disjunct's failure, where the same bound `c₀ + 2η < (r φ)² = ‖A φ‖²` applies.  The result goes in
namespace `Work.Drive.N2Lead`. -/
theorem mobius_park_off {η m R c₀ a' : ℝ} {r : ℝ → ℝ}
    (hη : 0 < η) (hη' : η < 1 / 10) (hm : 1 < m) (hm2 : m ≤ 2) (hR : 2 ≤ R)
    (ha' : 0 < a')
    (hprof : ∀ φ ∈ Set.Icc 0 (Work.Drive.N2Lead.mobiusPhiE η m),
      Real.sqrt (η ^ 2 + m ^ 2) ≤ r φ ^ 2 ∧ r φ ^ 2 ≤ R ^ 2)
    (habove : c₀ + 2 * η < Real.sqrt (η ^ 2 + m ^ 2))
    (hrper : ∀ φ : ℝ, r (φ + Real.pi) = r φ) (hreven : ∀ φ : ℝ, r (-φ) = r φ)
    (hrpos : ∀ φ : ℝ, 0 < r φ) :
    (∀ φ : ℝ, Work.Drive.N2Lead.mobiusDist φ ≤ Work.Drive.N2Lead.mobiusPhiE η m →
      c₀ + 2 * η < (r φ) ^ 2) ∧
    (∀ φ : ℝ, Work.Drive.N2Lead.mobiusDist φ ≤ Work.Drive.N2Lead.mobiusPhiE η m →
      (Work.Drive.N2Lead.twistY a' 1
        (Work.Drive.N2.cE3 (r φ * Complex.exp ((φ : ℂ) * Complex.I)))) 2 ≠ 0 ∨
      c₀ + 2 * η < ‖Work.Drive.N2Lead.twistY a' 1
        (Work.Drive.N2.cE3 (r φ * Complex.exp ((φ : ℂ) * Complex.I)))‖ ^ 2) := by
  have hbridge : ∀ φ : ℝ, mobiusDist φ ≤ mobiusPhiE η m → c₀ + 2 * η < (r φ) ^ 2 := by
    intro φ hdist
    obtain ⟨k, hk⟩ := exists_int_mul_pi_sub_le hdist
    set ψ : ℝ := φ - (k : ℝ) * Real.pi with hψ
    have hφ : φ = ψ + (k : ℝ) * Real.pi := by rw [hψ]; ring
    have hshift : r (ψ + (k : ℝ) * Real.pi) = r ψ := r_add_int_mul_pi hrper k ψ
    have hrφ : r φ = r ψ := by rw [hφ, hshift]
    have habs : r ψ = r |ψ| := by
      rcases abs_choice ψ with h | h
      · rw [h]
      · rw [h, hreven ψ]
    have hψle : |ψ| ≤ mobiusPhiE η m := by
      rw [hψ]
      exact hk
    have hb : Real.sqrt (η ^ 2 + m ^ 2) ≤ (r φ) ^ 2 := by
      have hprof' := (hprof |ψ| ⟨abs_nonneg ψ, hψle⟩).1
      rw [hrφ, habs]
      exact hprof'
    linarith
  refine ⟨hbridge, ?_⟩
  intro φ hdist
  have h1 : c₀ + 2 * η < (r φ) ^ 2 := hbridge φ hdist
  have h2 : c₀ + 2 * η <
      ‖Work.Drive.N2.cE3 (r φ * Complex.exp ((φ : ℂ) * Complex.I))‖ ^ 2 := by
    rw [norm_sq_cE3_mul_exp]
    exact h1
  exact twistY_off_row a' (c₀ + 2 * η) _ h2

end Work.Drive.N2Lead
