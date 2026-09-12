import Mathlib
import Submission.PolyaCore

/-!
# One small monic polynomial ⟹ polynomial control (submultiplicativity)

KEY REDUCTION (session 27): `Submission.PolyaCore.HedgehogBound S` asks for,
on some fattening `FatStar S ε` of the hedgehog, monic polynomials `p_j` of
*every* degree `j` with `‖p_j‖ ≤ C·θ^j` and `θ < 1`.  It suffices to find a
SINGLE monic polynomial `q` of some positive degree whose values on the
fattening are all `< 1` in norm:

    qSmall S := ∃ ε>0, ∃ q : ℂ[X], q.Monic ∧ q.natDegree ≠ 0 ∧
                   ∀ X ∈ FatStar S ε, ‖q.eval X‖ < 1

Boosting argument.  Let `N := q.natDegree`.  Since `X ↦ ‖q.eval X‖` is
continuous and `FatStar S ε` is compact (finite union of segments
`Submission.XTransfer.star S` is compact, and the closed `ε`-neighbourhood
`FatStar S ε` is compact), the function attains a maximum `S₀` on the
fattening, and `S₀ < 1` (each value is `< 1`).  Pick `θ` with
`S₀ < θ^N < 1` (e.g. `θ := (S₀ + 1)/2` raised appropriately; any
`S₀^(1/N) < θ < 1` works).  Also pick `R ≥ 1` with `‖X‖ ≤ R` for every
`X ∈ FatStar S ε` (boundedness of the compact fattening).  For each degree
`n`, write `n = a·N + r` with `0 ≤ r < N` (division by `N > 0`) and set
`p_n := X^r · q^a` — monic of degree `n`.  For `X ∈ FatStar S ε`:

    ‖p_n(X)‖ = ‖X‖^r · ‖q(X)‖^a  ≤  R^r · S₀^a  ≤  R^(N-1) · θ^(a·N)
             = (R^(N-1) · θ^(-r)) · θ^n  ≤  (R^(N-1) · θ^-(N-1)) · θ^n

so `C := R^(N-1) · θ^-(N-1)` (a constant, `θ > 0`) gives the bound
`‖p_n‖ ≤ C·θ^n` for all `n`, i.e. `HedgehogBound S` with that `ε, C, θ`.

Why this matters: the deep (Dubinin-type) content needed by the analytic
engine is only the production of ONE such polynomial `q`; this module
provides the elementary infinite-family extension.

## Helper facts the proof needs (develop inside this file, all with proofs)

* `isCompact_fatStar` : `IsCompact (FatStar S ε)` for `0 ≤ ε` —
  (a) `star S` is compact: `XTransfer.isClosed_star S` + bounded (each
  segment `[0,z²]`, `[0,z⁴]` lies in `closedBall 0 ‖z²‖`, `closedBall 0 ‖z⁴‖`,
  finite union), then closed-and-bounded in `ℂ` is compact
  (`Metric.isCompact_iff_isClosed_bounded` or similar, `ℂ` is proper);
  (b) `FatStar S ε = Metric.cthickening ε (star S)` for `0 ≤ ε` (use
  `Metric.mem_cthickening_iff` and, for the reverse inclusion, attainment of
  `infEDist` on the closed set `star S`), and `IsCompact.cthickening`.
* a boundedness witness `R` with `1 ≤ R` and `∀ X ∈ FatStar S ε, ‖X‖ ≤ R`
  (from `Bornology.IsBounded` of the compact fattening, via the ball
  covering lemma).
* max attainment: `IsCompact.exists_isMaxOn` / continuous functions on
  compact sets attain their maximum; `S₀ := max`, `S₀ < 1`.
* real/rpow arithmetic for `θ`, `C`, and `rpow` or plain powers
  (all exponents natural).
-/

noncomputable section

open scoped Polynomial Real Topology

namespace Submission.ChebPower

open Polynomial
open Submission.PolyaCore
open Submission.XTransfer

/-- A single monic polynomial of positive degree with all values `< 1` in
norm on some fattening of the hedgehog. -/
def qSmall (S : Finset ℂ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ q : ℂ[X], q.Monic ∧ q.natDegree ≠ 0 ∧
    ∀ X : ℂ, X ∈ FatStar S ε → ‖q.eval X‖ < 1

/-- Each segment `segment ℝ 0 c` is compact (image of `[0,1]`). -/
lemma isCompact_segment_zero (c : ℂ) : IsCompact (segment ℝ 0 c) := by
  have himage : segment ℝ 0 c = (fun θ : ℝ => θ • c) '' Set.Icc (0 : ℝ) 1 := by
    rw [segment_eq_image (𝕜 := ℝ) (x := (0 : ℂ)) (y := c)]
    ext X
    constructor
    · rintro ⟨θ, hθ, hX⟩
      refine ⟨θ, hθ, ?_⟩
      change θ • c = X
      calc
        θ • c = (1 - θ) • (0 : ℂ) + θ • c := by simp
        _ = X := hX
    · rintro ⟨θ, hθ, hX⟩
      refine ⟨θ, hθ, ?_⟩
      change (1 - θ) • (0 : ℂ) + θ • c = X
      simpa using hX
  rw [himage]
  exact (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).image (continuous_id.smul continuous_const)

/-- The star is a finite union of compact segments, hence compact. -/
lemma isCompact_star (S : Finset ℂ) : IsCompact (XTransfer.star S) := by
  classical
  have hstar : XTransfer.star S = ⋃ z ∈ (S : Set ℂ), (segment ℝ 0 (z ^ 2) ∪ segment ℝ 0 (z ^ 4)) := by
    ext X
    simp [XTransfer.star]
  rw [hstar]
  exact S.finite_toSet.isCompact_biUnion (fun z hz =>
    (isCompact_segment_zero (z ^ 2)).union (isCompact_segment_zero (z ^ 4)))

/-- For `0 ≤ ε`, `FatStar S ε` is the closed `ε`-thickening of the star. -/
lemma fatStar_eq_cthickening (S : Finset ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    FatStar S ε = Metric.cthickening ε (XTransfer.star S) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro X hX
    rcases hX with ⟨Y, hY, hXY⟩
    exact Metric.mem_cthickening_of_dist_le X Y ε (XTransfer.star S) hY (by simpa [dist_eq_norm] using hXY)
  · intro X hX
    rw [(isCompact_star S).cthickening_eq_biUnion_closedBall hε] at hX
    have h' : ∃ z ∈ (XTransfer.star S : Set ℂ), X ∈ Metric.closedBall z ε := by simpa using hX
    rcases h' with ⟨Y, hY, hXY⟩
    refine ⟨Y, hY, ?_⟩
    have hd := Metric.mem_closedBall.mp hXY
    simpa [dist_eq_norm] using hd

/-- The `ε`-fattening `FatStar S ε` of a hedgehog is compact for `0 ≤ ε`. -/
lemma isCompact_fatStar (S : Finset ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    IsCompact (FatStar S ε) := by
  rw [fatStar_eq_cthickening S hε]
  exact (isCompact_star S).cthickening

/-- Boundedness witness: some `R ≥ 1` bounds every point of the fattening. -/
lemma exists_bound_fatStar (S : Finset ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ X : ℂ, X ∈ FatStar S ε → ‖X‖ ≤ R := by
  let F : Set ℂ := FatStar S ε
  have hcomp : IsCompact F := isCompact_fatStar S hε
  have hbdd : Bornology.IsBounded F := hcomp.isBounded
  rcases (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hbdd with ⟨r, hsub⟩
  refine ⟨max 1 r, le_max_left _ _, ?_⟩
  intro X hX
  have hdist : dist X 0 ≤ r := Metric.mem_closedBall.mp (hsub hX)
  calc
    ‖X‖ = dist X 0 := by rw [dist_eq_norm, sub_zero]
    _ ≤ r := hdist
    _ ≤ max 1 r := le_max_right _ _

/-- If `0 ≤ S₀ < 1` and `N ≥ 1` there is `θ ∈ (0,1)` with `S₀ < θ^N`. -/
lemma exists_theta_pow_between {S₀ : ℝ} {N : ℕ} (hS0 : 0 ≤ S₀) (hS1 : S₀ < 1) (hN : 0 < N) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ S₀ < θ ^ N := by
  classical
  let m : ℝ := (1 + S₀) / 2
  have hm0 : 0 < m := by
    dsimp [m]
    positivity
  have hm1 : m < 1 := by
    dsimp [m]
    nlinarith
  let θ : ℝ := m ^ ((N : ℝ)⁻¹)
  refine ⟨θ, ?_, ?_, ?_⟩
  · dsimp [θ]
    exact Real.rpow_pos_of_pos hm0 _
  · dsimp [θ]
    exact Real.rpow_lt_one hm0.le hm1 (inv_pos.mpr (Nat.cast_pos.mpr hN))
  · have hθN : θ ^ N = m := by
      -- θ^N = (m ^ N⁻¹) ^ (N:ℝ) = m ^ (N⁻¹ * N) = m ^ 1 = m
      dsimp [θ]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hm0.le]
      rw [inv_mul_cancel₀]
      · rw [Real.rpow_one]
      · exact_mod_cast (ne_of_gt hN)
    rw [hθN]
    dsimp [m]
    nlinarith

/-- The polynomial power bound: monomial `X^r` times `q^a` is controlled by
`(R^N / θ^N) · θ^j` when `j = N·a + r` and `r ≤ N`. -/
lemma pow_mul_bound {R θ S₀ : ℝ} {N a r j : ℕ}
    (hR1 : 1 ≤ R) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hS0 : 0 ≤ S₀) (hSθ : S₀ ≤ θ ^ N)
    (hj : j = N * a + r) (hrN : r ≤ N) :
    R ^ r * S₀ ^ a ≤ (R ^ N / θ ^ N) * θ ^ j := by
  have hR0 : 0 ≤ R := le_trans zero_le_one hR1
  have hθ0le : 0 ≤ θ := le_of_lt hθ0
  have hθNpos : 0 < θ ^ N := pow_pos hθ0 N
  -- S₀^a ≤ θ^(N*a)
  have hSapow : S₀ ^ a ≤ θ ^ (N * a) := by
    calc
      S₀ ^ a ≤ (θ ^ N) ^ a := pow_le_pow_left₀ hS0 hSθ a
      _ = θ ^ (N * a) := by rw [pow_mul]
  -- main inequality, denominators cleared
  have hmain : R ^ r * S₀ ^ a * θ ^ N ≤ R ^ N * θ ^ j := by
    calc
      R ^ r * S₀ ^ a * θ ^ N = (R ^ r * θ ^ N) * S₀ ^ a := by ring
      _ ≤ (R ^ r * θ ^ N) * θ ^ (N * a) := by
        exact mul_le_mul_of_nonneg_left hSapow (mul_nonneg (pow_nonneg hR0 r) (pow_nonneg hθ0le N))
      _ = R ^ r * (θ ^ N * θ ^ (N * a)) := by rw [mul_assoc]
      _ = R ^ r * θ ^ (N + N * a) := by rw [← pow_add]
      _ ≤ R ^ r * θ ^ (N * a + r) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hR0 r)
        exact pow_le_pow_of_le_one hθ0le hθ1 (by
          rw [add_comm N (N * a)]
          exact Nat.add_le_add_left hrN (N * a))
      _ ≤ R ^ N * θ ^ (N * a + r) := by
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hR1 hrN) (pow_nonneg hθ0le (N * a + r))
      _ = R ^ N * θ ^ j := by rw [hj]
  -- clear the denominator
  calc
    R ^ r * S₀ ^ a ≤ (R ^ N * θ ^ j) / θ ^ N := (le_div_iff₀ hθNpos).2 hmain
    _ = (R ^ N / θ ^ N) * θ ^ j := by rw [div_mul_eq_mul_div]

/-- `X^r · q^a` is monic of degree `r + a·N` when `q` is monic of degree `N`. -/
lemma monic_poly_of_pow {q : ℂ[X]} (hq : q.Monic) (N a r : ℕ) (hdeg : q.natDegree = N) :
    (Polynomial.X ^ r * q ^ a).Monic ∧ (Polynomial.X ^ r * q ^ a).natDegree = r + a * N := by
  have hmonic : (Polynomial.X ^ r * q ^ a).Monic :=
    (Polynomial.monic_X_pow r).mul (hq.pow a)
  have hdegall : (Polynomial.X ^ r * q ^ a).natDegree = r + a * N := by
    rw [(Polynomial.monic_X_pow r).natDegree_mul (hq.pow a)]
    rw [Polynomial.natDegree_X_pow, hq.natDegree_pow, hdeg]
  exact ⟨hmonic, hdegall⟩

/-- **Boosting: one small monic polynomial gives the full polynomial control
of `HedgehogBound` on the same fattening.** -/
theorem hedgehogBound_of_qSmall (S : Finset ℂ) :
    qSmall S → HedgehogBound S := by
  classical
  intro hqsmall
  rcases hqsmall with ⟨ε0, hε0, q, hmonicq, hdegq, hvalq⟩
  let N : ℕ := q.natDegree
  have hNpos : 0 < N := by
    dsimp [N]
    exact Nat.pos_of_ne_zero hdegq
  by_cases hF : (FatStar S ε0).Nonempty
  · -- nonempty fattening: sup bound S₀ < 1, R-bound, θ and C as described
    have hcomp : IsCompact (FatStar S ε0) := isCompact_fatStar S (le_of_lt hε0)
    have hcontEval : Continuous fun X : ℂ => q.eval X := Polynomial.continuous q
    have hcont : Continuous fun X : ℂ => ‖q.eval X‖ := hcontEval.norm
    obtain ⟨x0, hx0, hmax0⟩ := hcomp.exists_isMaxOn hF hcont.continuousOn
    let S₀ : ℝ := ‖q.eval x0‖
    have hS0 : 0 ≤ S₀ := by
      dsimp [S₀]
      exact norm_nonneg _
    have hS1 : S₀ < 1 := by
      dsimp [S₀]
      exact hvalq x0 hx0
    have hmax : ∀ X : ℂ, X ∈ FatStar S ε0 → ‖q.eval X‖ ≤ S₀ := by
      intro X hX
      dsimp [S₀]
      simpa [IsMaxOn] using hmax0 hX
    obtain ⟨θ, hθ0, hθ1, hθgt⟩ := exists_theta_pow_between hS0 hS1 hNpos
    obtain ⟨R, hR1, hR⟩ := exists_bound_fatStar S (le_of_lt hε0)
    refine ⟨ε0, hε0, R ^ N / θ ^ N, ?_, θ, hθ0.le, hθ1, ?_⟩
    · -- 0 < C
      exact div_pos (pow_pos (lt_of_lt_of_le zero_lt_one hR1) N) (pow_pos hθ0 N)
    · intro j
      let a : ℕ := j / N
      let r : ℕ := j % N
      let p : ℂ[X] := Polynomial.X ^ r * q ^ a
      have hrN : r ≤ N := by
        dsimp [r]
        exact le_of_lt (Nat.mod_lt j hNpos)
      have hmonicdeg : p.Monic ∧ p.natDegree = r + a * N := by
        dsimp [p]
        exact monic_poly_of_pow hmonicq N a r rfl
      have hdegj : p.natDegree = j := by
        have hdeg := hmonicdeg.2
        dsimp [a, r] at hdeg
        have hdiv : N * (j / N) + j % N = j := Nat.div_add_mod j N
        calc
          p.natDegree = r + a * N := hmonicdeg.2
          _ = j := by
            dsimp [a, r]
            rw [add_comm, Nat.mul_comm]
            exact hdiv
      refine ⟨p, hmonicdeg.1, hdegj, ?_⟩
      intro X hX
      -- bound: ‖p.eval X‖ ≤ R^r · S₀^a
      have hXnorm : ‖X‖ ≤ R := hR X hX
      have hqe : ‖q.eval X‖ ≤ S₀ := hmax X hX
      have hb1 : ‖p.eval X‖ ≤ R ^ r * S₀ ^ a := by
        dsimp [p]
        calc
          ‖Polynomial.eval X (Polynomial.X ^ r * q ^ a)‖
              = ‖Polynomial.eval X (Polynomial.X ^ r) * Polynomial.eval X (q ^ a)‖ := by
                  rw [Polynomial.eval_mul]
          _ = ‖X ^ r * (Polynomial.eval X q) ^ a‖ := by
                  rw [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_pow]
          _ ≤ ‖X ^ r‖ * ‖(Polynomial.eval X q) ^ a‖ := norm_mul_le _ _
          _ ≤ ‖X‖ ^ r * ‖Polynomial.eval X q‖ ^ a := by
                  exact mul_le_mul (norm_pow_le (X : ℂ) r) (norm_pow_le (Polynomial.eval X q) a)
                    (norm_nonneg ((Polynomial.eval X q) ^ a)) (pow_nonneg (norm_nonneg X) r)
          _ ≤ R ^ r * S₀ ^ a := by
                  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg X) hXnorm r)
                    (pow_le_pow_left₀ (norm_nonneg (Polynomial.eval X q)) hqe a)
                    (pow_nonneg (norm_nonneg (Polynomial.eval X q)) a)
                    (pow_nonneg (le_trans zero_le_one hR1) r)
      -- R^r · S₀^a ≤ C·θ^j
      have hb2 : R ^ r * S₀ ^ a ≤ (R ^ N / θ ^ N) * θ ^ j := by
        exact pow_mul_bound hR1 hθ0 hθ1.le hS0 (le_of_lt hθgt)
          (by dsimp [a, r]; exact (Nat.div_add_mod j N).symm) hrN
      exact le_trans hb1 hb2
  · -- empty fattening: all bounds vacuous
    refine ⟨ε0, hε0, 1, zero_lt_one, (1 / 2 : ℝ), by norm_num, by norm_num, ?_⟩
    intro j
    refine ⟨Polynomial.X ^ j, Polynomial.monic_X_pow j, Polynomial.natDegree_X_pow j, ?_⟩
    intro X hX
    exfalso
    exact hF ⟨X, hX⟩

end Submission.ChebPower

end
