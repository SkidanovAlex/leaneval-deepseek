import Mathlib
import Submission.Work.TMC14Core.Assembly
import Submission.Work.TMC14Core.ratSpecIff
import Submission.Work.TMC14Core.derivDivGapLe
import Submission.Work.TMC14Core.ceyOddDiscDeriv
import Submission.Work.TMC14Core.ratDenomLarge
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC14Core.transferEstimate
import Submission.Work.TMC14Core.discSecondDerivLower
import Submission.Work.TMC14Core.absLowerEven
import Submission.Work.TMC14Core.discEven
import Submission.Work.TMC14Core.exists_coprime_reduce
import Submission.Work.TMC14Core.hyps_reduce
import Submission.Work.TMC14Core.sl2TracePowEasy
import Submission.Work.TMC14Core.ceyEvenDiscDeriv
import Submission.Work.TMC14Core.discZeroAbsEven
import Submission.Work.TMC14Core.evenZeroInterior

/-!
# TMC14Core: the CEY lower bound for the gaps of a rational approximant

`Work.TMC14Core.RatGapBound` (ROUTE_LEAD §4 C14, items 14e + 14f + 14g).

For `α` irrational, `0 < λ ≤ 1`, a window `[c,d] ⊆ Σ_α` and `ε > 0`, every gap of the union
spectrum `ratSpec p q lam` of a sufficiently good approximant `p/q` of `α` lying inside
`[c,d]` has length at least `e^{-εq} λ^{q/2}`.

Argument (AJ Theorem 7.2, the sharpening of Choi–Elliott–Yui):

* the endpoints `a,b` of such a gap are the two roots of one polynomial `Δ - c`, `Δ = disc`;
* hence `b - a = |Δ'(a)| / ∏_{r ≠ a,b}|a - r|`, and the product is bounded by `‖Δ(z)-c‖/η²`
  at the complex point `z = a + iη` (`derivDivGapLe`, using that `Δ - c` has real roots);
* `‖Δ(z)‖ ≤ e^{εq}` for `z` in a complex neighbourhood of `[c,d]`, by 14f:
  `P_LEBasics` (Furman) + `P_BJ` (`L = 0` on `Σ_α`) + the block-perturbation estimate
  (`transferBound`), together with Chambers' formula;
* `|Δ'(a)| ≥ q λ^{⌊(q-1)/2⌋}` at a gap edge (14e, CEY trace identity, `ceyOddDiscDeriv`);
  for even `q` the same argument gives the extra factor `|a|`, which is bounded below either
  by the mean value theorem (`Δ(0) = -c`) or by a Taylor expansion at `0` (`Δ'(0) = 0`
  because `Δ` is even, and `Δ''(0) ≠ 0`);
* finally `ε ↦ ε/N`.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC14Core

/-! ## 1. Elementary bounds -/

/-- Chambers' formula in the form `Δ(z) = tr A_q(θ,z) - chamCoef cos 2πqθ`. -/
theorem ratGapBound_disc_eq (p : ℤ) (q : ℕ) (lam : ℝ) (hpq : Nat.Coprime p.natAbs q)
    (hq : 1 ≤ q) (z : ℂ) (θ : ℝ) :
    (disc p q lam).eval z
      = trAq p q lam z θ
        - chamCoef p q lam * ((Real.cos (2 * Real.pi * (q : ℝ) * θ) : ℝ) : ℂ) := by
  rw [chambers p q lam z hpq hq θ]; ring

/-- Each entry is bounded by the Frobenius norm. -/
theorem ratGapBound_frob_entry (A : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) : ‖A i j‖ ≤ frob A := by
  have hsq : frob A ^ 2 = ‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 + ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2 := by
    rw [frob, Real.sq_sqrt (by positivity)]
  have h2 : ‖A i j‖ ^ 2 ≤ frob A ^ 2 := by
    rw [hsq]
    fin_cases i <;> fin_cases j <;> simp <;>
      nlinarith [sq_nonneg (‖A 0 0‖ : ℝ), sq_nonneg (‖A 0 1‖ : ℝ), sq_nonneg (‖A 1 0‖ : ℝ),
        sq_nonneg (‖A 1 1‖ : ℝ)]
  calc ‖A i j‖ = Real.sqrt (‖A i j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (frob A ^ 2) := Real.sqrt_le_sqrt h2
    _ = frob A := Real.sqrt_sq (Real.sqrt_nonneg _)

/-- `‖tr A_q(θ,z)‖ ≤ 2 frob A_q`. -/
theorem ratGapBound_trace_le_two_frob (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (θ : ℝ) :
    ‖trAq p q lam z θ‖ ≤ 2 * frob (iterC ((p : ℝ) / (q : ℝ)) lam z q θ) := by
  have h1 := ratGapBound_frob_entry (iterC ((p : ℝ) / (q : ℝ)) lam z q θ) 0 0
  have h2 := ratGapBound_frob_entry (iterC ((p : ℝ) / (q : ℝ)) lam z q θ) 1 1
  rw [trAq_eq_trace, Matrix.trace_fin_two]
  calc ‖_ + _‖ ≤ _ + _ := norm_add_le _ _
    _ ≤ 2 * frob (iterC ((p : ℝ) / (q : ℝ)) lam z q θ) := by linarith

/-- On the window `[c,d] ⊆ Σ_α` the Lyapunov exponent vanishes (`P_BJ`). -/
theorem ratGapBound_lyap_zero (hBJ : P_BJ) {α lam c d : ℝ} (hα : Irrational α)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hsub : Set.Icc c d ⊆ amoSpec α lam) :
    ∀ E ∈ Set.Icc c d, lyap α lam (E : ℂ) = 0 := by
  intro E hE
  have h := hBJ α lam hα (ne_of_gt hlam) E (hsub hE)
  rwa [max_eq_left (by simp [Real.log_nonpos hlam.le hlam1])] at h

/-! ## 2. The complex neighbourhood bound for `Δ` (14f) -/

/-- **14f, consequence.**  Under the transfer estimate, `‖Δ(z)‖ ≤ 2e^{εq}` for every `z` in a
complex neighbourhood of the window. -/
theorem ratGapBound_disc_near
    (hTransfer : ∀ (α lam c d : ℝ), Irrational α → 0 < lam → lam ≤ 1 → c < d →
      (∀ E ∈ Set.Icc c d, lyap α lam (E : ℂ) = 0) → ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ ∃ Q : ℕ, ∃ r : ℝ, 0 < r ∧
          ∀ (p : ℤ) (q : ℕ), Q ≤ q → |α - (p : ℝ) / (q : ℝ)| < δ / (q : ℝ) →
            ∀ z : ℂ, (∃ E ∈ Set.Icc c d, ‖z - E‖ < r) → ∀ θ : ℝ,
              frob (iterC ((p : ℝ) / (q : ℝ)) lam z q θ) ≤ Real.exp (ε * (q : ℝ)))
    (α lam c d : ℝ) (hα : Irrational α) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hcd : c < d)
    (hz : ∀ E ∈ Set.Icc c d, lyap α lam (E : ℂ) = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ Q : ℕ, ∃ r : ℝ, 0 < r ∧
      (1 ≤ Q) ∧
      ∀ (p : ℤ) (q : ℕ), Q ≤ q → |α - (p : ℝ) / (q : ℝ)| < δ / (q : ℝ) →
        ∀ z : ℂ, (∃ E ∈ Set.Icc c d, ‖z - E‖ < r) →
          ‖(disc p q lam).eval z‖ ≤ 2 * Real.exp (ε * (q : ℝ)) := by
  obtain ⟨δ, hδ, Q, r, hr, htr⟩ := hTransfer α lam c d hα hlam hlam1 hcd hz ε hε
  refine ⟨δ, hδ, max Q 1, min r 1, lt_min hr one_pos, le_max_right _ _, ?_⟩
  intro p q hQ hpq z hz'
  have hq : 1 ≤ q := le_trans (le_max_right Q 1) hQ
  have hQ' : Q ≤ q := le_trans (le_max_left Q 1) hQ
  have hr' : min r 1 ≤ r := min_le_left _ _
  have hz'' : ∃ E ∈ Set.Icc c d, ‖z - E‖ < r := by
    obtain ⟨E, hE, hE'⟩ := hz'
    exact ⟨E, hE, lt_of_lt_of_le hE' hr'⟩
  rw [disc_eval p q lam z hq]
  calc ‖trAq p q lam z (1 / (4 * (q : ℝ)))‖
      ≤ 2 * frob (iterC ((p : ℝ) / (q : ℝ)) lam z q (1 / (4 * (q : ℝ)))) :=
        ratGapBound_trace_le_two_frob p q lam z _
    _ ≤ 2 * Real.exp (ε * (q : ℝ)) := by
        have := htr p q hQ' hpq z hz'' (1 / (4 * (q : ℝ)))
        linarith


/-! ## 3. Realness of `Δ` at real energies -/

/-- The real transfer matrix. -/
def ratGapBound_tmCr (lam E x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![E - 2 * lam * Real.cos (2 * Real.pi * x), -1; 1, 0]

theorem ratGapBound_tmC_map (lam : ℝ) (E x : ℝ) :
    tmC lam (E : ℂ) x = (ratGapBound_tmCr lam E x).map Complex.ofRealHom := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tmC, ratGapBound_tmCr, Matrix.map_apply, Complex.ofRealHom]

theorem ratGapBound_iterC_re (α lam : ℝ) (E : ℝ) :
    ∀ (n : ℕ) (x : ℝ), ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
      iterC α lam (E : ℂ) n x = A.map Complex.ofRealHom := by
  intro n
  induction n with
  | zero => intro x; exact ⟨1, by rw [iterC]; ext i j; simp [Matrix.one_apply, Matrix.map_apply]⟩
  | succ n ih =>
    intro x
    obtain ⟨A, hA⟩ := ih x
    exact ⟨ratGapBound_tmCr lam E (x + (n : ℝ) * α) * A, by
      rw [iterC, hA, Matrix.map_mul, ratGapBound_tmC_map]⟩

theorem ratGapBound_trAq_re (p : ℤ) (q : ℕ) (lam : ℝ) (E θ : ℝ) :
    ∃ r : ℝ, trAq p q lam (E : ℂ) θ = (r : ℂ) := by
  obtain ⟨A, hA⟩ := ratGapBound_iterC_re ((p : ℝ) / (q : ℝ)) lam E q θ
  refine ⟨A 0 0 + A 1 1, ?_⟩
  rw [trAq, hA]
  simp [Matrix.map_apply, Complex.ofRealHom]

theorem ratGapBound_disc_re (p : ℤ) (q : ℕ) (lam : ℝ) (hq : 1 ≤ q) (E : ℝ) :
    ∃ r : ℝ, (disc p q lam).eval (E : ℂ) = (r : ℂ) := by
  obtain ⟨r, hr⟩ := ratGapBound_trAq_re p q lam E (1 / (4 * (q : ℝ)))
  exact ⟨r, by rw [disc_eval p q lam (E : ℂ) hq, hr]⟩

/-! ## 4. Cauchy's estimate for `Δ'` in the window -/

/-- Cauchy's estimate applied to the polynomial `Δ`: inside the window the derivative is of
the same exponential size as `Δ` itself. -/
theorem ratGapBound_deriv_le
    {α lam c d ε r : ℝ} {p : ℤ} {q : ℕ}
    (hNear : ∀ z : ℂ, (∃ E ∈ Set.Icc c d, ‖z - E‖ < r) →
      ‖(disc p q lam).eval z‖ ≤ 2 * Real.exp (ε * (q : ℝ)))
    (hr : 0 < r) {ξ : ℝ} (hξ : ξ ∈ Set.Icc c d) :
    ‖(disc p q lam).derivative.eval (ξ : ℂ)‖ ≤ 2 * Real.exp (ε * (q : ℝ)) / (r / 2) := by
  have hs : 0 < r / 2 := by linarith
  have hdiff : DiffContOnCl ℂ (fun z : ℂ => (disc p q lam).eval z) (Metric.ball (ξ : ℂ) (r / 2)) := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    exact (Polynomial.differentiable (disc p q lam) z).differentiableWithinAt
  have hbd : ∀ z ∈ Metric.sphere (ξ : ℂ) (r / 2),
      ‖(disc p q lam).eval z‖ ≤ 2 * Real.exp (ε * (q : ℝ)) := by
    intro z hz
    apply hNear z
    refine ⟨ξ, hξ, ?_⟩
    have h : ‖z - (ξ : ℂ)‖ = r / 2 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    rw [h]; linarith
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hs hdiff hbd
  rwa [Polynomial.deriv] at h


/-! ## 5. The two endpoints of a gap are the same level of `Δ` -/

/-- **Gap data.**  If `(a,b)` is a gap of `ratSpec p q lam` (its interior avoids the spectrum
and both endpoints belong to it) then `Δ(a) = Δ(b) = ±(2+2λ^q)`. -/
theorem ratGapBound_gap_data
    (hSpec : ∀ (p : ℤ) (q : ℕ) (lam : ℝ), Nat.Coprime p.natAbs q → 1 ≤ q → 0 < lam → lam ≤ 1 →
      ∀ E : ℝ, E ∈ ratSpec p q lam ↔ ‖(disc p q lam).eval (E : ℂ)‖ ≤ 2 + 2 * lam ^ q)
    {p : ℤ} {q : ℕ} {lam : ℝ} (hpq : Nat.Coprime p.natAbs q) (hq : 1 ≤ q)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) {a b : ℝ} (hab : a < b)
    (hfree : ∀ E ∈ Set.Ioo a b, ∀ θ : ℝ, 2 < ‖trAq p q lam (E : ℂ) θ‖)
    (ha : a ∈ ratSpec p q lam) (hb : b ∈ ratSpec p q lam) :
    ∃ c : ℝ, |c| = 2 + 2 * lam ^ q ∧ (disc p q lam).eval (a : ℂ) = (c : ℂ) ∧
      (disc p q lam).eval (b : ℂ) = (c : ℂ) := by
  set R : ℝ := 2 + 2 * lam ^ q with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  obtain ⟨ra, hra⟩ := ratGapBound_disc_re p q lam hq a
  obtain ⟨rb, hrb⟩ := ratGapBound_disc_re p q lam hq b
  have hIoo : ∀ E ∈ Set.Ioo a b, R < ‖(disc p q lam).eval (E : ℂ)‖ := by
    intro E hE
    by_contra hcon
    simp only [not_lt] at hcon
    obtain ⟨θ, hθ⟩ := (hSpec p q lam hpq hq hlam hlam1 E).mpr hcon
    exact absurd (hfree E hE θ) (not_lt.mpr hθ)
  have hcontD : Continuous fun E : ℝ => (disc p q lam).eval (E : ℂ) :=
    Continuous.comp (by continuity : Continuous fun z : ℂ => (disc p q lam).eval z)
      Complex.continuous_ofReal
  -- if `|Δ a| < R` then `|Δ| < R` near `a`, contradicting the gap
  have haR : R ≤ ‖(disc p q lam).eval (a : ℂ)‖ := by
    by_contra hcon
    simp only [not_le] at hcon
    have hopen : IsOpen {E : ℝ | ‖(disc p q lam).eval (E : ℂ)‖ < R} := by
      apply isOpen_lt
      · exact continuous_norm.comp hcontD
      · exact continuous_const
    obtain ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hcon)
    obtain ⟨E, haE, hEm⟩ := exists_between (lt_min hab (by linarith : a < a + ε))
    have hE : E ∈ Set.Ioo a b := ⟨haE, lt_of_lt_of_le hEm (min_le_left _ _)⟩
    have hEε : E ∈ Metric.ball a ε := by
      rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [lt_of_lt_of_le hEm (min_le_right _ _)]
    exact absurd (hIoo E hE) (not_lt.mpr (le_of_lt (hε' hEε)))
  have hbR : R ≤ ‖(disc p q lam).eval (b : ℂ)‖ := by
    by_contra hcon
    simp only [not_le] at hcon
    have hopen : IsOpen {E : ℝ | ‖(disc p q lam).eval (E : ℂ)‖ < R} := by
      apply isOpen_lt
      · exact continuous_norm.comp hcontD
      · exact continuous_const
    obtain ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hcon)
    obtain ⟨E, hEmax, hEb⟩ := exists_between (max_lt hab (by linarith : b - ε < b))
    have hE : E ∈ Set.Ioo a b := ⟨lt_of_le_of_lt (le_max_left _ _) hEmax, hEb⟩
    have hEε : E ∈ Metric.ball b ε := by
      rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_lt]
      constructor
      · linarith [lt_of_le_of_lt (le_max_right _ _) hEmax]
      · linarith
    exact absurd (hIoo E hE) (not_lt.mpr (le_of_lt (hε' hEε)))
  have hale : ‖(disc p q lam).eval (a : ℂ)‖ ≤ R :=
    (hSpec p q lam hpq hq hlam hlam1 a).mp ha
  have hble : ‖(disc p q lam).eval (b : ℂ)‖ ≤ R :=
    (hSpec p q lam hpq hq hlam hlam1 b).mp hb
  have hraR : |ra| = R := by
    have h1 : ‖(disc p q lam).eval (a : ℂ)‖ = |ra| := by rw [hra]; simp
    rw [h1] at haR hale; linarith
  have hrbR : |rb| = R := by
    have h1 : ‖(disc p q lam).eval (b : ℂ)‖ = |rb| := by rw [hrb]; simp
    rw [h1] at hbR hble; linarith
  have hraval : ra = R ∨ ra = -R := by
    rcases abs_cases ra with ⟨h1, _⟩ | ⟨h1, _⟩
    · left; rw [← h1]; exact hraR
    · right; rw [h1] at hraR; linarith
  have hrbval : rb = R ∨ rb = -R := by
    rcases abs_cases rb with ⟨h1, _⟩ | ⟨h1, _⟩
    · left; rw [← h1]; exact hrbR
    · right; rw [h1] at hrbR; linarith
  have hg : Continuous fun E : ℝ => ((disc p q lam).eval (E : ℂ)).re :=
    Complex.continuous_re.comp hcontD
  -- the two endpoint values of `E ↦ (Δ E).re` are `ra` and `rb`
  have hgval : ∀ E : ℝ, ((disc p q lam).eval (E : ℂ)).re = (if E = a then ra else
      if E = b then rb else ((disc p q lam).eval (E : ℂ)).re) := by
    intro E; by_cases h : E = a
    · rw [if_pos h, h, hra]; simp
    · rw [if_neg h]; by_cases h2 : E = b
      · rw [if_pos h2, h2, hrb]; simp
      · rw [if_neg h2]
  have hsame : ra = rb := by
    rcases hraval with h1 | h1 <;> rcases hrbval with h2 | h2
    · rw [h1, h2]
    · exfalso
      have ha' : ((disc p q lam).eval (a : ℂ)).re = R := by rw [hra]; simp [h1]
      have hb' : ((disc p q lam).eval (b : ℂ)).re = -R := by rw [hrb]; simp [h2]
      have hsv : (0 : ℝ) ∈ Set.Icc (((disc p q lam).eval (b : ℂ)).re)
          (((disc p q lam).eval (a : ℂ)).re) := by
        rw [ha', hb']; exact ⟨by linarith, by linarith⟩
      obtain ⟨y, hy, hgy⟩ := intermediate_value_Icc' hab.le hg.continuousOn hsv
      have hya : y ≠ a := by
        intro h'
        rw [h'] at hgy
        beta_reduce at hgy
        rw [ha'] at hgy
        linarith [hRpos]
      have hyb : y ≠ b := by
        intro h'
        rw [h'] at hgy
        beta_reduce at hgy
        rw [hb'] at hgy
        linarith [hRpos]
      have hyIoo : y ∈ Set.Ioo a b :=
        ⟨lt_of_le_of_ne hy.1 (Ne.symm hya), lt_of_le_of_ne hy.2 hyb⟩
      have hyz : (disc p q lam).eval (y : ℂ) = 0 := by
        obtain ⟨ry, hry⟩ := ratGapBound_disc_re p q lam hq y
        have hry0 : ry = 0 := by
          have := hgy
          beta_reduce at this
          rw [hry] at this
          simpa using this
        rw [hry, hry0]; simp
      have := hIoo y hyIoo
      rw [hyz] at this; simp at this; linarith [hRpos]
    · exfalso
      have ha' : ((disc p q lam).eval (a : ℂ)).re = -R := by rw [hra]; simp [h1]
      have hb' : ((disc p q lam).eval (b : ℂ)).re = R := by rw [hrb]; simp [h2]
      have hsv : (0 : ℝ) ∈ Set.Icc (((disc p q lam).eval (a : ℂ)).re)
          (((disc p q lam).eval (b : ℂ)).re) := by
        rw [ha', hb']; exact ⟨by linarith, by linarith⟩
      obtain ⟨y, hy, hgy⟩ := intermediate_value_Icc hab.le hg.continuousOn hsv
      have hya : y ≠ a := by
        intro h'
        rw [h'] at hgy
        beta_reduce at hgy
        rw [ha'] at hgy
        linarith [hRpos]
      have hyb : y ≠ b := by
        intro h'
        rw [h'] at hgy
        beta_reduce at hgy
        rw [hb'] at hgy
        linarith [hRpos]
      have hyIoo : y ∈ Set.Ioo a b :=
        ⟨lt_of_le_of_ne hy.1 (Ne.symm hya), lt_of_le_of_ne hy.2 hyb⟩
      have hyz : (disc p q lam).eval (y : ℂ) = 0 := by
        obtain ⟨ry, hry⟩ := ratGapBound_disc_re p q lam hq y
        have hry0 : ry = 0 := by
          have := hgy
          beta_reduce at this
          rw [hry] at this
          simpa using this
        rw [hry, hry0]; simp
      have := hIoo y hyIoo
      rw [hyz] at this; simp at this; linarith [hRpos]
    · rw [h1, h2]
  exact ⟨ra, hraR, hra, by rw [hrb, hsame]⟩



--  ## 6. The remaining assembly (plan)
-- 
-- `RatGapBound` is assembled from the pieces proved in the modules of this directory
-- (`ratSpecIff`, `derivDivGapLe`, `ceyOddDiscDeriv`, `ceyEvenDiscDeriv`, `transferBound`,
-- `discZeroEven`, `discEven`, `discSecondDerivQuant`), together with the lemmas proved above
-- (`ratGapBound_disc_near`, `ratGapBound_deriv_le`, `ratGapBound_gap_data`).
-- 
-- For coprime `p, q` and `q` large:
-- 
-- * `norm (Delta z) <= 2 * exp (e1 * q)` for `z` in a complex neighbourhood of `[c,d]`
--   (`ratGapBound_disc_near`, i.e. 14f with `e1 = eps / 16`);
-- * Cauchy's estimate (`ratGapBound_deriv_le`) gives `norm (Delta' xi) <= (4 / r_t) exp (e1 q)`
--   for `xi` in `[c,d]`;
-- * the gap endpoints satisfy `Delta a = Delta b = c` with `norm c = 2 + 2 lam^q`
--   (`ratGapBound_gap_data`);
-- * `b - a >= norm (Delta' a) * eta^2 / norm (Delta (a + I eta) - c)` with `eta = exp (-2 e1 q)`
--   (`derivDivGapLe`);
-- * for odd `q` this yields `b - a >= q lam^m exp (-6 e1 q) >= lam^(q/2) exp (-eps q)`;
-- * for even `q`, `ceyEvenDiscDeriv` gives the extra factor `norm a`, which is bounded below by
--   `exp (-2 e1 q)`: if `Delta 0 = -c` the mean value theorem on `[0,a]` applies (because
--   `Delta a - Delta 0 = 2 (2 + 2 lam^q)`), while if `Delta 0 = c` then `Delta - c` vanishes at
--   `0` with `Delta' 0 = 0` (`Delta` is even) and second derivative non-zero, so the Lagrange
--   remainder at order two bounds `norm a` from below.
-- 
-- Non-reduced `p/q = p'/q'` reduces to `p'/q'`: the union spectrum depends only on the value of
-- the fraction, and `RatDenomLarge` forces the reduced denominator of a good approximant to be
-- large.  Since `q' <= q`, `lam^(q'/2) >= lam^(q/2)` and `exp (-eps q') >= exp (-eps q)`, so the
-- bound at `q'` implies the bound at `q`.
-- 


/-! ## 7. Bookkeeping helpers -/

/-- The norm of a real number, seen as a complex number. -/
theorem ratGapBound_norm_ofReal (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

/-- For `c > 0` and `A > 0`, `exp (c q)` eventually dominates `A`. -/
theorem ratGapBound_eventually_exp_ge {c A : ℝ} (hc : 0 < c) (hA : 0 < A) :
    ∃ N : ℕ, ∀ q : ℕ, N ≤ q → A ≤ Real.exp (c * q) := by
  refine ⟨Nat.ceil (Real.log A / c), fun q hq => ?_⟩
  have h1 : Real.log A / c ≤ (q : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hq)
  have h2 : Real.log A ≤ c * q := by
    rw [div_le_iff₀ hc] at h1; linarith
  calc A = Real.exp (Real.log A) := (Real.exp_log hA).symm
    _ ≤ Real.exp (c * q) := Real.exp_le_exp.mpr h2

/-- For `c > 0` and `B > 0`, `exp (-(c q))` eventually drops below `B`. -/
theorem ratGapBound_eventually_exp_lt {c B : ℝ} (hc : 0 < c) (hB : 0 < B) :
    ∃ N : ℕ, ∀ q : ℕ, N ≤ q → Real.exp (-(c * q)) < B := by
  refine ⟨Nat.ceil (-(Real.log B) / c) + 1, fun q hq => ?_⟩
  have hN : -(Real.log B) / c < ((Nat.ceil (-(Real.log B) / c) + 1 : ℕ) : ℝ) := by
    have h1 : -(Real.log B) / c ≤ (Nat.ceil (-(Real.log B) / c) : ℝ) := Nat.le_ceil _
    push_cast
    linarith
  have hqR : ((Nat.ceil (-(Real.log B) / c) + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h3 : -(Real.log B) / c < (q : ℝ) := lt_of_lt_of_le hN hqR
  have h4 : -(Real.log B) < c * q := by
    rw [div_lt_iff₀ hc] at h3; linarith
  have h5 : -(c * q) < Real.log B := by linarith
  calc Real.exp (-(c * q)) < Real.exp (Real.log B) := Real.exp_lt_exp.mpr h5
    _ = B := Real.exp_log hB

/-- `lam ^ y ≤ lam ^ x` for `0 < lam ≤ 1` and `x ≤ y`. -/
theorem ratGapBound_rpow_le {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) {x y : ℝ}
    (hxy : x ≤ y) : lam ^ y ≤ lam ^ x := by
  rw [Real.rpow_def_of_pos hlam, Real.rpow_def_of_pos hlam]
  refine Real.exp_le_exp.mpr ?_
  have h : Real.log lam ≤ 0 := Real.log_nonpos hlam.le hlam1
  nlinarith

/-- Cauchy's estimate for the derivative of a polynomial on a disc of half the radius. -/
theorem ratGapBound_cauchy_step {M R : ℝ} {P : Polynomial ℂ} {c : ℂ} (hR : 0 < R)
    (hbd : ∀ z : ℂ, ‖z - c‖ ≤ R → ‖P.eval z‖ ≤ M) :
    ∀ z : ℂ, ‖z - c‖ ≤ R / 2 → ‖P.derivative.eval z‖ ≤ 2 * M / R := by
  intro z hz
  have hzlt : ‖z - c‖ < R := by
    have : R / 2 < R := by linarith
    linarith
  have hdiff : DiffContOnCl ℂ (fun w : ℂ => P.eval w) (Metric.ball z (R / 2)) := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    exact (Polynomial.differentiable P w).differentiableWithinAt
  have hsphere : ∀ w ∈ Metric.sphere z (R / 2), ‖P.eval w‖ ≤ M := by
    intro w hw
    refine hbd w ?_
    have h1 : ‖w - z‖ = R / 2 := by
      have := Metric.mem_sphere.mp hw
      rwa [dist_eq_norm] at this
    have h2 : ‖w - c‖ ≤ ‖w - z‖ + ‖z - c‖ := by
      calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by congr 1; ring
        _ ≤ ‖w - z‖ + ‖z - c‖ := norm_add_le _ _
    rw [h1] at h2
    linarith
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := R / 2) (C := M)
    (by linarith) hdiff hsphere
  rw [Polynomial.deriv] at h
  calc ‖P.derivative.eval z‖ ≤ M / (R / 2) := h
    _ = 2 * M / R := by ring

/-- Bounds for `Δ'` and `Δ'''` on a short segment meeting the window. -/
theorem ratGapBound_segment_bounds {M rt : ℝ} {P : Polynomial ℂ} {a : ℝ} (hrt : 0 < rt)
    (hM : 0 < M) (hbd : ∀ z : ℂ, ‖z - (a : ℂ)‖ < rt → ‖P.eval z‖ ≤ M) {ξ : ℝ}
    (hξ : |ξ - a| < rt / 2) :
    ‖P.derivative.eval (ξ : ℂ)‖ ≤ 4 * M / rt ∧
      ‖(Polynomial.derivative (Polynomial.derivative (Polynomial.derivative P))).eval (ξ : ℂ)‖
        ≤ 512 * M / rt ^ 3 := by
  have hξc : ‖(ξ : ℂ) - (a : ℂ)‖ = |ξ - a| := by
    rw [← ratGapBound_norm_ofReal (ξ - a)]; congr 1; push_cast; ring
  have hball : ∀ z : ℂ, ‖z - (ξ : ℂ)‖ ≤ rt / 2 → ‖P.eval z‖ ≤ M := by
    intro z hz
    refine hbd z ?_
    have h2 : ‖z - (a : ℂ)‖ ≤ ‖z - (ξ : ℂ)‖ + ‖(ξ : ℂ) - (a : ℂ)‖ := by
      calc ‖z - (a : ℂ)‖ = ‖(z - (ξ : ℂ)) + ((ξ : ℂ) - (a : ℂ))‖ := by congr 1; ring
        _ ≤ ‖z - (ξ : ℂ)‖ + ‖(ξ : ℂ) - (a : ℂ)‖ := norm_add_le _ _
    rw [hξc] at h2
    linarith
  have hrt2 : (0:ℝ) < rt / 2 := by linarith
  have hrt4 : (0:ℝ) < (rt / 2) / 2 := by linarith
  have hrt8 : (0:ℝ) < ((rt / 2) / 2) / 2 := by linarith
  have hrt16 : (0:ℝ) < (((rt / 2) / 2) / 2) / 2 := by linarith
  have s1 : ∀ z : ℂ, ‖z - (ξ : ℂ)‖ ≤ (rt / 2) / 2 → ‖P.derivative.eval z‖ ≤ 2 * M / (rt / 2) :=
    ratGapBound_cauchy_step hrt2 hball
  have s2 : ∀ z : ℂ, ‖z - (ξ : ℂ)‖ ≤ ((rt / 2) / 2) / 2 →
      ‖(Polynomial.derivative (Polynomial.derivative P)).eval z‖ ≤
        2 * (2 * M / (rt / 2)) / ((rt / 2) / 2) :=
    ratGapBound_cauchy_step hrt4 s1
  have s3 : ∀ z : ℂ, ‖z - (ξ : ℂ)‖ ≤ (((rt / 2) / 2) / 2) / 2 →
      ‖(Polynomial.derivative (Polynomial.derivative (Polynomial.derivative P))).eval z‖ ≤
        2 * (2 * (2 * M / (rt / 2)) / ((rt / 2) / 2)) / (((rt / 2) / 2) / 2) :=
    ratGapBound_cauchy_step hrt8 (fun z hz => s2 z (by linarith [hz]))
  have hfirst : ‖P.derivative.eval (ξ : ℂ)‖ ≤ 2 * M / (rt / 2) :=
    s1 (ξ : ℂ) (by simp only [sub_self, norm_zero]; linarith)
  have hthird : ‖(Polynomial.derivative (Polynomial.derivative (Polynomial.derivative P))).eval
      (ξ : ℂ)‖ ≤ 2 * (2 * (2 * M / (rt / 2)) / ((rt / 2) / 2)) / (((rt / 2) / 2) / 2) :=
    s3 (ξ : ℂ) (by simp only [sub_self, norm_zero]; linarith)
  constructor
  · calc ‖P.derivative.eval (ξ : ℂ)‖ ≤ 2 * M / (rt / 2) := hfirst
      _ = 4 * M / rt := by ring
  · calc ‖(Polynomial.derivative (Polynomial.derivative (Polynomial.derivative P))).eval (ξ : ℂ)‖
        ≤ 2 * (2 * (2 * M / (rt / 2)) / ((rt / 2) / 2)) / (((rt / 2) / 2) / 2) := hthird
      _ = 512 * M / rt ^ 3 := by field_simp; ring

/-- `Δ(0) = ±(2 + 2 λ^q)`: the value of the discriminant at `0` is a real number of modulus
`2 + 2 λ^q`. -/
theorem ratGapBound_disc_zero_pm (p : ℤ) (q : ℕ) (lam : ℝ) (hq : 1 ≤ q)
    (hval : ‖(disc p q lam).eval (0 : ℂ)‖ = 2 + 2 * lam ^ q) :
    (disc p q lam).eval (0 : ℂ) = ((2 + 2 * lam ^ q : ℝ) : ℂ) ∨
      (disc p q lam).eval (0 : ℂ) = ((-(2 + 2 * lam ^ q) : ℝ) : ℂ) := by
  obtain ⟨r, hr⟩ := ratGapBound_disc_re p q lam hq 0
  rw [Complex.ofReal_zero] at hr
  have hrabs : |r| = 2 + 2 * lam ^ q := by
    have h := hval
    rw [hr] at h
    rwa [ratGapBound_norm_ofReal] at h
  rcases abs_cases r with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have hr' : r = 2 + 2 * lam ^ q := by rw [← h1]; exact hrabs
    rw [hr, hr']
  · right
    have hr' : r = -(2 + 2 * lam ^ q) := by
      have h3 : -r = 2 + 2 * lam ^ q := by rw [← h1]; exact hrabs
      linarith
    rw [hr, hr']

/-! ## 8. The coprime case of `RatGapBound` -/

/-- **The coprime case.**  The three analytic inputs which the library does not contain yet
(the value `|Δ(0)| = 2 + 2λ^q` for even `q`, the fact that `0` is an interior point of the
union spectrum for even `q`, and the even-`q` CEY derivative bound) are hypotheses. -/
theorem ratGapBound_coprime_of
    (hLE : P_LEBasics)
    (hZeroAbs : ∀ (p : ℤ) (q m : ℕ), q = 2*m+2 → Nat.Coprime p.natAbs q → ∀ lam : ℝ, 0 < lam →
      ‖(disc p q lam).eval (0:ℂ)‖ = 2 + 2*lam^q)
    (hInterior : ∀ (p : ℤ) (q m : ℕ), q = 2*m+2 → Nat.Coprime p.natAbs q → ∀ lam : ℝ, 0 < lam →
      lam ≤ 1 → ‖(disc p q lam).eval (0:ℂ)‖ = 2 + 2*lam^q →
      ∃ δ : ℝ, 0 < δ ∧ ∀ E : ℝ, |E| < δ → ‖(disc p q lam).eval (E:ℂ)‖ ≤ 2 + 2*lam^q)
    (hEven : ∀ (p : ℤ) (q m : ℕ), q = 2*m+2 → Nat.Coprime p.natAbs q → ∀ lam : ℝ, 0 < lam →
      lam ≤ 1 → ∀ a : ℝ, ∀ c : ℂ, ‖c‖ ≤ 2 + 2*lam^q → (disc p q lam).eval (a:ℂ) = c →
      (q:ℝ) * lam^m * |a| ≤ ‖(disc p q lam).derivative.eval (a:ℂ)‖)
    (α lam c d : ℝ) (hα : Irrational α) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hcd : c < d)
    (hzero : ∀ E ∈ Set.Icc c d, lyap α lam (E:ℂ) = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ Q : ℕ, ∀ (p : ℤ) (q : ℕ), Q ≤ q →
      |α - (p:ℝ)/(q:ℝ)| < δ/(q:ℝ) → Nat.Coprime p.natAbs q →
      ∀ a b : ℝ, c ≤ a → a < b → b ≤ d →
        (∀ E ∈ Set.Ioo a b, ∀ θ : ℝ, 2 < ‖trAq p q lam (E:ℂ) θ‖) →
        a ∈ ratSpec p q lam → b ∈ ratSpec p q lam →
        Real.exp (-(ε * (q:ℝ))) * lam ^ ((q:ℝ)/2) ≤ b - a := by
  set e1 : ℝ := ε / 16 with he1def
  have he1 : 0 < e1 := by rw [he1def]; linarith
  obtain ⟨δt, hδt, Qt, rt, hrt, hQt1, hnear⟩ :=
    ratGapBound_disc_near (transferEstimate hLE) α lam c d hα hlam hlam1 hcd hzero e1 he1
  have hb1 : ∀ᶠ q : ℕ in Filter.atTop, 16 ≤ Real.exp (e1 * q) :=
    Filter.eventually_atTop.mpr (ratGapBound_eventually_exp_ge he1 (by norm_num))
  have hb2 : ∀ᶠ q : ℕ in Filter.atTop, 16 / rt ≤ Real.exp (3 * e1 * q) :=
    Filter.eventually_atTop.mpr (ratGapBound_eventually_exp_ge (by linarith) (by positivity))
  have hb3 : ∀ᶠ q : ℕ in Filter.atTop, 2048 / rt ^ 3 ≤ Real.exp (3 * e1 * q) :=
    Filter.eventually_atTop.mpr (ratGapBound_eventually_exp_ge (by linarith) (by positivity))
  have hb4 : ∀ᶠ q : ℕ in Filter.atTop, Real.exp (-(2 * e1 * q)) < rt :=
    Filter.eventually_atTop.mpr (ratGapBound_eventually_exp_lt (by linarith) hrt)
  have hb5 : ∀ᶠ q : ℕ in Filter.atTop, Real.exp (-(4 * e1 * q)) < rt / 2 :=
    Filter.eventually_atTop.mpr (ratGapBound_eventually_exp_lt (by linarith) (by positivity))
  have hb6 : ∀ᶠ q : ℕ in Filter.atTop, 3 ≤ q := Filter.eventually_ge_atTop 3
  obtain ⟨QL, hQL⟩ := Filter.eventually_atTop.mp
    (hb1.and (hb2.and (hb3.and (hb4.and (hb5.and hb6)))))
  refine ⟨δt, hδt, max Qt QL, ?_⟩
  intro p q hQ hαp hcop a b hca hab hbd hfree haspec hbspec
  have hQtq : Qt ≤ q := le_trans (le_max_left _ _) hQ
  have hQLq : QL ≤ q := le_trans (le_max_right _ _) hQ
  obtain ⟨h16exp, h16le, h2048le, he2lt, he4lt, hq3⟩ := hQL q hQLq
  have hq1 : 1 ≤ q := le_trans hQt1 hQtq
  have hnear' : ∀ z : ℂ, (∃ E ∈ Set.Icc c d, ‖z - E‖ < rt) →
      ‖(disc p q lam).eval z‖ ≤ 2 * Real.exp (e1 * (q:ℝ)) := hnear p q hQtq hαp
  obtain ⟨c0, hc0abs, hDa, hDb⟩ :=
    ratGapBound_gap_data ratSpecIff hcop hq1 hlam hlam1 hab hfree haspec hbspec
  have hc0le : |c0| ≤ 2 + 2 * lam ^ q := le_of_eq hc0abs
  have hc0norm : ‖((c0:ℝ):ℂ)‖ = |c0| := ratGapBound_norm_ofReal c0
  set eta : ℝ := Real.exp (-(2 * e1 * (q:ℝ))) with hetadef
  have hetapos : 0 < eta := Real.exp_pos _
  have hetalt : eta < rt := by rw [hetadef]; exact he2lt
  have hetasq : eta ^ 2 = Real.exp (-(4 * e1 * (q:ℝ))) := by
    rw [hetadef, sq, ← Real.exp_add]; congr 1; ring
  have hCpos : (0:ℝ) < 3 * Real.exp (e1 * (q:ℝ)) := by positivity
  have h3le' : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq3
  have hComplex : ‖(disc p q lam).eval ((a:ℂ) + eta * Complex.I) - (c0:ℂ)‖
      ≤ 3 * Real.exp (e1 * (q:ℝ)) := by
    have hz : ∃ E ∈ Set.Icc c d, ‖((a:ℂ) + eta * Complex.I) - E‖ < rt := by
      refine ⟨a, ⟨hca, le_trans hab.le hbd⟩, ?_⟩
      have hsub : ((a:ℂ) + eta * Complex.I) - (a:ℂ) = (eta:ℂ) * Complex.I := by ring
      have he : ‖(eta:ℂ)‖ = eta := by
        rw [ratGapBound_norm_ofReal, abs_of_pos hetapos]
      rw [hsub, norm_mul, he, Complex.norm_I, mul_one]
      exact hetalt
    have h1 := hnear' _ hz
    have h3 : ‖((c0:ℝ):ℂ)‖ ≤ 4 := by
      rw [hc0norm, hc0abs]
      have hle1 : lam ^ q ≤ 1 := by simpa using pow_le_pow_left₀ hlam.le hlam1 q
      linarith
    calc ‖(disc p q lam).eval ((a:ℂ) + eta * Complex.I) - (c0:ℂ)‖
        ≤ ‖(disc p q lam).eval ((a:ℂ) + eta * Complex.I)‖ + ‖((c0:ℝ):ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 * Real.exp (e1 * (q:ℝ)) + 4 := by linarith
      _ ≤ 3 * Real.exp (e1 * (q:ℝ)) := by linarith
  have hdiv := derivDivGapLe p q lam hcop hq1 hlam hlam1 c0 hc0le hDa hDb hab hetapos hComplex
  have hkey : Real.exp (-(5 * e1 * (q:ℝ)))
      * ‖(disc p q lam).derivative.eval (a:ℂ)‖ / 3 ≤ b - a := by
    have hbapos : 0 < b - a := sub_pos.mpr hab
    have h1 : ‖(disc p q lam).derivative.eval (a:ℂ)‖
        ≤ (3 * Real.exp (e1 * (q:ℝ))) / eta^2 * (b - a) := (div_le_iff₀ hbapos).mp hdiv
    have h3 : ‖(disc p q lam).derivative.eval (a:ℂ)‖ * eta^2
        ≤ (3 * Real.exp (e1 * (q:ℝ))) * (b - a) := by
      calc ‖(disc p q lam).derivative.eval (a:ℂ)‖ * eta^2
          ≤ ((3 * Real.exp (e1 * (q:ℝ))) / eta^2 * (b - a)) * eta^2 :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (3 * Real.exp (e1 * (q:ℝ))) * (b - a) := by field_simp
    have h4 : ‖(disc p q lam).derivative.eval (a:ℂ)‖ * eta^2
        / (3 * Real.exp (e1 * (q:ℝ))) ≤ b - a := by
      rw [div_le_iff₀ hCpos]; linarith
    have h5 : Real.exp (-(5 * e1 * (q:ℝ))) = eta^2 / Real.exp (e1 * (q:ℝ)) := by
      rw [hetasq, ← Real.exp_sub]; congr 1; ring
    rw [h5]
    have h6 : eta^2 / Real.exp (e1 * (q:ℝ))
        * ‖(disc p q lam).derivative.eval (a:ℂ)‖ / 3
        = ‖(disc p q lam).derivative.eval (a:ℂ)‖ * eta^2 / (3 * Real.exp (e1 * (q:ℝ))) := by
      ring
    rw [h6]; exact h4
  have hseg : ∀ ξ : ℝ, ξ ∈ Set.Icc (min 0 a) (max 0 a) → |ξ - a| ≤ |a| := by
    intro ξ hξ
    rcases lt_or_ge 0 a with ha0 | ha0
    · rw [min_eq_left ha0.le, max_eq_right ha0.le] at hξ
      rw [abs_of_nonpos (by linarith [hξ.2] : ξ - a ≤ 0), abs_of_nonneg ha0.le]
      linarith [hξ.1]
    · rw [min_eq_right ha0, max_eq_left ha0] at hξ
      rw [abs_of_nonneg (by linarith [hξ.1] : (0:ℝ) ≤ ξ - a), abs_of_nonpos ha0]
      linarith [hξ.2]
  have hseg_hnear : ∀ z : ℂ, ‖z - (a:ℂ)‖ < rt →
      ‖(disc p q lam).eval z‖ ≤ 2 * Real.exp (e1 * (q:ℝ)) :=
    fun z hz => hnear' z ⟨a, ⟨hca, le_trans hab.le hbd⟩, hz⟩
  rcases Nat.even_or_odd q with hm | hm
  · -- ## even `q`
    obtain ⟨m, hm⟩ := hm
    have hm2 : 2 ≤ m := by omega
    have hmq : q = 2 * (m - 1) + 2 := by omega
    have hval0 : ‖(disc p q lam).eval (0:ℂ)‖ = 2 + 2*lam^q := hZeroAbs p q (m-1) hmq hcop lam hlam
    have hzero' : (disc p q lam).eval 0 = ((2 + 2*lam^q:ℝ):ℂ) ∨
        (disc p q lam).eval 0 = ((-(2 + 2*lam^q):ℝ):ℂ) :=
      ratGapBound_disc_zero_pm p q lam hq1 hval0
    have hevenpoly : ∀ z : ℂ, (disc p q lam).eval (-z) = (disc p q lam).eval z :=
      discEven p q (m-1) hmq hcop lam
    have hEven' : (q:ℝ) * lam^(m-1) * |a| ≤ ‖(disc p q lam).derivative.eval (a:ℂ)‖ :=
      hEven p q (m-1) hmq hcop lam hlam hlam1 a c0 (by rw [hc0norm]; exact hc0le) hDa
    have hage : Real.exp (-(4 * e1 * (q:ℝ))) ≤ |a| := by
      by_contra hcon
      push_neg at hcon
      have hasmall : |a| < rt / 2 := lt_trans hcon he4lt
      have hK : ∀ ξ ∈ Set.Icc (min 0 a) (max 0 a),
          ‖(disc p q lam).derivative.eval (ξ:ℂ)‖ ≤ 8 * Real.exp (e1 * (q:ℝ)) / rt := by
        intro ξ hξ
        calc ‖(disc p q lam).derivative.eval (ξ:ℂ)‖
            ≤ 4 * (2 * Real.exp (e1 * (q:ℝ))) / rt :=
              (ratGapBound_segment_bounds (M := 2 * Real.exp (e1 * (q:ℝ))) hrt (by positivity)
                hseg_hnear (lt_of_le_of_lt (hseg ξ hξ) hasmall)).1
          _ = 8 * Real.exp (e1 * (q:ℝ)) / rt := by ring
      have hK2 : ∀ ξ ∈ Set.Icc (min 0 a) (max 0 a),
          ‖(Polynomial.derivative (Polynomial.derivative (Polynomial.derivative (disc p q lam)))).eval
            (ξ:ℂ)‖ ≤ 1024 * Real.exp (e1 * (q:ℝ)) / rt ^ 3 := by
        intro ξ hξ
        calc ‖(Polynomial.derivative (Polynomial.derivative (Polynomial.derivative (disc p q lam)))).eval
              (ξ:ℂ)‖
            ≤ 512 * (2 * Real.exp (e1 * (q:ℝ))) / rt ^ 3 :=
              (ratGapBound_segment_bounds (M := 2 * Real.exp (e1 * (q:ℝ))) hrt (by positivity)
                hseg_hnear (lt_of_le_of_lt (hseg ξ hξ) hasmall)).2
          _ = 1024 * Real.exp (e1 * (q:ℝ)) / rt ^ 3 := by ring
      have hSecond : (1:ℝ) ≤
          ‖(Polynomial.derivative (Polynomial.derivative (disc p q lam))).eval 0‖ := by
        have := discSecondDerivLower p q (m-1) hmq hcop lam hlam hval0
        linarith
      have hane : a ≠ 0 := by
        intro h0
        obtain ⟨δ, hδpos, hint⟩ := hInterior p q (m-1) hmq hcop lam hlam hlam1 hval0
        have hbpos : 0 < b := by rw [← h0]; exact hab
        set t : ℝ := min δ b / 2 with htdef
        have htmem : t ∈ Set.Ioo a b := by
          rw [htdef, h0]
          exact ⟨by linarith [lt_min hδpos hbpos], by linarith [min_le_right δ b]⟩
        have htδ : |t| < δ := by
          rw [htdef, abs_of_pos (by positivity)]
          linarith [min_le_left δ b]
        have hle := hint t htδ
        have hgt : 2 + 2*lam^q < ‖(disc p q lam).eval (t:ℂ)‖ := by
          by_contra hc
          push_neg at hc
          obtain ⟨θ, hθ⟩ := (ratSpecIff p q lam hcop hq1 hlam hlam1 t).mpr hc
          exact absurd (hfree t htmem θ) (not_lt.mpr hθ)
        linarith
      have hlower := absLowerEven p q (m-1) hmq hcop lam hlam hane hDa hc0abs hzero' hSecond
        hevenpoly hK hK2 (by positivity) (by positivity)
      have h16 : 16 * Real.exp (-(3 * e1 * (q:ℝ))) ≤ rt := by
        have h1 : 16 / Real.exp (3 * e1 * (q:ℝ)) ≤ rt := by
          rw [div_le_iff₀ (Real.exp_pos _)]
          linarith [(div_le_iff₀ hrt).mp h16le]
        have h2 : 16 * Real.exp (-(3 * e1 * (q:ℝ))) = 16 / Real.exp (3 * e1 * (q:ℝ)) := by
          rw [eq_div_iff (ne_of_gt (Real.exp_pos _)), mul_assoc, ← Real.exp_add]
          simp
        rwa [h2]
      have h2048 : 2048 * Real.exp (-(3 * e1 * (q:ℝ))) ≤ rt ^ 3 := by
        have h1 : 2048 / Real.exp (3 * e1 * (q:ℝ)) ≤ rt ^ 3 := by
          rw [div_le_iff₀ (Real.exp_pos _)]
          linarith [(div_le_iff₀ (by positivity : (0:ℝ) < rt ^ 3)).mp h2048le]
        have h2 : 2048 * Real.exp (-(3 * e1 * (q:ℝ))) = 2048 / Real.exp (3 * e1 * (q:ℝ)) := by
          rw [eq_div_iff (ne_of_gt (Real.exp_pos _)), mul_assoc, ← Real.exp_add]
          simp
        rwa [h2]
      have hbound1 : Real.exp (-(4 * e1 * (q:ℝ)))
          ≤ 1 / (2 * (8 * Real.exp (e1 * (q:ℝ)) / rt)) := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * (8 * Real.exp (e1 * (q:ℝ)) / rt))]
        have hcalc : Real.exp (-(4 * e1 * (q:ℝ))) * (2 * (8 * Real.exp (e1 * (q:ℝ)) / rt))
            = 16 * Real.exp (-(3 * e1 * (q:ℝ))) / rt := by
          have h1 : (2:ℝ) * (8 * Real.exp (e1 * (q:ℝ)) / rt)
              = 16 * Real.exp (e1 * (q:ℝ)) / rt := by ring
          rw [h1]
          rw [show Real.exp (-(4 * e1 * (q:ℝ))) * (16 * Real.exp (e1 * (q:ℝ)) / rt)
              = 16 * (Real.exp (-(4 * e1 * (q:ℝ))) * Real.exp (e1 * (q:ℝ))) / rt by ring]
          rw [← Real.exp_add]
          rw [show -(4 * e1 * (q:ℝ)) + e1 * (q:ℝ) = -(3 * e1 * (q:ℝ)) by ring]
        rw [hcalc]
        exact (div_le_one hrt).mpr h16
      have hbound2 : Real.exp (-(4 * e1 * (q:ℝ)))
          ≤ 1 / (2 * (1024 * Real.exp (e1 * (q:ℝ)) / rt ^ 3)) := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * (1024 * Real.exp (e1 * (q:ℝ)) / rt ^ 3))]
        have hcalc : Real.exp (-(4 * e1 * (q:ℝ))) * (2 * (1024 * Real.exp (e1 * (q:ℝ)) / rt ^ 3))
            = 2048 * Real.exp (-(3 * e1 * (q:ℝ))) / rt ^ 3 := by
          have h1 : (2:ℝ) * (1024 * Real.exp (e1 * (q:ℝ)) / rt ^ 3)
              = 2048 * Real.exp (e1 * (q:ℝ)) / rt ^ 3 := by ring
          rw [h1]
          rw [show Real.exp (-(4 * e1 * (q:ℝ))) * (2048 * Real.exp (e1 * (q:ℝ)) / rt ^ 3)
              = 2048 * (Real.exp (-(4 * e1 * (q:ℝ))) * Real.exp (e1 * (q:ℝ))) / rt ^ 3 by ring]
          rw [← Real.exp_add]
          rw [show -(4 * e1 * (q:ℝ)) + e1 * (q:ℝ) = -(3 * e1 * (q:ℝ)) by ring]
        rw [hcalc]
        exact (div_le_one (by positivity : (0:ℝ) < rt ^ 3)).mpr h2048
      exact absurd (le_trans (le_min hbound1 hbound2) hlower) (not_le.mpr hcon)
    have h2 : lam ^ ((q:ℝ)/2) ≤ (q:ℝ) * lam^(m-1) / 3 := by
      have hsplit : (q:ℝ)/2 = ((m-1:ℕ):ℝ) + 1 := by rw [hmq]; push_cast; ring
      rw [hsplit, Real.rpow_add hlam, Real.rpow_one, Real.rpow_natCast]
      have h5 : (1:ℝ) ≤ (q:ℝ)/3 := by linarith
      have hnn : (0:ℝ) ≤ lam^(m-1) := by positivity
      calc lam^(m-1) * lam ≤ lam^(m-1) * 1 := mul_le_mul_of_nonneg_left hlam1 hnn
        _ ≤ lam^(m-1) * ((q:ℝ)/3) := mul_le_mul_of_nonneg_left h5 hnn
        _ = (q:ℝ) * lam^(m-1) / 3 := by ring
    have h1 : Real.exp (-(ε * (q:ℝ))) ≤ Real.exp (-(9 * e1 * (q:ℝ))) := by
      apply Real.exp_le_exp.mpr
      rw [he1def]; nlinarith
    have h3 : Real.exp (-(9 * e1 * (q:ℝ))) * ((q:ℝ) * lam^(m-1) / 3) ≤ b - a := by
      have hstep1 : Real.exp (-(9 * e1 * (q:ℝ))) * ((q:ℝ) * lam^(m-1) / 3)
          = Real.exp (-(5 * e1 * (q:ℝ)))
            * ((q:ℝ) * lam^(m-1) * Real.exp (-(4 * e1 * (q:ℝ)))) / 3 := by
        rw [show -(9 * e1 * (q:ℝ)) = -(5 * e1 * (q:ℝ)) + (-(4 * e1 * (q:ℝ))) by ring, Real.exp_add]
        ring
      have hstep2 : Real.exp (-(5 * e1 * (q:ℝ)))
            * ((q:ℝ) * lam^(m-1) * Real.exp (-(4 * e1 * (q:ℝ)))) / 3
          ≤ Real.exp (-(5 * e1 * (q:ℝ))) * ((q:ℝ) * lam^(m-1) * |a|) / 3 := by
        have h4 : (q:ℝ) * lam^(m-1) * Real.exp (-(4 * e1 * (q:ℝ)))
            ≤ (q:ℝ) * lam^(m-1) * |a| := mul_le_mul_of_nonneg_left hage (by positivity)
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (Real.exp_nonneg _))
          (by norm_num : (0:ℝ) ≤ 3)
      have hstep3 : Real.exp (-(5 * e1 * (q:ℝ))) * ((q:ℝ) * lam^(m-1) * |a|) / 3
          ≤ Real.exp (-(5 * e1 * (q:ℝ))) * ‖(disc p q lam).derivative.eval (a:ℂ)‖ / 3 := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hEven' (Real.exp_nonneg _))
          (by norm_num : (0:ℝ) ≤ 3)
      rw [hstep1]
      exact le_trans hstep2 (le_trans hstep3 hkey)
    exact le_trans (mul_le_mul h1 h2 (Real.rpow_nonneg (le_of_lt hlam) _) (Real.exp_nonneg _)) h3
  · -- ## odd `q`
    obtain ⟨m, hm⟩ := hm
    have hmq : q = 2*m+1 := by omega
    have hcea : (q:ℝ) * lam^m ≤ ‖(disc p q lam).derivative.eval (a:ℂ)‖ :=
      ceyOddDiscDeriv p q m hmq hcop lam hlam a c0 (by rw [hc0norm]; exact hc0le) hDa
    have h2 : lam ^ ((q:ℝ)/2) ≤ (q:ℝ) * lam^m / 3 := by
      have hsplit : (q:ℝ)/2 = (m:ℝ) + 1/2 := by rw [hmq]; push_cast; ring
      rw [hsplit, Real.rpow_add hlam, Real.rpow_natCast]
      have h3 : lam^((1:ℝ)/2) ≤ 1 := Real.rpow_le_one hlam.le hlam1 (by norm_num)
      have h5 : (1:ℝ) ≤ (q:ℝ)/3 := by linarith
      have hnn : (0:ℝ) ≤ lam^m := by positivity
      calc lam^m * lam^((1:ℝ)/2) ≤ lam^m * 1 := mul_le_mul_of_nonneg_left h3 hnn
        _ ≤ lam^m * ((q:ℝ)/3) := mul_le_mul_of_nonneg_left h5 hnn
        _ = (q:ℝ) * lam^m / 3 := by ring
    have h1 : Real.exp (-(ε * (q:ℝ))) ≤ Real.exp (-(5 * e1 * (q:ℝ))) := by
      apply Real.exp_le_exp.mpr
      rw [he1def]; nlinarith
    have h3 : Real.exp (-(5 * e1 * (q:ℝ))) * ((q:ℝ) * lam^m / 3) ≤ b - a := by
      have h4 : Real.exp (-(5 * e1 * (q:ℝ))) * ((q:ℝ) * lam^m / 3)
          ≤ Real.exp (-(5 * e1 * (q:ℝ))) * ‖(disc p q lam).derivative.eval (a:ℂ)‖ / 3 := by
        have h5 : (q:ℝ) * lam^m / 3 ≤ ‖(disc p q lam).derivative.eval (a:ℂ)‖ / 3 := by linarith
        calc Real.exp (-(5 * e1 * (q:ℝ))) * ((q:ℝ) * lam^m / 3)
            ≤ Real.exp (-(5 * e1 * (q:ℝ))) * (‖(disc p q lam).derivative.eval (a:ℂ)‖ / 3) :=
              mul_le_mul_of_nonneg_left h5 (Real.exp_nonneg _)
          _ = Real.exp (-(5 * e1 * (q:ℝ))) * ‖(disc p q lam).derivative.eval (a:ℂ)‖ / 3 := by ring
      linarith [h4, hkey]
    exact le_trans (mul_le_mul h1 h2 (Real.rpow_nonneg (le_of_lt hlam) _) (Real.exp_nonneg _)) h3


/-! ## 9. Removing the coprimality hypothesis -/

/-- **Reduction of a non-reduced fraction to a reduced one.**  Given the coprime statement,
`RatGapBound` follows: the `q`-step transfer matrix of `p/q` is the `g`-th power of the
`q'`-step transfer matrix of the reduced fraction `p'/q'` (`g = q / gcd p q`), the Chebyshev
trace lemma moves the gap hypothesis both ways, and `RatDenomLarge` forces `q'` to be large
for a good approximant. -/
theorem ratGapBound_of_coprime
    (hg : ∀ (α lam c d : ℝ), Irrational α → 0 < lam → lam ≤ 1 → c < d →
      (∀ E ∈ Set.Icc c d, lyap α lam (E:ℂ) = 0) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ Q : ℕ, ∀ (p : ℤ) (q : ℕ), Q ≤ q →
        |α - (p:ℝ)/(q:ℝ)| < δ/(q:ℝ) → Nat.Coprime p.natAbs q →
        ∀ a b : ℝ, c ≤ a → a < b → b ≤ d →
          (∀ E ∈ Set.Ioo a b, ∀ θ : ℝ, 2 < ‖trAq p q lam (E:ℂ) θ‖) →
          a ∈ ratSpec p q lam → b ∈ ratSpec p q lam →
          Real.exp (-(ε * (q:ℝ))) * lam ^ ((q:ℝ)/2) ≤ b - a) :
    RatGapBound := by
  intro hLE hBJ α lam c d hα hlam hlam1 hcd hsub ε hε
  obtain ⟨δg, hδg, Qg, hg'⟩ :=
    hg α lam c d hα hlam hlam1 hcd (ratGapBound_lyap_zero hBJ hα hlam hlam1 hsub) ε hε
  obtain ⟨ρ, hρ, hρ'⟩ := ratDenomLarge α hα Qg
  refine ⟨min δg ρ, lt_min hδg hρ, max Qg 1, ?_⟩
  intro p q hQ hαp a b hca hab hbd hfree haspec hbspec
  have hq1 : 1 ≤ q := le_trans (le_max_right _ _) hQ
  have hQq : Qg ≤ q := le_trans (le_max_left _ _) hQ
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq1
  obtain ⟨p', q', hq'1, hcop, hq'e, hfreq⟩ := exists_coprime_reduce p q hq1
  set g : ℕ := Nat.gcd p.natAbs q with hgdef
  have hq'val : q' = q / g := by
    have h := hq'e
    rw [hgdef] at h
    exact_mod_cast h
  have hqq' : q = g * q' := by
    rw [hq'val, hgdef]
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right p.natAbs q)).symm
  have hfreq' : (p':ℝ)/(q':ℝ) = (p:ℝ)/(q:ℝ) := hfreq
  have hq'le : q' ≤ q := by
    rw [hq'val]
    exact Nat.div_le_self q g
  have hq'leR : (q':ℝ) ≤ (q:ℝ) := by exact_mod_cast hq'le
  have hq'posR : (0:ℝ) < (q':ℝ) := by exact_mod_cast hq'1
  have hgpos : 0 < g := by rw [hgdef]; exact Nat.gcd_pos_of_pos_right _ (by omega)
  -- the `q`-step transfer matrix is the `g`-th power of the `q'`-step one
  have hk : (q':ℝ) * ((p':ℝ)/(q':ℝ)) = (p':ℝ) := by field_simp
  have htrace : ∀ (E θ : ℝ), ‖trAq p q lam (E:ℂ) θ‖
      = |((Work.TMComp.RotBasics.iterR ((p':ℝ)/(q':ℝ)) lam E q' θ) ^ g).trace| := by
    intro E θ
    rw [trAq_norm_eq_iterR_trace p q lam E θ, ← hfreq', hqq',
      iterR_mul_pow ((p':ℝ)/(q':ℝ)) lam E q' g p' hk θ]
  have hdet' : ∀ (E θ : ℝ),
      (Work.TMComp.RotBasics.iterR ((p':ℝ)/(q':ℝ)) lam E q' θ).det = 1 :=
    fun E θ => iterR_det ((p':ℝ)/(q':ℝ)) lam E q' θ
  -- the easy Chebyshev direction
  have htrEasy : ∀ (E θ : ℝ), ‖trAq p' q' lam (E:ℂ) θ‖ ≤ 2 → ‖trAq p q lam (E:ℂ) θ‖ ≤ 2 := by
    intro E θ h
    rw [trAq_norm_eq_iterR_trace p' q' lam E θ] at h
    rw [htrace E θ]
    exact sl2TracePowEasy g _ (hdet' E θ) h
  -- the hard direction
  have htrHard : ∀ (E θ : ℝ), ‖trAq p q lam (E:ℂ) θ‖ ≤ 2 → ‖trAq p' q' lam (E:ℂ) θ‖ ≤ 2 := by
    intro E θ h
    rw [htrace E θ] at h
    rw [trAq_norm_eq_iterR_trace p' q' lam E θ]
    exact sl2_trace_pow_reduce g hgpos _ (hdet' E θ) h
  have hfree' : ∀ E ∈ Set.Ioo a b, ∀ θ : ℝ, 2 < ‖trAq p' q' lam (E:ℂ) θ‖ := by
    intro E hE θ
    by_contra hcon
    simp only [not_lt] at hcon
    exact absurd (hfree E hE θ) (not_lt.mpr (htrEasy E θ hcon))
  have haspec' : a ∈ ratSpec p' q' lam := by
    obtain ⟨θ, hθ⟩ := haspec
    exact ⟨θ, htrHard a θ hθ⟩
  have hbspec' : b ∈ ratSpec p' q' lam := by
    obtain ⟨θ, hθ⟩ := hbspec
    exact ⟨θ, htrHard b θ hθ⟩
  -- the reduced denominator of a good approximant is large
  have hQ' : Qg ≤ q' := by
    by_contra hcon
    simp only [not_le] at hcon
    have h1 := hρ' p' q' (by omega) hcon
    have h2 : |α - (p':ℝ)/(q':ℝ)| < ρ := by
      rw [hfreq']
      have h3 : (min δg ρ) / (q:ℝ) ≤ min δg ρ := by
        rw [div_le_iff₀ hqpos]
        have hq1R : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
        nlinarith [le_of_lt (lt_min hδg hρ)]
      exact lt_of_lt_of_le (lt_of_lt_of_le hαp h3) (min_le_right δg ρ)
    linarith
  have hsfreq : |α - (p':ℝ)/(q':ℝ)| < δg / (q':ℝ) := by
    rw [hfreq']
    have h4 : δg / (q:ℝ) ≤ δg / (q':ℝ) := by
      have h : (1:ℝ) / (q:ℝ) ≤ 1 / (q':ℝ) := one_div_le_one_div_of_le hq'posR hq'leR
      calc δg / (q:ℝ) = δg * (1 / (q:ℝ)) := by rw [mul_one_div]
        _ ≤ δg * (1 / (q':ℝ)) := mul_le_mul_of_nonneg_left h (le_of_lt hδg)
        _ = δg / (q':ℝ) := by rw [mul_one_div]
    have h5 : (min δg ρ) / (q:ℝ) ≤ δg / (q:ℝ) :=
      div_le_div_of_nonneg_right (min_le_left δg ρ) (le_of_lt hqpos)
    linarith [hαp, h5, h4]
  have hb := hg' p' q' hQ' hsfreq hcop a b hca hab hbd hfree' haspec' hbspec'
  refine le_trans ?_ hb
  refine mul_le_mul ?_ ?_ ?_ ?_
  · apply Real.exp_le_exp.mpr
    nlinarith [hε, hq'leR]
  · exact ratGapBound_rpow_le hlam hlam1 (by linarith [hq'leR])
  · exact Real.rpow_nonneg (le_of_lt hlam) _
  · exact Real.exp_nonneg _


/-! ## 10. The final assembly -/

/-- `RatGapBound` from the coprime case and the two remaining even-`q` inputs. -/
theorem ratGapBound_of_all
    (hZ : ∀ (p : ℤ) (q m : ℕ), q = 2*m+2 → Nat.Coprime p.natAbs q → ∀ lam : ℝ, 0 < lam →
      ‖(disc p q lam).eval (0:ℂ)‖ = 2 + 2*lam^q)
    (hI : ∀ (p : ℤ) (q m : ℕ), q = 2*m+2 → Nat.Coprime p.natAbs q → ∀ lam : ℝ, 0 < lam →
      lam ≤ 1 → ‖(disc p q lam).eval (0:ℂ)‖ = 2 + 2*lam^q →
      ∃ δ : ℝ, 0 < δ ∧ ∀ E : ℝ, |E| < δ → ‖(disc p q lam).eval (E:ℂ)‖ ≤ 2 + 2*lam^q) :
    RatGapBound := by
  intro hLE hBJ
  exact ratGapBound_of_coprime (ratGapBound_coprime_of hLE hZ hI ceyEvenDiscDeriv) hLE hBJ


/-- **`RatGapBound`** (AJ Theorem 7.2, ROUTE_LEAD C14 items 14e + 14f + 14g): for `α`
irrational, `0 < λ ≤ 1`, a window `[c,d] ⊆ Σ_α` and `ε > 0`, every gap of the union spectrum
`ratSpec p q lam` of a sufficiently good rational approximant `p/q` of `α` that lies inside
`[c,d]` has length at least `e^{-εq}λ^{q/2}`. -/
theorem ratGapBound : Work.TMC14Core.RatGapBound :=
  ratGapBound_of_all discZeroAbsEven evenZeroInterior

end Work.TMC14Core
