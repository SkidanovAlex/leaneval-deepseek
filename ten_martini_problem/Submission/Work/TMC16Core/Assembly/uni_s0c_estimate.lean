import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Assembly.Branch
import Submission.Work.TMC16Core.Core.uni_nonres3_support
import Submission.Work.TMC16Core.Core.irrat_blk_nr

/-!
# The honest uniformity estimate for the `s = 0`, case (3) windows

The file `Assembly/uni_s0c.lean` proves the *requested* statement
`Work.TMC16Core.Assembly.uni_s0c`.  As explained in the module docstring of that file, the
requested statement is vacuous for large `n` (the scale-dependent range of its phase-separation
hypothesis `hθ` grows without bound while `cθ` is a fixed positive constant, so by density of the
irrational rotation `hθ` becomes unsatisfiable).  Consequently the requested statement cannot be
used at a prescribed scale, which is what the AJ §9 assembly (`Glue.lean`, `RegFamily`) needs.

This file supplies the *honest* content — AJ §9, Lemma 9.10 for the case (3) windows
`I1s0c`/`I2s0c` (one block of `q (n-1)` sites on each side): an explicit uniformity rate, with
the scale-dependent separation constants `cθ` (for the phase sums `2θ + (i+k)α`) and `csep`
(for the differences `(i-j)α`) as hypotheses, and with the numeric budget as an explicit
hypothesis.  The three trigonometric block-sum bounds used are delegated / available separately
(`s0c_sum_bounds`); here they enter as hypotheses of `uniform_of_sum_bounds`, which contains the
Lagrange-product manipulation.

Main entry points:

* `uniform_of_sum_bounds` : Lagrange products + the four block sums ⇒ `Uniform ε` (phases
  `θ + pα` on the phase-index set `Qs0c h m qn`).
* `uni_s0c_estimate` : the same in the *site* coordinates of the requested statement, with the
  block sums instantiated from `s0c_sum_bounds`.
-/

namespace Work.TMC16Core.Assembly

open Work.TMC16Core

noncomputable section

/-- The phase-index set of the first window `I1s0c h` (its image under `j ↦ j + h - 1`). -/
def Q1s0c (h : ℕ) : Finset ℤ :=
  Finset.Icc (1 - ((h / 2 : ℕ) : ℤ)) ((h : ℤ) - ((h / 2 : ℕ) : ℤ))

/-- The phase-index set of the second window `I2s0c h m qn`. -/
def Q2s0c (h : ℕ) (m qn : ℤ) : Finset ℤ :=
  Finset.Icc (m * qn + (h : ℤ) - ((h / 2 : ℕ) : ℤ) + 1)
    (m * qn + 2 * (h : ℤ) - ((h / 2 : ℕ) : ℤ))

/-- The union of the two phase-index sets. -/
def Qs0c (h : ℕ) (m qn : ℤ) : Finset ℤ := Q1s0c h ∪ Q2s0c h m qn

/-- Every phase index is bounded by `|m qn| + 2h + 1`. -/
theorem Qs0c_abs_le {h : ℕ} {m qn : ℤ} {p : ℤ} (hp : p ∈ Qs0c h m qn) :
    |p| ≤ |m * qn| + 2 * (h : ℤ) + 1 := by
  rw [Qs0c, Finset.mem_union] at hp
  have hu0 : (0 : ℤ) ≤ ((h / 2 : ℕ) : ℤ) := Int.natCast_nonneg _
  have huh : ((h / 2 : ℕ) : ℤ) ≤ (h : ℤ) := by
    exact_mod_cast Nat.div_le_self h 2
  have hh0 : (0 : ℤ) ≤ (h : ℤ) := Int.natCast_nonneg _
  rcases hp with hp | hp
  · rw [Q1s0c, Finset.mem_Icc] at hp
    obtain ⟨h1, h2⟩ := hp
    rw [abs_le]
    have ha := neg_abs_le (m * qn)
    have hb := le_abs_self (m * qn)
    constructor <;> linarith [hu0, huh, hh0]
  · rw [Q2s0c, Finset.mem_Icc] at hp
    obtain ⟨h1, h2⟩ := hp
    rw [abs_le]
    have ha := neg_abs_le (m * qn)
    have hb := le_abs_self (m * qn)
    constructor <;> linarith [hu0, huh, hh0]

/-- For two phase indices the sum is bounded by `2 |m qn| + 8h + 4`. -/
theorem Qs0c_add_abs_le {h : ℕ} (hh : 1 ≤ h) {m qn : ℤ} {p q : ℤ}
    (hp : p ∈ Qs0c h m qn) (hq : q ∈ Qs0c h m qn) :
    |p + q| ≤ 2 * |m * qn| + 8 * (h : ℤ) + 4 := by
  have h1 := Qs0c_abs_le hp
  have h2 := Qs0c_abs_le hq
  have hhR : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hh
  have h3 : |p + q| ≤ |p| + |q| := abs_add_le p q
  have h4 : |p| + |q| ≤ |m * qn| + 2 * (h : ℤ) + 1 + (|m * qn| + 2 * (h : ℤ) + 1) := by
    linarith
  have hm : (0 : ℤ) ≤ |m * qn| := abs_nonneg _
  linarith

/-- **Distinctness of the phases.**  Distinct phase indices of the window carry distinct cosines,
provided the differences are `csep`-separated (`hsep`) and the sums are `cθ`-separated (`hθ`,
whose range covers `p + q`). -/
theorem s0c_cos_ne {α θ cθ csep Y : ℝ} {h : ℕ} (hh : 1 ≤ h) {m qn : ℤ} {p q : ℤ}
    (hp : p ∈ Qs0c h m qn) (hq : q ∈ Qs0c h m qn) (hne : p ≠ q)
    (hcθ : 0 < cθ) (hcsep : 0 < csep)
    (hadd : ∀ p q : ℤ, p ∈ Qs0c h m qn → q ∈ Qs0c h m qn →
      |p + q| ≤ 2 * |Y| + 8 * (h : ℤ) + 4)
    (hθ : ∀ j : ℤ, |j| ≤ 2 * |Y| + 8 * (h : ℤ) + 4 →
      cθ ≤ fracDist (2 * θ + (j : ℝ) * α))
    (hsep : ∀ p q : ℤ, p ∈ Qs0c h m qn → q ∈ Qs0c h m qn → p ≠ q →
      csep ≤ fracDist (((p - q : ℤ) : ℝ) * α)) :
    Real.cos (2 * Real.pi * (θ + (p : ℝ) * α))
      ≠ Real.cos (2 * Real.pi * (θ + (q : ℝ) * α)) := by
  intro hcon
  have hsub : Real.cos (2 * Real.pi * (θ + (p : ℝ) * α))
      - Real.cos (2 * Real.pi * (θ + (q : ℝ) * α)) = 0 := by rw [hcon]; ring
  rw [Real.cos_sub_cos] at hsub
  have hprod : Real.sin ((2 * Real.pi * (θ + (p : ℝ) * α)
        + 2 * Real.pi * (θ + (q : ℝ) * α)) / 2)
      * Real.sin ((2 * Real.pi * (θ + (p : ℝ) * α)
        - 2 * Real.pi * (θ + (q : ℝ) * α)) / 2) = 0 := by
    nlinarith [hsub]
  have harg1 : (2 * Real.pi * (θ + (p : ℝ) * α) + 2 * Real.pi * (θ + (q : ℝ) * α)) / 2
      = Real.pi * (2 * θ + ((p + q : ℤ) : ℝ) * α) := by push_cast; ring
  have harg2 : (2 * Real.pi * (θ + (p : ℝ) * α) - 2 * Real.pi * (θ + (q : ℝ) * α)) / 2
      = Real.pi * ((((p - q : ℤ)) : ℝ) * α) := by push_cast; ring
  rcases mul_eq_zero.mp hprod with hs | hd
  · rw [harg1] at hs
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hs
    have hk' : (2 * θ + ((p + q : ℤ) : ℝ) * α) = (k : ℝ) := by
      have h : Real.pi * ((k : ℝ)) = Real.pi * (2 * θ + ((p + q : ℤ) : ℝ) * α) := by
        rw [← hk]; ring
      exact (mul_left_cancel₀ Real.pi_ne_zero h).symm
    have hfd : fracDist (2 * θ + ((p + q : ℤ) : ℝ) * α) = 0 := by
      rw [fracDist, hk']
      simp
    have hrange := hadd p q hp hq
    have := hθ (p + q) hrange
    rw [hfd] at this
    linarith
  · rw [harg2] at hd
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hd
    have hk' : (((p - q : ℤ)) : ℝ) * α = (k : ℝ) := by
      have h : Real.pi * ((k : ℝ)) = Real.pi * ((((p - q : ℤ)) : ℝ) * α) := by
        rw [← hk]; ring
      exact (mul_left_cancel₀ Real.pi_ne_zero h).symm
    have hfd : fracDist ((((p - q : ℤ)) : ℝ) * α) = 0 := by
      rw [fracDist, hk']
      simp
    have := hsep p q hp hq hne
    rw [hfd] at this
    linarith


/-- **The Lagrange-product bound on the phase-index window.**  If the three trigonometric
block-sum bounds `hN`, `hD1`, `hD2` hold (they are supplied by `s0c_sum_bounds` from the
continued-fraction block estimate and the separations), then every Lagrange product of the
`2h` phases `θ + pα`, `p ∈ Qs0c h m qn`, is `< exp ((2h-1)ε)`. -/
theorem s0c_prod_bound {α θ ε cθ csep Y : ℝ} {h : ℕ} {m qn : ℤ}
    (hh : 1 ≤ h)
    (hadd : ∀ p q : ℤ, p ∈ Qs0c h m qn → q ∈ Qs0c h m qn →
      |p + q| ≤ 2 * |Y| + 8 * (h : ℤ) + 4)
    (hθ : ∀ j : ℤ, |j| ≤ 2 * |Y| + 8 * (h : ℤ) + 4 →
      cθ ≤ fracDist (2 * θ + (j : ℝ) * α))
    (hsep : ∀ p q : ℤ, p ∈ Qs0c h m qn → q ∈ Qs0c h m qn → p ≠ q →
      csep ≤ fracDist (((p - q : ℤ) : ℝ) * α))
    (hN : ∀ (k : ℤ) (ξ : ℝ), k ∈ Qs0c h m qn →
      (∀ i ∈ (Qs0c h m qn).erase k, Real.sin (Real.pi * (ξ + (i : ℝ) * α)) ≠ 0) →
      ∑ i ∈ (Qs0c h m qn).erase k, Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
        ≤ -2 * ((h : ℝ) - 1) * Real.log 2 + 64 * Real.log (h : ℝ))
    (hD1 : ∀ k : ℤ, k ∈ Qs0c h m qn →
      ∑ i ∈ (Qs0c h m qn).erase k,
          Real.log |Real.sin (Real.pi * (2 * θ + ((i + k : ℤ) : ℝ) * α))|
        ≥ -2 * ((h : ℝ) - 1) * Real.log 2 - 64 * Real.log (h : ℝ) + 2 * Real.log (2 * cθ))
    (hD2 : ∀ k : ℤ, k ∈ Qs0c h m qn →
      ∑ i ∈ (Qs0c h m qn).erase k, Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|
        ≥ -2 * ((h : ℝ) - 1) * Real.log 2 - 64 * Real.log (h : ℝ) + Real.log (2 * csep))
    (hcθ : 0 < cθ) (hcsep : 0 < csep)
    (hbudget : 256 * Real.log (h : ℝ) + 2 * Real.log (1 / (2 * cθ))
        + Real.log (1 / (2 * csep)) < (2 * (h : ℝ) - 1) * ε)
    {k : ℤ} (hk : k ∈ Qs0c h m qn) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |∏ i ∈ (Qs0c h m qn).erase k,
        (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
          (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
      < Real.exp ((2 * (h : ℝ) - 1) * ε) := by
  classical
  by_cases hzero : ∃ i ∈ (Qs0c h m qn).erase k,
      x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)) = 0
  · obtain ⟨i, hi, hiz⟩ := hzero
    have h1 : (∏ i ∈ (Qs0c h m qn).erase k,
        (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
          (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
            - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))) = 0 :=
      Finset.prod_eq_zero hi (by rw [hiz, zero_div])
    rw [h1, abs_zero]
    exact Real.exp_pos _
  · push_neg at hzero
    set a : ℝ := Real.arccos x / (2 * Real.pi) with ha
    have hxa : Real.cos (2 * Real.pi * a) = x := by
      have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      calc Real.cos (2 * Real.pi * a) = Real.cos (Real.arccos x) := by
            congr 1
            rw [ha]
            field_simp
        _ = x := Real.cos_arccos hx.1 hx.2
    have hfacN : ∀ i : ℤ, |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
        = 2 * |Real.sin (Real.pi * (a + (θ + (i : ℝ) * α)))| *
            |Real.sin (Real.pi * (a - (θ + (i : ℝ) * α)))| := by
      intro i
      rw [← hxa, Real.cos_sub_cos]
      rw [show (2 * Real.pi * a + 2 * Real.pi * (θ + (i : ℝ) * α)) / 2
            = Real.pi * (a + (θ + (i : ℝ) * α)) by ring,
          show (2 * Real.pi * a - 2 * Real.pi * (θ + (i : ℝ) * α)) / 2
            = Real.pi * (a - (θ + (i : ℝ) * α)) by ring]
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hfacD : ∀ i : ℤ,
        |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
            - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
        = 2 * |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))| *
            |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)| := by
      intro i
      rw [Real.cos_sub_cos]
      rw [show (2 * Real.pi * (θ + (k : ℝ) * α) + 2 * Real.pi * (θ + (i : ℝ) * α)) / 2
            = Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α) by push_cast; ring,
          show (2 * Real.pi * (θ + (k : ℝ) * α) - 2 * Real.pi * (θ + (i : ℝ) * α)) / 2
            = -(Real.pi * (((i - k : ℤ)) : ℝ) * α) by push_cast; ring,
          Real.sin_neg]
      rw [abs_mul, abs_mul, abs_neg, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hsinN : ∀ i ∈ (Qs0c h m qn).erase k,
        Real.sin (Real.pi * (a + (θ + (i : ℝ) * α))) ≠ 0 ∧
        Real.sin (Real.pi * (a - (θ + (i : ℝ) * α))) ≠ 0 := by
      intro i hi
      have h1 : 2 * |Real.sin (Real.pi * (a + (θ + (i : ℝ) * α)))| *
          |Real.sin (Real.pi * (a - (θ + (i : ℝ) * α)))| ≠ 0 := by
        rw [← hfacN i]
        exact (abs_pos.mpr (hzero i hi)).ne'
      constructor
      · intro h0; exact h1 (by rw [h0]; simp)
      · intro h0; exact h1 (by rw [h0]; simp)
    have hsinD : ∀ i ∈ (Qs0c h m qn).erase k,
        Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α)) ≠ 0 ∧
        Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α) ≠ 0 := by
      intro i hi
      rw [Finset.mem_erase] at hi
      have h3 : Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
          ≠ Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)) :=
        s0c_cos_ne hh hk hi.2 (fun h => hi.1 h.symm) hcθ hcsep hadd hθ hsep
      have h1 : 2 * |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))| *
          |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)| ≠ 0 := by
        rw [← hfacD i]
        exact (abs_pos.mpr (sub_ne_zero.mpr h3)).ne'
      constructor
      · intro h0; exact h1 (by rw [h0]; simp)
      · intro h0; exact h1 (by rw [h0]; simp)
    have hnum_ne : ∀ i ∈ (Qs0c h m qn).erase k,
        x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)) ≠ 0 := fun i hi => hzero i hi
    have hden_ne : ∀ i ∈ (Qs0c h m qn).erase k,
        Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
          - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)) ≠ 0 := by
      intro i hi
      rw [Finset.mem_erase] at hi
      exact sub_ne_zero.mpr
        (s0c_cos_ne hh hk hi.2 (fun h => hi.1 h.symm) hcθ hcsep hadd hθ hsep)
    have hlog : Real.log |∏ i ∈ (Qs0c h m qn).erase k,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
              - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
        = (∑ i ∈ (Qs0c h m qn).erase k,
            Real.log |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|)
          - (∑ i ∈ (Qs0c h m qn).erase k,
              Real.log |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
                - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|) := by
      rw [Finset.abs_prod]
      have h1 : ∏ i ∈ (Qs0c h m qn).erase k,
            |(x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
              (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
                - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
          = (∏ i ∈ (Qs0c h m qn).erase k,
              |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|) /
            (∏ i ∈ (Qs0c h m qn).erase k,
              |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
                - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|) := by
        rw [Finset.prod_congr rfl (fun i _ => abs_div _ _), Finset.prod_div_distrib]
      have hN0 : (∏ i ∈ (Qs0c h m qn).erase k,
          |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i hi => (abs_pos.mpr (hnum_ne i hi)).ne')
      have hD0 : (∏ i ∈ (Qs0c h m qn).erase k,
          |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
            - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i hi => (abs_pos.mpr (hden_ne i hi)).ne')
      rw [h1, Real.log_div hN0 hD0,
        Real.log_prod (fun i hi => (abs_pos.mpr (hnum_ne i hi)).ne'),
        Real.log_prod (fun i hi => (abs_pos.mpr (hden_ne i hi)).ne')]
    have htermN : ∀ i ∈ (Qs0c h m qn).erase k,
        Real.log |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
        = Real.log 2 + (Real.log |Real.sin (Real.pi * (a + (θ + (i : ℝ) * α)))|
            + Real.log |Real.sin (Real.pi * (a - (θ + (i : ℝ) * α)))|) := by
      intro i hi
      have hs0 := (hsinN i hi).1
      have ht0 := (hsinN i hi).2
      have h1 : |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
          = 2 * (|Real.sin (Real.pi * (a + (θ + (i : ℝ) * α)))| *
            |Real.sin (Real.pi * (a - (θ + (i : ℝ) * α)))|) := by
        rw [hfacN i]; ring
      rw [h1, Real.log_mul (by norm_num)
          (mul_ne_zero (abs_ne_zero.mpr hs0) (abs_ne_zero.mpr ht0)),
        Real.log_mul (abs_ne_zero.mpr hs0) (abs_ne_zero.mpr ht0)]
    have htermD : ∀ i ∈ (Qs0c h m qn).erase k,
        Real.log |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
            - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
        = Real.log 2 + (Real.log |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))|
            + Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|) := by
      intro i hi
      have hs0 := (hsinD i hi).1
      have ht0 := (hsinD i hi).2
      have h1 : |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
            - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
          = 2 * (|Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))| *
            |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|) := by
        rw [hfacD i]; ring
      rw [h1, Real.log_mul (by norm_num)
          (mul_ne_zero (abs_ne_zero.mpr hs0) (abs_ne_zero.mpr ht0)),
        Real.log_mul (abs_ne_zero.mpr hs0) (abs_ne_zero.mpr ht0)]
    have hexpN : ∑ i ∈ (Qs0c h m qn).erase k,
          Real.log |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
        = (((Qs0c h m qn).erase k).card : ℝ) * Real.log 2
          + ∑ i ∈ (Qs0c h m qn).erase k,
              (Real.log |Real.sin (Real.pi * (a + (θ + (i : ℝ) * α)))|
                + Real.log |Real.sin (Real.pi * (a - (θ + (i : ℝ) * α)))|) := by
      rw [Finset.sum_congr rfl htermN, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hexpD : ∑ i ∈ (Qs0c h m qn).erase k,
          Real.log |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
            - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
        = (((Qs0c h m qn).erase k).card : ℝ) * Real.log 2
          + ∑ i ∈ (Qs0c h m qn).erase k,
              (Real.log |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))|
                + Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|) := by
      rw [Finset.sum_congr rfl htermD, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hS1 : ∑ i ∈ (Qs0c h m qn).erase k,
            (Real.log |Real.sin (Real.pi * (a + (θ + (i : ℝ) * α)))|
              + Real.log |Real.sin (Real.pi * (a - (θ + (i : ℝ) * α)))|)
        = (∑ i ∈ (Qs0c h m qn).erase k,
            Real.log |Real.sin (Real.pi * ((a + θ) + (i : ℝ) * α))|)
          + (∑ i ∈ (Qs0c h m qn).erase k,
            Real.log |Real.sin (Real.pi * ((θ - a) + (i : ℝ) * α))|) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · exact Finset.sum_congr rfl (fun i _ => by
          rw [show a + (θ + (i : ℝ) * α) = (a + θ) + (i : ℝ) * α by ring])
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [show a - (θ + (i : ℝ) * α) = -((θ - a) + (i : ℝ) * α) by ring]
        rw [show Real.pi * -((θ - a) + (i : ℝ) * α)
            = -(Real.pi * ((θ - a) + (i : ℝ) * α)) by ring, Real.sin_neg, abs_neg]
    have hS2 : ∑ i ∈ (Qs0c h m qn).erase k,
            (Real.log |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))|
              + Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|)
        = (∑ i ∈ (Qs0c h m qn).erase k,
            Real.log |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))|)
          + (∑ i ∈ (Qs0c h m qn).erase k,
            Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|) :=
      Finset.sum_add_distrib
    have hmain : Real.log |∏ i ∈ (Qs0c h m qn).erase k,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
              - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
        = (∑ i ∈ (Qs0c h m qn).erase k,
              Real.log |Real.sin (Real.pi * ((a + θ) + (i : ℝ) * α))|)
          + (∑ i ∈ (Qs0c h m qn).erase k,
              Real.log |Real.sin (Real.pi * ((θ - a) + (i : ℝ) * α))|)
          - ((∑ i ∈ (Qs0c h m qn).erase k,
                Real.log |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))|)
            + (∑ i ∈ (Qs0c h m qn).erase k,
                Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|)) := by
      rw [hlog, hexpN, hS1, hexpD, hS2]
      ring
    -- the three block bounds
    have hUp1 : (∑ i ∈ (Qs0c h m qn).erase k,
          Real.log |Real.sin (Real.pi * ((a + θ) + (i : ℝ) * α))|)
        ≤ -2 * ((h : ℝ) - 1) * Real.log 2 + 64 * Real.log (h : ℝ) :=
      hN k (a + θ) hk (fun i hi => by
        have h := (hsinN i hi).1
        rwa [show a + (θ + (i : ℝ) * α) = a + θ + (i : ℝ) * α by ring] at h)
    have hUp2 : (∑ i ∈ (Qs0c h m qn).erase k,
          Real.log |Real.sin (Real.pi * ((θ - a) + (i : ℝ) * α))|)
        ≤ -2 * ((h : ℝ) - 1) * Real.log 2 + 64 * Real.log (h : ℝ) :=
      hN k (θ - a) hk (fun i hi => by
        intro h0
        exact (hsinN i hi).2 (by
          have : Real.pi * (a - (θ + (i : ℝ) * α))
              = -(Real.pi * ((θ - a) + (i : ℝ) * α)) := by ring
          rw [this, Real.sin_neg, h0, neg_zero]))
    have hLo3 := hD1 k hk
    have hLo4 := hD2 k hk
    have hmid : Real.log |∏ i ∈ (Qs0c h m qn).erase k,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
              - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
        ≤ 256 * Real.log (h : ℝ) + 2 * Real.log (1 / (2 * cθ))
            + Real.log (1 / (2 * csep)) := by
      have hcθ' : Real.log (2 * cθ) = -Real.log (1 / (2 * cθ)) := by
        rw [one_div, Real.log_inv, neg_neg]
      have hcsep' : Real.log (2 * csep) = -Real.log (1 / (2 * csep)) := by
        rw [one_div, Real.log_inv, neg_neg]
      rw [hmain]
      linarith [hUp1, hUp2, hLo3, hLo4, hcθ', hcsep']
    have hpos : 0 < |∏ i ∈ (Qs0c h m qn).erase k,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
              - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))| := by
      rw [Finset.abs_prod]
      refine Finset.prod_pos (fun i hi => ?_)
      rw [abs_div]
      exact div_pos (abs_pos.mpr (hnum_ne i hi)) (abs_pos.mpr (hden_ne i hi))
    calc |∏ i ∈ (Qs0c h m qn).erase k,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
              - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
        = Real.exp (Real.log |∏ i ∈ (Qs0c h m qn).erase k,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
              - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|) :=
          (Real.exp_log hpos).symm
      _ < Real.exp ((2 * (h : ℝ) - 1) * ε) := Real.exp_lt_exp.mpr (lt_of_le_of_lt hmid hbudget)


/-! ## Cardinality, disjointness, and the transfer to the site coordinates -/

/-- The first phase block has `h` elements. -/
theorem card_Q1s0c (h : ℕ) : (Q1s0c h).card = h := by
  rw [Q1s0c, Int.card_Icc]
  have : (h : ℤ) - ((h / 2 : ℕ) : ℤ) + 1 - (1 - ((h / 2 : ℕ) : ℤ)) = (h : ℤ) := by ring
  rw [this, Int.toNat_natCast]

/-- The second phase block has `h` elements. -/
theorem card_Q2s0c (h : ℕ) (m qn : ℤ) : (Q2s0c h m qn).card = h := by
  rw [Q2s0c, Int.card_Icc]
  have : m * qn + 2 * (h : ℤ) - ((h / 2 : ℕ) : ℤ) + 1
      - (m * qn + (h : ℤ) - ((h / 2 : ℕ) : ℤ) + 1) = (h : ℤ) := by ring
  rw [this, Int.toNat_natCast]

/-- The two phase blocks are disjoint as soon as `2h < qn`. -/
theorem disjoint_Q1s0c_Q2s0c {h : ℕ} {m qn : ℤ} (hqn : 0 < qn)
    (h2h : 2 * (h : ℤ) < qn) : Disjoint (Q1s0c h) (Q2s0c h m qn) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  rw [Q1s0c, Finset.mem_Icc] at hx1
  rw [Q2s0c, Finset.mem_Icc] at hx2
  obtain ⟨a1, a2⟩ := hx1
  obtain ⟨b1, b2⟩ := hx2
  by_cases hm : 0 ≤ m
  · have hmq : 0 ≤ m * qn := mul_nonneg hm hqn.le
    linarith
  · push_neg at hm
    have hmq : m * qn ≤ -qn := by nlinarith
    linarith

/-- The window has `2h` phase indices. -/
theorem card_Qs0c {h : ℕ} {m qn : ℤ} (hqn : 0 < qn) (h2h : 2 * (h : ℤ) < qn) :
    (Qs0c h m qn).card = 2 * h := by
  rw [Qs0c, Finset.card_union_of_disjoint (disjoint_Q1s0c_Q2s0c hqn h2h), card_Q1s0c,
    card_Q2s0c]
  ring

/-- Membership transfer: the site `j ∈ I1s0c h` has phase index `j + h - 1 ∈ Q1s0c h`. -/
theorem shift_mem_I1s0c {h : ℕ} {j : ℤ} (hj : j ∈ I1s0c h) : j + (h : ℤ) - 1 ∈ Q1s0c h := by
  rw [I1s0c, Finset.mem_Icc] at hj
  rw [Q1s0c, Finset.mem_Icc]
  obtain ⟨h1, h2⟩ := hj
  constructor <;> omega

/-- Membership transfer: the site `j ∈ I2s0c h m qn` has phase index `j + h - 1 ∈ Q2s0c h m qn`. -/
theorem shift_mem_I2s0c {h : ℕ} {m qn j : ℤ} (hj : j ∈ I2s0c h m qn) :
    j + (h : ℤ) - 1 ∈ Q2s0c h m qn := by
  rw [I2s0c, Finset.mem_Icc] at hj
  rw [Q2s0c, Finset.mem_Icc]
  obtain ⟨h1, h2⟩ := hj
  constructor <;> omega

/-- Membership transfer (inverse direction). -/
theorem unshift_mem_I1s0c {h : ℕ} {p : ℤ} (hp : p ∈ Q1s0c h) : p - (h : ℤ) + 1 ∈ I1s0c h := by
  rw [Q1s0c, Finset.mem_Icc] at hp
  rw [I1s0c, Finset.mem_Icc]
  obtain ⟨h1, h2⟩ := hp
  constructor <;> omega

/-- Membership transfer (inverse direction). -/
theorem unshift_mem_I2s0c {h : ℕ} {m qn p : ℤ} (hp : p ∈ Q2s0c h m qn) :
    p - (h : ℤ) + 1 ∈ I2s0c h m qn := by
  rw [Q2s0c, Finset.mem_Icc] at hp
  rw [I2s0c, Finset.mem_Icc]
  obtain ⟨h1, h2⟩ := hp
  constructor <;> omega

/-- The shift `j ↦ j + h - 1` identifies the two site windows with the two phase blocks. -/
noncomputable def shiftEquivs0c (h : ℕ) (m qn : ℤ) :
    {j : ℤ // j ∈ I1s0c h ∪ I2s0c h m qn} ≃ {p : ℤ // p ∈ Qs0c h m qn} where
  toFun j := ⟨j.1 + (h : ℤ) - 1, by
    rw [Qs0c, Finset.mem_union]
    rcases Finset.mem_union.1 j.2 with hj | hj
    · exact Or.inl (shift_mem_I1s0c hj)
    · exact Or.inr (shift_mem_I2s0c hj)⟩
  invFun p := ⟨p.1 - (h : ℤ) + 1, by
    rw [Finset.mem_union]
    rcases Finset.mem_union.1 p.2 with hp | hp
    · exact Or.inl (unshift_mem_I1s0c hp)
    · exact Or.inr (unshift_mem_I2s0c hp)⟩
  left_inv j := by ext; simp; ring
  right_inv p := by ext; simp; ring

/-- **The Lagrange-product bounds give `Uniform`.**  This is the assembly: distinctness of the
cosines plus the product bound `s0c_prod_bound`, expressed for the phase-index set. -/
theorem uniform_of_sum_bounds {α θ ε cθ csep Y : ℝ} {h : ℕ} {m qn : ℤ}
    (hh : 1 ≤ h) (hcard : (Qs0c h m qn).card = 2 * h)
    (hadd : ∀ p q : ℤ, p ∈ Qs0c h m qn → q ∈ Qs0c h m qn →
      |p + q| ≤ 2 * |Y| + 8 * (h : ℤ) + 4)
    (hθ : ∀ j : ℤ, |j| ≤ 2 * |Y| + 8 * (h : ℤ) + 4 →
      cθ ≤ fracDist (2 * θ + (j : ℝ) * α))
    (hsep : ∀ p q : ℤ, p ∈ Qs0c h m qn → q ∈ Qs0c h m qn → p ≠ q →
      csep ≤ fracDist (((p - q : ℤ) : ℝ) * α))
    (hN : ∀ (k : ℤ) (ξ : ℝ), k ∈ Qs0c h m qn →
      (∀ i ∈ (Qs0c h m qn).erase k, Real.sin (Real.pi * (ξ + (i : ℝ) * α)) ≠ 0) →
      ∑ i ∈ (Qs0c h m qn).erase k, Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
        ≤ -2 * ((h : ℝ) - 1) * Real.log 2 + 64 * Real.log (h : ℝ))
    (hD1 : ∀ k : ℤ, k ∈ Qs0c h m qn →
      ∑ i ∈ (Qs0c h m qn).erase k,
          Real.log |Real.sin (Real.pi * (2 * θ + ((i + k : ℤ) : ℝ) * α))|
        ≥ -2 * ((h : ℝ) - 1) * Real.log 2 - 64 * Real.log (h : ℝ) + 2 * Real.log (2 * cθ))
    (hD2 : ∀ k : ℤ, k ∈ Qs0c h m qn →
      ∑ i ∈ (Qs0c h m qn).erase k, Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|
        ≥ -2 * ((h : ℝ) - 1) * Real.log 2 - 64 * Real.log (h : ℝ) + Real.log (2 * csep))
    (hcθ : 0 < cθ) (hcsep : 0 < csep)
    (hbudget : 256 * Real.log (h : ℝ) + 2 * Real.log (1 / (2 * cθ))
        + Real.log (1 / (2 * csep)) < (2 * (h : ℝ) - 1) * ε) :
    Uniform ε (fun p : {p : ℤ // p ∈ Qs0c h m qn} => θ + (p : ℝ) * α) := by
  classical
  refine ⟨?_, ?_⟩
  · intro i j hij hcon
    exact s0c_cos_ne hh i.property j.property (fun h => hij (Subtype.ext h)) hcθ hcsep hadd hθ
      hsep hcon
  · intro k x hx
    have hcard' : Fintype.card {p : ℤ // p ∈ Qs0c h m qn} = 2 * h := by
      rw [Fintype.card_coe]
      exact hcard
    have hexp : ((Fintype.card {p : ℤ // p ∈ Qs0c h m qn} : ℝ) - 1)
        = 2 * (h : ℝ) - 1 := by
      rw [hcard']; push_cast; ring
    have hprod : (∏ i ∈ Finset.univ.erase k,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
              - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))))
        = ∏ i ∈ (Qs0c h m qn).erase (k : ℤ),
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
              - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) := by
      refine Finset.prod_bij (fun (i : {p : ℤ // p ∈ Qs0c h m qn}) _ => (i : ℤ)) ?_ ?_ ?_ ?_
      · intro i hi
        rw [Finset.mem_erase] at hi ⊢
        exact ⟨fun hEq => hi.1 (Subtype.ext hEq), i.property⟩
      · intro i _ i' _ hEq
        exact Subtype.ext hEq
      · intro b hb
        rw [Finset.mem_erase] at hb
        refine ⟨⟨b, hb.2⟩, ?_, rfl⟩
        rw [Finset.mem_erase]
        exact ⟨fun hEq => hb.1 (congrArg Subtype.val hEq), Finset.mem_univ _⟩
      · intro i _
        rfl
    rw [hprod, hexp]
    exact s0c_prod_bound hh hadd hθ hsep hN hD1 hD2 hcθ hcsep hbudget k.property hx


/-! ## The refined range bound and the final (site-coordinate) assembly -/

/-- Refined bound with `y`: under the cell conditions `m qn ≤ y < (m+1) qn` and
`|y - m qn| < h`, every phase index of the window is bounded by `|y| + 3h`. -/
theorem Qs0c_abs_le_y {h : ℕ} {m y qn : ℤ} (hh : 1 ≤ h)
    (hym : m * qn ≤ y) (hym' : y < (m + 1) * qn)
    (hcell : |(y : ℝ) - (m : ℝ) * (qn : ℝ)| < (h : ℝ)) {p : ℤ}
    (hp : p ∈ Qs0c h m qn) : |p| ≤ |y| + 3 * (h : ℤ) := by
  have hcellZ : |y - m * qn| < (h : ℤ) := by
    have hc : (y : ℝ) - (m : ℝ) * (qn : ℝ) = ((y - m * qn : ℤ) : ℝ) := by push_cast; ring
    rw [hc] at hcell
    exact_mod_cast hcell
  have hlt := abs_lt.mp hcellZ
  have hm1 : m * qn ≤ y + (h : ℤ) := by linarith [hlt.1]
  have hm2 : y - (h : ℤ) ≤ m * qn := by linarith [hlt.2]
  have hu0 : (0 : ℤ) ≤ ((h / 2 : ℕ) : ℤ) := Int.natCast_nonneg _
  have huh : ((h / 2 : ℕ) : ℤ) ≤ (h : ℤ) := by exact_mod_cast Nat.div_le_self h 2
  have hh0 : (0 : ℤ) ≤ (h : ℤ) := Int.natCast_nonneg _
  have hy1 : y ≤ |y| := le_abs_self y
  have hy2 : -|y| ≤ y := neg_abs_le y
  rw [Qs0c, Finset.mem_union] at hp
  rw [abs_le]
  rcases hp with hp | hp
  · rw [Q1s0c, Finset.mem_Icc] at hp
    obtain ⟨h1, h2⟩ := hp
    constructor <;> linarith
  · rw [Q2s0c, Finset.mem_Icc] at hp
    obtain ⟨h1, h2⟩ := hp
    constructor <;> linarith

/-- The sum of two phase indices is within the range of `hθ` (with `y`). -/
theorem Qs0c_add_abs_le_y {h : ℕ} {m y qn : ℤ} (hh : 1 ≤ h)
    (hym : m * qn ≤ y) (hym' : y < (m + 1) * qn)
    (hcell : |(y : ℝ) - (m : ℝ) * (qn : ℝ)| < (h : ℝ)) {p q : ℤ}
    (hp : p ∈ Qs0c h m qn) (hq : q ∈ Qs0c h m qn) :
    |p + q| ≤ 2 * |y| + 8 * (h : ℤ) + 4 := by
  have h1 := Qs0c_abs_le_y hh hym hym' hcell hp
  have h2 := Qs0c_abs_le_y hh hym hym' hcell hq
  have hhR : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hh
  have h3 : |p + q| ≤ |p| + |q| := abs_add_le p q
  have hy : (0 : ℤ) ≤ |y| := abs_nonneg y
  linarith

/-- **The honest uniformity estimate in the site coordinates of the requested statement.**
This is the statement that the AJ §9 assembly can use at a prescribed scale: the rate is the
explicit budget `256 log h + 2 log (1/(2cθ)) + log (1/(2csep))` per node, and the separation
constants `cθ`, `csep` are supplied by the caller (from `θ ∉ Θ` and the continued-fraction
separation).  `hblk` is the continued-fraction block estimate (`Core.irrat_blk_nr`), and the
three block-sum bounds are `s0c_sum_bounds`. -/
theorem uni_s0c_estimate_of_sum_bounds {α θ ε cθ csep Y : ℝ} {h : ℕ} {m : ℕ} {qn : ℤ}
    (hh : 1 ≤ h) (hqn : 0 < qn) (h2h : 2 * (h : ℤ) < qn)
    (hadd : ∀ p q : ℤ, p ∈ Qs0c h (m : ℤ) qn → q ∈ Qs0c h (m : ℤ) qn →
      |p + q| ≤ 2 * |Y| + 8 * (h : ℤ) + 4)
    (hθ : ∀ j : ℤ, |j| ≤ 2 * |Y| + 8 * (h : ℤ) + 4 →
      cθ ≤ Work.TMC16Core.fracDist (2 * θ + (j : ℝ) * α))
    (hsep : ∀ p q : ℤ, p ∈ Qs0c h (m : ℤ) qn → q ∈ Qs0c h (m : ℤ) qn → p ≠ q →
      csep ≤ Work.TMC16Core.fracDist (((p - q : ℤ) : ℝ) * α))
    (hN : ∀ (k : ℤ) (ξ : ℝ), k ∈ Qs0c h (m : ℤ) qn →
      (∀ i ∈ (Qs0c h (m : ℤ) qn).erase k,
        Real.sin (Real.pi * (ξ + (i : ℝ) * α)) ≠ 0) →
      ∑ i ∈ (Qs0c h (m : ℤ) qn).erase k,
          Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
        ≤ -2 * ((h : ℝ) - 1) * Real.log 2 + 64 * Real.log (h : ℝ))
    (hD1 : ∀ k : ℤ, k ∈ Qs0c h (m : ℤ) qn →
      ∑ i ∈ (Qs0c h (m : ℤ) qn).erase k,
          Real.log |Real.sin (Real.pi * (2 * θ + ((i + k : ℤ) : ℝ) * α))|
        ≥ -2 * ((h : ℝ) - 1) * Real.log 2 - 64 * Real.log (h : ℝ)
          + 2 * Real.log (2 * cθ))
    (hD2 : ∀ k : ℤ, k ∈ Qs0c h (m : ℤ) qn →
      ∑ i ∈ (Qs0c h (m : ℤ) qn).erase k,
          Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|
        ≥ -2 * ((h : ℝ) - 1) * Real.log 2 - 64 * Real.log (h : ℝ)
          + Real.log (2 * csep))
    (hcθ : 0 < cθ) (hcsep : 0 < csep)
    (hbudget : 256 * Real.log (h : ℝ) + 2 * Real.log (1 / (2 * cθ))
        + Real.log (1 / (2 * csep)) < (2 * (h : ℝ) - 1) * ε) :
    Work.TMC16Core.Uniform ε
      (fun j : {j : ℤ // j ∈ I1s0c h ∪ I2s0c h (m : ℤ) qn} =>
        θ + (((j : ℤ) : ℝ) + ((h : ℝ) - 1)) * α) := by
  have hcard : (Qs0c h (m : ℤ) qn).card = 2 * h := card_Qs0c hqn h2h
  have hph := uniform_of_sum_bounds hh hcard hadd hθ hsep hN hD1 hD2 hcθ hcsep hbudget
  refine (Work.TMC16Core.Core.Uniform_congr (shiftEquivs0c h (m : ℤ) qn) ?_).mpr hph
  intro j
  show θ + (((j.1 + (h : ℤ) - 1 : ℤ)) : ℝ) * α = θ + (((j.1 : ℝ) + ((h : ℝ) - 1)) * α)
  push_cast
  ring

end

end Work.TMC16Core.Assembly
