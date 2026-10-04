import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.pdList_le_sqrt_CSq
import Submission.Work.Diff.STE.CSq_le_ENormSq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

/-!
# Sup bounds for iterated derivatives from the `Hᵏ` energy

The Sobolev sup bound of `Work.Diff.STE.B3.pdList_le_sqrt_CSq` controls every iterated partial
derivative `∂^l f` of a smooth `1`-periodic function `f : (ι → ℝ) → ℂ` on the flat torus by the
weighted `ℓ²` norm `√(CSq k (fourierCoeff f))` of its Fourier coefficients, provided
`card ι + 2 * l.length < 2 * k`.  Here we replace the Fourier-side norm by the *physical* energy
`ENormSq` (`= Σ_{α : Fin k → ι} ∫_{cube} ‖∂^α f‖²`), using the Sobolev comparison
`CSq k (fourierCoeff f) ≤ C (ENormSq k f + ENormSq 0 f)`:

  `‖∂^l f x‖ ≤ C √E`

for all smooth `1`-periodic `f`, all lists `l` with `card ι + 2 l.length < 2 k`, all `x`, and all
`E` dominating both `ENormSq k f` and `ENormSq 0 f`.

## The uniformity in `l`

The analytic input `pdList_le_sqrt_CSq k m hm` produces a constant depending on the *order* `m`
(`l.length ≤ m`), so a single application cannot cover all lists: for a fixed `m` the hypothesis
`card ι + 2 m < 2 k` is only available when `m < k`, and the admissible lengths form an initial
segment.  We therefore define, for every `m`, the constant `cc m` attached to the order `m` (and
the junk value `0` when the order `m` is not admissible), and take the *sum* over `m ∈ range k`.
A list `l` satisfying the hypothesis of the theorem has `l.length < k`, hence `cc l.length` is one
of the summands, and the sum dominates it because all summands are nonnegative.

## The square root

`√(CSq k (fourierCoeff f)) ≤ √(2 * C) * √E`, by `Real.sqrt_le_sqrt` and `Real.sqrt_mul`.  No
hypothesis `E ≥ 0` is needed: only `2 * C ≥ 0` is used when splitting the square root.
-/

theorem sup_pdList_le_of_energy {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : (ι → ℝ) → ℂ) (E : ℝ),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f → Work.Diff.STE.Periodic1 f →
      Work.Diff.STE.ENormSq k f ≤ E → Work.Diff.STE.ENormSq 0 f ≤ E →
      ∀ (l : List ι), Fintype.card ι + 2 * l.length < 2 * k → ∀ x : ι → ℝ,
        ‖Work.Diff.STE.pdList l f x‖ ≤ C * Real.sqrt E := by
  classical
  -- the Sobolev comparison constant, fixed once and for all
  obtain ⟨C2, hC20, hC2b⟩ := Work.Diff.STE.CSq_le_ENormSq (ι := ι) k
  -- the Fourier-side sup constant attached to the order `m` (junk value `0` for inadmissible `m`)
  let cc : ℕ → ℝ := fun m =>
    if h : Fintype.card ι + 2 * m < 2 * k then
      Classical.choose (Work.Diff.STE.B3.pdList_le_sqrt_CSq (ι := ι) k m h)
    else 0
  let Cm : ℕ → ℝ := fun m => cc m * Real.sqrt (2 * C2)
  have hcc : ∀ m, 0 ≤ cc m := by
    intro m
    dsimp only [cc]
    split
    · rename_i h
      exact (Classical.choose_spec (Work.Diff.STE.B3.pdList_le_sqrt_CSq (ι := ι) k m h)).1
    · exact le_refl 0
  have hCm : ∀ m, 0 ≤ Cm m := fun m => mul_nonneg (hcc m) (Real.sqrt_nonneg _)
  refine ⟨Finset.sum (Finset.range k) Cm, Finset.sum_nonneg (fun m _ => hCm m), ?_⟩
  intro f E hf hper hEk hE0 l hl x
  -- the length of `l` is an admissible order, and it lies in `range k`
  have hlen : l.length < k := by omega
  have hmem : l.length ∈ Finset.range k := Finset.mem_range.mpr hlen
  have hcc_eq : cc l.length =
      Classical.choose (Work.Diff.STE.B3.pdList_le_sqrt_CSq (ι := ι) k l.length hl) := by
    dsimp only [cc]; exact dite_eq_left hl
  have hderiv0 := (Classical.choose_spec
    (Work.Diff.STE.B3.pdList_le_sqrt_CSq (ι := ι) k l.length hl)).2 f hf hper l le_rfl x
  have hderiv : ‖Work.Diff.STE.pdList l f x‖
      ≤ cc l.length * Real.sqrt (Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff f)) := by
    rw [hcc_eq]; exact hderiv0
  -- the Fourier norm is controlled by the physical energy
  have hCSq : Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff f) ≤ (2 * C2) * E := by
    have h1 := hC2b f (hf.of_le (WithTop.coe_le_coe.mpr (le_top : (k : ℕ∞) ≤ ⊤))) hper
    refine h1.trans ?_
    rw [mul_add]
    have ha := mul_le_mul_of_nonneg_left hEk hC20
    have hb := mul_le_mul_of_nonneg_left hE0 hC20
    linarith
  have hsqrt : Real.sqrt (Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff f))
      ≤ Real.sqrt (2 * C2) * Real.sqrt E := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * C2) E]
    exact Real.sqrt_le_sqrt hCSq
  have hmain : ‖Work.Diff.STE.pdList l f x‖
      ≤ cc l.length * (Real.sqrt (2 * C2) * Real.sqrt E) :=
    hderiv.trans (mul_le_mul_of_nonneg_left hsqrt (hcc l.length))
  have hsum : Cm l.length ≤ Finset.sum (Finset.range k) Cm :=
    Finset.single_le_sum (fun m _ => hCm m) hmem
  calc ‖Work.Diff.STE.pdList l f x‖
      ≤ cc l.length * (Real.sqrt (2 * C2) * Real.sqrt E) := hmain
    _ = Cm l.length * Real.sqrt E := by dsimp only [Cm]; ring
    _ ≤ (Finset.sum (Finset.range k) Cm) * Real.sqrt E :=
        mul_le_mul_of_nonneg_right hsum (Real.sqrt_nonneg E)

end Work.Diff.STE.Lead.GalTame
