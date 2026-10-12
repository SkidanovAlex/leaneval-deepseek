import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowQ2.maskTailDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.chiHatSq_tsum_le` — the `χ̂²`-lattice-tail of the corpus bump

The sibling `Work.BoseRowQ2.corpusBox_hatChi_sq_tsum_le` bounds the lattice tail of
`χ̂` (the cosine transform of `χ`).  The mask row of FS l.3253 needs the same estimate for
`χ̂²` (the cosine transform of `χ²`, `Work.BoseRowQ2.chiHatSq`), and this is what is proved
here:

    `∑'_{n : ℤ³, ‖vec n‖ ≥ R} χ̂²(vec n)² ≤ C/R^101`     for every `R ≥ 1`.

The mathematics is identical to the `χ̂` case — FS `lem:DecaychiHat`
(`Work.BoseK15.ChiReg_corpus`) gives, at every order `s`, a constant `Cchi` with

    `|χ̂²(p)| · (1 + ‖p‖²)^s ≤ Cchi`      for all `p`,

since `χ²` is again `C^∞` with compact support — but it is a genuinely different kernel
(`Work.BoseK15.ChiReg_corpus` is applied at its *second* conjunct), so the estimate has to
be re-derived: at order `52` the pointwise decay gives `χ̂²(vec n)² ≤ Cchi²(1+‖vec n‖²)^{-104}`
and the dyadic-annulus lattice tail `Work.BoseK15.sum_inv_one_add_norm_tail 104 101`
(allowed since `101 + 3 ≤ 2·104`) bounds the sum.

The finite-set bound is upgraded to the `tsum` over the subtype
`{n : Fin 3 → ℤ // R ≤ ‖vec n‖}` by the standard nonnegativity argument: in `ℝ≥0∞` the
`tsum` is the supremum of the finite partial sums, hence is `≤ ofReal (C/R^101) < ⊤`, and
`ENNReal.toReal` transfers the bound back to `ℝ`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowQ2

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The finite-set tail bound -/

/-- **The `χ̂²`-tail over a finite set of dual-lattice indices.**  There is a constant
`C ≥ 0` such that for every `R ≥ 1` and every finite set `S` of lattice indices whose
momenta `vec n = 2πn` all have norm at least `R`, the sum of `χ̂²(vec n)²` over `S` is at
most `C/R^101`.

Proof: `ChiReg_corpus 52` gives `|χ̂²(p)|(1+‖p‖²)^52 ≤ Cchi` (its *second* conjunct, applied
to `χ²`), hence `χ̂²(p)² ≤ Cchi²·(1+‖p‖²)^{-104}`; summing over `S` and applying the lattice
tail estimate `sum_inv_one_add_norm_tail 104 101` (legal since `101 + 3 ≤ 2·104`) gives the
claim with `C = Cchi²·Ctail`. -/
theorem chiHatSq_finset_tail_sum :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (S : Finset (Fin 3 → ℤ)), 1 ≤ R →
      (∀ n ∈ S, R ≤ ‖Work.BoseB4.vec n‖) →
      (∑ n ∈ S, chiHatSq (Work.BoseB4.vec n) ^ 2) ≤ C / R ^ 101 := by
  -- the `χ̂²`-decay at order `52` and the lattice tail sum at `(s, M) = (104, 101)`
  obtain ⟨Cchi, hCchi_nn, hChi⟩ := Work.BoseK15.ChiReg_corpus 52
  obtain ⟨Ctail, _hCtail_nn, hCtail⟩ :=
    Work.BoseK15.sum_inv_one_add_norm_tail 104 101 (by norm_num)
  refine ⟨Cchi ^ 2 * Ctail, by positivity, ?_⟩
  intro R S hR hS
  -- the pointwise bound `χ̂²(p)² ≤ Cchi²·(1+‖p‖²)^{-104}`
  have hpoint : ∀ n ∈ S, chiHatSq (Work.BoseB4.vec n) ^ 2
      ≤ Cchi ^ 2 * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 104)⁻¹ := by
    intro n _hn
    have hD : (0 : ℝ) < (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52 := by positivity
    have hle : |chiHatSq (Work.BoseB4.vec n)|
        ≤ Cchi / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52 := by
      rw [le_div_iff₀ hD]
      simpa only [chiHatSq] using hChi.2 (Work.BoseB4.vec n)
    have hK : 0 ≤ Cchi / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52 := div_nonneg hCchi_nn hD.le
    have hpow : (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52) ^ 2
        = ((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 104 := by
      rw [← pow_mul]
    calc chiHatSq (Work.BoseB4.vec n) ^ 2
        ≤ (Cchi / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52) ^ 2 := by
          rw [sq_le_sq, abs_of_nonneg hK]; exact hle
      _ = Cchi ^ 2 * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 104)⁻¹ := by
          rw [div_pow, div_eq_mul_inv, hpow]
  calc (∑ n ∈ S, chiHatSq (Work.BoseB4.vec n) ^ 2)
      ≤ ∑ n ∈ S, Cchi ^ 2 * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 104)⁻¹ :=
        Finset.sum_le_sum hpoint
    _ = Cchi ^ 2 * ∑ n ∈ S, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 104)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ Cchi ^ 2 * (Ctail / R ^ 101) :=
        mul_le_mul_of_nonneg_left (hCtail R S hR hS) (by positivity)
    _ = (Cchi ^ 2 * Ctail) / R ^ 101 := by ring

/-! ## 2. The passage to the `tsum` over the subtype -/

/-- **From a finite-set lattice bound to the `tsum`.**  If a *nonnegative* summand
`f : ℤ³ → ℝ` satisfies `∑_S f ≤ C/R^101` for every finite set `S` of lattice indices whose
momenta all have norm at least `R ≥ 1`, then the same bound holds for the `tsum` over the
subtype `{n : Fin 3 → ℤ // R ≤ ‖vec n‖}`.

This is the standard nonnegativity passage: every finite partial sum of the subtype sum is
at most `C/R^101`, so in `ℝ≥0∞` the `tsum` is `≤ ofReal (C/R^101) < ⊤`; `ENNReal.toReal`
(monotone, and inverse to `ofReal` on nonnegative reals) then transfers the bound back. -/
theorem tsum_subtype_le_of_finset {f : (Fin 3 → ℤ) → ℝ} (hnn : ∀ n, 0 ≤ f n) {C : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ (R : ℝ) (S : Finset (Fin 3 → ℤ)), 1 ≤ R →
      (∀ n ∈ S, R ≤ ‖Work.BoseB4.vec n‖) → (∑ n ∈ S, f n) ≤ C / R ^ 101)
    (R : ℝ) (hR : 1 ≤ R) :
    (∑' n : {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖}, f n.val) ≤ C / R ^ 101 := by
  have hB : 0 ≤ C / R ^ 101 := div_nonneg hC0 (by positivity)
  -- the finite partial sums over the subtype, transported to finite sets of lattice indices
  have hfin : ∀ s : Finset {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖},
      ∑ x ∈ s, f x.val ≤ C / R ^ 101 := by
    intro s
    have hS : ∀ n ∈ s.map (Function.Embedding.subtype
        (fun n : Fin 3 → ℤ => R ≤ ‖Work.BoseB4.vec n‖)),
        R ≤ ‖Work.BoseB4.vec n‖ := by
      intro n hn
      rw [Finset.mem_map] at hn
      obtain ⟨x, _hx, rfl⟩ := hn
      exact x.2
    have h1 := hC R (s.map (Function.Embedding.subtype
      (fun n : Fin 3 → ℤ => R ≤ ‖Work.BoseB4.vec n‖))) hR hS
    rw [Finset.sum_map] at h1
    exact h1
  -- the `ℝ≥0∞` version: `tsum` is the supremum of the finite partial sums
  have hENN : (∑' n : {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖}, ENNReal.ofReal (f n.val))
      ≤ ENNReal.ofReal (C / R ^ 101) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => hnn n.val)]
    exact ENNReal.ofReal_le_ofReal (hfin s)
  have hsummand : ∀ n : {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖},
      ENNReal.ofReal (f n.val) ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  have hne : (∑' n : {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖},
      ENNReal.ofReal (f n.val)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hENN
  -- back to `ℝ`: `toReal` of the `ℝ≥0∞`-sum is the real `tsum`, and it is monotone
  have htoReal : (∑' n : {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖},
        ENNReal.ofReal (f n.val)).toReal
      = ∑' n : {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖}, f n.val := by
    rw [ENNReal.tsum_toReal_eq hsummand]
    exact tsum_congr fun n => ENNReal.toReal_ofReal (hnn n.val)
  calc (∑' n : {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖}, f n.val)
      = (∑' n : {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖},
          ENNReal.ofReal (f n.val)).toReal := htoReal.symm
    _ ≤ (ENNReal.ofReal (C / R ^ 101)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
    _ = C / R ^ 101 := ENNReal.toReal_ofReal hB

/-! ## 3. The target -/

/-- **The `χ̂²`-lattice tail of the corpus bump.**  There is a constant `C ≥ 0` with

    `∑'_{n : ℤ³, ‖2πn‖ ≥ R} χ̂²(2πn)² ≤ C/R^101`      for every `R ≥ 1`.

Only existence of the constant is used downstream; the one produced here is
`Cchi²·Ctail` from `chiHatSq_finset_tail_sum`. -/
theorem chiHatSq_tsum_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      (∑' n : {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖},
        Work.BoseRowQ2.chiHatSq (Work.BoseB4.vec n.val) ^ 2) ≤ C / R ^ 101 := by
  obtain ⟨C, hC0, hC⟩ := chiHatSq_finset_tail_sum
  exact ⟨C, hC0, fun R hR =>
    tsum_subtype_le_of_finset (fun n => sq_nonneg _) hC0 hC R hR⟩

end Work.BoseRowQ2
