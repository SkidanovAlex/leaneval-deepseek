import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.Work.CNum.Basic
import Submission.Work.CNum.ArcUpC
import Submission.Work.CNum.ArcDn
import Submission.Work.CNum.TabCert
import Submission.Work.CNum.CertC.Assemble
import Submission.Work.CNum.CertC.Sum
import Submission.Work.CNum.continuousOn_circleLog
import Submission.Work.CNum.rearrInt_bridge
import Submission.Work.CNum.PairSumFinset
import Submission.Work.CNum.PhiCNormBounds

/-! # `Work.CNum.c_numerics`

Goal: `Submission.CDTPlan.CNumerics`, i.e.

* `rearrInt (fun _ : Fin 1 => 1) (fun _ => phiC) ≤ 102/10`, and
* `∀ z, ‖z‖ = 1 → 1/10^13 ≤ ‖phiC z‖ ∧ ‖phiC z‖ ≤ 700000`.

`phiC = hauptH ∘ psiC`, `psiC z = -(3/4)·lune(23/10,z)`.  With `c = 23/10`,
`A = (1+c²)²`, `B = 16c²`, `R(z) = A(1+z)² - Bz` one has `psiC z = (3/4)·Wfun z`
with `Wfun z = -((1+c²)(z-1)+√R(z))/(2(c²-1))`.  On `|z| = 1` the image is the
union of two arcs, and

* on the `C₁`-arc (`θ ∈ (-α,α)`, `α = arccos γ`, `γ = 8c²/A - 1`),
  `Wfun(e^{iθ}) = e^{iφ(θ)}` with `φ` strictly increasing, and
  `log‖phiC‖ = Hfun ∘ φ`;
* on the `C₂`-arc, `log‖phiC‖ = Jfun ∘ ψ` with `ψ` strictly decreasing.

The `1024`-arc certificate `Gv`/`gv` (`Work.CNum.Fx`) bounds `circleLog phiC` from above and below
on each arc `[k/1024,(k+1)/1024]`:

* `ArcUp k : circleLog phiC ≤ m2r (Gv k)` and `ArcDn k : m2r (gv k) ≤ circleLog phiC`;
* `Gv_lb`/`gv_lb`/`m2r_LOG7E5DN`/`m2r_LOG1E13LB` (via the tabulated kernel certificate
  `Work.CNum.CertB.*`) give `log (10⁻¹³) ≤ m2r (gv k)` and `m2r (Gv k) ≤ log 700000`.

The rearrangement integral is then bounded by `rearrInt_bridge` (the block bound for a uniform
subdivision, from `∫∫ max(g s, g t)`) and the resulting double sum is evaluated by the kernel on
the tabulated list of the `Gv` values (`CertB.Sum`).  The pointwise range statement is
`PhiCNormBounds`.
-/

namespace Work.CNum

open Submission.CDTPlan
open scoped BigOperators

/-- `m2r` is additive over finite sums of mantissas. -/
lemma m2r_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    Work.ANum.m2r (∑ i ∈ s, f i) = ∑ i ∈ s, Work.ANum.m2r (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [Work.ANum.m2r]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Work.ANum.m2r_add, ih]

/-- `phiC` does not vanish on the unit circle: `psiC` maps the closed disc into `closedBall 0 3/4`,
where `hauptH` vanishes only at `0`, and `psiC z = 0` forces `z = 0`. -/
lemma phiC_ne_zero_of_norm_eq_one (z : ℂ) (hz : ‖z‖ = 1) : phiC z ≠ 0 := by
  intro hzero
  have hψmem : psiC z ∈ Metric.ball (0 : ℂ) 1 := by
    have h1 : ‖psiC z‖ ≤ 3 / 4 := Work.CPsi.psiC_norm_le (le_of_eq hz)
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  have hψ0 : psiC z = 0 :=
    Work.Haupt.hauptH_ne_zero _ hψmem (by simpa [phiC] using hzero)
  have hz0 : z = 0 := Work.CPsi.psiC_eq_zero hψ0
  rw [hz0] at hz
  norm_num at hz

/-- The double sum of the tabulated arc bounds, in the `Fin`-indexed form produced by
`rearrInt_bridge`, equals `m2r` of the kernel-evaluated integer double sum `pairSumLit`. -/
lemma pairSum_fin_eq :
    (∑ k : Fin 1024, ∑ k' : Fin 1024, max (Work.ANum.m2r (Gv (k : ℕ))) (Work.ANum.m2r (Gv (k' : ℕ))))
      = Work.ANum.m2r pairSumLit := by
  have step1 :
      (∑ k : Fin 1024, ∑ k' : Fin 1024,
          max (Work.ANum.m2r (Gv (k : ℕ))) (Work.ANum.m2r (Gv (k' : ℕ))))
        = ∑ k : Fin 1024, ∑ k' : Fin 1024, Work.ANum.m2r (max (Gv (k : ℕ)) (Gv (k' : ℕ))) := by
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun k' _ => ?_))
    exact (m2r_maxZ _ _).symm
  have step2 :
      (∑ k : Fin 1024, ∑ k' : Fin 1024, Work.ANum.m2r (max (Gv (k : ℕ)) (Gv (k' : ℕ))))
        = Work.ANum.m2r (∑ k : Fin 1024, ∑ k' : Fin 1024, max (Gv (k : ℕ)) (Gv (k' : ℕ))) := by
    rw [m2r_finset_sum]
    exact Finset.sum_congr rfl (fun k _ => by rw [m2r_finset_sum])
  have step3 : (∑ k : Fin 1024, ∑ k' : Fin 1024, max (Gv (k : ℕ)) (Gv (k' : ℕ)))
      = ∑ i ∈ Finset.range 1024, ∑ j ∈ Finset.range 1024, max (Gv i) (Gv j) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => ∑ k' : Fin 1024, max (Gv i) (Gv (k' : ℕ))) 1024]
    exact Finset.sum_congr rfl
      (fun i _ => Fin.sum_univ_eq_sum_range (fun j => max (Gv i) (Gv j)) 1024)
  have step4 : (∑ i ∈ Finset.range 1024, ∑ j ∈ Finset.range 1024, max (Gv i) (Gv j))
      = pairSumLit := by
    rw [PairSumFinset 1024 Gv]
    simp only [map_Gv_eq]
    exact pairSumLit_eq
  rw [step1, step2, step3, step4]

/-- The rearrangement-integral bound: `rearrInt 1 phiC ≤ 102/10`. -/
theorem rearrInt_phiC_le :
    rearrInt (fun _ : Fin 1 => (1 : ℝ)) (fun _ => phiC) ≤ 102 / 10 := by
  have hbridge : rearrInt (fun _ : Fin 1 => (1 : ℝ)) (fun _ => phiC)
      ≤ ∑ k : Fin 1024, ∑ k' : Fin 1024,
          (1 / (1024 : ℝ) ^ 2) * max (Work.ANum.m2r (Gv (k : ℕ))) (Work.ANum.m2r (Gv (k' : ℕ))) :=
    rearrInt_bridge (N := 1024) (G := fun k : Fin 1024 => Work.ANum.m2r (Gv (k : ℕ)))
      (by norm_num) continuousOn_circleLog
      (fun k t ht => ArcUpC (k : ℕ) k.isLt t (by simpa using ht))
  refine le_trans hbridge ?_
  have hsplit : (∑ k : Fin 1024, ∑ k' : Fin 1024,
        (1 / (1024 : ℝ) ^ 2) * max (Work.ANum.m2r (Gv (k : ℕ))) (Work.ANum.m2r (Gv (k' : ℕ))))
      = (1 / (1024 : ℝ) ^ 2) *
        ∑ k : Fin 1024, ∑ k' : Fin 1024,
          max (Work.ANum.m2r (Gv (k : ℕ))) (Work.ANum.m2r (Gv (k' : ℕ))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
  rw [hsplit, pairSum_fin_eq]
  -- the kernel-evaluated integer certificate
  have hSC : (0 : ℝ) < (Work.ANum.SC : ℝ) := Work.ANum.SC_posR
  have hok : (pairSumLit : ℝ) * 10 ≤ 102 * 1024 * 1024 * (Work.ANum.SC : ℝ) := by
    have hZ : pairSumLit * 10 ≤ 102 * 1024 * 1024 * Work.ANum.SC := pairSumLit_ok
    have h := (Int.cast_le (R := ℝ)).mpr hZ
    push_cast at h
    linarith [h]
  have hm2r : Work.ANum.m2r pairSumLit = (pairSumLit : ℝ) / (Work.ANum.SC : ℝ) := rfl
  rw [hm2r]
  have hsl : (1 / (1024 : ℝ) ^ 2) * ((pairSumLit : ℝ) / (Work.ANum.SC : ℝ))
      = (pairSumLit : ℝ) / ((1024 : ℝ) ^ 2 * (Work.ANum.SC : ℝ)) := by
    field_simp
  rw [hsl, div_le_iff₀ (mul_pos (by norm_num) hSC)]
  have hgoal : (102 / 10) * ((1024 : ℝ) ^ 2 * (Work.ANum.SC : ℝ))
      = (102 * 1024 * 1024 * (Work.ANum.SC : ℝ)) / 10 := by ring
  rw [hgoal, le_div_iff₀ (by norm_num : (0 : ℝ) < 10)]
  linarith [hok]

/-- The boundary range of `|phiC|`: `1/10^13 ≤ ‖phiC z‖ ≤ 700000` on the unit circle. -/
theorem phiC_norm_bounds (z : ℂ) (hz : ‖z‖ = 1) :
    (1 : ℝ) / 10 ^ 13 ≤ ‖phiC z‖ ∧ ‖phiC z‖ ≤ 700000 :=
  PhiCNormBounds (fun k hk t ht => ArcUpC k hk t ht) (fun k hk t ht => ArcDn k hk t ht)
    (fun k hk => le_trans (Work.ANum.m2r_le (Gv_lb k hk)) m2r_LOG7E5DN)
    (fun k hk => le_trans m2r_LOG1E13LB (Work.ANum.m2r_le (gv_lb k hk)))
    z hz (phiC_ne_zero_of_norm_eq_one z hz)

theorem c_numerics : CNumerics :=
  ⟨rearrInt_phiC_le, phiC_norm_bounds⟩

end Work.CNum
