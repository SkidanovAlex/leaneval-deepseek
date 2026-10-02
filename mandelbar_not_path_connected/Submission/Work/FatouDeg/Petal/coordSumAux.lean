import Mathlib
import Submission.Work.FatouDeg.Petal.DefsAux
import Submission.Work.FatouDeg.Petal.orbitBoundsAux
import Submission.Work.FatouDeg.Petal.rpowSumBound
import Submission.Work.FatouDeg.Petal.afunDifferentiableAt
import Submission.Work.FatouDeg.Petal.rfunSummableUniform
import Submission.Work.FatouDeg.Petal.rfunGrowthBound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg.Petal

open scoped Topology
open Set Filter Metric

/-! ## Elementary facts about the working domain -/

/-- Every point of the working domain `Dom m ρ` has positive real part (its imaginary part is
dominated by a nonnegative multiple of the real part). -/
lemma Dom_re_pos {m : ℕ} {ρ : ℝ} {z : ℂ} (hz : z ∈ Dom m ρ) : 0 < z.re := by
  obtain ⟨-, h⟩ := mem_Dom.mp hz
  have h2 : 0 ≤ (7 * (m : ℝ) / 8) * |z.im| := mul_nonneg (by positivity) (abs_nonneg _)
  linarith

/-- The polynomial map `Pfun m G` is entire. -/
lemma Pfun_differentiable (m : ℕ) (G : Polynomial ℂ) : Differentiable ℂ (Pfun m G) := by
  unfold Pfun
  exact (differentiable_id.sub (differentiable_pow m)).add
    ((differentiable_pow (m + 1)).mul (Polynomial.differentiable G))

/-- Iterates of `Pfun m G` stay in any invariant set. -/
lemma iterate_mem {m : ℕ} {G : Polynomial ℂ} {ρ : ℝ}
    (hmap : Set.MapsTo (Pfun m G) (Dom m ρ) (Dom m ρ)) :
    ∀ z ∈ Dom m ρ, ∀ k : ℕ, (Pfun m G)^[k] z ∈ Dom m ρ := by
  intro z hz k
  induction k with
  | zero => simpa using hz
  | succ k ih => rw [Function.iterate_succ_apply']; exact hmap ih

/-- `Rfun m G` is holomorphic at every point `w` such that both `w` and `Pfun m G w` lie in the
right half-plane (the two points where `Afun` is evaluated). -/
lemma Rfun_differentiableAt (m : ℕ) (hm : 1 ≤ m) (G : Polynomial ℂ) {w : ℂ}
    (hw : 0 < w.re) (hPw : 0 < (Pfun m G w).re) :
    DifferentiableAt ℂ (Rfun m G) w := by
  have h1 : DifferentiableAt ℂ (fun z : ℂ => Afun m G (Pfun m G z)) w :=
    (afunDifferentiableAt m hm G hPw).comp w (Pfun_differentiable m G).differentiableAt
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Afun m G z) w :=
    afunDifferentiableAt m hm G hw
  have h3 : DifferentiableAt ℂ (fun z : ℂ => Afun m G (Pfun m G z) - Afun m G z - 1) w :=
    ((h1.sub h2).sub (differentiableAt_const (1 : ℂ)))
  change DifferentiableAt ℂ (fun z : ℂ => Afun m G (Pfun m G z) - Afun m G z - 1) w
  exact h3

/-- **The Fatou coordinate exists on the working domain and grows like the chart.**

Assume that `Dom m ρ` is `P`-invariant, that `‖P z‖ ≤ ‖z‖` and that the chart
`z ↦ (‖z‖^(m-1))⁻¹` increases by at least `c > 0` at every step on `Dom m ρ`, and that the defect
bound `‖Rfun m G z‖ ≤ C * ‖z‖^m` holds on `Dom m ρ`.  Then

* the defect series converges at every point of `Dom m ρ`;
* the Fatou coordinate `phifun m G = Afun m G + ∑' k, Rfun m G ∘ P^[k]` is holomorphic on
  `Dom m ρ`;
* it satisfies the Abel equation `phifun m G (P z) = phifun m G z + 1`;
* it stays within `D * ‖z‖` of the approximate coordinate.

Sketch: the orbit bound `‖P^[k] z‖^(m-1) ≤ ((‖z‖^(m-1))⁻¹ + c k)⁻¹` gives
`‖Rfun m G (P^[k] z)‖ ≤ C ((‖z‖^(m-1))⁻¹ + c k)^(-m/(m-1)) ≤ C (c k)^(-m/(m-1))`, summable since
`m/(m-1) > 1` and uniform in `z`, so the partial sums converge locally uniformly to a holomorphic
function (`TendstoLocallyUniformlyOn.differentiableOn`).  The Abel equation follows by shifting the
index (`Summable.tsum_nat_add` / `tsum_nat_add`), using that `P z ∈ Dom m ρ` again.  For the growth
bound split the sum at `k₀ = ⌈(‖z‖^(m-1))⁻¹⌉`: the first `k₀` terms are `≤ C‖z‖^m` each, and the
tail is bounded by `∑_{k>k₀} C (ck)^(-m/(m-1)) ≤ C'' k₀^(-1/(m-1)) = C'' ‖z‖`.  (`Dom m ρ` is open
and contained in `Re z > 0`, so `Complex.log` is holomorphic there.) -/
theorem coordSumAux (m : ℕ) (hm : 3 ≤ m) (G : Polynomial ℂ) {ρ c C : ℝ} (hρ : 0 < ρ) (hc : 0 < c)
    (hC : 0 ≤ C)
    (hmap : Set.MapsTo (Pfun m G) (Dom m ρ) (Dom m ρ))
    (hnorm : ∀ z ∈ Dom m ρ, ‖Pfun m G z‖ ≤ ‖z‖)
    (hcontract : ∀ z ∈ Dom m ρ, (‖z‖ ^ (m - 1))⁻¹ + c ≤ (‖Pfun m G z‖ ^ (m - 1))⁻¹)
    (hdefect : ∀ z ∈ Dom m ρ, ‖Rfun m G z‖ ≤ C * ‖z‖ ^ m) :
    (∀ z ∈ Dom m ρ, Summable (fun k : ℕ => Rfun m G ((Pfun m G)^[k] z))) ∧
    DifferentiableOn ℂ (phifun m G) (Dom m ρ) ∧
    (∀ z ∈ Dom m ρ, phifun m G (Pfun m G z) = phifun m G z + 1) ∧
    (∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ Dom m ρ, ‖phifun m G z - Afun m G z‖ ≤ D * ‖z‖) := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨hsum, hluc⟩ := rfunSummableUniform m hm G hρ hc hC hmap hnorm hcontract hdefect
  -- differentiability of the individual summands, by the chain rule
  have hterm : ∀ n : ℕ, ∀ r ∈ Dom m ρ,
      DifferentiableAt ℂ (fun z : ℂ => Rfun m G ((Pfun m G)^[n] z)) r := by
    intro n r hr
    have hrD : (Pfun m G)^[n] r ∈ Dom m ρ := iterate_mem hmap r hr n
    have hrP : (Pfun m G)^[n + 1] r ∈ Dom m ρ := iterate_mem hmap r hr (n + 1)
    have hPval : (Pfun m G) ((Pfun m G)^[n] r) = (Pfun m G)^[n + 1] r := by
      simp only [Function.iterate_succ_apply']
    have hPR : DifferentiableAt ℂ (Rfun m G) ((Pfun m G)^[n] r) := by
      refine Rfun_differentiableAt m hm1 G (Dom_re_pos hrD) ?_
      rw [hPval]
      exact Dom_re_pos hrP
    have hiter : DifferentiableAt ℂ ((Pfun m G)^[n]) r :=
      ((Pfun_differentiable m G).iterate n).differentiableAt
    exact hPR.comp r hiter
  refine ⟨hsum, ?_, ?_, ?_⟩
  · -- holomorphy of `phifun`
    have hAdiff : DifferentiableOn ℂ (Afun m G) (Dom m ρ) := fun w hw =>
      (afunDifferentiableAt m hm1 G (Dom_re_pos hw)).differentiableWithinAt
    have hSdiff : DifferentiableOn ℂ
        (fun z : ℂ => ∑' n : ℕ, Rfun m G ((Pfun m G)^[n] z)) (Dom m ρ) :=
      SummableLocallyUniformlyOn.differentiableOn (isOpen_Dom m ρ) hluc hterm
    show DifferentiableOn ℂ (fun z : ℂ => Afun m G z + ∑' n : ℕ, Rfun m G ((Pfun m G)^[n] z)) (Dom m ρ)
    exact hAdiff.add hSdiff
  · -- the Abel equation
    intro z hz
    have hsumz : Summable (fun k : ℕ => Rfun m G ((Pfun m G)^[k] z)) := hsum z hz
    have hsplit : (∑' k : ℕ, Rfun m G ((Pfun m G)^[k + 1] z))
        = (∑' k : ℕ, Rfun m G ((Pfun m G)^[k] z)) - Rfun m G z := by
      have h := hsumz.sum_add_tsum_nat_add 1
      simp only [Finset.sum_range_one, Function.iterate_zero_apply] at h
      rw [eq_sub_iff_add_eq, add_comm]
      exact h
    have hshift : (∑' k : ℕ, Rfun m G ((Pfun m G)^[k] (Pfun m G z)))
        = ∑' k : ℕ, Rfun m G ((Pfun m G)^[k + 1] z) := by
      apply tsum_congr
      intro k
      rw [Function.iterate_succ_apply]
    have hR : Rfun m G z = Afun m G (Pfun m G z) - Afun m G z - 1 := rfl
    simp only [phifun]
    rw [hshift, hsplit, hR]
    ring
  · -- the growth bound
    refine ⟨C * ((2 * ρ) ^ (m - 1) + (m - 1) / c), ?_, ?_⟩
    · have h1 : (0 : ℝ) ≤ 2 * ρ := by linarith
      have h2 : (0 : ℝ) ≤ (2 * ρ) ^ (m - 1) := pow_nonneg h1 _
      have h3 : (0 : ℝ) ≤ (m - 1) / c := by
        refine div_nonneg ?_ hc.le
        have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
        push_cast
        linarith
      exact mul_nonneg hC (add_nonneg h2 h3)
    · intro z hz
      have h := rfunGrowthBound m hm G hρ hc hC hmap hnorm hcontract hdefect z hz
      have heq : phifun m G z - Afun m G z = ∑' k : ℕ, Rfun m G ((Pfun m G)^[k] z) := by
        simp [phifun]
      rw [heq]
      exact h

end Work.FatouDeg.Petal
