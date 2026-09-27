import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.hetero_box
import Submission.Work.EQ.arc_near_A1
import Submission.Work.EQ.polarPt_basic
import Submission.Work.EQ.polarPt_inj
import Submission.Work.EQ.arc_eqU_maps
import Submission.Work.EQ.normEqCurve_periodic_and_sum
import Submission.Work.EQ.arc_iterate_aux
import Submission.Work.EQ.arcPt_O2_repr
import Submission.Work.EQ.arcPt_angle_lt_of_O2_repr
import Submission.Work.EQ.arcPt_limit_im_eq_zero

namespace Work.EQ

open Complex Filter
open scoped Topology

/-- **Orbits on the open upper arc converge to `A₁`.**  For a symmetric normalised equichordal
curve the half-map `eqU` maps the open upper arc (`arcSet a ρ₁`, in `Submission.Work.EQ.hetero_box`)
into itself; every forward orbit of a point of the open upper arc tends to `A₁ = -1/2`.

Route.  `hC`'s last clause says `range (polarPt (-(a/2)) (ρ₁·)) = range (polarPt (a/2) (ρ₂·))`;
with `exists_angle_of_mem_range` (in `Submission.Work.EQ.arc_eqU_maps`) this gives, for each
`θ ∈ (0,π)`, a unique `ψ ∈ (0,π)` with `polarPt (-(a/2)) (ρ₁ θ) θ = polarPt (a/2) (ρ₂ ψ) ψ`.
Take the *total* `ψ θ := Complex.arg (polarPt (-(a/2)) (ρ₁ θ) θ - ((a/2:ℝ):ℂ))`; prove
`0 < ψ θ < π` for `θ ∈ (0,π)` using `Complex.arg_nonneg_iff`, `Complex.sin_arg`,
`Complex.arg_le_pi`.  Then (i) `eqU a (polarPt (-(a/2)) (ρ₁ θ) θ) = polarPt (-(a/2)) (ρ₁ (ψ θ)) (ψ θ)`
(from `eqU a z = -z + (z-O₂)/‖z-O₂‖` and `ρ₂(ψ+π) = ρ₁ ψ`, via
`normEqCurve_periodic_and_sum`), and (ii) `ψ θ > θ`: with `u = ρ₁ θ`, `v = ρ₂ (ψ θ)` the
identity gives `u sin θ = v sin ψ` and `u cos θ - v cos ψ = a`, so
`v * sin (ψ-θ) = a * sin θ > 0`, whence `ψ-θ ∈ (0,π)` (contradiction via
`Real.sin_nonpos_of_nonpos_of_neg_pi_le`).  Hence `θ_0 := θ`, `θ_{m+1} := ψ θ_m` is strictly
increasing and `≤ π`, so converges to `ℓ`; limits give `eqU`-fixed `polarPt (-(a/2)) (ρ₁ ℓ) ℓ`; the
only fixed points of `eqU` are `∓1/2` (`2P = (P-O₂)/‖P-O₂‖` forces `P` real), while `ℓ ≥ θ_0 > 0`,
so `ℓ = π`, and `polarPt (-(a/2)) (ρ₁ π) π = -1/2` (`arc_near_A1`).  Clause 5 of `arc_near_A1`
gives `z = polarPt (-(a/2)) (ρ₁ θ) θ` with `θ ∈ (0,π)`, and `(eqU a)^[m] z = polarPt (-(a/2)) (ρ₁ θ_m) θ_m`. -/
theorem arc_iterate_tendsto_A1 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ) (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ))
    {z : ℂ} (hz : z ∈ arcSet a ρ₁) (hzim : 0 < z.im) :
    Filter.Tendsto (fun m : ℕ => (eqU a)^[m] z) Filter.atTop (nhds ((-(1/2) : ℝ) : ℂ)) := by
  classical
  have hρ₁pos : ∀ θ, 0 < ρ₁ θ := hC.2.2.1
  -- Step 1: a parameter `θ₀ ∈ (0, π)` with `z = arcPt a ρ₁ θ₀`.
  obtain ⟨hA1, -, -, -, -, harcθ, -, -⟩ := arc_near_A1 ha0 ha1 hC hs₁ hs₂
  rw [arcSet] at hz
  obtain ⟨θ₀, hθ₀0, hθ₀π, hzθ⟩ := harcθ z hz hzim
  -- Step 2: the (choice) next-angle map on `(0, π)`.
  have hnext : ∀ θ : ℝ, 0 < θ → θ < Real.pi →
      ∃ ψ : ℝ, 0 < ψ ∧ ψ < Real.pi ∧ θ < ψ ∧ eqU a (arcPt a ρ₁ θ) = arcPt a ρ₁ ψ := by
    intro θ hθ0 hθπ
    obtain ⟨ψ, hψ0, hψπ, hrepr, hU⟩ := arcPt_O2_repr ha0 ha1 hC hs₁ hs₂ hθ0 hθπ
    exact ⟨ψ, hψ0, hψπ,
      arcPt_angle_lt_of_O2_repr ha0 hθ0 hθπ hψ0 hψπ (hC.2.2.2.1 ψ) hrepr, hU⟩
  have hex : ∀ θ : ℝ, ∃ ψ : ℝ, (0 < θ ∧ θ < Real.pi) →
      0 < ψ ∧ ψ < Real.pi ∧ θ < ψ ∧ eqU a (arcPt a ρ₁ θ) = arcPt a ρ₁ ψ := by
    intro θ
    by_cases h : 0 < θ ∧ θ < Real.pi
    · obtain ⟨ψ, h1, h2, h3, h4⟩ := hnext θ h.1 h.2
      exact ⟨ψ, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨0, fun hh => absurd hh h⟩
  let nxt : ℝ → ℝ := fun θ => Classical.choose (hex θ)
  have hnxt : ∀ θ (h : 0 < θ ∧ θ < Real.pi), 0 < nxt θ ∧ nxt θ < Real.pi ∧ θ < nxt θ ∧
      eqU a (arcPt a ρ₁ θ) = arcPt a ρ₁ (nxt θ) := fun θ h => Classical.choose_spec (hex θ) h
  -- Step 3: the orbit of angles.
  let θm : ℕ → ℝ := fun m => nxt^[m] θ₀
  have hθm_zero : θm 0 = θ₀ := rfl
  have hbound : ∀ m, 0 < θm m ∧ θm m < Real.pi := by
    intro m
    induction m with
    | zero => rw [hθm_zero]; exact ⟨hθ₀0, hθ₀π⟩
    | succ m ih =>
        rw [show θm (m + 1) = nxt (θm m) from Function.iterate_succ_apply' nxt m θ₀]
        exact ⟨(hnxt (θm m) ih).1, (hnxt (θm m) ih).2.1⟩
  have hstep : ∀ m, θm m < θm (m + 1) := by
    intro m
    rw [show θm (m + 1) = nxt (θm m) from Function.iterate_succ_apply' nxt m θ₀]
    exact (hnxt (θm m) (hbound m)).2.2.1
  have hUm : ∀ m, eqU a (arcPt a ρ₁ (θm m)) = arcPt a ρ₁ (θm (m + 1)) := by
    intro m
    rw [show θm (m + 1) = nxt (θm m) from Function.iterate_succ_apply' nxt m θ₀]
    exact (hnxt (θm m) (hbound m)).2.2.2
  -- Step 4: convergence of the angles.
  have hmono : Monotone θm := monotone_nat_of_le_succ (fun m => le_of_lt (hstep m))
  have hBdd : BddAbove (Set.range θm) :=
    ⟨Real.pi, by rintro _ ⟨m, rfl⟩; exact le_of_lt (hbound m).2⟩
  let L : ℝ := ⨆ m, θm m
  have hLdef : L = ⨆ m, θm m := rfl
  have hlim : Tendsto θm atTop (nhds L) := tendsto_atTop_ciSup hmono hBdd
  have hLpos : 0 < L := by
    have h := le_ciSup hBdd 0
    rw [hLdef]
    exact lt_of_lt_of_le hθ₀0 (by simpa [θm] using h)
  have hLle : L ≤ Real.pi := by
    rw [hLdef]; exact ciSup_le (fun m => le_of_lt (hbound m).2)
  -- Step 5: the limiting arc point is real, hence (being in `(0, π]` parametrised) `A₁`.
  have him : (arcPt a ρ₁ L).im = 0 := arcPt_limit_im_eq_zero ha0 hC hlim hUm
  have hsin : Real.sin L = 0 := by
    have h1 : ρ₁ L * Real.sin L = 0 := by
      rw [arcPt_im a ρ₁ L] at him
      exact him
    exact (mul_eq_zero.mp h1).resolve_left (ne_of_gt (hρ₁pos L))
  have hLpi : L = Real.pi := by
    by_contra hne
    have hlt : L < Real.pi := lt_of_le_of_ne hLle hne
    exact absurd hsin (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hLpos hlt))
  have hcast : ((-(1/2) : ℝ) : ℂ) = -(1/2 : ℂ) := by norm_num
  have hPL : arcPt a ρ₁ L = ((-(1/2) : ℝ) : ℂ) := by
    rw [hLpi, hcast]
    simpa only [arcPt] using hA1
  -- Step 6: transfer back to the complex orbit.
  have hiter : ∀ m, (eqU a)^[m] z = arcPt a ρ₁ (θm m) := by
    intro m
    induction m with
    | zero => rw [hθm_zero]; simpa only [arcPt, Function.iterate_zero_apply] using hzθ
    | succ m ih =>
        rw [Function.iterate_succ_apply', ih]
        exact hUm m
  have hconv : Tendsto (fun m : ℕ => arcPt a ρ₁ (θm m)) atTop (nhds ((-(1/2) : ℝ) : ℂ)) := by
    have h1 : Tendsto (fun m : ℕ => arcPt a ρ₁ (θm m)) atTop (nhds (arcPt a ρ₁ L)) :=
      (arcPt_continuousAt hC L).tendsto.comp hlim
    rwa [hPL] at h1
  have hfun : (fun m : ℕ => (eqU a)^[m] z) = fun m : ℕ => arcPt a ρ₁ (θm m) := funext hiter
  rw [hfun]
  exact hconv

end Work.EQ
