import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.Setup
import Submission.Work.Parab.inversion.deriv_ne_zero_of_injOn
import Submission.Work.Parab.invOrbit.far_small
import Submission.Work.Parab.invOrbit.abel_chain_deriv
import Submission.Work.Parab.invOrbit.backward_chain

namespace Work.Parab.invOrbit

open Filter Metric Set

/-- **Lemma 5.1 (inverse orbits), sector form.**

`φ` is holomorphic on the open set `Dφ`, defined on Shishikura's repelling sector
`QLeft ξ = {π/3 < |arg (w + ξ)|}`, and `QLeft ξ` is closed under `w ↦ w - 1`; the Abel equation
`φ (w + 1) = f₀ (φ w)` holds whenever `w + 1 ∈ Dφ` (and `w + 1 ∈ Dφ ↔ φ w ∈ D₀`).  Assume
further that `φ` is injective on `QLeft ξ`, that the small values of `φ` on `QLeft ξ` come from
far away points (`hpre`), that `f₀` is injective near `0`, and that `φ` has the inverse-branch
asymptotics `φ*₀(w) = w + a log(-w) + b + o(1)` on `QLeft ξ`.

Then every backward orbit `z` of `f₀` in `D₀` converging to `0` whose tail lies in `φ '' QLeft ξ`
is the backward orbit of a single point `w ∈ Dφ`; and `deriv φ w ≠ 0` provided `deriv f₀` does
not vanish along `z`.

Compared with `Work.Parab.invOrbit.inv_orbit`, injectivity of `φ` is only assumed on the sector
`QLeft ξ` (global injectivity on `Dφ` is false when `D₀` is large, where `Dφ = ℂ`), and the
non-vanishing of `deriv φ w` is obtained by propagating `deriv f₀ ≠ 0` along the Abel chain
instead of from global injectivity.  The asymptotic and `hpre` are used to identify the two
preimages of `z j` that occur (the one-step translate `φ (u j - 1)` is far out, hence small by
the asymptotic, so it lands in the ball where `f₀` is injective). -/
theorem inv_orbit_QLeft {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {φ : ℂ → ℂ} {Dφ : Set ℂ} {ξ : ℝ}
    (hDφ_open : IsOpen Dφ)
    (hQopen : IsOpen (MandelDim.QLeft ξ))
    (hQ : MandelDim.QLeft ξ ⊆ Dφ)
    (hQsub : ∀ w ∈ MandelDim.QLeft ξ, w - 1 ∈ MandelDim.QLeft ξ)
    (hleft : ∀ w ∈ Dφ, w - 1 ∈ Dφ)
    (hsucc : ∀ w ∈ Dφ, (w + 1 ∈ Dφ ↔ φ w ∈ D₀))
    (habel : ∀ w ∈ Dφ, w + 1 ∈ Dφ → φ (w + 1) = f₀ (φ w))
    (hpre : ∀ B : ℝ, ∃ δ : ℝ, 0 < δ ∧
      ∀ u ∈ MandelDim.QLeft ξ, ‖φ u‖ < δ → B ≤ ‖u‖)
    (hφdiff : DifferentiableOn ℂ φ Dφ)
    (hinjQ : Set.InjOn φ (MandelDim.QLeft ξ))
    (hfinj : ∃ ρ : ℝ, 0 < ρ ∧ Set.InjOn f₀ (Metric.ball 0 ρ))
    (hasymp : ∃ a b : ℂ, ∀ ε > 0, ∃ R : ℝ, ∀ w ∈ MandelDim.QLeft ξ, R < ‖w‖ →
        ‖MandelDim.tau0 (φ w) - (w + a * Complex.log (-w) + b)‖ < ε)
    {z : ℕ → ℂ} (hzD : ∀ j : ℕ, 1 ≤ j → z j ∈ D₀)
    (hz : ∀ j : ℕ, f₀ (z (j + 1)) = z j)
    (hlim : Filter.Tendsto z Filter.atTop (nhds 0))
    (hj₀ : ∃ j₀ : ℕ, 1 ≤ j₀ ∧ ∀ j : ℕ, j₀ ≤ j → ∃ u ∈ MandelDim.QLeft ξ, φ u = z j) :
    ∃ w ∈ Dφ, (∀ j : ℕ, w - (j : ℂ) ∈ Dφ ∧ φ (w - (j : ℂ)) = z j) ∧
      ((∀ j : ℕ, 1 ≤ j → deriv f₀ (z j) ≠ 0) → deriv φ w ≠ 0) := by
  classical
  obtain ⟨ρ, hρpos, hfinjρ⟩ := hfinj
  obtain ⟨a, b, hasymp'⟩ := hasymp
  -- `φ` takes small values at far out points of the sector
  obtain ⟨Rsm, hRsm⟩ := far_small (S := MandelDim.QLeft ξ) (a := a) (b := b) hρpos hasymp'
  -- points of the sector with a small `φ`-value are far out
  obtain ⟨δ, hδpos, hδ⟩ := hpre (Rsm + 2)
  -- the backward orbit is eventually small
  have hevδ : ∀ᶠ j : ℕ in Filter.atTop, ‖z j‖ < δ := by
    have h1 : Filter.Tendsto (fun j : ℕ => ‖z j‖) Filter.atTop (nhds ‖(0 : ℂ)‖) := hlim.norm
    rw [norm_zero] at h1
    exact h1.eventually ((isOpen_lt continuous_id continuous_const).mem_nhds hδpos)
  have hevρ : ∀ᶠ j : ℕ in Filter.atTop, ‖z j‖ < ρ := by
    have h1 : Filter.Tendsto (fun j : ℕ => ‖z j‖) Filter.atTop (nhds ‖(0 : ℂ)‖) := hlim.norm
    rw [norm_zero] at h1
    exact h1.eventually ((isOpen_lt continuous_id continuous_const).mem_nhds hρpos)
  obtain ⟨Nδ, hNδ⟩ := Filter.eventually_atTop.mp hevδ
  obtain ⟨Nρ, hNρ⟩ := Filter.eventually_atTop.mp hevρ
  obtain ⟨j₀, _hj₀pos, hj₀prop⟩ := hj₀
  -- threshold from which on the tail argument applies
  set j₁ : ℕ := max j₀ (max Nδ Nρ) with hj₁def
  have hthr : ∀ j : ℕ, j₁ ≤ j → j₀ ≤ j ∧ Nδ ≤ j ∧ Nρ ≤ j := by
    intro j hj
    refine ⟨le_trans (le_max_left _ _) hj, ?_, ?_⟩
    · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hj
    · exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hj
  -- points of the sector above the tail of `z`
  have hex : ∀ j : ℕ, ∃ u : ℂ, j₁ ≤ j → u ∈ MandelDim.QLeft ξ ∧ φ u = z j := by
    intro j
    by_cases h : j₁ ≤ j
    · obtain ⟨u, huQ, huφ⟩ := hj₀prop j (hthr j h).1
      exact ⟨u, fun _ => ⟨huQ, huφ⟩⟩
    · exact ⟨0, fun hh => absurd hh h⟩
  choose u hu using hex
  -- consecutive points of the chosen tail differ by `1`
  have hchain : ∀ j : ℕ, j₁ ≤ j → u (j + 1) = u j - 1 := by
    intro j hj
    have hj1 : j₁ ≤ j + 1 := le_trans hj (Nat.le_succ j)
    have hujQ : u j ∈ MandelDim.QLeft ξ := (hu j hj).1
    have hujφ : φ (u j) = z j := (hu j hj).2
    have huj1Q : u (j + 1) ∈ MandelDim.QLeft ξ := (hu (j + 1) hj1).1
    have huj1φ : φ (u (j + 1)) = z (j + 1) := (hu (j + 1) hj1).2
    -- `u j` is far out
    have hfar2 : Rsm + 2 ≤ ‖u j‖ :=
      hδ (u j) hujQ (by rw [hujφ]; exact hNδ j (hthr j hj).2.1)
    -- the translate one step to the left
    have hvQ : u j - 1 ∈ MandelDim.QLeft ξ := hQsub (u j) hujQ
    have hvD : u j - 1 ∈ Dφ := hQ hvQ
    have hupD : (u j - 1) + 1 ∈ Dφ := by
      have h : (u j - 1) + 1 = u j := by ring
      rw [h]; exact hQ hujQ
    -- the Abel equation at `u j - 1`, and the asymptotic bound for its value
    have habel_v : f₀ (φ (u j - 1)) = z j := by
      have h := habel (u j - 1) hvD hupD
      rw [show (u j - 1) + 1 = u j from by ring, hujφ] at h
      exact h.symm
    have hsmall : ‖φ (u j - 1)‖ < ρ := by
      refine hRsm (u j - 1) hvQ ?_
      have h1 : ‖u j‖ - ‖(1 : ℂ)‖ ≤ ‖u j - 1‖ := norm_sub_norm_le (u j) 1
      simp only [norm_one] at h1
      linarith
    have hzsmall : ‖z (j + 1)‖ < ρ := hNρ (j + 1) (hthr (j + 1) hj1).2.2
    -- both are preimages of `z j` inside the ball where `f₀` is injective
    have hp_eq : φ (u j - 1) = z (j + 1) := by
      refine hfinjρ ?_ ?_ ?_
      · rw [Metric.mem_ball, dist_eq_norm]
        simpa using hsmall
      · rw [Metric.mem_ball, dist_eq_norm]
        simpa using hzsmall
      · rw [habel_v, hz j]
    exact hinjQ huj1Q hvQ (by rw [huj1φ, hp_eq])
  -- the point `w` whose backward orbit realizes the chain
  set w : ℂ := u j₁ + (j₁ : ℂ) with hwdef
  have hup : ∀ n : ℕ, j₁ ≤ n → w - (n : ℂ) = u n := by
    intro n hn
    refine Nat.le_induction (P := fun n _ => w - (n : ℂ) = u n) ?_ ?_ n hn
    · rw [hwdef]; ring
    · intro n hn ih
      have h := hchain n hn
      rw [h, ← ih]
      push_cast
      ring
  have hupper : ∀ j : ℕ, j₁ ≤ j → w - (j : ℂ) ∈ Dφ ∧ φ (w - (j : ℂ)) = z j := by
    intro j hj
    rw [hup j hj]
    exact ⟨hQ (hu j hj).1, (hu j hj).2⟩
  -- and downward by the Abel equation
  have hlower : ∀ j : ℕ, j ≤ j₁ → w - (j : ℂ) ∈ Dφ ∧ φ (w - (j : ℂ)) = z j := by
    refine backward_chain hsucc habel hzD hz (w := w) (k := j₁) ?_ ?_
    · exact (hupper j₁ le_rfl).1
    · exact (hupper j₁ le_rfl).2
  have hall : ∀ j : ℕ, w - (j : ℂ) ∈ Dφ ∧ φ (w - (j : ℂ)) = z j := by
    intro j
    rcases le_total j j₁ with h | h
    · exact hlower j h
    · exact hupper j h
  have hwD : w ∈ Dφ := by
    have h := (hall 0).1
    simpa using h
  refine ⟨w, hwD, hall, fun hder0 => ?_⟩
  -- `deriv φ ≠ 0` at the far end of the chain
  have hdu : deriv φ (u j₁) ≠ 0 :=
    Work.Parab.inversion.deriv_ne_zero_of_injOn (Work.Parab.isOpen_QLeft ξ)
      (hφdiff.mono hQ) hinjQ (u j₁) (hu j₁ le_rfl).1
  -- and it propagates along the chain
  have hkey : deriv φ (u j₁ + (j₁ : ℂ)) ≠ 0 := by
    refine abel_chain_deriv (f₀ := f₀) (φ := φ) (U := Dφ) hDφ_open hφdiff habel ?_ hdu ?_
    · intro k hk
      have e : u j₁ + (k : ℂ) = w - ((j₁ - k : ℕ) : ℂ) := by
        rw [Nat.cast_sub hk, hwdef]
        ring
      rw [e]
      exact (hall (j₁ - k)).1
    · intro k hk
      have hkj : k ≤ j₁ := le_of_lt hk
      have e : u j₁ + (k : ℂ) = w - ((j₁ - k : ℕ) : ℂ) := by
        rw [Nat.cast_sub hkj, hwdef]
        ring
      rw [e, (hall (j₁ - k)).2]
      exact hder0 (j₁ - k) (by omega)
  simpa [hwdef] using hkey

end Work.Parab.invOrbit
