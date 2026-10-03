import Mathlib
import Submission.Work.Horn.deriv_phi_ne_zero_of_noncrit
import Submission.Work.Interfaces.HornParts

/-!
# `deriv φ w ≠ 0` for `w ∈ Bu ∪ Bl` with `φ w` off the forward critical orbit

The maximal Fatou coordinate `d.φ` of the parabolic germ `f₀` satisfies the functional equation
`φ (w + 1) = f₀ (φ w)`, hence `φ w = f₀^[j] (φ (w - j))` for every `j` as long as the backward
orbit stays in `Dφ`.  The hypothesis `d.φ w ∉ critOrbit f₀ c` therefore *forces* every point
`φ (w - j)`, `j ≥ 1`, to be off the critical point `c` (else `d.φ w = f₀^[j] c` would lie on the
forward critical orbit), while `T`-invariance of `Bu`, `Bl` (`hTopo`) keeps `φ (w - j)` inside the
immediate basin `B`, where `c` is the *unique* critical point.  So all the factors in the
chain-rule identity for `deriv d.φ` are non-zero, which is exactly the hypothesis of
`Work.Horn.deriv_phi_ne_zero_of_noncrit`.
-/

namespace Work.HornCov

/-- A `T`-invariant set is closed under backward integer translations. -/
lemma sub_nat_mem_of_isTInvariant {U : Set ℂ} (hU : MandelDim.IsTInvariant U) {w : ℂ}
    (hw : w ∈ U) : ∀ n : ℕ, w - (n : ℂ) ∈ U := by
  intro n
  induction n with
  | zero => simpa using hw
  | succ m ih =>
      refine (hU (w - ((m + 1 : ℕ) : ℂ))).mpr ?_
      rwa [show w - ((m + 1 : ℕ) : ℂ) + 1 = w - (m : ℂ) by push_cast; ring]

/-- Iterating the functional equation of the Fatou coordinate backwards:
`φ w = f₀^[j] (φ (w - j))`, as long as the whole backward orbit stays in `Dφ`. -/
lemma phi_sub_iterate {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {w : ℂ}
    (hD : ∀ i : ℕ, w - (i : ℂ) ∈ d.Dφ) (j : ℕ) :
    d.φ w = f₀^[j] (d.φ (w - (j : ℂ))) := by
  induction j with
  | zero => simp
  | succ m ih =>
      have h1 : w - ((m + 1 : ℕ) : ℂ) ∈ d.Dφ := hD (m + 1)
      have h2 : w - (m : ℂ) ∈ d.Dφ := hD m
      have harith : w - ((m + 1 : ℕ) : ℂ) + 1 = w - (m : ℂ) := by push_cast; ring
      have hstep : d.φ (w - (m : ℂ)) = f₀ (d.φ (w - ((m + 1 : ℕ) : ℂ))) := by
        have h := d.φ_abel (w - ((m + 1 : ℕ) : ℂ)) h1 (by rwa [harith])
        rwa [harith] at h
      rw [ih, hstep, Function.iterate_succ_apply]

theorem deriv_varphi_ne_zero_of_notMem_critOrbit {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}
    (hTopo : MandelDim.HornTopoStatement) (d : MandelDim.ParabData f₀ D₀)
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c)
    {w : ℂ} (hw : w ∈ MandelDim.BuOf d B ∪ MandelDim.BlOf d B)
    (hcrit : d.φ w ∉ MandelDim.critOrbit f₀ c) : deriv d.φ w ≠ 0 := by
  have himm : MandelDim.IsImmediateBasin f₀ D₀ B := hsetup.2.1
  -- the basin is contained in the domain of `f₀`
  have hBsubD : B ⊆ D₀ := by
    intro z hz
    obtain ⟨U, hU, hiter, -⟩ := himm.2.2.1 hz
    simpa using hiter 0 (mem_of_mem_nhds hU)
  -- uniqueness of the critical point in the basin
  have hcru : ∀ z ∈ B, deriv f₀ z = 0 → z = c := hsetup.2.2.2.2
  -- `T`-invariance of `Bu`, `Bl`
  obtain ⟨-, -, hBuT, hBlT, -, -, -⟩ := hTopo f₀ D₀ B c d hsetup
  -- Step 1: the whole backward orbit stays in `Bu ∪ Bl`, hence in `φ⁻¹(B)`
  have hshift : ∀ n : ℕ, w - (n : ℂ) ∈ MandelDim.BuOf d B ∪ MandelDim.BlOf d B := by
    intro n
    rcases hw with hw | hw
    · exact Or.inl (sub_nat_mem_of_isTInvariant hBuT hw n)
    · exact Or.inr (sub_nat_mem_of_isTInvariant hBlT hw n)
  have hBtil : ∀ n : ℕ, w - (n : ℂ) ∈ MandelDim.Btil d B := fun n =>
    (hshift n).elim (fun h => connectedComponentIn_subset _ _ h)
      (fun h => connectedComponentIn_subset _ _ h)
  have hDφ : ∀ n : ℕ, w - (n : ℂ) ∈ d.Dφ := fun n => (hBtil n).1
  have hφB : ∀ n : ℕ, d.φ (w - (n : ℂ)) ∈ B := fun n => (hBtil n).2
  -- Step 2: no point of the backward orbit of `φ w` is the critical point `c`
  have hne_c : ∀ j : ℕ, 1 ≤ j → d.φ (w - (j : ℂ)) ≠ c := by
    intro j hj hjc
    have hiter := phi_sub_iterate d hDφ j
    rw [hiter, hjc] at hcrit
    exact hcrit ⟨j, hj, rfl⟩
  -- Step 3: apply the chain-rule criterion `deriv_phi_ne_zero_of_noncrit`
  refine Work.Horn.deriv_phi_ne_zero_of_noncrit f₀ D₀ d (by simpa using hDφ 0) ?_ ?_
  · intro j _
    exact hBsubD (hφB j)
  · intro j hj h0
    exact hne_c j hj (hcru _ (hφB j) h0)

end Work.HornCov
