import Mathlib
import Submission.Work.SSGRoute.Step4CokerData
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.twistLayer
import Submission.Work.SSGRoute.step4_conjugate_vanish
import Submission.Work.SSGRoute.shafarevich_existence
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open _root_.SSGRoute
open Work.CohomologicalShrinking

/-! ## Auxiliary facts for the old-ramification clause of Step 4

The clause `hxold` of Step 4 of Schmidt–Wingberg (the paper's `x_℘ = 0` for the primes of *old*
ramification, SW p. 30) is derived here from the corresponding clause of the `y`-datum
(`Step4YData`, clause 7) and the local clauses `hxsplit`/`hxnot` of the class `x`.

The mathematics.  At a place `B` that is conjugate to a place `A ∈ D.S` of the chosen set and at
which there is an inertia element `σ ∈ I_B ∩ G_K` with `D.phi σ ≠ 1` (`φ` = level-`τ` solution,
so `B` is a place of old ramification), the `y`-datum is *zero* on the whole decomposition group
`D_B`.  The condition "`I_B ∩ G_K` contains an element with nontrivial `φ`-image" is invariant
under conjugating the place (`D.phi` is a homomorphism and `G_K` is normal), so it holds at every
`G_ℚ`-conjugate place of `B`; hence every summand of the formal corestriction
`∑_s s • y ((sec s)⁻¹ δ sec s)` at such a place vanishes.  At a place `A ∈ S` that splits
completely in `K` the decomposition group `D_A ≤ G_K` acts trivially, so `hxsplit` turns into
`x δ = ∑_s s • y (…) = 0` on `D_A`, i.e. `x` is a coboundary there; at a place that does not
split `hxnot` gives the coboundary directly.  Coboundaries transfer between conjugate places, so
the coboundary property reaches the arbitrary place `B`. -/

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ QBar}
  [FiniteDimensional ℚ K] [Normal ℚ K] {n i j : ℕ}

/-- The hypothesis "`I_B ∩ G_K` contains an element whose `φ`-image is nontrivial" is invariant
under conjugating the place `B`. -/
theorem step4_inertia_phi_conj (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ) (D : Step4CokerData p K n i j)
    (B : ValuationSubring QBar) (g : GalQ)
    (h : ∃ σ, IsInertia ℚ B σ ∧ σ ∈ K.fixingSubgroup ∧ D.phi σ ≠ 1) :
    ∃ σ, IsInertia ℚ (g • B) σ ∧ σ ∈ K.fixingSubgroup ∧ D.phi σ ≠ 1 := by
  obtain ⟨σ, hI, hK, hphi⟩ := h
  refine ⟨g * σ * g⁻¹, (isInertia_conj B g σ).mpr hI, step4_conj_mem_fixingSubgroup K hK, ?_⟩
  intro hconj
  have h2 : D.phi (g * σ * g⁻¹) = D.phi g * D.phi σ * (D.phi g)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [h2] at hconj
  refine hphi ?_
  calc D.phi σ = (D.phi g)⁻¹ * (D.phi g * D.phi σ * (D.phi g)⁻¹) * D.phi g := by group
    _ = (D.phi g)⁻¹ * 1 * D.phi g := by rw [hconj]
    _ = 1 := by group

/-- **Every summand of the formal corestriction vanishes at a place of old ramification.**  If `B`
is a finite place conjugate to a place of `S` and `y` vanishes on `D_B` (the old-ramification
clause of the `y`-datum), then all summands `s • y ((sec s)⁻¹ δ sec s)`, `δ ∈ D_B`, vanish. -/
theorem step4_sum_smul_y_eq_zero_of_inertia_phi (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ)
    (D : Step4CokerData p K n i j) (y : GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hy7 : ∀ B : ValuationSubring QBar, IsFinPlace ℚ B →
      (∃ A ∈ D.S, IsConjPlace ℚ A B) →
      (∃ σ, IsInertia ℚ B σ ∧ σ ∈ K.fixingSubgroup ∧ D.phi σ ≠ 1) →
      ∀ σ ∈ decomp ℚ B, y σ = 0)
    (B : ValuationSubring QBar) (hB : IsFinPlace ℚ B)
    (hc : ∃ A ∈ D.S, IsConjPlace ℚ A B)
    (hI : ∃ σ, IsInertia ℚ B σ ∧ σ ∈ K.fixingSubgroup ∧ D.phi σ ≠ 1)
    (δ : GalQ) (hδ : δ ∈ decomp ℚ B) :
    (∑ s : K ≃ₐ[ℚ] K, s • y ((D.sec s)⁻¹ * δ * D.sec s)) = 0 := by
  refine Finset.sum_eq_zero (fun s _ => ?_)
  obtain ⟨A₀, hA₀S, hA₀conj⟩ := hc
  obtain ⟨σ₀, hσ₀I, hσ₀K, hσ₀phi⟩ := hI
  have hBs : IsFinPlace ℚ ((D.sec s)⁻¹ • B) :=
    (isFinPlace_smul_iff B (D.sec s)⁻¹).mpr hB
  have hcs : ∃ A ∈ D.S, IsConjPlace ℚ A ((D.sec s)⁻¹ • B) :=
    ⟨A₀, hA₀S, isConjPlace_smul hA₀conj (D.sec s)⁻¹⟩
  have hIs : ∃ σ, IsInertia ℚ ((D.sec s)⁻¹ • B) σ ∧ σ ∈ K.fixingSubgroup ∧ D.phi σ ≠ 1 := by
    have h := step4_inertia_phi_conj p K n i j D B (D.sec s)⁻¹ ⟨σ₀, hσ₀I, hσ₀K, hσ₀phi⟩
    simpa using h
  have hD : (D.sec s)⁻¹ * δ * D.sec s ∈ decomp ℚ ((D.sec s)⁻¹ • B) := by
    rw [decomp_conj]
    exact Subgroup.mem_map.mpr ⟨δ, hδ, by simp⟩
  rw [hy7 _ hBs hcs hIs _ hD, smul_zero]

/-- The corestriction sum of the `y`-datum vanishes on the decomposition group of a **split** place
`A ∈ D.S` all of whose conjugates are places of old ramification. -/
theorem step4_corestriction_sum_eq_zero_of_split_old (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ)
    (D : Step4CokerData p K n i j) (y : GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hy7 : ∀ B : ValuationSubring QBar, IsFinPlace ℚ B →
      (∃ A ∈ D.S, IsConjPlace ℚ A B) →
      (∃ σ, IsInertia ℚ B σ ∧ σ ∈ K.fixingSubgroup ∧ D.phi σ ≠ 1) →
      ∀ σ ∈ decomp ℚ B, y σ = 0)
    (A : ValuationSubring QBar) (hA : A ∈ D.S) (hsplit : IsSplitIn ℚ K A)
    (hIA : ∃ σ, IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ D.phi σ ≠ 1)
    (δ : GalQ) (hδ : δ ∈ decomp ℚ A) :
    (∑ s : K ≃ₐ[ℚ] K, s • y ((D.sec s)⁻¹ * δ * D.sec s)) = 0 :=
  step4_sum_smul_y_eq_zero_of_inertia_phi p K n i j D y hy7 A (D.hSfin A hA)
    ⟨A, hA, isConjPlace_refl A⟩ hIA δ hδ

theorem step4_x_old_ramification (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ) (D : Work.SSGRoute.Step4CokerData p K n i j)
    (y : SSGRoute.GalQ → Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) n i j)
    (hY : Work.SSGRoute.Step4YData p K n i j D y)
    (x : SSGRoute.GalQ → Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) n i j)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (Work.SSGRoute.restrict K σ) • x τ)
    (hxsplit : ∀ A ∈ D.S, SSGRoute.IsSplitIn ℚ K A →
      SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A)
        (fun δ => x δ - ∑ s : K ≃ₐ[ℚ] K, s • y ((D.sec s)⁻¹ * δ * D.sec s)))
    (hxnot : ∀ A ∈ D.S, ¬ SSGRoute.IsSplitIn ℚ K A →
      SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A) x) :
    ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∃ A ∈ D.S, SSGRoute.IsConjPlace ℚ A B) →
      (∃ σ, SSGRoute.IsInertia ℚ B σ ∧ σ ∈ K.fixingSubgroup ∧ D.phi σ ≠ 1) →
      SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ B) x := by
  intro B hBfin hconj hI
  -- extract the old-ramification clause of the `y`-datum
  obtain ⟨hy1, hy2, hy3, hy4, hy5, hy6, hy7, hy8⟩ := hY
  -- `x` is a `1`-cocycle for the `restrict K`-action
  have hxcoc : SSGRoute.IsCocycleOn (Work.SSGRoute.restrict K) ⊤ x := fun σ _ τ _ => hxmul σ τ
  obtain ⟨A, hAS, hAB⟩ := hconj
  obtain ⟨τ, hτ⟩ := hAB
  -- the old-ramification condition at `A`
  have hIA : ∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ D.phi σ ≠ 1 := by
    have h' := step4_inertia_phi_conj p K n i j D B τ⁻¹ hI
    have hs : τ⁻¹ • B = A := by rw [← hτ, inv_smul_smul]
    rwa [hs] at h'
  -- `x` is a coboundary on the decomposition group of `A`
  have hcobA : SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A) x := by
    by_cases hsplit : SSGRoute.IsSplitIn ℚ K A
    · -- `A` splits in `K`: `D_A ≤ G_K` acts trivially, so `hxsplit` forces `x = 0` on `D_A`
      refine step4_coboundary_of_eq_zero (fun δ hδ => ?_)
      obtain ⟨m, hm⟩ := hxsplit A hAS hsplit
      have hact : (Work.SSGRoute.restrict K) δ = 1 :=
        (step4_restrict_eq_one_iff K δ).mpr (hsplit hδ)
      have hsum : (∑ s : K ≃ₐ[ℚ] K, s • y ((D.sec s)⁻¹ * δ * D.sec s)) = 0 :=
        step4_corestriction_sum_eq_zero_of_split_old p K n i j D y hy7 A hAS hsplit hIA δ hδ
      have h1 : x δ - (∑ s : K ≃ₐ[ℚ] K, s • y ((D.sec s)⁻¹ * δ * D.sec s))
          = (Work.SSGRoute.restrict K) δ • m - m := hm δ hδ
      rw [hact, one_smul, sub_self, hsum, sub_zero] at h1
      exact h1
    · -- `A` does not split in `K`: `hxnot` gives the coboundary directly
      exact hxnot A hAS hsplit
  -- coboundaries transfer between conjugate places
  have h := isCoboundaryOn_map_conj (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A) τ x
    hxcoc hcobA
  rw [← decomp_conj A τ, hτ] at h
  exact h

end Work.SSGRoute
