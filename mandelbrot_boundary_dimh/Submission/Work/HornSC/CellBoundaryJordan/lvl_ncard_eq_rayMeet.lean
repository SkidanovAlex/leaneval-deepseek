import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour_range
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour_injective
import Submission.Work.HornSC.CellBoundaryJordan.grid_crossing_defs

/-!
# Counting the ray crossings of a simple closed grid cycle

Let `u` be a `k`-periodic unit-step lattice walk whose vertices `u 0, …, u (k-1)` are pairwise
distinct (`k ≥ 3`), so that the polygonal tour `tour u k : ℝ → ℂ` is a *simple* closed curve: it is
injective on `[0,1)` (`tourOn_injective`). Let `a ∉ cycleSet k u` and `1 + iε ≠ 0`.

Give `(tour u k t - a)/(1 + iε)` an argument function `Θ`, i.e. assume the polar decomposition

`(tour u k t - a)/(1 + iε) = ‖(tour u k t - a)/(1 + iε)‖ · exp(i Θ t)`.

The main result is that the level set of `Θ` (the parameters at which the point lies on the ray
`a + ℝ_{>0}(1 + iε)`) is in bijection with the set `rayMeet k u a ε` of *ray parameters* at which
that ray meets the cycle. The bijection sends `t` to `‖(tour u k t - a)/(1 + iε)‖`; injectivity is
exactly the simplicity of the tour, surjectivity is `cycleSet ⊆ tourOn '' [0,1]`.

Consequently the level set is finite as soon as the crossing set is, and the two cardinalities
coincide:

`(lvlSetIco Θ).ncard = (rayMeet k u a ε).Finite.toFinset.card`.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

/-- The ray parameter of the point `tour u k t`, as seen from `a` in the direction `1 + iε`.
That is, `tour u k t = a + rayNorm u k a ε t • (1 + iε)` whenever `Θ t` is a multiple of `2π`. -/
noncomputable def rayNorm (u : ℕ → ℤ × ℤ) (k : ℕ) (a : ℂ) (ε : ℝ) (t : ℝ) : ℝ :=
  ‖(tour u k t - a) / (⟨1, ε⟩ : ℂ)‖

lemma rayNorm_eq (u : ℕ → ℤ × ℤ) (k : ℕ) (a : ℂ) (ε : ℝ) (t : ℝ) :
    rayNorm u k a ε t = ‖(tour u k t - a) / (⟨1, ε⟩ : ℂ)‖ := rfl

/-- `exp (i θ) = 1` exactly for the real multiples of `2π`. -/
lemma exp_I_eq_one_iff {θ : ℝ} :
    Complex.exp ((θ : ℂ) * Complex.I) = 1 ↔ ∃ n : ℤ, θ = (n : ℝ) * (2 * Real.pi) := by
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hI : Complex.I * (-Complex.I) = 1 := by rw [mul_neg, Complex.I_mul_I]; ring
    have h2 : (θ : ℂ) = (n : ℂ) * (2 * (Real.pi : ℂ)) := by
      calc (θ : ℂ) = (θ : ℂ) * Complex.I * (-Complex.I) := by rw [mul_assoc, hI, mul_one]
        _ = ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (-Complex.I) := by rw [hn]
        _ = (n : ℂ) * (2 * (Real.pi : ℂ)) := by rw [mul_assoc, mul_assoc, hI, mul_one]
    refine ⟨n, ?_⟩
    exact_mod_cast h2
  · rintro ⟨n, h⟩
    refine ⟨n, ?_⟩
    rw [h]; push_cast; ring

/-- Every point of the cycle is visited by the tour at a parameter in `[0,1)`. -/
lemma exists_tour_eq_of_mem_cycleSet {k : ℕ} (hk0 : 0 < k) (u : ℕ → ℤ × ℤ)
    (hper : ∀ i, u (i + k) = u i) {z : ℂ} (hz : z ∈ cycleSet k u) :
    ∃ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 ∧ tour u k t = z := by
  obtain ⟨t, ht, htz⟩ := cycleSet_subset_tourOn_range hk0 u hz
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · exact ⟨t, ⟨ht.1, hlt⟩, by rw [tour_eq_tourOn u ht.1 hlt, htz]⟩
  · refine ⟨0, ⟨le_refl 0, by norm_num⟩, ?_⟩
    have h0 : tourOn u k 0 = tourOn u k 1 := by
      rw [tourOn_zero, tourOn_one, show u k = u 0 from by simpa using hper 0]
    rw [heq] at htz
    rw [tour_eq_tourOn u le_rfl (by norm_num : (0 : ℝ) < 1), h0, htz]

theorem lvl_ncard_eq_rayMeet {k : ℕ} (hk : 3 ≤ k) (u : ℕ → ℤ × ℤ)
    (hper : ∀ i, u (i + k) = u i)
    (hinj : ∀ i j, i < k → j < k → u i = u j → i = j)
    (hstep : ∀ i, i < k → IsUnitAdj (u i) (u (i + 1)))
    {a : ℂ} {ε : ℝ} (hε : 0 < ε) (ha : a ∉ cycleSet k u)
    {Θ : ℝ → ℝ}
    (hΘrep : ∀ t : ℝ, (tour u k t - a) / (⟨1, ε⟩ : ℂ) =
      ((‖(tour u k t - a) / (⟨1, ε⟩ : ℂ)‖ : ℝ) : ℂ) * Complex.exp ((Θ t : ℂ) * Complex.I))
    (hfin : (rayMeet k u a ε).Finite) :
    (lvlSetIco Θ).Finite ∧ (lvlSetIco Θ).ncard = hfin.toFinset.card := by
  have hk0 : 0 < k := by omega
  have hdir : (⟨1, ε⟩ : ℂ) ≠ 0 := by
    intro h
    have h2 : (⟨1, ε⟩ : ℂ).re = (0 : ℂ).re := by rw [h]
    simp at h2
  -- the ray parameter of a level point is a ray crossing
  have key1 : ∀ t, t ∈ lvlSetIco Θ → rayNorm u k a ε t ∈ rayMeet k u a ε := by
    intro t ht
    rw [mem_lvlSetIco] at ht
    obtain ⟨htIco, n, hn⟩ := ht
    have hexp : Complex.exp ((Θ t : ℂ) * Complex.I) = 1 := exp_I_eq_one_iff.mpr ⟨n, hn⟩
    have hft : (tour u k t - a) / (⟨1, ε⟩ : ℂ) = ((rayNorm u k a ε t : ℝ) : ℂ) := by
      have h := hΘrep t
      rw [hexp, mul_one] at h
      exact h
    have hmul : tour u k t - a = ((rayNorm u k a ε t : ℝ) : ℂ) * (⟨1, ε⟩ : ℂ) :=
      (div_eq_iff hdir).mp hft
    have htour : tour u k t = a + ((rayNorm u k a ε t : ℝ) : ℂ) * (⟨1, ε⟩ : ℂ) := by
      rw [← hmul]; ring
    rw [mem_rayMeet]
    refine ⟨?_, ?_⟩
    · have hnonneg : 0 ≤ rayNorm u k a ε t := by rw [rayNorm_eq]; exact norm_nonneg _
      rcases eq_or_lt_of_le hnonneg with h | h
      · exfalso
        have hz : ((rayNorm u k a ε t : ℝ) : ℂ) = 0 := by rw [← h]; simp
        have hmem : a + ((rayNorm u k a ε t : ℝ) : ℂ) * (⟨1, ε⟩ : ℂ) ∈ cycleSet k u := by
          rw [← htour]; exact tour_mem_cycleSet hk0 u t
        rw [hz, zero_mul, add_zero] at hmem
        exact ha hmem
      · exact h
    · rw [← htour]; exact tour_mem_cycleSet hk0 u t
  -- every ray crossing arises from exactly one level point
  have key2 : ∀ s ∈ rayMeet k u a ε, ∃ t ∈ lvlSetIco Θ, rayNorm u k a ε t = s := by
    intro s hs
    rw [mem_rayMeet] at hs
    obtain ⟨hs0, hsme⟩ := hs
    obtain ⟨t, htIco, ht⟩ := exists_tour_eq_of_mem_cycleSet hk0 u hper hsme
    have hdiv : (tour u k t - a) / (⟨1, ε⟩ : ℂ) = (s : ℂ) := by
      rw [show tour u k t - a = (s : ℂ) * (⟨1, ε⟩ : ℂ) from by rw [ht]; ring]
      exact mul_div_cancel_right₀ _ hdir
    have hφs : rayNorm u k a ε t = s := by
      rw [rayNorm_eq, hdiv]
      simp [abs_of_pos hs0]
    have hexp : Complex.exp ((Θ t : ℂ) * Complex.I) = 1 := by
      have key : (tour u k t - a) / (⟨1, ε⟩ : ℂ) =
          ((rayNorm u k a ε t : ℝ) : ℂ) * Complex.exp ((Θ t : ℂ) * Complex.I) := by
        rw [rayNorm_eq]; exact hΘrep t
      have h1 : ((s : ℂ)) = ((s : ℂ)) * Complex.exp ((Θ t : ℂ) * Complex.I) := by
        calc (s : ℂ) = (tour u k t - a) / (⟨1, ε⟩ : ℂ) := hdiv.symm
          _ = ((rayNorm u k a ε t : ℝ) : ℂ) * Complex.exp ((Θ t : ℂ) * Complex.I) := key
          _ = ((s : ℝ) : ℂ) * Complex.exp ((Θ t : ℂ) * Complex.I) := by rw [hφs]
      have hsne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs0)
      have h2 : (s : ℂ) * 1 = (s : ℂ) * Complex.exp ((Θ t : ℂ) * Complex.I) := by
        rw [mul_one]; exact h1
      exact (mul_left_cancel₀ hsne h2).symm
    exact ⟨t, by rw [mem_lvlSetIco]; exact ⟨htIco, exp_I_eq_one_iff.mp hexp⟩, hφs⟩
  -- `rayNorm` is injective on the level set, by simplicity of the tour
  have key3 : (lvlSetIco Θ).InjOn (fun t => rayNorm u k a ε t) := by
    intro t1 ht1 t2 ht2 hφ
    have hφ' : rayNorm u k a ε t1 = rayNorm u k a ε t2 := hφ
    rw [mem_lvlSetIco] at ht1 ht2
    obtain ⟨ht1Ico, hn1⟩ := ht1
    obtain ⟨ht2Ico, hn2⟩ := ht2
    have hft1 : (tour u k t1 - a) / (⟨1, ε⟩ : ℂ) = ((rayNorm u k a ε t1 : ℝ) : ℂ) := by
      have h := hΘrep t1
      rw [exp_I_eq_one_iff.mpr hn1, mul_one] at h
      exact h
    have hft2 : (tour u k t2 - a) / (⟨1, ε⟩ : ℂ) = ((rayNorm u k a ε t2 : ℝ) : ℂ) := by
      have h := hΘrep t2
      rw [exp_I_eq_one_iff.mpr hn2, mul_one] at h
      exact h
    have htour : tour u k t1 = tour u k t2 := by
      have h1 : tour u k t1 - a = tour u k t2 - a := by
        have e1 : tour u k t1 - a = ((rayNorm u k a ε t1 : ℝ) : ℂ) * (⟨1, ε⟩ : ℂ) :=
          (div_eq_iff hdir).mp hft1
        have e2 : tour u k t2 - a = ((rayNorm u k a ε t2 : ℝ) : ℂ) * (⟨1, ε⟩ : ℂ) :=
          (div_eq_iff hdir).mp hft2
        rw [e1, e2, hφ']
      have h2 := congrArg (fun z => z + a) h1
      simpa using h2
    have hOn : tourOn u k t1 = tourOn u k t2 := by
      rw [← tour_eq_tourOn u ht1Ico.1 ht1Ico.2, ← tour_eq_tourOn u ht2Ico.1 ht2Ico.2, htour]
    rcases tourOn_injective hk u hper hinj hstep t1 t2 ht1Ico.1 (le_of_lt ht1Ico.2) ht2Ico.1
      (le_of_lt ht2Ico.2) hOn with h | h | h
    · exact h
    · exact absurd h.2 (by linarith [ht2Ico.2])
    · exact absurd h.1 (by linarith [ht1Ico.2])
  have himage : (fun t => rayNorm u k a ε t) '' (lvlSetIco Θ) = rayMeet k u a ε := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact key1 t ht
    · intro hs
      obtain ⟨t, ht, hts⟩ := key2 s hs
      exact ⟨t, ht, hts⟩
  have hfinimg : ((fun t => rayNorm u k a ε t) '' (lvlSetIco Θ)).Finite := by
    rw [himage]; exact hfin
  have hfinlvl : (lvlSetIco Θ).Finite := hfinimg.of_finite_image key3
  refine ⟨hfinlvl, ?_⟩
  have hcard : (lvlSetIco Θ).ncard = (rayMeet k u a ε).ncard := by
    have h := key3.ncard_image
    rw [himage] at h
    exact h.symm
  rw [hcard]
  exact Set.ncard_eq_toFinset_card _ hfin

end Work.HornSC.CellBoundaryJordan
