import Mathlib
import Submission.Work.Smooth.Morse.Defs

namespace Work.Smooth.Morse.Flow

/-- A Lipschitz vector field `W` on the parameter plane which is invariant under the period
lattice `2πℤ²` generates an equivariant flow: `Φ u (q + (2πk, 2πl)) = Φ u q + (2πk, 2πl)`.

This is uniqueness of solutions of the ODE `ẏ = W y`: the translated trajectory
`s ↦ Φ s (q + (2πk, 2πl)) - (2πk, 2πl)` has the same initial condition and, by periodicity of
`W`, the same right-hand side as `s ↦ Φ s q`. -/
theorem flow_equivariant_of_periodic (W : ℝ × ℝ → ℝ × ℝ) {K : NNReal} (hW : LipschitzWith K W) (hper : ∀ (q : ℝ × ℝ) (k l : ℤ), W (q.1 + (k : ℝ) * (2 * Real.pi), q.2 + (l : ℝ) * (2 * Real.pi)) = W q) (Φ : ℝ × (ℝ × ℝ) → ℝ × ℝ) {T : ℝ} (hΦ0 : ∀ q : ℝ × ℝ, Φ (0, q) = q) (hΦ : ∀ (q : ℝ × ℝ) (u : ℝ), u ∈ Set.Icc 0 T → HasDerivWithinAt (fun s : ℝ => Φ (s, q)) (W (Φ (u, q))) (Set.Icc 0 T) u) : ∀ (q : ℝ × ℝ) (u : ℝ) (k l : ℤ), u ∈ Set.Icc 0 T → Φ (u, (q.1 + (k : ℝ) * (2 * Real.pi), q.2 + (l : ℝ) * (2 * Real.pi))) = ((Φ (u, q)).1 + (k : ℝ) * (2 * Real.pi), (Φ (u, q)).2 + (l : ℝ) * (2 * Real.pi)) := by
  intro q u k l hu
  -- the period lattice vector in additive notation
  set c : ℝ × ℝ := ((k : ℝ) * (2 * Real.pi), (l : ℝ) * (2 * Real.pi)) with hc
  -- the shifted base point is `q + c`
  have hshift : (q.1 + (k : ℝ) * (2 * Real.pi), q.2 + (l : ℝ) * (2 * Real.pi)) = q + c := by
    ext <;> simp [hc]
  -- periodicity of `W`, in additive form
  have hper_add : ∀ p : ℝ × ℝ, W (p + c) = W p := by
    intro p
    rw [show p + c = (p.1 + (k : ℝ) * (2 * Real.pi), p.2 + (l : ℝ) * (2 * Real.pi))
      from by ext <;> simp [hc]]
    exact hper p k l
  -- `Icc 0 T` is a neighbourhood of `t` within `Ici t` for `t ∈ Ico 0 T`
  have hIcc_nhds : ∀ t ∈ Set.Ico (0 : ℝ) T, Set.Icc (0 : ℝ) T ∈ nhdsWithin t (Set.Ici t) := by
    intro t ht
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Iio T, isOpen_Iio.mem_nhds ht.2, fun y hy => ⟨le_trans ht.1 hy.2, le_of_lt hy.1⟩⟩
  -- uniqueness of the ODE `ẏ = W y` with initial condition `q`
  have huniq := ODE_solution_unique_of_mem_Icc_right
    (v := fun _ : ℝ => W) (s := fun _ : ℝ => Set.univ) (K := K) (a := (0 : ℝ)) (b := T)
    (f := fun s : ℝ => Φ (s, q)) (g := (fun s : ℝ => Φ (s, q + c)) - (fun _ : ℝ => c))
    (fun t _ => hW.lipschitzOnWith)
    (fun t ht => (hΦ q t ht).continuousWithinAt)
    (fun t ht => (hΦ q t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hIcc_nhds t ht))
    (fun t _ => Set.mem_univ _)
    (fun t ht => ((hΦ (q + c) t ht).continuousWithinAt).sub continuousWithinAt_const)
    (fun t ht => by
      have hd := (hΦ (q + c) t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hIcc_nhds t ht)
      have hsub := hd.sub (hasDerivWithinAt_const t (Set.Ici t) c)
      rw [sub_zero] at hsub
      have hp : W (Φ (t, q + c)) = W (Φ (t, q + c) - c) := by
        have h := hper_add (Φ (t, q + c) - c)
        rwa [sub_add_cancel] at h
      rw [hp] at hsub
      exact hsub)
    (fun t _ => Set.mem_univ _)
    (by
      show Φ (0, q) = Φ (0, q + c) - c
      rw [hΦ0 q, hΦ0 (q + c)]
      abel)
  have huu : Φ (u, q) = Φ (u, q + c) - c := huniq hu
  rw [hshift]
  rw [eq_add_of_sub_eq huu.symm]
  ext <;> simp [hc]

end Work.Smooth.Morse.Flow
