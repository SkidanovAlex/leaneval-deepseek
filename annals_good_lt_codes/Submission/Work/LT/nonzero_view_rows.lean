import Mathlib
import Submission.Work.LT.Defs

namespace Work.LT

/-- The local view at a type-`00` vertex is simply the corresponding slice:
`(lrView A B 0 0 g w) (i, j) = w (g, i, j)`. -/
lemma lrView_zero_zero_apply {G : Type} [Group G] {Δ : ℕ} (A B : Fin Δ → G) (g : G)
    (w : G × Fin Δ × Fin Δ → ZMod 2) (i j : Fin Δ) :
    (lrView A B 0 0 g w) (i, j) = w (g, i, j) := by
  simp [lrView, LinearMap.funLeft_apply, lrSq]

/-- A type-`00` view of a word of the left-right Cayley code has all its columns in `CA`. -/
lemma column_mem_CA {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2))
    (f : G × Fin Δ × Fin Δ → ZMod 2) (hf : f ∈ lrCode A B CA CB) (g : G) (j : Fin Δ) :
    (fun i : Fin Δ => f (g, i, j)) ∈ CA := by
  have hview : lrView A B 0 0 g f ∈ tensorCode CA CB := by
    have h := hf
    simp only [lrCode, Submodule.mem_iInf] at h
    exact h (0 : Fin 2) (0 : Fin 2) g
  have h1 := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hview).2 j
  rw [Submodule.mem_comap] at h1
  convert h1 using 1
  funext i
  rw [LinearMap.funLeft_apply, lrView_zero_zero_apply]

/-- **Nonzero local view has `≥ δ0 Δ` nonzero rows**, as a real-valued cardinality bound: if
`f ≠ 0` lies in the left-right Cayley code and nonzero words of `CA` have weight `≥ δ0 Δ`, then
there is a vertex `g₀` whose local (type-00) view has at least `δ0 Δ` rows `i` which are nonzero
(so the slice `(g, j) ↦ f (g, i, j)` is a nonzero word of `CB`). -/
theorem nonzero_view_rows {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) (δ0 : ℝ)
    (hdA : ∀ x ∈ CA, x ≠ 0 → δ0 * Δ ≤ hammingNorm x)
    (f : G × Fin Δ × Fin Δ → ZMod 2) (hf : f ∈ lrCode A B CA CB) (hfne : f ≠ 0) :
    ∃ g₀ : G, δ0 * (Δ : ℝ) ≤
      ((Finset.univ.filter (fun i : Fin Δ => (fun j : Fin Δ => f (g₀, i, j)) ≠ 0)).card : ℝ) := by
  classical
  -- pick a nonzero coordinate of `f`
  obtain ⟨g₀, i₀, j₀, hp⟩ : ∃ (g : G) (i j : Fin Δ), f (g, i, j) ≠ 0 := by
    by_contra h
    push Not at h
    exact hfne (funext fun p => h p.1 p.2.1 p.2.2)
  refine ⟨g₀, ?_⟩
  -- the column `j₀` of the type-`00` view at `g₀` is a nonzero word of `CA`
  have hcol : (fun i : Fin Δ => f (g₀, i, j₀)) ∈ CA := column_mem_CA A B CA CB f hf g₀ j₀
  have hcolne : (fun i : Fin Δ => f (g₀, i, j₀)) ≠ 0 := by
    intro h
    exact hp (by simpa using congrFun h i₀)
  have hbound := hdA _ hcol hcolne
  -- its support is contained in the set of nonzero rows
  refine le_trans hbound ?_
  apply Nat.cast_le.mpr
  rw [hammingNorm]
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  intro h0
  exact hi (by simpa using congrFun h0 j₀)

end Work.LT
