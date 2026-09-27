import Mathlib
import Submission.Work.Isotopy.exists_local_retraction
import Submission.Work.Isotopy.exists_global_retraction
import Submission.Work.Isotopy.exists_box_separation

set_option linter.unusedVariables false

namespace Work.Isotopy

open scoped Manifold ContDiff
open Topology Set Function

/-- **Parametrised local retractions of a smooth family of injective immersions.**

Let `M` be a compact smooth `n`-manifold and let `Φ : ℝ → M → ℝ^N` be a smooth family of maps
into `ℝ^N` whose every time slice is an injective immersion.  Then, over any compact parameter
interval `[a,b]`, the family can be covered by finitely many "boxes" `O_j × B_j`, each carrying a
globally smooth map `ρ_j : ℝ → ℝ^N → M` which is a left inverse of `Φ` on that box. -/
theorem exists_family_retraction {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M]
    (Φ : ℝ → M → EuclideanSpace ℝ (Fin N))
    (hΦ : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 N) ∞ (Function.uncurry Φ))
    (himm : ∀ s x, Function.Injective (mfderiv (𝓡 n) (𝓡 N) (Φ s) x))
    (hinj : ∀ s, Function.Injective (Φ s)) (a b : ℝ) (hab : a ≤ b) :
    ∃ (ι : Type) (_ : Fintype ι) (O : ι → Set ℝ) (B : ι → Set (EuclideanSpace ℝ (Fin N)))
      (ρ : ι → ℝ → EuclideanSpace ℝ (Fin N) → M),
      (∀ j, IsOpen (O j)) ∧ (∀ j, IsOpen (B j)) ∧ (∀ j, Bornology.IsBounded (B j)) ∧
      (∀ j, ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓡 n) ∞ (Function.uncurry (ρ j))) ∧
      (∀ j s x, s ∈ O j → Φ s x ∈ B j → ρ j s (Φ s x) = x) ∧
      (∀ s ∈ Set.Icc a b, ∀ x, ∃ j, s ∈ O j ∧ Φ s x ∈ B j) := by
  classical
  -- For every point `p = (s₀, x₀)` of the parameter/fibre space we record a box `Obox p × Bbox p`
  -- together with a *globally* smooth retraction `ρbox p` which inverts `Φ` on that box.
  have key : ∀ p : ℝ × M,
      ∃ (O : Set ℝ) (B : Set (EuclideanSpace ℝ (Fin N))) (ρ : ℝ → EuclideanSpace ℝ (Fin N) → M),
        IsOpen O ∧ p.1 ∈ O ∧ IsOpen B ∧ Φ p.1 p.2 ∈ B ∧ Bornology.IsBounded B ∧
        ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓡 n) ∞ (Function.uncurry ρ) ∧
        (∀ s ∈ O, ∀ x, Φ s x ∈ B → ρ s (Φ s x) = x) := by
    rintro ⟨s₀, x₀⟩
    -- a local left inverse of the family near `(s₀, x₀)`,
    obtain ⟨O₁, V, W, ρ₁, hO₁, hs₁, hV, hx₀, hW, hw, hρ₁, hret⟩ :=
      exists_local_retraction Φ hΦ himm s₀ x₀
    -- shrunk to a box on which `Φ s x ∈ B` forces `x ∈ V`,
    obtain ⟨O₂, B, hO₂, hs₂, hO₂sub, hB, hwB, hBsub, hBbd, hsep⟩ :=
      exists_box_separation (n := n) Φ hΦ.continuous hinj s₀ x₀ V hV hx₀ O₁ hO₁ hs₁ W hW hw
    -- and then globalised.
    have hρ₂ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓡 n) ∞ (Function.uncurry ρ₁) (O₂ ×ˢ B) :=
      hρ₁.mono (Set.prod_mono hO₂sub hBsub)
    obtain ⟨O₃, W₃, ρ₃, hO₃, hs₃, hO₃sub, hW₃, hw₃, hW₃sub, hW₃bd, hρ₃, hagree⟩ :=
      exists_global_retraction O₂ B hO₂ hB s₀ (Φ s₀ x₀) hs₂ hwB ρ₁ hρ₂
    refine ⟨O₃, W₃, ρ₃, hO₃, hs₃, hW₃, hw₃, hW₃bd, hρ₃, ?_⟩
    intro s hs x hx
    have hs₂' : s ∈ O₂ := hO₃sub hs
    have hxV : x ∈ V := hsep s hs₂' x (hW₃sub hx)
    have h1 : ρ₃ s (Φ s x) = ρ₁ s (Φ s x) := hagree s hs (Φ s x) hx
    have h2 : ρ₁ s (Φ s x) = x := hret s (hO₂sub hs₂') x hxV
    exact h1.trans h2
  let Obox : ℝ × M → Set ℝ := fun p => Classical.choose (key p)
  let Bbox : ℝ × M → Set (EuclideanSpace ℝ (Fin N)) :=
    fun p => Classical.choose (Classical.choose_spec (key p))
  let ρbox : ℝ × M → ℝ → EuclideanSpace ℝ (Fin N) → M :=
    fun p => Classical.choose (Classical.choose_spec (Classical.choose_spec (key p)))
  have hbox : ∀ p, IsOpen (Obox p) ∧ p.1 ∈ Obox p ∧ IsOpen (Bbox p) ∧
      Φ p.1 p.2 ∈ Bbox p ∧ Bornology.IsBounded (Bbox p) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓡 n) ∞ (Function.uncurry (ρbox p)) ∧
      (∀ s ∈ Obox p, ∀ x, Φ s x ∈ Bbox p → ρbox p s (Φ s x) = x) :=
    fun p => Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (key p)))
  -- the trail of the family over the interval `[a,b]` is compact,
  set K := (fun q : ℝ × M => (q.1, Φ q.1 q.2)) '' (Set.Icc a b ×ˢ (Set.univ : Set M)) with hKdef
  have hK : IsCompact K :=
    (isCompact_Icc.prod isCompact_univ).image (continuous_fst.prodMk hΦ.continuous)
  have hcov : K ⊆ ⋃ p : ℝ × M, Obox p ×ˢ Bbox p := by
    rintro ⟨s, y⟩ ⟨q, hq, hqeq⟩
    obtain ⟨rfl, rfl⟩ := hqeq
    exact mem_iUnion.mpr ⟨q, (hbox q).2.1, (hbox q).2.2.2.1⟩
  -- so finitely many boxes suffice.
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun p : ℝ × M => Obox p ×ˢ Bbox p)
    (fun p => ((hbox p).1).prod ((hbox p).2.2.1)) hcov
  let φ := Finset.equivFin t
  refine ⟨Fin t.card, inferInstance,
    (fun i => Obox ((φ.symm i).val)), (fun i => Bbox ((φ.symm i).val)),
    (fun i => ρbox ((φ.symm i).val)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact (hbox _).1
  · intro i; exact (hbox _).2.2.1
  · intro i; exact (hbox _).2.2.2.2.1
  · intro i; exact (hbox _).2.2.2.2.2.1
  · intro i s x hs hx; exact (hbox _).2.2.2.2.2.2 s hs x hx
  · intro s hs x
    have hp : (s, Φ s x) ∈ K := ⟨(s, x), ⟨hs, trivial⟩, rfl⟩
    obtain ⟨p, hpt, hpbox⟩ := mem_iUnion₂.mp (ht hp)
    refine ⟨φ ⟨p, hpt⟩, ?_, ?_⟩
    · show s ∈ Obox ((φ.symm (φ ⟨p, hpt⟩)).val)
      rw [Equiv.symm_apply_apply]
      exact hpbox.1
    · show Φ s x ∈ Bbox ((φ.symm (φ ⟨p, hpt⟩)).val)
      rw [Equiv.symm_apply_apply]
      exact hpbox.2

end Work.Isotopy
