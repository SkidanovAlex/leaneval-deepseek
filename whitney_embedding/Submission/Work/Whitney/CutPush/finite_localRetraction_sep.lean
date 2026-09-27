import Mathlib
import Submission.Work.Isotopy.localRetraction_at
import Submission.Work.Whitney.CutPush.box_separation_arc

/-!
# Finitely many separated local retractions along a smooth arc family

The parametrised local inverse `Work.Isotopy.exists_localInverse_param` gives, at every point
`(lam, x)` of the trail box `[0,1] × [0,1]`, open boxes `O`, `U`, `B`, a *smooth* local inverse `par`
with `par s (Φ s y) = y` for `s ∈ O`, `y ∈ U`, `Φ s y ∈ B`, together with the smoothness of `par` on
`O × B`.  Feeding each point's data to the box separation `box_separation_arc` shrinks `O` and `B` so
that, in addition, `Φ s x ∈ B` with `x ∈ [0,1]` forces `x ∈ U`.  Compactness of the trail box then
yields *finitely many* such separated boxes covering the trail.

The smoothness of `par` on the box is what makes the patched velocity field
`(lam, y) ↦ ∑ j, ψ j lam y • vel lam (par j lam y)` smooth: it is used only where `ψ j ≠ 0`, which
is inside the box.
-/

open scoped Manifold ContDiff
open Topology Set MeasureTheory

namespace Work.Whitney.CutPush

/-- **Finitely many separated local retractions of an arc family**, smooth on their boxes. -/
theorem exists_finite_localRetraction_sep {m : ℕ}
    (Φ : ℝ → ℝ → EuclideanSpace ℝ (Fin m))
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => Φ p.1 p.2))
    (hinj : ∀ lam : ℝ, Set.InjOn (Φ lam) (Set.Icc (0 : ℝ) 1))
    (hreg : ∀ lam t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → fderiv ℝ (Φ lam) t 1 ≠ 0) :
    ∃ (ι : Type) (_ : Fintype ι) (O U : ι → Set ℝ)
      (B : ι → Set (EuclideanSpace ℝ (Fin m))) (par : ι → ℝ → EuclideanSpace ℝ (Fin m) → ℝ),
      (∀ j, IsOpen (O j)) ∧ (∀ j, IsOpen (U j)) ∧ (∀ j, IsOpen (B j)) ∧
      (∀ j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin m) => par j p.1 p.2) (O j ×ˢ B j)) ∧
      (∀ j s y, s ∈ O j → y ∈ U j → Φ s y ∈ B j → par j s (Φ s y) = y) ∧
      (∀ j s x, s ∈ O j → x ∈ Set.Icc (0 : ℝ) 1 → Φ s x ∈ B j → x ∈ U j) ∧
      (∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        ∃ j, lam ∈ O j ∧ x ∈ U j ∧ Φ lam x ∈ B j) := by
  classical
  have hpt : ∀ p : ↥(Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1),
      ∃ (O U : Set ℝ) (B : Set (EuclideanSpace ℝ (Fin m)))
        (par : ℝ → EuclideanSpace ℝ (Fin m) → ℝ),
        IsOpen O ∧ (p : ℝ × ℝ).1 ∈ O ∧ IsOpen U ∧ (p : ℝ × ℝ).2 ∈ U ∧ IsOpen B ∧
        Φ (p : ℝ × ℝ).1 (p : ℝ × ℝ).2 ∈ B ∧
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : ℝ × EuclideanSpace ℝ (Fin m) => par q.1 q.2) (O ×ˢ B) ∧
        (∀ s ∈ O, ∀ y ∈ U, Φ s y ∈ B → par s (Φ s y) = y) ∧
        (∀ s ∈ O, ∀ x ∈ Set.Icc (0 : ℝ) 1, Φ s x ∈ B → x ∈ U) := by
    intro p
    obtain ⟨O₀, U₀, W₀, h₀, hO₀, hmemO, hU₀, hmemU, hW₀, hmemW, _hV, hsm₀, _hGU, hretr₀⟩ :=
      Work.Isotopy.exists_localInverse_param (Function.uncurry Φ) Set.univ isOpen_univ
        (p : ℝ × ℝ).1 (p : ℝ × ℝ).2 (mem_univ _) (hΦ.contDiffOn (s := Set.univ))
        Set.univ isOpen_univ (mem_univ _)
        (Work.Isotopy.injective_partial_uncurry Φ hΦ (p : ℝ × ℝ).1 (p : ℝ × ℝ).2
          (hreg _ _ p.2.2))
    obtain ⟨O, B, hO, hmemO', hOsub, hB, hmemB, hBsub, _hbd, hsep⟩ :=
      box_separation_arc Φ hΦ.continuous hinj (p : ℝ × ℝ).1 (p : ℝ × ℝ).2
        p.2.2 U₀ hU₀ hmemU O₀ hO₀ hmemO W₀ hW₀ hmemW
    refine ⟨O, U₀, B, h₀, hO, hmemO', hU₀, hmemU, hB, hmemB, ?_, ?_, hsep⟩
    · exact hsm₀.mono (Set.prod_mono hOsub hBsub)
    · intro s hs y hy _hBy
      exact hretr₀ s (hOsub hs) y hy
  choose O U B par hO hmemO hU hmemU hB hmemB hsm hretr hsep using hpt
  set S : ↥(Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) → Set (ℝ × ℝ) :=
    fun p => {q : ℝ × ℝ | q.1 ∈ O p ∧ q.2 ∈ U p ∧ Φ q.1 q.2 ∈ B p} with hS
  have hSopen : ∀ p, IsOpen (S p) := by
    intro p
    have h1 : IsOpen {q : ℝ × ℝ | q.1 ∈ O p} := (hO p).preimage continuous_fst
    have h2 : IsOpen {q : ℝ × ℝ | q.2 ∈ U p} := (hU p).preimage continuous_snd
    have h3 : IsOpen {q : ℝ × ℝ | Function.uncurry Φ q ∈ B p} := (hB p).preimage hΦ.continuous
    exact h1.inter (h2.inter h3)
  have hcover : (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) ⊆ ⋃ p, S p := by
    rintro q hq
    exact Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hmemO ⟨q, hq⟩, hmemU ⟨q, hq⟩, hmemB ⟨q, hq⟩⟩
  obtain ⟨t, ht⟩ := (isCompact_Icc.prod isCompact_Icc).elim_finite_subcover S hSopen hcover
  refine ⟨↥t, inferInstance, fun j => O j, fun j => U j, fun j => B j, fun j => par j,
    fun j => hO _, fun j => hU _, fun j => hB _, fun j => hsm _, ?_, ?_, ?_⟩
  · intro j s y hs hy hBy; exact hretr j s hs y hy hBy
  · intro j s x hs hx hBx; exact hsep j s hs x hx hBx
  · intro lam hlam x hx
    have hq : (lam, x) ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 := ⟨hlam, hx⟩
    have hmem : (lam, x) ∈ ⋃ j ∈ t, S j := ht hq
    rcases Set.mem_iUnion.mp hmem with ⟨j, hj⟩
    rcases Set.mem_iUnion.mp hj with ⟨hjt, hqS⟩
    exact ⟨⟨j, hjt⟩, hqS.1, hqS.2.1, hqS.2.2⟩

end Work.Whitney.CutPush
