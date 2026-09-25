import Mathlib
import Submission.Work.LT.lr_sound_defs

namespace Work.LT

open Classical

variable {G : Type} [Group G] {Δ : ℕ}

/-- At a type-`(0,0)` vertex the local view of `f` is `f` itself. -/
lemma lrView_zero_zero (A B : Fin Δ → G) (g : G) (f : G × Fin Δ × Fin Δ → ZMod 2)
    (i j : Fin Δ) : lrView A B 0 0 g f (i, j) = f (g, i, j) := by
  simp [lrView, LinearMap.funLeft_apply, lrSq_eq_base, lrBase_zero_zero]

/-- The word `lrState W` reads off `W` at the type-`(0,0)` vertices.  If `W` agrees with the true
local view of `f` at every type-`(0,0)` vertex outside `rejectSet ∪ V1`, then `lrState W` differs
from `f` only on the `Δ²` squares based at such a vertex; this gives the claimed counting bound. -/
lemma hammingDist_lrState_le {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) (f : G × Fin Δ × Fin Δ → ZMod 2)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2))
    (V1 : Finset (Fin 2 × Fin 2 × G))
    (hW : ∀ v : Fin 2 × Fin 2 × G, v ∉ Work.LT.rejectSet A B CA CB f → v ∉ V1 →
      W v.1 v.2.1 v.2.2 = Work.LT.lrView A B v.1 v.2.1 v.2.2 f) :
    hammingDist f (Work.LT.lrState W) ≤
      Δ * Δ * ((Work.LT.rejectSet A B CA CB f).card + V1.card) := by
  classical
  set R : Finset (Fin 2 × Fin 2 × G) := rejectSet A B CA CB f ∪ V1 with hR
  set Bad : Finset (G × Fin Δ × Fin Δ) :=
    Finset.univ.filter (fun p => f p ≠ lrState W p) with hBad
  have hdist : hammingDist f (lrState W) = Bad.card := by
    simp [hammingDist, hBad]
  -- A differing square `p` has its base vertex `(0,0,p.1)` in `R`.
  have hmemR : ∀ p ∈ Bad, ((0 : Fin 2), 0, p.1) ∈ R := by
    intro p hp
    rw [hR]
    by_contra hcon
    simp only [Finset.mem_union, not_or] at hcon
    have hWp := hW (0, 0, p.1) hcon.1 hcon.2
    have heq : lrState W p = f p := by
      rw [lrState, hWp, lrView_zero_zero]
    have hp' : f p ≠ lrState W p := by simpa [hBad] using hp
    exact hp' heq.symm
  -- `Bad` injects into `(R ∩ {type (0,0)}) × (Fin Δ × Fin Δ)`.
  let φ : G × Fin Δ × Fin Δ → (Fin 2 × Fin 2 × G) × (Fin Δ × Fin Δ) :=
    fun p => ((0, 0, p.1), p.2)
  have hφinj : Function.Injective φ := by
    intro p q hpq
    have h1 : p.1 = q.1 := by
      have := congrArg (fun x : (Fin 2 × Fin 2 × G) × (Fin Δ × Fin Δ) => x.1.2.2) hpq
      simpa [φ] using this
    have h2 : p.2 = q.2 := by
      have := congrArg (fun x : (Fin 2 × Fin 2 × G) × (Fin Δ × Fin Δ) => x.2) hpq
      simpa [φ] using this
    exact Prod.ext h1 h2
  have hsub : Finset.image φ Bad ⊆
      (R.filter (fun v : Fin 2 × Fin 2 × G => v.1 = 0 ∧ v.2.1 = 0)) ×ˢ
        (Finset.univ : Finset (Fin Δ × Fin Δ)) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [Finset.mem_filter]
    exact ⟨hmemR p hp, by simp [φ]⟩
  have himg : Bad.card = (Finset.image φ Bad).card :=
    (Finset.card_image_of_injective Bad hφinj).symm
  have hprod : ((R.filter (fun v : Fin 2 × Fin 2 × G => v.1 = 0 ∧ v.2.1 = 0)) ×ˢ
      (Finset.univ : Finset (Fin Δ × Fin Δ))).card =
      (R.filter (fun v : Fin 2 × Fin 2 × G => v.1 = 0 ∧ v.2.1 = 0)).card * (Δ * Δ) := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  have hR0card : (R.filter (fun v : Fin 2 × Fin 2 × G => v.1 = 0 ∧ v.2.1 = 0)).card ≤
      (rejectSet A B CA CB f).card + V1.card := by
    calc (R.filter (fun v : Fin 2 × Fin 2 × G => v.1 = 0 ∧ v.2.1 = 0)).card
        ≤ R.card := Finset.card_filter_le _ _
      _ = (rejectSet A B CA CB f ∪ V1).card := by rw [hR]
      _ ≤ (rejectSet A B CA CB f).card + V1.card := Finset.card_union_le _ _
  calc hammingDist f (lrState W) = Bad.card := hdist
    _ = (Finset.image φ Bad).card := himg
    _ ≤ ((R.filter (fun v : Fin 2 × Fin 2 × G => v.1 = 0 ∧ v.2.1 = 0)) ×ˢ
          (Finset.univ : Finset (Fin Δ × Fin Δ))).card := Finset.card_le_card hsub
    _ = (R.filter (fun v : Fin 2 × Fin 2 × G => v.1 = 0 ∧ v.2.1 = 0)).card * (Δ * Δ) := hprod
    _ ≤ ((rejectSet A B CA CB f).card + V1.card) * (Δ * Δ) := Nat.mul_le_mul_right _ hR0card
    _ = Δ * Δ * ((rejectSet A B CA CB f).card + V1.card) := Nat.mul_comm _ _

end Work.LT
