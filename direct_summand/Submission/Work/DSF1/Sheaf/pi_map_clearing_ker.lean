import Mathlib

namespace Work.DSF1.Sheaf

open CategoryTheory

lemma pi_map_clearing_ker {R : Type} [CommRing R] {β : Type} [Fintype β]
    (F F' : β → ModuleCat R) (φ : ∀ b, F b ⟶ F' b) (h : R)
    (hcomp : ∀ b (t : ↥(F b)), (φ b).hom t = 0 → ∃ k : ℕ, h ^ k • t = 0) :
    ∀ t : ↥(∏ᶜ F), (CategoryTheory.Limits.Pi.map φ).hom t = 0 →
      ∃ k : ℕ, h ^ k • t = 0 := by
  intro t ht
  -- Componentwise: `φ b` kills the `b`-th component of `t`.
  have key : ∀ b, (φ b).hom ((CategoryTheory.Limits.Pi.π F b).hom t) = 0 := by
    intro b
    have h1 := CategoryTheory.Limits.Pi.map_π φ b
    have h2 := congrArg (fun (f : ∏ᶜ F ⟶ F' b) => f.hom t) h1
    simp only [ConcreteCategory.comp_apply] at h2
    rw [ht, map_zero] at h2
    exact h2.symm
  have ex : ∀ b, ∃ k : ℕ, h ^ k • ((CategoryTheory.Limits.Pi.π F b).hom t) = 0 :=
    fun b => hcomp b _ (key b)
  choose k hk using ex
  -- A common exponent `∑ b, k b` clears every component.
  refine ⟨∑ b, k b, ?_⟩
  have hle : ∀ b, k b ≤ ∑ b, k b := by
    intro b
    exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ b)
  have hzero : ∀ b, (CategoryTheory.Limits.Pi.π F b).hom (h ^ (∑ b, k b) • t) = 0 := by
    intro b
    rw [LinearMap.map_smul]
    rw [← Nat.sub_add_cancel (hle b), pow_add, mul_smul, hk b, smul_zero]
  -- The projections jointly detect zero.
  have hfinal : h ^ (∑ b, k b) • t = 0 := by
    apply CategoryTheory.Limits.Concrete.Pi.map_ext (F := 𝟭 (ModuleCat R)) (f := F)
    intro i
    simp only [Functor.id_map]
    change (CategoryTheory.Limits.Pi.π F i).hom ((h ^ ∑ b, k b) • t) =
      (CategoryTheory.Limits.Pi.π F i).hom (0 : ↥(∏ᶜ F))
    rw [hzero i, map_zero]
  exact hfinal

end Work.DSF1.Sheaf
