import Mathlib
import Submission.Work.Tate.Basic
import Submission.Work.Tate.map_augmentation_eq_of_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

/-- If an injective `G`-equivariant additive map `f : A →+ B` sends `a` into the augmentation
submodule of `B`, then `a` itself lies in the augmentation submodule of `A`.

Indeed, surjectivity of `f` gives `(augmentation G A).map f = augmentation G B`, so `f a = f a'`
for some `a' ∈ augmentation G A`, and injectivity yields `a = a'`. -/
theorem mem_augmentation_of_map_mem {G : Type*} {A : Type*} {B : Type*} [Group G]
    [AddCommGroup A] [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B]
    (f : A →+ B) (hf : ∀ (γ : G) (a : A), f (γ • a) = γ • f a) (hfb : Function.Bijective f)
    {a : A} (ha : f a ∈ augmentation G B) : a ∈ augmentation G A := by
  have hmap : (augmentation G A).map f = augmentation G B :=
    map_augmentation_eq_of_surjective f hf hfb.2
  rw [← hmap] at ha
  obtain ⟨a', ha', hfa'⟩ := AddSubgroup.mem_map.mp ha
  exact (hfb.1 hfa') ▸ ha'

theorem Hm1Map_bijective {G : Type*} {A : Type*} {B : Type*} [Group G] [AddCommGroup A]
    [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B] [Fintype G] (f : A →+ B)
    (hf : ∀ (γ : G) (a : A), f (γ • a) = γ • f a) (hfb : Function.Bijective f) :
    Function.Bijective (Work.Tate.Hm1Map G A B f hf) := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Hm1π_surjective (G := G) (A := A) x
    obtain ⟨b, rfl⟩ := Hm1π_surjective (G := G) (A := A) y
    rw [Hm1Map_Hm1π, Hm1Map_Hm1π] at hxy
    rw [Hm1π_eq_iff] at hxy ⊢
    change ((mapKer G A B f hf a - mapKer G A B f hf b : (norm G B).ker) : B)
      ∈ augmentation G B at hxy
    change ((a - b : (norm G A).ker) : A) ∈ augmentation G A
    have hval : ((mapKer G A B f hf a - mapKer G A B f hf b : (norm G B).ker) : B)
        = f ((a - b : (norm G A).ker) : A) := by
      simp only [AddSubgroup.coe_sub, mapKer_apply, map_sub]
    rw [hval] at hxy
    exact mem_augmentation_of_map_mem f hf hfb hxy
  · intro y
    obtain ⟨b, rfl⟩ := Hm1π_surjective (G := G) (A := B) y
    obtain ⟨a, ha⟩ := hfb.2 (b : B)
    have hka : a ∈ (norm G A).ker := by
      rw [AddMonoidHom.mem_ker]
      apply hfb.1
      rw [map_zero, ← norm_map f hf a, ha]
      exact AddMonoidHom.mem_ker.mp b.2
    refine ⟨Hm1π G A ⟨a, hka⟩, ?_⟩
    rw [Hm1Map_Hm1π]
    have hker : mapKer G A B f hf ⟨a, hka⟩ = b := by
      apply Subtype.ext
      rw [mapKer_apply]
      exact ha
    rw [hker]

end Work.Tate
