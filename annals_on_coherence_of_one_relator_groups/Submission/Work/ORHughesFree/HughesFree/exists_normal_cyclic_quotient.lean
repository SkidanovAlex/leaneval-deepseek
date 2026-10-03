import Mathlib
import Submission.Work.ORHughesFree.HughesFree

namespace Work.ORHughesFree.HughesFree

theorem exists_normal_cyclic_quotient {G : Type} [Group G] [Work.ORHughesFree.LocallyIndicable G]
    (H : Subgroup G) (hH : H.FG) (hHne : H ≠ ⊥) :
    ∃ (N : Subgroup H) (_ : N.Normal) (t : H),
      N ≠ ⊤ ∧ (⊤ : Subgroup H) = N ⊔ Subgroup.closure ({t} : Set H) ∧
      ∀ k : ℤ, k ≠ 0 → t ^ k ∉ N := by
  obtain ⟨f, hf⟩ := Work.ORHughesFree.LocallyIndicable.surj_z H hH hHne
  obtain ⟨t, ht⟩ := hf (Multiplicative.ofAdd (1 : ℤ))
  have hpow : ∀ m : ℤ, (Multiplicative.ofAdd (1 : ℤ)) ^ m = Multiplicative.ofAdd m := by
    intro m
    rw [← ofAdd_zsmul]
    simp
  refine ⟨f.ker, MonoidHom.normal_ker f, t, ?_, ?_, ?_⟩
  · intro h
    have hmem : t ∈ f.ker := by rw [h]; exact Subgroup.mem_top t
    have h1 : f t = 1 := MonoidHom.mem_ker.mp hmem
    rw [ht] at h1
    exact one_ne_zero (ofAdd_eq_one.mp h1)
  · symm
    rw [eq_top_iff]
    intro x _
    set n : ℤ := Multiplicative.toAdd (f x) with hn
    have hx : f x = Multiplicative.ofAdd n := by
      rw [hn]
      exact (ofAdd_toAdd (f x)).symm
    have hxN : x * t ^ (-n) ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_zpow, ht, hpow (-n), hx, ← ofAdd_add]
      simp
    have htN : t ^ n ∈ Subgroup.closure ({t} : Set H) :=
      Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) n
    have h1 : x * t ^ (-n) ∈ f.ker ⊔ Subgroup.closure ({t} : Set H) :=
      Subgroup.mem_sup_left hxN
    have h2 : t ^ n ∈ f.ker ⊔ Subgroup.closure ({t} : Set H) :=
      Subgroup.mem_sup_right htN
    have hmem : (x * t ^ (-n)) * t ^ n ∈ f.ker ⊔ Subgroup.closure ({t} : Set H) :=
      Subgroup.mul_mem _ h1 h2
    have heq : (x * t ^ (-n)) * t ^ n = x := by group
    rwa [heq] at hmem
  · intro k hk hmem
    have h1 : f (t ^ k) = 1 := MonoidHom.mem_ker.mp hmem
    rw [map_zpow, ht, hpow k] at h1
    exact hk (ofAdd_eq_one.mp h1)

end Work.ORHughesFree.HughesFree
