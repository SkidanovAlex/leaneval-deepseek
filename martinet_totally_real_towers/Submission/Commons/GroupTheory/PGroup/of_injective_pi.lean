import Mathlib.GroupTheory.PGroup

namespace Commons.GroupTheory.PGroup

/-- A finite product of `p`-groups is a `p`-group. -/
private lemma of_pi {p : ℕ} {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, Group (G i)]
    (hG : ∀ i, IsPGroup p (G i)) : IsPGroup p (∀ i, G i) := by
  classical
  rw [isPGroup_iff_pow_pow_eq_one]
  intro x
  choose k hk using fun i => hG i (x i)
  refine ⟨Finset.univ.sup k, ?_⟩
  funext i
  have hle : k i ≤ Finset.univ.sup k := Finset.le_sup (Finset.mem_univ i)
  calc
    x i ^ p ^ Finset.univ.sup k
        = x i ^ (p ^ k i * p ^ (Finset.univ.sup k - k i)) := by
          congr 1
          rw [← pow_add, Nat.add_sub_cancel' hle]
    _ = (x i ^ p ^ k i) ^ p ^ (Finset.univ.sup k - k i) := by rw [pow_mul]
    _ = 1 := by rw [hk i, one_pow]

/-- A group that injects into a finite product of `p`-groups is a `p`-group. -/
lemma of_injective_pi {p : ℕ} {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, Group (G i)]
    {H : Type*} [Group H] (f : H →* ∀ i, G i) (hf : Function.Injective f)
    (hG : ∀ i, IsPGroup p (G i)) : IsPGroup p H := by
  exact (of_pi hG).of_injective f hf

end Commons.GroupTheory.PGroup