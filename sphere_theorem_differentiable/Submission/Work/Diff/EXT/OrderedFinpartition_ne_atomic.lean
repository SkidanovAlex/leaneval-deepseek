import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- A strictly monotone self-map of `Fin n` is the identity.

Indeed, a strictly monotone map `f : Fin n → Fin n` satisfies `i ≤ f i` for all `i`
(`StrictMono.id_le`), and being injective on a finite type of the same cardinality it is a
bijection, hence permutes `Fin n`; comparing sums gives `f i = i` for all `i`. -/
lemma strictMono_fin_eq_id {n : ℕ} {f : Fin n → Fin n} (hf : StrictMono f) : f = id := by
  have hinj : Function.Injective f := hf.injective
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, rfl⟩
  have hsum : ∑ i : Fin n, (f i : ℕ) = ∑ i : Fin n, (i : ℕ) := by
    simpa [Equiv.ofBijective_apply] using
      (Equiv.ofBijective f hbij).sum_comp (fun i : Fin n => (i : ℕ))
  have hle : ∀ i : Fin n, (i : ℕ) ≤ (f i : ℕ) := fun i => hf.id_le i
  have hiff := Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := fun i : Fin n => (i : ℕ)) (g := fun i : Fin n => (f i : ℕ)) (fun i _ => hle i)
  funext i
  exact Fin.ext (hiff.mp hsum.symm i (Finset.mem_univ i)).symm

/-- An ordered finpartition of `Fin n` which is not the atomic (all singletons) one has a part of
size at least two. -/
theorem OrderedFinpartition_ne_atomic {n : ℕ} (c : OrderedFinpartition n)
    (hc : c ≠ OrderedFinpartition.atomic n) : ∃ j, 2 ≤ c.partSize j := by
  by_contra h
  simp only [not_exists, not_le] at h
  have hps1 : ∀ m, c.partSize m = 1 := fun m => by
    have h1 := c.partSize_pos m
    have h2 := h m
    omega
  have hlen : c.length = n := by
    have hsum1 : (∑ m : Fin c.length, c.partSize m) =
        Fintype.card ((m : Fin c.length) × Fin (c.partSize m)) := by
      rw [Fintype.card_sigma]; simp
    have hsum2 : Fintype.card ((m : Fin c.length) × Fin (c.partSize m)) = n := by
      rw [Fintype.card_congr c.equivSigma, Fintype.card_fin]
    have hsum : (∑ m : Fin c.length, c.partSize m) = n := hsum1.trans hsum2
    have hl' : (∑ m : Fin c.length, c.partSize m) = c.length := by simp [hps1]
    omega
  apply hc
  obtain ⟨l, ps, hp, e, he, hps, hd, hcv⟩ := c
  have hlen'' : n = l := hlen.symm
  subst hlen''
  change ∀ j : Fin n, ps j < 2 at h
  have hps1' : ∀ m : Fin n, ps m = 1 := fun m => by
    have h2 := h m; have h3 := hp m; omega
  have hid : (fun m : Fin n => e m ⟨ps m - 1, Nat.sub_one_lt_of_lt (hp m)⟩) = id :=
    strictMono_fin_eq_id hps
  have hemb : ∀ (m : Fin n) (i : Fin (ps m)), e m i = m := by
    intro m i
    have h1 : e m i = e m ⟨ps m - 1, Nat.sub_one_lt_of_lt (hp m)⟩ := by
      apply congrArg (e m)
      apply Fin.ext
      show (i : ℕ) = ps m - 1
      have := i.isLt; have := hps1' m; omega
    rw [h1]
    exact congrFun hid m
  refine OrderedFinpartition.ext rfl ?_ ?_
  · change ps ≍ (OrderedFinpartition.atomic n).partSize
    exact (Fin.heq_fun_iff rfl).mpr (fun i => by simpa using hps1' i)
  · change e ≍ (OrderedFinpartition.atomic n).emb
    apply Function.hfunext rfl
    intro m m' hmm
    apply (Fin.heq_fun_iff (hps1' m)).mpr
    intro i
    rw [hemb m i]
    exact eq_of_heq hmm

end Work.Diff.EXT
