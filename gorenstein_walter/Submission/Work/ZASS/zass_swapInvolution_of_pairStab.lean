import Mathlib

namespace Work.ZASS

/-- If `t` is an involution fixing the two distinct points `a ≠ b` of a 2-pretransitive action
in which no nonidentity element fixes more than two points, and `X` has a third point `c`
distinct from `a` and `b`, then some conjugate of `t` (by an element sending `c` to `a` and
`t • c` to `b`) is an involution interchanging `a` and `b`. -/
theorem zass_swapInvolution_of_pairStab {G X : Type} [Group G] [MulAction G X] [Finite X]
    {a b : X} (hab : a ≠ b) (hpre : MulAction.IsMultiplyPretransitive G X 2)
    (hfix : ∀ g : G, g ≠ 1 → {x : X | g • x = x}.ncard ≤ 2)
    (hc : ∃ c : X, c ≠ a ∧ c ≠ b)
    {t : G} (hta : t • a = a) (htb : t • b = b) (htord : orderOf t = 2) :
    ∃ s : G, orderOf s = 2 ∧ s • a = b ∧ s • b = a := by
  obtain ⟨c, hca, hcb⟩ := hc
  -- `t ≠ 1`, since `orderOf t = 2`
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htord
    exact absurd htord (by norm_num)
  -- `t * t = 1`
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [htord] at h
    simpa [pow_two] using h
  -- `t` does not fix the third point `c`: otherwise it would fix three distinct points
  have htcc : t • c ≠ c := by
    intro htc
    have hS : ({a, b, c} : Set X) ⊆ {x : X | t • x = x} := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hta
      · exact htb
      · exact htc
    have h3 : ({a, b, c} : Set X).ncard = 3 := by
      rw [Set.ncard_eq_three]
      exact ⟨a, b, c, hab, hca.symm, hcb.symm, rfl⟩
    have hle : ({a, b, c} : Set X).ncard ≤ ({x : X | t • x = x}).ncard :=
      Set.ncard_le_ncard hS (Set.toFinite _)
    have hle2 := hle.trans (hfix t ht1)
    omega
  -- `2`-transitivity moves the pair `(c, t • c)` to `(a, b)`
  obtain ⟨g, hgc, hgd⟩ := (MulAction.is_two_pretransitive_iff.mp hpre) (Ne.symm htcc) hab
  have hginvb : g⁻¹ • b = t • c := by rw [← hgd, inv_smul_smul]
  have htc : t • (t • c) = c := by rw [← mul_smul, ht2, one_smul]
  refine ⟨g * t * g⁻¹, ?_, ?_, ?_⟩
  · have h1 : (MulAut.conj g) t = g * t * g⁻¹ := by simp [MulAut.conj_apply]
    rw [← h1, (MulAut.conj g).orderOf_eq t, htord]
  · calc (g * t * g⁻¹) • a = g • (t • (g⁻¹ • a)) := by simp only [mul_smul]
      _ = g • (t • c) := by rw [← hgc, inv_smul_smul]
      _ = b := hgd
  · calc (g * t * g⁻¹) • b = g • (t • (g⁻¹ • b)) := by simp only [mul_smul]
      _ = g • (t • (t • c)) := by rw [hginvb]
      _ = g • c := by rw [htc]
      _ = a := hgc

end Work.ZASS
