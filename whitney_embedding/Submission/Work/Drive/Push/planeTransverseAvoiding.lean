import Mathlib

/-!
# An `n`-plane transverse to two given `n`-planes and avoiding a vector

This file establishes `Work.Drive.Push.planeTransverseAvoiding`: in `ℝ^{2n}`, given two
`n`-dimensional subspaces `V`, `W` and a nonzero vector `z`, there is an `n`-dimensional
subspace `H` with `H ⊓ V = ⊥`, `H ⊓ W = ⊥` and `z ∉ H`.

The proof is an induction on the dimension of `H`, adjoining one vector at a time.  At each
stage, given `H` of dimension `j < n` with the desired properties, the three subspaces
`V ⊔ H`, `W ⊔ H`, `ℝ ∙ z ⊔ H` are all proper (their finrank is `n + j`, `n + j` and at most
`1 + j ≤ n` respectively, all `< 2n`), so — over the infinite field `ℝ`, finitely many proper
subspaces never cover the whole space (`Subspace.biUnion_ne_univ_of_top_notMem`) — there is a
vector `h` outside all three.  Adjoining `h` preserves transversality to `V` and `W`, keeps
`z` out, and raises the dimension by one.
-/

set_option linter.unusedVariables false

namespace Work.Drive.Push

/-- Over an infinite field, finitely many proper subspaces never cover the whole space. -/
private lemma exists_notMem_fin_union {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*}
    [Finite ι] (p : ι → Submodule ℝ E) (hp : ∀ i, p i ≠ ⊤) : ∃ v : E, ∀ i, v ∉ p i := by
  by_contra h
  have h' : ∀ v : E, ∃ i, v ∈ p i := fun v => by
    by_contra hv
    exact h ⟨v, fun i hi => hv ⟨i, hi⟩⟩
  have hcov : ⋃ i, (p i : Set E) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact h' x
  obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcov
  exact hp i hi

/-- If `H₀` is transverse to `S` and `h ∉ S ⊔ H₀`, then `H₀ ⊔ ℝ ∙ h` is still transverse to `S`. -/
private lemma sup_span_singleton_inf_eq_bot {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S H₀ : Submodule ℝ E} {h : E} (hHS : H₀ ⊓ S = ⊥) (hh : h ∉ S ⊔ H₀) :
    (H₀ ⊔ ℝ ∙ h) ⊓ S = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨hxH, hxS⟩ := hx
  rw [Submodule.mem_sup] at hxH
  obtain ⟨a, ha, b, hb, hab⟩ := hxH
  rw [Submodule.mem_span_singleton] at hb
  obtain ⟨c, hc⟩ := hb
  by_cases hc0 : c = 0
  · have hxa : x = a := by rw [← hab, ← hc, hc0, zero_smul, add_zero]
    rw [hxa] at hxS ⊢
    have hmem : a ∈ H₀ ⊓ S := ⟨ha, hxS⟩
    rw [hHS] at hmem
    simpa using hmem
  · exfalso
    apply hh
    have h1 : x - a = c • h := by rw [← hab, ← hc, add_sub_cancel_left]
    have h2 : h = c⁻¹ • (x - a) := by rw [h1, inv_smul_smul₀ hc0]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.mem_sup_left hxS)
      (Submodule.mem_sup_right ha))

/-- If `z ∉ H₀` and `h ∉ ℝ ∙ z ⊔ H₀`, then `z ∉ H₀ ⊔ ℝ ∙ h`. -/
private lemma sup_span_singleton_notMem {E : Type*} [AddCommGroup E] [Module ℝ E]
    {H₀ : Submodule ℝ E} {z h : E} (hz : z ∉ H₀) (hh : h ∉ ℝ ∙ z ⊔ H₀) :
    z ∉ H₀ ⊔ ℝ ∙ h := by
  intro hz'
  rw [Submodule.mem_sup] at hz'
  obtain ⟨a, ha, b, hb, hab⟩ := hz'
  rw [Submodule.mem_span_singleton] at hb
  obtain ⟨c, hc⟩ := hb
  by_cases hc0 : c = 0
  · apply hz
    have : z = a := by rw [← hab, ← hc, hc0, zero_smul, add_zero]
    rw [this]; exact ha
  · apply hh
    have h1 : z - a = c • h := by rw [← hab, ← hc, add_sub_cancel_left]
    have h2 : h = c⁻¹ • (z - a) := by rw [h1, inv_smul_smul₀ hc0]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.mem_sup_left (Submodule.mem_span_singleton_self z))
      (Submodule.mem_sup_right ha))

/-- Adjoining a vector outside `H₀` raises the finrank by one. -/
private lemma finrank_sup_span_singleton {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E]
    {H₀ : Submodule ℝ E} {h : E} (hh : h ∉ H₀) :
    Module.finrank ℝ ↥(H₀ ⊔ ℝ ∙ h) = Module.finrank ℝ H₀ + 1 := by
  have hne : h ≠ 0 := fun h0 => hh (h0 ▸ Submodule.zero_mem H₀)
  have hinf : H₀ ⊓ ℝ ∙ h = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf, Submodule.mem_span_singleton] at hx
    obtain ⟨hxH, c, hc⟩ := hx
    by_cases hc0 : c = 0
    · rw [hc0, zero_smul] at hc; exact hc.symm
    · exfalso
      have : h = c⁻¹ • x := by rw [← hc, inv_smul_smul₀ hc0]
      exact hh (this ▸ Submodule.smul_mem _ _ hxH)
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq H₀ (ℝ ∙ h)
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hne] at h2
  exact h2

theorem planeTransverseAvoiding {n : ℕ}
    (H₀ V W : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n))))
    (hH₀ : Module.finrank ℝ H₀ = n) (hV : Module.finrank ℝ V = n)
    (hW : Module.finrank ℝ W = n)
    (hH₀V : H₀ ⊓ V = ⊥) (hH₀W : H₀ ⊓ W = ⊥)
    (z : EuclideanSpace ℝ (Fin (2 * n))) (hz : z ≠ 0) :
    ∃ H : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n))),
      Module.finrank ℝ H = n ∧ H ⊓ V = ⊥ ∧ H ⊓ W = ⊥ ∧ z ∉ H := by
  have hdimE : Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * n))) = 2 * n :=
    finrank_euclideanSpace_fin
  have key : ∀ i ≤ n, ∃ H : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n))),
      Module.finrank ℝ H = i ∧ H ⊓ V = ⊥ ∧ H ⊓ W = ⊥ ∧ z ∉ H := by
    intro i
    induction i with
    | zero =>
        intro _
        exact ⟨⊥, by simp [hz]⟩
    | succ j ih =>
        intro hj
        obtain ⟨H, hHj, hHV, hHW, hHz⟩ := ih (by omega)
        have hjn : j < n := by omega
        have hA : V ⊔ H ≠ ⊤ := by
          intro htop
          have h1 : Module.finrank ℝ ↥(V ⊔ H) = n + j := by
            have h2 := Submodule.finrank_sup_add_finrank_inf_eq V H
            rw [show V ⊓ H = ⊥ by rw [inf_comm]; exact hHV, finrank_bot, add_zero, hV,
              hHj] at h2
            exact h2
          rw [htop, finrank_top, hdimE] at h1
          omega
        have hB : W ⊔ H ≠ ⊤ := by
          intro htop
          have h1 : Module.finrank ℝ ↥(W ⊔ H) = n + j := by
            have h2 := Submodule.finrank_sup_add_finrank_inf_eq W H
            rw [show W ⊓ H = ⊥ by rw [inf_comm]; exact hHW, finrank_bot, add_zero, hW,
              hHj] at h2
            exact h2
          rw [htop, finrank_top, hdimE] at h1
          omega
        have hC : ℝ ∙ z ⊔ H ≠ ⊤ := by
          intro htop
          have h1 : Module.finrank ℝ ↥(ℝ ∙ z ⊔ H) ≤ 1 + j := by
            have h2 := Submodule.finrank_sup_add_finrank_inf_eq (ℝ ∙ z) H
            have hz1 : Module.finrank ℝ ↥(ℝ ∙ z) = 1 := finrank_span_singleton hz
            omega
          rw [htop, finrank_top, hdimE] at h1
          omega
        obtain ⟨h, hh⟩ := exists_notMem_fin_union
          (fun i : Fin 3 => (![V ⊔ H, W ⊔ H, ℝ ∙ z ⊔ H] :
            Fin 3 → Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n)))) i)
          (by intro i; fin_cases i <;> simp [hA, hB, hC])
        have hhA : h ∉ V ⊔ H := hh 0
        have hhB : h ∉ W ⊔ H := hh 1
        have hhC : h ∉ ℝ ∙ z ⊔ H := hh 2
        have hH : h ∉ H := fun hmem => hhA (Submodule.mem_sup_right hmem)
        refine ⟨H ⊔ ℝ ∙ h, ?_, ?_, ?_, ?_⟩
        · rw [finrank_sup_span_singleton hH]; omega
        · exact sup_span_singleton_inf_eq_bot hHV hhA
        · exact sup_span_singleton_inf_eq_bot hHW hhB
        · exact sup_span_singleton_notMem hHz hhC
  exact key n le_rfl

end Work.Drive.Push
