import Mathlib

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.CORE4.A7FGB

/-- If a subgroup `V ≤ A₇` has order `4` and every non-identity element has support exactly `T`
(with `|T| = 4`), then `V` acts transitively on `T`. -/
lemma V_transitive {V : Subgroup (alternatingGroup (Fin 7))} {T : Finset (Fin 7)}
    (hT : T.card = 4)
    (hVcard : Nat.card V = 4)
    (hsupp : ∀ v ∈ V, v ≠ 1 → (v : Equiv.Perm (Fin 7)).support = T)
    {t t' : Fin 7} (ht : t ∈ T) (ht' : t' ∈ T) :
    ∃ v : ↥V, (v : Equiv.Perm (Fin 7)) t = t' := by
  letI : Fintype ↥V := Fintype.ofFinite _
  -- every element of `V` maps `T` into `T`
  have hmap : ∀ v : ↥V, (v : Equiv.Perm (Fin 7)) t ∈ T := by
    intro v
    by_cases hv : v = 1
    · rw [hv]; simpa using ht
    · have hs := hsupp v.1 v.2 (fun h => hv (Subtype.ext h))
      have hmem : t ∈ (v : Equiv.Perm (Fin 7)).support := by rw [hs]; exact ht
      have := Equiv.Perm.apply_mem_support.mpr hmem
      rwa [hs] at this
  -- the orbit map `v ↦ v t` is injective
  have hinj : Function.Injective (fun v : ↥V => (v : Equiv.Perm (Fin 7)) t) := by
    intro v w hvw
    have h1 : (w⁻¹ * v) • t = t := by
      rw [mul_smul]
      have : v • t = w • t := by simpa [Subgroup.smul_def] using hvw
      rw [this, inv_smul_smul]
    have h2 : w⁻¹ * v = 1 := by
      by_contra hne
      have hsv := hsupp (w⁻¹ * v).1 (w⁻¹ * v).2 (fun h => hne (Subtype.ext h))
      have hmem : t ∈ ((w⁻¹ * v : ↥V) : Equiv.Perm (Fin 7)).support := by rw [hsv]; exact ht
      have hfix : ((w⁻¹ * v : ↥V) : Equiv.Perm (Fin 7)) t = t := by
        simpa [Subgroup.smul_def] using h1
      exact (Equiv.Perm.mem_support.mp hmem) hfix
    exact (inv_mul_eq_one.mp h2).symm
  have hFcard : Fintype.card ↥V = 4 := by rw [← Nat.card_eq_fintype_card]; exact hVcard
  have himgcard : (Finset.univ.image (fun v : ↥V => (v : Equiv.Perm (Fin 7)) t)).card = 4 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hFcard]
  have hsub : Finset.univ.image (fun v : ↥V => (v : Equiv.Perm (Fin 7)) t) ⊆ T := by
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨v, -, rfl⟩ := hs
    exact hmap v
  have heq : Finset.univ.image (fun v : ↥V => (v : Equiv.Perm (Fin 7)) t) = T :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hT]; rw [himgcard])
  have hmem2 : t' ∈ Finset.univ.image (fun v : ↥V => (v : Equiv.Perm (Fin 7)) t) := by
    rw [heq]; exact ht'
  rw [Finset.mem_image] at hmem2
  obtain ⟨v, -, hv⟩ := hmem2
  exact ⟨v, hv⟩

/-- If `x ∈ A₇` has order `3` and support exactly the complement `univ \ T` (with `|T| = 4`),
then `⟨x⟩` acts transitively on that complement. -/
lemma x_transitive {x : alternatingGroup (Fin 7)} {T : Finset (Fin 7)} (hT : T.card = 4)
    (hx3 : orderOf x = 3)
    (hxT : (x : Equiv.Perm (Fin 7)).support = Finset.univ \ T)
    {c c' : Fin 7} (hc : c ∈ Finset.univ \ T) (hc' : c' ∈ Finset.univ \ T) :
    ∃ k : ℕ, ((x : Equiv.Perm (Fin 7)) ^ k) c = c' := by
  let C := Finset.univ \ T
  have hCcard : C.card = 3 := by
    dsimp [C]; rw [Finset.card_sdiff]; simp [hT]
  have hxC : (x : Equiv.Perm (Fin 7)).support = C := hxT
  have hx3p : (x : Equiv.Perm (Fin 7))^3 = 1 := by
    have h := hx3 ▸ pow_orderOf_eq_one x
    have := congrArg (fun g : alternatingGroup (Fin 7) => (g : Equiv.Perm (Fin 7))) h
    simpa using this
  have hmaps : ∀ y ∈ C, (x : Equiv.Perm (Fin 7)) y ∈ C := by
    intro y hy
    rw [← hxC] at hy ⊢
    exact Equiv.Perm.apply_mem_support.mpr hy
  have hcC : c ∈ C := hc
  have hxcC : (x : Equiv.Perm (Fin 7)) c ∈ C := hmaps c hcC
  have hx2cC : ((x : Equiv.Perm (Fin 7)) ^ 2) c ∈ C := by
    rw [pow_two, Equiv.Perm.mul_apply]
    exact hmaps ((x : Equiv.Perm (Fin 7)) c) hxcC
  have hneq1 : c ≠ (x : Equiv.Perm (Fin 7)) c := by
    intro h
    have : c ∈ (x : Equiv.Perm (Fin 7)).support := by rw [hxC]; exact hcC
    exact (Equiv.Perm.mem_support.mp this) h.symm
  have hneq3 : (x : Equiv.Perm (Fin 7)) c ≠ ((x : Equiv.Perm (Fin 7)) ^ 2) c := by
    intro h
    rw [pow_two, Equiv.Perm.mul_apply] at h
    exact hneq1 (Equiv.injective (x : Equiv.Perm (Fin 7)) h)
  have hneq2 : c ≠ ((x : Equiv.Perm (Fin 7)) ^ 2) c := by
    intro h
    have hcube : ((x : Equiv.Perm (Fin 7)) ^ 3) c = c := by rw [hx3p]; rfl
    have hxceq : (x : Equiv.Perm (Fin 7)) c = c := by
      calc (x : Equiv.Perm (Fin 7)) c
          = (x : Equiv.Perm (Fin 7)) (((x : Equiv.Perm (Fin 7)) ^ 2) c) := by rw [h.symm]
        _ = ((x : Equiv.Perm (Fin 7)) ^ 3) c := by
              rw [pow_succ' (x : Equiv.Perm (Fin 7)) 2, Equiv.Perm.mul_apply]
        _ = c := hcube
    exact hneq1 hxceq.symm
  have hSsub :
      ({c, (x : Equiv.Perm (Fin 7)) c, ((x : Equiv.Perm (Fin 7)) ^ 2) c} : Finset (Fin 7)) ⊆ C := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact hcC
    · exact hxcC
    · exact hx2cC
  have hScard :
      ({c, (x : Equiv.Perm (Fin 7)) c, ((x : Equiv.Perm (Fin 7)) ^ 2) c} : Finset (Fin 7)).card = 3 := by
    rw [Finset.card_insert_of_notMem
          (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hneq1, hneq2⟩),
        Finset.card_insert_of_notMem (by simpa using hneq3), Finset.card_singleton]
  have heq :
      ({c, (x : Equiv.Perm (Fin 7)) c, ((x : Equiv.Perm (Fin 7)) ^ 2) c} : Finset (Fin 7)) = C :=
    Finset.eq_of_subset_of_card_le hSsub (by rw [hCcard, hScard])
  have hmem :
      c' ∈ ({c, (x : Equiv.Perm (Fin 7)) c, ((x : Equiv.Perm (Fin 7)) ^ 2) c} : Finset (Fin 7)) := by
    rw [heq]; exact hc'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · exact ⟨2, by simp⟩

theorem transitive_or_preserves (R V : Subgroup (alternatingGroup (Fin 7))) (x : alternatingGroup (Fin 7))
    (T : Finset (Fin 7)) (hT : T.card = 4) (hVR : V ≤ R) (hVcard : Nat.card V = 4)
    (h2 : ∀ v ∈ V, v * v = 1)
    (hsupp : ∀ v ∈ V, v ≠ 1 → (v : Equiv.Perm (Fin 7)).support = T)
    (hxR : x ∈ R) (hx3 : orderOf x = 3)
    (hxT : (x : Equiv.Perm (Fin 7)).support = Finset.univ \ T) :
    MulAction.IsPretransitive ↥R (Fin 7) ∨
      ∀ (r : ↥R) (t : Fin 7), t ∈ T → ((r : ↥R) : Equiv.Perm (Fin 7)) t ∈ T := by
  by_cases hpres : ∀ (r : ↥R) (t : Fin 7), t ∈ T → ((r : ↥R) : Equiv.Perm (Fin 7)) t ∈ T
  · exact Or.inr hpres
  · left
    push Not at hpres
    obtain ⟨r₀, t₀, ht₀, hnc₀⟩ := hpres
    set c₀ : Fin 7 := ((r₀ : ↥R) : Equiv.Perm (Fin 7)) t₀ with hc₀def
    have hc₀C : c₀ ∈ Finset.univ \ T := by
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ _, by rw [hc₀def]; exact hnc₀⟩
    -- `t₀` is a base point whose `R`-orbit is everything
    have key : ∀ a : Fin 7, ∃ ra : ↥R, ra • t₀ = a := by
      intro a
      have ha : a ∈ T ∨ a ∈ Finset.univ \ T := by
        have hun : a ∈ T ∪ (Finset.univ \ T) := by
          rw [Finset.union_sdiff_of_subset (Finset.subset_univ T)]
          exact Finset.mem_univ a
        exact Finset.mem_union.mp hun
      rcases ha with haT | haC
      · obtain ⟨v, hv⟩ := V_transitive (V := V) (T := T) hT hVcard hsupp ht₀ haT
        refine ⟨⟨v.1, hVR v.2⟩, ?_⟩
        simpa [Subgroup.smul_def] using hv
      · obtain ⟨k, hk⟩ := x_transitive (T := T) hT hx3 hxT hc₀C haC
        have hmem : x ^ k * r₀.1 ∈ R := R.mul_mem (R.pow_mem hxR k) r₀.2
        refine ⟨⟨x ^ k * r₀.1, hmem⟩, ?_⟩
        have hco : ((⟨x ^ k * r₀.1, hmem⟩ : ↥R) : Equiv.Perm (Fin 7)) t₀
            = ((x : Equiv.Perm (Fin 7)) ^ k) c₀ := by
          rw [hc₀def]
          simp [Subgroup.coe_mul, Equiv.Perm.mul_apply]
        simpa [Subgroup.smul_def, hco] using hk
    rw [MulAction.isPretransitive_iff]
    intro a b
    obtain ⟨ra, hra⟩ := key a
    obtain ⟨rb, hrb⟩ := key b
    refine ⟨rb * ra⁻¹, ?_⟩
    have hta : ra⁻¹ • a = t₀ := by rw [← hra, ← mul_smul, inv_mul_cancel, one_smul]
    rw [mul_smul, hta, hrb]

end Work.CORE4.A7FGB
