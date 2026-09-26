import Mathlib

namespace Work.Drive.EpsFormSphere

/-- **`Work.Drive.EpsFormSphere.submodule_const_of_finrank_jumps`**

Let `V : ℝ → Submodule ℚ (ℚ × ℚ)` be a one-parameter family of rational subspaces of the
two-dimensional space `ℚ × ℚ`.  Suppose that

* `V` is constant on every closed interval `[μ, ν] ⊆ [lam0, lam1]` that avoids the finite
  exceptional set `exc` (`hreg`);
* `exc ⊆ (lam0, lam1)` (`hexc`) and the dimension of `V` jumps by at most one as one crosses
  a single exceptional value, in either direction (`hjump`);
* at every non-exceptional value of `[lam0, lam1]` the subspace `V lam` is either `⊥` or `⊤`
  (`hdich`).

Then `V lam0 = V lam1`.

The proof is the elementary one: the exceptional points cut `[lam0, lam1]` into finitely many
intervals on which `V` is constant, and because every `V` at a non-exceptional point is `⊥` or
`⊤` its dimension lies in `{0, 2}`, so the "jump at most one" condition forces adjacent
intervals to carry the same value.  Formally we do strong induction on the number of
exceptional points in `(μ, ν)`, and squeeze one exceptional point at a time between a pair of
non-exceptional points. -/
theorem submodule_const_of_finrank_jumps (V : ℝ → Submodule ℚ (ℚ × ℚ)) (lam0 lam1 : ℝ)
    (exc : Finset ℝ) (hl : lam0 < lam1) (hexc : ∀ t ∈ exc, lam0 < t ∧ t < lam1)
    (hreg : ∀ μ ν : ℝ, lam0 ≤ μ → μ ≤ ν → ν ≤ lam1 → (∀ t ∈ exc, t < μ ∨ ν < t) → V μ = V ν)
    (hjump : ∀ lam ∈ exc, ∀ μ ν : ℝ, lam0 ≤ μ → μ < lam → lam < ν → ν ≤ lam1 →
      (∀ t ∈ exc, t < μ ∨ t = lam ∨ ν < t) →
      Module.finrank ℚ ↥(V μ) ≤ Module.finrank ℚ ↥(V ν) + 1 ∧
      Module.finrank ℚ ↥(V ν) ≤ Module.finrank ℚ ↥(V μ) + 1)
    (hdich : ∀ lam : ℝ, lam0 ≤ lam → lam ≤ lam1 → (∀ t ∈ exc, t ≠ lam) →
      V lam = ⊥ ∨ V lam = ⊤) :
    V lam0 = V lam1 := by
  -- The dimensions of `⊥` and `⊤` in `ℚ × ℚ`.
  have hfr_top : Module.finrank ℚ ↥(⊤ : Submodule ℚ (ℚ × ℚ)) = 2 := by
    rw [finrank_top, Module.finrank_prod, Module.finrank_self]
  have hfr_bot : Module.finrank ℚ ↥(⊥ : Submodule ℚ (ℚ × ℚ)) = 0 := by simp
  -- **Crossing a single exceptional value.**  If `e ∈ exc` and `μ < e < ν` are non-exceptional
  -- points such that `e` is the only exceptional point of `[μ, ν]`, then `V μ = V ν`.
  have crossing : ∀ (e : ℝ), e ∈ exc → ∀ μ ν : ℝ, lam0 ≤ μ → μ < e → e < ν → ν ≤ lam1 →
      μ ∉ exc → ν ∉ exc → (∀ t ∈ exc, t < μ ∨ t = e ∨ ν < t) → V μ = V ν := by
    intro e he μ ν hμ0 hμe heν hν1 hμnx hνnx hsep
    obtain ⟨h1, h2⟩ := hjump e he μ ν hμ0 hμe heν hν1 hsep
    have hμ1 : μ ≤ lam1 := le_trans hμe.le (le_trans heν.le hν1)
    have hν0 : lam0 ≤ ν := le_trans hμ0 (le_trans hμe.le heν.le)
    have hμd : V μ = ⊥ ∨ V μ = ⊤ := hdich μ hμ0 hμ1 (fun t ht h => hμnx (h.symm ▸ ht))
    have hνd : V ν = ⊥ ∨ V ν = ⊤ := hdich ν hν0 hν1 (fun t ht h => hνnx (h.symm ▸ ht))
    -- `V μ` and `V ν` are each `⊥` or `⊤`, of dimension `0` or `2`; a jump of at most one
    -- cannot separate two such values.
    rcases hμd with hμ | hμ <;> rcases hνd with hν | hν
    · rw [hμ, hν]
    · exfalso
      rw [hμ, hν, hfr_bot, hfr_top] at h2
      omega
    · exfalso
      rw [hμ, hν, hfr_bot, hfr_top] at h1
      omega
    · rw [hμ, hν]
  -- **The regularity hypothesis** at a pair of non-exceptional points with no exceptional point
  -- strictly between them.
  have hreg_no_between : ∀ μ ν : ℝ, lam0 ≤ μ → μ ≤ ν → ν ≤ lam1 → μ ∉ exc → ν ∉ exc →
      (∀ t ∈ exc, ¬ (μ < t ∧ t < ν)) → V μ = V ν := by
    intro μ ν hμ0 hμν hν1 hμnx hνnx hno
    apply hreg μ ν hμ0 hμν hν1
    intro t ht
    by_contra hcon
    push Not at hcon
    obtain ⟨hle1, hle2⟩ := hcon
    have hlt1 : μ < t := lt_of_le_of_ne hle1 (fun h => hμnx (h.symm ▸ ht))
    have hlt2 : t < ν := lt_of_le_of_ne hle2 (fun h => hνnx (h.symm ▸ ht))
    exact hno t ht ⟨hlt1, hlt2⟩
  -- **The chain.**  `V` takes the same value at any two non-exceptional points of `[lam0, lam1]`;
  -- strong induction on the number of exceptional points in between, removing the smallest one
  -- by the crossing lemma.
  have chain : ∀ k : ℕ, ∀ μ ν : ℝ, lam0 ≤ μ → μ ≤ ν → ν ≤ lam1 → μ ∉ exc → ν ∉ exc →
      (exc.filter (fun t => μ < t ∧ t < ν)).card ≤ k → V μ = V ν := by
    intro k
    induction k with
    | zero =>
      intro μ ν hμ0 hμν hν1 hμnx hνnx hk
      apply hreg_no_between μ ν hμ0 hμν hν1 hμnx hνnx
      intro t ht hlt
      have hmem : t ∈ exc.filter (fun t => μ < t ∧ t < ν) := Finset.mem_filter.mpr ⟨ht, hlt⟩
      have h0 : (exc.filter (fun t => μ < t ∧ t < ν)).card = 0 := Nat.eq_zero_of_le_zero hk
      rw [Finset.card_eq_zero] at h0
      rw [h0] at hmem
      exact Finset.notMem_empty t hmem
    | succ k ih =>
      intro μ ν hμ0 hμν hν1 hμnx hνnx hk
      rcases eq_or_lt_of_le hμν with h | hlt
      · rw [← h]
      · -- `F` = the exceptional points strictly between `μ` and `ν`.
        set F : Finset ℝ := exc.filter (fun t => μ < t ∧ t < ν) with hFdef
        have hkF : F.card ≤ k + 1 := by rw [hFdef]; exact hk
        by_cases hFne : F.Nonempty
        · -- The smallest exceptional point `e` strictly between `μ` and `ν`; there is no
          -- exceptional point in `(μ, e)`.
          set e : ℝ := F.min' hFne with hedef
          have heF : e ∈ F := Finset.min'_mem F hFne
          have heF' : e ∈ exc.filter (fun t => μ < t ∧ t < ν) := hFdef ▸ heF
          have heexc : e ∈ exc := (Finset.mem_filter.mp heF').1
          have hecond : μ < e ∧ e < ν := (Finset.mem_filter.mp heF').2
          have hemin : ∀ t ∈ F, e ≤ t := fun t ht => Finset.min'_le F t ht
          by_cases hF2ne : (exc.filter (fun t => e < t ∧ t < ν)).Nonempty
          · -- There is a next exceptional point `e'` after `e`; pick `ν' ∈ (e, e')` and cross
            -- `e` to `ν'`, then use the induction hypothesis on `(ν', ν)`.
            set e' : ℝ := (exc.filter (fun t => e < t ∧ t < ν)).min' hF2ne with he'def
            have he'F2 : e' ∈ exc.filter (fun t => e < t ∧ t < ν) := Finset.min'_mem _ hF2ne
            have he'exc : e' ∈ exc := (Finset.mem_filter.mp he'F2).1
            have he'cond : e < e' ∧ e' < ν := (Finset.mem_filter.mp he'F2).2
            set ν' : ℝ := (e + e') / 2 with hν'def
            have hν'1 : e < ν' := by rw [hν'def]; linarith [he'cond.1]
            have hν'2 : ν' < e' := by rw [hν'def]; linarith [he'cond.1]
            have hν'exc : ν' ∉ exc := by
              intro hν'mem
              have hν'F2 : ν' ∈ exc.filter (fun t => e < t ∧ t < ν) :=
                Finset.mem_filter.mpr ⟨hν'mem, ⟨hν'1, lt_trans hν'2 he'cond.2⟩⟩
              have hle : e' ≤ ν' := Finset.min'_le _ ν' hν'F2
              exact absurd hle (not_le_of_gt hν'2)
            have hν'le : ν' ≤ lam1 := le_trans (le_of_lt (lt_trans hν'2 he'cond.2)) hν1
            have hsep2 : ∀ t ∈ exc, t < μ ∨ t = e ∨ ν' < t := by
              intro t ht
              by_cases hltμ : t < μ
              · exact Or.inl hltμ
              · push Not at hltμ
                by_cases hte : t = e
                · exact Or.inr (Or.inl hte)
                · have hμt : μ < t := lt_of_le_of_ne hltμ (fun h => hμnx (h.symm ▸ ht))
                  by_cases hltν' : t < ν'
                  · -- `t` is an exceptional point strictly between `e` and `e'`, contradicting
                    -- the minimality of `e'`.
                    exfalso
                    have htF : t ∈ F := by
                      rw [hFdef]
                      exact Finset.mem_filter.mpr
                        ⟨ht, ⟨hμt, lt_trans hltν' (lt_trans hν'2 he'cond.2)⟩⟩
                    have hle : e ≤ t := hemin t htF
                    have het : e < t := lt_of_le_of_ne hle (fun h => hte h.symm)
                    have htF2 : t ∈ exc.filter (fun t => e < t ∧ t < ν) :=
                      Finset.mem_filter.mpr
                        ⟨ht, ⟨het, lt_trans hltν' (lt_trans hν'2 he'cond.2)⟩⟩
                    have hle' : e' ≤ t := Finset.min'_le _ t htF2
                    exact absurd hle' (not_le_of_gt (lt_trans hltν' hν'2))
                  · push Not at hltν'
                    exact Or.inr (Or.inr (lt_of_le_of_ne hltν' (fun h => hν'exc (h.symm ▸ ht))))
            have hcross := crossing e heexc μ ν' hμ0 hecond.1 hν'1 hν'le hμnx hν'exc hsep2
            have hcard : (exc.filter (fun t => ν' < t ∧ t < ν)).card ≤ k := by
              have hsub : exc.filter (fun t => ν' < t ∧ t < ν) ⊆ F.erase e := by
                intro t ht
                rw [Finset.mem_filter] at ht
                obtain ⟨htexc, hgt, hlt⟩ := ht
                rw [Finset.mem_erase]
                refine ⟨fun h => ?_, ?_⟩
                · rw [h] at hgt
                  exact (not_lt_of_ge hν'1.le) hgt
                · rw [hFdef]
                  exact Finset.mem_filter.mpr
                    ⟨htexc, ⟨lt_trans hecond.1 (lt_trans hν'1 hgt), hlt⟩⟩
              calc (exc.filter (fun t => ν' < t ∧ t < ν)).card ≤ (F.erase e).card :=
                    Finset.card_le_card hsub
                _ = F.card - 1 := Finset.card_erase_of_mem heF
                _ ≤ k := by omega
            have h0' : lam0 ≤ ν' := le_trans hμ0 (le_trans hecond.1.le hν'1.le)
            have hνν' : ν' ≤ ν := le_of_lt (lt_trans hν'2 he'cond.2)
            exact hcross.trans (ih ν' ν h0' hνν' hν1 hν'exc hνnx hcard)
          · -- No exceptional point in `(e, ν)`: cross `e` directly.
            refine crossing e heexc μ ν hμ0 hecond.1 hecond.2 hν1 hμnx hνnx ?_
            intro t ht
            by_cases hltμ : t < μ
            · exact Or.inl hltμ
            · push Not at hltμ
              by_cases hte : t = e
              · exact Or.inr (Or.inl hte)
              · have hμt : μ < t := lt_of_le_of_ne hltμ (fun h => hμnx (h.symm ▸ ht))
                by_cases hltν : t < ν
                · -- `t` would be an exceptional point strictly between `e` and `ν`.
                  exfalso
                  have htF : t ∈ F := by
                    rw [hFdef]
                    exact Finset.mem_filter.mpr ⟨ht, ⟨hμt, hltν⟩⟩
                  have hle : e ≤ t := hemin t htF
                  have het : e < t := lt_of_le_of_ne hle (fun h => hte h.symm)
                  have htF2 : t ∈ exc.filter (fun t => e < t ∧ t < ν) :=
                    Finset.mem_filter.mpr ⟨ht, ⟨het, hltν⟩⟩
                  exact hF2ne ⟨t, htF2⟩
                · push Not at hltν
                  exact Or.inr (Or.inr (lt_of_le_of_ne hltν (fun h => hνnx (h.symm ▸ ht))))
        · -- No exceptional point strictly between `μ` and `ν`.
          apply hreg_no_between μ ν hμ0 hμν hν1 hμnx hνnx
          intro t ht hlt
          have hmem : t ∈ F := by rw [hFdef]; exact Finset.mem_filter.mpr ⟨ht, hlt⟩
          exact hFne ⟨t, hmem⟩
  -- Apply the chain to `lam0` and `lam1`.
  exact chain exc.card lam0 lam1 le_rfl hl.le le_rfl
    (fun h => (lt_irrefl lam0) (hexc lam0 h).1) (fun h => (lt_irrefl lam1) (hexc lam1 h).2)
    (Finset.card_filter_le _ _)

end Work.Drive.EpsFormSphere
