import Mathlib
import Submission.Work.LT.Defs

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/LT/DESIGN.md first (the orchestrator's design; your lemma is one node of its DAG). Shared definitions: Submission/Work/LT/Defs.lean (namespace Work.LT) — do NOT edit it; if you need a new shared definition, put it in your own file. Siblings are being proved in parallel; import them when they land.

# transport_rate_distance — guidance

* `transportCode e C = C.comap (funLeft e)`, and `funLeft e` is a linear *equivalence*
  `(Fin n → 𝔽₂) ≃ₗ (X → 𝔽₂)` (`LinearEquiv.funCongrLeft`). So `transportCode e C` is the image of
  `C` under the inverse equivalence: `LinearEquiv.finrank_map_eq` / `Submodule.equivMapOfInjective`.
  Then `rate = dim / n` is `rfl` after that.
* Distance: `distance` is `sInf {d | ∃ c ∈ C', c ≠ 0 ∧ hammingNorm c = d}`; the set is nonempty
  (`hne`), so `Nat.sInf_mem` gives a minimiser `c'`; `c' ∘ e.symm ∈ C` is nonzero, and
  `hammingNorm c' = hammingNorm (c' ∘ e.symm)` (reindex the filter by `e`). Divide by `n`
  (if `n = 0` then `X` is empty, contradicting `hne`).

Expected size: 80–150 lines.
-/

namespace Work.LT

open GoodLTC NNReal

/-- Reindexing a word along a bijection preserves its Hamming weight. -/
lemma hammingNorm_comp_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (f : β → ZMod 2) : hammingNorm (f ∘ e) = hammingNorm f := by
  classical
  rw [hammingNorm, hammingNorm]
  refine Finset.card_bij (fun a _ => e a) ?_ ?_ ?_
  · intro a ha; simpa using ha
  · intro a₁ _ a₂ _ h; exact e.injective h
  · intro b hb; exact ⟨e.symm b, by simpa using hb, e.apply_symm_apply b⟩

/-- `LinearMap.funLeft` along a bijection preserves the Hamming weight. -/
lemma hammingNorm_funLeft_equiv {X : Type} [Fintype X] {n : ℕ} (e : X ≃ Fin n)
    (c : Fin n → ZMod 2) :
    hammingNorm (LinearMap.funLeft (ZMod 2) (ZMod 2) e c) = hammingNorm c := by
  classical
  exact hammingNorm_comp_equiv e c

/-- Rate and normalised distance survive transport along `e : X ≃ Fin n`: the dimension is
unchanged, and a weight lower bound `δ n` for nonzero codewords (with at least one nonzero
codeword) gives `normalisedDistance ≥ δ`. -/
theorem transport_rate_distance {X : Type} [Fintype X] {n : ℕ} (e : X ≃ Fin n)
    (C : Submodule (ZMod 2) (X → ZMod 2)) (δ : ℝ) (hne : ∃ f ∈ C, f ≠ 0)
    (hw : ∀ f ∈ C, f ≠ 0 → δ * n ≤ hammingNorm f) :
    rate (transportCode e C) = (Module.finrank (ZMod 2) C : ℝ) / n ∧
      δ ≤ normalisedDistance (transportCode e C) := by
  classical
  -- The transport is the image of `C` under the linear equivalence inverse to `funLeft e`.
  let φ : (X → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e.symm
  have hmap : transportCode e C =
      Submodule.map (φ : (X → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) C := by
    ext v
    rw [transportCode, Submodule.mem_comap, Submodule.mem_map]
    constructor
    · intro hv
      exact ⟨LinearMap.funLeft (ZMod 2) (ZMod 2) e v, hv, by
        show LinearMap.funLeft (ZMod 2) (ZMod 2) e.symm
          (LinearMap.funLeft (ZMod 2) (ZMod 2) e v) = v
        ext i; simp⟩
    · rintro ⟨w, hwC, rfl⟩
      show LinearMap.funLeft (ZMod 2) (ZMod 2) e
        (LinearMap.funLeft (ZMod 2) (ZMod 2) e.symm w) ∈ C
      rw [show LinearMap.funLeft (ZMod 2) (ZMod 2) e
          (LinearMap.funLeft (ZMod 2) (ZMod 2) e.symm w) = w from by
        ext i; simp]
      exact hwC
  -- Rate: `φ` is a linear equivalence, so it preserves the dimension.
  have hrate : rate (transportCode e C) = (Module.finrank (ZMod 2) C : ℝ) / n := by
    have hfin : Module.finrank (ZMod 2) (transportCode e C) = Module.finrank (ZMod 2) C := by
      rw [hmap]
      exact LinearEquiv.finrank_map_eq φ C
    rw [GoodLTC.rate, GoodLTC.dim, hfin]
  -- The length is nonzero: otherwise `X` is empty and no nonzero codeword exists.
  have hnpos : (0 : ℝ) < n := by
    have hn : n ≠ 0 := by
      rintro rfl
      obtain ⟨f, _, hfne⟩ := hne
      exact hfne (funext fun x => absurd (e x).isLt (Nat.not_lt_zero _))
    exact_mod_cast Nat.pos_of_ne_zero hn
  refine ⟨hrate, ?_⟩
  -- Distance: take a minimum-weight nonzero word of the transport.
  let S : Set ℕ := {d | ∃ c ∈ transportCode e C, c ≠ 0 ∧ hammingNorm c = d}
  obtain ⟨f, hfC, hfne⟩ := hne
  have hmem : (φ : (X → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) f ∈ transportCode e C :=
    hmap ▸ Submodule.mem_map.mpr ⟨f, hfC, rfl⟩
  have hφne : (φ : (X → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) f ≠ 0 := by
    intro h
    exact hfne (φ.injective (by simpa using h))
  have hSne : S.Nonempty :=
    ⟨hammingNorm ((φ : (X → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) f),
      (φ : (X → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) f, hmem, hφne, rfl⟩
  obtain ⟨c', hc'mem, hc'ne, hc'w⟩ := Nat.sInf_mem hSne
  -- Pull the minimiser back to a nonzero codeword of `C`.
  have hφc' : LinearMap.funLeft (ZMod 2) (ZMod 2) e c' ∈ C := by
    have h := hc'mem
    rwa [transportCode, Submodule.mem_comap] at h
  have hφc'ne : LinearMap.funLeft (ZMod 2) (ZMod 2) e c' ≠ 0 := by
    intro h
    refine hc'ne ?_
    have hinj := LinearMap.funLeft_injective_of_surjective (R := ZMod 2) (M := ZMod 2) e e.surjective
    exact hinj (by simp [h])
  have hbound : δ * n ≤ (hammingNorm c' : ℝ) := by
    have h1 := hw (LinearMap.funLeft (ZMod 2) (ZMod 2) e c') hφc' hφc'ne
    rwa [hammingNorm_funLeft_equiv e c'] at h1
  have hdist : (distance (transportCode e C) : ℝ) = ((sInf S : ℕ) : ℝ) := rfl
  have hnorm : normalisedDistance (transportCode e C) = ((sInf S : ℕ) : ℝ) / n := by
    simp only [GoodLTC.normalisedDistance]
    rw [hdist]
  rw [hnorm]
  rw [le_div_iff₀ hnpos]
  rw [← hc'w]
  exact hbound

end Work.LT
