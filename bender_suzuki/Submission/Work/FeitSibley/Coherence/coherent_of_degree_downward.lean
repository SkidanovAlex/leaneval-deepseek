import Mathlib
import Submission.Work.FeitSibley.Coherence.engine
import Submission.Work.FeitSibley.Coherence.coherent_union_singleton

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.coherent_of_degree_downward`

Coherence of a set of irreducible characters by induction *downward* in the degree.

Let `S` be a set of irreducible characters of a finite group `H`, orthonormal for the character
inner product, and let `τ : ℤ[H → ℂ] → ℤ[G → ℂ]` be an isometry on `ℤ[S]⁰` sending `ℤ[S]⁰` to
degree-zero virtual characters of `G`.  Suppose

* `χ₀ ∈ S` has a non-zero degree and a *minimal* degree among the elements of `S`;
* every degree in `S` is an integral multiple of `χ₀(1)`;
* (Feit's inequality, `hineq`) for every `χ ∈ S` of degree larger than `χ₀(1)`,
  `2 · χ₀(1) · χ(1) < ∑_{ξ ∈ S, ξ(1) < χ(1)} ξ(1)²`.

Then `S` is `τ`-coherent.

The proof has two ingredients.

* The **base case**: the set `T := {ξ ∈ S | ξ(1) = χ₀(1)}` of minimal-degree members of `S` is
  coherent (`Work.FeitSibley.Coherence.minimal_degree_class_coherent`).  As all its members have
  the same degree, this is Isaacs 7.15 / `Coherence.coherent_of_norm_two_lift` when `2 ≤ |T|`, and
  `Coherence.coherent_of_card_le_one` otherwise.

* The **degree-downward induction**: we prove `Coherent A τ` for every `A` with `T ⊆ A ⊆ S` which
  is *downward closed in degree inside `S`* (if `ξ ∈ A` and `ζ ∈ S` has smaller degree, then
  `ζ ∈ A`), by strong induction on `|A|`.  If `A ≠ T`, take `χ ∈ A ∖ T` of maximal degree.  Feit's
  criterion (`coherent_union_singleton`, Isaacs 7.14) applied to `S₀ = A ∖ {χ}` gives coherence of
  `A = (A ∖ {χ}) ∪ {χ}` provided

  `2 · χ₀(1) · χ(1) < ∑_{ξ ∈ A ∖ {χ}} ξ(1)²`.

  The right-hand sum dominates `∑_{ξ ∈ S, ξ(1) < χ(1)} ξ(1)²` (downward closure of `A`), and `hineq`
  bounds the latter from below by `2 · χ₀(1) · χ(1)`.  This is the "downward" step: one removes the
  top-degree element and recurses.

Finally `A := S` is downward closed, so `S` is coherent.
-/

set_option linter.unusedSectionVars false

namespace Work.FeitSibley.Coherence

open Classical

noncomputable section

theorem coherent_of_degree_downward
    {H G : Type*} [Group H] [Fintype H] [Group G] [Fintype G]
    {S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hIrr : ∀ χ ∈ S, χ ∈ Work.CharCore.Irr H)
    (hOrth : Work.Coherence.Orthonormal S)
    (hτ : Work.Coherence.IsometryOn S τ)
    (hτV : ∀ α ∈ Work.Coherence.ZSpan0 S,
      Work.Coherence.IsVChar (τ α) ∧ τ α 1 = 0)
    {χ₀ : H → ℂ} (hχ₀ : χ₀ ∈ S) (hχ₀ne : χ₀ 1 ≠ 0)
    (hmin : ∀ χ ∈ S, Work.CharCore.irrDeg χ₀ ≤ Work.CharCore.irrDeg χ)
    (hdiv : ∀ χ ∈ S, ∃ n : ℕ, χ 1 = (n : ℂ) * (χ₀ 1))
    (hineq : ∀ χ ∈ S, Work.CharCore.irrDeg χ₀ < Work.CharCore.irrDeg χ →
      2 * Work.CharCore.irrDeg χ₀ * Work.CharCore.irrDeg χ
        < ∑ ξ ∈ S.filter (fun ξ => Work.CharCore.irrDeg ξ < Work.CharCore.irrDeg χ),
            (Work.CharCore.irrDeg ξ) ^ 2) :
    Work.Coherence.Coherent S τ := by
  classical
  -- the minimal-degree class
  set T : Finset (H → ℂ) :=
    S.filter (fun ξ => Work.CharCore.irrDeg ξ = Work.CharCore.irrDeg χ₀) with hT
  have hTS : T ⊆ S := fun ξ hξ => (Finset.mem_filter.mp (by rwa [hT] at hξ)).1
  have hmemT : ∀ ξ, ξ ∈ T ↔ ξ ∈ S ∧ Work.CharCore.irrDeg ξ = Work.CharCore.irrDeg χ₀ := by
    intro ξ; rw [hT, Finset.mem_filter]
  have hχ₀T : χ₀ ∈ T := (hmemT χ₀).mpr ⟨hχ₀, rfl⟩
  -- the base case: the minimal-degree class is coherent
  have hbase : Work.Coherence.Coherent T τ := by
    have hIrrT : ∀ ξ ∈ T, ξ ∈ Work.CharCore.Irr H := fun ξ hξ => hIrr ξ ((hmemT ξ).mp hξ).1
    have hχ₀deg : χ₀ 1 = (Work.CharCore.irrDeg χ₀ : ℂ) :=
      Work.CharCore.irrDeg_spec (hIrr χ₀ hχ₀)
    have hdegT : ∀ ξ ∈ T, ξ 1 = χ₀ 1 := by
      intro ξ hξ
      rw [Work.CharCore.irrDeg_spec (hIrrT ξ hξ), ((hmemT ξ).mp hξ).2, ← hχ₀deg]
    by_cases hcard : T.card ≤ 1
    · exact coherent_of_card_le_one hcard (hOrth.mono hTS) (fun ξ hξ => by
        rw [hdegT ξ hξ, hχ₀deg]
        exact Work.CharCore.irrDeg_ne_zero (hIrr χ₀ hχ₀))
    · have hcard2 : 2 ≤ T.card := by omega
      have hmem0 : ∀ ξ ∈ T, ξ - χ₀ ∈ Work.Coherence.ZSpan0 T := by
        intro ξ hξ
        rw [Work.Coherence.mem_zSpan0]
        refine ⟨?_, ?_⟩
        · exact AddSubgroup.sub_mem _ (Work.Coherence.self_mem_zSpan hξ)
            (Work.Coherence.self_mem_zSpan hχ₀T)
        · rw [Pi.sub_apply, hdegT ξ hξ, sub_self]
      exact Work.Coherence.coherent_of_norm_two_lift (hOrth.mono hTS) hχ₀T hdegT
        (by rw [hχ₀deg]; exact Work.CharCore.irrDeg_ne_zero (hIrr χ₀ hχ₀))
        ⟨fun α hα β hβ => hτ.inner_eq α (Work.Coherence.zSpan0_mono hTS hα) β
          (Work.Coherence.zSpan0_mono hTS hβ)⟩
        (fun ξ hξ => (hτV (ξ - χ₀) (Work.Coherence.zSpan0_mono hTS (hmem0 ξ hξ))).1)
        (fun ξ hξ => (hτV (ξ - χ₀) (Work.Coherence.zSpan0_mono hTS (hmem0 ξ hξ))).2)
        hcard2
  -- the degree-downward induction
  have key : ∀ n : ℕ, ∀ A : Finset (H → ℂ), A.card = n → A ⊆ S → T ⊆ A →
      (∀ ξ ∈ A, ∀ ζ ∈ S, Work.CharCore.irrDeg ζ < Work.CharCore.irrDeg ξ → ζ ∈ A) →
      Work.Coherence.Coherent A τ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A hAcard hAS hTA hdown
      by_cases hAT : A \ T = ∅
      · -- `A = T`: the base case
        have hAeqT : A = T := by
          refine Finset.Subset.antisymm ?_ hTA
          intro ξ hξ
          by_contra hξT
          have hm : ξ ∈ A \ T := Finset.mem_sdiff.mpr ⟨hξ, hξT⟩
          rw [hAT] at hm
          exact Finset.notMem_empty ξ hm
        rw [hAeqT]; exact hbase
      · -- pick a maximal-degree element of `A ∖ T`
        obtain ⟨χ, hχAT, hχmax⟩ :=
          Finset.exists_max_image (A \ T) Work.CharCore.irrDeg
            (Finset.nonempty_iff_ne_empty.mpr hAT)
        have hχA : χ ∈ A := (Finset.mem_sdiff.mp hχAT).1
        have hχT : χ ∉ T := (Finset.mem_sdiff.mp hχAT).2
        have hχS : χ ∈ S := hAS hχA
        -- `χ(1) > χ₀(1)`
        have hχgt : Work.CharCore.irrDeg χ₀ < Work.CharCore.irrDeg χ :=
          Nat.lt_of_le_of_ne (hmin χ hχS) fun hcontra =>
            hχT ((hmemT χ).mpr ⟨hχS, hcontra.symm⟩)
        -- the induction hypothesis on `A ∖ {χ}`
        have hA0card : (A.erase χ).card < n := by
          have hpos : 0 < A.card := Finset.card_pos.mpr ⟨χ, hχA⟩
          rw [Finset.card_erase_of_mem hχA, hAcard]
          omega
        have hA0S : A.erase χ ⊆ S := fun ξ hξ => hAS (Finset.mem_of_mem_erase hξ)
        have hTA0 : T ⊆ A.erase χ := by
          intro ξ hξ
          rw [Finset.mem_erase]
          exact ⟨fun h => hχT (h ▸ hξ), hTA hξ⟩
        have hdown0 : ∀ ξ ∈ A.erase χ, ∀ ζ ∈ S,
            Work.CharCore.irrDeg ζ < Work.CharCore.irrDeg ξ → ζ ∈ A.erase χ := by
          intro ξ hξ ζ hζS hlt
          have hξA : ξ ∈ A := Finset.mem_of_mem_erase hξ
          have hζA : ζ ∈ A := hdown ξ hξA ζ hζS hlt
          rw [Finset.mem_erase]
          refine ⟨?_, hζA⟩
          intro hζχ
          rw [hζχ] at hlt
          have hξne : ξ ∉ T := by
            intro hξT
            have h1 : Work.CharCore.irrDeg ξ = Work.CharCore.irrDeg χ₀ :=
              ((hmemT ξ).mp hξT).2
            have h2 : Work.CharCore.irrDeg χ < Work.CharCore.irrDeg χ₀ := by
              rw [← h1]; exact hlt
            exact absurd hχgt (not_lt.mpr (le_of_lt h2))
          exact absurd (hχmax ξ (Finset.mem_sdiff.mpr ⟨hξA, hξne⟩)) (not_le.mpr hlt)
        have hcohA0 : Work.Coherence.Coherent (A.erase χ) τ :=
          ih (A.erase χ).card hA0card (A.erase χ) rfl hA0S hTA0 hdown0
        -- reassemble `A = (A ∖ {χ}) ∪ {χ}`
        have hunion : A.erase χ ∪ {χ} = A := by
          rw [Finset.union_singleton, Finset.insert_erase hχA]
        have hIrr' : ∀ ξ ∈ A.erase χ ∪ {χ}, ξ ∈ Work.CharCore.Irr H := by
          intro ξ hξ
          exact hIrr ξ (hAS (by rwa [hunion] at hξ))
        have hτ' : Work.Coherence.IsometryOn (A.erase χ ∪ {χ}) τ := by
          rw [hunion]
          exact ⟨fun α hα β hβ => hτ.inner_eq α (Work.Coherence.zSpan0_mono hAS hα)
            β (Work.Coherence.zSpan0_mono hAS hβ)⟩
        have hτV' : ∀ α ∈ Work.Coherence.ZSpan0 (A.erase χ ∪ {χ}),
            Work.Coherence.IsVChar (τ α) ∧ τ α 1 = 0 := by
          intro α hα
          rw [hunion] at hα
          exact hτV α (Work.Coherence.zSpan0_mono hAS hα)
        have hpsi : ∃ ψ ∈ A.erase χ, ∃ d : ℕ, χ 1 = (d : ℂ) * ψ 1 ∧
            2 * Work.CharCore.irrDeg ψ * Work.CharCore.irrDeg χ
              < ∑ ξ ∈ A.erase χ, (Work.CharCore.irrDeg ξ) ^ 2 := by
          obtain ⟨d, hd⟩ := hdiv χ hχS
          refine ⟨χ₀, ?_, d, hd, ?_⟩
          · rw [Finset.mem_erase]
            exact ⟨fun h => hχT (h ▸ hχ₀T), hTA hχ₀T⟩
          · refine lt_of_lt_of_le (hineq χ hχS hχgt) ?_
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun ξ _ _ => Nat.zero_le _)
            intro ξ hξ
            obtain ⟨hξS, hlt⟩ := Finset.mem_filter.mp hξ
            have hξA : ξ ∈ A := hdown χ hχA ξ hξS hlt
            rw [Finset.mem_erase]
            exact ⟨fun h => absurd (h ▸ hlt) (lt_irrefl _), hξA⟩
        have hfin : Work.Coherence.Coherent (A.erase χ ∪ {χ}) τ :=
          coherent_union_singleton (Finset.notMem_erase χ A) hIrr' hτ' hτV' hcohA0 hpsi
        rwa [hunion] at hfin
  exact key S.card S rfl (fun _ h => h) (fun ξ hξ => hTS hξ) (fun ξ _ ζ hζ _ => hζ)

end

end Work.FeitSibley.Coherence
