import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

/-! ## The helper bookkeeping for the trigger-place argument

The main lemma `swTriggerPlace` is the "hBc" step of `ZSplit.sw_conjuncts_five_six`, run at the
pair of times `(i, j)` of a `HistInv`-history: a place at which the sum `z_i + z_j` is ramified is
`K`-conjugate to `Q_i` or to `Q_j`.  The proof is a case analysis on the `K`-class of `B` relative
to the (unique) escape prime `Q_l` whose `k`-place is that of `B`:

* `swTrigGesKConj_trans`, `swTrigGesKConj_symm` — `K`-conjugacy is an equivalence relation;
* `swTrigHist_conj_unique` — among the escape primes, the one `k`-conjugate to `B` is unique
  (`hist_escapes_not_conj`);
* `swTrigBlockExcl` — a place `B` `k`-conjugate to `Q_l` is not `K`-conjugate to any block of the
  place set `T_m` as soon as `m ≤ l` (the exclusion clause of `HistInv` plus `hist_escapes_not_conj`);
  this is what feeds the confinement conjunct (the eighth of `HistInv`);
* `swTrigBlockPresc` — at a block `A` of `T_n` lying in the `k`-place of `Q_l` (`l < n`), the
  stage-`n` prescription collapses: `z_n` vanishes at `A` if `A` is the `K`-class of `Q_l`, and
  equals `-z_l` at a sibling;
* `swTrigPrescTransfer` — the transfer of a prescribed value from a block to an arbitrary place of
  the same `K`-class (`additive_conj_invariant`). -/

/-- `K`-conjugacy of places is transitive. -/
theorem swTrigGesKConj_trans {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) {A B C : ValuationSubring Ω}
    (h1 : Work.SSGRoute.gesKConj K A B) (h2 : Work.SSGRoute.gesKConj K B C) :
    Work.SSGRoute.gesKConj K A C := by
  obtain ⟨τ, hτK, hτ⟩ := h1
  obtain ⟨σ, hσK, hσ⟩ := h2
  exact ⟨σ * τ, K.fixingSubgroup.mul_mem hσK hτK, by rw [mul_smul, hτ, hσ]⟩

/-- `K`-conjugacy of places is symmetric. -/
theorem swTrigGesKConj_symm {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) {A B : ValuationSubring Ω}
    (h : Work.SSGRoute.gesKConj K A B) : Work.SSGRoute.gesKConj K B A := by
  obtain ⟨τ, hτK, hτ⟩ := h
  exact ⟨τ⁻¹, K.fixingSubgroup.inv_mem hτK, by rw [← hτ, inv_smul_smul]⟩

/-- `K`-conjugacy implies `k`-conjugacy. -/
theorem swTrigGesKConj_imp_conjPlace {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) {A B : ValuationSubring Ω}
    (h : Work.SSGRoute.gesKConj K A B) : SSGRoute.IsConjPlace k A B := by
  obtain ⟨τ, -, hτ⟩ := h
  exact ⟨τ, hτ⟩

/-- **The escape prime whose `k`-place is that of `B` is unique.** -/
theorem swTrigHist_conj_unique {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (f : ℕ → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)))
    (hf : HistInv K N S y f) {m l : ℕ} {B : ValuationSubring Ω}
    (hm : SSGRoute.IsConjPlace k ((f m).1) B) (hl : SSGRoute.IsConjPlace k ((f l).1) B) :
    m = l := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hist_escapes_not_conj K N S y f hf hlt
      (SSGRoute.isConjPlace_trans hm (SSGRoute.isConjPlace_symm hl))
  · exact hist_escapes_not_conj K N S y f hf hgt
      (SSGRoute.isConjPlace_trans hl (SSGRoute.isConjPlace_symm hm))

/-- **A place `k`-conjugate to `Q_l` is not `K`-conjugate to any block of `T_m` for `m ≤ l`.** -/
theorem swTrigBlockExcl {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (f : ℕ → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)))
    (hf : HistInv K N S y f) {m l : ℕ} (hml : m ≤ l) {B : ValuationSubring Ω}
    (hB : SSGRoute.IsConjPlace k ((f l).1) B) :
    ∀ A ∈ histPlaces K S (fun t : Fin m => f t), ¬ Work.SSGRoute.gesKConj K A B := by
  classical
  intro A hA hKconj
  obtain ⟨τ, -, hτ⟩ := hKconj
  have hAB : SSGRoute.IsConjPlace k A B := ⟨τ, hτ⟩
  have hAQl : SSGRoute.IsConjPlace k A ((f l).1) :=
    SSGRoute.isConjPlace_trans hAB (SSGRoute.isConjPlace_symm hB)
  rcases histPlaces_mem_conjPlace (p := p) K S (fun t : Fin m => f t) hA with
    ⟨A₀, hA₀, hA₀A⟩ | ⟨m', hm'A⟩
  · have hA₀Ql : SSGRoute.IsConjPlace k A₀ ((f l).1) :=
      SSGRoute.isConjPlace_trans hA₀A hAQl
    obtain ⟨A'', hA'', hKA''⟩ := kleadReps_covers K S hA₀ hA₀Ql
    have hmem : A'' ∈ histPlaces K S (fun t : Fin l => f t) :=
      Finset.mem_union_left _ hA''
    exact hf.2.2.2.1 l A'' hmem hKA''
  · have hm'B : SSGRoute.IsConjPlace k ((f (m' : ℕ)).1) B :=
      SSGRoute.isConjPlace_trans hm'A hAB
    have heq : (m' : ℕ) = l := swTrigHist_conj_unique K N S y f hf hm'B hB
    have hlt : (m' : ℕ) < l := lt_of_lt_of_le m'.2 hml
    exact absurd heq (ne_of_lt hlt)

/-- **The prescription at a block in the `k`-place of a live escape prime.**  For `l < n`,
`A ∈ T_n` lying in the `k`-place of `Q_l` (and `k`-conjugate to no *other* escape prime):

* if `A` is the `K`-class of `Q_l` itself, the stage-`n` class vanishes on the local group of `A`;
* if `A` is a sibling of `Q_l`, the stage-`n` class equals `-z_l` there. -/
theorem swTrigBlockPresc {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (f : ℕ → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)))
    (hf : HistInv K N S y f) {n l : ℕ} (hln : l < n) {A : ValuationSubring Ω}
    (hAmem : A ∈ histPlaces K S (fun t : Fin n => f t))
    (hAconj : SSGRoute.IsConjPlace k ((f l).1) A)
    (huniq : ∀ m : Fin n, m ≠ ⟨l, hln⟩ → ¬ SSGRoute.IsConjPlace k ((f (m : ℕ)).1) A) :
    (Work.SSGRoute.gesKConj K ((f l).1) A →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, ((f n).2) σ = 0) ∧
    (¬ Work.SSGRoute.gesKConj K ((f l).1) A →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
          ((f n).2) σ = - ((f l).2) σ) := by
  classical
  have hsum : ∀ (τ : Ω ≃ₐ[k] Ω),
      histDatum K y (fun j : Fin n => f j) A τ
        = correctionDatum K (fun σ => (2 : ZMod p)⁻¹ * y σ) ((f l).2) ((f l).1) A τ := by
    intro τ
    unfold histDatum
    refine Finset.sum_eq_single (⟨l, hln⟩ : Fin n) ?_ ?_
    · intro m _ hm
      have hz := correctionDatum_eq_zero_of_not_conjPlace (p := p)
        K (fun σ => (2 : ZMod p)⁻¹ * y σ) ((f m).2) ((f m).1) A (huniq m hm)
      rw [hz]
      rfl
    · intro hnot
      exact absurd (Finset.mem_univ (⟨l, hln⟩ : Fin n)) hnot
  constructor
  · intro hconj σ hσ
    have hpres := hf.2.2.2.2.2.2.1 n A hAmem σ hσ
    rw [hpres, hsum σ]
    simp only [correctionDatum, if_pos hconj]
    ring
  · intro hconj σ hσ
    have hpres := hf.2.2.2.2.2.2.1 n A hAmem σ hσ
    rw [hpres, hsum σ]
    simp only [correctionDatum, if_neg hconj, if_pos hAconj]
    ring

/-- **Transfer of a prescribed value along `K`-conjugacy of the place.**  If `z` and `F` are both
additive on `K.fixingSubgroup` and `z = F` on the local group of `A`, then `z = F` on the local group
of every `K`-conjugate `B` of `A` (`additive_conj_invariant`). -/
theorem swTrigPrescTransfer {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) {A B : ValuationSubring Ω}
    (hAB : Work.SSGRoute.gesKConj K A B)
    (z F : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hz : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (hF : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, F (g * h) = F g + F h)
    (h : ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z σ = F σ) :
    ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, z σ = F σ := by
  intro σ hσ
  obtain ⟨τ, hτK, hτA⟩ := hAB
  have hτiK : τ⁻¹ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hτK
  have hσK : σ ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hσ).2
  have hσB : σ ∈ SSGRoute.decomp k B := (Subgroup.mem_inf.mp hσ).1
  set σ' : Ω ≃ₐ[k] Ω := τ⁻¹ * σ * τ with hσ'def
  have hσ'K : σ' ∈ K.fixingSubgroup := by
    rw [hσ'def]
    exact K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem hτiK hσK) hτK
  have hσ'A : σ' ∈ SSGRoute.decomp k A := by
    have hBA : τ⁻¹ • B = A := by rw [← hτA, inv_smul_smul]
    show σ' • A = A
    rw [hσ'def, mul_smul, mul_smul, hτA, hσB, hBA]
  have hσeq : τ * σ' * τ⁻¹ = σ := by rw [hσ'def]; group
  have hz_conj : z σ = z σ' := by
    rw [← hσeq]
    exact additive_conj_invariant K z hz hτK hσ'K
  have hF_conj : F σ = F σ' := by
    rw [← hσeq]
    exact additive_conj_invariant K F hF hτK hσ'K
  calc z σ = z σ' := hz_conj
    _ = F σ' := h (σ') (Subgroup.mem_inf.mpr ⟨hσ'A, hσ'K⟩)
    _ = F σ := hF_conj.symm

/-- **The trigger places of clause 3 are the escape primes.**  If `B` is a finite place outside `cs(S)`, split in `N`, at which the sum of the two live classes is *ramified* (i.e. some inertia element of its local group has nonzero value), then `B` is `K`-conjugate to `Q_i` or to `Q_j`.

Proof plan: contraposing `hist_sum_kills_inertia` (proved in `swCoreDefs`) gives `B` `k`-conjugate to some `Q_l` with `l ≤ j`.  For `l ∉ {i,j}`:
* own `K`-prime of `Q_l`, `l < j`: the stage-`j` prescription at the block `Q_l ∈ histPlaces K S (f|j)` gives `z_j ≡ 0` there (the correction datum collapses to `-½y` by `hist_escapes_not_conj`), and `z_i ≡ 0` by the same argument when `l < i`, by the *confinement* conjunct (eighth conjunct of `HistInv`) when `i < l < j`;
* sibling `K`-prime of `Q_l`: the stage-`j` prescription gives `z_j ≡ -z_l` there, and `z_l` kills the inertia by confinement, so the sum does too; the confinement at stage `i` handles `z_i`;
* siblings of `Q_j` (no prescription available, since `Q_j ∉ histPlaces K S (f|j)`): both summands kill the inertia by the confinement conjuncts at stages `i` and `j`.
In every case the transfer from a block representative to an arbitrary `Ω`-place of the same `K`-class uses `additive_conj_invariant`.  (`IsSplitIn k N B` is not needed for the conclusion; it is kept because the caller has it.)  The step is the same as the (unexported) `hBc` step inside the proved `ZSplit.sw_conjuncts_five_six`. -/
theorem swTriggerPlace {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (f : ℕ → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)))
    (hf : Work.SSGRoute.ZDataMup.HistInv K N S y f) {i j : ℕ} (hij : i < j) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
      SSGRoute.IsSplitIn k N B →
      (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧
        ((f i).2 σ + (f j).2 σ) ≠ 0) →
      Work.SSGRoute.gesKConj K ((f i).1) B ∨ Work.SSGRoute.gesKConj K ((f j).1) B := by
  classical
  intro B hBfin hSB _hsplit hram
  by_contra hgoal
  rw [not_or] at hgoal
  obtain ⟨hQinot, hQjnot⟩ := hgoal
  obtain ⟨σ, hσI, hσK, hσne⟩ := hram
  have hσB : σ ∈ SSGRoute.decomp k B := hσI.1
  -- Contraposing the confinement of the sum: `B` is `k`-conjugate to some escape prime `Q_l`, `l ≤ j`.
  have hl : ∃ l : ℕ, l ≤ j ∧ SSGRoute.IsConjPlace k ((f l).1) B := by
    by_contra h
    push_neg at h
    exact hσne (hist_sum_kills_inertia K N S y f hf hij B hBfin hSB h σ hσK hσI)
  obtain ⟨l, hlj, hconj_l⟩ := hl
  have huniqB : ∀ a b : ℕ, SSGRoute.IsConjPlace k ((f a).1) B →
      SSGRoute.IsConjPlace k ((f b).1) B → a = b :=
    fun a b ha hb => swTrigHist_conj_unique K N S y f hf ha hb
  -- It suffices to show that the sum vanishes at the ramified element `σ`.
  have hzero : ((f i).2) σ + ((f j).2) σ = 0 := by
    by_cases hlj' : l = j
    · -- `l = j`: no block of `T_i` or `T_j` meets the `K`-class of `B`, so both stages are confined.
      have hconj_j : SSGRoute.IsConjPlace k ((f j).1) B := hlj' ▸ hconj_l
      have hexcl_j := swTrigBlockExcl K N S y f hf (le_rfl : j ≤ j) hconj_j
      have hexcl_i := swTrigBlockExcl K N S y f hf (le_of_lt hij) hconj_j
      rw [hf.2.2.2.2.2.2.2 i B hBfin hexcl_i hQinot σ hσK hσI,
        hf.2.2.2.2.2.2.2 j B hBfin hexcl_j hQjnot σ hσK hσI, add_zero]
    · have hljl : l < j := lt_of_le_of_ne hlj hlj'
      -- A block representative `A` of the `K`-class of `B` above the `k`-place of `Q_l`.
      obtain ⟨A, hAlead, hKAB⟩ :=
        kleadReps_covers K ({((f l).1)} : Finset (ValuationSubring Ω))
          (Finset.mem_singleton_self _) hconj_l
      have hAconj : SSGRoute.IsConjPlace k ((f l).1) A :=
        SSGRoute.isConjPlace_trans hconj_l
          (SSGRoute.isConjPlace_symm (swTrigGesKConj_imp_conjPlace K hKAB))
      have hAmem_j : A ∈ histPlaces K S (fun t : Fin j => f t) :=
        Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨⟨l, hljl⟩, Finset.mem_univ _, hAlead⟩)
      -- `A` is `k`-conjugate to no escape prime other than `Q_l`.
      have huniqAt : ∀ (n : ℕ) (hln : l < n), ∀ m : Fin n, m ≠ ⟨l, hln⟩ →
          ¬ SSGRoute.IsConjPlace k ((f (m : ℕ)).1) A := by
        intro n hln m hm hconj
        have hB' : SSGRoute.IsConjPlace k ((f (m : ℕ)).1) B :=
          SSGRoute.isConjPlace_trans hconj (swTrigGesKConj_imp_conjPlace K hKAB)
        exact hm (Fin.ext (huniqB (m : ℕ) l hB' hconj_l))
      by_cases hown : Work.SSGRoute.gesKConj K ((f l).1) B
      · -- `B` lies in the `K`-class of `Q_l` itself.
        have hownA : Work.SSGRoute.gesKConj K ((f l).1) A :=
          swTrigGesKConj_trans K hown (swTrigGesKConj_symm K hKAB)
        have hzjA := (swTrigBlockPresc K N S y f hf hljl hAmem_j hAconj (huniqAt j hljl)).1 hownA
        have hzjB : ∀ τ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, ((f j).2) τ = 0 :=
          swTrigPrescTransfer K hKAB ((f j).2) (fun _ => 0) (hf.2.2.2.2.2.1 j)
            (by intro g hg h hh; simp) hzjA
        have hzi : ((f i).2) σ = 0 := by
          rcases lt_trichotomy l i with hli | hli | hli
          · -- `l < i`: the stage-`i` prescription at `A`
            have hAmem_i : A ∈ histPlaces K S (fun t : Fin i => f t) :=
              Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨⟨l, hli⟩, Finset.mem_univ _, hAlead⟩)
            have hziA := (swTrigBlockPresc K N S y f hf hli hAmem_i hAconj (huniqAt i hli)).1 hownA
            exact swTrigPrescTransfer K hKAB ((f i).2) (fun _ => 0) (hf.2.2.2.2.2.1 i)
              (by intro g hg h hh; simp) hziA σ (Subgroup.mem_inf.mpr ⟨hσB, hσK⟩)
          · -- `l = i`: `B` is `K`-conjugate to `Q_i`, contrary to the assumption
            exact absurd (hli ▸ hown) hQinot
          · -- `i < l`: the stage-`i` confinement
            have hexcl_i := swTrigBlockExcl K N S y f hf (le_of_lt hli) hconj_l
            exact hf.2.2.2.2.2.2.2 i B hBfin hexcl_i hQinot σ hσK hσI
        rw [hzi, hzjB σ (Subgroup.mem_inf.mpr ⟨hσB, hσK⟩), add_zero]
      · -- `B` is a *sibling* of `Q_l` (`k`-conjugate but not `K`-conjugate).
        have hownA : ¬ Work.SSGRoute.gesKConj K ((f l).1) A :=
          fun hc => hown (swTrigGesKConj_trans K hc hKAB)
        have hzjA := (swTrigBlockPresc K N S y f hf hljl hAmem_j hAconj (huniqAt j hljl)).2 hownA
        have hzjB : ∀ τ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
            ((f j).2) τ = - ((f l).2) τ :=
          swTrigPrescTransfer K hKAB ((f j).2) (fun τ => - ((f l).2) τ) (hf.2.2.2.2.2.1 j)
            (fun g hg h hh => by rw [hf.2.2.2.2.2.1 l g hg h hh]; ring) hzjA
        -- `z_l` kills the inertia at `B` by the confinement at stage `l`.
        have hexcl_l := swTrigBlockExcl K N S y f hf (le_rfl : l ≤ l) hconj_l
        have hzl : ((f l).2) σ = 0 :=
          hf.2.2.2.2.2.2.2 l B hBfin hexcl_l hown σ hσK hσI
        have hzj : ((f j).2) σ = 0 := by
          rw [hzjB σ (Subgroup.mem_inf.mpr ⟨hσB, hσK⟩), hzl, neg_zero]
        have hzi : ((f i).2) σ = 0 := by
          rcases lt_trichotomy l i with hli | hli | hli
          · -- `l < i`: the stage-`i` prescription at the sibling `A`
            have hAmem_i : A ∈ histPlaces K S (fun t : Fin i => f t) :=
              Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨⟨l, hli⟩, Finset.mem_univ _, hAlead⟩)
            have hziA := (swTrigBlockPresc K N S y f hf hli hAmem_i hAconj (huniqAt i hli)).2 hownA
            have hziB := swTrigPrescTransfer K hKAB ((f i).2) (fun τ => - ((f l).2) τ)
              (hf.2.2.2.2.2.1 i)
              (fun g hg h hh => by rw [hf.2.2.2.2.2.1 l g hg h hh]; ring) hziA
            rw [hziB σ (Subgroup.mem_inf.mpr ⟨hσB, hσK⟩), hzl, neg_zero]
          · -- `l = i`: the stage-`i` class is the stage-`l` class, which kills the inertia
            exact hli ▸ hzl
          · -- `i < l`: the stage-`i` confinement
            have hexcl_i := swTrigBlockExcl K N S y f hf (le_of_lt hli) hconj_l
            exact hf.2.2.2.2.2.2.2 i B hBfin hexcl_i hQinot σ hσK hσI
        rw [hzi, hzj, add_zero]
  exact absurd hzero hσne

end Work.SSGRoute.ZDataMup
