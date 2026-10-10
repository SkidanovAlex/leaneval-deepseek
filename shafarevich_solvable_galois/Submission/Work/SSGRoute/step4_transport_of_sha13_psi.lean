import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.step4_transport_of_sha13
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/SSGRoute/DESIGN.md and the orchestrator's addendum DESIGN2 (copied as
Submission/Work/SSGRoute/DESIGN2.md). Interfaces: Submission/Work/SSGRoute/Interfaces.lean
(namespace SSGRoute; do NOT edit). NK.* CFT library available. Siblings in parallel.

# step4_transport_of_sha13_psi  (corrects `step4_transport_of_sha13`)

**The bug.** `step4_transport_of_sha13` applies Theorem 13 with `Λ := field of φ` (`hΛker : φ.ker = …`,
i.e. `N_τ`).
- Then `x` may ramify at places split in `N_τ` where `ψ` is *nontrivial* (an unramified Frobenius
  value).
- There the twist has local image `⟨ψ(Frob)+x(Frob), x(τ)⟩ ⊆ E`, which can be 2-dimensional.
- So Step4Input items (5)/(6) (local cyclicity) are underivable. This is the prover's "no plan".

SW p.31 applies Thm 13 with `Λ = N^n_{τ+1}` (the field of **ψ**, i.e. the step-3 solution) and
`T ⊇ Ram(N^n_{τ+1}/k)`: "we get new ramification only at places which are completely decomposed in
N_{τ+1}".

**Statement.** The same hypotheses with `hΛker : ψ.ker = Λ.fixingSubgroup` (`ψ` at level `τ+1`).
Conclusions:
- `x` is a coboundary at every `T¹` place;
- a place where `x` ramifies in `G_K` is not conjugate to `S`, **and ψ is trivial on its decomposition
  group**.

**Proof.** As in the existing file.
- T¹ places: `Ram(K) ⊆ Ram(Λ)` and places over `p` are `S`-conjugate (`hSram`). Use `hxnot`, or `hxsplit`
  together with `hy0` on all conjugates `sec s⁻¹ A`.
- Ramified `x`:
  - if `A` is `S`-conjugate, `x ≡ cor y` on `D_A`, with `y = 0` on inertia (`hyT`);
  - trivial action on `G_K` makes the coboundary vanish on `σ ∈ G_K`, so `x σ = 0`, a contradiction;
  - so `A` is not `S`-conjugate, and `hxinertia` forces `IsSplitIn ℚ Λ A`, i.e.
    `D_A ≤ Λ.fixingSubgroup = ψ.ker`.

**Imports.** `scholz_succ_of_properStage`, `place_basics`, `local_transport`, `CohomologicalShrinking.All`.

This file proves the transport argument of `step4_transport_of_sha13` in the form needed at level
`τ + 1`: the level-`τ` solution `φ : G_ℚ →* F(n)^{(i,j)} ⋊ G` of the original statement is replaced
by an *arbitrary* group-valued homomorphism `ψ : G_ℚ →* G` — only its kernel and its values on a
decomposition group are ever used.  The general lemma is `step4_transport_general`; the requested
statement is its instance `G := flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2`.
-/

namespace Work.SSGRoute

open _root_.SSGRoute
open Work.CohomologicalShrinking

/-- **Transport of the local clauses of `SSGRoute.shafarevich_theorem13`** at the places of a set `S`
(one per prime, containing the places over `Ram(Λ/ℚ)` and over `p`), in the form used at the level
`τ + 1` of the induction: the solution `ψ` at level `τ + 1` is used only through its kernel
`ψ.ker = G_Λ` and through its values on decomposition groups.

The two global conclusions are: `x` is a coboundary on the decomposition group of every place over
`Ram(K/ℚ) ∪ {p}`; and if `x` ramifies at a place `A` over `K`, then `A` is not conjugate to any
element of `S` and `ψ` is trivial on the whole decomposition group of `A` (so that `A` is completely
decomposed in the field of `ψ`; this is exactly what makes the twist cyclic there). -/
theorem step4_transport_general (p : ℕ) [Fact p.Prime]
    (K Λ : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    [FiniteDimensional ℚ Λ] [Normal ℚ Λ] (hKΛ : K ≤ Λ) (n i j : ℕ)
    (G : Type*) [Group G]
    (ψ : SSGRoute.GalQ →* G)
    (hΛker : ψ.ker = Λ.fixingSubgroup)
    (S : Finset (ValuationSubring SSGRoute.QBar)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace ℚ A)
    (hSram : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (SSGRoute.IsRamifiedIn ℚ Λ B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B)
    (sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ) (hsec : ∀ s, AlgEquiv.restrictNormalHom K (sec s) = s)
    (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hyT : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia ℚ B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B) →
      (¬ SSGRoute.IsSplitIn ℚ K B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ B → y σ = 0)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hxcoc : SSGRoute.IsCocycleOn (AlgEquiv.restrictNormalHom K) ⊤ x)
    (hxsplit : ∀ A ∈ S, SSGRoute.IsSplitIn ℚ K A →
      SSGRoute.IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (SSGRoute.decomp ℚ A)
        (fun δ => x δ - ∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)))
    (hxnot : ∀ A ∈ S, ¬ SSGRoute.IsSplitIn ℚ K A →
      SSGRoute.IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (SSGRoute.decomp ℚ A) x)
    (hxinertia : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace ℚ A B) → ¬ SSGRoute.IsSplitIn ℚ Λ B →
      ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ B σ → x σ = 0) :
    (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
      SSGRoute.IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (SSGRoute.decomp ℚ A) x) ∧
    (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ x σ ≠ 0) →
      (∀ A₀ ∈ S, ¬ SSGRoute.IsConjPlace ℚ A₀ A) ∧ ∀ σ ∈ SSGRoute.decomp ℚ A, ψ σ = 1) := by
  -- ramification in `K` implies ramification in `Λ`
  have hram_mono : ∀ B : ValuationSubring SSGRoute.QBar,
      IsRamifiedIn ℚ K B → IsRamifiedIn ℚ Λ B := by
    rintro B ⟨σ, hI, hσ⟩
    exact ⟨σ, hI, fun hmem => hσ (IntermediateField.fixingSubgroup_le hKΛ hmem)⟩
  -- every `T¹`-place is conjugate to an element of `S`
  have hT1_conj : ∀ B : ValuationSubring SSGRoute.QBar, IsT1Place p K B →
      ∃ A ∈ S, IsConjPlace ℚ A B := by
    rintro B ⟨hBfin, hval | hram⟩
    · exact hSram B hBfin (Or.inr hval)
    · exact hSram B hBfin (Or.inl (hram_mono B hram))
  refine ⟨?_, ?_⟩
  · -- ## Part 1: `x` is a coboundary on the decomposition group of every place of `T¹`
    intro A hA
    obtain ⟨hAfin, hAcond⟩ := hA
    obtain ⟨A', hA'S, τ, hτ⟩ := hT1_conj A ⟨hAfin, hAcond⟩
    -- a coboundary on `D_{A'}` transports to the conjugate place `A = τ • A'`
    have transfer : IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (decomp ℚ A') x →
        IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (decomp ℚ A) x := by
      intro hcob
      have h := isCoboundaryOn_map_conj (AlgEquiv.restrictNormalHom K) (decomp ℚ A') τ x
        hxcoc hcob
      rw [← decomp_conj A' τ, hτ] at h
      exact h
    by_cases hsplit : IsSplitIn ℚ K A'
    · -- `A'` splits completely in `K`: `x` and the formal corestriction agree on `D_{A'}`
      have hsplitA : IsSplitIn ℚ K A := hτ ▸ (step4_isSplitIn_smul K A' τ).mpr hsplit
      have hnotram : ¬ IsRamifiedIn ℚ K A := by
        rintro ⟨σ, hσI, hσK⟩
        exact hσK (hsplitA hσI.1)
      have hvalA : A.valuation (p : SSGRoute.QBar) < 1 :=
        hAcond.elim id (fun h => absurd h hnotram)
      have hvalA' : A'.valuation (p : SSGRoute.QBar) < 1 :=
        (step4_smul_valuation_p_lt_one p A' τ).mp (hτ.symm ▸ hvalA)
      have hxzero : ∀ δ ∈ decomp ℚ A', x δ = 0 := by
        obtain ⟨m, hm⟩ := hxsplit A' hA'S hsplit
        intro δ hδ
        have h1 : x δ - (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s))
            = AlgEquiv.restrictNormalHom K δ • m - m := hm δ hδ
        have hact : AlgEquiv.restrictNormalHom K δ = 1 :=
          (step4_restrict_eq_one_iff K δ).mpr (hsplit hδ)
        have hX0 : (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)) = 0 :=
          step4_sum_smul_y_eq_zero_of_over_p p K n i j S sec hsec y hy0 A' (hSfin A' hA'S)
            ⟨A', hA'S, isConjPlace_refl A'⟩ hvalA' δ (hsplit hδ) hδ
        rw [hact, one_smul, hX0, sub_zero, sub_self] at h1
        exact h1
      exact transfer (step4_coboundary_of_eq_zero hxzero)
    · -- `A'` does not split completely in `K`
      exact transfer (hxnot A' hA'S hsplit)
  · -- ## Part 2: `x` can only ramify over `K` at places split completely in `Λ/ℚ`
    intro A hAfin hram
    obtain ⟨σ₀, hσ₀I, hσ₀K, hσ₀ne⟩ := hram
    have hσ₀D : σ₀ ∈ decomp ℚ A := hσ₀I.1
    have hσ₀act : AlgEquiv.restrictNormalHom K σ₀ = 1 :=
      (step4_restrict_eq_one_iff K σ₀).mpr hσ₀K
    -- `A` is not conjugate to any place of `S`
    have hnotconj : ¬ ∃ A' ∈ S, IsConjPlace ℚ A' A := by
      rintro ⟨A', hA'S, τ, hτ⟩
      by_cases hsplitK : IsSplitIn ℚ K A'
      · -- `x` agrees with the formal corestriction on `D_{A'}`, which kills the inertia of `A'`
        have hgrp : τ * (τ⁻¹ * σ₀ * τ) * τ⁻¹ = σ₀ := by group
        have hXi : ∀ δ ∈ decomp ℚ A', IsInertia ℚ A' δ →
            (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)) = 0 :=
          fun δ hδ hI => step4_sum_smul_y_eq_zero_of_inertia p K n i j S sec hsec y hyT
            A' (hSfin A' hA'S) ⟨A', hA'S, isConjPlace_refl A'⟩ δ (hsplitK hδ) hI
        obtain ⟨m, hm⟩ := hxsplit A' hA'S hsplitK
        have hxX : ∀ δ ∈ decomp ℚ A',
            x δ = ∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s) := by
          intro δ hδ
          have h1 : x δ - (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s))
              = AlgEquiv.restrictNormalHom K δ • m - m := hm δ hδ
          have hact : AlgEquiv.restrictNormalHom K δ = 1 :=
            (step4_restrict_eq_one_iff K δ).mpr (hsplitK hδ)
          rw [hact, one_smul, sub_self] at h1
          exact sub_eq_zero.mp h1
        -- the conjugate `τ⁻¹ σ₀ τ` lies in the inertia of `A'`, where `x` vanishes
        have hbI : IsInertia ℚ A' (τ⁻¹ * σ₀ * τ) :=
          (isInertia_conj A' τ (τ⁻¹ * σ₀ * τ)).mp (by rw [hgrp, hτ]; exact hσ₀I)
        have hxb : x (τ⁻¹ * σ₀ * τ) = 0 := by
          rw [hxX _ hbI.1, hXi _ hbI.1 hbI]
        have hkey : x σ₀ = x τ + AlgEquiv.restrictNormalHom K τ • x (τ⁻¹ * σ₀ * τ)
            - AlgEquiv.restrictNormalHom K σ₀ • x τ := by
          have h := step4_cocycle_conj hxcoc τ (τ⁻¹ * σ₀ * τ)
          rwa [hgrp] at h
        have hzero : x σ₀ = 0 := by
          rw [hkey]
          simp [hxb, hσ₀act]
        exact hσ₀ne hzero
      · -- `A'` does not split in `K`: `hxnot` gives a coboundary on the conjugate `D_A`
        have hcobA : IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (decomp ℚ A') x :=
          hxnot A' hA'S hsplitK
        have hcob : IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (decomp ℚ A) x := by
          have h := isCoboundaryOn_map_conj (AlgEquiv.restrictNormalHom K) (decomp ℚ A') τ x
            hxcoc hcobA
          rw [← decomp_conj A' τ, hτ] at h
          exact h
        obtain ⟨m, hm⟩ := hcob
        have h1 : x σ₀ = AlgEquiv.restrictNormalHom K σ₀ • m - m := hm σ₀ hσ₀D
        rw [hσ₀act, one_smul] at h1
        exact hσ₀ne (by rw [sub_self] at h1; exact h1)
    have hsplitΛ : IsSplitIn ℚ Λ A := by
      by_contra hnsplit
      exact hσ₀ne (hxinertia A hAfin (fun A' hA' hc => hnotconj ⟨A', hA', hc⟩) hnsplit σ₀ hσ₀I)
    refine ⟨fun A₀ hA₀S hc => hnotconj ⟨A₀, hA₀S, hc⟩, ?_⟩
    intro σ hσ
    have hσΛ : σ ∈ Λ.fixingSubgroup := hsplitΛ hσ
    have h1 : σ ∈ ψ.ker := by rw [hΛker]; exact hσΛ
    exact MonoidHom.mem_ker.mp h1

open _root_.SSGRoute
open Work.CohomologicalShrinking

theorem step4_transport_of_sha13_psi (p : ℕ) [Fact p.Prime]
    (K Λ : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    [FiniteDimensional ℚ Λ] [Normal ℚ Λ] (hKΛ : K ≤ Λ) (n i j : ℕ)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hΛker : ψ.ker = Λ.fixingSubgroup)
    (S : Finset (ValuationSubring SSGRoute.QBar)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace ℚ A)
    (hSram : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (SSGRoute.IsRamifiedIn ℚ Λ B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B)
    (sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ) (hsec : ∀ s, AlgEquiv.restrictNormalHom K (sec s) = s)
    (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hyT : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia ℚ B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B) →
      (¬ SSGRoute.IsSplitIn ℚ K B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ B → y σ = 0)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hxcoc : SSGRoute.IsCocycleOn (AlgEquiv.restrictNormalHom K) ⊤ x)
    (hxsplit : ∀ A ∈ S, SSGRoute.IsSplitIn ℚ K A →
      SSGRoute.IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (SSGRoute.decomp ℚ A)
        (fun δ => x δ - ∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)))
    (hxnot : ∀ A ∈ S, ¬ SSGRoute.IsSplitIn ℚ K A →
      SSGRoute.IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (SSGRoute.decomp ℚ A) x)
    (hxinertia : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace ℚ A B) → ¬ SSGRoute.IsSplitIn ℚ Λ B →
      ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ B σ → x σ = 0) :
    (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
      SSGRoute.IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (SSGRoute.decomp ℚ A) x) ∧
    (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ x σ ≠ 0) →
      (∀ A₀ ∈ S, ¬ SSGRoute.IsConjPlace ℚ A₀ A) ∧ ∀ σ ∈ SSGRoute.decomp ℚ A, ψ σ = 1) :=
  step4_transport_general p K Λ hKΛ n i j
    (flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2) ψ hΛker S hSfin hSram sec hsec
    y hyT hy0 x hxcoc hxsplit hxnot hxinertia

end Work.SSGRoute
