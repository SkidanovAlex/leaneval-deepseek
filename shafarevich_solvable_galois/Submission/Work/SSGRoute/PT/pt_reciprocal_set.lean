import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.PT.pt_counting_assembly
import Submission.Work.SSGRoute.PT.vanishingInertia_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The reciprocal set `S'` of Poitou–Tate reciprocity

`Work.SSGRoute.PT.pt_orthogonality_of_realizable` (the inclusion `V ⊆ W^⊥`) needs, for a global
locally constant cocycle `ε` of the primal Selmer module and a global class `b` of the relaxed
dual Selmer module, a finite set `S' ⊇ S` of one place per prime such that

* outside `S'` (up to conjugacy) no prime divides `p` or ramifies in `K/k`, and both `ε` and `b`
  vanish on inertia,
* at the places of `S' ∖ S`, `b` is a coboundary on the decomposition group.

Here we construct it.  The two mathematical inputs are

* `Work.SSGRoute.PT.vanishingInertia_finite` (a locally constant cocycle fails to vanish on inertia
  at only finitely many `G_k`-classes of places), and
* the primal/dual Selmer conditions themselves: at a place `B ∉ S` which is **not** split in `N`,
  `ε` vanishes on inertia, so a place where `ε` fails to vanish and is outside `S` must be
  *split* in `N`; and at a *split* place outside `S` the dual class `b` is a coboundary on the
  decomposition group, hence `0` there (the decomposition group acts trivially on the
  coefficients).  In particular `b` vanishes on inertia at every place outside `S`.

Hence it suffices to take `S'` = `S` together with the (finitely many classes of) places of
`S_ε` at which `ε` actually fails, keeping only those that are not conjugate to an element of `S`
and *are split*; the failing places outside `S` are split, so this keeps a representative of every
class of failing places.
-/

open scoped TensorProduct Pointwise
open Classical

namespace Work.SSGRoute.PT

noncomputable section

set_option linter.style.haveILetI false

section ReciprocalSet

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
  (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
  (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
    (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)

local instance : AddCommGroup (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : DistribMulAction (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance
local instance : SMulCommClass (K ≃ₐ[k] K) (ZMod p) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance

/-! ## Conjugation of places -/

/-- The decomposition group of a conjugate place. -/
theorem decomp_smul_eq_map_conj (A : ValuationSubring Ω) (g : Ω ≃ₐ[k] Ω) :
    SSGRoute.decomp k (g • A)
      = (SSGRoute.decomp k A).map (MulAut.conj g).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g A

/-- A normal subgroup is invariant under conjugation. -/
theorem map_conj_eq_self_of_normal {H : Subgroup (Ω ≃ₐ[k] Ω)} (hH : H.Normal)
    (g : Ω ≃ₐ[k] Ω) : H.map (MulAut.conj g).toMonoidHom = H := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact hH.conj_mem y hy g
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hH.conj_mem x hx g⁻¹, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

/-- Containment in a normal subgroup is invariant under conjugation of the subgroup. -/
theorem map_conj_le_iff_of_normal {H F : Subgroup (Ω ≃ₐ[k] Ω)} (hF : F.Normal)
    (g : Ω ≃ₐ[k] Ω) : H.map (MulAut.conj g).toMonoidHom ≤ F ↔ H ≤ F := by
  have h1 : F.map (MulAut.conj g).toMonoidHom = F := map_conj_eq_self_of_normal k Ω hF g
  have h2 : F.map (MulAut.conj g⁻¹).toMonoidHom = F :=
    map_conj_eq_self_of_normal k Ω hF g⁻¹
  constructor
  · intro h x hx
    have hmem : (MulAut.conj g).toMonoidHom x ∈ F :=
      h (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    have : x ∈ F.map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨(MulAut.conj g).toMonoidHom x, hmem, by
        simp [MulAut.conj_apply, mul_assoc]⟩
    rwa [h2] at this
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hmem : (MulAut.conj g).toMonoidHom x ∈ F.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, h hx, rfl⟩
    rwa [h1] at hmem

/-- Splitting completely in `N` is invariant under conjugation of the place. -/
theorem isSplitIn_conj {A : ValuationSubring Ω} {g : Ω ≃ₐ[k] Ω} :
    SSGRoute.IsSplitIn k N (g • A) ↔ SSGRoute.IsSplitIn k N A := by
  haveI : IsGalois k Ω := inferInstance
  haveI hNnorm : N.fixingSubgroup.Normal := inferInstance
  rw [SSGRoute.IsSplitIn, SSGRoute.IsSplitIn, decomp_smul_eq_map_conj k Ω A g]
  exact map_conj_le_iff_of_normal k Ω hNnorm g

/-- Ramification in a smaller normal extension implies ramification in a larger one. -/
theorem isRamifiedIn_mono (hKN : K ≤ N) {B : ValuationSubring Ω}
    (hB : SSGRoute.IsRamifiedIn k K B) : SSGRoute.IsRamifiedIn k N B := by
  obtain ⟨σ, hσI, hσK⟩ := hB
  refine ⟨σ, hσI, fun hσN => hσK ?_⟩
  exact IntermediateField.fixingSubgroup_le hKN hσN

/-! ## The dual class vanishes on inertia outside `S` -/

/-- At a place outside `S` which is split in `N`, the dual Selmer class `b` is `0` on the whole
decomposition group: it is a coboundary there and the decomposition group acts trivially. -/
theorem dualClass_eq_zero_on_decomp_of_split (hKN : K ≤ N)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : b ∈ dualSelmer p k Ω K N T M S) {B : ValuationSubring Ω}
    (hBfin : SSGRoute.IsFinPlace k B) (hB : ∀ A₀ ∈ S, ¬ SSGRoute.IsConjPlace k A₀ B)
    (hsplit : SSGRoute.IsSplitIn k N B) :
    ∀ σ ∈ SSGRoute.decomp k B, b σ = 0 := by
  obtain ⟨m, hm⟩ := hb.2.2.1 B hBfin hB hsplit
  intro σ hσ
  have hres : SSGRoute.res k K σ = 1 := by
    have hle : (N.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) ≤ K.fixingSubgroup :=
      IntermediateField.fixingSubgroup_le hKN
    have hker : σ ∈ (SSGRoute.res k K).ker := by
      rw [IntermediateField.restrictNormalHom_ker (E := K)]
      exact hle (hsplit hσ)
    exact MonoidHom.mem_ker.mp hker
  rw [hm σ hσ, hres, one_smul, sub_self]

/-- **The dual Selmer class vanishes on inertia outside `S`.** -/
theorem dualClass_inertia_eq_zero (hKN : K ≤ N)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : b ∈ dualSelmer p k Ω K N T M S) {B : ValuationSubring Ω}
    (hBfin : SSGRoute.IsFinPlace k B) (hB : ∀ A₀ ∈ S, ¬ SSGRoute.IsConjPlace k A₀ B) :
    ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → b σ = 0 := by
  intro σ hσ
  by_cases hsplit : SSGRoute.IsSplitIn k N B
  · exact dualClass_eq_zero_on_decomp_of_split (p := p) (k := k) (Ω := Ω) (K := K) (N := N)
      (T := T) (M := M) (S := S) hKN (b := b) hb hBfin hB hsplit σ hσ.1
  · exact hb.2.2.2 B hBfin hB hsplit σ hσ


/-! ## The reciprocal set -/

/-- **The reciprocal set `S'`.**  Given a global locally constant cocycle `ε` of the relaxed primal
Selmer module and a global locally constant cocycle `b` of the relaxed dual Selmer module, there is
a finite set `S' ⊇ S`, one place per prime, outside which neither `p` nor ramification in `K`
occurs and both `ε` and `b` vanish on inertia; and at every place of `S'` which is not conjugate to
an element of `S`, `b` is a coboundary on the decomposition group.

The set is `S` together with the places at which `ε` fails to vanish on inertia and which are not
conjugate to an element of `S` and are split in `N`; the primal Selmer condition forces every
failing place outside `S` to be split, so every failing class is represented. -/
theorem exists_reciprocal_set (hKN : K ≤ N)
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (ε : (Ω ≃ₐ[k] Ω) → M) (hε : ε ∈ primalSelmer p k Ω K N M S)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : b ∈ dualSelmer p k Ω K N T M S) :
    ∃ S' : Finset (ValuationSubring Ω),
      (∀ A ∈ S, A ∈ S') ∧
      (∀ A ∈ S', SSGRoute.IsFinPlace k A) ∧
      (∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
        ¬ B.valuation (p : Ω) < 1 ∧ ¬ SSGRoute.IsRamifiedIn k K B ∧
          ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → ε σ = 0 ∧ b σ = 0) ∧
      (∀ A ∈ S', (∀ A₀ ∈ S, ¬ SSGRoute.IsConjPlace k A₀ A) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b) := by
  classical
  obtain ⟨Sε, hSεfin, hSεdisj, hSεvanish⟩ :=
    vanishingInertia_finite (k := k) (Ω := Ω) (K := K) (M := M) ε hε.1 hε.2.1
  set F : Finset (ValuationSubring Ω) :=
    Sε.filter (fun A => (∀ A₀ ∈ S, ¬ SSGRoute.IsConjPlace k A₀ A) ∧ SSGRoute.IsSplitIn k N A)
    with hFdef
  have hFmem : ∀ A, A ∈ F ↔ (A ∈ Sε ∧ (∀ A₀ ∈ S, ¬ SSGRoute.IsConjPlace k A₀ A) ∧
      SSGRoute.IsSplitIn k N A) := fun A => by
    rw [hFdef, Finset.mem_filter]
  have hFsub : ∀ A ∈ F, A ∈ Sε := fun A hA => ((hFmem A).mp hA).1
  have hFS : ∀ A ∈ F, ∀ A₀ ∈ S, ¬ SSGRoute.IsConjPlace k A₀ A :=
    fun A hA => ((hFmem A).mp hA).2.1
  have hFsplit : ∀ A ∈ F, SSGRoute.IsSplitIn k N A := fun A hA => ((hFmem A).mp hA).2.2
  have hFfin : ∀ A ∈ F, SSGRoute.IsFinPlace k A := fun A hA => hSεfin A (hFsub A hA)
  have hFdisj : ∀ A ∈ F, ∀ B ∈ F, SSGRoute.IsConjPlace k A B → A = B :=
    fun A hA B hB h => hSεdisj A (hFsub A hA) B (hFsub B hB) h
  have hSsub : ∀ A ∈ S, A ∈ S ∪ F := fun A hA => Finset.mem_union_left _ hA
  have hSF : ∀ A ∈ S ∪ F, SSGRoute.IsFinPlace k A := by
    intro A hA
    rcases Finset.mem_union.mp hA with h | h
    · exact hSfin A h
    · exact hFfin A h
  have hSdisj' : ∀ A ∈ S ∪ F, ∀ B ∈ S ∪ F, SSGRoute.IsConjPlace k A B → A = B := by
    intro A hA B hB h
    rcases Finset.mem_union.mp hA with hA | hA <;> rcases Finset.mem_union.mp hB with hB | hB
    · exact hSdisj A hA B hB h
    · exact absurd h (hFS B hB A hA)
    · exact absurd (SSGRoute.isConjPlace_symm (k := k) h) (hFS A hA B hB)
    · exact hFdisj A hA B hB h
  have hconjS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S ∪ F, ¬ SSGRoute.IsConjPlace k A B) →
      ∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B :=
    fun B _ hB A hA hc => hB A (hSsub A hA) hc
  refine ⟨S ∪ F, hSsub, hSF, hSdisj', ?_, ?_⟩
  · intro B hBfin hBconj
    have hBS := hconjS B hBfin hBconj
    have hnotramN : ¬ SSGRoute.IsRamifiedIn k N B := by
      intro hr
      obtain ⟨A, hA, hc⟩ := hSram B hBfin (Or.inl hr)
      exact hBS A hA hc
    refine ⟨?_, ?_, ?_⟩
    · intro hv
      obtain ⟨A, hA, hc⟩ := hSram B hBfin (Or.inr hv)
      exact hBS A hA hc
    · intro hr
      exact hnotramN (isRamifiedIn_mono (k := k) (Ω := Ω) (K := K) (N := N) (hKN := hKN) hr)
    · intro σ hσ
      refine ⟨?_, ?_⟩
      · by_cases hsplit : SSGRoute.IsSplitIn k N B
        · by_contra hne
          have hex : ∃ A ∈ Sε, SSGRoute.IsConjPlace k A B := by
            by_contra h
            have h' : ∀ A ∈ Sε, ¬ SSGRoute.IsConjPlace k A B := by
              intro A hAε hc
              exact h ⟨A, hAε, hc⟩
            exact hne (hSεvanish B hBfin h' σ hσ)
          obtain ⟨A, hAε, hc⟩ := hex
          have hAcl : ∀ A₀ ∈ S, ¬ SSGRoute.IsConjPlace k A₀ A := by
            intro A₀ hA₀ hc₀
            exact hBconj A₀ (hSsub A₀ hA₀) (SSGRoute.isConjPlace_trans (k := k) hc₀ hc)
          have hAsp : SSGRoute.IsSplitIn k N A := by
            obtain ⟨g, hg⟩ := hc
            have hg' : SSGRoute.IsSplitIn k N (g • A) := by rw [hg]; exact hsplit
            exact (isSplitIn_conj (k := k) (Ω := Ω) (N := N) (A := A) (g := g)).mp hg'
          exact hBconj A (Finset.mem_union_right _
            ((hFmem A).mpr ⟨hAε, hAcl, hAsp⟩)) hc
        · exact hε.2.2 B hBfin hBS hsplit σ hσ
      · by_cases hsplit : SSGRoute.IsSplitIn k N B
        · exact dualClass_eq_zero_on_decomp_of_split (p := p) (k := k) (Ω := Ω) (K := K) (N := N)
            (T := T) (M := M) (S := S) hKN (b := b) hb hBfin hBS hsplit σ hσ.1
        · exact hb.2.2.2 B hBfin hBS hsplit σ hσ
  · intro A hA hAconj
    rcases Finset.mem_union.mp hA with hA | hA
    · exact absurd (SSGRoute.isConjPlace_refl (k := k) A) (hAconj A hA)
    · exact hb.2.2.1 A (hFfin A hA) hAconj (hFsplit A hA)

end ReciprocalSet

end

end Work.SSGRoute.PT
