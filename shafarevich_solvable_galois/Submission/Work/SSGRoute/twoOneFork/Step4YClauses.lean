import Mathlib
import Submission.Work.SSGRoute.Step4CokerData
import Submission.Work.SSGRoute.Interfaces
-- NOTE (fork): dropped; nothing in this file uses a declaration of `step4Helpers` (checked).
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The clause verification of the datum `y` of Step 4 (node `step4_y_exists`)

This module isolates, as a *clean* (arithmetic-free) piece of the node
`Work.SSGRoute.step4_y_exists`, the step that turns the *arithmetic output* — a homomorphism
`ζ : G_K → E(n,τ)` with the prescribed local data and the prescribed vanishing — into the datum
`Work.SSGRoute.Step4YData`.

Two facts do the work, and both are consequences of `E(n,τ)` being an *abelian* group (a
`ZMod p`-module) together with the normality of `K.fixingSubgroup`:

* **conjugation invariance** (`fork_step4_conj_eq_of_additive`): for `δ, σ ∈ G_K` one has
  `y (δ⁻¹ * σ * δ) = y σ`, because `y` is additive on `G_K` and its values lie in an abelian group.
  This is what makes a vanishing that is prescribed at *one* place of a `K`-prime propagate to all
  places of that `K`-prime.

* **the formal corestriction is the identity** (`fork_step4_cor_sum_eq_of_vanish`): if `y` vanishes on
  the decomposition groups of the conjugates `(sec s)⁻¹ • A` (`s ≠ 1`) then
  `∑_s s • y ((sec s)⁻¹ * σ * (sec s)) = y σ` for `σ ∈ D_A`.  Note this needs *no* normalisation
  of the section: the `s = 1` term is `y ((sec 1)⁻¹ * σ * (sec 1)) = y σ` by conjugation
  invariance, since `sec 1 ∈ G_K`.

The final theorem `fork_step4_yData_of_prescribed` assembles `Step4YData` from those two facts plus the
Tnew/ηt block (`Work.SSGRoute.step4_y_tnew`, supplied here as an explicit hypothesis so that this
module stays independent of the arithmetic of the local targets).
-/

namespace Work.SSGRoute

open scoped Pointwise
open _root_.SSGRoute
open Work.CohomologicalShrinking

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ SSGRoute.QBar}
  [FiniteDimensional ℚ K] [Normal ℚ K] {n i j : ℕ}

/-- **Conjugation invariance of a homomorphism into an abelian group.**  If `y : G_ℚ → E` is
additive on `G_K` (with `E` abelian) then `y (δ⁻¹ * σ * δ) = y σ` for `δ, σ ∈ G_K`. -/
theorem fork_step4_conj_eq_of_additive (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hy : ∀ σ ∈ K.fixingSubgroup, ∀ τ ∈ K.fixingSubgroup, y (σ * τ) = y σ + y τ)
    {δ σ : SSGRoute.GalQ} (hδ : δ ∈ K.fixingSubgroup) (hσ : σ ∈ K.fixingSubgroup) :
    y (δ⁻¹ * σ * δ) = y σ := by
  have hy1 : y 1 = 0 := by
    have h := hy 1 (K.fixingSubgroup.one_mem) 1 (K.fixingSubgroup.one_mem)
    rw [mul_one] at h
    exact (add_left_cancel (show y 1 + 0 = y 1 + y 1 from by rw [add_zero, ← h])).symm
  have hinv : ∀ δ : SSGRoute.GalQ, δ ∈ K.fixingSubgroup → y δ⁻¹ = - y δ := by
    intro δ hδ'
    have h := hy δ⁻¹ (K.fixingSubgroup.inv_mem hδ') δ hδ'
    rw [inv_mul_cancel, hy1] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hδi : δ⁻¹ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hδ
  have hσδ : σ * δ ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hσ hδ
  have h1 : y (δ⁻¹ * (σ * δ)) = y δ⁻¹ + y (σ * δ) := hy δ⁻¹ hδi (σ * δ) hσδ
  have h2 : y (σ * δ) = y σ + y δ := hy σ hσ δ hδ
  have h3 : y (δ⁻¹ * σ * δ) = y (δ⁻¹ * (σ * δ)) := by rw [mul_assoc]
  rw [h3, h1, h2, hinv δ hδ]
  abel

/-- **The formal corestriction collapses to `y`.**  If `y` is additive on `G_K` (abelian target)
and vanishes on the decomposition groups of the conjugates `(sec s)⁻¹ • A` for `s ≠ 1`, then
`∑_s s • y ((sec s)⁻¹ * σ * (sec s)) = y σ` for `σ ∈ D_A` at a place `A` that splits completely in
`K`. -/
theorem fork_step4_cor_sum_eq_of_vanish (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hy : ∀ σ ∈ K.fixingSubgroup, ∀ τ ∈ K.fixingSubgroup, y (σ * τ) = y σ + y τ)
    (sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ)
    (hsec : ∀ s : K ≃ₐ[ℚ] K, SSGRoute.restrict K (sec s) = s)
    (A : ValuationSubring SSGRoute.QBar) (hsplit : SSGRoute.IsSplitIn ℚ K A)
    (hvan : ∀ s : K ≃ₐ[ℚ] K, s ≠ 1 →
      ∀ δ ∈ SSGRoute.decomp ℚ ((sec s)⁻¹ • A), δ ∈ K.fixingSubgroup → y δ = 0)
    (σ : SSGRoute.GalQ) (hσ : σ ∈ SSGRoute.decomp ℚ A) :
    (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * σ * sec s)) = y σ := by
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  haveI : IsGalois ℚ SSGRoute.QBar :=
    { to_isSeparable := inferInstance, to_normal := inferInstance }
  -- the `s ≠ 1` terms vanish
  have hzero : ∀ s ∈ (Finset.univ : Finset (K ≃ₐ[ℚ] K)), s ≠ 1 →
      s • y ((sec s)⁻¹ * σ * sec s) = 0 := by
    intro s _ hs
    have hmem : (sec s)⁻¹ * σ * sec s ∈ SSGRoute.decomp ℚ ((sec s)⁻¹ • A) := by
      rw [Work.SSGRoute.decomp_conj A (sec s)⁻¹]
      exact Subgroup.mem_map.mpr ⟨σ, hσ, by simp⟩
    have hK : (sec s)⁻¹ * σ * sec s ∈ K.fixingSubgroup := by
      refine Work.SSGRoute.mem_fixingSubgroup_of_restrict_eq_one K ?_
      have hσ1 : Work.SSGRoute.restrict K σ = 1 :=
        Work.SSGRoute.restrict_eq_one_of_mem_fixingSubgroup K (hsplit hσ)
      rw [map_mul, map_mul, map_inv, hsec s, hσ1]
      simp
    rw [hvan s hs _ hmem hK, smul_zero]
  have hsum : (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * σ * sec s)) =
      (1 : K ≃ₐ[ℚ] K) • y ((sec 1)⁻¹ * σ * sec 1) :=
    Finset.sum_eq_single 1 (fun s _ hs => hzero s (Finset.mem_univ s) hs)
      (fun h => absurd (Finset.mem_univ 1) h)
  -- the `s = 1` term is `y σ`
  have h1K : sec 1 ∈ K.fixingSubgroup :=
    Work.SSGRoute.mem_fixingSubgroup_of_restrict_eq_one K (hsec 1)
  have hσK : σ ∈ K.fixingSubgroup := hsplit hσ
  have hconj : y ((sec 1)⁻¹ * σ * sec 1) = y σ :=
    fork_step4_conj_eq_of_additive y hy h1K hσK
  rw [hsum, one_smul, hconj]

end Work.SSGRoute

namespace Work.SSGRoute

open scoped Pointwise
open _root_.SSGRoute
open Work.CohomologicalShrinking

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ SSGRoute.QBar}
  [FiniteDimensional ℚ K] [Normal ℚ K] {n i j : ℕ}

/-- **The clause verification of `Step4YData`.**  Given

* a coker-side datum `D` and the Tnew/ηt block of `Step4YData` (all its clauses except the
  agreement),
* a function `y : G_ℚ → E(n,τ)` which vanishes off `G_K`, is additive and locally constant on
  `G_K` (the arithmetic's output: the local data of the obstruction class),

and the *vanishing/escape* consequences of that local data (`hesc` = clause 3, `hinert` = clause 4,
`hdecomp` = clauses 5 and 7, `hT0`, `hTnew` = the prescribed values at `D.T0` and at the chosen
prolongations, and `hconj` = the vanishing at the conjugates `(sec s)⁻¹ • A`, `s ≠ 1`, which is
what makes the formal corestriction collapse), one obtains `Step4YData p K n i j D y`.

The two genuine steps are `fork_step4_cor_sum_eq_of_vanish` (twice: for the `T⁰`-clause and for the
agreement at `Tnew`) and `fork_step4_conj_eq_of_additive` inside it; everything else is the packing. -/
theorem fork_step4_yData_of_prescribed (D : Step4CokerData p K n i j)
    (Tnew : Finset (ValuationSubring SSGRoute.QBar))
    (ηt : (A : ValuationSubring SSGRoute.QBar) → A ∈ Tnew →
      SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hTnewS : ∀ A ∈ Tnew, A ∈ D.S)
    (hTnewfin : ∀ A ∈ Tnew, SSGRoute.IsFinPlace ℚ A)
    (hTnewnotp : ∀ A ∈ Tnew, ¬ A.valuation (p : SSGRoute.QBar) < 1)
    (hTnewφ : ∀ A ∈ Tnew, ∀ σ ∈ SSGRoute.decomp ℚ A, D.phi σ = 1)
    (hTnewsplit : ∀ A ∈ Tnew, SSGRoute.IsSplitIn ℚ K A)
    (hcover : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A → A ∉ D.T0 →
      (∃ A₀ ∈ D.S, SSGRoute.IsConjPlace ℚ A₀ A) →
      (∀ σ ∈ SSGRoute.decomp ℚ A, D.phi σ = 1) →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ D.psi σ ≠ 1) →
      ∃ P ∈ Tnew, SSGRoute.IsConjPlace ℚ P A)
    (hηt : ∀ (A : ValuationSubring SSGRoute.QBar) (hA : A ∈ Tnew),
      (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A,
        ηt A hA (σ * τ) = ηt A hA σ + ηt A hA τ) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) (ηt A hA) ∧
      (∀ σ, SSGRoute.IsInertia ℚ A σ → ηt A hA σ = 0) ∧
      IsCyclic (Subgroup.closure
        ((Work.SSGRoute.flowTwistE p K n i j (ηt A hA) D.psi) ''
          (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
      (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
        Work.SSGRoute.flowTwistE p K n i j (ηt A hA) D.psi τ =
          Work.SSGRoute.flowTwistE p K n i j (ηt A hA) D.psi σ))
    (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hyoff : ∀ σ : SSGRoute.GalQ, σ ∉ K.fixingSubgroup → y σ = 0)
    (hyadd : ∀ σ ∈ K.fixingSubgroup, ∀ τ ∈ K.fixingSubgroup, y (σ * τ) = y σ + y τ)
    (hyloc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hesc : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∀ A ∈ D.S, ¬ SSGRoute.IsConjPlace ℚ A B) → ¬ SSGRoute.IsSplitIn ℚ D.Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia ℚ B σ → y σ = 0)
    (hinert : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∃ A ∈ D.S, SSGRoute.IsConjPlace ℚ A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia ℚ B σ → y σ = 0)
    (hdecomp : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∃ A ∈ D.S, SSGRoute.IsConjPlace ℚ A B) →
      (¬ SSGRoute.IsSplitIn ℚ K B ∨ B.valuation (p : SSGRoute.QBar) < 1 ∨
        (∃ σ, SSGRoute.IsInertia ℚ B σ ∧ σ ∈ K.fixingSubgroup ∧ D.phi σ ≠ 1)) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ B → y σ = 0)
    (hT0 : ∀ A ∈ D.T0, ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ A → y σ = 0)
    (hTnew : ∀ (A : ValuationSubring SSGRoute.QBar) (hA : A ∈ Tnew),
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ A → y σ = ηt A hA σ)
    (hconjTnew : ∀ A ∈ Tnew, ∀ s : K ≃ₐ[ℚ] K, s ≠ 1 →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ ((D.sec s)⁻¹ • A) → y σ = 0)
    (hconjT0 : ∀ A ∈ D.T0, ∀ s : K ≃ₐ[ℚ] K, s ≠ 1 →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ ((D.sec s)⁻¹ • A) → y σ = 0) :
    Step4YData p K n i j D y := by
  classical
  refine ⟨hyadd, hyloc, hesc, hinert, ?_, ?_, ?_, ?_⟩
  · -- clause 5
    intro B hBfin hBc hBcase σ hσK hσB
    exact hdecomp B hBfin hBc (hBcase.elim Or.inl (fun h => Or.inr (Or.inl h))) σ hσK hσB
  · -- clause 6: the formal corestriction vanishes on the `T⁰` decomposition groups
    intro A hA σ hσ
    have hsplit : SSGRoute.IsSplitIn ℚ K A := D.hT0split A hA
    rw [fork_step4_cor_sum_eq_of_vanish y hyadd D.sec D.hsec A hsplit
      (fun s hs δ hδ hδK => hconjT0 A hA s hs δ hδK hδ) σ hσ]
    exact hT0 A hA σ (hsplit hσ) hσ
  · -- clause 7 (the places of old ramification)
    intro B hBfin hBc hBram σ hσ
    by_cases hσK : σ ∈ K.fixingSubgroup
    · exact hdecomp B hBfin hBc (Or.inr (Or.inr hBram)) σ hσK hσ
    · exact hyoff σ hσK
  · -- the `Tnew`/`ηt` block
    refine ⟨Tnew, ηt, hTnewS, hTnewfin, hTnewnotp, hTnewφ, hcover, hηt, ?_⟩
    intro A hA σ hσ
    have hsplit : SSGRoute.IsSplitIn ℚ K A := hTnewsplit A hA
    rw [fork_step4_cor_sum_eq_of_vanish y hyadd D.sec D.hsec A hsplit
      (fun s hs δ hδ hδK => hconjTnew A hA s hs δ hδK hδ) σ hσ]
    exact hTnew A hA σ (hsplit hσ) hσ

end Work.SSGRoute

namespace Work.SSGRoute

open scoped Pointwise
open _root_.SSGRoute
open Work.CohomologicalShrinking

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ SSGRoute.QBar}
  [FiniteDimensional ℚ K] [Normal ℚ K] {n i j : ℕ}

/-- Level-`K` conjugacy of places: `B = τ • A` for some `τ ∈ G_K` (i.e. `A` and `B` have the same
place of `K` below them).  This is the equivalence relation under which the local data of the
obstruction class at the places of `K` propagate: for a homomorphism into an *abelian* group the
values at two level-`K`-conjugate places are the same. -/
private def KConjLocal (A B : ValuationSubring SSGRoute.QBar) : Prop :=
  ∃ τ : SSGRoute.GalQ, τ ∈ K.fixingSubgroup ∧ τ • A = B

private theorem kConjLocal_refl (A : ValuationSubring SSGRoute.QBar) : KConjLocal (K := K) A A :=
  ⟨1, K.fixingSubgroup.one_mem, one_smul _ _⟩

private theorem kConjLocal_symm {A B : ValuationSubring SSGRoute.QBar} (h : KConjLocal (K := K) A B) :
    KConjLocal (K := K) B A := by
  obtain ⟨τ, hτ, hτA⟩ := h
  exact ⟨τ⁻¹, K.fixingSubgroup.inv_mem hτ, by rw [← hτA]; exact inv_smul_smul τ A⟩

private theorem kConjLocal_trans {A B C : ValuationSubring SSGRoute.QBar} (h₁ : KConjLocal (K := K) A B)
    (h₂ : KConjLocal (K := K) B C) : KConjLocal (K := K) A C := by
  obtain ⟨τ, hτ, hτA⟩ := h₁
  obtain ⟨τ', hτ', hτ'B⟩ := h₂
  exact ⟨τ' * τ, K.fixingSubgroup.mul_mem hτ' hτ, by rw [mul_smul, hτA, hτ'B]⟩

/-- **The raw output of the obstruction class** (SW Lemma 10 + Lemma 12 + the shrinking, in the
hybrid base-`K`/escape-over-`ℚ` form): a function `y : G_ℚ → E(n,τ)` supported on `G_K`, additive
and locally constant there, whose local values at the places of a finite set `Sbig` (one place per
prime of `K`) are the prescribed local data `a`, and which is unramified at every place outside
`Sbig` that is not split in `Λ`. -/
private def Step4YRaw (D : Step4CokerData p K n i j)
    (Sbig : Finset (ValuationSubring SSGRoute.QBar))
    (a : ValuationSubring SSGRoute.QBar → SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j) : Prop :=
  ∃ y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j,
    (∀ σ : SSGRoute.GalQ, σ ∉ K.fixingSubgroup → y σ = 0) ∧
    (∀ σ ∈ K.fixingSubgroup, ∀ τ ∈ K.fixingSubgroup, y (σ * τ) = y σ + y τ) ∧
    SSGRoute.IsLocConstOn K.fixingSubgroup y ∧
    (∀ A ∈ Sbig, ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ A → y σ = a A σ) ∧
    (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∀ A ∈ Sbig, ¬ KConjLocal (K := K) A B) → ¬ SSGRoute.IsSplitIn ℚ D.Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia ℚ B σ → y σ = 0)

/-- **The local data propagates along level-`K` conjugacy.**  If `y` is additive on `G_K`
(abelian target) and agrees with `a A` on `D_A ∩ G_K`, then at a place `B = τ • A` with `τ ∈ G_K` it
agrees with the transported data `σ ↦ a A (τ⁻¹ * σ * τ)`. -/
private theorem step4_raw_conj_value (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hy : ∀ σ ∈ K.fixingSubgroup, ∀ τ ∈ K.fixingSubgroup, y (σ * τ) = y σ + y τ)
    (a : ValuationSubring SSGRoute.QBar → SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    {A : ValuationSubring SSGRoute.QBar}
    (hA : ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ A → y σ = a A σ)
    {τ : SSGRoute.GalQ} (hτ : τ ∈ K.fixingSubgroup) :
    ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ (τ • A) → y σ = a A (τ⁻¹ * σ * τ) := by
  intro σ hσK hσB
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  haveI : IsGalois ℚ SSGRoute.QBar :=
    { to_isSeparable := inferInstance, to_normal := inferInstance }
  -- `τ⁻¹ σ τ ∈ D_A ∩ G_K`
  have hmemA : τ⁻¹ * σ * τ ∈ SSGRoute.decomp ℚ A := by
    have hmap : σ ∈ (SSGRoute.decomp ℚ A).map (MulAut.conj τ).toMonoidHom := by
      rw [← Work.SSGRoute.decomp_conj A τ]; exact hσB
    obtain ⟨δ, hδ, hδσ⟩ := Subgroup.mem_map.mp hmap
    have h1 : δ = τ⁻¹ * σ * τ := by
      have h2 : τ * δ * τ⁻¹ = σ := hδσ
      calc δ = τ⁻¹ * (τ * δ * τ⁻¹) * τ := by group
        _ = τ⁻¹ * σ * τ := by rw [h2]
    rw [← h1]; exact hδ
  have hK : τ⁻¹ * σ * τ ∈ K.fixingSubgroup :=
    K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem (K.fixingSubgroup.inv_mem hτ) hσK) hτ
  -- conjugation invariance
  have hσeq : σ = τ * (τ⁻¹ * σ * τ) * τ⁻¹ := by group
  have h1 : y σ = y (τ⁻¹ * σ * τ) := by
    conv_lhs => rw [hσeq]
    exact fork_step4_conj_eq_of_additive y hy (K.fixingSubgroup.inv_mem hτ) hK
  rw [h1, hA (τ⁻¹ * σ * τ) hK hmemA]

end Work.SSGRoute
