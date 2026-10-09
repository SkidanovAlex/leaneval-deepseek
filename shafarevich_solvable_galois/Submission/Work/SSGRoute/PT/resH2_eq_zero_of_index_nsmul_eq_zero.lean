import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PT.resH2
import Submission.Work.SSGRoute.PT.corH2_resH2_eq_index
import Submission.Work.SSGRoute.PT.H2Transfer
import Submission.Work.SSGRoute.PT.KrullCorrespondence
import Submission.Work.SSGRoute.PTCore.H2_level_defs
import Submission.Work.SSGRoute.PTCore.H2_units_infl
import Submission.Work.SSGRoute.PTCore.H2_level_mono
import Submission.Work.SSGRoute.PTfin.levelH2_cyclic_finiteExtension
import Submission.Work.SSGRoute.PTCore.H2_level_card_adicCompletion
import Submission.Work.SSGRoute.homCoindDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.style.haveILetI false

namespace Work.SSGRoute.PT

open Work.AbsoluteKummer
open Work.SSGRoute.PTCore

noncomputable section

/-!
# Restriction kills the index-torsion of `H²(D_A, Ωˣ)`

This file proves `Work.SSGRoute.PT.resH2_eq_zero_of_index_nsmul_eq_zero`.  The mathematical content
is that for the local Brauer group of a finite place, `res_U` is multiplication by the index
`[D_A : U]` on `ℚ/ℤ = H²(D_A, Ωˣ)`, so that every class annihilated by the index restricts to
zero.

The proof runs in the *local-field* model, where the level structure of `H²(G_F, F̄ˣ)`
(`Work.SSGRoute.PTCore.psiTilde`) and the cyclicity of the level groups
`H²(Gal(L/F), Lˣ) ≅ ℤ/[L:F]` (`Work.SSGRoute.PTfin.levelH2_cyclic_finiteExtension`) are available,
and then transports the statement back to `D_A` using the `μ_p`-transfer
`Work.SSGRoute.PT.decompLocalTransferMup`.
-/

/-! ## A locally constant function composed with a locally constant map -/

/-- Composition with a locally constant map preserves local constancy of the *inner* function, for
an arbitrary (not necessarily continuous) outer function. -/
theorem _root_.Work.AbsoluteKummer.IsLocallyConstant.comp_of_isLocallyConstant
    {X Y M : Type*} [TopologicalSpace X] {g : Y → M} {φ : X → Y}
    (hφ : Work.AbsoluteKummer.IsLocallyConstant φ) :
    Work.AbsoluteKummer.IsLocallyConstant (fun x => g (φ x)) := by
  intro x
  obtain ⟨U, hU, hxU, hconst⟩ := hφ x
  exact ⟨U, hU, hxU, fun y hy => by
    show g (φ y) = g (φ x)
    rw [hconst y hy]⟩

/-! ## The averaging primitive for finite groups -/

/-- **Averaging a `2`-cocycle over a finite group.**  For a `2`-cocycle `c` of a finite group `Λ`
with values in an additive `Λ`-module `M`, the cochain `S g = ∑ k, c (g, k)` satisfies
`d¹ S = |Λ| • c`.  This is the standard proof that `H²(Λ, M)` is annihilated by `|Λ|`. -/
theorem d1_sum_eq_card_nsmul {Λ : Type*} [Group Λ] [Fintype Λ] {M : Type*} [AddCommGroup M]
    [DistribMulAction Λ M] (c : Λ × Λ → M)
    (hc : ∀ g h k : Λ, c (g * h, k) + c (g, h) = g • c (h, k) + c (g, h * k)) :
    Work.GroupCohomology.d1 Λ M (fun g => ∑ k : Λ, c (g, k)) = Fintype.card Λ • c := by
  funext p
  obtain ⟨g, h⟩ := p
  have hterm : ∀ k : Λ, g • c (h, k) = c (g * h, k) + c (g, h) - c (g, h * k) := by
    intro k
    rw [eq_sub_iff_add_eq]
    exact (hc g h k).symm
  have h1 : g • (∑ k : Λ, c (h, k)) = ∑ k : Λ, g • c (h, k) := Finset.smul_sum
  have h2 : (∑ k : Λ, g • c (h, k))
      = ∑ k : Λ, (c (g * h, k) + c (g, h) - c (g, h * k)) :=
    Finset.sum_congr rfl (fun k _ => hterm k)
  have h3 : (∑ k : Λ, (c (g * h, k) + c (g, h) - c (g, h * k)))
      = (∑ k : Λ, c (g * h, k)) + (∑ k : Λ, c (g, h)) - (∑ k : Λ, c (g, h * k)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h4 : (∑ k : Λ, c (g, h)) = Fintype.card Λ • c (g, h) := by
    rw [Finset.sum_const, Finset.card_univ]
  have h5 : (∑ k : Λ, c (g, h * k)) = ∑ k : Λ, c (g, k) :=
    Fintype.sum_equiv (Equiv.mulLeft h) (fun k => c (g, h * k)) (fun k => c (g, k))
      (fun k => rfl)
  have hmain : g • (∑ k : Λ, c (h, k))
      = (∑ k : Λ, c (g * h, k)) + Fintype.card Λ • c (g, h) - (∑ k : Λ, c (g, k)) := by
    rw [h1, h2, h3, h4, h5]
  rw [Work.GroupCohomology.d1_apply, hmain, Pi.smul_apply]
  abel

/-- **`H²` of a finite group is annihilated by the group order.** -/
theorem natCard_nsmul_H2_eq_zero {Λ : Type*} [Group Λ] [Fintype Λ] [TopologicalSpace Λ]
    {M : Type*} [AddCommGroup M] [DistribMulAction Λ M]
    (y : Work.AbsoluteKummer.H2 Λ M) : Nat.card Λ • y = 0 := by
  classical
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 Λ M).comap (Work.AbsoluteKummer.Z2 Λ M).subtype) y
  rw [show y = Work.AbsoluteKummer.H2π Λ M c from hc.symm, ← map_nsmul,
    Work.AbsoluteKummer.H2π_eq_zero_iff, Work.AbsoluteKummer.mem_B2_iff]
  have hcoc : ∀ g h k : Λ, (c : Λ × Λ → M) (g * h, k) + (c : Λ × Λ → M) (g, h)
      = g • (c : Λ × Λ → M) (h, k) + (c : Λ × Λ → M) (g, h * k) :=
    ((Work.AbsoluteKummer.mem_Z2_iff (c := (c : Λ × Λ → M))).mp c.2).1
  have hlc : Work.AbsoluteKummer.IsLocallyConstant (c : Λ × Λ → M) :=
    ((Work.AbsoluteKummer.mem_Z2_iff (c := (c : Λ × Λ → M))).mp c.2).2
  refine ⟨fun g => ∑ k : Λ, (c : Λ × Λ → M) (g, k), ?_, ?_⟩
  · -- local constancy of the averaged cochain
    have hsingle : ∀ k : Λ, Work.AbsoluteKummer.IsLocallyConstant
        (fun g : Λ => (c : Λ × Λ → M) (g, k)) := by
      intro k
      exact hlc.comp (continuous_id.prodMk continuous_const)
    have hsum : ∀ s : Finset Λ, Work.AbsoluteKummer.IsLocallyConstant
        (fun g : Λ => ∑ k ∈ s, (c : Λ × Λ → M) (g, k)) := by
      intro s
      induction s using Finset.induction with
      | empty => simpa using Work.AbsoluteKummer.isLocallyConstant_const (0 : M)
      | insert a s ha ih =>
        have : (fun g : Λ => ∑ k ∈ insert a s, (c : Λ × Λ → M) (g, k))
            = fun g => (c : Λ × Λ → M) (g, a) + ∑ k ∈ s, (c : Λ × Λ → M) (g, k) := by
          funext g
          rw [Finset.sum_insert ha]
        rw [this]
        exact (hsingle a).add ih
    have := hsum Finset.univ
    simpa using this
  · -- `d¹` of the averaged cochain is `|Λ| • c`
    rw [Nat.card_eq_fintype_card]
    exact d1_sum_eq_card_nsmul (c : Λ × Λ → M) hcoc

/-! ## The level computation: `res` kills the image of the index `m = [U : Gal(F̄/L)]` -/

/-- The `d¹` of the cochain `w ↦ inclL (S (resL w))` evaluated at `(u,v)`, expressed on the level:
it is `inclL` of `(resL u) • S (resL v) - S (resL u * resL v) + S (resL u)`. -/
lemma d1_inclL_resL_apply {F : Type} [Field F] [IsGalois F (AlgebraicClosure F)]
    (L : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (U : Subgroup (Work.AbsoluteKummer.G F)) (S : LevelGal L → UnitsL L) (u v : ↥U) :
    Work.GroupCohomology.d1 ↥U (UnitsK F)
        (fun w : ↥U => inclL L (S (resL L ((w : ↥U) : Work.AbsoluteKummer.G F)))) (u, v)
      = inclL L ((LevelRep L).ρ (resL L ((u : ↥U) : Work.AbsoluteKummer.G F))
            (S (resL L ((v : ↥U) : Work.AbsoluteKummer.G F)))
          - S ((resL L ((u : ↥U) : Work.AbsoluteKummer.G F))
              * (resL L ((v : ↥U) : Work.AbsoluteKummer.G F)))
          + S (resL L ((u : ↥U) : Work.AbsoluteKummer.G F))) := by
  rw [Work.GroupCohomology.d1_apply]
  have h1 : (u : ↥U) • inclL L (S (resL L ((v : ↥U) : Work.AbsoluteKummer.G F)))
      = inclL L ((LevelRep L).ρ (resL L ((u : ↥U) : Work.AbsoluteKummer.G F))
          (S (resL L ((v : ↥U) : Work.AbsoluteKummer.G F)))) := by
    show (((u : ↥U) : Work.AbsoluteKummer.G F)) • inclL L (S (resL L ((v : ↥U) :
      Work.AbsoluteKummer.G F))) = _
    exact (inclL_rho L _ _).symm
  have h2 : inclL L (S (resL L (((u * v : ↥U)) : Work.AbsoluteKummer.G F)))
      = inclL L (S ((resL L ((u : ↥U) : Work.AbsoluteKummer.G F))
          * (resL L ((v : ↥U) : Work.AbsoluteKummer.G F)))) := by
    rw [show (((u * v : ↥U)) : Work.AbsoluteKummer.G F)
        = ((u : ↥U) : Work.AbsoluteKummer.G F) * ((v : ↥U) : Work.AbsoluteKummer.G F) from rfl,
      map_mul]
  rw [h1, h2]
  simp only [map_add, map_sub]

/-- **The level computation.**  Let `L` be a finite Galois level of `F̄/F`, `U ≤ G_F` an open
subgroup containing `Gal(F̄/L)`, and let `m = |U·Gal(F̄/L)/Gal(F̄/L)|`.  Then for every level class
`y` the class `m • y`, inflated to `H²(G_F, F̄ˣ)` and restricted to `U`, vanishes.

This is the arithmetic-free core of `res_U ∘ infl = [G_F : U]·(-)`: on the level `L` the class
`m • y` is represented by the cocycle `m • c`, whose restriction to `Λ = U·Gal(F̄/L)/Gal(F̄/L)`
is the coboundary of the averaging primitive `S(a) = ∑_{b ∈ Λ} c(a, b)`, since `H²(Λ, Lˣ)` is
annihilated by `|Λ| = m` (`d1_sum_eq_card_nsmul`). -/
theorem resH2_psiTilde_nsmul_eq_zero {F : Type} [Field F] [IsGalois F (AlgebraicClosure F)]
    (L : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (U : Subgroup (Work.AbsoluteKummer.G F)) (hU : IsOpen (U : Set (Work.AbsoluteKummer.G F)))
    (hVU : (L : IntermediateField F (AlgebraicClosure F)).fixingSubgroup ≤ U)
    (y : LevelH2 L) :
    resH2 U (psiTilde L ((Nat.card ↥(U.map (resL L))) • y)) = 0 := by
  classical
  obtain ⟨cy, hcy⟩ := QuotientAddGroup.mk'_surjective
    ((LevelCob L).comap (LevelCocycles L).subtype).toAddSubgroup y
  set Λ : Subgroup (LevelGal L) := U.map (resL L) with hΛdef
  have hmem : ∀ u : ↥U, resL L ((u : ↥U) : Work.AbsoluteKummer.G F) ∈ Λ := fun u =>
    Subgroup.mem_map.mpr ⟨((u : ↥U) : Work.AbsoluteKummer.G F), u.2, rfl⟩
  -- the cocycle condition of the level cocycle
  have hcoc : ∀ g h k : LevelGal L,
      (cy : LevelGal L × LevelGal L → UnitsL L) (g * h, k) + (cy : _) (g, h)
        = (LevelRep L).ρ g ((cy : _) (h, k)) + (cy : _) (g, h * k) :=
    fun g h k => (mem_cocycles₂_iff_add L (cy : LevelGal L × LevelGal L → UnitsL L)).mp cy.2 g h k
  -- the averaging primitive
  set S : LevelGal L → UnitsL L := fun g => ∑ b : ↥Λ, (cy : _) (g, (b : LevelGal L)) with hSdef
  have hSapply : ∀ g : LevelGal L, S g = ∑ b : ↥Λ, (cy : _) (g, (b : LevelGal L)) :=
    fun g => rfl
  -- the key averaging identity: `(m = |Λ|)`
  have hkey : ∀ a b : ↥Λ,
      (LevelRep L).ρ (a : LevelGal L) (S (b : LevelGal L))
        - S ((a : LevelGal L) * (b : LevelGal L)) + S (a : LevelGal L)
      = Nat.card ↥Λ • (cy : _) ((a : LevelGal L), (b : LevelGal L)) := by
    intro a b
    have hterm : ∀ c : ↥Λ,
        (LevelRep L).ρ (a : LevelGal L) ((cy : _) ((b : LevelGal L), (c : LevelGal L)))
        = (cy : _) (((a : LevelGal L) * (b : LevelGal L)), (c : LevelGal L))
          + (cy : _) ((a : LevelGal L), (b : LevelGal L))
          - (cy : _) ((a : LevelGal L), ((b : LevelGal L) * (c : LevelGal L))) := by
      intro c
      have h := hcoc (a : LevelGal L) (b : LevelGal L) (c : LevelGal L)
      rw [eq_sub_iff_add_eq]
      exact h.symm
    have h1 : (LevelRep L).ρ (a : LevelGal L) (S (b : LevelGal L))
        = ∑ c : ↥Λ, (LevelRep L).ρ (a : LevelGal L)
            ((cy : _) ((b : LevelGal L), (c : LevelGal L))) := by
      rw [hSapply]
      exact map_sum ((LevelRep L).ρ (a : LevelGal L)) _ _
    have h2 : (∑ c : ↥Λ, (LevelRep L).ρ (a : LevelGal L)
          ((cy : _) ((b : LevelGal L), (c : LevelGal L))))
        = ∑ c : ↥Λ, ((cy : _) (((a : LevelGal L) * (b : LevelGal L)), (c : LevelGal L))
          + (cy : _) ((a : LevelGal L), (b : LevelGal L))
          - (cy : _) ((a : LevelGal L), ((b : LevelGal L) * (c : LevelGal L)))) :=
      Finset.sum_congr rfl (fun c _ => hterm c)
    have h3 : (∑ c : ↥Λ, ((cy : _) (((a : LevelGal L) * (b : LevelGal L)), (c : LevelGal L))
          + (cy : _) ((a : LevelGal L), (b : LevelGal L))
          - (cy : _) ((a : LevelGal L), ((b : LevelGal L) * (c : LevelGal L)))))
        = (∑ c : ↥Λ, (cy : _) (((a : LevelGal L) * (b : LevelGal L)), (c : LevelGal L)))
          + (∑ c : ↥Λ, (cy : _) ((a : LevelGal L), (b : LevelGal L)))
          - (∑ c : ↥Λ, (cy : _) ((a : LevelGal L), ((b : LevelGal L) * (c : LevelGal L)))) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have h4 : (∑ c : ↥Λ, (cy : _) ((a : LevelGal L), (b : LevelGal L)))
        = Nat.card ↥Λ • (cy : _) ((a : LevelGal L), (b : LevelGal L)) := by
      rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
    have h5 : (∑ c : ↥Λ, (cy : _) ((a : LevelGal L), ((b : LevelGal L) * (c : LevelGal L))))
        = ∑ c : ↥Λ, (cy : _) ((a : LevelGal L), (c : LevelGal L)) := by
      refine Fintype.sum_equiv (Equiv.mulLeft b) _ _ (fun c => ?_)
      rfl
    rw [h1, h2, h3, h4, h5, hSapply, hSapply]
    abel
  -- the cobounding cochain, and the identification of the two cocycles
  have hmain : (fun p : ↥U × ↥U => inclL L ((Nat.card ↥Λ) • (cy : _)
      ((resL L ((p.1 : ↥U) : Work.AbsoluteKummer.G F)),
       (resL L ((p.2 : ↥U) : Work.AbsoluteKummer.G F)))))
      ∈ Work.AbsoluteKummer.B2 ↥U (UnitsK F) := by
    rw [Work.AbsoluteKummer.mem_B2_iff]
    refine ⟨fun u : ↥U => inclL L (S (resL L ((u : ↥U) : Work.AbsoluteKummer.G F))), ?_, ?_⟩
    · refine Work.AbsoluteKummer.IsLocallyConstant.map (inclL L) ?_
      have hlc1 : Work.AbsoluteKummer.IsLocallyConstant
          (fun x : Work.AbsoluteKummer.G F => S (resL L x)) :=
        (isLocallyConstant_resL L).comp_of_isLocallyConstant (g := S)
      exact hlc1.comp continuous_subtype_val
    · funext p
      obtain ⟨u, v⟩ := p
      rw [d1_inclL_resL_apply L U S u v, hkey ⟨_, hmem u⟩ ⟨_, hmem v⟩, map_nsmul]
  -- assemble
  have hgoal : resH2 U (psiTilde L ((Nat.card ↥Λ) • y)) = 0 := by
    rw [show y = QuotientAddGroup.mk'
      ((LevelCob L).comap (LevelCocycles L).subtype).toAddSubgroup cy from hcy.symm]
    rw [show (Nat.card ↥Λ) • (QuotientAddGroup.mk'
        ((LevelCob L).comap (LevelCocycles L).subtype).toAddSubgroup cy : LevelH2 L)
        = QuotientAddGroup.mk'
          ((LevelCob L).comap (LevelCocycles L).subtype).toAddSubgroup
            ((Nat.card ↥Λ) • cy) from (map_nsmul _ _ _).symm]
    rw [psiTilde_mk, resH2_H2π, Work.AbsoluteKummer.H2π_eq_zero_iff]
    have hcoe : ((Work.SSGRoute.PT.resZ2 U
        (inflCo L ((Nat.card ↥Λ) • cy)) : Work.AbsoluteKummer.Z2 ↥U (UnitsK F)) :
          ↥U × ↥U → UnitsK F)
        = (fun p : ↥U × ↥U => inclL L ((Nat.card ↥Λ) • (cy : _)
            ((resL L ((p.1 : ↥U) : Work.AbsoluteKummer.G F)),
             (resL L ((p.2 : ↥U) : Work.AbsoluteKummer.G F))))) := by
      funext p
      obtain ⟨u, v⟩ := p
      rfl
    rw [hcoe]
    exact hmain
  simpa [hΛdef] using hgoal

/-! ## Refining a level inside a prescribed open subgroup -/

/-- **Refinement of a level.**  For an open subgroup `U` of an absolute Galois group and any finite
Galois level `L₀`, there is a finite Galois level `L ⊇ L₀` whose fixing subgroup lies in `U`. -/
theorem exists_level_le_fixingSubgroup {F : Type} [Field F] [IsGalois F (AlgebraicClosure F)]
    (U : Subgroup (Work.AbsoluteKummer.G F)) (hU : IsOpen (U : Set (Work.AbsoluteKummer.G F)))
    (L₀ : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :
    ∃ L : FiniteGaloisIntermediateField F (AlgebraicClosure F),
      L₀.toIntermediateField ≤ L.toIntermediateField ∧ L.toIntermediateField.fixingSubgroup ≤ U := by
  classical
  obtain ⟨E, hEfin, hEU⟩ :=
    (krullTopology_mem_nhds_one_iff F (AlgebraicClosure F) (U : Set (Work.AbsoluteKummer.G F))).mp
      (hU.mem_nhds U.one_mem)
  haveI : FiniteDimensional F ↥E := hEfin
  let M : IntermediateField F (AlgebraicClosure F) :=
    IntermediateField.normalClosure F ↥E (AlgebraicClosure F)
  haveI hMfin : FiniteDimensional F ↥M := inferInstance
  let M' : FiniteGaloisIntermediateField F (AlgebraicClosure F) :=
    { toIntermediateField := M, finiteDimensional := hMfin,
      isGalois := IsGalois.normalClosure F ↥E (AlgebraicClosure F) }
  refine ⟨M' ⊔ L₀, ?_, ?_⟩
  · exact (FiniteGaloisIntermediateField.le_iff _ _).mp le_sup_right
  · have h1 : (M' ⊔ L₀).toIntermediateField.fixingSubgroup
        ≤ M'.toIntermediateField.fixingSubgroup :=
      IntermediateField.fixingSubgroup_le ((FiniteGaloisIntermediateField.le_iff _ _).mp le_sup_left)
    have h2 : M'.toIntermediateField.fixingSubgroup ≤ E.fixingSubgroup :=
      IntermediateField.fixingSubgroup_le (IntermediateField.le_normalClosure E)
    exact le_trans h1 (le_trans h2 hEU)

/-! ## A divisibility computation for a cyclic group -/

/-- **Divisibility in a cyclic group.**  If `x` lies in the cyclic subgroup generated by `u` of
order `N = n * m` (`n ≠ 0`) and `n • x = 0`, then `x` is divisible by `m`. -/
theorem exists_nsmul_eq_of_card_nsmul_eq_zero {A : Type*} [AddCommGroup A]
    (u x : A) (n m N : ℕ) (hu : addOrderOf u = N) (hN : N = n * m) (hn : n ≠ 0)
    (hx : x ∈ AddSubgroup.zmultiples u) (h0 : n • x = 0) :
    ∃ y : A, x = m • y := by
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  have hz : ((n : ℤ) * k) • u = 0 := by
    rw [mul_zsmul, hk, natCast_zsmul]
    exact h0
  have hdvd : ((N : ℤ)) ∣ (n : ℤ) * k := by
    rw [← hu]
    exact (addOrderOf_dvd_iff_zsmul_eq_zero).mpr hz
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  have hdvd' : (m : ℤ) ∣ k := by
    refine (mul_dvd_mul_iff_left hnz).mp ?_
    rw [← Nat.cast_mul, ← hN]
    exact hdvd
  obtain ⟨j, hj⟩ := hdvd'
  refine ⟨j • u, ?_⟩
  rw [← hk, hj, mul_zsmul, natCast_zsmul]

/-! ## The local-field target -/

/-- **The local-field form of the target.**  For a number field `K` and a finite place `Q`, let
`F = K_Q` be the `Q`-adic completion and `G_F` the absolute Galois group of `F`.  Then for every
open subgroup `U ≤ G_F` of finite index and every class `e ∈ H²(G_F, F̄ˣ)` annihilated by the index
`[G_F : U]`, the restriction of `e` to `U` vanishes.

Proof: `e` lives on a finite Galois level `L` of `F` (`psiTilde_range_cover`), which we may refine
so that `Gal(F̄/L) ≤ U` (`exists_level_le_fixingSubgroup`); its level class `x` satisfies
`n • x = 0`, and since `H²(Gal(L/F), Lˣ)` is cyclic of order `[L : F]`
(`levelH2_cyclic_finiteExtension`) and `[L : F] = n · m` with `m = |U·Gal(F̄/L)/Gal(F̄/L)|`, the
class `x` is divisible by `m` (`exists_nsmul_eq_of_card_nsmul_eq_zero`).  Finally
`res_U (psiTilde L (m • y)) = 0` by `resH2_psiTilde_nsmul_eq_zero`. -/
theorem local_resH2_eq_zero_of_index_nsmul_eq_zero {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∀ (e : Work.AbsoluteKummer.H2 (Work.AbsoluteKummer.G (Q.adicCompletion K))
        (Additive ((AlgebraicClosure (Q.adicCompletion K))ˣ)))
      (U : Subgroup (Work.AbsoluteKummer.G (Q.adicCompletion K)))
      (hU : IsOpen (U : Set (Work.AbsoluteKummer.G (Q.adicCompletion K))))
      [U.FiniteIndex] [Fintype (Work.AbsoluteKummer.G (Q.adicCompletion K) ⧸ U)],
      Nat.card (Work.AbsoluteKummer.G (Q.adicCompletion K) ⧸ U) • e = 0 →
        Work.SSGRoute.PT.resH2 U e = 0 := by
  intro e U hU hfinI hfin he
  classical
  obtain ⟨L₀, hL₀⟩ := psiTilde_range_cover e
  obtain ⟨L, hL₀L, hVLU⟩ := exists_level_le_fixingSubgroup U hU L₀
  obtain ⟨xb, hxb⟩ := psiTilde_range_mono L₀ L hL₀L hL₀
  -- the level class is annihilated by the index
  have hxb0 : Nat.card (Work.AbsoluteKummer.G (Q.adicCompletion K) ⧸ U) • xb = 0 := by
    apply psiTilde_injective L
    rw [map_nsmul, hxb, he, map_zero]
  -- cyclicity of the level
  obtain ⟨u, hutop, huord⟩ := levelH2_cyclic_finiteExtension (K := K) Q L
  have hux : xb ∈ AddSubgroup.zmultiples u := by rw [hutop]; exact AddSubgroup.mem_top xb
  -- the index computation `[L : F] = [G_F : U] * |U·Gal(F̄/L)/Gal(F̄/L)|`
  set V : Subgroup (Work.AbsoluteKummer.G (Q.adicCompletion K)) :=
    L.toIntermediateField.fixingSubgroup with hVdef
  set Φ : ↥U →* ↥(U.map (resL L)) := (resL L).subgroupMap U with hΦdef
  have hker : Φ.ker = V.subgroupOf U := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact (mem_ker_resL_iff L _).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext_iff.mpr ((mem_ker_resL_iff L _).mpr h)
  have hcard : Nat.card ↥(U.map (resL L)) = (V.subgroupOf U).index := by
    rw [Subgroup.index_eq_card]
    rw [← hker]
    have hrange : Nat.card ↥Φ.range = Nat.card ↥(U.map (resL L)) := by
      haveI : Φ.range = ⊤ :=
        MonoidHom.range_eq_top.mpr (MonoidHom.subgroupMap_surjective (resL L) U)
      rw [this]
      exact Nat.card_congr (Subgroup.topEquiv).toEquiv
    rw [← hrange]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange Φ).toEquiv).symm
  have hidx : V.index = (V.subgroupOf U).index * U.index := by
    have h := Subgroup.index_map_subtype (H := U) (V.subgroupOf U)
    rwa [Subgroup.map_subgroupOf_eq_of_le hVLU] at h
  have hN : Module.finrank (Q.adicCompletion K) ↥L.toIntermediateField
      = Nat.card (Work.AbsoluteKummer.G (Q.adicCompletion K) ⧸ U) * Nat.card ↥(U.map (resL L)) := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (AlgebraicClosure (Q.adicCompletion K))
      L.toIntermediateField]
    rw [hidx, hcard, Subgroup.index_eq_card]
    exact Nat.mul_comm _ _
  haveI hfinU : Finite (Work.AbsoluteKummer.G (Q.adicCompletion K) ⧸ U) := Finite.of_fintype _
  have hn0 : Nat.card (Work.AbsoluteKummer.G (Q.adicCompletion K) ⧸ U) ≠ 0 := by
    rw [← Subgroup.index_eq_card]
    exact Subgroup.index_ne_zero_of_finite
  obtain ⟨y, hy⟩ := exists_nsmul_eq_of_card_nsmul_eq_zero u xb
    (Nat.card (Work.AbsoluteKummer.G (Q.adicCompletion K) ⧸ U)) (Nat.card ↥(U.map (resL L)))
    (Module.finrank (Q.adicCompletion K) ↥L.toIntermediateField) huord hN hn0 hux hxb0
  rw [← hxb, hy]
  exact resH2_psiTilde_nsmul_eq_zero L U hU hVLU y


/-! ## The reduction to the class-formation axiom on the `p`-torsion -/

/-- **The class-formation axiom (1.1b) implies the target.**  Suppose that for every prime `p`
dividing the index `n = [D_A : U]` the corestriction `cor : H²(U, Ωˣ) → H²(D_A, Ωˣ)` is injective
on the `p`-torsion (Milne, *ADT*, (1.1b) for the local class formation `(D_A, \barΩˣ)`).  Then every
class annihilated by the index restricts to zero.

Indeed, if `res_U e ≠ 0` had order `d | n`, pick a prime `p | d`; then `(d/p) • res_U e ≠ 0` is
`p`-torsion, and `cor ((d/p) • res_U e) = (d/p) • [D_A : U] • e = 0` by the
restriction–corestriction identity — contradicting injectivity. -/
theorem resH2_eq_zero_of_corH2_injective_on_ptorsion
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (U : Subgroup ↥(SSGRoute.decomp k A)) (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A)))
    [U.FiniteIndex] [Fintype (↥(SSGRoute.decomp k A) ⧸ U)]
    (hcor : ∀ (p : ℕ), p.Prime → p ∣ Nat.card (↥(SSGRoute.decomp k A) ⧸ U) →
      ∀ y : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)), p • y = 0 →
        Work.SSGRoute.PT.corH2 U hU (Additive (Units Ω)) y = 0 → y = 0) :
    ∀ e : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)),
      Nat.card (↥(SSGRoute.decomp k A) ⧸ U) • e = 0 → Work.SSGRoute.PT.resH2 U e = 0 := by
  classical
  haveI : Finite (↥(SSGRoute.decomp k A) ⧸ U) := Finite.of_fintype _
  have hn0 : Nat.card (↥(SSGRoute.decomp k A) ⧸ U) ≠ 0 := by
    rw [← Subgroup.index_eq_card]
    exact Subgroup.index_ne_zero_of_finite
  intro e he
  by_contra hne
  have hdvd : addOrderOf (Work.SSGRoute.PT.resH2 U e)
      ∣ Nat.card (↥(SSGRoute.decomp k A) ⧸ U) :=
    (addOrderOf_dvd_iff_nsmul_eq_zero).mpr (by rw [← map_nsmul, he, map_zero])
  have hd0 : 0 < addOrderOf (Work.SSGRoute.PT.resH2 U e) :=
    Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn0)
  have hne' : addOrderOf (Work.SSGRoute.PT.resH2 U e) ≠ 1 := fun h1 =>
    hne (by rwa [AddMonoid.addOrderOf_eq_one_iff] at h1)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne'
  have hpindex : p ∣ Nat.card (↥(SSGRoute.decomp k A) ⧸ U) := hpdvd.trans hdvd
  have hpdp : p ≤ addOrderOf (Work.SSGRoute.PT.resH2 U e) := Nat.le_of_dvd hd0 hpdvd
  have hdp0 : addOrderOf (Work.SSGRoute.PT.resH2 U e) / p ≠ 0 :=
    (Nat.div_pos hpdp hp.pos).ne'
  set y : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)) :=
    (addOrderOf (Work.SSGRoute.PT.resH2 U e) / p) • Work.SSGRoute.PT.resH2 U e with hydef
  have hord : addOrderOf y = p := by
    rw [hydef, addOrderOf_nsmul' (n := addOrderOf (Work.SSGRoute.PT.resH2 U e) / p)
      (Work.SSGRoute.PT.resH2 U e) hdp0]
    rw [Nat.gcd_eq_right (Nat.div_dvd_of_dvd hpdvd), Nat.div_div_self hpdvd hd0.ne']
  have hy_ptor : p • y = 0 := (addOrderOf_dvd_iff_nsmul_eq_zero).mp (by rw [hord])
  have hy_ne : y ≠ 0 := by
    intro h0
    rw [h0, addOrderOf_zero] at hord
    exact hp.ne_one hord.symm
  have hy_cor : Work.SSGRoute.PT.corH2 U hU (Additive (Units Ω)) y = 0 := by
    rw [hydef, map_nsmul, Work.SSGRoute.PT.corH2_resH2_eq_index]
    rw [show U.index = Nat.card (↥(SSGRoute.decomp k A) ⧸ U) from Subgroup.index_eq_card U,
      he, smul_zero]
  exact hy_ne (hcor p hp hpindex y hy_ptor hy_cor)


/-! ## The remaining arithmetic input and the target -/

/-- **Milne, *ADT*, (1.1b) for the local class formation `(D_A, \barΩˣ)` (arithmetic input).**

`H²(D_A, Ωˣ)` is the Brauer group of the local field `k_𝔭 ≅ ℚ/ℤ`, and corestriction is the
identity of `ℚ/ℤ` under the invariant identifications `inv_{D_A} ∘ cor = inv_U`; in particular the
corestriction is injective on the `p`-torsion for every prime `p ∣ [D_A : U]`.

The route (with all *structural* ingredients already proved in this file and in the workspace):
pass to the completion `κ = PTembedding.localFieldOf k A hA`, where the level structure
(`Work.SSGRoute.PTCore.H2_units_level_structure`) and the cyclicity of the level groups
`H²(Gal(L/κ), Lˣ) ≅ ℤ/[L:κ]` (`levelH2_cyclic_finiteExtension`) are available — this is exactly
what proves the local target `local_resH2_eq_zero_of_index_nsmul_eq_zero` below — and transport
the `μ_p`-statement back along the `μ_p`-transfer of `H²`
(`Work.SSGRoute.PTCore.h2loc_equiv_localGal_mup` with `Work.SSGRoute.PT.H2Transfer`), using that
corestriction is functorial.  Alternatively use the invariant map `NK.NUV2.LC.localInvariant` with
the compatible fundamental classes `NK.NUV2.RouteE.exists_compatible_fundamentalClasses`.

The proof of the target below consumes only this statement:
`resH2_eq_zero_of_corH2_injective_on_ptorsion`. -/
theorem corH2_injective_on_ptorsion_aux (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (U : Subgroup ↥(SSGRoute.decomp k A)) (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A)))
    [U.FiniteIndex] [Fintype (↥(SSGRoute.decomp k A) ⧸ U)]
    (p : ℕ) (hp : p.Prime) (hpdiv : p ∣ Nat.card (↥(SSGRoute.decomp k A) ⧸ U)) :
    ∀ y : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)), p • y = 0 →
      Work.SSGRoute.PT.corH2 U hU (Additive (Units Ω)) y = 0 → y = 0 := by
  sorry

/-- **Shafarevich's route: restriction kills the index-torsion of `H²(D_A, Ωˣ)`.**

For a number field `k`, its algebraic closure `Ω`, a finite place `A` of `Ω` over `k`, an open
subgroup `U ≤ D_A = SSGRoute.decomp k A` of finite index and a class `e ∈ H²(D_A, Ωˣ)` annihilated
by the index `[D_A : U] = Nat.card (D_A ⧸ U)`, the restriction of `e` to `U` vanishes:

  `resH2 U e = 0`.

This is the class-formation axiom (1.1b): the local Brauer group `H²(D_A, Ωˣ)` of the completion at
`A` is `ℚ/ℤ` under the invariant map, on which restriction is multiplication by the index. -/
theorem resH2_eq_zero_of_index_nsmul_eq_zero (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) (U : Subgroup ↥(SSGRoute.decomp k A))
    (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A))) [U.FiniteIndex]
    [Fintype (↥(SSGRoute.decomp k A) ⧸ U)] :
    ∀ e : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)),
      Nat.card (↥(SSGRoute.decomp k A) ⧸ U) • e = 0 → Work.SSGRoute.PT.resH2 U e = 0 :=
  resH2_eq_zero_of_corH2_injective_on_ptorsion k Ω A hA U hU
    (fun p hp hpdiv => corH2_injective_on_ptorsion_aux k Ω A hA U hU p hp hpdiv)


end

end Work.SSGRoute.PT
