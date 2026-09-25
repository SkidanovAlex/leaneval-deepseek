import Mathlib
import Submission.Work.ShafarevichKoch.GeneratorRank
import Submission.Work.ShafarevichKoch.GeneratorRankKc
import Submission.Work.ClassFieldTower.ProTwoGeneratorRank
import Submission.Work.ClassFieldTower.hasGenusLevel_witness
import Submission.Work.ClassFieldTower.WitnessField
import Submission.Work.ClassFieldTower.exists_fiveUnramifiedQuadratics_of_unramified_exponentTwo
import Submission.Work.ProPDeficiency.All
import Submission.Work.ShafarevichKoch.exists_isOpen_index_two_le_of_isClosed
import Submission.Work.ShafarevichKoch.le_of_isOpen_index_two_Kc

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Classical
open Filter
open Work.ClassFieldTower

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- The equalizer of two monoid homomorphisms, as a subgroup. -/
def eqSubgroup {G T : Type*} [Group G] [Group T] (χ ψ : G →* T) : Subgroup G where
  carrier := {x | χ x = ψ x}
  mul_mem' := by
    intro a b ha hb
    change χ (a * b) = ψ (a * b)
    rw [map_mul, map_mul, ha, hb]
  one_mem' := by
    change χ 1 = ψ 1
    rw [map_one, map_one]
  inv_mem' := by
    intro a ha
    change χ a⁻¹ = ψ a⁻¹
    rw [map_inv, map_inv, ha]

/-- Two continuous monoid homomorphisms agreeing on a topologically dense subgroup are equal. -/
theorem monoidHom_ext_of_topologicalClosure_eq_top {G T : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [T2Space T]
    {H : Subgroup G} (hH : H.topologicalClosure = ⊤) {χ ψ : G →* T}
    (hχ : Continuous χ) (hψ : Continuous ψ) (h : H ≤ eqSubgroup χ ψ) : χ = ψ := by
  have hKclosed : IsClosed ((eqSubgroup χ ψ : Subgroup G) : Set G) := isClosed_eq hχ hψ
  have hle : H.topologicalClosure ≤ eqSubgroup χ ψ :=
    Subgroup.topologicalClosure_minimal H h hKclosed
  rw [hH] at hle
  ext x
  exact hle (Subgroup.mem_top x)

/-! ### The lower bound: five generators are necessary. -/

theorem five_le_card_of_topologicalClosure_eq_top
    (M : MaximalUnramifiedProP.{0} Kc 2)
    (S : Finset (galoisGroup M))
    (hS : (Subgroup.closure (S : Set (galoisGroup M))).topologicalClosure = ⊤) :
    5 ≤ S.card := by
  classical
  have hinj : Function.Injective
      (fun χ : ProTwoChar Kc M => fun s : S => χ.1 (s : galoisGroup M)) := by
    rintro ⟨χ, hχ⟩ ⟨ψ, hψ⟩ heq
    refine Subtype.ext (monoidHom_ext_of_topologicalClosure_eq_top hS hχ hψ ?_)
    intro x hx
    exact (Subgroup.closure_le (eqSubgroup χ ψ)).mpr
      (fun s hs => congr_fun heq ⟨s, hs⟩) hx
  have hcard : Nat.card (ProTwoChar Kc M) ≤ Nat.card (S → Multiplicative (ZMod 2)) :=
    Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hScard : Nat.card S = S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [card_proTwoChar_Kc_eq_thirtytwo M, Nat.card_fun, h2, hScard] at hcard
  have h32 : (32 : ℕ) = 2 ^ 5 := by norm_num
  rw [h32] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard

/-! ### The upper bound: five generators suffice. -/

theorem exists_generatingSet_card_five_Kc_aux (M : MaximalUnramifiedProP.{0} Kc 2) :
    ∃ S : Finset (galoisGroup M), S.card = 5 ∧
      (Subgroup.closure (S : Set (galoisGroup M))).topologicalClosure = ⊤ := by
  classical
  obtain ⟨L, iL, iNL, iAL, hfd, hgal, hunr, hexp, hcard⟩ := hasGenusLevel_witness
  letI : Field L := iL
  letI : NumberField L := iNL
  letI : Algebra Kc L := iAL
  letI : FiniteDimensional Kc L := hfd
  letI : IsGalois Kc L := hgal
  have hpro : IsPGroup 2 (L ≃ₐ[Kc] L) := fun σ => ⟨1, by rw [pow_one]; exact hexp σ⟩
  obtain ⟨φ, -⟩ := M.universal L hpro hunr
  let E : IntermediateField Kc M.K := φ.fieldRange
  haveI hEfd : FiniteDimensional Kc ↥E := (φ.equivFieldRange).toLinearEquiv.finiteDimensional
  haveI hEnorm : Normal Kc ↥E := (IsGalois.of_algEquiv (φ.equivFieldRange)).to_normal
  obtain ⟨eL⟩ := nonempty_mulEquiv_galoisGroup_five L hexp hcard
  let eE : (↥E ≃ₐ[Kc] ↥E) ≃* (Fin 5 → Multiplicative (ZMod 2)) :=
    (AlgEquiv.autCongr (φ.equivFieldRange)).symm.trans (eL.trans (piMulEquivZmodTwo 5).symm)
  let Ψ : galoisGroup M →* (Fin 5 → Multiplicative (ZMod 2)) :=
    eE.toMonoidHom.comp (AlgEquiv.restrictNormalHom (F := Kc) (K₁ := M.K) ↥E)
  have hΨsurj : Function.Surjective Ψ := eE.surjective.comp
    (AlgEquiv.restrictNormalHom_surjective (F := Kc) (K₁ := ↥E) M.K)
  let N : Subgroup (galoisGroup M) := Ψ.ker
  haveI hNnormal : N.Normal := MonoidHom.normal_ker Ψ
  have hfixle : E.fixingSubgroup ≤ N := by
    intro u hu
    rw [MonoidHom.mem_ker]
    have h1 : (AlgEquiv.restrictNormalHom (F := Kc) (K₁ := M.K) ↥E) u = 1 := by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker E]
      exact hu
    show eE ((AlgEquiv.restrictNormalHom (F := Kc) (K₁ := M.K) ↥E) u) = 1
    rw [h1, map_one]
  have hNopen : IsOpen (N : Set (galoisGroup M)) := by
    refine Subgroup.isOpen_of_mem_nhds N (g := 1) ?_
    have h1 : (E.fixingSubgroup : Set (galoisGroup M)) ∈ nhds (1 : galoisGroup M) :=
      (IntermediateField.fixingSubgroup_isOpen E).mem_nhds (Subgroup.one_mem _)
    exact Filter.mem_of_superset h1 (fun x hx => hfixle hx)
  let e : (galoisGroup M) ⧸ N ≃* (Fin 5 → Multiplicative (ZMod 2)) :=
    QuotientGroup.quotientKerEquivOfSurjective Ψ hΨsurj
  have hNle : ∀ M' : Subgroup (galoisGroup M), IsOpen (M' : Set (galoisGroup M)) →
      M'.index = 2 → N ≤ M' := fun M' h1 h2 => le_of_isOpen_index_two_Kc M N hNopen e h1 h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 (Fin 5 → Multiplicative (ZMod 2)) := by
    rw [IsPGroup.iff_card]
    exact ⟨5, by simp⟩
  obtain ⟨S₀, hS₀card, hS₀gen, hS₀min⟩ :=
    Commons.GroupTheory.PGroup.burnside_basis (p := 2) hpg
  have hS₀5 : S₀.card = 5 := by
    rw [← Work.ProPDeficiency.IsMinimalGeneratingSet.dGens_eq
        (G := Fin 5 → Multiplicative (ZMod 2)) ⟨hS₀gen, hS₀min⟩,
      Work.ProPDeficiency.dGens_zmod_two_pow 5]
  let f : (Fin 5 → Multiplicative (ZMod 2)) → galoisGroup M :=
    fun y => Classical.choose (QuotientGroup.mk'_surjective N (e.symm y))
  have hf : ∀ y, (QuotientGroup.mk' N) (f y) = e.symm y :=
    fun y => Classical.choose_spec (QuotientGroup.mk'_surjective N (e.symm y))
  let T : Finset (galoisGroup M) := S₀.image f
  have hTcard : T.card ≤ 5 := by
    rw [← hS₀5]
    exact Finset.card_image_le
  have hTgen : Subgroup.map (QuotientGroup.mk' N)
      (Subgroup.closure (T : Set (galoisGroup M))) = ⊤ := by
    have hkey : Subgroup.closure (⇑(QuotientGroup.mk' N) ''
        (f '' (S₀ : Set (Fin 5 → Multiplicative (ZMod 2))))) = ⊤ := by
      have h1 : ⇑(QuotientGroup.mk' N) ''
          (f '' (S₀ : Set (Fin 5 → Multiplicative (ZMod 2)))) =
          ⇑(e.symm) '' (S₀ : Set (Fin 5 → Multiplicative (ZMod 2))) := by
        rw [← Set.image_comp]
        rw [show (⇑(QuotientGroup.mk' N) ∘ f) = ⇑(e.symm) from funext (fun y => hf y)]
      rw [h1]
      have h2 : Subgroup.map (e.symm.toMonoidHom)
          (Subgroup.closure (S₀ : Set (Fin 5 → Multiplicative (ZMod 2)))) = ⊤ := by
        rw [hS₀gen, Subgroup.map_top_of_surjective _ e.symm.surjective]
      rw [MonoidHom.map_closure] at h2
      exact h2
    rw [MonoidHom.map_closure, Finset.coe_image]
    exact hkey
  have hsup : Subgroup.closure (T : Set (galoisGroup M)) ⊔ N = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro g
    have hg : (QuotientGroup.mk' N) g ∈ Subgroup.map (QuotientGroup.mk' N)
        (Subgroup.closure (T : Set (galoisGroup M))) := by
      rw [hTgen]
      trivial
    obtain ⟨h, hh, hhe⟩ := hg
    have hmem : h⁻¹ * g ∈ N := by
      rw [← QuotientGroup.eq]
      exact hhe
    have hge : g = h * (h⁻¹ * g) := by group
    rw [hge]
    exact Subgroup.mul_mem_sup hh hmem
  have hHtop : (Subgroup.closure (T : Set (galoisGroup M))).topologicalClosure = ⊤ := by
    have hHclosed : IsClosed
        ((Subgroup.closure (T : Set (galoisGroup M))).topologicalClosure : Set (galoisGroup M)) :=
      Subgroup.isClosed_topologicalClosure _
    have hHsup : (Subgroup.closure (T : Set (galoisGroup M))).topologicalClosure ⊔ N = ⊤ := by
      refine le_antisymm le_top ?_
      rw [← hsup]
      exact sup_le_sup_right (Subgroup.le_topologicalClosure _) N
    by_contra hne
    obtain ⟨M', hle', hidx, hM'open⟩ := exists_isOpen_index_two_le_of_isClosed M hHclosed hne
    have hNM' : N ≤ M' := hNle M' hM'open hidx
    have htop : (⊤ : Subgroup (galoisGroup M)) ≤ M' := by
      rw [← hHsup]
      exact sup_le hle' hNM'
    have hM'top : M' = ⊤ := top_le_iff.mp htop
    have hindex : M'.index = 1 := by rw [hM'top, Subgroup.index_top]
    omega
  refine ⟨T, ?_, hHtop⟩
  have := five_le_card_of_topologicalClosure_eq_top M T hHtop
  omega

/-- **The minimal number of topological generators of `G_∅ = Gal(Kc_∅/Kc)` is five.**

`Kc = ℚ(√-30030)` has `32` continuous characters `G_∅ → Multiplicative (ZMod 2)`, i.e.
`dim_{𝔽₂} H¹(G_∅, 𝔽₂) = 5`; equivalently `G_∅ ⧸ Φ(G_∅) ≅ (𝔽₂)^5`, so a set generating `G_∅`
topologically has at least five elements (burnside/duality: a dense subgroup is determined on the
`32` characters, so `32 ≤ 2 ^ #S`), and five elements suffice: the genus level of `Kc` exhibits a
surjection `G_∅ ↠ (𝔽₂)^5` with open kernel `N`, and `N` — being the intersection of the kernels of
all continuous characters — is the Frattini subgroup of `G_∅`, whence any five elements whose
images generate `G_∅ ⧸ N` generate `G_∅` topologically. -/
theorem exists_generatingSet_card_five_Kc
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2) :
    (∃ S : Finset (Work.ClassFieldTower.galoisGroup M), S.card = 5 ∧
      (Subgroup.closure (S : Set (Work.ClassFieldTower.galoisGroup M))).topologicalClosure = ⊤) ∧
    (∀ S : Finset (Work.ClassFieldTower.galoisGroup M),
      (Subgroup.closure (S : Set (Work.ClassFieldTower.galoisGroup M))).topologicalClosure = ⊤ →
      5 ≤ S.card) :=
  ⟨exists_generatingSet_card_five_Kc_aux M,
    fun S hS => five_le_card_of_topologicalClosure_eq_top M S hS⟩

end Work.ShafarevichKoch
