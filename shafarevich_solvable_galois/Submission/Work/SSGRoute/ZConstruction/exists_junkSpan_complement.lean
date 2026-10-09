import Mathlib
import Submission.Work.SSGRoute.ZConstruction.AuxExistsUnmixed
import Submission.Work.SSGRoute.line_complement_decomposition
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZConstruction

/-- Every additive subgroup of a module over `ZMod n` is a submodule: a `ZMod n`-scalar multiple
is an integer multiple, and an additive subgroup is closed under those. -/
def addSubgroupToSubmodule (n : ℕ) (E : Type) [AddCommGroup E] [Module (ZMod n) E]
    (H : AddSubgroup E) : Submodule (ZMod n) E where
  carrier := H
  add_mem' := fun ha hb => H.add_mem ha hb
  zero_mem' := H.zero_mem
  smul_mem' := fun c x hx => zmod_smul_mem (K := H) hx c

theorem exists_junkSpan_complement (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K Λ : IntermediateField k Ω} {S : Finset (ValuationSubring Ω)}
    {E : Type} [AddCommGroup E] [Module (ZMod p) E] [Finite E]
    (y : (Ω ≃ₐ[k] Ω) → E) (h : 2 ≤ Module.finrank (ZMod p) E)
    (hproper : Work.SSGRoute.ZConstruction.junkSpan K Λ S y ≠ ⊤) :
    ∃ (L E₀ : Submodule (ZMod p) E) (hc : IsCompl L E₀),
      Module.finrank (ZMod p) L = 1 ∧ Module.finrank (ZMod p) E₀ < Module.finrank (ZMod p) E ∧
      Work.SSGRoute.ZConstruction.junkSpan K Λ S y ≤ E₀.toAddSubgroup ∧
      ∃ (π₀ : E →ₗ[ZMod p] ↥E₀) (π₁ : E →ₗ[ZMod p] ↥L),
        (∀ x : E, (π₀ x : E) + (π₁ x : E) = x) ∧
        (∀ x : E, x ∈ E₀ → (π₀ x : E) = x) ∧
        (∀ x : E, x ∈ L → (π₁ x : E) = x) ∧
        (∀ x : E, x ∈ Work.SSGRoute.ZConstruction.junkSpan K Λ S y → (π₁ x : E) = 0) := by
  haveI : FiniteDimensional (ZMod p) E := Module.Finite.of_finite
  -- View `junkSpan` as a submodule of `E`.
  let Jm : Submodule (ZMod p) E := addSubgroupToSubmodule p E (junkSpan K Λ S y)
  have hproper' : Jm ≠ ⊤ := by
    intro hh
    apply hproper
    ext z
    have hz := congrArg (fun M : Submodule (ZMod p) E => z ∈ M) hh
    simpa [Jm, addSubgroupToSubmodule] using hz
  -- Pick `x` outside the junk span.
  obtain ⟨x, hx⟩ : ∃ x, x ∉ Jm := by
    by_contra hc
    apply hproper'
    rw [Submodule.eq_top_iff']
    intro z
    by_contra hz
    exact hc ⟨z, hz⟩
  have hx0 : x ≠ 0 := fun hxz => hx (by rw [hxz]; exact Jm.zero_mem)
  -- The line `L = ⟨x⟩` meets the junk span trivially.
  have hLfr : Module.finrank (ZMod p) (ZMod p ∙ x) = 1 := finrank_span_singleton hx0
  have hdisj_inf : (ZMod p ∙ x) ⊓ Jm = ⊥ := by
    have hd : Disjoint Jm (ZMod p ∙ x) :=
      (Submodule.disjoint_span_singleton' (s := Jm) hx0).mpr hx
    exact disjoint_iff.mp hd.symm
  -- A complement `N` of `Jm ⊔ L`; then `E₀ := Jm ⊔ N` contains the junk span and is a complement
  -- of `L`.
  obtain ⟨N, hc2⟩ := Submodule.exists_isCompl (Jm ⊔ (ZMod p ∙ x))
  have hJm_le : Jm ≤ Jm ⊔ N := le_sup_left
  have hdisj2 : (ZMod p ∙ x) ⊓ (Jm ⊔ N) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Submodule.mem_bot]
    obtain ⟨hzL, hzJN⟩ := Submodule.mem_inf.mp hz
    obtain ⟨j, hjJ, n, hnN, hjn⟩ := Submodule.mem_sup.mp hzJN
    -- `n = z - j` lies both in `Jm ⊔ L` and in `N`, hence is zero.
    have hn_mem : n ∈ (Jm ⊔ (ZMod p ∙ x) : Submodule (ZMod p) E) := by
      have hn_eq : n = (j + n) - j := by abel
      rw [hn_eq, hjn]
      exact Submodule.sub_mem _ (Submodule.mem_sup_right hzL) (Submodule.mem_sup_left hjJ)
    have hn0 : n = 0 := by
      have : n ∈ (⊥ : Submodule (ZMod p) E) := by
        rw [← hc2.inf_eq_bot]
        exact Submodule.mem_inf.mpr ⟨hn_mem, hnN⟩
      simpa using this
    have hzJ : z ∈ Jm := by
      rw [← hjn, hn0, add_zero]
      exact hjJ
    have : z ∈ (⊥ : Submodule (ZMod p) E) := by
      rw [← hdisj_inf]
      exact Submodule.mem_inf.mpr ⟨hzL, hzJ⟩
    simpa using this
  have hcodisj : (ZMod p ∙ x) ⊔ (Jm ⊔ N) = ⊤ := by
    rw [← hc2.sup_eq_top]
    ac_rfl
  have hc : IsCompl (ZMod p ∙ x) (Jm ⊔ N) :=
    ⟨disjoint_iff.mpr hdisj2, codisjoint_iff.mpr hcodisj⟩
  -- `E₀ = Jm ⊔ N` is a proper subspace since `L` is a nonzero complement.
  have hE₀ne : (Jm ⊔ N : Submodule (ZMod p) E) ≠ ⊤ := by
    intro htop
    have hLfr' := hLfr
    rw [htop, inf_top_eq] at hdisj2
    rw [hdisj2, finrank_bot] at hLfr'
    exact Nat.one_ne_zero hLfr'.symm
  refine ⟨ZMod p ∙ x, Jm ⊔ N, hc, hLfr, ?_, ?_, ?_⟩
  · exact Submodule.finrank_lt hE₀ne
  · intro z hz
    rw [Submodule.mem_toAddSubgroup]
    exact hJm_le (by simpa [Jm, addSubgroupToSubmodule] using hz)
  · refine ⟨(Jm ⊔ N).projectionOnto (ZMod p ∙ x) hc.symm,
      (ZMod p ∙ x).projectionOnto (Jm ⊔ N) hc, ?_, ?_, ?_, ?_⟩
    · intro z
      rw [Submodule.coe_projectionOnto_apply, Submodule.coe_projectionOnto_apply]
      exact Submodule.projection_add_projection_eq_self hc.symm z
    · intro z hz
      have hz' := Submodule.projectionOnto_apply_of_mem_left (hpq := hc.symm) hz
      simpa using congrArg Subtype.val hz'
    · intro z hz
      have hz' := Submodule.projectionOnto_apply_of_mem_left (hpq := hc) hz
      simpa using congrArg Subtype.val hz'
    · intro z hz
      have hzJ : z ∈ Jm := by simpa [Jm, addSubgroupToSubmodule] using hz
      have hzE : z ∈ (Jm ⊔ N : Submodule (ZMod p) E) := hJm_le hzJ
      have hz0 : (ZMod p ∙ x).projectionOnto (Jm ⊔ N) hc z = 0 :=
        (Submodule.projectionOnto_apply_eq_zero_iff (h := hc)).mpr hzE
      show (((ZMod p ∙ x).projectionOnto (Jm ⊔ N) hc z : ↥(ZMod p ∙ x)) : E) = 0
      rw [hz0]
      rfl

end Work.SSGRoute.ZConstruction
