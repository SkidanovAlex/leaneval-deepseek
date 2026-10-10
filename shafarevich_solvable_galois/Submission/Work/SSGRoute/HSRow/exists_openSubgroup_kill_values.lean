import Mathlib.GroupTheory.CosetCover
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.HSRow.NormalFormDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Killing the values of a locally constant family of cocycles

If `Φ : C = closure (zpowers σ) → Zr` is locally constant, where `Zr` is the module of locally
constant `1`-cocycles on `I`, then there is an open normal subgroup `Q ≤ Gal(Ω/k)` such that
every value of `Φ` vanishes on `Q ∩ I`.
-/

open scoped Pointwise
open Classical

namespace Work.SSGRoute.HSRow

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- If `Φ : C → Zr` is locally constant, where `C = closure (zpowers σ)` and `Zr` is the module of
locally constant `1`-cocycles on `I`, then there is an open normal subgroup `Q ≤ Gal(Ω/k)` such that
every value of `Φ` vanishes on `Q ∩ I`.

Suggested proof: `hΦlc` gives an open subgroup `W ≤ C` with `Φ (γ*u) = Φ γ`; since `↥(Ccl k Ω σ)`
is compact and `W` is open it has finite index, so `Set.range Φ` is finite. For each
`V ∈ Set.range Φ`, `V ∈ Zr` is locally constant (`IsLocConstI`), giving an open subgroup `U_V` of
`Gal(Ω/k)` with `V (g*u) = V g` for `(u : Gal(Ω/k)) ∈ U_V`; at `g = 1` and `V 1 = 0` (the `1`-cocycle
law at `(1,1)`) this gives `V = 0` on `I ∩ U_V`. Then `Q₀ := ⋂_{V ∈ range Φ} U_V` is a finite
intersection of open subgroups, hence open, and `Subgroup.normalCore Q₀` is open
(`Subgroup.normalCore_isClosed` + `Subgroup.isOpen_of_isClosed_of_finiteIndex`) and normal. -/
theorem exists_openSubgroup_kill_values
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (Φ : ↥(Ccl k Ω σ) → ↥(Zr p k Ω K M I))
    (hΦlc : ∃ W : Subgroup ↥(Ccl k Ω σ), IsOpen (W : Set ↥(Ccl k Ω σ)) ∧
      ∀ γ : ↥(Ccl k Ω σ), ∀ u ∈ W, Φ (γ * u) = Φ γ) :
    ∃ Q : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (Q : Set (Ω ≃ₐ[k] Ω)) ∧ Q.Normal ∧
      (∀ z : ↥I, (z : Ω ≃ₐ[k] Ω) ∈ Q → ∀ V ∈ Set.range Φ, (V : ↥I → M) z = 0) := by
  classical
  obtain ⟨W, hWopen, hWinv⟩ := hΦlc
  -- `↥(Ccl k Ω σ)` is compact, being a closed subgroup of the compact group `Gal(Ω/k)`.
  haveI hCcompact : CompactSpace ↥(Ccl k Ω σ) :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_topologicalClosure (Subgroup.zpowers σ)).isCompact
  -- Hence the open subgroup `W` has finite index, so `Φ` has finite range.
  haveI hWquot : Finite (↥(Ccl k Ω σ) ⧸ W) := Subgroup.quotient_finite_of_isOpen W hWopen
  have hWindex : W.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨t, -, hcover⟩ := W.exists_leftTransversal_of_FiniteIndex (H := ⊤) le_top
  have hcover_mem : ∀ γ : ↥(Ccl k Ω σ), ∃ g ∈ t, ∃ w ∈ W, (g : ↥(Ccl k Ω σ)) * w = γ := by
    intro γ
    have h1 : γ ∈ ⋃ g ∈ t, (g : ↥(Ccl k Ω σ)) • (W : Set ↥(Ccl k Ω σ)) := by
      rw [hcover]; simp
    simp only [Set.mem_iUnion, Set.mem_smul_set] at h1
    obtain ⟨g, hgt, w, hw, hgw⟩ := h1
    exact ⟨g, hgt, w, hw, hgw⟩
  have hrange : (Set.range Φ).Finite := by
    refine ((Finset.finite_toSet t).image
      (fun g : ↥(⊤ : Subgroup ↥(Ccl k Ω σ)) => (↑g : ↥(Ccl k Ω σ)))).image Φ |>.subset ?_
    intro V hV
    simp only [Set.mem_range] at hV
    obtain ⟨γ, rfl⟩ := hV
    obtain ⟨g, hgt, w, hw, hgw⟩ := hcover_mem γ
    rw [Set.mem_image]
    refine ⟨(g : ↥(Ccl k Ω σ)), ?_, ?_⟩
    · exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr hgt)
    · rw [← hWinv (g : ↥(Ccl k Ω σ)) w hw, hgw]
  -- For each value `V` of `Φ`, local constancy produces an open subgroup killing `V` on `I`.
  have hUexists : ∀ V : ↥(Zr p k Ω K M I), ∃ U : Subgroup (Ω ≃ₐ[k] Ω),
      IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧ ∀ z : ↥I, (z : Ω ≃ₐ[k] Ω) ∈ U → (V : ↥I → M) z = 0 := by
    intro V
    obtain ⟨hcoc, hloc⟩ := (mem_Zr p k Ω K M I V.1).mp V.2
    obtain ⟨U, hUo, hUk⟩ := hloc
    refine ⟨U, hUo, fun z hz => ?_⟩
    have hz1 : (V : ↥I → M) z = V.1 1 := by
      have h := hUk (1 : ↥I) z hz
      simpa using h
    have hone : V.1 (1 : ↥I) = 0 := by
      have h := hcoc (1 : ↥I) (1 : ↥I)
      simp only [mul_one, Subgroup.coe_one, map_one, one_smul] at h
      exact (add_left_cancel (show V.1 1 + 0 = V.1 1 + V.1 1 by rw [add_zero, ← h])).symm
    rw [hz1, hone]
  let U : ↥(Zr p k Ω K M I) → Subgroup (Ω ≃ₐ[k] Ω) := fun V => Classical.choose (hUexists V)
  have hUopen : ∀ V, IsOpen (U V : Set (Ω ≃ₐ[k] Ω)) :=
    fun V => (Classical.choose_spec (hUexists V)).1
  have hUkill : ∀ (V : ↥(Zr p k Ω K M I)) (z : ↥I),
      (z : Ω ≃ₐ[k] Ω) ∈ U V → (V : ↥I → M) z = 0 :=
    fun V => (Classical.choose_spec (hUexists V)).2
  -- Intersect the finitely many `U_V` and take the normal core.
  let ι := {V : ↥(Zr p k Ω K M I) // V ∈ hrange.toFinset}
  let Q₀ : Subgroup (Ω ≃ₐ[k] Ω) := ⨅ V : ι, U V.1
  have hQ₀open : IsOpen (Q₀ : Set (Ω ≃ₐ[k] Ω)) := by
    have hcoe : (Q₀ : Set (Ω ≃ₐ[k] Ω)) = ⋂ V : ι, (U V.1 : Set (Ω ≃ₐ[k] Ω)) :=
      Subgroup.coe_iInf
    rw [hcoe]
    exact isOpen_iInter_of_finite (fun V => hUopen V.1)
  have hUfin : ∀ V, (U V).FiniteIndex := fun V => by
    haveI : Finite ((Ω ≃ₐ[k] Ω) ⧸ U V) := Subgroup.quotient_finite_of_isOpen (U V) (hUopen V)
    exact Subgroup.finiteIndex_of_finite_quotient
  haveI hQ₀fin : Q₀.FiniteIndex := by
    change (⨅ V : ι, U V.1).FiniteIndex
    exact Subgroup.finiteIndex_iInf (fun V => hUfin V.1)
  have hQ₀closed : IsClosed (Q₀ : Set (Ω ≃ₐ[k] Ω)) := Subgroup.isClosed_of_isOpen Q₀ hQ₀open
  have hQclosed : IsClosed (Q₀.normalCore : Set (Ω ≃ₐ[k] Ω)) :=
    Subgroup.normalCore_isClosed Q₀ hQ₀closed
  haveI hQfin : Q₀.normalCore.FiniteIndex := Subgroup.finiteIndex_normalCore Q₀
  refine ⟨Q₀.normalCore, Subgroup.isOpen_of_isClosed_of_finiteIndex _ hQclosed,
    Subgroup.normalCore_normal Q₀, ?_⟩
  intro z hz V hVmem
  have hVt : V ∈ hrange.toFinset := (Set.Finite.mem_toFinset hrange).mpr hVmem
  have hzQ₀ : (z : Ω ≃ₐ[k] Ω) ∈ Q₀ := Subgroup.normalCore_le Q₀ hz
  have hzU : (z : Ω ≃ₐ[k] Ω) ∈ U V := by
    have hle : Q₀ ≤ U V := by
      change (⨅ V : ι, U V.1) ≤ U V
      exact iInf_le _ (⟨V, hVt⟩ : ι)
    exact hle hzQ₀
  exact hUkill V z hzU

end

end Work.SSGRoute.HSRow
