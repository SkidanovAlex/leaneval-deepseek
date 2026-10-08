import Mathlib
import Submission.Work.COPR.Glue

namespace Work.COPR

open scoped Pointwise

/-- Transport of conjugation inside a subgroup `K ≤ G` to the ambient group: for `c : ↥K` and a
subgroup `S ≤ ↥K`, mapping the conjugate `MulAut.conj c • S` down along `K.subtype` gives the same
as mapping `S` and conjugating by `(c : G)`. -/
theorem map_subtype_smul_conj {G : Type*} [Group G] (K : Subgroup G) (c : ↥K)
    (S : Subgroup ↥K) :
    (MulAut.conj c • S).map K.subtype =
      (S.map K.subtype).map (MulAut.conj (c : G)).toMonoidHom := by
  have hsmul : MulAut.conj c • S = S.map (MulAut.conj c).toMonoidHom := by
    rw [Subgroup.pointwise_smul_def]; rfl
  rw [hsmul, Subgroup.map_map, Subgroup.map_map]
  congr 1

/-- Bender 1981, 1.1(ii), conjugacy part: two `P`-invariant Sylow `q`-subgroups `R₁, R₂` of the
`p'`-group `K` (`P` a `p`-group acting coprimely, `P ≤ N_G(K)`) are conjugate by an element of
`C_K(P)`.  Second half of `Work.GW2.Coprime11iiProp` of area COPR.

Suggested route: `OddOrder.Isaacs.Ch04.glauberman_fixed_points_conj` (Isaacs Lemma 3.24(b),
`Submission/OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean`) applied to the `↥K`-set
`Sylow q ↥K` with `A := ↥P` and `φ := Work.COPR.conjAct P K hN`; coprimality is
`Work.COPR.coprime_card_of_isPGroup`, solvability of `↥P` is
`Work.COPR.isSolvable_of_isPGroup`, transitivity is Sylow conjugacy in `↥K`
(`Sylow.isPretransitive_of_finite`), and the `P`-invariance of `Rᵢ` gives the fixed-point
hypotheses.  The output element `c` satisfies `φ a c = c`, i.e. `c ∈ C_K(P)`
(`Work.COPR.fixedPoints_conjAct_map`). -/
theorem coprime11ii_conj (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P K : Subgroup G) (hP : IsPGroup p P) (hcop : Nat.Coprime p (Nat.card K))
    (hN : P ≤ Subgroup.normalizer (K : Set G)) :
    ∀ (q : ℕ) [Fact q.Prime] (R₁ R₂ : Subgroup G), R₁ ≤ K → R₂ ≤ K →
      IsPGroup q R₁ → IsPGroup q R₂ → ¬ q ∣ R₁.relIndex K → ¬ q ∣ R₂.relIndex K →
      P ≤ Subgroup.normalizer (R₁ : Set G) → P ≤ Subgroup.normalizer (R₂ : Set G) →
      ∃ c ∈ K ⊓ Subgroup.centralizer (P : Set G), R₂ = R₁.map (MulAut.conj c).toMonoidHom := by
  intro q _ R₁ R₂ hR₁ hR₂ hPg₁ hPg₂ hnd₁ hnd₂ hn₁ hn₂
  haveI : Finite ↥K := inferInstance
  -- `Rᵢ.subgroupOf K` is a `q`-subgroup of `↥K` …
  have hsub₁ : IsPGroup q (R₁.subgroupOf K) := by
    rw [← Subgroup.comap_subtype]
    exact hPg₁.comap_of_injective K.subtype K.subtype_injective
  have hsub₂ : IsPGroup q (R₂.subgroupOf K) := by
    rw [← Subgroup.comap_subtype]
    exact hPg₂.comap_of_injective K.subtype K.subtype_injective
  -- … and, since `q ∤ [K : Rᵢ]`, a Sylow `q`-subgroup of `↥K`.
  let S₁ : Sylow q ↥K := hsub₁.toSylow hnd₁
  let S₂ : Sylow q ↥K := hsub₂.toSylow hnd₂
  have hS₁ : (S₁ : Subgroup ↥K) = R₁.subgroupOf K := rfl
  have hS₂ : (S₂ : Subgroup ↥K) = R₂.subgroupOf K := rfl
  -- `P`-invariance of `Rᵢ` gives `↥P`-invariance of `Sᵢ` under the conjugation action.
  have hinv₁ : OddOrder.Isaacs.Ch03.IsAInvariant (conjAct P K hN) (S₁ : Subgroup ↥K) := by
    rw [hS₁, OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [conjAct_apply_coe]
    exact ((Subgroup.mem_normalizer_iff.mp (hn₁ a.2)) (x : G)).mp hx
  have hinv₂ : OddOrder.Isaacs.Ch03.IsAInvariant (conjAct P K hN) (S₂ : Subgroup ↥K) := by
    rw [hS₂, OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [conjAct_apply_coe]
    exact ((Subgroup.mem_normalizer_iff.mp (hn₂ a.2)) (x : G)).mp hx
  -- Apply Isaacs 3.23(b) (Glauberman 3.24(b)) inside `↥K`.
  have hsolv : Group.IsSolvable ↥P ∨ Group.IsSolvable ↥K :=
    Or.inl (isSolvable_of_isPGroup p hP)
  have hcop' : Nat.Coprime (Nat.card ↥P) (Nat.card ↥K) := coprime_card_of_isPGroup p hP hcop
  obtain ⟨cK, hcK_fix, hcK_smul⟩ :=
    OddOrder.Isaacs.Ch04.aInvariant_sylow_conj (φ := conjAct P K hN) hcop' hsolv hinv₁ hinv₂
  refine ⟨(cK : G), ⟨cK.2, ?_⟩, ?_⟩
  · -- `cK` is fixed by the conjugation action of `↥P`, i.e. centralises `P`.
    change (cK : G) ∈ Subgroup.centralizer (P : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 : h * (cK : G) * h⁻¹ = (cK : G) := by
      have h2 := congrArg (Subtype.val : ↥K → G) (hcK_fix ⟨h, hh⟩)
      rw [conjAct_apply_coe] at h2
      simpa using h2
    calc h * (cK : G) = h * (cK : G) * h⁻¹ * h := by group
      _ = (cK : G) * h := by rw [h1]
  · -- Transport the conjugacy `MulAut.conj cK • S₁ = S₂` back to `G`.
    have h₂ : R₂ ⊓ K = R₂ := le_antisymm inf_le_left (le_inf le_rfl hR₂)
    have h₁ : R₁ ⊓ K = R₁ := le_antisymm inf_le_left (le_inf le_rfl hR₁)
    have hmap : (MulAut.conj cK • (R₁.subgroupOf K)).map K.subtype = R₂ := by
      have h := congrArg (Subgroup.map K.subtype) hcK_smul
      rw [hS₁, hS₂, Subgroup.subgroupOf_map_subtype, h₂] at h
      exact h
    have key : (MulAut.conj cK • (R₁.subgroupOf K)).map K.subtype =
        R₁.map (MulAut.conj (cK : G)).toMonoidHom := by
      rw [map_subtype_smul_conj, Subgroup.subgroupOf_map_subtype, h₁]
    rw [← hmap, key]

end Work.COPR
