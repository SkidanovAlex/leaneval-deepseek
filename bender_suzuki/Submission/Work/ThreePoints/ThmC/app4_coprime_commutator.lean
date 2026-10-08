import Mathlib
import Submission.Work.Coprime.Internal
import Submission.Work.Coprime.Basic
import Submission.Work.Coprime.commutator_commutator_eq
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise commutatorElement

namespace Work.ThreePoints.ThmC

/-- **The bridge between the abstract and the internal commutator, relative to a subgroup.**
Let `X` normalise `Q ≤ Γ` and let `H ≤ ↥Q`.  Then the abstract commutator `FT.commutator ↥X H`
of `H` with the conjugation action of `X` on `↥Q`, pushed into `Γ`, is the internal commutator
`⁅H, X⁆` of the image of `H` with `X`.

This generalises `FT.commutator_conjAction` (the case `H = ⊤`). -/
theorem map_commutator_conjAction {Γ : Type} [Group Γ] {Q X : Subgroup Γ} [FT.Normalizes X Q]
    (H : Subgroup ↥Q) :
    (FT.commutator ↥X H).map Q.subtype = ⁅H.map Q.subtype, X⁆ := by
  refine le_antisymm ?_ ?_
  · -- Every generator `x⁻¹ * (a • x)` of `FT.commutator ↥X H` maps to the commutator
    -- `⁅x⁻¹, a⁆` of two elements of `H.map Q.subtype` and `X`.
    rw [Subgroup.map_le_iff_le_comap]
    refine FT.commutator_le fun a x hx => ?_
    show Q.subtype (x⁻¹ * (a • x)) ∈ ⁅H.map Q.subtype, X⁆
    have hmem := Subgroup.commutator_mem_commutator (H₁ := H.map Q.subtype) (H₂ := X)
      (Subgroup.mem_map_of_mem Q.subtype (H.inv_mem hx)) a.2
    convert hmem using 1
    simp [FT.conj_smul_coe, commutatorElement_def, mul_assoc]
  · -- Conversely `⁅h, a⁆` with `h ∈ H` is the image of the generator `h * (a • h⁻¹)`.
    refine Subgroup.commutator_le.mpr ?_
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨h, hh, rfl⟩ := hg₁
    show ⁅(h : Γ), g₂⁆ ∈ Subgroup.map Q.subtype (FT.commutator (↥X) H)
    have hz : Q.subtype (h * ((⟨g₂, hg₂⟩ : ↥X) • h⁻¹)) = ⁅(h : Γ), g₂⁆ := by
      simp [FT.conj_smul_coe, commutatorElement_def, mul_assoc]
    rw [← hz]
    exact Subgroup.mem_map_of_mem Q.subtype (by
      simpa using FT.le_commutator (⟨g₂, hg₂⟩ : ↥X) (H.inv_mem hh))

/-- Peterfalvi I App. IV, Lemma 1(a) (Huppert III.13.3/13.4), internal form.

Let `X` be a `p'`-subgroup of a finite group `Γ` normalising a `p`-subgroup `Q ≤ Γ`. Then the
internal commutator satisfies `⁅⁅Q,X⁆,X⁆ = ⁅Q,X⁆` (here `Q` is not assumed normal in `Γ`, only
normalised by `X`).

Route: view `X` as acting on the group `↥Q` by conjugation (`FT.Normalizes X Q`, giving
`MulDistribMulAction ↥X ↥Q`). Since `⁅Q,X⁆ ≤ Q` when `X ≤ N(Q)`, the bridge
`FT.commutator_conjAction X Q : (FT.commutator ↥X ⊤).map Q.subtype = ⁅Q,X⁆` identifies
`FT.commutator ↥X ⊤` with `⁅Q,X⁆`; more generally prove the auxiliary bridge
`(FT.commutator ↥X H).map Q.subtype = ⁅H.map Q.subtype, X⁆` for every `H : Subgroup ↥Q` (both
inclusions by `Subgroup.closure_le` / `Subgroup.commutator_le` and
`FT.conj_smul_coe : ↑(a • x) = ↑a * ↑x * (↑a)⁻¹`).
Then apply `Work.Coprime.commutator_commutator_eq ↥X hcop hsol` in the group `↥Q`, where
`hcop : Nat.Coprime (Nat.card ↥X) (Nat.card ↥Q)` follows from `hXp` and the fact that `Nat.card ↥Q`
is a power of `p` (`IsPGroup.iff_card`; trivially `|Q| = 1` is also a `p`-power), and
`hsol : IsSolvable ↥X ∨ IsSolvable ↥Q` holds because `↥Q` is a `p`-group, hence nilpotent, hence
solvable. Mapping the resulting identity
`FT.commutator ↥X (FT.commutator ↥X ⊤) = FT.commutator ↥X ⊤` under `Q.subtype` and using the
auxiliary bridge with `H := FT.commutator ↥X ⊤` on the left and `FT.commutator_conjAction X Q` on
both sides gives `⁅⁅Q,X⁆,X⁆ = ⁅Q,X⁆`. -/
theorem app4_coprime_commutator {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ} (hp : p.Prime)
    {Q X : Subgroup Γ} (hQp : IsPGroup p Q) (hXp : Nat.Coprime (Nat.card X) p)
    (hXQ : X ≤ Subgroup.normalizer (Q : Set Γ)) :
    ⁅⁅Q, X⁆, X⁆ = ⁅Q, X⁆ := by
  -- `X` acts on `↥Q` by conjugation.
  have : FT.Normalizes X Q := ⟨hXQ⟩
  have : Fact p.Prime := ⟨hp⟩
  -- `|X|` is coprime to `|Q|` because `|Q|` is a power of `p`.
  have hcop : Nat.Coprime (Nat.card ↥X) (Nat.card ↥Q) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQp
    rw [hn]
    exact hXp.pow_right n
  -- `↥Q` is a `p`-group, hence nilpotent, hence solvable.
  have hsol : Group.IsSolvable ↥X ∨ Group.IsSolvable ↥Q := by
    right
    have := IsPGroup.isNilpotent hQp
    infer_instance
  -- The coprime action identity in the group `↥Q`.
  have hmain := Work.Coprime.commutator_commutator_eq ↥X hcop hsol
  -- The bridge, specialised to `H = ⊤` and to `H = FT.commutator ↥X ⊤`.
  have h1 : (FT.commutator ↥X (⊤ : Subgroup ↥Q)).map Q.subtype = ⁅Q, X⁆ := by
    rw [map_commutator_conjAction (H := ⊤), Subgroup.map_top, Subgroup.range_subtype]
  have h2 : (FT.commutator ↥X (FT.commutator ↥X (⊤ : Subgroup ↥Q))).map Q.subtype
      = ⁅⁅Q, X⁆, X⁆ := by
    rw [map_commutator_conjAction (H := FT.commutator ↥X ⊤), h1]
  rw [← h2, ← h1]
  exact congrArg (Subgroup.map Q.subtype) hmain

end Work.ThreePoints.ThmC
