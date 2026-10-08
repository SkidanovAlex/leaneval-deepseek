import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.ChV12.fixedField_card_pow
import Submission.Work.ThmF.ChV12.card_map_subgroupOf_eq
import Submission.Work.ThmF.ChV12.mem_fixedField_iff_mem_centralizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Ch. V §3, step (1): `|C_{Q₀}(P)| ^ |P| = |Q₀|` for `P ≤ V` of prime order with `P ∩ W = 1`

Peterfalvi II, Ch. V §1 Prop. 3 identifies `Q₀ = ⟨Inv H⟩` with the additive group of a finite
field `F`, `V = C_D(t)` with a group of field automorphisms of `F`, and `W = C_V(K)` with the
kernel of that action.  Consequently a subgroup `P ≤ V` with `P ∩ W = 1` acts faithfully by
field automorphisms and, `P` being of prime order `p`, the group `C_{Q₀}(P)` of fixed points of
`P` in `Q₀` is the fixed field of a group of automorphisms of `F` of order `p`, whence (Artin)
`|C_{Q₀}(P)| ^ p = |Q₀|`.

The proof is assembled from three general lemmas, each in its own module:

* `Work.ThmF.ChV12.fixedField_card_pow` — Artin: for a finite field `F` and a subgroup `A` of
  its automorphism group, `|F^A| ^ |A| = |F|`;
* `Work.ThmF.ChV12.card_map_subgroupOf_eq` — the image of `P ≤ V` under a homomorphism with
  kernel `W` and with `P ∩ W = 1` has order `|P|`;
* `Work.ThmF.ChV12.mem_fixedField_iff_mem_centralizer` — the fixed points of `P` in `Q₀` are
  exactly the elements whose image in `F` lies in the fixed field of the image of `P`.

Together with the elementary `conj_mem_Q0sub` (below) these give, `A` being the image of `P` in
`F ≃+* F`:

  `|C_{Q₀}(P)| ^ |P| = |F^A| ^ |A| = |F| = |Q₀|`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV12

open Classical Submission.Blueprint

/-- Conjugation by an element of `H` preserves `Q₀sub H = ⟨Q₀ H⟩`: it permutes the set
`Q₀ H = Inv(H) ∪ {1}`, hence the subgroup this set generates.  (This is the clause of
`Q0sub_elementary` that does not need the involutions of `H` to commute.) -/
theorem conj_mem_Q0sub {G : Type} [Group G] {H : Subgroup G} {v : G} (hv : v ∈ H) {x : G}
    (hx : x ∈ Q0sub H) : v * x * v⁻¹ ∈ Q0sub H := by
  have hmem : ∀ y ∈ Q0 H, v * y * v⁻¹ ∈ Q0 H := by
    intro y hy
    rw [mem_Q0_iff] at hy ⊢
    rcases hy with ⟨hyH, hyo⟩ | rfl
    · refine Or.inl ⟨H.mul_mem (H.mul_mem hv hyH) (H.inv_mem hv), ?_⟩
      have hconj : v * y * v⁻¹ = (MulAut.conj v) y := by rw [MulAut.conj_apply]
      rw [hconj]
      exact (orderOf_injective (MulAut.conj v).toMonoidHom (MulAut.conj v).injective y).trans hyo
    · exact Or.inr (by group)
  have hle : Subgroup.map (MulAut.conj v).toMonoidHom (Q0sub H) ≤ Q0sub H := by
    rw [Subgroup.map_le_iff_le_comap, Q0sub]
    refine (Subgroup.closure_le _).mpr (fun y hy => ?_)
    simpa [MulAut.conj_apply, Q0sub] using Q0_le_Q0sub H (hmem y hy)
  simpa [MulAut.conj_apply] using hle (Subgroup.mem_map_of_mem _ hx)

open Classical Submission.Blueprint in theorem prop3_card_fixed_pow {G : Type} [Group G] [Finite G] (H Q : Subgroup G) (t : G) {P : Subgroup G} (hPV : P ≤ centD H t) (hPW : P ⊓ Work.ThmF.W H t = ⊥) (hp : (Nat.card P).Prime) (hstr : ∃ (F : Type) (_ : Field F) (_ : Fintype F) (e : ↥(Work.ThmF.Q0sub H) ≃* Multiplicative F) (ρ : ↥(centD H t) →* (F ≃+* F)), ρ.ker = (Work.ThmF.W H t).subgroupOf (centD H t) ∧ ∀ (v : ↥(centD H t)) (x : ↥(Work.ThmF.Q0sub H)) (hx : (v : G) * x * (v : G)⁻¹ ∈ Work.ThmF.Q0sub H), Multiplicative.toAdd (e ⟨(v : G) * x * (v : G)⁻¹, hx⟩) = ρ v (Multiplicative.toAdd (e x))) : Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) ^ Nat.card P = Nat.card ↥(Work.ThmF.Q0sub H) := by
  classical
  obtain ⟨F, hFld, hFint, e, ρ, hker, hact⟩ := hstr
  -- the image `A` of `P` in the automorphism group of `F`, of order `|P|`
  set A : Subgroup (F ≃+* F) := Subgroup.map ρ (P.subgroupOf (centD H t)) with hAdef
  have hAcard : Nat.card A = Nat.card P := card_map_subgroupOf_eq H t P hPV hPW ρ hker
  have hfield : Nat.card ↥(FixedPoints.subfield A F) ^ Nat.card A = Nat.card F :=
    fixedField_card_pow (F := F) A
  -- the fixed points of `P` on `Q₀` are the fixed field of `A`, via `e`
  have hkey : ∀ x : ↥(Q0sub H),
      Multiplicative.toAdd (e x) ∈ FixedPoints.subfield A F ↔
        (x : G) ∈ Subgroup.centralizer (P : Set G) :=
    fun x => mem_fixedField_iff_mem_centralizer H Q t hPV
      (fun v hv x hx => conj_mem_Q0sub hv hx) e ρ hact x
  -- the two fixed-point sets are in bijection through `e`
  have hfixCard : Nat.card ↥(Q0sub H ⊓ Subgroup.centralizer (P : Set G))
      = Nat.card ↥(FixedPoints.subfield A F) := by
    have hbij : Function.Bijective (fun x : ↥(Q0sub H ⊓ Subgroup.centralizer (P : Set G)) =>
        (⟨Multiplicative.toAdd (e ⟨x.1, x.2.1⟩),
          (hkey ⟨x.1, x.2.1⟩).mpr x.2.2⟩ : ↥(FixedPoints.subfield A F))) := by
      constructor
      · intro x y hxy
        have h1 : Multiplicative.toAdd (e ⟨x.1, x.2.1⟩)
            = Multiplicative.toAdd (e ⟨y.1, y.2.1⟩) := congrArg Subtype.val hxy
        have h2 : (⟨x.1, x.2.1⟩ : ↥(Q0sub H)) = ⟨y.1, y.2.1⟩ :=
          e.injective (Multiplicative.toAdd.injective h1)
        exact Subtype.ext (congrArg (fun z : ↥(Q0sub H) => (z : G)) h2)
      · intro y
        let w : ↥(Q0sub H) := e.symm (Multiplicative.ofAdd (y : F))
        have hwe : e w = Multiplicative.ofAdd (y : F) := MulEquiv.apply_symm_apply e _
        have hwmem : (w : G) ∈ Subgroup.centralizer (P : Set G) :=
          (hkey w).mp (by rw [hwe]; exact y.2)
        refine ⟨⟨w.1, w.2, hwmem⟩, ?_⟩
        apply Subtype.ext
        show Multiplicative.toAdd (e w) = (y : F)
        rw [hwe]
        rfl
    exact Nat.card_congr (Equiv.ofBijective _ hbij)
  have hQcard : Nat.card ↥(Q0sub H) = Nat.card F := by
    rw [Nat.card_congr e.toEquiv]
    exact (Nat.card_congr Multiplicative.ofAdd).symm
  calc Nat.card ↥(Q0sub H ⊓ Subgroup.centralizer (P : Set G)) ^ Nat.card P
      = Nat.card ↥(FixedPoints.subfield A F) ^ Nat.card A := by rw [hfixCard, hAcard]
    _ = Nat.card F := hfield
    _ = Nat.card ↥(Q0sub H) := hQcard.symm

end Work.ThmF.ChV12
