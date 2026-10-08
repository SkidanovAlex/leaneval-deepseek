import Mathlib
import Submission.Work.ThmF.Tools.External

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.hasNormalIndexP_of_commutator_le`

Peterfalvi II, Ch. V §3, step (9): the second Hall–Wielandt reduction.

`X` is a finite group, `S` a Sylow `p`-subgroup, `Z ⊴ X` with `Z ≤ S` and `[S,S] ≤ Z` (so that
`S/Z` is abelian), and `M ⊴ N_X(S)` is a normal subgroup of index `p` containing `Z`.  Then `X`
has a normal subgroup of index `p`.

**Proof.**  `S/Z` is an abelian Sylow `p`-subgroup of `X ⧸ Z`, hence weakly closed, so
Hall–Wielandt (`HallWielandtProp`) applied in `X ⧸ Z` shows that it suffices to produce a normal
subgroup of index `p` in `N_{X⧸Z}(S/Z)`.  That normalizer is the image of `N_X(S)` in `X ⧸ Z`
(because the preimage of `S/Z` is `S`: `Z ≤ S`), and the image of `M` is a normal subgroup of
index `[N_X(S) : M] = p`.  Pulling back along the quotient map `X → X ⧸ Z` finishes.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.ThmF.Prove

open Classical

/-- A normal subgroup of index `p` in a quotient `G ⧸ N` pulls back to a normal subgroup of
index `p` in `G`. -/
private theorem hasNormalIndexP_of_quotient_aux {G : Type} [Group G] {p : ℕ} {N : Subgroup G}
    [N.Normal] (h : Work.ThmF.HasNormalIndexP p (G ⧸ N)) : Work.ThmF.HasNormalIndexP p G := by
  obtain ⟨M, hMnormal, hMindex⟩ := h
  haveI : M.Normal := hMnormal
  exact ⟨M.comap (QuotientGroup.mk' N), Subgroup.normal_comap _, by
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N), hMindex]⟩

/-- The normalizer of the image of a subgroup `S` in a quotient `X ⧸ Z` is the image of the
normalizer, provided `Z ≤ S` (so that the preimage of `S/Z` is `S`). -/
private theorem map_normalizer_quotient {X : Type} [Group X] (Z S : Subgroup X) [Z.Normal]
    (hZS : Z ≤ S) :
    (Subgroup.normalizer (S : Set X)).map (QuotientGroup.mk' Z) =
      Subgroup.normalizer ((S.map (QuotientGroup.mk' Z) : Subgroup (X ⧸ Z)) : Set (X ⧸ Z)) := by
  have hf : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  have hcomap : Subgroup.comap (QuotientGroup.mk' Z)
      (Subgroup.normalizer ((S.map (QuotientGroup.mk' Z) : Subgroup (X ⧸ Z)) : Set (X ⧸ Z)))
      = Subgroup.normalizer (S : Set X) := by
    rw [Subgroup.comap_normalizer_eq_of_surjective _ hf, Subgroup.comap_map_eq,
      QuotientGroup.ker_mk', sup_eq_left.mpr hZS]
  rw [← hcomap, Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hf, top_inf_eq]

theorem hasNormalIndexP_of_commutator_le {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hHW : Work.ThmF.HallWielandtProp) (S : Sylow p X)
    (Z : Subgroup X) (hZn : Z.Normal) (hZle : Z ≤ (S : Subgroup X))
    (hcomm : ∀ a ∈ (S : Subgroup X), ∀ b ∈ (S : Subgroup X), a * b * a⁻¹ * b⁻¹ ∈ Z)
    (M : Subgroup ↥(Subgroup.normalizer (S : Set X))) (hMn : M.Normal) (hMidx : M.index = p)
    (hZleM : Z ≤ Subgroup.map (Subgroup.normalizer (S : Set X)).subtype M) :
    Work.ThmF.HasNormalIndexP p X := by
  classical
  haveI hZnI : Z.Normal := hZn
  have hp : p.Prime := Fact.out
  -- **(0)** `Z` lifts into `M`
  have hZsub : Z.subgroupOf (Subgroup.normalizer (S : Set X)) ≤ M := by
    intro x hx
    have hxZ : (x : X) ∈ Z := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨m, hmM, hmx⟩ := Subgroup.mem_map.mp (hZleM hxZ)
    have h2 : m = x := Subtype.ext hmx
    rw [← h2]; exact hmM
  -- **(1)** the image `Ā = S/Z` of `S` in `X ⧸ Z`
  set Ā : Subgroup (X ⧸ Z) := (S : Subgroup X).map (QuotientGroup.mk' Z) with hĀ
  -- the normalizer of `Ā` is the image of the normalizer of `S`
  have hK : (Subgroup.normalizer (S : Set X)).map (QuotientGroup.mk' Z) =
      Subgroup.normalizer (Ā : Set (X ⧸ Z)) := by
    rw [hĀ]
    exact map_normalizer_quotient Z (S : Subgroup X) hZle
  -- **(2)** `Ā` is abelian, because `[S,S] ≤ Z`
  have hab : ∀ a ∈ Ā, ∀ b ∈ Ā, a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hxS, rfl⟩ := Subgroup.mem_map.mp (hĀ ▸ ha)
    obtain ⟨y, hyS, rfl⟩ := Subgroup.mem_map.mp (hĀ ▸ hb)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_eq_mk']
    refine ⟨(x * y)⁻¹ * (y * x), ?_, by group⟩
    have h1 : (x * y)⁻¹ * (y * x) = y⁻¹ * x⁻¹ * y * x := by group
    rw [h1]
    simpa using hcomm y⁻¹ ((S : Subgroup X).inv_mem hyS) x⁻¹ ((S : Subgroup X).inv_mem hxS)
  -- **(3)** `Ā` is weakly closed in itself (it is a Sylow subgroup, so conjugation cannot shrink
  -- it)
  have hwc : ∀ g : X ⧸ Z, Ā.map (MulAut.conj g).toMonoidHom ≤ Ā →
      Ā.map (MulAut.conj g).toMonoidHom = Ā := by
    intro g hg
    refine Subgroup.eq_of_le_of_card_ge hg ?_
    exact le_of_eq (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm
  -- **(4)** `Ā` is a Sylow `p`-subgroup of `X ⧸ Z`
  let Sbar : Sylow p (X ⧸ Z) := Sylow.mapSurjective (QuotientGroup.mk'_surjective Z) S
  have hSbar : (Sbar : Subgroup (X ⧸ Z)) = Ā := by
    show ((Sylow.mapSurjective (QuotientGroup.mk'_surjective Z) S : Sylow p (X ⧸ Z)) :
      Subgroup (X ⧸ Z)) = Ā
    rw [hĀ]
    exact Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective Z) S
  -- **(5)** Hall–Wielandt in `X ⧸ Z` at the abelian Sylow `Ā = S/Z`
  have hHW' : Work.ThmF.HasNormalIndexP p (X ⧸ Z) ↔
      Work.ThmF.HasNormalIndexP p ↥(Subgroup.normalizer (Ā : Set (X ⧸ Z))) :=
    hHW (X ⧸ Z) p hp Sbar Ā (le_of_eq hSbar.symm) hwc hab
  -- **(6)** the natural map `N_X(S) → N_{X⧸Z}(S/Z)`, which is onto with kernel `Z`
  let ψ : ↥(Subgroup.normalizer (S : Set X)) →* ↥(Subgroup.normalizer (Ā : Set (X ⧸ Z))) :=
    MonoidHom.codRestrict
      ((QuotientGroup.mk' Z).comp (Subgroup.normalizer (S : Set X)).subtype) _
      (fun n => by
        rw [← hK]
        exact Subgroup.mem_map.mpr ⟨(n : X), n.2, rfl⟩)
  have hψsurj : Function.Surjective ψ := by
    intro y
    have hy : (y : X ⧸ Z) ∈ (Subgroup.normalizer (S : Set X)).map (QuotientGroup.mk' Z) := by
      rw [hK]; exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hψker : ψ.ker = Z.subgroupOf (Subgroup.normalizer (S : Set X)) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      have h2 : ψ x = 1 := MonoidHom.mem_ker.mp hx
      have h3 : (QuotientGroup.mk' Z) (x : X) = 1 := by
        have h4 := congrArg Subtype.val h2
        exact h4
      exact (QuotientGroup.eq_one_iff (x : X)).mp h3
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [MonoidHom.mem_ker]
      refine Subtype.ext ?_
      show (QuotientGroup.mk' Z) (x : X) = 1
      exact (QuotientGroup.eq_one_iff (x : X)).mpr hx
  -- **(7)** the image of `M` is a normal subgroup of index `p` in `N_{X⧸Z}(S/Z)`
  have hMnorm : (M.map ψ).Normal := Subgroup.Normal.map hMn ψ hψsurj
  have hMidx' : (M.map ψ).index = p := by
    rw [Subgroup.index_map_eq (f := ψ) M hψsurj (by rw [hψker]; exact hZsub), hMidx]
  have hRHS : Work.ThmF.HasNormalIndexP p ↥(Subgroup.normalizer (Ā : Set (X ⧸ Z))) :=
    ⟨M.map ψ, hMnorm, hMidx'⟩
  -- **(8)** conclude in `X ⧸ Z`, then pull back to `X`
  exact hasNormalIndexP_of_quotient_aux (hHW'.mpr hRHS)

end Work.ThmF.Prove
