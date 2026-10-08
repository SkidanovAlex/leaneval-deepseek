import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The `p`-rank is bounded by `log_p |G|`

This file proves `Work.PGroup.mRank_le_log_card`: for a finite group `G` and a prime `p`, the
`p`-rank `m_p(G)` (the maximum of the minimal number of generators of an elementary abelian
`p`-subgroup of `G`, FT §2) is at most `Nat.log p |G|`.

The mathematical content is that a finite elementary abelian `p`-group `E` of order `p ^ m`
*needs* exactly `m` generators, i.e. `Group.rank E = m = Nat.log p |E|`: a basis of the
`𝔽_p`-vector space `E` generates `E` as a group (giving `rank E ≤ m`), and conversely any
generating set of `E` spans `E` over `𝔽_p` (giving `m ≤ rank E`; only the first inequality is
needed below).  Since `|E| ≤ |G|`, monotonicity of `Nat.log` finishes the proof.

`𝔽_p` here is `ZMod p`, and the `ZMod p`-module structure on `Additive E` comes from
`AddCommGroup.zmodModule`, available because `E` has exponent `p`.

## Main results

* `Work.PGroup.rank_le_log_card_of_pow_eq_one` : an elementary abelian `p`-group has rank at
  most `log_p` of its order.
* `Work.PGroup.mRank_le_log_card` : `m_p(G) ≤ log_p |G|`.
-/

set_option linter.style.haveILetI false

namespace Work.PGroup

/-- **Key auxiliary result.** A finite commutative group of exponent dividing the prime `p`,
regarded as a module over `𝔽_p = ZMod p`, has rank at most the `p`-logarithm of its cardinality.

The proof uses a basis `b` of `V = Additive E` over `ZMod p`: the `i`-th basis vectors, read back
in `E`, form a generating set of `E` with `Module.finrank (ZMod p) V` elements, whence
`Group.rank E ≤ finrank`; and `Nat.card E = p ^ finrank` by `Module.card_eq_pow_finrank`. -/
theorem rank_le_log_card_of_zmod_module {E : Type*} [CommGroup E] [Finite E] {p : ℕ}
    [Module (ZMod p) (Additive E)] [Module.Finite (ZMod p) (Additive E)]
    [Module.Free (ZMod p) (Additive E)] [StrongRankCondition (ZMod p)] (hp : p.Prime) :
    Group.rank E ≤ Nat.log p (Nat.card E) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype (Additive E) := Fintype.ofFinite _
  let b := Module.finBasis (ZMod p) (Additive E)
  -- The basis vectors generate `E` as a group.
  have hgen : Subgroup.closure (Set.range fun i => Additive.toMul (b i)) = ⊤ := by
    set H : Subgroup E := Subgroup.closure (Set.range fun i => Additive.toMul (b i)) with hH
    set A : AddSubgroup (Additive E) := Subgroup.toAddSubgroup H with hA
    have htop : A = ⊤ := by
      have hle : (⊤ : Submodule (ZMod p) (Additive E)) ≤
          AddSubgroup.toZModSubmodule p A := by
        rw [← Module.Basis.span_eq b, Submodule.span_le]
        rintro x ⟨i, rfl⟩
        have hmem : Additive.toMul (b i) ∈ H := Subgroup.subset_closure ⟨i, rfl⟩
        simpa [hA] using hmem
      refine le_antisymm le_top fun x hx => ?_
      simpa using hle trivial
    exact Subgroup.toAddSubgroup.injective (by rw [← hA, htop, OrderIso.map_top])
  -- Hence `Group.rank E ≤ finrank`.
  have hrank : Group.rank E ≤ Module.finrank (ZMod p) (Additive E) := by
    have hS : (↑(Finset.univ.image fun i => Additive.toMul (b i)) : Set E) =
        Set.range fun i => Additive.toMul (b i) := by
      ext x; simp
    have h1 : Group.rank E ≤ (Finset.univ.image fun i => Additive.toMul (b i)).card :=
      Group.rank_le (by rw [hS]; exact hgen)
    have h2 : (Finset.univ.image fun i => Additive.toMul (b i)).card ≤
        Module.finrank (ZMod p) (Additive E) := by
      calc _ ≤ (Finset.univ : Finset (Fin (Module.finrank (ZMod p) (Additive E)))).card :=
            Finset.card_image_le
        _ = Module.finrank (ZMod p) (Additive E) := by simp
    exact h1.trans h2
  -- and `|E| = p ^ finrank`.
  have hcard : Nat.card E = p ^ Module.finrank (ZMod p) (Additive E) :=
    calc Nat.card E = Fintype.card (Additive E) :=
          (Nat.card_congr Additive.toMul).symm.trans Nat.card_eq_fintype_card
      _ = Fintype.card (ZMod p) ^ Module.finrank (ZMod p) (Additive E) :=
          Module.card_eq_pow_finrank (K := ZMod p) (V := Additive E)
      _ = p ^ Module.finrank (ZMod p) (Additive E) := by rw [ZMod.card p]
  calc Group.rank E ≤ Module.finrank (ZMod p) (Additive E) := hrank
    _ = Nat.log p (p ^ Module.finrank (ZMod p) (Additive E)) := (Nat.log_pow hp.one_lt _).symm
    _ = Nat.log p (Nat.card E) := by rw [hcard]

/-- A finite group all of whose elements have order dividing the prime `p`, and which is
commutative, has rank at most `log_p` of its cardinality (elementary abelian `p`-groups have
equality).

This is the form in which the result is applied below: the commutativity and the exponent
condition are precisely what makes `Additive E` a module over `𝔽_p`. -/
theorem rank_le_log_card_of_pow_eq_one {E : Type*} [Group E] [Finite E] {p : ℕ}
    (hp : p.Prime) (hcomm : ∀ a b : E, a * b = b * a) (hexp : ∀ x : E, x ^ p = 1) :
    Group.rank E ≤ Nat.log p (Nat.card E) := by
  letI : CommGroup E := { ‹Group E› with mul_comm := hcomm }
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  letI hmod : Module (ZMod p) (Additive E) := AddCommGroup.zmodModule (fun x => by
    have hx : (Additive.toMul x) ^ p = 1 := hexp _
    have h : (p • x).toMul = (0 : Additive E).toMul := by rw [toMul_nsmul, hx, toMul_zero]
    exact Additive.toMul.injective h)
  have hfin : Module.Finite (ZMod p) (Additive E) := Module.Finite.of_finite
  have hfree : Module.Free (ZMod p) (Additive E) :=
    Module.Free.of_divisionRing (ZMod p) (Additive E)
  have hsrr : StrongRankCondition (ZMod p) := commRing_strongRankCondition (ZMod p)
  exact @rank_le_log_card_of_zmod_module E _ _ p hmod hfin hfree hsrr hp

theorem mRank_le_log_card {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) :
    Work.PGroup.mRank p G ≤ Nat.log p (Nat.card G) := by
  classical
  -- `mRank p G` is a supremum over the ranks of the elementary abelian `p`-subgroups of `G`.
  refine csSup_le ⟨0, ⊥, isElementaryAbelian_bot p, ?_⟩ ?_
  · exact Group.rank_eq_zero (⊥ : Subgroup G)
  · rintro n ⟨E, hE, hrank⟩
    rw [← hrank]
    calc Group.rank E ≤ Nat.log p (Nat.card E) :=
          rank_le_log_card_of_pow_eq_one hp (fun a b => isMulCommutative_iff.mp hE.1 a b) hE.2
      _ ≤ Nat.log p (Nat.card G) :=
          Nat.log_mono_right
            (Nat.card_le_card_of_injective (Subtype.val : E → G) Subtype.val_injective)

end Work.PGroup
