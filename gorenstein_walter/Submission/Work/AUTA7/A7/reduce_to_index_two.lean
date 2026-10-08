import Mathlib
import Submission.Work.AUTA7.Defs
import Submission.Work.AUTA7.A7.dihedral_subgroup_isCyclic_or_dihedral
import Submission.Work.AUTA7.A7.exists_subgroup_index_two_of_isPGroup_two
import Submission.Work.AUTA7.GroupTheory.CardInfSylowTwo

set_option linter.style.haveILetI false

namespace Work.AUTA7.A7

open Subgroup

/-!
# Reduction to index two (AUTA7, even index case)

Let `Q` be a finite group with a normal subgroup `L ≅ A₇` whose centralizer in `Q` is trivial,
and suppose that `Q` has cyclic-or-dihedral Sylow `2`-subgroups.  If `2 ∣ [Q : L]` then there is
a subgroup `Q₀ ≤ Q` containing `L` with `[Q₀ : L] = 2`; for this `Q₀` (and `L₀ = L`) all the
hypotheses of the `A₇`-overgroup problem are again satisfied:

* `L₀ ◁ Q₀` is inherited from `L ◁ Q`;
* `L₀ ≅ L ≅ A₇`;
* `C_{Q₀}(L₀) = 1` because `C_{Q₀}(L) ≤ C_Q(L) = 1`;
* `Q₀` has cyclic-or-dihedral Sylow `2`-subgroups because this property is inherited by
  subgroups of a finite group (`dihOrCycSylow_subgroup`).

The subgroup `Q₀` is produced by Cauchy's theorem: `[Q : L] = |Q/L|` is even, so the quotient
`Q/L` has an element of order two, and the preimage of the subgroup it generates is a subgroup
`Q₀` with `L ≤ Q₀` and `[Q₀ : L] = 2`.

This is the reduction used at the start of the even-index case in the design (`design3` §4);
see also `Submission/Work/AUTA7/A7/EvenIndex.lean` and the note in `Main.lean`.
-/

/-- A finite dihedral group has nonzero parameter: `DihedralGroup 0` is infinite. -/
theorem neZero_of_finite_dihedral {n : ℕ} (h : Finite (DihedralGroup n)) : NeZero n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn] at h
    exact absurd h (not_finite_iff_infinite.mpr (inferInstance : Infinite (DihedralGroup 0)))
  · exact ⟨hn.ne'⟩

/-- **Heredity of `DihOrCycSylow`.** If every Sylow `2`-subgroup of the finite group `G` is cyclic
or dihedral, then the same holds for every subgroup `K ≤ G`.

A Sylow `2`-subgroup `P` of `K`, viewed in `G` via `K.subtype`, is a `2`-subgroup of `G`, hence
lies in a Sylow `2`-subgroup `S` of `G`.  If `S` is cyclic, so is `P`; if `S ≅ DihedralGroup n`,
push `P` through this isomorphism and apply `dihedral_subgroup_isCyclic_or_dihedral`. -/
theorem dihOrCycSylow_subgroup {G : Type} [Group G] [Finite G]
    (h : Work.GW2.DihOrCycSylow G) (K : Subgroup G) : Work.GW2.DihOrCycSylow ↥K := by
  intro P
  -- `P` viewed in `G`, together with the isomorphism `↥P ≃* ↥PG`.
  let PG : Subgroup G := (P : Subgroup ↥K).map K.subtype
  have he : ↥(P : Subgroup ↥K) ≃* ↥PG :=
    Subgroup.equivMapOfInjective (P : Subgroup ↥K) K.subtype K.subtype_injective
  -- `PG` is a `2`-subgroup of `G`, so it lies in a Sylow `2`-subgroup `S` of `G`.
  have hPp : IsPGroup 2 ↥PG := (P.isPGroup').of_equiv he
  obtain ⟨S, hSle⟩ := hPp.exists_le_sylow
  rcases h S with hcyc | ⟨n, ⟨e⟩⟩
  · -- `S` is cyclic, hence so is `PG`, and `P ≃* PG`.
    left
    haveI : IsCyclic ↥(S : Subgroup G) := hcyc
    exact (MulEquiv.isCyclic he).mpr (isCyclic_of_le hSle)
  · -- `S ≅ DihedralGroup n`: push `P` into `DihedralGroup n` and use the subgroups lemma.
    haveI hne : NeZero n := neZero_of_finite_dihedral
      (Finite.of_injective (e.symm : DihedralGroup n → ↥(S : Subgroup G)) e.symm.injective)
    let Q' : Subgroup ↥(S : Subgroup G) := PG.subgroupOf (S : Subgroup G)
    let H' : Subgroup (DihedralGroup n) := Q'.map e.toMonoidHom
    have h1 : ↥Q' ≃* ↥PG := Subgroup.subgroupOfEquivOfLe hSle
    have h2 : ↥Q' ≃* ↥H' :=
      Subgroup.equivMapOfInjective Q' e.toMonoidHom e.injective
    rcases dihedral_subgroup_isCyclic_or_dihedral H' with hcyc' | ⟨m, ⟨em⟩⟩
    · left
      exact (MulEquiv.isCyclic he).mpr
        ((MulEquiv.isCyclic h1).mp ((MulEquiv.isCyclic h2).mpr hcyc'))
    · right
      exact ⟨m, ⟨he.trans (h1.symm.trans (h2.trans em))⟩⟩

/-- **Existence of a subgroup of relative index two.** If `L ◁ Q` with `Q` finite and `2 ∣ [Q : L]`,
then `L` is contained in a subgroup `Q₀` with `[Q₀ : L] = 2`.

Indeed `[Q : L] = |Q/L|` is even, so by Cauchy's theorem the quotient `Q/L` has an element of
order two; the preimage of the subgroup it generates works. -/
theorem exists_subgroup_relIndex_two {Q : Type} [Group Q] [Finite Q] (L : Subgroup Q)
    (hL : L.Normal) (h2 : 2 ∣ L.index) :
    ∃ Q₀ : Subgroup Q, L ≤ Q₀ ∧ L.relIndex Q₀ = 2 := by
  classical
  haveI : Fintype (Q ⧸ L) := Fintype.ofFinite _
  have h2' : 2 ∣ Fintype.card (Q ⧸ L) := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact h2
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 2 h2'
  let M : Subgroup (Q ⧸ L) := Subgroup.zpowers g
  have hMcard : Nat.card ↥M = 2 := by
    show Nat.card ↥(Subgroup.zpowers g) = 2
    rw [Nat.card_zpowers, hg]
  set Q₀ : Subgroup Q := M.comap (QuotientGroup.mk' L) with hQ₀
  have hLQ₀ : L ≤ Q₀ := by
    intro x hx
    rw [hQ₀, Subgroup.mem_comap]
    have h1 : (QuotientGroup.mk' L) x = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hx
    rw [h1]
    exact M.one_mem
  have hidx : Q₀.index = M.index := by
    rw [hQ₀]
    exact Subgroup.index_comap_of_surjective M (QuotientGroup.mk'_surjective L)
  refine ⟨Q₀, hLQ₀, ?_⟩
  have hsplit : L.relIndex Q₀ * Q₀.index = 2 * Q₀.index := by
    calc L.relIndex Q₀ * Q₀.index = L.index := Subgroup.relIndex_mul_index hLQ₀
      _ = Nat.card (Q ⧸ L) := (Subgroup.index_eq_card L).symm
      _ = Nat.card ↥M * M.index := (Subgroup.card_mul_index M).symm
      _ = 2 * Q₀.index := by rw [hMcard, hidx]
  have hQ0pos : 0 < Q₀.index := by
    by_contra h
    have h0 : Q₀.index = 0 := Nat.le_zero.mp (not_lt.mp h)
    have hcard := Subgroup.card_mul_index Q₀
    rw [h0, mul_zero] at hcard
    exact (Nat.card_ne_zero.mpr ⟨⟨1⟩, ‹Finite Q›⟩) hcard.symm
  exact Nat.mul_right_cancel hQ0pos hsplit

/-- **Reduction to index two.**  Under the hypotheses of the `A₇`-overgroup problem
(`L ◁ Q`, `L ≅ A₇`, `C_Q(L) = 1`, cyclic-or-dihedral Sylow `2`-subgroups) and `2 ∣ [Q : L]`,
there is `Q₀ ≤ Q` and `L₀ = L ◁ Q₀` with `[Q₀ : L₀] = 2`, again containing a copy of `A₇` with
trivial centralizer, and `Q₀` again has cyclic-or-dihedral Sylow `2`-subgroups. -/
theorem reduce_to_index_two (Q : Type) [Group Q] [Finite Q] (L : Subgroup Q) (hL : L.Normal)
    (hφ : Nonempty (L ≃* alternatingGroup (Fin 7)))
    (hC : Subgroup.centralizer (L : Set Q) = ⊥)
    (hS : Work.GW2.DihOrCycSylow Q) (h2 : 2 ∣ L.index) :
    ∃ (Q₀ : Subgroup Q) (L₀ : Subgroup ↥Q₀),
      L₀.Normal ∧ L₀.index = 2 ∧
      Nonempty (L₀ ≃* alternatingGroup (Fin 7)) ∧
      Subgroup.centralizer (L₀ : Set ↥Q₀) = ⊥ ∧
      Work.GW2.DihOrCycSylow ↥Q₀ := by
  obtain ⟨Q₀, hLQ₀, hidx⟩ := exists_subgroup_relIndex_two L hL h2
  refine ⟨Q₀, L.subgroupOf Q₀, hL.subgroupOf Q₀, hidx, ⟨?_, ?_, ?_⟩⟩
  · -- `L.subgroupOf Q₀ ≅ L ≅ A₇`
    exact ⟨(Subgroup.subgroupOfEquivOfLe hLQ₀).trans hφ.some⟩
  · -- the centralizer in `Q₀` is trivial
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hx' : ∀ h ∈ (L.subgroupOf Q₀ : Set ↥Q₀), h * x = x * h :=
      Subgroup.mem_centralizer_iff.mp hx
    have hmem : (x : Q) ∈ Subgroup.centralizer (L : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy₀ : (⟨y, hLQ₀ hy⟩ : ↥Q₀) ∈ (L.subgroupOf Q₀ : Set ↥Q₀) := by
        simpa [Subgroup.mem_subgroupOf] using hy
      exact congrArg Subtype.val (hx' ⟨y, hLQ₀ hy⟩ hy₀)
    have h1 : (x : Q) = 1 := by
      have := hmem
      rw [hC] at this
      exact Subgroup.mem_bot.mp this
    exact Subtype.ext h1
  · -- `DihOrCycSylow` is inherited by the subgroup `Q₀`
    exact dihOrCycSylow_subgroup hS Q₀

end Work.AUTA7.A7
