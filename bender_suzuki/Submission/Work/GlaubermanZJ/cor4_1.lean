import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.GlaubermanZJ.isAbelianSubgroup_iff
import Submission.Work.GlaubermanZJ.lemma3_5_a
import Submission.Work.GlaubermanZJ.cor3_1
import Submission.Work.GlaubermanZJ.theorem4_1
import Submission.Work.GlaubermanZJ.Thm41.IterComm
import Submission.Work.GlaubermanZJ.Thm41.PComm
import Submission.Work.GlaubermanZJ.Thm41.Symmetry
import Submission.Work.PGroup.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement
open Subgroup

noncomputable section

namespace Work.GlaubermanZJ

variable {G : Type*} [Group G]

/-! ## 0. Elementary iterated-commutator facts -/

/-- `[B,A;k] ≤ γ_k(S)` whenever `B ≤ S` and `A ≤ S` (Mathlib's `S.lowerCentralSeries k` starts
at `S.lowerCentralSeries 0 = S`). -/
theorem iterComm_le_lowerCentralSeries_of_le (S A B : Subgroup G) (hB : B ≤ S) (hA : A ≤ S)
    (k : ℕ) : iterComm B A k ≤ S.lowerCentralSeries k := by
  induction k with
  | zero => simpa using hB
  | succ k ih =>
      rw [iterComm_succ, Subgroup.lowerCentralSeries_succ]
      exact Subgroup.commutator_mono ih hA

/-- `A` normalizes every iterated commutator `[B,A;k]` (provided `A ≤ N_G(B)`).  Indeed
`a [B,A;k] a⁻¹ = [aBa⁻¹, aAa⁻¹;k] = [B,A;k]` for `a ∈ A`. -/
theorem iterComm_conj_mem_normalizer (A B : Subgroup G) (hAB : A ≤ Subgroup.normalizer (B : Set G))
    {a : G} (ha : a ∈ A) (k : ℕ) : a ∈ Subgroup.normalizer (iterComm B A k : Set G) := by
  have hB' : B.map (MulAut.conj a : G →* G) = B :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAB ha)
  have hA' : A.map (MulAut.conj a : G →* G) = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ha)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmap : ∀ k, (iterComm B A k).map (MulAut.conj a : G →* G)
      = iterComm (B.map (MulAut.conj a : G →* G)) (A.map (MulAut.conj a : G →* G)) k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [iterComm_succ, iterComm_succ, Subgroup.map_commutator, ih]
  exact (hmap k).trans (by rw [hB', hA'])

/-- Glauberman 1968, (4.1) in the proof of Theorem 4.1 (p. 1111): if `A ∈ 𝒜(S)`, `B ≤ S` is a
subgroup with `[B,B] ≤ Z(J(S))`, then `A ∩ B` centralizes `[B,A]`.

Indeed `[B, A ⊓ B] ≤ [B,B] ≤ Z(J(S)) ≤ A` (Lemma 3.5 (a)), whence `[B, A⊓B] ≤ A` kills
`[B, A⊓B, A]`; and `[A⊓B, A] ≤ [A,A] = 1` kills `[A⊓B, A, B]`.  The Three Subgroups Lemma
gives `[A, B, A⊓B] = 1`. -/
theorem commutator_iterComm_one_of_maxAbelian (S A B : Subgroup G) [Finite S]
    (hA : IsMaxAbelianSubgroup S A) (hB : B ≤ S)
    (hcenter : ⁅B, B⁆ ≤ Submission.Blueprint.ZJ S) :
    ⁅⁅B, A⁆, A ⊓ B⁆ = ⊥ := by
  have hAab : IsMulCommutative ↥A := isAbelianSubgroup_iff.mp hA.2.1
  have hAA : ⁅A, A⁆ = ⊥ := Subgroup.commutator_self_eq_bot_iff.mpr hAab
  have hZJA : Submission.Blueprint.ZJ S ≤ A := (lemma3_5_a S A A hA le_rfl hA.1).1
  have hBB_A : ⁅B, B⁆ ≤ A := le_trans hcenter hZJA
  have h1 : ⁅⁅B, A ⊓ B⁆, A⁆ = ⊥ := by
    have hle : ⁅B, A ⊓ B⁆ ≤ A :=
      (Subgroup.commutator_mono (le_refl B) (inf_le_right : A ⊓ B ≤ B)).trans hBB_A
    have h3 : ⁅⁅B, A ⊓ B⁆, A⁆ ≤ ⁅A, A⁆ := Subgroup.commutator_mono hle le_rfl
    rw [hAA] at h3
    exact le_bot_iff.mp h3
  have h2 : ⁅⁅A ⊓ B, A⁆, B⁆ = ⊥ := by
    have h3 : ⁅A ⊓ B, A⁆ = ⊥ := by
      have h4 : ⁅A ⊓ B, A⁆ ≤ ⁅A, A⁆ := Subgroup.commutator_mono inf_le_left le_rfl
      rw [hAA] at h4
      exact le_bot_iff.mp h4
    rw [h3, Subgroup.commutator_bot_left]
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := A) (H₂ := B) (H₃ := A ⊓ B)
    h1 h2
  rwa [Subgroup.commutator_comm A B] at h3

/-- If `C` centralizes `M`, `C ≤ A` and `A` is commutative, then `[M ⊔ C, A] ≤ [M, A]`.
(For `c ∈ C` and `m ∈ M` one has `[m*c, a] = [m,a]`, because `c` centralizes `M` and commutes
with `A`; general elements of `M ⊔ C` are handled by closure induction, using that both
`M ⊔ C` and `A` normalize `[M,A]`.) -/
theorem commutator_sup_le_commutator (M C A : Subgroup G)
    (hCM : C ≤ Subgroup.centralizer (M : Set G)) (hCA : C ≤ A)
    (hAab : IsMulCommutative A) :
    ⁅M ⊔ C, A⁆ ≤ ⁅M, A⁆ := by
  let L : Subgroup G := ⁅M, A⁆
  have hAC : A ≤ Subgroup.centralizer (C : Set G) :=
    le_trans (Subgroup.le_centralizer_iff_isMulCommutative.mpr hAab)
      (Subgroup.centralizer_le fun x hx => hCA hx)
  -- `C` centralizes `M ⊔ A`
  have hCent : C ≤ Subgroup.centralizer ((M ⊔ A : Subgroup G) : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hMA : M ⊔ A ≤ Subgroup.centralizer ({c} : Set G) := by
      refine sup_le ?_ ?_
      · intro m hm
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact (Subgroup.mem_centralizer_iff.mp (hCM hc) m hm).symm
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact Subgroup.mem_centralizer_iff.mp (hAC ha) c hc
    exact (Subgroup.mem_centralizer_iff.mp (hMA hu) c (Set.mem_singleton c)).symm
  -- `M ⊔ C ≤ N([M,A])`
  have hN : Subgroup.closure (↑M ∪ ↑C : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    rw [← Subgroup.sup_eq_closure]
    refine sup_le (Subgroup.normalizer_commutator_ge_left M A) ?_
    intro c hc
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (Subgroup.commutator_le_sup M A) (hCent hc))
  have key : ∀ u ∈ Subgroup.closure (↑M ∪ ↑C : Set G), ∀ a ∈ A, ⁅u, a⁆ ∈ L := by
    intro u hu
    refine Subgroup.closure_induction (k := (↑M ∪ ↑C : Set G))
      (p := fun u _ => ∀ a ∈ A, ⁅u, a⁆ ∈ L) ?_ ?_ ?_ ?_ hu
    · intro u hu'
      rcases hu' with hu' | hu'
      · intro a ha
        exact Subgroup.commutator_mem_commutator hu' ha
      · intro a ha
        have hcomm : u * a = a * u :=
          congrArg Subtype.val (isMulCommutative_iff.mp hAab ⟨u, hCA hu'⟩ ⟨a, ha⟩)
        rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
        exact L.one_mem
    · intro a ha
      rw [commutatorElement_one_left]
      exact L.one_mem
    · intro x y hx hy hx' hy' a ha
      have hconj : x * ⁅y, a⁆ * x⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hN hx) ⁅y, a⁆).mp (hy' a ha)
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact L.mul_mem hconj (hx' a ha)
    · intro x hx hx' a ha
      have hxa : ⁅x, a⁆ ∈ L := hx' a ha
      rw [commutatorElement_inv_left, ← commutatorElement_inv (g₁ := x) (g₂ := a)]
      have hmem := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (L : Set G)).inv_mem (hN hx)) ⁅x, a⁆⁻¹).mp (L.inv_mem hxa)
      simpa using hmem
  rw [Subgroup.commutator_le]
  intro u hu a ha
  rw [Subgroup.sup_eq_closure] at hu
  exact key u hu a ha

/-- The "replacement step" in Glauberman's Theorem 4.1: given `A ∈ 𝒜(S)` and `x ∈ B` such that
`M = [x,A]` is commutative, contained in `B`, centralized-on-`A ⊓ B`, not contained in `A`, and
killed by a further commutator with `A` (`[M,A,A] = 1`), the subgroup `M·C_A(M)` is again in
`𝒜(S)`, contains `A ⊓ B` and meets `B` strictly more than `A` does. -/
theorem exists_maxAbelian_of_commClosure {G : Type*} [Group G] {S A B : Subgroup G} [Finite S]
    (hA : IsMaxAbelianSubgroup S A) (hB : B ≤ S) {x : G}
    (hMle : Work.PGroup.commClosure x A ≤ B)
    (hMab : IsMulCommutative (Work.PGroup.commClosure x A))
    (hcent : A ⊓ B ≤ Subgroup.centralizer ((Work.PGroup.commClosure x A : Subgroup G) : Set G))
    (hnotle : ¬ Work.PGroup.commClosure x A ≤ A)
    (hMAA : ⁅⁅Work.PGroup.commClosure x A, A⁆, A⁆ = ⊥) :
    ∃ A' : Subgroup G, IsMaxAbelianSubgroup S A' ∧ A ⊓ B < A' ⊓ B ∧ ⁅⁅A', A⁆, A⁆ = ⊥ := by
  obtain ⟨hAS, hAab, hAmax⟩ := hA
  have hAcom : IsMulCommutative ↥A := isAbelianSubgroup_iff.mp hAab
  have hAcard : Nat.card ↥A = Work.PGroup.maxAbelianOrder S :=
    (isMaxAbelianSubgroup_iff S A).mp ⟨hAS, hAab, hAmax⟩ |>.2.2
  let M : Subgroup G := Work.PGroup.commClosure x A
  let C : Subgroup G := A ⊓ Subgroup.centralizer (M : Set G)
  have hMleS : M ≤ S := le_trans hMle hB
  obtain ⟨hab, hcard⟩ :=
    Work.PGroup.thompson_product_centralizer (P := S) hAS hAcom hAcard (hMle.trans hB) hMab
  have hcentM : A ⊓ B ≤ Subgroup.centralizer (M : Set G) := hcent
  have hmax' : IsMaxAbelianSubgroup S (M ⊔ C) :=
    (isMaxAbelianSubgroup_iff S (M ⊔ C)).mpr
      ⟨sup_le hMleS (le_trans inf_le_left hAS), isAbelianSubgroup_iff.mpr hab, hcard⟩
  refine ⟨M ⊔ C, hmax', ?_, ?_⟩
  · refine lt_of_le_of_ne ?_ ?_
    · refine le_inf ?_ inf_le_right
      exact (le_inf inf_le_left hcentM).trans le_sup_right
    · intro hEq
      have hMleA : M ≤ A := by
        have h1 : M ≤ (M ⊔ C) ⊓ B := le_inf le_sup_left hMle
        rw [← hEq] at h1
        exact le_trans h1 inf_le_left
      exact hnotle hMleA
  · have hMAA' : ⁅⁅M, A⁆, A⁆ = ⊥ := hMAA
    have h1 : ⁅M ⊔ C, A⁆ ≤ ⁅M, A⁆ :=
      commutator_sup_le_commutator M C A inf_le_right inf_le_left hAcom
    have h2 : ⁅⁅M ⊔ C, A⁆, A⁆ ≤ ⁅⁅M, A⁆, A⁆ := Subgroup.commutator_mono h1 le_rfl
    rw [hMAA'] at h2
    exact le_bot_iff.mp h2

-- Glauberman 1968, Corollary 4.1 (p. 1113): S a finite p-group, `B ⊴ S` with
-- `[B,B] ⊆ Z(B) ∩ Z(J(S))`.  Then `∃ A ∈ 𝒜(S)` with `[B,A;3] = 1`, and if `p` is odd,
-- `∃ A ∈ 𝒜(S)` with `[B,A,A] = 1`.
/-- **Glauberman 1968, Corollary 4.1** (p. 1113): `S` a finite `p`-group, `B ⊴ S` of class at
most two with `[B,B] ⊆ Z(B) ∩ Z(J(S))`.  Then there is `A ∈ 𝒜(S)` with `[B,A;3] = 1`, and if
`p` is odd, there is `A ∈ 𝒜(S)` with `[B,A,A] = 1`.

The proof is the maximality argument of the source: choose `A ∈ 𝒜(S)` maximizing `|A ∩ B|`
(this exists since `𝒜(S) ≠ ∅` and `|A ∩ B| ≤ |B|`).  If `[B,A;3] ≠ 1`, or `[B,A,A] ≠ 1`,
Glauberman's replacement theorem `theorem4_1` produces `A' ∈ 𝒜(S)` with `A ⊓ B < A' ⊓ B`,
contradicting maximality.  Note that `p` odd is a hypothesis of the statement, so in both cases
`theorem4_1`'s disjunction is available. -/
theorem cor4_1 {G : Type*} [Group G] (p : ℕ) (hp : p.Prime) (hpne : p ≠ 2) (S B : Subgroup G)
    [Finite S] (hS : IsPGroup p S) (hB : B ≤ S) (hBn : S ≤ Subgroup.normalizer (B : Set G))
    (hBp : IsPGroup p B) (hclass : ⁅B, B⁆ ≤ Work.PGroup.centerIn B)
    (hcenter : ⁅B, B⁆ ≤ Submission.Blueprint.ZJ S) :
    (∃ A : Subgroup G, Work.GlaubermanZJ.IsMaxAbelianSubgroup S A ∧
        ⁅⁅⁅B, A⁆, A⁆, A⁆ = ⊥) ∧
      ∃ A : Subgroup G, Work.GlaubermanZJ.IsMaxAbelianSubgroup S A ∧ ⁅⁅B, A⁆, A⁆ = ⊥ := by
  -- `𝒜(S)` is nonempty
  have hex : ∃ A : Subgroup G, IsMaxAbelianSubgroup S A := by
    obtain ⟨A, hAS, hAcom, hAcard⟩ := Work.PGroup.maxAbelianOrder_attained S
    exact ⟨A, (isMaxAbelianSubgroup_iff S A).mpr
      ⟨hAS, isAbelianSubgroup_iff.mpr hAcom, hAcard⟩⟩
  haveI hfinB : Finite ↥B :=
    Finite.of_injective (Subgroup.inclusion hB) (Subgroup.inclusion_injective hB)
  -- choose `A ∈ 𝒜(S)` maximizing `|A ⊓ B|`
  have hmaxexists : ∃ A : Subgroup G, IsMaxAbelianSubgroup S A ∧
      ∀ A' : Subgroup G, IsMaxAbelianSubgroup S A' →
        Nat.card ↥(A' ⊓ B) ≤ Nat.card ↥(A ⊓ B) := by
    set K : Set ℕ := {m | ∃ A : Subgroup G, IsMaxAbelianSubgroup S A ∧ Nat.card ↥(A ⊓ B) = m}
    have hne : K.Nonempty := by
      obtain ⟨A, hA⟩ := hex
      exact ⟨_, A, hA, rfl⟩
    have hbdd : BddAbove K := ⟨Nat.card ↥B, by
      rintro m ⟨A, hA, rfl⟩
      exact Subgroup.card_le_of_le inf_le_right⟩
    obtain ⟨A, hA, hcard⟩ := Nat.sSup_mem hne hbdd
    exact ⟨A, hA, fun A' hA' => by
      have hmem : Nat.card ↥(A' ⊓ B) ∈ K := ⟨A', hA', rfl⟩
      rw [hcard]
      exact le_csSup hbdd hmem⟩
  obtain ⟨A, hA, hAmax⟩ := hmaxexists
  -- a strict increase of `A ⊓ B` is impossible, by Theorem 4.1
  have key : ∀ A' : Subgroup G, IsMaxAbelianSubgroup S A' → ¬ (A ⊓ B < A' ⊓ B) := by
    intro A' hA' hlt
    haveI hfin1 : Finite ↥(A ⊓ B) :=
      Finite.of_injective (Subgroup.inclusion (inf_le_left.trans hA.1))
        (Subgroup.inclusion_injective _)
    haveI hfin2 : Finite ↥(A' ⊓ B) :=
      Finite.of_injective (Subgroup.inclusion (inf_le_left.trans hA'.1))
        (Subgroup.inclusion_injective _)
    have hle : Nat.card ↥(A ⊓ B) ≤ Nat.card ↥(A' ⊓ B) := Subgroup.card_le_of_le hlt.le
    have hne' : Nat.card ↥(A ⊓ B) ≠ Nat.card ↥(A' ⊓ B) := fun heq =>
      hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le heq.symm.le)
    have hlt' : Nat.card ↥(A ⊓ B) < Nat.card ↥(A' ⊓ B) := lt_of_le_of_ne hle hne'
    have := hAmax A' hA'
    omega
  refine ⟨⟨A, hA, ?_⟩, ⟨A, hA, ?_⟩⟩
  · by_contra hc
    obtain ⟨A', hA', hlt, -⟩ :=
      theorem4_1 p hp hpne S A B hS hA hB hBn hBp hclass hcenter (Or.inl hc)
    exact key A' hA' hlt
  · by_contra hc
    obtain ⟨A', hA', hlt, -⟩ :=
      theorem4_1 p hp hpne S A B hS hA hB hBn hBp hclass hcenter (Or.inr hc)
    exact key A' hA' hlt

end Work.GlaubermanZJ
