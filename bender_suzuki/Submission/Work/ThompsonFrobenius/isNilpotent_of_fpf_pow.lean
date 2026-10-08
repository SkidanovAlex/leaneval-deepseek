import Mathlib
import Submission.Work.ThompsonFrobenius.GTDefs
import Submission.Work.ThompsonFrobenius.glauberman_thompson
import Submission.Work.ThompsonFrobenius.hasNormalPComplement_of_isNilpotent
import Submission.Work.ThompsonFrobenius.isInv_of_isNormalPComplement
import Submission.Work.ThompsonFrobenius.isSolvable_of_nilpotent_normal
import Submission.Work.ThompsonFrobenius.restrictEquiv_pow_eq_one
import Submission.Work.ThompsonFrobenius.ZJ_map_mulAut
import Submission.Work.ThompsonFrobenius.ZJ_ne_bot
import Submission.Work.ThompsonFrobenius.induced_isFpf
import Submission.Work.Frobenius.Fpf.isNilpotent_of_fpf_prime
import Submission.Work.Frobenius.Fpf.exists_invariant_sylow
import Submission.Work.Frobenius.Fpf.Basic
import Submission.Work.GlaubermanZJ.isAbelianSubgroup_ZJ
import Submission.Work.HallHigman.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# M4: Thompson's theorem by strong induction (area `ThompsonFrobenius`)

Let `α` be a fixed-point-free automorphism of a finite group `K` with `α ^ q = 1` for a prime `q`.
We show `K` nilpotent by strong induction on `|K|`.

* If some `α`-invariant normal `1 < N < K` exists, then `N` and `K ⧸ N` are nilpotent by induction
  (using M1 `restrictEquiv_pow_eq_one` + `isFpf_restrict`, resp. `induced_isFpf`), so `K` is
  solvable (M3) and the delivered `isNilpotent_of_fpf_prime` applies.
* Otherwise every `α`-invariant normal subgroup is `⊥` or `⊤` ("`α`-simple").  If `|K|` has an odd
  prime divisor `p`, take an `α`-invariant Sylow `p`-subgroup `P` (`exists_invariant_sylow`); then
  `Z = Z(J(P))` is `α`-invariant (`ZJ_map_mulAut`) and nontrivial, and so is `N_K(Z)`.
  * If `N_K(Z) = K`, then `Z ⊴ K`, hence `Z = K` by `α`-simplicity, and `K = Z(J(P))` is abelian.
  * If `N_K(Z) < K`, it is nilpotent by induction, hence `p`-nilpotent
    (`hasNormalPComplement_of_isNilpotent`); Theorem D (`glauberman_thompson`) makes `K`
    `p`-nilpotent.  Its normal `p`-complement `M` is `α`-invariant (M2), hence `⊥` or `⊤`; `M = ⊥`
    makes `K` a `p`-group (nilpotent), while `M = ⊤` contradicts `p ∣ |K|`.
* If `|K|` has no odd prime divisor, `K` is a `2`-group, hence nilpotent.
-/

set_option autoImplicit false

open scoped Pointwise

namespace Work.ThompsonFrobenius

open Work.NPC.Fpf

theorem isNilpotent_of_fpf_pow (hZJ : Submission.Blueprint.GlaubermanZJProp) :
    ∀ (n : ℕ) (K : Type) [Group K] [Finite K], Nat.card K = n →
      ∀ (α : MulAut K) (q : ℕ), q.Prime → α ^ q = 1 → IsFpf α → Group.IsNilpotent K := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K _ _ hKn α q hq hαq hfpf
    by_cases hex : ∃ N : Subgroup K, N.Normal ∧ IsInv α N ∧ N ≠ ⊥ ∧ N ≠ ⊤
    · -- a proper nontrivial `α`-invariant normal subgroup: `K` is solvable, then nilpotent
      obtain ⟨N, hNn, hNi, hNne, hNtop⟩ := hex
      haveI hNnormal : N.Normal := hNn
      have hNcard : Nat.card ↥N < n := by
        have h := Subgroup.card_lt_of_lt (H := N) (K := ⊤) (lt_top_iff_ne_top.mpr hNtop)
        rw [Subgroup.card_top] at h
        exact hKn ▸ h
      have hNnil : Group.IsNilpotent ↥N :=
        ih (Nat.card ↥N) hNcard ↥N rfl hNi.restrictEquiv q hq
          (restrictEquiv_pow_eq_one hNi hαq) (Work.Frobenius.Fpf.isFpf_restrict hNi hfpf)
      obtain ⟨hRord, hRfpf⟩ := induced_isFpf hq hαq hfpf hNi hNtop
      have hQcard : Nat.card (K ⧸ N) < n := by
        have hmul : Nat.card (K ⧸ N) * Nat.card ↥N = Nat.card K := by
          rw [← Subgroup.index_eq_card]
          exact Subgroup.index_mul_card N
        have h1 : 1 < Nat.card ↥N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hNne
        have h2 : 0 < Nat.card (K ⧸ N) := Nat.card_pos
        have h3 : Nat.card (K ⧸ N) < Nat.card K :=
          calc Nat.card (K ⧸ N) < Nat.card (K ⧸ N) * Nat.card ↥N :=
                lt_mul_of_one_lt_right h2 h1
            _ = Nat.card K := hmul
        exact hKn ▸ h3
      have hQnil : Group.IsNilpotent (K ⧸ N) :=
        ih (Nat.card (K ⧸ N)) hQcard (K ⧸ N) rfl
          (QuotientGroup.congr N N α (by simpa using hNi.map_eq)) q hq
          (by rw [← hRord]; exact pow_orderOf_eq_one _) hRfpf
      haveI : Group.IsSolvable K := isSolvable_of_nilpotent_normal N hNnil hQnil
      exact Work.Frobenius.Fpf.isNilpotent_of_fpf_prime hq hαq hfpf
    · -- `α`-simple case
      have hsimple : ∀ N : Subgroup K, N.Normal → IsInv α N → N ≠ ⊥ → N = ⊤ := by
        intro N hNn hNi hNne
        by_contra hNtop
        exact hex ⟨N, hNn, hNi, hNne, hNtop⟩
      by_cases hpodd : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card K
      · obtain ⟨p, hpp, hp2, hpdvd⟩ := hpodd
        haveI : Fact p.Prime := ⟨hpp⟩
        obtain ⟨P, hPinv⟩ := Work.Frobenius.Fpf.exists_invariant_sylow hfpf p
        have hPne : (P : Subgroup K) ≠ ⊥ := by
          intro hbot
          have hdiv : p ∣ Nat.card ↥(P : Subgroup K) := by
            rcases hpp.dvd_mul.mp (by
              rw [Subgroup.card_mul_index (P : Subgroup K)]
              exact hpdvd) with h | h
            · exact h
            · exact absurd h P.not_dvd_index
          rw [hbot, Subgroup.card_bot] at hdiv
          exact hpp.not_dvd_one hdiv
        let Z : Subgroup K := Submission.Blueprint.ZJ (P : Subgroup K)
        have hZne : Z ≠ ⊥ := ZJ_ne_bot P.isPGroup' hPne
        have hZmap : Z.map α.toMonoidHom = Z := by
          show (Submission.Blueprint.ZJ (P : Subgroup K)).map α.toMonoidHom
            = Submission.Blueprint.ZJ (P : Subgroup K)
          rw [ZJ_map_mulAut α (P : Subgroup K), hPinv.map_eq]
        have hZinv : IsInv α Z := Work.Frobenius.Fpf.isInv_of_map_eq hZmap
        let NZ : Subgroup K := Subgroup.normalizer (Z : Set K)
        have hNZmap : NZ.map α.toMonoidHom = NZ := by
          show (Subgroup.normalizer (Z : Set K)).map α.toMonoidHom
            = Subgroup.normalizer (Z : Set K)
          rw [Subgroup.map_equiv_normalizer_eq Z α, hZmap]
        have hNZinv : IsInv α NZ := Work.Frobenius.Fpf.isInv_of_map_eq hNZmap
        by_cases hNZtop : NZ = ⊤
        · -- `Z ⊴ K`: `Z = K` is abelian
          have hZnormal : Z.Normal := Subgroup.normalizer_eq_top_iff.mp hNZtop
          have hZtop : Z = ⊤ := hsimple Z hZnormal hZinv hZne
          haveI : IsMulCommutative K := isMulCommutative_iff.mpr fun x y =>
            Work.GlaubermanZJ.isAbelianSubgroup_ZJ (P : Subgroup K) x
              (by show x ∈ Z; rw [hZtop]; exact Subgroup.mem_top x)
              y (by show y ∈ Z; rw [hZtop]; exact Subgroup.mem_top y)
          infer_instance
        · -- `N_K(Z)` is a proper `α`-invariant subgroup: nilpotent, hence `p`-nilpotent
          have hNZcard : Nat.card ↥NZ < n := by
            have h := Subgroup.card_lt_of_lt (H := NZ) (K := ⊤) (lt_top_iff_ne_top.mpr hNZtop)
            rw [Subgroup.card_top] at h
            exact hKn ▸ h
          have hNZnil : Group.IsNilpotent ↥NZ :=
            ih (Nat.card ↥NZ) hNZcard ↥NZ rfl hNZinv.restrictEquiv q hq
              (restrictEquiv_pow_eq_one hNZinv hαq)
              (Work.Frobenius.Fpf.isFpf_restrict hNZinv hfpf)
          haveI : Group.IsNilpotent ↥NZ := hNZnil
          have hKnp : Work.NPC.HasNormalPComplement p K :=
            glauberman_thompson hZJ hpp hp2 K P
              (hasNormalPComplement_of_isNilpotent (G := ↥NZ) hpp)
          obtain ⟨M, hM⟩ := hKnp
          haveI hMnormal : M.Normal := hM.normal
          have hMinv : IsInv α M := isInv_of_isNormalPComplement hpp α hM
          by_cases hMbot : M = ⊥
          · have hKpg : IsPGroup p K := by
              rw [hMbot] at hM
              exact IsPGroup.of_equiv hM.isPGroup_quotient (QuotientGroup.quotientBot)
            exact hKpg.isNilpotent
          · have hMtop : M = ⊤ := hsimple M hMnormal hMinv hMbot
            have h1 : p ∣ Nat.card ↥M := by
              rw [hMtop, Subgroup.card_top]
              exact hpdvd
            exact False.elim (absurd h1 (hpp.coprime_iff_not_dvd.mp hM.coprime_card.symm))
      · -- no odd prime divisor: `K` is a `2`-group
        have h2 : Nat.card K = 2 ^ (Nat.card K).primeFactorsList.length :=
          Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
            (fun {d} hd hdd => by
              by_contra hd2
              exact hpodd ⟨d, hd, hd2, hdd⟩)
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact (IsPGroup.of_card h2).isNilpotent

end Work.ThompsonFrobenius
