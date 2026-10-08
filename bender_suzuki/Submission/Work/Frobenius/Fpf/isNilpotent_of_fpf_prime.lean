import Mathlib
import Submission.Work.Frobenius.Fpf.Basic
import Submission.Work.Frobenius.Fpf.SylowNormal
import Submission.Work.Frobenius.Fpf.isFpf_quotientCongr
import Submission.Work.Frobenius.Fpf.quotientCongr_pow_apply
import Submission.Work.Frobenius.Fpf.exists_invariant_sylow
import Submission.Work.Frobenius.Fpf.le_centralizer_of_fpf
import Submission.Work.Frobenius.Fpf.exists_characteristic_abelian_pGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# F9: a finite solvable group with a fixed-point-free automorphism of prime order is nilpotent

This is the main theorem of area A8b (see `Submission/Work/NOTES_LEAD_ft_npc.md` §2.3): if the
finite **solvable** group `K` carries a fixed-point-free automorphism `α` (in the sense of
`Work.NPC.Fpf.IsFpf`: the only fixed point of `α` is `1`) with `α ^ q = 1` for a prime `q`, then
`K` is nilpotent.

The proof is a strong induction on `Nat.card K` (`fpf_prime_step` below is the induction step).

1. If `K` is trivial there is nothing to prove.  Otherwise let `N` be a nontrivial characteristic
   abelian `p`-subgroup of `K` (`exists_characteristic_abelian_pGroup`) and `ᾱ` the automorphism
   induced by `α` on `K ⧸ N`.  It is again fixed-point-free (`isFpf_quotientCongr`) and of order
   `q` (`quotientCongr_pow_apply`), and `K ⧸ N` has smaller order, so by induction it is nilpotent.
2. For every prime `r`, pick an `α`-invariant Sylow `r`-subgroup `R` (`exists_invariant_sylow`).
   Its image in the nilpotent quotient `K ⧸ N` is a normal Sylow subgroup, so `R ⊔ N ⊴ K`
   (`normal_sup_of_map_normal`).
3. If `r = p` then `N ≤ R` (a normal `p`-subgroup lies in every Sylow `p`-subgroup) and `R` is
   normal.  If `r ≠ p`, then `R` and `N` have coprime orders, so `R` centralizes `N`
   (`le_centralizer_of_fpf`), which together with `R ⊔ N ⊴ K` forces `R ⊴ K`.
4. Every Sylow subgroup of `K` is conjugate to one of these normal Sylow subgroups, hence normal;
   a finite group all of whose Sylow subgroups are normal is nilpotent
   (`Group.isNilpotent_of_finite_tfae`).
-/

universe u

namespace Work.Frobenius.Fpf

open Work.NPC.Fpf
open MulAction

variable {K : Type*}

/-- If `R` centralizes `N`, then `R` is normal in the subgroup `R ⊔ N` that it generates with `N`. -/
private theorem subgroupOf_sup_normal_of_le_centralizer [Group K] {N R : Subgroup K}
    (hcent : R ≤ Subgroup.centralizer (N : Set K)) : (R.subgroupOf (R ⊔ N)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
  refine sup_le Subgroup.le_normalizer ?_
  exact (Subgroup.le_centralizer_iff.mp hcent).trans
    (Subgroup.centralizer_le_normalizer (R : Set K))

/-- A Sylow `r`-subgroup `R` that centralizes `N`, with `R ⊔ N` normal in `K`, is normal in `K`. -/
private theorem normal_of_sylow_of_sup_normal_of_le_centralizer [Group K] [Finite K]
    {r : ℕ} [Fact r.Prime] {N : Subgroup K} (R : Sylow r K)
    (hcent : (R : Subgroup K) ≤ Subgroup.centralizer (N : Set K))
    (hsup : ((R : Subgroup K) ⊔ N).Normal) : (R : Subgroup K).Normal :=
  normal_of_sylow_of_normal_subgroupOf R hsup le_sup_left
    (subgroupOf_sup_normal_of_le_centralizer hcent)

/-- The automorphism of `K ⧸ N` induced by an `N`-invariant `α` of order `q` again has order `q`. -/
private theorem quotientCongr_pow_eq_one {K : Type*} [Group K] {N : Subgroup K} [N.Normal]
    {α : MulAut K} (hN : IsInv α N) {q : ℕ} (hαq : α ^ q = 1) :
    (QuotientGroup.congr N N α (by simpa using hN.map_eq)) ^ q = 1 := by
  ext y
  refine QuotientGroup.induction_on y ?_
  intro x
  rw [← QuotientGroup.mk'_apply N x]
  rw [quotientCongr_pow_apply hN q x, hαq]
  simp

/-- The induction step of `isNilpotent_of_fpf_prime`. -/
private theorem fpf_prime_step (n : ℕ) (K : Type u) [Group K] [Finite K] [Group.IsSolvable K]
    (hcard : Nat.card K = n)
    (ih : ∀ m < n, ∀ (L : Type u) [Group L] [Finite L] [Group.IsSolvable L],
      Nat.card L = m → ∀ (α : MulAut L) (q : ℕ), q.Prime → α ^ q = 1 →
        IsFpf α → Group.IsNilpotent L)
    (α : MulAut K) (q : ℕ) (hq : q.Prime) (hαq : α ^ q = 1) (hα : IsFpf α) :
    Group.IsNilpotent K := by
  classical
  by_cases htriv : Subsingleton K
  · exact Group.isNilpotent_of_subsingleton
  haveI : Nontrivial K := not_subsingleton_iff_nontrivial.mp htriv
  -- A nontrivial characteristic abelian `p`-subgroup `N`.
  obtain ⟨p, N, hp, hNchar, hNne, hNab, hNp⟩ := exists_characteristic_abelian_pGroup (K := K)
  haveI : N.Normal := inferInstance
  have hNnormal : N.Normal := inferInstance
  have hNinv : IsInv α N := isInv_of_characteristic hNchar
  -- The automorphism induced by `α` on `K ⧸ N`.
  let β : MulAut (K ⧸ N) := QuotientGroup.congr N N α (by simpa using hNinv.map_eq)
  have hβfpf : IsFpf β := isFpf_quotientCongr hα hNinv
  have hβq : β ^ q = 1 := quotientCongr_pow_eq_one hNinv hαq
  haveI : Finite (K ⧸ N) := Quotient.finite _
  -- `K ⧸ N` is smaller and solvable, so nilpotent by induction.
  have hcard_lt : Nat.card (K ⧸ N) < n := by
    rw [← hcard]
    have hmul : Nat.card K = Nat.card (K ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hN2 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hNne
    have hpos : 1 ≤ Nat.card (K ⧸ N) := by
      rw [Nat.one_le_iff_ne_zero, Nat.card_ne_zero]
      exact ⟨⟨QuotientGroup.mk' N 1⟩, inferInstance⟩
    nlinarith [hmul, hN2, hpos]
  haveI : Group.IsSolvable (K ⧸ N) := inferInstance
  have hnilquot : Group.IsNilpotent (K ⧸ N) :=
    ih (Nat.card (K ⧸ N)) hcard_lt (K ⧸ N) rfl β q hq hβq hβfpf
  -- An `α`-invariant Sylow `r`-subgroup is normal, for every prime `r`.
  have hkey : ∀ (r : ℕ) [Fact r.Prime],
      ∃ R : Sylow r K, IsInv α (R : Subgroup K) ∧ (R : Subgroup K).Normal := by
    intro r hr
    haveI := hr
    obtain ⟨R, hRinv⟩ := exists_invariant_sylow hα r
    haveI : Group.IsNilpotent (K ⧸ N) := hnilquot
    have hRbarn : ((Sylow.mapSurjective (QuotientGroup.mk'_surjective N) R :
        Sylow r (K ⧸ N)) : Subgroup (K ⧸ N)).Normal := inferInstance
    have hsup : ((R : Subgroup K) ⊔ N).Normal := normal_sup_of_map_normal R hRbarn
    by_cases hrp : r = p
    · subst hrp
      have hNR : N ≤ (R : Subgroup K) := IsPGroup.le_sylow_of_normal hNp R
      have hsup' : (R : Subgroup K) ⊔ N = (R : Subgroup K) := sup_eq_left.mpr hNR
      exact ⟨R, hRinv, hsup' ▸ hsup⟩
    · have hcop : (Nat.card R).Coprime (Nat.card N) :=
        coprime_card_of_isPGroup_of_ne hp hr.out (fun h => hrp h.symm) hNp R.isPGroup'
      have hαq' : ∀ x : K, (α ^ q) x = x := fun x => by rw [hαq]; rfl
      have hpow : ∀ i : ℕ, 0 < i → i < q → IsFpf (α ^ i) :=
        fun i hi0 hiq => isFpf_pow hq hαq hα hi0 hiq
      have hcent : (R : Subgroup K) ≤ Subgroup.centralizer (N : Set K) :=
        le_centralizer_of_fpf hq.one_lt hαq' hpow hNnormal hNab hNinv hRinv hcop
      exact ⟨R, hRinv, normal_of_sylow_of_sup_normal_of_le_centralizer R hcent hsup⟩
  -- All Sylow subgroups are normal, so `K` is nilpotent.
  refine (Group.isNilpotent_of_finite_tfae (G := K)).out 1 4 rfl rfl |>.mpr ?_
  intro r hr P
  haveI := hr
  obtain ⟨R, -, hRn⟩ := hkey r
  haveI : (R : Subgroup K).Normal := hRn
  obtain ⟨g, hg⟩ := IsPretransitive.exists_smul_eq (M := K) R P
  have hPR : (↑P : Subgroup K) = ↑R := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.Normal.conj_smul_eq_self g (↑R)
  rw [hPR]
  exact hRn

private theorem fpf_prime_main : ∀ (n : ℕ) (K : Type*) [Group K] [Finite K] [Group.IsSolvable K],
    Nat.card K = n → ∀ (α : MulAut K) (q : ℕ), q.Prime → α ^ q = 1 →
      IsFpf α → Group.IsNilpotent K := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro m ih K _ _ _ hcard α q hq hαq hα
  exact fpf_prime_step m K hcard ih α q hq hαq hα

theorem isNilpotent_of_fpf_prime {K : Type*} [Group K] [Finite K] [Group.IsSolvable K] {α : MulAut K} {q : ℕ} (hq : q.Prime) (hαq : α ^ q = 1) (hα : Work.NPC.Fpf.IsFpf α) : Group.IsNilpotent K :=
  fpf_prime_main (Nat.card K) K rfl α q hq hαq hα

end Work.Frobenius.Fpf
