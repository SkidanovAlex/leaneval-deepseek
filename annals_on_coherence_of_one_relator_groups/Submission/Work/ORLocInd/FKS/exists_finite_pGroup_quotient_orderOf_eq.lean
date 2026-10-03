import Mathlib
import Submission.Work.ORLocInd.Basic
import Submission.Work.ORLocInd.FKS.not_mem_normalClosure_pow

set_option linter.style.haveILetI false

namespace Work.ORLocInd.FKS

/-- **Order reduction in a finite `p`-group.**  If `v` has order `p ^ m` in a finite `p`-group `Q`
and `k ≤ m`, then some finite `p`-group quotient of `Q` has the image of `v` of order exactly
`p ^ k` (namely `Q ⧸ normalClosure {v ^ (p ^ k)}`).  This is the "simple inductive argument" in the
proof of Fischer--Karrass--Solitar 1972, Theorem 2, used to pass from a quotient in which `u` has
order a multiple of `p ^ k` to one in which its order is exactly `p ^ k`.

Suggested proof.  Take the quotient `R := Q ⧸ N` by `N := Subgroup.normalClosure {v ^ p ^ k}` and
`θ := QuotientGroup.mk' N`.  Since `v ^ p ^ k ∈ N`, the order of `θ v` divides `p ^ k`, and because
`R` is again a finite `p`-group it is a power `p ^ s` of `p` with `s ≤ k`.  If `s < k` then
`(θ v) ^ p ^ (k - 1) = 1`, i.e. `v ^ p ^ (k - 1) ∈ N`; applying the companion lemma
`Work.ORLocInd.FKS.not_mem_normalClosure_pow` to the element `y := v ^ p ^ (k - 1)` of the finite
`p`-group `Q` (whose `p`-th power is `v ^ p ^ k`) gives `y = 1`, contradicting
`orderOf y = p ^ (m - k + 1) ≥ p > 1` (`orderOf_pow`, using `k ≤ m`).  Hence `s = k`.

Edge cases: `k = 0` (trivial quotient), and `m = 0` (then `v = 1` and `k = 0`).

Universe remark: the witness `R` is asked for in an arbitrary universe `u₂` (the statement uses
`Type*`), so we realize the quotient `G := Q ⧸ N` inside the small group `Equiv.Perm (Fin n)`
(`n := card G`) via the (conjugated) left regular action, and take `R` to be the range of that
faithful action.  In the intended applications one simply takes `u₂ = u₁` and `R = Q ⧸ N`. -/
theorem exists_finite_pGroup_quotient_orderOf_eq {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) (hQ : IsPGroup p Q) {v : Q} {m k : ℕ} (hord : orderOf v = p ^ m) (hk : k ≤ m) :
    ∃ (R : Type*) (_ : Group R) (_ : Finite R) (_ : IsPGroup p R) (θ : Q →* R),
      orderOf (θ v) = p ^ k := by
  -- the subgroup we quotient by
  set N : Subgroup Q := Subgroup.normalClosure ({v ^ p ^ k} : Set Q) with hN
  haveI hNn : N.Normal := by rw [hN]; exact Subgroup.normalClosure_normal
  have hmemN : v ^ p ^ k ∈ N := by
    rw [hN]; exact Subgroup.subset_normalClosure (Set.mem_singleton _)
  have hθmem : QuotientGroup.mk' N (v ^ p ^ k) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hmemN
  -- the image of `v` in `Q ⧸ N` has order exactly `p ^ k`
  have hmain : orderOf (QuotientGroup.mk' N v) = p ^ k := by
    by_contra hne
    have hdiv : orderOf (QuotientGroup.mk' N v) ∣ p ^ k := by
      rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, hθmem]
    obtain ⟨s, hsle, hs⟩ := (Nat.dvd_prime_pow hp).mp hdiv
    have hsk : s ≠ k := by rintro rfl; exact hne hs
    have hslt : s < k := lt_of_le_of_ne hsle hsk
    have hkpos : 1 ≤ k := by omega
    have hpsle : s ≤ k - 1 := by omega
    have hpow2 : (QuotientGroup.mk' N v) ^ (p ^ (k - 1)) = 1 :=
      (orderOf_dvd_iff_pow_eq_one).mp (by rw [hs]; exact pow_dvd_pow p hpsle)
    have hθy : QuotientGroup.mk' N (v ^ p ^ (k - 1)) = 1 := by
      rw [map_pow, hpow2]
    have hy_mem : v ^ p ^ (k - 1) ∈ N := by
      rw [hN, ← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
      exact hθy
    set y : Q := v ^ p ^ (k - 1) with hy
    have hy_pow : y ^ p = v ^ p ^ k := by
      have hexp : p ^ (k - 1) * p = p ^ k := by
        rw [← pow_succ, Nat.sub_add_cancel hkpos]
      rw [hy, ← pow_mul, hexp]
    have hmem2 : y ∈ Subgroup.normalClosure ({y ^ p} : Set Q) := by
      rw [hy_pow, ← hN, hy]
      exact hy_mem
    have hy1 : y = 1 := not_mem_normalClosure_pow hp hQ y hmem2
    have hyne : y ≠ 1 := by
      intro h
      rw [hy] at h
      have hdvd : orderOf v ∣ p ^ (k - 1) := (orderOf_dvd_iff_pow_eq_one).mpr h
      rw [hord] at hdvd
      have hmlt : m ≤ k - 1 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
      omega
    exact hyne hy1
  -- a faithful permutation realization of `G := Q ⧸ N` in a small universe
  haveI : Fintype (Q ⧸ N) := Fintype.ofFinite _
  let e : (Q ⧸ N) ≃ ULift (Fin (Fintype.card (Q ⧸ N))) :=
    (Fintype.equivFin (Q ⧸ N)).trans Equiv.ulift.symm
  letI : MulAction (Q ⧸ N) (ULift (Fin (Fintype.card (Q ⧸ N)))) :=
    { smul := fun g x => e (g * e.symm x)
      one_smul := by intro x; change e (1 * e.symm x) = x; simp
      mul_smul := by
        intro a b x
        change e ((a * b) * e.symm x) = e (a * e.symm (e (b * e.symm x)))
        simp [mul_assoc] }
  let φ : (Q ⧸ N) →* Equiv.Perm (ULift (Fin (Fintype.card (Q ⧸ N)))) :=
    MulAction.toPermHom (Q ⧸ N) (ULift (Fin (Fintype.card (Q ⧸ N))))
  have hφinj : Function.Injective φ := by
    intro g h hgh
    have h1 : g • (e 1) = h • (e 1) := by
      simpa [φ, MulAction.toPermHom_apply, MulAction.toPerm_apply] using
        congrArg (fun (σ : Equiv.Perm (ULift (Fin (Fintype.card (Q ⧸ N))))) => σ (e 1)) hgh
    have h2 : e (g * e.symm (e 1)) = e (h * e.symm (e 1)) := h1
    simpa [Equiv.symm_apply_apply] using e.injective h2
  let θ : Q →* Equiv.Perm (ULift (Fin (Fintype.card (Q ⧸ N)))) := φ.comp (QuotientGroup.mk' N)
  refine ⟨θ.range, inferInstance, inferInstance, ?_, θ.rangeRestrict, ?_⟩
  · exact IsPGroup.of_surjective hQ θ.rangeRestrict θ.rangeRestrict_surjective
  · rw [← Subgroup.orderOf_coe (θ.rangeRestrict v), MonoidHom.coe_rangeRestrict]
    rw [show θ v = φ (QuotientGroup.mk' N v) from rfl, orderOf_injective φ hφinj]
    exact hmain

end Work.ORLocInd.FKS
