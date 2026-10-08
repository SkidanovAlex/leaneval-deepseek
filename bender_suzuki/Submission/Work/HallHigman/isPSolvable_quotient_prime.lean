import Mathlib
import Submission.Work.HallHigman.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `p`-solvability passes to quotients

If `G` is `p`-solvable (in the sense of `Work.HallHigman.IsPSolvable`: `G` possesses a normal
series whose factors are `p`-groups or `p'`-groups) and `N ◁ G` is normal, then `G ⧸ N` is
`p`-solvable.

The series of `G` is simply pushed forward along the quotient map `G →* G ⧸ N`: the image of a
normal subgroup is normal, `⊥` and `⊤` are preserved (the quotient map is surjective), and the
index of the image factor `(K.map φ) / (H.map φ)` divides the index of the original factor
`K / (H ∩ K)`.

The latter is the content of `relIndex_map_dvd` below.  Its proof rests on two elementary
facts about the relative index:

* `Subgroup.relIndex_comap` computes a relative index after pulling back along a homomorphism,
  and
* `Subgroup.comap_map_eq` says that pulling back the image of `H` recovers `H ⊔ ker φ`.

Consequently `(H.map φ).relIndex (K.map φ) = (H ⊔ ker φ).relIndex K`, and since
`H ≤ H ⊔ ker φ`, the relative index `(H ⊔ ker φ).relIndex K` divides `H.relIndex K`
(`Subgroup.relIndex_dvd_of_le_left`).
-/

namespace Work.HallHigman

/-- A group homomorphism carries a relative index to a divisor of it: for subgroups `H`, `K` of
`G` and any homomorphism `φ : G →* L`, the index of the image factor `H.map φ` in `K.map φ`
divides the index of `H ⊓ K` in `K`.

No finiteness or normality assumption is needed: in fact
`(H.map φ).relIndex (K.map φ) = (H ⊔ φ.ker).relIndex K`. -/
theorem relIndex_map_dvd {G L : Type*} [Group G] [Group L] (φ : G →* L) (H K : Subgroup G) :
    (H.map φ).relIndex (K.map φ) ∣ H.relIndex K := by
  have key : (H.map φ).relIndex (K.map φ) = (H ⊔ φ.ker).relIndex K := by
    have h1 : (H ⊔ φ.ker).map φ = H.map φ := by
      rw [Subgroup.map_sup]
      simp
    rw [← h1, ← Subgroup.relIndex_comap (H := (H ⊔ φ.ker).map φ) (f := φ) (K := K),
      Subgroup.comap_map_eq]
    rw [sup_assoc, sup_idem]
  rw [key]
  exact Subgroup.relIndex_dvd_of_le_left K le_sup_left

theorem isPSolvable_quotient_prime {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] (N : Subgroup G)
    [N.Normal] (h : Work.HallHigman.IsPSolvable p G) : Work.HallHigman.IsPSolvable p (G ⧸ N) := by
  obtain ⟨n, f, hf0, hfn, hnorm, hfac⟩ := h
  refine ⟨n, fun i => (f i).map (QuotientGroup.mk' N), ?_, ?_, ?_, ?_⟩
  · -- the first term is `⊥`
    change (f ⟨0, Nat.succ_pos n⟩).map (QuotientGroup.mk' N) = ⊥
    rw [hf0]
    exact Subgroup.map_bot _
  · -- the last term is `⊤`
    change (f (Fin.last n)).map (QuotientGroup.mk' N) = ⊤
    rw [hfn]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)
  · -- every term is normal
    intro i
    exact Subgroup.Normal.map (hnorm i) (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  · -- the index of each factor divides the index of the corresponding factor of `G`
    intro i
    have hdvd : ((f i.castSucc).map (QuotientGroup.mk' N)).relIndex
        ((f i.succ).map (QuotientGroup.mk' N)) ∣ (f i.castSucc).relIndex (f i.succ) :=
      relIndex_map_dvd (QuotientGroup.mk' N) _ _
    rcases hfac i with hD | ⟨k, hk⟩
    · -- a factor of `p'`-index has `p'`-index in the quotient
      left
      intro hpd
      exact hD (hpd.trans hdvd)
    · -- a factor of `p`-power index has `p`-power index in the quotient
      right
      have hD : (f i.castSucc).relIndex (f i.succ) = p ^ k := hk
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (hD ▸ hdvd)
      exact ⟨j, hj⟩

end Work.HallHigman
