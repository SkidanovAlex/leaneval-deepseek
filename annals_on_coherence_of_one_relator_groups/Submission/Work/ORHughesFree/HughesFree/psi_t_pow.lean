import Mathlib
import Submission.Work.ORHughesFree.HughesFree.skewLaurentDecompAux

namespace Work.ORHughesFree.HughesFree

/-- The decomposition of the group element `t ^ k` is `1 * t ^ k`: both the `N`-part and the
exponent recorded by `npart`/`kpart` are the obvious ones, by uniqueness of the decomposition. -/
theorem npart_kpart_t_pow {K : Type} [Field K] {G : Type} [Group G] {H : Subgroup G}
    {N : Subgroup H} {t : H}
    (htinf : ∀ k : ℤ, k ≠ 0 → t ^ k ∉ N)
    (hgen : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k) (k : ℤ) :
    npart N t hgen (t ^ k) = 1 ∧ kpart N t hgen (t ^ k) = k := by
  have hdec : ((npart N t hgen (t ^ k) : N) : H) * t ^ (kpart N t hgen (t ^ k))
      = ((1 : N) : H) * t ^ k := by
    rw [← npart_mul_kpart N t hgen (t ^ k)]
    simp
  obtain ⟨hk, hn⟩ := decomp_unique htinf hdec
  exact ⟨hn, hk⟩

/-- The decomposition homomorphism `psi` sends the group-like element `t ^ k` of `K[H]` to the
monomial `t ^ k` of the skew Laurent polynomial ring `K[N][t^{±1}; τ]`. -/
theorem psi_t_pow {K : Type} [Field K] {G : Type} [Group G] {H : Subgroup G} {N : Subgroup H}
    {t : H} (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    [MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)]
    (hact : ∀ (k : ℤ) (n : N), (Multiplicative.ofAdd k) • (MonoidAlgebra.single n (1 : K)) =
        MonoidAlgebra.single ⟨t ^ k * (n : H) * t ^ (-k), htN k n⟩ (1 : K))
    (htinf : ∀ k : ℤ, k ≠ 0 → t ^ k ∉ N)
    (hgen : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k) (k : ℤ) :
    psi htN hact htinf hgen (t ^ k) = SkewMonoidAlgebra.single (Multiplicative.ofAdd k) 1 := by
  obtain ⟨hn, hk⟩ := npart_kpart_t_pow (K := K) (N := N) (t := t) htinf hgen k
  change psiFun N t hgen (t ^ k) = SkewMonoidAlgebra.single (Multiplicative.ofAdd k) 1
  rw [psiFun, hk, hn, ← MonoidAlgebra.one_def]

end Work.ORHughesFree.HughesFree
