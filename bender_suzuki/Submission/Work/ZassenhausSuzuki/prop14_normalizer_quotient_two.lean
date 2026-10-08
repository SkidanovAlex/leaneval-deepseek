import Mathlib
import Submission.Work.ZassenhausSuzuki.SingerAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-- **The group-theoretic bookkeeping step.**

Let `A ≤ N` be subgroups of a finite group, with `A` normal in `N` (witnessed by the elementwise
condition `∀ n ∈ N, ∀ a ∈ A, n a n⁻¹ ∈ A`) and with the `2^e`-th power of every element of `N`
lying in `A`.  Then `[N : A]` is a power of two, i.e. `|N| = |A| * 2^k`.

Proof: in the quotient `N ⧸ A` every element has order dividing `2^e`; hence the quotient is a
`2`-group (`isPGroup_iff_exists_pow_pow_eq_one`), so its cardinality — which is the index
`[N : A]` — is a power of two, and `|N| = |A| * [N : A]` by `Subgroup.card_mul_index`. -/
private lemma card_eq_mul_two_pow_of_normal {G : Type} [Group G] [Finite G]
    (A N : Subgroup G) (hAN : A ≤ N)
    (hNA : ∀ n ∈ N, ∀ a ∈ A, n * a * n⁻¹ ∈ A)
    (hexp : ∃ e : ℕ, ∀ x ∈ N, x ^ (2 ^ e) ∈ A) :
    ∃ k : ℕ, Nat.card ↥N = Nat.card ↥A * 2 ^ k := by
  obtain ⟨e, he⟩ := hexp
  set K : Subgroup ↥N := A.subgroupOf N with hK
  haveI hKnormal : K.Normal := by
    rw [hK]
    refine Subgroup.Normal.mk ?_
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    change (g : G) * (n : G) * (g : G)⁻¹ ∈ A
    exact hNA (g : G) g.2 (n : G) hn
  have hP : IsPGroup 2 (↥N ⧸ K) := by
    rw [isPGroup_iff_exists_pow_pow_eq_one]
    refine ⟨e, ?_⟩
    intro g
    refine QuotientGroup.induction_on g ?_
    intro x
    have hx : (QuotientGroup.mk' K) x ^ (2 ^ e) = 1 := by
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf]
      simpa using he (x : G) x.2
    simpa only [QuotientGroup.mk'_apply] using hx
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hcardK : Nat.card ↥K = Nat.card ↥A := by
    rw [hK]
    exact Nat.card_congr
      { toFun := fun x => ⟨(x : ↥N), Subgroup.mem_subgroupOf.mp x.2⟩
        invFun := fun a => ⟨⟨(a : G), hAN a.2⟩, Subgroup.mem_subgroupOf.mpr a.2⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun a => Subtype.ext rfl }
  exact ⟨k, by rw [← Subgroup.card_mul_index K, Subgroup.index_eq_card, hcardK, hk]⟩

/-- **Suzuki 1962, Proposition 14 (last clause).**

In the split rank-one Zassenhaus setting with root group `Q` a `2`-group and `H` strongly
embedded (`SzHyp`), let `z` be a *strongly real* element with `z * z ≠ 1` and put
`A = C_G(z)`.  Then `N_G(A)/A` is a `2`-group, i.e. `[N_G(A) : A]` is a power of two.

The claim is **false** for the weaker hypothesis "`A` abelian, self-centralising, every `a ∈ A#`
strongly real with `C_G(a) = A`" (`G = Z/7 ⋊ Z/6`, `A = Z/7`: `N_G(A)/A ≅ Z/6`), so the
`SzHyp` structure — in particular `HasFourGroup G` — is essential.

**Everything except the final bookkeeping step is already proved** in
`Submission/Work/ZassenhausSuzuki/singer_centralizer_eq.lean` (import it; all unproved-free):

* `isPGroup_centralizer_involution h hu` : `C_G(u)` is a `2`-group for **every** involution `u`;
* `involution_inverts_centralizer h hz2 hsr hyN hy2 hyA` : an involution `y ∈ N_G(A) \ A` inverts
  `A`, so every element of the coset `yA` is an involution;
* `mem_centralizer_of_commutes`, `inverting_differ_mem_centralizer`, `conj_inverts`,
  `conj_eq_mul_mem` : two elements of `N_G(A)` inverting `A` differ by an element of `A`, so
  `x y x⁻¹ = y * c` with `c ∈ A`;
* `conj_mul_inv_surjective` : the map `a ↦ (x a x⁻¹)·a⁻¹` is onto `A` (injective since a
  non-trivial fixed point would put `x` in `C_G(a) = A`);
* `exists_involution_commuting_of_notMem` : hence there is an involution in the coset `yA`
  commuting with `x`;
* `orderOf_dvd_card_Q_of_mem_centralizer_involution` : `x ∈ C_G(u)`, `u` an involution ⟹
  `orderOf x ∣ |Q|`;
* `pow_card_Q_mem_of_mem_normalizer` : **`x ^ |Q| ∈ A` for every `x ∈ N_G(A)`**;
* `inverting_involution_data` : from `z = a₀ * b₀` with involutions, `a₀` is an involution in
  `N_G(A) \ A`.

So the remaining work is exactly: apply `pow_card_Q_mem_of_mem_normalizer` (with `y := a₀` from
`inverting_involution_data`) and close with the quotient bookkeeping of
`Work.ZassenhausSuzuki.quotient_normalizer_isPGroup_two` (index identity + Cauchy). -/
theorem prop14_normalizer_quotient_two {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (h : Work.ZassenhausSuzuki.SzHyp H Q t s)
    {z : G} (hz2 : z * z ≠ 1)
    (hsr : ∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = z) :
    ∃ k : ℕ,
      Nat.card ↥(Subgroup.normalizer (Subgroup.centralizer ({z} : Set G) : Set G)) =
        Nat.card ↥(Subgroup.centralizer ({z} : Set G)) * 2 ^ k := by
  obtain ⟨a₀, b₀, ha₀, hb₀, hab⟩ := hsr
  obtain ⟨ha₀2, ha₀N, ha₀A⟩ := inverting_involution_data h hz2 ha₀ hb₀ hab
  obtain ⟨e, he⟩ := h.two.exists_card_eq
  refine card_eq_mul_two_pow_of_normal
    (Subgroup.centralizer ({z} : Set G))
    (Subgroup.normalizer (Subgroup.centralizer ({z} : Set G) : Set G))
    Subgroup.le_normalizer ?_ ?_
  · intro n hn a ha
    exact (Subgroup.mem_normalizer_iff.mp hn a).mp ha
  · refine ⟨e, ?_⟩
    intro x hx
    rw [← he]
    exact pow_card_Q_mem_of_mem_normalizer h hz2 ⟨a₀, b₀, ha₀, hb₀, hab⟩ ha₀N ha₀2 ha₀A hx

end Work.ZassenhausSuzuki
