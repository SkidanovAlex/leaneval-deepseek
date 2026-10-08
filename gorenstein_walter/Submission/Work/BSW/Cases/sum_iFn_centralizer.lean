import Mathlib
import Submission.Work.BSW.Char.iFn_t
import Submission.Work.BSW.Char.iFn_eq_card_of_mem_K
import Submission.Work.BSW.Char.coset_sK_involutions
import Submission.Work.BSW.Char.ncard_coset_sK
import Submission.Work.BSW.Api.mem_centralizer_iff
import Submission.Work.BSW.Api.ncard_involutions_eq_index

namespace Work.BSW.Cases

/-!
# The sum of `i(x)` over the centralizer of `t`

Bender (*The Brauer–Suzuki–Wall theorem*, Illinois J. Math. **18** (1974) 229–235), §3.

With `H = C_G(t) = K⟨s⟩`, `k = |K|` and `i(x) = #{u : u involution, u⁻¹ x u = x⁻¹}`
(`Work.BSW.iFn`), the restriction of the double count to `H` is

`∑_{x ∈ H} i(x) = I + 2k² + 1`,

where `I = |G : H|` is the number of involutions of `G`.

The proof assembles the values of `i` on the two pieces `H = K ∪ Ks`:

* `i(1) = I`;
* `i(x) = k` for `x ∈ K`, `x ≠ 1, t` (`Work.BSW.Char.iFn_eq_card_of_mem_K`);
* `i(t) = k + 1` (`Work.BSW.Char.iFn_t`);
* `i(x) = k + 1` for every involution `x` — in particular for the `k` elements of the coset
  `Ks` — because `i` is a class function and all involutions are conjugate to `t`.

This file also records the small conjugacy lemmas used to make `i` a class function, so that the
statement does not depend on the (still incomplete) `Submission.Work.BSW.Cases.bswCompletionProp`.
-/

section Conjugation

variable {G : Type} [Group G]

/-- `a⁻¹ * x * a` has the same order as `x`. -/
private theorem orderOf_conj_inv_aux (a x : G) : orderOf (a⁻¹ * x * a) = orderOf x := by
  have hh : a⁻¹ * x * a = (MulAut.conj a⁻¹) x := by simp
  rw [hh, MulEquiv.orderOf_eq]

/-- The conjugation relation `v⁻¹ * (a * x * a⁻¹) * v = (a * x * a⁻¹)⁻¹` is transported by
`v ↦ a⁻¹ * v * a`. -/
private theorem conj_inv_iff_aux (a x v : G) :
    (v⁻¹ * (a * x * a⁻¹) * v = (a * x * a⁻¹)⁻¹) ↔
      ((a⁻¹ * v * a)⁻¹ * x * (a⁻¹ * v * a) = x⁻¹) := by
  constructor
  · intro hv
    calc (a⁻¹ * v * a)⁻¹ * x * (a⁻¹ * v * a)
        = a⁻¹ * (v⁻¹ * (a * x * a⁻¹) * v) * a := by group
      _ = a⁻¹ * (a * x * a⁻¹)⁻¹ * a := by rw [hv]
      _ = x⁻¹ := by group
  · intro hv
    calc v⁻¹ * (a * x * a⁻¹) * v
        = a * ((a⁻¹ * v * a)⁻¹ * x * (a⁻¹ * v * a)) * a⁻¹ := by group
      _ = a * x⁻¹ * a⁻¹ := by rw [hv]
      _ = (a * x * a⁻¹)⁻¹ := by group

/-- `i` is invariant under conjugation. -/
private theorem iFn_conj_aux (a x : G) :
    Work.BSW.iFn G (a * x * a⁻¹) = Work.BSW.iFn G x := by
  rw [Work.BSW.iFn, Work.BSW.iFn]
  refine Set.ncard_congr (fun u _ => a⁻¹ * u * a) ?_ ?_ ?_
  · rintro u ⟨hu2, hu⟩
    exact ⟨by rw [orderOf_conj_inv_aux, hu2], (conj_inv_iff_aux a x u).mp hu⟩
  · intro u v _ _ huv
    have hh : a⁻¹ * u * a = a⁻¹ * v * a := huv
    calc u = a * (a⁻¹ * u * a) * a⁻¹ := by group
      _ = a * (a⁻¹ * v * a) * a⁻¹ := by rw [hh]
      _ = v := by group
  · intro b hb
    refine ⟨a * b * a⁻¹, ⟨?_, ?_⟩, by group⟩
    · have hh : a * b * a⁻¹ = (MulAut.conj a) b := by simp
      rw [hh, MulEquiv.orderOf_eq, hb.1]
    · exact (conj_inv_iff_aux a x (a * b * a⁻¹)).mpr (by
        calc (a⁻¹ * (a * b * a⁻¹) * a)⁻¹ * x * (a⁻¹ * (a * b * a⁻¹) * a)
            = b⁻¹ * x * b := by group
          _ = x⁻¹ := hb.2)

end Conjugation

/-- For every involution `x` of `G`, `i(x) = |K| + 1`: all involutions are conjugate to `t`
(`BSWHyps2` (iv)), conjugation preserves `i`, and `i(t) = |K| + 1`. -/
private theorem iFn_of_orderOf_eq_two_aux {G : Type} [Group G] [Finite G] {t s : G}
    {K : Subgroup G} (h : Work.GW2.BSWHyps2 G t s K) {x : G} (hx : orderOf x = 2) :
    Work.BSW.iFn G x = Nat.card ↥K + 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (Work.BSW.involutions_conj h x hx)
  have hx' : x = c⁻¹ * t * c := by rw [← hc]; group
  rw [hx']
  have hconj : Work.BSW.iFn G (c⁻¹ * t * c) = Work.BSW.iFn G t := by
    simpa only [inv_inv] using iFn_conj_aux c⁻¹ t
  rw [hconj, Work.BSW.Char.iFn_t h]

theorem sum_iFn_centralizer {G : Type} [Group G] [Fintype G] [DecidableEq G]
    {t s : G} {K : Subgroup G} (h : Work.GW2.BSWHyps2 G t s K) :
    Finset.sum (Finset.univ.filter (fun x : G => t * x = x * t)) (fun x => Work.BSW.iFn G x)
      = Work.BSW.invCount G + 2 * (Nat.card ↥K) ^ 2 + 1 := by
  classical
  -- The two pieces `K` and the coset `Ks` of `H = C_G(t)`, as finsets.
  set Kf : Finset G := Finset.univ.filter (fun x : G => x ∈ K) with hKf
  set Bf : Finset G := Finset.univ.filter (fun x : G => ∃ c ∈ K, x = c * s) with hBf
  have hmemKf : ∀ x : G, x ∈ Kf ↔ x ∈ K := by
    intro x; rw [hKf, Finset.mem_filter]; simp
  have hmemBf : ∀ x : G, x ∈ Bf ↔ ∃ c ∈ K, x = c * s := by
    intro x; rw [hBf, Finset.mem_filter]; simp
  have hcardKf : Kf.card = Nat.card ↥K := by
    rw [hKf, ← Fintype.card_subtype (fun x : G => x ∈ K), ← Nat.card_eq_fintype_card]
  set k : ℕ := Nat.card ↥K with hk
  have h1K : (1 : G) ∈ Kf := (hmemKf 1).mpr K.one_mem
  have htK : t ∈ Kf := (hmemKf t).mpr (Work.BSW.t_mem_K h)
  have h1t : (1 : G) ≠ t := (Work.BSW.t_ne_one h).symm
  have htne : t ≠ (1 : G) := Work.BSW.t_ne_one h
  have h2le : 2 ≤ k := by
    rw [← hcardKf]
    have hsub : ({(1 : G), t} : Finset G) ⊆ Kf := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h1K
      · exact htK
    have hc := Finset.card_le_card hsub
    rwa [Finset.card_pair h1t] at hc
  -- `H = K ∪ Ks`, a disjoint union.
  have hkey : ∀ x : G, (t * x = x * t) ↔ (x ∈ K ∨ ∃ c ∈ K, x = c * s) := by
    intro x
    have h1 : (t * x = x * t) ↔ x ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]; exact eq_comm
    exact h1.trans (Work.BSW.Api.mem_centralizer_iff h x)
  have hH : Finset.univ.filter (fun x : G => t * x = x * t) = Kf ∪ Bf := by
    ext x
    rw [Finset.mem_filter, Finset.mem_union, hmemKf x, hmemBf x, hkey x]
    simp
  have hdisj : Disjoint Kf Bf := by
    rw [Finset.disjoint_left]
    intro x hxK hxB
    rw [hmemKf] at hxK
    rw [hmemBf] at hxB
    obtain ⟨c, hc, hxc⟩ := hxB
    have hs : s = c⁻¹ * x := by rw [hxc]; group
    exact (Work.BSW.s_notMem_K h) (by rw [hs]; exact K.mul_mem (K.inv_mem hc) hxK)
  -- The sum over `K`: `i(1) = I`, `i(t) = k + 1`, and `i(x) = k` on the remaining `k - 2` points.
  have ht_erase : t ∈ Kf.erase 1 := by
    rw [Finset.mem_erase]; exact ⟨htne, htK⟩
  have e3 : ∑ x ∈ (Kf.erase 1).erase t, Work.BSW.iFn G x = ((Kf.erase 1).erase t).card * k := by
    trans ∑ x ∈ (Kf.erase 1).erase t, k
    · apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_erase, Finset.mem_erase] at hx
      obtain ⟨hxt, hx1, hxKf⟩ := hx
      rw [hk]
      exact Work.BSW.Char.iFn_eq_card_of_mem_K h ((hmemKf x).mp hxKf) hx1 hxt
    · rw [Finset.sum_const, smul_eq_mul]
  have hcard_rest : ((Kf.erase 1).erase t).card = k - 2 := by
    rw [Finset.card_erase_of_mem ht_erase, Finset.card_erase_of_mem h1K, hcardKf, hk]
    omega
  have e1 : ∑ x ∈ Kf, Work.BSW.iFn G x
      = ∑ x ∈ Kf.erase 1, Work.BSW.iFn G x + Work.BSW.iFn G 1 :=
    (Finset.sum_erase_add Kf (fun x => Work.BSW.iFn G x) h1K).symm
  have e2 : ∑ x ∈ Kf.erase 1, Work.BSW.iFn G x
      = ∑ x ∈ (Kf.erase 1).erase t, Work.BSW.iFn G x + Work.BSW.iFn G t :=
    (Finset.sum_erase_add (Kf.erase 1) (fun x => Work.BSW.iFn G x) ht_erase).symm
  have h_sum_K : ∑ x ∈ Kf, Work.BSW.iFn G x = Work.BSW.invCount G + (k + 1) + (k - 2) * k := by
    rw [e1, e2, e3, Work.BSW.iFn_one, Work.BSW.Char.iFn_t h, hcard_rest]
    ring
  -- The sum over the coset `Ks`: all `k` elements are involutions, so each contributes `k + 1`.
  have hBimage : Bf = Kf.image (fun c : G => c * s) := by
    ext x
    constructor
    · intro hx
      rw [hmemBf] at hx
      obtain ⟨c, hc, rfl⟩ := hx
      rw [Finset.mem_image]
      exact ⟨c, (hmemKf c).mpr hc, rfl⟩
    · intro hx
      rw [Finset.mem_image] at hx
      obtain ⟨c, hc, hcx⟩ := hx
      rw [hmemBf]
      exact ⟨c, (hmemKf c).mp hc, hcx.symm⟩
  have hinj : Set.InjOn (fun c : G => c * s) (↑Kf : Set G) := by
    intro a _ b _ hab; exact mul_right_cancel hab
  have h_sum_B : ∑ x ∈ Bf, Work.BSW.iFn G x = k * (k + 1) := by
    rw [hBimage, Finset.sum_image hinj]
    trans ∑ c ∈ Kf, (k + 1)
    · apply Finset.sum_congr rfl
      intro c hc
      rw [hk]
      exact iFn_of_orderOf_eq_two_aux h
        ((Work.BSW.Char.coset_sK_involutions h).1 c ((hmemKf c).mp hc)).1
    · rw [Finset.sum_const, smul_eq_mul, hcardKf, hk]
  -- Assemble and finish with the arithmetic `(k + 1) + (k - 2)k + k(k + 1) = 2k² + 1`.
  rw [hH, Finset.sum_union hdisj, h_sum_K, h_sum_B]
  have harith : Work.BSW.invCount G + (k + 1) + (k - 2) * k + k * (k + 1)
      = Work.BSW.invCount G + 2 * k ^ 2 + 1 := by
    have h1 : (k - 2) * k = k * k - 2 * k := Nat.sub_mul k 2 k
    rw [h1]
    have h2 : 2 * k ≤ k * k := by nlinarith
    have h3 : k * k - 2 * k + 2 * k = k * k := Nat.sub_add_cancel h2
    nlinarith [h3]
  rw [harith, hk]

end Work.BSW.Cases
