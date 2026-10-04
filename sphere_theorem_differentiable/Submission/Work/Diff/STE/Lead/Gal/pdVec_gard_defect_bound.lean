import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.pdList_mul_sub
import Submission.Work.Diff.STE.commutator_core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Leibniz defect bound for the `gal`-defect of `pdVec`

`Work.Diff.STE.Lead.Gal.pdVec_gard_defect_bound` compares the `k`-th iterated partial derivative
(along the directions `l : Fin k → ι`) of the coefficient function

  `y ↦ ∑ c, ∑ d, A c d y * ∂_c ∂_d u y`

with the expression in which the coefficient is *frozen at the point* `z`,

  `∑ c, ∑ d, A c d z * ∂_c ∂_d (∂^l u) z`.

The difference is the "Leibniz defect" of the product rule: by
`Work.Diff.STE.pdList_mul_sub` the iterated derivative of a product is the sum of the terms
`∂^{p.1}A · ∂^{p.2}g` over all complementary splits `(p.1, p.2)` of the direction list, and the
frozen expression is exactly the term with `p.1 = []` (all derivatives falling on `u`, which
commute with `∂_c ∂_d` by `Work.Diff.STE.cm_pdVec_pd_pd`).  Hence

  `∂^l (A·g) - A · ∂^l g = ∑_{p : p.1 ≠ []} ∂^{p.1}A · ∂^{p.2}g`,

and each remaining term carries at least one derivative of the coefficient (order `≤ k`, bounded
by `K`) and at most `k - 1` further derivatives of `u` on top of the two of `∂_c∂_d u` (order
`≤ k+1`, bounded by `P`).  Summing over the at most `2^k` splits and the `#ι ^ 2` pairs `(c,d)`
gives the statement with `C = #ι ^ 2 * 2^k`.

The file is self-contained: it only uses the iterated Leibniz rule and the `pd`-commutation
lemmas of the STE library, plus elementary list arithmetic.
-/

set_option maxHeartbeats 1000000

noncomputable section

namespace Work.Diff.STE.Lead.Gal

section Helpers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `pdVec 0` is the identity (`Fin 0 → ι` is a singleton, so the direction list is empty). -/
lemma pdVec_zero_gal (l : Fin 0 → ι) (f : (ι → ℝ) → ℂ) : Work.Diff.STE.pdVec 0 l f = f := by
  simp [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]

/-- `ContDiff` at the top (smooth) index implies any finite order. -/
lemma contDiff_nat_of_smooth {u : (ι → ℝ) → ℂ}
    (hu : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) u) (m : ℕ) :
    ContDiff ℝ ((m : ℕ) : WithTop ℕ∞) u :=
  hu.of_le (WithTop.coe_le_coe.mpr le_top)

/-- `pdList` of a list is `pdVec` of the corresponding `Fin`-indexed tuple. -/
lemma pdList_eq_pdVec_gal (q : List ι) (f : (ι → ℝ) → ℂ) :
    Work.Diff.STE.pdList q f
      = Work.Diff.STE.pdVec q.length (fun i : Fin q.length => q.get i) f := by
  rw [Work.Diff.STE.pdVec]
  congr 1
  exact (List.ofFn_get q).symm

/-- Norm of a list sum. -/
lemma norm_list_sum_le_gal {α : Type*} (L : List α) (f : α → ℂ) :
    ‖(L.map f).sum‖ ≤ (L.map (fun a => ‖f a‖)).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

/-- A list sum of values each bounded by `c` is at most `length * c`. -/
lemma norm_list_sum_le_mul_gal {α : Type*} (L : List α) (f : α → ℂ) (c : ℝ)
    (h : ∀ a ∈ L, ‖f a‖ ≤ c) :
    ‖(L.map f).sum‖ ≤ (L.length : ℝ) * c := by
  refine (norm_list_sum_le_gal L f).trans ?_
  induction L with
  | nil => simp
  | cons a t ih =>
      have ha : ‖f a‖ ≤ c := h a (by simp)
      have ht : ∀ x ∈ t, ‖f x‖ ≤ c := fun x hx => h x (by simp [hx])
      have hrec := ih ht
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      push_cast
      linarith

/-- The `pdVec` bound on the complexified coefficient function bounds every `pdList` iterate. -/
lemma norm_pdList_ofReal_le_gal {k : ℕ} {A : (ι → ℝ) → ℝ} {K : ℝ}
    (hK : ∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → ι) (z : ι → ℝ),
      ‖Work.Diff.STE.pdVec m β (fun y => ((A y : ℝ) : ℂ)) z‖ ≤ K)
    {q : List ι} (hq : q.length ≤ k) (z : ι → ℝ) :
    ‖Work.Diff.STE.pdList q (fun y => ((A y : ℝ) : ℂ)) z‖ ≤ K := by
  rw [pdList_eq_pdVec_gal]
  exact hK q.length hq (fun i : Fin q.length => q.get i) z

/-- The `pdVec` bound on `u` bounds every `pdList` iterate of `∂_c∂_d u`, one order down. -/
lemma norm_pdList_pair_le_gal {k : ℕ} {u : (ι → ℝ) → ℂ} {P : ℝ}
    (hP : ∀ (m : ℕ) (hm : m ≤ k + 1) (β : Fin m → ι) (z : ι → ℝ),
      ‖Work.Diff.STE.pdVec m β u z‖ ≤ P)
    (c d : ι) {q : List ι} (hq : q.length + 2 ≤ k + 1) (z : ι → ℝ) :
    ‖Work.Diff.STE.pdList q (fun y => Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) z‖ ≤ P := by
  rw [Work.Diff.STE.cm_pdList_pair q c d u, pdList_eq_pdVec_gal]
  refine hP (q ++ [c, d]).length ?_ (fun i : Fin (q ++ [c, d]).length => (q ++ [c, d]).get i) z
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- **The Leibniz defect bound for one coefficient `A` and one pair of directions `(c,d)`.**

This is the per-summand estimate behind `pdVec_gard_defect_bound`: the iterated derivative of
`y ↦ A y * ∂_c∂_d u y` minus the frozen term `A z * ∂_c∂_d (∂^l u) z` is bounded by `2^k K P`. -/
lemma pdList_mul_defect_le_gal (k : ℕ) (A : (ι → ℝ) → ℝ)
    (hA : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) A)
    (u : (ι → ℝ) → ℂ) (hu : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) u)
    {K P : ℝ} (hK0 : 0 ≤ K) (hP0 : 0 ≤ P)
    (hK : ∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → ι) (z : ι → ℝ),
      ‖Work.Diff.STE.pdVec m β (fun y => ((A y : ℝ) : ℂ)) z‖ ≤ K)
    (hP : ∀ (m : ℕ) (hm : m ≤ k + 1) (β : Fin m → ι) (z : ι → ℝ),
      ‖Work.Diff.STE.pdVec m β u z‖ ≤ P)
    (c d : ι) (l : Fin k → ι) (z : ι → ℝ) :
    ‖Work.Diff.STE.pdList (List.ofFn l) (fun y => ((A y : ℝ) : ℂ)
          * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) z
        - ((A z : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d
            (Work.Diff.STE.pdList (List.ofFn l) u)) z‖ ≤ (2 : ℝ) ^ k * K * P := by
  classical
  have hu2 : ContDiff ℝ (((k + 2 : ℕ)) : WithTop ℕ∞) u := contDiff_nat_of_smooth hu (k + 2)
  -- the iterated Leibniz rule
  have hleib := Work.Diff.STE.pdList_mul_sub (List.ofFn l) (fun y => ((A y : ℝ) : ℂ))
      (fun y => Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y)
      (fun q _ _ => Work.Diff.STE.cm_diff_pdList_ofReal A hA q)
      (fun q _ hlen => Work.Diff.STE.cm_diff_pdList_pair (k := k) (u := u) hu2 c d
        (by simpa [List.length_ofFn] using hlen))
  -- `∂_c∂_d` commutes with the iterated derivative
  have hcomm : Work.Diff.STE.pdList (List.ofFn l)
        (fun y => Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y)
      = Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdList (List.ofFn l) u)) := by
    have h := Work.Diff.STE.cm_pdVec_pd_pd k l c d u hu2
    rwa [Work.Diff.STE.pdVec] at h
  -- the defect identity
  have hkey : Work.Diff.STE.pdList (List.ofFn l) (fun y => ((A y : ℝ) : ℂ)
          * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) z
        - ((A z : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d
            (Work.Diff.STE.pdList (List.ofFn l) u)) z
      = (((Work.Diff.STE.splits (List.ofFn l)).filter (fun p : List ι × List ι => p.1 ≠ [])).map
          (fun p => Work.Diff.STE.pdList p.1 (fun y => ((A y : ℝ) : ℂ)) z
            * Work.Diff.STE.pdList p.2 (fun y => Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) z)).sum := by
    have h := congrFun hleib z
    rw [hcomm] at h
    exact h
  rw [hkey]
  -- the combinatorial part: at most `2^k` terms, each bounded by `K * P`
  set Sf : List (List ι × List ι) := (Work.Diff.STE.splits (List.ofFn l)).filter
      (fun p : List ι × List ι => p.1 ≠ []) with hSf
  have hSf_len : (Sf.length : ℝ) ≤ (2 : ℝ) ^ k := by
    have h2 : Sf.length ≤ (Work.Diff.STE.splits (List.ofFn l)).length := by
      rw [hSf]; exact List.length_filter_le _ _
    rw [Work.Diff.STE.cm_splits_length_count, List.length_ofFn] at h2
    exact_mod_cast h2
  have hterm : ∀ p ∈ Sf, ‖Work.Diff.STE.pdList p.1 (fun y => ((A y : ℝ) : ℂ)) z
        * Work.Diff.STE.pdList p.2 (fun y => Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) z‖
      ≤ K * P := by
    intro p hp
    rw [hSf] at hp
    obtain ⟨hp', hneBool⟩ := List.mem_filter.mp hp
    have hne : p.1 ≠ [] := of_decide_eq_true hneBool
    have hlen := Work.Diff.STE.cm_splits_mem_length (List.ofFn l) p hp'
    have hlen' : p.1.length + p.2.length = k := by simpa [List.length_ofFn] using hlen
    have h1 : ‖Work.Diff.STE.pdList p.1 (fun y => ((A y : ℝ) : ℂ)) z‖ ≤ K :=
      norm_pdList_ofReal_le_gal hK (by omega) z
    have h2 : ‖Work.Diff.STE.pdList p.2 (fun y => Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) z‖
        ≤ P := by
      refine norm_pdList_pair_le_gal hP c d ?_ z
      have hpos : 1 ≤ p.1.length := List.length_pos_of_ne_nil hne
      omega
    rw [norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) hK0
  have hSsum : ‖(Sf.map (fun p => Work.Diff.STE.pdList p.1 (fun y => ((A y : ℝ) : ℂ)) z
        * Work.Diff.STE.pdList p.2 (fun y => Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) z)).sum‖
      ≤ (Sf.length : ℝ) * (K * P) :=
    norm_list_sum_le_mul_gal Sf
      (fun p => Work.Diff.STE.pdList p.1 (fun y => ((A y : ℝ) : ℂ)) z
        * Work.Diff.STE.pdList p.2 (fun y => Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) z)
      (K * P) (fun p hp => hterm p hp)
  calc ‖(Sf.map (fun p => Work.Diff.STE.pdList p.1 (fun y => ((A y : ℝ) : ℂ)) z
          * Work.Diff.STE.pdList p.2 (fun y => Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) z)).sum‖
      ≤ (Sf.length : ℝ) * (K * P) := hSsum
    _ ≤ (2 : ℝ) ^ k * (K * P) :=
        mul_le_mul_of_nonneg_right hSf_len (mul_nonneg hK0 hP0)
    _ = (2 : ℝ) ^ k * K * P := by ring

end Helpers

/-- **The Leibniz defect bound of the garding/Gal defect.**

For every `k` there is a constant `C ≥ 0` such that: given a coefficient family `A c d` and a
function `u`, with bounds `K` for the iterated derivatives of the (complexified) coefficients
`A c d` up to order `k` at `z`, and `P` for the iterated derivatives of `u` up to order `k+1` at
`z`, the `k`-jet of `y ↦ ∑ c, ∑ d, A c d y * ∂_c∂_d u y` differs from the "frozen coefficient"
expression `∑ c, ∑ d, A c d z * ∂_c∂_d (∂^l u) z` by at most `C (1+K) (1+P)`. -/
theorem pdVec_gard_defect_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : ι → ι → (ι → ℝ) → ℝ) (K P : ℝ)
        (hA : ∀ c d, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (A c d))
        (hK : ∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → ι) (c d : ι) (z : ι → ℝ),
            ‖Work.Diff.STE.pdVec m β (fun y => ((A c d y : ℝ) : ℂ)) z‖ ≤ K)
        (u : (ι → ℝ) → ℂ) (hu : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) u)
        (hP : ∀ (m : ℕ) (hm : m ≤ k + 1) (β : Fin m → ι) (z : ι → ℝ),
            ‖Work.Diff.STE.pdVec m β u z‖ ≤ P)
        (l : Fin k → ι) (z : ι → ℝ),
        ‖Work.Diff.STE.pdVec k l (fun y => ∑ c, ∑ d,
            ((A c d y : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) z
            - (∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
                * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) z)‖
          ≤ C * (1 + K) * (1 + P) := by
  classical
  rcases k with _ | k'
  · -- ## `k = 0`: the two sides agree, so `C = 0` works
    refine ⟨0, le_rfl, ?_⟩
    intro A K P hA hK u hu hP l z
    have h1 : Work.Diff.STE.pdVec 0 l (fun y => ∑ c, ∑ d,
        ((A c d y : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y)
        = (fun y : ι → ℝ => ∑ c, ∑ d,
            ((A c d y : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) :=
      pdVec_zero_gal l _
    have h2 : Work.Diff.STE.pdVec 0 l u = u := pdVec_zero_gal l u
    rw [h1, h2]
    have h3 : (fun y : ι → ℝ => ∑ c, ∑ d,
          ((A c d y : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) z
        = ∑ c, ∑ d, ((A c d z : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) z := rfl
    rw [h3, sub_self, norm_zero, zero_mul, zero_mul]
  · -- ## `k = k' + 1 ≥ 1`: `C = #ι ^ 2 * 2 ^ k`
    refine ⟨(Fintype.card ι : ℝ) ^ 2 * 2 ^ (k' + 1), by positivity, ?_⟩
    intro A K P hA hK u hu hP l z
    by_cases hι : Nonempty ι
    · obtain ⟨i0⟩ := hι
      -- the two bounds are nonnegative
      have hK0 : 0 ≤ K := by
        have h := hK 0 (Nat.zero_le _) Fin.elim0 i0 i0 z
        have h2 : Work.Diff.STE.pdVec 0 Fin.elim0 (fun y => ((A i0 i0 y : ℝ) : ℂ)) z
            = ((A i0 i0 z : ℝ) : ℂ) := congrFun (pdVec_zero_gal Fin.elim0 _) z
        rw [h2] at h
        exact le_trans (norm_nonneg _) h
      have hP0 : 0 ≤ P := by
        have h := hP 0 (Nat.zero_le _) Fin.elim0 z
        have h2 : Work.Diff.STE.pdVec 0 Fin.elim0 u z = u z := congrFun (pdVec_zero_gal Fin.elim0 u) z
        rw [h2] at h
        exact le_trans (norm_nonneg _) h
      have hu' : ContDiff ℝ (((k' + 1 + 2 : ℕ)) : WithTop ℕ∞) u :=
        contDiff_nat_of_smooth hu (k' + 1 + 2)
      -- the subtracted double sum, as a sum over the product index type
      have hsub : (∑ c : ι, ∑ d : ι, ((A c d z : ℝ) : ℂ)
            * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec (k' + 1) l u)) z)
          = ∑ p : ι × ι, ((A p.1 p.2 z : ℝ) : ℂ)
            * Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2
                (Work.Diff.STE.pdVec (k' + 1) l u)) z := by
        rw [← Finset.univ_product_univ, Finset.sum_product]
      -- the `pdVec` of the sum, one `pdList` at a time
      have hfun : (fun y : ι → ℝ => ∑ c : ι, ∑ d : ι,
            ((A c d y : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y)
          = (fun y : ι → ℝ => ∑ p : ι × ι,
            ((A p.1 p.2 y : ℝ) : ℂ) * Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) y) := by
        funext y
        rw [← Finset.univ_product_univ, Finset.sum_product]
      have hlin : Work.Diff.STE.pdList (List.ofFn l) (fun y : ι → ℝ => ∑ p : ι × ι,
            ((A p.1 p.2 y : ℝ) : ℂ) * Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) y)
          = (fun y : ι → ℝ => ∑ p : ι × ι, Work.Diff.STE.pdList (List.ofFn l)
              (fun z : ι → ℝ => ((A p.1 p.2 z : ℝ) : ℂ)
                * Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) z) y) :=
        Work.Diff.STE.cm_pdList_sum (List.ofFn l) (Finset.univ : Finset (ι × ι))
          (fun p : ι × ι => fun y => ((A p.1 p.2 y : ℝ) : ℂ)
            * Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) y)
          (fun p _ q hq hlen => by
            have hlen' : q.length < k' + 1 := by
              have h := List.Sublist.length_le hq
              have hof : (List.ofFn l).length = k' + 1 := List.length_ofFn
              omega
            exact Work.Diff.STE.cm_diff_pdList_mul (k' + 1) A u hA hu' p hlen')
      have hkey : Work.Diff.STE.pdList (List.ofFn l) (fun y : ι → ℝ => ∑ p : ι × ι,
            ((A p.1 p.2 y : ℝ) : ℂ) * Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) y) z
          = ∑ p : ι × ι, Work.Diff.STE.pdList (List.ofFn l)
              (fun z : ι → ℝ => ((A p.1 p.2 z : ℝ) : ℂ)
                * Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) z) z :=
        congrFun hlin z
      rw [hsub, Work.Diff.STE.pdVec, hfun, hkey, ← Finset.sum_sub_distrib]
      -- each summand is a Leibniz defect, bounded by `2^k K P`
      have hterm : ∀ p : ι × ι,
          ‖Work.Diff.STE.pdList (List.ofFn l) (fun y => ((A p.1 p.2 y : ℝ) : ℂ)
              * Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) y) z
            - ((A p.1 p.2 z : ℝ) : ℂ) * Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2
                (Work.Diff.STE.pdList (List.ofFn l) u)) z‖
          ≤ (2 : ℝ) ^ (k' + 1) * K * P :=
        fun p => pdList_mul_defect_le_gal (k' + 1) (A p.1 p.2) (hA p.1 p.2) u hu hK0 hP0
          (fun m hm β z => hK m hm β p.1 p.2 z) hP p.1 p.2 l z
      calc ‖∑ p : ι × ι, (Work.Diff.STE.pdList (List.ofFn l) (fun y => ((A p.1 p.2 y : ℝ) : ℂ)
              * Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) y) z
            - ((A p.1 p.2 z : ℝ) : ℂ) * Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2
                (Work.Diff.STE.pdList (List.ofFn l) u)) z)‖
          ≤ ∑ p : ι × ι, ‖Work.Diff.STE.pdList (List.ofFn l) (fun y => ((A p.1 p.2 y : ℝ) : ℂ)
              * Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) y) z
            - ((A p.1 p.2 z : ℝ) : ℂ) * Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2
                (Work.Diff.STE.pdList (List.ofFn l) u)) z‖ := norm_sum_le _ _
        _ ≤ ∑ _p : ι × ι, (2 : ℝ) ^ (k' + 1) * K * P :=
            Finset.sum_le_sum (fun p _ => hterm p)
        _ = (Fintype.card (ι × ι) : ℝ) * ((2 : ℝ) ^ (k' + 1) * (K * P)) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
            ring
        _ = (Fintype.card ι : ℝ) ^ 2 * ((2 : ℝ) ^ (k' + 1) * (K * P)) := by
            rw [Fintype.card_prod]
            push_cast
            ring
        _ ≤ ((Fintype.card ι : ℝ) ^ 2 * 2 ^ (k' + 1)) * (1 + K) * (1 + P) := by
            have hstep : K * P ≤ (1 + K) * (1 + P) := by nlinarith [hK0, hP0]
            have hc : (0 : ℝ) ≤ (Fintype.card ι : ℝ) ^ 2 := by positivity
            have hp2 : (0 : ℝ) ≤ (2 : ℝ) ^ (k' + 1) := by positivity
            calc (Fintype.card ι : ℝ) ^ 2 * ((2 : ℝ) ^ (k' + 1) * (K * P))
                ≤ (Fintype.card ι : ℝ) ^ 2 * ((2 : ℝ) ^ (k' + 1) * ((1 + K) * (1 + P))) := by
                  refine mul_le_mul_of_nonneg_left ?_ hc
                  exact mul_le_mul_of_nonneg_left hstep hp2
              _ = ((Fintype.card ι : ℝ) ^ 2 * 2 ^ (k' + 1)) * (1 + K) * (1 + P) := by ring
    · -- `ι` is empty and `k = k' + 1 ≥ 1`: there is no `l : Fin (k'+1) → ι`
      exact absurd (show Nonempty ι from ⟨l ⟨0, by omega⟩⟩) hι

end Work.Diff.STE.Lead.Gal
