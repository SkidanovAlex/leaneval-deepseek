import Mathlib
import Submission.Work.Main.defs
import Submission.Work.Main.crt.Pcr_inj
import Submission.Work.Main.crt.Pcr_lt
import Submission.Work.Main.crt.Pinv_spec
import Submission.Work.Main.crt.subIdx_Pcr
import Submission.Work.DFT.phaseLin

/-!
# The Agarwal–Cooley reindexing identity for the cyclic convolution

`Work.Main.Pcr ss : ℕ → ℕ` embeds the multi-index `(m % s₁, …, m % s_d)` of `m < ∏ss` as its
flat lexicographic ("mixed-radix") index, and `Work.Main.Pinv ss` is its inverse on `[0, ∏ss)`
(`Pinv_spec`).  `HvdH.subIdx ss j k` is the flat index of the componentwise difference of the
multi-indices of `j` and `k`; on the flat side it corresponds to the *cyclic* subtraction
`m ↦ (m + ∏ss - ·) % ∏ss` of the arguments (`crt.subIdx_Pcr`).

This file records the resulting statement at the level of sums: for `m < ∏ss` and arbitrary
`F G : ℕ → ℂ`,

  `∑ k < ∏ss, F (Pinv ss k) · G (Pinv ss (subIdx ss (Pcr ss m) k))
       = ∑ i < ∏ss, F i · G ((m + ∏ss - i) % ∏ss)`,

i.e. the flat index `k` of the cyclic convolution is the CRT image of `Pinv ss k`, so that the
convolution sum indexed by `k` becomes the ordinary index sum with the cyclic difference.

## Ingredients

* `crt.Pinv_spec` (imported): for `k < ∏ss`, `Pinv ss k < ∏ss` and `Pcr ss (Pinv ss k) = k`;
* `crt.Pcr_inj` (imported): `Pcr ss` is injective on `[0, ∏ss)`, giving the converse
  `Pinv ss (Pcr ss k) = k` (`Pinv_Pcr` below);
* `crt.subIdx_Pcr` (imported): `subIdx` on flat indices is cyclic subtraction of arguments;
* `Finset.sum_nbij'`: the reindexing `k ↦ Pinv ss k` of the sum, with inverse `i ↦ Pcr ss i`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Main.conv

open Work.Main

/-- `Pinv` restricted to `[0, ∏ss)` lands in `[0, ∏ss)`. -/
lemma Pinv_lt_prod {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime) (hpos : ∀ s ∈ ss, 0 < s)
    {k : ℕ} (hk : k < ss.prod) : Pinv ss k < ss.prod :=
  (crt.Pinv_spec hcop hpos hk).1

/-- `Pcr` is a left inverse of `Pinv` on `[0, ∏ss)`. -/
lemma Pcr_Pinv {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime) (hpos : ∀ s ∈ ss, 0 < s)
    {k : ℕ} (hk : k < ss.prod) : Pcr ss (Pinv ss k) = k :=
  (crt.Pinv_spec hcop hpos hk).2

/-- `Pinv` is a left inverse of `Pcr` on `[0, ∏ss)`: both `Pinv ss (Pcr ss k)` and `k` are
preimages of `Pcr ss k` under the injective `Pcr ss`. -/
lemma Pinv_Pcr {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime) (hpos : ∀ s ∈ ss, 0 < s)
    {k : ℕ} (hk : k < ss.prod) : Pinv ss (Pcr ss k) = k :=
  crt.Pcr_inj hcop hpos (Pinv_lt_prod hcop hpos (crt.Pcr_lt hpos k)) hk
    (Pcr_Pinv hcop hpos (crt.Pcr_lt hpos k))

/-- `subIdx` of the flat index `Pcr ss m` with `k` is the flat index of the cyclic difference
`(m + ∏ss - Pinv ss k) % ∏ss` of the two arguments. -/
lemma subIdx_Pcr_Pinv {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime)
    (hpos : ∀ s ∈ ss, 0 < s) {m k : ℕ} (hm : m < ss.prod) (hk : k < ss.prod) :
    HvdH.subIdx ss (Pcr ss m) k = Pcr ss ((m + ss.prod - Pinv ss k) % ss.prod) := by
  conv_lhs => rw [← Pcr_Pinv hcop hpos hk]
  exact crt.subIdx_Pcr hcop hpos hm (Pinv_lt_prod hcop hpos hk)

/-- **The reindexing of the cyclic convolution sum.** For pairwise coprime positive moduli `ss`
and `m < ∏ss`, the sum indexed by the flat CRT index `k` -- whose summands are read through
`Pinv ss` -- is the ordinary index sum with the cyclic difference `(m + ∏ss - i) % ∏ss`:
the substitution `i = Pinv ss k` is a bijection of `[0, ∏ss)` (with inverse `Pcr ss`). -/
theorem sum_convC_reindex {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime)
    (hpos : ∀ s ∈ ss, 0 < s) {m : ℕ} (hm : m < ss.prod) (F G : ℕ → ℂ) :
    (∑ k : Fin ss.prod, F (Work.Main.Pinv ss k) * G (Work.Main.Pinv ss (HvdH.subIdx ss (Work.Main.Pcr ss m) k)))
      = ∑ i ∈ Finset.range ss.prod, F i * G ((m + ss.prod - i) % ss.prod) := by
  have hPpos : 0 < ss.prod := List.prod_pos hpos
  rw [Fin.sum_univ_eq_sum_range
    (fun k => F (Pinv ss k) * G (Pinv ss (HvdH.subIdx ss (Pcr ss m) k))) ss.prod]
  refine Finset.sum_nbij' (fun k => Pinv ss k) (fun i => Pcr ss i) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    exact Finset.mem_range.mpr (Pinv_lt_prod hcop hpos (Finset.mem_range.mp ha))
  · intro a _
    exact Finset.mem_range.mpr (crt.Pcr_lt hpos a)
  · intro a ha
    exact Pcr_Pinv hcop hpos (Finset.mem_range.mp ha)
  · intro a ha
    exact Pinv_Pcr hcop hpos (Finset.mem_range.mp ha)
  · intro a ha
    have ha' : a < ss.prod := Finset.mem_range.mp ha
    have h1 : Pinv ss (HvdH.subIdx ss (Pcr ss m) a)
        = (m + ss.prod - Pinv ss a) % ss.prod := by
      rw [subIdx_Pcr_Pinv hcop hpos hm ha', Pinv_Pcr hcop hpos (Nat.mod_lt _ hPpos)]
    rw [h1]

end Work.Main.conv
