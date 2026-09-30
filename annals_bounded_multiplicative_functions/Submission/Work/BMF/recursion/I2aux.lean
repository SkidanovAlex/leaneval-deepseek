import Mathlib
import Submission.Work.BMF.recursion.Defs
import Submission.Work.BMF.recursion.I1I2Defs
import Submission.Work.BMF.recursion.MomVec
import Submission.Work.BMF.recursion.card_sub_eq_sum_fiber
import Submission.Work.BMF.recursion.sum_fiber_sq_shift_le
import Submission.Vinogradov.Core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary splitting lemmas for the head/tail decomposition of the recursion

A tuple `x` of length `S` splits into its head `hdT hkS x` (first `k` coordinates) and its
tail `tlT hkS x` (last `S - k` coordinates), and `zipT hkS` reassembles it.  The moment
vector splits accordingly (`powerSums_hdT_tlT`), the head-distinctness and tail-congruence
conditions transfer (`hdT_HDp`, `tlT_Tails`), and a tail tuple is determined by its
`U`-tuple `uOf p t` (`uOf_inj`, `uOf_sub`).
-/

set_option autoImplicit false

namespace Work.BMF.recursion

open Finset
open scoped BigOperators

noncomputable section

/-- The bijection `Fin k ⊕ Fin (S-k) ≃ Fin S` underlying the head/tail split. -/
def splitEquiv {k S : ℕ} (hkS : k ≤ S) : Fin k ⊕ Fin (S - k) ≃ Fin S :=
  finSumFinEquiv.trans (finCongr (by omega))

lemma splitEquiv_inl {k S : ℕ} (hkS : k ≤ S) (i : Fin k) :
    splitEquiv hkS (Sum.inl i) = hIdx hkS i := by
  apply Fin.ext
  simp [splitEquiv, finSumFinEquiv, hIdx, Fin.castAdd]

lemma splitEquiv_inr {k S : ℕ} (hkS : k ≤ S) (r : Fin (S - k)) :
    splitEquiv hkS (Sum.inr r) = tIdx hkS r := by
  apply Fin.ext
  simp [splitEquiv, finSumFinEquiv, tIdx, Fin.natAdd]

/-- The head/tail sum split. -/
theorem sum_hIdx_tIdx {k S : ℕ} {M : Type*} [AddCommMonoid M] (hkS : k ≤ S) (f : Fin S → M) :
    (∑ i : Fin S, f i)
      = (∑ i : Fin k, f (hIdx hkS i)) + (∑ r : Fin (S - k), f (tIdx hkS r)) := by
  classical
  rw [← Equiv.sum_comp (splitEquiv hkS) f, Fintype.sum_sum_type]
  have h₁ : (∑ i : Fin k, f (splitEquiv hkS (Sum.inl i))) = ∑ i : Fin k, f (hIdx hkS i) :=
    Finset.sum_congr rfl (fun i _ => by rw [splitEquiv_inl])
  have h₂ : (∑ r : Fin (S - k), f (splitEquiv hkS (Sum.inr r)))
      = ∑ r : Fin (S - k), f (tIdx hkS r) :=
    Finset.sum_congr rfl (fun r _ => by rw [splitEquiv_inr])
  rw [h₁, h₂]

/-- The moment vector of a tuple splits into the moment vectors of its head and its tail. -/
theorem powerSums_hdT_tlT {k S Q : ℕ} (hkS : k ≤ S) (x : Tup S Q) :
    Submission.Vinogradov.powerSums k x
      = Submission.Vinogradov.powerSums k (hdT hkS x) + Submission.Vinogradov.powerSums k (tlT hkS x) := by
  funext j
  simp only [Submission.Vinogradov.powerSums, Pi.add_apply, hdT, tlT]
  rw [sum_hIdx_tIdx hkS (fun i : Fin S => (x i).1 ^ j.val)]
  push_cast
  ring

/-- Reassembling a tuple from its head and tail gives back the tuple. -/
private theorem zipT_hdT_tlT {k S Q : ℕ} (hkS : k ≤ S) (x : Tup S Q) :
    zipT hkS (hdT hkS x, tlT hkS x) = x := by
  funext i
  rw [zipT]
  by_cases h : i.1 < k
  · rw [dif_pos h]
    exact congrArg x (Fin.ext rfl)
  · rw [dif_neg h]
    refine congrArg x (Fin.ext ?_)
    simp only [tIdx]
    omega

/-- The head-distinctness condition transfers to the head. -/
theorem hdT_HDp {k S Q p : ℕ} (hkS : k ≤ S) (x : Tup S Q) :
    HDp p k hkS x ↔ HDp p k (le_refl k) (hdT hkS x) := by
  simp only [HDp]
  have e : ∀ i : Fin k, (hdT hkS x) (hIdx (le_refl k) i) = x (hIdx hkS i) := by
    intro i
    have hii : hIdx (le_refl k) i = i := Fin.ext rfl
    rw [hii]
    rfl
  constructor
  · intro h i j hij
    rw [e i, e j]
    exact h i j hij
  · intro h i j hij
    have h' := h i j hij
    rw [e i, e j] at h'
    exact h'

/-- The tail-congruence condition transfers to the tail. -/
theorem tlT_Tails {k S Q p y : ℕ} (hkS : k ≤ S) (x : Tup S Q) :
    TailEq p hkS y x ↔ Tails p y (tlT hkS x) := Iff.rfl

/-- Membership in `i2Set` is the conjunction of the head and tail conditions. -/
theorem mem_i2Set_iff {k S Q p y : ℕ} (hkS : k ≤ S) (x : Tup S Q) :
    x ∈ i2Set S k Q p y hkS ↔ hdT hkS x ∈ Hset p k Q ∧ tlT hkS x ∈ Tset p y (S - k) Q := by
  simp only [i2Set, i1Set, Hset, Tset, Tails, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact ⟨(hdT_HDp hkS x).mp h.1, (tlT_Tails hkS x).mp h.2⟩
  · intro h
    exact ⟨(hdT_HDp hkS x).mpr h.1, (tlT_Tails hkS x).mpr h.2⟩

/-- The integer identity `(t r) - y = p * uOf p t r` for a tail tuple. -/
theorem uOf_sub {s Q p y : ℕ} (hy : y < p) {t : Tup s Q} (ht : Tails p y t) (r : Fin s) :
    ((t r).1 : ℤ) - (y : ℤ) = (p : ℤ) * (uOf p t r : ℤ) := by
  have hmod : (t r).1 % p = y := by
    rw [ht r, Nat.mod_eq_of_lt hy]
  have hcomp : p * ((t r).1 / p) + y = (t r).1 := by
    have h := Nat.div_add_mod (t r).1 p
    rwa [hmod] at h
  have hcast : ((t r).1 : ℤ) = (y : ℤ) + (p : ℤ) * (((t r).1 / p : ℕ) : ℤ) := by
    have hnat : ((t r).1 : ℤ) = ((p * ((t r).1 / p) + y : ℕ) : ℤ) := by rw [hcomp]
    rw [hnat]; push_cast; ring
  rw [uOf, hcast]
  ring

/-- Two tail tuples with the same `U`-tuple are equal. -/
theorem uOf_inj {s Q p y : ℕ} (hy : y < p) {t t' : Tup s Q}
    (ht : Tails p y t) (ht' : Tails p y t') (h : uOf p t = uOf p t') : t = t' := by
  funext r
  apply Subtype.ext
  have h1 := uOf_sub hy ht r
  have h2 := uOf_sub hy ht' r
  rw [h] at h1
  have key : ((t r).1 : ℤ) = ((t' r).1 : ℤ) := by omega
  exact_mod_cast key


/-! ## Range shifting and the diagonal domination -/

/-- The shift `u ↦ u + 1`, from `[0,X]`-tuples to `[1,X+1]`-tuples. -/
def shU {s X : ℕ} (u : UTup s X) : Tup s (X + 1) :=
  fun r => ⟨(u r).1 + 1, Finset.mem_Icc.mpr
    ⟨by omega, by have := (Finset.mem_Icc.mp (u r).2).2; omega⟩⟩

lemma shU_injective {s X : ℕ} : Function.Injective (shU (s := s) (X := X)) := by
  intro u v h
  funext r
  apply Subtype.ext
  have h1 : (shU u r).1 = (shU v r).1 := by rw [congrFun h r]
  simp only [shU] at h1
  omega

/-- Binomial expansion: if all moments of degrees `1, …, k` of `u` and `v` agree, then so do
the moments of the shifted tuples `r ↦ u r + 1`. -/
lemma sum_add_one_pow_eq {s k : ℕ} (u v : Fin s → ℕ)
    (h : ∀ l, 1 ≤ l → l ≤ k → ∑ r, (u r : ℤ) ^ l = ∑ r, (v r : ℤ) ^ l)
    (j : ℕ) (hj : j ≤ k) :
    ∑ r, ((u r : ℤ) + 1) ^ j = ∑ r, ((v r : ℤ) + 1) ^ j := by
  have key : ∀ x : ℕ, ((x : ℤ) + 1) ^ j
      = ∑ l ∈ Finset.range (j + 1), (x : ℤ) ^ l * (j.choose l : ℤ) := by
    intro x
    rw [add_pow]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [one_pow, mul_one]
  have hstep : ∀ w : Fin s → ℕ,
      ∑ r, ((w r : ℤ) + 1) ^ j
        = ∑ l ∈ Finset.range (j + 1), (j.choose l : ℤ) * ∑ r, (w r : ℤ) ^ l := by
    intro w
    calc ∑ r, ((w r : ℤ) + 1) ^ j
        = ∑ r, ∑ l ∈ Finset.range (j + 1), (w r : ℤ) ^ l * (j.choose l : ℤ) := by
          exact Finset.sum_congr rfl (fun r _ => key (w r))
      _ = ∑ l ∈ Finset.range (j + 1), ∑ r, (w r : ℤ) ^ l * (j.choose l : ℤ) :=
          Finset.sum_comm
      _ = ∑ l ∈ Finset.range (j + 1), (j.choose l : ℤ) * ∑ r, (w r : ℤ) ^ l := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun r _ => by ring)
  rw [hstep u, hstep v]
  refine Finset.sum_congr rfl (fun l hl => ?_)
  rcases Nat.eq_zero_or_pos l with h0 | hpos
  · subst h0
    simp
  · have hlk : l ≤ k := by have := Finset.mem_range.mp hl; omega
    rw [h l hpos hlk]

/-- Moment matching is preserved by the shift `u ↦ u + 1`. -/
lemma powerSums_shU_eq {s X k : ℕ} {u v : UTup s X} (h : momVec k u = momVec k v) :
    Submission.Vinogradov.powerSums k (shU u) = Submission.Vinogradov.powerSums k (shU v) := by
  funext j
  have h' : ∀ l, 1 ≤ l → l ≤ k → ∑ r, ((u r).1 : ℤ) ^ l = ∑ r, ((v r).1 : ℤ) ^ l := by
    intro l hl1 hlk
    have := congrFun h ⟨l - 1, by omega⟩
    simpa only [momVec, Nat.sub_add_cancel hl1] using this
  have hz := sum_add_one_pow_eq (fun r => (u r).1) (fun r => (v r).1) h' j.val (by have := j.isLt; omega)
  simp only [Submission.Vinogradov.powerSums, shU]
  push_cast
  exact hz

/-- The number of diagonal pairs of `[0,X]`-tuples (equal moment vectors) is at most
`J s k (X+1)`. -/
theorem momVec_diag_le_J (s k X : ℕ) :
    (((Finset.univ : Finset (UTup s X × UTup s X)).filter
        (fun q => momVec k q.1 = momVec k q.2)).card : ℝ)
      ≤ LeanEval.NumberTheory.VinogradovMeanValue.J s k (X + 1) := by
  rw [Submission.Vinogradov.J_eq_filter_card]
  have hcard : (((Finset.univ : Finset (UTup s X × UTup s X)).filter
        (fun q => momVec k q.1 = momVec k q.2)).card : ℕ)
      ≤ ((Finset.univ : Finset (Submission.Vinogradov.PairSpace s (X + 1))).filter
        (fun p => Submission.Vinogradov.Matches s k (X + 1) p)).card := by
    refine Finset.card_le_card_of_injOn (fun q : UTup s X × UTup s X => (shU q.1, shU q.2)) ?_ ?_
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact (Submission.Vinogradov.powerSums_eq_iff_matches _ _).mp (powerSums_shU_eq hq)
    · intro a _ b _ hab
      have h1 : shU a.1 = shU b.1 := congrArg Prod.fst hab
      have h2 : shU a.2 = shU b.2 := congrArg Prod.snd hab
      exact Prod.ext (shU_injective h1) (shU_injective h2)
  exact_mod_cast hcard

/-- `J s k ·` is monotone in the range parameter. -/
theorem J_mono_range {s k X Y : ℕ} (h : X ≤ Y) :
    LeanEval.NumberTheory.VinogradovMeanValue.J s k X
      ≤ LeanEval.NumberTheory.VinogradovMeanValue.J s k Y := by
  rw [Submission.Vinogradov.J_eq_filter_card, Submission.Vinogradov.J_eq_filter_card]
  let emb : Tup s X → Tup s Y := fun x i =>
    ⟨(x i).1, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (x i).2).1,
      le_trans (Finset.mem_Icc.mp (x i).2).2 h⟩⟩
  have hemb : Function.Injective emb := by
    intro x y hxy
    funext i
    apply Subtype.ext
    have := congrFun hxy i
    simpa [emb] using congrArg Subtype.val this
  have hcard : (((Finset.univ : Finset (Submission.Vinogradov.PairSpace s X)).filter
        (fun p => Submission.Vinogradov.Matches s k X p)).card : ℕ)
      ≤ ((Finset.univ : Finset (Submission.Vinogradov.PairSpace s Y)).filter
        (fun p => Submission.Vinogradov.Matches s k Y p)).card := by
    refine Finset.card_le_card_of_injOn (fun p : PairSpace s X => (emb p.1, emb p.2)) ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      intro j hj
      simpa [emb] using hp j hj
    · intro a _ b _ hab
      refine Prod.ext (hemb ?_) (hemb ?_)
      · exact congrArg Prod.fst hab
      · exact congrArg Prod.snd hab
  exact_mod_cast hcard

/-- **Zero difference dominates** for the moment vectors of `[0,X]`-tuples: the number of pairs
with a prescribed moment difference is at most the number of pairs with difference `0`. -/
theorem momVec_fiber_le_diag (s k X : ℕ) (d : Fin k → ℤ) :
    ((Finset.univ : Finset (UTup s X × UTup s X)).filter
        (fun q => momVec k q.2 - momVec k q.1 = d)).card
      ≤ ((Finset.univ : Finset (UTup s X × UTup s X)).filter
        (fun q => momVec k q.1 = momVec k q.2)).card := by
  classical
  set f : UTup s X → (Fin k → ℤ) := fun u => momVec k u with hf
  set W : Finset (Fin k → ℤ) := (Finset.univ : Finset (UTup s X)).image f with hW
  set a : (Fin k → ℤ) → ℕ :=
    fun v => ((Finset.univ : Finset (UTup s X)).filter (fun x => f x = v)).card with ha
  have hswap : ((Finset.univ : Finset (UTup s X × UTup s X)).filter
        (fun q => f q.2 - f q.1 = d)).card
      = ((Finset.univ : Finset (UTup s X × UTup s X)).filter
        (fun q => f q.1 - f q.2 = d)).card := by
    refine Finset.card_nbij (fun q : UTup s X × UTup s X => (q.2, q.1)) ?_ ?_ ?_
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact hq
    · intro x _ y _ hxy
      exact Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy)
    · intro b hb
      refine ⟨(b.2, b.1), ?_, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact hb
  have hB : ((Finset.univ : Finset (UTup s X × UTup s X)).filter
        (fun q => f q.1 - f q.2 = d)).card = ∑ v ∈ W, a v * a (v + d) := by
    simpa only [ha, hW, hf] using card_sub_eq_sum_fiber f d
  have hC : (∑ v ∈ W, a (v + d) ^ 2) ≤ ∑ v ∈ W, a v ^ 2 := by
    simpa only [ha, hW, hf] using sum_fiber_sq_shift_le f d
  have h0 : ((Finset.univ : Finset (UTup s X × UTup s X)).filter
        (fun q => f q.1 = f q.2)).card = ∑ v ∈ W, a v ^ 2 := by
    have hset : ((Finset.univ : Finset (UTup s X × UTup s X)).filter
        (fun q => f q.1 = f q.2))
        = ((Finset.univ : Finset (UTup s X × UTup s X)).filter
        (fun q => f q.1 - f q.2 = 0)) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_eq_zero]
    rw [hset]
    have := card_sub_eq_sum_fiber f (0 : Fin k → ℤ)
    simpa only [ha, hW, hf, add_zero, pow_two] using this
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (s := W) (fun v => a v) (fun v => a (v + d))
  have hstep : (((Finset.univ : Finset (UTup s X × UTup s X)).filter
        (fun q => f q.2 - f q.1 = d)).card) ^ 2
      ≤ (((Finset.univ : Finset (UTup s X × UTup s X)).filter
        (fun q => f q.1 = f q.2)).card) ^ 2 := by
    rw [hswap, hB, h0]
    calc (∑ v ∈ W, a v * a (v + d)) ^ 2
        ≤ (∑ v ∈ W, a v ^ 2) * (∑ v ∈ W, a (v + d) ^ 2) := hCS
      _ ≤ (∑ v ∈ W, a v ^ 2) * (∑ v ∈ W, a v ^ 2) := Nat.mul_le_mul_left _ hC
      _ = (∑ v ∈ W, a v ^ 2) ^ 2 := by rw [pow_two]
  exact (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hstep


/-! ## The `U`-tuple of a tuple and the key shifted identity -/

/-- The `U`-tuple attached to a (full-length) tuple `x`: `r ↦ (x (tIdx r)) / p`. -/
def uTupOf {k S Q : ℕ} (p : ℕ) (hkS : k ≤ S) (x : Tup S Q) : UTup (S - k) (Q / p) :=
  fun r => ⟨(x (tIdx hkS r)).1 / p, Finset.mem_Icc.mpr
    ⟨Nat.zero_le _, Nat.div_le_div_right (Finset.mem_Icc.mp (x (tIdx hkS r)).2).2⟩⟩

lemma uTupOf_apply {k S Q p : ℕ} (hkS : k ≤ S) (x : Tup S Q) (r : Fin (S - k)) :
    ((uTupOf p hkS x r : ℕ)) = (x (tIdx hkS r)).1 / p := rfl

/-- On `i2Set`, a tuple is determined by its head and its `U`-tuple. -/
lemma uTupOf_injOn {k S Q p y : ℕ} (hkS : k ≤ S) (hy : y < p) :
    ∀ x ∈ i2Set S k Q p y hkS, ∀ w ∈ i2Set S k Q p y hkS,
      hdT hkS x = hdT hkS w → uTupOf p hkS x = uTupOf p hkS w → x = w := by
  classical
  intro x hx w hw h1 h2
  have hxT : Tails p y (tlT hkS x) :=
    Finset.mem_filter.mp ((mem_i2Set_iff hkS x).mp hx).2 |>.2
  have hwT : Tails p y (tlT hkS w) :=
    Finset.mem_filter.mp ((mem_i2Set_iff hkS w).mp hw).2 |>.2
  have h3 : uOf p (tlT hkS x) = uOf p (tlT hkS w) := by
    funext r
    exact congrArg Subtype.val (congrFun h2 r)
  have h4 : tlT hkS x = tlT hkS w := uOf_inj hy hxT hwT h3
  rw [← zipT_hdT_tlT hkS x, ← zipT_hdT_tlT hkS w, h1, h4]

/-- **Translation invariance of moments.**  If two tuples have the same moments of degrees
`≤ k`, then they have the same shifted moments with respect to any integer shift `z`. -/
lemma sum_shift_eq {S X k : ℕ} (x x' : Tup S X) (z : ℤ)
    (h : ∀ j ≤ k, ∑ i, ((x i).1 : ℤ) ^ j = ∑ i, ((x' i).1 : ℤ) ^ j) :
    ∀ j ≤ k, ∑ i, (((x i).1 : ℤ) - z) ^ j = ∑ i, (((x' i).1 : ℤ) - z) ^ j := by
  intro j hj
  have key : ∀ a : ℤ, (a - z) ^ j
      = ∑ l ∈ Finset.range (j + 1), a ^ l * (-z) ^ (j - l) * (j.choose l : ℤ) := by
    intro a
    have h' : a - z = a + (-z) := by ring
    rw [h', add_pow]
  have hstep : ∀ w : Tup S X,
      ∑ i, (((w i).1 : ℤ) - z) ^ j
        = ∑ l ∈ Finset.range (j + 1),
            (j.choose l : ℤ) * (-z) ^ (j - l) * ∑ i, ((w i).1 : ℤ) ^ l := by
    intro w
    calc ∑ i, (((w i).1 : ℤ) - z) ^ j
        = ∑ i, ∑ l ∈ Finset.range (j + 1),
            ((w i).1 : ℤ) ^ l * (-z) ^ (j - l) * (j.choose l : ℤ) :=
          Finset.sum_congr rfl (fun i _ => key _)
      _ = ∑ l ∈ Finset.range (j + 1), ∑ i,
            ((w i).1 : ℤ) ^ l * (-z) ^ (j - l) * (j.choose l : ℤ) := Finset.sum_comm
      _ = ∑ l ∈ Finset.range (j + 1),
            (j.choose l : ℤ) * (-z) ^ (j - l) * ∑ i, ((w i).1 : ℤ) ^ l := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hstep x, hstep x']
  refine Finset.sum_congr rfl (fun l hl => ?_)
  rw [h l (by have := Finset.mem_range.mp hl; omega)]

/-- **The key shifted identity.**  If two tuples of `i2Set` have equal moment vectors, then
their shifted head moments differ by `p^(j+1)` times the difference of the `U`-moments. -/
lemma key_identity {k S Q p y : ℕ} (hkS : k ≤ S) (hy : y < p) {x w : Tup S Q}
    (hx : x ∈ i2Set S k Q p y hkS) (hw : w ∈ i2Set S k Q p y hkS)
    (h : Submission.Vinogradov.powerSums k x = Submission.Vinogradov.powerSums k w) :
    ∀ j : Fin k,
      (p : ℤ) ^ (j.1 + 1) * (momVec k (uTupOf p hkS w) j - momVec k (uTupOf p hkS x) j)
        = hMom k y (hdT hkS x) j - hMom k y (hdT hkS w) j := by
  classical
  intro j
  have hsh := sum_shift_eq (k := k) x w (y : ℤ) (fun j' hj' => by
      have hc := congrFun h ⟨j', Nat.lt_succ_of_le hj'⟩
      simp only [Submission.Vinogradov.powerSums] at hc
      simpa only [Nat.cast_sum, Nat.cast_pow] using hc) (j.1 + 1) (Nat.succ_le_of_lt j.isLt)
  have hxT : Tails p y (tlT hkS x) :=
    Finset.mem_filter.mp ((mem_i2Set_iff hkS x).mp hx).2 |>.2
  have hwT : Tails p y (tlT hkS w) :=
    Finset.mem_filter.mp ((mem_i2Set_iff hkS w).mp hw).2 |>.2
  have hxt : ∀ r : Fin (S - k),
      (((x (tIdx hkS r)).1 : ℤ) - (y : ℤ)) = (p : ℤ) * (uTupOf p hkS x r : ℤ) := by
    intro r
    simpa only [uTupOf, uOf, tlT] using uOf_sub hy hxT r
  have hwt : ∀ r : Fin (S - k),
      (((w (tIdx hkS r)).1 : ℤ) - (y : ℤ)) = (p : ℤ) * (uTupOf p hkS w r : ℤ) := by
    intro r
    simpa only [uTupOf, uOf, tlT] using uOf_sub hy hwT r
  rw [sum_hIdx_tIdx hkS (fun i : Fin S => (((x i).1 : ℤ) - (y : ℤ)) ^ (j.1 + 1)),
    sum_hIdx_tIdx hkS (fun i : Fin S => (((w i).1 : ℤ) - (y : ℤ)) ^ (j.1 + 1))] at hsh
  have hxs : (∑ r : Fin (S - k), (((x (tIdx hkS r)).1 : ℤ) - (y : ℤ)) ^ (j.1 + 1))
      = (p : ℤ) ^ (j.1 + 1) * momVec k (uTupOf p hkS x) j := by
    simp only [momVec, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun r _ => by rw [hxt r, mul_pow])
  have hws : (∑ r : Fin (S - k), (((w (tIdx hkS r)).1 : ℤ) - (y : ℤ)) ^ (j.1 + 1))
      = (p : ℤ) ^ (j.1 + 1) * momVec k (uTupOf p hkS w) j := by
    simp only [momVec, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun r _ => by rw [hwt r, mul_pow])
  rw [hxs, hws] at hsh
  simp only [hMom, hdT]
  linarith [hsh]

end

end Work.BMF.recursion
