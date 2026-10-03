import Mathlib
import Submission.Work.OROneRel.sigma_hits
import Submission.Work.OROneRel.le_of_card_image_Icc
import Submission.Work.OROneRel.interval_connected

set_option linter.unusedVariables false

namespace Work.OROneRel

/-!
# Reachability of the levels of a closed ±A, ±B walk

Let `A, B ≥ 2` be coprime (witnessed by a Bézout relation `p * A + q * B = 1`) and let
`steps` be a closed walk (`steps.sum = 0`) whose entries are all in `{A, -A, B, -B}`, such
that the number of `+A` steps differs from the number of `-A` steps.  If `lo` bounds the
partial sums from below and `hi` from above, then every integer `j ∈ [lo, hi]` is reachable
from `0` by `±A`/`±B` steps that never leave `[lo, hi]`.

The proof has two independents halves.

* **Range bound** (`band_le`).  Assigning to each step `s` the sign
  `sgf A B s = +1` for `s ∈ {A, -B}` and `-1` for `s ∈ {-A, B}`, one shows
  `s ≡ A * sgf A B s (mod A+B)`.  Hence the partial sums `S t` and the running sign sums
  `σ t` satisfy `S t ≡ A * σ t (mod A+B)`, and `σ` changes by `±1` at each step, so by
  `sigma_hits` it attains every value between `0` and its total `σ length`.
  The total is `netA - netB`, which by the closed-walk relation `netA * A + netB * B = 0`
  and coprimality is a nonzero multiple of `A + B`; therefore `σ` attains
  `0, 1, …, A+B-1`, and the corresponding partial sums are `A+B` distinct integers whose
  residues mod `A+B` are distinct.  A pigeonhole argument (`le_of_card_image_Icc`) gives
  `hi - lo ≥ A + B - 1`.
* **Interval connectivity** (`interval_connected`): on an interval of length at least
  `A + B - 2` the moves `±A, ±B` connect every pair of points.

Putting the two together finishes the proof.
-/

/-- The number of occurrences of `c` in `l`, as an integer. -/
def cnt (c : ℤ) (l : List ℤ) : ℤ := ((l.filter (fun s => s = c)).length : ℤ)

lemma cnt_cons (c x : ℤ) (t : List ℤ) :
    cnt c (x :: t) = cnt c t + (if x = c then 1 else 0) := by
  unfold cnt; rw [List.filter_cons]; by_cases h : x = c <;> simp [h]

/-- The signed count of `A` and `-A` steps is the difference of the two cardinalities. -/
lemma sum_map_ind (A : ℤ) (hA : A ≠ 0) (l : List ℤ) :
    (l.map (fun s => if s = A then (1:ℤ) else if s = -A then -1 else 0)).sum
      = cnt A l - cnt (-A) l := by
  have hA' : A ≠ -A := by omega
  have hA'' : -A ≠ A := by omega
  induction l with
  | nil => simp [cnt]
  | cons x t ih =>
    rw [List.map_cons, List.sum_cons, ih, cnt_cons, cnt_cons]
    by_cases h1 : x = A
    · subst h1; simp [hA']; ring
    · by_cases h2 : x = -A
      · subst h2; simp [hA'']; ring
      · simp [h1, h2]

lemma map_sub_sum (l : List ℤ) (f g : ℤ → ℤ) :
    (l.map (fun s => f s - g s)).sum = (l.map f).sum - (l.map g).sum := by
  have h : (fun s => f s - g s) = fun s => f s + (-1) * g s := by funext s; ring
  rw [h, List.sum_map_add, List.sum_map_mul_left]; ring

/-- Decompose the sum of a `±A, ±B` walk into its signed `A`-count and `B`-count. -/
lemma sum_eq_net (A B : ℤ) (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hAB : A ≠ B) (hAnB : A ≠ -B)
    (l : List ℤ) (hstep : ∀ s ∈ l, s = A ∨ s = -A ∨ s = B ∨ s = -B) :
    l.sum = A * (l.map (fun s => if s = A then (1:ℤ) else if s = -A then -1 else 0)).sum
          + B * (l.map (fun s => if s = B then (1:ℤ) else if s = -B then -1 else 0)).sum := by
  have hn1 : -A ≠ A := by omega
  have hn2 : -B ≠ B := by omega
  have hn3 : -A ≠ B := by omega
  have hn4 : -A ≠ -B := by omega
  have hn5 : B ≠ A := by omega
  have hn6 : B ≠ -A := by omega
  have hn7 : -B ≠ A := by omega
  have hn8 : -B ≠ -A := by omega
  induction l with
  | nil => simp
  | cons x t ih =>
    have hx := hstep x (by simp)
    have ht : ∀ s ∈ t, s = A ∨ s = -A ∨ s = B ∨ s = -B := fun s hs => hstep s (by simp [hs])
    rw [List.sum_cons, ih ht]
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    rcases hx with h|h|h|h <;>
      · subst h
        simp only [hAB, hAnB, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, if_true, if_false]
        ring

/-- The sign carried by a step: `+1` for `A` and `-B`, `-1` for `-A` and `B`. -/
def sgf (A B : ℤ) : ℤ → ℤ := fun s => (if s = A then (1:ℤ) else if s = -A then -1 else 0)
    - (if s = B then (1:ℤ) else if s = -B then -1 else 0)

lemma sg_isSign (A B : ℤ) (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hAB : A ≠ B) (hAnB : A ≠ -B)
    (s : ℤ) (hs : s = A ∨ s = -A ∨ s = B ∨ s = -B) : sgf A B s = 1 ∨ sgf A B s = -1 := by
  have hn1 : -A ≠ A := by omega
  have hn2 : -B ≠ B := by omega
  have hn3 : -A ≠ B := by omega
  have hn4 : -A ≠ -B := by omega
  have hn5 : B ≠ A := by omega
  have hn6 : B ≠ -A := by omega
  have hn7 : -B ≠ A := by omega
  have hn8 : -B ≠ -A := by omega
  rcases hs with h|h|h|h <;> subst h <;> unfold sgf <;>
    simp only [hAB, hAnB, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, if_true, if_false] <;>
    norm_num

lemma sg_mod (A B : ℤ) (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hAB : A ≠ B) (hAnB : A ≠ -B)
    (s : ℤ) (hs : s = A ∨ s = -A ∨ s = B ∨ s = -B) :
    s ≡ A * sgf A B s [ZMOD (A + B)] := by
  have hn1 : -A ≠ A := by omega
  have hn2 : -B ≠ B := by omega
  have hn3 : -A ≠ B := by omega
  have hn4 : -A ≠ -B := by omega
  have hn5 : B ≠ A := by omega
  have hn6 : B ≠ -A := by omega
  have hn7 : -B ≠ A := by omega
  have hn8 : -B ≠ -A := by omega
  rcases hs with h|h|h|h <;> subst h <;> unfold sgf <;>
    simp only [hAB, hAnB, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, if_true, if_false]
  · rw [Int.modEq_iff_dvd]; exact ⟨0, by ring⟩
  · rw [Int.modEq_iff_dvd]; exact ⟨0, by ring⟩
  · rw [Int.modEq_iff_dvd]; exact ⟨-1, by ring⟩
  · rw [Int.modEq_iff_dvd]; exact ⟨1, by ring⟩

lemma sum_mod (A B : ℤ) (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hAB : A ≠ B) (hAnB : A ≠ -B)
    (l : List ℤ) (hstep : ∀ s ∈ l, s = A ∨ s = -A ∨ s = B ∨ s = -B) :
    l.sum ≡ A * (l.map (sgf A B)).sum [ZMOD (A + B)] := by
  induction l with
  | nil => simp only [List.sum_nil, List.map_nil, mul_zero]; exact Int.ModEq.refl 0
  | cons x t ih =>
    have hx := hstep x (by simp)
    have ht : ∀ s ∈ t, s = A ∨ s = -A ∨ s = B ∨ s = -B := fun s hs => hstep s (by simp [hs])
    have ih' := ih ht
    have hxm := sg_mod A B hA0 hB0 hAB hAnB x hx
    rw [List.sum_cons, List.map_cons, List.sum_cons, mul_add]
    exact hxm.add ih'

lemma map_sg_sum (A B : ℤ) (l : List ℤ) :
    (l.map (sgf A B)).sum
      = (l.map (fun s => if s = A then (1:ℤ) else if s = -A then -1 else 0)).sum
        - (l.map (fun s => if s = B then (1:ℤ) else if s = -B then -1 else 0)).sum := by
  rw [show sgf A B = fun s => (if s = A then (1:ℤ) else if s = -A then -1 else 0)
        - (if s = B then (1:ℤ) else if s = -B then -1 else 0) from rfl]
  exact map_sub_sum l _ _

/-- The partial sums of `l` (with initial value `c`) all lie in `l.scanl (· + ·) c`. -/
lemma take_sum_mem_scanl (l : List ℤ) :
    ∀ (c : ℤ) (k : ℕ), c + (l.take k).sum ∈ l.scanl (fun a b => a + b) c := by
  induction l with
  | nil => intro c k; simp [List.scanl_nil]
  | cons x t ih =>
    intro c k
    rw [List.scanl_cons]
    cases k with
    | zero => simp
    | succ k =>
      rw [List.take_succ_cons, List.sum_cons, List.mem_cons]
      refine Or.inr ?_
      have := ih (c + x) k
      simpa [add_comm, add_left_comm, add_assoc] using this

lemma zero_mem_scanl (steps : List ℤ) : (0:ℤ) ∈ steps.scanl (fun a b => a + b) 0 := by
  cases steps with
  | nil => simp [List.scanl]
  | cons h t => rw [List.scanl_cons]; exact List.mem_cons_self ..

/-- **Range bound.** A closed `±A, ±B` walk in which the `+A` and `-A` steps occur a
different number of times has range at least `A + B - 2`. -/
lemma band_le {A B : ℤ} (hA : 2 ≤ A) (hB : 2 ≤ B)
    (hbez : ∃ p q : ℤ, p * A + q * B = 1)
    (steps : List ℤ) (hstep : ∀ s ∈ steps, s = A ∨ s = -A ∨ s = B ∨ s = -B)
    (hsum : steps.sum = 0)
    (hnet : (steps.filter (· = A)).length ≠ (steps.filter (· = -A)).length)
    (lo hi : ℤ) (hlo : ∀ l ∈ steps.scanl (fun a b => a + b) (0 : ℤ), lo ≤ l)
    (hhi : ∀ l ∈ steps.scanl (fun a b => a + b) (0 : ℤ), l ≤ hi) :
    A + B - 2 ≤ hi - lo := by
  classical
  have hA0 : A ≠ 0 := by omega
  have hB0 : B ≠ 0 := by omega
  have hAnB : A ≠ -B := by omega
  have hAB : A ≠ B := by
    rintro rfl
    obtain ⟨p, q, hpq⟩ := hbez
    have hdvd : A ∣ 1 := ⟨p + q, by linarith⟩
    have hle : A ≤ 1 := Int.le_of_dvd (by norm_num) hdvd
    omega
  have hC1 : (1:ℤ) ≤ A + B := by omega
  have hCpos : (0:ℤ) < A + B := by omega
  have hCne : A + B ≠ 0 := by omega
  set u : ℤ → ℤ := (fun s => if s = A then (1:ℤ) else if s = -A then -1 else 0) with hu
  set v : ℤ → ℤ := (fun s => if s = B then (1:ℤ) else if s = -B then -1 else 0) with hv
  have hnetA_eq : (steps.map u).sum = cnt A steps - cnt (-A) steps := by
    rw [hu]; exact sum_map_ind A hA0 steps
  have hnetA_ne : (steps.map u).sum ≠ 0 := by
    intro h
    apply hnet
    have h2 : cnt A steps = cnt (-A) steps := by linarith [hnetA_eq, h]
    have h3 : ((steps.filter (fun s => s = A)).length : ℤ)
        = ((steps.filter (fun s => s = -A)).length : ℤ) := by simpa [cnt] using h2
    exact Int.natCast_inj.mp h3
  have hsum_net : steps.sum = A * (steps.map u).sum + B * (steps.map v).sum := by
    rw [hu, hv]; exact sum_eq_net A B hA0 hB0 hAB hAnB steps hstep
  have hsigma_rel : (steps.map (sgf A B)).sum = (steps.map u).sum - (steps.map v).sum := by
    rw [hu, hv]; exact map_sg_sum A B steps
  have hsigma_ne : (steps.map (sgf A B)).sum ≠ 0 := by
    intro h0
    have heq : (steps.map u).sum = (steps.map v).sum := by linarith [hsigma_rel, h0]
    have h1 : A * (steps.map u).sum + B * (steps.map v).sum = 0 := by rw [← hsum_net, hsum]
    have hzero : (steps.map u).sum * (A + B) = 0 := by nlinarith [h1, heq]
    rcases mul_eq_zero.mp hzero with h | h
    · exact hnetA_ne h
    · exact absurd h hCne
  have hmod := sum_mod A B hA0 hB0 hAB hAnB steps hstep
  have hCm : (A + B) ∣ A * (steps.map (sgf A B)).sum := by
    have h0 : (0:ℤ) ≡ A * (steps.map (sgf A B)).sum [ZMOD (A + B)] := by
      rw [← hsum]; exact hmod
    simpa using (Int.modEq_iff_dvd.mp h0)
  have hCcop : IsCoprime (A + B) A := by
    obtain ⟨p, q, hpq⟩ := hbez
    exact ⟨q, p - q, by nlinarith [hpq]⟩
  have hCm' : (A + B) ∣ (steps.map (sgf A B)).sum * A := by rw [mul_comm]; exact hCm
  have hCdvd : (A + B) ∣ (steps.map (sgf A B)).sum := hCcop.dvd_of_dvd_mul_right hCm'
  obtain ⟨kk, hkk⟩ := hCdvd
  have hkle : A + B ≤ |(steps.map (sgf A B)).sum| := by
    rw [hkk, abs_mul, abs_of_nonneg (by omega : (0:ℤ) ≤ A + B)]
    have hkne : kk ≠ 0 := by intro h; exact hsigma_ne (by rw [hkk, h, mul_zero])
    have hone : (1:ℤ) ≤ |kk| := Int.one_le_abs hkne
    nlinarith [hone, hCpos]
  set eps : ℤ := if 0 ≤ (steps.map (sgf A B)).sum then 1 else -1 with heps
  have heps_sq : eps * eps = 1 := by rw [heps]; split <;> norm_num
  have hl1 : ∀ x ∈ steps.map (sgf A B), x = 1 ∨ x = -1 := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    exact sg_isSign A B hA0 hB0 hAB hAnB s (hstep s hs)
  have hrange : ∀ w : ℤ, 0 ≤ w → w ≤ (A + B) - 1 →
      ((0 ≤ eps * w ∧ eps * w ≤ (steps.map (sgf A B)).sum) ∨
       ((steps.map (sgf A B)).sum ≤ eps * w ∧ eps * w ≤ 0)) := by
    intro w hw0 hw1
    rw [heps]
    by_cases hpos : 0 ≤ (steps.map (sgf A B)).sum
    · rw [if_pos hpos]
      refine Or.inl ⟨by omega, ?_⟩
      simp only [one_mul]
      have hge : A + B ≤ (steps.map (sgf A B)).sum := by
        rw [abs_of_nonneg hpos] at hkle; exact hkle
      omega
    · rw [if_neg hpos]
      refine Or.inr ⟨?_, by omega⟩
      simp only [neg_mul, one_mul]
      have hlt : (steps.map (sgf A B)).sum < 0 := lt_of_not_ge hpos
      have hle : (steps.map (sgf A B)).sum ≤ -(A + B) := by
        rw [abs_of_neg hlt] at hkle; linarith
      omega
  let kw : ℤ → ℕ := fun w => if h : 0 ≤ w ∧ w ≤ (A + B) - 1 then
      Classical.choose (sigma_hits (steps.map (sgf A B)) hl1 (eps * w) (hrange w h.1 h.2))
      else 0
  let S : ℤ → ℤ := fun w => (steps.take (kw w)).sum
  have hkw : ∀ w (hw : 0 ≤ w ∧ w ≤ (A + B) - 1),
      ((steps.map (sgf A B)).take (kw w)).sum = eps * w := by
    intro w hw
    have h1 : kw w = Classical.choose
        (sigma_hits (steps.map (sgf A B)) hl1 (eps * w) (hrange w hw.1 hw.2)) := dif_pos hw
    rw [h1]
    exact (Classical.choose_spec
      (sigma_hits (steps.map (sgf A B)) hl1 (eps * w) (hrange w hw.1 hw.2))).2
  have hSmod : ∀ w (hw : 0 ≤ w ∧ w ≤ (A + B) - 1),
      S w ≡ A * (eps * w) [ZMOD (A + B)] := by
    intro w hw
    have hst : ∀ s ∈ steps.take (kw w), s = A ∨ s = -A ∨ s = B ∨ s = -B :=
      fun s hs => hstep s (List.mem_of_mem_take hs)
    have hm := sum_mod A B hA0 hB0 hAB hAnB (steps.take (kw w)) hst
    have htake : ((steps.take (kw w)).map (sgf A B)).sum = eps * w := by
      rw [List.map_take]; exact hkw w hw
    rw [htake] at hm
    exact hm
  have hhmem : ∀ w, 0 ≤ w → w ≤ (A + B) - 1 → lo ≤ S w ∧ S w ≤ hi := by
    intro w hw0 hw1
    have hmem : S w ∈ steps.scanl (fun a b => a + b) (0:ℤ) := by
      have h := take_sum_mem_scanl steps 0 (kw w)
      simpa [S] using h
    exact ⟨hlo (S w) hmem, hhi (S w) hmem⟩
  have hhinj : ∀ x y, 0 ≤ x → x ≤ (A + B) - 1 → 0 ≤ y → y ≤ (A + B) - 1 →
      S x = S y → x = y := by
    intro x y hx0 hx1 hy0 hy1 heq
    have hv : 0 ≤ x ∧ x ≤ (A + B) - 1 := ⟨hx0, hx1⟩
    have hw : 0 ≤ y ∧ y ≤ (A + B) - 1 := ⟨hy0, hy1⟩
    have hmx := hSmod x hv
    have hmy := hSmod y hw
    have heqm : S x ≡ S y [ZMOD (A + B)] := by rw [heq]
    have hbad : A * (eps * x) ≡ A * (eps * y) [ZMOD (A + B)] :=
      (hmx.symm.trans heqm).trans hmy
    have hwv : (A + B) ∣ A * eps * (y - x) := by
      have h := Int.modEq_iff_dvd.mp hbad
      have he : A * (eps * y) - A * (eps * x) = A * eps * (y - x) := by ring
      rwa [he] at h
    have hdvdA : (A + B) ∣ A * (y - x) := by
      obtain ⟨c, hc⟩ := hwv
      have hcc : eps * (A * eps * (y - x)) = A * (y - x) := by
        have h2 : eps * (A * eps * (y - x)) = A * (eps * eps) * (y - x) := by ring
        rw [h2, heps_sq, mul_one]
      refine ⟨eps * c, ?_⟩
      calc A * (y - x) = eps * (A * eps * (y - x)) := hcc.symm
        _ = eps * ((A + B) * c) := by rw [hc]
        _ = (A + B) * (eps * c) := by ring
    have hdvd2 : (A + B) ∣ (y - x) := hCcop.dvd_of_dvd_mul_left hdvdA
    have habs : |y - x| < A + B := by
      have h1 : |y - x| ≤ (A + B) - 1 := by rw [abs_le]; constructor <;> omega
      omega
    have hzero : y - x = 0 := Int.eq_zero_of_abs_lt_dvd hdvd2 habs
    omega
  have hcard := le_of_card_image_Icc hC1 S hhmem hhinj
  omega

theorem reach_of_closed_walk {A B : ℤ} (hA : 2 ≤ A) (hB : 2 ≤ B)
    (hbez : ∃ p q : ℤ, p * A + q * B = 1)
    (steps : List ℤ) (hstep : ∀ s ∈ steps, s = A ∨ s = -A ∨ s = B ∨ s = -B)
    (hsum : steps.sum = 0)
    (hnet : (steps.filter (· = A)).length ≠ (steps.filter (· = -A)).length)
    (lo hi : ℤ) (hlo1 : ∀ l ∈ steps.scanl (fun a b => a + b) (0 : ℤ), lo ≤ l)
    (hlo2 : lo ∈ steps.scanl (fun a b => a + b) (0 : ℤ))
    (hhi1 : ∀ l ∈ steps.scanl (fun a b => a + b) (0 : ℤ), l ≤ hi)
    (hhi2 : hi ∈ steps.scanl (fun a b => a + b) (0 : ℤ)) :
    ∀ j : ℤ, lo ≤ j → j ≤ hi →
      Relation.ReflTransGen (fun x y => lo ≤ y ∧ y ≤ hi ∧
        (y = x + A ∨ y = x - A ∨ y = x + B ∨ y = x - B)) 0 j := by
  have hband : A + B - 2 ≤ hi - lo :=
    band_le hA hB hbez steps hstep hsum hnet lo hi hlo1 hhi1
  intro j hjlo hjhi
  exact interval_connected hA hB hbez lo hi hband 0 j
    (hlo1 0 (zero_mem_scanl steps)) (hhi1 0 (zero_mem_scanl steps)) hjlo hjhi

end Work.OROneRel
