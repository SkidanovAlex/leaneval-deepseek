import Mathlib

namespace Work.FIArea2.Count

/-!
### Counting lattice points in a box boundary satisfying a linear congruence

The main estimate: the number of `(x,y)` in the box `[-j,j]²` lying on its boundary
(`max (|x|,|y|) = j`) and satisfying `d ∣ A x - B y` is at most
`2 (2j gcd(B,d)/d + 1) + 2 (2j gcd(A,d)/d + 1)`.

The two ingredients are:

* in an interval of `2k+1` consecutive integers, the solutions of a single linear
  congruence `B y ≡ c (mod d)` number at most `2k gcd(B,d)/d + 1`
  (`card_Icc_filter_dvd_le`);
* the boundary of the box is covered by the two "slices" `|x| = j` and `|y| = j`,
  each containing at most two lines, and on each line the count is given by the
  first ingredient.
-/

/-- A finite set of natural numbers inside `[0,N]` whose elements are pairwise congruent
modulo `m` has at most `N/m + 1` elements: `t ↦ t/m` is injective on such a set. -/
lemma card_le_div_add_one_of_modEq {m N : ℕ} (hm : 0 < m) {T : Finset ℕ}
    (hsub : T ⊆ Finset.Icc 0 N) (hmod : ∀ a ∈ T, ∀ b ∈ T, a ≡ b [MOD m]) :
    T.card ≤ N / m + 1 := by
  rcases Finset.eq_empty_or_nonempty T with h | hne
  · rw [h]; simp
  · have hinj : Set.InjOn (fun t => t / m) ↑T := by
      intro a ha b hb hab
      have hmodab : a % m = b % m := hmod a ha b hb
      have hab' : a / m = b / m := hab
      calc a = m * (a / m) + a % m := (Nat.div_add_mod a m).symm
        _ = m * (b / m) + b % m := by rw [hab', hmodab]
        _ = b := Nat.div_add_mod b m
    have himg : T.image (fun t => t / m) ⊆ Finset.Icc 0 (N / m) := by
      intro t ht
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
      have haN : a ≤ N := (Finset.mem_Icc.mp (hsub ha)).2
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.div_le_div_right haN⟩
    calc T.card = (T.image (fun t => t / m)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc 0 (N / m)).card := Finset.card_le_card himg
      _ = N / m + 1 := by rw [Nat.card_Icc]; simp

/-- **Counting the solutions of a linear congruence in a symmetric interval.**
For `d ≥ 1` and integers `B, c`, the number of `y ∈ [-k,k]` with `d ∣ B*y - c` is at most
`2k·gcd(B,d)/d + 1`.

Indeed, if `g = gcd(B.natAbs,d)` and `m = d/g` then any two solutions differ by a multiple
of `m` (Bézout: `g ∈ (B,d)`, so `d ∣ B(y-y')` forces `d ∣ g(y-y')`, whence `m ∣ y - y'`).
The solutions therefore form a subset of a residue class mod `m`, i.e. of an arithmetical
progression of difference `m` inside an interval of length `2k`; such a set has at most
`2k/m + 1 = 2k·g/d + 1` elements. -/
lemma card_Icc_filter_dvd_le (d : ℕ) (hd : 1 ≤ d) (B c : ℤ) (k : ℕ) :
    ((Finset.Icc (-(k : ℤ)) (k : ℤ)).filter (fun y => (d : ℤ) ∣ B * y - c)).card
      ≤ 2 * k * (Nat.gcd B.natAbs d) / d + 1 := by
  set S := (Finset.Icc (-(k : ℤ)) (k : ℤ)).filter (fun y => (d : ℤ) ∣ B * y - c) with hS
  set g := Nat.gcd B.natAbs d with hg
  set m := d / g with hm
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ (by omega)
  have hgdvd : g ∣ d := Nat.gcd_dvd_right _ _
  have hdeq : d = g * m := by
    rw [hm]
    exact (Nat.mul_div_cancel' hgdvd).symm
  have hmpos : 0 < m := by
    rw [hm]
    exact Nat.div_pos (Nat.le_of_dvd (by omega) hgdvd) hgpos
  -- any two solutions differ by a multiple of `m`
  have hstep : ∀ y y' : ℤ, (d : ℤ) ∣ B * y - c → (d : ℤ) ∣ B * y' - c →
      (m : ℤ) ∣ (y - y') := by
    intro y y' hy hy'
    have hdiff : (d : ℤ) ∣ B * (y - y') := by
      have h1 : B * (y - y') = (B * y - c) - (B * y' - c) := by ring
      rw [h1]; exact dvd_sub hy hy'
    have hgcd : (g : ℤ) = (Int.gcd B (d : ℤ) : ℤ) := by
      rw [Int.gcd_eq_natAbs, hg, Int.natAbs_natCast]
    obtain ⟨ua, ub, hbez⟩ : ∃ ua ub : ℤ, (g : ℤ) = B * ua + (d : ℤ) * ub :=
      ⟨B.gcdA (d : ℤ), B.gcdB (d : ℤ), by rw [hgcd, Int.gcd_eq_gcd_ab]⟩
    have hgd : (d : ℤ) ∣ (g : ℤ) * (y - y') := by
      have h2 : (g : ℤ) * (y - y') = ua * (B * (y - y')) + ub * ((d : ℤ) * (y - y')) := by
        rw [hbez]; ring
      rw [h2]
      exact dvd_add (hdiff.mul_left ua) ((dvd_mul_right (d : ℤ) (y - y')).mul_left ub)
    have hdm : (d : ℤ) = (g : ℤ) * (m : ℤ) := by
      rw [hdeq]; push_cast; ring
    rw [hdm] at hgd
    exact (Int.mul_dvd_mul_iff_left (by exact_mod_cast hgpos.ne') ).mp hgd
  rcases Finset.eq_empty_or_nonempty S with hSe | ⟨y0, hy0⟩
  · rw [hSe]; simp
  · set φ : ℤ → ℕ := fun y => (y + k).toNat with hφdef
    have hmemS : ∀ y ∈ S, -(k : ℤ) ≤ y ∧ y ≤ (k : ℤ) := by
      intro y hy
      rw [hS, Finset.mem_filter, Finset.mem_Icc] at hy
      exact hy.1
    have hdvdS : ∀ y ∈ S, (d : ℤ) ∣ B * y - c := by
      intro y hy
      rw [hS, Finset.mem_filter] at hy
      exact hy.2
    have hnonneg : ∀ y ∈ S, (0 : ℤ) ≤ y + k := by
      intro y hy
      have := (hmemS y hy).1
      omega
    have hinjφ : Set.InjOn φ ↑S := by
      intro y hy y' hy' heq
      have h1 := hnonneg y hy
      have h2 := hnonneg y' hy'
      have hcast : ((φ y : ℕ) : ℤ) = ((φ y' : ℕ) : ℤ) := by rw [heq]
      rw [hφdef] at hcast
      simp only at hcast
      rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] at hcast
      omega
    have hsub' : S.image φ ⊆ Finset.Icc 0 (2 * k) := by
      intro t ht
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
      have h3 := hnonneg y hy
      have h4 : y + k ≤ ((2 * k : ℕ) : ℤ) := by
        have := (hmemS y hy).2
        push_cast
        omega
      rw [Finset.mem_Icc]
      refine ⟨Nat.zero_le _, ?_⟩
      rw [hφdef]
      simp only
      have h5 : (((y + k).toNat : ℕ) : ℤ) ≤ ((2 * k : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg h3]
        exact h4
      exact_mod_cast h5
    have hmod' : ∀ a ∈ S.image φ, ∀ b ∈ S.image φ, a ≡ b [MOD m] := by
      intro a ha b hb
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hb
      have hdiv : (m : ℤ) ∣ (y - y') := hstep y y' (hdvdS y hy) (hdvdS y' hy')
      have h1 := hnonneg y hy
      have h2 := hnonneg y' hy'
      have hA : (m : ℤ) ∣ (((y' + k).toNat : ℕ) : ℤ) - (((y + k).toNat : ℕ) : ℤ) := by
        have heq : (((y' + k).toNat : ℕ) : ℤ) - (((y + k).toNat : ℕ) : ℤ) = -(y - y') := by
          rw [Int.toNat_of_nonneg h2, Int.toNat_of_nonneg h1]; ring
        rw [heq]
        exact dvd_neg.mpr hdiv
      exact Nat.modEq_iff_dvd.mpr hA
    have hcard' : (S.image φ).card ≤ 2 * k / m + 1 :=
      card_le_div_add_one_of_modEq hmpos hsub' hmod'
    have hcardS : S.card = (S.image φ).card := (Finset.card_image_of_injOn hinjφ).symm
    rw [hcardS]
    have hrew : 2 * k * g / d = 2 * k / m := by
      rw [hdeq]
      rw [show g * m = m * g from Nat.mul_comm g m]
      exact Nat.mul_div_mul_right (2 * k) m hgpos
    rw [hrew]
    exact hcard'

/-- Variant of `card_Icc_filter_dvd_le` with the congruence written `d ∣ c - B*y`. -/
lemma card_Icc_filter_dvd_sub_le (d : ℕ) (hd : 1 ≤ d) (B c : ℤ) (k : ℕ) :
    ((Finset.Icc (-(k : ℤ)) (k : ℤ)).filter (fun y => (d : ℤ) ∣ c - B * y)).card
      ≤ 2 * k * (Nat.gcd B.natAbs d) / d + 1 := by
  have h : (Finset.Icc (-(k : ℤ)) (k : ℤ)).filter (fun y => (d : ℤ) ∣ c - B * y)
      = (Finset.Icc (-(k : ℤ)) (k : ℤ)).filter (fun y => (d : ℤ) ∣ B * y - c) := by
    apply Finset.filter_congr
    intro y _
    constructor
    · intro hh
      have hh' : B * y - c = -(c - B * y) := by ring
      rw [hh']; exact dvd_neg.mpr hh
    · intro hh
      have hh' : c - B * y = -(B * y - c) := by ring
      rw [hh']; exact dvd_neg.mpr hh
  rw [h]
  exact card_Icc_filter_dvd_le d hd B c k

/-- If `x ∈ [-j,j]` (as an integer) then `x.natAbs ≤ j`. -/
lemma natAbs_le_of_mem_Icc {j : ℕ} {x : ℤ} (hx : x ∈ Finset.Icc (-(j : ℤ)) (j : ℤ)) :
    x.natAbs ≤ j := by
  rw [Finset.mem_Icc] at hx
  obtain ⟨h1, h2⟩ := hx
  by_cases h : 0 ≤ x
  · have hx' : (x.natAbs : ℤ) = x := Int.ofNat_natAbs_of_nonneg h
    have : (x.natAbs : ℤ) ≤ (j : ℤ) := by rw [hx']; exact h2
    exact_mod_cast this
  · push_neg at h
    have h4 : 0 ≤ -x := by omega
    have h3 : -x ≤ (j : ℤ) := by omega
    have hx' : ((-x).natAbs : ℤ) = -x := Int.ofNat_natAbs_of_nonneg h4
    have h5 : ((-x).natAbs : ℤ) ≤ (j : ℤ) := by rw [hx']; exact h3
    have h6 : (-x).natAbs ≤ j := by exact_mod_cast h5
    rwa [Int.natAbs_neg] at h6

/-- **The slice `|x| = j`.**  The number of pairs `(x,y)` with `x ∈ [-j,j]`, `|x| = j`,
`y ∈ [-j,j]` and `d ∣ A*x - B*y` is at most `2·(2j·gcd(B,d)/d + 1)`: there are at most two
values of `x` (`x = ±j`), and for each of them the number of admissible `y` is at most
`2j·gcd(B,d)/d + 1`. -/
lemma card_fst_slice_le (d : ℕ) (hd : 1 ≤ d) (A B : ℤ) (j : ℕ) :
    (((((Finset.Icc (-(j : ℤ)) (j : ℤ)).filter (fun x => x.natAbs = j)).product
        (Finset.Icc (-(j : ℤ)) (j : ℤ))).filter
      (fun w => (d : ℤ) ∣ A * w.1 - B * w.2))).card
      ≤ 2 * (2 * j * (Nat.gcd B.natAbs d) / d + 1) := by
  set T : Finset ℤ := Finset.Icc (-(j : ℤ)) (j : ℤ) with hT
  set X : Finset ℤ := T.filter (fun x => x.natAbs = j) with hX
  set P : Finset (ℤ × ℤ) := (X.product T).filter (fun w => (d : ℤ) ∣ A * w.1 - B * w.2)
    with hP
  have hXcard : X.card ≤ 2 := by
    have hsubX : X ⊆ ({(j : ℤ), -(j : ℤ)} : Finset ℤ) := by
      intro x hx
      rw [hX, Finset.mem_filter] at hx
      obtain ⟨_, hxabs⟩ := hx
      rcases Int.natAbs_eq_iff.mp hxabs with h | h
      · simp [h]
      · simp [h]
    calc X.card ≤ ({(j : ℤ), -(j : ℤ)} : Finset ℤ).card := Finset.card_le_card hsubX
      _ ≤ 2 := by
          refine le_trans (Finset.card_insert_le (j : ℤ) ({-(j : ℤ)} : Finset ℤ)) ?_
          simp
  have hbound : ∀ x ∈ X, (P.filter (fun w => w.1 = x)).card
      ≤ 2 * j * (Nat.gcd B.natAbs d) / d + 1 := by
    intro x hx
    have hle : (P.filter (fun w => w.1 = x)).card
        ≤ (T.filter (fun y => (d : ℤ) ∣ A * x - B * y)).card := by
      apply Finset.card_le_card_of_injOn (fun w : ℤ × ℤ => w.2)
      · intro w hw
        rw [Finset.mem_coe, Finset.mem_filter] at hw
        obtain ⟨hwP, hw1⟩ := hw
        rw [Finset.mem_coe, Finset.mem_filter]
        rw [hP, Finset.mem_filter] at hwP
        obtain ⟨hwPT, hwdiv⟩ := hwP
        refine ⟨(Finset.mem_product.mp hwPT).2, ?_⟩
        rw [← hw1]
        simpa using hwdiv
      · intro w hw w' hw' heq
        rw [Finset.mem_coe, Finset.mem_filter] at hw hw'
        exact Prod.ext (by rw [hw.2, hw'.2]) heq
    refine le_trans hle ?_
    rw [hT]
    exact card_Icc_filter_dvd_sub_le d hd B (A * x) j
  have hfiber : P.card = ∑ x ∈ X, (P.filter (fun w => w.1 = x)).card :=
    Finset.card_eq_sum_card_fiberwise (f := fun w : ℤ × ℤ => w.1) (by
      intro w hw
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hw).1).1)
  calc P.card = ∑ x ∈ X, (P.filter (fun w => w.1 = x)).card := hfiber
    _ ≤ ∑ x ∈ X, (2 * j * (Nat.gcd B.natAbs d) / d + 1) := Finset.sum_le_sum hbound
    _ = X.card * (2 * j * (Nat.gcd B.natAbs d) / d + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 * (2 * j * (Nat.gcd B.natAbs d) / d + 1) := Nat.mul_le_mul_right _ hXcard

/-- **The slice `|y| = j`.**  Symmetric to `card_fst_slice_le`, with the roles of `A` and `B`
interchanged. -/
lemma card_snd_slice_le (d : ℕ) (hd : 1 ≤ d) (A B : ℤ) (j : ℕ) :
    ((((Finset.Icc (-(j : ℤ)) (j : ℤ)).product
        ((Finset.Icc (-(j : ℤ)) (j : ℤ)).filter (fun y => y.natAbs = j))).filter
      (fun w => (d : ℤ) ∣ A * w.1 - B * w.2))).card
      ≤ 2 * (2 * j * (Nat.gcd A.natAbs d) / d + 1) := by
  set T : Finset ℤ := Finset.Icc (-(j : ℤ)) (j : ℤ) with hT
  set Y : Finset ℤ := T.filter (fun y => y.natAbs = j) with hY
  set P : Finset (ℤ × ℤ) := (T.product Y).filter (fun w => (d : ℤ) ∣ A * w.1 - B * w.2)
    with hP
  have hYcard : Y.card ≤ 2 := by
    have hsubY : Y ⊆ ({(j : ℤ), -(j : ℤ)} : Finset ℤ) := by
      intro y hy
      rw [hY, Finset.mem_filter] at hy
      obtain ⟨_, hyabs⟩ := hy
      rcases Int.natAbs_eq_iff.mp hyabs with h | h
      · simp [h]
      · simp [h]
    calc Y.card ≤ ({(j : ℤ), -(j : ℤ)} : Finset ℤ).card := Finset.card_le_card hsubY
      _ ≤ 2 := by
          refine le_trans (Finset.card_insert_le (j : ℤ) ({-(j : ℤ)} : Finset ℤ)) ?_
          simp
  have hbound : ∀ y ∈ Y, (P.filter (fun w => w.2 = y)).card
      ≤ 2 * j * (Nat.gcd A.natAbs d) / d + 1 := by
    intro y hy
    have hle : (P.filter (fun w => w.2 = y)).card
        ≤ (T.filter (fun x => (d : ℤ) ∣ A * x - B * y)).card := by
      apply Finset.card_le_card_of_injOn (fun w : ℤ × ℤ => w.1)
      · intro w hw
        rw [Finset.mem_coe, Finset.mem_filter] at hw
        obtain ⟨hwP, hw2⟩ := hw
        rw [Finset.mem_coe, Finset.mem_filter]
        rw [hP, Finset.mem_filter] at hwP
        obtain ⟨hwPT, hwdiv⟩ := hwP
        refine ⟨(Finset.mem_product.mp hwPT).1, ?_⟩
        rw [← hw2]
        simpa using hwdiv
      · intro w hw w' hw' heq
        rw [Finset.mem_coe, Finset.mem_filter] at hw hw'
        exact Prod.ext heq (by rw [hw.2, hw'.2])
    refine le_trans hle ?_
    rw [hT]
    exact card_Icc_filter_dvd_le d hd A (B * y) j
  have hfiber : P.card = ∑ y ∈ Y, (P.filter (fun w => w.2 = y)).card :=
    Finset.card_eq_sum_card_fiberwise (f := fun w : ℤ × ℤ => w.2) (by
      intro w hw
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hw).1).2)
  calc P.card = ∑ y ∈ Y, (P.filter (fun w => w.2 = y)).card := hfiber
    _ ≤ ∑ y ∈ Y, (2 * j * (Nat.gcd A.natAbs d) / d + 1) := Finset.sum_le_sum hbound
    _ = Y.card * (2 * j * (Nat.gcd A.natAbs d) / d + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 * (2 * j * (Nat.gcd A.natAbs d) / d + 1) := Nat.mul_le_mul_right _ hYcard

theorem card_box_filter_congr_le (d : ℕ) (hd : 1 ≤ d) (A B : ℤ) (j : ℕ) :
    ((((Finset.Icc (-(j : ℤ)) (j : ℤ)).product (Finset.Icc (-(j : ℤ)) (j : ℤ))).filter
        (fun w => max w.1.natAbs w.2.natAbs = j ∧ (d : ℤ) ∣ A * w.1 - B * w.2)).card : ℝ)
      ≤ 2 * (2 * (j : ℝ) * ((Nat.gcd B.natAbs d : ℕ) : ℝ) / (d : ℝ) + 1)
        + 2 * (2 * (j : ℝ) * ((Nat.gcd A.natAbs d : ℕ) : ℝ) / (d : ℝ) + 1) := by
  set T : Finset ℤ := Finset.Icc (-(j : ℤ)) (j : ℤ) with hT
  set S : Finset (ℤ × ℤ) :=
    (T.product T).filter (fun w => max w.1.natAbs w.2.natAbs = j ∧ (d : ℤ) ∣ A * w.1 - B * w.2)
    with hS
  set S1 : Finset (ℤ × ℤ) :=
    ((T.filter (fun x => x.natAbs = j)).product T).filter
      (fun w => (d : ℤ) ∣ A * w.1 - B * w.2) with hS1
  set S2 : Finset (ℤ × ℤ) :=
    (T.product (T.filter (fun y => y.natAbs = j))).filter
      (fun w => (d : ℤ) ∣ A * w.1 - B * w.2) with hS2
  have hsub : S ⊆ S1 ∪ S2 := by
    intro w hw
    rw [hS, Finset.mem_filter] at hw
    obtain ⟨hwT, hwmax, hwdvd⟩ := hw
    obtain ⟨hw1, hw2⟩ := Finset.mem_product.mp hwT
    rw [Finset.mem_union]
    rcases max_eq_iff.mp hwmax with ⟨heq, _⟩ | ⟨heq, _⟩
    · left
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hw1, heq⟩, hw2⟩, hwdvd⟩
    · right
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hw1, Finset.mem_filter.mpr ⟨hw2, heq⟩⟩, hwdvd⟩
  have hnat : S.card
      ≤ 2 * (2 * j * (Nat.gcd B.natAbs d) / d + 1)
        + 2 * (2 * j * (Nat.gcd A.natAbs d) / d + 1) := by
    have h1 : S1.card ≤ 2 * (2 * j * (Nat.gcd B.natAbs d) / d + 1) := by
      rw [hS1, hT]
      exact card_fst_slice_le d hd A B j
    have h2 : S2.card ≤ 2 * (2 * j * (Nat.gcd A.natAbs d) / d + 1) := by
      rw [hS2, hT]
      exact card_snd_slice_le d hd A B j
    calc S.card ≤ S1.card + S2.card :=
          le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
      _ ≤ 2 * (2 * j * (Nat.gcd B.natAbs d) / d + 1)
            + 2 * (2 * j * (Nat.gcd A.natAbs d) / d + 1) := Nat.add_le_add h1 h2
  have hB : ((2 * j * (Nat.gcd B.natAbs d) / d : ℕ) : ℝ)
      ≤ 2 * (j : ℝ) * ((Nat.gcd B.natAbs d : ℕ) : ℝ) / (d : ℝ) := by
    have hc : ((2 * j * (Nat.gcd B.natAbs d) / d : ℕ) : ℝ)
        ≤ ((2 * j * (Nat.gcd B.natAbs d) : ℕ) : ℝ) / (d : ℝ) := Nat.cast_div_le
    have hc2 : ((2 * j * (Nat.gcd B.natAbs d) : ℕ) : ℝ) / (d : ℝ)
        = 2 * (j : ℝ) * ((Nat.gcd B.natAbs d : ℕ) : ℝ) / (d : ℝ) := by
      push_cast; ring
    linarith [hc, hc2]
  have hA : ((2 * j * (Nat.gcd A.natAbs d) / d : ℕ) : ℝ)
      ≤ 2 * (j : ℝ) * ((Nat.gcd A.natAbs d : ℕ) : ℝ) / (d : ℝ) := by
    have hc : ((2 * j * (Nat.gcd A.natAbs d) / d : ℕ) : ℝ)
        ≤ ((2 * j * (Nat.gcd A.natAbs d) : ℕ) : ℝ) / (d : ℝ) := Nat.cast_div_le
    have hc2 : ((2 * j * (Nat.gcd A.natAbs d) : ℕ) : ℝ) / (d : ℝ)
        = 2 * (j : ℝ) * ((Nat.gcd A.natAbs d : ℕ) : ℝ) / (d : ℝ) := by
      push_cast; ring
    linarith [hc, hc2]
  have hcast : ((S.card : ℕ) : ℝ)
      ≤ ((2 * (2 * j * (Nat.gcd B.natAbs d) / d + 1)
          + 2 * (2 * j * (Nat.gcd A.natAbs d) / d + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hrhs : ((2 * (2 * j * (Nat.gcd B.natAbs d) / d + 1)
          + 2 * (2 * j * (Nat.gcd A.natAbs d) / d + 1) : ℕ) : ℝ)
      = 2 * (((2 * j * (Nat.gcd B.natAbs d) / d : ℕ) : ℝ) + 1)
        + 2 * (((2 * j * (Nat.gcd A.natAbs d) / d : ℕ) : ℝ) + 1) := by
    push_cast; ring
  rw [hrhs] at hcast
  linarith [hcast, hB, hA]

end Work.FIArea2.Count
