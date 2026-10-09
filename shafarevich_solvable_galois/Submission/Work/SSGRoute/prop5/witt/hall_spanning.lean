import Mathlib
import Submission.Work.SSGRoute.prop5.witt.Basic
import Submission.Work.SSGRoute.prop5.witt.hall_foliage_lt_right
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Hall's spanning theorem in `ψ`-form

For a linearly ordered alphabet `X`, a Lie ring `M` and any map `ψ : Magma X → M` compatible with
the bracket (`ψ (mul a b) = ⁅ψ a, ψ b⁆`), every value `ψ w` lies in the `ℤ`-span of the values
`ψ h` on *Hall* trees `h`.  This is the spanning half of Hall's theorem that the Hall trees form a
basis of the free Lie ring.

The proof follows the classical decomposition algorithm for Hall sets: for two Hall trees `x < y`
with `y = mul z t`, either `mul x y` is again Hall, or `x < z` and the Jacobi identity gives

  `⁅ψ x, ψ y⁆ = ⁅⁅ψ x, ψ z⁆, ψ t⁆ + ⁅ψ z, ⁅ψ x, ψ t⁆⁆`,

reducing `⁅ψ x, ψ y⁆` to brackets of *smaller* pairs.  The recursion terminates because the smaller
element of the pair strictly increases in the foliage order while the multiset of leaves of the
pair is preserved; this is measured by a rank function on the words of a fixed finite alphabet.
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5.witt

variable {X : Type*} [LinearOrder X]

/-! ## A finite universe of words -/

/-- All words of length at most `n` whose letters lie in the finite set `A`. -/
def wordsLe (A : Finset X) : ℕ → Finset (List X)
  | 0 => {[]}
  | n + 1 => insert [] (A.biUnion (fun a => (wordsLe A n).image (fun u => a :: u)))

lemma mem_wordsLe {A : Finset X} :
    ∀ {n : ℕ} {u : List X}, u ∈ wordsLe A n ↔ u.length ≤ n ∧ ∀ x ∈ u, x ∈ A := by
  intro n
  induction n with
  | zero =>
      intro u
      simp only [wordsLe, Finset.mem_singleton]
      constructor
      · rintro rfl; simp
      · rintro ⟨hlen, _⟩
        exact List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
  | succ n ih =>
      intro u
      rw [wordsLe]
      constructor
      · intro h
        rcases Finset.mem_insert.mp h with rfl | h'
        · simp
        · obtain ⟨a, ha, hu⟩ := Finset.mem_biUnion.mp h'
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
          rw [ih] at hw
          refine ⟨by simpa using hw.1, fun x hx => ?_⟩
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ha
          · exact hw.2 x hx
      · rintro ⟨hlen, hletters⟩
        rcases u with _ | ⟨a, u'⟩
        · simp
        · refine Finset.mem_insert.mpr (Or.inr ?_)
          refine Finset.mem_biUnion.mpr ⟨a, hletters a (by simp), ?_⟩
          refine Finset.mem_image.mpr ⟨u', ?_, rfl⟩
          rw [ih]
          refine ⟨by simpa using hlen, ?_⟩
          intro x hx
          exact hletters x (by simp [hx])

lemma nil_mem_wordsLe (A : Finset X) (n : ℕ) : ([] : List X) ∈ wordsLe A n := by
  rw [mem_wordsLe]
  refine ⟨Nat.zero_le _, ?_⟩
  simp

lemma wordsLe_mono {A A' : Finset X} (hA : A' ⊆ A) {n n' : ℕ} (hn : n' ≤ n) :
    wordsLe A' n' ⊆ wordsLe A n := by
  intro u hu
  rw [mem_wordsLe] at hu ⊢
  exact ⟨le_trans hu.1 hn, fun x hx => hA (hu.2 x hx)⟩

/-- A word is strictly below its extension by a nonempty word. -/
lemma fol_lt_append {s t : List X} (ht : t ≠ []) : s < s ++ t := by
  induction s with
  | nil =>
      cases t with
      | nil => exact absurd rfl ht
      | cons b t => exact List.Lex.nil
  | cons a s ih => exact List.Lex.cons ih

/-- A prefix is below the word in the list order (with the ambient instances). -/
lemma isPrefix_le_of_prefix {a b : List X} (h : a <+: b) : a ≤ b := by
  rcases h with ⟨c, rfl⟩
  rcases eq_or_ne c [] with rfl | hc
  · exact le_of_eq (List.append_nil a).symm
  · exact le_of_lt (fol_lt_append hc)

lemma wordsLe_perm {L L' : List X} (h : L.Perm L') :
    wordsLe L.toFinset L.length = wordsLe L'.toFinset L'.length := by
  have hset : L.toFinset = L'.toFinset := by
    ext x
    rw [List.mem_toFinset, List.mem_toFinset]
    exact h.mem_iff
  rw [hset, h.length_eq]

/-! ## The pair measure

For a pair `(u, v)` of trees we measure the pair by

* `pN u v = |foliage u| + |foliage v|`, the total number of leaves, and
* `pWr u v`, the rank of `foliage u` among the words over the alphabet of `foliage u ++ foliage v`
  of length at most `pN u v`.

The measure `pmeas u v` is `pN * (#alphabet words) + (#alphabet words - pWr)`, so that it decreases
when either the total length decreases or (at constant length) the rank of `foliage u` increases.
-/

/-- The alphabet of a pair: the letters occurring in `foliage u ++ foliage v`. -/
def pA (u v : Magma X) : Finset X := (Magma.foliage u ++ Magma.foliage v).toFinset

/-- The total number of leaves of the pair `(u, v)`. -/
def pN (u v : Magma X) : ℕ := (Magma.foliage u ++ Magma.foliage v).length

/-- The finite universe of words attached to the pair `(u, v)`. -/
def pU (u v : Magma X) : Finset (List X) := wordsLe (pA u v) (pN u v)

/-- The rank of `foliage u` in the universe of the pair `(u, v)`. -/
def pWr (u v : Magma X) : ℕ := ((pU u v).filter (fun w => w ≤ Magma.foliage u)).card

/-- The termination measure of the pair `(u, v)`. -/
def pmeas (u v : Magma X) : ℕ := pN u v * (pU u v).card + ((pU u v).card - pWr u v)

variable {M : Type*} [LieRing M]

lemma pWr_le (u v : Magma X) : pWr u v ≤ (pU u v).card :=
  Finset.card_filter_le _ _

lemma pWr_lt_of_lt {u v u' v' : Magma X} (hU : pU u' v' = pU u v)
    (h : Magma.foliage u < Magma.foliage u') (hv : Magma.foliage u' ∈ pU u v) :
    pWr u v < pWr u' v' := by
  rw [pWr, pWr, hU]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro w hw
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨hw.1, le_trans hw.2 (le_of_lt h)⟩
  · intro heq
    have hmem : Magma.foliage u' ∈ (pU u v).filter (fun w => w ≤ Magma.foliage u) := by
      rw [heq]
      exact Finset.mem_filter.mpr ⟨hv, le_rfl⟩
    rw [Finset.mem_filter] at hmem
    exact absurd hmem.2 (not_le.mpr h)

lemma pN_eq_of_perm_aux {u v u' v' : Magma X}
    (hms : ((Magma.foliage u' ++ Magma.foliage v' : List X) : Multiset X) =
      ((Magma.foliage u ++ Magma.foliage v : List X) : Multiset X)) :
    pN u' v' = pN u v := by
  simp only [pN]
  simpa using congrArg Multiset.card hms

lemma pA_eq_of_perm_aux {u v u' v' : Magma X}
    (hms : ((Magma.foliage u' ++ Magma.foliage v' : List X) : Multiset X) =
      ((Magma.foliage u ++ Magma.foliage v : List X) : Multiset X)) :
    pA u' v' = pA u v := by
  simp only [pA]
  simpa using congrArg Multiset.toFinset hms

lemma pU_eq_of_perm_aux {u v u' v' : Magma X}
    (hms : ((Magma.foliage u' ++ Magma.foliage v' : List X) : Multiset X) =
      ((Magma.foliage u ++ Magma.foliage v : List X) : Multiset X)) :
    pU u' v' = pU u v := by
  rw [pU, pU, pA_eq_of_perm_aux hms, pN_eq_of_perm_aux hms]

lemma foliage_mem_pU_aux {u v u' v' : Magma X}
    (hms : ((Magma.foliage u' ++ Magma.foliage v' : List X) : Multiset X) =
      ((Magma.foliage u ++ Magma.foliage v : List X) : Multiset X)) :
    Magma.foliage u' ∈ pU u v := by
  have hlen : (Magma.foliage u').length ≤ pN u v := by
    have h1 : (Magma.foliage u').length ≤ pN u' v' := by
      rw [pN, List.length_append]
      exact Nat.le_add_right _ _
    rwa [pN_eq_of_perm_aux hms] at h1
  have hletters : ∀ x ∈ Magma.foliage u', x ∈ pA u v := by
    intro x hx
    have hx1 : x ∈ ((↑(Magma.foliage u' ++ Magma.foliage v') : Multiset X)) := by
      rw [Multiset.mem_coe]
      exact List.mem_append_left _ hx
    rw [hms] at hx1
    rw [Multiset.mem_coe] at hx1
    simp only [pA, List.mem_toFinset]
    exact hx1
  rw [pU, mem_wordsLe]
  exact ⟨hlen, hletters⟩

lemma pmeas_lt_of_perm_aux {u v u' v' : Magma X}
    (hms : ((Magma.foliage u' ++ Magma.foliage v' : List X) : Multiset X) =
      ((Magma.foliage u ++ Magma.foliage v : List X) : Multiset X))
    (h : Magma.foliage u < Magma.foliage u') : pmeas u' v' < pmeas u v := by
  have hN := pN_eq_of_perm_aux hms
  have hU := pU_eq_of_perm_aux hms
  have hwr : pWr u v < pWr u' v' := pWr_lt_of_lt hU h (foliage_mem_pU_aux hms)
  have hle : pWr u' v' ≤ (pU u v).card := by
    have := pWr_le u' v'
    rwa [hU] at this
  simp only [pmeas]
  rw [hN, hU]
  omega

lemma pmeas_lt_of_short_aux {u v u' v' : Magma X} (hfol : Magma.foliage u' = Magma.foliage u)
    (hA : pA u' v' ⊆ pA u v) (hN : pN u' v' < pN u v) : pmeas u' v' < pmeas u v := by
  have hsub : pU u' v' ⊆ pU u v := wordsLe_mono hA (le_of_lt hN)
  have hpos : 0 < (pU u v).card :=
    Finset.card_pos.mpr ⟨[], nil_mem_wordsLe (pA u v) (pN u v)⟩
  rcases lt_or_eq_of_le (Finset.card_le_card hsub) with hlt | heq
  · have h1 : pmeas u' v' ≤ (pN u' v' + 1) * (pU u' v').card :=
      calc pmeas u' v'
          ≤ pN u' v' * (pU u' v').card + (pU u' v').card := by
            simp only [pmeas]
            exact Nat.add_le_add_left (Nat.sub_le _ _) _
        _ = (pN u' v' + 1) * (pU u' v').card := (Nat.succ_mul _ _).symm
    have h2 : (pN u' v' + 1) * (pU u' v').card ≤ pN u v * (pU u' v').card :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hN)
    have h3 : pN u v * (pU u' v').card < pN u v * (pU u v).card :=
      Nat.mul_lt_mul_of_pos_left hlt (Nat.lt_of_le_of_lt (Nat.zero_le _) hN)
    have h4 : pN u v * (pU u v).card ≤ pmeas u v := by
      simp only [pmeas]
      exact Nat.le_add_right _ _
    exact lt_of_le_of_lt h1 (lt_of_le_of_lt h2 (lt_of_lt_of_le h3 h4))
  · have hset : pU u' v' = pU u v :=
      Finset.eq_of_subset_of_card_le hsub (le_of_eq heq.symm)
    have hwr : pWr u' v' = pWr u v := by
      simp only [pWr, hset, hfol]
    have hleft : pmeas u' v' =
        pN u' v' * (pU u v).card + ((pU u v).card - pWr u v) := by
      simp only [pmeas, hwr, heq]
    rw [hleft, pmeas]
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right hN hpos) _

/-! ## Injectivity of the foliage on Hall trees

Two Hall trees with the same foliage are equal.  The proof uses the "Lyndon-like" property of Hall
foliages (`hall_lyndonLike`: a Hall foliage is strictly below each of its proper nonempty suffixes)
and a descent along the right branch of a Hall tree.
-/

/-- `Dominated A1 q` holds when the foliage of every left part in the right-descent chain of `q`
is `≤ A1`. -/
def Dominated (A1 : List X) : Magma X → Prop
  | Magma.gen _ => True
  | Magma.mul z t => Magma.foliage z ≤ A1 ∧ Dominated A1 t

lemma dominated_mono {A1 A2 : List X} (h : A1 ≤ A2) :
    ∀ {q : Magma X}, Dominated A1 q → Dominated A2 q := by
  intro q
  induction q with
  | gen x => intro _; trivial
  | mul z t _ iht => intro hd; exact ⟨le_trans hd.1 h, iht hd.2⟩

lemma dominated_mono_pre {A1 A2 : List X} (h : A1 <+: A2) {q : Magma X} (hd : Dominated A1 q) :
    Dominated A2 q := dominated_mono (isPrefix_le_of_prefix h) hd

/-- The left part of a Hall product dominates its right part, in the sense of `Dominated`. -/
lemma dominated_of_hall_mul (p q : Magma X) (h : IsHall (Magma.mul p q)) :
    Dominated (Magma.foliage p) q := by
  have key : ∀ n, ∀ (p q : Magma X), Magma.size q = n → IsHall (Magma.mul p q) →
      Dominated (Magma.foliage p) q := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro p q hsize h
      cases q with
      | gen x => trivial
      | mul z t =>
        have hzt : IsHall (Magma.mul z t) := h.right
        have hz : Magma.foliage z ≤ Magma.foliage p :=
          not_lt.mp (IsHall.le_of_right_eq_mul (z := z) (t := t) h rfl)
        have hsub : Magma.size t < n := by
          rw [← hsize]; exact Magma.size_right_lt z t
        exact ⟨hz, dominated_mono hz (ih (Magma.size t) hsub z t rfl hzt)⟩
  exact key (Magma.size q) p q rfl h

/-- The descent lemma: if a nonempty proper prefix `e` of the foliage of a Hall tree is "dominated"
by `A1`, then `A1 ++ e` is not Lyndon-like (it has a proper nonempty suffix below it). -/
lemma not_lyndonLike_of_dominated : ∀ (n : ℕ) (q : Magma X), Magma.size q = n → IsHall q →
    ∀ (A1 e : List X), A1 ≠ [] → Dominated A1 q → e <+: Magma.foliage q → e ≠ [] →
      e ≠ Magma.foliage q → ¬ LyndonLike (A1 ++ e) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro q hsize hq A1 e hA1 hdom he hene hproper
    cases q with
    | gen x =>
      obtain ⟨c, hc⟩ := he
      have hlen : e.length ≤ 1 := by
        have h2 := congrArg List.length hc
        simp only [List.length_append, List.length_cons, List.length_nil, Magma.foliage_gen] at h2
        omega
      have hcases : e = [] ∨ e = [x] := by
        rcases e with _ | ⟨y, e'⟩
        · exact Or.inl rfl
        · have he' : e'.length = 0 := by simpa using hlen
          obtain rfl : e' = [] := List.eq_nil_of_length_eq_zero he'
          rw [List.cons_append, List.nil_append] at hc
          have hconj : y = x ∧ c = [] := by simpa using hc
          have hyx : y = x := hconj.1
          subst hyx
          exact Or.inr rfl
      rcases hcases with hnil | hx
      · rw [hnil] at hene
        exact absurd rfl hene
      · rw [hx] at hproper
        exact absurd rfl hproper
    | mul z t =>
      have hzt : IsHall (Magma.mul z t) := hq
      obtain ⟨hzA1, hdom_t⟩ := hdom
      have hfolz : Magma.foliage z <+: Magma.foliage (Magma.mul z t) := by
        rw [Magma.foliage_mul]; exact List.prefix_append _ _
      by_cases hcase : e <+: Magma.foliage z
      · -- `e` is a prefix of `foliage z`, hence `≤ A1`: it is a proper nonempty suffix of `A1 ++ e`
        intro hL
        have heA1 : e ≤ A1 := le_trans (isPrefix_le_of_prefix hcase) hzA1
        have hlt : e < A1 ++ e := by
          refine lt_of_le_of_ne (le_trans heA1 (isPrefix_le_of_prefix (List.prefix_append A1 e))) ?_
          intro hcon
          have h2 := congrArg List.length hcon
          simp only [List.length_append] at h2
          have h3 : 0 < A1.length := List.length_pos_iff.mpr hA1
          omega
        exact absurd (hL A1 e rfl hA1 hene) (not_lt.mpr hlt.le)
      · -- otherwise `foliage z` is a prefix of `e`: descend into `t`
        have hpc : Magma.foliage z <+: e :=
          (List.prefix_or_prefix_of_prefix he hfolz).resolve_left hcase
        obtain ⟨e', he'⟩ := hpc
        have he'ne : e' ≠ [] := by
          intro h0
          exact hcase (by rw [← he', h0, List.append_nil])
        have he'pre : e' <+: Magma.foliage t := by
          obtain ⟨c, hc⟩ := he
          rw [Magma.foliage_mul, ← he', List.append_assoc] at hc
          exact ⟨c, List.append_cancel_left hc⟩
        have he'proper : e' ≠ Magma.foliage t := by
          intro h0
          exact hproper (by rw [← he', h0, Magma.foliage_mul])
        have hsub : Magma.size t < n := by
          rw [← hsize]; exact Magma.size_right_lt z t
        have hgoal : (A1 ++ Magma.foliage z) ++ e' = A1 ++ e := by
          rw [← he', List.append_assoc]
        rw [← hgoal]
        exact ih (Magma.size t) hsub t rfl hzt.right (A1 ++ Magma.foliage z) e'
          (by simp [hA1])
          (dominated_mono_pre (List.prefix_append A1 (Magma.foliage z)) hdom_t)
          he'pre he'ne he'proper

/-- **Injectivity of the foliage on Hall trees.** -/
lemma hall_foliage_injective_aux {a b : Magma X} (ha : IsHall a) (hb : IsHall b)
    (h : Magma.foliage a = Magma.foliage b) : a = b := by
  have key : ∀ n, ∀ a : Magma X, Magma.size a = n → IsHall a → ∀ b : Magma X, IsHall b →
      Magma.foliage a = Magma.foliage b → a = b := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a hsize ha b hb hfol
      cases a with
      | gen x =>
        cases b with
        | gen y =>
          have hxy : x = y := by simpa using hfol
          rw [hxy]
        | mul b1 b2 =>
          exfalso
          have h2 := congrArg List.length hfol
          rw [Magma.foliage_gen, Magma.foliage_mul, List.length_append, List.length_cons,
            List.length_nil] at h2
          have h1 : 0 < (Magma.foliage b1).length :=
            List.length_pos_iff.mpr (Magma.foliage_ne_nil b1)
          have h3 : 0 < (Magma.foliage b2).length :=
            List.length_pos_iff.mpr (Magma.foliage_ne_nil b2)
          omega
      | mul a1 a2 =>
        cases b with
        | gen y =>
          exfalso
          have h2 := congrArg List.length hfol
          rw [Magma.foliage_mul, List.length_append, Magma.foliage_gen, List.length_cons,
            List.length_nil] at h2
          have h1 : 0 < (Magma.foliage a1).length :=
            List.length_pos_iff.mpr (Magma.foliage_ne_nil a1)
          have h3 : 0 < (Magma.foliage a2).length :=
            List.length_pos_iff.mpr (Magma.foliage_ne_nil a2)
          omega
        | mul b1 b2 =>
          have ha1 : IsHall a1 := ha.left
          have ha2 : IsHall a2 := ha.right
          have hb1 : IsHall b1 := hb.left
          have hb2 : IsHall b2 := hb.right
          have hpre1 : Magma.foliage a1 <+: Magma.foliage (Magma.mul a1 a2) := by
            rw [Magma.foliage_mul]; exact List.prefix_append _ _
          have hpre2 : Magma.foliage b1 <+: Magma.foliage (Magma.mul a1 a2) := by
            rw [hfol, Magma.foliage_mul]; exact List.prefix_append _ _
          by_cases heq : Magma.foliage a1 = Magma.foliage b1
          · have h1 : a1 = b1 := ih (Magma.size a1)
              (by rw [← hsize]; exact Magma.size_left_lt a1 a2) a1 rfl ha1 b1 hb1 heq
            have hfol2 : Magma.foliage a2 = Magma.foliage b2 := by
              have h2 := hfol
              rw [Magma.foliage_mul, Magma.foliage_mul, ← heq] at h2
              exact List.append_cancel_left h2
            have h2 : a2 = b2 := ih (Magma.size a2)
              (by rw [← hsize]; exact Magma.size_right_lt a1 a2) a2 rfl ha2 b2 hb2 hfol2
            rw [h1, h2]
          · rcases List.prefix_or_prefix_of_prefix hpre1 hpre2 with hc | hc
            · obtain ⟨s, hs⟩ := hc
              exfalso
              have hsne : s ≠ [] := by
                intro h0
                rw [h0, List.append_nil] at hs
                exact heq hs
              have hA2 : Magma.foliage a2 = s ++ Magma.foliage b2 := by
                have h2 := hfol
                rw [Magma.foliage_mul, Magma.foliage_mul, ← hs, List.append_assoc] at h2
                exact List.append_cancel_left h2
              have hpres : s <+: Magma.foliage a2 := by
                rw [hA2]; exact List.prefix_append s _
              have hsproper : s ≠ Magma.foliage a2 := by
                intro h0
                have h2 := congrArg List.length hA2
                rw [h0, List.length_append] at h2
                have h3 : 0 < (Magma.foliage b2).length :=
                  List.length_pos_iff.mpr (Magma.foliage_ne_nil b2)
                omega
              have hdom : Dominated (Magma.foliage a1) a2 := dominated_of_hall_mul a1 a2 ha
              have hnl := not_lyndonLike_of_dominated (Magma.size a2) a2 rfl ha2
                (Magma.foliage a1) s (Magma.foliage_ne_nil a1) hdom hpres hsne hsproper
              exact hnl (by rw [hs]; exact hall_lyndonLike b1 hb1)
            · obtain ⟨s, hs⟩ := hc
              exfalso
              have hsne : s ≠ [] := by
                intro h0
                rw [h0, List.append_nil] at hs
                exact heq hs.symm
              have hB2 : Magma.foliage b2 = s ++ Magma.foliage a2 := by
                have h2 := hfol
                rw [Magma.foliage_mul, Magma.foliage_mul, ← hs, List.append_assoc] at h2
                exact (List.append_cancel_left h2).symm
              have hpres : s <+: Magma.foliage b2 := by
                rw [hB2]; exact List.prefix_append s _
              have hsproper : s ≠ Magma.foliage b2 := by
                intro h0
                have h2 := congrArg List.length hB2
                rw [h0, List.length_append] at h2
                have h3 : 0 < (Magma.foliage a2).length :=
                  List.length_pos_iff.mpr (Magma.foliage_ne_nil a2)
                omega
              have hdom : Dominated (Magma.foliage b1) b2 := dominated_of_hall_mul b1 b2 hb
              have hnl := not_lyndonLike_of_dominated (Magma.size b2) b2 rfl hb2
                (Magma.foliage b1) s (Magma.foliage_ne_nil b1) hdom hpres hsne hsproper
              exact hnl (by rw [hs]; exact hall_lyndonLike a1 ha1)
  exact key (Magma.size a) a rfl ha b hb h

/-! ## The Hall elements occurring in the expansion of `⁅ψ x, ψ y⁆` -/

/-- The Hall trees that may occur in the expansion of `⁅ψ x, ψ y⁆`: they have the same multiset of
leaves as `foliage x ++ foliage y`, and their left factor is at least `foliage x`. -/
def Good (x y c : Magma X) : Prop :=
  IsHall c ∧ (Magma.foliage c : Multiset X) =
      (Magma.foliage x : Multiset X) + (Magma.foliage y : Multiset X) ∧
    ∃ a b, c = Magma.mul a b ∧ Magma.foliage x ≤ Magma.foliage a

/-- The submodule spanned by the values of `ψ` on the `Good` trees. -/
def W (ψ : Magma X → M) (x y : Magma X) : Submodule ℤ M :=
  Submodule.span ℤ (ψ '' {c : Magma X | Good x y c})

lemma mem_W_mul (ψ : Magma X → M) {x y : Magma X} (h : IsHall (Magma.mul x y)) :
    ψ (Magma.mul x y) ∈ W ψ x y := by
  refine Submodule.subset_span ⟨Magma.mul x y, ⟨h, ?_, x, y, rfl, le_rfl⟩, rfl⟩
  rw [Magma.foliage_mul, ← Multiset.coe_add]

lemma W_mono (ψ : Magma X → M) {x y u v : Magma X}
    (hms : (Magma.foliage u : Multiset X) + (Magma.foliage v : Multiset X) =
      (Magma.foliage x : Multiset X) + (Magma.foliage y : Multiset X))
    (hfol : Magma.foliage x ≤ Magma.foliage u) : W ψ u v ≤ W ψ x y := by
  refine Submodule.span_mono ?_
  rintro m ⟨c, hG, rfl⟩
  obtain ⟨a, b, hab, hle⟩ := hG.2.2
  exact ⟨c, ⟨hG.1, hG.2.1.trans hms, a, b, hab, le_trans hfol hle⟩, rfl⟩

/-- The Jacobi identity in the form used by the decomposition algorithm. -/
lemma jacobi_form {L : Type*} [LieRing L] (a b c : L) :
    ⁅a, ⁅b, c⁆⁆ = ⁅⁅a, b⁆, c⁆ + ⁅b, ⁅a, c⁆⁆ := by
  have h := lie_jacobi a b c
  have h1 : ⁅b, ⁅c, a⁆⁆ = -⁅b, ⁅a, c⁆⁆ := by
    rw [show ⁅c, a⁆ = -⁅a, c⁆ from neg_eq_iff_eq_neg.mp (lie_skew a c), lie_neg]
  have h2 : ⁅c, ⁅a, b⁆⁆ = -⁅⁅a, b⁆, c⁆ := neg_eq_iff_eq_neg.mp (lie_skew ⁅a, b⁆ c)
  rw [h1, h2, add_assoc] at h
  have h3 := eq_neg_of_add_eq_zero_left h
  rw [neg_add, neg_neg, neg_neg, add_comm] at h3
  exact h3

theorem pair_mem (ψ : Magma X → M)
    (hψ : ∀ a b : Magma X, ψ (Magma.mul a b) = ⁅ψ a, ψ b⁆) :
    ∀ x y : Magma X, IsHall x → IsHall y → Magma.foliage x < Magma.foliage y →
      ⁅ψ x, ψ y⁆ ∈ W ψ x y := by
  have key : ∀ n : ℕ, ∀ x y : Magma X, IsHall x → IsHall y →
      Magma.foliage x < Magma.foliage y → pmeas x y = n → ⁅ψ x, ψ y⁆ ∈ W ψ x y := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x y hx hy hlt hmeas
      have IH : ∀ u v : Magma X, IsHall u → IsHall v → Magma.foliage u < Magma.foliage v →
          pmeas u v < n → ⁅ψ u, ψ v⁆ ∈ W ψ u v :=
        fun u v hu hv huv hlt' => ih (pmeas u v) hlt' u v hu hv huv rfl
      by_cases hhall : IsHall (Magma.mul x y)
      · rw [show ⁅ψ x, ψ y⁆ = ψ (Magma.mul x y) from (hψ x y).symm]
        exact mem_W_mul ψ hhall
      · cases y with
        | gen g =>
            exact absurd (isHall_mul_iff.mpr ⟨hx, isHall_gen g, hlt, Or.inl ⟨g, rfl⟩⟩) hhall
        | mul z t =>
            have hz : IsHall z := hy.left
            have ht : IsHall t := hy.right
            have hzt : Magma.foliage z < Magma.foliage t := hy.foliage_lt
            have hxz : Magma.foliage x < Magma.foliage z := by
              by_contra hcon
              exact hhall (isHall_mul_iff.mpr ⟨hx, hy, hlt, Or.inr ⟨z, t, rfl, hcon⟩⟩)
            have hxt : Magma.foliage x < Magma.foliage t := lt_trans hxz hzt
            have hshort_xz : pmeas x z < n := by
              refine lt_of_lt_of_eq (pmeas_lt_of_short_aux (u := x) (v := Magma.mul z t)
                (u' := x) (v' := z) rfl ?_ ?_) hmeas
              · intro a ha
                simp only [pA, List.mem_toFinset, Magma.foliage_mul, List.mem_append] at ha ⊢
                tauto
              · simp only [pN, Magma.foliage_mul, List.length_append]
                have htlen : 0 < (Magma.foliage t).length :=
                  List.length_pos_iff.mpr (Magma.foliage_ne_nil t)
                omega
            have hshort_xt : pmeas x t < n := by
              refine lt_of_lt_of_eq (pmeas_lt_of_short_aux (u := x) (v := Magma.mul z t)
                (u' := x) (v' := t) rfl ?_ ?_) hmeas
              · intro a ha
                simp only [pA, List.mem_toFinset, Magma.foliage_mul, List.mem_append] at ha ⊢
                tauto
              · simp only [pN, Magma.foliage_mul, List.length_append]
                have hzlen : 0 < (Magma.foliage z).length :=
                  List.length_pos_iff.mpr (Magma.foliage_ne_nil z)
                omega
            rw [show ⁅ψ x, ψ (Magma.mul z t)⁆ = ⁅⁅ψ x, ψ z⁆, ψ t⁆ + ⁅ψ z, ⁅ψ x, ψ t⁆⁆ from by
              rw [hψ z t]
              exact jacobi_form (ψ x) (ψ z) (ψ t)]
            refine Submodule.add_mem _ ?_ ?_
            · have hleft : ∀ p ∈ W ψ x z, ⁅p, ψ t⁆ ∈ W ψ x (Magma.mul z t) := by
                intro p hp
                refine Submodule.span_induction
                  (p := fun y _ => ⁅y, ψ t⁆ ∈ W ψ x (Magma.mul z t)) ?_ ?_ ?_ ?_ hp
                · rintro m ⟨c, hG, rfl⟩
                  obtain ⟨hcH, hcms, a, b, hcab, hcfol⟩ := hG
                  have hxc : Magma.foliage x < Magma.foliage c := by
                    have : Magma.foliage a < Magma.foliage c := by
                      rw [hcab, Magma.foliage_mul]
                      exact fol_lt_append (Magma.foliage_ne_nil b)
                    exact lt_of_le_of_lt hcfol this
                  have hms_ct : (Magma.foliage c : Multiset X) + (Magma.foliage t : Multiset X) =
                      (Magma.foliage x : Multiset X) +
                        (Magma.foliage (Magma.mul z t) : Multiset X) := by
                    rw [hcms, Magma.foliage_mul, ← Multiset.coe_add]
                    ac_rfl
                  rcases eq_or_ne c t with rfl | hct
                  · rw [lie_self]; exact Submodule.zero_mem _
                  · rcases lt_trichotomy (Magma.foliage c) (Magma.foliage t) with h' | h' | h'
                    · have hsmall : pmeas c t < n :=
                        lt_of_lt_of_eq (pmeas_lt_of_perm_aux hms_ct hxc) hmeas
                      exact W_mono ψ hms_ct (le_of_lt hxc) (IH c t hcH ht h' hsmall)
                    · exact absurd (hall_foliage_injective_aux hcH ht h') hct
                    · have hms_tc : (Magma.foliage t : Multiset X) +
                          (Magma.foliage c : Multiset X) =
                          (Magma.foliage x : Multiset X) +
                            (Magma.foliage (Magma.mul z t) : Multiset X) := by
                        exact (add_comm (Magma.foliage t : Multiset X)
                          (Magma.foliage c : Multiset X)).trans hms_ct
                      have hsmall : pmeas t c < n :=
                        lt_of_lt_of_eq (pmeas_lt_of_perm_aux hms_tc hxt) hmeas
                      have hmem : ⁅ψ t, ψ c⁆ ∈ W ψ t c := IH t c ht hcH h' hsmall
                      rw [show ⁅ψ c, ψ t⁆ = -⁅ψ t, ψ c⁆ from (lie_skew (ψ c) (ψ t)).symm]
                      exact Submodule.neg_mem _ (W_mono ψ hms_tc (le_of_lt hxt) hmem)
                · rw [zero_lie]; exact Submodule.zero_mem _
                · intro p q _ _ hp' hq'
                  rw [add_lie]; exact Submodule.add_mem _ hp' hq'
                · intro r p _ hp'
                  rw [zsmul_lie]; exact Submodule.smul_mem _ r hp'
              exact hleft _ (IH x z hx hz hxz hshort_xz)
            · have hright : ∀ q ∈ W ψ x t, ⁅ψ z, q⁆ ∈ W ψ x (Magma.mul z t) := by
                intro q hq
                refine Submodule.span_induction
                  (p := fun y _ => ⁅ψ z, y⁆ ∈ W ψ x (Magma.mul z t)) ?_ ?_ ?_ ?_ hq
                · rintro m ⟨c, hG, rfl⟩
                  obtain ⟨hcH, hcms, a, b, hcab, hcfol⟩ := hG
                  have hxc : Magma.foliage x < Magma.foliage c := by
                    have : Magma.foliage a < Magma.foliage c := by
                      rw [hcab, Magma.foliage_mul]
                      exact fol_lt_append (Magma.foliage_ne_nil b)
                    exact lt_of_le_of_lt hcfol this
                  have hms_zc : (Magma.foliage z : Multiset X) + (Magma.foliage c : Multiset X) =
                      (Magma.foliage x : Multiset X) +
                        (Magma.foliage (Magma.mul z t) : Multiset X) := by
                    rw [hcms, Magma.foliage_mul, ← Multiset.coe_add]
                    ac_rfl
                  rcases eq_or_ne z c with rfl | hzc
                  · rw [lie_self]; exact Submodule.zero_mem _
                  · rcases lt_trichotomy (Magma.foliage z) (Magma.foliage c) with h' | h' | h'
                    · have hsmall : pmeas z c < n :=
                        lt_of_lt_of_eq (pmeas_lt_of_perm_aux hms_zc hxz) hmeas
                      exact W_mono ψ hms_zc (le_of_lt hxz) (IH z c hz hcH h' hsmall)
                    · exact absurd (hall_foliage_injective_aux hz hcH h') hzc
                    · have hms_cz : (Magma.foliage c : Multiset X) + (Magma.foliage z : Multiset X) =
                          (Magma.foliage x : Multiset X) +
                            (Magma.foliage (Magma.mul z t) : Multiset X) := by
                        exact (add_comm (Magma.foliage c : Multiset X)
                          (Magma.foliage z : Multiset X)).trans hms_zc
                      have hsmall : pmeas c z < n :=
                        lt_of_lt_of_eq (pmeas_lt_of_perm_aux hms_cz hxc) hmeas
                      have hmem : ⁅ψ c, ψ z⁆ ∈ W ψ c z := IH c z hcH hz h' hsmall
                      rw [show ⁅ψ z, ψ c⁆ = -⁅ψ c, ψ z⁆ from (lie_skew (ψ z) (ψ c)).symm]
                      exact Submodule.neg_mem _ (W_mono ψ hms_cz (le_of_lt hxc) hmem)
                · rw [lie_zero]; exact Submodule.zero_mem _
                · intro p q _ _ hp' hq'
                  rw [lie_add]; exact Submodule.add_mem _ hp' hq'
                · intro r p _ hp'
                  rw [lie_zsmul]; exact Submodule.smul_mem _ r hp'
              exact hright _ (IH x t hx ht hxt hshort_xt)
  intro x y hx hy hlt
  exact key (pmeas x y) x y hx hy hlt rfl

/-! ## The assembly -/

/-- The target submodule: the `ℤ`-span of the values of `ψ` on Hall trees. -/
abbrev Vspan (ψ : Magma X → M) : Submodule ℤ M :=
  Submodule.span ℤ (Set.range (fun h : {h : Magma X // IsHall h} => ψ h.1))

lemma W_le_Vspan (ψ : Magma X → M) (x y : Magma X) {m : M} (hm : m ∈ W ψ x y) :
    m ∈ Vspan ψ := by
  revert hm
  refine Submodule.span_induction (p := fun z _ => z ∈ Vspan ψ) ?_ ?_ ?_ ?_
  · rintro m ⟨c, hcH, rfl⟩
    exact Submodule.subset_span (show ψ c ∈ Set.range
        (fun h : {h : Magma X // IsHall h} => ψ h.1) from ⟨⟨c, hcH.1⟩, rfl⟩)
  · exact Submodule.zero_mem _
  · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
  · intro r a _ ha; exact Submodule.smul_mem _ r ha

lemma bracket_hall_mem (ψ : Magma X → M)
    (hψ : ∀ a b : Magma X, ψ (Magma.mul a b) = ⁅ψ a, ψ b⁆) (x y : Magma X)
    (hx : IsHall x) (hy : IsHall y) : ⁅ψ x, ψ y⁆ ∈ Vspan ψ := by
  rcases eq_or_ne x y with rfl | hne
  · rw [lie_self]; exact Submodule.zero_mem _
  · rcases lt_trichotomy (Magma.foliage x) (Magma.foliage y) with h | h | h
    · exact W_le_Vspan ψ x y (pair_mem ψ hψ x y hx hy h)
    · exact absurd (hall_foliage_injective_aux hx hy h) hne
    · rw [(lie_skew (ψ x) (ψ y)).symm]
      exact Submodule.neg_mem _ (W_le_Vspan ψ y x (pair_mem ψ hψ y x hy hx h))

lemma bracket_mem_Vspan (ψ : Magma X → M)
    (hψ : ∀ a b : Magma X, ψ (Magma.mul a b) = ⁅ψ a, ψ b⁆) {p q : M}
    (hp : p ∈ Vspan ψ) (hq : q ∈ Vspan ψ) : ⁅p, q⁆ ∈ Vspan ψ := by
  have key : ∀ p ∈ Vspan ψ, ∀ q ∈ Vspan ψ, ⁅p, q⁆ ∈ Vspan ψ := by
    intro p hp
    refine Submodule.span_induction
      (p := fun x _ => ∀ q ∈ Vspan ψ, ⁅x, q⁆ ∈ Vspan ψ) ?_ ?_ ?_ ?_ hp
    · rintro m ⟨h, rfl⟩ q hq
      refine Submodule.span_induction
        (p := fun y _ => ⁅ψ h.1, y⁆ ∈ Vspan ψ) ?_ ?_ ?_ ?_ hq
      · rintro m' ⟨h', rfl⟩
        exact bracket_hall_mem ψ hψ h.1 h'.1 h.2 h'.2
      · rw [lie_zero]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb; rw [lie_add]; exact Submodule.add_mem _ ha hb
      · intro r a _ ha; rw [lie_zsmul]; exact Submodule.smul_mem _ r ha
    · intro q _; rw [zero_lie]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb q hq; rw [add_lie]; exact Submodule.add_mem _ (ha q hq) (hb q hq)
    · intro r a _ ha q hq; rw [zsmul_lie]; exact Submodule.smul_mem _ r (ha q hq)
  exact key p hp q hq

lemma psi_mem_Vspan (ψ : Magma X → M)
    (hψ : ∀ a b : Magma X, ψ (Magma.mul a b) = ⁅ψ a, ψ b⁆) (w : Magma X) :
    ψ w ∈ Vspan ψ := by
  have key : ∀ n : ℕ, ∀ w : Magma X, Magma.size w = n → ψ w ∈ Vspan ψ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro w hw
      cases w with
      | gen x => exact Submodule.subset_span (Set.mem_range_self
          (f := fun h : {h : Magma X // IsHall h} => ψ h.1) ⟨Magma.gen x, isHall_gen x⟩)
      | mul a b =>
        rw [hψ a b]
        refine bracket_mem_Vspan ψ hψ ?_ ?_
        · exact ih (Magma.size a) (by rw [← hw]; exact Magma.size_left_lt a b) a rfl
        · exact ih (Magma.size b) (by rw [← hw]; exact Magma.size_right_lt a b) b rfl
  exact key (Magma.size w) w rfl

lemma hall_spanning {X : Type*} [LinearOrder X] {M : Type*} [LieRing M] (ψ : Magma X → M)
    (hψ : ∀ a b : Magma X, ψ (Magma.mul a b) = ⁅ψ a, ψ b⁆) (w : Magma X) :
    ψ w ∈ Submodule.span ℤ (Set.range (fun h : {h : Magma X // IsHall h} => ψ h.1)) :=
  psi_mem_Vspan ψ hψ w

end Work.SSGRoute.prop5.witt
