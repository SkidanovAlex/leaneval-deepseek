import Mathlib
import Submission.Variational
import Submission.SimplexMono
import Submission.Commons.Combinatorics.Embedding.sum_preimage_expOf

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

open Finset
open scoped BigOperators

/-!
# The labelled/symmetric bridge: `Slab α β k = θ(α)·θ(β)·Ssum α β k`

`Submission.SimplexMono` defines the *labelled* assignment sum

  `Slab α β k = Σ_{e : Fin α.length ↪ Fin k} Σ_{e' : Fin β.length ↪ Fin k}
      ∏_c (expOf α k e c + expOf β k e' c)!`,

while `Submission.Variational` defines the *computable* recursion `Ssum` (the sum over
*profiles*, i.e. over the multiplicity patterns of the placements).  The two differ by the
number of placements realising a given profile, which is

  `θ(α) = ∏_v (α.count v)!`,

because an injective placement is precisely a bijection between the entries of `α` and the
nonempty coordinates of its profile, matching values.

The plan (SESSION 47 §3(B4)) is

* `Slab α β k = θ(α)·θ(β)·Tsum α β k`, where `Tsum` is the double sum over profiles
  (from the commons `Combinatorics/Embedding/sum_preimage_expOf`), and
* `Tsum α β k = Ssum α β k`, by induction on `k`, splitting the profile sum at the last
  coordinate (`Fintype.piFinset` + `Fin.snoc`) and matching `Ssum`'s recursion.
-/

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

/-- `θ(α) = ∏_v (α.count v)!`: the number of injective placements realising a given profile. -/
def theta (α : List ℕ) : ℕ := ∏ v ∈ α.toFinset, (α.count v).factorial

/-- `f : Fin k → ℕ` is a *profile* of `α` on `k` coordinates: every part of `α` occurs as a value
of `f` with the same multiplicity, and every nonzero value of `f` is a part of `α`. -/
def IsProfile (α : List ℕ) {k : ℕ} (f : Fin k → ℕ) : Prop :=
  (∀ v ∈ α.toFinset, (Finset.univ.filter (fun c : Fin k => f c = v)).card = α.count v) ∧
    (∀ c : Fin k, f c = 0 ∨ f c ∈ α)

/-- The profile condition is decidable (it is a conjunction of finite quantifications). -/
instance (α : List ℕ) (k : ℕ) : DecidablePred (IsProfile α (k := k)) := fun f =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- The "clean" (unbounded) characterization of the profile condition. -/
theorem isProfile_iff (α : List ℕ) (hα : 0 ∉ α) {k : ℕ} (f : Fin k → ℕ) :
    IsProfile α f ↔
      ∀ v : ℕ, v ≠ 0 → (Finset.univ.filter (fun c : Fin k => f c = v)).card = α.count v := by
  constructor
  · rintro ⟨h1, h2⟩ v hv
    by_cases hv' : v ∈ α.toFinset
    · exact h1 v hv'
    · have hcnt : α.count v = 0 := by
        rw [List.count_eq_zero]
        intro hmem
        exact hv' (List.mem_toFinset.mpr hmem)
      have hzero : (Finset.univ.filter (fun c : Fin k => f c = v)).card = 0 := by
        rw [Finset.card_eq_zero]
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        intro hc
        rcases h2 c with h0 | hmem
        · exact hv (hc ▸ h0)
        · exact hv' (List.mem_toFinset.mpr (hc ▸ hmem))
      rw [hzero, hcnt]
  · intro h
    refine ⟨fun v hv => h v ?_, fun c => ?_⟩
    · intro h0
      exact hα (List.mem_toFinset.mp (h0 ▸ hv))
    · by_contra hc
      rw [not_or] at hc
      obtain ⟨hc1, hc2⟩ := hc
      have h3 := h (f c) hc1
      rw [List.count_eq_zero.mpr hc2] at h3
      have h4 : 0 < (Finset.univ.filter (fun c' : Fin k => f c' = f c)).card :=
        Finset.card_pos.mpr ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, rfl⟩⟩
      exact absurd (h3 ▸ h4) (Nat.lt_irrefl 0)

/-! ## Count bookkeeping for `eraseOne`, `List.count` and `Fin.snoc` -/

theorem count_cons_eq (a v : ℕ) (t : List ℕ) :
    (a :: t).count v = t.count v + (if a = v then 1 else 0) := by
  by_cases h : a = v
  · subst h
    rw [if_pos rfl, List.count_cons_self]
  · rw [if_neg h, List.count_cons_of_ne (b := a) (a := v) h, add_zero]

theorem eraseOne_cons_self (a : ℕ) (t : List ℕ) : eraseOne (a :: t) a = t := by
  rw [eraseOne]; exact if_pos rfl

theorem eraseOne_cons_of_ne {a p : ℕ} (h : a ≠ p) (t : List ℕ) :
    eraseOne (a :: t) p = a :: eraseOne t p := by
  rw [eraseOne]; exact if_neg h

theorem count_eraseOne (α : List ℕ) (p v : ℕ) (hp : p ∈ α) :
    α.count v = (eraseOne α p).count v + (if v = p then 1 else 0) := by
  induction α with
  | nil => exact absurd hp (by simp)
  | cons a t ih =>
      by_cases hap : a = p
      · subst hap
        rw [eraseOne_cons_self, count_cons_eq]
        congr 1
        by_cases h : a = v
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (fun hc => h hc.symm)]
      · have hpt : p ∈ t := by
          rcases List.mem_cons.mp hp with h | h
          · exact absurd h.symm hap
          · exact h
        rw [eraseOne_cons_of_ne hap, count_cons_eq, count_cons_eq, ih hpt]
        omega

theorem eraseOne_eq_self_of_notMem (α : List ℕ) (p : ℕ) (h : p ∉ α) : eraseOne α p = α := by
  induction α with
  | nil => rfl
  | cons a t ih =>
      have hap : a ≠ p := fun hc => h (List.mem_cons.mpr (Or.inl hc.symm))
      rw [eraseOne_cons_of_ne hap]
      congr 1
      exact ih (fun hc => h (List.mem_cons.mpr (Or.inr hc)))

theorem count_eraseOne_zero (α : List ℕ) (h0 : 0 ∉ α) (v : ℕ) (hv : v ≠ 0) :
    α.count v = (eraseOne α 0).count v := by
  rw [eraseOne_eq_self_of_notMem α 0 h0]

theorem eraseOne_length_add (α : List ℕ) (p : ℕ) (hp : p ∈ α) :
    (eraseOne α p).length + 1 = α.length := by
  induction α with
  | nil => exact absurd hp (by simp)
  | cons a t ih =>
      by_cases hap : a = p
      · subst hap
        rw [eraseOne_cons_self, List.length_cons]
      · have hpt : p ∈ t := by
          rcases List.mem_cons.mp hp with h | h
          · exact absurd h.symm hap
          · exact h
        rw [eraseOne_cons_of_ne hap, List.length_cons, List.length_cons, ih hpt]

theorem eraseOne_sum_add (α : List ℕ) (p : ℕ) (hp : p ∈ α) :
    (eraseOne α p).sum + p = α.sum := by
  induction α with
  | nil => exact absurd hp (by simp)
  | cons a t ih =>
      by_cases hap : a = p
      · subst hap
        rw [eraseOne_cons_self, List.sum_cons]
        omega
      · have hpt : p ∈ t := by
          rcases List.mem_cons.mp hp with h | h
          · exact absurd h.symm hap
          · exact h
        rw [eraseOne_cons_of_ne hap, List.sum_cons, List.sum_cons, Nat.add_assoc, ih hpt]


theorem eraseOne_notMem_zero (α : List ℕ) (hα : 0 ∉ α) (p : ℕ) : 0 ∉ eraseOne α p := by
  induction α with
  | nil => simp [eraseOne]
  | cons a t ih =>
      have h0t : 0 ∉ t := fun h => hα (List.mem_cons.mpr (Or.inr h))
      by_cases hap : a = p
      · subst hap
        rw [eraseOne_cons_self]
        exact h0t
      · rw [eraseOne_cons_of_ne hap]
        intro h
        rcases List.mem_cons.mp h with h1 | h2
        · exact hα (List.mem_cons.mpr (Or.inl h1))
        · exact ih h0t h2

/-! ## Splitting at the last coordinate -/

/-- Append a value at the last coordinate. -/
def snocFun {k : ℕ} (f : Fin k → ℕ) (p : ℕ) : Fin (k+1) → ℕ :=
  Fin.snoc (α := fun _ : Fin (k+1) => ℕ) f p

theorem snocFun_castSucc {k : ℕ} (f : Fin k → ℕ) (p : ℕ) (i : Fin k) :
    snocFun f p i.castSucc = f i := Fin.snoc_castSucc _ _ _

theorem snocFun_last {k : ℕ} (f : Fin k → ℕ) (p : ℕ) :
    snocFun f p (Fin.last k) = p := Fin.snoc_last _ _

theorem card_filter_snoc {k : ℕ} (f : Fin k → ℕ) (p v : ℕ) :
    (Finset.univ.filter (fun c : Fin (k+1) => snocFun f p c = v)).card
      = (Finset.univ.filter (fun i : Fin k => f i = v)).card + (if p = v then 1 else 0) := by
  rw [Finset.card_filter, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by rw [snocFun_castSucc])
  · rw [snocFun_last]

/-- **The profile condition is compatible with `Fin.snoc`.**  Appending the value `p` at the last
coordinate turns a profile of `eraseOne α p` into a profile of `α` exactly when `p` is a part of
`α` (or `p = 0`, i.e. the last coordinate is empty). -/
theorem isProfile_snoc {k : ℕ} (α : List ℕ) (hα : 0 ∉ α) (p : ℕ) (f : Fin k → ℕ) :
    IsProfile α (snocFun f p) ↔ (p = 0 ∨ p ∈ α) ∧ IsProfile (eraseOne α p) f := by
  rw [isProfile_iff _ hα, isProfile_iff _ (eraseOne_notMem_zero α hα p)]
  constructor
  · intro h
    have hp : p = 0 ∨ p ∈ α := by
      by_contra hc
      rw [not_or] at hc
      obtain ⟨hp0, hpa⟩ := hc
      have hc1 := h p hp0
      rw [card_filter_snoc, if_pos rfl, List.count_eq_zero.mpr hpa] at hc1
      omega
    refine ⟨hp, fun v hv => ?_⟩
    have hc1 := h v hv
    rw [card_filter_snoc] at hc1
    rcases hp with rfl | hpa
    · rw [count_eraseOne_zero α hα v hv, if_neg (fun h : (0:ℕ) = v => hv h.symm), add_zero] at hc1
      exact hc1
    · rw [count_eraseOne α p v hpa] at hc1
      rw [show (if p = v then 1 else 0) = (if v = p then 1 else 0) from by
        by_cases h : p = v
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (fun hc => h hc.symm)]] at hc1
      exact Nat.add_right_cancel hc1
  · rintro ⟨hp, hf⟩ v hv
    rw [card_filter_snoc]
    rcases hp with rfl | hpa
    · rw [count_eraseOne_zero α hα v hv, if_neg (fun h : (0:ℕ) = v => hv h.symm), add_zero]
      exact hf v hv
    · rw [count_eraseOne α p v hpa, hf v hv]
      by_cases h : p = v
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun hc => h hc.symm)]

/-! ## The range-bounded profile set and the type-function sum -/

/-- The profiles of `α` on `k` coordinates, with all coordinates bounded by `N`. -/
def profileSet (N : ℕ) (α : List ℕ) (k : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset (fun _ : Fin k => Finset.range (N + 1))).filter (IsProfile α)

/-- The type-function sum: the sum over pairs of profiles of `α`, `β` of `∏_c (f c + g c)!`. -/
def TsumR (N : ℕ) (α β : List ℕ) (k : ℕ) : ℕ :=
  ∑ f ∈ profileSet N α k, ∑ g ∈ profileSet N β k, ∏ c : Fin k, (f c + g c).factorial

theorem mem_profileSet {N : ℕ} {α : List ℕ} {k : ℕ} {f : Fin k → ℕ} :
    f ∈ profileSet N α k ↔ (∀ c, f c ≤ N) ∧ IsProfile α f := by
  rw [profileSet, Finset.mem_filter, Fintype.mem_piFinset]
  simp only [Finset.mem_range]
  exact ⟨fun h => ⟨fun c => Nat.lt_succ_iff.mp (h.1 c), h.2⟩,
    fun h => ⟨fun c => Nat.lt_succ_of_le (h.1 c), h.2⟩⟩

theorem snocFun_injective {k : ℕ} (p : ℕ) : Function.Injective (fun f : Fin k → ℕ => snocFun f p) := by
  intro f g h
  have h' : snocFun f p = snocFun g p := h
  funext i
  have h1 := congrFun h' i.castSucc
  rwa [snocFun_castSucc, snocFun_castSucc] at h1

theorem prod_snoc {k : ℕ} (f g : Fin k → ℕ) (p q : ℕ) :
    (∏ c : Fin (k+1), (snocFun f p c + snocFun g q c).factorial)
      = (p + q).factorial * ∏ c : Fin k, (f c + g c).factorial := by
  rw [Fin.prod_univ_castSucc]
  simp only [snocFun_castSucc, snocFun_last]
  ring

theorem pairwiseDisjoint_profileImage (N k : ℕ) (α : List ℕ) :
    (↑((0 :: α.dedup).toFinset) : Set ℕ).PairwiseDisjoint
      (fun p => (profileSet N (eraseOne α p) k).image (fun f => snocFun f p)) := by
  rw [Finset.pairwiseDisjoint_iff]
  intro p hp q hq hne
  rcases hne with ⟨x, hx⟩
  rw [Finset.mem_inter, Finset.mem_image, Finset.mem_image] at hx
  obtain ⟨⟨f1, -, hf1⟩, ⟨f2, -, hf2⟩⟩ := hx
  have h1 : p = x (Fin.last k) := by
    have hc := congrFun hf1 (Fin.last k)
    rwa [snocFun_last] at hc
  have h2 : q = x (Fin.last k) := by
    have hc := congrFun hf2 (Fin.last k)
    rwa [snocFun_last] at hc
  rw [h1, h2]

/-- **The profile set, split at the last coordinate.** -/
theorem profileSet_succ (N k : ℕ) (α : List ℕ) (hα : 0 ∉ α) (hN : α.sum ≤ N) :
    profileSet N α (k+1)
      = (0 :: α.dedup).toFinset.biUnion
          (fun p => (profileSet N (eraseOne α p) k).image (fun f => snocFun f p)) := by
  refine Finset.ext (fun f => ?_)
  simp only [Finset.mem_biUnion, Finset.mem_image]
  constructor
  · intro hf
    rw [mem_profileSet] at hf
    obtain ⟨hbox, hprof⟩ := hf
    refine ⟨f (Fin.last k), ?_, Fin.init f, ?_, ?_⟩
    · rw [List.mem_toFinset, List.mem_cons]
      rcases hprof.2 (Fin.last k) with h0 | hmem
      · exact Or.inl h0
      · exact Or.inr (List.mem_dedup.mpr hmem)
    · rw [mem_profileSet]
      refine ⟨fun i => ?_, ?_⟩
      · exact hbox i.castSucc
      · have hsn : snocFun (Fin.init f) (f (Fin.last k)) = f := by
          funext j
          exact congrFun (Fin.snoc_init_self f) j
        have h2 : IsProfile α (snocFun (Fin.init f) (f (Fin.last k))) := by
          rw [hsn]; exact hprof
        exact ((isProfile_snoc α hα (f (Fin.last k)) (Fin.init f)).mp h2).2
    · have hsn : snocFun (Fin.init f) (f (Fin.last k)) = f := by
        funext j
        exact congrFun (Fin.snoc_init_self f) j
      exact hsn
  · rintro ⟨p, hp, f', hf', rfl⟩
    rw [mem_profileSet] at hf'
    obtain ⟨hbox, hprof⟩ := hf'
    rw [List.mem_toFinset, List.mem_cons] at hp
    have hp' : p = 0 ∨ p ∈ α := by
      rcases hp with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_dedup.mp h)
    rw [mem_profileSet]
    refine ⟨fun j => ?_, ?_⟩
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
      · rw [snocFun_castSucc]; exact hbox i
      · rw [snocFun_last]
        rcases hp' with h | h
        · rw [h]; exact Nat.zero_le _
        · exact le_trans (List.le_sum_of_mem h) hN
    · exact (isProfile_snoc α hα p f').mpr ⟨hp', hprof⟩

/-- Splitting a sum over the profiles of `β` at the last coordinate. -/
theorem sum_profileSet_succ (N k : ℕ) (β : List ℕ) (hβ : 0 ∉ β) (hNβ : β.sum ≤ N)
    (G : (Fin (k+1) → ℕ) → ℕ) :
    (∑ g ∈ profileSet N β (k+1), G g)
      = ∑ q ∈ (0 :: β.dedup).toFinset,
          ∑ g' ∈ profileSet N (eraseOne β q) k, G (snocFun g' q) := by
  rw [profileSet_succ N k β hβ hNβ, Finset.sum_biUnion (pairwiseDisjoint_profileImage N k β)]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [Finset.sum_image ((snocFun_injective q).injOn)]

/-- **The recursion for the type-function sum**, in the shape of `Ssum`'s recursion. -/
theorem TsumR_succ (N k : ℕ) (α β : List ℕ) (hα : 0 ∉ α) (hβ : 0 ∉ β)
    (hNα : α.sum ≤ N) (hNβ : β.sum ≤ N) :
    TsumR N α β (k+1)
      = ∑ p ∈ (0 :: α.dedup).toFinset, ∑ q ∈ (0 :: β.dedup).toFinset,
          (p + q).factorial * TsumR N (eraseOne α p) (eraseOne β q) k := by
  have step1 : TsumR N α β (k+1)
      = ∑ p ∈ (0 :: α.dedup).toFinset, ∑ f' ∈ profileSet N (eraseOne α p) k,
          ∑ g ∈ profileSet N β (k+1),
            ∏ c : Fin (k+1), (snocFun f' p c + g c).factorial := by
    rw [TsumR, sum_profileSet_succ N k α hα hNα]
  have step2 : (∑ p ∈ (0 :: α.dedup).toFinset, ∑ f' ∈ profileSet N (eraseOne α p) k,
          ∑ g ∈ profileSet N β (k+1),
            ∏ c : Fin (k+1), (snocFun f' p c + g c).factorial)
      = ∑ p ∈ (0 :: α.dedup).toFinset, ∑ f' ∈ profileSet N (eraseOne α p) k,
          ∑ q ∈ (0 :: β.dedup).toFinset, ∑ g' ∈ profileSet N (eraseOne β q) k,
            ∏ c : Fin (k+1), (snocFun f' p c + snocFun g' q c).factorial := by
    refine Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun f' hf' => ?_))
    exact sum_profileSet_succ N k β hβ hNβ
      (fun g => ∏ c : Fin (k+1), (snocFun f' p c + g c).factorial)
  have step3 : (∑ p ∈ (0 :: α.dedup).toFinset, ∑ f' ∈ profileSet N (eraseOne α p) k,
          ∑ q ∈ (0 :: β.dedup).toFinset, ∑ g' ∈ profileSet N (eraseOne β q) k,
            ∏ c : Fin (k+1), (snocFun f' p c + snocFun g' q c).factorial)
      = ∑ p ∈ (0 :: α.dedup).toFinset, ∑ f' ∈ profileSet N (eraseOne α p) k,
          ∑ q ∈ (0 :: β.dedup).toFinset, ∑ g' ∈ profileSet N (eraseOne β q) k,
            (p + q).factorial * ∏ c : Fin k, (f' c + g' c).factorial := by
    refine Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun f' hf' =>
      Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (fun g' hg' => ?_))))
    rw [prod_snoc]
  have step4 : (∑ p ∈ (0 :: α.dedup).toFinset, ∑ f' ∈ profileSet N (eraseOne α p) k,
          ∑ q ∈ (0 :: β.dedup).toFinset, ∑ g' ∈ profileSet N (eraseOne β q) k,
            (p + q).factorial * ∏ c : Fin k, (f' c + g' c).factorial)
      = ∑ p ∈ (0 :: α.dedup).toFinset, ∑ q ∈ (0 :: β.dedup).toFinset,
          (p + q).factorial * TsumR N (eraseOne α p) (eraseOne β q) k := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [TsumR, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun f'' hf'' => ?_)
    rw [Finset.mul_sum]
  exact step1.trans (step2.trans (step3.trans step4))

/-! ## `TsumR` satisfies `Ssum`'s recursion -/

theorem foldl_add_sum_general {α : Type*} (L : List α) (g : α → ℕ) (c : ℕ) :
    L.foldl (fun acc x => acc + g x) c = c + (L.map g).sum := by
  induction L generalizing c with
  | nil => simp
  | cons a t ih =>
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem foldl_product_eq_sum {l m : List ℕ} (hl : l.Nodup) (hm : m.Nodup)
    (g : ℕ → ℕ → ℕ) :
    (l ×ˢ m).foldl (fun acc pq => acc + g pq.1 pq.2) 0
      = ∑ p ∈ l.toFinset, ∑ q ∈ m.toFinset, g p q := by
  rw [foldl_add_sum_general, zero_add]
  rw [← List.sum_toFinset (fun pq : ℕ × ℕ => g pq.1 pq.2) (hl.product hm)]
  have hset : (l ×ˢ m).toFinset = l.toFinset ×ˢ m.toFinset := by
    ext x
    rw [List.mem_toFinset, List.mem_product, Finset.mem_product, List.mem_toFinset,
      List.mem_toFinset]
  rw [hset, Finset.sum_product]

theorem eraseOne_sum_le (α : List ℕ) (p : ℕ) : (eraseOne α p).sum ≤ α.sum := by
  by_cases hp : p ∈ α
  · have h := eraseOne_sum_add α p hp
    omega
  · rw [eraseOne_eq_self_of_notMem α p hp]

theorem nodup_dedup_cons (α : List ℕ) (hα : 0 ∉ α) : (0 :: α.dedup).Nodup := by
  rw [List.nodup_cons]
  exact ⟨fun hc => hα (List.mem_dedup.mp hc), List.nodup_dedup α⟩

theorem isProfile_fin_zero {γ : List ℕ} (hγ : 0 ∉ γ) (f : Fin 0 → ℕ) :
    IsProfile γ f ↔ γ = [] := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil γ hne
    have hmem : a ∈ γ.toFinset := List.mem_toFinset.mpr ha
    have h1 := h.1 a hmem
    have h2 : (Finset.univ.filter (fun c : Fin 0 => f c = a)).card = 0 := by
      rw [Finset.card_eq_zero]
      ext c
      exact Fin.elim0 c
    rw [h2] at h1
    have h3 : 0 < γ.count a := List.count_pos_iff.mpr ha
    omega
  · rintro rfl
    exact ⟨fun v hv => absurd (List.not_mem_nil hv) (by simp), fun c => Fin.elim0 c⟩

theorem piFinset_fin_zero (B : ℕ) :
    Fintype.piFinset (fun _ : Fin 0 => Finset.range (B + 1)) = Finset.univ := by
  refine Finset.eq_univ_of_forall (fun f => ?_)
  rw [Fintype.mem_piFinset]
  intro i
  exact Fin.elim0 i

/-- **`TsumR` computes `Ssum`.** -/
theorem TsumR_eq_Ssum (B : ℕ) :
    ∀ (k : ℕ) (α β : List ℕ), 0 ∉ α → 0 ∉ β → α.sum ≤ B → β.sum ≤ B →
      TsumR B α β k = Ssum α β k := by
  intro k
  induction k with
  | zero =>
      intro α β hα hβ _ _
      rw [TsumR]
      have hpe : ∀ γ : List ℕ,
          profileSet B γ 0 = (Finset.univ : Finset (Fin 0 → ℕ)).filter (IsProfile γ) := by
        intro γ
        rw [profileSet, piFinset_fin_zero]
      rw [hpe α, hpe β]
      have hα0 : (Finset.univ : Finset (Fin 0 → ℕ)).filter (IsProfile α)
          = if α = [] then Finset.univ else ∅ := by
        by_cases h : α = []
        · rw [if_pos h]
          exact Finset.filter_true_of_mem (fun f _ => (isProfile_fin_zero hα f).mpr h)
        · rw [if_neg h]
          refine Finset.filter_eq_empty_iff.mpr (fun f _ => ?_)
          rw [isProfile_fin_zero hα f]
          exact fun hc => h hc
      have hβ0 : (Finset.univ : Finset (Fin 0 → ℕ)).filter (IsProfile β)
          = if β = [] then Finset.univ else ∅ := by
        by_cases h : β = []
        · rw [if_pos h]
          exact Finset.filter_true_of_mem (fun f _ => (isProfile_fin_zero hβ f).mpr h)
        · rw [if_neg h]
          refine Finset.filter_eq_empty_iff.mpr (fun f _ => ?_)
          rw [isProfile_fin_zero hβ f]
          exact fun hc => h hc
      rw [hα0, hβ0]
      rw [show Ssum α β 0 = if α = [] ∧ β = [] then 1 else 0 from rfl]
      split_ifs <;> simp_all
  | succ k ih =>
      intro α β hα hβ hBα hBβ
      rw [TsumR_succ B k α β hα hβ hBα hBβ]
      rw [show Ssum α β (k+1) = ((0 :: α.dedup) ×ˢ (0 :: β.dedup)).foldl
            (fun acc pq => acc + (pq.1 + pq.2).factorial *
              Ssum (eraseOne α pq.1) (eraseOne β pq.2) k) 0 from rfl]
      rw [foldl_product_eq_sum (nodup_dedup_cons α hα) (nodup_dedup_cons β hβ)
        (fun p q => (p + q).factorial * Ssum (eraseOne α p) (eraseOne β q) k)]
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
      rw [ih (eraseOne α p) (eraseOne β q) (eraseOne_notMem_zero α hα p)
        (eraseOne_notMem_zero β hβ q)
        (le_trans (eraseOne_sum_le α p) hBα) (le_trans (eraseOne_sum_le β q) hBβ)]

/-! ## Range independence and the `Slab` bridge -/

theorem profileSet_mono {M N k : ℕ} {γ : List ℕ} (hMN : M ≤ N) :
    profileSet M γ k ⊆ profileSet N γ k := by
  intro f hf
  rw [mem_profileSet] at hf ⊢
  exact ⟨fun c => le_trans (hf.1 c) hMN, hf.2⟩

/-- The profile set does not depend on the box bound `N`, as long as `N ≥ γ.sum`. -/
theorem profileSet_range {M N k : ℕ} {γ : List ℕ} (hM : γ.sum ≤ M) (hMN : M ≤ N) :
    profileSet N γ k = profileSet M γ k := by
  refine Finset.Subset.antisymm (fun f hf => ?_) (profileSet_mono hMN)
  rw [mem_profileSet] at hf ⊢
  refine ⟨fun c => ?_, hf.2⟩
  rcases hf.2.2 c with h0 | hmem
  · rw [h0]; exact Nat.zero_le _
  · exact le_trans (List.le_sum_of_mem hmem) hM

theorem TsumR_range {M N : ℕ} {α β : List ℕ} (hMα : α.sum ≤ M) (hMβ : β.sum ≤ M)
    (hMN : M ≤ N) (k : ℕ) : TsumR N α β k = TsumR M α β k := by
  rw [TsumR, TsumR, profileSet_range hMα hMN, profileSet_range hMβ hMN]

theorem Slab_eq_theta_mul (B : ℕ) (α β : List ℕ) (hα : 0 ∉ α) (hβ : 0 ∉ β)
    (hBα : α.sum ≤ B) (hBβ : β.sum ≤ B) (k : ℕ) :
    Slab α β k = theta α * theta β * Ssum α β k := by
  have hmain : Slab α β k = theta α * (∑ f ∈ profileSet (α.sum) α k,
      theta β * ∑ g ∈ profileSet (β.sum) β k, ∏ c : Fin k, (f c + g c).factorial) := by
    rw [Slab]
    have hlhs : (∑ e : Fin α.length ↪ Fin k, ∑ e' : Fin β.length ↪ Fin k,
          ∏ c : Fin k, (expOf α k e c + expOf β k e' c).factorial)
        = ∑ e : Fin α.length ↪ Fin k,
            (fun f => ∑ e' : Fin β.length ↪ Fin k,
              ∏ c : Fin k, (f c + expOf β k e' c).factorial)
              (fun c => ∑ i : Fin α.length, if e i = c then α.get i else 0) := rfl
    rw [hlhs]
    rw [Commons.Combinatorics.Embedding.sum_preimage_expOf (k := k) α hα
      (fun f => ∑ e' : Fin β.length ↪ Fin k, ∏ c : Fin k, (f c + expOf β k e' c).factorial)]
    rw [← Finset.sum_filter]
    refine congrArg (fun x => theta α * x) ?_
    refine Finset.sum_congr rfl (fun f hf => ?_)
    have hb1 : (∑ e' : Fin β.length ↪ Fin k,
          ∏ c : Fin k, (f c + expOf β k e' c).factorial)
        = ∑ e' : Fin β.length ↪ Fin k,
            (fun g => ∏ c : Fin k, (f c + g c).factorial)
              (fun c => ∑ i : Fin β.length, if e' i = c then β.get i else 0) := rfl
    rw [hb1, Commons.Combinatorics.Embedding.sum_preimage_expOf (k := k) β hβ
      (fun g => ∏ c : Fin k, (f c + g c).factorial), ← Finset.sum_filter]
    have hfe : (Fintype.piFinset (fun _ : Fin k => Finset.range (β.sum + 1))).filter
        (fun a => (∀ v ∈ β.toFinset,
            (Finset.univ.filter (fun c : Fin k => a c = v)).card = β.count v)
          ∧ (∀ c : Fin k, a c = 0 ∨ a c ∈ β)) = profileSet (β.sum) β k :=
      Finset.filter_congr (fun a _ => Iff.rfl)
    rw [hfe, theta]
  have hT : TsumR B α β k = ∑ f ∈ profileSet (α.sum) α k,
      ∑ g ∈ profileSet (β.sum) β k, ∏ c : Fin k, (f c + g c).factorial := by
    rw [TsumR, profileSet_range (M := α.sum) (N := B) (le_refl _) hBα,
      profileSet_range (M := β.sum) (N := B) (le_refl _) hBβ]
  rw [hmain, ← Finset.mul_sum, hT.symm, TsumR_eq_Ssum B k α β hα hβ hBα hBβ, mul_assoc]

end

end Commons.NumberTheory.MaynardSieve
