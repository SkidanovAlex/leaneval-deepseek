import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Perm
import Submission.Commons.Analysis.Complex.jensenCarleman

open Finset
open scoped BigOperators


namespace Commons.Combinatorics.Embedding

theorem list_count_eq_card_filter_get (l : List ℕ) (v : ℕ) :
    l.count v = (Finset.univ.filter (fun i : Fin l.length => l.get i = v)).card := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.count_cons]
    change l.count v + (if (a == v) = true then 1 else 0) =
        (Finset.univ.filter (fun i : Fin (l.length + 1) => (a :: l).get i = v)).card
    rw [Fin.card_filter_univ_succ']
    rw [ih]
    by_cases h : a = v
    · simp [h]; omega
    · simp [h, beq_iff_eq]

variable {k : ℕ}

/-- The profile of an injective placement `e` of the entries of `α`. -/
def expOf (α : List ℕ) (e : Fin α.length ↪ Fin k) (c : Fin k) : ℕ :=
  ∑ i : Fin α.length, if e i = c then α.get i else 0

lemma expOf_self (α : List ℕ) (e : Fin α.length ↪ Fin k) (i : Fin α.length) :
    expOf α e (e i) = α.get i := by
  unfold expOf
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg]
    intro h; exact hj (e.injective h)
  · intro h; exact absurd (Finset.mem_univ i) h

lemma expOf_eq_zero_of_forall_ne (α : List ℕ) (e : Fin α.length ↪ Fin k) (c : Fin k)
    (h : ∀ i, e i ≠ c) : expOf α e c = 0 := by
  unfold expOf
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg (h i)]

lemma expOf_eq_zero_or_mem (α : List ℕ) (e : Fin α.length ↪ Fin k) (c : Fin k) :
    expOf α e c = 0 ∨ expOf α e c ∈ α := by
  by_cases h : ∃ i, e i = c
  · right
    obtain ⟨i, hi⟩ := h
    have : expOf α e c = α.get i := by
      unfold expOf
      rw [Finset.sum_eq_single i]
      · rw [if_pos hi]
      · intro j _ hj
        rw [if_neg]
        intro hjc; exact hj (e.injective (hjc.trans hi.symm))
      · intro hm; exact absurd (Finset.mem_univ i) hm
    rw [this]
    exact List.get_mem α i
  · left
    exact expOf_eq_zero_of_forall_ne α e c (fun i hi => h ⟨i, hi⟩)

/-- Positions of the value `v` in `α`. -/
def fibP (α : List ℕ) (v : ℕ) : Finset (Fin α.length) :=
  Finset.univ.filter (fun i : Fin α.length => α.get i = v)

/-- Coordinates where `f` takes the value `v`. -/
def fibQ (f : Fin k → ℕ) (v : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun c : Fin k => f c = v)

lemma mem_fibP {α : List ℕ} {v : ℕ} {i : Fin α.length} :
    i ∈ fibP α v ↔ α.get i = v := by
  simp [fibP]

lemma mem_fibQ {f : Fin k → ℕ} {v : ℕ} {c : Fin k} :
    c ∈ fibQ f v ↔ f c = v := by
  simp [fibQ]

lemma fibP_card (α : List ℕ) (v : ℕ) : (fibP α v).card = α.count v := by
  rw [fibP, ← list_count_eq_card_filter_get]

noncomputable def fibreToFun (α : List ℕ) (hα : 0 ∉ α) (f : Fin k → ℕ)
    (e : Fin α.length ↪ Fin k) (he : ∀ c, expOf α e c = f c)
    (v : {v // v ∈ α.toFinset}) : ↥(fibP α v.val) ≃ ↥(fibQ f v.val) :=
  Equiv.ofBijective
    (fun x : ↥(fibP α v.val) => ⟨e x.val, by
      have hx : α.get x.val = v.val := (Finset.mem_filter.mp x.property).2
      simp only [fibQ, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← he (e x.val), expOf_self, hx]⟩)
    (by
      refine ⟨?_, ?_⟩
      · intro x y hxy
        apply Subtype.ext
        exact e.injective (Subtype.ext_iff.mp hxy)
      · intro c
        have hc : f c.val = v.val := (Finset.mem_filter.mp c.property).2
        have hv0 : v.val ≠ 0 := fun h => hα (h ▸ List.mem_toFinset.mp v.property)
        have hne : expOf α e c.val ≠ 0 := by rw [he c.val, hc]; exact hv0
        have hex : ∃ i, e i = c.val := by
          by_contra hno
          exact hne (expOf_eq_zero_of_forall_ne α e c.val (fun i hi => hno ⟨i, hi⟩))
        obtain ⟨i, hi⟩ := hex
        refine ⟨⟨i, ?_⟩, ?_⟩
        · rw [mem_fibP]
          rw [← expOf_self α e i, hi, he c.val, hc]
        · exact Subtype.ext hi)

noncomputable def fibreInvFun (α : List ℕ) (f : Fin k → ℕ)
    (g : (v : {v // v ∈ α.toFinset}) → ↥(fibP α v.val) ≃ ↥(fibQ f v.val)) :
    Fin α.length → Fin k :=
  fun i => (g ⟨α.get i, List.mem_toFinset.mpr (List.get_mem α i)⟩
              ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩).val

lemma f_fibreInvFun (α : List ℕ) (f : Fin k → ℕ)
    (g : (v : {v // v ∈ α.toFinset}) → ↥(fibP α v.val) ≃ ↥(fibQ f v.val))
    (i : Fin α.length) : f (fibreInvFun α f g i) = α.get i := by
  unfold fibreInvFun
  exact (Finset.mem_filter.mp (g ⟨α.get i, List.mem_toFinset.mpr (List.get_mem α i)⟩
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩).property).2

lemma fibreInvFun_eq_apply (α : List ℕ) (f : Fin k → ℕ)
    (g : (v : {v // v ∈ α.toFinset}) → ↥(fibP α v.val) ≃ ↥(fibQ f v.val))
    (v : {v // v ∈ α.toFinset}) (i : Fin α.length) (hi : i ∈ fibP α v.val) :
    fibreInvFun α f g i = (g v ⟨i, hi⟩).val := by
  have hx : α.get i = v.val := mem_fibP.mp hi
  have h1 : (⟨α.get i, List.mem_toFinset.mpr (List.get_mem α i)⟩ : {v // v ∈ α.toFinset}) = v :=
    Subtype.ext hx
  subst h1
  rfl

lemma fibreInvFun_injective (α : List ℕ) (f : Fin k → ℕ)
    (g : (v : {v // v ∈ α.toFinset}) → ↥(fibP α v.val) ≃ ↥(fibQ f v.val)) :
    Function.Injective (fibreInvFun α f g) := by
  intro i j hij
  have hw : α.get i = α.get j :=
    (f_fibreInvFun α f g i).symm.trans ((congrArg f hij).trans (f_fibreInvFun α f g j))
  have hiP : i ∈ fibP α (α.get i) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hjP : j ∈ fibP α (α.get i) := by rw [mem_fibP]; exact hw.symm
  have h2 : fibreInvFun α f g i = (g ⟨α.get i, List.mem_toFinset.mpr (List.get_mem α i)⟩ ⟨i, hiP⟩).val :=
    fibreInvFun_eq_apply α f g ⟨α.get i, List.mem_toFinset.mpr (List.get_mem α i)⟩ i hiP
  have h3 : fibreInvFun α f g j = (g ⟨α.get i, List.mem_toFinset.mpr (List.get_mem α i)⟩ ⟨j, hjP⟩).val :=
    fibreInvFun_eq_apply α f g ⟨α.get i, List.mem_toFinset.mpr (List.get_mem α i)⟩ j hjP
  have h4 : (g ⟨α.get i, List.mem_toFinset.mpr (List.get_mem α i)⟩ ⟨i, hiP⟩)
      = (g ⟨α.get i, List.mem_toFinset.mpr (List.get_mem α i)⟩ ⟨j, hjP⟩) :=
    Subtype.ext (h2.symm.trans (hij.trans h3))
  exact Subtype.ext_iff.mp ((g ⟨α.get i, List.mem_toFinset.mpr (List.get_mem α i)⟩).injective h4)

noncomputable def fibreInvEmb (α : List ℕ) (f : Fin k → ℕ)
    (g : (v : {v // v ∈ α.toFinset}) → ↥(fibP α v.val) ≃ ↥(fibQ f v.val)) :
    Fin α.length ↪ Fin k :=
  Function.Embedding.mk (fibreInvFun α f g) (fibreInvFun_injective α f g)

lemma image_fibreInvFun_subset (α : List ℕ) (f : Fin k → ℕ)
    (g : (v : {v // v ∈ α.toFinset}) → ↥(fibP α v.val) ≃ ↥(fibQ f v.val)) (v : ℕ) :
    (fibP α v).image (fibreInvFun α f g) ⊆ fibQ f v := by
  intro c hc
  rw [Finset.mem_image] at hc
  obtain ⟨i, hiP, rfl⟩ := hc
  rw [mem_fibQ, f_fibreInvFun α f g i]
  exact mem_fibP.mp hiP

lemma fibQ_subset_image (α : List ℕ) (f : Fin k → ℕ)
    (g : (v : {v // v ∈ α.toFinset}) → ↥(fibP α v.val) ≃ ↥(fibQ f v.val))
    (hcond1 : ∀ v ∈ α.toFinset, (fibQ f v).card = α.count v)
    (v : {v // v ∈ α.toFinset}) :
    fibQ f v.val ⊆ (fibP α v.val).image (fibreInvFun α f g) := by
  have hsub := image_fibreInvFun_subset α f g v.val
  have hcard : ((fibP α v.val).image (fibreInvFun α f g)).card = (fibQ f v.val).card := by
    rw [Finset.card_image_of_injective _ (fibreInvFun_injective α f g), fibP_card,
      hcond1 v.val v.property]
  rw [Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)]

lemma expOf_fibreInvFun (α : List ℕ) (hα : 0 ∉ α) (f : Fin k → ℕ)
    (g : (v : {v // v ∈ α.toFinset}) → ↥(fibP α v.val) ≃ ↥(fibQ f v.val))
    (hcond1 : ∀ v ∈ α.toFinset, (fibQ f v).card = α.count v)
    (hcond2 : ∀ c : Fin k, f c = 0 ∨ f c ∈ α) :
    ∀ c, expOf α (fibreInvEmb α f g) c = f c := by
  intro c
  by_cases hc : f c = 0
  · rw [hc]
    apply expOf_eq_zero_of_forall_ne
    intro i hi
    have hi' : fibreInvFun α f g i = c := hi
    have h1 : f (fibreInvFun α f g i) = 0 := by rw [hi']; exact hc
    have h2 : f (fibreInvFun α f g i) = α.get i := f_fibreInvFun α f g i
    have h3 : α.get i ≠ 0 := fun h0 => hα (h0 ▸ List.get_mem α i)
    exact h3 (h2.symm.trans h1)
  · have hmem : f c ∈ α.toFinset := List.mem_toFinset.mpr ((hcond2 c).resolve_left hc)
    have hcin : c ∈ (fibP α (f c)).image (fibreInvFun α f g) :=
      fibQ_subset_image α f g hcond1 ⟨f c, hmem⟩ (by rw [mem_fibQ])
    rw [Finset.mem_image] at hcin
    obtain ⟨i, hiP, hie⟩ := hcin
    have hie' : fibreInvEmb α f g i = c := hie
    rw [← hie', expOf_self]
    exact (f_fibreInvFun α f g i).symm

noncomputable def fibreEquiv (α : List ℕ) (hα : 0 ∉ α) (f : Fin k → ℕ)
    (hcond1 : ∀ v ∈ α.toFinset, (fibQ f v).card = α.count v)
    (hcond2 : ∀ c : Fin k, f c = 0 ∨ f c ∈ α) :
    {e : Fin α.length ↪ Fin k // ∀ c, expOf α e c = f c} ≃
      ((v : {v // v ∈ α.toFinset}) → ↥(fibP α v.val) ≃ ↥(fibQ f v.val)) :=
  { toFun := fun e v => fibreToFun α hα f e.val e.property v
    invFun := fun g => ⟨fibreInvEmb α f g, expOf_fibreInvFun α hα f g hcond1 hcond2⟩
    left_inv := by
      intro e
      apply Subtype.ext
      apply Function.Embedding.ext
      intro i
      rfl
    right_inv := by
      intro g
      funext v
      apply Equiv.ext
      intro x
      apply Subtype.ext
      exact fibreInvFun_eq_apply α f g v x.val x.property }

lemma fibQ_expOf_eq_image (α : List ℕ) (hα : 0 ∉ α) (e : Fin α.length ↪ Fin k)
    (v : {v // v ∈ α.toFinset}) :
    fibQ (expOf α e) v.val = Finset.image e (fibP α v.val) := by
  ext c
  rw [mem_fibQ, Finset.mem_image]
  constructor
  · intro hc
    have hv0 : v.val ≠ 0 := fun h => hα (h ▸ List.mem_toFinset.mp v.property)
    have hne : expOf α e c ≠ 0 := by rw [hc]; exact hv0
    by_contra hni
    have hzero : expOf α e c = 0 := by
      apply expOf_eq_zero_of_forall_ne
      intro i hi
      exact hni ⟨i, by rw [mem_fibP, ← expOf_self α e i, hi, hc], hi⟩
    exact hne hzero
  · rintro ⟨i, hiP, hic⟩
    rw [← hic, expOf_self]
    exact mem_fibP.mp hiP

lemma cond1_of_mem (α : List ℕ) (hα : 0 ∉ α) (f : Fin k → ℕ) (e : Fin α.length ↪ Fin k)
    (he : ∀ c, expOf α e c = f c) : ∀ v ∈ α.toFinset, (fibQ f v).card = α.count v := by
  intro v hv
  have h1 : fibQ f v = fibQ (expOf α e) v := by
    ext c
    rw [mem_fibQ, mem_fibQ, he c]
  rw [h1, fibQ_expOf_eq_image α hα e ⟨v, hv⟩,
    Finset.card_image_of_injective _ e.injective, fibP_card]

lemma cond2_of_mem (α : List ℕ) (f : Fin k → ℕ) (e : Fin α.length ↪ Fin k)
    (he : ∀ c, expOf α e c = f c) : ∀ c, f c = 0 ∨ f c ∈ α := by
  intro c
  have h := expOf_eq_zero_or_mem α e c
  rwa [he c] at h

lemma card_equiv_fibP_fibQ (α : List ℕ) (f : Fin k → ℕ)
    (hcond1 : ∀ v ∈ α.toFinset, (fibQ f v).card = α.count v)
    (v : {v // v ∈ α.toFinset}) :
    Fintype.card (↥(fibP α v.val) ≃ ↥(fibQ f v.val)) = (α.count v.val).factorial := by
  have hcard : Fintype.card ↥(fibP α v.val) = Fintype.card ↥(fibQ f v.val) := by
    rw [Fintype.card_coe, Fintype.card_coe, fibP_card, hcond1 v.val v.property]
  rw [Fintype.card_equiv (Fintype.equivOfCardEq hcard), Fintype.card_coe, fibP_card]

/-- **The fibre of the profile map of an injective placement.**

For a list `α` of nonzero natural numbers and a function `f : Fin k → ℕ`, the number of injective
placements `e : Fin α.length ↪ Fin k` whose induced profile `c ↦ Σ_i [e i = c] · α_i` equals `f`
is `∏ v ∈ α.toFinset, (α.count v)!` when every nonzero value of `f` lies in `α` and occurs in `f`
with the multiplicity with which it occurs in `α`; and it is `0` otherwise.

(As a function of the profile, the placement map is `∏_v (α.count v)!`-to-one onto the profiles
of `α`: an injective placement is exactly a bijection between the entries of `α` and the nonzero
coordinates of its profile, matching values.)

⚠ `0 ∉ α` is needed: the parts placed at the coordinates are recovered from their values, so a
zero part would be invisible. -/
theorem card_preimage_expOf {k : ℕ} (α : List ℕ) (hα : 0 ∉ α) (f : Fin k → ℕ) :
    (Finset.univ.filter (fun e : Fin α.length ↪ Fin k =>
      ∀ c : Fin k, (∑ i : Fin α.length, if e i = c then α.get i else 0) = f c)).card
      = if ((∀ v ∈ α.toFinset, (Finset.univ.filter (fun c : Fin k => f c = v)).card = α.count v)
          ∧ (∀ c : Fin k, f c = 0 ∨ f c ∈ α))
        then ∏ v ∈ α.toFinset, (α.count v).factorial else 0 := by
  change (Finset.univ.filter (fun e : Fin α.length ↪ Fin k => ∀ c, expOf α e c = f c)).card
      = if ((∀ v ∈ α.toFinset, (fibQ f v).card = α.count v) ∧ (∀ c : Fin k, f c = 0 ∨ f c ∈ α))
        then ∏ v ∈ α.toFinset, (α.count v).factorial else 0
  by_cases hcond : (∀ v ∈ α.toFinset, (fibQ f v).card = α.count v)
      ∧ (∀ c : Fin k, f c = 0 ∨ f c ∈ α)
  · rw [if_pos hcond]
    obtain ⟨hcond1, hcond2⟩ := hcond
    rw [← Fintype.card_subtype (p := fun e : Fin α.length ↪ Fin k => ∀ c, expOf α e c = f c)]
    rw [Fintype.card_congr (fibreEquiv α hα f hcond1 hcond2)]
    rw [Fintype.card_pi]
    rw [Finset.univ_eq_attach]
    rw [Finset.prod_congr rfl (fun v _ => card_equiv_fibP_fibQ α f hcond1 v)]
    exact Finset.prod_attach (α.toFinset) (fun v => (α.count v).factorial)
  · rw [if_neg hcond]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e _ he
    exact hcond ⟨cond1_of_mem α hα f e he, cond2_of_mem α f e he⟩

end Commons.Combinatorics.Embedding