import Mathlib
import Submission.Work.SSGRoute.prop5.magnusLieDefs
import Submission.Work.SSGRoute.prop5.magnusGroupPart
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Magnus leading term of an element of `γ_j` lies in the nested span

For the free group `F = FreeGroup X` and its lower central series (Mathlib indexing
`(⊤ : Subgroup F).lowerCentralSeries k` for the paper's `γ_{k+1}`), the leading term
`magLead (j+1) z` of an element `z ∈ γ_j` is the image modulo `fil X (j+1)` of an element of the
"nested span" `nestedSpan X j` (the `ℤ`-span of the left-nested bracket monomials `lnMon w`,
`|w| = j`).

The proof is an induction on `j`:
* `γ_j = ⁅γ_{j-1}, ⊤⁆` is the closure of the commutators `⁅u,v⁆`, `u ∈ γ_{j-1}`, `v ∈ F`;
* the degree-`j` component of `magLead` is additive on `γ_j` and converts a group commutator
  `⁅u,v⁆` into the ring commutator of the degree components of `u` and `v` (``magLead_commutator``);
* the nested span is closed under the ring commutator (`nestedSpan_bracket_le`).

The extraction of the degree components is done with the projection `degPart j` of
`FreeAssoc X = ℤ[FreeMonoid X]` onto the words of length `j`.
-/

noncomputable section

set_option maxHeartbeats 8000000

open scoped commutatorElement
attribute [local instance] Classical.propDecidable

namespace Work.SSGRoute.prop5

variable {X : Type*}

/-! ## The degree projection of the free associative algebra -/

/-- The projection of `FreeAssoc X = ℤ[FreeMonoid X]` onto the words of length `j` (the "degree
`j` part"). -/
noncomputable def degPart (j : ℕ) : FreeAssoc X →ₗ[ℤ] FreeAssoc X where
  toFun a := MonoidAlgebra.ofCoeff (Finsupp.filter (fun w : FreeMonoid X => w.length = j) a.coeff)
  map_add' a b := by
    apply MonoidAlgebra.ext
    ext w
    show (MonoidAlgebra.ofCoeff (Finsupp.filter (fun w : FreeMonoid X => w.length = j)
      (a + b).coeff)).coeff w = _
    rw [MonoidAlgebra.coeff_add, Finsupp.filter_add, Finsupp.add_apply]
    rfl
  map_smul' c a := by
    apply MonoidAlgebra.ext
    ext w
    show (MonoidAlgebra.ofCoeff (Finsupp.filter (fun w : FreeMonoid X => w.length = j)
      (c • a).coeff)).coeff w = _
    rw [MonoidAlgebra.coeff_smul, Finsupp.filter_smul, Finsupp.smul_apply]
    rfl

theorem coeff_degPart (j : ℕ) (a : FreeAssoc X) (w : FreeMonoid X) :
    (degPart (X:=X) j a).coeff w = if w.length = j then a.coeff w else 0 := by
  show (MonoidAlgebra.ofCoeff (Finsupp.filter (fun w : FreeMonoid X => w.length = j)
    a.coeff)).coeff w = _
  rw [Finsupp.filter_apply]

theorem coeff_single_fa (w v : FreeMonoid X) (r : ℤ) :
    (MonoidAlgebra.single w r : FreeAssoc X).coeff v = if v = w then r else 0 := by
  rw [MonoidAlgebra.coeff_single]
  by_cases h : v = w
  · subst h; rw [if_pos rfl, Finsupp.single_eq_same]
  · rw [if_neg h, Finsupp.single_eq_of_ne h]

theorem degPart_single (j : ℕ) (w : FreeMonoid X) (r : ℤ) :
    degPart (X:=X) j (MonoidAlgebra.single w r)
      = if w.length = j then MonoidAlgebra.single w r else 0 := by
  apply MonoidAlgebra.ext; ext v
  rw [coeff_degPart, coeff_single_fa]
  have hR : ((if w.length = j then (MonoidAlgebra.single w r : FreeAssoc X) else 0)).coeff v
      = (if w.length = j then (if v = w then r else 0) else 0) := by
    by_cases h : w.length = j
    · rw [if_pos h, if_pos h, coeff_single_fa]
    · rw [if_neg h, if_neg h, MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  rw [hR]
  by_cases hv : v = w
  · subst hv; rfl
  · rw [if_neg hv]
    by_cases hw : w.length = j
    · rw [if_pos hw]; split_ifs <;> rfl
    · rw [if_neg hw]; split_ifs <;> rfl

theorem degPart_wordEl (j : ℕ) (w : List X) :
    degPart (X:=X) j (wordEl w) = if w.length = j then wordEl w else 0 := by
  rw [wordEl, degPart_single]
  rfl

theorem single_mem_wordSpan {j : ℕ} {w : FreeMonoid X} (h : w.length = j) (r : ℤ) :
    MonoidAlgebra.single w r ∈ wordSpan (X:=X) j := by
  rw [show MonoidAlgebra.single w r = r • MonoidAlgebra.single w (1:ℤ) by
    rw [MonoidAlgebra.smul_single']; simp]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨FreeMonoid.toList w, h, by rw [wordEl, FreeMonoid.ofList_toList]⟩

theorem degPart_mem_wordSpan (j : ℕ) (a : FreeAssoc X) :
    degPart (X:=X) j a ∈ wordSpan (X:=X) j := by
  have hsum := Finsupp.sum_of_support_subset (degPart (X:=X) j a).coeff
      (s := (degPart (X:=X) j a).coeff.support) (Finset.Subset.refl _)
      (fun w r => MonoidAlgebra.single w r) (fun i hi => by simp)
  rw [show (degPart (X:=X) j a).coeff.sum (fun w r => MonoidAlgebra.single w r) =
      degPart (X:=X) j a from MonoidAlgebra.sum_coeff_single _] at hsum
  rw [hsum]
  refine Submodule.sum_mem _ (fun w hw => ?_)
  have hwj : w.length = j := by
    by_contra hw'
    exact (Finsupp.mem_support_iff.mp hw) (by rw [coeff_degPart, if_neg hw'])
  exact single_mem_wordSpan hwj ((degPart (X:=X) j a).coeff w)

theorem mem_wordSpan_iff (j : ℕ) (a : FreeAssoc X) :
    a ∈ wordSpan (X:=X) j ↔ ∀ w : FreeMonoid X, w.length ≠ j → a.coeff w = 0 := by
  constructor
  · intro h
    refine Submodule.span_induction (p := fun a _ => ∀ w, w.length ≠ j → a.coeff w = 0)
      ?_ ?_ ?_ ?_ h
    · rintro a ⟨u, hu, rfl⟩ w hw
      rw [wordEl, coeff_single_fa, if_neg]
      intro h'
      exact hw (by rw [h']; exact hu)
    · intro w hw; rw [MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    · intro x y _ _ hx hy w hw
      rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, hx w hw, hy w hw, add_zero]
    · intro c x _ hx w hw
      rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, hx w hw, smul_zero]
  · intro h
    have hsum := Finsupp.sum_of_support_subset a.coeff (s := a.coeff.support) (Finset.Subset.refl _)
        (fun w r => MonoidAlgebra.single w r) (fun i hi => by simp)
    rw [show a.coeff.sum (fun w r => MonoidAlgebra.single w r) = a
        from MonoidAlgebra.sum_coeff_single _] at hsum
    rw [hsum]
    refine Submodule.sum_mem _ (fun w hw => ?_)
    have hwj : w.length = j := by
      by_contra hw'
      exact (Finsupp.mem_support_iff.mp hw) (h w hw')
    exact single_mem_wordSpan hwj (a.coeff w)

theorem degPart_eq_self_of_mem_wordSpan {j : ℕ} {a : FreeAssoc X} (ha : a ∈ wordSpan (X:=X) j) :
    degPart (X:=X) j a = a := by
  apply MonoidAlgebra.ext; ext w
  rw [coeff_degPart]
  by_cases h : w.length = j
  · rw [if_pos h]
  · rw [if_neg h, (mem_wordSpan_iff j a).mp ha w h]

theorem wordSpan_mul_mem {p q : ℕ} {a b : FreeAssoc X}
    (ha : a ∈ wordSpan (X:=X) p) (hb : b ∈ wordSpan (X:=X) q) :
    a * b ∈ wordSpan (X:=X) (p+q) := by
  refine Submodule.span_induction₂ (p := fun a b _ _ => a * b ∈ wordSpan (X:=X) (p+q))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha hb
  · rintro x y ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    rw [wordEl, wordEl, MonoidAlgebra.single_mul_single, mul_one]
    rw [show MonoidAlgebra.single (FreeMonoid.ofList u * FreeMonoid.ofList v) (1:ℤ)
        = wordEl (u ++ v) by rw [wordEl, FreeMonoid.ofList_append]]
    exact Submodule.subset_span ⟨u ++ v, by rw [List.length_append, hu, hv], rfl⟩
  · intro y hy; rw [zero_mul]; exact Submodule.zero_mem _
  · intro x hx; rw [mul_zero]; exact Submodule.zero_mem _
  · intro x y z hx hy hz h1 h2; rw [add_mul]; exact Submodule.add_mem _ h1 h2
  · intro x y z hx hy hz h1 h2; rw [mul_add]; exact Submodule.add_mem _ h1 h2
  · intro r x y hx hy h; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h
  · intro r x y hx hy h; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h

theorem mem_fil_of_mem_wordSpan {j : ℕ} {a : FreeAssoc X} (h : a ∈ wordSpan (X:=X) j) :
    a ∈ fil X j := by
  rw [wordSpan] at h
  rw [fil_eq_filI]
  change a ∈ Submodule.span ℤ (filgen X j)
  exact (Submodule.span_le.mpr (by
    rintro a ⟨u, hu, rfl⟩
    exact Submodule.subset_span ⟨FreeMonoid.ofList u,
      by rw [show (FreeMonoid.ofList u).length = u.length from rfl, hu], rfl⟩)) h

theorem degPart_eq_zero_of_mem_fil {N j : ℕ} {a : FreeAssoc X} (h : a ∈ fil X N) (hN : j < N) :
    degPart (X:=X) j a = 0 := by
  rw [fil_eq_filI] at h
  change a ∈ Submodule.span ℤ (filgen X N) at h
  refine Submodule.span_induction (p := fun a _ => degPart (X:=X) j a = 0) ?_ ?_ ?_ ?_ h
  · rintro a ⟨w, hw, rfl⟩
    rw [degPart_single, if_neg (by omega)]
  · exact map_zero _
  · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
  · intro c x _ hx; rw [map_smul, hx, smul_zero]

theorem sub_degPart_mem_fil {p : ℕ} {a : FreeAssoc X} (h : a ∈ fil X p) :
    a - degPart (X:=X) p a ∈ fil X (p+1) := by
  rw [fil_eq_filI] at h ⊢
  change a ∈ Submodule.span ℤ (filgen X p) at h
  change a - degPart (X:=X) p a ∈ Submodule.span ℤ (filgen X (p+1))
  refine Submodule.span_induction (p := fun a _ => a - degPart (X:=X) p a ∈
      Submodule.span ℤ (filgen X (p+1))) ?_ ?_ ?_ ?_ h
  · rintro a ⟨w, hw, rfl⟩
    rw [degPart_single]
    by_cases hwj : w.length = p
    · rw [if_pos hwj, sub_self]; exact Submodule.zero_mem _
    · rw [if_neg hwj, sub_zero]
      exact Submodule.subset_span ⟨w, by omega, rfl⟩
  · rw [map_zero, sub_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    rw [show x + y - (degPart (X:=X) p x + degPart (X:=X) p y)
        = (x - degPart (X:=X) p x) + (y - degPart (X:=X) p y) from by abel]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [map_smul]
    rw [show c • x - c • degPart (X:=X) p x = c • (x - degPart (X:=X) p x)
        from by rw [smul_sub]]
    exact Submodule.smul_mem _ c hx

theorem degPart_mul_of_mem_fil {p q : ℕ} {a b : FreeAssoc X}
    (ha : a ∈ fil X p) (hb : b ∈ fil X q) :
    degPart (X:=X) (p+q) (a * b) = degPart (X:=X) p a * degPart (X:=X) q b := by
  have ha' : a - degPart (X:=X) p a ∈ fil X (p+1) := sub_degPart_mem_fil ha
  have hb' : b - degPart (X:=X) q b ∈ fil X (q+1) := sub_degPart_mem_fil hb
  have hdpa : degPart (X:=X) p a ∈ fil X p := mem_fil_of_mem_wordSpan (degPart_mem_wordSpan p a)
  have hdqb : degPart (X:=X) q b ∈ fil X q := mem_fil_of_mem_wordSpan (degPart_mem_wordSpan q b)
  have hrest : a * b - degPart (X:=X) p a * degPart (X:=X) q b ∈ fil X (p+q+1) := by
    have heq : a * b - degPart (X:=X) p a * degPart (X:=X) q b
        = degPart (X:=X) p a * (b - degPart (X:=X) q b) + (a - degPart (X:=X) p a) * b := by
      noncomm_ring
    rw [heq]
    refine Submodule.add_mem _ ?_ ?_
    · exact fil_mul_le X p (q+1) (Ideal.mul_mem_mul hdpa hb')
    · have h := fil_mul_le X (p+1) q (Ideal.mul_mem_mul ha' hb)
      rwa [show (p+1)+q = p+q+1 from by omega] at h
  have h1 : degPart (X:=X) (p+q) (a * b - degPart (X:=X) p a * degPart (X:=X) q b) = 0 :=
    degPart_eq_zero_of_mem_fil hrest (by omega)
  have h2 : degPart (X:=X) (p+q) (a * b)
      = degPart (X:=X) (p+q) (degPart (X:=X) p a * degPart (X:=X) q b) := by
    rw [map_sub] at h1
    exact sub_eq_zero.mp h1
  rw [h2, degPart_eq_self_of_mem_wordSpan
    (wordSpan_mul_mem (degPart_mem_wordSpan p a) (degPart_mem_wordSpan q b))]

/-! ## The nested span is closed under the ring commutator -/

/-- The fold `alFold` appends a letter on the right by bracketing. -/
theorem alFold_append_singleton (a : FreeAssoc X) (u : List X) (y : X) :
    alFold a (u ++ [y]) = alFold a u * wordEl [y] - wordEl [y] * alFold a u := by
  rw [alFold, List.foldl_append, alFold]; simp

/-- `lnMon` on a word with one more letter on the right. -/
theorem lnMon_append_singleton (x : X) (u : List X) (y : X) :
    lnMon (x :: (u ++ [y])) = lnMon (x :: u) * wordEl [y] - wordEl [y] * lnMon (x :: u) := by
  rw [lnMon_eq_alFold, lnMon_eq_alFold, alFold_append_singleton]

/-- Bracketing an element of `nestedSpan p` on the right by a generator stays in
`nestedSpan (p+1)`. -/
theorem nestedSpan_bracket_word (p : ℕ) {a : FreeAssoc X}
    (ha : a ∈ nestedSpan (X:=X) p) (y : X) :
    a * wordEl [y] - wordEl [y] * a ∈ nestedSpan (X:=X) (p+1) := by
  refine Submodule.span_induction
    (p := fun a _ => a * wordEl [y] - wordEl [y] * a ∈ nestedSpan (X:=X) (p+1)) ?_ ?_ ?_ ?_ ha
  · rintro a ⟨w, hw, rfl⟩
    rcases w with _ | ⟨x, rest⟩
    · show (0 : FreeAssoc X) * wordEl [y] - wordEl [y] * 0 ∈ nestedSpan (X:=X) (p+1)
      rw [zero_mul, mul_zero, sub_self]; exact Submodule.zero_mem _
    · refine Submodule.subset_span ⟨x :: (rest ++ [y]), ?_, (lnMon_append_singleton x rest y).symm⟩
      simp only [List.length_cons, List.length_append, List.length_nil] at hw ⊢
      omega
  · rw [zero_mul, mul_zero, sub_self]; exact Submodule.zero_mem _
  · intro x z _ _ hx hz
    rw [show (x + z) * wordEl [y] - wordEl [y] * (x + z)
        = (x * wordEl [y] - wordEl [y] * x) + (z * wordEl [y] - wordEl [y] * z)
        from by noncomm_ring]
    exact Submodule.add_mem _ hx hz
  · intro c x _ hx
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
    exact Submodule.smul_mem _ c hx

/-- The key induction: bracketing an element of `nestedSpan p` by a left-nested bracket `lnMon v`
stays in `nestedSpan (p + |v|)`. -/
theorem nestedSpan_bracket_lnMon : ∀ v : List X, ∀ (p : ℕ) (a : FreeAssoc X),
    a ∈ nestedSpan (X:=X) p →
    a * lnMon v - lnMon v * a ∈ nestedSpan (X:=X) (p + v.length) := by
  intro v
  induction v using List.reverseRecOn with
  | nil =>
      intro p a _
      rw [show lnMon (X:=X) ([] : List X) = 0 from rfl, List.length_nil, Nat.add_zero]
      rw [mul_zero, zero_mul, sub_self]; exact Submodule.zero_mem _
  | append_singleton u y ihv =>
      intro p a ha
      rcases u with _ | ⟨x, rest⟩
      · rw [List.nil_append]
        show a * wordEl [y] - wordEl [y] * a ∈ nestedSpan (X:=X) (p + 1)
        exact nestedSpan_bracket_word p ha y
      · change a * lnMon (x :: (rest ++ [y])) - lnMon (x :: (rest ++ [y])) * a ∈
          nestedSpan (X:=X) (p + (x :: (rest ++ [y])).length)
        have h1 : a * lnMon (x :: rest) - lnMon (x :: rest) * a
            ∈ nestedSpan (X:=X) (p + (x :: rest).length) := ihv p a ha
        have h1' : (a * lnMon (x :: rest) - lnMon (x :: rest) * a) * wordEl [y]
            - wordEl [y] * (a * lnMon (x :: rest) - lnMon (x :: rest) * a)
            ∈ nestedSpan (X:=X) (p + (x :: rest).length + 1) :=
          nestedSpan_bracket_word _ h1 y
        have hW : a * wordEl [y] - wordEl [y] * a ∈ nestedSpan (X:=X) (p+1) :=
          nestedSpan_bracket_word p ha y
        have h2 : (a * wordEl [y] - wordEl [y] * a) * lnMon (x :: rest)
            - lnMon (x :: rest) * (a * wordEl [y] - wordEl [y] * a)
            ∈ nestedSpan (X:=X) ((p+1) + (x :: rest).length) := ihv (p+1) _ hW
        have h3 : lnMon (x :: rest) * (a * wordEl [y] - wordEl [y] * a)
            - (a * wordEl [y] - wordEl [y] * a) * lnMon (x :: rest)
            ∈ nestedSpan (X:=X) (p + (x :: rest).length + 1) := by
          have := neg_mem h2
          rwa [show (p+1) + (x :: rest).length = p + (x :: rest).length + 1 from by omega,
            show - ((a * wordEl [y] - wordEl [y] * a) * lnMon (x :: rest)
                - lnMon (x :: rest) * (a * wordEl [y] - wordEl [y] * a))
              = lnMon (x :: rest) * (a * wordEl [y] - wordEl [y] * a)
                - (a * wordEl [y] - wordEl [y] * a) * lnMon (x :: rest) from by noncomm_ring] at this
        rw [lnMon_append_singleton x rest y]
        rw [show (x :: (rest ++ [y])).length = (x :: rest).length + 1 from by simp]
        rw [show a * (lnMon (x :: rest) * wordEl [y] - wordEl [y] * lnMon (x :: rest))
              - (lnMon (x :: rest) * wordEl [y] - wordEl [y] * lnMon (x :: rest)) * a
            = ((a * lnMon (x :: rest) - lnMon (x :: rest) * a) * wordEl [y]
                - wordEl [y] * (a * lnMon (x :: rest) - lnMon (x :: rest) * a))
              + (lnMon (x :: rest) * (a * wordEl [y] - wordEl [y] * a)
                - (a * wordEl [y] - wordEl [y] * a) * lnMon (x :: rest)) from by noncomm_ring]
        exact Submodule.add_mem _ h1' h3

/-- **The nested span is closed under the ring commutator.** -/
theorem nestedSpan_bracket_le {p q : ℕ} {a b : FreeAssoc X}
    (ha : a ∈ nestedSpan (X:=X) p) (hb : b ∈ nestedSpan (X:=X) q) :
    a * b - b * a ∈ nestedSpan (X:=X) (p+q) := by
  refine Submodule.span_induction₂
    (p := fun a b _ _ => a * b - b * a ∈ nestedSpan (X:=X) (p+q)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha hb
  · rintro x y ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    have := nestedSpan_bracket_lnMon v p (lnMon u) (Submodule.subset_span ⟨u, hu, rfl⟩)
    rwa [hv] at this
  · intro y _
    rw [zero_mul, mul_zero, sub_self]; exact Submodule.zero_mem _
  · intro x _
    rw [mul_zero, zero_mul, sub_self]; exact Submodule.zero_mem _
  · intro x y z _ _ _ h1 h2
    rw [show (x + y) * z - z * (x + y)
        = (x * z - z * x) + (y * z - z * y) from by noncomm_ring]
    exact Submodule.add_mem _ h1 h2
  · intro x y z _ _ _ h1 h2
    rw [show x * (y + z) - (y + z) * x
        = (x * y - y * x) + (x * z - z * x) from by noncomm_ring]
    exact Submodule.add_mem _ h1 h2
  · intro r x y _ _ h
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
    exact Submodule.smul_mem _ r h
  · intro r x y _ _ h
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
    exact Submodule.smul_mem _ r h

/-! ## The main induction -/

/-- The degree-`1` part of the free associative algebra is contained in the nested span. -/
theorem wordSpan_one_le_nestedSpan : wordSpan (X:=X) 1 ≤ nestedSpan (X:=X) 1 := by
  rw [wordSpan, nestedSpan]
  refine Submodule.span_le.mpr ?_
  rintro a ⟨u, hu, rfl⟩
  obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hu
  exact Submodule.subset_span ⟨[x], rfl, rfl⟩

/-- **The main induction.**  For `z ∈ γ_j` (`j = m+1`) and any lift `a ∈ fil X j` of the leading
term `magLead N z` (with `N ≥ j+1`), the degree-`j` component `degPart j a` lies in the nested
span. -/
theorem degPart_mem_nestedSpan_of_magLead : ∀ j : ℕ, 1 ≤ j → ∀ (N : ℕ), j+1 ≤ N →
    ∀ z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j-1),
    ∀ a : FreeAssoc X, a ∈ fil X j →
      Ideal.Quotient.mk (fil X N) a = magLead N z →
        degPart (X:=X) j a ∈ nestedSpan (X:=X) j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ m ih =>
      intro hm1 N hN z hz a ha haeq
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · -- base case `j = 1`
        subst hm0
        exact wordSpan_one_le_nestedSpan (degPart_mem_wordSpan 1 a)
      · -- step `j = m+1`, `m ≥ 1`
        have hzclos : z ∈ Subgroup.closure {g : FreeGroup X |
            ∃ g1 ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (m-1),
            ∃ g2 ∈ (⊤ : Subgroup (FreeGroup X)), ⁅g1, g2⁆ = g} := by
          rw [← Subgroup.commutator_def, ← Subgroup.lowerCentralSeries_succ (n := m - 1),
            show m - 1 + 1 = m from by omega]
          exact hz
        have hmem_of : ∀ z ∈ Subgroup.closure {g : FreeGroup X |
              ∃ g1 ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (m-1),
              ∃ g2 ∈ (⊤ : Subgroup (FreeGroup X)), ⁅g1, g2⁆ = g},
            z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries m := by
          intro z hz'
          have h1 : z ∈ ⁅(⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (m - 1), (⊤ : Subgroup (FreeGroup X))⁆ := by
            rwa [Subgroup.commutator_def]
          rw [show m = m - 1 + 1 from by omega, Subgroup.lowerCentralSeries_succ]
          exact h1
        revert a ha haeq
        refine Subgroup.closure_induction (p := fun z _ => ∀ a : FreeAssoc X, a ∈ fil X (m+1) →
            Ideal.Quotient.mk (fil X N) a = magLead N z →
              degPart (X:=X) (m+1) a ∈ nestedSpan (X:=X) (m+1)) ?_ ?_ ?_ ?_ hzclos
        · -- generator: `z = ⁅u,v⁆`
          rintro z ⟨u, hu, v, hv, rfl⟩ a ha haeq
          have hv' : v ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (1 - 1) := by
            rw [Nat.sub_self, Subgroup.lowerCentralSeries_zero]; exact hv
          have hU : magLead N u ∈ filq X N m := magLead_mem_filq N m (by omega) (by omega) hu
          have hV : magLead N v ∈ filq X N 1 := magLead_mem_filq N 1 le_rfl (by omega) hv'
          obtain ⟨a_u, ha_u, ha_ueq⟩ :=
            (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hU
          obtain ⟨a_v, ha_v, ha_veq⟩ :=
            (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hV
          have hmc := magLead_commutator N m 1 (by omega) le_rfl (by omega) hu hv'
          rw [← ha_ueq, ← ha_veq] at hmc
          -- the degree `(m+1)` components of `a` and of `⁅a_u,a_v⁆` agree
          have hdiff_deg : degPart (X:=X) (m+1) (a - (a_u * a_v - a_v * a_u)) = 0 := by
            have hmem : Ideal.Quotient.mk (fil X N) (a - (a_u * a_v - a_v * a_u))
                ∈ filq X N (m + 1 + 1) := by
              rw [map_sub, map_sub, map_mul, map_mul, haeq]
              exact hmc
            obtain ⟨d, hd, hdeq⟩ :=
              (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hmem
            have h2 : (a - (a_u * a_v - a_v * a_u)) - d ∈ fil X N := by
              rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hdeq, sub_self]
            have h3 : degPart (X:=X) (m+1) ((a - (a_u * a_v - a_v * a_u)) - d) = 0 :=
              degPart_eq_zero_of_mem_fil h2 (by omega)
            rw [map_sub, sub_eq_zero] at h3
            rw [h3]
            exact degPart_eq_zero_of_mem_fil hd (by omega)
          have hc_deg : degPart (X:=X) (m+1) (a_u * a_v - a_v * a_u)
              = degPart (X:=X) m a_u * degPart (X:=X) 1 a_v
                - degPart (X:=X) 1 a_v * degPart (X:=X) m a_u := by
            rw [map_sub, degPart_mul_of_mem_fil ha_u ha_v]
            have h2 : degPart (X:=X) (m+1) (a_v * a_u)
                = degPart (X:=X) 1 a_v * degPart (X:=X) m a_u := by
              have hh := degPart_mul_of_mem_fil (p := 1) (q := m) ha_v ha_u
              rwa [show 1 + m = m + 1 from by omega] at hh
            rw [h2]
          have hA : degPart (X:=X) m a_u ∈ nestedSpan (X:=X) m :=
            ih (by omega) N (by omega) u hu a_u ha_u ha_ueq
          have hW : degPart (X:=X) 1 a_v ∈ nestedSpan (X:=X) 1 :=
            wordSpan_one_le_nestedSpan (degPart_mem_wordSpan 1 a_v)
          have hfin := nestedSpan_bracket_le hA hW
          rw [show degPart (X:=X) (m+1) a
              = degPart (X:=X) (m+1) (a_u * a_v - a_v * a_u) from by
            rw [map_sub, sub_eq_zero] at hdiff_deg; exact hdiff_deg, hc_deg]
          exact hfin
        · -- `z = 1`
          intro a ha haeq
          have hmem : a ∈ fil X N := by
            rw [← Ideal.Quotient.eq_zero_iff_mem, haeq, magLead_one]
          have h0 : degPart (X:=X) (m+1) a = 0 := degPart_eq_zero_of_mem_fil hmem (by omega)
          rw [h0]; exact Submodule.zero_mem _
        · -- product
          intro z1 z2 hz1 hz2 ih1 ih2 a ha haeq
          have hz1' : z1 ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries m := hmem_of z1 hz1
          have hz2' : z2 ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries m := hmem_of z2 hz2
          obtain ⟨b1, hb1, hb1eq⟩ := (Ideal.mem_map_iff_of_surjective _
            Ideal.Quotient.mk_surjective).1 (magLead_mem_filq N (m+1) (by omega) (by omega) hz1')
          obtain ⟨b2, hb2, hb2eq⟩ := (Ideal.mem_map_iff_of_surjective _
            Ideal.Quotient.mk_surjective).1 (magLead_mem_filq N (m+1) (by omega) (by omega) hz2')
          have hprod : magLead N (z1 * z2)
              = magLead N z1 + magLead N z2 + magLead N z1 * magLead N z2 := by
            unfold magLead
            rw [map_mul, Units.val_mul]
            noncomm_ring
          have hdiff : a - (b1 + b2 + b1 * b2) ∈ fil X N := by
            rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, map_add, map_mul,
              haeq, hprod, hb1eq, hb2eq]
            abel
          have hmain : degPart (X:=X) (m+1) a
              = degPart (X:=X) (m+1) (b1 + b2 + b1 * b2) := by
            have h0 : degPart (X:=X) (m+1) (a - (b1 + b2 + b1 * b2)) = 0 :=
              degPart_eq_zero_of_mem_fil hdiff (by omega)
            rw [map_sub, sub_eq_zero] at h0
            exact h0
          have hzero : degPart (X:=X) (m+1) (b1 * b2) = 0 :=
            degPart_eq_zero_of_mem_fil
              (fil_mul_le X (m+1) (m+1) (Ideal.mul_mem_mul hb1 hb2)) (by omega)
          rw [hmain, map_add, map_add, hzero, add_zero]
          exact Submodule.add_mem _ (ih1 b1 hb1 hb1eq) (ih2 b2 hb2 hb2eq)
        · -- inverse
          intro z hz ihz a ha haeq
          have hz' : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries m := hmem_of z hz
          obtain ⟨b, hb, hbeq⟩ := (Ideal.mem_map_iff_of_surjective _
            Ideal.Quotient.mk_surjective).1 (magLead_mem_filq N (m+1) (by omega) (by omega) hz')
          have hhb : degPart (X:=X) (m+1) b ∈ nestedSpan (X:=X) (m+1) := ihz b hb hbeq
          have hrel : magLead N z⁻¹ + magLead N z + magLead N z⁻¹ * magLead N z = 0 := by
            have h1 : (1 + magLead N z⁻¹) * (1 + magLead N z) = 1 := by
              have hU : (1 + magLead N z⁻¹)
                  = ((magnus X N z⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) := by
                unfold magLead; noncomm_ring
              have hV : (1 + magLead N z)
                  = ((magnus X N z : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) := by
                unfold magLead; noncomm_ring
              rw [hU, hV, ← Units.val_mul, map_inv, inv_mul_cancel, Units.val_one]
            have h2 : (1 + magLead N z⁻¹) * (1 + magLead N z) - 1
                = magLead N z⁻¹ + magLead N z + magLead N z⁻¹ * magLead N z := by noncomm_ring
            rw [h1, sub_self] at h2
            exact h2.symm
          have hsum : Ideal.Quotient.mk (fil X N) (a + b) ∈ filq X N (m + 1 + 1) := by
            have heq : Ideal.Quotient.mk (fil X N) (a + b)
                = -(Ideal.Quotient.mk (fil X N) a * Ideal.Quotient.mk (fil X N) b) := by
              rw [map_add, haeq, hbeq]
              exact eq_neg_of_add_eq_zero_left hrel
            have hma : Ideal.Quotient.mk (fil X N) a ∈ filq X N (m+1) :=
              Ideal.mem_map_of_mem (Ideal.Quotient.mk (fil X N)) ha
            have hmb : Ideal.Quotient.mk (fil X N) b ∈ filq X N (m+1) :=
              Ideal.mem_map_of_mem (Ideal.Quotient.mk (fil X N)) hb
            have hprod : Ideal.Quotient.mk (fil X N) a * Ideal.Quotient.mk (fil X N) b
                ∈ filq X N ((m+1) + (m+1)) := mul_mem_filq X N (m+1) (m+1) hma hmb
            have hneg : -(Ideal.Quotient.mk (fil X N) a * Ideal.Quotient.mk (fil X N) b)
                ∈ filq X N (m + 1 + 1) :=
              filq_antitone X N (show m + 1 + 1 ≤ (m+1) + (m+1) from by omega) (neg_mem hprod)
            rw [heq]
            exact hneg
          obtain ⟨d, hd, hdeq⟩ := (Ideal.mem_map_iff_of_surjective _
            Ideal.Quotient.mk_surjective).1 hsum
          have hab_zero : degPart (X:=X) (m+1) (a + b) = 0 := by
            have h2 : (a + b) - d ∈ fil X N := by
              rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hdeq, sub_self]
            have h3 : degPart (X:=X) (m+1) ((a + b) - d) = 0 :=
              degPart_eq_zero_of_mem_fil h2 (by omega)
            rw [map_sub, sub_eq_zero] at h3
            rw [h3]
            exact degPart_eq_zero_of_mem_fil hd (by omega)
          rw [map_add] at hab_zero
          rw [eq_neg_of_add_eq_zero_left hab_zero]
          exact neg_mem hhb

/-- The Magnus leading term of an element of `γ_j` is the image of an element of the nested span. -/
theorem magLead_mem_nestedImage (X : Type) (j : ℕ) (hj : 1 ≤ j) (z : FreeGroup X)
    (hz : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) :
    ∃ a ∈ nestedSpan (X := X) j,
      Ideal.Quotient.mk (fil X (j + 1)) a = magLead (j + 1) z := by
  have hmem : magLead (j + 1) z ∈ filq X (j + 1) j :=
    magLead_mem_filq (j + 1) j hj (by omega) hz
  obtain ⟨a₀, ha₀, ha₀eq⟩ :=
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hmem
  refine ⟨degPart (X:=X) j a₀,
    degPart_mem_nestedSpan_of_magLead j hj (j + 1) le_rfl z hz a₀ ha₀ ha₀eq, ?_⟩
  have hdiff : a₀ - degPart (X:=X) j a₀ ∈ fil X (j + 1) := sub_degPart_mem_fil ha₀
  have hzero : Ideal.Quotient.mk (fil X (j + 1)) (a₀ - degPart (X:=X) j a₀) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hdiff
  rw [map_sub, sub_eq_zero] at hzero
  rw [← ha₀eq]
  exact hzero.symm

end Work.SSGRoute.prop5

