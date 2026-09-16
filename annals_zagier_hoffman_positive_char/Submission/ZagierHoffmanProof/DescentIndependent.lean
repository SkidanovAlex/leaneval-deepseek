import Submission.ZagierHoffmanProof.DescentLambda

/-!
# Chang's Proposition 4.3.1 (`prop: MZ property`): `K`-independence ⟹ `K̄`-independence

The paper (Dac, *On Zagier-Hoffman's conjectures in positive characteristic*) uses
`prop: MZ property` (= Chang, *Linear independence of monomials of multizeta values*, Prop. 4.3.1)
in Dac §5.2 Step 2 to pass from a nontrivial `K̄`-relation between the values `𝓛(t;Q)(θ)` of the top
weight to a nontrivial `K`-relation.  Here we prove it for the family
`{𝓛(t)(θ) : t ∈ tmI S, tmWeight t = w₀}` of the merged `t`-motive.

**Proof** (Chang's Step II, adapted).  Strong induction on the cardinality `n` of the top-weight
family.  If the family is `K`-independent but not `K̄`-independent, take a `K̄`-relation
`∑ g_t·Z_t = 0` with `g_{t₀} ≠ 0`, rewrite it as `Z_{t₀} = ∑_{t ≠ t₀} lam_t·Z_t`; by induction
(and the prefix-removal trick: the family with `t₀` deleted is again the top-weight family of a
`t`-motive, namely the one over `S' = {s ∈ S : t₀ is not a prefix of s}`), the family
`{Z_t : t ≠ t₀}` is `K̄`-independent, so `descent_lambda` proves `lam_t ∈ K` for every `t ≠ t₀`,
giving a nontrivial `K`-relation — contradiction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial Matrix Finset
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

variable {F : Type*} [Field F] [Finite F]

/-! ## §1. Two elementary facts about taking prefixes of a positive-weight tuple -/

/-- If a prefix of `t` has the same `tmWeight` as `t` and all entries of `t` have positive weight,
then that prefix is `t` itself. -/
theorem take_eq_self_of_tmWeight_take_eq {K : Type*} [Field K] [DecidableEq K]
    {t : List (ℕ × Polynomial K)} {j : ℕ}
    (hpos : ∀ y ∈ t, 1 ≤ y.1) (hw : tmWeight (t.take j) = tmWeight t) : t.take j = t := by
  have h1 : tmWeight (t.take j) = tmWeight (t.take j) + tmWeight (t.drop j) := by
    rw [← tmWeight_take_add_drop t j]; exact hw
  have h0 : tmWeight (t.drop j) = 0 := by omega
  have hnil : t.drop j = [] := by
    by_contra hne
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
    have hy1 : 1 ≤ y.1 := hpos y (List.mem_of_mem_drop hy)
    have hy2 : y.1 ≤ tmWeight (t.drop j) := by
      simpa [tmWeight] using List.le_sum_of_mem (List.mem_map_of_mem (f := Prod.fst) hy)
    omega
  calc t.take j = t.take j ++ t.drop j := by rw [hnil, List.append_nil]
    _ = t := List.take_append_drop j t

/-- If `u` is a prefix of `t` (say `t.take j = u`) and `u`, `t` have the same `tmWeight`, and the
entries of `t` are positive, then `u = t`. -/
theorem eq_of_take_eq_of_tmWeight_eq {K : Type*} [Field K] [DecidableEq K]
    {t u : List (ℕ × Polynomial K)} {j : ℕ}
    (hpos : ∀ y ∈ t, 1 ≤ y.1) (hu : t.take j = u) (hw : tmWeight u = tmWeight t) : u = t := by
  have hw' : tmWeight (t.take j) = tmWeight t := by rw [hu]; exact hw
  rw [take_eq_self_of_tmWeight_take_eq hpos hw'] at hu
  exact hu.symm

/-- If `t` is a prefix of `u` (say `u.take j = t`) and `u`, `t` have the same `tmWeight`, and the
entries of `u` are positive, then `t = u`. -/
theorem eq_of_eq_take_of_tmWeight_eq {K : Type*} [Field K] [DecidableEq K]
    {t u : List (ℕ × Polynomial K)} {j : ℕ}
    (hpos : ∀ y ∈ u, 1 ≤ y.1) (hu : u.take j = t) (hw : tmWeight t = tmWeight u) : t = u := by
  have hw' : tmWeight (u.take j) = tmWeight u := by rw [hu]; exact hw
  rw [take_eq_self_of_tmWeight_take_eq hpos hw'] at hu
  exact hu.symm

/-! ## §2. The tuple set with the prefixes of `t₀` removed -/

variable {S : Finset (List (ℕ × Polynomial (Ambient F)))}
variable {t₀ : List (ℕ × Polynomial (Ambient F))} {w₀ : ℕ}

/-- The tuples of `S` that do not have `t₀` as a prefix.  Its top-weight family is the top-weight
family of `tmI S` with `t₀` removed. -/
noncomputable def descS' (S : Finset (List (ℕ × Polynomial (Ambient F))))
    (t₀ : List (ℕ × Polynomial (Ambient F))) : Finset (List (ℕ × Polynomial (Ambient F))) :=
  S.filter (fun s => ∀ k ≤ s.length, s.take k ≠ t₀)

lemma mem_descS' {s : List (ℕ × Polynomial (Ambient F))} :
    s ∈ descS' S t₀ ↔ s ∈ S ∧ ∀ k ≤ s.length, s.take k ≠ t₀ := by
  simp [descS']

lemma mem_tmI_of_mem_tmI_descS' {t : List (ℕ × Polynomial (Ambient F))}
    (ht : t ∈ tmI (descS' S t₀)) : t ∈ tmI S := by
  obtain ⟨s, hs, k, hk, hk'⟩ := mem_tmI.mp ht
  exact mem_tmI.mpr ⟨s, (mem_descS'.mp hs).1, k, hk, hk'⟩

lemma not_mem_tmI_descS'_self : t₀ ∉ tmI (descS' S t₀) := by
  intro h
  obtain ⟨s, hs, k, hk, hk'⟩ := mem_tmI.mp h
  exact (mem_descS'.mp hs).2 k (le_of_lt hk) hk'

/-- A top-weight element of `tmI S` other than `t₀` stays in `tmI (descS' S t₀)`. -/
lemma mem_tmI_descS'_of_ne (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1)
    (hpos₀ : ∀ y ∈ t₀, 1 ≤ y.1) (ht₀ : tmWeight t₀ = w₀)
    {t : List (ℕ × Polynomial (Ambient F))} (ht : t ∈ tmI S)
    (hw : tmWeight t = w₀) (hne : t ≠ t₀) : t ∈ tmI (descS' S t₀) := by
  obtain ⟨s, hs, k, hk, rfl⟩ := mem_tmI.mp ht
  refine mem_tmI.mpr ⟨s, mem_descS'.mpr ⟨hs, ?_⟩, k, hk, rfl⟩
  intro j hj hjt
  have hspos : ∀ y ∈ s, 1 ≤ y.1 := hpos s hs
  have htake_pos : ∀ y ∈ s.take k, 1 ≤ y.1 := fun y hy => hspos y (List.mem_of_mem_take hy)
  rcases lt_or_ge j k with hkj | hjk
  · -- `s.take j` is a prefix of `s.take k`
    have h1 : (s.take k).take j = s.take j := by
      rw [List.take_take, min_eq_left (le_of_lt hkj)]
    have h2 : tmWeight ((s.take k).take j) = tmWeight (s.take k) := by
      rw [h1, hjt, ht₀, hw]
    have h3 := take_eq_self_of_tmWeight_take_eq htake_pos h2
    exact hne (by rw [← h3, h1, hjt])
  · -- `s.take k` is a prefix of `t₀`
    have h1 : (s.take j).take k = s.take k := by
      rw [List.take_take, min_eq_left hjk]
    have e : t₀.take k = s.take k := by rw [← h1, hjt]
    have h2 : tmWeight (t₀.take k) = tmWeight t₀ := by rw [e, hw, ht₀]
    have h3 := take_eq_self_of_tmWeight_take_eq hpos₀ h2
    exact hne (by rw [← h1, hjt, h3])

/-! ## §3. The top-weight families of `S` and of `descS' S t₀` -/

/-- The value attached to a tuple by the merged `t`-motive: `𝓛(t)(θ)`. -/
noncomputable def tmZ (ω : PowerSeries (Ambient F))
    (l : List (ℕ × Polynomial (Ambient F))) : Ambient F :=
  evalSeriesGen (tmL (Nat.card F) ω l) (ambTheta F)

/-- The top-weight elements of `tmI (descS' S t₀)` are the top-weight elements of `tmI S` other
than `t₀`. -/
noncomputable def descLevelEquiv (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1)
    (hpos₀ : ∀ y ∈ t₀, 1 ≤ y.1) (ht₀ : tmWeight t₀ = w₀) (hmem : t₀ ∈ tmI S) :
    {t : ↥(tmI (descS' S t₀)) // tmWeight t.1 = w₀} ≃
      {t : ↥(tmI S) // tmWeight t.1 = w₀ ∧ t ≠ (⟨t₀, hmem⟩ : ↥(tmI S))} where
  toFun t := ⟨⟨t.1.1, mem_tmI_of_mem_tmI_descS' t.1.2⟩, t.2, fun hh => by
    have h2 : t.1.1 = t₀ := congrArg (fun x : ↥(tmI S) => x.1) hh
    exact not_mem_tmI_descS'_self (h2 ▸ t.1.2)⟩
  invFun t := ⟨⟨t.1.1, mem_tmI_descS'_of_ne hpos hpos₀ ht₀ t.1.2 t.2.1
      (fun hh => t.2.2 (Subtype.ext hh))⟩, t.2.1⟩
  left_inv t := Subtype.ext (Subtype.ext rfl)
  right_inv t := Subtype.ext (Subtype.ext rfl)

lemma card_level_eq_descS'_add_one (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1)
    (hpos₀ : ∀ y ∈ t₀, 1 ≤ y.1) (ht₀ : tmWeight t₀ = w₀) (hmem : t₀ ∈ tmI S) :
    Nat.card {t : ↥(tmI S) // tmWeight t.1 = w₀}
      = Nat.card {t : ↥(tmI (descS' S t₀)) // tmWeight t.1 = w₀} + 1 := by
  classical
  rw [Nat.card_congr (descLevelEquiv (F := F) hpos hpos₀ ht₀ hmem)]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simp only [Fintype.card_subtype]
  have h1 : (Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀))
      = insert (⟨t₀, hmem⟩ : ↥(tmI S))
          (Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀ ∧ t ≠ ⟨t₀, hmem⟩)) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases h2 : t = ⟨t₀, hmem⟩
      · exact Or.inl h2
      · exact Or.inr ⟨h, h2⟩
    · rintro (rfl | ⟨h, -⟩)
      · exact ht₀
      · exact h
  have hnot : (⟨t₀, hmem⟩ : ↥(tmI S)) ∉
      Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀ ∧ t ≠ ⟨t₀, hmem⟩) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun h => h.2 rfl
  rw [h1, Finset.card_insert_of_notMem hnot]

/-! ## §4. Transport of linear independence across `descS'` -/

/-- K-independence of the `S`-level family implies K-independence of the `descS' S t₀`-level
family (they are the same family with `t₀` removed). -/
lemma linearIndependent_descS'_level (_hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1)
    (_hpos₀ : ∀ y ∈ t₀, 1 ≤ y.1) (_ht₀ : tmWeight t₀ = w₀) (_hmem : t₀ ∈ tmI S)
    (R : Subfield (Ambient F)) (ω : PowerSeries (Ambient F))
    (h : LinearIndependent ↥R
      (fun t : {t : ↥(tmI S) // tmWeight t.1 = w₀} => tmZ (F := F) ω t.1.1)) :
    LinearIndependent ↥R (fun t : {t : ↥(tmI (descS' S t₀)) // tmWeight t.1 = w₀} =>
      tmZ (F := F) ω t.1.1) := by
  let f : {t : ↥(tmI (descS' S t₀)) // tmWeight t.1 = w₀} →
      {t : ↥(tmI S) // tmWeight t.1 = w₀} :=
    fun t => ⟨⟨t.1.1, mem_tmI_of_mem_tmI_descS' t.1.2⟩, t.2⟩
  have hf : Function.Injective f := fun a b hab => by
    have h1 : a.1.1 = b.1.1 := by
      simpa only [f] using congrArg (fun t : {t : ↥(tmI S) // tmWeight t.1 = w₀} => t.1.1) hab
    exact Subtype.ext (Subtype.ext h1)
  have hcomp := h.comp f hf
  have hfuneq : ((fun t : {t : ↥(tmI S) // tmWeight t.1 = w₀} => tmZ (F := F) ω t.1.1) ∘ f)
      = fun t : {t : ↥(tmI (descS' S t₀)) // tmWeight t.1 = w₀} => tmZ (F := F) ω t.1.1 := by
    funext t; rfl
  rwa [hfuneq] at hcomp

/-- K-independence of the `descS' S t₀`-level family implies K-independence of the level family of
`S` with `t₀` removed. -/
lemma linearIndependent_level_ne_descS' (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1)
    (hpos₀ : ∀ y ∈ t₀, 1 ≤ y.1) (ht₀ : tmWeight t₀ = w₀) (hmem : t₀ ∈ tmI S)
    (R : Subfield (Ambient F)) (ω : PowerSeries (Ambient F))
    (h : LinearIndependent ↥R (fun t : {t : ↥(tmI (descS' S t₀)) // tmWeight t.1 = w₀} =>
      tmZ (F := F) ω t.1.1)) :
    LinearIndependent ↥R (fun t : {t : ↥(tmI S) // tmWeight t.1 = w₀ ∧
        t ≠ (⟨t₀, hmem⟩ : ↥(tmI S))} => tmZ (F := F) ω t.1.1) := by
  let f : {t : ↥(tmI S) // tmWeight t.1 = w₀ ∧ t ≠ (⟨t₀, hmem⟩ : ↥(tmI S))} →
      {t : ↥(tmI (descS' S t₀)) // tmWeight t.1 = w₀} :=
    fun t => ⟨⟨t.1.1, mem_tmI_descS'_of_ne hpos hpos₀ ht₀ t.1.2 t.2.1
      (fun hh => t.2.2 (Subtype.ext hh))⟩, t.2.1⟩
  have hf : Function.Injective f := fun a b hab => by
    have h1 : a.1.1 = b.1.1 := by
      simpa only [f] using
        congrArg (fun t : {t : ↥(tmI (descS' S t₀)) // tmWeight t.1 = w₀} => t.1.1) hab
    exact Subtype.ext (Subtype.ext h1)
  have hcomp := h.comp f hf
  have hfuneq : ((fun t : {t : ↥(tmI (descS' S t₀)) // tmWeight t.1 = w₀} =>
        tmZ (F := F) ω t.1.1) ∘ f)
      = fun t : {t : ↥(tmI S) // tmWeight t.1 = w₀ ∧
          t ≠ (⟨t₀, hmem⟩ : ↥(tmI S))} => tmZ (F := F) ω t.1.1 := by
    funext t; rfl
  rwa [hfuneq] at hcomp

/-! ## §5. Chang's Proposition 4.3.1 -/

/-- **Chang's Proposition 4.3.1** (`prop: MZ property` of Dac): for the merged `t`-motive, the
top-weight values are `K`-linearly independent iff they are `K̄`-linearly independent. -/
theorem descent_independent_aux {γ : ℚᵐ⁰} {ω : PowerSeries (Ambient F)}
    (hγ0 : 0 < γ) (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰) (hq : 2 ≤ Nat.card F)
    (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeriesGen ω ((ambTheta F) ^ (Nat.card F ^ k)) = 0)
    (hωfe : (PowerSeries.X - PowerSeries.C ((ambTheta F) ^ Nat.card F))
      * frobTwist (R := Ambient F) (p := Nat.card F) 1 ω = ω) :
    ∀ (m : ℕ) (S : Finset (List (ℕ × Polynomial (Ambient F)))) (w₀ : ℕ),
      (∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F)))) →
      (∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F)))) →
      (∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1) →
      (∀ s ∈ S, ∀ y ∈ s, ∀ k, (y.2).coeff k ∈ ambA F 0) →
      Nat.card {t : ↥(tmI S) // tmWeight t.1 = w₀} = m →
      LinearIndependent (ambK F) (fun t : {t : ↥(tmI S) // tmWeight t.1 = w₀} =>
        tmZ (F := F) ω t.1.1) →
      LinearIndependent (ambKperf F) (fun t : {t : ↥(tmI S) // tmWeight t.1 = w₀} =>
        tmZ (F := F) ω t.1.1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro S w₀ hsm hSse hpos hQmem hcard hind
    by_contra hnot
    rw [Fintype.linearIndependent_iff] at hnot
    push Not at hnot
    obtain ⟨g, hg0, i₀, hi₀⟩ := hnot
    set t₀ : ↥(tmI S) := i₀.1 with ht₀def
    have hw₀ : tmWeight t₀.1 = w₀ := i₀.2
    set g₀ : ↥(ambKperf F) := g i₀ with hg₀def
    have hg₀ne : g₀ ≠ 0 := hi₀
    have hpos₀ : ∀ y ∈ t₀.1, 1 ≤ y.1 := fun y hy => by
      obtain ⟨s, hs, hs'⟩ := mem_tmI_entry (F := F) t₀.2 hy
      exact hpos s hs y hs'
    -- ### the top-weight finsets and the split at `t₀`
    set Wf : Finset ↥(tmI S) := Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀)
      with hWf
    set W' : Finset ↥(tmI S) :=
      Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀ ∧ t ≠ t₀) with hW'
    have ht₀mem : t₀ ∈ Wf := by rw [hWf, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hw₀⟩
    have hWsplit : Wf = insert t₀ W' := by
      rw [hWf, hW']
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h
        by_cases h2 : t = t₀
        · exact Or.inl h2
        · exact Or.inr ⟨h, h2⟩
      · rintro (rfl | ⟨h, -⟩)
        · exact hw₀
        · exact h
    have hnotmem : t₀ ∉ W' := by
      rw [hW', Finset.mem_filter]
      rintro ⟨-, -, h⟩
      exact h rfl
    -- ### the relation as a sum over the filtered finset
    let G : ↥(tmI S) → Ambient F := fun t =>
      if h : tmWeight t.1 = w₀ then ((g ⟨t, h⟩ : ↥(ambKperf F)) : Ambient F) else 0
    have hG : ∀ (t : ↥(tmI S)) (h : tmWeight t.1 = w₀),
        G t = ((g ⟨t, h⟩ : ↥(ambKperf F)) : Ambient F) := by
      intro t h
      simp only [G]
      rw [dif_pos h]
    have hGeq : ∀ i : {t : ↥(tmI S) // tmWeight t.1 = w₀},
        G i.1 = ((g i : ↥(ambKperf F)) : Ambient F) := fun i => hG i.1 i.2
    have hsub : (∑ i : {t : ↥(tmI S) // tmWeight t.1 = w₀}, G i.1 * tmZ (F := F) ω i.1.1)
        = ∑ t ∈ Wf, G t * tmZ (F := F) ω t.1 := by
      rw [Finset.sum_subtype Wf (p := fun t : ↥(tmI S) => tmWeight t.1 = w₀)
        (by intro x; rw [hWf]; simp) (fun t => G t * tmZ (F := F) ω t.1)]
    have hsum0 : (∑ t ∈ Wf, G t * tmZ (F := F) ω t.1) = 0 := by
      rw [← hsub]
      have h1 : (∑ i : {t : ↥(tmI S) // tmWeight t.1 = w₀}, G i.1 * tmZ (F := F) ω i.1.1)
          = ∑ i : {t : ↥(tmI S) // tmWeight t.1 = w₀},
              ((g i : ↥(ambKperf F)) : Ambient F) * tmZ (F := F) ω i.1.1 :=
        Finset.sum_congr rfl (fun i _ => by rw [hGeq i])
      rw [h1]
      simpa only [Subfield.smul_def, smul_eq_mul] using hg0
    -- ### the isolated `t₀`-term
    have hg₀coe : G t₀ = ((g i₀ : ↥(ambKperf F)) : Ambient F) := hG t₀ hw₀
    have hsplit : ((g i₀ : ↥(ambKperf F)) : Ambient F) * tmZ (F := F) ω t₀.1
        + ∑ t ∈ W', G t * tmZ (F := F) ω t.1 = 0 := by
      have h := hsum0
      rw [hWsplit, Finset.sum_insert hnotmem, hg₀coe] at h
      exact h
    have hg₀Ane : ((g i₀ : ↥(ambKperf F)) : Ambient F) ≠ 0 := by
      intro h
      exact hi₀ (Subtype.ext h)
    -- ### the coefficients `lam`
    let lam : ↥(tmI S) → Ambient F :=
      fun t => -(G t) / ((g i₀ : ↥(ambKperf F)) : Ambient F)
    have hlamem : ∀ t : ↥(tmI S), tmWeight t.1 = w₀ → t ≠ t₀ → lam t ∈ ambKperf F := by
      intro t ht hne
      have hGmem : G t ∈ ambKperf F := by rw [hG t ht]; exact (g ⟨t, ht⟩).2
      have hgd : ((g i₀ : ↥(ambKperf F)) : Ambient F) ∈ ambKperf F := (g i₀).2
      exact Subfield.div_mem _ (Subfield.neg_mem _ hGmem) hgd
    have hrel : tmZ (F := F) ω t₀.1 = ∑ t ∈ W', lam t * tmZ (F := F) ω t.1 := by
      have h4 : ((g i₀ : ↥(ambKperf F)) : Ambient F) * tmZ (F := F) ω t₀.1
          = -(∑ t ∈ W', G t * tmZ (F := F) ω t.1) := by
        have h := hsplit
        rw [add_eq_zero_iff_eq_neg] at h
        exact h
      have h1 : tmZ (F := F) ω t₀.1
          = -(∑ t ∈ W', G t * tmZ (F := F) ω t.1) / ((g i₀ : ↥(ambKperf F)) : Ambient F) := by
        rw [eq_div_iff hg₀Ane, mul_comm]
        exact h4
      rw [h1, ← Finset.sum_neg_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [lam]
      ring
    -- ### the change of level
    have hcard' : Nat.card {t : ↥(tmI (descS' S t₀.1)) // tmWeight t.1 = w₀} + 1 = m := by
      have h := card_level_eq_descS'_add_one (F := F) (S := S) (t₀ := t₀.1) (w₀ := w₀)
        hpos hpos₀ hw₀ t₀.2
      rw [← hcard]
      exact h.symm
    have hS'pos : ∀ s ∈ descS' S t₀.1, ∀ y ∈ s, 1 ≤ y.1 := fun s hs y hy =>
      hpos s (mem_descS'.mp hs).1 y hy
    have hS'sm : ∀ s ∈ descS' S t₀.1, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))) :=
      fun s hs y hy => hsm s (mem_descS'.mp hs).1 y hy
    have hS'se : ∀ s ∈ descS' S t₀.1, ∀ y ∈ s,
        GSuperEntire γ ((y.2 : PowerSeries (Ambient F))) :=
      fun s hs y hy => hSse s (mem_descS'.mp hs).1 y hy
    have hS'Qmem : ∀ s ∈ descS' S t₀.1, ∀ y ∈ s, ∀ k, (y.2).coeff k ∈ ambA F 0 :=
      fun s hs y hy => hQmem s (mem_descS'.mp hs).1 y hy
    have hind' : LinearIndependent (ambK F)
        (fun t : {t : ↥(tmI (descS' S t₀.1)) // tmWeight t.1 = w₀} => tmZ (F := F) ω t.1.1) :=
      linearIndependent_descS'_level (F := F) hpos hpos₀ hw₀ t₀.2 (ambK F) ω hind
    have hcard'' : Nat.card {t : ↥(tmI (descS' S t₀.1)) // tmWeight t.1 = w₀}
        = (Nat.card {t : ↥(tmI (descS' S t₀.1)) // tmWeight t.1 = w₀}) := rfl
    have ihres := ih (Nat.card {t : ↥(tmI (descS' S t₀.1)) // tmWeight t.1 = w₀})
      (by omega) (descS' S t₀.1) w₀ hS'sm hS'se hS'pos hS'Qmem hcard'' hind'
    have hind₂ : LinearIndependent (ambKperf F)
        (fun t : {t : ↥(tmI S) // tmWeight t.1 = w₀ ∧ t ≠ t₀} => tmZ (F := F) ω t.1.1) :=
      linearIndependent_level_ne_descS' (F := F) hpos hpos₀ hw₀ t₀.2 (ambKperf F) ω ihres
    -- ### apply `descent_lambda`
    have hlamK : ∀ t : ↥(tmI S), tmWeight t.1 = w₀ → t ≠ t₀ → lam t ∈ ambK F :=
      descent_lambda (F := F) hγ0 hγ harch hq hω hωse hc hωfe hsm hSse hpos hQmem hw₀ hind₂
        hlamem hrel
    -- ### the resulting `K`-relation contradicts `hind`
    let cc : {t : ↥(tmI S) // tmWeight t.1 = w₀} → Ambient F := fun i =>
      if i.1 = t₀ then 1 else -(lam i.1)
    have hcc : ∀ i : {t : ↥(tmI S) // tmWeight t.1 = w₀}, cc i ∈ ambK F := by
      intro i
      by_cases h : i.1 = t₀
      · simp only [cc]
        rw [if_pos h]
        exact Subfield.one_mem _
      · simp only [cc]
        rw [if_neg h]
        exact Subfield.neg_mem _ (hlamK i.1 i.2 h)
    have hzero : (∑ i : {t : ↥(tmI S) // tmWeight t.1 = w₀},
        (⟨cc i, hcc i⟩ : ↥(ambK F)) • tmZ (F := F) ω i.1.1) = 0 := by
      have h1 : (∑ i : {t : ↥(tmI S) // tmWeight t.1 = w₀}, cc i * tmZ (F := F) ω i.1.1)
          = ∑ t ∈ Wf,
              (if t = t₀ then (1 : Ambient F) else -(lam t)) * tmZ (F := F) ω t.1 := by
        rw [Finset.sum_subtype Wf (p := fun t : ↥(tmI S) => tmWeight t.1 = w₀)
          (by intro x; rw [hWf]; simp)
          (fun t => (if t = t₀ then (1 : Ambient F) else -(lam t)) * tmZ (F := F) ω t.1)]
      have h2 : (∑ t ∈ Wf, (if t = t₀ then (1 : Ambient F) else -(lam t))
            * tmZ (F := F) ω t.1) = 0 := by
        rw [hWsplit, Finset.sum_insert hnotmem]
        rw [if_pos rfl, one_mul]
        have h3 : ∀ t ∈ W', (if t = t₀ then (1 : Ambient F) else -(lam t))
            * tmZ (F := F) ω t.1 = -(lam t * tmZ (F := F) ω t.1) := by
          intro t ht
          have htne : t ≠ t₀ := by
            have ht' : t ∈ Finset.univ.filter
                (fun t : ↥(tmI S) => tmWeight t.1 = w₀ ∧ t ≠ t₀) := by
              rw [← hW']; exact ht
            exact (Finset.mem_filter.mp ht').2.2
          rw [if_neg htne]
          ring
        rw [Finset.sum_congr rfl h3, Finset.sum_neg_distrib, hrel]
        ring
      rw [show (∑ i : {t : ↥(tmI S) // tmWeight t.1 = w₀},
            (⟨cc i, hcc i⟩ : ↥(ambK F)) • tmZ (F := F) ω i.1.1)
          = ∑ i : {t : ↥(tmI S) // tmWeight t.1 = w₀}, cc i * tmZ (F := F) ω i.1.1 by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Subfield.smul_def, smul_eq_mul]]
      rw [h1, h2]
    have hcout := (Fintype.linearIndependent_iff.mp hind)
      (fun i : {t : ↥(tmI S) // tmWeight t.1 = w₀} => (⟨cc i, hcc i⟩ : ↥(ambK F))) hzero i₀
    have hcceq : cc i₀ = 1 := by
      simp only [cc]
      rw [if_pos (show i₀.1 = t₀ from rfl)]
    have h0 : cc i₀ = 0 := by
      have h := congrArg (fun x : ↥(ambK F) => (x : Ambient F)) hcout
      simpa only [Subfield.coe_subtype, Subfield.coe_zero] using h
    rw [hcceq] at h0
    exact one_ne_zero h0


/-- **Chang's Proposition 4.3.1** (`prop: MZ property` of Dac), clean form: for the merged
`t`-motive, `K`-independence of the top-weight values of `tmI S` implies their `K̄`-independence. -/
theorem descent_independent {γ : ℚᵐ⁰} {ω : PowerSeries (Ambient F)}
    (hγ0 : 0 < γ) (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰) (hq : 2 ≤ Nat.card F)
    (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeriesGen ω ((ambTheta F) ^ (Nat.card F ^ k)) = 0)
    (hωfe : (PowerSeries.X - PowerSeries.C ((ambTheta F) ^ Nat.card F))
      * frobTwist (R := Ambient F) (p := Nat.card F) 1 ω = ω)
    {S : Finset (List (ℕ × Polynomial (Ambient F)))} {w₀ : ℕ}
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1)
    (hQmem : ∀ s ∈ S, ∀ y ∈ s, ∀ k, (y.2).coeff k ∈ ambA F 0)
    (hind : LinearIndependent (ambK F) (fun t : {t : ↥(tmI S) // tmWeight t.1 = w₀} =>
      tmZ (F := F) ω t.1.1)) :
    LinearIndependent (ambKperf F) (fun t : {t : ↥(tmI S) // tmWeight t.1 = w₀} =>
      tmZ (F := F) ω t.1.1) :=
  descent_independent_aux (F := F) hγ0 hγ harch hq hω hωse hc hωfe
    (Nat.card {t : ↥(tmI S) // tmWeight t.1 = w₀}) S w₀ hsm hSse hpos hQmem rfl hind

/-- **Dac §5.2, Step 2, last step.**  Given the leading-weight relation
`∑_t B_t(θ^{q^j})·(𝓛(t)(θ))^{q^j} = 0` for all `j ≥ 2` and the `K`-independence of the top-weight
values (condition (LW)), all the coefficients `B_t` vanish. -/
theorem descent_B_zero {γ : ℚᵐ⁰} {ω : PowerSeries (Ambient F)}
    (hγ0 : 0 < γ) (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰) (hq : 2 ≤ Nat.card F)
    (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeriesGen ω ((ambTheta F) ^ (Nat.card F ^ k)) = 0)
    (hωfe : (PowerSeries.X - PowerSeries.C ((ambTheta F) ^ Nat.card F))
      * frobTwist (R := Ambient F) (p := Nat.card F) 1 ω = ω)
    {S : Finset (List (ℕ × Polynomial (Ambient F)))} {w₀ : ℕ}
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1)
    (hQmem : ∀ s ∈ S, ∀ y ∈ s, ∀ k, (y.2).coeff k ∈ ambA F 0)
    (hind : LinearIndependent (ambK F) (fun t : {t : ↥(tmI S) // tmWeight t.1 = w₀} =>
      tmZ (F := F) ω t.1.1))
    {B : ↥(tmI S) → Polynomial (Ambient F)}
    (hBmem : ∀ t k, (B t).coeff k ∈ ambKperf F)
    (hrel : ∀ j : ℕ, 2 ≤ j →
      (∑ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀),
        (B t).eval ((ambTheta F) ^ (Nat.card F ^ j))
          * (tmZ (F := F) ω t.1) ^ (Nat.card F ^ j)) = 0) :
    ∀ t : ↥(tmI S), tmWeight t.1 = w₀ → B t = 0 := by
  classical
  have hqn : Nat.card F ≠ 0 := FrobPow.ne_zero (Ambient F) (q := Nat.card F)
  have hKbar := descent_independent (F := F) hγ0 hγ harch hq hω hωse hc hωfe
    hsm hSse hpos hQmem hind
  have hθmem : ∀ j : ℕ, (ambTheta F) ^ (Nat.card F ^ j) ∈ ambKperf F := fun j =>
    Subfield.pow_mem _ (ambTheta_mem_ambKperf F) _
  intro t ht
  have hev : ∀ᶠ j : ℕ in Filter.atTop,
      (B t).eval ((ambTheta F) ^ (Nat.card F ^ j)) = 0 := by
    rw [Filter.eventually_atTop]
    refine ⟨2, fun j hj => ?_⟩
    obtain ⟨c, hcmem, hc'⟩ : ∃ c : {t : ↥(tmI S) // tmWeight t.1 = w₀} → Ambient F,
        (∀ i, c i ∈ ambKperf F) ∧ ∀ i, (c i) ^ (Nat.card F ^ j)
          = (B i.1).eval ((ambTheta F) ^ (Nat.card F ^ j)) := by
      have h : ∀ i : {t : ↥(tmI S) // tmWeight t.1 = w₀}, ∃ c ∈ ambKperf F,
          c ^ (Nat.card F ^ j) = (B i.1).eval ((ambTheta F) ^ (Nat.card F ^ j)) := fun i =>
        exists_pow_pow_eq_of_mem_ambKperf (F := F)
          (Polynomial.eval_mem_ambKperf (F := F) (hBmem i.1) (hθmem j)) j
      choose c hcmem hc' using h
      exact ⟨c, hcmem, hc'⟩
    have hqj : Nat.card F ^ j ≠ 0 := pow_ne_zero j hqn
    have hsum : (∑ i : {t : ↥(tmI S) // tmWeight t.1 = w₀},
        c i * tmZ (F := F) ω i.1.1) ^ (Nat.card F ^ j) = 0 := by
      have : FrobPow (Ambient F) (Nat.card F ^ j) := FrobPow.pow (R := Ambient F) j
      rw [FrobPow.sum_pow_finset]
      have h1 : (∑ i : {t : ↥(tmI S) // tmWeight t.1 = w₀},
            (c i * tmZ (F := F) ω i.1.1) ^ (Nat.card F ^ j))
          = ∑ i : {t : ↥(tmI S) // tmWeight t.1 = w₀},
              (B i.1).eval ((ambTheta F) ^ (Nat.card F ^ j))
                * (tmZ (F := F) ω i.1.1) ^ (Nat.card F ^ j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_pow, hc' i]
      rw [h1]
      rw [← Finset.sum_subtype (Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀))
        (p := fun t : ↥(tmI S) => tmWeight t.1 = w₀) (fun x => by simp)
        (fun t => (B t).eval ((ambTheta F) ^ (Nat.card F ^ j))
          * (tmZ (F := F) ω t.1) ^ (Nat.card F ^ j))]
      exact hrel j hj
    have hsum0 : (∑ i : {t : ↥(tmI S) // tmWeight t.1 = w₀},
        c i * tmZ (F := F) ω i.1.1) = 0 := (pow_eq_zero_iff hqj).mp hsum
    have hczero := (Fintype.linearIndependent_iff.mp hKbar)
      (fun i : {t : ↥(tmI S) // tmWeight t.1 = w₀} => (⟨c i, hcmem i⟩ : ↥(ambKperf F)))
      (by
        rw [show (∑ i : {t : ↥(tmI S) // tmWeight t.1 = w₀},
              (⟨c i, hcmem i⟩ : ↥(ambKperf F)) • tmZ (F := F) ω i.1.1)
            = ∑ i : {t : ↥(tmI S) // tmWeight t.1 = w₀}, c i * tmZ (F := F) ω i.1.1 by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Subfield.smul_def, smul_eq_mul]]
        exact hsum0)
      ⟨t, ht⟩
    have hcu : c ⟨t, ht⟩ = 0 := by
      have h := congrArg (fun x : ↥(ambKperf F) => (x : Ambient F)) hczero
      simpa only [Subfield.coe_subtype, Subfield.coe_zero] using h
    rw [← hc' ⟨t, ht⟩, hcu, zero_pow hqj]
  have hθ0 : Valued.v (ambTheta F) ≠ 0 := by
    rw [v_ambTheta]; exact (WithZero.exp_pos (a := ((Nat.card F : ℚ) - 1))).ne'
  have hθ1 : Valued.v (ambTheta F) ≠ 1 := by
    rw [v_ambTheta]
    intro h
    have h2 : ((Nat.card F : ℚ) - 1) = 0 :=
      WithZero.exp_injective (h.trans (WithZero.exp_zero).symm)
    have h3 : (2 : ℚ) ≤ (Nat.card F : ℚ) := by exact_mod_cast hq
    linarith
  exact polynomial_eq_zero_of_eventually_eval_eq_zero_gen hθ0 hθ1 hq hev

end ZagierHoffmanPositiveChar
