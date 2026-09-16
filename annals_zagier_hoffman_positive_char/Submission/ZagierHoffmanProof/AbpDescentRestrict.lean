import Submission.ZagierHoffmanProof.AbpDescentMain

/-!
# The restricted `t`-motive over the top-weight coordinates, and the `K^{perf}` → `K` descent

For the descent step of Dac §5.2 / Chang Prop. 4.3.1 one needs a `t`-motive whose index set
contains the top-weight tuples *themselves* (the index set `tmI S` of the merged motive of
`TmMotive.lean` only contains proper prefixes).  This file constructs it:

* `descW S w₀` — the top-weight tuples of `tmI S`, as a finset of lists;
* `descS S w₀` — the tuple set `{t ++ [(0,0)] : t ∈ descW S w₀}`; its proper prefixes are exactly
  the prefixes of the top-weight tuples (`mem_tmI_descS`), and all its tuples have weight `w₀`.

With `A = tmAOpt q θ w₀ (descS S w₀) 0` the coordinates `some t` for `t ∈ descW S w₀` have
`A`-column `e_t` (`tmAOpt_descS_column`), which is what `tm_second_relation` needs, and the
evaluation at `θ` of the corresponding entry of the trivialisation is `𝓛(t)(θ)` with no `ω`-factor.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
open Polynomial Matrix Finset
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

variable {F : Type*} [Field F] [Finite F]

/-! ## §1. The restricted tuple set and its index set -/

section Restricted

variable {w₀ : ℕ} {S : Finset (List (ℕ × Polynomial (Ambient F)))}

/-- The top-weight tuples of `tmI S`, as a finset of lists. -/
noncomputable def descW (S : Finset (List (ℕ × Polynomial (Ambient F)))) (w₀ : ℕ) :
    Finset (List (ℕ × Polynomial (Ambient F))) :=
  (Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀)).image (fun t => t.1)

lemma mem_descW {u : List (ℕ × Polynomial (Ambient F))} :
    u ∈ descW S w₀ ↔ ∃ t : ↥(tmI S), tmWeight t.1 = w₀ ∧ t.1 = u := by
  classical
  rw [descW, Finset.mem_image]
  constructor
  · rintro ⟨t, ht, htu⟩
    exact ⟨t, (Finset.mem_filter.mp ht).2, htu⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, ht⟩, rfl⟩

/-- The tuple set of the restricted motive. -/
noncomputable def descS (S : Finset (List (ℕ × Polynomial (Ambient F)))) (w₀ : ℕ) :
    Finset (List (ℕ × Polynomial (Ambient F))) :=
  (descW S w₀).image fun t => t ++ [(0, (0 : Polynomial (Ambient F)))]

lemma mem_descS {u : List (ℕ × Polynomial (Ambient F))} :
    u ∈ descS S w₀ ↔ ∃ t : ↥(tmI S), tmWeight t.1 = w₀ ∧
      u = t.1 ++ [(0, (0 : Polynomial (Ambient F)))] := by
  classical
  rw [descS, Finset.mem_image]
  constructor
  · rintro ⟨t', ht', rfl⟩
    obtain ⟨t, ht, rfl⟩ := mem_descW.mp ht'
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t.1, mem_descW.mpr ⟨t, ht, rfl⟩, rfl⟩

/-- **The index set of the restricted motive**: its elements are exactly the prefixes (of any
length) of the top-weight tuples of `tmI S`. -/
lemma mem_tmI_descS {u : List (ℕ × Polynomial (Ambient F))} :
    u ∈ tmI (descS S w₀) ↔
      ∃ t : ↥(tmI S), tmWeight t.1 = w₀ ∧ ∃ k ≤ t.1.length, t.1.take k = u := by
  classical
  rw [mem_tmI]
  constructor
  · rintro ⟨s, hs, k, hk, rfl⟩
    obtain ⟨t, ht, rfl⟩ := mem_descS.mp hs
    simp only [List.length_append, List.length_singleton] at hk
    exact ⟨t, ht, k, by omega, (List.take_append_of_le_length (by omega)).symm⟩
  · rintro ⟨t, ht, k, hk, rfl⟩
    refine ⟨t.1 ++ [(0, (0 : Polynomial (Ambient F)))], mem_descS.mpr ⟨t, ht, rfl⟩, k, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton]; omega
    · exact List.take_append_of_le_length hk


/-- Every tuple of `descS S w₀` has weight `w₀`. -/
lemma descS_weight {s : List (ℕ × Polynomial (Ambient F))} (hs : s ∈ descS S w₀) :
    tmWeight s = w₀ := by
  obtain ⟨t, ht, rfl⟩ := mem_descS.mp hs
  rw [tmWeight_append, ht]
  simp [tmWeight]

lemma descS_ne_nil {s : List (ℕ × Polynomial (Ambient F))} (hs : s ∈ descS S w₀) : s ≠ [] := by
  obtain ⟨t, ht, rfl⟩ := mem_descS.mp hs
  simp

/-- The entries of a tuple of `descS S w₀` are either entries of a tuple of `S`, or the appended
`(0,0)`. -/
lemma mem_descS_entry {s : List (ℕ × Polynomial (Ambient F))} (hs : s ∈ descS S w₀)
    {y : ℕ × Polynomial (Ambient F)} (hy : y ∈ s) :
    (∃ s₀ ∈ S, y ∈ s₀) ∨ y = (0, (0 : Polynomial (Ambient F))) := by
  obtain ⟨t, ht, rfl⟩ := mem_descS.mp hs
  rw [List.mem_append] at hy
  rcases hy with hy | hy
  · exact Or.inl (mem_tmI_entry F t.2 hy)
  · rw [List.mem_singleton] at hy
    exact Or.inr hy

/-- The "small" condition transfers from `S` to `descS S w₀`. -/
lemma descS_isSmall {γ : ℚᵐ⁰} {ω : PowerSeries (Ambient F)}
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F)))) :
    ∀ s ∈ descS S w₀, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))) := by
  intro s hs y hy
  rcases mem_descS_entry hs hy with ⟨s₀, hs₀, hy₀⟩ | rfl
  · exact hsm s₀ hs₀ y hy₀
  · have h : (ω ^ ((0 : ℕ)) * (((0 : Polynomial (Ambient F))) : PowerSeries (Ambient F)))
        = (0 : PowerSeries (Ambient F)) := by simp
    rw [h]
    exact gIsSmall_zero γ

/-- The super-entire condition transfers from `S` to `descS S w₀`. -/
lemma descS_superEntire {γ : ℚᵐ⁰}
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F)))) :
    ∀ s ∈ descS S w₀, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))) := by
  intro s hs y hy
  rcases mem_descS_entry hs hy with ⟨s₀, hs₀, hy₀⟩ | rfl
  · exact hSse s₀ hs₀ y hy₀
  · exact GSuperEntire.zero γ

/-- Positivity of the entries of an element of `tmI S`. -/
lemma tmI_pos (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1) (t : ↥(tmI S))
    {y : ℕ × Polynomial (Ambient F)} (hy : y ∈ t.1) : 1 ≤ y.1 := by
  obtain ⟨s₀, hs₀, hy'⟩ := mem_tmI_entry F t.2 hy
  exact hpos s₀ hs₀ y hy'

/-- **Positivity of the entries of the index set of the restricted motive.** -/
lemma tmI_descS_pos (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1) (u : ↥(tmI (descS S w₀)))
    {y : ℕ × Polynomial (Ambient F)} (hy : y ∈ u.1) : 1 ≤ y.1 := by
  obtain ⟨t, ht, k, hk, hkt⟩ := mem_tmI_descS.mp u.2
  rw [← hkt] at hy
  exact tmI_pos hpos t (List.mem_of_mem_take hy)

/-- A list all of whose entries have weight `0` is empty, provided all the entries are positive. -/
lemma eq_nil_of_tmWeight_eq_zero {l : List (ℕ × Polynomial (Ambient F))}
    (hpos_l : ∀ y ∈ l, 1 ≤ y.1) (h : tmWeight l = 0) : l = [] := by
  by_contra hne
  obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil l hne
  have hz0 : z.1 = 0 :=
    List.sum_eq_zero_iff.mp h z.1 (List.mem_map.mpr ⟨z, hz, rfl⟩)
  have := hpos_l z hz
  omega

/-- Every element of the index set of the restricted motive has weight at most `w₀`. -/
lemma tmI_descS_weight_le (u : ↥(tmI (descS S w₀))) : tmWeight u.1 ≤ w₀ := by
  obtain ⟨t, ht, k, hk, hkt⟩ := mem_tmI_descS.mp u.2
  rw [← hkt]
  have h := tmWeight_take_add_drop t.1 k
  rw [ht] at h
  omega

/-- An element of the index set of weight exactly `w₀` is one of the top-weight tuples. -/
lemma mem_descW_of_mem_tmI_descS (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1) {u : List _}
    (hu : u ∈ tmI (descS S w₀)) (hw : tmWeight u = w₀) : u ∈ descW S w₀ := by
  obtain ⟨t, ht, k, hk, hkt⟩ := mem_tmI_descS.mp hu
  have hsplit := tmWeight_take_add_drop t.1 k
  rw [hkt, hw, ht] at hsplit
  have hdrop : tmWeight (t.1.drop k) = 0 := by omega
  have hnil : t.1.drop k = [] :=
    eq_nil_of_tmWeight_eq_zero (fun y hy => tmI_pos hpos t (List.drop_subset k t.1 hy)) hdrop
  rw [← hkt]
  have hlen : t.1.length ≤ k := by
    by_contra hlt
    rw [not_le] at hlt
    have : (t.1.drop k).length = t.1.length - k := List.length_drop
    rw [hnil] at this
    simp at this
    omega
  exact mem_descW.mpr ⟨t, ht, ((List.take_eq_self_iff t.1).mpr hlen).symm⟩

/-- A top-weight tuple is an element of the index set of the restricted motive. -/
lemma mem_tmI_descS_of_mem_descW {u : List (ℕ × Polynomial (Ambient F))}
    (hu : u ∈ descW S w₀) : u ∈ tmI (descS S w₀) := by
  obtain ⟨t, ht, rfl⟩ := mem_descW.mp hu
  exact mem_tmI_descS.mpr ⟨t, ht, t.1.length, le_rfl, List.take_length⟩


/-! ## §2. The column of the restricted motive at a top-weight coordinate -/

/-- If the `dropLast` of an index of the restricted motive is a top-weight tuple, then the last
entry of that index has polynomial part `0`.  (Indeed the index has a positive last entry unless it
is empty, and its weight is bounded by `w₀`.) -/
lemma tmQ_eq_zero_of_dropLast_mem_descW (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1)
    {u : ↥(tmI (descS S w₀))} (h : u.1.dropLast ∈ descW S w₀) : tmQ u.1 = 0 := by
  rcases List.eq_nil_or_concat u.1 with hnil | ⟨l, x, hcat⟩
  · simp [tmQ, hnil]
  · exfalso
    obtain ⟨t, ht, htu⟩ := mem_descW.mp h
    have hwt : tmWeight u.1.dropLast = w₀ := by rw [← htu, ht]
    have hlast : (u.1.getLastD (0, (0 : Polynomial (Ambient F)))) ∈ u.1 := by
      rw [hcat, List.concat_eq_append, List.getLastD_concat]
      exact List.mem_append_right _ (List.mem_singleton_self x)
    have hpos1 : 1 ≤ (u.1.getLastD (0, (0 : Polynomial (Ambient F)))).1 :=
      tmI_descS_pos hpos u hlast
    have hsplit := tmWeight_dropLast u.1
    have hle := tmI_descS_weight_le (S := S) (w₀ := w₀) u
    omega

/-- **The entries of the restricted `t`-motive at a top-weight column.** -/
lemma tmA_descS (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1)
    {u t' : ↥(tmI (descS S w₀))} (ht' : tmWeight t'.1 = w₀) :
    tmA (K := Ambient F) (Nat.card F) (ambTheta F) w₀ u.1 t'.1
      = if u.1 = t'.1 then 1 else 0 := by
  by_cases h1 : u.1 = t'.1
  · rw [if_pos h1, h1, tmA_diag, show w₀ - tmWeight t'.1 = 0 by omega, pow_zero]
  · rw [if_neg h1]
    by_cases h2 : t'.1 = u.1.dropLast
    · have hm : u.1.dropLast ∈ descW S w₀ :=
        mem_descW_of_mem_tmI_descS (S := S) (w₀ := w₀) hpos (dropLast_mem_tmI u.2)
          (by rw [← h2, ht'])
      rw [tmA, if_neg (Ne.symm h1), if_pos h2,
        show ((u.1).getLastD (0, (0 : Polynomial (Ambient F)))).2 = tmQ u.1 from rfl,
        tmQ_eq_zero_of_dropLast_mem_descW (S := S) (w₀ := w₀) hpos hm, zero_mul]
    · rw [tmA_eq_zero_of_ne (ambTheta F) w₀ (Ne.symm h1) h2]

/-- **The column of the restricted `t`-motive at a top-weight coordinate is `e_t`.** -/
lemma tmAOpt_descS_column (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1)
    {t' : ↥(tmI (descS S w₀))} (ht' : tmWeight t'.1 = w₀) :
    ∀ i : Option ↥(tmI (descS S w₀)),
      tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w₀ (descS S w₀)
        (fun _ => (0 : Polynomial (Ambient F))) i (some t')
      = if i = some t' then 1 else 0 := by
  intro i
  cases i with
  | none =>
    rw [tmAOpt_none_some, tmV, if_neg (by simp)]
    refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs <;> ring
  | some u =>
    rw [tmAOpt_some_some, tmA_descS (S := S) (w₀ := w₀) hpos ht']
    by_cases h : u = t'
    · have hsu : (some u : Option ↥(tmI (descS S w₀))) = some t' := by rw [h]
      rw [if_pos (by rw [h]), if_pos hsu]
    · have hsu : ¬ ((some u : Option ↥(tmI (descS S w₀))) = some t') :=
        fun hh => h (Option.some.inj hh)
      rw [if_neg (fun hh => h (Subtype.ext hh)), if_neg hsu]


/-! ## §3. `A_0`-coefficient bookkeeping for the restricted motive -/

/-- A natural number, viewed in the ambient field, lies in every level `A_ν`. -/
lemma ambA_natCast_mem (ν : ℕ) (n : ℕ) : ((n : ℕ) : Ambient F) ∈ ambA F ν := by
  exact (mem_ambA_iff F ν _).mpr ⟨Polynomial.C (n : F), by simp⟩

/-- The zero of the ambient field lies in every level `A_ν`. -/
lemma ambA_zero_mem (ν : ℕ) : (0 : Ambient F) ∈ ambA F ν := (ambASub F ν).zero_mem

/-- If `x ∈ A_ν` then every coefficient of `(X - C x)^n` lies in `A_ν`. -/
lemma coeff_X_sub_C_pow_mem {x : Ambient F} {ν : ℕ} (hx : x ∈ ambA F ν) (n : ℕ) :
    ∀ m, ((Polynomial.X - Polynomial.C x) ^ n : Polynomial (Ambient F)).coeff m ∈ ambA F ν := by
  obtain ⟨p, rfl⟩ := (mem_ambA_iff F ν x).mp hx
  have hmap : ((Polynomial.X - Polynomial.C
        (p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν))) ^ n : Polynomial (Ambient F))
      = Polynomial.map (Polynomial.eval₂RingHom (algebraMap F (Ambient F)) (ambThetaNu F ν))
          ((Polynomial.X - Polynomial.C p) ^ n : Polynomial (Polynomial F)) := by
    have hX : (Polynomial.eval₂RingHom (algebraMap F (Ambient F)) (ambThetaNu F ν)) p
        = p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν) := rfl
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hX]
  intro m
  rw [hmap, Polynomial.coeff_map, Polynomial.coe_eval₂RingHom]
  exact (mem_ambA_iff F ν _).mpr ⟨_, rfl⟩

/-- The last-entry polynomial `tmQ` of an element of the restricted index set has
`A_0`-coefficients, provided the entries of the tuples of `S` do. -/
lemma tmQ_coeff_mem_of_mem_tmI_descS
    (hQmem : ∀ s ∈ S, ∀ y ∈ s, ∀ m, (y.2).coeff m ∈ ambA F 0)
    (u : ↥(tmI (descS S w₀))) (m : ℕ) : (tmQ u.1).coeff m ∈ ambA F 0 := by
  rcases List.eq_nil_or_concat u.1 with hnil | ⟨l, x, hcat⟩
  · rw [hnil, tmQ]
    simp only [List.getLastD_nil, Polynomial.coeff_zero]
    exact ambA_zero_mem 0
  · obtain ⟨t, ht, k, hk, hkt⟩ := mem_tmI_descS.mp u.2
    have hx : x ∈ u.1 := by
      rw [hcat, List.concat_eq_append]
      exact List.mem_append_right _ (List.mem_singleton_self x)
    have hx' : x ∈ t.1 := by
      rw [← hkt] at hx
      exact List.mem_of_mem_take hx
    obtain ⟨s₀, hs₀, hx''⟩ := mem_tmI_entry F t.2 hx'
    have hQ : tmQ u.1 = x.2 := by
      rw [tmQ, hcat, List.concat_eq_append, List.getLastD_concat]
    rw [hQ]
    exact hQmem s₀ hs₀ x hx'' m

/-- **The `A_0`-coefficient condition for the restricted `t`-motive.** -/
lemma tmAOpt_descS_coeff_mem_ambA0
    (hQmem : ∀ s ∈ S, ∀ y ∈ s, ∀ m, (y.2).coeff m ∈ ambA F 0) :
    ∀ i j m, (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w₀ (descS S w₀)
      (fun _ => (0 : Polynomial (Ambient F))) i j).coeff m ∈ ambA F 0 := by
  have hθq : ((ambTheta F) ^ Nat.card F) ∈ ambA F 0 := by
    rw [← ambThetaNu_zero F]
    exact ambThetaNu_pow_mem F 0 (Nat.card F)
  intro i j m
  cases i with
  | none =>
    cases j with
    | none =>
      rw [tmAOpt_none_none, Polynomial.coeff_one]
      split_ifs
      · exact ambA_one_mem F 0
      · exact ambA_zero_mem 0
    | some t' =>
      rw [tmAOpt_none_some, tmV]
      rw [Finset.sum_eq_zero (fun s _ => by split_ifs <;> ring), Polynomial.coeff_zero]
      exact ambA_zero_mem 0
  | some u =>
    cases j with
    | none =>
      rw [tmAOpt_some_none, Polynomial.coeff_zero]
      exact ambA_zero_mem 0
    | some t' =>
      rw [tmAOpt_some_some, tmA]
      split_ifs with h1 h2
      · exact coeff_X_sub_C_pow_mem hθq _ m
      · rw [Polynomial.coeff_mul]
        have h1 : ∀ b : ℕ,
            ((u.1).getLastD (0, (0 : Polynomial (Ambient F)))).2.coeff b ∈ ambA F 0 := by
          intro b
          exact tmQ_coeff_mem_of_mem_tmI_descS hQmem u b
        refine ambA_sum_mem F fun b _ => ambA_mul_mem F (h1 b.1) ?_
        exact coeff_X_sub_C_pow_mem hθq _ _
      · rw [Polynomial.coeff_zero]
        exact ambA_zero_mem 0


/-! ## §4. The MZ property with positivity stated on the index set

`tmL_frobenius_pow` assumes `1 ≤ y.1` for the entries of the tuples of `S`.  For the restricted
tuple set `descS S w₀` this cannot hold (the appended `(0,0)` has weight `0`), while the entries of
the *index set* `tmI (descS S w₀)` are still positive (they come from `S`).  We therefore state the
MZ property with the positivity hypothesis on `tmI S`. -/

/-- **The MZ property for `tmL`**, with the positivity hypothesis stated on the index set. -/
lemma tmL_frobenius_pow_mem {γ : ℚᵐ⁰} {ω : PowerSeries (Ambient F)}
    (hγ0 : 0 < γ) (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰)
    (hq : 2 ≤ Nat.card F) (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (hpos : ∀ t : ↥(tmI S), ∀ y ∈ t.1, 1 ≤ y.1)
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeriesGen ω ((ambTheta F) ^ (Nat.card F ^ k)) = 0)
    (t : ↥(tmI S)) (k : ℕ) :
    evalSeriesGen (tmL (Nat.card F) ω t.1) ((ambTheta F) ^ (Nat.card F ^ k))
      = (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ k) := by
  rcases List.eq_nil_or_concat t.1 with h | ⟨u, x, h⟩
  · rw [h, tmL_nil]; simp
  · have hcoe : tmCoe (K := Ambient F) (u.concat x)
        = tmCoe (K := Ambient F) u ++ [(x.1, (x.2 : PowerSeries (Ambient F)))] := by
      rw [List.concat_eq_append, tmCoe_append]
      congr 1
    rw [h, tmL, hcoe]
    have hx : x ∈ t.1 := by
      rw [h, List.concat_eq_append]
      exact List.mem_append_right _ (List.mem_singleton_self x)
    refine evalSeriesGen_atLrPaperGen_frobenius_pow (K := Ambient F) (q := Nat.card F)
      (Q := (x.2 : PowerSeries (Ambient F))) hγ0 hγ harch hq hω hωse (tmCoe u) ?_ ?_ x.1 ?_ ?_
      ?_ hc k
    · intro y hy
      rw [tmCoe, List.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      have hz' : z ∈ t.1 := by
        rw [h, List.concat_eq_append]
        exact List.mem_append_left _ hz
      obtain ⟨s, hs, hz''⟩ := mem_tmI_entry F t.2 hz'
      exact hsm s hs z hz''
    · intro y hy
      rw [tmCoe, List.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      have hz' : z ∈ t.1 := by
        rw [h, List.concat_eq_append]
        exact List.mem_append_left _ hz
      obtain ⟨s, hs, hz''⟩ := mem_tmI_entry F t.2 hz'
      exact hSse s hs z hz''
    · exact hpos t x hx
    · obtain ⟨sx, hsx, hx'⟩ := mem_tmI_entry F t.2 hx
      exact hsm sx hsx x hx'
    · obtain ⟨sx, hsx, hx'⟩ := mem_tmI_entry F t.2 hx
      exact hSse sx hsx x hx'


/-! ## §5. The level fields `F_q(θ_ν)` and the level of an element of `K^{perf}`

The ABP criterion (`ABP_criterion_kperf`) requires a *uniform* level `A_ν` for the entries of both
the matrix `Φ` and the "vanishing matrix" `ϑ`.  For the descent, `ϑ` must be built from the
coefficient vector `ρ` of a `K^{perf}`-relation, whose entries are elements of the fields
`F_q(θ_ν) = Frac(A_ν)`.  This section provides the (elementary) fact that finitely many elements of
`K^{perf}` lie in a common `F_q(θ_ν)`.
-/

section RatLevel

/-- The subfield of the ambient field generated by the level-`ν` integers: `F_q(θ_ν)`. -/
noncomputable def ratLevelF (ν : ℕ) : Subfield (Ambient F) :=
  Subfield.closure (ambA F ν)

lemma ratLevelF_mono {ν μ : ℕ} (h : ν ≤ μ) : ratLevelF (F := F) ν ≤ ratLevelF (F := F) μ :=
  Subfield.closure_mono (ambA_mono F h)

lemma ambA_subset_ratLevelF (ν : ℕ) : ambA F ν ⊆ (ratLevelF (F := F) ν : Set (Ambient F)) :=
  Subfield.subset_closure

/-- The set of quotients of elements of `A_ν` is a subfield. -/
noncomputable def ratSetSub (ν : ℕ) : Subfield (Ambient F) where
  carrier := {x | ∃ p ∈ ambA F ν, ∃ q ∈ ambA F ν, q ≠ 0 ∧ p / q = x}
  zero_mem' := ⟨0, (ambASub F ν).zero_mem, 1, (ambASub F ν).one_mem, one_ne_zero, by simp⟩
  one_mem' := ⟨1, (ambASub F ν).one_mem, 1, (ambASub F ν).one_mem, one_ne_zero, by simp⟩
  add_mem' := by
    rintro x y ⟨p, hp, q, hq, hq0, rfl⟩ ⟨p', hp', q', hq', hq'0, rfl⟩
    refine ⟨p * q' + p' * q, ambA_add_mem F (ambA_mul_mem F hp hq') (ambA_mul_mem F hp' hq),
      q * q', ambA_mul_mem F hq hq', mul_ne_zero hq0 hq'0, ?_⟩
    field_simp
  neg_mem' := by
    rintro x ⟨p, hp, q, hq, hq0, rfl⟩
    exact ⟨-p, (ambASub F ν).neg_mem hp, q, hq, hq0, by rw [div_eq_mul_inv, div_eq_mul_inv, neg_mul]⟩
  mul_mem' := by
    rintro x y ⟨p, hp, q, hq, hq0, rfl⟩ ⟨p', hp', q', hq', hq'0, rfl⟩
    refine ⟨p * p', ambA_mul_mem F hp hp', q * q', ambA_mul_mem F hq hq',
      mul_ne_zero hq0 hq'0, ?_⟩
    field_simp
  inv_mem' := by
    rintro x ⟨p, hp, q, hq, hq0, rfl⟩
    by_cases hp0 : p = 0
    · subst hp0
      simp only [zero_div]
      exact ⟨0, (ambASub F ν).zero_mem, 1, (ambASub F ν).one_mem, one_ne_zero, by simp⟩
    · exact ⟨q, hq, p, hp, hp0, by field_simp⟩

/-- The elements of `F_q(θ_ν)` are exactly the quotients of elements of `A_ν`. -/
lemma mem_ratLevelF_iff (ν : ℕ) (x : Ambient F) :
    x ∈ ratLevelF (F := F) ν ↔ ∃ p ∈ ambA F ν, ∃ q ∈ ambA F ν, q ≠ 0 ∧ p / q = x := by
  constructor
  · intro hx
    have hle : ratLevelF (F := F) ν ≤ ratSetSub (F := F) ν :=
      Subfield.closure_le.mpr fun y hy => ⟨y, hy, 1, (ambASub F ν).one_mem, one_ne_zero, by simp⟩
    exact hle hx
  · rintro ⟨p, hp, q, hq, hq0, rfl⟩
    exact (ratLevelF (F := F) ν).div_mem (ambA_subset_ratLevelF ν hp)
      (ambA_subset_ratLevelF ν hq)

/-- The union of the fields `F_q(θ_ν)` is a subfield; it contains the generators of `K^{perf}`. -/
noncomputable def ratUnion : Subfield (Ambient F) where
  carrier := {x | ∃ ν, x ∈ ratLevelF (F := F) ν}
  zero_mem' := ⟨0, (ratLevelF (F := F) 0).zero_mem⟩
  one_mem' := ⟨0, (ratLevelF (F := F) 0).one_mem⟩
  add_mem' := by
    rintro x y ⟨ν, hν⟩ ⟨μ, hμ⟩
    exact ⟨max ν μ, (ratLevelF (F := F) (max ν μ)).add_mem
      (ratLevelF_mono (F := F) (le_max_left ν μ) hν)
      (ratLevelF_mono (F := F) (le_max_right ν μ) hμ)⟩
  neg_mem' := by
    rintro x ⟨ν, hν⟩
    exact ⟨ν, (ratLevelF (F := F) ν).neg_mem hν⟩
  mul_mem' := by
    rintro x y ⟨ν, hν⟩ ⟨μ, hμ⟩
    exact ⟨max ν μ, (ratLevelF (F := F) (max ν μ)).mul_mem
      (ratLevelF_mono (F := F) (le_max_left ν μ) hν)
      (ratLevelF_mono (F := F) (le_max_right ν μ) hμ)⟩
  inv_mem' := by
    rintro x ⟨ν, hν⟩
    exact ⟨ν, (ratLevelF (F := F) ν).inv_mem hν⟩

lemma ratLevelF_le_ratUnion (ν : ℕ) : ratLevelF (F := F) ν ≤ ratUnion (F := F) :=
  fun x hx => ⟨ν, hx⟩

lemma ambKperf_le_ratUnion : ambKperf F ≤ ratUnion (F := F) := by
  refine Subfield.closure_le.mpr ?_
  rintro x (⟨c, rfl⟩ | ⟨ν, rfl⟩)
  · exact ⟨0, ambA_subset_ratLevelF 0 ((mem_ambA_iff F 0 _).mpr ⟨Polynomial.C c, by rw [Polynomial.eval₂_C, algebraMap_ambient_eq]⟩)⟩
  · exact ⟨ν, ambA_subset_ratLevelF ν (by simpa using ambThetaNu_pow_mem F ν 1)⟩

/-- **Every element of `K^{perf}` lies in some `F_q(θ_ν)`.** -/
lemma exists_ratLevelF_of_mem_ambKperf {x : Ambient F} (hx : x ∈ ambKperf F) :
    ∃ ν, x ∈ ratLevelF (F := F) ν :=
  ambKperf_le_ratUnion hx

/-- **A common level for a finite family of elements of `K^{perf}`.** -/
lemma exists_ratLevelF_forall_of_mem_ambKperf {ι : Type*} (s : Finset ι) (x : ι → Ambient F)
    (hx : ∀ i ∈ s, x i ∈ ambKperf F) : ∃ ν, ∀ i ∈ s, x i ∈ ratLevelF (F := F) ν := by
  classical
  choose lev hlev using fun i (hi : i ∈ s) => exists_ratLevelF_of_mem_ambKperf (hx i hi)
  refine ⟨s.sup fun i => if hi : i ∈ s then lev i hi else 0, fun i hi => ?_⟩
  have hle : lev i hi ≤ s.sup (fun i => if hi : i ∈ s then lev i hi else 0) := by
    have h1 : (fun i => if hi : i ∈ s then lev i hi else 0) i = lev i hi := dif_pos hi
    rw [← h1]
    exact Finset.le_sup (f := fun i => if hi : i ∈ s then lev i hi else 0) hi
  exact ratLevelF_mono (F := F) hle (hlev i hi)

end RatLevel


/-! ## §6. The vanishing matrix `ϑ` with `A_ν`-coefficients

Given `ρ ≠ 0` with entries in a common level field `F_q(θ_ν)`, we construct the matrix `ϑ` required
by the ABP criterion: `|ι| - 1` independent columns, all with `A_ν`-coefficients, annihilated by
`ρ`.  Explicitly, writing `ρ i = p i / q i` with `p i, q i ∈ A_ν` and fixing `i₀` with `ρ i₀ ≠ 0`,
the column attached to `i ≠ i₀` is `p i q i₀ e_{i₀} - p i₀ q i e_i`. -/

lemma exists_aux_theta {ι : Type*} [Fintype ι] [DecidableEq ι] (ν : ℕ)
    {ρ : ι → Ambient F} (hρ0 : ρ ≠ 0) (hρlev : ∀ i, ρ i ∈ ratLevelF (F := F) ν) :
    ∃ ϑ : Matrix ι (Fin (Fintype.card ι - 1)) (Ambient F),
      (∀ i j, ϑ i j ∈ ambA F ν) ∧
      LinearIndependent (Ambient F)
        (fun c : Fin (Fintype.card ι - 1) => fun i : ι => ϑ i c) ∧
      Matrix.vecMul ρ ϑ = 0 := by
  classical
  have hρne : ∃ i, ρ i ≠ 0 := by
    by_contra h
    refine hρ0 (funext fun i => ?_)
    by_contra hh
    exact h ⟨i, hh⟩
  obtain ⟨i₀, hi₀⟩ := hρne
  have hfac : ∀ i, ∃ p q : Ambient F,
      p ∈ ambA F ν ∧ q ∈ ambA F ν ∧ q ≠ 0 ∧ p / q = ρ i := by
    intro i
    obtain ⟨p, hp, q, hq, hq0, hpq⟩ := (mem_ratLevelF_iff ν (ρ i)).mp (hρlev i)
    exact ⟨p, q, hp, hq, hq0, hpq⟩
  choose p q hp hq hq0 hpq using hfac
  have hp0 : p i₀ ≠ 0 := by
    intro h
    have h1 := hpq i₀
    rw [h, zero_div] at h1
    exact hi₀ h1.symm
  have hcard : Fintype.card {i : ι // i ≠ i₀} = Fintype.card ι - 1 := by
    have h := Fintype.card_subtype_compl (p := fun i : ι => i = i₀)
    rw [Fintype.card_subtype_eq] at h
    simpa using h
  let e : {i : ι // i ≠ i₀} ≃ Fin (Fintype.card ι - 1) := Fintype.equivFinOfCardEq hcard
  let col : {i : ι // i ≠ i₀} → ι → Ambient F := fun i j =>
    if j = i₀ then p i.1 * q i₀ else if j = i.1 then -(p i₀ * q i.1) else 0
  let ϑ : Matrix ι (Fin (Fintype.card ι - 1)) (Ambient F) := fun j c => col (e.symm c) j
  have hcol0 : ∀ (i : {i : ι // i ≠ i₀}) (j : ι), j ≠ i₀ → j ≠ i.1 → col i j = 0 := by
    intro i j h1 h2
    simp only [col]
    rw [if_neg h1, if_neg h2]
  have hcol1 : ∀ (i : {i : ι // i ≠ i₀}), col i i₀ = p i.1 * q i₀ := by
    intro i; simp [col]
  have hcol2 : ∀ (i : {i : ι // i ≠ i₀}), col i i.1 = -(p i₀ * q i.1) := by
    intro i
    show (if i.1 = i₀ then p i.1 * q i₀ else if i.1 = i.1 then -(p i₀ * q i.1) else 0)
      = -(p i₀ * q i.1)
    rw [if_neg i.2, if_pos rfl]
  refine ⟨ϑ, ?_, ?_, ?_⟩
  · intro j c
    show col (e.symm c) j ∈ ambA F ν
    by_cases h1 : j = i₀
    · rw [h1, hcol1]
      exact ambA_mul_mem F (hp _) (hq _)
    · by_cases h2 : j = (e.symm c).1
      · rw [h2, hcol2]
        exact (ambASub F ν).neg_mem (ambA_mul_mem F (hp _) (hq _))
      · rw [hcol0 _ _ h1 h2]
        exact ambA_zero_mem ν
  · rw [Fintype.linearIndependent_iff]
    intro g hg c
    have hcoord := congrFun hg (e.symm c).1
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hcoord
    have hsingle : (∑ c' : Fin (Fintype.card ι - 1), g c' * ϑ ((e.symm c).1) c')
        = g c * ϑ ((e.symm c).1) c := by
      refine Finset.sum_eq_single c ?_ ?_
      · intro c' _ hc'
        have hne : (e.symm c').1 ≠ (e.symm c).1 := by
          intro hh
          exact hc' (e.symm.injective (Subtype.ext hh))
        show g c' * col (e.symm c') ((e.symm c).1) = 0
        rw [hcol0 _ _ (e.symm c).2 (Ne.symm hne), mul_zero]
      · intro hc; exact absurd (Finset.mem_univ c) hc
    rw [hsingle] at hcoord
    simp only [ϑ] at hcoord
    rw [hcol2] at hcoord
    rcases mul_eq_zero.mp hcoord with h | h
    · exact h
    · exact absurd h (neg_ne_zero.mpr (mul_ne_zero hp0 (hq0 _)))
  · funext j
    rw [Matrix.vecMul, dotProduct, Pi.zero_apply]
    have h2 : (∑ j' : ι, ρ j' * ϑ j' j) = ρ i₀ * (p (e.symm j).1 * q i₀)
        + ρ (e.symm j).1 * (-(p i₀ * q (e.symm j).1)) := by
      simp only [ϑ]
      have hne : ¬ (i₀ = (e.symm j).1) := fun hh => (e.symm j).2 hh.symm
      rw [Finset.sum_eq_add i₀ (e.symm j).1 hne
        (fun c _ hc => by rw [hcol0 (e.symm j) c hc.1 hc.2, mul_zero])
        (fun h => absurd (Finset.mem_univ i₀) h)
        (fun h => absurd (Finset.mem_univ ((e.symm j).1)) h)]
      rw [hcol1, hcol2]
    rw [h2, ← hpq i₀, ← hpq (e.symm j).1]
    have hq1 : q i₀ ≠ 0 := hq0 i₀
    have hq2 : q (e.symm j).1 ≠ 0 := hq0 (e.symm j).1
    field_simp
    ring


/-! ## §7. The vanishing of the top-weight coefficients (Dac §5.2) -/

/-- The set of indices of the restricted motive of weight `w₀`. -/
noncomputable def descV {S : Finset (List (ℕ × Polynomial (Ambient F)))} (w₀ : ℕ) :
    Finset (↥(tmI (descS S w₀))) :=
  Finset.univ.filter (fun u : ↥(tmI (descS S w₀)) => tmWeight u.1 = w₀)

/-- The value of the `L`-series of an index of the restricted motive at `θ`. -/
noncomputable def descZ {S : Finset (List (ℕ × Polynomial (Ambient F)))} (w₀ : ℕ)
    (ω : PowerSeries (Ambient F)) (u : ↥(tmI (descS S w₀))) : Ambient F :=
  evalSeriesGen (tmL (Nat.card F) ω u.1) (ambTheta F)

/-- The coordinate of the restricted motive corresponding to a top-weight tuple `t₀`. -/
noncomputable def descT {S : Finset (List (ℕ × Polynomial (Ambient F)))} {w₀ : ℕ}
    (t₀ : ↥(tmI S)) (ht₀ : tmWeight t₀.1 = w₀) : ↥(tmI (descS S w₀)) :=
  ⟨t₀.1, mem_tmI_descS_of_mem_descW (mem_descW.mpr ⟨t₀, ht₀, rfl⟩)⟩

/-- A top-weight tuple of `tmI S` is an element of `tmI S`. -/
lemma mem_tmI_of_mem_descW {w₀ : ℕ} {S : Finset (List (ℕ × Polynomial (Ambient F)))}
    {u : List (ℕ × Polynomial (Ambient F))} (hu : u ∈ descW S w₀) : u ∈ tmI S := by
  obtain ⟨t, -, rfl⟩ := mem_descW.mp hu
  exact t.2

@[simp] lemma descT_val {S : Finset (List (ℕ × Polynomial (Ambient F)))} {w₀ : ℕ}
    (t₀ : ↥(tmI S)) (ht₀ : tmWeight t₀.1 = w₀) : (descT (F := F) (w₀ := w₀) t₀ ht₀).1 = t₀.1 :=
  rfl

@[simp] lemma descZ_def {S : Finset (List (ℕ × Polynomial (Ambient F)))} {w₀ : ℕ}
    (ω : PowerSeries (Ambient F)) (u : ↥(tmI (descS S w₀))) :
    descZ (F := F) w₀ ω u = evalSeriesGen (tmL (Nat.card F) ω u.1) (ambTheta F) := rfl

/-- A top-weight index of the restricted motive is an element of `descW S w₀`. -/
lemma mem_descW_of_mem_descV (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1) {w₀ : ℕ}
    {u : ↥(tmI (descS S w₀))} (hu : tmWeight u.1 = w₀) : u.1 ∈ descW S w₀ :=
  mem_descW_of_mem_tmI_descS (S := S) (w₀ := w₀) hpos u.2 hu

lemma linearIndependent_descS {ω : PowerSeries (Ambient F)} {S : Finset (List (ℕ × Polynomial (Ambient F)))}
    {w₀ : ℕ} {t₀ : ↥(tmI S)} (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1)
    (ht₀ : tmWeight t₀.1 = w₀)
    (hind : LinearIndependent (ambKperf F)
      (fun t : {t : ↥(tmI S) // tmWeight t.1 = w₀ ∧ t ≠ t₀} =>
        evalSeriesGen (tmL (Nat.card F) ω t.1.1) (ambTheta F))) :
    LinearIndependent (ambKperf F)
      (fun u : {u : ↥(tmI (descS S w₀)) // tmWeight u.1 = w₀ ∧
          u ≠ descT (F := F) (w₀ := w₀) t₀ ht₀} =>
        evalSeriesGen (tmL (Nat.card F) ω u.1.1) (ambTheta F)) := by
  let hf : {u : ↥(tmI (descS S w₀)) // tmWeight u.1 = w₀ ∧
        u ≠ descT (F := F) (w₀ := w₀) t₀ ht₀} →
      {t : ↥(tmI S) // tmWeight t.1 = w₀ ∧ t ≠ t₀} := fun u =>
    ⟨⟨u.1.1, mem_tmI_of_mem_descW
        (mem_descW_of_mem_tmI_descS (S := S) (w₀ := w₀) (u := u.1.1) hpos u.1.2 u.2.1)⟩,
      u.2.1, fun hh => u.2.2 (Subtype.ext (congrArg (fun x : ↥(tmI S) => x.1) hh))⟩
  have hfinj : Function.Injective hf := fun u v huv => by
    have h1 : u.1.1 = v.1.1 := by
      simpa only [hf] using
        congrArg (fun t : {t : ↥(tmI S) // tmWeight t.1 = w₀ ∧ t ≠ t₀} => t.1.1) huv
    exact Subtype.ext (Subtype.ext h1)
  have hcomp := LinearIndependent.comp hind hf hfinj
  have heq : ((fun t : {t : ↥(tmI S) // tmWeight t.1 = w₀ ∧ t ≠ t₀} =>
        evalSeriesGen (tmL (Nat.card F) ω t.1.1) (ambTheta F)) ∘ hf)
      = (fun u : {u : ↥(tmI (descS S w₀)) // tmWeight u.1 = w₀ ∧
          u ≠ descT (F := F) (w₀ := w₀) t₀ ht₀} =>
        evalSeriesGen (tmL (Nat.card F) ω u.1.1) (ambTheta F)) := by
    funext u
    simp only [Function.comp_apply, hf]
  rwa [heq] at hcomp



/-- **The vanishing step of Dac §5.2.** -/
theorem descent_vanishing {ω : PowerSeries (Ambient F)}
    {S : Finset (List (ℕ × Polynomial (Ambient F)))} (hq : 2 ≤ Nat.card F)
    (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1)
    {w₀ : ℕ} {t₀ : ↥(tmI S)} (ht₀ : tmWeight t₀.1 = w₀)
    (hind : LinearIndependent (ambKperf F)
      (fun t : {t : ↥(tmI S) // tmWeight t.1 = w₀ ∧ t ≠ t₀} =>
        evalSeriesGen (tmL (Nat.card F) ω t.1.1) (ambTheta F)))
    {B : ↥(tmI (descS S w₀)) → Polynomial (Ambient F)}
    (hBmem : ∀ u m, (B u).coeff m ∈ ambKperf F)
    (hBt : B (descT (F := F) (w₀ := w₀) t₀ ht₀) = 0)
    (hrel : ∀ N : ℕ, 2 ≤ N →
      (∑ u ∈ descV (F := F) (S := S) w₀,
        (B u).eval ((ambTheta F) ^ (Nat.card F ^ N))
          * (descZ (F := F) (S := S) w₀ ω u) ^ (Nat.card F ^ N)) = 0) :
    ∀ u : ↥(tmI (descS S w₀)), tmWeight u.1 = w₀ →
      u ≠ descT (F := F) (w₀ := w₀) t₀ ht₀ → B u = 0 := by
  classical
  have hqn : Nat.card F ≠ 0 := FrobPow.ne_zero (Ambient F) (q := Nat.card F)
  have hθmem : ∀ N : ℕ, (ambTheta F) ^ (Nat.card F ^ N) ∈ ambKperf F := fun N =>
    Subfield.pow_mem _ (ambTheta_mem_ambKperf F) _
  have hind' := linearIndependent_descS (F := F) (S := S) (w₀ := w₀) (ω := ω) hpos ht₀ hind
  intro u₀ hu₀ hu₀ne
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      (B u₀).eval ((ambTheta F) ^ (Nat.card F ^ N)) = 0 := by
    rw [Filter.eventually_atTop]
    refine ⟨2, fun N hN => ?_⟩
    obtain ⟨c, hcmem, hc⟩ : ∃ c : ↥(tmI (descS S w₀)) → Ambient F,
        (∀ u, c u ∈ ambKperf F) ∧ ∀ u, (c u) ^ (Nat.card F ^ N)
          = (B u).eval ((ambTheta F) ^ (Nat.card F ^ N)) := by
      have h : ∀ u : ↥(tmI (descS S w₀)), ∃ c ∈ ambKperf F, c ^ (Nat.card F ^ N)
          = (B u).eval ((ambTheta F) ^ (Nat.card F ^ N)) :=
        fun u => exists_pow_pow_eq_of_mem_ambKperf (F := F)
          (Polynomial.eval_mem_ambKperf (F := F) (hBmem u) (hθmem N)) N
      choose c hcmem hc using h
      exact ⟨c, hcmem, hc⟩
    have hqN : Nat.card F ^ N ≠ 0 := pow_ne_zero N hqn
    have hsum : (∑ u ∈ descV (F := F) (S := S) w₀, c u * descZ (F := F) (S := S) w₀ ω u)
        ^ (Nat.card F ^ N) = 0 := by
      haveI : FrobPow (Ambient F) (Nat.card F ^ N) := FrobPow.pow (R := Ambient F) N
      rw [FrobPow.sum_pow_finset]
      have h1 : (∑ u ∈ descV (F := F) (S := S) w₀,
            (c u * descZ (F := F) (S := S) w₀ ω u) ^ (Nat.card F ^ N))
          = ∑ u ∈ descV (F := F) (S := S) w₀,
              (B u).eval ((ambTheta F) ^ (Nat.card F ^ N))
                * (descZ (F := F) (S := S) w₀ ω u) ^ (Nat.card F ^ N) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [mul_pow, hc u]
      rw [h1, hrel N hN]
    have hsum0 : (∑ u ∈ descV (F := F) (S := S) w₀, c u * descZ (F := F) (S := S) w₀ ω u) = 0 :=
      (pow_eq_zero_iff hqN).mp hsum
    let t' : ↥(tmI (descS S w₀)) := descT (F := F) (w₀ := w₀) t₀ ht₀
    have ht'mem : t' ∈ descV (F := F) (S := S) w₀ := by
      rw [descV, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ht₀⟩
    have hct' : c t' = 0 := by
      have h := hc t'
      have hB0 : B t' = 0 := hBt
      rw [hB0, Polynomial.eval_zero] at h
      exact (pow_eq_zero_iff hqN).mp h
    have hdrop : (∑ u ∈ (descV (F := F) (S := S) w₀).erase t',
        c u * descZ (F := F) (S := S) w₀ ω u) = 0 := by
      have h := Finset.sum_erase_add (descV (F := F) (S := S) w₀)
        (fun u => c u * descZ (F := F) (S := S) w₀ ω u) ht'mem
      rw [hsum0, hct', zero_mul, add_zero] at h
      exact h
    have hiff : ∀ u : ↥(tmI (descS S w₀)),
        u ∈ (descV (F := F) (S := S) w₀).erase t' ↔ (tmWeight u.1 = w₀ ∧ u ≠ t') := by
      intro u
      rw [Finset.mem_erase, descV, Finset.mem_filter]
      constructor
      · rintro ⟨hne, -, hw⟩; exact ⟨hw, hne⟩
      · rintro ⟨hw, hne⟩; exact ⟨hne, Finset.mem_univ _, hw⟩
    have hsub : (∑ a : {u : ↥(tmI (descS S w₀)) // tmWeight u.1 = w₀ ∧ u ≠ t'},
        (⟨c a.1, hcmem a.1⟩ : ↥(ambKperf F))
          • (evalSeriesGen (tmL (Nat.card F) ω a.1.1) (ambTheta F))) = 0 := by
      have h1 : (∑ a : {u : ↥(tmI (descS S w₀)) // tmWeight u.1 = w₀ ∧ u ≠ t'},
            (⟨c a.1, hcmem a.1⟩ : ↥(ambKperf F))
              • (evalSeriesGen (tmL (Nat.card F) ω a.1.1) (ambTheta F)))
          = ∑ a : {u : ↥(tmI (descS S w₀)) // tmWeight u.1 = w₀ ∧ u ≠ t'},
              c a.1 * descZ (F := F) (S := S) w₀ ω a.1 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [descZ_def]
        rfl
      rw [h1, ← Finset.sum_subtype ((descV (F := F) (S := S) w₀).erase t')
        (p := fun u : ↥(tmI (descS S w₀)) => tmWeight u.1 = w₀ ∧ u ≠ t') hiff
        (fun u => c u * descZ (F := F) (S := S) w₀ ω u)]
      exact hdrop
    have hczero := (Fintype.linearIndependent_iff.mp hind')
      (fun a : {u : ↥(tmI (descS S w₀)) // tmWeight u.1 = w₀ ∧ u ≠ t'} =>
        (⟨c a.1, hcmem a.1⟩ : ↥(ambKperf F)))
      hsub ⟨u₀, hu₀, hu₀ne⟩
    have hcu₀ : c u₀ = 0 := congrArg (fun x : ↥(ambKperf F) => (x : Ambient F)) hczero
    rw [← hc u₀, hcu₀, zero_pow hqN]
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

end Restricted

end ZagierHoffmanPositiveChar
