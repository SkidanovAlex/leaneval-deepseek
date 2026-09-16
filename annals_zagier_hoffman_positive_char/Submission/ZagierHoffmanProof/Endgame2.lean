import Submission.ZagierHoffmanProof.TpAux
import Submission.ZagierHoffmanProof.TheoremB
import Submission.ZagierHoffmanProof.HDatum
import Submission.ZagierHoffmanProof.TpCount
import Submission.ZagierHoffmanProof.LinearIndependence
import Submission.ZagierHoffmanProof.Rationality

/-!
# Dac §6, Step 3(c): the two-term datum `{(w), (k, q-1)}` of the endgame

This file sets up the datum `S = {(w), (k,q-1)}` of Dac's Theorem 6.2 Step 3 (`q < w = k+q-1 ≤
2q-2`, `2 ≤ k ≤ q-1`) for the workspace's `t`-motive normalisation:

* the index set of the merged `t`-motive is `tmI S = {[], [(k,1)]}`;
* the row of `tmB` at the empty column (`tmB_col_eq`, `tmB_nil_row`);
* the divisibility consequences of the two surviving rows.

The endgame itself (Dac's (6.3)–(6.5)) is the content of the follow-up module.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
open Polynomial PowerSeries Finset Matrix
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. The two-term datum -/

/-- The one-entry exponent tuple `(w)`. -/
noncomputable def twS1 (w : ℕ) (hw : 0 < w) : Fin 1 → ℕ+ := fun _ => ⟨w, hw⟩

/-- The two-entry exponent tuple `(k, q-1)`. -/
noncomputable def twS2 (k : ℕ) (hk : 0 < k) : Fin 2 → ℕ+ :=
  ![⟨k, hk⟩, ⟨Nat.card F - 1, by have := two_le_ambCard F; omega⟩]

@[simp] lemma twS2_zero (k : ℕ) (hk : 0 < k) : twS2 F k hk 0 = ⟨k, hk⟩ := rfl

@[simp] lemma twS2_one (k : ℕ) (hk : 0 < k) :
    twS2 F k hk 1 = ⟨Nat.card F - 1, by have := two_le_ambCard F; omega⟩ := rfl

lemma twS1_list (w : ℕ) (hw : 0 < w) :
    tupleListHP F (twS1 w hw) = [(w, (ambH F w : Polynomial (Ambient F)))] := by
  simp [tupleListHP, twS1]

lemma twS2_list (k : ℕ) (hk : 0 < k) :
    tupleListHP F (twS2 F k hk)
    = [(k, (ambH F k : Polynomial (Ambient F))),
       (Nat.card F - 1, (ambH F (Nat.card F - 1) : Polynomial (Ambient F)))] := by
  simp [tupleListHP, twS2]

/-- The datum `S = {(w), (k,q-1)}`. -/
noncomputable def twDatum (w k : ℕ) (hw : 0 < w) (hk : 0 < k) :
    Finset (List (ℕ × Polynomial (Ambient F))) :=
  {tupleListHP F (twS1 w hw), tupleListHP F (twS2 F k hk)}

lemma twDatum_mem₁ (w k : ℕ) (hw : 0 < w) (hk : 0 < k) :
    tupleListHP F (twS1 w hw) ∈ twDatum F w k hw hk := by simp [twDatum]

lemma twDatum_mem₂ (w k : ℕ) (hw : 0 < w) (hk : 0 < k) :
    tupleListHP F (twS2 F k hk) ∈ twDatum F w k hw hk := by simp [twDatum]

lemma tmWeight_twS1 (w : ℕ) (hw : 0 < w) :
    tmWeight (K := Ambient F) (tupleListHP F (twS1 w hw)) = w := by
  rw [twS1_list]; simp [tmWeight]

lemma tmWeight_twS2 (k : ℕ) (hk : 0 < k) :
    tmWeight (K := Ambient F) (tupleListHP F (twS2 F k hk)) = k + (Nat.card F - 1) := by
  rw [twS2_list]; simp [tmWeight]

lemma tmI_twDatum (w k : ℕ) (hw : 0 < w) (hk : 0 < k) (hkq : k ≤ Nat.card F - 1) :
    tmI (twDatum F w k hw hk) = {[], [(k, (1 : Polynomial (Ambient F)))]} := by
  have hlen1 : (tupleListHP F (twS1 w hw)).length = 1 := by rw [twS1_list]; simp
  have hlen2 : (tupleListHP F (twS2 F k hk)).length = 2 := by rw [twS2_list]; simp
  ext t
  rw [mem_tmI]
  constructor
  · rintro ⟨s, hs, j, hj, rfl⟩
    simp only [twDatum, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · rw [hlen1] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      simp
    · rw [hlen2] at hj
      have hj2 : j = 0 ∨ j = 1 := by omega
      rcases hj2 with rfl | rfl
      · simp
      · rw [twS2_list]
        have hk1 : ambH F k = 1 := ambH_of_le F (show k ≤ Nat.card F by omega)
        simp [hk1]
  · intro ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · refine ⟨tupleListHP F (twS1 w hw), twDatum_mem₁ F w k hw hk, 0, ?_, ?_⟩
      · rw [hlen1]; omega
      · rw [twS1_list]; simp
    · refine ⟨tupleListHP F (twS2 F k hk), twDatum_mem₂ F w k hw hk, 1, ?_, ?_⟩
      · rw [hlen2]; omega
      · rw [twS2_list]
        have hk1 : ambH F k = 1 := ambH_of_le F (show k ≤ Nat.card F by omega)
        simp [hk1]


end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §2. The row of `tmB` at a general column -/

lemma tmB_col_eq {w : ℕ} {S : Finset (List (ℕ × Polynomial (Ambient F)))}
    {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}
    {P : Option ↥(tmI S) → Polynomial (Ambient F)}
    {t' : List (ℕ × Polynomial (Ambient F))} (ht' : t' ∈ tmI S) :
    tmB F w S cf P (some ⟨t', ht'⟩)
      = P none * polyTwist (q := Nat.card F) 1 (P (some ⟨t', ht'⟩))
        - polyTwist (q := Nat.card F) 1 (P none)
          * (P none * tmV (Nat.card F) (ambTheta F) w S cf t'
              + ∑ t : ↥(tmI S), P (some t) * tmA (Nat.card F) (ambTheta F) w t.1 t') := by
  rw [tmB, Fintype.sum_option]
  simp only [tmAOpt_none_some, tmAOpt_some_some]

/-! ## §3. The elementary `tmA` values at the empty column -/

lemma tmA_nil_nil (q : ℕ) (θ : Ambient F) (w : ℕ) :
    tmA q θ w ([] : List (ℕ × Polynomial (Ambient F))) [] =
      (Polynomial.X - Polynomial.C (θ ^ q)) ^ w := by
  rw [tmA_diag]; rfl

lemma tmA_singleton_nil (q : ℕ) (θ : Ambient F) (w : ℕ)
    (x : ℕ × Polynomial (Ambient F)) :
    tmA q θ w [x] ([] : List (ℕ × Polynomial (Ambient F))) =
      x.2 * (Polynomial.X - Polynomial.C (θ ^ q)) ^ w := by
  rw [tmA]
  simp [tmWeight]

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §4. The empty and the `(k)`-columns of the two-term datum -/

/-- The empty column. -/
noncomputable def twNil (w k : ℕ) (hw : 0 < w) (hk : 0 < k) (hkq : k ≤ Nat.card F - 1) :
    ↥(tmI (twDatum F w k hw hk)) :=
  ⟨[], by rw [tmI_twDatum F w k hw hk hkq]; simp⟩

/-- The `(k)`-column. -/
noncomputable def twK (w k : ℕ) (hw : 0 < w) (hk : 0 < k) (hkq : k ≤ Nat.card F - 1) :
    ↥(tmI (twDatum F w k hw hk)) :=
  ⟨[(k, (1 : Polynomial (Ambient F)))], by rw [tmI_twDatum F w k hw hk hkq]; simp⟩

@[simp] lemma twNil_val (w k : ℕ) (hw : 0 < w) (hk : 0 < k) (hkq : k ≤ Nat.card F - 1) :
    (twNil F w k hw hk hkq).1 = [] := rfl

@[simp] lemma twK_val (w k : ℕ) (hw : 0 < w) (hk : 0 < k) (hkq : k ≤ Nat.card F - 1) :
    (twK F w k hw hk hkq).1 = [(k, (1 : Polynomial (Ambient F)))] := rfl

lemma twNil_ne_twK (w k : ℕ) (hw : 0 < w) (hk : 0 < k) (hkq : k ≤ Nat.card F - 1) :
    twNil F w k hw hk hkq ≠ twK F w k hw hk hkq := by
  intro h
  have h2 : ([] : List (ℕ × Polynomial (Ambient F))) = [(k, 1)] :=
    congrArg Subtype.val h
  simpa using h2

lemma univ_twDatum (w k : ℕ) (hw : 0 < w) (hk : 0 < k) (hkq : k ≤ Nat.card F - 1) :
    (Finset.univ : Finset ↥(tmI (twDatum F w k hw hk)))
      = {twNil F w k hw hk hkq, twK F w k hw hk hkq} := by
  ext t
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  have ht : t.1 ∈ ({[], [(k, (1 : Polynomial (Ambient F)))]} :
      Finset (List (ℕ × Polynomial (Ambient F)))) := by
    simpa only [tmI_twDatum F w k hw hk hkq] using t.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with h | h
  · left; exact Subtype.ext h
  · right; exact Subtype.ext h

/-- The `v`-term of the empty column. -/
lemma tmV_nil_tw {w k : ℕ} (hw : 0 < w) (hk : 0 < k) (hkq : k ≤ Nat.card F - 1)
    (cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)) :
    tmV (Nat.card F) (ambTheta F) w (twDatum F w k hw hk) cf [] =
      cf (tupleListHP F (twS1 w hw)) * ambH F w *
        (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w := by
  have hne : tupleListHP F (twS1 w hw) ≠ tupleListHP F (twS2 F k hk) := by
    rw [twS1_list, twS2_list]; simp
  rw [tmV, twDatum, Finset.sum_pair hne]
  rw [if_pos (by rw [twS1_list]; simp), if_neg (by rw [twS2_list]; simp)]
  simp only [add_zero, tmWeight, List.map_nil, List.sum_nil, tsub_zero, tmQ]
  rw [twS1_list]
  simp

/-- The sum of the `tmA`-terms of the empty column. -/
lemma sum_tmA_nil_tw {w k : ℕ} (hw : 0 < w) (hk : 0 < k) (hkq : k ≤ Nat.card F - 1)
    (P : Option ↥(tmI (twDatum F w k hw hk)) → Polynomial (Ambient F)) :
    (∑ t : ↥(tmI (twDatum F w k hw hk)),
        P (some t) * tmA (Nat.card F) (ambTheta F) w t.1 [])
      = (P (some (twNil F w k hw hk hkq)) + P (some (twK F w k hw hk hkq)))
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w := by
  rw [univ_twDatum F w k hw hk hkq,
    Finset.sum_pair (twNil_ne_twK F w k hw hk hkq)]
  rw [twNil_val, twK_val, tmA_nil_nil, tmA_singleton_nil]
  ring

/-- **The row of `tmB` at the empty column of the two-term datum.** -/
theorem tmB_nil_row {w k : ℕ} (hw : 0 < w) (hk : 0 < k) (hkq : k ≤ Nat.card F - 1)
    (cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F))
    (P : Option ↥(tmI (twDatum F w k hw hk)) → Polynomial (Ambient F)) :
    tmB F w (twDatum F w k hw hk) cf P (some (twNil F w k hw hk hkq))
      = P none * polyTwist (q := Nat.card F) 1 (P (some (twNil F w k hw hk hkq)))
        - polyTwist (q := Nat.card F) 1 (P none)
          * ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
              * (P none * (cf (tupleListHP F (twS1 w hw)) * ambH F w)
                 + P (some (twNil F w k hw hk hkq))
                 + P (some (twK F w k hw hk hkq)))) := by
  have hnil : (some (twNil F w k hw hk hkq) : Option ↥(tmI (twDatum F w k hw hk)))
      = some ⟨[], (twNil F w k hw hk hkq).2⟩ := rfl
  have h := tmB_col_eq (F := F) (w := w) (S := twDatum F w k hw hk) (cf := cf) (P := P)
    (t' := []) (twNil F w k hw hk hkq).2
  rw [hnil, h, tmV_nil_tw F hw hk hkq cf, sum_tmA_nil_tw F hw hk hkq P, hnil]
  ring

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §5. The `(LW)` input at the two nontrivial levels of the two-term datum -/

/-- `LinearIndependent` for a family whose index type is a subsingleton, with a nonvanishing
value. -/
lemma linearIndependent_of_subsingleton {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [Subsingleton ι] (f : ι → K) (i : ι) (h : f i ≠ 0) : LinearIndependent K f := by
  rw [Fintype.linearIndependent_iffₛ]
  intro a b hab j
  have hji : j = i := Subsingleton.elim j i
  rw [hji]
  have huniv : (Finset.univ : Finset ι) = {i} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨Finset.mem_univ i, fun b _ => Subsingleton.elim b i⟩
  have h1 : (∑ x, a x • f x) = a i • f i := by rw [huniv, Finset.sum_singleton]
  have h2 : (∑ x, b x • f x) = b i • f i := by rw [huniv, Finset.sum_singleton]
  rw [h1, h2] at hab
  have h3 : (a i - b i) • f i = 0 := by rw [sub_smul, hab, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right h)

/-- The `L`-series value at the empty tuple is `1`. -/
@[simp] lemma tmZ_nil : tmZ (F := F) (ambOmega F) ([] : List (ℕ × Polynomial (Ambient F))) = 1 := by
  rw [tmZ, tmL_nil, evalSeriesGen_one]

/-- The `L`-series value at `(k)` does not vanish (the single-entry bridge). -/
lemma tmZ_twK_ne_zero {k : ℕ} (hk : 0 < k) (hkq : k ≤ Nat.card F - 1) :
    tmZ (F := F) (ambOmega F) [(k, (1 : Polynomial (Ambient F)))] ≠ 0 := by
  intro hzero
  set 𝔰 : Fin 1 → ℕ+ := fun _ => ⟨k, hk⟩ with h𝔰
  have hlist : tupleListP F 𝔰 = [(k, (1 : Polynomial (Ambient F)))] := by
    simp [tupleListP, h𝔰, Fin.forall_fin_one]
  have hOK : EntriesOK F 𝔰 := fun j => by
    rw [h𝔰]; simpa using le_trans hkq (Nat.sub_le _ _)
  have hbridge := bridge_tuple (F := F) 𝔰 (by norm_num) hOK
  have hzeta : ζ_A F 𝔰 ≠ 0 := zeta_entries_ne_zero F (by norm_num) 𝔰 hOK
  have hinf : ambInfHom F (ζ_A F 𝔰) ≠ 0 := fun h => hzeta (ambInfHom_injective F (by rw [h, map_zero]))
  have hsum : (∑ j : Fin 1, ((𝔰 j : ℕ))) = k := by simp [h𝔰]
  rw [hsum, hlist] at hbridge
  have hzero' : evalSeriesGen (tmL (Nat.card F) (ambOmega F)
      [(k, (1 : Polynomial (Ambient F)))]) (ambTheta F) = 0 := by
    simpa only [tmZ] using hzero
  rw [hzero', mul_zero] at hbridge
  exact hinf hbridge.symm

end ZagierHoffmanPositiveChar
namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

lemma linearIndependent_of_isEmpty {K : Type*} [Field K] {ι : Type*} [Fintype ι] [IsEmpty ι]
    (f : ι → K) : LinearIndependent K f := by
  rw [Fintype.linearIndependent_iffₛ]
  intro a b hab i
  exact (IsEmpty.false i).elim

/-- The elements of `tmI (twDatum …)` are the empty tuple and the `(k)`-column. -/
lemma twDatum_cases {w k : ℕ} (hw : 0 < w) (hk : 0 < k) (hkq : k ≤ Nat.card F - 1)
    (t : ↥(tmI (twDatum F w k hw hk))) :
    t.1 = [] ∨ t.1 = [(k, (1 : Polynomial (Ambient F)))] := by
  have ht : t.1 ∈ ({[], [(k, (1 : Polynomial (Ambient F)))]} :
      Finset (List (ℕ × Polynomial (Ambient F)))) := by
    simpa only [tmI_twDatum F w k hw hk hkq] using t.2
  simpa only [Finset.mem_insert, Finset.mem_singleton] using ht

lemma tmWeight_twK (k : ℕ) : tmWeight (K := Ambient F) [(k, (1 : Polynomial (Ambient F)))] = k := by
  simp [tmWeight]

/-- At level `0` the only element of `tmI (twDatum …)` is the empty tuple. -/
lemma twDatum_level_zero_eq_nil {w k : ℕ} (hw : 0 < w) (hk : 0 < k)
    (hkq : k ≤ Nat.card F - 1) (t : ↥(tmI (twDatum F w k hw hk)))
    (ht : tmWeight (K := Ambient F) t.1 = 0) : t.1 = [] := by
  rcases twDatum_cases F hw hk hkq t with h | h
  · exact h
  · rw [h, tmWeight_twK] at ht
    omega

/-- At level `k` the only element of `tmI (twDatum …)` is the `(k)`-column. -/
lemma twDatum_level_k_eq {w k : ℕ} (hw : 0 < w) (hk : 0 < k) (hkq : k ≤ Nat.card F - 1)
    (t : ↥(tmI (twDatum F w k hw hk))) (ht : tmWeight (K := Ambient F) t.1 = k) :
    t.1 = [(k, (1 : Polynomial (Ambient F)))] := by
  rcases twDatum_cases F hw hk hkq t with h | h
  · rw [h] at ht
    simp [tmWeight] at ht
    omega
  · exact h

lemma twDatum_subsingleton_zero {w k : ℕ} (hw : 0 < w) (hk : 0 < k)
    (hkq : k ≤ Nat.card F - 1) :
    Subsingleton {t : ↥(tmI (twDatum F w k hw hk)) // tmWeight (K := Ambient F) t.1 = 0} :=
  ⟨fun a b => Subtype.ext (Subtype.ext (by
    rw [twDatum_level_zero_eq_nil F hw hk hkq a a.2,
      twDatum_level_zero_eq_nil F hw hk hkq b b.2]))⟩

lemma twDatum_subsingleton_k {w k : ℕ} (hw : 0 < w) (hk : 0 < k) (hkq : k ≤ Nat.card F - 1) :
    Subsingleton {t : ↥(tmI (twDatum F w k hw hk)) // tmWeight (K := Ambient F) t.1 = k} :=
  ⟨fun a b => Subtype.ext (Subtype.ext (by
    rw [twDatum_level_k_eq F hw hk hkq a a.2, twDatum_level_k_eq F hw hk hkq b b.2]))⟩

/-- `LinearIndependent R f` for a module-valued family on a subsingleton index type with a
nonvanishing value. -/
lemma linearIndependent_of_subsingleton_module {R M : Type*} [Field R] [AddCommGroup M]
    [Module R M] [NoZeroSMulDivisors R M] {ι : Type*} [Fintype ι] [Subsingleton ι]
    (f : ι → M) (i : ι) (h : f i ≠ 0) : LinearIndependent R f := by
  rw [Fintype.linearIndependent_iffₛ]
  intro a b hab j
  have hji : j = i := Subsingleton.elim j i
  rw [hji]
  have huniv : (Finset.univ : Finset ι) = {i} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨Finset.mem_univ i, fun b _ => Subsingleton.elim b i⟩
  have h1 : (∑ x, a x • f x) = a i • f i := by rw [huniv, Finset.sum_singleton]
  have h2 : (∑ x, b x • f x) = b i • f i := by rw [huniv, Finset.sum_singleton]
  rw [h1, h2] at hab
  have h3 : (a i - b i) • f i = 0 := by rw [sub_smul, hab, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right h)

/-- **The `(LW)` input for the two-term datum**: at every weight level the `L`-series values of
`tmI (twDatum …)` are `ambK`-independent. -/
theorem hLW_twDatum {w k : ℕ} (hw : 0 < w) (hk : 0 < k) (hkq : k ≤ Nat.card F - 1) :
    ∀ w' : ℕ, w' ≤ w → LinearIndependent (ambK F)
      (fun t : {t : ↥(tmI (twDatum F w k hw hk)) // tmWeight (K := Ambient F) t.1 = w'} =>
        tmZ (F := F) (ambOmega F) t.1.1) := by
  intro w' _
  rcases eq_or_ne w' 0 with h0 | h0
  · subst h0
    haveI := twDatum_subsingleton_zero F hw hk hkq
    refine linearIndependent_of_subsingleton_module (R := ambK F) (M := Ambient F)
      (f := fun t : {t : ↥(tmI (twDatum F w k hw hk)) //
          tmWeight (K := Ambient F) t.1 = 0} => tmZ (F := F) (ambOmega F) t.1.1)
      ⟨twNil F w k hw hk hkq, by rw [twNil_val]; simp [tmWeight]⟩ ?_
    rw [twNil_val, tmZ_nil]
    exact one_ne_zero
  · rcases eq_or_ne w' k with hk' | hk'
    · rw [hk']
      haveI := twDatum_subsingleton_k F hw hk hkq
      refine linearIndependent_of_subsingleton_module (R := ambK F) (M := Ambient F)
        (f := fun t : {t : ↥(tmI (twDatum F w k hw hk)) //
            tmWeight (K := Ambient F) t.1 = k} => tmZ (F := F) (ambOmega F) t.1.1)
        ⟨twK F w k hw hk hkq, by rw [twK_val, tmWeight_twK]⟩ ?_
      rw [twK_val]
      exact tmZ_twK_ne_zero F hk hkq
    · haveI : IsEmpty {t : ↥(tmI (twDatum F w k hw hk)) //
          tmWeight (K := Ambient F) t.1 = w'} := ⟨fun t => by
        have ht := t.2
        rcases twDatum_cases F hw hk hkq t.1 with h | h
        · rw [h] at ht
          simp [tmWeight] at ht
          exact h0 ht.symm
        · rw [h, tmWeight_twK] at ht
          exact hk' ht.symm⟩
      rw [Fintype.linearIndependent_iffₛ]
      intro a b hab t
      exact (IsEmpty.false t).elim

-- NEXT (SESSION 350/351): `tw_second_relation` — the instantiation of `tmABP_a_leading_kperf` +
-- `step2_B_zero` for `twDatum` (adapt `ACMplDatum.acmpl_second_relation`).  All its inputs are now
-- available: the analytic hypotheses from `HDatum` (`gIsSmall_ambOmega_pow_mul_ambH`,
-- `gSuperEntire_ambH`, `ambH_coeff_mem`), `hLW_twDatum` above, `tmV_nil_tw`/`sum_tmA_nil_tw`,
-- and then `tmB_nil_row` gives Dac's (6.5).

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §6. The ABP second relation for the two-term datum -/

/-- The coefficient function of the two-term datum: `A₁` on `(w)`, `A₂` on `(k,q-1)`. -/
noncomputable def twCf {w k : ℕ} (hw : 0 < w) (hk : 0 < k)
    (A₁ A₂ : Polynomial (Ambient F)) :
    List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F) :=
  fun s => if s = tupleListHP F (twS1 w hw) then A₁ else A₂

lemma twCf_mem₁ {w k : ℕ} (hw : 0 < w) (hk : 0 < k) (A₁ A₂ : Polynomial (Ambient F)) :
    twCf F hw hk A₁ A₂ (tupleListHP F (twS1 w hw)) = A₁ := by
  simp [twCf]

lemma twCf_mem₂ {w k : ℕ} (hw : 0 < w) (hk : 0 < k) (A₁ A₂ : Polynomial (Ambient F)) :
    twCf F hw hk A₁ A₂ (tupleListHP F (twS2 F k hk)) = A₂ := by
  have hne : tupleListHP F (twS1 w hw) ≠ tupleListHP F (twS2 F k hk) := by
    rw [twS1_list, twS2_list]; simp
  simp [twCf, hne]

/-- The empty tuple belongs to `tmI (twDatum …)`. -/
lemma twDatum_nil_mem {w k : ℕ} (hw : 0 < w) (hk : 0 < k) :
    ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI (twDatum F w k hw hk) := by
  refine mem_tmI.mpr ⟨tupleListHP F (twS1 w hw), twDatum_mem₁ F w k hw hk, 0, ?_, by simp⟩
  rw [twS1_list]; simp

/-- **The ABP second relation (Dac §5.2) for the two-term datum.**  From the `(LD)` input (the
`L`-series relation) one gets a row `P` with `P·ψ = 0`, `P(θ) = tmRho`, `K^{perf}`-coefficients,
`P none ≠ 0`, and the vanishing of all the coefficients `B̃_t = tmB … P (some t)` of the second
relation. -/
theorem tw_second_relation {w k : ℕ} (hq : 3 ≤ Nat.card F) (hw : 0 < w) (hk : 0 < k)
    (hwk : w = k + (Nat.card F - 1)) (hkq : k ≤ Nat.card F - 1)
    (A₁ A₂ : Polynomial (Ambient F))
    (hA₁inv : frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((A₁ : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((A₁ : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hA₂inv : frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((A₂ : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((A₂ : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hval : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w (twDatum F w k hw hk)
        (twCf F hw hk A₁ A₂) ([] : List (ℕ × Polynomial (Ambient F)))) (ambTheta F)
      + (0 : Polynomial (Ambient F)).eval (ambTheta F) = 0) :
    ∃ P : Option ↥(tmI (twDatum F w k hw hk)) → Polynomial (Ambient F),
      (∑ j, coeHom (K := Ambient F) (P j)
          * tmPsiColA F (ambOmega F) w (twDatum F w k hw hk) (twCf F hw hk A₁ A₂)
              (twDatum_nil_mem F hw hk) 0 j = 0) ∧
      (∀ j, (P j).eval (ambTheta F) = tmRho F (twDatum F w k hw hk) j) ∧
      (∀ j m, (P j).coeff m ∈ ambKperf F) ∧
      P none ≠ 0 ∧
      (∀ t : ↥(tmI (twDatum F w k hw hk)),
        tmB F w (twDatum F w k hw hk) (twCf F hw hk A₁ A₂) P (some t) = 0) := by
  classical
  set S := twDatum F w k hw hk with hS
  set cf := twCf F hw hk A₁ A₂ with hcf
  have h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S := by
    rw [hS]; exact twDatum_nil_mem F hw hk
  have hmemA₁ : ∀ m, A₁.coeff m ∈ ambA F 0 := by
    intro m
    exact ambF_subset_ambA_zero (by
      have h1 := coeff_mem_ambF_of_frobTwist_one_eq (F := F)
        (f := (A₁ : PowerSeries (Ambient F))) hA₁inv m
      simpa only [Polynomial.coeff_coe] using h1)
  have hmemA₂ : ∀ m, A₂.coeff m ∈ ambA F 0 := by
    intro m
    exact ambF_subset_ambA_zero (by
      have h1 := coeff_mem_ambF_of_frobTwist_one_eq (F := F)
        (f := (A₂ : PowerSeries (Ambient F))) hA₂inv m
      simpa only [Polynomial.coeff_coe] using h1)
  have hcfmem : ∀ s ∈ S, ∀ m, (cf s).coeff m ∈ ambA F 0 := by
    intro s hs m
    rw [hS] at hs
    simp only [twDatum, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · rw [hcf, twCf_mem₁]; exact hmemA₁ m
    · rw [hcf, twCf_mem₂]; exact hmemA₂ m
  have hcfinv : ∀ s ∈ S, frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F)) := by
    intro s hs
    rw [hS] at hs
    simp only [twDatum, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · rw [hcf, twCf_mem₁]; exact hA₁inv
    · rw [hcf, twCf_mem₂]; exact hA₂inv
  have hwS : ∀ s ∈ S, tmWeight s = w := by
    intro s hs
    rw [hS] at hs
    simp only [twDatum, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · rw [tmWeight_twS1]
    · rw [tmWeight_twS2]; omega
  have hposS : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1 := by
    intro s hs y hy
    rw [hS] at hs
    simp only [twDatum, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · rw [twS1_list] at hy
      simp only [List.mem_singleton] at hy
      rw [hy]; exact hw
    · rw [twS2_list] at hy
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact hk
      · omega
  have hneS : ∀ s ∈ S, s ≠ [] := by
    intro s hs
    rw [hS] at hs
    simp only [twDatum, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · rw [twS1_list]; simp
    · rw [twS2_list]; simp
  have hQmem : ∀ s ∈ S, ∀ y ∈ s, ∀ m, (y.2).coeff m ∈ ambA F 0 := by
    intro s hs y hy m
    rw [hS] at hs
    simp only [twDatum, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · rw [twS1_list] at hy
      simp only [List.mem_singleton] at hy
      rw [hy]; exact ambH_coeff_mem F _ m
    · rw [twS2_list] at hy
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact ambH_coeff_mem F _ m
      · exact ambH_coeff_mem F _ m
  have hsm : ∀ s ∈ S, ∀ y ∈ s,
      GIsSmall ambGamma ((ambOmega F) ^ y.1 * (y.2 : PowerSeries (Ambient F))) := by
    intro s hs y hy
    rw [hS] at hs
    simp only [twDatum, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · rw [twS1_list] at hy
      simp only [List.mem_singleton] at hy
      rw [hy]
      exact gIsSmall_ambOmega_pow_mul_ambH F hw
    · rw [twS2_list] at hy
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact gIsSmall_ambOmega_pow_mul_ambH F hk
      · exact gIsSmall_ambOmega_pow_mul_ambH F (by omega)
  have hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire ambGamma ((y.2 : PowerSeries (Ambient F))) := by
    intro s hs y hy
    rw [hS] at hs
    simp only [twDatum, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · rw [twS1_list] at hy
      simp only [List.mem_singleton] at hy
      rw [hy]; exact gSuperEntire_ambH F _
    · rw [twS2_list] at hy
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact gSuperEntire_ambH F _
      · exact gSuperEntire_ambH F _
  have hA : ∀ i j m, (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j).coeff m
      ∈ ambA F 0 := tmAOpt_coeff_mem_ambA0 (F := F) w hQmem hcfmem
  have hle : ∀ t : ↥(tmI S), tmWeight t.1 ≤ w :=
    fun t => tmWeight_le_of_mem_tmI (S := S) (w := w) t.2 (fun s hs => hwS s hs)
  obtain ⟨P, hP, hPθ, hPmem, _⟩ :=
    tmABP_a_leading_kperf (F := F) (ambGamma_pos) (ambGamma_lt_one) gammaArchimedean_rat
      (two_le_ambCard F) (gIsSmall_ambOmega F) (gSuperEntire_ambOmega F) (coeff_zero_ambOmega F)
      (fun k hk => evalSeriesGen_ambOmega_frobenius_orbit F hk) (ambOmega_functional F)
      hwS hcfinv hsm hSse hposS hneS h0 hA
      (by rw [Polynomial.coe_zero, frobTwist_zero]) hval hle le_rfl
  have hΩ0 : (frobTwist (R := Ambient F) (p := Nat.card F) 1 (ambOmega F)).coeff 0 ≠ 0 := by
    rw [frobTwist_coeff, pow_one]
    exact pow_ne_zero _ (coeff_zero_ambOmega F)
  have hΩ1 : ∀ j : ℕ, 2 ≤ j →
      evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1 (ambOmega F))
        ((ambTheta F) ^ (Nat.card F) ^ j) = 0 := by
    intro j hj
    have hq1 : ((ambTheta F) ^ (Nat.card F ^ (j - 1))) ^ (Nat.card F ^ 1)
        = (ambTheta F) ^ (Nat.card F) ^ j := by
      rw [pow_one, ← pow_mul]
      congr 1
      conv_rhs => rw [← Nat.sub_add_cancel (show 1 ≤ j by omega)]
      rw [pow_succ]
    have h := evalSeriesGen_frobTwist (ambGamma_lt_one) gammaArchimedean_rat (Nat.card F)
      (gSuperEntire_ambOmega F) ((ambTheta F) ^ (Nat.card F ^ (j - 1))) 1
    rw [hq1] at h
    have h2 : evalSeriesGen (ambOmega F) ((ambTheta F) ^ (Nat.card F ^ (j - 1))) = 0 :=
      evalSeriesGen_ambOmega_frobenius_orbit F (by omega)
    rw [h2] at h
    have hz : (0 : Ambient F) ^ (Nat.card F ^ 1) = 0 :=
      zero_pow (pow_ne_zero 1 (FrobPow.ne_zero (Ambient F) (q := Nat.card F)))
    rw [hz] at h
    exact h
  have hfe : tmPsiColA F (ambOmega F) w S cf h0 0
      = (coeHom (K := Ambient F)).mapMatrix
          (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) *ᵥ
        frobTwistVec (q := Nat.card F) 1 (tmPsiColA F (ambOmega F) w S cf h0 0) := by
    have hfun := tmPsiColA_functional F (w := w) (cf := cf) (a := (0 : Polynomial (Ambient F)))
      (ambGamma_lt_one) gammaArchimedean_rat (two_le_ambCard F) (gIsSmall_ambOmega F)
      (ambOmega_functional F) hwS hcfinv hsm hneS h0 hA
      (by rw [Polynomial.coe_zero, frobTwist_zero])
    rw [tmPhi_twist_mat F _ hA] at hfun
    exact hfun
  have hB : ∀ t : ↥(tmI S), tmB F w S cf P (some t) = 0 :=
    step2_B_zero (F := F) (ambGamma_pos) (ambGamma_lt_one) gammaArchimedean_rat
      (two_le_ambCard F) (gIsSmall_ambOmega F) (gSuperEntire_ambOmega F)
      (fun k hk => evalSeriesGen_ambOmega_frobenius_orbit F hk) (ambOmega_functional F)
      hΩ0 hΩ1 hsm hSse hposS hQmem hwS h0 hA hfe
      (by rw [hS]; exact hLW_twDatum F hw hk hkq) hPmem hP
  have hP0 : P none ≠ 0 := by
    intro h0'
    have h1 : (P none).eval (ambTheta F) = 1 := by rw [hPθ none, tmRho_none]
    rw [h0', Polynomial.eval_zero] at h1
    exact one_ne_zero h1.symm
  exact ⟨P, hP, hPθ, hPmem, hP0, hB⟩

end ZagierHoffmanPositiveChar
