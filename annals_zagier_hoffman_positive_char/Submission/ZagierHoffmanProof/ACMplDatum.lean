import Submission.ZagierHoffmanProof.LinearIndependence
import Submission.ZagierHoffmanProof.AmbPeriod

/-!
# The CMPL/ACMPL datum of Dac §4.2–§4.3

Dac's alternating Carlitz multiple polylogarithms are the `L`-series of the dual `t`-motive whose
tuple entries are the *constants* `Q_{s_i,ε_i} = γ_i` (with `γ_i^{q-1} = ε_i ∈ F_q^×`); the case
`ε_i = 1` (all `γ_i = 1`) gives the ordinary CMPL `Li(𝔰)` and is the one used for the lower bound
`dim_K 𝒵_w ≥ d(w)` of Dac §5.2.

This file provides

* `tmQ_coeff_mem_of_mem_tmI` and ★★ `tmAOpt_coeff_mem_ambA0`: the `A_0`-coefficient bookkeeping for
  an *arbitrary* datum `(S, cf)` whose entries and coefficients lie in `F_q[θ]` (the existing
  `AbpDescentRestrict.tmAOpt_descS_coeff_mem_ambA0` is the special case of the restricted motive);
* `acmplS`: the CMPL/ACMPL tuple set `𝔰 ↦ [(s_1, C γ), …]` attached to a finset of exponent tuples;
* ★★★ `linear_independence_acmpl`: Dac's §3.3 (the rationality of the `f`-row) for this datum,
  obtained by instantiation of `LinearIndependence.linear_independence` with the period function
  `Ω` of `AmbPeriod.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
open Polynomial Finset Matrix
open scoped WithZero Topology Classical BigOperators

namespace ZagierHoffmanPositiveChar

variable {F : Type*} [Field F] [Finite F]

/-! ## §1. `A_0`-coefficient bookkeeping for a general datum -/

section CoeffMem

variable {S : Finset (List (ℕ × Polynomial (Ambient F)))}
variable {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}

/-- The last-entry polynomial `tmQ` of an element of the index set `tmI S` has `A_0`-coefficients,
provided the entries of the tuples of `S` do. -/
lemma tmQ_coeff_mem_of_mem_tmI
    (hQmem : ∀ s ∈ S, ∀ y ∈ s, ∀ m, (y.2).coeff m ∈ ambA F 0)
    (u : ↥(tmI S)) (m : ℕ) : (tmQ u.1).coeff m ∈ ambA F 0 := by
  rcases List.eq_nil_or_concat u.1 with hnil | ⟨l, x, hcat⟩
  · rw [hnil, tmQ]
    simp only [List.getLastD_nil, Polynomial.coeff_zero]
    exact ambA_zero_mem 0
  · have hx : x ∈ u.1 := by
      rw [hcat, List.concat_eq_append]
      exact List.mem_append_right _ (List.mem_singleton_self x)
    obtain ⟨s₀, hs₀, hx''⟩ := mem_tmI_entry F u.2 hx
    have hQ : tmQ u.1 = x.2 := by
      rw [tmQ, hcat, List.concat_eq_append, List.getLastD_concat]
    rw [hQ]
    exact hQmem s₀ hs₀ x hx'' m

/-- Coefficient-wise membership in `ambA F 0` is preserved by products of polynomials. -/
lemma coeff_mul_mem_ambA0 {p q : Polynomial (Ambient F)}
    (hp : ∀ m, p.coeff m ∈ ambA F 0) (hq : ∀ m, q.coeff m ∈ ambA F 0) (n : ℕ) :
    (p * q).coeff n ∈ ambA F 0 := by
  rw [Polynomial.coeff_mul]
  refine ambA_sum_mem F fun b _ => ambA_mul_mem F (hp b.1) (hq b.2)

/-- The last-entry polynomial `tmQ` of an element of `S` has `A_0`-coefficients. -/
lemma tmQ_coeff_mem_of_mem
    (hQmem : ∀ s ∈ S, ∀ y ∈ s, ∀ m, (y.2).coeff m ∈ ambA F 0)
    {s : List (ℕ × Polynomial (Ambient F))} (hs : s ∈ S) (m : ℕ) :
    (tmQ s).coeff m ∈ ambA F 0 := by
  rcases List.eq_nil_or_concat s with hnil | ⟨l, x, hcat⟩
  · rw [hnil, tmQ]
    simp only [List.getLastD_nil, Polynomial.coeff_zero]
    exact ambA_zero_mem 0
  · have hx : x ∈ s := by
      rw [hcat, List.concat_eq_append]
      exact List.mem_append_right _ (List.mem_singleton_self x)
    have hQ : tmQ s = x.2 := by
      rw [tmQ, hcat, List.concat_eq_append, List.getLastD_concat]
    rw [hQ]
    exact hQmem s hs x hx m

/-- **The `A_0`-coefficient condition for an arbitrary `t`-motive datum** whose tuple entries and
whose `cf`-coefficients lie in `F_q[θ]`. -/
theorem tmAOpt_coeff_mem_ambA0 (w : ℕ)
    (hQmem : ∀ s ∈ S, ∀ y ∈ s, ∀ m, (y.2).coeff m ∈ ambA F 0)
    (hcfmem : ∀ s ∈ S, ∀ m, (cf s).coeff m ∈ ambA F 0) :
    ∀ i j m, (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j).coeff m
      ∈ ambA F 0 := by
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
      rw [tmAOpt_none_some, tmV, Polynomial.finsetSum_coeff]
      refine ambA_sum_mem F fun s hs => ?_
      split_ifs with hdrop
      · have hQ : ∀ n, (tmQ s).coeff n ∈ ambA F 0 := fun n =>
          tmQ_coeff_mem_of_mem hQmem hs n
        exact coeff_mul_mem_ambA0 (coeff_mul_mem_ambA0 (hcfmem s hs) hQ)
          (coeff_X_sub_C_pow_mem hθq _) m
      · exact ambA_zero_mem 0
  | some u =>
    cases j with
    | none =>
      rw [tmAOpt_some_none, Polynomial.coeff_zero]
      exact ambA_zero_mem 0
    | some t' =>
      rw [tmAOpt_some_some, tmA]
      split_ifs with h1 h2
      · exact coeff_X_sub_C_pow_mem hθq _ m
      · exact coeff_mul_mem_ambA0 (tmQ_coeff_mem_of_mem_tmI hQmem u)
          (coeff_X_sub_C_pow_mem hθq _) m
      · rw [Polynomial.coeff_zero]
        exact ambA_zero_mem 0

end CoeffMem

/-! ## §2. The CMPL/ACMPL datum

Dac's ACMPL is the `L`-series of the `t`-motive whose tuple entries are *constants* `Q = γ`
(`γ^{q-1} = ε ∈ F_q^×`); the case `γ = 1` is the CMPL `Li(𝔰)`.  Here `γ` is an element of `ambF F`
(so `γ ∈ F_q`, `ε = 1`: any `(q-1)`-st root of a non-trivial `ε` would require an *algebraically
closed* constant field, which `Ambient F` — the completion of the perfect closure of `F((y))` — does
not have).  What matters for the proof below is only that `γ` is a *constant of valuation* `≤ 1`,
so the file is stated for a general `c ∈ ambF F`. -/

section Datum

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

/-- A constant series of valuation `≤ 1` can be multiplied into a small series without destroying
smallness. -/
lemma GIsSmall.mul_C_of_v_le_one {γ : Γ₀} {f : PowerSeries K} (hf : GIsSmall γ f) {c : K}
    (hc : Valued.v c ≤ 1) : GIsSmall γ (f * PowerSeries.C c) := by
  intro n
  rw [PowerSeries.coeff_mul_C, map_mul]
  exact le_trans (mul_le_mul' (hf n) hc) (le_of_eq (mul_one γ))

end Datum

section ACMpl

/-- The CMPL/ACMPL tuple set attached to a finset of exponent tuples `𝔰`: each entry `(s, Q)` has
`Q` the constant `C c`. -/
noncomputable def acmplS (c : Ambient F) (T : Finset (List ℕ)) :
    Finset (List (ℕ × Polynomial (Ambient F))) :=
  T.image fun s => s.map fun n => (n, Polynomial.C c)

lemma mem_acmplS {c : Ambient F} {T : Finset (List ℕ)}
    {t : List (ℕ × Polynomial (Ambient F))} :
    t ∈ acmplS (F := F) c T ↔ ∃ s ∈ T, s.map (fun n => (n, Polynomial.C c)) = t :=
  Finset.mem_image

lemma tmWeight_map_C (s : List ℕ) (c : Ambient F) :
    tmWeight (s.map fun n => (n, Polynomial.C c)) = s.sum := by
  rw [tmWeight, List.map_map]
  simp [Function.comp_def]

end ACMpl

/-! ## §3. Dac's §3.3 for the CMPL/ACMPL datum

The instantiation of `LinearIndependence.linear_independence` for the datum `(acmplS c T, cf)`: the
period parameter is the Anderson–Thakur period `Ω` of `AmbPeriod.lean`, so the smallness hypotheses
are discharged by `gIsSmall_ambOmega` and the product form `GIsSmall γ (Ω^n · C c)` (which holds
because `Ω` is small and `c` is a constant of valuation `≤ 1`). -/

section Instantiate

variable {c : Ambient F} {w : ℕ} {T : Finset (List ℕ)}
variable {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}

/-- The constant `c ∈ ambF F` has valuation `≤ 1`. -/
lemma v_le_one_of_mem_ambF {x : Ambient F} (hx : x ∈ ambF F) : Valued.v x ≤ 1 := by
  obtain ⟨c₀, rfl⟩ := eq_range_ambCoeff_of_mem_ambF F hx
  rcases eq_or_ne c₀ 0 with rfl | hne
  · have h0 : (ambCoeff F (0 : F)) = 0 := map_zero _
    rw [h0, map_zero]
    exact zero_le_one' ℚᵐ⁰
  · rw [v_ambCoeff F c₀ hne]

lemma mem_ambA_zero_of_mem_ambF {x : Ambient F} (hx : x ∈ ambF F) : x ∈ ambA F 0 := by
  obtain ⟨c₀, rfl⟩ := eq_range_ambCoeff_of_mem_ambF F hx
  exact (mem_ambA_iff F 0 _).mpr ⟨Polynomial.C c₀, by rw [Polynomial.eval₂_C]; rfl⟩

/-- The tuple entries of the CMPL/ACMPL datum have `A_0`-coefficients. -/
lemma acmplS_Qmem (hc : c ∈ ambF F) :
    ∀ s ∈ acmplS (F := F) c T, ∀ y ∈ s, ∀ k, (y.2).coeff k ∈ ambA F 0 := by
  intro s hs y hy k
  obtain ⟨s₀, hs₀, rfl⟩ := mem_acmplS.mp hs
  obtain ⟨n, -, hy'⟩ := List.mem_map.mp hy
  subst hy'
  rcases eq_or_ne k 0 with rfl | hk
  · rw [Polynomial.coeff_C, if_pos rfl]
    exact mem_ambA_zero_of_mem_ambF hc
  · rw [Polynomial.coeff_C, if_neg hk]
    exact ambA_zero_mem 0

/-- The product-form smallness of the CMPL/ACMPL datum. -/
lemma acmplS_small (hc : c ∈ ambF F) (hpos : ∀ s ∈ T, ∀ n ∈ s, 1 ≤ n) :
    ∀ s ∈ acmplS (F := F) c T, ∀ y ∈ s,
      GIsSmall ambGamma ((ambOmega F) ^ y.1 * (y.2 : PowerSeries (Ambient F))) := by
  intro s hs y hy
  obtain ⟨s₀, hs₀, rfl⟩ := mem_acmplS.mp hs
  obtain ⟨n, hn, hy'⟩ := List.mem_map.mp hy
  subst hy'
  have hn1 : 1 ≤ n := hpos s₀ hs₀ n hn
  have hω : GIsSmall ambGamma (ambOmega F) := gIsSmall_ambOmega F
  have hpow : GIsSmall ambGamma ((ambOmega F) ^ n) := by
    rw [show n = (n - 1) + 1 by omega]
    exact hω.pow_add_one ambGamma_le_one (n - 1)
  simpa using hpow.mul_C_of_v_le_one (v_le_one_of_mem_ambF hc)

/-- **Dac's Theorem (linear independence) for the CMPL/ACMPL datum.** -/
theorem linear_independence_acmpl (hc : c ∈ ambF F)
    {w : ℕ} (hT : ∀ s ∈ T, s.sum = w) (hne : ∀ s ∈ T, s ≠ [])
    (hpos : ∀ s ∈ T, ∀ n ∈ s, 1 ≤ n) (hTne : T.Nonempty)
    (hcfmem : ∀ s ∈ acmplS (F := F) c T, ∀ m, (cf s).coeff m ∈ ambA F 0)
    (hcfinv : ∀ s ∈ acmplS (F := F) c T, frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    {a : Polynomial (Ambient F)}
    (ha : frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((a : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((a : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hval : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w (acmplS (F := F) c T) cf
        ([] : List (ℕ × Polynomial (Ambient F)))) (ambTheta F) + a.eval (ambTheta F) = 0)
    (hLW : ∀ w' : ℕ, w' ≤ w → LinearIndependent (ambK F)
      (fun t : {t : ↥(tmI (acmplS (F := F) c T)) // tmWeight t.1 = w'} =>
        tmZ (F := F) (ambOmega F) t.1.1)) :
    ∀ t' : ↥(tmI (acmplS (F := F) c T)),
      evalSeriesGen (tmF (Nat.card F) (ambOmega F) w (acmplS (F := F) c T) cf t'.1)
        (ambTheta F) ∈ ambK F := by
  classical
  have hw : ∀ s ∈ acmplS (F := F) c T, tmWeight s = w := by
    intro s hs
    obtain ⟨s₀, hs₀, rfl⟩ := mem_acmplS.mp hs
    rw [tmWeight_map_C]
    exact hT s₀ hs₀
  have hne' : ∀ s ∈ acmplS (F := F) c T, s ≠ [] := by
    intro s hs hnil
    obtain ⟨s₀, hs₀, rfl⟩ := mem_acmplS.mp hs
    exact hne s₀ hs₀ (List.map_eq_nil_iff.mp hnil)
  have h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI (acmplS (F := F) c T) := by
    obtain ⟨s₀, hs₀⟩ := hTne
    refine mem_tmI.mpr ⟨s₀.map (fun n => (n, Polynomial.C c)),
      mem_acmplS.mpr ⟨s₀, hs₀, rfl⟩, 0, ?_, by simp⟩
    rw [List.length_pos_iff]
    exact fun h => hne s₀ hs₀ (List.map_eq_nil_iff.mp h)
  have hSse : ∀ s ∈ acmplS (F := F) c T, ∀ y ∈ s,
      GSuperEntire ambGamma ((y.2 : PowerSeries (Ambient F))) := by
    intro s hs y hy
    obtain ⟨s₀, hs₀, rfl⟩ := mem_acmplS.mp hs
    obtain ⟨n, -, hy'⟩ := List.mem_map.mp hy
    subst hy'
    simpa using GSuperEntire.C ambGamma c
  exact linear_independence (F := F) (ambGamma_pos) (ambGamma_lt_one) gammaArchimedean_rat
    (two_le_ambCard F) (gIsSmall_ambOmega F) (gSuperEntire_ambOmega F) (coeff_zero_ambOmega F)
    (fun k hk => evalSeriesGen_ambOmega_frobenius_orbit F hk) (ambOmega_functional F)
    hw hcfinv (acmplS_small hc hpos) hSse
    (fun s hs y hy => by
      obtain ⟨s₀, hs₀, rfl⟩ := mem_acmplS.mp hs
      obtain ⟨n, hn, hy'⟩ := List.mem_map.mp hy
      subst hy'
      exact hpos s₀ hs₀ n hn)
    (acmplS_Qmem hc) hne' h0
    (tmAOpt_coeff_mem_ambA0 (F := F) w (acmplS_Qmem hc) hcfmem)
    ha hval hLW


end Instantiate

/-! ## §4. The second relation (Dac §3.3 Step 2) for the CMPL/ACMPL datum

The ABP row `P` together with the vanishing of all the coefficients `B̃_t` of the second relation —
the input of the "cleared δ-system" of Dac §3.3/§4.3. -/

section Second

variable {c : Ambient F} {w : ℕ} {T : Finset (List ℕ)}
variable {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}

/-- The empty tuple belongs to `tmI (acmplS c T)` as soon as `T` is nonempty. -/
lemma acmplS_nil_mem (hne : ∀ s ∈ T, s ≠ []) (hTne : T.Nonempty) :
    ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI (acmplS (F := F) c T) := by
  obtain ⟨s₀, hs₀⟩ := hTne
  refine mem_tmI.mpr ⟨s₀.map (fun n => (n, Polynomial.C c)),
    mem_acmplS.mpr ⟨s₀, hs₀, rfl⟩, 0, ?_, by simp⟩
  rw [List.length_pos_iff]
  exact fun h => hne s₀ hs₀ (List.map_eq_nil_iff.mp h)

/-- **Dac §3.3, Step 2, for the CMPL/ACMPL datum**: there is an ABP row `P` with `P·ψ = 0`,
`P(θ) = tmRho`, `K^{perf}`-coefficients, `P none ≢ 0`, and all the coefficients `B̃_t` of the second
relation vanish. -/
theorem acmpl_second_relation (hc : c ∈ ambF F)
    (hT : ∀ s ∈ T, s.sum = w) (hne : ∀ s ∈ T, s ≠ [])
    (hpos : ∀ s ∈ T, ∀ n ∈ s, 1 ≤ n) (hTne : T.Nonempty)
    (hcfmem : ∀ s ∈ acmplS (F := F) c T, ∀ m, (cf s).coeff m ∈ ambA F 0)
    (hcfinv : ∀ s ∈ acmplS (F := F) c T, frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    {a : Polynomial (Ambient F)}
    (ha : frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((a : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((a : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hval : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w (acmplS (F := F) c T) cf
        ([] : List (ℕ × Polynomial (Ambient F)))) (ambTheta F) + a.eval (ambTheta F) = 0)
    (hLW : ∀ w' : ℕ, w' ≤ w → LinearIndependent (ambK F)
      (fun t : {t : ↥(tmI (acmplS (F := F) c T)) // tmWeight t.1 = w'} =>
        tmZ (F := F) (ambOmega F) t.1.1)) :
    ∃ P : Option ↥(tmI (acmplS (F := F) c T)) → Polynomial (Ambient F),
      (∑ j, coeHom (K := Ambient F) (P j)
          * tmPsiColA F (ambOmega F) w (acmplS (F := F) c T) cf
              (acmplS_nil_mem (F := F) hne hTne) a j = 0) ∧
      (∀ j, (P j).eval (ambTheta F) = tmRho F (acmplS (F := F) c T) j) ∧
      (∀ j m, (P j).coeff m ∈ ambKperf F) ∧
      P none ≠ 0 ∧
      (∀ t : ↥(tmI (acmplS (F := F) c T)),
        tmB F w (acmplS (F := F) c T) cf P (some t) = 0) := by
  classical
  set S := acmplS (F := F) c T with hS
  have h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S :=
    acmplS_nil_mem (F := F) hne hTne
  have hw : ∀ s ∈ S, tmWeight s = w := by
    intro s hs
    obtain ⟨s₀, hs₀, rfl⟩ := mem_acmplS.mp hs
    rw [tmWeight_map_C]
    exact hT s₀ hs₀
  have hsm : ∀ s ∈ S, ∀ y ∈ s,
      GIsSmall ambGamma ((ambOmega F) ^ y.1 * (y.2 : PowerSeries (Ambient F))) :=
    acmplS_small (F := F) hc hpos
  have hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire ambGamma ((y.2 : PowerSeries (Ambient F))) := by
    intro s hs y hy
    obtain ⟨s₀, hs₀, rfl⟩ := mem_acmplS.mp hs
    obtain ⟨n, -, hy'⟩ := List.mem_map.mp hy
    subst hy'
    simpa using GSuperEntire.C ambGamma c
  have hposS : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1 := by
    intro s hs y hy
    obtain ⟨s₀, hs₀, rfl⟩ := mem_acmplS.mp hs
    obtain ⟨n, hn, hy'⟩ := List.mem_map.mp hy
    subst hy'
    exact hpos s₀ hs₀ n hn
  have hQmem : ∀ s ∈ S, ∀ y ∈ s, ∀ k, (y.2).coeff k ∈ ambA F 0 := acmplS_Qmem (F := F) hc
  have hneS : ∀ s ∈ S, s ≠ [] := by
    intro s hs hnil
    obtain ⟨s₀, hs₀, rfl⟩ := mem_acmplS.mp hs
    exact hne s₀ hs₀ (List.map_eq_nil_iff.mp hnil)
  have hA : ∀ i j m, (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j).coeff m
      ∈ ambA F 0 := tmAOpt_coeff_mem_ambA0 (F := F) w hQmem hcfmem
  have hle : ∀ t : ↥(tmI S), tmWeight t.1 ≤ w :=
    fun t => tmWeight_le_of_mem_tmI (S := S) (w := w) t.2 (fun s hs => hw s hs)
  obtain ⟨P, hP, hPθ, hPmem, _⟩ :=
    tmABP_a_leading_kperf (F := F) (ambGamma_pos) (ambGamma_lt_one) gammaArchimedean_rat
      (two_le_ambCard F) (gIsSmall_ambOmega F) (gSuperEntire_ambOmega F) (coeff_zero_ambOmega F)
      (fun k hk => evalSeriesGen_ambOmega_frobenius_orbit F hk) (ambOmega_functional F)
      hw hcfinv hsm hSse hposS hneS h0 hA ha hval hle le_rfl
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
  have hfe : tmPsiColA F (ambOmega F) w S cf h0 a
      = (coeHom (K := Ambient F)).mapMatrix
          (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) *ᵥ
        frobTwistVec (q := Nat.card F) 1 (tmPsiColA F (ambOmega F) w S cf h0 a) := by
    have hfun := tmPsiColA_functional F (w := w) (cf := cf) (a := a) (ambGamma_lt_one)
      gammaArchimedean_rat (two_le_ambCard F) (gIsSmall_ambOmega F) (ambOmega_functional F)
      hw hcfinv hsm hneS h0 hA ha
    rw [tmPhi_twist_mat F _ hA] at hfun
    exact hfun
  have hB : ∀ t : ↥(tmI S), tmB F w S cf P (some t) = 0 :=
    step2_B_zero (F := F) (ambGamma_pos) (ambGamma_lt_one) gammaArchimedean_rat
      (two_le_ambCard F) (gIsSmall_ambOmega F) (gSuperEntire_ambOmega F)
      (fun k hk => evalSeriesGen_ambOmega_frobenius_orbit F hk) (ambOmega_functional F)
      hΩ0 hΩ1 hsm hSse hposS hQmem hw h0 hA hfe hLW hPmem hP
  have hP0 : P none ≠ 0 := by
    intro h0'
    have h1 : (P none).eval (ambTheta F) = 1 := by rw [hPθ none, tmRho_none]
    rw [h0', Polynomial.eval_zero] at h1
    exact one_ne_zero h1.symm
  exact ⟨P, hP, hPθ, hPmem, hP0, hB⟩

end Second

end ZagierHoffmanPositiveChar
