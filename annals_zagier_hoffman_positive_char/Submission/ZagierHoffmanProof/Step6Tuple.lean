import Submission.ZagierHoffmanProof.Step6H

/-!
# Dac's Theorem 6.2: the `𝒯'`-induction (`TupleIndP`) — the induction step

This module performs the induction step of Dac's Theorem 6.2 (ND21 Theorem 6.2) in the
tuple-indexed form `TupleIndP`: for a finite injective family of exponent tuples of common weight
`q < w ≤ 2q-2`, all of whose entries are not divisible by `q`, the MZV's `ζ_A 𝔰` are
`RatFunc F`-independent, assuming the induction hypothesis at all smaller weights and the
**two-term endgame** `TwoTermIndP` (Dac §6, proved separately in `Step7Endgame`).

The skeleton is that of `TheoremB.tuple_independent_step`, with the two modifications forced by the
Anderson–Thakur datum `Q_j = H_{s_j}`:

* the (LD) transport is `TpTrans.lseries_relationP` and the coefficient function carries the
  `Γ`-scaling `∏_{i'≠i} γ_{𝔰_{i'}}` (`mkCfH`);
* the (LW) transport is `TpTrans.linearIndependent_of_bridgeP`;
* Step 3 of the induction is `Step3HShared.dvd_pred_weight_H_shared` (no uniqueness of the extender),
  and the endgame is Dac's Step 3(b) (`Step3H.shape_of_dvd_H`) followed by `TwoTermIndP`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open Polynomial PowerSeries Finset
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

universe u

variable {F : Type u} [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. The two-term endgame (Dac §6, the `|T| = 2` case of the induction) -/

/-- **The two-term independence at weight `w`**: the only tuples of weight `w` that can occur in a
relation are `(w)` and `(w-(q-1), q-1)`, and the corresponding MZV's are `RatFunc F`-independent.
This is the analytic endgame of Dac's Theorem 6.2 (`Step7Endgame`).

⚠ Two design points, both forced by the use site:

* the non-vanishing hypotheses `A ≠ 0`, `B ≠ 0` are **essential**: without them the statement would
  be false (take `A = B = 0`).  They are available at every use site, because in Dac's Step 3 the
  relation (6.2) has `a₁, a₂ ∈ K^*`; in the tuple induction the pair `(A, B)` ranges over the
  *support* of the coefficient function, cf. `ha_ne`;
* the coefficients are stated as **polynomials** `A, B ∈ F[X]`, not arbitrary elements of
  `K = RatFunc F`.  This is exactly the shape of the cleared relation in the tuple induction (`a` is
  polynomial-valued there), and it is precisely the hypothesis of
  `TpTrans.lseries_relationP`. -/
def TwoTermIndP (F : Type u) [Field F] [Finite F] [DecidableEq (RatFunc F)] (w : ℕ) : Prop :=
  ∀ {r₁ r₂ : ℕ} (𝔰₁ : Fin r₁ → ℕ+) (𝔰₂ : Fin r₂ → ℕ+) (k : ℕ) (hk : 1 ≤ k)
    (hwk : w = k + (Nat.card F - 1))
    (h1 : tupleListHP F 𝔰₁ = [((w : ℕ), ambH F w)])
    (h2 : tupleListHP F 𝔰₂
      = [((k : ℕ), ambH F k), ((Nat.card F - 1 : ℕ), ambH F (Nat.card F - 1))])
    (A B : Polynomial F), A ≠ 0 → B ≠ 0 →
    (A : RatFunc F) • ζ_A F 𝔰₁ + (B : RatFunc F) • ζ_A F 𝔰₂ ≠ 0

/-! ## §2. Non-vanishing for tuples of length `1` and `2` -/

lemma zeta_ne_zero_of_length_one (𝔰 : Fin 1 → ℕ+) : ζ_A F 𝔰 ≠ 0 := by
  have heq : ζ_A F 𝔰 = ζ_A F (single (𝔰 ⟨0, by omega⟩)) :=
    congrArg (ζ_A F) (funext fun j => by
      refine PNat.eq ?_
      show (𝔰 j : ℕ) = (𝔰 ⟨0, by omega⟩ : ℕ)
      exact congrArg (fun i : Fin 1 => (𝔰 i : ℕ)) (Fin.ext (by have := j.2; omega)))
  rw [heq]
  exact zeta_single_ne_zero F (𝔰 ⟨0, by omega⟩)

lemma zeta_ne_zero_of_length_two (𝔰 : Fin 2 → ℕ+) : ζ_A F 𝔰 ≠ 0 := by
  have heq : ζ_A F 𝔰 = ζ_A F (pair (𝔰 ⟨0, by omega⟩) (𝔰 ⟨1, by omega⟩)) :=
    congrArg (ζ_A F) (funext fun j => by
      refine PNat.eq ?_
      show (𝔰 j : ℕ) = (pair (𝔰 ⟨0, by omega⟩) (𝔰 ⟨1, by omega⟩) j : ℕ)
      rw [pair]
      by_cases h : (j : ℕ) = 0
      · rw [if_pos h]
        exact congrArg (fun i : Fin 2 => (𝔰 i : ℕ)) (Fin.ext h)
      · rw [if_neg h]
        exact congrArg (fun i : Fin 2 => (𝔰 i : ℕ))
          (Fin.ext (by have h2 := j.2; simp only [Fin.val_mk]; omega)))
  rw [heq]
  exact zeta_pair_ne_zero F _ _

/-! ## §3. Recovering a tuple from the shape of its exponent list -/

lemma eq_singleton_of_map_fst_eq {L : List (ℕ × Polynomial (Ambient F))} {w : ℕ}
    (hE : ∀ x ∈ L, x.2 = ambH F x.1) (h : L.map Prod.fst = [w]) :
    L = [(w, ambH F w)] := by
  have hlen : L.length = 1 := by
    have h1 := congrArg List.length h
    simpa using h1
  obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
  have hx : x.1 = w := by simpa using h
  have hxE : x.2 = ambH F w := by rw [← hx]; exact hE x (by simp)
  rw [show x = (w, ambH F w) from Prod.ext hx hxE]

lemma eq_pair_of_map_fst_eq {L : List (ℕ × Polynomial (Ambient F))} {u v : ℕ}
    (hE : ∀ x ∈ L, x.2 = ambH F x.1) (h : L.map Prod.fst = [u, v]) :
    L = [(u, ambH F u), (v, ambH F v)] := by
  have hlen : L.length = 2 := by
    have h1 := congrArg List.length h
    simpa using h1
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hlen
  have hxy : [x.1, y.1] = [u, v] := by simpa using h
  obtain ⟨hx, hy⟩ := List.cons.inj hxy
  have hy' : y.1 = v := (List.cons.inj hy).1
  have hxE : x.2 = ambH F u := by rw [← hx]; exact hE x (by simp)
  have hyE : y.2 = ambH F v := by rw [← hy']; exact hE y (by simp)
  rw [show x = (u, ambH F u) from Prod.ext hx hxE,
    show y = (v, ambH F v) from Prod.ext hy' hyE]

/-! ## §4. The induction step -/

theorem tupleIndP_step (w : ℕ) (hw1 : 1 ≤ w) (hwq : Nat.card F < w)
    (hw2 : w ≤ 2 * Nat.card F - 2)
    (ih : ∀ (w' : ℕ), w' < w → 1 ≤ w' → ∀ (ι : Type u) [Fintype ι] [DecidableEq ι],
      TupleIndP (F := F) ι w')
    (hend : TwoTermIndP (F := F) w)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (𝔰 : ι → Σ r : ℕ, Fin r → ℕ+)
    (hnd : ∀ i j, ¬ Nat.card F ∣ ((𝔰 i).2 j : ℕ))
    (hwt : ∀ i, ∑ j : Fin (𝔰 i).1, ((𝔰 i).2 j : ℕ) = w)
    (hlinj : ∀ i j, tupleListHP F ((𝔰 i).2) = tupleListHP F ((𝔰 j).2) → i = j)
    (c : ι → RatFunc F) (hc : ∑ i, c i • ζ_A F ((𝔰 i).2) = 0) :
    ∀ i, c i = 0 := by
  classical
  intro i₀
  by_contra hi₀
  have hq3 : 3 ≤ Nat.card F := by omega
  -- the tuples are nonempty
  have hpos_i : ∀ i, 0 < (𝔰 i).1 := by
    intro i
    rcases Nat.eq_zero_or_pos (𝔰 i).1 with h | h
    · exfalso
      haveI : IsEmpty (Fin (𝔰 i).1) := ⟨fun j => by have := j.isLt; omega⟩
      have h2 : (∑ j : Fin (𝔰 i).1, ((𝔰 i).2 j : ℕ)) = 0 := by
        rw [Finset.univ_eq_empty]
        exact Finset.sum_empty
      have h3 := hwt i
      rw [h2] at h3
      omega
    · exact h
  have hsup : ∀ i j, ((𝔰 i).2 j : ℕ) ≤ 2 * Nat.card F - 2 := by
    intro i j
    have h1 : ((𝔰 i).2 j : ℕ) ≤ ∑ j' : Fin (𝔰 i).1, ((𝔰 i).2 j' : ℕ) :=
      Finset.single_le_sum (f := fun j' => ((𝔰 i).2 j' : ℕ))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h2 := hwt i
    omega
  -- §A. the support and the clearing of denominators
  set T : Finset ι := Finset.univ.filter (fun i => c i ≠ 0) with hT
  have hTm : ∀ i, i ∈ T ↔ c i ≠ 0 := fun i => by
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
  have hi₀T : i₀ ∈ T := (hTm i₀).mpr hi₀
  have hTne : T.Nonempty := ⟨i₀, hi₀T⟩
  have hout : ∀ i, i ∉ T → c i = 0 := fun i hi => by
    by_contra h; exact hi ((hTm i).mpr h)
  set Dp : Polynomial F := ∏ j ∈ T, RatFunc.denom (c j) with hDp
  set a : ι → Polynomial F :=
    fun i => RatFunc.num (c i) * ∏ j ∈ T.erase i, RatFunc.denom (c j) with ha
  have ha_eq : ∀ i ∈ T, (a i : RatFunc F) = c i * (Dp : RatFunc F) := by
    intro i hi
    simp only [ha, hDp]
    exact Commons.FieldTheory.RatFunc.num_mul_prod_erase_denom T c hi
  have ha_ne : ∀ i ∈ T, a i ≠ 0 := by
    intro i hi
    simp only [ha]
    exact Commons.FieldTheory.RatFunc.num_mul_prod_erase_denom_ne_zero T c hi ((hTm i).mp hi)
  have hane : ∀ i ∈ T, (a i : RatFunc F) ≠ 0 := fun i hi h =>
    ha_ne i hi (RatFunc.algebraMap_injective (K := F) (by simpa using h))
  have houta : ∀ i, i ∉ T → a i = 0 := by
    intro i hi
    simp only [ha]
    rw [hout i hi, RatFunc.num_zero, zero_mul]
  have hTrel : (∑ i ∈ T, (a i : RatFunc F) • ζ_A F ((𝔰 i).2)) = 0 := by
    have hcrel : (∑ i ∈ T, c i • ζ_A F ((𝔰 i).2)) = 0 := by
      refine (Finset.sum_subset (Finset.subset_univ T) ?_).trans hc
      intro i _ hi
      rw [hout i hi, zero_smul]
    have h1 : (∑ i ∈ T, (a i : RatFunc F) • ζ_A F ((𝔰 i).2))
        = (Dp : RatFunc F) • ∑ i ∈ T, c i • ζ_A F ((𝔰 i).2) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [ha_eq i hi, mul_smul, smul_comm]
    rw [h1, hcrel, smul_zero]
  -- §B. the Ambient coefficients
  set A : ι → Polynomial (Ambient F) := fun i => (a i).map (ambCoeff F) with hA
  have hA_ne : ∀ i ∈ T, A i ≠ 0 := by
    intro i hi
    simp only [hA]
    exact (Polynomial.map_ne_zero_iff (ambCoeff F).injective).mpr (ha_ne i hi)
  have hA_coeff : ∀ i m, (A i).coeff m ∈ ambA F 0 := by
    intro i m
    simp only [hA, Polynomial.coeff_map]
    exact mem_ambA_zero_of_mem_ambF (ambCoeff_mem_ambF F _)
  have hA_eval : ∀ i, (A i).eval (ambTheta F)
      = ambKHomAmb F (algebraMap (Polynomial F) (RatFunc F) (a i)) := by
    intro i
    simp only [hA]
    exact eval_map_ambCoeff (F := F) (a i)
  have hA_out : ∀ i, i ∉ T → A i = 0 := by
    intro i hi
    simp only [hA, houta i hi, Polynomial.map_zero]
  have hA_frob : ∀ i, frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((A i : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((A i : Polynomial (Ambient F)) : PowerSeries (Ambient F)) := by
    intro i
    ext n
    rw [frobTwist_coeff, pow_one, Polynomial.coeff_coe]
    simp only [hA, Polynomial.coeff_map]
    exact (mem_ambF_iff F _).mp (ambCoeff_mem_ambF F _)
  -- §C. the tuple set, the coefficient function and the datum
  set S : Finset (List (ℕ × Polynomial (Ambient F))) :=
    T.image (fun i => tupleListHP F ((𝔰 i).2)) with hS
  have hS_inj : Set.InjOn (fun i => tupleListHP F ((𝔰 i).2)) (T : Set ι) :=
    fun i _ j _ h => hlinj i j h
  have hS_entry : ∀ s ∈ S, ∀ x ∈ s, x.2 = ambH F x.1 := by
    intro s hs x hx
    rw [hS, Finset.mem_image] at hs
    obtain ⟨i, -, rfl⟩ := hs
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hx
    rw [tupleListHP_get]
  have hS_pos : ∀ s ∈ S, ∀ x ∈ s, 1 ≤ x.1 := by
    intro s hs x hx
    rw [hS, Finset.mem_image] at hs
    obtain ⟨i, -, rfl⟩ := hs
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hx
    rw [tupleListHP_get]
    exact ((𝔰 i).2 _).pos
  have hS_nd : ∀ s ∈ S, ∀ x ∈ s, ¬ Nat.card F ∣ x.1 := by
    intro s hs x hx
    rw [hS, Finset.mem_image] at hs
    obtain ⟨i, -, rfl⟩ := hs
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hx
    rw [tupleListHP_get]
    exact hnd i _
  have hS_weight : ∀ s ∈ S, tmWeight (K := Ambient F) s = w := by
    intro s hs
    rw [hS, Finset.mem_image] at hs
    obtain ⟨i, -, rfl⟩ := hs
    rw [tmWeight, tupleListHP, List.map_ofFn, List.sum_ofFn]
    exact hwt i
  have hS_le : ∀ s ∈ S, ∀ x ∈ s, x.1 ≤ 2 * Nat.card F - 2 := by
    intro s hs x hx
    have h1 : x.1 ≤ tmWeight (K := Ambient F) s := by
      have h2 := List.le_sum_of_mem (List.mem_map_of_mem (f := Prod.fst) hx)
      simpa [tmWeight] using h2
    have h3 := hS_weight s hs
    omega
  have hS_ne : ∀ s ∈ S, s ≠ [] := by
    intro s hs hnil
    have h1 := hS_weight s hs
    rw [hnil, tmWeight_nil] at h1
    omega
  have hcfmem : ∀ s ∈ S, ∀ m, (mkCfH (F := F) T 𝔰 A s).coeff m ∈ ambA F 0 :=
    fun s hs m => mkCfH_coeff_mem (F := F) (hA := fun i m => hA_coeff i m) hs m
  have hcf_frob : ∀ s ∈ S, frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((mkCfH (F := F) T 𝔰 A s : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((mkCfH (F := F) T 𝔰 A s : Polynomial (Ambient F)) : PowerSeries (Ambient F)) :=
    fun s hs => mkCfH_frob (F := F) (hA := fun i => hA_frob i) hs
  have hQmem : ∀ s ∈ S, ∀ y ∈ s, ∀ m, (y.2).coeff m ∈ ambA F 0 := by
    intro s hs y hy m
    rw [hS_entry s hs y hy]
    exact ambH_coeff_mem F y.1 m
  have h0mem : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S := by
    refine mem_tmI.mpr ⟨tupleListHP F ((𝔰 i₀).2), ?_, 0, ?_, rfl⟩
    · rw [hS]; exact Finset.mem_image.mpr ⟨i₀, hi₀T, rfl⟩
    · rw [tupleListHP_length]; exact hpos_i i₀
  have hsm : ∀ s ∈ S, ∀ y ∈ s,
      GIsSmall ambGamma ((ambOmega F) ^ y.1 * (y.2 : PowerSeries (Ambient F))) := by
    intro s hs y hy
    rw [hS_entry s hs y hy]
    exact gIsSmall_ambOmega_pow_mul_ambH F (hS_pos s hs y hy)
  have hSse : ∀ s ∈ S, ∀ y ∈ s,
      GSuperEntire ambGamma (y.2 : PowerSeries (Ambient F)) := by
    intro s hs y hy
    rw [hS_entry s hs y hy]
    exact gSuperEntire_ambH F y.1
  let hDD : MZVDH F w := ⟨S, hS_entry, hS_pos, hS_le, hS_nd, hS_weight⟩
  have hAcoeff : ∀ i j m,
      (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S (mkCfH (F := F) T 𝔰 A) i j).coeff m
        ∈ ambA F 0 :=
    tmAOpt_coeff_mem_ambA0 (F := F) w hQmem hcfmem
  -- §D. the (LD) input
  have hrel_all : (∑ i, (a i : RatFunc F) • ζ_A F ((𝔰 i).2)) = 0 := by
    refine (Finset.sum_subset (Finset.subset_univ T) ?_).symm.trans hTrel
    intro i _ hiT
    rw [houta i hiT]
    simp
  have hvan := lseries_relationP (F := F) 𝔰 hpos_i hsup w hwt a hrel_all
  have hval : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w S (mkCfH (F := F) T 𝔰 A)
        ([] : List (ℕ × Polynomial (Ambient F)))) (ambTheta F)
      + (0 : Polynomial (Ambient F)).eval (ambTheta F) = 0 := by
    rw [Polynomial.eval_zero, add_zero, tmF_nil]
    have hse : ∀ s ∈ S, GSuperEntire ambGamma (tmL (Nat.card F) (ambOmega F) s) :=
      fun s hs => gSuperEntire_tmL_of_mem (F := F) (γ := ambGamma) (ω := ambOmega F) (S := S)
        (u := s) ambGamma_lt_one gammaArchimedean_rat (two_le_ambCard F) (gIsSmall_ambOmega F)
        (gSuperEntire_ambOmega F) hsm hSse (fun y hy => ⟨s, hs, hy⟩)
    have hstep1 : evalSeriesGen (∑ s ∈ S, (mkCfH (F := F) T 𝔰 A s : PowerSeries (Ambient F))
          * tmL (Nat.card F) (ambOmega F) s) (ambTheta F)
        = ∑ s ∈ S, (mkCfH (F := F) T 𝔰 A s).eval (ambTheta F)
            * evalSeriesGen (tmL (Nat.card F) (ambOmega F) s) (ambTheta F) := by
      rw [evalSeriesGen_finset_sum ambGamma_lt_one gammaArchimedean_rat S
        (fun s => (mkCfH (F := F) T 𝔰 A s : PowerSeries (Ambient F))
          * tmL (Nat.card F) (ambOmega F) s)
        (fun s hs => GSuperEntire.mul ambGamma_le_one
          (GSuperEntire.polynomial ambGamma_pos ambGamma_le_one _) (hse s hs)) (ambTheta F)]
      refine Finset.sum_congr rfl (fun s hs => ?_)
      rw [evalSeriesGen_mul ambGamma_lt_one gammaArchimedean_rat
        (GSuperEntire.polynomial ambGamma_pos ambGamma_le_one _) (hse s hs) (ambTheta F),
        evalSeriesGen_polynomial]
    rw [hstep1, ← hvan, hS, Finset.sum_image hS_inj]
    rw [show (∑ i ∈ T, (mkCfH (F := F) T 𝔰 A (tupleListHP F ((𝔰 i).2))).eval (ambTheta F)
          * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListHP F ((𝔰 i).2))) (ambTheta F))
        = ∑ i ∈ T, (((A i) * ∏ i' ∈ Finset.univ.erase i, gammaPolyTup F ((𝔰 i').2)).eval
            (ambTheta F))
          * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListHP F ((𝔰 i).2))) (ambTheta F)
        from Finset.sum_congr rfl (fun i hi => by rw [mkCfH_apply hlinj hi])]
    exact Finset.sum_subset (Finset.subset_univ T) (fun i _ hiT => by
      simp only [hA_out i hiT, zero_mul, Polynomial.eval_zero])
  have hLW : ∀ w' : ℕ, w' ≤ w → LinearIndependent (ambK F)
      (fun t : {t : ↥(tmI S) // tmWeight (K := Ambient F) t.1 = w'} =>
        tmZ (F := F) (ambOmega F) t.1.1) := by
    intro w' hw'
    rcases eq_or_ne w' 0 with hw'0 | hw'0
    · subst hw'0
      have hnil : ∀ t : ↥(tmI S), tmWeight (K := Ambient F) t.1 = 0 → t.1 = [] := by
        intro t ht
        obtain ⟨s, hs, k, hk, htk⟩ := mem_tmI.mp t.2
        rw [← htk] at ht
        have h1 : (s.take k).length ≤ tmWeight (K := Ambient F) (s.take k) := by
          rw [tmWeight]
          conv_lhs => rw [← List.length_map (f := Prod.fst)]
          refine List.length_le_sum_of_one_le _ (fun x hx => ?_)
          rw [List.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          exact hS_pos s hs y (List.mem_of_mem_take hy)
        have h2 : (s.take k).length = k := by
          rw [List.length_take, Nat.min_eq_left (le_of_lt hk)]
        rw [h2] at h1
        have h3 : k = 0 := by omega
        rw [← htk, h3, List.take_zero]
      have hsub : Subsingleton {t : ↥(tmI S) // tmWeight (K := Ambient F) t.1 = 0} :=
        ⟨fun a b => Subtype.ext (Subtype.ext ((hnil a.1 a.2).trans (hnil b.1 b.2).symm))⟩
      rw [Fintype.linearIndependent_iffₛ]
      intro f g hfg i
      have huniv : (Finset.univ : Finset {t : ↥(tmI S) // tmWeight (K := Ambient F) t.1 = 0})
          = {i} :=
        Finset.eq_singleton_iff_unique_mem.mpr
          ⟨Finset.mem_univ i, fun b _ => Subsingleton.elim b i⟩
      have e1 : (∑ x : {t : ↥(tmI S) // tmWeight (K := Ambient F) t.1 = 0},
              f x • tmZ (F := F) (ambOmega F) x.1.1)
            = f i • tmZ (F := F) (ambOmega F) i.1.1 := by
        rw [huniv, Finset.sum_singleton]
      have e2 : (∑ x : {t : ↥(tmI S) // tmWeight (K := Ambient F) t.1 = 0},
              g x • tmZ (F := F) (ambOmega F) x.1.1)
            = g i • tmZ (F := F) (ambOmega F) i.1.1 := by
        rw [huniv, Finset.sum_singleton]
      have h1 : f i • tmZ (F := F) (ambOmega F) i.1.1
          = g i • tmZ (F := F) (ambOmega F) i.1.1 := by
        rw [← e1, ← e2]; exact hfg
      have hi0 : i.1.1 = [] := hnil i.1 i.2
      rw [hi0, tmZ, tmL_nil, evalSeriesGen_one] at h1
      exact Subtype.ext (by simpa [Algebra.smul_def] using h1)
    · rcases eq_or_lt_of_le hw' with hww | hw'lt
      · subst w'
        have hempty : ∀ t : {t : ↥(tmI S) // tmWeight (K := Ambient F) t.1 = w}, False := by
          intro t
          obtain ⟨s, hs, k, hk, htk⟩ := mem_tmI.mp t.1.2
          have h1 : tmWeight (K := Ambient F) s = w := hS_weight s hs
          have h2 : tmWeight (K := Ambient F) t.1 = w := t.2
          have h3 : tmWeight (K := Ambient F) s = tmWeight (K := Ambient F) (s.take k)
              + tmWeight (K := Ambient F) (s.drop k) :=
            tmWeight_take_add_drop (K := Ambient F) s k
          have h4 : 1 ≤ tmWeight (K := Ambient F) (s.drop k) := by
            rw [tmWeight]
            refine le_trans ?_ (List.length_le_sum_of_one_le _ (fun x hx => ?_))
            · rw [List.length_map]
              exact List.length_pos_iff.mpr (drop_ne_nil_of_lt_length hk)
            · rw [List.mem_map] at hx
              obtain ⟨y, hy, rfl⟩ := hx
              exact hS_pos s hs y (List.mem_of_mem_drop hy)
          rw [← htk] at h2
          omega
        rw [Fintype.linearIndependent_iffₛ]
        exact fun f g _ t => (hempty t).elim
      · have hw'1 : 1 ≤ w' := by omega
        have hw'2 : w' ≤ 2 * Nat.card F - 2 := by omega
        let 𝔰' : {t : ↥(tmI S) // tmWeight (K := Ambient F) t.1 = w'} →
            Σ r : ℕ, Fin r → ℕ+ := fun t => tmTup (S := S) hS_pos t.1
        have hpos' : ∀ t, 0 < (𝔰' t).1 := by
          intro t
          show 0 < (t.1.1).length
          rw [List.length_pos_iff]
          intro hnil
          have h2 : tmWeight (K := Ambient F) t.1 = w' := t.2
          rw [show (t.1 : List (ℕ × Polynomial (Ambient F))) = [] from hnil, tmWeight_nil] at h2
          omega
        have hsup' : ∀ t j, ((𝔰' t).2 j : ℕ) ≤ 2 * Nat.card F - 2 := by
          intro t j
          show (t.1.1.get j).1 ≤ 2 * Nat.card F - 2
          obtain ⟨s, hs, hx⟩ := mem_tmI_entry F t.1.2 (List.get_mem t.1.1 j)
          exact hS_le s hs _ hx
        have hwt' : ∀ t, ∑ j : Fin (𝔰' t).1, ((𝔰' t).2 j : ℕ) = w' := by
          intro t
          rw [tmTup_weight (S := S) hS_pos t.1]
          exact t.2
        have hLI := (ih w' hw'lt hw'1 _ :
          TupleIndP (F := F) {t : ↥(tmI S) // tmWeight (K := Ambient F) t.1 = w'} w')
          (fun t => tmTup (S := S) hS_pos t.1)
          (fun t j => tmTup_nd_H (S := S) hS_nd hS_pos t.1 j)
          (fun t => by rw [tmTup_weight (S := S) hS_pos t.1]; exact t.2)
          (fun t t' h => Subtype.ext (tmTup_inj_H (S := S) hS_entry hS_pos h))
        have hLI2 := linearIndependent_of_bridgeP (F := F) 𝔰' hpos' hsup' w' hwt' hLI
        have hfun : (fun t : {t : ↥(tmI S) // tmWeight (K := Ambient F) t.1 = w'} =>
              evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListHP F ((𝔰' t).2)))
                (ambTheta F))
            = (fun t : {t : ↥(tmI S) // tmWeight (K := Ambient F) t.1 = w'} =>
              tmZ (F := F) (ambOmega F) t.1.1) := by
          funext t
          rw [tmTup_entries_H (F := F) (hentry := hS_entry) (hpos := hS_pos)]
          rfl
        rwa [hfun] at hLI2
  -- §F. Dac's §3.3
  have hfK : ∀ t' : ↥(tmI S),
      evalSeriesGen (tmF (Nat.card F) (ambOmega F) w S (mkCfH (F := F) T 𝔰 A) t'.1)
        (ambTheta F) ∈ ambK F :=
    linear_independence (F := F) ambGamma_pos ambGamma_lt_one gammaArchimedean_rat
      (two_le_ambCard F) (gIsSmall_ambOmega F) (gSuperEntire_ambOmega F)
      (coeff_zero_ambOmega F) (fun k hk => evalSeriesGen_ambOmega_frobenius_orbit F hk)
      (ambOmega_functional F) hS_weight hcf_frob hsm hSse hS_pos hQmem hS_ne h0mem hAcoeff
      (by rw [Polynomial.coe_zero]; ext n; simp [frobTwist_coeff]) hval hLW
  -- §G.1 Step 3(a): the divisibility for every prefix
  have hGmem_shared : ∀ (s₀ : List (ℕ × Polynomial (Ambient F))) (hs₀ : s₀ ∈ S) (k : ℕ),
      ∀ s' (hs' : s' ∈ S), s'.take k = s₀.take k →
      (∏ j : Fin (suffixList F (s'.drop k)).length,
          ambGammaF F ((suffixExp F (s'.drop k) (hDD.drop_pos hs' k) j : ℕ)))
        * (mkCfH (F := F) T 𝔰 A s').eval (ambTheta F) ∈ ambK F := by
    intro s₀ hs₀ k s' hs' _
    have hΓ : (∏ j : Fin (suffixList F (s'.drop k)).length,
        ambGammaF F ((suffixExp F (s'.drop k) (hDD.drop_pos hs' k) j : ℕ))) ∈ ambK F :=
      (ambK F).prod_mem (fun j _ => ambGammaF_mem_ambK F _)
    have hcf : (mkCfH (F := F) T 𝔰 A s').eval (ambTheta F) ∈ ambK F := by
      rw [hS, Finset.mem_image] at hs'
      obtain ⟨i, hi, rfl⟩ := hs'
      rw [mkCfH_apply hlinj hi, Polynomial.eval_mul, Polynomial.eval_prod]
      exact (ambK F).mul_mem (eval_mem_ambK (F := F) (A i) (fun m => hA_coeff i m))
        ((ambK F).prod_mem (fun i' _ => by
          rw [eval_gammaPolyTup]
          exact (ambK F).prod_mem (fun j _ => ambGammaF_mem_ambK F _)))
    exact (ambK F).mul_mem hΓ hcf
  have hf0' : ∀ (s : List (ℕ × Polynomial (Ambient F))) (hs : s ∈ S) (k : ℕ),
      1 ≤ k → k < s.length →
      evalSeriesGen (tmF (Nat.card F) (ambOmega F) w S (mkCfH (F := F) T 𝔰 A) (s.take k))
        (ambTheta F) ≠ 0 := by
    intro s hs k hk1 hklt hzero
    -- the common weight of the dropped tails
    set m : ℕ := w - tmWeight (K := Ambient F) (s.take k) with hm
    have hms : ∀ s' ∈ S, s'.take k = s.take k → tmWeight (K := Ambient F) (s'.drop k) = m := by
      intro s' hs' hst
      have h1 : tmWeight (K := Ambient F) s' = w := hS_weight s' hs'
      have h2 := tmWeight_take_add_drop (K := Ambient F) s' k
      rw [h1, hst] at h2
      simp only [hm]
      omega
    have hmlt : m < w := by
      have h1 : 1 ≤ tmWeight (K := Ambient F) (s.take k) := by
        rw [tmWeight]
        refine le_trans ?_ (List.length_le_sum_of_one_le _ (fun x hx => ?_))
        · rw [List.length_map, List.length_take, Nat.min_eq_left (le_of_lt hklt)]
          omega
        · rw [List.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          exact hS_pos s hs y (List.mem_of_mem_take hy)
      have h2 := hS_weight s hs
      have h3 := tmWeight_take_add_drop (K := Ambient F) s k
      simp only [hm]
      omega
    have hm1 : 1 ≤ m := by
      have h3 := tmWeight_take_add_drop (K := Ambient F) s k
      have h2 := hS_weight s hs
      have h4 : 1 ≤ tmWeight (K := Ambient F) (s.drop k) := by
        rw [tmWeight]
        refine le_trans ?_ (List.length_le_sum_of_one_le _ (fun x hx => ?_))
        · rw [List.length_map]
          exact List.length_pos_iff.mpr (drop_ne_nil_of_lt_length hklt)
        · rw [List.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          exact hS_pos s hs y (List.mem_of_mem_drop hy)
      simp only [hm]
      omega
    -- the extenders of the prefix `s.take k`
    set J : Finset (List (ℕ × Polynomial (Ambient F))) :=
      S.filter (fun s' => s'.take k = s.take k) with hJ
    have hJs : s ∈ J := Finset.mem_filter.mpr ⟨hs, rfl⟩
    have hlen : (s.take k).length = k := by
      rw [List.length_take, Nat.min_eq_left (le_of_lt hklt)]
    -- the evaluation of `f` at the shared prefix
    have hse : ∀ s' ∈ S, GSuperEntire ambGamma (tmL (Nat.card F) (ambOmega F) (s'.drop k)) :=
      fun s' hs' => gSuperEntire_tmL_of_mem (F := F) (γ := ambGamma) (ω := ambOmega F) (S := S)
        (u := s'.drop k) ambGamma_lt_one gammaArchimedean_rat (two_le_ambCard F)
        (gIsSmall_ambOmega F) (gSuperEntire_ambOmega F) hsm hSse
        (fun y hy => ⟨s', hs', List.mem_of_mem_drop hy⟩)
    have hse' : ∀ s' ∈ S, GSuperEntire ambGamma
        (tmL (Nat.card F) (ambOmega F) (s'.drop (s.take k).length)) := by
      intro s' hs'
      rw [hlen]
      exact hse s' hs'
    have hII := evalSeriesGen_tmF_shared (F := F) (w := w) (S := S) (cf := mkCfH (F := F) T 𝔰 A)
      (t := s.take k) hse'
    rw [hlen] at hII
    have hII0 : (∑ s' ∈ S, if s'.take k = s.take k then (mkCfH (F := F) T 𝔰 A s').eval (ambTheta F)
        * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (s'.drop k)) (ambTheta F) else 0) = 0 := by
      rw [hzero] at hII
      exact hII.symm
    have hsum0 : (∑ s' ∈ J, (mkCfH (F := F) T 𝔰 A s').eval (ambTheta F)
        * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (s'.drop k)) (ambTheta F)) = 0 := by
      rw [hJ, Finset.sum_filter]
      exact hII0
    -- the bridge, and the common `π̃`-factor
    have hbridge : (ambPiTilde F) ^ m
        * (∑ s' ∈ J, (mkCfH (F := F) T 𝔰 A s').eval (ambTheta F)
            * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (s'.drop k)) (ambTheta F))
        = ∑ s' ∈ J, sharedG hDD k (mkCfH (F := F) T 𝔰 A) s' * sharedS hDD k s' := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s' hs' => ?_)
      obtain ⟨hs'S, hst⟩ := Finset.mem_filter.mp hs'
      have hne' : s'.drop k ≠ [] := by
        intro hnil
        have h1 := hms s' hs'S hst
        rw [hnil, tmWeight_nil] at h1
        omega
      have hb := bridgeP_mul F (suffixList F (s'.drop k)) (suffixList_ne_nil F hne')
        (fun j => suffixList_mem_ambH (F := F) (hDD.drop_entry hs'S k) _ (List.get_mem _ j))
        (fun j => suffixList_mem_pos F (hDD.drop_pos hs'S k) _ (List.get_mem _ j))
        (fun j => suffixList_mem_le_two (F := F) (hDD.drop_le hs'S k) _ (List.get_mem _ j))
        (suffixExp F (s'.drop k) (hDD.drop_pos hs'S k)) (fun j => rfl)
        (fun j => by
          simp only [suffixExp_apply]
          exact suffixList_mem_le_two (F := F) (hDD.drop_le hs'S k) _
            (List.get_mem (suffixList F (s'.drop k)) (Fin.rev j)))
        (mkCfH (F := F) T 𝔰 A s')
      have hsum : (∑ j : Fin (suffixList F (s'.drop k)).length,
          (suffixExp F (s'.drop k) (hDD.drop_pos hs'S k) j : ℕ)) = m := by
        have h1 := suffixList_weight F (s'.drop k)
        simp only [suffixExp_apply]
        rw [h1, hms s' hs'S hst]
      rw [hsum] at hb
      rw [sharedG, dif_pos hs'S, sharedS, dif_pos hs'S]
      refine hb.trans ?_
      ring
    -- transport to `RatFunc F`
    have hGmem : ∀ s' ∈ J, sharedG hDD k (mkCfH (F := F) T 𝔰 A) s' ∈ ambK F := by
      intro s' hs'
      obtain ⟨hs'S, hst⟩ := Finset.mem_filter.mp hs'
      rw [sharedG, dif_pos hs'S]
      exact hGmem_shared s hs k s' hs'S hst
    have hSrange : ∀ s' ∈ J, sharedS hDD k s' ∈ Set.range (ambInfHom F) := by
      intro s' hs'
      obtain ⟨hs'S, -⟩ := Finset.mem_filter.mp hs'
      rw [sharedS, dif_pos hs'S]
      exact ⟨_, rfl⟩
    -- the induction datum: the dropped tails
    set 𝔰₂ : ↥J → Σ r : ℕ, Fin r → ℕ+ := fun x =>
      ⟨(suffixList F (x.1.drop k)).length,
        suffixExp F (x.1.drop k) (hDD.drop_pos (Finset.mem_filter.mp x.2).1 k)⟩ with h𝔰₂
    have hnd₂ : ∀ x j, ¬ Nat.card F ∣ ((𝔰₂ x).2 j : ℕ) := by
      intro x j
      show ¬ Nat.card F ∣ (suffixExp F (x.1.drop k)
        (hDD.drop_pos (Finset.mem_filter.mp x.2).1 k) j : ℕ)
      rw [suffixExp_apply]
      obtain ⟨y, hy, hyx⟩ := (mem_suffixList F).mp (List.get_mem (suffixList F (x.1.drop k)) (Fin.rev j))
      rw [← hyx]
      exact hS_nd x.1 (Finset.mem_filter.mp x.2).1 y (List.mem_of_mem_drop hy)
    have hwt₂ : ∀ x, ∑ j : Fin (𝔰₂ x).1, ((𝔰₂ x).2 j : ℕ) = m := by
      intro x
      show (∑ j : Fin (suffixList F (x.1.drop k)).length,
        (suffixExp F (x.1.drop k) (hDD.drop_pos (Finset.mem_filter.mp x.2).1 k) j : ℕ)) = m
      have h1 := suffixList_weight F (x.1.drop k)
      simp only [suffixExp_apply]
      rw [h1]
      exact hms x.1 (Finset.mem_filter.mp x.2).1 (Finset.mem_filter.mp x.2).2
    have hlinj₂ : ∀ x y, tupleListHP F ((𝔰₂ x).2) = tupleListHP F ((𝔰₂ y).2) → x = y := by
      intro x y hxy
      refine Subtype.ext ?_
      have hx := tupleListHP_suffixExp (F := F) (L := x.1.drop k)
        (hDD.drop_pos (Finset.mem_filter.mp x.2).1 k) (hDD.drop_entry (Finset.mem_filter.mp x.2).1 k)
      have hy := tupleListHP_suffixExp (F := F) (L := y.1.drop k)
        (hDD.drop_pos (Finset.mem_filter.mp y.2).1 k) (hDD.drop_entry (Finset.mem_filter.mp y.2).1 k)
      have h1 : x.1.drop k = y.1.drop k := by rw [← hx, ← hy]; exact hxy
      have h2 : x.1.take k = y.1.take k := by
        rw [(Finset.mem_filter.mp x.2).2, (Finset.mem_filter.mp y.2).2]
      calc x.1 = x.1.take k ++ x.1.drop k := (List.take_append_drop k x.1).symm
        _ = y.1.take k ++ y.1.drop k := by rw [h2, h1]
        _ = y.1 := List.take_append_drop k y.1
    have hLI := ih m hmlt hm1 ↥J 𝔰₂ hnd₂ hwt₂ hlinj₂
    rw [Fintype.linearIndependent_iffₛ] at hLI
    -- the coefficients
    set cf₂ : ↥J → RatFunc F := fun x => (ambKEquiv F).symm
      ⟨sharedG hDD k (mkCfH (F := F) T 𝔰 A) x.1, hGmem x.1 x.2⟩ with hcf₂
    have hcf₂_eq : ∀ x : ↥J, ambInfHom F (cf₂ x • ζ_A F ((𝔰₂ x).2))
        = sharedG hDD k (mkCfH (F := F) T 𝔰 A) x.1 * sharedS hDD k x.1 := by
      intro x
      obtain ⟨hxS, -⟩ := Finset.mem_filter.mp x.2
      rw [sharedS, dif_pos hxS]
      rw [Algebra.smul_def, map_mul]
      congr 1
      have hcoe : (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) (cf₂ x)
          = ((cf₂ x : RatFunc F) : RatFunc.CompletionAtInfty F) := rfl
      rw [hcoe, ambInfHom_coe, ambKHomAmb_apply]
      dsimp only [cf₂]
      rw [RingEquiv.apply_symm_apply]
    have hrel₂ : (∑ x : ↥J, cf₂ x • ζ_A F ((𝔰₂ x).2)) = 0 := by
      apply ambInfHom_injective
      rw [map_zero, map_sum]
      have h1 : (∑ x : ↥J, ambInfHom F (cf₂ x • ζ_A F ((𝔰₂ x).2)))
          = ∑ s' ∈ J, sharedG hDD k (mkCfH (F := F) T 𝔰 A) s' * sharedS hDD k s' := by
        rw [Finset.univ_eq_attach, ← Finset.sum_attach J (fun s' =>
          sharedG hDD k (mkCfH (F := F) T 𝔰 A) s' * sharedS hDD k s')]
        exact Finset.sum_congr rfl (fun x _ => hcf₂_eq x)
      rw [h1, ← hbridge, hsum0, mul_zero]
    have hzeroG : sharedG hDD k (mkCfH (F := F) T 𝔰 A) s = 0 := by
      have h := hLI cf₂ 0 (by rw [hrel₂]; simp) ⟨s, hJs⟩
      have h2 := congrArg (fun z : RatFunc F => (ambKEquiv F) z) h
      have h3 : (⟨sharedG hDD k (mkCfH (F := F) T 𝔰 A) s, hGmem s hJs⟩ : ↥(ambK F)) = 0 := by
        simpa only [cf₂, RingEquiv.apply_symm_apply, Pi.zero_apply, map_zero] using h2
      simpa using congrArg Subtype.val h3
    -- but the coefficient is a product of nonzero factors
    have hshared_ne : sharedG hDD k (mkCfH (F := F) T 𝔰 A) s ≠ 0 := by
      have hsimg : s ∈ T.image (fun i => tupleListHP F ((𝔰 i).2)) := by rw [← hS]; exact hs
      obtain ⟨i, hi, hsi⟩ := Finset.mem_image.mp hsimg
      subst hsi
      rw [sharedG, dif_pos (show tupleListHP F ((𝔰 i).2) ∈ hDD.S from hs)]
      have hΓne : (∏ j : Fin (suffixList F ((tupleListHP F ((𝔰 i).2)).drop k)).length,
          ambGammaF F ((suffixExp F ((tupleListHP F ((𝔰 i).2)).drop k)
            (hDD.drop_pos hs k) j : ℕ))) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun j _ => ambGammaF_ne_zero F _)
      have hcfne : (mkCfH (F := F) T 𝔰 A (tupleListHP F ((𝔰 i).2))).eval (ambTheta F) ≠ 0 := by
        rw [mkCfH_apply hlinj hi, Polynomial.eval_mul, Polynomial.eval_prod]
        refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr (fun i' _ => ?_))
        · rw [hA_eval]
          intro h0
          exact ha_ne i hi (RatFunc.algebraMap_injective (K := F)
            (ambKHomAmb_injective (by simpa using h0)))
        · rw [eval_gammaPolyTup]
          exact Finset.prod_ne_zero_iff.mpr (fun j _ => ambGammaF_ne_zero F _)
      exact mul_ne_zero hΓne hcfne
    exact hshared_ne hzeroG
  -- §G.1 Step 3(a): the divisibility for every prefix
  have hdiv : ∀ s ∈ S, ∀ k : ℕ, 1 ≤ k → k ≤ s.length →
      (Nat.card F - 1) ∣ tmWeight (K := Ambient F) (s.drop k) := by
    intro s hs k hk1 hk2
    rcases lt_or_eq_of_le hk2 with hklt | hkeq
    · have hf0 := hf0' s hs k hk1 hklt
      have hfK' : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w S (mkCfH (F := F) T 𝔰 A)
          (s.take k)) (ambTheta F) ∈ ambK F :=
        hfK ⟨s.take k, mem_tmI.mpr ⟨s, hs, k, hklt, rfl⟩⟩
      have hres := dvd_pred_weight_H_shared (F := F) hDD hs hklt hfK' hf0 (hGmem_shared s hs k)
      rwa [show w - tmWeight (K := Ambient F) (s.take k) = tmWeight (K := Ambient F) (s.drop k)
        from by
          have h := hDD.drop_weight hs k
          omega] at hres
    · subst hkeq
      rw [List.drop_length, tmWeight_nil]
      exact dvd_zero _
  have hshape : ∀ s ∈ S,
      s.map Prod.fst = [w] ∨ s.map Prod.fst = [w - (Nat.card F - 1), Nat.card F - 1] :=
    shape_of_dvd_H (F := F) hq3 hw1 hw2 hDD hdiv
  -- §G.2 the endgame
  rcases lt_or_ge T.card 2 with hlt2 | hge2
  · -- the support has a single element
    have hT1 : T.card = 1 := by have := Finset.card_pos.mpr hTne; omega
    obtain ⟨i₁, hT1eq⟩ := Finset.card_eq_one.mp hT1
    have hi₁T : i₁ ∈ T := by rw [hT1eq]; exact Finset.mem_singleton_self i₁
    have hrel1 : (a i₁ : RatFunc F) • ζ_A F ((𝔰 i₁).2) = 0 := by
      have h := hTrel
      rw [hT1eq, Finset.sum_singleton] at h
      exact h
    have ha1 : a i₁ ≠ 0 := ha_ne i₁ hi₁T
    have hz1 : ζ_A F ((𝔰 i₁).2) = 0 := by
      apply ambInfHom_injective
      rw [map_zero]
      have h3 := congrArg (ambInfHom F) hrel1
      rw [map_zero, Algebra.smul_def, map_mul] at h3
      have hcoe : ambInfHom F (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (a i₁))
          = ambKHomAmb F (a i₁) := by
        rw [show (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (a i₁))
            = ((a i₁ : RatFunc F) : RatFunc.CompletionAtInfty F) from rfl, ambInfHom_coe]
      rw [hcoe] at h3
      rcases mul_eq_zero.mp h3 with h | h
      · have h4 : (a i₁ : RatFunc F) = 0 :=
          ambKHomAmb_injective (show ambKHomAmb F (a i₁) = ambKHomAmb F 0 by simpa using h)
        exact absurd (RatFunc.algebraMap_injective (K := F) (by rw [map_zero]; exact h4)) ha1
      · exact h
    have hs_mem : tupleListHP F ((𝔰 i₁).2) ∈ S :=
      Finset.mem_image.mpr ⟨i₁, hi₁T, rfl⟩
    rcases hshape _ hs_mem with hsh | hsh
    · have hr : (𝔰 i₁).1 = 1 := by
        have h1 : (tupleListHP F ((𝔰 i₁).2)).length = 1 := by
          have hc := congrArg List.length hsh
          simpa using hc
        rwa [tupleListHP_length] at h1
      have heq : ζ_A F ((𝔰 i₁).2)
          = ζ_A F (fun _ : Fin 1 => (𝔰 i₁).2 ⟨0, by omega⟩) := by
        refine ζ_A_eq_of_reindex F hr ((𝔰 i₁).2) _ (fun i => ?_)
        refine PNat.eq ?_
        refine congrArg (fun j : Fin ((𝔰 i₁).1) => ((𝔰 i₁).2 j : ℕ)) ?_
        apply Fin.ext
        have h2 := i.2
        simp only [Fin.val_mk]
        omega
      exact (fun h0 => zeta_ne_zero_of_length_one (F := F) _
        (heq.symm.trans h0)) hz1
    · have hr : (𝔰 i₁).1 = 2 := by
        have h1 : (tupleListHP F ((𝔰 i₁).2)).length = 2 := by
          have hc := congrArg List.length hsh
          simpa using hc
        rwa [tupleListHP_length] at h1
      have heq : ζ_A F ((𝔰 i₁).2)
          = ζ_A F (fun j : Fin 2 => (𝔰 i₁).2 ⟨j.1, by have := j.2; omega⟩) := by
        refine ζ_A_eq_of_reindex F hr ((𝔰 i₁).2) _ (fun i => ?_)
        refine PNat.eq ?_
        refine congrArg (fun j : Fin ((𝔰 i₁).1) => ((𝔰 i₁).2 j : ℕ)) ?_
        exact Fin.ext rfl
      exact (fun h0 => zeta_ne_zero_of_length_two (F := F) _
        (heq.symm.trans h0)) hz1
  · -- the support has exactly two elements
    obtain ⟨i₁, hi₁, i₂, hi₂, hne12⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
    have hs1mem : tupleListHP F ((𝔰 i₁).2) ∈ S := Finset.mem_image.mpr ⟨i₁, hi₁, rfl⟩
    have hs2mem : tupleListHP F ((𝔰 i₂).2) ∈ S := Finset.mem_image.mpr ⟨i₂, hi₂, rfl⟩
    -- Step 3(b): at most two tuples can occur
    have hSsub : S ⊆ ({[(w, ambH F w)],
        [(w - (Nat.card F - 1), ambH F (w - (Nat.card F - 1))),
          (Nat.card F - 1, ambH F (Nat.card F - 1))]} :
          Finset (List (ℕ × Polynomial (Ambient F)))) := by
      intro s hs
      rcases hshape s hs with hsh | hsh
      · rw [eq_singleton_of_map_fst_eq (F := F) (hS_entry s hs) hsh]
        exact Finset.mem_insert_self _ _
      · rw [eq_pair_of_map_fst_eq (F := F) (hS_entry s hs) hsh]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hScard : S.card ≤ 2 := by
      have h2 : ({[(w, ambH F w)],
          [(w - (Nat.card F - 1), ambH F (w - (Nat.card F - 1))),
            (Nat.card F - 1, ambH F (Nat.card F - 1))]} :
            Finset (List (ℕ × Polynomial (Ambient F)))).card ≤ 2 := by
        refine le_trans (Finset.card_insert_le _ _) ?_
        rw [Finset.card_singleton]
      exact le_trans (Finset.card_le_card hSsub) h2
    have hTcard : T.card = 2 := by
      have h1 : S.card = T.card := by
        rw [hS]
        exact Finset.card_image_of_injOn hS_inj
      omega
    have hsub : ({i₁, i₂} : Finset ι) ⊆ T := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi₁
      · exact hi₂
    have hTeq : T = {i₁, i₂} := by
      refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
      have hc : ({i₁, i₂} : Finset ι).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hne12]), Finset.card_singleton]
      omega
    have hrel2 : (a i₁ : RatFunc F) • ζ_A F ((𝔰 i₁).2)
        + (a i₂ : RatFunc F) • ζ_A F ((𝔰 i₂).2) = 0 := by
      have h := hTrel
      rw [hTeq, Finset.sum_pair hne12] at h
      exact h
    -- the two possible shapes
    rcases hshape _ hs1mem with h1 | h1 <;> rcases hshape _ hs2mem with h2 | h2
    · exfalso
      exact (fun hh => by
        exact hh ((eq_singleton_of_map_fst_eq (F := F) (hS_entry _ hs1mem) h1).trans
          (eq_singleton_of_map_fst_eq (F := F) (hS_entry _ hs2mem) h2).symm))
        (fun hh => hne12 (hlinj i₁ i₂ hh))
    · have hp1 := eq_singleton_of_map_fst_eq (F := F) (hS_entry _ hs1mem) h1
      have hp2 := eq_pair_of_map_fst_eq (F := F) (hS_entry _ hs2mem) h2
      have hk : 1 ≤ w - (Nat.card F - 1) := by
        have hmem : ((w - (Nat.card F - 1), ambH F (w - (Nat.card F - 1))) :
            ℕ × Polynomial (Ambient F)) ∈ tupleListHP F ((𝔰 i₂).2) := by rw [hp2]; simp
        exact hS_pos _ hs2mem _ hmem
      have hwk : w = (w - (Nat.card F - 1)) + (Nat.card F - 1) := by omega
      exact (hend ((𝔰 i₁).2) ((𝔰 i₂).2) (w - (Nat.card F - 1)) hk hwk hp1 hp2
        (a i₁) (a i₂) (ha_ne i₁ hi₁) (ha_ne i₂ hi₂)) hrel2
    · have hp2 := eq_singleton_of_map_fst_eq (F := F) (hS_entry _ hs2mem) h2
      have hp1 := eq_pair_of_map_fst_eq (F := F) (hS_entry _ hs1mem) h1
      have hk : 1 ≤ w - (Nat.card F - 1) := by
        have hmem : ((w - (Nat.card F - 1), ambH F (w - (Nat.card F - 1))) :
            ℕ × Polynomial (Ambient F)) ∈ tupleListHP F ((𝔰 i₁).2) := by rw [hp1]; simp
        exact hS_pos _ hs1mem _ hmem
      have hwk : w = (w - (Nat.card F - 1)) + (Nat.card F - 1) := by omega
      refine (hend ((𝔰 i₂).2) ((𝔰 i₁).2) (w - (Nat.card F - 1)) hk hwk hp2 hp1
        (a i₂) (a i₁) (ha_ne i₂ hi₂) (ha_ne i₁ hi₁)) ?_
      rw [add_comm]; exact hrel2
    · exfalso
      exact (fun hh => hne12 (hlinj i₁ i₂ hh))
        ((eq_pair_of_map_fst_eq (F := F) (hS_entry _ hs1mem) h1).trans
          (eq_pair_of_map_fst_eq (F := F) (hS_entry _ hs2mem) h2).symm)

/-! ## §5. The `𝒯'`-induction, assuming the two-term endgame -/

/-- ★★★ **Dac's Theorem 6.2 (`𝒯'`-independence), conditional on the two-term endgame.**  For every
weight `1 ≤ w ≤ 2q-2`, the family `𝒯'_w` of MZV's of tuples with `q ∤ s_i` is `RatFunc F`-linearly
independent, assuming `TwoTermIndP w'` for every weight `q < w' ≤ 2q-2` (Dac's §6 endgame).

⚠ The hypothesis is needed **only for `q < w'`**: at `w' ≤ q` the independence is
`TupleIndP.tupleIndP_of_le`, and indeed `TwoTermIndP w'` is *false* at `w' = q` in general (over
`F₂` the space `𝒵_2` is one-dimensional, cf. `PLAN.md`).  Stating the hypothesis in this honest
range is what makes the assembly of `theorem_D` correct. -/
theorem tupleIndP_of_twoTerm :
    ∀ (w : ℕ) (hw1 : 1 ≤ w), w ≤ 2 * Nat.card F - 2 →
    (∀ w' : ℕ, Nat.card F < w' → w' ≤ 2 * Nat.card F - 2 → TwoTermIndP (F := F) w') →
    ∀ (ι : Type u) [Fintype ι] [DecidableEq ι], TupleIndP (F := F) ι w := by
  intro w
  refine Nat.strong_induction_on w ?_
  intro w ih hw1 hw2 hend ι _ _
  rcases lt_or_ge (Nat.card F) w with hwq | hwq
  · rw [TupleIndP]
    intro 𝔰 hnd hwt hlinj
    rw [Fintype.linearIndependent_iffₛ]
    intro c g hcg i
    have hd : (∑ i, (c i - g i) • ζ_A F ((𝔰 i).2)) = 0 := by
      have h1 : (∑ i, (c i - g i) • ζ_A F ((𝔰 i).2))
          = ∑ i, (c i • ζ_A F ((𝔰 i).2) - g i • ζ_A F ((𝔰 i).2)) :=
        Finset.sum_congr rfl (fun i _ => sub_smul (c i) (g i) _)
      rw [h1, Finset.sum_sub_distrib, hcg, sub_self]
    exact sub_eq_zero.mp (tupleIndP_step (F := F) w hw1 hwq hw2
      (fun w' hlt hw1' => ih w' hlt hw1' (by omega) hend)
      (hend w hwq hw2) 𝔰 hnd hwt hlinj (fun i => c i - g i) hd i)
  · exact tupleIndP_of_le (F := F) hw1 hwq ι

end ZagierHoffmanPositiveChar
