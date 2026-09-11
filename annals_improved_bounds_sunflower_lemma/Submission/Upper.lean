import Mathlib
import Submission.SunBasic
import Submission.SunExtras
import Submission.SunOne
import Submission.Deep
import Submission.Ground
import Submission.LinkProps
import Submission.SunLift
import Submission.Spread

/-!
# From the petal estimate to sunflower-free bounds (Bell–Chueluecha–Warnke / Rao)
-/
open Finset
open scoped BigOperators
open Real

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]

/-- constant for the sunflower-free level bound -/
noncomputable def Ksf : ℝ := 2 ^ 72

/-! ## log helpers -/
lemma log_two_pos_real : (0 : ℝ) < Real.log 2 := by
  exact Real.log_pos (by norm_num)

lemma log_two_ge_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h
  linarith

lemma log_two_k_pos {k : ℕ} (hk : 1 ≤ k) : (0 : ℝ) < Real.log (2 * (k : ℝ)) := by
  apply Real.log_pos
  norm_num
  nlinarith [show (1 : ℝ) ≤ (k : ℝ) by exact_mod_cast hk]

/-- union of all members -/
noncomputable def unionMem (F : Finset (Finset α)) : Finset α := F.biUnion id

lemma mem_unionMem {F : Finset (Finset α)} {A : Finset α} (hA : A ∈ F) :
    A ⊆ unionMem F := by
  intro x hx
  simp [unionMem]
  exact ⟨A, hA, hx⟩



lemma Ksf_ge_Cmain : Cmain ≤ Ksf := by unfold Cmain Ksf; norm_num
lemma Ksf_ge_two : (2 : ℝ) ≤ Ksf := by unfold Ksf; norm_num

/-- `(p-1) < Ksf·p·log 2` for p ≥ 2 -/
lemma base_bound {p : ℕ} (hp : 2 ≤ p) : ((p : ℝ) - 1) < Ksf * (p : ℝ) * Real.log 2 := by
  have hK : (2 : ℝ) ≤ Ksf := Ksf_ge_two
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := log_two_ge_half
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hKlog : (1 : ℝ) ≤ Ksf * Real.log 2 := by nlinarith [hK, hlog2]
  have hp0 : 0 ≤ (p : ℝ) := by positivity
  have hR : (p : ℝ) ≤ Ksf * (p : ℝ) * Real.log 2 := by nlinarith [hKlog, hp0]
  have hpm : (p : ℝ) - 1 < (p : ℝ) := by nlinarith [hp2]
  linarith

/-! ## Sunflower-free bound for k-uniform families (BCW induction) -/
lemma sunfree_level_bound {F : Finset (Finset α)} {p k : ℕ}
    (hp : 2 ≤ p) (hk : 1 ≤ k)
    (huni : ∀ A ∈ F, A.card = k)
    (hfree : SunflowerFree F p) :
    (F.card : ℝ) < (Ksf * (p : ℝ) * Real.log (2 * (k : ℝ))) ^ k := by
  have main : ∀ (k : ℕ) (F : Finset (Finset α)),
      (∀ A ∈ F, A.card = k) → SunflowerFree F p → 1 ≤ k →
      (F.card : ℝ) < (Ksf * (p : ℝ) * Real.log (2 * (k : ℝ))) ^ k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro F huni hfree hk
      by_cases hk1 : k = 1
      · subst k
        have hc : F.card ≤ p - 1 := one_uniform_sunfree_card (F := F) (p := p) hp huni hfree
        have hpm : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
          have hp1 : 1 ≤ p := by omega
          have : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by exact_mod_cast (Nat.sub_add_cancel hp1)
          linarith
        have hcle : (F.card : ℝ) ≤ (p : ℝ) - 1 := by
          rw [← hpm]
          exact_mod_cast hc
        have hlt : (F.card : ℝ) < Ksf * (p : ℝ) * Real.log 2 := lt_of_le_of_lt hcle (base_bound hp)
        simpa [pow_one] using hlt
      · have hk2 : 2 ≤ k := by omega
        by_contra hnot
        have hge : (Ksf * (p : ℝ) * Real.log (2 * (k : ℝ))) ^ k ≤ (F.card : ℝ) := le_of_not_gt hnot
        let R : ℝ := Ksf * (p : ℝ) * Real.log (2 * (k : ℝ))
        let X : Finset α := unionMem F
        have hsubF : ∀ A ∈ F, A ⊆ X := by intro A hA; exact mem_unionMem hA
        have huniX : ∀ A ∈ F, A ⊆ X ∧ A.card = k := by intro A hA; exact ⟨hsubF A hA, huni A hA⟩
        have hRpos : 0 < R := by
          have h1 : 0 < Real.log (2 * (k : ℝ)) := log_two_k_pos hk
          unfold R
          have hp0 : 0 < (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
          have hKp : 0 < Ksf * (p : ℝ) := by
            have hK : 0 < Ksf := by unfold Ksf; norm_num
            exact mul_pos hK hp0
          exact mul_pos hKp h1
        by_cases hsp : ∀ T : Finset α, T ⊆ X → T.Nonempty →
            (#(F.filter (fun A : Finset α => T ⊆ A)) : ℝ) ≤ R ^ (k - T.card)
        · have h6ltR : (6 : ℝ) < R := by
            have hKsf7 : (7 : ℝ) ≤ Ksf := by unfold Ksf; norm_num
            have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
            have hlog1 : (1 : ℝ) ≤ Real.log (2 * (k : ℝ)) := by
              have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := log_two_ge_half
              have hk2r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
              have hlogk : Real.log 2 ≤ Real.log (k : ℝ) := by
                apply Real.log_le_log
                · norm_num
                · nlinarith
              have hsum : Real.log (2 * (k : ℝ)) = Real.log 2 + Real.log (k : ℝ) := by
                have h2n : (2 : ℝ) ≠ 0 := by norm_num
                have hkn : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
                rw [Real.log_mul h2n hkn]
              rw [hsum]
              nlinarith [hhalf, hlogk]
            have hK0 : 0 ≤ Ksf := by unfold Ksf; norm_num
            have hp0' : 0 ≤ (p : ℝ) := by positivity
            have hKp7 : (7 : ℝ) ≤ Ksf * (p : ℝ) := by
              have hpr := mul_le_mul hKsf7 hp1 (by norm_num) hK0
              simpa using hpr
            have hfull : (7 : ℝ) ≤ (Ksf * (p : ℝ)) * Real.log (2 * (k : ℝ)) := by
              have h0 : 0 ≤ Ksf * (p : ℝ) := mul_nonneg hK0 hp0'
              have hm := mul_le_mul hKp7 hlog1 (by norm_num) h0
              simpa using hm
            have h7 : (7 : ℝ) ≤ R := by unfold R; exact hfull
            nlinarith
          have hGround1 : (1 : ℝ) ≤ R := by nlinarith [h6ltR]
          have hGround6 : 6 * k ≤ X.card := Ground.sixk_le_card (X := X) (F := F) (k := k) (R := R)
            huniX hsp hge h6ltR hk
          have hGroundr : R ≤ (X.card : ℝ) := Ground.r_le_card (X := X) (F := F) (k := k) (R := R)
            huniX hge (le_of_lt hRpos) hk
          have hCmain : Cmain * (p : ℝ) * Real.log (2 * (k : ℝ)) ≤ R := by
            unfold R
            have hK : Cmain ≤ Ksf := Ksf_ge_Cmain
            have hlog : 0 ≤ Real.log (2 * (k : ℝ)) := le_of_lt (log_two_k_pos hk)
            have hp0 : 0 ≤ (p : ℝ) := by positivity
            have hplog0 : 0 ≤ (p : ℝ) * Real.log (2 * (k : ℝ)) := mul_nonneg hp0 hlog
            have hmain : Cmain * ((p : ℝ) * Real.log (2 * (k : ℝ))) ≤
                Ksf * ((p : ℝ) * Real.log (2 * (k : ℝ))) :=
              mul_le_mul_of_nonneg_right hK hplog0
            simpa [mul_assoc] using hmain
          rcases spread_disjoint (X := X) (S := F) (k := k) (p := p) (r := R) hk2 hp
            hsubF huni hsp hge hGround1 hGroundr hGround6 hCmain with ⟨T, hTF, hTcard, hdisjT⟩
          have hsun := hasSunflower_of_disjoint_indexed (F := F) (r := p) (by
            refine ⟨T, hTF, hTcard, ?_⟩
            intro A B hA hB hAB
            exact hdisjT A hA B hB hAB)
          exact hfree hsun
        · push_neg at hsp
          rcases hsp with ⟨T, hTX, hTne, hTgt⟩
          have hgt : R ^ (k - T.card) < (#(F.filter (fun A : Finset α => T ⊆ A)) : ℝ) := hTgt
          have hmemT : ∃ A ∈ F, T ⊆ A := by
            have h0 : (0 : ℝ) ≤ R ^ (k - T.card) := pow_nonneg (le_of_lt hRpos) (k - T.card)
            have hpos : (0 : ℝ) < (#(F.filter (fun A : Finset α => T ⊆ A)) : ℝ) :=
              lt_of_le_of_lt h0 hgt
            have hposN : 0 < (F.filter (fun A : Finset α => T ⊆ A)).card := by
              exact_mod_cast hpos
            rw [Finset.card_pos] at hposN
            rcases hposN with ⟨A, hA⟩
            exact ⟨A, (Finset.mem_filter.mp hA).1, (Finset.mem_filter.mp hA).2⟩
          rcases hmemT with ⟨A0, hA0F, hTA0⟩
          have hTle : T.card ≤ k := by
            have : T.card ≤ A0.card := Finset.card_le_card hTA0
            rw [huni A0 hA0F] at this
            exact this
          have hTlt : T.card < k := by
            by_contra hnotlt
            have hTk : T.card = k := by omega
            have hcnt : (F.filter (fun A : Finset α => T ⊆ A)).card ≤ 1 := by
              have hsub1 : F.filter (fun A : Finset α => T ⊆ A) ⊆ {T} := by
                intro A hA
                have hA' : A ∈ F := (Finset.mem_filter.mp hA).1
                have hTA : T ⊆ A := (Finset.mem_filter.mp hA).2
                have hAcard : A.card = k := huni A hA'
                have hAeq : A = T := by
                  have hTAcard : A.card ≤ T.card := by rw [hAcard, hTk]
                  have hTeq : T = A := Finset.eq_of_subset_of_card_le hTA hTAcard
                  exact hTeq.symm
                simp [hAeq]
              exact Finset.card_le_card hsub1
            have hR0 : R ^ (k - T.card) = 1 := by
              rw [hTk]
              simp
            have h1lt : (1 : ℝ) < (#(F.filter (fun A : Finset α => T ⊆ A)) : ℝ) := by
              simpa [hR0] using hgt
            have hle1 : (#(F.filter (fun A : Finset α => T ⊆ A)) : ℝ) ≤ 1 := by exact_mod_cast hcnt
            linarith
          let G : Finset (Finset α) := link F T
          have hGcard : G.card = (F.filter (fun A : Finset α => T ⊆ A)).card := link_card (F := F) (T := T)
          have hGuni : ∀ B ∈ G, B.card = k - T.card := by
            intro B hB
            apply link_mem_card (F := F) (T := T) (k := k) hB huni
            intro A hA hTA
            have hinter : T ∩ A = T := by
              apply Finset.ext
              intro x
              constructor
              · intro hx; exact (Finset.mem_inter.mp hx).1
              · intro hx; exact Finset.mem_inter.mpr ⟨hx, hTA hx⟩
            have hsd : (A \ T).card = A.card - T.card := by
              rw [Finset.card_sdiff, hinter]
            have hk : A.card = k := huni A hA
            rw [hsd, hk]
          have hGfree : SunflowerFree G p := link_sunflower_free (F := F) (T := T) hfree
          have hkt : 1 ≤ k - T.card := by
            have hTlt' : T.card + 1 ≤ k := by omega
            omega
          have hTcardpos : 0 < T.card := Finset.card_pos.mpr hTne
          have hih := ih (k - T.card) (by omega) G hGuni hGfree hkt
          have hlogle : Real.log (2 * ((k - T.card : ℕ) : ℝ)) ≤ Real.log (2 * (k : ℝ)) := by
            have hposN : 0 < k - T.card := by omega
            have hpos2 : (0 : ℝ) < 2 * ((k - T.card : ℕ) : ℝ) := by
              have hx : (0 : ℝ) < ((k - T.card : ℕ) : ℝ) := by exact_mod_cast hposN
              nlinarith
            apply Real.log_le_log hpos2
            have hsub : (k - T.card : ℕ) ≤ k := Nat.sub_le k T.card
            have hcast : ((k - T.card : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hsub
            nlinarith
          have hK0 : 0 ≤ Ksf := by unfold Ksf; norm_num
          have hp0' : 0 ≤ (p : ℝ) := by positivity
          have hKp0 : 0 ≤ Ksf * (p : ℝ) := mul_nonneg hK0 hp0'
          have hKle : Ksf * (p : ℝ) * Real.log (2 * ((k - T.card : ℕ) : ℝ)) ≤ R := by
            have hmm := mul_le_mul_of_nonneg_left hlogle hKp0
            unfold R
            simpa [mul_assoc] using hmm
          have hb0 : 0 ≤ Ksf * (p : ℝ) * Real.log (2 * ((k - T.card : ℕ) : ℝ)) := by
            have hlog0 : 0 ≤ Real.log (2 * ((k - T.card : ℕ) : ℝ)) := le_of_lt (log_two_k_pos hkt)
            exact mul_nonneg hKp0 hlog0
          have hthr : (Ksf * (p : ℝ) * Real.log (2 * ((k - T.card : ℕ) : ℝ))) ^ (k - T.card)
              ≤ R ^ (k - T.card) := pow_le_pow_left₀ hb0 hKle (k - T.card)
          have hih_lt : (G.card : ℝ) < (Ksf * (p : ℝ) * Real.log (2 * ((k - T.card : ℕ) : ℝ))) ^ (k - T.card) := hih
          have h1lt : (G.card : ℝ) < R ^ (k - T.card) := lt_of_lt_of_le hih_lt hthr
          have hcount : (F.filter (fun A : Finset α => T ⊆ A)).card = G.card := hGcard.symm
          have hgt2 : R ^ (k - T.card) < (G.card : ℝ) := by
            rw [hcount] at hgt
            exact hgt
          linarith
  exact main k F huni hfree hk

def level (F : Finset (Finset α)) (j : ℕ) : Finset (Finset α) :=
  F.filter (fun A => A.card = j)

lemma mem_level {F : Finset (Finset α)} {j : ℕ} {A : Finset α} :
    A ∈ level F j ↔ A ∈ F ∧ A.card = j := by
  simp [level]

lemma level_subset (F : Finset (Finset α)) (j : ℕ) : level F j ⊆ F := by
  intro A hA
  unfold level at hA
  exact (Finset.mem_filter.mp hA).1

lemma level_card_real (F : Finset (Finset α)) (j : ℕ) :
    ((level F j).card : ℝ) = ∑ A ∈ F, (if A.card = j then (1 : ℝ) else 0) := by
  unfold level
  exact_mod_cast (Finset.card_filter (s := F) (p := fun A : Finset α => A.card = j))

lemma sum_partition {F : Finset (Finset α)} {w : ℕ}
    (hsize : ∀ A ∈ F, A.card ≤ w) :
    (F.card : ℝ) = ∑ j ∈ Finset.range (w + 1), ((level F j).card : ℝ) := by
  calc
    (F.card : ℝ) = ∑ A ∈ F, (1 : ℝ) := by simp
    _ = ∑ A ∈ F, (∑ j ∈ Finset.range (w + 1), if A.card = j then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro A hA
      have hc : A.card ≤ w := hsize A hA
      have hlt : A.card < w + 1 := by omega
      have hmem : A.card ∈ Finset.range (w + 1) := Finset.mem_range.mpr hlt
      rw [Finset.sum_ite_eq (Finset.range (w + 1)) (A.card) (fun _ : ℕ => (1 : ℝ))]
      simp [hmem]
    _ = ∑ j ∈ Finset.range (w + 1), (∑ A ∈ F, if A.card = j then (1 : ℝ) else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range (w + 1), ((level F j).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [level_card_real]

lemma log_two_w_ge_one {w : ℕ} (hw : 2 ≤ w) : (1 : ℝ) ≤ Real.log (2 * (w : ℝ)) := by
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := log_two_ge_half
  have hw2 : (2 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hlogw : Real.log 2 ≤ Real.log (w : ℝ) := by
    apply Real.log_le_log
    · norm_num
    · nlinarith
  have hsum : Real.log (2 * (w : ℝ)) = Real.log 2 + Real.log (w : ℝ) := by
    have h2n : (2 : ℝ) ≠ 0 := by norm_num
    have hwn : (w : ℝ) ≠ 0 := by exact_mod_cast (by omega : w ≠ 0)
    rw [Real.log_mul h2n hwn]
  rw [hsum]
  nlinarith [hhalf, hlogw]

lemma sunfree_wsets_bound {F : Finset (Finset α)} {p w : ℕ}
    (hp : 2 ≤ p) (hw : 2 ≤ w)
    (hsize : ∀ A ∈ F, A.card ≤ w)
    (hfree : SunflowerFree F p) :
    (F.card : ℝ) < ((w : ℝ) + (p : ℝ) + 1) * (Ksf * (p : ℝ) * Real.log (2 * (w : ℝ))) ^ w := by
  let base : ℝ := Ksf * (p : ℝ) * Real.log (2 * (w : ℝ))
  have hbase1 : (1 : ℝ) ≤ base := by
    have hK1 : (1 : ℝ) ≤ Ksf := by unfold Ksf; norm_num
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
    have hlog1 : (1 : ℝ) ≤ Real.log (2 * (w : ℝ)) := log_two_w_ge_one hw
    have hK0 : 0 ≤ Ksf := by unfold Ksf; norm_num
    have hp0 : 0 ≤ (p : ℝ) := by positivity
    have hKp : (1 : ℝ) ≤ Ksf * (p : ℝ) := by
      have hmm := mul_le_mul hK1 hp1 (by norm_num) hK0
      simpa using hmm
    have hmm := mul_le_mul hKp hlog1 (by norm_num) (mul_nonneg hK0 hp0)
    simpa [base] using hmm
  have hbasew1 : (1 : ℝ) ≤ base ^ w := one_le_pow₀ hbase1
  have hbasew0 : 0 < base ^ w := by nlinarith [hbasew1]
  -- per-level bound
  have hlev : ∀ j : ℕ, j ≤ w →
      ((level F j).card : ℝ) ≤ base ^ w := by
    intro j hjw
    by_cases hj0 : j = 0
    · subst j
      have hle1 : (level F 0).card ≤ 1 := by
        have hsub : level F 0 ⊆ {∅} := by
          intro A hA
          rcases (mem_level.mp hA) with ⟨hA', hc0⟩
          have hA0 : A = ∅ := Finset.card_eq_zero.mp hc0
          simp [hA0]
        exact Finset.card_le_card hsub
      have hle1r : ((level F 0).card : ℝ) ≤ 1 := by exact_mod_cast hle1
      calc
        ((level F 0).card : ℝ) ≤ 1 := hle1r
        _ ≤ base ^ w := by nlinarith [hbasew1]
    · have hj1 : 1 ≤ j := by omega
      have hfreej : SunflowerFree (level F j) p :=
        SunflowerFree.of_subset (level_subset F j) hfree
      have hunij : ∀ A ∈ (level F j), A.card = j := by
        intro A hA
        exact (mem_level.mp hA).2
      have hlb := sunfree_level_bound (F := level F j) (p := p) (k := j) hp hj1 hunij hfreej
      -- hlb : (level F j).card < (Ksf p log(2j))^j
      have hlogmono : Real.log (2 * (j : ℝ)) ≤ Real.log (2 * (w : ℝ)) := by
        have hpos2 : (0 : ℝ) < 2 * (j : ℝ) := by
          have hj0r : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
          nlinarith
        apply Real.log_le_log hpos2
        have hjw : (j : ℝ) ≤ (w : ℝ) := by exact_mod_cast hjw
        nlinarith
      have hK0 : 0 ≤ Ksf := by unfold Ksf; norm_num
      have hp0 : 0 ≤ (p : ℝ) := by positivity
      have hKp0 : 0 ≤ Ksf * (p : ℝ) := mul_nonneg hK0 hp0
      have hb01 : 0 ≤ Ksf * (p : ℝ) * Real.log (2 * (j : ℝ)) := by
        have hlj : 0 ≤ Real.log (2 * (j : ℝ)) := le_of_lt (log_two_k_pos hj1)
        exact mul_nonneg hKp0 hlj
      have hLj : Ksf * (p : ℝ) * Real.log (2 * (j : ℝ)) ≤ base := by
        have hmm := mul_le_mul_of_nonneg_left hlogmono hKp0
        unfold base
        simpa [mul_assoc] using hmm
      have hLjw : (Ksf * (p : ℝ) * Real.log (2 * (j : ℝ))) ^ j ≤ base ^ w := by
        have h1 : (Ksf * (p : ℝ) * Real.log (2 * (j : ℝ))) ^ j ≤ base ^ j :=
          pow_le_pow_left₀ hb01 hLj j
        have h2 : base ^ j ≤ base ^ w := pow_le_pow_right₀ hbase1 hjw
        exact le_trans h1 h2
      have hstrict : ((level F j).card : ℝ) < base ^ w := lt_of_lt_of_le hlb hLjw
      exact le_of_lt hstrict
  have hsum : (F.card : ℝ) = ∑ j ∈ Finset.range (w + 1), ((level F j).card : ℝ) := sum_partition hsize
  have htotal : (F.card : ℝ) ≤ ((w : ℝ) + 1) * base ^ w := by
    rw [hsum]
    calc
      (∑ j ∈ Finset.range (w + 1), ((level F j).card : ℝ))
          ≤ ∑ j ∈ Finset.range (w + 1), base ^ w := by
            apply Finset.sum_le_sum
            intro j hj
            exact hlev j (by have : j < w + 1 := Finset.mem_range.mp hj; omega)
      _ = ((w : ℝ) + 1) * base ^ w := by
        rw [Finset.sum_const]
        simp [nsmul_eq_mul]
  have hcoef : ((w : ℝ) + 1) * base ^ w < ((w : ℝ) + (p : ℝ) + 1) * base ^ w := by
    have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have h01 : (0 : ℝ) < (p : ℝ) := by nlinarith [hp2r]
    have hmid : (w : ℝ) + 1 < (w : ℝ) + (p : ℝ) + 1 := by nlinarith [hp2r]
    exact mul_lt_mul_of_pos_right hmid hbasew0
  exact lt_of_le_of_lt htotal hcoef

/-! ## consequence: large enough families contain a sunflower -/
theorem sunflower_of_large {X : Finset α} {F : Finset (Finset α)} {p w : ℕ} {B : ℝ}
    (hp : 2 ≤ p) (hw : 2 ≤ w)
    (hS : ∀ A ∈ F, A ⊆ X) (hsize : ∀ A ∈ F, A.card ≤ w)
    (hB : ((w : ℝ) + (p : ℝ) + 1) * (Ksf * (p : ℝ) * Real.log (2 * (w : ℝ))) ^ w ≤ B)
    (hcard : (F.card : ℝ) ≥ B) :
    HasSunflower F p := by
  by_contra hfree
  have hlt := sunfree_wsets_bound (F := F) (p := p) (w := w) hp hw hsize hfree
  have : (F.card : ℝ) < B := lt_of_lt_of_le hlt hB
  linarith

end Submission.Sun
