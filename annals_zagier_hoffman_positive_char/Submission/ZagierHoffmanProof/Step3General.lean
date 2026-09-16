import Submission.ZagierHoffmanProof.Step3Splitting
import Submission.Commons.Combinatorics.List.take_eq_take_imp_eq_of_sup_lt

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Polynomial PowerSeries Finset
open scoped WithZero Topology

/-!
# Dac §5.3 Step 3 for a general MZV-type datum

`Step3Splitting.lean` runs the "second relation" of Dac's §5.3 Step 3 on the FULL datum `T0S` of
all weight-`w` tuples of `𝒯0`.  For the final contradiction one needs the datum of the *support* of
the relation (the paper's `I = ⋃_i I(s_i)`), i.e. an arbitrary sub-`Finset`.  This file provides the
general versions: a structure `MZVD` bundling the membership facts, and the chain

  `evalSeriesGen_tmF_MZVD`  → `bridge_MZVD` → `step3_II_MZVD` → `dvd_pred_weight_MZVD`

for an arbitrary `MZVD`.  The `T0S`-instances are `T0S_MZVD`.
-/

namespace ZagierHoffmanPositiveChar

/-- A `Finset` of exponent tuples of the MZV type: unit `Q`'s, positive exponents `≤ q`, all of the
same weight `w`. -/
structure MZVD (F : Type*) [Field F] [Finite F] (w : ℕ) where
  /-- the tuples -/
  S : Finset (List (ℕ × Polynomial (Ambient F)))
  /-- all `Q`'s are `1` -/
  two : ∀ s ∈ S, ∀ x ∈ s, x.2 = 1
  /-- all exponents are `≥ 1` -/
  pos : ∀ s ∈ S, ∀ x ∈ s, 1 ≤ x.1
  /-- all exponents are `≤ q` -/
  le : ∀ s ∈ S, ∀ x ∈ s, x.1 ≤ Nat.card F
  /-- all tuples have weight `w` -/
  weight : ∀ s ∈ S, tmWeight s = w

section General

variable {F : Type*} [Field F] [Finite F] [DecidableEq (RatFunc F)]

attribute [local instance 100] Classical.decEq

lemma MZVD.drop_two {w : ℕ} (D : MZVD F w) {s : List (ℕ × Polynomial (Ambient F))}
    (hs : s ∈ D.S) (k : ℕ) : ∀ x ∈ s.drop k, x.2 = 1 := by
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp (List.mem_of_mem_drop hx)
  exact D.two s hs _ (List.get_mem s j)

lemma MZVD.drop_pos {w : ℕ} (D : MZVD F w) {s : List (ℕ × Polynomial (Ambient F))}
    (hs : s ∈ D.S) (k : ℕ) : ∀ x ∈ s.drop k, 1 ≤ x.1 := by
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp (List.mem_of_mem_drop hx)
  exact D.pos s hs _ (List.get_mem s j)

lemma MZVD.drop_le {w : ℕ} (D : MZVD F w) {s : List (ℕ × Polynomial (Ambient F))}
    (hs : s ∈ D.S) (k : ℕ) : ∀ x ∈ s.drop k, x.1 ≤ Nat.card F := by
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp (List.mem_of_mem_drop hx)
  exact D.le s hs _ (List.get_mem s j)

lemma MZVD.drop_weight {w : ℕ} (D : MZVD F w) {s : List (ℕ × Polynomial (Ambient F))}
    (hs : s ∈ D.S) (k : ℕ) : tmWeight (s.drop k) + tmWeight (s.take k) = w := by
  have h1 := tmWeight_take_add_drop s k
  have h2 := D.weight s hs
  omega

/-- `GSuperEntire` of the `L`-series of the dropped tail. -/
lemma gSuperEntire_tmL_drop {w : ℕ} (D : MZVD F w) {s : List (ℕ × Polynomial (Ambient F))}
    (hs : s ∈ D.S) (k : ℕ) :
    GSuperEntire ambGamma (tmL (Nat.card F) (ambOmega F) (s.drop k)) :=
  gSuperEntire_tmL_unit F (s.drop k) (D.drop_two hs k) (D.drop_pos hs k)

/-! ## §2. Step 3 (II) for a general datum -/

/-- **Step 3 (II) for a general datum**: if the prefix `t` is uniquely extendable in `D.S`, then
`f_t(θ)` is the single term `b_v(θ)·𝓛(s₀ ⧵ t)(θ)`. -/
theorem evalSeriesGen_tmF_MZVD {w : ℕ} (hw : 1 ≤ w)
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    (D : MZVD F w) (b : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} →
      Polynomial (Ambient F))
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w})
    (hvS : tupleListP F (T0exp F w hw v) ∈ D.S) {k : ℕ}
    (hklen : k ≤ (tupleListP F (T0exp F w hw v)).length)
    (huniq : ∀ s ∈ D.S, s.take k = (tupleListP F (T0exp F w hw v)).take k →
      s = tupleListP F (T0exp F w hw v)) :
    evalSeriesGen (tmF (Nat.card F) (ambOmega F) w D.S (T0cf F w hw b)
        ((tupleListP F (T0exp F w hw v)).take k)) (ambTheta F)
      = (b v).eval (ambTheta F) * evalSeriesGen (tmL (Nat.card F) (ambOmega F)
          ((tupleListP F (T0exp F w hw v)).drop k)) (ambTheta F) := by
  have hlen : ((tupleListP F (T0exp F w hw v)).take k).length = k := by
    rw [List.length_take, Nat.min_eq_left hklen]
  have htake : (tupleListP F (T0exp F w hw v)).take
      ((tupleListP F (T0exp F w hw v)).take k).length
      = (tupleListP F (T0exp F w hw v)).take k := by
    rw [hlen]
  have hse' : GSuperEntire ambGamma (tmL (Nat.card F) (ambOmega F)
      ((tupleListP F (T0exp F w hw v)).drop
        ((tupleListP F (T0exp F w hw v)).take k).length)) := by
    rw [hlen]
    exact gSuperEntire_tmL_drop D hvS k
  have huniq' : ∀ s ∈ D.S, s.take ((tupleListP F (T0exp F w hw v)).take k).length
      = (tupleListP F (T0exp F w hw v)).take k →
      s = tupleListP F (T0exp F w hw v) := by
    rw [hlen]
    exact huniq
  have h1 := evalSeriesGen_tmF_single (F := F) w (S := D.S) (cf := T0cf F w hw b)
    (t := (tupleListP F (T0exp F w hw v)).take k)
    (s₀ := tupleListP F (T0exp F w hw v)) hvS htake huniq' hse'
  rw [h1, hlen, T0cf_apply F hw b v]

/-! ## §3. The bridge on the dropped tail, for a general datum -/

/-- **The bridge on the dropped tail**: `π̃^{w(suffix)}·𝓛(suffix)(θ) =
b_v(θ)·ambInfHom (ζ_A 𝔰_suffix)`. -/
theorem bridge_MZVD {w : ℕ} (hw : 1 ≤ w)
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    (D : MZVD F w) (b : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} →
      Polynomial (Ambient F))
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w})
    (hvS : tupleListP F (T0exp F w hw v) ∈ D.S) {k : ℕ}
    (hkl : k < (tupleListP F (T0exp F w hw v)).length) :
    (ambPiTilde F) ^ (∑ j : Fin (suffixList F ((tupleListP F (T0exp F w hw v)).drop k)).length,
        (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k)
          (D.drop_pos hvS k) j : ℕ))
      * ((b v).eval (ambTheta F) * evalSeriesGen
          (tmL (Nat.card F) (ambOmega F) ((tupleListP F (T0exp F w hw v)).drop k))
          (ambTheta F))
      = (b v).eval (ambTheta F) * ambInfHom F (ζ_A F
          (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k) (D.drop_pos hvS k))) :=
  bridge_mul F (suffixList F ((tupleListP F (T0exp F w hw v)).drop k))
    (suffixList_ne_nil F (drop_ne_nil_of_lt_length hkl))
    (fun j => suffixList_mem_two F (D.drop_two hvS k)
      _ (List.get_mem (suffixList F ((tupleListP F (T0exp F w hw v)).drop k)) j))
    (fun j => suffixList_mem_pos F (D.drop_pos hvS k)
      _ (List.get_mem (suffixList F ((tupleListP F (T0exp F w hw v)).drop k)) j))
    (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k) (D.drop_pos hvS k))
    (fun j => rfl)
    (fun j => suffixList_mem_le F (D.drop_le hvS k)
      _ (List.get_mem (suffixList F ((tupleListP F (T0exp F w hw v)).drop k)) (Fin.rev j)))
    (b v)

/-- **Step 3 (II)**: the second relation of Dac §5.3 for a general datum. -/
theorem step3_II_MZVD {w : ℕ} (hw : 1 ≤ w)
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    (D : MZVD F w) (b : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} →
      Polynomial (Ambient F))
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w})
    (hvS : tupleListP F (T0exp F w hw v) ∈ D.S) {k : ℕ}
    (hkl : k < (tupleListP F (T0exp F w hw v)).length)
    (huniq : ∀ s ∈ D.S, s.take k = (tupleListP F (T0exp F w hw v)).take k →
      s = tupleListP F (T0exp F w hw v)) :
    (ambPiTilde F) ^ (∑ j : Fin (suffixList F ((tupleListP F (T0exp F w hw v)).drop k)).length,
        (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k) (D.drop_pos hvS k) j : ℕ))
      * evalSeriesGen (tmF (Nat.card F) (ambOmega F) w D.S (T0cf F w hw b)
          ((tupleListP F (T0exp F w hw v)).take k)) (ambTheta F)
      = (b v).eval (ambTheta F) * ambInfHom F (ζ_A F
          (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k) (D.drop_pos hvS k))) := by
  rw [evalSeriesGen_tmF_MZVD hw D b v hvS (le_of_lt hkl) huniq]
  exact bridge_MZVD hw D b v hvS hkl

/-! ## §4. Step 3, third part: the divisibility `(q-1) ∣ w - w(𝔱)`, for a general datum -/

/-- **Step 3's divisibility for a general datum**, in the exponent-sum form. -/
theorem dvd_pred_step3_II_MZVD {w : ℕ} (hw : 1 ≤ w)
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    (D : MZVD F w) (b : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} →
      Polynomial (Ambient F))
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w})
    (hvS : tupleListP F (T0exp F w hw v) ∈ D.S) {k : ℕ}
    (hkl : k < (tupleListP F (T0exp F w hw v)).length)
    (huniq : ∀ s ∈ D.S, s.take k = (tupleListP F (T0exp F w hw v)).take k →
      s = tupleListP F (T0exp F w hw v))
    (hbmem : ∀ j, (b v).coeff j ∈ ambA F 0)
    (hb0 : (b v).eval (ambTheta F) ≠ 0)
    (hζ : ζ_A F (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k) (D.drop_pos hvS k))
      ≠ 0)
    (hfK : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w D.S (T0cf F w hw b)
      ((tupleListP F (T0exp F w hw v)).take k)) (ambTheta F) ∈ ambK F)
    (hf0 : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w D.S (T0cf F w hw b)
      ((tupleListP F (T0exp F w hw v)).take k)) (ambTheta F) ≠ 0) :
    (Nat.card F - 1) ∣ (∑ j : Fin (suffixList F
        ((tupleListP F (T0exp F w hw v)).drop k)).length,
        (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k) (D.drop_pos hvS k) j : ℕ)) := by
  refine dvd_pred_of_v_eq_exp_mul
    (m := ∑ j : Fin (suffixList F ((tupleListP F (T0exp F w hw v)).drop k)).length,
        (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k) (D.drop_pos hvS k) j : ℕ))
    (y := (ambPiTilde F) ^ (∑ j : Fin (suffixList F
        ((tupleListP F (T0exp F w hw v)).drop k)).length,
        (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k) (D.drop_pos hvS k) j : ℕ)))
    (u := (b v).eval (ambTheta F) * ambInfHom F (ζ_A F
      (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k) (D.drop_pos hvS k))))
    (v := evalSeriesGen (tmF (Nat.card F) (ambOmega F) w D.S (T0cf F w hw b)
      ((tupleListP F (T0exp F w hw v)).take k)) (ambTheta F))
    (hy := ?_) (hu := ?_) (hv := ?_) (hv0 := hf0)
    (h := step3_II_MZVD hw D b v hvS hkl huniq)
  · exact v_ambPiTilde_pow F _
  · obtain ⟨k₁, hk₁⟩ := v_mem_ambK F (eval_mem_ambK F (b v) hbmem) hb0
    obtain ⟨k₂, hk₂⟩ := v_ambInfHom_mem_pred F _ hζ
    refine ⟨k₁ + k₂, ?_⟩
    rw [map_mul, hk₁, hk₂, ← WithZero.exp_add]
    congr 1
    push_cast
    ring
  · exact v_mem_ambK F hfK hf0

/-- **Step 3's divisibility in weight form**, for a general datum. -/
theorem dvd_pred_weight_MZVD {w : ℕ} (hw : 1 ≤ w)
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    (D : MZVD F w) (b : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} →
      Polynomial (Ambient F))
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w})
    (hvS : tupleListP F (T0exp F w hw v) ∈ D.S) {k : ℕ}
    (hkl : k < (tupleListP F (T0exp F w hw v)).length)
    (huniq : ∀ s ∈ D.S, s.take k = (tupleListP F (T0exp F w hw v)).take k →
      s = tupleListP F (T0exp F w hw v))
    (hbmem : ∀ j, (b v).coeff j ∈ ambA F 0)
    (hb0 : (b v).eval (ambTheta F) ≠ 0)
    (hζ : ζ_A F (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k) (D.drop_pos hvS k))
      ≠ 0)
    (hfK : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w D.S (T0cf F w hw b)
      ((tupleListP F (T0exp F w hw v)).take k)) (ambTheta F) ∈ ambK F)
    (hf0 : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w D.S (T0cf F w hw b)
      ((tupleListP F (T0exp F w hw v)).take k)) (ambTheta F) ≠ 0) :
    (Nat.card F - 1) ∣ (w - tmWeight ((tupleListP F (T0exp F w hw v)).take k)) := by
  have h1 := dvd_pred_step3_II_MZVD hw D b v hvS hkl huniq hbmem hb0 hζ hfK hf0
  have h2 : (∑ j : Fin (suffixList F ((tupleListP F (T0exp F w hw v)).drop k)).length,
      (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k) (D.drop_pos hvS k) j : ℕ))
      = tmWeight ((tupleListP F (T0exp F w hw v)).drop k) := by
    have hs := suffixList_weight F ((tupleListP F (T0exp F w hw v)).drop k)
    simp only [suffixExp_apply]
    rw [hs]
  rw [h2] at h1
  have h3 := D.drop_weight hvS k
  have h4 : w - tmWeight ((tupleListP F (T0exp F w hw v)).take k)
      = tmWeight ((tupleListP F (T0exp F w hw v)).drop k) := by omega
  rw [h4]
  exact h1

/-! ## §5. The same, with an abstract coefficient function (arbitrary index families) -/

/-- **Step 3 (II) with an abstract coefficient function.** -/
theorem evalSeriesGen_tmF_gen {w : ℕ}
    {S : Finset (List (ℕ × Polynomial (Ambient F)))}
    {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}
    {s₀ : List (ℕ × Polynomial (Ambient F))} (hs₀ : s₀ ∈ S) {k : ℕ}
    (hklen : k ≤ s₀.length)
    (huniq : ∀ s ∈ S, s.take k = s₀.take k → s = s₀)
    {b : Polynomial (Ambient F)} (hcf : cf s₀ = b)
    (hse : GSuperEntire ambGamma (tmL (Nat.card F) (ambOmega F) (s₀.drop k))) :
    evalSeriesGen (tmF (Nat.card F) (ambOmega F) w S cf (s₀.take k)) (ambTheta F)
      = b.eval (ambTheta F) * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (s₀.drop k))
          (ambTheta F) := by
  have hlen : (s₀.take k).length = k := by
    rw [List.length_take, Nat.min_eq_left hklen]
  have htake : s₀.take (s₀.take k).length = s₀.take k := by rw [hlen]
  have huniq' : ∀ s ∈ S, s.take (s₀.take k).length = s₀.take k → s = s₀ := by
    rw [hlen]; exact huniq
  have hse' : GSuperEntire ambGamma (tmL (Nat.card F) (ambOmega F)
      (s₀.drop (s₀.take k).length)) := by
    rw [hlen]; exact hse
  have h1 := evalSeriesGen_tmF_single (F := F) w (S := S) (cf := cf)
    (t := s₀.take k) (s₀ := s₀) hs₀ htake huniq' hse'
  rw [h1, hlen, hcf]

/-- **Step 3's divisibility with an abstract coefficient function.** -/
theorem dvd_pred_weight_gen {w : ℕ} (hw : 1 ≤ w) (D : MZVD F w)
    {s₀ : List (ℕ × Polynomial (Ambient F))} (hs₀ : s₀ ∈ D.S) {k : ℕ}
    (hkl : k < s₀.length)
    (huniq : ∀ s ∈ D.S, s.take k = s₀.take k → s = s₀)
    {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}
    {b : Polynomial (Ambient F)} (hcf : cf s₀ = b)
    (hbmem : ∀ j, b.coeff j ∈ ambA F 0) (hb0 : b.eval (ambTheta F) ≠ 0)
    (hζ : ζ_A F (suffixExp F (s₀.drop k) (D.drop_pos hs₀ k)) ≠ 0)
    (hfK : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w D.S cf (s₀.take k)) (ambTheta F)
      ∈ ambK F)
    (hf0 : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w D.S cf (s₀.take k)) (ambTheta F)
      ≠ 0) :
    (Nat.card F - 1) ∣ (w - tmWeight (K := Ambient F) (s₀.take k)) := by
  have hII := evalSeriesGen_tmF_gen (F := F) (w := w) (S := D.S) (cf := cf) hs₀
    (le_of_lt hkl) huniq hcf (gSuperEntire_tmL_drop D hs₀ k)
  have hbridge := bridge_mul F (suffixList F (s₀.drop k))
    (suffixList_ne_nil F (drop_ne_nil_of_lt_length hkl))
    (fun j => suffixList_mem_two F (D.drop_two hs₀ k)
      _ (List.get_mem (suffixList F (s₀.drop k)) j))
    (fun j => suffixList_mem_pos F (D.drop_pos hs₀ k)
      _ (List.get_mem (suffixList F (s₀.drop k)) j))
    (suffixExp F (s₀.drop k) (D.drop_pos hs₀ k)) (fun j => rfl)
    (fun j => suffixList_mem_le F (D.drop_le hs₀ k)
      _ (List.get_mem (suffixList F (s₀.drop k)) (Fin.rev j)))
    b
  have hstep : (ambPiTilde F) ^ (∑ j : Fin (suffixList F (s₀.drop k)).length,
        (suffixExp F (s₀.drop k) (D.drop_pos hs₀ k) j : ℕ))
      * evalSeriesGen (tmF (Nat.card F) (ambOmega F) w D.S cf (s₀.take k)) (ambTheta F)
      = b.eval (ambTheta F) * ambInfHom F (ζ_A F
          (suffixExp F (s₀.drop k) (D.drop_pos hs₀ k))) := by
    rw [hII]
    exact hbridge
  have hwt : tmWeight (K := Ambient F) s₀ = w := D.weight s₀ hs₀
  have h1 : (∑ j : Fin (suffixList F (s₀.drop k)).length,
      (suffixExp F (s₀.drop k) (D.drop_pos hs₀ k) j : ℕ)) = tmWeight (K := Ambient F) (s₀.drop k) := by
    have h := suffixList_weight F (s₀.drop k)
    simp only [suffixExp_apply]
    exact h
  have hfinal : (ambPiTilde F) ^ (tmWeight (K := Ambient F) (s₀.drop k))
      * evalSeriesGen (tmF (Nat.card F) (ambOmega F) w D.S cf (s₀.take k)) (ambTheta F)
      = b.eval (ambTheta F) * ambInfHom F (ζ_A F
          (suffixExp F (s₀.drop k) (D.drop_pos hs₀ k))) := by
    rw [← h1]; exact hstep
  have h2 : w - tmWeight (K := Ambient F) (s₀.take k) = tmWeight (K := Ambient F) (s₀.drop k) := by
    have h3 := tmWeight_take_add_drop (K := Ambient F) s₀ k
    omega
  rw [h2]
  refine dvd_pred_of_v_eq_exp_mul
    (m := tmWeight (K := Ambient F) (s₀.drop k))
    (y := (ambPiTilde F) ^ (tmWeight (K := Ambient F) (s₀.drop k)))
    (u := b.eval (ambTheta F) * ambInfHom F (ζ_A F
      (suffixExp F (s₀.drop k) (D.drop_pos hs₀ k))))
    (v := evalSeriesGen (tmF (Nat.card F) (ambOmega F) w D.S cf (s₀.take k)) (ambTheta F))
    (hy := ?_) (hu := ?_) (hv := ?_) (hv0 := hf0) (h := hfinal)
  · exact v_ambPiTilde_pow F _
  · obtain ⟨k₁, hk₁⟩ := v_mem_ambK F (eval_mem_ambK F b hbmem) hb0
    obtain ⟨k₂, hk₂⟩ := v_ambInfHom_mem_pred F _ hζ
    refine ⟨k₁ + k₂, ?_⟩
    rw [map_mul, hk₁, hk₂, ← WithZero.exp_add]
    congr 1
    push_cast
    ring
  · exact v_mem_ambK F hfK hf0

end General

end ZagierHoffmanPositiveChar
