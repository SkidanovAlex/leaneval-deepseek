import Submission.ZagierHoffmanProof.TmFShared
import Submission.ZagierHoffmanProof.PiTildeDvd

/-!
# Step 3(a) for a SHARED prefix (Dac §6, Theorem 6.2)

`Step3H.dvd_pred_weight_H` proves the divisibility `(q-1) ∣ (w - w(𝔱))` of Dac §5.3 Step 3 for a
prefix `𝔱` that is **uniquely extendable** inside the datum `D.S`: it evaluates
`f_𝔱(θ) = evalSeriesGen (tmF … 𝔱) θ` with `Step3General.evalSeriesGen_tmF_gen` and then applies the
bridge to the single extender.

For Dac's Theorem 6.2 the prefix `𝔱` may be shared by several tuples of `D.S`.  Then

  `f_𝔱(θ) = ∑_{s ∈ J(𝔱)} (cf s)(θ) · 𝓛(s.drop k)(θ)`,     `J(𝔱) = {s ∈ D.S : s.take k = 𝔱}`

(`TmFShared.evalSeriesGen_tmF_shared`, no uniqueness hypothesis), and the per-tail bridge gives one
identity

  `π̃^m · f_𝔱(θ) = ∑_{s ∈ J(𝔱)} G_s · ambInfHom (ζ_A 𝔰_s)`

with `m = w - w(𝔱)`, `G_s = (∏_j Γ_{s_j})·(cf s)(θ)`.  Since `f_𝔱(θ) ∈ K`, `f_𝔱(θ) ≠ 0` and the
right hand side lies in the image of `ambInfHom`, `PiTildeDvd.dvd_pred_of_piTilde_pow_mul_finset_sum`
yields `(q-1) ∣ m` **directly** — with no case split and no uniqueness hypothesis.

* `sharedG`, `sharedS` — the two total functions above (junk value `0` off `D.S`);
* ★★★ `dvd_pred_weight_H_shared` — the divisibility.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
open Polynomial PowerSeries Finset
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

variable {F : Type*} [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The `Γ`-scaled coefficient `G_s = (∏_j Γ_{s_j})·(cf s)(θ)` of the extender `s` of a prefix,
as a total function (value `0` off `D.S`). -/
noncomputable def sharedG {w : ℕ} (D : MZVDH F w) (k : ℕ)
    (cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F))
    (s : List (ℕ × Polynomial (Ambient F))) : Ambient F :=
  if h : s ∈ D.S then
    (∏ j : Fin (suffixList F (s.drop k)).length,
        ambGammaF F ((suffixExp F (s.drop k) (D.drop_pos h k) j : ℕ))) * (cf s).eval (ambTheta F)
  else 0

/-- The `ζ_A`-value `ambInfHom (ζ_A 𝔰_s)` of the dropped tail of the extender `s` of a prefix,
as a total function (value `0` off `D.S`). -/
noncomputable def sharedS {w : ℕ} (D : MZVDH F w) (k : ℕ)
    (s : List (ℕ × Polynomial (Ambient F))) : Ambient F :=
  if h : s ∈ D.S then ambInfHom F (ζ_A F (suffixExp F (s.drop k) (D.drop_pos h k))) else 0

/-- ★★★ **Step 3's divisibility `(q-1) ∣ w - w(𝔱)` for a SHARED prefix** (Dac §5.3 Step 3, in the
form used in the `𝒯'`-induction of Theorem 6.2).  No uniqueness hypothesis. -/
theorem dvd_pred_weight_H_shared {w : ℕ} (D : MZVDH F w)
    {s₀ : List (ℕ × Polynomial (Ambient F))} (hs₀ : s₀ ∈ D.S) {k : ℕ}
    (hkl : k < s₀.length)
    {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}
    (hfK : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w D.S cf (s₀.take k)) (ambTheta F)
      ∈ ambK F)
    (hf0 : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w D.S cf (s₀.take k)) (ambTheta F)
      ≠ 0)
    (hGmem : ∀ s (hs : s ∈ D.S), s.take k = s₀.take k →
      (∏ j : Fin (suffixList F (s.drop k)).length,
          ambGammaF F ((suffixExp F (s.drop k) (D.drop_pos hs k) j : ℕ)))
        * (cf s).eval (ambTheta F) ∈ ambK F) :
    (Nat.card F - 1) ∣ (w - tmWeight (K := Ambient F) (s₀.take k)) := by
  classical
  by_cases hm0 : w - tmWeight (K := Ambient F) (s₀.take k) = 0
  · rw [hm0]; exact dvd_zero _
  have hmpos : 0 < w - tmWeight (K := Ambient F) (s₀.take k) := Nat.pos_of_ne_zero hm0
  have hlen : (s₀.take k).length = k := by
    rw [List.length_take, Nat.min_eq_left (le_of_lt hkl)]
  have hms : ∀ s (hs : s ∈ D.S), s.take k = s₀.take k →
      tmWeight (K := Ambient F) (s.drop k) = w - tmWeight (K := Ambient F) (s₀.take k) := by
    intro s hs hst
    have h1 : tmWeight (K := Ambient F) s = w := D.weight s hs
    have h2 := tmWeight_take_add_drop (K := Ambient F) s k
    rw [h1, hst] at h2
    omega
  have hne : ∀ s (hs : s ∈ D.S), s.take k = s₀.take k → s.drop k ≠ [] := by
    intro s hs hst hnil
    have h1 := hms s hs hst
    simp only [hnil, tmWeight_nil] at h1
    omega
  have hse : ∀ s ∈ D.S, GSuperEntire ambGamma (tmL (Nat.card F) (ambOmega F) (s.drop k)) :=
    fun s hs => gSuperEntire_tmL_dropH (F := F) D hs k
  have hse' : ∀ s ∈ D.S, GSuperEntire ambGamma
      (tmL (Nat.card F) (ambOmega F) (s.drop (s₀.take k).length)) := by
    intro s hs
    rw [hlen]
    exact hse s hs
  set f := evalSeriesGen (tmF (Nat.card F) (ambOmega F) w D.S cf (s₀.take k)) (ambTheta F)
    with hfdef
  have hII : f = ∑ s ∈ D.S.filter (fun s => s.take k = s₀.take k),
      (cf s).eval (ambTheta F)
        * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (s.drop k)) (ambTheta F) := by
    have h := evalSeriesGen_tmF_shared (F := F) (w := w) (S := D.S) (cf := cf)
      (t := s₀.take k) hse'
    rw [hlen] at h
    rw [hfdef, h, Finset.sum_filter]
  have hbr : ∀ s (hs : s ∈ D.S), s.take k = s₀.take k →
      (ambPiTilde F) ^ (w - tmWeight (K := Ambient F) (s₀.take k))
        * ((cf s).eval (ambTheta F)
          * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (s.drop k)) (ambTheta F))
      = (∏ j : Fin (suffixList F (s.drop k)).length,
          ambGammaF F ((suffixExp F (s.drop k) (D.drop_pos hs k) j : ℕ)))
        * ((cf s).eval (ambTheta F)
          * ambInfHom F (ζ_A F (suffixExp F (s.drop k) (D.drop_pos hs k)))) := by
    intro s hs hst
    have hb := bridgeP_mul F (suffixList F (s.drop k))
      (suffixList_ne_nil F (hne s hs hst))
      (fun j => suffixList_mem_ambH (F := F) (D.drop_entry hs k) _ (List.get_mem _ j))
      (fun j => suffixList_mem_pos F (D.drop_pos hs k) _ (List.get_mem _ j))
      (fun j => suffixList_mem_le_two (F := F) (D.drop_le hs k) _ (List.get_mem _ j))
      (suffixExp F (s.drop k) (D.drop_pos hs k)) (fun j => rfl)
      (fun j => by
        simp only [suffixExp_apply]
        exact suffixList_mem_le_two (F := F) (D.drop_le hs k) _
          (List.get_mem (suffixList F (s.drop k)) (Fin.rev j)))
      (cf s)
    have hsum : (∑ j : Fin (suffixList F (s.drop k)).length,
        (suffixExp F (s.drop k) (D.drop_pos hs k) j : ℕ))
        = w - tmWeight (K := Ambient F) (s₀.take k) := by
      have h1 := suffixList_weight F (s.drop k)
      simp only [suffixExp_apply]
      rw [h1]
      exact hms s hs hst
    rw [hsum] at hb
    exact hb
  have hmain : (ambPiTilde F) ^ (w - tmWeight (K := Ambient F) (s₀.take k)) * f
      = ∑ s ∈ D.S.filter (fun s => s.take k = s₀.take k),
          sharedG D k cf s * sharedS D k s := by
    rw [hII, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    obtain ⟨hsD, hst⟩ := Finset.mem_filter.mp hs
    refine (hbr s hsD hst).trans ?_
    simp only [sharedG, sharedS, dif_pos hsD]
    ring
  exact dvd_pred_of_piTilde_pow_mul_finset_sum (F := F)
    (m := w - tmWeight (K := Ambient F) (s₀.take k)) (a := f)
    (D.S.filter (fun s => s.take k = s₀.take k)) (G := sharedG D k cf) (S := sharedS D k)
    hfK hf0 (fun i hi => by
      obtain ⟨hiD, hik⟩ := Finset.mem_filter.mp hi
      simp only [sharedG, dif_pos hiD]
      exact hGmem i hiD hik)
    (fun i hi => by
      obtain ⟨hiD, -⟩ := Finset.mem_filter.mp hi
      simp only [sharedS, dif_pos hiD]
      exact ⟨ζ_A F (suffixExp F (i.drop k) (D.drop_pos hiD k)), rfl⟩)
    hmain

end ZagierHoffmanPositiveChar
