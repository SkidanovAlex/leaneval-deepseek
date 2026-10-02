import Mathlib
import Submission.Work.ELPull.Defs
import Submission.Work.ELPull.landsN_image
import Submission.Work.ELPull.preimage_localization
import Submission.Work.ELPull.landsN_preimage
import Submission.Work.ELPull.preimage_paramRay
import Submission.Work.ELPull.side_image_eq
import Submission.Work.Top.rayPt_injOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section
open Classical Set Function Filter
open scoped Topology

namespace Work.ELPull

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## 0. Periodicities of the ray points and rays -/

lemma rayPt_add_int' {c : ℂ} (hN : DynB c) (θ t : ℝ) (m : ℤ) :
    hN.rayPt (θ + m) t = hN.rayPt θ t := by
  by_cases ht : 1 < t
  · exact rayPt_periodic hN θ t m ht
  · rw [Work.Top.NakaneData.rayPt, Work.Top.NakaneData.rayPt]; simp [ht]

lemma rayPt_fract' {c : ℂ} (hN : DynB c) (θ t : ℝ) :
    hN.rayPt (Int.fract θ) t = hN.rayPt θ t := by
  by_cases ht : 1 < t
  · exact rayPt_fract_eq hN θ t ht
  · rw [Work.Top.NakaneData.rayPt, Work.Top.NakaneData.rayPt]; simp [ht]

lemma landsN_fract {c : ℂ} (hN : DynB c) (θ : ℝ) (y : ℂ) :
    LandsN hN θ y ↔ LandsN hN (Int.fract θ) y := by
  have hf : (fun t : ℝ => hN.rayPt θ t) = (fun t : ℝ => hN.rayPt (Int.fract θ) t) := by
    funext t; exact (rayPt_fract' hN θ t).symm
  rw [LandsN, LandsN, hf]

lemma landsN_add_int {c : ℂ} (hN : DynB c) (θ : ℝ) (m : ℤ) (y : ℂ) :
    LandsN hN (θ + m) y ↔ LandsN hN θ y := by
  have hf : (fun t : ℝ => hN.rayPt (θ + m) t) = (fun t : ℝ => hN.rayPt θ t) := by
    funext t; exact rayPt_add_int' hN θ t m
  rw [LandsN, LandsN, hf]

lemma paramRay_add_int {c : ℂ} (hN : DynB c) (θ : ℝ) (m : ℤ) :
    hN.paramRay (θ + m) = hN.paramRay θ := by
  ext z
  rw [Work.Top.NakaneData.paramRay_eq_range hN (θ + m),
    Work.Top.NakaneData.paramRay_eq_range hN θ]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨t, (rayPt_add_int' hN θ t.1 m).symm⟩
  · rintro ⟨t, rfl⟩; exact ⟨t, rayPt_add_int' hN θ t.1 m⟩

lemma paramRay_fract {c : ℂ} (hN : DynB c) (θ : ℝ) :
    hN.paramRay (Int.fract θ) = hN.paramRay θ := by
  conv_lhs => rw [Int.fract]
  rw [show θ - (⌊θ⌋ : ℝ) = θ + (-⌊θ⌋ : ℤ) by push_cast; ring]
  exact paramRay_add_int hN θ (-⌊θ⌋)

/-! ## 1. Angle arithmetic of `T` and `preArc` -/

lemma fract_neg_two_fract (a : ℝ) : Int.fract (-2 * Int.fract a) = Int.fract (-2 * a) := by
  have h : -2 * Int.fract a = (-2 * a) + ((2 * ⌊a⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [h, Int.fract_add_intCast]

lemma T_fract (a : ℝ) : T (Int.fract a) = T a := by
  unfold T; rw [fract_neg_two_fract]

lemma T_add_intCast (θ : ℝ) (m : ℤ) : T (θ + m) = T θ := by
  unfold T
  rw [show -2 * (θ + (m:ℝ)) = -2*θ + ((-2*m : ℤ) : ℝ) by push_cast; ring]
  rw [Int.fract_add_intCast]

lemma fin2_cast_int (k : Fin 2) : ∃ m : ℤ, (k : ℝ) = (m : ℝ) :=
  ⟨(k : ℕ), by push_cast; rfl⟩

lemma T_preArc_snd (k : Fin 2) (I : ℝ × ℝ) : T (preArc k I).2 = Int.fract I.1 := by
  obtain ⟨m, hm⟩ := fin2_cast_int k
  rw [preArc, T_fract, T_def, hm]
  have h : -2 * (-I.1 / 2 + (m : ℝ) / 2) = I.1 - (m:ℝ) := by ring
  rw [h, Int.fract_sub_intCast]

lemma T_preArc_fst (k : Fin 2) (I : ℝ × ℝ) : T (preArc k I).1 = Int.fract I.2 := by
  obtain ⟨m, hm⟩ := fin2_cast_int k
  rw [preArc, T_fract, T_def, hm]
  have h : -2 * (-I.2 / 2 + (m : ℝ) / 2) = I.2 - (m:ℝ) := by ring
  rw [h, Int.fract_sub_intCast]

lemma fract_fract_sub (a b : ℝ) : Int.fract (Int.fract a - Int.fract b) = Int.fract (a - b) := by
  have h : Int.fract a - Int.fract b = (a - b) + ((⌊b⌋ - ⌊a⌋ : ℤ) : ℝ) := by
    rw [Int.fract, Int.fract]; push_cast; ring
  rw [h, Int.fract_add_intCast]

lemma InArc_add_int_left (θ a b : ℝ) (m : ℤ) : InArc θ (a + m) b ↔ InArc θ a b := by
  unfold InArc arcLen
  rw [show θ - (a + (m:ℝ)) = (θ - a) + ((-m : ℤ) : ℝ) by push_cast; ring, Int.fract_add_intCast,
      show b - (a + (m:ℝ)) = (b - a) + ((-m : ℤ) : ℝ) by push_cast; ring, Int.fract_add_intCast]

lemma InArc_add_int_right (θ a b : ℝ) (m : ℤ) : InArc θ a (b + m) ↔ InArc θ a b := by
  unfold InArc arcLen
  rw [show b + (m:ℝ) - a = (b - a) + (m:ℤ) by ring, Int.fract_add_intCast]

lemma InArc_add_int_theta (θ a b : ℝ) (m : ℤ) : InArc (θ + m) a b ↔ InArc θ a b := by
  unfold InArc arcLen
  rw [show θ + (m:ℝ) - a = (θ - a) + (m:ℤ) by ring, Int.fract_add_intCast]

lemma InArc_fract (θ a b : ℝ) : InArc θ a b ↔ InArc (Int.fract θ) (Int.fract a) (Int.fract b) := by
  unfold InArc arcLen
  rw [(fract_fract_sub θ a).symm, (fract_fract_sub b a).symm]

lemma InArc_congr {θ θ' a a' b b' : ℝ}
    (hθ : ∃ m : ℤ, θ = θ' + m) (ha : ∃ m : ℤ, a = a' + m) (hb : ∃ m : ℤ, b = b' + m) :
    InArc θ a b ↔ InArc θ' a' b' := by
  obtain ⟨m, hm⟩ := hθ; obtain ⟨n, hn⟩ := ha; obtain ⟨l, hl⟩ := hb
  rw [InArc_fract θ a b, InArc_fract θ' a' b']
  rw [hm, hn, hl, Int.fract_add_intCast, Int.fract_add_intCast, Int.fract_add_intCast]

lemma arcSide_add_int_right {c : ℂ} (hN : DynB c) (P : CoPair hN) (p q : ℝ) (m : ℤ) :
    arcSide hN P p (q + m) = arcSide hN P p q := by
  unfold arcSide arcLen
  rw [show q + (m:ℝ) - p = (q - p) + ((m:ℤ):ℝ) by push_cast; ring, Int.fract_add_intCast]

lemma arcSide_add_int_left {c : ℂ} (hN : DynB c) (P : CoPair hN) (p q : ℝ) (m : ℤ) :
    arcSide hN P (p + m) q = arcSide hN P p q := by
  have hpt : hN.rayPt ((p + (m:ℝ)) + Int.fract (q - (p + (m:ℝ))) / 2) 2
      = hN.rayPt (p + Int.fract (q - p) / 2) 2 := by
    rw [show q - (p + (m:ℝ)) = (q - p) + (((-m:ℤ)):ℝ) by push_cast; ring, Int.fract_add_intCast]
    rw [show p + (m:ℝ) + Int.fract (q - p) / 2 = (p + Int.fract (q - p) / 2) + ((m:ℤ):ℝ) by push_cast; ring]
    exact rayPt_add_int' hN _ 2 m
  unfold arcSide arcLen
  rw [hpt]

/-! ## 2. The two preimages of a regular value -/

lemma fiber_neg {c y : ℂ} (hy : y ≠ c) :
    ∃ u : ℂ, Tantibar c u = y ∧ Tantibar c (-u) = y ∧ u ≠ 0 ∧
      (∀ z : ℂ, Tantibar c z = y → z = u ∨ z = -u) := by
  obtain ⟨u, v, hu, hv, huv, hall, -⟩ :=
    preimage_localization hy (show (0:ℝ) < 1 by norm_num)
  have hneg : v = -u := by
    have hsq : (starRingEnd ℂ u)^2 = (starRingEnd ℂ v)^2 := by
      have h1 : Tantibar c u = Tantibar c v := by rw [hu, hv]
      simp only [Tantibar] at h1
      linear_combination h1
    have hfac : ((starRingEnd ℂ u) - (starRingEnd ℂ v)) *
        ((starRingEnd ℂ u) + (starRingEnd ℂ v)) = 0 := by
      have : ((starRingEnd ℂ u) - (starRingEnd ℂ v)) * ((starRingEnd ℂ u) + (starRingEnd ℂ v))
          = (starRingEnd ℂ u)^2 - (starRingEnd ℂ v)^2 := by ring
      rw [this, hsq, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exfalso
      have h' : u = v := by
        have := congrArg (starRingEnd ℂ) (sub_eq_zero.mp h)
        simpa using this
      exact huv h'
    · have h' : u = -v := by
        have := congrArg (starRingEnd ℂ) (add_eq_zero_iff_eq_neg.mp h)
        simpa using this
      rw [h']; ring
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · rw [← hneg]; exact hv
  · intro h0
    exact huv (by rw [hneg, h0]; ring)
  · intro z hz; rcases hall z hz with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h, hneg])

lemma mem_K_of_mem_mandelbar {c : ℂ} (hc : c ∈ Mandelbar) : c ∈ K c := by
  obtain ⟨M, hM⟩ := hc
  refine ⟨M, fun n => ?_⟩
  show ‖(Tantibar c)^[n] c‖ ≤ M
  have hstep : (Tantibar c)^[n] c = (Tantibar c)^[n+1] 0 :=
    (congrArg (fun x => (Tantibar c)^[n] x)
      (show c = (Tantibar c) 0 by simp [Tantibar])).trans
      (Function.iterate_succ_apply (Tantibar c) n 0).symm
  rw [hstep]
  exact hM (n+1)

/-! ## 3. The image of a ray, and the two rays above a ray -/

lemma image_paramRay_subset {c : ℂ} (hN : DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c)) (θ : ℝ) :
    Tantibar c '' hN.paramRay θ ⊆ hN.paramRay (T θ) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Work.Top.NakaneData.paramRay_eq_range] at hz ⊢
  obtain ⟨t, rfl⟩ := hz
  exact ⟨⟨t.1 ^ 2, by nlinarith [t.2]⟩, rayPt_Tantibar hN hφ t.2⟩

lemma fract_pos_of_ne_zero {x : ℝ} (h : Int.fract x ≠ 0) : 0 < Int.fract x :=
  lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm h)

lemma fract_half : Int.fract (1/2 : ℝ) = 1/2 :=
  Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

/-! ## 4. The two preimage rays of an arc are negatives at every level -/

/-- The two preimage angles `(preArc 0 I).2 = fract (-I.1/2)`, `(preArc 1 I).2 = fract (-I.1/2+1/2)`
are distinct (they differ by `1/2` modulo `1`). -/
lemma preArc_snd_ne (I : ℝ × ℝ) : (preArc 1 I).2 ≠ (preArc 0 I).2 := by
  intro h
  have e1 : (preArc 1 I).2 = Int.fract (-I.1/2 + 1/2) := by norm_num [preArc]
  have e0 : (preArc 0 I).2 = Int.fract (-I.1/2) := by norm_num [preArc]
  have h1 : Int.fract ((preArc 1 I).2 - (preArc 0 I).2) = 1/2 := by
    rw [e1, e0, fract_fract_sub, show -I.1/2 + 1/2 - -I.1/2 = (1/2 : ℝ) by ring, fract_half]
  rw [h, sub_self, Int.fract_zero] at h1
  norm_num at h1

lemma preArc_fst_ne (I : ℝ × ℝ) : (preArc 1 I).1 ≠ (preArc 0 I).1 := by
  intro h
  have e1 : (preArc 1 I).1 = Int.fract (-I.2/2 + 1/2) := by norm_num [preArc]
  have e0 : (preArc 0 I).1 = Int.fract (-I.2/2) := by norm_num [preArc]
  have h1 : Int.fract ((preArc 1 I).1 - (preArc 0 I).1) = 1/2 := by
    rw [e1, e0, fract_fract_sub, show -I.2/2 + 1/2 - -I.2/2 = (1/2 : ℝ) by ring, fract_half]
  rw [h, sub_self, Int.fract_zero] at h1
  norm_num at h1

/-- At every level `t > 1` the ray points of the two angles above `I.1` are opposite. -/
lemma rayPt_preArc_snd_neg {c : ℂ} (hN : DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c)) (hcK : c ∈ K c)
    (I : ℝ × ℝ) {t : ℝ} (ht : 1 < t) :
    hN.rayPt (preArc 1 I).2 t = - hN.rayPt (preArc 0 I).2 t := by
  set m : ℂ := hN.rayPt (Int.fract I.1) (t^2) with hm
  have ht2 : 1 < t^2 := by nlinarith
  have hmK : m ∉ K c := hN.rayPt_notMem ht2
  have hmc : m ≠ c := fun h => hmK (h ▸ hcK)
  obtain ⟨uu, hu1, hu2, hu0, hall⟩ := fiber_neg hmc
  have hz0 : hN.rayPt (preArc 0 I).2 t = uu ∨ hN.rayPt (preArc 0 I).2 t = -uu := by
    apply hall
    rw [← rayPt_Tantibar hN hφ ht, T_preArc_snd]
  have hz1 : hN.rayPt (preArc 1 I).2 t = uu ∨ hN.rayPt (preArc 1 I).2 t = -uu := by
    apply hall
    rw [← rayPt_Tantibar hN hφ ht, T_preArc_snd]
  have hne' : hN.rayPt (preArc 1 I).2 t ≠ hN.rayPt (preArc 0 I).2 t := by
    intro h
    have h01 : (preArc 1 I).2 = (preArc 0 I).2 :=
      (Work.Top.rayPt_injOn hN (Int.fract_nonneg _) (Int.fract_lt_one _)
        (Int.fract_nonneg _) (Int.fract_lt_one _) ht ht h).1
    exact preArc_snd_ne I h01
  rcases hz0 with h0 | h0 <;> rcases hz1 with h1 | h1
  · exact absurd (by rw [h0, h1]) hne'
  · rw [h1, h0]
  · rw [h0, h1]; ring
  · exact absurd (by rw [h0, h1]) hne'

/-- At every level `t > 1` the ray points of the two angles above `I.2` are opposite. -/
lemma rayPt_preArc_fst_neg {c : ℂ} (hN : DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c)) (hcK : c ∈ K c)
    (I : ℝ × ℝ) {t : ℝ} (ht : 1 < t) :
    hN.rayPt (preArc 1 I).1 t = - hN.rayPt (preArc 0 I).1 t := by
  set m : ℂ := hN.rayPt (Int.fract I.2) (t^2) with hm
  have ht2 : 1 < t^2 := by nlinarith
  have hmK : m ∉ K c := hN.rayPt_notMem ht2
  have hmc : m ≠ c := fun h => hmK (h ▸ hcK)
  obtain ⟨uu, hu1, hu2, hu0, hall⟩ := fiber_neg hmc
  have hz0 : hN.rayPt (preArc 0 I).1 t = uu ∨ hN.rayPt (preArc 0 I).1 t = -uu := by
    apply hall
    rw [← rayPt_Tantibar hN hφ ht, T_preArc_fst]
  have hz1 : hN.rayPt (preArc 1 I).1 t = uu ∨ hN.rayPt (preArc 1 I).1 t = -uu := by
    apply hall
    rw [← rayPt_Tantibar hN hφ ht, T_preArc_fst]
  have hne' : hN.rayPt (preArc 1 I).1 t ≠ hN.rayPt (preArc 0 I).1 t := by
    intro h
    have h01 : (preArc 1 I).1 = (preArc 0 I).1 :=
      (Work.Top.rayPt_injOn hN (Int.fract_nonneg _) (Int.fract_lt_one _)
        (Int.fract_nonneg _) (Int.fract_lt_one _) ht ht h).1
    exact preArc_fst_ne I h01
  rcases hz0 with h0 | h0 <;> rcases hz1 with h1 | h1
  · exact absurd (by rw [h0, h1]) hne'
  · rw [h1, h0]
  · rw [h0, h1]; ring
  · exact absurd (by rw [h0, h1]) hne'

/-! ## 5. The two angles of an unwrapped arc of a pair -/

lemma arcLen_swap_ne_zero {c : ℂ} {hN : DynB c} {P : CoPair hN}
    (hab : arcLen P.a P.b ≠ 0) : arcLen P.b P.a ≠ 0 := by
  unfold arcLen at hab ⊢
  rw [show P.a - P.b = -(P.b - P.a) by ring, Int.fract_neg hab]
  intro h
  have := Int.fract_lt_one (P.b - P.a)
  linarith

lemma unwrapped_arc_pos {c : ℂ} {hN : DynB c} {Q : CoPair hN} {I : ℝ × ℝ}
    (hab : arcLen Q.a Q.b ≠ 0) (hI : IsUnwrappedArcOf Q I) :
    0 < I.2 - I.1 ∧ I.2 - I.1 < 1 := by
  rcases hI with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, show Q.a + arcLen Q.a Q.b - Q.a = arcLen Q.a Q.b by ring]
    exact ⟨fract_pos_of_ne_zero hab, Int.fract_lt_one _⟩
  · rw [h1, h2, show Q.b + arcLen Q.b Q.a - Q.b = arcLen Q.b Q.a by ring]
    exact ⟨fract_pos_of_ne_zero (arcLen_swap_ne_zero hab), Int.fract_lt_one _⟩

/-! ## 6. Landing points lie in the filled Julia set -/

lemma landsN_mem_K {c : ℂ} (hN : DynB c) {θ : ℝ} {y : ℂ} (h : LandsN hN θ y) : y ∈ K c := by
  have hpot : (fun t : ℝ => Work.Top.potential (K c) (Work.ParamRays.dynPhi c) (hN.rayPt θ t))
      =ᶠ[nhdsWithin (1:ℝ) (Set.Ioi 1)] Real.log := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact Work.Top.NakaneData.potential_rayPt hN ht
  have hlog : Tendsto Real.log (nhdsWithin (1:ℝ) (Set.Ioi 1)) (nhds 0) := by
    have h := (Real.continuousAt_log one_ne_zero).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 1))
    simpa using h
  have h2 := hlog.congr' hpot.symm
  have h1 : Tendsto (fun t : ℝ => Work.Top.potential (K c) (Work.ParamRays.dynPhi c) (hN.rayPt θ t))
      (nhdsWithin (1:ℝ) (Set.Ioi 1))
      (nhds (Work.Top.potential (K c) (Work.ParamRays.dynPhi c) y)) := by
    have hc := hN.continuous_potential.continuousAt.tendsto.comp h
    simpa only [Function.comp_def] using hc
  have hy0 : Work.Top.potential (K c) (Work.ParamRays.dynPhi c) y = 0 :=
    tendsto_nhds_unique h1 h2
  exact (Work.Top.NakaneData.potential_eq_zero_iff hN y).mp hy0

/-! ## 7. Sides -/

lemma arcSide_subset {c : ℂ} (hN : DynB c) (P : CoPair hN) (p q : ℝ) :
    arcSide hN P p q ⊆ (pairCurve hN P)ᶜ := connectedComponentIn_subset _ _

lemma isOpen_arcSide {c : ℂ} (hN : DynB c) (htop : PB1Top hN) (P : CoPair hN) (p q : ℝ) :
    IsOpen (arcSide hN P p q) :=
  (htop.closed P).isOpen_compl.connectedComponentIn

/-! ## 8. Angle data of the four preimage arcs -/

lemma preArc_lift_snd (k : Fin 2) (I : ℝ × ℝ) :
    (preArc k I).2 = Int.fract (-I.1/2 + (k:ℝ)/2) := rfl

lemma preArc_lift_fst (k : Fin 2) (I : ℝ × ℝ) :
    (preArc k I).1 = Int.fract (-I.2/2 + (k:ℝ)/2) := rfl

lemma InArc_lift (x y z : ℝ) :
    InArc (Int.fract x) (Int.fract y) (Int.fract z) ↔ InArc x y z :=
  (InArc_fract x y z).symm

lemma fract_half_sub_half {g : ℝ} (h0 : 0 < g) (h1 : g < 1) :
    Int.fract (g/2 - 1/2) = g/2 + 1/2 := by
  rw [show g/2 - 1/2 = (g/2 + 1/2) + ((-1:ℤ):ℝ) by ring, Int.fract_add_intCast,
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]

lemma fract_half_pos {g : ℝ} (h0 : 0 < g) (h1 : g < 1) :
    Int.fract (g/2) = g/2 :=
  Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩

lemma fract_neg_half : Int.fract (-(1/2) : ℝ) = 1/2 := by
  rw [Int.fract_neg (by rw [fract_half]; norm_num), fract_half]; norm_num

lemma InArc_A1B1A0 (I : ℝ × ℝ) (h0 : 0 < I.2 - I.1) (h1 : I.2 - I.1 < 1) :
    InArc (preArc 1 I).2 (preArc 1 I).1 (preArc 0 I).2 := by
  have e1 : (preArc 1 I).2 = Int.fract (-I.1/2 + 1/2) := by norm_num [preArc]
  have e2 : (preArc 1 I).1 = Int.fract (-I.2/2 + 1/2) := by norm_num [preArc]
  have e3 : (preArc 0 I).2 = Int.fract (-I.1/2) := by norm_num [preArc]
  rw [e1, e2, e3, InArc_lift]
  have hh : (-I.1/2 + 1/2) - (-I.2/2 + 1/2) = (I.2 - I.1)/2 := by ring
  have hh2 : (-I.1/2) - (-I.2/2 + 1/2) = (I.2 - I.1)/2 - 1/2 := by ring
  unfold InArc arcLen
  rw [hh, hh2, fract_half_pos h0 h1, fract_half_sub_half h0 h1]
  constructor <;> linarith

lemma InArc_B0B1A0 (I : ℝ × ℝ) (h0 : 0 < I.2 - I.1) (h1 : I.2 - I.1 < 1) :
    InArc (preArc 0 I).1 (preArc 1 I).1 (preArc 0 I).2 := by
  have e1 : (preArc 0 I).1 = Int.fract (-I.2/2) := by norm_num [preArc]
  have e2 : (preArc 1 I).1 = Int.fract (-I.2/2 + 1/2) := by norm_num [preArc]
  have e3 : (preArc 0 I).2 = Int.fract (-I.1/2) := by norm_num [preArc]
  rw [e1, e2, e3, InArc_lift]
  have hh : (-I.2/2) - (-I.2/2 + 1/2) = -(1/2:ℝ) := by ring
  have hh2 : (-I.1/2) - (-I.2/2 + 1/2) = (I.2 - I.1)/2 - 1/2 := by ring
  unfold InArc arcLen
  rw [hh, hh2, fract_neg_half, fract_half_sub_half h0 h1]
  constructor <;> linarith

lemma InArc_A0B0A1 (I : ℝ × ℝ) (h0 : 0 < I.2 - I.1) (h1 : I.2 - I.1 < 1) :
    InArc (preArc 0 I).2 (preArc 0 I).1 (preArc 1 I).2 := by
  have e1 : (preArc 0 I).2 = Int.fract (-I.1/2) := by norm_num [preArc]
  have e2 : (preArc 0 I).1 = Int.fract (-I.2/2) := by norm_num [preArc]
  have e3 : (preArc 1 I).2 = Int.fract (-I.1/2 + 1/2) := by norm_num [preArc]
  rw [e1, e2, e3, InArc_lift]
  have hh : (-I.1/2) - (-I.2/2) = (I.2 - I.1)/2 := by ring
  have hh2 : (-I.1/2 + 1/2) - (-I.2/2) = (I.2 - I.1)/2 + 1/2 := by ring
  have e4 : Int.fract ((I.2-I.1)/2 + 1/2) = (I.2-I.1)/2 + 1/2 := by
    rw [Int.fract_eq_self]; constructor <;> linarith
  unfold InArc arcLen
  rw [hh, hh2, fract_half_pos h0 h1, e4]
  constructor <;> linarith

lemma InArc_B1B0A1 (I : ℝ × ℝ) (h0 : 0 < I.2 - I.1) (h1 : I.2 - I.1 < 1) :
    InArc (preArc 1 I).1 (preArc 0 I).1 (preArc 1 I).2 := by
  have e1 : (preArc 1 I).1 = Int.fract (-I.2/2 + 1/2) := by norm_num [preArc]
  have e2 : (preArc 0 I).1 = Int.fract (-I.2/2) := by norm_num [preArc]
  have e3 : (preArc 1 I).2 = Int.fract (-I.1/2 + 1/2) := by norm_num [preArc]
  rw [e1, e2, e3, InArc_lift]
  have hh : (-I.2/2 + 1/2) - (-I.2/2) = (1/2:ℝ) := by ring
  have hh2 : (-I.1/2 + 1/2) - (-I.2/2) = (I.2 - I.1)/2 + 1/2 := by ring
  have e4 : Int.fract ((I.2-I.1)/2 + 1/2) = (I.2-I.1)/2 + 1/2 := by
    rw [Int.fract_eq_self]; constructor <;> linarith
  unfold InArc arcLen
  rw [hh, hh2, fract_half, e4]
  constructor <;> linarith

lemma arcLen_A0B1 (I : ℝ × ℝ) (h0 : 0 < I.2 - I.1) (h1 : I.2 - I.1 < 1) :
    arcLen (preArc 0 I).2 (preArc 1 I).1 = (1 - (I.2 - I.1))/2 := by
  have e1 : (preArc 0 I).2 = Int.fract (-I.1/2) := by norm_num [preArc]
  have e2 : (preArc 1 I).1 = Int.fract (-I.2/2 + 1/2) := by norm_num [preArc]
  unfold arcLen
  rw [e1, e2, fract_fract_sub]
  rw [show (-I.2/2 + 1/2) - (-I.1/2) = (I.1 - I.2)/2 + 1/2 by ring]
  rw [show (I.1 - I.2)/2 + 1/2 = ((1 - (I.2 - I.1))/2 : ℝ) by ring]
  exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩

lemma arcLen_A1B0 (I : ℝ × ℝ) (h0 : 0 < I.2 - I.1) (h1 : I.2 - I.1 < 1) :
    arcLen (preArc 1 I).2 (preArc 0 I).1 = (1 - (I.2 - I.1))/2 := by
  have e1 : (preArc 1 I).2 = Int.fract (-I.1/2 + 1/2) := by norm_num [preArc]
  have e2 : (preArc 0 I).1 = Int.fract (-I.2/2) := by norm_num [preArc]
  unfold arcLen
  rw [e1, e2, fract_fract_sub]
  rw [show (-I.2/2) - (-I.1/2 + 1/2) = (I.1 - I.2)/2 - 1/2 by ring]
  rw [show (I.1 - I.2)/2 - 1/2 = ((1 - (I.2 - I.1))/2) + ((-1:ℤ):ℝ) by push_cast; ring]
  rw [Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩

/-- The preimage arcs: the four angles `A_k = (preArc k I).2` and `B_k = (preArc k I).1`. -/

lemma InArc_mid0 (I : ℝ × ℝ) (h0 : 0 < I.2 - I.1) (h1 : I.2 - I.1 < 1) :
    InArc ((preArc 0 I).2 + arcLen (preArc 0 I).2 (preArc 1 I).1 / 2)
      (preArc 0 I).2 (preArc 1 I).1 := by
  have harc := arcLen_A0B1 I h0 h1
  have hfac : Int.fract (((preArc 0 I).2 + arcLen (preArc 0 I).2 (preArc 1 I).1 / 2)
      - (preArc 0 I).2) = (1 - (I.2 - I.1))/4 := by
    rw [show (preArc 0 I).2 + arcLen (preArc 0 I).2 (preArc 1 I).1 / 2 - (preArc 0 I).2
        = arcLen (preArc 0 I).2 (preArc 1 I).1 / 2 by ring, harc]
    rw [show (1 - (I.2 - I.1))/2/2 = ((1 - (I.2 - I.1))/4 : ℝ) by ring]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  unfold InArc
  rw [hfac, harc]
  constructor <;> linarith

lemma InArc_mid1 (I : ℝ × ℝ) (h0 : 0 < I.2 - I.1) (h1 : I.2 - I.1 < 1) :
    InArc ((preArc 1 I).2 + arcLen (preArc 1 I).2 (preArc 0 I).1 / 2)
      (preArc 1 I).2 (preArc 0 I).1 := by
  have harc := arcLen_A1B0 I h0 h1
  have hfac : Int.fract (((preArc 1 I).2 + arcLen (preArc 1 I).2 (preArc 0 I).1 / 2)
      - (preArc 1 I).2) = (1 - (I.2 - I.1))/4 := by
    rw [show (preArc 1 I).2 + arcLen (preArc 1 I).2 (preArc 0 I).1 / 2 - (preArc 1 I).2
        = arcLen (preArc 1 I).2 (preArc 0 I).1 / 2 by ring, harc]
    rw [show (1 - (I.2 - I.1))/2/2 = ((1 - (I.2 - I.1))/4 : ℝ) by ring]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  unfold InArc
  rw [hfac, harc]
  constructor <;> linarith

-- The three transformed arc-memberships for the *opposite* side of `G_0` and `G_1`.

/-- `mid_0` lies in the arc `(B_0, A_1)`. -/
lemma InArc_mid0_other (I : ℝ × ℝ) (h0 : 0 < I.2 - I.1) (h1 : I.2 - I.1 < 1) :
    InArc ((preArc 0 I).2 + arcLen (preArc 0 I).2 (preArc 1 I).1 / 2)
      (preArc 0 I).1 (preArc 1 I).2 := by
  have harc : arcLen (preArc 0 I).2 (preArc 1 I).1 = (1 - (I.2 - I.1))/2 := arcLen_A0B1 I h0 h1
  set g := I.2 - I.1 with hg
  have e1 : (preArc 0 I).2 = Int.fract (-I.1/2) := by norm_num [preArc]
  have e2 : (preArc 0 I).1 = Int.fract (-I.2/2) := by norm_num [preArc]
  have e3 : (preArc 1 I).2 = Int.fract (-I.1/2 + 1/2) := by norm_num [preArc]
  have hmid : (preArc 0 I).2 + arcLen (preArc 0 I).2 (preArc 1 I).1 / 2
      = (-I.1/2 + (1 - g)/4) + (-⌊-I.1/2⌋ : ℤ) := by
    rw [harc, e1, Int.fract]; push_cast; ring
  have ha : ∃ m : ℤ, (preArc 0 I).1 = (-I.2/2) + m :=
    ⟨-⌊-I.2/2⌋, by rw [e2, Int.fract]; push_cast; ring⟩
  have hb : ∃ m : ℤ, (preArc 1 I).2 = (-I.1/2 + 1/2) + m :=
    ⟨-⌊-I.1/2 + 1/2⌋, by rw [e3, Int.fract]; push_cast; ring⟩
  refine (InArc_congr ⟨_, hmid⟩ ha hb).mpr ?_
  have hh : (-I.1/2 + (1-g)/4) - (-I.2/2) = (1 + g)/4 := by rw [hg]; ring
  have hh2 : (-I.1/2 + 1/2) - (-I.2/2) = (1 + g)/2 := by rw [hg]; ring
  unfold InArc arcLen
  rw [hh, hh2]
  have e4 : Int.fract ((1+g)/4) = (1+g)/4 := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have e5 : Int.fract ((1+g)/2) = (1+g)/2 := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [e4, e5]
  constructor <;> linarith

/-- `mid_1` lies in the arc `(B_1, A_0)`. -/
lemma InArc_mid1_other (I : ℝ × ℝ) (h0 : 0 < I.2 - I.1) (h1 : I.2 - I.1 < 1) :
    InArc ((preArc 1 I).2 + arcLen (preArc 1 I).2 (preArc 0 I).1 / 2)
      (preArc 1 I).1 (preArc 0 I).2 := by
  have harc : arcLen (preArc 1 I).2 (preArc 0 I).1 = (1 - (I.2 - I.1))/2 := arcLen_A1B0 I h0 h1
  set g := I.2 - I.1 with hg
  have e1 : (preArc 1 I).2 = Int.fract (-I.1/2 + 1/2) := by norm_num [preArc]
  have e2 : (preArc 1 I).1 = Int.fract (-I.2/2 + 1/2) := by norm_num [preArc]
  have e3 : (preArc 0 I).2 = Int.fract (-I.1/2) := by norm_num [preArc]
  have hmid : (preArc 1 I).2 + arcLen (preArc 1 I).2 (preArc 0 I).1 / 2
      = (-I.1/2 + 1/2 + (1 - g)/4) + (-⌊-I.1/2 + 1/2⌋ : ℤ) := by
    rw [harc, e1, Int.fract]; push_cast; ring
  have ha : ∃ m : ℤ, (preArc 1 I).1 = (-I.2/2 + 1/2) + m :=
    ⟨-⌊-I.2/2 + 1/2⌋, by rw [e2, Int.fract]; push_cast; ring⟩
  have hb : ∃ m : ℤ, (preArc 0 I).2 = (-I.1/2) + m :=
    ⟨-⌊-I.1/2⌋, by rw [e3, Int.fract]; push_cast; ring⟩
  refine (InArc_congr ⟨_, hmid⟩ ha hb).mpr ?_
  have hh : (-I.1/2 + 1/2 + (1-g)/4) - (-I.2/2 + 1/2) = (1 + g)/4 := by rw [hg]; ring
  have hh2 : (-I.1/2) - (-I.2/2 + 1/2) = (1 + g)/2 - 1 := by rw [hg]; ring
  unfold InArc arcLen
  rw [hh, hh2]
  have e4 : Int.fract ((1+g)/4) = (1+g)/4 := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have e5 : Int.fract ((1+g)/2 - 1) = (1+g)/2 := by
    rw [show (1+g)/2 - 1 = ((1+g)/2) + ((-1:ℤ):ℝ) by ring, Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [e4, e5]
  constructor <;> linarith


lemma fract_fract_sub' (a b : ℝ) : Int.fract (Int.fract a - b) = Int.fract (a - b) := by
  have h : Int.fract a - b = (a - b) + ((-⌊a⌋ : ℤ):ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [h, Int.fract_add_intCast]

lemma rayPt_mem_paramRay {c : ℂ} (hN : DynB c) (θ : ℝ) {t : ℝ} (ht : 1 < t) :
    hN.rayPt θ t ∈ hN.paramRay θ :=
  ⟨hN.rayPt_notMem ht, t, ht, hN.Phi_rayPt ht⟩

lemma paramRay_I1_subset_pairCurve {c : ℂ} (hN : DynB c) {Q : CoPair hN} {I : ℝ × ℝ}
    (hI : IsUnwrappedArcOf Q I) : hN.paramRay I.1 ⊆ pairCurve hN Q := by
  rcases hI with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1]
    intro z hz
    exact Or.inl (Or.inl hz)
  · rw [h1]
    intro z hz
    exact Or.inr hz

lemma paramRay_I2_subset_pairCurve {c : ℂ} (hN : DynB c) {Q : CoPair hN} {I : ℝ × ℝ}
    (hI : IsUnwrappedArcOf Q I) : hN.paramRay I.2 ⊆ pairCurve hN Q := by
  rcases hI with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2]
    have hm : Q.a + arcLen Q.a Q.b = Q.b + ((-⌊Q.b - Q.a⌋ : ℤ):ℝ) := by
      unfold arcLen; rw [Int.fract]; push_cast; ring
    rw [hm, paramRay_add_int hN Q.b (-⌊Q.b - Q.a⌋)]
    intro z hz
    exact Or.inr hz
  · rw [h2]
    have hm : Q.b + arcLen Q.b Q.a = Q.a + ((-⌊Q.a - Q.b⌋ : ℤ):ℝ) := by
      unfold arcLen; rw [Int.fract]; push_cast; ring
    rw [hm, paramRay_add_int hN Q.a (-⌊Q.a - Q.b⌋)]
    intro z hz
    exact Or.inl (Or.inl hz)

lemma pairCurve_eq_I {c : ℂ} (hN : DynB c) {Q : CoPair hN} {I : ℝ × ℝ}
    (hI : IsUnwrappedArcOf Q I) :
    pairCurve hN Q = hN.paramRay I.1 ∪ {Q.y} ∪ hN.paramRay I.2 := by
  rcases hI with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    have hm : Q.a + arcLen Q.a Q.b = Q.b + ((-⌊Q.b - Q.a⌋ : ℤ):ℝ) := by
      unfold arcLen; rw [Int.fract]; push_cast; ring
    rw [hm, paramRay_add_int hN Q.b (-⌊Q.b - Q.a⌋)]
    rfl
  · rw [h1, h2]
    have hm : Q.b + arcLen Q.b Q.a = Q.a + ((-⌊Q.a - Q.b⌋ : ℤ):ℝ) := by
      unfold arcLen; rw [Int.fract]; push_cast; ring
    rw [hm, paramRay_add_int hN Q.a (-⌊Q.a - Q.b⌋)]
    ext z; simp only [pairCurve, Set.mem_union, Set.mem_singleton_iff]; tauto

lemma InArc_Tmid0_I (I : ℝ × ℝ) (h0 : 0 < I.2 - I.1) (h1 : I.2 - I.1 < 1) :
    InArc (T ((preArc 0 I).2 + arcLen (preArc 0 I).2 (preArc 1 I).1 / 2)) I.2 I.1 := by
  set g := I.2 - I.1 with hg
  have harc : arcLen (preArc 0 I).2 (preArc 1 I).1 = (1-g)/2 := arcLen_A0B1 I h0 h1
  have e1 : (preArc 0 I).2 = Int.fract (-I.1/2) := by norm_num [preArc]
  have hmid : (preArc 0 I).2 + arcLen (preArc 0 I).2 (preArc 1 I).1 / 2
      = (-I.1/2 + (1-g)/4) + (-⌊-I.1/2⌋ : ℤ) := by
    rw [harc, e1, Int.fract]; push_cast; ring
  have hTm : T ((preArc 0 I).2 + arcLen (preArc 0 I).2 (preArc 1 I).1 / 2)
      = Int.fract (I.1 - (1-g)/2) := by
    unfold T
    rw [hmid]
    rw [show -2 * ((-I.1/2 + (1-g)/4) + (-⌊-I.1/2⌋ : ℤ))
        = (I.1 - (1-g)/2) + (2 * ⌊-I.1/2⌋ : ℤ) by push_cast; ring]
    rw [Int.fract_add_intCast]
  have hh : (I.1 - (1-g)/2) - I.2 = -(1+g)/2 := by rw [hg]; ring
  have hh2 : I.1 - I.2 = -g := by rw [hg]; ring
  rw [hTm]
  unfold InArc arcLen
  rw [fract_fract_sub', hh, hh2]
  have e4 : Int.fract (-(1+g)/2) = (1-g)/2 := by
    rw [show -(1+g)/2 = ((1-g)/2) + ((-1:ℤ):ℝ) by ring, Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have e5 : Int.fract (-g) = 1 - g := by
    rw [show -g = (1-g) + ((-1:ℤ):ℝ) by ring, Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [e4, e5]
  constructor <;> linarith

lemma InArc_Tmid1_I (I : ℝ × ℝ) (h0 : 0 < I.2 - I.1) (h1 : I.2 - I.1 < 1) :
    InArc (T ((preArc 1 I).2 + arcLen (preArc 1 I).2 (preArc 0 I).1 / 2)) I.2 I.1 := by
  set g := I.2 - I.1 with hg
  have harc : arcLen (preArc 1 I).2 (preArc 0 I).1 = (1-g)/2 := arcLen_A1B0 I h0 h1
  have e1 : (preArc 1 I).2 = Int.fract (-I.1/2 + 1/2) := by norm_num [preArc]
  have hmid : (preArc 1 I).2 + arcLen (preArc 1 I).2 (preArc 0 I).1 / 2
      = (-I.1/2 + 1/2 + (1-g)/4) + (-⌊-I.1/2 + 1/2⌋ : ℤ) := by
    rw [harc, e1, Int.fract]; push_cast; ring
  have hTm : T ((preArc 1 I).2 + arcLen (preArc 1 I).2 (preArc 0 I).1 / 2)
      = Int.fract (I.1 - (1-g)/2) := by
    unfold T
    rw [hmid]
    rw [show -2 * ((-I.1/2 + 1/2 + (1-g)/4) + (-⌊-I.1/2 + 1/2⌋ : ℤ))
        = (I.1 - (1-g)/2) + (2 * ⌊-I.1/2 + 1/2⌋ - 1 : ℤ) by push_cast; ring]
    rw [Int.fract_add_intCast]
  have hh : (I.1 - (1-g)/2) - I.2 = -(1+g)/2 := by rw [hg]; ring
  have hh2 : I.1 - I.2 = -g := by rw [hg]; ring
  rw [hTm]
  unfold InArc arcLen
  rw [fract_fract_sub', hh, hh2]
  have e4 : Int.fract (-(1+g)/2) = (1-g)/2 := by
    rw [show -(1+g)/2 = ((1-g)/2) + ((-1:ℤ):ℝ) by ring, Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have e5 : Int.fract (-g) = 1 - g := by
    rw [show -g = (1-g) + ((-1:ℤ):ℝ) by ring, Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [e4, e5]
  constructor <;> linarith

theorem pb1Top {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) (hN : DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c)) (htop : PB1Top hN)
    (Q : CoPair hN) (hab : arcLen Q.a Q.b ≠ 0) (I : ℝ × ℝ) (hI : IsUnwrappedArcOf Q I)
    (hcv : c ∈ arcSide hN Q I.2 I.1) (k : Fin 2) :
    ∃ y' : ℂ, LeanEval.ComplexAnalysis.Tantibar c y' = Q.y ∧
      LandsN hN (preArc k I).1 y' ∧ LandsN hN (preArc k I).2 y' := by
  have hcK : c ∈ K c := mem_K_of_mem_mandelbar hc
  obtain ⟨hIp, hIq⟩ := unwrapped_arc_pos hab hI
  have hQc : Q.y ≠ c := by
    intro h
    have hmem : c ∈ pairCurve hN Q := by
      simp only [pairCurve]
      rw [h]
      exact Or.inl (Or.inr rfl)
    exact arcSide_subset hN Q I.2 I.1 hcv hmem
  have hland1 : LandsN hN (Int.fract I.1) Q.y := by
    rcases hI with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1]; exact (landsN_fract hN Q.a Q.y).mp Q.lands_a
    · rw [h1]; exact (landsN_fract hN Q.b Q.y).mp Q.lands_b
  have hland2 : LandsN hN (Int.fract I.2) Q.y := by
    rcases hI with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]
      have hm : Q.a + arcLen Q.a Q.b = Q.b + ((-⌊Q.b - Q.a⌋ : ℤ):ℝ) := by
        unfold arcLen; rw [Int.fract]; push_cast; ring
      rw [hm, Int.fract_add_intCast]
      exact (landsN_fract hN Q.b Q.y).mp Q.lands_b
    · rw [h2]
      have hm : Q.b + arcLen Q.b Q.a = Q.a + ((-⌊Q.a - Q.b⌋ : ℤ):ℝ) := by
        unfold arcLen; rw [Int.fract]; push_cast; ring
      rw [hm, Int.fract_add_intCast]
      exact (landsN_fract hN Q.a Q.y).mp Q.lands_a
  have hTA : ∀ j : Fin 2, LandsN hN (T (preArc j I).2) Q.y := by
    intro j; rw [T_preArc_snd]; exact hland1
  have hTB : ∀ j : Fin 2, LandsN hN (T (preArc j I).1) Q.y := by
    intro j; rw [T_preArc_fst]; exact hland2
  choose uA huA using fun j : Fin 2 => landsN_preimage hN hφ hQc (hTA j)
  choose uB huB using fun j : Fin 2 => landsN_preimage hN hφ hQc (hTB j)
  obtain ⟨u, hu1, hu2, hu0, hall⟩ := fiber_neg hQc
  have hmemA : ∀ j, uA j = u ∨ uA j = -u := fun j => hall _ (huA j).1
  have hmemB : ∀ j, uB j = u ∨ uB j = -u := fun j => hall _ (huB j).1
  have huA1 : uA 1 = - uA 0 := by
    have hlim1 : Tendsto (fun t : ℝ => hN.rayPt (preArc 1 I).2 t) (𝓝[>] (1:ℝ)) (𝓝 (uA 1)) :=
      (huA 1).2
    have hlim0 : Tendsto (fun t : ℝ => hN.rayPt (preArc 0 I).2 t) (𝓝[>] (1:ℝ)) (𝓝 (uA 0)) :=
      (huA 0).2
    have heq : (fun t : ℝ => hN.rayPt (preArc 1 I).2 t)
        = (fun t : ℝ => - hN.rayPt (preArc 0 I).2 t) := by
      funext t
      by_cases ht : 1 < t
      · exact rayPt_preArc_snd_neg hN hφ hcK I ht
      · rw [Work.Top.NakaneData.rayPt, Work.Top.NakaneData.rayPt]; simp [ht]
    rw [heq] at hlim1
    exact tendsto_nhds_unique hlim1 hlim0.neg
  have huB1 : uB 1 = - uB 0 := by
    have hlim1 : Tendsto (fun t : ℝ => hN.rayPt (preArc 1 I).1 t) (𝓝[>] (1:ℝ)) (𝓝 (uB 1)) :=
      (huB 1).2
    have hlim0 : Tendsto (fun t : ℝ => hN.rayPt (preArc 0 I).1 t) (𝓝[>] (1:ℝ)) (𝓝 (uB 0)) :=
      (huB 0).2
    have heq : (fun t : ℝ => hN.rayPt (preArc 1 I).1 t)
        = (fun t : ℝ => - hN.rayPt (preArc 0 I).1 t) := by
      funext t
      by_cases ht : 1 < t
      · exact rayPt_preArc_fst_neg hN hφ hcK I ht
      · rw [Work.Top.NakaneData.rayPt, Work.Top.NakaneData.rayPt]; simp [ht]
    rw [heq] at hlim1
    exact tendsto_nhds_unique hlim1 hlim0.neg
  have huA_ne : uA 0 ≠ uA 1 := by
    intro h
    have h0 : uA 0 = 0 := by
      rw [huA1] at h
      have h2 : (2:ℂ) * uA 0 = 0 := by rw [two_mul]; linear_combination h
      exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
    rcases hmemA 0 with h' | h'
    · exact hu0 (h'.symm.trans h0)
    · exact hu0 (neg_eq_zero.mp (by rw [h'] at h0; exact h0))
  by_cases hcase : uB 0 = uA 0
  · have hk : ∀ j : Fin 2, uB j = uA j := by
      intro j
      have hj : j.val = 0 ∨ j.val = 1 := by have := j.isLt; omega
      rcases hj with hv | hv
      · have hj0 : j = 0 := Fin.ext (by simpa using hv)
        rw [hj0]; exact hcase
      · have hj1 : j = 1 := Fin.ext (by simpa using hv)
        rw [hj1]; rw [huB1, huA1, hcase]
    exact ⟨uA k, (huA k).1, (hk k) ▸ (huB k).2, (huA k).2⟩
  · -- the crossed case leads to a contradiction
    have hB0 : uB 0 = -uA 0 := by
      rcases hmemA 0 with h' | h' <;> rcases hmemB 0 with h'' | h''
      · exact absurd (h''.trans h'.symm) hcase
      · simp only [h'', h', neg_neg]
      · simp only [h'', h', neg_neg]
      · exact absurd (h''.trans h'.symm) hcase
    have hB1' : uB 1 = uA 0 := by rw [huB1, hB0]; ring
    have hB0' : uB 0 = uA 1 := by rw [hB0, huA1]
    let G0 : CoPair hN := ⟨(preArc 0 I).2, (preArc 1 I).1, uA 0, (huA 0).2, hB1' ▸ (huB 1).2⟩
    let G1 : CoPair hN := ⟨(preArc 1 I).2, (preArc 0 I).1, uA 1, (huA 1).2, hB0' ▸ (huB 0).2⟩
    have hG0a : G0.a = (preArc 0 I).2 := rfl
    have hG0b : G0.b = (preArc 1 I).1 := rfl
    have hG0y : G0.y = uA 0 := rfl
    have hG1a : G1.a = (preArc 1 I).2 := rfl
    have hG1b : G1.b = (preArc 0 I).1 := rfl
    have hG1y : G1.y = uA 1 := rfl
    -- the exact (unwrapped) arc of `Q` whose side contains `c`
    obtain ⟨Sq, Sp, hSp, hSqm, hSJeq, harc⟩ :
        ∃ (Sq Sp : ℝ), I.1 = Sp ∧ (∃ m : ℤ, I.2 = Sq + m) ∧
          arcSide hN Q I.2 I.1 = arcSide hN Q Sq Sp ∧
          ((Sq = Q.a ∧ Sp = Q.b) ∨ (Sq = Q.b ∧ Sp = Q.a)) := by
      rcases hI with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨Q.b, Q.a, by rw [h1], ?_, ?_, Or.inr ⟨rfl, rfl⟩⟩
        · exact ⟨-⌊Q.b - Q.a⌋, by rw [h2]; unfold arcLen; rw [Int.fract]; push_cast; ring⟩
        · rw [h1, h2]
          have hm : Q.a + arcLen Q.a Q.b = Q.b + ((-⌊Q.b - Q.a⌋ : ℤ):ℝ) := by
            unfold arcLen; rw [Int.fract]; push_cast; ring
          rw [hm, arcSide_add_int_left hN Q Q.b Q.a (-⌊Q.b - Q.a⌋)]
      · refine ⟨Q.a, Q.b, by rw [h1], ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨-⌊Q.a - Q.b⌋, by rw [h2]; unfold arcLen; rw [Int.fract]; push_cast; ring⟩
        · rw [h1, h2]
          have hm : Q.b + arcLen Q.b Q.a = Q.a + ((-⌊Q.a - Q.b⌋ : ℤ):ℝ) := by
            unfold arcLen; rw [Int.fract]; push_cast; ring
          rw [hm, arcSide_add_int_left hN Q Q.a Q.b (-⌊Q.a - Q.b⌋)]
    have hcv' : c ∈ arcSide hN Q Sq Sp := by rw [← hSJeq]; exact hcv
    have hne0 : arcLen G0.a G0.b ≠ 0 := by
      rw [hG0a, hG0b, arcLen_A0B1 I hIp hIq]; intro h; linarith
    have hne1 : arcLen G1.a G1.b ≠ 0 := by
      rw [hG1a, hG1b, arcLen_A1B0 I hIp hIq]; intro h; linarith
    have hIn_other0 : InArc (preArc 1 I).2 G0.b G0.a := by
      rw [hG0b, hG0a]; exact InArc_A1B1A0 I hIp hIq
    have hIn_other0' : InArc (preArc 0 I).1 G0.b G0.a := by
      rw [hG0b, hG0a]; exact InArc_B0B1A0 I hIp hIq
    have hIn_other1 : InArc (preArc 0 I).2 G1.b G1.a := by
      rw [hG1b, hG1a]; exact InArc_A0B0A1 I hIp hIq
    have hIn_other1' : InArc (preArc 1 I).1 G1.b G1.a := by
      rw [hG1b, hG1a]; exact InArc_B1B0A1 I hIp hIq
    have hIn_mid0 : InArc (G0.a + arcLen G0.a G0.b / 2) G0.a G0.b := by
      rw [hG0a, hG0b]; exact InArc_mid0 I hIp hIq
    have hIn_mid1 : InArc (G1.a + arcLen G1.a G1.b / 2) G1.a G1.b := by
      rw [hG1a, hG1b]; exact InArc_mid1 I hIp hIq
    have hIn_mid0o : InArc (G0.a + arcLen G0.a G0.b / 2) G1.b G1.a := by
      rw [hG0a, hG0b, hG1b, hG1a]; exact InArc_mid0_other I hIp hIq
    have hIn_mid1o : InArc (G1.a + arcLen G1.a G1.b / 2) G0.b G0.a := by
      rw [hG1a, hG1b, hG0b, hG0a]; exact InArc_mid1_other I hIp hIq
    have hsubA0 : hN.paramRay (preArc 1 I).2 ⊆ arcSide hN G0 G0.b G0.a :=
      htop.angle G0 G0.b G0.a (preArc 1 I).2 (Or.inr ⟨rfl, rfl⟩) hne0 hIn_other0
    have hsubB0 : hN.paramRay (preArc 0 I).1 ⊆ arcSide hN G0 G0.b G0.a :=
      htop.angle G0 G0.b G0.a (preArc 0 I).1 (Or.inr ⟨rfl, rfl⟩) hne0 hIn_other0'
    have hsubA1 : hN.paramRay (preArc 0 I).2 ⊆ arcSide hN G1 G1.b G1.a :=
      htop.angle G1 G1.b G1.a (preArc 0 I).2 (Or.inr ⟨rfl, rfl⟩) hne1 hIn_other1
    have hsubB1 : hN.paramRay (preArc 1 I).1 ⊆ arcSide hN G1 G1.b G1.a :=
      htop.angle G1 G1.b G1.a (preArc 1 I).1 (Or.inr ⟨rfl, rfl⟩) hne1 hIn_other1'
    have hcl1 : uA 1 ∈ closure (arcSide hN G0 G0.b G0.a) := by
      refine mem_closure_of_tendsto (huA 1).2 ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hsubA0 (rayPt_mem_paramRay hN _ ht)
    have hcl0 : uA 0 ∈ closure (arcSide hN G1 G1.b G1.a) := by
      refine mem_closure_of_tendsto (huA 0).2 ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hsubA1 (rayPt_mem_paramRay hN _ ht)
    have hnotin1 : uA 1 ∉ pairSide hN G0 := by
      intro hmem
      have hopen := isOpen_arcSide hN htop G0 G0.a G0.b
      obtain ⟨y, hy⟩ := mem_closure_iff.mp hcl1 (pairSide hN G0) hopen hmem
      rw [Set.mem_inter_iff] at hy
      exact Set.disjoint_left.mp (htop.sep G0 hne0) hy.1 hy.2
    have hnotin0 : uA 0 ∉ pairSide hN G1 := by
      intro hmem
      have hopen := isOpen_arcSide hN htop G1 G1.a G1.b
      obtain ⟨y, hy⟩ := mem_closure_iff.mp hcl0 (pairSide hN G1) hopen hmem
      rw [Set.mem_inter_iff] at hy
      exact Set.disjoint_left.mp (htop.sep G1 hne1) hy.1 hy.2
    have hpre0 : (preArc 0 I).2 = Int.fract (-I.1/2) := by norm_num [preArc]
    have hpre1 : (preArc 1 I).2 = Int.fract (-I.1/2 + 1/2) := by norm_num [preArc]
    have hfst0 : (preArc 0 I).1 = Int.fract (-I.2/2) := by norm_num [preArc]
    have hfst1 : (preArc 1 I).1 = Int.fract (-I.2/2 + 1/2) := by norm_num [preArc]
    have hpc := pairCurve_eq_I hN hI
    -- the two "the side misses the preimage of the curve" statements
    have hmiss0 : Disjoint (pairSide hN G0) (Tantibar c ⁻¹' pairCurve hN Q) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      have hxPC : x ∉ pairCurve hN G0 := (arcSide_subset hN G0 G0.a G0.b) hx
      have hxAS : x ∉ arcSide hN G0 G0.b G0.a :=
        Set.disjoint_left.mp (htop.sep G0 hne0) hx
      rw [hpc] at hx'
      rcases hx' with (hx' | hx'y) | hx'
      · have hle := preimage_paramRay hN hφ I.1 hx'
        rw [← hpre0, ← hpre1, Set.mem_union] at hle
        rcases hle with hle | hle
        · exact hxPC (Or.inl (Or.inl (by rw [hG0a]; exact hle)))
        · exact hxAS (hsubA0 hle)
      · have hxu : x = u ∨ x = -u := hall x hx'y
        have hpair : x = uA 0 ∨ x = uA 1 := by
          rcases hxu with h | h
          · rcases hmemA 0 with h' | h'
            · exact Or.inl (h.trans h'.symm)
            · exact Or.inr (by rw [huA1, h', neg_neg]; exact h)
          · rcases hmemA 0 with h' | h'
            · exact Or.inr (by rw [huA1, h']; exact h)
            · exact Or.inl (by rw [h, h'])
        rcases hpair with h | h
        · exact hxPC (by
            rw [h]
            rw [show pairCurve hN G0 = hN.paramRay G0.a ∪ {G0.y} ∪ hN.paramRay G0.b from rfl]
            exact Or.inl (Or.inr rfl))
        · rw [h] at hx; exact hnotin1 hx
      · have hle := preimage_paramRay hN hφ I.2 hx'
        rw [← hfst0, ← hfst1, Set.mem_union] at hle
        rcases hle with hle | hle
        · exact hxAS (hsubB0 hle)
        · exact hxPC (Or.inr (by rw [hG0b]; exact hle))
    have hmiss1 : Disjoint (pairSide hN G1) (Tantibar c ⁻¹' pairCurve hN Q) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      have hxPC : x ∉ pairCurve hN G1 := (arcSide_subset hN G1 G1.a G1.b) hx
      have hxAS : x ∉ arcSide hN G1 G1.b G1.a :=
        Set.disjoint_left.mp (htop.sep G1 hne1) hx
      rw [hpc] at hx'
      rcases hx' with (hx' | hx'y) | hx'
      · have hle := preimage_paramRay hN hφ I.1 hx'
        rw [← hpre0, ← hpre1, Set.mem_union] at hle
        rcases hle with hle | hle
        · exact hxAS (hsubA1 hle)
        · exact hxPC (Or.inl (Or.inl (by rw [hG1a]; exact hle)))
      · have hxu : x = u ∨ x = -u := hall x hx'y
        have hpair : x = uA 0 ∨ x = uA 1 := by
          rcases hxu with h | h
          · rcases hmemA 0 with h' | h'
            · exact Or.inl (h.trans h'.symm)
            · exact Or.inr (by rw [huA1, h', neg_neg]; exact h)
          · rcases hmemA 0 with h' | h'
            · exact Or.inr (by rw [huA1, h']; exact h)
            · exact Or.inl (by rw [h, h'])
        rcases hpair with h | h
        · rw [h] at hx; exact hnotin0 hx
        · exact hxPC (by
            rw [h]
            rw [show pairCurve hN G1 = hN.paramRay G1.a ∪ {G1.y} ∪ hN.paramRay G1.b from rfl]
            exact Or.inl (Or.inr rfl))
      · have hle := preimage_paramRay hN hφ I.2 hx'
        rw [← hfst0, ← hfst1, Set.mem_union] at hle
        rcases hle with hle | hle
        · exact hxPC (Or.inr (by rw [hG1b]; exact hle))
        · exact hxAS (hsubB1 hle)
    -- the two images
    have himg0 : Tantibar c '' pairCurve hN G0 ⊆ pairCurve hN Q := by
      have h1 : Tantibar c '' hN.paramRay G0.a ⊆ pairCurve hN Q :=
        (image_paramRay_subset hN hφ G0.a).trans (by
          rw [hG0a, T_preArc_snd, paramRay_fract]
          exact paramRay_I1_subset_pairCurve hN hI)
      have h2 : Tantibar c '' hN.paramRay G0.b ⊆ pairCurve hN Q :=
        (image_paramRay_subset hN hφ G0.b).trans (by
          rw [hG0b, T_preArc_fst, paramRay_fract]
          exact paramRay_I2_subset_pairCurve hN hI)
      rintro w ⟨z, hz, rfl⟩
      rw [show pairCurve hN G0 = hN.paramRay G0.a ∪ {G0.y} ∪ hN.paramRay G0.b from rfl] at hz
      rcases hz with (hz | hzy) | hz
      · exact h1 ⟨z, hz, rfl⟩
      · rw [Set.mem_singleton_iff] at hzy
        rw [hzy, hG0y, (huA 0).1]
        rw [show pairCurve hN Q = hN.paramRay Q.a ∪ {Q.y} ∪ hN.paramRay Q.b from rfl]
        exact Or.inl (Or.inr rfl)
      · exact h2 ⟨z, hz, rfl⟩
    have himg1 : Tantibar c '' pairCurve hN G1 ⊆ pairCurve hN Q := by
      have h1 : Tantibar c '' hN.paramRay G1.a ⊆ pairCurve hN Q :=
        (image_paramRay_subset hN hφ G1.a).trans (by
          rw [hG1a, T_preArc_snd, paramRay_fract]
          exact paramRay_I1_subset_pairCurve hN hI)
      have h2 : Tantibar c '' hN.paramRay G1.b ⊆ pairCurve hN Q :=
        (image_paramRay_subset hN hφ G1.b).trans (by
          rw [hG1b, T_preArc_fst, paramRay_fract]
          exact paramRay_I2_subset_pairCurve hN hI)
      rintro w ⟨z, hz, rfl⟩
      rw [show pairCurve hN G1 = hN.paramRay G1.a ∪ {G1.y} ∪ hN.paramRay G1.b from rfl] at hz
      rcases hz with (hz | hzy) | hz
      · exact h1 ⟨z, hz, rfl⟩
      · rw [Set.mem_singleton_iff] at hzy
        rw [hzy, hG1y, (huA 1).1]
        rw [show pairCurve hN Q = hN.paramRay Q.a ∪ {Q.y} ∪ hN.paramRay Q.b from rfl]
        exact Or.inl (Or.inr rfl)
      · exact h2 ⟨z, hz, rfl⟩
    have hInSq0 : InArc (T (G0.a + arcLen G0.a G0.b / 2)) Sq Sp := by
      rw [hG0a, hG0b]
      have h := InArc_Tmid0_I I hIp hIq
      rw [hSp] at h
      obtain ⟨m, hm⟩ := hSqm
      rw [hm] at h
      exact (InArc_add_int_left (T ((preArc 0 I).2 + arcLen (preArc 0 I).2 (preArc 1 I).1 / 2))
        Sq Sp m).mp h
    have hInSq1 : InArc (T (G1.a + arcLen G1.a G1.b / 2)) Sq Sp := by
      rw [hG1a, hG1b]
      have h := InArc_Tmid1_I I hIp hIq
      rw [hSp] at h
      obtain ⟨m, hm⟩ := hSqm
      rw [hm] at h
      exact (InArc_add_int_left (T ((preArc 1 I).2 + arcLen (preArc 1 I).2 (preArc 0 I).1 / 2))
        Sq Sp m).mp h
    have hpt0 : ∃ x ∈ pairSide hN G0, Tantibar c x ∈ arcSide hN Q Sq Sp := by
      refine ⟨hN.rayPt (G0.a + arcLen G0.a G0.b / 2) 2, ?_, ?_⟩
      · exact htop.angle G0 G0.a G0.b (G0.a + arcLen G0.a G0.b / 2) (Or.inl ⟨rfl, rfl⟩) hne0
          hIn_mid0 (rayPt_mem_paramRay hN _ (by norm_num))
      · rw [← rayPt_Tantibar hN hφ (show (1:ℝ) < 2 by norm_num)]
        exact htop.angle Q Sq Sp (T (G0.a + arcLen G0.a G0.b / 2)) harc hab hInSq0
          (rayPt_mem_paramRay hN _ (by norm_num))
    have hpt1 : ∃ x ∈ pairSide hN G1, Tantibar c x ∈ arcSide hN Q Sq Sp := by
      refine ⟨hN.rayPt (G1.a + arcLen G1.a G1.b / 2) 2, ?_, ?_⟩
      · exact htop.angle G1 G1.a G1.b (G1.a + arcLen G1.a G1.b / 2) (Or.inl ⟨rfl, rfl⟩) hne1
          hIn_mid1 (rayPt_mem_paramRay hN _ (by norm_num))
      · rw [← rayPt_Tantibar hN hφ (show (1:ℝ) < 2 by norm_num)]
        exact htop.angle Q Sq Sp (T (G1.a + arcLen G1.a G1.b / 2)) harc hab hInSq1
          (rayPt_mem_paramRay hN _ (by norm_num))
    -- the images are the side `arcSide Q Sq Sp`, which contains `c`; hence `0` lies in both sides
    have hSI0 := side_image_eq hN htop G0 Q Sq Sp himg0 hmiss0 hpt0
    have hSI1 := side_image_eq hN htop G1 Q Sq Sp himg1 hmiss1 hpt1
    have hzero0 : (0:ℂ) ∈ pairSide hN G0 := by
      have hc0 : c ∈ Tantibar c '' pairSide hN G0 := by rw [hSI0]; exact hcv'
      obtain ⟨x0, hx0, hx0eq⟩ := hc0
      have hx0z : x0 = 0 := by
        have h2 : (starRingEnd ℂ x0)^2 = 0 := by
          have h1 : Tantibar c x0 = c := hx0eq
          simp only [Tantibar] at h1
          linear_combination h1
        have h3 : (starRingEnd ℂ x0) = 0 := sq_eq_zero_iff.mp h2
        simpa using congrArg (starRingEnd ℂ) h3
      rw [hx0z] at hx0
      exact hx0
    have hzero1 : (0:ℂ) ∈ pairSide hN G1 := by
      have hc0 : c ∈ Tantibar c '' pairSide hN G1 := by rw [hSI1]; exact hcv'
      obtain ⟨x0, hx0, hx0eq⟩ := hc0
      have hx0z : x0 = 0 := by
        have h2 : (starRingEnd ℂ x0)^2 = 0 := by
          have h1 : Tantibar c x0 = c := hx0eq
          simp only [Tantibar] at h1
          linear_combination h1
        have h3 : (starRingEnd ℂ x0) = 0 := sq_eq_zero_iff.mp h2
        simpa using congrArg (starRingEnd ℂ) h3
      rw [hx0z] at hx0
      exact hx0
    -- the two sides are disjoint
    have hy0 : hN.rayPt (G0.a + arcLen G0.a G0.b / 2) 2 ∈ pairSide hN G0 :=
      htop.angle G0 G0.a G0.b (G0.a + arcLen G0.a G0.b / 2) (Or.inl ⟨rfl, rfl⟩) hne0 hIn_mid0
        (rayPt_mem_paramRay hN _ (by norm_num))
    have hy0' : hN.rayPt (G0.a + arcLen G0.a G0.b / 2) 2 ∈ arcSide hN G1 G1.b G1.a :=
      htop.angle G1 G1.b G1.a (G0.a + arcLen G0.a G0.b / 2) (Or.inr ⟨rfl, rfl⟩) hne1 hIn_mid0o
        (rayPt_mem_paramRay hN _ (by norm_num))
    have hsub01 : pairSide hN G0 ⊆ arcSide hN G1 G1.b G1.a := by
      have heq : arcSide hN G1 G1.b G1.a
          = connectedComponentIn (pairCurve hN G1)ᶜ
              (hN.rayPt (G0.a + arcLen G0.a G0.b / 2) 2) :=
        connectedComponentIn_eq hy0'
      rw [heq]
      exact IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
        hy0 (fun x hx => by
          intro hx1
          exact (Set.disjoint_left.mp hmiss0 hx) (himg1 ⟨x, hx1, rfl⟩))
    have hdisj : Disjoint (pairSide hN G0) (pairSide hN G1) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact Set.disjoint_left.mp (htop.sep G1 hne1) hx' (hsub01 hx)
    exact (Set.disjoint_left.mp hdisj hzero0 hzero1).elim

end Work.ELPull
