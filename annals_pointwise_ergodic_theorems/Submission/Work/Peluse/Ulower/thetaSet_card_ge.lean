import Mathlib
import Submission.Work.Peluse.Ulower.thetaDefs

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Finset

/-! ### Pointwise lemmas for the coordinatewise selection -/

lemma thetaSel_cons_tail {σ : ℕ} (ω : Fin (σ+1) → Bool) (a b : ℤ) (u v : Fin σ → ℤ) :
    thetaSel ω (Fin.cons a u) (Fin.cons b v) =
      Fin.cons (if ω 0 then a else b) (thetaSel (Fin.tail ω) u v) := by
  rw [← thetaSel_cons (ω 0) (Fin.tail ω) a b u v, Fin.cons_self_tail ω]

lemma thetaSel_const_true {σ : ℕ} (s t : Fin σ → ℤ) :
    thetaSel (fun _ : Fin σ => true) s t = s := by
  funext i; simp [thetaSel]

lemma thetaSel_const_false {σ : ℕ} (s t : Fin σ → ℤ) :
    thetaSel (fun _ : Fin σ => false) s t = t := by
  funext i; simp [thetaSel]

/-- The `2^(σ+1)` conditions of the `(σ+1)`-dimensional pair count split into the two
`2^σ`-fold conditions for the fibres at the two possible values of the new coordinate. -/
lemma cond_cons_iff {σ D : ℕ} {K : Finset (Fin (σ+1) → ℤ)} {a b : ℤ}
    {u v : Fin σ → ℤ} (hu : u ∈ thetaBox σ D) (hv : v ∈ thetaBox σ D) :
    (∀ ω : Fin (σ+1) → Bool, thetaSel ω (Fin.cons a u) (Fin.cons b v) ∈ K) ↔
      (∀ ω' : Fin σ → Bool,
        thetaSel ω' u v ∈ thetaFibreOne D K a ∩ thetaFibreOne D K b) := by
  constructor
  · intro h ω'
    have hbox := thetaSel_mem_thetaBox hu hv ω'
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · rw [mem_thetaFibreOne]
      exact ⟨hbox, by simpa [thetaSel_cons] using h (Fin.cons true ω')⟩
    · rw [mem_thetaFibreOne]
      exact ⟨hbox, by simpa [thetaSel_cons] using h (Fin.cons false ω')⟩
  · intro h ω
    rw [thetaSel_cons_tail ω a b u v]
    have hw := h (Fin.tail ω)
    rw [Finset.mem_inter, mem_thetaFibreOne, mem_thetaFibreOne] at hw
    obtain ⟨⟨_, ha⟩, ⟨_, hb⟩⟩ := hw
    by_cases hε : ω 0
    · simpa [hε] using ha
    · simpa [hε] using hb

/-- **The recursion.** The pair count in dimension `σ+1` is the sum, over the two possible values
of the new coordinate, of the pair counts of the corresponding fibres. -/
theorem thetaPairCount_succ {σ D : ℕ} (K : Finset (Fin (σ+1) → ℤ)) :
    thetaPairCount (σ+1) D K =
      ∑ a ∈ Finset.Icc (1:ℤ) (D:ℤ), ∑ b ∈ Finset.Icc (1:ℤ) (D:ℤ),
        thetaPairCount σ D (thetaFibreOne D K a ∩ thetaFibreOne D K b) := by
  rw [thetaPairCount_eq_sum (σ+1) D K]
  set I : Finset ℤ := Finset.Icc (1:ℤ) (D:ℤ) with hI
  have hstep : ∀ a ∈ I, ∀ b ∈ I,
      (∑ u ∈ thetaBox σ D, ∑ v ∈ thetaBox σ D,
        if (∀ ω : Fin (σ+1) → Bool, thetaSel ω (Fin.cons a u) (Fin.cons b v) ∈ K)
          then 1 else 0)
        = thetaPairCount σ D (thetaFibreOne D K a ∩ thetaFibreOne D K b) := by
    intro a ha b hb
    rw [thetaPairCount_eq_sum]
    refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
    simp only [cond_cons_iff hu hv]
  calc ∑ s ∈ thetaBox (σ+1) D, ∑ t ∈ thetaBox (σ+1) D,
          (if (∀ ω : Fin (σ+1) → Bool, thetaSel ω s t ∈ K) then 1 else 0)
      = ∑ a ∈ I, ∑ u ∈ thetaBox σ D, ∑ t ∈ thetaBox (σ+1) D,
          (if (∀ ω : Fin (σ+1) → Bool, thetaSel ω (Fin.cons a u) t ∈ K) then 1 else 0) :=
        thetaSum_box_succ _
    _ = ∑ a ∈ I, ∑ u ∈ thetaBox σ D, ∑ b ∈ I, ∑ v ∈ thetaBox σ D,
          (if (∀ ω : Fin (σ+1) → Bool,
            thetaSel ω (Fin.cons a u) (Fin.cons b v) ∈ K) then 1 else 0) := by
        refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun u hu => ?_
        exact thetaSum_box_succ _
    _ = ∑ a ∈ I, ∑ b ∈ I, ∑ u ∈ thetaBox σ D, ∑ v ∈ thetaBox σ D,
          (if (∀ ω : Fin (σ+1) → Bool,
            thetaSel ω (Fin.cons a u) (Fin.cons b v) ∈ K) then 1 else 0) := by
        refine Finset.sum_congr rfl fun a ha => ?_
        exact Finset.sum_comm
    _ = ∑ a ∈ I, ∑ b ∈ I, thetaPairCount σ D (thetaFibreOne D K a ∩ thetaFibreOne D K b) :=
        Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hstep a ha b hb


/-! ### Counting lemmas -/

/-- Splitting a subset of `[1,D]^(σ+1)` according to the value of the `0`-th coordinate. -/
lemma thetaCard_eq_sum_fibreOne_card {σ D : ℕ} {K : Finset (Fin (σ+1) → ℤ)}
    (hK : K ⊆ thetaBox (σ+1) D) :
    K.card = ∑ a ∈ Finset.Icc (1:ℤ) (D:ℤ), (thetaFibreOne D K a).card := by
  have h1 : K = (thetaBox (σ+1) D).filter (fun s => s ∈ K) := by
    ext s
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hK h, h⟩, fun h => h.2⟩
  calc K.card = ((thetaBox (σ+1) D).filter (fun s => s ∈ K)).card := by
        conv_lhs => rw [h1]
    _ = ∑ s ∈ thetaBox (σ+1) D, (if s ∈ K then 1 else 0) := by rw [Finset.card_filter]
    _ = ∑ a ∈ Finset.Icc (1:ℤ) (D:ℤ), ∑ u ∈ thetaBox σ D,
          (if Fin.cons a u ∈ K then 1 else 0) :=
        thetaSum_box_succ (fun s : Fin (σ+1) → ℤ => if s ∈ K then 1 else 0)
    _ = ∑ a ∈ Finset.Icc (1:ℤ) (D:ℤ), (thetaFibreOne D K a).card := by
        refine Finset.sum_congr rfl fun a ha => ?_
        simp only [thetaFibreOne, Finset.card_filter]

/-- Double counting the elements of `H` by their first component. -/
lemma thetaFibre_card_eq {σ D : ℕ} {H : Finset ((Fin σ → ℤ) × (Fin σ → ℤ))}
    (hH : ∀ p ∈ H, p.1 ∈ thetaBox σ D ∧ p.2 ∈ thetaBox σ D) :
    H.card = ∑ k1 ∈ thetaBox σ D, (thetaFibre D H k1).card := by
  have h1 : H = ((thetaBox σ D) ×ˢ (thetaBox σ D)).filter (fun p => p ∈ H) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨fun h => ⟨⟨(hH p h).1, (hH p h).2⟩, h⟩, fun h => h.2⟩
  calc H.card = (((thetaBox σ D) ×ˢ (thetaBox σ D)).filter (fun p => p ∈ H)).card := by
        conv_lhs => rw [h1]
    _ = ∑ p ∈ (thetaBox σ D) ×ˢ (thetaBox σ D), (if p ∈ H then 1 else 0) := by
        rw [Finset.card_filter]
    _ = ∑ k1 ∈ thetaBox σ D, ∑ k2 ∈ thetaBox σ D, (if (k1, k2) ∈ H then 1 else 0) := by
        rw [Finset.sum_product]
    _ = ∑ k1 ∈ thetaBox σ D, (thetaFibre D H k1).card := by
        refine Finset.sum_congr rfl fun k1 hk1 => ?_
        simp only [thetaFibre, Finset.card_filter]

set_option maxHeartbeats 1000000 in
/-- `ThetaSet σ D H` is the disjoint union over `k1 ∈ [1,D]^σ` of the pairs `(k2,k3)` whose `2^σ`
corners all lie in the fibre `{c | (k1,c) ∈ H}`. -/
theorem thetaSet_card_eq (σ D : ℕ) (H : Finset ((Fin σ → ℤ) × (Fin σ → ℤ))) :
    (ThetaSet σ D H).card =
      ∑ k1 ∈ thetaBox σ D, thetaPairCount σ D (thetaFibre D H k1) := by
  have hTS : ThetaSet σ D H = ((thetaBox σ D) ×ˢ ((thetaBox σ D) ×ˢ (thetaBox σ D))).filter
      (fun k => ∀ ω : Fin σ → Bool, (k.1, thetaSel ω k.2.1 k.2.2) ∈ H) := rfl
  have hcond : ∀ (k1 t u : Fin σ → ℤ), t ∈ thetaBox σ D → u ∈ thetaBox σ D →
      ((∀ ω : Fin σ → Bool, (k1, thetaSel ω t u) ∈ H) ↔
       (∀ ω : Fin σ → Bool, thetaSel ω t u ∈ thetaFibre D H k1)) := by
    intro k1 t u ht hu
    constructor
    · intro h ω
      simp only [mem_thetaFibre]
      exact ⟨thetaSel_mem_thetaBox ht hu ω, h ω⟩
    · intro h ω
      simp only [mem_thetaFibre] at h
      exact (h ω).2
  rw [hTS, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun k1 hk1 => ?_
  have hsplit : (∑ k2 ∈ (thetaBox σ D) ×ˢ (thetaBox σ D),
        (if (∀ ω : Fin σ → Bool, (k1, thetaSel ω k2.1 k2.2) ∈ H) then 1 else 0))
      = ∑ t ∈ thetaBox σ D, ∑ u ∈ thetaBox σ D,
        (if (∀ ω : Fin σ → Bool, (k1, thetaSel ω t u) ∈ H) then 1 else 0) := by
    rw [Finset.sum_product]
  rw [hsplit, thetaPairCount_eq_sum]
  refine Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun u hu => ?_
  simp only [hcond k1 t u ht hu]

/-- **Cauchy–Schwarz plus the power mean.**  If each `Kf a` is contained in `T`, then the `2t`-th
power of the total mass is bounded by the `2t`-fold diagonal sum of the intersection sizes. -/
theorem thetaPairIntersection_pow_sum {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (T : Finset α) (Kf : ι → Finset α) (hK : ∀ a ∈ s, Kf a ⊆ T)
    {t : ℕ} (ht : 1 ≤ t) :
    ((∑ a ∈ s, ((Kf a).card : ℝ)) ^ (2 * t)) ≤
      ((T.card : ℝ) ^ t * (s.card : ℝ) ^ (2 * t - 2)) *
        (∑ a ∈ s, ∑ b ∈ s, (((Kf a ∩ Kf b).card : ℝ)) ^ t) := by
  have hprod : ∀ (a b : ι) (v : α),
      (if v ∈ Kf a then (1:ℝ) else 0) * (if v ∈ Kf b then (1:ℝ) else 0)
        = (if v ∈ Kf a ∩ Kf b then (1:ℝ) else 0) := by
    intro a b v
    by_cases h1 : v ∈ Kf a <;> by_cases h2 : v ∈ Kf b <;>
      simp [h1, h2, Finset.mem_inter]
  have hcard : ∀ a ∈ s, ((Kf a).card : ℝ) = ∑ v ∈ T, (if v ∈ Kf a then (1:ℝ) else 0) := by
    intro a ha
    have hfil : T.filter (fun v => v ∈ Kf a) = Kf a := by
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hK a ha h, h⟩⟩
    conv_lhs => rw [← hfil]
    rw [Finset.card_filter, Nat.cast_sum]
    simp
  have hinter : ∀ a ∈ s, ∀ b ∈ s, (((Kf a ∩ Kf b).card : ℝ))
      = ∑ v ∈ T, (if v ∈ Kf a then (1:ℝ) else 0) * (if v ∈ Kf b then (1:ℝ) else 0) := by
    intro a ha b hb
    have hfil : T.filter (fun v => v ∈ Kf a ∩ Kf b) = Kf a ∩ Kf b := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_inter]
      exact ⟨fun h => h.2, fun h => ⟨hK a ha h.1, h⟩⟩
    conv_lhs => rw [← hfil]
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [hprod]
    simp
  have hCS : ((∑ a ∈ s, ((Kf a).card : ℝ)))^2
      ≤ (T.card : ℝ) * (∑ a ∈ s, ∑ b ∈ s, (((Kf a ∩ Kf b).card : ℝ))) := by
    have h1 : (∑ a ∈ s, ((Kf a).card : ℝ))
        = ∑ v ∈ T, (∑ a ∈ s, (if v ∈ Kf a then (1:ℝ) else 0)) := by
      rw [Finset.sum_congr rfl (fun a ha => hcard a ha)]
      exact Finset.sum_comm
    have h2 : (∑ a ∈ s, ∑ b ∈ s, (((Kf a ∩ Kf b).card : ℝ)))
        = ∑ v ∈ T, (∑ a ∈ s, (if v ∈ Kf a then (1:ℝ) else 0))^2 := by
      have e1 : (∑ a ∈ s, ∑ b ∈ s, (((Kf a ∩ Kf b).card : ℝ)))
          = ∑ p ∈ s ×ˢ s, (((Kf p.1 ∩ Kf p.2).card : ℝ)) := by
        rw [Finset.sum_product]
      rw [e1]
      have e2 : (∑ p ∈ s ×ˢ s, (((Kf p.1 ∩ Kf p.2).card : ℝ)))
          = ∑ p ∈ s ×ˢ s, ∑ v ∈ T,
              (if v ∈ Kf p.1 then (1:ℝ) else 0) * (if v ∈ Kf p.2 then (1:ℝ) else 0) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        have hp1 : p.1 ∈ s := (Finset.mem_product.mp hp).1
        have hp2 : p.2 ∈ s := (Finset.mem_product.mp hp).2
        exact hinter p.1 hp1 p.2 hp2
      rw [e2, Finset.sum_comm]
      refine Finset.sum_congr rfl fun v hv => ?_
      have e3 : (∑ p ∈ s ×ˢ s,
            (if v ∈ Kf p.1 then (1:ℝ) else 0) * (if v ∈ Kf p.2 then (1:ℝ) else 0))
          = (∑ a ∈ s, (if v ∈ Kf a then (1:ℝ) else 0)) *
            (∑ b ∈ s, (if v ∈ Kf b then (1:ℝ) else 0)) := by
        rw [Finset.sum_product, Finset.sum_mul_sum]
      rw [e3, pow_two]
    rw [h1, h2]
    exact sq_sum_le_card_mul_sum_sq
  have hPM : (∑ a ∈ s, ∑ b ∈ s, (((Kf a ∩ Kf b).card : ℝ)))^t
      ≤ ((s.card : ℝ)^(2*t-2)) *
        (∑ a ∈ s, ∑ b ∈ s, (((Kf a ∩ Kf b).card : ℝ))^t) := by
    have e1 : (∑ a ∈ s, ∑ b ∈ s, (((Kf a ∩ Kf b).card : ℝ)))
        = ∑ p ∈ s ×ˢ s, (((Kf p.1 ∩ Kf p.2).card : ℝ)) := by
      rw [Finset.sum_product]
    rw [e1]
    have h := pow_sum_le_card_mul_sum_pow (s := s ×ˢ s)
        (f := fun p : ι × ι => (((Kf p.1 ∩ Kf p.2).card : ℝ))) (fun i hi => by positivity) (t - 1)
    rw [Nat.sub_add_cancel ht] at h
    refine h.trans ?_
    have hcardp : ((#(s ×ˢ s) : ℕ) : ℝ) = (s.card : ℝ) * (s.card : ℝ) := by
      rw [Finset.card_product, Nat.cast_mul]
    rw [hcardp, mul_pow]
    have hright : (∑ p ∈ s ×ˢ s, (((Kf p.1 ∩ Kf p.2).card : ℝ))^t)
        = (∑ a ∈ s, ∑ b ∈ s, (((Kf a ∩ Kf b).card : ℝ))^t) := by
      rw [Finset.sum_product]
    rw [hright]
    refine mul_le_mul_of_nonneg_right (le_of_eq ?_)
      (Finset.sum_nonneg fun a ha => Finset.sum_nonneg fun b hb => by positivity)
    rw [← pow_add]
    congr 1
    omega
  calc ((∑ a ∈ s, ((Kf a).card : ℝ))^(2*t))
      = (((∑ a ∈ s, ((Kf a).card : ℝ))^2)^t) := by rw [pow_mul]
    _ ≤ (((T.card : ℝ) * (∑ a ∈ s, ∑ b ∈ s, (((Kf a ∩ Kf b).card : ℝ))))^t) :=
        pow_le_pow_left₀ (sq_nonneg _) hCS t
    _ = (T.card : ℝ)^t * (∑ a ∈ s, ∑ b ∈ s, (((Kf a ∩ Kf b).card : ℝ)))^t := by
        rw [mul_pow]
    _ ≤ (T.card : ℝ)^t * (((s.card : ℝ)^(2*t-2)) *
          (∑ a ∈ s, ∑ b ∈ s, (((Kf a ∩ Kf b).card : ℝ))^t)) :=
        mul_le_mul_of_nonneg_left hPM (by positivity)
    _ = (T.card : ℝ)^t * (s.card : ℝ)^(2*t-2) *
          (∑ a ∈ s, ∑ b ∈ s, (((Kf a ∩ Kf b).card : ℝ))^t) := by ring

/-! ### Bookkeeping lemmas for the real arithmetic -/

lemma thetaIcc_card_real (D : ℕ) :
    (((Finset.Icc (1:ℤ) (D:ℤ)).card : ℕ) : ℝ) = (D:ℝ) := by
  rw [Int.card_Icc]; norm_num

lemma thetaBox_card_real (σ D : ℕ) :
    (((thetaBox σ D).card : ℕ) : ℝ) = (D:ℝ)^σ := by
  rw [thetaBox_card, Nat.cast_pow]

lemma two_pow_succ_eq (σ : ℕ) : (2:ℕ)^(σ+1) = 2 * 2^σ := by
  rw [pow_succ', mul_comm]

/-- The exponent identity of the induction step. -/
lemma thetaExp_identity (n : ℕ) :
    n * 2^n + (2 * 2^n - 2) + n * (2^n - 2) = (n+1) * (2 * 2^n - 2) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; norm_num
  · have hm : 2 ≤ 2^n := by
      have h1 := Nat.one_lt_two_pow h.ne'
      omega
    have hkey : 2 * 2^n - 2 = 2^n + (2^n - 2) := by omega
    rw [hkey]; ring

/-- **The pair-counting bound.**  For `K ⊆ [1,D]^σ`, the number of ordered pairs `(s,t)` in the box
whose whole `2^σ`-point box lies in `K` dominates `|K|^{2^σ}/D^{σ(2^σ-2)}`. -/
theorem thetaPairCount_ge : ∀ (σ D : ℕ), 1 ≤ σ → ∀ K : Finset (Fin σ → ℤ), K ⊆ thetaBox σ D →
    ((K.card : ℝ) ^ (2 ^ σ)) ≤ ((D : ℝ) ^ (σ * (2 ^ σ - 2))) * (thetaPairCount σ D K : ℝ) := by
  intro σ
  induction σ with
  | zero => intro D h K hK; omega
  | succ n ih =>
      intro D hn K hK
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · -- base case: `σ = 1`
        subst h0
        have hcond : ∀ s t : Fin 1 → ℤ,
            (∀ ω : Fin 1 → Bool, thetaSel ω s t ∈ K) ↔ (s ∈ K ∧ t ∈ K) := by
          intro s t
          have hω : ∀ ω : Fin 1 → Bool, ω = (fun _ => ω 0) := by
            intro ω; funext i; rw [Subsingleton.elim i 0]
          constructor
          · intro h
            refine ⟨?_, ?_⟩
            · have h1 := h (fun _ => true)
              rwa [thetaSel_const_true] at h1
            · have h0' := h (fun _ => false)
              rwa [thetaSel_const_false] at h0'
          · rintro ⟨hs, ht⟩ ω
            rw [hω ω]
            by_cases hb : ω 0
            · have hst : thetaSel (fun _ : Fin 1 => ω 0) s t = s := by
                funext i; simp [thetaSel, hb]
              rw [hst]; exact hs
            · have hst : thetaSel (fun _ : Fin 1 => ω 0) s t = t := by
                funext i; simp [thetaSel, hb]
              rw [hst]; exact ht
        have hset : ((thetaBox 1 D).product (thetaBox 1 D)).filter
              (fun p : (Fin 1 → ℤ) × (Fin 1 → ℤ) =>
                ∀ ω : Fin 1 → Bool, thetaSel ω p.1 p.2 ∈ K)
            = (thetaBox 1 D).filter (fun s => s ∈ K) ×ˢ (thetaBox 1 D).filter (fun t => t ∈ K) := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_product, Finset.product_eq_sprod]
          constructor
          · rintro ⟨⟨hp1, hp2⟩, hq⟩
            obtain ⟨hk1, hk2⟩ := (hcond p.1 p.2).mp hq
            exact ⟨⟨hp1, hk1⟩, ⟨hp2, hk2⟩⟩
          · rintro ⟨⟨h1, hk1⟩, ⟨h2, hk2⟩⟩
            exact ⟨⟨h1, h2⟩, (hcond p.1 p.2).mpr ⟨hk1, hk2⟩⟩
        have hfil : (thetaBox 1 D).filter (fun s => s ∈ K) = K := by
          ext s
          simp only [Finset.mem_filter]
          exact ⟨fun h => h.2, fun h => ⟨hK h, h⟩⟩
        have hgoal : thetaPairCount 1 D K = K.card * K.card := by
          unfold thetaPairCount
          rw [hset, hfil]
          simp only [Finset.card_product]
        have hsq : ((K.card : ℝ) ^ (2:ℕ) ^ 1)
            = (D:ℝ)^(1 * (2^1 - 2)) * (((K.card * K.card : ℕ) : ℝ)) := by
          rw [Nat.cast_mul]
          norm_num
          ring
        rw [hgoal]
        exact le_of_eq hsq
      · -- induction step
        have hIccR : (((Finset.Icc (1:ℤ) (D:ℤ)).card : ℕ) : ℝ) = (D:ℝ) := thetaIcc_card_real D
        have hboxR : (((thetaBox n D).card : ℕ) : ℝ) = (D:ℝ)^n := thetaBox_card_real n D
        have hA : (∑ a ∈ Finset.Icc (1:ℤ) (D:ℤ), (((thetaFibreOne D K a).card : ℝ))) ^ (2 * 2^n)
              ≤ (D:ℝ)^(n * 2^n) * (D:ℝ)^(2 * 2^n - 2) *
                (∑ a ∈ Finset.Icc (1:ℤ) (D:ℤ), ∑ b ∈ Finset.Icc (1:ℤ) (D:ℤ),
                  (((thetaFibreOne D K a ∩ thetaFibreOne D K b).card : ℝ)) ^ (2^n)) := by
          have h := thetaPairIntersection_pow_sum (s := Finset.Icc (1:ℤ) (D:ℤ))
              (T := thetaBox n D) (Kf := fun a => thetaFibreOne D K a)
              (fun a _ => thetaFibreOne_subset K a) (t := 2^n) Nat.one_le_two_pow
          rwa [hboxR, hIccR, ← pow_mul] at h
        have hsum_bound :
            (∑ a ∈ Finset.Icc (1:ℤ) (D:ℤ), ∑ b ∈ Finset.Icc (1:ℤ) (D:ℤ),
                (((thetaFibreOne D K a ∩ thetaFibreOne D K b).card : ℝ)) ^ (2^n))
              ≤ (D:ℝ)^(n * (2^n - 2)) *
                (∑ a ∈ Finset.Icc (1:ℤ) (D:ℤ), ∑ b ∈ Finset.Icc (1:ℤ) (D:ℤ),
                  (thetaPairCount n D (thetaFibreOne D K a ∩ thetaFibreOne D K b) : ℝ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun a ha => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun b hb => ?_
          exact ih D hpos (thetaFibreOne D K a ∩ thetaFibreOne D K b)
            (Finset.inter_subset_left.trans (thetaFibreOne_subset K a))
        have hexp :
            (D:ℝ)^(n * 2^n) * (D:ℝ)^(2 * 2^n - 2) *
                ((D:ℝ)^(n * (2^n - 2)) *
                  (∑ a ∈ Finset.Icc (1:ℤ) (D:ℤ), ∑ b ∈ Finset.Icc (1:ℤ) (D:ℤ),
                    (thetaPairCount n D (thetaFibreOne D K a ∩ thetaFibreOne D K b) : ℝ)))
              = (D:ℝ)^((n+1) * (2 * 2^n - 2)) *
                  (∑ a ∈ Finset.Icc (1:ℤ) (D:ℤ), ∑ b ∈ Finset.Icc (1:ℤ) (D:ℤ),
                    (thetaPairCount n D (thetaFibreOne D K a ∩ thetaFibreOne D K b) : ℝ)) := by
          have hre : (D:ℝ)^(n * 2^n) * (D:ℝ)^(2 * 2^n - 2) *
                ((D:ℝ)^(n * (2^n - 2)) * (∑ a ∈ Finset.Icc (1:ℤ) (D:ℤ),
                  ∑ b ∈ Finset.Icc (1:ℤ) (D:ℤ),
                    (thetaPairCount n D (thetaFibreOne D K a ∩ thetaFibreOne D K b) : ℝ)))
              = ((D:ℝ)^(n * 2^n) * (D:ℝ)^(2 * 2^n - 2) * (D:ℝ)^(n * (2^n - 2))) *
                  (∑ a ∈ Finset.Icc (1:ℤ) (D:ℤ), ∑ b ∈ Finset.Icc (1:ℤ) (D:ℤ),
                    (thetaPairCount n D (thetaFibreOne D K a ∩ thetaFibreOne D K b) : ℝ)) := by
            ring
          rw [hre, ← pow_add, ← pow_add, thetaExp_identity]
        calc (K.card : ℝ) ^ (2 ^ (n+1))
            = (∑ a ∈ Finset.Icc (1:ℤ) (D:ℤ), (((thetaFibreOne D K a).card : ℝ))) ^ (2 * 2^n) := by
              rw [thetaCard_eq_sum_fibreOne_card hK, Nat.cast_sum, two_pow_succ_eq]
          _ ≤ (D:ℝ)^(n * 2^n) * (D:ℝ)^(2 * 2^n - 2) *
                (∑ a ∈ Finset.Icc (1:ℤ) (D:ℤ), ∑ b ∈ Finset.Icc (1:ℤ) (D:ℤ),
                  (((thetaFibreOne D K a ∩ thetaFibreOne D K b).card : ℝ)) ^ (2^n)) := hA
          _ ≤ (D:ℝ)^(n * 2^n) * (D:ℝ)^(2 * 2^n - 2) *
                ((D:ℝ)^(n * (2^n - 2)) *
                  (∑ a ∈ Finset.Icc (1:ℤ) (D:ℤ), ∑ b ∈ Finset.Icc (1:ℤ) (D:ℤ),
                    (thetaPairCount n D (thetaFibreOne D K a ∩ thetaFibreOne D K b) : ℝ))) :=
              mul_le_mul_of_nonneg_left hsum_bound (by positivity)
          _ = (D:ℝ)^((n+1) * (2 * 2^n - 2)) *
                (∑ a ∈ Finset.Icc (1:ℤ) (D:ℤ), ∑ b ∈ Finset.Icc (1:ℤ) (D:ℤ),
                  (thetaPairCount n D (thetaFibreOne D K a ∩ thetaFibreOne D K b) : ℝ)) := hexp
          _ = (D:ℝ)^((n+1) * (2 ^ (n+1) - 2)) * (thetaPairCount (n+1) D K : ℝ) := by
              rw [thetaPairCount_succ K, two_pow_succ_eq]
              simp only [Nat.cast_sum]


/-! ### The counting lemma -/

/-- **Peluse's counting lemma for `□_σ(H)`.**  If `H ⊆ [1,D]^σ × [1,D]^σ` has density at least `γ`,
then the set `ThetaSet σ D H` of `3σ`-tuples of `[1,D]` whose `2^σ` "corners" all lie in `H` has
cardinality at least `γ^{2^σ} · D^{3σ}`. -/
theorem thetaSet_card_ge {σ : ℕ} (hσ : 1 ≤ σ) {D : ℕ} (hD : 1 ≤ D)
    (H : Finset ((Fin σ → ℤ) × (Fin σ → ℤ))) {γ : ℝ} (hγ : 0 ≤ γ)
    (hH : ∀ p ∈ H, ∀ i : Fin σ, p.1 i ∈ Finset.Icc (1 : ℤ) (D : ℤ) ∧ p.2 i ∈ Finset.Icc (1 : ℤ) (D : ℤ))
    (hdens : γ * ((D : ℝ) ^ (2 * σ)) ≤ (H.card : ℝ)) :
    γ ^ (2 ^ σ) * ((D : ℝ) ^ (3 * σ)) ≤ ((Work.Peluse.Ulower.ThetaSet σ D H).card : ℝ) := by
  classical
  set n : ℕ := 2 ^ σ with hn
  have hn2 : 2 ≤ n := by
    rw [hn]
    have h1 := Nat.one_lt_two_pow (by omega : σ ≠ 0)
    omega
  have hDpos : (0:ℝ) < (D:ℝ) := by
    have h : (0:ℕ) < D := by omega
    exact_mod_cast h
  have hHbox : ∀ p ∈ H, p.1 ∈ thetaBox σ D ∧ p.2 ∈ thetaBox σ D := by
    intro p hp
    exact ⟨by rw [mem_thetaBox]; intro i; exact (hH p hp i).1,
           by rw [mem_thetaBox]; intro i; exact (hH p hp i).2⟩
  have hT : ((ThetaSet σ D H).card : ℝ)
      = ∑ k1 ∈ thetaBox σ D, (thetaPairCount σ D (thetaFibre D H k1) : ℝ) := by
    rw [thetaSet_card_eq, Nat.cast_sum]
  have hS : (H.card : ℝ) = ∑ k1 ∈ thetaBox σ D, ((thetaFibre D H k1).card : ℝ) := by
    rw [thetaFibre_card_eq hHbox, Nat.cast_sum]
  have hper : ∀ k1 ∈ thetaBox σ D,
      (((thetaFibre D H k1).card : ℝ) ^ n) ≤ (D:ℝ)^(σ * (n - 2)) *
        (thetaPairCount σ D (thetaFibre D H k1) : ℝ) := by
    intro k1 hk1
    have h := thetaPairCount_ge σ D hσ (thetaFibre D H k1) (thetaFibre_subset H k1)
    rwa [← hn] at h
  have hpm : ((∑ k1 ∈ thetaBox σ D, ((thetaFibre D H k1).card : ℝ)) ^ n)
      ≤ ((D:ℝ)^σ)^(n-1) *
        (∑ k1 ∈ thetaBox σ D, ((thetaFibre D H k1).card : ℝ)^n) := by
    have hn1 : 1 ≤ n := by omega
    have h := pow_sum_le_card_mul_sum_pow (s := thetaBox σ D)
        (f := fun k1 => ((thetaFibre D H k1).card : ℝ)) (fun i hi => by positivity) (n - 1)
    rwa [Nat.sub_add_cancel hn1, thetaBox_card_real] at h
  have hsum : (∑ k1 ∈ thetaBox σ D, ((thetaFibre D H k1).card : ℝ)^n)
      ≤ (D:ℝ)^(σ*(n-2)) *
        (∑ k1 ∈ thetaBox σ D, (thetaPairCount σ D (thetaFibre D H k1) : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k1 hk1 => hper k1 hk1
  have hcomb : (H.card : ℝ)^n ≤ (D:ℝ)^(σ*(2*n-3)) *
      (∑ k1 ∈ thetaBox σ D, (thetaPairCount σ D (thetaFibre D H k1) : ℝ)) := by
    have hexp1 : σ * (n - 1) + σ * (n - 2) = σ * (2 * n - 3) := by
      have h1 : (n - 1) + (n - 2) = 2 * n - 3 := by omega
      calc σ * (n - 1) + σ * (n - 2) = σ * ((n - 1) + (n - 2)) := by rw [Nat.mul_add]
        _ = σ * (2 * n - 3) := by rw [h1]
    calc (H.card : ℝ)^n
        = (∑ k1 ∈ thetaBox σ D, ((thetaFibre D H k1).card : ℝ))^n := by rw [hS]
      _ ≤ ((D:ℝ)^σ)^(n-1) * (∑ k1 ∈ thetaBox σ D, ((thetaFibre D H k1).card : ℝ)^n) :=
          hpm
      _ ≤ ((D:ℝ)^σ)^(n-1) * ((D:ℝ)^(σ*(n-2)) *
            (∑ k1 ∈ thetaBox σ D, (thetaPairCount σ D (thetaFibre D H k1) : ℝ))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (D:ℝ)^(σ*(2*n-3)) *
            (∑ k1 ∈ thetaBox σ D, (thetaPairCount σ D (thetaFibre D H k1) : ℝ)) := by
          rw [← mul_assoc, ← pow_mul, ← pow_add, hexp1]
  have hkey : γ^n * (D:ℝ)^(2*σ*n) ≤
      (D:ℝ)^(σ*(2*n-3)) * ((ThetaSet σ D H).card : ℝ) := by
    have h1 : (γ * (D:ℝ)^(2*σ))^n ≤ (H.card : ℝ)^n :=
      pow_le_pow_left₀ (by positivity) hdens n
    rw [mul_pow, ← pow_mul] at h1
    rw [hT]
    exact le_trans h1 hcomb
  have hswap : γ ^ n * (D:ℝ)^(3*σ) * (D:ℝ)^(σ*(2*n-3))
      ≤ ((ThetaSet σ D H).card : ℝ) * (D:ℝ)^(σ*(2*n-3)) := by
    have hexp2 : 3 * σ + σ * (2 * n - 3) ≤ 2 * σ * n := by
      have h1 : 3 + (2 * n - 3) ≤ 2 * n := by omega
      calc 3 * σ + σ * (2 * n - 3) = σ * 3 + σ * (2 * n - 3) := by ring
        _ = σ * (3 + (2 * n - 3)) := by rw [Nat.mul_add]
        _ ≤ σ * (2 * n) := Nat.mul_le_mul_left σ h1
        _ = 2 * σ * n := by ring
    calc γ ^ n * (D:ℝ)^(3*σ) * (D:ℝ)^(σ*(2*n-3))
        = γ ^ n * ((D:ℝ)^(3*σ) * (D:ℝ)^(σ*(2*n-3))) := by ring
      _ = γ ^ n * (D:ℝ)^(3*σ + σ*(2*n-3)) := by rw [pow_add]
      _ ≤ γ ^ n * (D:ℝ)^(2*σ*n) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact pow_le_pow_right₀ (by exact_mod_cast hD) hexp2
      _ ≤ (D:ℝ)^(σ*(2*n-3)) * ((ThetaSet σ D H).card : ℝ) := hkey
      _ = ((ThetaSet σ D H).card : ℝ) * (D:ℝ)^(σ*(2*n-3)) := by ring
  have hres := (mul_le_mul_iff_of_pos_right
    (show (0:ℝ) < (D:ℝ)^(σ*(2*n-3)) by positivity)).mp hswap
  exact hres

end

end Work.Peluse.Ulower
