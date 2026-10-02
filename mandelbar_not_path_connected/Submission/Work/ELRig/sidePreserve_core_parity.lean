/-
# ELRig — the horizontal crossing parity of `sidePreserve_core`

This file proves `Work.ELRig.sidePreserve_core_parity`: at a far-left level, the side of the
`α`-pair `P` of `Ψ u` and of `Ψ (u + 1)` agree.

The proof is the *even* analogue of the crossing parity of `Work.ELRig.side_of_odd_crossings`:

* the horizontal segment `[u, u+1]` (which lies in the half plane `{Re < -L.R}`) meets the two
  lifts `γ₁`, `γ₂` in a finite set `T` of crossing times; at a crossing time the side flips
  exactly when the crossing is *transversal* in the sense that the height function
  `s ↦ (γᵢ s).im` changes sign there (`Work.ELRig.side_flip_at_crossing` for `γ₁`,
  `Work.ELRig.side_flip_at_crossing_gamma2` for `γ₂`);
* the transversal crossings of the level `Im = u.im` with `γᵢ` in one period are **even** in
  number (`Work.ELRig.even_sign_changes`), and the crossing times of the segment are in bijection
  with the crossing parameters of one period (`level_window_shift_bij`);
* hence the number of flips is even, and `Work.ELRig.same_side_of_even_flips` (the walking lemma
  along `[u, u+1]`) gives that `Ψ u` and `Ψ (u+1)` are on the same side.
-/
import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.CylSides
import Submission.Work.ELRig.Sides
import Submission.Work.ELRig.Defs
import Submission.Work.ELRig.Flower
import Submission.Work.ELRig.side_flip_at_crossing
import Submission.Work.ELRig.side_flip_at_crossing_gamma2
import Submission.Work.ELRig.even_sign_changes
import Submission.Work.ELRig.sign_flip_of_two_components_horiz
import Submission.Work.ELRig.side_of_odd_crossings
import Submission.Work.ELRig.TailBand
import Submission.Work.ELRig.range_lift_closed
import Submission.Work.ELRig.level_window_shift_bij
import Submission.Work.ELRig.countable_level_set_exceptions

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

noncomputable section

namespace Work.ELRig

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ} {d : Work.EL.RootParabolic c}
variable {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}

/-! ## Elementary facts about the two lifts -/

/-- The two lifts are invariant under the shift `w ↦ w + 1`, in both directions. -/
theorem sp_lift_shift (L : RayCylLift d fl) (u : ℂ) :
    (u ∈ Set.range L.γ₁ ∪ Set.range L.γ₂) ↔
      (u + 1 ∈ Set.range L.γ₁ ∪ Set.range L.γ₂) := by
  constructor
  · rintro (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · exact Or.inl ⟨s + 1, L.per₁ s⟩
    · exact Or.inr ⟨s + 1, L.per₂ s⟩
  · rintro (⟨s, hs⟩ | ⟨s, hs⟩)
    · refine Or.inl ⟨s - 1, ?_⟩
      have h := L.per₁ (s - 1)
      rw [sub_add_cancel] at h
      rw [hs] at h
      exact (add_right_cancel h).symm
    · refine Or.inr ⟨s - 1, ?_⟩
      have h := L.per₂ (s - 1)
      rw [sub_add_cancel] at h
      rw [hs] at h
      exact (add_right_cancel h).symm

/-- **Case `u ∈ Λ`.**  Both `Ψ u` and `Ψ (u+1)` lie on the pair curve, hence in neither side. -/
theorem sp_sidePreserve_mem_lift (L : RayCylLift d fl) (P : Work.EL.CoPair d.hN)
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁)
    (hside : Work.EL.PairSides d.hN P) {u : ℂ} (hu : u.re < -L.R) (hu1 : u.re + 1 < -L.R)
    (huΛ : u ∈ Set.range L.γ₁ ∪ Set.range L.γ₂) :
    (fl.Ψ u ∈ Work.EL.pairSide P ↔ fl.Ψ (u + 1) ∈ Work.EL.pairSide P) := by
  have hu1Λ : u + 1 ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ := (sp_lift_shift L u).mp huΛ
  have hu1' : (u + 1).re < -L.R := by
    have : (u + 1).re = u.re + 1 := by simp
    rw [this]; exact hu1
  have h1 : fl.Ψ u ∈ Work.EL.pairCurve P :=
    (RayCylLift.preimage_pairCurve L P hPa hPb hPy u hu).mpr huΛ
  have h2 : fl.Ψ (u + 1) ∈ Work.EL.pairCurve P :=
    (RayCylLift.preimage_pairCurve L P hPa hPb hPy (u + 1) hu1').mpr hu1Λ
  exact ⟨fun h => (hside.notMem_curve_of_mem_far h h1).elim,
    fun h => (hside.notMem_curve_of_mem_far h h2).elim⟩

/-- The two lifts are disjoint: a point of `γ₁` is never a point of `γ₂`. -/
theorem sp_range_disjoint (L : RayCylLift d fl) :
    Disjoint (Set.range L.γ₁) (Set.range L.γ₂) := by
  rw [Set.disjoint_left]
  rintro z ⟨s, rfl⟩ ⟨s', hs'⟩
  have h1 : fl.Ψ (L.γ₁ s) ∈ Work.EL.paramRay d.hN Work.EL.alpha1 := L.img₁ s
  have h2 : fl.Ψ (L.γ₁ s) ∈ Work.EL.paramRay d.hN Work.EL.alpha2 := by
    rw [← hs']; exact L.img₂ s'
  have ha1 : Work.EL.alpha1 ∈ Set.Ico (0 : ℝ) 1 := by
    rw [Work.EL.alpha1]; norm_num
  have ha2 : Work.EL.alpha2 ∈ Set.Ico (0 : ℝ) 1 := by
    rw [Work.EL.alpha2]; norm_num
  have h3 : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ (L.γ₁ s))
      = Work.EL.alpha1 :=
    Work.Top.extAngle_of_mem_paramRay d.hN ha1.1 ha1.2 h1
  have h4 : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ (L.γ₁ s))
      = Work.EL.alpha2 :=
    Work.Top.extAngle_of_mem_paramRay d.hN ha2.1 ha2.2 h2
  have : Work.EL.alpha1 = Work.EL.alpha2 := by rw [← h3, h4]
  rw [Work.EL.alpha1, Work.EL.alpha2] at this
  norm_num at this

/-- `Cross` is invariant under negating both the function and the level. -/
theorem sp_Cross_neg {f : ℝ → ℝ} {c s : ℝ} :
    Cross (fun t => -f t) (-c) s ↔ Cross f c s := by
  have e1 : (∃ ε > 0, ∀ t ∈ Set.Ioo (s - ε) s, -c < -f t) ↔
      (∃ ε > 0, ∀ t ∈ Set.Ioo (s - ε) s, f t < c) := by
    constructor
    · rintro ⟨ε, hε, h⟩; exact ⟨ε, hε, fun t ht => by linarith [h t ht]⟩
    · rintro ⟨ε, hε, h⟩; exact ⟨ε, hε, fun t ht => by linarith [h t ht]⟩
  have e2 : (∃ ε > 0, ∀ t ∈ Set.Ioo s (s + ε), -f t < -c) ↔
      (∃ ε > 0, ∀ t ∈ Set.Ioo s (s + ε), c < f t) := by
    constructor
    · rintro ⟨ε, hε, h⟩; exact ⟨ε, hε, fun t ht => by linarith [h t ht]⟩
    · rintro ⟨ε, hε, h⟩; exact ⟨ε, hε, fun t ht => by linarith [h t ht]⟩
  have e3 : (∃ ε > 0, ∀ t ∈ Set.Ioo (s - ε) s, -f t < -c) ↔
      (∃ ε > 0, ∀ t ∈ Set.Ioo (s - ε) s, c < f t) := by
    constructor
    · rintro ⟨ε, hε, h⟩; exact ⟨ε, hε, fun t ht => by linarith [h t ht]⟩
    · rintro ⟨ε, hε, h⟩; exact ⟨ε, hε, fun t ht => by linarith [h t ht]⟩
  have e4 : (∃ ε > 0, ∀ t ∈ Set.Ioo s (s + ε), -c < -f t) ↔
      (∃ ε > 0, ∀ t ∈ Set.Ioo s (s + ε), f t < c) := by
    constructor
    · rintro ⟨ε, hε, h⟩; exact ⟨ε, hε, fun t ht => by linarith [h t ht]⟩
    · rintro ⟨ε, hε, h⟩; exact ⟨ε, hε, fun t ht => by linarith [h t ht]⟩
  simp only [Cross, LPos, RNeg, LNeg, RPos]
  constructor
  · rintro (h | h)
    · exact Or.inr ⟨e1.mp h.1, e2.mp h.2⟩
    · exact Or.inl ⟨e3.mp h.1, e4.mp h.2⟩
  · rintro (h | h)
    · exact Or.inr ⟨e3.mpr h.1, e4.mpr h.2⟩
    · exact Or.inl ⟨e1.mpr h.1, e2.mpr h.2⟩



/-- `Cross` in the raw form in which `side_flip_at_crossing` states the sign change. -/
theorem sp_Cross_iff {f : ℝ → ℝ} {c s : ℝ} :
    Cross f c s ↔
      ((∃ ε > 0, (∀ t ∈ Set.Ioo (s - ε) s, f t < c) ∧
          (∀ t ∈ Set.Ioo s (s + ε), c < f t)) ∨
        (∃ ε > 0, (∀ t ∈ Set.Ioo (s - ε) s, c < f t) ∧
          (∀ t ∈ Set.Ioo s (s + ε), f t < c))) := by
  simp only [Cross, LPos, RNeg, LNeg, RPos]
  constructor
  · rintro (h | h)
    · obtain ⟨⟨ε₁, hε₁, h₁⟩, ⟨ε₂, hε₂, h₂⟩⟩ := h
      refine Or.inr ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_, ?_⟩
      · intro t ht
        exact h₁ t ⟨by linarith [ht.1, min_le_left ε₁ ε₂], ht.2⟩
      · intro t ht
        exact h₂ t ⟨ht.1, by linarith [ht.2, min_le_right ε₁ ε₂]⟩
    · obtain ⟨⟨ε₁, hε₁, h₁⟩, ⟨ε₂, hε₂, h₂⟩⟩ := h
      refine Or.inl ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_, ?_⟩
      · intro t ht
        exact h₁ t ⟨by linarith [ht.1, min_le_left ε₁ ε₂], ht.2⟩
      · intro t ht
        exact h₂ t ⟨ht.1, by linarith [ht.2, min_le_right ε₁ ε₂]⟩
  · rintro (h | h)
    · obtain ⟨ε, hε, h₁, h₂⟩ := h
      exact Or.inr ⟨⟨ε, hε, h₁⟩, ⟨ε, hε, h₂⟩⟩
    · obtain ⟨ε, hε, h₁, h₂⟩ := h
      exact Or.inl ⟨⟨ε, hε, h₁⟩, ⟨ε, hε, h₂⟩⟩

/-! ## The parity walking lemma (even case)

The *even* analogue of `Work.ELRig.side_of_odd_crossings`: the crossing set `T ⊆ (0,b)` is split
into a subset `F` of *flipping* crossings (at which the two neighbouring points of the path lie on
opposite sides) and the remaining *non-flipping* ones.  If `#F` is even, the two endpoints of the
path lie on the same side. -/

theorem sp_side_same_of_even_flips {A B : Set ℂ} {σ : ℝ → ℂ} {b : ℝ} {T F : Finset ℝ}
    (hA : IsOpen A) (hB : IsOpen B) (hdisj : Disjoint A B) (hσ : Continuous σ) (hb : 0 < b)
    (hT0 : ∀ t ∈ T, 0 < t) (hTb : ∀ t ∈ T, t < b) (hFT : F ⊆ T)
    (hFflip : ∀ t ∈ F, ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε → t + δ ∈ Set.Icc (0 : ℝ) b →
      t - δ ∈ Set.Icc (0 : ℝ) b → t + δ ∉ T → t - δ ∉ T →
      (σ (t + δ) ∈ A ∧ σ (t - δ) ∈ B) ∨ (σ (t + δ) ∈ B ∧ σ (t - δ) ∈ A))
    (hnoflip : ∀ t ∈ T, t ∉ F → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
      t + δ ∈ Set.Icc (0 : ℝ) b ∧ t - δ ∈ Set.Icc (0 : ℝ) b ∧ t + δ ∉ T ∧ t - δ ∉ T ∧
      ((σ (t + δ) ∈ A ∧ σ (t - δ) ∈ A) ∨ (σ (t + δ) ∈ B ∧ σ (t - δ) ∈ B)))
    (hoff : ∀ t ∈ Set.Icc (0 : ℝ) b, t ∉ T → σ t ∈ A ∪ B)
    (heven : Even F.card) :
    (σ 0 ∈ A ↔ σ b ∈ A) := by
  classical
  by_cases hne : T.card = 0
  · -- `T` is empty: `[0, b]` is crossing free and connected
    have hTempty : T = ∅ := Finset.card_eq_zero.mp hne
    have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) b := ⟨le_rfl, le_of_lt hb⟩
    have hbI : b ∈ Set.Icc (0 : ℝ) b := ⟨le_of_lt hb, le_rfl⟩
    have hnoT : ∀ u ∈ Set.Icc (0 : ℝ) b, u ∉ T := by
      intro u hu; rw [hTempty]; simp
    exact side_iff_of_Icc hA hB hdisj hσ hoff h0I hbI (le_of_lt hb) hnoT
  · set n := T.card with hn
    have hnpos : 0 < n := by rw [hn]; exact Nat.pos_of_ne_zero hne
    let a : Fin n ↪o ℝ := T.orderEmbOfFin hn.symm
    have ha_mono : StrictMono (a : Fin n → ℝ) := a.strictMono
    have ha_mem : ∀ i : Fin n, a i ∈ T := fun i => Finset.orderEmbOfFin_mem T hn.symm i
    have ha_range : Set.range (a : Fin n → ℝ) = (T : Set ℝ) := Finset.range_orderEmbOfFin T hn.symm
    have ha0 : ∀ i : Fin n, 0 < a i := fun i => hT0 _ (ha_mem i)
    have hab : ∀ i : Fin n, a i < b := fun i => hTb _ (ha_mem i)
    have hbpos : 0 < b := lt_trans (ha0 ⟨0, hnpos⟩) (hab ⟨0, hnpos⟩)
    have ht_range : ∀ t ∈ T, ∃ i : Fin n, a i = t := by
      intro t ht
      have hmem : t ∈ Set.range (a : Fin n → ℝ) := by rw [ha_range]; exact ht
      exact hmem
    have hp_ge0 : ∀ j, j ≤ n → 0 ≤ p n a b j := by
      intro j hj
      have h1 := (p_mem ha_mono ha0 hab hnpos hj).1
      have h2 := q_ge_zero ha0 hbpos j
      linarith
    have hp_le_b : ∀ j, j ≤ n → p n a b j ≤ b := by
      intro j hj
      have h1 := (p_mem ha_mono ha0 hab hnpos hj).2
      have h2 := q_le_b hab hbpos (j+1)
      linarith
    have hpI : ∀ j, j ≤ n → p n a b j ∈ Set.Icc (0 : ℝ) b :=
      fun j hj => ⟨hp_ge0 j hj, hp_le_b j hj⟩
    -- the unique crossing in the `j`-th gap
    have hTmid : ∀ {j : ℕ} (hj : j < n) {u : ℝ},
        u ∈ Set.Icc (p n a b j) (p n a b (j+1)) → u ∈ T → u = a ⟨j, hj⟩ := by
      intro j hj u hu huT
      obtain ⟨i, hi⟩ := ht_range u huT
      have hqi : q n a b (i.val + 1) = u := (q_succ_of_lt i.isLt).trans hi
      have hpj : q n a b j < p n a b j := (p_mem ha_mono ha0 hab hnpos (le_of_lt hj)).1
      have hpj1 : p n a b (j+1) < q n a b (j+2) :=
        (p_mem ha_mono ha0 hab hnpos (by omega : j+1 ≤ n)).2
      have hlt1 : q n a b j < q n a b (i.val+1) := by rw [hqi]; exact lt_of_lt_of_le hpj hu.1
      have hlt2 : q n a b (i.val+1) < q n a b (j+2) := by rw [hqi]; exact lt_of_le_of_lt hu.2 hpj1
      have hji : j < i.val + 1 := by
        by_contra h
        push_neg at h
        exact absurd (q_mono_le ha_mono ha0 hab hnpos (i.val+1) j h (by omega)) (not_le.mpr hlt1)
      have hi2 : i.val + 1 < j + 2 := by
        by_contra h
        push_neg at h
        exact absurd (q_mono_le ha_mono ha0 hab hnpos (j+2) (i.val+1) h (by omega)) (not_le.mpr hlt2)
      have hiv : i.val = j := by omega
      have hfin : i = ⟨j, hj⟩ := Fin.ext hiv
      rw [hfin] at hi
      exact hi.symm
    have hTle0 : ∀ t ∈ T, p n a b 0 < t := by
      intro t ht
      obtain ⟨i, hi⟩ := ht_range t ht
      have hqi : q n a b (i.val + 1) = t := (q_succ_of_lt i.isLt).trans hi
      have hle : q n a b 1 ≤ q n a b (i.val + 1) :=
        q_mono_le ha_mono ha0 hab hnpos 1 (i.val+1) (by omega) (by omega)
      have hpq : p n a b 0 < q n a b 1 := (p_mem ha_mono ha0 hab hnpos (by omega : 0 ≤ n)).2
      rw [hqi] at hle
      linarith
    have hTltn : ∀ t ∈ T, t < p n a b n := by
      intro t ht
      obtain ⟨i, hi⟩ := ht_range t ht
      have hqi : q n a b (i.val + 1) = t := (q_succ_of_lt i.isLt).trans hi
      have hle : q n a b (i.val + 1) ≤ q n a b n :=
        q_mono_le ha_mono ha0 hab hnpos (i.val+1) n (by omega) (by omega)
      have hqn : q n a b n < p n a b n := (p_mem ha_mono ha0 hab hnpos le_rfl).1
      rw [hqi] at hle
      linarith
    -- `P j`: the side of `σ` at the `j`-th sample point
    let P : ℕ → Prop := fun j => σ (p n a b j) ∈ A
    have hPn : P n ↔ σ b ∈ A := by
      have hbI : b ∈ Set.Icc (0 : ℝ) b := ⟨le_of_lt hbpos, le_rfl⟩
      have hnoT : ∀ u ∈ Set.Icc (p n a b n) b, u ∉ T := by
        intro u hu huT
        exact absurd hu.1 (not_le.mpr (hTltn u huT))
      exact side_iff_of_Icc hA hB hdisj hσ hoff (hpI n le_rfl) hbI (hp_le_b n le_rfl) hnoT
    have hP0 : (σ 0 ∈ A) ↔ P 0 := by
      have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) b := ⟨le_rfl, le_of_lt hbpos⟩
      have hnoT : ∀ u ∈ Set.Icc (0 : ℝ) (p n a b 0), u ∉ T := by
        intro u hu huT
        exact absurd hu.2 (not_le.mpr (hTle0 u huT))
      exact side_iff_of_Icc hA hB hdisj hσ hoff h0I (hpI 0 (by omega)) (hp_ge0 0 (by omega)) hnoT
    -- the index set of flipping crossing times
    let K : Finset (Fin n) := Finset.univ.filter (fun i => a i ∈ F)
    have hKcard : K.card = F.card := by
      have himg : K.image (fun i => (a i : ℝ)) = F := by
        ext y
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, K]
        constructor
        · rintro ⟨i, hiF, rfl⟩; exact hiF
        · intro hyF
          have hyT : y ∈ T := hFT hyF
          have hymem : y ∈ Set.range (a : Fin n → ℝ) := by rw [ha_range]; exact hyT
          obtain ⟨i, hi⟩ := hymem
          exact ⟨i, by rwa [← hi] at hyF, hi⟩
      have hc : (K.image (fun i => (a i : ℝ))).card = K.card :=
        Finset.card_image_of_injective (f := fun i => (a i : ℝ)) K
          (fun i j hij => a.injective hij)
      rw [himg] at hc
      exact hc.symm
    -- the conditional step relation
    have hstep : ∀ j (hj : j < n),
        (P (j+1) ↔ (P j ↔ ¬ ((⟨j, hj⟩ : Fin n) ∈ K))) := by
      intro j hj
      have hmemK : ((⟨j, hj⟩ : Fin n) ∈ K) ↔ (a ⟨j, hj⟩ ∈ F) := by
        simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
      have hajq : a ⟨j, hj⟩ = q n a b (j+1) := (q_succ_of_lt hj).symm
      have hleft : p n a b j < a ⟨j, hj⟩ := by
        rw [hajq]; exact (p_mem ha_mono ha0 hab hnpos (le_of_lt hj)).2
      have hright : a ⟨j, hj⟩ < p n a b (j+1) := by
        rw [hajq]; exact (p_mem ha_mono ha0 hab hnpos (by omega : j+1 ≤ n)).1
      -- the relations between the two nearby points and the sample points
      have key : ∀ δ : ℝ, 0 < δ → δ < a ⟨j, hj⟩ - p n a b j → δ < p n a b (j+1) - a ⟨j, hj⟩ →
          ((σ (a ⟨j, hj⟩ - δ) ∈ A) ↔ P j) ∧ ((σ (a ⟨j, hj⟩ + δ) ∈ A) ↔ P (j+1)) := by
        intro δ hδ hδl hδr
        constructor
        · have hIJ : a ⟨j, hj⟩ - δ ∈ Set.Icc (0 : ℝ) b :=
            ⟨le_of_lt (lt_of_le_of_lt (hp_ge0 j (le_of_lt hj)) (by linarith)),
              le_of_lt (lt_trans (by linarith) (hab ⟨j, hj⟩))⟩
          have hnoT : ∀ u ∈ Set.Icc (p n a b j) (a ⟨j, hj⟩ - δ), u ∉ T := by
            intro u hu huT
            have hmem : u ∈ Set.Icc (p n a b j) (p n a b (j+1)) :=
              ⟨hu.1, le_of_lt (lt_of_le_of_lt hu.2 (by linarith))⟩
            have hthis := hTmid hj hmem huT
            rw [hthis] at hu
            linarith [hu.2, hδ]
          exact (side_iff_of_Icc hA hB hdisj hσ hoff (hpI j (le_of_lt hj)) hIJ
            (le_of_lt (by linarith)) hnoT).symm
        · have hIJ : a ⟨j, hj⟩ + δ ∈ Set.Icc (0 : ℝ) b :=
            ⟨le_of_lt (by linarith [ha0 ⟨j, hj⟩, hδ]),
              le_of_lt (lt_of_lt_of_le (by linarith) (hp_le_b (j+1) (by omega)))⟩
          have hnoT : ∀ u ∈ Set.Icc (a ⟨j, hj⟩ + δ) (p n a b (j+1)), u ∉ T := by
            intro u hu huT
            have hmem : u ∈ Set.Icc (p n a b j) (p n a b (j+1)) :=
              ⟨le_of_lt (lt_of_lt_of_le (by linarith) hu.1), hu.2⟩
            have hthis := hTmid hj hmem huT
            rw [hthis] at hu
            linarith [hu.1, hδ]
          exact side_iff_of_Icc hA hB hdisj hσ hoff hIJ (hpI (j+1) (by omega))
            (le_of_lt (by linarith)) hnoT
      by_cases hafF : a ⟨j, hj⟩ ∈ F
      · -- flipping crossing
        obtain ⟨ε, hεpos, hεflip⟩ := hFflip (a ⟨j, hj⟩) hafF
        set δ : ℝ := min (ε/2) (min ((a ⟨j, hj⟩ - p n a b j)/2) ((p n a b (j+1) - a ⟨j, hj⟩)/2))
          with hδdef
        have hδpos : 0 < δ := by
          rw [hδdef]
          exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
        have hδε : δ < ε := by
          rw [hδdef]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have hδl : δ < a ⟨j, hj⟩ - p n a b j := by
          rw [hδdef]
          exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) (by linarith)
        have hδr : δ < p n a b (j+1) - a ⟨j, hj⟩ := by
          rw [hδdef]
          exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)
        have hδIcc1 : a ⟨j, hj⟩ + δ ∈ Set.Icc (0 : ℝ) b :=
          ⟨le_of_lt (by linarith [ha0 ⟨j, hj⟩, hδpos]),
            le_of_lt (lt_of_lt_of_le (by linarith) (hp_le_b (j+1) (by omega)))⟩
        have hδIcc2 : a ⟨j, hj⟩ - δ ∈ Set.Icc (0 : ℝ) b :=
          ⟨le_of_lt (lt_of_le_of_lt (hp_ge0 j (le_of_lt hj)) (by linarith)),
            le_of_lt (lt_trans (by linarith) (hab ⟨j, hj⟩))⟩
        have hδnotT1 : a ⟨j, hj⟩ + δ ∉ T := by
          intro hT
          have hmem : a ⟨j, hj⟩ + δ ∈ Set.Icc (p n a b j) (p n a b (j+1)) :=
            ⟨le_of_lt (by linarith), le_of_lt (by linarith)⟩
          have hthis := hTmid hj hmem hT
          linarith [hδpos]
        have hδnotT2 : a ⟨j, hj⟩ - δ ∉ T := by
          intro hT
          have hmem : a ⟨j, hj⟩ - δ ∈ Set.Icc (p n a b j) (p n a b (j+1)) :=
            ⟨le_of_lt (by linarith), le_of_lt (by linarith)⟩
          have hthis := hTmid hj hmem hT
          linarith [hδpos]
        have hfl := hεflip δ hδpos hδε hδIcc1 hδIcc2 hδnotT1 hδnotT2
        have hkey := key δ hδpos hδl hδr
        have hrel : P (j+1) ↔ ¬ P j := by
          rcases hfl with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · constructor
            · intro _ hpj
              exact absurd (hkey.1.mpr hpj) (Set.disjoint_right.mp hdisj h2)
            · intro _
              exact hkey.2.mp h1
          · constructor
            · intro hpj1 _
              exact absurd (hkey.2.mpr hpj1) (Set.disjoint_right.mp hdisj h1)
            · intro hnpj
              exact absurd (hkey.1.mp h2) hnpj
        have hK : (⟨j, hj⟩ : Fin n) ∈ K := hmemK.mpr hafF
        simpa [hK] using hrel
      · -- non-flipping crossing
        have hgap : 0 < min (a ⟨j, hj⟩ - p n a b j) (p n a b (j+1) - a ⟨j, hj⟩) :=
          lt_min (by linarith) (by linarith)
        obtain ⟨δ, hδpos, hδlt, hδIcc1, hδIcc2, hδnotT1, hδnotT2, hfl⟩ :=
          hnoflip (a ⟨j, hj⟩) (ha_mem ⟨j, hj⟩) hafF
            (min (a ⟨j, hj⟩ - p n a b j) (p n a b (j+1) - a ⟨j, hj⟩) / 2) (by linarith)
        have hδl : δ < a ⟨j, hj⟩ - p n a b j := by
          have h1 : δ < min (a ⟨j, hj⟩ - p n a b j) (p n a b (j+1) - a ⟨j, hj⟩) / 2 := hδlt
          have h2 : min (a ⟨j, hj⟩ - p n a b j) (p n a b (j+1) - a ⟨j, hj⟩) / 2 ≤
              (a ⟨j, hj⟩ - p n a b j) / 2 := by
            have := min_le_left (a ⟨j, hj⟩ - p n a b j) (p n a b (j+1) - a ⟨j, hj⟩)
            linarith
          linarith
        have hδr : δ < p n a b (j+1) - a ⟨j, hj⟩ := by
          have h1 : δ < min (a ⟨j, hj⟩ - p n a b j) (p n a b (j+1) - a ⟨j, hj⟩) / 2 := hδlt
          have h2 : min (a ⟨j, hj⟩ - p n a b j) (p n a b (j+1) - a ⟨j, hj⟩) / 2 ≤
              (p n a b (j+1) - a ⟨j, hj⟩) / 2 := by
            have := min_le_right (a ⟨j, hj⟩ - p n a b j) (p n a b (j+1) - a ⟨j, hj⟩)
            linarith
          linarith
        have hkey := key δ hδpos hδl hδr
        have hrel : P j ↔ P (j+1) := by
          rcases hfl with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨fun _ => hkey.2.mp h1, fun _ => hkey.1.mp h2⟩
          · exact ⟨fun hpj => absurd (hkey.1.mpr hpj) (Set.disjoint_right.mp hdisj h2),
                   fun hpj1 => absurd (hkey.2.mpr hpj1) (Set.disjoint_right.mp hdisj h1)⟩
        have hnotK : (⟨j, hj⟩ : Fin n) ∉ K := fun h => hafF (hmemK.mp h)
        simpa [hnotK] using hrel.symm
    -- the number of flips among the first `j` crossing times
    set G : ℕ → ℕ := (fun j => (K.filter (fun i : Fin n => i.val < j)).card) with hGdef
    have hG0 : G 0 = 0 := by simp [hGdef]
    have hGn : G n = F.card := by
      have hfull : K.filter (fun i : Fin n => i.val < n) = K := by
        ext i
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.1, fun h => ⟨h, i.isLt⟩⟩
      simp only [hGdef, hfull, hKcard]
    have hGstep : ∀ j (hj : j < n),
        G (j+1) = G j + (if (⟨j, hj⟩ : Fin n) ∈ K then 1 else 0) := by
      intro j hj
      simp only [hGdef]
      have hsplit : K.filter (fun i : Fin n => i.val < j+1) =
          K.filter (fun i : Fin n => i.val < j) ∪
            K.filter (fun i : Fin n => i = ⟨j, hj⟩) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hiK, hi⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
          · exact Or.inl ⟨hiK, h⟩
          · exact Or.inr ⟨hiK, Fin.ext h⟩
        · rintro (⟨hiK, h⟩ | ⟨hiK, h⟩)
          · exact ⟨hiK, Nat.lt_succ_of_lt h⟩
          · exact ⟨hiK, by rw [h]; exact Nat.lt_succ_self j⟩
      have hdisjK : Disjoint (K.filter (fun i : Fin n => i.val < j))
          (K.filter (fun i : Fin n => i = ⟨j, hj⟩)) := by
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        rw [Finset.mem_filter] at hi1 hi2
        have h2 : i.val = j := by rw [hi2.2]
        omega
      have hcard_last : (K.filter (fun i : Fin n => i = ⟨j, hj⟩)).card =
          if (⟨j, hj⟩ : Fin n) ∈ K then 1 else 0 := by
        rw [Finset.filter_eq' K ⟨j, hj⟩]
        by_cases hc : (⟨j, hj⟩ : Fin n) ∈ K
        · rw [if_pos hc, if_pos hc, Finset.card_singleton]
        · rw [if_neg hc, if_neg hc, Finset.card_empty]
      rw [hsplit, Finset.card_union_of_disjoint hdisjK, hcard_last]
    have hEven_step : ∀ j (hj : j < n),
        Even (G (j+1)) ↔ (Even (G j) ↔ ¬ ((⟨j, hj⟩ : Fin n) ∈ K)) := by
      intro j hj
      have h := hGstep j hj
      by_cases hc : (⟨j, hj⟩ : Fin n) ∈ K
      · rw [h, if_pos hc]
        simp only [hc, not_true, iff_false, Nat.even_add_one]
      · rw [h, if_neg hc]
        simp only [hc, not_false_eq_true, iff_true, Nat.add_zero]
    have hpar : ∀ j, j ≤ n → (P j ↔ (P 0 ↔ Even (G j))) := by
      intro j
      induction j with
      | zero => intro _; rw [hG0]; simp
      | succ j ih =>
          intro hj
          have hj' : j < n := by omega
          have hih : P j ↔ (P 0 ↔ Even (G j)) := ih (by omega)
          rw [hstep j hj', hih, hEven_step j hj']
          tauto
    have hGn_even : Even (G n) := by rw [hGn]; exact heven
    have hstep1 : P n ↔ P 0 := by
      have h := hpar n le_rfl
      constructor
      · intro hpn
        exact (h.mp hpn).mpr hGn_even
      · intro hp0
        exact h.mpr ⟨fun _ => hGn_even, fun _ => hp0⟩
    exact ⟨fun h => hPn.mp (hstep1.mpr (hP0.mp h)),
      fun h => hP0.mpr (hstep1.mp (hPn.mpr h))⟩

/-! ## The parity count on the horizontal segment

For a fixed `u : ℂ` in the far-left half plane we walk along the horizontal segment `[u, u+1]`.
The crossing times are the images of the two *windows*

`Wᵢ = {s | (γᵢ s).im = u.im, u.re ≤ (γᵢ s).re < u.re + 1}`

under `βᵢ s = (γᵢ s).re - u.re`; the *flipping* crossings are those whose parameter is a sign
change of the height function (`Cross`).  The main counting statement is `sp_even_count`: when the
two windows are finite and contain evenly many sign changes, the number of flipping crossing times
is even. -/

/-- The window of parameters of the segment `[u, u+1]` for the first lift. -/
def spWindow₁ (L : RayCylLift d fl) (u : ℂ) : Set ℝ :=
  {s : ℝ | (L.γ₁ s).im = u.im ∧ u.re ≤ (L.γ₁ s).re ∧ (L.γ₁ s).re < u.re + 1}

/-- The window of parameters of the segment `[u, u+1]` for the second lift. -/
def spWindow₂ (L : RayCylLift d fl) (u : ℂ) : Set ℝ :=
  {s : ℝ | (L.γ₂ s).im = u.im ∧ u.re ≤ (L.γ₂ s).re ∧ (L.γ₂ s).re < u.re + 1}

/-- The crossing time of a parameter in the first window. -/
def spBeta₁ (L : RayCylLift d fl) (u : ℂ) (s : ℝ) : ℝ := (L.γ₁ s).re - u.re

/-- The crossing time of a parameter in the second window. -/
def spBeta₂ (L : RayCylLift d fl) (u : ℂ) (s : ℝ) : ℝ := (L.γ₂ s).re - u.re

variable {u : ℂ}

/-- A parameter of the first window gives a point of the segment on the first lift. -/
theorem sp_beta₁_mem (L : RayCylLift d fl) (hu : u.re < -L.R - 1) {s : ℝ}
    (hs : s ∈ spWindow₁ L u) : u + ((spBeta₁ L u s : ℝ) : ℂ) = L.γ₁ s := by
  have him : (L.γ₁ s).im = u.im := hs.1
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, spBeta₁]
    ring
  · simp only [Complex.add_im, Complex.ofReal_im, spBeta₁]
    rw [him]
    ring

/-- A parameter of the second window gives a point of the segment on the second lift. -/
theorem sp_beta₂_mem (L : RayCylLift d fl) (hu : u.re < -L.R - 1) {s : ℝ}
    (hs : s ∈ spWindow₂ L u) : u + ((spBeta₂ L u s : ℝ) : ℂ) = L.γ₂ s := by
  have him : (L.γ₂ s).im = u.im := hs.1
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, spBeta₂]
    ring
  · simp only [Complex.add_im, Complex.ofReal_im, spBeta₂]
    rw [him]
    ring

/-- `spBeta₁` is injective on the first window. -/
theorem sp_beta₁_inj (L : RayCylLift d fl) (hu : u.re < -L.R - 1) :
    Set.InjOn (spBeta₁ L u) (spWindow₁ L u) := by
  intro s hs s' hs' h
  have hre : (L.γ₁ s).re = (L.γ₁ s').re := by
    have := h
    simp only [spBeta₁] at this
    linarith
  have him : (L.γ₁ s).im = (L.γ₁ s').im := by rw [hs.1, hs'.1]
  exact injective₁ L s s' (Complex.ext hre him)

/-- `spBeta₂` is injective on the second window. -/
theorem sp_beta₂_inj (L : RayCylLift d fl) (hu : u.re < -L.R - 1) :
    Set.InjOn (spBeta₂ L u) (spWindow₂ L u) := by
  intro s hs s' hs' h
  have hre : (L.γ₂ s).re = (L.γ₂ s').re := by
    have := h
    simp only [spBeta₂] at this
    linarith
  have him : (L.γ₂ s).im = (L.γ₂ s').im := by rw [hs.1, hs'.1]
  have h2 : L.γ₂ s = L.γ₂ s' := Complex.ext hre him
  rw [L.anti s, L.anti s'] at h2
  have := add_right_cancel h2
  have h3 : star (L.γ₁ s) = star (L.γ₁ s') := this
  exact injective₁ L s s' (star_inj.mp h3)



/-- An element of a finite set of reals is isolated in it. -/
theorem sp_isolated {T : Finset ℝ} {τ : ℝ} (hτ : τ ∈ T) :
    ∃ dd > 0, ∀ x ∈ T, x ≠ τ → dd ≤ |x - τ| := by
  by_cases hne : (T.erase τ).Nonempty
  · refine ⟨(T.erase τ).inf' hne (fun x => |x - τ|), ?_, ?_⟩
    · refine (Finset.lt_inf'_iff (s := T.erase τ) (H := hne)
        (f := fun x => |x - τ|) (a := 0)).mpr ?_
      intro x hx
      rw [Finset.mem_erase] at hx
      exact abs_pos.mpr (sub_ne_zero.mpr hx.1)
    · intro x hx hxne
      exact Finset.inf'_le _ (Finset.mem_erase.mpr ⟨hxne, hx⟩)
  · refine ⟨1, one_pos, fun x hx hxne => ?_⟩
    exfalso
    exact hne ⟨x, Finset.mem_erase.mpr ⟨hxne, hx⟩⟩

/-- The **conditional parity statement of the horizontal segment**: if the two windows of the
segment `[u, u+1]` are finite and contain evenly many sign changes of the height functions, then
`Ψ u` and `Ψ (u+1)` lie on the same side of the `α`-pair `P`. -/
theorem sp_sidePreserve_good {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (L : RayCylLift d fl) (P : Work.EL.CoPair d.hN)
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁)
    (hside : Work.EL.PairSides d.hN P)
    {u : ℂ} (hu : u.re < -L.R - 1)
    (huΛ : u ∉ Set.range L.γ₁ ∪ Set.range L.γ₂)
    (hW₁fin : (spWindow₁ L u).Finite)
    (hcross₁fin : (spWindow₁ L u ∩ {s : ℝ | Cross (fun t : ℝ => (L.γ₁ t).im) u.im s}).Finite)
    (heven₁ : Even ((spWindow₁ L u ∩ {s : ℝ | Cross (fun t : ℝ => (L.γ₁ t).im) u.im s}).ncard))
    (hW₂fin : (spWindow₂ L u).Finite)
    (hcross₂fin : (spWindow₂ L u ∩ {s : ℝ | Cross (fun t : ℝ => (L.γ₂ t).im) u.im s}).Finite)
    (heven₂ : Even ((spWindow₂ L u ∩ {s : ℝ | Cross (fun t : ℝ => (L.γ₂ t).im) u.im s}).ncard)) :
    (fl.Ψ u ∈ Work.EL.pairSide P ↔ fl.Ψ (u + 1) ∈ Work.EL.pairSide P) := by
  classical
  have huH : u.re < -L.R := by linarith
  have hu1Λ : u + 1 ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ := fun h => huΛ ((sp_lift_shift L u).mpr h)
  set W₁ : Set ℝ := spWindow₁ L u with hW₁
  set W₂ : Set ℝ := spWindow₂ L u with hW₂
  set W₁F : Finset ℝ := hW₁fin.toFinset with hW₁F
  set W₂F : Finset ℝ := hW₂fin.toFinset with hW₂F
  have hmemW₁ : ∀ s : ℝ, s ∈ W₁F ↔ s ∈ W₁ := fun s => by
    rw [hW₁F]; exact Set.Finite.mem_toFinset hW₁fin
  have hmemW₂ : ∀ s : ℝ, s ∈ W₂F ↔ s ∈ W₂ := fun s => by
    rw [hW₂F]; exact Set.Finite.mem_toFinset hW₂fin
  set T₁ : Finset ℝ := W₁F.image (spBeta₁ L u) with hT₁
  set T₂ : Finset ℝ := W₂F.image (spBeta₂ L u) with hT₂
  set T : Finset ℝ := T₁ ∪ T₂ with hT
  set C₁ : Finset ℝ :=
    (W₁F.filter (fun s : ℝ => Cross (fun t : ℝ => (L.γ₁ t).im) u.im s)).image (spBeta₁ L u)
    with hC₁
  set C₂ : Finset ℝ :=
    (W₂F.filter (fun s : ℝ => Cross (fun t : ℝ => (L.γ₂ t).im) u.im s)).image (spBeta₂ L u)
    with hC₂
  set F : Finset ℝ := C₁ ∪ C₂ with hF
  have hmemT₁ : ∀ τ : ℝ, τ ∈ T₁ ↔ ∃ s ∈ W₁, spBeta₁ L u s = τ := by
    intro τ
    rw [hT₁, Finset.mem_image]
    constructor
    · rintro ⟨s, hs, hst⟩; exact ⟨s, (hmemW₁ s).mp hs, hst⟩
    · rintro ⟨s, hs, hst⟩; exact ⟨s, (hmemW₁ s).mpr hs, hst⟩
  have hmemT₂ : ∀ τ : ℝ, τ ∈ T₂ ↔ ∃ s ∈ W₂, spBeta₂ L u s = τ := by
    intro τ
    rw [hT₂, Finset.mem_image]
    constructor
    · rintro ⟨s, hs, hst⟩; exact ⟨s, (hmemW₂ s).mp hs, hst⟩
    · rintro ⟨s, hs, hst⟩; exact ⟨s, (hmemW₂ s).mpr hs, hst⟩
  have hmemT : ∀ τ : ℝ, τ ∈ T ↔ τ ∈ T₁ ∨ τ ∈ T₂ := fun τ => by rw [hT, Finset.mem_union]
  have hmemC₁ : ∀ τ : ℝ, τ ∈ C₁ ↔
      ∃ s ∈ W₁, Cross (fun t : ℝ => (L.γ₁ t).im) u.im s ∧ spBeta₁ L u s = τ := by
    intro τ
    rw [hC₁, Finset.mem_image]
    constructor
    · rintro ⟨s, hs, hst⟩
      rw [Finset.mem_filter] at hs
      exact ⟨s, (hmemW₁ s).mp hs.1, hs.2, hst⟩
    · rintro ⟨s, hs, hcr, hst⟩
      exact ⟨s, Finset.mem_filter.mpr ⟨(hmemW₁ s).mpr hs, hcr⟩, hst⟩
  have hmemC₂ : ∀ τ : ℝ, τ ∈ C₂ ↔
      ∃ s ∈ W₂, Cross (fun t : ℝ => (L.γ₂ t).im) u.im s ∧ spBeta₂ L u s = τ := by
    intro τ
    rw [hC₂, Finset.mem_image]
    constructor
    · rintro ⟨s, hs, hst⟩
      rw [Finset.mem_filter] at hs
      exact ⟨s, (hmemW₂ s).mp hs.1, hs.2, hst⟩
    · rintro ⟨s, hs, hcr, hst⟩
      exact ⟨s, Finset.mem_filter.mpr ⟨(hmemW₂ s).mpr hs, hcr⟩, hst⟩
  have hmemF : ∀ τ : ℝ, τ ∈ F ↔ τ ∈ C₁ ∨ τ ∈ C₂ := fun τ => by rw [hF, Finset.mem_union]
  have hFT : F ⊆ T := by
    intro τ hτ
    rw [hmemF] at hτ
    rcases hτ with h | h
    · rw [hmemC₁] at h
      obtain ⟨s, hs, _, hst⟩ := h
      rw [hmemT]; left; rw [hmemT₁]; exact ⟨s, hs, hst⟩
    · rw [hmemC₂] at h
      obtain ⟨s, hs, _, hst⟩ := h
      rw [hmemT]; right; rw [hmemT₂]; exact ⟨s, hs, hst⟩
  have hb₁mem : ∀ {s τ : ℝ}, s ∈ W₁ → spBeta₁ L u s = τ → u + (τ : ℂ) = L.γ₁ s := by
    intro s τ hs h
    rw [← h]
    exact sp_beta₁_mem L hu hs
  have hb₂mem : ∀ {s τ : ℝ}, s ∈ W₂ → spBeta₂ L u s = τ → u + (τ : ℂ) = L.γ₂ s := by
    intro s τ hs h
    rw [← h]
    exact sp_beta₂_mem L hu hs
  have hmemT₁' : ∀ τ ∈ T, τ ∈ T₁ ∨ τ ∈ T₂ := fun τ hτ => (hmemT τ).mp hτ
  have hT_lift : ∀ τ ∈ T, u + (τ : ℂ) ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
    intro τ hτ
    rcases hmemT₁' τ hτ with h | h
    · rw [hmemT₁] at h
      obtain ⟨s, hs, hst⟩ := h
      exact Or.inl ⟨s, (hb₁mem hs hst).symm⟩
    · rw [hmemT₂] at h
      obtain ⟨s, hs, hst⟩ := h
      exact Or.inr ⟨s, (hb₂mem hs hst).symm⟩
  have hnotT_lift : ∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) 1 → τ ∉ T →
      u + (τ : ℂ) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
    intro τ hτ hτT
    rintro (⟨s, hs⟩ | ⟨s, hs⟩)
    · have hre : (L.γ₁ s).re = u.re + τ := by
        have h := congrArg Complex.re hs
        simp only [Complex.add_re, Complex.ofReal_re] at h
        linarith
      have him : (L.γ₁ s).im = u.im := by
        have h := congrArg Complex.im hs
        simp only [Complex.add_im, Complex.ofReal_im, add_zero] at h
        linarith
      rcases lt_or_eq_of_le hτ.2 with hlt | heq
      · have hsW : s ∈ W₁ := by
          refine ⟨him, ?_, ?_⟩
          · rw [hre]; linarith [hτ.1]
          · rw [hre]; linarith
        exact hτT (by
          rw [hmemT]; left; rw [hmemT₁]
          exact ⟨s, hsW, by simp only [spBeta₁]; rw [hre]; ring⟩)
      · exact hu1Λ (Or.inl ⟨s, by rw [hs, heq]; simp⟩)
    · have hre : (L.γ₂ s).re = u.re + τ := by
        have h := congrArg Complex.re hs
        simp only [Complex.add_re, Complex.ofReal_re] at h
        linarith
      have him : (L.γ₂ s).im = u.im := by
        have h := congrArg Complex.im hs
        simp only [Complex.add_im, Complex.ofReal_im, add_zero] at h
        linarith
      rcases lt_or_eq_of_le hτ.2 with hlt | heq
      · have hsW : s ∈ W₂ := by
          refine ⟨him, ?_, ?_⟩
          · rw [hre]; linarith [hτ.1]
          · rw [hre]; linarith
        exact hτT (by
          rw [hmemT]; right; rw [hmemT₂]
          exact ⟨s, hsW, by simp only [spBeta₂]; rw [hre]; ring⟩)
      · exact hu1Λ (Or.inr ⟨s, by rw [hs, heq]; simp⟩)
  have hT0 : ∀ τ ∈ T, 0 < τ := by
    intro τ hτ
    rcases hmemT₁' τ hτ with h | h
    · rw [hmemT₁] at h
      obtain ⟨s, hs, hst⟩ := h
      have hτeq : τ = (L.γ₁ s).re - u.re := by rw [← hst]; rfl
      have hge : u.re ≤ (L.γ₁ s).re := hs.2.1
      have hne : τ ≠ 0 := by
        intro h0
        have h := hb₁mem hs hst
        rw [h0] at h
        simp only [Complex.ofReal_zero, add_zero] at h
        exact huΛ (Or.inl ⟨s, h.symm⟩)
      have hge' : (0 : ℝ) ≤ τ := by rw [hτeq]; linarith
      exact lt_of_le_of_ne hge' (Ne.symm hne)
    · rw [hmemT₂] at h
      obtain ⟨s, hs, hst⟩ := h
      have hτeq : τ = (L.γ₂ s).re - u.re := by rw [← hst]; rfl
      have hge : u.re ≤ (L.γ₂ s).re := hs.2.1
      have hne : τ ≠ 0 := by
        intro h0
        have h := hb₂mem hs hst
        rw [h0] at h
        simp only [Complex.ofReal_zero, add_zero] at h
        exact huΛ (Or.inr ⟨s, h.symm⟩)
      have hge' : (0 : ℝ) ≤ τ := by rw [hτeq]; linarith
      exact lt_of_le_of_ne hge' (Ne.symm hne)
  have hTb : ∀ τ ∈ T, τ < 1 := by
    intro τ hτ
    rcases hmemT₁' τ hτ with h | h
    · rw [hmemT₁] at h
      obtain ⟨s, hs, hst⟩ := h
      have hτeq : τ = (L.γ₁ s).re - u.re := by rw [← hst]; rfl
      have hlt : (L.γ₁ s).re < u.re + 1 := hs.2.2
      rw [hτeq]; linarith
    · rw [hmemT₂] at h
      obtain ⟨s, hs, hst⟩ := h
      have hτeq : τ = (L.γ₂ s).re - u.re := by rw [← hst]; rfl
      have hlt : (L.γ₂ s).re < u.re + 1 := hs.2.2
      rw [hτeq]; linarith
  have hnotcurve : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → t ∉ T →
      fl.Ψ (u + (t : ℂ)) ∉ Work.EL.pairCurve P := by
    intro t ht htT hc
    have hre : (u + (t : ℂ)).re < -L.R := by
      simp only [Complex.add_re, Complex.ofReal_re]; linarith [ht.2]
    exact (hnotT_lift t ht htT)
      ((RayCylLift.preimage_pairCurve L P hPa hPb hPy (u + (t : ℂ)) hre).mp hc)
  -- isolation of the crossing times
  have hiso : ∀ τ ∈ T, ∃ dd > 0, ∀ x ∈ T, x ≠ τ → dd ≤ |x - τ| := fun τ hτ => sp_isolated hτ
  -- simplicity of each crossing in the horizontal line
  have hsimple : ∀ τ ∈ T, ∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
      u + ((τ + t : ℝ) : ℂ) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ ∧
      u + ((τ - t : ℝ) : ℂ) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
    intro τ hτ
    obtain ⟨dd, hddpos, hdd⟩ := hiso τ hτ
    have hτpos : 0 < τ := hT0 τ hτ
    have hτlt : τ < 1 := hTb τ hτ
    refine ⟨min (min (dd / 2) (τ / 2)) ((1 - τ) / 2), ?_, ?_⟩
    · exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
    · intro t ht
      have h1 : min (min (dd / 2) (τ / 2)) ((1 - τ) / 2) ≤ dd / 2 :=
        le_trans (min_le_left _ _) (min_le_left _ _)
      have ht1 : t < τ / 2 := lt_of_lt_of_le ht.2 (le_trans (min_le_left _ _) (min_le_right _ _))
      have ht2 : t < (1 - τ) / 2 := lt_of_lt_of_le ht.2 (min_le_right _ _)
      have htd : t < dd / 2 := lt_of_lt_of_le ht.2 h1
      have hmem1 : τ + t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith [ht.1, ht.2, hτpos, hτlt, ht1, ht2],
         by linarith [ht.1, ht.2, hτpos, hτlt, ht1, ht2]⟩
      have hmem2 : τ - t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith [ht.1, ht.2, hτpos, hτlt, ht1, ht2],
         by linarith [ht.1, ht.2, hτpos, hτlt, ht1, ht2]⟩
      have hnot1 : τ + t ∉ T := by
        intro hc
        have hne : τ + t ≠ τ := by linarith [ht.1]
        have h2 := hdd (τ + t) hc hne
        have h3 : |τ + t - τ| = t := by rw [show τ + t - τ = t by ring, abs_of_pos ht.1]
        rw [h3] at h2
        linarith
      have hnot2 : τ - t ∉ T := by
        intro hc
        have hne : τ - t ≠ τ := by linarith [ht.1]
        have h2 := hdd (τ - t) hc hne
        have h3 : |τ - t - τ| = t := by
          rw [show τ - t - τ = -t by ring, abs_neg, abs_of_pos ht.1]
        rw [h3] at h2
        linarith
      exact ⟨hnotT_lift _ hmem1 hnot1, hnotT_lift _ hmem2 hnot2⟩
  -- the flip datum of a crossing, in the coordinates of the segment
  have hflipdata : ∀ (τ s : ℝ), s ∈ W₁ → spBeta₁ L u s = τ →
      ((∃ t ∈ Set.Ioo (0 : ℝ) 1, True) ∨ True) → True := fun _ _ _ _ _ => trivial
  -- the flipping crossings
  have hflip : ∀ τ ∈ F, ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε →
      τ + δ ∈ Set.Icc (0 : ℝ) 1 → τ - δ ∈ Set.Icc (0 : ℝ) 1 → τ + δ ∉ T → τ - δ ∉ T →
      (fl.Ψ (u + ((τ + δ : ℝ) : ℂ)) ∈ Work.EL.pairSide P ∧
        fl.Ψ (u + ((τ - δ : ℝ) : ℂ)) ∈ Work.EL.pairSideNear P) ∨
      (fl.Ψ (u + ((τ + δ : ℝ) : ℂ)) ∈ Work.EL.pairSideNear P ∧
        fl.Ψ (u + ((τ - δ : ℝ) : ℂ)) ∈ Work.EL.pairSide P) := by
    intro τ hτ
    rw [hmemF] at hτ
    rcases hτ with hτ | hτ
    · -- first lift
      rw [hmemC₁] at hτ
      obtain ⟨s, hsW, hcross, hbs⟩ := hτ
      have hτT : τ ∈ T := by
        rw [hmemT]; left; rw [hmemT₁]; exact ⟨s, hsW, hbs⟩
      have hre : (L.γ₁ s).re < -L.R := by linarith [hsW.2.2]
      obtain ⟨δ, hδp, hδ⟩ := hsimple τ hτT
      have hδs : ∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
          L.γ₁ s + (t : ℂ) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ ∧
          L.γ₁ s - (t : ℂ) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
        refine ⟨δ, hδp, fun t ht => ?_⟩
        have e1 : L.γ₁ s + (t : ℂ) = u + (((τ + t : ℝ)) : ℂ) := by
          have h := hb₁mem hsW hbs
          rw [← h]; push_cast; ring
        have e2 : L.γ₁ s - (t : ℂ) = u + (((τ - t : ℝ)) : ℂ) := by
          have h := hb₁mem hsW hbs
          rw [← h]; push_cast; ring
        rw [e1, e2]
        exact hδ t ht
      have hcross' : Cross (fun t : ℝ => (L.γ₁ t).im) ((L.γ₁ s).im) s := by
        rw [hsW.1]; exact hcross
      have hcross'' := (sp_Cross_iff (f := fun t : ℝ => (L.γ₁ t).im)
        (c := (L.γ₁ s).im) (s := s)).mp hcross'
      obtain ⟨ε, hεpos, hε⟩ :=
        (side_flip_at_crossing d fl L P hPa hPb hPy hside hre hδs).mp hcross''
      refine ⟨ε, hεpos, fun δ' hδ' hδε h1 h2 h3 h4 => ?_⟩
      have e1 : L.γ₁ s + (δ' : ℂ) = u + ((τ + δ' : ℝ) : ℂ) := by
        have h := hb₁mem hsW hbs
        rw [← h]; push_cast; ring
      have e2 : L.γ₁ s - (δ' : ℂ) = u + ((τ - δ' : ℝ) : ℂ) := by
        have h := hb₁mem hsW hbs
        rw [← h]; push_cast; ring
      have hf := hε δ' ⟨hδ', hδε⟩
      rw [e1, e2] at hf
      by_cases hA : fl.Ψ (u + ((τ + δ' : ℝ) : ℂ)) ∈ Work.EL.pairSide P
      · by_cases hB : fl.Ψ (u + ((τ - δ' : ℝ) : ℂ)) ∈ Work.EL.pairSide P
        · exact absurd hB (hf.mp hA)
        · refine Or.inl ⟨hA, ?_⟩
          rcases hside.mem_or_mem (hnotcurve _ h2 h4) with h | h
          · exact absurd h hB
          · exact h
      · by_cases hB : fl.Ψ (u + ((τ - δ' : ℝ) : ℂ)) ∈ Work.EL.pairSide P
        · refine Or.inr ⟨?_, hB⟩
          rcases hside.mem_or_mem (hnotcurve _ h1 h3) with h | h
          · exact absurd h hA
          · exact h
        · exact absurd (hf.mpr hB) hA
    · -- second lift
      rw [hmemC₂] at hτ
      obtain ⟨s, hsW, hcross, hbs⟩ := hτ
      have hτT : τ ∈ T := by
        rw [hmemT]; right; rw [hmemT₂]; exact ⟨s, hsW, hbs⟩
      have hre : (L.γ₂ s).re < -L.R := by linarith [hsW.2.2]
      obtain ⟨δ, hδp, hδ⟩ := hsimple τ hτT
      have hδs : ∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
          L.γ₂ s + (t : ℂ) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ ∧
          L.γ₂ s - (t : ℂ) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
        refine ⟨δ, hδp, fun t ht => ?_⟩
        have e1 : L.γ₂ s + (t : ℂ) = u + (((τ + t : ℝ)) : ℂ) := by
          have h := hb₂mem hsW hbs
          rw [← h]; push_cast; ring
        have e2 : L.γ₂ s - (t : ℂ) = u + (((τ - t : ℝ)) : ℂ) := by
          have h := hb₂mem hsW hbs
          rw [← h]; push_cast; ring
        rw [e1, e2]
        exact hδ t ht
      have hcross' : Cross (fun t : ℝ => (L.γ₂ t).im) ((L.γ₂ s).im) s := by
        rw [hsW.1]; exact hcross
      have hcross'' := (sp_Cross_iff (f := fun t : ℝ => (L.γ₂ t).im)
        (c := (L.γ₂ s).im) (s := s)).mp hcross'
      obtain ⟨ε, hεpos, hε⟩ :=
        (side_flip_at_crossing_gamma2 d fl L P hPa hPb hPy hside hre hδs).mp hcross''
      refine ⟨ε, hεpos, fun δ' hδ' hδε h1 h2 h3 h4 => ?_⟩
      have e1 : L.γ₂ s + (δ' : ℂ) = u + ((τ + δ' : ℝ) : ℂ) := by
        have h := hb₂mem hsW hbs
        rw [← h]; push_cast; ring
      have e2 : L.γ₂ s - (δ' : ℂ) = u + ((τ - δ' : ℝ) : ℂ) := by
        have h := hb₂mem hsW hbs
        rw [← h]; push_cast; ring
      have hf := hε δ' ⟨hδ', hδε⟩
      rw [e1, e2] at hf
      by_cases hA : fl.Ψ (u + ((τ + δ' : ℝ) : ℂ)) ∈ Work.EL.pairSide P
      · by_cases hB : fl.Ψ (u + ((τ - δ' : ℝ) : ℂ)) ∈ Work.EL.pairSide P
        · exact absurd hB (hf.mp hA)
        · refine Or.inl ⟨hA, ?_⟩
          rcases hside.mem_or_mem (hnotcurve _ h2 h4) with h | h
          · exact absurd h hB
          · exact h
      · by_cases hB : fl.Ψ (u + ((τ - δ' : ℝ) : ℂ)) ∈ Work.EL.pairSide P
        · refine Or.inr ⟨?_, hB⟩
          rcases hside.mem_or_mem (hnotcurve _ h1 h3) with h | h
          · exact absurd h hA
          · exact h
        · exact absurd (hf.mpr hB) hA
  -- the non-flipping crossings
  have hnoflip : ∀ τ ∈ T, τ ∉ F → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
      τ + δ ∈ Set.Icc (0 : ℝ) 1 ∧ τ - δ ∈ Set.Icc (0 : ℝ) 1 ∧ τ + δ ∉ T ∧ τ - δ ∉ T ∧
      ((fl.Ψ (u + ((τ + δ : ℝ) : ℂ)) ∈ Work.EL.pairSide P ∧
          fl.Ψ (u + ((τ - δ : ℝ) : ℂ)) ∈ Work.EL.pairSide P) ∨
        (fl.Ψ (u + ((τ + δ : ℝ) : ℂ)) ∈ Work.EL.pairSideNear P ∧
          fl.Ψ (u + ((τ - δ : ℝ) : ℂ)) ∈ Work.EL.pairSideNear P)) := by
    intro τ hτ hτF ε hε
    obtain ⟨dd, hddpos, hdd⟩ := hiso τ hτ
    have hτpos : 0 < τ := hT0 τ hτ
    have hτlt : τ < 1 := hTb τ hτ
    set ε' : ℝ := min (min (ε / 2) (dd / 2)) (min (τ / 2) ((1 - τ) / 2)) / 2 with hε'def
    have hε'pos : 0 < ε' := by
      rw [hε'def]
      exact div_pos (lt_min (lt_min (by linarith) (by linarith))
        (lt_min (by linarith) (by linarith))) (by norm_num)
    have hε'ε : ε' < ε := by
      rw [hε'def]
      have h1 : min (min (ε / 2) (dd / 2)) (min (τ / 2) ((1 - τ) / 2)) ≤ ε / 2 :=
        le_trans (min_le_left _ _) (min_le_left _ _)
      linarith
    have hε'd : ε' < dd := by
      rw [hε'def]
      have h1 : min (min (ε / 2) (dd / 2)) (min (τ / 2) ((1 - τ) / 2)) ≤ dd / 2 :=
        le_trans (min_le_left _ _) (min_le_right _ _)
      linarith
    have hε'τ : ε' < τ / 2 := by
      rw [hε'def]
      have h1 : min (min (ε / 2) (dd / 2)) (min (τ / 2) ((1 - τ) / 2)) ≤ τ / 2 :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      linarith [hτpos]
    have hε'1 : ε' < (1 - τ) / 2 := by
      rw [hε'def]
      have h1 : min (min (ε / 2) (dd / 2)) (min (τ / 2) ((1 - τ) / 2)) ≤ (1 - τ) / 2 :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      linarith [hτlt]
    rcases hmemT₁' τ hτ with hτ | hτ
    · -- first lift
      rw [hmemT₁] at hτ
      obtain ⟨s, hsW, hbs⟩ := hτ
      have hre : (L.γ₁ s).re < -L.R := by linarith [hsW.2.2]
      have hncross : ¬ Cross (fun t : ℝ => (L.γ₁ t).im) u.im s := by
        intro hc
        exact hτF (by
          rw [hmemF]; left; rw [hmemC₁]
          exact ⟨s, hsW, hc, hbs⟩)
      obtain ⟨δf, hδfp, hδf⟩ := hsimple τ (by
        rw [hmemT]; left; rw [hmemT₁]; exact ⟨s, hsW, hbs⟩)
      have hδfs : ∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
          L.γ₁ s + (t : ℂ) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ ∧
          L.γ₁ s - (t : ℂ) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
        refine ⟨δf, hδfp, fun t ht => ?_⟩
        have e1 : L.γ₁ s + (t : ℂ) = u + (((τ + t : ℝ)) : ℂ) := by
          have h := hb₁mem hsW hbs
          rw [← h]; push_cast; ring
        have e2 : L.γ₁ s - (t : ℂ) = u + (((τ - t : ℝ)) : ℂ) := by
          have h := hb₁mem hsW hbs
          rw [← h]; push_cast; ring
        rw [e1, e2]
        exact hδf t ht
      have hncross' : ¬ Cross (fun t : ℝ => (L.γ₁ t).im) ((L.γ₁ s).im) s := by
        rw [hsW.1]; exact hncross
      have hnflip : ¬ (∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
          (fl.Ψ (L.γ₁ s + (t : ℂ)) ∈ Work.EL.pairSide P ↔
            ¬ (fl.Ψ (L.γ₁ s - (t : ℂ)) ∈ Work.EL.pairSide P))) :=
        fun h => hncross' ((sp_Cross_iff (f := fun t : ℝ => (L.γ₁ t).im)
          (c := (L.γ₁ s).im) (s := s)).mpr ((side_flip_at_crossing d fl L P hPa hPb hPy hside hre hδfs).mpr h))
      have hex : ∃ t ∈ Set.Ioo (0 : ℝ) ε', ¬ (fl.Ψ (L.γ₁ s + (t : ℂ)) ∈ Work.EL.pairSide P ↔
          ¬ (fl.Ψ (L.γ₁ s - (t : ℂ)) ∈ Work.EL.pairSide P)) := by
        by_contra hcon
        exact hnflip ⟨ε', hε'pos, fun t ht => by
          by_contra h; exact hcon ⟨t, ht, h⟩⟩
      obtain ⟨t, ht, htf⟩ := hex
      have htd : t < dd := lt_trans ht.2 hε'd
      have hmem1 : τ + t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith [ht.1, ht.2, hτpos, hτlt, hε'τ, hε'1],
         by linarith [ht.1, ht.2, hτpos, hτlt, hε'τ, hε'1]⟩
      have hmem2 : τ - t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith [ht.1, ht.2, hτpos, hτlt, hε'τ, hε'1],
         by linarith [ht.1, ht.2, hτpos, hτlt, hε'τ, hε'1]⟩
      have hnot1 : τ + t ∉ T := by
        intro hc
        have hne : τ + t ≠ τ := by linarith [ht.1]
        have h2 := hdd (τ + t) hc hne
        have h3 : |τ + t - τ| = t := by rw [show τ + t - τ = t by ring, abs_of_pos ht.1]
        rw [h3] at h2
        linarith
      have hnot2 : τ - t ∉ T := by
        intro hc
        have hne : τ - t ≠ τ := by linarith [ht.1]
        have h2 := hdd (τ - t) hc hne
        have h3 : |τ - t - τ| = t := by
          rw [show τ - t - τ = -t by ring, abs_neg, abs_of_pos ht.1]
        rw [h3] at h2
        linarith
      have e1 : L.γ₁ s + (t : ℂ) = u + ((τ + t : ℝ) : ℂ) := by
        have h := hb₁mem hsW hbs
        rw [← h]; push_cast; ring
      have e2 : L.γ₁ s - (t : ℂ) = u + ((τ - t : ℝ) : ℂ) := by
        have h := hb₁mem hsW hbs
        rw [← h]; push_cast; ring
      rw [e1, e2] at htf
      refine ⟨t, ht.1, lt_trans ht.2 hε'ε, hmem1, hmem2, hnot1, hnot2, ?_⟩
      by_cases hA : fl.Ψ (u + ((τ + t : ℝ) : ℂ)) ∈ Work.EL.pairSide P
      · have hBfar : fl.Ψ (u + ((τ - t : ℝ) : ℂ)) ∈ Work.EL.pairSide P := by
          by_contra hnb
          exact htf ⟨fun _ => hnb, fun _ => hA⟩
        exact Or.inl ⟨hA, hBfar⟩
      · have hnBfar : ¬ (fl.Ψ (u + ((τ - t : ℝ) : ℂ)) ∈ Work.EL.pairSide P) := by
          intro hB
          exact htf ⟨fun hA' _ => absurd hA' hA, fun hnb => False.elim (absurd hB hnb)⟩
        refine Or.inr ⟨?_, ?_⟩
        · rcases hside.mem_or_mem (hnotcurve _ hmem1 hnot1) with h | h
          · exact absurd h hA
          · exact h
        · rcases hside.mem_or_mem (hnotcurve _ hmem2 hnot2) with h | h
          · exact absurd h hnBfar
          · exact h
    · -- second lift
      rw [hmemT₂] at hτ
      obtain ⟨s, hsW, hbs⟩ := hτ
      have hre : (L.γ₂ s).re < -L.R := by linarith [hsW.2.2]
      have hncross : ¬ Cross (fun t : ℝ => (L.γ₂ t).im) u.im s := by
        intro hc
        exact hτF (by
          rw [hmemF]; right; rw [hmemC₂]
          exact ⟨s, hsW, hc, hbs⟩)
      obtain ⟨δf, hδfp, hδf⟩ := hsimple τ (by
        rw [hmemT]; right; rw [hmemT₂]; exact ⟨s, hsW, hbs⟩)
      have hδfs : ∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
          L.γ₂ s + (t : ℂ) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ ∧
          L.γ₂ s - (t : ℂ) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
        refine ⟨δf, hδfp, fun t ht => ?_⟩
        have e1 : L.γ₂ s + (t : ℂ) = u + (((τ + t : ℝ)) : ℂ) := by
          have h := hb₂mem hsW hbs
          rw [← h]; push_cast; ring
        have e2 : L.γ₂ s - (t : ℂ) = u + (((τ - t : ℝ)) : ℂ) := by
          have h := hb₂mem hsW hbs
          rw [← h]; push_cast; ring
        rw [e1, e2]
        exact hδf t ht
      have hncross' : ¬ Cross (fun t : ℝ => (L.γ₂ t).im) ((L.γ₂ s).im) s := by
        rw [hsW.1]; exact hncross
      have hnflip : ¬ (∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
          (fl.Ψ (L.γ₂ s + (t : ℂ)) ∈ Work.EL.pairSide P ↔
            ¬ (fl.Ψ (L.γ₂ s - (t : ℂ)) ∈ Work.EL.pairSide P))) :=
        fun h => hncross' ((sp_Cross_iff (f := fun t : ℝ => (L.γ₂ t).im)
          (c := (L.γ₂ s).im) (s := s)).mpr ((side_flip_at_crossing_gamma2 d fl L P hPa hPb hPy hside hre hδfs).mpr h))
      have hex : ∃ t ∈ Set.Ioo (0 : ℝ) ε', ¬ (fl.Ψ (L.γ₂ s + (t : ℂ)) ∈ Work.EL.pairSide P ↔
          ¬ (fl.Ψ (L.γ₂ s - (t : ℂ)) ∈ Work.EL.pairSide P)) := by
        by_contra hcon
        exact hnflip ⟨ε', hε'pos, fun t ht => by
          by_contra h; exact hcon ⟨t, ht, h⟩⟩
      obtain ⟨t, ht, htf⟩ := hex
      have htd : t < dd := lt_trans ht.2 hε'd
      have hmem1 : τ + t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith [ht.1, ht.2, hτpos, hτlt, hε'τ, hε'1],
         by linarith [ht.1, ht.2, hτpos, hτlt, hε'τ, hε'1]⟩
      have hmem2 : τ - t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith [ht.1, ht.2, hτpos, hτlt, hε'τ, hε'1],
         by linarith [ht.1, ht.2, hτpos, hτlt, hε'τ, hε'1]⟩
      have hnot1 : τ + t ∉ T := by
        intro hc
        have hne : τ + t ≠ τ := by linarith [ht.1]
        have h2 := hdd (τ + t) hc hne
        have h3 : |τ + t - τ| = t := by rw [show τ + t - τ = t by ring, abs_of_pos ht.1]
        rw [h3] at h2
        linarith
      have hnot2 : τ - t ∉ T := by
        intro hc
        have hne : τ - t ≠ τ := by linarith [ht.1]
        have h2 := hdd (τ - t) hc hne
        have h3 : |τ - t - τ| = t := by
          rw [show τ - t - τ = -t by ring, abs_neg, abs_of_pos ht.1]
        rw [h3] at h2
        linarith
      have e1 : L.γ₂ s + (t : ℂ) = u + ((τ + t : ℝ) : ℂ) := by
        have h := hb₂mem hsW hbs
        rw [← h]; push_cast; ring
      have e2 : L.γ₂ s - (t : ℂ) = u + ((τ - t : ℝ) : ℂ) := by
        have h := hb₂mem hsW hbs
        rw [← h]; push_cast; ring
      rw [e1, e2] at htf
      refine ⟨t, ht.1, lt_trans ht.2 hε'ε, hmem1, hmem2, hnot1, hnot2, ?_⟩
      by_cases hA : fl.Ψ (u + ((τ + t : ℝ) : ℂ)) ∈ Work.EL.pairSide P
      · have hBfar : fl.Ψ (u + ((τ - t : ℝ) : ℂ)) ∈ Work.EL.pairSide P := by
          by_contra hnb
          exact htf ⟨fun _ => hnb, fun _ => hA⟩
        exact Or.inl ⟨hA, hBfar⟩
      · have hnBfar : ¬ (fl.Ψ (u + ((τ - t : ℝ) : ℂ)) ∈ Work.EL.pairSide P) := by
          intro hB
          exact htf ⟨fun hA' _ => absurd hA' hA, fun hnb => False.elim (absurd hB hnb)⟩
        refine Or.inr ⟨?_, ?_⟩
        · rcases hside.mem_or_mem (hnotcurve _ hmem1 hnot1) with h | h
          · exact absurd h hA
          · exact h
        · rcases hside.mem_or_mem (hnotcurve _ hmem2 hnot2) with h | h
          · exact absurd h hnBfar
          · exact h
  -- the number of flipping crossing times is even
  have hcardC₁ : C₁.card = (spWindow₁ L u ∩
      {s : ℝ | Cross (fun t : ℝ => (L.γ₁ t).im) u.im s}).ncard := by
    rw [hC₁, Finset.card_image_of_injOn (by
      intro s hs s' hs' h
      exact sp_beta₁_inj L hu ((hmemW₁ s).mp (Finset.mem_filter.mp hs).1)
        ((hmemW₁ s').mp (Finset.mem_filter.mp hs').1) h)]
    rw [Set.ncard_eq_toFinset_card _ hcross₁fin]
    congr 1
    ext s
    rw [Set.Finite.mem_toFinset hcross₁fin, Finset.mem_filter, hmemW₁ s, hW₁]
    simp only [spWindow₁, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_setOf_eq]
  have hcardC₂ : C₂.card = (spWindow₂ L u ∩
      {s : ℝ | Cross (fun t : ℝ => (L.γ₂ t).im) u.im s}).ncard := by
    rw [hC₂, Finset.card_image_of_injOn (by
      intro s hs s' hs' h
      exact sp_beta₂_inj L hu ((hmemW₂ s).mp (Finset.mem_filter.mp hs).1)
        ((hmemW₂ s').mp (Finset.mem_filter.mp hs').1) h)]
    rw [Set.ncard_eq_toFinset_card _ hcross₂fin]
    congr 1
    ext s
    rw [Set.Finite.mem_toFinset hcross₂fin, Finset.mem_filter, hmemW₂ s, hW₂]
    simp only [spWindow₂, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_setOf_eq]
  have hdisjTT : Disjoint T₁ T₂ := by
    rw [Finset.disjoint_left] at *
    intro τ h1 h2
    rw [hmemT₁] at h1
    rw [hmemT₂] at h2
    obtain ⟨s, hsW, hst⟩ := h1
    obtain ⟨s', hsW', hst'⟩ := h2
    have hΛ : u + (τ : ℂ) ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ :=
      Or.inl ⟨s, (hb₁mem hsW hst).symm⟩
    rw [hb₂mem hsW' hst'] at hΛ
    rcases hΛ with h | h
    · exact Set.disjoint_left.mp (sp_range_disjoint L) h ⟨s', rfl⟩
    · exact (Set.disjoint_left.mp (sp_range_disjoint L) ⟨s, rfl⟩)
        ⟨s', hb₂mem hsW' hst' ▸ hb₁mem hsW hst⟩
  have hdisjCC : Disjoint C₁ C₂ := by
    rw [Finset.disjoint_left] at hdisjTT ⊢
    intro τ h1 h2
    rw [hmemC₁] at h1
    rw [hmemC₂] at h2
    obtain ⟨s, hsW, _, hst⟩ := h1
    obtain ⟨s', hsW', _, hst'⟩ := h2
    have hτ1 : τ ∈ T₁ := by rw [hmemT₁]; exact ⟨s, hsW, hst⟩
    have hτ2 : τ ∈ T₂ := by rw [hmemT₂]; exact ⟨s', hsW', hst'⟩
    exact hdisjTT hτ1 hτ2
  have hFcard : F.card = C₁.card + C₂.card := by
    rw [hF, Finset.card_union_of_disjoint hdisjCC]
  have hevenF : Even F.card := by
    rw [hFcard, hcardC₁, hcardC₂]
    exact heven₁.add heven₂
  -- the walking lemma
  have hσ : Continuous (fun t : ℝ => fl.Ψ (u + (t : ℂ))) :=
    fl.Ψ_diff.continuous.comp (continuous_const.add Complex.continuous_ofReal)
  have hoff : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ T →
      fl.Ψ (u + (t : ℂ)) ∈ Work.EL.pairSide P ∪ Work.EL.pairSideNear P := by
    intro t ht htT
    rcases hside.mem_or_mem (hnotcurve t ht htT) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hmain := sp_side_same_of_even_flips (A := Work.EL.pairSide P)
    (B := Work.EL.pairSideNear P) (σ := fun t : ℝ => fl.Ψ (u + (t : ℂ))) (b := 1)
    (T := T) (F := F) hside.isOpen_far hside.isOpen_near hside.disjoint hσ one_pos
    hT0 hTb hFT hflip hnoflip hoff hevenF
  simpa using hmain



/-! ## The final assembly

The conditional statement `sp_sidePreserve_good` of the previous section is applied at a *generic*
height: the heights at which the level sets of the height function fail to be finite form a
countable set (`countable_level_set_exceptions`), so at every point `u` in the far-left half plane
off the pair curve there is a nearby point `v` with the same real part, a generic height and a
small ball around `u` avoiding the pair curve; the property `P` is locally constant there, so
`P` holds at `u` as well. -/

/-- A countable set of reals misses every open interval. -/
theorem sp_exists_notMem_Ioo {S : Set ℝ} (hS : S.Countable) {x y : ℝ} (hxy : x < y) :
    ∃ c ∈ Set.Ioo x y, c ∉ S := by
  by_contra hcon
  have hcon' : ∀ c ∈ Set.Ioo x y, c ∈ S := by
    intro c hc
    by_contra hcS
    exact hcon ⟨c, hc, hcS⟩
  have hsub : Set.Ioo x y ⊆ S := hcon'
  have hcount : (Set.Ioo x y).Countable := Countable.mono hsub hS
  have hcard : Cardinal.mk (Set.Ioo x y) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.mpr hcount
  rw [Cardinal.mk_Ioo_real hxy] at hcard
  exact absurd hcard (not_le.mpr Cardinal.aleph0_lt_continuum)

/-- **Evenness of the sign changes of one window.**  If the level set of the height function in one
period is finite, then the sign changes of the height function in the window
`{a ≤ Re γ < a+1}` are even in number. -/
theorem sp_window_even (L : RayCylLift d fl) {cc a : ℝ}
    (hfin : ({s : ℝ | (L.γ₁ s).im = cc} ∩ Set.Ico (0 : ℝ) 1).Finite) :
    Even (({s : ℝ | (L.γ₁ s).im = cc ∧ a ≤ (L.γ₁ s).re ∧ (L.γ₁ s).re < a + 1} ∩
      {s : ℝ | Cross (fun t : ℝ => (L.γ₁ t).im) cc s}).ncard) := by
  classical
  obtain ⟨Φ, hΦ, hΦc⟩ := level_window_shift_bij (γ := L.γ₁) (c := cc) (a := a) L.per₁ hfin
  set Z : Set ℝ := {s : ℝ | (L.γ₁ s).im = cc} ∩ Set.Ico (0 : ℝ) 1 with hZ
  set W : Set ℝ := {s : ℝ | (L.γ₁ s).im = cc ∧ a ≤ (L.γ₁ s).re ∧ (L.γ₁ s).re < a + 1}
    with hW
  set Cz : Set ℝ := {s : ℝ | Cross (fun t : ℝ => (L.γ₁ t).im) cc s} with hCz
  have hZW : Φ '' Z = W := hΦ.image_eq
  have heq : W ∩ Cz = Φ '' (Z ∩ Cz) := by
    rw [← hZW]
    ext w
    constructor
    · rintro ⟨hw, hwc⟩
      rcases hw with ⟨s, hs, rfl⟩
      exact ⟨s, ⟨hs, (hΦc s hs).mpr hwc⟩, rfl⟩
    · rintro ⟨s, ⟨hs, hsc⟩, rfl⟩
      exact ⟨⟨s, hs, rfl⟩, (hΦc s hs).mp hsc⟩
  have hcard : (W ∩ Cz).ncard = (Z ∩ Cz).ncard := by
    rw [heq, (hΦ.injOn.mono Set.inter_subset_left).ncard_image]
  have hev : Even (({s : ℝ | (fun t : ℝ => (L.γ₁ t).im) s = cc ∧
      Cross (fun t : ℝ => (L.γ₁ t).im) cc s} ∩ Set.Ico (0 : ℝ) 1).ncard) :=
    even_sign_changes (fun t : ℝ => (L.γ₁ t).im) (Complex.continuous_im.comp L.cont₁)
      (fun s => by rw [L.per₁ s]; simp) cc hfin
  have hset : ({s : ℝ | (fun t : ℝ => (L.γ₁ t).im) s = cc ∧
        Cross (fun t : ℝ => (L.γ₁ t).im) cc s} ∩ Set.Ico (0 : ℝ) 1) = Z ∩ Cz := by
    ext s
    simp only [hZ, hCz, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_setOf_eq, Set.mem_Ico]
    tauto
  have hev' : Even ((Z ∩ Cz).ncard) := by
    rw [← hset]
    exact hev
  rw [hcard]
  exact hev'

/-- **Side preservation of the shift in the far-left half plane.**  For `u` in the far-left half
plane, the side of the `α`-pair `P` of `Ψ u` and of `Ψ (u+1) = F (Ψ u)` agree. -/
theorem sidePreserve_core_parity {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl)
    (han : ∀ n : ℤ, AnalyticOn ℝ (fun s : ℝ => L.γ₁ s) (Set.Ioo (n : ℝ) ((n : ℝ) + 1)))
    (P : Work.EL.CoPair d.hN) (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2)
    (hPy : P.y = d.z₁) (hside : Work.EL.PairSides d.hN P)
    {R : ℝ} (hR : L.R + 1 ≤ R) :
    ∀ u : ℂ, u.re < -R - 1 →
      (fl.Ψ u ∈ Work.EL.pairSide P ↔ fl.Ψ (u + 1) ∈ Work.EL.pairSide P) := by
  classical
  intro u hu
  have huH : u.re < -L.R := by linarith
  by_cases huΛ : u ∈ Set.range L.γ₁ ∪ Set.range L.γ₂
  · exact sp_sidePreserve_mem_lift L P hPa hPb hPy hside huH (by linarith) huΛ
  · -- the side relation is locally constant off the pair curve
    have hloc : ∀ v : ℂ, v.re < -L.R - 1 → v ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ →
        ∃ ε > 0, ∀ w : ℂ, w ∈ Metric.ball v ε →
          ((fl.Ψ w ∈ Work.EL.pairSide P ↔ fl.Ψ (w + 1) ∈ Work.EL.pairSide P) ↔
           (fl.Ψ v ∈ Work.EL.pairSide P ↔ fl.Ψ (v + 1) ∈ Work.EL.pairSide P)) := by
      intro v hvR hv
      have hvcurve : fl.Ψ v ∉ Work.EL.pairCurve P :=
        fun h => hv ((RayCylLift.preimage_pairCurve L P hPa hPb hPy v (by linarith)).mp h)
      have hv1R : (v + 1).re < -L.R := by
        have h : (v + 1).re = v.re + 1 := by simp
        rw [h]; linarith
      have hv1 : v + 1 ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ :=
        fun h => hv ((sp_lift_shift L v).mpr h)
      have hv1curve : fl.Ψ (v + 1) ∉ Work.EL.pairCurve P :=
        fun h => hv1 ((RayCylLift.preimage_pairCurve L P hPa hPb hPy (v + 1) hv1R).mp h)
      have hshiftcont : Continuous (fun w : ℂ => fl.Ψ (w + 1)) :=
        fl.Ψ_diff.continuous.comp (continuous_id.add continuous_const)
      have hfarEv : (fl.Ψ v ∈ Work.EL.pairSide P) →
          ∀ᶠ w in 𝓝 v, fl.Ψ w ∈ Work.EL.pairSide P :=
        fun h => (hside.isOpen_far.preimage fl.Ψ_diff.continuous).mem_nhds h
      have hnearEv : (fl.Ψ v ∈ Work.EL.pairSideNear P) →
          ∀ᶠ w in 𝓝 v, fl.Ψ w ∈ Work.EL.pairSideNear P :=
        fun h => (hside.isOpen_near.preimage fl.Ψ_diff.continuous).mem_nhds h
      have hfarEv1 : (fl.Ψ (v + 1) ∈ Work.EL.pairSide P) →
          ∀ᶠ w in 𝓝 v, fl.Ψ (w + 1) ∈ Work.EL.pairSide P :=
        fun h => (hside.isOpen_far.preimage hshiftcont).mem_nhds h
      have hnearEv1 : (fl.Ψ (v + 1) ∈ Work.EL.pairSideNear P) →
          ∀ᶠ w in 𝓝 v, fl.Ψ (w + 1) ∈ Work.EL.pairSideNear P :=
        fun h => (hside.isOpen_near.preimage hshiftcont).mem_nhds h
      have hdisjA : ∀ w : ℂ, fl.Ψ w ∈ Work.EL.pairSide P →
          fl.Ψ w ∈ Work.EL.pairSideNear P → False :=
        fun w hf hn => Set.disjoint_left.mp hside.disjoint hf hn
      have hev : ∀ᶠ w in 𝓝 v,
          ((fl.Ψ w ∈ Work.EL.pairSide P ↔ fl.Ψ v ∈ Work.EL.pairSide P) ∧
           (fl.Ψ (w + 1) ∈ Work.EL.pairSide P ↔ fl.Ψ (v + 1) ∈ Work.EL.pairSide P)) := by
        rcases hside.mem_or_mem hvcurve with h | h
        · rcases hside.mem_or_mem hv1curve with h1 | h1
          · filter_upwards [hfarEv h, hfarEv1 h1] with w hw hw1
            exact ⟨⟨fun _ => h, fun _ => hw⟩, ⟨fun _ => h1, fun _ => hw1⟩⟩
          · filter_upwards [hfarEv h, hnearEv1 h1] with w hw hw1
            exact ⟨⟨fun _ => h, fun _ => hw⟩,
              ⟨fun hc => False.elim (hdisjA (w + 1) hc hw1),
                fun hv => False.elim (hdisjA (v + 1) hv h1)⟩⟩
        · rcases hside.mem_or_mem hv1curve with h1 | h1
          · filter_upwards [hnearEv h, hfarEv1 h1] with w hw hw1
            exact ⟨⟨fun hc => False.elim (hdisjA w hc hw),
                fun hv => False.elim (hdisjA v hv h)⟩, ⟨fun _ => h1, fun _ => hw1⟩⟩
          · filter_upwards [hnearEv h, hnearEv1 h1] with w hw hw1
            exact ⟨⟨fun hc => False.elim (hdisjA w hc hw),
                fun hv => False.elim (hdisjA v hv h)⟩,
              ⟨fun hc => False.elim (hdisjA (w + 1) hc hw1),
                fun hv => False.elim (hdisjA (v + 1) hv h1)⟩⟩
      obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hev
      refine ⟨ε, hε, fun w hw => ?_⟩
      rcases hsub hw with ⟨h1, h2⟩
      tauto
    -- the radius of local constancy at `u`
    have huH1 : u.re < -L.R - 1 := by linarith
    obtain ⟨εloc, hεloc_pos, hεloc⟩ := hloc u huH1 huΛ
    -- a ball around `u` inside the half plane and off the pair curve
    have hclosed : IsClosed (Set.range L.γ₁ ∪ Set.range L.γ₂) := range_lift_closed d fl L
    have hmem_open : ((Set.range L.γ₁ ∪ Set.range L.γ₂)ᶜ) ∈ 𝓝 u :=
      hclosed.isOpen_compl.mem_nhds huΛ
    have hmem_half : {w : ℂ | w.re < -L.R} ∈ 𝓝 u :=
      (isOpen_lt Complex.continuous_re continuous_const).mem_nhds huH
    obtain ⟨εΩ, hεΩ_pos, hεΩsub⟩ := Metric.mem_nhds_iff.mp
      (Filter.inter_mem hmem_open hmem_half)
    -- the countable set of heights at which the level set of the height function is infinite
    set Bad : Set ℝ := {cc : ℝ |
        ¬ ({s : ℝ | (L.γ₁ s).im = cc} ∩ Set.Ico (0 : ℝ) 1).Finite ∨
        ¬ ({s : ℝ | (L.γ₁ s).im = -cc} ∩ Set.Ico (0 : ℝ) 1).Finite} with hBaddef
    have hcount : ({cc : ℝ | ¬ ({s : ℝ | (L.γ₁ s).im = cc} ∩
        Set.Ico (0 : ℝ) 1).Finite}).Countable :=
      countable_level_set_exceptions L.cont₁ L.per₁ han
    have hcount2 : ({cc : ℝ | ¬ ({s : ℝ | (L.γ₁ s).im = -cc} ∩
        Set.Ico (0 : ℝ) 1).Finite}).Countable := by
      have himg : ({cc : ℝ | ¬ ({s : ℝ | (L.γ₁ s).im = -cc} ∩
          Set.Ico (0 : ℝ) 1).Finite}) = (fun cc : ℝ => -cc) '' {cc : ℝ |
            ¬ ({s : ℝ | (L.γ₁ s).im = cc} ∩ Set.Ico (0 : ℝ) 1).Finite} := by
        ext cc
        simp only [Set.mem_setOf_eq, Set.mem_image]
        constructor
        · intro h
          exact ⟨-cc, by simpa using h, by simp⟩
        · rintro ⟨dd, hd, rfl⟩
          simpa using hd
      rw [himg]
      exact hcount.image _
    have hBadcount : Bad.Countable := by
      rw [hBaddef]
      exact hcount.union hcount2
    -- choose a good height close enough to `u.im`
    set δ : ℝ := min εloc (εΩ / 2) with hδdef
    have hδpos : 0 < δ := lt_min hεloc_pos (by linarith)
    obtain ⟨cc, hccIoo, hccgood⟩ :=
      sp_exists_notMem_Ioo hBadcount (x := u.im - δ) (y := u.im + δ) (by linarith)
    have hccfin : ({s : ℝ | (L.γ₁ s).im = cc} ∩ Set.Ico (0 : ℝ) 1).Finite ∧
        ({s : ℝ | (L.γ₁ s).im = -cc} ∩ Set.Ico (0 : ℝ) 1).Finite := by
      have hnotbad : cc ∉ Bad := hccgood
      rw [hBaddef] at hnotbad
      simp only [Set.mem_setOf_eq] at hnotbad
      push Not at hnotbad
      exact hnotbad
    -- the point with the good height
    set v : ℂ := (u.re : ℂ) + (cc : ℂ) * Complex.I with hvdef
    have hv_re : v.re = u.re := by simp [hvdef]
    have hv_im : v.im = cc := by simp [hvdef]
    have huv_dist : dist v u = |cc - u.im| := by
      have h : v - u = ((cc - u.im : ℝ) : ℂ) * Complex.I := by
        rw [hvdef]; apply Complex.ext <;> simp <;> ring
      rw [dist_eq_norm, h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
    have hv_ltδ : dist v u < δ := by
      rw [huv_dist, abs_lt]
      exact ⟨by linarith [hccIoo.1], by linarith [hccIoo.2]⟩
    have hv_ball_loc : v ∈ Metric.ball u εloc := by
      rw [Metric.mem_ball]
      exact lt_of_lt_of_le hv_ltδ (min_le_left _ _)
    have hv_ball_Ω : v ∈ Metric.ball u εΩ := by
      rw [Metric.mem_ball]
      exact lt_trans (lt_of_lt_of_le hv_ltδ (min_le_right _ _)) (by linarith)
    have hv_notΛ : v ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ := (hεΩsub hv_ball_Ω).1
    have hvH : v.re < -L.R := (hεΩsub hv_ball_Ω).2
    have hv_lt : v.re < -L.R - 1 := by rw [hv_re]; linarith
    -- finiteness and evenness of the two windows at the good height
    have hW₁fin : (spWindow₁ L v).Finite := by
      obtain ⟨Φ, hΦ, _⟩ := level_window_shift_bij (γ := L.γ₁) (c := cc) (a := v.re)
        L.per₁ hccfin.1
      have hW : spWindow₁ L v = {s : ℝ | (L.γ₁ s).im = cc ∧ v.re ≤ (L.γ₁ s).re ∧
          (L.γ₁ s).re < v.re + 1} := by
        ext s
        simp only [spWindow₁, Set.mem_ofPred_eq, Set.mem_setOf_eq, hv_im]
      rw [hW, ← hΦ.image_eq]
      exact hccfin.1.image Φ
    have hW₂fin : (spWindow₂ L v).Finite := by
      obtain ⟨Φ, hΦ, _⟩ := level_window_shift_bij (γ := L.γ₁) (c := -cc) (a := v.re - 1/2)
        L.per₁ hccfin.2
      have hWeq : spWindow₂ L v = {s : ℝ | (L.γ₁ s).im = -cc ∧ v.re - 1/2 ≤ (L.γ₁ s).re ∧
          (L.γ₁ s).re < v.re - 1/2 + 1} := by
        ext s
        simp only [spWindow₂, Set.mem_ofPred_eq, Set.mem_setOf_eq]
        rw [im_γ₂, re_γ₂]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith [h1], by linarith [h2], by linarith [h3]⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith [h1], by linarith [h2], by linarith [h3]⟩
      rw [hWeq, ← hΦ.image_eq]
      exact hccfin.2.image Φ
    have hcross₁fin : (spWindow₁ L v ∩
        {s : ℝ | Cross (fun t : ℝ => (L.γ₁ t).im) v.im s}).Finite :=
      hW₁fin.subset Set.inter_subset_left
    have hcross₂fin : (spWindow₂ L v ∩
        {s : ℝ | Cross (fun t : ℝ => (L.γ₂ t).im) v.im s}).Finite :=
      hW₂fin.subset Set.inter_subset_left
    have heven₁ : Even ((spWindow₁ L v ∩
        {s : ℝ | Cross (fun t : ℝ => (L.γ₁ t).im) v.im s}).ncard) := by
      have h := sp_window_even L (cc := cc) (a := v.re) hccfin.1
      rwa [← hv_im] at h
    have heven₂ : Even ((spWindow₂ L v ∩
        {s : ℝ | Cross (fun t : ℝ => (L.γ₂ t).im) v.im s}).ncard) := by
      have hWeq : spWindow₂ L v = {s : ℝ | (L.γ₁ s).im = -cc ∧ v.re - 1/2 ≤ (L.γ₁ s).re ∧
          (L.γ₁ s).re < v.re - 1/2 + 1} := by
        ext s
        simp only [spWindow₂, Set.mem_ofPred_eq, Set.mem_setOf_eq]
        rw [im_γ₂, re_γ₂]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith [h1], by linarith [h2], by linarith [h3]⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith [h1], by linarith [h2], by linarith [h3]⟩
      have hCeq : {s : ℝ | Cross (fun t : ℝ => (L.γ₂ t).im) v.im s} =
          {s : ℝ | Cross (fun t : ℝ => (L.γ₁ t).im) (-cc) s} := by
        ext s
        have hf : (fun t : ℝ => (L.γ₂ t).im) = (fun t : ℝ => -((L.γ₁ t).im)) := by
          funext t; rw [im_γ₂]
        rw [hf, hv_im]
        simpa using (sp_Cross_neg (f := fun t : ℝ => (L.γ₁ t).im) (c := -cc) (s := s))
      rw [hWeq, hCeq]
      exact sp_window_even L (cc := -cc) (a := v.re - 1/2) hccfin.2
    have hvgood : (fl.Ψ v ∈ Work.EL.pairSide P ↔ fl.Ψ (v + 1) ∈ Work.EL.pairSide P) :=
      sp_sidePreserve_good d fl L P hPa hPb hPy hside hv_lt hv_notΛ hW₁fin hcross₁fin
        heven₁ hW₂fin hcross₂fin heven₂
    exact (hεloc v hv_ball_loc).mp hvgood

end Work.ELRig
