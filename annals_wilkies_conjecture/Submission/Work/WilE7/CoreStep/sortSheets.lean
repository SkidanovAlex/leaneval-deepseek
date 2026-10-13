import Mathlib
import Submission.Work.WilE7.DecompDefs
import Submission.Work.WilE7.CoreStep.exists_perm_monotone
import Submission.Work.WilE7.CoreStep.sign_const_of_isPreconnected

namespace Work.WilE7.CoreStep

open Classical

theorem sortSheets {p m r : ℕ} (C : Set (Fin p → ℝ)) (hCpre : IsPreconnected C)
    (k : Fin r → ℕ) (hk : ∀ t, 0 < k t)
    (s : ∀ t : Fin r, Fin (k t) → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ (t : Fin r) (j : Fin (k t)), ContinuousOn (s t j) C)
    (hinj : ∀ (t : Fin r) (x : Fin p → ℝ), x ∈ C →
      Function.Injective fun j : Fin (k t) => s t j x)
    (hbnd : ∀ (t : Fin r) (j : Fin (k t)) (x : Fin p → ℝ), x ∈ C →
      |(s t j x) (Fin.last m)| < 1)
    (hdich : ∀ (t t' : Fin r) (j : Fin (k t)) (j' : Fin (k t')),
      (∃ x ∈ C, (s t j x) (Fin.last m) = (s t' j' x) (Fin.last m)) →
      ∀ x ∈ C, (s t j x) (Fin.last m) = (s t' j' x) (Fin.last m)) :
    ∃ (K : ℕ) (T : Fin K → (Fin p → ℝ) → ℝ)
      (s' : ∀ t : Fin r, Fin (k t) → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
      (σ : ∀ t : Fin r, Equiv.Perm (Fin (k t))),
      (∀ (t : Fin r) (j : Fin (k t)) (x : Fin p → ℝ), s' t j x = s t (σ t j) x) ∧
      K ≤ ∑ t, k t ∧
      (∀ i : Fin K, ContinuousOn (T i) C) ∧
      (∀ x ∈ C, StrictMono fun i : Fin K => T i x) ∧
      (∀ x ∈ C, ∀ i : Fin K, |T i x| < 1) ∧
      (∀ (t : Fin r) (j : Fin (k t)), ∃ i : Fin K, ∀ x ∈ C, T i x = (s' t j x) (Fin.last m)) ∧
      (∀ t (x : Fin p → ℝ), x ∈ C → Monotone fun j : Fin (k t) => (s' t j x) (Fin.last m)) ∧
      (∀ hK : 0 < K, ∃ t : Fin r,
        ∀ x ∈ C, T ⟨0, hK⟩ x = (s' t ⟨0, hk t⟩ x) (Fin.last m)) ∧
      (∀ hK : 0 < K, ∃ t : Fin r,
        ∀ x ∈ C, T ⟨K - 1, Nat.sub_lt hK (by norm_num)⟩ x =
          (s' t ⟨k t - 1, Nat.sub_lt (hk t) (by norm_num)⟩ x) (Fin.last m)) := by
  classical
  by_cases hCne : C.Nonempty
  · -- main case: `C` is nonempty, so we have a base point `x0`
    obtain ⟨x0, hx0⟩ := hCne
    let X := Σ t : Fin r, Fin (k t)
    let L : X → (Fin p → ℝ) → ℝ := fun a x => (s a.1 a.2 x) (Fin.last m)
    have hdichL : ∀ a b : X, (∃ x ∈ C, L a x = L b x) → ∀ x ∈ C, L a x = L b x :=
      fun a b h => hdich a.1 b.1 a.2 b.2 h
    have hLcont : ∀ a : X, ContinuousOn (L a) C := by
      intro a
      simpa only [L, Function.comp_def] using
        (continuous_apply (Fin.last m)).comp_continuousOn (hcont a.1 a.2)
    have htrans_eq : ∀ a b : X, L a x0 = L b x0 → ∀ x ∈ C, L a x = L b x :=
      fun a b h => hdichL a b ⟨x0, hx0, h⟩
    have htransfer : ∀ a b : X, L a x0 < L b x0 → ∀ x ∈ C, L a x < L b x := by
      intro a b hab x hx
      have hfcont : ContinuousOn (fun y => L a y - L b y) C := (hLcont a).sub (hLcont b)
      have hfne : ∀ y ∈ C, L a y - L b y ≠ 0 := by
        intro y hy h0
        have hyz : L a y = L b y := sub_eq_zero.mp h0
        have hx0eq : L a x0 = L b x0 := hdichL a b ⟨y, hy, hyz⟩ x0 hx0
        exact (ne_of_lt hab) hx0eq
      have hsign := sign_const_of_isPreconnected hCpre hfcont hfne hx0 hx
      have hx0neg : L a x0 - L b x0 < 0 := sub_neg.mpr hab
      have hnotpos : ¬ (0 < L a x - L b x) := fun hpos =>
        not_lt.mpr (le_of_lt hx0neg) (hsign.mp hpos)
      exact sub_neg.mp (lt_of_le_of_ne (not_lt.mp hnotpos) (hfne x hx))
    have htransfer_le : ∀ a b : X, L a x0 ≤ L b x0 → ∀ x ∈ C, L a x ≤ L b x := by
      intro a b h x hx
      rcases lt_or_eq_of_le h with h' | h'
      · exact le_of_lt (htransfer a b h' x hx)
      · exact le_of_eq (hdichL a b ⟨x0, hx0, h'⟩ x hx)
    -- the finite set of distinct levels at the base point
    let S : Finset ℝ := Finset.univ.image fun a : X => L a x0
    let K : ℕ := S.card
    -- its increasing enumeration
    let emb : Fin K ↪o ℝ := S.orderEmbOfFin rfl
    have hemb_mem : ∀ i : Fin K, emb i ∈ S := fun i => Finset.orderEmbOfFin_mem S rfl i
    -- a representative sheet for each distinct level
    let rep : Fin K → X := fun i => (Finset.mem_image.mp (hemb_mem i)).choose
    have hrep : ∀ i : Fin K, L (rep i) x0 = emb i := fun i =>
      (Finset.mem_image.mp (hemb_mem i)).choose_spec.2
    let T : Fin K → (Fin p → ℝ) → ℝ := fun i x => L (rep i) x
    have hLmem : ∀ a : X, L a x0 ∈ S :=
      fun a => Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
    -- the index of a (level of a) sheet in the global enumeration
    have hidx_exists : ∀ a : X, ∃ i : Fin K, emb i = L a x0 := by
      intro a
      have h : L a x0 ∈ Set.range emb := by
        rw [show Set.range emb = (S : Set ℝ) by simp [emb]]
        exact hLmem a
      exact h
    let idx : X → Fin K := fun a => (hidx_exists a).choose
    have hidx : ∀ a : X, emb (idx a) = L a x0 := fun a => (hidx_exists a).choose_spec
    -- sort each block by its level at the base point
    have hsort : ∀ t : Fin r, ∃ σ : Equiv.Perm (Fin (k t)),
        Monotone fun j : Fin (k t) => idx ⟨t, σ j⟩ :=
      fun t => exists_perm_monotone (fun j : Fin (k t) => idx ⟨t, j⟩)
    choose σ hσmono using hsort
    let s' : ∀ t : Fin r, Fin (k t) → (Fin p → ℝ) → (Fin (m + 1) → ℝ) :=
      fun t j x => s t (σ t j) x
    have hmu_mono : ∀ t : Fin r, Monotone fun j : Fin (k t) => L ⟨t, σ t j⟩ x0 := by
      intro t
      have h1 : Monotone fun j : Fin (k t) => emb (idx ⟨t, σ t j⟩) :=
        emb.strictMono.monotone.comp (hσmono t)
      have h2 : (fun j : Fin (k t) => emb (idx ⟨t, σ t j⟩)) = fun j => L ⟨t, σ t j⟩ x0 :=
        funext fun j => hidx ⟨t, σ t j⟩
      rwa [h2] at h1
    have hKle : K ≤ ∑ t, k t := by
      have h1 : S.card ≤ (Finset.univ : Finset X).card :=
        Finset.card_image_le (s := Finset.univ) (f := fun a : X => L a x0)
      rw [Finset.card_univ, Fintype.card_sigma] at h1
      simpa [K] using h1
    have hTcont : ∀ i : Fin K, ContinuousOn (T i) C := fun i => hLcont (rep i)
    have hTstrict : ∀ x ∈ C, StrictMono fun i : Fin K => T i x := by
      intro x hx i j hij
      have hlt : emb i < emb j := emb.strictMono hij
      have hx0lt : L (rep i) x0 < L (rep j) x0 := by rw [hrep i, hrep j]; exact hlt
      exact htransfer (rep i) (rep j) hx0lt x hx
    have hTbnd : ∀ x ∈ C, ∀ i : Fin K, |T i x| < 1 :=
      fun x hx i => hbnd (rep i).1 (rep i).2 x hx
    have hcover : ∀ (t : Fin r) (j : Fin (k t)), ∃ i : Fin K,
        ∀ x ∈ C, T i x = (s' t j x) (Fin.last m) := by
      intro t j
      refine ⟨idx ⟨t, σ t j⟩, ?_⟩
      have h1 : L (rep (idx ⟨t, σ t j⟩)) x0 = L ⟨t, σ t j⟩ x0 := by
        rw [hrep (idx ⟨t, σ t j⟩), hidx ⟨t, σ t j⟩]
      intro x hx
      change L (rep (idx ⟨t, σ t j⟩)) x = (s t (σ t j) x) (Fin.last m)
      rw [htrans_eq (rep (idx ⟨t, σ t j⟩)) ⟨t, σ t j⟩ h1 x hx]
    have hmono : ∀ (t : Fin r) (x : Fin p → ℝ), x ∈ C →
        Monotone fun j : Fin (k t) => (s' t j x) (Fin.last m) := by
      intro t x hx
      change Monotone fun j : Fin (k t) => L ⟨t, σ t j⟩ x
      exact fun j j' hjj => htransfer_le ⟨t, σ t j⟩ ⟨t, σ t j'⟩ (hmu_mono t hjj) x hx
    have hmin : ∀ hK : 0 < K, ∃ t : Fin r,
        ∀ x ∈ C, T ⟨0, hK⟩ x = (s' t ⟨0, hk t⟩ x) (Fin.last m) := by
      intro hK
      refine ⟨(rep ⟨0, hK⟩).1, ?_⟩
      have hleft : ∀ a : X, emb ⟨0, hK⟩ ≤ L a x0 := by
        intro a
        rw [← hidx a]
        exact emb.strictMono.monotone (Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
      have key : L (rep ⟨0, hK⟩) x0
          = L ⟨(rep ⟨0, hK⟩).1, σ (rep ⟨0, hK⟩).1 ⟨0, hk (rep ⟨0, hK⟩).1⟩⟩ x0 := by
        apply le_antisymm
        · rw [hrep ⟨0, hK⟩]
          exact hleft _
        · obtain ⟨j, hj⟩ := (σ (rep ⟨0, hK⟩).1).surjective (rep ⟨0, hK⟩).2
          have hjj : (⟨0, hk (rep ⟨0, hK⟩).1⟩ : Fin (k (rep ⟨0, hK⟩).1)) ≤ j :=
            Fin.le_iff_val_le_val.mpr (Nat.zero_le _)
          have hstep : L ⟨(rep ⟨0, hK⟩).1, σ (rep ⟨0, hK⟩).1 ⟨0, hk (rep ⟨0, hK⟩).1⟩⟩ x0
              ≤ L ⟨(rep ⟨0, hK⟩).1, σ (rep ⟨0, hK⟩).1 j⟩ x0 :=
            hmu_mono (rep ⟨0, hK⟩).1 hjj
          rw [hj] at hstep
          exact hstep
      intro x hx
      change L (rep ⟨0, hK⟩) x
        = (s ((rep ⟨0, hK⟩).1) (σ ((rep ⟨0, hK⟩).1) ⟨0, hk ((rep ⟨0, hK⟩).1)⟩) x)
            (Fin.last m)
      rw [htrans_eq (rep ⟨0, hK⟩)
        ⟨(rep ⟨0, hK⟩).1, σ (rep ⟨0, hK⟩).1 ⟨0, hk (rep ⟨0, hK⟩).1⟩⟩ key x hx]
    have hmax : ∀ hK : 0 < K, ∃ t : Fin r,
        ∀ x ∈ C, T ⟨K - 1, Nat.sub_lt hK (by norm_num)⟩ x =
          (s' t ⟨k t - 1, Nat.sub_lt (hk t) (by norm_num)⟩ x) (Fin.last m) := by
      intro hK
      let i1 : Fin K := ⟨K - 1, Nat.sub_lt hK (by norm_num)⟩
      let a1 : X := rep i1
      refine ⟨a1.1, ?_⟩
      have hright : ∀ a : X, L a x0 ≤ emb i1 := by
        intro a
        rw [← hidx a]
        exact emb.strictMono.monotone
          (Fin.le_iff_val_le_val.mpr (Nat.le_sub_one_of_lt (idx a).2))
      have key : L a1 x0
          = L ⟨a1.1, σ a1.1 ⟨k a1.1 - 1, Nat.sub_lt (hk a1.1) (by norm_num)⟩⟩ x0 := by
        apply le_antisymm
        · obtain ⟨j, hj⟩ := (σ a1.1).surjective a1.2
          have hjj : j ≤ (⟨k a1.1 - 1, Nat.sub_lt (hk a1.1) (by norm_num)⟩ : Fin (k a1.1)) :=
            Fin.le_iff_val_le_val.mpr (Nat.le_sub_one_of_lt j.2)
          have hstep : L ⟨a1.1, σ a1.1 j⟩ x0
              ≤ L ⟨a1.1, σ a1.1 ⟨k a1.1 - 1, Nat.sub_lt (hk a1.1) (by norm_num)⟩⟩ x0 :=
            hmu_mono a1.1 hjj
          rw [hj] at hstep
          exact hstep
        · have h := hright ⟨a1.1, σ a1.1 ⟨k a1.1 - 1, Nat.sub_lt (hk a1.1) (by norm_num)⟩⟩
          rw [← hrep i1] at h
          exact h
      intro x hx
      change L (rep i1) x
        = (s a1.1 (σ a1.1 ⟨k a1.1 - 1, Nat.sub_lt (hk a1.1) (by norm_num)⟩) x)
            (Fin.last m)
      rw [htrans_eq (rep i1)
        ⟨a1.1, σ a1.1 ⟨k a1.1 - 1, Nat.sub_lt (hk a1.1) (by norm_num)⟩⟩ key x hx]
    exact ⟨K, T, s', σ, fun t j x => rfl, hKle, hTcont, hTstrict, hTbnd,
      hcover, hmono, hmin, hmax⟩
  · -- degenerate case: `C` is empty, all pointwise conditions are vacuous
    have hCempty : ∀ x : Fin p → ℝ, x ∉ C := fun x hx => hCne ⟨x, hx⟩
    have hr_of_Kpos : 0 < (∑ t, k t) → 0 < r := by
      intro hK
      by_contra hr
      have hr' : r ≤ 0 := not_lt.mp hr
      have hsum0 : (∑ t, k t) = 0 := by
        apply Finset.sum_eq_zero
        intro t _
        exact absurd t.isLt (by omega)
      rw [hsum0] at hK
      exact lt_irrefl 0 hK
    refine ⟨∑ t, k t, fun _ _ => (0 : ℝ), s, fun _ => Equiv.refl _, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · intro t j x
      rfl
    · exact le_refl _
    · intro i
      exact continuousOn_const
    · intro x hx
      exact absurd hx (hCempty x)
    · intro x hx
      exact absurd hx (hCempty x)
    · intro t j
      exact ⟨⟨0, Finset.sum_pos (fun t' _ => hk t') ⟨t, Finset.mem_univ t⟩⟩,
        fun x hx => absurd hx (hCempty x)⟩
    · intro t x hx
      exact absurd hx (hCempty x)
    · intro hK
      exact ⟨⟨0, hr_of_Kpos hK⟩, fun x hx => absurd hx (hCempty x)⟩
    · intro hK
      exact ⟨⟨0, hr_of_Kpos hK⟩, fun x hx => absurd hx (hCempty x)⟩

end Work.WilE7.CoreStep
