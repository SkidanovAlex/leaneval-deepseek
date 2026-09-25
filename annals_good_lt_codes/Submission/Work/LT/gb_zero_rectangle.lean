import Mathlib
import Submission.Work.LT.good_base_defs
import Submission.Work.LT.gb_prodsum_tensor_bot

namespace Work.LT

/-- A determining set of a binary code contains an *information set* `I` with a linear
section: every assignment on `I` extends uniquely to a codeword, and the extension map is
linear.  (Kalachev--Panteleev, used for the zero-rectangle lemma.) -/
lemma gb_determining_section_aux {D : ℕ} (CA : Submodule (ZMod 2) (Fin D → ZMod 2))
    (A : Finset (Fin D))
    (hA : ∀ c ∈ CA, c ≠ 0 → (Finset.univ \ A).card < hammingNorm c) :
    ∃ I : Finset (Fin D), I ⊆ A ∧
      ∃ σ : ({i // i ∈ I} → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2),
        (∀ w, σ w ∈ CA) ∧
        (∀ (w : {i // i ∈ I} → ZMod 2) (i : {i // i ∈ I}), σ w i.1 = w i) ∧
        (∀ c ∈ CA, σ (fun i : {i // i ∈ I} => c i.1) = c) := by
  classical
  have hdet : ∀ c ∈ CA, (∀ i ∈ A, c i = 0) → c = 0 := by
    intro c hc h0
    by_contra hne
    have hle : hammingNorm c ≤ (Finset.univ \ A).card := by
      rw [hammingNorm]
      apply Finset.card_le_card
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ i, fun hiA => hi.2 (h0 i hiA)⟩
    have := hA c hc hne
    omega
  have main : ∀ n, ∀ I : Finset (Fin D), I ⊆ A → I.card = n →
      (∀ c ∈ CA, (∀ i ∈ I, c i = 0) → c = 0) →
      ∃ J : Finset (Fin D), J ⊆ I ∧ J.card = Module.finrank (ZMod 2) CA ∧
        (∀ c ∈ CA, (∀ i ∈ J, c i = 0) → c = 0) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro I hIA hcard hdetI
      by_cases h : I.card = Module.finrank (ZMod 2) CA
      · exact ⟨I, Finset.Subset.refl I, h, hdetI⟩
      · have hdle : Module.finrank (ZMod 2) CA ≤ I.card := by
          let φ : CA →ₗ[ZMod 2] ({i // i ∈ I} → ZMod 2) :=
            (LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : {i // i ∈ I} => i.1)).comp CA.subtype
          have hinj : Function.Injective φ := by
            intro c c' hcc
            have hpt : ∀ i ∈ I, (c : Fin D → ZMod 2) i = (c' : Fin D → ZMod 2) i := by
              intro i hi
              exact congr_fun hcc ⟨i, hi⟩
            have hmem : ((c : Fin D → ZMod 2) - (c' : Fin D → ZMod 2)) ∈ CA := sub_mem c.2 c'.2
            have hzero : ∀ i ∈ I, ((c : Fin D → ZMod 2) - (c' : Fin D → ZMod 2)) i = 0 := by
              intro i hi
              simp only [Pi.sub_apply, hpt i hi, sub_self]
            exact Subtype.ext (sub_eq_zero.mp (hdetI _ hmem hzero))
          have h1 := LinearMap.finrank_le_finrank_of_injective hinj
          rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h1
        have hlt : Module.finrank (ZMod 2) CA < I.card := lt_of_le_of_ne hdle (Ne.symm h)
        have hx : ∃ i₀ ∈ I, ∀ c ∈ CA, (∀ i ∈ I.erase i₀, c i = 0) → c = 0 := by
          by_contra hcon
          push Not at hcon
          have hcon' : ∀ i : ↥I, ∃ c : Fin D → ZMod 2,
              c ∈ CA ∧ (∀ t ∈ I.erase i.1, c t = 0) ∧ c ≠ 0 := fun i => hcon i.1 i.2
          choose f hfmem hfvan hfne using hcon'
          have hfi : ∀ i : ↥I, f i i.1 ≠ 0 := by
            intro i h0
            have hvanish : ∀ t ∈ I, f i t = 0 := by
              intro t ht
              by_cases ht_eq : t = i.1
              · rw [ht_eq]; exact h0
              · exact hfvan i t (Finset.mem_erase.mpr ⟨ht_eq, ht⟩)
            exact hfne i (hdetI (f i) (hfmem i) hvanish)
          have hli : LinearIndependent (ZMod 2) (fun i : ↥I => (⟨f i, hfmem i⟩ : CA)) := by
            rw [Fintype.linearIndependent_iff]
            intro a ha i
            have h := congrArg (fun v : CA => (v : Fin D → ZMod 2) i.1) ha
            simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
              Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
            have hsum : (∑ x : ↥I, a x * f x i.1) = a i * f i i.1 := by
              apply Finset.sum_eq_single i
              · intro j _ hji
                have hji' : i.1 ∈ I.erase j.1 :=
                  Finset.mem_erase.mpr ⟨fun hh => hji (Subtype.ext hh.symm), i.2⟩
                rw [hfvan j i.1 hji', mul_zero]
              · intro hi; exact absurd (Finset.mem_univ i) hi
            rw [hsum] at h
            exact (mul_eq_zero.mp h).resolve_right (hfi i)
          have hcardle := hli.fintype_card_le_finrank
          rw [Fintype.card_coe] at hcardle
          omega
        obtain ⟨i₀, hi₀, hi₀det⟩ := hx
        obtain ⟨J, hJsub, hJcard, hJdet⟩ :=
          ih (I.erase i₀).card (by rw [← hcard]; exact Finset.card_erase_lt_of_mem hi₀) (I.erase i₀)
            (fun i hi => hIA (Finset.mem_of_mem_erase hi)) rfl hi₀det
        exact ⟨J, Finset.Subset.trans hJsub (Finset.erase_subset i₀ I), hJcard, hJdet⟩
  obtain ⟨I, hIA, hIcard, hdetI⟩ := main A.card A (Finset.Subset.refl A) rfl hdet
  let ρ' : CA →ₗ[ZMod 2] ({i // i ∈ I} → ZMod 2) :=
    (LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : {i // i ∈ I} => i.1)).comp CA.subtype
  have hinj : Function.Injective ρ' := by
    intro c c' hcc
    have hpt : ∀ i ∈ I, (c : Fin D → ZMod 2) i = (c' : Fin D → ZMod 2) i := by
      intro i hi
      exact congr_fun hcc ⟨i, hi⟩
    have hmem : ((c : Fin D → ZMod 2) - (c' : Fin D → ZMod 2)) ∈ CA := sub_mem c.2 c'.2
    have hzero : ∀ i ∈ I, ((c : Fin D → ZMod 2) - (c' : Fin D → ZMod 2)) i = 0 := by
      intro i hi
      simp only [Pi.sub_apply, hpt i hi, sub_self]
    exact Subtype.ext (sub_eq_zero.mp (hdetI _ hmem hzero))
  have hfr : Module.finrank (ZMod 2) CA = Module.finrank (ZMod 2) ({i // i ∈ I} → ZMod 2) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hIcard]
  have hsurj : Function.Surjective ρ' :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hinj
  obtain ⟨σ₀, hσ₀⟩ := LinearMap.exists_rightInverse_of_surjective ρ'
    (LinearMap.range_eq_top.mpr hsurj)
  have hσ₀' : ∀ w, ρ' (σ₀ w) = w := fun w => by
    have hh := congrArg (fun (f : ({i // i ∈ I} → ZMod 2) →ₗ[ZMod 2] ({i // i ∈ I} → ZMod 2)) => f w) hσ₀
    simpa [LinearMap.comp_apply] using hh
  refine ⟨I, hIA, (Submodule.subtype CA).comp σ₀, ?_, ?_, ?_⟩
  · intro w; exact (σ₀ w).2
  · intro w i; exact congr_fun (hσ₀' w) i
  · intro c hc
    have h1 : σ₀ (ρ' (⟨c, hc⟩ : CA)) = ⟨c, hc⟩ := by
      apply hinj
      rw [hσ₀' (ρ' ⟨c, hc⟩)]
    exact congrArg (fun v : CA => (v : Fin D → ZMod 2)) h1

/-- Kalachev--Panteleev Lemma 7 ("zero rectangles"). If `x ∈ CA ⊞ CB` vanishes on the rectangle `A × B`, and the complements of `A` and `B` are smaller than the distances of `CA`, resp. `CB` (expressed by saying that a non-zero codeword is longer than the complement), then `x` is a sum of a column-wise-`CA` matrix with at most `|Bᶜ|` non-zero columns and a row-wise-`CB` matrix with at most `|Aᶜ|` non-zero rows. -/
theorem gb_zero_rectangle {D : ℕ} (CA CB : Submodule (ZMod 2) (Fin D → ZMod 2))
    (x : Fin D × Fin D → ZMod 2) (hx : x ∈ GB.prodSum CA CB) (A B : Finset (Fin D))
    (hA : ∀ c ∈ CA, c ≠ 0 → (Finset.univ \ A).card < hammingNorm c)
    (hB : ∀ c ∈ CB, c ≠ 0 → (Finset.univ \ B).card < hammingNorm c)
    (hzero : ∀ i ∈ A, ∀ j ∈ B, x (i, j) = 0) :
    ∃ a ∈ GB.colCode CA, ∃ b ∈ GB.rowCode CB, x = a + b ∧
      GB.nzCols a ≤ (Finset.univ \ B).card ∧ GB.nzRows b ≤ (Finset.univ \ A).card := by
  classical
  -- Information sets of the two codes inside `A`, `B`.
  obtain ⟨I, hIA, σ, hσmem, hσres, hσid⟩ := gb_determining_section_aux CA A hA
  obtain ⟨J, hJB, τ, hτmem, hτres, hτid⟩ := gb_determining_section_aux CB B hB
  -- Restriction maps, projections onto the codes, and their kernels.
  set ρI : (Fin D → ZMod 2) →ₗ[ZMod 2] ({i // i ∈ I} → ZMod 2) :=
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : {i // i ∈ I} => i.1) with hρI
  set ρJ : (Fin D → ZMod 2) →ₗ[ZMod 2] ({j // j ∈ J} → ZMod 2) :=
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun j : {j // j ∈ J} => j.1) with hρJ
  set p₁ : (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2) := σ.comp ρI with hp₁
  set p₂ : (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2) := τ.comp ρJ with hp₂
  set P₁ : Submodule (ZMod 2) (Fin D → ZMod 2) := LinearMap.ker ρI with hP₁
  set P₂ : Submodule (ZMod 2) (Fin D → ZMod 2) := LinearMap.ker ρJ with hP₂
  -- The two correcting matrices: `a` is column-wise `CA` and supported outside the columns `B`,
  -- `b` is row-wise `CB` and supported outside the rows `A`.
  set a : Fin D × Fin D → ZMod 2 :=
    (fun q => if q.2 ∈ B then 0 else p₁ (fun i' => x (i', q.2)) q.1) with ha
  set b : Fin D × Fin D → ZMod 2 :=
    (fun q => if q.1 ∈ A then 0 else p₂ (fun j' => x (q.1, j')) q.2) with hb
  have ha_apply : ∀ i j, a (i,j) = if j ∈ B then 0 else p₁ (fun i' => x (i',j)) i := by
    intro i j; rw [ha]
  have hb_apply : ∀ i j, b (i,j) = if i ∈ A then 0 else p₂ (fun j' => x (i,j')) j := by
    intro i j; rw [hb]
  -- The projections take values in the codes.
  have hp₁mem : ∀ v : Fin D → ZMod 2, p₁ v ∈ CA := by
    intro v
    rw [hp₁]
    exact hσmem (ρI v)
  have hp₂mem : ∀ v : Fin D → ZMod 2, p₂ v ∈ CB := by
    intro v
    rw [hp₂]
    exact hτmem (ρJ v)
  -- `a` is column-wise `CA`, `b` is row-wise `CB`.
  have ha_col : a ∈ GB.colCode CA := by
    rw [GB.mem_colCode]
    intro j
    change (fun i : Fin D => a (i,j)) ∈ CA
    by_cases hj : j ∈ B
    · have hz : (fun i : Fin D => a (i,j)) = 0 := by
        funext i; rw [ha_apply i j, ite_eq_left hj]; simp
      rw [hz]
      exact Submodule.zero_mem CA
    · have hz : (fun i : Fin D => a (i,j)) = p₁ (fun i' => x (i',j)) := by
        funext i; rw [ha_apply i j, ite_eq_right hj]
      rw [hz]
      exact hp₁mem _
  have hb_row : b ∈ GB.rowCode CB := by
    rw [GB.mem_rowCode]
    intro i
    change (fun j : Fin D => b (i,j)) ∈ CB
    by_cases hi : i ∈ A
    · have hz : (fun j : Fin D => b (i,j)) = 0 := by
        funext j; rw [hb_apply i j, ite_eq_left hi]; simp
      rw [hz]
      exact Submodule.zero_mem CB
    · have hz : (fun j : Fin D => b (i,j)) = p₂ (fun j' => x (i,j')) := by
        funext j; rw [hb_apply i j, ite_eq_right hi]
      rw [hz]
      exact hp₂mem _
  -- The difference `x - a - b` vanishes on the rows `I` and the columns `J`.
  have hvanI : ∀ i ∈ I, ∀ j, (x - a - b) (i,j) = 0 := by
    intro i hi j
    have hiA : i ∈ A := hIA hi
    have hb0 : b (i,j) = 0 := by rw [hb_apply i j, ite_eq_left hiA]
    by_cases hjB : j ∈ B
    · have ha0 : a (i,j) = 0 := by rw [ha_apply i j, ite_eq_left hjB]
      have hx0 : x (i,j) = 0 := hzero i hiA j hjB
      simp [Pi.sub_apply, ha0, hb0, hx0]
    · have haX : a (i,j) = x (i,j) := by
        rw [ha_apply i j, ite_eq_right hjB, hp₁]
        show σ (ρI (fun i' => x (i',j))) i = x (i,j)
        rw [show ρI (fun i' => x (i',j)) = (fun t : {i // i ∈ I} => x (t.1, j)) from rfl]
        exact hσres (fun t : {i // i ∈ I} => x (t.1, j)) ⟨i, hi⟩
      simp [Pi.sub_apply, haX, hb0]
  have hvanJ : ∀ j ∈ J, ∀ i, (x - a - b) (i,j) = 0 := by
    intro j hj i
    have hjB : j ∈ B := hJB hj
    have ha0 : a (i,j) = 0 := by rw [ha_apply i j, ite_eq_left hjB]
    by_cases hiA : i ∈ A
    · have hb0 : b (i,j) = 0 := by rw [hb_apply i j, ite_eq_left hiA]
      have hx0 : x (i,j) = 0 := hzero i hiA j hjB
      simp [Pi.sub_apply, ha0, hb0, hx0]
    · have hbX : b (i,j) = x (i,j) := by
        rw [hb_apply i j, ite_eq_right hiA, hp₂]
        show τ (ρJ (fun j' => x (i,j'))) j = x (i,j)
        rw [show ρJ (fun j' => x (i,j')) = (fun t : {j // j ∈ J} => x (i, t.1)) from rfl]
        exact hτres (fun t : {j // j ∈ J} => x (i, t.1)) ⟨j, hj⟩
      simp [Pi.sub_apply, ha0, hbX]
  -- Membership in `CA ⊞ CB` and in `P₁ ⊗ P₂`.
  have hx'1 : x - a - b ∈ GB.prodSum CA CB :=
    sub_mem (sub_mem hx (Submodule.mem_sup_left ha_col)) (Submodule.mem_sup_right hb_row)
  have hx'2 : x - a - b ∈ tensorCode P₁ P₂ := by
    rw [GB.mem_tensorCode]
    constructor
    · intro j
      rw [hP₁, LinearMap.mem_ker, hρI]
      funext t
      rw [LinearMap.funLeft_apply]
      exact hvanI t.1 t.2 j
    · intro i
      rw [hP₂, LinearMap.mem_ker, hρJ]
      funext t
      rw [LinearMap.funLeft_apply]
      exact hvanJ t.1 t.2 i
  -- The projections fix the codes and kill the kernels.
  have hp₁C : ∀ v ∈ CA, p₁ v = v := by
    intro v hv
    rw [hp₁]
    exact hσid v hv
  have hp₁P : ∀ v ∈ P₁, p₁ v = 0 := by
    intro v hv
    rw [hP₁, LinearMap.mem_ker] at hv
    rw [hp₁]
    show σ (ρI v) = 0
    rw [hv, map_zero]
  have hp₂C : ∀ v ∈ CB, p₂ v = v := by
    intro v hv
    rw [hp₂]
    exact hτid v hv
  have hp₂P : ∀ v ∈ P₂, p₂ v = 0 := by
    intro v hv
    rw [hP₂, LinearMap.mem_ker] at hv
    rw [hp₂]
    show τ (ρJ v) = 0
    rw [hv, map_zero]
  have hx'0 : x - a - b = 0 :=
    gb_prodsum_tensor_bot CA CB P₁ P₂ p₁ p₂ hp₁C hp₁P hp₂C hp₂P (x - a - b) hx'1 hx'2
  have hxab : x = a + b := by
    have h1 : x - a = b := sub_eq_zero.mp hx'0
    have h2 : x = b + a := sub_eq_iff_eq_add.mp h1
    rw [h2, add_comm]
  -- The support bounds.
  have hnzcol : GB.nzCols a ≤ (Finset.univ \ B).card := by
    rw [GB.nzCols]
    apply Finset.card_le_card
    intro j hj
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ j, ?_⟩
    intro hjB
    rw [Finset.mem_filter] at hj
    obtain ⟨-, i, hi⟩ := hj
    rw [ha_apply i j, ite_eq_left hjB] at hi
    exact hi rfl
  have hnzrow : GB.nzRows b ≤ (Finset.univ \ A).card := by
    rw [GB.nzRows]
    apply Finset.card_le_card
    intro i hi
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ i, ?_⟩
    intro hiA
    rw [Finset.mem_filter] at hi
    obtain ⟨-, j, hj⟩ := hi
    rw [hb_apply i j, ite_eq_left hiA] at hj
    exact hj rfl
  exact ⟨a, ha_col, b, hb_row, hxab, hnzcol, hnzrow⟩

end Work.LT
