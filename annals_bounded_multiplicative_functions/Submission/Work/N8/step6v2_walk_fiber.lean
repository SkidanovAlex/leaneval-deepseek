import Mathlib
import Submission.Work.N8.step6v2_defs
import Submission.Work.N8.step6_defs
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

/-- A finite set of reals, all of whose elements lie in `[lo, hi]` with `hi - lo < 2 d` and which
is `d`-separated (distinct elements are at distance `≥ d`), has at most two elements. -/
lemma card_le_two_of_sep {s : Finset ℝ} {lo hi d : ℝ}
    (hsub : ∀ x ∈ s, lo ≤ x ∧ x ≤ hi)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ |x - y|)
    (hlen : hi - lo < 2 * d) : s.card ≤ 2 := by
  classical
  have hmem : ∀ x ∈ s, (fun x : ℝ => if x < lo + d then (0 : ℝ) else 1) x
      ∈ ({0, 1} : Finset ℝ) := by
    intro x _
    by_cases h : x < lo + d <;> simp [h]
  have hinj : ∀ x ∈ s, ∀ y ∈ s, (fun x : ℝ => if x < lo + d then (0 : ℝ) else 1) x
      = (fun x : ℝ => if x < lo + d then (0 : ℝ) else 1) y → x = y := by
    intro x hx y hy hxy
    change (if x < lo + d then (0 : ℝ) else 1) = (if y < lo + d then (0 : ℝ) else 1) at hxy
    by_cases hx1 : x < lo + d
    · have hy1 : y < lo + d := by
        by_contra hy1
        rw [if_pos hx1, if_neg hy1] at hxy
        exact absurd hxy (by norm_num)
      have h1 : x - y < d := by have hy' := (hsub y hy).1; linarith
      have h2 : y - x < d := by have hx' := (hsub x hx).1; linarith
      have h3 : |x - y| < d := abs_lt.mpr ⟨by linarith, h1⟩
      by_contra hne
      exact absurd (hsep x hx y hy hne) (by linarith)
    · have hxge : lo + d ≤ x := not_lt.mp hx1
      have hy1 : ¬ y < lo + d := by
        by_contra hy1
        rw [if_neg hx1, if_pos hy1] at hxy
        exact absurd hxy (by norm_num)
      have hyge : lo + d ≤ y := not_lt.mp hy1
      have h1 : x - y < d := by have := (hsub x hx).2; linarith
      have h2 : y - x < d := by have := (hsub y hy).2; linarith
      have h3 : |x - y| < d := abs_lt.mpr ⟨by linarith, h1⟩
      by_contra hne
      exact absurd (hsep x hx y hy hne) (by linarith)
  have hcard : s.card ≤ ({0, 1} : Finset ℝ).card :=
    Finset.card_le_card_of_injOn (fun x : ℝ => if x < lo + d then (0 : ℝ) else 1) hmem hinj
  calc s.card ≤ ({0, 1} : Finset ℝ).card := hcard
    _ = 2 := Finset.card_pair (by norm_num)

/-- **Successor bound with the `200·L` window.**  Fix `x ∈ T` and a pair `(a,b)` of labels.  Every
`y ∈ T` with `Adj x y` and `pr x y = (a,b)` satisfies `|pos x - (b/a)·pos y| ≤ 200 L`, i.e.
`pos y ∈ [(pos x - 200L)·(a/b), (pos x + 200L)·(a/b)]`, an interval of length `400L·(a/b) ≤ 800L`
(using `a ≤ 2P ≤ 2b`).  Since distinct points of `T` are `500L`-separated and `800L < 2·500L`,
those `pos`-values take at most two values, and each `pos`-fiber of `T` has at most `K` elements. -/
lemma succ_card_le_v2 {V : Type} [Fintype V] [DecidableEq V]
    (Adj : V → V → Prop) [DecidableRel Adj] (T : Finset V) (pos : V → ℝ) (pr : V → V → ℕ × ℕ)
    (P L : ℝ) (hL : 0 < L) (K : ℕ)
    (hpr : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' →
      Work.BMF.IsPrimeIn P (2 * P) (pr v v').1 ∧ Work.BMF.IsPrimeIn P (2 * P) (pr v v').2)
    (hgeo : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' →
      |pos v - (((pr v v').2 : ℕ) : ℝ) / (((pr v v').1 : ℕ) : ℝ) * pos v'| ≤ 200 * L)
    (hfib : ∀ y : ℝ, ((T.filter (fun v ↦ pos v = y)).card : ℝ) ≤ (K : ℝ))
    (hsep : ∀ v ∈ T, ∀ v' ∈ T, pos v ≠ pos v' → 500 * L ≤ |pos v - pos v'|)
    (x : V) (hxT : x ∈ T) (a b : ℕ) :
    ((T.filter (fun y ↦ Adj x y ∧ (pr x y).1 = a ∧ (pr x y).2 = b)).card : ℝ) ≤ 2 * (K : ℝ) := by
  classical
  set Sx : Finset V := T.filter (fun y ↦ Adj x y ∧ (pr x y).1 = a ∧ (pr x y).2 = b) with hSx
  rcases Finset.eq_empty_or_nonempty Sx with hE | ⟨y₀, hy₀⟩
  · rw [hE, Finset.card_empty, Nat.cast_zero]
    positivity
  · have hmem : ∀ y ∈ Sx, y ∈ T ∧ Adj x y ∧ (pr x y).1 = a ∧ (pr x y).2 = b :=
      fun y hy => Finset.mem_filter.mp hy
    obtain ⟨hy0T, hAx0, ha0, hb0⟩ := hmem y₀ hy₀
    have hpr0 := hpr x hxT y₀ hy0T hAx0
    have haP : P ≤ (a : ℝ) := by rw [← ha0]; exact hpr0.1.2.1
    have hbP : P ≤ (b : ℝ) := by rw [← hb0]; exact hpr0.2.2.1
    have ha2P : (a : ℝ) ≤ 2 * P := by rw [← ha0]; exact hpr0.1.2.2
    have ha2 : 2 ≤ a := by rw [← ha0]; exact hpr0.1.1.two_le
    have hb2 : 2 ≤ b := by rw [← hb0]; exact hpr0.2.1.two_le
    have hapos : (0 : ℝ) < (a : ℝ) := by
      have h2 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha2
      linarith
    have hbpos : (0 : ℝ) < (b : ℝ) := by
      have h2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb2
      linarith
    have hane : (a : ℝ) ≠ 0 := ne_of_gt hapos
    have hbne : (b : ℝ) ≠ 0 := ne_of_gt hbpos
    have hratio : (a : ℝ) / (b : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hbpos]
      linarith
    set lo : ℝ := (pos x - 200 * L) * ((a : ℝ) / (b : ℝ)) with hlo
    set hi : ℝ := (pos x + 200 * L) * ((a : ℝ) / (b : ℝ)) with hhi
    have hq : (0 : ℝ) ≤ (a : ℝ) / (b : ℝ) := le_of_lt (div_pos hapos hbpos)
    have hratio' : ((a : ℝ) / (b : ℝ)) * ((b : ℝ) / (a : ℝ)) = 1 := by
      rw [div_mul_div_comm, mul_comm (b : ℝ) (a : ℝ), div_self (mul_ne_zero hane hbne)]
    have hsub_img : ∀ z ∈ Sx.image pos, lo ≤ z ∧ z ≤ hi := by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨y, hySx, rfl⟩ := hz
      obtain ⟨hyT, hAxy, ha, hb⟩ := hmem y hySx
      have hgy := hgeo x hxT y hyT hAxy
      rw [hb, ha] at hgy
      have hp1 : pos x - 200 * L ≤ ((b : ℝ) / (a : ℝ)) * pos y := by
        have h := (abs_le.mp hgy).2
        linarith
      have hp2 : ((b : ℝ) / (a : ℝ)) * pos y ≤ pos x + 200 * L := by
        have h := (abs_le.mp hgy).1
        linarith
      have key1 : ((a : ℝ) / (b : ℝ)) * (((b : ℝ) / (a : ℝ)) * pos y) = pos y := by
        rw [← mul_assoc, hratio', one_mul]
      constructor
      · rw [hlo]
        calc (pos x - 200 * L) * ((a : ℝ) / (b : ℝ))
            = ((a : ℝ) / (b : ℝ)) * (pos x - 200 * L) := by ring
          _ ≤ ((a : ℝ) / (b : ℝ)) * (((b : ℝ) / (a : ℝ)) * pos y) :=
              mul_le_mul_of_nonneg_left hp1 hq
          _ = pos y := key1
      · rw [hhi]
        calc pos y = ((a : ℝ) / (b : ℝ)) * (((b : ℝ) / (a : ℝ)) * pos y) := key1.symm
          _ ≤ ((a : ℝ) / (b : ℝ)) * (pos x + 200 * L) := mul_le_mul_of_nonneg_left hp2 hq
          _ = (pos x + 200 * L) * ((a : ℝ) / (b : ℝ)) := by ring
    have himg_sep : ∀ z ∈ Sx.image pos, ∀ z' ∈ Sx.image pos, z ≠ z' → 500 * L ≤ |z - z'| := by
      intro z hz z' hz' hne
      rw [Finset.mem_image] at hz hz'
      obtain ⟨y, hySx, rfl⟩ := hz
      obtain ⟨y', hy'Sx, rfl⟩ := hz'
      exact hsep y (hmem y hySx).1 y' (hmem y' hy'Sx).1 hne
    have hlen : hi - lo < 2 * (500 * L) := by
      have hsub2 : hi - lo = ((a : ℝ) / (b : ℝ)) * (400 * L) := by
        rw [hhi, hlo]; ring
      rw [hsub2]
      have h4 : ((a : ℝ) / (b : ℝ)) * (400 * L) ≤ 2 * (400 * L) :=
        mul_le_mul_of_nonneg_right hratio (by linarith)
      linarith
    have himg_card : (Sx.image pos).card ≤ 2 :=
      card_le_two_of_sep (s := Sx.image pos) (lo := lo) (hi := hi) (d := 500 * L)
        hsub_img himg_sep hlen
    have hfiber : ∀ z : ℝ, (Sx.filter (fun y ↦ pos y = z)).card ≤ K := by
      intro z
      have hsub' : Sx.filter (fun y ↦ pos y = z) ⊆ T.filter (fun v ↦ pos v = z) := by
        intro y hy
        rw [Finset.mem_filter] at hy ⊢
        exact ⟨(hmem y hy.1).1, hy.2⟩
      have h1 : ((Sx.filter (fun y ↦ pos y = z)).card : ℝ) ≤ (K : ℝ) :=
        le_trans (by exact_mod_cast Finset.card_le_card hsub') (hfib z)
      exact_mod_cast h1
    have hstep : Sx.card ≤ K * (Sx.image pos).card :=
      Finset.card_le_mul_card_image (f := pos) Sx K (fun b _ => hfiber b)
    have h1 : (Sx.card : ℝ) ≤ ((K * (Sx.image pos).card : ℕ) : ℝ) := by exact_mod_cast hstep
    have h2 : ((K * (Sx.image pos).card : ℕ) : ℝ) = (K : ℝ) * ((Sx.image pos).card : ℝ) := by
      rw [Nat.cast_mul]
    rw [h2] at h1
    have himg2 : ((Sx.image pos).card : ℝ) ≤ 2 := by exact_mod_cast himg_card
    have h3 : (K : ℝ) * ((Sx.image pos).card : ℝ) ≤ (K : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left himg2 (Nat.cast_nonneg K)
    linarith

theorem step6v2_walk_fiber {V : Type} [Fintype V] [DecidableEq V]
    (Adj : V → V → Prop) [DecidableRel Adj]
    (T : Finset V) (pos : V → ℝ) (pr : V → V → ℕ × ℕ) (ℓ : ℕ) (hℓ2 : 2 ≤ ℓ)
    (P L : ℝ) (hL : 0 < L) (K : ℕ)
    (hedge : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' →
      Work.BMF.IsPrimeIn P (2 * P) (pr v v').1 ∧ Work.BMF.IsPrimeIn P (2 * P) (pr v v').2)
    (hgeo : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' →
      |pos v - (((pr v v').2 : ℕ) : ℝ) / (((pr v v').1 : ℕ) : ℝ) * pos v'| ≤ 200 * L)
    (hfib : ∀ y : ℝ, ((T.filter (fun v ↦ pos v = y)).card : ℝ) ≤ (K : ℝ))
    (hsep : ∀ v ∈ T, ∀ v' ∈ T, pos v ≠ pos v' → 500 * L ≤ |pos v - pos v'|)
    (u : V) (hu : u ∈ T) (v₁ v₂ : Fin ℓ → ℕ) :
    ((Finset.univ.filter (fun w : Fin ℓ → V ↦ w ∈ Work.N8.step6Walks Adj T ℓ ∧
        w ⟨0, by omega⟩ = u ∧
        Work.N8.step6Tuple1 ℓ pr w = v₁ ∧ Work.N8.step6Tuple2 ℓ pr w = v₂)).card : ℝ)
      ≤ (4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ := by
  classical
  have hK1 : 1 ≤ K := by
    have hmem : u ∈ T.filter (fun v ↦ pos v = pos u) := Finset.mem_filter.mpr ⟨hu, rfl⟩
    have h1 : (1 : ℝ) ≤ ((T.filter (fun v ↦ pos v = pos u)).card : ℝ) := by
      have h := Finset.card_pos.mpr ⟨u, hmem⟩
      have h' : (1 : ℕ) ≤ (T.filter (fun v ↦ pos v = pos u)).card := by omega
      exact_mod_cast h'
    have h2 : (1 : ℝ) ≤ (K : ℝ) := by
      have h3 := hfib (pos u)
      linarith
    exact_mod_cast h2
  set S : Fin ℓ → V → Finset V := fun j x =>
      if x ∈ T then T.filter (fun y ↦ Adj x y ∧ (pr x y).1 = v₁ j ∧ (pr x y).2 = v₂ j)
      else ∅ with hSdef
  have hS : ∀ (j : Fin ℓ) (x : V), (S j x).card ≤ 2 * K := by
    intro j x
    by_cases hx : x ∈ T
    · have hSx : S j x
          = T.filter (fun y ↦ Adj x y ∧ (pr x y).1 = v₁ j ∧ (pr x y).2 = v₂ j) := by
        rw [hSdef]; simp [hx]
      rw [hSx]
      have h := succ_card_le_v2 Adj T pos pr P L hL K hedge hgeo hfib hsep x hx (v₁ j) (v₂ j)
      exact_mod_cast h
    · have hSx : S j x = ∅ := by
        rw [hSdef]; simp [hx]
      rw [hSx, Finset.card_empty]
      omega
  have h2K : 1 ≤ 2 * K := by omega
  have hchain : ((chainSet ℓ u S).card : ℝ) ≤ ((2 * K : ℕ) : ℝ) ^ ℓ :=
    chain_card_le ℓ u S (2 * K) h2K hS
  have hsub : (Finset.univ.filter (fun w : Fin ℓ → V ↦ w ∈ step6Walks Adj T ℓ ∧
        w ⟨0, by omega⟩ = u ∧
        step6Tuple1 ℓ pr w = v₁ ∧ step6Tuple2 ℓ pr w = v₂)) ⊆ chainSet ℓ u S := by
    intro w hw
    obtain ⟨_, hwWalks, hw0, hwt1, hwt2⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwT, hwAdj⟩ := mem_step6Walks.mp hwWalks
    rw [chainSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ w, ?_, ?_⟩
    · intro h
      exact hw0
    · intro j hj
      have hTj : w j ∈ T := hwT j
      have hSx : S j (w j)
          = T.filter (fun y ↦ Adj (w j) y ∧ (pr (w j) y).1 = v₁ j ∧ (pr (w j) y).2 = v₂ j) := by
        rw [hSdef]; simp [hTj]
      rw [hSx, Finset.mem_filter]
      have hnext : step6next ℓ j = (⟨(j : ℕ) + 1, hj⟩ : Fin ℓ) := by
        apply Fin.ext
        simp [step6next, Nat.mod_eq_of_lt hj]
      refine ⟨hwT ⟨(j : ℕ) + 1, hj⟩, ?_, ?_, ?_⟩
      · have h := hwAdj j
        rwa [hnext] at h
      · have h : (pr (w j) (w (step6next ℓ j))).1 = v₁ j := congrFun hwt1 j
        rwa [hnext] at h
      · have h : (pr (w j) (w (step6next ℓ j))).2 = v₂ j := congrFun hwt2 j
        rwa [hnext] at h
  calc ((Finset.univ.filter (fun w : Fin ℓ → V ↦ w ∈ step6Walks Adj T ℓ ∧
        w ⟨0, by omega⟩ = u ∧
        step6Tuple1 ℓ pr w = v₁ ∧ step6Tuple2 ℓ pr w = v₂)).card : ℝ)
      ≤ ((chainSet ℓ u S).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((2 * K : ℕ) : ℝ) ^ ℓ := hchain
    _ = (2 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ := by push_cast; ring
    _ ≤ (4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (Nat.cast_nonneg K) ℓ)
        exact pow_le_pow_left₀ (by norm_num) (by norm_num) ℓ

end Work.N8
