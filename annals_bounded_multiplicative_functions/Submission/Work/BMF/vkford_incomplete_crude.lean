import Mathlib
import Submission.Work.BMF.vkford_defs
import Submission.Work.BMF.fiber_pairs_sq_sum
import Submission.Work.BMF.card_box_le
import Submission.Work.BMF.Jincom_one_le_vJ

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Ford's crude bound for the incomplete Vinogradov system (Ford (1.9))

For `B ⊆ [1,P]`, the number `Jincom s k h B` of solutions of the *incomplete* system
`Σᵢ xᵢʲ = Σᵢ yᵢʲ` (`h ≤ j ≤ k`, `xᵢ,yᵢ ∈ B`) is at most `s^{h-1} P^{h(h-1)/2} · J_{s,k}(P)`.

The factor `s^{h-1} P^{h(h-1)/2}` is an upper bound for the number of possible values of the
*missing* power sums `(Σᵢ xᵢʲ)_{j=1}^{h-1}`: the `j`-th one lies in `[s, sP^j]`, an interval with at
most `sP^j` integers.  Splitting the degrees `1 ≤ j ≤ k` into `1 ≤ j ≤ h-1` (`keyB`) and
`h ≤ j ≤ k` (`keyA`), the solutions of the incomplete system are the `keyA`-collisions, while the
solutions of the complete system on `B` are the joint `(keyB,keyA)`-collisions.  The collision
reduction `card_collision_le_aux` (Cauchy–Schwarz over the `keyA`-fibres, each split into at most `#T`
`keyB`-pieces) converts the former into the latter at the cost of the factor `#T`.
-/

namespace Work.BMF

open Finset
open scoped BigOperators

/-- The power-sum key for the degrees `h, …, k`. -/
private def keyA (s k h : ℕ) (B : Finset ℕ) : (Fin s → B) → (Fin (k - h + 1) → ℕ) :=
  fun x i => ∑ t, ((x t : ℕ)) ^ (i.val + h)

/-- The power-sum key for the degrees `1, …, h-1`. -/
private def keyB (s h : ℕ) (B : Finset ℕ) : (Fin s → B) → (Fin (h - 1) → ℕ) :=
  fun x i => ∑ t, ((x t : ℕ)) ^ (i.val + 1)

/-- `keyA` records exactly the power sums of degrees `h, …, k`. -/
private lemma keyA_eq_iff (s k h : ℕ) (B : Finset ℕ) (_hh : 1 ≤ h) (hhk : h ≤ k)
    (x y : Fin s → B) :
    keyA s k h B x = keyA s k h B y ↔
      ∀ j : ℕ, h ≤ j → j ≤ k → (∑ i, (x i : ℕ) ^ j) = (∑ i, (y i : ℕ) ^ j) := by
  constructor
  · intro h1 j hj hjk
    rw [← Nat.sub_add_cancel hj]
    exact congrFun h1 (⟨j - h, by omega⟩ : Fin (k - h + 1))
  · intro h1
    funext i
    exact h1 (i.val + h) (by omega) (by omega)

/-- Together, `keyB` and `keyA` record all the power sums of degrees `1, …, k`. -/
private lemma keyB_keyA_eq_iff (s k h : ℕ) (B : Finset ℕ) (_hh : 1 ≤ h) (hhk : h ≤ k)
    (x y : Fin s → B) :
    (keyB s h B x = keyB s h B y ∧ keyA s k h B x = keyA s k h B y) ↔
      ∀ j : ℕ, 1 ≤ j → j ≤ k → (∑ i, (x i : ℕ) ^ j) = (∑ i, (y i : ℕ) ^ j) := by
  constructor
  · rintro ⟨h1, h2⟩ j hj1 hjk
    by_cases hjcase : j ≤ h - 1
    · rw [← Nat.sub_add_cancel hj1]
      exact congrFun h1 (⟨j - 1, by omega⟩ : Fin (h - 1))
    · rw [← Nat.sub_add_cancel (by omega : h ≤ j)]
      exact congrFun h2 (⟨j - h, by omega⟩ : Fin (k - h + 1))
  · intro h1
    refine ⟨?_, ?_⟩
    · funext i
      exact h1 (i.val + 1) (by omega) (by omega)
    · funext i
      exact h1 (i.val + h) (by omega) (by omega)


/-- Cauchy–Schwarz for a sum of naturals: `(∑ f)^2 ≤ #s · ∑ f^2`. -/
private lemma sq_sum_le_card_mul_sum_sq_nat {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => ((f i : ℕ) : ℝ))
  simp only [← Nat.cast_sum, ← Nat.cast_pow, ← Nat.cast_mul] at h
  exact Nat.cast_le.mp h

/-- **Collision reduction (Cauchy–Schwarz).**  If every `keyB`-value lies in `T`, then the number of
ordered pairs of points of `Ω` on which `keyA` collides is at most `#T` times the number of ordered
pairs on which both `keyA` and `keyB` collide. -/
private lemma card_collision_le_aux {Ω β γ : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq β] [DecidableEq γ]
    (keyB : Ω → β) (keyA : Ω → γ) (T : Finset β) (hT : ∀ x : Ω, keyB x ∈ T) :
    (((Finset.univ : Finset Ω) ×ˢ (Finset.univ : Finset Ω)).filter
        (fun q : Ω × Ω => keyA q.1 = keyA q.2)).card ≤
      T.card * (((Finset.univ : Finset Ω) ×ˢ (Finset.univ : Finset Ω)).filter
        (fun q : Ω × Ω => keyB q.1 = keyB q.2 ∧ keyA q.1 = keyA q.2)).card := by
  classical
  let G : β × γ → ℕ := fun p => ((Finset.univ : Finset Ω).filter (fun x => (keyB x, keyA x) = p)).card
  let F : β × γ → ℕ := fun p => G p ^ 2
  let nA : γ → ℕ := fun a => ((Finset.univ : Finset Ω).filter (fun x => keyA x = a)).card
  set A : Finset γ := (Finset.univ : Finset Ω).image keyA with hA
  set M : Finset (β × γ) := (Finset.univ : Finset Ω).image (fun x => (keyB x, keyA x)) with hM
  have hL : (((Finset.univ : Finset Ω) ×ˢ (Finset.univ : Finset Ω)).filter
        (fun q : Ω × Ω => keyA q.1 = keyA q.2)).card = ∑ a ∈ A, nA a ^ 2 := by
    rw [hA]
    exact fiber_pairs_sq_sum keyA
  have hR : (((Finset.univ : Finset Ω) ×ˢ (Finset.univ : Finset Ω)).filter
        (fun q : Ω × Ω => keyB q.1 = keyB q.2 ∧ keyA q.1 = keyA q.2)).card
      = ∑ c ∈ M, F c := by
    rw [hM]
    have hflt : (((Finset.univ : Finset Ω) ×ˢ (Finset.univ : Finset Ω)).filter
          (fun q : Ω × Ω => keyB q.1 = keyB q.2 ∧ keyA q.1 = keyA q.2))
        = (((Finset.univ : Finset Ω) ×ˢ (Finset.univ : Finset Ω)).filter
          (fun q : Ω × Ω => (keyB q.1, keyA q.1) = (keyB q.2, keyA q.2))) := by
      apply Finset.filter_congr
      intro q _
      simp [Prod.mk.injEq]
    rw [hflt]
    exact fiber_pairs_sq_sum (fun x => (keyB x, keyA x))
  have hfib : ∀ a : γ, nA a = ∑ b ∈ T, G (b, a) := by
    intro a
    show ((Finset.univ : Finset Ω).filter (fun x => keyA x = a)).card = ∑ b ∈ T, G (b, a)
    rw [Finset.card_eq_sum_card_fiberwise (f := keyB)
      (s := (Finset.univ : Finset Ω).filter (fun x => keyA x = a)) (t := T) (fun x _ => hT x)]
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
    tauto
  have hCS : ∀ a : γ, nA a ^ 2 ≤ T.card * ∑ b ∈ T, F (b, a) := by
    intro a
    rw [hfib a]
    exact sq_sum_le_card_mul_sum_sq_nat T (fun b => G (b, a))
  have hstep1 : ∑ a ∈ A, nA a ^ 2 ≤ T.card * ∑ a ∈ A, ∑ b ∈ T, F (b, a) := by
    calc ∑ a ∈ A, nA a ^ 2
        ≤ ∑ a ∈ A, T.card * ∑ b ∈ T, F (b, a) := Finset.sum_le_sum (fun a _ => hCS a)
      _ = T.card * ∑ a ∈ A, ∑ b ∈ T, F (b, a) := by rw [Finset.mul_sum]
  have hMsub : M ⊆ T ×ˢ A := by
    intro c hc
    rw [hM] at hc
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hc
    rw [← hx, Finset.mem_product]
    exact ⟨hT x, Finset.mem_image_of_mem keyA (Finset.mem_univ x)⟩
  have hzero : ∀ c ∈ T ×ˢ A, c ∉ M → F c = 0 := by
    intro c _ hc
    have hempty : (Finset.univ : Finset Ω).filter (fun x => (keyB x, keyA x) = c) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x _ hx
      exact hc (by rw [hM]; exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩)
    show G c ^ 2 = 0
    have hG : G c = 0 := by
      show ((Finset.univ : Finset Ω).filter (fun x => (keyB x, keyA x) = c)).card = 0
      rw [hempty]; simp
    rw [hG]; simp
  have hstep2 : ∑ a ∈ A, ∑ b ∈ T, F (b, a) = ∑ c ∈ M, F c := by
    rw [show (∑ a ∈ A, ∑ b ∈ T, F (b, a)) = (∑ b ∈ T, ∑ a ∈ A, F (b, a)) from
      Finset.sum_comm (s := A) (t := T) (f := fun a b => F (b, a))]
    rw [show (∑ b ∈ T, ∑ a ∈ A, F (b, a)) = (∑ c ∈ T ×ˢ A, F c) from
      (Finset.sum_product T A F).symm]
    exact (Finset.sum_subset hMsub hzero).symm
  rw [hL, hR]
  exact le_trans hstep1 (le_of_eq (by rw [hstep2]))

theorem vkford_incomplete_crude
    (s k h P : ℕ) (B : Finset ℕ) (hs : 1 ≤ s) (hh : 1 ≤ h) (hhk : h ≤ k)
    (hB : B ⊆ Finset.Icc 1 P) :
    Work.BMF.Jincom s k h B
      ≤ (s : ℝ) ^ (h - 1) * (P : ℝ) ^ (h * (h - 1) / 2) * Work.BMF.vJ s k P := by
  classical
  have hbox := card_box_le s h P hs
  have hone := Jincom_one_le_vJ s k P B hB
  -- `T` : the box of possible values of the "free" power sums `Σᵢ xᵢʲ`, `1 ≤ j ≤ h-1`
  have hT : ∀ x : Fin s → B, keyB s h B x ∈
      Fintype.piFinset (fun i : Fin (h - 1) => Finset.Icc s (s * P ^ (i.val + 1))) := by
    intro x
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    constructor
    · change s ≤ ∑ t : Fin s, ((x t : ℕ)) ^ (i.val + 1)
      calc s = ∑ _t : Fin s, 1 := by simp
        _ ≤ ∑ t : Fin s, ((x t : ℕ)) ^ (i.val + 1) := by
            apply Finset.sum_le_sum
            intro t _
            have ht : 1 ≤ ((x t : ℕ)) := (Finset.mem_Icc.mp (hB (x t).2)).1
            calc (1 : ℕ) = 1 ^ (i.val + 1) := by simp
              _ ≤ ((x t : ℕ)) ^ (i.val + 1) := Nat.pow_le_pow_left ht _
    · change (∑ t : Fin s, ((x t : ℕ)) ^ (i.val + 1)) ≤ s * P ^ (i.val + 1)
      calc (∑ t : Fin s, ((x t : ℕ)) ^ (i.val + 1)) ≤ ∑ _t : Fin s, P ^ (i.val + 1) := by
            apply Finset.sum_le_sum
            intro t _
            have ht : ((x t : ℕ)) ≤ P := (Finset.mem_Icc.mp (hB (x t).2)).2
            exact Nat.pow_le_pow_left ht _
        _ = s * P ^ (i.val + 1) := by simp
  -- the incomplete system is exactly the `keyA`-collision count
  have hLHS : Jincom s k h B
      = (((Finset.univ : Finset ((Fin s → B) × (Fin s → B))).filter
          (fun q : (Fin s → B) × (Fin s → B) => keyA s k h B q.1 = keyA s k h B q.2)).card : ℝ) := by
    unfold Jincom
    congr 1
    exact congrArg Finset.card
      (Finset.filter_congr (fun q _ => (keyA_eq_iff s k h B hh hhk q.1 q.2).symm))
  -- the complete system on `B` is exactly the joint collision count
  have hRHS : Jincom s k 1 B
      = (((Finset.univ : Finset ((Fin s → B) × (Fin s → B))).filter
          (fun q : (Fin s → B) × (Fin s → B) =>
            keyB s h B q.1 = keyB s h B q.2 ∧ keyA s k h B q.1 = keyA s k h B q.2)).card : ℝ) := by
    unfold Jincom
    congr 1
    exact congrArg Finset.card
      (Finset.filter_congr (fun q _ => (keyB_keyA_eq_iff s k h B hh hhk q.1 q.2).symm))
  -- Cauchy–Schwarz collision reduction
  have hcoll := card_collision_le_aux (keyB s h B) (keyA s k h B)
      (Fintype.piFinset (fun i : Fin (h - 1) => Finset.Icc s (s * P ^ (i.val + 1)))) hT
  rw [Finset.univ_product_univ] at hcoll
  have h1 : Jincom s k h B
      ≤ ((Fintype.piFinset (fun i : Fin (h - 1) => Finset.Icc s (s * P ^ (i.val + 1)))).card : ℝ)
        * Jincom s k 1 B := by
    rw [hLHS, hRHS]
    exact_mod_cast hcoll
  have h2 : ((Fintype.piFinset (fun i : Fin (h - 1) => Finset.Icc s (s * P ^ (i.val + 1)))).card : ℝ)
      ≤ (s : ℝ) ^ (h - 1) * (P : ℝ) ^ (h * (h - 1) / 2) := by
    exact_mod_cast hbox
  calc Jincom s k h B
      ≤ ((Fintype.piFinset (fun i : Fin (h - 1) => Finset.Icc s (s * P ^ (i.val + 1)))).card : ℝ)
          * Jincom s k 1 B := h1
    _ ≤ ((s : ℝ) ^ (h - 1) * (P : ℝ) ^ (h * (h - 1) / 2)) * (vJ s k P) :=
        mul_le_mul h2 hone (by unfold Jincom; exact Nat.cast_nonneg _)
          (mul_nonneg (pow_nonneg (Nat.cast_nonneg s) _) (pow_nonneg (Nat.cast_nonneg P) _))
    _ = (s : ℝ) ^ (h - 1) * (P : ℝ) ^ (h * (h - 1) / 2) * (vJ s k P) := by ring

end Work.BMF
