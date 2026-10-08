import Mathlib
import Submission.Work.GlaubermanZJ.Thm41.PComm
import Submission.Work.GlaubermanZJ.Thm41.IterComm

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The lower central series of `S = A·B` inside `[B,A;k] ⊔ [B,B]`

Let `S` be a subgroup of a group `G` with `S = A ⊔ B` (`A, B ≤ S`), where `B` is normalised by
`S` and `A` is abelian.  Then every term of the lower central series of `S` satisfies

`S.lowerCentralSeries k ≤ [B,A;k] ⊔ ⁅B,B⁆`  for `k ≥ 1`,

where `[B,A;k] = iterComm B A k` denotes the `k`-fold left-normed commutator
`[[[B,A],A],…,A]`.

The intuition is that every generator of `γₖ(S)` is a left-normed commutator of `k` elements of
`S`, each of which can be written `a·b` with `a ∈ A`, `b ∈ B`; since `A` is abelian and `B` is
normal, the `A`'s contribute one further `A` at each step, while every contribution involving a
`B` in the "wrong" slot collapses into `⁅B,B⁆`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.GlaubermanZJ.Thm41

variable {G : Type*} [Group G]

/-- If `H` normalises `K`, then `H ⊔ K` is the set of products `h * k` with `h ∈ H`, `k ∈ K`.

(Without a normality/normaliser hypothesis an element of `H ⊔ K` is only an alternating word.) -/
theorem mem_sup_of_le_normalizer {H K : Subgroup G}
    (h : H ≤ Subgroup.normalizer (K : Set G)) {x : G} :
    x ∈ H ⊔ K ↔ ∃ a ∈ H, ∃ b ∈ K, a * b = x := by
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · rintro y (hy | hy)
      · exact ⟨y, hy, 1, K.one_mem, by simp⟩
      · exact ⟨1, H.one_mem, y, hy, by simp⟩
    · exact ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
      have hb1' : a₂⁻¹ * b₁ * a₂ ∈ K := by
        have h2 := h ha₂
        rw [Subgroup.mem_normalizer_iff''] at h2
        exact (h2 b₁).mp hb₁
      exact ⟨a₁ * a₂, H.mul_mem ha₁ ha₂, (a₂⁻¹ * b₁ * a₂) * b₂, K.mul_mem hb1' hb₂, by group⟩
    · rintro _ _ ⟨a, ha, b, hb, rfl⟩
      have h2 := h ha
      rw [Subgroup.mem_normalizer_iff] at h2
      exact ⟨a⁻¹, H.inv_mem ha, a * b⁻¹ * a⁻¹, (h2 b⁻¹).mp (K.inv_mem hb), by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

/-- Conjugation by an element of `H` maps `K` into itself if `H` normalises `K`. -/
theorem conj_mem_of_le_normalizer {H K : Subgroup G}
    (h : H ≤ Subgroup.normalizer (K : Set G)) {a x : G} (ha : a ∈ H) (hx : x ∈ K) :
    a * x * a⁻¹ ∈ K :=
  (Subgroup.mem_normalizer_iff.mp (h ha) x).mp hx

/-- Two elements of a commutative subgroup commute. -/
theorem mul_comm_of_mem {H : Subgroup G} (hH : IsMulCommutative H) {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) : a * b = b * a := by
  have h := isMulCommutative_iff.mp hH ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val h

/-- A subgroup normalising `B` also normalises the commutator subgroup `⁅B,B⁆`. -/
theorem le_normalizer_commutator_self {B K : Subgroup G}
    (h : K ≤ Subgroup.normalizer (B : Set G)) :
    K ≤ Subgroup.normalizer (⁅B, B⁆ : Subgroup G) := by
  rw [Subgroup.le_normalizer_iff] at h ⊢
  intro s hs y hy
  have hmap : B.map (MulAut.conj s : G →* G) ≤ B := by
    rw [Subgroup.map_le_iff_le_comap]
    intro b hb
    rw [Subgroup.mem_comap]
    show s * b * s⁻¹ ∈ B
    exact h s hs b hb
  have hle : (⁅B, B⁆).map (MulAut.conj s : G →* G) ≤ ⁅B, B⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hmap hmap
  have hmem : s * y * s⁻¹ ∈ (⁅B, B⁆).map (MulAut.conj s : G →* G) :=
    Subgroup.mem_map.mpr ⟨y, hy, by show (MulAut.conj s : G →* G) y = s * y * s⁻¹; rfl⟩
  exact hle hmem

theorem lowerCentralSeries_le_iterComm_sup {G : Type*} [Group G] (S A B : Subgroup G)
    (hAS : A ≤ S) (hBS : B ≤ S) (hSAB : S ≤ A ⊔ B)
    (hBn : S ≤ Subgroup.normalizer (B : Set G)) (hAab : IsMulCommutative A) :
    ∀ k, 1 ≤ k → S.lowerCentralSeries k ≤ Work.GlaubermanZJ.iterComm B A k ⊔ ⁅B, B⁆ := by
  have hAn : A ≤ Subgroup.normalizer (B : Set G) := hAS.trans hBn
  have hBA : ⁅B, A⁆ ≤ B :=
    (Subgroup.commutator_comm A B) ▸ (Subgroup.le_normalizer_iff_commutator_le_right.mp hAn)
  have hA_BB : A ≤ Subgroup.normalizer (⁅B, B⁆ : Subgroup G) := le_normalizer_commutator_self hAn
  have hB_BB : B ≤ Subgroup.normalizer (⁅B, B⁆ : Subgroup G) :=
    Subgroup.normalizer_commutator_ge_left B B
  have hIterB : ∀ k, Work.GlaubermanZJ.iterComm B A k ≤ B := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
        rw [Work.GlaubermanZJ.iterComm_succ]
        exact (Subgroup.commutator_mono ih le_rfl).trans hBA
  have hSeq : S = A ⊔ B := le_antisymm hSAB (sup_le hAS hBS)
  -- Step 1: `[S,S] ≤ [B,A] ⊔ [B,B]`.
  have hbase : S.lowerCentralSeries 1 ≤ Work.GlaubermanZJ.iterComm B A 1 ⊔ ⁅B, B⁆ := by
    have hSS : S.lowerCentralSeries 1 = ⁅S, S⁆ := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, Subgroup.lowerCentralSeries_succ,
        Subgroup.lowerCentralSeries_zero]
    rw [hSS, Work.GlaubermanZJ.iterComm_one, Subgroup.commutator_le]
    intro s₁ hs₁ s₂ hs₂
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := (mem_sup_of_le_normalizer hAn).mp (hSeq ▸ hs₁)
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := (mem_sup_of_le_normalizer hAn).mp (hSeq ▸ hs₂)
    rw [commutatorElement_mul_left_eq_conj_mul]
    refine mul_mem ?_ ?_
    · rw [commutatorElement_mul_right_eq_mul_conj]
      have hu : ⁅b₁, a₂⁆ ∈ ⁅B, A⁆ := Subgroup.commutator_mem_commutator hb₁ ha₂
      have hv : a₂ * ⁅b₁, b₂⁆ * a₂⁻¹ ∈ ⁅B, B⁆ :=
        conj_mem_of_le_normalizer hA_BB ha₂ (Subgroup.commutator_mem_commutator hb₁ hb₂)
      rw [show a₁ * (⁅b₁, a₂⁆ * a₂ * ⁅b₁, b₂⁆ * a₂⁻¹) * a₁⁻¹
            = (a₁ * ⁅b₁, a₂⁆ * a₁⁻¹) * (a₁ * (a₂ * ⁅b₁, b₂⁆ * a₂⁻¹) * a₁⁻¹) from by group]
      refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
      · exact conj_mem_of_le_normalizer (Subgroup.normalizer_commutator_ge_right B A) ha₁ hu
      · exact conj_mem_of_le_normalizer hA_BB ha₁ hv
    · rw [commutatorElement_mul_right_eq_mul_conj]
      have hab : ⁅a₁, a₂⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact mul_comm_of_mem hAab ha₁ ha₂
      rw [hab, one_mul]
      exact Subgroup.mem_sup_left
        (conj_mem_of_le_normalizer (Subgroup.normalizer_commutator_ge_right B A) ha₂
          ((Subgroup.commutator_comm A B) ▸ Subgroup.commutator_mem_commutator ha₁ hb₂))
  -- Step 2: `[D(k), S] ≤ D(k+1)` where `D(k) = [B,A;k] ⊔ [B,B]`.
  have hstep : ∀ k, 1 ≤ k →
      ⁅Work.GlaubermanZJ.iterComm B A k ⊔ ⁅B, B⁆, S⁆ ≤
        Work.GlaubermanZJ.iterComm B A (k + 1) ⊔ ⁅B, B⁆ := by
    intro k _hk
    rw [Subgroup.commutator_le]
    intro x hx s hs
    obtain ⟨c, hc, y, hy, rfl⟩ :=
      (mem_sup_of_le_normalizer ((hIterB k).trans hB_BB)).mp hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_le_normalizer hAn).mp (hSeq ▸ hs)
    rw [commutatorElement_mul_left_eq_conj_mul]
    refine mul_mem ?_ ?_
    · have hyab : ⁅y, a * b⁆ ∈ ⁅B, B⁆ := by
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hya : ⁅y, a⁆ ∈ ⁅B, B⁆ :=
          Subgroup.commutator_le.mp (Subgroup.le_normalizer_iff_commutator_le_left.mp hA_BB)
            y hy a ha
        have hyb : ⁅y, b⁆ ∈ ⁅B, B⁆ :=
          Subgroup.commutator_le.mp (Subgroup.le_normalizer_iff_commutator_le_left.mp hB_BB)
            y hy b hb
        have hayb : a * ⁅y, b⁆ * a⁻¹ ∈ ⁅B, B⁆ := conj_mem_of_le_normalizer hA_BB ha hyb
        rw [show ⁅y, a⁆ * a * ⁅y, b⁆ * a⁻¹ = ⁅y, a⁆ * (a * ⁅y, b⁆ * a⁻¹) from by group]
        exact mul_mem hya hayb
      exact Subgroup.mem_sup_right
        (conj_mem_of_le_normalizer ((hIterB k).trans hB_BB) hc hyab)
    · rw [commutatorElement_mul_right_eq_mul_conj]
      have hca : ⁅c, a⁆ ∈ Work.GlaubermanZJ.iterComm B A (k + 1) := by
        rw [Work.GlaubermanZJ.iterComm_succ]
        exact Subgroup.commutator_mem_commutator hc ha
      have hcb : a * ⁅c, b⁆ * a⁻¹ ∈ ⁅B, B⁆ :=
        conj_mem_of_le_normalizer hA_BB ha
          ((Subgroup.commutator_mono (hIterB k) le_rfl)
            (Subgroup.commutator_mem_commutator hc hb))
      rw [show ⁅c, a⁆ * a * ⁅c, b⁆ * a⁻¹ = ⁅c, a⁆ * (a * ⁅c, b⁆ * a⁻¹) from by group]
      exact mul_mem (Subgroup.mem_sup_left hca) (Subgroup.mem_sup_right hcb)
  -- Step 3: the induction.
  intro k hk
  refine Nat.le_induction (m := 1)
    (P := fun n _ => S.lowerCentralSeries n ≤ Work.GlaubermanZJ.iterComm B A n ⊔ ⁅B, B⁆)
    hbase ?_ k hk
  intro n hn ih
  calc S.lowerCentralSeries (n + 1) = ⁅S.lowerCentralSeries n, S⁆ :=
        Subgroup.lowerCentralSeries_succ S n
    _ ≤ ⁅Work.GlaubermanZJ.iterComm B A n ⊔ ⁅B, B⁆, S⁆ := Subgroup.commutator_mono ih le_rfl
    _ ≤ Work.GlaubermanZJ.iterComm B A (n + 1) ⊔ ⁅B, B⁆ := hstep n hn

end Work.GlaubermanZJ.Thm41
