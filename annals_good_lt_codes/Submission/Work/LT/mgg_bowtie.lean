import Mathlib
import Submission.Work.LT.valMinAbs_add_nowrap
import Submission.Work.LT.valMinAbs_sub_nowrap
import Submission.Work.LT.bowtie_sqrt_bound

namespace Work.LT

open scoped BigOperators

variable {p : ℕ}

/-! ## Definitions -/

/-- Signed (absolutely least) representative of the first coordinate. -/
def sx (z : ZMod p × ZMod p) : ℤ := z.1.valMinAbs

/-- Signed (absolutely least) representative of the second coordinate. -/
def sy (z : ZMod p × ZMod p) : ℤ := z.2.valMinAbs

/-- The four integer "bow-tie" quarters (in signed coordinates). -/
def W1i (x y : ℤ) : Prop := (0 < x ∧ 0 ≤ y ∧ y < x) ∨ (x < 0 ∧ x < y ∧ y ≤ 0)
def W2i (x y : ℤ) : Prop := (0 < y ∧ 0 < x ∧ x ≤ y) ∨ (x < 0 ∧ y < 0 ∧ y ≤ x)
def W3i (x y : ℤ) : Prop := (x ≤ 0 ∧ 0 < y ∧ -x < y) ∨ (y < 0 ∧ 0 ≤ x ∧ x < -y)
def W4i (x y : ℤ) : Prop := (x < 0 ∧ 0 < y ∧ y ≤ -x) ∨ (y < 0 ∧ 0 < x ∧ -y ≤ x)

def U1i (x y : ℤ) : Prop := W1i x y ∨ W2i x y
def U2i (x y : ℤ) : Prop := W3i x y ∨ W4i x y

/-- The four bow-tie quarters as subsets of `(ℤ/p)²`. -/
def W1 (z : ZMod p × ZMod p) : Prop := W1i (sx z) (sy z)
def W2 (z : ZMod p × ZMod p) : Prop := W2i (sx z) (sy z)
def W3 (z : ZMod p × ZMod p) : Prop := W3i (sx z) (sy z)
def W4 (z : ZMod p × ZMod p) : Prop := W4i (sx z) (sy z)
def U1 (z : ZMod p × ZMod p) : Prop := U1i (sx z) (sy z)
def U2 (z : ZMod p × ZMod p) : Prop := U2i (sx z) (sy z)

/-- The central "quarter square" `{|z₁| < p/4} × {|z₂| < p/4}`. -/
def Xg (z : ZMod p × ZMod p) : Prop :=
  4 * (z.1.valMinAbs).natAbs < p ∧ 4 * (z.2.valMinAbs).natAbs < p

/-- The four transvections. -/
def T1p (z : ZMod p × ZMod p) : ZMod p × ZMod p := (z.1 + z.2, z.2)
def T1m (z : ZMod p × ZMod p) : ZMod p × ZMod p := (z.1 - z.2, z.2)
def T2p (z : ZMod p × ZMod p) : ZMod p × ZMod p := (z.1, z.2 + z.1)
def T2m (z : ZMod p × ZMod p) : ZMod p × ZMod p := (z.1, z.2 - z.1)

/-! ## Integer geometry -/

lemma int_W1 {x y : ℤ} (h : U1i x y) : W1i (x + y) y := by unfold U1i W1i W2i at *; omega
lemma int_W2 {x y : ℤ} (h : U1i x y) : W2i x (y + x) := by unfold U1i W1i W2i at *; omega
lemma int_W4 {x y : ℤ} (h : U2i x y) : W4i (x - y) y := by unfold U2i W3i W4i at *; omega
lemma int_W3 {x y : ℤ} (h : U2i x y) : W3i x (y - x) := by unfold U2i W3i W4i at *; omega
lemma int_cover {x y : ℤ} (h : x ≠ 0 ∨ y ≠ 0) : U1i x y ∨ U2i x y := by
  unfold U1i U2i W1i W2i W3i W4i at *; omega
lemma int_disj12 {x y : ℤ} (h1 : W1i x y) (h2 : W2i x y) : False := by
  unfold W1i W2i at *; omega
lemma int_disj34 {x y : ℤ} (h1 : W3i x y) (h2 : W4i x y) : False := by
  unfold W3i W4i at *; omega

/-! ## Generic sum lemmas -/

lemma ssum_mono {α : Type*} [DecidableEq α] (m : α → ℝ) (hm : ∀ z, 0 ≤ m z)
    {B C : Finset α} (h : B ⊆ C) : ∑ z ∈ B, m z ≤ ∑ z ∈ C, m z :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => hm i)

lemma ssum_union_le {α : Type*} [DecidableEq α] (m : α → ℝ) (hm : ∀ z, 0 ≤ m z)
    (B C : Finset α) : ∑ z ∈ B ∪ C, m z ≤ ∑ z ∈ B, m z + ∑ z ∈ C, m z := by
  have h1 : B ∪ C = B ∪ (C \ B) := by
    ext z; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  rw [h1, Finset.sum_union Finset.disjoint_sdiff]
  exact add_le_add_right (ssum_mono m hm Finset.sdiff_subset) _

/-! ## Containment lemmas -/

lemma T1p_mem_W1 [NeZero p] (z : ZMod p × ZMod p) (hU : U1 z) (hX : Xg z) :
    W1 (T1p z) := by
  have hsum : (z.1 + z.2).valMinAbs = z.1.valMinAbs + z.2.valMinAbs := valMinAbs_add_nowrap z.1 z.2 hX.1 hX.2
  change W1i (sx (T1p z)) (sy (T1p z))
  have h1 : sx (T1p z) = sx z + sy z := by simp only [T1p, sx, sy]; exact hsum
  have h2 : sy (T1p z) = sy z := by simp only [T1p, sy]
  rw [h1, h2]
  exact int_W1 hU

lemma T2p_mem_W2 [NeZero p] (z : ZMod p × ZMod p) (hU : U1 z) (hX : Xg z) :
    W2 (T2p z) := by
  have hsum : (z.2 + z.1).valMinAbs = z.2.valMinAbs + z.1.valMinAbs := valMinAbs_add_nowrap z.2 z.1 hX.2 hX.1
  change W2i (sx (T2p z)) (sy (T2p z))
  have h1 : sx (T2p z) = sx z := by simp only [T2p, sx]
  have h2 : sy (T2p z) = sy z + sx z := by simp only [T2p, sx, sy]; exact hsum
  rw [h1, h2]
  exact int_W2 hU

lemma T1m_mem_W4 [NeZero p] (z : ZMod p × ZMod p) (hU : U2 z) (hX : Xg z) :
    W4 (T1m z) := by
  have hsub : (z.1 - z.2).valMinAbs = z.1.valMinAbs - z.2.valMinAbs := valMinAbs_sub_nowrap z.1 z.2 hX.1 hX.2
  change W4i (sx (T1m z)) (sy (T1m z))
  have h1 : sx (T1m z) = sx z - sy z := by simp only [T1m, sx, sy]; exact hsub
  have h2 : sy (T1m z) = sy z := by simp only [T1m, sy]
  rw [h1, h2]
  exact int_W4 hU

lemma T2m_mem_W3 [NeZero p] (z : ZMod p × ZMod p) (hU : U2 z) (hX : Xg z) :
    W3 (T2m z) := by
  have hsub : (z.2 - z.1).valMinAbs = z.2.valMinAbs - z.1.valMinAbs := valMinAbs_sub_nowrap z.2 z.1 hX.2 hX.1
  change W3i (sx (T2m z)) (sy (T2m z))
  have h1 : sx (T2m z) = sx z := by simp only [T2m, sx]
  have h2 : sy (T2m z) = sy z - sx z := by simp only [T2m, sx, sy]; exact hsub
  rw [h1, h2]
  exact int_W3 hU

/-! ## The theorem -/

theorem mgg_bowtie :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      ∀ (m : ZMod p × ZMod p → ℝ), (∀ z, 0 ≤ m z) → ∀ ε : ℝ, 0 ≤ ε →
        (∑ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p => p ≤ 4 * (ZMod.valMinAbs z.1).natAbs), m z) ≤ ε ^ 2 / 2 →
        (∑ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p => p ≤ 4 * (ZMod.valMinAbs z.2).natAbs), m z) ≤ ε ^ 2 / 2 →
        (∀ B : Finset (ZMod p × ZMod p),
          |(∑ z ∈ B.image (fun z => (z.1 + z.2, z.2)), m z) - ∑ z ∈ B, m z| ≤ 2 * ε * Real.sqrt (∑ z ∈ B, m z) + ε ^ 2) →
        (∀ B : Finset (ZMod p × ZMod p),
          |(∑ z ∈ B.image (fun z => (z.1 - z.2, z.2)), m z) - ∑ z ∈ B, m z| ≤ 2 * ε * Real.sqrt (∑ z ∈ B, m z) + ε ^ 2) →
        (∀ B : Finset (ZMod p × ZMod p),
          |(∑ z ∈ B.image (fun z => (z.1, z.2 + z.1)), m z) - ∑ z ∈ B, m z| ≤ 2 * ε * Real.sqrt (∑ z ∈ B, m z) + ε ^ 2) →
        (∀ B : Finset (ZMod p × ZMod p),
          |(∑ z ∈ B.image (fun z => (z.1, z.2 - z.1)), m z) - ∑ z ∈ B, m z| ≤ 2 * ε * Real.sqrt (∑ z ∈ B, m z) + ε ^ 2) →
        ∑ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p => z ≠ 0), m z ≤ C * ε ^ 2 := by
  refine ⟨2 * (2 + 2 * Real.sqrt 2) ^ 2, by positivity, ?_⟩
  intro p hpF hp2 m hm0 ε hε hBx hBy hT1p hT1m hT2p hT2m
  classical
  set U1s : Finset (ZMod p × ZMod p) := Finset.univ.filter (fun z => U1 z) with hU1s
  set U2s : Finset (ZMod p × ZMod p) := Finset.univ.filter (fun z => U2 z) with hU2s
  set W1s : Finset (ZMod p × ZMod p) := Finset.univ.filter (fun z => W1 z) with hW1s
  set W2s : Finset (ZMod p × ZMod p) := Finset.univ.filter (fun z => W2 z) with hW2s
  set W3s : Finset (ZMod p × ZMod p) := Finset.univ.filter (fun z => W3 z) with hW3s
  set W4s : Finset (ZMod p × ZMod p) := Finset.univ.filter (fun z => W4 z) with hW4s
  set Xs : Finset (ZMod p × ZMod p) := Finset.univ.filter (fun z => Xg z) with hXs
  set Bxset : Finset (ZMod p × ZMod p) :=
    Finset.univ.filter (fun z => p ≤ 4 * (ZMod.valMinAbs z.1).natAbs) with hBxset
  set Byset : Finset (ZMod p × ZMod p) :=
    Finset.univ.filter (fun z => p ≤ 4 * (ZMod.valMinAbs z.2).natAbs) with hByset
  have hBx' : ∑ z ∈ Bxset, m z ≤ ε ^ 2 / 2 := by rw [hBxset]; exact hBx
  have hBy' : ∑ z ∈ Byset, m z ≤ ε ^ 2 / 2 := by rw [hByset]; exact hBy
  -- coverage
  have hcover : Finset.univ.filter (fun z : ZMod p × ZMod p => z ≠ 0) ⊆ U1s ∪ U2s := by
    intro z hz
    rw [Finset.mem_filter] at hz
    have hz0 : z ≠ 0 := hz.2
    rw [hU1s, hU2s, Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    have hne : sx z ≠ 0 ∨ sy z ≠ 0 := by
      by_contra hc
      rw [not_or] at hc
      simp only [not_not] at hc
      exact hz0 (Prod.ext ((ZMod.valMinAbs_eq_zero z.1).mp hc.1)
        ((ZMod.valMinAbs_eq_zero z.2).mp hc.2))
    exact int_cover hne
  have h1μ : ∑ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p => z ≠ 0), m z
      ≤ ∑ z ∈ U1s ∪ U2s, m z := ssum_mono m hm0 hcover
  have h2μ : ∑ z ∈ U1s ∪ U2s, m z ≤ ∑ z ∈ U1s, m z + ∑ z ∈ U2s, m z :=
    ssum_union_le m hm0 U1s U2s
  -- U1 bound
  have hU1bd : ∑ z ∈ U1s, m z ≤ (2 + 2 * Real.sqrt 2) ^ 2 * ε ^ 2 := by
    set A1s : Finset (ZMod p × ZMod p) := Finset.univ.filter (fun z => U1 z ∧ Xg z) with hA1s
    have hU1split : U1s = W1s ∪ W2s := by
      rw [hU1s, hW1s, hW2s]
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      exact ⟨fun h => h, fun h => h⟩
    have hdisj12 : Disjoint W1s W2s := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      rw [hW1s, Finset.mem_filter] at hz1
      rw [hW2s, Finset.mem_filter] at hz2
      exact int_disj12 hz1.2 hz2.2
    have hA1eq : ∑ z ∈ U1s, m z = ∑ z ∈ W1s, m z + ∑ z ∈ W2s, m z := by
      rw [hU1split, Finset.sum_union hdisj12]
    have hA1sub : A1s ⊆ U1s := by
      intro z hz
      rw [hA1s, Finset.mem_filter] at hz
      rw [hU1s, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hz.2.1⟩
    have hA1le : ∑ z ∈ A1s, m z ≤ ∑ z ∈ U1s, m z := ssum_mono m hm0 hA1sub
    have hsub1 : A1s.image T1p ⊆ W1s := by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      rw [hA1s, Finset.mem_filter] at hw
      simp only [Finset.mem_univ, true_and] at hw
      rw [hW1s, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, T1p_mem_W1 w hw.1 hw.2⟩
    have hsub2 : A1s.image T2p ⊆ W2s := by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      rw [hA1s, Finset.mem_filter] at hw
      simp only [Finset.mem_univ, true_and] at hw
      rw [hW2s, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, T2p_mem_W2 w hw.1 hw.2⟩
    have himg1 : ∑ z ∈ A1s.image T1p, m z ≤ ∑ z ∈ W1s, m z := ssum_mono m hm0 hsub1
    have himg2 : ∑ z ∈ A1s.image T2p, m z ≤ ∑ z ∈ W2s, m z := ssum_mono m hm0 hsub2
    have hs1 : ∑ z ∈ A1s, m z - (2 * ε * Real.sqrt (∑ z ∈ A1s, m z) + ε ^ 2)
        ≤ ∑ z ∈ A1s.image T1p, m z := by
      have h' : |(∑ z ∈ A1s.image T1p, m z) - ∑ z ∈ A1s, m z|
          ≤ 2 * ε * Real.sqrt (∑ z ∈ A1s, m z) + ε ^ 2 := hT1p A1s
      have h2 := neg_abs_le ((∑ z ∈ A1s.image T1p, m z) - ∑ z ∈ A1s, m z)
      linarith
    have hs2 : ∑ z ∈ A1s, m z - (2 * ε * Real.sqrt (∑ z ∈ A1s, m z) + ε ^ 2)
        ≤ ∑ z ∈ A1s.image T2p, m z := by
      have h' : |(∑ z ∈ A1s.image T2p, m z) - ∑ z ∈ A1s, m z|
          ≤ 2 * ε * Real.sqrt (∑ z ∈ A1s, m z) + ε ^ 2 := hT2p A1s
      have h2 := neg_abs_le ((∑ z ∈ A1s.image T2p, m z) - ∑ z ∈ A1s, m z)
      linarith
    have hchain : 2 * (∑ z ∈ A1s, m z) - 4 * ε * Real.sqrt (∑ z ∈ A1s, m z) - 2 * ε ^ 2
        ≤ ∑ z ∈ U1s, m z := by linarith [hA1eq, himg1, himg2, hs1, hs2]
    have hsubX : U1s \ A1s ⊆ Bxset ∪ Byset := by
      intro z hz
      rw [Finset.mem_sdiff] at hz
      obtain ⟨hzU, hzA⟩ := hz
      rw [hU1s, Finset.mem_filter] at hzU
      rw [hA1s, Finset.mem_filter] at hzA
      simp only [Finset.mem_univ, true_and] at hzU hzA
      have hnotX : ¬ Xg z := fun hx => hzA ⟨hzU, hx⟩
      rw [hBxset, hByset, Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      unfold Xg at hnotX
      rcases lt_or_ge (4 * z.1.valMinAbs.natAbs) p with h1 | h1
      · rcases lt_or_ge (4 * z.2.valMinAbs.natAbs) p with h2 | h2
        · exact absurd ⟨h1, h2⟩ hnotX
        · exact Or.inr h2
      · exact Or.inl h1
    have hleX : ∑ z ∈ U1s \ A1s, m z ≤ ε ^ 2 := by
      have h1 : ∑ z ∈ U1s \ A1s, m z ≤ ∑ z ∈ Bxset ∪ Byset, m z := ssum_mono m hm0 hsubX
      have h2 : ∑ z ∈ Bxset ∪ Byset, m z ≤ ∑ z ∈ Bxset, m z + ∑ z ∈ Byset, m z :=
        ssum_union_le m hm0 Bxset Byset
      linarith [h1, h2, hBx', hBy']
    have hA1ge : ∑ z ∈ U1s, m z - ε ^ 2 ≤ ∑ z ∈ A1s, m z := by
      have := Finset.sum_sdiff hA1sub (f := m)
      linarith [this, hleX]
    have hμ1 : ∑ z ∈ U1s, m z ≤ 4 * ε * Real.sqrt (∑ z ∈ U1s, m z) + 4 * ε ^ 2 := by
      have hmul : 4 * ε * Real.sqrt (∑ z ∈ A1s, m z) ≤ 4 * ε * Real.sqrt (∑ z ∈ U1s, m z) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hA1le) (by linarith : (0:ℝ) ≤ 4 * ε)
      linarith [hchain, hA1ge, hmul, hε]
    have hnn : 0 ≤ ∑ z ∈ U1s, m z := Finset.sum_nonneg (fun z _ => hm0 z)
    exact bowtie_sqrt_bound _ _ hnn hε hμ1
  -- U2 bound
  have hU2bd : ∑ z ∈ U2s, m z ≤ (2 + 2 * Real.sqrt 2) ^ 2 * ε ^ 2 := by
    set A2s : Finset (ZMod p × ZMod p) := Finset.univ.filter (fun z => U2 z ∧ Xg z) with hA2s
    have hU2split : U2s = W3s ∪ W4s := by
      rw [hU2s, hW3s, hW4s]
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      exact ⟨fun h => h, fun h => h⟩
    have hdisj34 : Disjoint W3s W4s := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      rw [hW3s, Finset.mem_filter] at hz1
      rw [hW4s, Finset.mem_filter] at hz2
      exact int_disj34 hz1.2 hz2.2
    have hA2eq : ∑ z ∈ U2s, m z = ∑ z ∈ W3s, m z + ∑ z ∈ W4s, m z := by
      rw [hU2split, Finset.sum_union hdisj34]
    have hA2sub : A2s ⊆ U2s := by
      intro z hz
      rw [hA2s, Finset.mem_filter] at hz
      rw [hU2s, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hz.2.1⟩
    have hA2le : ∑ z ∈ A2s, m z ≤ ∑ z ∈ U2s, m z := ssum_mono m hm0 hA2sub
    have hsub4 : A2s.image T1m ⊆ W4s := by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      rw [hA2s, Finset.mem_filter] at hw
      simp only [Finset.mem_univ, true_and] at hw
      rw [hW4s, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, T1m_mem_W4 w hw.1 hw.2⟩
    have hsub3 : A2s.image T2m ⊆ W3s := by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      rw [hA2s, Finset.mem_filter] at hw
      simp only [Finset.mem_univ, true_and] at hw
      rw [hW3s, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, T2m_mem_W3 w hw.1 hw.2⟩
    have himg4 : ∑ z ∈ A2s.image T1m, m z ≤ ∑ z ∈ W4s, m z := ssum_mono m hm0 hsub4
    have himg3 : ∑ z ∈ A2s.image T2m, m z ≤ ∑ z ∈ W3s, m z := ssum_mono m hm0 hsub3
    have hs4 : ∑ z ∈ A2s, m z - (2 * ε * Real.sqrt (∑ z ∈ A2s, m z) + ε ^ 2)
        ≤ ∑ z ∈ A2s.image T1m, m z := by
      have h' : |(∑ z ∈ A2s.image T1m, m z) - ∑ z ∈ A2s, m z|
          ≤ 2 * ε * Real.sqrt (∑ z ∈ A2s, m z) + ε ^ 2 := hT1m A2s
      have h2 := neg_abs_le ((∑ z ∈ A2s.image T1m, m z) - ∑ z ∈ A2s, m z)
      linarith
    have hs3 : ∑ z ∈ A2s, m z - (2 * ε * Real.sqrt (∑ z ∈ A2s, m z) + ε ^ 2)
        ≤ ∑ z ∈ A2s.image T2m, m z := by
      have h' : |(∑ z ∈ A2s.image T2m, m z) - ∑ z ∈ A2s, m z|
          ≤ 2 * ε * Real.sqrt (∑ z ∈ A2s, m z) + ε ^ 2 := hT2m A2s
      have h2 := neg_abs_le ((∑ z ∈ A2s.image T2m, m z) - ∑ z ∈ A2s, m z)
      linarith
    have hchain2 : 2 * (∑ z ∈ A2s, m z) - 4 * ε * Real.sqrt (∑ z ∈ A2s, m z) - 2 * ε ^ 2
        ≤ ∑ z ∈ U2s, m z := by linarith [hA2eq, himg4, himg3, hs4, hs3]
    have hsubX2 : U2s \ A2s ⊆ Bxset ∪ Byset := by
      intro z hz
      rw [Finset.mem_sdiff] at hz
      obtain ⟨hzU, hzA⟩ := hz
      rw [hU2s, Finset.mem_filter] at hzU
      rw [hA2s, Finset.mem_filter] at hzA
      simp only [Finset.mem_univ, true_and] at hzU hzA
      have hnotX : ¬ Xg z := fun hx => hzA ⟨hzU, hx⟩
      rw [hBxset, hByset, Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      unfold Xg at hnotX
      rcases lt_or_ge (4 * z.1.valMinAbs.natAbs) p with h1 | h1
      · rcases lt_or_ge (4 * z.2.valMinAbs.natAbs) p with h2 | h2
        · exact absurd ⟨h1, h2⟩ hnotX
        · exact Or.inr h2
      · exact Or.inl h1
    have hleX2 : ∑ z ∈ U2s \ A2s, m z ≤ ε ^ 2 := by
      have h1 : ∑ z ∈ U2s \ A2s, m z ≤ ∑ z ∈ Bxset ∪ Byset, m z := ssum_mono m hm0 hsubX2
      have h2 : ∑ z ∈ Bxset ∪ Byset, m z ≤ ∑ z ∈ Bxset, m z + ∑ z ∈ Byset, m z :=
        ssum_union_le m hm0 Bxset Byset
      linarith [h1, h2, hBx', hBy']
    have hA2ge : ∑ z ∈ U2s, m z - ε ^ 2 ≤ ∑ z ∈ A2s, m z := by
      have := Finset.sum_sdiff hA2sub (f := m)
      linarith [this, hleX2]
    have hμ2 : ∑ z ∈ U2s, m z ≤ 4 * ε * Real.sqrt (∑ z ∈ U2s, m z) + 4 * ε ^ 2 := by
      have hmul : 4 * ε * Real.sqrt (∑ z ∈ A2s, m z) ≤ 4 * ε * Real.sqrt (∑ z ∈ U2s, m z) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hA2le) (by linarith : (0:ℝ) ≤ 4 * ε)
      linarith [hchain2, hA2ge, hmul, hε]
    have hnn : 0 ≤ ∑ z ∈ U2s, m z := Finset.sum_nonneg (fun z _ => hm0 z)
    exact bowtie_sqrt_bound _ _ hnn hε hμ2
  have hsum : ∑ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p => z ≠ 0), m z
      ≤ 2 * (2 + 2 * Real.sqrt 2) ^ 2 * ε ^ 2 := by
    linarith [h1μ, h2μ, hU1bd, hU2bd]
  exact hsum

end Work.LT
