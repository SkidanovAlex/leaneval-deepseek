import Mathlib
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.ChainDefs
import Submission.Work.DeltaHomology.RealizationDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology Work.DeltaHomology
open scoped unitInterval

noncomputable section

/-!
# The barycentric collar of the boundary of the standard simplex

We build, for each `k`, an open neighbourhood `Uset k` of the boundary
`StdSimplexBoundary k` of the standard `k`-simplex — namely the complement of the
barycentre — together with the radial projection of `Uset k` away from the
barycentre, contracted back to the boundary in a way that fixes the boundary
pointwise.  The result is packaged in `collarMap k` and used to prove
`exists_collar_deformationRetract`.

Concretely, with `c = 1/(k+1)` the barycentric coordinate of the barycentre and
`M w = max_i max (c - w_i) 0`, the map
`H t w = c + (1 - t + t * c/M w) * (w - c)`
(grouped weightwise) is the required homotopy: at `t = 0` it fixes `w`, at
`t = 1` it lands on the boundary (at a coordinate where `M w` is attained), and
for `w` on the boundary `M w = c`, so it is the constant homotopy.
-/

/-- The barycentric coordinate of the barycentre of `Δ^k`. -/
private def c (k : ℕ) : ℝ := ((k : ℝ) + 1)⁻¹

private lemma c_pos (k : ℕ) : 0 < c k := by rw [c]; positivity

private lemma c_ne_zero (k : ℕ) : c k ≠ 0 := ne_of_gt (c_pos k)

private lemma sum_c (k : ℕ) : ∑ _ : Fin (k + 1), c k = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, c]
  field_simp

/-- The signed distance `max (c - w_i) 0` from the `i`-th coordinate of `w` to the
barycentric coordinate. -/
private def bdist (k : ℕ) (w : StdSimplex ℝ (Fin (k + 1))) (i : Fin (k + 1)) : ℝ :=
  max (c k - w.weights i) 0

private lemma bdist_nonneg (k : ℕ) (w : StdSimplex ℝ (Fin (k + 1))) (i : Fin (k + 1)) :
    0 ≤ bdist k w i := le_max_right _ _

private lemma bdist_le_c (k : ℕ) (w : StdSimplex ℝ (Fin (k + 1))) (i : Fin (k + 1)) :
    bdist k w i ≤ c k :=
  max_le (by linarith [w.weights_nonneg i]) (le_of_lt (c_pos k))

/-- `M w = max_i max (c - w_i) 0`, the radius (in barycentric units) of the point
where the ray from the barycentre through `w` first meets the boundary. -/
private def Mfun (k : ℕ) (w : StdSimplex ℝ (Fin (k + 1))) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => bdist k w i)

private lemma le_Mfun (k : ℕ) (w : StdSimplex ℝ (Fin (k + 1))) (i : Fin (k + 1)) :
    bdist k w i ≤ Mfun k w :=
  Finset.le_sup' _ (Finset.mem_univ i)

private lemma Mfun_nonneg (k : ℕ) (w : StdSimplex ℝ (Fin (k + 1))) : 0 ≤ Mfun k w :=
  le_trans (bdist_nonneg k w 0) (le_Mfun k w 0)

private lemma Mfun_le_c (k : ℕ) (w : StdSimplex ℝ (Fin (k + 1))) : Mfun k w ≤ c k :=
  Finset.sup'_le _ _ (fun i _ => bdist_le_c k w i)

/-- The complement of the barycentre, described by a coordinate different from the
barycentric coordinate. -/
private def Uset (k : ℕ) : Set (StdSimplex ℝ (Fin (k + 1))) :=
  {w | ∃ i, w.weights i ≠ c k}

private lemma isOpen_Uset (k : ℕ) : IsOpen (Uset k) := by
  have h : Uset k
      = ⋃ i, {w : StdSimplex ℝ (Fin (k + 1)) | w.weights i ≠ c k} := by
    ext w; simp [Uset]
  rw [h]
  exact isOpen_iUnion (fun i =>
    (StdSimplex.continuous_weights_apply ℝ i).isOpen_preimage {x : ℝ | x ≠ c k} isOpen_ne)

private lemma boundary_subset_Uset (k : ℕ) : StdSimplexBoundary k ⊆ Uset k := by
  intro w hw
  obtain ⟨i, hi⟩ := hw
  exact ⟨i, by rw [hi]; exact ne_of_lt (c_pos k)⟩

private lemma Mfun_pos_of_mem (k : ℕ) {w : StdSimplex ℝ (Fin (k + 1))} (hw : w ∈ Uset k) :
    0 < Mfun k w := by
  obtain ⟨j, hj⟩ : ∃ j, w.weights j < c k := by
    by_contra h
    simp only [not_exists, not_lt] at h
    obtain ⟨i, hi⟩ := hw
    have hlt : c k < w.weights i := lt_of_le_of_ne (h i) (Ne.symm hi)
    have hsum := Finset.sum_lt_sum (fun j _ => h j) ⟨i, Finset.mem_univ i, hlt⟩
    rw [sum_c, w.total_of_fintype] at hsum
    exact lt_irrefl 1 hsum
  have hbd : 0 < bdist k w j := by
    rw [bdist, max_eq_left (by linarith)]
    linarith
  exact lt_of_lt_of_le hbd (le_Mfun k w j)

private lemma Mfun_eq_c_of_boundary (k : ℕ) {w : StdSimplex ℝ (Fin (k + 1))}
    (hw : w ∈ StdSimplexBoundary k) : Mfun k w = c k := by
  obtain ⟨i, hi⟩ := hw
  refine le_antisymm (Mfun_le_c k w) ?_
  have h := le_Mfun k w i
  rw [bdist, hi, sub_zero, max_eq_left (le_of_lt (c_pos k))] at h
  exact h

/-- The scaling factor of the projection: the parameter where the ray from the
barycentre through `w` reaches the boundary. -/
private def sfun (k : ℕ) (w : StdSimplex ℝ (Fin (k + 1))) : ℝ := c k / Mfun k w

/-- The interpolation parameter of the homotopy. -/
private def alpha (k : ℕ) (t : ℝ) (w : StdSimplex ℝ (Fin (k + 1))) : ℝ :=
  (1 - t) + t * sfun k w

/-- The weight function of the homotopy. -/
private def Hfun (k : ℕ) (t : ℝ) (w : StdSimplex ℝ (Fin (k + 1))) (i : Fin (k + 1)) : ℝ :=
  c k + alpha k t w * (w.weights i - c k)

private lemma one_le_sfun (k : ℕ) {w : StdSimplex ℝ (Fin (k + 1))} (hw : w ∈ Uset k) :
    1 ≤ sfun k w := by
  have hM0 : 0 < Mfun k w := Mfun_pos_of_mem k hw
  rw [sfun, one_le_div hM0]
  exact Mfun_le_c k w

private lemma sfun_mul_Mfun (k : ℕ) {w : StdSimplex ℝ (Fin (k + 1))} (hw : w ∈ Uset k) :
    sfun k w * Mfun k w = c k := by
  have hM0 : Mfun k w ≠ 0 := ne_of_gt (Mfun_pos_of_mem k hw)
  rw [sfun, div_mul_cancel₀ _ hM0]

private lemma alpha_ge_one (k : ℕ) {w : StdSimplex ℝ (Fin (k + 1))} (hw : w ∈ Uset k) (t : I) :
    1 ≤ alpha k t w := by
  have h1 := one_le_sfun k hw
  have ht : 0 ≤ (t : ℝ) := t.2.1
  have hprod : 0 ≤ (t : ℝ) * (sfun k w - 1) := mul_nonneg ht (by linarith)
  have heq : alpha k t w - 1 = (t : ℝ) * (sfun k w - 1) := by simp only [alpha]; ring
  linarith

private lemma alpha_le_sfun (k : ℕ) {w : StdSimplex ℝ (Fin (k + 1))} (hw : w ∈ Uset k) (t : I) :
    alpha k t w ≤ sfun k w := by
  have h1 := one_le_sfun k hw
  have ht : (t : ℝ) ≤ 1 := t.2.2
  have hprod : 0 ≤ (1 - (t : ℝ)) * (sfun k w - 1) := mul_nonneg (by linarith) (by linarith)
  have heq : sfun k w - alpha k t w = (1 - (t : ℝ)) * (sfun k w - 1) := by
    simp only [alpha]; ring
  linarith

private lemma alpha_pos (k : ℕ) {w : StdSimplex ℝ (Fin (k + 1))} (hw : w ∈ Uset k) (t : I) :
    0 < alpha k t w :=
  lt_of_lt_of_le zero_lt_one (alpha_ge_one k hw t)

private lemma alpha_zero (k : ℕ) (w : StdSimplex ℝ (Fin (k + 1))) :
    alpha k (0 : ℝ) w = 1 := by simp only [alpha]; ring

private lemma alpha_one (k : ℕ) (w : StdSimplex ℝ (Fin (k + 1))) :
    alpha k (1 : ℝ) w = sfun k w := by simp only [alpha]; ring

private lemma alpha_eq_one_of_boundary (k : ℕ) {w : StdSimplex ℝ (Fin (k + 1))}
    (hw : w ∈ StdSimplexBoundary k) (t : I) : alpha k t w = 1 := by
  rw [alpha, sfun, Mfun_eq_c_of_boundary k hw, div_self (c_ne_zero k)]
  ring

private lemma Hfun_nonneg (k : ℕ) {w : StdSimplex ℝ (Fin (k + 1))} (hw : w ∈ Uset k) (t : I)
    (i : Fin (k + 1)) : 0 ≤ Hfun k t w i := by
  have hM0 : 0 < Mfun k w := Mfun_pos_of_mem k hw
  have hα0 : 0 ≤ alpha k t w := le_of_lt (alpha_pos k hw t)
  have hαs : alpha k t w ≤ sfun k w := alpha_le_sfun k hw t
  have h1 : c k - w.weights i ≤ Mfun k w := le_trans (le_max_left _ _) (le_Mfun k w i)
  have h2 : alpha k t w * (c k - w.weights i) ≤ c k := by
    have h3 : alpha k t w * (c k - w.weights i) ≤ alpha k t w * Mfun k w :=
      mul_le_mul_of_nonneg_left h1 hα0
    have h4 : alpha k t w * Mfun k w ≤ sfun k w * Mfun k w :=
      mul_le_mul_of_nonneg_right hαs (le_of_lt hM0)
    rw [sfun_mul_Mfun k hw] at h4
    linarith
  have heq : Hfun k t w i = c k - alpha k t w * (c k - w.weights i) := by
    simp only [Hfun]; ring
  rw [heq]; linarith

private lemma Hfun_sum (k : ℕ) (w : StdSimplex ℝ (Fin (k + 1))) (t : I) :
    ∑ i, Hfun k t w i = 1 := by
  simp only [Hfun]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    w.total_of_fintype, sum_c]
  ring

private lemma Hfun_zero (k : ℕ) (w : StdSimplex ℝ (Fin (k + 1))) (i : Fin (k + 1)) :
    Hfun k ((0 : I) : ℝ) w i = w.weights i := by
  have h : ((0 : I) : ℝ) = 0 := rfl
  simp only [Hfun, alpha, h]
  ring

/-- At `t = 1` the homotopy lands on the boundary, at a coordinate where `Mfun` is
attained. -/
private lemma Hfun_one_boundary (k : ℕ) {w : StdSimplex ℝ (Fin (k + 1))} (hw : w ∈ Uset k) :
    ∃ i, Hfun k ((1 : I) : ℝ) w i = 0 := by
  obtain ⟨i0, _, hi0⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => bdist k w i)
  have hM0 : 0 < Mfun k w := Mfun_pos_of_mem k hw
  have hbd : bdist k w i0 = Mfun k w := hi0.symm
  have ha : 0 < c k - w.weights i0 := by
    have hpos : 0 < bdist k w i0 := by rw [hbd]; exact hM0
    rcases lt_max_iff.mp hpos with h | h
    · exact h
    · exact absurd h (lt_irrefl 0)
  have hcw : c k - w.weights i0 = Mfun k w := by
    have h1 : bdist k w i0 = c k - w.weights i0 := by rw [bdist, max_eq_left (le_of_lt ha)]
    rw [← h1, hbd]
  refine ⟨i0, ?_⟩
  have hwc : w.weights i0 - c k = -Mfun k w := by linarith
  have h1 : ((1 : I) : ℝ) = 1 := rfl
  have hMne : Mfun k w ≠ 0 := ne_of_gt hM0
  rw [Hfun, h1, alpha_one, hwc, sfun]
  field_simp
  ring

private lemma Hfun_boundary (k : ℕ) {w : StdSimplex ℝ (Fin (k + 1))}
    (hw : w ∈ StdSimplexBoundary k) (t : I) (i : Fin (k + 1)) :
    Hfun k t w i = w.weights i := by
  rw [Hfun, alpha_eq_one_of_boundary k hw t]
  ring

/-! ### Building the collar map -/

/-- The weights of the homotopy form a point of the simplex. -/
private def hpt (k : ℕ) (p : I × ↥(Uset k)) : StdSimplex ℝ (Fin (k + 1)) :=
  { weights := Finsupp.equivFunOnFinite.symm (Hfun k (p.1 : ℝ) p.2.val)
    nonneg := by
      rw [Finsupp.le_def]
      intro i
      rw [Finsupp.coe_zero, Pi.zero_apply, Finsupp.equivFunOnFinite_symm_apply_apply]
      exact Hfun_nonneg k p.2.property p.1 i
    total := by
      rw [Finsupp.sum_fintype]
      · simpa using Hfun_sum k p.2.val p.1
      · intro i; rfl }

private lemma hpt_weights (k : ℕ) (p : I × ↥(Uset k)) (i : Fin (k + 1)) :
    (hpt k p).weights i = Hfun k (p.1 : ℝ) p.2.val i :=
  Finsupp.equivFunOnFinite_symm_apply_apply _ i

private lemma hpt_mem (k : ℕ) (p : I × ↥(Uset k)) : hpt k p ∈ Uset k := by
  obtain ⟨i, hi⟩ := p.2.property
  refine ⟨i, ?_⟩
  intro h
  rw [hpt_weights, Hfun] at h
  exact mul_ne_zero (ne_of_gt (alpha_pos k p.2.property p.1)) (sub_ne_zero.mpr hi) (by linarith)

private lemma hpt_continuous (k : ℕ) :
    Continuous (fun p : I × ↥(Uset k) =>
      (⟨hpt k p, hpt_mem k p⟩ : ↥(Uset k))) := by
  apply Continuous.subtype_mk
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (k + 1))).continuous_iff]
  rw [continuous_pi_iff]
  intro i
  change Continuous (fun p : I × ↥(Uset k) => (hpt k p).weights i)
  rw [show (fun p : I × ↥(Uset k) => (hpt k p).weights i)
        = fun p : I × ↥(Uset k) => Hfun k (p.1 : ℝ) p.2.val i from
      funext fun p => hpt_weights k p i]
  have hfst : Continuous (fun p : I × ↥(Uset k) => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hMcont : Continuous (fun w : StdSimplex ℝ (Fin (k + 1)) => Mfun k w) := by
    simp only [Mfun, bdist]
    exact Continuous.finset_sup'_apply _ (fun i _ =>
      (continuous_const.sub (StdSimplex.continuous_weights_apply ℝ i)).max continuous_const)
  have hM : Continuous (fun p : I × ↥(Uset k) => Mfun k p.2.val) :=
    hMcont.comp (continuous_subtype_val.comp continuous_snd)
  have hs : Continuous (fun p : I × ↥(Uset k) => c k / Mfun k p.2.val) :=
    continuous_const.div hM (fun p => ne_of_gt (Mfun_pos_of_mem k p.2.property))
  have hα : Continuous (fun p : I × ↥(Uset k) => alpha k (p.1 : ℝ) p.2.val) := by
    simp only [alpha]
    exact (continuous_const.sub hfst).add (hfst.mul hs)
  have hw : Continuous (fun p : I × ↥(Uset k) => p.2.val.weights i) :=
    (StdSimplex.continuous_weights_apply ℝ i).comp (continuous_subtype_val.comp continuous_snd)
  simp only [Hfun]
  exact continuous_const.add (hα.mul (hw.sub continuous_const))

/-- The radial projection of `Uset k` (the simplex minus its barycentre) onto the
boundary, contracted back to the boundary. -/
private def collarMap (k : ℕ) : C(I × ↥(Uset k), ↥(Uset k)) where
  toFun p := ⟨hpt k p, hpt_mem k p⟩
  continuous_toFun := hpt_continuous k

private lemma collarMap_apply (k : ℕ) (p : I × ↥(Uset k)) :
    collarMap k p = ⟨hpt k p, hpt_mem k p⟩ := rfl

private lemma hpt_coe (k : ℕ) (p : I × ↥(Uset k)) :
    ((⟨hpt k p, hpt_mem k p⟩ : ↥(Uset k)) : StdSimplex ℝ (Fin (k + 1))) = hpt k p := rfl

theorem exists_collar_deformationRetract (k : ℕ) :
    ∃ U : Set (StdSimplex ℝ (Fin (k + 1))),
      IsOpen U ∧ StdSimplexBoundary k ⊆ U ∧
      ∃ H : C(I × ↥U, ↥U),
        (∀ u : ↥U, H (0, u) = u) ∧
        (∀ u : ↥U, ((H (1, u) : ↥U) : StdSimplex ℝ (Fin (k + 1))) ∈ StdSimplexBoundary k) ∧
        (∀ u : ↥U, (u : StdSimplex ℝ (Fin (k + 1))) ∈ StdSimplexBoundary k →
          ∀ t : I, H (t, u) = u) := by
  refine ⟨Uset k, isOpen_Uset k, boundary_subset_Uset k, collarMap k, ?_, ?_, ?_⟩
  · intro u
    apply Subtype.ext
    rw [collarMap_apply, hpt_coe]
    apply StdSimplex.ext
    apply Finsupp.ext
    intro i
    rw [hpt_weights]
    exact Hfun_zero k u.val i
  · intro u
    obtain ⟨i, hi⟩ := Hfun_one_boundary k u.property
    exact ⟨i, by rw [collarMap_apply, hpt_coe, hpt_weights]; exact hi⟩
  · intro u hu t
    apply Subtype.ext
    rw [collarMap_apply, hpt_coe]
    apply StdSimplex.ext
    apply Finsupp.ext
    intro i
    rw [hpt_weights]
    exact Hfun_boundary k hu t i

end

end Work.DeltaHomology
