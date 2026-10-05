import Mathlib

set_option autoImplicit false

/-!
# Global existence of integral curves

A locally Lipschitz vector field on a complete space which admits a *uniform* local existence time
has global integral curves.  The proof adapts the argument of
`Mathlib/Geometry/Manifold/IntegralCurve/UniformTime.lean` to the elementary ODE case.
-/

open scoped Topology NNReal
open Set Function

namespace Work.RPCore.Port.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : E → E} {L : NNReal} {γ γ' : ℝ → E}

local notation "V" => (fun (_ : ℝ) (z : E) => X z)

/-- Two integral curves of the same field on overlapping intervals which agree at a point of the
intersection agree on the whole intersection. -/
lemma eqOn_of_isIntegralCurveOn_Ioo (hLip : LipschitzWith L X)
    {a b a' b' : ℝ} (hγ : IsIntegralCurveOn γ V (Ioo a b))
    (hγ' : IsIntegralCurveOn γ' V (Ioo a' b'))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b ∩ Ioo a' b') (h : γ t₀ = γ' t₀) :
    EqOn γ γ' (Ioo (max a a') (min b b')) := by
  exact ODE_solution_unique_of_mem_Ioo (v := V) (s := fun _ => univ) (K := L)
    (f := γ) (g := γ') (a := max a a') (b := min b b') (t₀ := t₀)
    (fun _ _ => hLip.lipschitzOnWith)
    ⟨max_lt ht₀.1.1 ht₀.2.1, lt_min ht₀.1.2 ht₀.2.2⟩
    (fun s hs => by
      have hs' : s ∈ Ioo a b := Ioo_subset_Ioo (le_max_left ..) (min_le_left ..) hs
      exact ⟨(hγ s hs').hasDerivAt (Ioo_mem_nhds hs'.1 hs'.2), mem_univ _⟩)
    (fun s hs => by
      have hs' : s ∈ Ioo a' b' := Ioo_subset_Ioo (le_max_right ..) (min_le_right ..) hs
      exact ⟨(hγ' s hs').hasDerivAt (Ioo_mem_nhds hs'.1 hs'.2), mem_univ _⟩) h

/-- The `piecewise` extension of an integral curve agrees with the second curve on its domain. -/
lemma eqOn_piecewise_of_isIntegralCurveOn_Ioo (hLip : LipschitzWith L X)
    {a b a' b' : ℝ} (hγ : IsIntegralCurveOn γ V (Ioo a b))
    (hγ' : IsIntegralCurveOn γ' V (Ioo a' b'))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b ∩ Ioo a' b') (h : γ t₀ = γ' t₀) :
    EqOn (piecewise (Ioo a b) γ γ') γ' (Ioo a' b') := by
  intro t ht
  have H : EqOn γ γ' (Ioo (max a a') (min b b')) :=
    eqOn_of_isIntegralCurveOn_Ioo hLip hγ hγ' ht₀ h
  by_cases hmem : t ∈ Ioo a b
  · rw [piecewise, if_pos hmem]
    exact H ⟨max_lt hmem.1 ht.1, lt_min hmem.2 ht.2⟩
  · rw [piecewise, if_neg hmem]

/-- The extension of an integral curve by another integral curve is an integral curve. -/
lemma isIntegralCurveOn_piecewise (hLip : LipschitzWith L X) {a b a' b' : ℝ}
    (hγ : IsIntegralCurveOn γ V (Ioo a b)) (hγ' : IsIntegralCurveOn γ' V (Ioo a' b'))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b ∩ Ioo a' b') (h : γ t₀ = γ' t₀) :
    IsIntegralCurveOn (piecewise (Ioo a b) γ γ') V (Ioo a b ∪ Ioo a' b') := by
  intro t ht
  by_cases hmem : t ∈ Ioo a b
  · have hnb : Ioo a b ∈ 𝓝 t := Ioo_mem_nhds hmem.1 hmem.2
    have heq : piecewise (Ioo a b) γ γ' =ᶠ[𝓝 t] γ := by
      filter_upwards [hnb] with s hs using by rw [piecewise, if_pos hs]
    rw [show piecewise (Ioo a b) γ γ' t = γ t from by rw [piecewise, if_pos hmem]]
    exact (heq.hasDerivAt_iff.mpr ((hγ t hmem).hasDerivAt hnb)).hasDerivWithinAt
  · have ht' : t ∈ Ioo a' b' := by
      rcases ht with hh | hh
      · exact absurd hh hmem
      · exact hh
    have hnb : Ioo a' b' ∈ 𝓝 t := Ioo_mem_nhds ht'.1 ht'.2
    have heq : piecewise (Ioo a b) γ γ' =ᶠ[𝓝 t] γ' := by
      filter_upwards [hnb] with s hs using
        eqOn_piecewise_of_isIntegralCurveOn_Ioo hLip hγ hγ' ht₀ h hs
    rw [show piecewise (Ioo a b) γ γ' t = γ' t from
      eqOn_piecewise_of_isIntegralCurveOn_Ioo hLip hγ hγ' ht₀ h ht']
    exact (heq.hasDerivAt_iff.mpr ((hγ' t ht').hasDerivAt hnb)).hasDerivWithinAt

/-- Time translation of an integral curve. -/
lemma isIntegralCurveOn_comp_sub {a b c : ℝ} (hγ : IsIntegralCurveOn γ V (Ioo a b)) :
    IsIntegralCurveOn (fun t => γ (t - c)) V (Ioo (a + c) (b + c)) := by
  intro t ht
  have ht' : t - c ∈ Ioo a b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h1 : HasDerivAt γ (X (γ (t - c))) (t - c) :=
    (hγ (t - c) ht').hasDerivAt (Ioo_mem_nhds ht'.1 ht'.2)
  exact (HasDerivAt.comp_sub_const t c h1).hasDerivWithinAt

/-- **Right extension.**  If `γ` solves on `Ioo (-a) a` then it extends to a solution on
`Ioo (-a) (a + ε/2)`. -/
lemma exists_extend_right (hLip : LipschitzWith L X) {ε : ℝ} (hε : 0 < ε)
    (hloc : ∀ x : E, ∃ γ : ℝ → E, γ 0 = x ∧ IsIntegralCurveOn γ V (Ioo (-ε) ε))
    {a : ℝ} (ha : ε / 4 < a) {γ : ℝ → E} (hγ : IsIntegralCurveOn γ V (Ioo (-a) a)) :
    ∃ γ' : ℝ → E, γ' 0 = γ 0 ∧ IsIntegralCurveOn γ' V (Ioo (-a) (a + ε / 2)) := by
  have hza : a - ε / 2 ∈ Ioo (-a) a := ⟨by linarith, by linarith⟩
  obtain ⟨w, hw0, hw⟩ := hloc (γ (a - ε / 2))
  set γ₂ : ℝ → E := fun t => w (t - (a - ε / 2)) with hγ₂
  have hγ₂' : IsIntegralCurveOn γ₂ V (Ioo (a - 3 * ε / 2) (a + ε / 2)) := by
    have h := isIntegralCurveOn_comp_sub (c := a - ε / 2) hw
    have e1 : -ε + (a - ε / 2) = a - 3 * ε / 2 := by ring
    have e2 : ε + (a - ε / 2) = a + ε / 2 := by ring
    rwa [e1, e2] at h
  have hagree : γ (a - ε / 2) = γ₂ (a - ε / 2) := by
    simp [hγ₂, hw0]
  refine ⟨piecewise (Ioo (-a) a) γ γ₂, ?_, ?_⟩
  · rw [piecewise, if_pos (show (0:ℝ) ∈ Ioo (-a) a from ⟨by linarith, by linarith⟩)]
  · have hglue := isIntegralCurveOn_piecewise hLip hγ hγ₂'
      (t₀ := a - ε / 2) ⟨hza, ⟨by linarith, by linarith⟩⟩ hagree
    refine hglue.mono fun t ht => ?_
    rcases lt_or_ge t a with h | h
    · exact Or.inl ⟨ht.1, h⟩
    · exact Or.inr ⟨by linarith, ht.2⟩

/-- **Left extension.**  If `γ` solves on `Ioo (-a) b` with `b ≥ a` then it extends to a solution
on `Ioo (-(a + ε/2)) b`. -/
lemma exists_extend_left (hLip : LipschitzWith L X) {ε : ℝ} (hε : 0 < ε)
    (hloc : ∀ x : E, ∃ γ : ℝ → E, γ 0 = x ∧ IsIntegralCurveOn γ V (Ioo (-ε) ε))
    {a b : ℝ} (ha : ε / 4 < a) (hb : a ≤ b) {γ : ℝ → E}
    (hγ : IsIntegralCurveOn γ V (Ioo (-a) b)) :
    ∃ γ' : ℝ → E, γ' 0 = γ 0 ∧ IsIntegralCurveOn γ' V (Ioo (-(a + ε / 2)) b) := by
  have hza : -a + ε / 2 ∈ Ioo (-a) b := ⟨by linarith, by linarith⟩
  obtain ⟨w, hw0, hw⟩ := hloc (γ (-a + ε / 2))
  set γ₁ : ℝ → E := fun t => w (t + (a - ε / 2)) with hγ₁
  have hγ₁' : IsIntegralCurveOn γ₁ V (Ioo (-(a + ε / 2)) (-(a - 3 * ε / 2))) := by
    have h := isIntegralCurveOn_comp_sub (c := -(a - ε / 2)) hw
    simp only [sub_neg_eq_add] at h
    have e1 : -ε + -(a - ε / 2) = -(a + ε / 2) := by ring
    have e2 : ε + -(a - ε / 2) = -(a - 3 * ε / 2) := by ring
    rwa [e1, e2] at h
  have hagree : γ (-a + ε / 2) = γ₁ (-a + ε / 2) := by
    simp [hγ₁, hw0]
  refine ⟨piecewise (Ioo (-a) b) γ γ₁, ?_, ?_⟩
  · rw [piecewise, if_pos (show (0:ℝ) ∈ Ioo (-a) b from ⟨by linarith, by linarith⟩)]
  · have hglue := isIntegralCurveOn_piecewise hLip hγ hγ₁'
      (t₀ := -a + ε / 2) ⟨hza, ⟨by linarith, by linarith⟩⟩ hagree
    refine hglue.mono fun t ht => ?_
    rcases lt_or_ge (-a) t with h | h
    · exact Or.inl ⟨h, ht.2⟩
    · exact Or.inr ⟨ht.1, by linarith⟩

/-- Going from a solution on `Ioo (-a) a` to one on `Ioo (-(a + ε/2)) (a + ε/2)`. -/
lemma exists_extend_both (hLip : LipschitzWith L X) {ε : ℝ} (hε : 0 < ε)
    (hloc : ∀ x : E, ∃ γ : ℝ → E, γ 0 = x ∧ IsIntegralCurveOn γ V (Ioo (-ε) ε))
    {a : ℝ} (ha : ε / 4 < a) {γ : ℝ → E} (hγ : IsIntegralCurveOn γ V (Ioo (-a) a)) :
    ∃ γ' : ℝ → E, γ' 0 = γ 0 ∧
      IsIntegralCurveOn γ' V (Ioo (-(a + ε / 2)) (a + ε / 2)) := by
  obtain ⟨γ₁, h10, h1⟩ := exists_extend_right hLip hε hloc ha hγ
  obtain ⟨γ₂, h20, h2⟩ := exists_extend_left hLip hε hloc ha (by linarith) h1
  exact ⟨γ₂, by rw [h20, h10], h2⟩

/-- For every radius there is a solution through `y` on `Ioo (-a) a`. -/
lemma exists_isIntegralCurveOn_all_radii (hLip : LipschitzWith L X) {ε : ℝ} (hε : 0 < ε)
    (hloc : ∀ x : E, ∃ γ : ℝ → E, γ 0 = x ∧ IsIntegralCurveOn γ V (Ioo (-ε) ε)) (y : E) :
    ∀ a > 0, ∃ γ : ℝ → E, γ 0 = y ∧ IsIntegralCurveOn γ V (Ioo (-a) a) := by
  have key : ∀ n : ℕ, ∃ γ : ℝ → E, γ 0 = y ∧
      IsIntegralCurveOn γ V (Ioo (-(ε + n * (ε / 2))) (ε + n * (ε / 2))) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨γ₀, h0, hγ₀⟩ := hloc y
      exact ⟨γ₀, h0, hγ₀.mono (Ioo_subset_Ioo (by linarith) (by linarith))⟩
    | succ n ih =>
      obtain ⟨γ₁, h10, h1⟩ := ih
      have hnn : (0:ℝ) ≤ (n : ℝ) * (ε / 2) := by positivity
      have hpos : ε / 4 < ε + n * (ε / 2) := by linarith
      obtain ⟨γ₂, h20, h2⟩ := exists_extend_both hLip hε hloc hpos h1
      exact ⟨γ₂, h20.trans h10, by
        convert h2 using 1
        push_cast
        ring_nf⟩
  intro a ha
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a ≤ ε + n * (ε / 2) := by
    refine ⟨⌈a / (ε / 2)⌉₊ + 1, ?_⟩
    have h1 : a / (ε / 2) ≤ (⌈a / (ε / 2)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (0:ℝ) < ε / 2 := by linarith
    have : a ≤ (⌈a / (ε / 2)⌉₊ : ℝ) * (ε / 2) := by
      rw [div_le_iff₀ h2] at h1
      linarith
    have : (⌈a / (ε / 2)⌉₊ : ℝ) * (ε / 2) ≤ ε + (⌈a / (ε / 2)⌉₊ + 1 : ℕ) * (ε / 2) := by
      push_cast
      nlinarith
    linarith
  obtain ⟨γ, h0, hγ⟩ := key n
  exact ⟨γ, h0, hγ.mono (Ioo_subset_Ioo (by linarith) (by linarith))⟩

/-- For a fixed initial point, curves solving on the intervals of the family agree. -/
lemma eqOn_of_radius_le {γf : ℝ → ℝ → E} {y : E} (hLip : LipschitzWith L X)
    (hγf0 : ∀ a, γf a 0 = y) (hγf : ∀ a > 0, IsIntegralCurveOn (γf a) V (Ioo (-a) a))
    {a a' : ℝ} (hpos : 0 < a') (hle : a' ≤ a) :
    EqOn (γf a') (γf a) (Ioo (-a') a') := by
  have h0 : (0 : ℝ) ∈ Ioo (-a) a ∩ Ioo (-a') a' :=
    ⟨⟨by linarith, lt_of_lt_of_le hpos hle⟩, ⟨by linarith, hpos⟩⟩
  have h := eqOn_of_isIntegralCurveOn_Ioo hLip (hγf a (lt_of_lt_of_le hpos hle)) (hγf a' hpos)
    h0 (by rw [hγf0 a, hγf0 a'])
  intro t ht
  have h1 : max (-a) (-a') < t := max_lt (lt_of_le_of_lt (neg_le_neg hle) ht.1) ht.1
  have h2 : t < min a a' := lt_min (lt_of_lt_of_le ht.2 hle) ht.2
  exact (h ⟨h1, h2⟩).symm

/-- The diagonal curve agrees with each member of the family on the member's interval. -/
lemma eqOn_diagonal {γf : ℝ → ℝ → E} {y : E} (hLip : LipschitzWith L X)
    (hγf0 : ∀ a, γf a 0 = y) (hγf : ∀ a > 0, IsIntegralCurveOn (γf a) V (Ioo (-a) a))
    {a : ℝ} (ha : 0 < a) :
    EqOn (fun t => γf (|t| + 1) t) (γf a) (Ioo (-a) a) := by
  intro t ht
  by_cases hlt : |t| + 1 < a
  · exact eqOn_of_radius_le hLip hγf0 hγf (by positivity) hlt.le (abs_lt.mp (lt_add_one |t|))
  · exact (eqOn_of_radius_le hLip hγf0 hγf ha (le_of_not_gt hlt) ht).symm

theorem exists_isIntegralCurve_of_lipschitzWith {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (X : E → E) {L : NNReal} (hLip : LipschitzWith L X)
    {M : ℝ} (hM : ∀ z, ‖X z‖ ≤ M) (y : E) :
    ∃ γ : ℝ → E, γ 0 = y ∧ IsIntegralCurve γ (fun _ z => X z) := by
  obtain ⟨Mnn, hMnn⟩ : ∃ Mnn : NNReal, ∀ z, ‖X z‖₊ ≤ Mnn := by
    refine ⟨M.toNNReal, fun z => ?_⟩
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal M ((norm_nonneg (X 0)).trans (hM 0))]
    exact hM z
  set eps : ℝ := min 1 (1 / (2 * ((Mnn : ℝ) + 1))) with hepsdef
  have hepspos : 0 < eps := by
    rw [hepsdef]
    exact lt_min zero_lt_one (by positivity)
  have hPL : ∀ x : E, IsPicardLindelof (fun _ : ℝ => X) (tmin := -eps) (tmax := eps)
      ⟨0, by simp [le_of_lt hepspos]⟩ x 1 0 Mnn L := by
    intro x
    have hmax : max (eps - 0) (0 - -eps) = eps := by
      rw [sub_zero, sub_neg_eq_add, zero_add, max_self]
    refine IsPicardLindelof.of_time_independent (t₀ := ⟨0, by simp [le_of_lt hepspos]⟩)
      (fun z _ => hMnn z) (hLip.lipschitzOnWith) ?_
    rw [hmax]
    have hcast : (((1 : NNReal) : ℝ) - ((0 : NNReal) : ℝ)) = 1 := by norm_num
    rw [hcast]
    have hepsle : eps ≤ 1 / (2 * ((Mnn : ℝ) + 1)) := by
      rw [hepsdef]; exact min_le_right _ _
    have hfin : (Mnn : ℝ) * (1 / (2 * ((Mnn : ℝ) + 1))) ≤ 1 := by
      have h1 : (0:ℝ) < 2 * ((Mnn : ℝ) + 1) := by positivity
      rw [mul_one_div, div_le_iff₀ h1]
      nlinarith [show (0:ℝ) ≤ (Mnn : ℝ) by positivity]
    calc (Mnn : ℝ) * eps ≤ (Mnn : ℝ) * (1 / (2 * ((Mnn : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hepsle (by positivity : (0:ℝ) ≤ (Mnn : ℝ))
      _ ≤ 1 := hfin
  have hloc : ∀ x : E, ∃ γ : ℝ → E, γ 0 = x ∧ IsIntegralCurveOn γ (fun (_ : ℝ) (z : E) => X z) (Ioo (-eps) eps) := by
    intro x
    obtain ⟨α, hα0, hα⟩ := IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ (hPL x)
    refine ⟨α, hα0, fun t ht => ?_⟩
    exact ((hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt
  have hS := exists_isIntegralCurveOn_all_radii (X := X) hLip hepspos hloc y
  let γf : ℝ → ℝ → E := fun a => if h : 0 < a then Classical.choose (hS a h) else fun _ => y
  have hγf0 : ∀ a, γf a 0 = y := by
    intro a
    by_cases h : 0 < a
    · have h1 : γf a = Classical.choose (hS a h) := by
        show (if h' : 0 < a then Classical.choose (hS a h') else fun _ => y) = _
        rw [dif_pos h]
      rw [h1]
      exact (Classical.choose_spec (hS a h)).1
    · have h1 : γf a = fun _ => y := by
        show (if h' : 0 < a then Classical.choose (hS a h') else fun _ => y) = _
        rw [dif_neg h]
      rw [h1]
  have hγf : ∀ a > 0, IsIntegralCurveOn (γf a) (fun (_ : ℝ) (z : E) => X z) (Ioo (-a) a) := by
    intro a h
    have h1 : γf a = Classical.choose (hS a h) := by
      show (if h' : 0 < a then Classical.choose (hS a h') else fun _ => y) = _
      rw [dif_pos h]
    rw [h1]
    exact (Classical.choose_spec (hS a h)).2
  refine ⟨fun t => γf (|t| + 1) t, by simp [hγf0], ?_⟩
  intro t
  have hmem : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := by
    rw [mem_Ioo, ← abs_lt]; exact lt_add_one |t|
  have hnb : Ioo (-(|t| + 1)) (|t| + 1) ∈ 𝓝 t := Ioo_mem_nhds hmem.1 hmem.2
  have heq : (fun s => γf (|s| + 1) s) =ᶠ[𝓝 t] γf (|t| + 1) := by
    filter_upwards [hnb] with s hs using
      eqOn_diagonal hLip hγf0 hγf (by positivity) hs
  rw [heq.hasDerivAt_iff]
  exact (hγf (|t| + 1) (by positivity) t hmem).hasDerivAt hnb

end Work.RPCore.Port.ODE
