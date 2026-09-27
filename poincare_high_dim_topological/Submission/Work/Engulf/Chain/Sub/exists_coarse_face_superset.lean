import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Chain.Sub.Basic

namespace Work.Engulf.Chain.Sub

open Set Metric

/-- A point of `simp s` lying in the relative interior of the face `s`: it avoids `simp t` for
every proper subface `t = s.erase v`. -/
theorem exists_relint_point {N : ℕ} {Γ₁ : PL.Cx N} {s : Finset (PL.E N)} (hs : s ∈ Γ₁.faces) :
    ∃ x : PL.E N, x ∈ PL.simp s ∧ ∀ v ∈ s, x ∉ PL.simp (s.erase v) := by
  classical
  have hne : s.Nonempty := Γ₁.nonempty_of_mem_faces hs
  have hcard : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hne
  have hpos_card : 0 < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  refine ⟨∑ v ∈ s, (s.card : ℝ)⁻¹ • v, ?_, ?_⟩
  · change _ ∈ convexHull ℝ (s : Set (PL.E N))
    rw [Finset.mem_convexHull']
    refine ⟨fun _ => (s.card : ℝ)⁻¹, fun y _ => inv_nonneg.mpr hpos_card.le, ?_, rfl⟩
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcard]
  · intro v hv hmem
    change _ ∈ convexHull ℝ ((s.erase v : Finset (PL.E N)) : Set (PL.E N)) at hmem
    rw [Finset.mem_convexHull'] at hmem
    obtain ⟨μ, hμnn, hμsum, hμx⟩ := hmem
    let μ' : PL.E N → ℝ := fun y => if y ∈ s.erase v then μ y else 0
    have h1 : ∑ y ∈ s, μ' y = ∑ y ∈ s.erase v, μ y := by
      rw [← Finset.sum_subset (Finset.erase_subset v s)
        (fun y _ hy' => by simp only [μ', if_neg hy'])]
      exact Finset.sum_congr rfl (fun y hy => by simp only [μ', if_pos hy])
    have h2 : ∑ y ∈ s, μ' y • y = ∑ y ∈ s.erase v, μ y • y := by
      rw [← Finset.sum_subset (Finset.erase_subset v s)
        (fun y _ hy' => by simp only [μ', if_neg hy', zero_smul])]
      exact Finset.sum_congr rfl (fun y hy => by simp only [μ', if_pos hy])
    have hsum' : ∑ y ∈ s, μ' y = 1 := by rw [h1, hμsum]
    have hsumx' : ∑ y ∈ s, μ' y • y = ∑ v ∈ s, (s.card : ℝ)⁻¹ • v := by rw [h2, hμx]
    have hw1sum : ∑ y ∈ s, (s.card : ℝ)⁻¹ = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcard]
    have hv_eq : (s.card : ℝ)⁻¹ = μ' v :=
      AffineIndependent.eq_of_sum_eq_sum_subtype (w₁ := fun _ => (s.card : ℝ)⁻¹) (w₂ := μ')
        (Γ₁.indep hs) (by rw [hw1sum, hsum']) (by rw [hsumx']) v hv
    have hμ'v : μ' v = 0 := by simp only [μ']; simp [Finset.mem_erase]
    rw [hμ'v] at hv_eq
    exact (inv_ne_zero hcard) hv_eq

/-- Carrier lemma for a subdivision: a point in the relative interior of `s`, with
`simp s ⊆ simp e`, cannot lie in `simp g` for `g ⊆ e` unless `simp s ⊆ simp g` already. -/
theorem simp_subset_of_mem_simp_of_positive_weights {N : ℕ} {e s g : Finset (PL.E N)}
    (he : AffineIndependent ℝ ((↑) : ↑e → PL.E N))
    (hse : PL.simp s ⊆ PL.simp e) {x : PL.E N} (hx : x ∈ PL.simp s)
    (hpos : ∀ v ∈ s, x ∉ PL.simp (s.erase v))
    (hg : g ⊆ e) (hxg : x ∈ PL.simp g) :
    PL.simp s ⊆ PL.simp g := by
  classical
  have hx' : x ∈ convexHull ℝ ((s : Finset (PL.E N)) : Set (PL.E N)) := hx
  rw [Finset.mem_convexHull'] at hx'
  obtain ⟨lam, hlamnn, hlamsum, hlamx⟩ := hx'
  have hlampos : ∀ v ∈ s, 0 < lam v := by
    intro v hv
    rcases lt_or_eq_of_le (hlamnn v hv) with hlt | heq
    · exact hlt
    · exfalso
      have heq' : lam v = 0 := heq.symm
      have hmem : x ∈ PL.simp (s.erase v) := by
        change x ∈ convexHull ℝ ((s.erase v : Finset (PL.E N)) : Set (PL.E N))
        rw [Finset.mem_convexHull']
        refine ⟨lam, fun y hy => hlamnn y (Finset.mem_of_mem_erase hy), ?_, ?_⟩
        · have h1 := Finset.sum_erase_add s lam hv
          rw [heq', add_zero, hlamsum] at h1
          exact h1
        · have h1 := Finset.sum_erase_add s (fun y => lam y • y) hv
          rw [heq', zero_smul, add_zero, hlamx] at h1
          exact h1
      exact hpos v hv hmem
  have hvmem : ∀ v ∈ s, v ∈ PL.simp e := fun v hv => hse (Work.Engulf.subset_simp hv)
  have hex : ∀ v : PL.E N, ∃ βv : PL.E N → ℝ,
      (v ∈ s → (∀ u ∈ e, 0 ≤ βv u) ∧ ∑ u ∈ e, βv u = 1 ∧ ∑ u ∈ e, βv u • u = v) := by
    intro v
    by_cases hv : v ∈ s
    · have hve : v ∈ convexHull ℝ ((e : Finset (PL.E N)) : Set (PL.E N)) := hvmem v hv
      rw [Finset.mem_convexHull'] at hve
      obtain ⟨βv, h1, h2, h3⟩ := hve
      exact ⟨βv, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hv⟩
  let β : PL.E N → PL.E N → ℝ := fun v => (hex v).choose
  have hβspec : ∀ v, v ∈ s →
      (∀ u ∈ e, 0 ≤ β v u) ∧ ∑ u ∈ e, β v u = 1 ∧ ∑ u ∈ e, β v u • u = v :=
    fun v => (hex v).choose_spec
  have hxg' : x ∈ convexHull ℝ ((g : Finset (PL.E N)) : Set (PL.E N)) := hxg
  rw [Finset.mem_convexHull'] at hxg'
  obtain ⟨γ, hγnn, hγsum, hγx⟩ := hxg'
  let W : PL.E N → ℝ := fun u => ∑ v ∈ s, lam v * β v u
  let γ' : PL.E N → ℝ := fun u => if u ∈ g then γ u else 0
  have hWsum : ∑ u ∈ e, W u = 1 := by
    calc ∑ u ∈ e, W u
        = ∑ u ∈ e, ∑ v ∈ s, lam v * β v u := by simp only [W]
      _ = ∑ v ∈ s, ∑ u ∈ e, lam v * β v u := Finset.sum_comm
      _ = ∑ v ∈ s, lam v * ∑ u ∈ e, β v u := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [Finset.mul_sum]
      _ = ∑ v ∈ s, lam v * 1 := by
            refine Finset.sum_congr rfl fun v hv => ?_
            rw [(hβspec v hv).2.1]
      _ = 1 := by simp_rw [mul_one]; exact hlamsum
  have hWx : ∑ u ∈ e, W u • u = x := by
    calc ∑ u ∈ e, W u • u
        = ∑ u ∈ e, ∑ v ∈ s, lam v • (β v u • u) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            simp only [W]
            rw [Finset.sum_smul]
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [mul_smul]
      _ = ∑ v ∈ s, ∑ u ∈ e, lam v • (β v u • u) := Finset.sum_comm
      _ = ∑ v ∈ s, lam v • ∑ u ∈ e, β v u • u := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [Finset.smul_sum]
      _ = ∑ v ∈ s, lam v • v := by
            refine Finset.sum_congr rfl fun v hv => ?_
            rw [(hβspec v hv).2.2]
      _ = x := hlamx
  have h1 : ∑ u ∈ e, γ' u = ∑ u ∈ g, γ u := by
    rw [← Finset.sum_subset hg (fun u _ hu => by simp only [γ', if_neg hu])]
    exact Finset.sum_congr rfl (fun u hu => by simp only [γ', if_pos hu])
  have h2 : ∑ u ∈ e, γ' u • u = ∑ u ∈ g, γ u • u := by
    rw [← Finset.sum_subset hg (fun u _ hu => by simp only [γ', if_neg hu, zero_smul])]
    exact Finset.sum_congr rfl (fun u hu => by simp only [γ', if_pos hu])
  have hγ'sum : ∑ u ∈ e, γ' u = 1 := by rw [h1, hγsum]
  have hγ'x : ∑ u ∈ e, γ' u • u = x := by rw [h2, hγx]
  have hWeq : ∀ u ∈ e, W u = γ' u :=
    AffineIndependent.eq_of_sum_eq_sum_subtype (w₁ := W) (w₂ := γ') he
      (by rw [hWsum, hγ'sum]) (by rw [hWx, hγ'x])
  have hvinG : ∀ v ∈ s, v ∈ PL.simp g := by
    intro v hv
    change v ∈ convexHull ℝ ((g : Finset (PL.E N)) : Set (PL.E N))
    rw [Finset.mem_convexHull']
    have hβz : ∀ u ∈ e, u ∉ g → β v u = 0 := by
      intro u hu hug
      have hWu : W u = 0 := by
        rw [hWeq u hu]
        simp only [γ', if_neg hug]
      have hle : lam v * β v u ≤ W u := by
        simp only [W]
        exact Finset.single_le_sum
          (fun v' hv' => mul_nonneg (hlampos v' hv').le ((hβspec v' hv').1 u hu)) hv
      rw [hWu] at hle
      have hnn : 0 ≤ lam v * β v u :=
        mul_nonneg (hlampos v hv).le ((hβspec v hv).1 u hu)
      exact (mul_eq_zero.mp (le_antisymm hle hnn)).resolve_left (ne_of_gt (hlampos v hv))
    refine ⟨β v, fun u hu => (hβspec v hv).1 u (hg hu), ?_, ?_⟩
    · rw [Finset.sum_subset hg (fun u hu hug => hβz u hu hug), (hβspec v hv).2.1]
    · rw [Finset.sum_subset hg (fun u hu hug => by rw [hβz u hu hug, zero_smul]),
        (hβspec v hv).2.2]
  change convexHull ℝ ((s : Finset (PL.E N)) : Set (PL.E N))
      ⊆ convexHull ℝ ((g : Finset (PL.E N)) : Set (PL.E N))
  exact convexHull_min (fun y hy => hvinG y (by simpa using hy)) (Work.Engulf.convex_simp g)

theorem exists_coarse_face_superset {N : ℕ} {Γ Γ₁ : PL.Cx N}
    (hsub : PL.Subdivides Γ₁ Γ) {L : Set (PL.E N)}
    (hL : Work.Engulf.IsSubSp Γ L) {s : Finset (PL.E N)}
    (hs : s ∈ Γ₁.faces) (h : PL.simp s ⊆ L) :
    ∃ e ∈ Γ.faces, PL.simp e ⊆ L ∧ PL.simp s ⊆ PL.simp e := by
  classical
  obtain ⟨_, hfaces⟩ := hsub
  obtain ⟨e₀, he₀, hse₀⟩ := hfaces s hs
  obtain ⟨x, hxs, hpos⟩ := exists_relint_point hs
  have hxL : x ∈ L := h hxs
  obtain ⟨f, hf, hxf, hfL⟩ := hL.2 x hxL
  have hxinter : x ∈ PL.simp (e₀ ∩ f) := by
    have hsi := Work.Engulf.simp_inter he₀ hf
    rw [← hsi]
    exact ⟨hse₀ hxs, hxf⟩
  have hgmem : e₀ ∩ f ∈ Γ.faces := by
    rcases Finset.eq_empty_or_nonempty (e₀ ∩ f) with hemp | hne
    · rw [hemp] at hxinter
      simpa using hxinter
    · exact Γ.down_closed he₀ Finset.inter_subset_left hne
  refine ⟨e₀ ∩ f, hgmem, ?_, ?_⟩
  · exact Subset.trans (Work.Engulf.simp_mono Finset.inter_subset_right) hfL
  · exact simp_subset_of_mem_simp_of_positive_weights (Γ.indep he₀) hse₀ hxs hpos
      Finset.inter_subset_left hxinter

end Work.Engulf.Chain.Sub
