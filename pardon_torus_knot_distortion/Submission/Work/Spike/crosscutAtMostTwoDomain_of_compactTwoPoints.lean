import Mathlib
import Submission.Work.Spike.slitPreconnectedAux
import Submission.Work.Spike.janiszewski_pointInter
import Submission.Work.Spike.spikeAux

/-!
# The crosscut theorem from the compact two-point Janiszewski theorem

The target `Work.Spike.crosscutAtMostTwoDomain_of_compactTwoPoints` derives the classical
*crosscut theorem for a plane domain*

> if `D ⊆ ℂ` is open and preconnected and `γ : [0,1] → ℂ` is injective with `γ 0, γ 1 ∉ D` and
> `γ t ∈ D` for `t ∈ (0,1)`, then `D \ range γ` has at most two connected components

from the **compact** two-point Janiszewski theorem `h2p` (of any two compact `A, B ⊆ ℂ` with
preconnected complements and `A ∩ B = {p,q}`, `p ≠ q`, the complement of `A ∪ B` has at most two
connected components).

## Why an inversion is needed

The pair `(Dᶜ, range γ)` realizes the crosscut situation but `Dᶜ` need not be compact (e.g. for a
bounded `D`), so `h2p` cannot be applied to it directly.  Choosing a point `c ∈ D` outside the arc
and inverting in `c` (`Psi c w = (w-c)⁻¹`, `PsiInv c v = c + v⁻¹`) replaces `D` by

  `invDomain c D = {v | v ≠ 0 ∧ PsiInv c v ∈ D} = Psi c '' (D \ {c})`,

whose complement **is** compact, while `γ` goes to `γ' = Psi c ∘ γ`.  Then `h2p` applies to
`(invDomain c D)ᶜ` and `Set.range γ'`, whose intersection is `{γ' 0, γ' 1}`, and preconnectedness of
both complements is available (`slitAux_diff_point` and `isPreconnected_compl_range_arc`).
Finally the conclusion is transported back from `invDomain c D \ range γ'` to `D \ range γ`
along the continuous inverse `PsiInv c` (`connectedComponentIn_eq_of_inversion`).
-/

namespace Work.Spike

open Set Metric

noncomputable section

/-- The **inverted domain**: the image of `D \ {c}` under `w ↦ (w - c)⁻¹`. -/
def invDomain (c : ℂ) (D : Set ℂ) : Set ℂ := {v : ℂ | v ≠ 0 ∧ PsiInv c v ∈ D}

@[simp] theorem mem_invDomain {c v : ℂ} {D : Set ℂ} :
    v ∈ invDomain c D ↔ v ≠ 0 ∧ PsiInv c v ∈ D := Iff.rfl

/-- A point of `D` different from `c`, outside the arc, exists: `D` is open and nonempty, while
`range γ ∪ F` has empty interior for a finite `F`. -/
theorem exists_mem_notMem_range_finite {D : Set ℂ} (hDopen : IsOpen D) (hDne : D.Nonempty)
    {γ : C(Set.Icc (0 : ℝ) 1, ℂ)} (hγ : Function.Injective γ) {F : Set ℂ} (hF : F.Finite) :
    ∃ c : ℂ, c ∈ D ∧ c ∉ Set.range γ ∧ c ∉ F := by
  obtain ⟨a, ha⟩ := hDne
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hDopen a ha
  -- a ball is infinite: it contains the injective image of the open interval `(0, ε)`
  have hball_inf : (Metric.ball a ε).Infinite := by
    have hinj : Set.InjOn (fun t : ℝ => a + (t : ℂ)) (Set.Ioo (0 : ℝ) ε) :=
      fun s _ t _ hst => Complex.ofReal_injective (add_left_cancel hst)
    have himg : ((fun t : ℝ => a + (t : ℂ)) '' Set.Ioo (0 : ℝ) ε).Infinite :=
      Set.Infinite.image hinj (Set.Ioo_infinite hε)
    refine himg.mono ?_
    rintro z ⟨t, ht, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht.1]
    exact ht.2
  have hne : (Metric.ball a ε \ F).Nonempty := (hball_inf.sdiff hF).nonempty
  by_contra hcon
  have hsub : Metric.ball a ε \ F ⊆ Set.range γ := by
    intro z hz
    by_contra hzγ
    exact hcon ⟨z, hεD hz.1, hzγ, hz.2⟩
  have hopen : IsOpen (Metric.ball a ε \ F) := Metric.isOpen_ball.sdiff hF.isClosed
  have hsub' : Metric.ball a ε \ F ⊆ interior (Set.range γ) := interior_maximal hsub hopen
  rw [interior_range_empty_of_injective hγ] at hsub'
  obtain ⟨z, hz⟩ := hne
  exact hsub' hz

theorem invDomain_isOpen {D : Set ℂ} {c : ℂ} (hDopen : IsOpen D) : IsOpen (invDomain c D) := by
  have heq : invDomain c D = ({0}ᶜ : Set ℂ) ∩ PsiInv c ⁻¹' D := by
    ext v
    simp only [mem_invDomain, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_preimage]
  rw [heq]
  exact (continuousOn_PsiInv c).isOpen_inter_preimage isClosed_singleton.isOpen_compl hDopen

theorem invDomain_preconnected {D : Set ℂ} (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    {c : ℂ} (hc : c ∈ D) : IsPreconnected (invDomain c D) := by
  have hSeq : invDomain c D = Psi c '' (D \ {c}) := by
    ext v
    constructor
    · intro hv
      rw [mem_invDomain] at hv
      exact ⟨PsiInv c v, ⟨hv.2, fun hwc => hv.1 (by rw [← Psi_PsiInv c v, hwc, Psi_zero])⟩,
        Psi_PsiInv c v⟩
    · rintro ⟨w, ⟨hwD, hwc⟩, rfl⟩
      rw [mem_invDomain]
      exact ⟨fun h0 => hwc (sub_eq_zero.mp (inv_eq_zero.mp h0)),
        by rw [PsiInv_Psi]; exact hwD⟩
  rw [hSeq]
  exact (slitAux_diff_point hDopen hDconn hc).image _ ((continuousOn_Psi c).mono fun w hw => by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hw.2)

theorem invDomain_compact_compl {D : Set ℂ} (hDopen : IsOpen D) {c : ℂ} (hc : c ∈ D) :
    IsCompact (invDomain c D)ᶜ := by
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hDopen c hc
  have hbdd : Bornology.IsBounded (invDomain c D)ᶜ := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
    refine ⟨ε⁻¹, fun w hw => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hle
    rw [not_le] at hle
    apply hw
    have hw0 : w ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hle
      exact not_lt_of_ge (inv_nonneg.mpr hε.le) hle
    rw [mem_invDomain]
    refine ⟨hw0, ?_⟩
    have hnorm : ‖w⁻¹‖ < ε := by
      rw [norm_inv]
      exact (inv_lt_comm₀ hε (norm_pos_iff.mpr hw0)).mp hle
    have : c + w⁻¹ ∈ Metric.ball c ε := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hnorm
    exact hεD this
  exact Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨(invDomain_isOpen hDopen).isClosed_compl, hbdd⟩

/-- **Transport of components through the inversion.**  If two points `u, v ∈ D \ range γ`
(different from the inversion centre `c`) have the same component in
`invDomain c D \ Psi c '' range γ`, they have the same component in `D \ range γ`. -/
theorem connectedComponentIn_eq_of_inversion {D : Set ℂ} {c : ℂ}
    {γ : C(Set.Icc (0 : ℝ) 1, ℂ)} {u v : ℂ}
    (hu : u ∈ D \ Set.range γ) (hv : v ∈ D \ Set.range γ) (huc : u ≠ c) (hvc : v ≠ c)
    (h : connectedComponentIn (invDomain c D \ (Psi c '' Set.range γ)) (Psi c u) =
      connectedComponentIn (invDomain c D \ (Psi c '' Set.range γ)) (Psi c v)) :
    connectedComponentIn (D \ Set.range γ) u = connectedComponentIn (D \ Set.range γ) v := by
  set Y : Set ℂ := invDomain c D \ (Psi c '' Set.range γ) with hY
  set X : Set ℂ := D \ Set.range γ with hX
  have hYsub : Y ⊆ ({0}ᶜ : Set ℂ) := by
    intro w hw
    rw [hY, Set.mem_sdiff, mem_invDomain] at hw
    exact hw.1.1
  have hYu : Psi c u ∈ Y := by
    rw [hY]
    refine ⟨?_, ?_⟩
    · rw [mem_invDomain]
      exact ⟨fun h0 => huc (sub_eq_zero.mp (inv_eq_zero.mp h0)), by rw [PsiInv_Psi]; exact hu.1⟩
    · rintro ⟨y, ⟨t, rfl⟩, hy⟩
      exact hu.2 ⟨t, by rw [← PsiInv_Psi c u, ← hy, PsiInv_Psi c (γ t)]⟩
  have hYv : Psi c v ∈ Y := by
    rw [hY]
    refine ⟨?_, ?_⟩
    · rw [mem_invDomain]
      exact ⟨fun h0 => hvc (sub_eq_zero.mp (inv_eq_zero.mp h0)), by rw [PsiInv_Psi]; exact hv.1⟩
    · rintro ⟨y, ⟨t, rfl⟩, hy⟩
      exact hv.2 ⟨t, by rw [← PsiInv_Psi c v, ← hy, PsiInv_Psi c (γ t)]⟩
  have hpre : IsPreconnected (PsiInv c '' connectedComponentIn Y (Psi c u)) :=
    isPreconnected_connectedComponentIn.image _ ((continuousOn_PsiInv c).mono fun w hw =>
      hYsub (connectedComponentIn_subset Y (Psi c u) hw))
  have himgsub : PsiInv c '' connectedComponentIn Y (Psi c u) ⊆ X := by
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨hzS, hzT⟩ := connectedComponentIn_subset Y (Psi c u) hz
    rw [mem_invDomain] at hzS
    rw [hX]
    refine ⟨hzS.2, fun hzr => hzT ?_⟩
    obtain ⟨t, ht⟩ := hzr
    exact ⟨γ t, ⟨t, rfl⟩, by rw [← Psi_PsiInv c z, ht]⟩
  have humem : u ∈ PsiInv c '' connectedComponentIn Y (Psi c u) :=
    ⟨Psi c u, mem_connectedComponentIn hYu, PsiInv_Psi c u⟩
  have hvmem : v ∈ PsiInv c '' connectedComponentIn Y (Psi c u) :=
    ⟨Psi c v, by rw [h]; exact mem_connectedComponentIn hYv, PsiInv_Psi c v⟩
  exact connectedComponentIn_eq (hpre.subset_connectedComponentIn humem himgsub hvmem)

/-- The complement of the inverted domain meets the image of the arc exactly in the two image
endpoints. -/
theorem inter_invDomain_compl_range {D : Set ℂ} {c : ℂ}
    {γ : C(Set.Icc (0 : ℝ) 1, ℂ)} (hcr : c ∉ Set.range γ)
    (h₀ : γ ⟨0, by norm_num⟩ ∉ D) (h₁ : γ ⟨1, by norm_num⟩ ∉ D)
    (hint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → γ t ∈ D) :
    (invDomain c D)ᶜ ∩ (Psi c '' Set.range γ) =
      {Psi c (γ ⟨0, by norm_num⟩), Psi c (γ ⟨1, by norm_num⟩)} := by
  ext v
  constructor
  · rintro ⟨hv, y, hy, hyv⟩
    obtain ⟨t, ht, rfl⟩ := hy
    have hnotD : γ t ∉ D := by
      intro hD
      apply hv
      rw [← hyv, mem_invDomain]
      exact ⟨fun h0 => hcr ⟨t, sub_eq_zero.mp (inv_eq_zero.mp h0)⟩, by rw [PsiInv_Psi]; exact hD⟩
    have ht01 : (t : ℝ) = 0 ∨ (t : ℝ) = 1 := by
      by_contra hneg
      push Not at hneg
      exact hnotD (hint t ⟨lt_of_le_of_ne t.2.1 (Ne.symm hneg.1),
        lt_of_le_of_ne t.2.2 hneg.2⟩)
    rcases ht01 with h | h
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      left
      have ht0 : t = (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := Subtype.ext h
      rw [← hyv, ht0]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      right
      have ht1 : t = (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := Subtype.ext h
      rw [← hyv, ht1]
  · rintro (h | h)
    · rw [h]
      refine ⟨?_, γ ⟨0, by norm_num⟩, ⟨⟨0, by norm_num⟩, rfl⟩, rfl⟩
      intro hmem
      rw [mem_invDomain, PsiInv_Psi] at hmem
      exact h₀ hmem.2
    · rw [h]
      refine ⟨?_, γ ⟨1, by norm_num⟩, ⟨⟨1, by norm_num⟩, rfl⟩, rfl⟩
      intro hmem
      rw [mem_invDomain, PsiInv_Psi] at hmem
      exact h₁ hmem.2

theorem crosscutAtMostTwoDomain_of_compactTwoPoints
    (h2p : ∀ {A B : Set ℂ}, IsCompact A → IsCompact B → IsPreconnected Aᶜ → IsPreconnected Bᶜ →
      ∀ {p q : ℂ}, p ≠ q → A ∩ B = {p, q} →
      ∀ x y z : ℂ, x ∉ A ∪ B → y ∉ A ∪ B → z ∉ A ∪ B →
        connectedComponentIn (A ∪ B)ᶜ x = connectedComponentIn (A ∪ B)ᶜ y ∨
        connectedComponentIn (A ∪ B)ᶜ x = connectedComponentIn (A ∪ B)ᶜ z ∨
        connectedComponentIn (A ∪ B)ᶜ y = connectedComponentIn (A ∪ B)ᶜ z)
    {D : Set ℂ} (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    {γ : C(Set.Icc (0 : ℝ) 1, ℂ)} (hγ : Function.Injective γ)
    (h₀ : γ ⟨0, by norm_num⟩ ∉ D) (h₁ : γ ⟨1, by norm_num⟩ ∉ D)
    (hint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → γ t ∈ D) :
    ∀ x y z : ℂ, x ∈ D \ Set.range γ → y ∈ D \ Set.range γ → z ∈ D \ Set.range γ →
      connectedComponentIn (D \ Set.range γ) x = connectedComponentIn (D \ Set.range γ) y ∨
      connectedComponentIn (D \ Set.range γ) x = connectedComponentIn (D \ Set.range γ) z ∨
      connectedComponentIn (D \ Set.range γ) y = connectedComponentIn (D \ Set.range γ) z := by
  intro x y z hx hy hz
  by_cases hxy : x = y
  · exact Or.inl (by rw [hxy])
  by_cases hxz : x = z
  · exact Or.inr (Or.inl (by rw [hxz]))
  by_cases hyz : y = z
  · exact Or.inr (Or.inr (by rw [hyz]))
  -- the inversion centre
  have hDne : D.Nonempty := ⟨x, hx.1⟩
  obtain ⟨c, hcD, hcr, hcF⟩ :=
    exists_mem_notMem_range_finite hDopen hDne hγ
      (F := ({x, y, z} : Set ℂ)) ((Set.finite_singleton (z : ℂ)).insert y |>.insert x)
  have hcx : x ≠ c := fun h => hcF (by rw [h]; simp)
  have hcy : y ≠ c := fun h => hcF (by rw [h]; simp)
  have hcz : z ≠ c := fun h => hcF (by rw [h]; simp)
  -- the inverted arc
  set γ' : C(Set.Icc (0 : ℝ) 1, ℂ) :=
    ⟨fun t => Psi c (γ t), by
      exact Continuous.inv₀ (γ.continuous.sub continuous_const)
        (fun t => sub_ne_zero.mpr (fun h => hcr ⟨t, h⟩))⟩ with hγ'def
  have hγ'eq : ∀ t : Set.Icc (0 : ℝ) 1, γ' t = Psi c (γ t) := fun _ => rfl
  have hrange : Set.range γ' = Psi c '' Set.range γ := by
    rw [hγ'def]
    exact Set.range_comp (Psi c) γ
  have hφinj : Function.Injective (Psi c) := fun u v huv => by
    rw [← PsiInv_Psi c u, huv, PsiInv_Psi c v]
  have hγ'inj : Function.Injective γ' := fun s t hst => by
    refine hγ (hφinj ?_)
    rw [← hγ'eq s, ← hγ'eq t]
    exact hst
  have hpne : γ' ⟨0, by norm_num⟩ ≠ γ' ⟨1, by norm_num⟩ := by
    intro h
    have h' : (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) = ⟨1, by norm_num⟩ := hγ'inj h
    exact absurd (congrArg Subtype.val h') (by norm_num)
  have hinter : (invDomain c D)ᶜ ∩ Set.range γ' =
      {γ' ⟨0, by norm_num⟩, γ' ⟨1, by norm_num⟩} := by
    have h := inter_invDomain_compl_range (D := D) (c := c) (γ := γ) hcr h₀ h₁ hint
    simpa only [hrange, hγ'eq ⟨0, by norm_num⟩, hγ'eq ⟨1, by norm_num⟩] using h
  -- the three points in the inverted picture
  have memx : Psi c x ∈ invDomain c D \ Set.range γ' := by
    refine ⟨?_, ?_⟩
    · rw [mem_invDomain]
      exact ⟨fun h0 => hcx (sub_eq_zero.mp (inv_eq_zero.mp h0)), by rw [PsiInv_Psi]; exact hx.1⟩
    · rw [hrange]
      rintro ⟨w, ⟨t, rfl⟩, hw⟩
      exact hx.2 ⟨t, by rw [← PsiInv_Psi c x, ← hw, PsiInv_Psi c (γ t)]⟩
  have memy : Psi c y ∈ invDomain c D \ Set.range γ' := by
    refine ⟨?_, ?_⟩
    · rw [mem_invDomain]
      exact ⟨fun h0 => hcy (sub_eq_zero.mp (inv_eq_zero.mp h0)), by rw [PsiInv_Psi]; exact hy.1⟩
    · rw [hrange]
      rintro ⟨w, ⟨t, rfl⟩, hw⟩
      exact hy.2 ⟨t, by rw [← PsiInv_Psi c y, ← hw, PsiInv_Psi c (γ t)]⟩
  have memz : Psi c z ∈ invDomain c D \ Set.range γ' := by
    refine ⟨?_, ?_⟩
    · rw [mem_invDomain]
      exact ⟨fun h0 => hcz (sub_eq_zero.mp (inv_eq_zero.mp h0)), by rw [PsiInv_Psi]; exact hz.1⟩
    · rw [hrange]
      rintro ⟨w, ⟨t, rfl⟩, hw⟩
      exact hz.2 ⟨t, by rw [← PsiInv_Psi c z, ← hw, PsiInv_Psi c (γ t)]⟩
  have hcompl : ((invDomain c D)ᶜ ∪ Set.range γ')ᶜ = invDomain c D \ Set.range γ' := by
    ext w
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_sdiff, not_or]
    tauto
  have hmain := h2p (invDomain_compact_compl hDopen hcD) (isCompact_range γ'.continuous)
    (by simpa using invDomain_preconnected hDopen hDconn hcD)
    (isPreconnected_compl_range_arc hγ'inj) hpne hinter (Psi c x) (Psi c y) (Psi c z)
    (by rw [← Set.mem_compl_iff, hcompl]; exact memx)
    (by rw [← Set.mem_compl_iff, hcompl]; exact memy)
    (by rw [← Set.mem_compl_iff, hcompl]; exact memz)
  rw [hcompl] at hmain
  rcases hmain with h | h | h
  · exact Or.inl (connectedComponentIn_eq_of_inversion hx hy hcx hcy (by rw [hrange] at h; exact h))
  · exact Or.inr (Or.inl
      (connectedComponentIn_eq_of_inversion hx hz hcx hcz (by rw [hrange] at h; exact h)))
  · exact Or.inr (Or.inr
      (connectedComponentIn_eq_of_inversion hy hz hcy hcz (by rw [hrange] at h; exact h)))

end

end Work.Spike
