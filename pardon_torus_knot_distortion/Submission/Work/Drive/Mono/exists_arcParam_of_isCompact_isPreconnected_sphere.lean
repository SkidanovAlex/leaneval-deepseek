import Mathlib

/-!
# A compact preconnected proper subset of the circle is a closed arc

A compact preconnected subset `A` of the unit circle `S¹ ⊂ ℂ` with at least two points and
different from the whole circle is a *closed arc*: it is the image of `[-1,1]` under an injective
continuous map `u`, the image of the **open** interval is an **open** subset of the circle, and the
two endpoints `u (-1)`, `u 1` are limits of points of the complement of `A`.

Proof outline.  Choose `p ∉ A` and `θ` with `exp θ = p`.  The map `exp : ℝ → S¹`,
`exp t = e^{it}`, is a covering map with period `2π`; cutting the circle at `p`, the set
`A' = exp ⁻¹' A ∩ [θ, θ+2π] ⊆ ℝ` is compact, nonempty and preconnected (the last is the only
non-formal point: it is order convexity of `A'`, proved by cutting a supposed gap with the two
closed pieces `A' ∩ (-∞, z]`, `A' ∩ [z, ∞)` and using preconnectedness of `A = exp '' A'`).
A nonempty compact preconnected subset of `ℝ` is a closed interval `[c,d]`, and since `A` is
nontrivial and misses `p`, one gets `c < d`, `d - c < 2π` and `A = exp '' [c,d]`.  Parametrising
`[c,d]` by `[-1,1]` gives the arc; openness of the image of the open interval follows from
`Circle.exp` being an open map, and the endpoint conditions from the open arcs just beyond
`c` and `d`.
-/

open Set Filter

namespace Work.Drive.Mono

/-- A nonempty compact preconnected subset of `ℝ` is a closed interval. -/
theorem exists_Icc_of_isCompact_isPreconnected_real {s : Set ℝ} (hne : s.Nonempty)
    (hcomp : IsCompact s) (hconn : IsPreconnected s) :
    ∃ c d : ℝ, c ≤ d ∧ s = Set.Icc c d :=
  ⟨sInf s, sSup s, csInf_le_csSup hne hcomp.bddBelow hcomp.bddAbove,
    eq_Icc_of_connected_compact ⟨hne, hconn⟩ hcomp⟩

/-- The endpoints of the closed arc `exp '' [c,d]` of length `< 2π` are limits of points of the
complement of the arc. -/
theorem exp_endpoints_mem_closure_compl_exp_Icc (c d : ℝ) (h : d - c < 2 * Real.pi) :
    Circle.exp c ∈ closure ((Circle.exp '' Set.Icc c d)ᶜ) ∧
    Circle.exp d ∈ closure ((Circle.exp '' Set.Icc c d)ᶜ) := by
  have hm : 0 < 2 * Real.pi - (d - c) := by linarith [h, Real.pi_pos]
  have keyL : ∀ ε : ℝ, 0 < ε → ε < 2 * Real.pi - (d - c) →
      Circle.exp (c - ε) ∉ Circle.exp '' Set.Icc c d := by
    intro ε hε0 hεm
    rintro ⟨t, ht, hte⟩
    have hlen : d - (c - ε) < 2 * Real.pi := by linarith
    have := (Circle.exp_injOn_Icc hlen)
      (show t ∈ Set.Icc (c - ε) d from ⟨by linarith [ht.1, ht.2], ht.2⟩)
      (show c - ε ∈ Set.Icc (c - ε) d from ⟨le_refl _, by linarith [ht.1, ht.2]⟩) hte
    linarith [ht.1]
  have keyR : ∀ ε : ℝ, 0 < ε → ε < 2 * Real.pi - (d - c) →
      Circle.exp (d + ε) ∉ Circle.exp '' Set.Icc c d := by
    intro ε hε0 hεm
    rintro ⟨t, ht, hte⟩
    have hlen : (d + ε) - c < 2 * Real.pi := by linarith
    have := (Circle.exp_injOn_Icc hlen)
      (show t ∈ Set.Icc c (d + ε) from ⟨ht.1, by linarith [ht.1, ht.2]⟩)
      (show d + ε ∈ Set.Icc c (d + ε) from ⟨by linarith [ht.1, ht.2], le_refl _⟩) hte
    linarith [ht.2]
  have hsub : Set.Iio (2 * Real.pi - (d - c)) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
    nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hm)
  constructor
  · rw [mem_closure_iff_clusterPt]
    have hcont : Continuous (fun ε : ℝ => Circle.exp (c - ε)) :=
      Circle.exp.continuous.comp (by fun_prop)
    have htend : Filter.Tendsto (fun ε : ℝ => Circle.exp (c - ε))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (Circle.exp c)) := by
      have h0 : (fun ε : ℝ => Circle.exp (c - ε)) 0 = Circle.exp c := by simp
      rw [← h0]
      exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
        Circle.exp (c - ε) ∈ (Circle.exp '' Set.Icc c d)ᶜ := by
      filter_upwards [self_mem_nhdsWithin, hsub] with ε hε0 hεm
      exact keyL ε hε0 hεm
    exact (htend.mapClusterPt).clusterPt.mono (Filter.le_principal_iff.mpr hev)
  · rw [mem_closure_iff_clusterPt]
    have hcont : Continuous (fun ε : ℝ => Circle.exp (d + ε)) :=
      Circle.exp.continuous.comp (by fun_prop)
    have htend : Filter.Tendsto (fun ε : ℝ => Circle.exp (d + ε))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (Circle.exp d)) := by
      have h0 : (fun ε : ℝ => Circle.exp (d + ε)) 0 = Circle.exp d := by simp
      rw [← h0]
      exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
        Circle.exp (d + ε) ∈ (Circle.exp '' Set.Icc c d)ᶜ := by
      filter_upwards [self_mem_nhdsWithin, hsub] with ε hε0 hεm
      exact keyR ε hε0 hεm
    exact (htend.mapClusterPt).clusterPt.mono (Filter.le_principal_iff.mpr hev)

/-- Cutting the circle at `exp θ`, the preimage under `exp` of a preconnected set avoiding
`exp θ` is preconnected. -/
theorem isPreconnected_preimage_exp_inter_Icc (A : Set Circle) (θ : ℝ)
    (hcomp : IsCompact A) (hconn : IsPreconnected A) (hdisj : Circle.exp θ ∉ A) :
    IsPreconnected (Circle.exp ⁻¹' A ∩ Set.Icc θ (θ + 2 * Real.pi)) := by
  set A' : Set ℝ := Circle.exp ⁻¹' A ∩ Set.Icc θ (θ + 2 * Real.pi) with hA'def
  have hA'comp : IsCompact A' :=
    isCompact_Icc.inter_left (hcomp.isClosed.preimage Circle.exp.continuous)
  have hexpA' : Circle.exp '' A' = A := by
    ext w
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht.1
    · intro hw
      have hmem : w ∈ Circle.exp '' Set.Icc θ (θ + 2 * Real.pi) := by
        rw [Circle.periodic_exp.image_Icc Real.two_pi_pos θ,
          Circle.exp_surjective.range_eq]
        exact mem_univ w
      obtain ⟨t, ht, htw⟩ := hmem
      exact ⟨t, ⟨show Circle.exp t ∈ A from htw ▸ hw, ht⟩, htw⟩
  rw [isPreconnected_iff_ordConnected, Set.ordConnected_iff]
  intro x hx y hy hxy z hz
  have hzI : z ∈ Set.Icc θ (θ + 2 * Real.pi) :=
    ⟨le_trans hx.2.1 hz.1, le_trans hz.2 hy.2.2⟩
  by_contra hzA'
  set S₁ : Set ℝ := A' ∩ Set.Iic z with hS₁def
  set S₂ : Set ℝ := A' ∩ Set.Ici z with hS₂def
  have hS₁c : IsCompact S₁ := hA'comp.inter_right isClosed_Iic
  have hS₂c : IsCompact S₂ := hA'comp.inter_right isClosed_Ici
  have hunion : S₁ ∪ S₂ = A' := by
    rw [hS₁def, hS₂def]
    ext w
    constructor
    · rintro (⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw
    · intro hw
      rcases le_total w z with hh | hh
      · exact Or.inl ⟨hw, hh⟩
      · exact Or.inr ⟨hw, hh⟩
  have hXY : Circle.exp '' S₁ ∪ Circle.exp '' S₂ = A := by
    rw [← Set.image_union, hunion, hexpA']
  have hdisXY : Disjoint (Circle.exp '' S₁) (Circle.exp '' S₂) := by
    rw [Set.disjoint_left]
    rintro w ⟨a, ⟨haA', haz⟩, rfl⟩ ⟨b, ⟨hbA', hbz⟩, hba⟩
    have hle : b - a ≤ 2 * Real.pi := by linarith [haA'.2.1, hbA'.2.2]
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hab : a = b := (Circle.exp_injOn_Icc hlt)
        (show a ∈ Set.Icc a b from ⟨le_refl a, le_trans haz hbz⟩)
        (show b ∈ Set.Icc a b from ⟨le_trans haz hbz, le_refl b⟩) hba.symm
      have hza : z ≤ a := by rw [hab]; exact hbz
      have hzea : z = a := le_antisymm hza haz
      have hzA'' : z ∈ A' := by rw [hzea]; exact haA'
      exact hzA' hzA''
    · have haθ : θ ≤ a := haA'.2.1
      have hb2 : b ≤ θ + 2 * Real.pi := hbA'.2.2
      have hone : a ≤ θ := by linarith
      have haθeq : a = θ := le_antisymm hone haθ
      have hmemA : Circle.exp a ∈ A := haA'.1
      rw [haθeq] at hmemA
      exact hdisj hmemA
  have hclosed1 : IsClosed (Circle.exp '' S₁) := (hS₁c.image Circle.exp.continuous).isClosed
  have hclosed2 : IsClosed (Circle.exp '' S₂) := (hS₂c.image Circle.exp.continuous).isClosed
  have hdis : A ∩ (Circle.exp '' S₁ ∩ Circle.exp '' S₂) = ∅ := by
    rw [Set.disjoint_iff_inter_eq_empty.mp hdisXY]; exact Set.inter_empty A
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hconn _ _ hclosed1 hclosed2
      (le_of_eq hXY.symm) hdis) with hh | hh
  · have hmem : Circle.exp y ∈ Circle.exp '' S₂ := ⟨y, ⟨hy, hz.2⟩, rfl⟩
    exact (Set.disjoint_left.mp hdisXY (hh hy.1)) hmem
  · have hmem : Circle.exp x ∈ Circle.exp '' S₁ := ⟨x, ⟨hx, hz.1⟩, rfl⟩
    exact (Set.disjoint_left.mp hdisXY.symm (hh hx.1)) hmem

/-- Cutting the circle at `exp θ`, the part of `exp ⁻¹' A` inside a full period maps onto `A`. -/
theorem exp_image_preimage_inter_Icc (A : Set Circle) (θ : ℝ) :
    Circle.exp '' (Circle.exp ⁻¹' A ∩ Set.Icc θ (θ + 2 * Real.pi)) = A := by
  ext w
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ht.1
  · intro hw
    have hmem : w ∈ Circle.exp '' Set.Icc θ (θ + 2 * Real.pi) := by
      rw [Circle.periodic_exp.image_Icc Real.two_pi_pos θ, Circle.exp_surjective.range_eq]
      exact mem_univ w
    obtain ⟨t, ht, htw⟩ := hmem
    exact ⟨t, ⟨show Circle.exp t ∈ A from htw ▸ hw, ht⟩, htw⟩

/-- A compact preconnected subset of the circle with at least two points, different from the whole
circle, is a closed arc `exp '' [c,d]` of length `< 2π`. -/
theorem exists_exp_Icc_of_isCompact_isPreconnected_circle (A : Set Circle)
    (hcomp : IsCompact A) (hconn : IsPreconnected A) (hnontriv : A.Nontrivial)
    (hproper : A ≠ Set.univ) :
    ∃ c d : ℝ, c < d ∧ d - c < 2 * Real.pi ∧ A = Circle.exp '' Set.Icc c d := by
  obtain ⟨p, hp⟩ : ∃ p : Circle, p ∉ A := by
    by_contra hcon
    exact hproper (eq_univ_of_forall fun x => by by_contra hx; exact hcon ⟨x, hx⟩)
  obtain ⟨θ, hθ⟩ := Circle.exp_surjective p
  have hθA : Circle.exp θ ∉ A := by rw [hθ]; exact hp
  set A' : Set ℝ := Circle.exp ⁻¹' A ∩ Set.Icc θ (θ + 2 * Real.pi) with hA'def
  have hmemA' : ∀ t, t ∈ A' ↔ Circle.exp t ∈ A ∧ t ∈ Set.Icc θ (θ + 2 * Real.pi) := by
    intro t; rw [hA'def]; rfl
  have hexpA' : Circle.exp '' A' = A := by
    rw [hA'def]; exact exp_image_preimage_inter_Icc A θ
  have hA'comp : IsCompact A' := by
    rw [hA'def]
    exact isCompact_Icc.inter_left (hcomp.isClosed.preimage Circle.exp.continuous)
  have hA'conn : IsPreconnected A' := by
    rw [hA'def]
    exact isPreconnected_preimage_exp_inter_Icc A θ hcomp hconn hθA
  have htwo : ∃ t₁ ∈ A', ∃ t₂ ∈ A', t₁ ≠ t₂ := by
    obtain ⟨q₁, hq₁, q₂, hq₂, hqne⟩ := hnontriv
    obtain ⟨t₁, ht₁, he₁⟩ : q₁ ∈ Circle.exp '' A' := by rw [hexpA']; exact hq₁
    obtain ⟨t₂, ht₂, he₂⟩ : q₂ ∈ Circle.exp '' A' := by rw [hexpA']; exact hq₂
    exact ⟨t₁, ht₁, t₂, ht₂, fun h => hqne (by rw [← he₁, h, he₂])⟩
  have hA'ne : A'.Nonempty := by obtain ⟨t₁, ht₁, -⟩ := htwo; exact ⟨t₁, ht₁⟩
  obtain ⟨c, d, hcd, hA'eq⟩ :=
    exists_Icc_of_isCompact_isPreconnected_real hA'ne hA'comp hA'conn
  have hc : Circle.exp c ∈ A ∧ c ∈ Set.Icc θ (θ + 2 * Real.pi) :=
    (hmemA' c).mp (by rw [hA'eq]; exact left_mem_Icc.mpr hcd)
  have hd : Circle.exp d ∈ A ∧ d ∈ Set.Icc θ (θ + 2 * Real.pi) :=
    (hmemA' d).mp (by rw [hA'eq]; exact right_mem_Icc.mpr hcd)
  have hcne : c ≠ d := by
    rintro hcd_eq
    obtain ⟨t₁, ht₁, t₂, ht₂, hne'⟩ := htwo
    rw [hA'eq, hcd_eq, Set.Icc_self, Set.mem_singleton_iff] at ht₁ ht₂
    exact hne' (ht₁.trans ht₂.symm)
  have hθc : θ < c := lt_of_le_of_ne hc.2.1 (fun h => hθA (by rw [h]; exact hc.1))
  have hdθ2 : d < θ + 2 * Real.pi := by
    refine lt_of_le_of_ne hd.2.2 (fun h => ?_)
    have hmem : Circle.exp (θ + 2 * Real.pi) ∈ A := by rw [← h]; exact hd.1
    rw [Circle.periodic_exp θ] at hmem
    exact hθA hmem
  refine ⟨c, d, lt_of_le_of_ne hcd hcne, by linarith, ?_⟩
  rw [← hexpA', hA'eq]

theorem exists_arcParam_of_isCompact_isPreconnected_sphere
    (A : Set (Metric.sphere (0 : ℂ) 1))
    (hcomp : IsCompact A) (hconn : IsPreconnected A)
    (h2 : ∃ p ∈ A, ∃ q ∈ A, p ≠ q) (hne : ∃ p : Metric.sphere (0 : ℂ) 1, p ∉ A) :
    ∃ u : ℝ → Metric.sphere (0 : ℂ) 1, Continuous u ∧ Set.InjOn u (Set.Icc (-1:ℝ) 1) ∧
      u '' Set.Icc (-1:ℝ) 1 = A ∧
      IsOpen (u '' Set.Ioo (-1:ℝ) 1) ∧
      u (-1) ∈ closure (Aᶜ) ∧ u 1 ∈ closure (Aᶜ) ∧ u (-1) ≠ u 1 := by
  have hproper : A ≠ Set.univ := by
    intro h
    obtain ⟨p, hp⟩ := hne
    exact hp (by rw [h]; exact Set.mem_univ p)
  obtain ⟨c, d, hcd, hdiff, hA⟩ :=
    exists_exp_Icc_of_isCompact_isPreconnected_circle A hcomp hconn h2 hproper
  let φ : ℝ → ℝ := fun t => c + (d - c) * ((t + 1) / 2)
  let u : ℝ → Metric.sphere (0:ℂ) 1 := fun t => Circle.exp (φ t)
  have hφcc : φ '' Set.Icc (-1:ℝ) 1 = Set.Icc c d := by
    dsimp only [φ]
    have hd0 : 0 < d - c := sub_pos.mpr hcd
    ext x
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      refine ⟨2 * (x - c) / (d - c) - 1, ⟨?_, ?_⟩, ?_⟩
      · have h : 0 ≤ 2 * (x - c) / (d - c) := div_nonneg (by linarith) hd0.le
        linarith
      · have h : 2 * (x - c) / (d - c) ≤ 2 := by rw [div_le_iff₀ hd0]; linarith
        linarith
      · field_simp; ring
  have hφoo : φ '' Set.Ioo (-1:ℝ) 1 = Set.Ioo c d := by
    dsimp only [φ]
    have hd0 : 0 < d - c := sub_pos.mpr hcd
    ext x
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      refine ⟨2 * (x - c) / (d - c) - 1, ⟨?_, ?_⟩, ?_⟩
      · have h : 0 < 2 * (x - c) / (d - c) := div_pos (by linarith) hd0
        linarith
      · have h : 2 * (x - c) / (d - c) < 2 := by rw [div_lt_iff₀ hd0]; linarith
        linarith
      · field_simp; ring
  have hcont : Continuous u := Circle.exp.continuous.comp (by fun_prop)
  have hinj : Set.InjOn u (Set.Icc (-1:ℝ) 1) := by
    intro s hs t ht hst
    have hs' : φ s ∈ Set.Icc c d := by rw [← hφcc]; exact ⟨s, hs, rfl⟩
    have ht' : φ t ∈ Set.Icc c d := by rw [← hφcc]; exact ⟨t, ht, rfl⟩
    have hst' : φ s = φ t := (Circle.exp_injOn_Icc hdiff) hs' ht' hst
    have hd0 : 0 < d - c := sub_pos.mpr hcd
    have key : (d - c) * ((s + 1) / 2) = (d - c) * ((t + 1) / 2) := by
      dsimp only [φ] at hst'; linarith
    have key2 : (s + 1) / 2 = (t + 1) / 2 := mul_left_cancel₀ (ne_of_gt hd0) key
    linarith
  have himg : u '' Set.Icc (-1:ℝ) 1 = A := by
    have h1 : u '' Set.Icc (-1:ℝ) 1 = Circle.exp '' Set.Icc c d := by
      change (⇑Circle.exp ∘ φ) '' Set.Icc (-1:ℝ) 1 = Circle.exp '' Set.Icc c d
      rw [Set.image_comp, hφcc]
    rw [h1, ← hA]
  have hopen : IsOpen (u '' Set.Ioo (-1:ℝ) 1) := by
    have h1 : u '' Set.Ioo (-1:ℝ) 1 = Circle.exp '' Set.Ioo c d := by
      change (⇑Circle.exp ∘ φ) '' Set.Ioo (-1:ℝ) 1 = Circle.exp '' Set.Ioo c d
      rw [Set.image_comp, hφoo]
    rw [h1]
    exact Circle.isCoveringMap_exp.isOpenMap _ isOpen_Ioo
  have hcl := exp_endpoints_mem_closure_compl_exp_Icc c d hdiff
  have hu1 : u (-1) = Circle.exp c := by dsimp only [u, φ]; congr 1; ring
  have hu2 : u 1 = Circle.exp d := by dsimp only [u, φ]; congr 1; ring
  have hcl1 : u (-1) ∈ closure (Aᶜ) := by rw [hu1, hA]; exact hcl.1
  have hcl2 : u 1 ∈ closure (Aᶜ) := by rw [hu2, hA]; exact hcl.2
  have hne1 : u (-1) ≠ u 1 := by
    have h1 : (-1:ℝ) ∈ Set.Icc (-1:ℝ) 1 := by norm_num
    have h2 : (1:ℝ) ∈ Set.Icc (-1:ℝ) 1 := by norm_num
    intro h
    have := (hinj.eq_iff h1 h2).mp h
    norm_num at this
  exact ⟨u, hcont, hinj, himg, hopen, hcl1, hcl2, hne1⟩

end Work.Drive.Mono
