import Mathlib
import Submission.Commons.Topology.Jordan.closed_separates_continuum
import Submission.Commons.Topology.Jordan.joinedIn_compl_of_re_im_bounds

open Set
open scoped Topology

namespace Commons.Topology.Strip

noncomputable section

/-- The real-linear homeomorphism `ℝ × ℝ ≃ₜ ℂ`, `(x,y) ↦ x + y·I`. -/
private def toC : (ℝ × ℝ) ≃ₜ ℂ := Complex.equivRealProdCLM.toHomeomorph.symm

private lemma toC_apply (q : ℝ × ℝ) : toC q = (q.1 : ℂ) + (q.2 : ℂ) * Complex.I := by
  simp [toC, Complex.equivRealProdCLM_symm_apply]

private lemma toC_re (q : ℝ × ℝ) : (toC q).re = q.1 := by
  rw [toC_apply]
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]

private lemma toC_im (q : ℝ × ℝ) : (toC q).im = q.2 := by
  rw [toC_apply]
  simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]

/-- **A vertical variant of `joinedIn_compl_of_re_im_bounds`.** If `T ⊆ ℂ` is contained in the
rectangle `{α ≤ re ≤ β, c ≤ im ≤ d}`, `a` lies strictly below it and `b` strictly above it, then
`a` and `b` can be joined by a path avoiding `T`: go right, up, and back left. -/
private lemma joinedIn_compl_of_re_im_bounds_vert {T : Set ℂ} {α β c d : ℝ} {a b : ℂ}
    (hT : ∀ w ∈ T, α ≤ w.re ∧ w.re ≤ β ∧ c ≤ w.im ∧ w.im ≤ d)
    (ha : a.im < c) (hb : d < b.im) : JoinedIn Tᶜ a b := by
  set a' : ℂ := a + ((β + 1 - a.re : ℝ) : ℂ) with ha'def
  set b' : ℂ := b + ((β + 1 - b.re : ℝ) : ℂ) with hb'def
  have him_a' : a'.im = a.im := by
    rw [ha'def]; simp only [Complex.add_im, Complex.ofReal_im]; ring
  have him_b' : b'.im = b.im := by
    rw [hb'def]; simp only [Complex.add_im, Complex.ofReal_im]; ring
  have hre_a' : a'.re = β + 1 := by
    rw [ha'def]; simp only [Complex.add_re, Complex.ofReal_re]; ring
  have hre_b' : b'.re = β + 1 := by
    rw [hb'def]; simp only [Complex.add_re, Complex.ofReal_re]; ring
  have hseg1 : segment ℝ a a' ⊆ Tᶜ := by
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzT
    have hzim : z.im = a.im := by
      have hconv : Convex ℝ {w : ℂ | w.im = a.im} := by
        have h := convex_hyperplane (𝕜 := ℝ) (f := Complex.imLm) Complex.imLm.isLinear a.im
        simpa using h
      exact hconv.segment_subset (by simp) him_a' hz
    have h1 := (hT z hzT).2.2.1
    linarith
  have hseg2 : segment ℝ a' b' ⊆ Tᶜ := by
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzT
    have hzre : z.re = β + 1 := by
      have hconv : Convex ℝ {w : ℂ | w.re = β + 1} := by
        have h := convex_hyperplane (𝕜 := ℝ) (f := Complex.reLm) Complex.reLm.isLinear (β + 1)
        simpa using h
      exact hconv.segment_subset hre_a' hre_b' hz
    have h2 := (hT z hzT).2.1
    linarith
  have hseg3 : segment ℝ b' b ⊆ Tᶜ := by
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzT
    have hzim : z.im = b.im := by
      have hconv : Convex ℝ {w : ℂ | w.im = b.im} := by
        have h := convex_hyperplane (𝕜 := ℝ) (f := Complex.imLm) Complex.imLm.isLinear b.im
        simpa using h
      exact hconv.segment_subset him_b' (by simp) hz
    have h3 := (hT z hzT).2.2.2
    linarith
  exact (JoinedIn.of_segment_subset hseg1).trans
    ((JoinedIn.of_segment_subset hseg2).trans (JoinedIn.of_segment_subset hseg3))

/-- A path from `(0,-1)` to `(0,2)` avoiding `F` yields the strip crosscut: reparametrising so that
the first crossing of the line `{y = 0}` is the new start and the last crossing of `{y = 1}` is the
new end. -/
private theorem crosscut_of_path (F : Set (ℝ × ℝ))
    (ρ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ))
    (hρ0 : ρ 0 = (0, -1)) (hρ1 : ρ 1 = (0, 2))
    (hρF : ∀ t, ρ t ∉ F) :
    ∃ γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ),
      (γ 0).2 = 0 ∧ (γ 1).2 = 1 ∧
      (∀ t : Set.Icc (0:ℝ) 1, 0 < (t:ℝ) → (t:ℝ) < 1 →
        0 < (γ t).2 ∧ (γ t).2 < 1 ∧ γ t ∉ F) := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  let G : ℝ → ℝ := fun s => (ρ (Set.projIcc 0 1 h01 s)).2
  have hGc : Continuous G := (continuous_snd.comp ρ.continuous).comp continuous_projIcc
  have proj_eq (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
      Set.projIcc 0 1 h01 x = (⟨x, hx⟩ : Set.Icc (0:ℝ) 1) :=
    Set.projIcc_of_mem h01 hx
  have hG0 : G 0 = -1 := by
    show (ρ (Set.projIcc 0 1 h01 0)).2 = -1
    have h : Set.projIcc 0 1 h01 0 = (0 : Set.Icc (0:ℝ) 1) := by
      rw [proj_eq 0 (by norm_num : (0:ℝ) ∈ Set.Icc (0:ℝ) 1)]; rfl
    rw [h, hρ0]
  have hG1 : G 1 = 2 := by
    show (ρ (Set.projIcc 0 1 h01 1)).2 = 2
    have h : Set.projIcc 0 1 h01 1 = (1 : Set.Icc (0:ℝ) 1) := by
      rw [proj_eq 1 (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)]; rfl
    rw [h, hρ1]
  let T1 : Set ℝ := {s | s ∈ Set.Icc (0:ℝ) 1 ∧ G s = 1}
  have hT1ne : T1.Nonempty := by
    have himg := intermediate_value_Icc h01 hGc.continuousOn
      (show (1:ℝ) ∈ Set.Icc (G 0) (G 1) from by rw [hG0, hG1]; norm_num)
    obtain ⟨s, hs, hGs⟩ := himg
    exact ⟨s, hs, hGs⟩
  have hT1cl : IsClosed T1 := by
    have : T1 = Set.Icc (0:ℝ) 1 ∩ {s | G s = 1} := by ext s; simp [T1]
    rw [this]; exact isClosed_Icc.inter (isClosed_eq hGc continuous_const)
  have hT1bd : BddBelow T1 := ⟨0, fun s hs => hs.1.1⟩
  set t₁ := sInf T1 with ht₁
  have ht1mem : t₁ ∈ T1 := hT1cl.csInf_mem hT1ne hT1bd
  have ht1low : (0:ℝ) ≤ t₁ := ht1mem.1.1
  have ht1up : t₁ ≤ 1 := ht1mem.1.2
  have hGt1 : G t₁ = 1 := ht1mem.2
  have ht1le : ∀ s ∈ T1, t₁ ≤ s := fun s hs => csInf_le hT1bd hs
  let T0 : Set ℝ := {s | s ∈ Set.Icc (0:ℝ) t₁ ∧ G s = 0}
  have hT0ne : T0.Nonempty := by
    have himg := intermediate_value_Icc ht1low hGc.continuousOn
      (show (0:ℝ) ∈ Set.Icc (G 0) (G t₁) from by rw [hG0, hGt1]; norm_num)
    obtain ⟨s, hs, hGs⟩ := himg
    exact ⟨s, hs, hGs⟩
  have hT0cl : IsClosed T0 := by
    have : T0 = Set.Icc (0:ℝ) t₁ ∩ {s | G s = 0} := by ext s; simp [T0]
    rw [this]; exact isClosed_Icc.inter (isClosed_eq hGc continuous_const)
  have hT0bd : BddAbove T0 := ⟨t₁, fun s hs => hs.1.2⟩
  set t₀ := sSup T0 with ht₀
  have ht0mem : t₀ ∈ T0 := hT0cl.csSup_mem hT0ne hT0bd
  have ht0low : (0:ℝ) ≤ t₀ := ht0mem.1.1
  have ht0le1 : t₀ ≤ t₁ := ht0mem.1.2
  have hGt0 : G t₀ = 0 := ht0mem.2
  have ht0ge : ∀ s ∈ T0, s ≤ t₀ := fun s hs => le_csSup hT0bd hs
  have ht0lt : t₀ < t₁ := by
    rcases lt_or_eq_of_le ht0le1 with h | h
    · exact h
    · exfalso; rw [h] at hGt0; rw [hGt1] at hGt0; norm_num at hGt0
  have hmid : ∀ s : ℝ, t₀ < s → s < t₁ → 0 < G s ∧ G s < 1 := by
    intro s hs0 hs1
    have hs0' : (0:ℝ) < s := lt_of_le_of_lt ht0low hs0
    have hpos : 0 < G s := by
      rcases lt_trichotomy (G s) 0 with h | h | h
      · have himg := intermediate_value_Icc hs1.le hGc.continuousOn
          (show (0:ℝ) ∈ Set.Icc (G s) (G t₁) from ⟨h.le, by rw [hGt1]; norm_num⟩)
        obtain ⟨s', hs', hGs'⟩ := himg
        have hs'0 : t₀ < s' := lt_of_lt_of_le hs0 hs'.1
        have hs'T0 : s' ∈ T0 := ⟨⟨le_trans hs0'.le hs'.1, hs'.2⟩, hGs'⟩
        exact absurd (ht0ge s' hs'T0) (not_le.mpr hs'0)
      · have hsT0 : s ∈ T0 := ⟨⟨hs0'.le, hs1.le⟩, h⟩
        exact absurd (ht0ge s hsT0) (not_le.mpr hs0)
      · exact h
    have hlt1 : G s < 1 := by
      rcases lt_trichotomy (G s) 1 with h | h | h
      · exact h
      · exact absurd (ht1le s ⟨⟨hs0'.le, hs1.le.trans ht1up⟩, h⟩) (not_le.mpr hs1)
      · have himg := intermediate_value_Icc (le_of_lt hs0) hGc.continuousOn
          (show (1:ℝ) ∈ Set.Icc (G t₀) (G s) from ⟨by rw [hGt0]; norm_num, h.le⟩)
        obtain ⟨s', hs', hGs'⟩ := himg
        have hs'1 : s' < t₁ := lt_of_le_of_lt hs'.2 hs1
        have hs'T1 : s' ∈ T1 := ⟨⟨le_trans ht0low hs'.1, le_trans (le_trans hs'.2 hs1.le) ht1up⟩, hGs'⟩
        exact absurd (ht1le s' hs'T1) (not_le.mpr hs'1)
    exact ⟨hpos, hlt1⟩
  have ht0mem01 : t₀ ∈ Set.Icc (0:ℝ) 1 := ⟨ht0low, ht0le1.trans ht1up⟩
  have ht1mem01 : t₁ ∈ Set.Icc (0:ℝ) 1 := ⟨ht1low, ht1up⟩
  let γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ) :=
    ⟨fun u => ρ (Set.projIcc 0 1 h01 (t₀ + (u:ℝ) * (t₁ - t₀))),
      ρ.continuous.comp (continuous_projIcc.comp (continuous_const.add
        (continuous_subtype_val.mul continuous_const)))⟩
  refine ⟨γ, ?_, ?_, ?_⟩
  · show (ρ (Set.projIcc 0 1 h01 (t₀ + ((0:Set.Icc (0:ℝ) 1):ℝ) * (t₁ - t₀)))).2 = 0
    have hz : t₀ + ((0:Set.Icc (0:ℝ) 1):ℝ) * (t₁ - t₀) = t₀ := by
      rw [show ((0:Set.Icc (0:ℝ) 1):ℝ) = 0 from rfl]; ring
    rw [hz]; exact hGt0
  · show (ρ (Set.projIcc 0 1 h01 (t₀ + ((1:Set.Icc (0:ℝ) 1):ℝ) * (t₁ - t₀)))).2 = 1
    have ho : t₀ + ((1:Set.Icc (0:ℝ) 1):ℝ) * (t₁ - t₀) = t₁ := by
      rw [show ((1:Set.Icc (0:ℝ) 1):ℝ) = 1 from rfl]; ring
    rw [ho]; exact hGt1
  · intro u hu0 hu1
    set s : ℝ := t₀ + (u:ℝ) * (t₁ - t₀) with hsdef
    have hs0 : t₀ < s := by have : (0:ℝ) < (u:ℝ) := hu0; nlinarith [ht0lt]
    have hs1 : s < t₁ := by have : (u:ℝ) < 1 := hu1; nlinarith [ht0lt]
    have hsin : s ∈ Set.Icc (0:ℝ) 1 :=
      ⟨le_of_lt (lt_of_le_of_lt ht0low hs0), le_of_lt (lt_of_lt_of_le hs1 ht1up)⟩
    have hGs := hmid s hs0 hs1
    have hγs : γ u = ρ ⟨s, hsin⟩ := by
      show ρ (Set.projIcc 0 1 h01 (t₀ + (u:ℝ) * (t₁ - t₀))) = ρ ⟨s, hsin⟩
      rw [proj_eq s hsin]
    have h2 : (ρ ⟨s, hsin⟩).2 = G s := by
      rw [show G s = (ρ (Set.projIcc 0 1 h01 s)).2 from rfl, proj_eq s hsin]
    refine ⟨?_, ?_, ?_⟩
    · rw [hγs, h2]; exact hGs.1
    · rw [hγs, h2]; exact hGs.2
    · rw [hγs]; exact hρF ⟨s, hsin⟩

theorem strip_crosscut_bounded_away
    (F : Set (ℝ × ℝ))
    (hF : IsClosed (F ∪ {z : ℝ × ℝ | z.2 ≤ 0 ∨ 1 ≤ z.2}))
    (hstrip : F ⊆ {z : ℝ × ℝ | 0 < z.2 ∧ z.2 < 1})
    (haway : Disjoint (closure F) {z : ℝ × ℝ | z.2 ≤ 0 ∨ 1 ≤ z.2})
    (hbdd : ∀ z : ℝ × ℝ, z ∈ F →
      Bornology.IsBounded (Prod.fst '' (connectedComponentIn F z))) :
    ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
      (γ 0).2 = 0 ∧ (γ 1).2 = 1 ∧
      (∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → (t : ℝ) < 1 →
        0 < (γ t).2 ∧ (γ t).2 < 1 ∧ γ t ∉ F) := by
  set B : Set (ℝ × ℝ) := {z : ℝ × ℝ | z.2 ≤ 0 ∨ 1 ≤ z.2} with hBdef
  -- `F` is closed
  have hclsub : closure F ⊆ F ∪ B := closure_minimal (Set.subset_union_left) hF
  have hclB : closure F ∩ B = ∅ := Set.disjoint_iff_inter_eq_empty.mp haway
  have hFsub : closure F ⊆ F := by
    intro z hz
    rcases hclsub hz with h | h
    · exact h
    · exact absurd (hclB ▸ (⟨hz, h⟩ : z ∈ closure F ∩ B)) (Set.notMem_empty z)
  have hcleq : closure F = F := Set.Subset.antisymm hFsub subset_closure
  have hFclosed : IsClosed F := hcleq ▸ isClosed_closure
  -- it suffices to join the points `(0,-1)` and `(0,2)` inside the complement
  have hjoined : JoinedIn Fᶜ (((0:ℝ),(-1:ℝ)) : ℝ × ℝ) (((0:ℝ),(2:ℝ)) : ℝ × ℝ) := by
    by_contra hsep
    set F' : Set ℂ := toC '' F with hF'def
    have hF'closed : IsClosed F' := by
      rw [hF'def]; exact Homeomorph.isClosedMap toC F hFclosed
    have ha : toC (((0:ℝ),(-1:ℝ)) : ℝ × ℝ) ∉ F' := by
      intro hmem
      rw [hF'def] at hmem
      obtain ⟨z, hzF, hza⟩ := hmem
      have h1 : z = (((0:ℝ),(-1:ℝ)) : ℝ × ℝ) := toC.injective hza
      rw [h1] at hzF
      have h2 := (hstrip hzF).1
      linarith
    have hb : toC (((0:ℝ),(2:ℝ)) : ℝ × ℝ) ∉ F' := by
      intro hmem
      rw [hF'def] at hmem
      obtain ⟨z, hzF, hza⟩ := hmem
      have h1 : z = (((0:ℝ),(2:ℝ)) : ℝ × ℝ) := toC.injective hza
      rw [h1] at hzF
      have h2 := (hstrip hzF).2
      linarith
    have hsep' : ¬ ∃ p : Path (toC (((0:ℝ),(-1:ℝ)) : ℝ × ℝ))
        (toC (((0:ℝ),(2:ℝ)) : ℝ × ℝ)), ∀ t, p t ∉ F' := by
      rintro ⟨p, hp⟩
      apply hsep
      refine ⟨(p.map toC.symm.continuous).cast ?_ ?_, fun t => ?_⟩
      · exact (toC.symm_apply_apply _).symm
      · exact (toC.symm_apply_apply _).symm
      · rw [Path.cast_coe, Path.map_coe]
        intro hmem
        exact hp t (by
          rw [hF'def]
          exact ⟨toC.symm (p t), hmem, toC.apply_symm_apply (p t)⟩)
    obtain ⟨S', hS'sub, hS'cl, hS'pre, hS'sep⟩ :=
      Commons.Topology.Jordan.closed_separates_continuum hF'closed ha hb hsep'
    -- pull the separating continuum back to `ℝ × ℝ`
    set S : Set (ℝ × ℝ) := toC.symm '' S' with hSdef
    have hSsub' : S' ⊆ toC '' F := by rw [← hF'def]; exact hS'sub
    have hSsub : S ⊆ F := by
      intro z hz
      rw [hSdef] at hz
      obtain ⟨w, hwS', rfl⟩ := hz
      obtain ⟨v, hvF, hvw⟩ := hSsub' hwS'
      have hvw' : toC.symm w = v := by rw [← hvw, toC.symm_apply_apply]
      rw [hvw']; exact hvF
    have hScl : IsClosed S := by
      rw [hSdef]; exact Homeomorph.isClosedMap toC.symm S' hS'cl
    have hSpre : IsPreconnected S := by
      rw [hSdef]; exact hS'pre.image toC.symm (toC.symm.continuous.continuousOn)
    have hS'ne : S'.Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      refine hS'sep ?_
      rw [hne]
      have hJ : JoinedIn (Set.univ : Set ℂ) (toC (((0:ℝ),(-1:ℝ)) : ℝ × ℝ))
          (toC (((0:ℝ),(2:ℝ)) : ℝ × ℝ)) :=
        JoinedIn.of_segment_subset (Set.subset_univ _)
      exact ⟨hJ.somePath, fun t => Set.notMem_empty _⟩
    obtain ⟨z₀, hz₀S⟩ := hS'ne.image toC.symm
    have hz₀F : z₀ ∈ F := hSsub hz₀S
    have hSsubcc : S ⊆ connectedComponentIn F z₀ :=
      hSpre.subset_connectedComponentIn hz₀S hSsub
    have hbdd_fst : Bornology.IsBounded (Prod.fst '' S) :=
      (hbdd z₀ hz₀F).subset (Set.image_mono hSsubcc)
    obtain ⟨M₁, hM₁⟩ := isBounded_iff_forall_norm_le.mp hbdd_fst
    set R : ℝ := max M₁ 1 with hRdef
    have hR1 : (1:ℝ) ≤ R := by rw [hRdef]; exact le_max_right _ _
    have hnorm : ∀ w ∈ S, ‖w‖ ≤ R := by
      intro w hw
      rw [Prod.norm_def, hRdef]
      refine max_le (le_trans (hM₁ w.1 ⟨w, hw, rfl⟩) (le_max_left _ _)) ?_
      have h := hstrip (hSsub hw)
      refine le_trans ?_ (le_max_right _ _)
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    have hS'eq : S' = toC '' S := by
      rw [hSdef]
      ext w
      constructor
      · intro hw
        exact ⟨toC.symm w, ⟨w, hw, rfl⟩, toC.apply_symm_apply w⟩
      · rintro ⟨z, ⟨w', hw', hz'⟩, hzw⟩
        have hww : w = w' := by rw [← hzw, ← hz', toC.apply_symm_apply]
        rw [hww]; exact hw'
    -- the rectangular bounds on `S'` used to route around it
    have hTbound : ∀ w ∈ S', -R ≤ w.re ∧ w.re ≤ R ∧ 0 ≤ w.im ∧ w.im ≤ 1 := by
      intro w hw
      rw [hS'eq] at hw
      obtain ⟨z, hzS, hzw⟩ := hw
      have hzn := hnorm z hzS
      have hz1 : |z.1| ≤ R := by
        have h := le_max_left ‖z.1‖ ‖z.2‖
        rw [← Prod.norm_def] at h
        rw [Real.norm_eq_abs] at h
        linarith
      have hzs := hstrip (hSsub hzS)
      rw [← hzw, toC_re, toC_im]
      exact ⟨by nlinarith [neg_abs_le z.1, hz1], by linarith [le_abs_self z.1, hz1],
        le_of_lt hzs.1, le_of_lt hzs.2⟩
    have hjoin' : JoinedIn S'ᶜ (toC (((0:ℝ),(-1:ℝ)) : ℝ × ℝ))
        (toC (((0:ℝ),(2:ℝ)) : ℝ × ℝ)) :=
      joinedIn_compl_of_re_im_bounds_vert (α := -R) (β := R) (c := 0) (d := 1)
        hTbound (by rw [toC_im]; norm_num) (by rw [toC_im]; norm_num)
    exact hS'sep hjoin'
  obtain ⟨ρ, hρ⟩ := hjoined
  exact crosscut_of_path F ρ.toContinuousMap
    (by rw [Path.coe_toContinuousMap]; exact ρ.source)
    (by rw [Path.coe_toContinuousMap]; exact ρ.target)
    (fun t => by rw [Path.coe_toContinuousMap]; exact hρ t)


end

end Commons.Topology.Strip
