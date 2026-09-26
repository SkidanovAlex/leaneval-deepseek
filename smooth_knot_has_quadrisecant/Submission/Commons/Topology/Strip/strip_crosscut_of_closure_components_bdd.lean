import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Commons.Topology.Jordan.closed_separates_continuum

namespace Commons.Topology.Strip

open Set

noncomputable section

/-- The real-linear homeomorphism `ℝ × ℝ ≃ₜ ℂ`, `(x,y) ↦ x + y·I`. -/
private def scbToC : (ℝ × ℝ) ≃ₜ ℂ := Complex.equivRealProdCLM.toHomeomorph.symm

private lemma scbToC_apply (q : ℝ × ℝ) : scbToC q = (q.1 : ℂ) + (q.2 : ℂ) * Complex.I := by
  simp [scbToC, Complex.equivRealProdCLM_symm_apply]

/-- Transport of the irreducible-cut theorem to `ℝ × ℝ`: a closed subset of the plane separating
two points contains a closed preconnected subset separating them. -/
private theorem separates_continuum_of_closed {K : Set (ℝ × ℝ)} (hK : IsClosed K) {a b : ℝ × ℝ}
    (ha : a ∉ K) (hb : b ∉ K)
    (hsep : ¬ ∃ p : Path a b, ∀ t, p t ∉ K) :
    ∃ S : Set (ℝ × ℝ), S ⊆ K ∧ IsClosed S ∧ IsPreconnected S ∧
      ¬ ∃ p : Path a b, ∀ t, p t ∉ S := by
  have hK' : IsClosed (scbToC '' K) := (Homeomorph.isClosedMap scbToC) K hK
  have hsep' : ¬ ∃ p : Path (scbToC a) (scbToC b), ∀ t, p t ∉ scbToC '' K := by
    rintro ⟨p, hp⟩
    refine hsep ⟨(p.map (f := scbToC.symm) scbToC.symm.continuous).cast
      (scbToC.symm_apply_apply a).symm (scbToC.symm_apply_apply b).symm, fun t => ?_⟩
    rw [Path.cast_coe, Path.map_coe]
    intro hmem
    exact hp t ⟨scbToC.symm (p t), hmem, scbToC.apply_symm_apply (p t)⟩
  have ha' : scbToC a ∉ scbToC '' K := by rintro ⟨k, hk, h⟩; exact ha (scbToC.injective h ▸ hk)
  have hb' : scbToC b ∉ scbToC '' K := by rintro ⟨k, hk, h⟩; exact hb (scbToC.injective h ▸ hk)
  obtain ⟨S', hS'K, hS'cl, hS'pc, hS'sep⟩ :=
    Commons.Topology.Jordan.closed_separates_continuum hK' ha' hb' hsep'
  refine ⟨scbToC.symm '' S', ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    obtain ⟨k, hk, hk'⟩ := hS'K hs
    rw [← hk', scbToC.symm_apply_apply]; exact hk
  · exact (Homeomorph.isClosedMap scbToC.symm) S' hS'cl
  · exact hS'pc.image scbToC.symm scbToC.symm.continuous.continuousOn
  · rintro ⟨p, hp⟩
    refine hS'sep ⟨p.map (f := scbToC) scbToC.continuous, fun t => ?_⟩
    rw [Path.map_coe]
    intro hmem
    exact hp t ⟨scbToC (p t), hmem, scbToC.symm_apply_apply (p t)⟩

/-- The straight-line path between two points of `ℝ × ℝ`. -/
private noncomputable def segPath (x y : ℝ × ℝ) : Path x y where
  toFun := fun t => (1 - (t:ℝ)) • x + (t:ℝ) • y
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

private lemma segPath_fst (x y : ℝ × ℝ) (t : Set.Icc (0:ℝ) 1) :
    (segPath x y t).1 = (1 - (t:ℝ)) * x.1 + (t:ℝ) * y.1 := by
  simp [segPath]

private lemma segPath_snd (x y : ℝ × ℝ) (t : Set.Icc (0:ℝ) 1) :
    (segPath x y t).2 = (1 - (t:ℝ)) * x.2 + (t:ℝ) * y.2 := by
  simp [segPath]

/-- **No compact subset of the closed strip separates `(0,-1)` from `(0,2)`.**  Since such a set is
contained in `[−R,R] × [0,1]` one can route around it: go right, up, and back left. -/
private theorem exists_path_avoiding_compact_of_strip
    {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (hsubS : S ⊆ {z : ℝ × ℝ | 0 ≤ z.2 ∧ z.2 ≤ 1}) :
    ∃ p : Path ((0:ℝ),(-1:ℝ)) ((0:ℝ),(2:ℝ)), ∀ t, p t ∉ S := by
  obtain ⟨M, hM⟩ := (hS.image continuous_fst).bddAbove
  have hM' : ∀ z ∈ S, z.1 ≤ M := fun z hz => hM ⟨z, hz, rfl⟩
  obtain ⟨R, hRx⟩ : ∃ R : ℝ, ∀ z ∈ S, z.1 < R :=
    ⟨M + 1, fun z hz => by have := hM' z hz; linarith⟩
  let p : Path ((0:ℝ),(-1:ℝ)) ((0:ℝ),(2:ℝ)) :=
    (segPath ((0:ℝ),(-1:ℝ)) (R,(-1:ℝ))).trans
      ((segPath (R,(-1:ℝ)) (R,(2:ℝ))).trans (segPath (R,(2:ℝ)) ((0:ℝ),(2:ℝ))))
  have hr : Set.range p = Set.range (segPath ((0:ℝ),(-1:ℝ)) (R,(-1:ℝ))) ∪
      (Set.range (segPath (R,(-1:ℝ)) (R,(2:ℝ))) ∪
        Set.range (segPath (R,(2:ℝ)) ((0:ℝ),(2:ℝ)))) := by
    simp only [p]
    rw [Path.trans_range, Path.trans_range]
  refine ⟨p, ?_⟩
  rintro t ht
  have hmem : p t ∈ Set.range p := ⟨t, rfl⟩
  rw [hr] at hmem
  rcases hmem with h | h | h
  · obtain ⟨s, hs⟩ := h
    have hz : (p t).2 = (-1:ℝ) := by
      have : (p t).2 = (segPath ((0:ℝ),(-1:ℝ)) (R,(-1:ℝ)) s).2 := by rw [← hs]
      rw [this, segPath_snd]; ring
    have h0 := (hsubS ht).1
    linarith
  · obtain ⟨s, hs⟩ := h
    have hz : (p t).1 = R := by
      have : (p t).1 = (segPath (R,(-1:ℝ)) (R,(2:ℝ)) s).1 := by rw [← hs]
      rw [this, segPath_fst]; ring
    have hlt := hRx (p t) ht
    linarith
  · obtain ⟨s, hs⟩ := h
    have hz : (p t).2 = (2:ℝ) := by
      have : (p t).2 = (segPath (R,(2:ℝ)) ((0:ℝ),(2:ℝ)) s).2 := by rw [← hs]
      rw [this, segPath_snd]; ring
    have h1 := (hsubS ht).2
    linarith

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

theorem strip_crosscut_of_closure_components_bdd
    (F : Set (ℝ × ℝ))
    (hsub : F ⊆ {z : ℝ × ℝ | 0 < z.2 ∧ z.2 < 1})
    (hbdd : ∀ z : ℝ × ℝ, z ∈ closure F →
      Bornology.IsBounded (Prod.fst '' (connectedComponentIn (closure F) z))) :
    ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
      (γ 0).2 = 0 ∧ (γ 1).2 = 1 ∧
      (∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → (t : ℝ) < 1 →
        0 < (γ t).2 ∧ (γ t).2 < 1 ∧ γ t ∉ closure F) := by
  let K : Set (ℝ × ℝ) := closure F
  have hKcl : IsClosed K := isClosed_closure
  have hclosed : IsClosed {z : ℝ × ℝ | 0 ≤ z.2 ∧ z.2 ≤ 1} :=
    isClosed_Icc.preimage continuous_snd
  have hKsub : K ⊆ {z : ℝ × ℝ | 0 ≤ z.2 ∧ z.2 ≤ 1} :=
    closure_minimal (fun z hz => ⟨(hsub hz).1.le, (hsub hz).2.le⟩) hclosed
  have ha : ((0:ℝ),(-1:ℝ)) ∉ K := by
    intro h
    have hh := hKsub h
    norm_num at hh
  have hb : ((0:ℝ),(2:ℝ)) ∉ K := by
    intro h
    have hh := hKsub h
    norm_num at hh
  have hpath : ∃ p : Path ((0:ℝ),(-1:ℝ)) ((0:ℝ),(2:ℝ)), ∀ t, p t ∉ K := by
    by_contra hsep
    obtain ⟨S, hSK, hScl, hSpc, hSsep⟩ := separates_continuum_of_closed hKcl ha hb hsep
    have hSne : S.Nonempty := by
      rcases S.eq_empty_or_nonempty with h | h
      · exfalso
        refine hSsep ⟨segPath ((0:ℝ),(-1:ℝ)) ((0:ℝ),(2:ℝ)), ?_⟩
        intro t
        rw [h]
        exact Set.notMem_empty _
      · exact h
    obtain ⟨z₀, hz₀⟩ := hSne
    have hScc : S ⊆ connectedComponentIn K z₀ := hSpc.subset_connectedComponentIn hz₀ hSK
    have hbounded : Bornology.IsBounded (Prod.fst '' S) :=
      (hbdd z₀ (hSK hz₀)).subset (Set.image_mono hScc)
    have hSstrip : S ⊆ {z : ℝ × ℝ | 0 ≤ z.2 ∧ z.2 ≤ 1} := hSK.trans hKsub
    have hScpt : IsCompact S := by
      obtain ⟨r, hr⟩ := hbounded.subset_closedBall (0:ℝ)
      have hbox : IsCompact (Set.Icc (-r) r ×ˢ Set.Icc (0:ℝ) 1) :=
        isCompact_Icc.prod isCompact_Icc
      refine hbox.of_isClosed_subset hScl ?_
      intro z hz
      constructor
      · have hh := hr ⟨z, hz, rfl⟩
        rw [Metric.mem_closedBall, dist_zero_right] at hh
        simp only [Real.norm_eq_abs] at hh
        exact abs_le.mp hh
      · exact hSstrip hz
    obtain ⟨p, hp⟩ := exists_path_avoiding_compact_of_strip hScpt hSstrip
    exact hSsep ⟨p, hp⟩
  obtain ⟨p, hp⟩ := hpath
  exact crosscut_of_path (closure F) p.toContinuousMap
    (by rw [Path.coe_toContinuousMap]; exact p.source)
    (by rw [Path.coe_toContinuousMap]; exact p.target)
    (fun t => by rw [Path.coe_toContinuousMap]; exact hp t)

end

end Commons.Topology.Strip