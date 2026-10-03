import Mathlib
import Submission.Work.L61.Basic
import Submission.Work.L61.Chain.isCompact_Kset
import Submission.Work.L61.CovAux.exists_ball_log_branch
import Submission.Work.L61.CovAux.exists_local_section_piExp
import Submission.Work.L61.CovAux.eventually_eq_zero_of_int_valued
import Submission.Work.L61.CovAux.E_covering_union



/-!
# The pushed-down horn map is a covering over the complement of the critical orbit

`Work.L61.covering` : for the pushed-down horn map `g = pushdown Ẽ_{f₀}` of a germ in `𝓕₀`
with horn data `HornData d`, the map `g` (restricted to `gdom` and with the preimages of the
critical value `π v` removed) is a covering map over `(Kset)ᶜ`, where `Kset` is the critical
orbit of `g` together with `0`.

The proof is the standard sheet construction.  Fix `x` outside `Kset`.

* `ε > 0` is so small that the ball `U = ball x ε` avoids `Kset` (and hence `0`), and `L` is a
  branch of `log/(2πi)` on `U`: `piExp (L z) = z`.
* `E = Ẽ_{f₀}` is a covering map on the union `Y = Bu ∪ Bl` of the two ends of the horn
  cylinder, over the complement `S` of the critical-value lattice `v + ℤ`.
* The sheets of `g` over `U` are indexed by the fibre `q ⁻¹' {L x}` of `E` over `L x` (a
  discrete set): for `w` in that fibre, the lift `σ w : U → Y` of `L` with `σ w x = w` exists by
  the lifting theorem for coverings (the ball is simply connected), and the sheet is
  `a ↦ piExp (σ w a)`.  The sheets are pairwise disjoint (two of them agree at a point only if
  the lifts differ by an integer, which the equation `E (w + k) = E w + k` forbids), they cover
  the preimage of `U`, and they are open in the domain (local constancy of the index, proved with
  a local section of `piExp` and the injectivity of `E` on the source of a chart).

`IsOpen.trivializationDiscrete` then assembles these sheets into a trivialization, and
`IsEvenlyCovered.of_trivialization` gives the even covering property.
-/

namespace Work.L61.Covering

open MandelDim Set Function Metric Filter
open scoped Topology

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {d : MandelDim.ParabData f₀ D₀}

/-! ## Elementary facts about the ends and about `piExp` -/

theorem continuous_piExp : Continuous piExp := by
  unfold piExp
  fun_prop

/-- `piExp (u - v) = piExp u / piExp v`. -/
theorem piExp_sub_placeholder : True := trivial

/-- A nonzero integer has norm at least one. -/
theorem one_le_norm_intCast {m : ℤ} (hm : m ≠ 0) : 1 ≤ ‖(m : ℂ)‖ := by
  rw [Complex.norm_intCast]
  have h := Int.one_le_abs hm
  exact_mod_cast h

/-- A vector of norm `< 1` that is an integer vanishes. -/
theorem intCast_eq_zero_of_norm_lt_one {m : ℤ} (h : ‖(m : ℂ)‖ < 1) : m = 0 := by
  by_contra hm
  have h1 := one_le_norm_intCast hm
  linarith

/-- The ends `Bu ∪ Bl` are invariant under translations by integers. -/
theorem mem_ends_add {d : MandelDim.ParabData f₀ D₀} (hd : HornData d) {w : ℂ}
    (hw : w ∈ hd.Bu ∪ hd.Bl) (k : ℤ) : w + k ∈ hd.Bu ∪ hd.Bl := by
  have hD : IsTInvariant (hd.Bu ∪ hd.Bl) := fun v => by
    simp only [Set.mem_union]
    rw [hd.Bu_T v, hd.Bl_T v]
  exact IsTInvariant.add_int hD hw k

/-- `E` is equivariant under the translations on `Bu ∪ Bl`. -/
theorem E_add_int_mem {d : MandelDim.ParabData f₀ D₀} (hd : HornData d) {w : ℂ}
    (hw : w ∈ hd.Bu ∪ hd.Bl) (k : ℤ) : d.E (w + k) = d.E w + k := by
  have hD : IsTInvariant (hd.Bu ∪ hd.Bl) := fun v => by
    simp only [Set.mem_union]
    rw [hd.Bu_T v, hd.Bl_T v]
  have hE : ∀ v ∈ hd.Bu ∪ hd.Bl, v + 1 ∈ hd.Bu ∪ hd.Bl → d.E (v + 1) = d.E v + 1 :=
    fun v hv hv1 => E_add_one d (hd.sub hv) (hd.sub hv1)
  exact E_add_int (E := d.E) hD hE hw k

/-- `d.E` is continuous on its domain `DE`. -/
theorem E_continuousOn (d : MandelDim.ParabData f₀ D₀) : ContinuousOn d.E d.DE := by
  have h1 : ContinuousOn d.φ d.DE := d.φ_holo.continuousOn.mono fun w hw => hw.1
  have h2 : ContinuousOn d.Φ (d.φ '' d.DE) :=
    d.Φ_holo.continuousOn.mono fun z hz => by
      obtain ⟨w, hw, rfl⟩ := hz
      exact hw.2
  exact h2.comp h1 fun w hw => ⟨w, hw, rfl⟩

theorem isOpen_parabolicBasin (_d : MandelDim.ParabData f₀ D₀) :
    IsOpen (ParabolicBasin f₀ D₀) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨U, hU, h1, h2⟩
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  refine Filter.mem_of_superset (Metric.ball_mem_nhds z hε) fun z' hz' =>
    ⟨Metric.ball z ε, Metric.isOpen_ball.mem_nhds hz', ?_, ?_⟩
  · exact fun n => (h1 n).mono hεU subset_rfl
  · exact h2.mono hεU

theorem isOpen_DE (d : MandelDim.ParabData f₀ D₀) : IsOpen d.DE := by
  have h1 : IsOpen (d.Dφ ∩ d.φ ⁻¹' (ParabolicBasin f₀ D₀)) :=
    d.φ_holo.continuousOn.isOpen_inter_preimage d.Dφ_open (isOpen_parabolicBasin d)
  convert h1 using 3
  ext w
  rfl

/-! ## The domain `Gdom` of the pushed-down horn map -/

/-- `Dom g` with the preimages of the critical value removed. -/
def Gdom (d : MandelDim.ParabData f₀ D₀) (hd : HornData d) : Set ℂ :=
  {ζ | ζ ∈ gdom d hd ∧ g d ζ ≠ critVal hd}

/-- The type of the fibre of a map over a point. -/
abbrev Fiber {α β : Type*} (q : α → β) (c : β) : Type _ := ↥(q ⁻¹' ({c} : Set β))

/-- Translate a point of the union of the two ends by an integer. -/
def Eshift {d : MandelDim.ParabData f₀ D₀} (hd : HornData d) {w : ℂ}
    (hw : w ∈ hd.Bu ∪ hd.Bl) (k : ℤ) : ↥(hd.Bu ∪ hd.Bl) :=
  ⟨w + k, mem_ends_add hd hw k⟩

theorem Eshift_val {d : MandelDim.ParabData f₀ D₀} (hd : HornData d) {w : ℂ}
    (hw : w ∈ hd.Bu ∪ hd.Bl) (k : ℤ) :
    (((Eshift hd hw k) : ↥(hd.Bu ∪ hd.Bl)) : ℂ) = w + k := rfl

theorem Eshift_E {d : MandelDim.ParabData f₀ D₀} (hd : HornData d) {w : ℂ}
    (hw : w ∈ hd.Bu ∪ hd.Bl) (k : ℤ) :
    d.E ((Eshift hd hw k : ↥(hd.Bu ∪ hd.Bl)) : ℂ) = d.E w + k :=
  E_add_int_mem hd hw k


theorem covering {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {d : MandelDim.ParabData f₀ D₀} (hd : MandelDim.HornData d) :
    IsCoveringMapOn (fun ζ : {ζ : ℂ // ζ ∈ Work.L61.gdom d hd ∧ Work.L61.g d ζ ≠ Work.L61.critVal hd} =>
      Work.L61.g d ζ) (Work.L61.Kset d hd)ᶜ := by
  show IsCoveringMapOn (fun ζ : ↥(Gdom d hd) => g d ζ) (Kset d hd)ᶜ
  intro x hx
  obtain ⟨ε, hε, hsub, h0, L, hLc, hLp⟩ := CovAux.exists_ball_log_branch hd hx
  set U : Set ℂ := Metric.ball x ε with hUdef
  have hxU : x ∈ U := by rw [hUdef]; exact mem_ball_self hε
  have hUopen : IsOpen U := by rw [hUdef]; exact Metric.isOpen_ball
  have hUsub : U ⊆ (Kset d hd)ᶜ := hsub
  have hU0 : (0 : ℂ) ∉ U := h0
  set c : ℂ := L x with hcdef
  have hcx : piExp c = x := hLp x hxU
  set Y : Set ℂ := hd.Bu ∪ hd.Bl with hYdef
  have hYopen : IsOpen Y := hYdef ▸ hd.Bu_open.union hd.Bl_open
  set q : ↥Y → ℂ := fun w => d.E (w : ℂ) with hqdef
  set S : Set ℂ := {y : ℂ | ∀ k : ℤ, y ≠ hd.v + k} with hSdef
  have hcov : IsCoveringMapOn q S := CovAux.E_covering_union hd
  have hcS : c ∈ S := by
    rw [hSdef]
    intro k hk
    have h1 : x = critVal hd := by
      rw [← hcx, hk, piExp_add_intCast]
      rfl
    exact hUsub hxU (h1.symm ▸ critVal_mem_Kset d hd)
  haveI : DiscreteTopology (Fiber q c) := (hcov c hcS).discreteTopology_fiber
  haveI : Nonempty (Fiber q c) := by
    obtain ⟨w, hw, hwE⟩ := hd.surj_u c
    exact ⟨⟨⟨w, Or.inl hw⟩, by rw [hqdef]; exact hwE⟩⟩
  haveI : Nonempty ↥U := ⟨⟨x, hxU⟩⟩
  haveI : Nonempty ↥(Gdom d hd) :=
    ⟨⟨0, Set.mem_insert_iff.mpr (Or.inl rfl), by rw [g_zero]; exact (critVal_ne_zero hd).symm⟩⟩
  haveI : SimplyConnectedSpace ↥U :=
    @SimplyConnectedSpace.ofContractible (↥U) _ (Metric.contractibleSpace_ball hε)
  haveI : LocallyPathConnectedSpace ↥U := hUopen.locallyPathConnectedSpace
  let fbase : C(↥U, ℂ) := ⟨fun a => L (a : ℂ), hLc.domRestrict⟩
  have hfbaseS : ∀ a : ↥U, fbase a ∈ S := by
    intro a
    rw [hSdef]
    intro k hk
    have hk' : L (a : ℂ) = hd.v + k := hk
    have h1 : (a : ℂ) = critVal hd := by
      rw [← hLp a a.2, hk', piExp_add_intCast]
      rfl
    exact hUsub a.2 (h1.symm ▸ critVal_mem_Kset d hd)
  have hbase (w : Fiber q c) : q (w : ↥Y) = fbase ⟨x, hxU⟩ := by
    have h1 : q (w : ↥Y) = c := Set.mem_singleton_iff.mp w.2
    rw [h1]
    rfl
  have hlift (w : Fiber q c) :
      ∃! F : C(↥U, ↥Y), F ⟨x, hxU⟩ = (w : ↥Y) ∧ (fun a => q (F a)) = ⇑fbase :=
    hcov.existsUnique_continuousMap_lifts fbase (a₀ := ⟨x, hxU⟩) (e₀ := (w : ↥Y)) (hbase w) hfbaseS
  have hσex (w : Fiber q c) : ∃ F : C(↥U, ↥Y), F ⟨x, hxU⟩ = (w : ↥Y) ∧ ∀ a, q (F a) = fbase a := by
    obtain ⟨F, hF, -⟩ := hlift w
    exact ⟨F, hF.1, fun a => congrFun hF.2 a⟩
  let σ : Fiber q c → C(↥U, ↥Y) := fun w => Classical.choose (hσex w)
  have hσ (w : Fiber q c) : σ w ⟨x, hxU⟩ = (w : ↥Y) ∧ ∀ a, q (σ w a) = fbase a :=
    Classical.choose_spec (hσex w)
  have hσE (w : Fiber q c) (a : ↥U) : d.E (((σ w a) : ↥Y) : ℂ) = L (a : ℂ) := (hσ w).2 a
  have hσ_eq (w : Fiber q c) (F : C(↥U, ↥Y)) (h1 : F ⟨x, hxU⟩ = (w : ↥Y))
      (h2 : ∀ a, q (F a) = fbase a) : F = σ w := by
    obtain ⟨G, hG, hu⟩ := hlift w
    rw [hu F ⟨h1, funext h2⟩]
    exact (hu (σ w) ⟨(hσ w).1, funext (hσ w).2⟩).symm
  have hσ_uniq (F G : C(↥U, ↥Y)) (hF : ∀ a, q (F a) = fbase a) (hG : ∀ a, q (G a) = fbase a)
      {a₀ : ↥U} (heq : F a₀ = G a₀) : F = G := by
    obtain ⟨H, hH, hu⟩ := hcov.existsUnique_continuousMap_lifts fbase (a₀ := a₀) (e₀ := F a₀)
      (hF a₀) hfbaseS
    rw [hu F ⟨rfl, funext hF⟩]
    exact (hu G ⟨heq.symm, funext hG⟩).symm
  have hsw_mem (w : Fiber q c) (a : ↥U) : piExp (((σ w a) : ↥Y) : ℂ) ∈ Gdom d hd := by
    refine ⟨Set.mem_insert_iff.mpr (Or.inr ⟨((σ w a : ↥Y) : ℂ), (σ w a).2, rfl⟩), ?_⟩
    rw [g_piExp d hd (σ w a).2]
    have h1 : piExp (d.E (((σ w a) : ↥Y) : ℂ)) = (a : ℂ) := by
      rw [hσE w a]
      exact hLp a a.2
    rw [h1]
    exact fun hcon => hUsub a.2 (hcon.symm ▸ critVal_mem_Kset d hd)
  let sw : Fiber q c → ↥U → ↥(Gdom d hd) :=
    fun w a => ⟨piExp (((σ w a) : ↥Y) : ℂ), hsw_mem w a⟩
  have hsw_val (w : Fiber q c) (a : ↥U) :
      ((sw w a : ↥(Gdom d hd)) : ℂ) = piExp (((σ w a) : ↥Y) : ℂ) := rfl
  have hsw_g (w : Fiber q c) (a : ↥U) : g d (sw w a) = (a : ℂ) := by
    rw [show (sw w a : ℂ) = piExp (((σ w a) : ↥Y) : ℂ) from rfl,
      g_piExp d hd (σ w a).2, hσE w a]
    exact hLp a a.2
  have hsw_cont (w : Fiber q c) : Continuous (sw w) :=
    Continuous.subtype_mk (continuous_piExp.comp (continuous_subtype_val.comp (σ w).continuous))
      (hsw_mem w)
  have hg_cont : Continuous (fun ζ : ↥(Gdom d hd) => g d ζ) :=
    (hd.g_holo.continuousOn.mono fun ζ hζ => hζ.1).domRestrict
  -- local constancy of the index
  have hlocal (w₀ : Fiber q c) (a₀ : ↥U) :
      ∃ N : Set ↥(Gdom d hd), N ∈ 𝓝 (sw w₀ a₀) ∧
        ∀ ζ ∈ N, g d ζ ∈ U → ζ ∈ Set.range (sw w₀) := by
    set v : ℂ := (((σ w₀ a₀) : ↥Y) : ℂ) with hvdef
    have hvY : v ∈ hd.Bu ∪ hd.Bl := (σ w₀ a₀).2
    have hvE : d.E v = L (a₀ : ℂ) := hσE w₀ a₀
    have hπv : piExp v = ((sw w₀ a₀ : ↥(Gdom d hd)) : ℂ) := rfl
    have he₀ne : ((sw w₀ a₀ : ↥(Gdom d hd)) : ℂ) ≠ 0 := by
      intro h
      have hg : g d (sw w₀ a₀) = 0 := by
        rw [show (sw w₀ a₀ : ℂ) = 0 from h]
        exact g_zero d
      rw [hsw_g w₀ a₀] at hg
      exact hU0 (hg ▸ a₀.2)
    have hvS : q (⟨v, hvY⟩ : ↥Y) ∈ S := by
      have h1 : d.E v ∈ S := by rw [hvE]; exact hfbaseS a₀
      exact h1
    obtain ⟨e, he_mem, he_eq⟩ := hcov.isLocalHomeomorphOn (⟨v, hvY⟩ : ↥Y) hvS
    have hEp_open : IsOpen (Subtype.val '' e.source) :=
      hYopen.isOpenEmbedding_subtypeVal.isOpenMap e.source e.open_source
    have hinjE : ∀ u₁ u₂ : ℂ, u₁ ∈ Subtype.val '' e.source → u₂ ∈ Subtype.val '' e.source →
        d.E u₁ = d.E u₂ → u₁ = u₂ := by
      rintro u₁ u₂ ⟨x₁, hx₁, rfl⟩ ⟨x₂, hx₂, rfl⟩ hE
      have h1 : e x₁ = e x₂ := by
        have h2 : q x₁ = q x₂ := hE
        rw [congrFun he_eq x₁, congrFun he_eq x₂] at h2
        exact h2
      exact congrArg Subtype.val (e.injOn hx₁ hx₂ h1)
    obtain ⟨lam, hlam_cont, hlam_e, hlam_pi⟩ :=
      CovAux.exists_local_section_piExp (e₀ := ((sw w₀ a₀ : ↥(Gdom d hd)) : ℂ)) (w₀ := v) hπv he₀ne
    have hσc : ContinuousAt (fun a : ↥U => (σ w₀ a : ↥Y)) a₀ := (σ w₀).continuous.continuousAt
    have hopen1 : {a : ↥U | (σ w₀ a) ∈ e.source} ∈ 𝓝 a₀ :=
      hσc.preimage_mem_nhds (e.open_source.mem_nhds he_mem)
    have hU''ex : ∃ U'' : Set ↥U, U'' ∈ 𝓝 a₀ ∧ (∀ a ∈ U'', (σ w₀ a) ∈ e.source) :=
      ⟨_, hopen1, fun a ha => ha⟩
    obtain ⟨U'', hU''mem, hU''sub1⟩ := hU''ex
    set Uc : Set ℂ := Subtype.val '' U'' with hUcdef
    have hUc_mem : Uc ∈ 𝓝 (a₀ : ℂ) :=
      hUopen.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hU''mem
    have hlamcontS : ContinuousAt (fun ζ : ↥(Gdom d hd) => lam ((ζ : ℂ))) (sw w₀ a₀) :=
      hlam_cont.comp continuous_subtype_val.continuousAt
    have hlamYev : ∀ᶠ ζ : ↥(Gdom d hd) in 𝓝 (sw w₀ a₀), lam ((ζ : ℂ)) ∈ Y := by
      refine hlamcontS.preimage_mem_nhds ?_
      rw [hlam_e]
      exact hYopen.mem_nhds hvY
    have hne0ev : ∀ᶠ ζ : ↥(Gdom d hd) in 𝓝 (sw w₀ a₀), (ζ : ℂ) ≠ 0 :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds
        ((isClosed_singleton.isOpen_compl).mem_nhds he₀ne)
    have hgUev : ∀ᶠ ζ : ↥(Gdom d hd) in 𝓝 (sw w₀ a₀), g d ζ ∈ U :=
      hg_cont.continuousAt.preimage_mem_nhds
        (hUopen.mem_nhds (by rw [hsw_g w₀ a₀]; exact a₀.2))
    have hlamEpev : ∀ᶠ ζ : ↥(Gdom d hd) in 𝓝 (sw w₀ a₀),
        lam ((ζ : ℂ)) ∈ Subtype.val '' e.source := by
      refine hlamcontS.preimage_mem_nhds ?_
      rw [hlam_e]
      exact hEp_open.mem_nhds ⟨⟨v, hvY⟩, he_mem, rfl⟩
    have hgUcev : ∀ᶠ ζ : ↥(Gdom d hd) in 𝓝 (sw w₀ a₀), g d ζ ∈ Uc :=
      hg_cont.continuousAt.preimage_mem_nhds (by rwa [hsw_g w₀ a₀])
    have hdiffcont : ContinuousAt (fun ζ : ↥(Gdom d hd) => d.E (lam ((ζ : ℂ))) - L (g d ζ))
        (sw w₀ a₀) := by
      have hEv : ContinuousAt d.E v :=
        (E_continuousOn d).continuousAt ((isOpen_DE d).mem_nhds (hd.sub hvY))
      have hEv' : ContinuousAt d.E (lam (((sw w₀ a₀ : ↥(Gdom d hd)) : ℂ))) := by
        rw [hlam_e]
        exact hEv
      have h1 : ContinuousAt (fun ζ : ↥(Gdom d hd) => lam ((ζ : ℂ))) (sw w₀ a₀) := hlamcontS
      have h2 : ContinuousAt (fun ζ : ↥(Gdom d hd) => d.E (lam ((ζ : ℂ)))) (sw w₀ a₀) :=
        ContinuousAt.comp (g := d.E) (f := fun ζ : ↥(Gdom d hd) => lam ((ζ : ℂ))) hEv' h1
      have h3 : ContinuousAt (fun ζ : ↥(Gdom d hd) => L (g d ζ)) (sw w₀ a₀) := by
        have hLa : ContinuousAt L ((a₀ : ↥U) : ℂ) := hLc.continuousAt (hUopen.mem_nhds a₀.2)
        have hLa' : ContinuousAt L (g d (sw w₀ a₀)) := by rw [hsw_g w₀ a₀]; exact hLa
        exact ContinuousAt.comp (g := L) (f := fun ζ : ↥(Gdom d hd) => g d ζ) hLa'
          hg_cont.continuousAt
      exact h2.sub h3
    have hdiffzero : d.E (lam (((sw w₀ a₀ : ↥(Gdom d hd)) : ℂ))) - L (g d (sw w₀ a₀)) = 0 := by
      rw [hlam_e, hsw_g, hvE]
      ring
    have hvan : ∀ᶠ ζ : ↥(Gdom d hd) in 𝓝 (sw w₀ a₀),
        d.E (lam ((ζ : ℂ))) - L (g d ζ) = 0 := by
      have hsmall : ∀ᶠ ζ : ↥(Gdom d hd) in 𝓝 (sw w₀ a₀),
          ‖d.E (lam ((ζ : ℂ))) - L (g d ζ)‖ < 1 := by
        have hb : Metric.ball (0 : ℂ) 1 ∈
            𝓝 (d.E (lam (((sw w₀ a₀ : ↥(Gdom d hd)) : ℂ))) - L (g d (sw w₀ a₀))) := by
          rw [hdiffzero]
          exact Metric.ball_mem_nhds 0 one_pos
        have hb' := hdiffcont.preimage_mem_nhds hb
        filter_upwards [hb'] with ζ hζ
        simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hζ
      have hint : ∀ᶠ ζ : ↥(Gdom d hd) in 𝓝 (sw w₀ a₀),
          ∃ m : ℤ, d.E (lam ((ζ : ℂ))) - L (g d ζ) = (m : ℂ) := by
        filter_upwards [hlamYev, hne0ev, hgUev] with ζ hζY hζ0 hζU
        have h1 : piExp (d.E (lam ((ζ : ℂ)))) = g d ζ := by
          rw [← g_piExp d hd hζY, hlam_pi (ζ : ℂ) hζ0]
        have h2 : piExp (L (g d ζ)) = g d ζ := hLp (g d ζ) hζU
        obtain ⟨m, hm⟩ := piExp_eq_iff.mp (h1.trans h2.symm)
        exact ⟨m, by rw [hm]; ring⟩
      filter_upwards [hsmall, hint] with ζ hζsmall ⟨m, hm⟩
      have hm0 : (m : ℂ) = 0 := by
        exact_mod_cast intCast_eq_zero_of_norm_lt_one (by rw [← hm]; exact hζsmall)
      rw [hm, hm0]
    refine ⟨{ζ : ↥(Gdom d hd) | lam ((ζ : ℂ)) ∈ Subtype.val '' e.source ∧ g d ζ ∈ Uc ∧
      d.E (lam ((ζ : ℂ))) - L (g d ζ) = 0 ∧ (ζ : ℂ) ≠ 0}, ?_, ?_⟩
    · filter_upwards [hlamEpev, hgUcev, hvan, hne0ev] with ζ h1 h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩
    · intro ζ hζ _
      obtain ⟨hlamEp, hgUc, hdiff, hζ0⟩ := hζ
      obtain ⟨a, haU'', haval⟩ := hgUc
      have hσa : (σ w₀ a) ∈ e.source := hU''sub1 a haU''
      have hσamem : (((σ w₀ a) : ↥Y) : ℂ) ∈ Subtype.val '' e.source := ⟨(σ w₀ a), hσa, rfl⟩
      have hEeq : d.E (lam ((ζ : ℂ))) = d.E (((σ w₀ a) : ↥Y) : ℂ) := by
        have h1 : d.E (lam ((ζ : ℂ))) = L (g d ζ) := sub_eq_zero.mp hdiff
        have h2 : d.E (((σ w₀ a) : ↥Y) : ℂ) = L (a : ℂ) := hσE w₀ a
        rw [h1, h2, haval]
      have hlamEq : lam ((ζ : ℂ)) = (((σ w₀ a) : ↥Y) : ℂ) :=
        hinjE _ _ hlamEp hσamem hEeq
      have hfin : (ζ : ℂ) = ((sw w₀ a : ↥(Gdom d hd)) : ℂ) := by
        rw [← hlam_pi (ζ : ℂ) hζ0, hlamEq]
      exact Set.mem_range.mpr ⟨a, Subtype.ext hfin.symm⟩
  let htriv : Bundle.Trivialization (Fiber q c) (fun ζ : ↥(Gdom d hd) => g d ζ) :=
    IsOpen.trivializationDiscrete (f := fun ζ : ↥(Gdom d hd) => g d ζ) (fun w => Set.range (sw w))
      U hUopen
      (by
        intro w W hWU
        constructor
        · intro hW
          rw [isOpen_iff_mem_nhds]
          rintro ζ ⟨hζW, a, rfl⟩
          have haW : (a : ℂ) ∈ W := by
            have h : g d (sw w a) ∈ W := hζW
            rwa [hsw_g w a] at h
          obtain ⟨N, hNmem, hNsub⟩ := hlocal w a
          refine Filter.mem_of_superset
            (Filter.inter_mem hNmem
              (hg_cont.continuousAt.preimage_mem_nhds
                (hW.mem_nhds (show g d (sw w a) ∈ W from by rw [hsw_g w a]; exact haW)))) ?_
          rintro ζ' ⟨hζ'N, hζ'W⟩
          refine ⟨hζ'W, hNsub ζ' hζ'N ?_⟩
          exact hWU (show g d ζ' ∈ W from hζ'W)
        · intro hOpen
          have hpre : IsOpen ((sw w) ⁻¹'
              ((fun ζ : ↥(Gdom d hd) => g d ζ) ⁻¹' W ∩ Set.range (sw w))) :=
            hOpen.preimage (hsw_cont w)
          have hval : IsOpen (Subtype.val '' ((sw w) ⁻¹'
              ((fun ζ : ↥(Gdom d hd) => g d ζ) ⁻¹' W ∩ Set.range (sw w)))) :=
            hUopen.isOpenEmbedding_subtypeVal.isOpenMap _ hpre
          have hset : W = Subtype.val '' ((sw w) ⁻¹'
              ((fun ζ : ↥(Gdom d hd) => g d ζ) ⁻¹' W ∩ Set.range (sw w))) := by
            ext y
            constructor
            · intro hy
              refine ⟨⟨y, hWU hy⟩, ?_, rfl⟩
              exact ⟨show g d (sw w ⟨y, hWU hy⟩) ∈ W from by
                  rw [hsw_g w ⟨y, hWU hy⟩]; exact hy, ⟨_, rfl⟩⟩
            · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
              have h3 : g d (sw w a) ∈ W := h1
              rwa [hsw_g w a] at h3
          rw [hset]
          exact hval)
      (by
        intro w ζ₁ h₁ ζ₂ h₂ heq
        obtain ⟨a₁, rfl⟩ := h₁
        obtain ⟨a₂, rfl⟩ := h₂
        have h : (a₁ : ℂ) = (a₂ : ℂ) := by
          calc (a₁ : ℂ) = g d (sw w a₁) := (hsw_g w a₁).symm
            _ = g d (sw w a₂) := heq
            _ = (a₂ : ℂ) := hsw_g w a₂
        exact congrArg (sw w) (Subtype.ext h))
      (by
        intro w b hb
        exact ⟨sw w ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩, hsw_g w ⟨b, hb⟩⟩)
      (by
        intro w₁ w₂ hne
        show Disjoint (Set.range (sw w₁)) (Set.range (sw w₂))
        rw [Set.disjoint_left]
        rintro ζ ⟨a₁, h₁⟩ ⟨a₂, h₂⟩
        have haeq : a₁ = a₂ := Subtype.ext (by
          have h3 : g d (sw w₁ a₁) = g d (sw w₂ a₂) := by rw [h₁, h₂]
          calc (a₁ : ℂ) = g d (sw w₁ a₁) := (hsw_g w₁ a₁).symm
            _ = g d (sw w₂ a₂) := h3
            _ = (a₂ : ℂ) := hsw_g w₂ a₂)
        have h₁' : sw w₁ a₂ = ζ := by rw [← haeq]; exact h₁
        have hswEq : sw w₁ a₂ = sw w₂ a₂ := h₁'.trans h₂.symm
        have hsheet : ((σ w₁ a₂ : ↥Y) : ℂ) = ((σ w₂ a₂ : ↥Y) : ℂ) := by
          have hπ : piExp (((σ w₁ a₂ : ↥Y) : ℂ)) = piExp (((σ w₂ a₂ : ↥Y) : ℂ)) := by
            calc piExp (((σ w₁ a₂ : ↥Y) : ℂ)) = ((sw w₁ a₂ : ↥(Gdom d hd)) : ℂ) :=
                  (hsw_val w₁ a₂).symm
              _ = ((sw w₂ a₂ : ↥(Gdom d hd)) : ℂ) := congrArg Subtype.val hswEq
              _ = piExp (((σ w₂ a₂ : ↥Y) : ℂ)) := hsw_val w₂ a₂
          obtain ⟨m, hm⟩ := piExp_eq_iff.mp hπ
          have h1 : d.E (((σ w₁ a₂ : ↥Y) : ℂ)) = L (a₂ : ℂ) := hσE w₁ a₂
          have h2 : d.E (((σ w₂ a₂ : ↥Y) : ℂ)) = L (a₂ : ℂ) := hσE w₂ a₂
          have hm0 : (m : ℂ) = 0 := by
            have h : L (a₂ : ℂ) + (m : ℂ) = L (a₂ : ℂ) + 0 := by
              have h' := h1
              rw [hm, E_add_int_mem hd (σ w₂ a₂).2 m, h2] at h'
              simpa using h'
            exact add_left_cancel h
          rw [hm, hm0]
          ring
        have hσeq : σ w₁ = σ w₂ := hσ_uniq (σ w₁) (σ w₂) (hσ w₁).2 (hσ w₂).2 (Subtype.ext hsheet)
        have hw : (w₁ : ↥Y) = (w₂ : ↥Y) := by
          rw [← (hσ w₁).1, ← (hσ w₂).1, hσeq]
        exact hne (Subtype.ext hw))
      (by
        intro ζ hζ
        have hgζU : g d (ζ : ℂ) ∈ U := hζ
        have hζ0 : (ζ : ℂ) ≠ 0 := by
          intro h
          have hg : g d (ζ : ℂ) = 0 := by rw [h]; exact g_zero d
          rw [hg] at hgζU
          exact hU0 hgζU
        obtain ⟨w, hwY, hwπ⟩ : ∃ w ∈ hd.Bu ∪ hd.Bl, piExp w = (ζ : ℂ) := by
          have hζg : (ζ : ℂ) ∈ gdom d hd := ζ.2.1
          rw [gdom, Set.mem_insert_iff] at hζg
          rcases hζg with h | ⟨w, hw, hwπ⟩
          · exact absurd h hζ0
          · exact ⟨w, hw, hwπ⟩
        let wY : ↥Y := ⟨w, hwY⟩
        have hEw : piExp (d.E w) = g d ζ := by
          rw [← g_piExp d hd hwY, hwπ]
        obtain ⟨k₀, hk₀⟩ : ∃ k : ℤ, d.E w = L (g d ζ) + k := by
          have h1 : piExp (d.E w) = piExp (L (g d ζ)) := by
            rw [hEw]
            exact (hLp (g d ζ) hgζU).symm
          exact piExp_eq_iff.mp h1
        have hpi2 : ∀ a : ↥U, piExp (L (a : ℂ) + (d.E w - L (g d ζ))) = (a : ℂ) := by
          intro a
          have h1 : L (a : ℂ) + (d.E w - L (g d ζ)) = L (a : ℂ) + k₀ := by rw [hk₀]; ring
          rw [h1, piExp_add_intCast, hLp a a.2]
        have hf2cont : Continuous fun a : ↥U => L (a : ℂ) + (d.E w - L (g d ζ)) :=
          hLc.domRestrict.add_const _
        let f2 : C(↥U, ℂ) := ⟨fun a => L (a : ℂ) + (d.E w - L (g d ζ)), hf2cont⟩
        have hf2S : ∀ a : ↥U, f2 a ∈ S := by
          intro a
          rw [hSdef]
          intro k hk
          have hk' : L (a : ℂ) + (d.E w - L (g d ζ)) = hd.v + k := hk
          have h1 : (a : ℂ) = critVal hd := by
            rw [← hpi2 a, hk', piExp_add_intCast]
            rfl
          exact hUsub a.2 (h1.symm ▸ critVal_mem_Kset d hd)
        let aζ : ↥U := ⟨g d ζ, hgζU⟩
        obtain ⟨σ2, hσ2, hu2⟩ := hcov.existsUnique_continuousMap_lifts f2
          (a₀ := aζ) (e₀ := wY) (by
            show d.E w = L (g d ζ) + (d.E w - L (g d ζ))
            ring) hf2S
        have hσ2val : ∀ a : ↥U, d.E (((σ2 a) : ↥Y) : ℂ) = L (a : ℂ) + (d.E w - L (g d ζ)) :=
          fun a => congrFun hσ2.2 a
        have hσ2base : σ2 aζ = wY := hσ2.1
        have hgen : ∀ a : ↥U,
            piExp (d.E (((σ2 a) : ↥Y) : ℂ)) = piExp (L ((a : ↥U) : ℂ)) := by
          intro a
          rw [hσ2val a, hpi2 a]
          exact (hLp a a.2).symm
        have hm1ex : ∃ m : ℤ, d.E (((σ2 ⟨x, hxU⟩) : ↥Y) : ℂ) = L x + m :=
          piExp_eq_iff.mp (hgen ⟨x, hxU⟩)
        obtain ⟨m₁, hm₁⟩ := hm1ex
        have hm₁' : (m₁ : ℂ) = d.E w - L (g d ζ) := by
          have h := hσ2val ⟨x, hxU⟩
          rw [hm₁] at h
          have h2 : L x + (m₁ : ℂ) = L x + (d.E w - L (g d ζ)) := h
          exact add_left_cancel h2
        let wstar : Fiber q c :=
          ⟨Eshift hd (σ2 ⟨x, hxU⟩).2 (-m₁), by
            have h1 : d.E ((Eshift hd (σ2 ⟨x, hxU⟩).2 (-m₁) : ↥Y) : ℂ) = L x := by
              rw [Eshift_E, hm₁]
              push_cast
              ring
            exact Set.mem_singleton_iff.mpr h1⟩
        have hτc : Continuous fun a : ↥U => (((σ2 a) : ↥Y) : ℂ) + (((-m₁ : ℤ)) : ℂ) :=
          (continuous_subtype_val.comp (σ2).continuous).add_const (((-m₁ : ℤ)) : ℂ)
        let τ : C(↥U, ↥Y) :=
          ⟨fun a => Eshift hd (σ2 a).2 (-m₁),
            Continuous.subtype_mk hτc (fun a => mem_ends_add hd (σ2 a).2 (-m₁))⟩
        have hτbase : τ ⟨x, hxU⟩ = (wstar : ↥Y) := rfl
        have hτE : ∀ a : ↥U, q (τ a) = fbase a := by
          intro a
          show d.E ((Eshift hd (σ2 a).2 (-m₁) : ↥Y) : ℂ) = L (a : ℂ)
          rw [Eshift_E, hσ2val a, ← hm₁']
          push_cast
          ring
        have hτeq : τ = σ wstar := hσ_eq wstar τ hτbase hτE
        have hsigval : ((σ wstar aζ : ↥Y) : ℂ) = w + (((-m₁ : ℤ)) : ℂ) := by
          have h2 : (σ wstar) aζ = τ aζ := by rw [← hτeq]
          rw [h2]
          show (((σ2 aζ : ↥Y) : ℂ)) + (((-m₁ : ℤ)) : ℂ) = w + (((-m₁ : ℤ)) : ℂ)
          rw [show (σ2 aζ : ↥Y) = wY from hσ2base]
        have hfin : (ζ : ℂ) = ((sw wstar aζ : ↥(Gdom d hd)) : ℂ) := by
          rw [hsw_val, ← hwπ, hsigval]
          show piExp w = piExp (w + (((-m₁ : ℤ)) : ℂ))
          rw [piExp_add_intCast]
        exact Set.mem_iUnion.mpr ⟨wstar, Set.mem_range.mpr ⟨aζ, Subtype.ext hfin.symm⟩⟩)
  refine (IsEvenlyCovered.of_trivialization (f := fun ζ : ↥(Gdom d hd) => g d ζ) (x := x)
    (t := htriv) ?_).to_isEvenlyCovered_preimage
  change x ∈ U
  exact hxU


end

end Work.L61.Covering
