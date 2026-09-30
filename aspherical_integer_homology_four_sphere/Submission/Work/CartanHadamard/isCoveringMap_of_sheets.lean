import Mathlib
import Submission.Work.RiemLib.API

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

namespace Work.CartanHadamard

theorem isCoveringMap_of_sheets {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] (f : X → Y)
    (hdisc : ∀ y : Y, DiscreteTopology (f ⁻¹' {y}))
    (h : ∀ y : Y, ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧
      ∃ U : (f ⁻¹' {y}) → Set X,
        (∀ i {W : Set Y}, W ⊆ V → (IsOpen W ↔ IsOpen (f ⁻¹' W ∩ U i))) ∧
        (∀ i, Set.SurjOn f (U i) V) ∧ (∀ i, Set.InjOn f (U i)) ∧
        Pairwise (Function.onFun Disjoint U) ∧ f ⁻¹' V ⊆ ⋃ i, U i) :
    IsCoveringMap f := by
  classical
  intro y
  obtain ⟨V, hVopen, hyV, U, hopeniff, hsurj, hinj, hdisj, hcover⟩ := h y
  rcases isEmpty_or_nonempty (f ⁻¹' {y}) with hIempty | hIne
  · -- empty fibre
    haveI := hIempty
    have hfV : f ⁻¹' V = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨i, _⟩ := Set.mem_iUnion.mp (hcover he)
      exact isEmptyElim i
    exact IsEvenlyCovered.of_preimage_eq_empty (f ⁻¹' {y}) (hVopen.mem_nhds hyV) hfV
  · -- nonempty fibre
    let Wi : (f ⁻¹' {y}) → Set X := fun i => f ⁻¹' V ∩ U i
    have hWi_open : ∀ i, IsOpen (Wi i) := fun i => (hopeniff i (le_refl V)).mp hVopen
    have hWi_eq : f ⁻¹' V = ⋃ i, Wi i := by
      apply Set.Subset.antisymm
      · intro e he
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover he)
        exact Set.mem_iUnion.mpr ⟨i, ⟨he, hi⟩⟩
      · intro e he
        obtain ⟨i, h1, _⟩ := Set.mem_iUnion.mp he
        exact h1
    have hfVopen : IsOpen (f ⁻¹' V) := by
      rw [hWi_eq]; exact isOpen_iUnion hWi_open
    have hdisjW : ∀ i j, i ≠ j → Disjoint (Wi i) (Wi j) := fun i j hij =>
      Disjoint.mono Set.inter_subset_right Set.inter_subset_right (hdisj hij)
    have hmem_unique : ∀ (e : X), e ∈ f ⁻¹' V → ∀ i j, e ∈ U i → e ∈ U j → i = j := by
      intro e he i j hi hj
      by_contra hne
      exact (Set.disjoint_left.mp (hdisjW i j hne)) ⟨he, hi⟩ ⟨he, hj⟩
    have hlift : ∀ (i : f ⁻¹' {y}) (v : V), ∃ e : X, e ∈ U i ∧ f e = (v : Y) :=
      fun i v => (Set.mem_image f (U i) (v : Y)).mp (hsurj i v.2)
    let Phi : (i : f ⁻¹' {y}) → V → f ⁻¹' V := fun i v =>
      ⟨Classical.choose (hlift i v),
        by simpa only [Set.mem_preimage, (Classical.choose_spec (hlift i v)).2] using v.2⟩
    have hPhi_spec : ∀ (i : f ⁻¹' {y}) (v : V),
        (Phi i v : X) ∈ U i ∧ f (Phi i v) = (v : Y) := fun i v =>
      Classical.choose_spec (hlift i v)
    have hcont_on : ∀ i : f ⁻¹' {y}, ContinuousOn f (Wi i) := by
      intro i
      rw [continuousOn_iff]
      intro x hx t ht hft
      exact ⟨f ⁻¹' (t ∩ V) ∩ U i, (hopeniff i Set.inter_subset_right).mp (ht.inter hVopen),
        ⟨⟨hft, hx.1⟩, hx.2⟩, fun z hz => hz.1.1.1⟩
    have hcfOn : ContinuousOn f (f ⁻¹' V) := by
      rw [hWi_eq]; exact ContinuousOn.iUnion_of_isOpen hcont_on hWi_open
    have hcf : Continuous (fun e : f ⁻¹' V => (f e : Y)) := hcfOn.domRestrict
    have hcfV : Continuous (fun e : f ⁻¹' V => (⟨f e, e.2⟩ : V)) :=
      hcf.subtype_mk (fun e => e.2)
    let chi : (f ⁻¹' V) → (f ⁻¹' {y}) := fun e =>
      Classical.choose (Set.mem_iUnion.mp (hcover e.2))
    have chi_spec : ∀ e : f ⁻¹' V, (e : X) ∈ U (chi e) := fun e =>
      Classical.choose_spec (Set.mem_iUnion.mp (hcover e.2))
    have hchi_cont : Continuous chi := by
      refine continuous_of_continuousOn_iUnion_of_isOpen
        (s := fun i : f ⁻¹' {y} => {e : f ⁻¹' V | (e : X) ∈ Wi i}) ?_ ?_ ?_
      · intro i
        exact ContinuousOn.congr continuousOn_const
          (fun e he => hmem_unique (e : X) e.2 (chi e) i (chi_spec e) he.2)
      · intro i
        exact (hWi_open i).preimage continuous_subtype_val
      · apply Set.eq_univ_iff_forall.mpr
        intro e
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover e.2)
        exact Set.mem_iUnion.mpr ⟨i, ⟨e.2, hi⟩⟩
    have htoB : Continuous (fun e : f ⁻¹' V => ((⟨f e, e.2⟩ : V), chi e)) :=
      hcfV.prodMk hchi_cont
    let invB : V × (f ⁻¹' {y}) → f ⁻¹' V := fun p => Phi p.2 p.1
    have invB_spec : ∀ p : V × (f ⁻¹' {y}),
        (invB p : X) ∈ U p.2 ∧ f (invB p) = (p.1 : Y) := fun p => hPhi_spec p.2 p.1
    have hPhiX_cont : ∀ i : f ⁻¹' {y}, Continuous (fun v : V => (Phi i v : X)) := by
      intro i
      rw [continuous_def]
      intro O' hO'
      have hWopen : IsOpen (f '' (O' ∩ Wi i)) := by
        have hsub : f '' (O' ∩ Wi i) ⊆ V := by
          rintro _ ⟨z, hz, rfl⟩
          exact hz.2.1
        refine (hopeniff i hsub).mpr ?_
        have heq : f ⁻¹' (f '' (O' ∩ Wi i)) ∩ U i = O' ∩ Wi i := by
          ext z; constructor
          · rintro ⟨hz1, hz2⟩
            obtain ⟨z', hz', hff⟩ := (Set.mem_image f (O' ∩ Wi i) (f z)).mp hz1
            have hzz : z = z' := hinj i hz2 hz'.2.2 hff.symm
            rw [hzz]; exact hz'
          · intro hz
            exact ⟨(Set.mem_image f (O' ∩ Wi i) (f z)).mpr ⟨z, hz, rfl⟩, hz.2.2⟩
        rw [heq]; exact hO'.inter (hWi_open i)
      have heq2 : (fun v : V => (Phi i v : X)) ⁻¹' O'
          = Subtype.val ⁻¹' (f '' (O' ∩ Wi i)) := by
        ext v; constructor
        · intro hv
          exact (Set.mem_image f (O' ∩ Wi i) (v : Y)).mpr
            ⟨(Phi i v : X),
              ⟨hv, ⟨by simpa only [Set.mem_preimage, (hPhi_spec i v).2] using v.2,
                    (hPhi_spec i v).1⟩⟩,
              (hPhi_spec i v).2⟩
        · rintro ⟨z, ⟨hzO, hzW⟩, hfz⟩
          have hz : z = (Phi i v : X) :=
            hinj i hzW.2 (hPhi_spec i v).1 (hfz.trans ((hPhi_spec i v).2).symm)
          show (Phi i v : X) ∈ O'
          rw [← hz]; exact hzO
      rw [heq2]; exact hWopen.preimage continuous_subtype_val
    have hPhi_cont : ∀ i : f ⁻¹' {y}, Continuous (Phi i) := fun i => by
      simpa using (hPhiX_cont i).subtype_mk (fun v => (Phi i v).2)
    have hinvB_cont : Continuous invB := by
      refine continuous_of_continuousOn_iUnion_of_isOpen
        (s := fun i : f ⁻¹' {y} => Set.univ ×ˢ ({i} : Set (f ⁻¹' {y}))) ?_ ?_ ?_
      · intro i
        refine (((hPhi_cont i).comp continuous_fst).continuousOn).congr ?_
        intro p hp
        have hp2 : p.2 = i := by
          simpa only [Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff, true_and] using hp
        show Phi p.2 p.1 = Phi i p.1
        rw [hp2]
      · intro i
        exact IsOpen.prod isOpen_univ ((discreteTopology_iff_isOpen_singleton.mp (hdisc y)) i)
      · apply Set.eq_univ_iff_forall.mpr
        intro p
        exact Set.mem_iUnion.mpr ⟨p.2, ⟨Set.mem_univ _, Set.mem_singleton p.2⟩⟩
    have hleft : ∀ e : f ⁻¹' V, invB ((⟨f e, e.2⟩ : V), chi e) = e := by
      intro e
      apply Subtype.ext
      show (Phi (chi e) (⟨f e, e.2⟩ : V) : X) = (e : X)
      exact hinj (chi e) (hPhi_spec (chi e) (⟨f e, e.2⟩ : V)).1 (chi_spec e)
        (by rw [(hPhi_spec (chi e) (⟨f e, e.2⟩ : V)).2])
    have hright : ∀ p : V × (f ⁻¹' {y}),
        ((⟨f (invB p), (invB p).2⟩ : V), chi (invB p)) = p := by
      rintro ⟨v, i⟩
      refine Prod.ext ?_ ?_
      · apply Subtype.ext
        exact (invB_spec (v, i)).2
      · exact hmem_unique (invB (v, i) : X) (invB (v, i)).2 (chi (invB (v, i))) i
          (chi_spec (invB (v, i))) (invB_spec (v, i)).1
    let H : f ⁻¹' V ≃ₜ V × (f ⁻¹' {y}) :=
      { toEquiv :=
          { toFun := fun e => ((⟨f e, e.2⟩ : V), chi e)
            invFun := invB
            left_inv := hleft
            right_inv := hright }
        continuous_toFun := htoB
        continuous_invFun := hinvB_cont }
    exact ⟨hdisc y, V, hyV, hVopen, hfVopen, H, fun e => rfl⟩

end Work.CartanHadamard
