import Mathlib
import Submission.Work.Topology.Covering.sheet_mem_iff_of_saturated

namespace Work.Topology.Covering

open Function

/-- **Restricting a map to a union of sheets of a trivialization.** Let `f : X → Y`, let
`H : f ⁻¹' U' ≃ₜ ↥U' × I` trivialize `f` over an open, *preconnected* set `U' ∋ y` (with `I`
discrete and `(H x).1 = f x`), and let `X₀ ⊆ X` be saturated with respect to preconnected
subsets of `f ⁻¹' U'`:
`hsat : ∀ C : Set X, IsPreconnected C → C ⊆ f ⁻¹' U' → (C ∩ X₀).Nonempty → C ⊆ X₀`.
(As `U'` is preconnected every sheet of `H` is preconnected, so `hsat` makes each sheet either
contained in `X₀` or disjoint from it.)  Then the restricted map `fun x : ↥X₀ => f x` is evenly
covered at `y`. -/
theorem isEvenlyCovered_subtype_of_sheets {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {y : Y} {I : Type*} [TopologicalSpace I] [DiscreteTopology I]
    {X₀ : Set X} {U' : Set Y} (hyU' : y ∈ U') (hU'open : IsOpen U')
    (hU'conn : IsPreconnected U') (hfU'open : IsOpen (f ⁻¹' U'))
    (H : f ⁻¹' U' ≃ₜ U' × I) (hH : ∀ x : f ⁻¹' U', ((H x).1 : Y) = f x)
    (hsat : ∀ C : Set X, IsPreconnected C → C ⊆ f ⁻¹' U' → (C ∩ X₀).Nonempty → C ⊆ X₀) :
    IsEvenlyCovered (fun x : ↥X₀ => f x) y ((fun x : ↥X₀ => f x) ⁻¹' {y}) := by
  classical
  -- `J` indexes the sheets of the trivialization `H` that meet `X₀`.
  let J : Set I := {i | ∃ u : ↥U', ((H.symm (u, i) : ↥(f ⁻¹' U')) : X) ∈ X₀}
  -- Because `U'` is preconnected, every sheet of `H` is preconnected, so `hsat` shows that a
  -- point of `↥(f ⁻¹' U')` lies in `X₀` exactly when its sheet does.
  have hkey : ∀ (q : ↥U' × I), ((H.symm q : ↥(f ⁻¹' U')) : X) ∈ X₀ ↔ q.2 ∈ J := by
    intro q
    simpa only [J, Set.mem_ofPred_eq] using sheet_mem_iff_of_saturated hU'conn H hsat q
  -- The part of `↥X₀` above `U'`.
  let s : Set ↥X₀ := (fun x : ↥X₀ => f x) ⁻¹' U'
  let pT : ↥s → ↥(f ⁻¹' U') := fun x => ⟨(x.1 : X), x.2⟩
  have hpT : Continuous pT :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun x => x.2)
  have hmem : ∀ x : ↥s, (H (pT x)).2 ∈ J := by
    intro x
    refine (hkey (H (pT x))).mp ?_
    rw [Homeomorph.symm_apply_apply]
    exact x.1.2
  -- The homeomorphism `↥s ≃ₜ ↥U' × ↥J`.
  let toFun : ↥s → ↥U' × ↥J := fun x => ((H (pT x)).1, ⟨(H (pT x)).2, hmem x⟩)
  have hsymm : ∀ x : ↥s, H.symm ((H (pT x)).1, (H (pT x)).2) = pT x := by
    intro x
    rw [Prod.mk.eta, Homeomorph.symm_apply_apply]
  let invFun : ↥U' × ↥J → ↥s := fun w =>
    ⟨⟨((H.symm (w.1, (w.2 : I)) : ↥(f ⁻¹' U')) : X),
        (hkey (w.1, (w.2 : I))).mpr w.2.2⟩,
     (H.symm (w.1, (w.2 : I)) : ↥(f ⁻¹' U')).2⟩
  have hli : LeftInverse invFun toFun := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change ((H.symm ((H (pT x)).1, (H (pT x)).2) : ↥(f ⁻¹' U')) : X) = (x.1 : X)
    rw [hsymm x]
  have hpinv : ∀ w : ↥U' × ↥J, pT (invFun w) = H.symm (w.1, (w.2 : I)) :=
    fun w => Subtype.ext rfl
  have hri : RightInverse invFun toFun := by
    intro w
    apply Prod.ext
    · show (H (pT (invFun w))).1 = w.1
      rw [hpinv w, Homeomorph.apply_symm_apply]
    · apply Subtype.ext
      show (H (pT (invFun w))).2 = (w.2 : I)
      rw [hpinv w, Homeomorph.apply_symm_apply]
  let e : ↥s ≃ ↥U' × ↥J :=
    { toFun := toFun, invFun := invFun, left_inv := hli, right_inv := hri }
  have hcont_to : Continuous toFun :=
    Continuous.prodMk (H.continuous.comp hpT).fst
      (Continuous.subtype_mk (H.continuous.comp hpT).snd hmem)
  have hw : Continuous fun w : ↥U' × ↥J => ((w.1, (w.2 : I)) : ↥U' × I) :=
    Continuous.prodMk continuous_fst (continuous_subtype_val.comp continuous_snd)
  have hcont_inv : Continuous invFun :=
    Continuous.subtype_mk
      (Continuous.subtype_mk (continuous_subtype_val.comp (H.symm.continuous.comp hw))
        (fun w => (hkey (w.1, (w.2 : I))).mpr w.2.2))
      (fun w => (H.symm (w.1, (w.2 : I))).2)
  have hJ : IsEvenlyCovered (fun x : ↥X₀ => f x) y J := by
    refine ⟨inferInstance, U', hyU', hU'open, ?_, ?_, ?_⟩
    · have h1 : Subtype.val ⁻¹' (f ⁻¹' U') = (fun x : ↥X₀ => f x) ⁻¹' U' := rfl
      rw [← h1]
      exact hfU'open.preimage continuous_subtype_val
    · exact { toEquiv := e, continuous_toFun := hcont_to, continuous_invFun := hcont_inv }
    · intro x; exact hH (pT x)
  exact hJ.to_isEvenlyCovered_preimage

end Work.Topology.Covering
