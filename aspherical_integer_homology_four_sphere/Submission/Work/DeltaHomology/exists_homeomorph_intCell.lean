import Mathlib
import Submission.Work.DeltaHomology.CellData
import Submission.Work.DeltaHomology.eq_of_cls_eq_of_pos
import Submission.Work.DeltaHomology.mem_skelSet_iff
import Submission.Work.DeltaHomology.PunctSkelBasic
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Work.Homology

open Convexity

/-- The interior of the standard `n`-simplex (the points all of whose barycentric weights are
strictly positive) is open in the standard `n`-simplex. -/
lemma isOpen_setOf_isOpenSimplexPoint (n : ℕ) :
    IsOpen {w : StdSimplex ℝ (Fin (n + 1)) | IsOpenSimplexPoint n w} := by
  have h : {w : StdSimplex ℝ (Fin (n + 1)) | IsOpenSimplexPoint n w}
      = ⋂ i : Fin (n + 1), {w : StdSimplex ℝ (Fin (n + 1)) | 0 < w.weights i} := by
    ext w
    simp [IsOpenSimplexPoint]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    (StdSimplex.continuous_weights_apply (R := ℝ) i).isOpen_preimage _ isOpen_Ioi

/-- **The open cell of an `n`-simplex of a realized `Δ`-complex is homeomorphic to the open
standard `n`-simplex**, the homeomorphism being the characteristic map `χ.cls n σ` restricted to
the points of `Δⁿ` with strictly positive barycentric weights:
`↥{w | IsOpenSimplexPoint n w} ≃ₜ ↥(χ.intCell n σ)`, given by `w ↦ χ.cls n σ w`.  (Injectivity on
the interior is `eq_of_cls_eq_of_pos`; the topology is the quotient topology of the characteristic
map, by `IsQuotientMap.of_surjective_continuous` from the compact source `Δⁿ` to the Hausdorff
closed cell, restricted to the saturated open set of interior points.)  Note `openStdSimplex n`
(`Submission/Work/DeltaHomology/exists_homeo_intCell.lean`) is the set `{w | IsOpenSimplexPoint n w}`;
this statement is the strong form of the `Nonempty` statement proved there, recording also that
the homeomorphism is the characteristic map (so that it carries the barycentre to the
barycentre of the cell). -/
theorem exists_homeomorph_intCell {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (n : ℕ) (σ : Fin (K.card n)) :
    ∃ e : ↥{w : Convexity.StdSimplex ℝ (Fin (n + 1)) | IsOpenSimplexPoint n w} ≃ₜ
        ↥(R.toDeltaSimplexMap.intCell n σ),
      ∀ (w : ↥{w : Convexity.StdSimplex ℝ (Fin (n + 1)) | IsOpenSimplexPoint n w}),
        (e w : X) = R.toDeltaSimplexMap.cls n σ w := by
  classical
  letI : T2Space X := R.t2
  let χ : DeltaSimplexMap K X := R.toDeltaSimplexMap
  let Int : Set (StdSimplex ℝ (Fin (n + 1))) := {w | IsOpenSimplexPoint n w}
  have hInt_open : IsOpen Int := isOpen_setOf_isOpenSimplexPoint n
  -- (A) interior points map into the open cell
  have mem_intCell : ∀ (w : StdSimplex ℝ (Fin (n + 1))), w ∈ Int →
      χ.cls n σ w ∈ χ.intCell n σ := by
    intro w hw
    refine ⟨Set.mem_range_self w, ?_⟩
    intro j hj hmem
    obtain ⟨q, hq, hquniq⟩ := R.bij (χ.cls n σ w)
    obtain ⟨p, hp, hpd⟩ := (mem_skelSet_iff R j (χ.cls n σ w)).mp hmem
    have hpq : p = q := hquniq p hp
    have hqn : q.dim = n := by
      have h : (⟨n, σ, w, hw⟩ : OpenSimplex K) = q := hquniq ⟨n, σ, w, hw⟩ rfl
      rw [← h]
    have hpn : p.dim = n := by rw [hpq, hqn]
    omega
  let hfn : StdSimplex ℝ (Fin (n + 1)) → X := fun w => χ.cls n σ w
  let f : ↥Int → ↥(χ.intCell n σ) := fun w => ⟨hfn w.1, mem_intCell w.1 w.2⟩
  have hcont : Continuous hfn := (χ.cls n σ).continuous
  have hfn_closed : IsClosedMap hfn := hcont.isClosedMap
  have f_cont : Continuous f :=
    (hcont.comp continuous_subtype_val).subtype_mk (fun w => mem_intCell w.1 w.2)
  have f_inj : Function.Injective f := by
    intro a b hab
    have hcls : χ.cls n σ a.1 = χ.cls n σ b.1 := congrArg Subtype.val hab
    have h2 : a.1 = b.1 := (eq_of_cls_eq_of_pos R a.2 hcls).2
    exact Subtype.ext h2
  have f_surj : Function.Surjective f := by
    intro x
    obtain ⟨hcell, hnotin⟩ := x.2
    obtain ⟨w, hw⟩ := hcell
    obtain ⟨q, hq, hquniq⟩ := R.bij x.1
    have hle : q.dim ≤ n := by
      have hxskel : x.1 ∈ χ.skelSet n := by rw [← hw]; exact χ.cls_mem_skelSet le_rfl σ w
      obtain ⟨p, hp, hpd⟩ := (mem_skelSet_iff R n x.1).mp hxskel
      rw [← hquniq p hp]; exact hpd
    have hge : ¬ q.dim < n := by
      intro hlt
      exact hnotin q.dim hlt (by rw [← hq]; exact χ.real_mem_skelSet q)
    have hqn : q.dim = n := by omega
    have hwInt : w ∈ Int := R.interior_of_cls_eq_real q hqn σ w (by rw [hw, hq])
    exact ⟨⟨w, hwInt⟩, Subtype.ext hw⟩
  have intCell_eq : χ.intCell n σ = hfn '' Int := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨w, hw⟩ := f_surj ⟨x, hx⟩
      exact ⟨w.1, w.2, by simpa [f] using congrArg Subtype.val hw⟩
    · rintro x ⟨w, hw, rfl⟩
      exact mem_intCell w hw
  have satur : ∀ c : StdSimplex ℝ (Fin (n + 1)), hfn c ∈ hfn '' Int → c ∈ Int := by
    rintro c ⟨u, hu, huc⟩
    have huc' : u = c := (eq_of_cls_eq_of_pos R hu huc).2
    rw [← huc']; exact hu
  have f_open : IsOpenMap f := by
    intro U hU
    obtain ⟨c, hc_open, hc_eq⟩ := hU.image_val
    let U₀ : Set (StdSimplex ℝ (Fin (n + 1))) := Subtype.val '' U
    have hU₀_eq : U₀ = c ∩ Int := hc_eq
    have hU₀_open : IsOpen U₀ := by rw [hU₀_eq]; exact hc_open.inter hInt_open
    have hU₀_sub : U₀ ⊆ Int := by rw [hU₀_eq]; exact Set.inter_subset_right
    let C : Set (StdSimplex ℝ (Fin (n + 1))) := U₀ᶜ
    have hC_closed : IsClosed C := hU₀_open.isClosed_compl
    have hC_img_closed : IsClosed (hfn '' C) := hfn_closed C hC_closed
    have key : hfn '' U₀ = χ.intCell n σ ∩ (hfn '' C)ᶜ := by
      apply Set.Subset.antisymm
      · rintro x ⟨w, hw, rfl⟩
        refine ⟨mem_intCell w (hU₀_sub hw), ?_⟩
        rintro ⟨c', hc', hcw⟩
        have hwInt : w ∈ Int := hU₀_sub hw
        have heq : w = c' := (eq_of_cls_eq_of_pos R hwInt hcw.symm).2
        exact hc' (heq ▸ hw)
      · rintro x ⟨hxint, hxC⟩
        rw [intCell_eq] at hxint
        obtain ⟨w, hwInt, hwx⟩ := hxint
        by_cases hw : w ∈ U₀
        · exact ⟨w, hw, hwx⟩
        · exact absurd ⟨w, by simpa [C] using hw, hwx⟩ hxC
    have hpre : (Subtype.val : ↥(χ.intCell n σ) → X) ⁻¹' ((hfn '' C)ᶜ) = f '' U := by
      have h1 : (Subtype.val : ↥(χ.intCell n σ) → X) ⁻¹' ((hfn '' C)ᶜ)
          = (Subtype.val : ↥(χ.intCell n σ) → X) ⁻¹' (χ.intCell n σ ∩ (hfn '' C)ᶜ) := by
        ext x
        simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_inter_iff]
        exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
      rw [h1, ← key]
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨w, hw, hwx⟩
        have hw' : w ∈ Subtype.val '' U := hw
        obtain ⟨u, hu, rfl⟩ := hw'
        exact ⟨u, hu, by apply Subtype.ext; simpa [f] using hwx⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u.1, ⟨u, hu, rfl⟩, by simp [f]⟩
    exact (Topology.IsInducing.subtypeVal (t := χ.intCell n σ)).isOpen_iff.mpr
      ⟨(hfn '' C)ᶜ, hC_img_closed.isOpen_compl, hpre⟩
  have hf : IsHomeomorph f := ⟨f_cont, f_open, f_inj, f_surj⟩
  refine ⟨hf.homeomorph f, ?_⟩
  intro w
  show (f w : X) = R.toDeltaSimplexMap.cls n σ w
  rfl

end Work.DeltaHomology
