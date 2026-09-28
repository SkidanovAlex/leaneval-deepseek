import Mathlib
import Submission.Work.Serre.thomCylLadderEps
import Submission.Work.Serre.thomCylLadder
import Submission.Work.Serre.attachRelCohVanishing
import Submission.Work.Serre.attachRelCohVanishingHigh
import Submission.Work.Serre.discPairCellVanishing
import Submission.Work.Serre.hG_ladderLight

/-!
# The ladder assembly of the cellular step `Work.Serre.thomCylCellStepAlt`

This module isolates the *bookkeeping* of the cellular step: given the two long exact sequences of
the ladder

* the pair `(Γ', S)` of the cell attachment (`Work.Serre.baseF/G/D`, exact by
  `Work.Serre.baseExact₁/₂/₃`), and
* the triple `A ⊆ N ⊆ M` of the mapping cylinder of `q` (`Work.Serre.totF/G/D`, exact by
  `Work.Serre.totExact₁/₂/₃`),

and the extension class `U` of the induction class over the old part (`cellStepU`), the target
vertical `TP m : H^m(Γ') → H^{m+r+1}(M,A)` is an isomorphism for every degree **except possibly**
`m = D-1` and `m = D`.

The argument is the direct diagram chase (`isIso_TP_of_ne_mid`), not the five lemma: away from the
cell dimension both `H^{m}(Γ',S)` and `H^{m+1}(Γ',S)` vanish (`attachRelCohVanishing` /
`attachRelCohVanishingHigh`), so `F₁(m) = 0` (whence `TP m` is injective) and `δ₁(m) = 0`
(whence `G₁(m)` is onto, giving surjectivity up to the vanishing of the new-cell group
`H^{m+r+1}(M,N)`, which is `discPairCellVanishing`).  The only new ingredient is the middle square
`hG` (`Work.Serre.hG_ladder`, proved).

Thus `Work.Serre.ThomCylAt r N q` follows from the two critical isomorphisms at `m = D-1` and
`m = D` (`thomCylCellStepAlt_of_mid`).
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

set_option maxHeartbeats 1600000

/-- **The extension class `U` of the cellular step**: the class on the pair `(cyl q, A)` whose
restriction to the preimage of the old part is the induction class `IH.choose`.  It is the witness
of `Work.Serre.exists_extensionClass` (and is unique). -/
noncomputable def cellStepU (r N D : ℕ) (hr : 1 ≤ r) (hN : r ≤ N) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q
      (Work.Serre.ladS D Γ ι f))) :
    Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)) :=
  (Work.Serre.exists_extensionClass r N D hr hN hD hΓ ι f q hq hvan hpc IH.choose).choose

/-- The defining property of `cellStepU`: its restriction to the preimage of the old part is the
induction class. -/
theorem cellStepU_spec (r N D : ℕ) (hr : 1 ≤ r) (hN : r ≤ N) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q
      (Work.Serre.ladS D Γ ι f))) :
    (HomologicalComplex.homologyMap (Work.Serre.tripleRestr ℚ (TopCat.of (Work.Serre.cyl q))
        (Set.range (Work.Serre.cylIncl q))
        ((Work.Serre.cylRetract q) ⁻¹' (Work.Serre.ladS D Γ ι f) ∪
          Set.range (Work.Serre.cylIncl q)) (fun _ hx => Or.inr hx)) (r + 1)).hom
        (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH)
      = Work.Serre.uNew r q (Work.Serre.ladS D Γ ι f)
          Work.RatHurewicz.isClosed_range_attachIncl IH.choose :=
  (Work.Serre.exists_extensionClass r N D hr hN hD hΓ ι f q hq hvan hpc IH.choose).choose_spec

/-- The middle square of the ladder (`Work.Serre.hG_ladder`) for the extension class
`cellStepU`. -/
theorem cellStepU_hG (r N D : ℕ) (hr : 1 ≤ r) (hN : r ≤ N) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q
      (Work.Serre.ladS D Γ ι f))) (k : ℕ) :
    CategoryTheory.CategoryStruct.comp (Work.Serre.baseG D Γ ι f k)
        (Work.Serre.TQ r q (Work.Serre.ladS D Γ ι f)
          Work.RatHurewicz.isClosed_range_attachIncl IH.choose k)
      = CategoryTheory.CategoryStruct.comp
          (Work.Serre.TP r q (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH) k)
          (Work.Serre.totG D ι f q (k + (r + 1))) :=
  Work.Serre.mq_hG_ladder r D hD ι f q IH.choose
    (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH)
    (cellStepU_spec r N D hr hN hD hΓ ι f q hq hvan hpc IH) k


/-- **The non-critical degrees of the cellular step.**  For `m ≤ N - r` with `m ∉ {D-1, D}`, the
target cup map `TP m : H^m(Γ') → H^{m+r+1}(M,A)` of the ladder is an isomorphism.

The proof is a direct diagram chase with the middle square `cellStepU_hG`:
* injectivity: `TP x = 0` forces `G₁ x = 0` (as `TQ m` is injective), hence `x ∈ im F₁(m)`, which is
  `0` because `H^m(Γ',S) = 0` for `m ≠ D`;
* surjectivity: `c := (TQ m)⁻¹ (G₂ y)` lies in `ker δ₁(m)`, which is all of `H^m(S)` because
  `H^{m+1}(Γ',S) = 0` for `m ≠ D-1`; so `c = G₁ x` for some `x`, and the error
  `TP x - y ∈ ker G₂(m+r+1) = im F₂(m+r+1) = H^{m+r+1}(M,N)` vanishes because `m ≠ D`.
-/
theorem isIso_TP_of_ne_mid (r N D : ℕ) (hr : 1 ≤ r) (hN : r ≤ N) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q
      (Work.Serre.ladS D Γ ι f)))
    (m : ℕ) (hm : m ≤ N - r) (hm1 : m ≠ D - 1) (hm2 : m ≠ D) :
    CategoryTheory.IsIso (Work.Serre.TP r q
      (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH) m) := by
  classical
  have hG_ap : ∀ x : Work.Thom.Coh ℚ m (Work.RatHurewicz.attachCells (D - 2) Γ ι f),
      (Work.Serre.TQ r q (Work.Serre.ladS D Γ ι f)
          Work.RatHurewicz.isClosed_range_attachIncl IH.choose m).hom
        ((Work.Serre.baseG D Γ ι f m).hom x)
      = (Work.Serre.totG D ι f q (m + (r + 1))).hom
          ((Work.Serre.TP r q (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH) m).hom x) := by
    intro x
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      (cellStepU_hG r N D hr hN hD hΓ ι f q hq hvan hpc IH m)) x
  have hTQbij : Function.Bijective (Work.Serre.TQ r q (Work.Serre.ladS D Γ ι f)
      Work.RatHurewicz.isClosed_range_attachIncl IH.choose m).hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp
      (Work.Serre.isIso_TQ r N q (Work.Serre.ladS D Γ ι f)
        Work.RatHurewicz.isClosed_range_attachIncl IH m (by omega))
  -- the vanishing of `H^m(Γ',S)`
  have hzero₁ : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ m
      (Work.RatHurewicz.attachCells (D - 2) Γ ι f) (Work.Serre.ladS D Γ ι f)) := by
    rcases lt_or_ge m D with hlt | hge
    · exact Work.Serre.attachRelCohVanishing D hD hΓ ι f m (by omega)
    · rcases eq_or_lt_of_le hge with heq | hlt
      · exact absurd heq.symm hm2
      · exact Work.Serre.attachRelCohVanishingHigh D hD ι f m hlt
  -- the vanishing of `H^{m+1}(Γ',S)`
  have hzero₂ : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (m + 1)
      (Work.RatHurewicz.attachCells (D - 2) Γ ι f) (Work.Serre.ladS D Γ ι f)) := by
    rcases lt_or_ge (m + 1) D with hlt | hge
    · exact Work.Serre.attachRelCohVanishing D hD hΓ ι f (m + 1) (by omega)
    · rcases eq_or_lt_of_le hge with heq | hlt
      · exact absurd (by omega : m = D - 1) hm1
      · exact Work.Serre.attachRelCohVanishingHigh D hD ι f (m + 1) hlt
  -- the vanishing of the new-cell group `H^{m+r+1}(M,N)`
  have hzero₃ : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (m + (r + 1))
      (Work.Serre.cyl q) (Work.Serre.ladNew D ι f q)) :=
    Work.Serre.discPairCellVanishing r N D hr hD hΓ ι f q hq hvan hpc (m + r + 1)
      (by omega) (by omega)
  have hbaseF0 : Work.Serre.baseF D Γ ι f m = 0 := hzero₁.eq_of_src _ _
  have hbaseD0 : Work.Serre.baseD D Γ ι f m = 0 := hzero₂.eq_of_tgt _ _
  have htotF0 : Work.Serre.totF D ι f q (m + (r + 1)) = 0 := hzero₃.eq_of_src _ _
  refine (CategoryTheory.ConcreteCategory.isIso_iff_bijective
    (Work.Serre.TP r q (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH) m)).mpr ⟨?_, ?_⟩
  · -- injectivity
    intro x y hxy
    have hsub : (Work.Serre.TP r q
        (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH) m).hom (x - y) = 0 := by
      rw [map_sub, hxy]
      exact sub_self _
    have h1 : (Work.Serre.TQ r q (Work.Serre.ladS D Γ ι f)
        Work.RatHurewicz.isClosed_range_attachIncl IH.choose m).hom
        ((Work.Serre.baseG D Γ ι f m).hom (x - y)) = 0 :=
      (hG_ap (x - y)).trans (by rw [hsub]; exact map_zero _)
    have h2 : (Work.Serre.baseG D Γ ι f m).hom (x - y) = 0 :=
      hTQbij.1 (h1.trans (map_zero _).symm)
    have h3 : x - y ∈ LinearMap.range
        (ModuleCat.Hom.hom (Work.Serre.baseF D Γ ι f m)) := by
      rw [Work.Serre.baseExact₂ D Γ ι f m]
      simpa [LinearMap.mem_ker] using h2
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp h3
    have hz0 : x - y = 0 := by
      obtain ⟨z', hz'⟩ : ∃ z', (ModuleCat.Hom.hom (Work.Serre.baseF D Γ ι f m)) z' = x - y :=
        ⟨z, hz⟩
      rw [← hz']
      have hz'' : (ModuleCat.Hom.hom (Work.Serre.baseF D Γ ι f m)) z' = 0 := by
        rw [hbaseF0]
        exact LinearMap.zero_apply z'
      rw [hz'']
    exact sub_eq_zero.mp hz0
  · -- surjectivity
    intro y
    obtain ⟨c, hc⟩ := hTQbij.2 ((Work.Serre.totG D ι f q (m + (r + 1))).hom y)
    have hcd : (Work.Serre.baseD D Γ ι f m).hom c = 0 := by simp [hbaseD0]
    have h4 : c ∈ LinearMap.range (ModuleCat.Hom.hom (Work.Serre.baseG D Γ ι f m)) := by
      rw [Work.Serre.baseExact₃ D Γ ι f m]
      simpa [LinearMap.mem_ker] using hcd
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp h4
    have h5 : (Work.Serre.totG D ι f q (m + (r + 1))).hom
        ((Work.Serre.TP r q (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH) m).hom x)
        = (Work.Serre.totG D ι f q (m + (r + 1))).hom y := by
      rw [← hG_ap x, hx, hc]
    have h6 : (Work.Serre.TP r q
        (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH) m).hom x - y
        ∈ LinearMap.ker (ModuleCat.Hom.hom (Work.Serre.totG D ι f q (m + (r + 1)))) := by
      rw [LinearMap.mem_ker, map_sub, h5]
      exact sub_self _
    rw [← Work.Serre.totExact₂ D ι f q (m + (r + 1))] at h6
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp h6
    have hw0 : (Work.Serre.TP r q
        (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH) m).hom x - y = 0 := by
      obtain ⟨z, hz⟩ : ∃ z, (ModuleCat.Hom.hom (Work.Serre.totF D ι f q (m + (r + 1)))) z
        = (Work.Serre.TP r q (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH) m).hom x - y :=
        ⟨w, hw⟩
      rw [← hz]
      have hz0 : (ModuleCat.Hom.hom (Work.Serre.totF D ι f q (m + (r + 1)))) z = 0 := by
        rw [htotF0]
        exact LinearMap.zero_apply z
      rw [hz0]
    exact ⟨x, sub_eq_zero.mp hw0⟩

/-- **The cellular step from its two critical degrees.**  If the target cup map is an isomorphism in
the two critical degrees `D-1` and `D` (whenever those degrees lie in the range), then
`Work.Serre.ThomCylAt r N q` holds: every other degree is `isIso_TP_of_ne_mid`.

The two hypotheses are the only mathematical input left; they are the multiplicative cell comparison
(the Thom isomorphism in the cell dimension). -/
theorem thomCylCellStepAlt_of_mid (r N D : ℕ) (hr : 1 ≤ r) (hN : r ≤ N) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q
      (Work.Serre.ladS D Γ ι f)))
    (hpred : D - 1 ≤ N - r → CategoryTheory.IsIso (Work.Serre.TP r q
      (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH) (D - 1)))
    (hcell : D ≤ N - r → CategoryTheory.IsIso (Work.Serre.TP r q
      (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH) D)) :
    Work.Serre.ThomCylAt r N q := by
  classical
  refine ⟨cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH, fun m hm => ?_⟩
  have hm' : m ≤ N - r := by omega
  by_cases h1 : m = D - 1
  · subst h1
    exact hpred (by omega)
  by_cases h2 : m = D
  · subst h2
    exact hcell (by omega)
  · exact isIso_TP_of_ne_mid r N D hr hN hD hΓ ι f q hq hvan hpc IH m hm' h1 h2

/-- **Injectivity of `TP (D-1)`.**  This is *free*: from `cellStepU_hG` and the injectivity of
`TQ (D-1)` (the induction hypothesis, valid as `D-1 + r + 1 ≤ N + 1`), `TP (D-1) x = 0` forces
`baseG (D-1) x = 0`, i.e. `x ∈ range (baseF (D-1))`, and `H^{D-1}(Γ',S) = 0`
(`attachRelCohVanishing`), so `baseF (D-1) = 0` and `x = 0`. -/
theorem injective_TP_cellPred (r N D : ℕ) (hr : 1 ≤ r) (hN : r ≤ N) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q
      (Work.Serre.ladS D Γ ι f)))
    (hpred : D - 1 ≤ N - r) :
    Function.Injective (Work.Serre.TP r q
      (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH) (D - 1)).hom := by
  classical
  have hG_ap : ∀ x : Work.Thom.Coh ℚ (D - 1) (Work.RatHurewicz.attachCells (D - 2) Γ ι f),
      (Work.Serre.TQ r q (Work.Serre.ladS D Γ ι f)
          Work.RatHurewicz.isClosed_range_attachIncl IH.choose (D - 1)).hom
        ((Work.Serre.baseG D Γ ι f (D - 1)).hom x)
      = (Work.Serre.totG D ι f q ((D - 1) + (r + 1))).hom
          ((Work.Serre.TP r q (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH) (D - 1)).hom x) := by
    intro x
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      (cellStepU_hG r N D hr hN hD hΓ ι f q hq hvan hpc IH (D - 1))) x
  have hTQbij : Function.Bijective (Work.Serre.TQ r q (Work.Serre.ladS D Γ ι f)
      Work.RatHurewicz.isClosed_range_attachIncl IH.choose (D - 1)).hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp
      (Work.Serre.isIso_TQ r N q (Work.Serre.ladS D Γ ι f)
        Work.RatHurewicz.isClosed_range_attachIncl IH (D - 1) (by omega))
  have hzero₁ : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (D - 1)
      (Work.RatHurewicz.attachCells (D - 2) Γ ι f) (Work.Serre.ladS D Γ ι f)) :=
    Work.Serre.attachRelCohVanishing D hD hΓ ι f (D - 1) (by omega)
  have hbaseF0 : Work.Serre.baseF D Γ ι f (D - 1) = 0 := hzero₁.eq_of_src _ _
  intro x y hxy
  have hsub : (Work.Serre.TP r q
      (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH) (D - 1)).hom (x - y) = 0 := by
    rw [map_sub, hxy]
    exact sub_self _
  have h1 : (Work.Serre.TQ r q (Work.Serre.ladS D Γ ι f)
      Work.RatHurewicz.isClosed_range_attachIncl IH.choose (D - 1)).hom
      ((Work.Serre.baseG D Γ ι f (D - 1)).hom (x - y)) = 0 :=
    (hG_ap (x - y)).trans (by rw [hsub]; exact map_zero _)
  have h2 : (Work.Serre.baseG D Γ ι f (D - 1)).hom (x - y) = 0 :=
    hTQbij.1 (h1.trans (map_zero _).symm)
  have h3 : x - y ∈ LinearMap.range
      (ModuleCat.Hom.hom (Work.Serre.baseF D Γ ι f (D - 1))) := by
    rw [Work.Serre.baseExact₂ D Γ ι f (D - 1)]
    simpa [LinearMap.mem_ker] using h2
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp h3
  have hz0 : x - y = 0 := by
    have hz' : (ModuleCat.Hom.hom (Work.Serre.baseF D Γ ι f (D - 1))) z = 0 := by
      rw [hbaseF0]
      exact LinearMap.zero_apply z
    rw [← hz, hz']
  exact sub_eq_zero.mp hz0

/-- **The cellular step from its three critical facts.**  The two critical degrees of the ladder are
`m = D-1` and `m = D`; the target cup map `TP` is an isomorphism there as soon as
* `TP D` is injective (the `CellInjectivity` half of the multiplicative cell comparison),
* `TP D` is surjective (the `CellImageEqLower` half),
* `TP (D-1)` is surjective (the transgression square `δ₁(D-1) ∘ TQ(D-1)⁻¹ ∘ G₂(D+r) = 0`),

the injectivity of `TP (D-1)` being free (`injective_TP_cellPred`).  Every other degree is
`isIso_TP_of_ne_mid`. -/
theorem thomCylCellStepAlt_of_crux (r N D : ℕ) (hr : 1 ≤ r) (hN : r ≤ N) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q
      (Work.Serre.ladS D Γ ι f)))
    (hinj : D ≤ N - r → Function.Injective (Work.Serre.TP r q
      (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH) D).hom)
    (hsurj : D ≤ N - r → Function.Surjective (Work.Serre.TP r q
      (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH) D).hom)
    (hpred : D - 1 ≤ N - r → Function.Surjective (Work.Serre.TP r q
      (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH) (D - 1)).hom) :
    Work.Serre.ThomCylAt r N q := by
  classical
  refine ⟨cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH, fun m hm => ?_⟩
  have hm' : m ≤ N - r := by omega
  by_cases h1 : m = D - 1
  · subst h1
    exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨injective_TP_cellPred r N D hr hN hD hΓ ι f q hq hvan hpc IH (by omega),
        hpred (by omega)⟩
  by_cases h2 : m = D
  · subst h2
    exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨hinj (by omega), hsurj (by omega)⟩
  · exact isIso_TP_of_ne_mid r N D hr hN hD hΓ ι f q hq hvan hpc IH m hm' h1 h2

end

end Work.Serre
