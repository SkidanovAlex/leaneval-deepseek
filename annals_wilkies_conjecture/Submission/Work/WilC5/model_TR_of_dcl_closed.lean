/-
  Area C5 (WilC5): `model_TR_of_dcl_closed`.

  A `dcl`-closed substructure `S` of a model `M ⊨ TR` (o-minimality of `TR`-models is supplied as
  the hypothesis `hOM`) is again a model of `TR`.  The proof is Tarski–Vaught: it suffices to
  show that `S` *meets* every nonempty `S`-definable subset `D ⊆ M`, i.e. that
  `FirstOrder.Language.MeetsDefinable (S : Set M)` holds.  That is the key lemma
  `meetsDefinable_of_dclClosed` below; `S.IsElementary` and `S ⊨ TR` then follow from Mathlib's
  `MeetsDefinable.isElementary_closure`.

  The key lemma: suppose `D` is `A`-definable (with `A = S`, `Dcl A ⊆ A`), nonempty, and meets `A`
  in no point.  O-minimality writes `D` as a finite union of order-convex pieces, so `maxSet D`
  and `supSet D` are finite and `A`-definable (`Work.WilC2`), hence contained in `A`; the same
  holds for `Dᶜ`.  Pick `y ∈ D` and let `J = comp D y` be its component.  Since no point of
  `D ∩ A` must exist, it suffices to produce one:
  * if `y` is the min (resp. max) of `J`, then `y ∈ supSet Dᶜ` (resp. `y ∈ maxSet D`), so `y ∈ A`;
  * otherwise the component of `y` extends on both sides.  If `J` is bounded above, its supremum
    `β` lies in `maxSet D ∪ supSet D ⊆ A`; if additionally `J` is bounded below, its infimum `α`
    lies in `supSet Dᶜ ∪ maxSet Dᶜ ⊆ A` and `(α + β) / 2 ∈ A ∩ D`.  Otherwise use the element
    `β - 1` (or `α + 1`, or `0`), which is in `A` and, by the convexity of `J`, lies in `D`.
-/
import Mathlib
import Submission.Work.WilC5.cut_determines_type_of_omin
import Submission.Work.WilC2.boundary_finite
import Submission.Work.WilC2.finite_maxSet_supSet
import Submission.Work.WilC2.definable_maxSet_supSet
import Submission.Work.WilC2.finite_definable_singleton
import Submission.Work.WilC2.definable_comp
import Submission.Work.WilC4.sup_exists_dcl
import Submission.Work.WilC4.accum_definable_aux
import Submission.Work.WilC4.dcl_add
import Submission.Work.WilC4.dcl_mul
import Submission.Work.WilC4.dcl_neg
import Submission.Work.WilC4.dcl_inv

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.WilC5

open Classical FirstOrder FirstOrder.Language
open WilkiesDesign.CG (LR LRc TR rexpL)

open Work.WilC2 (comp maxSet supSet mem_comp mem_comp_self mem_supSet mem_maxSet comp_subset comp_ordConnected
  mem_maxSet_of_max_comp mem_maxSet_of_isLUB_comp mem_supSet_of_isLUB_comp exists_lt_of_isLUB
  Dcl mem_dcl finite_definable_singleton finite_maxSet_supSet definable_maxSet_supSet
  definable_comp)

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
  [FirstOrder.Ring.CompatibleRing M] [rexpL.Structure M]
  [(FirstOrder.Language.constantsOn ℝ).Structure M]

/-! ## Order-theoretic companions for the case analysis (`J = comp D y`) -/

/-- If `y ∈ D` and `β` bounds `comp D y` above, then all of `(y, β)` lies in the component. -/
lemma comp_of_lt_isLUB {D : Set M} {y β : M} (hJ : IsLUB (comp D y) β) (hyD : y ∈ D) :
    ∀ t, y < t → t < β → t ∈ comp D y := by
  intro t hyt htβ
  obtain ⟨x, hxJ, htx⟩ := exists_lt_of_isLUB hJ htβ
  exact (comp_ordConnected D y).out (mem_comp_self hyD) hxJ ⟨le_of_lt hyt, le_of_lt htx⟩

/-- If `y ∈ D` and `α` bounds `comp D y` below, then all of `(α, y]` lies in the component. -/
lemma comp_of_isGLB_le {D : Set M} {y α : M} (hJ : IsGLB (comp D y) α) (hyD : y ∈ D) :
    ∀ t, α < t → t ≤ y → t ∈ comp D y := by
  intro t hαt hty
  have hex : ∃ x ∈ comp D y, x < t := by
    by_contra hc
    push_neg at hc
    exact absurd (hJ.2 hc) (not_le.mpr hαt)
  obtain ⟨x, hxJ, hxt⟩ := hex
  exact (comp_ordConnected D y).out hxJ (mem_comp_self hyD) ⟨le_of_lt hxt, hty⟩

/-- If `y ∈ D` and `α`, `β` bound `comp D y` below resp. above, then all of `(α, β)` lies in
the component (convexity plus both bounding properties). -/
lemma comp_of_between {D : Set M} {y α β : M} (hglb : IsGLB (comp D y) α)
    (hlub : IsLUB (comp D y) β) {t : M} (hαt : α < t) (htβ : t < β) : t ∈ comp D y := by
  have h1 : ∃ x ∈ comp D y, x < t := by
    by_contra hc
    push_neg at hc
    exact absurd (hglb.2 hc) (not_le.mpr hαt)
  have h2 : ∃ x ∈ comp D y, t < x := by
    by_contra hc
    push_neg at hc
    exact absurd (hlub.2 hc) (not_le.mpr htβ)
  obtain ⟨x, hxJ, hxt⟩ := h1
  obtain ⟨x', hx'J, htx'⟩ := h2
  exact (comp_ordConnected D y).out hxJ hx'J ⟨le_of_lt hxt, le_of_lt htx'⟩

/-- If `comp D y` is unbounded above, then all of `(y, ∞)` lies in the component. -/
lemma comp_of_unboundedAbove {D : Set M} {y : M} (hyD : y ∈ D)
    (hunb : ∀ z : M, ∃ x ∈ comp D y, z < x) : ∀ t, y < t → t ∈ comp D y := by
  intro t hyt
  obtain ⟨x, hxJ, htx⟩ := hunb t
  exact (comp_ordConnected D y).out (mem_comp_self hyD) hxJ ⟨le_of_lt hyt, le_of_lt htx⟩

/-- If `comp D y` is unbounded below, then all of `(-∞, y]` lies in the component. -/
lemma comp_of_unboundedBelow {D : Set M} {y : M} (hyD : y ∈ D)
    (hunb : ∀ z : M, ∃ x ∈ comp D y, x < z) : ∀ t, t ≤ y → t ∈ comp D y := by
  intro t hty
  obtain ⟨x, hxJ, hxt⟩ := hunb t
  exact (comp_ordConnected D y).out hxJ (mem_comp_self hyD) ⟨le_of_lt hxt, hty⟩

/-! ## The auxiliary facts used by the case analysis -/

theorem inf_exists_definable₁ (hM : M ⊨ TR) {T X : Set M}
    (hX : T.Definable₁ LRc X) (hne : X.Nonempty)
    (hbdd : ∃ l : M, ∀ a ∈ X, l ≤ a) :
    ∃ s : M, IsGLB X s ∧ T.Definable₁ LRc ({s} : Set M) := by
  -- the set `LB` of lower bounds of `X` is `T`-definable
  have hLBdef : T.Definable LRc {v : Fin 1 → M | ∀ a : M, a ∈ X → v 0 ≤ a} :=
    Work.WilC4.lowerBounds_definable hM hX
  have hLBdef' : T.Definable₁ LRc {c : M | ∀ a : M, a ∈ X → c ≤ a} := hLBdef
  -- it is nonempty (a lower bound of `X`) and bounded above (by any point of `X`)
  obtain ⟨l, hl⟩ := hbdd
  have hLBne : ({c : M | ∀ a : M, a ∈ X → c ≤ a} : Set M).Nonempty := ⟨l, hl⟩
  obtain ⟨a₀, ha₀⟩ := hne
  have hLBbdd : ∃ u : M, ∀ c ∈ ({c : M | ∀ a : M, a ∈ X → c ≤ a} : Set M), c ≤ u :=
    ⟨a₀, fun c hc => hc a₀ ha₀⟩
  obtain ⟨s, hLUB, hsdef⟩ := Work.WilC4.sup_exists_dcl hM hLBdef' hLBne hLBbdd
  refine ⟨s, ⟨?_, ?_⟩, ?_⟩
  · -- `s` is a lower bound of `X`
    intro a ha
    exact hLUB.2 (mem_upperBounds.mpr fun c hc => hc a ha)
  · -- any lower bound of `X` is `≤ s`
    intro c hc
    exact hLUB.1 hc
  · -- `s` is `T`-definable
    have hset : {v : Fin 1 → M | v 0 ∈ ({s} : Set M)} = {fun _ : Fin 1 => s} := by
      ext v; simp [funext_iff]
    have h := hsdef
    unfold Work.WilC4.DefinableElt at h
    rw [Set.union_empty] at h
    rw [Set.Definable₁, hset]
    exact h

theorem mem_supSet_compl_of_isGLB_comp_mem {D : Set M} {y α : M} (hyD : y ∈ D)
    (hJ : IsGLB (comp D y) α) (hαD : α ∈ D) : α ∈ supSet Dᶜ := by
  have hyJ : y ∈ comp D y := mem_comp_self hyD
  have hαy : α ≤ y := hJ.1 hyJ
  -- `α` itself lies in the component of `y`
  have hαJ : α ∈ comp D y := by
    refine ⟨hαD, ?_, ?_⟩
    · intro t hαt hty
      rcases lt_or_eq_of_le hαt with h | h
      · exact comp_subset D y (comp_of_isGLB_le hJ hyD t h hty)
      · rw [← h]; exact hαD
    · intro t hyt htα
      have h1 : t = y := le_antisymm (le_trans htα hαy) hyt
      rw [h1]; exact hyD
  -- every interval `(z, α)` below `α` contains a point of the complement
  have hgap : ∀ z : M, z < α → ∃ z' ∈ Dᶜ, z < z' ∧ z' < α := by
    intro z hz
    by_contra hc
    have hmem : ∀ z' : M, z < z' → z' < α → z' ∈ D := by
      intro z' h1 h2
      by_contra h3
      exact hc ⟨z', Set.mem_compl h3, h1, h2⟩
    have hmidD : (z + α) / 2 ∈ D := hmem _ (by linarith) (by linarith)
    have hmidJ : (z + α) / 2 ∈ comp D y := by
      refine ⟨hmidD, ?_, ?_⟩
      · intro t hmt hty
        by_cases htα : t ≤ α
        · rcases lt_or_eq_of_le htα with h | h
          · exact hmem t (by linarith) h
          · rw [h]; exact hαD
        · exact comp_subset D y (comp_of_isGLB_le hJ hyD t (lt_of_not_ge htα) hty)
      · intro t hyt htm
        exact absurd (le_trans hαy hyt) (not_le.mpr (lt_of_le_of_lt htm (by linarith)))
    exact absurd (hJ.1 hmidJ) (not_le.mpr (by linarith))
  rw [mem_supSet]
  refine ⟨by simpa using hαD, ?_, ?_⟩
  · obtain ⟨z, hz1, hz2⟩ := hgap (α - 1) (by linarith)
    exact ⟨z, hz1, hz2.2⟩
  · intro z hz
    exact hgap z hz

theorem mem_maxSet_compl_of_isGLB_comp_notMem {D : Set M} {y α : M} (hyD : y ∈ D)
    (hJ : IsGLB (comp D y) α) (hαD : α ∉ D) : α ∈ maxSet Dᶜ := by
  rw [mem_maxSet]
  refine ⟨Set.mem_compl hαD, ?_⟩
  intro y' hy' hαy'
  have hhex : ∃ s ∈ comp D y, s < y' := by
    by_contra hc
    have hle : y' ∈ lowerBounds (comp D y) :=
      mem_lowerBounds.mpr fun s hs => le_of_not_gt fun h => hc ⟨s, hs, h⟩
    exact absurd (hJ.2 hle) (not_le.mpr hαy')
  obtain ⟨s, hsJ, hsy'⟩ := hhex
  have hsD : s ∈ D := comp_subset D y hsJ
  have hαs : α < s := lt_of_le_of_ne (hJ.1 hsJ) (fun h => hαD (h ▸ hsD))
  exact ⟨s, hαs, hsy', fun h => h hsD⟩

private lemma empty_definable_one : (∅ : Set M).Definable₁ LRc ({1} : Set M) := by
  rw [Set.Definable₁, Set.empty_definable_iff]
  refine ⟨(lhomWithConstants (Language.ring.sum rexpL) ℝ).onFormula
    ((LHom.sumInl : Language.ring →ᴸ Language.ring.sum rexpL).onFormula
      ((Term.var (0 : Fin 1)).equal (1 : Language.ring.Term (Fin 1)))), ?_⟩
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  rw [LHom.realize_onFormula, LHom.realize_onFormula, Formula.realize_equal]
  simp only [Term.realize_var]
  rw [Ring.realize_one v]

private lemma empty_definable_zero : (∅ : Set M).Definable₁ LRc ({0} : Set M) := by
  rw [Set.Definable₁, Set.empty_definable_iff]
  refine ⟨(lhomWithConstants (Language.ring.sum rexpL) ℝ).onFormula
    ((LHom.sumInl : Language.ring →ᴸ Language.ring.sum rexpL).onFormula
      ((Term.var (0 : Fin 1)).equal (0 : Language.ring.Term (Fin 1)))), ?_⟩
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  rw [LHom.realize_onFormula, LHom.realize_onFormula, Formula.realize_equal]
  simp only [Term.realize_var]
  rw [Ring.realize_zero v]

/-- `Work.WilC4`'s `DefinableElt` with no extra parameters is `Work.WilC2`'s `Dcl`. -/
private lemma definableElt_iff_definable₁ {A : Set M} {x : M} :
    Work.WilC4.DefinableElt A ∅ x ↔ A.Definable₁ LRc ({x} : Set M) := by
  have hset : {v : Fin 1 → M | v 0 ∈ ({x} : Set M)} = {fun _ : Fin 1 => x} := by
    ext v; simp [funext_iff]
  unfold Work.WilC4.DefinableElt
  rw [Set.union_empty, Set.Definable₁, hset]

theorem dclClosure_ring {A : Set M} (hA : Dcl A ⊆ A) :
    (0 : M) ∈ A ∧ (1 : M) ∈ A ∧ (∀ x ∈ A, -x ∈ A) ∧
      (∀ x ∈ A, x / 2 ∈ A) ∧ (∀ x ∈ A, ∀ y ∈ A, x + y ∈ A) := by
  have hmem : ∀ ⦃x : M⦄, x ∈ A → Work.WilC4.Dcl A ∅ x := fun {x} hx =>
    definableElt_iff_definable₁.mpr
      ((Set.Definable.singleton LRc x).mono (Set.singleton_subset_iff.mpr hx))
  have h1 : (1 : M) ∈ A := hA (mem_dcl.mpr (empty_definable_one.mono (Set.empty_subset A)))
  have h0 : (0 : M) ∈ A := hA (mem_dcl.mpr (empty_definable_zero.mono (Set.empty_subset A)))
  have h2d : Work.WilC4.Dcl A ∅ (2 : M) := by
    have h := Work.WilC4.dcl_add (hmem h1) (hmem h1)
    have h2 : (2 : M) = 1 + 1 := by norm_num
    rwa [h2]
  have h2ne : (2 : M) ≠ 0 := ne_of_gt (two_pos : (0 : M) < 2)
  have hhalf : Work.WilC4.Dcl A ∅ ((2 : M)⁻¹) := Work.WilC4.dcl_inv h2d h2ne
  refine ⟨h0, h1, ?_, ?_, ?_⟩
  · intro x hx
    exact hA (mem_dcl.mpr (definableElt_iff_definable₁.mp (Work.WilC4.dcl_neg (hmem hx))))
  · intro x hx
    have h := Work.WilC4.dcl_mul (hmem hx) hhalf
    rw [div_eq_mul_inv]
    exact hA (mem_dcl.mpr (definableElt_iff_definable₁.mp h))
  · intro x hx y hy
    exact hA (mem_dcl.mpr (definableElt_iff_definable₁.mp
      (Work.WilC4.dcl_add (hmem hx) (hmem hy))))

/-! ## The key lemma: a `dcl`-closed parameter set meets every nonempty definable set -/

/-- **Key lemma.**  In a model `M ⊨ TR` (o-minimal by `hOM`), a set `A` of parameters with
`Dcl A ⊆ A` meets every nonempty `A`-definable subset of `M`. -/
theorem meetsDefinable_of_dclClosed (hOM : WilkiesDesign.CG.OMinModels) {A : Set M} [M ⊨ TR]
    (hA : Dcl A ⊆ A) : FirstOrder.Language.MeetsDefinable (L := LRc) A := by
  intro D hDne hDdef
  by_contra hcon
  -- ## 1. `D` is a finite union of order-convex pieces: `maxSet D` and `supSet D` are finite and
  -- `A`-definable, hence contained in `A`.
  have hDuniv : (Set.univ : Set M).Definable LRc {v : Fin 1 → M | v 0 ∈ D} :=
    hDdef.mono (Set.subset_univ A)
  obtain ⟨s, hsord, hscov⟩ := hOM M {v : Fin 1 → M | v 0 ∈ D} hDuniv
  have hDcov : D = ⋃₀ (s : Set (Set M)) := by
    ext y
    have h := Set.ext_iff.mp hscov (fun _ : Fin 1 => y)
    simpa using h
  have hfinD := finite_maxSet_supSet hsord hDcov
  have hdefD := definable_maxSet_supSet ‹M ⊨ TR› hDdef
  have hmaxA : maxSet D ⊆ A := fun e he =>
    hA (mem_dcl.mpr (finite_definable_singleton ‹M ⊨ TR› hdefD.1 hfinD.1 e he))
  have hsupA : supSet D ⊆ A := fun e he =>
    hA (mem_dcl.mpr (finite_definable_singleton ‹M ⊨ TR› hdefD.2 hfinD.2 e he))
  -- ## 2. The same for the complement `Dᶜ`
  have hDcdef : A.Definable₁ LRc Dᶜ := by
    have hset : {v : Fin 1 → M | v 0 ∈ Dᶜ} = {v : Fin 1 → M | v 0 ∈ D}ᶜ := by
      ext v; simp
    rw [Set.Definable₁, hset]
    exact hDdef.compl
  have hDcuniv : (Set.univ : Set M).Definable LRc {v : Fin 1 → M | v 0 ∈ Dᶜ} :=
    hDcdef.mono (Set.subset_univ A)
  obtain ⟨s', hsord', hscov'⟩ := hOM M {v : Fin 1 → M | v 0 ∈ Dᶜ} hDcuniv
  have hDccov : Dᶜ = ⋃₀ (s' : Set (Set M)) := by
    ext y
    have h := Set.ext_iff.mp hscov' (fun _ : Fin 1 => y)
    simpa using h
  have hfinDc := finite_maxSet_supSet hsord' hDccov
  have hdefDc := definable_maxSet_supSet ‹M ⊨ TR› hDcdef
  have hmaxAc : maxSet Dᶜ ⊆ A := fun e he =>
    hA (mem_dcl.mpr (finite_definable_singleton ‹M ⊨ TR› hdefDc.1 hfinDc.1 e he))
  have hsupAc : supSet Dᶜ ⊆ A := fun e he =>
    hA (mem_dcl.mpr (finite_definable_singleton ‹M ⊨ TR› hdefDc.2 hfinDc.2 e he))
  -- ## 3. A point `y ∈ D` and its component `J = comp D y`
  obtain ⟨y, hyD⟩ := hDne
  have hyA : y ∉ A := fun h => hcon ⟨y, hyD, h⟩
  obtain ⟨h0A, h1A, hnegA, hhalfA, haddA⟩ := dclClosure_ring (M := M) (A := A) hA
  have hJdef : (A ∪ {y}).Definable₁ LRc (comp D y) := definable_comp ‹M ⊨ TR› hDdef
  have hyJ : y ∈ comp D y := mem_comp_self hyD
  -- ## 4. Case analysis
  by_cases hmin : ∃ x ∈ comp D y, x < y
  · by_cases hmax : ∃ x ∈ comp D y, y < x
    · -- `y` is an interior point of its component
      obtain ⟨xlo, hxloJ, hxloy⟩ := hmin
      obtain ⟨xhi, hxhiJ, hyxhi⟩ := hmax
      by_cases hbddA : ∃ u : M, ∀ a ∈ comp D y, a ≤ u
      · -- the component is bounded above, with supremum `β`
        obtain ⟨β, hβLUB, -⟩ := Work.WilC4.sup_exists_dcl ‹M ⊨ TR› hJdef ⟨y, hyJ⟩ hbddA
        have hyβ : y < β := lt_of_lt_of_le hyxhi (hβLUB.1 hxhiJ)
        have hβA : β ∈ A := by
          by_cases hβD : β ∈ D
          · exact hmaxA (mem_maxSet_of_isLUB_comp hyD hβLUB hβD)
          · exact hsupA (mem_supSet_of_isLUB_comp hyD hβLUB hβD hyβ)
        have hup : ∀ t, y < t → t < β → t ∈ comp D y := comp_of_lt_isLUB hβLUB hyD
        by_cases hbddB : ∃ l : M, ∀ a ∈ comp D y, l ≤ a
        · -- the component is bounded below too, with infimum `α`
          obtain ⟨α, hαGLB, -⟩ := inf_exists_definable₁ ‹M ⊨ TR› hJdef ⟨y, hyJ⟩ hbddB
          have hαy : α < y := lt_of_le_of_lt (hαGLB.1 hxloJ) hxloy
          have hαA : α ∈ A := by
            by_cases hαD : α ∈ D
            · exact hsupAc (mem_supSet_compl_of_isGLB_comp_mem hyD hαGLB hαD)
            · exact hmaxAc (mem_maxSet_compl_of_isGLB_comp_notMem hyD hαGLB hαD)
          have hαβ : α < β := lt_trans hαy hyβ
          have hmidJ : (α + β) / 2 ∈ comp D y :=
            comp_of_between hαGLB hβLUB (by linarith) (by linarith)
          exact hcon ⟨(α + β) / 2, comp_subset D y hmidJ,
            hhalfA _ (haddA α hαA β hβA)⟩
        · -- the component is unbounded below: `β - 1` works
          push_neg at hbddB
          have hbelow : ∀ t, t ≤ y → t ∈ comp D y :=
            comp_of_unboundedBelow hyD (fun z => by
              obtain ⟨a, haJ, haz⟩ := hbddB z
              exact ⟨a, haJ, haz⟩)
          have hβm1A : β - 1 ∈ A := by
            simpa [sub_eq_add_neg] using haddA β hβA (-1) (hnegA 1 h1A)
          rcases le_or_gt (β - 1) y with hle | hlt
          · exact hcon ⟨β - 1, comp_subset D y (hbelow _ hle), hβm1A⟩
          · exact hcon ⟨β - 1, comp_subset D y (hup _ hlt (by linarith)), hβm1A⟩
      · -- the component is unbounded above
        push_neg at hbddA
        have habove : ∀ t, y < t → t ∈ comp D y :=
          comp_of_unboundedAbove hyD (fun z => by
            obtain ⟨a, haJ, haz⟩ := hbddA z
            exact ⟨a, haJ, haz⟩)
        by_cases hbddB : ∃ l : M, ∀ a ∈ comp D y, l ≤ a
        · -- bounded below: `α + 1` works
          obtain ⟨α, hαGLB, -⟩ := inf_exists_definable₁ ‹M ⊨ TR› hJdef ⟨y, hyJ⟩ hbddB
          have hαy : α < y := lt_of_le_of_lt (hαGLB.1 hxloJ) hxloy
          have hαA : α ∈ A := by
            by_cases hαD : α ∈ D
            · exact hsupAc (mem_supSet_compl_of_isGLB_comp_mem hyD hαGLB hαD)
            · exact hmaxAc (mem_maxSet_compl_of_isGLB_comp_notMem hyD hαGLB hαD)
          have hlow : ∀ t, α < t → t ≤ y → t ∈ comp D y := comp_of_isGLB_le hαGLB hyD
          have hα1A : α + 1 ∈ A := haddA α hαA 1 h1A
          rcases le_or_gt (α + 1) y with hle | hlt
          · exact hcon ⟨α + 1, comp_subset D y (hlow _ (by linarith) hle), hα1A⟩
          · exact hcon ⟨α + 1, comp_subset D y (habove _ hlt), hα1A⟩
        · -- unbounded on both sides: everything is in `D`, in particular `0`
          push_neg at hbddB
          have hbelow' : ∀ t, t ≤ y → t ∈ comp D y :=
            comp_of_unboundedBelow hyD (fun z => by
              obtain ⟨a, haJ, haz⟩ := hbddB z
              exact ⟨a, haJ, haz⟩)
          rcases le_or_gt (0 : M) y with h | h
          · exact hcon ⟨0, comp_subset D y (hbelow' _ h), h0A⟩
          · exact hcon ⟨0, comp_subset D y (habove _ h), h0A⟩
    · -- `y` is the maximum of its component, hence `y ∈ maxSet D ⊆ A`
      push_neg at hmax
      exact hcon ⟨y, hyD,
        hmaxA (mem_maxSet_of_max_comp hyD (fun x hx => hmax x hx))⟩
  · -- `y` is the minimum of its component, hence `y ∈ supSet Dᶜ ⊆ A`
    push_neg at hmin
    have hGLB : IsGLB (comp D y) y := ⟨hmin, fun b hb => hb hyJ⟩
    exact hcon ⟨y, hyD, hsupAc (mem_supSet_compl_of_isGLB_comp_mem hyD hGLB hyD)⟩

/-! ## The theorem -/

theorem model_TR_of_dcl_closed (hOM : WilkiesDesign.CG.OMinModels) {M : Type} [Field M]
    [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M]
    [FirstOrder.Language.Structure WilkiesDesign.CG.rexpL M]
    [FirstOrder.Language.Structure (FirstOrder.Language.constantsOn ℝ) M]
    [FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR]
    (S : FirstOrder.Language.Substructure WilkiesDesign.CG.LRc M)
    (hS : Work.WilC2.Dcl (S : Set M) ⊆ S) :
    FirstOrder.Language.Theory.Model S WilkiesDesign.CG.TR := by
  have hmeet : FirstOrder.Language.MeetsDefinable (L := LRc) (S : Set M) :=
    meetsDefinable_of_dclClosed hOM hS
  have helem : S.IsElementary := by
    have h := FirstOrder.Language.MeetsDefinable.isElementary_closure (L := LRc) (M := M)
      (A := (S : Set M)) hmeet
    rwa [Substructure.closure_eq] at h
  exact (FirstOrder.Language.ElementarySubstructure.theory_model_iff ⟨S, helem⟩ TR).mpr
    (inferInstance : M ⊨ TR)

end Work.WilC5
