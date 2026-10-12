import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.B13Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.ae_upd2_res_compl`

A null-set (Fubini) statement about the two-slot update map of the configuration space.

For a pair of slots `p = (p.1, p.2)` with `p.1 ≠ p.2` and a null measurable set
`N ⊆ (Fin n → ℝ³)`, for almost every `y` (the value at the slot `p.1`) and almost every
`z = (x', w) : Fib1 p × ℝ³` (the coordinates other than `p.2`, and the value at the slot
`p.2`), the full configuration `upd2 p y z.2 (res p z.1)` (slots `p.1`, `p.2` set to `y`,
`z.2`, all other slots taken from `z.1`) is outside `N`.

The mathematical content is that the coordinate map
`(y, x', w) ↦ upd2 p y w (res p x')` is a *coordinate collapse*: it inserts `y` at the slot
`p.1` and forgets the existing value of `x'` at that slot.  Since a.e. the section of a null
set at a fixed value of a collapsing coordinate is null (`Measure.prod_apply`), the pullback
of `N` is null.

The proof is done in general form (an arbitrary finite index type `ι`, an arbitrary slot
`a : ι` and a second slot `b : {k // k ≠ a}`), the peel equivalence `peelE` being the standard
one-coordinate splitting; the target is then the instance `ι = Fin n`, `a = p.2`,
`b = ⟨p.1, _⟩`.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The one-coordinate peel -/

/-- Peel off the coordinate `a` of `ι → E3`. -/
def peelE (a : ι) : (ι → E3) ≃ᵐ E3 × ({k : ι // k ≠ a} → E3) := by
  letI : Unique {k : ι // k = a} := uniqueOfSubsingleton ⟨a, rfl⟩
  exact (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => E3) (fun k : ι => k = a)).trans
    ((MeasurableEquiv.funUnique {k : ι // k = a} E3).prodCongr (MeasurableEquiv.refl _))

/-- The value of `fibreIns` at its insertion slot. -/
theorem fibreIns_apply_self (a : ι) (w : E3) (u : {k : ι // k ≠ a} → E3) :
    fibreIns a w u a = w := by
  show (if h : a = a then w else u ⟨a, h⟩) = w
  simp

/-- The value of `fibreIns` away from its insertion slot. -/
theorem fibreIns_apply_ne (a : ι) (w : E3) (u : {k : ι // k ≠ a} → E3) {k : ι} (h : k ≠ a) :
    fibreIns a w u k = u ⟨k, h⟩ := by
  show (if h : k = a then w else u ⟨k, h⟩) = u ⟨k, h⟩
  simp [h]

theorem peelE_apply (a : ι) (x : ι → E3) :
    peelE (ι := ι) a x = (x a, fun k : {k : ι // k ≠ a} => x k.1) := by
  simp only [peelE, MeasurableEquiv.trans_apply, MeasurableEquiv.piEquivPiSubtypeProd_apply,
    MeasurableEquiv.prodCongr, MeasurableEquiv.funUnique]
  rfl

theorem peelE_symm_apply (a : ι) (p : E3 × ({k : ι // k ≠ a} → E3)) :
    (peelE (ι := ι) a).symm p = fibreIns a p.1 p.2 := by
  refine (Equiv.symm_apply_eq (peelE (ι := ι) a).toEquiv).mpr ?_
  change p = peelE (ι := ι) a (fibreIns a p.1 p.2)
  rw [peelE_apply]
  refine Prod.ext ?_ ?_
  · show p.1 = fibreIns a p.1 p.2 a
    rw [fibreIns_apply_self]
  · funext k
    show p.2 k = fibreIns a p.1 p.2 k.1
    rw [fibreIns_apply_ne a p.1 p.2 k.2]

theorem peelE_fun_eq (a : ι) :
    ⇑(peelE (ι := ι) a) = fun x : ι → E3 =>
      Prod.map (⇑(MeasurableEquiv.funUnique {k : ι // k = a} E3)) id
        (⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => E3) (fun k : ι => k = a)) x) := by
  funext x
  rw [peelE_apply, MeasurableEquiv.piEquivPiSubtypeProd_apply, Prod.map_apply,
    MeasurableEquiv.funUnique_apply]
  rfl

theorem measurePreserving_peelE (a : ι) :
    MeasurePreserving (peelE (ι := ι) a) (volume : Measure (ι → E3))
      (volume : Measure (E3 × ({k : ι // k ≠ a} → E3))) := by
  letI : Unique {k : ι // k = a} := uniqueOfSubsingleton ⟨a, rfl⟩
  letI : Fintype {k : ι // k = a} := Subtype.fintype (fun k : ι => k = a)
  have h₁ := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => E3) (fun k : ι => k = a)
  have h₂ := volume_preserving_piUnique (fun _ : {k : ι // k = a} => E3)
  have h₃ := h₂.prod (MeasurePreserving.id (volume : Measure ({k : ι // ¬(k = a)} → E3)))
  refine (h₃.comp h₁).congr (peelE (ι := ι) a).measurable ?_
  filter_upwards with x
  exact congrFun (peelE_fun_eq (ι := ι) a) x

/-- Updating the coordinate `a` of `x` to `y` and then peeling at `a`. -/
theorem peelE_update (a : ι) (x : ι → E3) (y : E3) :
    peelE (ι := ι) a (Function.update x a y) = (y, (peelE (ι := ι) a x).2) := by
  rw [peelE_apply, peelE_apply]
  refine Prod.ext ?_ ?_
  · exact Function.update_self a y x
  · funext j
    exact Function.update_of_ne j.2 y x

/-- `fibreIns` of the restriction of `x` is the update of `x` at `a`. -/
theorem fibreIns_restrict_eq_update (a : ι) (x : ι → E3) (y : E3) :
    fibreIns a y (fun j : {k : ι // k ≠ a} => x j.1) = Function.update x a y := by
  funext k
  by_cases h : k = a
  · subst h
    rw [fibreIns_apply_self, Function.update_self]
  · rw [fibreIns_apply_ne a y _ h, Function.update_of_ne h]

/-- Updating `fibreIns` at its insertion slot. -/
theorem fibreIns_update_left {a : ι} (w y : E3) (u : {k : ι // k ≠ a} → E3) :
    Function.update (fibreIns a w u) a y = fibreIns a y u := by
  funext k
  by_cases h : k = a
  · subst h
    rw [Function.update_self, fibreIns_apply_self]
  · rw [Function.update_of_ne h, fibreIns_apply_ne a w u h, fibreIns_apply_ne a y u h]

/-- Measurability of the insertion. -/
theorem measurable_fibreIns_prod' (a : ι) :
    Measurable (fun q : E3 × ({k : ι // k ≠ a} → E3) => fibreIns a q.1 q.2) := by
  refine measurable_pi_iff.mpr (fun k => ?_)
  by_cases h : k = a
  · have hfun : (fun q : E3 × ({k : ι // k ≠ a} → E3) => fibreIns a q.1 q.2 k) = fun q => q.1 := by
      funext q
      rw [h, fibreIns_apply_self]
    rw [hfun]
    exact measurable_fst
  · have hfun : (fun q : E3 × ({k : ι // k ≠ a} → E3) => fibreIns a q.1 q.2 k)
        = fun q => q.2 ⟨k, h⟩ := by
      funext q
      rw [fibreIns_apply_ne a q.1 q.2 h]
    rw [hfun]
    exact (measurable_pi_apply (⟨k, h⟩ : {k : ι // k ≠ a})).comp measurable_snd

/-- Measurability of the swapped insertion. -/
theorem measurable_fibreIns_swap (a : ι) :
    Measurable (fun s : ({k : ι // k ≠ a} → E3) × E3 => fibreIns a s.2 s.1) := by
  have h2 : Measurable (fun s : ({k : ι // k ≠ a} → E3) × E3 => (s.2, s.1)) :=
    measurable_snd.prodMk measurable_fst
  have h3 := (measurable_fibreIns_prod' (ι := ι) a).comp h2
  exact h3

/-! ## The collapse (peel at `b` and reassociate) -/

/-- The collapse map `(x', w) ↦ (x' b, (x' restricted, w))`. -/
def collapseE (b : ι) : ((ι → E3) × E3) ≃ᵐ E3 × (({j : ι // j ≠ b} → E3) × E3) where
  toEquiv :=
    { toFun := fun s => (s.1 b, ((fun j : {j : ι // j ≠ b} => s.1 j.1), s.2))
      invFun := fun r => (fibreIns b r.1 r.2.1, r.2.2)
      left_inv := by
        intro s
        show (fibreIns b (s.1 b) (fun j : {j : ι // j ≠ b} => s.1 j.1), s.2) = s
        refine Prod.ext ?_ ?_
        · change fibreIns b (s.1 b) (fun j : {j : ι // j ≠ b} => s.1 j.1) = s.1
          funext k
          by_cases h : k = b
          · rw [h, fibreIns_apply_self]
          · rw [fibreIns_apply_ne b (s.1 b) _ h]
        · rfl
      right_inv := by
        intro r
        refine Prod.ext ?_ ?_
        · show fibreIns b r.1 r.2.1 b = r.1
          rw [fibreIns_apply_self]
        · refine Prod.ext ?_ ?_
          · funext j
            show fibreIns b r.1 r.2.1 j.1 = r.2.1 j
            rw [fibreIns_apply_ne b r.1 r.2.1 j.2]
          · rfl }
  measurable_toFun := by
    have h1 : Measurable (fun s : (ι → E3) × E3 => s.1 b) :=
      (measurable_pi_apply b).comp measurable_fst
    have h2 : Measurable (fun s : (ι → E3) × E3 => fun j : {j : ι // j ≠ b} => s.1 j.1) :=
      measurable_pi_iff.mpr (fun j => (measurable_pi_apply j.1).comp measurable_fst)
    exact h1.prodMk (h2.prodMk measurable_snd)
  measurable_invFun := by
    have h2 : Measurable (fun r : E3 × (({j : ι // j ≠ b} → E3) × E3) => (r.1, r.2.1)) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have hfib : Measurable (fun r : E3 × (({j : ι // j ≠ b} → E3) × E3) =>
        fibreIns b r.1 r.2.1) := by
      have h3 := (measurable_fibreIns_prod' (ι := ι) b).comp h2
      exact h3
    exact hfib.prodMk (measurable_snd.comp measurable_snd)

theorem collapseE_apply (b : ι) (s : (ι → E3) × E3) :
    collapseE (ι := ι) b s = (s.1 b, ((fun j : {j : ι // j ≠ b} => s.1 j.1), s.2)) := rfl

theorem collapseE_symm_apply (b : ι) (r : E3 × (({j : ι // j ≠ b} → E3) × E3)) :
    (collapseE (ι := ι) b).symm r = (fibreIns b r.1 r.2.1, r.2.2) := rfl

theorem measurePreserving_collapseE (b : ι) :
    MeasurePreserving (collapseE (ι := ι) b) (volume : Measure ((ι → E3) × E3))
      (volume : Measure (E3 × (({j : ι // j ≠ b} → E3) × E3))) := by
  have h₁ : MeasurePreserving (fun s : (ι → E3) × E3 => (peelE (ι := ι) b s.1, s.2))
      (volume : Measure ((ι → E3) × E3))
      (volume : Measure ((E3 × ({j : ι // j ≠ b} → E3)) × E3)) :=
    (measurePreserving_peelE (ι := ι) b).prod (MeasurePreserving.id (volume : Measure E3))
  have h₂ : MeasurePreserving (MeasurableEquiv.prodAssoc)
      (volume : Measure ((E3 × ({j : ι // j ≠ b} → E3)) × E3))
      (volume : Measure (E3 × (({j : ι // j ≠ b} → E3) × E3))) :=
    volume_preserving_prodAssoc
  refine (h₂.comp h₁).congr (collapseE (ι := ι) b).measurable ?_
  filter_upwards with s
  rfl

/-- The image of the update-collapse set under the collapse equivalence. -/
theorem collapseE_image_update (b : ι) {A : Set ((ι → E3) × E3)} (y : E3) :
    collapseE (ι := ι) b '' {s : (ι → E3) × E3 | (Function.update s.1 b y, s.2) ∈ A}
      = Set.univ ×ˢ (Prod.mk y ⁻¹' ((collapseE (ι := ι) b).symm ⁻¹' A)) := by
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨trivial, ?_⟩
    rw [Set.mem_preimage, collapseE_apply]
    show (fibreIns b y (fun j : {j : ι // j ≠ b} => s.1 j.1), s.2) ∈ A
    rw [fibreIns_restrict_eq_update]
    exact hs
  · rintro ⟨-, hz⟩
    simp only [Set.mem_preimage] at hz
    have hz' : (fibreIns b y z.2.1, z.2.2) ∈ A := by
      simpa only [collapseE_symm_apply] using hz
    refine ⟨(collapseE (ι := ι) b).symm z, ?_, MeasurableEquiv.apply_symm_apply _ z⟩
    show (Function.update ((collapseE (ι := ι) b).symm z).1 b y,
      ((collapseE (ι := ι) b).symm z).2) ∈ A
    rw [collapseE_symm_apply, fibreIns_update_left]
    exact hz'

/-- **The collapse lemma.** The pullback of a null set under the collapsing update map is
null. -/
theorem volume_update_collapse_eq_zero (b : ι) {A : Set ((ι → E3) × E3)}
    (hA : MeasurableSet A) (hA0 : (volume : Measure ((ι → E3) × E3)) A = 0) :
    (volume : Measure (E3 × ((ι → E3) × E3)))
      {q | (Function.update q.2.1 b q.1, q.2.2) ∈ A} = 0 := by
  classical
  have hE := measurePreserving_collapseE (ι := ι) b
  have hupd : Measurable (fun q : E3 × ((ι → E3) × E3) => Function.update q.2.1 b q.1) := by
    have h2 : Measurable (fun q : E3 × ((ι → E3) × E3) => (q.2.1, q.1)) :=
      (measurable_fst.comp measurable_snd).prodMk measurable_fst
    have h3 := (measurable_update' (X := fun _ : ι => E3) (a := b)).comp h2
    exact h3
  have hSmeas : MeasurableSet {q : E3 × ((ι → E3) × E3) |
      (Function.update q.2.1 b q.1, q.2.2) ∈ A} :=
    hA.preimage (hupd.prodMk (measurable_snd.comp measurable_snd))
  have hA'meas : MeasurableSet ((collapseE (ι := ι) b).symm ⁻¹' A) :=
    hA.preimage (collapseE (ι := ι) b).symm.measurable
  have hA'0 : (volume : Measure (E3 × (({j : ι // j ≠ b} → E3) × E3)))
      ((collapseE (ι := ι) b).symm ⁻¹' A) = 0 := by
    have h1 : (volume : Measure (E3 × (({j : ι // j ≠ b} → E3) × E3)))
        ((collapseE (ι := ι) b).symm ⁻¹' A) = (volume : Measure ((ι → E3) × E3)) A :=
      MeasurePreserving.measure_preimage_equiv
        (MeasurePreserving.symm (collapseE (ι := ι) b) hE) A
    rw [h1, hA0]
  have hsec : (fun y => (volume : Measure (({j : ι // j ≠ b} → E3) × E3))
      (Prod.mk y ⁻¹' ((collapseE (ι := ι) b).symm ⁻¹' A))) =ᵐ[volume] 0 :=
    (Measure.measure_prod_null hA'meas).mp hA'0
  refine (Measure.measure_prod_null (μ := (volume : Measure E3))
    (ν := (volume : Measure ((ι → E3) × E3))) hSmeas).mpr ?_
  filter_upwards [hsec] with y hy
  have hset : Prod.mk y ⁻¹' {q : E3 × ((ι → E3) × E3) |
        (Function.update q.2.1 b q.1, q.2.2) ∈ A}
      = {s : (ι → E3) × E3 | (Function.update s.1 b y, s.2) ∈ A} := rfl
  rw [hset]
  have him : collapseE (ι := ι) b '' {s : (ι → E3) × E3 | (Function.update s.1 b y, s.2) ∈ A}
      = Set.univ ×ˢ (Prod.mk y ⁻¹' ((collapseE (ι := ι) b).symm ⁻¹' A)) :=
    collapseE_image_update (ι := ι) b (A := A) y
  have hmp : (volume : Measure ((ι → E3) × E3))
        {s : (ι → E3) × E3 | (Function.update s.1 b y, s.2) ∈ A}
      = volume (collapseE (ι := ι) b ''
          {s : (ι → E3) × E3 | (Function.update s.1 b y, s.2) ∈ A}) := by
    have h1 : (volume : Measure ((ι → E3) × E3))
        ((collapseE (ι := ι) b) ⁻¹' (collapseE (ι := ι) b ''
          {s : (ι → E3) × E3 | (Function.update s.1 b y, s.2) ∈ A}))
        = volume (collapseE (ι := ι) b ''
          {s : (ι → E3) × E3 | (Function.update s.1 b y, s.2) ∈ A}) :=
      MeasurePreserving.measure_preimage_equiv hE _
    rw [← h1]
    congr 1
    exact (Equiv.preimage_image (collapseE (ι := ι) b).toEquiv _).symm
  have hsum : (volume : Measure (E3 × (({j : ι // j ≠ b} → E3) × E3)))
      (Set.univ ×ˢ (Prod.mk y ⁻¹' ((collapseE (ι := ι) b).symm ⁻¹' A)))
      = (volume : Measure E3) Set.univ
        * (volume : Measure (({j : ι // j ≠ b} → E3) × E3))
          (Prod.mk y ⁻¹' ((collapseE (ι := ι) b).symm ⁻¹' A)) :=
    Measure.prod_prod _ _
  simp only [Pi.zero_apply] at hy ⊢
  rw [hmp, him, hsum, hy, mul_zero]

/-! ## The general statement -/

/-- The general form: for a null measurable `N` on `ι → E3`, almost every `y` and almost every
`(x', w)` give `fibreIns a w (update x' b y) ∉ N`. -/
theorem ae_fibreIns_update_compl (a : ι) (b : {k : ι // k ≠ a})
    {N : Set (ι → E3)} (hN : MeasurableSet N) (h0 : (volume : Measure (ι → E3)) N = 0) :
    ∀ᵐ y : E3, ∀ᵐ z : ({k : ι // k ≠ a} → E3) × E3,
      fibreIns a z.2 (Function.update z.1 b y) ∉ N := by
  classical
  set A : Set (({k : ι // k ≠ a} → E3) × E3) := {s | fibreIns a s.2 s.1 ∈ N} with hA
  have hAmeas : MeasurableSet A := by
    rw [hA]
    exact hN.preimage (measurable_fibreIns_swap (ι := ι) a)
  have hins : MeasurePreserving (fun q : E3 × ({k : ι // k ≠ a} → E3) => fibreIns a q.1 q.2)
      (volume : Measure (E3 × ({k : ι // k ≠ a} → E3))) (volume : Measure (ι → E3)) :=
    (MeasurePreserving.symm (peelE (ι := ι) a) (measurePreserving_peelE (ι := ι) a)).congr
      (measurable_fibreIns_prod' (ι := ι) a)
      (Filter.Eventually.of_forall fun q => peelE_symm_apply (ι := ι) a q)
  have hA0 : (volume : Measure (({k : ι // k ≠ a} → E3) × E3)) A = 0 := by
    have hswap : MeasurePreserving
        (Prod.swap : (({k : ι // k ≠ a} → E3) × E3) → (E3 × ({k : ι // k ≠ a} → E3)))
        (volume : Measure (({k : ι // k ≠ a} → E3) × E3))
        (volume : Measure (E3 × ({k : ι // k ≠ a} → E3))) :=
      ⟨measurable_swap, Measure.prod_swap⟩
    have hAset : A = Prod.swap ⁻¹'
        ((fun q : E3 × ({k : ι // k ≠ a} → E3) => fibreIns a q.1 q.2) ⁻¹' N) := by
      rw [hA]
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Prod.swap]
    have hnull : NullMeasurableSet
        ((fun q : E3 × ({k : ι // k ≠ a} → E3) => fibreIns a q.1 q.2) ⁻¹' N)
        (volume : Measure (E3 × ({k : ι // k ≠ a} → E3))) :=
      (hN.preimage hins.measurable).nullMeasurableSet
    have h1 : (volume : Measure (({k : ι // k ≠ a} → E3) × E3))
        (Prod.swap ⁻¹' ((fun q : E3 × ({k : ι // k ≠ a} → E3) => fibreIns a q.1 q.2) ⁻¹' N))
        = (volume : Measure (E3 × ({k : ι // k ≠ a} → E3)))
          ((fun q : E3 × ({k : ι // k ≠ a} → E3) => fibreIns a q.1 q.2) ⁻¹' N) :=
      MeasurePreserving.measure_preimage hswap hnull
    have h2 : (volume : Measure (E3 × ({k : ι // k ≠ a} → E3)))
        ((fun q : E3 × ({k : ι // k ≠ a} → E3) => fibreIns a q.1 q.2) ⁻¹' N)
        = (volume : Measure (ι → E3)) N :=
      MeasurePreserving.measure_preimage hins hN.nullMeasurableSet
    rw [hAset, h1, h2, h0]
  have hS0 : (volume : Measure (E3 × (({k : ι // k ≠ a} → E3) × E3)))
      {q | (Function.update q.2.1 b q.1, q.2.2) ∈ A} = 0 :=
    volume_update_collapse_eq_zero (ι := {k : ι // k ≠ a}) b hAmeas hA0
  have hupd : Measurable (fun q : E3 × (({k : ι // k ≠ a} → E3) × E3) =>
      Function.update q.2.1 b q.1) := by
    have h2 : Measurable (fun q : E3 × (({k : ι // k ≠ a} → E3) × E3) => (q.2.1, q.1)) :=
      (measurable_fst.comp measurable_snd).prodMk measurable_fst
    have h3 := (measurable_update' (X := fun _ : {k : ι // k ≠ a} => E3) (a := b)).comp h2
    exact h3
  have hSmeas : MeasurableSet {q : E3 × (({k : ι // k ≠ a} → E3) × E3) |
      (Function.update q.2.1 b q.1, q.2.2) ∈ A} :=
    hAmeas.preimage (hupd.prodMk (measurable_snd.comp measurable_snd))
  have hae : ∀ᵐ q ∂(volume : Measure (E3 × (({k : ι // k ≠ a} → E3) × E3))),
      (Function.update q.2.1 b q.1, q.2.2) ∉ A := by
    rw [MeasureTheory.ae_iff]
    have hset : {q : E3 × (({k : ι // k ≠ a} → E3) × E3) |
          ¬ (Function.update q.2.1 b q.1, q.2.2) ∉ A}
        = {q : E3 × (({k : ι // k ≠ a} → E3) × E3) |
          (Function.update q.2.1 b q.1, q.2.2) ∈ A} := by
      ext q
      simp
    rw [hset]
    exact hS0
  have hgoal := (Measure.ae_prod_iff_ae_ae hSmeas.compl).mp hae
  simpa only [hA, Set.mem_ofPred_eq] using hgoal

/-! ## The target -/

theorem upd2_res_eq_fibreIns_update {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (y : E3) (x' : Fib1 p) (w : E3) :
    upd2 p y w (res p x') = fibreIns p.2 w (Function.update x' ⟨p.1, hp⟩ y) := by
  rw [upd2_eq_fibreIns_upd1]
  congr 1
  funext k
  by_cases h : k.1 = p.1
  · rw [upd1_apply_self k h]
    have hk : k = (⟨p.1, hp⟩ : I1 p) := Subtype.ext h
    rw [hk, Function.update_self]
  · rw [upd1_apply_ne k h]
    have hk : k ≠ (⟨p.1, hp⟩ : I1 p) := fun hc => h (congrArg Subtype.val hc)
    rw [Function.update_of_ne hk]
    rfl

theorem ae_upd2_res_compl {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {N : Set (Fin n → EuclideanSpace ℝ (Fin 3))} (hN : MeasurableSet N) (h0 : MeasureTheory.volume N = 0) : ∀ᵐ y : EuclideanSpace ℝ (Fin 3), ∀ᵐ z : Work.BoseBoxFock.Fib1 p × EuclideanSpace ℝ (Fin 3), Work.BoseBoxFock.upd2 p y z.2 (Work.BoseBoxFock.res p z.1) ∉ N := by
  have hgen := ae_fibreIns_update_compl (ι := Fin n) (a := p.2) (b := (⟨p.1, hp⟩ : I1 p)) hN h0
  simpa only [upd2_res_eq_fibreIns_update p hp] using hgen

end Work.BoseBoxFock
