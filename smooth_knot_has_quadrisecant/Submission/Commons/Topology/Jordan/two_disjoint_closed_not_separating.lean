import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.LocallyConstant.Basic
import Submission.Commons.Topology.Covering.section_of_monodromy_eq_self_weak

open Set Metric
open scoped Topology
open Classical

set_option linter.defProp false
set_option linter.style.haveILetI false

namespace Commons.Topology.Jordan.ClosedDisjoint
namespace QD
noncomputable section
variable {X : Type*} [MetricSpace X] {A B : Set X}

lemma mem_compl_union_of {a : ↥(Aᶜ)} {b : ↥(Bᶜ)} (hab : (a : X) = (b : X)) :
    (a : X) ∈ (A ∪ B)ᶜ := by
  rw [Set.mem_compl_iff, Set.mem_union]
  intro h; rcases h with h | h
  · exact a.2 h
  · rw [hab] at h; exact b.2 h

abbrev Sheet (A B : Set X) := (↥(Aᶜ) × ℤ) ⊕ (↥(Bᶜ) × ℤ)
def glRel (h : ↥((A ∪ B)ᶜ) → ℤ) : Sheet A B → Sheet A B → Prop :=
  fun x y => x = y ∨ ∃ (a : ↥(Aᶜ)) (b : ↥(Bᶜ)) (n : ℤ) (hab : (a : X) = (b : X)),
    ((x = Sum.inl (a, n) ∧ y = Sum.inr (b, n + h ⟨(a : X), mem_compl_union_of hab⟩)) ∨
     (x = Sum.inr (b, n) ∧ y = Sum.inl (a, n - h ⟨(a : X), mem_compl_union_of hab⟩)))
def glSetoid (h : ↥((A ∪ B)ᶜ) → ℤ) : Setoid (Sheet A B) := Relation.EqvGen.setoid (glRel h)
abbrev Tot (h : ↥((A ∪ B)ᶜ) → ℤ) := Quotient (glSetoid h)
def Fst : Sheet A B → X
  | Sum.inl (a, _) => (a : X)
  | Sum.inr (b, _) => (b : X)

def glRel_liftAux {β : Type*} (h : ↥((A ∪ B)ᶜ) → ℤ) (f : Sheet A B → β)
    (hf : ∀ x y, glRel h x y → f x = f y) :
    ∀ a b, (glSetoid h) a b → f a = f b := by
  haveI : IsEquiv (Sheet A B) (fun x y : Sheet A B => f x = f y) :=
    (Equivalence.mk (r := fun x y : Sheet A B => f x = f y) (fun _ => rfl)
      (fun h => h.symm) (fun h1 h2 => h1.trans h2)).isEquiv
  exact fun x y hxy => Relation.EqvGen.eqvGen_le hf x y hxy

def glRel_lift {β : Type*} (h : ↥((A ∪ B)ᶜ) → ℤ) (f : Sheet A B → β)
    (hf : ∀ x y, glRel h x y → f x = f y) : Tot h → β :=
  Quotient.lift f (glRel_liftAux h f hf)

@[simp] lemma glRel_lift_mk {β : Type*} (h : ↥((A ∪ B)ᶜ) → ℤ) (f : Sheet A B → β)
    (hf : ∀ x y, glRel h x y → f x = f y) (x : Sheet A B) :
    glRel_lift h f hf (Quotient.mk _ x) = f x := Quotient.lift_mk f (glRel_liftAux h f hf) x

noncomputable def proj (h : ↥((A ∪ B)ᶜ) → ℤ) : Tot h → X :=
  glRel_lift h Fst (by
    intro x y hg
    rcases hg with hpq | ⟨a, b, n, hab, h1 | h1⟩
    · rw [hpq]
    · rw [h1.1, h1.2]; exact hab
    · rw [h1.1, h1.2]; exact hab.symm)

@[simp] lemma proj_mk (h : ↥((A ∪ B)ᶜ) → ℤ) (x : Sheet A B) :
    proj h (Quotient.mk _ x) = Fst x := glRel_lift_mk h Fst _ x

lemma Fst_eq_of_glRel (h : ↥((A ∪ B)ᶜ) → ℤ) {x y : Sheet A B} (hg : glRel h x y) :
    Fst x = Fst y := by
  rcases hg with hpq | ⟨a, b, n, hab, h1 | h1⟩
  · rw [hpq]
  · rw [h1.1, h1.2]; exact hab
  · rw [h1.1, h1.2]; exact hab.symm

lemma Fst_eq_of_glSetoid (h : ↥((A ∪ B)ᶜ) → ℤ) :
    ∀ x y : Sheet A B, glSetoid h x y → Fst x = Fst y := by
  have hf : ∀ x y : Sheet A B, glRel h x y → Fst x = Fst y :=
    fun x y hxy => Fst_eq_of_glRel h hxy
  haveI : IsEquiv (Sheet A B) (fun x y : Sheet A B => Fst x = Fst y) :=
    (Equivalence.mk (r := fun x y : Sheet A B => Fst x = Fst y) (fun _ => rfl)
      (fun h => h.symm) (fun h1 h2 => h1.trans h2)).isEquiv
  exact fun x y hxy => Relation.EqvGen.eqvGen_le hf x y hxy

lemma Fst_eq_of_glSetoid' (h : ↥((A ∪ B)ᶜ) → ℤ) {x y : Sheet A B} (hg : glSetoid h x y) :
    Fst x = Fst y :=
  Fst_eq_of_glSetoid h x y hg

lemma glue_inl_inr (h : ↥((A ∪ B)ᶜ) → ℤ) {a : ↥(Aᶜ)} {b : ↥(Bᶜ)} (hab : (a : X) = (b : X)) (n : ℤ) :
    Quotient.mk (glSetoid h) (Sum.inl (a, n))
      = Quotient.mk _ (Sum.inr (b, n + h ⟨(a : X), mem_compl_union_of hab⟩)) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (Or.inr ⟨a, b, n, hab, Or.inl ⟨rfl, rfl⟩⟩)

lemma glue_inr_inl (h : ↥((A ∪ B)ᶜ) → ℤ) {a : ↥(Aᶜ)} {b : ↥(Bᶜ)} (hab : (a : X) = (b : X)) (n : ℤ) :
    Quotient.mk (glSetoid h) (Sum.inr (b, n))
      = Quotient.mk _ (Sum.inl (a, n - h ⟨(a : X), mem_compl_union_of hab⟩)) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (Or.inr ⟨a, b, n, hab, Or.inr ⟨rfl, rfl⟩⟩)

lemma fst_continuous : Continuous (Fst : Sheet A B → X) := by
  rw [continuous_sum_dom]
  refine ⟨?_, ?_⟩
  · rw [show (Fst ∘ Sum.inl) = (fun p : ↥(Aᶜ) × ℤ => ((p.1 : ↥(Aᶜ)) : X)) from rfl]; fun_prop
  · rw [show (Fst ∘ Sum.inr) = (fun p : ↥(Bᶜ) × ℤ => ((p.1 : ↥(Bᶜ)) : X)) from rfl]; fun_prop

lemma proj_continuous (h : ↥((A ∪ B)ᶜ) → ℤ) : Continuous (proj h) := by
  rw [Topology.IsQuotientMap.continuous_iff (isQuotientMap_quotient_mk' (s := glSetoid h))]
  change Continuous (proj h ∘ (Quotient.mk (glSetoid h)))
  rw [show proj h ∘ (Quotient.mk (glSetoid h)) = Fst from by funext x; exact proj_mk h x]
  exact fst_continuous

/-- Value of `h` at the underlying point, or 0 if not in `W`. -/
def hval (h : ↥((A ∪ B)ᶜ) → ℤ) (z : X) : ℤ := if hz : z ∈ (A ∪ B)ᶜ then h ⟨z, hz⟩ else 0

lemma hval_of_mem (h : ↥((A ∪ B)ᶜ) → ℤ) {z : X} (hz : z ∈ (A ∪ B)ᶜ) :
    hval h z = h ⟨z, hz⟩ := dif_pos hz

-- coordinate on the first chart
def coord1f (h : ↥((A ∪ B)ᶜ) → ℤ) : Sheet A B → ℤ
  | Sum.inl (_, n) => n
  | Sum.inr (b, m) => m - hval h (b : X)

lemma coord1f_compat (h : ↥((A ∪ B)ᶜ) → ℤ) :
    ∀ x y, glRel h x y → coord1f h x = coord1f h y := by
  intro x y hg
  rcases hg with hpq | ⟨a, b, n, hab, h1 | h1⟩
  · rw [hpq]
  · rw [h1.1, h1.2]
    simp only [coord1f]
    have hv : hval h (b : X) = hval h (a : X) := by rw [hab]
    rw [hv, hval_of_mem h (mem_compl_union_of hab)]
    omega
  · rw [h1.1, h1.2]
    simp only [coord1f]
    have hv : hval h (b : X) = hval h (a : X) := by rw [hab]
    rw [hv, hval_of_mem h (mem_compl_union_of hab)]

def coord1 (h : ↥((A ∪ B)ᶜ) → ℤ) : Tot h → ℤ := glRel_lift h (coord1f h) (coord1f_compat h)

@[simp] lemma coord1_mk (h : ↥((A ∪ B)ᶜ) → ℤ) (x : Sheet A B) :
    coord1 h (Quotient.mk _ x) = coord1f h x := glRel_lift_mk h (coord1f h) _ x

-- coordinate on the second chart
def coord2f (h : ↥((A ∪ B)ᶜ) → ℤ) : Sheet A B → ℤ
  | Sum.inl (a, n) => n + hval h (a : X)
  | Sum.inr (_, m) => m

lemma coord2f_compat (h : ↥((A ∪ B)ᶜ) → ℤ) :
    ∀ x y, glRel h x y → coord2f h x = coord2f h y := by
  intro x y hg
  rcases hg with hpq | ⟨a, b, n, hab, h1 | h1⟩
  · rw [hpq]
  · rw [h1.1, h1.2]
    simp only [coord2f]
    rw [hval_of_mem h (mem_compl_union_of hab)]
  · rw [h1.1, h1.2]
    simp only [coord2f]
    rw [hval_of_mem h (mem_compl_union_of hab)]
    omega

def coord2 (h : ↥((A ∪ B)ᶜ) → ℤ) : Tot h → ℤ := glRel_lift h (coord2f h) (coord2f_compat h)

@[simp] lemma coord2_mk (h : ↥((A ∪ B)ᶜ) → ℤ) (x : Sheet A B) :
    coord2 h (Quotient.mk _ x) = coord2f h x := glRel_lift_mk h (coord2f h) _ x

end
end QD
end Commons.Topology.Jordan.ClosedDisjoint

namespace Commons.Topology.Jordan.ClosedDisjoint
namespace QD
noncomputable section
variable {X : Type*} [MetricSpace X] {A B : Set X} (h : ↥((A ∪ B)ᶜ) → ℤ)

def Phi1 (U : Set X) (hU : U ⊆ Aᶜ) (p : U × ℤ) : ↥(proj h ⁻¹' U) :=
  ⟨Quotient.mk _ (Sum.inl (⟨p.1.1, hU p.1.2⟩, p.2)), by
    show proj h (Quotient.mk _ (Sum.inl (⟨p.1.1, hU p.1.2⟩, p.2))) ∈ U
    rw [proj_mk]; exact p.1.2⟩

def H1 (U : Set X) (hU : U ⊆ Aᶜ) (e : ↥(proj h ⁻¹' U)) : U × ℤ :=
  (⟨proj h e.1, e.2⟩, coord1 h e.1)

lemma H1_Phi1 (U : Set X) (hU : U ⊆ Aᶜ) (p : U × ℤ) : H1 h U hU (Phi1 h U hU p) = p := by
  unfold H1 Phi1
  simp only [proj_mk, coord1_mk, coord1f]
  exact Prod.ext (Subtype.ext rfl) rfl

lemma Phi1_H1 (U : Set X) (hU : U ⊆ Aᶜ) (e : ↥(proj h ⁻¹' U)) : Phi1 h U hU (H1 h U hU e) = e := by
  obtain ⟨q, hq⟩ := e
  apply Subtype.ext
  change Quotient.mk _ (Sum.inl (⟨proj h q, hU hq⟩, coord1 h q)) = q
  revert hq
  induction q using Quotient.inductionOn with
  | h y =>
    intro hq
    cases y with
    | inl p =>
      obtain ⟨a, n⟩ := p
      simp only [proj_mk, coord1_mk, coord1f]
      rfl
    | inr p =>
      obtain ⟨b, m⟩ := p
      simp only [proj_mk, coord1_mk, coord1f]
      have hbW : (b : X) ∈ (A ∪ B)ᶜ := by
        rw [Set.mem_compl_iff, Set.mem_union]; intro hh; rcases hh with hh | hh
        · exact hU hq hh
        · exact b.2 hh
      rw [hval_of_mem h hbW]
      apply Quotient.sound
      refine Relation.EqvGen.rel _ _ (Or.inr ?_)
      refine ⟨(⟨(b:X), hU hq⟩ : ↥(Aᶜ)), b, m - h ⟨(b:X), hbW⟩, rfl, Or.inl ⟨rfl, ?_⟩⟩
      show Sum.inr (b, m) = Sum.inr (b, (m - h ⟨(b:X), hbW⟩) + h ⟨(b:X), mem_compl_union_of (a := (⟨(b:X), hU hq⟩ : ↥(Aᶜ))) (b := b) rfl⟩)
      rw [show h ⟨(b:X), mem_compl_union_of (a := (⟨(b:X), hU hq⟩ : ↥(Aᶜ))) (b := b) rfl⟩ = h ⟨(b:X), hbW⟩ from congrArg h (Subtype.ext rfl)]
      rw [show (m - h ⟨(b:X), hbW⟩) + h ⟨(b:X), hbW⟩ = m from by omega]

end
end QD
end Commons.Topology.Jordan.ClosedDisjoint

namespace Commons.Topology.Jordan.ClosedDisjoint
namespace QD
noncomputable section
variable {X : Type*} [MetricSpace X] {A B : Set X} (h : ↥((A ∪ B)ᶜ) → ℤ)

lemma mem_compl_union2 {z : X} (ha : z ∈ A ᶜ) (hb : z ∈ B ᶜ) : z ∈ (A ∪ B) ᶜ := by
  rw [Set.mem_compl_iff, Set.mem_union]
  intro h; rcases h with h | h
  · exact ha h
  · exact hb h

lemma int_dist_lt_one {a b : ℤ} (h : dist a b < 1) : a = b := by
  have h1 : |a - b| < 1 := by
    rw [Int.dist_eq'] at h
    exact_mod_cast h
  have h2 : a - b = 0 := Int.abs_lt_one_iff.mp h1
  omega

lemma hval_locallyConstant (hh : ∀ z, ContinuousAt h z) (U : Set X) (hU : U ⊆ Aᶜ) :
    IsLocallyConstant (fun b : {b : ↥(Bᶜ) // (b:X) ∈ U} => hval h (b.1 : X)) := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro c
  rw [isOpen_iff_forall_mem_open]
  rintro ⟨b, hbU⟩ hmem
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hmem
  have hbW : (b : X) ∈ (A ∪ B)ᶜ := mem_compl_union2 (hU hbU) b.2
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp (hh ⟨(b:X), hbW⟩) 1 (by norm_num)
  refine ⟨{b' : {b : ↥(Bᶜ) // (b:X) ∈ U} | dist (b'.1 : X) (b:X) < δ}, ?_, ?_, ?_⟩
  · intro b' hb'
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    have hb'W : (b'.1 : X) ∈ (A ∪ B)ᶜ := mem_compl_union2 (hU b'.2) b'.1.2
    rw [hval_of_mem h hb'W, ← hmem, hval_of_mem h hbW]
    exact int_dist_lt_one (hδ' hb')
  · exact isOpen_lt (by fun_prop : Continuous (fun b' : {b : ↥(Bᶜ) // (b:X) ∈ U} => dist (b'.1:X) (b:X))) continuous_const
  · show dist (b:X) (b:X) < δ
    rw [dist_self]; exact hδ

end
end QD
end Commons.Topology.Jordan.ClosedDisjoint

namespace Commons.Topology.Jordan.ClosedDisjoint
namespace QD
noncomputable section
variable {X : Type*} [MetricSpace X] {A B : Set X}

lemma hval_continuousAt (h : ↥((A ∪ B)ᶜ) → ℤ) (hW : IsOpen ((A ∪ B)ᶜ))
    (hh : ∀ z : ↥((A ∪ B)ᶜ), ContinuousAt h z) {z : X} (hz : z ∈ (A ∪ B)ᶜ) :
    ContinuousAt (hval h) z := by
  obtain ⟨ε₁, hε₁, hε₁'⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hz)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp (hh ⟨z, hz⟩) 1 (by norm_num)
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min δ ε₁, lt_min hδ hε₁, fun w hw => ?_⟩
  have hwW : w ∈ (A ∪ B)ᶜ :=
    hε₁' (by rw [Metric.mem_ball]; exact lt_of_lt_of_le hw (min_le_right _ _))
  have hd : dist (⟨w, hwW⟩ : ↥((A ∪ B)ᶜ)) ⟨z, hz⟩ < δ := by
    rw [Subtype.dist_eq]; exact lt_of_lt_of_le hw (min_le_left _ _)
  have heq : h ⟨w, hwW⟩ = h ⟨z, hz⟩ := int_dist_lt_one (hδ' hd)
  rw [hval_of_mem h hwW, hval_of_mem h hz, heq]
  simpa using hε

lemma continuousOn_coord1f (h : ↥((A ∪ B)ᶜ) → ℤ) (hW : IsOpen ((A ∪ B)ᶜ))
    (hh : ∀ z : ↥((A ∪ B)ᶜ), ContinuousAt h z) (U : Set X) (hU : U ⊆ Aᶜ) :
    ContinuousOn (coord1f h) (Fst ⁻¹' U) := by
  intro x hx
  have hpt : ContinuousAt (coord1f h) x := by
    cases x with
    | inl p =>
      rw [← (Topology.IsOpenEmbedding.inl (X := ↥(Aᶜ) × ℤ) (Y := ↥(Bᶜ) × ℤ)).continuousAt_iff]
      show ContinuousAt (fun p : ↥(Aᶜ) × ℤ => p.2) p
      exact continuous_snd.continuousAt
    | inr q =>
      rw [← (Topology.IsOpenEmbedding.inr (X := ↥(Aᶜ) × ℤ) (Y := ↥(Bᶜ) × ℤ)).continuousAt_iff]
      show ContinuousAt (fun q : ↥(Bᶜ) × ℤ => q.2 - hval h (q.1 : X)) q
      have hqW : (q.1 : X) ∈ (A ∪ B)ᶜ := mem_compl_union2 (hU hx) q.1.2
      have hcont1 : ContinuousAt (fun q' : ↥(Bᶜ) × ℤ => ((q'.1 : ↥(Bᶜ)) : X)) q := by fun_prop
      have hcont : ContinuousAt (fun q' : ↥(Bᶜ) × ℤ => hval h (q'.1 : X)) q :=
        ContinuousAt.comp (f := fun q' : ↥(Bᶜ) × ℤ => ((q'.1 : ↥(Bᶜ)) : X)) (x := q)
          (hval_continuousAt h hW hh hqW) hcont1
      exact continuous_snd.continuousAt.sub hcont
  exact hpt.continuousWithinAt

lemma continuous_domRestrict_coord1f (h : ↥((A ∪ B)ᶜ) → ℤ) (hW : IsOpen ((A ∪ B)ᶜ))
    (hh : ∀ z : ↥((A ∪ B)ᶜ), ContinuousAt h z) (U : Set X) (hU : U ⊆ Aᶜ) :
    Continuous ((Fst ⁻¹' U).domRestrict (coord1f h)) :=
  continuousOn_iff_continuous_domRestrict.mp (continuousOn_coord1f h hW hh U hU)

end
end QD
end Commons.Topology.Jordan.ClosedDisjoint

namespace Commons.Topology.Jordan.ClosedDisjoint
namespace QD
noncomputable section
variable {X : Type*} [MetricSpace X] {A B : Set X}

/-- A continuous map out of a quotient, restricted to the image of a saturated subset. -/
theorem continuous_subtype_image_quotient {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    {s : Setoid X} {S : Set X} (hSo : IsOpen S) (hSat : ∀ a b, s a b → a ∈ S → b ∈ S)
    {g : Quotient s → Z} (hg : Continuous fun y : S => g (Quotient.mk s y.1)) :
    Continuous fun t : ↥(Quotient.mk s '' S) => g t.1 := by
  rw [continuous_def]
  intro T hT
  let R : Set X := Quotient.mk s ⁻¹' (g ⁻¹' T)
  obtain ⟨V, hV, hVeq⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp (hg.isOpen_preimage T hT)
  have hVS : V ∩ S = S ∩ R := by
    ext x; constructor
    · rintro ⟨hxV, hxS⟩
      refine ⟨hxS, ?_⟩
      have h1 : (⟨x, hxS⟩ : S) ∈ (Subtype.val ⁻¹' V : Set S) := hxV
      rw [hVeq] at h1
      exact h1
    · rintro ⟨hxS, hxR⟩
      refine ⟨?_, hxS⟩
      have h1 : (⟨x, hxS⟩ : S) ∈ (Subtype.val ⁻¹' V : Set S) := by
        rw [hVeq]; exact hxR
      exact h1
  have hpre : Quotient.mk s ⁻¹' (Quotient.mk s '' (S ∩ R)) = S ∩ R := by
    ext y; constructor
    · rintro ⟨x, hx, hxy⟩
      have hxy' : Quotient.mk s y = Quotient.mk s x := hxy.symm
      refine ⟨hSat x y (Quotient.exact hxy) hx.1, ?_⟩
      show g (Quotient.mk s y) ∈ T
      rw [hxy']; exact hx.2
    · rintro hy
      exact ⟨y, hy, rfl⟩
  have hq : Topology.IsQuotientMap (Quotient.mk (s := s)) :=
    isQuotientMap_quotient_mk' (s := s)
  have hQ : IsOpen (Quotient.mk s '' (S ∩ R)) :=
    hq.isCoinducing.isOpen_preimage.mp
      (by rw [hpre, ← hVS]; exact hV.inter hSo)
  have hgoal : (fun t : ↥(Quotient.mk s '' S) => g t.1) ⁻¹' T
      = Subtype.val ⁻¹' (Quotient.mk s '' (S ∩ R)) := by
    ext t; constructor
    · intro ht
      obtain ⟨x, hxS, hx⟩ := t.2
      refine ⟨x, ⟨hxS, ?_⟩, hx⟩
      show g (Quotient.mk s x) ∈ T
      rw [hx]; exact ht
    · rintro ⟨x, hx, hx'⟩
      show g t.1 ∈ T
      rw [← hx']
      exact hx.2
  rw [hgoal]
  exact hQ.preimage continuous_subtype_val

def Phi2 (h : ↥((A ∪ B)ᶜ) → ℤ) (U : Set X) (hU : U ⊆ Bᶜ) (p : U × ℤ) : ↥(proj h ⁻¹' U) :=
  ⟨Quotient.mk _ (Sum.inr (⟨p.1.1, hU p.1.2⟩, p.2)), by
    show proj h (Quotient.mk _ (Sum.inr (⟨p.1.1, hU p.1.2⟩, p.2))) ∈ U
    rw [proj_mk]; exact p.1.2⟩

def H2 (h : ↥((A ∪ B)ᶜ) → ℤ) (U : Set X) (hU : U ⊆ Bᶜ) (e : ↥(proj h ⁻¹' U)) : U × ℤ :=
  (⟨proj h e.1, e.2⟩, coord2 h e.1)

lemma H2_Phi2 (h : ↥((A ∪ B)ᶜ) → ℤ) (U : Set X) (hU : U ⊆ Bᶜ) (p : U × ℤ) :
    H2 h U hU (Phi2 h U hU p) = p := by
  unfold H2 Phi2
  simp only [proj_mk, coord2_mk, coord2f]
  exact Prod.ext (Subtype.ext rfl) rfl

lemma Phi2_H2 (h : ↥((A ∪ B)ᶜ) → ℤ) (U : Set X) (hU : U ⊆ Bᶜ) (e : ↥(proj h ⁻¹' U)) :
    Phi2 h U hU (H2 h U hU e) = e := by
  obtain ⟨q, hq⟩ := e
  apply Subtype.ext
  change Quotient.mk _ (Sum.inr (⟨proj h q, hU hq⟩, coord2 h q)) = q
  revert hq
  induction q using Quotient.inductionOn with
  | h y =>
    intro hq
    cases y with
    | inr p =>
      obtain ⟨b, m⟩ := p
      simp only [proj_mk, coord2_mk, coord2f]
      rfl
    | inl p =>
      obtain ⟨a, n⟩ := p
      simp only [proj_mk, coord2_mk, coord2f]
      have haW : (a : X) ∈ (A ∪ B)ᶜ := mem_compl_union2 a.2 (hU hq)
      rw [hval_of_mem h haW]
      refine (glue_inr_inl h (a := a) (b := ⟨(a : X), hU hq⟩) rfl
        (n + h ⟨(a : X), haW⟩)).trans ?_
      rw [show (n + h ⟨(a : X), haW⟩)
            - h ⟨(a : X), mem_compl_union_of (a := a) (b := (⟨(a : X), hU hq⟩ : ↥(Bᶜ))) rfl⟩ = n from by
        rw [show h ⟨(a : X), mem_compl_union_of (a := a) (b := (⟨(a : X), hU hq⟩ : ↥(Bᶜ))) rfl⟩
            = h ⟨(a : X), haW⟩ from congrArg h (Subtype.ext rfl)]
        omega]

lemma H1_continuous (h : ↥((A ∪ B)ᶜ) → ℤ) (hW : IsOpen ((A ∪ B)ᶜ))
    (hh : ∀ z : ↥((A ∪ B)ᶜ), ContinuousAt h z) (U : Set X) (hU : U ⊆ Aᶜ) (hUOpen : IsOpen U) :
    Continuous fun t : ↥(Quotient.mk (glSetoid h) '' (Fst ⁻¹' U)) => coord1 h t.1 := by
  refine continuous_subtype_image_quotient (S := Fst ⁻¹' U) (hUOpen.preimage fst_continuous) ?_ ?_
  · intro a b hab ha
    show Fst b ∈ U
    rw [← Fst_eq_of_glSetoid' h hab]; exact ha
  have heq : (fun y : ↥(Fst ⁻¹' U) => coord1 h (Quotient.mk (glSetoid h) y.1))
      = fun y : ↥(Fst ⁻¹' U) => coord1f h y.1 := by
    funext y; exact coord1_mk h y.1
  rw [heq]
  exact continuous_domRestrict_coord1f h hW hh U hU

lemma H2_continuous (h : ↥((A ∪ B)ᶜ) → ℤ) (hW : IsOpen ((A ∪ B)ᶜ))
    (hh : ∀ z : ↥((A ∪ B)ᶜ), ContinuousAt h z) (U : Set X) (hU : U ⊆ Bᶜ) (hUOpen : IsOpen U) :
    Continuous fun t : ↥(Quotient.mk (glSetoid h) '' (Fst ⁻¹' U)) => coord2 h t.1 := by
  refine continuous_subtype_image_quotient (S := Fst ⁻¹' U) (hUOpen.preimage fst_continuous) ?_ ?_
  · intro a b hab ha
    show Fst b ∈ U
    rw [← Fst_eq_of_glSetoid' h hab]; exact ha
  have heq : (fun y : ↥(Fst ⁻¹' U) => coord2 h (Quotient.mk (glSetoid h) y.1))
      = fun y : ↥(Fst ⁻¹' U) => coord2f h y.1 := by
    funext y; exact coord2_mk h y.1
  rw [heq]
  refine (continuousOn_iff_continuous_domRestrict (f := coord2f h) (s := Fst ⁻¹' U)).mp ?_
  intro x hx
  have hpt : ContinuousAt (coord2f h) x := by
    cases x with
    | inr p =>
      rw [← (Topology.IsOpenEmbedding.inr (X := ↥(Aᶜ) × ℤ) (Y := ↥(Bᶜ) × ℤ)).continuousAt_iff]
      show ContinuousAt (fun q : ↥(Bᶜ) × ℤ => q.2) p
      exact continuous_snd.continuousAt
    | inl p =>
      rw [← (Topology.IsOpenEmbedding.inl (X := ↥(Aᶜ) × ℤ) (Y := ↥(Bᶜ) × ℤ)).continuousAt_iff]
      show ContinuousAt (fun q : ↥(Aᶜ) × ℤ => q.2 + hval h (q.1 : X)) p
      have hpW : (p.1 : X) ∈ (A ∪ B)ᶜ := mem_compl_union2 p.1.2 (hU hx)
      have hcont1 : ContinuousAt (fun q : ↥(Aᶜ) × ℤ => ((q.1 : ↥(Aᶜ)) : X)) p := by fun_prop
      have hcont : ContinuousAt (fun q : ↥(Aᶜ) × ℤ => hval h (q.1 : X)) p :=
        ContinuousAt.comp (f := fun q : ↥(Aᶜ) × ℤ => ((q.1 : ↥(Aᶜ)) : X)) (x := p)
          (hval_continuousAt h hW hh hpW) hcont1
      exact continuous_snd.continuousAt.add hcont
  exact hpt.continuousWithinAt

lemma chart1_continuous (h : ↥((A ∪ B)ᶜ) → ℤ) (hW : IsOpen ((A ∪ B)ᶜ))
    (hh : ∀ z : ↥((A ∪ B)ᶜ), ContinuousAt h z) (U : Set X) (hU : U ⊆ Aᶜ) (hUOpen : IsOpen U) :
    Continuous (H1 h U hU) := by
  have hSeteq : Quotient.mk (glSetoid h) '' (Fst ⁻¹' U) = proj h ⁻¹' U := by
    ext t; constructor
    · rintro ⟨y, hy, rfl⟩; rw [Set.mem_preimage, proj_mk]; exact hy
    · intro ht
      obtain ⟨y, rfl⟩ := Quotient.exists_rep t
      refine ⟨y, ?_, rfl⟩
      rw [Set.mem_preimage, proj_mk] at ht
      exact ht
  have hc1 : Continuous fun t : ↥(proj h ⁻¹' U) => coord1 h t.1 := by
    rw [← hSeteq]
    exact H1_continuous h hW hh U hU hUOpen
  have hc2 : Continuous fun t : ↥(proj h ⁻¹' U) => (⟨proj h t.1, t.2⟩ : U) :=
    Continuous.subtype_mk ((proj_continuous h).comp continuous_subtype_val) (fun t => t.2)
  exact hc2.prodMk hc1

lemma chart2_continuous (h : ↥((A ∪ B)ᶜ) → ℤ) (hW : IsOpen ((A ∪ B)ᶜ))
    (hh : ∀ z : ↥((A ∪ B)ᶜ), ContinuousAt h z) (U : Set X) (hU : U ⊆ Bᶜ) (hUOpen : IsOpen U) :
    Continuous (H2 h U hU) := by
  have hSeteq : Quotient.mk (glSetoid h) '' (Fst ⁻¹' U) = proj h ⁻¹' U := by
    ext t; constructor
    · rintro ⟨y, hy, rfl⟩; rw [Set.mem_preimage, proj_mk]; exact hy
    · intro ht
      obtain ⟨y, rfl⟩ := Quotient.exists_rep t
      refine ⟨y, ?_, rfl⟩
      rw [Set.mem_preimage, proj_mk] at ht
      exact ht
  have hc1 : Continuous fun t : ↥(proj h ⁻¹' U) => coord2 h t.1 := by
    rw [← hSeteq]
    exact H2_continuous h hW hh U hU hUOpen
  have hc2 : Continuous fun t : ↥(proj h ⁻¹' U) => (⟨proj h t.1, t.2⟩ : U) :=
    Continuous.subtype_mk ((proj_continuous h).comp continuous_subtype_val) (fun t => t.2)
  exact hc2.prodMk hc1

lemma chart1_continuous_inv (h : ↥((A ∪ B)ᶜ) → ℤ) (U : Set X) (hU : U ⊆ Aᶜ) :
    Continuous (Phi1 h U hU) := by
  have hmem : ∀ p : U × ℤ,
      proj h (Quotient.mk (glSetoid h) (Sum.inl (⟨(⟨p.1.1, hU p.1.2⟩ : ↥(Aᶜ)), p.2⟩))) ∈ U := by
    intro p
    rw [proj_mk]; exact p.1.2
  have hinner : Continuous fun p : U × ℤ =>
      (⟨(⟨p.1.1, hU p.1.2⟩ : ↥(Aᶜ)), p.2⟩ : ↥(Aᶜ) × ℤ) := by
    refine Continuous.prodMk ?_ continuous_snd
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_fst) (fun p => hU p.1.2)
  have hcont : Continuous fun p : U × ℤ =>
      Quotient.mk (glSetoid h) (Sum.inl (⟨(⟨p.1.1, hU p.1.2⟩ : ↥(Aᶜ)), p.2⟩)) :=
    (continuous_quotient_mk' (s := glSetoid h)).comp (continuous_inl.comp hinner)
  exact Continuous.subtype_mk hcont hmem

lemma chart2_continuous_inv (h : ↥((A ∪ B)ᶜ) → ℤ) (U : Set X) (hU : U ⊆ Bᶜ) :
    Continuous (Phi2 h U hU) := by
  have hmem : ∀ p : U × ℤ,
      proj h (Quotient.mk (glSetoid h) (Sum.inr (⟨(⟨p.1.1, hU p.1.2⟩ : ↥(Bᶜ)), p.2⟩))) ∈ U := by
    intro p
    rw [proj_mk]; exact p.1.2
  have hinner : Continuous fun p : U × ℤ =>
      (⟨(⟨p.1.1, hU p.1.2⟩ : ↥(Bᶜ)), p.2⟩ : ↥(Bᶜ) × ℤ) := by
    refine Continuous.prodMk ?_ continuous_snd
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_fst) (fun p => hU p.1.2)
  have hcont : Continuous fun p : U × ℤ =>
      Quotient.mk (glSetoid h) (Sum.inr (⟨(⟨p.1.1, hU p.1.2⟩ : ↥(Bᶜ)), p.2⟩)) :=
    (continuous_quotient_mk' (s := glSetoid h)).comp (continuous_inr.comp hinner)
  exact Continuous.subtype_mk hcont hmem

def chart1 (h : ↥((A ∪ B)ᶜ) → ℤ) (hW : IsOpen ((A ∪ B)ᶜ))
    (hh : ∀ z : ↥((A ∪ B)ᶜ), ContinuousAt h z) (U : Set X) (hU : U ⊆ Aᶜ) (hUOpen : IsOpen U) :
    ↥(proj h ⁻¹' U) ≃ₜ U × ℤ where
  toFun := H1 h U hU
  invFun := Phi1 h U hU
  left_inv e := Phi1_H1 h U hU e
  right_inv p := H1_Phi1 h U hU p
  continuous_toFun := chart1_continuous h hW hh U hU hUOpen
  continuous_invFun := chart1_continuous_inv h U hU

def chart2 (h : ↥((A ∪ B)ᶜ) → ℤ) (hW : IsOpen ((A ∪ B)ᶜ))
    (hh : ∀ z : ↥((A ∪ B)ᶜ), ContinuousAt h z) (U : Set X) (hU : U ⊆ Bᶜ) (hUOpen : IsOpen U) :
    ↥(proj h ⁻¹' U) ≃ₜ U × ℤ where
  toFun := H2 h U hU
  invFun := Phi2 h U hU
  left_inv e := Phi2_H2 h U hU e
  right_inv p := H2_Phi2 h U hU p
  continuous_toFun := chart2_continuous h hW hh U hU hUOpen
  continuous_invFun := chart2_continuous_inv h U hU

end
end QD
end Commons.Topology.Jordan.ClosedDisjoint

namespace Commons.Topology.Jordan.ClosedDisjoint
namespace QD
noncomputable section
variable {X : Type*} [MetricSpace X] {A B : Set X}

lemma compl_left {z : X} (hz : z ∈ (A ∪ B)ᶜ) : z ∈ Aᶜ := fun h => hz (Or.inl h)
lemma compl_right {z : X} (hz : z ∈ (A ∪ B)ᶜ) : z ∈ Bᶜ := fun h => hz (Or.inr h)

lemma tot_nonempty [Nonempty X] (h : ↥((A ∪ B)ᶜ) → ℤ) (hAB : A ⊆ Bᶜ) : Nonempty (Tot h) := by
  by_cases hA : (Aᶜ : Set X).Nonempty
  · obtain ⟨a, ha⟩ := hA
    exact ⟨Quotient.mk (glSetoid h) (Sum.inl (⟨a, ha⟩, 0))⟩
  · have hAempty : Aᶜ = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    obtain ⟨z⟩ := ‹Nonempty X›
    have hzA : z ∈ A := by
      by_contra hz
      have : z ∈ Aᶜ := hz
      rw [hAempty] at this
      exact this
    exact ⟨Quotient.mk (glSetoid h) (Sum.inr (⟨z, hAB hzA⟩, 0))⟩

lemma isEvenlyCovered_chart1 (h : ↥((A ∪ B)ᶜ) → ℤ) (hW : IsOpen ((A ∪ B)ᶜ))
    (hh : ∀ z : ↥((A ∪ B)ᶜ), ContinuousAt h z) (hAc : IsClosed A) {z : X} (hz : z ∈ Aᶜ) :
    IsEvenlyCovered (proj h) z ℤ := by
  obtain ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.mp (hAc.isOpen_compl.mem_nhds hz)
  refine ⟨inferInstance, Metric.ball z ε, Metric.mem_ball_self hε, Metric.isOpen_ball,
    Metric.isOpen_ball.preimage (proj_continuous h),
    chart1 h hW hh (Metric.ball z ε) hε' Metric.isOpen_ball, ?_⟩
  intro e
  rfl

lemma isEvenlyCovered_chart2 (h : ↥((A ∪ B)ᶜ) → ℤ) (hW : IsOpen ((A ∪ B)ᶜ))
    (hh : ∀ z : ↥((A ∪ B)ᶜ), ContinuousAt h z) (hBc : IsClosed B) {z : X} (hz : z ∈ Bᶜ) :
    IsEvenlyCovered (proj h) z ℤ := by
  obtain ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.mp (hBc.isOpen_compl.mem_nhds hz)
  refine ⟨inferInstance, Metric.ball z ε, Metric.mem_ball_self hε, Metric.isOpen_ball,
    Metric.isOpen_ball.preimage (proj_continuous h),
    chart2 h hW hh (Metric.ball z ε) hε' Metric.isOpen_ball, ?_⟩
  intro e
  rfl

theorem isCoveringMap_proj (h : ↥((A ∪ B)ᶜ) → ℤ) (hW : IsOpen ((A ∪ B)ᶜ))
    (hh : ∀ z : ↥((A ∪ B)ᶜ), ContinuousAt h z) (hAc : IsClosed A) (hBc : IsClosed B)
    (hAB : A ⊆ Bᶜ) : IsCoveringMap (proj h) := by
  intro z
  by_cases hz : z ∈ Aᶜ
  · exact (isEvenlyCovered_chart1 h hW hh hAc hz).to_isEvenlyCovered_preimage
  · exact (isEvenlyCovered_chart2 h hW hh hBc (hAB (not_not.mp hz))).to_isEvenlyCovered_preimage

lemma coord2_eq_coord1_add (h : ↥((A ∪ B)ᶜ) → ℤ) {t : Tot h} {z : X}
    (hz : z ∈ (A ∪ B)ᶜ) (ht : proj h t = z) :
    coord2 h t = coord1 h t + h ⟨z, hz⟩ := by
  induction t using Quotient.inductionOn with
  | h y =>
    cases y with
    | inl p =>
      obtain ⟨a, n⟩ := p
      simp only [coord1_mk, coord2_mk, coord1f, coord2f]
      have ht' : (a : X) = z := by rw [proj_mk] at ht; exact ht
      have hz' : (a : X) ∈ (A ∪ B)ᶜ := by rw [ht']; exact hz
      rw [hval_of_mem h hz']
      rw [show h ⟨(a : X), hz'⟩ = h ⟨z, hz⟩ from congrArg h (Subtype.ext ht')]
    | inr p =>
      obtain ⟨b, m⟩ := p
      simp only [coord1_mk, coord2_mk, coord1f, coord2f]
      have ht' : (b : X) = z := by rw [proj_mk] at ht; exact ht
      have hz' : (b : X) ∈ (A ∪ B)ᶜ := by rw [ht']; exact hz
      rw [hval_of_mem h hz']
      rw [show h ⟨(b : X), hz'⟩ = h ⟨z, hz⟩ from congrArg h (Subtype.ext ht')]
      omega

/-- Decomposition of a locally constant `ℤ`-valued function on `(A ∪ B)ᶜ` into a difference of
locally constant functions on `Aᶜ` and `Bᶜ`. -/
theorem exists_decomposition [ConnectedSpace X] [LocallyPathConnectedSpace X]
    (hmono : ∀ z : X, Subsingleton (FundamentalGroup X z))
    (h : ↥((A ∪ B)ᶜ) → ℤ) (hW : IsOpen ((A ∪ B)ᶜ)) (hh : ∀ z : ↥((A ∪ B)ᶜ), ContinuousAt h z)
    (hAc : IsClosed A) (hBc : IsClosed B) (hAB : A ⊆ Bᶜ) (hBA : B ⊆ Aᶜ) :
    ∃ (f : ↥(Aᶜ) → ℤ) (g : ↥(Bᶜ) → ℤ), IsLocallyConstant f ∧ IsLocallyConstant g ∧
      ∀ (z : X) (hz : z ∈ (A ∪ B)ᶜ), h ⟨z, hz⟩ = g ⟨z, compl_right hz⟩ - f ⟨z, compl_left hz⟩ := by
  have hcover : IsCoveringMap (proj h) := isCoveringMap_proj h hW hh hAc hBc hAB
  obtain ⟨e₀⟩ := tot_nonempty h hAB
  obtain ⟨σ, -, hσp⟩ := Commons.Topology.Covering.section_of_monodromy_eq_self_weak hcover e₀
    (by
      intro γ
      haveI : Subsingleton (FundamentalGroup X (proj h e₀)) := hmono _
      have h1 : γ = 1 := Subsingleton.elim γ 1
      rw [h1]
      rw [← IsCoveringMap.coe_monodromyPerm, map_one]
      rfl)
  let f : ↥(Aᶜ) → ℤ := fun a => (H1 h Aᶜ (subset_refl Aᶜ)
    ⟨σ a.1, by rw [Set.mem_preimage, hσp]; exact a.2⟩).2
  let g : ↥(Bᶜ) → ℤ := fun b => (H2 h Bᶜ (subset_refl Bᶜ)
    ⟨σ b.1, by rw [Set.mem_preimage, hσp]; exact b.2⟩).2
  have hf_eq : ∀ (z : X) (hz : z ∈ Aᶜ), f ⟨z, hz⟩ = coord1 h (σ z) := fun z hz => rfl
  have hg_eq : ∀ (z : X) (hz : z ∈ Bᶜ), g ⟨z, hz⟩ = coord2 h (σ z) := fun z hz => rfl
  have hfcont : Continuous f := by
    have hmem : ∀ a : ↥(Aᶜ), σ a.1 ∈ (proj h ⁻¹' Aᶜ : Set (Tot h)) := fun a => by
      rw [Set.mem_preimage, hσp]; exact a.2
    have h1 : Continuous fun a : ↥(Aᶜ) => σ a.1 := σ.continuous.comp continuous_subtype_val
    have hsub : Continuous fun a : ↥(Aᶜ) => (⟨σ a.1, hmem a⟩ : ↥(proj h ⁻¹' Aᶜ)) :=
      Continuous.subtype_mk h1 hmem
    exact continuous_snd.comp ((chart1_continuous h hW hh Aᶜ (subset_refl Aᶜ) hAc.isOpen_compl).comp hsub)
  have hgcont : Continuous g := by
    have hmem : ∀ b : ↥(Bᶜ), σ b.1 ∈ (proj h ⁻¹' Bᶜ : Set (Tot h)) := fun b => by
      rw [Set.mem_preimage, hσp]; exact b.2
    have h1 : Continuous fun b : ↥(Bᶜ) => σ b.1 := σ.continuous.comp continuous_subtype_val
    have hsub : Continuous fun b : ↥(Bᶜ) => (⟨σ b.1, hmem b⟩ : ↥(proj h ⁻¹' Bᶜ)) :=
      Continuous.subtype_mk h1 hmem
    exact continuous_snd.comp ((chart2_continuous h hW hh Bᶜ (subset_refl Bᶜ) hBc.isOpen_compl).comp hsub)
  refine ⟨f, g, ?_, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_continuous]; exact hfcont
  · rw [IsLocallyConstant.iff_continuous]; exact hgcont
  · intro z hz
    have h1 : f ⟨z, compl_left hz⟩ = coord1 h (σ z) := hf_eq z (compl_left hz)
    have h2 : g ⟨z, compl_right hz⟩ = coord2 h (σ z) := hg_eq z (compl_right hz)
    have h3 := coord2_eq_coord1_add h hz (hσp z)
    rw [h2, h1, h3]
    omega

end
end QD
end Commons.Topology.Jordan.ClosedDisjoint

namespace Commons.Topology.Jordan.ClosedDisjoint
namespace QD
noncomputable section
variable {X : Type*} [TopologicalSpace X]

lemma isLocallyConstant_eq_of_joinedIn {F : Set X} {f : ↥F → ℤ}
    (hf : IsLocallyConstant f) {x y : X} (h : JoinedIn F x y) :
    f ⟨x, h.source_mem⟩ = f ⟨y, h.target_mem⟩ := by
  have hx' : x ∈ F := h.source_mem
  have hy' : y ∈ F := h.target_mem
  obtain ⟨γ, hγ⟩ := h
  have hlc : IsLocallyConstant (fun t : unitInterval => f ⟨γ t, hγ t⟩) :=
    hf.comp_continuous (Continuous.subtype_mk γ.continuous hγ)
  have h01 : f ⟨γ 0, hγ 0⟩ = f ⟨γ 1, hγ 1⟩ :=
    hlc.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial
  have e0 : (⟨γ 0, hγ 0⟩ : ↥F) = ⟨x, hx'⟩ := Subtype.ext γ.source
  have e1 : (⟨γ 1, hγ 1⟩ : ↥F) = ⟨y, hy'⟩ := Subtype.ext γ.target
  rw [e0, e1] at h01
  exact h01

end
end QD
end Commons.Topology.Jordan.ClosedDisjoint

namespace Commons.Topology.Jordan

open ClosedDisjoint.QD

/-- **Janiszewski's theorem (simply-connected form).**  In a simply-connected, connected,
locally path-connected metric space `X`, if `A` and `B` are disjoint closed sets and two points
`x, y` outside `A ∪ B` can be joined by a path avoiding `A` and by a path avoiding `B`
respectively, then they can be joined by a path avoiding `A ∪ B`. -/
theorem two_disjoint_closed_not_separating {X : Type*} [MetricSpace X] [ConnectedSpace X]
    [LocallyPathConnectedSpace X]
    (hmono : ∀ z : X, Subsingleton (FundamentalGroup X z))
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hdisj : Disjoint A B) {x y : X} (hx : x ∉ A ∪ B) (hy : y ∉ A ∪ B)
    (hA' : JoinedIn Aᶜ x y) (hB' : JoinedIn Bᶜ x y) : JoinedIn (A ∪ B)ᶜ x y := by
  classical
  by_contra hcon
  let W : Set X := (A ∪ B)ᶜ
  have hW : IsOpen W := (hA.union hB).isOpen_compl
  have hAB : A ⊆ Bᶜ := fun z hz hzB => Set.disjoint_left.mp hdisj hz hzB
  have hBA : B ⊆ Aᶜ := fun z hz hzA => Set.disjoint_left.mp hdisj hzA hz
  let H : ↥W → ℤ := fun w => if JoinedIn W x (w : X) then 1 else 0
  have hHlc : IsLocallyConstant H := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro w
    obtain ⟨V, ⟨hVnhds, hVpc⟩, hVsub⟩ :=
      (LocallyPathConnectedSpace.path_connected_basis (w : X)).mem_iff.mp (hW.mem_nhds w.2)
    refine Filter.mem_of_superset
      ((continuous_subtype_val.continuousAt).preimage_mem_nhds hVnhds) ?_
    intro w' hw'
    have hww' : JoinedIn W (w : X) (w' : X) :=
      ((hVpc.joinedIn (w : X) (mem_of_mem_nhds hVnhds) (w' : X) hw').mono hVsub)
    change (if JoinedIn W x (w' : X) then (1 : ℤ) else 0)
      = (if JoinedIn W x (w : X) then (1 : ℤ) else 0)
    by_cases hcase : JoinedIn W x (w : X)
    · rw [if_pos (hcase.trans hww'), if_pos hcase]
    · rw [if_neg (fun hJ => hcase (hJ.trans hww'.symm)), if_neg hcase]
  have hH : ∀ z : ↥W, ContinuousAt H z :=
    fun z => (IsLocallyConstant.iff_continuous H).mp hHlc |>.continuousAt
  obtain ⟨f, g, hflc, hglc, hkey⟩ :=
    exists_decomposition hmono H hW hH hA hB hAB hBA
  have hfx : f ⟨x, compl_left hx⟩ = f ⟨y, compl_left hy⟩ := by
    have h1 : f ⟨x, compl_left hx⟩ = f ⟨x, hA'.source_mem⟩ := congrArg f (Subtype.ext rfl)
    have h2 : f ⟨y, hA'.target_mem⟩ = f ⟨y, compl_left hy⟩ := congrArg f (Subtype.ext rfl)
    rw [h1, ← h2]
    exact isLocallyConstant_eq_of_joinedIn hflc hA'
  have hgy : g ⟨x, compl_right hx⟩ = g ⟨y, compl_right hy⟩ := by
    have h1 : g ⟨x, compl_right hx⟩ = g ⟨x, hB'.source_mem⟩ := congrArg g (Subtype.ext rfl)
    have h2 : g ⟨y, hB'.target_mem⟩ = g ⟨y, compl_right hy⟩ := congrArg g (Subtype.ext rfl)
    rw [h1, ← h2]
    exact isLocallyConstant_eq_of_joinedIn hglc hB'
  have hHx : H ⟨x, hx⟩ = 1 := by
    change (if JoinedIn W x x then (1 : ℤ) else 0) = 1
    rw [if_pos (JoinedIn.refl hx)]
  have hHy : H ⟨y, hy⟩ = 0 := by
    change (if JoinedIn W x y then (1 : ℤ) else 0) = 0
    rw [if_neg hcon]
  have hEq : H ⟨x, hx⟩ = H ⟨y, hy⟩ := by
    rw [hkey x hx, hkey y hy, hfx, hgy]
  rw [hHx, hHy] at hEq
  norm_num at hEq

end Commons.Topology.Jordan