import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.LocallyConstant.Basic
import Submission.Commons.Topology.Covering.section_of_monodromy_eq_self_weak

set_option linter.defProp false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false
set_option maxHeartbeats 1600000


open Set Metric
open scoped Topology
open Classical

set_option linter.defProp false
set_option linter.style.haveILetI false

/-- A preconnected set inside an open set of a locally path connected space is joined. -/
theorem IsPreconnected.joinedIn_of_isOpen_subset {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] {T U : Set X} (hT : IsPreconnected T) (hU : IsOpen U)
    (hTU : T ⊆ U) {x y : X} (hx : x ∈ T) (hy : y ∈ T) : JoinedIn U x y := by
  have hS : IsOpen (pathComponentIn U x) := hU.pathComponentIn x
  have hmain : T ⊆ pathComponentIn U x := by
    refine hT.subset_of_closure_inter_subset hS ⟨x, hx, mem_pathComponentIn_self (hTU hx)⟩ ?_
    rintro w ⟨hwcl, hwT⟩
    have hwU : w ∈ U := hTU hwT
    have hSw : IsOpen (pathComponentIn U w) := hU.pathComponentIn w
    obtain ⟨z, hzw, hzS⟩ := mem_closure_iff.mp hwcl _ hSw (mem_pathComponentIn_self hwU)
    have h1 : pathComponentIn U w = pathComponentIn U x := by
      rw [← pathComponentIn_congr hzw, ← pathComponentIn_congr hzS]
    rw [← h1]
    exact mem_pathComponentIn_self hwU
  exact hmain hy

/-- Convex subsets of a real normed space are locally path connected. -/
theorem LocallyPathConnectedSpace.of_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (hs : Convex ℝ s) : LocallyPathConnectedSpace ↥s := by
  refine LocallyPathConnectedSpace.of_bases
    (p := fun (x : ↥s) (ε : ℝ) => 0 < ε) (s := fun (x : ↥s) (ε : ℝ) => Metric.ball x ε)
    (by intro x; exact Metric.nhds_basis_ball) fun x ε hε => ?_
  refine ⟨x, Metric.mem_ball_self hε, fun y hy => ?_⟩
  have hmem : ∀ t : unitInterval, (1 - (t:ℝ)) • (x:E) + (t:ℝ) • (y:E) ∈ s := fun t =>
    hs x.2 y.2 (by linarith [t.2.2]) (by linarith [t.2.1]) (by ring)
  have hcont : Continuous fun t : unitInterval => (1 - (t:ℝ)) • (x:E) + (t:ℝ) • (y:E) := by fun_prop
  have hyε : dist (y:E) (x:E) < ε := by
    have := hy; rwa [Metric.mem_ball, Subtype.dist_eq] at this
  refine ⟨{ toFun := fun t => ⟨_, hmem t⟩
            continuous_toFun := hcont.subtype_mk hmem
            source' := Subtype.ext (by simp)
            target' := Subtype.ext (by simp) }, ?_⟩
  intro t
  have ht0 : (0:ℝ) ≤ t := t.2.1
  have ht1 : (t:ℝ) ≤ 1 := t.2.2
  rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
  change ‖(1 - (t:ℝ)) • (x:E) + (t:ℝ) • (y:E) - (x:E)‖ < ε
  have hsub : ((1 - (t:ℝ)) • (x:E) + (t:ℝ) • (y:E)) - (x:E) = (t:ℝ) • ((y:E) - (x:E)) := by
    module
  rw [hsub, norm_smul, Real.norm_of_nonneg ht0]
  rw [dist_eq_norm] at hyε
  calc (t:ℝ) * ‖(y:E) - (x:E)‖ ≤ 1 * ‖(y:E) - (x:E)‖ :=
        mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
    _ = ‖(y:E) - (x:E)‖ := one_mul _
    _ < ε := hyε

namespace Commons.Topology.Jordan.Square2
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
end Commons.Topology.Jordan.Square2

namespace Commons.Topology.Jordan.Square2
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
end Commons.Topology.Jordan.Square2

namespace Commons.Topology.Jordan.Square2
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
end Commons.Topology.Jordan.Square2

namespace Commons.Topology.Jordan.Square2
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
end Commons.Topology.Jordan.Square2

namespace Commons.Topology.Jordan.Square2
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
end Commons.Topology.Jordan.Square2

namespace Commons.Topology.Jordan.Square2
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
end Commons.Topology.Jordan.Square2

namespace Commons.Topology.Jordan.Square2
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
end Commons.Topology.Jordan.Square2

namespace Commons.Topology.Jordan.Square2

open QD

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

end Commons.Topology.Jordan.Square2
namespace Commons.Topology.Jordan

/-- The parameter square `[-1,1]² ⊆ ℂ`. -/
def Qsq : Set ℂ := {z : ℂ | z.re ∈ Set.Icc (-1:ℝ) 1 ∧ z.im ∈ Set.Icc (-1:ℝ) 1}

lemma isClosed_Qsq : IsClosed Qsq := by
  have h1 : IsClosed (Complex.re ⁻¹' Set.Icc (-1:ℝ) 1) := isClosed_Icc.preimage Complex.continuous_re
  have h2 : IsClosed (Complex.im ⁻¹' Set.Icc (-1:ℝ) 1) := isClosed_Icc.preimage Complex.continuous_im
  convert h1.inter h2 using 1
  ext z; simp [Qsq, and_assoc]

lemma isCompact_Qsq : IsCompact Qsq := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨isClosed_Qsq, ?_⟩
  refine (Metric.isBounded_closedBall (x := (0:ℂ)) (r := 2)).subset ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 := hz.1.1; have h2 := hz.1.2; have h3 := hz.2.1; have h4 := hz.2.2
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  nlinarith [sq_nonneg z.re, sq_nonneg z.im, norm_nonneg z]

lemma convex_Qsq : Convex ℝ Qsq := by
  have h1 : Convex ℝ ((Complex.reCLM : ℂ →L[ℝ] ℝ).toLinearMap ⁻¹' (Set.Icc (-1:ℝ) 1)) :=
    (convex_Icc _ _).linear_preimage _
  have h2 : Convex ℝ ((Complex.imCLM : ℂ →L[ℝ] ℝ).toLinearMap ⁻¹' (Set.Icc (-1:ℝ) 1)) :=
    (convex_Icc _ _).linear_preimage _
  convert h1.inter h2 using 1
  ext z; simp [Qsq, Complex.reCLM, Complex.imCLM]

/-- The top edge of the square. -/
def tE : Set ℂ := {z : ℂ | z.im = 1 ∧ z ∈ Qsq}
/-- The bottom edge of the square. -/
def bE : Set ℂ := {z : ℂ | z.im = -1 ∧ z ∈ Qsq}
/-- The left edge of the square. -/
def lE : Set ℂ := {z : ℂ | z.re = -1 ∧ z ∈ Qsq}
/-- The right edge of the square. -/
def rE : Set ℂ := {z : ℂ | z.re = 1 ∧ z ∈ Qsq}

lemma tE_preconnected : IsPreconnected tE := by
  have hseg : tE = (fun x : ℝ => (x:ℂ) + Complex.I) '' (Set.Icc (-1:ℝ) 1) := by
    ext z; constructor
    · rintro ⟨hzim, hzQ⟩
      exact ⟨z.re, hzQ.1, by apply Complex.ext <;> simp [hzim]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by simp, by constructor <;> simp; simpa using hx⟩
  rw [hseg]
  exact isPreconnected_Icc.image _ (by fun_prop)

lemma bE_preconnected : IsPreconnected bE := by
  have hseg : bE = (fun x : ℝ => (x:ℂ) - Complex.I) '' (Set.Icc (-1:ℝ) 1) := by
    ext z; constructor
    · rintro ⟨hzim, hzQ⟩
      exact ⟨z.re, hzQ.1, by apply Complex.ext <;> simp [hzim]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by simp, by constructor <;> simp; simpa using hx⟩
  rw [hseg]
  exact isPreconnected_Icc.image _ (by fun_prop)

lemma tE_compact : IsCompact tE := by
  rw [tE]
  exact isCompact_Qsq.of_isClosed_subset
    ((isClosed_eq Complex.continuous_im continuous_const).inter isClosed_Qsq) Set.inter_subset_right

lemma bE_compact : IsCompact bE := by
  rw [bE]
  exact isCompact_Qsq.of_isClosed_subset
    ((isClosed_eq Complex.continuous_im continuous_const).inter isClosed_Qsq) Set.inter_subset_right

lemma lE_preconnected : IsPreconnected lE := by
  have hseg : lE = (fun x : ℝ => ((-1:ℂ) + (x:ℂ) * Complex.I)) '' (Set.Icc (-1:ℝ) 1) := by
    ext z; constructor
    · rintro ⟨hzre, hzQ⟩
      exact ⟨z.im, hzQ.2, by apply Complex.ext <;> simp [hzre]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by simp, by norm_num, by simpa using hx⟩
  rw [hseg]
  exact isPreconnected_Icc.image _ (by fun_prop)

lemma rE_preconnected : IsPreconnected rE := by
  have hseg : rE = (fun x : ℝ => (1:ℂ) + (x:ℂ) * Complex.I) '' (Set.Icc (-1:ℝ) 1) := by
    ext z; constructor
    · rintro ⟨hzre, hzQ⟩
      exact ⟨z.im, hzQ.2, by apply Complex.ext <;> simp [hzre]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by simp, by norm_num, by simpa using hx⟩
  rw [hseg]
  exact isPreconnected_Icc.image _ (by fun_prop)

lemma lE_compact : IsCompact lE := by
  rw [lE]
  exact isCompact_Qsq.of_isClosed_subset
    ((isClosed_eq Complex.continuous_re continuous_const).inter isClosed_Qsq) Set.inter_subset_right

lemma rE_compact : IsCompact rE := by
  rw [rE]
  exact isCompact_Qsq.of_isClosed_subset
    ((isClosed_eq Complex.continuous_re continuous_const).inter isClosed_Qsq) Set.inter_subset_right

lemma lE_top : ∃ z ∈ lE, z.im = 1 := ⟨(-1:ℂ) + Complex.I, ⟨by simp, by constructor <;> simp⟩, by simp⟩
lemma lE_bot : ∃ z ∈ lE, z.im = -1 := ⟨(-1:ℂ) - Complex.I, ⟨by simp, by constructor <;> simp⟩, by simp⟩
lemma rE_top : ∃ z ∈ rE, z.im = 1 := ⟨(1:ℂ) + Complex.I, ⟨by simp, by constructor <;> simp⟩, by simp⟩
lemma rE_bot : ∃ z ∈ rE, z.im = -1 := ⟨(1:ℂ) - Complex.I, ⟨by simp, by constructor <;> simp⟩, by simp⟩
lemma tE_nonempty : tE.Nonempty := ⟨Complex.I, by simp [tE, Qsq]⟩
lemma bE_nonempty : bE.Nonempty := ⟨-Complex.I, by simp [bE, Qsq]⟩

/-- `Sep S` means: there is a top-bottom continuum inside the square avoiding `S`. -/
def Sep (S : Set ℂ) : Prop :=
  ∃ T : Set ℂ, T ⊆ Qsq \ S ∧ IsPreconnected T ∧ IsCompact T ∧
    (∃ z ∈ T, z.im = 1) ∧ (∃ z ∈ T, z.im = -1)

/-- The hexagon `{|re| ≤ 1, |re| + |im| ≤ 2}`: the square with two conical caps. -/
def Hex : Set ℂ := {z : ℂ | |z.re| ≤ 1 ∧ |z.re| + |z.im| ≤ 2}

lemma convex_Hex : Convex ℝ Hex := by
  intro z hz w hw a b ha hb hab
  obtain ⟨hz1, hz2⟩ := hz; obtain ⟨hw1, hw2⟩ := hw
  have hzre := abs_le.mp hz1; have hwre := abs_le.mp hw1
  have hre : (a • z + b • w).re = a * z.re + b * w.re := by simp
  have him : (a • z + b • w).im = a * z.im + b * w.im := by simp
  constructor
  · rw [hre, abs_le]
    constructor <;> nlinarith [hzre.1, hzre.2, hwre.1, hwre.2]
  · rw [hre, him]
    have e1 : |a * z.re + b * w.re| ≤ a * |z.re| + b * |w.re| := by
      calc |a * z.re + b * w.re| ≤ |a * z.re| + |b * w.re| := abs_add_le _ _
        _ = a * |z.re| + b * |w.re| := by
              rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    have e2 : |a * z.im + b * w.im| ≤ a * |z.im| + b * |w.im| := by
      calc |a * z.im + b * w.im| ≤ |a * z.im| + |b * w.im| := abs_add_le _ _
        _ = a * |z.im| + b * |w.im| := by
              rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    nlinarith [e1, e2, hz2, hw2]

lemma zero_mem_Hex : (0:ℂ) ∈ Hex := by
  constructor <;> norm_num [Hex, Complex.zero_re, Complex.zero_im]

lemma two_I_mem_Hex : (2:ℂ) * Complex.I ∈ Hex := by
  constructor <;> norm_num [Hex, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]

lemma neg_two_I_mem_Hex : -((2:ℂ) * Complex.I) ∈ Hex := by
  constructor <;> norm_num [Hex, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]

lemma Qsq_subset_Hex : Qsq ⊆ Hex := by
  rintro z ⟨h1, h2⟩
  have hre : |z.re| ≤ 1 := by rw [abs_le]; exact ⟨h1.1, h1.2⟩
  have him : |z.im| ≤ 1 := by rw [abs_le]; exact ⟨h2.1, h2.2⟩
  exact ⟨hre, by linarith⟩

lemma mem_Qsq_of_mem_Hex_of_im {z : ℂ} (hz : z ∈ Hex) (h1 : -1 ≤ z.im) (h2 : z.im ≤ 1) :
    z ∈ Qsq :=
  ⟨by have h := hz.1; rw [abs_le] at h; exact ⟨h.1, h.2⟩, ⟨h1, h2⟩⟩

instance : LocallyPathConnectedSpace ↥Hex := LocallyPathConnectedSpace.of_convex convex_Hex

lemma isPreconnected_subtype_preimage {s t : Set ℂ} (ht : IsPreconnected t) (hts : t ⊆ s) :
    IsPreconnected (Subtype.val ⁻¹' t : Set ↥s) := by
  refine (Topology.IsInducing.subtypeVal (t := s)).isPreconnected_image.mp ?_
  rw [Subtype.image_preimage_coe, inter_eq_right.mpr hts]
  exact ht

lemma segment_twoI_im {p z : ℂ} (hp : p.im = 1) (hz : z ∈ segment ℝ (2*Complex.I) p) :
    1 ≤ z.im ∧ (z.im = 1 → z = p) := by
  rw [segment_eq_image] at hz
  obtain ⟨θ, ⟨hθ0, hθ1⟩, hz⟩ := hz
  have h2I : ((2:ℂ) * Complex.I).im = 2 := by simp
  have hzim : z.im = 2 - θ := by
    rw [← hz]
    have : ((1 - θ) • ((2:ℂ) * Complex.I) + θ • p).im
        = (1 - θ) * (((2:ℂ) * Complex.I).im) + θ * p.im := by simp
    rw [this, h2I, hp]
    ring
  constructor
  · rw [hzim]; linarith
  · intro h
    have hθ : θ = 1 := by rw [hzim] at h; linarith
    rw [← hz, hθ]; simp

lemma segment_neg_twoI_im {p z : ℂ} (hp : p.im = -1) (hz : z ∈ segment ℝ p (-(2*Complex.I))) :
    z.im ≤ -1 ∧ (z.im = -1 → z = p) := by
  rw [segment_eq_image] at hz
  obtain ⟨θ, ⟨hθ0, hθ1⟩, hz⟩ := hz
  have h2I : (-((2:ℂ) * Complex.I)).im = -2 := by simp
  have hzim : z.im = -1 - θ := by
    rw [← hz]
    have : ((1 - θ) • p + θ • (-((2:ℂ) * Complex.I))).im
        = (1 - θ) * p.im + θ * (-((2:ℂ) * Complex.I)).im := by simp
    rw [this, hp, h2I]
    ring
  constructor
  · rw [hzim]; linarith
  · intro h
    have hθ : θ = 0 := by rw [hzim] at h; linarith
    rw [← hz, hθ]; simp

/-- Inside the hexagon, a top-bottom continuum avoiding `S` gives a joining of the two cone tips
avoiding `S`. -/
lemma joinedIn_of_sep {S : Set ℂ} (hScomp : IsCompact S) (hSsub : S ⊆ Qsq) (hSsep : Sep S) :
    JoinedIn ((Subtype.val ⁻¹' S : Set ↥Hex))ᶜ (⟨2*Complex.I, two_I_mem_Hex⟩ : ↥Hex)
      (⟨-(2*Complex.I), neg_two_I_mem_Hex⟩ : ↥Hex) := by
  obtain ⟨T, hTsub, hTpre, _, ⟨p, hpT, hpim⟩, ⟨q, hqT, hqim⟩⟩ := hSsep
  have hpS : p ∉ S := fun h => (hTsub hpT).2 h
  have hqS : q ∉ S := fun h => (hTsub hqT).2 h
  have hpHex : p ∈ Hex := Qsq_subset_Hex (hTsub hpT).1
  have hqHex : q ∈ Hex := Qsq_subset_Hex (hTsub hqT).1
  have hU : IsOpen ((Subtype.val ⁻¹' S : Set ↥Hex))ᶜ :=
    (hScomp.isClosed.preimage continuous_subtype_val).isOpen_compl
  -- (a) `p` and `q` are joined in `U` by `T`
  have hTpre' : IsPreconnected (Subtype.val ⁻¹' T : Set ↥Hex) :=
    isPreconnected_subtype_preimage hTpre (hTsub.trans (Set.sdiff_subset.trans Qsq_subset_Hex))
  have hTmem : (Subtype.val ⁻¹' T : Set ↥Hex) ⊆ (Subtype.val ⁻¹' S : Set ↥Hex)ᶜ := by
    intro z hz
    simp only [mem_compl_iff, mem_preimage] at hz ⊢
    exact fun hzS => (hTsub hz).2 hzS
  have hpq : JoinedIn ((Subtype.val ⁻¹' S : Set ↥Hex))ᶜ ⟨p, hpHex⟩ ⟨q, hqHex⟩ :=
    hTpre'.joinedIn_of_isOpen_subset hU hTmem (mem_preimage.mpr hpT) (mem_preimage.mpr hqT)
  -- (b) the cone tips are joined to `p` and `q`
  have hx_seg : (2*Complex.I) ∈ segment ℝ (2*Complex.I) p := by
    rw [segment_eq_image]; exact ⟨0, ⟨le_refl 0, zero_le_one⟩, by simp⟩
  have hp_seg : p ∈ segment ℝ (2*Complex.I) p := by
    rw [segment_eq_image]; exact ⟨1, ⟨zero_le_one, le_refl 1⟩, by simp⟩
  have hq_seg : q ∈ segment ℝ q (-(2*Complex.I)) := by
    rw [segment_eq_image]; exact ⟨0, ⟨le_refl 0, zero_le_one⟩, by simp⟩
  have hy_seg : -(2*Complex.I) ∈ segment ℝ q (-(2*Complex.I)) := by
    rw [segment_eq_image]; exact ⟨1, ⟨zero_le_one, le_refl 1⟩, by simp⟩
  have hseg1 : JoinedIn ((Subtype.val ⁻¹' S : Set ↥Hex))ᶜ ⟨2*Complex.I, two_I_mem_Hex⟩
      ⟨p, hpHex⟩ := by
    have hpre : IsPreconnected (Subtype.val ⁻¹' (segment ℝ (2*Complex.I) p) : Set ↥Hex) :=
      isPreconnected_subtype_preimage (convex_segment _ _).isPreconnected
        (convex_Hex.segment_subset two_I_mem_Hex hpHex)
    refine hpre.joinedIn_of_isOpen_subset hU ?_ (by simpa using hx_seg) (by simpa using hp_seg)
    intro z hz
    simp only [mem_compl_iff, mem_preimage] at hz ⊢
    intro hzS
    obtain ⟨h1, h2⟩ := segment_twoI_im hpim hz
    have h3 : (z:ℂ).im ≤ 1 := (hSsub hzS).2.2
    have hzp : (z:ℂ) = p := h2 (le_antisymm h3 h1)
    rw [hzp] at hzS
    exact hpS hzS
  have hseg2 : JoinedIn ((Subtype.val ⁻¹' S : Set ↥Hex))ᶜ ⟨q, hqHex⟩
      ⟨-(2*Complex.I), neg_two_I_mem_Hex⟩ := by
    have hpre : IsPreconnected (Subtype.val ⁻¹' (segment ℝ q (-(2*Complex.I))) : Set ↥Hex) :=
      isPreconnected_subtype_preimage (convex_segment _ _).isPreconnected
        (convex_Hex.segment_subset hqHex neg_two_I_mem_Hex)
    refine hpre.joinedIn_of_isOpen_subset hU ?_ (by simpa using hq_seg) (by simpa using hy_seg)
    intro z hz
    simp only [mem_compl_iff, mem_preimage] at hz ⊢
    intro hzS
    obtain ⟨h1, h2⟩ := segment_neg_twoI_im hqim hz
    have h3 : -1 ≤ (z:ℂ).im := (hSsub hzS).2.1
    have hzq : (z:ℂ) = q := h2 (le_antisymm h1 h3)
    rw [hzq] at hzS
    exact hqS hzS
  exact hseg1.trans (hpq.trans hseg2)

/-- **The left edge itself is a top-to-bottom continuum.**  Consequently any set missing the
left edge does not separate the top edge from the bottom edge. -/
lemma sep_of_disjoint_left {S : Set ℂ} (hS : Disjoint S lE) : Sep S := by
  refine ⟨lE, ?_, lE_preconnected, lE_compact, lE_top, lE_bot⟩
  intro z hz
  exact ⟨hz.2, fun hzS => Set.disjoint_left.mp hS hzS hz⟩

/-- **Likewise for the right edge.** -/
lemma sep_of_disjoint_right {S : Set ℂ} (hS : Disjoint S rE) : Sep S := by
  refine ⟨rE, ?_, rE_preconnected, rE_compact, rE_top, rE_bot⟩
  intro z hz
  exact ⟨hz.2, fun hzS => Set.disjoint_left.mp hS hzS hz⟩

/-- Consequently a non-separating set must meet both the left and the right edge. -/
lemma nonempty_inter_left_of_not_sep {S : Set ℂ} (hS : ¬ Sep S) : (S ∩ lE).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  exact hS (sep_of_disjoint_left (Set.disjoint_iff_inter_eq_empty.mpr h))

lemma nonempty_inter_right_of_not_sep {S : Set ℂ} (hS : ¬ Sep S) : (S ∩ rE).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  exact hS (sep_of_disjoint_right (Set.disjoint_iff_inter_eq_empty.mpr h))

set_option maxHeartbeats 3200000 in
/-- **The two-set Janiszewski property of the square** (the key geometric input). -/
lemma janiszewski_lines {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hdisj : Disjoint A B)
    (hAsub : A ⊆ Qsq) (hBsub : B ⊆ Qsq)
    (hAsep : Sep A) (hBsep : Sep B) : Sep (A ∪ B) := by
  classical
  have hJA := joinedIn_of_sep hA hAsub hAsep
  have hJB := joinedIn_of_sep hB hBsub hBsep
  have hA' : IsClosed (Subtype.val ⁻¹' A : Set ↥Hex) := hA.isClosed.preimage continuous_subtype_val
  have hB' : IsClosed (Subtype.val ⁻¹' B : Set ↥Hex) := hB.isClosed.preimage continuous_subtype_val
  have hdisj' : Disjoint (Subtype.val ⁻¹' A : Set ↥Hex) (Subtype.val ⁻¹' B : Set ↥Hex) := by
    rw [Set.disjoint_left]
    exact fun z hzA hzB => Set.disjoint_left.mp hdisj hzA hzB
  have hxnot : (⟨2*Complex.I, two_I_mem_Hex⟩ : ↥Hex) ∉
      (Subtype.val ⁻¹' A : Set ↥Hex) ∪ (Subtype.val ⁻¹' B : Set ↥Hex) := by
    simp only [mem_union, mem_preimage, not_or]
    constructor
    · intro h; have := (hAsub h).2; norm_num at this
    · intro h; have := (hBsub h).2; norm_num at this
  have hynot : (⟨-(2*Complex.I), neg_two_I_mem_Hex⟩ : ↥Hex) ∉
      (Subtype.val ⁻¹' A : Set ↥Hex) ∪ (Subtype.val ⁻¹' B : Set ↥Hex) := by
    simp only [mem_union, mem_preimage, not_or]
    constructor
    · intro h; have := (hAsub h).2; norm_num at this
    · intro h; have := (hBsub h).2; norm_num at this
  haveI : ContractibleSpace ↥Hex := convex_Hex.contractibleSpace ⟨0, zero_mem_Hex⟩
  haveI : ConnectedSpace ↥Hex := by
    rw [← isConnected_iff_connectedSpace]
    exact ⟨⟨0, zero_mem_Hex⟩, convex_Hex.isPreconnected⟩
  have hmono : ∀ z : ↥Hex, Subsingleton (FundamentalGroup ↥Hex z) := fun z => inferInstance
  have hmain := Square2.two_disjoint_closed_not_separating (X := ↥Hex)
    hmono hA' hB' hdisj' hxnot hynot hJA hJB
  obtain ⟨γ, hγ⟩ := hmain
  have hγ' : ∀ v : unitInterval, ((γ v : ↥Hex) : ℂ) ∉ A ∪ B := by
    intro v
    have h := hγ v
    simp only [mem_compl_iff, mem_union, mem_preimage, not_or] at h
    exact fun hh => hh.elim h.1 h.2
  set F : ℝ → ℂ := fun u => ((γ.extend u : ↥Hex) : ℂ) with hFdef
  have hFcont : Continuous F := continuous_subtype_val.comp γ.continuous_extend
  have hFnot : ∀ u : ℝ, F u ∉ A ∪ B := by
    intro u
    have hmem : γ.extend u ∈ range γ := by
      rw [← Path.extend_range γ]; exact ⟨u, rfl⟩
    obtain ⟨v, hv⟩ := hmem
    rw [hFdef]
    dsimp only
    rw [← hv]
    exact hγ' v
  have hF0 : F 0 = 2*Complex.I := by rw [hFdef]; simp [γ.extend_zero]
  have hF1 : F 1 = -(2*Complex.I) := by rw [hFdef]; simp [γ.extend_one]
  have hFim : Continuous fun u : ℝ => (F u).im := Complex.continuous_im.comp hFcont
  -- first level
  set P : Set ℝ := {u : ℝ | 1 ≤ (F u).im} ∩ Set.Icc (0:ℝ) 1 with hPdef
  have hPcl : IsClosed P := by
    rw [hPdef]; exact (isClosed_le continuous_const hFim).inter isClosed_Icc
  have h0P : (0:ℝ) ∈ P := by
    rw [hPdef]
    refine ⟨?_, by norm_num⟩
    show 1 ≤ (F 0).im
    rw [hF0]; norm_num
  have hPne : P.Nonempty := ⟨0, h0P⟩
  have hPbdd : BddAbove P := ⟨1, fun u hu => by rw [hPdef] at hu; exact hu.2.2⟩
  set s : ℝ := sSup P with hsdef
  have hsP : s ∈ P := by rw [hsdef]; exact hPcl.csSup_mem hPne hPbdd
  have hs1 : 1 ≤ (F s).im := by rw [hPdef] at hsP; exact hsP.1
  have hs01 : s ∈ Set.Icc (0:ℝ) 1 := by rw [hPdef] at hsP; exact hsP.2
  set Q : Set ℝ := {u : ℝ | (F u).im ≤ -1} ∩ Set.Icc s 1 with hQdef
  have hQcl : IsClosed Q := by
    rw [hQdef]; exact (isClosed_le hFim continuous_const).inter isClosed_Icc
  have h1Q : (1:ℝ) ∈ Q := by
    rw [hQdef]
    refine ⟨?_, ⟨hs01.2, le_rfl⟩⟩
    show (F 1).im ≤ -1
    rw [hF1]; norm_num
  have hQne : Q.Nonempty := ⟨1, h1Q⟩
  have hQbdd : BddBelow Q := ⟨s, fun u hu => by rw [hQdef] at hu; exact hu.2.1⟩
  set t : ℝ := sInf Q with htdef
  have htQ : t ∈ Q := by rw [htdef]; exact hQcl.csInf_mem hQne hQbdd
  have hmt : (F t).im ≤ -1 := by rw [hQdef] at htQ; exact htQ.1
  have hst : s ≤ t := by rw [hQdef] at htQ; exact htQ.2.1
  have hstlt : s < t := by
    refine lt_of_le_of_ne hst fun h => ?_
    rw [h] at hs1
    linarith
  have hmid : ∀ u : ℝ, s < u → u < t → -1 < (F u).im ∧ (F u).im < 1 := by
    intro u hsu hut
    have hu01 : u ∈ Set.Icc (0:ℝ) 1 :=
      ⟨le_trans hs01.1 hsu.le, le_trans hut.le (by rw [hQdef] at htQ; exact htQ.2.2)⟩
    constructor
    · by_contra hcon
      push_neg at hcon
      have huQ : u ∈ Q := by rw [hQdef]; exact ⟨hcon, ⟨hsu.le, hu01.2⟩⟩
      have h := csInf_le hQbdd huQ
      rw [← htdef] at h
      linarith
    · by_contra hcon
      push_neg at hcon
      have huP : u ∈ P := by rw [hPdef]; exact ⟨hcon, hu01⟩
      have h := le_csSup hPbdd huP
      rw [← hsdef] at h
      linarith
  -- second level
  set R : Set ℝ := {u : ℝ | (F u).im = 1} ∩ Set.Icc s t with hRdef
  have hRcl : IsClosed R := by
    rw [hRdef]; exact (isClosed_eq hFim continuous_const).inter isClosed_Icc
  have hRne : R.Nonempty := by
    have h1 : (1:ℝ) ∈ Set.Icc ((F t).im) ((F s).im) := ⟨by linarith, hs1⟩
    obtain ⟨u, hu, hux⟩ := intermediate_value_Icc' hstlt.le hFim.continuousOn h1
    exact ⟨u, by rw [hRdef]; exact ⟨hux, hu⟩⟩
  have hRbdd : BddBelow R := ⟨s, fun u hu => by rw [hRdef] at hu; exact hu.2.1⟩
  set s₂ : ℝ := sInf R with hs2def
  have hs2R : s₂ ∈ R := by rw [hs2def]; exact hRcl.csInf_mem hRne hRbdd
  have hs2im : (F s₂).im = 1 := by rw [hRdef] at hs2R; exact hs2R.1
  have hs2ge : s ≤ s₂ := by rw [hRdef] at hs2R; exact hs2R.2.1
  have hs2let : s₂ ≤ t := by rw [hRdef] at hs2R; exact hs2R.2.2
  set U₂ : Set ℝ := {u : ℝ | (F u).im = -1} ∩ Set.Icc s₂ t with hU2def
  have hU2cl : IsClosed U₂ := by
    rw [hU2def]; exact (isClosed_eq hFim continuous_const).inter isClosed_Icc
  have hU2ne : U₂.Nonempty := by
    have h1 : (-1:ℝ) ∈ Set.Icc ((F t).im) ((F s₂).im) := ⟨by linarith, by linarith [hs2im]⟩
    obtain ⟨u, hu, hux⟩ := intermediate_value_Icc' hs2let hFim.continuousOn h1
    exact ⟨u, by rw [hU2def]; exact ⟨hux, hu⟩⟩
  have hU2bdd : BddBelow U₂ := ⟨s₂, fun u hu => by rw [hU2def] at hu; exact hu.2.1⟩
  set t₂ : ℝ := sInf U₂ with ht2def
  have ht2U : t₂ ∈ U₂ := by rw [ht2def]; exact hU2cl.csInf_mem hU2ne hU2bdd
  have ht2im : (F t₂).im = -1 := by rw [hU2def] at ht2U; exact ht2U.1
  have ht2ge : s₂ ≤ t₂ := by rw [hU2def] at ht2U; exact ht2U.2.1
  have ht2let : t₂ ≤ t := by rw [hU2def] at ht2U; exact ht2U.2.2
  refine ⟨F '' Set.Icc s₂ t₂, ?_, ?_, ?_, ?_, ?_⟩
  · rintro z ⟨u, hu, rfl⟩
    refine ⟨?_, hFnot u⟩
    rcases lt_or_eq_of_le hu.1 with hlt | heq
    · rcases lt_or_eq_of_le hu.2 with hlt2 | heq2
      · obtain ⟨h1, h2⟩ := hmid u (lt_of_le_of_lt hs2ge hlt) (lt_of_lt_of_le hlt2 ht2let)
        exact mem_Qsq_of_mem_Hex_of_im (γ.extend u).2 h1.le h2.le
      · rw [heq2]
        exact mem_Qsq_of_mem_Hex_of_im (γ.extend t₂).2
          (by linarith [ht2im]) (by linarith [ht2im])
    · rw [← heq]
      exact mem_Qsq_of_mem_Hex_of_im (γ.extend s₂).2
        (by linarith [hs2im]) (by linarith [hs2im])
  · exact isPreconnected_Icc.image F hFcont.continuousOn
  · exact isCompact_Icc.image hFcont
  · exact ⟨F s₂, ⟨s₂, ⟨le_rfl, ht2ge⟩, rfl⟩, hs2im⟩
  · exact ⟨F t₂, ⟨t₂, ⟨ht2ge, le_rfl⟩, rfl⟩, ht2im⟩


/-- **Minimal non-separating closed subsets exist.** -/
theorem exists_minimal_separating_lines {K : Set ℂ} (hK : IsCompact K)
    (hsep : ¬ Sep K) :
    ∃ M : Set ℂ, M ⊆ K ∧ IsClosed M ∧ ¬ Sep M ∧
      ∀ S : Set ℂ, S ⊆ M → IsClosed S → ¬ Sep S → S = M := by
  classical
  set 𝓢 : Set (Set ℂ) := {S | S ⊆ K ∧ IsClosed S ∧ ¬ Sep S} with h𝓢
  have hKmem : K ∈ 𝓢 := ⟨subset_rfl, hK.isClosed, hsep⟩
  have hchain : ∀ c ⊆ 𝓢, IsChain (· ⊆ ·) c → ∃ lb ∈ 𝓢, ∀ s ∈ c, lb ⊆ s := by
    intro c hc hchain
    rcases c.eq_empty_or_nonempty with rfl | hcne
    · exact ⟨K, hKmem, by simp⟩
    · refine ⟨⋂₀ c, ?_, fun s hs => sInter_subset_of_mem hs⟩
      have hsub : ⋂₀ c ⊆ K := by
        obtain ⟨s₀, hs₀⟩ := hcne
        exact (Set.sInter_subset_of_mem hs₀).trans (hc hs₀).1
      have hclosed : IsClosed (⋂₀ c) := isClosed_sInter (fun t ht => (hc ht).2.1)
      refine ⟨hsub, hclosed, ?_⟩
      rintro ⟨T, hTsub, hTpre, hTc, hTt, hTb⟩
      have hdisj0 : T ∩ (⋂ i : {s // s ∈ c}, ((i : {s // s ∈ c}).1 : Set ℂ)) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z ⟨hzT, hzc⟩
        rw [← Set.sInter_eq_iInter] at hzc
        exact (hTsub hzT).2 hzc
      obtain ⟨u, hu⟩ := hTc.elim_finite_subfamily_closed
        (fun i : {s // s ∈ c} => ((i : {s // s ∈ c}).1 : Set ℂ))
        (fun i => (hc i.2).2.1) (Set.disjoint_iff_inter_eq_empty.mpr hdisj0)
      replace hu := Set.disjoint_iff_inter_eq_empty.mp hu
      have hune : u.Nonempty := by
        rcases u.eq_empty_or_nonempty with h | h
        · exfalso
          rw [h] at hu
          simp at hu
          obtain ⟨z, hzT, _⟩ := hTt
          rw [hu] at hzT
          exact hzT
        · exact h
      obtain ⟨i₀, hi₀u, hi₀min⟩ := Finset.exists_minimal (s := u) hune
      have hle : ∀ j ∈ u, ((i₀ : {s // s ∈ c}).1 : Set ℂ) ⊆ ((j : {s // s ∈ c}).1 : Set ℂ) := by
        intro j hj
        rcases hchain.total i₀.2 j.2 with h | h
        · exact h
        · exact hi₀min hj h
      have hinter : (⋂ i ∈ u, ((i : {s // s ∈ c}).1 : Set ℂ)) = ((i₀ : {s // s ∈ c}).1 : Set ℂ) :=
        Set.Subset.antisymm (Set.biInter_subset_of_mem hi₀u) (Set.subset_iInter₂ hle)
      have hTi₀ : T ∩ ((i₀ : {s // s ∈ c}).1 : Set ℂ) = ∅ := by rw [← hinter]; exact hu
      refine (hc i₀.2).2.2 ⟨T, ?_, hTpre, hTc, hTt, hTb⟩
      intro z hz
      exact ⟨(hTsub hz).1, fun hzS => Set.eq_empty_iff_forall_notMem.mp hTi₀ z ⟨hz, hzS⟩⟩
  obtain ⟨m, hmmin⟩ := zorn_superset 𝓢 hchain
  exact ⟨m, hmmin.1.1, hmmin.1.2.1, hmmin.1.2.2,
    fun S hSm hSc hSs => Set.Subset.antisymm hSm (hmmin.2 ⟨hSm.trans hmmin.1.1, hSc, hSs⟩ hSm)⟩

/-- **Irreducible cut.**  Any compact non-separating set contains a *connected* one. -/
theorem continuum_cut {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ Qsq) (hsep : ¬ Sep K) :
    ∃ C : Set ℂ, C ⊆ K ∧ IsCompact C ∧ IsPreconnected C ∧ ¬ Sep C := by
  classical
  obtain ⟨m, hmK, hmcl, hmsep, hmmin⟩ := exists_minimal_separating_lines hK hsep
  have hmc : IsCompact m := hK.of_isClosed_subset hmcl hmK
  refine ⟨m, hmK, hmc, ?_, hmsep⟩
  by_contra hnp
  rw [isPreconnected_iff_subset_of_disjoint] at hnp
  push Not at hnp
  obtain ⟨u, v, huopen, hvopen, hmuv, hinter, hnu, hnv⟩ := hnp
  set A : Set ℂ := m ∩ vᶜ with hA
  set B : Set ℂ := m ∩ uᶜ with hB
  have hAc : IsCompact A := hmc.of_isClosed_subset (hmcl.inter hvopen.isClosed_compl) Set.inter_subset_left
  have hBc : IsCompact B := hmc.of_isClosed_subset (hmcl.inter huopen.isClosed_compl) Set.inter_subset_left
  have hAsub : A ⊆ Qsq := Set.inter_subset_left.trans (hmK.trans hKsub)
  have hBsub : B ⊆ Qsq := Set.inter_subset_left.trans (hmK.trans hKsub)
  have hAB : A ∪ B = m := by
    rw [hA, hB]
    ext x; constructor
    · rintro (⟨hxS, -⟩ | ⟨hxS, -⟩) <;> exact hxS
    · intro hxS
      by_cases hxu : x ∈ u
      · refine Or.inl ⟨hxS, ?_⟩
        simp only [Set.mem_compl_iff]
        intro hxv
        exact Set.eq_empty_iff_forall_notMem.mp hinter x ⟨hxS, hxu, hxv⟩
      · exact Or.inr ⟨hxS, by simpa using hxu⟩
  have hdisjAB : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro x ⟨hxS, hxv⟩ ⟨-, hxu⟩
    rcases hmuv hxS with h | h
    · exact hxu h
    · exact hxv h
  have hAne : A ≠ m := by
    intro hAm
    have hmv : m ⊆ vᶜ := by rw [← hAm, hA]; exact Set.inter_subset_right
    apply hnu
    intro x hxm
    rcases hmuv hxm with hxu | hxv
    · exact hxu
    · exact absurd hxv (hmv hxm)
  have hBne : B ≠ m := by
    intro hBm
    have hmu : m ⊆ uᶜ := by rw [← hBm, hB]; exact Set.inter_subset_right
    apply hnv
    intro x hxm
    rcases hmuv hxm with hxu | hxv
    · exact absurd hxu (hmu hxm)
    · exact hxv
  have hTA : Sep A := by
    by_contra hcon
    exact hAne (hmmin A Set.inter_subset_left hAc.isClosed hcon)
  have hTB : Sep B := by
    by_contra hcon
    exact hBne (hmmin B Set.inter_subset_left hBc.isClosed hcon)
  exact hmsep (by rw [← hAB]; exact janiszewski_lines hAc hBc hdisjAB hAsub hBsub hTA hTB)

/-- **The planar square lemma** (the statement requested by the project). -/
theorem square_aux {E F : Set ℂ} (hEcl : IsClosed E) (hFcl : IsClosed F)
    (hEsub : E ⊆ Qsq) (hFsub : F ⊆ Qsq) (hdisj : Disjoint E F)
    (hEright : ∀ z ∈ E, z.re < 1) (hFleft : ∀ z ∈ F, -1 < z.re)
    (hEleft : ∃ z ∈ E, z.re = -1) (hFright : ∃ z ∈ F, z.re = 1) :
    ∃ K : Set ℂ, K ⊆ Qsq ∧ Disjoint K E ∧ Disjoint K F ∧ IsPreconnected K ∧ IsCompact K ∧
      (∃ z ∈ K, z.im = 1) ∧ (∃ z ∈ K, z.im = -1) := by
  by_contra hno
  have hEcomp : IsCompact E := isCompact_Qsq.of_isClosed_subset hEcl hEsub
  have hFcomp : IsCompact F := isCompact_Qsq.of_isClosed_subset hFcl hFsub
  have hKcomp : IsCompact (E ∪ F) := hEcomp.union hFcomp
  have hKsub : E ∪ F ⊆ Qsq := union_subset hEsub hFsub
  have hsep : ¬ Sep (E ∪ F) := by
    rintro ⟨T, hTsub, hTpre, hTc, hTt, hTb⟩
    exact hno ⟨T, hTsub.trans Set.sdiff_subset,
      (Set.disjoint_left.mpr fun a ha haE => (hTsub ha).2 (Or.inl haE)),
      (Set.disjoint_left.mpr fun a ha haF => (hTsub ha).2 (Or.inr haF)),
      hTpre, hTc, hTt, hTb⟩
  obtain ⟨C, hCK, hCc, hCpre, hCsep⟩ := continuum_cut hKcomp hKsub hsep
  have hCl : (C ∩ lE).Nonempty := nonempty_inter_left_of_not_sep hCsep
  have hCr : (C ∩ rE).Nonempty := nonempty_inter_right_of_not_sep hCsep
  have hCEF : C ⊆ E ∨ C ⊆ F :=
    isPreconnected_iff_subset_of_disjoint_closed.mp hCpre E F hEcl hFcl hCK
      (by rw [Set.disjoint_iff_inter_eq_empty.mp hdisj, Set.inter_empty])
  rcases hCEF with hCE | hCF
  · obtain ⟨z, hzC, hzr⟩ := hCr
    exact absurd (hEright z (hCE hzC)) (not_lt.mpr (le_of_eq hzr.1.symm))
  · obtain ⟨z, hzC, hzl⟩ := hCl
    exact absurd (hFleft z (hCF hzC)) (not_lt.mpr (le_of_eq hzl.1))

end Commons.Topology.Jordan

namespace Commons.Topology.Jordan

/-- The requested lemma: for two disjoint closed subsets `E`, `F` of the square, `E` touching the
left edge and avoiding the right edge, `F` touching the right edge and avoiding the left edge,
there is a top-to-bottom continuum inside the square avoiding both. -/
theorem square_sets_top_bottom_continuum {E F : Set ℂ}
    (hEcl : IsClosed E) (hFcl : IsClosed F)
    (hEsub : E ⊆ {z : ℂ | z.re ∈ Set.Icc (-1:ℝ) 1 ∧ z.im ∈ Set.Icc (-1:ℝ) 1})
    (hFsub : F ⊆ {z : ℂ | z.re ∈ Set.Icc (-1:ℝ) 1 ∧ z.im ∈ Set.Icc (-1:ℝ) 1})
    (hdisj : Disjoint E F)
    (hEright : ∀ z ∈ E, z.re < 1) (hFleft : ∀ z ∈ F, -1 < z.re)
    (hEleft : ∃ z ∈ E, z.re = -1) (hFright : ∃ z ∈ F, z.re = 1) :
    ∃ K : Set ℂ, K ⊆ {z : ℂ | z.re ∈ Set.Icc (-1:ℝ) 1 ∧ z.im ∈ Set.Icc (-1:ℝ) 1} ∧
      Disjoint K E ∧ Disjoint K F ∧ IsPreconnected K ∧ IsCompact K ∧
      (∃ z ∈ K, z.im = 1) ∧ (∃ z ∈ K, z.im = -1) :=
  square_aux hEcl hFcl hEsub hFsub hdisj hEright hFleft hEleft hFright

end Commons.Topology.Jordan